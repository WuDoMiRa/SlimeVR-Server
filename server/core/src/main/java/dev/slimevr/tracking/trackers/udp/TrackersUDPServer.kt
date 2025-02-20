package dev.slimevr.tracking.trackers.udp

import com.jme3.math.FastMath
import dev.slimevr.NetworkProtocol
import dev.slimevr.VRServer
import dev.slimevr.config.config
import dev.slimevr.protocol.rpc.MAG_TIMEOUT
import dev.slimevr.tracking.trackers.*
import io.eiren.util.Util
import io.eiren.util.collections.FastList
import io.eiren.util.logging.LogManager
import io.github.axisangles.ktmath.Quaternion.Companion.fromRotationVector
import io.github.axisangles.ktmath.Vector3
import kotlinx.coroutines.*
import org.apache.commons.lang3.ArrayUtils
import solarxr_protocol.rpc.ResetType
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetSocketAddress
import java.net.NetworkInterface
import java.net.SocketAddress
import java.net.SocketTimeoutException
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.ConcurrentLinkedDeque
import java.util.function.Consumer
import kotlin.collections.HashMap
import kotlin.coroutines.resume
import java.util.concurrent.locks.LockSupport
import kotlin.math.*

/**
 * Receives trackers data by UDP using extended owoTrack protocol.
 */
class TrackersUDPServer(private val port: Int, name: String, private val trackersConsumer: Consumer<Tracker>) : Thread(name) {
	private val random = Random()
	private val connections: MutableList<UDPDevice> = FastList()
	private val connectionsByAddress: MutableMap<SocketAddress, UDPDevice> = HashMap()
	private val connectionsByMAC: MutableMap<String, UDPDevice> = HashMap()
	private val broadcastAddresses: List<InetSocketAddress> = try {
		NetworkInterface.getNetworkInterfaces().asSequence().filter {
			// Ignore loopback, PPP, virtual and disabled interfaces
			!it.isLoopback && it.isUp && !it.isPointToPoint && !it.isVirtual
		}.flatMap {
			it.interfaceAddresses.asSequence()
		}.map {
			// This ignores IPv6 addresses
			it.broadcast
		}.filter { it != null && it.isSiteLocalAddress }.map { InetSocketAddress(it, this.port) }.toList()
	} catch (e: Exception) {
		LogManager.severe("[TrackerServer] Can't enumerate network interfaces", e)
		emptyList()
	}
	private val parser = UDPProtocolParser()

	// 1500 is a common network MTU. 1472 is the maximum size of a UDP packet (1500 - 20 for IPv4 header - 8 for UDP header)
	private val rcvBuffer = ByteArray(1500 - 20 - 8)
	private val bb = ByteBuffer.wrap(rcvBuffer).order(ByteOrder.BIG_ENDIAN)

	// Gets initialized in this.run()
	private lateinit var socket: DatagramSocket
	private var lastKeepup = System.currentTimeMillis()

	private fun setUpNewConnection(handshakePacket: DatagramPacket, handshake: UDPPacket3Handshake) {
		LogManager.info("[TrackerServer] Handshake received from ${handshakePacket.address}:${handshakePacket.port}")
		val addr = handshakePacket.address
		val socketAddr = handshakePacket.socketAddress

		// Check if it's a known device
		VRServer.instance.configManager.vrConfig.let { vrConfig ->
			if (vrConfig.isKnownDevice(handshake.macString)) return@let
			val mac = handshake.macString ?: return@let

			VRServer.instance.handshakeHandler.sendUnknownHandshake(mac)
			return
		}

		// Get a connection either by an existing one, or by creating a new one
		val connection: UDPDevice = synchronized(connections) {
			connectionsByMAC[handshake.macString]?.apply {
				// Look for an existing connection by the MAC address and update the
				// connection information
				connectionsByAddress.remove(address)
				address = socketAddr
				lastPacketNumber = 0
				ipAddress = addr
				name = handshake.macString?.let { "udp://$it" }
				descriptiveName = "udp:/$addr"
				protocolVersion = handshake.protocolVersion
				firmwareVersion = handshake.firmware
				connectionsByAddress[address] = this

				val i = connections.indexOf(this)
				LogManager
					.info(
						"""
						[TrackerServer] Tracker $i handed over to address $socketAddr.
						Board type: ${handshake.boardType},
						firmware name: ${handshake.firmware},
						protocol version: $protocolVersion,
						mac: ${handshake.macString},
						name: $name
						""".trimIndent(),
					)
			} ?: connectionsByAddress[socketAddr]?.apply {
				// Look for an existing connection by the socket address (IP and port)
				// and update the connection information
				lastPacketNumber = 0
				ipAddress = addr
				name = handshake.macString?.let { "udp://$it" }
					?: "udp:/$addr"
				descriptiveName = "udp:/$addr"
				protocolVersion = handshake.protocolVersion
				firmwareVersion = handshake.firmware
				val i = connections.indexOf(this)
				LogManager
					.info(
						"""
						[TrackerServer] Tracker $i reconnected from address $socketAddr.
						Board type: ${handshake.boardType},
						firmware name: ${handshake.firmware},
						protocol version: $protocolVersion,
						mac: ${handshake.macString},
						name: $name
						""".trimIndent(),
					)
			}
		} ?: run {
			// No existing connection could be found, create a new one

			val connection = UDPDevice(
				socketAddr,
				addr,
				handshake.macString ?: addr.hostAddress,
				handshake.boardType,
				handshake.mcuType,
			)
			VRServer.instance.deviceManager.addDevice(connection)
			connection.protocolVersion = handshake.protocolVersion
			connection.protocol = if (handshake.firmware?.isEmpty() == true) {
				// Only old owoTrack doesn't report firmware and have different packet IDs with SlimeVR
				NetworkProtocol.OWO_LEGACY
			} else {
				NetworkProtocol.SLIMEVR_RAW
			}
			connection.name = handshake.macString?.let { "udp://$it" }
				?: "udp:/$addr"
			// TODO: The missing slash in udp:// was intended because InetAddress.toString()
			// 		returns "hostname/address" but it wasn't known that if hostname is empty
			// 		string it just looks like "/address" lol.
			// 		Fixing this would break config!
			connection.descriptiveName = "udp:/$addr"
			connection.firmwareVersion = handshake.firmware
			synchronized(connections) {
				// Register the new connection
				val i = connections.size
				connections.add(connection)
				connectionsByAddress[socketAddr] = connection
				if (handshake.macString != null) {
					connectionsByMAC[handshake.macString!!] = connection
				}
				LogManager
					.info(
						"""
						[TrackerServer] Tracker $i connected from address $socketAddr.
						Board type: ${handshake.boardType},
						firmware name: ${handshake.firmware},
						protocol version: ${connection.protocolVersion},
						mac: ${handshake.macString},
						name: ${connection.name}
						""".trimIndent(),
					)
			}
			if (connection.protocol == NetworkProtocol.OWO_LEGACY || connection.protocolVersion < 9) {
				// Set up new sensor for older firmware.
				// Firmware after 7 should send sensor status packet and sensor
				// will be created when it's received
				setUpSensor(connection, 0, handshake.imuType, 1, MagnetometerStatus.NOT_SUPPORTED, null, TrackerDataType.ROTATION)
			}
			connection
		}
		connection.firmwareFeatures = FirmwareFeatures()
		bb.limit(bb.capacity())
		bb.rewind()
		parser.writeHandshakeResponse(bb, connection)
		socket.send(DatagramPacket(rcvBuffer, bb.position(), connection.address))
	}

	private val mainScope = CoroutineScope(SupervisorJob())
	private fun setUpSensor(connection: UDPDevice, trackerId: Int, sensorType: IMUType, sensorStatus: Int, magStatus: MagnetometerStatus, trackerPosition: TrackerPosition?, trackerDataType: TrackerDataType) {
		LogManager.info("[TrackerServer] Sensor $trackerId for ${connection.name} status: $sensorStatus")
		var imuTracker = connection.getTracker(trackerId)
		if (imuTracker == null) {
			var formattedHWID = connection.hardwareIdentifier.replace(":", "").takeLast(5)
			if (trackerId != 0) {
				formattedHWID += "_$trackerId"
			}

			imuTracker = Tracker(
				connection,
				VRServer.getNextLocalTrackerId(),
				connection.name + "/" + trackerId,
				"IMU Tracker $formattedHWID",
				trackerPosition,
				trackerNum = trackerId,
				hasRotation = true,
				hasAcceleration = true,
				userEditable = true,
				imuType = if (trackerDataType == TrackerDataType.ROTATION) sensorType else null,
				allowFiltering = true,
				needsReset = true,
				needsMounting = true,
				usesTimeout = true,
				magStatus = magStatus,
				trackerDataType = trackerDataType,
			)
			connection.trackers[trackerId] = imuTracker
			trackersConsumer.accept(imuTracker)
			LogManager.info("[TrackerServer] Added sensor $trackerId for ${connection.name}, ImuType $sensorType, DataType $trackerDataType, default TrackerPosition $trackerPosition")
		}
		val status = UDPPacket15SensorInfo.getStatus(sensorStatus)
		if (status != null) imuTracker.status = status

		if (magStatus == MagnetometerStatus.NOT_SUPPORTED) return
		if (magStatus == MagnetometerStatus.ENABLED &&
			(!VRServer.instance.configManager.vrConfig.server.useMagnetometerOnAllTrackers || imuTracker.config.shouldHaveMagEnabled == false)
		) {
			mainScope.launch {
				withTimeoutOrNull(MAG_TIMEOUT) {
					connection.setMag(false, trackerId)
				}
			}
		} else if (magStatus == MagnetometerStatus.DISABLED &&
			VRServer.instance.configManager.vrConfig.server.useMagnetometerOnAllTrackers && imuTracker.config.shouldHaveMagEnabled == true
		) {
			mainScope.launch {
				withTimeoutOrNull(MAG_TIMEOUT) {
					connection.setMag(true, trackerId)
				}
			}
		}
	}

	private data class ConfigStateWaiter(
		val expectedState: Boolean,
		val channel: CancellableContinuation<Boolean>,
		var ran: Boolean = false,
	)

	private val queues: MutableMap<Triple<SocketAddress, ConfigTypeId, Int>, Deque<ConfigStateWaiter>> = ConcurrentHashMap()
	suspend fun setConfigFlag(device: UDPDevice, configTypeId: ConfigTypeId, state: Boolean, sensorId: Int = 255) {
		if (device.timedOut) return
		val triple = Triple(device.address, configTypeId, sensorId)
		val queue = queues.computeIfAbsent(triple) { _ -> ConcurrentLinkedDeque() }

		suspendCancellableCoroutine {
			val waiter = ConfigStateWaiter(state, it)
			queue.add(waiter)
			it.invokeOnCancellation {
				queue.remove(waiter)
			}
		}
	}

	private fun actualSetConfigFlag(device: UDPDevice, configTypeId: ConfigTypeId, state: Boolean, sensorId: Int) {
		val packet = UDPPacket25SetConfigFlag(sensorId, configTypeId, state)
		bb.limit(bb.capacity())
		bb.rewind()
		parser.write(bb, null, packet)
		socket.send(DatagramPacket(rcvBuffer, bb.position(), device.address))
	}

	override fun run() {
		val serialBuffer2 = StringBuilder()
		var CycleStart = System.nanoTime()
		val CycleDelay = 500 // This controls the delay between requesting data for each tracker.
		var DelayBetweenCycleStart = System.nanoTime()
		val DelayBetweenCycles=200_000_000 // This controls the delay between cycles itself. I.e if we already finished a cycle,
		// wait until this time has passed to do another cycle.
		try {
			socket = DatagramSocket(port)
			var prevPacketTime = System.currentTimeMillis()
			socket.soTimeout = 250
			while (true) {
				var received: DatagramPacket? = null
				try {
					val hasActiveTrackers = connections.any { it.trackers.size > 0 }
					if (!hasActiveTrackers) {
						val discoveryPacketTime = System.currentTimeMillis()
						if (discoveryPacketTime - prevPacketTime >= 2000) {
							for (addr in broadcastAddresses) {
								bb.limit(bb.capacity())
								bb.rewind()
								parser.write(bb, null, UDPPacket0Heartbeat)
								socket.send(DatagramPacket(rcvBuffer, bb.position(), addr))
							}
							prevPacketTime = discoveryPacketTime
						}
					}
					received = DatagramPacket(rcvBuffer, rcvBuffer.size)
					socket.receive(received)
					bb.limit(received.length)
					bb.rewind()
					val connection = synchronized(connections) { connectionsByAddress[received.socketAddress] }
					parser.parse(bb, connection)
						.filterNotNull()
						.forEach { processPacket(received, it, connection) }

					queues.forEach { (t, p) ->
						val q = p.firstOrNull() ?: return@forEach
						if (q.ran) return@forEach

						val device = connectionsByAddress[t.first] ?: run {
							p.removeFirst()
							LogManager.info("[TrackerServer] Device ${t.first} not connected, so can't communicate with it")
							return@forEach
						}
						actualSetConfigFlag(device, t.second, q.expectedState, t.third)
						if (!device.timedOut) q.ran = true
					}
				} catch (ignored: SocketTimeoutException) {
				} catch (e: Exception) {
					LogManager.warning(
						"[TrackerServer] Error parsing packet ${packetToString(received)}",
						e,
					)
				}
				// Iterate through trackers and send a packet to update. This code could be moved upwards though...
				// Why is this made in kotlin?
				// And why am I getting errors in this file just by installing an extension for Kotlin code :sob:
				//val CycleDelayElapsed = System.nanoTime() - DelayBetweenCycleStart
				//if (CycleDelayElapsed < DelayBetweenCycles) {
				//	LockSupport.parkNanos(DelayBetweenCycles - CycleDelayElapsed)
				//	DelayBetweenCycleStart=System.nanoTime()
					
				//}
				// Unified TFRC-controlled sending
				synchronized(connections) {
					for (conn in connections) {
						try {
							// 1. Calculate time since last send
							val elapsed = System.currentTimeMillis() - conn.lastSendTime
							val interval = (1000.0 / conn.currentRate).toLong()
							
							// 2. Send if interval elapsed
							if (elapsed >= interval) {
								sendSensorData(conn)
								sendHeartbeat(conn) // Integrated heartbeat
								conn.lastSendTime = System.currentTimeMillis()
							}
	
							// 3. Dynamic timeout check
							val timeoutThreshold = (3000 / conn.currentRate).toLong() // 3x interval
							handleConnectionState(conn, timeoutThreshold)
						} catch (e: Exception) {
							LogManager.warning("[TrackerServer] Error processing ${conn.name}", e)
						}
					}
				}
				// TFRC rate calculation every 2 seconds
				if (System.currentTimeMillis() - lastKeepup >= 2000) {
					updateAllTFRCRates()
					lastKeepup = System.currentTimeMillis()
				}
				

			}
		} catch (e: Exception) {
			e.printStackTrace()
		} finally {
			Util.close(socket)
		}
	}

	private fun sendSensorData(conn: UDPDevice) {
		val seqNum = conn.sequenceNumber++
		conn.sentPackets[seqNum] = System.currentTimeMillis()
		
		bb.limit(bb.capacity())
		bb.rewind()
		val ackPacket = UDPPacket27Ack(seqNum, System.currentTimeMillis())
		parser.write(bb, conn, ackPacket)
		socket.send(DatagramPacket(rcvBuffer, bb.position(), conn.address))
	}
	
	private fun sendHeartbeat(conn: UDPDevice) {
		bb.limit(bb.capacity())
		bb.rewind()
		parser.write(bb, conn, UDPPacket1Heartbeat)
		socket.send(DatagramPacket(rcvBuffer, bb.position(), conn.address))
	}
	
	private fun handleConnectionState(conn: UDPDevice, timeoutThreshold: Long) {
		val timeSinceLastPacket = System.currentTimeMillis() - conn.lastPacket
		val shouldTimeout = timeSinceLastPacket > timeoutThreshold
		
		if (shouldTimeout && !conn.timedOut) {
			LogManager.info("[TrackerServer] ${conn.name} timed out (${timeSinceLastPacket}ms > ${timeoutThreshold}ms)")
			conn.trackers.values.forEach { it.status = TrackerStatus.TIMED_OUT }
			conn.timedOut = true
		} else if (!shouldTimeout && conn.timedOut) {
			LogManager.info("[TrackerServer] ${conn.name} recovered")
			conn.trackers.values.forEach { it.status = TrackerStatus.OK }
			conn.timedOut = false
		}
	}
	
	private fun updateAllTFRCRates() {
		connections.forEach { conn ->
			try {
				// [Keep existing TFRC calculation code]
				conn.currentRate = conn.currentRate.coerceIn(25.0, 400.0) // Higher minimum
			} catch (e: Exception) {
				LogManager.warning("[TrackerServer] TFRC error", e)
			}
		}
	}

	private fun calculateLossEventRate(conn: UDPDevice): Double {
		if (conn.lossIntervals.isEmpty()) return 0.0
		val n = minOf(conn.lossIntervals.size, 8)
		var weightedSum = 0.0
		var totalWeight = 0.0
	
		conn.lossIntervals.take(n).forEachIndexed { i, interval ->
			val weight = 1.0 / (1 shl (n - i - 1))
			weightedSum += weight * interval
			totalWeight += weight
		}
	
		return if (totalWeight > 0) 1.0 / (weightedSum / totalWeight) else 0.0
	}

	private fun handleConnectionTimeout(conn: UDPDevice) {
		if (!conn.timedOut) {
			conn.timedOut = true
			LogManager.info("[TrackerServer] Tracker timed out: $conn")
		}
		conn.trackers.values.forEach { tracker ->
			if (tracker.status == TrackerStatus.OK) {
				tracker.status = TrackerStatus.TIMED_OUT
			}
		}
	}

	private fun processPacket(received: DatagramPacket, packet: UDPPacket, connection: UDPDevice?) {
		connection?.lastPacket = System.currentTimeMillis()
		val tracker: Tracker?
		when (packet) {
			is UDPPacket0Heartbeat, is UDPPacket1Heartbeat, is UDPPacket25SetConfigFlag -> {}

			is UDPPacket27Ack -> {
				if (connection == null) return@processPacket
				connection.lastPacket = System.currentTimeMillis() // Add this
				// Detect lost packets using 4×RTT threshold
				val lost = connection.sentPackets.filter { (seq, time) ->
					seq < packet.sequenceNumber && 
					(System.currentTimeMillis() - time) > 4 * connection.rtt
				}
				
				if (lost.isNotEmpty()) {
					recordLossEvent(connection)
					connection.sentPackets.keys.removeAll(lost.keys)
				}
				
				// Update RTT (existing implementation)
				val sendTime = connection.sentPackets.remove(packet.sequenceNumber)
				if (sendTime != null) {
					val measuredRtt = (System.currentTimeMillis() - sendTime).toDouble()
					connection.rtt = 0.875 * connection.rtt + 0.125 * measuredRtt
				}
			}

			is UDPPacket3Handshake -> setUpNewConnection(received, packet)

			is RotationPacket -> {
				var rot = packet.rotation
				rot = AXES_OFFSET.times(rot)
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				tracker.setRotation(rot)
				if (packet is UDPPacket23RotationAndAcceleration) {
					// Switch x and y around to adjust for different axes
					tracker.setAcceleration(Vector3(packet.acceleration.y, packet.acceleration.x, packet.acceleration.z))
				}
				tracker.dataTick()
			}

			is UDPPacket17RotationData -> {
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				var rot17 = packet.rotation
				rot17 = AXES_OFFSET * rot17
				when (packet.dataType) {
					UDPPacket17RotationData.DATA_TYPE_NORMAL -> {
						tracker.setRotation(rot17)
						tracker.dataTick()
						// tracker.calibrationStatus = rotationData.calibrationInfo;
						// Not implemented in server
					}

					UDPPacket17RotationData.DATA_TYPE_CORRECTION -> {
// 						tracker.rotMagQuaternion.set(rot17);
// 						tracker.magCalibrationStatus = rotationData.calibrationInfo;
// 						tracker.hasNewCorrectionData = true;
						// Not implemented in server
					}
				}
			}

			is UDPPacket18MagnetometerAccuracy -> {}

			is UDPPacket4Acceleration -> {
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				// Switch x and y around to adjust for different axes
				tracker.setAcceleration(Vector3(packet.acceleration.y, packet.acceleration.x, packet.acceleration.z))
			}

			is UDPPacket10PingPong -> {
				if (connection == null) return
				if (connection.lastPingPacketId == packet.pingId) {
					for (t in connection.trackers.values) {
						t.ping = (System.currentTimeMillis() - connection.lastPingPacketTime).toInt() / 2
						t.dataTick()
					}
				} else {
					LogManager.debug(
						"[TrackerServer] Wrong ping id ${packet.pingId} != ${connection.lastPingPacketId}",
					)
				}
			}

			is UDPPacket11Serial -> {
				if (connection == null) return
				println("[${connection.name}] ${packet.serial}")
			}

			is UDPPacket12BatteryLevel -> connection?.trackers?.values?.forEach {
				it.batteryVoltage = packet.voltage
				it.batteryLevel = packet.level * 100
			}

			is UDPPacket13Tap -> {
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				LogManager.info(
					"[TrackerServer] Tap packet received from ${tracker.name}: ${packet.tap}",
				)
			}

			is UDPPacket14Error -> {
				LogManager.severe(
					"[TrackerServer] Error received from ${received.socketAddress}: ${packet.errorNumber}",
				)
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				tracker.status = TrackerStatus.ERROR
			}

			is UDPPacket15SensorInfo -> {
				if (connection == null) return
				val magStatus = packet.sensorConfig?.magStatus ?: MagnetometerStatus.NOT_SUPPORTED
				setUpSensor(
					connection,
					packet.sensorId,
					packet.sensorType,
					packet.sensorStatus,
					magStatus,
					packet.trackerPosition,
					packet.trackerDataType,
				)
				// Send ack
				bb.limit(bb.capacity())
				bb.rewind()
				parser.writeSensorInfoResponse(bb, connection, packet)
				socket.send(DatagramPacket(rcvBuffer, bb.position(), connection.address))
				LogManager.info(
					"[TrackerServer] Sensor info for ${connection.descriptiveName}/${packet.sensorId}: ${packet.sensorStatus}, mag $magStatus",
				)
			}

			is UDPPacket19SignalStrength -> connection?.trackers?.values?.forEach {
				it.signalStrength = packet.signalStrength
			}

			is UDPPacket20Temperature -> {
				tracker = connection?.getTracker(packet.sensorId) ?: return
				tracker.temperature = packet.temperature
			}

			is UDPPacket21UserAction -> {
				if (connection == null) return
				var name = ""
				when (packet.type) {
					UDPPacket21UserAction.RESET_FULL -> {
						name = "Full reset"
						VRServer.instance.resetHandler.sendStarted(ResetType.Full)
						VRServer.instance.resetTrackersFull(RESET_SOURCE_NAME)
					}

					UDPPacket21UserAction.RESET_YAW -> {
						name = "Yaw reset"
						VRServer.instance.resetHandler.sendStarted(ResetType.Yaw)
						VRServer.instance.resetTrackersYaw(RESET_SOURCE_NAME)
					}

					UDPPacket21UserAction.RESET_MOUNTING -> {
						name = "Mounting reset"
						VRServer
							.instance
							.resetHandler
							.sendStarted(ResetType.Mounting)
						VRServer.instance.resetTrackersMounting(RESET_SOURCE_NAME)
					}

					UDPPacket21UserAction.PAUSE_TRACKING -> {
						name = "Pause tracking toggle"
						VRServer.instance.togglePauseTracking(RESET_SOURCE_NAME)
					}
				}

				LogManager.info(
					"[TrackerServer] User action from ${connection.descriptiveName} received. $name performed.",
				)
			}

			is UDPPacket22FeatureFlags -> {
				if (connection == null) return
				// Respond with server flags
				bb.limit(bb.capacity())
				bb.rewind()
				parser.write(bb, connection, packet)
				socket.send(DatagramPacket(rcvBuffer, bb.position(), connection.address))
				connection.firmwareFeatures = packet.firmwareFeatures
			}

			is UDPPacket24AckConfigChange -> {
				if (connection == null) return
				val queue = queues[Triple(connection.address, packet.configType, packet.sensorId)] ?: run {
					LogManager.severe("[TrackerServer] Error, acknowledgment of config change that we don't have in our queue.")
					return
				}
				val changed = queue.removeFirst()
				changed.channel.resume(true)
				val trackers = if (SensorSpecificPacket.isGlobal(packet.sensorId)) {
					connection.trackers.values.toList()
				} else {
					listOf(connection.getTracker(packet.sensorId) ?: return)
				}
				LogManager.info("[TrackerServer] Acknowledged config change on ${connection.descriptiveName} (${trackers.map { it.trackerNum }.joinToString()}). Config changed on ${packet.configType}")
			}

			is UDPPacket26FlexData -> {
				tracker = connection?.getTracker(packet.sensorId)
				if (tracker == null) return
				if (tracker.trackerDataType == TrackerDataType.FLEX_RESISTANCE) {
					tracker.trackerFlexHandler.setFlexResistance(packet.flexData)
				} else if (tracker.trackerDataType == TrackerDataType.FLEX_ANGLE) {
					tracker.trackerFlexHandler.setFlexAngle(packet.flexData)
				}
				tracker.dataTick()
			}

			is UDPPacket200ProtocolChange -> {}
		}
	}

		// TrackersUDPServer.kt
	private fun updateTFCRate(conn: UDPDevice) {
		// Calculate loss event rate
		val lossEventRate = if (conn.lossIntervals.isEmpty()) 0.0 else {
			val n = minOf(conn.lossIntervals.size, 8)
			var weightedSum = 0.0
			var totalWeight = 0.0
			
			conn.lossIntervals.take(n).forEachIndexed { i, interval ->
				val weight = 1.0 / (1 shl (n - i - 1))
				weightedSum += weight * interval
				totalWeight += weight
			}
			
			1.0 / (weightedSum / totalWeight)
		}

		// TFRC throughput equation
		val R = conn.rtt / 1000.0 // Convert to seconds
		val p = lossEventRate.coerceAtLeast(1e-8)
		val s = conn.packetSize.toDouble()
		
		val X = (s * 8) / (R * sqrt(p) + 
			12.0 * p * (1 + 32 * p*p) * sqrt(3.0 * p/8.0))

		// Convert from bits/sec to packets/sec
		conn.currentRate = X / (s * 8)
		conn.currentRate = conn.currentRate.coerceIn(20.0, 400.0)
	}

	private fun processAck(conn: UDPDevice, ackedSeq: Long) {
		// Detect lost packets
		val lostPackets = conn.sentPackets.filter { (seq, time) ->
			seq < ackedSeq && (System.currentTimeMillis() - time) > conn.rtt * 4
		}
		
		if (lostPackets.isNotEmpty()) {
			recordLossEvent(conn)
			conn.sentPackets.keys.removeAll(lostPackets.keys)
		}
	}

	private fun recordLossEvent(conn: UDPDevice) {
		val currentTime = System.currentTimeMillis() / 1000.0
		if (!conn.firstLoss) {
			val interval = currentTime - conn.lastLossTime
			conn.lossIntervals.addFirst(interval)
			if (conn.lossIntervals.size > 8) conn.lossIntervals.removeLast()
		} else {
			conn.firstLoss = false
		}
		conn.lastLossTime = currentTime
	}

	fun getConnections(): List<UDPDevice?> = connections

	// FIXME: for some reason it ends up disconnecting after 30 seconds have passed instead of immediately
	fun disconnectDevice(device: UDPDevice) {
		synchronized(connections) {
			connections.remove(device)
		}
		synchronized(connectionsByAddress) {
			connectionsByAddress.filter { (_, dev) -> dev.id == device.id }.keys.forEach(
				connectionsByAddress::remove,
			)
		}
		device.trackers.forEach { (_, tracker) ->
			tracker.status = TrackerStatus.DISCONNECTED
		}

		LogManager.info(
			"[TrackerServer] Forcefully disconnected ${device.hardwareIdentifier} device.",
		)
	}

	companion object {
		/**
		 * Change between IMU axes and OpenGL/SteamVR axes
		 */
		private val AXES_OFFSET = fromRotationVector(-FastMath.HALF_PI, 0f, 0f)
		private const val RESET_SOURCE_NAME = "TrackerServer"
		private fun packetToString(packet: DatagramPacket?): String {
			val sb = StringBuilder()
			sb.append("DatagramPacket{")
			if (packet == null) {
				sb.append("null")
			} else {
				sb.append(packet.address.toString())
				sb.append(packet.port)
				sb.append(',')
				sb.append(packet.length)
				sb.append(',')
				sb.append(ArrayUtils.toString(packet.data))
			}
			sb.append('}')
			return sb.toString()
		}
	}
}
