/**
 * Generated by @openapi-codegen
 *
 * @version 0.0.1
 */
export type VerionCheckResponse = {
  success: boolean;
  reason?: {
    message: string;
    versions: string;
  };
};

/**
 * Root object declaring a built firmware
 * this object contains:
 *  - the status of the build
 *  - the the repository and commit used as source
 */
export type FirmwareDTO = {
  /**
   * UUID of the firmware
   *
   * @format uuid
   */
  id: string;
  /**
   * Id of the firmware version used.
   * Usually the commit id of the source
   * used to build the firmware
   */
  releaseId: string;
  /**
   * Current status of the build
   * this value will change during the build
   * process
   *
   * BUILDING -> DONE \\ the firmwrare is build and ready
   *          -> FAILED  \\ the build failled and will be garbage collected
   */
  buildStatus:
    | 'CREATING_BUILD_FOLDER'
    | 'DOWNLOADING_FIRMWARE'
    | 'EXTRACTING_FIRMWARE'
    | 'SETTING_UP_DEFINES'
    | 'BUILDING'
    | 'SAVING'
    | 'DONE'
    | 'ERROR';
  /**
   * The repository and branch used as source of the firmware
   */
  buildVersion: string;
  /**
   * The date of creation of this firmware build
   *
   * @format date-time
   */
  createdAt: string;
};

export type BuildResponseDTO = {
  /**
   * Id of the firmware
   *
   * @format uuid
   */
  id: string;
  /**
   * Build status of the firmware
   */
  status:
    | 'CREATING_BUILD_FOLDER'
    | 'DOWNLOADING_FIRMWARE'
    | 'EXTRACTING_FIRMWARE'
    | 'SETTING_UP_DEFINES'
    | 'BUILDING'
    | 'SAVING'
    | 'DONE'
    | 'ERROR';
  /**
   * List of built firmware files, only set if the build succeeded
   */
  firmwareFiles?: FirmwareFileDTO[];
};

export type FirmwareFileDTO = {
  /**
   * Url to the file
   */
  url: string;
  /**
   * Address of the partition
   */
  offset: number;
  /**
   * Is this file the main firmware
   */
  isFirmware: boolean;
  /**
   * Id of the linked firmware
   *
   * @format uuid
   */
  firmwareId: string;
};

export type CreateBuildFirmwareDTO = {
  /**
   * Repository of the firmware used
   */
  version: string;
  /**
   * Board config, used to declare the pins used by the board
   */
  boardConfig: CreateBoardConfigDTO;
  /**
   * Imu config, list of all the imus used and their pins
   *
   * @minItems 1
   */
  imusConfig: CreateImuConfigDTO[];
};

export type CreateBoardConfigDTO = {
  /**
   * Type of the board
   */
  type:
    | 'BOARD_SLIMEVR'
    | 'BOARD_NODEMCU'
    | 'BOARD_WROOM32'
    | 'BOARD_WEMOSD1MINI'
    | 'BOARD_TTGO_TBASE'
    | 'BOARD_ESP01'
    | 'BOARD_LOLIN_C3_MINI'
    | 'BOARD_BEETLE32C3'
    | 'BOARD_ES32C3DEVKITM1';
  /**
   * Pin address of the indicator LED
   */
  ledPin: string;
  /**
   * Is the indicator LED enabled
   */
  enableLed: boolean;
  /**
   * Is the led inverted
   */
  ledInverted: boolean;
  /**
   * Pin address of the battery indicator
   */
  batteryPin: string;
  /**
   * Type of battery
   */
  batteryType: 'BAT_EXTERNAL' | 'BAT_INTERNAL' | 'BAT_MCP3021' | 'BAT_INTERNAL_MCP3021';
  /**
   * Array of the different battery resistors, [indicator, SHIELD_R1, SHIELD_R2]
   *
   * @minItems 3
   * @maxItems 3
   */
  batteryResistances: number[];
};

export type CreateImuConfigDTO = {
  /**
   * Type of the imu
   */
  type:
    | 'IMU_BNO085'
    | 'IMU_MPU9250'
    | 'IMU_MPU6500'
    | 'IMU_BNO080'
    | 'IMU_BNO055'
    | 'IMU_BNO086'
    | 'IMU_MPU6050'
    | 'IMU_BMI160'
    | 'IMU_ICM20948'
    | 'IMU_BMI270';
  /**
   * Pin address of the imu int pin
   * not all imus use it
   */
  intPin: string | null;
  /**
   * Rotation of the imu in degrees
   */
  rotation: number;
  /**
   * Pin address of the scl pin
   */
  sclPin: string;
  /**
   * Pin address of the sda pin
   */
  sdaPin: string;
  /**
   * Is this imu optionnal
   * Allows for extensions to be unplugged
   */
  optional: boolean;
};

export type VersionNotFoundExeption = {
  cause: void;
  name: string;
  message: string;
  stack?: string;
};

/**
 * A representation of any set of values over any amount of time. This is the most basic building block
 * of RxJS.
 */
export type ObservableType = {
  /**
   * @deprecated true
   */
  source?: Observableany;
  /**
   * @deprecated true
   */
  operator?: OperatoranyType;
};

/**
 * A representation of any set of values over any amount of time. This is the most basic building block
 * of RxJS.
 */
export type Observableany = {
  /**
   * @deprecated true
   */
  source?: Observableany;
  /**
   * @deprecated true
   */
  operator?: Operatoranyany;
};

/**
 * *
 */
export type Operatoranyany = {};

/**
 * *
 */
export type OperatoranyType = {};

export type ReleaseDTO = {
  /**
   * id of the release, usually the commit id
   */
  id: string;
  /**
   * url of the release
   */
  url: string;
  /**
   * name of the release
   */
  name: string;
  /**
   * url of the source archive
   */
  zipball_url: string;
  /**
   * Is this release a pre release
   */
  prerelease: boolean;
  /**
   * Is this release a draft
   */
  draft: boolean;
};

export type Imudto = {
  /**
   * Type of the imu
   */
  type:
    | 'IMU_BNO085'
    | 'IMU_MPU9250'
    | 'IMU_MPU6500'
    | 'IMU_BNO080'
    | 'IMU_BNO055'
    | 'IMU_BNO086'
    | 'IMU_MPU6050'
    | 'IMU_BMI160'
    | 'IMU_ICM20948'
    | 'IMU_BMI270';
  /**
   * Does that imu type require a int pin
   */
  hasIntPin: boolean;
  /**
   * First address of the imu
   */
  imuStartAddress: number;
  /**
   * Increment of the address for each new imus
   */
  addressIncrement: number;
};

export type DefaultBuildConfigDTO = {
  /**
   * Default config of the selected board
   * contains all the default pins information about the selected board
   */
  boardConfig: CreateBoardConfigDTO;
  /**
   * Inform the flashing utility that the user need to press the boot (or Flash) button
   * on the tracker
   */
  needBootPress?: boolean;
  /**
   * Inform the flashing utility that the board will need a reboot after
   * being flashed
   */
  needManualReboot?: boolean;
  /**
   * Will use the default values and skip the customisation options
   */
  shouldOnlyUseDefaults?: boolean;
  /**
   * List of the possible imus pins, usually only two items will be sent
   *
   * @minItems 1
   */
  imuDefaults: IMUDefaultDTO[];
  /**
   * Gives the offset of the firmare file in the eeprom. Used for flashing
   */
  application_offset: number;
};

export type IMUDefaultDTO = {
  /**
   * Type of the imu
   */
  type?:
    | 'IMU_BNO085'
    | 'IMU_MPU9250'
    | 'IMU_MPU6500'
    | 'IMU_BNO080'
    | 'IMU_BNO055'
    | 'IMU_BNO086'
    | 'IMU_MPU6050'
    | 'IMU_BMI160'
    | 'IMU_ICM20948'
    | 'IMU_BMI270';
  /**
   * Pin address of the imu int pin
   * not all imus use it
   */
  intPin: string | null;
  /**
   * Rotation of the imu in degrees
   */
  rotation?: number;
  /**
   * Pin address of the scl pin
   */
  sclPin: string;
  /**
   * Pin address of the sda pin
   */
  sdaPin: string;
  /**
   * Is this imu optionnal
   * Allows for extensions to be unplugged
   */
  optional: boolean;
};

export type BoardConfigDTONullable = {
  /**
   * Unique id of the board config, used for relations
   *
   * @format uuid
   */
  id: string;
  /**
   * Type of the board
   */
  type:
    | 'BOARD_SLIMEVR'
    | 'BOARD_NODEMCU'
    | 'BOARD_WROOM32'
    | 'BOARD_WEMOSD1MINI'
    | 'BOARD_TTGO_TBASE'
    | 'BOARD_ESP01'
    | 'BOARD_LOLIN_C3_MINI'
    | 'BOARD_BEETLE32C3'
    | 'BOARD_ES32C3DEVKITM1';
  /**
   * Pin address of the indicator LED
   */
  ledPin: string;
  /**
   * Is the indicator LED enabled
   */
  enableLed: boolean;
  /**
   * Is the led inverted
   */
  ledInverted: boolean;
  /**
   * Pin address of the battery indicator
   */
  batteryPin: string;
  /**
   * Type of battery
   */
  batteryType: 'BAT_EXTERNAL' | 'BAT_INTERNAL' | 'BAT_MCP3021' | 'BAT_INTERNAL_MCP3021';
  /**
   * Array of the different battery resistors, [indicator, SHIELD_R1, SHIELD_R2]
   *
   * @minItems 3
   * @maxItems 3
   */
  batteryResistances: number[];
  /**
   * Id of the linked firmware, used for relations
   *
   * @format uuid
   */
  firmwareId: string;
};

export type FirmwareDetailDTO = {
  /**
   * Pins informations about the board
   */
  boardConfig: BoardConfigDTONullable;
  /**
   * List of the declared imus, and their pin configuration
   *
   * @minItems 1
   */
  imusConfig: ImuConfigDTO[];
  /**
   * List of the built files / partitions with their url and offsets
   */
  firmwareFiles: FirmwareFileDTO[];
  /**
   * UUID of the firmware
   *
   * @format uuid
   */
  id: string;
  /**
   * Id of the firmware version used.
   * Usually the commit id of the source
   * used to build the firmware
   */
  releaseId: string;
  /**
   * Current status of the build
   * this value will change during the build
   * process
   *
   * BUILDING -> DONE \\ the firmwrare is build and ready
   *          -> FAILED  \\ the build failled and will be garbage collected
   */
  buildStatus:
    | 'CREATING_BUILD_FOLDER'
    | 'DOWNLOADING_FIRMWARE'
    | 'EXTRACTING_FIRMWARE'
    | 'SETTING_UP_DEFINES'
    | 'BUILDING'
    | 'SAVING'
    | 'DONE'
    | 'ERROR';
  /**
   * The repository and branch used as source of the firmware
   */
  buildVersion: string;
  /**
   * The date of creation of this firmware build
   *
   * @format date-time
   */
  createdAt: string;
};

export type BoardConfigDTO = {
  /**
   * Unique id of the board config, used for relations
   *
   * @format uuid
   */
  id: string;
  /**
   * Type of the board
   */
  type:
    | 'BOARD_SLIMEVR'
    | 'BOARD_NODEMCU'
    | 'BOARD_WROOM32'
    | 'BOARD_WEMOSD1MINI'
    | 'BOARD_TTGO_TBASE'
    | 'BOARD_ESP01'
    | 'BOARD_LOLIN_C3_MINI'
    | 'BOARD_BEETLE32C3'
    | 'BOARD_ES32C3DEVKITM1';
  /**
   * Pin address of the indicator LED
   */
  ledPin: string;
  /**
   * Is the indicator LED enabled
   */
  enableLed: boolean;
  /**
   * Is the led inverted
   */
  ledInverted: boolean;
  /**
   * Pin address of the battery indicator
   */
  batteryPin: string;
  /**
   * Type of battery
   */
  batteryType: 'BAT_EXTERNAL' | 'BAT_INTERNAL' | 'BAT_MCP3021' | 'BAT_INTERNAL_MCP3021';
  /**
   * Array of the different battery resistors, [indicator, SHIELD_R1, SHIELD_R2]
   *
   * @minItems 3
   * @maxItems 3
   */
  batteryResistances: number[];
  /**
   * Id of the linked firmware, used for relations
   *
   * @format uuid
   */
  firmwareId: string;
};

export type ImuConfigDTO = {
  /**
   * Unique id of the config
   * this probably will never be shown to the user as it is moslty use for relations
   *
   * @format uuid
   */
  id: string;
  /**
   * Type of the imu
   */
  type:
    | 'IMU_BNO085'
    | 'IMU_MPU9250'
    | 'IMU_MPU6500'
    | 'IMU_BNO080'
    | 'IMU_BNO055'
    | 'IMU_BNO086'
    | 'IMU_MPU6050'
    | 'IMU_BMI160'
    | 'IMU_ICM20948'
    | 'IMU_BMI270';
  /**
   * Rotation of the imu in degrees
   */
  rotation: number;
  /**
   * Pin address of the imu int pin
   * not all imus use it
   */
  intPin: string | null;
  /**
   * Pin address of the scl pin
   */
  sclPin: string;
  /**
   * Pin address of the sda pin
   */
  sdaPin: string;
  /**
   * Is this imu optionnal
   * Allows for extensions to be unplugged
   */
  optional: boolean;
  /**
   * id of the linked firmware, used for relations
   *
   * @format uuid
   */
  firmwareId: string;
};

/**
 * Defines the base Nest HTTP exception, which is handled by the default
 * Exceptions Handler.
 */
export type HttpException = {
  cause: void;
  name: string;
  message: string;
  stack?: string;
};
