eq_aws = {
    "us-east-2":	"Ohio",
    "us-east-1":	"NVirginia",
    "us-west-1":	"Northern_California",
    "us-west-2":	"Oregon",
    "ap-south-1":	"Mumbai",
    "ap-northeast-2":	"Seoul",
    "ap-southeast-1": "Singapore",
    "ap-southeast-2":	"Sydney",
    "ap-northeast-1":	"Tokyo",
    "ca-central-1":	"Canada",
    "cn-north-1":	"Beijing",
    "eu-central-1":	"Frankfurt",
    "eu-west-1":	"Ireland",
    "eu-west-2":	"London",
    "eu-west-3":	"Paris",
    "sa-east-1":	"Sao_Paulo"
}

eq_google = {
      # "us": 4.0240,
      "us-central1": "Iowa",
      "us-east1": "SCarolina",
      "us-east4": "NVirginia",
      "us-west1": "Oregon",
      # "europe": 4.0240,
      "europe-west1": "Belgium",
      "europe-west2": "London",
      "europe-west3": "Frankfurt",
      "europe-west4": "Netherlands",
      "northamerica-northeast1": "Canada",  # Montreal
      # "asia": 4.0240,
      "asia-east": "Taiwan",
      "asia-northeast": "Tokyo",
      "asia-southeast": "Singapore",
      "australia-southeast1": "Sidney",
      # "australia": 5.4324,
      "southamerica-east1": "Sao_Paulo",
      "asia-south1": "Mumbai"
}

eq_OS = {
    "linux": "Linux",

}

# "ML_AI": ['AmazonLex', 'AmazonRekognition', 'AmazonPolly', 'AmazonML'],
# "Analytics": ['AmazonAthena', 'AmazonCloudSearch', 'AmazonKinesis', 'AmazonKinesisAnalytics', 'AmazonQuickSight',
# 'AWSGlue', 'ElasticMapReduce', 'AmazonRedshift', 'datapipeline'],


eq_services = {
    "Compute": ['AmazonEC2', 'AmazonLightsail', 'AWSLambda' 'AmazonECR' 'AmazonSWF'],
    "Storage": ['AmazonS3', 'AmazonEFS', 'AWSStorageGateway', 'IngestionServiceSnowball', 'SnowballExtraDays',
                'AmazonGlacier', 'AmazonES'],
    "DataBases": ['AmazonDynamoDB', 'AmazonDAX', 'AmazonRedshift', 'AWSDatabaseMigrationSvc', 'AmazonRDS',
                  'AmazonElastiCache', 'AmazonSimpleDB'],
    "Networking": ['AmazonVPC', 'AmazonRoute53', 'AWSDirectConnect', 'AmazonCloudFront', 'AmazonApiGateway'],
    "Management_Tools": ['AmazonCloudWatch', 'AWSConfig', 'AWSCloudTrail', 'OpsWorks', 'AWSServiceCatalog',
                         'AmazonWAM', 'awskms', 'AWSBudgets', 'AWSCostExplorer'],
    "Dev": ['CodeBuild', 'AWSCodePipeline', 'AWSXRay', 'AWSCodeCommit', 'AWSCodeDeploy', 'CodeBuild', 'AmazonGameLift'],
    "Security": ['AmazonCognito', 'AmazonCognitoSync', 'AmazonGuardDuty', 'AmazonInspector', 'AWSDirectoryService',
                 'awswaf', 'AmazonCloudDirectory', 'AWSDirectConnect', 'CloudHSM', 'AWSShield'],
    "ML_AI": ['AmazonLex', 'AmazonRekognition', 'AmazonPolly', 'AmazonML', 'AmazonAthena', 'AmazonCloudSearch',
              'AmazonKinesis', 'AmazonKinesisAnalytics', 'AmazonQuickSight', 'AWSGlue', 'ElasticMapReduce',
              'AmazonRedshift', 'datapipeline', 'mobileanalytics'],
    "IoT": ['AWSIoT', 'AWSGreengrass'],
    "Integration": ['AmazonSNS', 'AWSQueueService', 'AmazonMQ', 'AmazonKinesisFirehose', 'IngestionService'],
    "Migration": ['AWSDatabaseMigrationSvc', 'IngestionServiceSnowball'],
    "Mobile": ['AmazonPinpoint', 'AWSDeviceFarm', 'AmazonApiGateway', 'mobileanalytics'],
    "Media": ['AmazonETS', 'AWSElementalMediaConvert', 'AWSElementalMediaPackage', 'AWSElementalMediaTailor',
              'AWSElementalMediaLive', 'AWSElementalMediaStore'],
    "Bussiness_Productivity": ['AmazonChime', 'AmazonWorkMail', 'AmazonWorkDocs', 'AmazonSES', 'AmazonConnect',
                               'AmazonChimeDialin', 'AWSSupportBusiness', 'AWSSupportEnterprise'],
    "App_Streaming": ['AmazonWorkSpaces', 'AmazonWAM'],
    "supported_services": ['AmazonKinesis', 'AWSDatabaseMigrationSvc', 'IngestionServiceSnowball', 'AmazonRDS',
                           'AWSCloudTrail', 'AWSGlue', 'AmazonChimeDialin', 'AmazonWorkMail', 'AmazonMQ',
                           'AmazonCloudFront', 'AmazonS3', 'AmazonPolly', 'AmazonCloudSearch', 'AmazonQuickSight',
                           'CloudHSM', 'AmazonLex', 'AmazonKinesisAnalytics', 'ElasticMapReduce', 'AmazonSimpleDB',
                           'AWSBudgets', 'AmazonInspector', 'AWSCodeDeploy', 'IngestionService',
                           'AWSElementalMediaLive', 'AmazonES', 'AWSConfig', 'AmazonConnect', 'AmazonVPC',
                           'datapipeline', 'AmazonApiGateway', 'AmazonCloudWatch', 'AWSCostExplorer',
                           'AmazonDynamoDB', 'AWSDirectoryService', 'AmazonAthena', 'AWSIoT', 'AmazonCognito',
                           'AWSElementalMediaPackage', 'AWSElementalMediaStore', 'AmazonEFS', 'SnowballExtraDays',
                           'OpsWorks', 'AWSQueueService', 'awskms', 'AmazonCognitoSync', 'AWSElementalMediaConvert',
                           'AWSElementalMediaTailor', 'AWSLambda', 'AmazonECR', 'AmazonSWF', 'AWSGreengrass', 'mobileanalytics',
                           'AmazonRekognition', 'AmazonPinpoint', 'AmazonChime', 'AWSSupportEnterprise',
                           'AWSServiceCatalog', 'AWSCodePipeline', 'AmazonEC2', 'AmazonWorkDocs', 'AWSDirectConnect',
                           'AmazonGlacier', 'AmazonKinesisFirehose', 'AWSDeviceFarm', 'AmazonSES', 'AmazonWorkSpaces',
                           'AmazonWAM', 'AmazonElastiCache', 'CodeBuild', 'AmazonCloudDirectory', 'AmazonSNS',
                           'AmazonETS', 'awswaf', 'AmazonGameLift', 'AWSXRay', 'AmazonML', 'AmazonRedshift',
                           'AmazonDAX', 'AmazonRoute53', 'AmazonGuardDuty', 'AWSShield', 'AWSCodeCommit',
                           'AmazonLightsail', 'AWSStorageGateway', 'AWSSupportBusiness']
}

validCfg = [(1, 1), (1, 2), (1, 4), (1, 8), (1, 16), (2, 1), (2, 2), (2, 4), (2, 8), (2, 16), (2, 32), (4, 4), (4, 8),
            (4, 16), (4, 32), (8, 4), (8, 16), (8, 32), (8, 64), (16, 32), (16, 64), (32, 128), (64, 1), (64, 256),
            (96, 384), (128, 1), (128, 2)]