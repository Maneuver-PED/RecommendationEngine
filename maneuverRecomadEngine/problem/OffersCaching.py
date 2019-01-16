from maneuverRecomadEngine.escore.core import ESCore
from maneuverRecomadEngine.escore.pyQueryConstructor import QueryConstructor
import math
import sys
import json

def test():
    #testConnection = ESCore('85.120.206.38')
    testConnection = ESCore('85.120.206.38', index="maneuver2")


    # print(testConnection.clusterState())

    test_rec = {"0": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 2}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}, "IP": {"publicIPs": 3, "IPType": "IP4"},
            "1": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 50, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 20}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
            "2": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 50, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
            "3": {"memory": 16000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 50, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}}

    resp = testConnection.recomQuery(test_rec)

    print(resp)


# test_rec = {"0": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0},
#                   "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0},
#                   "network": {"connections": 20, "dataIn": 20, "dataOut": 2},
#                   "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]},
#             "IP": {"publicIPs": 3, "IPType": "IP4"},
#             "1": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0},
#                   "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0},
#                   "network": {"connections": 20, "dataIn": 20, "dataOut": 20},
#                   "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
#             "2": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0},
#                   "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0},
#                   "network": {"connections": 60, "dataIn": 60, "dataOut": 60},
#                   "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
#             "3": {"memory": 16000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0},
#                   "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0},
#                   "network": {"connections": 60, "dataIn": 60, "dataOut": 60},
#                   "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}}
#
#
# test_rec = {"0": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 2}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}, "IP": {"publicIPs": 3, "IPType": "IP4"},
#             "1": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 50, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 20}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
#             "2": {"memory": 8000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 50, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
#             "3": {"memory": 16000, "cpu": {"type": ["CPU"], "cpu": 8, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}}
#
# #web intrution
# test_rec = {0: {'memory': 16000, 'cpu': {'type': ['HDD', 'CPU'], 'cpu': 8, 'gpu': 0}, 'storage': {'type': [], 'hdd': 2000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'}, 1: {'memory': 2304, 'cpu': {'type': ['HDD', 'CPU'], 'cpu': 5, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1250, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 2: {'memory': 2304, 'cpu': {'type': ['HDD', 'CPU'], 'cpu': 5, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1250, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 3: {'memory': 768, 'cpu': {'type': ['HDD', 'CPU'], 'cpu': 3, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1250, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 4: {'memory': 2048, 'cpu': {'type': ['HDD', 'CPU'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 500, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}}
# #orx
# test_rec ={8: {'memory': 66048, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 26, 'gpu': 0}, 'storage': {'type': ['SSD'], 'hdd': 8000, 'ssd': 500}, 'network': {'connections': 100, 'dataIn': 6400, 'dataOut': 6400}, 'keywords': ['storage application', 'big data application', 'platform management'], 'operatingSystem': ['Linux']}, 'IP': {'publicIPs': 3, 'IPType': 'IP4'}, 9: {'memory': 74096, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 29, 'gpu': 0}, 'storage': {'type': ['SSD'], 'hdd': 10500, 'ssd': 500}, 'network': {'connections': 220, 'dataIn': 28400, 'dataOut': 28400}, 'keywords': ['queue', 'storage application', 'big data application', 'stream processing', 'platform management'], 'operatingSystem': ['Linux']}, 7: {'memory': 56000, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 22, 'gpu': 0}, 'storage': {'type': [], 'hdd': 7000, 'ssd': 0}, 'network': {'connections': 80, 'dataIn': 8000, 'dataOut': 8000}, 'keywords': ['storage application', 'big data application', 'schedueling', 'platform management'], 'operatingSystem': ['Linux']}}


#wordpress2
test_rec1 = {9: {'memory': 2048, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 500, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
            10: {'memory': 512, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 2, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            11: {'memory': 4512, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 6, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1500, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            12: {'memory': 4512, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 6, 'gpu': 0}, 'storage': {'type': [], 'hdd': 1500, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            13: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 3000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            14: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 3000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            15: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 3000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            16: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 3000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            17: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 3000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            18: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 5000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            19: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 6000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']},
            20: {'memory': 1024, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 7000, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['Linux']}}
#oryx2v2-2
test_rec2 = {8: {'memory': 66048, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 26, 'gpu': 0}, 'storage': {'type': ['SSD'], 'hdd': 8000, 'ssd': 500}, 'network': {'connections': 100, 'dataIn': 6400, 'dataOut': 6400}, 'keywords': ['platform management', 'storage application', 'big data application'], 'operatingSystem': ['Linux']}, 'IP': {'publicIPs': 3, 'IPType': 'IP4'},
            9: {'memory': 74096, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 29, 'gpu': 0}, 'storage': {'type': ['SSD'], 'hdd': 10500, 'ssd': 500}, 'network': {'connections': 220, 'dataIn': 28400, 'dataOut': 28400}, 'keywords': ['big data application', 'storage application', 'stream processing', 'platform management', 'queue'], 'operatingSystem': ['Linux']},
            7: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 32, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 80, 'dataIn': 8000, 'dataOut': 8000}, 'keywords': ['platform management', 'storage application', 'big data application', 'schedueling'], 'operatingSystem': ['Linux']}}

#WebIntrusionDetection3
test_rec = {1: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 64, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},

2: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 32, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
3: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 16, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
4: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 8, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
5: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 4, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
6: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 2, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},
7: {'memory': 0, 'cpu': {'type': ['CPU', 'HDD'], 'cpu': 1, 'gpu': 0}, 'storage': {'type': [], 'hdd': 0, 'ssd': 0}, 'network': {'connections': 0, 'dataIn': 0, 'dataOut': 0}, 'keywords': [], 'operatingSystem': ['']}, 'IP': {'publicIPs': 1, 'IPType': 'IP4'},

}

def getChipesOffer11(configuration):
    offer = {}
    prices={2:20, 4:40, 6: 60, 8: 80, 10: 100, 11:110, 12:120, 13:130, 14:140, 15:150, 16:160, 17:170,
            18:180, 19:190, 20:200, 21:210, 22:220, 23:230, 24:240, 25:250, 26:260, 27:270, 'IP': 0}
    for key, value in configuration.items():
        #print(key, value)
        val=0
        for k,v in value.items():
            if k == 'cpu':
                val = v['cpu']
        print("------------------", key, val, offer)
        if key != 'IP':
            offer[key] = prices[val]
    return offer

def getChipesOffer(configuration):
    # testConnection = ESCore('85.120.206.38', index="manuver2")
    #testConnection = ESCore('194.102.63.78')
    testConnection = ESCore('85.120.206.38', index="maneuver2")
    resp = testConnection.recomQuery(configuration)
    offer={}

    offers={}
    #print("response:", len(resp), resp, configuration)
    for machineId, maches in resp.items():
        if len(maches) > 0:
            min = sys.maxsize
            #print(machineId, maches)
            for mach in maches:
                #print('mach', len(mach))
                price = float(mach['pricePerUnit']['USD'])
                if price > 0:
                    if min > price:
                        min = price
                    if 'operatingSystem' in mach:
                        if mach['operatingSystem'] == "Linux" and (mach['storage']!=-1 if 'storage' in mach else True):
                        #if  (mach['storage'] != -1 if 'storage' in mach else True):
                            print(mach['pricePerUnit']['USD'],  mach['vcpu'], mach['memory'],
                                  mach['storage'] if 'storage' in mach else None,
                                  mach['operatingSystem'] if 'operatingSystem' in mach else None)
                            key="c{}m{}s{}os{}p{}".format( mach['vcpu'], mach['memory'],
                                  mach['storage'] if 'storage' in mach else None,
                                  mach['operatingSystem'] if 'operatingSystem' in mach else None, mach['pricePerUnit']['USD'])
                            #print(key)
                            offers[key]={'cpu':int(mach['vcpu']), 'memory':int(1000* mach['memory']), 'storage':int(mach['storage']*1000) if 'storage' in mach else None,
                                        'operatingSystem':mach['operatingSystem'] if 'operatingSystem' in mach else None,
                                        'price': int(1000*float(mach['pricePerUnit']['USD'])) }
        else:
            min = 10000000
        offer[machineId] = min
        print("machineId:", machineId, " min price:", min)
        print(offers)
    return offer, offers



def getChipesOffer(configurationDictionary, offerFileName):

    #print("!!!!!!!!!!!!!!!!!", offerFileName)
    with open(offerFileName) as json_data:
        offersDictionary = json.load(json_data)

    offer = {}

    for vmId, vmInfo in configurationDictionary.items():
        minPrice = 50000000
        if 'cpu' not in vmInfo:
            continue
        #print (vmId, vmInfo)
        for offerId, offerInfo in offersDictionary.items():
            #print(offerInfo)
            if (int(offerInfo['cpu']) >= int(vmInfo['cpu']['cpu'])) and \
                (offerInfo["memory"] >= vmInfo["memory"]) and \
                (offerInfo["storage"] >= (vmInfo["storage"]["hdd"]+vmInfo["storage"]["ssd"])):
                    if minPrice > offerInfo["price"]:
                        minPrice = offerInfo["price"]
        offer[vmId] = {"price": minPrice, "cpu": offerInfo['cpu'], "memory": vmInfo["memory"], "storage": vmInfo["storage"]}

    return offer


if __name__ == "__main__":
    all= {}
    #o, os =getChipesOffer(test_rec)
    #all.update(os)
    #o, os = getChipesOffer(test_rec1)
    #all.update(os)
    o, os = getChipesOffer(test_rec)
    all.update(os)
    with open('file.txt', 'w') as file:
        file.write(json.dumps(all))


