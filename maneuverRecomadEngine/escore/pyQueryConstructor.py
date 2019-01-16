from addict import Dict
import os
import json

class QueryConstructor():
    def __init__(self):
        self.author = 'Constructor for maneuver ES connector querys'
        # self.systemLoadString = "collectd_type:\"load\" AND host:\"dice.cdh.master\""

    def ceQueryString(self, opt):
        # print(opt.keys())
        qslist = {}
        for k, v in opt.items():
            if k == 'IP':
                v['publicIPs']
                v['IPType']
            else:
                # print('Component: {}'.format(k))
                # print(v['memory']/1000)
                # print(v['cpu']['type'])
                # print(v['cpu']['cpu'])
                # print(v['cpu']['gpu'])
                if 'SSD' in v['storage']['type']:
                    sstorage = int(v['storage']['ssd'])
                else:
                    sstorage = int(v['storage']['hdd'])
                qstring = "memory:\"{}\" AND vcpu:\"{}\" AND storage:\"{}\"".format(int(v['memory']/1000), int(v['cpu']['cpu']), sstorage)
                qslist[k] = qstring
                print(qstring)
        return qslist

    def cequery(self, qstring, size=10000, msc=2.0, msm=4.0, mss=2.0):
        for dp in qstring.split("AND"):
            if "vcpu" == dp.split(":")[0].lstrip():
                sc = float(dp.split(":")[1].replace("\"", ""))
            if "memory" == dp.split(":")[0].lstrip():
                sm = float(dp.split(":")[1].replace("\"", ""))
            if "storage" == dp.split(":")[0].lstrip():
                ss = float(dp.split(":")[1].replace("\"", ""))
        filterl = []
        if sc != 0.0:
            filterl.append({"range": {"vcpu": {"gte": sc, "lte": sc + msc}}})
        if sm != 0.0:
            filterl.append({"range": {"memory": {"gte": sm, "lte": sm+msm}}})
        if ss != 0.0:
            filterl.append({"range": {"storage": {"gte": ss, "lte": ss * mss}}})

        cquery = Dict()
        cquery.size = size
        cquery.query.bool.must.query_string.query = "*"
        cquery.query.bool.filter = filterl
        #print("filter:", filterl)
        cqueryd = cquery.to_dict()
        return cqueryd


if __name__ == '__main__':
    # test = {
    #     "query": {
    #         "bool": {
    #             "must": {
    #                 "query_string": {
    #                     "query": "*"
    #                 }
    #             }
    #         }
    #     }
    # }
    t = QueryConstructor()
    # print(test)
    # print(t.cequery("memory:\"7*\" AND vcpu:\"4\""))


    test = {"0": {"memory": 4000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 2}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}, "IP": {"publicIPs": 3, "IPType": "IP4"},
        "1": {"memory": 4000, "cpu": {"type": ["CPU"], "cpu": 2, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 20, "dataIn": 20, "dataOut": 20}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
        "2": {"memory": 12000, "cpu": {"type": ["CPU"], "cpu": 6, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Windows"]},
        "3": {"memory": 10000, "cpu": {"type": ["CPU"], "cpu": 6, "gpu": 0}, "storage": {"type": ["HDD"], "hdd": 0, "ssd": 0}, "network": {"connections": 60, "dataIn": 60, "dataOut": 60}, "keywords": ["storage application", "big data application"], "operatingSystem": ["Linux"]}}
    print(t.ceQueryString(test))
    print(t.cequery(t.ceQueryString(test)["0"]))