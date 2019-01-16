from datetime import datetime
from elasticsearch import Elasticsearch
from datetime import datetime
from elasticsearch import Elasticsearch
from maneuverRecomadEngine.escore.pyQueryConstructor import QueryConstructor
from maneuverRecomadEngine.utils.utils import parse_query_string, closest_cfg, man_qstring, closest_to
import requests
import os
import sys, getopt
import math

import time

# from pyQueryConstructor import QueryConstructor


class ESCore:
    def __init__(self, esEndpoint,  esInstanceEndpoint=9200, index="maneuver"):
        self.esInstance = Elasticsearch(esEndpoint)
        self.esEndpoint = esEndpoint
        self.esInstanceEndpoint = esInstanceEndpoint
        self.myIndex = index
        self.adt_timeout = os.environ['ADP_TIMEOUT'] = os.getenv('ADP_TIMEOUT', str(60))
        self.newquery = QueryConstructor()

    def query(self, queryBody, allm=True, dMetrics=[], debug=False):
        res = self.esInstance.search(index=self.myIndex, body=queryBody, request_timeout=230)
        if debug == True:
            print ("%---------------------------------------------------------%")
            print ("Raw JSON Ouput")
            print (res)
            print("%d documents found" % res['hits']['total'])
            print ("%---------------------------------------------------------%")
        termsList = []
        termValues = []
        ListMetrics = []
        for doc in res['hits']['hits']:
            if allm == False:
                if not dMetrics:
                    sys.exit("dMetrics argument not set. Please supply valid list of metrics!")
                for met in dMetrics:
                    # prints the values of the metrics defined in the metrics list
                    if debug == True:
                        print ("%---------------------------------------------------------%")
                        print ("Parsed Output -> ES doc id, metrics, metrics values.")
                        print("doc id %s) metric %s -> value %s" % (doc['_id'], met, doc['_source'][met]))
                        print ("%---------------------------------------------------------%")
                    termsList.append(met)
                    termValues.append(doc['_source'][met])
                dictValues = dict(zip(termsList, termValues))
            else:
                for terms in doc['_source']:
                    # prints the values of the metrics defined in the metrics list
                    if debug == True:
                        print ("%---------------------------------------------------------%")
                        print ("Parsed Output -> ES doc id, metrics, metrics values.")
                        print("doc id %s) metric %s -> value %s" % (doc['_id'], terms, doc['_source'][terms]))
                        print ("%---------------------------------------------------------%")
                    termsList.append(terms)
                    termValues.append(doc['_source'][terms])
                    dictValues = dict(zip(termsList, termValues))
            ListMetrics.append(dictValues)
        return ListMetrics, res

    def info(self):
        try:
            res = self.esInstance.info()
        except Exception as inst:
            # logger.error('[%s] : [ERROR] Exception has occured while connecting to ES with type %s at arguments %s', datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), type(inst), inst.args)
            print("An exception has occured with type %s at arguments %s" %(type(inst), inst.args))
            sys.exit(2)
        return res

    def createIndex(self, indexName):
        try:
            self.esInstance.create(index=indexName, ignore=400)
            # logger.info('[%s] : [INFO] Created index %s',
            #              datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName)
        except Exception as inst:
            print(" Failed to created index %s with %s and %s") % (indexName, type(inst), inst.args)
            # logger.error('[%s] : [ERROR] Failed to created index %s with %s and %s',
            #             datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName, type(inst), inst.args)

    def closeIndex(self, indexName):
        try:
            self.esInstance.close(index=indexName)
            # logger.info('[%s] : [INFO] Closed index %s',
            #              datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName)
        except Exception as inst:
            print('Failed to close index %s with %s and %s' % (indexName, type(inst), inst.args))
            # logger.error('[%s] : [ERROR] Failed to close index %s with %s and %s',
            #              datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName, type(inst),
            #              inst.args)

    def deleteIndex(self, indexName):
        try:
            res = self.esInstance.indices.delete(index=indexName, ignore=[400, 404])
            # logger.info('[%s] : [INFO] Deleted index %s',
            #         datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName)
        except Exception as inst:
            print('Failed to delete index %s with %s and %s' % (indexName, type(inst), inst.args))
            # logger.error('[%s] : [ERROR] Failed to delete index %s with %s and %s',
            #              datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName, type(inst),
            #              inst.args)
            return 0
        return res

    def openIndex(self, indexName):
        res = self.esInstance.indices.open(index=indexName)
        # logger.info('[%s] : [INFO] Open index %s',
        #             datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), indexName)
        return res

    def getIndex(self, indexName):
        res = self.esInstance.indices.get(index=indexName, human=True)
        return res

    def getIndexSettings(self, indexName):
        res = self.esInstance.indices.get_settings(index=indexName, human=True)
        return res

    def clusterHealth(self):
        res = self.esInstance.cluster.health(request_timeout=15)
        return res

    def clusterSettings(self):
        res = self.esInstance.cluster.get_settings(request_timeout=15)
        return res

    def clusterState(self):
        res = self.esInstance.cluster.stats(human=True, request_timeout=15)
        return res

    def nodeInfo(self):
        res = self.esInstance.nodes.info(request_timeout=15)
        return res

    def nodeState(self):
        res = self.esInstance.nodes.stats(request_timeout=15)
        return res

    def pushData(self, anomalyIndex, doc_type, body):
        try:
            res = self.esInstance.index(index=anomalyIndex, doc_type=doc_type, body=body)
        except Exception as inst:
            # logger.error('[%s] : [ERROR] Exception has occured while pushing anomaly with type %s at arguments %s',
            #              datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), type(inst), inst.args)
            print("Can't push data to ES!")
            print('Exception has occured while pushing anomaly with type %s at arguments %s', type(inst), inst.args)
            sys.exit(2)
        return res

    def mquery(self, queryBody):
        # adt_timeout = os.environ['ADP_TIMEOUT'] = os.getenv('ADP_TIMEOUT', str(60)) # Set timeout as env variable ADT_TIMEOUT, if not set use default 60
        try:
            res = self.esInstance.search(index=self.myIndex, body=queryBody, request_timeout=float(self.adt_timeout))
        except Exception as inst:
            # logger.error('[%s] : [ERROR] Exception while executing ES query with %s and %s', datetime.fromtimestamp(time.time()).strftime('%Y-%m-%d %H:%M:%S'), type(inst), inst.args)
            print("Error while querying elasticsearch backend with {} and {}".format(type(inst), inst.args))
            sys.exit(2)
        return res

    def _squery(self, queryBody, scrollSize = '1m'):
        try:
            res = self.esInstance.search(index=self.myIndex, body=queryBody, request_timeout=float(self.adt_timeout), scroll=scrollSize)
        except Exception as inst:
            print("Error while querying elasticsearch backend with {} and {}".format(type(inst), inst.args))
            sys.exit(2)
        return res

    def _scroll(self, scrollID, scrollSize='1m'):
        try:
            res = self.esInstance.scroll(scroll_id=scrollID, scroll=scrollSize)
        except Exception as inst:
            print("Error while querying elasticsearch backend with {} and {}".format(type(inst), inst.args))
            sys.exit(2)
        return res

    def _compQuery(self, queryBody):
        final_resp = []
        respS = self._squery(queryBody=queryBody)
        #print("Query took: {}".format(respS['took']))
        final_resp = final_resp + respS['hits']['hits']
        scroll_id = respS['_scroll_id']
        total_length = math.ceil(respS['hits']['total'] / 10000)
        if total_length >= 2:
            for e in range(int(total_length)):
                sres = self._scroll(scroll_id)
                final_resp = final_resp + sres['hits']['hits']
        #print("Length of response: {}".format(len(final_resp)))
        filtered = []
        for el in final_resp:
            if 'instanceFamily' in el['_source']:
                filtered.append(el['_source'])
        #print("Length of filtered response: {}".format(len(filtered)))
        return filtered

    def _recurentQuery(self, q, treashold=None):
        #print("Calculating closest valid values ....")
        qs = closest_cfg(q)
        print(qs)
        re_queryBody = self.newquery.cequery(qs)
        re_resp = self._compQuery(queryBody=re_queryBody)
        if len(re_resp) == 0:
            return self._recurentQuery(qs)
        else:
            return re_resp

    def recomQuery(self, opt_query):
        lq = self.newquery.ceQueryString(opt_query)
        qresp = {}
        for k, q in lq.items():
            queryBody = self.newquery.cequery(q)
            resp = self._compQuery(queryBody=queryBody)
            if len(resp) == 0:
                resp = self._recurentQuery(q)
            qresp[k] = resp
        return qresp


if __name__ == "__main__":
    testConnection = ESCore('85.120.206.38')
    print(testConnection.info())
    print(testConnection.clusterHealth())
    # print(testConnection.createIndex())
    # print(testConnection.getIndex('maneuver'))
    body = {'test': "ttt"}
    testConnection.pushData('whatever', doc_type='d', body=body)
