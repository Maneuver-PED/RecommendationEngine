from flask import Flask, render_template, request
from maneuverRecomadEngine.problem.ProblemDefinition import ManeuverProblem
from flask_cors import CORS, cross_origin
import json

app = Flask(__name__)
cors = CORS(app, resources={r"/api/*": {"origins": "*"}})

@app.route("/re")
def isAlive():
    return "True"

@app.route("/re/z3", methods = ['POST'])
@cross_origin()
def run_z3():
    print("Start exposeRE")
    if request.headers['Content-Type'] == 'application/json':
        #ManeuverProblem().readConfigurationJSON(request.json)
        # request.json
        print("Application description (from webUI):", json.dumps(request.json))
        mp = ManeuverProblem()
        mp.readConfigurationJSON(request.json)
        print("Querying...")
        # offers: offers matching the query?
        # full_offers: all offers
        offers, full_offers = get_available_offers("http://hal720m.sage.ieat.ro:5000/OMS/query/full", mp)
        print("Offers after querying...")
        print("Offers matching the query", len(offers))
        print("Offers matching the query", len(full_offers))

        # print("List of Offers")
        # for o in offers:
        #     print(o)
        # print("Number of offers:", len(offers))

        minPrice, priceVMs, t, a, vms_type = mp.solveSMT(offers, None, None, "optimize", False, True, True, False, False)
        print("minPrice ", minPrice)

        if minPrice != -1:
            print("time ", t)
            print("available Offers ", a)
            print("vm # on list (first elem has id=0)", vms_type)

            res = json.dumps(build_responce(mp, a, vms_type, offers, full_offers))

            print("JSON Offer", res)
            return res
        else:
            return "unsat"
    else:
        return "415 Unsupported Media Type ;)"

def build_responce(mp, a, vms_type, offers, full_offers):
    r=[]
    vms_nr = 1
    print(vms_type, vms_type[0].is_int(), vms_type[0].is_real(), vms_type[0].is_int_value())
    for k in range(len(a[0])):
        comp_list = []
        for i in range(len(a)):
            if a[i][k] == 1:
                comp_list.append(mp.componentsList[i].name)
        if len(comp_list) > 0:
            d_vm = {"id": vms_nr, "components" : comp_list, "offer": full_offers[offers[vms_type[k].numerator().as_long()][0]]["initial"]}
            vms_nr += 1
            r.append(d_vm)

    return r

def get_available_offers_file():
    import csv

    with open("offers.txt", "r") as csvfile:
        spamreader = csv.reader(csvfile, delimiter=',', quotechar='|')
        set_cpus = set()
        set_memory = set()
        set_storage = set()
        for row in spamreader:
            set_cpus.add(row[1])
            set_memory.add(row[2])
            set_storage.add(row[3])
            print(row)
        print(set_cpus)
        print(set_memory)
        print(set_storage)

def get_available_offers(url, mp):
        """
        Method used to retrive all available offers and filter the offers at satiesfies components and extract the values
        that are taken in consideration by solver
        :param url: the rest URL used to retreive all offers
        :param mp: manuver problem
        :return:
        """
        import requests
        headers = {'Content-type': 'application/json', 'Accept': '*/*'}

        data = mp.buildSolutinInformations(mp.buildInitialAllocation(), mp.nrComp)

        data = {1: {'memory': 256000, 'cpu': {'type': ['CPU'], 'cpu': 64, 'gpu': 0}, 'storage': {'type': ['HDD'], 'hdd': 8000, 'ssd': 0}},
                2: {'memory': 1952, 'cpu': {'type': ['CPU'], 'cpu': 64, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 1000, 'ssd': 0}},
                3: {'memory': 244000, 'cpu': {'type': ['CPU'], 'cpu': 32, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 4000, 'ssd': 0}},
                4: {'memory': 60000, 'cpu': {'type': ['CPU'], 'cpu': 32, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 2000, 'ssd': 0}},
                5: {'memory': 64000, 'cpu': {'type': ['CPU'], 'cpu': 16, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 2000, 'ssd': 0}},
                6: {'memory': 122000, 'cpu': {'type': ['CPU'], 'cpu': 16, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 1000, 'ssd': 0}},
                7: {'memory': 30000, 'cpu': {'type': ['CPU'], 'cpu': 8, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 2000, 'ssd': 0}},
                8: {'memory': 6100, 'cpu': {'type': ['CPU'], 'cpu': 8, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 6000, 'ssd': 0}},
                9: {'memory': 15000, 'cpu': {'type': ['CPU'], 'cpu': 4, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 2000, 'ssd': 0}},
                10: {'memory': 30500, 'cpu': {'type': ['CPU'], 'cpu': 4, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 3000, 'ssd': 0}},
                11: {'memory': 1500, 'cpu': {'type': ['CPU'], 'cpu': 2, 'gpu': 0},
                    'storage': {'type': ['HDD'], 'hdd': 2000, 'ssd': 0}},
                12: {'memory': 3050, 'cpu': {'type': ['CPU'], 'cpu': 2, 'gpu': 0},
                     'storage': {'type': ['HDD'], 'hdd': 1000, 'ssd': 0}},
                13: {'memory': 3750, 'cpu': {'type': ['CPU'], 'cpu': 1, 'gpu': 0},
                     'storage': {'type': ['HDD'], 'hdd': 1000, 'ssd': 0}},
                14: {'memory': 117000, 'cpu': {'type': ['CPU'], 'cpu': 17, 'gpu': 0},
                     'storage': {'type': ['HDD'], 'hdd': 24000, 'ssd': 0}}
                }

        response = requests.post(url, headers=headers, data=json.dumps(data))
        data = response.json()

        #filter offers here will be removed when ontology search is rafinated
        set_os = set()
        for comp in mp.componentsList:
            if not ((mp.componentsList[comp].operatingSystem is None) or (len(mp.componentsList[comp].operatingSystem) == 0)):
                set_os.add(mp.componentsList[comp].operatingSystem.lower())

        print("Operating system of the components: {}".format(set_os))

        keys = set()
        available_offers = []
        full_offers ={}
        for key, value in data.items():
            for item in value:
                offer = extract_information_about_offer(item)
                if offer is None or offer["key"] in keys: continue
                if str(offer["operatingSystem"]).lower() not in set_os: continue

                keys.add(offer["key"])
                l = [offer["key"]]
                l.append(offer["cpu"])
                l.append(offer["memory"])
                l.append(offer["storage"])
                l.append(offer["price"])
                #if offer["price"] == 0: print(item)
                available_offers.append(l)
                full_offers[offer["key"]] = offer
        #print(".......", len(available_offers))
        return available_offers, full_offers

def extract_information_about_offer(initial_offer):
        offer = {}
        offer["storage"] = int(float(initial_offer["storage"]))*1000  if "storage" in initial_offer else -1000
        if offer["storage"] == -1000:
            return None
        offer["price"] = int(float(initial_offer["pricePerUnit"]["USD"]) * 1000)
        if offer["price"] == 0:
            return None
        offer["storageType"] = initial_offer["storageType"]if "storageType" in initial_offer else None
        offer["cpu"] = initial_offer["vcpu"]
        offer["operatingSystem"] = initial_offer["operatingSystem"] if "operatingSystem" in initial_offer else None

        offer["memory"] = int(float(initial_offer["memory"]))*1000
        offer["description"] = initial_offer["description"]
        offer["usagetype"] = initial_offer["usagetype"]
        offer["instanceType"] = initial_offer["instanceType"]
        offer["initial"] = initial_offer

        id = offer["instanceType"] + offer["description"] + offer["usagetype"]
        offer["key"] = id
        return offer


# class ManeuverRERequest(MethodView):
#     def get(self):
#         return True
#
#     def post(self):
#         if request.headers['Content-Type'] == 'application/json':
#             ManeuverProblem().readConfigurationJSON(request.json)
#
#
#             return jsonify(request.json)
#         else:
#             return "415 Unsupported Media Type ;)"


# app.add_url_rule(
#     '/re_z3_recomandation',
#     view_func=ManeuverRERequest.as_view('re_request')
# )

if __name__ == "__main__":
    app.run(debug=True)

#http://hal720m.sage.ieat.ro:5000
#/OMS/query/full
#post
