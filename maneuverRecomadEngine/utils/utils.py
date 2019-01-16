import numpy as np
import sys
from scipy.spatial import distance
import itertools
from maneuverRecomadEngine.utils.eq import validCfg


def parse_g_name(name):
    split_name = name.split("-")
    return ("{}{}".format(split_name[3], split_name[4])).lower()


def parse_a_dtype(desc):
    if "SSD" in desc:
        return "SSD"
    else:
        return "HDD"


def parse_query_string(qstring):
    sc = sm = ss = ''
    for dp in qstring.split("AND"):
        if "vcpu" == dp.split(":")[0].lstrip():
            sc = float(dp.split(":")[1].replace("\"", ""))
        if "memory" == dp.split(":")[0].lstrip():
            sm = float(dp.split(":")[1].replace("\"", ""))
        if "storage" == dp.split(":")[0].lstrip():
            ss = float(dp.split(":")[1].replace("\"", ""))
    return sc, sm, ss


def closest_to(qstring, tresholds=None):
    vCPU, memory, storage = parse_query_string(qstring)
    if tresholds is None:
        cl = [1, 2, 4, 8,  16, 17, 32, 48, 64, 96, 128]
        ml = [1, 2, 4, 8, 16, 32, 64, 128, 256, 384]
        sl = [50, 100, 200, 300, 400, 500, 1000, 2000, 5000, 10000]
    else:
        cl = tresholds['cl']
        ml = tresholds['ml']
        sl = tresholds['sl']
    print("This is the memory ->{}".format(memory))
    nvcpu = min(cl, key=lambda x: abs(x - vCPU))
    nmemory = min(ml, key=lambda x: abs(x - memory))
    print ("nvcpu", nvcpu, "nmemory", nmemory)
    # nstorage = min(sl, key=lambda x: abs(x - storage))
    nstorage = 0.0
    dcl = list(np.array(cl)[np.logical_and(np.array(cl) > vCPU, np.array(cl) <= cl[-1])])
    dml = list(np.array(ml)[np.logical_and(np.array(ml) > memory, np.array(ml) <= ml[-1])])
    # dsl = list(np.array(sl)[np.logical_and(np.array(sl) > storage, np.array(sl) <= sl[-1])])

    print("dcl", dcl,"dml", dml)
    if not dcl or not dml:
        print("Empty list found!!")
        sys.exit()
    print("This is the valid ml values {} and this the new ajusted ones {}".format(ml, dml))
    newtresholds = {'cl': dcl, 'ml': dml, 'sl': []}
    nqstring = "memory:\"{}\" AND vcpu:\"{}\" AND storage:\"{}\"".format(nmemory, nvcpu, nstorage)
    return nqstring, newtresholds


def closest_cfg(qstring):
    vCPU, memory, storage = parse_query_string(qstring)
    cfg = [vCPU, memory]
    cl = [2, 4, 8, 16, 32, 48, 64, 96, 128]
    ml = [1, 2, 4, 8, 16, 32, 64, 128, 256, 384]
    dcl = list(np.array(cl)[np.logical_and(np.array(cl) > vCPU, np.array(cl) <= cl[-1])])
    dml = list(np.array(ml)[np.logical_and(np.array(ml) > memory, np.array(ml) <= ml[-1])])
    if not dcl or not dml:
        print("Empty list found for {}!!".format(qstring))
        sys.exit()
    closest_index = distance.cdist([cfg], validCfg).argmin()

    return "memory:\"{}\" AND vcpu:\"{}\" AND storage:\"{}\"".format(validCfg[closest_index][1], validCfg[closest_index][0], 0)


def man_qstring(vCPU, memory, storage):
    return "memory:\"{}\" AND vcpu:\"{}\" AND storage:\"{}\"".format(memory, vCPU, storage)


def parse_location(loc):
    ploc = loc.split("(")[-1].split(")")[0]
    if "Virginia" in ploc:
        return "NVirginia"
    if "Carolina" in ploc:
        return "SCarolina"
    if "Paulo" in ploc:
        return "Sao_Paulo"
    if "California" in ploc:
        return "Northern_California"
    if "US" in ploc:
        return "GovCloud"
    if "Japan" in ploc:
        return "Tokyo"
    if "Osaka" in ploc:
        return "Tokyo"
    if "india" in ploc:
        return "Mumbai"
    if "United" in ploc:
        return "US"
    if "Pacific" in ploc:
        return "Asia_Pacific"
    return loc.split("(")[-1].split(")")[0]


def parse_cs(cs):
    return cs.split(" ")[0]


def parse_usg(usg):
    # print(usg.split(':')[1].split('.'))
    return "{}{}".format(usg.split(':')[1].split('.')[0], usg.split(':')[1].split('.')[1])


def parseStorageType(ustr):
    ustr = '0.16TB SSD'
    ssize = parseStorage(ustr.split(" ")[0])


def parseStorage(ustr):
    ln = []
    ls = []
    for e in ustr:
        try:
            ln.append(int(e))
        except:
            ls.append(e)
    finalNumber = ''
    finalUnit = ''
    for el in ln:
        finalNumber += str(el)

    for le in ls:
        finalUnit += str(le)

    finalfNumber = float(finalNumber)

    if finalUnit == 'TB':
        finalfNumber = finalfNumber * 1000.0
    return finalfNumber

if __name__ == "__main__":
    name = "CP-COMPUTEENGINE-VMIMAGE-N1-HIGHMEM-4"
    loc = "US East (N. Virginia)"
    loc2 = ['Asia Pacific (Mumbai)', 'Any', 'South America (Sao Paulo)', 'Europe', 'Australia', 'EU (Paris)', 'US ISO East', 'EU (Ireland)', 'South America', 'Asia Pacific (Sydney)', 'US ISOB East (Ohio)', 'United States', 'Asia Pacific (Seoul)', 'Canada', 'EU (London)', 'EU (Frankfurt)', 'India', 'Asia Pacific (Singapore)', 'Japan', 'Asia Pacific (Tokyo)', 'US West (N. California)', 'US East (N. Virginia)', 'Asia Pacific', 'Canada (Central)', 'AWS GovCloud (US)', 'Asia Pacific (Osaka-Local)', 'US West (Oregon)', 'US East (Ohio)']
    csl = ['2.5 GHz', '2.3 GHz', '3.0 Ghz', '2.4 GHz', '2.9 GHz']
    usg = 'EUW2-DedicatedUsage:c4.xlarge'
    print(parse_g_name(name))

    d1 = "1 x 1920 SSD"
    d2 = "ebsonly"
    d3 = "1 x 1920 HDD"

    print(parse_a_dtype(d1))
    print(parse_a_dtype(d2))
    print(parse_a_dtype(d3))

    print(parse_location(loc))

    for el in loc2:
        print(parse_location(el))

    for el in csl:
        print(parse_cs(el))

    print(parse_usg(usg))
