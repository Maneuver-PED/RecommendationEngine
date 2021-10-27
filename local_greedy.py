import numpy as np

class Resources:
    def __init__(self, cpu, memory, storage, price=0):
        self.mem = memory
        self.cpu = cpu
        self.storage = storage
        self.price = price

    def get_mem(self):
        return self.mem

    def get_cpu(self):
        return self.cpu

    def get_storage(self):
        return self.storage

    def get_price(self):
        return self.price


# components hardware spec
components = [Resources(2, 512, 1000), #wordpress
              Resources(2, 512, 2000), #mysql
              Resources(4, 2048, 500), #DNSloadbalancer
              Resources(4, 2048, 500), #HTTPloadbalancer
              Resources(4, 4000, 500)] #Varnish
map_resurse = {}
min_val = 100000000000
min_sol = []

def checkConflict(comp1, comp2, assignMat):
    for k in range(len(assignMat[0])):
        #print("sum ", assignMat[comp1][k] + assignMat[comp2][k])
        if (assignMat[comp1][k] + assignMat[comp2][k] > 1):
            return 0
    return 1

# if (checkRequireProvides(2, 0, 7, 1, assignMat) and checkRequireProvides(3, 0, 3, 1, assignMat) and
#             checkRequireProvides(0, 1, 2, 3, assignMat)):

def checkRequireProvides(comp1, comp2, reqn, provn, assignMat):
    s1 = 0
    s2 = 0
    for k in range(len(assignMat[0])):
        s1 += assignMat[comp1][k]
        s2 += assignMat[comp2][k]
    print(reqn, "***", s1, "***", provn, "***", s2)
    if (reqn * s1 > provn * s2):
        return 0
    return 1

def checkHardware(assignMat, VMsType, offersLst, compLst):
    sumCPU = 0
    sumMem = 0
    sumSto = 0

    for column in range(len(assignMat[0])):
        for row in range(len(assignMat)):
            if (assignMat[row][column] == 1):
                sumCPU += compLst[column].get_cpu()
                sumMem += compLst[column].get_mem()
                sumSto += compLst[column].get_storage()
            print(sumCPU, ", ", sumMem, ",", sumSto)
            print(VMsType[column], ":", offersLst[VMsType[column]].get_cpu(), ", ", offersLst[VMsType[column]].get_mem(), ",",
                  offersLst[VMsType[column]].get_storage(), ",", offersLst[VMsType[column]].get_price())
            if not (sumCPU <= offersLst[VMsType[column]].get_cpu() and
                        sumMem <= offersLst[VMsType[column]].get_mem() and
                        sumSto <= offersLst[VMsType[column]].get_storage()):
                print("in")
                return 0
    return 1

def local_greedy(price, assignMat, VMsType, offersLst, compLst):
    setNewWordpress = 0
    setNewMySQL = 0
    idxWordpress = -1
    print("assignMat before WP =", assignMat)
    # add 1 WP on first free place
    for j in assignMat[0]:
        if (assignMat[0][j]==0):
            assignMat[0][j] = 1
            idxWordpress = j
            break
    if (checkConflict(0, 2, assignMat) and checkConflict(0, 3, assignMat)):
        setNewWordpress = 1
    else:
        #restore value
        assignMat[0][idxWordpress] = 0
        j = idxWordpress + 1
        while (not (checkConflict(0, 2, assignMat) and checkConflict(0, 3, assignMat)) and j < len(assignMat[0])):
            if (assignMat[0][j]==0):
                assignMat[0][j] = 1
                setNewWordpress = 1
            j=j+1
    # new VM to be aquired
    if setNewWordpress == 0:
        for arr in assignMat:
            arr.append(0)
        assignMat[0][len(assignMat[0])-1] = 1
        setNewWordpress = 1
    print("assignMat after WP=", assignMat)
    #comp1id, comp2id, comp1number, comp2number
    if (checkRequireProvides(2, 0, 7, 1, assignMat) and checkRequireProvides(3, 0, 3, 1, assignMat) and
            checkRequireProvides(0, 1, 2, 3, assignMat)):
        print("todo #check hardware")
    else:
        if (checkRequireProvides(0, 1, 2, 3, assignMat) == 0):
            print("acquireNewMySQL")
            acquireNewMySQL = 1

    if (acquireNewMySQL):
        for column in range(len(assignMat[0])):
            sumCPU = 0
            sumMem = 0
            sumSto = 0
            for row in range(len(assignMat)):
                if (assignMat[row][column] == 1):
                    sumCPU += compLst[column].get_cpu()
                    sumMem += compLst[column].get_mem()
                    sumSto += compLst[column].get_storage()
                # Add new MySQL
                sumCPU += compLst[1].get_cpu()
                sumMem += compLst[1].get_mem()
                sumSto += compLst[1].get_storage()

                print("sumCPU ", sumCPU, "sumMem ", sumMem, "sumSto ", sumSto)
                print("vmCPU ", offersLst[VMsType[column]].get_cpu(), "vmMem ", offersLst[VMsType[column]].get_mem(),
                      "vmSto ", offersLst[VMsType[column]].get_storage())


                if not (sumCPU <= offersLst[VMsType[column]].get_cpu() and
                            sumMem <= offersLst[VMsType[column]].get_mem() and
                            sumSto <= offersLst[VMsType[column]].get_storage()) and row == len(assignMat)-1:
                        print("new VM needed")
                        return 0



        # put the new MySQL on the new VM in order not too destroy the already acquired components
        assignMat[1][len(assignMat[0]) - 1] = 1
        print("assignMat before MySQL=", assignMat)
        if (checkConflict(1, 2, assignMat) and checkConflict(1, 3, assignMat) and checkConflict(1, 4, assignMat)):
            print("setNewMySQL=1")
            setNewMySQL = 1
            sumCPU = compLst[0].get_cpu() + compLst[1].get_cpu()
            sumMem = compLst[0].get_mem() + compLst[1].get_mem()
            sumSto = compLst[0].get_storage()+ compLst[1].get_storage()
            for i in range(len(offersLst)-1, -1, -1):
                print("sumCPU ", sumCPU)
                print("sumMem ", sumMem)
                print("sumSto ", sumSto)
                print("offersLst[i].get_cpu() ", offersLst[i].get_cpu())
                print("offersLst[i].get_mem() ", offersLst[i].get_mem())
                print("offersLst[i].get_storage() ", offersLst[i].get_storage())
                if sumCPU <= offersLst[i].get_cpu() and sumMem <= offersLst[i].get_mem() and sumSto <= offersLst[i].get_storage():
                    VMsType.append(i)
                    price +=offersLst[i].get_price()/1000.
                    print("VMsType ", VMsType)
                    print("price ", price)
                    return

        else:
            # lease new machine - easy way
            assignMat[0][assignMat[0] - 1] = 0
            for arr in assignMat:
                arr.append(0)
            assignMat[1][len(assignMat[1]) - 1] = 1
            setNewMySQL = 1
            print("assignMat after MySQL=", assignMat)
    if (setNewWordpress and setNewMySQL):
        print("???", checkHardware(assignMat, VMsType, offersLst, compLst))

if __name__ == "__main__":
    opt_price = 1.777
    opt_WP3 = [
        [1, 0, 1, 0, 0, 0, 0, 1],
        [0, 0, 0, 1, 0, 1, 0, 0],
        [0, 0, 0, 0, 0, 0, 0, 0],
        [0, 1, 0, 0, 0, 0, 0, 0],
        [0, 0, 0, 0, 1, 0, 1, 0]
    ]
    # [17, 15, 17, 17, 15, 17, 15, 17] minus 1
    VMsType = [16, 14, 16, 16, 14, 16, 14, 16]
    # #offers = 20
    offers20 = [Resources(64, 976000, 1000, price=8403),
              Resources(64, 488000, 8000, price=9152),
              Resources(64, 1952, 1000, price=16000),
              Resources(32, 244000, 2000, price=4105),
              Resources(32, 244000, 4000, price=4576),
              Resources(16, 122000, 2000, price=1373),
              Resources(16, 30000, 2000, price=1430),
              Resources(17, 117000, 24000, price=5400),
              Resources(16, 122000, 1000, price=3079),
              Resources(8, 61000, 6000, price=1470),
              Resources(8, 68400, 2000, price=1301),
              Resources(8, 68400, 2000, price=1288),
              Resources(4, 15000, 2000, price=402),
              Resources(4, 30500, 3000, price=827),
              Resources(4, 30500, 1000, price=379),
              Resources(2, 7500, 1000, price=146),
              Resources(2, 3750, 2000, price=128),
              Resources(1, 1700, 1000, price=58),
              Resources(1, 3750, 1000, price=93),
              Resources(1, 3750, 1000, price=98)
              ]

    print(local_greedy(opt_price, opt_WP3, VMsType, offers20, components))




