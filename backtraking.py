import time

class Resources:
    def __init__(self, cpu, memory, storage, pret=0):
        self.mem = memory
        self.cpu = cpu
        self.storage = storage
        self.pret = pret
# components hardware spec
components = {1: Resources(2, 512, 1000), 2: Resources(2, 512, 2000), 3: Resources(4, 2048, 500),
              4: Resources(4, 2048, 500), 5: Resources(4, 4000, 500)}
map_resurse = {}
min_val = 100000000000
min_sol = []

def BT2(i, j, rez, s):
    global min_val
    global min_sol
    # print("i=",i,"j=",j)
    if (i == nrComponents) and (j == nrVM):
        if (validFinal(s) == True):
            # # print("1. ", sumaLinie(s, j, 0))
            # # print("2. ", sumaLinie(s, j, 1))
            # print("***", 2 * sumaLinie(s, j, 0) > 3 * sumaLinie(s, j, 1))
            #
            # #2,1<=3,2
            #
            # if (not((2 * sumaLinie(s, j, 0) )> (3 * sumaLinie(s, j, 1)))):
            #     print("constraint 3: failed")
            #     return

            # if sumaLinie(s, j, 2) >= 1 and ((sumaLinie(s, j, 3) >= 1 or sumaLinie(s, j, 4) >= 1)):
            #     # print("validContinuare: constraint 4 failed")
            #     return

            if not(sumaLinie(s, j, 2) == 0 and ((sumaLinie(s, j, 3) >= 1 and sumaLinie(s, j, 4) >= 1))):
                #print("validContinuare: constraint 4 failed")
                return

            # if (sumaLinie(s, j, 2) == 0 and ((sumaLinie(s, j, 3) == 1 and sumaLinie(s, j, 4) >= 0))):
            #     #print("validContinuare: constraint 4 failed")
            #     return

            a = eval_solutie(s);
            if a < min_val:
                min_val = a
                min_sol = [x[:] for x in s]

            # print("SOLUTION:", sumaLinie(s, j, 0), "*", sumaLinie(s, j, 1), "*", s)
            # #rez.append([x[:] for x in s])
            # print("Price: ", eval_solutie(s))
    else:
        i0 = i
        j0 = j
        s[i][j] = 0
        for k in range(i + 1, nrComponents):
            s[k][j] = 0
        for klin in range(0, nrComponents):
            for kcol in range(j + 1, nrVM):
                s[klin][kcol] = 0
        if (validContinuare(s, i, j) == True):
            if (i == nrComponents - 1):
                j = j + 1
                if (j < nrVM):
                    i = 0
                else:
                    i = nrComponents
            else:
                i = i + 1
            BT2(i, j, rez,s)
        i = i0
        j = j0
        for k in range(i + 1, nrComponents):
            s[k][j] = 0
        for klin in range(0, nrComponents):
            for kcol in range(j + 1, nrVM):
                s[klin][kcol] = 0
        s[i][j] = 1
        if (validContinuare(s, i, j) == True):
            if (i == nrComponents - 1):
                j = j + 1
                if (j < nrVM):
                    i = 0
                else:
                    i = nrComponents
            else:
                i = i + 1
            BT2(i, j, rez,s)


def sumaLinie(s, nrcol, ilin):
    suma = 0
    for j in range(nrcol):
        suma = suma + s[ilin][j]
    return suma


def validContinuare(s, i, j):
    # constraint 4
    if sumaLinie(s, j, 2) >= 1 and ((sumaLinie(s, j, 3) >= 1 or sumaLinie(s, j, 4) >= 1)):
        #print("validContinuare: constraint 4 failed")
        return False

    if (sumaLinie(s, j, 2) == 0 and ((sumaLinie(s, j, 3) >= 1 and sumaLinie(s, j, 4) == 0))):
        #print("validContinuare: constraint 4 failed")
        return False

    if (sumaLinie(s, j, 2) == 0 and ((sumaLinie(s, j, 3) == 1 and sumaLinie(s, j, 4) >= 0))):
        #print("validContinuare: constraint 4 failed")
        return False

    # constraint 8
    if sumaLinie(s, j, 2) > 1:
        # print("validContinuare: constraint 8 failed")
        return False
    # constraints 5, 9
    for k in range(j):
        if (s[4][k] + s[1][k] > 1) or (s[4][k] + s[2][k] > 1) or (s[4][k] + s[3][k] > 1) or \
                (s[2][k] + s[0][k] > 1) or (s[2][k] + s[1][k] > 1) or (s[2][k] + s[4][k] > 1) or \
                (s[3][k] + s[0][k] > 1) or (    s[3][k] + s[1][k] > 1) or (s[3][k] + s[4][k] > 1):
            # print("validContinuare: constraint 5, 9 failed")
            return False
    return True


def validFinal(s):
    n = len(s)
    m = len(s[0])
    # print("validFinal:", s)
    # constraint 1
    if sumaLinie(s, m, 2) > 7 * sumaLinie(s, m, 0):
        # print("constraint 1: failed")
        return False
    # constraint 2
    if sumaLinie(s, m, 3) > 3 * sumaLinie(s, m, 0):
        # print("constraint 2: failed")
        return False
    # constraint 3
    if 2 * sumaLinie(s, m, 0) > 3 * sumaLinie(s, m, 1):
        # print("constraint 3: failed")
        return False
    # constraint 4
    if sumaLinie(s, m, 2) > 0 and ((sumaLinie(s, m, 3) > 0 or sumaLinie(s, m, 4) > 0)):
        # print("constraint 4: failed")
        return False
    # constraint 5
    for k in range(m):
        if (s[4][k] + s[1][k] > 1) or (s[4][k] + s[2][k] > 1) or (s[4][k] + s[3][k] > 1):
            # print("constraint 5: failed")
            return False
    # constraint 6
    if sumaLinie(s, m, 4) < 2:
        # print("constraint 6: failed")
        return False
    # constraint 7
    if sumaLinie(s, m, 1) < 2:
        # print("constraint 7: failed")
        return False
    # constraint 8
    if sumaLinie(s, m, 2) > 1:
        # print("constraint 8: failed")
        return False
    # constraint 9
    for k in range(m):
        if (s[2][k] + s[0][k] > 1) or (s[2][k] + s[1][k] > 1) or (s[2][k] + s[4][k] > 1):
            # print("constraint 9: failed")
            return False
    for k in range(m):
        if (s[3][k] + s[0][k] > 1) or (s[3][k] + s[1][k] > 1) or (s[3][k] + s[4][k] > 1):
            # print("constraint 9: failed")
            return False
    # nr WordPress
    if sumaLinie(s, m, 0) != nrWordpress:
        # print("constraint 10: failed")
        return False
    # print("valid")
    return True

def eval_solutie(sol):
    nr_comp = len(sol)
    nr_vm =len(sol[0])
    pret_final = 0;
    for j in range(nr_vm):
        cpus = 0
        mems = 0
        sts = 0
        for i in range(nr_comp):
            if sol[i][j] == 1:
                cpus += components[i+1].cpu
                mems += components[i+1].mem
                sts += components[i+1].storage
        #print(cpus, mems, sts)
        lista_preturi =[]
        if cpus > 0:
            for cpu, map_mem in map_resurse.items():
                if cpus <= cpu:
                    for mem, st_map  in map_mem.items():
                        if mems <= mem:
                            for st, preturi in st_map.items():
                                if sts <= st:
                                    lista_preturi.extend(preturi)
            pret_final += min(lista_preturi)
        #print(cpus, mems, sts, lista_preturi)
    #print(pret_final)
    return pret_final



if __name__ == "__main__":
    # #offers = 20
    offers = [Resources(64, 976000, 1000, pret=8403),
              Resources(64, 488000, 8000, pret=9152),
              Resources(64, 1952, 1000, pret=16000),
              Resources(32, 244000, 2000, pret=4105),
              Resources(32, 244000, 4000, pret=4576),
              Resources(16, 122000, 2000, pret=1373),
              Resources(16, 30000, 2000, pret=1430),
              Resources(17, 117000, 24000, pret=5400),
              Resources(16, 122000, 1000, pret=3079),
              Resources(8, 61000, 6000, pret=1470),
              Resources(8, 68400, 2000, pret=1301),
              Resources(8, 68400, 2000, pret=1288),
              Resources(4, 15000, 2000, pret=402),
              Resources(4, 30500, 3000, pret=827),
              Resources(4, 30500, 1000, pret=379),
              Resources(2, 7500, 1000, pret=146),
              Resources(2, 3750, 2000, pret=128),
              Resources(1, 1700, 1000, pret=58),
              Resources(1, 3750, 1000, pret=93),
              Resources(1, 3750, 1000, pret=98)
              ]

    for oferta in offers:
        if map_resurse.get(oferta.cpu) is None:
            map_resurse[oferta.cpu] = {oferta.mem: {oferta.storage: [oferta.pret]}}
        else:
            _map = map_resurse.get(oferta.cpu)
            if _map.get(oferta.mem) is None:
                _map[oferta.mem] = {oferta.storage: [oferta.pret]}
            else:
                __map = _map.get(oferta.mem)
                if __map.get(oferta.storage) is None:
                    __map[oferta.storage] = [oferta.pret]
                else:
                    __map.get(oferta.storage).append(oferta.pret)


    nrComponents = 5
    nrWordpress = 3
    nrVM = 8
    rez = []
    s = [[0 for j in range(nrVM)] for i in range(nrComponents)]
    nrSol = 0
    tStart = time.time()
    print(BT2(0, 0, rez, s))
    tEnd = time.time()

    # time in seconds
    print("time=", tEnd - tStart)
    #print(rez)
    print("min_sol ", min_sol)
    print("min_val ", min_val)

    #caracteristici componente

    # for k,v in map_resurse.items():
    #     print(k,v)

    #solutie = [[0, 0, 0, 0, 0, 1, 1, 1], [0, 0, 0, 1, 1, 1, 1, 1], [0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0]]

    #eval_solutie(solutie, map_resurse, componete)
    # [0, 0, 0, 1, 0, 1, 0, 1]
    # [1, 0, 0, 0, 1, 0, 0, 0]
    # [0, 0, 0, 0, 0, 0, 0, 0]
    # [0, 0, 1, 0, 0, 0, 0, 0]
    # [0, 1, 0, 0, 0, 0, 1, 0]




