import time

class Resources:
    def __init__(self, cpu, memory, storage, price=0):
        self.mem = memory
        self.cpu = cpu
        self.storage = storage
        self.price = price

def get_mem(resource):
    return resource.mem

def get_storage(resource):
    return resource.storage

def get_cpu(resource):
    return resource.cpu

def get_price(resource):
    return resource.price


# components hardware spec
components = [Resources(2, 512, 1000), #wordpress
              Resources(2, 512, 2000), #mysql
              Resources(4, 2048, 500), #DNSloadbalancer
              Resources(4, 2048, 500), #HTTPloadbalancer
              Resources(4, 4000, 500)] #Varnish
map_resurse = {}
min_val = 100000000000
min_sol = []

def binpacking(components, offers):
    a = []
    for i in range (len(components)):
        a.append([0]*len(components))
    K = [0] * len(components)
    S = [0] * len(components)
    k = 0
    i = 0
    while (k < len(offers) and i < len(components)-1):#offers
        print("offer ", offers[k].cpu, " ", offers[k].mem, " ", offers[k].storage)
        for i in range(len(components)):#components
            j = 0
            while (S[j] + components[i].cpu > offers[k].cpu):
                k = k+1
            a[j][K[j]] = components[i].cpu
            S[j] = S[j] + components[i].cpu
            K[j] = K[j] + 1
    return a

if __name__ == "__main__":
    # #offers = 20
    offers = [Resources(64, 976000, 1000, price=8403),
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
    print("sort offers decreasing by price")
    #sort offers increasing by price
    offers.sort(key=get_price, reverse=True)
    for offer in offers:
        print(offer.cpu, " ", offer.mem, " ", offer.storage, " ", offer.price)
    # First Fit Decreasing
    print("sort components decreasing by cpu")
    components.sort(key=get_cpu, reverse=True)
    for component in components:
        print(component.cpu, " ", component.mem, " ", component.storage)

    print("result=", binpacking(components, offers))