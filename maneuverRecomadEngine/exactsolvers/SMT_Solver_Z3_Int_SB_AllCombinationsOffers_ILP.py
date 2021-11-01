from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOr_ILP import Z3_Solver_Int_Parent_ILP
from maneuverRecomadEngine.exactsolvers.ManuverSolver_SB_ILP import ManuverSolver_SB_ILP

class Z3_SolverInt_SB_Enc_AllCombinationsOffers_ILP(Z3_Solver_Int_Parent_ILP, ManuverSolver_SB_ILP):

    def _defineVariablesAndConstraints(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding, usage vector, etc.)
        :return: None
        """
        super()._defineVariablesAndConstraints()

        self.ProcProv = []
        self.MemProv = []
        self.StorageProv = []
        self.PriceProv = []

        if self.default_offers_encoding:
            for i in range(len(self.offers_list)):
                self.ProcProv.append(self.offers_list[i][1])
                self.MemProv.append(self.offers_list[i][2])
                self.StorageProv.append(self.offers_list[i][3])
                self.PriceProv.append(self.offers_list[i][4])

        print("ProcProv ", self.ProcProv)
        print("MemProv ", self.MemProv)
        print("StorageProv ", self.StorageProv)
        print("PriceProv ", self.PriceProv)

        # values from availableConfigurations
        # if self.default_offers_encoding:
        #     self.ProcProv = [Int('ProcProv%i' % j) for j in range(1, self.nrVM + 1)]
        #     self.MemProv = [Int('MemProv%i' % j) for j in range(1, self.nrVM + 1)]
        #     self.StorageProv = [Int('StorageProv%i' % j) for j in range(1, self.nrVM + 1)]
        # self.PriceProv = [Int('PriceProv%i' % j) for j in range(1, self.nrVM + 1)]

        self.a = [Int('C%i_VM%i_T%i' % (i + 1, j + 1, k + 1))
                  for k in range(self.nrOffers) for j in range(self.nrVM) for i in range(self.nrComp)  ]
        self.v = [Int('VM%i_T%i' % (j + 1, k + 1)) for k in range(self.nrOffers) for j in range(self.nrVM) ]

        print("a=", self.a)
        print("v=", self.v)


        # elements of the association matrix should be just 0 or 1
        for i in range(len(self.a)):
            self.solver.add(Or([self.a[i] == 0, self.a[i] == 1]))
        # elements of the occupancy vector should be just 0 or 1
        for i in range(len(self.v)):
            self.solver.add(Or([self.v[i] == 0, self.v[i] == 1]))

        #self.vmType = [Int('VM%iType' % j) for j in range(1, self.nrVM + 1)]

        # for i in range(self.nrComp):
        #     for j in range(self.nrVM):
        #         self.solver.add(Implies(self.a[i * self.nrVM + j] == 1, Not(self.vmType[j] == 0)))

    def convert_price(self, price):
        return price / 1000.

    def _hardware_and_offers_restrictionns(self, scale_factor):
        #price restrictions
        # for j in range(self.nrVM):
        #     self.solver.add(self.PriceProv[j] >= 0)
        #     self.solver.add(
        #         Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) == 0, self.PriceProv[j] == 0))

        # #map vm to type
        # priceIndex = len(self.offers_list[0]) - 1
        # for vm_id in range(self.nrVM):
        #     index = 0
        #     for offer in self.offers_list:
        #         index += 1
        #         price = offer[priceIndex] if int(scale_factor) == 1 else offer[priceIndex] / scale_factor
        #         self.solver.add(
        #             Implies(And(sum([self.a[i + vm_id] for i in range(0, len(self.a), self.nrVM)]) >= 1,
        #                         self.vmType[vm_id] == index),
        #                     And(self.PriceProv[vm_id] == price,
        #                         self.ProcProv[vm_id] == offer[1],
        #                         self.MemProv[vm_id] == (
        #                         offer[2] if int(scale_factor) == 1 else offer[2] / scale_factor),
        #                         self.StorageProv[vm_id] == (
        #                         offer[3] if int(scale_factor) == 1 else offer[3] / scale_factor)
        #                         )
        #                     ))
        #     lst = [self.vmType[vm_id] == offerID for offerID in range(1, len(self.offers_list)+1)]
        #     self.solver.add(Or(lst))

        #map hardware
        # tmp = []
        # for k in range(self.nrVM):
        #     tmp.append(
        #         sum([self.a[i * self.nrVM + k] * (self.problem.componentsList[i].HC) for i in range(self.nrComp)]) <=
        #         self.ProcProv[k])
        #     tmp.append(sum([self.a[i * self.nrVM + k] * ((
        #         self.problem.componentsList[i].HM if int(scale_factor) == 1 else
        #         self.problem.componentsList[i].HM / scale_factor)) for i in range(self.nrComp)]) <=
        #                self.MemProv[k])
        #     tmp.append(sum([self.a[i * self.nrVM + k] * ((
        #         self.problem.componentsList[i].HS if int(scale_factor) == 1 else
        #         self.problem.componentsList[i].HS / scale_factor)) for i in range(self.nrComp)]) <=
        #                self.StorageProv[k])
        # self.solver.add(tmp)

        # A machine can have only one type
        tmp = []
        for k in range(self.nrVM):
            print("A machine can have only one type:", sum([self.v[i * self.nrVM + k] for i in range(self.nrOffers)]) <= 1)
            tmp.append(sum([self.v[i * self.nrVM + k] for i in range(self.nrOffers)]) <= 1)
        self.solver.add(tmp)

        # capacity constraints
        tmp = []
        for o in range(self.nrOffers):
            for k in range(self.nrVM):
                print("???", sum([self.a[i + self.nrVM*k] * (self.problem.componentsList[i].HC) for i in range(self.nrComp)])
                      <= self.ProcProv[o] #*self.v[j] for j in range(self.nrVM)
        )

        #     # tmp.append(
        #     #     sum([self.a[i * self.nrVM + k] * (self.problem.componentsList[i].HC) for i in range(self.nrComp)]) <=
        #     #     self.ProcProv[k])
        #     # tmp.append(sum([self.a[i * self.nrVM + k] * ((
        #     #     self.problem.componentsList[i].HM if int(scale_factor) == 1 else
        #     #     self.problem.componentsList[i].HM / scale_factor)) for i in range(self.nrComp)]) <=
        #     #            self.MemProv[k])
        #     # tmp.append(sum([self.a[i * self.nrVM + k] * ((
        #     #     self.problem.componentsList[i].HS if int(scale_factor) == 1 else
        #     #     self.problem.componentsList[i].HS / scale_factor)) for i in range(self.nrComp)]) <=
        #     #            self.StorageProv[k])
        # #self.solver.add(tmp)