from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_SymmBreaking import Z3_SolverSymmBreaking


class Z3_SolverIntIntSymBreak(Z3_SolverSymmBreaking):

    def _defineVariablesAndConstraints(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding, usage vector, etc.)
        :return: None
        """
        super()._defineVariablesAndConstraints()

        # values from availableConfigurations
        if self.default_offers_encoding:
            self.ProcProv = [Int('ProcProv%i' % j) for j in range(1, self.nrVM + 1)]
            self.MemProv = [Int('MemProv%i' % j) for j in range(1, self.nrVM + 1)]
            self.StorageProv = [Int('StorageProv%i' % j) for j in range(1, self.nrVM + 1)]
        self.PriceProv = [Int('PriceProv%i' % j) for j in range(1, self.nrVM + 1)]

        self.a = [Int('C%i_VM%i' % (i + 1, j + 1)) for i in range(self.nrComp) for j in range(self.nrVM)]

        # elements of the association matrix should be just 0 or 1
        for i in range(len(self.a)):
            self.solver.add(Or([self.a[i] == 0, self.a[i] == 1]))

        self.vmType = [Int('VM%iType' % j) for j in range(1, self.nrVM + 1)]

        for i in range(self.nrComp):
            for j in range(self.nrVM):
                self.solver.add(Implies(self.a[i * self.nrVM + j] == 1, Not(self.vmType[j] == 0)))

    def convert_price(self, price):
        return price.as_long() / 1000.

    def _hardware_and_offers_restrictionns(self, scale_factor):
        #price restrictions
        for j in range(self.nrVM):
            self.solver.add(self.PriceProv[j] >= 0)
            self.solver.add(
                Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) == 0, self.PriceProv[j] == 0))

        #map vm to type
        priceIndex = len(self.offers_list[0]) - 1
        for vm_id in range(self.nrVM):
            index = 0
            for offer in self.offers_list:
                index += 1
                price = offer[priceIndex] if int(scale_factor) == 1 else offer[priceIndex] / scale_factor
                self.solver.add(
                    Implies(And(sum([self.a[i + vm_id] for i in range(0, len(self.a), self.nrVM)]) >= 1,
                                self.vmType[vm_id] == index),
                            And(self.PriceProv[vm_id] == price,
                                self.ProcProv[vm_id] == offer[1],
                                self.MemProv[vm_id] == (
                                offer[2] if int(scale_factor) == 1 else offer[2] / scale_factor),
                                self.StorageProv[vm_id] == (
                                offer[3] if int(scale_factor) == 1 else offer[3] / scale_factor)
                                )
                            ))
            lst = [self.vmType[vm_id] == offerID for offerID in range(1, len(self.offers_list)+1)]
            self.solver.add(Or(lst))

        #map hardware
        tmp = []
        for k in range(self.nrVM):
            tmp.append(
                sum([self.a[i * self.nrVM + k] * (self.problem.componentsList[i].HC) for i in range(self.nrComp)]) <=
                self.ProcProv[k])
            tmp.append(sum([self.a[i * self.nrVM + k] * ((
                self.problem.componentsList[i].HM if int(scale_factor) == 1 else
                self.problem.componentsList[i].HM / scale_factor)) for i in range(self.nrComp)]) <=
                       self.MemProv[k])
            tmp.append(sum([self.a[i * self.nrVM + k] * ((
                self.problem.componentsList[i].HS if int(scale_factor) == 1 else
                self.problem.componentsList[i].HS / scale_factor)) for i in range(self.nrComp)]) <=
                       self.StorageProv[k])
        self.solver.add(tmp)