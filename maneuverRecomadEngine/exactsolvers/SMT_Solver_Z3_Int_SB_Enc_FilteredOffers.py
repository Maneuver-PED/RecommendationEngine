from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOr import Z3_Solver_Int_Parent
from maneuverRecomadEngine.exactsolvers.ManuverSolver_SB import ManuverSolver_SB


class Z3_SolverInt_SB_Enc_FilteredOffers(Z3_Solver_Int_Parent, ManuverSolver_SB):

    def _defineVariablesAndConstraints(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding, usage vector, etc.)
        :return: None
        """
        super()._defineVariablesAndConstraints()

        # values from availableConfigurations
        self.PriceProv = [Int('PriceProv%i' % j) for j in range(1, self.nrVM + 1)]
        self.vmType = [Int('Offer%i_VM%i' % (i + 1, j + 1)) for i in range(len(self.offers_list)) for j in range(self.nrVM)]
        self.vm = [Int('VM%i' % j) for j in range(1, self.nrVM + 1)]
        self.a = [Int('C%i_VM%i' % (i + 1, j + 1)) for i in range(self.nrComp) for j in range(self.nrVM)]

        # elements of the association matrix should be just 0 or 1
        for i in range(len(self.a)):
            self.solver.add(Or([self.a[i] == 0, self.a[i] == 1]))

        for j in range(len(self.vm)):
            self.solver.add(Or([self.vm[j] == 0, self.vm[j] == 1]))
            self.solver.add(Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) >= 1, self.vm[j] == 1))

        for i in range(len(self.vmType)):
            self.solver.add(Or([self.vmType[i] == 0, self.vmType[i] == 1]))

        #self._hardware_and_offers_restrictionns(1)

    def convert_price(self, price):
        return price.as_long() / 1000.

    def _hardware_and_offers_restrictionns(self, scale_factor):
        cpu_values = {}
        memory_values = {}
        storage_values = {}
        index = 0
        for offer in self.offers_list:
            index += 1
            cpu = offer[1]
            if cpu in cpu_values:
                cpu_values[cpu].append(index)
            else:
                cpu_values[cpu] = [index]

            memory = offer[2]
            if memory in memory_values:
                memory_values[memory].append(index)
            else:
                memory_values[memory] = [index]

            storage = offer[3]
            if storage in storage_values:
                storage_values[storage].append(index)
            else:
                storage_values[storage] = [index]


        # price restrictions
        priceIndex = len(self.offers_list[0]) - 1
        for j in range(self.nrVM):
            self.solver.add(self.PriceProv[j] >= 0)
            self.solver.add(Implies(self.vm[j] == 0, self.PriceProv[j] == 0))
            self.solver.add(Implies(self.vm[j] == 1, sum([self.vmType[offer * self.nrVM + j]
                                                          for offer in range(len(self.offers_list))]) == 1))

            for offer in range(len(self.offers_list)):
                self.solver.add(Implies(self.vmType[offer*self.nrVM + j] == 1, self.PriceProv[j] ==
                                        self.offers_list[offer][priceIndex]))


        # map offers
        self.__encode_carachteristic(cpu_values, [self.problem.componentsList[i].HC for i in range(self.nrComp)], "cpu")
        self.__encode_carachteristic(memory_values, [self.problem.componentsList[i].HM for i in range(self.nrComp)], "mem")
        self.__encode_carachteristic(storage_values, [self.problem.componentsList[i].HS for i in range(self.nrComp)], "sto")

    def __encode_carachteristic(self, characteristic_values, componentsRequirements, text):
        """
        Helper function in order to encode harware constraints
        """
        print("characteristic_values", characteristic_values)
        print("componentsRequirements", componentsRequirements)
        for k in range(self.nrVM):
            keys = list(characteristic_values.keys())
            keys.sort(reverse=True)

            # calculate resources sum
            cpus_sum = Int('Comp%s_VM%i' %(text, k))
            self.solver.add(cpus_sum == sum([self.a[i * self.nrVM + k]*componentsRequirements[i]
                                             for i in range(self.nrComp)]))

            # to many components on VM (execed max offer)
            key = keys[0]
            offers_applicable = characteristic_values[key].copy()
            #print("offers_applicable", offers_applicable)
            self.solver.add(Implies(cpus_sum >= key + 1, sum([self.vmType[(offer-1) * self.nrVM + k]
                                                        for offer in offers_applicable]) == 0))

            # in bounds
            ##remove max
            keys.pop(0)
            for key in keys:
                # print(key, "offers_applicable", offers_applicable)
                values = characteristic_values[key]
                self.solver.add(Implies(cpus_sum >= key + 1, sum([self.vmType[(offer-1) * self.nrVM + k]
                                                   for offer in offers_applicable]) == 1))

                offers_applicable.extend(values)
                offers_applicable.sort()

            # lower bound
            key = keys.pop()
            self.solver.add(Implies(And([cpus_sum <= key, cpus_sum >= 1]), sum([self.vmType[(offer-1) * self.nrVM + k]
                                                     for offer in offers_applicable]) == 1))

    def RestrictionFullDeployment(self, alphaCompId, notInConflictCompsIdList):
        """
        Adds the fact that the component alphaCompId must be deployed on all machines except the ones that contain
         components that alphaCompId alpha is in conflict with
        :param alphaCompId: the component which must be fully deployed
        :param notInConflictCompsIdList: the list of components that alphaCompId is not in conflict in
        :return: None
        """
        for j in range(self.nrVM):
            self.solver.add( sum([self.a[alphaCompId * self.nrVM + j]] + [self.a[_compId * self.nrVM + j]
                                                        for _compId in notInConflictCompsIdList]) == self.vm[j])