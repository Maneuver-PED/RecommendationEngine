from z3 import *
from maneuverRecomadEngine.exactsolvers.ManuverSolver import ManuverSolver
import time

class Z3_Solver_Parent(ManuverSolver):#ManeuverProblem):

    def _initSolver(self):
        """
        Initializes the solver
        :return: None
        """
        if self.solverTypeOptimize:
            self.solver = Optimize()
        else:
            self.solver = Solver()
            self.solver.set(unsat_core=True)
            self.labelIdx = 0
            self.labelIdx_oneToOne = 0
            self.labelIdx_offer = 0
            self.labelIdx_conflict = 0

        self.vmIds_for_fixedComponents = set()
        self._defineVariablesAndConstraints()

    def _defineVariablesAndConstraints(self):
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        self.vm = {}
        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        self.a = {}
        # VMType  - type of a leased VM
        self.VMType = {}


    def _simetry_breaking(self):
        max_id = -1
        for vmid in self.vmIds_for_fixedComponents:
            if max_id < vmid:
                max_id = vmid

        if self.sb_vms_order_by_price:
            print("add price?", self.sb_vms_order_by_price, "max_id: ", max_id)
            for j in range(max_id + 1, self.nrVM - 1):
                print(self.PriceProv[j] >= self.PriceProv[j + 1])
                self.solver.add(self.PriceProv[j] >= self.PriceProv[j + 1])

        if self.sb_vms_order_by_components_number:
            for j in range(max_id + 1, self.nrVM - 1):
                self.solver.add(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) >= sum(
                    [self.a[i + j + 1] for i in range(0, len(self.a), self.nrVM)]))


        #k=0
        for j in range(self.nrVM - 1):
            if self.sb_redundant_price:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j + 1],
                                        self.PriceProv[j] == self.PriceProv[j + 1]))
            if self.sb_redundant_processor:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                        self.ProcProv[j] == self.ProcProv[j + 1]))
            if self.sb_redundant_memory:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                    self.MemProv[j] >= self.MemProv[j + 1]))
            if self.sb_redundant_storage:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                    self.StorageProv[j] == self.StorageProv[j + 1]))


            # #Sym br type 3 - 1
            if self.sb_equal_vms_type_order_by_components_number:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                    sum([self.a[i+j] for i in range(0, len(self.a), self.nrVM)]) >=
                                      sum([self.a[i+j+1] for i in range(0, len(self.a), self.nrVM)])))
            # Sym br type 3 - 2
            if self.sb_equal_vms_type_order_lex:
                for i in range(0, self.nrComp):
                    l= [self.a[u*self.nrVM + j] == self.a[u*self.nrVM + j+1] for u in range(0,i)]
                    l.append(self.vmType[j] == self.vmType[j+1])
                    self.solver.add(Implies(And(l), self.a[i*self.nrVM + j] >= self.a[i*self.nrVM + j+1]))


    def RestrictionPriceOrder(self, start_vm_id, end_vm_id):

        print("PriceOrder Z3", start_vm_id, end_vm_id)
        if self.sb_vms_order_by_price:
            for j in range(start_vm_id, end_vm_id-1):
                self.solver.add(self.PriceProv[j] >= self.PriceProv[j + 1])


    def RestrictionFixComponentOnVM(self, comp_id, vm_id, value):
        """
        Force placing component on a specific VM
        :param comp_id: the ID of the component
        :param vm_id: the ID of the VM
        :return: None
        """
        if not self.sb_fix_variables:
            return
        if value == 1:
            if self.solverTypeOptimize:
                self.solver.add(self.a[comp_id * self.nrVM + vm_id] == 1)
                for compId in self.problem.componentsList[comp_id].conflictComponentsList:
                    self.solver.add(self.a[compId * self.nrVM + vm_id] == 0)

            else:
                self.solver.assert_and_track(self.a[comp_id * self.nrVM + vm_id] == 1, "Label: " + str(self.labelIdx))
                self.labelIdx += 1
        else:
            self.solver.add(self.a[comp_id * self.nrVM + vm_id] == 0)
        # self.__addPriceOffer(comp_id, vm_id)
        self.vm_with_offers[vm_id] = comp_id
        self.vmIds_for_fixedComponents.add(vm_id)

    def _encodeOffers(self, scale_factor):

        print("scale_falctor",scale_factor)
        # encode offers
        for j in range(self.nrVM):
            self.solver.add(self.PriceProv[j] >= 0)

        if self.use_vm_vector_in_encoding:
            for i in range(self.nrVM):
                if self.solverTypeOptimize:
                    self.solver.add(Implies(self.vm[i] == 0, self.PriceProv[i] == 0))
                else:
                    self.solver.assert_and_track(Implies(self.vm[i] == 0, self.PriceProv[i] == 0), "Label: " + str(self.labelIdx))
                    self.labelIdx += 1
        else:
            for j in range(self.nrVM):
                self.solver.add(Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) == 0, self.PriceProv[j] == 0))

        priceIndex = len(self.offers_list[0]) - 1
        print("price Index", self.offers_list[0], priceIndex)
        print("price Index", self.offers_list[1], priceIndex)
        for vm_id in range(self.nrVM):
            index = 0
            availableOffers = []
            for offer in self.offers_list:
                index += 1
                addOffer = True
                if self.offers_list_filtered:
                    if vm_id in self.vm_with_offers:
                        # testez daca oferta e aplicabila
                        comp_id = self.vm_with_offers[vm_id]
                        if offer[1] < self.problem.componentsList[comp_id].HC:
                            addOffer = False
                        elif offer[2] < self.problem.componentsList[comp_id].HM:
                            addOffer = False
                        elif offer[3] < self.problem.componentsList[comp_id].HS:
                            addOffer = False
                if addOffer:
                    availableOffers.append(index)


                    if self.use_vm_vector_in_encoding:
                        if self.solverTypeOptimize:
                            self.solver.add(
                                Implies(And(self.vm[vm_id] == 1, self.vmType[vm_id] == index),
                                        And(self.PriceProv[vm_id] == (offer[priceIndex] if int(scale_factor) == 1 else offer[priceIndex] / scale_factor),
                                            self.ProcProv[vm_id] == offer[1],
                                            self.MemProv[vm_id] == (offer[2] if int(scale_factor) == 1 else offer[2] / scale_factor),
                                            self.StorageProv[vm_id] == (offer[3] if int(scale_factor) == 1 else offer[3] / scale_factor)
                                            )
                                ))
                        else:
                            self.solver.assert_and_track(
                                Implies(And(self.vm[vm_id] == 1, self.vmType[vm_id] == index),
                                        And(self.PriceProv[vm_id] == (offer[priceIndex] if int(scale_factor)==1 else offer[priceIndex]/ scale_factor),
                                             self.ProcProv[vm_id] == offer[1],
                                             self.MemProv[vm_id] == (offer[2] if int(scale_factor) ==1 else offer[2] / scale_factor),
                                             self.StorageProv[vm_id] == (offer[3] if int(scale_factor) ==1 else offer[3] / scale_factor)
                                            )
                                ), "Label: " + str(self.labelIdx))
                            self.labelIdx += 1
                    else:
                        price = offer[priceIndex] if int(scale_factor) == 1 else offer[priceIndex] / scale_factor
                        self.solver.add(
                            Implies(And(sum([self.a[i + vm_id] for i in range(0, len(self.a), self.nrVM)]) >= 1,
                                        self.vmType[vm_id] == index),
                                    And(self.PriceProv[vm_id] == price,
                                        self.ProcProv[vm_id] == offer[1],
                                        self.MemProv[vm_id] == (offer[2] if int(scale_factor) == 1 else offer[2] / scale_factor),
                                        self.StorageProv[vm_id] == (offer[3] if int(scale_factor) == 1 else offer[3] / scale_factor)
                                        )
                                    ))

            lst = [self.vmType[vm_id] == offerID for offerID in availableOffers]
            self.solver.add(Or(lst))


    def RestrictionConflict(self, alphaCompId, conflictCompsIdList):
        """
        Constraint describing the conflict between components. The 2 params. should not be placed on the same VM
        :param alphaCompId: id of the first conflict component
        :param conflictCompsIdList: id of the second conflict component
        :return: None
        """

        print("restriction conflictCompsIdList ", alphaCompId, conflictCompsIdList)

        self.problem.logger.debug(
            "RestrictionConflict: alphaCompId = {} conflictComponentsList = {}".format(alphaCompId,
                                                                                       conflictCompsIdList))

        for j in range(self.nrVM):
            for conflictCompId in conflictCompsIdList:
                # self.problem.logger.debug("...{} <= 1".format([self.a[alphaCompId * self.nrVM + j], self.a[conflictCompId * self.nrVM + j]]))
                if self.solverTypeOptimize:
                    self.solver.add(sum([self.a[alphaCompId * self.nrVM + j],
                                         self.a[conflictCompId * self.nrVM + j]]) <= 1)
                else:
                    self.solver.assert_and_track(
                        sum([self.a[alphaCompId * self.nrVM + j], self.a[conflictCompId * self.nrVM + j]]) <= 1,
                        "LabelConflict: " + str(self.labelIdx_conflict))
                    self.labelIdx_conflict += 1

    def RestrictionOneToOneDependency(self, alphaCompId, betaCompId):
        """
        Contraint describing that alphaCompId and betaCompId should be deployed on the same VM
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return: None
        """
        for j in range(self.nrVM):
            if self.solverTypeOptimize:
                self.solver.add(
                    self.a[alphaCompId * self.nrVM + j] == self.a[betaCompId * self.nrVM + j])
            else:
                self.solver.assert_and_track(
                    self.a[alphaCompId * self.nrVM + j] == self.a[betaCompId * self.nrVM + j],
                    "LabelOneToOne" + str(self.labelIdx))
                self.labelIdx_oneToOne += 1

    def RestrictionManyToManyDependency(self, alphaCompId, betaCompId, relation):
        """
        The number of instances of component alphaCompId depends on the number of instances of component betaCompId
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param relation: one of the strings in the set {"=", "<=", ">="}
            "=": sum(instances of alpha component) == sum(instances of beta component)
            "<=": sum(instances of alpha component) <= sum(instances of beta component)
            ">=": sum(instances of alpha component) >= sum(instances of beta component)
        :return: None
        """
        if relation == "<=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <=
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
            else:
                self.solver.assert_and_track(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <=
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]), "LabelManyToMany1: " + str(self.labelIdx))
                self.labelIdx += 1
        elif relation == ">=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >=
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
            else:
                self.solver.assert_and_track(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >=
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]), "LabelManyToMany2: " + str(self.labelIdx))
                self.labelIdx += 1
        elif relation == "=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) ==
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
            else:
                self.solver.assert_and_track(
                    sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) ==
                    sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]), "LabelManyToMany3: " + str(self.labelIdx))
                self.labelIdx += 1

    def RestrictionOneToManyDependency(self, alphaCompId, betaCompId, noInstances):
        """
        At each alphaCompId component should be deployed noInstances betaCompId components
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param noInstances: depending instances number
        :return: None
        """
        if self.solverTypeOptimize:
            self.solver.add(
                noInstances * sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
                              sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) > 0)
        else:
            self.solver.assert_and_track(
                noInstances * sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
                              sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) > 0, "LabelOneToMany: " + str(self.labelIdx))
            self.labelIdx += 1

        if self.solverTypeOptimize:
            self.solver.add(
                noInstances * sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
                              sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) <= noInstances)
        else:
            self.solver.assert_and_track(
                noInstances * sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
                              sum([self.a[betaCompId  * self.nrVM + j] for j in range(self.nrVM)]) <= noInstances, "LabelOneToMany: " + str(self.labelIdx))
            self.labelIdx += 1

    def RestrictionUpperLowerEqualBound(self, compsIdList, bound, operator):
        """
        Defines an upper/lower/equal bound on the number of instances that a component must have
        :param compsIdList: list of components
        :param bound: a positive number
        :param operator: <=, >=, =
            "<=": sum(compsIdList) <= bound
            ">=": sum(compsIdList) >= bound
            "==":  sum(compsIdList) == bound
        :return: None
        """

        self.problem.logger.debug("RestrictionUpperLowerEqualBound: {} {} {} ".format(compsIdList, operator, bound))

        if operator == "<=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)])
                    <= bound)
            else:
                self.__constMap[str("LabelUpperLowerEqualBound" + str(self.labelIdx))] = sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) <= bound
                self.solver.assert_and_track(
                    sum([If(self.a[compId * self.nrVM + j], 1, 0) for compId in compsIdList for j in range(self.nrVM)]) <= bound, "LabelUpperLowerEqualBound" + str(self.labelIdx))
                self.labelIdx += 1
        elif operator == ">=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) >= bound)
            else:
                self.__constMap[str("LabelUpperLowerEqualBound" + str(self.labelIdx))] = sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) >= bound
                self.solver.assert_and_track(
                    sum([If(self.a[compId * self.nrVM + j], 1, 0) for compId in compsIdList for j in range(self.nrVM)]) >= bound, "LabelUpperLowerEqualBound" + str(self.labelIdx))
                self.labelIdx += 1
        elif operator == "=":
            if self.solverTypeOptimize:
                self.solver.add(
                    sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) == bound)
            else:
                self.__constMap[str("LabelUpperLowerEqualBound" + str(self.labelIdx))] = sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) == bound

                self.solver.assert_and_track(
                    sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) == bound, "LabelUpperLowerEqualBound" + str(self.labelIdx))
                self.labelIdx += 1
        else:
            self.problem.logger.info("Unknown operator")

    def RestrictionRangeBound(self, compsIdList, lowerBound, upperBound):
        """
        Defines a lower and upper bound of instances that a component must have
        :param compsIdList: list of components
        :param lowerBound: a positive number
        :param upperBound: a positive number
        :return:
        """
        for i in range(len(compsIdList)): compsIdList[i] -= 1
        if self.solverTypeOptimize:
            self.solver.add(sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) >= lowerBound)
        else:
            self.solver.assert_and_track(
                sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) >= lowerBound, "LabelRangeBound: " + str(self.labelIdx))
            self.labelIdx += 1
        if self.solverTypeOptimize:
            self.solver.add(sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) <= upperBound)
        else:
            self.solver.assert_and_track(
                sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) <= upperBound, "LabelRangeBound: " + str(self.labelIdx))
            self.labelIdx += 1

    def RestrictionFullDeployment(self, alphaCompId, notInConflictCompsIdList):
        """
        Adds the fact that the component alphaCompId must be deployed on all machines except the ones that contain
         components that alphaCompId alpha is in conflict with
        :param alphaCompId: the component which must be fully deployed
        :param notInConflictCompsIdList: the list of components that alphaCompId is not in conflict in
        :return: None
        """
        for j in range(self.nrVM):
            if self.use_vm_vector_in_encoding:
                if self.solverTypeOptimize:
                    self.solver.add(
                        sum([self.a[alphaCompId * self.nrVM + j]] + [self.a[_compId * self.nrVM + j] for _compId in
                                                                     notInConflictCompsIdList]) == self.vm[j])
                else:
                    self.solver.assert_and_track(
                        sum([self.a[alphaCompId * self.nrVM + j]] + [self.a[_compId * self.nrVM + j] for _compId in
                                                                     notInConflictCompsIdList]) == self.vm[j],
                        "LabelFullDeployment: " + str(self.labelIdx))
                    self.labelIdx += 1
            else:
                if self.solverTypeOptimize:
                    self.solver.add(
                        (sum([self.a[alphaCompId * self.nrVM + j]] + [self.a[_compId * self.nrVM + j] for _compId in
                                                                      notInConflictCompsIdList]))
                        ==
                        (If(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) >= 1, 1, 0)))
                else:
                    self.solver.assert_and_track(
                        (sum(
                            [If(self.a[alphaCompId * self.nrVM + j], 1, 0)] + [If(self.a[_compId * self.nrVM + j], 1, 0)
                                                                               for _compId in
                                                                               notInConflictCompsIdList])) ==
                        (sum([If(self.a[i + j], 1, 0) for i in range(0, len(self.a), self.nrVM)]) >= 1),
                        "LabelFullDeployment: " + str(self.labelIdx)
                    )
                    self.labelIdx += 1

    def RestrictionRequireProvideDependency(self, alphaCompId, betaCompId, alphaCompIdInstances, betaCompIdInstances):
        """
        The number of instances of component alpha depends on the number of instances of component beta
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param alphaCompIdInstances: number of instances of component alphaCompId
        :param betaCompIdInstances: number of instances of component betaCompId
        :return: None
        """
        # self.problem.logger.debug("RestrictionRequireProvideDependency: alphaCompId={}, betaCompId={}, alphaCompIdInstances={}, "
        #                          "betaCompIdInstances={}".format(alphaCompId, betaCompId, alphaCompIdInstances, betaCompIdInstances))

        if self.solverTypeOptimize:
            self.solver.add(
                alphaCompIdInstances * sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <=
                betaCompIdInstances * sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
        else:
            self.__constMap["LabelRequireProvide: " + str(self.labelIdx)] = \
                alphaCompIdInstances * sum([If(self.a[alphaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) \
                <= \
                betaCompIdInstances * sum([If(self.a[betaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)])
            self.solver.assert_and_track(
                alphaCompIdInstances * sum([If(self.a[alphaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) <=
                betaCompIdInstances * sum([If(self.a[betaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]),
                "LabelRequireProvide: " + str(self.labelIdx))
            self.labelIdx += 1
    def RestrictionAlphaOrBeta(self, alphaCompId, betaCompId):
        """
        Describes the fact that alphaCompId or betaCompId not both
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return:
        """
        self.problem.logger.debug("RestrictionAlphaOrBeta: alphaCompId={}, betaCompId={}".format(alphaCompId, betaCompId))
        if self.solverTypeOptimize:
            self.solver.add(Or(sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) == 0,
                               sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) >= 1))

            self.solver.add(Or(sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) == 0,
                               sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >= 1))

            self.solver.add(sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) +
                            sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >= 1)

            # self.solver.add(
            #     Xor(sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) == 0,
            #         sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) == 0, True))
        else:
            self.solver.assert_and_track(
                Or(sum([If(self.a[betaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) == 0,
                   sum([If(self.a[betaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) >= 1),
                "LabelAlphaOrBeta: " + str(self.labelIdx))
            self.labelIdx += 1

            self.solver.assert_and_track(
                Or(sum([If(self.a[alphaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) == 0,
                   sum([If(self.a[alphaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) >= 1),
                "LabelAlphaOrBeta: " + str(self.labelIdx))
            self.labelIdx += 1

            self.solver.assert_and_track(sum([If(self.a[betaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)]) +
                                         sum([If(self.a[alphaCompId * self.nrVM + j], 1, 0) for j in range(self.nrVM)])
                                         >= 1, "LabelAlphaOrBeta: " + str(self.labelIdx))
            self.labelIdx += 1


    def _constraintsHardware(self, componentsRequirements, scale_factor):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """

        self.problem.logger.debug("constraintsHardware: componentsRequirements={}".format(componentsRequirements))
        componentsRequirements = [[0 if i is None else i for i in line] for line in componentsRequirements]

        tmp = []
        for k in range(self.nrVM):
            tmp.append(sum([self.a[i * self.nrVM + k] * (componentsRequirements[i][0]) for i in range(self.nrComp)]) <=
                       self.ProcProv[k])
            tmp.append(sum([self.a[i * self.nrVM + k] * ((componentsRequirements[i][1] if int(scale_factor)==1 else componentsRequirements[i][1]/ scale_factor)) for i in range(self.nrComp)]) <=
                       self.MemProv[k])
            tmp.append(sum([self.a[i * self.nrVM + k] * ((componentsRequirements[i][2] if int(scale_factor)==1 else componentsRequirements[i][2]/ scale_factor)) for i in range(self.nrComp)]) <=
                       self.StorageProv[k])

        self.solver.add(tmp)



    def createSMT2LIBFile(self, fileName):
        """
        File creation
        :param fileName: string representing the file name storing the SMT2LIB formulation of the problem
        :return:
        """
        #with open(fileName, 'w+') as fo:
        #   fo.write("(set-logic QF_LIA)\n") # quantifier free linear integer-real arithmetic
        #fo.close()
        if fileName is None: return
        with open(fileName, 'w+') as fo:
            fo.write(self.solver.sexpr())
        fo.close()

    def createSMT2LIBFileSolution(self, fileName, status, model):
        """
        File creation
        :param fileName: string representing the file name storing the SMT2LIB formulation of the problem
        :param status: SAT/UNSAT
        :param model: string representing key-values pairs for the variables in the model
        :return:
        """
        if fileName is None: return
        with open(fileName, 'w+') as foo:
            foo.write(repr(status)+ '[\n')
            for k in model:
                foo.write('%s = %s, ' % (k, model[k]))
                foo.write('\n')
            foo.write(']')
        foo.close()

    def run(self):
        """
        Invokes the solving of the problem (solution and additional effect like creation of special files)
        :param smt2lib: string indicating a file name storing the SMT2LIB encoding of the problem
        :param smt2libsol: string indicating a file name storing the solution of the problem together with a model (if applicable)
        :return:
        """

        if self.solverTypeOptimize:
            opt = sum(self.PriceProv)
            min = self.solver.minimize(opt)


        self.createSMT2LIBFile(self.smt2lib)

        startime = time.time()
        status = self.solver.check()
        stoptime = time.time()

        if not self.solverTypeOptimize:
            c = self.solver.unsat_core()
            self.problem.logger.debug("unsat_constraints= {}".format(c))
            for cc in c:
                self.problem.logger.debug(
                    "Constraint label: {} constraint description {}".format(str(cc), self.__constMap[cc]))

        self.problem.logger.info("Z3 status: {}".format(status))


        if status == sat:
            model = self.solver.model()
            a_mat = []
            for i in range(self.nrComp):
                l = []
                for k in range(self.nrVM):
                    l.append(model[self.a[i * self.nrVM + k]])
                a_mat.append(l)

            vms_price = []
            for k in range(self.nrVM):
                vms_price.append(model[self.PriceProv[k]])

            vms_type = []
            for k in range(self.nrVM):
                vms_type.append(model[self.vmType[k]])
        else:
            print("!!!!!!!UNSAT")

        self.createSMT2LIBFileSolution(self.smt2libsol, status, model)

        if self.solverTypeOptimize:
            if status == sat:
                print("a_mat", a_mat)
                # do not return min.value() since the type is not comparable with -1 in the exposeRE
                return min.value(), vms_price, stoptime - startime, a_mat, vms_type
            else:
                # unsat
                return -1, None, None, None, None
        else:
            return None, vms_price, stoptime - startime