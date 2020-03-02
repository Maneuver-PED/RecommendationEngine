import docplex.mp.model as cpx
import docloud as dc
from docplex.mp.conflict_refiner import ConflictRefiner, VarUbConstraintWrapper, VarLbConstraintWrapper
import time
from docplex.mp.functional import LogicalOrExpr, LogicalAndExpr
from maneuverRecomadEngine.exactsolvers.ManuverSolver import ManuverSolver

class CPlex_SolverSymBreak(ManuverSolver):

    def _initSolver(self):

        self.orCntIndex = 0

        self.nr_vms = self.problem.nrVM
        self.nr_comps = self.problem.nrComp

        self.model = cpx.Model(name="Manuver Model")
        self.model.parameters.timelimit.set(400.0)
        self.__define_variables()
        self.__add_offers_restrictions()


    def __define_variables(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding,
        usage vector, etc.)
        :return: None
        """
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        self.vm = {j: self.model.binary_var(name="vm{0}".format(j+1)) for j in range(self.nr_vms)}

        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        print("???????", self.nr_comps, self.nr_vms)
        self.a = {(i, j): self.model.binary_var(name="C{0}_VM{1}".format(i+1, j+1))
                  for i in range(self.nr_comps) for j in range(self.nr_vms)}

        for j in range(self.nr_vms):
            self.model.add_equivalence( self.vm[j], self.model.sum(self.a[i, j] for i in range(self.nr_comps)) >= 1,
                name="c{0}_vm_allocated".format(j))

        self.__define_variables_offers()


    def __define_variables_offers(self):
        """
        Function that describes the offers
        :return:
        """
        maxType = len(self.offers_list)
        if self.default_offers_encoding:
            self.vmType = {(j): self.model.integer_var(lb=0, ub=maxType, name="vmType{0}".format(j + 1))
                           for j in range(self.nr_vms)}
            # values from availableConfigurations
            minProc = min(self.offers_list[t][1] for t in range(len(self.offers_list)))
            maxProc = max(self.offers_list[t][1] for t in range(len(self.offers_list)))
            self.ProcProv = {(j): self.model.integer_var(lb=minProc, ub=maxProc,
                name="ProcProv{0}".format(j + 1)) for j in range(self.nr_vms)}

            minMem = min(self.offers_list[t][2] for t in range(len(self.offers_list)))
            maxMem = max(self.offers_list[t][2] for t in range(len(self.offers_list)))
            self.MemProv = {(j): self.model.integer_var(lb=minMem, ub=maxMem,
                name="MemProv{0}".format(j + 1)) for j in range(self.nr_vms)}

            minSto = min(self.offers_list[t][3] for t in range(len(self.offers_list)))
            maxSto = max(self.offers_list[t][3] for t in range(len(self.offers_list)))
            self.StorageProv = {(j): self.model.integer_var(#b=minSto, ub=maxSto,
                 name="StorageProv{0}".format(j + 1)) for j in range(self.nr_vms)}
        else:
            self.newVmType = {(i, j): self.model.binary_var(name="newType{0}_VM{1}".format(i + 1, j + 1))
                              for i in range(maxType) for j in range(self.nr_vms)}

            # for j in range(self.nr_vms):
            #     self.model.add_indicator(
            #         self.vm[j], self.model.sum(self.newVmType[i, j] for i in range(len(self.offers_list))) >= 1,
            #         name="c{0}_vm_allocated".format(j))

        maxPrice = max(self.offers_list[t][len(self.offers_list[0]) - 1] for t in range(len(self.offers_list)))
        self.PriceProv = {(j): self.model.integer_var(lb=0, ub=maxPrice,
            name="PriceProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        # If a machine is not leased then its price is 0
        for j in range(self.nr_vms):
            self.model.add_indicator(self.vm[j], self.PriceProv[j]==0, active_value=0,
                                     name="c{0}_vm_free_price_0".format(j))


    def run(self):
        objective = self.model.sum(self.PriceProv[j] for j in range(self.nr_vms))
        self.model.minimize(objective)

#        self.model.prettyprint("out")
#        self.model.export_as_lp("alt")
#        self.model.export_as_mps("nou")

        vmPrice = []
        vmType = []
        a_mat = []
        # m[j] for j in range(self.nr_vms))

        starttime = time.time()
        xx = self.model.solve()
        stoptime = time.time()

        print("cplex: ", self.model.get_solve_status(), self.model.get_statistics)

        if (dc.status.JobSolveStatus.OPTIMAL_SOLUTION ==  self.model.get_solve_status()):
            print(self.model.solve_details)
            print("vmType")

            if (self.default_offers_encoding):
                for index, var in self.vmType.items():
                    print(var.solution_value, end=" ")
                    vmType.append(var.solution_value)
            else:
                vmType = []
                l = []
                col = 0
                for index, var in self.newVmType.items():
                    if col == self.problem.nrVM:
                        vmType.append(l)
                        l = []
                        col = 0
                    col += 1
                    l.append(int(var.solution_value))
                    vmType.append(l)


            print("\nvmPrice")
            for index, var in self.PriceProv.items():
                print(var.solution_value, end=" ")
                vmPrice.append(var.solution_value)

            print("\nVm Aquired")
            for index,var in self.vm.items():
               print(var.solution_value, end=" ")
            print()


            l=[]
            col = 0
            for index, var in self.a.items():

                if (col == self.problem.nrVM):
                    a_mat.append(l)
                    l = []
                    col = 0
                col += 1
                l.append(int(var.solution_value))
            a_mat.append(l)
            print("\n comp allocation matrix", self.nrVM, self.nrComp)
            for l in a_mat:
                print(l)

            print(xx.get_objective_value())
        else:
            print("!!!!!!!!!!Unsolve CPLEX")
            print(self.model.get_time_limit())
            cr = ConflictRefiner()
            conflicts = cr.refine_conflict(self.model)
            print(self.model.get_solve_status())
            for conflict in conflicts:
                st = conflict.status
                ct = conflict.element
                label = conflict.name
                label_type = type(conflict.element)
                if isinstance(conflict.element, VarLbConstraintWrapper) \
                        or isinstance(conflict.element, VarUbConstraintWrapper):
                    ct = conflict.element.get_constraint()
                # Print conflict information in console
                print("Conflict involving constraint: %s" % label)
                print(" \tfor: %s" % ct)


        return xx.get_objective_value(), vmPrice , stoptime-starttime, a_mat, vmType

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
            self.model.add_constraint(ct=self.a[comp_id, vm_id] == 1, ctname="c_fix_component")
            for compId in self.problem.componentsList[comp_id].conflictComponentsList:
                self.model.add_constraint(ct=self.a[compId, vm_id] == 0, ctname="c_fix_component")
        else:
            self.model.add_constraint(ct=self.a[comp_id, vm_id] == 0, ctname="c_fix_component")

        self.vm_with_offers[vm_id] = comp_id
        self.vmIds_for_fixedComponents.add(vm_id)


    def RestrictionConflict(self, alphaCompId, conflictCompsIdList):
        """
        Constraint describing the conflict between components. The 2 params. should not be placed on the same VM
        :param alphaCompId: id of the first conflict component
        :param conflictCompsIdList: id of the second conflict component
        :return: None
        """
        for compId in conflictCompsIdList:
            compId += 1

        self.problem.logger.debug(
            "RestrictionConflict: alphaCompId = {} conflictComponentsList = {}".format(alphaCompId,
                                                                                       conflictCompsIdList))

        for j in range(self.nr_vms):
            for conflictCompId in conflictCompsIdList:
                self.model.add_constraint(ct=self.a[alphaCompId, j]+ self.a[conflictCompId, j] <= 1, ctname="c_comp_conflict")



    def constraintsHardware(self, componentsRequirements):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """

        self.problem.logger.debug("constraintsHardware: componentsRequirements={}".format(componentsRequirements))
        componentsRequirements = [[0 if i is None else i for i in line] for line in componentsRequirements]

        if self.default_offers_encoding:
            tmp = []
            for k in range(self.nr_vms):
                self.model.add_constraint(ct=self.model.sum(self.a[i, k] * componentsRequirements[i][0]
                                                            for i in range(self.nr_comps)) <= self.ProcProv[k],
                                          ctname="c_hard")
                self.model.add_constraint(
                    ct=self.model.sum(self.a[i, k] * componentsRequirements[i][1] for i in range(self.nr_comps)) <=
                       self.MemProv[k],
                    ctname="c_hard_mem")
                self.model.add_constraint(
                    ct=self.model.sum(self.a[i, k] * componentsRequirements[i][2] for i in range(self.nr_comps)) <=
                       self.StorageProv[k],
                    ctname="c_hard_storage")
        else:
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

            self.__encode_carachteristic(cpu_values, 0, componentsRequirements, "cpu")
            self.__encode_carachteristic(memory_values, 1, componentsRequirements, "mem")
            self.__encode_carachteristic(storage_values, 2, componentsRequirements, "sto")

    def __encode_carachteristic(self, characteristic_values, characteristic_index, componentsRequirements, text):
        """
        Helper function in order to encode harware constraints
        """
        for k in range(self.nrVM):
            keys = list(characteristic_values.keys())
            keys.sort(reverse=True)

            cpus_sum = self.model.integer_var(lb=0, name="{}_sum{}".format(text, k))
            self.model.add_constraint(
                ct=self.model.sum([self.a[i, k] * componentsRequirements[i][characteristic_index] for i in range(self.nr_comps)]) == cpus_sum,
                ctname="set_vm_{}{}".format(text, k))
            key = keys[0]
            offers_applicable = characteristic_values[key].copy()

            var_aux1 = self.model.binary_var("sum_equal_zero_{}__vm{}_{}".format(text, k, key))
            var_aux2 = self.model.binary_var("sum_upper_bound_{}__vm{}_{}".format(text, k, key))
            self.model.add_equivalence(var_aux1, cpus_sum == 0)
            self.model.add_equivalence(var_aux2, cpus_sum >= key + 1)
            for offer_id in range(len(self.offers_list)):
                self.model.add_indicator(var_aux1, self.newVmType[offer_id, k] == 0)
                self.model.add_indicator(var_aux2, self.newVmType[offer_id, k] == 0)

            keys.pop(0)
            # print(keys)
            for key in keys:
                values = characteristic_values[key]
                var1 = self.model.binary_var("available_offers_{}__vm{}_{}".format(text, k, key))

                self.model.add_equivalence(var1,
                                    self.model.sum([self.newVmType[index - 1, k] for index in offers_applicable]) >= 1)

                var_aux3 = self.model.binary_var("sum_inner_bounds_{}__vm{}_{}".format(text, k, key))
                self.model.add_equivalence(var_aux3, cpus_sum >= key + 1)

                self.model.add_indicator(var_aux3, var1 == 1)
                offers_applicable.extend(values)
                offers_applicable.sort()



            key = keys.pop()
            var1 = self.model.binary_var("available_offers_{}_vm{}_{}".format(text, k, key))
            self.model.add_equivalence(var1,
                                       self.model.sum([self.newVmType[index - 1, k] for index in offers_applicable]) >= 1)

            var_aux6 = self.model.binary_var("sum_ge_one_{}__vm{}_{}".format(text, k, key))
            self.model.add_equivalence(var_aux6, cpus_sum >= 1)
            var_aux7 = self.model.binary_var("sum_le_lower_{}__vm{}_{}".format(text, k, key))
            self.model.add_equivalence(var_aux7, cpus_sum <= key +1)

            var_aux8 = self.model.binary_var("sum_and_{}__vm{}_{}".format(text, k, key))
            self.model.add_equivalence(var_aux8, LogicalAndExpr(self.model, [var_aux6, var_aux7])==1)

            self.model.add_indicator(var_aux8, var1 == 1)
            # self.model.add_constraint(
            #     self.model.add_if_then(if_ct=LogicalAndExpr(self.model, [var_aux6, var_aux7])==1 , then_ct=var1 == 1))



    def RestrictionOneToOneDependency(self, alphaCompId, betaCompId):
        """
        Contraint describing that alphaCompId and betaCompId should be deployed on the same VM
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return: None
        """
        for j in range(self.nr_vms):
            self.model.add_constraint(ct=self.a[alphaCompId, j] == self.a[betaCompId, j], ctname="c_one_2_one_dependency")

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
            self.model.add_constraint(ct=
                self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) <=
                self.model.sum(self.a[betaCompId, j]for j in range(self.nr_vms)),
                                          ctname="c_many_2_many_dependency_le")

        elif relation == ">=":
            self.model.add_constraint(ct=self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) >=
                                  self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)),
                                  ctname="c_many_2_many_dependency_ge")

        elif relation == "=":
                self.model.add_constraint(ct=
                                          self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) ==
                                          self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)),
                                          ctname="c_many_2_many_dependency_eq")


    def RestrictionOneToManyDependency(self, alphaCompId, betaCompId, noInstances):
        """
        At each alphaCompId component should be deployed noInstances betaCompId components
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param noInstances: depending instances number
        :return: None
        """

        self.model.add_constraint(ct=
                                  noInstances * self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms))-
                                  self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) >= 1,
                                  ctname="c_one_2_many_dependency_p1")

        self.model.add_constraint(ct=noInstances * self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms))-
                                  self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) <= noInstances,
                                  ctname="c_one_2_many_dependency_p1")


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
            self.model.add_constraint(
                ct= self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) <= bound,
                ctname="c_upper_lower_bound")

        elif operator == ">=":
            self.model.add_constraint(
            ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) >= bound,
            ctname="c_upper_lower_bound")

        elif operator == "=":
            self.model.add_constraint(
                ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) == bound,
                ctname="c_upper_lower_bound")
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
        self.model.add_constraint(
            ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) >= lowerBound,
            ctname="c_range_bound")
        self.model.add_constraint(
            ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) <= upperBound,
            ctname="c_range_bound")


    def RestrictionFullDeployment(self, alphaCompId, inConflictCompsIdList):
        """
        Adds the fact that the component alphaCompId must be deployed on all machines except the ones that contain
         components that alphaCompId alpha is in conflict with
        :param alphaCompId: the component which must be fully deployed
        :param inConflictCompsIdList: the list of components that alphaCompId is in conflict in
        :return: None
        """
        for j in range(self.nr_vms):
            # self.solver.add(
            #     sum([self.a[alphaCompId * self.nr_vms + j]] + [self.a[_compId * self.nr_vms + j] for _compId in
            #                                                       notInConflictCompsIdList]) == self.vm[j])

            l = [self.a[_compId, j] for _compId in inConflictCompsIdList]
            l.append(self.a[alphaCompId, j])
            self.model.add_indicator(self.vm[j], self.model.sum(l) == 1, name="c_full_deployment"+str(j))


    def RestrictionRequireProvideDependency(self, alphaCompId, betaCompId, alphaCompIdInstances, betaCompIdInstances):
        """
        The number of instances of component alpha depends on the number of instances of component beta
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param alphaCompIdInstances: number of instances of component alphaCompId
        :param betaCompIdInstances: number of instances of component betaCompId
        :return: None
        """
        self.model.add_constraint(
            ct=alphaCompIdInstances*self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) <=
               betaCompIdInstances * self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)),
            ctname="c_provide_require")


    def RestrictionAlphaOrBeta(self, alphaCompId, betaCompId):
        """
        Describes the fact that alphaCompId or betaCompId not both
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return:
        """
        self.problem.logger.debug(
            "RestrictionAlphaOrBeta: alphaCompId={}, betaCompId={}".format(alphaCompId, betaCompId))
        print("RestrictionAlphaOrBeta", alphaCompId, betaCompId)

        self.alphaSum = self.model.integer_var(lb=0, ub=self.nr_vms, name="alphaSum{0}".format(self.orCntIndex))
        self.betaSum = self.model.integer_var(lb=0, ub=self.nr_vms, name="betaSum{0}".format(self.orCntIndex))

        self.orCntIndex += 1

        self.model.add_constraint(
            ct=self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) == self.alphaSum,
            ctname="c_or_alpha")
        self.model.add_constraint(
            ct=self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) == self.betaSum,
            ctname="c_or_beta")

        LogicalOrExpr(self.model, [self.alphaSum == 0, self.alphaSum >= 1])
        LogicalOrExpr(self.model, [self.betaSum == 0, self.betaSum >= 1])

        self.model.add_constraint(ct=self.model.sum(self.alphaSum + self.betaSum) >= 1, ctname="c_or")

    def __add_hardware_restrictions(self):
        """
        Describes the hardware requirements for each component
        :return: None
        """

        if self.offers_list is None:
            return

        componentsRequirements = self.problem._getComponentsHardwareRestrictions()
        self.problem.logger.debug("constraintsHardware: componentsRequirements={}".format(componentsRequirements))
        componentsRequirements = [[0 if i is None else int(i) for i in line] for line in componentsRequirements]

        for k in range(self.nr_vms):
            if self.default_offers_encoding:
                    self.model.add_constraint(
                        ct=self.model.sum(self.a[i, k]*componentsRequirements[i][0] for i in range(self.nr_comps)) <=
                           self.ProcProv[k], ctname="c_hardware_proc{}".format(k))

                    self.model.add_constraint(
                        ct=self.model.sum(self.a[i, k]*componentsRequirements[i][1] for i in range(self.nr_comps)) <=
                           self.MemProv[k], ctname="c_hardware_mem{}".format(k))

                    self.model.add_constraint(
                        ct=self.model.sum(self.a[i, k]*componentsRequirements[i][2] for i in range(self.nr_comps)) <=
                           self.StorageProv[k], ctname="c_hardware_storage{}".format(k))
            else:
                #implemented in constraintsHardware() function
                pass


    def __add_offers_restrictions(self):
        if self.default_offers_encoding:
            cnt = 0
            for vm_id in range(self.nr_vms):
                addedOffers = []
                for t in range(len(self.offers_list)):
                    addOffer = True
                    if self.offers_list_filtered:
                        if vm_id in self.vm_with_offers:
                            # test if offer is applicable to problem
                            comp_id = self.vm_with_offers[vm_id]
                            if self.offers_list[t][1] < self.problem.componentsList[comp_id].HC:
                                addOffer = False
                            elif self.offers_list[t][2] < self.problem.componentsList[comp_id].HM:
                                addOffer = False
                            elif self.offers_list[t][3] < self.problem.componentsList[comp_id].HS:
                                addOffer = False
                    if addOffer:
                        cnt += 1
                        addedOffers.append(t + 1)

                        var = self.model.binary_var(name="aux_hard{0}".format(cnt))
                        ct = self.model.add_equivalence(var, self.vmType[vm_id] == t + 1)

                        self.model.add_indicator(var,
                                                 self.PriceProv[vm_id] == int(self.offers_list[t][len(self.offers_list[0]) - 1])
                                                 , active_value=1,
                                                 name="c_order_vm_price".format(vm_id))
                        self.model.add_indicator(var, (self.ProcProv[vm_id] == int(self.offers_list[t][1])),
                                                 name="c_order_vm_cpu".format(vm_id))
                        self.model.add_indicator(var, (self.MemProv[vm_id] == int(self.offers_list[t][2])),
                                                 name="c_order_vm_memory".format(vm_id))
                        self.model.add_indicator(var, (self.StorageProv[vm_id] == int(self.offers_list[t][3])),
                                                 name="c_order_vm_storage".format(vm_id))

                lst = [(self.vmType[vm_id] == offer) for offer in addedOffers]
                ct = self.model.add_indicator(self.vm[vm_id], self.vmType[vm_id] >= 1)

        else:
            # new encoding
            priceIndex = len(self.offers_list[0]) - 1
            for vm_id in range(self.nrVM):
                index = 0
                for offer in self.offers_list:
                    index += 1
                    price = offer[priceIndex]
                    self.model.add_indicator(self.newVmType[index - 1, vm_id], self.PriceProv[vm_id] == price,
                                             name="price_type_mapping_offer{}_vm{}".format(index-1, vm_id))


    def RestrictionPriceOrder(self, start_vm_id, end_vm_id):
        print("RestrictionPriceOrder",start_vm_id, end_vm_id)

        if self.sb_vms_order_by_price:
            for j in range(start_vm_id, end_vm_id - 1):
                self.model.add_constraint(ct=self.PriceProv[j] >= self.PriceProv[j + 1], ctname="c_price_lex_order")


    def RestrictionComponentsNumberOrder(self, start_vm_id, end_vm_id):
        if self.sb_vms_order_by_components_number:
            for j in range(start_vm_id, end_vm_id - 1):
                self.model.add_constraint(ct=self.model.sum(self.a[i, j] for i in range(self.nr_comps)) <=
                                             self.model.sum(self.a[i, j+1] for i in range(self.nr_compss)),
                                          ctname="c_offers_type")


    def _symmetry_breaking(self):
        """
        Different symmetry breaking
        """
        max_id = -1
        for vmid in self.vmIds_for_fixedComponents:
            if max_id < vmid:
                max_id = vmid
        self.RestrictionPriceOrder(max_id + 1, self.nr_vms)

        # VMs are order decreasingly based on price
        if self.sb_vms_order_by_price:
            print("add price?", self.sb_vms_order_by_price, "max_id: ", max_id)
            for j in range(max_id + 1, self.nrVM - 1):

                self.model.add_constraint(ct=self.PriceProv[j] >= self.PriceProv[j + 1],  ctname="c_price_lex_order")

        # ??? where is this used??? might give wrong results, run e.g. SecureWebContainer with this option True
        if self.sb_vms_order_by_components_number:
            for j in range(max_id + 1, self.nrVM - 1):
                self.model.add_constraint(ct=sum([self.a[i, j] for i in range(0, self.nr_comps)]) >= sum(
                    [self.a[i, j + 1] for i in range(0, self.nr_comps)]),   ctname="c_vm_load_lex_order")


        for j in range(self.nrVM - 1):
            if self.sb_redundant_price or self.sb_redundant_processor or self.sb_redundant_memory or \
                    self.sb_redundant_storage or self.sb_equal_vms_type_order_by_components_number:
                var = self.model.binary_var(name="aux_vmType{0}".format(j))

                if self.default_offers_encoding:
                    self.model.add_equivalence(var, self.vmType[j] == self.vmType[j + 1])
                else:
                    self.model.add_equivalence(var, self.model.sum([self.newVmType[offer, j] == self.newVmType[offer, j+1]
                                                                    for offer in range(len(self.offers_list))]) == 1)

                # VMs with same type have the same price
                if self.sb_redundant_price:
                    self.model.add_indicator(var,
                                            self.PriceProv[j] == self.PriceProv[j + 1], name="sb_redundant_price")

                if self.default_offers_encoding:
                    # VMs with same type have the same number of procs
                    if self.sb_redundant_processor:
                        self.model.add_indicator(var,
                                                self.ProcProv[j] == self.ProcProv[j + 1], name="sb_redundant_procesor")
                    # VMs with same type have the same amount of memory
                    if self.sb_redundant_memory:
                        self.model.add_indicator(var,
                                                self.MemProv[j] >= self.MemProv[j + 1], name="sb_redundant_memory")

                    # VMs with same type have the same storage
                    if self.sb_redundant_storage:
                        self.model.add_indicator(var,
                                                self.StorageProv[j] == self.StorageProv[j + 1], name="sb_redundant_storage")

                # VMs with the same type should be ordered decreasingly on the number of components
                if self.sb_equal_vms_type_order_by_components_number:
                    self.model.add_indicator(var,
                                            sum([self.a[i, j] for i in range(self.nrComp)]) >=
                                            sum([self.a[i, j + 1] for i in range(self.nrComp)]),
                                            name="sb_equal_vms_type_order_by_components_number")


                # VMs with the same type should occupy columns from top left
                if self.sb_equal_vms_type_order_lex:
                    for i in range(0, self.nrComp):
                        l = [self.a[u, j] == self.a[u, j + 1] for u in range(0, i)]

                        if self.default_offers_encoding:
                            l.append(self.vmType[j] == self.vmType[j + 1])
                        else:
                            l.append(self.model.sum(
                                [self.newVmType[offer, j] == self.newVmType[offer, j + 1]
                                 for offer in range(len(self.offers_list))]) == 1)


                        #l.append(self.vmType[j] == self.vmType[j + 1])
                        var = self.model.binary_var(name="top_vmType{0}_comp{1}".format(j,i))

                        self.model.add_equivalence(var,  LogicalAndExpr(self.model,l)==1)
                        self.model.add_indicator(var, self.a[i, j] >= self.a[i,  j + 1])

                # One to one dependency
                if self.sb_one_to_one_dependency:
                    for one_to_one_group in self.problem.one_to_one_dependencies:
                        component = -1
                        for first_item in one_to_one_group:
                            component = first_item
                            break
                        for comp_id in one_to_one_group:
                            self.model.add_constraint(ct=self.a[comp_id, component] == 1, ctname="sb_one_to_one")



        #lex order on line
        #component 0
        print("elf.sb_lex_line", self.sb_lex_line, self.sb_lex_line_price)
        if self.sb_lex_line:
            instances_nr = 0
            for vm_id in range(self.nrVM-1):
                self.model.add_constraint(self.a[0, vm_id] >= self.a[0, vm_id+1])
            instances_nr = self.problem.componentsList[0].minimumNumberOfInstances
            if self.sb_lex_line_price:
                for vm_id in range(instances_nr-1):
                    self.model.add_constraint(self.PriceProv[vm_id] >= self.PriceProv[vm_id + 1])

            for comp_id in range(1,self.nrComp):
                for vm_id in range(instances_nr+1, self.nrVM - 1):
                    self.model.add_constraint(self.a[comp_id, vm_id] >= self.a[comp_id, vm_id + 1])
                if self.sb_lex_line_price:
                    for vm_id in range(instances_nr + 1, instances_nr+ self.problem.componentsList[comp_id].minimumNumberOfInstances-1):
                        self.model.add_constraint(self.PriceProv[vm_id] >= self.PriceProv[vm_id + 1])
                instances_nr += self.problem.componentsList[comp_id].minimumNumberOfInstances