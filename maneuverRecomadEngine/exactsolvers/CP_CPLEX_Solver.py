import docplex.mp.model as cpx
import docloud as dc
from docplex.mp.conflict_refiner import ConflictRefiner, VarUbConstraintWrapper, VarLbConstraintWrapper
import time
from docplex.mp.functional import LogicalOrExpr, LogicalAndExpr
from maneuverRecomadEngine.exactsolvers.ManuverSolver import ManuverSolver

class CP_Solver_CPlex(ManuverSolver):

    def _initSolver(self):

        self.orCntIndex = 0

        self.nr_vms = self.problem.nrVM
        self.nr_comps = self.problem.nrComp

        self.model = cpx.Model(name="MIP Model")

        self.__define_variables()

        self.__add_offers_restrictions()
        # for restriction in self.problem.restrictionsList:
        #     restriction.generateRestrictions(self)
        #self.__add_hardware_restrictions()


    def __define_variables(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding, usage vector, etc.)
        :return: None
        """
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        self.vm = {j: self.model.binary_var(name="vm{0}".format(j+1)) for j in range(self.nr_vms)}

        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        self.a = {(i, j): self.model.binary_var(name="C{0}_VM{1}".format(i+1, j+1))
                  for i in range(self.nr_comps) for j in range(self.nr_vms)}

        for j in range(self.nr_vms):
            self.model.add_equivalence(
                self.vm[j], self.model.sum(self.a[i, j] for i in range(self.nr_comps)) >= 1,
                name="c{0}_vm_allocated".format(j))

            # self.model.add_constraint(ct=self.model.add_equivalence(
            #     self.model.logical_ self.vm[j] == 0, self.model.sum(self.a[i, j] for i in range(self.nr_comps)) == 0),
            #     ctname="c{0}_vm_free".format(j))

        self.__define_variables_offers()


    def __define_variables_offers(self):

        # values from availableConfigurations
        minProc = min(self.offers_list[t][1] for t in range(len(self.offers_list)))
        maxProc = max(self.offers_list[t][1] for t in range(len(self.offers_list)))
        self.ProcProv = {(j): self.model.integer_var(lb=minProc, ub=maxProc,
            name="ProcProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        minMem = min(self.offers_list[t][2] for t in range(len(self.offers_list)))
        maxMem = max(self.offers_list[t][2] for t in range(len(self.offers_list)))
        print("minMem", minMem, "maxMem", maxMem)
        self.MemProv = {(j): self.model.integer_var(lb=minMem, ub=maxMem,
            name="MemProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        minSto = min(self.offers_list[t][3] for t in range(len(self.offers_list)))
        maxSto = max(self.offers_list[t][3] for t in range(len(self.offers_list)))
        self.StorageProv = {(j): self.model.integer_var(#b=minSto, ub=maxSto,
             name="StorageProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        maxPrice = max(self.offers_list[t][len(self.offers_list[0]) - 1] for t in range(len(self.offers_list)))

        print("MAX price, ", maxPrice)
        self.PriceProv = {(j): self.model.integer_var(lb=0, ub=maxPrice,
            name="PriceProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        maxType = len(self.offers_list)
        self.vmType = {(j): self.model.integer_var(lb=0, ub=maxType,
            name="vmType{0}".format(j + 1)) for j in range(self.nr_vms)}

        # If a machine is not leased then its price is 0
        for j in range(self.nr_vms):
            self.model.add_indicator(self.vm[j], self.PriceProv[j] == 0, active_value=0,
                name="c{0}_vm_free_price_0".format(j))


    def run(self):
        objective = self.model.sum(self.PriceProv[j] for j in range(self.nr_vms))
        #objective = self.model.sum(self.v

        self.model.minimize(objective)

        self.model.prettyprint("out")
        self.model.export_as_lp("alt")
        self.model.export_as_mps("nou")

        vmPrice = []
        vmType = []
        a_mat = []
        # m[j] for j in range(self.nr_vms))

        starttime = time.time()
        xx = self.model.solve()
        stoptime = time.time()


        print("cplex: ", self.model.get_solve_status(), self.model.get_statistics)
        print(self.vm)
        if (dc.status.JobSolveStatus.OPTIMAL_SOLUTION ==  self.model.get_solve_status()):
            print(self.model.solve_details)
            print("vmType")
            for index, var in self.vmType.items():
                print(var.solution_value, end=" ")
                vmType.append(var.solution_value)
            print("\n vmPrice")

            for index, var in self.PriceProv.items():
                print(var.solution_value, end=" ")
                vmPrice.append(var.solution_value)
            print("\n Vm Aquired")
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
            for l in a_mat:
                print(l)

            print(xx.get_objective_value())
        else:
            print("!!!!!!!!!!Unsolve")
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

        tmp = []
        for k in range(self.nr_vms):
            self.model.add_constraint(ct=self.model.sum(self.a[i, k] * componentsRequirements[i][0] for i in range(self.nr_comps)) <= self.ProcProv[k],
                                      ctname="c_hard")
            self.model.add_constraint(
                ct=self.model.sum(self.a[i, k] * componentsRequirements[i][1] for i in range(self.nr_comps)) <=
                   self.MemProv[k],
                ctname="c_hard_mem")
            self.model.add_constraint(
                ct=self.model.sum(self.a[i, k] * componentsRequirements[i][2] for i in range(self.nr_comps)) <=
                   self.StorageProv[k],
                ctname="c_hard_storage")
        pass



    def RestrictionOneToOneDependency(self, alphaCompId, betaCompId):
        """
        Contraint describing that alphaCompId and betaCompId should be deployed on the same VM
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return: None
        """
        for j in range(self.nr_vms):
            self.model.add_constraint(ct=self.a[alphaCompId, j] == self.a[betaCompId, j], ctname="c_one_2_one_dependency")

        #self.solver.add(self.a[alphaCompId * self.nr_vms + j] == self.a[betaCompId * self.nr_vms + j])



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
                # self.solver.add(
                #     sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) <=
                #     sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]))
            self.model.add_constraint(ct=
                self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) <=
                self.model.sum(self.a[betaCompId, j]for j in range(self.nr_vms)),
                                          ctname="c_many_2_many_dependency_le")

        elif relation == ">=":

                # self.solver.add(
                #     sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) >=
                #     sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]))
            self.model.add_constraint(ct=
                                  self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) >=
                                  self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)),
                                  ctname="c_many_2_many_dependency_ge")

        elif relation == "=":
                # self.solver.add(
                #     sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) ==
                #     sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]))
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

            # self.solver.add(
            #     noInstances * sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) -
            #     sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) > 0)
        self.model.add_constraint(ct=
                                  noInstances * self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms))-
                                  self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) >= 1,
                                  ctname="c_one_2_many_dependency_p1")


            # self.solver.add(
            #     noInstances * sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) -
            #     sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) <= noInstances)

        self.model.add_constraint(ct= noInstances * self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms))-
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

                # self.solver.add(
                #     sum([self.a[compId * self.nr_vms + j] for compId in compsIdList for j in range(self.nr_vms)]) <= bound)
            self.model.add_constraint(
                ct= self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) <= bound,
                ctname="c_upper_lower_bound")

        elif operator == ">=":

                # self.solver.add(
                #     sum([self.a[compId * self.nr_vms + j] for compId in compsIdList for j in range(self.nr_vms)]) >= bound)
            self.model.add_constraint(
            ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) >= bound,
            ctname="c_upper_lower_bound")

        elif operator == "=":
            # if not self.debug:
            #     self.solver.add(
            #         sum([self.a[compId * self.nr_vms + j] for compId in compsIdList for j in range(self.nr_vms)]) == bound)
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
        # if not self.debug:
        #     self.solver.add(
        #         sum([self.a[compId * self.nr_vms + j] for compId in compsIdList for j in range(self.nr_vms)]) >= lowerBound)

        self.model.add_constraint(
            ct=self.model.sum(self.a[compId, j] for compId in compsIdList for j in range(self.nr_vms)) >= lowerBound,
            ctname="c_range_bound")

        # if not self.debug:
        #     self.solver.add(
        #         sum([self.a[compId * self.nr_vms + j] for compId in compsIdList for j in range(self.nr_vms)]) <= upperBound)
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


        print("!!!!!!!!!!!  ", alphaCompId, inConflictCompsIdList)# 4 [3, 0]
        for j in range(self.nr_vms):
            # self.solver.add(
            #     sum([self.a[alphaCompId * self.nr_vms + j]] + [self.a[_compId * self.nr_vms + j] for _compId in
            #                                                       notInConflictCompsIdList]) == self.vm[j])

            l = [self.a[_compId, j] for _compId in inConflictCompsIdList]
            l.append(self.a[alphaCompId, j])
            # self.model.add_constraint(
            #     ct=self.model.sum(l) <=self.vm[j],
            #     ctname="c_range_bound")
            #self.model.add_indicator(self.vm[j], self.a[alphaCompId, j] == 0, active_value=0, name="c_full_deplpyment")
            self.model.add_indicator(self.vm[j], self.model.sum(l) == 1, name="c_full_deployment"+str(j))


            #print(j, " uff: " + alphaCompId + [(" " + _compId) for _compId in notInConflictCompsIdList] )



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


            # self.solver.add(
            #     alphaCompIdInstances * sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) <=
            #     betaCompIdInstances * sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]))


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
            # self.solver.add(
            #     Or(sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) == 0,
            #        sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) >= 1))
            # self.solver.add(
            #     Or(sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) == 0,
            #        sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) >= 1))

            # self.solver.add(
            #     Xor(sum([self.a[betaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) == 0,
            #         sum([self.a[alphaCompId * self.nr_vms + j] for j in range(self.nr_vms)]) == 0, True))

        # aux_var_alpha = self.model.binary_var(name="or_alpha")
        # self.model.add_equivalence(
        #     aux_var_alpha, self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) == 0)
        # # self.model.add_equivalence(
        # #     aux_var_alpha,
        # #     self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) >= 1)
        #
        # aux_var_beta = self.model.binary_var(name="or_beta")
        # self.model.add_equivalence(
        #     aux_var_beta, self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) == 0)


        # LogicalOrExpr(self.model, [self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) == 0,
        #                            self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) >= 1])
        #
        # LogicalOrExpr(self.model, [self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) == 0,
        #                            self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms)) >= 1])
        #
        # self.model.add_constraint(ct=self.model.sum(self.a[alphaCompId, j] for j in range(self.nr_vms))+
        #                              self.model.sum(self.a[betaCompId, j] for j in range(self.nr_vms)) >= 1, ctname="c_or")

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

        print("??????????????__add_hardware_restrictions")

        if self.offers_list is None:
            return

        componentsRequirements = self.problem._getComponentsHardwareRestrictions()
        self.problem.logger.debug("constraintsHardware: componentsRequirements={}".format(componentsRequirements))
        componentsRequirements = [[0 if i is None else int(i) for i in line] for line in componentsRequirements]
        print("componentsRequirements", componentsRequirements)

        # for i in range(self.nr_comps):
        #     componentsRequirements[i][1] /= 1000.
        #     componentsRequirements[i][2] /= 1000.

        for k in range(self.nr_vms):
            # tmp.append(sum([componentsRequirements[i][0] * self.a[i * self.nr_vms + k] for i in range(self.nr_comps)]) <=
            #            self.ProcProv[k])

            self.model.add_constraint(
                ct=self.model.sum(self.a[i, k]*componentsRequirements[i][0] for i in range(self.nr_comps)) <= self.ProcProv[k],
                ctname="c_hardware_proc")

            # tmp.append(sum([componentsRequirements[i][1] * self.a[i * self.nr_vms + k] for i in range(self.nr_comps)]) <=
            #            self.MemProv[k])

            self.model.add_constraint(
                ct=self.model.sum(self.a[i, k]*componentsRequirements[i][1] for i in range(self.nr_comps)) <=
                   self.MemProv[k],
                ctname="c_hardware_mem")

            # tmp.append(sum([componentsRequirements[i][2] * self.a[i * self.nr_vms + k] for i in range(self.nr_comps)]) <=
            #            self.StorageProv[k])

            self.model.add_constraint(
                ct=self.model.sum(self.a[i, k]*componentsRequirements[i][2] for i in range(self.nr_comps)) <=
                   self.StorageProv[k],
                ctname="c_hardware_storage")

        # if not self.debug:
        #     for constaint in tmp:
        #         self.solver.add(constaint)
        # else:
        #     for constaint in tmp:
        #         self.solver.assert_and_track(constaint, "Label: " + str(self.labelIdx))
        #         self.labelIdx += 1


    def __add_offers_restrictions(self):
        max_id = -1
        for vmid in self.vmIds_for_fixedComponents:
            if max_id < vmid:
                max_id = vmid

        self.RestrictionPriceOrder(max_id + 1, self.nr_vms)

        # make offers real again
        # for t in range(len(self.offers)):
        #     self.offers[t][len(self.offers[0]) - 1] /= 1000.
        #     self.offers[t][2] /= 1000.
        #     self.offers[t][3] /= 1000.
        cnt = 0
        for vm_id in range(self.nr_vms):
            addedOffers = []
            vars = []
            for t in range(len(self.offers_list)):
                addOffer = True
                if self.offers_list_filtered:
                    if vm_id in self.vm_with_offers:
                        # testez daca oferta e aplicabila
                        comp_id = self.vm_with_offers[vm_id]
                        if self.offers_list[t][1] < self.problem.componentsList[comp_id].HC:
                            addOffer = False
                        elif self.offers_list[t][2] < self.problem.componentsList[comp_id].HM:# / 1000.:
                            addOffer = False
                        elif self.offers_list[t][3] < self.problem.componentsList[comp_id].HS:# / 1000.:
                            addOffer = False
                if addOffer:
                    cnt += 1
                    addedOffers.append(t + 1)
                            # self.solver.add(
                            #     Implies(And(self.vm[vm_id] == 1, self.vmType[vm_id] == t + 1),
                            #             And(self.PriceProv[vm_id] == self.offers[t][len(self.offers[0]) - 1],
                            #                 self.ProcProv[vm_id] == self.offers[t][1],
                            #                 self.MemProv[vm_id] == self.offers[t][2],
                            #                 self.StorageProv[vm_id] == self.offers[t][3]
                            #                 )
                            #             ))
                    var = self.model.binary_var(name="aux_hard{0}".format(cnt))
                    vars.append(var)

                    ct = self.model.add_equivalence(var, self.vmType[vm_id] == t + 1)

                    # ct = self.model.add_indicator(var, LogicalAndExpr(self.model, [
                    #                             self.PriceProv[vm_id] == int(self.offers[t][len(self.offers[0]) - 1]),
                    #                             self.ProcProv[vm_id] == int(self.offers[t][1]),
                    #                             self.MemProv[vm_id] == int(self.offers[t][2]),
                    #                             self.StorageProv[vm_id] == int(self.offers[t][3])
                    #                             ])==1)

                    self.model.add_indicator(var,  self.PriceProv[vm_id] == int(self.offers_list[t][len(self.offers_list[0]) - 1])
                                             , active_value=1,
                                             name="c_order_vm_price".format(vm_id))
                    self.model.add_indicator(var, (self.ProcProv[vm_id] == int(self.offers_list[t][1])),
                                             name="c_order_vm_cpu".format(vm_id))
                    self.model.add_indicator(var, (self.MemProv[vm_id] == int(self.offers_list[t][2])),
                                             name="c_order_vm_memory".format(vm_id))
                    self.model.add_indicator(var, (self.StorageProv[vm_id] == int(self.offers_list[t][3])),
                                              name="c_order_vm_storage".format(vm_id))

                else:
                    self.model.add_indicator(self.vm[vm_id], self.vmType[vm_id] != t+1)
            print("offers: ", vm_id, addedOffers)
            lst = [(self.vmType[vm_id] == offer) for offer in addedOffers]
            ct = self.model.add_indicator(self.vm[vm_id], self.vmType[vm_id] >= 1)
            #Todo: oare nu e in plus
            #self.model.add_constraint(ct=self.model.logical_or(lst)==1, ctname="c_offers_type")

            # else:
            #     if self.use_vms_variable:
            #         if not self.debug:
            #             self.solver.add(Implies(And(self.vm[vm_id] == 1, self.vmType[vm_id] == t + 1),
            #                                     self.PriceProv[vm_id] == Constants.MAX_OFFER_PRICE ))
            #         else:
            #             self.solver.assert_and_track(Implies(And(self.vm[vm_id] == 1, self.vmType[vm_id] == t + 1),
            #                                     self.PriceProv[vm_id] == Constants.MAX_OFFER_PRICE), "Label: " + str(self.labelIdx))
            #
            #             self.labelIdx += 1
            #     else:
            #
            #         self.solver.add(Implies(And(sum([self.a[i + vm_id] for i in range(0, len(self.a), self.nr_vms)]) >= 1, self.vmType[vm_id] == t + 1),
            #                                 self.PriceProv[vm_id] == Constants.MAX_OFFER_PRICE))


    def RestrictionPriceOrder(self, start_vm_id, end_vm_id):



        if self.sb_vms_order_by_price:
            for j in range(start_vm_id, end_vm_id - 1):
                # sum c1 <= sum c2 <= sum c3 - fortez la inceput masinile goale <- de vazut daca ajuta daca cres numarul de vm-uri
                # self.solver.add(sum([self.a[i + j] for i in range(0, len(self.a), self.nr_vms)]) >= sum([self.a[i + j + 1] for i in range(0, len(self.a), self.nr_vms)]))
                #self.solver.add(self.PriceProv[j] <= self.PriceProv[j + 1])
                self.model.add_constraint(ct=self.PriceProv[j] >= self.PriceProv[j + 1], ctname="c_offers_type")


    def RestrictionComponentsNumberOrder(self, start_vm_id, end_vm_id):
        if self.sb_vms_order_by_components_number:
            for j in range(start_vm_id, end_vm_id - 1):
                # sum c1 <= sum c2 <= sum c3 - fortez la inceput masinile goale <- de vazut daca ajuta daca cres numarul de vm-uri
                # self.model.add(sum([self.a[i + j] for i in range(0, len(self.a), self.nr_vms)]) <= sum(
                #     [self.a[i + j + 1] for i in range(0, len(self.a), self.nr_vms)]))
                self.model.add_constraint(ct=self.model.sum(self.a[i, j] for i in range(self.nr_comps)) <= self.model.sum(self.a[i, j+1] for i in range(self.nr_compss)), ctname="c_offers_type")
                # for j in range(start_vm_id, end_vm_id - 1):
                #     self.solver.add(self.PriceProv[j] >= self.PriceProv[j + 1])



# [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], \
# [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0],
# [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
# [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
# [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0],
# [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
# [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
# [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0],
# [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0],
# [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
