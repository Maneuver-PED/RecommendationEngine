import time
import numpy
from ortools.constraint_solver import pywrapcp

class CP_Solver_Got:
    def __init__(self, problem, solver_type, nr_of_solution_limit, not_optimisation_problem, available_configurations,
                 time_limit, vmNr):
        self.nrComp = problem.nrComp
        self.problem = problem
        self.nrVM = vmNr#problem.nrVM
        self.VM_MaxLoad = 10
        self.option = solver_type
        self.availableConfig = available_configurations
        self.offerSize = len(available_configurations) if self.availableConfig is not None else 0
        self.timeLimit = time_limit
        self.__nr_of_solution_limit = nr_of_solution_limit
        self.__optimization_problem = not_optimisation_problem
        self.__solveVariantSMTEncoding = True
        self.__defineSolver(self.option)




    def __defineSolver(self, option):
        #print("--define solver")
        # define solver
        parameters = pywrapcp.Solver.DefaultSolverParameters()
        self.solver = pywrapcp.Solver("maneuver_CP_GOT", parameters)
        self.cost = None

        # define some cut limits
        time_limit = self.timeLimit#500000# 4 minute
        #time_limit = 100
        branch_limit = 1000000000
        failures_limit = 1000000000
        solutions_limit = self.__nr_of_solution_limit# 10000
        self.limits = self.solver.Limit(time_limit, branch_limit, failures_limit, solutions_limit, True)

        self.__defineVarinablesAndGeneralConstraints()

        variables = self.vm + self.a + self.PriceProv#+ self.cost

        if option == "FIRST_UNBOUND_MIN":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_FIRST_UNBOUND,
                                                      self.solver.ASSIGN_MIN_VALUE)
        elif option == "FIRST_UNBOUND_MAX":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_FIRST_UNBOUND,
                                                      self.solver.ASSIGN_MAX_VALUE)
        elif option == "FIRST_UNBOUND_RANDOM":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_FIRST_UNBOUND,
                                                      self.solver.ASSIGN_RANDOM_VALUE)
        elif option == "LOWEST_MIN_MIN":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_LOWEST_MIN,
                                                      self.solver.ASSIGN_MIN_VALUE)
        elif option == "LOWEST_MIN_MAX":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_LOWEST_MIN,
                                                      self.solver.ASSIGN_MAX_VALUE)
        elif option == "LOWEST_MIN_RANDOM":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_LOWEST_MIN,
                                                      self.solver.ASSIGN_RANDOM_VALUE)
        elif option == "RANDOM_MIN":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_RANDOM,
                                                      self.solver.ASSIGN_MIN_VALUE)
        elif option == "RANDOM_MAX":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_RANDOM,
                                                      self.solver.ASSIGN_MAX_VALUE)
        elif option == "RANDOM_RANDOM":
            self.decision_builder = self.solver.Phase(variables,
                                                      self.solver.CHOOSE_RANDOM,
                                                      self.solver.ASSIGN_RANDOM_VALUE)

    def __defineVarinablesAndGeneralConstraints(self):
        self.vm = [self.solver.IntVar(0, 1, "VM%i" % j) for j in range(0, self.nrVM)]
        self.a = [self.solver.IntVar(0, 1, 'C%i_VM%i' % (i, j)) for i in range(self.nrComp) for j in
                  range(self.nrVM)]

        #print(".....", self.nrVM, self.offerSize)

        if self.__solveVariantSMTEncoding:
            self.vmType = [self.solver.IntVar(0, self.offerSize, "vmType%i" % j) for j in range(0, self.nrVM)]
            #print(self.vmType)
            self.ProcProv = [self.solver.IntVar(0, 100, "ProcProv%i" % j) for j in range(0, self.nrVM)]
            self.MemProv = [self.solver.IntVar(0, 10000000, "MemProv%i" % j) for j in range(0, self.nrVM)]
            self.StorageProv = [self.solver.IntVar(0, 100000, "StorageProv%i" % j) for j in range(0, self.nrVM)]
            self.PriceProv = [self.solver.IntVar(0, 100000, "PriceProv%i" % j) for j in range(0, self.nrVM)]
            self.__addConstraintsSMT()

        self.cost = self.solver.IntVar(0, 10000000, 'cost')

        if self.__solveVariantSMTEncoding and (self.availableConfig is not None):
            #print(self.cost == self.solver.Sum(self.PriceProv[j] for j in range(self.nrVM)))
            self.solver.Add(self.cost == self.solver.Sum(self.PriceProv[j] for j in range(self.nrVM)))
        else:
            self.solver.Add(self.cost == self.solver.Sum(self.vm[j] for j in range(self.nrVM)))


        # self.__GC1()
        #self.__GC2()
        self.__GC3()

    def addFixComponentRestriction(self, compId, vmId):
        self.solver.Add(self.a[compId * self.nrVM + vmId] == 1)

    def __addConstraintsSMT(self):

        if self.availableConfig is None:
            return
        #print("start smt", self.nrVM)
        # for i in range(self.nrVM):
        #     self.solver.Add((self.vm[i] == 0) == (self.PriceProv[i] == 0))
        #print("add 0 price smt")

        #print(self.nrVM, self.availableConfig)
        #la un assigned vm trebuie sa existe un singur vm type
        for i in range(self.nrVM):
            self.solver.Add(
                self.solver.Sum([
                    self.solver.Sum([self.vm[i] == 0, self.PriceProv[i] == 0]) == 2,
                    self.solver.Sum([
                        self.solver.Sum([self.vm[i] == 1,
                                         self.vmType[i] == t,
                                         self.PriceProv[i] == self.availableConfig[t][4],
                                         self.ProcProv[i] == self.availableConfig[t][1],
                                         self.MemProv[i] == self.availableConfig[t][2],
                                         self.StorageProv[i] == self.availableConfig[t][3]
                                        ]) == 6
                         for t in range(len(self.availableConfig))]) >= 1]) == 1
            )

    def __GC1(self):
        """At least one instance of a component is deployed on acquired VM"""
        for i in range(self.nrComp):
            self.solver.Add(self.solver.Sum([self.a[i*self.nrVM+j] for j in range(self.nrVM)]) >= 1)

    def __GC2(self):
        """The number of components deployed on a virtual machine is less or equal with VM_MaxLoad"""
        for k in range(self.nrVM):
            self.solver.Add(self.solver.Sum([self.a[i * self.nrVM + k] for i in range(self.nrComp)]) <= self.VM_MaxLoad)

    def __GC3(self):
        """The components are deployed only on acquired VM"""
        for j in range(self.nrVM):
            for i in range(self.nrComp):
                self.solver.Add(self.a[i * self.nrVM + j] <= self.vm[j])

    def RestrictionConflict(self, alphaCompID, conflictCompsIDList):
        """
        Constrain that describe the constraints between components
        :param alphaComponentId - ID of the component that is in conflict with other components,
                                  ID should be in set {1,...,N}
        :param conflictCompsIDList - the IDs list of components that alphaComponent is in conflict,
                                     ID should be in set {1,...,N}
        """
        for j in range(self.nrVM):
            for conflictCompId in conflictCompsIDList:
                self.solver.Add(self.solver.Sum([self.a[alphaCompID * self.nrVM + j],  self.a[conflictCompId * self.nrVM + j]]) <= 1)

    def RestrictionUpperLowerEqualBound(self, compsIdList, n1, operation):
        """
        Constrains that defines the number of instances that a component must have
        :param compsIdList:
        :param n1: a positive limit for components number
        :param operation: should be one of the strings {"<=","==",">="}
            "<=": sum(compsIdList) <= n1
            ">=": sum(compsIdList) >= n1
            "==": sum(compsIdList) == n1
        """
        if operation == "<=":
            self.solver.Add(
                self.solver.Sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) <= n1)
        elif operation == ">=":
            self.solver.Add(
                self.solver.Sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in
                                 range(self.nrVM)]) >= n1)
        elif operation == "==":
            self.solver.Add(
                self.solver.Sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in
                                 range(self.nrVM)]) == n1)

    def RestrictionRangeBound(self, compsIdList, n1, n2):
        """
        Constrains that defines the number of instances that a component must have
        :param compsIdList:
        :param n1: a positive lower limit for components number
        :param n2: a positive upper limit for components number
        """
        self.solver.Add(
            self.solver.Sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) >= n1)
        self.solver.Add(
            self.solver.Sum([self.a[compId * self.nrVM + j] for compId in compsIdList for j in range(self.nrVM)]) <= n2)

    def RestrictionFullDeployment(self, alphaCompId, compsIdList):
        """
        Component alpha must be deployed on all machines except the ones that contains components that component alpha in in conflict
        :param alphaCompId: the component id that must be deployed on all machines
        s:param compsIdList: the list of components that component alpha is not in conflict
        :return: None
        """
        for j in range(self.nrVM):
            self.solver.Add(self.solver.Sum([self.a[alphaCompId * self.nrVM + j]]+[self.a[_compId * self.nrVM + j]
                                                                                   for _compId in compsIdList]) == self.vm[j])

    def minimumVmsNumberConstraint(self, minNrOfVm):
        """
        Minimum VM number that should be aquaired
        NOT USED NOW
        :param minNrOfVm:
        :return: None
        """
        self.solver.Add(self.solver.Sum([self.vm[j] for j in range(self.nrVM)]) >= minNrOfVm)

    def RestrictionManyToManyDependency(self, alphaCompId, betaCompId, operation):
        """
        The number of instance of component alpha depends on the number of instances of component beta
        :param alphaCompId: ID of component alpha, ID should be in set {1,...,N}
        :param betaCompId: ID of component beta, ID should be in set {1,...,N}
        :param operation: one of the strings in set {"==", "<=", ">="}
            "==": sum(instances of alpha component) == sum(instances of beta component)
            "<=": sum(instances of alpha component) <= sum(instances of beta component)
            ">=": sum(instances of alpha component) >= sum(instances of beta component)
        :return: None
        """
        if operation == "<=":
            self.solver.Add(
                self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <=
                self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
        elif operation == ">=":
            self.solver.Add(
                self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >=
                self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))
        elif operation == "==":
            self.solver.Add(
                self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) ==
                self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))

    def RestrictionManyToManyDependencyNew(self, alphaCompId, betaCompId, n, m):
        """
        The number of instance of component alpha depends on the number of instances of component beta
        :param alphaCompId: ID of component alpha, ID should be in set {1,...,N}
        :param betaCompId: ID of component beta, ID should be in set {1,...,N}
        :param operation: one of the strings in set {"==", "<=", ">="}
            "==": sum(instances of alpha component) == sum(instances of beta component)
            "<=": sum(instances of alpha component) <= sum(instances of beta component)
            ">=": sum(instances of alpha component) >= sum(instances of beta component)
        :return: None
        """

        self.solver.Add(
            m * self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
            n * self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) >= 0)
        self.solver.Add(
            m * self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) -
            n * self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) < n*m)

        self.solver.Add(
            m * self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) >= n)

        self.solver.Add(
            n * self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <= int(m*self.nrVM))





    def RestrictionOneToManyDependency(self, alphaCompId, betaCompId, n):
        """
        For one alpha component should be deployed n beta components
        old: SC4 Flor
        :param alphaCompId: ID of component alpha, ID should be in set {1,...,N}
        :param betaCompId: ID of component beta, ID should be in set {1,...,N}
        :param n: depending instances number
        :return:
        """
        self.solver.Add(
            n*self.solver.Sum([self.a[alphaCompId * self.nrVM + k] for k in range(self.nrVM)]) -
            self.solver.Sum([self.a[betaCompId * self.nrVM + k] for k in range(self.nrVM)]) >= 0) #insteed of > to enshure that for q_n beta components q_n alpha compoments

        self.solver.Add(
            n * self.solver.Sum([self.a[alphaCompId * self.nrVM + k] for k in range(self.nrVM)]) -
            self.solver.Sum([self.a[betaCompId * self.nrVM + k] for k in range(self.nrVM)]) < n) #insteed of <= for same reason like before


        ### multiplu exact de n => ok nr de alpha
        # self.solver.Add(
        #     n * self.solver.Sum([self.a[alphaCompId * self.nrVM + k] for k in range(self.nrVM)]) -
        #     self.solver.Sum([self.a[betaCompId * self.nrVM + k] for k in range(self.nrVM)]) >= 0)
        #
        # self.solver.Add(
        #     n * self.solver.Sum([self.a[alphaCompId * self.nrVM + k] for k in range(self.nrVM)]) -
        #     self.solver.Sum([self.a[betaCompId * self.nrVM + k] for k in range(self.nrVM)]) < n)


#subset de sc4  - doua componente depind una de alta (trebuie tot timpul sa fie puse impreuna pe aceeasi masina)
    def RestrictionOneToOneDependency(self, alphaCompId, betaCompId):
        """
        Components alpha and beta should always be deployed together
        :param alphaCompId: ID of component alpha, ID should be in set {1,...,N}
        :param betaCompId: ID of component beta, ID should be in set {1,...,N}
        :return:
        """
        for k in range(self.nrVM):
            self.solver.Add(self.a[alphaCompId * self.nrVM + k] == self.a[betaCompId * self.nrVM + k])

    def constraintsHardware(self, componentsValues):

        if self.availableConfig is None:
            return
        # if self.availableConfig is None:
        #     self.problem.logger.debug("Optimize machine number because no offers are available")
        #     self.solver.Add(self.cost == self.solver.Sum(self.vm[j] for j in range(self.nrVM)))
        #     return

        self.problem.logger.debug("Hardware constaints: componentsValues: {} avalibaleConfigurations: {}".format(
            componentsValues, self.availableConfig))
        """
        for line in componentsValues:
            for i in line:
                if i is None:
                    return
        """

        componentsValues =[[0 if val is None else val for val in line] for line in componentsValues]


        #pt fiecare tip de configuratie (cp, mem, ..) exista o masina care le respecta pe toate
        #print("componentsValues=",componentsValues, "\n availableConfigurationsValues=", availableConfigurationsValues)
        hardwareLen  = len(componentsValues[0])
        availableConfLen = len(self.availableConfig)

        #print("availableConfig: ")
        if self.__solveVariantSMTEncoding:
            for k in range(self.nrVM):
                self.solver.Add(self.solver.Sum([self.a[i * self.nrVM + k] * int(componentsValues[i][0])
                                                  for i in range(self.nrComp)]) <= self.ProcProv[k])
                self.solver.Add(self.solver.Sum([self.a[i * self.nrVM + k] * int(componentsValues[i][1])
                                                  for i in range(self.nrComp)]) <= self.MemProv[k])
                self.solver.Add(self.solver.Sum([self.a[i * self.nrVM + k] * int(componentsValues[i][2])
                                                  for i in range(self.nrComp)]) <= self.StorageProv[k])

        else:
            print("!!!!!!!!!!!!old check")
            # if not self.__optimizePrice:
            #     for k in range(self.nrVM):
            #         self.solver.Add(
            #             self.solver.Sum([
            #                 self.solver.Sum([
            #                     self.solver.Sum([
            #                         self.solver.Sum([self.a[i * self.nrVM + k] * componentsValues[i][h] for i in range(self.nrComp)])
            #                     <= conf[h + 1] for h in range(hardwareLen)])
            #                 == hardwareLen]) for conf in availableConfigurationsValues])
            #             >= 1
            #         )



    def RestrictionAlphaOrBeta(self, alphaCompId, betaCompId):
        self.solver.Add(
            self.solver.Sum([
             self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]) > 0,
             self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) > 0]) == 1)

    def RestrictionRequireProvideDependency(self, alphaCompId, betaCompId, n, m):
        self.solver.Add(
            n * self.solver.Sum([self.a[alphaCompId * self.nrVM + j] for j in range(self.nrVM)]) <=
            m * self.solver.Sum([self.a[betaCompId * self.nrVM + j] for j in range(self.nrVM)]))


    def __runMinimizationProblem(self):
        """
        Minimize mumber of virtual machines
        :return:
        """
        #print("-----------runminimization problem")
        # problem objective is to minimize price
        self.objective = self.solver.Minimize(self.cost, 1)
        # Create a solution collector.
        self.collector = self.solver.LastSolutionCollector()
        # Add the decision variables.
        self.collector.Add(self.a)
        self.collector.Add(self.vm)
        self.collector.Add(self.PriceProv)

        # Add the objective.
        self.collector.AddObjective(self.cost)

        startTime = time.process_time()
        self.solver.Solve(self.decision_builder, [self.limits, self.objective, self.collector])
        #self.solver.Solve(self.decision_builder, [self.objective, self.collector])
        stopTime = time.process_time()

        return startTime, stopTime

    def __runCPProblem(self):
        """
        Just run CP problem
        :return:
        """
        # Create a solution collector.
        self.collector = self.solver.AllSolutionCollector()
        # Add the decision variables.
        self.collector.Add(self.a)
        self.collector.Add(self.vm)
        self.collector.Add(self.cost)
        self.collector.Add(self.PriceProv)

        startTime = time.process_time()
        self.solver.Solve(self.decision_builder, [self.limits,  self.collector])
        stopTime = time.process_time()

        return startTime, stopTime

    def __rebuild_solution(self, solutionIndex):
        _vm = []
        _a = []
        _priceVector = []

        for vm in self.vm:
            _vm.append(self.collector.Value(solutionIndex, vm))

        i = 0
        line = []
        for el in self.a:
            if i % self.nrVM == 0 and len(line) > 0:
                _a.append(line)
                line = []
            line.append(self.collector.Value(solutionIndex, el))
            i += 1
        _a.append(line)

        for p in self.PriceProv:
            _priceVector.append(self.collector.Value(solutionIndex, p))

        #print("Optimal cost:",_priceVector)

        return numpy.sum(_priceVector), _priceVector, numpy.sum(_vm), _a

    def run(self):
        #print("-----start run")
        if self.__optimization_problem:
            startTime, stopTime = self.__runMinimizationProblem()
        else:
            startTime, stopTime = self.__runCPProblem()
        #print("end run")
        _vm = []
        _a = []
        _costVector = []

        objectiveValue = -1

        if self.__optimization_problem:
            if self.collector.SolutionCount() > 0:
                #print("SOLUTIONS NUMBER: ", self.collector.SolutionCount())
                best_solution = self.collector.SolutionCount() - 1
                objectiveValue = self.collector.ObjectiveValue(best_solution)
                #print("Objective value:", best_nr_of_vm)

                cost, _costVector, _vm, _a = self.__rebuild_solution(best_solution)

        else: #collec more solutions
            if self.collector.SolutionCount() > 0:
                #print("SOLUTIONS NUMBER (not optimization): ", self.collector.SolutionCount())
                best_nr_of_vm = None
                for solIndex in range(self.collector.SolutionCount()):
                    cost, aux_costVector, aux_vm, aux_a = self.__rebuild_solution(solIndex)
                    _vm.append(aux_vm)
                    _a.append(aux_a)
                    _costVector.append(aux_costVector)
                    # print('--vm--')
                    # print(aux_vm)
                    # print('--a--')
                    # #if 1 not in aux_a[len(aux_a)-1]:
                    # for i in aux_a:
                    #     print(i)
                    if best_nr_of_vm is None:
                        best_nr_of_vm = numpy.sum(aux_vm)
                    else:
                        aux = numpy.sum(aux_vm)
                        if aux < best_nr_of_vm:
                            best_nr_of_vm = aux

        return objectiveValue, _costVector, _vm, _a


