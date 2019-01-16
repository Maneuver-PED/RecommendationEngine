import time
import numpy
from ortools.constraint_solver import pywrapcp

class CP_Solver_Got_Nr_Instances:
    def __init__(self, problem, solver_type, nr_of_solution_limit):
        self.problem = problem
        self.nrComp = problem.nrComp
        self.option = solver_type
        self.__optimizePrice = False  # variable used to add logic for price minimization
        self.__nr_of_solution_limit = nr_of_solution_limit
        self.__defineSolver(self.option)


    def __defineSolver(self, option):

        # define solver
        parameters = pywrapcp.Solver.DefaultSolverParameters()
        self.solver = pywrapcp.Solver("maneuver_CP_GOT_ll", parameters)
        self.cost = None

        # define some cut limits
        time_limit = 50000# 4 minute
        branch_limit = 100000000
        failures_limit = 100000000
        solutions_limit = self.__nr_of_solution_limit  # 10000
        self.limits = self.solver.Limit(time_limit, branch_limit, failures_limit, solutions_limit, True)

        self.__defineVarinables()


        variables = self.components
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

    def __defineVarinables(self):
        self.components = [self.solver.IntVar(0, 100000, "C%i" % j) for j in range(0, self.nrComp)]
        self.cost = self.solver.IntVar(0, 1000000, 'cost')
        self.solver.Add(self.cost == self.solver.Sum(component for component in self.components))

    def RestrictionUpperLowerEqualBound(self, compsIdList, n1, operation):
        """
        Constraint that defines the number of instances that a component must have
        :param compsIdList:
        :param n1: a positive limit for components number
        :param operation: should be one of the strings {"<=","==",">="}
            "<=": sum(compsIdList) <= n1
            ">=": sum(compsIdList) >= n1
            "==": sum(compsIdList) == n1
        """
        if operation == "<=":
            self.solver.Add(
                self.solver.Sum([self.components[compId] for compId in compsIdList]) <= n1)
        elif operation == ">=":
            self.solver.Add(
                self.solver.Sum([self.components[compId] for compId in compsIdList]) >= n1)
        elif operation == "==":
            self.solver.Add(
                self.solver.Sum([self.components[compId] for compId in compsIdList]) == n1)

    def RestrictionRangeBound(self, compsIdList, n1, n2):
        """
        Constrains that defines the number of instances that a component must have
        :param compsIdList:
        :param n1: a positive lower limit for components number
        :param n2: a positive upper limit for components number
        """
        self.solver.Add(self.solver.Sum([self.components[compId] for compId in compsIdList]) >= n1)
        self.solver.Add(self.solver.Sum([self.components[compId] for compId in compsIdList]) <= n2)


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
            self.solver.Add(self.components[alphaCompId] <= self.components[betaCompId])
        elif operation == ">=":
            self.solver.Add(self.components[alphaCompId] >= self.components[betaCompId])
        elif operation == "==":
            self.solver.Add(self.components[alphaCompId] == self.components[betaCompId])

    def RestrictionOneToManyDependency(self, alphaCompId, betaCompId, n):
        """
        For one alpha component should be deployed n beta components
        :param alphaCompId: ID of component alpha, ID should be in set {1,...,N}
        :param betaCompId: ID of component beta, ID should be in set {1,...,N}
        :param n: depending instances number
        :return:
        """
        self.solver.Add(n * self.components[alphaCompId] - self.components[betaCompId] > 0)
        self.solver.Add(n * self.components[alphaCompId] - self.components[betaCompId] <= n)

    def RestrictionAlphaOrBeta(self, alphaCompId, betaCompId):
        self.solver.Add(self.solver.Sum([self.components[alphaCompId] > 0, self.components[betaCompId] > 0]) == 1)

    def RestrictionRequireProvideDependency(self, alphaCompId, betaCompId, n, m):
        self.solver.Add(n * self.components[alphaCompId] <= m * self.components[betaCompId])




    def __runMinimizationProblem(self):
        """
        Minimize mumber of virtual machines
        :return:
        """
        # problem objective is to minimize price
        self.objective = self.solver.Minimize(self.cost, 1)
        # Create a solution collector.
        self.collector = self.solver.LastSolutionCollector()
        # Add the decision variables.
        self.collector.Add(self.components)

        # Add the objective.
        self.collector.AddObjective(self.cost)

        startTime = time.process_time()
        self.solver.Solve(self.decision_builder, [self.limits, self.objective, self.collector])
        stopTime = time.process_time()


        #print("**********", stopTime - startTime, self.objective)

        return startTime, stopTime

    def __runCPProblem(self):
        """
        Just run CP problem
        :return:
        """
        # Create a solution collector.
        self.collector = self.solver.AllSolutionCollector()
        # Add the decision variables.
        self.collector.Add(self.components)

        startTime = time.process_time()
        self.solver.Solve(self.decision_builder, [self.limits,  self.collector])
        stopTime = time.process_time()

        return startTime, stopTime

    def __rebuild_solution(self, solutionIndex):
        _components = []

        for comp in self.components:
            _components.append(self.collector.Value(solutionIndex, comp))

        return _components

    def run(self):

        startTime, stopTime = self.__runMinimizationProblem()

        _components = []
        if self.collector.SolutionCount() > 0:
            best_solution = self.collector.SolutionCount() - 1
            _components = self.__rebuild_solution(best_solution)

        # self.NUMARUL_DE_CONFIGURATII

        self.problem.logger.debug("Nr of instances for each component: {}".format(_components))

        return (stopTime - startTime),  _components



    def RestrictionConflict(self, comp_id, conflict_comps_id_list):
        return

    def constraintsHardware(self, components_values, available_configurations):
        return

    def RestrictionOneToOneDependency(self, compId, relatedCompId):
        return

    def RestrictionFullDeployment(self, compId, compsIdList):
        return

    def RestrictionManyToManyDependencyNew(self,  alphaCompId, betaCompId, n,m):

        self.solver.Add(m*self.components[betaCompId] - n*self.components[alphaCompId] >= 0)
