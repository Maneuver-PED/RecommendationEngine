from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3 import Z3_Solver_Parent


class Z3_SolverIntInt(Z3_Solver_Parent):#ManeuverProblem):


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


        super()._encodeOffers(1)

    def constraintsHardware(self, componentsRequirements):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """

        super()._constraintsHardware(componentsRequirements, 1)


    def convert_price(self, price):
        return price / 1000.0
