from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3 import Z3_Solver_Parent
#from util.UtilsRE import Constants

class Z3_SolverReal(Z3_Solver_Parent):

    def _defineVariablesAndConstraints(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding, usage vector, etc.)
        :return: None
        """
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        #self.vm = {}
        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        self.a = {}
        # VMType  - type of a leased VM
        self.VMType = {}

        # values from availableConfigurations
        self.ProcProv = [Real('ProcProv%i' % j) for j in range(1, self.nrVM + 1)]
        self.MemProv = [Real('MemProv%i' % j) for j in range(1, self.nrVM + 1)]
        self.StorageProv = [Real('StorageProv%i' % j) for j in range(1, self.nrVM + 1)]
        self.PriceProv = [Real('PriceProv%i' % j) for j in range(1, self.nrVM + 1)]

        if self.use_vm_vector_in_encoding:
            self.vm = [Real('VM%i' % j) for j in range(1, self.nrVM + 1)]
            # elements of VM should be positive
            for i in range(len(self.vm)):
                if self.solverTypeOptimize:
                    self.solver.add(Or(self.vm[i] == 0, self.vm[i] == 1))
                else:
                    self.solver.assert_and_track(Or(self.vm[i] == 0, self.vm[i] == 1), "Label: " + str(self.labelIdx))
                    self.labelIdx += 1

        self.a = [Real('C%i_VM%i' % (i + 1, j + 1)) for i in range(self.nrComp) for j in range(self.nrVM)]
        # elements of the association matrix should be just 0 or 1
        for i in range(len(self.a)):
            if self.solverTypeOptimize:
                self.solver.add(Or(self.a[i] == 0, self.a[i] == 1))
            else:
                self.solver.assert_and_track(Or(self.a[i] == 0, self.a[i] == 1), "Label: " + str(self.labelIdx))
                self.labelIdx += 1


        self.vmType = [Real('VM%iType' % j) for j in range(1, self.nrVM + 1)]
        for i in range(self.nrComp):
            for j in range(self.nrVM):
                self.solver.add(Implies(self.a[i * self.nrVM + j] == 1, Not(self.vmType[j] == 0)))


        if self.use_vm_vector_in_encoding:
            # If a machine is leased then its assignment vector is 1
            for j in range(self.nrVM):
                if self.solverTypeOptimize:
                    self.solver.add(
                        Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) >= 1, self.vm[j] == 1))
                else:
                    self.solver.assert_and_track(
                        Implies(sum([self.a[i + j] for i in range(0, len(self.a), self.nrVM)]) >= 1, self.vm[j] == 1),
                        "LabelSC1: " + str(self.labelIdx))
                    self.labelIdx += 1

        # add the  the offers
        self._encodeOffers(1000.)
        super()._simetry_breaking()

    def constraintsHardware(self, componentsRequirements):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """

        super()._constraintsHardware(componentsRequirements, 1000.)
