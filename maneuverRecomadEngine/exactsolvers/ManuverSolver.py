from maneuverRecomadEngine.restrictions.RestrictionHardware import RestrictionHardware

class ManuverSolver(object):

    def init_problem(self, problem, solver_type, default_offers_encoding=True, sb_vms_order_by_price=False,
                     sb_vms_order_by_components_number=False,
                     sb_fix_variables=False, sb_redundant_price=False, sb_redundant_processor=False, sb_redundant_memory=False,
                     sb_redundant_storage=False, sb_equal_vms_type_order_by_components_number=False,
                     sb_equal_vms_type_order_lex = False,
                     smt2lib=None, smt2libsol=None,
                     use_vm_vector_in_encoding=False, offers_list_filtered=False, sb_one_to_one_dependency=False):


        self.__constMap = {}
        self.problem = problem
        self.nrVM = self.problem.nrVM
        self.nrComp = self.problem.nrComp
        self.vm_with_offers = {}
        self.vmIds_for_fixedComponents = set()
        if solver_type == "optimize":
            self.solverTypeOptimize = True  # optimize, debug
        else:
            self.solverTypeOptimize = False

        self.offers_list = self.problem.offers_list
        self.sb_vms_order_by_price = sb_vms_order_by_price
        self.sb_vms_order_by_components_number = sb_vms_order_by_components_number
        self.sb_fix_variables = sb_fix_variables
        self.sb_redundant_price = sb_redundant_price
        self.sb_redundant_processor = sb_redundant_processor
        self.sb_redundant_memory = sb_redundant_memory
        self.sb_redundant_storage = sb_redundant_storage
        self.sb_equal_vms_type_order_by_components_number = sb_equal_vms_type_order_by_components_number
        self.sb_equal_vms_type_order_lex =sb_equal_vms_type_order_lex
        self.smt2lib = smt2lib
        self.smt2libsol = smt2libsol
        self.use_vm_vector_in_encoding = use_vm_vector_in_encoding
        self.offers_list_filtered = offers_list_filtered
        self.sb_one_to_one_dependency = sb_one_to_one_dependency
        self.default_offers_encoding = default_offers_encoding

        print("self.default_offers_encoding", self.default_offers_encoding)

        self._initSolver()

        from maneuverRecomadEngine.restrictions.RestrictionHardware import RestrictionHardware
        from maneuverRecomadEngine.restrictions.RestrictionConflicts import RestrictionConflict, RestrictionAlphaOrBeta
        from maneuverRecomadEngine.restrictions.RestrictionDependences import RestrictionOneToManyDependency, RestrictionOneToOneDependency, RestrictionManyToManyDependency
        for restriction in self.problem.restrictionsList:
            restriction.generateRestrictions(self)

        self._simetry_breaking()

    def run(self):
        print("Start evaluation")

    def _simetry_breaking(self):
        print("Parent class simetry breaking")

    def _initSolver(self):
        print("Start solver initialization")

    def RestrictionConflict(self, alphaCompId, conflictCompsIdList):
        """
        Constraint describing the conflict between components. The 2 params. should not be placed on the same VM
        :param alphaCompId: id of the first conflict component
        :param conflictCompsIdList: id of the second conflict component
        :return: None
        """
        print("Parent class RestrictionConflict")

    def RestrictionOneToOneDependency(self, alphaCompId, betaCompId):
        """
        Contraint describing that alphaCompId and betaCompId should be deployed on the same VM
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return: None
        """
        print("Parent class RestrictionOneToOneDependency")

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
        print("Parent class RestrictionManyToManyDependency")

    def RestrictionOneToManyDependency(self, alphaCompId, betaCompId, noInstances):
        """
        At each alphaCompId component should be deployed noInstances betaCompId components
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :param noInstances: depending instances number
        :return: None
        """
        print("Parent class RestrictionOneToManyDependency")

    def RestrictionRangeBound(self, compsIdList, lowerBound, upperBound):
        """
        Defines a lower and upper bound of instances that a component must have
        :param compsIdList: list of components
        :param lowerBound: a positive number
        :param upperBound: a positive number
        :return:
        """
        for i in range(len(compsIdList)): compsIdList[i] -= 1
        print("Parent class RestrictionRangeBound")

    def RestrictionFullDeployment(self, alphaCompId, notInConflictCompsIdList):
        """
        Adds the fact that the component alphaCompId must be deployed on all machines except the ones that contain
         components that alphaCompId alpha is in conflict with
        :param alphaCompId: the component which must be fully deployed
        :param notInConflictCompsIdList: the list of components that alphaCompId is not in conflict in
        :return: None
        """
        print("Parent class RestrictionFullDeployment")

    def RestrictionRequireProvideDependency(self, alphaCompId, betaCompId, alphaCompIdInstances,
                                            betaCompIdInstances):
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

        print("Parent class RestrictionRequireProvideDependency")

    def RestrictionAlphaOrBeta(self, alphaCompId, betaCompId):
        """
        Describes the fact that alphaCompId or betaCompId not both
        :param alphaCompId: id of the first component
        :param betaCompId: id of the second component
        :return:
        """
        print("Parent class RestrictionAlphaOrBeta")

    def constraintsHardware(self, componentsRequirements):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """

        print("Parent class constraintsHardware")

    def run(self):
        """
        Invokes the solving of the problem (solution and additional effect like creation of special files)
        :param smt2lib: string indicating a file name storing the SMT2LIB encoding of the problem
        :param smt2libsol: string indicating a file name storing the solution of the problem together with a model (if applicable)
        :return:
        """
        print("Parent class run")

    def RestrictionFixComponentOnVM(self, comp_id, vm_id, value):
        """
          Force placing component on a specific VM
          :param comp_id: the ID of the component
          :param vm_id: the ID of the VM
          :return: None
          """
        print("Parent RestrictionFixComponentOnVM")

    def RestrictionPriceOrder(self, start_vm_id, end_vm_id):
        print("Parent RestrictionPriceOrder")