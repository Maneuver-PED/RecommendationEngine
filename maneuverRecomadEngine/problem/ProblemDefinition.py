import json
import numpy
from maneuverRecomadEngine.restrictions.RestrictionConflicts import RestrictionConflict, RestrictionAlphaOrBeta
from maneuverRecomadEngine.restrictions.RestrictionDependences import RestrictionOneToOneDependency, \
    RestrictionOneToManyDependency, RestrictionManyToManyDependency, RestrictionManyToManyDependencyNew
from maneuverRecomadEngine.restrictions.RestrictionNumberOfInstances import RestrictionUpperLowerEqualBound, \
    RestrictionRangeBound, RestrictionFullDeployment, RestrictionRequireProvideDependency
from maneuverRecomadEngine.restrictions.RestrictionHardware import RestrictionHardware
from maneuverRecomadEngine.problem.Component import Component
import logging.config

class ManeuverProblem:
    def __init__(self):
        self.VM_MaxLoad = 20
        self.componentsList = {}  # list of components
        self.restrictionsList = []  # list of restrictions
        self.IpInfo = {}  # list with other information
        self.applicationName = None

        logging.config.fileConfig('loggerConfig.conf')
        self.logger = logging.getLogger("maneuverApp")
        self.priceOffersFile = None
        self.nrComp = 0
        self.nrVM = 0

    def init(self, nr_vm, nr_comp):# used at initilization for test instances
        self.nrVM = nr_vm
        self.nrComp = nr_comp
        self.R = numpy.zeros((self.nrComp, self.nrComp),  dtype=numpy.int) #conflicts graph
        self.D = numpy.zeros((self.nrComp, self.nrComp), dtype=numpy.int) #corelation hraph


    def solveSMT(self, availableConfigs, smt2lib, smt2libsol, solver_type, solver):
        """
        Solves the optimization problem using the imported SMT solver and available VMs configurations
        :param self: the optimization problem
        :param available_configurations: available VMs configurations
        :param solver_type: the Z3 solver type (optimize/debug)
        :return:
        """

        if solver == "SMT_Solver_Z3_IntIntOr":
            from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_IntIntOr
            SMTSolver = SMT_Solver_Z3_IntIntOr.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)
        elif solver == "SMT_Solver_Z3_IntIntLessThan":
            from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_IntIntLessThan
            SMTSolver = SMT_Solver_Z3_IntIntLessThan.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)
        elif solver == "SMT_Solver_Z3_RealReal":
            from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_RealReal
            SMTSolver = SMT_Solver_Z3_RealReal.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)
        elif solver == "SMT_Solver_Z3_RealBool":
             from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_RealBool
             SMTSolver = SMT_Solver_Z3_RealBool.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)
        elif solver == "SMT_Solver_Z3_BV":
             from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_BV
             SMTSolver = SMT_Solver_Z3_BV.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)
        elif solver == "SMT_Solver_Z3_RealSymBreak":
             from maneuverRecomadEngine.exactsolvers import SMT_Solver_Z3_RealSymBreak
             SMTSolver = SMT_Solver_Z3_RealSymBreak.Z3_Solver(self.nrVM, self.nrComp, availableConfigs, self, solver_type)

        if SMTSolver.availableConfigurations is not None:
            self.restrictionsList.append(
                RestrictionHardware(self._getComponentsHardwareRestrictions(), SMTSolver.availableConfigurations, self))

        for restriction in self.restrictionsList:
            restriction.generateRestrictions(SMTSolver)

        return SMTSolver.run(smt2lib, smt2libsol)

    def solveCP(self, choosing_stategy, solutions_limit, optimize_price, available_configurations, time_limit):
        """
        Start solving the problem using the chosen solver and available configurations for VM
        :param cpSolver: Solver choosed to solve the problem
        :return:
        """
        self.logger.info("Resolve problem using CP solver ")
        from maneuverRecomadEngine.exactsolvers import CP_Solver_GOT
        cpSolver = CP_Solver_GOT.CP_Solver_Got(self, choosing_stategy, solutions_limit, optimize_price,
                                               available_configurations, time_limit, self.nrVM)

        # cpSolver = CP_Solver_GOT.CP_Solver_Got(self, choosing_stategy, 2, False,
        #                                                                         None, 10000)

        self.restrictionsList.append(RestrictionHardware(self._getComponentsHardwareRestrictions(),
                                                         cpSolver.availableConfig, self))

        for restriction in self.restrictionsList:
            restriction.generateRestrictions(cpSolver)

        return cpSolver.run()



    def solveLIP(self, choosing_stategy, solutions_limit):
        """
        Start solving the problem using the chosen solver and available configurations for VM
        :param cpSolver: Solver choosed to solve the problem
        :return:
        """
        self.logger.info("Resolve problem using CP solver")
        from maneuverRecomadEngine.exactsolvers import CP_Solver_GOT_LP
        cpSolver = CP_Solver_GOT_LP.CP_Solver_GOT_LP(choosing_stategy, self)

        for restriction in self.restrictionsList:
            restriction.generateRestrictions(cpSolver)

        return cpSolver.run()

    def findPartitionsBasedOnConflictsMatrix(self):# inspired from tarjan algorithm

        visitedComponents = {}
        for i in range(self.nrComp):
            visitedComponents[i] = False

        #print("visitedComponents", visitedComponents)
        #print(self.R)
        partitions = [[]]
        for i in range(self.nrComp):
            if visitedComponents[i]:
                continue
            visitedComponents[i] = True

            print(i, "visitedComponents", visitedComponents)
            for partition in partitions:
                inConflic = False # in conflict cu cele din partitia curenta
                for j in partition:
                    if self.R[i][j] == 1:
                        inConflic = True

                        #print("conflict direct", i, j, partition)

                    else: #uitatate sa nu fie in conflict cu cele colocate
                        for compId in self.componentsList[j].dependenceComponentsList:
                            if self.R[i][compId] == 1:
                                inConflic = True
                                #print("conflict dependences", i, j, partition)
                                break
                if not inConflic:
                    partition.append(i)
                    break
            else:
                partitions.append([i])
            #print(i, partitions)

        #print("!!!!!!!!!!!!!!!", partitions)
        return partitions



    def solveCPNrOfInstances(self, choosing_stategy, solutions_limit):
        """
        Start solving components number problem using the chosen solver and available configurations for VM
        :param cpSolver: Solver choosed to solve the problem
        :return:
        """
        self.logger.info("Find number of needed virtual machines based on components number restrictions")
        from maneuverRecomadEngine.exactsolvers.CP_Solver_Number_of_Instances import CP_Solver_Got_Nr_Instances
        cpSolver = CP_Solver_Got_Nr_Instances(self, choosing_stategy, solutions_limit)

        for restriction in self.restrictionsList:
            restriction.generateRestrictions(cpSolver)

        return cpSolver.run()

    def solveEA(self, populationSize, cpInitializationNr, numberOfIterations, stagnationsSteps, EPSILON,
                probability_to_add_a_new_vm, availableOffers_CP):


        self.logger.info("Resolve problem using EA")
        from maneuverRecomadEngine.metaEuristics.evolutionaryAlgorithm.EvolutionaryAlgorithm import \
            EvolutionaryAlgorithm
        ea = EvolutionaryAlgorithm(populationSize, cpInitializationNr, numberOfIterations, stagnationsSteps, self,
                                   EPSILON, probability_to_add_a_new_vm, availableOffers_CP)
        ea.run()
        return ea.getSolution()

    def readConfiguration(self, jsonFilePath):
        """
        Open json file that contains problem configurations and fills problem data
        :param jsonFilePath:
        :return:
        """
        with open(jsonFilePath) as json_data:
            dictionary = json.load(json_data)
            self.logger.info(dictionary)
        self.applicationName = dictionary["application"]
        for component in dictionary["components"]:
            self._addComponent(component)

        self.init(len(self.componentsList), len(self.componentsList))

        orComponents = set()
        for restriction in dictionary["restrictions"]:
            for comp in self._addRestriction(restriction):
                orComponents.add(comp)

        self.nrComp = len(self.componentsList)

        self.IpInfo = dictionary["IP"]

        # add restriction OS
        self.__addOperationSystemRestriction()

        # add information about minimum number of instances of each component
        self.__addRestrictionsComponentsNumber(orComponents)

        # find minimum components number based on problem description regarding components number
        self.nrVM = self.__findMinimumNumberOfInstancesForEachComponent(orComponents)
        print("..........self.nrVM", self.nrVM)

        # add other useful information for EA alg
        #  -- like number of conflicts that a component is in
        self.__addInformationForEA()

    def __addInformationForEA(self):
        for i in range(self.nrComp):
            for j in range(self.nrComp):
                if self.R[i][j] == 1:
                    self.componentsList[i].conflictComponentsList.add(j)
            self.componentsList[i].numberOfConflictComponents = len(self.componentsList[i].conflictComponentsList)
        for i in range(self.nrComp):
            for j in range(self.nrComp):
                if self.D[i][j] == 1:
                    self.componentsList[i].dependenceComponentsList.add(j)

    def __findMinimumNumberOfInstancesForEachComponent(self, orComponents):
        """
        Resolve CP problem regarding minimum number of instances needed for each component and add this information to
        each component
        :param orComponents:
        :return: number of VM, if each component in in conflict with the others components
        """
        runningTime, components = self.solveCPNrOfInstances("LOWEST_MIN_MIN", 10000)
        print("components", components)
        for (compId, comp) in self.componentsList.items():
            comp.minimumNumberOfInstances = components[compId]

        minimumBeanNr = self.findPartitionsBasedOnConflictsMatrix()
        return numpy.sum(components) #+ len(minimumBeanNr)

    def __addRestrictionsComponentsNumber(self, orComponents):
        """
        Adds restriction regarding the fact that at least one component should be deployed.
        The components that are not in 'OR' relation should be deployed alt least one time.
        :param orComponents: list of components in 'OR' relation
        :return:
        """
        all_comps = set()
        for component in self.componentsList:
            all_comps.add(component+1)
        all_comps = all_comps.difference(orComponents)

        print ("all_comps", all_comps, "orcomps", orComponents, "elf.componentsList", self.componentsList)
        for compId in all_comps:
            self.restrictionsList.append(RestrictionUpperLowerEqualBound([compId], ">=", 1, self))

    def __addOperationSystemRestriction(self):
        """
        Add conflict restriction induced by the fact that different components need different operating system.
        The restriction is induced by the fact that the user is not adding explicit restrictions
        :return:
        """
        dict = {}
        for comp in self.componentsList:
            if not ((self.componentsList[comp].operatingSystem is None) or (len(self.componentsList[comp].operatingSystem) == 0)):
                if self.componentsList[comp].operatingSystem in dict:
                    dict[self.componentsList[comp].operatingSystem].append(comp)
                else:
                    dict[self.componentsList[comp].operatingSystem] = [comp]
        self.logger.debug("Operating system of the components: {}".format(dict))
        dict2 = dict.copy()
        if len(dict) > 1:
            for i in dict:
                dict2.pop(i, None)
                for j in dict2:
                    for k in dict[i]:
                        self.restrictionsList.append(RestrictionConflict(k + 1, [u + 1 for u in dict2[j]], self))

    def _addComponent(self, comp_dictionary):
        """
        From json description of the component extract the properties and stores them into a instance of Component class
        :param comp_dictionary: a dictionary loaded from json component description
        :return:
        """
        id = comp_dictionary["id"] - 1

        c = Component(id, comp_dictionary["name"] if "name" in comp_dictionary else None,
                      comp_dictionary["Compute"]["CPU"] if "CPU" in comp_dictionary["Compute"] else None,
                      comp_dictionary["Compute"]["GPU"] if "GPU" in comp_dictionary["Compute"] else "false",
                      comp_dictionary["Compute"]["Memory"] if "Memory" in comp_dictionary["Compute"] else None,

                      comp_dictionary["Storage"]["StorageSize"] if "StorageSize" in comp_dictionary["Storage"] else 50,
                      comp_dictionary["Storage"]["StorageType"] if "StorageType" in comp_dictionary["Storage"] else None,
                      comp_dictionary["Storage"]["StorageValue"] if "StorageValue" in comp_dictionary["Storage"] else None,

                      comp_dictionary["Network"]["dataIn"] if "dataIn" in comp_dictionary["Network"] else None,
                      comp_dictionary["Network"]["dataOut"] if "dataOut" in comp_dictionary["Network"] else None,
                      comp_dictionary["Network"]["networkConnections"] if "networkConnections" in comp_dictionary[
                          "Network"] else None,

                      comp_dictionary["keywords"] if "keywords" in comp_dictionary else None,
                      comp_dictionary["operatingSystem"] if "operatingSystem" in comp_dictionary else None)

        self.componentsList[id] = c

    def _addRestriction(self, dictionary):
        """
        From json description extracts the restrictions (conflict, multiplicity and dependency between components
        :param restrictionDictionary: From json description of the components restrictions
        :return:
        """
        dictionaryOrRelation = set()
        restrictionType = dictionary["type"]
        if restrictionType == "Conflicts":
            self.restrictionsList.append(RestrictionConflict(dictionary["alphaCompId"], dictionary["compsIdList"], self))

        elif restrictionType == "OneToOneDependency":
            self.restrictionsList.append(RestrictionOneToOneDependency(dictionary["alphaCompId"],
                                                                       dictionary["betaCompId"], self))
        elif restrictionType == "ManyToManyDependency":
            self.restrictionsList.append(RestrictionManyToManyDependency(dictionary["alphaCompId"],
                                                                         dictionary["betaCompId"],
                                                                         dictionary["sign"], self))
        elif restrictionType == "ManyToManyDependencyNew":
            self.restrictionsList.append(RestrictionManyToManyDependencyNew(dictionary["alphaCompId"],
                                                                         dictionary["betaCompId"],
                                                                         dictionary["n"],
                                                                         dictionary["m"], self))
        elif restrictionType == "OneToManyDependency":
            self.restrictionsList.append(
                RestrictionOneToManyDependency(dictionary["alphaCompId"], dictionary["betaCompId"],
                                               dictionary["number"], self))
        elif restrictionType == "RangeBound":
            self.restrictionsList.append(RestrictionRangeBound(dictionary["components"],
                                                               dictionary["lowerBound"],
                                                               dictionary["upperBound"], self))
        elif restrictionType == "UpperBound":
            self.restrictionsList.append(RestrictionUpperLowerEqualBound(dictionary["compsIdList"], "<=",
                                                                         dictionary["bound"], self))
        elif restrictionType == "LowerBound":
            self.restrictionsList.append(RestrictionUpperLowerEqualBound(dictionary["compsIdList"], ">=",
                                                                         dictionary["bound"], self))
        elif restrictionType == "EqualBound":
            self.restrictionsList.append(RestrictionUpperLowerEqualBound(dictionary["compsIdList"], "=",
                                                                         dictionary["bound"], self))
        elif restrictionType == "FullDeployment":
            self.restrictionsList.append(RestrictionFullDeployment(dictionary["alphaCompId"],
                                                                   dictionary["compsIdList"], self))
        elif restrictionType == "RequireProvideDependency":
            self.restrictionsList.append(RestrictionRequireProvideDependency(dictionary["alphaCompId"],
                                                                             dictionary["betaCompId"],
                                                                             dictionary["alphaCompIdInstances"],
                                                                             dictionary["betaCompIdInstances"], self))
        elif restrictionType == "AlternativeComponents":
            self.restrictionsList.append(RestrictionAlphaOrBeta(dictionary["alphaCompId"], dictionary["betaCompId"],
                                                                self))
            dictionaryOrRelation.add(dictionary["alphaCompId"])
            dictionaryOrRelation.add(dictionary["betaCompId"])

        return dictionaryOrRelation


    def __repr__(self):
        for i in self.componentsList:
            print(i)
        return str(self.componentsList)

    def _getComponentsHardwareRestrictions(self):
        """
        Resturns a list with hardware restriction for each component
        :return:
        """
        print("len(self.componentsList)", len(self.componentsList))
        return [self.componentsList[compId].getComponentHardWareResources() for compId in range(0, len(self.componentsList))]

    def compareComponentsRegardingHardwareRestrictions(self, compAlphaId, compBetaId):
        """
        Finds which component alpha or beta needs more hardware resources
        :param compAlphaId: alpha component id
        :param compBetaId: beta component id
        :return: sumAlpha - in how many cases component alpha needs less resources that component beta
                 sumBeta - in how many cases component beta needs less resources that component alpha
        """
        compAlpha = self.componentsList[compAlphaId]
        compBeta = self.componentsList[compBetaId]
        sumAlpha = 0  # add 1 if alpha component need less resources then beta components
        sumBeta = 0  # add 1 if beta component need less resources then alpha components
        retAlpha, retBeta = self.__compareResource(compAlpha.HM, compBeta.HM)
        sumAlpha += retAlpha
        sumBeta += retBeta

        retAlpha, retBeta = self.__compareResource(compAlpha.HC, compBeta.HC)
        sumAlpha += retAlpha
        sumBeta += retBeta

        retAlpha, retBeta = self.__compareResource(compAlpha.HS, compBeta.HS)
        sumAlpha += retAlpha
        sumBeta += retBeta

        retAlpha, retBeta = self.__compareResource(compAlpha.NIn, compBeta.NIn)
        sumAlpha += retAlpha
        sumBeta += sumBeta

        retAlpha, retBeta = self.__compareResource(compAlpha.NOut, compBeta.NOut)
        sumAlpha += retAlpha
        sumBeta += retBeta

        retAlpha, retBeta = self.__compareResource(compAlpha.NConnections, compBeta.NConnections)
        sumAlpha += retAlpha
        sumBeta += retBeta
        return sumAlpha, sumBeta

    def __compareResource(self,alphaValue, betaValue):
        """
        Compare 2 hardware resources to which component alpha or beta needs more resources
        :param alphaValue: alpha component resource value
        :param betaValue: beta component resource value
        :return: retAlpha - 1 if component alpha needs more resources that component beta, 0 otherwais
                 retBeta - 1 if component beta needs more resources that component alpha, 0 otherwais
        """
        retAlpha = 0
        retBeta = 0
        if (alphaValue is None) and (betaValue is None):
            return retAlpha, retBeta
        if (alphaValue is None) and (betaValue is not None):
            if betaValue.HM > 0:
                retAlpha = 1
        elif (betaValue is None) and (alphaValue is not None):
            if alphaValue > 0:
                retBeta = 1
        return retAlpha, retBeta