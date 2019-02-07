import random
import numpy
import json
from maneuverRecomadEngine.problem.OffersCaching import getChipesOffer
from maneuverRecomadEngine.restrictions.RestrictionNumberOfInstances import RestrictionFullDeployment

class Element:
    """
    A solution of the component allocation problem on a VM
    """
    def __init__(self, problem):
        self.problem = problem

        self.reset_solution_initialization()

        # evaluation measures
        self.violatedConstraintsNr = None
        self.vmsNr = None
        self.componentsNr = None

        #different measures - just for debug
        self.numberOfSucessMutations = 0
        self.priceList =[]
        self.howManyTimesANewElemetIsCreatedFromCurrentOne = 0


    def reset_solution_initialization(self):

        # solution encoded into cmp,vm matrix
        self.a = numpy.zeros((self.problem.nrComp, self.problem.nrVM), dtype=numpy.int)
        self.vms = set()

        # solution encoded, for each component store vm list
        self.solComponents = {}
        for compId in self.problem.componentsList.keys():
            self.solComponents[compId] = []  # list of empty VM for each component

        # solution encoded, for each vm store component list
        self.solVms = {}  # list of VM

        # vms const
        self.vmsPriceModified = {}
        self.vmsPrice = {}  # map vmId, vmCost
        self.elementCost = 0  # total configuration cost
        self.noOfferFond = set()  # store vmId for wich no offer is fond they will be taken in account by mutation in order to split

    def copy(self):
        """
        Copy the current element, need when try to create the new element into starting from current one population
        :return:
        """
        copy_el = Element(self.problem)
        copy_el.a = self.a.copy()
        copy_el.vms = self.vms.copy()
        copy_el.solComponents = {}
        for key in self.solComponents:
            copy_el.solComponents[key] = self.solComponents[key].copy()

        copy_el.solVms = {}
        for key in self.solVms:
            copy_el.solVms[key] = self.solVms[key].copy()

        copy_el.violatedConstraintsNr = self.violatedConstraintsNr
        copy_el.vmsNr = self.vmsNr
        copy_el.componentsNr = self.componentsNr


        copy_el.numberOfSucessMutations = self.numberOfSucessMutations
        copy_el.priceList = self.priceList
        copy_el.howManyTimesANewElemetIsCreatedFromCurrentOne = self.howManyTimesANewElemetIsCreatedFromCurrentOne


        copy_el.vmsPrice = self.vmsPrice.copy()
        copy_el.vmsPriceModified = {}
        copy_el.elementCost = self.elementCost
        copy_el.noOfferFound = self.noOfferFond

        #print("!!!!!!!!!!!!!", self.numberOfSucessMutations, copy_el.numberOfSucessMutations)

        return copy_el

    def eval_old(self):
        """
        Fills the information regarding element quality: nr of VM used, number of constraints violated,
        number of deployed components
        :return:
        """
        self.violatedConstraintsNr = 0
        for restriction in self.problem.restrictionsList:
            self.violatedConstraintsNr += restriction.eval(self.a)

        self.componentsNr = 0
        for comp in self.solComponents:
            self.componentsNr += len(self.solComponents[comp])

        self.vmsNr = len(self.vms)
        self.vmsPrice = {}
        self.elementCost = 0
        if self.violatedConstraintsNr == 0:
            __vms = list(self.vms)

            modifiedVms = self.buildSolutinInformations()
            vmsPrice_aux = getChipesOffer(json.loads(json.dumps(modifiedVms)))
            for i in range(len(__vms)):
                self.vmsPrice[__vms[i]] = vmsPrice_aux[str(i)]
                self.elementCost += float(self.vmsPrice[__vms[i]])
            self.problem.logger.debug("price: {} vms {}".format(self.vmsPrice, self.vms))
            self.vmsPriceModified = {}
        else:
            self.elementCost = 100000000
        self.priceList.append(self.elementCost)


    def eval(self):
        """
        Fills the information regarding element quality: nr of VM used, number of constraints violated,
        number of deployed components
        :return:
        """
        self.violatedConstraintsNr = 0
        for restriction in self.problem.restrictionsList:
            self.violatedConstraintsNr += restriction.eval(self.a)

        self.componentsNr = 0
        for comp in self.solComponents:
            self.componentsNr += len(self.solComponents[comp])

        self.vmsNr = len(self.vms)
        #self.vmsPrice = {} #//old price
        vmsPrice_aux = {}
        vmsPriceModified = {}
        self.noOfferFond = set()
        self.elementCost = 0
        #print("old price: ", self.vmsPrice)
        if self.violatedConstraintsNr == 0:
            __vms = list(self.vms)

            modifiedVms = self.buildSolutinInformations()
            #print("modifiedVms", modifiedVms.keys())

            #print("Before: modifiedvms-key: ", self.vmsPriceModified.keys(), " solution machines: ", modifiedVms.keys())
            if 'IP' in modifiedVms:
                modifiedVms.pop('IP', None)
            if len(self.vmsPrice) > 0:
                for vmId in self.vms:
                    if vmId not in self.vmsPriceModified:
                        modifiedVms.pop(vmId, None)
            #print("After:  modifiedvms-key: ", self.vmsPriceModified.keys(), " solution machines: ", modifiedVms.keys())
            else:
                for vmId in __vms:
                    self.vmsPriceModified[vmId] = True

            vmsPrice_aux = getChipesOffer(json.loads(json.dumps(modifiedVms)), self.problem.priceOffersFile)
            #print("offfer: ", vmsPrice_aux, __vms, "modifiedVms", modifiedVms.keys())
            for vmId in __vms:
                #print(vmId, "new peices" ,vmsPrice_aux, self.vmsPrice, self.vmsPriceModified)
                if vmId in self.vmsPriceModified:
                    if vmsPrice_aux[str(vmId)]["price"] == 50000000: #!!scoate constanta configurabila
                        self.noOfferFond.add(vmId)
                    self.vmsPrice[vmId] = vmsPrice_aux[str(vmId)]["price"]
                self.elementCost += float(self.vmsPrice[vmId])
            #self.problem.logger.debug("price: {} vms {}".format(self.vmsPrice, self.vms))
            self.vmsPriceModified = {}
        else:
            self.elementCost = 50000000
        self.priceList.append(self.elementCost)

    def eval_fara_pret(self):
        """
        Fills the information regarding element quality: nr of VM used, number of constraints violated,
        number of deployed components
        :return:
        """
        self.violatedConstraintsNr = 0
        for restriction in self.problem.restrictionsList:
            self.violatedConstraintsNr += restriction.eval(self.a)

        self.componentsNr = 0
        for comp in self.solComponents:
            self.componentsNr += len(self.solComponents[comp])

        self.vmsNr = len(self.vms)
        self.vmsPrice = {}  # //old price
        self.elementCost = 0
        if self.violatedConstraintsNr == 0:
            self.elementCost = len(self.vms)
        else:
            self.elementCost = 10000000
        self.priceList.append(self.elementCost)



    def initRandom(self):
        """
        Pure random initialization of an element
        :return:
        """
        for compId in range(self.problem.nrComp):
            for vmId in range(self.problem.nrVM):
                if random.random() > 0.75:
                    self.addCompToVM(compId, vmId)

    def initBasedOnMinimumComponentsNumber(self):
        """
        We know the minimum component number that is required so try to initialize a solution based on this information
        :return:
        """
        orComponentsDecidedNotToBeDeployed = set()
        #salvate ca sa functioneze pt mai multe elemente
        _compInstances = {}
        for comp_id, comp in self.problem.componentsList.items():
            _compInstances[comp_id] = comp.minimumNumberOfInstances

        for comp_id, comp in self.problem.componentsList.items():
            comp_instances_number = _compInstances[comp_id]

            if len(comp.orComponentsList) > 0: # or case (c1 or c2 should be deployed) - in order to let also other or component to be deployed
                s = 0
                comp_instances_number = 0
                for compId in comp.orComponentsList:
                    s += numpy.sum(self.a[compId])
                if s == 0 and numpy.sum(self.a[comp_id]) == 0:
                    #print("....componentId or init", comp_id, "initial number of instance", comp.minimumNumberOfInstances,
                    #      "fond nr", comp_instances_number, comp.orComponentsList)

                    __aux__orList = comp.orComponentsList.copy()
                    for _compId in __aux__orList:
                        if _compId in orComponentsDecidedNotToBeDeployed:
                            __aux__orList.remove(_compId)
                    #print("....orComponentsDecidedNotToBeDeployed", orComponentsDecidedNotToBeDeployed, __aux__orList)
                    if len(__aux__orList) > 0:
                        if random.random() < 0.5:
                            #comp_id = comp_id
                            comp_instances_number = max(1, _compInstances[comp_id])
                            for compId in comp.orComponentsList:
                                _compInstances[compId] = 0
                                orComponentsDecidedNotToBeDeployed.add(compId)
                        else:
                            orComponentsDecidedNotToBeDeployed.add(comp_id)
                            comp_id = comp.orComponentsList[int(random.random()*len(comp.orComponentsList))] #TODO: review here
                            #print("chosee fom or list", comp_id, "instances nr", self.problem.componentsList[comp_id].minimumNumberOfInstances)

                            _compInstances[comp_id] = max(1, self.problem.componentsList[comp_id].minimumNumberOfInstances)
                            continue
                    else:
                        comp_instances_number = comp.minimumNumberOfInstances
                #if comp_instances_number > 0:
                #    comp_instances_number = comp_instances_number - numpy.sum(self.a[comp_id])

            #print("componentId", comp_id, "initial number of instance", comp.minimumNumberOfInstances,"fond nr",comp_instances_number)
            for i in range(comp_instances_number):
                vm_id = int(random.random() * self.problem.nrVM)
                #TODO: build the VMs list which are free and choose from it
                while self.a[comp_id][vm_id] == 1:
                     vm_id = int(random.random() * self.problem.nrVM)
                self.addCompToVM(comp_id, vm_id)

        #print('before full', self)
        for comp_id, comp in self.problem.componentsList.items():
            if comp.fullDeployedComponent:
                for vm_id, vm_compList in self.solVms.items():
                    if comp_id not in vm_compList:
                        no_conflict_components_on_vm = True
                        for comp_id_conflict in comp.conflictComponentsList:
                            if comp_id_conflict in vm_compList:
                                no_conflict_components_on_vm = False
                                break
                        if no_conflict_components_on_vm:
                            self.addCompToVM(comp_id, vm_id)

        # nu ar trebui aici probabil
        for comp_id, comp in self.problem.componentsList.items():
            if comp.fullDeployedComponent:
                if len(self.solComponents[comp_id]) > 1:
                    for vm_id in self.solComponents[comp_id]:
                        if len(self.solVms[vm_id]) == 1:
                            self.removeCompFromVM(comp_id, vm_id)
        self.problem.logger.debug("New element")
        self.problem.logger.debug(self.a)

    def addCompToVM(self, compId, vmId):
        """
        EA  - add the virtual machine ID on the list where the component is deployed
        :param vmId: the ID of the virtual machine
        :return: the updated virtual machines list on which the component is deployed
        """
        #print("add start: ", self.solVms, self.solComponents)
        if self.a[compId][vmId] == 0:
            if not vmId in self.solVms:
                self.solVms[vmId] = []
            self.solVms[vmId].append(compId)
            self.solComponents[compId].append(vmId)

            self.a[compId][vmId] = 1
            self.vms.add(vmId)

        self.vmsPriceModified[vmId] = True
        #print("add end : ", self.solVms, self.solComponents)

    def removeCompFromVM(self, compId, vmId):
        """
        Remove the component from a virtual machine
        :param vmId: the ID of the virtual machine from which the component is removed
        :return: the updated virtual machines list on which the component is deployed
        """
        #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!------------remove:", vmId, compId, self.solComponents, self.solVms, self.vms)
        if vmId in self.solComponents[compId]:
            self.solComponents[compId].remove(vmId)

        #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!------------remove:", vmId, self.solVms)
        if compId in self.solVms[vmId]:
            self.solVms[vmId].remove(compId)

        self.a[compId][vmId] = 0
        if (vmId in self.vms) and len(self.solVms[vmId]) == 0:
            #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!------------remove:", vmId, self.solVms)
            self.vms.remove(vmId)
            del self.solVms[vmId]
            self.vmsPriceModified.pop(vmId, None)
        else:
            self.vmsPriceModified[vmId] = True
        #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!------------remove:", vmId, self.solVms)



    def __repairOrConstrain(self):
        """
        If both deployed eliminate one
        :param element: contains current vm, components allocation
        :return:
        """
        for compId in self.solComponents:
            if len(self.problem.componentsList[compId].orComponentsList) > 0:
                alphaCompId = compId
                betaCompId = self.problem.componentsList[compId].orComponentsList[0]  #!!nu am considerat cu mai multe in or
                #print("or: ", alphaCompId, betaCompId)
                if (numpy.sum(self.a[alphaCompId]) > 0) and (numpy.sum(self.a[betaCompId]) > 0):
                    # 1. remove the one with more conflicts
                    if self.problem.componentsList[alphaCompId].numberOfConflictComponents == \
                            self.problem.componentsList[alphaCompId].numberOfConflictComponents:
                        alphaResources, betaResources = self.problem.compareComponentsRegardingHardwareRestrictions(
                            alphaCompId, betaCompId)
                        # 2. remove the most expensive component regarding hardware requirement
                        if alphaResources == betaResources:
                            # 3. remove random
                            removed_comp_id = alphaCompId if random.random() < 0.5 else betaCompId
                        elif alphaResources < betaResources:
                            removed_comp_id = alphaResources
                        else:
                            removed_comp_id = betaResources
                    elif self.problem.componentsList[alphaCompId].numberOfConflictComponents > \
                            self.problem.componentsList[
                                alphaCompId].numberOfConflictComponents:
                        removed_comp_id = alphaCompId
                    else:
                        removed_comp_id = betaCompId

                    for vmId in self.solComponents[removed_comp_id]:
                        self.removeCompFromVM(removed_comp_id, vmId)


    def __repairConflictComponentsOnSameMachine(self):

        for compId in self.solComponents:
            if len(self.problem.componentsList[compId].conflictComponentsList) > 0:
                # repair conflicts
                __conflictComponentsList = self.problem.componentsList[compId].conflictComponentsList
                __alphaCompId = compId
                for alpha_deployed_vm in self.solComponents[compId]:
                    for compId_in_deployed_vm in self.solVms[alpha_deployed_vm]:
                        if compId_in_deployed_vm in __conflictComponentsList:
                            #exists a conflict try to solve it
                            __betaCompId = compId_in_deployed_vm
                            __vmId = alpha_deployed_vm

                            nrOfAlphaInstances = len(self.solComponents[__alphaCompId])
                            minimumNrOfAlpahaComponnetId = self.problem.componentsList[__alphaCompId].minimumNumberOfInstances

                            nrOfBetaInstances = len(self.solComponents[__betaCompId])
                            minimumNrOfBetaComponnetId = self.problem.componentsList[__betaCompId].minimumNumberOfInstances

                            if (nrOfAlphaInstances > minimumNrOfAlpahaComponnetId) and (
                                        nrOfBetaInstances > minimumNrOfBetaComponnetId):
                                # remove one with the most components
                                if (nrOfAlphaInstances - minimumNrOfAlpahaComponnetId) == (
                                            nrOfBetaInstances - minimumNrOfBetaComponnetId):
                                    if random.random() > 0.5:
                                        self.removeCompFromVM(__alphaCompId, __vmId)
                                    else:
                                        self.removeCompFromVM(__betaCompId, __vmId)
                                elif (nrOfAlphaInstances - minimumNrOfAlpahaComponnetId) > (
                                            nrOfBetaInstances - minimumNrOfBetaComponnetId):
                                    self.removeCompFromVM(__alphaCompId, __vmId)
                                else:
                                    self.removeCompFromVM(__betaCompId, __vmId)

                            elif nrOfAlphaInstances > minimumNrOfAlpahaComponnetId:
                                self.removeCompFromVM(__alphaCompId, __vmId)
                            elif nrOfBetaInstances > minimumNrOfBetaComponnetId:
                                self.removeCompFromVM(__betaCompId, __vmId)
                            else:
                                # try to move - acum greedy la prima care reuseste -
                                # mai trebuie sa modifici ca pe harie (nu am verificat restrictii hardware)
                                comp_moved = False
                                for k_vm, k_compsList in self.solVms.items():
                                    if __alphaCompId not in k_compsList:
                                        canMove = True
                                        for comp_h in __conflictComponentsList:
                                            if comp_h in k_compsList:
                                                canMove = False
                                                break
                                        if canMove:
                                            self.removeCompFromVM(__alphaCompId, __vmId)
                                            self.addCompToVM(__alphaCompId, k_vm)
                                            comp_moved = True
                                            break
                                if not comp_moved:
                                    # add a new vm
                                    allVm = set()
                                    for i in range(self.problem.nrVM):
                                        allVm.add(i)
                                    freeVms = allVm.difference(self.vms)
                                    if len(freeVms) > 0:
                                        new_vm = freeVms.pop()
                                        self.addCompToVM(__alphaCompId, new_vm)

    def __repairFullDeployment(self):
        fullDeploymentRestrictions = []
        for restriction in self.problem.restrictionsList:
            if isinstance(restriction, RestrictionFullDeployment):
                if restriction.eval(self.a) > 0:

                    vmsAquired = numpy.sum(self.a, axis=0)
                    for j in range(len(vmsAquired)):
                        if vmsAquired[j] != 0:
                            conflict = False
                            for conflictId in restriction.compsIdList:
                                if self.a[conflictId][j] == 1:
                                    conflict = True  # a component that is in conflict with full deploy component
                            if conflict and self.a[restriction.compId][j] == 1:
                                self.removeCompFromVM(restriction.compId, j)
                            elif conflict == False and self.a[restriction.compId][j] == 0:
                                self.addCompToVM(restriction.compId, j)

    def repair(self):
        self.__repairOrConstrain()
        self.__repairConflictComponentsOnSameMachine()
        self.__repairFullDeployment()

    def isComponentOnMachine(self, compId, vmId):
        """
        Tests if a component is on a vm
        :param compId: the component ID
        :param vmId: the Vm ID
        :return: True if component is placed on VM
        """
        return self.a[compId][vmId] == 1

    def __repr__(self):
        string = "Element: nrOfViolatedConstraints {} nrOfVm {} nrOfComponents {} \n".format(self.violatedConstraintsNr, self.vmsNr, self.componentsNr)
        for line in self.a:
            string += str(line)+"\n"
        return string


    def buildSolutinInformations(self):
        result = {}
        #neededVM = 0
        vms = list(self.vms)

        #print("vms", vms)
        for k in range(len(vms)):

            memory = 0

            cpus = 0
            gpus = 0
            cpusType = set()

            storageHDD = 0
            storageSSD = 0
            storageType = set()

            netConnections = 0
            netDataIn = 0
            netDataOut = 0

            keywords = set()
            operatingSystem = set()

            for i in range(self.problem.nrComp):
                __component = self.problem.componentsList[i]
                if self.a[i][vms[k]] == 1:
                    # memory
                    memory += __component.HM if __component.HM is not None else 0
                    # cpu
                    __cpuType = __component.HCType
                    if __cpuType is None or __cpuType == "false":
                        cpusType.add("CPU")
                        __cpuType = "CPU"
                    else:
                        cpusType.add("GPU")
                        __cpuType = "GPU"
                    if __cpuType == "CPU":
                        cpus += __component.HC if __component.HC is not None else 0
                    else:
                        gpus += __component.HC if __component.HC is not None else 0
                    #storage
                    __storageType = __component.HSType
                    if __storageType == "SSD":
                        storageType.add("SSD")
                        __storageType = "SSD"
                    else:
                        storageType.add("HDD")
                        __storageType = "HDD"
                    if __storageType == "HDD":
                        storageHDD += __component.HS if __component.HS is not None else 0
                    else:
                        storageSSD += __component.HS if __component.HS is not None else 0
                    #network
                    netConnections += __component.NConnections if __component.NConnections is not None else 0
                    netDataIn += __component.NIn if __component.NIn is not None else 0
                    netDataOut += __component.NOut if __component.NOut is not None else 0
                    #keywords
                    for key in __component.keywords:
                        keywords.add(key)
                    #OS
                    operatingSystem.add(__component.operatingSystem)
            result[vms[k]] = {"memory": memory,
                                    "cpu": {"type": list(cpusType), "cpu": cpus, "gpu": gpus},
                                    "storage": {"type": list(storageType),"hdd": storageHDD, "ssd": storageSSD},
                                    "network": {"connections": netConnections, "dataIn": netDataIn, "dataOut": netDataOut},
                                    "keywords": list(keywords),
                                    "operatingSystem": list(operatingSystem)}

            #neededVM += 1
            result["IP"] = self.problem.IpInfo
        #print("result:", result, "\n")
        return result