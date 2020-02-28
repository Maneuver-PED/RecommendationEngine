class Component:
    def __init__(self, id, name, cpus, gpu,  memory,  storageSize, storageType, storageValue, netIn, netOut, netConnections,
                 keywords, operatingSystem):
        self.id = id
        self.name = name
        # hardware description
        self.HC = cpus
        self.HCType = gpu
        self.HM = memory
        self.HS = storageSize
        self.HSType = storageType
        self.HSValue =storageValue
        # network description
        self.NIn = netIn
        self.NOut = netOut
        self.NConnections = netConnections
        # other information
        self.keywords = keywords
        self.operatingSystem = operatingSystem

        # minimum number of instances
        self.minimumNumberOfInstances = 0
        self.numberOfConflictComponents = 0
        self.orComponentsList = []
        self.dependenceComponentsList = set()
        self.conflictComponentsList = set()
        self.fullDeployedComponent = False
        self.numberOfInstancesDependences = set()



    def getMinimumPossibleNumberOfInstances(self, comps_set):
        """
        Get minimum nr of instances for fix components
        If the number of instances of a set of components depends on a value, then the minimum number of instances of
        the component in the set is the minimum of the number of instances of all components
        :return:
        """
        if len(self.numberOfInstancesDependences) == 0:
            return self.minimumNumberOfInstances
        else:
            minimum = self.minimumNumberOfInstances
            for comp_id in self.numberOfInstancesDependences:
                if minimum > comps_set[comp_id].minimumNumberOfInstances:
                    minimum = comps_set[comp_id].minimumNumberOfInstances
        return minimum

    def __repr__(self):
        return "ID: {} Name: {} Hardware [CPUs: {} GPU: {} Memory: {} StorageSize: {} StorageType: {} StorageValue: {}]"\
                " Network[ In: {} Out: {} Connections: {} ] Keywords: {} OperatingSystem: {}"\
            .format(self.id, self.name, self.HC, self.HCType, self.HM, self.HS, self.HSType, self.HSValue, self.NIn,
                    self.NOut, self.NConnections, self.keywords, self.operatingSystem)

    def getComponentHardWareResources(self):
        """
        Used for CP Solver in order to add restrictions regarding hardware requirements
        :return: a list with component hardware restrictions
        """
        return [self.HC, self.HM, self.HS]

    def getResorces(self):
        """
        Function used by EA in order to obtain a aggregation of component hardware resources
        :return:
        """
        return self.HC * self.HM * self.HS