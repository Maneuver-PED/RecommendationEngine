class RestrictionHardware:
    def __init__(self, componentsValues, availableConfigurations, problem):
        self.availableConfigurations = availableConfigurations
        self.componentsValues = componentsValues
        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.constraintsHardware(self.componentsValues)

    def __repr__(self):
        return "RestrictionHardware: components values: {}".format(str(self.componentsValues))

    def eval(self, solutionMatrix):
        _vioatedConstraints = 0
        return _vioatedConstraints

