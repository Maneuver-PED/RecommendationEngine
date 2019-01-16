import numpy
import random

class RestrictionOneToOneDependency:#DependencesCorelation:

    def __init__(self, component, dependentComponent, problem):
        self.compId = component - 1
        self.relatedCompId = dependentComponent - 1
        problem.D[self.compId][self.relatedCompId] = 1
        problem.D[self.relatedCompId][self.compId] = 1
        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionOneToOneDependency(self.compId, self.relatedCompId)

    def __repr__(self):
        return "OneToOneDependency restriction: if component with id {} is on a VM component with id {} is also"\
            .format(self.compId, self.relatedCompId)

    def eval(self, solutionMatrix):
        vms = len(solutionMatrix[0])
        viotatedRestrictions = 0
        for j in range(vms):
            if solutionMatrix[self.compId][j] != solutionMatrix[self.relatedCompId][j]:
                    viotatedRestrictions += 1
        return viotatedRestrictions


class RestrictionManyToManyDependency:#DependencesOnTotalNumber:

    def __init__(self, alphaComp, betaComp, sign, problem):
        self.alphaCompId = alphaComp - 1
        self.betaCompId = betaComp - 1
        self.sign = sign
        self.problem = problem
        self.problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionManyToManyDependency(self.alphaCompId, self.betaCompId, self.sign)

    def __repr__(self):
        return "RestrictionManyToManyDependency: component id {} number of instances on all VM is {} then component id {} number"\
            .format(self.alphaCompId, self.sign, self.betaCompId)

    def eval(self, solutionMatrix):
        sumCompIdNr = numpy.sum(solutionMatrix[self.alphaCompId])
        sumRelatedComponentId = numpy.sum(solutionMatrix[self.betaCompId])

        viotatedRestrictions = 0
        if self.sign == "==":
            if sumCompIdNr != sumRelatedComponentId:
                viotatedRestrictions = 1
        elif self.sign == ">=":
            if sumCompIdNr < sumRelatedComponentId:
                viotatedRestrictions = 1
        elif self.sign == "<=":
            if sumCompIdNr > sumRelatedComponentId:
                viotatedRestrictions = 1
        return viotatedRestrictions

class RestrictionManyToManyDependencyNew:#DependencesOnTotalNumber:

    def __init__(self, alphaComp, betaComp, n,m, problem):
        self.alphaCompId = alphaComp - 1
        self.betaCompId = betaComp - 1
        self.n = n
        self.m=m
        self.problem = problem
        self.problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionManyToManyDependencyNew(self.alphaCompId, self.betaCompId, self.n, self.m)

    def __repr__(self):
        return "RestrictionManyToManyDependencyNew: component id {} number of instances on all VM is {} then component id {} {} number"\
            .format(self.alphaCompId, self.n,self.m, self.betaCompId)

    def eval(self, solutionMatrix):

        return 0

class RestrictionOneToManyDependency:

    def __init__(self, component, dependentComponent, instancesNumber, problem):
        self.compAlphaId = component - 1  # provider
        self.compBetaId = dependentComponent - 1  # consumer
        self.n = instancesNumber
        self.problem = problem
        self.problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionOneToManyDependency(self.compAlphaId, self.compBetaId, self.n)

    def __repr__(self):
        return "RestrictionOneToManyDependency: for one component with id {} should be deployed {} components with id {}"\
            .format(self.compAlphaId, self.n, self.compBetaId)

    def eval(self, solutionMatrix):
        sumAlpha = numpy.sum(solutionMatrix[self.compAlphaId])
        sumBeta = numpy.sum(solutionMatrix[self.compBetaId])

        viotatedRestrictions = 0
        s = self.n * sumAlpha - sumBeta
        if s < 0 or s >= self.n:
             viotatedRestrictions = 1
        self.problem.logger.debug("RestrictionOneToManyDependency violated: {} {} {}".format(viotatedRestrictions, s, self.n))
        return viotatedRestrictions