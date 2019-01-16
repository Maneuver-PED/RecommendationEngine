import numpy
import random

class RestrictionFullDeployment:
    def __init__(self, component, componentList, problem):
        self.compId = component - 1
        self.compsIdList = []
        for compId in componentList:
            self.compsIdList.append(compId-1)
            problem.R[self.compId][compId-1] = 1
            problem.R[compId-1][self.compId] = 1
        self.problem = problem
        problem.componentsList[self.compId].fullDeployedComponent = True
        problem.logger.info(self)

    def generateRestrictions(self, solver):
            solver.RestrictionFullDeployment(self.compId, self.compsIdList)

    def __repr__(self):
            return "RestrictionFullDeployment: component with id {} should be deployed on all VM that does not contain " \
                    "components which it is in conflict, conflicted components list {}".format(self.compId, self.compsIdList)

    def eval(self, solutionMatrix):
        _viotatedRestrictions = 0
        vmsAquired = numpy.sum(solutionMatrix, axis=0) # nr componente pe fiecare masina
        for j in range(len(vmsAquired)):
            if vmsAquired[j] != 0:
                conflict = False
                for conflictId in self.compsIdList:
                    if solutionMatrix[conflictId][j] == 1:
                        conflict = True  # a component that is in conflict with full deploy component
                        break
                if conflict and solutionMatrix[self.compId][j] == 1:
                    _viotatedRestrictions += 1
                elif conflict == False and solutionMatrix[self.compId][j] == 0:
                    _viotatedRestrictions += 1

        #print("Full deployment check: ", self)
        if _viotatedRestrictions > 0:
            self.problem.logger.debug("violated full deployment: {}".format( _viotatedRestrictions))
        return _viotatedRestrictions


class RestrictionUpperLowerEqualBound:
    def __init__(self, componentList, sign, n, problem):
        self.compsIdList = []
        for comp_id in componentList:
            self.compsIdList.append(comp_id - 1)
        self.sign = sign
        self.n = n
        self.problem = problem
        self.problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionUpperLowerEqualBound(self.compsIdList, self.n, self.sign)

    def __repr__(self):
            return "RestrictionUpperLowerEqualBound: components with ids {} {} {}"\
                .format(self.compsIdList, self.sign, self.n)

    def eval(self, solutionMatrix):
        sum = 0
        for compId in self.compsIdList:
            sum += numpy.sum(solutionMatrix[compId])

        viotatedRestrictions = 0
        if self.sign == "==":
            if sum != self.n:
                viotatedRestrictions = 1
        elif self.sign == ">=":
            if sum < self.n:
                viotatedRestrictions = 1
        elif self.sign == "<=":
            if sum > self.n:
                viotatedRestrictions = 1

        if viotatedRestrictions == 1:
            # daca componenta in or constraints
            for compId in self.compsIdList:
                if len(self.problem.componentsList[compId].orComponentsList) and sum == 0: # NU E CORECT TOTAL MAI GANDESTETE LA CAZUL GENERAL
                    if sum == 0:
                        s = 0
                        for compId in self.problem.componentsList[compId].orComponentsList:
                            s += numpy.sum(solutionMatrix[compId])
                        if s > 0:
                             viotatedRestrictions = 0
        if viotatedRestrictions == 1:
            self.problem.logger.debug("RestrictionUpperLowerEqualBound violated:(sum_comp {} = {}) {} {}"\
                        .format(self.compsIdList, sum, self.sign, self.n))

        return viotatedRestrictions


class RestrictionRangeBound:
    def __init__(self, componentList, n1, n2, problem):
        self.compsIdtList = []
        for comp_id in componentList:
            self.compsIdtList.append(comp_id - 1)
        self.n1 = n1
        self.n2 = n2
        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionRangeBound(self.compsIdList, self.n1, self.n2)

    def __repr__(self):
        return "RestrictionRangeBound: {} <= components with id list {} <= {}"\
            .format(self.n1, self.compsIdtList, self.n2)

    def eval(self, solutionMatrix):
        _sum = 0
        for compId in self.compsIdsList:
            _sum += numpy.sum(solutionMatrix[compId])

        _viotatedRestrictions = 0
        if _sum < self.n1 or _sum > self.n2:
            _viotatedRestrictions = 1
            self.problem.logger.debug("RestrictionRangeBound violated: {} <= (sum_comp {} = {})<= {}"\
            .format(self.n1, self.compsIdtList,  _sum, self.n2))
        return _viotatedRestrictions

class RestrictionRequireProvideDependency:
    def __init__(self, alphaComp, betaComp, nAlphaBeta, nBetaAlpha, problem):
        self.alphaCompId = alphaComp - 1 # consumer
        self.betaCompId = betaComp - 1 # provider
        self.nAlphaBeta = nAlphaBeta #n
        self.nBetaAlpha = nBetaAlpha #m
        self.problem = problem
        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionRequireProvideDependency(self.alphaCompId, self.betaCompId, self.nAlphaBeta, self.nBetaAlpha)

    def __repr__(self):
        return "RestrictionRequireProvideDependency: each component with id {} consumes at least {} components with id {}, " \
               "each component with id {} serves at least {} components with id {}".format(self.alphaCompId, self.nAlphaBeta,
                                                self.betaCompId, self.betaCompId, self.nBetaAlpha, self.alphaCompId)

    def eval(self, solutionMatrix):
        _viotatedRestrictions = 0

        if self.nAlphaBeta * numpy.sum(solutionMatrix[self.alphaCompId]) > \
                        self.nBetaAlpha * numpy.sum(solutionMatrix[self.betaCompId]):
            _viotatedRestrictions = 1
            self.problem.logger.debug("RestrictionRequireProvideDependency violated {} {} * {} <= {} * {}".format(
                                      _viotatedRestrictions, self.nAlphaBeta,
              numpy.sum(solutionMatrix[self.alphaCompId]),
                        self.nBetaAlpha, numpy.sum(solutionMatrix[self.betaCompId])))
        return _viotatedRestrictions
