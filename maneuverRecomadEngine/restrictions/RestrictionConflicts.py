import random
import numpy

class RestrictionAlphaOrBeta:
    def __init__(self, alphaCompId, betaCompId, problem):
        self.alphaCompId = alphaCompId - 1
        self.betaCompId = betaCompId - 1

        problem.componentsList[self.alphaCompId].orComponentsList.append(self.betaCompId)
        problem.componentsList[self.betaCompId].orComponentsList.append(self.alphaCompId)
        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionAlphaOrBeta(self.alphaCompId, self.betaCompId)

    def __repr__(self):
        return "RestrictionAlphaOrBeta: Component with id {} or component with id {} id deployed".format(
            self.alphaCompId, self.betaCompId)

    def eval(self, solutionMatrix):
        """
        Counts how many components conflicts are not respected into current solution
        :param solutionMatrix:
        :return:
        """
        if (numpy.sum(solutionMatrix[self.alphaCompId]) > 0) + (numpy.sum(solutionMatrix[self.betaCompId]) > 0) == 1:
            return 0
        return 1


class RestrictionConflict:
    def __init__(self, compId, compsIsList, problem):
        self.compId = compId - 1
        self.conflictCompsIdList = []
        for comp_id in compsIsList:
            self.conflictCompsIdList.append(comp_id - 1)
        for conflict_comp_id in self.conflictCompsIdList:
            problem.R[self.compId][conflict_comp_id] = 1
            problem.R[conflict_comp_id][self.compId] = 1

        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionConflict(self.compId, self.conflictCompsIdList)

    def __repr__(self):
        return "RestrictionConflict: component with id {} in conflict with components with id {}"\
            .format(self.compId, self.conflictCompsIdList)

    def eval(self, solutionMatrix):
        """
        Counts how many components conflicts are not respected into current solution
        :param solutionMatrix:
        :return:
        """
        vms = len(solutionMatrix[0])
        viotatedRestrictions = 0
        for conflictCompId in self.conflictCompsIdList:
            for j in range(vms):
                if solutionMatrix[self.compId][j] == 1 and solutionMatrix[conflictCompId][j] == 1:
                    viotatedRestrictions += 1
        return viotatedRestrictions