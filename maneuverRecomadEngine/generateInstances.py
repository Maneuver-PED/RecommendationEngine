'''
In order to investigate the comparative performance of exact
and heuristic methods and to identify up to which problem size
(related to N and M) the exact methods are feasible in practice
we designed a simple test instances generator which provides
test cases characterized by different levels of complexity with
respect to the constraints to be satisfied. For a given problem
size (N components and M VMs) a test case is created by
generating a binary matrix R which encodes the conflicts
between the components and by generating the number of
instances of each component which should be deployed. Each
test case is characterized by a probability, pR, controlling the
amount of conflictual components and by a probability, pI ,
controlling the number of components for which constraints
concerning the number of instances is imposed.
'''
import csv
import fnmatch
import os

import numpy as np

from exactsolvers.CP_Pulp import CP_Solver_Pulp
from exactsolvers.CP_Solver_GOT import CP_Solver_GOT
from exactsolvers.CP_Solver_GOT_LP import CP_Solver_GOT_LP


class TestInstances:

    def generateInstances(self, pR, pI, N, M, directoryPath):
        """
        Genereate a file that contains a conflic matrix and the number of instances for each componenent
        :param pR: conflic probability
        :param pI: instance number probability
        :param N: number of components
        :param M:  number of machines
        :param directoryPath: the directory name where the instances will be saved
        :return:
        """
        if not os.path.exists(directoryPath):
            os.makedirs(directoryPath)

        fileName = directoryPath + "/test _N_" + str(N) + "_M_" + str(M) +"_pR_" + str(pR) + "_pI_" + str(pI) + ".csv"
        #build conflicts matrix
        R = np.zeros((N, N), dtype=np.int)
        nrOfCompfictsForComponent = np.zeros(N, dtype=np.int)
        for i in range(N):
            for j in range(i):
                if (np.random.rand()<pR):
                    R[i][j] = R[j][i] = 1
                    nrOfCompfictsForComponent[i] += 1
                    nrOfCompfictsForComponent[j] += 1
        print("Conflict matrix = ", R)

        #build components number

        #nu mai stiu de ce am facut asta
        maxNrOfConflicts = max(nrOfCompfictsForComponent)
        upperBound = (M - maxNrOfConflicts)/2
        #print("maxNrOfConflicts=", maxNrOfConflicts, "upperBound=",upperBound)

        #!!!!!!!!!!!!!!!!!!!!!
        print(upperBound) #uneori pot aparea probleme aici verifica

        #constangerile erau cu egal
        nrInstances=np.zeros((N),  dtype=np.int)
        for i in range(N):
            if np.random.rand() < pI:
                nrInstances[i] = 2 + np.random.randint(0, upperBound, size=1)
        #print("Number of instances of compoents =", nrInstances)

        #  write into file the conflict matrix and components number
        with open(fileName, 'w', newline='') as csvfile:
            spamwriter = csv.writer(csvfile, delimiter=' ')
            # linia 1 nr de componente, nr de masini, probabilitatea de conflict, probabilitatea de prepetare
            spamwriter.writerow([N, M, pR, pI])
            # Matricea de conflicte
            for i in range(N):
                spamwriter.writerow(R[i])
            # Nr de componente
            spamwriter.writerow(nrInstances)

    def readTestFile(self, filePath):
        """
        Reads from the file the conflict matrix and the number of components
        :param filePath: the path of the file
        :return: numberOfComponents, numberOfMAchines, conflictMatrix, numberOfComponents
        """
        print("open file: ", filePath)
        filecontent=[]
        with open(filePath, newline='') as csvfile:
            spamreader = csv.reader(csvfile, delimiter=' ')
            for row in spamreader:
                filecontent.append(row)
        N = int(filecontent[0][0])
        M = int(filecontent[0][1])
        R = []
        for i in range(1, N+1):
            R.append(list(map(int, filecontent[i])))
        nrComp = list(map(int,filecontent[-1]))
        return N, M, R, nrComp


    def executeCP(self, inputFilePath, cpSolver):
        """
        Execute CP problem for specified input data
        :param inputFilePath: input data file
        :param outputFilePath: time and result file
        :param cpSolver: The solver used to solve the CP problem
        :return:
        """
        N, M, R, componentsNumber = self.readTestFile(inputFilePath)
        cpSolver.init(N, M)
        for i in range(N):
            for j in range(i+1, N):
                if R[i][j] == 1:
                    cpSolver.componentConflictConstrain(i+1, [j+1])

        for i in range(N):
            if componentsNumber[i] > 1:
                cpSolver.componentNumberConstrain([i+1], componentsNumber[i], None, "=")

        vals = []
        times = []
        for i in range(15):
            time, nrOfVm, __vm, __a = cpSolver.run()
            vals.append(nrOfVm)
            times.append(time)
        #time = timeit.Timer(lambda: rez.append(cpSolver.run), 'from __main__ import TestInstances'). repeat(repeat=15, number=1)#10,10
        print(inputFilePath, " Time in seconds", times)
        return min(times), max(times), np.average(times), min(vals), max(vals), np.average(vals)

    def generateInstancesROLCGPaper(self):
        path = "../testInstances/testRolcg1"
        self.generateInstances(0.4, 0, 12, 12, path)
        self.generateInstances(0.5, 0, 12, 12, path)
        self.generateInstances(0.6, 0, 12, 12, path)
        self.generateInstances(0.4, 0, 13, 13, path)
        self.generateInstances(0.5, 0, 13, 13, path)
        self.generateInstances(0.6, 0, 13, 13, path)
        self.generateInstances(0.4, 0, 14, 14, path)
        self.generateInstances(0.5, 0, 14, 14, path)
        self.generateInstances(0.6, 0, 14, 14, path)
        self.generateInstances(0.4, 0, 15, 15, path)
        self.generateInstances(0.5, 0, 12, 15, path)
        self.generateInstances(0.6, 0, 15, 15, path)
        self.generateInstances(0.4, 0.1, 15, 15, path)
        self.generateInstances(0.4, 0.5, 15, 15, path)
        self.generateInstances(0.4, 0.9, 15, 15, path)
        self.generateInstances(0.6, 1.0, 15, 15, path)

    def generateInstances16_19(self):
        path = "../../testInstances/test16_19"
        self.generateInstances(0.4, 0, 16, 16, path)
        self.generateInstances(0.5, 0, 16, 16, path)
        self.generateInstances(0.6, 0, 16, 16, path)
        self.generateInstances(0.4, 0, 17, 17, path)
        self.generateInstances(0.5, 0, 17, 17, path)
        self.generateInstances(0.6, 0, 17, 17, path)
        self.generateInstances(0.4, 0, 18, 18, path)
        self.generateInstances(0.5, 0, 18, 18, path)
        self.generateInstances(0.6, 0, 18, 18, path)
        self.generateInstances(0.4, 0, 19, 19, path)
        self.generateInstances(0.5, 0, 19, 19, path)
        self.generateInstances(0.6, 0, 19, 19, path)
        self.generateInstances(0.4, 0.1, 19, 19, path)
        self.generateInstances(0.4, 0.5, 19, 19, path)
        self.generateInstances(0.4, 0.9, 19, 19, path)
        self.generateInstances(0.6, 1, 19, 19, path)

    def writeRunInstancesInFile(self, outPath, testFileDirectoryPath, cpSolver):
        fileList = fnmatch.filter(os.listdir(testFileDirectoryPath), "*.csv")
        print(fileList)
        for file in fileList:
            with open(outPath, 'a', newline='') as csvfile:
                spamwriter = csv.writer(csvfile, delimiter=',')
                minTime, maxTime, avgTime, minVms, maxVms, avgVms = self.executeCP(testFileDirectoryPath + file, cpSolver)
                spamwriter.writerow([file, minTime, maxTime, avgTime, minVms, maxVms, avgVms])
            csvfile.close()


if __name__ == "__main__":
    testDirectory = "../testInstances/testRolcg1/"
    testObj = TestInstances()
    testObj.generateInstancesROLCGPaper()
    #testObj.generateInstances16_19()


    #testDirectory = "./test16_19/"
    outDir=testDirectory+"results/"

    cpSolver = CP_Solver_Pulp()
    testObj.writeRunInstancesInFile(outDir + "pulp.csv", testDirectory, cpSolver)

    pSolver = CP_Solver_GOT_LP("CBC")
    testObj.writeRunInstancesInFile(outDir + "google_lp_cbc.csv", testDirectory, cpSolver)

    pSolver = CP_Solver_GOT_LP("BOP")
    testObj.writeRunInstancesInFile(outDir + "google_lp_bop.csv", testDirectory, cpSolver)

    pSolver = CP_Solver_GOT_LP("CLP")
    testObj.writeRunInstancesInFile(outDir + "google_lp_clp.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("FIRST_UNBOUND_MIN")
    testObj.writeRunInstancesInFile(outDir+"google_first_unbound_min.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("FIRST_UNBOUND_MAX")
    testObj.writeRunInstancesInFile(outDir+"google_first_unbound_max.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("FIRST_UNBOUND_RANDOM")
    testObj.writeRunInstancesInFile(outDir+"google_first_unbound_random.csv", testDirectory, cpSolver)
    
    cpSolver = CP_Solver_GOT("RANDOM_MIN")
    testObj.writeRunInstancesInFile(outDir+"google_random_min.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("RANDOM_MAX")
    testObj.writeRunInstancesInFile(outDir+"google_random_max.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("RANDOM_RANDOM")
    testObj.writeRunInstancesInFile(outDir+"google_random_random.csv", testDirectory, cpSolver)
    
    cpSolver = CP_Solver_GOT("LOWEST_MIN_MIN")
    testObj.writeRunInstancesInFile(outDir + "google_lowest_min_min.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("LOWEST_MIN_MAX")
    testObj.writeRunInstancesInFile(outDir + "google_lowest_min_max.csv", testDirectory, cpSolver)

    cpSolver = CP_Solver_GOT("LOWEST_MIN_RANDOM")
    testObj.writeRunInstancesInFile(outDir + "google_lowest_min_random.csv", testDirectory, cpSolver)

