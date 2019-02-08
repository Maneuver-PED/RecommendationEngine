#from maneuverRecomadEngine.exactsolvers.CP_Pulp import CP_Solver_Pulp
from maneuverRecomadEngine.problem.ProblemDefinition import ManeuverProblem


import os
import csv
import time
import logging
import logging.config
import json
import numpy


def run_test_cp(resultsDirectoryPath):
    offers = [10, 20, 40, 60, 80, 100]
    testFiles = ["oryx2v2-2",
                 "WebIntrusionDetection3", "Wordpress3", "Wordpress4",
                 "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8", "Wordpress9",
                 "Wordpress10", "Wordpress11", "Wordpress12"]
    cp_selection_strategies = [ "FIRST_UNBOUND_MAX", "FIRST_UNBOUND_RANDOM",
                      "RANDOM_MIN", "RANDOM_MAX", "RANDOM_RANDOM"] #"FIRST_UNBOUND_MIN",

    pattern_fileConfigurations = "../testInstances/ptArticolICCP/testOffers/offers_{}.json"
    pattern_problem_file_name = "../testInstances/ptArticolICCP/testProblems/{}.json"

    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    resultFileName = resultsDirectoryPath + "cp_run_offf.csv"

    with open(resultFileName, 'a', newline='') as csvfile:
        spamwriter = csv.writer(csvfile, delimiter=';')
        spamwriter.writerow(["Problem", "Offer", "CP_Strategy", "Time", "TotalPrice", "NrVm","Price", "Solution"])

    for strategy in cp_selection_strategies:
        for testProblem in testFiles:
            for offer in offers:
                priceOffersFile = pattern_fileConfigurations.format(offer)
                problemFileName = pattern_problem_file_name.format(testProblem)

                mp = ManeuverProblem()
                mp.readConfiguration(problemFileName)
                mp.priceOffersFile = priceOffersFile
                availableConfigurations = read_available_configurations(priceOffersFile)


                with open(resultFileName, 'a', newline='') as csvfile:
                    spamwriter = csv.writer(csvfile, delimiter=';')

                    strat_time = time.time()
                    try:
                        cost, costVector, vmNr, allocationMatrix = mp.solveCP(strategy, 10000, True, availableConfigurations,10000)
                    except (UnboundLocalError):
                        cost, costVector, vmNr, allocationMatrix = 0,[], 0, []

                    end_time = time.time()
                    print("%%%%", cost, costVector, vmNr, allocationMatrix)
                    if len(costVector) == 0:
                        for i in range(2):
                            spamwriter.writerow(["Cp", testProblem, offer, strategy, (end_time - strat_time), 0, [], [], []])
                    else:
                        for i in range(2):
                            spamwriter.writerow(["Cp", testProblem, offer, strategy, (end_time-strat_time),  numpy.sum(costVector[i]), vmNr[i],
                                                 costVector[i], allocationMatrix[i]])
                    print("Cp", testProblem, offer, strategy, (end_time-strat_time),  cost, vmNr)

def run_test(problemFileName, resultsDirectoryPath, priceOffersFile, numberOfRepeat):
    mp = ManeuverProblem()
    mp.readConfiguration(problemFileName)
    mp.priceOffersFile = priceOffersFile


    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    str = problemFileName.split("/")
    outFileName = resultsDirectoryPath + "/" + str.pop().split(".")[0] + ".csv"

    with open(outFileName, 'a', newline='') as csvfile:
        spamwriter = csv.writer(csvfile, delimiter=';')
        spamwriter.writerow(["Algorithm", "NrOfVMInitial", "Time(s)",  "NrOfVMSolution", "Price", "NrOfUnsidesfiedConstraints", "IterationsNr", "StagnationNr", "SucessMutations", "Solution", "Price", "NrOfSuccessCPMutation", "betterSolutionFromMutationCP", "OtherInformations"])
    for i in range(numberOfRepeat):
        with open(outFileName, 'a', newline='') as csvfile:
            spamwriter = csv.writer(csvfile, delimiter=';')
            popSize = 25
            cpInstances = 2
            iterations = 100
            stagnations = 50
            availableConfigurations = read_available_configurations(priceOffersFile)
            strat_time = time.time()
            nrvm, price, nrconstaints, solution, priceList, iterationsNr, stagnationNr, successMutationNr, sucessMutationCP, betterSolutionFromMutationCP = mp.solveEA(popSize, cpInstances, iterations, stagnations, 0.1, 0.25, availableConfigurations)
            end_time = time.time()
            eaDetails = "EA: populationsize: {}, 6*cpInstances: {}, iterations: {}, stagnations: {}".format(popSize, cpInstances, iterations, stagnations)
            spamwriter.writerow(["EA", mp.nrVM, (end_time-strat_time),  nrvm, price, nrconstaints, iterationsNr, stagnationNr, successMutationNr, solution.tolist(), priceList, sucessMutationCP, betterSolutionFromMutationCP, eaDetails])

    # with open(outFileName, 'a', newline='') as csvfile:
    #     spamwriter = csv.writer(csvfile, delimiter=';')
    #     for i in range(numberOfRepeat):
    #         strat_time = time.time()
    #         nrvm, nrconstaints, solution = mp.solveEA(50, 5, 100, 10)
    #         end_time = time.time()
    #         spamwriter.writerow(["EA5", (end_time - strat_time), nrvm, nrconstaints, solution,
    #                              "solveEA(popsize=50, CPInit=5, it=100, stagnation=10)"])
    # with open(outFileName, 'a', newline='') as csvfile:
    #     spamwriter = csv.writer(csvfile, delimiter=';')
    #
    #     for i in range(numberOfRepeat):
    #         strat_time = time.time()
    #         nrvm, nrconstaints, solution = mp.solveEA(50, 10, 100, 10)
    #         end_time = time.time()
    #         spamwriter.writerow(["EA10", (end_time - strat_time), nrvm, nrconstaints, solution,
    #                              "solveEA(popsize=50, CPInit=10, it=100, stagnation=10)"])

    # with open(outFileName, 'a', newline='') as csvfile:
    #     spamwriter = csv.writer(csvfile, delimiter=';')
    #     #     spamwriter.writerow(["Algorithm", "Time(s)", "NrOfVMInitial", "OptimalVMNr", "Solution", "OtherInformations"])
    #
    #     for i in range(numberOfRepeat):
    #         strat_time = time.time()
    #         runningTime, nrvm, vms, allocation = mp.solveCP("FIRST_UNBOUND_MIN", 100000000, True, None)
    #         end_time = time.time()
    #         spamwriter.writerow(["FIRST_UNBOUND_MIN", (end_time - strat_time), mp.nrVM,nrvm,allocation,
    #                              "solveCP(FIRST_UNBOUND_MIN, 100000000, True, None"])
    #
    #     csvfile.close()

def read_available_configurations(fileConfigurations):

    with open(fileConfigurations) as json_data:
        dictionary = json.load(json_data)

    availableConfigurations = []
    for key, value in dictionary.items():
        l = [key]
        l.append(value["cpu"])
        l.append(value["memory"])
        l.append(value["storage"])
        l.append(value["price"])
        availableConfigurations.append(l)
    #print(availableConfigurations)
    return availableConfigurations


def testFinal(outputDirectoryPath):

    offers = [10, 20, 40, 100]#10, 40, 60, 80, 100]
    testFiles = ["oryx2v2-2", "WebIntrusionDetection3", "Wordpress4", "Wordpress5", "Wordpress6", "Wordpress7"]
    #testFiles = ["oryx2v2-2"],
         # "WebIntrusionDetection3", "Wordpress3", "Wordpress4",
         #         "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8", "Wordpress9",
         #         "Wordpress10", "Wordpress11", "Wordpress12"]

    pattern_fileConfigurations = "../testInstances/ptArticolICCP/testOffers/offers_{}.json"
    pattern_problem_file_name = "../testInstances/ptArticolICCP/testProblems/{}.json"



    for offer in offers:
        fileConfigurations = pattern_fileConfigurations.format(offer)

        for testProblem in testFiles:
            mp = ManeuverProblem()
            mp.priceOffersFile = fileConfigurations

            problem_file_name = pattern_problem_file_name.format(testProblem)
            #print("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!", problem_file_name)
            run_test(problem_file_name, outputDirectoryPath + "/ea_offer{}/".format(offer), fileConfigurations, 30)

def constructFileFromCp():
    offers = [10, 20, 40, 60, 80, 100]
    testFiles = ["oryx2v2-2"
        , "WebIntrusionDetection3", "Wordpress3", "Wordpress4",
                 "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8", "Wordpress9",
                 "Wordpress10", "Wordpress11", "Wordpress12"]
    path = "../testInstances/ptArticolICCP/"
    cp_selection_strategies = ["FIRST_UNBOUND_MIN","FIRST_UNBOUND_MAX", "FIRST_UNBOUND_RANDOM", \
                               "RANDOM_MIN", "RANDOM_MAX", "RANDOM_RANDOM"]  #

    with open(path + "cpAdunate_new_1.csv", 'w', newline='') as csvfile:
        spamwriter = csv.writer(csvfile, delimiter=';')

        # row1 = [" "]
        # row2 = [" "]
        # row3 = [" "]
        # for problem in testFiles:
        #     row1.append(problem)
        #
        #     for strategy in cp_selection_strategies:
        #         row3.append("VM Nr")
        #         row3.append("Price")
        #         row3.append("Time")
        #         row2.append(strategy)
        #         row2.append(" ")
        #         row2.append(" ")
        #         row1.append(" ")
        #     row1.pop() # remove one problem name
        #
        # spamwriter.writerow(row1)
        # spamwriter.writerow(row2)
        # spamwriter.writerow(row3)


        # rezMat =[[offers[i]] for i in range(len(offers))]
        # with open(path+"/results/cp_run_intermediar.csv", 'r') as csvfile:
        #     spamreader = csv.reader(csvfile, delimiter=';', quotechar='|')
        #
        #     firstRow = 0
        #     line = 0
        #     offerIndex = 0
        #     for row in spamreader:
        #         if firstRow == 0:
        #             firstRow = 1
        #             continue
        #         rezMat[offerIndex].append(row[6])
        #         rezMat[offerIndex].append(row[5])
        #         rezMat[offerIndex].append(row[4])
        #
        #         offerIndex += 1
        #         if offerIndex % len(offers) == 0:
        #             offerIndex = 0
        #
        # for row in rezMat:
        #     spamwriter.writerow(row)



        row1 = [" "]
        row2 = [" "]
        row3 = [" "]
        for problem in testFiles:
            row1.append(problem)

            for offer in offers:
                row3.append("VM Nr")
                row3.append("Price")
                row3.append("Time")
                row2.append("Offer "+str(offer))
                row2.append(" ")
                row2.append(" ")
                row1.append(" ")
                row1.append(" ")
                row1.append(" ")

            row1.pop() # remove one problem name

        spamwriter.writerow(row1)
        spamwriter.writerow(row2)
        spamwriter.writerow(row3)
        rezMat =[[cp_selection_strategies[i]] for i in range(len(cp_selection_strategies))]
        with open(path+"/results/cp_run_intermediar.csv", 'r') as csvfile:
            spamreader = csv.reader(csvfile, delimiter=';', quotechar='|')

            firstRow = 0
            line = 0
            offerIndex = 0
            for row in spamreader:
                if firstRow == 0:
                    firstRow = 1
                    continue
                #print(row)
                rezMat[offerIndex].append(row[6])
                rezMat[offerIndex].append(row[5])
                rezMat[offerIndex].append(row[4])

                line += 1
                if line % (len(offers)*len(testFiles)) == 0:
                    offerIndex += 1

        for row in rezMat:
            spamwriter.writerow(row)


def constructFinal_agregat(resultsPath):
    offers = [10, 20, 40, 100]  # 10, 40, 60, 80, 100]
    testFiles = ["oryx2v2-2", "WebIntrusionDetection3", "Wordpress4", "Wordpress5", "Wordpress6", "Wordpress7"]
    #testVariants = ["ea_minComp1", "ea_minComp1_50_stagnation", "ea_minComp1_50_stagnation_population50",
    # "ea_minComp1_50_stagnation_population25_cpPrice", "ea_minComp1_50_stagnation_population25_cpPrice_cpRestrictions1",
    #  "ea_minComp1minBean_50_stagnation_population25_cpPrice_cpRestrictions1","ea_minCompMinBean"]#, "ea_minComp_mutPrice_5", "ea_minCompMinBean_mutPrice_5"]
    testVariants = ["ea_minComp1_50_stagnation_population25", "ea_minComp1minBean_50_stagnation_population25_r2",
                    "ea_minComp1_50_stagnation_population25_pr", "ea_minComp1minBean_50_stagnation_population25_pr"]
    smtResults={"oryx2v2-2_10":[54912,6,  15.91],
    "oryx2v2-2_20": [54912, 6, 16.21],
    "oryx2v2-2_40": [26400, 6, 49.52],
    "oryx2v2-2_100": [26400, 6, 87.01]

    ,"WebIntrusionDetection3_10": [11611, 5, 0.15]
    ,"WebIntrusionDetection3_20": [2889, 5, 0.29]
    ,"WebIntrusionDetection3_40": [2889, 5, 0.41]
    ,"WebIntrusionDetection3_100": [2019, 5, 1.69]

    ,"Wordpress4_10": [10145, 10, 10.13]
    ,"Wordpress4_20": [1654, 10, 27.02]
    ,"Wordpress4_40": [1654, 10, 144.19]
    ,"Wordpress4_100": [1584, 10, 2786.18]

    ,"Wordpress5_10": [13099, 12, 215.74]
    ,"Wordpress5_20": [1884, 12, 1406.55]
    ,"Wordpress5_40": [-1, -1, -1]
    ,"Wordpress5_100": [-1, -1, -1]

    ,"Wordpress6_10": [13245, 13, 325.99]
    ,"Wordpress6_20": [1 - 1, -1, -1]
    ,"Wordpress6_40": [-1, -1, -1]
    ,"Wordpress6_100": [-1, -1, -1]

    ,"Wordpress7_10": [-1, -1, -1]
    ,"Wordpress7_20": [- 1, -1, -1]
    ,"Wordpress7_40": [-1, -1, -1]
    ,"Wordpress7_100": [-1, -1, -1]
    }

    with open(resultsPath + "/cp_all_ea.csv", 'w', newline='') as outCsvfile:
        spamwriter = csv.writer(outCsvfile, delimiter=';')

        for testProblem in testFiles:
            spamwriter.writerow([])
            spamwriter.writerow([testProblem])
            rezMat = [["InitialVmNr"], ["EaVmNr"], ["SmtVmNr"], ["EaMinPrice"], ["SmtMinPrice"], ["EATotalTime"],
                      ["SmtTime"],["Min/30"], ["MinSMT/30"], ["AvgTime"]]
            line1 =["Offer"]
            line2 = ["Algorithm"]
            for offer in offers:
                line1.append(offer)
                for i in range(len(testVariants)-1):
                    line1.append(" ")
                for testAlg in testVariants:
                    line2.append(testAlg)

            spamwriter.writerow(line1)
            spamwriter.writerow(line2)

            for offer in offers:
                for algVariant in testVariants:
                    path = resultsPath + "/" + algVariant + "/ea_offer" + str(offer) + "/" + testProblem + ".csv"

                    with open(path, 'r') as csvfile:
                        spamreader = csv.reader(csvfile, delimiter=';', quotechar='|')

                        firstRow = 0
                        runIndex = 0 #suma timp de rulare
                        minPrice = 10000000000
                        minPriceTime = -1
                        minPriceVm = -1

                        initialVmNr = -1
                        nrOfTimesThatMinimumIsReached = 0
                        nrOfTimesThatMinimumIsReachedSMT = 0

                        smt = smtResults[testProblem+"_"+str(offer)]
                        minPriceSMT = smt[0]
                        print(smt)

                        totalTime = 0
                        for row in spamreader:
                            if firstRow == 0:
                                firstRow = 1
                                continue
                            # print(row)
                            initialVmNr = row[1]
                            time = float(row[2])
                            vmnr = row[3]
                            price = float(row[4])

                            runIndex += 1
                            if minPrice > price:
                                minPrice = price
                                nrOfTimesThatMinimumIsReached = 1
                                minPriceVm = vmnr
                                minPriceTime = time
                            elif minPrice == price:
                                nrOfTimesThatMinimumIsReached += 1

                            if price == minPriceSMT:
                                nrOfTimesThatMinimumIsReachedSMT += 1
                            totalTime += time


                        print("minPriceSMT", minPriceSMT, "vm nr", smt[1])

                        rezMat[0].append(initialVmNr)
                        rezMat[1].append(minPriceVm)
                        rezMat[2].append(smt[1])

                        rezMat[3].append(minPrice)
                        rezMat[4].append(minPriceSMT)

                        rezMat[5].append(totalTime)
                        rezMat[6].append(smt[2])

                        rezMat[7].append(nrOfTimesThatMinimumIsReached)
                        rezMat[8].append(nrOfTimesThatMinimumIsReachedSMT)

            for row in rezMat:
                spamwriter.writerow(row)


def constructFinalFile():
    offers = [10, 20, 40, 60, 80, 100]
    testFiles = ["oryx2v2-2"
        , "WebIntrusionDetection3", "Wordpress3", "Wordpress4",
                 "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8", "Wordpress9",
                 "Wordpress10", "Wordpress11", "Wordpress12"]

    path = "../testInstances/ptArticolICCP/"

    #           {"oryx2v2-2_60",[6,26400]},{"oryx2v2-2_80",[6,26400]},{"oryx2v2-2_100",[6,26400]}}




    shortVersion= True

    if shortVersion:
        factor = 3
        fileName = "rezAdunate3-ea.csv"
    else:
        factor = 6
        fileName = "rezAdunate3-ea-all.csv"

    with open(path + fileName, 'w', newline='') as csvfile:
        spamwriter = csv.writer(csvfile, delimiter=';')
        row1 = []
        row2 = []
        row3 = []
        for testProblem in testFiles:
            row1.append(testProblem)
            for i in range(factor * len(offers) - 1):
                    row1.append(" ")
            for offer in offers:
                row2.append("offer" + str(offer))
                row2.append(" ")
                row2.append(" ")
                if not shortVersion:
                    row2.append(" ")
                    row2.append(" ")
                    row2.append(" ")
                row3.append("VMs")
                row3.append("Price")
                row3.append("Time")
                if not shortVersion:
                    row3.append("ViolatedConstraints")
                    row3.append("IterationNr")
                    row3.append("SucessMutations")
        spamwriter.writerow(row1)
        spamwriter.writerow(row2)
        spamwriter.writerow(row3)

        rezMat = [[]for i in range(30)]
        for testProblem in testFiles:
            for offer in offers:
                fileName = path + "results_ea/ea_offer"+str(offer)+"/"+testProblem+".csv"
                print(fileName)
                with open(fileName, 'r') as csvfile:
                    spamreader = csv.reader(csvfile, delimiter=';', quotechar='|')
                    firstRow = 0
                    count = 0
                    for row in spamreader:
                        if firstRow == 0:
                            firstRow = 1
                            continue
                        rezMat[count].append(row[3])
                        rezMat[count].append(row[4])
                        rezMat[count].append(row[2])
                        if not shortVersion:
                            rezMat[count].append(row[5])
                            rezMat[count].append(row[6])
                            rezMat[count].append(row[8])

                        count += 1
                        #print (', '.join(row))

        for row in rezMat:
            spamwriter.writerow(row)


def runCPOnce(problem_file_name, configurations_file_name):
    availableConfigurations = read_available_configurations(configurations_file_name)
    mp = ManeuverProblem()
    mp.readConfiguration(problem_file_name)
    strat_time = time.time()
    objectiveValue, _costVector, _vm, _a = mp.solveCP("RANDOM_MIN", 100000000000, True, availableConfigurations, 500000)
    stop_time = time.time()
    print(problem_file_name, configurations_file_name)
    print("runningTime", (stop_time-strat_time), "cost", objectiveValue, "_costVector", _costVector)


def runEAOnce(problem_file_name, configurations_file_name):
    mp = ManeuverProblem()
    mp.readConfiguration(problem_file_name)
    availableConfigurations = read_available_configurations(configurations_file_name)
    mp.priceOffersFile = configurations_file_name
    mp.solveEA(24, 2, 30, 10, 0.1, 0.25, availableConfigurations)

def aboutOffers(path):
    with open(path) as json_data:
        dictionary = json.load(json_data)

    memorySet = set()
    storageSet = set()
    for id, entry in dictionary.items():
        memorySet.add(entry["memory"])
        storageSet.add(entry["storage"])

    print("storageSet", storageSet, "memorySet", memorySet)

def runZ3OnceLinear(problem_file_name, configurations_file_name, solver):

    filename1 = problem_file_name.split("/").pop().split(".")[0]
    filename2 = configurations_file_name.split("/").pop().split(".")[0]

    resultsDirectoryPath = "../output_"+solver+"/csv/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    outcsv = resultsDirectoryPath + filename1 + "-" + filename2 + ".csv"

    # File for saving the problem into SMT2LIB format
    resultsDirectoryPath = "../output_"+solver+"/SMT2/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2lib = resultsDirectoryPath + filename1 + "-" + filename2 + ".smt2"

    # File for saving the solution of the problem into SMT2LIB format
    resultsDirectoryPath = "../output_"+solver+"/SMT2-Sol/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2libsol = resultsDirectoryPath + filename1 + "-" + filename2 + "-sol.smt2"

    with open(outcsv, 'w', newline='') as csvfile:
        fwriter = csv.writer(csvfile, delimiter=',', )
        fwriter.writerow(['Price min value', 'Price for each machine', 'Time'])
        for it in range(1):
            mp = ManeuverProblem()
            try:
                mp.readConfiguration(problem_file_name)
            except IOError:
                print("File '%s' doesn't exist", problem_file_name)
                exit(1)

            availableConfigurations = read_available_configurations(configurations_file_name)
            mp.priceOffersFile = configurations_file_name
            # debug - used for debugging
            # optimize - used for debugging
            #if useSimetryBr:
            minPrice, priceVMs, t = mp.solveSMT(availableConfigurations,
                                                    smt2lib,
                                                    smt2libsol,
                                                    "optimize",
                                                    solver
                                                    # ,
                                                    # use_Price_Simetry_Brecking=True,
                                                    # use_components_on_vm_Simetry_Breaking=True,
                                                    # use_fix_variables=True,
                                                    # filter_offers=True
                                                    )
            # else:
            #     print("here")
            #     minPrice, priceVMs, t = mp.solveSMT(availableConfigurations,
            #                                         smt2lib,
            #                                         smt2libsol,
            #                                         "optimize",
            #                                         solver,
            #                                         use_Price_Simetry_Brecking=False,
            #                                         use_components_on_vm_Simetry_Breaking=False,
            #                                         use_fix_variables=False,
            #                                         filter_offers=False)

            print("min price = {}, price vm = {}, time = {}".format(minPrice, priceVMs, t))
            fwriter.writerow([minPrice, priceVMs, t])

        csvfile.close()

def runZ3OnceNonlinear(problem_file_name, configurations_file_name, solver):

    filename1 = problem_file_name.split("/").pop().split(".")[0]
    filename2 = configurations_file_name.split("/").pop().split(".")[0]

    resultsDirectoryPath = "../nonlinear_output_"+solver+"/csv/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    outcsv = resultsDirectoryPath + filename1 + "-" + filename2 + ".csv"

    # File for saving the problem into SMT2LIB format
    resultsDirectoryPath = "../nonlinear_output_"+solver+"/SMT2/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2lib = resultsDirectoryPath + filename1 + "-" + filename2 + ".smt2"

    # File for saving the solution of the problem into SMT2LIB format
    resultsDirectoryPath = "../nonlinear_output_"+solver+"/SMT2-Sol/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2libsol = resultsDirectoryPath + filename1 + "-" + filename2 + "-sol.smt2"

    with open(outcsv, 'w', newline='') as csvfile:
        fwriter = csv.writer(csvfile, delimiter=',', )
        fwriter.writerow(['Price min value', 'Price for each machine', 'Time'])
        for it in range(1):
            mp = ManeuverProblem()
            try:
                mp.readConfiguration(problem_file_name)
            except IOError:
                print("File '%s' doesn't exist", problem_file_name)
                exit(1)

            availableConfigurations = read_available_configurations(configurations_file_name)
            mp.priceOffersFile = configurations_file_name
            # debug/optimize
            minPrice, priceVMs, t = mp.solveSMT(availableConfigurations, smt2lib, smt2libsol, "optimize", solver)
            print("min price = {}, price vm = {}, time = {}".format(minPrice, priceVMs, t))
            fwriter.writerow([minPrice, priceVMs, t])

        csvfile.close()


if __name__ == "__main__":
    ##############################
    ### SMT_Solver_Z3_RealReal ###
    ##############################
    # TODO: argument True/False use both real symmetry breaking. Not correct
    runZ3OnceLinear("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_RealReal")
    #runZ3OnceLinear("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_RealReal")
    #
    #runZ3OnceLinear("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_RealReal")
    #
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_100.json",
    #           "SMT_Solver_Z3_RealReal")
    #
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_RealReal")
    #

    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_RealReal")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_100.json",
    #          "SMT_Solver_Z3_RealReal")

    #runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_4.json",
    #          "SMT_Solver_Z3_RealReal")
    #runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_RealReal")
    #runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_20.json",
    #          "SMT_Solver_Z3_RealReal")

    #runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_4.json",
    #          "SMT_Solver_Z3_RealReal")

    #############################
    ### SMT_Solver_Z3_RealBool###
    #############################
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_RealBool")

    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_RealBool")
    #
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_100.json",
    #           "SMT_Solver_Z3_RealBool")

    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_100.json",
    #          "SMT_Solver_Z3_RealBool")
    #
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_4.json",
    #          "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_RealBool")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_20.json",
    #          "SMT_Solver_Z3_RealBool")

    #runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_4.json",
    #         "SMT_Solver_Z3_RealBool")
    #runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_RealBool")

    ##############################
    ### SMT_Solver_Z3_IntIntOr ###
    ##############################
    # TODO for only for Oryx2: there is a bug in Z3 optimize since the problem is SAT
    # runZ3OnceLinear("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_IntIntOr", False)
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_IntIntOr")

    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_IntIntOr")
    # #
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_100.json",
    #           "SMT_Solver_Z3_IntIntOr")

    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_IntIntOr")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_100.json",
    #          "SMT_Solver_Z3_IntIntOr")

    #runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_4.json",
    #         "SMT_Solver_Z3_IntIntOr")
#     runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_10.json",
#               "SMT_Solver_Z3_IntIntOr")
    #runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_20.json",
    #         "SMT_Solver_Z3_IntIntOr")

    #runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_IntIntOr")

    ####################################
    ### SMT_Solver_Z3_IntIntLessThan ###
    ####################################
    # TODO only for Oryx2: there is a bug in Z3 optimize since the problem is SAT
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_IntIntLessThan")
    #
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_IntIntLessThan")
    #
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_100.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    #
    #runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_4.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_10.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_40.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_60.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_80.json",
    #           "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_100.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
#
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_4.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_20.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_40.json",
    #        "SMT_Solver_Z3_IntIntLessThan")

    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_4.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_10.json",
    #          "SMT_Solver_Z3_IntIntLessThan")
    #runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_20.json",
    #         "SMT_Solver_Z3_IntIntLessThan")


    ########################
    ### SMT_Solver_Z3_BV ###
    ########################

    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_BV")

    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_BV")

    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_BV")

    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_BV")

    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_60.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_80.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress5.json", "../testInstances/offersICCP2018/offers_100.json", "SMT_Solver_Z3_BV")
    #
    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress6.json", "../testInstances/offersICCP2018/offers_40.json", "SMT_Solver_Z3_BV")

    #runZ3Once("../testInstances/Wordpress7.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress7.json", "../testInstances/offersICCP2018/offers_10.json", "SMT_Solver_Z3_BV")
    # runZ3Once("../testInstances/Wordpress7.json", "../testInstances/offersICCP2018/offers_20.json", "SMT_Solver_Z3_BV")

    # runZ3Once("../testInstances/Wordpress8.json", "../testInstances/offersICCP2018/offers_4.json", "SMT_Solver_Z3_BV")

#run_test_cp("../testInstances/ptArticolICCP/results/")
    #testFinal("../testInstances/ptArticolICCP/final/ea_minComp1minBean_50_stagnation_population25_r2")
    #constructFinalFile()

    #constructFinal_agregat("../testInstances/ptArticolICCP/final")

    #runCPOnce("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json")


    # runEAOnce("../testInstances/Wordpress3.json", "../testInstances/offersICCP2018/offers_4.json")

    # logging.config.fileConfig('loggerConfig.conf')
    # logger = logging.getLogger("maneuverApp")
    # logger.info("Start new run")


    #mp.readConfiguration("../testInstances/problemaGabi/oryx2.json")
    #nr = 20
    #fileConfigurations = "../testInstances/ptArticolICCP/testOffers/offers_{}.json".format(nr)

    #problem_file_name = "../testInstances/ptArticolICCP/wordpress2.json"
    #problem_file_name = "../testInstances/problemaGabi/wordpress1.json"
    #problem_file_name = "../testInstances/ptArticolICCP/testProblems/Wordpress5.json"
    #problem_file_name = "../testInstances/ptArticolICCP/testProblems/oryx2v2-2.json"
    #problem_file_name = "../testInstances/ptArticolICCP/WebIntrusionDetection3.json"

    #runEAOnce(problem_file_name, fileConfigurations)

    #run_test(problem_file_name, "../testInstances/results/ea_test_init__5_oferte{}/".format(nr), fileConfigurations, 40)


    #mp.readConfiguration("../testInstances/problemaGabi/wordpress.json")
   # mp.readConfiguration("../testInstances/problemaGabi/wordpress1.json")
    #mp.readConfiguration("../testInstances/problemaGabi/WebIntrusionDetection.json")

    #mp.readConfiguration("../testInstances/problemaGabi/oryx2_v2.json")

    #problem_file_name = "../testInstances/problemaGabi/wordpress1.json"
    #problem_file_name = "../testInstances/ptArticolICCP/wordpress2.json"
    #problem_file_name = "../testInstances/ptArticolICCP/oryx2v2-2.json"
   # problem_file_name = "../testInstances/ptArticolICCP/WebIntrusionDetection3.json"
   # logger.info('Read configuration {}'.format(problem_file_name))
    #mp.readConfiguration(problem_file_name)

    #mp.addComponent('{"id": "mysql", "HC":3, "HCtype" : "gpu", "HM": 4, "HMtype" :"habar nu am", "HS":200, "HStype": "SSD", "HNin":123, "HNout":456}')
    #print(mp)
    #print(mp.solve( CP_Solver_Pulp(), availableConfigurations))