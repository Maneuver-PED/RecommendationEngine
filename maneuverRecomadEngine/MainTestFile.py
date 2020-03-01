#from maneuverRecomadEngine.exactsolvers.CP_Pulp import CP_Solver_Pulp
from maneuverRecomadEngine.problem.ProblemDefinition import ManeuverProblem
import maneuverRecomadEngine.exactsolvers

import os
import csv
import time
import logging
import logging.config
import json
import numpy

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

def aboutOffers(path):
    with open(path) as json_data:
        dictionary = json.load(json_data)

    memorySet = set()
    storageSet = set()
    for id, entry in dictionary.items():
        memorySet.add(entry["memory"])
        storageSet.add(entry["storage"])

    print("storageSet", storageSet, "memorySet", memorySet)

def prepareManuverProblem(problem_file_name, configurations_file_name):
    mp = ManeuverProblem()
    offers_list = read_available_configurations(configurations_file_name)
    try:
        mp.readConfiguration(problem_file_name, offers_list)
    except IOError:
        print("File '%s' doesn't exist", problem_file_name)
        exit(1)

    mp.priceOffersFile = configurations_file_name

    return mp

def runOnce(solver, mp, outFolderDetails, repetion_number=1, default_offers_encoding=True, sb_vms_order_by_price=False,
                     sb_vms_order_by_components_number=False,
                     sb_fix_variables=False, sb_redundant_price=False, sb_redundant_processor=False, sb_redundant_memory=False,
                     sb_redundant_storage=False, sb_equal_vms_type_order_by_components_number=False,
                     sb_equal_vms_type_order_lex=False, sb_one_to_one_dependency=False):

    solver_name = solver.__class__.__name__
    filename1 = ""+mp.applicationName
    filename2 = mp.priceOffersFile.split("/").pop().split(".")[0]
    folder = "../journal/" + outFolderDetails

    resultsDirectoryPath = folder + "/output_"+solver_name+"/csv/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    outcsv = resultsDirectoryPath + filename1 + "-" + filename2 + ".csv"

    # File for saving the problem into SMT2LIB format
    resultsDirectoryPath = folder + "/output_"+solver_name+"/SMT2/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2lib = resultsDirectoryPath + filename1 + "-" + filename2 + ".smt2"

    # File for saving the solution of the problem into SMT2LIB format
    resultsDirectoryPath = folder +"/output_"+solver_name+"/SMT2-Sol/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2libsol = resultsDirectoryPath + filename1 + "-" + filename2 + "-sol.smt2"

    with open(outcsv, 'w', newline='') as csvfile:
        fwriter = csv.writer(csvfile, delimiter=',', )
        fwriter.writerow([ default_offers_encoding,
                                            sb_vms_order_by_price,
                                            sb_vms_order_by_components_number,
                                            sb_fix_variables,
                                            sb_redundant_price,
                                            sb_redundant_processor,
                                            sb_redundant_memory,
                                            sb_redundant_storage,
                                            sb_equal_vms_type_order_by_components_number,
                                            sb_equal_vms_type_order_lex,
                                            sb_one_to_one_dependency])
        fwriter.writerow(['Price min value', 'Price for each machine', 'Time'])
        for it in range(repetion_number):
            # debug/optimize
            getattr(solver, "init_problem")(mp, "optimize", smt2lib=smt2lib, smt2libsol=smt2libsol,
                                            default_offers_encoding=default_offers_encoding,
                                            sb_vms_order_by_price=sb_vms_order_by_price,
                                            sb_vms_order_by_components_number=sb_vms_order_by_components_number,
                                            sb_fix_variables=sb_fix_variables,
                                            sb_redundant_price=sb_redundant_price,
                                            sb_redundant_processor=sb_redundant_processor,
                                            sb_redundant_memory=sb_redundant_memory,
                                            sb_redundant_storage=sb_redundant_storage,
                                            sb_equal_vms_type_order_by_components_number=sb_equal_vms_type_order_by_components_number,
                                            sb_equal_vms_type_order_lex=sb_equal_vms_type_order_lex,
                                            sb_one_to_one_dependency=sb_one_to_one_dependency
                                            )
            minPrice, priceVMs, t, a, vms_type = solver.run()
            print("min price = {}, price vm = {}, time = {}".format(minPrice, priceVMs, t))
            fwriter.writerow([minPrice, priceVMs, t])

        csvfile.close()

def agregate_tests(solverName, outputFileName):
    offers = ["offers_20", "offers_40", "offers_100", "offers_250", "offers_500"]
    applications = ["Oryx2", "SecureBillingEmail", "SecureWebContainer", "Wordpress3", "Wordpress4", "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8"]
    configurations = ["simple_offerOld",
                      "simple_offerNew",
                      "price_offerOld",
                      "price_offerNew",
                      "vmLoad_offerOld",
                      "vmLoad_offerNew",
                      "price_redundant_offerOld",
                      "price_redundant_offerNew",
                      "fixvar_offerOld",
                      "fixvar_offerNew",
                      "price_fixvar_redundant_offerOld",
                       "price_fixvar_redundant_offerNew",
                       "price_fixvar_offerOld",
                       "price_fixvar_offerNew",
                       "price_fixvar_redundant_byLoad_offerOld",
                       "price_fixvar_redundant_byLoad_offerNew",
                       "price_fixvar_redundant_lex_offerOld",
                       "price_fixvar_redundant_lex_offerNew",
                       "simple_oneToOne_offerOld",
                      "simple_oneToOne_offerNew"
                      ]

    firstLine = ["strategy"]
    secondLine = [""]
    thirdLine =[""]
    for application in applications:
        firstLine.append(application)
        change_app = True
        for offer in offers:
            if change_app:
                firstLine.extend([" ", " "])
                change_app = False
            else:
                firstLine.extend(["", "", ""])
            secondLine.extend([offer, "", ""])
            thirdLine.extend(["Value", "Mean", "Std"])

    with open("../journal/" + outputFileName + ".csv", 'w', newline='') as csvfile:
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        outfile.writerow(secondLine)
        outfile.writerow(thirdLine)
        for configuration in configurations:
            fileInfo = [configuration]
            for application in applications:
                for offer in offers:
                    incsv = "../journal/" + configuration + "/" + solverName + "/csv/" + application + "-" + offer+".csv"
                    print(incsv)
                    try:
                        with open(incsv, 'r') as csvfile:
                            freader = csv.reader(csvfile, delimiter=',', quotechar='"')
                            firstRow = 1
                            values = set()
                            vtimes = []
                            for row in freader:
                                if firstRow < 3:
                                    firstRow += 1
                                    continue
                                values.add(row[0])
                                vtimes.append(float(row[2]))

                            fileInfo.extend([values, numpy.mean(vtimes), numpy.std(vtimes)])

                    except:
                        fileInfo.extend(["", "", ""])
                        print("file not found")
            outfile.writerow(fileInfo)



def start_tests():
    offers = ["../testInstances/offersLPAR2018/offers_20.json", "../testInstances/offersLPAR2018/offers_40.json",
              "../testInstances/offersLPAR2018/offers_100.json", "../testInstances/offersLPAR2018/offers_250.json",
              "../testInstances/offersLPAR2018/offers_500.json"]

    test_files = ["../testInstances/Oryx2.json", "../testInstances/SecureBillingEmail.json", "../testInstances/SecureWebContainer.json",
                  "../testInstances/Wordpress3.json", "../testInstances/Wordpress4.json", "../testInstances/Wordpress5.json",
                  "../testInstances/Wordpress6.json", "../testInstances/Wordpress7.json",
                  "../testInstances/Wordpress8.json"
                  ]
    configurations = [("simple_offerOld", True, False, False, False, False, False, False, False, False, False, False),
                     ("simple_offerNew", False, False, False, False, False, False, False, False, False, False, False),
                     ("price_offerOld", True, True, False, False, False, False, False, False, False, False, False),
                     ("price_offerNew", False, True, False, False, False, False, False, False, False, False, False),
                     ("vmLoad_offerOld", True, False, True, False, False, False, False, False, False, False, False),
                     ("vmLoad_offerNew", False, False, True, False, False, False, False, False, False, False, False),
                     (
                     "price_redundant_offerOld", True, True, False, False, True, True, True, True, False, False, False),
                     ("price_redundant_offerNew", False, True, False, False, True, False, False, False, False, False,
                      False),
                     ("fixvar_offerOld", True, False, True, False, False, False, False, False, False, False, False),
                     ("fixvar_offerNew", False, False, True, False, False, False, False, False, False, False, False),
                     ("price_fixvar_redundant_offerOld", True, True, False, True, True, True, True, True, False, False,
                      False),
                     ("price_fixvar_redundant_offerNew", False, True, False, True, True, False, False, False, False,
                      False,
                      False),
                     (
                     "price_fixvar_offerOld", True, True, False, True, False, False, False, False, False, False, False),
                     ("price_fixvar_offerNew", False, True, False, True, False, False, False, False, False, False,
                      False),
                     ("price_fixvar_redundant_byLoad_offerOld", True, True, False, True, True, True, True, True, True,
                      False,
                      False),
                     ("price_fixvar_redundant_byLoad_offerNew", False, True, False, True, True, False, False, False,
                      True,
                      False,
                      False),
                     ("price_fixvar_redundant_lex_offerOld", True, True, False, True, True, True, True, True, False,
                      True,
                      False),
                     ("price_fixvar_redundant_lex_offerNew", False, True, False, True, True, False, False, False,
                      False,
                      True,
                      False),
                     ("simple_oneToOne_offerOld", True, False, False, False, False, False, False, False, False, False, True),
                     ("simple_oneToOne_offerNew", False, False, False, False, False, False, False, False, False, False, True)
                     ]
    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOrSymBreaking import Z3_SolverIntIntSymBreak
    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_RealSymBreak import Z3_SolverRealSymBreak

    for offer in offers:
        for problem in test_files:
            mp = prepareManuverProblem(problem, offer)
            for configuration in configurations:

                print("-----------Z3_Solver------------------")
                solver = Z3_SolverIntIntSymBreak()
                runOnce(solver, mp, configuration[0], repetion_number=repetion_number,
                        default_offers_encoding=configuration[1],
                        sb_vms_order_by_price=configuration[2],
                        sb_vms_order_by_components_number=configuration[3],
                        sb_fix_variables=configuration[4],
                        sb_redundant_price=configuration[5],
                        sb_redundant_processor=configuration[6],
                        sb_redundant_memory=configuration[7],
                        sb_redundant_storage=configuration[8],
                        sb_equal_vms_type_order_by_components_number=configuration[9],
                        sb_equal_vms_type_order_lex=configuration[10],
                        sb_one_to_one_dependency=configuration[11]
                        )


                solver = Z3_SolverRealSymBreak()
                print("-----------Z3_SolverReal------------------")
                runOnce(solver, mp, configuration[0], repetion_number=repetion_number,
                        default_offers_encoding=configuration[1],
                        sb_vms_order_by_price=configuration[2],
                        sb_vms_order_by_components_number=configuration[3],
                        sb_fix_variables=configuration[4],
                        sb_redundant_price=configuration[5],
                        sb_redundant_processor=configuration[6],
                        sb_redundant_memory=configuration[7],
                        sb_redundant_storage=configuration[8],
                        sb_equal_vms_type_order_by_components_number=configuration[9],
                        sb_equal_vms_type_order_lex=configuration[10],
                        sb_one_to_one_dependency=configuration[11]
                        )


if __name__ == "__main__":
    #aboutOffers("../testInstances/offersICCP2018/offers_10.json")

    mp = prepareManuverProblem("../testInstances/SecureWebContainer.json", "../testInstances/offersICCP2018/offers_20.json")

    # from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOr import Z3_SolverSimple
    # print("-----------------------------")
    # solver = Z3_SolverSimple()
    # runOnce(solver, mp)
    repetion_number = 5

    start_tests()
    #agregate_tests("output_Z3_SolverRealSymBreak", "agregateReal")

    # repetion_number = 1
    # from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOrSymBreaking import Z3_SolverIntIntSymBreak
    # print("-----------Z3_Solver------------------")
    # # # can we have the name Z3_SolverInt to be similar to the below?
    # solver = Z3_SolverIntIntSymBreak()
    # runOnce(solver, mp, "flavia",repetion_number = repetion_number, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=False, sb_redundant_price=False,
    #         sb_equal_vms_type_order_lex=False, default_offers_encoding=False, sb_vms_order_by_components_number=False)
    #         #this is not always good: sb_vms_order_by_components_number=True)
    # print("-----------Z3_Solver fix------------------")
    # runOnce(solver, mp, "flavia", repetion_number=repetion_number, sb_vms_order_by_price=True, sb_fix_variables=True,
    #         sb_redundant_memory=False, sb_redundant_price=False,
    #         sb_equal_vms_type_order_lex=False, default_offers_encoding=False, sb_vms_order_by_components_number=False)


    #
    # from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_RealSymBreak import Z3_SolverRealSymBreak
    # solver = Z3_SolverRealSymBreak()
    # print("-----------Z3_SolverReal------------------")
    # runOnce(solver, mp, repetion_number=repetion_number, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=False, sb_redundant_price=False,
    #         sb_equal_vms_type_order_lex=False, default_offers_encoding=False)
    # # #runZ3OnceLinear("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", )
    # #
    # from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CPlex_SolverSymBreak
    # solver = CPlex_SolverSymBreak()
    # print("------------CP_Solver_CPlex-----------------")
    # runOnce(solver, mp, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=True, sb_redundant_price=False,
    #         sb_equal_vms_type_order_lex=False, default_offers_encoding=False)

#wordpress 4
#500 - time = 425.969221115112 (real); 24.140674114227295 (int) - new
#500 - time = 374.8490 (real) time = 17.500(int)

#100 - time = time = 10.212916851043701(real) 20.296855688095093(int)
#100 - time -=time =  6.05139374732971\(real) 1.905466079711914(int) - new

#wordpress 5
# time = 15.9271261692(real) 37.3353168964386 (int)
# time = 5.579587936401367(real) 2.1694862842559814(int) -new 189/100

#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]
#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
