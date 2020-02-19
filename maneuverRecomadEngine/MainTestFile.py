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

def runOnce(solver, mp, sb_vms_order_by_price=False,
                     sb_vms_order_by_components_number=False,
                     sb_fix_variables=False, sb_redundant_price=False, sb_redundant_processor=False, sb_redundant_memory=False,
                     sb_redundant_storage=False, sb_equal_vms_type_order_by_components_number=False,
                     sb_equal_vms_type_order_lex = False):

    solver_name = solver.__class__.__name__
    filename1 = ""+mp.applicationName
    filename2 = mp.priceOffersFile.split("/").pop().split(".")[0]

    resultsDirectoryPath = "../nonlinear_output_"+solver_name+"/csv/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    outcsv = resultsDirectoryPath + filename1 + "-" + filename2 + ".csv"

    # File for saving the problem into SMT2LIB format
    resultsDirectoryPath = "../jurnal_output_"+solver_name+"/SMT2/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2lib = resultsDirectoryPath + filename1 + "-" + filename2 + ".smt2"

    # File for saving the solution of the problem into SMT2LIB format
    resultsDirectoryPath = "../jurnal_output_"+solver_name+"/SMT2-Sol/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2libsol = resultsDirectoryPath + filename1 + "-" + filename2 + "-sol.smt2"

    with open(outcsv, 'w', newline='') as csvfile:
        fwriter = csv.writer(csvfile, delimiter=',', )
        fwriter.writerow(['Price min value', 'Price for each machine', 'Time'])
        for it in range(1):

            # debug/optimize


            getattr(solver, "init_problem")(mp, "optimize", smt2lib=smt2lib, smt2libsol=smt2libsol,
                                            sb_vms_order_by_price=sb_vms_order_by_price,
                                            sb_vms_order_by_components_number=sb_vms_order_by_components_number,
                                            sb_fix_variables=sb_fix_variables,
                                            sb_redundant_price=sb_redundant_price,
                                            sb_redundant_processor=sb_redundant_processor,
                                            sb_redundant_memory=sb_redundant_memory,
                                            sb_redundant_storage=sb_redundant_storage,
                                            sb_equal_vms_type_order_by_components_number=sb_equal_vms_type_order_by_components_number,
                                            sb_equal_vms_type_order_lex=sb_equal_vms_type_order_lex
                                            )
            minPrice, priceVMs, t, a, vms_type = solver.run()
            print("min price = {}, price vm = {}, time = {}".format(minPrice, priceVMs, t))
            fwriter.writerow([minPrice, priceVMs, t])

        csvfile.close()


if __name__ == "__main__":
    #aboutOffers("../testInstances/offersICCP2018/offers_10.json")

    # TODO: argument True/False use both real symmetry breaking. Not correct

    mp = prepareManuverProblem("../testInstances/Wordpress4.json", "../testInstances/offersICCP2018/offers_20.json")

    # from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOr import Z3_SolverSimple
    # print("-----------------------------")
    # solver = Z3_SolverSimple()
    # runOnce(solver, mp)

    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOrSymBreaking import Z3_Solver
    print("-----------------------------")
    solver = Z3_Solver()
    runOnce(solver, mp, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=False, sb_redundant_price=False,
            sb_equal_vms_type_order_lex=True)

    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_RealSymBreak import Z3_SolverReal
    solver = Z3_SolverReal()
    print("-----------------------------")
    runOnce(solver, mp, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=False, sb_redundant_price=False,
            sb_equal_vms_type_order_lex=True)
    # #runZ3OnceLinear("../testInstances/Oryx2.json", "../testInstances/offersICCP2018/offers_10.json", )
    #
    from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CP_Solver_CPlex
    solver = CP_Solver_CPlex()
    print("-----------------------------")
    runOnce(solver, mp, sb_vms_order_by_price=True, sb_fix_variables=False, sb_redundant_memory=False, sb_redundant_price=False,
            sb_equal_vms_type_order_lex=True)


#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]]
#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
#a_mat [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]]
