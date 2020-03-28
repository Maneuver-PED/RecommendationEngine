# from maneuverRecomadEngine.exactsolvers.CP_Pulp import CP_Solver_Pulp
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
    # print(availableConfigurations)
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

    print("nrComp=", mp.nrComp, "nrVM=", mp.nrVM)
    return mp


def runOnce(solver, mp, outFolderDetails, repetion_number=1,
            default_offers_encoding=True,
            sb_vms_order_by_price=False,
            sb_vms_order_by_components_number=False,
            sb_fix_variables=False,
            sb_redundant_price=False,
            sb_redundant_processor=False,
            sb_redundant_memory=False,
            sb_redundant_storage=False,
            sb_equal_vms_type_order_by_components_number=False,
            sb_equal_vms_type_order_lex=False,
            sb_one_to_one_dependency=False,
            sb_lex_line=False,
            sb_lex_line_price=False,
            sb_lex_col_binary=False,
            sb_vms_order_by_components_number_order_lex=False):
    solver_name = solver.__class__.__name__
    filename1 = "" + mp.applicationName
    filename2 = mp.priceOffersFile.split("/").pop().split(".")[0]
    folder = "../journal/" + outFolderDetails

    resultsDirectoryPath = folder + "/output_" + solver_name + "/csv/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)

    outcsv = resultsDirectoryPath + filename1 + "-" + filename2 + ".csv"

    # File for saving the problem into SMT2LIB format
    resultsDirectoryPath = folder + "/output_" + solver_name + "/SMT2/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2lib = resultsDirectoryPath + filename1 + "-" + filename2 + ".smt2"

    # File for saving the solution of the problem into SMT2LIB format
    resultsDirectoryPath = folder + "/output_" + solver_name + "/SMT2-Sol/"
    if not os.path.exists(resultsDirectoryPath):
        os.makedirs(resultsDirectoryPath)
    smt2libsol = resultsDirectoryPath + filename1 + "-" + filename2 + "-sol.smt2"

    with open(outcsv, 'w', newline='') as csvfile:
        fwriter = csv.writer(csvfile, delimiter=',', )
        fwriter.writerow([default_offers_encoding,
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
                                            sb_one_to_one_dependency=sb_one_to_one_dependency,
                                            sb_lex_line=sb_lex_line,
                                            sb_lex_line_price=sb_lex_line_price,
                                            sb_lex_col_binary=sb_lex_col_binary,
                                            sb_vms_order_by_components_number_order_lex=sb_vms_order_by_components_number_order_lex
                                            )
            minPrice, priceVMs, t, a, vms_type = solver.run()
            print("min price = {}, price vm = {}, time = {}".format(minPrice, priceVMs, t))
            fwriter.writerow([minPrice, priceVMs, t])

        csvfile.close()


def agregate_tests(solverName, outputFileName):
    offers = ["offers_20", "offers_40", "offers_100", "offers_250", "offers_500"
              ]
    applications = ["Oryx 2",
                    "SecureBillingEmail",
                    "SecureWebContainer",
                    #add delete depending on how much Wordpress scaled
                    "Wordpress3", "Wordpress4", "Wordpress5", "Wordpress6", "Wordpress7", "Wordpress8"]
    configurations = [
        # PRFV
        "price_fixvar_offerOld",
        # FV,
        "fixvar_offerOld",
        # no sym breaking
        "simple_offerOld",
        # PR
        "price_offerOld",
        # VMLX
        "vmLoad_lex_offerOld",
         # TVMLX
        "vmtype_vmload_lex_offerOld"
         ]

    firstLine = ["strategy"]
    secondLine = [""]
    thirdLine = [""]
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
        print("../journal/" + outputFileName + ".csv")
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        outfile.writerow(secondLine)
        outfile.writerow(thirdLine)
        for configuration in configurations:
            fileInfo = [configuration]
            for application in applications:
                for offer in offers:
                    incsv = "../journal/" + configuration + "/output_" + solverName + "/csv/" + application + "-" + offer + ".csv"
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

def agregate_tests_grafice(outputFileName):
    offers = ["offers_20", "offers_40", "offers_100", "offers_250", "offers_500"]
    applications = ["Oryx 2", "SecureBillingEmail", "WebIntrusionDetection", "Wordpress3", "Wordpress4", "Wordpress5",
                    "Wordpress6", "Wordpress7", "Wordpress8"]
    solvers = ["Z3_SolverIntIntSymBreak", "CPlex_SolverSymBreak"]

    configurations = [
        # PRFV
        "price_fixvar_offerOld",
        # FV,
        "fixvar_offerOld",
        # no sym breaking
        "simple_offerOld",
        # PR
        "price_offerOld",
        # VMLX
        "vmLoad_lex_offerOld",
        # TVMLX
        "vmtype_vmload_lex_offerOld"
    ]

    firstLine = ["strategy","solver"]
    secondLine = [""]
    thirdLine = [""]
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
            thirdLine.extend([ "Mean"])

    with open("../journal/" + outputFileName + ".csv", 'w', newline='') as csvfile:
        print("../journal/" + outputFileName + ".csv")
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        outfile.writerow(secondLine)
        outfile.writerow(thirdLine)
        for configuration in configurations:
            for solverName in solvers:
                print(solverName)
                fileInfo = [configuration, solverName]
                line_value = []
                for application in applications:
                    for offer in offers:
                        incsv = "../journal/" + configuration + "/output_" + solverName + "/csv/"+ application + "-" + offer + ".csv"
                        from os import listdir
                        from os.path import isfile, join
                        # onlyfiles = [f for f in listdir(incsv) if isfile(join(incsv, f))]
                        print(incsv)#,onlyfiles)
                        import os.path
                        from os import path
                        print("File exists:" + str(path.exists(incsv)))
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
                                #print(vtimes)
                                if len(vtimes) == 0:
                                    line_value.append(2400)
                                    #fileInfo.extend([2400])
                                else:
                                    line_value.append(numpy.mean(vtimes))
                                    #fileInfo.extend([numpy.mean(vtimes)])

                        except:
                            #fileInfo.extend([2400])
                            line_value.append(2400)
                            print("File not found")
                line_value.sort()
                fileInfo.extend(line_value)
                outfile.writerow(fileInfo)


def agregate_tests_tabel(outputFileName):
    offers = ["offers_20", "offers_40", "offers_100", "offers_250", "offers_500"]
    applications = [("Oryx 2", "Oryx2"), ("SecureBillingEmail","SBE"), ("WebIntrusionDetection", "WID"),
                    ("Wordpress3", "WP#3"), ("Wordpress4", "WP#4"), ("Wordpress5", "WP#5"),
                    ("Wordpress6", "WP#6"), ("Wordpress7", "WP#7"), ("Wordpress8", "WP#8")]

    solvers = ["Z3_SolverIntIntSymBreak", "CPlex_SolverSymBreak"]

    configurations = [
        # PRFV
        "price_fixvar_offerOld",
        # FV,
        "fixvar_offerOld",
        # no sym breaking
        "simple_offerOld",
        # PR
        "price_offerOld",
        # VMLX
        "vmLoad_lex_offerOld",
        # TVMLX
        "vmtype_vmload_lex_offerOld"
    ]

    firstLine = ["Problem", "#offers=20","","#offers=40","","#offers=100","","#offers=250","", "#offers=500",""]
    secondLine = ["", "Z3","Cplex", "Z3","Cplex", "Z3","Cplex", "Z3","Cplex", "Z3","Cplex"]
    thirdLine = [""]


    with open("../journal/" + outputFileName + ".csv", 'w', newline='') as csvfile:
        print("../journal/" + outputFileName + ".csv")
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        outfile.writerow(secondLine)

        for configuration in configurations:

            line_value = []
            for application in applications:

                offer_time = [application[1]]
                offer_mean = [' ']
                for offer in offers:
                    for solverName in solvers:
                        incsv = "../journal/" + configuration + "/output_" + solverName + "/csv/"+ application[0] + "-" + offer + ".csv"
                        from os import listdir
                        from os.path import isfile, join
                        # onlyfiles = [f for f in listdir(incsv) if isfile(join(incsv, f))]
                        print(incsv)#,onlyfiles)
                        import os.path
                        from os import path
                        print("File exists:" + str(path.exists(incsv)))
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
                                #print(vtimes)
                                if len(vtimes) == 0:
                                    offer_time.append("-")
                                    offer_mean.append(" ")
                                    #fileInfo.extend([2400])
                                else:
                                    offer_time.append('{:.2f}'.format(numpy.average(vtimes)))
                                    ss = "$\pm{"
                                    ss += "{:.2f}".format(numpy.std(vtimes)) + '}$'
                                    offer_mean.append(ss)

                        except:
                            #fileInfo.extend([2400])
                            offer_time.append("-")
                            offer_mean.append(" ")
                            print("file not found")

                print("offer_time", offer_time)
                print("offer_mean", offer_mean)
                outfile.writerow(offer_time)
                outfile.writerow(offer_mean)




def agregate_tests_tabel_offerencoding(outputFileName):
    offers = ["offers_20", "offers_40", "offers_100", "offers_250", "offers_500"]
    applications = [("Oryx 2", "Oryx2"), ("SecureBillingEmail","SBE"), ("WebIntrusionDetection", "WID"),
                    ("Wordpress3", "WP#3"), ("Wordpress4", "WP#4"), ("Wordpress5", "WP#5"),
                    ("Wordpress6", "WP#6"), ("Wordpress7", "WP#7"), ("Wordpress8", "WP#8"),
                    ("Wordpress9", "WP#9"),("Wordpress10", "WP#10"),("Wordpress11", "WP#11")]

    solvers = ["Z3_SolverIntIntSymBreak"]#, #"CPlex_SolverSymBreak"]

    configurations = [
        # PRFV
        (
        "price_fixvar_offerOld", True, True, False, True, False, False, False, False, False, False, False, False, False,
        False, False),
        # FV
        ("fixvar_offerOld", True, False, False, True, False, False, False, False, False, False, False, False, False,
         False, False),
        # no sym breaking
        ("simple_offerOld", True, False, False, False, False, False, False, False, False, False, False, False, False,
         False, False),
        # PR
        ("price_offerOld", True, True, False, False, False, False, False, False, False, False, False, False, False,
         False, False),
        # VMLX
        ("vmLoad_lex_offerOld", False, False, False, False, False, False, False, False, False, False, False, False,
         False, False, True)
        # TVMLX
        ("vmtype_vmload_lex_offerOld",
         False, False, False, False, False, False, False, False, True, True, False, False, False, False, False),
    ]

    #firstLine = ["Problem", "#offers=20","","#offers=40","","#offers=100","","#offers=250","", "#offers=500",""]
    #secondLine = ["", "Enc1","Enc2", "Enc1","Enc2", "Enc1","Enc2", "Enc1","Enc2", "Enc1","Enc2"]
    firstLine = ["Problem", "#offers=20","","","#offers=40","","","#offers=100","","","#offers=250","","", "#offers=500","",""]
    secondLine = ["", "P","PR", "PRL","P","PR", "PRL","P","PR", "PRL","P","PR", "PRL","P","PR", "PRL"]
    thirdLine = [""]


    with open("../journal/" + outputFileName + ".csv", 'w', newline='') as csvfile:
        print("../journal/" + outputFileName + ".csv")
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        outfile.writerow(secondLine)

        for application in applications:
            line_value = []
            offer_time = [application[1]]
            offer_mean = [' ']
            for offer in offers:
                for solverName in solvers:
                    for configuration in configurations:
                        incsv = "../journal/" + configuration + "/output_" + solverName + "/csv/"+ application[0] + "-" + offer + ".csv"
                        from os import listdir
                        from os.path import isfile, join
                        # onlyfiles = [f for f in listdir(incsv) if isfile(join(incsv, f))]
                        print(incsv)#,onlyfiles)
                        import os.path
                        from os import path
                        print("File exists:" + str(path.exists(incsv)))
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
                                #print(vtimes)
                                if len(vtimes) == 0:
                                    offer_time.append("-")
                                    offer_mean.append(" ")
                                    #fileInfo.extend([2400])
                                else:
                                    offer_time.append('{:.1f}'.format(numpy.average(vtimes)))
                                    ss = "$\pm{"
                                    ss += "{:.1f}".format(numpy.std(vtimes)) + '}$'
                                    offer_mean.append(ss)

                        except:
                            #fileInfo.extend([2400])
                            offer_time.append("-")
                            offer_mean.append(" ")
                            print("file not found")

            print("offer_time", offer_time)
            print("offer_mean", offer_mean)
            outfile.writerow(offer_time)
            outfile.writerow(offer_mean)


def start_tests(solver, repetion_number=1):
    offers = ["../testInstances/offersLPAR2018/offers_20.json",
              "../testInstances/offersLPAR2018/offers_40.json",
              "../testInstances/offersLPAR2018/offers_100.json",
              "../testInstances/offersLPAR2018/offers_250.json",
              "../testInstances/offersLPAR2018/offers_500.json"
    ]

    test_files = [
        # "../testInstances/Oryx2.json",
        #"../testInstances/SecureBillingEmail.json",
        # "../testInstances/SecureWebContainer.json",
        # "../testInstances/Wordpress3.json",
        #  "../testInstances/Wordpress4.json",
        # "../testInstances/Wordpress5.json",
        # "../testInstances/Wordpress6.json",
        # "../testInstances/Wordpress7.json",
        # "../testInstances/Wordpress8.json",
        # "../testInstances/Wordpress9.json",
        "../testInstances/Wordpress10.json",
        "../testInstances/Wordpress11.json",
        "../testInstances/Wordpress12.json"
                  ]

    configurations = [
        # PRFV
        ("price_fixvar_offerOld", True, True,  False, True,  False, False, False, False, False, False, False, False, False, False, False),
        # FV
        # ("fixvar_offerOld",       True, False, False, True,  False, False, False, False, False, False, False, False, False, False, False),
        # # no sym breaking
        # ("simple_offerOld",       True, False, False, False, False, False, False, False, False, False, False, False, False, False, False),
        # PR
        ("price_offerOld",        True, True,  False, False, False, False, False, False, False, False, False, False, False, False, False),
        # VMLX
        # ("vmLoad_lex_offerOld",   False, False, False, False, False, False, False, False, False, False, False, False, False, False, True),
        # # TVMLX
        # ("vmtype_vmload_lex_offerOld",
        #                            False, False, False, False, False, False, False, False, True,  True, False, False, False, False, False)
    ]
    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOrSymBreaking import Z3_SolverIntIntSymBreak

    for offer in offers:
        for problem in test_files:
            mp = prepareManuverProblem(problem, offer)
            for configuration in configurations:
                # print("-----------Z3_Solver------------------")
                # solver = Z3_SolverIntIntSymBreak()
                print("Application name ", mp.applicationName)
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
                        sb_one_to_one_dependency=configuration[11],
                        sb_lex_line=configuration[12],
                        sb_lex_line_price=configuration[13],
                        sb_lex_col_binary=configuration[14],
                        sb_vms_order_by_components_number_order_lex=configuration[15]
                        )


if __name__ == "__main__":

    from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CPlex_SolverSymBreak
    from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3_IntIntOrSymBreaking import Z3_SolverIntIntSymBreak

    # use one type of solver at a time
    solver = Z3_SolverIntIntSymBreak()
    #solver = CPlex_SolverSymBreak()

    repetion_number = 3

    # For starting tests
    start_tests(solver, repetion_number= repetion_number)

    #After having the tests, we can agregate them
    # agregate_tests("CPlex_SolverSymBreak", "agregate_Cplex_old")
    #agregate_tests("Z3_SolverIntIntSymBreak", "agregate_Z3intint")
    #agregate_tests_grafice("grafic_simple")
    #agregate_tests_tabel("tabel_simple.txt")
    #agregate_tests_tabel_offerencoding("tabel__z3_olderEnc_Price.txt")