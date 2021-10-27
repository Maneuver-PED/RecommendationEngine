import os
import csv
import time
import logging
import logging.config
import json
import numpy
from os import path

if __name__ == "__main__":
    p = "../../journal/Encoding_AllCombinationsOffers/"
    sbLst = ["noSymBreaking", "PR", "LX", "FV", "PRLX", "FVPR", "FVLX"]
    appLst = ["Oryx 2", "SecureBillingEmail", "SecureWebContainer",
                "Wordpress3", "Wordpress4", "Wordpress5", "Wordpress6", "Wordpress7",
                "Wordpress8", "Wordpress9", "Wordpress10", "Wordpress11", "Wordpress12"]
    offersLst = ["offers_20", "offers_40", "offers_250", "offers_500"]
    solversLst = ["Z3"]

    firstLine = ["Solver", "Use case","Sym breaking", "#offers", "#vars", "#constraints", "time"]
    outputFileName = "data"

    varsNo   = 0
    constrNo = 0

    with open(outputFileName + ".csv", 'w', newline='') as csvfile:
        print(outputFileName + ".csv")
        outfile = csv.writer(csvfile, delimiter=';')
        outfile.writerow(firstLine)
        for sb in sbLst:
            for solver in solversLst:
                for app in appLst:
                    for offer in offersLst:
                            if solver is "Z3":
                                dir = "output_" + solver + "_SolverInt_SB_Enc_AllCombinationsOffers"

                                fileName = p + sb + "/" + dir + "/SMT2/" + app + "-" + offer + ".smt2"
                                fN       = p + sb + "/" + dir + "/csv/" + app + "-" + offer + ".csv"
                                # print("File exists:" + str(os.path.exists(fileName)))
                                # print(fileName)
                                print("File exists:" + str(os.path.exists(fN)))
                                print(fN)

                                # get time
                                if os.path.exists(fN):
                                    with open(fN) as read_time:
                                        lines = read_time.readlines()
                                    #print("line ", lines[2].rstrip())  # get 3rd line
                                    time = lines[2].rstrip().split(",")[len(lines[2].split(",")) - 1]
                                    #print("time=", time)
                                else:
                                    time = 2400

                                # elif solver is "CPlex":
                                #     dir = "output_" + solver + "_Solver_SB_Enc_AllCombinationsOffers-default-s-b"
                                #     fileName = p + sb + "/" + dir + "/CPlex_LP/" + app + "-" + offer + ".lp"
                                #     print("File exists:" + str(os.path.exists(fileName)))
                                #     print(fileName)
            #                     """ Check if any line in the file contains given string """
            #                     # Open the file in read only mode
                                varsNo = 0
                                constrNo = 0
                                if os.path.exists(fileName):
                                    with open(fileName, 'r') as read_obj:
                                        # Read all lines in the file one by one
                                        for line in read_obj:
                                            # For each line, check if line contains the string
                                            if "declare-fun" in line:
                                                varsNo += 1
                                            elif "assert" in line:
                                                constrNo += 1
                                row = [solver, app, sb, offer[len("output_"):], varsNo, constrNo, time]
                                print("row", row)
                                outfile.writerow(row)
