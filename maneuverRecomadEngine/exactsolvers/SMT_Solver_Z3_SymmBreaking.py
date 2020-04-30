from z3 import *
from maneuverRecomadEngine.exactsolvers.SMT_Solver_Z3 import Z3_Solver_Parent


class Z3_SolverSymmBreaking(Z3_Solver_Parent):

    def _symmetry_breaking(self):
        if self.sb_price: #PR
            self.sbPrice()
        elif self.sb_price_lex: #PRLX
            self.sbPrice(combined="RestrictionLex")
        elif self.sb_vm_load: #L
            self.sbVMLoad()
        elif self.sb_vm_load_lex: #LLX
            self.sbVMLoad(combined="RestrictionLex")
        elif self.sb_lex:  #LX
            self.sbLex();
        elif self.sb_fix_var: #FV
            self.sbFixVariables()
        elif self.sb_fix_var_price: #FVPR
            self.sbFixVariables(criteria="RestrictionPriceOrder")
        elif self.sb_fix_var_vm_load: #FVL
            self.sbFixVariables(criteria="RestrictionLoadOrder")
        elif self.sb_fix_var_lex: #FVLX
            self.sbFixVariables(criteria="RestrictionLexOrder")
        elif self.sb_fix_var_price_lex: #FVPRLX
            self.sbFixVariables(criteria="RestrictionPriceOrder", combined="RestrictionLex")
        elif self.sb_fix_var_vm_load_lex: #FVLLX
            self.sbFixVariables(criteria="RestrictionLoadOrder", combined="RestrictionLex")
        elif self.sb_load_price:
            self.sbVMLoad(combined="RestrictionPrice")
        elif self.sb_lex_col_binary: #do tests for curiosity
            self.sbBinary()


    def sbBinary(self):
        self.RestrictionLexBinaryNumber()

    def sbFixVariables(self, criteria=None, combined=None):
        """
        Fix values from maximum clique
        """
        vm_id = 0
        #print("Max cliques=", self.problem.max_clique)
        for comp_id in self.problem.max_clique:
            instances = self.problem.componentsList[comp_id].getMinimumPossibleNumberOfInstances(self.problem.componentsList)
            start_id = vm_id
            #print("comp=",comp_id," instances:", instances)
            for instance in range(instances):
                self.RestrictionFixComponentOnVM(comp_id, vm_id, 1)
                for conflict_comp_id in self.problem.componentsList[comp_id].conflictComponentsList:
                    self.RestrictionFixComponentOnVM(conflict_comp_id, vm_id, 0)

                vm_id += 1
                self.vm_with_offers[vm_id] = comp_id
                self.vmIds_for_fixedComponents.add(vm_id)
            stop_id = vm_id

            if criteria is not None:
                #print("comp=", comp_id, " interval[", start_id, ", ", stop_id, "]")
                getattr(self, criteria)(start_id, stop_id, combined)
        if criteria is not None:
            print("rest_of interval", " interval[", stop_id, ", ", self.nrVM, "]")
            getattr(self, criteria)(stop_id, self.nrVM, combined)


    def sbLex(self):
        self.RestrictionLexOrder(0, self.nrVM)

    def sbPrice(self, combined=None):
        """
         order by price
        :return:
        """
        #print("sbPrice")
        self.RestrictionPriceOrder(0, self.nrVM, combined)

    def sbVMLoad(self, combined=None):
        """
         order by VM Load
        :return:
        """
        self.RestrictionLoadOrder(0, self.nrVM, combined)

    def sbRedundant(self):
        """
        Redundant Constrains - no improvment
        :return:
        """
        for j in range(self.nrVM - 1):
            # VMs with same type have the same price
            if self.sb_redundant_price:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j + 1],
                                        self.PriceProv[j] == self.PriceProv[j + 1]))
            # VMs with same type have the same number of procs
            if self.sb_redundant_processor:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                        self.ProcProv[j] == self.ProcProv[j + 1]))
            # VMs with same type have the same amount of memory
            if self.sb_redundant_memory:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                    self.MemProv[j] == self.MemProv[j + 1]))
            # VMs with same type have the same storage
            if self.sb_redundant_storage:
                self.solver.add(Implies(self.vmType[j] == self.vmType[j+1],
                                    self.StorageProv[j] == self.StorageProv[j + 1]))
            # VMs with the same type should be ordered lex
            if self.sb_equal_vms_type_order_by_components_number:
                self.RestrictionLex(j, [self.vmType[j] == self.vmType[j+1]])
