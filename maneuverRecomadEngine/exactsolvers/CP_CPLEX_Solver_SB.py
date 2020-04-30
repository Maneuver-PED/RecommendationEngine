from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CPlex_SolverBase
class CPlex_SolverBaseSB(CPlex_SolverBase):
    def _symmetry_breaking(self):
        if self.sb_price:  # PR
            self.sbPrice()
        elif self.sb_price_lex:  # PRLX
            self.sbPrice(True)
        elif self.sb_vm_load:  # L
            self.sbVMLoad()
        elif self.sb_vm_load_lex:  # LLX
            self.sbVMLoad(True)
        elif self.sb_lex:  # LX
            self.sbLex();
        elif self.sb_fix_var:  # FV
            self.sbFixVariables()
        elif self.sb_fix_var_price:  # FVPR
            self.sbFixVariables(criteria="RestrictionPriceOrder")
        elif self.sb_fix_var_vm_load:  # FVL
            self.sbFixVariables(criteria="RestrictionLoadOrder")
        elif self.sb_fix_var_lex:  # FVLX
            self.sbFixVariables(criteria="RestrictionLexOrder")
        elif self.sb_fix_var_price_lex:  # FVPRLX
            self.sbFixVariables(criteria="RestrictionPriceOrder", lex=True)
        elif self.sb_fix_var_vm_load_lex:  # FVLLX
            self.sbFixVariables(criteria="RestrictionLoadOrder", lex=True)
        elif self.sb_lex_col_binary:  # do tests for curiosity
            self.sbBinary()


    def sbBinary(self):
        self.RestrictionLexBinaryNumber()


    def sbFixVariables(self, criteria=None, lex=False):
        """
        Fix values from maximum clique
        """
        vm_id = 0
        # print("Max cliques=", self.problem.max_clique)
        for comp_id in self.problem.max_clique:
            instances = self.problem.componentsList[comp_id].getMinimumPossibleNumberOfInstances(
                self.problem.componentsList)
            start_id = vm_id
            # print("comp=",comp_id," instances:", instances)
            for instance in range(instances):
                self.RestrictionFixComponentOnVM(comp_id, vm_id, 1)
                for conflict_comp_id in self.problem.componentsList[comp_id].conflictComponentsList:
                    self.RestrictionFixComponentOnVM(conflict_comp_id, vm_id, 0)

                vm_id += 1
                self.vm_with_offers[vm_id] = comp_id
                self.vmIds_for_fixedComponents.add(vm_id)
            stop_id = vm_id

            if criteria is not None:
                # print("comp=", comp_id, " interval[", start_id, ", ", stop_id, "]")
                getattr(self, criteria)(start_id, stop_id, lex)
        if criteria is not None:
            print("rest_of interval", " interval[", stop_id, ", ", self.nrVM, "]")
            getattr(self, criteria)(stop_id, self.nrVM, lex)


    def sbLex(self):
        self.RestrictionLexOrder(0, self.nrVM)


    def sbPrice(self, lex=False):
        """
         order by price
        :return:
        """
        # print("sbPrice")
        self.RestrictionPriceOrder(0, self.nrVM, lex)


    def sbVMLoad(self, lex=False):
        """
         order by VM Load
        :return:
        """
        self.RestrictionLoadOrder(0, self.nrVM, lex)


    def sbRedundant(self):
        """
        Redundant Constrains - no improvment
        :return:
        """
        for j in range(self.nrVM - 1):
            var = self.model.binary_var(name="redundanr_type{0}".format(j))
            self._sameType(var, j)

            # VMs with same type have the same price
            if self.sb_redundant_price:
                self.model.add_indicator(var,
                                         self.PriceProv[j] == self.PriceProv[j + 1], name="sb_redundant_price")

            if self.sb_redundant_processor:
                self.model.add_indicator(var,
                                         self.ProcProv[j] == self.ProcProv[j + 1], name="sb_redundant_procesor")
            # VMs with same type have the same amount of memory
            if self.sb_redundant_memory:
                self.model.add_indicator(var,
                                         self.MemProv[j] >= self.MemProv[j + 1], name="sb_redundant_memory")

            # VMs with same type have the same storage
            if self.sb_redundant_storage:
                self.model.add_indicator(var,
                                         self.StorageProv[j] == self.StorageProv[j + 1], name="sb_redundant_storage")

    def _sameType(self, var, vm_id):
        """
        Variable to be taken into account by CPLEX
        :param var:  a CPLEX variable
        :param vm_id: The index of VM that has to be equal with the next one
        :return:
        """
        print("Provide implementation for specific encoding")