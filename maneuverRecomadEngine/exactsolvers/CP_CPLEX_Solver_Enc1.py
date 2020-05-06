from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CPlex_Solver_Parent
from maneuverRecomadEngine.exactsolvers.ManuverSolver_SB import ManuverSolver_SB

class CPlex_Solver_SB_Enc1(CPlex_Solver_Parent, ManuverSolver_SB):

    def _define_variables(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding,
        usage vector, etc.)
        :return: None
        """

        print("OVERLOADED METHOD ................................")
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        self.vm = {j: self.model.binary_var(name="vm{0}".format(j+1)) for j in range(self.nr_vms)}

        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        print("#comp, #VMs ", self.nr_comps, self.nr_vms)
        self.a = {(i, j): self.model.binary_var(name="C{0}_VM{1}".format(i+1, j+1))
                  for i in range(self.nr_comps) for j in range(self.nr_vms)}

        for j in range(self.nr_vms):
            self.model.add_equivalence( self.vm[j], self.model.sum(self.a[i, j] for i in range(self.nr_comps)) >= 1, name="c{0}_vm_allocated".format(j))

        #Variables for offers description
        maxType = len(self.offers_list)
        self.vmType = {(j): self.model.integer_var(lb=0, ub=maxType, name="vmType{0}".format(j + 1))
                       for j in range(self.nr_vms)}

        minProc = min(self.offers_list[t][1] for t in range(len(self.offers_list)))
        maxProc = max(self.offers_list[t][1] for t in range(len(self.offers_list)))
        self.ProcProv = {(j): self.model.integer_var(lb=minProc, ub=maxProc, name="ProcProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        minMem = min(self.offers_list[t][2] for t in range(len(self.offers_list)))
        maxMem = max(self.offers_list[t][2] for t in range(len(self.offers_list)))
        self.MemProv = {(j): self.model.integer_var(lb=minMem, ub=maxMem, name="MemProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        minSto = min(self.offers_list[t][3] for t in range(len(self.offers_list)))
        maxSto = max(self.offers_list[t][3] for t in range(len(self.offers_list)))
        self.StorageProv = {(j): self.model.integer_var(lb=minSto, ub=maxSto, name="StorageProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        maxPrice = max(self.offers_list[t][len(self.offers_list[0]) - 1] for t in range(len(self.offers_list)))
        self.PriceProv = {(j): self.model.integer_var(lb=0, ub=maxPrice, name="PriceProv{0}".format(j + 1)) for j in range(self.nr_vms)}

        # If a machine is not leased then its price is 0
        for j in range(self.nr_vms):
            self.model.add_indicator(self.vm[j], self.PriceProv[j] == 0, active_value=0, name="c{0}_vm_free_price_0".format(j))

    def _hardware_and_offers_restrictionns(self, scaleFactor):
        """
        Describes the hardware requirements for each component
        :param componentsRequirements: list of components requirements as given by the user
        :return: None
        """
        for k in range(self.nr_vms):
            self.model.add_constraint(ct=self.model.sum(self.a[i, k] * (self.problem.componentsList[i].HC)
                                    for i in range(self.nr_comps)) <= self.ProcProv[k], ctname="c_hard_cpu")
            self.model.add_constraint(ct=self.model.sum(self.a[i, k] * (self.problem.componentsList[i].HM)
                                    for i in range(self.nr_comps)) <= self.MemProv[k], ctname="c_hard_mem")
            self.model.add_constraint(ct=self.model.sum(self.a[i, k] * (self.problem.componentsList[i].HS)
                                        for i in range(self.nr_comps)) <= self.StorageProv[k], ctname="c_hard_storage")

        print("offers_list: ", len(self.offers_list), " vmsno=", self.nr_vms, len(self.offers_list)*self.nr_vms)
        index_constraint = 0
        for vm_id in range(self.nr_vms):
            cnt = 0
            for offer in self.offers_list:
                cnt += 1
                index_constraint += 1

                var = self.model.binary_var(name="aux_hard{0}".format(index_constraint))
                ct = self.model.add_equivalence(var, self.vmType[vm_id] == cnt)

                self.model.add_indicator(var,
                                         self.PriceProv[vm_id] == int(offer[len(self.offers_list[0]) - 1]),
                                         active_value=1, name="c_order_vm_price".format(vm_id))
                self.model.add_indicator(var, (self.ProcProv[vm_id] == int(offer[1])),
                                         name="c_order_vm_cpu".format(vm_id))
                self.model.add_indicator(var, (self.MemProv[vm_id] == int(offer[2])),
                                         name="c_order_vm_memory".format(vm_id))
                self.model.add_indicator(var, (self.StorageProv[vm_id] == int(offer[3])),
                                         name="c_order_vm_storage".format(vm_id))

            lst = [(self.vmType[vm_id] == offer) for offer in range(1, len(self.offers_list)+1)]
            ct = self.model.add_indicator(self.vm[vm_id], self.vmType[vm_id] >= 1)


    def _same_type(self, var, vm_id):
        self.model.add_equivalence(var, self.vmType[vm_id] == self.vmType[vm_id + 1])

    def _get_solution_vm_type(self):
        vm_types = []
        for index, var in self.vmType.items():
            print(var.solution_value, end=" ")
            vm_types.append(var.solution_value)
        return vm_types