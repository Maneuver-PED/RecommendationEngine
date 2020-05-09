from maneuverRecomadEngine.exactsolvers.CP_CPLEX_Solver import CPlex_Solver_Parent

from maneuverRecomadEngine.exactsolvers.ManuverSolver_SB import ManuverSolver_SB

class CPlex_Solver_SB_Enc_FilteredOffers(CPlex_Solver_Parent, ManuverSolver_SB):

    def _define_variables(self):
        """
        Creates the variables used in the solver and the constraints on them as well as others (offers encoding,
        usage vector, etc.)
        :return: None
        """
        # VM usage vector vm in {0, 1}, k = 1..M; vm_k = 1 if at least one component is assigned to vm_k.
        self.vm = {j: self.model.binary_var(name="vm{0}".format(j+1)) for j in range(self.nr_vms)}

        # Assignment matrix a_{alpha,k}: 1 if component alpha is on machine k, 0 otherwise
        print("#comp, #VMs ", self.nr_comps, self.nr_vms)
        self.a = {(i, j): self.model.binary_var(name="C{0}_VM{1}".format(i+1, j+1))
                  for i in range(self.nr_comps) for j in range(self.nr_vms)}

        for j in range(self.nr_vms):
            self.model.add_equivalence( self.vm[j], self.model.sum(self.a[i, j] for i in range(self.nr_comps)) >= 1, name="c{0}_vm_allocated".format(j))

        # Variables for offers description
        maxType = len(self.offers_list)
        self.newVmType = {(i, j): self.model.binary_var(name="newType{0}_VM{1}".format(i + 1, j + 1)) for i in range(maxType) for j in range(self.nr_vms)}

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
        cpu_values = {}
        memory_values = {}
        storage_values = {}
        index = 0
        for offer in self.offers_list:
            index += 1
            cpu = offer[1]
            if cpu in cpu_values:
                cpu_values[cpu].append(index)
            else:
                cpu_values[cpu] = [index]

            memory = offer[2]
            if memory in memory_values:
                memory_values[memory].append(index)
            else:
                memory_values[memory] = [index]

            storage = offer[3]
            if storage in storage_values:
                storage_values[storage].append(index)
            else:
                storage_values[storage] = [index]

        for k in range(self.nrVM):
            self.model.add_indicator(self.vm[k], self.model.sum(
                [self.newVmType[index, k] for index in range(len(self.offers_list))]) == 1,
                                     name='no_offer_vm_free')#, active_value=0)

        print("CPLEX cpus:", cpu_values.keys(),cpu_values)
        # print("memory:", memory_values.keys(), memory_values)
        # print("storage:", storage_values.keys(), storage_values)
        self.__encode_carachteristic(cpu_values, 0, [self.problem.componentsList[i].HC for i in range(self.nrComp)], "cpu")
        self.__encode_carachteristic(memory_values, 1, [self.problem.componentsList[i].HM for i in range(self.nrComp)], "mem")
        self.__encode_carachteristic(storage_values, 2, [self.problem.componentsList[i].HS for i in range(self.nrComp)], "sto")

    def __encode_carachteristic(self, characteristic_values, characteristic_index, componentsRequirements, text):
        """
        Helper function in order to encode harware constraints
        """
        print("CPLEX characteristic_values", characteristic_values)
        print([componentsRequirements[i] for i in range(self.nr_comps)])
        for k in range(self.nrVM):
            keys = list(characteristic_values.keys())
            keys.sort(reverse=True)

            #calculate resources sum
            cpus_sum = self.model.integer_var(lb=0, name="{}_sum{}".format(text, k))
            self.model.add_constraint(
                ct=self.model.sum([self.a[i, k] * componentsRequirements[i] for i in range(self.nr_comps)]) == cpus_sum,
                ctname="set_vm_{}{}".format(text, k))
            #to many components on VM (execed max offer)
            key = keys[0]
            offers_applicable = characteristic_values[key].copy()
            cpus_sum_exceed_max = self.model.binary_var("sum_upper_bound_{}__vm{}_{}".format(text, k, key))
            self.model.add_equivalence(cpus_sum_exceed_max, cpus_sum >= key + 1)
            self.model.add_indicator(cpus_sum_exceed_max,
                                     self.model.sum([self.newVmType[index, k] for index in range(len(self.offers_list))]) == 0)

            #in bounds
            ##remove max
            keys.pop(0)
            for key in keys:
                #print(key, "offers_applicable", offers_applicable)
                values = characteristic_values[key]
                _offers = self.model.binary_var("available_offers_{}__vm{}_{}".format(text, k, key))

                self.model.add_equivalence(_offers, self.model.sum([self.newVmType[index-1, k] for index in offers_applicable]) == 1)

                cpus_limit = self.model.binary_var("sum_inner_bounds_{}__vm{}_{}".format(text, k, key))
                self.model.add_equivalence(cpus_limit, cpus_sum >= key + 1)

                #print("tex>=", key+1, offers_applicable)

                self.model.add_indicator(cpus_limit, _offers == 1)
                offers_applicable.extend(values)
                offers_applicable.sort()

            #lower bound
            key = keys.pop()
            #print("lower<=", key, offers_applicable)
            # if key == 1:
            #     cpus_limit_low = self.model.binary_var("sum_lower_bounds_{}__vm{}_{}".format(text, k, key))
            #     self.model.add_equivalence(cpus_limit_low, cpus_sum == 1)
            #     self.model.add_indicator(cpus_limit_low, self.model.sum([self.newVmType[index - 1, k]
            #                                                      for index in offers_applicable]) == 1)
            # else:

            cpus_limit_low = self.model.binary_var("low_sum_lower_bounds_{}_vm{}_{}".format(text, k, key))
            self.model.add_equivalence(cpus_limit_low, cpus_sum <= key)
            cpus_limit_one = self.model.binary_var("one_sum_lower_bounds_{}_vm{}_{}".format(text, k, key))

            self.model.add_equivalence(cpus_limit_one, cpus_sum >= 1)
            self.model.add_if_then(if_ct=cpus_limit_low+cpus_limit_one == 2, then_ct=self.model.sum([self.newVmType[index - 1, k]
                                                                 for index in offers_applicable]) == 1)

        # new encoding
        priceIndex = len(self.offers_list[0]) - 1
        for vm_id in range(self.nrVM):
            index = 0
            for offer in self.offers_list:
                index += 1
                price = offer[priceIndex]
                self.model.add_indicator(self.newVmType[index - 1, vm_id], self.PriceProv[vm_id] == price,
                                         name="price_type_mapping_offer{}_vm{}".format(index-1, vm_id))

    def _same_type(self, var, vm_id):
        self.model.add_indicator(var, sum([self.a[i, vm_id] for i in range(0, self.nr_comps)])
                                 >= sum([self.a[i, vm_id + 1] for i in range(0, self.nr_comps)]))

    def _get_solution_vm_type(self):
        print("get vm type")
        vmType = [0 for i in range(self.nrVM)]
        line = []
        col = 0
        id_type = 0
        for index, var in self.newVmType.items():
            if col == self.problem.nrVM:
                id_type += 1;
                vmType = self.__find_vm_type_id(line, vmType, id_type)
                line = []
                col = 0
            col += 1
            line.append(int(var.solution_value))

        vmType = self.__find_vm_type_id(line, vmType, id_type)
        return vmType

    def __find_vm_type_id(self, line, vm_type, id_type):
        index = 0
        for type in line:
            if type == 1:
                vm_type[index] = id_type
            index += 1
        return vm_type

