
class RestrictionFixComponentOnVM:
    """
    Restriction that fixes a component on a VM
    """
    def __init__(self, comp_id, vm_id,  problem, value = 1):
        self.comp_id = comp_id
        self.vm_id = vm_id
        self.value = value

        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionFixComponentOnVM(self.comp_id, self.vm_id, self.value)

    def __repr__(self):
        return "RestrictionFixComponentOnVM: Component with ID {} is deployed on VM with ID {}".format(
            self.comp_id, self.vm_id)

    def eval(self, solutionMatrix):
        return 1

class RestrictionPriceOrder:
    """
    Restriction that orders VM price
    """

    def __init__(self, strat_vm_id, end_vm_id, problem):
        self.start_vm_id = strat_vm_id
        self.end_vm_id = end_vm_id

        problem.logger.info(self)

    def generateRestrictions(self, solver):
        solver.RestrictionPriceOrder(self.start_vm_id, self.end_vm_id)

    def __repr__(self):
        return "RestrictionPriceOrder: start VM ID {} - end VM ID {}".format(
            self.start_vm_id, self.end_vm_id)

    def eval(self, solutionMatrix):
        return 1