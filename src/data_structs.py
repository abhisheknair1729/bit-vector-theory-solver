from enum import Enum
import sys

class Op(Enum):
    CONST = 0
    AND = 1
    OR = 2
    NOT = 3
    ADD = 4
    MUL = 5
    EQUALS = 6
    CONCAT = 7
    EXTRACT = 8
    EXTRACT_IDX = 9
    SUB = 10
    LOG_NOT = 11
    LOG_AND = 12
    LOG_OR = 13
    FIXED_CONST = 14
    IMPLY = 15
    ITE = 16
    DISTINCT = 17
    SLE = 18
    ULE = 19
    SLT = 20
    ULT = 21
    XOR = 22
    SIGN_EXT = 23

class Result(Enum):
    UNSAT = 0
    SAT = 1
    UNKNOWN = 2

class Node:
    node_dict = {}
    constraints = []
    exp_constraints = []
    prop_var_count = 0 #global prop variable count
    
    def get_prop_variables(size):
        ret_val = ["prop_" + str(i) for i in range(Node.prop_var_count, Node.prop_var_count + size)]
        Node.prop_var_count += size
        return ret_val

    def __init__(self, op=Op.CONST, term1=None, term2=None, size=0, id=None,\
                     bool_skeleton=False):
        self.op = op
        self.term1 = term1
        self.term2 = term2
        self.term3 = None
        self.size = size
        self.bool_arr = None
        self.id = id
        self.bool_skeleton=bool_skeleton
        Node.node_dict[id] = self
        

    def generate_constraints(self, optimization=False):
        '''Generates the constraints for this term'''
        LOG_ON = False

        if LOG_ON:
            print("Constraint: " + self.id)
            print("Operation:" + str(self.op))
            print("Bool Variables:")
            print(self.bool_arr)
        
        if self.op == Op.CONST:
            pass
        
        elif self.op == Op.ITE:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            term3_var = self.term3.bool_arr
            
            assert len(term1_var) == 1

            for i in range(len(term2_var)):
                Node.constraints.append("not {}, {}, not  \
                         {}".format(term1_var[0], term2_var[i], self.bool_arr[i]))
                Node.constraints.append("{}, {}, not {}".format(\
                               term1_var[0], term3_var[i], self.bool_arr[i]))
                Node.constraints.append("not {}, not {}, {}".format(\
                              term1_var[0], term2_var[i], self.bool_arr[i]))
                Node.constraints.append("{}, not {}, {}".format(\
                              term1_var[0], term3_var[i], self.bool_arr[i]))
        
        elif self.op == Op.SIGN_EXT: 
            assert len(self.bool_arr) == len(self.term2.bool_arr) + self.term1.term1

            for i in range(len(self.bool_arr)):
                if i<len(self.term2.bool_arr):
                    Node.constraints.append("{}, not\
                        {}".format(self.bool_arr[i], self.term2.bool_arr[i]))
                    Node.constraints.append("not {}, {}".format(\
                        self.bool_arr[i], self.term2.bool_arr[i]))
                else:
                    Node.constraints.append("{}, not\
                        {}".format(self.bool_arr[i], self.term2.bool_arr[-1]))
                    Node.constraints.append("not {}, {}".format(\
                        self.bool_arr[i], self.term2.bool_arr[-1]))

        elif self.op == Op.SLE:
            node = Node(id="SLE_SUB")
            node.term2 = self.term1
            node.term1 = self.term2
            bool_var   = self.bool_arr[0]
            node.op    = Op.SUB
            node.bool_arr \
                  = Node.get_prop_variables(len(self.term1.bool_arr))
            node.size = len(self.term1.bool_arr)
            node.generate_constraints()
            Node.constraints.append("{}, {}, not {}, {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, {}, {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("{}, not {}, not {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          bool_var))
            Node.constraints.append("{}, {}, not {}".format(\
                          self.term1.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, {}, not {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          bool_var))
            Node.constraints.append("{}, {}, not {}".format(\
                          self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, not {}".format(\
                          self.term1.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, not {}".format(\
                          self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            
            if not self.bool_skeleton:
                Node.constraints.append("not {}".format(bool_var))


        elif self.op == Op.SLT:
            node = Node(id="SLT_SUB")
            node.term1 = self.term1
            node.term2 = self.term2
            bool_var   = self.bool_arr[0]
            node.op    = Op.SUB
            node.bool_arr \
                  = Node.get_prop_variables(len(self.term1.bool_arr))
            node.size = len(self.term1.bool_arr)
            node.generate_constraints()
            Node.constraints.append("{}, {}, not {}, {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, {}, {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("{}, not {}, not {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          bool_var))
            Node.constraints.append("{}, {}, not {}".format(\
                          self.term1.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, {}, not {}".format(\
                          self.term1.bool_arr[-1], self.term2.bool_arr[-1],\
                          bool_var))
            Node.constraints.append("{}, {}, not {}".format(\
                          self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, not {}".format(\
                          self.term1.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            Node.constraints.append("not {}, not {}, not {}".format(\
                          self.term2.bool_arr[-1],\
                          node.term3.bool_arr[-1], bool_var))
            
            if not self.bool_skeleton:
                Node.constraints.append("{}".format(bool_var))

        elif self.op == Op.ULE:
            node = Node(id="ULE_SUB")
            node.term1 = self.term2
            node.term2 = self.term1
            bool_var   = self.bool_arr[0]
            node.op = Op.SUB
            node.bool_arr \
                  = Node.get_prop_variables(len(self.term1.bool_arr))
            node.size = len(self.term1.bool_arr)
            node.generate_constraints()
            Node.constraints.append("{}, {}".format(node.term3.bool_arr[-1],\
                                      bool_var))
            Node.constraints.append("not {}, not {}".format(\
                                      node.term3.bool_arr[-1], bool_var))

            if not self.bool_skeleton:
                Node.constraints.append("not {}".format(bool_var))


        elif self.op == Op.ULT:
            node = Node(id="ULT_SUB")
            node.term1 = self.term1
            node.term2 = self.term2
            bool_var   = self.bool_arr[0]
            node.op = Op.SUB
            node.bool_arr \
                  = Node.get_prop_variables(len(self.term1.bool_arr))
            node.size = len(self.term1.bool_arr)
            node.generate_constraints()
            Node.constraints.append("{}, {}".format(node.term3.bool_arr[-1],\
                                      bool_var))
            Node.constraints.append("not {}, not {}".format(\
                                      node.term3.bool_arr[-1], bool_var))

            if not self.bool_skeleton:
                Node.constraints.append("{}".format(bool_var))


        elif self.op == Op.FIXED_CONST:
            term1_var = self.term1
            if term1_var == "bv0":
                for i in range(len(self.bool_arr)):
                    Node.constraints.append("not {}".format(self.bool_arr[i]))
                    if LOG_ON:
                        print("not {}".format(self.bool_arr[i]))
            elif term1_var == "bv1":
                for i in range(len(self.bool_arr)):
                    Node.constraints.append("{}".format(self.bool_arr[i]))
                    if LOG_ON:
                        print("{}".format(self.bool_arr[i]))
            else:
                term1_num = int(term1_var[2:])
                term1_str = "{0:0" + str(len(self.bool_arr)) + "b}"
                term1_bin = term1_str.format(term1_num)
                for i in range(len(self.bool_arr)):
                    if term1_bin[i] == "1":
                        Node.constraints.append("{}".format(self.bool_arr[i]))
                    if term1_bin[i] == "0":
                        Node.constraints.append("not {}".format(self.bool_arr[i]))

        elif self.op == Op.NOT:
            term1_var = self.term1.bool_arr
            assert len(term1_var) == len(self.bool_arr)
            for i in range(len(term1_var)):
                Node.constraints.append("{}, {}".format(term1_var[i], self.bool_arr[i]))
                Node.constraints.append("not {}, not {}".format(term1_var[i], self.bool_arr[i]))
                if LOG_ON:
                    print("{}, {}".format(term1_var[i], self.bool_arr[i]))
                    print("not {}, not {}".format(term1_var[i], self.bool_arr[i]))
                
        elif self.op == Op.AND:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            for i in range(self.size):
                Node.constraints.append("{}, not {}, not {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, {}".format(self.bool_arr[i], term1_var[i]))
                Node.constraints.append("not {}, {}".format(self.bool_arr[i], term2_var[i]))
                if LOG_ON:
                    print("{}, not {}, not {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                    print("not {}, {}".format(self.bool_arr[i], term1_var[i]))
                    print("not {}, {}".format(self.bool_arr[i], term2_var[i]))

        elif self.op == Op.XOR:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            for i in range(self.size):
                Node.constraints.append("not {}, not {}, not {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, {}, {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, {}, not {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, not {}, {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))

        elif self.op == Op.OR:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            for i in range(self.size):
                Node.constraints.append("not {}, {}, {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, not {}".format(self.bool_arr[i], term1_var[i]))
                Node.constraints.append("{}, not {}".format(self.bool_arr[i], term2_var[i]))
                if LOG_ON:
                    print("not {}, {}, {}".format(self.bool_arr[i], term1_var[i], term2_var[i]))
                    print("{}, not {}".format(self.bool_arr[i], term1_var[i]))
                    print("{}, not {}".format(self.bool_arr[i], term2_var[i]))
       

        elif self.op == Op.DISTINCT:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            bool_var = self.bool_arr[0]
            assert len(self.bool_arr) == 1
            new_bool_vars = Node.get_prop_variables(len(term1_var))
            if LOG_ON:
                print("New Variables:")
                print(new_bool_vars)
            for i in range(len(new_bool_vars)):
                Node.constraints.append("not {}, {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, not {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, not {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, {}".format(bool_var, new_bool_vars[i]))
            
            constraint = "{}".format(bool_var)
            for c in new_bool_vars:
                constraint = constraint + ", not {}".format(c)
            
            Node.constraints.append(constraint)
            if not self.bool_skeleton:
                Node.constraints.append("{}".format(bool_var))


        elif self.op == Op.EQUALS:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            bool_var = self.bool_arr[0]
            assert len(self.bool_arr) == 1
            new_bool_vars = Node.get_prop_variables(len(term1_var))
            if LOG_ON:
                print("New Variables:")
                print(new_bool_vars)
            for i in range(len(new_bool_vars)):
                Node.constraints.append("not {}, {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, not {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("{}, not {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                Node.constraints.append("not {}, {}".format(bool_var, new_bool_vars[i]))
                if LOG_ON:
                    print("not {}, {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                    print("not {}, not {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                    print("{}, {}, {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                    print("{}, not {}, not {}".format(new_bool_vars[i], term1_var[i], term2_var[i]))
                    print("not {}, {}".format(bool_var, new_bool_vars[i]))
            constraint = "{}".format(bool_var)
            for c in new_bool_vars:
                constraint = constraint + ", not {}".format(c)
            
            if LOG_ON:
                print(constraint)
                if not self.bool_skeleton:
                    print("{}".format(bool_var))
            
            Node.constraints.append(constraint)
            if not self.bool_skeleton:
                Node.constraints.append("{}".format(bool_var))

        elif self.op == Op.CONCAT:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            m = len(term2_var)
            assert len(self.bool_arr) == len(term1_var) + len(term2_var)
            constraints = Node.exp_constraints if optimization else\
                            Node.constraints
            for i in range(len(self.bool_arr)):
                constraints.append("{}, not {}".format(self.bool_arr[i], term2_var[i] if i<m else term1_var[i-m]))
                constraints.append("not {}, {}".format(self.bool_arr[i], term2_var[i] if i<m else term1_var[i-m]))
                if LOG_ON:
                    print("{}, not {}".format(self.bool_arr[i], term2_var[i] if i<m else term1_var[i-m]))
                    print("not {}, {}".format(self.bool_arr[i], term2_var[i] if i<m else term1_var[i-m]))
            
        elif self.op == Op.EXTRACT:
            term1 = self.term1
            assert term1.op == Op.EXTRACT_IDX
            idx_i = term1.term1
            idx_j = term1.term2
            if LOG_ON:
                print("Extract Idx: [{}, {}]".format(idx_j, idx_i))
            term2_var = self.term2.bool_arr
            
            constraints = Node.exp_constraints if optimization else\
                              Node.constraints
            
            for i in range(idx_i - idx_j + 1):
                constraints.append("{}, not {}".format(self.bool_arr[i], term2_var[idx_j + i]))
                constraints.append("not {}, {}".format(self.bool_arr[i], term2_var[idx_j + i]))
                if LOG_ON:
                    print("{}, not {}".format(self.bool_arr[i], term2_var[idx_j + i]))
                    print("not {}, {}".format(self.bool_arr[i], term2_var[idx_j + i]))

        elif self.op == Op.ADD:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            carry_variables = Node.get_prop_variables(size=len(term1_var)+1)
            if LOG_ON:
                print("Carry Variables:")
                print(carry_variables)
            constraints = Node.exp_constraints if optimization else\
                              Node.constraints

            constraints.append("not {}".format(carry_variables[0]))
            for i in range(len(term1_var)):
                constraints.append("{}, {}, {}, not {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, not {}, {}, not {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, {}, not {}, not {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, not {}, not {}, not {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, not {}, not {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, {}, {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, not {}, {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, {}, not {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], self.bool_arr[i] ))
                # constraints on carry out
                constraints.append("{}, {}, not {}".format(term1_var[i], term2_var[i], carry_variables[i+1]))
                constraints.append("{}, {}, not {}".format(term1_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("{}, {}, not {}".format(term2_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, not {}, not {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, not {}, {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, {}, not {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("{}, not {}, not {}, {}".format(term1_var[i], term2_var[i], carry_variables[i], carry_variables[i+1]))

        elif self.op == Op.SUB:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            carry_variables = Node.get_prop_variables(size=len(term1_var)+1)
            self.term3 = Node()
            self.term3.bool_arr = carry_variables
            complement_vars = Node.get_prop_variables(size=len(term2_var))

            constraints = Node.exp_constraints if optimization else \
                           Node.constraints
            constraints.append("{}".format(carry_variables[0]))
            for i in range(len(term2_var)):
                constraints.append("{}, {}".format(complement_vars[i], term2_var[i]))
                constraints.append("not {}, not {}".format(complement_vars[i], term2_var[i]))

            for i in range(len(term1_var)):
                constraints.append("{}, {}, {}, not {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, not {}, {}, not {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, {}, not {}, not {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, not {}, not {}, not {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, not {}, not {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("not {}, {}, {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, not {}, {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                constraints.append("{}, {}, not {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], self.bool_arr[i] ))
                # constraints on carry out
                constraints.append("{}, {}, not {}".format(term1_var[i], complement_vars[i], carry_variables[i+1]))
                constraints.append("{}, {}, not {}".format(term1_var[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("{}, {}, not {}".format(complement_vars[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, not {}, not {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, not {}, {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("not {}, {}, not {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], carry_variables[i+1]))
                constraints.append("{}, not {}, not {}, {}".format(term1_var[i], complement_vars[i], carry_variables[i], carry_variables[i+1]))

        elif self.op == Op.MUL:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            assert len(self.bool_arr) == len(term1_var)
            bitwise_products = []
            partial_sums = []

            for i in range(len(term1_var)): #m arrays of size m 
                bitwise_products.append(Node.get_prop_variables(len(term1_var)))
            
            for i in range(len(term1_var)):
                partial_sums.append(Node.get_prop_variables(len(term1_var)))
            partial_sums.append(self.bool_arr)
            
            constraints = Node.exp_constraints if optimization else \
                           Node.constraints

            for i in range(len(term2_var)):
                constraints.append("not {}".format(partial_sums[0][i]))
                for k in range(i):
                    constraints.append("not {}".format(bitwise_products[i][k]))
                for k in range(i, len(term1_var)):
                    constraints.append("{}, not {}, not {}".format(bitwise_products[i][k], term1_var[k-i], term2_var[i]))
                    constraints.append("{}, not {}".format(term1_var[k-i], bitwise_products[i][k]))
                    constraints.append("{}, not {}".format(term2_var[i], bitwise_products[i][k]))
            
            for i in range(len(term2_var)):
                n = Node(op=Op.ADD, id="intermediate_add_"+str(i))
                n.term1 = Node()
                n.term2 = Node()
                n.term1.bool_arr = bitwise_products[i]
                n.term2.bool_arr = partial_sums[i]
                n.bool_arr = partial_sums[i+1]
                n.generate_constraints(optimization)

        elif self.op == Op.LOG_NOT:
            term1_var = self.term1.bool_arr
            assert term1_var != None
            assert len(term1_var) == 1
            Node.constraints.append("not {}".format(term1_var[0]))
            Node.constraints.append("{}, {}".format(term1_var[0], self.bool_arr[0]))
            Node.constraints.append("not {}, not {}".format(term1_var[0], self.bool_arr[0]))
            if LOG_ON:
                print("not {}".format(term1_var[0]))
                print("{}, {}".format(term1_var[0], self.bool_arr[0]))
                print("not {}, not {}".format(term1_var[0], self.bool_arr[0]))
        
        elif self.op == Op.LOG_AND:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert len(term1_var) == len(term2_var)
            assert term1_var != None
            assert term2_var != None
            Node.constraints.append("{}".format(term1_var[0]))
            Node.constraints.append("{}".format(term2_var[0]))
            Node.constraints.append("not {}, not {}, {}".format(term1_var[0], term2_var[0], self.bool_arr[0]))
            Node.constraints.append("{}, not {}".format(term1_var[0], self.bool_arr[0]))
            Node.constraints.append("{}, not {}".format(term2_var[0], self.bool_arr[0]))
        
        elif self.op == Op.LOG_OR:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert term1_var != None
            assert term2_var != None
            assert len(term1_var) == len(term2_var)
            Node.constraints.append("{}, {}".format(term1_var[0], term2_var[0]))
            Node.constraints.append("not {}, {}".format(term1_var[0], self.bool_arr[0]))
            Node.constraints.append("not {}, {}".format(term2_var[0], self.bool_arr[0]))
            Node.constraints.append("{}, {}, not {}".format(term1_var[0], term2_var[0], self.bool_arr[0]))
        
        elif self.op == Op.IMPLY:
            term1_var = self.term1.bool_arr
            term2_var = self.term2.bool_arr
            assert term1_var != None
            assert term2_var != None
            assert len(term1_var) == len(term2_var)
            Node.constraints.append("{}, {}".format(term1_var[0], self.bool_arr[0]))
            Node.constraints.append("not {}, {}".format(term2_var[0], self.bool_arr[0]))
            Node.constraints.append("not {}, {}, not {}".format(term1_var[0], term2_var[0], self.bool_arr[0]))


        else:
            sys.exit("Constraints Not supported")
