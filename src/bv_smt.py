import os
import sys
from data_structs import Op
from data_structs import Node
from data_structs import Result
from helper import cnf_to_dimacs, tokenize, paran_split, convert_to_op
from helper import satisfied, run_cadical

def preprocess(input_smt):
    '''Removes whitespace, comments and tokenizes input'''
    smt = []
    smt_tokens = []
    for line in input_smt:
        text = line.strip()
        if len(text) == 0: 
            continue
        if text[0] == ";":
            continue
        smt.append(text)
        smt_tokens.append(tokenize(text))  
    return (smt,smt_tokens)

def create_node(formula, bool_skeleton=False, optimization=False):
    '''Recursively creates nodes and sub-nodes from a formula'''
    orig_formula = formula
    
    if orig_formula in Node.node_dict.keys():
        return Node.node_dict[orig_formula]
    
    if formula[0] == "(":
        formula = formula[1:]
    if formula[-1] == ")":
        formula = formula[:-1]

    formula = formula.strip()
    
    tokens = paran_split(formula)
    
    if tokens[0].isdigit() and len(tokens) == 1:
        node = Node(op=Op.CONST, id=orig_formula, \
                 bool_skeleton=bool_skeleton)
        node.term1 = int(tokens[0])
        node.size  = -1
        return node

    if tokens[0].isdigit() and tokens[1].isdigit():
        node = Node(op=Op.EXTRACT_IDX, id=orig_formula, \
                       bool_skeleton=bool_skeleton)
        
        node.term1 = int(tokens[0])
        node.term2 = int(tokens[1])
        node.size = -1
        node.id = "EXTRACT_IDX" + str(Node.prop_var_count)
        return node
    
    if tokens[0] == "_":
        if "bv" in tokens[1]:
            node = Node(op=Op.FIXED_CONST, term1=None, term2=None, \
                         size=int(tokens[2]), id=orig_formula,  \
                         bool_skeleton=bool_skeleton)

            node.term1 = tokens[1]
            node.bool_arr = Node.get_prop_variables(node.size)
            node.generate_constraints()
            return node

    node = Node(id=orig_formula)
    node.op = convert_to_op(tokens[0])
    
    node.bool_skeleton=bool_skeleton
    if node.op in [Op.LOG_AND, Op.LOG_NOT, Op.LOG_OR]:
        node.bool_skeleton = True
    
    node.term1 = create_node(tokens[1], node.bool_skeleton,\
                              optimization=optimization)
    
    if node.op not in [Op.NOT, Op.LOG_NOT]:
        node.term2 = create_node(tokens[2], node.bool_skeleton,\
                                  optimization=optimization)
    if node.op == Op.ITE:
        node.term3 = create_node(tokens[3], node.bool_skeleton,\
                                  optimization=optimization)

    if node.op in [Op.EQUALS, Op.DISTINCT, Op.ULT, Op.ULE, Op.SLE, Op.SLT]:
        node.size = 1
    elif node.op == Op.CONCAT:
        node.size = node.term1.size + node.term2.size
    elif node.op == Op.EXTRACT:
        node.size = node.term1.term1 - node.term1.term2 + 1
    elif node.op == Op.ITE:
        node.size = node.term2.size
    elif node.op == Op.SIGN_EXT:
        node.size = node.term1.term1 + node.term2.size
    else:
        node.size = node.term1.size
    
    node.bool_arr = Node.get_prop_variables(node.size)
    
    node.generate_constraints(optimization & (node.op == Op.MUL))
    return node


def process(smt_form, smt_tokens, optimization=False):
    '''Create nodes for each formula and generate constraints'''
    assert len(smt_form) == len(smt_tokens)

    for i in range(len(smt_form)):
        formula = smt_form[i]
        tokens  = smt_tokens[i]
        paran_tokens = paran_split(formula[1:-1])

        if paran_tokens[0] == "set_logic":
            if paran_tokens[1] != "QF_BV":
                sys.exit("Only Quantifier-free Bit Vector logic supported")
        
        if paran_tokens[0] in ["declare-const", "declare-fun"]:
            node = Node(op=Op.CONST, term1=None, term2=None, size=1,\
                 id=paran_tokens[1])
            term_length = int(tokens[-1])
            node.bool_arr = Node.get_prop_variables(size=term_length)
            node.size = term_length
            node.generate_constraints()
        
        if paran_tokens[0] == "assert":
            formula = paran_tokens[1]
            while "_ extract" in formula:
                s_idx = formula.find("_ extract")
                e_idx = s_idx + len("_ extract") + 1
                formula = formula[:s_idx-1] + "extract" + " (" + formula[e_idx:]
            while "_ sign_extend" in formula:
                s_idx = formula.find("_ sign_extend")
                e_idx = s_idx + len("_ sign_extend") + 1
                formula = formula[:s_idx-1] + "sign_extend " + "("\
                                   + formula[e_idx:]
            node = create_node(formula, optimization=optimization)

def main():

    if len(sys.argv) != 3:
        print("Usage: python3 run.py input.smt2 incremental_optimization")
        sys.exit(-1)
    
    input_filename       = sys.argv[1]
    turn_on_optimization = int(sys.argv[2])
    output_file          = "output.dimacs"

    if turn_on_optimization == 1:
        opt_flag = True
    else:
        opt_flag = False
    
    input_smt = []
    with open(input_filename, "r") as f:
        input_smt = f.readlines()

    smt_form, smt_tokens = preprocess(input_smt)
    
    process(smt_form, smt_tokens, optimization=opt_flag)
    
    var_dict = cnf_to_dimacs(Node.constraints, output_file)
    
    result, assignment = run_cadical(output_file)
    
    if result == Result.UNKNOWN:
        sys.exit("Sat Solver returned Unknown result")

    MAGIC_NUMBER=5
    while result == Result.SAT:
        
        satisfied_flag = True
        for constraint in Node.exp_constraints:
            if not satisfied(assignment, constraint, var_dict):
                satisfied_flag = False
                break

        if satisfied_flag == True:
            print("Result: {}".format(Result.SAT))
            sys.exit()

        for _ in range(MAGIC_NUMBER):
            try:
                constraint = Node.exp_constraints.pop()
                Node.constraints.append(constraint)
            except IndexError:
                pass
        
        var_dict            = cnf_to_dimacs(Node.constraints, output_file)
        result, assignment = run_cadical(output_file)
        if not Node.exp_constraints:
            break
    
    print("Result: {}".format(result))

if __name__ == "__main__":
    main()
