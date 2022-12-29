import sys
from data_structs import Op
import os
from data_structs import Result

def cnf_to_dimacs(cnf:list, dimacs_file:str):
    num_clauses = len(cnf)
    lit_dict = {}
    lit_count = 0
    for i in range(num_clauses):
        clause = cnf[i].split(",")
        for lit in clause:
            lit = lit.strip()
            if "not" in lit:
                lit = lit.split()[1]
            
            if lit not in lit_dict.keys():
                lit_dict[lit] = lit_count
                lit_count += 1
    
    with open(dimacs_file, "w") as f:
        f.write("p cnf {} {}\n".format(lit_count, num_clauses))
        for clause in cnf:
            clause = clause.split(",")
            for lit in clause:
                lit = lit.strip()
                if "not" in lit:
                    lit = lit.split()[1]
                    lit_num = lit_dict[lit] + 1
                    f.write("-{} ".format(str(lit_num)))
                else:    
                    lit_num = lit_dict[lit] + 1 
                    f.write("{} ".format(str(lit_num)))
            f.write("0\n")
    
    return lit_dict


def tokenize(line):
    '''Breaks up line into individual words'''
    import re
    temp_tokens = re.split(r'[\s()]', line)
    return [c for c in temp_tokens if c != '']

def paran_split(formula):
    '''Splits up the formula based on parantheses'''
    lparan = 0
    rparan = 0
    last_i = 0
    tokens = []
    for i in range(len(formula)):
        c = formula[i]
        if c == "(":
            lparan += 1
        elif c == ")":
            rparan += 1
        elif c == " ":
            if lparan == rparan:
                tokens.append(formula[last_i:i])
                last_i = i+1
    tokens.append(formula[last_i:i+1])
    return tokens

def convert_to_op(op_str):
    '''Converts SMT2 standard keywords into Enum type'''
    if op_str == "bvand":
        return Op.AND
    if op_str == "bvor":
        return Op.OR
    if op_str == "bvadd":
        return Op.ADD
    if op_str == "bvnot":
        return Op.NOT
    if op_str == "bvmul":
        return Op.MUL
    if op_str == "and":
        return Op.LOG_AND
    if op_str == "or":
        return Op.LOG_OR
    if op_str == "=":
        return Op.EQUALS
    if op_str == "not":
        return Op.LOG_NOT
    if op_str == "concat":
        return Op.CONCAT
    if op_str == "extract":
        return Op.EXTRACT
    if op_str == "bvsub":
        return Op.SUB
    if op_str == "=>":
        return Op.IMPLY
    if op_str == "ite":
        return Op.ITE
    if op_str == "distinct":
        return Op.DISTINCT
    if op_str == "bvslt":
        return Op.SLT
    if op_str == "bvult":
        return Op.ULT
    if op_str == "bvsle":
        return Op.SLE
    if op_str == "bvule":
        return Op.ULE
    if op_str == "bvxor":
        return Op.XOR
    if op_str == "sign_extend":
        return Op.SIGN_EXT

    sys.exit("Operation not supported!")

def run_cadical(output_file):
    os.system("./cadical {} > output.result".format(output_file))
    with open("output.result", "r") as f:
        result_data = f.read()
        if "UNSATISFIABLE" in result_data:
            return (Result.UNSAT, None)
        elif "SATISFIABLE" in result_data:
            
            f.seek(0)
            result_lines = f.readlines()
            assignment = {}
            for line in result_lines:
                if line[0] == "v":
                    lits = line.split()[1:]
                    for lit in lits:
                        l = int(lit)
                        if l>0:
                            assignment[l] = True
                        elif l<0:
                            assignment[-l] = False
                        elif l==0:
                            break
            return (Result.SAT, assignment)
        elif "UNKNOWN" in result_data:
            return (Result.UNKNOWN, None)

def satisfied(assignment, constraint, var_dict):
    lits = constraint.split(",")
    for lit in lits:
        flag = True
        if "not" in lit:
            lit = lit.split()[1]
            flag = False
        if lit in var_dict.keys():
            lit_num = var_dict[lit]
            
            if assignment[lit_num] == flag:
                return True
        else:
            # if current assignment doesn't assign any truth value to a variable
            # assume that variable is not satisfied
            continue
  
    return False


