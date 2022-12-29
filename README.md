# bit-vector-theory-solver

This repository contains code for final project of CS257: Introduction to Automated Reasoning at Stanford University. I have implemented 
an SMT solver for the Quantifier-Free fragment of the Theory of Bit Vectors. 

Usage (from src directory): python3 bv_smt.py ../tests/<test-path> optimization_flag (0 or 1)

Enabling the optimization_flag causes the constraints for expensive operations such as multiplication to not be generated initially. If the decision procedure can prove unsatisfiability, then those constraints are never used resulting in significant speedups.

Note: The cadical binary file used was compiled for the Myth cluster at Stanford. You may need to recompile it if you use a different system.
