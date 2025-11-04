#!/usr/bin/env python3
"""
BFO Axiom Validation using Z3 SMT Solver
Validates BFO Axiom 21: Process definition
"""

try:
    from z3 import *
    print("Z3 imported successfully!")
    
    def validate_bfo_axiom_21():
        """Validate: Process iff (Occurrent ∧ has proper temporal parts ∧ depends on material entity)"""
        
        print("Setting up Z3 validation for BFO Axiom 21...")
        
        # Declare sorts
        Entity = DeclareSort('Entity')
        Time = DeclareSort('Time')
        
        # Declare predicates
        Process = Function('Process', Entity, BoolSort())
        Occurrent = Function('Occurrent', Entity, BoolSort())
        MaterialEntity = Function('MaterialEntity', Entity, BoolSort())
        properTemporalPartOf = Function('properTemporalPartOf', Entity, Entity, BoolSort())
        specificallyDependsOnAt = Function('specificallyDependsOnAt', Entity, Entity, Time, BoolSort())
        existsAt = Function('existsAt', Entity, Time, BoolSort())
        
        solver = Solver()
        
        # Encode BFO Axiom 21
        a, b, c = Consts('a b c', Entity)
        t_time = Const('t_time', Time)
        
        process_def = ForAll([a], 
            Process(a) == And(
                Occurrent(a),
                Exists([b], properTemporalPartOf(b, a)),
                Exists([c, t_time], And(MaterialEntity(c), 
                                       specificallyDependsOnAt(a, c, t_time)))
            )
        )
        
        solver.add(process_def)
        print("Added BFO Axiom 21 definition to solver")
        
        # Test 1: Every process is an occurrent
        print("\nTest 1: Checking if every process is an occurrent...")
        test_entailment = ForAll([a], Implies(Process(a), Occurrent(a)))
        
        solver.push()
        solver.add(Not(test_entailment))
        
        if solver.check() == unsat:
            print("✓ Axiom 21 correctly entails: All processes are occurrents")
        else:
            print("✗ Problem with axiom 21!")
            print("Counterexample:", solver.model())
        
        solver.pop()
        
        # Test 2: Check consistency of axiom itself
        print("\nTest 2: Checking consistency of Axiom 21...")
        solver.push()
        
        if solver.check() == sat:
            print("✓ Axiom 21 is consistent (satisfiable)")
            print("Sample model:", solver.model())
        elif solver.check() == unsat:
            print("✗ Axiom 21 is inconsistent!")
        else:
            print("? Solver timeout or unknown result")
        
        solver.pop()
        
        # Test 3: Create a concrete process and verify properties
        print("\nTest 3: Testing concrete process instance...")
        p1 = Const('p1', Entity)
        temp_part = Const('temp_part', Entity)
        material_ent = Const('material_ent', Entity)
        time1 = Const('time1', Time)
        
        solver.push()
        
        # Assert p1 is a process
        solver.add(Process(p1))
        
        # This should force the consequent of the definition
        if solver.check() == sat:
            model = solver.model()
            print("✓ Created concrete process instance")
            print(f"Process p1 properties in model:")
            print(f"  - Is Occurrent: {model.eval(Occurrent(p1))}")
            print(f"  - Model: {model}")
        else:
            print("✗ Cannot create concrete process instance")
        
        solver.pop()
        
        return True
    
    def simple_z3_test():
        """Simple test to verify Z3 is working"""
        print("Running simple Z3 test...")
        
        x = Int('x')
        y = Int('y')
        
        solver = Solver()
        solver.add(x + y == 10)
        solver.add(x > y)
        solver.add(x > 0)
        
        if solver.check() == sat:
            model = solver.model()
            print(f"✓ Z3 working! Solution: x = {model[x]}, y = {model[y]}")
            return True
        else:
            print("✗ Z3 simple test failed")
            return False
    
    if __name__ == "__main__":
        print("=" * 60)
        print("BFO AXIOM VALIDATION USING Z3")
        print("=" * 60)
        
        # First test Z3 itself
        if simple_z3_test():
            print("\n" + "=" * 60)
            validate_bfo_axiom_21()
        
        print("\n" + "=" * 60)
        print("Validation complete!")

except ImportError as e:
    print("❌ Z3 not available!")
    print(f"Error: {e}")
    print("To install Z3: pip install z3-solver")
    print("\nFor now, here's what the validation would check:")
    print("1. Logical consistency of BFO Axiom 21")
    print("2. Expected entailments (all processes are occurrents)")
    print("3. Concrete instance generation")
    print("4. Counterexample detection if axioms conflict")
    
except Exception as e:
    print(f"❌ Error running validation: {e}")
    import traceback
    traceback.print_exc()