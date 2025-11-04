;; BFO Axiom 21 Validation using Z3 SMT-LIB
;; Axiom 21: Process iff (Occurrent ∧ has proper temporal parts ∧ depends on material entity)

(set-logic ALL)
(set-info :status unknown)

;; Declare sorts (types)
(declare-sort Entity)
(declare-sort Time)

;; Declare predicates
(declare-fun Process (Entity) Bool)
(declare-fun Occurrent (Entity) Bool)
(declare-fun MaterialEntity (Entity) Bool)
(declare-fun properTemporalPartOf (Entity Entity) Bool)
(declare-fun specificallyDependsOnAt (Entity Entity Time) Bool)
(declare-fun existsAt (Entity Time) Bool)

;; BFO Axiom 21: Process definition
;; Process(a) ↔ (Occurrent(a) ∧ ∃b(properTemporalPartOf(b,a)) ∧ ∃c,t(MaterialEntity(c) ∧ specificallyDependsOnAt(a,c,t)))
(assert (forall ((a Entity))
  (= (Process a)
     (and (Occurrent a)
          (exists ((b Entity)) (properTemporalPartOf b a))
          (exists ((c Entity) (t Time)) 
                  (and (MaterialEntity c) 
                       (specificallyDependsOnAt a c t)))))))

;; Test 1: Check consistency - can we have a process?
(echo "=== TEST 1: CONSISTENCY CHECK ===")
(push)
(declare-const p1 Entity)
(declare-const temp_part Entity)
(declare-const material_obj Entity)
(declare-const time1 Time)

(assert (Process p1))

(check-sat)
(echo "Can we construct a Process instance?")
(get-model)
(pop)

;; Test 2: Check entailment - all processes are occurrents
(echo "=== TEST 2: ENTAILMENT CHECK ===")
(push)
;; Try to find counterexample: Process(x) but not Occurrent(x)
(declare-const x Entity)
(assert (Process x))
(assert (not (Occurrent x)))

(check-sat)
(echo "Does Process(x) → Occurrent(x)?")
(echo "If UNSAT, then yes (no counterexample exists)")
(pop)

;; Test 3: Check reverse - not all occurrents are processes
(echo "=== TEST 3: REVERSE ENTAILMENT CHECK ===")
(push)
;; Try to find: Occurrent(x) but not Process(x)
(declare-const y Entity)
(assert (Occurrent y))
(assert (not (Process y)))

(check-sat)
(echo "Can we have Occurrent(x) but not Process(x)?")
(echo "If SAT, then yes (occurrents can be non-processes)")
(get-model)
(pop)

;; Test 4: Check if axiom is well-formed
(echo "=== TEST 4: AXIOM WELL-FORMEDNESS ===")
(check-sat)
(echo "Is the axiom set consistent overall?")

(exit)