;; Comprehensive BFO Axiom Validation using Z3
;; Testing multiple key BFO axioms together

(set-logic ALL)
(set-info :status unknown)

;; Declare sorts
(declare-sort Entity)
(declare-sort Time)

;; Core BFO predicates
(declare-fun Entity-pred (Entity) Bool)
(declare-fun Continuant (Entity) Bool)
(declare-fun Occurrent (Entity) Bool)
(declare-fun Process (Entity) Bool)
(declare-fun MaterialEntity (Entity) Bool)
(declare-fun SpatialRegion (Entity) Bool)
(declare-fun TemporalRegion (Entity) Bool)
(declare-fun IndependentContinuant (Entity) Bool)
(declare-fun SpecificallyDependentContinuant (Entity) Bool)
(declare-fun Quality (Entity) Bool)

;; Relations
(declare-fun properTemporalPartOf (Entity Entity) Bool)
(declare-fun specificallyDependsOnAt (Entity Entity Time) Bool)
(declare-fun continuantPartOfAt (Entity Entity Time) Bool)
(declare-fun existsAt (Entity Time) Bool)
(declare-fun locatedInAt (Entity Entity Time) Bool)

;; BFO Axiom 2: All continuants are entities
(assert (forall ((x Entity))
  (=> (Continuant x) (Entity-pred x))))

;; BFO Axiom 5: Occurrent iff (Entity ∧ has temporal parts)  
(assert (forall ((x Entity))
  (= (Occurrent x)
     (and (Entity-pred x)
          (exists ((y Entity)) (properTemporalPartOf y x))))))

;; BFO Axiom 21: Process definition
(assert (forall ((a Entity))
  (= (Process a)
     (and (Occurrent a)
          (exists ((b Entity)) (properTemporalPartOf b a))
          (exists ((c Entity) (t Time)) 
                  (and (MaterialEntity c) 
                       (specificallyDependsOnAt a c t)))))))

;; BFO Axiom 41: All material entities are independent continuants
(assert (forall ((x Entity))
  (=> (MaterialEntity x) (IndependentContinuant x))))

;; BFO Axiom 8: Independent continuant iff (Continuant ∧ not specifically dependent)
(assert (forall ((a Entity))
  (= (IndependentContinuant a)
     (and (Continuant a)
          (not (exists ((b Entity) (t Time)) 
                       (specificallyDependsOnAt a b t)))))))

;; BFO Axiom 11: All spatial regions are continuants
(assert (forall ((x Entity))
  (=> (SpatialRegion x) (Continuant x))))

;; BFO Axiom 12: All temporal regions are occurrents
(assert (forall ((x Entity))
  (=> (TemporalRegion x) (Occurrent x))))

;; Disjointness: Continuants and Occurrents are disjoint
(assert (forall ((x Entity))
  (not (and (Continuant x) (Occurrent x)))))

;; Now run tests
(echo "=== COMPREHENSIVE BFO VALIDATION ===")

;; Test 1: Basic consistency
(echo "TEST 1: Basic consistency check")
(push)
(check-sat)
(echo "Are the axioms consistent?")
(pop)

;; Test 2: Can we have processes?
(echo "TEST 2: Process existence")
(push)
(declare-const proc Entity)
(assert (Process proc))
(check-sat)
(echo "Can we construct a Process?")
(pop)

;; Test 3: All processes are occurrents (should be UNSAT = valid entailment)
(echo "TEST 3: Process → Occurrent entailment")
(push)
(declare-const p Entity)
(assert (Process p))
(assert (not (Occurrent p)))
(check-sat)
(echo "Counterexample to Process → Occurrent? (should be UNSAT)")
(pop)

;; Test 4: Material entities are continuants (via independent continuants)
(echo "TEST 4: MaterialEntity → Continuant entailment")
(push)
(declare-const m Entity)
(assert (MaterialEntity m))
(assert (not (Continuant m)))
(check-sat)
(echo "Counterexample to MaterialEntity → Continuant? (should be UNSAT)")
(pop)

;; Test 5: No entity can be both continuant and occurrent
(echo "TEST 5: Continuant-Occurrent disjointness")
(push)
(declare-const x Entity)
(assert (Continuant x))
(assert (Occurrent x))
(check-sat)
(echo "Can something be both Continuant and Occurrent? (should be UNSAT)")
(pop)

;; Test 6: Spatial regions are not occurrents
(echo "TEST 6: SpatialRegion disjoint from Occurrent")
(push)
(declare-const s Entity)
(assert (SpatialRegion s))
(assert (Occurrent s))
(check-sat)
(echo "Can SpatialRegion be Occurrent? (should be UNSAT)")
(pop)

;; Test 7: Temporal regions are not continuants  
(echo "TEST 7: TemporalRegion disjoint from Continuant")
(push)
(declare-const t Entity)
(assert (TemporalRegion t))
(assert (Continuant t))
(check-sat)
(echo "Can TemporalRegion be Continuant? (should be UNSAT)")
(pop)

(echo "=== VALIDATION COMPLETE ===")
(exit)