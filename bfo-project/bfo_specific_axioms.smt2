;; Testing specific BFO axioms from our extracted FOL list
;; Focus on axioms with interesting logical structure

(set-logic ALL)

;; Declare sorts
(declare-sort Entity)
(declare-sort Time)

;; Predicates from BFO axioms
(declare-fun Entity-pred (Entity) Bool)
(declare-fun Continuant (Entity) Bool)
(declare-fun Occurrent (Entity) Bool)
(declare-fun MaterialEntity (Entity) Bool)
(declare-fun TemporalRegion (Entity) Bool)
(declare-fun SpatialRegion (Entity) Bool)
(declare-fun ZeroDimensionalSpatialRegion (Entity) Bool)
(declare-fun OneDimensionalSpatialRegion (Entity) Bool)  
(declare-fun TwoDimensionalSpatialRegion (Entity) Bool)
(declare-fun ThreeDimensionalSpatialRegion (Entity) Bool)
(declare-fun Quality (Entity) Bool)
(declare-fun SpecificallyDependentContinuant (Entity) Bool)

;; Relations
(declare-fun existsAt (Entity Time) Bool)
(declare-fun continuantPartOfAt (Entity Entity Time) Bool)
(declare-fun temporalPartOf (Entity Entity) Bool)

;; BFO Axiom from line 1: Material Entity → ∃t(TemporalRegion(t) ∧ existsAt(x,t))
(assert (forall ((x Entity))
  (=> (MaterialEntity x)
      (exists ((t Entity))
        (and (TemporalRegion t) (existsAt x t))))))

;; BFO Axiom from line 2: Continuant → Entity
(assert (forall ((x Entity))
  (=> (Continuant x) (Entity-pred x))))

;; BFO Axiom from line 10: SpatialRegion parts are SpatialRegions
(assert (forall ((x Entity) (y Entity) (t Time))
  (=> (and (SpatialRegion x) (continuantPartOfAt y x t))
      (SpatialRegion y))))

;; BFO Axiom from line 11: SpatialRegion → Continuant  
(assert (forall ((x Entity))
  (=> (SpatialRegion x) (Continuant x))))

;; BFO Axiom from line 15: TwoDimensionalSpatialRegion → SpatialRegion
(assert (forall ((x Entity))
  (=> (TwoDimensionalSpatialRegion x) (SpatialRegion x))))

;; BFO Axiom from line 26: ZeroDimensionalSpatialRegion → SpatialRegion
(assert (forall ((x Entity))
  (=> (ZeroDimensionalSpatialRegion x) (SpatialRegion x))))

;; BFO Axiom from line 27: Quality persistence
(assert (forall ((x Entity))
  (=> (exists ((t Time)) (and (existsAt x t) (Quality x)))
      (forall ((t1 Time)) (=> (existsAt x t1) (Quality x))))))

;; BFO Axiom from line 28: Quality → SpecificallyDependentContinuant
(assert (forall ((x Entity))
  (=> (Quality x) (SpecificallyDependentContinuant x))))

(echo "=== TESTING SPECIFIC BFO AXIOMS ===")

;; Test spatial region hierarchy
(echo "TEST 1: Spatial region type hierarchy")
(push)
(declare-const point Entity)
(assert (ZeroDimensionalSpatialRegion point))
;; Should entail: SpatialRegion and Continuant and Entity
(assert (not (and (SpatialRegion point) 
                  (Continuant point) 
                  (Entity-pred point))))
(check-sat)
(echo "Does 0D spatial region → spatial region → continuant → entity? (should be UNSAT)")
(pop)

;; Test quality persistence
(echo "TEST 2: Quality persistence through time")
(push)
(declare-const qual Entity)
(declare-const time1 Time)
(declare-const time2 Time)
(assert (existsAt qual time1))
(assert (Quality qual))
(assert (existsAt qual time2))
(assert (not (Quality qual))) ;; Try to make it not a quality at time2
(check-sat)
(echo "Can quality lose its quality-ness over time? (should be UNSAT)")
(pop)

;; Test material entity temporal requirement
(echo "TEST 3: Material entities must exist at some time")
(push)
(declare-const mat Entity)
(assert (MaterialEntity mat))
(assert (forall ((t Entity)) (not (and (TemporalRegion t) (existsAt mat t)))))
(check-sat)
(echo "Can material entity exist without temporal region? (should be UNSAT)")
(pop)

;; Test mereological closure for spatial regions
(echo "TEST 4: Spatial region mereological closure")
(push)
(declare-const region1 Entity)
(declare-const region2 Entity)
(declare-const time_t Time)
(assert (SpatialRegion region1))
(assert (continuantPartOfAt region2 region1 time_t))
(assert (not (SpatialRegion region2)))
(check-sat)
(echo "Can non-spatial-region be part of spatial region? (should be UNSAT)")
(pop)

;; Test satisfiability with multiple dimensional regions
(echo "TEST 5: Multiple dimensional spatial regions")
(push)
(declare-const p Entity)
(declare-const l Entity) 
(declare-const s Entity)
(declare-const v Entity)
(assert (ZeroDimensionalSpatialRegion p))      ; point
(assert (OneDimensionalSpatialRegion l))       ; line  
(assert (TwoDimensionalSpatialRegion s))       ; surface
(assert (ThreeDimensionalSpatialRegion v))     ; volume
(check-sat)
(echo "Can we have all spatial dimensions simultaneously?")
(get-model)
(pop)

(echo "=== SPECIFIC AXIOM TESTING COMPLETE ===")
(exit)