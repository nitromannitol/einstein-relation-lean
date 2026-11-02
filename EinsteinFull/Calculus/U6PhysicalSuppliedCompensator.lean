import EinsteinFull.Calculus.U6PathwiseAssembly
import EinsteinFull.Calculus.S4SmoothGeneratorSupport

/-! Conditional consumers of the countable comparison for the actual supplied laws. -/

open MeasureTheory ProbabilityTheory EinsteinRelation
open Filter
open scoped Topology BigOperators

namespace EinsteinFull

/-- Comparison along one supplied physical solution identifies it with any
textbook solution in the same environment and at the same starting point. -/
theorem u6_supplied_physical_eq_textbook_of_countable_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P T : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hT : SolvesMartingaleProblem
      (External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)) x T)
    (hcompare : ∀ f ∈ tfam d, ∀ᵐ γ ∂P,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal)) : P = T := by
  have hocc := u5_physical_occupation_ac_of_countable_generator_comparison
    hd hΛ hω i lam hP hcompare
  have hPtext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛ hω i lam hP hocc
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨R, _, huniq⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω i lam) hc hs hb he hm hbd x
  exact (huniq _ hPtext).trans (huniq _ hT).symm


/-- The countable comparison is needed only for the two supplied laws in the
actual environment; it yields uniqueness of those laws. -/
theorem u6_physical_family_unique_of_countable_comparison
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hX' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω)))
    (hcompare : ∀ᵐ ω ∂Q.measure, ∀ f ∈ tfam d,
      ∀ᵐ γ ∂PX (0, ω), ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f (γ u.toNNReal))
    (hcompare' : ∀ᵐ ω ∂Q.measure, ∀ f ∈ tfam d,
      ∀ᵐ γ ∂PX' (0, ω), ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f (γ u.toNNReal)) :
    ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, hX, hX', hcompare, hcompare'] with ω hω hP hP' hc hc'
  have ho := u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP hc
  have ho' := u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP' hc'
  obtain ⟨hcA, hs, hb, he, hm, hbd⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨R, _, huniq⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω i lam) hcA hs hb he hm hbd 0
  exact (huniq _ (c4_textbook_solves_of_physical_and_averaged_occupation hΛ hω i lam hP ho)).trans
    (huniq _ (c4_textbook_solves_of_physical_and_averaged_occupation hΛ hω i lam hP' ho')).symm

/-- Avoiding nondifferentiability of the actual reduced coefficient along the
supplied law suffices for absolute continuity of that law's occupation. -/
theorem u6_physical_occupation_of_ae_coefficient_differentiability
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hD : ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ k j : Fin d, DifferentiableAt ℝ
        (fun z => reducedCoefficient ω z k j) (γ u.toNNReal)) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP
  intro f hf
  have hA : (⇑ω.1 : Vec d → Mat d) =
      fun y => (clockDensity ω y)⁻¹ • reducedCoefficient ω y := by
    funext y
    rw [reducedCoefficient, inv_smul_smul₀ (clockDensity_pos ω y).ne']
  filter_upwards [hD] with γ hγ
  filter_upwards [hγ] with u hu
  have he : reducedGenerator i ω lam f (γ u.toNNReal) =
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam) f (γ u.toNNReal) := by
    unfold reducedGenerator
    exact generator_eq_svGenerator_of_differentiableAt (reducedCoefficient ω) i lam
      (contDiff_two_of_top (tfam_test d f hf).1) hu
  rw [physicalGenerator_eq_inv_mul, he, hA]
  exact (svGenerator_smul (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam)
    (fun y => (clockDensity ω y)⁻¹) f (γ u.toNNReal)).symm



/-- A countable additivity-defect cover of the generator-comparison failure
set suffices for occupation absolute continuity of the supplied solution. -/
theorem u6_physical_occupation_of_countable_comparison_defect_cover
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n))
    (hcover : ∀ y f, f ∈ tfam d →
      physicalGenerator i ω lam f y ≠
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam) f y →
      ∃ n, physicalGenerator i ω lam (fun z => F n z + G n z) y ≠
        physicalGenerator i ω lam (F n) y + physicalGenerator i ω lam (G n) y) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP
  intro f hf
  filter_upwards [c4_physical_additivity_defect_countable_ae_zero
    hΛ hω i lam hP F G hF hcF hG hcG] with γ hγ
  filter_upwards [hγ] with u hu
  by_contra hn
  obtain ⟨n, hne⟩ := hcover (γ u.toNNReal) f hf hn
  exact hne (hu n)


/-- A countable family of additivity defects covering the nondifferentiability
set yields occupation absolute continuity for the same supplied solution. -/
theorem u6_physical_occupation_of_countable_defect_cover
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (F G : ℕ → Vec d → ℝ)
    (hF : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (F n))
    (hcF : ∀ n, HasCompactSupport (F n))
    (hG : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (G n))
    (hcG : ∀ n, HasCompactSupport (G n))
    (hcover : ∀ y k j, ¬ DifferentiableAt ℝ
        (fun z => reducedCoefficient ω z k j) y →
      ∃ n, physicalGenerator i ω lam (fun z => F n z + G n z) y ≠
        physicalGenerator i ω lam (F n) y + physicalGenerator i ω lam (G n) y) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply u6_physical_occupation_of_ae_coefficient_differentiability hd hΛ hω i lam hP
  filter_upwards [c4_physical_additivity_defect_countable_ae_zero
    hΛ hω i lam hP F G hF hcF hG hcG] with γ hγ
  filter_upwards [hγ] with u hu
  intro k j
  by_contra hn
  obtain ⟨n, hne⟩ := hcover (γ u.toNNReal) k j hn
  exact hne (hu n)


/-- For the supplied solution, occupation absolute continuity is equivalent to
path-time avoidance of the reduced coefficient's nondifferentiability set. -/
theorem u6_physical_occupation_iff_ae_coefficient_differentiability
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P) :
    (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) ↔
    (∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ k j : Fin d, DifferentiableAt ℝ
        (fun z => reducedCoefficient ω z k j) (γ u.toNNReal)) := by
  constructor
  · intro hocc
    have hA : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ k j : Fin d,
        DifferentiableAt ℝ (fun z => reducedCoefficient ω z k j) y := by
      refine ae_all_iff.2 fun k => ae_all_iff.2 fun j => ?_
      exact (reducedCoefficient_lipschitz hΛ hω k j).ae_differentiableAt_of_real
    exact c16_ae_path_of_averaged_occupation P hocc hA
  · exact u6_physical_occupation_of_ae_coefficient_differentiability hd hΛ hω i lam hP


/-- The exact pathwise conclusion follows from the comparison for the fixed
countable test family on each actual supplied physical law. -/
theorem u6_pathwise_of_countable_comparison
    (hcompare : ∀ {d : ℕ}, 2 ≤ d → ∀ {Λ : ℝ}, 0 < Λ →
      ∀ {ω : FieldPair d}, IsRegular Λ ω → ∀ (i : Fin d) (lam : ℝ)
        {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        ∀ f ∈ tfam d, ∀ᵐ γ ∂P,
          ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
            physicalGenerator i ω lam f (γ u.toNNReal) =
              External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
                f (γ u.toNNReal)) :
    Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt := by
  apply u6_pathwise_of_physical_occupation
  intro d hd Λ hΛ ω hω i lam x P hP
  exact u5_physical_occupation_ac_of_countable_generator_comparison
    hd hΛ hω i lam hP (hcompare hd hΛ hω i lam hP)

/-- The pathwise conclusion follows once every supplied physical solution
avoids the reduced coefficient's nondifferentiability set in path-time. -/
theorem u6_pathwise_of_ae_coefficient_differentiability
    (hD : ∀ {d : ℕ}, 2 ≤ d → ∀ {Λ : ℝ}, 0 < Λ →
      ∀ {ω : FieldPair d}, IsRegular Λ ω → ∀ (i : Fin d) (lam : ℝ)
        {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
          ∀ k j : Fin d, DifferentiableAt ℝ
            (fun z => reducedCoefficient ω z k j) (γ u.toNNReal)) :
    Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt := by
  apply u6_pathwise_of_physical_occupation
  intro d hd Λ hΛ ω hω i lam x P hP
  exact u6_physical_occupation_of_ae_coefficient_differentiability
    hd hΛ hω i lam hP (hD hd hΛ hω i lam hP)




/-- For any physical martingale-problem law, a smooth compact test agrees
with the textbook generator whenever its gradient lies in a prescribed
countable set, on a single path-time event. -/
theorem u6_physical_countable_gradient_values_ae
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d}
    (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (c : ℕ → Vec d) :
    ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)), ∀ m : ℕ,
      gradient f (γ u.toNNReal) = c m →
      physicalGenerator i ω lam f (γ u.toNNReal) =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          f (γ u.toNNReal) := by
  classical
  obtain ⟨χ, hχ, _, _, hχ1, hχ0⟩ := exists_cutoff d
  have hp (m : ℕ) : ∀ᵐ γ ∂P, ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ r : ℕ, ‖γ u.toNNReal‖ < (r : ℝ) + 1 →
        gradient f (γ u.toNNReal) = c m →
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal) := by
    let A : ℕ → Fin d → Vec d → ℝ := fun r j =>
      cutoffFn χ ((r : ℝ) + 1) (fun z => c m j * z j)
    have hA (r : ℕ) (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (A r j) :=
      contDiff_cutoffFn hχ (contDiff_const.mul (contDiff_apply ℝ ℝ j)) _
    have hcA (r : ℕ) (j : Fin d) : HasCompactSupport (A r j) :=
      hasCompactSupport_cutoffFn _ (by positivity) hχ0
    have hc := u5_physical_countable_affine_gradient_comparison hΛ hω i lam hP
      (fun _ => f) A (fun _ => c m) (fun _ => Finset.univ)
      (fun _ => hf) (fun _ => hfc) hA hcA
    filter_upwards [hc] with γ hγ
    filter_upwards [hγ] with u hu
    intro r hr hg
    have hloc (j : Fin d) : A r j =ᶠ[𝓝 (γ u.toNNReal)]
        fun z => c m j * z j :=
      cutoffFn_eventuallyEq _ (by positivity) hχ1 hr
    have he : (fun z => ∑ j : Fin d, A r j z) =ᶠ[𝓝 (γ u.toNNReal)]
        (fun z => ∑ j : Fin d, c m j * z j) := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hr] with z hz
      apply Finset.sum_congr rfl
      intro j _
      exact cutoffFn_eq _ (by positivity) hχ1 (le_of_lt hz)
    have hjet : gradient (fun z => ∑ j : Fin d, A r j z) (γ u.toNNReal) = c m := by
      funext k
      change fderiv ℝ (fun z => ∑ j : Fin d, A r j z) (γ u.toNNReal)
        (unitVector k) = c m k
      rw [he.fderiv_eq]
      have hs : (fun z : Vec d => ∑ j : Fin d, c m j * z j) =
          ∑ j : Fin d, (fun z : Vec d => c m j * z j) := by
        ext z
        simp
      rw [hs, fderiv_sum (fun j _ => (differentiableAt_apply j _).const_mul (c m j))]
      have hder (j : Fin d) : fderiv ℝ (fun z : Vec d => c m j * z j)
          (γ u.toNNReal) = c m j • ContinuousLinearMap.proj j := by
        rw [fderiv_const_mul (differentiableAt_apply j _), (hasFDerivAt_apply j _).fderiv]
      simp_rw [hder]
      simp [unitVector, Pi.single_apply]
    apply hu r (fun j _ => hloc j)
    simpa using hg.trans hjet.symm
  have h := ae_all_iff.mpr hp
  filter_upwards [h] with γ hγ
  have hu := ae_all_iff.mpr hγ
  filter_upwards [hu] with u hu
  intro m hg
  obtain ⟨r, hr⟩ := exists_nat_gt ‖γ u.toNNReal‖
  exact hu m r (by linarith) hg


/-- Occupation control follows from comparison away from any prescribed
countable set of gradients; comparison on the set itself is automatic. -/
theorem u6_physical_occupation_of_comparison_off_countable_gradients
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (c : ℕ → Vec d)
    (hcompare : ∀ f ∈ tfam d, ∀ᵐ γ ∂P,
      ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
        (∀ m, gradient f (γ u.toNNReal) ≠ c m) →
        physicalGenerator i ω lam f (γ u.toNNReal) =
          External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
            f (γ u.toNNReal)) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply u5_physical_occupation_ac_of_countable_generator_comparison hd hΛ hω i lam hP
  intro f hf
  have ht := tfam_test d f hf
  filter_upwards [hcompare f hf,
    u6_physical_countable_gradient_values_ae hΛ hω i lam hP f ht.1 ht.2 c] with γ ho hc
  filter_upwards [ho, hc] with u ho hc
  by_cases hm : ∃ m, gradient f (γ u.toNNReal) = c m
  · obtain ⟨m, hm⟩ := hm
    exact hc m hm
  · exact ho (fun m he => hm ⟨m, he⟩)


/-- The pathwise statement follows if comparison holds outside a prescribed
countable gradient set for every actual physical solution. -/
theorem u6_pathwise_of_comparison_off_countable_gradients
    (hcompare : ∀ {d : ℕ}, 2 ≤ d → ∀ {Λ : ℝ}, 0 < Λ →
      ∀ {ω : FieldPair d}, IsRegular Λ ω → ∀ (i : Fin d) (lam : ℝ)
        {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        ∃ c : ℕ → Vec d, ∀ f ∈ tfam d, ∀ᵐ γ ∂P,
          ∀ᵐ u ∂volume.restrict (Set.Ioi (0 : ℝ)),
            (∀ m, gradient f (γ u.toNNReal) ≠ c m) →
            physicalGenerator i ω lam f (γ u.toNNReal) =
              External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
                f (γ u.toNNReal)) :
    Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt := by
  apply u6_pathwise_of_physical_occupation
  intro d hd Λ hΛ ω hω i lam x P hP
  obtain ⟨c, hc⟩ := hcompare hd hΛ hω i lam hP
  exact u6_physical_occupation_of_comparison_off_countable_gradients
    hd hΛ hω i lam hP c hc


/-- A supplied reduced solution in a smooth environment spends no positive
time in any fixed spatial null set. -/
theorem u6_smooth_supplied_reduced_null_occupation
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω))) :
    ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, hQ, hY] with ω hω hs hy
  have ht := (reducedGenerator_solves_iff hs.1 (⟨0, by omega⟩ : Fin d)
    lam 0 (Y (0, ω))).1 hy
  have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛ hω (⟨0, by omega⟩ : Fin d) lam ht
  intro N hN hnull
  exact c16_ae_path_of_averaged_occupation (Y (0, ω)) hocc
    (p := fun y => y ∉ N) (ae_iff.mpr (by simpa using hnull))


open scoped ENNReal NNReal

/-- Scale-uniform weak flux coercivity yields the finite occupation energy bound. -/
theorem u6_occupation_energy_of_weak_flux {d : ℕ}
    (P : Measure (Path d)) [IsProbabilityMeasure P] (T : ℝ≥0)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b)
    (F : ℝ → Vec d → Vec d) (ρ : ℝ → Vec d → ℝ)
    (hflux : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      HasWeakDivergence Set.univ (F r) (ρ r) ∧
      (∀ j : Fin d, Integrable (fun y => F r y j) volume) ∧
      Integrable (ρ r) volume ∧ (∫ y, |ρ r y|) ≤ 2 ∧
      ∀ y, a * euclideanSq (gradient u y) - b * u y ^ 2 ≤
        dot (F r y) (gradient u y)) :
    ∃ E : ℝ, 0 < E ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + α)
      Integrable e volume ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)) := by
  let D : ℝ := (2 + α * b) / (α * a)
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D + (1 - α), by linarith, ?_⟩
  intro r hr
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  obtain ⟨hu, hui, hDu, hmass⟩ :=
    c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z-y)).le
  obtain ⟨B, hB0, hB⟩ := c16_normalized_polynomial_smoothing_fderiv_bounded μ hr m
  obtain ⟨hw, hFi, hρi, hρbound, hco⟩ := hflux r hr
  have he := c16_weak_divergence_nonlinear_energy hw hFi hρi hu hu0 hui hDu
    hB0 hB ha hb hα hco
  have hei := c16_nonlinear_energy_integrable hu hu0 hDu hB0 hB hα.le
  refine ⟨hei, ?_⟩
  change (∫ y, euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)) ≤
    (D + (1 - α)) * (1 + (T : ℝ))
  calc
    _ ≤ ((∫ y, |ρ r y|) + α * b * ∫ y, u y) / (α * a) := he
    _ ≤ (2 + α * b * (T : ℝ)) / (α * a) := by
      rw [hmass]
      exact div_le_div_of_nonneg_right (add_le_add hρbound (le_refl _)) (mul_pos hα ha).le
    _ ≤ ((2 + α * b) * (1 + (T : ℝ))) / (α * a) := by
      apply div_le_div_of_nonneg_right _ (mul_pos hα ha).le
      nlinarith [T.coe_nonneg]
    _ = D * (1 + (T : ℝ)) := by dsimp only [D]; ring
    _ ≤ (D + (1 - α)) * (1 + (T : ℝ)) := by
      nlinarith [T.coe_nonneg]

/-- Physical coefficient smoothing has a scale-uniform commutator bound for
the occupation measure of the supplied law. -/
theorem u6_physical_occupation_smoothing_commutator {d : ℕ} {Λ : ℝ}
    (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    {x : Vec d} {P : Measure (Path d)} (i : Fin d) (lam : ℝ)
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (T : ℝ≥0) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    {r : ℝ} (hr : 0 < r) (k j l : Fin d) (y : Vec d) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ := c16NormalizedPolynomialKernel r m
    let u : Vec d → ℝ := fun v => ∫ z, κ (z-v) ∂μ
    |fderiv ℝ (fun v => ∫ z, ω.1 z k j * κ (z-v) ∂μ) y (unitVector l) -
      ω.1 y k j * fderiv ℝ u y (unitVector l)| ≤
      (Λ * ((d : ℝ) + 1)) * (2 * (m : ℝ)) * u y := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let L : ℝ≥0 := ⟨Λ * ((d : ℝ) + 1), by positivity⟩
  have hLip : LipschitzWith L (fun z => ω.1 z k j) :=
    lipschitzWith_of_euclidean_bound Λ hΛ.le (hω.2.2.1.entry_bound k j)
  have hbound (z : Vec d) : |ω.1 z k j| ≤ (⟨Λ, hΛ.le⟩ : ℝ≥0) :=
    abs_apply_le_of_isElliptic hΛ hω.1 z k j
  have he := c16_normalized_smoothing_derivative_commutator μ hLip
    ⟨Λ, hΛ.le⟩ hbound hr m hdm y l
  have hL : (L : ℝ) = Λ * ((d : ℝ) + 1) := rfl
  dsimp only [μ] at he
  dsimp only
  rw [he.1]
  simpa only [add_sub_cancel_left, hL] using he.2

/-- The physical smoothed flux is integrable and has a uniform commutator estimate. -/
theorem u6_physical_smoothed_flux_bound {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (μ : Measure (Vec d)) [IsFiniteMeasure μ]
      (r : ℝ), 0 < r →
      let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
      let u : Vec d → ℝ := fun y => ∫ z, κ (z - y) ∂μ
      let F : Vec d → Vec d := fun y j =>
        (1 / 2 : ℝ) * (∑ k, fderiv ℝ
          (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k)) -
          ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
      (∀ j, Integrable (fun y => F y j)) ∧
      ∀ y j, |F y j - (1 / 2 : ℝ) *
        ∑ k, ω.1 y k j * fderiv ℝ u y (unitVector k)| ≤ M * u y := by
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := physical_svHypotheses hΛ hω i lam
  let L : ℝ≥0 := ⟨Λ₀ * ((d : ℝ) + 1), by positivity⟩
  let Q : ℝ := (L : ℝ) * (2 * (m : ℝ))
  let M : ℝ := (1 / 2 : ℝ) * (d : ℝ) * Q + |Mb|
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  refine ⟨M, by dsimp only [M]; positivity, ?_⟩
  intro μ _ r hr
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let u : Vec d → ℝ := fun y => ∫ z, κ (z - y) ∂μ
  let H (k j : Fin d) (y : Vec d) := fderiv ℝ
    (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k)
  let V (j : Fin d) (y : Vec d) :=
    ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
  let F : Vec d → Vec d := fun y j => (1 / 2 : ℝ) * ∑ k, H k j y - V j y
  obtain ⟨hpos, hc, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  obtain ⟨K, D, hK, _⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hui : Integrable u := (c16_normalized_polynomial_smoothing_mass μ hr m hdm).1
  have hDui := c16_normalized_polynomial_smoothing_fderiv_integrable μ hr m hdm
  have hκi (y : Vec d) : Integrable (fun z => κ (z - y)) μ :=
    (integrable_const (K : ℝ)).mono'
      ((hc.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hK _))
  have hHc (k j : Fin d) : Continuous (H k j) :=
    ((c16_normalized_weighted_smoothing_contDiff_one μ hr m
      (hA.matrix_elem k j).measurable ⟨|Ma|, abs_nonneg Ma⟩
      (fun z => (hAb z k j).trans (le_abs_self Ma))).continuous_fderiv one_ne_zero).clm_apply
        continuous_const
  have hVc (j : Fin d) : Continuous (V j) :=
    (c16_normalized_weighted_smoothing_contDiff_one μ hr m
      ((measurable_pi_apply j).comp hb) ⟨|Mb|, abs_nonneg Mb⟩
      (fun z => (hbb z j).trans (le_abs_self Mb))).continuous
  have hE (k j : Fin d) (y : Vec d) :
      |H k j y - ω.1 y k j * fderiv ℝ u y (unitVector k)| ≤ Q * u y := by
    have he := c16_normalized_smoothing_derivative_commutator μ
      (lipschitzWith_of_euclidean_bound Λ₀ hΛ.le (hω.2.2.1.entry_bound k j)) ⟨|Ma|, abs_nonneg Ma⟩
      (fun z => (hAb z k j).trans (le_abs_self Ma)) hr m hdm y k
    change H k j y = _ ∧ _ at he
    dsimp only [u, κ]
    rw [he.1]
    simpa only [add_sub_cancel_left] using he.2
  have hVb (j : Fin d) (y : Vec d) : |V j y| ≤ |Mb| * u y :=
    (c16_bounded_smoothing_flux μ ((measurable_pi_apply j).comp hb)
      ⟨|Mb|, abs_nonneg Mb⟩ (fun z => (hbb z j).trans (le_abs_self Mb))
      hc.continuous.measurable (fun z => (hpos z).le) y (hκi y)).2
  have hHi (k j : Fin d) : Integrable (H k j) := by
    apply ((hDui.norm.const_mul |Ma|).add (hui.const_mul Q)).mono' (hHc k j).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun y => ?_
    have hv : |fderiv ℝ u y (unitVector k)| ≤ ‖fderiv ℝ u y‖ := by
      simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one, mul_one] using
        (fderiv ℝ u y).le_opNorm (unitVector k)
    have hp : |ω.1 y k j * fderiv ℝ u y (unitVector k)| ≤
        |Ma| * ‖fderiv ℝ u y‖ := by
      rw [abs_mul]
      exact mul_le_mul ((hAb y k j).trans (le_abs_self Ma)) hv (abs_nonneg _) (abs_nonneg _)
    have ha := abs_add_le (H k j y - ω.1 y k j *
      fderiv ℝ u y (unitVector k)) (ω.1 y k j * fderiv ℝ u y (unitVector k))
    rw [sub_add_cancel] at ha
    rw [Real.norm_eq_abs]
    change |H k j y| ≤ |Ma| * ‖fderiv ℝ u y‖ + Q * u y
    exact ha.trans (by linarith [hE k j y])
  have hVi (j : Fin d) : Integrable (V j) :=
    (hui.const_mul |Mb|).mono' (hVc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => (Real.norm_eq_abs _).trans_le (hVb j y))
  change (∀ j, Integrable (fun y => F y j)) ∧ ∀ y j,
    |F y j - (1 / 2 : ℝ) * ∑ k, ω.1 y k j *
      fderiv ℝ u y (unitVector k)| ≤ M * u y
  refine ⟨fun j => ((integrable_finsetSum _ (fun k _ => hHi k j)).const_mul _).sub (hVi j), ?_⟩
  intro y j
  have heq : F y j - (1 / 2 : ℝ) * ∑ k, ω.1 y k j *
      fderiv ℝ u y (unitVector k) = (1 / 2 : ℝ) *
      ∑ k, (H k j y - ω.1 y k j * fderiv ℝ u y (unitVector k)) - V j y := by
    dsimp only [F]
    rw [Finset.sum_sub_distrib]
    ring
  rw [heq]
  calc
    _ ≤ |(1 / 2 : ℝ) * ∑ k, (H k j y - ω.1 y k j *
        fderiv ℝ u y (unitVector k))| + |V j y| := abs_sub _ _
    _ ≤ (1 / 2 : ℝ) * (∑ k : Fin d, Q * u y) + |Mb| * u y := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left
        ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hE k j y))
          (by norm_num)) (hVb j y)
    _ = M * u y := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; dsimp only [M]; ring

/-- Weak divergence of the physical smoothed flux yields the same-law energy bound. -/
theorem u6_physical_occupation_energy_of_smoothed_divergence {d : ℕ} {Λ : ℝ}
    (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (T : ℝ≥0) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    (α : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hweak : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let κ := c16NormalizedPolynomialKernel r m
      let F : Vec d → Vec d := fun y j =>
        (1 / 2 : ℝ) * (∑ k, fderiv ℝ
          (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k)) -
          ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
      let ρ : Vec d → ℝ := fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
      HasWeakDivergence Set.univ F ρ) :
    ∃ E : ℝ, 0 < E ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + α)
      Integrable e volume ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)) := by
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨_, _, _, ⟨c, hc, hell⟩, _, _⟩ := physical_svHypotheses hΛ hω i lam
  obtain ⟨M, hM, hflux⟩ := u6_physical_smoothed_flux_bound hΛ hω i lam m hdm
  let F : ℝ → Vec d → Vec d := fun r y j =>
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ := c16NormalizedPolynomialKernel r m
    (1 / 2 : ℝ) * (∑ k, fderiv ℝ
      (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k)) -
      ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
  let ρ : ℝ → Vec d → ℝ := fun r y =>
    (∫ γ, c16NormalizedPolynomialKernel r m (γ T - y) ∂P) -
      c16NormalizedPolynomialKernel r m (x - y)
  apply u6_occupation_energy_of_weak_flux P T m hdm α hα hα1
    (c / 4) ((d : ℝ) * (M ^ 2 / c)) (by positivity) (by positivity) F ρ
  intro r hr
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  obtain ⟨hFi, hFe⟩ := hflux μ r hr
  obtain ⟨hρi, hρbound⟩ := c16_probability_smoothed_endpoint_l1 P T x hr m hdm
  refine ⟨hweak r hr, hFi, hρi, hρbound, ?_⟩
  intro y
  exact c16_elliptic_flux_coercivity (ω.1 y) (gradient u y) (F r y)
    hc (hell y (gradient u y)) (hFe y)


/-- The convolved generator identity gives the corresponding flux identity. -/
theorem u6_physical_smoothed_divergence_of_convolved_weak {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ))
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (T : ℝ≥0)
    (hconvolved : ∀ (f : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∫ y, ∫ z, c16NormalizedPolynomialKernel r m (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z) (fun _ => physicalDrift ω i lam z) f y
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
        ∫ y, ((∫ γ, c16NormalizedPolynomialKernel r m (γ T - y) ∂P) -
          c16NormalizedPolynomialKernel r m (x - y)) * f y) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y,
      fderiv ℝ (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k) *
        fderiv ℝ f y (unitVector j)) =
      (∑ k, ∫ y, (∫ z, physicalDrift ω i lam z k * κ (z - y) ∂μ) *
        fderiv ℝ f y (unitVector k)) -
      ∫ y, ((∫ γ, κ (γ T - y) ∂P) - κ (x - y)) * f y := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := physical_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (ω.1)
      (physicalDrift ω i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  have hdiv := c16_smoothed_generator_divergence μ hcoef hr m hdm hf hfc
  have hweak := hconvolved f hf hfc
  have he := hdiv.symm.trans hweak
  dsimp only at he ⊢
  linarith only [he]


/-- The convolved generator identity gives weak divergence of the smoothed flux. -/
theorem u6_physical_hasWeakDivergence_of_convolved_weak {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    {r : ℝ} (hr : 0 < r) (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (hconvolved : ∀ (f : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∫ y, ∫ z, c16NormalizedPolynomialKernel r m (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z) (fun _ => physicalDrift ω i lam z) f y
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
        ∫ y, ((∫ γ, c16NormalizedPolynomialKernel r m (γ T - y) ∂P) -
          c16NormalizedPolynomialKernel r m (x - y)) * f y) :
    let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
    let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
    let F : Vec d → Vec d := fun y j =>
      (1 / 2 : ℝ) * (∑ k, fderiv ℝ
        (fun v => ∫ z, ω.1 z k j * κ (z - v) ∂μ) y (unitVector k)) -
        ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
    let ρ : Vec d → ℝ := fun y => (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
    HasWeakDivergence Set.univ F ρ := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let κ : Vec d → ℝ := c16NormalizedPolynomialKernel r m
  let S (k j : Fin d) (y : Vec d) := ∫ z, ω.1 z k j * κ (z - y) ∂μ
  let V (j : Fin d) (y : Vec d) :=
    ∫ z, physicalDrift ω i lam z j * κ (z - y) ∂μ
  let H (k j : Fin d) (y : Vec d) := fderiv ℝ (S k j) y (unitVector k)
  let F : Vec d → Vec d := fun y j => (1 / 2 : ℝ) * (∑ k, H k j y) - V j y
  let ρ (y : Vec d) := (∫ γ, κ (γ T - y) ∂P) - κ (x - y)
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := physical_svHypotheses hΛ hω i lam
  have hS (k j : Fin d) : ContDiff ℝ 1 (S k j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m (hA.matrix_elem k j).measurable
      ⟨|Ma|, abs_nonneg Ma⟩ (fun z => (hAb z k j).trans (le_abs_self Ma))
  have hV (j : Fin d) : ContDiff ℝ 1 (V j) :=
    c16_normalized_weighted_smoothing_contDiff_one μ hr m
      ((measurable_pi_apply j).comp hb) ⟨|Mb|, abs_nonneg Mb⟩
      (fun z => (hbb z j).trans (le_abs_self Mb))
  have hH (k j : Fin d) : Continuous (H k j) :=
    ((hS k j).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hF (j : Fin d) : Continuous (fun y => F y j) :=
    (continuous_const.mul (continuous_finsetSum _ fun k _ => hH k j)).sub (hV j).continuous
  obtain ⟨_, hκ, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  obtain ⟨K, D, hK, hD⟩ := c16_normalized_polynomial_kernel_bounded (d := d) hr m
  have hρ : Continuous ρ := by
    apply Continuous.sub ?_ (hκ.continuous.comp (continuous_const.sub continuous_id))
    refine continuous_of_dominated (bound := fun _ : Path d => (K : ℝ)) ?_ ?_
      (integrable_const _) ?_
    · intro y
      exact ((hκ.continuous.measurable.comp
        (((continuous_eval.comp (continuous_id.prodMk continuous_const)).measurable).sub
          measurable_const)).aestronglyMeasurable)
    · intro y
      exact Filter.Eventually.of_forall fun γ => (Real.norm_eq_abs _).trans_le (hK _)
    · exact Filter.Eventually.of_forall fun γ =>
        hκ.continuous.comp (continuous_const.sub continuous_id)
  have hpair {q : Vec d → ℝ} (hq : ContDiff ℝ 1 q) (hqc : HasCompactSupport q) :
      (∫ y, dot (F y) (gradient q y)) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j) := by
    have hI (k j : Fin d) : Integrable (fun y => H k j y * fderiv ℝ q y (unitVector j)) :=
      ((hH k j).mul ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
        (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hIV (j : Fin d) : Integrable (fun y => V j y * fderiv ℝ q y (unitVector j)) :=
      ((hV j).continuous.mul
        ((hq.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
          (hqc.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_left
    have hII (k : Fin d) := integrable_finsetSum Finset.univ (fun j _ => hI k j)
    have hIII := integrable_finsetSum Finset.univ (fun k _ => hII k)
    have hIVs := integrable_finsetSum Finset.univ (fun j _ => hIV j)
    have hp (y : Vec d) : dot (F y) (gradient q y) =
        (1 / 2 : ℝ) * (∑ k, ∑ j, H k j y * fderiv ℝ q y (unitVector j)) -
          ∑ j, V j y * fderiv ℝ q y (unitVector j) := by
      dsimp only [F, dot, gradient, coordinateDerivative]
      simp_rw [sub_mul, mul_assoc, Finset.sum_mul, Finset.sum_sub_distrib]
      rw [← Finset.mul_sum, Finset.sum_comm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hp), integral_sub (hIII.const_mul _) hIVs,
      integral_const_mul, integral_finsetSum _ (fun j _ => hIV j),
      integral_finsetSum _ (fun k _ => hII k)]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    exact integral_finsetSum _ (fun j _ => hI k j)
  have hw : HasWeakDivergence Set.univ F ρ := by
    refine ⟨fun j => (hF j).locallyIntegrable.locallyIntegrableOn _,
      hρ.locallyIntegrable.locallyIntegrableOn _, ?_⟩
    intro q hq
    simp only [Measure.restrict_univ]
    rw [hpair (hq.1.of_le (by simp)) hq.2.1]
    have he := u6_physical_smoothed_divergence_of_convolved_weak hΛ hω i lam hP
      hr m hdm hq.1 hq.2.1 T hconvolved
    dsimp only at he
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) -
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) = -(∫ y, ρ y * q y)
    change (1 / 2 : ℝ) * (∑ k, ∑ j, ∫ y, H k j y * fderiv ℝ q y (unitVector j)) =
      (∑ j, ∫ y, V j y * fderiv ℝ q y (unitVector j)) - (∫ y, ρ y * q y) at he
    linarith only [he]
  exact hw



/-- A convolved weak generator identity for the supplied law yields its finite
occupation energy estimate. -/
theorem u6_literal_physical_finite_occupation_energy_of_convolved_weak
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (T : ℝ≥0)
    (hconvolved : ∀ r : ℝ, 0 < r → ∀ (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∫ y, ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z)
          (fun _ => physicalDrift ω i lam z) f y
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
        ∫ y, ((∫ γ, c16NormalizedPolynomialKernel r (d + 1) (γ T - y) ∂P) -
          c16NormalizedPolynomialKernel r (d + 1) (x - y)) * f y) :
    ∃ E : ℝ, 0 < E ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)) := by
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    push_cast
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < (2 * (d : ℝ))⁻¹ := by positivity
  have hα1 : (2 * (d : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity)]
    linarith
  apply u6_physical_occupation_energy_of_smoothed_divergence hΛ hω i lam hP T
    (d + 1) hdm _ hα hα1
  intro r hr
  exact u6_physical_hasWeakDivergence_of_convolved_weak hΛ hω i lam hP hr
    (d + 1) hdm T (hconvolved r hr)

end EinsteinFull
