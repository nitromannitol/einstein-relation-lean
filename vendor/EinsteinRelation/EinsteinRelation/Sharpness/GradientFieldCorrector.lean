import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Correctors.HorizontalH1GradientMeanZero
import EinsteinRelation.Environment.ReductionEmbedding
import EinsteinRelation.Sharpness.Energy

/-! # Gradient fields as sharpness correctors

Source `paper/main.tex:1235-1238` (Proposition 7.1, Step 2), with the stationary scalar potential
replaced by its orbit gradient. The orbit gradient is read from a bounded measurable field
`G : FieldPair d → Vec d` on the physical environment, with `G (translate x ω)` the gradient of
the potential at the point `x`. Since `G` is defined on the environment itself, no stationary
scalar potential on `FieldPair d` is needed.

* `gradientField_exists_reduced_mem`: the reduced `L²` representative of `G` lies in the closed
  stationary potential-gradient domain. This uses the characterization
  `OrbitPotentialGradientDomain`, which is carried as an explicit proposition.
* `gradient_field_corrector_identification`: the reduced representative is the canonical corrector
  gradient, and the expected flux column is the unit vector `e_{i₁}`.
* `integral_gradientSharpEnergy_pos`: the mean sharp energy of `G` is strictly positive unless
  `G` vanishes almost surely.
-/

open EinsteinRelation.Correctors
open MeasureTheory Filter

namespace EinsteinRelation.Sharpness

noncomputable section

/-! ### The orbit-potential characterization of the domain -/

/-- The orbit-potential characterization of the closed stationary potential-gradient domain of
the reduced law.

If `G` is measurable and bounded by `1/4` pointwise, and almost every translation orbit of `G`
is the gradient of a `C¹` potential bounded by `M`, then every `L²` representative `E` of the
reduced field, meaning `E (reduce ω) = G ω` almost surely, lies in `correctorPotentialDomain Q`.

The library does not contain this characterization, so it is carried as an explicit proposition
and every consumer below takes it as a hypothesis. -/
def OrbitPotentialGradientDomain {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) : Prop :=
  ∀ (G : FieldPair d → Vec d) (M : ℝ),
    Measurable G → (∀ ω, euclideanNorm (G ω) ≤ 1 / 4) →
    (∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω)) →
    ∀ E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      (∀ᵐ ω ∂Q.measure, (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d))) →
      E ∈ correctorPotentialDomain Q

/-! ### Euclidean norm on the coordinate carrier -/

private theorem gradientField_norm_toLp {d : ℕ} (v : Vec d) :
    euclideanNorm v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d))‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (v i)).symm

/-! ### Step 1: the reduced representative lies in the domain -/

/-- Step 1. A bounded measurable field whose translation orbits are gradients of bounded
potentials has a reduced `L²` representative in the closed potential-gradient domain. -/
theorem gradientField_exists_reduced_mem {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hdomain : OrbitPotentialGradientDomain Q) (G : FieldPair d → Vec d) (M : ℝ)
    (hGm : Measurable G) (hGb : ∀ ω, euclideanNorm (G ω) ≤ 1 / 4)
    (hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω)) :
    ∃ E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      E ∈ correctorPotentialDomain Q ∧
        ∀ᵐ ω ∂Q.measure, (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) := by
  obtain ⟨D, hDm, hDL⟩ := EinsteinRelation.Probability.exists_measurable_leftInverse_reduce d
  have hDr : ∀ ω, D (reduce ω) = ω := fun ω => hDL ω
  have hGDm : Measurable (fun ω' : FieldPair d =>
      (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))) :=
    (WithLp.measurable_toLp 2 (Vec d)).comp (hGm.comp hDm)
  have hGDb : ∀ ω', ‖(WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))‖ ≤ 1 / 4 := by
    intro ω'
    rw [← gradientField_norm_toLp]
    exact hGb (D ω')
  have hmem : MemLp (fun ω' : FieldPair d =>
      (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))) 2 (reducedEnvironmentLaw Q) :=
    MemLp.of_bound hGDm.aestronglyMeasurable (1 / 4) (Filter.Eventually.of_forall hGDb)
  obtain ⟨E, hEΓ⟩ : ∃ E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      (⇑E : FieldPair d → EuclideanSpace ℝ (Fin d)) =ᵐ[reducedEnvironmentLaw Q]
        (fun ω' => (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))) :=
    ⟨hmem.toLp _, hmem.coeFn_toLp⟩
  have hpull : ∀ᵐ ω ∂Q.measure,
      (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) := by
    have h1 : ∀ᵐ ω' ∂(Measure.map (reduce (d := d)) Q.measure),
        (⇑E) ω' = (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)) := hEΓ
    filter_upwards [((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
      (p := fun ω' : FieldPair d =>
        (⇑E) ω' = (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)))).mp h1] with ω hω
    have hω' : (⇑E) (reduce ω) = (WithLp.toLp 2 (G (D (reduce ω))) : EuclideanSpace ℝ (Fin d)) :=
      hω
    rw [hω', hDr ω]
  exact ⟨E, hdomain G M hGm hGb hG E hpull, hpull⟩

/-! ### The reduced coefficient action at the origin -/

private noncomputable def gradientPairAction {d : ℕ} (p : Mat d × EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (p.1.mulVec p.2.ofLp)

private theorem gradientPairAction_continuous {d : ℕ} :
    Continuous (gradientPairAction (d := d)) := by
  exact (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp
    (continuous_fst.matrix_mulVec
      ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).comp continuous_snd))

private theorem gradientPairAction_norm_le {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    {M : Mat d} (hM : IsElliptic Λ (fun _ : Vec d => M))
    (u : EuclideanSpace ℝ (Fin d)) :
    ‖gradientPairAction (M, u)‖ ≤ Λ * ‖u‖ := by
  have h := isElliptic_mulVec_euclideanNorm_le hΛ hM 0 u.ofLp
  calc
    ‖gradientPairAction (M, u)‖ = euclideanNorm (M.mulVec u.ofLp) := by
      simp only [gradientPairAction, gradientField_norm_toLp]
    _ ≤ Λ * euclideanNorm u.ofLp := h
    _ = Λ * ‖u‖ := by
      simp only [gradientField_norm_toLp, WithLp.toLp_ofLp]

private theorem gradientPairOrigin_continuous {d : ℕ} :
    Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

private theorem gradientPairAction_aestronglyMeasurable {d : ℕ} {Q : Measure (FieldPair d)}
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    AEStronglyMeasurable (fun ω : FieldPair d => gradientPairAction (ω.1 (0 : Vec d), u ω)) Q := by
  have hPseudo : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    exact inferInstance
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) := hPseudo
  have hSecond : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    exact inferInstance
  letI : SecondCountableTopology (Mat d) := hSecond
  apply gradientPairAction_continuous.comp_aestronglyMeasurable
  exact (gradientPairOrigin_continuous.measurable.aestronglyMeasurable.prodMk
    (Lp.aestronglyMeasurable u))

private theorem gradientPairAction_memLp {d : ℕ} {Q : Measure (FieldPair d)}
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hEll : ∀ᵐ ω ∂Q, IsElliptic Λ (fun _ : Vec d => ω.1 (0 : Vec d)))
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) :
    MemLp (fun ω : FieldPair d => gradientPairAction (ω.1 (0 : Vec d), u ω)) 2 Q := by
  apply (Lp.memLp u).of_le_mul (gradientPairAction_aestronglyMeasurable u)
  filter_upwards [hEll] with ω hω
  exact gradientPairAction_norm_le hΛ hω (u ω)

/-- The coefficient action at the origin, read pointwise on the reduced law. -/
private theorem gradientReducedAction_coeFn {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (u : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    (fun ω => reducedOriginCoefficientAction Q u ω) =ᵐ[reducedEnvironmentLaw Q]
      fun ω => gradientPairAction (ω.1 (0 : Vec d), u ω) := by
  have hmem := gradientPairAction_memLp
    (mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))
    (ae_reducedEnvironmentLaw_origin_elliptic Q) u
  have heq : reducedOriginCoefficientAction Q u =
      hmem.toLp (fun ω : FieldPair d => gradientPairAction (ω.1 (0 : Vec d), u ω)) := rfl
  have h := hmem.coeFn_toLp
  rw [← heq] at h
  exact h

/-! ### The flux identity on the reduced law -/

private theorem gradientInner_correctorUnitVector {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (i : Fin d) : inner ℝ x (correctorUnitVector i) = x i := by
  simp [correctorUnitVector, PiLp.inner_apply, RCLike.inner_apply, mul_ite, mul_comm]

private theorem gradientInner_eq_integral_coord {d : ℕ} {μ : Measure (FieldPair d)}
    (X F : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) (i : Fin d)
    (hF : ∀ᵐ ω ∂μ, F ω = correctorUnitVector i) :
    inner ℝ X F = ∫ ω, X ω i ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hF] with ω hω
  show inner ℝ (X ω) (F ω) = X ω i
  rw [hω]
  exact gradientInner_correctorUnitVector (X ω) i

/-- The flux `a (e_i + E)` equals `e_i` almost surely on the reduced law, when `E` is almost
surely the Euclidean field `Γ` and `a (e_i + Γ) = e_i` holds there. -/
private theorem gradientFlux_ae {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (Γ : FieldPair d → EuclideanSpace ℝ (Fin d))
    (hE : (⇑E : FieldPair d → EuclideanSpace ℝ (Fin d)) =ᵐ[reducedEnvironmentLaw Q] Γ)
    (hs : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      (ω.1 (0 : Vec d)).mulVec (unitVector i + (Γ ω).ofLp) = unitVector i) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, correctorFluxOfGradient Q i E ω = correctorUnitVector i := by
  filter_upwards [gradientReducedAction_coeFn Q
      (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) + E),
    Lp.coeFn_add (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i)) E,
    Lp.coeFn_const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i), hE, hs]
    with ω hb hadd hc hEω hsω
  have hb' : reducedOriginCoefficientAction Q
      (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) + E) ω =
        gradientPairAction (ω.1 (0 : Vec d),
          (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) + E) ω) := hb
  have hu : (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) + E) ω =
      correctorUnitVector i + Γ ω := by
    rw [hadd, Pi.add_apply, hEω]
    exact congrArg (fun x : EuclideanSpace ℝ (Fin d) => x + Γ ω) hc
  show reducedOriginCoefficientAction Q
      (Lp.const 2 (reducedEnvironmentLaw Q) (correctorUnitVector i) + E) ω = correctorUnitVector i
  rw [hb', hu]
  show WithLp.toLp 2 ((ω.1 (0 : Vec d)).mulVec
      (correctorUnitVector i + Γ ω : EuclideanSpace ℝ (Fin d)).ofLp) = correctorUnitVector i
  have hv : (correctorUnitVector i + Γ ω : EuclideanSpace ℝ (Fin d)).ofLp =
      unitVector i + (Γ ω).ofLp := rfl
  rw [hv, hsω]
  rfl

/-! ### Step 2: identification with the canonical corrector -/

/-- Step 2, mirroring `sharp_corrector_identification` with the orbit gradient replaced by the
bounded field `G`. The reduced representative of `G` is the canonical corrector gradient, and
the expected flux column is `e_{i₁}`. -/
theorem gradient_field_corrector_identification {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hdomain : OrbitPotentialGradientDomain Q)
    (i₁ : Fin d) (G : FieldPair d → Vec d) (M : ℝ) (hGm : Measurable G)
    (hGb : ∀ ω, euclideanNorm (G ω) ≤ 1 / 4)
    (hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω))
    (hharm : ∀ᵐ ω ∂Q.measure,
      (reducedCoefficient ω 0).mulVec (unitVector i₁ + G ω) = unitVector i₁) :
    (∀ᵐ ω ∂Q.measure, (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) =
        (canonicalCorrectorGradient Q i₁ :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (reduce ω)) ∧
      expectedCorrectorFlux Q i₁ = correctorUnitVector i₁ := by
  obtain ⟨E, hEdom, hpull⟩ := gradientField_exists_reduced_mem Q hdomain G M hGm hGb hG
  obtain ⟨D, -, hDL⟩ := EinsteinRelation.Probability.exists_measurable_leftInverse_reduce d
  have hDr : ∀ ω, D (reduce ω) = ω := fun ω => hDL ω
  -- On the reduced law, `E` is the Euclidean field `G ∘ D`.
  have hEΓ : (⇑E : FieldPair d → EuclideanSpace ℝ (Fin d)) =ᵐ[reducedEnvironmentLaw Q]
      (fun ω' => (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))) := by
    refine ((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
      (p := fun ω' : FieldPair d =>
        (⇑E) ω' = (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)))).mpr ?_
    filter_upwards [hpull] with ω hω
    have hω' : (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d)) := hω
    show (⇑E) (reduce ω) = (WithLp.toLp 2 (G (D (reduce ω))) : EuclideanSpace ℝ (Fin d))
    rw [hDr ω]
    exact hω'
  -- The sharpness identity `a (e_{i₁} + G) = e_{i₁}` holds on the reduced law.
  have hsν : ∀ᵐ ω' ∂reducedEnvironmentLaw Q,
      (ω'.1 (0 : Vec d)).mulVec (unitVector i₁ +
        (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)).ofLp) = unitVector i₁ := by
    refine ((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
      (p := fun ω' : FieldPair d => (ω'.1 (0 : Vec d)).mulVec (unitVector i₁ +
        (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)).ofLp) = unitVector i₁)).mpr ?_
    filter_upwards [hharm] with ω hω
    show (reducedCoefficient ω 0).mulVec (unitVector i₁ +
      (WithLp.toLp 2 (G (D (reduce ω))) : EuclideanSpace ℝ (Fin d)).ofLp) = unitVector i₁
    rw [hDr ω]
    exact hω
  have hflux := gradientFlux_ae Q i₁ E
    (fun ω' => (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d))) hEΓ hsν
  -- The variational identity, tested against every horizontal `H¹` element.
  have hvar : ∀ f : horizontalH1 (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i₁ E) = 0 := by
    intro f
    rw [gradientInner_eq_integral_coord (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f) (correctorFluxOfGradient Q i₁ E) i₁ hflux]
    rw [integral_congr_ae (horizontalEuclideanGradient_coordinates (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f i₁)]
    exact integral_horizontalH1Gradient_eq_zero (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) f i₁
  have hcan : canonicalCorrectorGradient Q i₁ = ⟨E, hEdom⟩ :=
    (correctorGradient_eq_canonical_of_horizontal_variational Q i₁ ⟨E, hEdom⟩ hvar).symm
  have hcoe : (canonicalCorrectorGradient Q i₁ :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) = E :=
    congrArg Subtype.val hcan
  constructor
  · rw [hcoe]
    exact hpull.mono fun ω hω => hω.symm
  · have hcf : canonicalCorrectorFlux Q i₁ = correctorFluxOfGradient Q i₁ E := by
      unfold canonicalCorrectorFlux
      rw [hcoe]
    rw [expectedCorrectorFlux_eq_integral, hcf]
    calc ∫ ω, correctorFluxOfGradient Q i₁ E ω ∂reducedEnvironmentLaw Q
        = ∫ _ω, correctorUnitVector i₁ ∂reducedEnvironmentLaw Q := integral_congr_ae hflux
      _ = correctorUnitVector i₁ := by simp

/-! ### Step 3: positivity of the sharp energy -/

private theorem gradientField_coord_sq_le {d : ℕ} (g : Vec d) (i : Fin d) :
    g i * g i ≤ euclideanSq g := by
  unfold euclideanSq dot
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)

private theorem gradientField_abs_coord_le {d : ℕ} (g : Vec d) (i : Fin d) :
    |g i| ≤ euclideanNorm g := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact gradientField_coord_sq_le g i

private theorem gradientField_euclideanSq_le {d : ℕ} (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : euclideanSq g ≤ 1 / 16 := by
  have h0 : 0 ≤ euclideanNorm g := Real.sqrt_nonneg _
  have hsq : euclideanNorm g ^ 2 = euclideanSq g := Real.sq_sqrt (euclideanSq_nonneg g)
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hg)]

private theorem gradientField_one_add_pos {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : 0 < 1 + g i := by
  have hlo := (abs_le.mp ((gradientField_abs_coord_le g i).trans hg)).1
  linarith

private theorem gradientField_sharpEnergy_le {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : sharpEnergy i g ≤ 1 / 12 := by
  have hj := gradientField_one_add_pos i g hg
  have hlo := (abs_le.mp ((gradientField_abs_coord_le g i).trans hg)).1
  have hE := gradientField_euclideanSq_le g hg
  rw [sharpEnergy, div_le_iff₀ hj]
  linarith

/-- Step 3. If the bounded gradient field `G` is not almost surely zero, its mean sharp energy
`E[|G|² / (1 + G_{i₁})]` is strictly positive. -/
theorem integral_gradientSharpEnergy_pos {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (i₁ : Fin d) {G : FieldPair d → Vec d} (hGm : Measurable G)
    (hGb : ∀ ω, euclideanNorm (G ω) ≤ 1 / 4)
    (hne : ¬ G =ᵐ[Q] (0 : FieldPair d → Vec d)) :
    0 < ∫ ω, sharpEnergy i₁ (G ω) ∂Q := by
  have hcoord : ∀ j : Fin d, Measurable (fun ω : FieldPair d => G ω j) :=
    fun j => (measurable_pi_apply j).comp hGm
  have hsqM : Measurable (fun ω : FieldPair d => euclideanSq (G ω)) := by
    have hsum : Measurable (fun ω : FieldPair d => ∑ j, G ω j * G ω j) :=
      Finset.measurable_sum Finset.univ fun j _ => (hcoord j).mul (hcoord j)
    exact hsum
  have hden : Measurable (fun ω : FieldPair d => 1 + G ω i₁) :=
    measurable_const.add (hcoord i₁)
  have hmeas : Measurable (fun ω : FieldPair d => sharpEnergy i₁ (G ω)) :=
    hsqM.div hden
  have hpos : ∀ ω, 0 < 1 + G ω i₁ := fun ω => gradientField_one_add_pos i₁ (G ω) (hGb ω)
  have hnonneg : ∀ ω, 0 ≤ sharpEnergy i₁ (G ω) := fun ω => sharpEnergy_nonneg i₁ _ (hpos ω)
  have hint : Integrable (fun ω : FieldPair d => sharpEnergy i₁ (G ω)) Q :=
    Integrable.of_bound hmeas.aestronglyMeasurable (1 / 12) (ae_of_all _ fun ω => by
      show ‖sharpEnergy i₁ (G ω)‖ ≤ 1 / 12
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg ω)]
      exact gradientField_sharpEnergy_le i₁ _ (hGb ω))
  have hf0 : (0 : FieldPair d → ℝ) ≤ fun ω => sharpEnergy i₁ (G ω) :=
    fun ω => hnonneg ω
  have hsupp : Function.support (fun ω : FieldPair d => sharpEnergy i₁ (G ω)) =
      {ω | G ω ≠ 0} := by
    ext ω
    simp only [Function.mem_support, Set.mem_setOf_eq]
    constructor
    · intro h hG0
      apply h
      rw [hG0]
      simp [sharpEnergy, euclideanSq, dot]
    · intro hG0
      exact ((sharpEnergy_pos_iff i₁ (G ω) (hpos ω)).mpr hG0).ne'
  have hμ : Q {ω | G ω ≠ 0} ≠ 0 := by
    intro h0
    apply hne
    show ∀ᵐ ω ∂Q, G ω = (0 : FieldPair d → Vec d) ω
    rw [ae_iff]
    exact h0
  refine (integral_pos_iff_support_of_nonneg hf0 hint).mpr ?_
  rw [hsupp]
  exact pos_iff_ne_zero.mpr hμ

end

end EinsteinRelation.Sharpness
