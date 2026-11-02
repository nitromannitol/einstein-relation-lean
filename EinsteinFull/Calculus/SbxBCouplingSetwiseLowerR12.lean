import EinsteinFull.Calculus.SbxAChainVolumeScalingR09
import EinsteinFull.Calculus.SbxACouplingFinalStepR11
import EinsteinFull.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.Calculus.SbxBActualTranslatedOneStepSetwiseR15
import EinsteinFull.Calculus.SbxBActualNativeLowerTransferR11
import EinsteinFull.Calculus.SbxBTranslatedNativeLocalStepR15

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Diffusion EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP EinsteinFull.Blueprint.TubeProbability
noncomputable section

/-- The actual integration windows of the eighty-step coupling chain. -/
@[nolint defsWithUnderscore]
def b_couplingChainWindow {d : ℕ} (i : Fin d) (R : ℝ) (x : Vec d) (k : ℕ) : Set (Vec d) :=
  if k < 80 then sourceBall
    (Calculus.b_tube_segment_center x (x + (9 * R) • unitVector i) 80 k) (R / 16)
  else if k = 80 then endpointBall i R x else ∅

/-- Every chain transition fits in a killed ball inside the coupling region,
with both successive windows contained in its inner half. -/
theorem b_coupling_chain_step_geometry {d : ℕ} (i : Fin d) (R : ℝ)
    (x : Vec d) (hR : 0 < R) (k : ℕ) (hk : k < 80) :
    ∃ z : Vec d, ∃ s : ℝ, 0 < s ∧
      (s = R / 2 ∨ s = 2 * R) ∧
      sourceBall z s ⊆ couplingRegion i R x ∧
      b_couplingChainWindow i R x k ⊆ sourceBall z (s / 2) ∧
      b_couplingChainWindow i R x (k + 1) ⊆ sourceBall z (s / 2) := by
  let e := x + (9 * R) • unitVector i
  have he : e ∈ endpointBall i R x := by
    change euclideanNorm (e - (x + (9 * R) • unitVector i)) < R
    simp only [e, sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, Real.sqrt_zero]
    exact hR
  by_cases hlast : k = 79
  · subst k
    have hg := Calculus.a_coupling_final_step_geometry i R x hR 80 (by omega)
    refine ⟨e, 2 * R, by positivity, Or.inr rfl, ?_, ?_, ?_⟩
    · exact hg.1
    · intro y hy
      have hy' : y ∈ sourceBall (Calculus.b_tube_segment_center x e 80 (80 - 1))
          (R / 16) := by
        simpa [b_couplingChainWindow, e] using hy
      have hz := hg.2.2 hy'
      simpa using hz
    · intro y hy
      have hy' : y ∈ endpointBall i R x := by
        simpa [b_couplingChainWindow] using hy
      have hz := hg.2.1 ▸ hy'
      simpa using hz
  · have hk' : k + 1 < 80 := by omega
    let z := Calculus.b_tube_segment_center x e 80 k
    refine ⟨z, R / 2, by positivity, Or.inl rfl, ?_, ?_, ?_⟩
    · exact Calculus.a_coupling_equispaced_margin i R x e hR he 80 k (by omega) (by omega)
    · intro y hy
      change euclideanNorm (y - z) < (R / 2) / 2
      have hy' : euclideanNorm (y - z) < R / 16 := by
        simpa [b_couplingChainWindow, hk, z, e, sourceBall] using hy
      linarith
    · intro y hy
      have hy' : y ∈ sourceBall (Calculus.b_tube_segment_center x e 80 (k+1))
          (R / 16) := by
        simpa [b_couplingChainWindow, hk', e] using hy
      have hz : z ∈ sourceBall (Calculus.b_tube_segment_center x e 80 k) (R / 16) := by
        change euclideanNorm (z - z) < R / 16
        simp only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero,
          Finset.sum_const_zero, Real.sqrt_zero]
        positivity
      have h := (Calculus.a_coupling_consecutive_inner_ball i R x e hR he 80 k
        (by omega) z y hz hy').2
      change euclideanNorm (y - z) < (R / 2) / 2
      change euclideanNorm (y - z) < R / 4 at h
      linarith

/-- The physical substep is the scaled time used by the local estimate. -/
theorem b_coupling_step_time (μ : ℝ) (hμ : 0 < μ) :
    ((1 / 80 : ℝ) / μ^2).toNNReal = Renewal.regenDelta μ / (80 : ℝ≥0) := by
  apply NNReal.coe_injective
  change (((((1 / 80 : ℝ) / μ^2).toNNReal : ℝ≥0) : ℝ)) =
    (((((μ^2)⁻¹).toNNReal : ℝ≥0) : ℝ) / 80)
  rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
  ring

/-- Force scaling sends the inner half of a physical ball into its
corresponding scaled inner ball. -/
theorem b_coupling_scaled_inner {d : ℕ} (μ s : ℝ) (hμ : 0 < μ)
    (z v : Vec d) (hv : v ∈ sourceBall z (s/2)) :
    μ • (v-z) ∈ sourceBall 0 ((μ*s)/2) := by
  change euclideanNorm (μ • (v-z)-0) < (μ*s)/2
  change euclideanNorm (v-z) < s/2 at hv
  rw [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos hμ]
  nlinarith

/-- Eighty literal one-step bounds imply the full-duration endpoint estimate.
The coefficient is selected before the force and environment. -/
theorem b_coupling_setwise_of_local_chain {d : ℕ} (a l : ℝ)
    (ha : 0 < a) (hl : 0 < l) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : ℝ) (hμ : 0 < μ),
    ∀ {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
      {hω : IsRegular L ω} {h₁ : μ ≤ 1}
      (G : GantertFixedEnvironmentRealization hd L hL ω hω μ hμ.le h₁)
      (x : Vec d),
    let i := Renewal.forceCoord hd
    let R := l / μ
    let U := couplingRegion i R x
    let τ := Renewal.regenDelta μ / (80 : ℝ≥0)
    let A := b_couplingChainWindow i R x
    (∀ k < 80, ∀ z ∈ A k,
      ENNReal.ofReal (a * μ ^ d) • (volume : Measure (Vec d)).restrict (A (k+1)) ≤
        gmpKilledEndpointKernel G U (by
          exact isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
            (continuous_id.sub continuous_const)) continuous_const) τ z) →
    ENNReal.ofReal (c * μ ^ d) • (volume : Measure (Vec d)).restrict (endpointBall i R x) ≤
      ((G.pathLaw x).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ → γ t ∈ U}).map
        (fun γ => γ (Renewal.regenDelta μ)) := by
  obtain ⟨c, hc, hchain⟩ := a_actual_killed_chain_scaled (d := d) a (l / 16) ha (by positivity) 79
  refine ⟨c, hc, ?_⟩
  intro μ hμ hd L hL ω hω h₁ G x
  dsimp only
  let i := Renewal.forceCoord hd
  let R := l / μ
  let e := x + (9 * R) • unitVector i
  let U := couplingRegion i R x
  let A := b_couplingChainWindow i R x
  let centers : ℕ → Vec d := fun k => Calculus.b_tube_segment_center x e 80 k
  have hR : 0 < R := div_pos hl hμ
  have he : e ∈ endpointBall i R x := by
    change euclideanNorm (e - (x + (9 * R) • unitVector i)) < R
    simp only [e, sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, Real.sqrt_zero]
    exact hR
  have hopen (z : Vec d) (r : ℝ) : IsOpen (sourceBall z r) := by
    exact isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hU : IsOpen U := by
    change IsOpen (sourceBall (x + (5 * R) • unitVector i) (6 * R))
    exact hopen _ _
  have hA (k : ℕ) : MeasurableSet (A k) := by
    dsimp [A, b_couplingChainWindow]
    split
    · exact (hopen _ _).measurableSet
    · split
      · change MeasurableSet (sourceBall e R)
        exact (hopen _ _).measurableSet
      · exact MeasurableSet.empty
  have hAU (k : ℕ) : A k ⊆ U := by
    by_cases hk : k < 80
    · have hm := Calculus.a_coupling_equispaced_margin i R x e hR he 80 k (by omega) (by omega)
      intro z hz
      apply hm
      change euclideanNorm (z - centers k) < R / 2
      simp only [A, b_couplingChainWindow, if_pos hk] at hz
      change euclideanNorm (z - centers k) < R / 16 at hz
      linarith
    · by_cases hk' : k = 80
      · subst k
        have hf := Calculus.a_coupling_final_step_geometry i R x hR 80 (by omega)
        intro z hz
        apply hf.1
        change euclideanNorm (z - e) < 2 * R
        simp only [A, b_couplingChainWindow, show ¬ 80 < 80 by omega, if_false, if_true] at hz
        change euclideanNorm (z - e) < R at hz
        linarith
      · simp [A, b_couplingChainWindow, hk, hk']
  have hballs : ∀ j ∈ Finset.range 79,
      A (j+1) = sourceBall (centers (j+1)) ((l/16)/μ) := by
    intro j hj
    have hj' : j+1 < 80 := by have := Finset.mem_range.mp hj; omega
    simp only [A, b_couplingChainWindow, if_pos hj', centers, e, R]
    congr 1
    ring
  have hx : x ∈ A 0 := by
    change euclideanNorm (x - centers 0) < R/16
    have hc0 : centers 0 = x := by simp [centers, Calculus.b_tube_segment_center]
    rw [hc0]
    simp only [sub_self, euclideanNorm, euclideanSq, dot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  intro hstep
  have hs : ∀ k z, z ∈ A k → ENNReal.ofReal (a * μ ^ d) •
      (volume : Measure (Vec d)).restrict (A (k+1)) ≤
        gmpKilledEndpointKernel G U hU (Renewal.regenDelta μ / (80 : ℝ≥0)) z := by
    intro k z hz
    by_cases hk : k < 80
    · exact hstep k hk z hz
    · have hempty : A (k+1) = ∅ := by simp [A, b_couplingChainWindow, show ¬ k+1 < 80 by omega, show k+1 ≠ 80 by omega]
      rw [hempty, Measure.restrict_empty, smul_zero]
      exact bot_le
  have h := hchain μ hμ G U hU (Renewal.regenDelta μ / (80 : ℝ≥0)) A centers hA hAU hballs hs x hx
  have ht := (Calculus.a_regen_delta_subdivision μ hμ 80 (by omega)).1
  have hlast : A (79+1) = endpointBall i R x := by simp [A, b_couplingChainWindow]
  rw [hlast] at h
  norm_num only at h
  norm_num only at ht
  rw [ht, gmpKilledEndpointKernel_apply] at h
  have hevent : {γ : Path d | ((Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) < localityExitTime U γ} =
      {γ : Path d | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ → γ t ∈ U} := by
    ext γ
    exact lt_localityExitTime_iff U hU γ _
  rw [hevent] at h
  exact h

/-- The translated actual-coefficient case needs no normalization premise.
The native pointwise input is stated at the scaled one-step strength. -/
theorem s14_actual_translated_one_step_physical
    {d : ℕ} (hd : 2 ≤ d) (κ b : ℝ) (hκ : 0 < κ) (hb : 0 < b)
    (μ : ℝ) (hμ : 0 < μ)
    (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular L (translate z ω))
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (s : GantertFixedEnvironmentRealization hd L hL (translate z ω) hωz lam h0 h1)
    (R : ℝ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd (translate z ω) lam x ∧
      α x = s4PhysicalAlpha hd (translate z ω) lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hsub : (fun x : Vec d => x - z) ⁻¹' sourceBall 0 R ⊆ U)
    (A V : Set (Vec d)) (hV : MeasurableSet V)
    (hA : ∀ x ∈ A, x - z ∈ sourceBall 0 R)
    (hVinside : ∀ x ∈ V, x - z ∈ sourceBall 0 R)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (hlower : ∀ x ∈ A, ∀ y ∈ V,
      b * μ ^ d ≤ K t (y - z) (x - z) / ρ (x - z)) :
    ∀ x ∈ A, ENNReal.ofReal ((κ * b) * μ ^ d) •
      (volume : Measure (Vec d)).restrict V ≤ gmpKilledEndpointKernel r U hU t x := by
  intro x hx
  let V' : Set (Vec d) := (fun y : Vec d => y + z) ⁻¹' V
  have hV' : MeasurableSet V' := hV.preimage (continuous_id.add continuous_const).measurable
  have hVsub : V' ⊆ sourceBall (0 : Vec d) R := by
    intro y hy
    simpa using hVinside (y + z) hy
  let q : ℝ := Real.rpow (t : ℝ) (-(d : ℝ) / 2)
  have hq : 0 < q := Real.rpow_pos_of_pos ht _
  let a : ℝ := b * μ ^ d / q
  have ha : 0 < a := div_pos (mul_pos hb (pow_pos hμ _)) hq
  have haeq : a * q = b * μ ^ d := div_mul_cancel₀ _ (ne_of_gt hq)
  have hpoint : ∀ y ∈ V', a * q ≤ K t y (x - z) / ρ (x - z) := by
    intro y hy
    rw [haeq]
    simpa using hlower x hx (y + z) hy
  have hcenter := b_actual_native_setwise_lower_of_pointwise a κ ha hκ s hκ hR
    hell hcoeff hK t ht (x-z) (hA x hx) V' hV' hVsub hpoint
    (fun y _ => (hell.2.2 y).1)
  have hecoeff : κ * a * Real.rpow (t : ℝ) (-(d : ℝ) / 2) = (κ*b)*μ^d := by
    change κ * a * q = _
    rw [show κ * a * q = κ * (a*q) by ring, haeq]
    ring
  rw [hecoeff] at hcenter
  have h := b_translated_killed_setwise_mono_r15 hd L hL ω hω lam h0 h1 z hωz r s
    R U hU hsub V' hV' t (x-z) _ hcenter
  have heq : (fun y : Vec d => y - z) ⁻¹' V' = V := by
    ext y
    simp [V']
  simpa only [heq, sub_add_cancel] using h

/-- Uniform one-step estimate for translated actual coefficients at a
prescribed positive scaled time. -/
theorem s14_actual_translated_uniform_one_step
    (d : ℕ) (hd : 2 ≤ d) (L l T : ℝ)
    (hL : 1 ≤ L) (hl : 0 < l) (hT : 0 < T) :
    ∃ a : ℝ, 0 < a ∧ ∀ (μ R : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1), 0 < R → l = μ * R →
    ∀ (ω : FieldPair d) (hω : IsRegular L ω) (z : Vec d)
      (r : GantertFixedEnvironmentRealization hd L hL ω hω μ hμ.le hμ1)
      (U : Set (Vec d)) (hU : IsOpen U),
    (fun x : Vec d => x-z) ⁻¹' sourceBall 0 R ⊆ U →
    ∀ (A V : Set (Vec d)), MeasurableSet V →
      (∀ x ∈ A, x-z ∈ sourceBall 0 R) →
      (∀ y ∈ V, y-z ∈ sourceBall 0 R) →
      (∀ x ∈ A, μ • (x-z) ∈ sourceBall 0 (l/2)) →
      (∀ y ∈ V, μ • (y-z) ∈ sourceBall 0 (l/2)) →
    ∀ x ∈ A, ENNReal.ofReal (a * μ^d) • (volume : Measure (Vec d)).restrict V ≤
      gmpKilledEndpointKernel r U hU (T/μ^2).toNNReal x := by
  obtain ⟨κ, b, hκ, hb, hnative⟩ :=
    Calculus.b_translated_actual_native_local_step_r15 d hd L l T hL hl hT
  refine ⟨κ*b, mul_pos hκ hb, ?_⟩
  intro μ R hμ hμ1 hR hlR ω hω z r U hU hsub A V hV hA hVin hAs hVs
  let hωz : IsRegular L (translate z ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff z ω).mpr hω
  let s := Classical.choice (u5_regular_signed_fixed_environment_realization_exists
    hd hL (translate z ω) hωz μ hμ.le hμ1)
  obtain ⟨ρ, α, hell, _, _, _, spec, G, hK, hcoeff, hbound⟩ :=
    hnative R μ hR (ne_of_gt hμ) (by simpa [abs_of_pos hμ] using hlR) z ω hω
  let ρ' : Vec d → ℝ := fun y => ρ (z+y)
  let α' : Vec d → Mat d := fun y => α (z+y)
  have hs : Continuous (fun y : Vec d => z+y) := continuous_const.add continuous_id
  have hell' : IsUniformlyElliptic κ ρ' α' :=
    ⟨hell.1.comp hs.measurable, hell.2.1.comp hs.measurable, fun y => hell.2.2 _⟩
  have ht : 0 < T / μ^2 := div_pos hT (sq_pos_of_pos hμ)
  have ht' : 0 < (((T/μ^2).toNNReal : ℝ≥0) : ℝ) := by
    simpa only [Real.coe_toNNReal _ ht.le] using ht
  have hpoint : ∀ x ∈ A, ∀ y ∈ V, b * μ^d ≤
      bNativeSpectralKernelR13 spec
        (T/μ^2).toNNReal (y-z) (x-z) / ρ' (x-z) := by
    intro x hx y hy
    have hh := (hbound (μ • (y-z)) (hVs y hy) (μ • (x-z)) (hAs x hx)).1
    rw [abs_of_pos hμ] at hh
    have heq (w : Vec d) : μ⁻¹ • (μ • w) = w := by simp [smul_smul, hμ.ne']
    rw [heq, heq] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (pow_nonneg hμ.le d)
    have hcancel : μ^d * ((μ⁻¹)^d *
        bNativeSpectralKernelR13 spec
          (T/μ^2) (y-z) (x-z) / ρ' (x-z)) =
        bNativeSpectralKernelR13 spec
          (T/μ^2) (y-z) (x-z) / ρ' (x-z) := by
      rw [inv_pow]
      field_simp
    rw [hcancel] at hh'
    simpa only [Real.coe_toNNReal _ ht.le, mul_comm] using hh'
  exact s14_actual_translated_one_step_physical hd κ b hκ hb
    μ hμ L hL ω hω μ hμ.le hμ1 z hωz r s R hR hell' hcoeff hK
    U hU hsub A V hV hA hVin (T/μ^2).toNNReal ht' hpoint

/-- The remaining local estimate: each of the eighty individual transitions
has a uniform lower bound at the prescribed substep time. -/
def bCouplingLocalStepInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
    ∃ a : ℝ, 0 < a ∧ ∀ (Q : EnvironmentLaw d Λ r)
      (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1)
      (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
        hω μ hμ.le h₁) (x : Vec d),
      let i := Renewal.forceCoord hd
      let R := l / μ
      let U := couplingRegion i R x
      let A := b_couplingChainWindow i R x
      ∀ k < 80, ∀ z ∈ A k,
        ENNReal.ofReal (a * μ ^ d) • (volume : Measure (Vec d)).restrict (A (k+1)) ≤
          gmpKilledEndpointKernel G U (by
            exact isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
              (continuous_id.sub continuous_const)) continuous_const)
            (Renewal.regenDelta μ / (80 : ℝ≥0)) z

/-- The translated native estimate supplies all eighty local transitions. -/
theorem b_coupling_local_steps : bCouplingLocalStepInput := by
  intro d hd Λ r l hl
  by_cases hΛ : 1 ≤ Λ
  · have hl' : 0 < l := lt_of_lt_of_le zero_lt_one hl
    obtain ⟨a₁, ha₁, hstep₁⟩ := s14_actual_translated_uniform_one_step
      d hd (sourceReducedBound Λ) (l/2) (1/80) (one_le_sourceReducedBound hΛ)
      (by positivity) (by norm_num)
    obtain ⟨a₂, ha₂, hstep₂⟩ := s14_actual_translated_uniform_one_step
      d hd (sourceReducedBound Λ) (2*l) (1/80) (one_le_sourceReducedBound hΛ)
      (by positivity) (by norm_num)
    refine ⟨min a₁ a₂, lt_min ha₁ ha₂, ?_⟩
    intro Q μ hμ hμ1 ω hω G x
    dsimp only
    let i := Renewal.forceCoord hd
    let R := l / μ
    let U := couplingRegion i R x
    let A := b_couplingChainWindow i R x
    have hR : 0 < R := div_pos hl' hμ
    have hopen (z : Vec d) (s : ℝ) : IsOpen (sourceBall z s) :=
      isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)) continuous_const
    have hU : IsOpen U := hopen _ _
    have hA (k : ℕ) : MeasurableSet (A k) := by
      dsimp [A, b_couplingChainWindow]
      split
      · exact (hopen _ _).measurableSet
      · split
        · exact (hopen _ _).measurableSet
        · exact MeasurableSet.empty
    intro k hk y hy
    obtain ⟨z,s,hs,hsr,hsub,hprev,hnext⟩ :=
      b_coupling_chain_step_geometry i R x hR k hk
    have hsub' : (fun v : Vec d => v-z) ⁻¹' sourceBall 0 s ⊆ U := by
      intro v hv
      apply hsub
      simpa [sourceBall] using hv
    have hinside {v : Vec d} (hv : v ∈ sourceBall z (s/2)) :
        v-z ∈ sourceBall 0 s := by
      change euclideanNorm (v-z-0) < s
      change euclideanNorm (v-z) < s/2 at hv
      simp only [sub_zero]
      linarith
    have hscaled {v : Vec d} (hv : v ∈ sourceBall z (s/2)) :
        μ • (v-z) ∈ sourceBall 0 ((μ*s)/2) :=
      b_coupling_scaled_inner μ s hμ z v hv
    have htime := b_coupling_step_time μ hμ
    have hRscale : μ*R=l := by dsimp [R]; field_simp
    rcases hsr with hs₁|hs₂
    · have hscale : l/2=μ*s := by rw [hs₁]; nlinarith
      have h := hstep₁ μ s hμ hμ1 hs hscale _ hω z G U hU hsub'
        (A k) (A (k+1)) (hA (k+1))
        (fun v hv => hinside (hprev hv)) (fun v hv => hinside (hnext hv))
        (fun v hv => by simpa [←hscale] using hscaled (hprev hv))
        (fun v hv => by simpa [←hscale] using hscaled (hnext hv)) y hy
      rw [htime] at h
      apply le_trans ?_ h
      gcongr
      exact min_le_left _ _
    · have hscale : 2*l=μ*s := by rw [hs₂]; nlinarith
      have h := hstep₂ μ s hμ hμ1 hs hscale _ hω z G U hU hsub'
        (A k) (A (k+1)) (hA (k+1))
        (fun v hv => hinside (hprev hv)) (fun v hv => hinside (hnext hv))
        (fun v hv => by simpa [←hscale] using hscaled (hprev hv))
        (fun v hv => by simpa [←hscale] using hscaled (hnext hv)) y hy
      rw [htime] at h
      apply le_trans ?_ h
      gcongr
      exact min_le_right _ _
  · refine ⟨1, zero_lt_one, ?_⟩
    intro Q
    exact (hΛ Q.ellipticity_parameter).elim

/-- The original all-regular full-duration lower bound follows from the
individual local transitions, uniformly for every prescribed starting point. -/
theorem b_original_setwise_lower_of_local_steps (hlocal : bCouplingLocalStepInput) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
      ∃ c : ℝ, 0 < c ∧ ∀ (Q : EnvironmentLaw d Λ r)
        (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le h₁ P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) • (volume : Measure (Vec d)).restrict
              (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ)) := by
  intro d hd Λ r l hl
  obtain ⟨a, ha, hstep⟩ := hlocal d hd Λ r l hl
  obtain ⟨c, hc, hchain⟩ := b_coupling_setwise_of_local_chain a l ha
    (lt_of_lt_of_le zero_lt_one hl)
  refine ⟨c, hc, ?_⟩
  intro Q μ hμ h₁
  obtain ⟨P, hP, _, _, _⟩ := SbxASection3R04.global_reduced_kernel_exists hd Q μ hμ.le h₁
  refine ⟨P, hP, ?_⟩
  filter_upwards [hP] with ω hω
  obtain ⟨hω, G, hG⟩ := hω
  intro x
  rw [hG x]
  exact hchain μ hμ G x (hstep Q μ hμ h₁ ω hω G x)

/-- Original all-regular full-duration coupling lower bound. -/
theorem b_original_setwise_lower :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ), 1 ≤ l →
      ∃ c : ℝ, 0 < c ∧ ∀ (Q : EnvironmentLaw d Λ r)
        (μ : ℝ) (hμ : 0 < μ) (h₁ : μ ≤ 1),
        ∃ P : QuenchedPathLaws d,
          IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le h₁ P ∧
          ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
            ENNReal.ofReal (c * μ ^ d) • (volume : Measure (Vec d)).restrict
              (endpointBall (Renewal.forceCoord hd) (l / μ) x) ≤
            ((P (x, ω)).restrict {γ | ∀ t : ℝ≥0, t ≤ Renewal.regenDelta μ →
              γ t ∈ couplingRegion (Renewal.forceCoord hd) (l / μ) x}).map
                (fun γ => γ (Renewal.regenDelta μ)) :=
  b_original_setwise_lower_of_local_steps b_coupling_local_steps

#print axioms b_coupling_local_steps
#print axioms b_original_setwise_lower

#print axioms b_coupling_setwise_of_local_chain
#print axioms b_original_setwise_lower_of_local_steps
end
end EinsteinFull
