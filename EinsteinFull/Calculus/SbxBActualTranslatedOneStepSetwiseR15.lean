import EinsteinFull.Calculus.SbxAKilledChainDominationR09
import EinsteinFull.Calculus.SbxS4KilledTranslationR02
import EinsteinFull.Calculus.SbxBNormalizedPhysicalNativeRowR13
import EinsteinFull.Calculus.SbxBActualNativeLowerTransferR11
import EinsteinFull.Calculus.SbxBTranslatedNativeLocalStepR15
import EinsteinFull.Calculus.SbxACouplingInteriorChainR09
import EinsteinRelation.Regeneration.KilledSegmentLocality

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP EinsteinFull.Blueprint.TubeProbability

/-- Translate a centered killed-row estimate and enlarge the killing domain. -/
theorem b_translated_killed_setwise_mono_r15 {d : ℕ} (hd : 2 ≤ d)
    (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular L (translate z ω))
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (s : GantertFixedEnvironmentRealization hd L hL (translate z ω) hωz lam h0 h1)
    (R : ℝ) (U : Set (Vec d)) (hU : IsOpen U)
    (hsub : (fun x : Vec d => x - z) ⁻¹' sourceBall 0 R ⊆ U)
    (V : Set (Vec d)) (hV : MeasurableSet V) (t : ℝ≥0) (x : Vec d)
    (a : ℝ≥0∞)
    (hlower : a • (volume : Measure (Vec d)).restrict V ≤
      gmpKilledEndpointKernel s (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t x) :
    a • (volume : Measure (Vec d)).restrict ((fun y : Vec d => y - z) ⁻¹' V) ≤
      gmpKilledEndpointKernel r U hU t (x + z) := by
  let W : Set (Vec d) := (fun y : Vec d => y - z) ⁻¹' sourceBall 0 R
  have hW : IsOpen W := (dirichletBall (d := d) R).isOpen.preimage (continuous_id.sub continuous_const)
  have hpre : (fun y : Vec d => y + z) ⁻¹' W = sourceBall 0 R := by
    ext y
    simp [W]
  have hrow := s4_supplied_killed_endpoint_translation hd L hL ω hω lam h0 h1 z hωz r s W hW t x
  have hrow' : gmpKilledEndpointKernel s (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t x =
      (gmpKilledEndpointKernel r W hW t (x + z)).map (fun y => y - z) := by
    simpa only [hpre] using hrow
  let f : Vec d → Vec d := fun y => y + z
  have hf : Measurable f := (continuous_id.add continuous_const).measurable
  have hg : Measurable (fun y : Vec d => y - z) := (continuous_id.sub continuous_const).measurable
  have hmap := Measure.map_mono hlower hf
  rw [hrow', Measure.map_map hf hg] at hmap
  have hcomp : f ∘ (fun y : Vec d => y - z) = id := by
    funext y
    simp [f]
  rw [hcomp, Measure.map_id] at hmap
  have hvol : Measure.map f (volume : Measure (Vec d)) = volume := map_add_right_eq_self volume z
  rw [Measure.map_smul _ hf.aemeasurable] at hmap
  have heq : Measure.map f ((volume : Measure (Vec d)).restrict V) =
      (volume : Measure (Vec d)).restrict ((fun y : Vec d => y - z) ⁻¹' V) := by
    have hp : f ⁻¹' ((fun y : Vec d => y - z) ⁻¹' V) = V := by
      ext y
      simp [f]
    calc
      _ = Measure.map f ((volume : Measure (Vec d)).restrict
          (f ⁻¹' ((fun y : Vec d => y - z) ⁻¹' V))) := by rw [hp]
      _ = (Measure.map f volume).restrict ((fun y : Vec d => y - z) ⁻¹' V) :=
        (Measure.restrict_map hf (hV.preimage hg)).symm
      _ = _ := by rw [hvol]
  rw [heq] at hmap
  exact hmap.trans (a_gmpKilledEndpointKernel_mono_domain r W U hW hU hsub t (x + z))

/-- A normalized native pointwise estimate yields the actual translated
one-step bound on every start in the previous window. -/
theorem b_actual_translated_one_step_setwise_r15
    {d : ℕ} (hd : 2 ≤ d) (κ b : ℝ) (hκ : 0 < κ) (hb : 0 < b)
    (μ : ℝ) (hμ : 0 < μ)
    (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d) (hω : IsRegular L ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (z : Vec d)
    (hωz : IsRegular L (translate z ω))
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (s : GantertFixedEnvironmentRealization hd L hL (translate z ω) hωz lam h0 h1)
    (R : ℝ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd (translate z ω) lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd (translate z ω) lam x)
    (hrep : BNormalizedPhysicalScalingIsometry hd (translate z ω) lam L R hωz ρ c)
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
    have hy' := hVinside (y + z) hy
    simpa using hy'
  have hpoint : ∀ y ∈ V', b * μ ^ d ≤ K t y (x - z) / ρ (x - z) := by
    intro y hy
    simpa using hlower x hx (y + z) hy
  have hcenter : ENNReal.ofReal ((κ * b) * μ ^ d) •
      (volume : Measure (Vec d)).restrict V' ≤
      gmpKilledEndpointKernel s (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t (x - z) := by
    rw [b_normalized_every_start_supplied_row_of_scaling_isometry s hκ hR c hc hell hcoeff
      hrep hK t ht (x - z) (hA x hx), ← withDensity_const, ← withDensity_indicator hV']
    apply withDensity_mono
    filter_upwards with y
    by_cases hy : y ∈ V'
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (hVsub hy)]
      apply ENNReal.ofReal_le_ofReal
      have hrho : κ ≤ ρ y := (hell.2.2 y).1
      have hp : 0 ≤ b * μ ^ d := (mul_pos hb (pow_pos hμ _)).le
      have hmul := mul_le_mul hrho (hpoint y hy) hp (hκ.le.trans hrho)
      calc
        (κ * b) * μ ^ d = κ * (b * μ ^ d) := by ring
        _ ≤ ρ y * (K t y (x - z) / ρ (x - z)) := hmul
        _ = (ρ y / ρ (x - z)) * K t y (x - z) := by ring
    · simp [hy]
  have h := b_translated_killed_setwise_mono_r15 hd L hL ω hω lam h0 h1 z hωz r s
    R U hU hsub V' hV' t (x - z) _ hcenter
  have heq : (fun y : Vec d => y - z) ⁻¹' V' = V := by
    ext y
    simp [V']
  simpa only [heq, sub_add_cancel] using h

/-- The translated actual-coefficient case needs no normalization premise.
The native pointwise input is stated at the scaled one-step strength. -/
theorem b_actual_translated_one_step_setwise_of_physical_coefficients_r15
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
theorem b_actual_translated_uniform_one_step_r15
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
  exact b_actual_translated_one_step_setwise_of_physical_coefficients_r15 hd κ b hκ hb
    μ hμ L hL ω hω μ hμ.le hμ1 z hωz r s R hR hell' hcoeff hK
    U hU hsub A V hV hA hVin (T/μ^2).toNNReal ht' hpoint

/-- The actual killed row dominates the next integration ball in the
interior coupling chain, uniformly over all regular environments. -/
theorem b_actual_coupling_one_step_setwise_r15
    (d : ℕ) (hd : 2 ≤ d) (L l T : ℝ)
    (hL : 1 ≤ L) (hl : 0 < l) (hT : 0 < T) :
    ∃ a : ℝ, 0 < a ∧ ∀ (μ D : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1),
    0 < D → l = μ * D →
    ∀ (ω : FieldPair d) (hω : IsRegular L ω)
      (r : GantertFixedEnvironmentRealization hd L hL ω hω μ hμ.le hμ1)
      (i : Fin d) (x y : Vec d), y ∈ EinsteinRelation.Regeneration.endpointBall i D x →
    ∀ (n k : ℕ), 80 ≤ n → k ≤ n →
    ∀ p ∈ sourceBall (Calculus.b_tube_segment_center x y n k) (D/16),
      ENNReal.ofReal (a * μ^d) • (volume : Measure (Vec d)).restrict
        (sourceBall (Calculus.b_tube_segment_center x y n (k+1)) (D/16)) ≤
      gmpKilledEndpointKernel r (EinsteinRelation.Regeneration.couplingRegion i D x)
        (EinsteinRelation.Regeneration.isOpen_couplingRegion i D x) (T/μ^2).toNNReal p := by
  obtain ⟨a, ha, hstep⟩ := b_actual_translated_uniform_one_step_r15
    d hd L (l/2) T hL (by positivity) hT
  refine ⟨a, ha, ?_⟩
  intro μ D hμ hμ1 hD hscale ω hω r i x y hy n k hn hk p hp
  let z := Calculus.b_tube_segment_center x y n k
  let z' := Calculus.b_tube_segment_center x y n (k+1)
  have hz : z ∈ sourceBall z (D/16) := by
    change euclideanNorm (z-z) < D/16
    simp [euclideanNorm, euclideanSq, dot, hD]
  have hz' : z' ∈ sourceBall z' (D/16) := by
    change euclideanNorm (z'-z') < D/16
    simp [euclideanNorm, euclideanSq, dot, hD]
  have hA (w : Vec d) (hw : w ∈ sourceBall z (D/16)) : w ∈ sourceBall z (D/4) :=
    (Calculus.a_coupling_consecutive_inner_ball i D x y hD hy n k hn w z' hw hz').1
  have hV (w : Vec d) (hw : w ∈ sourceBall z' (D/16)) : w ∈ sourceBall z (D/4) :=
    (Calculus.a_coupling_consecutive_inner_ball i D x y hD hy n k hn z w hz hw).2
  have hnorm (w : Vec d) (hw : w ∈ sourceBall z (D/4)) :
      w-z ∈ sourceBall 0 (D/2) ∧ μ • (w-z) ∈ sourceBall 0 ((l/2)/2) := by
    change euclideanNorm (w-z) < D/4 at hw
    constructor
    · change euclideanNorm (w-z-0) < D/2
      simp only [sub_zero]
      linarith
    · change euclideanNorm (μ • (w-z)-0) < (l/2)/2
      rw [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos hμ, hscale]
      have hm := mul_lt_mul_of_pos_left hw hμ
      nlinarith
  have hsub : (fun w : Vec d => w-z) ⁻¹' sourceBall 0 (D/2) ⊆
      EinsteinRelation.Regeneration.couplingRegion i D x := by
    apply Set.Subset.trans _ (Calculus.a_coupling_equispaced_margin i D x y hD hy n k (by omega) hk)
    intro w hw
    change euclideanNorm (w-z-0) < D/2 at hw
    change euclideanNorm (w-z) < D/2
    simpa only [sub_zero] using hw
  have hmeas : MeasurableSet (sourceBall z' (D/16)) := by
    have ho := (dirichletBall (d := d) (D/16)).isOpen.preimage
      (continuous_id.sub (continuous_const : Continuous fun _ : Vec d => z'))
    convert ho.measurableSet using 1
    ext w
    simp [dirichletBall, sourceBall]
  apply hstep μ (D/2) hμ hμ1 (by positivity) (by rw [hscale]; ring)
    ω hω z r _ _ hsub (sourceBall z (D/16)) (sourceBall z' (D/16)) hmeas
      (fun w hw => (hnorm w (hA w hw)).1) (fun w hw => (hnorm w (hV w hw)).1)
      (fun w hw => (hnorm w (hA w hw)).2) (fun w hw => (hnorm w (hV w hw)).2) p hp

#print axioms b_actual_coupling_one_step_setwise_r15

#print axioms b_actual_translated_uniform_one_step_r15

#print axioms b_actual_translated_one_step_setwise_of_physical_coefficients_r15

#print axioms b_actual_translated_one_step_setwise_r15
end EinsteinFull
