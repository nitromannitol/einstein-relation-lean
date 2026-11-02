import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinFull.Calculus.FellerRegularSet
import EinsteinFull.Calculus.ParabolicLibraryBridgeAffine
import EinsteinRelation.Correctors.WeakGradientCentering

open MeasureTheory Filter EinsteinRelation EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- A time-independent bounded density annihilates the time derivative of a
smooth compactly supported test. -/
theorem c11_density_time_derivative_integral_zero {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Measurable ρ) (C : ℝ)
    (hbound : ∀ x, ‖ρ x‖ ≤ C) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∫ z, ρ z.2 * fderiv ℝ ψ z (1, 0) = 0 := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  have hD : Continuous D := (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDc : HasCompactSupport D := hc.fderiv_apply ℝ (1, 0)
  have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport hDc
  have hmul : Integrable (fun z : ℝ × Vec d => D z * ρ z.2) volume :=
    hDi.mul_bdd (c := C) (hρ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hbound z.2)
  have hmul' : Integrable (fun z : ℝ × Vec d => ρ z.2 * D z) volume := by
    simpa only [mul_comm] using hmul
  rw [Measure.volume_eq_prod] at hmul' ⊢
  rw [MeasureTheory.integral_prod_symm _ hmul']
  have hzero : ∀ x : Vec d, (∫ t : ℝ, ρ x * D (t, x)) = 0 := by
   intro x
   rw [integral_const_mul]
   have hs : HasCompactSupport (fun t : ℝ => ψ (t, x)) := by
     have hK : IsCompact (Prod.fst '' tsupport ψ) := hc.image continuous_fst
     refine hK.of_isClosed_subset isClosed_closure (closure_minimal ?_ hK.isClosed)
     intro t ht
     exact ⟨(t,x), subset_tsupport ψ ht, rfl⟩
   have hsm : ContDiff ℝ 1 (fun t : ℝ => ψ (t, x)) :=
     hψ1.comp (contDiff_id.prodMk contDiff_const)
   have he (t : ℝ) : deriv (fun s : ℝ => ψ (s, x)) t = D (t,x) := by
     exact (((hψ1.differentiable (by norm_num)) (t,x)).hasFDerivAt.comp_hasDerivAt t
       ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))).deriv
   have hz := EinsteinFull.ParabolicBridge.integral_fderiv_eq_zero_of_compactSupport (μ := volume) hsm hs (1 : ℝ)
   simp only [fderiv_apply_one_eq_deriv] at hz
   simp_rw [he] at hz
   rw [hz, mul_zero]

  simp only [hzero, integral_zero]

/-- The same cancellation on a cylinder containing the test support. -/
theorem c11_density_time_derivative_integral_zero_on {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Measurable ρ) (C : ℝ)
    (hbound : ∀ x, ‖ρ x‖ ≤ C) (I : Set ℝ) (U : Set (Vec d))
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ I ×ˢ U) :
    ∫ z in I ×ˢ U, ρ z.2 * fderiv ℝ ψ z (1, 0) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact c11_density_time_derivative_integral_zero ρ hρ C hbound ψ hψ hc
  · intro z hz
    have hzs : z ∉ tsupport ψ := fun hz' => hz (hs hz')
    simp only [fderiv_of_notMem_tsupport (𝕜 := ℝ) hzs, ContinuousLinearMap.zero_apply,
      mul_zero]

/-- Subtracting a constant preserves the native weighted equation on a finite cylinder. -/
theorem c11_weighted_caloric_sub_const {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} (hfinite : volume (I ×ˢ U) ≠ ⊤)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (c : ℝ) :
    IsWeightedCaloric ρ α I U (fun z => u z - c) G := by
  have hρbound (x : Vec d) : ‖ρ x‖ ≤ κ⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hκ.le (hell.2.2 x).1)]
    exact (hell.2.2 x).2.1
  let μ := volume.restrict (I ×ˢ U)
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using (lt_top_iff_ne_top.mpr hfinite)⟩
  refine ⟨hu.1.sub (memLp_const c), hu.2.1, hu.2.2.1, ?_, ?_⟩
  · filter_upwards [hu.2.2.2.1] with t ht
    exact EinsteinRelation.Correctors.hasWeakGradient_sub_const U ht c
  · intro ψ hψ hc hs
    let D : ℝ × Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hD : Continuous D := (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hDc : HasCompactSupport D := hc.fderiv_apply ℝ (1, 0)
    have hDi : Integrable D volume := hD.integrable_of_hasCompactSupport hDc
    have hDρ : Integrable (fun z : ℝ × Vec d => D z * ρ z.2) volume :=
      hDi.mul_bdd (c := κ⁻¹) (hell.1.comp measurable_snd).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => hρbound z.2)
    have hρD : Integrable (fun z : ℝ × Vec d => ρ z.2 * D z) volume := by
      simpa only [mul_comm] using hDρ
    have hcorr : Integrable (fun z : ℝ × Vec d => c * (ρ z.2 * D z)) μ :=
      (hρD.const_mul c).integrableOn
    have hzero : ∫ z in I ×ˢ U, ρ z.2 * D z = 0 :=
      c11_density_time_derivative_integral_zero_on ρ hell.1 κ⁻¹ hρbound I U ψ hψ hc
        (hs.trans (Set.prod_mono interior_subset (fun _ h => h)))
    let F : ℝ × Vec d → ℝ := fun z =>
      -(ρ z.2 * u z) * D z + dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0, unitVector j))
    have heq : (fun z : ℝ × Vec d =>
        -(ρ z.2 * (u z - c)) * D z + dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) =
        fun z => F z + c * (ρ z.2 * D z) := by
      funext z
      dsimp [F]
      ring
    change ∫ z, (-(ρ z.2 * (u z - c)) * D z + dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ ψ z (0, unitVector j))) ∂μ = 0
    rw [heq]
    by_cases hF : Integrable F μ
    · rw [integral_add hF hcorr, integral_const_mul, hzero, mul_zero, add_zero]
      exact hu.2.2.2.2 ψ hψ hc hs
    · have hsum : ¬ Integrable (fun z => F z + c * (ρ z.2 * D z)) μ := by
        intro h
        apply hF
        convert h.sub hcorr using 1
        ext z
        simp
      exact integral_undef hsum

/-- The actual clock-weighted solution remains in the same local L² space. -/
theorem c11_weighted_caloric_density_memLp {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hcal : IsWeightedCaloric ρ α I U u G) :
    MemLp (fun z => ρ z.2 * u z) 2 (volume.restrict (I ×ˢ U)) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Vec d => ρ z.2)
      (volume.restrict (I ×ˢ U)) := (hell.1.comp measurable_snd).aestronglyMeasurable
  apply (hcal.1.norm.const_mul κ⁻¹).mono' (hm.mul hcal.1.aestronglyMeasurable)
  filter_upwards with z
  change |ρ z.2 * u z| ≤ κ⁻¹ * ‖u z‖
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (le_trans hκ.le (hell.2.2 z.2).1)]
  exact mul_le_mul_of_nonneg_right (hell.2.2 z.2).2.1 (abs_nonneg _)

/-- A continuous representative of a function that vanishes almost everywhere in the
past also vanishes at time zero throughout the smaller ball. -/
theorem c11_zero_past_continuous_representative_at_zero {d : ℕ}
    (u v : ℝ × Vec d → ℝ)
    (hv : ContinuousOn v (Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2)))
    (heq : v =ᵐ[volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ sourceBall 0 (1/2))] u)
    (hz : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall 0 1), u z = 0) :
    ∀ y ∈ sourceBall (0 : Vec d) (1/2), v (0,y) = 0 := by
  let B := sourceBall (0 : Vec d) (1/2)
  let S := Set.Ioo (-1/4 : ℝ) 0 ×ˢ B
  let T := Set.Ioc (-1/4 : ℝ) 0 ×ˢ B
  have hB : IsOpen B := isOpen_lt
    ((Feller.continuous_euclideanNorm d).comp (continuous_id.sub continuous_const))
    continuous_const
  have hsub : S ⊆ Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ B := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨ht.1, by linarith [ht.2]⟩, hx⟩
  have hsubpast : S ⊆ Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall 0 1 := by
    rintro ⟨t, x⟩ ⟨ht, hx⟩
    exact ⟨⟨by linarith [ht.1], ht.2⟩, by
      change euclideanNorm (x - 0) < 1 at ⊢
      change euclideanNorm (x - 0) < 1/2 at hx
      linarith⟩
  have hae : v =ᵐ[volume.restrict S] (fun _ => 0) := by
    have h₁ := ae_restrict_of_ae_restrict_of_subset hsub heq
    have h₂ := ae_restrict_of_ae_restrict_of_subset hsubpast hz
    filter_upwards [h₁, h₂] with z hz₁ hz₂
    exact hz₁.trans hz₂
  have hpoint : Set.EqOn v (fun _ => 0) S :=
    Measure.eqOn_open_of_ae_eq hae (isOpen_Ioo.prod hB) (hv.mono hsub)
      continuousOn_const
  have hTsub : T ⊆ Set.Ioo (-1/4 : ℝ) (1/4) ×ˢ B := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    exact ⟨⟨ht.1, by linarith [ht.2]⟩,hx⟩
  have hST : S ⊆ T := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    exact ⟨⟨ht.1, ht.2.le⟩, hx⟩
  have hTS : T ⊆ closure S := by
    rw [show closure S = closure (Set.Ioo (-1/4 : ℝ) 0) ×ˢ closure B from closure_prod_eq]
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    rw [closure_Ioo (by norm_num : (-1/4 : ℝ) ≠ 0)]
    exact ⟨⟨ht.1.le, ht.2⟩, subset_closure hx⟩
  have hzero := hpoint.of_subset_closure (hv.mono hTsub) continuousOn_const hST hTS
  intro y hy
  exact hzero (show ((0 : ℝ), y) ∈ T from ⟨⟨by norm_num, le_rfl⟩, hy⟩)

end EinsteinFull.Calculus
