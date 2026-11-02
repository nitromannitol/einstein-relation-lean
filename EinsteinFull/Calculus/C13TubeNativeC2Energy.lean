import EinsteinFull.Calculus.C13TubeGeneralChainAssembly
import EinsteinFull.Calculus.C11TubeWeightedLocalMax

open EinsteinRelation PDE MeasureTheory Filter Set EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The cutoff renormalized mass is integrable on a finite cylinder. -/
theorem c13_C2_cutoff_mass_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (I : Set ℝ) (U : Set (EinsteinRelation.Vec d)) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d) (hu : IsWeightedCaloric ρ α I U u G)
    (hfinite : volume (I ×ˢ U) < ∞) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M) (χ : EinsteinRelation.Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * F (u z))
      (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 ^ 2) ∞ μ := by
    have hp : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hm := c11_weighted_caloric_renormalized_mass_integrable hκ hell hu hfinite F hF M hM hder
  convert hm.mul_of_top_right hsq using 1
  funext z
  simp only [Pi.mul_apply]
  ring

/-- The signed cutoff flux for a bounded-second-derivative renormalization is integrable. -/
theorem c13_C2_cutoff_flux_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (I : Set ℝ) (U : Set (EinsteinRelation.Vec d)) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d) (hu : IsWeightedCaloric ρ α I U u G)
    (hfinite : volume (I ×ˢ U) < ∞) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 * deriv (deriv F) (u z) *
      dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j))) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hDtop (i : Fin d) : MemLp (fun z : ℝ × EinsteinRelation.Vec d =>
      fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    have hd : Continuous (fun x : EinsteinRelation.Vec d => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ :=
      ((hχc.fderiv_apply ℝ (unitVector i)).isCompact_range hd).isBounded.exists_pos_norm_le
    apply memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 ^ 2) ∞ μ := by
    have hp : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hfirst := (c11_weighted_caloric_second_chain_flux_integrable hκ hell hu F hF M hder).mul_of_top_right hsq
  have hF' : ContDiff ℝ 1 (deriv F) := PDE.Parabolic.Chain.contDiff_deriv_of_two hF
  have hDF : MemLp (fun z => deriv F (u z)) 2 μ :=
    (c11_weighted_caloric_spacetime_chain_memLp_finite hu hfinite (deriv F) hF' M hM hder).1
  have hflux := c11_weighted_caloric_flux_memLp hκ hell hu
  have hterm (i : Fin d) : Integrable (fun z : ℝ × EinsteinRelation.Vec d =>
      (χ z.2 * deriv F (u z) * fderiv ℝ χ z.2 (unitVector i)) *
        ((α z.2).mulVec (G z)) i) μ := by
    have hχDF : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 * deriv F (u z)) 2 μ := hχtop.mul hDF
    have hχDFD : MemLp (fun z : ℝ × EinsteinRelation.Vec d =>
        χ z.2 * deriv F (u z) * fderiv ℝ χ z.2 (unitVector i)) 2 μ := hχDF.mul (hDtop i)
    exact hχDFD.integrable_mul (hflux i)
  have hcross : Integrable (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 * deriv F (u z) *
      dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ χ z.2 (unitVector j))) μ := by
    convert integrable_finsetSum Finset.univ (fun i _ => hterm i) using 1
    funext z
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  convert hfirst.add (hcross.const_mul 2) using 1
  funext z
  simp only [Pi.add_apply, Pi.mul_apply]
  ring


/-- The actual weighted C² renormalized cutoff mass has a continuous time trace. -/
theorem c13_actual_weighted_C2_continuous_energy {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M) (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * deriv (deriv F) (u (r,x)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j))) := by
  let I := Set.Ioo a b
  let U := sourceBall (0 : EinsteinRelation.Vec d) R
  let μ := volume.restrict (I ×ˢ U)
  let A : ℝ × EinsteinRelation.Vec d → ℝ := fun z => ρ z.2 * χ z.2 ^ 2 * F (u z)
  let B : ℝ × EinsteinRelation.Vec d → ℝ := fun z =>
    χ z.2 ^ 2 * deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) +
    2 * χ z.2 * deriv F (u z) * dot ((α z.2).mulVec (G z))
      (fun j => fderiv ℝ χ z.2 (unitVector j))
  let f : ℝ → ℝ := fun t => ∫ x in U, A (t,x)
  let q : ℝ → ℝ := fun t => ∫ x in U, B (t,x)
  have : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (I ×ˢ U) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  have hA : Integrable A μ :=
    c13_C2_cutoff_mass_integrable hκ ρ α hell I U u G hcal hfinite F hF M hM hder χ hχ hχc
  have hB : Integrable B μ :=
    c13_C2_cutoff_flux_integrable hκ ρ α hell I U u G hcal hfinite F hF M hM hder χ hχ hχc
  have hp : (volume.restrict I).prod (volume.restrict U) = μ := by
    simp only [μ, Measure.prod_restrict, Measure.volume_eq_prod]
  have hAp : Integrable A ((volume.restrict I).prod (volume.restrict U)) := by rw [hp]; exact hA
  have hBp : Integrable B ((volume.restrict I).prod (volume.restrict U)) := by rw [hp]; exact hB
  have hf : IntegrableOn f I := hAp.integral_prod_left
  have hq : IntegrableOn q I := hBp.integral_prod_left
  have hw : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ I → ∫ t in I, f t * deriv η t = -∫ t in I, (-q t) * η t := by
    intro η hη hηc hηI
    let θ : ℝ × EinsteinRelation.Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
    obtain ⟨hθ, hθc, hθs⟩ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
    have hc := c13_actual_weighted_caloric_renormalization hκ hR hab ρ α hell u G hcal
      F hF hF0 M hM hder θ hθ hθc hθs
    have hηtop : MemLp (fun z : ℝ × EinsteinRelation.Vec d => η z.1) ∞ μ := by
      have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc (Measure.map Prod.fst μ)
      exact ht.comp_of_map measurable_fst.aemeasurable
    have hdtop : MemLp (fun z : ℝ × EinsteinRelation.Vec d => deriv η z.1) ∞ μ := by
      have ht := (hη.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
        hηc.deriv (Measure.map Prod.fst μ)
      exact ht.comp_of_map measurable_fst.aemeasurable
    have hAt : Integrable (fun z => deriv η z.1 * A z) μ := by
      convert hA.mul_of_top_left hdtop using 1
      funext z
      simp only [Pi.mul_apply]
      ring
    have hBt : Integrable (fun z => η z.1 * B z) μ := by
      convert hB.mul_of_top_left hηtop using 1
      funext z
      simp only [Pi.mul_apply]
      ring
    have heq : (∫ z in I ×ˢ U, -(deriv η z.1 * A z) + η z.1 * B z) = 0 := by
      convert hc using 1
      apply integral_congr_ae
      filter_upwards with z
      simp only [θ, A, B,
        c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
          (hχ.differentiable (by simp)),
        c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
          (hχ.differentiable (by simp))]
      have hdot : dot ((α z.2).mulVec (G z))
          (fun j => η z.1 * (2 * χ z.2 * fderiv ℝ χ z.2 (unitVector j))) =
          (2 * η z.1 * χ z.2) * dot ((α z.2).mulVec (G z))
            (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
        simp only [dot, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hdot]
      ring
    have hneg : Integrable (fun z => -(deriv η z.1 * A z)) μ := hAt.neg
    change (∫ z, (-(deriv η z.1 * A z)) + η z.1 * B z ∂μ) = 0 at heq
    rw [integral_add hneg hBt, integral_neg] at heq
    have hAtp : Integrable (fun z => deriv η z.1 * A z)
        ((volume.restrict I).prod (volume.restrict U)) := by rw [hp]; exact hAt
    have hBtp : Integrable (fun z => η z.1 * B z)
        ((volume.restrict I).prod (volume.restrict U)) := by rw [hp]; exact hBt
    have ha : (∫ z in I ×ˢ U, deriv η z.1 * A z) = ∫ t in I, deriv η t * f t := by
      change (∫ z, deriv η z.1 * A z ∂μ) = _
      rw [← hp, integral_prod _ hAtp]
      simp only [f, integral_const_mul]
    have hb : (∫ z in I ×ˢ U, η z.1 * B z) = ∫ t in I, η t * q t := by
      change (∫ z, η z.1 * B z ∂μ) = _
      rw [← hp, integral_prod _ hBtp]
      simp only [q, integral_const_mul]
    rw [ha, hb] at heq
    simp_rw [neg_mul, integral_neg]
    simp only [neg_neg]
    simp_rw [mul_comm (f _), mul_comm (q _)]
    linarith
  obtain ⟨C, hC⟩ := c13_w11_ae_eq_ac_representative hab hf hq.neg hw
  have hi : IntervalIntegrable (fun t => -q t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le]
    rw [IntegrableOn, ← Measure.restrict_congr_set (μ := volume) Ioo_ae_eq_Ioc]
    exact hq.neg
  refine ⟨fun t => C + ∫ r in a..t, -q r, ?_, ?_, ?_⟩
  · have hgcc : IntegrableOn (fun t => -q t) (Set.Icc a b) volume := by
      rw [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]
      exact hq.neg
    have hc : ContinuousOn (fun x => ∫ r in a..x, -q r) (Set.Icc a b) :=
      (intervalIntegral.continuousOn_primitive hgcc).congr
        (fun x hx => by rw [intervalIntegral.integral_of_le hx.1])
    exact (continuousOn_const.add hc).mono Set.Ioo_subset_Icc_self
  · exact hC.symm
  · intro s hs t ht
    have hs' : s ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨hs.1.le, hs.2.le⟩
    have ht' : t ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨ht.1.le, ht.2.le⟩
    have his := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs')
    have hit := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht')
    change (C + ∫ r in a..t, -q r) - (C + ∫ r in a..s, -q r) = -(∫ r in s..t, q r)
    have hadd := intervalIntegral.integral_interval_sub_left hit his
    calc
      _ = ∫ r in s..t, -q r := by linarith [hadd]
      _ = -(∫ r in s..t, q r) := intervalIntegral.integral_neg

end EinsteinFull.Calculus
