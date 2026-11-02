import EinsteinFull.Calculus.C13TubeNativeC2Energy
import EinsteinFull.Calculus.C5TubeSignedUnitMomentGain
import EinsteinFull.Calculus.C11TubeSymmetricTruncationFiniteness

open EinsteinRelation PDE MeasureTheory EinsteinFull.External.Source.GMP
open PDE.Parabolic.LocalMax
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The dissipation in a bounded-curvature cutoff energy is integrable on the
native weighted caloric cylinder. -/
theorem c20_cutoff_dissipation_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (EinsteinRelation.Vec d)}
    {u : ℝ × EinsteinRelation.Vec d → ℝ} {G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d}
    (hcal : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (M : ℝ) (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    Integrable (fun z => χ z.2 ^ 2 * deriv (deriv F) (u z) *
      dot ((α z.2).mulVec (G z)) (G z)) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  obtain ⟨C, hC, hbound⟩ := (hχc.isCompact_range hχ.continuous).isBounded.exists_pos_norm_le
  have hχtop : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2) ∞ μ := by
    apply memLp_top_of_bound (hχ.continuous.comp continuous_snd).aestronglyMeasurable C
    exact ae_of_all μ (fun z => hbound _ ⟨z.2, rfl⟩)
  have hsq : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 ^ 2) ∞ μ := by
    have hp : MemLp (fun z : ℝ × EinsteinRelation.Vec d => χ z.2 * χ z.2) ∞ μ := hχtop.mul hχtop
    simpa only [pow_two] using hp
  have hi := (c11_weighted_caloric_second_chain_flux_integrable hκ hell hcal F hF M hder).mul_of_top_right hsq
  convert hi using 1
  funext z
  simp only [Pi.mul_apply]
  ring

/-- The cutoff-gradient cost of a fixed signed truncation is integrable. -/
theorem c20_signed_truncation_cutoff_cost_integrable {d : ℕ}
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    {I : Set ℝ} {U : Set (EinsteinRelation.Vec d)}
    {u : ℝ × EinsteinRelation.Vec d → ℝ} {G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d}
    (hcal : IsWeightedCaloric ρ α I U u G) (hfinite : volume (I ×ˢ U) < ∞)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    Integrable (fun z => (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) (volume.restrict (I ×ˢ U)) := by
  let μ := volume.restrict (I ×ˢ U)
  haveI : IsFiniteMeasure μ := ⟨by simpa [μ] using hfinite⟩
  have hf := c11_symmetric_truncation_integrable_of_memLp_two μ u hcal.1 p ε hp hε n
  have hDtop (i : Fin d) : MemLp (fun z : ℝ × EinsteinRelation.Vec d =>
      fderiv ℝ χ z.2 (unitVector i)) ∞ μ := by
    have hd : Continuous (fun x : EinsteinRelation.Vec d => fderiv ℝ χ x (unitVector i)) :=
      (hχ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
    obtain ⟨B, hB, hb⟩ :=
      ((hχc.fderiv_apply ℝ (unitVector i)).isCompact_range hd).isBounded.exists_pos_norm_le
    apply memLp_top_of_bound (hd.comp continuous_snd).aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z.2, rfl⟩)
  have ht (i : Fin d) : Integrable (fun z : ℝ × EinsteinRelation.Vec d =>
      (powF p ε (n : ℝ) (u z) + powF p ε (n : ℝ) (-u z)) *
        (fderiv ℝ χ z.2 (unitVector i) * fderiv ℝ χ z.2 (unitVector i))) μ :=
    by
      convert hf.mul_of_top_right ((hDtop i).mul (hDtop i)) using 1
      funext z
      simp only [Pi.mul_apply]
      ring
  convert integrable_finsetSum Finset.univ (fun i _ => ht i) using 1
  funext z
  simp only [euclideanSq, dot, Finset.mul_sum]


/-- The symmetric truncation has bounded curvature. -/
theorem c20_signed_truncation_regular (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    let F := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s) - 2 * powF p ε (n : ℝ) 0
    ContDiff ℝ 2 F ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ s, |deriv (deriv F) s| ≤ M := by
  dsimp only
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hF : ContDiff ℝ 2 (fun s => f s + f (-s) - 2 * f 0) := by
    change ContDiff ℝ 2 (fun s => f s + f (-s) - 2 * f 0)
    exact (hf.add (hf.comp contDiff_neg)).sub contDiff_const
  obtain ⟨C, hC⟩ := exists_powF2_bound (p := p) (by linarith : 1 < p) hε (Nat.cast_nonneg n)
  have hd : ∀ s, deriv (deriv (fun s => f s + f (-s) - 2 * f 0)) s = deriv (deriv f) s + deriv (deriv f) (-s) := by
    intro s
    have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hdf : Differentiable ℝ (deriv f) :=
      (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
    have hfirst : deriv (fun x => f x + f (-x) - 2 * f 0) =
        (fun x => deriv f x - deriv f (-x)) := by
      funext x
      change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) x = _
      rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
        (differentiableAt_const _), deriv_add hf'.differentiableAt
        (hf'.comp differentiable_neg).differentiableAt]
      change deriv f x + deriv (fun y => f (-y)) x - deriv (fun _ => 2 * f 0) x = _
      rw [deriv_comp_neg, deriv_const]
      ring
    rw [hfirst]
    change deriv (deriv f - (deriv f ∘ Neg.neg)) s = _
    rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
    change deriv (deriv f) s - deriv (fun x => deriv f (-x)) s = _
    rw [deriv_comp_neg, sub_neg_eq_add]
  refine ⟨hF, 2 * (C : ℝ), by positivity, ?_⟩
  intro s
  rw [hd]
  calc
    |deriv (deriv f) s + deriv (deriv f) (-s)| ≤
        |deriv (deriv f) s| + |deriv (deriv f) (-s)| := abs_add_le _ _
    _ ≤ 2 * (C : ℝ) := by have h₁ := hC s; have h₂ := hC (-s); dsimp [f]; linarith

/-- Pointwise absorption of the native signed cutoff flux. -/
theorem c20_signed_truncated_cutoff_flux_lower {d : ℕ} {κ p ε : ℝ}
    (hκ : 0 < κ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    {ρ : EinsteinRelation.Vec d → ℝ} {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (χ : EinsteinRelation.Vec d → ℝ) (q : ℝ) (x : EinsteinRelation.Vec d) :
    let f := powF p ε (n : ℝ)
    let F := fun s => f s + f (-s) - 2 * f 0
    (1 / 2 : ℝ) * χ x ^ 2 * deriv (deriv F) (u (q,x)) *
        dot (G (q,x)) ((α x).mulVec (G (q,x))) -
      (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))) *
        (f (u (q,x)) + f (-u (q,x))) *
        euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤
    χ x ^ 2 * deriv (deriv F) (u (q,x)) *
        dot ((α x).mulVec (G (q,x))) (G (q,x)) +
      2 * χ x * deriv F (u (q,x)) *
        dot ((α x).mulVec (G (q,x))) (fun j => fderiv ℝ χ x (unitVector j)) := by
  dsimp only
  have h := c5_symmetric_truncated_energy_cross_bound hκ hp hε n hell x
    (G (q,x)) (fun j => fderiv ℝ χ x (unitVector j)) (u (q,x)) (χ x)
  dsimp only at h
  have hswap : dot ((α x).mulVec (G (q,x))) (G (q,x)) =
      dot (G (q,x)) ((α x).mulVec (G (q,x))) := by
    simp only [dot, mul_comm]
  rw [hswap]
  have hl := neg_le_of_abs_le h
  nlinarith only [hl]


/-- The signed cutoff energy inequality holds on almost every time slice. -/
theorem c20_signed_truncation_spatial_energy_bound {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) :
    let f := powF p ε (n : ℝ)
    let F := fun s => f s + f (-s) - 2 * f 0
    ∀ᵐ q ∂volume.restrict (Set.Ioo a b),
      (1 / 2 : ℝ) * (∫ x in sourceBall 0 R, χ x ^ 2 * deriv (deriv F) (u (q,x)) *
        dot ((α x).mulVec (G (q,x))) (G (q,x))) ≤
      (∫ x in sourceBall 0 R, χ x ^ 2 * deriv (deriv F) (u (q,x)) *
        dot ((α x).mulVec (G (q,x))) (G (q,x)) +
        2 * χ x * deriv F (u (q,x)) * dot ((α x).mulVec (G (q,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) +
      (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))) *
        (∫ x in sourceBall 0 R, (f (u (q,x)) + f (-u (q,x))) *
          euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  dsimp only
  let f := powF p ε (n : ℝ)
  let F := fun s => f s + f (-s) - 2 * f 0
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : EinsteinRelation.Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : EinsteinRelation.Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  obtain ⟨hF, M, hM, hder⟩ := c20_signed_truncation_regular p ε hp hε n
  have hd := c20_cutoff_dissipation_integrable hκ hell hcal F hF M hder χ hχ hχc
  have hf := c13_C2_cutoff_flux_integrable hκ ρ α hell _ _ u G hcal hfinite F hF M hM hder χ hχ hχc
  have hc := c20_signed_truncation_cutoff_cost_integrable hcal hfinite p ε hp hε n χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hf hc
  filter_upwards [hd.prod_right_ae, hf.prod_right_ae, hc.prod_right_ae] with q hd' hf' hc'
  have hm := integral_mono_ae (hd'.const_mul (1 / 2 : ℝ))
    (hf'.add (hc'.const_mul (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))))) (by
      filter_upwards with x
      have h := c20_signed_truncated_cutoff_flux_lower hκ hp hε n hell u G χ q x
      dsimp only at h
      have hs : dot ((α x).mulVec (G (q,x))) (G (q,x)) =
          dot (G (q,x)) ((α x).mulVec (G (q,x))) := by simp only [dot, mul_comm]
      rw [hs]
      dsimp only [Pi.add_apply, Pi.mul_apply]
      linarith only [h])
  simpa only [Pi.add_apply, Pi.mul_apply, integral_const_mul,
    integral_add hf' (hc'.const_mul (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))))] using hm


theorem c20_signed_truncated_integrated_energy_of_eq {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (F : ℝ → ℝ)
    (hF_eq : F = fun s => PDE.Parabolic.LocalMax.powF p ε (n:ℝ) s + PDE.Parabolic.LocalMax.powF p ε (n:ℝ) (-s) - 2*PDE.Parabolic.LocalMax.powF p ε (n:ℝ) 0)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        E t + (1/2 : ℝ) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * deriv (deriv F) (u (q,x)) *
            dot (G (q,x)) ((α x).mulVec (G (q,x)))) ≤
        E s + (2 * κ⁻¹ * (2 * (2 + p/(p-1)))) *
          (∫ q in s..t, ∫ x in sourceBall 0 R,
            (powF p ε (n:ℝ) (u (q,x)) + powF p ε (n:ℝ) (-u (q,x))) *
              euclideanSq (fun j => fderiv ℝ χ x (unitVector j))) := by
  subst F
  let f := powF p ε (n : ℝ)
  let F := fun s => f s + f (-s) - 2 * f 0
  obtain ⟨E, hEc, hEae, hEdiff⟩ :=
    c5_signed_truncated_C2_continuous_energy_of_eq hκ hR hab ρ α hell u G hcal p ε hp hε n F rfl χ hχ hχc hχU
  refine ⟨E, hEc, hEae, ?_⟩
  intro s hs t ht hst
  let D : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * deriv (deriv F) (u (q,x)) * dot ((α x).mulVec (G (q,x))) (G (q,x))
  let Q : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    χ x ^ 2 * deriv (deriv F) (u (q,x)) * dot ((α x).mulVec (G (q,x))) (G (q,x)) +
      2 * χ x * deriv F (u (q,x)) * dot ((α x).mulVec (G (q,x)))
        (fun j => fderiv ℝ χ x (unitVector j))
  let C : ℝ → ℝ := fun q => ∫ x in sourceBall 0 R,
    (f (u (q,x)) + f (-u (q,x))) * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))
  have hsub : Set.Icc s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_of_lt_of_le hs.1 hq.1, lt_of_le_of_lt hq.2 ht.2⟩
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : EinsteinRelation.Vec d) R)
  haveI : IsFiniteMeasure μ := c20_sourceCylinder_isFiniteMeasure a b R 0
  have hfinite : volume (Set.Ioo a b ×ˢ sourceBall (0 : EinsteinRelation.Vec d) R) < ∞ := by
    simpa [μ] using (measure_lt_top μ Set.univ)
  obtain ⟨hF, M, hM, hder⟩ := c20_signed_truncation_regular p ε hp hε n
  have hd := c20_cutoff_dissipation_integrable hκ hell hcal F hF M hder χ hχ hχc
  have hq := c13_C2_cutoff_flux_integrable hκ ρ α hell _ _ u G hcal hfinite F hF M hM hder χ hχ hχc
  have hc := c20_signed_truncation_cutoff_cost_integrable hcal hfinite p ε hp hε n χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hd hq hc
  have hD : IntegrableOn D (Set.Ioo a b) volume := hd.integral_prod_left
  have hQ : IntegrableOn Q (Set.Ioo a b) volume := hq.integral_prod_left
  have hC : IntegrableOn C (Set.Ioo a b) volume := hc.integral_prod_left
  have hdi : IntervalIntegrable D volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hD.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hqi : IntervalIntegrable Q volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hQ.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hci : IntervalIntegrable C volume s t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hst]
    exact hC.mono_set (Set.Ioc_subset_Icc_self.trans hsub)
  have hbound : ∀ᵐ q ∂volume.restrict (Set.Icc s t),
      (1 / 2 : ℝ) * D q ≤ Q q + (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))) * C q :=
    (c20_signed_truncation_spatial_energy_bound hκ ρ α hell u G hcal p ε hp hε n χ hχ hχc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hm := intervalIntegral.integral_mono_ae_restrict hst (hdi.const_mul (1 / 2 : ℝ))
    (hqi.add (hci.const_mul (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))))) hbound
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hqi (hci.const_mul (2 * κ⁻¹ * (2 * (2 + p / (p - 1))))),
    intervalIntegral.integral_const_mul] at hm
  have hdiff := hEdiff s hs t ht
  change E t - E s = -(∫ q in s..t, Q q) at hdiff
  have hswap : ∀ q x, dot (G (q,x)) ((α x).mulVec (G (q,x))) =
      dot ((α x).mulVec (G (q,x))) (G (q,x)) := by
    intro q x
    simp only [dot, mul_comm]
  simp_rw [hswap]
  change E t + (1 / 2 : ℝ) * (∫ q in s..t, D q) ≤
    E s + (2 * κ⁻¹ * (2 * (2 + p / (p - 1)))) * (∫ q in s..t, C q)
  linarith


end EinsteinFull.Calculus
