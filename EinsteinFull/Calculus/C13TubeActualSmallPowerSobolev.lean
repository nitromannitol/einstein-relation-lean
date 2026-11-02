import EinsteinFull.Calculus.C13TubeSmallPowerSobolev
import EinsteinFull.Calculus.C13TubeSmallPositivePower

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The small-power Sobolev gain with regularity derived from the caloric field. -/
theorem c13_actual_small_power_cutoff_sobolev_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1) →
    ∀ p ε : ℝ, 0 < p → p < 1 → 0 < ε →
    (∀ᵐ z ∂volume.restrict (I ×ˢ U), ε ≤ u z) →
    ∀ A E : ℝ≥0∞,
    let v : ℝ × Vec d → ℝ := fun z => η z * (u z) ^ (p / 2)
    let J : ℝ × Vec d → Vec d := fun z =>
      η z • ((p / 2 * (u z) ^ (p / 2 - 1)) • G z) +
        (u z) ^ (p / 2) • (fun j => fderiv ℝ η z (0, unitVector j))
    (∀ᵐ t ∂volume.restrict I, (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖v (t,x)‖ₑ ^ (2 : ℝ)) ≤ A) →
    AEMeasurable (fun z => ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z)))
      (volume.restrict (I ×ˢ U)) →
    (∫⁻ z in I ×ˢ U, ENNReal.ofReal (dot ((α z.2).mulVec (J z)) (J z))) ≤ E →
    (∫⁻ z in S, ENNReal.ofReal (u z) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E) := by
  obtain ⟨C, hC, hsob⟩ := c13_small_power_cutoff_sobolev_gain d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU hfinite u G hu η hη hcη K hK hKU hzero S hS hSI hηone p ε hp hp1 hε hpos A E v J hmass hEm henergy
  let F := c13SmallPositivePower ε (p / 2)
  have hF : ContDiff ℝ 1 F := (c13_small_positive_power_smooth hε).of_le (by simp)
  obtain ⟨M, hM, hb⟩ := c13_small_positive_power_bounded (p := p / 2) hε (by linarith) (by linarith)
  have hdF : ∀ r, |deriv F r| ≤ M := fun r => (hb r).1
  let V : ℝ × Vec d → ℝ := fun z => η z * F (u z)
  let H : ℝ × Vec d → Vec d := fun z => η z • (deriv F (u z) • G z) +
    F (u z) • (fun j => fderiv ℝ η z (0, unitVector j))
  have hvh := c11_weighted_caloric_spacetime_cutoff_chain_memLp hu hfinite F hF M hM hdF η hη hcη
  have hHm : AEStronglyMeasurable H (volume.restrict (I ×ˢ U)) :=
    (hη.continuous.aestronglyMeasurable.smul
      ((hF.continuous_deriv_one.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).smul hu.2.1)).add
      ((hF.continuous.comp_aestronglyMeasurable hu.1.aestronglyMeasurable).smul
        ((continuous_pi fun j => (hη.continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable))
  have heq : ∀ᵐ z ∂volume.restrict (I ×ˢ U), V z = v z ∧ H z = J z := by
    filter_upwards [hpos] with z hz
    have hv : F (u z) = (u z) ^ (p/2) := c13_small_positive_power_eq hε (by linarith)
    have hd : deriv F (u z) = p/2 * (u z) ^ (p/2-1) := c13_small_positive_power_deriv hε (by linarith)
    simp only [V, H, v, J, hv, hd, and_self]
  have hv : MemLp v 2 (volume.restrict (I ×ˢ U)) := (memLp_congr_ae (heq.mono fun _ h => h.1)).mp hvh.1
  have hJm : AEStronglyMeasurable J (volume.restrict (I ×ˢ U)) := hHm.congr (heq.mono fun _ h => h.2)
  have hJ : MemLp (fun z => euclideanNorm (J z)) 2 (volume.restrict (I ×ˢ U)) :=
    (memLp_congr_ae (heq.mono fun _ h => congrArg euclideanNorm h.2)).mp hvh.2
  have htest : ∀ᵐ t ∂volume.restrict I, IsSpatialTest U (fun x => η (t,x)) := by
    filter_upwards with t
    have hsupp : tsupport (fun x => η (t,x)) ⊆ K := by
      apply closure_minimal _ hK.isClosed
      intro x hx
      by_contra hn
      exact hx (hzero t x hn)
    exact ⟨hη.comp (contDiff_const.prodMk contDiff_id),
      hK.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hKU⟩
  have hprod : volume.restrict (I ×ˢ U) = (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  have heq' := heq
  rw [hprod] at heq'
  have hw : ∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => v (t,x)) (fun x => J (t,x)) := by
    filter_upwards [c11_weighted_caloric_cutoff_spatial_chain_finite hU hu hfinite F hF M hM hdF
      (fun t x => η (t,x)) htest, Measure.ae_ae_of_ae_prod heq'] with t ht he
    have heqder (x : Vec d) (j : Fin d) :
        fderiv ℝ (fun y => η (t,y)) x (unitVector j) = fderiv ℝ η (t,x) (0, unitVector j) := by
      have hf := (hη.differentiable (by simp) (t,x)).hasFDerivAt.comp x
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
      simpa [Function.comp_def] using congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) hf.fderiv
    have ht' : HasWeakGradient U (fun x => V (t,x)) (fun x => H (t,x)) := by
      simpa only [V, H, heqder] using ht.1
    exact Correctors.hasWeakGradient_congr_ae hU ht' (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)
  exact hsob ρ α hcoeff I U hI hU u G η K hK hKU hzero S hS hSI hηone p ε hp hε hpos A E hv hJm hJ hw hmass hEm henergy

#lint
end EinsteinFull.Calculus
