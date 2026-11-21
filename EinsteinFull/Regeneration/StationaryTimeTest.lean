import EinsteinFull.Regeneration.StationaryEnergySpace
import EllipticRegularity.Parabolic.Chain.Integral

/-!
# Time tests for stationary energy functions

A compactly supported time derivative has zero pairing with a stationary
spatial energy function.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Each spatial section of a compactly supported time derivative integrates to zero. -/
theorem integral_parTimeDeriv_section_eq_zero {d : ℕ} (φ : PDE.Vec d × ℝ → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) (x : PDE.Vec d) :
    (∫ t : ℝ, PDE.parTimeDeriv φ (x, t)) = 0 := by
  have hsecC : ContDiff ℝ 1 (fun t : ℝ => φ (x, t)) :=
    hφ.comp (contDiff_const.prodMk contDiff_id)
  have hsecK : HasCompactSupport (fun t : ℝ => φ (x, t)) := by
    let K : Set ℝ := Prod.snd '' tsupport φ
    have hK : IsCompact K := hc.isCompact.image continuous_snd
    refine HasCompactSupport.of_support_subset_isCompact (K := K) hK ?_
    intro t ht
    have hne : φ (x, t) ≠ 0 := by simpa only [Function.mem_support] using ht
    exact ⟨(x, t), subset_tsupport φ hne, rfl⟩
  have hsecInt : Integrable (fun t : ℝ => φ (x, t)) volume :=
    hsecC.continuous.integrable_of_hasCompactSupport hsecK
  have hdC : Continuous (deriv fun t : ℝ => φ (x, t)) :=
    hsecC.continuous_deriv (by norm_num)
  have hdK : HasCompactSupport (deriv fun t : ℝ => φ (x, t)) := hsecK.deriv
  have hdInt : Integrable (deriv fun t : ℝ => φ (x, t)) volume :=
    hdC.integrable_of_hasCompactSupport hdK
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => φ (x, s))
      (deriv (fun s : ℝ => φ (x, s)) t) t :=
    (hsecC.differentiable (by norm_num) t).hasDerivAt
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hdInt hsecInt
  have heq (t : ℝ) : PDE.parTimeDeriv φ (x, t) = deriv (fun s : ℝ => φ (x, s)) t := by
    have hpair : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
      (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
    have hcomp := (hφ.differentiable (by norm_num) (x, t)).hasFDerivAt.comp t hpair
    have h : HasDerivAt (fun s : ℝ => φ (x, s)) (PDE.parTimeDeriv φ (x, t)) t := by
      simpa [Function.comp_def, PDE.parTimeDeriv] using hcomp.hasDerivAt
    exact h.deriv.symm.trans rfl
  rw [show (fun t : ℝ => PDE.parTimeDeriv φ (x, t)) =
    fun t => deriv (fun s : ℝ => φ (x, s)) t from funext heq]
  exact hzero

/-- The time-derivative term vanishes against every stationary spatial L² function. -/
theorem stationary_time_test_eq_zero {d : ℕ} (U : Set (PDE.Vec d)) (I : Set ℝ)
    [IsFiniteMeasure (volume.restrict I : Measure ℝ)] (v : PDE.Vec d → ℝ)
    (hv : MemLp v 2 (volume.restrict U)) (φ : PDE.ParTestFunction U (interior I)) :
    Integrable (fun z : PDE.Vec d × ℝ => v z.1 * PDE.parTimeDeriv φ.toFun z)
      (volume.restrict (U ×ˢ I)) ∧
      (∫ z in U ×ˢ I, v z.1 * PDE.parTimeDeriv φ.toFun z) = 0 := by
  have hcont : Continuous (PDE.parTimeDeriv φ.toFun) := by
    unfold PDE.parTimeDeriv
    exact (φ.contDiff.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  have hcompact : HasCompactSupport (PDE.parTimeDeriv φ.toFun) := by
    exact φ.hasCompactSupport.fderiv_apply ℝ (0, 1)
  have hφlp : MemLp (PDE.parTimeDeriv φ.toFun) 2 (volume.restrict (U ×ˢ I)) :=
    (hcont.memLp_of_hasCompactSupport hcompact).mono_measure Measure.restrict_le_self
  have hvlp : MemLp (fun z : PDE.Vec d × ℝ => v z.1) 2
      (volume.restrict (U ×ˢ I)) := by
    rw [PDE.Parabolic.Energy.volume_restrict_prod]
    exact hv.comp_fst (volume.restrict I)
  have hint : Integrable (fun z : PDE.Vec d × ℝ => v z.1 * PDE.parTimeDeriv φ.toFun z)
      (volume.restrict (U ×ˢ I)) := hvlp.integrable_mul hφlp
  refine ⟨hint, ?_⟩
  have hsection (x : PDE.Vec d) : (∫ t in I, PDE.parTimeDeriv φ.toFun (x, t)) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_parTimeDeriv_section_eq_zero φ.toFun φ.contDiff φ.hasCompactSupport x
    · intro t ht
      have hs : (x, t) ∉ tsupport φ.toFun := by
        intro hx
        exact ht (interior_subset (φ.tsupport_subset hx).2)
      have hs' : (x, t) ∉ tsupport (fderiv ℝ φ.toFun) := fun hx =>
        hs (tsupport_fderiv_subset ℝ hx)
      have hf : fderiv ℝ φ.toFun (x, t) = 0 := image_eq_zero_of_notMem_tsupport hs'
      simp [PDE.parTimeDeriv, hf]
  rw [PDE.Parabolic.Energy.volume_restrict_prod] at hint ⊢
  rw [integral_prod _ hint]
  apply integral_eq_zero_of_ae
  filter_upwards [] with x
  simp only [integral_const_mul, hsection x, mul_zero, Pi.zero_apply]

end EinsteinFull.Regeneration
