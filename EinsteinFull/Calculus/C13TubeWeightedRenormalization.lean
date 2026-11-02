import EinsteinFull.Calculus.C13TubeWeakGradientChain
import EinsteinFull.External.Source.GMPDirichletKernel
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinFull.Calculus.C18TubeWeightedSobolevTestExtension
import EinsteinFull.Calculus.C13TubeNativeCutoffProduct
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.Calculus.C20TubeWeightedNonlinearEnergyLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The time chain rule for a differentiable time-regularized solution, with
its spatial density retained. The existence of the derivative is established
separately for the time regularization. -/
theorem c13_weighted_time_chain_hasDerivAt
    (ρ : ℝ) (v : ℝ → ℝ) (t v' : ℝ)
    (hv : HasDerivAt v v' t) (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    HasDerivAt (fun s => ρ * F (v s)) (ρ * (deriv F (v t) * v')) t := by
  exact ((hF.differentiable (by simp) (v t)).hasDerivAt.comp t hv).const_mul ρ

/-- The density-weighted nonlinear time chain for local forward averages. -/
theorem c13_weighted_forward_average_chain_ae
    (ρ h : ℝ) (f : ℝ → ℝ)
    (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasDerivAt
        (fun s => ρ * F (h⁻¹ * (∫ r in (0 : ℝ)..h, f (s + r))))
        (ρ * (deriv F (h⁻¹ * (∫ r in (0 : ℝ)..h, f (t + r))) *
          (h⁻¹ * (f (t + h) - f t)))) t := by
  filter_upwards [c18_forward_integral_local_ae_hasDerivAt hf hh hhsmall] with t ht
  exact c13_weighted_time_chain_hasDerivAt ρ _ t _ (ht.const_mul h⁻¹) F hF

/-- The nonlinear forward-average chain rule on an arbitrary interior time
interval, using only local integrability on the original interval. -/
theorem c13_weighted_forward_average_chain_interval_ae
    (a b c d ρ h : ℝ) (hac : a ≤ c) (hdb : d + h ≤ b) (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b) volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo c d),
      HasDerivAt
        (fun s => ρ * F (h⁻¹ * (∫ r in (0 : ℝ)..h, f (s + r))))
        (ρ * (deriv F (h⁻¹ * (∫ r in (0 : ℝ)..h, f (t + r))) *
          (h⁻¹ * (f (t + h) - f t)))) t := by
  let g := (Set.Ioo a b).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  have hd := c18_forward_integral_ae_hasDerivAt hg.locallyIntegrable h
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t ht htm
  have htm0 : t ∈ Set.Ioo a b := by constructor <;> linarith [htm.1, htm.2]
  have htmh : t + h ∈ Set.Ioo a b := by constructor <;> linarith [htm.1, htm.2]
  have heq : (fun t => ∫ s in (0 : ℝ)..h, g (t + s)) =ᶠ[nhds t]
      (fun t => ∫ s in (0 : ℝ)..h, f (t + s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with q hq
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
    have hqs : q + s ∈ Set.Ioo a b := by constructor <;> linarith [hq.1, hq.2, hs'.1, hs'.2]
    exact Set.indicator_of_mem hqs f
  have ht' := ht.congr_of_eventuallyEq heq.symm
  have hdf : HasDerivAt (fun t => ∫ s in (0 : ℝ)..h, f (t + s))
      (f (t + h) - f t) t := by
    simpa only [g, Set.indicator_of_mem htm0, Set.indicator_of_mem htmh] using ht'
  exact c13_weighted_time_chain_hasDerivAt ρ _ t _ (hdf.const_mul h⁻¹) F hF

/-- The arbitrary-interval chain rule on almost every spatial slice of a
weighted caloric function on a source cylinder. -/
theorem c13_weighted_caloric_forward_average_chain_interval_ae {d : ℕ}
    (a b c e h r : ℝ) (hac : a ≤ c) (heb : e + h ≤ b) (hh : 0 ≤ h)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      ∀ᵐ t ∂volume.restrict (Set.Ioo c e),
        HasDerivAt
          (fun s => ρ x * F (h⁻¹ * (∫ q in (0 : ℝ)..h, u (s + q, x))))
          (ρ x * (deriv F (h⁻¹ * (∫ q in (0 : ℝ)..h, u (t + q, x))) *
            (h⁻¹ * (u (t + h, x) - u (t, x))))) t := by
  letI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  have hf' : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
    rwa [Measure.prod_restrict] at hf
  letI := hf'
  have hi : Integrable u ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  exact c13_weighted_forward_average_chain_interval_ae a b c e (ρ x) h hac heb hh
    (fun t => u (t, x)) hx F hF

/-- The nonlinear chain rule applies to almost every spatial slice of an
actual weighted caloric function. -/
theorem c13_weighted_caloric_forward_average_chain_ae {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (y : Vec d) (u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
        HasDerivAt
          (fun s => ρ x * F (h⁻¹ * (∫ q in (0 : ℝ)..h, u (s + q, x))))
          (ρ x * (deriv F (h⁻¹ * (∫ q in (0 : ℝ)..h, u (t + q, x))) *
            (h⁻¹ * (u (t + h, x) - u (t, x))))) t := by
  letI := c18_sourceCylinder_isFiniteMeasure y r
  have hi : Integrable u ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  exact c13_weighted_forward_average_chain_ae (ρ x) h (fun t => u (t, x))
    hx (le_of_lt hh) hhsmall F hF

/-- The centered derivative of a bounded C² nonlinearity has the native weak
spatial gradient needed for nonlinear tests. Centering avoids any assumption
that the spatial domain has finite measure. -/
theorem c13_native_weak_gradient_deriv_chain {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hF2 : ∀ r, |deriv (deriv F) r| ≤ M) :
    MemLp (fun x => deriv F (u x) - deriv F 0) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm (deriv (deriv F) (u x) • G x)) 2
      (volume.restrict U) ∧
    HasWeakGradient U (fun x => deriv F (u x) - deriv F 0)
      (fun x => deriv (deriv F) (u x) • G x) := by
  let H : ℝ → ℝ := fun r => deriv F r - deriv F 0
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  have hH : ContDiff ℝ 1 H := hF'.sub contDiff_const
  have hH0 : H 0 = 0 := sub_self _
  have hHd (r : ℝ) : deriv H r = deriv (deriv F) r := by
    change deriv (deriv F - fun _ => deriv F 0) r = _
    rw [deriv_sub (hF'.differentiable (by simp) r) (differentiableAt_const _),
      deriv_const, sub_zero]
  have hd : ∀ r, |deriv H r| ≤ M := fun r => by rw [hHd]; exact hF2 r
  have hc := c13_native_weak_gradient_bounded_C1_chain hU u G hu hG hw H hH hH0 M hM hd
  simpa only [H, hHd] using hc

/-- The uncentered derivative has its actual weak spatial gradient, without
requiring its values to be square integrable on an unbounded domain. -/
theorem c13_native_weak_gradient_deriv {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hF2 : ∀ r, |deriv (deriv F) r| ≤ M) :
    HasWeakGradient U (fun x => deriv F (u x))
      (fun x => deriv (deriv F) (u x) • G x) := by
  have hc := (c13_native_weak_gradient_deriv_chain hU u G hu hG hw F hF M hM hF2).2.2
  simpa only [sub_neg_eq_add, sub_add_cancel] using
    EinsteinRelation.Correctors.hasWeakGradient_sub_const U hc (-deriv F 0)

/-- On a finite-measure domain the derivative itself, as well as its weak
gradient, is square integrable. -/
theorem c13_native_weak_gradient_deriv_memLp {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hF2 : ∀ r, |deriv (deriv F) r| ≤ M) :
    MemLp (fun x => deriv F (u x)) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm (deriv (deriv F) (u x) • G x)) 2
      (volume.restrict U) ∧
    HasWeakGradient U (fun x => deriv F (u x))
      (fun x => deriv (deriv F) (u x) • G x) := by
  have hc := c13_native_weak_gradient_deriv_chain hU u G hu hG hw F hF M hM hF2
  refine ⟨?_, hc.2.1, c13_native_weak_gradient_deriv hU u G hu hG hw F hF M hM hF2⟩
  have heq : ((fun x : Vec d => deriv F (u x) - deriv F 0) +
      fun _ => deriv F 0) = (fun x => deriv F (u x)) := by
    funext x
    simp
  rw [← heq]
  exact hc.1.add (memLp_const (deriv F 0))

/-- A smooth cutoff of the nonlinear derivative is an admissible spatial
Sobolev test, with its explicit weak gradient. -/
theorem c13_native_cutoff_deriv_weak_gradient {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hF2 : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : Vec d → ℝ) (hχ : IsSpatialTest U χ) :
    HasWeakGradient U (fun x => χ x * deriv F (u x))
      (fun x => χ x • (deriv (deriv F) (u x) • G x) +
        deriv F (u x) • (fun j => fderiv ℝ χ x (unitVector j))) ∧
    MemLp (fun x => χ x * deriv F (u x)) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm (χ x • (deriv (deriv F) (u x) • G x) +
      deriv F (u x) • (fun j => fderiv ℝ χ x (unitVector j)))) 2
      (volume.restrict U) := by
  have hc := c13_native_weak_gradient_deriv_memLp hU u G hu hG hw F hF M hM hF2
  exact EinsteinFull.c13_native_cutoff_weak_gradient hU _ _ hc.2.2 hc.1 hc.2.1 χ hχ

/-- Almost every slice of a weighted caloric solution admits the nonlinear
cutoff test, with the explicit spatial weak gradient. -/
theorem c13_weighted_caloric_cutoff_deriv_slices {d : ℕ} {I : Set ℝ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : Vec d → ℝ) (hχ : IsSpatialTest U χ) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => χ x * deriv F (u (t, x)))
        (fun x => χ x • (deriv (deriv F) (u (t, x)) • G (t, x)) +
          deriv F (u (t, x)) • (fun j => fderiv ℝ χ x (unitVector j))) ∧
      MemLp (fun x => χ x * deriv F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (χ x • (deriv (deriv F) (u (t, x)) • G (t, x)) +
        deriv F (u (t, x)) • (fun j => fderiv ℝ χ x (unitVector j)))) 2
        (volume.restrict U) := by
  have hu' : MemLp u 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.1
  have hG' : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.2.2.1
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu',
    c9_memLp_prod_right_ae _ _ _ hG', hu.2.2.2.1] with t hut hGt hwt
  exact c13_native_cutoff_deriv_weak_gradient hU _ _ hut hGt hwt F hF M hM hF2 χ hχ

/-- Time-dependent spatial cutoffs give nonlinear Sobolev tests on almost
every time slice of a weighted caloric solution. -/
theorem c13_weighted_caloric_time_cutoff_deriv_slices {d : ℕ} {I : Set ℝ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ r, |deriv (deriv F) r| ≤ M)
    (χ : ℝ → Vec d → ℝ) (hχ : ∀ t, IsSpatialTest U (χ t)) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => χ t x * deriv F (u (t, x)))
        (fun x => χ t x • (deriv (deriv F) (u (t, x)) • G (t, x)) +
          deriv F (u (t, x)) • (fun j => fderiv ℝ (χ t) x (unitVector j))) ∧
      MemLp (fun x => χ t x * deriv F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (χ t x • (deriv (deriv F) (u (t, x)) • G (t, x)) +
        deriv F (u (t, x)) • (fun j => fderiv ℝ (χ t) x (unitVector j)))) 2
        (volume.restrict U) := by
  have hu' : MemLp u 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.1
  have hG' : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict]
    exact hu.2.2.1
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu',
    c9_memLp_prod_right_ae _ _ _ hG', hu.2.2.2.1] with t hut hGt hwt
  exact c13_native_cutoff_deriv_weak_gradient hU _ _ hut hGt hwt F hF M hM hF2 (χ t) (hχ t)

/-- Expanding the flux pairing with the nonlinear cutoff gradient yields the
two spatial terms of the renormalized equation. -/
theorem c13_nonlinear_cutoff_flux_identity {d : ℕ}
    (α : Mat d) (G D : Vec d) (χ v : ℝ) (F : ℝ → ℝ) :
    dot (α.mulVec G) (χ • (deriv (deriv F) v • G) + deriv F v • D) =
      deriv F v * dot (α.mulVec G) D +
        deriv (deriv F) v * dot (α.mulVec G) G * χ := by
  unfold dot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ j, ((deriv F v) * ((α.mulVec G) j * D j) +
        (deriv (deriv F) v * χ) * ((α.mulVec G) j * G j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring

/-- Every spatial slice of a compactly supported spacetime test is an
admissible spatial test, with its literal spacetime derivative. -/
theorem c13_spacetime_test_spatial_slice {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hsp : tsupport ψ ⊆ I ×ˢ U) (t : ℝ) :
    IsSpatialTest U (fun x => ψ (t, x)) ∧
      ∀ x v, fderiv ℝ (fun y => ψ (t, y)) x v = fderiv ℝ ψ (t, x) (0, v) := by
  let K : Set (Vec d) := Prod.snd '' tsupport ψ
  have hK : IsCompact K := hc.image continuous_snd
  have hKU : K ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hsp hz).2
  have hsupp : Function.support (fun x => ψ (t, x)) ⊆ K := by
    intro x hx
    exact ⟨(t, x), subset_closure hx, rfl⟩
  have htsupp : tsupport (fun x => ψ (t, x)) ⊆ K :=
    closure_minimal hsupp hK.isClosed
  refine ⟨⟨hψ.comp (contDiff_const.prodMk contDiff_id),
    hK.of_isClosed_subset (isClosed_tsupport _) htsupp, htsupp.trans hKU⟩, ?_⟩
  intro x v
  have h := (hψ.differentiable (by simp) (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change fderiv ℝ (ψ ∘ Prod.mk t) x v = fderiv ℝ ψ (t, x) (0, v)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- The nonlinear test formed with an actual smooth spacetime test has the
spatial Sobolev regularity and gradient used in renormalization. -/
theorem c13_weighted_caloric_spacetime_test_deriv_slices {d : ℕ} {I : Set ℝ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ r, |deriv (deriv F) r| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hsp : tsupport ψ ⊆ I ×ˢ U) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => ψ (t, x) * deriv F (u (t, x)))
        (fun x => ψ (t, x) • (deriv (deriv F) (u (t, x)) • G (t, x)) +
          deriv F (u (t, x)) • (fun j => fderiv ℝ ψ (t, x) (0, unitVector j))) ∧
      MemLp (fun x => ψ (t, x) * deriv F (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (ψ (t, x) • (deriv (deriv F) (u (t, x)) • G (t, x)) +
        deriv F (u (t, x)) • (fun j => fderiv ℝ ψ (t, x) (0, unitVector j)))) 2
        (volume.restrict U) := by
  have hs := c13_weighted_caloric_time_cutoff_deriv_slices hU ρ α u G hu F hF M hM hF2
    (fun t x => ψ (t, x)) (fun t => (c13_spacetime_test_spatial_slice ψ hψ hc hsp t).1)
  filter_upwards [hs] with t ht
  simpa only [(c13_spacetime_test_spatial_slice ψ hψ hc hsp t).2] using ht

/-- A compactly supported test in an open cylinder is supported in a
strictly smaller time interval, leaving room for a forward time average. -/
theorem c13_spacetime_test_compact_time_interval {d : ℕ} {a b : ℝ}
    (hab : a < b) {U : Set (Vec d)} (ψ : ℝ × Vec d → ℝ)
    (hc : HasCompactSupport ψ) (hsp : tsupport ψ ⊆ Set.Ioo a b ×ˢ U) :
    ∃ c e : ℝ, a < c ∧ c < e ∧ e < b ∧
      tsupport ψ ⊆ Set.Ioo c e ×ˢ U := by
  let K : Set ℝ := Prod.fst '' tsupport ψ
  have hK : IsCompact K := hc.image continuous_fst
  have hKI : K ⊆ Set.Ioo a b := by
    rintro t ⟨z, hz, rfl⟩
    exact (hsp hz).1
  by_cases hne : K.Nonempty
  · obtain ⟨m, hm⟩ := hK.exists_isLeast hne
    obtain ⟨n, hn⟩ := hK.exists_isGreatest hne
    have ham := (hKI hm.1).1
    have hnb := (hKI hn.1).2
    have hmn : m ≤ n := hm.2 hn.1
    refine ⟨(a + m) / 2, (n + b) / 2, by linarith, by linarith,
      by linarith, ?_⟩
    intro z hz
    have hzK : z.1 ∈ K := ⟨z, hz, rfl⟩
    exact ⟨⟨by linarith [hm.2 hzK], by linarith [hn.2 hzK]⟩, (hsp hz).2⟩
  · refine ⟨(2 * a + b) / 3, (a + 2 * b) / 3, by linarith,
      by linarith, by linarith, ?_⟩
    intro z hz
    exact (hne ⟨z.1, z, hz, rfl⟩).elim

/-- A bounded-derivative nonlinearity of a forward time average is
absolutely continuous on every bounded interval. -/
theorem c13_nonlinear_forward_average_absolutelyContinuous (f : ℝ → ℝ)
    (hf : LocallyIntegrable f volume) (h c e : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv F r| ≤ M) :
    AbsolutelyContinuousOnInterval
      (fun t => F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) c e := by
  have hac := (c18_forward_integral_absolutelyContinuous hf h c e).const_mul h⁻¹
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM (hF.differentiable (by simp)) hder
  exact hlip.comp_absolutelyContinuousOnInterval hac


/-- The nonlinear forward average is absolutely continuous on interior
intervals when the original function is integrable on the time cylinder. -/
theorem c13_nonlinear_forward_average_local_absolutelyContinuous {f : ℝ → ℝ}
    {h a b : ℝ} (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    (hab : Set.uIcc a b ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv F r| ≤ M) :
    AbsolutelyContinuousOnInterval
      (fun t => F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) a b := by
  have hac := (c18_forward_integral_local_absolutelyContinuous hf hh hhsmall hab).const_mul h⁻¹
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM (hF.differentiable (by simp)) hder
  exact hlip.comp_absolutelyContinuousOnInterval hac


/-- A nonlinear forward average is absolutely continuous on any closed time
interval whose shifts stay inside the original integrability interval. -/
theorem c13_nonlinear_forward_average_interval_absolutelyContinuous
    {a b c e h : ℝ} (hac : a < c) (hce : c ≤ e) (heb : e + h < b)
    (hh : 0 ≤ h) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b) volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv F r| ≤ M) :
    AbsolutelyContinuousOnInterval
      (fun t => F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) c e := by
  let g := (Set.Ioo a b).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  apply (c13_nonlinear_forward_average_absolutelyContinuous g hg.locallyIntegrable
    h c e F hF M hM hder).congr
  intro t ht
  have ht' : t ∈ Set.Icc c e := by simpa [Set.uIcc_of_le hce] using ht
  apply congrArg F
  apply congrArg (fun z : ℝ => h⁻¹ * z)
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
  have hts : t + s ∈ Set.Ioo a b := by constructor <;> linarith [ht'.1, ht'.2, hs'.1, hs'.2]
  exact Set.indicator_of_mem hts f


/-- Integration by parts for the density-weighted nonlinear time average. -/
theorem c13_weighted_nonlinear_forward_average_integration_by_parts
    {a b c e h : ℝ} (hac : a < c) (hce : c ≤ e) (heb : e + h < b)
    (hh : 0 ≤ h) (ρ : ℝ) (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo a b) volume)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv F r| ≤ M) (ψ : ℝ → ℝ)
    (hψ : AbsolutelyContinuousOnInterval ψ c e) (hc : ψ c = 0) (he : ψ e = 0) :
    (∫ t in c..e, (ρ * F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))) * deriv ψ t) =
      -∫ t in c..e, (ρ * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s))) *
        (h⁻¹ * (f (t + h) - f t)))) * ψ t := by
  let v : ℝ → ℝ := fun t => ρ * F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s)))
  have hv := (c13_nonlinear_forward_average_interval_absolutelyContinuous hac hce heb hh
    f hf F hF M hM hder).const_mul ρ
  have hparts := hv.integral_mul_deriv_eq_deriv_mul hψ
  have heq : (∫ t in c..e, deriv v t * ψ t) =
      ∫ t in c..e, (ρ * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, f (t + s))) *
        (h⁻¹ * (f (t + h) - f t)))) * ψ t := by
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le hce]
    apply (ae_restrict_iff' measurableSet_Ioc).mp
    rw [← restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [c13_weighted_forward_average_chain_interval_ae a b c e ρ h
      hac.le heb.le hh f hf F hF] with t ht
    rw [ht.deriv]
  rw [heq, hc, he] at hparts
  simpa [v] using hparts


/-- The density-weighted nonlinear time integration by parts applies on
almost every spatial slice of a weighted caloric cylinder. -/
theorem c13_weighted_caloric_nonlinear_forward_average_integration_by_parts_ae
    {d : ℕ} {a b c e h r : ℝ} (hac : a < c) (hce : c ≤ e)
    (heb : e + h < b) (hh : 0 ≤ h)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv F q| ≤ M) (ψ : ℝ → ℝ)
    (hψ : AbsolutelyContinuousOnInterval ψ c e) (hc : ψ c = 0) (he : ψ e = 0) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      (∫ t in c..e, (ρ x * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x)))) * deriv ψ t) =
        -∫ t in c..e, (ρ x * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x))) *
          (h⁻¹ * (u (t + h, x) - u (t, x))))) * ψ t := by
  letI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  have hf' : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
    rwa [Measure.prod_restrict] at hf
  letI := hf'
  have hi : Integrable u ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  exact c13_weighted_nonlinear_forward_average_integration_by_parts hac hce heb hh
    (ρ x) (fun t => u (t, x)) hx F hF M hM hder ψ hψ hc he


/-- Integration by parts on caloric time slices with the time slice of an
actual smooth spacetime test. -/
theorem c13_weighted_caloric_spacetime_nonlinear_integration_by_parts_ae
    {d : ℕ} {a b c e h r : ℝ} (hac : a < c) (hce : c ≤ e)
    (heb : e + h < b) (hh : 0 ≤ h)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv F q| ≤ M) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo c e ×ˢ sourceBall y r) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      (∫ t in c..e, (ρ x * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x)))) *
        deriv (fun q => ψ (q, x)) t) =
        -∫ t in c..e, (ρ x * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x))) *
          (h⁻¹ * (u (t + h, x) - u (t, x))))) * ψ (t, x) := by
  letI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hf : IsFiniteMeasure ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := inferInstance
  have hf' : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ sourceBall y r)) := by
    rwa [Measure.prod_restrict] at hf
  letI := hf'
  have hi : Integrable u ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  have hs : ContDiff ℝ 1 (fun t => ψ (t, x)) :=
    (hψ.comp (contDiff_id.prodMk contDiff_const)).of_le (by simp)
  have hc : ψ (c, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (lt_irrefl c) (hsp hm).1.1
  have he : ψ (e, x) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    exact (lt_irrefl e) (hsp hm).1.2
  exact c13_weighted_nonlinear_forward_average_integration_by_parts hac hce heb hh
    (ρ x) (fun t => u (t, x)) hx F hF M hM hder (fun t => ψ (t, x))
    hs.contDiffOn.absolutelyContinuousOnInterval hc he


/-- The spacetime-test time integration by parts in set-integral form,
ready for Fubini on the open time interval. -/
theorem c13_weighted_caloric_spacetime_nonlinear_set_integration_by_parts_ae
    {d : ℕ} {a b c e h r : ℝ} (hac : a < c) (hce : c ≤ e)
    (heb : e + h < b) (hh : 0 ≤ h)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv F q| ≤ M) (ψ : ℝ × Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo c e ×ˢ sourceBall y r) :
    ∀ᵐ x ∂volume.restrict (sourceBall y r),
      (∫ t in Set.Ioo c e, (ρ x * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x)))) *
        deriv (fun q => ψ (q, x)) t) =
        -∫ t in Set.Ioo c e, (ρ x * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (t + s, x))) *
          (h⁻¹ * (u (t + h, x) - u (t, x))))) * ψ (t, x) := by
  filter_upwards [c13_weighted_caloric_spacetime_nonlinear_integration_by_parts_ae
    hac hce heb hh ρ α y u G hu F hF M hM hder ψ hψ hsp] with x hx
  simpa only [intervalIntegral.integral_of_le hce, ← restrict_Ioo_eq_restrict_Ioc] using hx

/-- The time derivative of a spacetime test slice is its derivative in the
unit time direction. -/
theorem c13_spacetime_test_time_slice_deriv {d : ℕ}
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (t : ℝ) (x : Vec d) :
    deriv (fun q => ψ (q, x)) t = fderiv ℝ ψ (t, x) (1, 0) := by
  have hg : HasDerivAt (fun q : ℝ => (q, x)) (1, 0) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact ((hψ.differentiable (by simp) (t, x)).hasFDerivAt.comp_hasDerivAt t hg).deriv

/-- The density-weighted nonlinear time term is integrable on the interior
slab for a smooth compactly supported spacetime test. -/
theorem c13_weighted_forward_nonlinear_time_term_integrable {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 2)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
      fderiv ℝ ψ z (1, 0))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hus : MemLp u 2 μ := hu.1.mono_measure (Measure.restrict_mono_set volume (by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩))
  have hd := c20_scalar_forward_average_slab_memLp (sourceBall y r)
    (c18_sourceBall_measurable y r) u hu.1 hh hhsmall
  have havg : MemLp (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) 2 μ := by
    convert hd.add hus using 1 <;> ext z <;> simp
  have hf := c20_nonlinear_comp_integrable _ havg F hF M hM hF2
  have hρ := (c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell).1
  have hdt : Continuous (fun z : ℝ × Vec d => fderiv ℝ ψ z (1, 0)) :=
    (hψ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB, hb⟩ :=
    ((hψc.fderiv_apply ℝ (1, 0)).isCompact_range hdt).isBounded.exists_pos_norm_le
  have hdtLp : MemLp (fun z : ℝ × Vec d => fderiv ℝ ψ z (1, 0)) ∞ μ := by
    apply memLp_top_of_bound hdt.aestronglyMeasurable B
    exact ae_of_all μ (fun z => hb _ ⟨z, rfl⟩)
  convert (hf.mul_of_top_right hρ).mul_of_top_right hdtLp using 1
  funext z
  simp only [Pi.mul_apply]
  ring

/-- The density-weighted forward difference paired with a nonlinear test is
integrable on the interior slab. -/
theorem c13_weighted_forward_nonlinear_difference_integrable {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Integrable (fun z => ρ z.2 * (deriv F (h⁻¹ *
      (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
      (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hus : MemLp u 2 μ := hu.1.mono_measure (Measure.restrict_mono_set volume (by
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩))
  have hd := c20_scalar_forward_average_slab_memLp (sourceBall y r)
    (c18_sourceBall_measurable y r) u hu.1 (le_of_lt hh) (by linarith : h ≤ 1 / 2)
  have havg : MemLp (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) 2 μ := by
    convert hd.add hus using 1 <;> ext z <;> simp
  let Q : ℝ → ℝ := fun q => deriv F q - deriv F 0
  have hQ : ContDiff ℝ 1 Q := hF.deriv'.sub contDiff_const
  have hq : MemLp (fun z => Q (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))) 2 μ := by
    change MemLp (Q ∘ _) 2 μ
    apply (PDE.lipschitzWith_of_abs_deriv_le hM (hQ.differentiable (by simp)) ?_).comp_memLp
      (by simp [Q]) havg
    intro q
    simpa [Q, deriv_sub_const] using hF2 q
  have hf : MemLp (fun z => deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2)))) 2 μ := by
    convert hq.add (memLp_const (deriv F 0)) using 1
    ext z
    simp [Q]
  have hdiff := c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu
  have hρ := (c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell).1
  have hψtop : MemLp ψ ∞ μ := hψ.continuous.memLp_top_of_hasCompactSupport hψc μ
  have hρdiff : MemLp (fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)) 2 μ :=
    hρ.mul hdiff
  have hi := (hρdiff.integrable_mul hf).mul_of_top_right hψtop
  convert hi using 1
  funext z
  simp only [Pi.mul_apply, div_eq_mul_inv]
  ring

/-- Spacetime integration by parts for a nonlinear forward average, with the
actual density and smooth spacetime test. -/
theorem c13_weighted_forward_nonlinear_spacetime_integration_by_parts
    {d : ℕ} {κ r h : ℝ} (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    (hder : ∀ q, |deriv F q| ≤ M) (hF2 : ∀ q, |deriv (deriv F) q| ≤ N)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        fderiv ℝ ψ z (1, 0)) =
    -(∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * (deriv F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z) := by
  let μ := (volume : Measure ℝ).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
  let ν := (volume : Measure (Vec d)).restrict (sourceBall y r)
  let A : ℝ × Vec d → ℝ := fun z => ρ z.2 * F (h⁻¹ *
    (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1, 0)
  let B : ℝ × Vec d → ℝ := fun z => ρ z.2 * (deriv F (h⁻¹ *
    (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
      (h⁻¹ * (u (z.1+h,z.2) - u z))) * ψ z
  have hA : Integrable A (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact c13_weighted_forward_nonlinear_time_term_integrable hκ (le_of_lt hh)
      (by linarith) ρ α hell y u G hu F hF N hN hF2 ψ hψ hψc
  have hB : Integrable B (μ.prod ν) := by
    rw [Measure.prod_restrict]
    exact c13_weighted_forward_nonlinear_difference_integrable hκ hh hhsmall
      ρ α hell y u G hu F hF N hN hF2 ψ hψ hψc
  have hs := c13_weighted_caloric_spacetime_nonlinear_set_integration_by_parts_ae
    (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)) (by norm_num : (-(1 / 2 : ℝ)) ≤ 1 / 2)
    (by linarith : (1 / 2 : ℝ) + h < 1) (le_of_lt hh)
    ρ α y u G hu F (hF.of_le (by norm_num)) M hM hder ψ hψ hsp
  have hslice : ∀ᵐ x ∂ν, (∫ t, A (t, x) ∂μ) = -(∫ t, B (t, x) ∂μ) := by
    filter_upwards [hs] with x hx
    simpa only [A, B, μ, c13_spacetime_test_time_slice_deriv ψ (hψ.of_le (by simp))] using hx
  change (∫ z, A z ∂(volume.restrict (_ ×ˢ _))) =
    -(∫ z, B z ∂(volume.restrict (_ ×ˢ _)))
  have hμν : μ.prod ν = (volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hμν, integral_prod_symm _ hA, integral_prod_symm _ hB, ← integral_neg]
  exact integral_congr_ae hslice

/-- The density-weighted time term converges as the forward average tends
to the original caloric function. -/
theorem c13_weighted_forward_nonlinear_time_term_limit {d : ℕ} {κ r : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (y : Vec d)
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) *
        fderiv ℝ ψ z (1, 0)) (𝓝[>] 0)
      (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
        ρ z.2 * F (u z) * fderiv ℝ ψ z (1, 0))) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hdt : Continuous (fun z : ℝ × Vec d => fderiv ℝ ψ z (1, 0)) :=
    (hψ.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  obtain ⟨B, hB, hb⟩ :=
    ((hψc.fderiv_apply ℝ (1, 0)).isCompact_range hdt).isBounded.exists_pos_norm_le
  have hm : AEStronglyMeasurable (fun z : ℝ × Vec d =>
      ρ z.2 * fderiv ℝ ψ z (1, 0)) μ :=
    ((hell.1.comp measurable_snd).mul hdt.measurable).aestronglyMeasurable
  have hw : ∀ᵐ z ∂μ, |ρ z.2 * fderiv ℝ ψ z (1, 0)| ≤ κ⁻¹ * B := by
    filter_upwards with z
    have hp : 0 < ρ z.2 := lt_of_lt_of_le hκ (hell.2.2 z.2).1
    have hρ : ρ z.2 ≤ κ⁻¹ := (hell.2.2 z.2).2.1
    have hd : |fderiv ℝ ψ z (1, 0)| ≤ B := by
      simpa only [Real.norm_eq_abs] using hb _ ⟨z, rfl⟩
    rw [abs_mul, abs_of_pos hp]
    exact mul_le_mul hρ hd (abs_nonneg _) (le_of_lt (inv_pos.mpr hκ))
  have ht := c20_scalar_forward_average_weighted_comp_limit (sourceBall y r)
    (c18_sourceBall_measurable y r) u hu F hF M hM hF2
    (fun z => ρ z.2 * fderiv ℝ ψ z (1, 0)) (κ⁻¹ * B)
    hm hw
  convert ht using 1
  · funext h
    apply integral_congr_ae
    filter_upwards with z
    ring
  · congr 1
    apply integral_congr_ae
    filter_upwards with z
    ring

end EinsteinFull.Calculus
