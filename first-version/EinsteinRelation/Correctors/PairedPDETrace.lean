import EinsteinRelation.Correctors.PairedParabolicEquation
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! # Identifying the strong initial trace of the paired flow

Source: `paper/main.tex:822–843`. A continuous L² extension to the initial
time has a uniquely determined initial value, because the actual semigroup
solutions already specify their distributional initial data. Constructing
such an extension is separate from identifying its value.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Distributional zero trace fixes the value of every strongly continuous
L² extension. The value at zero is proved to vanish, rather than supplied
as an additional initial condition. Source: `paper/main.tex:822–843`. -/
theorem paired_semigroupSolution_zero_L2_trace_of_continuous_extension
    {d : ℕ} {K : ℝ} {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U)
    [IsFiniteMeasure (volume.restrict U)] (hg : Set.EqOn g₁ g₂ U)
    (v : ℝ → Lp ℝ 2 (volume.restrict U))
    (hv : ContinuousWithinAt v (Set.Ici 0) 0)
    (hrep : ∀ t : ℝ, 0 < t →
      (v t : Vec d → ℝ) =ᵐ[volume.restrict U] fun x => u₁ (t, x) - u₂ (t, x)) :
    v 0 = 0 ∧
      Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) ∧
      Tendsto (fun t => ∫ x in U, (u₁ (t, x) - u₂ (t, x))^2 ∂volume)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  let μ := volume.restrict U
  have hvlim : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (v 0)) :=
    hv.mono (show Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 from
      fun _ hx => Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)
  have htest (ψ : Vec d → ℝ) (hψ : IsSpatialTest U ψ) :
      (∫ x in U, ψ x * v 0 x ∂volume) = 0 := by
    have hm : MemLp ψ 2 μ :=
      (hψ.1.continuous.memLp_of_hasCompactSupport hψ.2.1).mono_measure
        Measure.restrict_le_self
    let q := hm.toLp ψ
    have heq (t : ℝ) : inner ℝ (v t) q = ∫ x in U, ψ x * v t x ∂volume := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hm.coeFn_toLp] with x hx
      simp only [q, hx, RCLike.inner_apply, conj_trivial]
    have hpair := hvlim.inner (𝕜 := ℝ) (tendsto_const_nhds (x := q))
    have hlim := paired_semigroupSolution_initial_zero h₁ h₂ hg hψ
    have hcompare : (fun t => inner ℝ (v t) q) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        fun t => ∫ x, (u₁ (t, x) - u₂ (t, x)) * ψ x ∂volume := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [heq t]
      calc
        _ = ∫ x in U, (u₁ (t, x) - u₂ (t, x)) * ψ x ∂volume := by
          apply integral_congr_ae
          filter_upwards [hrep t ht] with x hx
          rw [hx, mul_comm]
        _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have hxs : x ∉ tsupport ψ := fun hm => hx (hψ.2.2 hm)
          rw [image_eq_zero_of_notMem_tsupport hxs, mul_zero])
    rw [← heq 0]
    exact tendsto_nhds_unique hpair (hlim.congr' hcompare.symm)
  have hzero : ∀ᵐ x ∂volume, x ∈ U → v 0 x = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp (v 0)).integrable (by norm_num)).locallyIntegrable)
    intro ψ hψ hψc hψU
    have hid : (∫ x, ψ x • v 0 x ∂volume) = ∫ x in U, ψ x * v 0 x ∂volume := by
      symm
      exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hxs : x ∉ tsupport ψ := fun hm => hx (hψU hm)
        rw [image_eq_zero_of_notMem_tsupport hxs, zero_mul])
    rw [hid]
    exact htest ψ ⟨hψ, hψc, hψU⟩
  have hv0 : v 0 = 0 := by
    apply Lp.ext
    have hae : (v 0 : Vec d → ℝ) =ᵐ[μ] fun _ => 0 :=
      (ae_restrict_iff' hU.measurableSet).mpr hzero
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 μ] with x hx hz
    exact hx.trans hz.symm
  have hvlim0 : Tendsto v (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa only [hv0] using hvlim
  refine ⟨hv0, hvlim0, ?_⟩
  have hnorm := hvlim0.norm.pow 2
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0)] at hnorm
  apply hnorm.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  calc
    ‖v t‖ ^ 2 = ∫ x in U, (v t x)^2 ∂volume := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      congr 1
      funext x
      simp only [RCLike.inner_apply, conj_trivial, pow_two]
    _ = _ := integral_congr_ae ((hrep t ht).mono fun x hx => congrArg (fun z : ℝ => z^2) hx)

end EinsteinRelation.Correctors
