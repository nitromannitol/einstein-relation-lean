import EinsteinRelation.Correctors.AKMHeatKernelSpatialExhaustion
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! # Spatial energy slices of the fundamental solution

Source: AKM (E.1)–(E.2), p. 499; `paper/main.tex:821–838`.
Fubini retains actual weak spatial gradients at almost every time.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A local parabolic energy solution has square-integrable gradient
coordinates at almost every time in its cylinder. -/
theorem akm_energy_slices_on_cylinder {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsParabolicSolution A I U u G) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x)) ∧
      ∀ j : Fin d, MemLp (fun x => G (t,x) j) 2 (volume.restrict U) := by
  have hv : (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U) =
      (volume.restrict I).prod (volume.restrict U) := by
    rw [Measure.prod_restrict]; rfl
  have hm := h.2.1
  have hn := h.2.2.1
  rw [hv] at hm hn
  filter_upwards [hm.prodMk_left, hn.aestronglyMeasurable.prodMk_left,
    hn.integrable_sq.prod_right_ae, h.2.2.2.1] with t ht hnt hit hwt
  refine ⟨hwt, fun j => ?_⟩
  have hN : MemLp (fun x => euclideanNorm (G (t,x))) 2 (volume.restrict U) :=
    (memLp_two_iff_integrable_sq hnt).mpr hit
  apply hN.mono' ((continuous_apply j).comp_aestronglyMeasurable ht)
  filter_upwards with x
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  change (G (t,x) j)^2 ≤ ∑ i, G (t,x) i * G (t,x) i
  simpa only [pow_two] using
    (Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) => mul_self_nonneg (G (t,x) i))
      (Finset.mem_univ j))

/-- Almost every positive-time slice has its genuine whole-space weak
gradient and square-integrable coordinates on every compact set.
Source: AKM (E.1)–(E.2), p. 499; `paper/main.tex:821–838`. -/
theorem akm_fundamental_energy_slices {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : ∀ a b R : ℝ, 0 < a → a < b → 0 < R →
      IsParabolicSolution A (Set.Ioo a b) (originBall d R) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
      HasWeakGradient Set.univ (fun x => u (t,x)) (fun x => G (t,x)) ∧
      ∀ s : Set (Vec d), IsCompact s → ∀ j : Fin d,
        MemLp (fun x => G (t,x) j) 2 (volume.restrict s) := by
  have hlocal (n m : ℕ) :
      ∀ᵐ t ∂volume.restrict (Set.Ioo (1 / (n + 2 : ℝ)) (n + 2 : ℝ)),
        HasWeakGradient (originBall d (m + 1 : ℝ))
            (fun x => u (t,x)) (fun x => G (t,x)) ∧
          ∀ j : Fin d, MemLp (fun x => G (t,x) j) 2
            (volume.restrict (originBall d (m + 1 : ℝ))) := by
    apply akm_energy_slices_on_cylinder
    apply h
    · positivity
    · have hn : (2 : ℝ) ≤ n + 2 := by
        have : (0 : ℝ) ≤ n := by positivity
        linarith
      have hi : 1 / (n + 2 : ℝ) ≤ 1 / 2 := by gcongr
      linarith
    · positivity
  have hall : ∀ᵐ t ∂volume, ∀ n m : ℕ,
      t ∈ Set.Ioo (1 / (n + 2 : ℝ)) (n + 2 : ℝ) →
        HasWeakGradient (originBall d (m + 1 : ℝ))
            (fun x => u (t,x)) (fun x => G (t,x)) ∧
          ∀ j : Fin d, MemLp (fun x => G (t,x) j) 2
            (volume.restrict (originBall d (m + 1 : ℝ))) :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun m =>
      (ae_restrict_iff' measurableSet_Ioo).mp (hlocal n m)
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  obtain ⟨n, hn⟩ := exists_nat_gt (max t t⁻¹)
  have hninv : t⁻¹ < (n : ℝ) := (le_max_right _ _).trans_lt hn
  have hint : t ∈ Set.Ioo (1 / (n + 2 : ℝ)) (n + 2 : ℝ) := by
    constructor
    · apply (div_lt_iff₀ (by positivity : (0 : ℝ) < n + 2)).mpr
      have hh := mul_lt_mul_of_pos_left hninv htpos
      rw [mul_inv_cancel₀ (ne_of_gt htpos)] at hh
      nlinarith
    · have hh : t < (n : ℝ) := (le_max_left _ _).trans_lt hn
      linarith
  refine ⟨akm_hasWeakGradient_univ_of_originBall (fun m => (ht n m hint).1), ?_⟩
  intro s hs j
  obtain ⟨m, hm⟩ := akm_compact_subset_originBall hs
  exact ((ht n m hint).2 j).mono_measure (Measure.restrict_mono_set volume hm)

end EinsteinRelation.Correctors
