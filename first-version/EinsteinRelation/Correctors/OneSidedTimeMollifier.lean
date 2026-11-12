import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- A one-sided smooth probability kernel supported strictly between zero
and the requested positive time scale. Source: `paper/main.tex:798–806`. -/
theorem exists_one_sided_time_kernel {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ s, 0 ≤ ρ s) ∧ (∫ s, ρ s) = 1 ∧ tsupport ρ ⊆ Set.Ioo 0 ε := by
  let f : ContDiffBump (ε/2) :=
    { rIn := ε/8
      rOut := ε/4
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  refine ⟨f.normed volume,f.contDiff_normed,f.hasCompactSupport_normed,
    f.nonneg_normed,f.integral_normed,?_⟩
  rw [f.tsupport_normed_eq]
  intro s hs
  have hdist : |s-ε/2| ≤ ε/4 := by simpa only [Metric.mem_closedBall,Real.dist_eq] using hs
  have hd := abs_le.mp hdist
  constructor <;> linarith

/-- A sequence of one-sided normalized smooth temporal kernels shrinks to
zero while remaining inside a fixed positive time scale.
Source: `paper/main.tex:798–806`. -/
theorem exists_one_sided_time_approximation {δ : ℝ} (hδ : 0 < δ) :
    ∃ (ε : ℕ → ℝ) (ρ : ℕ → ℝ → ℝ),
      Tendsto ε atTop (𝓝 0) ∧ (∀ k, 0 < ε k ∧ ε k ≤ δ) ∧
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k)) ∧
      (∀ k, HasCompactSupport (ρ k)) ∧
      (∀ k s, 0 ≤ ρ k s) ∧ (∀ k, (∫ s, ρ k s) = 1) ∧
      ∀ k, tsupport (ρ k) ⊆ Set.Ioo 0 (ε k) := by
  let ε : ℕ → ℝ := fun k => δ * (1 / ((k : ℝ)+1))
  have hε k : 0 < ε k ∧ ε k ≤ δ := by
    dsimp only [ε]
    constructor
    · positivity
    · apply mul_le_of_le_one_right hδ.le
      exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) k])
  choose ρ hρ hρc hρ0 hρ1 hρs using fun k => exists_one_sided_time_kernel (hε k).1
  refine ⟨ε,ρ,?_,hε,hρ,hρc,hρ0,hρ1,hρs⟩
  simpa only [mul_zero] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul δ

/-- The reflected support of a one-sided kernel lies strictly before the
chosen time. Source: `paper/main.tex:798–806`. -/
theorem tsupport_time_kernel_subset {ρ : ℝ → ℝ} {ε a b t : ℝ}
    (hs : tsupport ρ ⊆ Set.Ioo 0 ε) (ha : a+ε ≤ t) (hb : t ≤ b) :
    tsupport (fun s => ρ (t-s)) ⊆ Set.Ioo a b := by
  have hc : tsupport (fun s => ρ (t-s)) ⊆ (fun s => t-s) ⁻¹' tsupport ρ := by
    exact closure_minimal (fun s hs => subset_tsupport ρ hs)
      ((isClosed_tsupport ρ).preimage (continuous_const.sub continuous_id))
  intro s hst
  have h := hs (hc hst)
  change 0 < t-s ∧ t-s < ε at h
  constructor <;> linarith

end EinsteinRelation.Correctors
