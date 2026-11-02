import EinsteinRelation.External.AKMLocalCorrectors
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # A smooth cutoff on a reference parabolic cylinder

Source: `paper/main.tex:788–796,822–830`. The cutoff equals one on the
inner cylinder, is compactly supported in the larger cylinder, and has a
bounded derivative. The spatial support uses the paper's Euclidean ball.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM

/-- A fixed smooth cylinder cutoff with a deterministic derivative bound.
Source: `paper/main.tex:788–796,822–830`. -/
theorem exists_parabolic_reference_cutoff (d : ℕ) :
    ∃ (ζ : ℝ × Vec d → ℝ) (M : ℝ), 0 < M ∧
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Set.Ioo 1 4 ×ˢ originBall d 2 ∧
      (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧
      (∀ z ∈ Set.Icc 2 3 ×ˢ originBall d 1, ζ z = 1) ∧
      ∀ z, ‖fderiv ℝ ζ z‖ ≤ M := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let T := (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr J
  let b : ContDiffBump ((5 / 2 : ℝ), (0 : EuclideanSpace ℝ (Fin d))) :=
    ⟨1, 5 / 4, by norm_num, by norm_num⟩
  let ζ : ℝ × Vec d → ℝ := b ∘ T
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := b.contDiff.comp T.contDiff
  have hc : HasCompactSupport ζ := b.hasCompactSupport.comp_homeomorph T.toHomeomorph
  obtain ⟨N, hN⟩ := (hζ.continuous_fderiv (by norm_num)).norm.bddAbove_range_of_hasCompactSupport
    ((hc.fderiv ℝ).comp_left norm_zero)
  refine ⟨ζ, max N 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hζ, hc, ?_,
    (fun z => ⟨b.nonneg, b.le_one⟩), ?_, fun z => (hN (Set.mem_range_self z)).trans
      (le_max_left _ _)⟩
  · intro z hz
    have hz' : T z ∈ Metric.closedBall ((5 / 2 : ℝ), 0) (5 / 4) := by
      have heq := tsupport_comp_eq_preimage (b : (ℝ × EuclideanSpace ℝ (Fin d)) → ℝ)
        T.toHomeomorph
      rw [b.tsupport_eq] at heq
      exact (Set.ext_iff.mp heq z).mp hz
    have hdist : max |z.1 - 5 / 2| (euclideanNorm z.2) ≤ 5 / 4 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
        Prod.snd_sub, sub_zero, Real.norm_eq_abs, T, ContinuousLinearEquiv.prodCongr_apply,
        ContinuousLinearEquiv.refl_apply, J, PiLp.continuousLinearEquiv_symm_apply,
        ← TimeChange.euclideanNorm_eq_norm_toLp] using hz'
    have ht := abs_le.mp ((le_max_left _ _).trans hdist)
    have hx := (le_max_right _ _).trans hdist
    exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, by change euclideanNorm z.2 < 2; linarith⟩
  · intro z hz
    apply b.one_of_mem_closedBall
    have ht : |z.1 - 5 / 2| ≤ 1 := abs_le.mpr ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    have hx : euclideanNorm z.2 ≤ 1 := hz.2.le
    simpa only [Metric.mem_closedBall, dist_eq_norm, Prod.norm_def, Prod.fst_sub,
      Prod.snd_sub, sub_zero, Real.norm_eq_abs, T, ContinuousLinearEquiv.prodCongr_apply,
      ContinuousLinearEquiv.refl_apply, J, PiLp.continuousLinearEquiv_symm_apply,
      ← TimeChange.euclideanNorm_eq_norm_toLp] using max_le ht hx

end EinsteinRelation.Correctors
