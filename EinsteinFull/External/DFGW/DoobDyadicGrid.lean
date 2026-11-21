import EinsteinFull.External.DFGW.DynkinDyadicMaximal
import LatticeProb.Prob.Process.BDGFreedman

/-! # Doob bounds on dyadic grids

The discrete Doob inequality controls the maximum of a continuous-time martingale on each
finite dyadic grid by its terminal second moment.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- A square-integrable martingale starting at zero has uniformly bounded squared dyadic
grid maxima. -/
theorem exists_lintegral_max_dyadic_martingale_le
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P) (hzero : ∀ ω, M 0 ω = 0)
    (t : ℝ≥0) : ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ,
      (∫⁻ ω, (⨆ k ≤ 2 ^ r, ENNReal.ofReal |M (dyadicGridTime t r k) ω|) ^ (2 : ℝ) ∂P) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal |M t ω| ^ (2 : ℝ) ∂P := by
  obtain ⟨C, hC, hDoob⟩ := LatticeProb.Process.RandomizedFreedman.doobMaximalLp_holds
    2 (by norm_num)
  refine ⟨C, hC, fun r => ?_⟩
  let u : ℝ≥0 := t / ((2 ^ r : ℕ) : ℝ≥0)
  let F : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq := fun k => ℱ (k • u)
      mono' := fun _ _ h => ℱ.mono (nsmul_le_nsmul_left (show 0 ≤ u from bot_le) h)
      le' := fun k => ℱ.le (k • u) }
  let X : ℕ → Ω → ℝ := fun k ω => M (k • u) ω
  have hX : Martingale X F P := by
    constructor
    · intro k
      exact hM.stronglyMeasurable (k • u)
    · intro k l hkl
      exact hM.condExp_ae_eq (nsmul_le_nsmul_left (show 0 ≤ u from bot_le) hkl)
  have hXzero : ∀ ω, X 0 ω = 0 := by
    intro ω
    simpa only [X, zero_nsmul] using hzero ω
  have h := hDoob P F X (2 ^ r) hX hXzero
  have hlast : (2 ^ r : ℕ) • u = t := dyadicGridTime_last t r
  simpa only [X, u, dyadicGridTime, hlast] using h

/-- The squared supremum of a martingale over all dyadic times has a finite Doob bound. -/
theorem exists_lintegral_sup_dyadic_martingale_le
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P) (hzero : ∀ ω, M 0 ω = 0)
    (t : ℝ≥0) : ∃ C : ℝ, 0 < C ∧
      (∫⁻ ω, ⨆ r : ℕ, (⨆ k ≤ 2 ^ r, ENNReal.ofReal |M (dyadicGridTime t r k) ω|) ^ 2 ∂P) ≤
        ENNReal.ofReal C * ∫⁻ ω, ENNReal.ofReal |M t ω| ^ 2 ∂P := by
  obtain ⟨C, hC, hgrid⟩ := exists_lintegral_max_dyadic_martingale_le M hM hzero t
  refine ⟨C, hC, ?_⟩
  let F (r : ℕ) (ω : Ω) : ℝ≥0∞ :=
    (⨆ k ≤ 2 ^ r, ENNReal.ofReal |M (dyadicGridTime t r k) ω|) ^ 2
  have hF (r : ℕ) : Measurable (F r) := by
    apply Measurable.pow_const
    apply Measurable.iSup
    intro k
    apply Measurable.iSup
    intro hk
    exact (((hM.stronglyMeasurable (dyadicGridTime t r k)).mono
      (ℱ.le (dyadicGridTime t r k))).measurable.abs).ennreal_ofReal
  have hmono : Monotone F := by
    apply monotone_nat_of_le_succ
    intro r ω
    dsimp only [F]
    apply pow_le_pow_left' _ 2
    refine iSup_le fun k => iSup_le fun hk => ?_
    have hk' : 2 * k ≤ 2 ^ (r + 1) := by rw [pow_succ]; omega
    refine le_iSup_of_le (2 * k) (le_iSup_of_le hk' ?_)
    rw [dyadicGridTime_succ]
  change (∫⁻ ω, ⨆ r, F r ω ∂P) ≤ _
  rw [lintegral_iSup hF hmono]
  apply iSup_le
  intro r
  have h := hgrid r
  simpa only [F, ENNReal.rpow_two] using h

/-- A square-integrable terminal value gives a square-integrable dyadic supremum. -/
theorem lintegral_sup_dyadic_martingale_lt_top
    (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P) (hzero : ∀ ω, M 0 ω = 0)
    (t : ℝ≥0) (hM2 : MemLp (M t) 2 P) :
    (∫⁻ ω, ⨆ r : ℕ, (⨆ k ≤ 2 ^ r, ENNReal.ofReal |M (dyadicGridTime t r k) ω|) ^ 2 ∂P) < ⊤ := by
  obtain ⟨C, _, hbound⟩ := exists_lintegral_sup_dyadic_martingale_le M hM hzero t
  have hterm : (∫⁻ ω, ENNReal.ofReal |M t ω| ^ 2 ∂P) < ⊤ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (p := (2 : ℝ≥0∞)) (f := M t) (μ := P) (by norm_num) (by norm_num) hM2
    simpa only [ENNReal.toReal_ofNat, ← ofReal_norm, Real.norm_eq_abs,
      ENNReal.rpow_two] using h
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hterm)

end EinsteinFull.External.DFGW
