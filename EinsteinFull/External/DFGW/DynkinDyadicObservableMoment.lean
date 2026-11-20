import EinsteinFull.External.DFGW.DynkinDyadicObservableBound
import EinsteinFull.External.DFGW.FiniteSquareLIntegral
import EinsteinFull.External.DFGW.TimeIntegralBound

/-! # Second moment of dyadic observable maxima

A generator-domain observable has a square-integrable supremum over dyadic times on every
bounded interval of a stationary trajectory.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The dyadic supremum of a generator-domain observable has finite second moment. -/
theorem lintegral_sup_dyadic_observable_lt_top
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    (∫⁻ η, (⨆ r : ℕ, ⨆ k ≤ 2 ^ r, ENNReal.ofReal
      |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|) ^ 2 ∂P) < ⊤ := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g := (transitionSemigroup hP).generator f
  let M : ℝ≥0 → C(ℝ, S) → ℝ := fun s η => dynkinProcess hP f s η - dynkinProcess hP f 0 η
  let J : C(ℝ, S) → ℝ≥0∞ := fun η => ⨆ r : ℕ, ⨆ k ≤ 2 ^ r,
    ENNReal.ofReal |M (dyadicGridTime t r k) η|
  let I : C(ℝ, S) → ℝ≥0∞ := fun η => ENNReal.ofReal |(f : Lp ℝ 2 μ) (η 0)|
  let H : C(ℝ, S) → ℝ≥0∞ := fun η => ENNReal.ofReal |(∫ u in (0 : ℝ)..t, |g (η u)|)|
  have hM : Martingale M Draft.dfgwPast P := martingale_dynkin_increment hP hcoord f
  have hJ : Measurable J := by
    apply Measurable.iSup
    intro r
    apply Measurable.iSup
    intro k
    apply Measurable.iSup
    intro hk
    exact (continuous_abs.measurable.comp
      ((hM.stronglyMeasurable (dyadicGridTime t r k)).mono
        (Draft.dfgwPast.le (dyadicGridTime t r k))).measurable).ennreal_ofReal
  have hI : Measurable I := by
    exact (continuous_abs.measurable.comp
      ((Lp.stronglyMeasurable (f : Lp ℝ 2 μ)).measurable.comp
        (continuous_eval_const 0).measurable)).ennreal_ofReal
  have hJ2 : (∫⁻ η, J η ^ 2 ∂P) < ⊤ := by
    have h := lintegral_sup_dyadic_dynkin_increment_lt_top hP hcoord f t
    have heq (η : C(ℝ, S)) : J η ^ 2 = ⨆ r : ℕ,
        (⨆ k ≤ 2 ^ r, ENNReal.ofReal |M (dyadicGridTime t r k) η|) ^ 2 :=
      ENNReal.iSup_pow _ 2
    simpa only [heq, M] using h
  have heval : MeasurePreserving (fun η : C(ℝ, S) => η 0) P μ :=
    ⟨(continuous_eval_const 0).measurable, hP.marginal 0⟩
  have hI2 : (∫⁻ η, I η ^ 2 ∂P) < ⊤ :=
    lintegral_ofReal_abs_sq_lt_top _ ((Lp.memLp (f : Lp ℝ 2 μ)).comp_measurePreserving heval)
  have hH2 : (∫⁻ η, H η ^ 2 ∂P) < ⊤ :=
    lintegral_ofReal_abs_sq_lt_top _
      (time_integral_memLp_and_sq_le hP (fun x => |g x|) (Lp.memLp g).abs t.coe_nonneg).1
  have hsum : (∫⁻ η, (J η + I η + H η) ^ 2 ∂P) < ⊤ :=
    lintegral_add_sq_lt_top (J + I) H (hJ.add hI)
      (lintegral_add_sq_lt_top J I hJ hJ2 hI2) hH2
  have hpoint : ∀ᵐ η ∂P, (⨆ r : ℕ, ⨆ k ≤ 2 ^ r, ENNReal.ofReal
      |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|) ^ 2 ≤ (J η + I η + H η) ^ 2 := by
    filter_upwards [ae_abs_observable_dyadic_le hP f t] with η hη
    apply pow_le_pow_left' _ 2
    refine iSup_le fun r => iSup_le fun k => iSup_le fun hk => ?_
    have hsmall := hη r k hk
    have hreal : |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))| ≤
        |M (dyadicGridTime t r k) η| + |(f : Lp ℝ 2 μ) (η 0)| +
          |(∫ u in (0 : ℝ)..t, |g (η u)|)| := by
      dsimp only [M, g] at hsmall ⊢
      linarith [le_abs_self (∫ u in (0 : ℝ)..t, |(transitionSemigroup hP).generator f (η u)|)]
    have hJle : ENNReal.ofReal |M (dyadicGridTime t r k) η| ≤ J η :=
      le_iSup_of_le r (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
    calc
      ENNReal.ofReal |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))| ≤
          ENNReal.ofReal (|M (dyadicGridTime t r k) η| +
            |(f : Lp ℝ 2 μ) (η 0)| + |(∫ u in (0 : ℝ)..t, |g (η u)|)|) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal |M (dyadicGridTime t r k) η| + I η + H η := by
        simp only [I, H, ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _),
          ENNReal.ofReal_add (add_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _)]
      _ ≤ J η + I η + H η := by gcongr
  exact lt_of_le_of_lt (lintegral_mono_ae hpoint) hsum

end EinsteinFull.External.DFGW
