import EinsteinFull.External.DFGW.DynkinDyadicObservableMoment

/-! # Real dyadic observable maxima

The square-integrable dyadic supremum has a measurable real representative that dominates
the observable at every dyadic time almost surely.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The real representative of the dyadic supremum of a generator-domain observable. -/
noncomputable def dyadicObservableSup (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) (η : C(ℝ, S)) : ℝ :=
  (⨆ r : ℕ, ⨆ k ≤ 2 ^ r, ENNReal.ofReal
    |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|).toReal

/-- The dyadic observable supremum is measurable. -/
theorem measurable_dyadicObservableSup (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    Measurable (dyadicObservableSup hP f t) := by
  apply Measurable.ennreal_toReal
  apply Measurable.iSup
  intro r
  apply Measurable.iSup
  intro k
  apply Measurable.iSup
  intro hk
  exact (continuous_abs.measurable.comp
    ((Lp.stronglyMeasurable (f : Lp ℝ 2 μ)).measurable.comp
      (continuous_eval_const _).measurable)).ennreal_ofReal

/-- The real dyadic supremum belongs to `L²`. -/
theorem memLp_dyadicObservableSup
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    MemLp (dyadicObservableSup hP f t) 2 P := by
  have hmeas : AEStronglyMeasurable (dyadicObservableSup hP f t) P :=
    (measurable_dyadicObservableSup hP f t).aestronglyMeasurable
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num) hmeas]
  have hbound : (∫⁻ η, ‖dyadicObservableSup hP f t η‖ₑ ^ (2 : ℝ) ∂P) ≤
      ∫⁻ η, (⨆ r : ℕ, ⨆ k ≤ 2 ^ r, ENNReal.ofReal
        |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|) ^ 2 ∂P := by
    apply lintegral_mono
    intro η
    simp only [← ofReal_norm, Real.norm_eq_abs, ENNReal.rpow_two,
      abs_of_nonneg ENNReal.toReal_nonneg, dyadicObservableSup]
    exact pow_le_pow_left' ENNReal.ofReal_toReal_le 2
  exact lt_of_le_of_lt hbound (lintegral_sup_dyadic_observable_lt_top hP hcoord f t)

/-- Almost surely the real dyadic supremum dominates each observable value on the grid. -/
theorem ae_abs_le_dyadicObservableSup
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    ∀ᵐ η ∂P, ∀ r k : ℕ, k ≤ 2 ^ r →
      |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))| ≤ dyadicObservableSup hP f t η := by
  let G : C(ℝ, S) → ℝ≥0∞ := fun η => ⨆ r : ℕ, ⨆ k ≤ 2 ^ r, ENNReal.ofReal
    |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))|
  have hG : Measurable G := by
    apply Measurable.iSup
    intro r
    apply Measurable.iSup
    intro k
    apply Measurable.iSup
    intro hk
    exact (continuous_abs.measurable.comp
      ((Lp.stronglyMeasurable (f : Lp ℝ 2 μ)).measurable.comp
        (continuous_eval_const _).measurable)).ennreal_ofReal
  have hfinite := ae_lt_top (hG.pow_const 2)
    (lintegral_sup_dyadic_observable_lt_top hP hcoord f t).ne
  filter_upwards [hfinite] with η hη r k hk
  have hGne : G η ≠ ⊤ := by
    intro he
    rw [he] at hη
    norm_num at hη
  have hle : ENNReal.ofReal |(f : Lp ℝ 2 μ) (η (dyadicGridTime t r k))| ≤ G η :=
    le_iSup_of_le r (le_iSup_of_le k (le_iSup_of_le hk le_rfl))
  have hreal := ENNReal.toReal_mono hGne hle
  simpa only [ENNReal.toReal_ofReal (abs_nonneg _), dyadicObservableSup, G] using hreal

end EinsteinFull.External.DFGW
