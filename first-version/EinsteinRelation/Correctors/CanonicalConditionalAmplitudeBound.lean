import EinsteinRelation.Correctors.CanonicalConditionalCenterVersions
import EinsteinRelation.Correctors.LocalMollifierGradientConstruction
import EinsteinRelation.Correctors.LocalAverageError
import EinsteinRelation.Correctors.KernelLpContraction

/-! # Amplitude of the common conditional mollifier fields

Source: `paper/main.tex:942–947`. Conditional contraction and unit-mass
averaging preserve a source amplitude estimate. The source moments are
internal obligations, to be obtained from the corrector estimates; no
amplitude estimate is added to the literature boundary.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace
local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- Unit-mass averaging of the actual conditional source preserves a
uniform probability-moment bound. Source: `paper/main.tex:942–947`. -/
theorem eLpNorm_centered_conditional_mollifier_le
    {d : ℕ} {L r₀ R p C : ℝ} (Q : EnvironmentLaw d L r₀) (hR : 0 < R)
    (hp : 1 ≤ p) (hC : 0 ≤ C) (u : FieldPair d → Vec d → ℝ)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hui : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      Integrable (fun ω => u ω (-y.1)) (reducedEnvironmentLaw Q))
    (hb : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      eLpNorm (fun ω => u (translate y.1 ω) (-y.1))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) :
    MemLp (fun ω => ∫ y, Calculus.unitMassScaledMollifier d R (-y) *
      conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate y ω) (-y))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
    eLpNorm (fun ω => ∫ y, Calculus.unitMassScaledMollifier d R (-y) *
      conditionalSpatialAverage
        (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
        (reducedEnvironmentLaw Q) u (translate y ω) (-y))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C := by
  letI := finiteMeasure_mollifierCenterDomain (d := d) R
  let v : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ := fun z =>
    conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate z.1.1 z.2) (-z.1.1)
  have hvm : Measurable v := measurable_centered_conditionalSpatialAverage Q u hum
  have hvb (y : {y : Vec d // euclideanNorm y ≤ R}) :
      eLpNorm (fun ω => v (y, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal C := by
    rw [eLpNorm_congr_ae (centered_conditionalSpatialAverage_ae_eq_condExp
      Q R u hum y.1 (hui y))]
    let U : Set (Vec d) := {x | euclideanNorm (x - y.1) < 32 * R}
    have heval : Measurable (fun (ω : FieldPair d) (x : U) => ω.1 x) :=
      measurable_pi_lambda _ fun x =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable
    have hpres : MeasurePreserving (translate y.1)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
    have hfi := hpres.integrable_comp_of_integrable (hui y)
    have hc := eLpNorm_condExp_comap_le _ heval
      (ENNReal.one_le_ofReal.mpr hp) ENNReal.ofReal_ne_top hfi
    rw [← reducedCoefficientObservationSigma_eq_comap_evaluation] at hc
    exact hc.trans (hb y)
  let w : {y : Vec d // euclideanNorm y ≤ R} → ℝ :=
    fun y => Calculus.unitMassScaledMollifier d R (-y.1)
  have hwm : Measurable w :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp
      measurable_subtype_coe.neg
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have hc : Continuous (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.comp continuous_neg
  have hcs : HasCompactSupport (fun y : Vec d => Calculus.unitMassScaledMollifier d R (-y)) :=
    (Entropy.hasCompactSupport_unitMassScaledMollifier hR).comp_homeomorph (Homeomorph.neg _)
  have hwi : Integrable w volume :=
    (integrableOn_iff_comap_subtypeVal hS).mp (hc.integrable_of_hasCompactSupport hcs).integrableOn
  have hw : (∫ y, w y) = 1 := integral_center_mollifier_eq_one hR
  have hw0 (y) : 0 ≤ w y := Entropy.unitMassScaledMollifier_nonneg' hR _
  have hwabs : (∫ y, |w y|) = 1 := by
    simpa only [abs_of_nonneg (hw0 _)] using hw
  obtain ⟨_, hmem, hnorm⟩ := local_average_error_bound
    (reducedEnvironmentLaw Q) volume hp hC w hwm hwi hw v hvm
    (fun _ => (0 : ℝ)) measurable_const (fun y => by
      simpa only [sub_zero] using
        (show MemLp (fun ω => v (y, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
          eLpNorm (fun ω => v (y, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal C from
          ⟨⟨(hvm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable,
            (hvb y).trans_lt ENNReal.ofReal_lt_top⟩, hvb y⟩))
  simpa only [mollifier_integral_eq_centerIntegral hR, v, w, smul_eq_mul,
    sub_zero, hwabs, mul_one] using And.intro hmem hnorm

/-- The Frobenius norm is bounded by the sum of the absolute entries.
Source: `paper/main.tex:942–947`. -/
theorem frobeniusNorm_le_sum_abs_entries {d : ℕ} (M : Mat d) :
    frobeniusNorm M ≤ ∑ j, ∑ k, |M j k| := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)), ?_⟩
  calc
    _ ≤ ∑ j : Fin d, (∑ k : Fin d, |M j k|) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [sq_abs, ← sq] using
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun k => |M j k|)
          (fun k _ => abs_nonneg _)
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg
      (fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg (M j k))

/-- Entrywise probability moments control the actual Frobenius moment.
Source: `paper/main.tex:942–947`. -/
theorem eLpNorm_frobeniusNorm_le_sum_entries {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {μ : Measure Ω} {p : ENNReal} (hp : 1 ≤ p)
    (F : Ω → Mat d) (hF : Measurable F) :
    eLpNorm (fun ω => frobeniusNorm (F ω)) p μ ≤
      ∑ j : Fin d, ∑ k : Fin d, eLpNorm (fun ω => F ω j k) p μ := by
  have he (j k : Fin d) : Measurable (fun ω => |F ω j k|) :=
    ((continuous_id.matrix_elem j k).measurable.comp hF).norm
  have hr (j : Fin d) : Measurable (fun ω => ∑ k : Fin d, |F ω j k|) :=
    Finset.measurable_fun_sum _ fun k _ => he j k
  have ho : eLpNorm (fun ω => ∑ j : Fin d, ∑ k : Fin d, |F ω j k|) p μ ≤
      ∑ j : Fin d, eLpNorm (fun ω => ∑ k : Fin d, |F ω j k|) p μ := by
    simpa only [Finset.sum_fn] using
      eLpNorm_sum_le (μ := μ) (f := fun j ω => ∑ k : Fin d, |F ω j k|)
        (s := Finset.univ) (fun j _ => (hr j).aestronglyMeasurable) hp
  have hi (j : Fin d) : eLpNorm (fun ω => ∑ k : Fin d, |F ω j k|) p μ ≤
      ∑ k : Fin d, eLpNorm (fun ω => F ω j k) p μ := by
    have hs := eLpNorm_sum_le (μ := μ) (f := fun k ω => |F ω j k|)
      (s := Finset.univ) (fun k _ => (he j k).aestronglyMeasurable) hp
    simp only [Finset.sum_fn] at hs
    exact hs.trans_eq (Finset.sum_congr rfl fun k _ => by
      simpa only [Real.norm_eq_abs] using
        eLpNorm_norm (p := p) (μ := μ) (fun ω => F ω j k))
  have hpoint (ω : Ω) : ‖frobeniusNorm (F ω)‖ ≤ ∑ j, ∑ k, |F ω j k| := by
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ frobeniusNorm (F ω) from Real.sqrt_nonneg _)]
    exact frobeniusNorm_le_sum_abs_entries (F ω)
  exact (eLpNorm_mono_real hpoint).trans
    (ho.trans (Finset.sum_le_sum fun j _ => hi j))

/-- Scalar and entrywise source amplitudes control the actual common scalar
and Frobenius skew average. Source: `paper/main.tex:942–947`. -/
theorem canonicalConditionalMollifierFields_amplitude_bound
    {d : ℕ} {L r₀ R p C : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (hR : 0 < R) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
    (hum : StronglyMeasurable (Function.uncurry u))
    (hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
    (hui : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      Integrable (fun ω => u ω (-y.1)) (reducedEnvironmentLaw Q))
    (hSi : ∀ j k (y : {y : Vec d // euclideanNorm y ≤ R}),
      Integrable (fun ω => S ω (-y.1) j k) (reducedEnvironmentLaw Q))
    (hu : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      eLpNorm (fun ω => u (translate y.1 ω) (-y.1))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C)
    (hS : ∀ j k (y : {y : Vec d // euclideanNorm y ≤ R}),
      eLpNorm (fun ω => S (translate y.1 ω) (-y.1) j k)
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) :
    let f := canonicalConditionalMollifierFields Q i R u S
    eLpNorm f.scalar (ENNReal.ofReal p) (reducedEnvironmentLaw Q) +
      eLpNorm (fun ω => frobeniusNorm (f.skew ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal ((1 + (d : ℝ) * d) * C) := by
  let f := canonicalConditionalMollifierFields Q i R u S
  have hφ := (eLpNorm_centered_conditional_mollifier_le Q hR hp hC u hum hui hu).2
  have hentry (j k : Fin d) : eLpNorm (fun ω => f.skew ω j k)
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C :=
    (eLpNorm_centered_conditional_mollifier_le Q hR hp hC
      (fun a x => S a x j k) (hSm j k) (hSi j k) (hS j k)).2
  have hm : Measurable f.skew := by
    have hobs : reducedCoefficientObservationSigma
        {x : Vec d | euclideanNorm x < 33 * R} ≤ borel (FieldPair d) := by
      rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
      exact (measurable_pi_lambda _ fun x : {x : Vec d | euclideanNorm x < 33 * R} =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
    exact (measurable_canonicalConditionalMollifierFields Q i hR u S hum hSm).2.1.mono
      hobs le_rfl
  have hskew : eLpNorm (fun ω => frobeniusNorm (f.skew ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal ((d : ℝ) * d * C) := by
    calc
      _ ≤ ∑ j : Fin d, ∑ k : Fin d, eLpNorm (fun ω => f.skew ω j k)
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) :=
        eLpNorm_frobeniusNorm_le_sum_entries (ENNReal.one_le_ofReal.mpr hp) f.skew hm
      _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, ENNReal.ofReal C :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ d)]
        congr 1
        ring
  calc
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal ((d : ℝ) * d * C) := add_le_add hφ hskew
    _ = _ := by
      rw [← ENNReal.ofReal_add hC (by positivity)]
      congr 1
      ring

end EinsteinRelation.Correctors
