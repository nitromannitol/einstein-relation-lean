import EinsteinFull.Calculus.C8VelocityTransport
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinFull.Frozen.RealLocalObservation
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linter.Lint

/-!
Reflection of the actual reduced joint law and its complex L² space.
The reflected law is a pushforward; no symmetry of the original law is assumed.
-/

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

noncomputable section
namespace EinsteinFull.SbxS10KmReflection
open EinsteinRelation

theorem reduce_reflect (d : ℕ) (ω : FieldPair d) :
    reduce (reflectEnvironment ω) = reflectEnvironment (reduce ω) := by
  apply Prod.ext <;> ext x <;> rfl

theorem reducedLaw_reflected {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) :
    reducedLaw (reflectedEnvironmentLaw Q) = (reducedLaw Q).map reflectEnvironment := by
  have hr := (continuous_reflectEnvironment (d := d)).measurable
  unfold reducedLaw
  rw [reflectedEnvironmentLaw_measure, Measure.map_map Probability.measurable_reduce hr,
    Measure.map_map hr Probability.measurable_reduce]
  congr 1

theorem measurePreserving_reflect {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) :
    MeasurePreserving reflectEnvironment (reducedLaw Q)
      (reducedLaw (reflectedEnvironmentLaw Q)) :=
  ⟨(continuous_reflectEnvironment (d := d)).measurable, (reducedLaw_reflected Q).symm⟩

theorem measurePreserving_reflect_reverse {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) :
    MeasurePreserving reflectEnvironment (reducedLaw (reflectedEnvironmentLaw Q))
      (reducedLaw Q) := by
  refine ⟨(continuous_reflectEnvironment (d := d)).measurable, ?_⟩
  rw [reducedLaw_reflected, Measure.map_map
    (continuous_reflectEnvironment (d := d)).measurable
    (continuous_reflectEnvironment (d := d)).measurable]
  have hi : reflectEnvironment (d := d) ∘ reflectEnvironment = id := by
    funext ω
    exact reflectEnvironment_involutive ω
  rw [hi, Measure.map_id]

/-- Pullback from the reflected reduced law to the original reduced law. -/
def pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) :
    Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q)) ≃ₗᵢ[ℂ] Lp ℂ 2 (reducedLaw Q) where
  __ := Lp.compMeasurePreservingₗᵢ ℂ reflectEnvironment (measurePreserving_reflect Q)
  invFun := Lp.compMeasurePreserving reflectEnvironment (measurePreserving_reflect_reverse Q)
  left_inv f := by
    change Lp.compMeasurePreserving _ (measurePreserving_reflect_reverse Q)
      (Lp.compMeasurePreserving _ (measurePreserving_reflect Q) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_reflect Q)
      (measurePreserving_reflect_reverse Q)]
    have hi : reflectEnvironment (d := d) ∘ reflectEnvironment = id := by
      funext ω
      exact reflectEnvironment_involutive ω
    simp only [hi, Lp.compMeasurePreserving_id_apply]
  right_inv f := by
    change Lp.compMeasurePreserving _ (measurePreserving_reflect Q)
      (Lp.compMeasurePreserving _ (measurePreserving_reflect_reverse Q) f) = f
    rw [← Lp.compMeasurePreserving_comp_apply f (measurePreserving_reflect_reverse Q)
      (measurePreserving_reflect Q)]
    have hi : reflectEnvironment (d := d) ∘ reflectEnvironment = id := by
      funext ω
      exact reflectEnvironment_involutive ω
    simp only [hi, Lp.compMeasurePreserving_id_apply]

theorem pullback_ae {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) :
    (pullback Q f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => f (reflectEnvironment ω) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_reflect Q)

theorem pullback_symm_ae {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ((pullback Q).symm f : FieldPair d → ℂ) =ᵐ[reducedLaw (reflectedEnvironmentLaw Q)]
      fun ω => f (reflectEnvironment ω) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_reflect_reverse Q)

theorem eLpNorm_pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) (p : ℝ≥0∞) :
    eLpNorm (pullback Q f : FieldPair d → ℂ) p (reducedLaw Q) =
      eLpNorm (f : FieldPair d → ℂ) p (reducedLaw (reflectedEnvironmentLaw Q)) := by
  rw [eLpNorm_congr_ae (pullback_ae Q f)]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
    (measurePreserving_reflect Q)

theorem integral_pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) :
    (∫ ω, pullback Q f ω ∂reducedLaw Q) =
      ∫ ω, f ω ∂reducedLaw (reflectedEnvironmentLaw Q) := by
  rw [integral_congr_ae (pullback_ae Q f)]
  exact (measurePreserving_reflect Q).integral_comp
    (reflectEnvironmentHomeomorph d).measurableEmbedding _

theorem integral_mul_pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f g : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) :
    (∫ ω, pullback Q f ω * pullback Q g ω ∂reducedLaw Q) =
      ∫ ω, f ω * g ω ∂reducedLaw (reflectedEnvironmentLaw Q) := by
  calc
    _ = ∫ ω, f (reflectEnvironment ω) * g (reflectEnvironment ω) ∂reducedLaw Q :=
      integral_congr_ae ((pullback_ae Q f).mul (pullback_ae Q g))
    _ = _ := (measurePreserving_reflect Q).integral_comp
      (reflectEnvironmentHomeomorph d).measurableEmbedding (fun ω => f ω * g ω)

theorem localSigma_reflect_ball {d : ℕ} (R : ℝ) :
    (localSigma {x : Vec d | euclideanNorm x < R}).comap reflectEnvironment ≤
      localSigma {x : Vec d | euclideanNorm x < R} := by
  have he : (fun x : Vec d => -x) ⁻¹' {x | euclideanNorm x < R} =
      {x | euclideanNorm x < R} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, euclideanNorm, euclideanSq, dot,
      Pi.neg_apply, neg_mul_neg]
  simpa only [he] using
    localSigma_reflectEnvironment_comap_le {x : Vec d | euclideanNorm x < R}

theorem realLocal_pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {R : ℝ} {F : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))}
    (hF : IsRealLocalObservation (reflectedEnvironmentLaw Q) R F) :
    IsRealLocalObservation Q R (pullback Q F) := by
  obtain ⟨f, hf, he⟩ := hF
  refine ⟨f ∘ reflectEnvironment,
    hf.comp (Measurable.of_comap_le (localSigma_reflect_ball R)), ?_⟩
  filter_upwards [(measurePreserving_reflect Q).quasiMeasurePreserving.ae he,
    pullback_ae Q F] with ω h₁ h₂
  exact h₁.trans h₂.symm

theorem realLocal_pullback_symm {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {R : ℝ} {F : Lp ℂ 2 (reducedLaw Q)} (hF : IsRealLocalObservation Q R F) :
    IsRealLocalObservation (reflectedEnvironmentLaw Q) R ((pullback Q).symm F) := by
  obtain ⟨f, hf, he⟩ := hF
  refine ⟨f ∘ reflectEnvironment,
    hf.comp (Measurable.of_comap_le (localSigma_reflect_ball R)), ?_⟩
  filter_upwards [(measurePreserving_reflect_reverse Q).quasiMeasurePreserving.ae he,
    pullback_symm_ae Q F] with ω h₁ h₂
  exact h₁.trans h₂.symm

theorem pullback_translation {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (x : Vec d) (f : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) :
    pullback Q (complexTranslation _ (reducedLaw_stationary _) x f) =
      complexTranslation _ (reducedLaw_stationary _) (-x) (pullback Q f) := by
  apply Lp.ext
  have ht := Lp.coeFn_compMeasurePreserving f
    (measurePreserving_translate _ (reducedLaw_stationary (reflectedEnvironmentLaw Q)) x)
  have hp := (measurePreserving_reflect Q).quasiMeasurePreserving.ae ht
  have hu := (measurePreserving_translate _ (reducedLaw_stationary Q) (-x)).quasiMeasurePreserving.ae
    (pullback_ae Q f)
  filter_upwards [pullback_ae Q (complexTranslation _ (reducedLaw_stationary _) x f),
    hp, Lp.coeFn_compMeasurePreserving (pullback Q f)
      (measurePreserving_translate _ (reducedLaw_stationary Q) (-x)), hu] with ω h₁ h₂ h₃ h₄
  change complexTranslation _ (reducedLaw_stationary _) x f (reflectEnvironment ω) =
    f (translate x (reflectEnvironment ω)) at h₂
  change complexTranslation _ (reducedLaw_stationary _) (-x) (pullback Q f) ω =
    pullback Q f (translate (-x) ω) at h₃
  rw [h₁, h₂, h₃, h₄, reflectEnvironment_translate, neg_neg]

theorem pullback_symm_translation {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (x : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    (pullback Q).symm (complexTranslation _ (reducedLaw_stationary _) x f) =
      complexTranslation _ (reducedLaw_stationary _) (-x) ((pullback Q).symm f) := by
  apply (pullback Q).injective
  rw [(pullback Q).apply_symm_apply, pullback_translation, neg_neg,
    (pullback Q).apply_symm_apply]

/-- A translation-conjugating isometry reverses the literal two-sided derivative. -/
theorem horizontalDerivative_of_conjugacy {d : ℕ} {μ ν : Measure (FieldPair d)}
    {hμ : IsStationary μ} {hν : IsStationary ν}
    (e : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (he : ∀ x f, e (complexTranslation μ hμ x f) =
      complexTranslation ν hν (-x) (e f))
    {i : Fin d} {f g : Lp ℂ 2 μ} (h : HasComplexHorizontalDerivative μ hμ i f g) :
    HasComplexHorizontalDerivative ν hν i (e f) (-e g) := by
  have hn : Tendsto (fun t : ℝ => -t) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · simpa only [neg_zero] using
        (continuous_neg.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, neg_eq_zero] using ht
  have hh := ((e.continuous.tendsto g).comp (h.comp hn)).neg
  unfold HasComplexHorizontalDerivative
  apply hh.congr
  intro t
  change -(e (((-t : ℝ) : ℂ)⁻¹ •
    (complexTranslation μ hμ ((-t) • unitVector i) f - f))) =
      (t : ℂ)⁻¹ • (complexTranslation ν hν (t • unitVector i) (e f) - e f)
  rw [map_smul, map_sub, he]
  simp only [neg_smul, neg_neg, Complex.ofReal_neg, inv_neg]

theorem horizontalDerivative_pullback {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))}
    (h : HasComplexHorizontalDerivative _ (reducedLaw_stationary _) i f g) :
    HasComplexHorizontalDerivative _ (reducedLaw_stationary _) i (pullback Q f)
      (-pullback Q g) :=
  horizontalDerivative_of_conjugacy (pullback Q) (pullback_translation Q) h

theorem horizontalDerivative_pullback_symm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {i : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (h : HasComplexHorizontalDerivative _ (reducedLaw_stationary _) i f g) :
    HasComplexHorizontalDerivative _ (reducedLaw_stationary _) i ((pullback Q).symm f)
      (-(pullback Q).symm g) :=
  horizontalDerivative_of_conjugacy (pullback Q).symm (pullback_symm_translation Q) h

theorem translation_conjugacy_symm {d : ℕ} {μ ν : Measure (FieldPair d)}
    {hμ : IsStationary μ} {hν : IsStationary ν}
    (e : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν)
    (he : ∀ x f, e (complexTranslation μ hμ x f) =
      complexTranslation ν hν (-x) (e f)) (x : Vec d) (f : Lp ℂ 2 ν) :
    e.symm (complexTranslation ν hν x f) =
      complexTranslation μ hμ (-x) (e.symm f) := by
  apply e.injective
  rw [e.apply_symm_apply, he, neg_neg, e.apply_symm_apply]

/-- Reflection transports every weak test in the full generator graph. -/
theorem generatorPair_of_reflection {d : ℕ} {Λ r₀ : ℝ}
    (Q Q' : EnvironmentLaw d Λ r₀)
    (e : Lp ℂ 2 (reducedLaw Q) ≃ₗᵢ[ℂ] Lp ℂ 2 (reducedLaw Q'))
    (hm : MeasurePreserving reflectEnvironment (reducedLaw Q') (reducedLaw Q))
    (hae : ∀ f, (e f : FieldPair d → ℂ) =ᵐ[reducedLaw Q']
      fun ω => f (reflectEnvironment ω))
    (he : ∀ x f, e (complexTranslation _ (reducedLaw_stationary Q) x f) =
      complexTranslation _ (reducedLaw_stationary Q') (-x) (e f))
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) :
    IsComplexGeneratorPair Q' i (-ζ) (e f) (e g) := by
  obtain ⟨G, hG, hweak⟩ := hfg
  refine ⟨fun j => -e (G j), fun j =>
    horizontalDerivative_of_conjugacy e he (hG j), ?_⟩
  intro v Gv hv
  let w := e.symm v
  let Gw := fun j => -e.symm (Gv j)
  have hw : HasComplexHorizontalGradient _ (reducedLaw_stationary Q) w Gw :=
    fun j => horizontalDerivative_of_conjugacy e.symm
      (translation_conjugacy_symm e he) (hv j)
  have htest := hweak w Gw hw
  have hwval : (v : FieldPair d → ℂ) =ᵐ[reducedLaw Q']
      fun ω => w (reflectEnvironment ω) := by
    simpa only [w, e.apply_symm_apply] using hae w
  have hGval : ∀ᵐ ω ∂reducedLaw Q', ∀ j,
      (-e (G j)) ω = -(G j) (reflectEnvironment ω) := by
    apply ae_all_iff.mpr
    intro j
    filter_upwards [hae (G j), Lp.coeFn_neg (e (G j))] with ω h₁ h₂
    exact h₂.trans (congrArg Neg.neg h₁)
  have hGwval : ∀ᵐ ω ∂reducedLaw Q', ∀ j,
      Gv j ω = -(Gw j) (reflectEnvironment ω) := by
    apply ae_all_iff.mpr
    intro j
    have hgwe : e (Gw j) = -Gv j := by
      simp only [Gw, map_neg, e.apply_symm_apply]
    have ha := hae (Gw j)
    rw [hgwe] at ha
    filter_upwards [ha, Lp.coeFn_neg (Gv j)] with ω h₁ h₂
    calc
      Gv j ω = -(-(Gv j ω)) := (neg_neg _).symm
      _ = -(Gw j) (reflectEnvironment ω) := congrArg Neg.neg (h₂.symm.trans h₁)
  have hleft : (∫ ω, e g ω * v ω ∂reducedLaw Q') =
      ∫ ω, g ω * w ω ∂reducedLaw Q := by
    calc
      _ = ∫ ω, g (reflectEnvironment ω) * w (reflectEnvironment ω) ∂reducedLaw Q' :=
        integral_congr_ae ((hae g).mul hwval)
      _ = _ := hm.integral_comp (reflectEnvironmentHomeomorph d).measurableEmbedding
        (fun ω => g ω * w ω)
  have hdiff : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * (-e (G k)) ω * Gv j ω
      ∂reducedLaw Q') =
      ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * Gw j ω ∂reducedLaw Q := by
    calc
      _ = ∫ ω, ∑ j, ∑ k, ((reflectEnvironment ω).1 0 j k : ℂ) *
          G k (reflectEnvironment ω) * Gw j (reflectEnvironment ω) ∂reducedLaw Q' := by
        apply integral_congr_ae
        filter_upwards [hGval, hGwval] with ω h₁ h₂
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        simp only [h₁ k, h₂ j, reflectEnvironment_matrix, neg_zero, mul_neg, neg_mul,
          neg_neg]
      _ = _ := hm.integral_comp (reflectEnvironmentHomeomorph d).measurableEmbedding
        (fun ω => ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * Gw j ω)
  have hdrift : (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * (-e (G j)) ω) * v ω
      ∂reducedLaw Q') =
      -(∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * w ω ∂reducedLaw Q) := by
    calc
      _ = ∫ ω, -((∑ j, ((reflectEnvironment ω).1 0 j i : ℂ) *
          G j (reflectEnvironment ω)) * w (reflectEnvironment ω)) ∂reducedLaw Q' := by
        apply integral_congr_ae
        filter_upwards [hGval, hwval] with ω h₁ h₂
        simp only [h₂, h₁, reflectEnvironment_matrix, neg_zero, mul_neg,
          Finset.sum_neg_distrib, neg_mul]
      _ = _ := by
        rw [integral_neg, hm.integral_comp
          (reflectEnvironmentHomeomorph d).measurableEmbedding
          (fun ω => (∑ j, (ω.1 0 j i : ℂ) * G j ω) * w ω)]
  rw [hleft, hdiff, hdrift]
  simpa only [neg_mul_neg] using htest

theorem generatorPair_pullback {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))}
    (hfg : IsComplexGeneratorPair (reflectedEnvironmentLaw Q) i ζ f g) :
    IsComplexGeneratorPair Q i (-ζ) (pullback Q f) (pullback Q g) :=
  generatorPair_of_reflection (reflectedEnvironmentLaw Q) Q (pullback Q)
    (measurePreserving_reflect Q) (pullback_ae Q) (pullback_translation Q) hfg

theorem generatorPair_pullback_symm {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g) :
    IsComplexGeneratorPair (reflectedEnvironmentLaw Q) i (-ζ)
      ((pullback Q).symm f) ((pullback Q).symm g) :=
  generatorPair_of_reflection Q (reflectedEnvironmentLaw Q) (pullback Q).symm
    (measurePreserving_reflect_reverse Q) (pullback_symm_ae Q)
    (pullback_symm_translation Q) hfg

theorem generatorPair_pullback_iff {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))} :
    IsComplexGeneratorPair Q i (-ζ) (pullback Q f) (pullback Q g) ↔
      IsComplexGeneratorPair (reflectedEnvironmentLaw Q) i ζ f g := by
  constructor
  · intro h
    simpa only [neg_neg, (pullback Q).symm_apply_apply] using
      generatorPair_pullback_symm Q h
  · exact generatorPair_pullback Q

theorem eLpNorm_pullback_symm {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) (p : ℝ≥0∞) :
    eLpNorm ((pullback Q).symm f : FieldPair d → ℂ) p
        (reducedLaw (reflectedEnvironmentLaw Q)) =
      eLpNorm (f : FieldPair d → ℂ) p (reducedLaw Q) := by
  rw [eLpNorm_congr_ae (pullback_symm_ae Q f)]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f)
    (measurePreserving_reflect_reverse Q)

theorem memLp_pullback_symm {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {f : Lp ℂ 2 (reducedLaw Q)} {p : ℝ≥0∞}
    (hf : MemLp (f : FieldPair d → ℂ) p (reducedLaw Q)) :
    MemLp ((pullback Q).symm f : FieldPair d → ℂ) p
      (reducedLaw (reflectedEnvironmentLaw Q)) := by
  rw [memLp_iff, eLpNorm_pullback_symm]
  exact hf

theorem integral_pullback_symm {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, (pullback Q).symm f ω ∂reducedLaw (reflectedEnvironmentLaw Q)) =
      ∫ ω, f ω ∂reducedLaw Q := by
  rw [integral_congr_ae (pullback_symm_ae Q f)]
  exact (measurePreserving_reflect_reverse Q).integral_comp
    (reflectEnvironmentHomeomorph d).measurableEmbedding _

/-- The entire original evolution conjugated onto the reflected joint law. -/
def reflectedSemigroup {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q)) →L[ℂ]
      Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q)) :=
  (pullback Q).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((S t).comp (pullback Q).toContinuousLinearEquiv.toContinuousLinearMap)

theorem reflectedSemigroup_apply {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw (reflectedEnvironmentLaw Q))) :
    reflectedSemigroup Q S t f = (pullback Q).symm (S t (pullback Q f)) := rfl

theorem isSemigroup_reflected {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ}
    {S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hS : IsComplexEnvironmentSemigroup Q i ζ S) :
    IsComplexEnvironmentSemigroup (reflectedEnvironmentLaw Q) i (-ζ)
      (reflectedSemigroup Q S) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro f
    simp only [reflectedSemigroup_apply, hS.1, ContinuousLinearMap.id_apply,
      (pullback Q).symm_apply_apply]
  · intro s t
    apply ContinuousLinearMap.ext
    intro f
    simp only [reflectedSemigroup_apply, hS.2.1, ContinuousLinearMap.comp_apply,
      (pullback Q).apply_symm_apply]
  · intro f
    exact (pullback Q).symm.continuous.comp (hS.2.2.1 (pullback Q f))
  · intro f g
    constructor
    · intro h
      have ht := ((pullback Q).continuous.tendsto g).comp h
      have hslope : Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
          (S t (pullback Q f) - pullback Q f)) (𝓝[>] 0) (𝓝 (pullback Q g)) := by
        apply ht.congr
        intro t
        change pullback Q (((t : ℝ) : ℂ)⁻¹ • (reflectedSemigroup Q S t f - f)) = _
        rw [map_smul, map_sub, reflectedSemigroup_apply, (pullback Q).apply_symm_apply]
      simpa only [(pullback Q).symm_apply_apply] using
        generatorPair_pullback_symm Q ((hS.2.2.2 _ _).mp hslope)
    · intro h
      have hg : IsComplexGeneratorPair Q i ζ (pullback Q f) (pullback Q g) := by
        simpa only [neg_neg] using generatorPair_pullback Q h
      have ht := ((pullback Q).symm.continuous.tendsto (pullback Q g)).comp
        ((hS.2.2.2 _ _).mpr hg)
      rw [(pullback Q).symm_apply_apply] at ht
      apply ht.congr
      intro t
      change (pullback Q).symm (((t : ℝ) : ℂ)⁻¹ •
        (S t (pullback Q f) - pullback Q f)) = _
      rw [map_smul, map_sub, (pullback Q).symm_apply_apply, reflectedSemigroup_apply]

theorem forcedComplexEvolution_reflected {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    pullback Q (forcedComplexEvolution (reflectedEnvironmentLaw Q) i (-ζ) t
      ((pullback Q).symm f)) = forcedComplexEvolution Q i ζ t f := by
  have he := (isSemigroup_reflected Q
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ)).eq_forcedComplexEvolution
  rw [← he, reflectedSemigroup_apply, (pullback Q).apply_symm_apply,
    (pullback Q).apply_symm_apply]

theorem covariance_reflected {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, f ω * S t g ω ∂reducedLaw Q) =
      ∫ ω, (pullback Q).symm f ω *
        reflectedSemigroup Q S t ((pullback Q).symm g) ω
          ∂reducedLaw (reflectedEnvironmentLaw Q) := by
  simpa only [reflectedSemigroup_apply, (pullback Q).apply_symm_apply] using
    integral_mul_pullback Q ((pullback Q).symm f)
      (reflectedSemigroup Q S t ((pullback Q).symm g))

/-- The full graph equivalence, in the original-to-reflected direction. -/
theorem generatorPair_reflection_iff {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)} :
    IsComplexGeneratorPair Q i ζ f g ↔
      IsComplexGeneratorPair (reflectedEnvironmentLaw Q) i (-ζ)
        ((pullback Q).symm f) ((pullback Q).symm g) := by
  constructor
  · exact generatorPair_pullback_symm Q
  · intro h
    simpa only [neg_neg, (pullback Q).apply_symm_apply] using
      generatorPair_pullback Q h

/-- Canonical evolution intertwines with the actual reflected-law isometry. -/
theorem forcedComplexEvolution_reflection {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (pullback Q).symm (forcedComplexEvolution Q i ζ t f) =
      forcedComplexEvolution (reflectedEnvironmentLaw Q) i (-ζ) t ((pullback Q).symm f) := by
  apply (pullback Q).injective
  rw [(pullback Q).apply_symm_apply, forcedComplexEvolution_reflected]

/-- Any supplied evolution conjugates to the canonical evolution of the reflected law. -/
theorem reflectedSemigroup_eq_forcedComplexEvolution {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {i : Fin d} {ζ : ℂ}
    {S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hS : IsComplexEnvironmentSemigroup Q i ζ S) :
    reflectedSemigroup Q S = forcedComplexEvolution (reflectedEnvironmentLaw Q) i (-ζ) :=
  (isSemigroup_reflected Q hS).eq_forcedComplexEvolution

/-- The supplied semigroup's covariance is the actual reflected canonical covariance. -/
theorem covariance_reflection_of_isSemigroup {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {i : Fin d} {ζ : ℂ}
    {S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hS : IsComplexEnvironmentSemigroup Q i ζ S)
    (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, f ω * S t g ω ∂reducedLaw Q) =
      ∫ ω, (pullback Q).symm f ω *
        forcedComplexEvolution (reflectedEnvironmentLaw Q) i (-ζ) t
          ((pullback Q).symm g) ω ∂reducedLaw (reflectedEnvironmentLaw Q) := by
  rw [covariance_reflected Q S t f g, reflectedSemigroup_eq_forcedComplexEvolution Q hS]

/-- At negative real force the reflected covariance has the positive force `|lam|`. -/
theorem covariance_negative_force {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {i : Fin d} {lam : ℝ} (hlam : lam < 0)
    {S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hS : IsComplexEnvironmentSemigroup Q i (lam : ℂ) S)
    (t : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, f ω * S t g ω ∂reducedLaw Q) =
      ∫ ω, (pullback Q).symm f ω *
        forcedComplexEvolution (reflectedEnvironmentLaw Q) i ((|lam| : ℝ) : ℂ) t
          ((pullback Q).symm g) ω ∂reducedLaw (reflectedEnvironmentLaw Q) := by
  simpa only [abs_of_neg hlam, Complex.ofReal_neg] using
    covariance_reflection_of_isSemigroup Q hS t f g

/-- Uniform positive-force and signed-force estimates are equivalent with exactly
 the same constants. Reflection changes the actual joint law and preserves every
 observable side condition, so this needs no symmetry or coupling assumption. -/
theorem positive_covariance_bound_iff_signed {d : ℕ} {Λ r₀ : ℝ}
    (i : Fin d) (l p c C lam₀ : ℝ) :
    (∀ (Q : EnvironmentLaw d Λ r₀) (lam : ℝ), 0 < lam → lam ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / lam) F →
      IsRealLocalObservation Q (A / lam) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ↔
    (∀ (Q : EnvironmentLaw d Λ r₀) (lam : ℝ), 0 < |lam| → |lam| ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  constructor
  · intro hpositive Q lam h0 h1 S hS A hA F G hF hG hFp hGp hmean t
    by_cases hpos : 0 < lam
    · simp only [abs_of_pos hpos] at h1 hF hG
      exact hpositive Q lam hpos h1 S hS A hA F G hF hG hFp hGp hmean t
    · have hneg : lam < 0 := lt_of_le_of_ne (le_of_not_gt hpos) (abs_pos.mp h0)
      have hSr : IsComplexEnvironmentSemigroup (reflectedEnvironmentLaw Q) i
          ((|lam| : ℝ) : ℂ) (reflectedSemigroup Q S) := by
        simpa only [abs_of_neg hneg, Complex.ofReal_neg] using isSemigroup_reflected Q hS
      have hmeanr : (∫ ω, (pullback Q).symm F ω
          ∂reducedLaw (reflectedEnvironmentLaw Q)) = 0 :=
        (integral_pullback_symm Q F).trans hmean
      have hb := hpositive (reflectedEnvironmentLaw Q) |lam| h0 h1
        (reflectedSemigroup Q S) hSr A hA ((pullback Q).symm F) ((pullback Q).symm G)
        (realLocal_pullback_symm Q hF) (realLocal_pullback_symm Q hG)
        (memLp_pullback_symm Q hFp) (memLp_pullback_symm Q hGp) hmeanr t
      rw [← covariance_reflected Q S t F G] at hb
      simpa only [eLpNorm_pullback_symm, sq_abs] using hb
  · intro hsigned Q lam h0 h1 S hS A hA F G hF hG hFp hGp hmean t
    exact hsigned Q lam (by simpa only [abs_of_pos h0] using h0)
      (by simpa only [abs_of_pos h0] using h1) S hS A hA F G
      (by simpa only [abs_of_pos h0] using hF)
      (by simpa only [abs_of_pos h0] using hG) hFp hGp hmean t

#print axioms reduce_reflect
#print axioms reducedLaw_reflected
#print axioms measurePreserving_reflect
#print axioms measurePreserving_reflect_reverse
#print axioms pullback
#print axioms pullback_ae
#print axioms pullback_symm_ae
#print axioms eLpNorm_pullback
#print axioms integral_pullback
#print axioms integral_mul_pullback
#print axioms localSigma_reflect_ball
#print axioms realLocal_pullback
#print axioms realLocal_pullback_symm
#print axioms pullback_translation
#print axioms pullback_symm_translation
#print axioms horizontalDerivative_of_conjugacy
#print axioms horizontalDerivative_pullback
#print axioms horizontalDerivative_pullback_symm
#print axioms translation_conjugacy_symm
#print axioms generatorPair_of_reflection
#print axioms generatorPair_pullback
#print axioms generatorPair_pullback_symm
#print axioms generatorPair_pullback_iff
#print axioms eLpNorm_pullback_symm
#print axioms memLp_pullback_symm
#print axioms integral_pullback_symm
#print axioms reflectedSemigroup
#print axioms reflectedSemigroup_apply
#print axioms isSemigroup_reflected
#print axioms forcedComplexEvolution_reflected
#print axioms covariance_reflected
#print axioms generatorPair_reflection_iff
#print axioms forcedComplexEvolution_reflection
#print axioms reflectedSemigroup_eq_forcedComplexEvolution
#print axioms covariance_reflection_of_isSemigroup
#print axioms covariance_negative_force

#print axioms positive_covariance_bound_iff_signed

#lint

end EinsteinFull.SbxS10KmReflection
