import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinFull.Calculus.ComplexHorizontalClosedGraphSupport
import EinsteinFull.Calculus.ComplexHorizontalDensitySupport
import EinsteinRelation.Calculus.EnvironmentWeakCalculusCore

/-!
# Horizontal graph regularization by the actual Gaussian evolution

These results concern the literal anisotropic stationary Gaussian operator.
They prove preservation and approximation of existing horizontal derivative
jets, and integration by parts against the full horizontal H1 test domain.
Creation of horizontal derivatives from arbitrary L2 data, and identification
with the strong time generator, are separate remaining obligations.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

attribute [local instance] reducedLaw_probability

/-- The actual stationary homogeneous integral commutes with spatial translations. -/
theorem homogeneousAverage_complexTranslation (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (t : ℝ) (ht : 0 < t) (ζ : ℂ) (x : Vec d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i t ht ζ
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (homogeneousAverage Q i t ht ζ f) := by
  rw [complexTranslation_homogeneousAverage]
  unfold homogeneousAverage
  apply integral_congr_ae
  refine Eventually.of_forall fun y => ?_
  dsimp only
  rw [← complexTranslation_add, add_comm y x]


/-- The actual Gaussian operator preserves each strong horizontal derivative. -/
theorem HasComplexHorizontalDerivative.homogeneousAverage
    {Q : EnvironmentLaw d Λ r} {j : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (EinsteinFull.homogeneousAverage Q i s hs ζ f) (EinsteinFull.homogeneousAverage Q i s hs ζ g) := by
  let H := homogeneousAverageCLM Q i s hs ζ
  have h := (H.continuous.tendsto g).comp hf
  change Tendsto (fun t : ℝ => H ((t : ℂ)⁻¹ •
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
      (t • unitVector j) f - f))) (𝓝[≠] (0 : ℝ)) (𝓝 (H g)) at h
  unfold HasComplexHorizontalDerivative
  dsimp only [H] at h
  simpa only [map_smul, map_sub, homogeneousAverageCLM_apply,
    homogeneousAverage_complexTranslation] using h

/-- The full H1 gradient is transported coordinatewise by actual convolution. -/
theorem HasComplexHorizontalGradient.homogeneousAverage
    {Q : EnvironmentLaw d Λ r} {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (EinsteinFull.homogeneousAverage Q i s hs ζ f) (fun j => EinsteinFull.homogeneousAverage Q i s hs ζ (G j)) :=
  fun j => (hf j).homogeneousAverage i s hs ζ

/-- Horizontal derivative commutation includes zero evolution time. -/
theorem HasComplexHorizontalDerivative.homogeneousGaussianEvolution
    {Q : EnvironmentLaw d Λ r} {j : Fin d} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (homogeneousGaussianEvolution Q i ζ t f) (homogeneousGaussianEvolution Q i ζ t g) := by
  by_cases ht : 0 < (t : ℝ)
  · simp only [homogeneousGaussianEvolution_pos Q i ζ t ht]
    exact hf.homogeneousAverage i t ht ζ
  · have ht0 : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.coe_nonneg)
    subst t
    simpa only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply] using hf

/-- The actual all-time evolution preserves the entire horizontal H1 graph. -/
theorem HasComplexHorizontalGradient.homogeneousGaussianEvolution
    {Q : EnvironmentLaw d Λ r} {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (i : Fin d) (ζ : ℂ) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (homogeneousGaussianEvolution Q i ζ t f)
      (fun j => homogeneousGaussianEvolution Q i ζ t (G j)) :=
  fun j => (hf j).homogeneousGaussianEvolution i ζ t

/-- Actual Gaussian regularizations tend to the datum in the full H1 graph
whenever the datum has a strong horizontal gradient. -/
theorem tendsto_homogeneousGaussianEvolution_horizontalGraph
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => (homogeneousGaussianEvolution Q i ζ t f,
      fun j => homogeneousGaussianEvolution Q i ζ t (G j))) (𝓝 0) (𝓝 (f, G)) := by
  have ht (u : Lp ℂ 2 (reducedLaw Q)) :
      Tendsto (fun t : ℝ≥0 => homogeneousGaussianEvolution Q i ζ t u) (𝓝 0) (𝓝 u) := by
    simpa only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply] using
      (continuous_homogeneousGaussianEvolution Q i ζ u).tendsto 0
  exact (ht f).prodMk_nhds (tendsto_pi_nhds.mpr fun j => ht (G j))

/-- A coherent actual strong horizontal derivative jet of all finite orders.
The head coordinate is differentiated last. -/
def HasComplexHorizontalJet (Q : EnvironmentLaw d Λ r)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∀ (coords : List (Fin d)) (j : Fin d),
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (J coords) (J (j :: coords))

/-- The actual smooth horizontal domain, defined by strong translation
 derivatives of every order, with no equation or estimate in its definition. -/
def IsComplexHorizontallySmooth (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ J : List (Fin d) → Lp ℂ 2 (reducedLaw Q), J [] = f ∧ HasComplexHorizontalJet Q J

/-- Every order of a coherent strong horizontal jet is uniquely determined
by its value at the empty coordinate list. -/
theorem HasComplexHorizontalJet.unique {Q : EnvironmentLaw d Λ r}
    {J K : List (Fin d) → Lp ℂ 2 (reducedLaw Q)}
    (hJ : HasComplexHorizontalJet Q J) (hK : HasComplexHorizontalJet Q K)
    (h0 : J [] = K []) : J = K := by
  funext coords
  induction coords with
  | nil => exact h0
  | cons j coords ih =>
    have hd := hJ coords j
    rw [ih] at hd
    exact hd.unique (hK coords j)

/-- Actual Gaussian convolution transports every order of a horizontal jet. -/
theorem HasComplexHorizontalJet.homogeneousAverage
    {Q : EnvironmentLaw d Λ r} {J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)}
    (hJ : HasComplexHorizontalJet Q J) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    HasComplexHorizontalJet Q (fun coords => EinsteinFull.homogeneousAverage Q i s hs ζ (J coords)) :=
  fun coords j => (hJ coords j).homogeneousAverage i s hs ζ

/-- The actual Gaussian regularization preserves the smooth horizontal domain. -/
theorem IsComplexHorizontallySmooth.homogeneousAverage
    {Q : EnvironmentLaw d Λ r} {f : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexHorizontallySmooth Q f) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    IsComplexHorizontallySmooth Q (EinsteinFull.homogeneousAverage Q i s hs ζ f) := by
  obtain ⟨J, hJ0, hJ⟩ := hf
  exact ⟨fun coords => EinsteinFull.homogeneousAverage Q i s hs ζ (J coords),
    congrArg (EinsteinFull.homogeneousAverage Q i s hs ζ) hJ0, hJ.homogeneousAverage i s hs ζ⟩

private theorem smooth_complexified_core (Q : EnvironmentLaw d Λ r)
    {F H : FieldPair d → ℝ} (hF : IsHorizontalTest F) (hH : IsHorizontalTest H) :
    IsComplexHorizontallySmooth Q
      (Complex.ofRealCLM.compLpL 2 (reducedLaw Q) ((hF.memLp (reducedLaw Q) 2).toLp F) +
        Complex.I • Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
          ((hH.memLp (reducedLaw Q) 2).toLp H)) := by
  letI := reducedLaw_probability Q
  let C := Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
  let JF (coords : List (Fin d)) :=
    ((hF.iterated coords).memLp (reducedLaw Q) 2).toLp (iteratedHorizontalDerivative coords F)
  let JH (coords : List (Fin d)) :=
    ((hH.iterated coords).memLp (reducedLaw Q) 2).toLp (iteratedHorizontalDerivative coords H)
  refine ⟨fun coords => C (JF coords) + Complex.I • C (JH coords), rfl, ?_⟩
  intro coords j
  have hdf := (hF.iterated coords).hasHorizontalLpDerivative_toLp (reducedLaw Q)
    (reducedLaw_stationary Q) j
  have hdh := (hH.iterated coords).hasHorizontalLpDerivative_toLp (reducedLaw Q)
    (reducedLaw_stationary Q) j
  exact (hasComplexHorizontalDerivative_ofReal hdf).add
    ((hasComplexHorizontalDerivative_ofReal hdh).smul Complex.I)

private theorem complex_reconstruction (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (Complex.reCLM.compLpL 2 (reducedLaw Q) f) +
      Complex.I • Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
        (Complex.imCLM.compLpL 2 (reducedLaw Q) f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (Complex.reCLM.compLpL 2 (reducedLaw Q) f))
      (Complex.I • Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
        (Complex.imCLM.compLpL 2 (reducedLaw Q) f)),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
      (Complex.imCLM.compLpL 2 (reducedLaw Q) f)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL 2 (reducedLaw Q) f),
    Complex.ofRealCLM.coeFn_compLpL (Complex.imCLM.compLpL 2 (reducedLaw Q) f),
    Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f]
    with ω ha hb hc hd he hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb
  rw [ha, hb, hc, hd, he, hh]
  simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    mul_comm Complex.I] using Complex.re_add_im (f ω)

/-- Smoothness of every order is proved for a dense actual horizontal domain;
no density assumption is used. -/
theorem dense_complexHorizontallySmooth (Q : EnvironmentLaw d Λ r) :
    Dense {f : Lp ℂ 2 (reducedLaw Q) | IsComplexHorizontallySmooth Q f} := by
  letI := reducedLaw_probability Q
  intro f
  let C := Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
  obtain ⟨F, hF, hFm, htF⟩ := Correctors.exists_horizontalCore_Lp_approximation
    (reducedLaw Q) (reducedLaw_stationary Q) (Complex.reCLM.compLpL 2 (reducedLaw Q) f)
  obtain ⟨H, hH, hHm, htH⟩ := Correctors.exists_horizontalCore_Lp_approximation
    (reducedLaw Q) (reducedLaw_stationary Q) (Complex.imCLM.compLpL 2 (reducedLaw Q) f)
  have ht := ((C.continuous.tendsto _).comp htF).add
    (((C.continuous.tendsto _).comp htH).const_smul Complex.I)
  rw [complex_reconstruction] at ht
  exact mem_closure_of_tendsto ht (Eventually.of_forall fun n =>
    smooth_complexified_core Q (hF n) (hH n))

/-- Positive-time, actual Gaussian regularizations of smooth horizontal data
form a dense subset of L2. This does not yet assert graph density for the time generator. -/
theorem dense_gaussianRegularized_horizontalSmooth (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) :
    Dense {u : Lp ℂ 2 (reducedLaw Q) | ∃ (s : ℝ) (hs : 0 < s)
      (f : Lp ℂ 2 (reducedLaw Q)), IsComplexHorizontallySmooth Q f ∧
        u = EinsteinFull.homogeneousAverage Q i s hs ζ f} := by
  apply Dense.of_closure
  apply (dense_complexHorizontallySmooth Q).mono
  intro f hf
  let times : ℕ → ℝ≥0 := fun n => 1 / ((n : ℝ≥0) + 1)
  have ht : Tendsto times atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := ((continuous_homogeneousGaussianEvolution Q i ζ f).tendsto 0).comp ht
  simp only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply] at hlim
  apply mem_closure_of_tendsto hlim
  refine Eventually.of_forall fun n => ?_
  have hp : 0 < (times n : ℝ) := by dsimp only [times]; positivity
  exact ⟨times n, hp, f, hf, homogeneousGaussianEvolution_pos Q i ζ (times n) hp f⟩

/-- The anisotropic differential expression on a supplied actual horizontal
second-derivative jet. No generator-domain assertion is part of this definition. -/
def homogeneousHorizontalAction (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (H : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  (1 / 2 : ℂ) • ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) • H j k +
    ζ • ∑ j, (homogenizedCoefficient Q j i : ℂ) • G j

/-- The actual Gaussian operator commutes with the full signed anisotropic
horizontal differential expression on an existing second-derivative jet. -/
theorem homogeneousAverage_horizontalAction (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ η : ℂ)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (H : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) :
    EinsteinFull.homogeneousAverage Q i s hs ζ (homogeneousHorizontalAction Q i η G H) =
      homogeneousHorizontalAction Q i η
        (fun j => EinsteinFull.homogeneousAverage Q i s hs ζ (G j))
        (fun j k => EinsteinFull.homogeneousAverage Q i s hs ζ (H j k)) := by
  change homogeneousAverageCLM Q i s hs ζ _ = _
  simp only [homogeneousHorizontalAction, map_add, map_smul, map_sum,
    homogeneousAverageCLM_apply]

private def horizontalPair (Q : EnvironmentLaw d Λ r) (v : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 v

private theorem horizontalPair_apply (Q : EnvironmentLaw d Λ r)
    (v u : Lp ℂ 2 (reducedLaw Q)) :
    horizontalPair Q v u = ∫ ω, v ω * u ω ∂reducedLaw Q :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

/-- Bilinear weak form of the literal homogeneous differential expression,
for every test in the full horizontal H1 domain. The drift is +zeta*A*e_i;
there is no complex conjugation of the signed force. -/
theorem homogeneousHorizontalAction_weak (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (H : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hH : ∀ j k, HasComplexHorizontalDerivative (reducedLaw Q)
      (reducedLaw_stationary Q) j (G k) (H j k))
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, v ω * homogeneousHorizontalAction Q i ζ G H ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, V j ω * G k ω ∂reducedLaw Q) +
      ζ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
        (∫ ω, v ω * G j ω ∂reducedLaw Q) := by
  rw [← horizontalPair_apply]
  simp only [homogeneousHorizontalAction, map_add, map_smul, map_sum,
    horizontalPair_apply, smul_eq_mul]
  have hb (j k : Fin d) : (∫ ω, v ω * H j k ω ∂reducedLaw Q) =
      -(∫ ω, V j ω * G k ω ∂reducedLaw Q) := by
    have he := (complexHorizontalDerivatives_integration_by_parts (hv j) (hH j k)).2.2
    simpa only [neg_neg] using congrArg Neg.neg he.symm
  simp_rw [hb, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The full H1 weak identity for the Gaussian regularization of an actual
smooth horizontal jet. Every spatial derivative is supplied by its proved
strong translation limit and commuted through the literal Gaussian integral. -/
theorem homogeneousAverage_horizontalJet_weak
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hJ : HasComplexHorizontalJet Q J)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, v ω * EinsteinFull.homogeneousAverage Q i s hs ζ
      (homogeneousHorizontalAction Q i ζ (fun k => J [k]) (fun j k => J [j, k])) ω
      ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, V j ω * EinsteinFull.homogeneousAverage Q i s hs ζ (J [k]) ω ∂reducedLaw Q) +
      ζ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
        (∫ ω, v ω * EinsteinFull.homogeneousAverage Q i s hs ζ (J [j]) ω ∂reducedLaw Q) := by
  rw [homogeneousAverage_horizontalAction]
  exact homogeneousHorizontalAction_weak Q i ζ _ _
    (fun j k => (hJ [k] j).homogeneousAverage i s hs ζ) v V hv

end EinsteinFull
