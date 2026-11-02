import EinsteinFull.Calculus.C13CanonicalSpatialPotential
import EinsteinFull.Calculus.C5CorrectorUniformSublinearity
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import EinsteinRelation.Correctors.NormedIntegralMoment
import EinsteinRelation.Correctors.EuclideanCoordinateMomentBound
import EinsteinRelation.TimeChange.EuclideanTransport

/-! Finite-coordinate assembly of the canonical, uniformly sublinear corrector. -/

open EinsteinRelation MeasureTheory Filter
open scoped NNReal Topology BigOperators

noncomputable section

namespace EinsteinFull

open EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3

/-- Coordinatewise uniform sublinearity gives uniform Euclidean sublinearity
and a global bound with an arbitrarily small linear coefficient. -/
theorem vector_sublinearity_of_component_sublinearity {d : ℕ}
    (χ : Vec d → Vec d)
    (hsub : ∀ i : Fin d, ∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → |χ x i|/(t+1) ≤ ε) :
    (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ x, euclideanNorm (χ x) ≤ C + ε*euclideanNorm x) := by
  constructor
  · intro R ε hR hε
    have hD : 0 < (d : ℝ) + 1 := by positivity
    have hδ : 0 < ε / ((d : ℝ) + 1) := div_pos hε hD
    filter_upwards [eventually_ge_atTop (0 : ℝ),
      eventually_all.2 (fun i => hsub i R (ε / ((d : ℝ) + 1)) hR hδ)] with t ht hs
    intro x hx
    have ht1 : 0 < t+1 := by linarith only [ht]
    have hpi : ‖χ x‖ ≤ ε / ((d : ℝ) + 1) * (t+1) := by
      apply (pi_norm_le_iff_of_nonneg (mul_nonneg hδ.le ht1.le)).2
      intro i
      rw [Real.norm_eq_abs]
      exact (div_le_iff₀ ht1).mp (hs i x hx)
    apply (div_le_iff₀ ht1).mpr
    calc
      euclideanNorm (χ x) ≤ ((d : ℝ) + 1) * ‖χ x‖ :=
        euclideanNorm_le_dimension_mul_norm (χ x)
      _ ≤ ((d : ℝ) + 1) * (ε / ((d : ℝ) + 1) * (t+1)) :=
        mul_le_mul_of_nonneg_left hpi hD.le
      _ = ε * (t+1) := by rw [← mul_assoc, mul_div_cancel₀ _ hD.ne']
  · apply euclidean_growth_of_component_sublinearity χ
    intro i ε hε
    have h := tendsto_natCast_atTop_atTop.eventually (hsub i 1 ε zero_lt_one hε)
    simpa only [mul_one] using h

/-- The scalar canonical potentials can be chosen on one common full-measure
set to form a continuous, origin-zero, uniformly sublinear vector corrector. -/
theorem exists_vector_uniformly_sublinear_canonical_corrector
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ G : Fin d → Coefficient d (AKMUpperEllipticity L) → Vec d → EuclideanSpace ℝ (Fin d),
      (∀ i, Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => G i p.1 p.2)) ∧
      (∀ᵐ a ∂actualCoefficientLaw Q, ∃ χ : Vec d → Vec d,
        Continuous χ ∧ χ 0 = 0 ∧
        (∀ i : Fin d, HasWeakGradient Set.univ (fun x => χ x i) (fun x => (G i a x).ofLp)) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R → MemLp (fun x => χ x i) 2 (volume.restrict (ball 0 R))) ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x, euclideanNorm (χ x) ≤ C + ε*euclideanNorm x)) ∧
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ i : Fin d, ∀ᵐ x ∂(volume : Measure (Vec d)),
        G i (project (r₀ := r) Q.ellipticity_parameter ω) x =
          (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))) := by
  classical
  choose G hG hpot hid using exists_uniformly_sublinear_canonical_corrector Q
  refine ⟨G, hG, ?_, eventually_all.2 hid⟩
  filter_upwards [eventually_all.2 hpot] with a ha
  choose χ hc hz hw hm hs hsub using ha
  let Ψ : Vec d → Vec d := fun x i => χ i x
  have hvec := vector_sublinearity_of_component_sublinearity Ψ
    (fun i R ε hR hε => hsub i R hR ε hε)
  refine ⟨Ψ, continuous_pi hc, ?_, hw, hm, hvec⟩
  funext i
  exact hz i

/-- The same vector potential pulls back to the physical reference law, with
each weak gradient identified with the translated canonical corrector gradient. -/
theorem ae_physical_vector_uniformly_sublinear_canonical_corrector
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ χ : Vec d → Vec d,
      Continuous χ ∧ χ 0 = 0 ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε) ∧
      (∀ i : Fin d, HasWeakGradient Set.univ (fun x => χ x i) (fun x =>
        ((canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))).ofLp)) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        euclideanNorm (χ x) ≤ C + ε*euclideanNorm x) := by
  obtain ⟨G, _, hpot, hid⟩ := exists_vector_uniformly_sublinear_canonical_corrector Q
  have hπ := measurable_project (d := d) (r₀ := r) Q.ellipticity_parameter
  have hphysical := ae_of_ae_map hπ.aemeasurable hpot
  filter_upwards [hphysical, hid] with ω hω hidω
  obtain ⟨χ, hc, hz, hw, _, hs, hg⟩ := hω
  refine ⟨χ, hc, hz, hs, ?_, hg⟩
  intro i j
  apply (hw i j).congr_ae (ae_eq_refl _)
  simpa only [Measure.restrict_univ, Filter.EventuallyEq] using
    (hidω i).mono (fun x hx =>
      congrArg (fun z : EuclideanSpace ℝ (Fin d) => z.ofLp j) hx)

/-- The same scalar harmonic potentials assemble on a common physical
full-measure event into a uniformly sublinear vector harmonic coordinate. -/
theorem ae_physical_vector_uniform_canonical_harmonic_coordinate
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∃ χ : Vec d → Vec d,
      Continuous χ ∧ χ 0 = 0 ∧
      (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
        ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ x)/(t+1) ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
        euclideanNorm (χ x) ≤ C + ε*euclideanNorm x) ∧
      (∀ (i : Fin d) (R : ℝ), 0 < R →
        WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ x i)
          (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))).ofLp)) := by
  classical
  filter_upwards [eventually_all.2
    (fun i => ae_physical_uniform_canonical_harmonic_coordinate Q i)] with ω hω
  choose χ hc hz hw hm hs hsol using hω
  let Ψ : Vec d → Vec d := fun x i => χ i x
  have hvec := vector_sublinearity_of_component_sublinearity Ψ hs
  refine ⟨Ψ, continuous_pi hc, ?_, hvec.1, hvec.2, hsol⟩
  funext i
  exact hz i

/-- Radial integration of a spatially smoothed gradient. The formula is defined
also for fields for which the integrals are not integrable. -/
def mollifiedRadialPotential {α : Type*} {d : ℕ}
    (ψ : Vec d → ℝ) (G : α → Vec d → Vec d) (a : α) (x : Vec d) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1,
    ∑ j : Fin d, x j * ∫ y : Vec d, ψ y * G a (t • x - y) j

/-- Smoothing and radial integration preserve joint measurability, without any
integrability assumption on exceptional environments. -/
theorem measurable_mollifiedRadialPotential {α : Type*} [MeasurableSpace α]
    {d : ℕ} {ψ : Vec d → ℝ} (hψ : Measurable ψ)
    {G : α → Vec d → Vec d}
    (hG : Measurable (fun z : α × Vec d => G z.1 z.2)) :
    Measurable (fun z : α × Vec d => mollifiedRadialPotential ψ G z.1 z.2) := by
  have hcoord (j : Fin d) : Measurable
      (fun z : ((α × Vec d) × ℝ) × Vec d =>
        ψ z.2 * G z.1.1.1 (z.1.2 • z.1.1.2 - z.2) j) := by
    apply (hψ.comp measurable_snd).mul
    exact ((measurable_pi_apply j).comp hG).comp
      (((measurable_fst.comp measurable_fst).comp measurable_fst).prodMk
        (((measurable_snd.comp measurable_fst).smul
          ((measurable_snd.comp measurable_fst).comp measurable_fst)).sub measurable_snd))
  have hinner (j : Fin d) : Measurable
      (fun z : (α × Vec d) × ℝ =>
        ∫ y : Vec d, ψ y * G z.1.1 (z.2 • z.1.2 - y) j) :=
    (hcoord j).stronglyMeasurable.integral_prod_right'.measurable
  have hsum : Measurable (fun z : (α × Vec d) × ℝ =>
      ∑ j : Fin d, z.1.2 j * ∫ y : Vec d, ψ y * G z.1.1 (z.2 • z.1.2 - y) j) := by
    apply Finset.measurable_sum
    intro j _
    exact (((measurable_pi_apply j).comp measurable_snd).comp measurable_fst).mul (hinner j)
  exact hsum.stronglyMeasurable.integral_prod_right'.measurable

/-- A countable family of smooth averaging kernels with support shrinking to
the origin, used to reconstruct the normalized spatial potential. -/
private def correctorReconstructionBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [h]

/-- A total, measurable candidate for the normalized scalar potential of a
gradient. Its value on fields without a convergent reconstruction is supplied
by `limUnder`; no choice of pathwise potentials occurs in this definition. -/
def radialGradientReconstruction {α : Type*} {d : ℕ}
    (G : α → Vec d → Vec d) (a : α) (x : Vec d) : ℝ :=
  limUnder atTop (fun n : ℕ => mollifiedRadialPotential
    ((correctorReconstructionBump d n).normed volume) G a x)

/-- The reconstruction candidate is jointly measurable in environment and
space whenever the actual gradient is jointly measurable. -/
theorem measurable_radialGradientReconstruction {α : Type*} [MeasurableSpace α]
    {d : ℕ} {G : α → Vec d → Vec d}
    (hG : Measurable (fun z : α × Vec d => G z.1 z.2)) :
    Measurable (fun z : α × Vec d => radialGradientReconstruction G z.1 z.2) := by
  have hm (n : ℕ) : Measurable (fun z : α × Vec d =>
      mollifiedRadialPotential ((correctorReconstructionBump d n).normed volume)
        G z.1 z.2) :=
    measurable_mollifiedRadialPotential
      (correctorReconstructionBump d n).continuous_normed.measurable hG
  exact (StronglyMeasurable.limUnder (fun n => (hm n).stronglyMeasurable)).measurable

private theorem reconstruction_coordinateDerivative_reflect {d : ℕ}
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (x y : Vec d) (j : Fin d) :
    coordinateDerivative j (fun z : Vec d => ψ (x - z)) y =
      -coordinateDerivative j ψ (x - y) := by
  have houter := (hψ.differentiable one_ne_zero (x - y)).hasFDerivAt
  have hinner : HasFDerivAt (fun z : Vec d => x - z)
      (-ContinuousLinearMap.id ℝ (Vec d)) y := (hasFDerivAt_id y).const_sub x
  have hcomp : HasFDerivAt (fun z : Vec d => ψ (x - z))
      ((fderiv ℝ ψ (x - y)).comp (-ContinuousLinearMap.id ℝ (Vec d))) y :=
    HasFDerivAt.comp y houter hinner
  unfold coordinateDerivative
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

private theorem reconstruction_integral_weakPartial {d : ℕ}
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hDu : HasWeakGradient Set.univ u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (x : Vec d) (j : Fin d) :
    (∫ y : Vec d, coordinateDerivative j ψ y * u (x - y)) =
      ∫ y : Vec d, ψ y * G (x - y) j := by
  have htest : IsSpatialTest Set.univ (fun z : Vec d => ψ (x - z)) :=
    ⟨hψ.comp (contDiff_const.sub contDiff_id),
      hψc.comp_homeomorph (Homeomorph.subLeft x), Set.subset_univ _⟩
  have heq := (hDu j).2.2 _ htest
  simp only [Measure.restrict_univ,
    reconstruction_coordinateDerivative_reflect (hψ.of_le (by simp)),
    mul_neg, integral_neg, neg_inj] at heq
  have hleft := integral_sub_left_eq_self
    (fun y : Vec d => coordinateDerivative j ψ y * u (x - y)) volume x
  have hright := integral_sub_left_eq_self
    (fun y : Vec d => ψ y * G (x - y) j) volume x
  simp only [sub_sub_cancel] at hleft hright
  rw [← hleft, ← hright]
  simpa only [mul_comm] using heq

private theorem reconstruction_fderiv_convolution {d : ℕ}
    {u : Vec d → ℝ} (hu : Continuous u) {G : Vec d → Vec d}
    (hDu : HasWeakGradient Set.univ u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (x v : Vec d) :
    fderiv ℝ (MeasureTheory.convolution ψ u
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) x v =
      ∑ j : Fin d, v j * ∫ y : Vec d, ψ y * G (x - y) j := by
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  rw [(hψc.hasFDerivAt_convolution_left B hψ1 hu.locallyIntegrable x).fderiv]
  have hint : Integrable (fun y : Vec d =>
      B.precompL (Vec d) (fderiv ℝ ψ y) (u (x - y))) volume :=
    (hψc.fderiv ℝ).convolutionExists_left (B.precompL (Vec d))
      (hψ1.continuous_fderiv (by simp)) hu.locallyIntegrable x
  rw [MeasureTheory.convolution_def, ContinuousLinearMap.integral_apply hint v]
  change (∫ y : Vec d, fderiv ℝ ψ y v * u (x - y)) = _
  have hv : v = ∑ j : Fin d, v j • unitVector j := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, unitVector,
      Pi.single_apply]
    simp
  have hpoint (y : Vec d) : fderiv ℝ ψ y v * u (x - y) =
      ∑ j : Fin d, v j * (coordinateDerivative j ψ y * u (x - y)) := by
    conv_lhs => rw [hv]
    simp only [map_sum, map_smul, smul_eq_mul, Finset.sum_mul, coordinateDerivative]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hintj (j : Fin d) : Integrable
      (fun y : Vec d => coordinateDerivative j ψ y * u (x - y)) volume :=
    (hψc.fderiv_apply ℝ (unitVector j)).convolutionExists_left B
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      hu.locallyIntegrable x
  simp_rw [hpoint]
  rw [integral_finsetSum Finset.univ (fun j _ => (hintj j).const_mul (v j))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_const_mul, reconstruction_integral_weakPartial hDu hψ hψc]

/-- For a continuous weak potential, radial reconstruction of its smoothed
gradient is exactly its smoothed increment from the origin. -/
theorem mollifiedRadialPotential_eq_convolution_sub {α : Type*} {d : ℕ}
    {G : α → Vec d → Vec d} (a : α) {u : Vec d → ℝ} (hu : Continuous u)
    (hDu : HasWeakGradient Set.univ u (G a))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (x : Vec d) :
    mollifiedRadialPotential ψ G a x =
      MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
      MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 := by
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let F := MeasureTheory.convolution ψ u B volume
  have hFD (y : Vec d) : HasFDerivAt F (fderiv ℝ F y) y :=
    (hψc.hasFDerivAt_convolution_left B (hψ.of_le (by simp))
      hu.locallyIntegrable y).differentiableAt.hasFDerivAt
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => F (s • x))
      (∑ j : Fin d, x j * ∫ y : Vec d, ψ y * G a (t • x - y) j) t := by
    have h := (hFD (t • x)).comp_hasDerivAt t ((hasDerivAt_id t).smul_const x)
    simpa only [one_smul, F, B,
      reconstruction_fderiv_convolution hu hDu hψ hψc] using! h
  have hcont : Continuous (fun t : ℝ =>
      ∑ j : Fin d, x j * ∫ y : Vec d, ψ y * G a (t • x - y) j) := by
    apply continuous_finsetSum
    intro j _
    have hgj : LocallyIntegrable (fun y => G a y j) volume :=
      locallyIntegrableOn_univ.mp (hDu j).2.1
    exact continuous_const.mul
      ((hψc.continuous_convolution_left B hψ.continuous hgj).comp
        (continuous_id.smul continuous_const))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hcont.intervalIntegrable (0 : ℝ) 1)
  simpa only [intervalIntegral.integral_of_le zero_le_one, one_smul, zero_smul,
    mollifiedRadialPotential, F, B] using heq

/-- A mollified weak potential has increments given by the integral of its
mollified weak gradient along the segment joining the two points. -/
theorem mollified_potential_increment_eq_segment_integral {d : ℕ}
    {u : Vec d → ℝ} (hu : Continuous u) {G : Vec d → Vec d}
    (hDu : HasWeakGradient Set.univ u G)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (x y : Vec d) :
    MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
      MeasureTheory.convolution ψ u (ContinuousLinearMap.lsmul ℝ ℝ) volume y =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        ∑ j : Fin d, (x - y) j * ∫ z : Vec d, ψ z * G (y + t • (x - y) - z) j := by
  let B : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let F := MeasureTheory.convolution ψ u B volume
  have hFD (z : Vec d) : HasFDerivAt F (fderiv ℝ F z) z :=
    (hψc.hasFDerivAt_convolution_left B (hψ.of_le (by simp))
      hu.locallyIntegrable z).differentiableAt.hasFDerivAt
  have hderiv (t : ℝ) : HasDerivAt (fun s : ℝ => F (y + s • (x - y)))
      (∑ j : Fin d, (x - y) j * ∫ z : Vec d, ψ z * G (y + t • (x - y) - z) j) t := by
    have h := (hFD (y + t • (x - y))).comp_hasDerivAt t
      (((hasDerivAt_id t).smul_const (x - y)).const_add y)
    simpa only [one_smul, F, B, reconstruction_fderiv_convolution hu hDu hψ hψc] using! h
  have hcont : Continuous (fun t : ℝ =>
      ∑ j : Fin d, (x - y) j * ∫ z : Vec d, ψ z * G (y + t • (x - y) - z) j) := by
    apply continuous_finsetSum
    intro j _
    have hgj : LocallyIntegrable (fun z => G z j) volume :=
      locallyIntegrableOn_univ.mp (hDu j).2.1
    exact continuous_const.mul
      ((hψc.continuous_convolution_left B hψ.continuous hgj).comp
        (continuous_const.add (continuous_id.smul continuous_const)))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) (hcont.intervalIntegrable (0 : ℝ) 1)
  have hp : y + (x - y) = x := by abel
  simpa only [intervalIntegral.integral_of_le zero_le_one, one_smul, zero_smul,
    add_zero, hp, F, B] using heq.symm

/-- The measurable reconstruction agrees everywhere with any continuous
origin-zero weak potential of the supplied gradient. -/
theorem radialGradientReconstruction_eq {α : Type*} {d : ℕ}
    {G : α → Vec d → Vec d} (a : α) {u : Vec d → ℝ} (hu : Continuous u)
    (hu0 : u 0 = 0) (hDu : HasWeakGradient Set.univ u (G a)) (x : Vec d) :
    radialGradientReconstruction G a x = u x := by
  have hr : Tendsto (fun n : ℕ => (correctorReconstructionBump d n).rOut)
      atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hx := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Vec d))) hr hu x
  have hzero := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (Vec d))) hr hu 0
  have heq (n : ℕ) := mollifiedRadialPotential_eq_convolution_sub a hu hDu
    ((correctorReconstructionBump d n).contDiff_normed
      (μ := (volume : Measure (Vec d))))
    ((correctorReconstructionBump d n).hasCompactSupport_normed
      (μ := (volume : Measure (Vec d)))) x
  have hlim : Tendsto (fun n : ℕ => mollifiedRadialPotential
      ((correctorReconstructionBump d n).normed volume) G a x) atTop (𝓝 (u x)) := by
    simpa only [heq, hu0, sub_zero] using hx.sub hzero
  exact hlim.limUnder_eq

/-- The canonical physical vector corrector has a jointly measurable choice
with the same continuous normalized weak gradient and uniform sublinearity. -/
theorem exists_jointly_measurable_physical_vector_corrector
 {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
 ∃ χ : FieldPair d → Vec d → Vec d,
 Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
 (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
   Continuous (χ ω) ∧ χ ω 0 = 0 ∧
   (∀ i : Fin d, HasWeakGradient Set.univ (fun x => χ ω x i)
     (fun x => ((canonicalCorrectorGradient Q i :
       Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
         (translate x (reduce ω.1))).ofLp)) ∧
   (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
     ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε)) := by
  obtain ⟨G, hG, hpot, hid⟩ := exists_vector_uniformly_sublinear_canonical_corrector Q
  let H : Fin d → Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d :=
    fun i a x => (G i a x).ofLp
  have hH (i : Fin d) : Measurable
      (fun z : Coefficient d (AKMUpperEllipticity L) × Vec d => H i z.1 z.2) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp (hG i)
  let Ψ : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d :=
    fun a x i => radialGradientReconstruction (H i) a x
  have hΨ : Measurable
      (fun z : Coefficient d (AKMUpperEllipticity L) × Vec d => Ψ z.1 z.2) :=
    Measurable.of_eval (fun i => measurable_radialGradientReconstruction (hH i))
  let π : PhysicalField d L → Coefficient d (AKMUpperEllipticity L) :=
    project (r₀ := r) Q.ellipticity_parameter
  have hπ : Measurable π := measurable_project (d := d) (r₀ := r) Q.ellipticity_parameter
  have hpull : Measurable
      (fun z : PhysicalField d L × Vec d => Ψ (π z.1) z.2) :=
    hΨ.comp (f := Prod.map π (id : Vec d → Vec d))
      (hπ.prodMap (measurable_id : Measurable (id : Vec d → Vec d)))
  let f : PhysicalField d L × Vec d → FieldPair d × Vec d :=
    Prod.map Subtype.val id
  have hf : MeasurableEmbedding f :=
    (MeasurableEmbedding.subtype_coe
      (Sharpness.measurableSet_isRegular_fieldPair (d := d) L)).prodMap
        MeasurableEmbedding.id
  let κ : FieldPair d × Vec d → Vec d := Function.extend f
    (fun z => Ψ (π z.1) z.2) (fun _ => 0)
  have hκ : Measurable κ := hf.measurable_extend
    (g := fun z : PhysicalField d L × Vec d => Ψ (π z.1) z.2)
    (g' := fun _ : FieldPair d × Vec d => (0 : Vec d)) hpull measurable_const
  let χ : FieldPair d → Vec d → Vec d := fun ω x => κ (ω, x)
  have hext (ω : PhysicalField d L) (x : Vec d) :
      χ ω x = Ψ (π ω) x := hf.injective.extend_apply
        (fun z : PhysicalField d L × Vec d => Ψ (π z.1) z.2)
        (fun _ : FieldPair d × Vec d => (0 : Vec d)) (ω, x)
  refine ⟨χ, hκ, ?_⟩
  filter_upwards [ae_of_ae_map hπ.aemeasurable hpot, hid] with ω hω hidω
  obtain ⟨φ, hc, hz, hw, _, hs, _⟩ := hω
  have heq : χ ω = φ := by
    funext x i
    calc
      χ ω x i = radialGradientReconstruction (H i) (π ω) x :=
        congrFun (hext ω x) i
      _ = φ x i := radialGradientReconstruction_eq (G := H i) (π ω)
        ((continuous_apply i).comp hc) (congrFun hz i) (hw i) x
  subst φ
  refine ⟨hc, hz, ?_, hs⟩
  intro i j
  apply (hw i j).congr_ae (ae_eq_refl _)
  simpa only [Measure.restrict_univ, Filter.EventuallyEq] using
    (hidω i).mono (fun x hx =>
      congrArg (fun z : EuclideanSpace ℝ (Fin d) => z.ofLp j) hx)

/-- The jointly measurable normalized corrector has weak harmonic affine
coordinates on every ball and a global Euclidean sublinear growth bound. -/
theorem exists_jointly_measurable_physical_vector_harmonic_corrector
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) := by
  obtain ⟨χ, hmeas, hχ⟩ := exists_jointly_measurable_physical_vector_corrector Q
  refine ⟨χ, hmeas, ?_⟩
  filter_upwards [hχ, eventually_all.2
    (fun i => ae_physical_uniform_canonical_harmonic_coordinate Q i)] with ω hχω hω
  obtain ⟨hc, hz, hw, hsub⟩ := hχω
  choose φ hφc hφz hφw _ hφsub hφsol using hω
  have hsame (i : Fin d) : (fun x => χ ω x i) = φ i :=
    continuous_normalized_weak_potential_unique
      ((continuous_apply i).comp hc) (hφc i) (congrFun hz i) (hφz i) (hw i) (hφw i)
  have heq : χ ω = fun x i => φ i x := by
    funext x i
    exact congrFun (hsame i) x
  have hvec := vector_sublinearity_of_component_sublinearity (fun x i => φ i x) hφsub
  refine ⟨hc, hz, hsub, ?_, ?_⟩
  · rw [heq]
    exact hvec.2
  · rw [heq]
    exact hφsol


/-- A single measurable corrector carries both its canonical weak gradient and
its harmonic-coordinate and sublinear properties. -/
theorem exists_jointly_measurable_physical_harmonic_corrector_with_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ i : Fin d, HasWeakGradient Set.univ (fun x => χ ω x i)
          (fun x => ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))).ofLp)) ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) := by
  obtain ⟨χ, hmeas, hχ⟩ := exists_jointly_measurable_physical_vector_corrector Q
  refine ⟨χ, hmeas, ?_⟩
  filter_upwards [hχ, eventually_all.2
    (fun i => ae_physical_uniform_canonical_harmonic_coordinate Q i)] with ω hχω hω
  obtain ⟨hc, hz, hw, hsub⟩ := hχω
  choose φ hφc hφz hφw _ hφsub hφsol using hω
  have hsame (i : Fin d) : (fun x => χ ω x i) = φ i :=
    continuous_normalized_weak_potential_unique
      ((continuous_apply i).comp hc) (hφc i) (congrFun hz i) (hφz i) (hw i) (hφw i)
  have heq : χ ω = fun x i => φ i x := by
    funext x i
    exact congrFun (hsame i) x
  have hvec := vector_sublinearity_of_component_sublinearity (fun x i => φ i x) hφsub
  refine ⟨hc, hz, hw, hsub, ?_, ?_⟩
  · rw [heq]
    exact hvec.2
  · rw [heq]
    exact hφsol

/-- The translated canonical gradient has the same L² norm under the
physical reference law at every deterministic point. -/
@[nolint unusedArguments]
theorem physical_translated_canonical_gradient_memLp
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (i : Fin d) (x : Vec d) :
    MemLp (fun ω : PhysicalField d L =>
      (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))) 2
        (physicalReferenceLaw Q) ∧
    eLpNorm (fun ω : PhysicalField d L =>
      (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))) 2
        (physicalReferenceLaw Q) =
      eLpNorm (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) 2 (reducedEnvironmentLaw Q) := by
  let f := (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
    (reducedEnvironmentLaw Q))
  have ht := measurePreserving_translate (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) x
  have hp := measurePreserving_physicalReduction Q
  have hm : MemLp (fun ω => f (translate x ω)) 2 (reducedEnvironmentLaw Q) :=
    (Lp.memLp f).comp_measurePreserving ht
  refine ⟨hm.comp_measurePreserving hp, ?_⟩
  exact (eLpNorm_comp_measurePreserving hm.aestronglyMeasurable hp).trans
    (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) ht)

/-- The physical realization of each canonical gradient is jointly measurable
and has a finite L² bound uniform over deterministic spatial translations. -/
theorem physical_canonical_gradient_jointly_measurable_uniform_memLp
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (i : Fin d) :
    Measurable (fun p : Vec d × PhysicalField d L =>
      (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
        (reducedEnvironmentLaw Q)) (translate p.1 (reduce p.2.1))) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Vec d,
      MemLp (fun ω : PhysicalField d L =>
        (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))) 2
          (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω : PhysicalField d L =>
        (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) (translate x (reduce ω.1))) 2
          (physicalReferenceLaw Q) ≤ ENNReal.ofReal M := by
  let g := (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
    (reducedEnvironmentLaw Q))
  have hg : eLpNorm g 2 (reducedEnvironmentLaw Q) ≠ ⊤ := (Lp.memLp g).eLpNorm_ne_top
  constructor
  · exact (Lp.stronglyMeasurable g).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_fst.prodMk
          (Probability.measurable_reduce.comp (measurable_subtype_coe.comp measurable_snd))))
  · refine ⟨(eLpNorm g 2 (reducedEnvironmentLaw Q)).toReal, ENNReal.toReal_nonneg, ?_⟩
    intro x
    obtain ⟨hm, he⟩ := physical_translated_canonical_gradient_memLp Q i x
    refine ⟨hm, ?_⟩
    rw [he, ENNReal.ofReal_toReal hg]

/-- Averaging a jointly measurable field over a probability measure preserves
any uniform L² bound on its random sections. -/
theorem probability_average_uniform_l2_bound
    {Ω X E : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (M : ℝ) (hM : 0 ≤ M) (f : X × Ω → E) (hf : Measurable f)
    (hsec : ∀ x, MemLp (fun ω => f (x, ω)) 2 μ ∧
      eLpNorm (fun ω => f (x, ω)) 2 μ ≤ ENNReal.ofReal M) :
    (∀ᵐ ω ∂μ, Integrable (fun x => f (x, ω)) ν) ∧
      MemLp (fun ω => ∫ x, f (x, ω) ∂ν) 2 μ ∧
      eLpNorm (fun ω => ∫ x, f (x, ω) ∂ν) 2 μ ≤ ENNReal.ofReal M := by
  have h := normed_integral_moment_le μ ν (p := 2) (by norm_num)
    (fun _ => M) measurable_const (fun _ => hM) (integrable_const M) f hf
    (by simpa using hsec)
  simpa using h

/-- Every measurable family of shifts of a uniformly L²-bounded field
retains the same bound after averaging against a probability measure. -/
theorem shifted_probability_average_uniform_l2_bound
    {Ω X Z E : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure Z) [IsProbabilityMeasure ν]
    (M : ℝ) (hM : 0 ≤ M) (f : X × Ω → E) (hf : Measurable f)
    (hsec : ∀ x, MemLp (fun ω => f (x, ω)) 2 μ ∧
      eLpNorm (fun ω => f (x, ω)) 2 μ ≤ ENNReal.ofReal M)
    (s : Z → X) (hs : Measurable s) :
    MemLp (fun ω => ∫ z, f (s z, ω) ∂ν) 2 μ ∧
      eLpNorm (fun ω => ∫ z, f (s z, ω) ∂ν) 2 μ ≤ ENNReal.ofReal M := by
  have hm : Measurable (fun p : Z × Ω => f (s p.1, p.2)) :=
    hf.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  exact (probability_average_uniform_l2_bound μ ν M hM _ hm (fun z => hsec (s z))).2

/-- The canonical physical gradient as a jointly measurable stationary field. -/
@[nolint unusedArguments]
private def physicalCanonicalGradient {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ}
    (Q : EnvironmentLaw d L r) (i : Fin d) (p : Vec d × PhysicalField d L) :
    EuclideanSpace ℝ (Fin d) :=
  (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
    (reducedEnvironmentLaw Q)) (translate p.1 (reduce p.2.1))

/-- Probability averages of shifted canonical gradients retain one finite
L² bound, uniformly over all measurable shifts. -/
private theorem physical_gradient_shifted_probability_averages
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (i : Fin d) {Z : Type*} [MeasurableSpace Z]
    (ν : Measure Z) [IsProbabilityMeasure ν] :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : Z → Vec d, Measurable s →
      MemLp (fun ω => ∫ z, physicalCanonicalGradient Q i (s z, ω) ∂ν)
        2 (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω => ∫ z, physicalCanonicalGradient Q i (s z, ω) ∂ν)
        2 (physicalReferenceLaw Q) ≤ ENNReal.ofReal M := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  obtain ⟨hf, M, hM, hb⟩ := physical_canonical_gradient_jointly_measurable_uniform_memLp Q i
  refine ⟨M, hM, ?_⟩
  intro s hs
  exact shifted_probability_average_uniform_l2_bound (physicalReferenceLaw Q) ν M hM
    (physicalCanonicalGradient Q i) hf hb s hs

/-- The normalized smooth kernel defines a probability measure. -/
private def correctorBumpMeasure {d : ℕ} (b : ContDiffBump (0 : Vec d)) :
    Measure (Vec d) :=
  volume.withDensity (fun x => ENNReal.ofReal (b.normed volume x))

private theorem correctorBumpMeasure_isProbability {d : ℕ}
    (b : ContDiffBump (0 : Vec d)) : IsProbabilityMeasure (correctorBumpMeasure b) := by
  rw [isProbabilityMeasure_iff, correctorBumpMeasure,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal b.integrable_normed
      (Filter.Eventually.of_forall b.nonneg_normed), b.integral_normed]
  simp

/-- Integrating against the bump measure is the usual weighted integral. -/
private theorem integral_correctorBumpMeasure {d : ℕ}
    (b : ContDiffBump (0 : Vec d)) (f : Vec d → ℝ) :
    (∫ z, f z ∂correctorBumpMeasure b) =
      ∫ z, b.normed volume z * f z := by
  rw [correctorBumpMeasure, integral_withDensity_eq_integral_toReal_smul
    b.continuous_normed.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (b.nonneg_normed _), smul_eq_mul]

/-- The unit segment carries a probability measure. -/
private theorem correctorSegment_isProbability :
    IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  rw [isProbabilityMeasure_iff, Measure.restrict_apply MeasurableSet.univ]
  simp [Real.volume_Ioc]

/-- The gradient averaged over a segment and a normalized mollifier obeys a
single L² bound, uniformly in the endpoints and mollifier. -/
private theorem physical_gradient_segment_bump_average_bound
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (i : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (b : ContDiffBump (0 : Vec d)) (x y : Vec d),
      let ν := (volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b)
      (∀ᵐ ω ∂physicalReferenceLaw Q, Integrable (fun p => physicalCanonicalGradient Q i
        (y + p.1 • (x - y) - p.2, ω)) ν) ∧
      MemLp (fun ω => ∫ p, physicalCanonicalGradient Q i
        (y + p.1 • (x - y) - p.2, ω) ∂ν) 2 (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω => ∫ p, physicalCanonicalGradient Q i
        (y + p.1 • (x - y) - p.2, ω) ∂ν) 2 (physicalReferenceLaw Q)
        ≤ ENNReal.ofReal M := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  letI : IsProbabilityMeasure (volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    correctorSegment_isProbability
  obtain ⟨hf, M, hM, hb⟩ := physical_canonical_gradient_jointly_measurable_uniform_memLp Q i
  refine ⟨M, hM, ?_⟩
  intro b x y
  letI : IsProbabilityMeasure (correctorBumpMeasure b) := correctorBumpMeasure_isProbability b
  let s : ℝ × Vec d → Vec d := fun p => y + p.1 • (x - y) - p.2
  have hs : Measurable s := by
    dsimp [s]
    fun_prop
  have hm : Measurable (fun p : (ℝ × Vec d) × PhysicalField d L =>
      physicalCanonicalGradient Q i (s p.1, p.2)) :=
    hf.comp ((hs.comp measurable_fst).prodMk measurable_snd)
  exact probability_average_uniform_l2_bound (physicalReferenceLaw Q)
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b)) M hM
    _ hm (fun p => hb (s p))

/-- Each coordinate of an integrable segment--mollifier average can be
computed by the iterated weighted integral. -/
private theorem segment_bump_average_coordinate {d : ℕ}
    (b : ContDiffBump (0 : Vec d))
    (F : ℝ × Vec d → EuclideanSpace ℝ (Fin d)) (j : Fin d)
    (hF : Integrable F ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (correctorBumpMeasure b))) :
    (∫ p, F p ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (correctorBumpMeasure b)).ofLp j =
      ∫ t in Set.Ioc (0 : ℝ) 1, ∫ z, b.normed volume z * (F (t, z)).ofLp j := by
  letI : IsProbabilityMeasure (correctorBumpMeasure b) := correctorBumpMeasure_isProbability b
  let π : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj j
  have hi : Integrable (fun p => (F p).ofLp j)
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b)) := by
    simpa only [π, PiLp.proj_apply] using π.integrable_comp hF
  calc
    (∫ p, F p ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (correctorBumpMeasure b)).ofLp j =
        ∫ p, (F p).ofLp j ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
          (correctorBumpMeasure b) := by
            simpa only [π, PiLp.proj_apply] using (π.integral_comp_comm hF).symm
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ z, (F (t, z)).ofLp j
        ∂correctorBumpMeasure b := integral_prod _ hi
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ z, b.normed volume z * (F (t, z)).ofLp j := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun t => integral_correctorBumpMeasure b _)

/-- Pairing a segment--mollifier gradient average with a fixed vector gives
exactly the scalar segment integral appearing in the weak-gradient formula. -/
private theorem segment_bump_average_pairing {d : ℕ}
    (b : ContDiffBump (0 : Vec d)) (v : Vec d)
    (F : ℝ × Vec d → EuclideanSpace ℝ (Fin d))
    (hF : Integrable F ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (correctorBumpMeasure b))) :
    (∑ j : Fin d, v j * (∫ p, F p ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
      (correctorBumpMeasure b)).ofLp j) =
      ∫ t in Set.Ioc (0 : ℝ) 1,
        ∑ j : Fin d, v j * ∫ z, b.normed volume z * (F (t, z)).ofLp j := by
  letI : IsProbabilityMeasure (correctorBumpMeasure b) := correctorBumpMeasure_isProbability b
  have hi (j : Fin d) : Integrable (fun t =>
      ∫ z, b.normed volume z * (F (t, z)).ofLp j)
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    have hj : Integrable (fun p => (F p).ofLp j)
        ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b)) := by
      simpa only [PiLp.proj_apply] using (EuclideanSpace.proj (𝕜 := ℝ) j).integrable_comp hF
    convert hj.integral_prod_left using 1
    funext t
    exact (integral_correctorBumpMeasure b _).symm
  calc
    (∑ j : Fin d, v j * (∫ p, F p ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (correctorBumpMeasure b)).ofLp j) =
        ∑ j : Fin d, v j * ∫ t in Set.Ioc (0 : ℝ) 1,
          ∫ z, b.normed volume z * (F (t, z)).ofLp j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [segment_bump_average_coordinate b F j hF]
    _ = ∫ t in Set.Ioc (0 : ℝ) 1,
        ∑ j : Fin d, v j * ∫ z, b.normed volume z * (F (t, z)).ofLp j := by
          rw [integral_finsetSum Finset.univ (fun j _ => (hi j).const_mul (v j))]
          simp_rw [integral_const_mul]

/-- A mollified weak potential increment is the pairing of its displacement
with the averaged weak gradient. -/
private theorem mollified_increment_eq_segment_bump_pairing {d : ℕ}
    {u : Vec d → ℝ} (hu : Continuous u)
    {G : Vec d → EuclideanSpace ℝ (Fin d)}
    (hDu : HasWeakGradient Set.univ u (fun z => (G z).ofLp))
    (b : ContDiffBump (0 : Vec d)) (x y : Vec d)
    (hF : Integrable (fun p : ℝ × Vec d => G (y + p.1 • (x - y) - p.2))
      ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b))) :
    MeasureTheory.convolution (b.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
      MeasureTheory.convolution (b.normed volume) u (ContinuousLinearMap.lsmul ℝ ℝ) volume y =
    ∑ j : Fin d, (x - y) j *
      (∫ p, G (y + p.1 • (x - y) - p.2)
        ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (correctorBumpMeasure b)).ofLp j := by
  rw [mollified_potential_increment_eq_segment_integral hu hDu
    (b.contDiff_normed (μ := (volume : Measure (Vec d))))
    (b.hasCompactSupport_normed (μ := (volume : Measure (Vec d)))) x y]
  exact (segment_bump_average_pairing b (x - y) _ hF).symm

/-- The coordinate pairing is bounded by the Euclidean displacement norm. -/
private theorem corrector_coordinate_pairing_bound {d : ℕ}
    (v : Vec d) (w : EuclideanSpace ℝ (Fin d)) :
    |∑ j : Fin d, v j * w.ofLp j| ≤ euclideanNorm v * ‖w‖ := by
  have h := abs_real_inner_le_norm (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) w
  simpa only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PiLp.toLp_apply, ← TimeChange.euclideanNorm_eq_norm_toLp, mul_comm] using h

/-- Pairing an L² Euclidean random vector with a fixed displacement
preserves the L² bound with the Euclidean displacement as factor. -/
@[nolint unusedArguments]
private theorem corrector_pairing_l2_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (v : Vec d)
    (F : Ω → EuclideanSpace ℝ (Fin d)) (hF : MemLp F 2 μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : eLpNorm F 2 μ ≤ ENNReal.ofReal M) :
    MemLp (fun ω => ∑ j : Fin d, v j * (F ω).ofLp j) 2 μ ∧
    eLpNorm (fun ω => ∑ j : Fin d, v j * (F ω).ofLp j) 2 μ ≤
      ENNReal.ofReal (euclideanNorm v * M) := by
  let V : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 v
  have heq : (fun ω => ∑ j : Fin d, v j * (F ω).ofLp j) =
      (fun ω => @inner ℝ _ _ V (F ω)) := by
    funext ω
    simp only [V, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, PiLp.toLp_apply, mul_comm]
  have hm : MemLp (fun ω => ∑ j : Fin d, v j * (F ω).ofLp j) 2 μ := by
    rw [heq]
    exact hF.const_inner V
  refine ⟨hm, ?_⟩
  let c : ℝ≥0 := ⟨euclideanNorm v, Real.sqrt_nonneg _⟩
  have hle : ∀ᵐ ω ∂μ,
      ‖∑ j : Fin d, v j * (F ω).ofLp j‖₊ ≤ c * ‖F ω‖₊ := by
    filter_upwards with ω
    apply NNReal.coe_le_coe.mp
    change ‖∑ j : Fin d, v j * (F ω).ofLp j‖ ≤ euclideanNorm v * ‖F ω‖
    simpa only [Real.norm_eq_abs] using corrector_coordinate_pairing_bound v (F ω)
  calc
    eLpNorm (fun ω => ∑ j : Fin d, v j * (F ω).ofLp j) 2 μ ≤
        c • eLpNorm F 2 μ :=
      eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hm.aestronglyMeasurable hle 2
    _ ≤ c • ENNReal.ofReal M := by
      change (c : ENNReal) * eLpNorm F 2 μ ≤ (c : ENNReal) * ENNReal.ofReal M
      simpa only [mul_comm] using mul_le_mul_left hbound (c : ENNReal)
    _ = ENNReal.ofReal (euclideanNorm v * M) := by
      change (c : ENNReal) * ENNReal.ofReal M = ENNReal.ofReal (euclideanNorm v * M)
      rw [ENNReal.coe_nnreal_eq c]
      change ENNReal.ofReal (euclideanNorm v) * ENNReal.ofReal M =
        ENNReal.ofReal (euclideanNorm v * M)
      exact (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm

/-- A pointwise almost-everywhere limit retains a uniform finite L² bound. -/
private theorem corrector_l2_limit_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (F : ℕ → Ω → ℝ) (G : Ω → ℝ) (C : ℝ)
    (hF : ∀ n, MemLp (F n) 2 μ)
    (hbound : ∀ n, eLpNorm (F n) 2 μ ≤ ENNReal.ofReal C)
    (hG : AEStronglyMeasurable G μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun n => F n ω) atTop (𝓝 (G ω))) :
    MemLp G 2 μ ∧ eLpNorm G 2 μ ≤ ENNReal.ofReal C := by
  have h := Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound)
    (fun n => (hF n).aestronglyMeasurable) hG hlim
  exact ⟨h.trans_lt ENNReal.ofReal_lt_top, h⟩

/-- Every coordinate of a continuous canonical weak corrector has an L²
increment bound with a constant independent of the two endpoints. -/
private theorem physical_corrector_coordinate_increment_l2
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hae : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      Continuous (χ ω) ∧ ∀ i : Fin d,
        HasWeakGradient Set.univ (fun x => χ ω x i)
          (fun x => (physicalCanonicalGradient Q i (x, ω)).ofLp))
    (i : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x y : Vec d,
      MemLp (fun ω : PhysicalField d L => χ ω x i - χ ω y i)
        2 (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω : PhysicalField d L => χ ω x i - χ ω y i)
        2 (physicalReferenceLaw Q) ≤ ENNReal.ofReal (euclideanNorm (x - y) * M) := by
  obtain ⟨M, hM, hb⟩ := physical_gradient_segment_bump_average_bound Q i
  refine ⟨M, hM, ?_⟩
  intro x y
  let A (n : ℕ) (ω : PhysicalField d L) :=
    ∫ p : ℝ × Vec d, physicalCanonicalGradient Q i (y + p.1 • (x - y) - p.2, ω)
      ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)).prod
        (correctorBumpMeasure (correctorReconstructionBump d n))
  let F (n : ℕ) (ω : PhysicalField d L) :=
    ∑ j : Fin d, (x - y) j * (A n ω).ofLp j
  have hF (n : ℕ) : MemLp (F n) 2 (physicalReferenceLaw Q) ∧
      eLpNorm (F n) 2 (physicalReferenceLaw Q) ≤
        ENNReal.ofReal (euclideanNorm (x - y) * M) := by
    have hn := hb (correctorReconstructionBump d n) x y
    exact corrector_pairing_l2_bound (physicalReferenceLaw Q) (x - y) (A n)
      hn.2.1 M hM hn.2.2
  have hmeas (z : Vec d) : Measurable (fun ω : PhysicalField d L => χ ω z i) := by
    exact (measurable_pi_apply i).comp (hχ.comp
      (measurable_subtype_coe.prodMk measurable_const))
  have hG : AEStronglyMeasurable
      (fun ω : PhysicalField d L => χ ω x i - χ ω y i) (physicalReferenceLaw Q) :=
    ((hmeas x).sub (hmeas y)).aestronglyMeasurable
  have hlim : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      Tendsto (fun n => F n ω) atTop (𝓝 (χ ω x i - χ ω y i)) := by
    filter_upwards [hae, ae_all_iff.2 (fun n =>
      (hb (correctorReconstructionBump d n) x y).1)] with ω hω hI
    have hc : Continuous (fun z => χ ω z i) := (continuous_apply i).comp hω.1
    have hr : Tendsto (fun n : ℕ => (correctorReconstructionBump d n).rOut)
        atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hx := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := (volume : Measure (Vec d))) hr hc x
    have hy := ContDiffBump.convolution_tendsto_right_of_continuous
      (μ := (volume : Measure (Vec d))) hr hc y
    have heq (n : ℕ) : F n ω =
        MeasureTheory.convolution ((correctorReconstructionBump d n).normed volume)
          (fun z => χ ω z i) (ContinuousLinearMap.lsmul ℝ ℝ) volume x -
        MeasureTheory.convolution ((correctorReconstructionBump d n).normed volume)
          (fun z => χ ω z i) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
      exact (mollified_increment_eq_segment_bump_pairing hc (hω.2 i)
        (correctorReconstructionBump d n) x y (hI n)).symm
    simpa only [heq] using hx.sub hy
  exact corrector_l2_limit_bound (physicalReferenceLaw Q) F _ _
    (fun n => (hF n).1) (fun n => (hF n).2) hG hlim

/-- Uniform quadratic increment bounds for a jointly measurable canonical potential. -/
private theorem physical_corrector_l2_increments_of_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hw : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      Continuous (χ ω) ∧ ∀ i : Fin d,
        HasWeakGradient Set.univ (fun x => χ ω x i)
          (fun x => (physicalCanonicalGradient Q i (x, ω)).ofLp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Vec d,
      Integrable (fun ω : PhysicalField d L =>
        (euclideanNorm (χ ω x-χ ω y))^2) (physicalReferenceLaw Q) ∧
      (∫ ω : PhysicalField d L, (euclideanNorm (χ ω x-χ ω y))^2
        ∂physicalReferenceLaw Q) ≤ C*(euclideanNorm (x-y))^2 := by
  choose M hM hb using fun i => physical_corrector_coordinate_increment_l2 Q χ hχ hw i
  let B : ℝ := ∑ i : Fin d, M i
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i _ => hM i)
  refine ⟨(Real.sqrt d * B)^2, sq_nonneg _, ?_⟩
  · intro x y
    letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
    let V : PhysicalField d L → Vec d := fun ω => χ ω x - χ ω y
    have hm (z : Vec d) : Measurable (fun ω : PhysicalField d L => χ ω z) :=
      hχ.comp (measurable_subtype_coe.prodMk measurable_const)
    have hV : Measurable V := (hm x).sub (hm y)
    have hb' (i : Fin d) : eLpNorm (fun ω => V ω i) (ENNReal.ofReal 2)
        (physicalReferenceLaw Q) ≤ ENNReal.ofReal (euclideanNorm (x-y) * B) := by
      have hi : M i ≤ B := Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ i)
      simpa only [V, Pi.sub_apply, ENNReal.ofReal_ofNat] using
        (hb i x y).2.trans (ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left hi (Real.sqrt_nonneg _)))
    let W : PhysicalField d L → EuclideanSpace ℝ (Fin d) :=
      fun ω => WithLp.toLp 2 (V ω)
    have hW : Measurable W := (WithLp.measurable_toLp 2 (Vec d)).comp hV
    have hWb (i : Fin d) : eLpNorm (fun ω => W ω i) (ENNReal.ofReal 2)
        (physicalReferenceLaw Q) ≤ ENNReal.ofReal (euclideanNorm (x-y) * B) := by
      simpa only [W] using hb' i
    have hnorm := (eLpNorm_euclidean_le_sqrt_card (physicalReferenceLaw Q) 2
      (euclideanNorm (x-y) * B) (by norm_num)
      (mul_nonneg (Real.sqrt_nonneg _) hB) W hW hWb).2
    rw [← eLpNorm_norm W hW.aestronglyMeasurable] at hnorm
    have hnorm' : eLpNorm (fun ω => euclideanNorm (V ω)) 2 (physicalReferenceLaw Q) ≤
        ENNReal.ofReal (Real.sqrt d * (euclideanNorm (x-y) * B)) := by
      simpa only [W, Fintype.card_fin, ← TimeChange.euclideanNorm_eq_norm_toLp,
        ENNReal.ofReal_ofNat] using hnorm
    have hmem : MemLp (fun ω => euclideanNorm (V ω)) 2 (physicalReferenceLaw Q) :=
      hnorm'.trans_lt ENNReal.ofReal_lt_top
    have hint : Integrable (fun ω => (euclideanNorm (V ω))^2) (physicalReferenceLaw Q) := by
      simpa only [Real.norm_eq_abs, sq_abs] using hmem.integrable_sq
    refine ⟨hint, ?_⟩
    have hreal : Real.sqrt (∫ ω, (euclideanNorm (V ω))^2 ∂physicalReferenceLaw Q) ≤
        Real.sqrt d * (euclideanNorm (x-y) * B) := by
      apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _) hB))).mp
      have hrms : eLpNorm (fun ω => euclideanNorm (V ω)) 2 (physicalReferenceLaw Q) =
          ENNReal.ofReal (Real.sqrt (∫ ω, (euclideanNorm (V ω))^2
            ∂physicalReferenceLaw Q)) := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow,
          Real.norm_eq_abs, sq_abs] using
            hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
      rw [← hrms]
      exact hnorm'
    have hi0 : 0 ≤ ∫ ω, (euclideanNorm (V ω))^2 ∂physicalReferenceLaw Q :=
      integral_nonneg (fun ω => sq_nonneg _)
    calc
      (∫ ω : PhysicalField d L, (euclideanNorm (χ ω x-χ ω y))^2
          ∂physicalReferenceLaw Q) ≤
          (Real.sqrt d * (euclideanNorm (x-y) * B))^2 := by
        have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
          (mul_nonneg (Real.sqrt_nonneg _) hB))).2 hreal
        rw [Real.sq_sqrt hi0] at hs
        exact hs
      _ = (Real.sqrt d * B)^2 * (euclideanNorm (x-y))^2 := by ring

/-- The actual jointly measurable canonical corrector has square-integrable
increments with a uniform quadratic displacement bound. -/
theorem exists_jointly_measurable_physical_corrector_with_l2_increments
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Vec d,
       Integrable (fun ω : PhysicalField d L =>
        (euclideanNorm (χ ω x-χ ω y))^2) (ReductionImageV3.physicalReferenceLaw Q) ∧
       (∫ ω : PhysicalField d L, (euclideanNorm (χ ω x-χ ω y))^2
        ∂(ReductionImageV3.physicalReferenceLaw Q)) ≤ C*(euclideanNorm (x-y))^2 := by
  obtain ⟨χ, hχ, hω⟩ := exists_jointly_measurable_physical_harmonic_corrector_with_gradient Q
  have hw : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      Continuous (χ ω) ∧ ∀ i : Fin d,
        HasWeakGradient Set.univ (fun x => χ ω x i)
          (fun x => (physicalCanonicalGradient Q i (x, ω)).ofLp) := by
    filter_upwards [hω] with ω h
    exact ⟨h.1, h.2.2.1⟩
  refine ⟨χ, hχ, ?_, physical_corrector_l2_increments_of_gradient Q χ hχ hw⟩
  filter_upwards [hω] with ω h
  exact ⟨h.1, h.2.1, h.2.2.2⟩

/-- A jointly measurable corrector, continuous almost everywhere, has a
measurable centered path version along any measurable continuous path. -/
theorem exists_measurable_corrector_path_version
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (Y : Ω → Path d) (hY : Measurable Y) :
    ∃ Z : Ω → Path d, Measurable Z ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
        Z ω t = χ ω (Y ω t) - χ ω (Y ω 0) := by
  classical
  obtain ⟨s, hs, hsm, hsc⟩ := hcont.exists_measurable_mem
  let Z : Ω → Path d := fun ω =>
    if h : ω ∈ s then
      ⟨fun t => χ ω (Y ω t) - χ ω (Y ω 0),
        ((hsc ω h).comp (Y ω).continuous).sub continuous_const⟩
    else 0
  refine ⟨Z, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have ht : Measurable (fun ω => χ ω (Y ω t) - χ ω (Y ω 0)) :=
      (hχ.comp (measurable_id.prodMk ((measurable_pathPosition t).comp hY))).sub
        (hχ.comp (measurable_id.prodMk ((measurable_pathPosition 0).comp hY)))
    have heval : (fun ω => Z ω t) =
        s.piecewise (fun ω => χ ω (Y ω t) - χ ω (Y ω 0)) (fun _ => 0) := by
      funext ω
      by_cases h : ω ∈ s <;> simp [Z, Set.piecewise, h]
    rw [heval]
    exact ht.piecewise hsm measurable_const
  · filter_upwards [hs] with ω hω
    intro t
    simp [Z, hω]


/-- A jointly measurable corrector, continuous almost everywhere, has a
measurable two-point path version along measurable continuous paths. -/
theorem exists_measurable_two_point_corrector_path_version
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (X Y : Ω → Path d) (hX : Measurable X) (hY : Measurable Y) :
    ∃ Z : Ω → Path d, Measurable Z ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
        Z ω t = χ ω (Y ω t + X ω t) - χ ω (Y ω t) := by
  classical
  obtain ⟨s, hs, hsm, hsc⟩ := hcont.exists_measurable_mem
  let Z : Ω → Path d := fun ω =>
    if h : ω ∈ s then
      ⟨fun t => χ ω (Y ω t + X ω t) - χ ω (Y ω t),
        ((hsc ω h).comp ((Y ω).continuous.add (X ω).continuous)).sub
          ((hsc ω h).comp (Y ω).continuous)⟩
    else 0
  refine ⟨Z, ?_, ?_⟩
  · apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have ht : Measurable (fun ω => χ ω (Y ω t + X ω t) - χ ω (Y ω t)) :=
      (hχ.comp (measurable_id.prodMk
        (((measurable_pathPosition t).comp hY).add
          ((measurable_pathPosition t).comp hX)))).sub
        (hχ.comp (measurable_id.prodMk ((measurable_pathPosition t).comp hY)))
    have heval : (fun ω => Z ω t) =
        s.piecewise (fun ω => χ ω (Y ω t + X ω t) - χ ω (Y ω t)) (fun _ => 0) := by
      funext ω
      by_cases h : ω ∈ s <;> simp [Z, Set.piecewise, h]
    rw [heval]
    exact ht.piecewise hsm measurable_const
  · filter_upwards [hs] with ω hω
    intro t
    simp [Z, hω]


/-- A measurable time change preserves the measurable two-point corrector path. -/
theorem exists_measurable_time_changed_two_point_corrector_path_version
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (χ : Ω → Vec d → Vec d)
    (hχ : Measurable (fun z : Ω × Vec d => χ z.1 z.2))
    (hcont : ∀ᵐ ω ∂μ, Continuous (χ ω))
    (X Y : Ω → Path d) (hX : Measurable X) (hY : Measurable Y)
    (θ : Ω → ContinuousMap ℝ≥0 ℝ≥0) (hθ : Measurable θ) :
    ∃ Z : Ω → Path d, Measurable Z ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
        Z ω t = χ ω (Y ω (θ ω t) + X ω (θ ω t)) - χ ω (Y ω (θ ω t)) := by
  obtain ⟨Z, hZ, hZeq⟩ :=
    exists_measurable_two_point_corrector_path_version μ χ hχ hcont X Y hX hY
  refine ⟨fun ω => (Z ω).comp (θ ω), ?_, ?_⟩
  · exact ContinuousMap.continuous_comp'.measurable.comp (hθ.prodMk hZ)
  · filter_upwards [hZeq] with ω hω
    intro t
    exact hω (θ ω t)

/-- The actual physical corrector admits a measurable time-changed two-point
observable along measurable continuous paths. -/
theorem exists_physical_measurable_time_changed_corrector_observable
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (X Y : ReductionImageV3.PhysicalField d L → Path d)
    (hX : Measurable X) (hY : Measurable Y)
    (θ : ReductionImageV3.PhysicalField d L → ContinuousMap ℝ≥0 ℝ≥0)
    (hθ : Measurable θ) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
    ∃ Z : ReductionImageV3.PhysicalField d L → Path d, Measurable Z ∧
      ∀ᵐ ω ∂ ReductionImageV3.physicalReferenceLaw Q, ∀ t : ℝ≥0,
        Z ω t = χ ω (Y ω (θ ω t)+X ω (θ ω t))-χ ω (Y ω (θ ω t)) := by
  obtain ⟨χ, hmeas, hχ⟩ := exists_jointly_measurable_physical_vector_harmonic_corrector Q
  have hphysical : Measurable (fun z : PhysicalField d L × Vec d => χ z.1 z.2) :=
    hmeas.comp ((measurable_subtype_coe.comp measurable_fst).prodMk measurable_snd)
  have hcont : ∀ᵐ (ω : PhysicalField d L) ∂ physicalReferenceLaw Q, Continuous (χ ω) :=
    hχ.mono (fun _ h => h.1)
  obtain ⟨Z, hZ, hZeq⟩ := exists_measurable_time_changed_two_point_corrector_path_version
    (physicalReferenceLaw Q) (fun ω => χ ω) hphysical hcont X Y hX hY θ hθ
  exact ⟨χ, hmeas, hχ, Z, hZ, hZeq⟩

/-- The physical corrector has a measurable observable on any sample whose
environment law is dominated by the physical reference law. -/
theorem exists_physical_corrector_observable_on_dominated_environment_sample
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Ω → ReductionImageV3.PhysicalField d L) (he : Measurable e)
    (hdom : Measure.map e μ ≪ ReductionImageV3.physicalReferenceLaw Q)
    (X Y : Ω → Path d) (hX : Measurable X) (hY : Measurable Y)
    (θ : Ω → ContinuousMap ℝ≥0 ℝ≥0) (hθ : Measurable θ) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
      ∃ Z : Ω → Path d, Measurable Z ∧
        ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
          Z ω t = χ (e ω) (Y ω (θ ω t)+X ω (θ ω t))-χ (e ω) (Y ω (θ ω t)) := by
  obtain ⟨χ, hmeas, hχ⟩ := exists_jointly_measurable_physical_vector_harmonic_corrector Q
  have hsample : Measurable (fun z : Ω × Vec d => χ (e z.1) z.2) :=
    hmeas.comp (((measurable_subtype_coe.comp he).comp measurable_fst).prodMk measurable_snd)
  have hcont : ∀ᵐ ω ∂μ, Continuous (χ (e ω)) :=
    ae_of_ae_map he.aemeasurable (hdom.ae_le (hχ.mono (fun _ h => h.1)))
  obtain ⟨Z, hZ, hZeq⟩ := exists_measurable_time_changed_two_point_corrector_path_version
    μ (fun ω => χ (e ω)) hsample hcont X Y hX hY θ hθ
  exact ⟨χ, hmeas, hχ, Z, hZ, hZeq⟩

/-- A single physical corrector gives a measurable sequence of scaled,
time-changed two-point observables on a dominated environment sample. -/
@[nolint unusedArguments]
theorem exists_scaled_physical_corrector_observables_on_dominated_environment_sample
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Ω → ReductionImageV3.PhysicalField d L) (he : Measurable e)
    (hdom : Measure.map e μ ≪ ReductionImageV3.physicalReferenceLaw Q)
    (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n)
    (X Y : ℕ → Ω → Path d)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (θ : ℕ → Ω → ContinuousMap ℝ≥0 ℝ≥0)
    (hθ : ∀ n, Measurable (θ n)) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
      ∃ Z : ℕ → Ω → Path d, (∀ n, Measurable (Z n)) ∧
        ∀ᵐ ω ∂μ, ∀ n, ∀ t : ℝ≥0,
          Z n ω t = (ρ n)⁻¹ • (χ (e ω) (Y n ω (θ n ω t)+X n ω (θ n ω t))-χ (e ω) (Y n ω (θ n ω t))) := by
  obtain ⟨χ, hmeas, hχ⟩ := exists_jointly_measurable_physical_vector_harmonic_corrector Q
  have hsample : Measurable (fun z : Ω × Vec d => χ (e z.1) z.2) :=
    hmeas.comp (((measurable_subtype_coe.comp he).comp measurable_fst).prodMk measurable_snd)
  have hcont : ∀ᵐ ω ∂μ, Continuous (χ (e ω)) :=
    ae_of_ae_map he.aemeasurable (hdom.ae_le (hχ.mono (fun _ h => h.1)))
  have hex : ∀ n, ∃ Z : Ω → Path d, Measurable Z ∧
      ∀ᵐ ω ∂μ, ∀ t : ℝ≥0,
        Z ω t = χ (e ω) (Y n ω (θ n ω t) + X n ω (θ n ω t)) -
          χ (e ω) (Y n ω (θ n ω t)) := by
    intro n
    exact exists_measurable_time_changed_two_point_corrector_path_version
      μ (fun ω => χ (e ω)) hsample hcont (X n) (Y n) (hX n) (hY n) (θ n) (hθ n)
  choose Z hZ hZeq using hex
  refine ⟨χ, hmeas, hχ, (fun n ω => (ρ n)⁻¹ • Z n ω), ?_, ?_⟩
  · intro n
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (measurable_const_smul (ρ n)⁻¹).comp ((measurable_pathPosition t).comp (hZ n))
  · filter_upwards [ae_all_iff.mpr hZeq] with ω hω
    intro n t
    change (ρ n)⁻¹ • (Z n ω t) = _
    rw [hω n t]

/-- Scaled corrector and harmonic-coordinate observables share one physical corrector. -/
theorem exists_scaled_harmonic_coordinate_observables_on_dominated_environment_sample
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
 (e : Ω → ReductionImageV3.PhysicalField d L) (he : Measurable e)
 (hdom : Measure.map e μ ≪ ReductionImageV3.physicalReferenceLaw Q)
 (ρ : ℕ → ℝ) (hρ : ∀ n, 0 < ρ n)
 (X Y : ℕ → Ω → Path d)
 (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
 (θ : ℕ → Ω → ContinuousMap ℝ≥0 ℝ≥0)
 (hθ : ∀ n, Measurable (θ n)) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
 ∃ Z H : ℕ → Ω → Path d, (∀ n, Measurable (Z n)) ∧
 (∀ n, Measurable (H n)) ∧
 ∀ᵐ ω ∂μ, ∀ n, ∀ t : ℝ≥0,
 Z n ω t = (ρ n)⁻¹ • (χ (e ω) (Y n ω (θ n ω t)+X n ω (θ n ω t))-χ (e ω) (Y n ω (θ n ω t))) ∧
 H n ω t = (ρ n)⁻¹ • (X n ω (θ n ω t)+
 (χ (e ω) (Y n ω (θ n ω t)+X n ω (θ n ω t))-χ (e ω) (Y n ω (θ n ω t)))) := by
  obtain ⟨χ, hmeas, hχ, Z, hZ, hZeq⟩ :=
    exists_scaled_physical_corrector_observables_on_dominated_environment_sample
      Q μ e he hdom ρ hρ X Y hX hY θ hθ
  let H : ℕ → Ω → Path d := fun n ω => (ρ n)⁻¹ • (X n ω).comp (θ n ω) + Z n ω
  refine ⟨χ, hmeas, hχ, Z, H, hZ, ?_, ?_⟩
  · intro n
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    have hc : Measurable (fun ω => (X n ω).comp (θ n ω)) :=
      ContinuousMap.continuous_comp'.measurable.comp ((hθ n).prodMk (hX n))
    exact ((measurable_const_smul (ρ n)⁻¹).comp
      ((measurable_pathPosition t).comp hc)).add ((measurable_pathPosition t).comp (hZ n))
  · filter_upwards [hZeq] with ω hω
    intro n t
    refine ⟨hω n t, ?_⟩
    change (ρ n)⁻¹ • X n ω (θ n ω t) + Z n ω t = _
    rw [hω n t, smul_add]

/-- The actual canonical corrector is a stationary cocycle with L² increments. -/
theorem exists_physical_l2_corrector_with_stationary_cocycle
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r) :
    ∃ χ : FieldPair d → Vec d → Vec d,
      Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2) ∧
      (∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        Continuous (χ ω) ∧ χ ω 0 = 0 ∧
        (∀ R ε : ℝ, 0 < R → 0 < ε → ∀ᶠ t : ℝ in atTop,
          ∀ x, euclideanNorm x ≤ (t+1)*R → euclideanNorm (χ ω x)/(t+1) ≤ ε) ∧
        (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
          euclideanNorm (χ ω x) ≤ C + ε*euclideanNorm x) ∧
        (∀ (i : Fin d) (R : ℝ), 0 < R →
          WeakSolution (ball 0 R) (reduce ω.1).1 (fun x => x i + χ ω x i)
            (fun x => (correctorUnitVector i + (canonicalCorrectorGradient Q i :
              Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
                (translate x (reduce ω.1))).ofLp))) ∧
      (∀ y : Vec d, ∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
        ∀ x : Vec d, χ (translate y ω.1) x = χ ω (y+x)-χ ω y) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : Vec d,
       Integrable (fun ω : PhysicalField d L =>
        (euclideanNorm (χ ω x-χ ω y))^2) (ReductionImageV3.physicalReferenceLaw Q) ∧
       (∫ ω : PhysicalField d L, (euclideanNorm (χ ω x-χ ω y))^2
        ∂(ReductionImageV3.physicalReferenceLaw Q)) ≤ C*(euclideanNorm (x-y))^2 := by
  obtain ⟨χ, hχ, hω⟩ := exists_jointly_measurable_physical_harmonic_corrector_with_gradient Q
  have hw : ∀ᵐ ω : PhysicalField d L ∂physicalReferenceLaw Q,
      Continuous (χ ω) ∧ ∀ i : Fin d,
        HasWeakGradient Set.univ (fun x => χ ω x i)
          (fun x => (physicalCanonicalGradient Q i (x, ω)).ofLp) := by
    filter_upwards [hω] with ω h
    exact ⟨h.1, h.2.2.1⟩
  refine ⟨χ, hχ, ?_, ?_, physical_corrector_l2_increments_of_gradient Q χ hχ hw⟩
  · filter_upwards [hω] with ω h
    exact ⟨h.1, h.2.1, h.2.2.2⟩
  · intro y
    have hmp : MeasurePreserving (physicalTranslate y)
        (physicalReferenceLaw Q) (physicalReferenceLaw Q) :=
      ⟨measurable_physicalTranslate _, physicalReferenceLaw_translation_invariant Q _⟩
    filter_upwards [hω, hmp.quasiMeasurePreserving.ae hω] with ω h hs
    intro x
    ext i
    have hi := normalized_weak_potential_translate
      (u := fun z => χ ω z i) (v := fun z => χ (translate y ω.1) z i)
      (G := fun z => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate z (reduce ω.1))).ofLp) y
      ((continuous_apply i).comp h.1) ((continuous_apply i).comp hs.1)
      (congrFun hs.2.1 i) (h.2.2.1 i) (by
        simpa only [physicalTranslate, reduce_translate, translate_add, add_comm] using hs.2.2.1 i) x
    exact hi


/-- Stationary corrector increments have the same coordinate cross integrals. -/
@[nolint unusedArguments]
theorem physical_corrector_stationary_increment_cross_integral
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hcoc : ∀ y : Vec d, ∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
      ∀ x : Vec d, χ (translate y ω.1) x = χ ω (y+x)-χ ω y)
    (x y : Vec d) (i j : Fin d) :
    (∫ ω : PhysicalField d L,
      (χ ω (y+x)-χ ω y) i * (χ ω (y+x)-χ ω y) j
      ∂ ReductionImageV3.physicalReferenceLaw Q) =
    (∫ ω : PhysicalField d L, χ ω x i * χ ω x j
      ∂ ReductionImageV3.physicalReferenceLaw Q) := by
  have hm : Measurable (fun ω : PhysicalField d L => χ ω x i * χ ω x j) := by
    have h : Measurable (fun ω : PhysicalField d L => χ ω x) :=
      hχ.comp (measurable_subtype_coe.prodMk measurable_const)
    exact ((measurable_pi_apply i).comp h).mul ((measurable_pi_apply j).comp h)
  calc
    _ = ∫ ω : PhysicalField d L, χ (translate y ω.1) x i * χ (translate y ω.1) x j
        ∂physicalReferenceLaw Q := by
      apply integral_congr_ae
      filter_upwards [hcoc y] with ω hω
      rw [hω x]
    _ = ∫ ω : PhysicalField d L, χ ω x i * χ ω x j ∂physicalReferenceLaw Q := by
      symm
      simpa only [physicalReferenceLaw_translation_invariant Q y, physicalTranslate] using
        (integral_map_of_stronglyMeasurable (μ := physicalReferenceLaw Q)
          (measurable_physicalTranslate y) hm.stronglyMeasurable)


/-- Polarization of the stationary corrector increment covariance. -/
theorem physical_corrector_spatial_covariance_polarization
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hcoc : ∀ y : Vec d, ∀ᵐ (ω : PhysicalField d L) ∂ ReductionImageV3.physicalReferenceLaw Q,
      ∀ x : Vec d, χ (translate y ω.1) x = χ ω (y+x)-χ ω y)
    (hL2 : ∀ x : Vec d, ∀ k : Fin d,
      MemLp (fun ω : PhysicalField d L => χ ω x k) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (x y : Vec d) (i j : Fin d) :
    (∫ ω : PhysicalField d L, χ ω x i * χ ω y j ∂ ReductionImageV3.physicalReferenceLaw Q) +
    (∫ ω : PhysicalField d L, χ ω y i * χ ω x j ∂ ReductionImageV3.physicalReferenceLaw Q) =
    (∫ ω : PhysicalField d L, χ ω x i * χ ω x j ∂ ReductionImageV3.physicalReferenceLaw Q) +
    (∫ ω : PhysicalField d L, χ ω y i * χ ω y j ∂ ReductionImageV3.physicalReferenceLaw Q) -
    (∫ ω : PhysicalField d L, χ ω (x-y) i * χ ω (x-y) j ∂ ReductionImageV3.physicalReferenceLaw Q) := by
  have hp (a b : Vec d) (k l : Fin d) :
      Integrable (fun ω : PhysicalField d L => χ ω a k * χ ω b l)
        (physicalReferenceLaw Q) :=
    (hL2 a k).integrable_mul (hL2 b l)
  have h := physical_corrector_stationary_increment_cross_integral Q χ hχ hcoc (x-y) y i j
  have he : ∀ ω : PhysicalField d L,
      (χ ω (y+(x-y))-χ ω y) i * (χ ω (y+(x-y))-χ ω y) j =
        (χ ω x i * χ ω x j - χ ω x i * χ ω y j) -
          (χ ω y i * χ ω x j - χ ω y i * χ ω y j) := by
    intro ω
    have hxy : y + (x-y) = x := by abel
    simp only [hxy, Pi.sub_apply]
    ring
  simp_rw [he] at h
  have hsub := integral_sub ((hp x x i j).sub (hp x y i j))
    ((hp y x i j).sub (hp y y i j))
  have hsub₁ := integral_sub (hp x x i j) (hp x y i j)
  have hsub₂ := integral_sub (hp y x i j) (hp y y i j)
  simp only [Pi.sub_apply] at hsub hsub₁ hsub₂
  rw [hsub, hsub₁, hsub₂] at h
  linarith only [h]


/-- A jointly measurable corrector at an independent square-integrable endpoint. -/
@[nolint unusedArguments]
theorem physical_corrector_l2_at_independent_endpoint
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (K : ℝ) (hK : 0 ≤ K)
    (hχL2 : ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ K*euclideanNorm x^2)
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : Vec d => euclideanNorm x) 2 ν) :
    MemLp (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2))
      2 ((ReductionImageV3.physicalReferenceLaw Q).prod ν) ∧
    (∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
      ∂ ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) ≤
      K*(∫ x : Vec d, euclideanNorm x^2 ∂ ν) := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    have hs : Continuous (fun x : Vec d => ∑ i, x i * x i) := by
      apply continuous_finset_sum
      intro i _
      exact (continuous_apply i).mul (continuous_apply i)
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp hs
  have hm : Measurable (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)) :=
    hc.measurable.comp (hχ.comp (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd))
  have hs : Integrable (fun x : Vec d => euclideanNorm x ^ 2) ν := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hν.integrable_norm_pow (by decide : 2 ≠ 0)
  have hi (x : Vec d) : Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω x)^2)
      (physicalReferenceLaw Q) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      (hχmem x).integrable_norm_pow (by decide : 2 ≠ 0)
  have hm2 := hm.pow_const 2
  have hinner : Integrable (fun x : Vec d =>
      ∫ ω : PhysicalField d L, ‖euclideanNorm (χ ω x)^2‖ ∂ physicalReferenceLaw Q) ν := by
    apply (hs.const_mul K).mono' (hm2.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_sq]
    apply abs_le.mpr
    constructor
    · exact le_trans (neg_nonpos.mpr (mul_nonneg hK (sq_nonneg _)))
        (integral_nonneg fun ω => sq_nonneg _)
    · exact hχL2 x
  have hp : Integrable (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)^2)
      ((physicalReferenceLaw Q).prod ν) :=
    (integrable_prod_iff' hm2.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hi, hinner⟩
  constructor
  · apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num) (by norm_num)).1
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
      sq_abs] using hp
  · rw [integral_prod_symm _ hp, ← integral_const_mul]
    apply integral_mono_ae hp.integral_prod_right (hs.const_mul K)
    exact Filter.Eventually.of_forall hχL2

/-- An L² corrector estimate for a joint law dominated by a product law. -/
theorem physical_corrector_l2_under_product_law_domination
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (K : ℝ) (hK : 0 ≤ K)
    (hχL2 : ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ K*euclideanNorm x^2)
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : Vec d => euclideanNorm x) 2 ν)
    (A : ℝ) (hA : 0 ≤ A)
    (ρ : Measure (PhysicalField d L × Vec d))
    (hdom : ρ ≤ ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) :
    MemLp (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)) 2 ρ ∧
    (∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2 ∂ ρ) ≤
      A*K*(∫ x : Vec d, euclideanNorm x^2 ∂ ν) := by
  obtain ⟨hp, hb⟩ := physical_corrector_l2_at_independent_endpoint Q χ hχ K hK hχL2 hχmem ν hν
  have hi : Integrable (fun z : PhysicalField d L × Vec d =>
      euclideanNorm (χ z.1 z.2)^2)
      ((ReductionImageV3.physicalReferenceLaw Q).prod ν) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hp.integrable_norm_pow (by decide : 2 ≠ 0)
  constructor
  · exact hp.of_measure_le_smul ENNReal.ofReal_ne_top hdom
  · calc
      _ ≤ ∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
          ∂ (ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) :=
        integral_mono_measure hdom (Filter.Eventually.of_forall fun z => sq_nonneg _)
          (hi.smul_measure ENNReal.ofReal_ne_top)
      _ = A * (∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
          ∂ ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
      _ ≤ A*K*(∫ x : Vec d, euclideanNorm x^2 ∂ ν) := by
        exact (mul_le_mul_of_nonneg_left hb hA).trans_eq (mul_assoc _ _ _).symm


/-- The dominated joint-law estimate transported to the original sample space. -/
theorem physical_corrector_l2_at_dominated_sample_endpoint
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (K : ℝ) (hK : 0 ≤ K)
    (hχL2 : ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ K*euclideanNorm x^2)
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : Vec d => euclideanNorm x) 2 ν)
    (A : ℝ) (hA : 0 ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Ω → PhysicalField d L) (he : Measurable e)
    (X : Ω → Vec d) (hX : Measurable X)
    (hdom : Measure.map (fun ω => (e ω, X ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) :
    MemLp (fun ω => euclideanNorm (χ (e ω) (X ω))) 2 μ ∧
    (∫ ω, euclideanNorm (χ (e ω) (X ω))^2 ∂μ) ≤
      A*K*(∫ x : Vec d, euclideanNorm x^2 ∂ν) := by
  have hm : Measurable (fun ω => (e ω, X ω)) := he.prodMk hX
  obtain ⟨hp, hb⟩ := physical_corrector_l2_under_product_law_domination
    Q χ hχ K hK hχL2 hχmem ν hν A hA _ hdom
  have hi : Integrable (fun z : PhysicalField d L × Vec d =>
      euclideanNorm (χ z.1 z.2)^2) (Measure.map (fun ω => (e ω, X ω)) μ) := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      hp.integrable_norm_pow (by decide : 2 ≠ 0)
  constructor
  · exact hp.comp_of_map hm.aemeasurable
  · rw [← integral_map hm.aemeasurable hi.aestronglyMeasurable]
    exact hb


/-- A corrector increment between two endpoints with dominated joint laws. -/
theorem physical_corrector_increment_l2_at_two_dominated_sample_endpoints
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (K : ℝ) (hK : 0 ≤ K)
    (hχL2 : ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ K*euclideanNorm x^2)
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (ν : Measure (Vec d)) [IsProbabilityMeasure ν]
    (hν : MemLp (fun x : Vec d => euclideanNorm x) 2 ν)
    (A : ℝ) (hA : 0 ≤ A)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (e : Ω → PhysicalField d L) (he : Measurable e)
    (X : Ω → Vec d) (hX : Measurable X)
    (Z : Ω → Vec d) (hZ : Measurable Z)
    (hdomZ : Measure.map (fun ω => (e ω, Z ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod ν))
    (hdom : Measure.map (fun ω => (e ω, X ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod ν)) :
    MemLp (fun ω => euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω))) 2 μ ∧
    (∫ ω, euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω))^2 ∂μ) ≤
      4*A*K*(∫ x : Vec d, euclideanNorm x^2 ∂ν) := by
  obtain ⟨hx, bx⟩ := physical_corrector_l2_at_dominated_sample_endpoint
    Q χ hχ K hK hχL2 hχmem ν hν A hA μ e he X hX hdom
  obtain ⟨hz, bz⟩ := physical_corrector_l2_at_dominated_sample_endpoint
    Q χ hχ K hK hχL2 hχmem ν hν A hA μ e he Z hZ hdomZ
  have hmX : Measurable (fun ω => χ (e ω) (X ω)) :=
    hχ.comp ((measurable_subtype_coe.comp he).prodMk hX)
  have hmZ : Measurable (fun ω => χ (e ω) (Z ω)) :=
    hχ.comp ((measurable_subtype_coe.comp he).prodMk hZ)
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have ht (ω : Ω) : euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω)) ≤
      euclideanNorm (χ (e ω) (X ω)) + euclideanNorm (χ (e ω) (Z ω)) := by
    rw [sub_eq_add_neg]
    have hn := TimeChange.euclideanNorm_smul (-1 : ℝ) (χ (e ω) (Z ω))
    have hn' : euclideanNorm (-χ (e ω) (Z ω)) = euclideanNorm (χ (e ω) (Z ω)) := by
      simpa using hn
    simpa only [hn'] using TimeChange.euclideanNorm_add_le (χ (e ω) (X ω)) (-χ (e ω) (Z ω))
  have hi : MemLp (fun ω => euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω))) 2 μ := by
    apply (hx.add hz).mono' (hc.measurable.comp (hmX.sub hmZ)).aestronglyMeasurable
    filter_upwards with ω
    change |euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω))| ≤
      euclideanNorm (χ (e ω) (X ω)) + euclideanNorm (χ (e ω) (Z ω))
    have hn : 0 ≤ euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω)) :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg hn]
    exact ht ω
  have ix : Integrable (fun ω => euclideanNorm (χ (e ω) (X ω))^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hx.integrable_norm_pow (by decide : 2 ≠ 0)
  have iz : Integrable (fun ω => euclideanNorm (χ (e ω) (Z ω))^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hz.integrable_norm_pow (by decide : 2 ≠ 0)
  have ii : Integrable (fun ω => euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω))^2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hi.integrable_norm_pow (by decide : 2 ≠ 0)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, (2 * euclideanNorm (χ (e ω) (X ω))^2 +
        2 * euclideanNorm (χ (e ω) (Z ω))^2) ∂μ := by
      apply integral_mono_ae ii ((ix.const_mul 2).add (iz.const_mul 2))
      filter_upwards with ω
      dsimp only [Pi.add_apply]
      have h1 := ht ω
      have h2 := Real.sqrt_nonneg (euclideanSq (χ (e ω) (X ω) - χ (e ω) (Z ω)))
      have h3 := Real.sqrt_nonneg (euclideanSq (χ (e ω) (X ω)))
      have h4 := Real.sqrt_nonneg (euclideanSq (χ (e ω) (Z ω)))
      change 0 ≤ euclideanNorm (χ (e ω) (X ω) - χ (e ω) (Z ω)) at h2
      change 0 ≤ euclideanNorm (χ (e ω) (X ω)) at h3
      change 0 ≤ euclideanNorm (χ (e ω) (Z ω)) at h4
      nlinarith [sq_nonneg (euclideanNorm (χ (e ω) (X ω)) - euclideanNorm (χ (e ω) (Z ω)))]
    _ = 2 * (∫ ω, euclideanNorm (χ (e ω) (X ω))^2 ∂μ) +
        2 * (∫ ω, euclideanNorm (χ (e ω) (Z ω))^2 ∂μ) := by
      rw [integral_add (ix.const_mul 2) (iz.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ 4*A*K*(∫ x : Vec d, euclideanNorm x^2 ∂ν) := by nlinarith [bx, bz]

/-- Mean sublinearity yields a vanishing scaled endpoint remainder under joint-law domination. -/
@[nolint unusedArguments]
theorem physical_corrector_scaled_endpoint_l2_of_mean_sublinearity
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ (ReductionImageV3.physicalReferenceLaw Q)) ≤ C + ε*euclideanNorm x^2)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Ω → PhysicalField d L) (he : Measurable e)
    (X : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n))
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (ν : ℕ → Measure (Vec d)) (hνprob : ∀ n, IsProbabilityMeasure (ν n))
    (hν : ∀ n, MemLp (fun x : Vec d => euclideanNorm x) 2 (ν n))
    (M : ℝ) (hM : 0 ≤ M)
    (hmom : ∀ n, (∫ x : Vec d, euclideanNorm x^2 ∂ (ν n)) ≤ M*(ρ n)^2)
    (A : ℝ) (hA : 0 ≤ A)
    (hdom : ∀ n, Measure.map (fun ω => (e ω, X n ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod (ν n))) :
    (∀ n, MemLp (fun ω => euclideanNorm (χ (e ω) (X n ω))/ρ n) 2 μ) ∧
    Tendsto (fun n => ∫ ω, (euclideanNorm (χ (e ω) (X n ω))/ρ n)^2 ∂ μ)
      atTop (𝓝 0) := by
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hm : Measurable (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)) :=
    hc.measurable.comp (hχ.comp (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd))
  have hb (ε : ℝ) (hε : 0 < ε) (C : ℝ) (hC : 0 ≤ C)
      (hbound : ∀ x : Vec d, (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ (physicalReferenceLaw Q)) ≤ C + ε * euclideanNorm x^2) (n : ℕ) :
      MemLp (fun ω => euclideanNorm (χ (e ω) (X n ω))) 2 μ ∧
      (∫ ω, euclideanNorm (χ (e ω) (X n ω))^2 ∂ μ) ≤
        A * (C + ε * (∫ x, euclideanNorm x^2 ∂ (ν n))) := by
    letI := hνprob n
    have hs : Integrable (fun x : Vec d => euclideanNorm x ^ 2) (ν n) := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (hν n).integrable_norm_pow (by decide : 2 ≠ 0)
    have hi (x : Vec d) : Integrable (fun ω : PhysicalField d L => euclideanNorm (χ ω x)^2)
        (physicalReferenceLaw Q) := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (hχmem x).integrable_norm_pow (by decide : 2 ≠ 0)
    have hm2 := hm.pow_const 2
    have hmajor : Integrable (fun x : Vec d => C + ε * euclideanNorm x^2) (ν n) :=
      integrable_const C |>.add (hs.const_mul ε)
    have hinner : Integrable (fun x : Vec d =>
        ∫ ω : PhysicalField d L, ‖euclideanNorm (χ ω x)^2‖ ∂ (physicalReferenceLaw Q)) (ν n) := by
      apply hmajor.mono' (hm2.norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable
      filter_upwards with x
      simp only [Real.norm_eq_abs, abs_sq]
      apply abs_le.mpr
      constructor
      · exact le_trans (neg_nonpos.mpr (add_nonneg hC (mul_nonneg hε.le (sq_nonneg _))))
          (integral_nonneg fun ω => sq_nonneg _)
      · exact hbound x
    have hp : Integrable (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)^2)
        ((physicalReferenceLaw Q).prod (ν n)) :=
      (integrable_prod_iff' hm2.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hi, hinner⟩
    have hpb : (∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
        ∂ ((physicalReferenceLaw Q).prod (ν n))) ≤ C + ε * (∫ x, euclideanNorm x^2 ∂ (ν n)) := by
      rw [integral_prod_symm _ hp]
      calc
        _ ≤ ∫ x, (C + ε * euclideanNorm x^2) ∂ (ν n) :=
          integral_mono_ae hp.integral_prod_right hmajor (Filter.Eventually.of_forall hbound)
        _ = _ := by rw [integral_add (integrable_const C) (hs.const_mul ε), integral_const_mul]; simp
    have hmap : Measurable (fun ω => (e ω, X n ω)) := he.prodMk (hX n)
    have hpm : MemLp (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2))
        2 ((physicalReferenceLaw Q).prod (ν n)) := by
      apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num) (by norm_num)).1
      simpa only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hp
    have hmapmem := hpm.of_measure_le_smul ENNReal.ofReal_ne_top (hdom n)
    have hmapint : Integrable (fun z : PhysicalField d L × Vec d => euclideanNorm (χ z.1 z.2)^2)
        (Measure.map (fun ω => (e ω, X n ω)) μ) := by
      simpa only [Real.norm_eq_abs, sq_abs] using hmapmem.integrable_norm_pow (by decide : 2 ≠ 0)
    refine ⟨hmapmem.comp_of_map hmap.aemeasurable, ?_⟩
    rw [← integral_map hmap.aemeasurable hmapint.aestronglyMeasurable]
    calc
      _ ≤ ∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
          ∂ (ENNReal.ofReal A • ((physicalReferenceLaw Q).prod (ν n))) :=
        integral_mono_measure (hdom n) (Filter.Eventually.of_forall fun z => sq_nonneg _)
          (hp.smul_measure ENNReal.ofReal_ne_top)
      _ = A * (∫ z : PhysicalField d L × Vec d, euclideanNorm (χ z.1 z.2)^2
          ∂ ((physicalReferenceLaw Q).prod (ν n))) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hA, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hpb hA
  obtain ⟨C₀, hC₀, hbound₀⟩ := hsub 1 zero_lt_one
  have hmem (n : ℕ) := (hb 1 zero_lt_one C₀ hC₀ hbound₀ n).1
  constructor
  · intro n
    simpa only [div_eq_mul_inv] using (hmem n).mul_const (ρ n)⁻¹
  · apply tendsto_order.2
    constructor
    · intro a ha
      exact Eventually.of_forall fun n => lt_of_lt_of_le ha (integral_nonneg fun ω => sq_nonneg _)
    · intro b hbpos
      let ε := b / (2 * (A * M + 1))
      have hε : 0 < ε := by dsimp [ε]; positivity
      obtain ⟨C, hC, hbound⟩ := hsub ε hε
      have hinv : Tendsto (fun n => (ρ n)⁻¹ ^ 2) atTop (𝓝 0) := by
        simpa using (tendsto_inv_atTop_zero.comp hρ).pow 2
      have ht : Tendsto (fun n => (A*C) * (ρ n)⁻¹ ^ 2) atTop (𝓝 0) := by
        simpa using hinv.const_mul (A*C)
      have hev := ht.eventually (gt_mem_nhds (half_pos hbpos))
      filter_upwards [hev] with n hn
      have hbn := (hb ε hε C hC hbound n).2
      have hr : 0 < (ρ n)^2 := sq_pos_of_pos (hρpos n)
      have hmoment := hmom n
      have hprod : ε * A * M < b / 2 := by
        have hd : 0 < 2 * (A * M + 1) := by positivity
        dsimp [ε]
        rw [show b / (2 * (A * M + 1)) * A * M =
          (b * (A * M)) / (2 * (A * M + 1)) by ring]
        apply (div_lt_iff₀ hd).2
        nlinarith
      have hscaled : (∫ ω, (euclideanNorm (χ (e ω) (X n ω))/ρ n)^2 ∂ μ) =
          (∫ ω, euclideanNorm (χ (e ω) (X n ω))^2 ∂ μ) / (ρ n)^2 := by
        simp_rw [div_pow, integral_div]
      rw [hscaled]
      have hest : (∫ ω, euclideanNorm (χ (e ω) (X n ω))^2 ∂ μ) / (ρ n)^2 ≤
          A*C / (ρ n)^2 + A*ε*M := by
        have hm' := mul_le_mul_of_nonneg_left hmoment (mul_nonneg hA hε.le)
        apply (div_le_iff₀ hr).2
        field_simp [ne_of_gt (hρpos n)]
        nlinarith
      have hn' : A*C / (ρ n)^2 < b / 2 := by simpa [div_eq_mul_inv, inv_pow] using hn
      nlinarith


/-- Mean sublinearity controls the scaled corrector increment at two dominated endpoints. -/
theorem physical_corrector_scaled_increment_l2_of_mean_sublinearity
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ C + ε*euclideanNorm x^2)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Ω → PhysicalField d L) (he : Measurable e)
    (X : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n))
    (Z : ℕ → Ω → Vec d) (hZ : ∀ n, Measurable (Z n))
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (ν : ℕ → Measure (Vec d)) (hνprob : ∀ n, IsProbabilityMeasure (ν n))
    (hν : ∀ n, MemLp (fun x : Vec d => euclideanNorm x) 2 (ν n))
    (M : ℝ) (hM : 0 ≤ M)
    (hmom : ∀ n, (∫ x : Vec d, euclideanNorm x^2 ∂ν n) ≤ M*(ρ n)^2)
    (A : ℝ) (hA : 0 ≤ A)
    (hdom : ∀ n, Measure.map (fun ω => (e ω, X n ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod (ν n)))
    (hdomZ : ∀ n, Measure.map (fun ω => (e ω, Z n ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod (ν n))) :
    (∀ n, MemLp (fun ω => euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω))/ρ n) 2 μ) ∧
    Tendsto (fun n => ∫ ω, (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω))/ρ n)^2 ∂μ)
      atTop (𝓝 0) := by
  obtain ⟨hx, tx⟩ := physical_corrector_scaled_endpoint_l2_of_mean_sublinearity
    Q χ hχ hχmem hsub μ e he X hX ρ hρpos hρ ν hνprob hν M hM hmom A hA hdom
  obtain ⟨hz, tz⟩ := physical_corrector_scaled_endpoint_l2_of_mean_sublinearity
    Q χ hχ hχmem hsub μ e he Z hZ ρ hρpos hρ ν hνprob hν M hM hmom A hA hdomZ
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have ht (n : ℕ) (ω : Ω) :
      euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n ≤
        euclideanNorm (χ (e ω) (X n ω)) / ρ n +
          euclideanNorm (χ (e ω) (Z n ω)) / ρ n := by
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (hρpos n).le
    rw [sub_eq_add_neg]
    have hn := TimeChange.euclideanNorm_smul (-1 : ℝ) (χ (e ω) (Z n ω))
    have hn' : euclideanNorm (-χ (e ω) (Z n ω)) = euclideanNorm (χ (e ω) (Z n ω)) := by
      simpa using hn
    simpa only [hn'] using TimeChange.euclideanNorm_add_le (χ (e ω) (X n ω)) (-χ (e ω) (Z n ω))
  have hi (n : ℕ) : MemLp (fun ω =>
      euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n) 2 μ := by
    have hmX : Measurable (fun ω => χ (e ω) (X n ω)) :=
      hχ.comp ((measurable_subtype_coe.comp he).prodMk (hX n))
    have hmZ : Measurable (fun ω => χ (e ω) (Z n ω)) :=
      hχ.comp ((measurable_subtype_coe.comp he).prodMk (hZ n))
    apply ((hx n).add (hz n)).mono'
      (((hc.measurable.comp (hmX.sub hmZ)).div_const (ρ n)).aestronglyMeasurable)
    filter_upwards with ω
    change |euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n| ≤
      euclideanNorm (χ (e ω) (X n ω)) / ρ n + euclideanNorm (χ (e ω) (Z n ω)) / ρ n
    have hn : 0 ≤ euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) :=
      Real.sqrt_nonneg _
    rw [abs_of_nonneg (div_nonneg hn (hρpos n).le)]
    exact ht n ω
  refine ⟨hi, ?_⟩
  apply squeeze_zero (g := fun n =>
    2 * (∫ ω, (euclideanNorm (χ (e ω) (X n ω)) / ρ n)^2 ∂μ) +
    2 * (∫ ω, (euclideanNorm (χ (e ω) (Z n ω)) / ρ n)^2 ∂μ))
    (fun n => integral_nonneg fun ω => sq_nonneg _) ?_ ?_
  · intro n
    have ix := (hx n).integrable_norm_pow (by decide : 2 ≠ 0)
    have iz := (hz n).integrable_norm_pow (by decide : 2 ≠ 0)
    have ii := (hi n).integrable_norm_pow (by decide : 2 ≠ 0)
    simp only [Real.norm_eq_abs, sq_abs] at ix iz ii
    calc
      _ ≤ ∫ ω, (2 * (euclideanNorm (χ (e ω) (X n ω)) / ρ n)^2 +
          2 * (euclideanNorm (χ (e ω) (Z n ω)) / ρ n)^2) ∂μ := by
        apply integral_mono_ae ii ((ix.const_mul 2).add (iz.const_mul 2))
        filter_upwards with ω
        dsimp only [Pi.add_apply]
        have h1 := ht n ω
        have h2 : 0 ≤ euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n :=
          div_nonneg (Real.sqrt_nonneg _) (hρpos n).le
        have h3 : 0 ≤ euclideanNorm (χ (e ω) (X n ω)) / ρ n :=
          div_nonneg (Real.sqrt_nonneg _) (hρpos n).le
        have h4 : 0 ≤ euclideanNorm (χ (e ω) (Z n ω)) / ρ n :=
          div_nonneg (Real.sqrt_nonneg _) (hρpos n).le
        nlinarith [sq_nonneg (euclideanNorm (χ (e ω) (X n ω)) / ρ n -
          euclideanNorm (χ (e ω) (Z n ω)) / ρ n)]
      _ = 2 * (∫ ω, (euclideanNorm (χ (e ω) (X n ω)) / ρ n)^2 ∂μ) +
          2 * (∫ ω, (euclideanNorm (χ (e ω) (Z n ω)) / ρ n)^2 ∂μ) := by
        rw [integral_add (ix.const_mul 2) (iz.const_mul 2), integral_const_mul, integral_const_mul]
  · simpa using (tx.const_mul 2).add (tz.const_mul 2)

/-- Mean sublinearity yields convergence in probability of scaled increments. -/
theorem physical_corrector_scaled_increment_in_probability_of_mean_sublinearity
    {d : ℕ} [Fact (2 ≤ d)] {L r : ℝ} (Q : EnvironmentLaw d L r)
    (χ : FieldPair d → Vec d → Vec d)
    (hχ : Measurable (fun z : FieldPair d × Vec d => χ z.1 z.2))
    (hχmem : ∀ x : Vec d, MemLp (fun ω : PhysicalField d L =>
      euclideanNorm (χ ω x)) 2 (ReductionImageV3.physicalReferenceLaw Q))
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Vec d,
      (∫ ω : PhysicalField d L, euclideanNorm (χ ω x)^2
        ∂ ReductionImageV3.physicalReferenceLaw Q) ≤ C + ε*euclideanNorm x^2)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (e : Ω → PhysicalField d L) (he : Measurable e)
    (X : ℕ → Ω → Vec d) (hX : ∀ n, Measurable (X n))
    (Z : ℕ → Ω → Vec d) (hZ : ∀ n, Measurable (Z n))
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (ν : ℕ → Measure (Vec d)) (hνprob : ∀ n, IsProbabilityMeasure (ν n))
    (hν : ∀ n, MemLp (fun x : Vec d => euclideanNorm x) 2 (ν n))
    (M : ℝ) (hM : 0 ≤ M)
    (hmom : ∀ n, (∫ x : Vec d, euclideanNorm x^2 ∂ν n) ≤ M*(ρ n)^2)
    (A : ℝ) (hA : 0 ≤ A)
    (hdom : ∀ n, Measure.map (fun ω => (e ω, X n ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod (ν n)))
    (hdomZ : ∀ n, Measure.map (fun ω => (e ω, Z n ω)) μ ≤
      ENNReal.ofReal A • ((ReductionImageV3.physicalReferenceLaw Q).prod (ν n))) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => μ {ω | ε <
        euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω))/ρ n}) atTop (𝓝 0) := by
  obtain ⟨hi, ht⟩ := physical_corrector_scaled_increment_l2_of_mean_sublinearity
    Q χ hχ hχmem hsub μ e he X hX Z hZ ρ hρpos hρ ν hνprob hν M hM hmom A hA hdom hdomZ
  intro ε hε
  rw [← ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)]
  apply squeeze_zero (g := fun n =>
    (∫ ω, (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n)^2 ∂μ) / ε^2)
    (fun n => ENNReal.toReal_nonneg) ?_ ?_
  · intro n
    have hint := (hi n).integrable_norm_pow (by decide : 2 ≠ 0)
    simp only [Real.norm_eq_abs, sq_abs] at hint
    have hm := mul_meas_ge_le_integral_of_nonneg
      (μ := μ) (f := fun ω => (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n)^2)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hint (ε^2)
    have hset : {ω | ε < euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n} ⊆
        {ω | ε^2 ≤ (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n)^2} := by
      intro ω hω
      change ε < euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n at hω
      change ε^2 ≤ (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n)^2
      simpa only [pow_two] using mul_self_le_mul_self hε.le hω.le
    have hmeasure : μ.real {ω | ε < euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n} ≤
        μ.real {ω | ε^2 ≤ (euclideanNorm (χ (e ω) (X n ω) - χ (e ω) (Z n ω)) / ρ n)^2} :=
      measureReal_mono hset
    change μ.real _ ≤ _
    apply (le_div_iff₀ (sq_pos_of_pos hε)).2
    nlinarith
  · simpa using ht.div_const (ε^2)

end EinsteinFull
