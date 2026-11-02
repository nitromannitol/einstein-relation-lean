import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinRelation.Environment.EuclideanLipschitz
import PDEFoundation.Measure.MatrixPerturbationProbabilityAverage
import PDEFoundation.Measure.BallVolume
import PDEFoundation.Sobolev.Mean
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof
import EllipticRegularity.CalderonZygmund.NegativeSobolevInterior
import PDEFoundation.PDE.DGNM.Scaling
import EinsteinFull.Calculus.LocalEnergySupport
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import PDEFoundation.Measure.LpPower

/-! Actual finite-moment production for the clock value and uniform L2
gradient bounds on the parabolic force disc. Higher gradient moments are
still needed for the shared finite-p gradient/flux contract. -/

open MeasureTheory Filter
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- One structural constant controls every moment of the actual clock datum. -/
theorem clock_observation_uniform_moments
    (d : ℕ) (D : StructuralData d) :
    ∃ L : ℝ, 0 < L ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ p : ℝ≥0∞, eLpNorm μ p (reducedLaw Q) ≤ ENNReal.ofReal L := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨L, zero_lt_one.trans_le hL, ?_⟩
  intro Q μ hμ p
  let := reducedLaw_probability Q
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ L := by
    filter_upwards [hμ, (hb d D.dependenceRange Q).2.2] with ω hω hbounds
    rw [hω, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hbounds.2.1 0).1)]
    exact (hbounds.2.1 0).2
  simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
    (eLpNorm_le_of_ae_bound (p := p) (Lp.memLp μ).aestronglyMeasurable hbound)

/-- The actual W has entire finite-p representatives and bounded moments on
compact time/force sets, with its constant chosen before Q and the datum.
This proves the value estimate without assuming local moments. -/
theorem clock_value_finitep_on_compact_sets_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p A T : ℝ) (hp : 2 ≤ p) (hA : 0 < A) (hT : 0 < T) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∀ r : ℝ≥0, (r : ℝ) ≤ T →
    ∃ Wp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (∀ ζ, (Wp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        centeredComplexLp Q (P ζ r μ)) ∧
      (∀ ζ, AnalyticAt ℂ Wp ζ) ∧
      (∀ ζ, ‖ζ‖ ≤ A → ‖Wp ζ‖ ≤ C ∧
        MemLp (centeredComplexLp Q (P ζ r μ) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (centeredComplexLp Q (P ζ r μ) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal C) := by
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨L, hL, hdatum⟩ := clock_observation_uniform_moments d D
  obtain ⟨K, hK, hrep⟩ :=
    AnalyticClock.exists_centered_representatives h0 d hd D p A T hp hA hT
  refine ⟨K * L, mul_pos hK hL, ?_⟩
  intro Q hQ μ hμ P hP r hr
  obtain ⟨Wp, hae, han, hnorm⟩ := hrep Q hQ μ hμ P hP r hr
  have hμnorm : (eLpNorm μ (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ L := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hdatum Q μ hμ _)).trans_eq (ENNReal.toReal_ofReal hL.le)
  refine ⟨Wp, hae, han, ?_⟩
  intro ζ hζ
  have hn : ‖Wp ζ‖ ≤ K * L :=
    (hnorm ζ hζ).trans (mul_le_mul_of_nonneg_left hμnorm hK.le)
  refine ⟨hn, (Lp.memLp (Wp ζ)).ae_eq (hae ζ), ?_⟩
  rw [← eLpNorm_congr_ae (hae ζ), ← Lp.enorm_def, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal hn

/-- Local higher moments of the actual centered clock orbit are produced from
the permitted semigroup input, including at zero force and zero time. -/
theorem clock_value_local_moments_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (q : ℝ) (hq : 2 ≤ q)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (r : ℝ≥0) (z₀ : ℂ) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      ∀ z : ℂ, ‖z - z₀‖ < δ →
        MemLp (centeredComplexLp Q (P z r μ) : FieldPair d → ℂ)
          (ENNReal.ofReal q) (reducedLaw Q) ∧
        eLpNorm (centeredComplexLp Q (P z r μ) : FieldPair d → ℂ)
          (ENNReal.ofReal q) (reducedLaw Q) ≤ ENNReal.ofReal K := by
  obtain ⟨K, hK, hrep⟩ := clock_value_finitep_on_compact_sets_of_deps
    h0 d hd D q (‖z₀‖ + 1) ((r : ℝ) + 1) hq (by positivity) (by positivity)
  obtain ⟨Wp, _, _, hb⟩ := hrep Q hQ μ hμ P hP r (by linarith)
  refine ⟨1, K, zero_lt_one, hK.le, ?_⟩
  intro z hz
  have hnorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
    have h := norm_add_le (z - z₀) z₀
    rw [sub_add_cancel] at h
    linarith
  exact (hb z hnorm).2

/-- The quadratic force shift stays bounded after parabolic rescaling. -/
theorem clock_force_shift_on_parabolic_disc
    (d : ℕ) (Λ B : ℝ) (hΛ : 0 ≤ Λ) (ζ : ℂ) (r : ℝ≥0)
    (hdisc : ‖ζ‖ * Real.sqrt (r : ℝ) ≤ B) :
    complexForceShift d Λ ζ * (r : ℝ) ≤
      (Real.exp (2 * Λ) * Λ) *
        ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) ^ 2 * B ^ 2 := by
  let K := Real.exp (2 * Λ) * Λ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le hΛ
  calc
    complexForceShift d Λ ζ * (r : ℝ) =
        (K * ((d : ℝ) * K) ^ 2) * (‖ζ‖ * Real.sqrt (r : ℝ)) ^ 2 := by
      dsimp [complexForceShift, K]
      ring_nf
      congr 1
      exact (Real.sq_sqrt r.property).symm
    _ ≤ (K * ((d : ℝ) * K) ^ 2) * B ^ 2 :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) hdisc 2)
        (mul_nonneg hK (sq_nonneg _))

/-- The same canonical gradient used by the shared weak flux has uniform
rescaled L2 size on the root's force disc. Constants precede the law and datum;
there is no upper time cutoff and no assumed local gradient moment. -/
theorem clock_gradient_l2_on_parabolic_disc
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
      (ζ : ℂ) (r : ℝ≥0), 0 < r → ‖ζ‖ * Real.sqrt (r : ℝ) ≤ B →
    ∀ j : Fin d,
      Real.sqrt (r : ℝ) * ‖ClockAnalyticity.gradient
        (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j‖ ≤ C ∧
      (1 ≤ (r : ℝ) → ‖ClockAnalyticity.gradient
        (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j‖ ≤ C) := by
  obtain ⟨L, hL, hdatum⟩ := clock_observation_uniform_moments d D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let S := K * ((d : ℝ) * K) ^ 2 * B ^ 2
  let C := 2 * Real.sqrt K * Real.exp (65 * S) * L
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (zero_lt_one.trans_le D.one_le_ellipticity)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q μ hμ P hP ζ r hr hdisc j
  have hμnorm : ‖μ‖ ≤ L := by
    rw [Lp.norm_def]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hdatum Q μ hμ 2)).trans_eq (ENNReal.toReal_ofReal hL.le)
  have hsqrt : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hr)
  have hshift := clock_force_shift_on_parabolic_disc d D.ellipticity B
    (zero_le_one.trans D.one_le_ellipticity) ζ r hdisc
  have hexp : Real.exp (65 * complexForceShift d D.ellipticity ζ * (r : ℝ)) ≤
      Real.exp (65 * S) := by
    apply Real.exp_le_exp.mpr
    dsimp [S, K]
    nlinarith
  have hgradient : ‖ClockAnalyticity.gradient
      (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j‖ ≤
      (2 * Real.sqrt K / Real.sqrt (r : ℝ) *
        Real.exp (65 * complexForceShift d D.ellipticity ζ * (r : ℝ))) * ‖μ‖ := by
    simp only [ClockAnalyticity.gradient, dite_eq_left hr]
    exact (PiLp.norm_apply_le _ j).trans
      (((hP ζ).forcedGradient r hr).le_opNorm μ |>.trans
        (mul_le_mul_of_nonneg_right ((hP ζ).norm_forcedGradient_le r hr) (norm_nonneg μ)))
  have hrescaled : Real.sqrt (r : ℝ) * ‖ClockAnalyticity.gradient
      (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j‖ ≤ C := by
    calc
      _ ≤ Real.sqrt (r : ℝ) *
          ((2 * Real.sqrt K / Real.sqrt (r : ℝ) *
            Real.exp (65 * complexForceShift d D.ellipticity ζ * (r : ℝ))) * ‖μ‖) :=
        mul_le_mul_of_nonneg_left hgradient hsqrt.le
      _ = 2 * Real.sqrt K *
          Real.exp (65 * complexForceShift d D.ellipticity ζ * (r : ℝ)) * ‖μ‖ := by
        field_simp [hsqrt.ne']
      _ ≤ C := mul_le_mul
        (mul_le_mul_of_nonneg_left hexp (by positivity)) hμnorm
        (norm_nonneg μ) (by positivity)
  refine ⟨hrescaled, ?_⟩
  intro hrone
  have hsqrtone : 1 ≤ Real.sqrt (r : ℝ) := by
    simpa using Real.sqrt_le_sqrt hrone
  exact (le_mul_of_one_le_left (norm_nonneg _) hsqrtone).trans hrescaled

/-- The actual anisotropic flux has an L2 bound from its literal coefficient
multipliers. This keeps the canonical flux rather than selecting a new witness. -/
theorem clock_flux_l2_norm_le {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    ‖ClockAnalyticity.flux Q G j‖ ≤
      (2 * sourceReducedBound Λ) * ∑ k : Fin d, ‖G k‖ := by
  have hκ : 0 ≤ sourceReducedBound Λ := by
    unfold sourceReducedBound
    have := Q.ellipticity_parameter
    positivity
  have hentry (k : Fin d) :
      ‖(homogenizedCoefficient Q j k : ℂ)‖ ≤ sourceReducedBound Λ := by
    have hcoord (x : Vec d) : |x j| ≤ euclideanNorm x := by
      unfold euclideanNorm euclideanSq dot
      rw [← Real.sqrt_sq_eq_abs (x j)]
      apply Real.sqrt_le_sqrt
      simpa only [pow_two] using!
        (Finset.single_le_sum (fun l _ => mul_self_nonneg (x l)) (Finset.mem_univ j))
    have h := (hcoord ((homogenizedCoefficient Q).mulVec (unitVector k))).trans
      (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
    simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
      Complex.norm_real, Real.norm_eq_abs] using! h
  have hmul (k : Fin d) :
      ‖complexCoefficientMul Q j k (G k)‖ ≤ sourceReducedBound Λ * ‖G k‖ := by
    apply ((complexCoefficientMul Q j k).le_opNorm (G k)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply (norm_complexCoefficientMul_le Q j k).trans
    unfold sourceReducedBound
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg Λ]) (Real.exp_pos _).le
  unfold ClockAnalyticity.flux
  calc
    _ ≤ ∑ k : Fin d, ‖complexCoefficientMul Q j k (G k) -
          (homogenizedCoefficient Q j k : ℂ) • G k‖ := norm_sum_le _ _
    _ ≤ ∑ k : Fin d, (2 * sourceReducedBound Λ) * ‖G k‖ := by
      apply Finset.sum_le_sum
      intro k _
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      have h := add_le_add (hmul k)
        (mul_le_mul_of_nonneg_right (hentry k) (norm_nonneg (G k)))
      nlinarith
    _ = _ := (Finset.mul_sum ..).symm

/-- The same shared clock flux inherits the uniform parabolic-disc L2 estimate,
with its structural constant chosen before the environment law. -/
theorem clock_flux_l2_on_parabolic_disc
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
      (ζ : ℂ) (r : ℝ≥0), 1 ≤ (r : ℝ) → ‖ζ‖ * Real.sqrt (r : ℝ) ≤ B →
    ∀ j : Fin d,
      ‖ClockAnalyticity.flux Q (ClockAnalyticity.gradient
        (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) j‖ ≤ C := by
  obtain ⟨C, hC, hgrad⟩ := clock_gradient_l2_on_parabolic_disc d hd D B
  let κ := sourceReducedBound D.ellipticity
  have hκ : 0 < κ := by
    dsimp [κ, sourceReducedBound]
    have := D.one_le_ellipticity
    positivity
  refine ⟨(2 * κ) * ((d : ℝ) * C), by positivity, ?_⟩
  intro Q μ hμ P hP ζ r hr hdisc j
  have hrpos : 0 < r := by exact_mod_cast (zero_lt_one.trans_le hr)
  apply (clock_flux_l2_norm_le Q _ j).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 2 * κ)
  calc
    _ ≤ ∑ _k : Fin d, C := Finset.sum_le_sum fun k _ =>
      (hgrad Q μ hμ P hP ζ r hrpos hdisc k).2 hr
    _ = (d : ℝ) * C := by simp

section InitialGenerator
variable {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}

private def c15_coordinateDirections : (cs : List (Fin d)) → Fin cs.length → Vec d
  | [] => Fin.elim0
  | k :: cs => Fin.cons (unitVector k) (c15_coordinateDirections cs)

private theorem c15_coordinateIterate_eq {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) (x : Vec d) :
    coordinateIterate cs f x =
      iteratedFDeriv ℝ cs.length f x (c15_coordinateDirections cs) := by
  induction cs generalizing x with
  | nil => simp [coordinateIterate, iteratedFDeriv_zero_apply]
  | cons k cs ih =>
    have he : coordinateIterate cs f = fun y =>
        iteratedFDeriv ℝ cs.length f y (c15_coordinateDirections cs) := funext ih
    simp only [coordinateIterate, List.length_cons, c15_coordinateDirections,
      iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rw [he]
    exact fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (m := cs.length) (by
        exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _)) x) _ _

private theorem c15_euclidean_unit (k : Fin d) :
    euclideanNorm (unitVector k) = 1 := by
  change Real.sqrt (dotProduct (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem c15_directions_norm (cs : List (Fin d))
    (k : Fin cs.length) : euclideanNorm (c15_coordinateDirections cs k) = 1 := by
  induction cs with
  | nil => exact Fin.elim0 k
  | cons j cs ih =>
    refine Fin.cases ?_ (fun l => ?_) k
    · exact c15_euclidean_unit j
    · exact ih l

private theorem c15_jet_bound {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hω : IsSmoothWithBounds M ω) (cs : List (Fin d)) (hcs : 1 ≤ cs.length)
    (x : Vec d) : |coordinateIterate cs (fun y => ω.2 y) x| ≤ M cs.length := by
  obtain ⟨A, B, hA, _, hAB, _, hB⟩ := hω.2 cs.length hcs
  rw [c15_coordinateIterate_eq hω.1.2]
  have hb := hB x (c15_coordinateDirections cs)
  simp only [c15_directions_norm, Finset.prod_const_one, mul_one] at hb
  exact hb.trans (by linarith)

private theorem c15_memLp_top (Q : EnvironmentLaw d Λ r) :
    MemLp (fun ω : FieldPair d => ω.2 0) ∞ (reducedLaw Q) := by
  apply memLp_top_of_bound (by fun_prop) (Real.exp (2 * Λ))
  apply (ae_map_iff Probability.measurable_reduce.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [Q.regular] with ω hω
  have h := clockDensity_bounds ω 0 Λ (hω.2.1 0)
  change ‖clockDensity ω 0‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_pos (clockDensity_pos ω 0)] using h.2

private theorem c15_coefficient_jet_bound {M : ℕ → ℝ} {ω : FieldPair d}
    (hω : IsSmoothWithBounds M ω) (cs : List (Fin d)) (hcs : 1 ≤ cs.length)
    (j k : Fin d) (x : Vec d) :
    |coordinateIterate cs (fun y => ω.1 y j k) x| ≤ M cs.length := by
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hω.2 cs.length hcs
  rw [c15_coordinateIterate_eq (hω.1.1 j k)]
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => iteratedFDeriv ℝ cs.length
      (fun y => ω.1 y j k) x (c15_coordinateDirections cs)) (unitVector k)) j
  have hb := hA x (c15_coordinateDirections cs) (unitVector k)
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun l => N j l) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  simp only [c15_directions_norm, Finset.prod_const_one,
    c15_euclidean_unit, mul_one] at hb
  exact (hc.trans hb).trans (by linarith)

private theorem c15_clock_jet_curve {ω : FieldPair d} {M : ℕ → ℝ}
    (hω : IsSmoothWithBounds M ω) (l : Fin d) (cs : List (Fin d)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedHorizontalDerivative cs
      (fun η : FieldPair d => η.2 0) (translate (t • unitVector l) ω))
      (iteratedHorizontalDerivative (l :: cs)
        (fun η : FieldPair d => η.2 0) (translate (s • unitVector l) ω)) s := by
  let f := iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0)
  have horbit : orbit f ω = coordinateIterate cs (fun y => ω.2 y) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_scalar, add_zero]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
    rw [horbit]
    exact contDiff_coordinateIterate hω.1.2 cs
  have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
    s ((hasDerivAt_id' s).smul_const (unitVector l))
  change HasDerivAt (fun t => orbit f ω (t • unitVector l))
    (horizontalDerivative l f (translate (s • unitVector l) ω)) s
  rw [horizontalDerivative_translate]
  simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd


private def c15_generatorPairing (f : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 f

private theorem c15_generatorPairing_apply (f g : Lp ℂ 2 (reducedLaw Q)) :
    c15_generatorPairing f g = ∫ ω, f ω * g ω ∂reducedLaw Q := by
  rw [c15_generatorPairing, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

private theorem c15_coefficient_jet_curve {ω : FieldPair d} {M : ℕ → ℝ}
    (hω : IsSmoothWithBounds M ω) (j k l : Fin d) (cs : List (Fin d)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedHorizontalDerivative cs
      (fun η : FieldPair d => η.1 0 j k) (translate (t • unitVector l) ω))
      (iteratedHorizontalDerivative (l :: cs)
        (fun η : FieldPair d => η.1 0 j k) (translate (s • unitVector l) ω)) s := by
  let f := iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k)
  have horbit : orbit f ω = coordinateIterate cs (fun y => ω.1 y j k) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_matrix, add_zero]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
    rw [horbit]
    exact contDiff_coordinateIterate (hω.1.1 j k) cs
  have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
    s ((hasDerivAt_id' s).smul_const (unitVector l))
  change HasDerivAt (fun t => orbit f ω (t • unitVector l))
    (horizontalDerivative l f (translate (s • unitVector l) ω)) s
  rw [horizontalDerivative_translate]
  simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd

private theorem c15_clock_jet_products {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs bs : List (Fin d)) :
    let f := iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k)
    let g := iteratedHorizontalDerivative bs (fun ω : FieldPair d => ω.2 0)
    ∃ hf : MemLp (fun ω => f ω * g ω) 2 (reducedLaw Q),
      ∀ l : Fin d, ∃ hg : MemLp (fun ω =>
        iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.1 0 j k) ω * g ω +
          f ω * iteratedHorizontalDerivative (l :: bs)
            (fun η : FieldPair d => η.2 0) ω) 2 (reducedLaw Q),
        HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
          (hf.toLp _) (hg.toLp _) := by
  dsimp only
  have hf : MemLp (fun ω =>
      iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative bs (fun η : FieldPair d => η.2 0) ω)
      2 (reducedLaw Q) :=
    (timeFlux_coefficient_jets_memLp_top hQ j k cs).fun_mul
      (centeredClock_jets hQ bs).choose
  refine ⟨hf, ?_⟩
  intro l
  obtain ⟨C, hC, hCb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ j k
  obtain ⟨E, hE, hEb⟩ := centeredClock_jets_orbit_bounds hQ
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  apply timeFlux_horizontal_derivative_of_bounded_orbit (reducedLaw_stationary Q) l hf
    (C (l :: cs) * E bs + C cs * E (l :: bs))
  · filter_upwards [hM Q hQ] with ω hω
    intro s
    exact (c15_coefficient_jet_curve hω j k l cs s).mul
      (c15_clock_jet_curve hω l bs s)
  · filter_upwards [hCb (l :: cs), hCb cs, hEb (l :: bs), hEb bs]
      with ω h1 h2 h3 h4
    intro s
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (h1 _) (h4 _) (abs_nonneg _) (hC _)
    · rw [abs_mul]
      exact mul_le_mul (h2 _) (h3 _) (abs_nonneg _) (hC _)

private def c15_clockJet {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) :
    Lp ℂ 2 (reducedLaw Q) :=
  Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
    ((centeredClock_jets hQ cs).choose.toLp _)

private theorem c15_clockJet_ae {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) :
    c15_clockJet hQ cs =ᵐ[reducedLaw Q]
      (fun ω => (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω : ℂ)) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
    ((centeredClock_jets hQ cs).choose.toLp _),
    (centeredClock_jets hQ cs).choose.coeFn_toLp] with ω h1 h2
  exact h1.trans (congrArg Complex.ofReal h2)

private theorem c15_clockJet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) (l : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
      (c15_clockJet hQ cs) (c15_clockJet hQ (l :: cs)) :=
  hasComplexHorizontalDerivative_ofReal
    ((centeredClock_jets hQ cs).choose_spec l).choose_spec

private theorem c15_sum_ae (μ : Measure (FieldPair d))
    (s : Finset (Fin d)) (f : Fin d → Lp ℂ 2 μ) :
    (∑ j ∈ s, f j : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∑ j ∈ s, f j ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using! Lp.coeFn_zero ℂ 2 μ
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with ω h1 h2
    simpa only [Pi.add_apply, h2] using h1

private theorem c15_coefficient_mul_jet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k l : Fin d) (cs : List (Fin d)) :
    ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (complexCoefficientMul Q j k (c15_clockJet hQ cs)) H ∧
      MemLp (H : FieldPair d → ℂ) ∞ (reducedLaw Q) ∧
      H =ᵐ[reducedLaw Q] (fun ω =>
        ((iteratedHorizontalDerivative [l] (fun η : FieldPair d => η.1 0 j k) ω *
          iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω +
          iteratedHorizontalDerivative [] (fun η : FieldPair d => η.1 0 j k) ω *
          iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.2 0) ω : ℝ) : ℂ)) := by
  obtain ⟨hf, hh⟩ := c15_clock_jet_products hQ j k [] cs
  obtain ⟨hg, hd⟩ := hh l
  have he : complexCoefficientMul Q j k (c15_clockJet hQ cs) =
      Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (hf.toLp _) := by
    apply Lp.ext
    filter_upwards [complexCoefficientMul_coe Q j k (c15_clockJet hQ cs),
      c15_clockJet_ae hQ cs,
      Complex.ofRealCLM.coeFn_compLpL (hf.toLp _), hf.coeFn_toLp] with ω h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Complex.ofRealCLM_apply, Complex.ofReal_mul]
    rfl
  rw [he]
  refine ⟨_, hasComplexHorizontalDerivative_ofReal hd, ?_⟩
  have hm : MemLp (fun ω : FieldPair d =>
      ((iteratedHorizontalDerivative [l] (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω +
        iteratedHorizontalDerivative [] (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.2 0) ω : ℝ) : ℂ))
      ∞ (reducedLaw Q) := Complex.ofRealCLM.comp_memLp'
    (((timeFlux_coefficient_jets_memLp_top hQ j k [l]).fun_mul
        (centeredClock_jets_memLp_top hQ cs)).add
      ((timeFlux_coefficient_jets_memLp_top hQ j k []).fun_mul
        (centeredClock_jets_memLp_top hQ (l :: cs))))
  have hae : Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (hg.toLp _) =ᵐ[reducedLaw Q]
      (fun ω => ((iteratedHorizontalDerivative [l] (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω +
        iteratedHorizontalDerivative [] (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.2 0) ω : ℝ) : ℂ)) := by
    filter_upwards [Complex.ofRealCLM.coeFn_compLpL (hg.toLp _), hg.coeFn_toLp]
      with ω h1 h2
    exact h1.trans (congrArg Complex.ofReal h2)
  exact ⟨hm.ae_eq hae.symm, hae⟩

private theorem c15_generator_of_flux_derivatives
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hGtop : ∀ k, MemLp (G k : FieldPair d → ℂ) ∞ (reducedLaw Q))
    (H : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hH : ∀ j k, HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (complexCoefficientMul Q j k (G k)) (H j k))
    (hHtop : ∀ j k, MemLp (H j k : FieldPair d → ℂ) ∞ (reducedLaw Q)) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ f g ∧
      MemLp (g : FieldPair d → ℂ) ∞ (reducedLaw Q) ∧
      g = (1 / 2 : ℂ) • (∑ j, ∑ k, H j k) +
        ζ • ∑ j, complexCoefficientMul Q j i (G j) := by
  classical
  let g : Lp ℂ 2 (reducedLaw Q) :=
    (1 / 2 : ℂ) • (∑ j, ∑ k, H j k) + ζ • ∑ j, complexCoefficientMul Q j i (G j)
  refine ⟨g, ⟨G, hG, ?_⟩, ?_, rfl⟩
  · intro v V hV
    have hp (j k : Fin d) : c15_generatorPairing v (H j k) =
        -(∫ ω, (ω.1 0 j k : ℂ) * G k ω * V j ω ∂reducedLaw Q) := by
      rw [c15_generatorPairing_apply]
      have hb := (complexHorizontalDerivatives_integration_by_parts (hH j k) (hV j)).2.2
      calc
        _ = ∫ ω, H j k ω * v ω ∂reducedLaw Q := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => mul_comm _ _
        _ = _ := hb
        _ = _ := by
          congr 1
          apply integral_congr_ae
          filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
          rw [hω]
    have hd : c15_generatorPairing v (∑ j, complexCoefficientMul Q j i (G j)) =
        ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q := by
      rw [c15_generatorPairing_apply]
      apply integral_congr_ae
      filter_upwards [c15_sum_ae (reducedLaw Q) Finset.univ
          (fun j => complexCoefficientMul Q j i (G j)),
        ae_all_iff.mpr (fun j => complexCoefficientMul_coe Q j i (G j))] with ω h1 h2
      simp only [h1, h2]
      exact mul_comm _ _
    have hi (j k : Fin d) : Integrable
        (fun ω => (ω.1 0 j k : ℂ) * G k ω * V j ω) (reducedLaw Q) := by
      have hm := (Lp.memLp (complexCoefficientMul Q j k (G k))).integrable_mul (Lp.memLp (V j))
      apply hm.congr
      filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
      simp only [Pi.mul_apply, hω]
    have he : (∫ ω, g ω * v ω ∂reducedLaw Q) = c15_generatorPairing v g := by
      simp only [c15_generatorPairing_apply, mul_comm]
    rw [he]
    change c15_generatorPairing v ((1 / 2 : ℂ) • (∑ j, ∑ k, H j k) +
      ζ • ∑ j, complexCoefficientMul Q j i (G j)) = _
    rw [map_add, map_smul, map_smul, hd]
    simp only [map_sum, hp, smul_eq_mul, Finset.sum_neg_distrib]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hi j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hi _ k)]
    ring
  · have hsum (s : Finset (Fin d)) (F : Fin d → Lp ℂ 2 (reducedLaw Q))
        (hF : ∀ k, MemLp (F k : FieldPair d → ℂ) ∞ (reducedLaw Q)) :
        MemLp (↑(∑ k ∈ s, F k) : FieldPair d → ℂ) ∞ (reducedLaw Q) :=
      (memLp_finsetSum s (fun k _ => hF k)).ae_eq (c15_sum_ae _ s F).symm
    have hcoeff (j : Fin d) :
        MemLp (complexCoefficientMul Q j i (G j) : FieldPair d → ℂ) ∞
          (reducedLaw Q) :=
      ((memLp_reduced_coefficient_complex Q j i).fun_mul (hGtop j)).ae_eq
        (complexCoefficientMul_coe Q j i (G j)).symm
    apply ((hsum _ _ (fun j => hsum _ _ (hHtop j))).const_smul (1 / 2 : ℂ)).add
      ((hsum _ _ hcoeff).const_smul ζ) |>.ae_eq
    exact (Lp.coeFn_add _ _).trans ((Lp.coeFn_smul _ _).add (Lp.coeFn_smul _ _)) |>.symm

private theorem c15_raw_clock_bound {M : ℕ → ℝ}
    (hs : ∀ᵐ ω ∂reducedLaw Q, IsSmoothWithBounds M ω)
    (cs : List (Fin d)) (hcs : 1 ≤ cs.length) :
    ∀ᵐ ω ∂reducedLaw Q,
      |iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω| ≤ M cs.length := by
  filter_upwards [hs] with ω hω
  have he := congrFun (orbit_iteratedHorizontalDerivative cs
    (fun η : FieldPair d => η.2 0) ω) 0
  simp only [orbit, translate_zero] at he
  rw [he]
  have ho : orbit (fun η : FieldPair d => η.2 0) ω = fun x => ω.2 x := by
    funext x
    simp only [orbit, translate_scalar, add_zero]
  rw [ho]
  exact c15_jet_bound hω cs hcs 0

private theorem c15_raw_coefficient_bound {M : ℕ → ℝ}
    (hs : ∀ᵐ ω ∂reducedLaw Q, IsSmoothWithBounds M ω)
    (cs : List (Fin d)) (hcs : 1 ≤ cs.length) (j k : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q,
      |iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω| ≤ M cs.length := by
  filter_upwards [hs] with ω hω
  have he := congrFun (orbit_iteratedHorizontalDerivative cs
    (fun η : FieldPair d => η.1 0 j k) ω) 0
  simp only [orbit, translate_zero] at he
  rw [he]
  have ho : orbit (fun η : FieldPair d => η.1 0 j k) ω = fun x => ω.1 x j k := by
    funext x
    simp only [orbit, translate_matrix, add_zero]
  rw [ho]
  exact c15_coefficient_jet_bound hω cs hcs j k 0

private theorem c15_sum_bound (F : Fin d → Lp ℂ 2 (reducedLaw Q)) (b : ℝ)
    (hb : ∀ j, ∀ᵐ ω ∂reducedLaw Q, ‖F j ω‖ ≤ b) :
    ∀ᵐ ω ∂reducedLaw Q, ‖(∑ j, F j : Lp ℂ 2 (reducedLaw Q)) ω‖ ≤ d * b := by
  classical
  filter_upwards [c15_sum_ae (reducedLaw Q) Finset.univ F, ae_all_iff.mpr hb]
    with ω he hω
  rw [he]
  calc
    ‖∑ j, F j ω‖ ≤ ∑ j, ‖F j ω‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, b := Finset.sum_le_sum (fun j _ => hω j)
    _ = d * b := by simp

/-- The initial clock generator has a structural bound in every moment,
with the same generator and a constant chosen before the environment law. -/
theorem clock_initial_generator_uniform_moments
    (d : ℕ) (D : StructuralData d) (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (_hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedClockObservation Q μ → ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ A →
        ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ μ g ∧
          MemLp (g : FieldPair d → ℂ) ∞ (reducedLaw Q) ∧
          ∀ p : ℝ≥0∞, eLpNorm g p (reducedLaw Q) ≤ ENNReal.ofReal C := by
  classical
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let U := |M 1|
  let V := |M 2|
  let E := U * U + K * V
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hU : 0 ≤ U := abs_nonneg _
  have hV : 0 ≤ V := abs_nonneg _
  have hE : 0 ≤ E := by positivity
  let B : ℝ := (1 / 2) * (d * (d * E)) + A * (d * (K * U))
  refine ⟨B + 1, by dsimp [B]; positivity, ?_⟩
  intro Q hQ μ hμ i ζ hζ
  let := reducedLaw_probability Q
  have hμeq : μ = c15_clockJet hQ [] := by
    apply Lp.ext
    exact hμ.trans (c15_clockJet_ae hQ []).symm
  choose H hH hHtop hHae using fun j k => c15_coefficient_mul_jet_derivative hQ j k j [k]
  obtain ⟨g, hg, hgtop, hgeq⟩ := c15_generator_of_flux_derivatives
    (i := i) (ζ := ζ) (fun l => c15_clockJet_derivative hQ [] l)
    (fun k => (Complex.ofRealCLM.comp_memLp' (centeredClock_jets_memLp_top hQ [k])).ae_eq
      (c15_clockJet_ae hQ [k]).symm) H hH hHtop
  refine ⟨g, hμeq.symm ▸ hg, hgtop, ?_⟩
  have hfirst (k : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      |iteratedHorizontalDerivative [k] (fun η : FieldPair d => η.2 0) ω| ≤ U :=
    (c15_raw_clock_bound (hM Q hQ) [k] (by simp)).mono
      (fun _ h => h.trans (le_abs_self _))
  have hsecond (j k : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      |iteratedHorizontalDerivative [j, k] (fun η : FieldPair d => η.2 0) ω| ≤ V :=
    (c15_raw_clock_bound (hM Q hQ) [j, k] (by simp)).mono
      (fun _ h => h.trans (le_abs_self _))
  have hcoeff (j k : Fin d) : ∀ᵐ ω ∂reducedLaw Q, |ω.1 0 j k| ≤ K := by
    filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
    apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (hω 0).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1
    · exact fun ξ => ((hω 0).2 ξ).2
  have hGb (k : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ‖c15_clockJet hQ [k] ω‖ ≤ U := by
    filter_upwards [c15_clockJet_ae hQ [k], hfirst k] with ω he hb
    simpa only [he, Complex.norm_real, Real.norm_eq_abs] using hb
  have hHb (j k : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ‖H j k ω‖ ≤ E := by
    filter_upwards [hHae j k, c15_raw_coefficient_bound (hM Q hQ) [j] (by simp) j k,
      hfirst k, hsecond j k, hcoeff j k] with ω he hc hf hs ha
    rw [he, Complex.norm_real, Real.norm_eq_abs]
    change |iteratedHorizontalDerivative [j] (fun η : FieldPair d => η.1 0 j k) ω *
      iteratedHorizontalDerivative [k] (fun η : FieldPair d => η.2 0) ω +
      ω.1 0 j k * iteratedHorizontalDerivative [j, k] (fun η : FieldPair d => η.2 0) ω| ≤ E
    calc
      _ ≤ _ := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ U * U + K * V := add_le_add
        (mul_le_mul (hc.trans (le_abs_self _)) hf (abs_nonneg _) hU)
        (mul_le_mul ha hs (abs_nonneg _) hK)
  have hFb (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ‖complexCoefficientMul Q j i (c15_clockJet hQ [j]) ω‖ ≤ K * U := by
    filter_upwards [complexCoefficientMul_coe Q j i (c15_clockJet hQ [j]),
      hcoeff j i, hGb j] with ω he ha hg
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul ha hg (norm_nonneg _) hK
  have hgb : ∀ᵐ ω ∂reducedLaw Q, ‖g ω‖ ≤ B + 1 := by
    rw [hgeq]
    filter_upwards [Lp.coeFn_add ((1 / 2 : ℂ) • ∑ j, ∑ k, H j k)
        (ζ • ∑ j, complexCoefficientMul Q j i (c15_clockJet hQ [j])),
      Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, ∑ k, H j k),
      Lp.coeFn_smul ζ (∑ j, complexCoefficientMul Q j i (c15_clockJet hQ [j])),
      c15_sum_bound (fun j => ∑ k, H j k) (d * E)
        (fun j => c15_sum_bound (H j) E (hHb j)),
      c15_sum_bound (fun j => complexCoefficientMul Q j i (c15_clockJet hQ [j])) (K * U) hFb]
      with ω ha hs ht hh hf
    simp only [ha, hs, ht, Pi.add_apply, Pi.smul_apply]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) * (d * (d * E)) + A * (d * (K * U)) := by
        have hn : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
        simp only [norm_smul, hn]
        exact add_le_add (mul_le_mul_of_nonneg_left hh (by norm_num))
          (mul_le_mul hζ hf (norm_nonneg _) hA)
      _ ≤ B + 1 := by dsimp [B]; linarith
  intro p
  simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
    (eLpNorm_le_of_ae_bound (p := p) (Lp.memLp g).aestronglyMeasurable hgb)

/-- Smoothness of the actual clock datum gives an essentially bounded generator
output at every complex force; no generator-domain assumption is added. -/
theorem clock_initial_generator_memLp_top
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    {μ : Lp ℂ 2 (reducedLaw Q)} (hμ : IsReducedClockObservation Q μ) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ μ g ∧
      MemLp (g : FieldPair d → ℂ) ∞ (reducedLaw Q) := by
  have he : μ = c15_clockJet hQ [] := by
    apply Lp.ext
    exact hμ.trans (c15_clockJet_ae hQ []).symm
  rw [he]
  classical
  choose H hH hHtop hHae using fun j k => c15_coefficient_mul_jet_derivative hQ j k j [k]
  obtain ⟨g, hg, hgtop, _⟩ := c15_generator_of_flux_derivatives
    (i := i) (ζ := ζ) (fun l => c15_clockJet_derivative hQ [] l)
    (fun k => (Complex.ofRealCLM.comp_memLp' (centeredClock_jets_memLp_top hQ [k])).ae_eq
      (c15_clockJet_ae hQ [k]).symm) H hH hHtop
  exact ⟨g, hg, hgtop⟩

end InitialGenerator

/-- The actual clock orbit has a finite-p generator output. Its initial
output is derived from smoothness and is propagated by the same semigroup.
The remaining quantitative step is a structural bound for that initial output. -/
theorem clock_orbit_generator_finitep_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p A T : ℝ) (hp : 2 ≤ p) (hA : 0 ≤ A) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (_hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
    ∀ ζ : ℂ, ‖ζ‖ ≤ A →
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ μ g ∧
      MemLp (g : FieldPair d → ℂ) ∞ (reducedLaw Q) ∧
      ∀ r : ℝ≥0, (r : ℝ) ≤ T →
        IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ (P ζ r μ) (P ζ r g) ∧
        MemLp (P ζ r g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (P ζ r g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal C * eLpNorm g (ENNReal.ofReal p) (reducedLaw Q) := by
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C, hC, hb⟩ := (h0 d hd D).2 p (A + 1) T hp (by linarith) hT
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ P hP ζ hζ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨g, hg, hgtop⟩ := clock_initial_generator_memLp_top hQ ⟨0, by omega⟩ ζ hμ
  refine ⟨g, hg, hgtop, ?_⟩
  intro r hr
  have hbound := ((hb Q hQ g (hgtop.mono_exponent le_top) r hr).1 ζ
    (hζ.trans (by linarith))).1
  have hnorm := ((hb Q hQ g (hgtop.mono_exponent le_top) r hr).1 ζ
    (hζ.trans (by linarith))).2.2.1
  refine ⟨(hP ζ).map_generator hg r, ?_, ?_⟩
  · simpa only [(hP ζ).eq_forcedComplexEvolution] using hbound
  · simpa only [(hP ζ).eq_forcedComplexEvolution] using hnorm

/-- The same clock semigroup propagates a uniformly bounded initial generator.
Thus its actual forcing has finite-p moments with a structural constant. -/
theorem clock_orbit_generator_uniform_finitep_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p A T : ℝ) (hp : 2 ≤ p) (hA : 0 ≤ A) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q)
      (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (_hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
    ∀ ζ : ℂ, ‖ζ‖ ≤ A →
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ μ g ∧
      MemLp (g : FieldPair d → ℂ) ∞ (reducedLaw Q) ∧
      ∀ r : ℝ≥0, (r : ℝ) ≤ T →
        IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ (P ζ r μ) (P ζ r g) ∧
        MemLp (P ζ r g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (P ζ r g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal C := by
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C0, hC0, hb0⟩ := clock_initial_generator_uniform_moments d D A hA
  obtain ⟨C1, hC1, hb1⟩ := (h0 d hd D).2 p (A + 1) T hp (by linarith) hT
  refine ⟨C1 * C0, mul_pos hC1 hC0, ?_⟩
  intro Q hQ μ hμ P hP ζ hζ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨g, hg, hgtop, hgnorm⟩ := hb0 Q hQ μ hμ ⟨0, by omega⟩ ζ hζ
  refine ⟨g, hg, hgtop, ?_⟩
  intro r hr
  have hb := ((hb1 Q hQ g (hgtop.mono_exponent le_top) r hr).1 ζ
    (hζ.trans (by linarith)))
  refine ⟨(hP ζ).map_generator hg r, ?_, ?_⟩
  · simpa only [(hP ζ).eq_forcedComplexEvolution] using hb.1
  · calc
      _ ≤ ENNReal.ofReal C1 * eLpNorm g (ENNReal.ofReal p) (reducedLaw Q) := by
        simpa only [(hP ζ).eq_forcedComplexEvolution] using hb.2.2.1
      _ ≤ ENNReal.ofReal C1 * ENNReal.ofReal C0 :=
        mul_le_mul le_rfl (hgnorm _) (by positivity) (by positivity)
      _ = ENNReal.ofReal (C1 * C0) := (ENNReal.ofReal_mul hC1.le).symm

private theorem c15_perturbation_coordinate_average
    {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {d : ℕ} (a : α → PDE.Mat d) (A : PDE.Mat d) (δ : ℝ)
    (ha : ∀ j k, Integrable (fun y => a y j k) ν)
    (hclose : ∀ᵐ y ∂ν, PDE.IsMatrixPerturbationLE δ A (a y)) :
    PDE.IsMatrixPerturbationLE δ A (Matrix.of (fun j k => ∫ y, a y j k ∂ν)) := by
  classical
  intro ξ
  let g : α → PDE.Vec d := fun y => PDE.matVecMul (A - a y) ξ
  have hg (j : Fin d) : Integrable (fun y => g y j) ν := by
    exact integrable_finsetSum _ fun k _ => ((integrable_const _).sub (ha j k)).mul_const _
  have he : PDE.matVecMul (A - Matrix.of (fun j k => ∫ y, a y j k ∂ν)) ξ =
      fun j => ∫ y, g y j ∂ν := by
    ext j
    dsimp only [g, PDE.matVecMul, Matrix.sub_apply, Matrix.of_apply]
    rw [integral_finsetSum Finset.univ (f := fun k y => (A j k - a y j k) * ξ k) (fun k _ =>
      ((integrable_const (A j k)).sub (ha j k)).mul_const (ξ k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_mul_const, integral_sub (integrable_const _) (ha j k)]
    simp
  rw [he]
  calc
    _ ≤ ∫ y, PDE.vecEuclideanNorm (g y) ∂ν :=
      PDE.vecEuclideanNorm_integral_le_integral_vecEuclideanNorm g hg
    _ ≤ ∫ _y : α, δ * PDE.vecEuclideanNorm ξ ∂ν := by
      apply integral_mono_ae (PDE.integrable_vecEuclideanNorm_of_coord g hg)
        (integrable_const _)
      filter_upwards [hclose] with y hy
      exact hy ξ
    _ = δ * PDE.vecEuclideanNorm ξ := by simp

/-- A deterministic spatial scale makes every actual reduced coefficient field
close to its literal ball average, uniformly in the center and the law. -/
theorem clock_coefficient_small_scale_average
    (d : ℕ) (D : StructuralData d) (ε : ℝ) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ᵐ ω ∂reducedLaw Q, ∀ z : Vec d,
      ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
        PDE.IsMatrixPerturbationLE ε (ω.1 (z + ρ • x))
          (Matrix.of (fun j k => PDE.integralAverage (PDE.euclideanBall (0 : PDE.Vec d) 1)
            (fun y => ω.1 (z + ρ • y) j k))) := by
  classical
  obtain ⟨K, L, B, hK, hL, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  let ρ := ε / (2 * (L + 1))
  have hρ : 0 < ρ := div_pos hε (by positivity)
  have hsmall : L * (ρ * 2) ≤ ε := by
    have he : ρ * (2 * (L + 1)) = ε := div_mul_cancel₀ _ (by positivity)
    nlinarith
  refine ⟨ρ, hρ, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2] with ω hω
  intro z x hx
  let U := PDE.euclideanBall (0 : PDE.Vec d) 1
  let ν := PDE.normalizedVolumeOn U
  let : IsProbabilityMeasure ν :=
    PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      (PDE.volume_euclideanBall_pos (0 : PDE.Vec d) (by norm_num))
      (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top (0 : PDE.Vec d) (by norm_num)))
  let a : PDE.Vec d → PDE.Mat d := fun y => ω.1 (z + ρ • y)
  have hac (j k : Fin d) : Continuous (fun y => a y j k) := by
    have hs : Continuous (fun y : Vec d => z + ρ • y) := by fun_prop
    exact (lipschitzWith_of_euclidean_bound L hL
      (hω.2.2.1.entry_bound j k)).continuous.comp hs
  have hab (j k : Fin d) (y : PDE.Vec d) : |a y j k| ≤ K := by
    apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hK)
      (a y) (hω.1 (z + ρ • y)).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hK))
        (euclideanSq_nonneg_coords ξ)).trans ((hω.1 (z + ρ • y)).2 ξ).1
    · exact fun ξ => ((hω.1 (z + ρ • y)).2 ξ).2
  have haint (j k : Fin d) : Integrable (fun y => a y j k) ν := by
    exact (MemLp.of_bound (hac j k).aestronglyMeasurable K
      (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hab j k y)
      : MemLp (fun y => a y j k) 1 ν).integrable le_rfl
  have hyU : ∀ᵐ y ∂ν, y ∈ U := by
    exact Measure.ae_smul_measure
      (ae_restrict_mem (PDE.isOpen_euclideanBall (0 : PDE.Vec d) 1).measurableSet) _
  have hclose : ∀ᵐ y ∂ν, PDE.IsMatrixPerturbationLE ε (a x) (a y) := by
    filter_upwards [hyU] with y hy
    intro ξ
    change euclideanNorm ((ω.1 (z + ρ • x) - ω.1 (z + ρ • y)).mulVec ξ) ≤
      ε * euclideanNorm ξ
    have hxnorm : PDE.vecEuclideanNorm x < 1 := by
      simpa only [sub_zero] using
        (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
    have hynorm : PDE.vecEuclideanNorm y < 1 := by
      simpa only [sub_zero] using
        (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
    have hxy : PDE.vecEuclideanNorm (x - y) ≤ 2 := by
      have ht := PDE.vecEuclideanNorm_add_le x (-y)
      rw [PDE.vecEuclideanNorm_neg] at ht
      rw [sub_eq_add_neg]
      linarith
    have hdist : euclideanNorm ((z + ρ • x) - (z + ρ • y)) ≤ ρ * 2 := by
      rw [add_sub_add_left_eq_sub, ← smul_sub]
      change PDE.vecEuclideanNorm (ρ • (x - y)) ≤ ρ * 2
      rw [PDE.vecEuclideanNorm_smul, abs_of_pos hρ]
      exact mul_le_mul_of_nonneg_left hxy hρ.le
    exact (hω.2.2.1 _ _ ξ).trans
      (mul_le_mul_of_nonneg_right
        ((mul_le_mul_of_nonneg_left hdist hL).trans hsmall) (Real.sqrt_nonneg _))
  have havg := c15_perturbation_coordinate_average a (a x) ε haint hclose
  simpa only [a, ν, U, PDE.integral_normalizedVolumeOn_eq_integralAverage] using havg

private theorem c15_perturbation_smul {d : ℕ} {δ c : ℝ}
    {A B : PDE.Mat d} (hc : 0 ≤ c) (hAB : PDE.IsMatrixPerturbationLE δ A B) :
    PDE.IsMatrixPerturbationLE (c * δ) (c • A) (c • B) := by
  intro ξ
  have he : PDE.matVecMul (c • A - c • B) ξ = c • PDE.matVecMul (A - B) ξ := by
    rw [← smul_sub]
    exact Matrix.smul_mulVec c (A - B) ξ
  rw [he, PDE.vecEuclideanNorm_smul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left (hAB ξ) hc).trans_eq (mul_assoc _ _ _).symm

/-- The actual spatial coefficient admits the normalized ellipticity and
small oscillation required by interior elliptic estimates. Both constants
are selected before the environment law and the spatial center. -/
theorem clock_normalized_coefficient_small_scale
    (d : ℕ) (D : StructuralData d) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ ε : ℝ, 0 < ε →
      ∃ ρ : ℝ, 0 < ρ ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      ∀ᵐ ω ∂reducedLaw Q, ∀ z : Vec d,
        (∀ x : Vec d, PDE.IsEllipticMatrix 1 (K ^ 2) (K • ω.1 (z + ρ • x))) ∧
        (∀ j k : Fin d, Continuous (fun x : Vec d => (K • ω.1 (z + ρ • x)) j k)) ∧
        ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1,
          PDE.IsMatrixPerturbationLE ε (K • ω.1 (z + ρ • x))
            (Matrix.of (fun j k => PDE.integralAverage
              (PDE.euclideanBall (0 : PDE.Vec d) 1)
              (fun y => (K • ω.1 (z + ρ • y)) j k))) := by
  obtain ⟨K, L, B, hK, hL, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  refine ⟨K, hK, ?_⟩
  intro ε hε
  obtain ⟨ρ, hρ, hs⟩ := clock_coefficient_small_scale_average d D (ε / K) (div_pos hε hKpos)
  refine ⟨ρ, hρ, ?_⟩
  intro Q
  filter_upwards [(hb d D.dependenceRange Q).2.2, hs Q] with ω hω hsmall
  intro z
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hK
      (hω.1 (z + ρ • x)).1
      (fun ξ => ((hω.1 (z + ρ • x)).2 ξ).1)
      (fun ξ => ((hω.1 (z + ρ • x)).2 ξ).2)
  · intro j k
    have hc : Continuous (fun x : Vec d => ω.1 (z + ρ • x) j k) := by
      apply (lipschitzWith_of_euclidean_bound L hL
        (hω.2.2.1.entry_bound j k)).continuous.comp
      fun_prop
    simpa only [Matrix.smul_apply, smul_eq_mul] using hc.const_mul K
  · intro x hx
    have hm : Matrix.of (fun j k => PDE.integralAverage
        (PDE.euclideanBall (0 : PDE.Vec d) 1)
        (fun y => (K • ω.1 (z + ρ • y)) j k)) =
        K • Matrix.of (fun j k => PDE.integralAverage
          (PDE.euclideanBall (0 : PDE.Vec d) 1)
          (fun y => ω.1 (z + ρ • y) j k)) := by
      ext j k
      simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, PDE.integralAverage,
        integral_const_mul]
      ring
    rw [hm]
    have he := c15_perturbation_smul hKpos.le (hsmall z x hx)
    rwa [mul_div_cancel₀ ε hKpos.ne'] at he

private theorem c15_complex_weighted_gradient_test {d : ℕ}
    {u v : Vec d → ℂ} (j : Fin d)
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    (hw : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      (∫ x, u x * (coordinateDerivative j ψ x : ℂ)) = -(∫ x, v x * (ψ x : ℂ)))
    (a φ : Vec d → ℝ) (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, (a x : ℂ) * v x * (φ x : ℂ)) =
      -(∫ x, u x * ((coordinateDerivative j a x * φ x : ℝ) : ℂ)) -
        (∫ x, u x * ((a x * coordinateDerivative j φ x : ℝ) : ℂ)) := by
  have hda : Continuous (coordinateDerivative j a) :=
    (ha.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hi₁ : Integrable (fun x =>
      u x * ((coordinateDerivative j a x * φ x : ℝ) : ℂ)) volume :=
    integrable_spatial_mul_test hu (hda.mul hφ.continuous) hφc.mul_left
  have hi₂ : Integrable (fun x =>
      u x * ((a x * coordinateDerivative j φ x : ℝ) : ℂ)) volume :=
    integrable_spatial_mul_test hu (ha.continuous.mul hdφ)
      ((hφc.fderiv_apply ℝ (unitVector j)).mul_left)
  have he := hw (fun x => a x * φ x) (ha.mul hφ) hφc.mul_left
  have hs : (fun x => u x * (coordinateDerivative j (fun y => a y * φ y) x : ℂ)) =
      fun x => u x * ((coordinateDerivative j a x * φ x : ℝ) : ℂ) +
        u x * ((a x * coordinateDerivative j φ x : ℝ) : ℂ) := by
    funext x
    rw [coordinateDerivative_mul j a φ x
      (ha.differentiable (by simp) x) (hφ.differentiable (by simp) x)]
    push_cast
    ring
  rw [hs, integral_add hi₁ hi₂] at he
  have hv : (∫ x, v x * ((a x * φ x : ℝ) : ℂ)) =
      ∫ x, (a x : ℂ) * v x * (φ x : ℂ) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by push_cast; ring
  rw [hv] at he
  linear_combination he

/-- The actual generator equation can be written with a divergence forcing
depending on the value, rather than on higher moments of its gradient. The
identity is simultaneous for all compactly supported smooth spatial tests. -/
theorem clock_generator_spatial_value_forcing {d : ℕ} [Fact (2 ≤ d)]
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
        (coordinateDerivative j φ x : ℂ)) =
        -(2 : ℂ) * (∫ x,
          (g (translate x ω) + ζ * (∑ j,
            (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) *
              f (translate x ω)) * (φ x : ℂ)) -
        (2 * ζ) * (∫ x, ∑ j,
          (ω.1 x j i : ℂ) * f (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
  classical
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [hM Q hQ, hG.ae_reduced_spatial Q, hG.ae_spatial_test,
    hfg.spatial_flux_all_tests hG,
    ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) g] with ω hs hloc hw he hg
  intro φ hφ hφc
  let B : Fin d → Vec d → ℂ := fun j x =>
    (ω.1 x j i : ℂ) * G j (translate x ω) * (φ x : ℂ)
  let H : Fin d → Vec d → ℂ := fun j x =>
    f (translate x ω) * ((coordinateDerivative j (fun y => ω.1 y j i) x * φ x : ℝ) : ℂ)
  let V : Fin d → Vec d → ℂ := fun j x =>
    f (translate x ω) * ((ω.1 x j i * coordinateDerivative j φ x : ℝ) : ℂ)
  have hBi (j : Fin d) : Integrable (B j) volume := by
    have hi := integrable_spatial_mul_test (fun K hK => (hloc.2.2 K hK).2 j)
      ((hs.1.1 j i).continuous.mul hφ.continuous) hφc.mul_left
    exact hi.congr (Filter.Eventually.of_forall fun x => by dsimp [B]; push_cast; ring)
  have hHi (j : Fin d) : Integrable (H j) volume := by
    exact integrable_spatial_mul_test (fun K hK => (hloc.2.2 K hK).1)
      (((hs.1.1 j i).continuous_fderiv (by simp)).clm_apply continuous_const |>.mul
        hφ.continuous) hφc.mul_left
  have hVi (j : Fin d) : Integrable (V j) volume := by
    exact integrable_spatial_mul_test (fun K hK => (hloc.2.2 K hK).1)
      ((hs.1.1 j i).continuous.mul
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))
      ((hφc.fderiv_apply ℝ (unitVector j)).mul_left)
  have hp (j : Fin d) : (∫ x, B j x) = -(∫ x, H j x) - (∫ x, V j x) := by
    exact c15_complex_weighted_gradient_test j
      (fun K hK => (hloc.2.2 K hK).1)
      (fun ψ hψ hψc => hw j ψ ⟨hψ, hψc, Set.subset_univ _⟩)
      (fun x => ω.1 x j i) φ (hs.1.1 j i) hφ hφc
  have hsum : (∫ x, ∑ j, B j x) =
      -(∫ x, ∑ j, H j x) - (∫ x, ∑ j, V j x) := by
    rw [integral_finsetSum Finset.univ (fun j _ => hBi j)]
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      integral_finsetSum Finset.univ (fun j _ => hHi j),
      integral_finsetSum Finset.univ (fun j _ => hVi j)]
  have hBeq : (fun x => (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) =
      fun x => ∑ j, B j x := by
    funext x
    simp only [B, Finset.sum_mul]
  have hHeq : (fun x => ∑ j, H j x) = fun x =>
      (∑ j, (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) *
        f (translate x ω) * (φ x : ℂ) := by
    funext x
    simp only [H, Complex.ofReal_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hVeq : (fun x => ∑ j, V j x) = fun x => ∑ j,
      (ω.1 x j i : ℂ) * f (translate x ω) * (coordinateDerivative j φ x : ℂ) := by
    funext x
    apply Finset.sum_congr rfl
    intro j _
    dsimp [V]
    push_cast
    ring
  have hgint := integrable_spatial_mul_test hg hφ.continuous hφc
  have hHint : Integrable (fun x =>
      (∑ j, (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) *
        f (translate x ω) * (φ x : ℂ)) volume := by
    rw [← hHeq]
    exact integrable_finsetSum _ (fun j _ => hHi j)
  have hforce : (∫ x,
      (g (translate x ω) + ζ * (∑ j,
        (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)) *
          (φ x : ℂ)) =
      (∫ x, g (translate x ω) * (φ x : ℂ)) +
        ζ * (∫ x, (∑ j,
          (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) *
            f (translate x ω) * (φ x : ℂ)) := by
    simp_rw [add_mul, mul_assoc ζ]
    rw [integral_add hgint (hHint.const_mul ζ), integral_const_mul]
  have heφ := he φ hφ hφc
  rw [hBeq, hsum, hHeq, hVeq] at heφ
  rw [hforce]
  linear_combination 2 * heφ

private theorem c15_inner_eq_vecDot {d : ℕ} (x y : PDE.HilbertVec d) :
    inner ℝ x y = PDE.vecDot x.toVec y.toVec := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
    PDE.vecDot, PDE.HilbertVec.toVec_apply, mul_comm]

/-- Scalar and divergence forcing on the unit ball define a bounded functional
for the gradient norm used by the interior negative-Sobolev estimate. The
Poincaré constant depends only on the dimension. -/
theorem clock_unit_ball_forcing_functional
    (d : ℕ) (hd : 0 < d) (p : ℝ) (hp : 2 ≤ p) :
    let q := ENNReal.ofReal (p / (p - 1))
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    letI : Fact (1 ≤ q) :=
      ⟨ENNReal.one_le_ofReal.mpr
        (Real.HolderConjugate.conjExponent (lt_of_lt_of_le one_lt_two hp)).symm.lt.le⟩
    let U := PDE.euclideanBall (0 : Vec d) 1
    let S := PDE.W10pGraph (p := q) (PDE.isOpen_euclideanBall (0 : Vec d) 1)
    let A : S →ₗ[ℝ] PDE.HilbertVectorLp U q :=
      (PDE.w10pGradientCLM q (PDE.isOpen_euclideanBall (0 : Vec d) 1)).toLinearMap
    letI : NormedAddCommGroup S :=
      NormedAddCommGroup.induced S (PDE.HilbertVectorLp U q) A
        (PDE.w10pGradientCLM_injective hd
          (PDE.isOpenBoundedConvexDomain_euclideanBall
            (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
          (PDE.hasEuclideanDiameterLE_euclideanBall
            (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
          (by norm_num : (0 : ℝ) ≤ 2 * 1)
          (Real.HolderConjugate.conjExponent
            (lt_of_lt_of_le one_lt_two hp)).symm.lt)
    letI : SeminormedAddCommGroup S :=
      (inferInstance : NormedAddCommGroup S).toSeminormedAddCommGroup
    letI : TopologicalSpace S :=
      (inferInstance : NormedAddCommGroup S).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : Norm S := (inferInstance : NormedAddCommGroup S).toNorm
    letI : NormedSpace ℝ S :=
      NormedSpace.induced ℝ S (PDE.HilbertVectorLp U q) A
    ∀ (h : PDE.ScalarLp U (ENNReal.ofReal p))
      (F : PDE.HilbertVectorLp U (ENNReal.ofReal p)),
      ∃ L : S →L[ℝ] ℝ,
        ‖L‖ ≤ (((2 : ℝ) ^ d + 1) * 2) * ‖h‖ + ‖F‖ ∧
        ∀ φ : PDE.WeakTestFunction U,
          L (PDE.smoothCompactlySupportedW1pGraphToW10pGraph
            (p := q) (PDE.isOpen_euclideanBall (0 : Vec d) 1) φ) =
            (∫ x in U, h x * φ x) +
              ∫ x in U, PDE.vecDot (F x).toVec (φ.grad x) := by
  intro q U S A
  have hpOne : 1 < p := lt_of_lt_of_le one_lt_two hp
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hpOne.le⟩
  letI : Fact (1 ≤ q) :=
    ⟨ENNReal.one_le_ofReal.mpr (Real.HolderConjugate.conjExponent hpOne).symm.lt.le⟩
  letI : ENNReal.HolderConjugate (ENNReal.ofReal p) q :=
    (Real.HolderConjugate.conjExponent hpOne).ennrealOfReal
  have hA : Function.Injective A :=
    PDE.w10pGradientCLM_injective hd
      (PDE.isOpenBoundedConvexDomain_euclideanBall
        (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
      (PDE.hasEuclideanDiameterLE_euclideanBall
        (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
      (by norm_num : (0 : ℝ) ≤ 2 * 1)
      (Real.HolderConjugate.conjExponent hpOne).symm.lt
  let value : S →ₗ[ℝ] PDE.ScalarLp U q :=
    (LinearMap.fst ℝ (PDE.ScalarLp U q) (PDE.HilbertVectorLp U q)).comp
      ((PDE.weakGradientGraph U q).subtype.comp
        (PDE.w10pGraphClosedSubmodule (p := q)
          (PDE.isOpen_euclideanBall (0 : Vec d) 1)).toSubmodule.subtype)
  have hPoincare (v : S) :
      ‖value v‖ ≤ (((2 : ℝ) ^ d + 1) * 2) * ‖A v‖ := by
    change ‖(v : PDE.W1pGraph U q).1.1‖ ≤
      (((2 : ℝ) ^ d + 1) * 2) * ‖(v : PDE.W1pGraph U q).1.2‖
    simpa only [mul_one] using!
      PDE.W10pGraph.norm_fst_le_two_pow_add_one_mul_diameter_norm_snd hd
        (PDE.isOpenBoundedConvexDomain_euclideanBall
          (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (PDE.hasEuclideanDiameterLE_euclideanBall
          (0 : Vec d) (by norm_num : (0 : ℝ) < 1))
        (by norm_num : (0 : ℝ) ≤ 2 * 1)
        (Real.HolderConjugate.conjExponent hpOne).symm.lt v
  letI : NormedAddCommGroup S :=
    NormedAddCommGroup.induced S (PDE.HilbertVectorLp U q) A hA
  letI : SeminormedAddCommGroup S :=
    (inferInstance : NormedAddCommGroup S).toSeminormedAddCommGroup
  letI : TopologicalSpace S :=
    (inferInstance : NormedAddCommGroup S).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : Norm S := (inferInstance : NormedAddCommGroup S).toNorm
  letI : NormedSpace ℝ S := NormedSpace.induced ℝ S (PDE.HilbertVectorLp U q) A
  intro h F
  let scalar : PDE.ScalarLp U q →L[ℝ] ℝ :=
    (ContinuousLinearMap.mul ℝ ℝ).lpPairing (PDE.volumeOn U)
      (ENNReal.ofReal p) q h
  let vector : PDE.HilbertVectorLp U q →L[ℝ] ℝ :=
    (innerSL ℝ).lpPairing (PDE.volumeOn U) (ENNReal.ofReal p) q F
  let l : S →ₗ[ℝ] ℝ := scalar.toLinearMap.comp value + vector.toLinearMap.comp A
  let B : ℝ := (((2 : ℝ) ^ d + 1) * 2) * ‖h‖ + ‖F‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound (v : S) : ‖l v‖ ≤ B * ‖v‖ := by
    have hscalar : ‖scalar‖ ≤ ‖h‖ := PDE.norm_scalarLpPairing_le h
    have hvector : ‖vector‖ = ‖F‖ := PDE.norm_hilbertLpPairing_eq hpOne F
    change ‖scalar (value v) + vector (A v)‖ ≤ B * ‖A v‖
    calc
      _ ≤ ‖scalar (value v)‖ + ‖vector (A v)‖ := norm_add_le _ _
      _ ≤ ‖h‖ * ‖value v‖ + ‖F‖ * ‖A v‖ :=
        add_le_add ((scalar.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)))
          (by rw [← hvector]; exact vector.le_opNorm _)
      _ ≤ ‖h‖ * ((((2 : ℝ) ^ d + 1) * 2) * ‖A v‖) + ‖F‖ * ‖A v‖ :=
        add_le_add (mul_le_mul_of_nonneg_left (hPoincare v) (norm_nonneg h)) le_rfl
      _ = B * ‖A v‖ := by dsimp [B]; ring
  refine ⟨l.mkContinuous B hbound, LinearMap.mkContinuous_norm_le _ hB _, ?_⟩
  intro φ
  let v : S := PDE.smoothCompactlySupportedW1pGraphToW10pGraph
    (p := q) (PDE.isOpen_euclideanBall (0 : Vec d) 1) φ
  change scalar (value v) + vector (A v) = _
  rw [ContinuousLinearMap.lpPairing_eq_integral,
    ContinuousLinearMap.lpPairing_eq_integral]
  congr 1
  · apply integral_congr_ae
    have hv : (value v : Vec d → ℝ) =ᵐ[PDE.volumeOn U] φ :=
      (PDE.W1pFunction.ofContDiff (PDE.isOpen_euclideanBall (0 : Vec d) 1)
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport q).coeFn_toW1pGraph_fst
    filter_upwards [hv] with x hx
    change h x * value v x = h x * φ x
    rw [hx]
  · apply integral_congr_ae
    have hv := PDE.w10pGradientCLM_smoothCompactlySupported_ae q
      (PDE.isOpen_euclideanBall (0 : Vec d) 1) φ
    filter_upwards [hv] with x hx
    change inner ℝ (F x) (A v x) = PDE.vecDot (F x).toVec (φ.grad x)
    exact (c15_inner_eq_vecDot (F x) (A v x)).trans (congrArg _ hx)

private def c15_rescaled_spatial_h1 {d : ℕ} {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u 2 (volume.restrict K))
    (hG : ∀ K : Set (Vec d), IsCompact K →
      ∀ j : Fin d, MemLp (fun x => G x j) 2 (volume.restrict K))
    (hw : HasWeakGradient Set.univ u G) (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ) :
    PDE.H1Function (PDE.euclideanBall (0 : Vec d) 1) := by
  let U := PDE.euclideanBall z ρ
  let K := PDE.euclideanClosedBall z ρ
  have hK : IsCompact K := PDE.isCompact_euclideanClosedBall z hρ.le
  have hUK : U ⊆ K := PDE.euclideanBall_subset_euclideanClosedBall z ρ
  have hwp : PDE.HasWeakGradientOn Set.univ u G := by
    intro j φ hφ hφc hφu
    exact (hw j).2.2 φ ⟨hφ, hφc, hφu⟩
  let v : PDE.H1Function U :=
    { toFun := u
      grad := G
      memL2 := (hu K hK).mono_measure (Measure.restrict_mono hUK le_rfl)
      gradMemL2 := fun j => (hG K hK j).mono_measure (Measure.restrict_mono hUK le_rfl)
      hasWeakGradient := hwp.restrict (PDE.isOpen_euclideanBall z ρ) (Set.subset_univ _) }
  let w := ρ⁻¹ • PDE.DGNM.blowUp v z hρ (Set.Subset.refl U)
  exact PDE.DGNM.H1copy w rfl
    (fun x => ρ⁻¹ * u (z + ρ • x))
    (fun x => by simp only [w, PDE.H1Function.smul_toFun,
      PDE.DGNM.blowUp_toFun, v, add_comm])
    (fun x => G (z + ρ • x))
    (fun x => by
      simp only [w, PDE.H1Function.smul_grad, PDE.DGNM.blowUp_grad,
        v, smul_smul, inv_mul_cancel₀ hρ.ne', one_smul, add_comm])

/-- The real and imaginary parts of the actual canonical orbit have unit-ball
H1 representatives after rescaling. Amplitude normalization leaves their
gradients equal to the literal rescaled canonical gradient. All centers and
positive scales share one full-measure event. -/
theorem clock_gradient_spatial_rescaled_h1 {d : ℕ} [Fact (2 ≤ d)]
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      ∃ u v : PDE.H1Function (PDE.euclideanBall (0 : Vec d) 1),
        (∀ x, u x = ρ⁻¹ * (f (translate (z + ρ • x) ω)).re) ∧
        (∀ x j, u.grad x j = (G j (translate (z + ρ • x) ω)).re) ∧
        (∀ x, v x = ρ⁻¹ * (f (translate (z + ρ • x) ω)).im) ∧
        (∀ x j, v.grad x j = (G j (translate (z + ρ • x) ω)).im) := by
  filter_upwards [hG.ae_reduced_spatial Q] with ω hω
  intro z ρ hρ
  exact ⟨c15_rescaled_spatial_h1
      (fun K hK => (hω.2.2 K hK).1.re)
      (fun K hK j => ((hω.2.2 K hK).2 j).re) hω.1 z hρ,
    c15_rescaled_spatial_h1
      (fun K hK => (hω.2.2 K hK).1.im)
      (fun K hK j => ((hω.2.2 K hK).2 j).im) hω.2.1 z hρ,
    fun _ => rfl, fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl⟩


private theorem c15_project_forcing_identity {d : ℕ}
    (L : ℂ →L[ℝ] ℝ) (a : Vec d → Fin d → Fin d → ℝ)
    (G : Vec d → Fin d → ℂ) (H : Vec d → ℂ) (B : Vec d → Fin d → ℂ)
    (φ : Vec d → ℝ)
    (hflux : Integrable (fun x => ∑ j, (∑ k, (a x j k : ℂ) * G x k) *
      (coordinateDerivative j φ x : ℂ)) volume)
    (hsource : Integrable (fun x => H x * (φ x : ℂ)) volume)
    (hforcing : Integrable (fun x => ∑ j, B x j *
      (coordinateDerivative j φ x : ℂ)) volume)
    (he : (∫ x, ∑ j, (∑ k, (a x j k : ℂ) * G x k) *
        (coordinateDerivative j φ x : ℂ)) =
      (-2 : ℂ) * (∫ x, H x * (φ x : ℂ)) -
        (2 : ℂ) * (∫ x, ∑ j, B x j * (coordinateDerivative j φ x : ℂ))) :
    Integrable (fun x => ∑ j, (∑ k, a x j k * L (G x k)) *
      coordinateDerivative j φ x) volume ∧
    Integrable (fun x => L (H x) * φ x) volume ∧
    Integrable (fun x => ∑ j, L (B x j) * coordinateDerivative j φ x) volume ∧
    (∫ x, ∑ j, (∑ k, a x j k * L (G x k)) * coordinateDerivative j φ x) =
      -2 * (∫ x, L (H x) * φ x) -
        2 * (∫ x, ∑ j, L (B x j) * coordinateDerivative j φ x) := by
  have hleft (c : ℝ) (z : ℂ) : L ((c : ℂ) * z) = c * L z := by
    rw [← Complex.real_smul, L.map_smul, smul_eq_mul]
  have hright (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, hleft, mul_comm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [map_sum, hleft, hright] using L.integrable_comp hflux
  · simpa only [hright] using L.integrable_comp hsource
  · simpa only [map_sum, hright] using L.integrable_comp hforcing
  · have h := congrArg L he
    rw [map_sub, show (-2 : ℂ) = ((-2 : ℝ) : ℂ) by norm_num,
      hleft, show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, hleft,
      ← L.integral_comp_comm hflux, ← L.integral_comp_comm hsource,
      ← L.integral_comp_comm hforcing] at h
    simpa only [map_sum, hleft, hright] using h

/-- Projection of the actual complex equation onto any real linear component.
All three smooth-test pairings are integrable on the same environment event.
Taking `Complex.reCLM` and `Complex.imCLM` gives the two real equations used by
interior elliptic regularity. -/
theorem clock_generator_spatial_projected_value_forcing {d : ℕ} [Fact (2 ≤ d)]
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      let H := fun x => g (translate x ω) + ζ * (∑ j,
        (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)
      let B := fun x j => ζ * (ω.1 x j i : ℂ) * f (translate x ω)
      ∀ (L : ℂ →L[ℝ] ℝ) (φ : Vec d → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      Integrable (fun x => ∑ j, (∑ k, ω.1 x j k * L (G k (translate x ω))) *
        coordinateDerivative j φ x) volume ∧
      Integrable (fun x => L (H x) * φ x) volume ∧
      Integrable (fun x => ∑ j, L (B x j) * coordinateDerivative j φ x) volume ∧
      (∫ x, ∑ j, (∑ k, ω.1 x j k * L (G k (translate x ω))) *
        coordinateDerivative j φ x) =
        -2 * (∫ x, L (H x) * φ x) -
          2 * (∫ x, ∑ j, L (B x j) * coordinateDerivative j φ x) := by
  classical
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [hM Q hQ, hG.ae_reduced_spatial Q,
    ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) g,
    clock_generator_spatial_value_forcing D Q hQ i ζ hfg hG] with ω hs hloc hg he
  intro H B L φ hφ hφc
  have hderivCont (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hderivCompact (j : Fin d) : HasCompactSupport (coordinateDerivative j φ) :=
    hφc.fderiv_apply ℝ (unitVector j)
  have hflux : Integrable (fun x => ∑ j, (∑ k, (ω.1 x j k : ℂ) *
      G k (translate x ω)) * (coordinateDerivative j φ x : ℂ)) volume := by
    simp_rw [Finset.sum_mul]
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    have h := integrable_spatial_mul_test (fun K hK => (hloc.2.2 K hK).2 k)
      ((hs.1.1 j k).continuous.mul (hderivCont j)) (hderivCompact j).mul_left
    exact h.congr (Filter.Eventually.of_forall fun x => by
      dsimp only [Pi.mul_apply]
      push_cast
      ring)
  have hsource : Integrable (fun x => H x * (φ x : ℂ)) volume := by
    have h₁ := integrable_spatial_mul_test hg hφ.continuous hφc
    have h₂ := integrable_spatial_mul_test
      (φ := fun x => (∑ j, coordinateDerivative j (fun y => ω.1 y j i) x) * φ x)
      (fun K hK => (hloc.2.2 K hK).1)
      ((continuous_finsetSum Finset.univ (fun j _ =>
        (hs.1.1 j i).continuous_fderiv (by simp) |>.clm_apply continuous_const)).mul
          hφ.continuous) hφc.mul_left
    apply (h₁.add (h₂.const_mul ζ)).congr
    exact Filter.Eventually.of_forall fun x => by dsimp [H]; push_cast; ring
  have hforcing : Integrable (fun x => ∑ j, B x j *
      (coordinateDerivative j φ x : ℂ)) volume := by
    apply integrable_finsetSum
    intro j _
    have h := integrable_spatial_mul_test (fun K hK => (hloc.2.2 K hK).1)
      ((hs.1.1 j i).continuous.mul (hderivCont j)) (hderivCompact j).mul_left
    apply (h.const_mul ζ).congr
    exact Filter.Eventually.of_forall fun x => by dsimp [B]; push_cast; ring
  apply c15_project_forcing_identity L ω.1 (fun x j => G j (translate x ω))
    H B φ hflux hsource hforcing
  have heφ := he φ hφ hφc
  have hB : (∫ x, ∑ j, B x j * (coordinateDerivative j φ x : ℂ)) =
      ζ * (∫ x, ∑ j, (ω.1 x j i : ℂ) * f (translate x ω) *
        (coordinateDerivative j φ x : ℂ)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      simp only [B, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hB]
  change _ = (-2 : ℂ) * (∫ x, H x * (φ x : ℂ)) - _
  linear_combination heφ


private theorem c15_test_source_integral {d : ℕ} {U : Set (Vec d)}
    (H : Vec d → ℝ) (φ : PDE.WeakTestFunction U) :
    (∫ x in U, H x * φ x) = ∫ x, H x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h => hx (φ.tsupport_subset h)), mul_zero]

private theorem c15_test_vector_integral {d : ℕ} {U : Set (Vec d)}
    (V : Vec d → Vec d) (φ : PDE.WeakTestFunction U) :
    (∫ x in U, PDE.vecDot (V x) (φ.grad x)) =
      ∫ x, PDE.vecDot (V x) (φ.grad x) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hn : x ∉ tsupport φ.toFun := fun h => hx (φ.tsupport_subset h)
  simp [PDE.vecDot, PDE.WeakTestFunction.grad, PDE.WeakTestFunction.partialDeriv,
    fderiv_of_notMem_tsupport ℝ hn]

private theorem c15_rescaled_test_pairings {d : ℕ}
    (H : Vec d → ℝ) (V : Vec d → Vec d) (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (φ : PDE.WeakTestFunction (PDE.euclideanBall (0 : Vec d) 1)) :
    let ψ := PDE.DGNM.pullTest z hρ φ
    ((∫ x in PDE.euclideanBall (0 : Vec d) 1, H (z + ρ • x) * φ x) =
      (ρ ^ d)⁻¹ * ∫ x, H x * ψ x) ∧
    ((∫ x in PDE.euclideanBall (0 : Vec d) 1,
        PDE.vecDot (V (z + ρ • x)) (φ.grad x)) =
      ρ * (ρ ^ d)⁻¹ * ∫ x, PDE.vecDot (V x) (ψ.grad x)) := by
  intro ψ
  constructor
  · have h := PDE.DGNM.setIntegral_comp_affineScale_ball z hρ 1
      (fun x => H x * ψ x)
    rw [mul_one, c15_test_source_integral] at h
    simpa only [ψ, PDE.DGNM.pullTest_apply, add_sub_cancel_right,
      inv_smul_smul₀ hρ.ne', add_comm z] using h
  · calc
      _ = ∫ x in PDE.euclideanBall (0 : Vec d) 1,
          ρ * PDE.vecDot (V (ρ • x + z)) (ψ.grad (ρ • x + z)) := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [ψ, PDE.DGNM.pullTest_grad, add_sub_cancel_right,
          inv_smul_smul₀ hρ.ne', add_comm z, PDE.vecDot,
          Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
      _ = ρ * (∫ x in PDE.euclideanBall (0 : Vec d) 1,
          PDE.vecDot (V (ρ • x + z)) (ψ.grad (ρ • x + z))) := integral_const_mul _ _
      _ = ρ * ((ρ ^ d)⁻¹ * ∫ x in PDE.euclideanBall z ρ,
          PDE.vecDot (V x) (ψ.grad x)) := by
        congr 1
        simpa only [mul_one] using PDE.DGNM.setIntegral_comp_affineScale_ball z hρ 1
          (fun x => PDE.vecDot (V x) (ψ.grad x))
      _ = ρ * (ρ ^ d)⁻¹ * ∫ x, PDE.vecDot (V x) (ψ.grad x) := by
        rw [c15_test_vector_integral]
        ring

/-- The actual projected weak equation at every center and positive scale.
The amplitude-normalized gradient is unchanged, while the scalar source
acquires the exact factor of the spatial scale. The coefficient multiplier
is explicit for use with the structural ellipticity normalization. -/
theorem clock_generator_spatial_rescaled_value_forcing {d : ℕ} [Fact (2 ≤ d)]
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      let H := fun x => g (translate x ω) + ζ * (∑ j,
        (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)
      let B := fun x j => ζ * (ω.1 x j i : ℂ) * f (translate x ω)
      ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → ∀ (K : ℝ) (L : ℂ →L[ℝ] ℝ)
        (φ : PDE.WeakTestFunction (PDE.euclideanBall (0 : Vec d) 1)),
      (∫ x in PDE.euclideanBall (0 : Vec d) 1,
        PDE.vecDot (PDE.matVecMul (fun j k => K * ω.1 (z + ρ • x) j k)
          (fun j => L (G j (translate (z + ρ • x) ω)))) (φ.grad x)) =
        (∫ x in PDE.euclideanBall (0 : Vec d) 1,
          (-2 * K * ρ * L (H (z + ρ • x))) * φ x) +
        ∫ x in PDE.euclideanBall (0 : Vec d) 1,
          PDE.vecDot (fun j => -2 * K * L (B (z + ρ • x) j)) (φ.grad x) := by
  filter_upwards [clock_generator_spatial_projected_value_forcing D Q hQ i ζ hfg hG]
    with ω he
  intro H B z ρ hρ K L φ
  let ψ := PDE.DGNM.pullTest z hρ φ
  let J := fun x => PDE.matVecMul (ω.1 x) (fun j => L (G j (translate x ω)))
  let V := fun x j => L (B x j)
  have h := (he L ψ ψ.contDiff ψ.hasCompactSupport).2.2.2
  have hbase : (∫ x, PDE.vecDot (J x) (ψ.grad x)) =
      -2 * (∫ x, L (H x) * ψ x) - 2 * ∫ x, PDE.vecDot (V x) (ψ.grad x) := by
    simpa only [J, V, H, B, PDE.vecDot, PDE.matVecMul, PDE.WeakTestFunction.grad,
      PDE.WeakTestFunction.partialDeriv, coordinateDerivative, PDE.basisVec, unitVector] using h
  have hJ := (c15_rescaled_test_pairings (fun x => L (H x)) J z hρ φ).2
  have hH := (c15_rescaled_test_pairings (fun x => L (H x)) V z hρ φ).1
  have hV := (c15_rescaled_test_pairings (fun x => L (H x)) V z hρ φ).2
  have hleft : (fun x => PDE.vecDot
      (PDE.matVecMul (fun j k => K * ω.1 (z + ρ • x) j k)
        (fun j => L (G j (translate (z + ρ • x) ω)))) (φ.grad x)) =
      fun x => K * PDE.vecDot (J (z + ρ • x)) (φ.grad x) := by
    funext x
    simp only [J, PDE.vecDot, PDE.matVecMul, ← Finset.mul_sum, mul_assoc]
  have hsource : (fun x => (-2 * K * ρ * L (H (z + ρ • x))) * φ x) =
      fun x => (-2 * K * ρ) * (L (H (z + ρ • x)) * φ x) := by
    funext x
    ring
  have hvector : (fun x => PDE.vecDot
      (fun j => -2 * K * L (B (z + ρ • x) j)) (φ.grad x)) =
      fun x => (-2 * K) * PDE.vecDot (V (z + ρ • x)) (φ.grad x) := by
    funext x
    simp only [V, PDE.vecDot, Finset.mul_sum, mul_assoc]
  rw [hleft, hsource, hvector, integral_const_mul, integral_const_mul, integral_const_mul,
    hJ, hH, hV, hbase]
  ring


/-- Interior elliptic regularity with scalar and vector data, using the exact
unit-ball coefficient average. The forcing norm is bounded explicitly by
Poincaré and Hölder, so it does not contain a higher-moment gradient premise. -/
theorem clock_unit_ball_scalar_vector_regularity
    (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (p : ℝ) (hp : 2 ≤ p),
      letI : Fact (1 ≤ ENNReal.ofReal p) :=
        ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
      let U := PDE.euclideanBall (0 : Vec d) 1
      ∀ (a : PDE.CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (PDE.volumeOn U)) →
      (∀ᵐ x ∂PDE.volumeOn U, PDE.IsEllipticMatrix 1 Λ (a x)) →
      (let A₀ : PDE.Mat d := fun i j => PDE.integralAverage U (fun x => a x i j)
        ∀ᵐ x ∂PDE.volumeOn U, PDE.IsMatrixPerturbationLE (1 / (C * p)) (a x) A₀) →
      ∀ (u : PDE.H1Function U) (h : PDE.ScalarLp U (ENNReal.ofReal p))
        (F : PDE.HilbertVectorLp U (ENNReal.ofReal p)),
      (∀ φ : PDE.WeakTestFunction U,
        (∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x)) (φ.grad x)) =
          (∫ x in U, h x * φ x) + ∫ x in U, PDE.vecDot (F x).toVec (φ.grad x)) →
      PDE.MemW1p (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))
          (ENNReal.ofReal p) u.toFun ∧
        ∃ hgrad : MemLp (fun x => PDE.vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal p)
            (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))),
          PDE.euclideanFieldLpMeanNormOn
              (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ)) (ENNReal.ofReal p) u.grad
              (PDE.memLp_normalizedVolumeOn_of_memLpOn hgrad
                (PDE.volume_euclideanBall_pos (0 : Vec d) (by norm_num))) ≤
            C * (Real.sqrt (PDE.integralAverage U (fun x => PDE.vecNormSq (u.grad x))) +
              p * (((volume U)⁻¹ ^ (1 / ENNReal.ofReal p).toReal).toReal *
                ((((2 : ℝ) ^ d + 1) * 2) * ‖h‖ + ‖F‖))) := by
  obtain ⟨C, hC, hCZ⟩ := PDE.exists_interior_negativeSobolev d hd Λ hΛ
  refine ⟨C, hC, ?_⟩
  intro p hp U a hameas hell hclose u h F he
  obtain ⟨L, hL, hLeval⟩ := clock_unit_ball_forcing_functional d hd p hp h F
  have hEq := fun φ => (he φ).trans (hLeval φ).symm
  obtain ⟨hu, hgrad, hbound⟩ := hCZ p hp a hameas hell hclose u L hEq
  refine ⟨hu, hgrad, hbound.trans ?_⟩
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  gcongr


/-- Any finite moment of the literal stationary observable gives local spatial
membership, on one event preceding every compact set. -/
theorem clock_ae_orbit_finitep_on_all_compacts {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp (f : FieldPair d → ℂ) p Q) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => f (translate x ω)) p (volume.restrict K) := by
  have hm : Measurable (fun ω => ‖f ω‖ ^ p.toReal) :=
    (Lp.stronglyMeasurable f).measurable.norm.pow_const _
  have hn (n : ℕ) := ae_integrableOn_stationary_orbit hQ hm
    (hf.integrable_norm_rpow hp0 hpt)
    (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : Vec d)
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hKn : K ⊆ Metric.closedBall (0 : Vec d) (n : ℝ) :=
    hR.trans ((Metric.ball_subset_ball hn.le).trans Metric.ball_subset_closedBall)
  have hmeas : AEStronglyMeasurable (fun x => f (translate x ω))
      (volume.restrict K) :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  exact (integrable_norm_rpow_iff hmeas hp0 hpt).mp
    ((hω n).mono_set hKn)

private theorem c15_memLp_affine_unit_ball {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E} {p : ℝ≥0∞}
    (z : Vec d) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : MemLp f p (PDE.volumeOn (PDE.euclideanBall z ρ))) :
    MemLp (fun x => f (z + ρ • x)) p
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1)) := by
  have hmap : MemLp f p (Measure.map (fun x => ρ • x + z)
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1))) := by
    rw [PDE.DGNM.map_affineScale_volumeOn z hρ,
      PDE.DGNM.translateSet_smul_euclideanBall z hρ, mul_one]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  simpa only [Function.comp_def, add_comm] using
    hmap.comp_of_map (continuous_id.const_smul ρ |>.add continuous_const).measurable.aemeasurable

private theorem c15_continuous_memLp_top_on_unit_ball {d : ℕ}
    {f : Vec d → ℂ} (hf : Continuous f) :
    MemLp f ∞ (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨C, hC⟩ := (PDE.isCompact_euclideanClosedBall (0 : Vec d)
    (by norm_num : (0 : ℝ) ≤ 1)).exists_bound_of_continuousOn hf.continuousOn
  apply memLp_top_of_bound hf.aestronglyMeasurable C
  filter_upwards [ae_restrict_mem (PDE.isOpen_euclideanBall (0 : Vec d) 1).measurableSet]
    with x hx
  exact hC x (PDE.euclideanBall_subset_euclideanClosedBall (0 : Vec d) 1 hx)

/-- The actual rescaled scalar and vector forcing have finite spatial
moments. This uses value and generator moments only; the gradient does not
occur in any premise. The event precedes every center, scale and projection. -/
theorem clock_generator_spatial_rescaled_forcing_memLp {d : ℕ}
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hpt : p ≠ ∞)
    (hf : MemLp (f : FieldPair d → ℂ) p (reducedLaw Q))
    (hg : MemLp (g : FieldPair d → ℂ) p (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q,
      let H := fun x => g (translate x ω) + ζ * (∑ j,
        (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)
      let B := fun x j => ζ * (ω.1 x j i : ℂ) * f (translate x ω)
      ∀ (z : Vec d) (ρ : ℝ), 0 < ρ → ∀ (K : ℝ) (L : ℂ →L[ℝ] ℝ),
        MemLp (fun x => -2 * K * ρ * L (H (z + ρ • x))) p
          (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1)) ∧
        ∀ j, MemLp (fun x => -2 * K * L (B (z + ρ • x) j)) p
          (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1)) := by
  letI := reducedLaw_probability Q
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [hM Q hQ,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      f hp0 hpt hf,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      g hp0 hpt hg] with ω hs hfl hgl
  intro H B z ρ hρ K L
  have hloc {u : Vec d → ℂ}
      (hu : ∀ K : Set (Vec d), IsCompact K → MemLp u p (volume.restrict K)) :=
    c15_memLp_affine_unit_ball z hρ
      ((hu _ (PDE.isCompact_euclideanClosedBall z hρ.le)).mono_measure
        (Measure.restrict_mono_set volume (PDE.euclideanBall_subset_euclideanClosedBall z ρ)))
  have hfr := hloc hfl
  have hgr := hloc hgl
  have hscale : Continuous (fun x : Vec d => z + ρ • x) :=
    continuous_const.add (continuous_id.const_smul ρ)
  have hder : Continuous (fun x => ζ * (∑ j : Fin d,
      (coordinateDerivative j (fun y => ω.1 y j i) (z + ρ • x) : ℂ))) := by
    apply continuous_const.mul
    exact continuous_finsetSum _ fun j _ => Complex.continuous_ofReal.comp
      (((hs.1.1 j i).continuous_fderiv (by simp)).clm_apply continuous_const |>.comp hscale)
  have hH : MemLp (fun x => H (z + ρ • x)) p
      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1)) :=
    hgr.add ((c15_continuous_memLp_top_on_unit_ball hder).mul hfr)
  refine ⟨(L.comp_memLp' hH).const_mul (-2 * K * ρ), ?_⟩
  intro j
  have hcoeff : Continuous (fun x => ζ * (ω.1 (z + ρ • x) j i : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp ((hs.1.1 j i).continuous.comp hscale))
  exact (L.comp_memLp'
    ((c15_continuous_memLp_top_on_unit_ball hcoeff).mul hfr)).const_mul (-2 * K)


/-- Interior regularity for both literal real components of the actual clock
orbit. The scale and elliptic constants precede the law. The right hand side
contains only the actual scalar/vector forcing and the local quadratic energy. -/
theorem clock_generator_spatial_rescaled_interior_estimate
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ K C ρ : ℝ, 1 ≤ K ∧ 1 ≤ C ∧ 0 < ρ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ)
        (f g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsComplexGeneratorPair Q i ζ f g →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
        MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        ∀ᵐ ω ∂reducedLaw Q,
          let H := fun x => g (translate x ω) + ζ * (∑ j,
            (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)
          let B := fun x j => ζ * (ω.1 x j i : ℂ) * f (translate x ω)
          ∀ (z : Vec d) (b : Bool),
            let L := if b then Complex.reCLM else Complex.imCLM
            let V := fun x j => L (G j (translate (z + ρ • x) ω))
            let S := fun x => -2 * K * ρ * L (H (z + ρ • x))
            let F := fun x j => -2 * K * L (B (z + ρ • x) j)
            MemLp (fun x => PDE.vecEuclideanNorm (V x)) (ENNReal.ofReal p)
                (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))) ∧
            (eLpNorm (fun x => PDE.vecEuclideanNorm (V x)) (ENNReal.ofReal p)
                (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ)))).toReal ≤
              C * (Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) 1)
                    (fun x => PDE.vecNormSq (V x))) +
                p * (((volume (PDE.euclideanBall (0 : Vec d) 1))⁻¹ ^
                  (1 / ENNReal.ofReal p).toReal).toReal *
                  ((((2 : ℝ) ^ d + 1) * 2) *
                    (eLpNorm S (ENNReal.ofReal p)
                      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1))).toReal +
                    (eLpNorm (PDE.toHilbertVecField F) (ENNReal.ofReal p)
                      (PDE.volumeOn (PDE.euclideanBall (0 : Vec d) 1))).toReal))) := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨K, hK, hs⟩ := clock_normalized_coefficient_small_scale d D
  obtain ⟨C, hC, hCZ⟩ := clock_unit_ball_scalar_vector_regularity d (by omega)
    (K ^ 2) (by nlinarith)
  have hCp : 0 < C * p := mul_pos (by linarith) (by linarith)
  obtain ⟨ρ, hρ, hcoef⟩ := hs (1 / (C * p)) (one_div_pos.mpr hCp)
  refine ⟨K, C, ρ, hK, hC, hρ, ?_⟩
  intro Q hQ i ζ f g G hfg hG hf hg
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  filter_upwards [hcoef Q, clock_gradient_spatial_rescaled_h1 Q hG,
    clock_generator_spatial_rescaled_value_forcing D Q hQ i ζ hfg hG,
    clock_generator_spatial_rescaled_forcing_memLp D Q hQ i ζ f g hp0
      ENNReal.ofReal_ne_top hf hg] with ω hcoeff h1 he hm
  intro H B z b L V S F
  let U := PDE.euclideanBall (0 : Vec d) 1
  obtain ⟨u, v, _, hu, _, hv⟩ := h1 z ρ hρ
  have hrep : ∃ w : PDE.H1Function U, w.grad = V := by
    cases b with
    | false => exact ⟨v, funext fun x => funext fun j => hv x j⟩
    | true => exact ⟨u, funext fun x => funext fun j => hu x j⟩
  obtain ⟨w, hw⟩ := hrep
  have hS : MemLp S (ENNReal.ofReal p) (PDE.volumeOn U) :=
    (hm z ρ hρ K L).1
  have hF : PDE.GradMemLpOn U (ENNReal.ofReal p) F := (hm z ρ hρ K L).2
  let s : PDE.ScalarLp U (ENNReal.ofReal p) := hS.toLp S
  let vF : PDE.HilbertVectorLp U (ENNReal.ofReal p) := hF.toHilbertVectorLp
  have heq (φ : PDE.WeakTestFunction U) :
      (∫ x in U, PDE.vecDot
        (PDE.matVecMul (fun j k => K * ω.1 (z + ρ • x) j k) (w.grad x)) (φ.grad x)) =
      (∫ x in U, s x * φ x) + ∫ x in U, PDE.vecDot (vF x).toVec (φ.grad x) := by
    rw [hw]
    have hsint : (∫ x in U, s x * φ x) = ∫ x in U, S x * φ x := by
      apply integral_congr_ae
      filter_upwards [hS.coeFn_toLp] with x hx
      exact congrArg (fun t => t * φ x) hx
    have hFint : (∫ x in U, PDE.vecDot (vF x).toVec (φ.grad x)) =
        ∫ x in U, PDE.vecDot (F x) (φ.grad x) := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toHilbertVectorLp] with x hx
      change PDE.vecDot (vF x).toVec (φ.grad x) = _
      rw [show vF x = PDE.toHilbertVecField F x from hx]
      rfl
    rw [hsint, hFint]
    exact he z ρ hρ K L φ
  obtain ⟨_, hgrad, hbound⟩ := hCZ p hp
    (fun x j k => K * ω.1 (z + ρ • x) j k)
    (fun j k => ((hcoeff z).2.1 j k).measurable.aemeasurable)
    (Filter.Eventually.of_forall (hcoeff z).1)
    (by
      filter_upwards [ae_restrict_mem (PDE.isOpen_euclideanBall (0 : Vec d) 1).measurableSet]
        with x hx
      exact (hcoeff z).2.2 x hx)
    w s vF heq
  simp only [PDE.euclideanFieldLpMeanNormOn, PDE.lpMeanNormOn_eq_toReal] at hbound
  rw [hw] at hgrad hbound
  refine ⟨hgrad, ?_⟩
  have hsNorm : ‖s‖ = (eLpNorm S (ENNReal.ofReal p) (PDE.volumeOn U)).toReal :=
    Lp.norm_toLp S hS
  have hFNorm : ‖vF‖ =
      (eLpNorm (PDE.toHilbertVecField F) (ENNReal.ofReal p) (PDE.volumeOn U)).toReal :=
    Lp.norm_toLp _ (PDE.gradMemLpOn_iff_memLp_toHilbertVecField.mp hF)
  simpa only [PDE.euclideanFieldLpMeanNormOn, PDE.lpMeanNormOn_eq_toReal,
    PDE.eLpMeanNormOn, hsNorm, hFNorm] using hbound


/-- Structural pointwise bounds on the literal scalar/vector sources. These
hold at every spatial point on one event, for arbitrary value and generator
observables, and introduce no gradient-moment premise. -/
theorem clock_spatial_forcing_pointwise_bound (d : ℕ) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q),
      ∀ᵐ ω ∂reducedLaw Q, ∀ (i : Fin d) (ζ : ℂ)
        (f g : FieldPair d → ℂ) (x : Vec d),
        ‖g (translate x ω) + ζ * (∑ j,
            (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)‖ ≤
          ‖g (translate x ω)‖ + ‖ζ‖ * B * ‖f (translate x ω)‖ ∧
        ∀ j, ‖ζ * (ω.1 x j i : ℂ) * f (translate x ω)‖ ≤
          ‖ζ‖ * B * ‖f (translate x ω)‖ := by
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  let B := K + (d : ℝ) * |M 1| + 1
  have hdb : (d : ℝ) * |M 1| ≤ B := by dsimp [B]; linarith
  have hkb : K ≤ B := by
    dsimp [B]
    linarith [mul_nonneg (Nat.cast_nonneg d) (abs_nonneg (M 1))]
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro Q hQ
  filter_upwards [hM Q hQ, c4_ae_reduced_physical_elliptic Q]
    with ω hs hell
  intro i ζ f g x
  have hder (j : Fin d) :
      |coordinateDerivative j (fun y => ω.1 y j i) x| ≤ |M 1| := by
    have h := c15_coefficient_jet_bound hs [j] (by simp) j i x
    exact h.trans (le_abs_self _)
  have hsum : ‖∑ j : Fin d,
      (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)‖ ≤ B := by
    calc
      _ ≤ ∑ j : Fin d, ‖(coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, |M 1| := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hder j
      _ = (d : ℝ) * |M 1| := by simp
      _ ≤ B := hdb
  have ha (j : Fin d) : |ω.1 x j i| ≤ B := by
    apply le_trans ?_ hkb
    apply abs_entry_le_of_quadratic_bounds hK (ω.1 x) (hell x).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
        ((hell x).2 ξ).1
    · exact fun ξ => ((hell x).2 ξ).2
  constructor
  · calc
      _ ≤ ‖g (translate x ω)‖ +
          ‖ζ * (∑ j : Fin d, (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) *
            f (translate x ω)‖ := norm_add_le _ _
      _ = ‖g (translate x ω)‖ + ‖ζ‖ *
          ‖∑ j : Fin d, (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)‖ *
            ‖f (translate x ω)‖ := by rw [norm_mul, norm_mul]
      _ ≤ _ := by gcongr
  · intro j
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    exact ha j


private lemma c15_lintegral_stationary_spatial_moment
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (F : FieldPair d → E) (hF : Measurable F)
    (κ : Measure (Vec d)) [SFinite κ] (p : ℝ) :
    (∫⁻ ω, ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂κ ∂Q) =
      κ Set.univ * (∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q) := by
  have hm : Measurable (fun q : FieldPair d × Vec d => ‖F (translate q.2 q.1)‖ₑ ^ p) :=
    (hF.comp (Probability.continuous_translate.measurable.comp measurable_swap)).enorm.pow_const p
  rw [lintegral_lintegral_swap hm.aemeasurable]
  calc
    _ = ∫⁻ _x : Vec d, ∫⁻ ω, ‖F ω‖ₑ ^ p ∂Q ∂κ := by
      apply lintegral_congr
      intro x
      exact (measurePreserving_translate Q hQ x).lintegral_comp (hF.enorm.pow_const p)
    _ = _ := by rw [lintegral_const, mul_comm]

private lemma c15_eLpNorm_pow_eq_lintegral
    {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
    (p : ℝ) (hp : 0 < p) (ν : Measure X) (f : X → V)
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f (ENNReal.ofReal p) ν ^ p = ∫⁻ x, ‖f x‖ₑ ^ p ∂ν := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul]
  simp [one_div, hp.ne']

/-- Recovery of a stationary moment from a genuine local spatial `L^p` norm
bound. Local membership is explicit, so a nonintegrable Bochner integral or
`ENNReal.toReal` convention cannot yield a spurious moment. -/
theorem clock_stationary_moment_of_local_lp_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (κ : Measure (Vec d)) [IsProbabilityMeasure κ]
    (F : FieldPair d → E) (hF : Measurable F) (p : ℝ) (hp : 0 < p)
    (R : FieldPair d → ℝ) (hR : MemLp R (ENNReal.ofReal p) Q)
    (hlocal : ∀ᵐ ω ∂Q, MemLp (fun x => F (translate x ω)) (ENNReal.ofReal p) κ)
    (hbound : ∀ᵐ ω ∂Q,
      (eLpNorm (fun x => F (translate x ω)) (ENNReal.ofReal p) κ).toReal ≤ R ω) :
    MemLp F (ENNReal.ofReal p) Q ∧
      eLpNorm F (ENNReal.ofReal p) Q ≤ eLpNorm R (ENNReal.ofReal p) Q := by
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hpoint : ∀ᵐ ω ∂Q,
      (∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂κ) ≤ ‖R ω‖ₑ ^ p := by
    filter_upwards [hlocal, hbound] with ω hloc hb
    rw [← c15_eLpNorm_pow_eq_lintegral p hp κ _ hloc.aestronglyMeasurable]
    apply ENNReal.rpow_le_rpow _ hp.le
    calc
      _ = ENNReal.ofReal
          (eLpNorm (fun x => F (translate x ω)) (ENNReal.ofReal p) κ).toReal :=
        (ENNReal.ofReal_toReal hloc.eLpNorm_ne_top).symm
      _ ≤ ENNReal.ofReal (R ω) := ENNReal.ofReal_le_ofReal hb
      _ ≤ ENNReal.ofReal ‖R ω‖ := ENNReal.ofReal_le_ofReal (Real.le_norm_self _)
      _ = ‖R ω‖ₑ := ofReal_norm_eq_enorm _
  have hmoment := lintegral_mono_ae hpoint
  rw [c15_lintegral_stationary_spatial_moment Q hQ F hF κ p,
    measure_univ, one_mul, ← c15_eLpNorm_pow_eq_lintegral p hp Q F hF.aestronglyMeasurable,
    ← c15_eLpNorm_pow_eq_lintegral p hp Q R hR.aestronglyMeasurable] at hmoment
  have hnorm := (ENNReal.rpow_le_rpow_iff hp).mp hmoment
  exact ⟨hnorm.trans_lt hR.eLpNorm_lt_top, hnorm⟩


/-- The local spatial `L^p` norm has exactly the original stationary `L^p`
moment. The local membership assumption is supplied by compact localization,
and ensures that taking the real norm loses no infinite values. -/
theorem clock_stationary_local_lp_norm_moment
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (κ : Measure (Vec d)) [IsProbabilityMeasure κ]
    (F : FieldPair d → E) (hF : Measurable F) (p : ℝ) (hp : 0 < p)
    (hglobal : MemLp F (ENNReal.ofReal p) Q)
    (hlocal : ∀ᵐ ω ∂Q, MemLp (fun x => F (translate x ω)) (ENNReal.ofReal p) κ) :
    let N := fun ω => (eLpNorm (fun x => F (translate x ω)) (ENNReal.ofReal p) κ).toReal
    MemLp N (ENNReal.ofReal p) Q ∧
      eLpNorm N (ENNReal.ofReal p) Q = eLpNorm F (ENNReal.ofReal p) Q := by
  intro N
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp)
  have hshift : Measurable (fun q : FieldPair d × Vec d => F (translate q.2 q.1)) :=
    hF.comp (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_fst))
  have hN : Measurable N := by
    have he : N = fun ω =>
        ((∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂κ) ^ (1 / p)).toReal := by
      funext ω
      dsimp [N]
      have hsω : Measurable (fun x => F (translate x ω)) :=
        hshift.comp measurable_prodMk_left
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
        hsω.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
    rw [he]
    exact ((hshift.enorm.pow_const p).lintegral_prod_right'.pow_const _).ennreal_toReal
  have hpoint : ∀ᵐ ω ∂Q,
      ‖N ω‖ₑ ^ p = ∫⁻ x, ‖F (translate x ω)‖ₑ ^ p ∂κ := by
    filter_upwards [hlocal] with ω hloc
    rw [show ‖N ω‖ₑ = eLpNorm (fun x => F (translate x ω)) (ENNReal.ofReal p) κ by
      exact (Real.enorm_eq_ofReal ENNReal.toReal_nonneg).trans
        (ENNReal.ofReal_toReal hloc.eLpNorm_ne_top)]
    exact c15_eLpNorm_pow_eq_lintegral p hp κ _ hloc.aestronglyMeasurable
  have heq : eLpNorm N (ENNReal.ofReal p) Q = eLpNorm F (ENNReal.ofReal p) Q := by
    apply (ENNReal.rpow_left_injective hp.ne')
    change eLpNorm N (ENNReal.ofReal p) Q ^ p = eLpNorm F (ENNReal.ofReal p) Q ^ p
    rw [c15_eLpNorm_pow_eq_lintegral p hp Q N hN.aestronglyMeasurable, lintegral_congr_ae hpoint,
      c15_lintegral_stationary_spatial_moment Q hQ F hF κ p,
      measure_univ, one_mul, c15_eLpNorm_pow_eq_lintegral p hp Q F hF.aestronglyMeasurable]
  exact ⟨heq.trans_lt hglobal.eLpNorm_lt_top, heq⟩

private lemma c15_compact_weight_integral_le
    {d : ℕ} {K : Set (Vec d)} (hK : IsCompact K)
    {F : Vec d → ℝ} (hF : IntegrableOn F K volume) (hFpos : ∀ x, 0 ≤ F x)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hz : ∀ x, x ∉ K → ψ x = 0)
    {C : ℝ} (hb : ∀ x ∈ K, ψ x ≤ C) :
    (∫ x, ψ x * F x) ≤ C * ∫ x in K, F x := by
  have hi : IntegrableOn (fun x => ψ x * F x) K volume :=
    IntegrableOn.continuousOn_mul hψ.continuousOn hF hK
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := K) (f := fun x => ψ x * F x)
    (fun x hx => by rw [hz x hx, zero_mul]), ← integral_const_mul]
  apply integral_mono_ae hi (hF.const_mul C)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact mul_le_mul_of_nonneg_right (hb x hx) (hFpos x)

/-- Spatial Caccioppoli for the actual generator pair. The radius and force
cap precede the law, and only value/generator squares occur on the outer ball. -/
theorem clock_generator_spatial_ball_energy
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (A ρ : ℝ) (hA : 0 ≤ A) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ A →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsComplexGeneratorPair Q i ζ f g →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
    ∀ᵐ ω ∂reducedLaw Q, ∀ z : Vec d,
      (∫ x in PDE.euclideanBall z ρ, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
        C * ∫ x in {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ},
          (‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2) := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  obtain ⟨B, hB, hcut⟩ := exists_physical_euclidean_cutoff d
  let E := A ^ 2 + (d : ℝ) * (B / ρ) ^ 2
  let C₀ := 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨4 * L * (1 + C₀ * E), by positivity, ?_⟩
  intro Q i ζ hζ f g G hfg hG
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  filter_upwards [hfg.ae_physical_cutoff_energy hG,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))] with ω henergy hf hg hgrad
  intro z
  obtain ⟨φ, hφ, hrange, hone, hzero, hD⟩ := hcut z ρ hρ
  let K := {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (2 * ρ)
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupp : tsupport φ ⊆ K := physical_cutoff_tsupport_subset hzero
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupp hm)
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  have hcf := (memLp_two_iff_integrable_sq_norm (hf K hK).aestronglyMeasurable).mp (hf K hK)
  have hcg := (memLp_two_iff_integrable_sq_norm (hg K hK).aestronglyMeasurable).mp (hg K hK)
  have hcgD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hgrad j K hK).aestronglyMeasurable).mp
      (hgrad j K hK))
  have hpair := integrable_physical_cutoff_pairing
    (fun K hK => (hf K hK).star) (fun K hK => (hg K hK).neg) hφ
  simp only [Pi.star_apply, Pi.neg_apply] at hpair
  have hp : (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω))).re ≤
      ∫ x in K, (‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2) := by
    have hre := Complex.reCLM.integral_comp_comm hpair
    change (∫ x, ((φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω))).re) =
      (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re at hre
    rw [← hre, ← setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := K) (f := fun x =>
        ((φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re)
      (fun x hx => by simp [hz x hx])]
    apply integral_mono_ae hpair.re.restrict (hcf.add hcg)
    filter_upwards with x
    calc
      _ ≤ ‖(φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))‖ :=
        Complex.re_le_norm _
      _ = φ x ^ 2 * ‖f (translate x ω)‖ * ‖g (translate x ω)‖ := by
        simp [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      _ ≤ ‖f (translate x ω)‖ * ‖g (translate x ω)‖ := by
        have hs : φ x ^ 2 ≤ 1 := by nlinarith [hrange x]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hs (norm_nonneg (f (translate x ω))))
          (norm_nonneg (g (translate x ω)))
      _ ≤ _ := by
        change ‖f (translate x ω)‖ * ‖g (translate x ω)‖ ≤
          ‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2
        nlinarith [sq_nonneg (‖f (translate x ω)‖ - ‖g (translate x ω)‖),
          sq_nonneg ‖f (translate x ω)‖, sq_nonneg ‖g (translate x ω)‖]
  have hcont j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have herr := c15_compact_weight_integral_le hK hcf (fun x => sq_nonneg _)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hcont j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx]) (C := E) (by
      intro x hx
      have hφsq : φ x ^ 2 ≤ 1 := by nlinarith [hrange x]
      have hsq : ‖ζ‖ ^ 2 ≤ A ^ 2 := sq_le_sq₀ (norm_nonneg _) hA |>.mpr hζ
      have hder j : (coordinateDerivative j φ x) ^ 2 ≤ (B / ρ) ^ 2 := by
        simpa only [← sq, sq_abs] using
          mul_self_le_mul_self (abs_nonneg (coordinateDerivative j φ x)) (hD j x)
      have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hder j)
      dsimp [E]
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] using add_le_add
          ((mul_le_mul_of_nonneg_left hφsq (sq_nonneg ‖ζ‖)).trans (by simpa using hsq)) hsum)
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at herr
  have hinner : (∫ x in PDE.euclideanBall z ρ, ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
      ∫ x, φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2 := by
    have hw : IntegrableOn (fun x => φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2) K volume :=
      IntegrableOn.continuousOn_mul (hφ.1.continuous.pow 2).continuousOn hcgD hK
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (μ := volume) (s := K)
      (f := fun x => φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2)
      (fun x hx => by rw [hz x hx]; simp)]
    have heq : (∫ x in PDE.euclideanBall z ρ, ∑ j, ‖G j (translate x ω)‖ ^ 2) =
        ∫ x in PDE.euclideanBall z ρ, φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2 := by
      apply setIntegral_congr_fun (PDE.isOpen_euclideanBall z ρ).measurableSet
      intro x hx
      change (∑ j, ‖G j (translate x ω)‖ ^ 2) =
        φ x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2
      rw [hone x ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hx).le]
      simp
    rw [heq]
    apply setIntegral_mono_set hw
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
    exact Eventually.of_forall (fun x hx => by
      change euclideanNorm (x - z) ≤ 2 * ρ
      have hxρ : euclideanNorm (x - z) ≤ ρ :=
        ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hx).le
      linarith)
  have hnon : 0 ≤ ∫ x in K, ‖g (translate x ω)‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have htotal : (∫ x in K, ‖f (translate x ω)‖ ^ 2) ≤
      ∫ x in K, (‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2) := by
    rw [integral_add hcf hcg]
    linarith
  have hupper := (henergy φ hφ).trans (add_le_add hp (mul_le_mul_of_nonneg_left
    (herr.trans (mul_le_mul_of_nonneg_left htotal hE)) hC₀))
  have hm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 4 * L by positivity)
  have hinv : (4 * L) * (L⁻¹ / 4) = 1 := by field_simp [hL.ne']
  change (4 * L) * ((L⁻¹ / 4) * _) ≤ _ at hm
  rw [← mul_assoc, hinv, one_mul] at hm
  convert hinner.trans hm using 1 <;> ring

private lemma c15_lp_norm_bound_of_pointwise_sources
    {X E F H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup H]
    (ν : Measure X) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (f : X → E) (g : X → F) (h : X → H)
    (hf : MemLp f p ν) (hg : MemLp g p ν) (hh : AEStronglyMeasurable h ν)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ᵐ x ∂ν, ‖h x‖ ≤ a * ‖f x‖ + b * ‖g x‖) :
    MemLp h p ν ∧ (eLpNorm h p ν).toReal ≤
      a * (eLpNorm f p ν).toReal + b * (eLpNorm g p ν).toReal := by
  let A : X → ℝ := fun x => a * ‖f x‖
  let B : X → ℝ := fun x => b * ‖g x‖
  have hA : MemLp A p ν := hf.norm.const_mul a
  have hB : MemLp B p ν := hg.norm.const_mul b
  have hsum : MemLp (A + B) p ν := hA.add hB
  have hm : eLpNorm h p ν ≤ eLpNorm (A + B) p ν :=
    eLpNorm_mono_ae_real hh hbound
  have hAe : eLpNorm A p ν = ENNReal.ofReal a * eLpNorm f p ν := by
    change eLpNorm (a • fun x => ‖f x‖) p ν = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal ha,
      eLpNorm_norm f hf.aestronglyMeasurable]
  have hBe : eLpNorm B p ν = ENNReal.ofReal b * eLpNorm g p ν := by
    change eLpNorm (b • fun x => ‖g x‖) p ν = _
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hb,
      eLpNorm_norm g hg.aestronglyMeasurable]
  refine ⟨hm.trans_lt hsum.eLpNorm_lt_top, ?_⟩
  calc
    _ ≤ (eLpNorm (A + B) p ν).toReal := ENNReal.toReal_mono hsum.eLpNorm_ne_top hm
    _ ≤ (eLpNorm A p ν + eLpNorm B p ν).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hA.eLpNorm_ne_top, hB.eLpNorm_ne_top⟩)
        (eLpNorm_add_le hp)
    _ = _ := by
      rw [ENNReal.toReal_add hA.eLpNorm_ne_top hB.eLpNorm_ne_top, hAe, hBe,
        ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha,
        ENNReal.toReal_ofReal hb]

/-- The rescaled real scalar source and Euclidean vector source satisfy
literal value/generator bounds for both real and imaginary projections. -/
theorem clock_spatial_rescaled_forcing_pointwise_bound (d : ℕ) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q),
    ∀ᵐ ω ∂reducedLaw Q, ∀ (i : Fin d) (ζ : ℂ)
      (f g : FieldPair d → ℂ) (z : Vec d) (ρ K : ℝ)
      (L : ℂ →L[ℝ] ℝ), (∀ w, |L w| ≤ ‖w‖) → ∀ x : Vec d,
      |(-2 * K * ρ) * L (g (translate (z + ρ • x) ω) +
          ζ * (∑ j, (coordinateDerivative j (fun y => ω.1 y j i) (z + ρ • x) : ℂ)) *
            f (translate (z + ρ • x) ω))| ≤
        (2 * |K| * |ρ|) * (‖g (translate (z + ρ • x) ω)‖ +
          ‖ζ‖ * B * ‖f (translate (z + ρ • x) ω)‖) ∧
      ‖PDE.toHilbertVecField (fun y j => (-2 * K) *
          L (ζ * (ω.1 (z + ρ • y) j i : ℂ) * f (translate (z + ρ • y) ω))) x‖ ≤
        (2 * |K| * (d : ℝ) * ‖ζ‖ * B) * ‖f (translate (z + ρ • x) ω)‖ := by
  obtain ⟨B, hB, hb⟩ := clock_spatial_forcing_pointwise_bound d D
  refine ⟨B, hB, ?_⟩
  intro Q hQ
  filter_upwards [hb Q hQ] with ω hω
  intro i ζ f g z ρ K L hL x
  have hs := (hL _).trans (hω i ζ f g (z + ρ • x)).1
  have hv (j : Fin d) :
      |(-2 * K) * L (ζ * (ω.1 (z + ρ • x) j i : ℂ) *
        f (translate (z + ρ • x) ω))| ≤
      (2 * |K|) * (‖ζ‖ * B * ‖f (translate (z + ρ • x) ω)‖) := by
    rw [abs_mul]
    have h := mul_le_mul_of_nonneg_left
      ((hL _).trans ((hω i ζ f g (z + ρ • x)).2 j))
      (show 0 ≤ 2 * |K| by positivity)
    simpa [abs_mul] using h
  constructor
  · calc
      _ = (2 * |K| * |ρ|) * |L (g (translate (z + ρ • x) ω) +
          ζ * (∑ j, (coordinateDerivative j (fun y => ω.1 y j i) (z + ρ • x) : ℂ)) *
            f (translate (z + ρ • x) ω))| := by
        simp [abs_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (by positivity)
  · rw [PDE.norm_toHilbertVecField_apply]
    calc
      _ ≤ ∑ j : Fin d, |(-2 * K) * L (ζ * (ω.1 (z + ρ • x) j i : ℂ) *
          f (translate (z + ρ • x) ω))| := PDE.vecEuclideanNorm_le_sum_abs _
      _ ≤ ∑ _j : Fin d, (2 * |K|) *
          (‖ζ‖ * B * ‖f (translate (z + ρ • x) ω)‖) :=
        Finset.sum_le_sum (fun j _ => hv j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]; ring


/-- Uniform stationary `L^p` bounds for the actual scalar and coordinate
forcing terms, with the constant chosen before the environment law. -/
theorem c15_clock_forcing_norms (d : ℕ) (D : StructuralData d) (p : ℝ)
    (hp : 2 ≤ p) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
        MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      let H : FieldPair d → ℂ := fun ω => g ω + ζ *
        (∑ j : Fin d, (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ)) * f ω
      let F : Fin d → FieldPair d → ℂ := fun j ω => ζ * (ω.1 0 j i : ℂ) * f ω
      MemLp H (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm H (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C *
          ((eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
            (eLpNorm (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ∧
      ∀ j : Fin d, MemLp (F j) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (F j) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C *
          (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  classical
  obtain ⟨M, hM, hbound⟩ := clock_spatial_forcing_pointwise_bound d D
  have hBM : 0 ≤ B * M := mul_nonneg hB hM.le
  refine ⟨1 + B * M, by linarith, ?_⟩
  intro Q hQ i ζ hζ f g hf hg H F
  have hpp : 1 ≤ ENNReal.ofReal p := by
    exact ENNReal.one_le_ofReal.mpr (by linarith)
  let a (j k : Fin d) (ω : FieldPair d) : C(Vec d, ℝ) :=
    ⟨fun x => ω.1 x j k,
      (continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)⟩
  have ham (j k : Fin d) : @Measurable (FieldPair d) C(Vec d, ℝ)
      inferInstance (borel _) (a j k) := by
    apply measurable_continuousMap_of_evaluations
    intro x
    have heval : Continuous (fun ω : FieldPair d => ω.1 x) :=
      (continuous_eval_const x).comp continuous_fst
    exact ((continuous_apply k).comp ((continuous_apply j).comp heval)).measurable
  have hder : Measurable (fun ω : FieldPair d =>
      ∑ j : Fin d, (coordinateDerivative j (fun y => ω.1 y j i) 0 : ℂ)) :=
    Finset.measurable_sum _ (fun j _ => Complex.measurable_ofReal.comp
      (Sharpness.measurable_coordinateDerivative_of_measurable_continuousMap
        (a j i) (ham j i) j 0))
  have hHm : AEStronglyMeasurable H (reducedLaw Q) :=
    hg.aestronglyMeasurable.add
      ((hder.const_mul ζ).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hHb : ∀ᵐ ω ∂reducedLaw Q,
      ‖H ω‖ ≤ (B * M) * ‖f ω‖ + 1 * ‖g ω‖ := by
    filter_upwards [hbound Q hQ] with ω hω
    have h := (hω i ζ f g 0).1
    simp only [translate_zero] at h
    calc
      _ ≤ ‖g ω‖ + ‖ζ‖ * M * ‖f ω‖ := h
      _ ≤ ‖g ω‖ + B * M * ‖f ω‖ := by gcongr
      _ = _ := by ring
  obtain ⟨hH, hHn⟩ := c15_lp_norm_bound_of_pointwise_sources
    (reducedLaw Q) (ENNReal.ofReal p) hpp f g H hf hg hHm
    (B * M) 1 hBM (by norm_num) hHb
  refine ⟨hH, ?_, ?_⟩
  · nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)),
      ENNReal.toReal_nonneg (a := eLpNorm g (ENNReal.ofReal p) (reducedLaw Q))]
  · intro j
    have ha : Measurable (fun ω : FieldPair d => (ω.1 0 j i : ℂ)) := by
      exact (by fun_prop : Continuous (fun ω : FieldPair d => (ω.1 0 j i : ℂ))).measurable
    have hFm : AEStronglyMeasurable (F j) (reducedLaw Q) :=
      (ha.const_mul ζ).aestronglyMeasurable.mul hf.aestronglyMeasurable
    have hFb : ∀ᵐ ω ∂reducedLaw Q,
        ‖F j ω‖ ≤ (B * M) * ‖f ω‖ + 0 * ‖g ω‖ := by
      filter_upwards [hbound Q hQ] with ω hω
      have h := (hω i ζ f g 0).2 j
      simp only [translate_zero] at h
      calc
        _ ≤ ‖ζ‖ * M * ‖f ω‖ := h
        _ ≤ B * M * ‖f ω‖ := by gcongr
        _ = _ := by ring
    obtain ⟨hF, hFn⟩ := c15_lp_norm_bound_of_pointwise_sources
      (reducedLaw Q) (ENNReal.ofReal p) hpp f g (F j) hf hg hFm
      (B * M) 0 hBM (by norm_num) hFb
    refine ⟨hF, ?_⟩
    simp only [zero_mul, add_zero] at hFn
    nlinarith [ENNReal.toReal_nonneg (a := eLpNorm f (ENNReal.ofReal p) (reducedLaw Q))]


private lemma c15_local_square_integral_le_lp
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (R : ℝ) (hR : 0 < R) (p : ℝ) (hp : 2 ≤ p) (f : Vec d → E)
    (hf : MemLp f (ENNReal.ofReal p) (PDE.volumeOn (PDE.euclideanBall 0 R))) :
    (∫ x in PDE.euclideanBall 0 R, ‖f x‖ ^ 2) ≤
      (volume (PDE.euclideanBall (0 : Vec d) R)).toReal *
        (eLpNorm f (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 R))).toReal ^ 2 := by
  have hpos := PDE.volume_euclideanBall_pos (0 : Vec d) hR
  have htop : volume (PDE.euclideanBall (0 : Vec d) R) < ∞ :=
    lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top _ hR.le)
  letI := PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hpos htop
  have hpn := PDE.memLp_normalizedVolumeOn_of_memLpOn hf hpos
  have hpp : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have htwo := hpn.mono_exponent hpp
  have hnorm : (eLpNorm f 2
      (PDE.normalizedVolumeOn (PDE.euclideanBall 0 R))).toReal ≤
      (eLpNorm f (ENNReal.ofReal p)
        (PDE.normalizedVolumeOn (PDE.euclideanBall 0 R))).toReal :=
    ENNReal.toReal_mono hpn.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hpp)
  have heq : (eLpNorm f 2
      (PDE.normalizedVolumeOn (PDE.euclideanBall 0 R))).toReal ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂PDE.normalizedVolumeOn (PDE.euclideanBall 0 R) := by
    rw [← eLpNorm_norm f htwo.aestronglyMeasurable]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq htwo.norm
  calc
    _ = (volume (PDE.euclideanBall (0 : Vec d) R)).toReal *
        (eLpNorm f 2
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 R))).toReal ^ 2 := by
      rw [heq, ← smul_eq_mul, ← integral_smul_measure,
        PDE.volume_smul_normalizedVolumeOn_eq_volumeOn hpos htop]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg).mpr hnorm)
      ENNReal.toReal_nonneg

/-- The rescaled quadratic gradient term is controlled by actual local value
and generator moments on a larger ball. -/
theorem clock_generator_spatial_rescaled_energy_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p A ρ : ℝ)
    (hp : 2 ≤ p) (hA : 0 ≤ A) (hρ : 0 < ρ) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
        (ζ : ℂ), ‖ζ‖ ≤ A →
      ∀ (f g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsComplexGeneratorPair Q i ζ f g →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
        MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℂ →L[ℝ] ℝ, (∀ w, |L w| ≤ ‖w‖) →
        Real.sqrt (PDE.integralAverage (PDE.euclideanBall (0 : Vec d) 1)
          (fun x => PDE.vecNormSq (fun j => L (G j (translate (ρ • x) ω))))) ≤
        C * ((eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal +
          (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
            (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal) := by
  obtain ⟨E, hE, henergy⟩ := clock_generator_spatial_ball_energy d hd D A ρ hA hρ
  let k := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal⁻¹ *
    (ρ ^ d)⁻¹ * E * (volume (PDE.euclideanBall (0 : Vec d) (3 * ρ))).toReal
  have hk : 0 ≤ k := by dsimp [k]; positivity
  refine ⟨Real.sqrt k + 1, by linarith [Real.sqrt_nonneg k], ?_⟩
  intro Q i ζ hζ f g G hfg hG hf hg
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  filter_upwards [henergy Q i ζ hζ f g G hfg hG,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      f hp0 ENNReal.ofReal_ne_top hf,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      g hp0 ENNReal.ofReal_ne_top hg,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))] with ω he hf hg hgrad
  intro L hL
  have hmem {q : ℝ≥0∞} (F : Vec d → ℂ)
      (hF : ∀ K : Set (Vec d), IsCompact K → MemLp F q (volume.restrict K))
      (R : ℝ) (hR : 0 < R) : MemLp F q (PDE.volumeOn (PDE.euclideanBall 0 R)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_)
      (hF {x | euclideanNorm x ≤ R}
        (by simpa only [sub_zero] using isCompact_physical_euclidean_closedBall (0 : Vec d) R))
    intro x hx
    change euclideanNorm x ≤ R
    simpa only [sub_zero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
      euclideanNorm, euclideanSq, dot] using
      ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx).le
  have hf3 := hmem _ hf (3 * ρ) (by positivity)
  have hg3 := hmem _ hg (3 * ρ) (by positivity)
  letI := PDE.isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d)
    (by positivity : (0 : ℝ) ≤ 3 * ρ)
  have hpp : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hfi := (memLp_two_iff_integrable_sq_norm (hf3.mono_exponent hpp).aestronglyMeasurable).mp
    (hf3.mono_exponent hpp)
  have hgi := (memLp_two_iff_integrable_sq_norm (hg3.mono_exponent hpp).aestronglyMeasurable).mp
    (hg3.mono_exponent hpp)
  let Nf := (eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
    (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
  let Ng := (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
    (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
  have hNf : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNg : 0 ≤ Ng := ENNReal.toReal_nonneg
  have houter : (∫ x in {x : Vec d | euclideanNorm (x - 0) ≤ 2 * ρ},
      ‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2) ≤
      (volume (PDE.euclideanBall (0 : Vec d) (3 * ρ))).toReal * (Nf + Ng) ^ 2 := by
    calc
      _ ≤ ∫ x in PDE.euclideanBall 0 (3 * ρ),
          ‖f (translate x ω)‖ ^ 2 + ‖g (translate x ω)‖ ^ 2 := by
        apply setIntegral_mono_set (hfi.add hgi)
          (Eventually.of_forall fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
        exact Eventually.of_forall (fun x hx =>
          (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr (by
            change euclideanNorm (x - 0) ≤ 2 * ρ at hx
            change euclideanNorm (x - 0) < 3 * ρ
            linarith))
      _ ≤ (volume (PDE.euclideanBall (0 : Vec d) (3 * ρ))).toReal * (Nf ^ 2 + Ng ^ 2) := by
        rw [integral_add hfi hgi, mul_add]
        exact add_le_add
          (c15_local_square_integral_le_lp (3 * ρ) (by positivity) p hp _ hf3)
          (c15_local_square_integral_le_lp (3 * ρ) (by positivity) p hp _ hg3)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by nlinarith) ENNReal.toReal_nonneg
  have hgradInt : IntegrableOn (fun x => ∑ j, ‖G j (translate (ρ • x) ω)‖ ^ 2)
      (PDE.euclideanBall 0 1) volume := by
    apply integrable_finsetSum Finset.univ
    intro j _
    have hm := c15_memLp_affine_unit_ball (0 : Vec d) hρ (hmem _ (hgrad j) ρ hρ)
    simp only [zero_add] at hm
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hproj : (∫ x in PDE.euclideanBall (0 : Vec d) 1,
      PDE.vecNormSq (fun j => L (G j (translate (ρ • x) ω)))) ≤
      ∫ x in PDE.euclideanBall (0 : Vec d) 1, ∑ j, ‖G j (translate (ρ • x) ω)‖ ^ 2 := by
    apply integral_mono_of_nonneg
      (Eventually.of_forall fun x => PDE.vecNormSq_nonneg _) hgradInt
    apply Eventually.of_forall
    intro x
    unfold PDE.vecNormSq PDE.vecDot
    apply Finset.sum_le_sum
    intro j _
    have hs := (sq_le_sq₀ (abs_nonneg (L (G j (translate (ρ • x) ω))))
      (norm_nonneg (G j (translate (ρ • x) ω)))).mpr (hL _)
    rw [sq_abs] at hs
    simpa only [pow_two] using hs
  have hscale := PDE.DGNM.setIntegral_comp_affineScale_ball (0 : Vec d) hρ 1
    (fun x => ∑ j, ‖G j (translate x ω)‖ ^ 2)
  simp only [add_zero, mul_one] at hscale
  have hraw := hproj.trans (hscale.trans_le
    (mul_le_mul_of_nonneg_left ((he 0).trans
      (mul_le_mul_of_nonneg_left houter hE.le)) (by positivity)))
  have hmean : PDE.integralAverage (PDE.euclideanBall (0 : Vec d) 1)
      (fun x => PDE.vecNormSq (fun j => L (G j (translate (ρ • x) ω)))) ≤
      k * (Nf + Ng) ^ 2 := by
    unfold PDE.integralAverage
    convert mul_le_mul_of_nonneg_left hraw
      (show 0 ≤ (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal⁻¹ by positivity) using 1 <;>
      dsimp [k] <;> ring
  calc
    _ ≤ Real.sqrt (k * (Nf + Ng) ^ 2) := Real.sqrt_le_sqrt hmean
    _ = Real.sqrt k * (Nf + Ng) := by
      rw [Real.sqrt_mul hk, Real.sqrt_sq (add_nonneg hNf hNg)]
    _ ≤ _ := by dsimp [Nf, Ng] at *; nlinarith [Real.sqrt_nonneg k]

private theorem c15_memLp_orbit_on_euclidean_ball
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (f : Vec d → E)
    (hf : ∀ K : Set (Vec d), IsCompact K → MemLp f p (volume.restrict K))
    (R : ℝ) (hR : 0 < R) : MemLp f p (PDE.volumeOn (PDE.euclideanBall 0 R)) := by
  apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_)
    (hf {x | euclideanNorm x ≤ R}
      (by simpa only [sub_zero] using isCompact_physical_euclidean_closedBall (0 : Vec d) R))
  intro x hx
  change euclideanNorm x ≤ R
  simpa only [sub_zero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
      euclideanNorm, euclideanSq, dot] using
      ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).mp hx).le

private theorem c15_rescaled_local_lp_bound
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (ρ : ℝ) (hρ : 0 < ρ) (p : ℝ≥0∞) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ f : Vec d → E,
      MemLp f p (PDE.volumeOn (PDE.euclideanBall 0 (3 * ρ))) →
      MemLp (fun x => f (ρ • x)) p (PDE.volumeOn (PDE.euclideanBall 0 1)) ∧
      (eLpNorm (fun x => f (ρ • x)) p (PDE.volumeOn (PDE.euclideanBall 0 1))).toReal ≤
        J * (eLpNorm f p (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal := by
  let V := volume (PDE.euclideanBall (0 : Vec d) (3 * ρ))
  let α := ENNReal.ofReal ((ρ ^ d)⁻¹) ^ (1 / p).toReal
  refine ⟨α.toReal * (V ^ (1 / p).toReal).toReal, by positivity, ?_⟩
  intro f hf
  have hsub : PDE.euclideanBall (0 : Vec d) ρ ⊆ PDE.euclideanBall 0 (3 * ρ) := by
    intro x hx
    exact (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).mpr
      (lt_trans ((PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hρ).mp hx) (by linarith))
  have hfi := MemLp.mono_measure (Measure.restrict_mono_set volume hsub) hf
  have hfm := c15_memLp_affine_unit_ball (0 : Vec d) hρ hfi
  simp only [zero_add] at hfm
  refine ⟨hfm, ?_⟩
  have hscale := PDE.DGNM.eLpNorm_comp_affineScale_ball (0 : Vec d) hρ 1 f p
  simp only [add_zero, mul_one] at hscale
  rw [hscale, ENNReal.toReal_mul]
  have hmono : (eLpNorm f p (PDE.volumeOn (PDE.euclideanBall 0 ρ))).toReal ≤
      (eLpNorm f p (PDE.volumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal :=
    ENNReal.toReal_mono hf.eLpNorm_ne_top
      (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hsub))
  have hraw := PDE.eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn
    (PDE.volume_euclideanBall_pos (0 : Vec d) (by positivity : 0 < 3 * ρ))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top (0 : Vec d)
      (by positivity : 0 ≤ 3 * ρ))) p f
  change eLpNorm f p (PDE.volumeOn (PDE.euclideanBall 0 (3 * ρ))) =
    V ^ (1 / p).toReal * eLpNorm f p
      (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ))) at hraw
  calc
    _ ≤ α.toReal * (eLpNorm f p (PDE.volumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal :=
      mul_le_mul_of_nonneg_left hmono ENNReal.toReal_nonneg
    _ = _ := by rw [hraw, ENNReal.toReal_mul]; ring

private theorem c15_rescaled_forcing_norm_bound
    (d : ℕ) (D : StructuralData d) (p A K ρ : ℝ)
    (hp : 2 ≤ p) (hA : 0 ≤ A) (hρ : 0 < ρ) :
    ∃ M : ℝ, 0 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ A →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)),
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℂ →L[ℝ] ℝ, (∀ w, |L w| ≤ ‖w‖) →
      let H := fun x => g (translate x ω) + ζ * (∑ j,
        (coordinateDerivative j (fun y => ω.1 y j i) x : ℂ)) * f (translate x ω)
      let B := fun x j => ζ * (ω.1 x j i : ℂ) * f (translate x ω)
      let S := fun x => -2 * K * ρ * L (H (ρ • x))
      let F := fun x j => -2 * K * L (B (ρ • x) j)
      let N := (eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal +
        (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
      (eLpNorm S (ENNReal.ofReal p) (PDE.volumeOn (PDE.euclideanBall 0 1))).toReal ≤ M * N ∧
      (eLpNorm (PDE.toHilbertVecField F) (ENNReal.ofReal p)
        (PDE.volumeOn (PDE.euclideanBall 0 1))).toReal ≤ M * N := by
  obtain ⟨B₀, hB₀, hb⟩ := clock_spatial_rescaled_forcing_pointwise_bound d D
  obtain ⟨J, hJ, hscale⟩ := c15_rescaled_local_lp_bound (E := ℂ) ρ hρ (ENNReal.ofReal p)
  let a := 2 * |K| * ρ * (A * B₀)
  let b := 2 * |K| * ρ
  let c := 2 * |K| * (d : ℝ) * A * B₀
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb' : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨(a + b + c) * J, by positivity, ?_⟩
  intro Q hQ i ζ hζ f g hf hg
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  filter_upwards [hb Q hQ,
    clock_generator_spatial_rescaled_forcing_memLp D Q hQ i ζ f g hp0
      ENNReal.ofReal_ne_top hf hg,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      f hp0 ENNReal.ofReal_ne_top hf,
    clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      g hp0 ENNReal.ofReal_ne_top hg] with ω hpoint hmem hfω hgω
  intro L hL H B S F N
  let Nf := (eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
    (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
  let Ng := (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
    (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
  have hNf : 0 ≤ Nf := ENNReal.toReal_nonneg
  have hNg : 0 ≤ Ng := ENNReal.toReal_nonneg
  obtain ⟨hfs, hnfs⟩ := hscale _
    (c15_memLp_orbit_on_euclidean_ball _ hfω (3 * ρ) (by positivity))
  obtain ⟨hgs, hngs⟩ := hscale _
    (c15_memLp_orbit_on_euclidean_ball _ hgω (3 * ρ) (by positivity))
  have hSmem : MemLp S (ENNReal.ofReal p) (PDE.volumeOn (PDE.euclideanBall 0 1)) := by
    simpa only [zero_add] using (hmem 0 ρ hρ K L).1
  have hFmem : MemLp (PDE.toHilbertVecField F) (ENNReal.ofReal p)
      (PDE.volumeOn (PDE.euclideanBall 0 1)) := by
    apply PDE.gradMemLpOn_iff_memLp_toHilbertVecField.mp
    change ∀ j, MemLp (fun x => F x j) (ENNReal.ofReal p)
      (PDE.volumeOn (PDE.euclideanBall 0 1))
    intro j
    simpa only [zero_add] using (hmem 0 ρ hρ K L).2 j
  have hSbound : ∀ x, ‖S x‖ ≤ a * ‖f (translate (ρ • x) ω)‖ +
      b * ‖g (translate (ρ • x) ω)‖ := by
    intro x
    have hs := (hpoint i ζ f g 0 ρ K L hL x).1
    simp only [zero_add, abs_of_pos hρ] at hs
    calc
      _ ≤ (2 * |K| * ρ) * (‖g (translate (ρ • x) ω)‖ +
          ‖ζ‖ * B₀ * ‖f (translate (ρ • x) ω)‖) := hs
      _ ≤ (2 * |K| * ρ) * (‖g (translate (ρ • x) ω)‖ +
          A * B₀ * ‖f (translate (ρ • x) ω)‖) := by
        gcongr
      _ = _ := by dsimp [a, b]; ring
  have hFbound : ∀ x, ‖PDE.toHilbertVecField F x‖ ≤
      c * ‖f (translate (ρ • x) ω)‖ + 0 * ‖g (translate (ρ • x) ω)‖ := by
    intro x
    have hs := (hpoint i ζ f g 0 ρ K L hL x).2
    simp only [zero_add] at hs
    calc
      _ ≤ (2 * |K| * (d : ℝ) * ‖ζ‖ * B₀) * ‖f (translate (ρ • x) ω)‖ := hs
      _ ≤ (2 * |K| * (d : ℝ) * A * B₀) * ‖f (translate (ρ • x) ω)‖ := by gcongr
      _ = _ := by dsimp [c]; ring
  have hSn := (c15_lp_norm_bound_of_pointwise_sources _ _ hp1 _ _ S hfs hgs
    hSmem.aestronglyMeasurable a b ha hb' (Eventually.of_forall hSbound)).2
  have hFn := (c15_lp_norm_bound_of_pointwise_sources _ _ hp1 _ _
    (PDE.toHilbertVecField F) hfs hgs hFmem.aestronglyMeasurable c 0 hc le_rfl
    (Eventually.of_forall hFbound)).2
  have hSfinal := hSn.trans (add_le_add
    (mul_le_mul_of_nonneg_left hnfs ha) (mul_le_mul_of_nonneg_left hngs hb'))
  have hFfinal : (eLpNorm (PDE.toHilbertVecField F) (ENNReal.ofReal p)
      (PDE.volumeOn (PDE.euclideanBall 0 1))).toReal ≤ c * (J * Nf) := by
    have h := hFn.trans (add_le_add
      (mul_le_mul_of_nonneg_left hnfs hc) (le_refl (0 *
        (eLpNorm (fun x => g (translate (ρ • x) ω)) (ENNReal.ofReal p)
          (PDE.volumeOn (PDE.euclideanBall 0 1))).toReal)))
    simpa only [zero_mul, add_zero] using h
  change _ ≤ _ * (Nf + Ng) ∧ _ ≤ _ * (Nf + Ng)
  constructor
  · apply hSfinal.trans
    nlinarith [mul_nonneg hc (mul_nonneg hJ hNf),
      mul_nonneg hc (mul_nonneg hJ hNg), mul_nonneg ha (mul_nonneg hJ hNg),
      mul_nonneg hb' (mul_nonneg hJ hNf)]
  · apply hFfinal.trans
    nlinarith [mul_nonneg (add_nonneg ha hb') (mul_nonneg hJ (add_nonneg hNf hNg)),
      mul_nonneg hc (mul_nonneg hJ hNg)]

/-- A local higher-moment bound for the actual complex horizontal gradient.
The radius and constant are uniform in the environment law. -/
theorem clock_generator_spatial_local_gradient_bound
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p A : ℝ)
    (hp : 2 ≤ p) (hA : 0 ≤ A) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ A →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsComplexGeneratorPair Q i ζ f g →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d,
      MemLp (fun x => G j (translate (ρ • x) ω)) (ENNReal.ofReal p)
        (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))) ∧
      (eLpNorm (fun x => G j (translate (ρ • x) ω)) (ENNReal.ofReal p)
        (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ)))).toReal ≤
      C * ((eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal +
        (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
          (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal) := by
  obtain ⟨K, C, ρ, hK, hC, hρ, hinterior⟩ :=
    clock_generator_spatial_rescaled_interior_estimate d hd D p hp
  obtain ⟨E, hE, he⟩ := clock_generator_spatial_rescaled_energy_bound d hd D p A ρ hp hA hρ
  obtain ⟨M, hM, hm⟩ := c15_rescaled_forcing_norm_bound d D p A K ρ hp hA hρ
  let v := (((volume (PDE.euclideanBall (0 : Vec d) 1))⁻¹ ^
    (1 / ENNReal.ofReal p).toReal).toReal)
  let H := ((2 : ℝ) ^ d + 1) * 2
  let Z := C * (E + p * v * (H * M + M))
  have hv : 0 ≤ v := ENNReal.toReal_nonneg
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hp' : 0 ≤ p := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  refine ⟨ρ, 2 * Z + 1, hρ, by linarith, ?_⟩
  intro Q hQ i ζ hζ f g G hfg hG hf hg
  filter_upwards [hinterior Q hQ i ζ f g G hfg hG hf hg,
    he Q i ζ hζ f g G hfg hG hf hg,
    hm Q hQ i ζ hζ f g hf hg] with ω hi heω hmω
  intro j
  let N := (eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p)
    (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal +
    (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p)
      (PDE.normalizedVolumeOn (PDE.euclideanBall 0 (3 * ρ)))).toReal
  have hN : 0 ≤ N := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  let L : Bool → ℂ →L[ℝ] ℝ := fun b => if b then Complex.reCLM else Complex.imCLM
  let V : Bool → Vec d → ℝ := fun b x =>
    PDE.vecEuclideanNorm (fun k => L b (G k (translate (ρ • x) ω)))
  have hcomponent (b : Bool) :
      MemLp (V b) (ENNReal.ofReal p)
        (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))) ∧
      (eLpNorm (V b) (ENNReal.ofReal p)
        (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ)))).toReal ≤ Z * N := by
    have hL : ∀ w, |L b w| ≤ ‖w‖ := by
      intro w
      cases b
      · exact Complex.abs_im_le_norm w
      · exact Complex.abs_re_le_norm w
    have hc := hi 0 b
    simp only [zero_add] at hc
    refine ⟨PDE.memLp_normalizedVolumeOn_of_memLpOn hc.1
      (PDE.volume_euclideanBall_pos (0 : Vec d) (by norm_num)), ?_⟩
    have henergy := heω (L b) hL
    obtain ⟨hscalar, hvector⟩ := hmω (L b) hL
    refine hc.2.trans ?_
    calc
      _ ≤ C * (E * N + p * v * (H * (M * N) + M * N)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        have hforcing := mul_le_mul_of_nonneg_left
          (add_le_add (mul_le_mul_of_nonneg_left hscalar hH) hvector) (mul_nonneg hp' hv)
        simpa only [L, N, v, H, mul_assoc] using add_le_add henergy hforcing
      _ = Z * N := by dsimp [Z]; ring
  have hr := hcomponent true
  have hi' := hcomponent false
  have hmeas : AEStronglyMeasurable (fun x => G j (translate (ρ • x) ω))
      (PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))) := by
    exact ((Lp.stronglyMeasurable (G j)).measurable.comp
      (Probability.continuous_translate.measurable.comp
        ((measurable_id.const_smul ρ).prodMk measurable_const))).aestronglyMeasurable
  have hpoint : ∀ x, ‖G j (translate (ρ • x) ω)‖ ≤ 1 * ‖V true x‖ + 1 * ‖V false x‖ := by
    intro x
    calc
      _ ≤ |(G j (translate (ρ • x) ω)).re| + |(G j (translate (ρ • x) ω)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ V true x + V false x := by
        change |(G j (translate (ρ • x) ω)).re| + |(G j (translate (ρ • x) ω)).im| ≤
          PDE.vecEuclideanNorm (fun k => (G k (translate (ρ • x) ω)).re) +
          PDE.vecEuclideanNorm (fun k => (G k (translate (ρ • x) ω)).im)
        exact add_le_add
          (PDE.abs_apply_le_vecEuclideanNorm (fun k => (G k (translate (ρ • x) ω)).re) j)
          (PDE.abs_apply_le_vecEuclideanNorm (fun k => (G k (translate (ρ • x) ω)).im) j)
      _ = _ := by
        rw [Real.norm_of_nonneg (PDE.vecEuclideanNorm_nonneg _),
          Real.norm_of_nonneg (PDE.vecEuclideanNorm_nonneg _)]
        ring
  obtain ⟨hmem, hnorm⟩ := c15_lp_norm_bound_of_pointwise_sources _ _
    (ENNReal.one_le_ofReal.mpr (by linarith)) (V true) (V false)
    (fun x => G j (translate (ρ • x) ω)) hr.1 hi'.1 hmeas 1 1 zero_le_one zero_le_one
    (Eventually.of_forall hpoint)
  refine ⟨hmem, hnorm.trans ?_⟩
  change _ ≤ (2 * Z + 1) * N
  nlinarith [hr.2, hi'.2]

/-- Uniform higher moments of an actual generator-pair gradient. The constant
precedes the environment law, and no higher gradient moment is assumed. -/
theorem c15_clock_gradient_finitep_of_generator_pair
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p)
    (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ A →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsComplexGeneratorPair Q i ζ f g →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G →
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ j : Fin d, MemLp (G j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (G j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * ((eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
          (eLpNorm (g : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) := by
  obtain ⟨ρ, C, hρ, hC, hlocal⟩ := clock_generator_spatial_local_gradient_bound d hd D p A hp hA
  refine ⟨C, hC, ?_⟩
  intro Q hQ i ζ hζ f g G hfg hG hf hg j
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hp' : 0 < p := by linarith
  have hp0 : ENNReal.ofReal p ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hp')
  let ν := PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (1 / 2 : ℝ))
  let κ₀ := PDE.normalizedVolumeOn (PDE.euclideanBall (0 : Vec d) (3 * ρ))
  let κ := Measure.map (PDE.DGNM.affineScale (0 : Vec d) hρ.ne') ν
  letI : IsProbabilityMeasure ν := PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
    (PDE.volume_euclideanBall_pos (0 : Vec d) (by norm_num))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)))
  letI : IsProbabilityMeasure κ₀ := PDE.isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
    (PDE.volume_euclideanBall_pos (0 : Vec d) (by positivity : 0 < 3 * ρ))
    (lt_top_iff_ne_top.mpr (PDE.volume_euclideanBall_ne_top (0 : Vec d)
      (by positivity : 0 ≤ 3 * ρ)))
  letI : IsProbabilityMeasure κ := inferInstanceAs (IsProbabilityMeasure (Measure.map _ ν))
  have horbit (F : Lp ℂ 2 (reducedLaw Q))
      (hF : MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) :
      ∀ᵐ ω ∂reducedLaw Q, MemLp (fun x => F (translate x ω)) (ENNReal.ofReal p) κ₀ := by
    filter_upwards [clock_ae_orbit_finitep_on_all_compacts (reducedLaw Q)
      (reducedLaw_stationary Q) F hp0 ENNReal.ofReal_ne_top hF] with ω hω
    exact PDE.memLp_normalizedVolumeOn_of_memLpOn
      (c15_memLp_orbit_on_euclidean_ball _ hω (3 * ρ) (by positivity))
      (PDE.volume_euclideanBall_pos (0 : Vec d) (by positivity : 0 < 3 * ρ))
  let Nf := fun ω => (eLpNorm (fun x => f (translate x ω)) (ENNReal.ofReal p) κ₀).toReal
  let Ng := fun ω => (eLpNorm (fun x => g (translate x ω)) (ENNReal.ofReal p) κ₀).toReal
  obtain ⟨hNf, hNfe⟩ := clock_stationary_local_lp_norm_moment (reducedLaw Q)
    (reducedLaw_stationary Q) κ₀ f (Lp.stronglyMeasurable f).measurable p hp' hf (horbit f hf)
  obtain ⟨hNg, hNge⟩ := clock_stationary_local_lp_norm_moment (reducedLaw Q)
    (reducedLaw_stationary Q) κ₀ g (Lp.stronglyMeasurable g).measurable p hp' hg (horbit g hg)
  have hC0 : 0 ≤ C := by linarith
  let R := fun ω => C * (Nf ω + Ng ω)
  have hR : MemLp R (ENNReal.ofReal p) (reducedLaw Q) := (hNf.add hNg).const_mul C
  have hRn := (c15_lp_norm_bound_of_pointwise_sources (reducedLaw Q) (ENNReal.ofReal p)
    (ENNReal.one_le_ofReal.mpr (by linarith)) Nf Ng R hNf hNg hR.aestronglyMeasurable
    C C (by linarith) (by linarith) (Eventually.of_forall (fun ω => by
      simp only [R, Real.norm_of_nonneg (show 0 ≤ C * (Nf ω + Ng ω) by
          dsimp [Nf, Ng]; positivity),
        Real.norm_of_nonneg (show 0 ≤ Nf ω from ENNReal.toReal_nonneg),
        Real.norm_of_nonneg (show 0 ≤ Ng ω from ENNReal.toReal_nonneg)]
      exact le_of_eq (mul_add C (Nf ω) (Ng ω))))).2
  have hmap (ω : FieldPair d) :
      eLpNorm (fun x => G j (translate x ω)) (ENNReal.ofReal p) κ =
      eLpNorm (fun x => G j (translate (ρ • x) ω)) (ENNReal.ofReal p) ν := by
    dsimp only [κ]
    rw [(PDE.DGNM.affineScale (0 : Vec d) hρ.ne').measurableEmbedding.eLpNorm_map_measure]
    simp only [Function.comp_def, PDE.DGNM.affineScale_apply, add_zero]
  have hloc := hlocal Q hQ i ζ hζ f g G hfg hG hf hg
  have hm : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun x => G j (translate x ω)) (ENNReal.ofReal p) κ := by
    filter_upwards [hloc] with ω hω
    change eLpNorm _ _ _ < ∞
    rw [hmap]
    exact (hω j).1
  have hb : ∀ᵐ ω ∂reducedLaw Q,
      (eLpNorm (fun x => G j (translate x ω)) (ENNReal.ofReal p) κ).toReal ≤ R ω := by
    filter_upwards [hloc] with ω hω
    rw [hmap]
    exact (hω j).2
  obtain ⟨hGj, hbound⟩ := clock_stationary_moment_of_local_lp_bound (reducedLaw Q)
    (reducedLaw_stationary Q) κ (G j) (Lp.stronglyMeasurable (G j)).measurable p hp' R hR hm hb
  refine ⟨hGj, (ENNReal.toReal_mono hR.eLpNorm_ne_top hbound).trans ?_⟩
  rw [hNfe, hNge] at hRn
  exact hRn.trans_eq (mul_add C _ _).symm

/-- Every finite moment of the same canonical clock gradient is uniform on
compact positive-time and force sets, using only the semigroup dependency. -/
theorem c15_clock_gradient_finite_moments_on_compact_time_force_sets_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p A τ T : ℝ),
      2 ≤ p → 0 ≤ A → 0 < τ → τ ≤ T →
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
    ∀ (ζ : ℂ) (r : ℝ≥0), ‖ζ‖ ≤ A → τ ≤ (r : ℝ) → (r : ℝ) ≤ T →
    ∀ j : Fin d,
      MemLp (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal C := by
  intro d hd D p A τ T hp hA hτ hτT
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hT : 0 < T := hτ.trans_le hτT
  obtain ⟨L, hL, hdatum⟩ := clock_observation_uniform_moments d D
  obtain ⟨V, hV, hval⟩ := (h0 d hd D).2 p (A + 1) T hp (by linarith) hT
  obtain ⟨B, hB, hgen⟩ := clock_orbit_generator_uniform_finitep_of_deps h0 d hd D
    p A T hp hA hT
  obtain ⟨K, hK, hgrad⟩ := c15_clock_gradient_finitep_of_generator_pair d hd D p hp A hA
  have hK0 : 0 < K := by linarith
  refine ⟨K * (V * L + B), mul_pos hK0 (add_pos (mul_pos hV hL) hB), ?_⟩
  intro Q hQ μ hμ P hP ζ r hζ hrτ hrT j
  have hμp : MemLp (μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hdatum Q μ hμ _).trans_lt (by finiteness)
  have hv := ((hval Q hQ μ hμp r hrT).1 ζ (hζ.trans (by linarith)))
  have hf : MemLp (P ζ r μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
    simpa only [(hP ζ).eq_forcedComplexEvolution] using hv.1
  have hfn : eLpNorm (P ζ r μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (V * L) := by
    calc
      _ ≤ ENNReal.ofReal V * eLpNorm μ (ENNReal.ofReal p) (reducedLaw Q) := by
        simpa only [(hP ζ).eq_forcedComplexEvolution] using hv.2.2.1
      _ ≤ ENNReal.ofReal V * ENNReal.ofReal L :=
        mul_le_mul' le_rfl (hdatum Q μ hμ _)
      _ = _ := (ENNReal.ofReal_mul hV.le).symm
  obtain ⟨g₀, _, _, hg₀⟩ := hgen Q hQ μ hμ P hP ζ hζ
  obtain ⟨hfg, hg, hgn⟩ := hg₀ r hrT
  have hr : 0 < r := by exact_mod_cast hτ.trans_le hrτ
  have hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P ζ r μ) (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) := by
    intro k
    simpa only [ClockAnalyticity.gradient, dif_pos hr] using
      ((hP ζ).forcedGradient_spec r hr μ k)
  obtain ⟨hmem, hnorm⟩ := hgrad Q hQ ⟨0, by omega⟩ ζ hζ
    (P ζ r μ) (P ζ r g₀) (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) hfg hG hf hg j
  refine ⟨hmem, ?_⟩
  rw [← ENNReal.ofReal_toReal hmem.eLpNorm_ne_top]
  apply ENNReal.ofReal_le_ofReal
  exact hnorm.trans (mul_le_mul_of_nonneg_left (add_le_add
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hfn).trans_eq
      (ENNReal.toReal_ofReal (mul_pos hV hL).le))
    ((ENNReal.toReal_mono ENNReal.ofReal_ne_top hgn).trans_eq
      (ENNReal.toReal_ofReal hB.le))) hK0.le)

end EinsteinFull.Blueprint
