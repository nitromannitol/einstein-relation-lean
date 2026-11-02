import Mathlib.Analysis.Complex.Schwarz
import EinsteinFull.Calculus.C3SmoothedDuhamelClosureSupport
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import EinsteinFull.Calculus.C1EndpointsV2Support
import EinsteinFull.Work.W3.GaussianProfileScalingSupport
import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinFull.Blueprint.G1.Proofs.S3AnnuliReal
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Calculus.C1BootstrapAverageSupport
import EinsteinFull.Calculus.ComplexHighExponentSupport
import EinsteinRelation.Clock.SpatialAverageBound
import EinsteinFull.Calculus.S1FiniteRangeSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints

/-! Unit-initialization bounds from V1 locality and the exact endpoint premise. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.UnitInitialization
open EinsteinRelation EinsteinRelation.Clock EinsteinFull.Blueprint

private instance probability {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q

/-- Centering a uniformly bounded actual L2 class costs at most two. -/
theorem ae_norm_centered_le {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) {K : ℝ}
    (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
    ∀ᵐ ω ∂reducedLaw Q, ‖centeredComplexLp Q f ω‖ ≤ 2 * K := by
  have hi : ‖∫ ω, f ω ∂reducedLaw Q‖ ≤ K := by
    simpa using norm_integral_le_of_norm_le_const hf
  filter_upwards [centeredComplexLp_ae Q f, hf] with ω he hb
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

/-- The indexed endpoint inherits an uncentered bound, including the clock. -/
theorem ae_norm_indexed_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ K) :
    ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ 2 * K := by
  rcases ν with i | b
  · exact ae_norm_centered_le Q _ hb
  · cases b
    · have hc := ae_norm_centered_le Q _ hb
      filter_upwards [hc, smul_centered_ae_eq Q ζ (P t μ)] with ω hc he
      exact he.symm ▸ hc
    · exact hb.mono fun ω h => h.trans (by linarith)

/-- A single deterministic bound controls all positive times up to the horizon.
This uses only V1 locality, whose pointwise clause includes times below one. -/
theorem positive_time_bound (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) ≤ T →
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ C := by
  obtain ⟨A, c, N, hA, _, hloc⟩ := hlocal d hd D
  let K := A * (2 + T) ^ N * Real.exp (A * 4 * T)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨1 + 2 * K, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht htT
  obtain ⟨G, _, _, hb⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hz2 : ‖ζ‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg ζ]
  have hp : (2 + (t : ℝ)) ^ N ≤ (2 + T) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  have he : Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (A * 4 * T) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 hA0)
      t.coe_nonneg).trans (mul_le_mul_of_nonneg_left htT (by positivity))
  have hbound : A * (2 + (t : ℝ)) ^ N * Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ K :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp hA0) he (Real.exp_pos _).le
      (by positivity)
  have hu : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ K := by
    filter_upwards [hb t ht (by linarith)] with ω h
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (h.trans hbound)
  exact (ae_norm_indexed_le hd Q ν ζ P Pdag β a μ t hK hu).mono
    fun ω h => h.trans (by linarith)

/-- At time zero the literal observations give a uniform bound for all indices. -/
theorem zero_time_bound (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 →
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ ≤ C := by
  obtain ⟨K, hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨1 + 6 * K, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hu : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ ≤ 3 * K := by
    rcases ν with i | b
    · simp only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply]
      filter_upwards [Lp.coeFn_add (β i) (ζ • a ⟨0, by omega⟩ i),
        Lp.coeFn_smul ζ (a ⟨0, by omega⟩ i), hb i, ha' ⟨0, by omega⟩ i]
        with ω he hs hbω haω
      rw [he, Pi.add_apply, hs, Pi.smul_apply]
      exact (norm_add_le _ _).trans (by rw [norm_smul]; nlinarith [norm_nonneg ζ])
    · cases b
      · simp only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply]
        filter_upwards [Lp.coeFn_smul ζ μ, hm] with ω he hmω
        rw [he, Pi.smul_apply, norm_smul]
        nlinarith [norm_nonneg ζ]
      · simp only [uncenteredEndpoint, transposeEndpoint, hPdag.zero hP,
          ContinuousLinearMap.id_apply]
        exact (hb ⟨0, by omega⟩).mono fun ω h => h.trans (by linarith)
  exact (ae_norm_indexed_le hd Q ν ζ P Pdag β a μ 0 (by positivity) hu).mono
    fun ω h => h.trans (by linarith)

/-- The point half of unit initialization holds at every time in the interval.
The same constant works for every exponent, since the bound is deterministic. -/
theorem point_bound (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ p : ℝ≥0∞,
      MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        p (reducedLaw Q) ∧
      (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        p (reducedLaw Q)).toReal ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := zero_time_bound d hd D
  obtain ⟨C₁, hC₁, hb₁⟩ := positive_time_bound hlocal d hd D T hT
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht p
  have hb : ∀ᵐ ω ∂reducedLaw Q,
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ max C₀ C₁ := by
    by_cases hz : t = 0
    · subst t
      exact (hb₀ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ).mono
        fun ω h => h.trans (le_max_left _ _)
    · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hz)
      exact (hb₁ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t htpos ht).mono
        fun ω h => h.trans (le_max_right _ _)
  exact ⟨MemLp.of_bound (Lp.memLp _).aestronglyMeasurable _ hb,
    AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp _).aestronglyMeasurable
      ((zero_le_one.trans hC₀).trans (le_max_left _ _)) hb⟩

/-- The literal unforced homogenized Gaussian is an Lp contraction. -/
theorem gaussian_average_bound {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) :
    MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  simpa only [homogeneousAverage, gaussianAverage, Complex.zero_im, zero_pow (by decide : 2 ≠ 0),
    zero_mul, zero_div, Real.exp_zero, one_mul] using
    bootstrap_average_homogeneous_Lp Q ⟨0, by omega⟩ s hs 0 p hp f hf

/-- Contraction in the extended norm, for restricting the actual L2 operator. -/
theorem gaussian_average_eLpNorm_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) :
    eLpNorm (gaussianAverage hd Q s hs f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨hm, hn⟩ := gaussian_average_bound hd Q p hp f hf s hs
  calc
    _ = ENNReal.ofReal (eLpNorm (gaussianAverage hd Q s hs f)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      (ENNReal.ofReal_toReal hm.eLpNorm_ne_top).symm
    _ ≤ ENNReal.ofReal (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
      ENNReal.ofReal_le_ofReal hn
    _ = _ := ENNReal.ofReal_toReal hf.eLpNorm_ne_top

private theorem two_le_exponent {p : ℝ} (hp : 2 ≤ p) : 2 ≤ ENNReal.ofReal p := by
  exact_mod_cast ENNReal.ofReal_le_ofReal hp

/-- The full homogenized Gaussian on finite Lp is the restriction of its actual
L2 Bochner integral. This preserves linearity and the exact contraction constant. -/
noncomputable def gaussianAverageFiniteP {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s) :
    Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) :=
  complexL2OperatorLpRestriction (reducedLaw Q) (two_le_exponent hp)
    (homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0)
    (fun f => (gaussian_average_bound hd Q p hp _ (Lp.memLp f) s hs).1)
    (C := 1) (by norm_num)
    (fun f => by
      rw [ENNReal.ofReal_one, mul_one]
      have he := gaussian_average_eLpNorm_le hd Q p hp
        (complexLpToL2 (reducedLaw Q) (two_le_exponent hp) f) (Lp.memLp f) s hs
      convert he using 1 <;> rfl)

/-- Inclusion identifies finite-p Gaussian averaging with the literal L2 integral. -/
theorem gaussianAverageFiniteP_apply {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :
    complexLpToL2 (reducedLaw Q) (two_le_exponent hp)
      (gaussianAverageFiniteP hd Q p hp s hs f) =
    gaussianAverage hd Q s hs (complexLpToL2 (reducedLaw Q) (two_le_exponent hp) f) := rfl

/-- Gaussian averaging preserves any finite-p localization error without loss. -/
theorem norm_gaussianAverageFiniteP_sub_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :
    ‖gaussianAverageFiniteP hd Q p hp s hs f -
      gaussianAverageFiniteP hd Q p hp s hs g‖ ≤ ‖f - g‖ := by
  rw [← map_sub]
  have h := (gaussian_average_bound hd Q p hp
    (complexLpToL2 (reducedLaw Q) (two_le_exponent hp) (f - g))
    (Lp.memLp (f - g)) s hs).2
  rw [← gaussianAverageFiniteP_apply hd Q p hp s hs (f - g)] at h
  exact h

/-- The finite-p force quotient commutes exactly with the full Gaussian. This
keeps the signed complex force as a scalar rather than estimating it prematurely. -/
theorem gaussianAverageFiniteP_force_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s)
    (E E₀ H : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) (ζ : ℂ)
    (h : E - E₀ = ζ • H) :
    gaussianAverageFiniteP hd Q p hp s hs E =
      gaussianAverageFiniteP hd Q p hp s hs E₀ +
        ζ • gaussianAverageFiniteP hd Q p hp s hs H := by
  have he : E = E₀ + ζ • H := by rw [← h]; abel
  rw [he, map_add, map_smul]

/-- Transfer a local approximation of the force quotient to the literal
Gaussian-averaged endpoint. The remaining inputs are the two spatial decay
estimates; Gaussian averaging adds no loss to the localization error. -/
theorem gaussian_average_force_bound {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q))
    (E E₀ H K : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) (ζ : ℂ)
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] f)
    (hforce : E - E₀ = ζ • H) :
    MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      ‖gaussianAverageFiniteP hd Q p hp s hs E₀‖ +
        ‖ζ‖ * (‖gaussianAverageFiniteP hd Q p hp s hs K‖ + ‖H - K‖) := by
  let G := gaussianAverageFiniteP hd Q p hp s hs
  have hinc : complexLpToL2 (reducedLaw Q) (two_le_exponent hp) E = f :=
    Lp.ext hE
  have hactual : gaussianAverage hd Q s hs f =
      complexLpToL2 (reducedLaw Q) (two_le_exponent hp) (G E) := by
    rw [← hinc]
    exact (gaussianAverageFiniteP_apply hd Q p hp s hs E).symm
  rw [hactual]
  refine ⟨Lp.memLp (G E), ?_⟩
  change ‖G E‖ ≤ ‖G E₀‖ + ‖ζ‖ * (‖G K‖ + ‖H - K‖)
  have hH : ‖G H‖ ≤ ‖G K‖ + ‖H - K‖ := by
    calc
      ‖G H‖ = ‖G K + (G H - G K)‖ := by congr 1; abel
      _ ≤ ‖G K‖ + ‖G H - G K‖ := norm_add_le _ _
      _ ≤ ‖G K‖ + ‖H - K‖ :=
        add_le_add (le_refl _) (norm_gaussianAverageFiniteP_sub_le hd Q p hp s hs H K)
  calc
    ‖G E‖ = ‖G E₀ + ζ • G H‖ := by
      rw [gaussianAverageFiniteP_force_split hd Q p hp s hs E E₀ H ζ hforce]
    _ ≤ ‖G E₀‖ + ‖ζ‖ * ‖G H‖ := by simpa only [norm_smul] using norm_add_le (G E₀) (ζ • G H)
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hH (norm_nonneg ζ))

/-- On Gaussian scales at most one, the point bound already gives the full
initialization weight, without any locality or cancellation assumption. -/
theorem gaussian_small_scale_bound {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q))
    {C : ℝ} (hC : 0 ≤ C)
    (hb : (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p)
      (reducedLaw Q)).toReal ≤ C)
    (ζ : ℂ) (s : ℝ) (hs : 0 < s) (hs₁ : s ≤ 1) :
    MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      C * (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨hm, hn⟩ := gaussian_average_bound hd Q p hp f hf s hs
  refine ⟨hm, hn.trans (hb.trans ?_)⟩
  have hw : 1 ≤ s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4) :=
    (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs hs₁
      (by linarith [Nat.cast_nonneg (α := ℝ) d])).trans
      (le_add_of_nonneg_right (by positivity))
  exact le_mul_of_one_le_right hC hw

/-- Cube masses have a square-sum bound from their total mass and largest
mass. Applied to the absolute kernel or its derivative, this preserves the
full spatial decay supplied by those two deterministic estimates. -/
theorem summable_sq_and_tsum_sq_le {ι : Type*} (a : ι → ℝ) {M : ℝ}
    (ha : ∀ i, 0 ≤ a i) (haM : ∀ i, a i ≤ M) (hs : Summable a) :
    Summable (fun i => a i ^ 2) ∧ (∑' i, a i ^ 2) ≤ M * ∑' i, a i := by
  have hsum : HasSum (fun i => M * a i) (M * ∑' i, a i) := hs.hasSum.mul_left M
  have hle : ∀ i, a i ^ 2 ≤ M * a i := fun i => by
    rw [sq]
    exact mul_le_mul_of_nonneg_right (haM i) (ha i)
  have hs2 : Summable (fun i => a i ^ 2) :=
    Summable.of_nonneg_of_le (fun i => sq_nonneg (a i)) hle hsum.summable
  exact ⟨hs2, hasSum_le hle hs2.hasSum hsum⟩

/-- Absolute masses for the actual kernel, without an isotropic replacement. -/
noncomputable def kernelCubeMass {d : ℕ} (L : ℝ) (k : Vec d → ℝ)
    (z : Fin d → ℤ) : ℝ := ∫ x in heatCube L z, ‖k x‖

/-- The absolute cube masses sum to the full kernel L1 norm. -/
theorem hasSum_kernelCubeMass {d : ℕ} {L : ℝ} (hL : 0 < L)
    {k : Vec d → ℝ} (hk : Integrable k) :
    HasSum (kernelCubeMass L k) (∫ x, ‖k x‖) := by
  have hint : IntegrableOn (fun x => ‖k x‖)
      (⋃ z : Fin d → ℤ, heatCube L z) volume := hk.norm.integrableOn
  have h := hasSum_integral_iUnion (fun z : Fin d → ℤ => measurableSet_heatCube L z)
    (pairwise_disjoint_heatCube hL) hint
  rw [iUnion_heatCube hL, Measure.restrict_univ] at h
  exact h

/-- L1 mass and a uniform cube-mass estimate control the square sum of the
actual kernel pieces. This also applies to signed spatial derivatives. -/
theorem summable_sq_kernelCubeMass {d : ℕ} {L M : ℝ} (hL : 0 < L)
    {k : Vec d → ℝ} (hk : Integrable k)
    (hM : ∀ z, kernelCubeMass L k z ≤ M) :
    Summable (fun z => kernelCubeMass L k z ^ 2) ∧
      (∑' z, kernelCubeMass L k z ^ 2) ≤ M * ∫ x, ‖k x‖ := by
  have h := hasSum_kernelCubeMass hL hk
  simpa only [h.tsum_eq] using summable_sq_and_tsum_sq_le (kernelCubeMass L k)
    (fun z => integral_nonneg fun x => norm_nonneg (k x)) hM h.summable

/-- Euclidean cubes have their literal product volume. -/
theorem volume_kernelCube {d : ℕ} {L : ℝ} (hL : 0 < L) (z : Fin d → ℤ) :
    volume (heatCube L z) = ENNReal.ofReal (L ^ d) := by
  have hset : heatCube L z = Set.pi Set.univ
      (fun i : Fin d => Set.Ico (L * z i) (L * (z i + 1))) := by
    ext x
    simp [heatCube, Set.mem_pi]
  have hdiff : ∀ i : Fin d,
      ENNReal.ofReal (L * ((z i : ℝ) + 1) - L * (z i : ℝ)) = ENNReal.ofReal L := by
    intro i
    congr 1
    ring
  rw [hset, Real.volume_pi_Ico]
  simp only [hdiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow hL.le]

/-- A pointwise kernel supremum controls every absolute cube mass. -/
theorem kernelCubeMass_le_of_bound {d : ℕ} {L C : ℝ} (hL : 0 < L)
    {k : Vec d → ℝ} (hC : ∀ x, ‖k x‖ ≤ C) (z : Fin d → ℤ) :
    kernelCubeMass L k z ≤ C * L ^ d := by
  have hv := volume_kernelCube hL z
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure (Vec d))) (s := heatCube L z)
    (f := fun x => ‖k x‖) (by rw [hv]; exact ENNReal.ofReal_lt_top)
    (fun x _ => by simpa only [norm_norm] using hC x)
  simpa only [kernelCubeMass, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (k x)),
    Measure.real, hv, ENNReal.toReal_ofReal (pow_nonneg hL.le d)] using h

/-- Uniform all-scale supremum for the full homogenized Gaussian density. -/
theorem norm_homogenizedDensity_le {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖anisotropicGaussian (homogenizedCoefficient Q) s x‖ ≤
      ((2 * Real.pi) ^ (-(d : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)) *
        s ^ (-(d : ℝ) / 2) := by
  have hq : 0 ≤ ∑ j, ∑ k, x j * (homogenizedCoefficient Q)⁻¹ j k * x k := by
    have h := (posDef_homogenizedCoefficient Q).inv.posSemidef.dotProduct_mulVec_nonneg x
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, mul_assoc] using h
  have hp : 0 ≤ (2 * Real.pi * s) ^ (-(d : ℝ) / 2) /
      Real.sqrt (homogenizedCoefficient Q).det := by positivity
  have he : Real.exp (-(∑ j, ∑ k, x j * (homogenizedCoefficient Q)⁻¹ j k * x k) /
      (2 * s)) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) (by positivity))
  have hn : 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) s x := by
    unfold anisotropicGaussian
    positivity
  rw [Real.norm_of_nonneg hn]
  calc
    anisotropicGaussian (homogenizedCoefficient Q) s x ≤
        (2 * Real.pi * s) ^ (-(d : ℝ) / 2) /
          Real.sqrt (homogenizedCoefficient Q).det :=
      (mul_le_mul_of_nonneg_left he hp).trans_eq (mul_one _)
    _ ≤ (2 * Real.pi * s) ^ (-(d : ℝ) / 2) *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (inv_sqrt_det_homogenizedCoefficient_le Q)
        (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi) hs.le]
      ring

/-- The actual homogenized Gaussian has unit absolute spatial mass. -/
theorem integral_norm_homogenizedDensity {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {s : ℝ} (hs : 0 < s) :
    (∫ x, ‖anisotropicGaussian (homogenizedCoefficient Q) s x‖) = 1 := by
  have hn : ∀ x : Vec d, 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) s x := by
    intro x
    unfold anisotropicGaussian
    positivity
  simp_rw [Real.norm_of_nonneg (hn _)]
  exact integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs

/-- Squared absolute cube masses of the full homogenized Gaussian decay as
`s^(-d/2)`, uniformly over the law, with an explicit structural constant. -/
theorem summable_sq_homogenizedDensity_cubeMass {d : ℕ} {Λ r L s : ℝ}
    (Q : EnvironmentLaw d Λ r) (hL : 0 < L) (hs : 0 < s) :
    Summable (fun z => kernelCubeMass L (anisotropicGaussian (homogenizedCoefficient Q) s) z ^ 2) ∧
      (∑' z, kernelCubeMass L (anisotropicGaussian (homogenizedCoefficient Q) s) z ^ 2) ≤
        (((2 * Real.pi) ^ (-(d : ℝ) / 2) *
          Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)) *
          s ^ (-(d : ℝ) / 2)) * L ^ d := by
  have h := summable_sq_kernelCubeMass hL
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs)
    (kernelCubeMass_le_of_bound hL (norm_homogenizedDensity_le Q hs))
  simpa only [integral_norm_homogenizedDensity Q hs, mul_one] using h

/-- The literal complex integral on one cube. -/
noncomputable def kernelCubePiece {d : ℕ} (L : ℝ) (k : Vec d → ℝ)
    (f : FieldPair d → ℂ) (z : Fin d → ℤ) (ω : FieldPair d) : ℂ :=
  ∫ x in heatCube L z, k x • f (translate x ω)

/-- Bounded complex observations can be integrated against any integrable
kernel, including the full covariance Gaussian and its signed derivatives. -/
theorem integrable_kernel_smul_translate {d : ℕ} {k : Vec d → ℝ}
    (hk : Integrable k) (hkm : Measurable k) {f : FieldPair d → ℂ}
    (hf : Measurable f) {B : ℝ} (hfB : ∀ ω, ‖f ω‖ ≤ B) (ω : FieldPair d) :
    Integrable (fun x => k x • f (translate x ω)) := by
  refine (hk.norm.mul_const B).mono' ?_ (ae_of_all _ fun x => ?_)
  · exact (hkm.smul (hf.comp (Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)).measurable)).aestronglyMeasurable
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _)

/-- The actual kernel average is the sum of its literal cube integrals. -/
theorem hasSum_kernelCubePiece {d : ℕ} {L : ℝ} (hL : 0 < L)
    {k : Vec d → ℝ} (hk : Integrable k) (hkm : Measurable k)
    {f : FieldPair d → ℂ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ ω, ‖f ω‖ ≤ B) (ω : FieldPair d) :
    HasSum (fun z => kernelCubePiece L k f z ω)
      (∫ x, k x • f (translate x ω)) := by
  have hint : IntegrableOn (fun x => k x • f (translate x ω))
      (⋃ z : Fin d → ℤ, heatCube L z) volume :=
    (integrable_kernel_smul_translate hk hkm hf hfB ω).integrableOn
  have h := hasSum_integral_iUnion (fun z : Fin d → ℤ => measurableSet_heatCube L z)
    (pairwise_disjoint_heatCube hL) hint
  rw [iUnion_heatCube hL, Measure.restrict_univ] at h
  exact h

/-- Cube integrals are bounded by their actual absolute kernel mass. -/
theorem norm_kernelCubePiece_le {d : ℕ} (L : ℝ) {k : Vec d → ℝ}
    (hk : Integrable k) {f : FieldPair d → ℂ} {B : ℝ}
    (hfB : ∀ ω, ‖f ω‖ ≤ B) (z : Fin d → ℤ) (ω : FieldPair d) :
    ‖kernelCubePiece L k f z ω‖ ≤ B * kernelCubeMass L k z := by
  have h := norm_integral_le_of_norm_le ((hk.norm.mul_const B).restrict
    (s := heatCube L z)) (ae_of_all _ fun x => show
      ‖k x • f (translate x ω)‖ ≤ ‖k x‖ * B by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _))
  simpa only [kernelCubePiece, kernelCubeMass, integral_mul_const, mul_comm B] using h

/-- Literal complex cube integrals are measurable for the enlarged local
sigma-algebra. The measurability comes from the field and kernel themselves. -/
theorem measurable_local_kernelCubePiece {d : ℕ} (L : ℝ) (z : Fin d → ℤ)
    {U W : Set (Vec d)} (hUW : ∀ x ∈ heatCube L z, ∀ y ∈ U, x + y ∈ W)
    {k : Vec d → ℝ} (hk : Integrable k) (hkm : Measurable k)
    {f : FieldPair d → ℂ} (hf : Measurable[localSigma U] f)
    {B : ℝ} (hfB : ∀ ω, ‖f ω‖ ≤ B) :
    Measurable[localSigma W] (kernelCubePiece L k f z) := by
  have hfg : Measurable f := hf.mono (Probability.localSigma_le_borel U) le_rfl
  have hr := measurable_localSigma_setIntegral_translate (measurableSet_heatCube L z)
    hUW k hkm (fun ω => (f ω).re) (Complex.continuous_re.measurable.comp hf)
  have hi := measurable_localSigma_setIntegral_translate (measurableSet_heatCube L z)
    hUW k hkm (fun ω => (f ω).im) (Complex.continuous_im.measurable.comp hf)
  have he : kernelCubePiece L k f z = fun ω =>
      ((∫ x in heatCube L z, k x * (f (translate x ω)).re : ℝ) : ℂ) +
      Complex.I * ((∫ x in heatCube L z, k x * (f (translate x ω)).im : ℝ) : ℂ) := by
    funext ω
    have hint := (integrable_kernel_smul_translate hk hkm hfg hfB ω).restrict
      (s := heatCube L z)
    apply Complex.ext
    · simpa [kernelCubePiece] using (integral_re hint).symm
    · simpa [kernelCubePiece] using (integral_im hint).symm
  rw [he]
  exact (Complex.continuous_ofReal.measurable.comp hr).add
    (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hi))

/-- Stationarity preserves centering of every actual complex kernel piece. -/
theorem integral_kernelCubePiece_eq_zero {d : ℕ} (L : ℝ) (z : Fin d → ℤ)
    {k : Vec d → ℝ} (hk : Integrable k) (hkm : Measurable k)
    {f : FieldPair d → ℂ} (hf : Measurable f) {B : ℝ}
    (hfB : ∀ ω, ‖f ω‖ ≤ B) {P : Measure (FieldPair d)} [IsProbabilityMeasure P]
    (hP : IsStationary P) (hmean : ∫ ω, f ω ∂P = 0) :
    ∫ ω, kernelCubePiece L k f z ω ∂P = 0 := by
  have hbound : Integrable (fun q : FieldPair d × Vec d => ‖k q.2‖ * B)
      (P.prod (volume.restrict (heatCube L z))) :=
    ((hk.norm.mul_const B).restrict (s := heatCube L z)).comp_snd P
  have hm : Measurable (fun q : FieldPair d × Vec d =>
      k q.2 • f (translate q.2 q.1)) :=
    (hkm.comp measurable_snd).smul
      (hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_fst)))
  have hint : Integrable (fun q : FieldPair d × Vec d =>
      k q.2 • f (translate q.2 q.1)) (P.prod (volume.restrict (heatCube L z))) :=
    hbound.mono' hm.aestronglyMeasurable (ae_of_all _ fun q => by
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hfB _) (norm_nonneg _))
  have hzero : ∀ x : Vec d, ∫ ω, k x • f (translate x ω) ∂P = 0 := by
    intro x
    have hmap := integral_map (μ := P) (Probability.measurable_translate x).aemeasurable
      hf.aestronglyMeasurable
    rw [hP x] at hmap
    rw [integral_smul, ← hmap, hmean, smul_zero]
  unfold kernelCubePiece
  rw [integral_integral_swap hint]
  simp only [hzero, integral_zero]

/-- Complex weighted block sums satisfy the real colored Hoeffding estimate
up to a factor two. The weights enter only through their squared sum, so this
estimate applies equally to Gaussian pieces and spatial derivative pieces. -/
theorem eLpNorm_complex_tsum_le_colored {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Countable ι] {N : ℕ}
    (col : ι → Fin N) (X : ι → Ω → ℂ) (hmeas : ∀ i, Measurable (X i))
    (c : ι → ℝ)
    (hindep : ∀ (k : Fin N) (s : Finset ι), (∀ i ∈ s, col i = k) →
      ProbabilityTheory.iIndepFun (fun i : s => X i) P)
    (hc : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ c i)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hc2 : Summable (fun i => c i ^ 2))
    (hpt : ∀ ω, Summable (fun i => X i ω)) (p : ℝ) (hp : 1 ≤ p) :
    MemLp (fun ω => ∑' i, X i ω) (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => ∑' i, X i ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (2 * ((N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p) *
        (∑' i, c i ^ 2) ^ (1 / 2 : ℝ))) := by
  have hXi : ∀ i, Integrable (X i) P := fun i =>
    (integrable_const (c i)).mono' (hmeas i).aestronglyMeasurable (hc i)
  have hre := Probability.eLpNorm_tsum_le_colored col (fun i ω => (X i ω).re)
    (fun i => Complex.continuous_re.measurable.comp (hmeas i)) c
    (fun k s hs => (hindep k s hs).comp (fun _ => Complex.re)
      (fun _ => Complex.continuous_re.measurable))
    (fun i => (hc i).mono fun ω hω => (Complex.abs_re_le_norm _).trans hω)
    (fun i => by simpa [hmean i] using integral_re (hXi i)) hc2
    (fun ω => (RCLike.reCLM.hasSum (hpt ω).hasSum).summable) p hp
  have him := Probability.eLpNorm_tsum_le_colored col (fun i ω => (X i ω).im)
    (fun i => Complex.continuous_im.measurable.comp (hmeas i)) c
    (fun k s hs => (hindep k s hs).comp (fun _ => Complex.im)
      (fun _ => Complex.continuous_im.measurable))
    (fun i => (hc i).mono fun ω hω => (Complex.abs_im_le_norm _).trans hω)
    (fun i => by simpa [hmean i] using integral_im (hXi i)) hc2
    (fun ω => (RCLike.imCLM.hasSum (hpt ω).hasSum).summable) p hp
  let A : ℝ := (N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p) *
    (∑' i, c i ^ 2) ^ (1 / 2 : ℝ)
  have hHC : 0 ≤ Probability.hoeffdingMomentConst p := by
    unfold Probability.hoeffdingMomentConst
    positivity
  have hA : 0 ≤ A :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg N) (Real.rpow_nonneg hHC _))
      (Real.rpow_nonneg (tsum_nonneg fun i => sq_nonneg (c i)) _)
  have hmr : MemLp (fun ω => ∑' i, (X i ω).re) (ENNReal.ofReal p) P :=
    hre.trans_lt ENNReal.ofReal_lt_top
  have hmi : MemLp (fun ω => ∑' i, (X i ω).im) (ENNReal.ofReal p) P :=
    him.trans_lt ENNReal.ofReal_lt_top
  let u : Ω → ℂ := fun ω => ((∑' i, (X i ω).re : ℝ) : ℂ)
  let v : Ω → ℂ := fun ω => ((∑' i, (X i ω).im : ℝ) : ℂ)
  have hu : MemLp u (ENNReal.ofReal p) P := hmr.ofReal
  have hv : MemLp v (ENNReal.ofReal p) P := hmi.ofReal
  have heu : eLpNorm u (ENNReal.ofReal p) P ≤ ENNReal.ofReal A := by
    refine (eLpNorm_congr_norm_ae hu.aestronglyMeasurable hmr.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => Complex.norm_real _)).trans_le hre
  have hev : eLpNorm v (ENNReal.ofReal p) P ≤ ENNReal.ofReal A := by
    refine (eLpNorm_congr_norm_ae hv.aestronglyMeasurable hmi.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => Complex.norm_real _)).trans_le him
  have heI : eLpNorm (Complex.I • v) (ENNReal.ofReal p) P =
      eLpNorm v (ENNReal.ofReal p) P := by
    rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I,
      ENNReal.ofReal_one, one_mul]
  have he : (fun ω => ∑' i, X i ω) = u + Complex.I • v := by
    funext ω
    apply Complex.ext
    · simpa [u, v] using RCLike.re_tsum ℂ (hpt ω)
    · simpa [u, v] using RCLike.im_tsum ℂ (hpt ω)
  rw [he]
  refine ⟨hu.add (hv.const_smul Complex.I), ?_⟩
  calc
    eLpNorm (u + Complex.I • v) (ENNReal.ofReal p) P ≤
        eLpNorm u (ENNReal.ofReal p) P +
          eLpNorm (Complex.I • v) (ENNReal.ofReal p) P :=
      eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)
    _ ≤ ENNReal.ofReal A + ENNReal.ofReal A := by
      rw [heI]
      exact add_le_add heu hev
    _ = ENNReal.ofReal (2 * A) := by
      rw [← ENNReal.ofReal_add hA hA]
      congr 1
      ring

/-- Finite range supplies the independence needed by the complex weighted
block estimate from the actual joint local sigma algebras. -/
theorem eLpNorm_complex_local_tsum_le {d : ℕ} {ι : Type*} [Countable ι]
    {P : Measure (FieldPair d)} [IsProbabilityMeasure P] {r R : ℝ}
    (hfr : HasFiniteRange r P) (hR : r < R) {N : ℕ} (col : ι → Fin N)
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → col i = col j →
      ∀ x ∈ U i, ∀ y ∈ U j, R ≤ euclideanNorm (x - y))
    (X F : ι → FieldPair d → ℂ)
    (hlocal : ∀ i, Measurable[localSigma (U i)] (X i))
    (hrep : ∀ i, X i =ᵐ[P] F i)
    (c : ι → ℝ) (hc : ∀ i, ∀ᵐ ω ∂P, ‖X i ω‖ ≤ c i)
    (hmean : ∀ i, (∫ ω, X i ω ∂P) = 0)
    (hc2 : Summable (fun i => c i ^ 2))
    (hpt : ∀ ω, Summable (fun i => X i ω)) (p : ℝ) (hp : 1 ≤ p) :
    MemLp (fun ω => ∑' i, F i ω) (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => ∑' i, F i ω) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (2 * ((N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p) *
        (∑' i, c i ^ 2) ^ (1 / 2 : ℝ))) := by
  classical
  have hb := eLpNorm_complex_tsum_le_colored col X
    (fun i => (hlocal i).mono (Probability.localSigma_le_borel (U i)) le_rfl) c
    (by
      intro k s hs
      exact Calculus.S1.iIndepFun_of_local hfr (fun i : s => U i) (fun i => hU i) hR
        (fun i j hij x hx y hy => hsep i j
          (fun he => hij (Subtype.ext he)) ((hs i i.2).trans (hs j j.2).symm) x hx y hy)
        (fun i : s => X i) (fun i => hlocal i) (fun _ => Filter.EventuallyEq.rfl))
    hc hmean hc2 hpt p hp
  have heq : (fun ω => ∑' i, X i ω) =ᵐ[P] (fun ω => ∑' i, F i ω) := by
    filter_upwards [ae_all_iff.mpr hrep] with ω hω
    exact tsum_congr hω
  refine ⟨hb.1.ae_eq heq, ?_⟩
  rw [← eLpNorm_congr_ae heq]
  exact hb.2

/-- Joint finite range controls the literal complex average for a general
integrable kernel through its absolute cube masses. -/
theorem eLpNorm_kernelAverage_le {d : ℕ} {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] {r R L M B : ℝ} (hP : IsStationary P)
    (hfr : HasFiniteRange r P) (hR : r < R) (hL : 0 < L) {N : ℕ}
    (col : (Fin d → ℤ) → Fin N) (U : Set (Vec d))
    (W : (Fin d → ℤ) → Set (Vec d)) (hW : ∀ z, MeasurableSet (W z))
    (hUW : ∀ z, ∀ x ∈ heatCube L z, ∀ y ∈ U, x + y ∈ W z)
    (hsep : ∀ z w, z ≠ w → col z = col w →
      ∀ x ∈ W z, ∀ y ∈ W w, R ≤ euclideanNorm (x - y))
    {k : Vec d → ℝ} (hk : Integrable k) (hkm : Measurable k)
    (hM : ∀ z, kernelCubeMass L k z ≤ M)
    {f : FieldPair d → ℂ} (hf : Measurable[localSigma U] f)
    (hfB : ∀ ω, ‖f ω‖ ≤ B) (hmean : ∫ ω, f ω ∂P = 0) (p : ℝ) (hp : 1 ≤ p) :
    MemLp (fun ω => ∫ x, k x • f (translate x ω)) (ENNReal.ofReal p) P ∧
    eLpNorm (fun ω => ∫ x, k x • f (translate x ω)) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (2 * ((N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p) *
        (∑' z, (B * kernelCubeMass L k z) ^ 2) ^ (1 / 2 : ℝ))) := by
  have hfg : Measurable f := hf.mono (Probability.localSigma_le_borel U) le_rfl
  have hc2 : Summable (fun z => (B * kernelCubeMass L k z) ^ 2) := by
    simp only [mul_pow]
    exact (summable_sq_kernelCubeMass hL hk hM).1.mul_left (B ^ 2)
  have hsum := hasSum_kernelCubePiece hL hk hkm hfg hfB
  have hb := eLpNorm_complex_local_tsum_le hfr hR col W hW hsep
    (kernelCubePiece L k f) (kernelCubePiece L k f)
    (fun z => measurable_local_kernelCubePiece L z (hUW z) hk hkm hf hfB)
    (fun _ => Filter.EventuallyEq.rfl) (fun z => B * kernelCubeMass L k z)
    (fun z => ae_of_all _ fun ω => norm_kernelCubePiece_le L hk hfB z ω)
    (fun z => integral_kernelCubePiece_eq_zero L z hk hkm hfg hfB hP hmean)
    hc2 (fun ω => (hsum ω).summable) p hp
  have heq : (fun ω => ∑' z, kernelCubePiece L k f z ω) =
      (fun ω => ∫ x, k x • f (translate x ω)) := funext fun ω => (hsum ω).tsum_eq
  simpa only [heq] using hb

/-- The actual full homogenized Gaussian has finite-p decay on bounded
local complex fields. Its constant is chosen before either probability law. -/
theorem exists_homogenized_local_average_bound (d : ℕ) (Λ L B p : ℝ)
    (N : ℕ) (hL : 0 < L) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → ∀ {r R : ℝ}, HasFiniteRange r P → r < R →
      ∀ (col : (Fin d → ℤ) → Fin N) (U : Set (Vec d))
        (W : (Fin d → ℤ) → Set (Vec d)),
      (∀ z, MeasurableSet (W z)) →
      (∀ z, ∀ x ∈ heatCube L z, ∀ y ∈ U, x + y ∈ W z) →
      (∀ z w, z ≠ w → col z = col w →
        ∀ x ∈ W z, ∀ y ∈ W w, R ≤ euclideanNorm (x - y)) →
      ∀ f : FieldPair d → ℂ, Measurable[localSigma U] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) := by
  let K : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)
  let A : ℝ := B ^ 2 * K * L ^ d
  let H : ℝ := (N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by
    dsimp [H, Probability.hoeffdingMomentConst]
    positivity
  refine ⟨2 * H * A ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro r₀ Q P _ hP r R hfr hR col U W hW hUW hsep f hf hfB hmean s hs
  have hmass := summable_sq_homogenizedDensity_cubeMass Q hL hs
  have hsum : (∑' z, (B * kernelCubeMass L
      (anisotropicGaussian (homogenizedCoefficient Q) s) z) ^ 2) ≤
      A * s ^ (-(d : ℝ) / 2) := by
    simp only [mul_pow]
    rw [tsum_mul_left]
    calc
      _ ≤ B ^ 2 * ((K * s ^ (-(d : ℝ) / 2)) * L ^ d) :=
        mul_le_mul_of_nonneg_left hmass.2 (sq_nonneg B)
      _ = _ := by dsimp [A]; ring
  have hroot := Real.rpow_le_rpow
    (tsum_nonneg fun z => sq_nonneg (B * kernelCubeMass L
      (anisotropicGaussian (homogenizedCoefficient Q) s) z)) hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hscale : (A * s ^ (-(d : ℝ) / 2)) ^ (1 / 2 : ℝ) =
      A ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
    rw [Real.mul_rpow hA (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
    congr 2
    ring
  rw [hscale] at hroot
  have hb := eLpNorm_kernelAverage_le hP hfr hR hL col U W hW hUW hsep
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs)
    (contDiff_anisotropicGaussian _ _).continuous.measurable
    (kernelCubeMass_le_of_bound hL (norm_homogenizedDensity_le Q hs)) hf hfB hmean p hp
  refine ⟨hb.1, hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc
    _ ≤ 2 * (H * (A ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot hH) (by norm_num)
    _ = _ := by ring

private theorem measurableSet_kernelNbhd {d : ℕ} (ρ : ℝ) (z : Fin d → ℤ) :
    MeasurableSet (clockNbhd ρ z) := by
  apply IsOpen.measurableSet
  unfold clockNbhd
  refine isOpen_biUnion fun a _ => ?_
  apply isOpen_lt _ continuous_const
  unfold euclideanNorm euclideanSq dot
  fun_prop

private theorem kernelNbhd_separated {d : ℕ} (ρ : ℝ) (N : ℕ)
    {z w : Fin d → ℤ} (hzw : z ≠ w)
    (hcol : heatCubeColour N z = heatCubeColour N w)
    {x y : Vec d} (hx : x ∈ clockNbhd ρ z) (hy : y ∈ clockNbhd ρ w) :
    (N : ℝ) - 1 - 2 * ρ ≤ euclideanNorm (x - y) := by
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp hx
  obtain ⟨b, hb, hyb⟩ := Set.mem_iUnion₂.mp hy
  change euclideanNorm (x - a) < ρ at hxa
  change euclideanNorm (y - b) < ρ at hyb
  have hsep := heatCube_dist_of_same_colour one_pos N hzw hcol a ha b hb
  rw [mul_one] at hsep
  have hneg : euclideanNorm (a - x) = euclideanNorm (x - a) := by
    have h : a - x = -(x - a) := by abel
    rw [h]
    simp only [euclideanNorm, euclideanSq, dot, Pi.neg_apply, neg_mul_neg]
  have e : a - b = (a - x) + (x - y) + (y - b) := by abel
  have htri₁ := TimeChange.euclideanNorm_add_le ((a - x) + (x - y)) (y - b)
  have htri₂ := TimeChange.euclideanNorm_add_le (a - x) (x - y)
  rw [← e] at htri₁
  linarith

/-- Full homogenized Gaussian decay for a bounded complex observation of a
Euclidean ball. Joint finite range supplies every independence hypothesis. -/
theorem exists_homogenized_ball_average_bound (d : ℕ) (Λ r ρ B p : ℝ)
    (hρ : 0 ≤ ρ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ f : FieldPair d → ℂ,
      Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|r| + 2 * ρ + 3)
  have hNpos : (0 : ℝ) < N := by linarith [abs_nonneg r]
  haveI : NeZero N := ⟨by intro he; simp only [he, Nat.cast_zero] at hNpos; exact lt_irrefl _ hNpos⟩
  have hgap : r < (N : ℝ) - 1 - 2 * ρ := by linarith [le_abs_self r]
  let e := Fintype.equivFin (Fin d → ZMod N)
  obtain ⟨C, hC, hb⟩ := exists_homogenized_local_average_bound d Λ 1 B p
    (Fintype.card (Fin d → ZMod N)) one_pos hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q P _ hP hfr f hf hfB hmean s hs
  apply hb Q P hP hfr hgap (fun z => e (heatCubeColour N z))
    {y : Vec d | euclideanNorm y < ρ} (clockNbhd ρ)
    (measurableSet_kernelNbhd ρ) ?_ ?_ f hf hfB hmean s hs
  · intro z x hx y hy
    exact Set.mem_iUnion₂.mpr ⟨x, hx, by simpa using hy⟩
  · intro z w hzw hcol x hx y hy
    exact kernelNbhd_separated ρ N hzw (e.injective hcol) hx hy

/-- Stationary spatial averaging respects AE equality, even before choosing
integrable representatives. -/
theorem kernel_average_congr_ae_measure {d : ℕ} (μ : Measure (Vec d)) [SFinite μ]
    (P : Measure (FieldPair d)) [SFinite P] (hP : IsStationary P)
    {f g : FieldPair d → ℂ} (heq : f =ᵐ[P] g) (k : Vec d → ℝ) :
    (fun ω => ∫ x, k x • f (translate x ω) ∂μ) =ᵐ[P]
      (fun ω => ∫ x, k x • g (translate x ω) ∂μ) := by
  have hT : Measurable (fun q : Vec d × FieldPair d => translate q.1 q.2) :=
    Probability.continuous_translate.measurable
  have ht : Measure.QuasiMeasurePreserving
      (fun q : Vec d × FieldPair d => translate q.1 q.2) (μ.prod P) P :=
    QuasiMeasurePreserving.prod_of_right hT (Filter.Eventually.of_forall fun x =>
      (measurePreserving_translate P hP x).quasiMeasurePreserving)
  have hp := ht.ae_eq_comp heq
  have hs := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp)
  filter_upwards [hs] with ω hω
  exact integral_congr_ae (hω.mono fun x hx => congrArg (fun z => k x • z) hx)

/-- Volume specialization of AE invariance of stationary kernel averages. -/
theorem kernel_average_congr_ae {d : ℕ}
    (P : Measure (FieldPair d)) [SFinite P] (hP : IsStationary P)
    {f g : FieldPair d → ℂ} (heq : f =ᵐ[P] g) (k : Vec d → ℝ) :
    (fun ω => ∫ x, k x • f (translate x ω)) =ᵐ[P]
      (fun ω => ∫ x, k x • g (translate x ω)) :=
  kernel_average_congr_ae_measure volume P hP heq k

/-- Full homogenized Gaussian decay for bounded local AE classes. The original
field needs no additional measurability assumption: a clipped local version
supplies the actual independent blocks, and stationarity transfers the average. -/
theorem exists_homogenized_ball_ae_average_bound (d : ℕ) (Λ r ρ B p : ℝ)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ f : FieldPair d → ℂ,
      (∃ g : FieldPair d → ℂ,
        Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] g ∧ g =ᵐ[P] f) →
      (∀ᵐ ω ∂P, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_homogenized_ball_average_bound d Λ r ρ (2 * B) p hρ hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q P _ hP hfr f hlocal hfB hmean s hs
  obtain ⟨g, hg, hgf⟩ := hlocal
  let clip : ℝ → ℝ := fun x => max (-B) (min B x)
  have hc (x : ℝ) : |clip x| ≤ B := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfix (x : ℝ) (hx : |x| ≤ B) : clip x = x := by
    dsimp only [clip]
    rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
  let k : FieldPair d → ℂ := fun ω =>
    (clip (g ω).re : ℂ) + Complex.I * (clip (g ω).im : ℂ)
  have hkr : Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}]
      (fun ω => clip (g ω).re) :=
    measurable_const.max (measurable_const.min (Complex.continuous_re.measurable.comp hg))
  have hki : Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}]
      (fun ω => clip (g ω).im) :=
    measurable_const.max (measurable_const.min (Complex.continuous_im.measurable.comp hg))
  have hk : Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] k :=
    (Complex.measurable_ofReal.comp hkr).add
      (measurable_const.mul (Complex.measurable_ofReal.comp hki))
  have hkB (ω) : ‖k ω‖ ≤ 2 * B := by
    calc
      ‖k ω‖ ≤ ‖(clip (g ω).re : ℂ)‖ + ‖Complex.I * (clip (g ω).im : ℂ)‖ :=
        norm_add_le _ _
      _ = |clip (g ω).re| + |clip (g ω).im| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * B := by linarith [hc (g ω).re, hc (g ω).im]
  have hkf : k =ᵐ[P] f := by
    filter_upwards [hgf, hfB] with ω he hb
    dsimp only [k]
    rw [he, hfix _ ((Complex.abs_re_le_norm _).trans hb),
      hfix _ ((Complex.abs_im_le_norm _).trans hb)]
    simpa only [mul_comm Complex.I] using Complex.re_add_im (f ω)
  have hkm : ∫ ω, k ω ∂P = 0 := (integral_congr_ae hkf).trans hmean
  have hbound := hb Q P hP hfr k hk hkB hkm s hs
  have he := kernel_average_congr_ae P hP hkf
    (anisotropicGaussian (homogenizedCoefficient Q) s)
  exact ⟨hbound.1.ae_eq he, (eLpNorm_congr_ae he).symm ▸ hbound.2⟩

/-- Finite-range decay for a bounded real local AE class. Clipping the local
representative supplies the pointwise bound required by the independent-block
theorem without imposing any extra measurability on the original class. -/
theorem exists_real_local_heat_bound (d : ℕ) (r ρ B p : ℝ)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ f : FieldPair d → ℝ,
      (∃ g : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] g ∧ g =ᵐ[P] f) →
      (∀ᵐ ω ∂P, |f ω| ≤ B) → (∫ ω, f ω ∂P) = 0 →
      ∀ t : ℝ, 0 ≤ t →
      MemLp (Correctors.heatSmoothed t f) (ENNReal.ofReal p) P ∧
      eLpNorm (Correctors.heatSmoothed t f) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hbound⟩ := Clock.eLpNorm_heatSmoothed_local_le (d := d) r ρ B p hρ hp
  refine ⟨C, hC, ?_⟩
  intro P _ hstat hfr f hlocal hfB hfmean t ht
  obtain ⟨g, hg, hgf⟩ := hlocal
  let k : FieldPair d → ℝ := fun ω => max (-B) (min B (g ω))
  have hk : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] k :=
    measurable_const.max (measurable_const.min hg)
  have hkm : Measurable k := hk.mono
    (Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}) le_rfl
  have hkB : ∀ ω, |k ω| ≤ B := by
    intro ω
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hkf : k =ᵐ[P] f := by
    filter_upwards [hgf, hfB] with ω he hb
    dsimp [k]
    rw [he, min_eq_right (abs_le.mp hb).2, max_eq_right (abs_le.mp hb).1]
  have hmean : ∫ ω, k ω ∂P = 0 := (integral_congr_ae hkf).trans hfmean
  have hklocal : Measurable[localSigma
      {y : Vec d | euclideanNorm (y - (0 : Vec d)) < ρ}] k := by
    convert hk using 1; simp
  have hdecay := hbound P hstat hfr k hkm hklocal hkB hmean t ht
  have hheat := Clock.heatSmoothed_congr_ae t hstat hkf
  refine ⟨?_, ?_⟩
  · exact (show MemLp (Correctors.heatSmoothed t k) (ENNReal.ofReal p) P from
      hdecay.trans_lt ENNReal.ofReal_lt_top).ae_eq hheat
  · rw [← eLpNorm_congr_ae hheat]
    exact hdecay

/-- Isotropic heat averaging of a complex field, component by component. -/
noncomputable def complexHeatSmoothed {d : ℕ} (t : ℝ) (f : FieldPair d → ℂ) : FieldPair d → ℂ :=
  fun ω => (Correctors.heatSmoothed t (fun η => (f η).re) ω : ℂ) +
    Complex.I * (Correctors.heatSmoothed t (fun η => (f η).im) ω : ℂ)

@[simp] theorem complexHeatSmoothed_zero {d : ℕ} (f : FieldPair d → ℂ) :
    complexHeatSmoothed 0 f = f := by
  funext ω
  simp only [complexHeatSmoothed, Correctors.heatSmoothed, if_pos rfl]
  exact (Complex.ext (by simp) (by simp))

/-- Complex heat smoothing depends only on the stationary AE class. -/
theorem complexHeatSmoothed_congr_ae {d : ℕ} (t : ℝ)
    {P : Measure (FieldPair d)} [IsProbabilityMeasure P] (hP : IsStationary P)
    {f g : FieldPair d → ℂ} (hfg : f =ᵐ[P] g) :
    complexHeatSmoothed t f =ᵐ[P] complexHeatSmoothed t g := by
  have hre := Clock.heatSmoothed_congr_ae t hP (hfg.fun_comp Complex.re)
  have him := Clock.heatSmoothed_congr_ae t hP (hfg.fun_comp Complex.im)
  filter_upwards [hre, him] with ω hr hi
  dsimp only [Function.comp_def] at hr hi
  simp only [complexHeatSmoothed, hr, hi]

/-- Bounded complex local AE classes inherit the real finite-range heat bound.
The constant is uniform in the stationary law and the chosen representative. -/
theorem exists_complex_local_heat_bound (d : ℕ) (r ρ B p : ℝ)
    (hρ : 0 ≤ ρ) (hB : 0 ≤ B) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ f : FieldPair d → ℂ,
      Integrable f P →
      (∃ g : FieldPair d → ℂ,
        Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] g ∧ g =ᵐ[P] f) →
      (∀ᵐ ω ∂P, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 →
      ∀ t : ℝ, 0 ≤ t →
      MemLp (complexHeatSmoothed t f) (ENNReal.ofReal p) P ∧
      eLpNorm (complexHeatSmoothed t f) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hbound⟩ := exists_real_local_heat_bound d r ρ B p hρ hB hp
  refine ⟨2 * C, by positivity, ?_⟩
  intro P _ hstat hfr f hfi hlocal hfB hfmean t ht
  obtain ⟨g, hg, hgf⟩ := hlocal
  have hre := hbound P hstat hfr (fun ω => (f ω).re)
    ⟨fun ω => (g ω).re, Complex.continuous_re.measurable.comp hg, hgf.fun_comp Complex.re⟩
    (hfB.mono fun ω hω => (Complex.abs_re_le_norm (f ω)).trans hω)
    (by simpa [hfmean] using integral_re hfi) t ht
  have him := hbound P hstat hfr (fun ω => (f ω).im)
    ⟨fun ω => (g ω).im, Complex.continuous_im.measurable.comp hg, hgf.fun_comp Complex.im⟩
    (hfB.mono fun ω hω => (Complex.abs_im_le_norm (f ω)).trans hω)
    (by simpa [hfmean] using integral_im hfi) t ht
  let u : FieldPair d → ℂ := fun ω =>
    (Correctors.heatSmoothed t (fun η => (f η).re) ω : ℂ)
  let v : FieldPair d → ℂ := fun ω =>
    (Correctors.heatSmoothed t (fun η => (f η).im) ω : ℂ)
  have hu : MemLp u (ENNReal.ofReal p) P := hre.1.ofReal
  have hv : MemLp v (ENNReal.ofReal p) P := him.1.ofReal
  have heu : eLpNorm u (ENNReal.ofReal p) P =
      eLpNorm (Correctors.heatSmoothed t (fun η => (f η).re)) (ENNReal.ofReal p) P :=
    eLpNorm_congr_norm_ae hu.aestronglyMeasurable hre.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => Complex.norm_real _)
  have hev : eLpNorm v (ENNReal.ofReal p) P =
      eLpNorm (Correctors.heatSmoothed t (fun η => (f η).im)) (ENNReal.ofReal p) P :=
    eLpNorm_congr_norm_ae hv.aestronglyMeasurable him.1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => Complex.norm_real _)
  have heI : eLpNorm (Complex.I • v) (ENNReal.ofReal p) P =
      eLpNorm v (ENNReal.ofReal p) P := by
    rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_I,
      ENNReal.ofReal_one, one_mul]
  have he : complexHeatSmoothed t f = u + Complex.I • v := rfl
  rw [he]
  refine ⟨hu.add (hv.const_smul Complex.I), ?_⟩
  calc
    eLpNorm (u + Complex.I • v) (ENNReal.ofReal p) P ≤
        eLpNorm u (ENNReal.ofReal p) P +
          eLpNorm (Complex.I • v) (ENNReal.ofReal p) P :=
      eLpNorm_add_le (ENNReal.one_le_ofReal.mpr hp)
    _ ≤ ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) +
        ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) := by
      rw [heu, heI, hev]
      exact add_le_add hre.2 him.2
    _ = ENNReal.ofReal ((2 * C) * (1 + t) ^ (-(d : ℝ) / 4)) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

/-- The exact endpoints premise gives a centered local force quotient for any
single-force semigroup witness. The other forces use the proved canonical
evolution, so no additional family-existence premise is required. -/
theorem exists_force_quotient
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 0 ≤ T) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    ∃ E E₀ H : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P Pdag β a μ t ∧
      (E₀ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν 0 (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
          (fun s => complexL2Transpose (reducedLaw Q)
            (forcedComplexEvolution Q ⟨0, by omega⟩ 0 s)) β a μ t ∧
      E - E₀ = ζ • H ∧ (∫ ω, H ω ∂reducedLaw Q) = 0 ∧ ‖H‖ ≤ C ∧
      ∀ ρ : ℝ, C ≤ ρ →
      ∃ K : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      ∃ K₂ : Lp ℂ 2 (reducedLaw Q),
        (K : FieldPair d → ℂ) =ᵐ[reducedLaw Q] K₂ ∧
        IsComplexLocalObservation Q ρ K₂ ∧
        (∫ ω, K ω ∂reducedLaw Q) = 0 ∧ ‖K‖ ≤ C ∧
        ‖H - K‖ ≤ C * Real.exp (-c * ρ ^ 2) := by
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C, c, hC, hc, hpacket⟩ := hends d hd D p hp T 3 hT (by norm_num)
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
  let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
  obtain ⟨E, H, he, _, _, _, hfactor, hlocal⟩ :=
    hpacket Q hQ β a μ hβ ha hμ F Fdag
      (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ z)
      (fun z => isComplexTransposeSemigroup_complexL2Transpose Q (F z)) ν t ht
  have hP' : P = F ζ := hP.eq_forcedComplexEvolution
  have hPdag' : Pdag = Fdag ζ := by
    rw [hPdag.eq_complexL2Transpose, hP']
  have hz : ‖ζ‖ < 3 := by linarith
  obtain ⟨hf, hm, hn⟩ := hfactor ζ hz
  refine ⟨E ζ, E 0, H ζ, ?_, he 0, hf, hm, hn, ?_⟩
  · simpa only [hP', hPdag'] using he ζ
  · intro ρ hρ
    obtain ⟨L, K, L₂, K₂, hrep, _, _, _, _, _, hK⟩ := hlocal ρ hρ
    obtain ⟨_, _, hmean, hnorm, herr⟩ := hK ζ hz
    exact ⟨K ζ, K₂ ζ, (hrep ζ).2.1, (hrep ζ).2.2.2, hmean, hnorm, herr⟩

/-- The literal coordinate derivative of the full homogenized density is
absolutely integrable at every positive spatial scale. -/
theorem integrable_homogenizedDensity_derivative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : Vec d =>
      fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) := by
  have hsym : (homogenizedCoefficient Q).transpose = homogenizedCoefficient Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (posDef_homogenizedCoefficient Q).isHermitian.eq
  simp_rw [fderiv_anisotropicGaussian_coordinate _ hsym]
  convert (integrable_mulVec_mul_anisotropicGaussian _
    (posDef_homogenizedCoefficient Q) (homogenizedCoefficient Q)⁻¹ j s hs).const_mul
      (-1 / s) using 1
  funext x
  ring

/-- Coordinate derivatives of the actual centered density have zero spatial
integral, preserving the cancellation used by the flux representation. -/
theorem integral_homogenizedDensity_derivative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (s : ℝ) :
    (∫ x : Vec d,
      fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) = 0 := by
  have hsym : (homogenizedCoefficient Q).transpose = homogenizedCoefficient Q := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (posDef_homogenizedCoefficient Q).isHermitian.eq
  simp_rw [fderiv_anisotropicGaussian_coordinate _ hsym]
  have he (x : Vec d) :
      -(homogenizedCoefficient Q)⁻¹.mulVec x j / s *
        anisotropicGaussian (homogenizedCoefficient Q) s x =
      (-1 / s) * ((homogenizedCoefficient Q)⁻¹.mulVec x j *
        anisotropicGaussian (homogenizedCoefficient Q) s x) := by ring
  simp_rw [he]
  rw [integral_const_mul, integral_mulVec_mul_anisotropicGaussian, mul_zero]

/-- The full Gaussian derivative gains one inverse square root of scale in L1.
The second moment and inverse-entry bound retain the actual covariance and give
a deterministic constant before the environment law. -/
theorem integral_norm_homogenizedDensity_derivative_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) {s : ℝ} (hs : 0 < s) :
    (∫ x : Vec d,
      ‖fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)‖) ≤
      (sourceReducedBound Λ + 1) * s ^ (-(1 : ℝ) / 2) := by
  let A := homogenizedCoefficient Q
  let G := anisotropicGaussian A s
  let v : Vec d → ℝ := fun x => A⁻¹.mulVec x j
  have hA : A.PosDef := posDef_homogenizedCoefficient Q
  have hsym : A.transpose = A := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hA.isHermitian.eq
  have hG (x : Vec d) : 0 ≤ G x := by dsimp [G, anisotropicGaussian]; positivity
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hfirst := integrable_mulVec_mul_anisotropicGaussian A hA A⁻¹ j s hs
  have habs : Integrable (fun x => |v x| * G x) := by
    convert hfirst.norm using 1
    funext x
    change |v x| * G x = ‖v x * G x‖
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hG x)]
  have hsecond := integrable_mulVec_mulVec_mul_anisotropicGaussian A hA A⁻¹ A⁻¹ j j s hs
  have hden := integrable_anisotropicGaussian A hA s hs
  have hupper := (hsecond.const_mul (Real.sqrt s)⁻¹).add (hden.const_mul (Real.sqrt s))
  have hpoint (x : Vec d) : |v x| * G x ≤
      (Real.sqrt s)⁻¹ * (v x * v x * G x) + Real.sqrt s * G x := by
    have hv : |v x| ≤ (Real.sqrt s)⁻¹ * (v x * v x) + Real.sqrt s := by
      apply (mul_le_mul_iff_left₀ hroot).mp
      have he : ((Real.sqrt s)⁻¹ * (v x * v x) + Real.sqrt s) * Real.sqrt s =
          v x * v x + s := by
        rw [add_mul, mul_right_comm, inv_mul_cancel₀ hroot.ne', one_mul, hsq]
      rw [he]
      nlinarith [sq_nonneg (|v x| - Real.sqrt s), sq_abs (v x)]
    nlinarith [mul_le_mul_of_nonneg_right hv (hG x)]
  have hm : (∫ x, |v x| * G x) ≤ Real.sqrt s * (sourceReducedBound Λ + 1) := by
    calc
      _ ≤ ∫ x, (Real.sqrt s)⁻¹ * (v x * v x * G x) + Real.sqrt s * G x :=
        integral_mono habs hupper hpoint
      _ = (Real.sqrt s)⁻¹ * (s * A⁻¹ j j) + Real.sqrt s := by
        rw [integral_add (hsecond.const_mul _) (hden.const_mul _), integral_const_mul,
          integral_const_mul, integral_inv_mulVec_mulVec_mul_anisotropicGaussian A hA j j s hs,
          integral_anisotropicGaussian A hA s hs, mul_one]
      _ = Real.sqrt s * (A⁻¹ j j + 1) := by
        have he : (Real.sqrt s)⁻¹ * s = Real.sqrt s := by
          calc
            _ = (Real.sqrt s)⁻¹ * (Real.sqrt s * Real.sqrt s) := by rw [hsq]
            _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hroot.ne', one_mul]
        rw [← mul_assoc, he]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by
        have he := (le_abs_self _).trans (abs_homogenizedCoefficient_inv_entry_le Q j j)
        change (homogenizedCoefficient Q)⁻¹ j j + 1 ≤ sourceReducedBound Λ + 1
        linarith) hroot.le
  have hn (x : Vec d) :
      ‖fderiv ℝ (anisotropicGaussian A s) x (unitVector j)‖ =
        s⁻¹ * (|v x| * G x) := by
    rw [fderiv_anisotropicGaussian_coordinate A hsym]
    change |-(v x) / s * G x| = s⁻¹ * (|v x| * G x)
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hs, abs_of_nonneg (hG x)]
    ring
  change (∫ x : Vec d, ‖fderiv ℝ (anisotropicGaussian A s) x (unitVector j)‖) ≤ _
  simp_rw [hn]
  rw [integral_const_mul]
  calc
    _ ≤ s⁻¹ * (Real.sqrt s * (sourceReducedBound Λ + 1)) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr hs.le)
    _ = (sourceReducedBound Λ + 1) * s ^ (-(1 : ℝ) / 2) := by
      rw [neg_div, Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
      have he : s⁻¹ * Real.sqrt s = (Real.sqrt s)⁻¹ := by
        apply mul_right_cancel₀ hroot.ne'
        rw [mul_assoc, hsq, inv_mul_cancel₀ hs.ne', inv_mul_cancel₀ hroot.ne']
      rw [← mul_assoc, he, mul_comm]

/-- At zero force the complex kernel derivative is exactly the real density
derivative, including its absolute value. -/
theorem norm_homogenizedKernel_zero_derivative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖fderiv ℝ (homogenizedGaussianKernel Q j s hs 0) x (unitVector j)‖ =
      ‖fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)‖ := by
  rw [fderiv_homogenizedGaussianKernel_zero_coordinate,
    homogenizedGaussianKernel_zero_eq_ofReal, ← Complex.ofReal_mul,
    Complex.norm_real,
    fderiv_anisotropicGaussian_coordinate (homogenizedCoefficient Q)
      (homogenizedMatrix_transpose Q)]

/-- The actual homogenized density derivative has the parabolic supremum rate.
The displayed structural constant is independent of the environment law. -/
theorem norm_homogenizedDensity_derivative_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)‖ ≤
      (gaussianSchwartzBound d Λ 0 * Real.exp (gaussianSchwartzBound d Λ 0)) *
        s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 2) := by
  let R := Real.sqrt s
  have hR : 0 < R := Real.sqrt_pos.mpr hs
  have hRs : R ^ 2 * 1 = s := by simpa only [mul_one] using Real.sq_sqrt hs.le
  have hu := (homogenizedGaussianKernel_weighted_coordinate_bounds Q j 1 one_pos
    (by norm_num) le_rfl 0 (R⁻¹ • x) 0).2.1 j
  simp only [pow_zero, one_mul, norm_zero, add_zero, one_pow, mul_one] at hu
  have he := fderiv_homogenizedGaussianKernel_parabolic_scale Q j j R 1 hR one_pos 0 x
  have hker : homogenizedGaussianKernel Q j (R ^ 2 * 1)
      (mul_pos (sq_pos_of_pos hR) one_pos) 0 =
      homogenizedGaussianKernel Q j s hs 0 := by
    unfold homogenizedGaussianKernel
    rw [hRs]
  rw [hker, zero_mul] at he
  have hcoef : 0 ≤ R ^ (-(d : ℝ)) / R := div_nonneg (Real.rpow_nonneg hR.le _) hR.le
  have hn := congrArg norm he
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hcoef] at hn
  have hp : R ^ (-(d : ℝ)) / R = s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 2) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg_one R, ← Real.rpow_add hR,
      show R = s ^ ((1 : ℝ) / 2) from Real.sqrt_eq_rpow s,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  calc
    _ = (R ^ (-(d : ℝ)) / R) *
        ‖fderiv ℝ (homogenizedGaussianKernel Q j 1 one_pos 0) (R⁻¹ • x) (unitVector j)‖ := by
      rw [← norm_homogenizedKernel_zero_derivative Q j hs x, hn]
    _ ≤ (R ^ (-(d : ℝ)) / R) *
        (gaussianSchwartzBound d Λ 0 * Real.exp (gaussianSchwartzBound d Λ 0)) :=
      mul_le_mul_of_nonneg_left hu hcoef
    _ = _ := by rw [hp, mul_comm]

/-- The actual signed derivative kernel has square-summable absolute cube
masses, with the extra full inverse-scale gain over density cube masses. -/
theorem summable_sq_homogenizedDensity_derivative_cubeMass {d : ℕ} {Λ r L s : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (hL : 0 < L) (hs : 0 < s) :
    let k := fun x : Vec d =>
      fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)
    Summable (fun z => kernelCubeMass L k z ^ 2) ∧
      (∑' z, kernelCubeMass L k z ^ 2) ≤
        ((gaussianSchwartzBound d Λ 0 * Real.exp (gaussianSchwartzBound d Λ 0)) *
          (sourceReducedBound Λ + 1) * L ^ d) * s ^ (-(1 : ℝ) - (d : ℝ) / 2) := by
  dsimp only
  let K := gaussianSchwartzBound d Λ 0 * Real.exp (gaussianSchwartzBound d Λ 0)
  have hK : 0 ≤ K := by
    exact mul_nonneg (gaussianSchwartzBound_pos d Λ Q.ellipticity_parameter 0).le
      (Real.exp_pos _).le
  have h := summable_sq_kernelCubeMass hL
    (integrable_homogenizedDensity_derivative Q j hs)
    (fun z => kernelCubeMass_le_of_bound hL
      (norm_homogenizedDensity_derivative_le Q j hs) z)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ (K * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 2) * L ^ d) *
        ((sourceReducedBound Λ + 1) * s ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (integral_norm_homogenizedDensity_derivative_le Q j hs)
        (by positivity)
    _ = _ := by
      have he : (-(1 : ℝ) / 2 - (d : ℝ) / 2) + (-(1 : ℝ) / 2) =
          -(1 : ℝ) - (d : ℝ) / 2 := by ring
      rw [← he, Real.rpow_add hs]
      dsimp only [K]
      ring

/-- Finite-range averaging of the actual density derivative, with its full
extra inverse-square-root decay and a constant before both laws. -/
theorem exists_homogenized_derivative_local_average_bound (d : ℕ) (Λ L B p : ℝ)
    (N : ℕ) (hL : 0 < L) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → ∀ {r R : ℝ}, HasFiniteRange r P → r < R →
      ∀ (col : (Fin d → ℤ) → Fin N) (U : Set (Vec d))
        (W : (Fin d → ℤ) → Set (Vec d)),
      (∀ z, MeasurableSet (W z)) →
      (∀ z, ∀ x ∈ heatCube L z, ∀ y ∈ U, x + y ∈ W z) →
      (∀ z w, z ≠ w → col z = col w →
        ∀ x ∈ W z, ∀ y ∈ W w, R ≤ euclideanNorm (x - y)) →
      ∀ f : FieldPair d → ℂ, Measurable[localSigma U] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ (j : Fin d) (s : ℝ), 0 < s →
      MemLp (fun ω => ∫ x, (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  let K : ℝ := |(gaussianSchwartzBound d Λ 0 * Real.exp (gaussianSchwartzBound d Λ 0)) *
    (sourceReducedBound Λ + 1)|
  let A : ℝ := B ^ 2 * K * L ^ d
  let H : ℝ := (N : ℝ) * Probability.hoeffdingMomentConst p ^ (1 / p)
  have hK : 0 ≤ K := by exact abs_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hH : 0 ≤ H := by
    dsimp [H, Probability.hoeffdingMomentConst]
    positivity
  refine ⟨2 * H * A ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro r₀ Q P _ hP r R hfr hR col U W hW hUW hsep f hf hfB hmean j s hs
  have hm := summable_sq_homogenizedDensity_derivative_cubeMass Q j hL hs
  have hmass := hm.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (pow_nonneg hL.le d))
    (Real.rpow_nonneg hs.le _))
  have hsum : (∑' z, (B * kernelCubeMass L
      (fun x => fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) z) ^ 2) ≤
      A * s ^ (-(1 : ℝ) - (d : ℝ) / 2) := by
    simp only [mul_pow]
    rw [tsum_mul_left]
    calc
      _ ≤ B ^ 2 * ((K * L ^ d) * s ^ (-(1 : ℝ) - (d : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left hmass (sq_nonneg B)
      _ = _ := by dsimp [A]; ring
  have hroot := Real.rpow_le_rpow
    (tsum_nonneg fun z => sq_nonneg (B * kernelCubeMass L
      (fun x => fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) z)) hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hscale : (A * s ^ (-(1 : ℝ) - (d : ℝ) / 2)) ^ (1 / 2 : ℝ) =
      A ^ (1 / 2 : ℝ) * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4) := by
    rw [Real.mul_rpow hA (Real.rpow_nonneg hs.le _), ← Real.rpow_mul hs.le]
    congr 2
    ring
  rw [hscale] at hroot
  have hkm : Measurable (fun x => fderiv ℝ
      (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) := by
    simp_rw [fderiv_anisotropicGaussian_coordinate (homogenizedCoefficient Q)
      (homogenizedMatrix_transpose Q)]
    have hg := (contDiff_anisotropicGaussian (homogenizedCoefficient Q) s).continuous
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hb := eLpNorm_kernelAverage_le hP hfr hR hL col U W hW hUW hsep
    (integrable_homogenizedDensity_derivative Q j hs) hkm
    (kernelCubeMass_le_of_bound hL (norm_homogenizedDensity_derivative_le Q j hs)) hf hfB hmean p hp
  refine ⟨hb.1, hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc
    _ ≤ 2 * (H * (A ^ (1 / 2 : ℝ) * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hroot hH) (by norm_num)
    _ = _ := by ring

/-- The derivative averaging bound with all ball-colouring geometry discharged. -/
theorem exists_homogenized_derivative_ball_average_bound (d : ℕ) (Λ r ρ B p : ℝ)
    (hρ : 0 ≤ ρ) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ f : FieldPair d → ℂ,
      Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ (j : Fin d) (s : ℝ), 0 < s →
      MemLp (fun ω => ∫ x, (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, (fderiv ℝ (anisotropicGaussian (homogenizedCoefficient Q) s) x (unitVector j)) •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * s ^ (-(1 : ℝ) / 2 - (d : ℝ) / 4)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (|r| + 2 * ρ + 3)
  have hNpos : (0 : ℝ) < N := by linarith [abs_nonneg r]
  haveI : NeZero N := ⟨by intro he; simp only [he, Nat.cast_zero] at hNpos; exact lt_irrefl _ hNpos⟩
  have hgap : r < (N : ℝ) - 1 - 2 * ρ := by linarith [le_abs_self r]
  let e := Fintype.equivFin (Fin d → ZMod N)
  obtain ⟨C, hC, hb⟩ := exists_homogenized_derivative_local_average_bound d Λ 1 B p
    (Fintype.card (Fin d → ZMod N)) one_pos hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q P _ hP hfr f hf hfB hmean j s hs
  apply hb Q P hP hfr hgap (fun z => e (heatCubeColour N z))
    {y : Vec d | euclideanNorm y < ρ} (clockNbhd ρ)
    (measurableSet_kernelNbhd ρ) ?_ ?_ f hf hfB hmean j s hs
  · intro z x hx y hy
    exact Set.mem_iUnion₂.mpr ⟨x, hx, by simpa using hy⟩
  · intro z w hzw hcol x hx y hy
    exact kernelNbhd_separated ρ N hzw (e.injective hcol) hx hy


/-- Bounds for every set integral control both components of an integrable
complex random variable, without selecting a pointwise representative. -/
theorem ae_norm_le_of_setIntegral_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℂ} (hf : Integrable f μ)
    {B : ℝ} (hb : ∀ s, MeasurableSet s → ‖∫ ω in s, f ω ∂μ‖ ≤ B * μ.real s) :
    ∀ᵐ ω ∂μ, ‖f ω‖ ≤ 2 * B := by
  have hpart (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖) :
      ∀ᵐ ω ∂μ, |L (f ω)| ≤ B := by
    have hi := L.integrable_comp hf
    have hsbound (s : Set Ω) (hs : MeasurableSet s) :
        |∫ ω in s, L (f ω) ∂μ| ≤ B * μ.real s := by
      rw [L.integral_comp_comm hf.integrableOn]
      exact (hL _).trans (hb s hs)
    have hu := ae_le_of_forall_setIntegral_le hi (integrable_const B) (fun s hs _ => by
      simpa only [integral_const, smul_eq_mul, measureReal_def,
        Measure.restrict_apply_univ, mul_comm] using
        (le_abs_self _).trans (hsbound s hs))
    have hl := ae_le_of_forall_setIntegral_le (integrable_const (-B)) hi (fun s hs _ => by
      have hh := (abs_le.mp (hsbound s hs)).1
      simpa only [integral_const, smul_eq_mul, measureReal_def,
        Measure.restrict_apply_univ, mul_neg, neg_mul, mul_comm] using hh)
    filter_upwards [hu, hl] with ω hu hl
    exact abs_le.mpr ⟨hl, hu⟩
  have hre := hpart Complex.reCLM Complex.abs_re_le_norm
  have him := hpart Complex.imCLM Complex.abs_im_le_norm
  filter_upwards [hre, him] with ω hre him
  change |(f ω).re| ≤ B at hre
  change |(f ω).im| ≤ B at him
  calc
    ‖f ω‖ = ‖((f ω).re : ℂ) + (f ω).im * Complex.I‖ := by rw [Complex.re_add_im]
    _ ≤ ‖((f ω).re : ℂ)‖ + ‖(f ω).im * Complex.I‖ := norm_add_le _ _
    _ = |(f ω).re| + |(f ω).im| := by
      simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 2 * B := by linarith

/-- Schwarz applied to all bounded set-integral functionals gives a uniform
AE bound for a holomorphic force quotient. Only the original L2 classes occur. -/
theorem ae_norm_holomorphic_quotient_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {E H : ℂ → Lp ℂ 2 μ} {B : ℝ} (hB : 0 ≤ B)
    (hE : DifferentiableOn ℂ E (Metric.ball 0 3))
    (hbound : ∀ z ∈ Metric.ball (0 : ℂ) 3, ∀ᵐ ω ∂μ, ‖E z ω‖ ≤ B)
    (hfactor : ∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 2) (hζne : ζ ≠ 0) :
    ∀ᵐ ω ∂μ, ‖H ζ ω‖ ≤ 4 * B := by
  have hint : Integrable (H ζ) μ := (Lp.memLp _).integrable (by norm_num)
  have hset (s : Set Ω) (hs : MeasurableSet s) :
      ‖∫ ω in s, H ζ ω ∂μ‖ ≤ (2 * B) * μ.real s := by
    let J : Lp ℂ 2 μ →L[ℂ] ℂ :=
      innerSL ℂ (indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ))
    have hJ (f : Lp ℂ 2 μ) : J f = ∫ ω in s, f ω ∂μ :=
      L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) f
    have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 3 := by simp
    have hz : ζ ∈ Metric.ball (0 : ℂ) 3 := by
      simpa only [Metric.mem_ball, dist_zero_right] using (lt_of_le_of_lt hζ (by norm_num : (2 : ℝ) < 3))
    have hm : Set.MapsTo (fun z => J (E z)) (Metric.ball 0 3)
        (Metric.closedBall (J (E 0)) (2 * B * μ.real s)) := by
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have hbz : ‖J (E z)‖ ≤ B * μ.real s := by
        rw [hJ]
        exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ s)
          (ae_restrict_of_ae (hbound z hz))
      have hb0 : ‖J (E 0)‖ ≤ B * μ.real s := by
        rw [hJ]
        exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ s)
          (ae_restrict_of_ae (hbound 0 hzero))
      exact (norm_sub_le _ _).trans (by linarith)
    have hh := Complex.norm_dslope_le_div_of_mapsTo_ball
      (J.differentiable.comp_differentiableOn hE) hm hz
    have heq : dslope (fun z => J (E z)) 0 ζ = J (H ζ) := by
      rw [dslope_of_ne _ hζne, slope_def_module, sub_zero, ← map_sub, hfactor ζ hz,
        map_smul, inv_smul_smul₀ hζne]
    simp only [Function.comp_def] at hh
    rw [heq, hJ] at hh
    exact hh.trans (by nlinarith [mul_nonneg hB (by positivity : 0 ≤ μ.real s)])
  have hb := ae_norm_le_of_setIntegral_norm_le hint hset
  simpa only [show 2 * (2 * B) = 4 * B by ring] using hb


/-- V1 also bounds the larger force disc used in Cauchy estimates. -/
theorem positive_time_bound_on_four (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 4 → ∀ t : ℝ≥0, 0 < (t : ℝ) → (t : ℝ) ≤ T →
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ C := by
  obtain ⟨A, c, N, hA, _, hloc⟩ := hlocal d hd D
  let K := A * (2 + T) ^ N * Real.exp (A * 16 * T)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨1 + 2 * K, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht htT
  obtain ⟨G, _, _, hb⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hz2 : ‖ζ‖ ^ 2 ≤ 16 := by nlinarith [norm_nonneg ζ]
  have hp : (2 + (t : ℝ)) ^ N ≤ (2 + T) ^ N :=
    pow_le_pow_left₀ (by positivity) (by linarith) N
  have he : Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (A * 16 * T) := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hz2 hA0)
      t.coe_nonneg).trans (mul_le_mul_of_nonneg_left htT (by positivity))
  have hbound : A * (2 + (t : ℝ)) ^ N * Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ K :=
    mul_le_mul (mul_le_mul_of_nonneg_left hp hA0) he (Real.exp_pos _).le
      (by positivity)
  have hu : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ K := by
    filter_upwards [hb t ht (by linarith)] with ω h
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (h.trans hbound)
  exact (ae_norm_indexed_le hd Q ν ζ P Pdag β a μ t hK hu).mono
    fun ω h => h.trans (by linarith)

/-- Literal time-zero observations on the same larger force disc. -/
theorem zero_time_bound_on_four (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 4 →
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ ≤ C := by
  obtain ⟨K, hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨1 + 10 * K, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hu : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ ≤ 5 * K := by
    rcases ν with i | b
    · simp only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply]
      filter_upwards [Lp.coeFn_add (β i) (ζ • a ⟨0, by omega⟩ i),
        Lp.coeFn_smul ζ (a ⟨0, by omega⟩ i), hb i, ha' ⟨0, by omega⟩ i]
        with ω he hs hbω haω
      rw [he, Pi.add_apply, hs, Pi.smul_apply]
      exact (norm_add_le _ _).trans (by rw [norm_smul]; nlinarith [norm_nonneg ζ])
    · cases b
      · simp only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply]
        filter_upwards [Lp.coeFn_smul ζ μ, hm] with ω he hmω
        rw [he, Pi.smul_apply, norm_smul]
        nlinarith [norm_nonneg ζ]
      · simp only [uncenteredEndpoint, transposeEndpoint, hPdag.zero hP,
          ContinuousLinearMap.id_apply]
        exact (hb ⟨0, by omega⟩).mono fun ω h => h.trans (by linarith)
  exact (ae_norm_indexed_le hd Q ν ζ P Pdag β a μ 0 (by positivity) hu).mono
    fun ω h => h.trans (by linarith)

/-- A common AE endpoint bound on the radius-four disc, uniformly including
zero time. This uses precisely the pointwise clause of V1. -/
theorem ae_point_bound_on_four (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 4 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω‖ ≤ C := by
  obtain ⟨C₀, hC₀, hb₀⟩ := zero_time_bound_on_four d hd D
  obtain ⟨C₁, _, hb₁⟩ := positive_time_bound_on_four hlocal d hd D T hT
  refine ⟨max C₀ C₁, hC₀.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  by_cases hz : t = 0
  · subst t
    exact (hb₀ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ).mono
      fun ω h => h.trans (le_max_left _ _)
  · have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hz)
    exact (hb₁ Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t htpos ht).mono
      fun ω h => h.trans (le_max_right _ _)

/-- V1 and the exact endpoint analyticity premise bound the actual force
quotient almost everywhere, uniformly on the closed force disc. -/
theorem exists_ae_bounded_force_quotient
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    ∃ E E₀ H : Lp ℂ 2 (reducedLaw Q),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P Pdag β a μ t ∧
      (E₀ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν 0 (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
          (fun s => complexL2Transpose (reducedLaw Q)
            (forcedComplexEvolution Q ⟨0, by omega⟩ 0 s)) β a μ t ∧
      E - E₀ = ζ • H ∧ (∫ ω, H ω ∂reducedLaw Q) = 0 ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ C) := by
  obtain ⟨A, hA, hbound⟩ := ae_point_bound_on_four hlocal d hd D T hT
  obtain ⟨_, _, _, _, hpacket⟩ := hends d hd D 2 (by norm_num) T 3 hT (by norm_num)
  refine ⟨4 * A, by linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
  let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
  have hF := fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q
    (⟨0, by omega⟩ : Fin d) z
  have hFdag := fun z => isComplexTransposeSemigroup_complexL2Transpose Q (F z)
  suffices hdata : ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
      DifferentiableOn ℂ E {z : ℂ | ‖z‖ < 4} ∧
      (∀ z : ℂ, ‖z‖ < 3 → E z - E 0 = z • H z ∧
        (∫ ω, H z ω ∂reducedLaw Q) = 0) by
    obtain ⟨E, H, he, hE, hfactor⟩ := hdata
    have hP' : P = F ζ := hP.eq_forcedComplexEvolution
    have hPdag' : Pdag = Fdag ζ := by
      rw [hPdag.eq_complexL2Transpose, hP']
    have hre : (E ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P Pdag β a μ t := by
      simpa only [hP', hPdag'] using he ζ
    by_cases hz : ζ = 0
    · refine ⟨E ζ, E 0, 0, hre, he 0, ?_, by simp, ?_⟩
      · simp [hz]
      · filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
        simp only [hω, Pi.zero_apply, norm_zero]
        linarith
    · have hdisc : Metric.ball (0 : ℂ) 3 ⊆ {z : ℂ | ‖z‖ < 4} := by
        intro z hz
        have := Metric.mem_ball.mp hz
        simp only [dist_zero_right] at this
        dsimp
        linarith
      have hb : ∀ z ∈ Metric.ball (0 : ℂ) 3, ∀ᵐ ω ∂reducedLaw Q, ‖E z ω‖ ≤ A := by
        intro z hz
        have hz4 : ‖z‖ ≤ 4 := by
          have := Metric.mem_ball.mp hz
          simp only [dist_zero_right] at this
          linarith
        filter_upwards [he z,
          hbound Q hQ β a μ hβ ha hμ z (F z) (Fdag z) (hF z) (hFdag z) ν hz4 t ht]
          with ω heω hbω
        simpa only [heω] using hbω
      have hf : ∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z := by
        intro z hz
        exact (hfactor z (by simpa using hz)).1
      have hquot := ae_norm_holomorphic_quotient_le (by linarith : 0 ≤ A)
        (hE.mono hdisc) hb hf hζ hz
      exact ⟨E ζ, E 0, H ζ, hre, he 0,
        (hfactor ζ (by linarith)).1, (hfactor ζ (by linarith)).2, hquot⟩

  have hcast (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q = 2)
      (h : ∃ E H : ℂ → Lp ℂ q (reducedLaw Q),
        (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
        DifferentiableOn ℂ E {z : ℂ | ‖z‖ < 4} ∧
        (∀ z : ℂ, ‖z‖ < 3 → E z - E 0 = z • H z ∧
          (∫ ω, H z ω ∂reducedLaw Q) = 0)) :
      ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
        (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
        DifferentiableOn ℂ E {z : ℂ | ‖z‖ < 4} ∧
        (∀ z : ℂ, ‖z‖ < 3 → E z - E 0 = z • H z ∧
          (∫ ω, H z ω ∂reducedLaw Q) = 0) := by
    subst q
    exact h
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  apply hcast (ENNReal.ofReal (2 : ℝ)) (by norm_num)
  obtain ⟨E, H, he, hE, _, _, hf, _⟩ :=
    hpacket Q hQ β a μ hβ ha hμ F Fdag hF hFdag ν t ht
  exact ⟨E, H, he, by convert hE using 1 <;> norm_num,
    fun z hz => ⟨(hf z hz).1, (hf z hz).2.1⟩⟩

/-- Conditional projection retains an AE uniform bound on the original class. -/
theorem ae_norm_project_le {Ω : Type*} [m0 : MeasurableSpace Ω]
    {μ : Measure Ω} {m : MeasurableSpace Ω}
    (f : Lp ℂ 2 μ) {B : ℝ} (hf : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ B) :
    ∀ᵐ ω ∂μ, ‖EndpointProjection.project (m := m) f ω‖ ≤ B := by
  filter_upwards [EndpointProjection.project_ae (m := m) f,
    ae_bdd_norm_condExp_of_ae_bdd_norm (m := m) hf] with ω he hb
  simpa only [he] using hb

/-- An actual local approximation controls the fixed projection pointwise AE. -/
theorem ae_norm_sub_project_of_local_approximation {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ρ : ℝ) (E U V : Lp ℂ 2 (reducedLaw Q))
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] U)
    (hV : IsComplexLocalObservation Q ρ V) {ε : ℝ}
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q, ‖E ω - EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E ω‖ ≤ 2 * ε := by
  let m := localSigma {x : Vec d | euclideanNorm x < ρ}
  have hm := Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}
  obtain ⟨v, hv, hve⟩ := hV
  have he : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - v ω‖ ≤ ε := by
    filter_upwards [herr, hve] with ω h h' using h' ▸ h
  have hb := AnnuliSupport.ae_norm_condExpL2_sub_le hm le_rfl U v hv he
  have hp : (EndpointProjection.project (m := m) E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      (condExpL2 ℂ ℂ hm U : FieldPair d → ℂ) :=
    (EndpointProjection.project_ae E).trans
      ((condExp_congr_ae hE).trans (AnnuliSupport.condExpL2_ae_eq hm U).symm)
  filter_upwards [hE, hp, hb] with ω he hp hb
  rw [he, hp, norm_sub_rev]
  exact hb

/-- A fixed conditional projection preserves the quotient factorization. -/
theorem sub_project_force_factor {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    (E E₀ H : Lp ℂ 2 μ) (ζ : ℂ) (hf : E - E₀ = ζ • H) :
    (E - EndpointProjection.project (m := m) E) -
      (E₀ - EndpointProjection.project (m := m) E₀) =
      ζ • (H - EndpointProjection.project (m := m) H) := by
  let P := EndpointProjection.projectionCLM (μ := μ) (m := m) (p := 2)
  have hp := congrArg P hf
  change P (E - E₀) = P (ζ • H) at hp
  simp only [map_sub, map_smul] at hp
  change (E - P E) - (E₀ - P E₀) = ζ • (H - P H)
  calc
    (E - P E) - (E₀ - P E₀) = (E - E₀) - (P E - P E₀) := by abel
    _ = ζ • (H - P H) := by rw [hf, hp, smul_sub]

/-- Schwarz transfers an AE error bound for the analytic endpoint family to
its quotient under one fixed conditional projection. -/
theorem ae_norm_quotient_sub_project_le {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {m : MeasurableSpace Ω}
    {E H : ℂ → Lp ℂ 2 μ} {ε : ℝ} (hε : 0 ≤ ε)
    (hE : DifferentiableOn ℂ E (Metric.ball 0 3))
    (herr : ∀ z ∈ Metric.ball (0 : ℂ) 3,
      ∀ᵐ ω ∂μ, ‖E z ω - EndpointProjection.project (m := m) (E z) ω‖ ≤ ε)
    (hf : ∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z)
    {ζ : ℂ} (hζ : ‖ζ‖ ≤ 2) (hζne : ζ ≠ 0) :
    ∀ᵐ ω ∂μ, ‖H ζ ω - EndpointProjection.project (m := m) (H ζ) ω‖ ≤ 4 * ε := by
  have hdiff := hE.sub (EndpointProjection.differentiableOn_project (m := m) hE)
  have hb : ∀ z ∈ Metric.ball (0 : ℂ) 3, ∀ᵐ ω ∂μ,
      ‖(E z - EndpointProjection.project (m := m) (E z)) ω‖ ≤ ε := by
    intro z hz
    filter_upwards [herr z hz,
      Lp.coeFn_sub (E z) (EndpointProjection.project (m := m) (E z))] with ω hb he
    simpa only [he, Pi.sub_apply] using hb
  have hfactor := fun z hz => @sub_project_force_factor Ω m₀ μ _ m (E z) (E 0) (H z) z (hf z hz)
  have hq := @ae_norm_holomorphic_quotient_le Ω m₀ μ _ _ _ ε hε hdiff hb hfactor ζ hζ hζne
  filter_upwards [hq,
    Lp.coeFn_sub (H ζ) (EndpointProjection.project (m := m) (H ζ))] with ω hq he
  simpa only [he, Pi.sub_apply] using hq

/-- V1 supplies an AE estimate for one fixed local projection throughout its
actual time range. No short-time locality premise is used. -/
theorem positive_time_ae_projection (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ A c : ℝ, ∃ N : ℕ, 1 ≤ A ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, A * Real.sqrt (t : ℝ) ≤ ρ →
    ∀ᵐ ω ∂reducedLaw Q,
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ})
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) ω‖ ≤
      4 * A * (2 + (t : ℝ)) ^ N *
        Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
  obtain ⟨A, c, N, hA, hc, hloc⟩ := hlocal d hd D
  refine ⟨A, c, N, hA, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht ρ hρ
  obtain ⟨G, _, hl, _⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨U, _, hU, _, hu, hc, _⟩ := hl t ht ρ hρ
  let ε := A * (2 + (t : ℝ)) ^ N *
    Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hu' : ∀ᵐ ω ∂reducedLaw Q,
      ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω - U ω‖ ≤ ε := by
    filter_upwards [hu] with ω h
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans h
  have hc' : ∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) ω -
        centeredComplexLp Q U ω‖ ≤ 2 * ε := by
    filter_upwards [hc] with ω h
    exact h.trans (le_of_eq (by dsimp only [ε]; ring))
  have hi : ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t ω - V ω‖ ≤ 2 * ε := by
    rcases ν with i | b
    · exact ⟨centeredComplexLp Q U, isComplexLocal_centered Q hU, hc'⟩
    · cases b
      · refine ⟨centeredComplexLp Q U, isComplexLocal_centered Q hU, ?_⟩
        filter_upwards [hc', smul_centered_ae_eq Q ζ (P t μ)] with ω h he
        exact he ▸ h
      · exact ⟨U, hU, hu'.mono fun ω h => h.trans (by linarith)⟩
  obtain ⟨V, hV, hv⟩ := hi
  have hp := ae_norm_sub_project_of_local_approximation Q ρ
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) V Filter.EventuallyEq.rfl hV hv
  exact hp.mono fun ω h => h.trans (le_of_eq (by dsimp only [ε]; ring))

/-- Extract one analytic L2 family from the exact endpoints premise. This
retains the canonical family and its centered quotient without extra inputs. -/
theorem exists_l2_force_family
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ν : EndpointIndex d) (t : ℝ≥0) :
    let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
    let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
    ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
      DifferentiableOn ℂ E (Metric.ball 0 3) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z ∧
        (∫ ω, H z ω ∂reducedLaw Q) = 0) := by
  dsimp only
  let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
  let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
  have hcast (q : ℝ≥0∞) [Fact (1 ≤ q)] (hq : q = 2)
      (h : ∃ E H : ℂ → Lp ℂ q (reducedLaw Q),
        (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
        DifferentiableOn ℂ E (Metric.ball 0 3) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z ∧
          (∫ ω, H z ω ∂reducedLaw Q) = 0)) :
      ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
        (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
        DifferentiableOn ℂ E (Metric.ball 0 3) ∧
        (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z ∧
          (∫ ω, H z ω ∂reducedLaw Q) = 0) := by
    subst q
    exact h
  letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  apply hcast (ENNReal.ofReal (2 : ℝ)) (by norm_num)
  obtain ⟨_, _, _, _, hpkt⟩ := hends d hd D 2 (by norm_num) t 3 t.coe_nonneg (by norm_num)
  obtain ⟨E, H, he, hE, _, _, hf, _⟩ := hpkt Q hQ β a μ hβ ha hμ F Fdag
    (fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ z)
    (fun z => isComplexTransposeSemigroup_complexL2Transpose Q (F z)) ν t le_rfl
  have hdisc : Metric.ball (0 : ℂ) 3 ⊆ {z : ℂ | ‖z‖ < 3 + 1} := by
    intro z hz
    have hz' : ‖z‖ < 3 := by simpa using hz
    change ‖z‖ < 3 + 1
    linarith
  refine ⟨E, H, he, hE.mono hdisc, ?_⟩
  intro z hz
  exact ⟨(hf z (by simpa using hz)).1, (hf z (by simpa using hz)).2.1⟩

/-- On V1's actual time range, an analytic representative family has a
pointwise AE localized force quotient. The constants precede the law. -/
theorem positive_time_ae_local_quotient_error
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ A c : ℝ, ∃ N : ℕ, 1 ≤ A ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ν : EndpointIndex d) (t : ℝ≥0),
    1 ≤ (t : ℝ) → ∀ ρ : ℝ, A * Real.sqrt (t : ℝ) ≤ ρ →
    let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
    let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
    ∀ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) →
      DifferentiableOn ℂ E (Metric.ball 0 3) →
      (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z) →
    ∀ ζ : ℂ, ‖ζ‖ ≤ 2 → ζ ≠ 0 →
      ∀ᵐ ω ∂reducedLaw Q,
        ‖H ζ ω - EndpointProjection.project
          (m := localSigma {x : Vec d | euclideanNorm x < ρ}) (H ζ) ω‖ ≤
        16 * A * (2 + (t : ℝ)) ^ N *
          Real.exp (A * 16 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
  obtain ⟨A, c, N, hA, hc, hp⟩ := positive_time_ae_projection hlocal d hd D
  refine ⟨A, c, N, hA, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ν t ht ρ hρ
  dsimp only
  intro E H he hE hf ζ hζ hζne
  let ε := 4 * A * (2 + (t : ℝ)) ^ N *
    Real.exp (A * 16 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have herr : ∀ z ∈ Metric.ball (0 : ℂ) 3, ∀ᵐ ω ∂reducedLaw Q,
      ‖E z ω - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ}) (E z) ω‖ ≤ ε := by
    intro z hz
    have heq : E z = indexedEndpoint hd Q ν z
        (forcedComplexEvolution Q ⟨0, by omega⟩ z)
        (fun s => complexL2Transpose (reducedLaw Q)
          (forcedComplexEvolution Q ⟨0, by omega⟩ z s)) β a μ t := Lp.ext (he z)
    rw [heq]
    have hb := hp Q hQ β a μ hβ ha hμ z _ _
      (isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ z)
      (isComplexTransposeSemigroup_complexL2Transpose Q _) ν t ht ρ hρ
    have hz' : ‖z‖ < 3 := by simpa using hz
    have hzsq : ‖z‖ ^ 2 ≤ 16 := by nlinarith [norm_nonneg z]
    have hexp : A * ‖z‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ) ≤
        A * 16 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ) := by
      exact sub_le_sub_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hzsq (by linarith)) t.coe_nonneg) _
    exact hb.mono fun ω h => h.trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity))
  have hq := ae_norm_quotient_sub_project_le
    (μ := reducedLaw Q) hε hE herr hf hζ hζne
  exact hq.mono fun ω h => h.trans (le_of_eq (by dsimp only [ε]; ring))

/-- A bounded centered class has a bounded centered local representative of
its fixed projection, with the original AE approximation error. -/
theorem exists_bounded_centered_local_projection {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ρ : ℝ) (H : Lp ℂ 2 (reducedLaw Q))
    {B ε : ℝ} (hB : ∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ B)
    (hmean : (∫ ω, H ω ∂reducedLaw Q) = 0)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖H ω - EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) H ω‖ ≤ ε) :
    ∃ K : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ K ∧
      (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖H ω - K ω‖ ≤ ε) := by
  obtain ⟨K, hK, hlocal⟩ := EndpointProjection.exists_local_l2 Q ρ (by norm_num) H
  have hp := ae_norm_project_le
    (m := localSigma {x : Vec d | euclideanNorm x < ρ}) H hB
  refine ⟨K, hlocal, ?_, ?_, ?_⟩
  · calc
      (∫ ω, K ω ∂reducedLaw Q) = ∫ ω, EndpointProjection.project
          (m := localSigma {x : Vec d | euclideanNorm x < ρ}) H ω ∂reducedLaw Q :=
        integral_congr_ae hK.symm
      _ = 0 := (EndpointProjection.integral_project
        (Probability.localSigma_le_borel _) H).trans hmean
  · filter_upwards [hK, hp] with ω he hb
    exact he ▸ hb
  · filter_upwards [hK, herr] with ω he hb
    exact he ▸ hb

/-- The exact two dependencies give a uniformly bounded force quotient and
bounded centered local approximants for every time in V1's locality range. -/
theorem exists_positive_time_local_force_family
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C A c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 1 ≤ A ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ν : EndpointIndex d) (t : ℝ≥0),
    1 ≤ (t : ℝ) → (t : ℝ) ≤ T →
    let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
    let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
    ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z ∧
        (∫ ω, H z ω ∂reducedLaw Q) = 0) ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ 2 → ζ ≠ 0 →
        (∀ᵐ ω ∂reducedLaw Q, ‖H ζ ω‖ ≤ C) ∧
        ∀ ρ : ℝ, A * Real.sqrt (t : ℝ) ≤ ρ →
        ∃ K : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ K ∧
          (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
          (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ C) ∧
          (∀ᵐ ω ∂reducedLaw Q, ‖H ζ ω - K ω‖ ≤
            16 * A * (2 + (t : ℝ)) ^ N *
              Real.exp (A * 16 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) := by
  obtain ⟨B, hB, hb⟩ := ae_point_bound_on_four hlocal d hd D T hT
  obtain ⟨A, c, N, hA, hc, hp⟩ := positive_time_ae_local_quotient_error hlocal d hd D
  refine ⟨4 * B, A, c, N, by linarith, hA, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ν t ht htT
  dsimp only
  let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
  let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
  obtain ⟨E, H, he, hE, hf⟩ := exists_l2_force_family hends d hd D Q hQ β a μ hβ ha hμ ν t
  have hbound : ∀ z ∈ Metric.ball (0 : ℂ) 3, ∀ᵐ ω ∂reducedLaw Q, ‖E z ω‖ ≤ B := by
    intro z hz
    have hz4 : ‖z‖ ≤ 4 := by
      have hz' : ‖z‖ < 3 := by simpa using hz
      linarith
    filter_upwards [he z, hb Q hQ β a μ hβ ha hμ z (F z) (Fdag z)
      (isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ z)
      (isComplexTransposeSemigroup_complexL2Transpose Q _) ν hz4 t htT] with ω heω hbω
    exact heω ▸ hbω
  have hfactor := fun z hz => (hf z hz).1
  refine ⟨E, H, he, hf, ?_⟩
  intro ζ hζ hζne
  have hζ3 : ζ ∈ Metric.ball (0 : ℂ) 3 := by
    simpa using (lt_of_le_of_lt hζ (by norm_num : (2 : ℝ) < 3))
  have hquot := ae_norm_holomorphic_quotient_le (by linarith : 0 ≤ B)
    hE hbound hfactor hζ hζne
  refine ⟨hquot, ?_⟩
  intro ρ hρ
  exact exists_bounded_centered_local_projection Q ρ (H ζ) hquot (hf ζ hζ3).2
    (hp Q hQ β a μ hβ ha hμ ν t ht ρ hρ E H he hE hfactor ζ hζ hζne)

/-- The local Gaussian estimate is linear in the field bound and number of
colors. This dependence permits summation over growing locality radii. -/
theorem exists_homogenized_local_average_bound_linear (d : ℕ) (Λ p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → ∀ {r R : ℝ}, HasFiniteRange r P → r < R →
      ∀ (N : ℕ) (col : (Fin d → ℤ) → Fin N) (U : Set (Vec d))
        (W : (Fin d → ℤ) → Set (Vec d)),
      (∀ z, MeasurableSet (W z)) →
      (∀ z, ∀ x ∈ heatCube 1 z, ∀ y ∈ U, x + y ∈ W z) →
      (∀ z w, z ≠ w → col z = col w →
        ∀ x ∈ W z, ∀ y ∈ W w, R ≤ euclideanNorm (x - y)) →
      ∀ B : ℝ, 0 ≤ B → ∀ f : FieldPair d → ℂ, Measurable[localSigma U] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * (N : ℝ) * B * s ^ (-(d : ℝ) / 4)) := by
  let K : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)
  let H : ℝ := Probability.hoeffdingMomentConst p ^ (1 / p)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := by dsimp only [H, Probability.hoeffdingMomentConst]; positivity
  refine ⟨2 * H * K ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro r₀ Q P _ hP r R hfr hR N col U W hW hUW hsep B hB f hf hfB hmean s hs
  have hmass := summable_sq_homogenizedDensity_cubeMass Q one_pos hs
  have hsum : (∑' z, (B * kernelCubeMass 1
      (anisotropicGaussian (homogenizedCoefficient Q) s) z) ^ 2) ≤
      (B ^ 2 * K) * s ^ (-(d : ℝ) / 2) := by
    simp only [mul_pow]
    rw [tsum_mul_left]
    have hh := mul_le_mul_of_nonneg_left hmass.2 (sq_nonneg B)
    simpa only [K, one_pow, mul_one, mul_assoc] using hh
  have hroot := Real.rpow_le_rpow
    (tsum_nonneg fun z => sq_nonneg (B * kernelCubeMass 1
      (anisotropicGaussian (homogenizedCoefficient Q) s) z)) hsum
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hscale : ((B ^ 2 * K) * s ^ (-(d : ℝ) / 2)) ^ (1 / 2 : ℝ) =
      B * K ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
    rw [Real.mul_rpow (mul_nonneg (sq_nonneg B) hK) (Real.rpow_nonneg hs.le _),
      Real.mul_rpow (sq_nonneg B) hK, ← Real.sqrt_eq_rpow, Real.sqrt_sq hB,
      ← Real.rpow_mul hs.le]
    congr 2
    ring
  rw [hscale] at hroot
  have hb := eLpNorm_kernelAverage_le hP hfr hR one_pos col U W hW hUW hsep
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs)
    (contDiff_anisotropicGaussian _ _).continuous.measurable
    (kernelCubeMass_le_of_bound one_pos (norm_homogenizedDensity_le Q hs)) hf hfB hmean p hp
  refine ⟨hb.1, hb.2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  calc
    _ ≤ 2 * (((N : ℝ) * H) *
        (B * K ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hroot (mul_nonneg (Nat.cast_nonneg N) hH)) (by norm_num)
    _ = _ := by ring

/-- Explicit color dependence for ball observations, with a constant uniform
in the radius and bound. The number of colors is the actual residue count. -/
theorem exists_homogenized_ball_average_bound_linear (d : ℕ) (Λ r p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ (ρ : ℝ) (N : ℕ) [NeZero N],
      r < (N : ℝ) - 1 - 2 * ρ → ∀ B : ℝ, 0 ≤ B →
      ∀ f : FieldPair d → ℂ,
      Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] f →
      (∀ ω, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * (N : ℝ) ^ d * B * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_homogenized_local_average_bound_linear d Λ p hp
  refine ⟨C, hC, ?_⟩
  intro r₀ Q P _ hP hfr ρ N _ hgap B hB f hf hfB hmean s hs
  let e := Fintype.equivFin (Fin d → ZMod N)
  have h := hb Q P hP hfr hgap (Fintype.card (Fin d → ZMod N))
    (fun z => e (heatCubeColour N z)) {y : Vec d | euclideanNorm y < ρ}
    (clockNbhd ρ) (measurableSet_kernelNbhd ρ)
    (fun z x hx y hy => Set.mem_iUnion₂.mpr ⟨x, hx, by simpa using hy⟩)
    (fun z w hzw hcol x hx y hy => kernelNbhd_separated ρ N hzw (e.injective hcol) hx hy)
    B hB f hf hfB hmean s hs
  simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] using h

/-- An AE bounded locally measurable complex class has a pointwise bounded
local version. Clipping real and imaginary parts costs only a factor two. -/
theorem exists_bounded_local_version {Ω : Type*} {m₀ m : MeasurableSpace Ω}
    {P : @Measure Ω m₀} {f : Ω → ℂ} {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∃ g : Ω → ℂ, Measurable[m] g ∧ g =ᵐ[P] f)
    (hfB : ∀ᵐ ω ∂P, ‖f ω‖ ≤ B) :
    ∃ k : Ω → ℂ, Measurable[m] k ∧ (∀ ω, ‖k ω‖ ≤ 2 * B) ∧ k =ᵐ[P] f := by
  obtain ⟨g, hg, hgf⟩ := hlocal
  let clip : ℝ → ℝ := fun x => max (-B) (min B x)
  have hc (x : ℝ) : |clip x| ≤ B := by
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hfix (x : ℝ) (hx : |x| ≤ B) : clip x = x := by
    dsimp only [clip]
    rw [min_eq_right (abs_le.mp hx).2, max_eq_right (abs_le.mp hx).1]
  let k : Ω → ℂ := fun ω => (clip (g ω).re : ℂ) + Complex.I * (clip (g ω).im : ℂ)
  have hkr : Measurable[m] (fun ω => clip (g ω).re) :=
    measurable_const.max (measurable_const.min (Complex.continuous_re.measurable.comp hg))
  have hki : Measurable[m] (fun ω => clip (g ω).im) :=
    measurable_const.max (measurable_const.min (Complex.continuous_im.measurable.comp hg))
  refine ⟨k, (Complex.measurable_ofReal.comp hkr).add
    (measurable_const.mul (Complex.measurable_ofReal.comp hki)), ?_, ?_⟩
  · intro ω
    calc
      ‖k ω‖ ≤ ‖(clip (g ω).re : ℂ)‖ + ‖Complex.I * (clip (g ω).im : ℂ)‖ :=
        norm_add_le _ _
      _ = |clip (g ω).re| + |clip (g ω).im| := by
        simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 2 * B := by linarith [hc (g ω).re, hc (g ω).im]
  · filter_upwards [hgf, hfB] with ω he hb
    dsimp only [k]
    rw [he, hfix _ ((Complex.abs_re_le_norm _).trans hb),
      hfix _ ((Complex.abs_im_le_norm _).trans hb)]
    simpa only [mul_comm Complex.I] using Complex.re_add_im (f ω)

/-- Uniform linear color and bound dependence for actual local AE classes. -/
theorem exists_homogenized_ball_ae_average_bound_linear (d : ℕ) (Λ r p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r P → ∀ (ρ : ℝ) (N : ℕ) [NeZero N],
      r < (N : ℝ) - 1 - 2 * ρ → ∀ B : ℝ, 0 ≤ B → ∀ f : FieldPair d → ℂ,
      (∃ g : FieldPair d → ℂ,
        Measurable[localSigma {y : Vec d | euclideanNorm y < ρ}] g ∧ g =ᵐ[P] f) →
      (∀ᵐ ω ∂P, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂P) = 0 → ∀ s : ℝ, 0 < s →
      MemLp (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ∧
      eLpNorm (fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω)) (ENNReal.ofReal p) P ≤
        ENNReal.ofReal (C * (N : ℝ) ^ d * B * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hb⟩ := exists_homogenized_ball_average_bound_linear d Λ r p hp
  refine ⟨2 * C, by positivity, ?_⟩
  intro r₀ Q P _ hP hfr ρ N _ hgap B hB f hlocal hfB hmean s hs
  obtain ⟨k, hk, hkB, hkf⟩ := exists_bounded_local_version hB hlocal hfB
  have hkm : ∫ ω, k ω ∂P = 0 := (integral_congr_ae hkf).trans hmean
  have hbound := hb Q P hP hfr ρ N hgap (2 * B) (by positivity) k hk hkB hkm s hs
  have he := kernel_average_congr_ae P hP hkf
    (anisotropicGaussian (homogenizedCoefficient Q) s)
  refine ⟨hbound.1.ae_eq he, ?_⟩
  rw [← eLpNorm_congr_ae he]
  convert hbound.2 using 1 <;> congr 1 <;> ring

/-- Summable finite-p bounds pass through an actual L2 series. Continuous
inclusion identifies the higher-Lp sum with the original L2 class. -/
theorem memLp_of_hasSum_of_summable_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : 2 ≤ p) (f : ℕ → Lp ℂ 2 P) (F : Lp ℂ 2 P) (hF : HasSum f F)
    (hf : ∀ n, MemLp (f n : Ω → ℂ) p P) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n, (eLpNorm (f n : Ω → ℂ) p P).toReal ≤ b n) :
    MemLp (F : Ω → ℂ) p P ∧ (eLpNorm (F : Ω → ℂ) p P).toReal ≤ ∑' n, b n := by
  let g : ℕ → Lp ℂ p P := fun n => (hf n).toLp (f n)
  have hg : ∀ n, ‖g n‖ ≤ b n := by
    intro n
    simpa only [g, Lp.norm_toLp] using hbound n
  have hgnorm : Summable (fun n => ‖g n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hg hb
  have hgs : Summable g := hgnorm.of_norm
  have hi : ∀ n, complexLpToL2 P hp (g n) = f n := by
    intro n
    apply Lp.ext
    exact (hf n).coeFn_toLp
  have hsum : HasSum (fun n => complexLpToL2 P hp (g n))
      (complexLpToL2 P hp (∑' n, g n)) :=
    (complexLpToL2CLM P hp).hasSum hgs.hasSum
  simp only [hi] at hsum
  have heq := hsum.unique hF
  have hae : ((∑' n, g n : Lp ℂ p P) : Ω → ℂ) =ᵐ[P] F := by
    change (complexLpToL2 P hp (∑' n, g n) : Ω → ℂ) =ᵐ[P] F
    rw [heq]
  refine ⟨(Lp.memLp (∑' n, g n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  exact (norm_tsum_le_tsum_norm hgnorm).trans (Summable.tsum_le_tsum hg hgnorm hb)

/-- Averaging commutes with an actual L2 series; summable higher-moment
bounds on its pieces therefore control the average of the original class. -/
theorem gaussian_average_series_bound {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    [Fact (1 ≤ ENNReal.ofReal p)] (s : ℝ) (hs : 0 < s)
    (f : ℕ → Lp ℂ 2 (reducedLaw Q)) (F : Lp ℂ 2 (reducedLaw Q))
    (hF : HasSum f F)
    (hf : ∀ n, MemLp (gaussianAverage hd Q s hs (f n) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q))
    (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n, (eLpNorm (gaussianAverage hd Q s hs (f n) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ b n) :
    MemLp (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ ∑' n, b n := by
  have hsum : HasSum (fun n => gaussianAverage hd Q s hs (f n))
      (gaussianAverage hd Q s hs F) :=
    (homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0).hasSum hF
  exact memLp_of_hasSum_of_summable_bound (reducedLaw Q) (two_le_exponent hp)
    _ _ hsum hf b hb hbound

/-- Polynomial color growth is summable against the squared-radius
localization error. This is uniform in the later Gaussian averaging scale. -/
theorem summable_nat_pow_mul_exp_neg_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-b * (n : ℝ) ^ 2)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _
    (Real.summable_pow_mul_exp_neg_nat_mul k hb)
  intro n
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hsq (by linarith))) (pow_nonneg (Nat.cast_nonneg n) k)

/-- The stationary L2 kernel integral has the literal translated integral as
its representative. The equality retains its almost-everywhere qualifier. -/
theorem coeFn_kernel_average_measure {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (μ : Measure (Vec d)) [SFinite μ]
    (k : Vec d → ℂ) (hk : Continuous k) (hki : Integrable k μ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x, k x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f ∂μ :
      Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∫ x, k x * f (translate x ω) ∂μ := by
  let P := reducedLaw Q
  let g : Vec d × FieldPair d → ℂ := fun q => k q.1 * f (translate q.1 q.2)
  have hm : Measurable g := (hk.measurable.comp measurable_fst).mul
    ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable)
  have hf : Integrable (f : FieldPair d → ℂ) P :=
    (Lp.memLp f).integrable (by norm_num)
  have hg : Integrable g (μ.prod P) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ fun x =>
      ((measurePreserving_translate P (reducedLaw_stationary Q) x).integrable_comp
        (Lp.stronglyMeasurable f).aestronglyMeasurable |>.mpr hf).const_mul (k x), ?_⟩
    have hn (x : Vec d) : (∫ ω, ‖g (x, ω)‖ ∂P) = ‖k x‖ * ∫ ω, ‖f ω‖ ∂P := by
      simp only [g, norm_mul]
      rw [integral_const_mul]
      congr 1
      exact Probability.integral_translate P (reducedLaw_stationary Q) x
        (fun ω => ‖f ω‖) (Lp.stronglyMeasurable f).measurable.norm
    exact (hki.norm.mul_const (∫ ω, ‖f ω‖ ∂P)).congr
      (ae_of_all _ fun x => (hn x).symm)
  let v : Vec d → Lp ℂ 2 P := fun x =>
    k x • complexTranslation P (reducedLaw_stationary Q) x f
  have hv : Integrable v μ := by
    have ht : Continuous (fun x : Vec d =>
        complexTranslation P (reducedLaw_stationary Q) x f) :=
      (continuous_complexTranslation P (reducedLaw_stationary Q)).comp
        (continuous_id.prodMk continuous_const)
    apply (hki.norm.mul_const ‖f‖).mono' (hk.fun_smul ht).aestronglyMeasurable
    exact ae_of_all _ fun x => by rw [norm_smul, norm_complexTranslation]
  have he (x : Vec d) : (v x : FieldPair d → ℂ) =ᵐ[P] fun ω => g (x, ω) := by
    filter_upwards [Lp.coeFn_smul (k x)
      (complexTranslation P (reducedLaw_stationary Q) x f),
      coeFn_complexTranslation P (reducedLaw_stationary Q) x f] with ω hsm ht
    exact hsm.trans (congrArg (fun z => k x * z) ht)
  let V : Lp ℂ 2 P := ∫ x, v x ∂μ
  apply Integrable.ae_eq_of_forall_setIntegral_eq (V : FieldPair d → ℂ)
    (fun ω => ∫ x, g (x, ω) ∂μ) ((Lp.memLp V).integrable (by norm_num)) hg.integral_prod_right
  intro U hU _
  let W : Lp ℂ 2 P := indicatorConstLp 2 hU (measure_ne_top P U) (1 : ℂ)
  have hgU : Integrable g (μ.prod (P.restrict U)) :=
    hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in U, V ω ∂P) = inner ℂ W V :=
      (L2.inner_indicatorConstLp_one hU (measure_ne_top P U) V).symm
    _ = ∫ x, inner ℂ W (v x) ∂μ := ((innerSL ℂ W).integral_comp_comm hv).symm
    _ = ∫ x, ∫ ω in U, g (x, ω) ∂P ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun x =>
        (L2.inner_indicatorConstLp_one hU (measure_ne_top P U) (v x)).trans
          (integral_congr_ae (ae_restrict_of_ae (he x)))
    _ = ∫ ω in U, (∫ x, g (x, ω) ∂μ) ∂P := integral_integral_swap hgU

/-- The volume specialization of the literal representative formula. -/
theorem coeFn_kernel_average {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (k : Vec d → ℂ) (hk : Continuous k) (hki : Integrable k)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x, k x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f :
      Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∫ x, k x * f (translate x ω) :=
  coeFn_kernel_average_measure Q volume k hk hki f

/-- The local moment estimate applies to the actual L2 Gaussian integral,
with the same explicit radius, residue count, and field-bound dependence. -/
theorem exists_gaussian_average_local_bound_linear (d : ℕ) (Λ r p : ℝ)
    (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) → ∀ (ρ : ℝ) (N : ℕ) [NeZero N],
      r < (N : ℝ) - 1 - 2 * ρ → ∀ B : ℝ, 0 ≤ B →
      ∀ f : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ f →
      (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂reducedLaw Q) = 0 →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (N : ℝ) ^ d * B * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_homogenized_ball_ae_average_bound_linear d Λ r p hp
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr ρ N _ hgap B hB f hlocal hfB hmean s hs
  have h := hb Q (reducedLaw Q) (reducedLaw_stationary Q) hfr ρ N hgap B hB
    f hlocal hfB hmean s hs
  have he := coeFn_kernel_average Q (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
    (by unfold homogenizedGaussianKernel; fun_prop)
    (integrable_homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) f
  have he' : (gaussianAverage hd Q s hs f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∫ x, anisotropicGaussian (homogenizedCoefficient Q) s x •
        f (translate x ω) := by
    refine he.trans (ae_of_all _ fun ω => ?_)
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [homogenizedGaussianKernel_zero_eq_ofReal]
      exact Complex.real_smul.symm
  refine ⟨h.1.ae_eq he'.symm, ?_⟩
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top h.2
  rw [ENNReal.toReal_ofReal (by positivity)] at hn
  rw [eLpNorm_congr_ae he']
  exact hn

/-- Summable approximation errors make the consecutive local differences an
actual telescoping series in the original normed space. -/
theorem hasSum_localization_differences {E : Type*} [NormedAddCommGroup E]
    (K : ℕ → E) (F : E) (a : ℕ → ℝ) (ha : Summable a)
    (herr : ∀ n, ‖F - K n‖ ≤ a n) :
    HasSum (fun n => K (n + 1) - K n) (F - K 0) := by
  have hstep (n : ℕ) : ‖K (n + 1) - K n‖ ≤ a (n + 1) + a n := by
    calc
      _ ≤ ‖K (n + 1) - F‖ + ‖F - K n‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add (by simpa only [norm_sub_rev] using herr (n + 1)) (herr n)
  have hnorm : Summable (fun n => ‖K (n + 1) - K n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hstep
      ((ha.comp_injective Nat.succ_injective).add ha)
  have hK : Filter.Tendsto K Filter.atTop (nhds F) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by
      simpa only [norm_sub_rev] using herr n) ha.tendsto_atTop_zero
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr
  simpa only [Finset.sum_range_sub] using hK.sub_const (K 0)

/-- Summing the finite-range bounds of genuinely local pieces preserves the
full Gaussian and its spatial decay. The weighted color sum is independent of s. -/
theorem exists_gaussian_average_local_series_bound (d : ℕ) (Λ r p : ℝ)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (f : ℕ → Lp ℂ 2 (reducedLaw Q)) (F : Lp ℂ 2 (reducedLaw Q)),
      HasSum f F → ∀ (ρ : ℕ → ℝ) (N : ℕ → ℕ) [∀ n, NeZero (N n)],
      (∀ n, r < (N n : ℝ) - 1 - 2 * ρ n) →
      ∀ (B : ℕ → ℝ), (∀ n, 0 ≤ B n) →
      (∀ n, IsComplexLocalObservation Q (ρ n) (f n)) →
      (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖f n ω‖ ≤ B n) →
      (∀ n, (∫ ω, f n ω ∂reducedLaw Q) = 0) →
      Summable (fun n => (N n : ℝ) ^ d * B n) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (∑' n, (N n : ℝ) ^ d * B n) * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_average_local_bound_linear d Λ r p (by linarith)
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr f F hF ρ N _ hgap B hB hlocal hfB hmean hw s hs
  have hpiece (n : ℕ) := hb hd Q hfr (ρ n) (N n) (hgap n) (B n) (hB n)
    (f n) (hlocal n) (hfB n) (hmean n) s hs
  have hsum : Summable (fun n => C * ((N n : ℝ) ^ d * B n) *
      s ^ (-(d : ℝ) / 4)) := (hw.mul_left C).mul_right _
  have h := gaussian_average_series_bound hd Q p hp s hs f F hF
    (fun n => (hpiece n).1) _ hsum (fun n => by
      simpa only [mul_assoc] using (hpiece n).2)
  refine ⟨h.1, ?_⟩
  simpa only [tsum_mul_right, tsum_mul_left] using h.2

/-- A bounded centered class with summably accurate local approximants obeys
the full Gaussian estimate obtained by summing its actual telescoping blocks. -/
theorem exists_gaussian_average_multiscale_bound (d : ℕ) (Λ r p : ℝ)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q))
        (ρ : ℕ → ℝ) (N : ℕ → ℕ) [∀ n, NeZero (N n)],
      Monotone ρ → (∀ n, r < (N n : ℝ) - 1 - 2 * ρ n) →
      ∀ B : ℝ, 0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖K 0 ω‖ ≤ B) →
      (∀ n, IsComplexLocalObservation Q (ρ n) (K n)) →
      (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
      ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → Summable a →
      (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖H ω - K n ω‖ ≤ a n) →
      Summable (fun n => (N (n + 1) : ℝ) ^ d * (a n + a (n + 1))) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * ((N 0 : ℝ) ^ d * B +
            ∑' n, (N (n + 1) : ℝ) ^ d * (a n + a (n + 1))) *
              s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_average_local_series_bound d Λ r p hp
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr H K ρ N _ hρ hgap B hB hK0 hlocal hmean a ha hsum herr hw s hs
  let f : ℕ → Lp ℂ 2 (reducedLaw Q)
    | 0 => K 0
    | n + 1 => K (n + 1) - K n
  let b : ℕ → ℝ
    | 0 => B
    | n + 1 => a n + a (n + 1)
  have hlocal' (n : ℕ) : IsComplexLocalObservation Q (ρ n) (f n) := by
    cases n with
    | zero => exact hlocal 0
    | succ n =>
      obtain ⟨g₁, hg₁, he₁⟩ := hlocal (n + 1)
      obtain ⟨g₀, hg₀, he₀⟩ := hlocal n
      have hg₀' := hg₀.mono (Probability.localSigma_mono
        (fun x hx => hx.trans_le (hρ (Nat.le_succ n)))) le_rfl
      exact ⟨fun ω => g₁ ω - g₀ ω, hg₁.sub hg₀',
        (he₁.sub he₀).trans (Lp.coeFn_sub _ _).symm⟩
  have hbound (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q, ‖f n ω‖ ≤ b n := by
    cases n with
    | zero => exact hK0
    | succ n =>
      filter_upwards [herr n, herr (n + 1), Lp.coeFn_sub (K (n + 1)) (K n)]
        with ω hn hn₁ he
      change ‖(K (n + 1) - K n) ω‖ ≤ a n + a (n + 1)
      rw [he]
      have hh := norm_sub_le_norm_sub_add_norm_sub (K (n + 1) ω) (H ω) (K n ω)
      rw [norm_sub_rev (K (n + 1) ω) (H ω)] at hh
      exact hh.trans (add_le_add hn₁ hn |>.trans (le_of_eq (add_comm _ _)))
  have hmean' (n : ℕ) : (∫ ω, f n ω ∂reducedLaw Q) = 0 := by
    cases n with
    | zero => exact hmean 0
    | succ n =>
      rw [show f (n + 1) = K (n + 1) - K n from rfl,
        integral_congr_ae (Lp.coeFn_sub _ _)]
      change (∫ ω, K (n + 1) ω - K n ω ∂reducedLaw Q) = 0
      rw [integral_sub ((Lp.memLp (K (n + 1))).integrable (by norm_num))
        ((Lp.memLp (K n)).integrable (by norm_num)), hmean, hmean, sub_self]
  have herr' (n : ℕ) : ‖H - K n‖ ≤ a n := by
    rw [Lp.norm_def]
    apply AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp _).aestronglyMeasurable (ha n)
    filter_upwards [herr n, Lp.coeFn_sub H (K n)] with ω h he
    rw [he]
    exact h
  have hF : HasSum f H := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa only [f, Finset.sum_range_one] using
      hasSum_localization_differences K H a hsum herr'
  have hw' : Summable (fun n => (N n : ℝ) ^ d * b n) := by
    apply (summable_nat_add_iff 1).mp
    exact hw
  have h := hb hd Q hfr f H hF ρ N hgap b (fun n => by
      cases n with
      | zero => exact hB
      | succ n => exact add_nonneg (ha n) (ha (n + 1)))
    hlocal' hbound hmean' hw' s hs
  have hweight : (∑' n, (N n : ℝ) ^ d * b n) =
      (N 0 : ℝ) ^ d * B + ∑' n, (N (n + 1) : ℝ) ^ d * (a n + a (n + 1)) := by
    simpa only [Finset.sum_range_one, b] using (hw'.sum_add_tsum_nat_add 1).symm
  exact ⟨h.1, by simpa only [hweight] using h.2⟩

/-- The two-step shift in the residue-color polynomial is harmless for the
squared-radius Gaussian localization error. -/
theorem summable_nat_add_two_pow_mul_exp_neg_sq (k : ℕ) {b : ℝ} (hb : 0 < b) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) ^ k * Real.exp (-b * (n : ℝ) ^ 2)) := by
  apply ((summable_nat_pow_mul_exp_neg_sq k hb).mul_left ((3 : ℝ) ^ k)).of_norm_bounded_eventually_nat
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ((3 : ℝ) * n) ^ k * Real.exp (-b * (n : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by linarith) k) (Real.exp_pos _).le
    _ = _ := by rw [mul_pow]; ring

/-- The actual linearly growing residue counts have summable weighted
consecutive Gaussian errors, as required by the local telescoping estimate. -/
theorem summable_residue_gaussian_errors (k M : ℕ) {L b : ℝ}
    (hL : 0 ≤ L) (hb : 0 < b) :
    Summable (fun n : ℕ => ((M * (n + 2) : ℕ) : ℝ) ^ k *
      (L * Real.exp (-b * (n : ℝ) ^ 2) +
        L * Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2))) := by
  have hsum := (summable_nat_add_two_pow_mul_exp_neg_sq k hb).mul_left
    (2 * L * (M : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hsq : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-b * (n : ℝ) ^ 2) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hsq (by linarith))
  calc
    _ ≤ ((M * (n + 2) : ℕ) : ℝ) ^ k *
        (2 * L * Real.exp (-b * (n : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [mul_le_mul_of_nonneg_left he hL])
        (pow_nonneg (Nat.cast_nonneg _) k)
    _ = _ := by push_cast; rw [mul_pow]; ring

/-- Radius-by-radius Gaussian approximation errors imply spatial decay for the
actual Gaussian average, with a constant chosen before the environment law. -/
theorem exists_gaussian_average_of_gaussian_local_approximants
    (d : ℕ) (Λ r R B L b p : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : 0 < b) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q)),
      (∀ᵐ ω ∂reducedLaw Q, ‖K 0 ω‖ ≤ B) →
      (∀ n : ℕ, IsComplexLocalObservation Q (R + n) (K n)) →
      (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
      (∀ n, ∀ᵐ ω ∂reducedLaw Q,
        ‖H ω - K n ω‖ ≤ L * Real.exp (-b * (n : ℝ) ^ 2)) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (|r| + 2 * R + 4)
  have hMpos : (0 : ℝ) < M := by linarith [abs_nonneg r]
  have hMne : M ≠ 0 := by exact_mod_cast hMpos.ne'
  have hMtwo : 0 ≤ (M : ℝ) - 2 := by linarith [abs_nonneg r]
  let N : ℕ → ℕ := fun n => M * (n + 1)
  let a : ℕ → ℝ := fun n => L * Real.exp (-b * (n : ℝ) ^ 2)
  let w : ℕ → ℝ := fun n => (N (n + 1) : ℝ) ^ d * (a n + a (n + 1))
  have hw : Summable w := by
    simpa only [w, N, a, Nat.add_assoc] using summable_residue_gaussian_errors d M hL hb
  have hw0 : 0 ≤ ∑' n, w n := tsum_nonneg fun n => by dsimp only [w, a]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_average_multiscale_bound d Λ r p hp
  refine ⟨C * ((M : ℝ) ^ d * B + ∑' n, w n), by positivity, ?_⟩
  intro hd r₀ Q hfr H K hK0 hlocal hmean herr s hs
  letI (n : ℕ) : NeZero (N n) := ⟨Nat.mul_ne_zero hMne (Nat.succ_ne_zero n)⟩
  have hρ : Monotone (fun n : ℕ => R + (n : ℝ)) :=
    fun n m hnm => by dsimp only; linarith [(Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)]
  have hgap (n : ℕ) : r < (N n : ℝ) - 1 - 2 * (R + n) := by
    dsimp only [N]
    push_cast
    nlinarith [mul_nonneg hMtwo (Nat.cast_nonneg (α := ℝ) n), le_abs_self r]
  have ha : Summable a := (summable_nat_pow_mul_exp_neg_sq 0 hb).mul_left L |>.congr
    (fun n => by simp only [pow_zero, one_mul, a])
  have h := hbound hd Q hfr H K (fun n => R + n) N hρ hgap B hB hK0 hlocal hmean
    a (fun n => mul_nonneg hL (Real.exp_pos _).le) ha herr hw s hs
  refine ⟨h.1, ?_⟩
  simpa only [N, Nat.zero_add, Nat.zero_add, Nat.mul_one, w] using h.2

/-- A fixed finite horizon turns V1's radius error into a summable Gaussian
sequence, with constants independent of the time and environment law. -/
theorem positive_time_radius_error_le (A c T t R : ℝ) (N n : ℕ)
    (hA : 0 ≤ A) (hc : 0 < c) (hT : 1 ≤ T) (ht : 1 ≤ t) (htT : t ≤ T)
    (hR : 0 ≤ R) :
    16 * A * (2 + t) ^ N * Real.exp (A * 16 * t - c * (R + n) ^ 2 / t) ≤
      (16 * A * (2 + T) ^ N * Real.exp (A * 16 * T)) *
        Real.exp (-(c / T) * (n : ℝ) ^ 2) := by
  have hT0 : 0 < T := by linarith
  have ht0 : 0 < t := by linarith
  have hbt : (c / T) * t ≤ c := by
    calc
      (c / T) * t ≤ (c / T) * T :=
        mul_le_mul_of_nonneg_left htT (div_nonneg hc.le hT0.le)
      _ = c := div_mul_cancel₀ c hT0.ne'
  have hsq : (n : ℝ) ^ 2 ≤ (R + n) ^ 2 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hdecay : (c / T) * (n : ℝ) ^ 2 ≤ c * (R + n) ^ 2 / t := by
    apply (le_div_iff₀ ht0).mpr
    calc
      (c / T) * (n : ℝ) ^ 2 * t = ((c / T) * t) * (n : ℝ) ^ 2 := by ring
      _ ≤ c * (n : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hbt (sq_nonneg _)
      _ ≤ c * (R + n) ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
  have hexp : Real.exp (A * 16 * t - c * (R + n) ^ 2 / t) ≤
      Real.exp (A * 16 * T - (c / T) * (n : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left htT (show 0 ≤ A * 16 by positivity)
    linarith
  have hpow : (2 + t) ^ N ≤ (2 + T) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith) N
  calc
    _ ≤ (16 * A * (2 + T) ^ N) *
        Real.exp (A * 16 * T - (c / T) * (n : ℝ) ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hexp
        (Real.exp_pos _).le (by positivity)
    _ = _ := by rw [sub_eq_add_neg, Real.exp_add]; ring

/-- In V1's time range the exact two dependencies give the spatial decay of
actual Gaussian averages of the canonical force quotient, uniformly in force. -/
theorem exists_positive_time_gaussian_force_family
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T p : ℝ) (hT : 1 ≤ T)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ν : EndpointIndex d) (t : ℝ≥0),
    1 ≤ (t : ℝ) → (t : ℝ) ≤ T →
    let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
    let Fdag := fun z s => complexL2Transpose (reducedLaw Q) (F z s)
    ∃ E H : ℂ → Lp ℂ 2 (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (F z) (Fdag z) β a μ t) ∧
      (∀ z ∈ Metric.ball (0 : ℂ) 3, E z - E 0 = z • H z ∧
        (∫ ω, H z ω ∂reducedLaw Q) = 0) ∧
      ∀ ζ : ℂ, ‖ζ‖ ≤ 2 → ζ ≠ 0 → ∀ s : ℝ, ∀ hs : 0 < s,
        MemLp (gaussianAverage hd Q s hs (H ζ) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianAverage hd Q s hs (H ζ) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (-(d : ℝ) / 4) := by
  classical
  have hT0 : 0 < T := by linarith
  obtain ⟨B, A, c, N, hB, hA, hc, hf⟩ :=
    exists_positive_time_local_force_family hlocal hends d hd D T hT0.le
  let R := A * Real.sqrt T
  let L := 16 * A * (2 + T) ^ N * Real.exp (A * 16 * T)
  have hR : 0 ≤ R := mul_nonneg (zero_le_one.trans hA) (Real.sqrt_nonneg _)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_average_of_gaussian_local_approximants
    d D.ellipticity D.dependenceRange R B L (c / T) p hR
    (zero_le_one.trans hB) hL (div_pos hc hT0) hp
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ν t ht htT
  obtain ⟨E, H, he, hfactor, hloc⟩ := hf Q hQ β a μ hβ ha hμ ν t ht htT
  refine ⟨E, H, he, hfactor, ?_⟩
  intro ζ hζ hζne s hs
  have hrad (n : ℕ) : A * Real.sqrt (t : ℝ) ≤ R + n := by
    have hh := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htT)
      (zero_le_one.trans hA)
    dsimp only [R]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  choose K hK using fun n : ℕ => (hloc ζ hζ hζne).2 (R + n) (hrad n)
  have herr (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      ‖H ζ ω - K n ω‖ ≤ L * Real.exp (-(c / T) * (n : ℝ) ^ 2) := by
    filter_upwards [(hK n).2.2.2] with ω hω
    exact hω.trans (positive_time_radius_error_le A c T t R N n
      (zero_le_one.trans hA) hc hT ht htT hR)
  exact hbound hd Q (Localization.finiteRange_map_reduce Q.measure Q.finiteRange)
    (H ζ) K (hK 0).2.2.1 (fun n => (hK n).1) (fun n => (hK n).2.1) herr s hs

/-- Independent centered complex L2 classes are orthogonal. -/
theorem inner_eq_zero_of_indepFun {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (f g : Lp ℂ 2 P)
    (hi : ProbabilityTheory.IndepFun (f : Ω → ℂ) (g : Ω → ℂ) P)
    (hf : (∫ ω, f ω ∂P) = 0) : inner ℂ f g = 0 := by
  have h := (hi.comp Complex.continuous_conj.measurable measurable_id).integral_fun_mul_eq_mul_integral
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f))
      (Lp.aestronglyMeasurable g)
  simpa [L2.inner_def, RCLike.inner_apply, mul_comm, integral_conj, hf] using h

/-- Pythagoras for a finite collection of mutually orthogonal vectors. -/
theorem norm_sum_sq_of_orthogonal {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (s : Finset ι) (f : ι → E)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → inner ℂ (f i) (f j) = 0) :
    ‖∑ i ∈ s, f i‖ ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hz : inner ℂ (f a) (∑ i ∈ s, f i) = 0 := by
      rw [inner_sum]
      exact Finset.sum_eq_zero fun i hi => ho a (by simp) i (by simp [hi])
        (by intro h; exact ha (h ▸ hi))
    rw [Finset.sum_insert ha, norm_add_sq (𝕜 := ℂ), hz, map_zero, mul_zero, add_zero,
      ih (fun i hi j hj hij => ho i (by simp [hi]) j (by simp [hj]) hij),
      Finset.sum_insert ha]

/-- A finite residue decomposition bounds an orthogonal sum by its squared
weights. No pointwise bound on the random variables enters this L2 estimate. -/
theorem norm_sum_le_colored_sqrt {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {N : ℕ} (col : ι → Fin N) (f : ι → E)
    (c : ι → ℝ) (s : Finset ι)
    (ho : ∀ i ∈ s, ∀ j ∈ s, col i = col j → i ≠ j → inner ℂ (f i) (f j) = 0)
    (hc : ∀ i ∈ s, ‖f i‖ ≤ c i) :
    ‖∑ i ∈ s, f i‖ ≤ (N : ℝ) * Real.sqrt (∑ i ∈ s, c i ^ 2) := by
  classical
  have hb (k : Fin N) : ‖∑ i ∈ s with col i = k, f i‖ ≤
      Real.sqrt (∑ i ∈ s, c i ^ 2) := by
    apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)).mpr
    rw [norm_sum_sq_of_orthogonal]
    · exact (Finset.sum_le_sum fun i hi => by
        have h := hc i (Finset.mem_filter.mp hi).1
        exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h) |>.mpr h).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => sq_nonneg _))
    · intro i hi j hj hij
      exact ho i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1
        ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm) hij
  calc
    ‖∑ i ∈ s, f i‖ = ‖∑ k : Fin N, ∑ i ∈ s with col i = k, f i‖ := by
      congr 1
      exact (Finset.sum_fiberwise s col f).symm
    _ ≤ ∑ k : Fin N, ‖∑ i ∈ s with col i = k, f i‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin N, Real.sqrt (∑ i ∈ s, c i ^ 2) := Finset.sum_le_sum fun k _ => hb k
    _ = _ := by simp

/-- The same residue estimate passes to an actual Hilbert-space series. -/
theorem norm_hasSum_le_colored_sqrt {ι E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {N : ℕ} (col : ι → Fin N) (f : ι → E)
    (c : ι → ℝ) {F : E} (hf : HasSum f F)
    (ho : ∀ i j, col i = col j → i ≠ j → inner ℂ (f i) (f j) = 0)
    (hc : ∀ i, ‖f i‖ ≤ c i) (hc2 : Summable (fun i => c i ^ 2)) :
    ‖F‖ ≤ (N : ℝ) * Real.sqrt (∑' i, c i ^ 2) := by
  apply le_of_tendsto hf.norm
  exact Filter.Eventually.of_forall fun s =>
    (norm_sum_le_colored_sqrt col f c s (fun i _ j _ => ho i j) (fun i _ => hc i)).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hc2.sum_le_tsum s (fun _ _ => sq_nonneg _)))
        (Nat.cast_nonneg N))

/-- Cube pieces in the actual stationary complex L2 space. -/
noncomputable def kernelCubeAverageLp2 {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (L : ℝ) (k : Vec d → ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) (z : Fin d → ℤ) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x in heatCube L z,
    (k x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f

/-- The cube's L2 norm depends on the L2 size of the input, rather than a
pointwise bound. This is the small amplitude needed for localization errors. -/
theorem norm_kernelCubeAverageLp2_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (L : ℝ) (k : Vec d → ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) (z : Fin d → ℤ) :
    ‖kernelCubeAverageLp2 Q L k f z‖ ≤ ‖f‖ * kernelCubeMass L k z := by
  calc
    _ ≤ ∫ x in heatCube L z,
        ‖(k x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
      norm_integral_le_integral_norm _
    _ = ‖f‖ * kernelCubeMass L k z := by
      simp only [norm_smul, norm_complexTranslation, Complex.norm_real, Real.norm_eq_abs,
        kernelCubeMass, integral_mul_const]
      ring

/-- The literal cube integral is a representative of its actual L2 class. -/
theorem coeFn_kernelCubeAverageLp2 {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (L : ℝ) {k : Vec d → ℝ}
    (hk : Integrable k) (hkc : Continuous k)
    (f : Lp ℂ 2 (reducedLaw Q)) (z : Fin d → ℤ) :
    (kernelCubeAverageLp2 Q L k f z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      kernelCubePiece L k f z := by
  have h := coeFn_kernel_average_measure Q (volume.restrict (heatCube L z))
    (fun x => (k x : ℂ)) (Complex.continuous_ofReal.comp hkc)
    (hk.restrict.ofReal) f
  refine h.trans (ae_of_all _ fun ω => ?_)
  apply integral_congr_ae
  exact ae_of_all _ fun x => Complex.real_smul.symm

/-- The partition into heat cubes is also a sum in the actual L2 space. -/
theorem hasSum_kernelCubeAverageLp2 {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {L : ℝ} (hL : 0 < L) {k : Vec d → ℝ}
    (hk : Integrable k) (hkc : Continuous k) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasSum (kernelCubeAverageLp2 Q L k f)
      (∫ x, (k x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  have hi := integrable_kernel_complexTranslation (reducedLaw Q)
    (reducedLaw_stationary Q) (fun x => (k x : ℂ)) hk.ofReal
    (Complex.continuous_ofReal.comp hkc) f
  have h := hasSum_integral_iUnion (fun z : Fin d → ℤ => measurableSet_heatCube L z)
    (pairwise_disjoint_heatCube hL) hi.integrableOn
  rw [iUnion_heatCube hL, Measure.restrict_univ] at h
  exact h

/-- Joint finite range supplies orthogonality of same-residue L2 classes
from genuine local representatives. The amplitude is an L2 norm bound. -/
theorem norm_local_hasSum_le {d : ℕ} {ι : Type*}
    {P : Measure (FieldPair d)} [IsProbabilityMeasure P] {r R : ℝ}
    (hfr : HasFiniteRange r P) (hR : r < R) {N : ℕ} (col : ι → Fin N)
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i))
    (hsep : ∀ i j, i ≠ j → col i = col j →
      ∀ x ∈ U i, ∀ y ∈ U j, R ≤ euclideanNorm (x - y))
    (F : ι → Lp ℂ 2 P) (X : ι → FieldPair d → ℂ)
    (hlocal : ∀ i, Measurable[localSigma (U i)] (X i))
    (hrep : ∀ i, (F i : FieldPair d → ℂ) =ᵐ[P] X i)
    (hmean : ∀ i, (∫ ω, F i ω ∂P) = 0)
    (c : ι → ℝ) (hc : ∀ i, ‖F i‖ ≤ c i)
    (hc2 : Summable (fun i => c i ^ 2)) {V : Lp ℂ 2 P} (hsum : HasSum F V) :
    ‖V‖ ≤ (N : ℝ) * Real.sqrt (∑' i, c i ^ 2) := by
  classical
  apply norm_hasSum_le_colored_sqrt col F c hsum ?_ hc hc2
  intro i j hcol hij
  have hi := Calculus.S1.iIndepFun_of_local hfr
    (fun i : {i // col i = col j} => U i) (fun i => hU i) hR
    (fun i j hij x hx y hy => hsep i j
      (fun he => hij (Subtype.ext he)) (i.2.trans j.2.symm) x hx y hy)
    (fun i : {i // col i = col j} => X i) (fun i => hlocal i) (fun i => hrep i)
  exact inner_eq_zero_of_indepFun (F i) (F j)
    (hi.indepFun (i := ⟨i, hcol⟩) (j := ⟨j, rfl⟩)
      (fun he => hij (congrArg Subtype.val he))) (hmean i)

/-- An actual stationary kernel integral has an L2 finite-range bound with
L2 amplitude. Boundedness of a local representative is used for its literal
cube measurability and centering, but does not enter the resulting bound. -/
theorem norm_kernel_average_le_of_local_L2 {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {r R L : ℝ}
    (hfr : HasFiniteRange r (reducedLaw Q)) (hR : r < R) (hL : 0 < L)
    {N : ℕ} (col : (Fin d → ℤ) → Fin N) (U : Set (Vec d))
    (W : (Fin d → ℤ) → Set (Vec d)) (hW : ∀ z, MeasurableSet (W z))
    (hUW : ∀ z, ∀ x ∈ heatCube L z, ∀ y ∈ U, x + y ∈ W z)
    (hsep : ∀ z w, z ≠ w → col z = col w →
      ∀ x ∈ W z, ∀ y ∈ W w, R ≤ euclideanNorm (x - y))
    {k : Vec d → ℝ} (hk : Integrable k) (hkc : Continuous k)
    (hsq : Summable (fun z => kernelCubeMass L k z ^ 2))
    (f : Lp ℂ 2 (reducedLaw Q)) (g : FieldPair d → ℂ)
    (hlocal : Measurable[localSigma U] g)
    (hrep : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] g)
    {B : ℝ} (hB : ∀ ω, ‖g ω‖ ≤ B) (hmean : (∫ ω, g ω ∂reducedLaw Q) = 0) :
    ‖∫ x, (k x : ℂ) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ ≤
      (N : ℝ) * Real.sqrt (∑' z, (‖f‖ * kernelCubeMass L k z) ^ 2) := by
  have he (z : Fin d → ℤ) :
      (kernelCubeAverageLp2 Q L k f z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        kernelCubePiece L k g z :=
    (coeFn_kernelCubeAverageLp2 Q L hk hkc f z).trans
      (kernel_average_congr_ae_measure (volume.restrict (heatCube L z))
        (reducedLaw Q) (reducedLaw_stationary Q) hrep k)
  have hg : Measurable g := hlocal.mono (Probability.localSigma_le_borel U) le_rfl
  exact norm_local_hasSum_le hfr hR col W hW hsep
    (kernelCubeAverageLp2 Q L k f) (kernelCubePiece L k g)
    (fun z => measurable_local_kernelCubePiece L z (hUW z) hk hkc.measurable hlocal hB)
    he (fun z => (integral_congr_ae (he z)).trans
      (integral_kernelCubePiece_eq_zero L z hk hkc.measurable hg hB
        (reducedLaw_stationary Q) hmean))
    (fun z => ‖f‖ * kernelCubeMass L k z)
    (norm_kernelCubeAverageLp2_le Q L _ f)
    (by simpa only [mul_pow] using hsq.mul_left (‖f‖ ^ 2))
    (hasSum_kernelCubeAverageLp2 Q hL hk hkc f)

/-- Finite-range Gaussian averaging with an L2 amplitude and the full
anisotropic spatial decay, uniformly over the law and the localization radius. -/
theorem exists_gaussian_average_local_L2_bound (d : ℕ) (Λ r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) → ∀ (ρ : ℝ) (N : ℕ) [NeZero N],
      r < (N : ℝ) - 1 - 2 * ρ → ∀ B : ℝ, 0 ≤ B →
      ∀ f : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ f →
      (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂reducedLaw Q) = 0 →
      ∀ s : ℝ, ∀ hs : 0 < s,
      ‖gaussianAverage hd Q s hs f‖ ≤ C * (N : ℝ) ^ d * ‖f‖ * s ^ (-(d : ℝ) / 4) := by
  let K : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K ^ (1 / 2 : ℝ), by positivity, ?_⟩
  intro hd r₀ Q hfr ρ N _ hgap B hB f hlocal hfB hmean s hs
  obtain ⟨g, hg, hgB, hgf⟩ := exists_bounded_local_version hB hlocal hfB
  have hgm : (∫ ω, g ω ∂reducedLaw Q) = 0 := (integral_congr_ae hgf).trans hmean
  let e := Fintype.equivFin (Fin d → ZMod N)
  have hmass := summable_sq_homogenizedDensity_cubeMass Q one_pos hs
  have hb := norm_kernel_average_le_of_local_L2 Q hfr hgap one_pos
    (fun z => e (heatCubeColour N z)) {y : Vec d | euclideanNorm y < ρ}
    (clockNbhd ρ) (measurableSet_kernelNbhd ρ)
    (fun z x hx y hy => Set.mem_iUnion₂.mpr ⟨x, hx, by simpa using hy⟩)
    (fun z w hzw hcol x hx y hy => kernelNbhd_separated ρ N hzw (e.injective hcol) hx hy)
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs)
    (contDiff_anisotropicGaussian _ _).continuous hmass.1 f g hg hgf.symm hgB hgm
  have hsum : (∑' z, (‖f‖ * kernelCubeMass 1
      (anisotropicGaussian (homogenizedCoefficient Q) s) z) ^ 2) ≤
      (‖f‖ ^ 2 * K) * s ^ (-(d : ℝ) / 2) := by
    simp only [mul_pow]
    rw [tsum_mul_left]
    simpa only [K, one_pow, mul_one, mul_assoc] using
      mul_le_mul_of_nonneg_left hmass.2 (sq_nonneg ‖f‖)
  have hroot := Real.sqrt_le_sqrt hsum
  have hscale : Real.sqrt ((‖f‖ ^ 2 * K) * s ^ (-(d : ℝ) / 2)) =
      ‖f‖ * K ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow,
      Real.mul_rpow (mul_nonneg (sq_nonneg ‖f‖) hK) (Real.rpow_nonneg hs.le _),
      Real.mul_rpow (sq_nonneg ‖f‖) hK, ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (norm_nonneg f), ← Real.rpow_mul hs.le]
    congr 2
    ring
  rw [hscale] at hroot
  have he : gaussianAverage hd Q s hs f =
      ∫ x, ((anisotropicGaussian (homogenizedCoefficient Q) s x : ℝ) : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f := by
    unfold gaussianAverage
    simp_rw [homogenizedGaussianKernel_zero_eq_ofReal]
  rw [he]
  calc
    _ ≤ (Fintype.card (Fin d → ZMod N) : ℝ) *
        Real.sqrt (∑' z, (‖f‖ * kernelCubeMass 1
          (anisotropicGaussian (homogenizedCoefficient Q) s) z) ^ 2) := hb
    _ ≤ (N : ℝ) ^ d * (‖f‖ * K ^ (1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4)) := by
      simpa only [Fintype.card_fun, ZMod.card, Fintype.card_fin, Nat.cast_pow] using
        mul_le_mul_of_nonneg_left hroot
          (Nat.cast_nonneg (Fintype.card (Fin d → ZMod N)))
    _ = _ := by ring

/-- A Cauchy--Schwarz interpolation inequality retaining both spatial
averaging factors. It will be applied to the L2 and higher-moment bounds. -/
theorem eLpNorm_rpow_le_L2_mul_high {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℂ) (hf : AEStronglyMeasurable f P)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm f (ENNReal.ofReal p) P ^ p ≤
      eLpNorm f 2 P * eLpNorm f (ENNReal.ofReal (2 * (p - 1))) P ^ (p - 1) := by
  have hp1 : 0 < p - 1 := by linarith
  have hpow : AEStronglyMeasurable (fun ω => ‖f ω‖ ^ (p - 1)) P :=
    (hf.norm.aemeasurable.pow_const _).aestronglyMeasurable
  have hh := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (p := 2) (q := 2) (r := 1) (fun x y : ℝ => x * y) (1 : ℝ≥0)
    continuous_mul hf.norm hpow (ae_of_all _ fun ω => by simp)
  have he : (fun ω => ‖f ω‖ * ‖f ω‖ ^ (p - 1)) = fun ω => ‖f ω‖ ^ p := by
    funext ω
    by_cases hz : ‖f ω‖ = 0
    · simp [hz, Real.zero_rpow (by linarith : p ≠ 0)]
    · have hn : 0 < ‖f ω‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      calc
        _ = ‖f ω‖ ^ (1 : ℝ) * ‖f ω‖ ^ (p - 1) := by rw [Real.rpow_one]
        _ = ‖f ω‖ ^ (1 + (p - 1)) := (Real.rpow_add hn _ _).symm
        _ = _ := by congr 1; ring
  rw [he, eLpNorm_norm_rpow f hf (by linarith : 0 < p),
    eLpNorm_norm_rpow f hf hp1] at hh
  rw [eLpNorm_norm f hf] at hh
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simpa only [one_mul, ENNReal.coe_one, ENNReal.ofReal_ofNat] using hh

/-- Root form of the L2/higher-moment interpolation estimate. -/
theorem eLpNorm_le_L2_rpow_mul_high_rpow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℂ) (hf : AEStronglyMeasurable f P)
    (p : ℝ) (hp : 2 ≤ p) :
    eLpNorm f (ENNReal.ofReal p) P ≤
      eLpNorm f 2 P ^ (1 / p) *
        eLpNorm f (ENNReal.ofReal (2 * (p - 1))) P ^ ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have hh := ENNReal.rpow_le_rpow (eLpNorm_rpow_le_L2_mul_high P f hf p hp)
    (by positivity : 0 ≤ 1 / p)
  rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p),
    ← ENNReal.rpow_mul] at hh
  simpa only [div_eq_mul_inv, one_mul] using hh

/-- The fixed local conditional projection inherits the error of any
actual local L2 approximation, using only projection contraction. -/
theorem norm_sub_project_le_two_mul {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ρ : ℝ) (F G : Lp ℂ 2 (reducedLaw Q))
    (hG : IsComplexLocalObservation Q ρ G) :
    ‖F - EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) F‖ ≤ 2 * ‖F - G‖ := by
  let m := localSigma {x : Vec d | euclideanNorm x < ρ}
  have hm := Probability.localSigma_le_borel {x : Vec d | euclideanNorm x < ρ}
  obtain ⟨g, hg, hgf⟩ := hG
  have hgi : Integrable g (reducedLaw Q) :=
    ((Lp.memLp G).integrable (by norm_num)).congr hgf.symm
  have hfix : EndpointProjection.project (m := m) G = G := by
    apply Lp.ext
    exact (EndpointProjection.project_ae G).trans
      ((condExp_congr_ae hgf.symm).trans
        ((Filter.EventuallyEq.of_eq (condExp_of_stronglyMeasurable hm
          hg.stronglyMeasurable hgi)).trans hgf))
  let A := EndpointProjection.projectionCLM (μ := reducedLaw Q) (m := m) (p := 2)
  have he : F - A F = (F - G) - A (F - G) := by
    rw [map_sub]
    change F - A F = (F - G) - (A F - EndpointProjection.project (m := m) G)
    rw [hfix]
    abel
  change ‖F - A F‖ ≤ _
  rw [he]
  exact (norm_sub_le _ _).trans (by
    have hb := EndpointProjection.norm_project_le (m := m) (F - G)
    change ‖A (F - G)‖ ≤ ‖F - G‖ at hb
    linarith)

/-- Interpolation consumes numerical L2 and higher-moment bounds directly. -/
theorem eLpNorm_le_of_L2_high_bounds {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Lp ℂ 2 P) (p : ℝ) (hp : 2 ≤ p)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h2 : ‖f‖ ≤ A)
    (hq : eLpNorm (f : Ω → ℂ) (ENNReal.ofReal (2 * (p - 1))) P ≤ ENNReal.ofReal B) :
    eLpNorm (f : Ω → ℂ) (ENNReal.ofReal p) P ≤
      ENNReal.ofReal (A ^ (1 / p) * B ^ ((p - 1) / p)) := by
  have hp0 : 0 < p := by linarith
  have he1 : 0 ≤ 1 / p := by positivity
  have he2 : 0 ≤ (p - 1) / p := div_nonneg (by linarith) hp0.le
  have h2' : eLpNorm (f : Ω → ℂ) 2 P ≤ ENNReal.ofReal A := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal h2
  calc
    _ ≤ eLpNorm (f : Ω → ℂ) 2 P ^ (1 / p) *
        eLpNorm (f : Ω → ℂ) (ENNReal.ofReal (2 * (p - 1))) P ^ ((p - 1) / p) :=
      eLpNorm_le_L2_rpow_mul_high_rpow P f (Lp.aestronglyMeasurable f) p hp
    _ ≤ ENNReal.ofReal A ^ (1 / p) * ENNReal.ofReal B ^ ((p - 1) / p) :=
      mul_le_mul' (ENNReal.rpow_le_rpow h2' he1) (ENNReal.rpow_le_rpow hq he2)
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg hA he1,
        ENNReal.ofReal_rpow_of_nonneg hB he2,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg hA _)]

/-- The common spatial factor survives interpolation without a loss of decay. -/
theorem interpolation_common_factor {W A B p : ℝ} (hW : 0 ≤ W)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 2 ≤ p) :
    (W * A) ^ (1 / p) * (W * B) ^ ((p - 1) / p) =
      W * A ^ (1 / p) * B ^ ((p - 1) / p) := by
  have hp0 : 0 < p := by linarith
  have he1 : 0 < 1 / p := by positivity
  have he2 : 0 < (p - 1) / p := div_pos (by linarith) hp0
  by_cases hW0 : W = 0
  · simp [hW0, Real.zero_rpow he1.ne', Real.zero_rpow he2.ne']
  have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hW0)
  rw [Real.mul_rpow hW hA, Real.mul_rpow hW hB]
  calc
    _ = (W ^ (1 / p) * W ^ ((p - 1) / p)) *
        A ^ (1 / p) * B ^ ((p - 1) / p) := by ring
    _ = _ := by
      rw [← Real.rpow_add hWpos]
      have he : 1 / p + (p - 1) / p = 1 := by field_simp; ring
      rw [he, Real.rpow_one]

/-- Local Gaussian averaging uses the small L2 amplitude and a bounded
higher moment together, with the full anisotropic spatial exponent. -/
theorem exists_gaussian_average_local_interpolated_bound (d : ℕ) (Λ r p : ℝ)
    (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) → ∀ (ρ : ℝ) (N : ℕ) [NeZero N],
      r < (N : ℝ) - 1 - 2 * ρ → ∀ B : ℝ, 0 ≤ B →
      ∀ f : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ f →
      (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) → (∫ ω, f ω ∂reducedLaw Q) = 0 →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (N : ℝ) ^ d * ‖f‖ ^ (1 / p) * B ^ ((p - 1) / p) *
            s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_gaussian_average_local_L2_bound d Λ r
  obtain ⟨Cq, hCq, hbq⟩ := exists_gaussian_average_local_bound_linear d Λ r
    (2 * (p - 1)) (by linarith)
  let C := max C₂ Cq
  have hC : 0 ≤ C := le_trans hC₂ (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr ρ N _ hgap B hB f hlocal hfB hmean s hs
  let W := C * (N : ℝ) ^ d * s ^ (-(d : ℝ) / 4)
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have h2 : ‖gaussianAverage hd Q s hs f‖ ≤ W * ‖f‖ := by
    calc
      _ ≤ C₂ * (N : ℝ) ^ d * ‖f‖ * s ^ (-(d : ℝ) / 4) :=
        hb₂ hd Q hfr ρ N hgap B hB f hlocal hfB hmean s hs
      _ ≤ C * (N : ℝ) ^ d * ‖f‖ * s ^ (-(d : ℝ) / 4) := by
        gcongr
        exact le_max_left _ _
      _ = _ := by dsimp [W]; ring
  obtain ⟨hmq, hnq⟩ := hbq hd Q hfr ρ N hgap B hB f hlocal hfB hmean s hs
  have hq : eLpNorm (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal (2 * (p - 1))) (reducedLaw Q) ≤ ENNReal.ofReal (W * B) := by
    rw [← ENNReal.ofReal_toReal hmq.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Cq * (N : ℝ) ^ d * B * s ^ (-(d : ℝ) / 4) := hnq
      _ ≤ C * (N : ℝ) ^ d * B * s ^ (-(d : ℝ) / 4) := by
        gcongr
        exact le_max_right _ _
      _ = _ := by dsimp [W]; ring
  have he := eLpNorm_le_of_L2_high_bounds (reducedLaw Q)
    (gaussianAverage hd Q s hs f) p hp (mul_nonneg hW (norm_nonneg f))
    (mul_nonneg hW hB) h2 hq
  rw [interpolation_common_factor hW (norm_nonneg f) hB hp] at he
  have hm : MemLp (gaussianAverage hd Q s hs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) :=
    lt_of_le_of_lt he ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  have hn := ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  rw [ENNReal.toReal_ofReal (by positivity)] at hn
  calc
    _ ≤ W * ‖f‖ ^ (1 / p) * B ^ ((p - 1) / p) := hn
    _ = _ := by dsimp [W]; ring

/-- A true L2 series of bounded local pieces can be summed using their
small L2 amplitudes, while preserving the spatial exponent at finite p. -/
theorem exists_gaussian_average_interpolated_series_bound (d : ℕ) (Λ r p : ℝ)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (f : ℕ → Lp ℂ 2 (reducedLaw Q)) (F : Lp ℂ 2 (reducedLaw Q)),
      HasSum f F → ∀ (ρ : ℕ → ℝ) (N : ℕ → ℕ) [∀ n, NeZero (N n)],
      (∀ n, r < (N n : ℝ) - 1 - 2 * ρ n) →
      ∀ B : ℝ, 0 ≤ B → ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) →
      (∀ n, ‖f n‖ ≤ a n) →
      (∀ n, IsComplexLocalObservation Q (ρ n) (f n)) →
      (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖f n ω‖ ≤ B) →
      (∀ n, (∫ ω, f n ω ∂reducedLaw Q) = 0) →
      Summable (fun n => (N n : ℝ) ^ d * (a n) ^ (1 / p)) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs F : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * B ^ ((p - 1) / p) *
            (∑' n, (N n : ℝ) ^ d * (a n) ^ (1 / p)) * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_average_local_interpolated_bound d Λ r p hp
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr f F hF ρ N _ hgap B hB a ha hnorm hlocal hfB hmean hw s hs
  have hpiece (n : ℕ) := hb hd Q hfr (ρ n) (N n) (hgap n) B hB
    (f n) (hlocal n) (hfB n) (hmean n) s hs
  let b : ℕ → ℝ := fun n => C * B ^ ((p - 1) / p) *
    ((N n : ℝ) ^ d * (a n) ^ (1 / p)) * s ^ (-(d : ℝ) / 4)
  have hsum : Summable b := (hw.mul_left (C * B ^ ((p - 1) / p))).mul_right _
  have hbound (n : ℕ) : (eLpNorm (gaussianAverage hd Q s hs (f n) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ b n := by
    calc
      _ ≤ C * (N n : ℝ) ^ d * ‖f n‖ ^ (1 / p) * B ^ ((p - 1) / p) *
          s ^ (-(d : ℝ) / 4) := (hpiece n).2
      _ ≤ C * (N n : ℝ) ^ d * (a n) ^ (1 / p) * B ^ ((p - 1) / p) *
          s ^ (-(d : ℝ) / 4) := by
        gcongr
        exact hnorm n
      _ = _ := by dsimp [b]; ring
  have h := gaussian_average_series_bound hd Q p hp s hs f F hF
    (fun n => (hpiece n).1) b hsum hbound
  refine ⟨h.1, ?_⟩
  simpa only [b, tsum_mul_right, tsum_mul_left] using h.2

/-- Bounded centered local approximants with small L2 errors give a genuine
finite-p multiscale estimate. Approximation errors are used only in L2 norm. -/
theorem exists_gaussian_average_norm_approximants_bound (d : ℕ) (Λ r p : ℝ)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q))
        (ρ : ℕ → ℝ) (N : ℕ → ℕ) [∀ n, NeZero (N n)],
      Monotone ρ → (∀ n, r < (N n : ℝ) - 1 - 2 * ρ n) →
      ∀ B : ℝ, 0 ≤ B → (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖K n ω‖ ≤ B) →
      (∀ n, IsComplexLocalObservation Q (ρ n) (K n)) →
      (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
      ∀ a : ℕ → ℝ, (∀ n, 0 ≤ a n) → Summable a →
      (∀ n, ‖H - K n‖ ≤ a n) →
      Summable (fun n => (N (n + 1) : ℝ) ^ d * (a n + a (n + 1)) ^ (1 / p)) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (2 * B) ^ ((p - 1) / p) *
            ((N 0 : ℝ) ^ d * B ^ (1 / p) +
              ∑' n, (N (n + 1) : ℝ) ^ d * (a n + a (n + 1)) ^ (1 / p)) *
                s ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussian_average_interpolated_series_bound d Λ r p hp
  refine ⟨C, hC, ?_⟩
  intro hd r₀ Q hfr H K ρ N _ hρ hgap B hB hK hlocal hmean a ha hsum herr hw s hs
  let f : ℕ → Lp ℂ 2 (reducedLaw Q)
    | 0 => K 0
    | n + 1 => K (n + 1) - K n
  let b : ℕ → ℝ
    | 0 => B
    | n + 1 => a n + a (n + 1)
  have hlocal' (n : ℕ) : IsComplexLocalObservation Q (ρ n) (f n) := by
    cases n with
    | zero => exact hlocal 0
    | succ n =>
      obtain ⟨g₁, hg₁, he₁⟩ := hlocal (n + 1)
      obtain ⟨g₀, hg₀, he₀⟩ := hlocal n
      have hg₀' := hg₀.mono (Probability.localSigma_mono
        (fun x hx => hx.trans_le (hρ (Nat.le_succ n)))) le_rfl
      exact ⟨fun ω => g₁ ω - g₀ ω, hg₁.sub hg₀',
        (he₁.sub he₀).trans (Lp.coeFn_sub _ _).symm⟩
  have hbound (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q, ‖f n ω‖ ≤ 2 * B := by
    cases n with
    | zero => exact (hK 0).mono fun ω h => h.trans (by linarith)
    | succ n =>
      filter_upwards [hK n, hK (n + 1), Lp.coeFn_sub (K (n + 1)) (K n)]
        with ω hn hn₁ he
      change ‖(K (n + 1) - K n) ω‖ ≤ 2 * B
      rw [he]
      exact (norm_sub_le _ _).trans (by linarith)
  have hnorm (n : ℕ) : ‖f n‖ ≤ b n := by
    cases n with
    | zero =>
      change ‖K 0‖ ≤ B
      rw [Lp.norm_def]
      exact AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le
        (Lp.memLp _).aestronglyMeasurable hB (hK 0)
    | succ n =>
      change ‖K (n + 1) - K n‖ ≤ a n + a (n + 1)
      have hh := norm_sub_le_norm_sub_add_norm_sub (K (n + 1)) H (K n)
      rw [norm_sub_rev (K (n + 1)) H] at hh
      exact hh.trans (add_le_add (herr (n + 1)) (herr n) |>.trans (le_of_eq (add_comm _ _)))
  have hmean' (n : ℕ) : (∫ ω, f n ω ∂reducedLaw Q) = 0 := by
    cases n with
    | zero => exact hmean 0
    | succ n =>
      rw [show f (n + 1) = K (n + 1) - K n from rfl,
        integral_congr_ae (Lp.coeFn_sub _ _)]
      change (∫ ω, K (n + 1) ω - K n ω ∂reducedLaw Q) = 0
      rw [integral_sub ((Lp.memLp (K (n + 1))).integrable (by norm_num))
        ((Lp.memLp (K n)).integrable (by norm_num)), hmean, hmean, sub_self]
  have hF : HasSum f H := by
    apply (hasSum_nat_add_iff' 1).mp
    simpa only [f, Finset.sum_range_one] using
      hasSum_localization_differences K H a hsum herr
  have hw' : Summable (fun n => (N n : ℝ) ^ d * (b n) ^ (1 / p)) := by
    apply (summable_nat_add_iff 1).mp
    exact hw
  have h := hb hd Q hfr f H hF ρ N hgap (2 * B) (by positivity) b (fun n => by
      cases n with
      | zero => exact hB
      | succ n => exact add_nonneg (ha n) (ha (n + 1)))
    hnorm hlocal' hbound hmean' hw' s hs
  have hweight : (∑' n, (N n : ℝ) ^ d * (b n) ^ (1 / p)) =
      (N 0 : ℝ) ^ d * B ^ (1 / p) +
        ∑' n, (N (n + 1) : ℝ) ^ d * (a n + a (n + 1)) ^ (1 / p) := by
    simpa only [Finset.sum_range_one, b] using (hw'.sum_add_tsum_nat_add 1).symm
  exact ⟨h.1, by simpa only [hweight] using h.2⟩

/-- Rooted Gaussian localization errors remain summable against the actual
linearly growing residue counts, for every finite exponent. -/
theorem summable_residue_rooted_gaussian_errors (k M : ℕ) {L b p : ℝ}
    (hL : 0 ≤ L) (hb : 0 < b) (hp : 0 < p) :
    Summable (fun n : ℕ => ((M * (n + 2) : ℕ) : ℝ) ^ k *
      (L * Real.exp (-b * (n : ℝ) ^ 2) +
        L * Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2)) ^ (1 / p)) := by
  have hsum := (summable_nat_add_two_pow_mul_exp_neg_sq k (div_pos hb hp)).mul_left
    ((2 * L) ^ (1 / p) * (M : ℝ) ^ k)
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hsum
  intro n
  have hsq : (n : ℝ) ^ 2 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have he : Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-b * (n : ℝ) ^ 2) := Real.exp_le_exp.mpr
    (mul_le_mul_of_nonpos_left hsq (by linarith))
  calc
    _ ≤ ((M * (n + 2) : ℕ) : ℝ) ^ k *
        (2 * L * Real.exp (-b * (n : ℝ) ^ 2)) ^ (1 / p) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Nat.cast_nonneg _) k)
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith [mul_le_mul_of_nonneg_left he hL]
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * L) (Real.exp_pos _).le,
        ← Real.exp_mul]
      have heq : (-b * (n : ℝ) ^ 2) * (1 / p) = -(b / p) * (n : ℝ) ^ 2 := by ring
      rw [heq]
      push_cast
      rw [mul_pow]
      ring

/-- Gaussian L2 approximation errors, with bounded centered local
approximants, imply the full finite-p spatial decay of the actual average. -/
theorem exists_gaussian_average_of_gaussian_norm_approximants
    (d : ℕ) (Λ r R B L b p : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hb : 0 < b) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (hd : 2 ≤ d) {r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀),
      HasFiniteRange r (reducedLaw Q) →
      ∀ (H : Lp ℂ 2 (reducedLaw Q)) (K : ℕ → Lp ℂ 2 (reducedLaw Q)),
      (∀ n, ∀ᵐ ω ∂reducedLaw Q, ‖K n ω‖ ≤ B) →
      (∀ n : ℕ, IsComplexLocalObservation Q (R + n) (K n)) →
      (∀ n, (∫ ω, K n ω ∂reducedLaw Q) = 0) →
      (∀ n, ‖H - K n‖ ≤ L * Real.exp (-b * (n : ℝ) ^ 2)) →
      ∀ s : ℝ, ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (-(d : ℝ) / 4) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (|r| + 2 * R + 4)
  have hMpos : (0 : ℝ) < M := by linarith [abs_nonneg r]
  have hMne : M ≠ 0 := by exact_mod_cast hMpos.ne'
  have hMtwo : 0 ≤ (M : ℝ) - 2 := by linarith [abs_nonneg r]
  let N : ℕ → ℕ := fun n => M * (n + 1)
  let a : ℕ → ℝ := fun n => L * Real.exp (-b * (n : ℝ) ^ 2)
  let w : ℕ → ℝ := fun n => (N (n + 1) : ℝ) ^ d * (a n + a (n + 1)) ^ (1 / p)
  have hw : Summable w := by
    simpa only [w, N, a, Nat.add_assoc] using
      summable_residue_rooted_gaussian_errors d M hL hb (by linarith : 0 < p)
  have hw0 : 0 ≤ ∑' n, w n := tsum_nonneg fun n => by dsimp only [w, a]; positivity
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_average_norm_approximants_bound d Λ r p hp
  refine ⟨C * (2 * B) ^ ((p - 1) / p) *
    ((M : ℝ) ^ d * B ^ (1 / p) + ∑' n, w n), by positivity, ?_⟩
  intro hd r₀ Q hfr H K hKB hlocal hmean herr s hs
  letI (n : ℕ) : NeZero (N n) := ⟨Nat.mul_ne_zero hMne (Nat.succ_ne_zero n)⟩
  have hρ : Monotone (fun n : ℕ => R + (n : ℝ)) :=
    fun n m hnm => by dsimp only; linarith [(Nat.cast_le.mpr hnm : (n : ℝ) ≤ m)]
  have hgap (n : ℕ) : r < (N n : ℝ) - 1 - 2 * (R + n) := by
    dsimp only [N]
    push_cast
    nlinarith [mul_nonneg hMtwo (Nat.cast_nonneg (α := ℝ) n), le_abs_self r]
  have ha : Summable a := (summable_nat_pow_mul_exp_neg_sq 0 hb).mul_left L |>.congr
    (fun n => by simp only [pow_zero, one_mul, a])
  have h := hbound hd Q hfr H K (fun n => R + n) N hρ hgap B hB hKB hlocal hmean
    a (fun n => mul_nonneg hL (Real.exp_pos _).le) ha herr hw s hs
  refine ⟨h.1, ?_⟩
  simpa only [N, Nat.zero_add, Nat.mul_one, w] using h.2

/-- The fixed local projection is bounded and centered; its L2 error is at
most twice the error of any genuine local L2 approximant. -/
theorem exists_bounded_centered_local_projection_norm {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ρ : ℝ) (H G : Lp ℂ 2 (reducedLaw Q))
    {B ε : ℝ} (hB : ∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ B)
    (hmean : (∫ ω, H ω ∂reducedLaw Q) = 0)
    (hG : IsComplexLocalObservation Q ρ G) (herr : ‖H - G‖ ≤ ε) :
    ∃ K : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ K ∧
      (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧ ‖H - K‖ ≤ 2 * ε := by
  obtain ⟨K, hK, hlocal⟩ := EndpointProjection.exists_local_l2 Q ρ (by norm_num) H
  have hKeq : K = EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) H := Lp.ext hK.symm
  refine ⟨K, hlocal, ?_, ?_, ?_⟩
  · rw [hKeq]
    exact (EndpointProjection.integral_project (Probability.localSigma_le_borel _) H).trans hmean
  · rw [hKeq]
    exact ae_norm_project_le (m := localSigma {x : Vec d | euclideanNorm x < ρ}) H hB
  · rw [hKeq]
    exact (norm_sub_project_le_two_mul Q ρ H G hG).trans (by linarith)

/-- The two exact dependencies give bounded local quotient approximants in
L2 norm at every time, including zero. No AE approximation error is asserted. -/
theorem exists_all_time_local_force_quotient
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B R c : ℝ, 1 ≤ B ∧ 1 ≤ R ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ζ ≠ 0 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    ∃ E E₀ H : Lp ℂ 2 (reducedLaw Q),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P Pdag β a μ t ∧
      (E₀ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν 0 (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
          (fun s => complexL2Transpose (reducedLaw Q)
            (forcedComplexEvolution Q ⟨0, by omega⟩ 0 s)) β a μ t ∧
      E - E₀ = ζ • H ∧ (∫ ω, H ω ∂reducedLaw Q) = 0 ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ B) ∧
      ∀ ρ : ℝ, R ≤ ρ → ∃ K : Lp ℂ 2 (reducedLaw Q),
        IsComplexLocalObservation Q ρ K ∧ (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
        (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
        ‖H - K‖ ≤ 2 * R * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨B, hB, hb⟩ := exists_ae_bounded_force_quotient hlocal hends d hd D T hT
  have hpacket := exists_force_quotient hends d hd D 2 (by norm_num) T hT
  generalize hq : ENNReal.ofReal (2 : ℝ) = q at hpacket
  have hq2 : q = 2 := by rw [← hq]; norm_num
  cases hq2
  obtain ⟨R, c, hR, hc, hr⟩ := hpacket
  refine ⟨B, R, c, hB, hR, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ hζne t ht
  obtain ⟨E, E₀, H, he, he₀, hf, hm, hHB⟩ :=
    hb Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  obtain ⟨E', E₀', H', he', he₀', hf', _, _, happrox⟩ :=
    hr Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht
  have hEE : E = E' := Lp.ext (he.trans he'.symm)
  have hE₀E₀ : E₀ = E₀' := Lp.ext (he₀.trans he₀'.symm)
  have hsmul : ζ • H = ζ • H' := by rw [← hf, ← hf', hEE, hE₀E₀]
  have hHH : H = H' := by
    have h := congrArg (fun X : Lp ℂ 2 (reducedLaw Q) => ζ⁻¹ • X) hsmul
    simpa only [smul_smul, inv_mul_cancel₀ hζne, one_smul] using h
  refine ⟨E, E₀, H, he, he₀, hf, hm, hHB, ?_⟩
  intro ρ hρ
  obtain ⟨K, K₂, hK, hKlocal, _, _, herror⟩ := happrox ρ hρ
  have hKK : K = K₂ := Lp.ext hK
  have herr : ‖H - K₂‖ ≤ R * Real.exp (-c * ρ ^ 2) := by
    simpa only [hHH, hKK] using herror
  obtain ⟨L, hLlocal, hLm, hLB, hLerr⟩ :=
    exists_bounded_centered_local_projection_norm Q ρ H K₂ hHB hm hKlocal herr
  refine ⟨L, hLlocal, hLm, hLB, ?_⟩
  simpa only [mul_assoc] using hLerr

/-- The force-dependent quotient has full Gaussian spatial decay throughout
the finite time horizon, including t=0, from exactly V1 and analytic endpoints. -/
theorem exists_all_time_gaussian_force_quotient
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T p : ℝ) (hT : 0 ≤ T)
    (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)] :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ζ ≠ 0 → ∀ t : ℝ≥0, (t : ℝ) ≤ T →
    ∃ E E₀ H : Lp ℂ 2 (reducedLaw Q),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν ζ P Pdag β a μ t ∧
      (E₀ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν 0 (forcedComplexEvolution Q ⟨0, by omega⟩ 0)
          (fun s => complexL2Transpose (reducedLaw Q)
            (forcedComplexEvolution Q ⟨0, by omega⟩ 0 s)) β a μ t ∧
      E - E₀ = ζ • H ∧ (∫ ω, H ω ∂reducedLaw Q) = 0 ∧
      ∀ s : ℝ, ∀ hs : 0 < s,
        MemLp (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianAverage hd Q s hs H : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C * s ^ (-(d : ℝ) / 4) := by
  classical
  obtain ⟨B, R, c, hB, hR, hc, hf⟩ :=
    exists_all_time_local_force_quotient hlocal hends d hd D T hT
  obtain ⟨C, hC, hbound⟩ := exists_gaussian_average_of_gaussian_norm_approximants
    d D.ellipticity D.dependenceRange R B (2 * R) c p (by linarith)
    (by linarith) (by linarith) hc hp
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ hζne t ht
  obtain ⟨E, E₀, H, he, he₀, hfactor, hmean, _, hloc⟩ :=
    hf Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ hζne t ht
  choose K hK using fun n : ℕ => hloc (R + n) (le_add_of_nonneg_right (Nat.cast_nonneg n))
  have herr (n : ℕ) : ‖H - K n‖ ≤ 2 * R * Real.exp (-c * (n : ℝ) ^ 2) := by
    have hsq : (n : ℝ) ^ 2 ≤ (R + n) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    exact (hK n).2.2.2.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsq (by linarith))) (by linarith))
  refine ⟨E, E₀, H, he, he₀, hfactor, hmean, ?_⟩
  intro s hs
  exact hbound hd Q (Localization.finiteRange_map_reduce Q.measure Q.finiteRange)
    H K (fun n => (hK n).2.2.1) (fun n => (hK n).1) (fun n => (hK n).2.1) herr s hs

/-- A uniform essential bound passes through an actual finite-measure L2
Bochner integral. Testing against set indicators avoids pointwise time choices. -/
theorem ae_norm_integral_Lp_le {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    {m : Measure α} [IsFiniteMeasure m] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {f : α → Lp ℂ 2 μ} (hf : Integrable f m) {B : ℝ}
    (hB : ∀ᵐ x ∂m, ∀ᵐ ω ∂μ, ‖f x ω‖ ≤ B) :
    ∀ᵐ ω ∂μ, ‖(∫ x, f x ∂m) ω‖ ≤ 2 * (B * m.real Set.univ) := by
  apply ae_norm_le_of_setIntegral_norm_le ((Lp.memLp _).integrable (by norm_num))
  intro S hS
  let J : Lp ℂ 2 μ →L[ℂ] ℂ :=
    innerSL ℂ (indicatorConstLp 2 hS (measure_ne_top μ S) (1 : ℂ))
  have hJ (u : Lp ℂ 2 μ) : J u = ∫ ω in S, u ω ∂μ :=
    L2.inner_indicatorConstLp_one hS (measure_ne_top μ S) u
  rw [← hJ, ← J.integral_comp_comm hf]
  have hb : ∀ᵐ x ∂m, ‖J (f x)‖ ≤ B * μ.real S := by
    filter_upwards [hB] with x hx
    rw [hJ]
    exact norm_setIntegral_le_of_norm_le_const_ae (measure_lt_top μ S)
      (ae_restrict_of_ae hx)
  have hh := norm_integral_le_of_norm_le_const hb
  exact hh.trans_eq (by ring)

/-- V1's gradient bound identifies and controls the actual zero-force gradient
orbit at every positive time; no short-time gradient locality is asserted. -/
theorem exists_bounded_unforced_drift_gradient
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ B : ℝ, 0 ≤ B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
      IsComplexTransposeSemigroup Q P Pdag → ∀ j k : Fin d,
      ∀ t : ℝ, 0 < t → t ≤ T →
      ∀ᵐ ω ∂reducedLaw Q, ‖hP.gradientOrbit (β j) t k ω‖ ≤ B := by
  obtain ⟨A, c, N, hA, _, hloc⟩ := hlocal d hd D
  refine ⟨A * (2 + T) ^ N, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag j k t ht htT
  obtain ⟨G, hG, _, hb⟩ := hloc Q hQ β a μ hβ ha hμ 0 P Pdag hP hPdag (.inl j)
  have htn : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht.le
  have hg : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t.toNNReal (β j)) (G t.toNNReal) := by
    simpa only [uncenteredEndpoint, zero_smul, add_zero] using
      (hG t.toNNReal (by simpa only [htn] using ht)).2
  have he : (fun k => hP.gradientOrbit (β j) t k) = G t.toNNReal :=
    (hP.gradientOrbit_spec (β j) ht).unique hg
  have hpow : (2 + t) ^ N ≤ (2 + T) ^ N :=
    pow_le_pow_left₀ (by linarith) (by linarith) N
  have hbound := hb t.toNNReal (by simpa only [htn] using ht) (by norm_num)
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Real.exp_zero,
    mul_one, htn] at hbound
  filter_upwards [hbound] with ω hω
  rw [congrFun he k]
  have hs : ‖G t.toNNReal k ω‖ ^ 2 ≤ ∑ l : Fin d, ‖G t.toNNReal l ω‖ ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg ‖G t.toNNReal l ω‖) (Finset.mem_univ k)
  have hnn : 0 ≤ ∑ l : Fin d, ‖G t.toNNReal l ω‖ ^ 2 :=
    Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have hk : ‖G t.toNNReal k ω‖ ≤ Real.sqrt (∑ l : Fin d, ‖G t.toNNReal l ω‖ ^ 2) := by
    nlinarith [Real.sq_sqrt hnn, norm_nonneg (G t.toNNReal k ω), Real.sqrt_nonneg
      (∑ l : Fin d, ‖G t.toNNReal l ω‖ ^ 2)]
  exact hk.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hω |>.trans
    (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hA)))

/-- The actual zero-force source bracket is deterministically bounded on each
finite horizon, including time zero. Its short-time locality remains separate. -/
theorem exists_bounded_unforced_flux_bracket
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ j l : Fin d,
    ∀ᵐ ω ∂reducedLaw Q,
      ‖(ω.1 0 l j : ℂ) +
        (∫ s in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k (hP.gradientOrbit (β j) s k) :
            Lp ℂ 2 (reducedLaw Q)) ω‖ ≤ C := by
  obtain ⟨B, hB, hb⟩ := exists_bounded_unforced_drift_gradient hlocal d hd D T hT
  obtain ⟨K, hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨K + (d : ℝ) * K * (2 * (B * T)), by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht j l
  have hprimitive (k : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ‖((∫ s in Set.Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j) s) k) ω‖ ≤
        2 * (B * T) := by
    let J := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k
    have hi := J.integrable_comp (hP.integrableOn_gradientOrbit (β j) t)
    have htime : ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) (t : ℝ)),
        ∀ᵐ ω ∂reducedLaw Q, ‖hP.gradientOrbit (β j) s k ω‖ ≤ B := by
      filter_upwards [ae_restrict_mem measurableSet_Icc,
        ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
      exact hb Q hQ β a μ hβ ha hμ P Pdag hP hPdag j k s
        (lt_of_le_of_ne hs.1 (Ne.symm hs0)) (hs.2.trans ht)
    have hh := ae_norm_integral_Lp_le hi htime
    have hmeasure : (volume.restrict (Set.Icc (0 : ℝ) (t : ℝ))).real Set.univ = t := by
      simp [measureReal_def, t.coe_nonneg]
    rw [J.integral_comp_comm (hP.integrableOn_gradientOrbit (β j) t), hmeasure] at hh
    exact hh.mono fun ω h => h.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left ht hB) (by norm_num))
  have hc (k : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ‖(ω.1 0 l k : ℂ)‖ ≤ K := by
    filter_upwards [(hobs Q hQ β a μ hβ ha hμ).2.1 l k, ha l k] with ω hk he
    simpa only [he] using hk
  filter_upwards [hP.integral_flux_gradientOrbit_coe (β j) t l,
    ae_all_iff.mpr hprimitive, ae_all_iff.mpr hc, hc j] with ω he hg hcω hcj
  rw [he]
  apply (norm_add_le _ _).trans
  have hs : ‖∑ k, (ω.1 0 l k : ℂ) *
      ((∫ s in Set.Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j) s) k) ω‖ ≤
        (d : ℝ) * K * (2 * (B * T)) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _k : Fin d, K * (2 * (B * T)) := by
        apply Finset.sum_le_sum
        intro k _
        rw [norm_mul]
        exact mul_le_mul (hcω k) (hg k) (norm_nonneg _) hK.le
      _ = _ := by simp; ring
  exact add_le_add hcj hs

/-- Gaussian smoothing of the actual unforced drift moves its weak divergence
onto the anisotropic Gaussian kernel. The bracket is the actual L2 flux. -/
theorem unforced_gaussian_flux_pairing
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (t : ℝ≥0) (j : Fin d) (s : ℝ) (hs : 0 < s)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    let F := fun l => a l j + ∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
      complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k)
    c4EndpointPairing Q (gaussianAverage hd Q s hs (P t (β j))) g =
      (1 / 2 : ℂ) * ∑ l, c4EndpointPairing Q
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (F l)) g := by
  intro F
  let V := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 g
  have hV := homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ s hs 0 g
  have hw := hP.unforced_orbit_weak_flux_timeIntegral hβ t j
    (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g) V hV
  have hF (l : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      F l ω = (ω.1 0 l j : ℂ) + (∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
        complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k) :
          Lp ℂ 2 (reducedLaw Q)) ω := by
    filter_upwards [Lp.coeFn_add (a l j) (∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
      complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k)), ha l j] with ω he haω
    exact he.trans (congrArg (fun z : ℂ => z + _) haω)
  have hi (l : Fin d) : Integrable (fun ω => F l ω * V l ω) (reducedLaw Q) :=
    (Lp.memLp (F l)).integrable_mul (Lp.memLp (V l))
  have he : (∫ ω, ∑ l,
      ((ω.1 0 l j : ℂ) + (∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
        complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k) :
          Lp ℂ 2 (reducedLaw Q)) ω) * V l ω ∂reducedLaw Q) =
        ∑ l, c4EndpointPairing Q (F l) (V l) := by
    simp only [c4EndpointPairing_apply]
    rw [← integral_finset_sum _ (fun l _ => hi l)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hF] with ω hω
    simp only [c4EndpointPairing_apply] at *
    simp only [hω]
  rw [he] at hw
  have hav := c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (P t (β j)) g
  simp only [neg_zero] at hav
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (P t (β j))) g = _
  rw [hav, c4EndpointPairing_apply, hw]
  have hder (l : Fin d) : c4EndpointPairing Q
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => l) (F l)) g =
        -c4EndpointPairing Q (F l) (V l) := by
    rw [c3EndpointPairing_gaussianDerivativeAverage_one,
      c3GaussianDerivativeAverage_one_eq_gradient]
  simp_rw [hder]
  rw [Finset.sum_neg_distrib]
  ring

/-- The physical bilinear pairing separates actual complex L2 classes. -/
theorem endpointPairing_ext {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {f h : Lp ℂ 2 (reducedLaw Q)}
    (he : ∀ g, c4EndpointPairing Q f g = c4EndpointPairing Q h g) : f = h := by
  have hc : complexL2Conjugation (reducedLaw Q) f =
      complexL2Conjugation (reducedLaw Q) h := by
    apply ext_inner_right ℂ
    intro g
    simpa only [inner_complexL2Conjugation_eq_integral_mul,
      c4EndpointPairing_apply] using he g
  simpa only [complexL2Conjugation_involutive] using
    congrArg (complexL2Conjugation (reducedLaw Q)) hc

/-- Centering does not change a first Gaussian derivative of any actual L2 datum. -/
theorem gaussianDerivativeAverage_one_centered {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (centeredComplexLp Q f) =
      gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f := by
  apply endpointPairing_ext Q
  intro g
  rw [c3EndpointPairing_gaussianDerivativeAverage_one,
    c3EndpointPairing_gaussianDerivativeAverage_one]
  simp only [c3GaussianDerivativeAverage_one_eq_gradient]
  rw [c3EndpointPairing_centered_gradient Q
    (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g)
    (homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 g)
    (homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 g) f j]

/-- Actual Gaussian-smoothed unforced drift is the Gaussian derivative of its
centered physical flux bracket, at every nonnegative physical time. -/
theorem unforced_gaussian_centered_flux
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (t : ℝ≥0) (j : Fin d) (s : ℝ) (hs : 0 < s) :
    let F := fun l => a l j + ∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
      complexCoefficientMul Q l k (hP.gradientOrbit (β j) r k)
    gaussianAverage hd Q s hs (P t (β j)) =
      (1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1
        (fun _ => l) (centeredComplexLp Q (F l)) := by
  intro F
  simp only [gaussianDerivativeAverage_one_centered]
  apply endpointPairing_ext Q
  intro g
  rw [unforced_gaussian_flux_pairing hd hP hβ ha]
  simp only [map_smul, map_sum, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, smul_eq_mul]
  norm_num [Complex.real_smul, F]

end EinsteinFull.UnitInitialization
