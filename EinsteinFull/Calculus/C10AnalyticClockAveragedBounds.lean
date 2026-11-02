import Batteries.Tactic.Lint.Basic
import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_clock
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.G3.Proofs.C1ClockAnalyticity
import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/-- The canonical shared flux equals any weak flux of the clock endpoint.
This identifies the witnesses in the forced decay input without dividing by force. -/
private theorem c10_clock_flux_unique {d : ℕ} (hd : 2 ≤ d) {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (μ : Lp ℂ 2 (reducedLaw Q))
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (ζ : ℂ) (r : ℝ≥0) (hr : 0 < r)
    (G J : Fin d → Lp ℂ 2 (reducedLaw Q))
    (h : IsEndpointWeakFlux hd Q (.inr false) ζ a
      (clockEndpoint Q ζ (P ζ) μ r) G J) :
    J = fun j => ζ • ClockAnalyticity.flux Q (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) j := by
  have hc := (ClockAnalyticity.sharedWeakFlux hd a ha hP μ ζ r hr).2
  have hg := h.1.unique hc.1
  funext j
  apply Lp.ext
  exact (h.2 j).trans (by simpa only [hg] using (hc.2 j).symm)

/-- The literal averaged endpoint and flux retain their force factors, including
at zero. These are the identities used in the supervisor target. -/
private theorem c10_clock_average_factors {d : ℕ} (hd : 2 ≤ d) {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (s : ℝ) (hs : 0 < s)
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q)) (r : ℝ≥0)
    (J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q)) :
    gaussianAverage hd Q s hs (clockEndpoint Q 0 (P 0) μ r) = 0 ∧
    (∀ j, gaussianAverage hd Q s hs (centeredComplexLp Q ((0 : ℂ) • J 0 r j)) = 0) ∧
    (∀ ζ, gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r) =
      ζ • gaussianAverage hd Q s hs (centeredComplexLp Q (P ζ r μ))) ∧
    (∀ ζ j, gaussianAverage hd Q s hs (centeredComplexLp Q (ζ • J ζ r j)) =
      ζ • gaussianAverage hd Q s hs (centeredComplexLp Q (J ζ r j))) := by
  have hsmul (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
      gaussianAverage hd Q s hs (ζ • f) = ζ • gaussianAverage hd Q s hs f :=
    map_smul (homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0) ζ f
  have hzero : gaussianAverage hd Q s hs 0 = 0 :=
    map_zero (homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0)
  have hcenter (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
      centeredComplexLp Q (ζ • f) = ζ • centeredComplexLp Q f := by
    simpa only [centeredComplexLpCLM_apply] using (centeredComplexLpCLM Q).map_smul ζ f
  refine ⟨?_, ?_, fun ζ => hsmul ζ _, fun ζ j => ?_⟩
  · simp only [clockEndpoint, zero_smul, hzero]
  · intro j
    rw [hcenter, zero_smul, hzero]
  · rw [hcenter, hsmul]

/-- Forced-flux decay applies to the literal force times the canonical clock
flux. All constants precede the law, with no division by a possibly zero force. -/
private theorem c10_clock_flux_decay
    (h1 : node_l_u3A_forced_u2D_fluxStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε η growth₀ t₀ C₀ : ℝ, ∃ L₀ : ℕ,
      0 < ε ∧ 0 < η ∧ 0 < growth₀ ∧ 1 ≤ t₀ ∧ 0 < C₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
    ∀ (ζ : ℂ) (r : ℝ≥0), t₀ ≤ (r : ℝ) →
      ‖ζ‖ * Real.sqrt (r : ℝ) ≤ (r : ℝ) ^ η →
    ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
      ‖clockEndpoint Q ζ (P ζ) μ (r / 8)‖ ≤
        K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 8) *
          (((r : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * ((r : ℝ) / 8) ^ (-(d : ℝ) / 4)) →
    ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
      Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
        (centeredComplexLp Q
          (ζ • ClockAnalyticity.flux Q (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) j))‖ ^ 2) ≤
        C₀ * K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 2) *
          (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (1 + (r : ℝ) / s) ^ L₀ := by
  obtain ⟨ε, η, L, hε, hη, hrest⟩ := h1 d hd D
  obtain ⟨growth₀, t₀, Cder, hgrowth, ht₀, hCder, hflux, _⟩ := hrest 2 (by norm_num)
  refine ⟨ε, η, growth₀, t₀, Cder 0, L 0, hε, hη, hgrowth, ht₀, hCder 0, ?_⟩
  intro Q hQ β a μ hβ ha hμ P hP ζ r hr hζ growth K hg hK hbound s hs hspos
  let Pdag := fun t => complexL2Transpose (reducedLaw Q) (P ζ t)
  obtain ⟨G, J, hweak, hdecay⟩ := hflux Q hQ β a μ hβ ha hμ ζ (P ζ) Pdag (hP ζ)
    (isComplexTransposeSemigroup_complexL2Transpose Q (P ζ)) (.inr false)
  have hrpos : 0 < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one (ht₀.trans hr))
  have heq := c10_clock_flux_unique hd Q a ha μ P hP ζ r hrpos (G r) (J r)
    (hweak r hrpos)
  have hnorm : (eLpNorm
      (indexedEndpoint hd Q (.inr false) ζ (P ζ) Pdag β a μ (r / 8) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
      K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 8) *
        (((r : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * ((r : ℝ) / 8) ^ (-(d : ℝ) / 4)) := by
    simpa only [indexedEndpoint, ENNReal.ofReal_ofNat, ← Lp.norm_def] using hbound
  have hmem : MemLp
      (indexedEndpoint hd Q (.inr false) ζ (P ζ) Pdag β a μ (r / 8) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q) := by
    rw [ENNReal.ofReal_ofNat]
    exact Lp.memLp _
  have hb := (hdecay r hr hζ growth K hg hK hmem hnorm s hs hspos 0
    (fun j => Fin.elim0 j)).2
  rw [heq] at hb
  simpa only [gaussianDerivativeAverage, iteratedFDeriv_zero_apply, gaussianAverage,
    ← homogenizedGaussianKernel_neg_force, neg_zero, ENNReal.ofReal_ofNat,
    ← Lp.norm_def, Nat.cast_zero, zero_div, sub_zero] using hb

/-- The two root estimates require a drift observation even in the clock
case. Construct that observation from the actual smooth reduced coefficient. -/
private theorem c10_exists_drift {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    ∃ β : Fin d → Lp ℂ 2 (reducedLaw Q), IsReducedDriftObservation Q hQ β := by
  letI := reducedLaw_probability Q
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hunit (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
    change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  have hentry {ω : FieldPair d} (hω : IsSmoothWithBounds M ω) (l j k : Fin d) :
      |coordinateDerivative l (fun x => ω.1 x j k) 0| ≤ M 1 := by
    obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hω.2 1 (by norm_num)
    have hb := hA 0 (fun _ => unitVector l) (unitVector k)
    simp only [iteratedFDeriv_one_apply, hunit, Finset.prod_const_one, mul_one] at hb
    have hc := Regeneration.coordinate_abs_le_euclideanNorm
      (Matrix.mulVec (fun j k => fderiv ℝ (fun x => ω.1 x j k) 0 (unitVector l))
        (unitVector k)) j
    have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
      change dotProduct (fun m => N j m) (Pi.single k 1) = _
      rw [dotProduct_single, mul_one]
    erw [he] at hc
    exact (hc.trans hb).trans (by linarith)
  let F (j k : Fin d) (ω : FieldPair d) : C(Vec d, ℝ) :=
    ⟨fun x => ω.1 x j k,
      (continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)⟩
  have hFm (j k : Fin d) : @Measurable (FieldPair d) C(Vec d, ℝ)
      inferInstance (borel _) (F j k) := by
    apply measurable_continuousMap_of_evaluations
    intro x
    have heval : Continuous (fun ω : FieldPair d => ω.1 x) :=
      (continuous_eval_const x).comp continuous_fst
    exact ((continuous_apply k).comp ((continuous_apply j).comp heval)).measurable
  let b (i : Fin d) (ω : FieldPair d) : ℂ :=
    ((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (fun x => ω.1 x j i) 0 : ℝ)
  have hm (i : Fin d) : Measurable (b i) :=
    Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
      Sharpness.measurable_coordinateDerivative_of_measurable_continuousMap
        (F j i) (hFm j i) j 0).const_mul (1 / 2 : ℝ))
  have hmem (i : Fin d) : MemLp (b i) 2 (reducedLaw Q) := by
    apply MemLp.of_bound (hm i).aestronglyMeasurable ((d : ℝ) * M 1)
    filter_upwards [hM Q hQ] with ω hω
    dsimp only [b]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hb : |∑ j, coordinateDerivative j (fun x => ω.1 x j i) 0| ≤ (d : ℝ) * M 1 :=
      (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hentry hω j j i))
    nlinarith [abs_nonneg (∑ j, coordinateDerivative j (fun x => ω.1 x j i) 0)]
  exact ⟨fun i => (hmem i).toLp (b i), fun i => MemLp.coeFn_toLp (hmem i)⟩

/-- The scalar dependency supplies both the input-size premise for forced
flux decay and the actual averaged clock estimate, using genuine observations. -/
private theorem c10_clock_scalar_decay
    (h2 : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ η C Dp t₀ : ℝ, 0 < η ∧ 0 < C ∧ 0 < Dp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
      (∀ (ζ : ℂ) (r : ℝ≥0), 1 ≤ (r : ℝ) → ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 2 →
        ‖clockEndpoint Q ζ (P ζ) μ r‖ ≤ C * (r : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4))) ∧
      (∀ (ζ : ℂ) (r : ℝ≥0), t₀ ≤ (r : ℝ) → ‖ζ‖ ≤ 1 →
        ‖ζ‖ * Real.sqrt (r : ℝ) ≤ (r : ℝ) ^ η →
        ∀ (s : ℝ), (r : ℝ) ≤ s → ∀ hs : 0 < s,
          ‖gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r)‖ ≤
            C * Real.exp (Dp * ‖ζ‖ ^ 2 * (r : ℝ)) *
              (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))) := by
  obtain ⟨a₀, η, ha₀, ha₁, hη, hrest⟩ := h2 d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, hDp, ht₀, _, hscalar⟩ := hrest 2 (by norm_num)
  refine ⟨η, C, Dp, t₀, hη, hC, hDp, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP
  obtain ⟨β, hβ⟩ := c10_exists_drift D Q hQ
  have hbound (ζ : ℂ) := hscalar Q hQ β a μ hβ ha hμ ζ (P ζ)
    (fun t => complexL2Transpose (reducedLaw Q) (P ζ t)) (hP ζ)
    (isComplexTransposeSemigroup_complexL2Transpose Q (P ζ))
  constructor
  · intro ζ r hr hζ
    have hb := ((hbound ζ).1 r hr hζ).2
    have hn₀ := ENNReal.toReal_nonneg (a := eLpNorm
      (transposeEndpoint Q ⟨0, by omega⟩
        (fun t => complexL2Transpose (reducedLaw Q) (P ζ t)) β r : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q))
    have hn₁ : 0 ≤ ∑ j : Fin d, (eLpNorm
        (velocityEndpoint Q ⟨0, by omega⟩ j ζ (P ζ) β a r : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal :=
      Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    have hc : (eLpNorm (clockEndpoint Q ζ (P ζ) μ r : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
        C * (r : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) := by linarith only [hb, hn₀, hn₁]
    simpa only [ENNReal.ofReal_ofNat, ← Lp.norm_def] using hc
  · intro ζ r hr hζ hscale s hrs hs
    have hmem : clockEndpoint Q ζ (P ζ) μ r ∈
        endpointCollection Q ⟨0, by omega⟩ ζ (P ζ)
          (fun t => complexL2Transpose (reducedLaw Q) (P ζ t)) β a μ r :=
      Or.inr rfl
    have has : a₀ * (r : ℝ) ≤ s :=
      (mul_le_of_le_one_left r.coe_nonneg ha₁.le).trans hrs
    have hb := (((hbound ζ).2 r hr hζ hscale _ hmem).2.1 s has hs).2
    simpa only [ENNReal.ofReal_ofNat, ← Lp.norm_def] using hb

private theorem c10_force_bound (r m : ℝ) (hr : 0 < r)
    (h : m * Real.sqrt r ≤ 2) : m ≤ 2 * r ^ (-1 / 2 : ℝ) := by
  have he : Real.sqrt r * r ^ (-1 / 2 : ℝ) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hr]
    norm_num
  calc
    m = (m * Real.sqrt r) * r ^ (-1 / 2 : ℝ) := by rw [mul_assoc, he, mul_one]
    _ ≤ 2 * r ^ (-1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hr.le _)

private theorem c10_scalar_absorption (d : ℕ) (r s m : ℝ)
    (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s)
    (hforce : m * Real.sqrt r ≤ 2) :
    s ^ (-(1 / 2 + (d : ℝ) / 4)) + m * s ^ (-(d : ℝ) / 4) ≤
      3 * r ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
  have hsplit : s ^ (-(1 / 2 + (d : ℝ) / 4)) =
      s ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hhalf := Real.rpow_le_rpow_of_nonpos hr hrs (show (-1 / 2 : ℝ) ≤ 0 by norm_num)
  have hm' := c10_force_bound r m hr hforce
  rw [hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hhalf (Real.rpow_nonneg hs.le (-(d : ℝ) / 4)),
    mul_le_mul_of_nonneg_right hm' (Real.rpow_nonneg hs.le (-(d : ℝ) / 4))]

/-- Averaged bounds for the actual clock and the same shared weak flux.
The exact dependency interface retains `h0`; the bounds use the flux and scalar inputs. -/
@[nolint unusedArguments]
theorem analytic_clock_averaged_bounds_of_deps
  (h0 : EinsteinFull.Blueprint.node_stationary_u2D_analytic_u2D_semigroupStmt)
  (h1 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_fluxStmt)
  (h2 : EinsteinFull.Blueprint.node_p_u3A_scalarStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε : ℝ, 0 < ε ∧ ∀ (p B : ℝ) (hp : 2 ≤ p), 2 ≤ B →
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩

    ∃ C t₀ : ℝ, ∃ N : ℕ, 0 < C ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
    ∃ G J : ℂ → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ (r : ℝ≥0), 0 < (r : ℝ) →
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (centeredComplexLp Q (P ζ r μ)) (G ζ r) (J ζ r) ∧
        IsEndpointWeakFlux hd Q (.inr false) ζ a
          (clockEndpoint Q ζ (P ζ) μ r)
          (fun j => ζ • G ζ r j) (fun j => ζ • J ζ r j)) ∧
      ∀ (r : ℝ≥0), t₀ ≤ (r : ℝ) →
        ∀ (s : ℝ) (hs : 0 < s), 2 * (r : ℝ) ≤ s →
          let W := fun ζ => centeredComplexLp Q (P ζ r μ)
          let U := fun ζ => gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r)
          let V := fun ζ j => gaussianAverage hd Q s hs
            (centeredComplexLp Q (ζ • J ζ r j))
          U 0 = 0 ∧ (∀ j, V 0 j = 0) ∧
          (∀ ζ, U ζ = ζ • gaussianAverage hd Q s hs (W ζ)) ∧
          (∀ ζ j, V ζ j = ζ • gaussianAverage hd Q s hs
            (centeredComplexLp Q (J ζ r j))) ∧
          ∀ ζ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 2 →
            ‖U ζ‖ ≤ C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) ∧
            Real.sqrt (∑ j : Fin d, ‖V ζ j‖ ^ 2) ≤
              C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) := by
  classical
  intro d hd D
  obtain ⟨ε, ηf, growth, tf, Cf, L, hε, hηf, hgrowth, htf, hCf, hflux⟩ :=
    c10_clock_flux_decay h1 d hd D
  obtain ⟨ηs, Cs, Dp, ts, hηs, hCs, hDp, hts, hscalar⟩ :=
    c10_clock_scalar_decay h2 d hd D
  obtain ⟨Rf, hRf⟩ := (eventually_atTop.1
    ((tendsto_rpow_atTop hηf).eventually (eventually_ge_atTop (2 : ℝ))))
  obtain ⟨Rs, hRs⟩ := (eventually_atTop.1
    ((tendsto_rpow_atTop hηs).eventually (eventually_ge_atTop (2 : ℝ))))
  refine ⟨ε, hε, ?_⟩
  intro p B hp hB
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let T := max 8 (max tf (max ts (max Rf Rs)))
  let K := max 1 Cs
  let Cu := 3 * Cs * Real.exp (4 * Dp)
  let Cv := Cf * K * Real.exp (2 * growth) * (3 / 2 : ℝ) ^ L
  have hK : 1 ≤ K := le_max_left _ _
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hCu : 0 < Cu := by dsimp only [Cu]; positivity
  have hCv : 0 < Cv := by dsimp only [Cv]; positivity
  have hT8 : 8 ≤ T := le_max_left _ _
  have hTf : tf ≤ T := (le_max_left _ _).trans (le_max_right _ _)
  have hTs : ts ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hTRf : Rf ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hTRs : Rs ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨Cu + Cv, T, 0, add_pos hCu hCv, by linarith only [hT8], ?_⟩
  intro Q hQ a μ ha hμ P hP
  let G := ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ
  let J := fun ζ r => ClockAnalyticity.flux Q (G ζ r)
  refine ⟨G, J, ?_, ?_⟩
  · intro ζ r hr
    exact ClockAnalyticity.sharedWeakFlux hd a ha hP μ ζ r hr
  · intro r hr s hs hrs
    dsimp only
    obtain ⟨hu0, hv0, hufactor, hvfactor⟩ := c10_clock_average_factors hd Q s hs P μ r J
    refine ⟨hu0, hv0, hufactor, hvfactor, ?_⟩
    intro ζ hforce
    have hr8 : 8 ≤ (r : ℝ) := hT8.trans hr
    have hrpos : 0 < (r : ℝ) := by linarith only [hr8]
    have hr1 : 1 ≤ (r : ℝ) := by linarith only [hr8]
    have hrs' : (r : ℝ) ≤ s := by linarith only [hrs, hr8]
    have hs1 : 1 ≤ s := hr1.trans hrs'
    have hsqrt : 2 ≤ Real.sqrt (r : ℝ) := by
      nlinarith [Real.sq_sqrt r.coe_nonneg, Real.sqrt_nonneg (r : ℝ)]
    have hζ1 : ‖ζ‖ ≤ 1 := by
      nlinarith [mul_le_mul_of_nonneg_left hsqrt (norm_nonneg ζ)]
    have hζsq : ‖ζ‖ ^ 2 * (r : ℝ) ≤ 4 := by
      have hsq : (‖ζ‖ * Real.sqrt (r : ℝ)) ^ 2 ≤ 4 := by
        nlinarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg (r : ℝ))]
      simpa only [mul_pow, Real.sq_sqrt r.coe_nonneg] using hsq
    have hfscale := hforce.trans (hRf _ (hTRf.trans hr))
    have hsscale := hforce.trans (hRs _ (hTRs.trans hr))
    obtain ⟨hscalar₀, hscalaravg⟩ := hscalar Q hQ a μ ha hμ P hP
    have hu := hscalaravg ζ r (hTs.trans hr) hζ1 hsscale s hrs' hs
    have hExpU : Real.exp (Dp * ‖ζ‖ ^ 2 * (r : ℝ)) ≤ Real.exp (4 * Dp) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hζsq hDp.le]
    have hAbs := c10_scalar_absorption d (r : ℝ) s ‖ζ‖ hrpos hs hrs' hforce
    have hu' : ‖gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r)‖ ≤
        Cu * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) := by
      calc
        _ ≤ Cs * Real.exp (Dp * ‖ζ‖ ^ 2 * (r : ℝ)) *
            (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) := hu
        _ ≤ Cs * Real.exp (4 * Dp) *
            (3 * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4)) := by
          gcongr
        _ = _ := by dsimp only [Cu]; ring
    have hrsmall : 1 ≤ ((r / 8 : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith only [hr8]
    have hsmall : ‖ζ‖ * Real.sqrt ((r / 8 : ℝ≥0) : ℝ) ≤ 2 := by
      apply le_trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg ζ)) hforce
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith only [hr8]
    have hsmallbound := hscalar₀ ζ (r / 8) hrsmall hsmall
    have hExp1 : 1 ≤ Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 8) :=
      Real.one_le_exp (by positivity)
    have hfac : Cs ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 8) :=
      (le_max_right _ _).trans (le_mul_of_one_le_right hKpos.le hExp1)
    have hinput : ‖clockEndpoint Q ζ (P ζ) μ (r / 8)‖ ≤
        K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 8) *
          (((r : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * ((r : ℝ) / 8) ^ (-(d : ℝ) / 4)) := by
      apply hsmallbound.trans
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      exact mul_le_mul hfac (le_add_of_nonneg_right (by positivity))
        (by positivity) (by positivity)
    obtain ⟨β, hβ⟩ := c10_exists_drift D Q hQ
    have hv := hflux Q hQ β a μ hβ ha hμ P hP ζ r (hTf.trans hr) hfscale
      growth K le_rfl hK hinput s hs1 hs
    have hExpV : Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 2) ≤ Real.exp (2 * growth) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_le_mul_of_nonneg_left hζsq hgrowth.le]
    have hratio : 1 + (r : ℝ) / s ≤ (3 / 2 : ℝ) := by
      have h := (div_le_iff₀ hs).mpr (show (r : ℝ) ≤ 1 / 2 * s by linarith only [hrs])
      linarith only [h]
    have hv' : Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
        (centeredComplexLp Q (ζ • J ζ r j))‖ ^ 2) ≤
        Cv * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) := by
      calc
        _ ≤ Cf * K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ) / 2) *
            (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) *
              (1 + (r : ℝ) / s) ^ L := hv
        _ ≤ Cf * K * Real.exp (2 * growth) *
            (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (3 / 2 : ℝ) ^ L := by
          gcongr
        _ = _ := by dsimp only [Cv]; ring
    constructor
    · exact hu'.trans (by gcongr; exact le_add_of_nonneg_right hCv.le)
    · exact hv'.trans (by gcongr; exact le_add_of_nonneg_left hCu.le)
end EinsteinFull.Blueprint
