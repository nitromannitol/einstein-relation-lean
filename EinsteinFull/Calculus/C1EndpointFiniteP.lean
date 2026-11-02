import EinsteinFull.Calculus.C1EndpointsV2Support
import EinsteinFull.Calculus.ComplexEndpointAnalyticSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations

/-! Finite-p assembly of actual endpoint families. -/
open MeasureTheory
open scoped ENNReal NNReal Topology
noncomputable section

namespace EinsteinFull.EndpointFiniteP
open EinsteinRelation EinsteinFull.Blueprint

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Centering on the actual finite-p quotient is complex linear. -/
def center : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  ContinuousLinearMap.id ℂ _ - EndpointProjection.projectionCLM (m := ⊥)

/-- The representative is the literal subtraction of its expectation. -/
theorem center_ae (f : Lp ℂ p μ) :
    (center f : Ω → ℂ) =ᵐ[μ] fun ω => f ω - ∫ η, f η ∂μ := by
  exact (Lp.coeFn_sub _ _).trans
    ((Filter.EventuallyEq.rfl.sub (EndpointProjection.project_ae f)).trans
      (Filter.Eventually.of_forall fun ω => by rw [condExp_bot]; rfl))

/-- Centering costs at most a factor two. -/
theorem norm_center_le (f : Lp ℂ p μ) : ‖center f‖ ≤ 2 * ‖f‖ := by
  exact (norm_sub_le _ _).trans (by
    have h := EndpointProjection.norm_project_le (m := ⊥) f
    change ‖f‖ + ‖EndpointProjection.project (m := ⊥) f‖ ≤ 2 * ‖f‖
    linarith)

private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Finite-p centering agrees with the frozen L2 centering under AE identification. -/
theorem center_ae_l2 {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ p (reducedLaw Q)) (g : Lp ℂ 2 (reducedLaw Q))
    (h : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] g) :
    (center f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] centeredComplexLp Q g := by
  apply (center_ae f).trans
  rw [integral_congr_ae h]
  exact (h.sub (Filter.EventuallyEq.rfl)).trans
    (((Lp.coeFn_sub _ _).trans
      ((Filter.EventuallyEq.rfl).sub (Lp.coeFn_const 2 (reducedLaw Q) _))).symm)

omit [Fact (1 ≤ p)] in
/-- A semigroup witness has its norm bounded by the actual input norm. -/
private theorem norm_rep_le {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {C : ℝ} (hC : 0 ≤ C) (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f p (reducedLaw Q)) (u : Lp ℂ p (reducedLaw Q))
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q] g)
    (hb : eLpNorm g p (reducedLaw Q) ≤ ENNReal.ofReal C * eLpNorm f p (reducedLaw Q)) :
    ‖u‖ ≤ C * (eLpNorm f p (reducedLaw Q)).toReal := by
  rw [Lp.norm_def, eLpNorm_congr_ae hu]
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top) hb
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using h

/-- Fixed-datum finite-p holomorphy assembles the actual force-dependent
velocity, clock and transpose endpoints, for arbitrary valid P/Pdag.
The estimate retains the literal input norms. -/
private theorem exists_representatives_of_memLp
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (q : ℝ) (hq : 2 ≤ q) (T R : ℝ) (hT : 0 ≤ T) (hR : 0 < R) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ₀ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
      (∀ j, MemLp (β j) (ENNReal.ofReal q) (reducedLaw Q)) →
      (∀ j k, MemLp (a j k) (ENNReal.ofReal q) (reducedLaw Q)) →
      MemLp μ₀ (ENNReal.ofReal q) (reducedLaw Q) →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ z, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ z (P z)) →
      (∀ z, IsComplexTransposeSemigroup Q (P z) (Pdag z)) →
    ∀ (ν : EndpointIndex d) (t : ℝ≥0), (t : ℝ) ≤ T →
    ∃ E : ℂ → Lp ℂ (ENNReal.ofReal q) (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (P z) (Pdag z) β a μ₀ t) ∧
      (∀ z, AnalyticAt ℂ E z) ∧
      (∀ z, (∫ ω, E z ω ∂reducedLaw Q) = 0) ∧
      (∀ z, ‖z‖ ≤ R → ‖E z‖ ≤ C *
        (1 + R) * ((∑ j, (eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q)).toReal) +
          (∑ j, ∑ k, (eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)).toReal) +
          (eLpNorm μ₀ (ENNReal.ofReal q) (reducedLaw Q)).toReal)) := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨C, hC, hb⟩ := (hA d hd D).2 q R (T + 1) hq hR (by linarith)
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q hQ β a μ₀ hβ hβp hap hμp P Pdag hP hPdag ν t ht
  have hPF (z : ℂ) := (hP z).eq_forcedComplexEvolution
  have hPG (z : ℂ) : Pdag z = fun s =>
      complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q ⟨0, by omega⟩ z s) := by
    rw [(hPdag z).eq_complexL2Transpose, hPF z]
  have htime : (t : ℝ) ≤ T + 1 := by linarith
  have fixed (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal q) (reducedLaw Q)) :
      ∃ u v : ℂ → Lp ℂ (ENNReal.ofReal q) (reducedLaw Q),
        (∀ z, (u z : FieldPair d → ℂ) =ᵐ[reducedLaw Q] P z t f ∧
          (v z : FieldPair d → ℂ) =ᵐ[reducedLaw Q] Pdag z t f) ∧
        (∀ z, AnalyticAt ℂ u z ∧ AnalyticAt ℂ v z) ∧
        (∀ z, ‖z‖ ≤ R → ‖u z‖ ≤ C * (eLpNorm f (ENNReal.ofReal q) (reducedLaw Q)).toReal ∧
          ‖v z‖ ≤ C * (eLpNorm f (ENNReal.ofReal q) (reducedLaw Q)).toReal) := by
    obtain ⟨bounds, u, v, huv, han⟩ := hb Q hQ f hf t htime
    refine ⟨u, v, ?_, han, ?_⟩
    · intro z
      simpa only [hPF z, hPG z] using huv z
    · intro z hz
      have h := bounds z hz
      constructor
      · exact norm_rep_le Q hC.le f _ hf _ (huv z).1 h.2.2.1
      · exact norm_rep_le Q hC.le f _ hf _ (huv z).2 h.2.2.2
  let S := (∑ j, (eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q)).toReal) +
    (∑ j, ∑ k, (eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)).toReal) +
    (eLpNorm μ₀ (ENNReal.ofReal q) (reducedLaw Q)).toReal
  have hβS (j : Fin d) : (eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ S := by
    have h := Finset.single_le_sum (f := fun j =>
      (eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q)).toReal)
      (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
    dsimp only [S]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
        ENNReal.toReal_nonneg (a := eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)))),
      ENNReal.toReal_nonneg (a := eLpNorm μ₀ (ENNReal.ofReal q) (reducedLaw Q))]
  have haS (j k : Fin d) : (eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ S := by
    have h₁ := Finset.single_le_sum (f := fun k =>
      (eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)).toReal)
      (fun k _ => ENNReal.toReal_nonneg) (Finset.mem_univ k)
    have h₂ := Finset.single_le_sum (f := fun j => ∑ k,
      (eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q)).toReal)
      (fun j _ => Finset.sum_nonneg (fun k _ => ENNReal.toReal_nonneg)) (Finset.mem_univ j)
    dsimp only [S]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      ENNReal.toReal_nonneg (a := eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q))),
      ENNReal.toReal_nonneg (a := eLpNorm μ₀ (ENNReal.ofReal q) (reducedLaw Q))]
  have hμS : (eLpNorm μ₀ (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ S := by
    dsimp only [S]
    linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
      ENNReal.toReal_nonneg (a := eLpNorm (β j) (ENNReal.ofReal q) (reducedLaw Q))),
      Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) =>
        Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
          ENNReal.toReal_nonneg (a := eLpNorm (a j k) (ENNReal.ofReal q) (reducedLaw Q))))]
  have hS : 0 ≤ S := le_trans ENNReal.toReal_nonneg hμS
  have finish (E : ℂ → Lp ℂ (ENNReal.ofReal q) (reducedLaw Q))
      (he : ∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (P z) (Pdag z) β a μ₀ t)
      (han : ∀ z, AnalyticAt ℂ E z)
      (hn : ∀ z, ‖z‖ ≤ R → ‖E z‖ ≤ 2 * C * (1 + R) * S) :
      ∃ E : ℂ → Lp ℂ (ENNReal.ofReal q) (reducedLaw Q),
        (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          indexedEndpoint hd Q ν z (P z) (Pdag z) β a μ₀ t) ∧
        (∀ z, AnalyticAt ℂ E z) ∧
        (∀ z, (∫ ω, E z ω ∂reducedLaw Q) = 0) ∧
        (∀ z, ‖z‖ ≤ R → ‖E z‖ ≤ 2 * C * (1 + R) * S) := by
    refine ⟨E, he, han, ?_, hn⟩
    intro z
    rw [integral_congr_ae (he z)]
    exact centeredEquations_endpoint_mean_zero hd hβ a μ₀ (hP z) (hPdag z) ν t
  rcases ν with j | b
  · obtain ⟨u, v, huv, huan, hun⟩ := fixed (β j) (hβp j)
    obtain ⟨w, x, hwx, hwan, hwn⟩ := fixed (a ⟨0, by omega⟩ j) (hap _ j)
    apply finish (fun z => center (u z + z • w z))
    · intro z
      apply center_ae_l2 Q
      exact ((Lp.coeFn_add _ _).trans ((huv z).1.add
        ((Lp.coeFn_smul z _).trans ((hwx z).1.const_smul z)))).trans (by
          rw [map_add, map_smul]
          exact ((Filter.EventuallyEq.rfl.add (Lp.coeFn_smul z _).symm)).trans
            (Lp.coeFn_add _ _).symm)
    · intro z
      exact (center.analyticAt _).comp ((huan z).1.add
        (analyticAt_id.fun_smul (hwan z).1))
    · intro z hz
      have h₁ := (hun z hz).1
      have h₂ := (hwn z hz).1
      have hn := norm_center_le (u z + z • w z)
      have ha := norm_add_le (u z) (z • w z)
      rw [norm_smul] at ha
      have hh₁ := mul_le_mul_of_nonneg_left (hβS j) hC.le
      have hh₂ := mul_le_mul_of_nonneg_left (haS ⟨0, by omega⟩ j) hC.le
      have hz₁ := mul_le_mul hz (h₂.trans hh₂) (norm_nonneg _) hR.le
      nlinarith
  · cases b
    · obtain ⟨u, v, huv, huan, hun⟩ := fixed μ₀ hμp
      apply finish (fun z => z • center (u z))
      · intro z
        exact (Lp.coeFn_smul z _).trans
          (((center_ae_l2 Q _ _ (huv z).1).const_smul z).trans
          (Lp.coeFn_smul z _).symm)
      · intro z
        exact analyticAt_id.fun_smul ((center.analyticAt _).comp (huan z).1)
      · intro z hz
        rw [norm_smul]
        have hn := norm_center_le (u z)
        have hu := (hun z hz).1
        have hμ := mul_le_mul_of_nonneg_left hμS hC.le
        have hz₁ := mul_le_mul hz (hn.trans (mul_le_mul_of_nonneg_left (hu.trans hμ)
          (by norm_num : (0 : ℝ) ≤ 2))) (norm_nonneg _) hR.le
        nlinarith
    · obtain ⟨u, v, huv, huan, hun⟩ := fixed (β ⟨0, by omega⟩) (hβp _)
      apply finish v (fun z => (huv z).2) (fun z => (huan z).2)
      intro z hz
      have hn := (hun z hz).2
      have hβ := mul_le_mul_of_nonneg_left (hβS ⟨0, by omega⟩) hC.le
      calc
        _ ≤ C * S := hn.trans hβ
        _ ≤ 2 * C * (1 + R) * S := by
          nlinarith [mul_nonneg hC.le hS, mul_nonneg hR.le (mul_nonneg hC.le hS)]


private lemma euclidean_unit {d : ℕ} (j : Fin d) : euclideanNorm (unitVector j) = 1 := by
  change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem derivative_entry_bound {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hω : IsSmoothWithBounds M ω) (l j k : Fin d) :
    |coordinateDerivative l (fun x => ω.1 x j k) 0| ≤ M 1 := by
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hω.2 1 (by norm_num)
  have hb := hA 0 (fun _ => unitVector l) (unitVector k)
  simp only [iteratedFDeriv_one_apply, euclidean_unit, Finset.prod_const_one, mul_one] at hb
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => fderiv ℝ (fun x => ω.1 x j k) 0 (unitVector l))
      (unitVector k)) j
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun m => N j m) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  exact (hc.trans hb).trans (by linarith)

/-- A single structural bound controls the literal observations, before their law
and L2 witnesses are chosen. -/
theorem observation_bounds (d : ℕ) (D : StructuralData d) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ₀ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ₀ →
      (∀ j, ∀ᵐ ω ∂reducedLaw Q, ‖β j ω‖ ≤ K) ∧
      (∀ j k, ∀ᵐ ω ∂reducedLaw Q, ‖a j k ω‖ ≤ K) ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖μ₀ ω‖ ≤ K) := by
  obtain ⟨M, hM, hs⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  let K := 1 + (d : ℝ) * M 1 + L
  have hM₁ := hM 1 (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro Q hQ β a μ₀ hβ ha hμ
  have hLK : L ≤ K := by
    dsimp only [K]
    linarith [mul_nonneg (Nat.cast_nonneg d) hM₁.le]
  refine ⟨?_, ?_, ?_⟩
  · intro j
    filter_upwards [hβ j, hs Q hQ] with ω hβω hω
    rw [hβω, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hh : |∑ k, coordinateDerivative k (fun x => ω.1 x k j) 0| ≤ (d : ℝ) * M 1 := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans (by
        simpa using Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => derivative_entry_bound hω k k j))
    dsimp only [K]
    nlinarith [mul_nonneg (Nat.cast_nonneg d) hM₁.le]
  · intro j k
    filter_upwards [ha j k, (hb d D.dependenceRange Q).2.2] with ω hω hbounds
    rw [hω, Complex.norm_real, Real.norm_eq_abs]
    apply le_trans (b := L) _ hLK
    apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hL) (ω.1 0) (hbounds.1 0).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hL))
        (euclideanSq_nonneg_coords ξ)).trans ((hbounds.1 0).2 ξ).1
    · exact fun ξ => ((hbounds.1 0).2 ξ).2
  · filter_upwards [hμ, (hb d D.dependenceRange Q).2.2] with ω hω hbounds
    rw [hω, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hbounds.2.1 0).1)]
    exact (hbounds.2.1 0).2.trans hLK

/-- The actual endpoints have entire finite-p representatives, zero expectation
and a uniform closed-disc bound on every nonnegative compact time interval.
Constants precede the law, all observation witnesses, evolutions, index and time. -/
theorem exists_representatives
    (hA : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (q : ℝ) (hq : 2 ≤ q) (T B : ℝ) (hT : 0 ≤ T) (hB : 0 < B) :
    letI : Fact (1 ≤ ENNReal.ofReal q) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ₀ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ₀ →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ z, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ z (P z)) →
      (∀ z, IsComplexTransposeSemigroup Q (P z) (Pdag z)) →
    ∀ (ν : EndpointIndex d) (t : ℝ≥0), (t : ℝ) ≤ T →
    ∃ E : ℂ → Lp ℂ (ENNReal.ofReal q) (reducedLaw Q),
      (∀ z, (E z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q ν z (P z) (Pdag z) β a μ₀ t) ∧
      (∀ z, AnalyticAt ℂ E z) ∧
      DifferentiableOn ℂ E {z | ‖z‖ < B + 1} ∧
      (∀ z, (∫ ω, E z ω ∂reducedLaw Q) = 0) ∧
      (∀ z, ‖z‖ ≤ B + 1 → ‖E z‖ ≤ C) := by
  let : Fact (1 ≤ ENNReal.ofReal q) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨K, hK, hob⟩ := observation_bounds d D
  obtain ⟨C, hC, hrep⟩ := exists_representatives_of_memLp hA d hd D q hq T (B + 1) hT (by linarith)
  let S := ((d : ℝ) + (d : ℝ) * d + 1) * K
  refine ⟨max 1 (C * (1 + (B + 1)) * S), le_max_left _ _, ?_⟩
  intro Q hQ β a μ₀ hβ ha hμ P Pdag hP hPdag ν t ht
  obtain ⟨hβb, hab, hμb⟩ := hob Q hQ β a μ₀ hβ ha hμ
  have mem (f : Lp ℂ 2 (reducedLaw Q)) (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
      MemLp f (ENNReal.ofReal q) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp f).aestronglyMeasurable K hf
  have norm (f : Lp ℂ 2 (reducedLaw Q)) (hf : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ K) :
      (eLpNorm f (ENNReal.ofReal q) (reducedLaw Q)).toReal ≤ K :=
    AnnuliSupport.eLpNorm_toReal_le_of_ae_norm_le (Lp.memLp f).aestronglyMeasurable hK.le hf
  obtain ⟨E, he, han, hmean, hn⟩ := hrep Q hQ β a μ₀ hβ
    (fun j => mem _ (hβb j)) (fun j k => mem _ (hab j k)) (mem _ hμb)
    P Pdag hP hPdag ν t ht
  refine ⟨E, he, han, fun z _ => (han z).differentiableAt.differentiableWithinAt, hmean, ?_⟩
  intro z hz
  apply (hn z hz).trans
  apply le_trans (b := C * (1 + (B + 1)) * S) _ (le_max_right _ _)
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (by linarith))
  have h₁ := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => norm (β j) (hβb j))
  have h₂ := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => norm (a j k) (hab j k)))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h₁ h₂
  dsimp only [S]
  nlinarith [norm μ₀ hμb]

end EinsteinFull.EndpointFiniteP
