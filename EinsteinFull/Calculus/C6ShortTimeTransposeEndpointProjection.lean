import EinsteinFull.Calculus.C3EndpointLocalizationSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinFull.Calculus.C2RetainedPhysicalMeasurableEvolution
import EinsteinFull.Calculus.C6GaussianLocalLocalDivergenceTesting
import EinsteinFull.Calculus.C3PhysicalEvolutionJointMeasurability
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinFull.Calculus.C4ComplexCaccioppoliEnergy
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
/- EXACT SUPERVISOR TARGET
theorem endpoint_short_time_transpose_projection_of_graph_deps :
∀ (hA : node_stationary_u2D_analytic_u2D_semigroupStmt) (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → (t : ℝ) ≤ 1 → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2)
-/
/-- The actual drift is measurable from any unit neighborhood of the origin. -/
theorem c6_short_time_initial_drift_local {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ρ : ℝ} (hρ : 1 ≤ ρ) :
    IsComplexLocalObservation Q ρ (β i) := by
  let χ : Vec d → ℝ := fun x => min 1 (max 0 (2 - 2 * euclideanNorm x))
  have hχ : Continuous χ := by
    dsimp only [χ]
    exact continuous_const.min (continuous_const.max
      (continuous_const.sub (continuous_const.mul Entropy.continuous_euclideanNorm')))
  let F (ω : FieldPair d) (j : Fin d) : C(Vec d, ℝ) :=
    ⟨fun x => χ x * ω.1 x j i, hχ.mul ((continuous_apply i).comp ((continuous_apply j).comp ω.1.continuous))⟩
  have hFm (j : Fin d) : @Measurable (FieldPair d) C(Vec d, ℝ)
      (localSigma {x : Vec d | euclideanNorm x < ρ}) (borel _) (fun ω => F ω j) := by
    let : MeasurableSpace (FieldPair d) := localSigma {x : Vec d | euclideanNorm x < ρ}
    apply measurable_continuousMap_of_evaluations
    intro x
    by_cases hx : euclideanNorm x < ρ
    · have hm : Measurable (fun ω : FieldPair d => (ω.1 x, ω.2 x)) := by
        rw [measurable_iff_comap_le]
        exact le_iSup_of_le ⟨x, hx⟩ le_rfl
      exact ((show Continuous (fun A : Mat d => A j i) from
        (continuous_apply i).comp (continuous_apply j)).measurable.comp hm.fst).const_mul (χ x)
    · have hz : χ x = 0 := by
        dsimp only [χ]
        rw [max_eq_left (by linarith : 2 - 2 * euclideanNorm x ≤ 0)]
        norm_num
      simpa only [F, ContinuousMap.coe_mk, hz, zero_mul] using
        (measurable_const : Measurable (fun _ : FieldPair d => (0 : ℝ)))
  have he (ω : FieldPair d) (j : Fin d) :
      coordinateDerivative j (F ω j) 0 = coordinateDerivative j (fun x => ω.1 x j i) 0 := by
    have hn : ∀ᶠ x : Vec d in 𝓝 0, euclideanNorm x < 1 / 2 :=
      (Entropy.continuous_euclideanNorm'.continuousAt.eventually_lt_const (by
        norm_num [euclideanNorm, euclideanSq, dot])).filter_mono le_rfl
    have hh : (fun x => F ω j x) =ᶠ[𝓝 0] (fun x => ω.1 x j i) := by
      filter_upwards [hn] with x hx
      have hxχ : χ x = 1 := by
        dsimp only [χ]
        rw [min_eq_left (le_max_of_le_right (by linarith))]
      simp only [F, ContinuousMap.coe_mk, hxχ, one_mul]
    exact congrArg (fun A => A (unitVector j)) (hh.fderiv_eq (𝕜 := ℝ))
  refine ⟨fun ω => ((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (F ω j) 0 : ℝ), ?_, ?_⟩
  · let : MeasurableSpace (FieldPair d) := localSigma {x : Vec d | euclideanNorm x < ρ}
    exact Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
      Sharpness.measurable_coordinateDerivative_of_measurable_continuousMap
        (fun ω => F ω j) (hFm j) j 0).const_mul (1 / 2 : ℝ))
  · filter_upwards [hβ i] with ω hω
    simp only [he, hω]

/-- At time zero the transpose endpoint is exactly the local drift. -/
theorem c6_short_time_transpose_initial_projection_eq {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ρ : ℝ) (hρ : 1 ≤ ρ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (E : Lp ℂ p (reducedLaw Q))
    (hE : (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ 0) :
    EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E = E := by
  have hloc : IsComplexLocalObservation Q ρ
      (indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ 0) := by
    simpa only [indexedEndpoint, transposeEndpoint, hPdag.zero hP,
      ContinuousLinearMap.id_apply] using
        c6_short_time_initial_drift_local hβ ⟨0, by omega⟩ hρ
  have herr := EndpointLocalization.norm_sub_project_le Q ρ E _ _ hE hloc (le_refl 0)
    (Filter.Eventually.of_forall fun ω => by simp only [sub_self, norm_zero, le_refl])
  have hz : E - EndpointProjection.project
      (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E = 0 :=
    norm_eq_zero.mp (le_antisymm (by simpa only [mul_zero] using herr) (norm_nonneg _))
  exact (sub_eq_zero.mp hz).symm

/-- The unit-time boundary of the short-time transpose estimate follows from
its original graph dependency, with constants chosen before the law and force. -/
theorem c6_short_time_transpose_unit_projection
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) :
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ ρ : ℝ, R ≤ ρ → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)]
      (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ 1 →
      ‖E - EndpointProjection.project
        (m := localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
  obtain ⟨C, c, N, hC, hc, hloc⟩ := hlocal d hd D
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨C, 2 * C * 3 ^ N * Real.exp (C * B ^ 2), c, hC, by positivity, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ρ hρ p _ E hE
  obtain ⟨G, _, happ, _⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag (Sum.inr true)
  obtain ⟨V, _, hV, _, herr, _⟩ := happ 1 (by norm_num)
    ρ (by simpa only [NNReal.coe_one, Real.sqrt_one, mul_one] using hρ)
  let ε := C * 3 ^ N * Real.exp (C * ‖ζ‖ ^ 2 - c * ρ ^ 2)
  have he : ∀ᵐ ω ∂reducedLaw Q,
      ‖indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ 1 ω - V ω‖ ≤ ε := by
    filter_upwards [herr] with ω hω
    have hh := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω
    simpa only [uncenteredEndpoint, indexedEndpoint, NNReal.coe_one,
      mul_one, div_one, show (2 : ℝ) + 1 = 3 by norm_num] using hh
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hp := EndpointLocalization.norm_sub_project_le Q ρ E _ V hE hV hε he
  have hsquare : ‖ζ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hexp : Real.exp (C * ‖ζ‖ ^ 2 - c * ρ ^ 2) ≤
      Real.exp (C * B ^ 2 - c * ρ ^ 2) :=
    Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hsquare hCpos.le) _)
  calc
    _ ≤ 2 * ε := hp
    _ ≤ 2 * (C * 3 ^ N * Real.exp (C * B ^ 2 - c * ρ ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hexp (by positivity)) (by norm_num)
    _ = _ := by
      rw [show C * B ^ 2 - c * ρ ^ 2 = C * B ^ 2 + -c * ρ ^ 2 by ring,
        Real.exp_add]
      ring

/-- Retaining a smooth field leaves a compactly supported coefficient
perturbation, whose actual spatial derivatives are physical square-integrable
initial drift data. The constant exterior matrix differentiates to zero. -/
theorem c6_retained_coefficient_derivative_memLp
    {d : ℕ} (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ 1 χ)
    (hcχ : HasCompactSupport χ) (ω : FieldPair d)
    (hω : IsSmoothFieldPair ω) (i j k : Fin d) :
    MemLp (fun x => (coordinateDerivative k
      (fun y => (EinsteinFull.ForcedLocality.retainedPair χ ω).1 y i j) x : ℂ))
      2 volume := by
  let b : Vec d → ℝ := fun x => χ x * (ω.1 x i j - (1 : Mat d) i j)
  have hb : ContDiff ℝ 1 b :=
    hχ.mul ((hω.1 i j).of_le (by simp) |>.sub contDiff_const)
  have hcb : HasCompactSupport b := hcχ.mul_right
  have hcd : HasCompactSupport (coordinateDerivative k b) :=
    hcb.fderiv_apply ℝ (unitVector k)
  have hcont : Continuous (coordinateDerivative k b) := by
    exact (hb.continuous_fderiv_apply one_ne_zero).comp
      (continuous_id.prodMk continuous_const)
  have hm : MemLp (fun x => (coordinateDerivative k b x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hcont).memLp_of_hasCompactSupport
      (hcd.comp_left (by simp))
  have he : (fun y => (EinsteinFull.ForcedLocality.retainedPair χ ω).1 y i j) =
      fun y => b y + (1 : Mat d) i j := by
    funext y
    simp only [EinsteinFull.ForcedLocality.retainedPair, ContinuousMap.coe_mk,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, b]
    ring
  simpa only [he, coordinateDerivative, fderiv_add_const] using hm

/-- The literal retained transpose datum is in physical L2. Its value agrees
with the original divergence drift throughout the retained open region. -/
theorem c6_retained_transpose_initial_data {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (i : Fin d)
    (U : Set (Vec d)) (hU : IsOpen U) (hinterior : ∀ x ∈ U, χ x = 1) :
    ∃ f : Lp ℂ 2 (volume : Measure (Vec d)),
      ((f : Vec d → ℂ) =ᵐ[volume] fun x =>
        ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ)) ∧
      ∀ᵐ x ∂volume, x ∈ U → f x =
        ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => ω.1 y j i) x : ℝ) := by
  let b : Vec d → ℂ := fun x =>
    ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
      (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ)
  have hb : MemLp b 2 volume := by
    have hs := (memLp_finsetSum Finset.univ (fun j _ =>
      c6_retained_coefficient_derivative_memLp χ hχ hcχ ω hω j i j)).const_mul
        ((1 / 2 : ℝ) : ℂ)
    simpa only [b, Complex.ofReal_mul, Complex.ofReal_sum] using hs
  refine ⟨hb.toLp b, hb.coeFn_toLp, ?_⟩
  filter_upwards [hb.coeFn_toLp] with x hx
  intro hxU
  rw [hx]
  exact congrArg (fun z : ℝ => (z : ℂ))
    (ForcedLocality.retainedPair_drift χ ω hU hinterior hxU i)

/-- Negating a real weak derivative preserves its local integrability. -/
private theorem c6_weak_partial_neg {d : ℕ} {U : Set (Vec d)} {j : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g) :
    HasWeakPartialDerivative U j (fun x => -f x) (fun x => -g x) := by
  refine ⟨h.1.neg, h.2.1.neg, ?_⟩
  intro φ hφ
  simpa only [neg_mul, integral_neg, neg_neg] using congrArg Neg.neg (h.2.2 φ hφ)

/-- Conjugate Gaussian testing for locally H1 functions. Only Gaussian weighted
L2 bounds are required; the unweighted stationary orbit need not be in L2. -/
theorem c6_gaussian_conjugate_divergence_testing
    {d : ℕ} (r : ℝ) (hr : 0 < r)
    (P : Fin d → Vec d → ℂ) (q v : Vec d → ℂ) (H : Fin d → Vec d → ℂ)
    (hdivre : HasWeakDivergence Set.univ (fun x j => (P j x).re) (fun x => (q x).re))
    (hdivim : HasWeakDivergence Set.univ (fun x j => (P j x).im) (fun x => (q x).im))
    (hvre : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (v x).re)
      (fun x => (H j x).re))
    (hvim : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (v x).im)
      (fun x => (H j x).im))
    (hP : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * P j x) 2 volume)
    (hq : MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * q x) 2 volume)
    (hv : MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * v x) 2 volume)
    (hH : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * H j x) 2 volume) :
    (∫ x : Vec d, (Real.exp (-euclideanSq x/r) : ℂ) * q x * star (v x)) =
      -(∫ x : Vec d, ∑ j, P j x *
        ((Real.exp (-euclideanSq x/r) : ℂ) * star (H j x) +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * star (v x))) := by
  apply physical_gaussian_locally_h1_divergence_testing r hr P q
    (fun x => star (v x)) (fun j x => star (H j x)) hdivre hdivim
  · intro j
    simpa only [Complex.star_def, Complex.conj_re] using hvre j
  · intro j
    simpa only [Complex.star_def, Complex.conj_im] using c6_weak_partial_neg (hvim j)
  · exact hP
  · exact hq
  · have hs := hv.star
    change MemLp (fun x => star ((Real.exp (-euclideanSq x/(4*r)) : ℂ) * v x))
      2 volume at hs
    simpa only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] using hs
  · intro j
    have hs := (hH j).star
    change MemLp (fun x => star ((Real.exp (-euclideanSq x/(4*r)) : ℂ) * H j x))
      2 volume at hs
    simpa only [star_mul, Complex.star_def, Complex.conj_ofReal, mul_comm] using hs

/-- Subtract two actual weak equations before conjugate Gaussian testing.
All weak derivatives and weighted L2 bounds are inherited from the two orbits. -/
theorem c6_gaussian_conjugate_defect_testing
    {d : ℕ} (r : ℝ) (hr : 0 < r)
    (P : Bool → Fin d → Vec d → ℂ) (q v : Bool → Vec d → ℂ)
    (H : Bool → Fin d → Vec d → ℂ)
    (hdivre : ∀ n, HasWeakDivergence Set.univ
      (fun x j => (P n j x).re) (fun x => (q n x).re))
    (hdivim : ∀ n, HasWeakDivergence Set.univ
      (fun x j => (P n j x).im) (fun x => (q n x).im))
    (hvre : ∀ n j, HasWeakPartialDerivative Set.univ j
      (fun x => (v n x).re) (fun x => (H n j x).re))
    (hvim : ∀ n j, HasWeakPartialDerivative Set.univ j
      (fun x => (v n x).im) (fun x => (H n j x).im))
    (hP : ∀ n j, MemLp
      (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * P n j x) 2 volume)
    (hq : ∀ n, MemLp
      (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * q n x) 2 volume)
    (hv : ∀ n, MemLp
      (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * v n x) 2 volume)
    (hH : ∀ n j, MemLp
      (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * H n j x) 2 volume) :
    (∫ x : Vec d, (Real.exp (-euclideanSq x/r) : ℂ) *
      (q true x - q false x) * star (v true x - v false x)) =
      -(∫ x : Vec d, ∑ j, (P true j x - P false j x) *
        ((Real.exp (-euclideanSq x/r) : ℂ) * star (H true j x - H false j x) +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) *
            star (v true x - v false x))) := by
  apply c6_gaussian_conjugate_divergence_testing r hr
    (fun j x => P true j x - P false j x)
    (fun x => q true x - q false x) (fun x => v true x - v false x)
    (fun j x => H true j x - H false j x)
  · simpa only [Pi.sub_def, Complex.sub_re] using
      Correctors.hasWeakDivergence_sub (hdivre true) (hdivre false)
  · simpa only [Pi.sub_def, Complex.sub_im] using
      Correctors.hasWeakDivergence_sub (hdivim true) (hdivim false)
  · intro j
    simpa only [Complex.sub_re] using
      Correctors.hasWeakPartialDerivative_sub (hvre true j) (hvre false j)
  · intro j
    simpa only [Complex.sub_im] using
      Correctors.hasWeakPartialDerivative_sub (hvim true j) (hvim false j)
  · intro j
    simpa only [Pi.sub_def, mul_sub] using (hP true j).sub (hP false j)
  · simpa only [Pi.sub_def, mul_sub] using (hq true).sub (hq false)
  · simpa only [Pi.sub_def, mul_sub] using (hv true).sub (hv false)
  · intro j
    simpa only [Pi.sub_def, mul_sub] using (hH true j).sub (hH false j)

/-- Exact transpose flux comparison. The coefficient defect multiplies the
retained solution and its gradient; the force stays inside the divergence. -/
theorem c6_transpose_flux_difference {d : ℕ}
    (a b : Mat d) (i j : Fin d) (ζ u v : ℂ) (Gu Gv : Fin d → ℂ) :
    ((1 / 2 : ℂ) * ∑ k, (a k j : ℂ) * Gu k - ζ * (a j i : ℂ) * u) -
        ((1 / 2 : ℂ) * ∑ k, (b k j : ℂ) * Gv k - ζ * (b j i : ℂ) * v) =
      (1 / 2 : ℂ) * ∑ k, (a k j : ℂ) * (Gu k - Gv k) -
        ζ * (a j i : ℂ) * (u - v) +
        ((1 / 2 : ℂ) * ∑ k, ((a k j - b k j : ℝ) : ℂ) * Gv k -
          ζ * ((a j i - b j i : ℝ) : ℂ) * v) := by
  simp only [Complex.ofReal_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

/-- The actual transpose coefficient defect is supported outside the region
where the original and retained matrices agree. -/
theorem c6_transpose_flux_defect_vanishes {d : ℕ}
    (χ : C(Vec d, ℝ)) (ω : FieldPair d) (x : Vec d) (hχ : χ x = 1)
    (i j : Fin d) (ζ v : ℂ) (Gv : Fin d → ℂ) :
    (1 / 2 : ℂ) * ∑ k,
        ((ω.1 x k j - (ForcedLocality.retainedPair χ ω).1 x k j : ℝ) : ℂ) * Gv k -
      ζ * ((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ) * v = 0 := by
  simp [ForcedLocality.retainedPair, hχ]

/-- The transpose force differentiates the conjugate test. Its additional
cutoff term is absorbed without dividing by the cutoff, which may vanish. -/
theorem c6_transpose_cutoff_coercive {d : ℕ} {A : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (X : Fin d → ℂ) (u : ℂ)
    (D : Fin d → ℝ) (η : ℝ) (i : Fin d) (ζ : ℂ) :
    (-(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ))) +
      ζ * u * (∑ j, (A j i : ℂ) *
        (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ)))).re ≤
      -(Λ⁻¹ / 4) * η ^ 2 * (∑ j, ‖X j‖ ^ 2) +
        10 * Λ ^ 3 * (s5Nrm D ^ 2 + ‖ζ‖ ^ 2 * η ^ 2) * ‖u‖ ^ 2 := by
  let F := ∑ j, (A j i : ℂ) * X j
  let R := ∑ j, D j * A j i
  let M := -(1 / 2 : ℂ) * (∑ j, ∑ k, (A j k : ℂ) * X k *
    (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ)))
  have hbase := complexForced_cutoff_coercive hA X u D η i (star ζ)
  change (M + star ζ * (F * (((η ^ 2 : ℝ) : ℂ) * star u))).re ≤ _ at hbase
  rw [norm_star] at hbase
  have hflux : (∑ j, (A j i : ℂ) *
      (((η ^ 2 : ℝ) : ℂ) * star (X j) + star u * ((2 * η * D j : ℝ) : ℂ))) =
      ((η ^ 2 : ℝ) : ℂ) * star F + (2 * η : ℂ) * star u * (R : ℂ) := by
    simp only [F, R, map_sum, Complex.star_def, map_mul, Complex.conj_ofReal,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    push_cast
    ring
  have hconj : (ζ * u * (((η ^ 2 : ℝ) : ℂ) * star F)).re =
      (star ζ * (F * (((η ^ 2 : ℝ) : ℂ) * star u))).re := by
    calc
      _ = (star (ζ * u * (((η ^ 2 : ℝ) : ℂ) * star F))).re := by
        simp only [Complex.star_def, Complex.conj_re]
      _ = _ := by
        congr 1
        simp only [star_mul, Complex.star_def, Complex.conj_conj, Complex.conj_ofReal]
        ring
  have herr : (ζ * u * ((2 * η : ℂ) * star u * (R : ℂ))).re =
      2 * η * ζ.re * ‖u‖ ^ 2 * R := by
    have he : ζ * u * ((2 * η : ℂ) * star u * (R : ℂ)) =
        ((2 * η * R : ℝ) : ℂ) * ζ * (u * star u) := by push_cast; ring
    rw [he, Complex.star_def, Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  have hR := s5_row_real_le hA i D
  have hL : 0 ≤ Λ := le_trans zero_le_one hA.one_le
  have hsmall : 2 * η * ζ.re * R ≤ Λ * (s5Nrm D ^ 2 + ‖ζ‖ ^ 2 * η ^ 2) := by
    calc
      _ ≤ 2 * |η| * |ζ.re| * |R| := by
        simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using
          le_abs_self (2 * η * ζ.re * R)
      _ ≤ 2 * |η| * ‖ζ‖ * (Λ * s5Nrm D) := by
        gcongr
        exact Complex.abs_re_le_norm ζ
      _ ≤ Λ * (s5Nrm D ^ 2 + ‖ζ‖ ^ 2 * η ^ 2) := by
        have hs := mul_nonneg hL (sq_nonneg (s5Nrm D - ‖ζ‖ * |η|))
        rw [sub_sq, mul_pow, sq_abs] at hs
        nlinarith only [hs]
  have herror := mul_le_mul_of_nonneg_right hsmall (sq_nonneg ‖u‖)
  have hcube : Λ ≤ Λ ^ 3 := by
    have hs : 1 ≤ Λ ^ 2 := by nlinarith only [hA.one_le]
    have hh := mul_le_mul_of_nonneg_left hs hL
    nlinarith only [hh]
  have hnonneg : 0 ≤ (s5Nrm D ^ 2 + ‖ζ‖ ^ 2 * η ^ 2) * ‖u‖ ^ 2 := by positivity
  have hextra := mul_le_mul_of_nonneg_right hcube hnonneg
  change (M + ζ * u * _).re ≤ _
  rw [hflux, mul_add, Complex.add_re, Complex.add_re, hconj, herr]
  simp only [Complex.add_re] at hbase
  have hplus := mul_nonneg (pow_nonneg hL 3) hnonneg
  ring_nf at hbase herror hextra hplus ⊢
  linarith only [hbase, herror, hextra, hplus]

end EinsteinFull.Blueprint
