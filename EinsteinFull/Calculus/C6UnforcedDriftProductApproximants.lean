import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinRelation.Sharpness.FieldDerivativeMeasurability
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The actual drift is measurable from any unit neighborhood of the origin. -/
private theorem drift_local {d : ℕ} {D : StructuralData d}
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

/-- Centered products of the actual drift and its zero-force orbit admit uniformly
bounded, centered local approximants with a structural Gaussian L2 error. -/
theorem unforced_drift_product_local_approximants
    : ∀ (hlocal : node_e_u3A_forced_u2D_localityStmt)
        (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt)
        (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ), 0 ≤ T →
      ∃ B R L c : ℝ, 1 ≤ B ∧ 1 ≤ R ∧ 0 < L ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ →
      ∀ (P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
        (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
      ∀ (t : ℝ≥0), (t : ℝ) ≤ T → ∀ (m l : Fin d),
        ∃ H : Lp ℂ 2 (reducedLaw Q),
          ((H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
            β l ω * P 0 t (β m) ω - ∫ η, β l η * P 0 t (β m) η ∂reducedLaw Q) ∧
          (∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ B) ∧
          ∀ ρ : ℝ, R ≤ ρ → ∃ K : Lp ℂ 2 (reducedLaw Q),
            IsComplexLocalObservation Q ρ K ∧ (∫ ω, K ω ∂reducedLaw Q) = 0 ∧
            (∀ᵐ ω ∂reducedLaw Q, ‖K ω‖ ≤ B) ∧
            ‖H-K‖ ≤ L * Real.exp (-c * ρ^2) := by
  intro hlocal hends d hd D T hT
  obtain ⟨K, hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨A, b, N, hA, _, hloc⟩ := hlocal d hd D
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hep := hends d hd D 2 (by norm_num) T 1 hT (by norm_num)
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  obtain ⟨C, c, hC, hc, heps⟩ := hep
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  let V := K + A * (2 + T) ^ N
  have hV : 0 < V := by dsimp only [V]; positivity
  refine ⟨max 1 (2 * K * V), max 1 C, 2 * K * C, c,
    le_max_left _ _, le_max_left _ _, by positivity, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag t ht m l
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hb := (hobs Q hQ β a μ hβ ha hμ).1
  have hv : ∀ᵐ ω ∂reducedLaw Q, ‖P 0 t (β m) ω‖ ≤ V := by
    by_cases ht0 : t = 0
    · subst t
      rw [(hP 0).1, ContinuousLinearMap.id_apply]
      exact (hb m).mono fun ω hω => hω.trans (le_add_of_nonneg_right (mul_nonneg hA0 (pow_nonneg (by linarith) N)))
    · have htpos : 0 < (t : ℝ) := lt_of_le_of_ne t.coe_nonneg (by
        intro he; apply ht0; exact NNReal.eq (he.symm))
      obtain ⟨G, _, _, hsize⟩ :=
        hloc Q hQ β a μ hβ ha hμ 0 (P 0) (Pdag 0) (hP 0) (hPdag 0) (.inl m)
      have hsize' := hsize t htpos (by norm_num)
      simp only [uncenteredEndpoint, zero_smul, add_zero, norm_zero,
        zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, Real.exp_zero, mul_one] at hsize'
      have hp : (2 + (t : ℝ)) ^ N ≤ (2 + T) ^ N :=
        pow_le_pow_left₀ (by positivity) (by linarith) N
      filter_upwards [hsize'] with ω hω
      exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hω |>.trans
        ((mul_le_mul_of_nonneg_left hp (by linarith)).trans (by dsimp only [V]; linarith))
  have hβtop : MemLp (β l : FieldPair d → ℂ) ∞ (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp _).aestronglyMeasurable K (hb l)
  let M : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2
      (hβtop.toLp (β l))
  have hM (f : Lp ℂ 2 (reducedLaw Q)) :
      (M f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => β l ω * f ω := by
    filter_upwards [hβtop.coeFn_toLp,
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) (hβtop.toLp (β l)) f]
      with ω h1 h2
    simpa only [M, ContinuousLinearMap.holderL_apply_apply,
      ContinuousLinearMap.mul_apply', h1] using h2
  have hMn (f : Lp ℂ 2 (reducedLaw Q)) : ‖M f‖ ≤ K * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hM f, hb l] with ω he hbω
    rw [he, norm_mul]
    exact mul_le_mul_of_nonneg_right hbω (norm_nonneg _)
  let F := M (P 0 t (β m))
  let H := centeredComplexLp Q F
  have hF : ∀ᵐ ω ∂reducedLaw Q, ‖F ω‖ ≤ K * V := by
    filter_upwards [hM (P 0 t (β m)), hb l, hv] with ω he hβω hvω
    rw [show F ω = _ from he, norm_mul]
    exact mul_le_mul hβω hvω (norm_nonneg _) hK.le
  have hHB : ∀ᵐ ω ∂reducedLaw Q, ‖H ω‖ ≤ max 1 (2 * K * V) :=
    (UnitInitialization.ae_norm_centered_le Q F hF).mono fun ω hω =>
      hω.trans (by rw [mul_assoc]; exact le_max_right _ _)
  have hrep : (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      β l ω * P 0 t (β m) ω - ∫ η, β l η * P 0 t (β m) η ∂reducedLaw Q := by
    have hi := integral_congr_ae (hM (P 0 t (β m)))
    filter_upwards [centeredComplexLp_ae Q F, hM (P 0 t (β m))] with ω h1 h2
    exact h1.trans (by rw [h2, hi])
  refine ⟨H, hrep, hHB, ?_⟩
  intro ρ hρ
  obtain ⟨E, J, hE, _, _, _, _, happ⟩ :=
    heps Q hQ β a μ hβ ha hμ P Pdag hP hPdag (.inl m) t ht
  obtain ⟨L, Jloc, L₂, J₂, hL, _, _, _, _, herr, _⟩ :=
    happ ρ ((le_max_right 1 C).trans hρ)
  let z := ∫ ω, P 0 t (β m) ω ∂reducedLaw Q
  let U := L₂ 0 + Lp.const 2 (reducedLaw Q) z
  have hdiff : P 0 t (β m) - U = centeredComplexLp Q (P 0 t (β m)) - L₂ 0 := by
    dsimp only [U, centeredComplexLp, z]
    abel
  have hn : ‖centeredComplexLp Q (P 0 t (β m)) - L₂ 0‖ = ‖E 0 - L 0‖ := by
    let f : FieldPair d → ℂ := E 0 - L 0
    have hnorm : ‖E 0 - L 0‖ = (eLpNorm f 2 (reducedLaw Q)).toReal := by
      rw [Lp.norm_def]
      calc
        _ = (eLpNorm f (ENNReal.ofReal 2) (reducedLaw Q)).toReal :=
          congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub (E 0) (L 0)))
        _ = _ := by rw [htwo]
    rw [hnorm, Lp.norm_def]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_ae
    have he : (E 0 : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        (centeredComplexLp Q (P 0 t (β m)) : FieldPair d → ℂ) := by
      simpa only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero] using hE 0
    filter_upwards [Lp.coeFn_sub (centeredComplexLp Q (P 0 t (β m))) (L₂ 0),
      Lp.coeFn_sub (E 0) (L 0), he, (hL 0).1] with ω h1 h2 h3 h4
    simp only [f, h1, Pi.sub_apply, h3, h4]
  have hUn : ‖P 0 t (β m) - U‖ ≤ C * Real.exp (-c * ρ ^ 2) := by
    rw [hdiff, hn]
    exact (herr 0 (by norm_num)).2.2
  have hUlocal : IsComplexLocalObservation Q ρ U := by
    obtain ⟨f, hf, he⟩ := (hL 0).2.2.1
    refine ⟨fun ω => f ω + z, hf.add measurable_const, ?_⟩
    filter_upwards [he, Lp.coeFn_add (L₂ 0) (Lp.const 2 (reducedLaw Q) z),
      Lp.coeFn_const 2 (reducedLaw Q) z] with ω h1 h2 h3
    simp only [U, h2, Pi.add_apply, h3, Function.const_apply, h1]
  let G := M U - Lp.const 2 (reducedLaw Q) (∫ ω, F ω ∂reducedLaw Q)
  have hGlocal : IsComplexLocalObservation Q ρ G := by
    obtain ⟨f, hf, hfe⟩ := drift_local hβ l ((le_max_left 1 C).trans hρ)
    obtain ⟨g, hg, hge⟩ := hUlocal
    refine ⟨fun ω => f ω * g ω - ∫ η, F η ∂reducedLaw Q,
      (hf.mul hg).sub measurable_const, ?_⟩
    filter_upwards [hfe, hge, hM U,
      Lp.coeFn_sub (M U) (Lp.const 2 (reducedLaw Q) (∫ ω, F ω ∂reducedLaw Q)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ ω, F ω ∂reducedLaw Q)] with ω h1 h2 h3 h4 h5
    simp only [G, h4, Pi.sub_apply, h5, Function.const_apply, h3, h1, h2]
  have hHG : H - G = M (P 0 t (β m) - U) := by
    dsimp only [H, G, centeredComplexLp, F]
    rw [map_sub]
    abel
  have herror : ‖H - G‖ ≤ K * (C * Real.exp (-c * ρ ^ 2)) := by
    rw [hHG]
    exact (hMn _).trans (mul_le_mul_of_nonneg_left hUn hK.le)
  obtain ⟨Z, hZlocal, hZm, hZB, hZe⟩ :=
    UnitInitialization.exists_bounded_centered_local_projection_norm Q ρ H G hHB
      (integral_centeredComplexLp Q F) hGlocal herror
  refine ⟨Z, hZlocal, hZm, hZB, ?_⟩
  simpa only [mul_assoc] using hZe

end EinsteinFull.Blueprint
