import EinsteinFull.Blueprint.G3.node_e_u3A_time_u2D_flux
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinFull.Calculus.ComplexSemigroupEnergySupport
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedDerivatives
import EinsteinRelation.Calculus.WeakHorizontalProducts
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
  {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private def timeFluxPair (f : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 f

private theorem timeFluxPair_apply (f g : Lp ℂ 2 (reducedLaw Q)) :
    timeFluxPair f g = ∫ ω, f ω * g ω ∂reducedLaw Q := by
  rw [timeFluxPair, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- Dominated convergence on the actual horizontal difference quotients.
The raw derivative need only be defined almost everywhere; its measurability
and L2 membership follow from the bounded orbit derivatives themselves. -/
theorem timeFlux_horizontal_derivative_of_bounded_orbit
    {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (k : Fin d) {f g : FieldPair d → ℝ} (hf : MemLp f 2 μ) (C : ℝ)
    (hd : ∀ᵐ ω ∂μ, ∀ s : ℝ,
      HasDerivAt (fun t : ℝ => f (translate (t • unitVector k) ω))
        (g (translate (s • unitVector k) ω)) s)
    (hb : ∀ᵐ ω ∂μ, ∀ s : ℝ, |g (translate (s • unitVector k) ω)| ≤ C) :
    ∃ hg : MemLp g 2 μ,
      HasHorizontalLpDerivative μ hμ k (hf.toLp f) (hg.toLp g) := by
  let q : ℝ → FieldPair d → ℝ := fun t ω =>
    t⁻¹ * (f (translate (t • unitVector k) ω) - f ω)
  have hqm (t : ℝ) : AEStronglyMeasurable (q t) μ :=
    (((hf.comp_measurePreserving (measurePreserving_translate μ hμ _)).sub hf).aestronglyMeasurable).const_mul _
  have hlim : ∀ᵐ ω ∂μ, Filter.Tendsto (fun t => q t ω)
      (𝓝[≠] (0 : ℝ)) (𝓝 (g ω)) := by
    filter_upwards [hd] with ω hω
    simpa only [q, zero_smul, translate_zero, sub_zero, zero_add, smul_eq_mul]
      using! (hω 0).tendsto_slope_zero
  have hgm := aestronglyMeasurable_of_tendsto_ae (𝓝[≠] (0 : ℝ)) hqm hlim
  have hgb : ∀ᵐ ω ∂μ, |g ω| ≤ C := by
    simpa only [zero_smul, translate_zero] using! hb.mono (fun _ h => h 0)
  have hg : MemLp g 2 μ := MemLp.of_bound hgm C hgb
  refine ⟨hg, ?_⟩
  have hqb (t : ℝ) (ht : t ≠ 0) : ∀ᵐ ω ∂μ, |q t ω| ≤ C := by
    filter_upwards [hd, hb] with ω hdω hbω
    have hs : ‖f (translate (t • unitVector k) ω) -
        f (translate ((0 : ℝ) • unitVector k) ω)‖ ≤ C * ‖t - 0‖ :=
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun s _ => (hdω s).differentiableAt)
        (fun s _ => by rw [(hdω s).deriv]; exact hbω s)
        convex_univ (mem_univ 0) (mem_univ t)
    simp only [zero_smul, translate_zero, sub_zero, Real.norm_eq_abs] at hs
    dsimp [q]
    rw [abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr ht), mul_comm]
    exact hs
  let u : ℝ → Lp ℝ 2 μ := fun t =>
    t⁻¹ • (translationLp μ hμ (t • unitVector k) (hf.toLp f) - hf.toLp f)
  have hu (t : ℝ) : u t =ᵐ[μ] q t := by
    have ht : translationLp μ hμ (t • unitVector k) (hf.toLp f) =ᵐ[μ]
        (fun ω => f (translate (t • unitVector k) ω)) := by
      rw [translationLp_toLp]
      exact MemLp.coeFn_toLp _
    filter_upwards [Lp.coeFn_smul t⁻¹
        (translationLp μ hμ (t • unitVector k) (hf.toLp f) - hf.toLp f),
      Lp.coeFn_sub (translationLp μ hμ (t • unitVector k) (hf.toLp f)) (hf.toLp f),
      ht, hf.coeFn_toLp] with ω h1 h2 h3 h4
    dsimp only [u, q]
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul]
  have hnorm (t : ℝ) : ‖u t - hg.toLp g‖ ^ 2 =
      ∫ ω, (q t ω - g ω) * (q t ω - g ω) ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u t) (hg.toLp g), hu t, hg.coeFn_toLp]
      with ω h1 h2 h3
    simp only [h1, Pi.sub_apply, h2, h3]
    rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, sq]
  have hdc : Filter.Tendsto
      (fun t => ∫ ω, (q t ω - g ω) * (q t ω - g ω) ∂μ)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    letI : (𝓝[≠] (0 : ℝ)).IsCountablyGenerated := inferInstance
    have he := tendsto_integral_filter_of_dominated_convergence (l := 𝓝[≠] (0 : ℝ)) (μ := μ)
      (fun _ => (2 * C) * (2 * C))
      (F := fun t ω => (q t ω - g ω) * (q t ω - g ω))
      (f := fun _ => (0 : ℝ))
      (Filter.Eventually.of_forall fun t => ((hqm t).sub hgm).mul ((hqm t).sub hgm))
      (by
        filter_upwards [self_mem_nhdsWithin] with t ht
        filter_upwards [hqb t ht, hgb] with ω h1 h2
        have hab : |q t ω - g ω| ≤ 2 * C := by
          calc
            _ ≤ |q t ω| + |g ω| := abs_sub _ _
            _ ≤ 2 * C := by linarith
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hab hab (abs_nonneg _) (by linarith [abs_nonneg (q t ω - g ω)]))
      (integrable_const _)
      (by
        filter_upwards [hlim] with ω hω
        simpa only [sub_self, mul_zero] using! (hω.sub_const (g ω)).mul
          (hω.sub_const (g ω)))
    simpa using! he
  unfold HasHorizontalLpDerivative
  change Filter.Tendsto u (𝓝[≠] (0 : ℝ)) (𝓝 (hg.toLp g))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : (fun t => ‖u t - hg.toLp g‖) =
      fun t => Real.sqrt (∫ ω, (q t ω - g ω) * (q t ω - g ω) ∂μ) := by
    funext t
    rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
  rw [he]
  simpa only [Real.sqrt_zero, Function.comp_def] using!
    (Real.continuous_sqrt.tendsto 0).comp hdc

private def timeFluxDirections : (cs : List (Fin d)) → Fin cs.length → Vec d
  | [] => Fin.elim0
  | k :: cs => Fin.cons (unitVector k) (timeFluxDirections cs)

private theorem timeFlux_coordinateIterate_eq {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) (x : Vec d) :
    coordinateIterate cs f x =
      iteratedFDeriv ℝ cs.length f x (timeFluxDirections cs) := by
  induction cs generalizing x with
  | nil => simp [coordinateIterate, iteratedFDeriv_zero_apply]
  | cons k cs ih =>
    have he : coordinateIterate cs f = fun y =>
        iteratedFDeriv ℝ cs.length f y (timeFluxDirections cs) := funext ih
    simp only [coordinateIterate, List.length_cons, timeFluxDirections,
      iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rw [he]
    exact fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (m := cs.length) (by
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)) x) _ _

private theorem timeFlux_euclidean_unit (k : Fin d) :
    euclideanNorm (unitVector k) = 1 := by
  change Real.sqrt (dotProduct (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem timeFlux_directions_norm (cs : List (Fin d))
    (k : Fin cs.length) : euclideanNorm (timeFluxDirections cs k) = 1 := by
  induction cs with
  | nil => exact Fin.elim0 k
  | cons j cs ih =>
    refine Fin.cases ?_ (fun l => ?_) k
    · exact timeFlux_euclidean_unit j
    · exact ih l

private theorem timeFlux_coefficient_jet_bound {M : ℕ → ℝ} {ω : FieldPair d}
    (hω : IsSmoothWithBounds M ω) (cs : List (Fin d)) (hcs : 1 ≤ cs.length)
    (j k : Fin d) (x : Vec d) :
    |coordinateIterate cs (fun y => ω.1 y j k) x| ≤ M cs.length := by
  obtain ⟨A, B, _, hB, hAB, hA, _⟩ := hω.2 cs.length hcs
  rw [timeFlux_coordinateIterate_eq (hω.1.1 j k)]
  have hc := Regeneration.coordinate_abs_le_euclideanNorm
    (Matrix.mulVec (fun j k => iteratedFDeriv ℝ cs.length
      (fun y => ω.1 y j k) x (timeFluxDirections cs)) (unitVector k)) j
  have hb := hA x (timeFluxDirections cs) (unitVector k)
  have he (N : Mat d) : (N.mulVec (unitVector k)) j = N j k := by
    change dotProduct (fun l => N j l) (Pi.single k 1) = _
    rw [dotProduct_single, mul_one]
  erw [he] at hc
  simp only [timeFlux_directions_norm, Finset.prod_const_one,
    timeFlux_euclidean_unit, mul_one] at hb
  exact (hc.trans hb).trans (by linarith)

private theorem timeFlux_coefficient_jet_step
    {M : ℕ → ℝ} (hs : ∀ᵐ ω ∂reducedLaw Q, IsSmoothWithBounds M ω)
    (j k : Fin d) (cs : List (Fin d))
    (hf : MemLp (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k))
      2 (reducedLaw Q)) (l : Fin d) :
    ∃ hg : MemLp (iteratedHorizontalDerivative (l :: cs)
      (fun ω : FieldPair d => ω.1 0 j k)) 2 (reducedLaw Q),
      HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (hf.toLp _) (hg.toLp _) := by
  let f := iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k)
  have horbit (ω : FieldPair d) : orbit f ω =
      coordinateIterate cs (fun y => ω.1 y j k) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_matrix, add_zero]
  apply timeFlux_horizontal_derivative_of_bounded_orbit
    (reducedLaw_stationary Q) l hf (M (l :: cs).length)
  · filter_upwards [hs] with ω hω
    have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
      rw [horbit]
      exact contDiff_coordinateIterate (hω.1.1 j k) cs
    intro s
    have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
      s ((hasDerivAt_id' s).smul_const (unitVector l))
    change HasDerivAt (fun t => orbit f ω (t • unitVector l))
      (horizontalDerivative l f (translate (s • unitVector l) ω)) s
    rw [horizontalDerivative_translate]
    simpa only [Function.comp_def, one_smul, coordinateDerivative] using! hd
  · filter_upwards [hs] with ω hω
    intro s
    change |horizontalDerivative l f (translate (s • unitVector l) ω)| ≤ _
    rw [horizontalDerivative_translate, horbit]
    exact timeFlux_coefficient_jet_bound hω (l :: cs) (by simp) j k _

/-- Every finite horizontal derivative of an actual reduced coefficient is an
L2 observation. Each next raw derivative is its two-sided strong translation
derivative. All smoothness and uniform bounds are derived from the physical
smooth-law assumption; no initial horizontal-domain assumption is added. -/
theorem timeFlux_coefficient_jets
    {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) :
    ∀ cs : List (Fin d), ∃ hf : MemLp
      (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k))
      2 (reducedLaw Q),
      ∀ l : Fin d, ∃ hg : MemLp
        (iteratedHorizontalDerivative (l :: cs) (fun ω : FieldPair d => ω.1 0 j k))
        2 (reducedLaw Q),
        HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
          (hf.toLp _) (hg.toLp _) := by
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hs := hM Q hQ
  have hmem : ∀ cs : List (Fin d), MemLp
      (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k))
      2 (reducedLaw Q) := by
    intro cs
    induction cs with
    | nil =>
      exact Complex.reCLM.comp_memLp'
        ((memLp_reduced_coefficient_complex Q j k).mono_exponent le_top)
    | cons l cs ih => exact (timeFlux_coefficient_jet_step hs j k cs ih l).choose
  intro cs
  exact ⟨hmem cs, fun l => timeFlux_coefficient_jet_step hs j k cs (hmem cs) l⟩

/-- All finite raw coefficient jets are essentially bounded under the actual
reduced law, including order zero. This supplies the bounded factors needed
for products in the initial generator graphs. -/
theorem timeFlux_coefficient_jets_memLp_top {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs : List (Fin d)) :
    MemLp (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k))
      ∞ (reducedLaw Q) := by
  cases cs with
  | nil => exact Complex.reCLM.comp_memLp' (memLp_reduced_coefficient_complex Q j k)
  | cons l cs =>
    obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
      node_eq_u2E_reduced_u2D_bounds_of_deps d D
    apply MemLp.of_bound
      (timeFlux_coefficient_jets hQ j k (l :: cs)).choose.aestronglyMeasurable
      (M (l :: cs).length)
    filter_upwards [hM Q hQ] with ω hω
    have he := congrFun (orbit_iteratedHorizontalDerivative (l :: cs)
      (fun η : FieldPair d => η.1 0 j k) ω) 0
    simp only [orbit, translate_zero] at he
    rw [Real.norm_eq_abs, he]
    have ho : orbit (fun η : FieldPair d => η.1 0 j k) ω = fun x => ω.1 x j k := by
      funext x
      simp only [orbit, translate_matrix, add_zero]
    rw [ho]
    exact timeFlux_coefficient_jet_bound hω (l :: cs) (by simp) j k 0

/-- Every raw coefficient jet has a bound along its entire spatial orbit on
one full-measure event. The order-zero bound comes from actual reduced
ellipticity; the positive orders use the physical smooth-law bounds. -/
theorem timeFlux_coefficient_jets_orbit_bounds {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) :
    ∃ B : List (Fin d) → ℝ, (∀ cs, 0 ≤ B cs) ∧
      ∀ cs, ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
        |orbit (iteratedHorizontalDerivative cs
          (fun η : FieldPair d => η.1 0 j k)) ω x| ≤ B cs := by
  obtain ⟨K, A, B, hK, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity Q.ellipticity_parameter
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  refine ⟨fun cs => if cs = [] then K else |M cs.length|, ?_, ?_⟩
  · intro cs
    dsimp only
    split_ifs
    · exact zero_le_one.trans hK
    · exact abs_nonneg _
  · intro cs
    filter_upwards [(hb d D.dependenceRange Q).2.2, hM Q hQ] with ω he hs
    intro x
    rw [orbit_iteratedHorizontalDerivative]
    have ho : orbit (fun η : FieldPair d => η.1 0 j k) ω = fun y => ω.1 y j k := by
      funext y
      simp only [orbit, translate_matrix, add_zero]
    rw [ho]
    cases cs with
    | nil =>
      simp only [coordinateIterate, ↓reduceIte]
      apply abs_entry_le_of_quadratic_bounds (zero_le_one.trans hK) (ω.1 x) (he.1 x).1
      · intro ξ
        exact (mul_nonneg (inv_nonneg.mpr (zero_le_one.trans hK))
          (euclideanSq_nonneg_coords ξ)).trans (((he.1 x).2 ξ).1)
      · exact fun ξ => ((he.1 x).2 ξ).2
    | cons l cs =>
      simp only [List.cons_ne_nil, ↓reduceIte]
      exact (timeFlux_coefficient_jet_bound hs (l :: cs) (by simp) j k x).trans
        (le_abs_self _)

private theorem timeFlux_coefficient_jet_curve {ω : FieldPair d} {M : ℕ → ℝ}
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
  simpa only [Function.comp_def, one_smul, coordinateDerivative] using! hd

/-- Products of any two actual coefficient jets have their literal Leibniz
strong L2 derivatives. Both factors and all required bounds are derived from
HasSmoothBounds, including products with an undifferentiated coefficient. -/
theorem timeFlux_coefficient_jet_products {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k m n : Fin d) (cs bs : List (Fin d)) :
    let f := iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k)
    let g := iteratedHorizontalDerivative bs (fun ω : FieldPair d => ω.1 0 m n)
    ∃ hf : MemLp (fun ω => f ω * g ω) 2 (reducedLaw Q),
      ∀ l : Fin d, ∃ hg : MemLp (fun ω =>
        iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.1 0 j k) ω * g ω +
          f ω * iteratedHorizontalDerivative (l :: bs)
            (fun η : FieldPair d => η.1 0 m n) ω) 2 (reducedLaw Q),
        HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
          (hf.toLp _) (hg.toLp _) := by
  dsimp only
  have hf : MemLp (fun ω =>
      iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative bs (fun η : FieldPair d => η.1 0 m n) ω)
      2 (reducedLaw Q) :=
    (timeFlux_coefficient_jets_memLp_top hQ j k cs).fun_mul
      (timeFlux_coefficient_jets hQ m n bs).choose
  refine ⟨hf, ?_⟩
  intro l
  obtain ⟨C, hC, hCb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ j k
  obtain ⟨E, hE, hEb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ m n
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  apply timeFlux_horizontal_derivative_of_bounded_orbit (reducedLaw_stationary Q) l hf
    (C (l :: cs) * E bs + C cs * E (l :: bs))
  · filter_upwards [hM Q hQ] with ω hω
    intro s
    exact (timeFlux_coefficient_jet_curve hω j k l cs s).mul
      (timeFlux_coefficient_jet_curve hω m n l bs s)
  · filter_upwards [hCb (l :: cs), hCb cs, hEb (l :: bs), hEb bs]
      with ω h1 h2 h3 h4
    intro s
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (h1 _) (h4 _) (abs_nonneg _) (hC _)
    · rw [abs_mul]
      exact mul_le_mul (h2 _) (h3 _) (abs_nonneg _) (hC _)

private def timeFluxCoefficientJet {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs : List (Fin d)) :
    Lp ℂ 2 (reducedLaw Q) :=
  Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
    ((timeFlux_coefficient_jets hQ j k cs).choose.toLp _)

private theorem timeFluxCoefficientJet_ae {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs : List (Fin d)) :
    timeFluxCoefficientJet hQ j k cs =ᵐ[reducedLaw Q]
      (fun ω => (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω : ℂ)) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
    ((timeFlux_coefficient_jets hQ j k cs).choose.toLp _),
    (timeFlux_coefficient_jets hQ j k cs).choose.coeFn_toLp] with ω h1 h2
  exact h1.trans (congrArg Complex.ofReal h2)

private theorem timeFluxCoefficientJet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs : List (Fin d)) (l : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
      (timeFluxCoefficientJet hQ j k cs) (timeFluxCoefficientJet hQ j k (l :: cs)) :=
  hasComplexHorizontalDerivative_ofReal
    ((timeFlux_coefficient_jets hQ j k cs).choose_spec l).choose_spec

private theorem timeFlux_sum_ae (μ : Measure (FieldPair d))
    (s : Finset (Fin d)) (f : Fin d → Lp ℂ 2 μ) :
    (∑ j ∈ s, f j : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∑ j ∈ s, f j ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 μ
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with ω h1 h2
    simpa only [Pi.add_apply, h2] using! h1

private theorem timeFlux_coefficient_mul_jet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k m n l : Fin d) (cs : List (Fin d)) :
    ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (complexCoefficientMul Q j k (timeFluxCoefficientJet hQ m n cs)) H := by
  obtain ⟨hf, hh⟩ := timeFlux_coefficient_jet_products hQ j k m n [] cs
  obtain ⟨hg, hd⟩ := hh l
  have he : complexCoefficientMul Q j k (timeFluxCoefficientJet hQ m n cs) =
      Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (hf.toLp _) := by
    apply Lp.ext
    filter_upwards [complexCoefficientMul_coe Q j k (timeFluxCoefficientJet hQ m n cs),
      timeFluxCoefficientJet_ae hQ m n cs,
      Complex.ofRealCLM.coeFn_compLpL (hf.toLp _), hf.coeFn_toLp] with ω h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Complex.ofRealCLM_apply, Complex.ofReal_mul]
    rfl
  rw [he]
  exact ⟨_, hasComplexHorizontalDerivative_ofReal hd⟩

private theorem timeFlux_generator_of_flux_derivatives
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hF : ∀ j k : Fin d, ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (complexCoefficientMul Q j k (G k)) H) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ f g := by
  classical
  choose H hH using hF
  let g : Lp ℂ 2 (reducedLaw Q) :=
    (1 / 2 : ℂ) • (∑ j, ∑ k, H j k) + ζ • ∑ j, complexCoefficientMul Q j i (G j)
  refine ⟨g, G, hG, ?_⟩
  intro v V hV
  have hp (j k : Fin d) : timeFluxPair v (H j k) =
      -(∫ ω, (ω.1 0 j k : ℂ) * G k ω * V j ω ∂reducedLaw Q) := by
    rw [timeFluxPair_apply]
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
  have hd : timeFluxPair v (∑ j, complexCoefficientMul Q j i (G j)) =
      ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q := by
    rw [timeFluxPair_apply]
    apply integral_congr_ae
    filter_upwards [timeFlux_sum_ae (reducedLaw Q) Finset.univ
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
  have he : (∫ ω, g ω * v ω ∂reducedLaw Q) = timeFluxPair v g := by
    simp only [timeFluxPair_apply, mul_comm]
  rw [he]
  change timeFluxPair v ((1 / 2 : ℂ) • (∑ j, ∑ k, H j k) +
    ζ • ∑ j, complexCoefficientMul Q j i (G j)) = _
  rw [map_add, map_smul, map_smul, hd]
  simp only [map_sum, hp, smul_eq_mul, Finset.sum_neg_distrib]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum _ (fun k _ => hi _ k)]
  ring

private theorem timeFluxCoefficientJet_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs : List (Fin d)) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ (timeFluxCoefficientJet hQ j k cs) g := by
  apply timeFlux_generator_of_flux_derivatives
    (G := fun l => timeFluxCoefficientJet hQ j k (l :: cs))
    (fun l => timeFluxCoefficientJet_derivative hQ j k cs l)
  intro l m
  exact timeFlux_coefficient_mul_jet_derivative hQ l m j k l (m :: cs)

/-- Every actual coefficient observation lies in the full weak generator
domain for every signed complex force. Its coefficient-flux derivatives are
constructed from the physical smooth-law bounds, not assumed. -/
theorem timeFlux_coefficient_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (j k : Fin d) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ (a j k) g := by
  have he : a j k = timeFluxCoefficientJet hQ j k [] := by
    apply Lp.ext
    exact (ha j k).trans (timeFluxCoefficientJet_ae hQ j k []).symm
  rw [he]
  exact timeFluxCoefficientJet_generator hQ j k []

/-- The actual coefficient observations have full strong horizontal gradients
at time zero, derived directly from the physical smooth-law assumption. -/
theorem timeFlux_coefficient_gradient {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (j k : Fin d) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (a j k) G := by
  have he : a j k = timeFluxCoefficientJet hQ j k [] := by
    apply Lp.ext
    exact (ha j k).trans (timeFluxCoefficientJet_ae hQ j k []).symm
  rw [he]
  exact ⟨fun l => timeFluxCoefficientJet hQ j k [l],
    fun l => timeFluxCoefficientJet_derivative hQ j k [] l⟩

private theorem timeFlux_drift_eq {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (k : Fin d) :
    β k = (1 / 2 : ℂ) • ∑ j, timeFluxCoefficientJet hQ j k [j] := by
  apply Lp.ext
  filter_upwards [hβ k,
    Lp.coeFn_smul (1 / 2 : ℂ) (∑ j, timeFluxCoefficientJet hQ j k [j]),
    timeFlux_sum_ae (reducedLaw Q) Finset.univ (fun j => timeFluxCoefficientJet hQ j k [j]),
    ae_all_iff.mpr (fun j => timeFluxCoefficientJet_ae hQ j k [j])]
    with ω h1 h2 h3 h4
  rw [h1, h2, Pi.smul_apply, h3]
  simp only [smul_eq_mul, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [h4 j]
  congr 1
  change coordinateDerivative j (fun x => ω.1 x j k) 0 =
    coordinateDerivative j (orbit (fun η : FieldPair d => η.1 0 j k) ω) 0
  congr 1
  funext x
  simp only [orbit, translate_matrix, add_zero]

/-- The actual reduced drift also has a full strong horizontal gradient at
zero. Its derivatives are the literal sums of second coefficient jets. -/
theorem timeFlux_drift_gradient {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (k : Fin d) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (β k) G := by
  rw [timeFlux_drift_eq hβ k]
  refine ⟨fun l => (1 / 2 : ℂ) • ∑ j, timeFluxCoefficientJet hQ j k [l, j], ?_⟩
  intro l
  apply HasComplexHorizontalDerivative.smul
  have hs (s : Finset (Fin d)) :
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (∑ j ∈ s, timeFluxCoefficientJet hQ j k [j])
        (∑ j ∈ s, timeFluxCoefficientJet hQ j k [l, j]) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using!
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) l
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (timeFluxCoefficientJet_derivative hQ j k [j] l).add ih
  exact hs Finset.univ

/-- Actual reduced drift observations belong to the full forward generator
domain, for every complex force, with no additional regularity premise. -/
theorem timeFlux_drift_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (k : Fin d) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ (β k) g := by
  classical
  rw [timeFlux_drift_eq hβ k]
  have hJ (j : Fin d) := timeFluxCoefficientJet_generator (i := i) (ζ := ζ) hQ j k [j]
  choose H hH using hJ
  have hs (s : Finset (Fin d)) : IsComplexGeneratorPair Q i ζ
      (∑ j ∈ s, timeFluxCoefficientJet hQ j k [j]) (∑ j ∈ s, H j) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty, zero_smul] using! (hH k).smul 0
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      exact (hH j).add ih
  exact ⟨_, (hs Finset.univ).smul (1 / 2 : ℂ)⟩

/-- The literal initial datum beta_j + zeta*a_ij lies in the full forward
generator domain. This includes the initial endpoint used in e:time-flux. -/
theorem timeFlux_forward_initial_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (j : Fin d) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ (β j + ζ • a i j) g := by
  obtain ⟨g, hg⟩ := timeFlux_drift_generator (i := i) (ζ := ζ) hβ j
  obtain ⟨h, hh⟩ := timeFlux_coefficient_generator (i := i) (ζ := ζ) hQ ha i j
  exact ⟨_, hg.add (hh.smul ζ)⟩

/-- The actual forward endpoint data have a continuous strong horizontal
gradient orbit on the closed half-line, including the initial time. -/
theorem timeFlux_forward_continuous_gradient {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (j : Fin d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ l, Continuous (fun t => G t l)) ∧
      ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t (β j + ζ • a i j)) (G t) := by
  obtain ⟨g, hg⟩ := timeFlux_forward_initial_generator (i := i) (ζ := ζ) hβ ha j
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hg
  refine ⟨fun t l => G (t : ℝ) l, ?_, ?_⟩
  · intro l
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) l).continuous.comp
      (hGc.comp continuous_subtype_val)
  · intro t
    simpa only [Real.toNNReal_coe] using! hG (t : ℝ)

private theorem timeFlux_coefficient_mul_drift_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (j k l m : Fin d) :
    ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (complexCoefficientMul Q j k (β m)) H := by
  classical
  rw [timeFlux_drift_eq hβ m, map_smul, map_sum]
  have hJ (n : Fin d) := timeFlux_coefficient_mul_jet_derivative hQ j k n m l [n]
  choose H hH using hJ
  have hs (s : Finset (Fin d)) : HasComplexHorizontalDerivative
      (reducedLaw Q) (reducedLaw_stationary Q) l
      (∑ n ∈ s, complexCoefficientMul Q j k (timeFluxCoefficientJet hQ n m [n]))
      (∑ n ∈ s, H n) := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using!
        HasComplexHorizontalDerivative.zero (reducedLaw Q) (reducedLaw_stationary Q) l
    | @insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      exact (hH n).add ih
  exact ⟨_, (hs Finset.univ).smul (1 / 2 : ℂ)⟩

private theorem timeFlux_transpose_generator_of_column_derivatives
    {f g : Lp ℂ 2 (reducedLaw Q)} (h0 : IsComplexGeneratorPair Q i 0 f g)
    (hF : ∀ j : Fin d, ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (complexCoefficientMul Q j i f) H) :
    ∃ h : Lp ℂ 2 (reducedLaw Q), IsComplexTransposeGeneratorPair Q i ζ f h := by
  classical
  choose H hH using hF
  obtain ⟨G, hG, hw⟩ := h0
  refine ⟨g - ζ • ∑ j, H j, G, hG, ?_⟩
  intro v V hV
  have hp (j : Fin d) : timeFluxPair v (H j) =
      -(∫ ω, f ω * (ω.1 0 j i : ℂ) * V j ω ∂reducedLaw Q) := by
    have hb := (complexHorizontalDerivatives_integration_by_parts (hH j) (hV j)).2.2
    rw [timeFluxPair_apply]
    calc
      _ = ∫ ω, H j ω * v ω ∂reducedLaw Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => mul_comm _ _
      _ = _ := hb
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [complexCoefficientMul_coe Q j i f] with ω hω
        rw [hω]
        ring
  have hi (j : Fin d) : Integrable
      (fun ω => f ω * (ω.1 0 j i : ℂ) * V j ω) (reducedLaw Q) := by
    have hm := (Lp.memLp (complexCoefficientMul Q j i f)).integrable_mul (Lp.memLp (V j))
    apply hm.congr
    filter_upwards [complexCoefficientMul_coe Q j i f] with ω hω
    simp only [Pi.mul_apply, hω]
    ring
  have he : (∫ ω, (g - ζ • ∑ j, H j) ω * v ω ∂reducedLaw Q) =
      timeFluxPair v (g - ζ • ∑ j, H j) := by
    simp only [timeFluxPair_apply, mul_comm]
  rw [he, map_sub, map_smul]
  simp only [map_sum, hp, smul_eq_mul, Finset.sum_neg_distrib]
  have hg := hw v V hV
  simp only [zero_mul, add_zero] at hg
  have hpair : timeFluxPair v g = ∫ ω, g ω * v ω ∂reducedLaw Q := by
    simp only [timeFluxPair_apply, mul_comm]
  rw [hpair, hg]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [integral_finset_sum _ (fun j _ => hi j)]
  ring

/-- Actual drift data lie in the full TRUE bilinear-transpose generator
domain. The force contribution is minus the divergence of the coefficient
column times the datum, obtained by integration by parts on the full domain. -/
theorem timeFlux_transpose_initial_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (k : Fin d) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexTransposeGeneratorPair Q i ζ (β k) g := by
  obtain ⟨g, hg⟩ := timeFlux_drift_generator (i := i) (ζ := 0) hβ k
  apply timeFlux_transpose_generator_of_column_derivatives hg
  intro j
  exact timeFlux_coefficient_mul_drift_derivative hβ j i j k

/- Adapted from the W2 full-transpose graph energy argument, using only
production calculus imports and keeping all proof obligations here. -/
/-- The transpose column pairing has the same structural Young bound as the
forward pairing, by conjugation of the scalar force and Hilbert pairing. -/
private theorem timeFlux_transpose_force_pair_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q))
    (G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) :
    (ζ * inner ℂ (complexForceDrift Q i G) f).re ≤
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) +
        complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have h := re_complexForceDrift_pair_le Q i (star ζ) f G
  have he : (star ζ * inner ℂ f (complexForceDrift Q i G)).re =
      (ζ * inner ℂ (complexForceDrift Q i G) f).re := by
    rw [← inner_conj_symm f (complexForceDrift Q i G)]
    change (star ζ * star (inner ℂ (complexForceDrift Q i G) f)).re = _
    rw [← star_mul]
    simp only [Complex.star_def, Complex.conj_re, mul_comm]
  simpa only [he, complexForceShift, norm_star] using! h

/-- Full transpose graph coercivity for its unique actual H1 gradient.
The coefficient and force shift depend only on dimension and ellipticity. -/
private theorem timeFlux_transpose_gradient_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * (∑ j, ‖G j‖ ^ 2) ≤
      -(inner ℂ f g).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have ht := hfg.conjugate_test hG f G hG
  have hb := reduced_complex_energy_lowerBound Q G
  have hy := timeFlux_transpose_force_pair_le Q i ζ f (WithLp.toLp 2 G)
  have hr : (inner ℂ f g).re = -(1 / 2 : ℝ) *
      (∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * G k ω
        ∂reducedLaw Q).re +
      (ζ * inner ℂ (complexForceDrift Q i (WithLp.toLp 2 G)) f).re := by
    rw [ht, Complex.add_re, Complex.mul_re]
    norm_num
  linarith only [hb, hy, hr]

private theorem timeFlux_transpose_generator_sub
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g u v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (huv : IsComplexTransposeGeneratorPair Q i ζ u v) :
    IsComplexTransposeGeneratorPair Q i ζ (f - u) (g - v) := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
  apply (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mpr
  have hf := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mp hfg
  have hu := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mp huv
  rw [show (s : ℂ) • (f - u) - (g - v) =
    ((s : ℂ) • f - g) - ((s : ℂ) • u - v) by module, map_sub, hf, hu]

private theorem timeFlux_transpose_euclidean_gradient_coercive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * ‖G‖ ^ 2 ≤
      -(inner ℂ f g).re + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  simpa only [PiLp.norm_sq_eq_of_L2] using! timeFlux_transpose_gradient_coercive hfg hG

private theorem timeFlux_transpose_gradient_sq_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) * ‖G‖ ^ 2 ≤
      ‖f‖ * ‖g‖ + complexForceShift d Λ₀ ζ * ‖f‖ ^ 2 := by
  have hi : -(inner ℂ f g).re ≤ ‖f‖ * ‖g‖ := by
    calc
      _ ≤ ‖inner ℂ f g‖ := (neg_le_abs _).trans (Complex.abs_re_le_norm _)
      _ ≤ _ := norm_inner_le_norm _ _
  exact (timeFlux_transpose_euclidean_gradient_coercive hfg hG).trans (add_le_add hi le_rfl)

/-- Convergence in the full generator graph implies convergence of the actual Euclidean gradient. -/
private theorem timeFlux_tendsto_complexHorizontalGradient_of_transpose_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ} {α : Type*} {l : Filter α}
    {u v : α → Lp ℂ 2 (reducedLaw Q)}
    {G : α → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    {f g : Lp ℂ 2 (reducedLaw Q)}
    {H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hg : ∀ x, IsComplexTransposeGeneratorPair Q i ζ (u x) (v x))
    (hG : ∀ x, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u x) (G x))
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f H)
    (hu : Tendsto u l (𝓝 f)) (hv : Tendsto v l (𝓝 g)) : Tendsto G l (𝓝 H) := by
  let c := (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4
  have hc : 0 < c := div_pos (inv_pos.mpr (mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))) (by norm_num)
  have hb (x : α) : ‖G x - H‖ ^ 2 ≤
      (‖u x-f‖ * ‖v x-g‖ + complexForceShift d Λ₀ ζ * ‖u x-f‖ ^ 2) / c := by
    apply (le_div_iff₀ hc).mpr
    have hd : IsComplexTransposeGeneratorPair Q i ζ (u x-f) (v x-g) := by
      exact timeFlux_transpose_generator_sub (hg x) hfg
    have hD : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (u x-f) (G x-H) := by
      intro j
      simpa only [PiLp.sub_apply, neg_one_smul, ← sub_eq_add_neg] using!
        (hG x j).add ((hH j).smul (-1))
    rw [mul_comm]
    exact timeFlux_transpose_gradient_sq_le hd hD
  have hu0 := (hu.sub_const f).norm
  have hv0 := (hv.sub_const g).norm
  simp only [sub_self, norm_zero] at hu0 hv0
  have he : Tendsto (fun x =>
      (‖u x-f‖ * ‖v x-g‖ + complexForceShift d Λ₀ ζ * ‖u x-f‖ ^ 2) / c) l (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, zero_div] using! ((hu0.mul hv0).add ((hu0.pow 2).const_mul _)).div_const c
  have hn := (squeeze_zero (fun x => sq_nonneg ‖G x-H‖) hb he).sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- A continuous curve in the full generator graph has a continuous actual horizontal gradient. -/
private theorem timeFlux_continuous_complexHorizontalGradient_of_transpose_generator {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {α : Type*} [TopologicalSpace α]
    {u v : α → Lp ℂ 2 (reducedLaw Q)}
    {G : α → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hg : ∀ x, IsComplexTransposeGeneratorPair Q i ζ (u x) (v x))
    (hG : ∀ x, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u x) (G x))
    (hu : Continuous u) (hv : Continuous v) : Continuous G :=
  continuous_iff_continuousAt.mpr fun x =>
    timeFlux_tendsto_complexHorizontalGradient_of_transpose_generator hg hG (hg x) (hG x)
      (hu.tendsto x) (hv.tendsto x)

/-- The actual transpose drift endpoint has a continuous strong horizontal
L2 gradient on the closed time half-line, including its initial value. -/
theorem timeFlux_transpose_continuous_gradient {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (k : Fin d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ l, Continuous (fun t => G t l)) ∧
      ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T t (β k)) (G t) := by
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := i) (ζ := ζ) hβ k
  have he (t : ℝ≥0) : ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T t (β k)) G := by
    obtain ⟨G, hG, _⟩ := hT.map_generator hP hg t
    exact ⟨WithLp.toLp 2 G, hG⟩
  choose G hG using he
  have hc : Continuous G := timeFlux_continuous_complexHorizontalGradient_of_transpose_generator
    (fun t => hT.map_generator hP hg t) hG
    (hT.continuous_apply hP (β k)) (hT.continuous_apply hP g)
  refine ⟨fun t l => G t l, ?_, hG⟩
  intro l
  exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) l).continuous.comp hc

/-- The true transpose primitive satisfies its full generator graph at every
finite time, including zero. No initial domain or gradient assumption is used.
This is the integrated generator step of `e:time-flux`; the continuous
endpoint gradients constructed above also identify its primitive gradient. -/
theorem timeFlux_transpose_primitive_graph
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IsComplexTransposeGeneratorPair Q i ζ
      (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f) (T t f - f) := by
  apply (isComplexTransposeGeneratorPair_iff_bilinear_adjoint Q i ζ _ _).mpr
  intro u v huv
  have hcT : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hu : Continuous (fun s : ℝ => timeFluxPair f (P s.toNNReal u)) :=
    (timeFluxPair f).continuous.comp ((hP.2.2.1 u).comp continuous_real_toNNReal)
  have hv : Continuous (fun s : ℝ => timeFluxPair f (P s.toNNReal v)) :=
    (timeFluxPair f).continuous.comp ((hP.2.2.1 v).comp continuous_real_toNNReal)
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.property
    hu.continuousOn
    (fun s hs =>
      (((timeFluxPair f).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt s
        (hP.hasDerivWithinAt_orbit huv s hs.1.le)).mono Ioi_subset_Ici_self)
    (hv.intervalIntegrable 0 t)
  have hi : (∫ s in Icc (0 : ℝ) (t : ℝ), timeFluxPair f (P s.toNNReal v)) =
      timeFluxPair f (P t u) - timeFluxPair f u := by
    rw [integral_Icc_eq_integral_Ioc]
    rw [intervalIntegral.integral_of_le t.property] at he
    change (∫ s in Ioc (0 : ℝ) (t : ℝ), timeFluxPair f (P s.toNNReal v)) =
      timeFluxPair f (P (t : ℝ).toNNReal u) -
        timeFluxPair f (P (0 : ℝ).toNNReal u) at he
    simpa only [Real.toNNReal_coe, Real.toNNReal_zero, hP.1,
      ContinuousLinearMap.id_apply] using! he
  have hp (s : ℝ≥0) (w : Lp ℂ 2 (reducedLaw Q)) :
      timeFluxPair w (T s f) = timeFluxPair f (P s w) := by
    simp only [timeFluxPair_apply]
    simpa only [mul_comm] using! (hT s w f).symm
  have hleft : (∫ ω, (T t f - f) ω * u ω ∂reducedLaw Q) =
      timeFluxPair f (P t u) - timeFluxPair f u := by
    have hm : (∫ ω, (T t f - f) ω * u ω ∂reducedLaw Q) =
        timeFluxPair u (T t f - f) := by
      simp only [timeFluxPair_apply, mul_comm]
    rw [hm, map_sub, hp]
    simp only [timeFluxPair_apply, mul_comm]
  have hright : (∫ ω,
      (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f) ω * v ω ∂reducedLaw Q) =
      ∫ s in Icc (0 : ℝ) (t : ℝ), timeFluxPair f (P s.toNNReal v) := by
    calc
      _ = timeFluxPair v (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal f) := by
        simp only [timeFluxPair_apply, mul_comm]
      _ = ∫ s in Icc (0 : ℝ) (t : ℝ), timeFluxPair v (T s.toNNReal f) :=
        ((timeFluxPair v).integral_comp_comm hcT.continuousOn.integrableOn_Icc).symm
      _ = _ := by simp_rw [hp]
  exact hleft.trans (hi.symm.trans hright.symm)

/-- The true transpose endpoint has the conservative finite-time flux on all
horizontal H1 tests. The gradient here is the actual gradient of the orbit
primitive; closed-graph integration below identifies it with the integral
of the continuous endpoint gradients used in the source definition. -/
theorem timeFlux_transpose_endpoint_weak
    {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {T P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (t : ℝ≥0) :
    ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β i)) H ∧
      ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
        (∫ ω, T t (β i) ω * v ω ∂reducedLaw Q) =
          -(1 / 2 : ℂ) * ∫ ω, ∑ j,
            ((ω.1 0 j i : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
              2 * ζ * (ω.1 0 j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β i)) ω) * V j ω
            ∂reducedLaw Q := by
  let u := ∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β i)
  obtain ⟨H, hH, hw⟩ := timeFlux_transpose_primitive_graph hP hT (β i) t
  refine ⟨H, hH, ?_⟩
  intro v V hV
  have hc : Integrable (fun ω => ∑ j, (ω.1 0 j i : ℂ) * V j ω)
      (reducedLaw Q) := by
    apply integrable_finset_sum
    intro j _
    exact ((Lp.memLp (complexCoefficientMul Q j i (V j))).ae_eq
      (complexCoefficientMul_coe Q j i (V j))).integrable (by norm_num)
  have hp : Integrable (fun ω => ∑ j, ∑ k,
      (ω.1 0 j k : ℂ) * H k ω * V j ω) (reducedLaw Q) := by
    simpa only [Pi.mul_apply, Finset.sum_mul] using! integrable_finset_sum Finset.univ
      (fun j _ => (memLp_complex_coefficient_flux Q H j).integrable_mul (Lp.memLp (V j)))
  have hd : Integrable (fun ω => u ω * ∑ j, (ω.1 0 j i : ℂ) * V j ω)
      (reducedLaw Q) := by
    have hm : MemLp (fun ω => ∑ j, (ω.1 0 j i : ℂ) * V j ω) 2
        (reducedLaw Q) := by
      apply memLp_finset_sum
      intro j _
      exact (Lp.memLp (complexCoefficientMul Q j i (V j))).ae_eq
        (complexCoefficientMul_coe Q j i (V j))
    exact (Lp.memLp u).integrable_mul hm
  have he : (fun ω => ∑ j,
      ((ω.1 0 j i : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
        2 * ζ * (ω.1 0 j i : ℂ) * u ω) * V j ω) =
      (fun ω => (∑ j, (ω.1 0 j i : ℂ) * V j ω) +
        (∑ j, ∑ k, (ω.1 0 j k : ℂ) * H k ω * V j ω) -
        (2 * ζ) * (u ω * ∑ j, (ω.1 0 j i : ℂ) * V j ω)) := by
    funext ω
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  change _ = -(1 / 2 : ℂ) * ∫ ω, ∑ j,
    ((ω.1 0 j i : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
      2 * ζ * (ω.1 0 j i : ℂ) * u ω) * V j ω ∂reducedLaw Q
  have hs := integral_sub (hc.add hp) (hd.const_mul (2 * ζ))
  have ha := integral_add hc hp
  simp only [Pi.add_apply] at hs ha
  rw [he, hs, ha, integral_const_mul]
  have hinc : (∫ ω, (T t (β i) - β i) ω * v ω ∂reducedLaw Q) =
      (∫ ω, T t (β i) ω * v ω ∂reducedLaw Q) -
        (∫ ω, β i ω * v ω ∂reducedLaw Q) := by
    have hm := (timeFluxPair v).map_sub (T t (β i)) (β i)
    simpa only [timeFluxPair_apply, mul_comm] using! hm
  have hweak := hw v V hV
  rw [hinc, hβ.integral_mul i v V hV] at hweak
  linear_combination hweak

/-- The forward endpoint has its literal finite-time weak flux for every
signed complex force. The primitive gradient is the Bochner integral of the
actual positive-time Euclidean gradient orbit, with no initial domain premise. -/
theorem timeFlux_forward_endpoint_weak
    {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) (j : Fin d)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    let f := β j + ζ • a i j
    let H := ∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s
    (∫ ω, P t f ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∫ ω, ∑ k,
        ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) * H l ω) * V k ω ∂reducedLaw Q) +
      ζ * ∫ ω, ((ω.1 0 i j : ℂ) + ∑ l, (ω.1 0 i l : ℂ) * H l ω) * v ω
        ∂reducedLaw Q := by
  dsimp only
  let f := β j + ζ • a i j
  let H := ∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s
  obtain ⟨K, hK, hw⟩ := hP.integral_orbit_graph_forced f t
  have hKH : K = fun l => H l := hK.unique (hP.integral_orbit_gradient f t)
  rw [hKH] at hw
  have hweak := hw v V hV
  have hinc : (∫ ω, (P t f - f) ω * v ω ∂reducedLaw Q) =
      (∫ ω, P t f ω * v ω ∂reducedLaw Q) -
        (∫ ω, f ω * v ω ∂reducedLaw Q) := by
    simpa only [timeFluxPair_apply, mul_comm] using! (timeFluxPair v).map_sub (P t f) f
  have hinit : (∫ ω, f ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * (∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q) +
        ζ * ∫ ω, (ω.1 0 i j : ℂ) * v ω ∂reducedLaw Q := by
    have hf : (∫ ω, f ω * v ω ∂reducedLaw Q) =
        (∫ ω, β j ω * v ω ∂reducedLaw Q) +
          ζ * ∫ ω, a i j ω * v ω ∂reducedLaw Q := by
      have hm : timeFluxPair v f = timeFluxPair v (β j) + ζ * timeFluxPair v (a i j) := by
        simp only [f, map_add, map_smul, smul_eq_mul]
      simpa only [timeFluxPair_apply, mul_comm] using! hm
    rw [hf, hβ.integral_mul j v V hV]
    congr 2
    apply integral_congr_ae
    filter_upwards [ha i j] with ω hω
    rw [hω]
  have hc : Integrable (fun ω => ∑ k, (ω.1 0 k j : ℂ) * V k ω)
      (reducedLaw Q) := by
    apply integrable_finset_sum
    intro k _
    exact ((Lp.memLp (complexCoefficientMul Q k j (V k))).ae_eq
      (complexCoefficientMul_coe Q k j (V k))).integrable (by norm_num)
  have hp : Integrable (fun ω => ∑ k, ∑ l,
      (ω.1 0 k l : ℂ) * H l ω * V k ω) (reducedLaw Q) := by
    simpa only [Pi.mul_apply, Finset.sum_mul] using! integrable_finset_sum Finset.univ
      (fun k _ => (memLp_complex_coefficient_flux Q (fun l => H l) k).integrable_mul
        (Lp.memLp (V k)))
  have hflux : (∫ ω, ∑ k,
      ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) * H l ω) * V k ω ∂reducedLaw Q) =
      (∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q) +
        ∫ ω, ∑ k, ∑ l, (ω.1 0 k l : ℂ) * H l ω * V k ω ∂reducedLaw Q := by
    rw [← integral_add hc hp]
    congr 1
    funext ω
    simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  have haiv : Integrable (fun ω => (ω.1 0 i j : ℂ) * v ω) (reducedLaw Q) :=
    ((Lp.memLp (complexCoefficientMul Q i j v)).ae_eq
      (complexCoefficientMul_coe Q i j v)).integrable (by norm_num)
  have hhv : Integrable (fun ω => (∑ l, (ω.1 0 i l : ℂ) * H l ω) * v ω)
      (reducedLaw Q) :=
    (memLp_complex_coefficient_flux Q (fun l => H l) i).integrable_mul (Lp.memLp v)
  have hrow : (∫ ω, ((ω.1 0 i j : ℂ) + ∑ l, (ω.1 0 i l : ℂ) * H l ω) * v ω
      ∂reducedLaw Q) = (∫ ω, (ω.1 0 i j : ℂ) * v ω ∂reducedLaw Q) +
        ∫ ω, (∑ l, (ω.1 0 l i : ℂ) * H l ω) * v ω ∂reducedLaw Q := by
    simp_rw [add_mul]
    rw [integral_add haiv hhv]
    congr 1
    apply integral_congr_ae
    filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have hs : ω.1 0 i l = ω.1 0 l i :=
      congrArg (fun M : Mat d => M l i) (hω 0).1
    rw [hs]
  change _ = -(1 / 2 : ℂ) * (∫ ω, ∑ k,
    ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) * H l ω) * V k ω ∂reducedLaw Q) +
    ζ * ∫ ω, ((ω.1 0 i j : ℂ) + ∑ l, (ω.1 0 i l : ℂ) * H l ω) * v ω ∂reducedLaw Q
  rw [hflux, hrow]
  rw [hinc, hinit] at hweak
  linear_combination hweak

/-- Integrating a continuous full horizontal gradient orbit preserves the
actual strong derivative graph, including both endpoints of the interval. -/
theorem timeFlux_integral_gradient
    (u : ℝ≥0 → Lp ℂ 2 (reducedLaw Q))
    (G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hu : Continuous u) (hGc : ∀ k, Continuous (fun t => G t k))
    (hG : ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (u t) (G t)) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ), u s.toNNReal)
      (fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal k) := by
  intro k
  exact HasComplexHorizontalDerivative.integral_of_ae
    (hu.comp continuous_real_toNNReal).continuousOn.integrableOn_Icc
    ((hGc k).comp continuous_real_toNNReal).continuousOn.integrableOn_Icc
    (Eventually.of_forall fun s => hG s.toNNReal k)

private theorem timeFlux_centered_gradient
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q f) G := by
  intro k
  have he (t : ℝ) :
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k)
        (centeredComplexLp Q f) - centeredComplexLp Q f =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k) f - f := by
    change complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector k)
      (f - Lp.const 2 (reducedLaw Q) _) - (f - Lp.const 2 (reducedLaw Q) _) = _
    rw [map_sub, complexTranslation_const]
    abel
  unfold HasComplexHorizontalDerivative
  simp_rw [he]
  exact hG k

/-- The canonical forward primitive gradient equals the integral of any
continuous actual endpoint gradient, including the gradient chosen at zero. -/
theorem timeFlux_forward_integral_gradient_eq
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hGc : ∀ k, Continuous (fun t => G t k))
    (hG : ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (G t)) (t : ℝ≥0) :
    (fun k => (∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) =
      fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal k :=
  (hP.integral_orbit_gradient f t).unique
    (timeFlux_integral_gradient _ G (hP.2.2.1 f) hGc hG t)

private theorem timeFlux_coefficient_product_memLp
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (j k : Fin d)
    (u : Lp ℂ 2 (reducedLaw Q)) :
    MemLp (fun ω => a j k ω * u ω) 2 (reducedLaw Q) := by
  apply (Lp.memLp (complexCoefficientMul Q j k u)).ae_eq
  filter_upwards [complexCoefficientMul_coe Q j k u, ha j k] with ω h1 h2
  simpa only [h2] using! h1

private theorem timeFlux_observation_memLp (hd : 2 ≤ d)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (G : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ ν k, Continuous (fun t => G t ν k))
    (hU : ∀ f, Continuous (fun t => T t f))
    (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :
    MemLp (finiteTimeFluxObservation hd Q ν ζ T β a G t hG hU j) 2
      (reducedLaw Q) := by
  have hm : MemLp (fun ω => ∑ k, a j k ω *
      (∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν k) ω) 2 (reducedLaw Q) :=
    memLp_finset_sum _ (fun k _ => timeFlux_coefficient_product_memLp ha j k _)
  cases ν with
  | inl k =>
    change MemLp (fun ω => a j k ω + (∑ l, a j l ω *
      (∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inl k) l) ω) - 0) 2 _
    simpa only [sub_zero] using! (Lp.memLp (a j k)).add hm
  | inr u =>
    have hc := (timeFlux_coefficient_product_memLp ha j ⟨0, by omega⟩
      (∫ s in Icc (0 : ℝ) (t : ℝ), transposeEndpoint Q ⟨0, by omega⟩ T β s.toNNReal)).const_mul
        (2 * ζ)
    change MemLp (fun ω => a j ⟨0, by omega⟩ ω + (∑ k, a j k ω *
      (∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal (.inr u) k) ω) -
      2 * ζ * a j ⟨0, by omega⟩ ω *
        (∫ s in Icc (0 : ℝ) (t : ℝ),
          transposeEndpoint Q ⟨0, by omega⟩ T β s.toNNReal) ω) 2 _
    simpa only [Pi.add_apply, Pi.sub_apply, mul_assoc] using!
      ((Lp.memLp (a j ⟨0, by omega⟩)).add hm).sub hc

private theorem timeFlux_observation_raw (hd : 2 ≤ d)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a)
    (G : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ ν k, Continuous (fun t => G t ν k))
    (hU : ∀ f, Continuous (fun t => T t f))
    (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :
    finiteTimeFluxObservation hd Q ν ζ T β a G t hG hU j =ᵐ[reducedLaw Q]
      fun ω => (ω.1 0 j (ν.elim id (fun _ => ⟨0, by omega⟩)) : ℂ) +
        (∑ k, (ω.1 0 j k : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), G s.toNNReal ν k) ω) -
        ν.elim (fun _ => 0) (fun _ => 2 * ζ * (ω.1 0 j ⟨0, by omega⟩ : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β ⟨0, by omega⟩)) ω) := by
  filter_upwards [ae_all_iff.mpr (fun k => ha j k)] with ω hω
  cases ν <;> simp only [finiteTimeFluxObservation, Sum.elim_inl, Sum.elim_inr,
    transposeEndpoint, hω]

/-- Exact finite-time forward and true-transpose flux construction for the
smooth stationary endpoint data, with the original graph dependency binder. -/
theorem node_e_u3A_time_u2D_flux_of_deps
    (hdeps : node_stationary_u2D_analytic_u2D_semigroupStmt) :
    node_e_u3A_time_u2D_fluxStmt := by
  intro d hd D Q hQ β a μ hβ ha _hμ ζ P T hP hT
  let i : Fin d := ⟨0, by omega⟩
  have hP : IsComplexEnvironmentSemigroup Q i ζ P := by
    have hc := (((hdeps d hd D).1 Q hQ).1 ζ).1
    exact (hP.unique hc).symm ▸ hc
  obtain ⟨Gf, hGfc, hGf⟩ : ∃ Gf : Fin d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j k, Continuous (fun t => Gf j t k)) ∧
      ∀ j t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t (β j + ζ • a i j)) (Gf j t) := by
    choose Gf hGc hG using timeFlux_forward_continuous_gradient hβ ha hP
    exact ⟨Gf, hGc, hG⟩
  obtain ⟨Gt, hGtc, hGt⟩ := timeFlux_transpose_continuous_gradient hβ hP hT i
  let G : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q) :=
    fun t ν => ν.elim (fun j => Gf j t) (fun _ => Gt t)
  have hGc (ν : FluxIndex d) (k : Fin d) : Continuous (fun t => G t ν k) := by
    cases ν with
    | inl j => exact hGfc j k
    | inr u => exact hGtc k
  have hUc : ∀ f, Continuous (fun t => T t f) := hT.continuous_apply hP
  let F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q) := fun t ν j =>
    (timeFlux_observation_memLp hd ha G hGc hUc t ν j).toLp
      (finiteTimeFluxObservation hd Q ν ζ T β a G t hGc hUc j)
  have hF (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :
      (F t ν j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        finiteTimeFluxObservation hd Q ν ζ T β a G t hGc hUc j :=
    (timeFlux_observation_memLp hd ha G hGc hUc t ν j).coeFn_toLp
  have hFr (t : ℝ≥0) (ν : FluxIndex d) (j : Fin d) :=
    (hF t ν j).trans (timeFlux_observation_raw hd ha G hGc hUc t ν j)
  refine ⟨G, F, ⟨hGc, hUc, ?_, hF⟩, ?_⟩
  · intro t ν
    cases ν with
    | inl j => exact timeFlux_centered_gradient (hGf j t)
    | inr u => exact hGt t
  · intro t v V hV
    constructor
    · intro j
      have hw := timeFlux_forward_endpoint_weak hβ ha hP t j v V hV
      have he := timeFlux_forward_integral_gradient_eq hP (β j + ζ • a i j)
        (Gf j) (hGfc j) (hGf j) t
      dsimp only at hw
      have hrow (k : Fin d) : (fun ω => F t (.inl j) k ω) =ᵐ[reducedLaw Q]
          fun ω => (ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j + ζ • a i j) s) l) ω := by
        have hh := hFr t (.inl j) k
        simp only [Sum.elim_inl, sub_zero] at hh
        have hk := congrFun he
        simp only at hk
        simpa only [hk, G, Sum.elim_inl] using! hh
      have hsum : (∫ ω, ∑ k, F t (.inl j) k ω * V k ω ∂reducedLaw Q) =
          ∫ ω, ∑ k, ((ω.1 0 k j : ℂ) + ∑ l, (ω.1 0 k l : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j + ζ • a i j) s) l) ω) *
              V k ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hrow] with ω hω
        simp only [hω]
      have hforce : (∫ ω, F t (.inl j) i ω * v ω ∂reducedLaw Q) =
          ∫ ω, ((ω.1 0 i j : ℂ) + ∑ l, (ω.1 0 i l : ℂ) *
            ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j + ζ • a i j) s) l) ω) *
              v ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [hrow i] with ω hω
        rw [hω]
      rw [hsum, hforce]
      exact hw
    · obtain ⟨H, hH, hw⟩ := timeFlux_transpose_endpoint_weak hβ hP hT t
      have he : H = fun k => ∫ s in Icc (0 : ℝ) (t : ℝ), Gt s.toNNReal k :=
        hH.unique (timeFlux_integral_gradient _ Gt (hUc (β i)) hGtc hGt t)
      have hrow (j : Fin d) : (fun ω => F t (.inr ()) j ω) =ᵐ[reducedLaw Q]
          fun ω => (ω.1 0 j i : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
            2 * ζ * (ω.1 0 j i : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β i)) ω := by
        have hh := hFr t (.inr ()) j
        simpa only [Sum.elim_inr, G, he] using! hh
      have hsum : (∫ ω, ∑ j, F t (.inr ()) j ω * V j ω ∂reducedLaw Q) =
          ∫ ω, ∑ j, ((ω.1 0 j i : ℂ) + (∑ k, (ω.1 0 j k : ℂ) * H k ω) -
            2 * ζ * (ω.1 0 j i : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), T s.toNNReal (β i)) ω) * V j ω
                ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hrow] with ω hω
        simp only [hω]
      rw [hsum]
      exact hw v V hV

end EinsteinFull.Blueprint
