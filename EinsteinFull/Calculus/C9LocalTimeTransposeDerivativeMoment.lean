import EinsteinFull.Work.W2.TransposeResolventGradientContinuitySupport
import EinsteinFull.Work.W2.TransposeAllDataHorizonEnergySupport
import EinsteinFull.Calculus.C9LocalTimeTransposeTrace
import EinsteinFull.Calculus.C10LocalTimeTransposeGradientCylinder
import EinsteinFull.Calculus.C10LocalTimeEnergyMoment
import EinsteinFull.Calculus.C4LocalTimeDerivativeMoment

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/- EXACT SUPERVISOR TARGET (comment only).
theorem local_time_transpose_derivative_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν = .inr true →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal))
-/
/-- The vector fundamental theorem identifies the derivative of a genuine
transpose graph orbit at every positive real time. -/
theorem local_time_transpose_orbit_hasDerivAt
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => T s.toNNReal f) (T t.toNNReal g) t := by
  have hc : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : (fun s : ℝ => T s.toNNReal f) =ᶠ[𝓝 t]
      (fun s : ℝ => (∫ r in (0 : ℝ)..s, T r.toNNReal g) + f) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have hi := hT.integral_orbit_eq_sub hP hfg s.toNNReal
    rw [Real.coe_toNNReal s hs.le] at hi
    rw [hi, sub_add_cancel]
  exact (hd.add_const f).congr_of_eventuallyEq he

/-- The transpose endpoint has common gradient witnesses and a derivative
which is the actual transpose evolution of the drift's generator image.
The restart identity also holds for this same derivative witness. -/
theorem local_time_transpose_endpoint_orbit_witnesses
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsComplexTransposeGeneratorPair Q ⟨0, by omega⟩ ζ (β ⟨0, by omega⟩) g ∧
      (∀ t : ℝ≥0,
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q (.inr true) ζ P T β a μ t) (G t) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q (.inr true) ζ P T β a μ t) (G t)) ∧
      (∀ t : ℝ≥0, 0 < (t : ℝ) →
        HasDerivAt (fun r : ℝ => indexedEndpoint hd Q (.inr true) ζ P T β a μ r.toNNReal)
          (T t g) (t : ℝ)) ∧
      (∀ s t : ℝ≥0, T (s + t) g = T t (T s g)) := by
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator
    (i := (⟨0, by omega⟩ : Fin d)) (ζ := ζ) hβ ⟨0, by omega⟩
  obtain ⟨G, ⟨hG, _⟩, _⟩ := hT.existsUnique_continuous_gradient_orbit hP hg
  refine ⟨g, fun t j => G t j, hg, ?_, ?_, ?_⟩
  · intro t
    exact ⟨hG t, hG t⟩
  · intro t ht
    simpa only [indexedEndpoint, transposeEndpoint, Real.toNNReal_coe] using
      local_time_transpose_orbit_hasDerivAt hP hT hg ht
  · intro s t
    rw [add_comm s t, hT.add hP, ContinuousLinearMap.comp_apply]

/-- The Lp-growth input controls every later transpose slice by an earlier
slice, with its structural constant fixed before the law and the force.
In the derivative estimate the earlier slice is chosen to be exactly t/8. -/
theorem local_time_transpose_slice_moment_of_growth
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (a s t : ℝ≥0),
      a ≤ s → s ≤ t →
      MemLp (T a f) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (T s f) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (T s f) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (T a f) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨C, hC, hbound⟩ := h1 d Λ₀ r₀ p hd hp
  refine ⟨C, hC, ?_⟩
  intro Q i ζ P T hP hT f a s t has hst hf
  have hg := (hbound Q i ζ P T hP hT).1 (s - a) (T a f) hf
  have he : T (s - a) (T a f) = T s f := by
    rw [← ContinuousLinearMap.comp_apply, ← hT.add hP, tsub_add_cancel_of_le has]
  rw [he] at hg
  refine ⟨hg.2.1, ?_⟩
  have hn := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.ne_top) hg.2.2.2.2.1
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hn
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ ENNReal.toReal_nonneg)
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left
    (show ((s - a : ℝ≥0) : ℝ) ≤ (t : ℝ) from
      NNReal.coe_le_coe.mpr ((tsub_le_self).trans hst))
    (mul_nonneg hC.le (sq_nonneg _))

/-- A stationary probability average of the actual transpose orbit has the
same slice growth bound. This applies to normalized space-time cylinders
and keeps the spatial averaging measure arbitrary. -/
theorem local_time_transpose_cylinder_moment_of_growth
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ p : ℝ) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (a t : ℝ≥0),
      MemLp (T a f) (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν]
      (κ : Measure (Vec d)) [IsProbabilityMeasure κ],
      (∀ᵐ s ∂ν, a ≤ s.toNNReal ∧ s.toNNReal ≤ t) →
    ∀ W : ℝ × FieldPair d → ℂ, Measurable W →
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
      let A := fun ω : FieldPair d => Real.sqrt
        (∫ s, ∫ y, ‖W (s, translate y ω)‖ ^ 2 ∂κ ∂ν)
      MemLp A (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm A (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (T a f) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨C, hC, hslice⟩ :=
    local_time_transpose_slice_moment_of_growth h1 d hd Λ₀ r₀ p hp
  refine ⟨C, hC, ?_⟩
  intro Q i ζ P T hP hT f a t hf ν hν κ hκ hsupp W hW heW
  apply local_time_stationary_square_average_memLp Q ν κ p
    (Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) *
      (eLpNorm (T a f) (ENNReal.ofReal p) (reducedLaw Q)).toReal)
    hp (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg) W hW
  filter_upwards [hsupp] with s hs
  obtain ⟨hmem, hnorm⟩ := hslice Q i ζ P T hP hT f a s.toNNReal t hs.1 hs.2 hf
  refine ⟨(memLp_congr_ae (heW s)).2 hmem, ?_⟩
  rw [eLpNorm_congr_ae (heW s)]
  exact hnorm

/-- The joint transpose output estimate only requires graph and gradient
identities almost everywhere in time, as supplied by all-data horizon energy. -/
theorem local_time_transpose_ae_joint_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G H : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ᵐ s ∂volume.restrict (Icc b c), IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ᵐ s ∂volume.restrict (Icc b c),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    (hout : ∀ᵐ s ∂volume.restrict (Icc b c),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (v s) (H s))
    {W V : ℝ × FieldPair d → ℂ} {D E : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V) (hD : ∀ j, Measurable (D j)) (hE : ∀ j, Measurable (E j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    (heE : ∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] H s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) {ε : ℝ} (hε : 0 < ε) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2)) +
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) := by
  intro L
  let := reducedLaw_probability Q
  let R : Vec d → ℝ := fun x =>
    φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)
  have hRm : Measurable R := by
    have hd j : Continuous (coordinateDerivative j φ) :=
      ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
    exact (hφ.1.continuous.measurable.pow_const 2).div_const _ |>.add
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => (hd j).measurable.pow_const 2))
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d => U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hweight {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * ‖U (p.1, translate x p.2)‖ ^ 2) :=
    ((hψ.comp measurable_snd).mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hsum {J : Fin d → ℝ × FieldPair d → ℂ} (hJ : ∀ j, Measurable (J j))
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * (∑ j, ‖J j (p.1, translate x p.2)‖ ^ 2)) :=
    ((hψ.comp measurable_snd).mul (Finset.measurable_sum _ fun j _ =>
      ((hshift (hJ j)).norm.pow_const 2))).stronglyMeasurable.integral_prod_right'.measurable
  let A := fun p : ℝ × FieldPair d =>
    (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (p.1, translate x p.2)‖ ^ 2)
  let B := fun p : ℝ × FieldPair d =>
    ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (p.1, translate x p.2)‖ ^ 2)) +
      (∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
        (∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (p.1, translate x p.2)‖ ^ 2))
  have hA : Measurable A := measurable_const.mul
    (hweight hV (hφ.1.continuous.measurable.pow_const 2))
  have hB : Measurable B := (measurable_const.mul
    (hsum hE (hφ.1.continuous.measurable.pow_const 2))).add
    (((hRm.comp measurable_snd).mul
      ((measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        ((hshift (hD j)).norm.pow_const 2))).add
        (measurable_const.mul ((hshift hW).norm.pow_const 2)))).stronglyMeasurable.integral_prod_right'.measurable)
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [hgen, hgrad, hout] with s hgs hds hes
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  have hee j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hE j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (H s j)).measurable (heE j s)
  filter_upwards [local_time_transpose_physical_output_young hgs hds hes,
    hew, hev, ae_all_iff.mpr hed, ae_all_iff.mpr hee] with ω hy hw hv hd he
  have heall := ae_all_iff.mpr he
  have hdall := ae_all_iff.mpr hd
  have hmass : (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) =
      ∫ x, φ x ^ 2 * ‖(v s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    change V (s, translate x ω) = _ at hx
    rw [hx]
  have hsum_eq {J : Fin d → ℝ × FieldPair d → ℂ} {K : Fin d → Lp ℂ 2 (reducedLaw Q)}
      (hJK : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, J j (s, translate x ω) = K j (translate x ω))
      (ψ : Vec d → ℝ) :
      (∫ x, ψ x * (∑ j, ‖J j (s, translate x ω)‖ ^ 2)) =
        ∫ x, ψ x * (∑ j, ‖K j (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hJK] with x hx
    simp only [hx]
  have hrest : (∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
      (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
      2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) =
      ∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
        (∑ j, ‖G s j (translate x ω)‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖(u s) (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hdall, hw] with x hd hw
    change W (s, translate x ω) = _ at hw
    change ∀ j, D j (s, translate x ω) = _ at hd
    simp only [hd, hw]
  change (1 / 2 : ℝ) * _ ≤ ε * _ + _
  rw [hmass, hsum_eq heall, hrest]
  exact hy φ hφ ε hε

/-- Applied to a genuine graph orbit, the output estimate uses the canonical
all-data gradient of its derivative. No generator-domain assumption on the
generator image is needed. -/
theorem local_time_transpose_derivative_orbit_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {t : ℝ} (ht : 0 ≤ t)
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {W V : ℝ × FieldPair d → ℂ} {D E : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V) (hD : ∀ j, Measurable (D j)) (hE : ∀ j, Measurable (E j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T f s j)
    (heE : ∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T g s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) {ε : ℝ} (hε : 0 < ε) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc 0 t),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2)) +
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) := by
  have hgrad := (hT.gradientOrbit_horizon_energy hP f ⟨t, ht⟩).2.1
  have hout := (hT.gradientOrbit_horizon_energy hP g ⟨t, ht⟩).2.1
  rw [restrict_Ioc_eq_restrict_Icc] at hgrad hout
  exact local_time_transpose_ae_joint_output_young
    (Filter.Eventually.of_forall (fun s => hT.map_generator hP hfg s.toNNReal))
    hgrad hout hW hV hD hE heW heV heD heE hφ hε


private def localTimeLpRestrict {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (f : Lp E 2 μ) : Lp E 2 (μ.restrict A) :=
  ((Lp.memLp f).restrict A).toLp f

private theorem localTimeLpRestrict_continuous {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) : Continuous (localTimeLpRestrict (E := E) μ A) := by
  apply continuous_iff_continuousAt.mpr
  intro f
  rw [ContinuousAt]
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun g : Lp E 2 μ => (g : Ω → E))
    (fun g => (Lp.memLp g).restrict A) f ((Lp.memLp f).restrict A)).mpr
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (fun g : Lp E 2 μ => g) f).mp
    tendsto_id
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ => bot_le) (fun g => eLpNorm_mono_measure _ Measure.restrict_le_self)

private theorem localTimeLpRestrict_norm_sq {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (f : Lp E 2 μ) :
    ‖localTimeLpRestrict μ A f‖ ^ 2 = ∫ ω in A, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).restrict A).coeFn_toLp] with ω hω
  exact congrArg (fun z : E => ‖z‖ ^ 2) hω

private theorem localTimeLpRestrict_norm_le {Ω E : Type*} [NormedAddCommGroup E] [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Set Ω) (f : Lp E 2 μ) :
    ‖localTimeLpRestrict μ A f‖ ≤ ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  change eLpNorm (((Lp.memLp f).restrict A).toLp f) 2 (μ.restrict A) ≤ _
  rw [eLpNorm_congr_ae ((Lp.memLp f).restrict A).coeFn_toLp]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

/-- Conditional quadratic averages are stable under bounded L2 approximation.
The environment event is arbitrary, so this limit step preserves pathwise
inequalities after testing them on measurable events. -/
theorem local_time_conditional_quadratic_average_tendsto
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) (ν : Measure X) [IsFiniteMeasure ν] (A : Set Ω)
    {u : ℕ → X → Lp ℂ 2 μ} {v : X → Lp ℂ 2 μ} {M : ℝ}
    (hu : ∀ n, AEStronglyMeasurable (u n) ν)
    (hb : ∀ n, ∀ᵐ x ∂ν, ‖u n x‖ ≤ M)
    (hc : ∀ᵐ x ∂ν, Tendsto (fun n => u n x) atTop (𝓝 (v x))) :
    Tendsto (fun n => ∫ x, ∫ ω in A, ‖u n x ω‖ ^ 2 ∂μ ∂ν)
      atTop (𝓝 (∫ x, ∫ ω in A, ‖v x ω‖ ^ 2 ∂μ ∂ν)) := by
  simp_rw [← localTimeLpRestrict_norm_sq]
  apply tendsto_integral_of_dominated_convergence (fun _ => M ^ 2)
  · intro n
    exact (((localTimeLpRestrict_continuous μ A).comp_aestronglyMeasurable
      (hu n)).norm.pow 2)
  · exact integrable_const _
  · intro n
    filter_upwards [hb n] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) ((localTimeLpRestrict_norm_le μ A _).trans hx) 2
  · filter_upwards [hc] with x hx
    exact (((localTimeLpRestrict_continuous μ A).tendsto (v x)).comp hx).norm.pow 2

/-- Every finite conditional space-time average of the actual transpose orbit
is continuous under L2 approximation of its initial datum. The averaging
measure may in particular be a space-time cylinder. -/
theorem local_time_transpose_conditional_cylinder_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f : ℕ → Lp ℂ 2 (reducedLaw Q)} {g : Lp ℂ 2 (reducedLaw Q)}
    (hf : Tendsto f atTop (𝓝 g))
    (ν : Measure (ℝ × Vec d)) [IsFiniteMeasure ν] (A : Set (FieldPair d))
    (t : ℝ≥0) (hν : ∀ᵐ q ∂ν, q.1.toNNReal ≤ t) :
    Tendsto (fun n => ∫ q, ∫ ω in A,
      ‖(T q.1.toNNReal (f n)) (translate q.2 ω)‖ ^ 2 ∂reducedLaw Q ∂ν)
      atTop (𝓝 (∫ q, ∫ ω in A,
        ‖(T q.1.toNNReal g) (translate q.2 ω)‖ ^ 2 ∂reducedLaw Q ∂ν)) := by
  let μ := reducedLaw Q
  let τ := complexTranslation μ (reducedLaw_stationary Q)
  have he (v : Lp ℂ 2 μ) (q : ℝ × Vec d) :
      (∫ ω in A, ‖(τ q.2 (T q.1.toNNReal v)) ω‖ ^ 2 ∂μ) =
        ∫ ω in A, ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae
      (coeFn_complexTranslation μ (reducedLaw_stationary Q) q.2 (T q.1.toNNReal v))]
      with ω hω
    rw [hω]
  have hrewrite (v : Lp ℂ 2 μ) :
      (∫ q, ∫ ω in A, ‖(τ q.2 (T q.1.toNNReal v)) ω‖ ^ 2 ∂μ ∂ν) =
        ∫ q, ∫ ω in A, ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ ∂ν :=
    integral_congr_ae (ae_of_all _ fun q => he v q)
  have hlim : Tendsto (fun n => ∫ q, ∫ ω in A,
      ‖(τ q.2 (T q.1.toNNReal (f n))) ω‖ ^ 2 ∂μ ∂ν) atTop
      (𝓝 (∫ q, ∫ ω in A, ‖(τ q.2 (T q.1.toNNReal g)) ω‖ ^ 2 ∂μ ∂ν)) := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto f hf).exists_norm_le
    apply local_time_conditional_quadratic_average_tendsto μ ν A
      (M := Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) * max R 0)
    · intro n
      exact ((continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
        (continuous_snd.prodMk (((hT.continuous_apply hP (f n)).comp
          continuous_real_toNNReal).comp continuous_fst))).aestronglyMeasurable
    · intro n
      filter_upwards [hν] with q hq
      rw [norm_complexTranslation]
      exact ((T q.1.toNNReal).le_opNorm (f n)).trans
        (mul_le_mul ((hT.norm_le hP _).trans (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hq) (complexForceShift_nonneg Q ζ))))
          ((hR _ (mem_range_self n)).trans (le_max_left _ _))
          (norm_nonneg _) (Real.exp_nonneg _))
    · exact ae_of_all _ fun q =>
        ((τ q.2).continuous.tendsto (T q.1.toNNReal g)).comp
          (((T q.1.toNNReal).continuous.tendsto g).comp hf)
  simpa only [hrewrite] using hlim

private theorem conditional_quadratic_average_fubini
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {u : X → Lp ℂ 2 μ} (hu : Integrable (fun x => ‖u x‖ ^ 2) ν)
    {U : X × Ω → ℂ} (hU : Measurable U)
    (heU : ∀ x, (fun ω => U (x, ω)) =ᵐ[μ] u x) :
    Integrable (fun ω => ∫ x, ‖U (x, ω)‖ ^ 2 ∂ν) μ ∧
      ∀ A : Set Ω,
        (∫ ω in A, ∫ x, ‖U (x, ω)‖ ^ 2 ∂ν ∂μ) =
          ∫ x, ∫ ω in A, ‖u x ω‖ ^ 2 ∂μ ∂ν := by
  have hi := integrable_sq_joint_l2_representative hu hU heU
  refine ⟨hi.integral_prod_right, fun A => ?_⟩
  have hA : Integrable (fun p : X × Ω => ‖U p‖ ^ 2) (ν.prod (μ.restrict A)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap hA]
  apply integral_congr_ae
  exact ae_of_all _ fun x => integral_congr_ae
    ((ae_restrict_of_ae (heU x)).mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)

private theorem localTimeLpRestrict_lipschitz {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] (μ : Measure Ω) (A : Set Ω) :
    LipschitzWith 1 (localTimeLpRestrict μ A : Lp E 2 μ → Lp E 2 (μ.restrict A)) := by
  have hsub (f g : Lp E 2 μ) :
      localTimeLpRestrict μ A f - localTimeLpRestrict μ A g =
        localTimeLpRestrict μ A (f - g) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (localTimeLpRestrict μ A f) (localTimeLpRestrict μ A g),
      ((Lp.memLp f).restrict A).coeFn_toLp, ((Lp.memLp g).restrict A).coeFn_toLp,
      ((Lp.memLp (f - g)).restrict A).coeFn_toLp,
      ae_restrict_of_ae (Lp.coeFn_sub f g)] with ω hsub hf hg hfg hdiff
    change (localTimeLpRestrict μ A f) ω = f ω at hf
    change (localTimeLpRestrict μ A g) ω = g ω at hg
    change (localTimeLpRestrict μ A (f - g)) ω = (f - g) ω at hfg
    calc
      _ = (localTimeLpRestrict μ A f) ω - (localTimeLpRestrict μ A g) ω := hsub
      _ = f ω - g ω := by rw [hf, hg]
      _ = (f - g) ω := hdiff.symm
      _ = _ := hfg.symm
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simpa only [dist_eq_norm, hsub, NNReal.coe_one, one_mul] using
    localTimeLpRestrict_norm_le μ A (f - g)

private theorem localTimeLpRestrict_zero {Ω E : Type*}
    [MeasurableSpace Ω] [NormedAddCommGroup E] (μ : Measure Ω) (A : Set Ω) :
    localTimeLpRestrict μ A (0 : Lp E 2 μ) = 0 := by
  apply Lp.ext
  filter_upwards [((Lp.memLp (0 : Lp E 2 μ)).restrict A).coeFn_toLp,
    ae_restrict_of_ae (Lp.coeFn_zero E 2 μ), Lp.coeFn_zero E 2 (μ.restrict A)] with ω hω hμ hA
  exact hω.trans (hμ.trans hA.symm)

/-- A conditional quadratic time average is continuous in the actual time L2
norm. In particular this applies to gradient resolvent approximations, where
pointwise-in-time convergence is unavailable. -/
theorem local_time_conditional_timeL2_tendsto
    {S Ω E : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    [NormedAddCommGroup E] (ν : Measure S) (μ : Measure Ω) (A : Set Ω)
    {H : E → Lp ℂ 2 μ} (hH : LipschitzWith 1 H) (hH0 : H 0 = 0)
    {f : ℕ → Lp E 2 ν} {g : Lp E 2 ν} (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => ∫ s, ∫ ω in A, ‖H (f n s) ω‖ ^ 2 ∂μ ∂ν)
      atTop (𝓝 (∫ s, ∫ ω in A, ‖H (g s) ω‖ ^ 2 ∂μ ∂ν)) := by
  let K := fun v => localTimeLpRestrict μ A (H v)
  have hK : LipschitzWith 1 K := by
    simpa only [K, Function.comp_def, mul_one] using (localTimeLpRestrict_lipschitz μ A).comp hH
  have hK0 : K 0 = 0 := by
    change localTimeLpRestrict μ A (H 0) = 0
    rw [hH0, localTimeLpRestrict_zero]
  have he (v : Lp E 2 ν) :
      ‖hK.compLp hK0 v‖ ^ 2 = ∫ s, ∫ ω in A, ‖H (v s) ω‖ ^ 2 ∂μ ∂ν := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hK.coeFn_compLp hK0 v] with s hs
    rw [real_inner_self_eq_norm_sq, hs]
    exact localTimeLpRestrict_norm_sq μ A (H (v s))
  simpa only [Function.comp_apply, he] using ((hK.continuous_compLp hK0).tendsto g |>.comp hf).norm.pow 2

/-- The conditional gradient mass on any part of a finite horizon is stable
under the actual resolvent approximation, for arbitrary initial data. -/
theorem local_time_transpose_conditional_gradient_mass_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (J : Set ℝ) (A : Set (FieldPair d)) (x : Vec d) (j : Fin d) :
    Tendsto (fun n => ∫ s in J,
      ∫ ω in A, ‖(complexTransposeGradientOrbit Q T
        (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t)) atTop
      (𝓝 (∫ s in J,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t))) := by
  let μ := reducedLaw Q
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let τ := complexTranslation μ (reducedLaw_stationary Q) x
  let H := fun v : PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ) => τ (v j)
  have hH : LipschitzWith 1 H := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    simp only [NNReal.coe_one, one_mul, dist_eq_norm]
    change ‖τ (v j) - τ (w j)‖ ≤ ‖v - w‖
    rw [← map_sub, norm_complexTranslation]
    exact PiLp.norm_apply_le (v - w) j
  have hH0 : H 0 = 0 := by simp [H, τ]
  let F := fun v : Lp ℂ 2 μ =>
    localTimeLpRestrict ν J ((hT.gradientOrbit_horizon_energy hP v t).1.toLp
      (complexTransposeGradientOrbit Q T v))
  have he (v : Lp ℂ 2 μ) :
      (∫ s in J, ∫ ω in A, ‖H (F v s) ω‖ ^ 2 ∂μ ∂ν) =
        ∫ s in J, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2 ∂μ ∂ν := by
    apply integral_congr_ae
    have hr := ((Lp.memLp ((hT.gradientOrbit_horizon_energy hP v t).1.toLp
      (complexTransposeGradientOrbit Q T v))).restrict J).coeFn_toLp
    filter_upwards [hr, ae_restrict_of_ae (hT.gradientOrbit_horizon_energy hP v t).1.coeFn_toLp]
      with s hs ht
    change F v s = _ at hs
    rw [hs, ht]
    apply integral_congr_ae
    exact (ae_restrict_of_ae (coeFn_complexTranslation μ (reducedLaw_stationary Q) x
      (complexTransposeGradientOrbit Q T v s j))).mono fun ω hω =>
        congrArg (fun z : ℂ => ‖z‖ ^ 2) hω
  have hlim := local_time_conditional_timeL2_tendsto (ν.restrict J) μ A hH hH0
    (((localTimeLpRestrict_continuous ν J).tendsto _).comp
      (hT.tendsto_Lp_gradientOrbit_resolvent hP f t))
  change Tendsto (fun n => ∫ s in J, ∫ ω in A,
    ‖H (F (complexTransposeResolventApproximation Q i ζ n f) s) ω‖ ^ 2 ∂μ ∂ν)
    atTop (𝓝 (∫ s in J, ∫ ω in A, ‖H (F f s) ω‖ ^ 2 ∂μ ∂ν)) at hlim
  simpa only [he] using hlim

private theorem translated_conditional_gradient_time_mass
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) (A : Set (FieldPair d))
    (F : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)) 2 ν) (j : Fin d) :
    Continuous (fun x : Vec d => ∫ s, ∫ ω in A,
      ‖(F s j) (translate x ω)‖ ^ 2 ∂μ ∂ν) ∧
    ∀ x : Vec d, 0 ≤ (∫ s, ∫ ω in A, ‖(F s j) (translate x ω)‖ ^ 2 ∂μ ∂ν) ∧
      (∫ s, ∫ ω in A, ‖(F s j) (translate x ω)‖ ^ 2 ∂μ ∂ν) ≤ ‖F‖ ^ 2 := by
  let τ := complexTranslation μ hμ
  let m := fun (x : Vec d) s => ‖localTimeLpRestrict μ A (τ x (F s j))‖ ^ 2
  have he x s : m x s = ∫ ω in A, ‖(F s j) (translate x ω)‖ ^ 2 ∂μ := by
    change ‖localTimeLpRestrict μ A (τ x (F s j))‖ ^ 2 = _
    rw [localTimeLpRestrict_norm_sq]
    apply integral_congr_ae
    exact (ae_restrict_of_ae (coeFn_complexTranslation μ hμ x (F s j))).mono
      fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω
  have hm x : AEStronglyMeasurable (m x) ν := by
    have hp : Continuous (fun v : PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ) => v j) :=
      (PiLp.continuous_apply 2 _ j)
    exact (((localTimeLpRestrict_continuous μ A).comp
      ((τ x).continuous.comp hp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable F)).norm.pow 2
  have hb x s : m x s ≤ ‖F s‖ ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact ((localTimeLpRestrict_norm_le μ A _).trans
      (by rw [norm_complexTranslation]; exact PiLp.norm_apply_le (F s) j))
  have hi : Integrable (fun s => ‖F s‖ ^ 2) ν :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  have hmi x : Integrable (m x) ν :=
    hi.mono' (hm x) (ae_of_all _ fun s => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb x s)
  have hc : Continuous (fun x => ∫ s, m x s ∂ν) := by
    apply continuous_of_dominated hm (fun x => ae_of_all _ fun s => ?_) hi
      (ae_of_all _ fun s => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hb x s
    · exact ((localTimeLpRestrict_continuous μ A).comp
        ((continuous_complexTranslation μ hμ).comp
          (continuous_id.prodMk continuous_const))).norm.pow 2
  have heF : (∫ s, ‖F s‖ ^ 2 ∂ν) = ‖F‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  simp_rw [he] at hc
  refine ⟨hc, fun x => ⟨integral_nonneg (fun s => integral_nonneg (fun ω => sq_nonneg _)), ?_⟩⟩
  rw [← heF]
  simpa only [he] using integral_mono_ae (hmi x) hi (ae_of_all _ (hb x))

private theorem conditional_gradient_cylinder_timeL2_tendsto
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    (A : Set (FieldPair d)) (j : Fin d)
    {F : ℕ → Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)) 2 ν}
    {G : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)) 2 ν}
    (hF : Tendsto F atTop (𝓝 G)) :
    Tendsto (fun n => ∫ x, ∫ s, ∫ ω in A,
      ‖(F n s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ) atTop
      (𝓝 (∫ x, ∫ s, ∫ ω in A, ‖(G s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto F hF).exists_norm_le
  apply tendsto_integral_of_dominated_convergence (fun _ => R ^ 2)
  · intro n
    exact (translated_conditional_gradient_time_mass μ hμ ν A (F n) j).1.aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg
        ((translated_conditional_gradient_time_mass μ hμ ν A (F n) j).2 x).1]
      exact ((translated_conditional_gradient_time_mass μ hμ ν A (F n) j).2 x).2.trans
        (pow_le_pow_left₀ (norm_nonneg _) (hR _ (mem_range_self n)) 2)
  · exact ae_of_all _ fun x => by
      let τ := complexTranslation μ hμ x
      let H := fun v : PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ) => τ (v j)
      have hH : LipschitzWith 1 H := by
        apply LipschitzWith.of_dist_le_mul
        intro v w
        simp only [NNReal.coe_one, one_mul, dist_eq_norm]
        change ‖τ (v j) - τ (w j)‖ ≤ ‖v - w‖
        rw [← map_sub, norm_complexTranslation]
        exact PiLp.norm_apply_le (v - w) j
      have hH0 : H 0 = 0 := by simp [H, τ]
      have he (v : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)) 2 ν) :
          (∫ s, ∫ ω in A, ‖H (v s) ω‖ ^ 2 ∂μ ∂ν) =
            ∫ s, ∫ ω in A, ‖(v s j) (translate x ω)‖ ^ 2 ∂μ ∂ν := by
        apply integral_congr_ae
        exact ae_of_all _ fun s => integral_congr_ae
          ((ae_restrict_of_ae (coeFn_complexTranslation μ hμ x (v s j))).mono
            fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)
      simpa only [he] using local_time_conditional_timeL2_tendsto ν μ A hH hH0 hF

/-- Conditional spatially averaged gradient cylinders converge under actual
resolvent approximation of arbitrary initial data. Both the environment event
and the part of the time horizon can be chosen freely. -/
theorem local_time_transpose_conditional_gradient_cylinder_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (J : Set ℝ) (A : Set (FieldPair d)) (j : Fin d)
    (κ : Measure (Vec d)) [IsFiniteMeasure κ] :
    Tendsto (fun n => ∫ x, ∫ s in J,
      ∫ ω in A, ‖(complexTransposeGradientOrbit Q T
        (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t) ∂κ) atTop
      (𝓝 (∫ x, ∫ s in J,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t) ∂κ)) := by
  let μ := reducedLaw Q
  let ν := volume.restrict (Ioc (0 : ℝ) t)
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let F := fun v : Lp ℂ 2 μ =>
    localTimeLpRestrict ν J ((hT.gradientOrbit_horizon_energy hP v t).1.toLp
      (complexTransposeGradientOrbit Q T v))
  have he (v : Lp ℂ 2 μ) :
      (∫ x, ∫ s in J, ∫ ω in A, ‖(F v s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ) =
        ∫ x, ∫ s in J, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => integral_congr_ae (by
      have hr := ((Lp.memLp ((hT.gradientOrbit_horizon_energy hP v t).1.toLp
        (complexTransposeGradientOrbit Q T v))).restrict J).coeFn_toLp
      filter_upwards [hr, ae_restrict_of_ae (hT.gradientOrbit_horizon_energy hP v t).1.coeFn_toLp]
        with s hs ht
      change F v s = _ at hs
      rw [hs, ht])
  have hlim := conditional_gradient_cylinder_timeL2_tendsto μ (reducedLaw_stationary Q)
    (ν.restrict J) κ A j
    (((localTimeLpRestrict_continuous ν J).tendsto _).comp
      (hT.tendsto_Lp_gradientOrbit_resolvent hP f t))
  change Tendsto (fun n => ∫ x, ∫ s in J, ∫ ω in A,
    ‖(F (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ)
    atTop (𝓝 (∫ x, ∫ s in J, ∫ ω in A, ‖(F f s j) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ)) at hlim
  simpa only [he] using hlim

private theorem translated_conditional_cylinder_fubini
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) [SFinite ν] (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    {u : S → Lp ℂ 2 μ} (hu : Integrable (fun s => ‖u s‖ ^ 2) ν)
    {U : S × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[μ] u s) :
    Integrable (fun ω => ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν) μ ∧
    (∀ᵐ ω ∂μ, Integrable (fun q : S × Vec d => ‖U (q.1, translate q.2 ω)‖ ^ 2) (ν.prod κ)) ∧
    ∀ A : Set (FieldPair d),
      (∫ ω in A, ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν ∂μ) =
        ∫ x, ∫ s, ∫ ω in A, ‖(u s) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
  let v := fun q : S × Vec d => complexTranslation μ hμ q.2 (u q.1)
  let V := fun p : (S × Vec d) × FieldPair d => U (p.1.1, translate p.1.2 p.2)
  have hV : Measurable V := hU.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hv : Integrable (fun q => ‖v q‖ ^ 2) (ν.prod κ) := by
    simpa only [v, norm_complexTranslation] using hu.comp_fst κ
  have heV (q : S × Vec d) : (fun ω => V (q, ω)) =ᵐ[μ] v q := by
    filter_upwards [(measurePreserving_translate μ hμ q.2).quasiMeasurePreserving.ae
      (heU q.1), coeFn_complexTranslation μ hμ q.2 (u q.1)] with ω huω hτω
    exact huω.trans hτω.symm
  have hi := integrable_sq_joint_l2_representative hv hV heV
  have hpair : (fun ω => ∫ q, ‖V (q, ω)‖ ^ 2 ∂ν.prod κ) =ᵐ[μ]
      fun ω => ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν := by
    filter_upwards [hi.prod_left_ae] with ω hω
    exact integral_prod _ hω
  have hf := conditional_quadratic_average_fubini μ (ν.prod κ) hv hV heV
  refine ⟨hf.1.congr hpair, hi.prod_left_ae, fun A => ?_⟩
  rw [← integral_congr_ae (ae_restrict_of_ae hpair), hf.2 A]
  have hA : Integrable (fun p : (S × Vec d) × FieldPair d => ‖V p‖ ^ 2)
      ((ν.prod κ).prod (μ.restrict A)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have heq : (fun q : S × Vec d => ∫ ω in A, ‖v q ω‖ ^ 2 ∂μ) =ᵐ[ν.prod κ]
      fun q => ∫ ω in A, ‖V (q, ω)‖ ^ 2 ∂μ := by
    filter_upwards with q
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (heV q)] with ω hω
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hω.symm
  rw [integral_congr_ae heq, integral_prod_symm _ hA.integral_prod_left]
  apply integral_congr_ae
  exact ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun s => integral_congr_ae
    ((ae_restrict_of_ae ((measurePreserving_translate μ hμ x).quasiMeasurePreserving.ae
      (heU s))).mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω))

private theorem translated_conditional_gradient_cylinder_fubini
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) [SFinite ν] (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    {u : Fin d → S → Lp ℂ 2 μ}
    (hu : ∀ j, Integrable (fun s => ‖u j s‖ ^ 2) ν)
    {U : Fin d → S × FieldPair d → ℂ} (hU : ∀ j, Measurable (U j))
    (heU : ∀ j s, (fun ω => U j (s, ω)) =ᵐ[μ] u j s) :
    Integrable (fun ω => ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν) μ ∧
    ∀ A : Set (FieldPair d),
      (∫ ω in A, ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν ∂μ) =
        ∑ j, ∫ x, ∫ s, ∫ ω in A, ‖(u j s) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
  have h j := translated_conditional_cylinder_fubini μ hμ ν κ (hu j) (hU j) (heU j)
  have he : (fun ω => ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν) =ᵐ[μ]
      fun ω => ∑ j, ∫ s, ∫ x, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν := by
    filter_upwards [ae_all_iff.mpr (fun j => (h j).2.1)] with ω hω
    rw [← integral_finsetSum Finset.univ (fun j _ => (hω j).integral_prod_left)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => (hω j).prod_right_ae)] with s hs
    exact integral_finsetSum Finset.univ (fun j _ => hs j)
  refine ⟨(integrable_finsetSum Finset.univ (fun j _ => (h j).1)).congr he.symm, fun A => ?_⟩
  rw [integral_congr_ae (ae_restrict_of_ae he),
    integral_finsetSum Finset.univ (fun j _ => (h j).1.restrict (s := A))]
  exact Finset.sum_congr rfl (fun j _ => (h j).2.2 A)

/-- The graph-data cylinder estimate tested on an arbitrary environment
event, expressed using the prescribed horizon-independent gradient. -/
theorem local_time_transpose_conditional_graph_gradient_cylinder
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (t : ℝ), 0 < t → ∀ (ρ : ℝ), Real.sqrt t ≤ ρ →
    ∀ (z : Vec d) (A : Set (FieldPair d)),
      (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∫ s in Icc (t / 2) t,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) ≤
      C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t *
        (∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ∫ s in Icc (t / 4) t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨C, hC, hcyl⟩ := local_time_transpose_gradient_cylinder d Λ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ P T hP hT f g hfg t ht ρ hρ z A
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let K₁ := {x : Vec d | euclideanNorm (x - z) ≤ ρ}
  let K₂ := {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ}
  let : IsFiniteMeasure (volume.restrict K₁) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z ρ).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict K₂) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z (2 * ρ)).measure_lt_top (μ := volume)⟩
  obtain ⟨G, U, DU, hU, hDU, heU, hG, heDU, hineq⟩ := hcyl _ Q i ζ P T hP hT f g hfg
  obtain ⟨H, hH, _⟩ := hT.existsUnique_continuous_gradient_orbit hP hfg
  have hGH s j : G s j = H s j := congrFun ((hG s).unique (hH.1 s)) j
  have hiG j : IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc (t / 2) t) := by
    simp_rw [hGH]
    exact (((PiLp.continuous_apply 2 _ j).comp hH.2).comp
      continuous_real_toNNReal).norm.pow 2 |>.continuousOn.integrableOn_compact isCompact_Icc
  have hiU : IntegrableOn (fun s : ℝ => ‖T s.toNNReal f‖ ^ 2) (Icc (t / 4) t) :=
    (((hT.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hD := translated_conditional_gradient_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc (t / 2) t)) (volume.restrict K₁) hiG hDU (fun j s => heDU s j)
  have hW := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc (t / 4) t)) (volume.restrict K₂) hiU hU heU
  have hm := setIntegral_mono_ae (s := A) hD.1.restrict
    (hW.1.const_mul (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t)).restrict (hineq t ht ρ hρ z)
  rw [integral_const_mul, hD.2 A, hW.2.2 A] at hm
  have he j x :
      (∫ s in Icc (t / 2) t, ∫ ω in A, ‖(G s.toNNReal j) (translate x ω)‖ ^ 2 ∂μ) =
        ∫ s in Icc (t / 2) t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hg : complexTransposeGradientOrbit Q T f s = WithLp.toLp 2 (G s.toNNReal) :=
      complexTransposeGradientOrbit_eq (by linarith [hs.1]) (hG s.toNNReal)
    rw [hg]
  simpa only [he] using hm

private theorem transpose_conditional_iterated_cylinder_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f : ℕ → Lp ℂ 2 (reducedLaw Q)} {g : Lp ℂ 2 (reducedLaw Q)}
    (hf : Tendsto f atTop (𝓝 g)) (b c : ℝ)
    (κ : Measure (Vec d)) [IsFiniteMeasure κ] (A : Set (FieldPair d)) :
    Tendsto (fun n => ∫ x, ∫ s in Icc b c, ∫ ω in A,
      ‖(T s.toNNReal (f n)) (translate x ω)‖ ^ 2 ∂reducedLaw Q ∂volume ∂κ) atTop
      (𝓝 (∫ x, ∫ s in Icc b c, ∫ ω in A,
        ‖(T s.toNNReal g) (translate x ω)‖ ^ 2 ∂reducedLaw Q ∂volume ∂κ)) := by
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let ν := volume.restrict (Icc b c)
  have he (v : Lp ℂ 2 μ) (q : ℝ × Vec d) :
      (∫ ω in A, ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ) =
        ‖localTimeLpRestrict μ A
          (complexTranslation μ (reducedLaw_stationary Q) q.2 (T q.1.toNNReal v))‖ ^ 2 := by
    rw [localTimeLpRestrict_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (coeFn_complexTranslation μ (reducedLaw_stationary Q)
      q.2 (T q.1.toNNReal v))] with ω hω
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hω.symm
  have hi (v : Lp ℂ 2 μ) : Integrable
      (fun q : ℝ × Vec d => ∫ ω in A, ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ)
      (ν.prod κ) := by
    simp_rw [he]
    have hc := ((localTimeLpRestrict_continuous μ A).comp
      ((continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
        (continuous_snd.prodMk (((hT.continuous_apply hP v).comp
          continuous_real_toNNReal).comp continuous_fst)))).norm.pow 2
    have ht : Integrable (fun s : ℝ => ‖T s.toNNReal v‖ ^ 2) ν :=
      (((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc
    apply (ht.comp_fst κ).mono' hc.aestronglyMeasurable
    exact ae_of_all _ fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (localTimeLpRestrict_norm_le μ A _).trans (by
        change ‖complexTranslation μ (reducedLaw_stationary Q) q.2 (T q.1.toNNReal v)‖ ≤ _
        exact (norm_complexTranslation _ _ _ _).le)
  have hre (v : Lp ℂ 2 μ) :
      (∫ q : ℝ × Vec d, ∫ ω in A,
        ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ ∂ν.prod κ) =
      ∫ x, ∫ s in Icc b c, ∫ ω in A,
        ‖(T s.toNNReal v) (translate x ω)‖ ^ 2 ∂μ ∂volume ∂κ :=
    integral_prod_symm _ (hi v)
  have hν : ∀ᵐ q ∂ν.prod κ, q.1.toNNReal ≤ c.toNNReal := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun x => Real.toNNReal_le_toNNReal hs.2
  have hl := local_time_transpose_conditional_cylinder_tendsto hP hT hf (ν.prod κ) A c.toNNReal hν
  change Tendsto (fun n => ∫ q : ℝ × Vec d, ∫ ω in A,
    ‖(T q.1.toNNReal (f n)) (translate q.2 ω)‖ ^ 2 ∂μ ∂ν.prod κ) atTop
    (𝓝 (∫ q : ℝ × Vec d, ∫ ω in A,
      ‖(T q.1.toNNReal g) (translate q.2 ω)‖ ^ 2 ∂μ ∂ν.prod κ)) at hl
  simpa only [hre] using hl

/-- The actual transpose gradient cylinder estimate for arbitrary L2 data,
tested on any environment event. No generator-domain assumption is needed. -/
theorem local_time_transpose_conditional_allData_gradient_cylinder
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ), 0 < t →
    ∀ (ρ : ℝ), Real.sqrt t ≤ ρ → ∀ (z : Vec d) (A : Set (FieldPair d)),
      (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∫ s in Icc (t / 2) t,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) ≤
      C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t *
        (∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ∫ s in Icc (t / 4) t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨C, hC, hcyl⟩ := local_time_transpose_conditional_graph_gradient_cylinder d Λ₀ hΛ
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ P T hP hT f t ht ρ hρ z A
  let K₁ := {x : Vec d | euclideanNorm (x - z) ≤ ρ}
  let K₂ := {x : Vec d | euclideanNorm (x - z) ≤ 2 * ρ}
  let : IsFiniteMeasure (volume.restrict K₁) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z ρ).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict K₂) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z (2 * ρ)).measure_lt_top (μ := volume)⟩
  have hm : (volume.restrict (Ioc (0 : ℝ) (⟨t, ht.le⟩ : ℝ≥0))).restrict (Icc (t / 2) t) =
      volume.restrict (Icc (t / 2) t) := by
    rw [Measure.restrict_restrict measurableSet_Icc]
    congr 1
    apply inter_eq_left.mpr
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hl (j : Fin d) :
      Tendsto (fun n => ∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
        ‖(complexTransposeGradientOrbit Q T
          (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) atTop
        (𝓝 (∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2 ∂reducedLaw Q)) := by
    have hj := local_time_transpose_conditional_gradient_cylinder_tendsto
      hP hT f ⟨t, ht.le⟩ (Icc (t / 2) t) A j (volume.restrict K₁)
    have he (v : Lp ℂ 2 (reducedLaw Q)) :
        (∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2
            ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t)) =
        ∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2 ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hm]
    change Tendsto (fun n => ∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
      ‖(complexTransposeGradientOrbit Q T
        (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t)) atTop
      (𝓝 (∫ x in K₁, ∫ s in Icc (t / 2) t, ∫ ω in A,
        ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t))) at hj
    simpa only [he] using hj
  have hleft := tendsto_finsetSum Finset.univ (fun j _ => hl j)
  have hright := (transpose_conditional_iterated_cylinder_tendsto hP hT
    (tendsto_complexTransposeResolventApproximation Q i ζ f) (t / 4) t
    (volume.restrict K₂) A).const_mul (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n =>
    hcyl hP hT (complexTransposeResolventApproximation_graph Q i ζ n f) t ht ρ hρ z A)

private theorem timeLp_component_integrable_sq
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ν : Measure ℝ}
    (F : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)) 2 ν) (j : Fin d) :
    Integrable (fun s => ‖F s j‖ ^ 2) ν := by
  have hm := (PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable F)
  have hi := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).mp (Lp.memLp F)
  apply hi.mono' (hm.norm.pow 2)
  exact ae_of_all _ fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (F s) j) 2

/-- Integrated output Young for an actual transpose derivative orbit. The
arbitrary derivative datum needs no generator-domain assumption. Gradient
representatives agree with the canonical orbits almost everywhere in time. -/
theorem local_time_transpose_derivative_integrated_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b t : ℝ} (hb : 0 ≤ b) (hbt : b ≤ t)
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ W V : ℝ × FieldPair d → ℂ, ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal g) ∧
      (∀ᵐ s ∂volume.restrict (Icc b t), ∀ j,
        (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T f s j) ∧
      (∀ᵐ s ∂volume.restrict (Icc b t), ∀ j,
        (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T g s j) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun q : Vec d × ℝ => W (q.2, translate q.1 ω)) 2 ((volume.restrict K).prod (volume.restrict (Icc b t))) ∧
        MemLp (fun q : Vec d × ℝ => V (q.2, translate q.1 ω)) 2 ((volume.restrict K).prod (volume.restrict (Icc b t))) ∧
        (∀ j, MemLp (fun q : Vec d × ℝ => D j (q.2, translate q.1 ω)) 2 ((volume.restrict K).prod (volume.restrict (Icc b t)))) ∧
        (∀ j, MemLp (fun q : Vec d × ℝ => E j (q.2, translate q.1 ω)) 2 ((volume.restrict K).prod (volume.restrict (Icc b t))))) ∧
      ∀ (φ : Vec d → ℝ), IsSpatialTest univ φ → ∀ ε : ℝ, 0 < ε →
      ∀ η : ℝ → ℝ, ContinuousOn η (Icc b t) → (∀ s ∈ Icc b t, 0 ≤ η s) →
      let L := Real.exp (2 * Λ₀) * Λ₀
      ∀ᵐ ω ∂reducedLaw Q,
        (1 / 2 : ℝ) * (∫ s in Icc b t, η s *
          (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2)) ≤
        ε * (∫ s in Icc b t, η s *
          (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2))) +
        (∫ s in Icc b t, η s *
          (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
            (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
              2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2))) := by
  let μ := reducedLaw Q
  let ν := volume.restrict (Icc b t)
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  have henergy v := hT.gradientOrbit_horizon_energy hP v ⟨t, hb.trans hbt⟩
  simp only [restrict_Ioc_eq_restrict_Icc] at henergy
  have hsub : Icc b t ⊆ Icc (0 : ℝ) t := fun s hs => ⟨hb.trans hs.1, hs.2⟩
  have hmem v : MemLp (complexTransposeGradientOrbit Q T v) 2 ν :=
    (henergy v).1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hga v := ae_restrict_of_ae_restrict_of_subset hsub (henergy v).2.1
  let F v := (hmem v).toLp (complexTransposeGradientOrbit Q T v)
  have hFc v j : StronglyMeasurable (fun s => F v s j) :=
    (PiLp.continuous_apply 2 _ j).comp_stronglyMeasurable (Lp.stronglyMeasurable (F v))
  choose D hD heD using fun j =>
    EinsteinFull.StronglyMeasurable.exists_joint_l2_representative (hFc f j)
  choose E hE heE using fun j =>
    EinsteinFull.StronglyMeasurable.exists_joint_l2_representative (hFc g j)
  obtain ⟨W, hW, heW⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative
    (((hT.continuous_apply hP f).comp continuous_real_toNNReal).stronglyMeasurable)
  obtain ⟨V, hV, heV⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative
    (((hT.continuous_apply hP g).comp continuous_real_toNNReal).stronglyMeasurable)
  have heF v : (fun s => F v s) =ᵐ[ν] complexTransposeGradientOrbit Q T v :=
    (hmem v).coeFn_toLp
  have hgrad v : ∀ᵐ s ∂ν,
      HasComplexHorizontalGradient μ (reducedLaw_stationary Q) (T s.toNNReal v) (F v s) := by
    filter_upwards [hga v, heF v] with s hs he
    rw [he]
    exact hs
  have hlocal {v : Lp ℂ 2 μ} {U : ℝ × FieldPair d → ℂ}
      (hU : Measurable U) (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[μ] T s.toNNReal v) :=
    ae_locally_memLp_joint_spatial_translate μ (reducedLaw_stationary Q) hU
      (integrable_sq_joint_l2_representative
        ((((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          (μ := (volume : Measure ℝ)) (K := Icc b t) isCompact_Icc) hU heU)
  have hlocalD j := ae_locally_memLp_joint_spatial_translate μ (reducedLaw_stationary Q) (hD j)
    (integrable_sq_joint_l2_representative (timeLp_component_integrable_sq (F f) j) (hD j) (heD j))
  have hlocalE j := ae_locally_memLp_joint_spatial_translate μ (reducedLaw_stationary Q) (hE j)
    (integrable_sq_joint_l2_representative (timeLp_component_integrable_sq (F g) j) (hE j) (heE j))
  refine ⟨W, V, D, E, hW, hV, hD, hE, heW, heV, ?_, ?_, ?_, ?_⟩
  · filter_upwards [heF f] with s hs
    exact fun j => (heD j s).trans (by rw [hs])
  · filter_upwards [heF g] with s hs
    exact fun j => (heE j s).trans (by rw [hs])
  · filter_upwards [hlocal hW heW, hlocal hV heV, ae_all_iff.mpr hlocalD,
      ae_all_iff.mpr hlocalE] with ω hωW hωV hωD hωE
    exact fun K hK => ⟨hωW K hK, hωV K hK, fun j => hωD j K hK, fun j => hωE j K hK⟩
  intro φ hφ ε hε η hη hηpos L
  have hy := local_time_transpose_ae_joint_output_young
    (Eventually.of_forall fun s => hT.map_generator hP hfg s.toNNReal)
    (hgrad f) (hgrad g) hW hV hD hE heW heV heD heE hφ hε
  filter_upwards [hlocal hW heW, hlocal hV heV, ae_all_iff.mpr hlocalD,
    ae_all_iff.mpr hlocalE, hy] with ω hωW hωV hωD hωE hωy
  exact local_time_transpose_output_young_time_integral hφ
    (hωW _ hφ.2.1) (hωV _ hφ.2.1) (fun j => hωD j _ hφ.2.1)
    (fun j => hωE j _ hφ.2.1) hη hηpos hωy

/-- Remove the spatial weights from integrated transpose output Young with
an explicit spatial-gap coefficient. The force mass term is retained. -/
theorem local_time_transpose_cylinder_output_young
    {d : ℕ} {K S : Set (Vec d)} (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {b c ε L B δ : ℝ} (hε : 0 < ε) {ζ : ℂ}
    {J : Set ℝ} (hJ : MeasurableSet J) (hJI : J ⊆ Icc b c)
    {W V : Vec d × ℝ → ℂ} {D E : Fin d → Vec d × ℝ → ℂ}
    (hW : MemLp W 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hE : ∀ j, MemLp (E j) 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ S, φ x = 1) (hzero : ∀ x, x ∉ K → φ x = 0)
    (hφD : ∀ j x, |coordinateDerivative j φ x| ≤ B / δ)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1)
    (hηlower : ∀ s ∈ J, 1 ≤ η s)
    (hy : (1 / 2 : ℝ) * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ‖V (x, s)‖ ^ 2)) ≤
      ε * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * (∑ j, ‖E j (x, s)‖ ^ 2))) +
      (∫ s in Icc b c, η s *
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (x, s)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (x, s)‖ ^ 2)))) :
    (1 / 2 : ℝ) * (∫ s in J, ∫ x in S, ‖V (x, s)‖ ^ 2) ≤
      ε * (∫ s in Icc b c, ∫ x in K, ∑ j, ‖E j (x, s)‖ ^ 2) +
      (1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / δ ^ 2) *
        (∫ s in Icc b c, ∫ x in K,
          ((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (x, s)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (x, s)‖ ^ 2) := by
  have hiV := (memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
  have hiE := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hE j).aestronglyMeasurable).mp (hE j))
  have hinner := physical_inner_spacetime_integral_le hK hS hSK hJ hJI hiV
    (fun p => sq_nonneg _) hφ.1.continuous hzero hone hη
    (fun s hs => (hηrange s hs).1) hηlower
  have hφsq x : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
  have hEbound := physical_spacetime_weight_integral_le hK hiE
    (fun p => Finset.sum_nonneg fun j _ => sq_nonneg _) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hzero x hx, zero_pow (by decide : 2 ≠ 0)]) hη
    (A := 1) (fun s hs x _ => by
      exact (mul_le_mul_of_nonneg_right (hηrange s hs).2 (sq_nonneg _)).trans
        (by simpa only [one_mul] using hφsq x))
  let R : Vec d → ℝ := fun x => φ x ^ 2 / (4 * ε) +
    4 * (∑ j, (coordinateDerivative j φ x) ^ 2)
  have hRpos x : 0 ≤ R x := by dsimp only [R]; positivity
  have hRbound x : R x ≤ 1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / δ ^ 2 := by
    have hd := physical_gap_cutoff_error_bound (ζ := 0) hφrange hφD x
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hd
    have hp := div_le_div_of_nonneg_right (hφsq x) (by positivity : 0 ≤ 4 * ε)
    dsimp only [R]
    apply add_le_add hp
    convert mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 4) using 1; ring
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hRc : Continuous R := (hφ.1.continuous.pow 2).div_const _ |>.add
    (continuous_const.mul (continuous_finsetSum _ fun j _ => (hd j).pow 2))
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hzero x hn)) hK.isClosed
  have hRzero x (hx : x ∉ K) : R x = 0 := by
    have hd0 j : coordinateDerivative j φ x = 0 := by
      have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
    simp only [R, hzero x hx, hd0, zero_pow (by decide : 2 ≠ 0), zero_div,
      Finset.sum_const_zero, mul_zero, add_zero]
  have hrest := physical_spacetime_weight_integral_le hK
    ((hiD.const_mul ((d : ℝ) ^ 2 * L ^ 2 / 2)).add
      (hiW.const_mul (2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2)))
    (fun p => by
      change 0 ≤ _ * (∑ j, ‖D j p‖ ^ 2) + _ * ‖W p‖ ^ 2
      exact add_nonneg (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun j _ => sq_nonneg _)) (by positivity)) hRc hRzero hη
    (A := 1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / δ ^ 2) (fun s hs x _ =>
      (mul_le_mul_of_nonneg_right (hηrange s hs).2 (hRpos x)).trans
        (by simpa only [one_mul] using hRbound x))
  simp only [one_mul] at hEbound
  exact (mul_le_mul_of_nonneg_left hinner (by norm_num)).trans
    (hy.trans (add_le_add (mul_le_mul_of_nonneg_left hEbound hε.le) hrest))

/-- Spatial interpolation for the actual transpose derivative on arbitrary
nested balls. No generator-domain hypothesis is imposed on the derivative datum. -/
theorem local_time_transpose_derivative_ball_output_young
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {b t : ℝ}, 0 ≤ b → b ≤ t →
    ∀ {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∃ W V : ℝ × FieldPair d → ℂ, ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal g) ∧
      (∀ᵐ s ∂volume.restrict (Icc b t), ∀ j,
        (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T f s j) ∧
      (∀ᵐ s ∂volume.restrict (Icc b t), ∀ j,
        (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] complexTransposeGradientOrbit Q T g s j) ∧
      ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R → ∀ ε : ℝ, 0 < ε →
      let L := Real.exp (2 * Λ₀) * Λ₀
      ∀ᵐ ω ∂reducedLaw Q,
        (1 / 2 : ℝ) * (∫ s in Icc b t, ∫ x in {x | euclideanNorm (x - z) ≤ r},
          ‖V (s, translate x ω)‖ ^ 2) ≤
        ε * (∫ s in Icc b t, ∫ x in {x | euclideanNorm (x - z) ≤ R},
          ∑ j, ‖E j (s, translate x ω)‖ ^ 2) +
        (1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / (R - r) ^ 2) *
          (∫ s in Icc b t, ∫ x in {x | euclideanNorm (x - z) ≤ R},
            ((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
              2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcut⟩ := exists_physical_gap_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ b t hb hbt P T hP hT f g hfg
  obtain ⟨W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hlocal, hy⟩ :=
    local_time_transpose_derivative_integrated_output_young hb hbt hP hT hfg
  refine ⟨W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, ?_⟩
  intro z r R hr hrR ε hε L
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcut z r R hr hrR
  have hK := isCompact_physical_euclidean_closedBall z R
  have hS := (isCompact_physical_euclidean_closedBall z r).measurableSet
  have hSK : {x : Vec d | euclideanNorm (x - z) ≤ r} ⊆
      {x : Vec d | euclideanNorm (x - z) ≤ R} := fun x hx => hx.trans hrR.le
  filter_upwards [hlocal, hy φ hφ ε hε (fun _ => 1) continuousOn_const
    (fun _ _ => by norm_num)] with ω hωlocal hωy
  obtain ⟨hωW, hωV, hωD, hωE⟩ := hωlocal _ hK
  exact local_time_transpose_cylinder_output_young
    (d := d) (b := b) (c := t) (L := L) (B := B) (δ := R - r) (ζ := ζ)
    (J := Icc b t) (W := fun q => W (q.2, translate q.1 ω))
    (V := fun q => V (q.2, translate q.1 ω))
    (D := fun j q => D j (q.2, translate q.1 ω))
    (E := fun j q => E j (q.2, translate q.1 ω)) (φ := φ) (η := fun _ => 1)
    hK hS hSK hε
    measurableSet_Icc (Subset.refl _) hωW hωV hωD hωE hφ hφrange
    (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le) hφD
    continuousOn_const (fun _ _ => ⟨by norm_num, le_rfl⟩) (fun _ _ => le_rfl) hωy

/-- Boundary-energy argument for arbitrary temporal and spatial gaps.
Adapted from the fixed-gap producer; kept private to this consumer. -/
private theorem c9_transpose_spatial_weighted_energy
    {d : ℕ} {b c : ℝ} (hbc : b ≤ c)
    {W V : Vec d × ℝ → ℂ} {u v : Vec d → ℂ}
    {K : Set (Vec d)} (hK : IsCompact K)
    (hlW : MemLp W 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hlV : MemLp V 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hu : MemLp u 2 (volume.restrict K)) (hv : MemLp v 2 (volume.restrict K))
    {φ : Vec d → ℝ} (hφ : Continuous φ)
    {η : ℝ → ℝ} (hη : AbsolutelyContinuousOnInterval η b c)
    (hη' : ContinuousOn (deriv η) (Icc b c))
    (htime : ∀ᵐ x ∂volume.restrict K,
      (∫ s in b..c, η s * (2 * (star (W (x,s)) * V (x,s)).re)) =
        η c * ‖v x‖ ^ 2 - η b * ‖u x‖ ^ 2 -
          ∫ s in b..c, deriv η s * ‖W (x,s)‖ ^ 2) :
    (∫ s in Icc b c, η s * (∫ x in K, φ x ^ 2 *
      (2 * (star (W (x,s)) * V (x,s)).re))) =
        η c * (∫ x in K, φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (∫ x in K, φ x ^ 2 * ‖u x‖ ^ 2) -
        ∫ s in Icc b c, deriv η s * (∫ x in K, φ x ^ 2 * ‖W (x,s)‖ ^ 2) := by
  let X : Vec d × ℝ → ℂ := W
  let Y : Vec d × ℝ → ℂ := V
  let A : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * η p.2 * (2 * (star (X p) * Y p).re)
  let B : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * deriv η p.2 * ‖X p‖ ^ 2
  have hηc : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc] using hη.continuousOn
  have hweight (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc b c)) :
      ContinuousOn (fun p : Vec d × ℝ => φ p.1 ^ 2 * ψ p.2) (K ×ˢ Icc b c) :=
    ((hφ.pow 2).comp continuous_fst).continuousOn.mul
      (hψ.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hprod : Integrable (fun p => star (X p) * Y p)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    hlW.star.integrable_mul hlV
  have hA : Integrable A ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((Complex.reCLM.integrable_comp hprod).const_mul 2) (hweight η hηc)
  have hB : Integrable B ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((memLp_two_iff_integrable_sq_norm hlW.aestronglyMeasurable).mp hlW)
      (hweight (deriv η) hη')
  have hend (a : Vec d → ℂ) (ha : MemLp a 2 (volume.restrict K)) :
      Integrable (fun x => φ x ^ 2 * ‖a x‖ ^ 2) (volume.restrict K) :=
    IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn
      ((memLp_two_iff_integrable_sq_norm ha.aestronglyMeasurable).mp ha) hK
  have heq : ∀ᵐ x ∂volume.restrict K,
      (∫ s in Icc b c, A (x, s)) =
        η c * (φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (φ x ^ 2 * ‖u x‖ ^ 2) - ∫ s in Icc b c, B (x, s) := by
    filter_upwards [htime] with x hx
    have he := hx
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc] at he
    simp only [A, B, X, Y]
    simp_rw [mul_assoc (φ x ^ 2)]
    rw [integral_const_mul, integral_const_mul, he]
    ring
  calc
    _ = ∫ s in Icc b c, ∫ x in K, A (x, s) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [A, X, Y]
      ring
    _ = ∫ x in K, ∫ s in Icc b c, A (x, s) := (integral_integral_swap hA).symm
    _ = η c * (∫ x in K, φ x ^ 2 * ‖v x‖ ^ 2) -
        η b * (∫ x in K, φ x ^ 2 * ‖u x‖ ^ 2) -
        ∫ x in K, ∫ s in Icc b c, B (x, s) := by
      have hsplit := integral_sub
        (((hend v hv).const_mul (η c)).sub ((hend u hu).const_mul (η b)))
        hB.integral_prod_left
      have hends := integral_sub ((hend v hv).const_mul (η c))
        ((hend u hu).const_mul (η b))
      simp only [Pi.sub_apply] at hsplit hends
      rw [integral_congr_ae heq, hsplit, hends, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [integral_integral_swap hB]
      congr 1
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [B, X]
      ring

private theorem c9_transpose_ae_joint_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    {W V : ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V)
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {D : Fin d → ℝ × FieldPair d → ℂ}
    (hD : ∀ j, Measurable (D j))
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))).re +
        (10 * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2) := by
  intro L
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hφm : Measurable (fun q : (ℝ × FieldPair d) × Vec d => φ q.2) :=
    hφ.1.continuous.measurable.comp measurable_snd
  have hder j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  let B := (fun p : ℝ × FieldPair d =>
      (∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))).re +
        (10 * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (p.1, translate x p.2)‖ ^ 2))
  have hB : Measurable B := by
    have hmain : Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))) :=
      (((Complex.continuous_ofReal.measurable.comp hφm).pow_const 2).mul
      ((hshift hW).stronglyMeasurable.star.measurable) |>.mul (hshift hV).neg).stronglyMeasurable.integral_prod_right'.measurable
    have herr : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        (‖ζ‖ ^ 2 * φ q.2 ^ 2 + (∑ j, (coordinateDerivative j φ q.2) ^ 2)) *
          ‖W (q.1.1, translate q.2 q.1.2)‖ ^ 2) :=
      ((measurable_const.mul (hφm.pow_const 2)).add
      (Finset.measurable_sum _ fun j _ =>
        (((hder j).measurable.comp measurable_snd).pow_const 2))).mul
          ((hshift hW).norm.pow_const 2)
    exact (Complex.continuous_re.measurable.comp hmain).add
      (measurable_const.mul herr.stronglyMeasurable.integral_prod_right'.measurable)
  let A := fun p : ℝ × FieldPair d =>
    (L⁻¹ / 4) * (∫ x, φ x ^ 2 * ∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2)
  have hA : Measurable A :=
    measurable_const.mul ((hφm.pow_const 2).mul
      (Finset.measurable_sum _ fun j _ => (hshift (hD j)).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed (j : Fin d) := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  filter_upwards [local_time_transpose_physical_cutoff_energy (hgen s hs) (hG s), hew, hev,
    ae_all_iff.mpr hed] with ω henergy hw hv hd
  have hgrad : (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) =
      ∫ x, φ x ^ 2 * ∑ j, ‖G s j (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hd] with x hx
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj : D j (s, translate x ω) = G s j (translate x ω) := hx j
    rw [hj]
  have hmain : (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))) =
      ∫ x, (φ x : ℂ) ^ 2 * star ((u s) (translate x ω)) * (-(v s) (translate x ω)) := by
    apply integral_congr_ae
    filter_upwards [hw, hv] with x hx hy
    change W (s, translate x ω) = _ at hx
    change V (s, translate x ω) = _ at hy
    rw [hx, hy]
  have herr : (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ‖W (s, translate x ω)‖ ^ 2) =
      ∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
        ‖(u s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    change W (s, translate x ω) = _ at hx
    rw [hx]
  change (L⁻¹ / 4) * _ ≤ _ + _ * _
  rw [hgrad, hmain, herr]
  exact henergy φ hφ



private theorem c9_transpose_cutoff_energy_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c : ℝ}
    {W V : Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hW : MemLp W 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {D : Fin d → Vec d × ℝ → ℂ}
    (hD : ∀ j, MemLp (D j) 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hcoer : ∀ᵐ s ∂volume.restrict (Icc b c),
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re +
          (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
            (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
              ‖W (x, s)‖ ^ 2)) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      (∫ s in Icc b c, η s *
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re) +
      (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
        (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
            ‖W (x, s)‖ ^ 2)) := by
  have hK := hφ.2.1
  have hz : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hdz j x (hx : x ∉ tsupport φ) : coordinateDerivative j φ x = 0 := by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  have herr := integrable_time_integral_compact_spatial_weight hK
    (ψ := fun x => ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2)
    ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx])
  have hm := integrable_time_integral_compact_spatial_weight hK
    (hW.star.integrable_mul hV.neg)
    ((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2)
    (fun x hx => by simp [Function.comp_def, hz x hx])
  have hmain : Integrable (fun s => η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re)
      (volume.restrict (Icc b c)) := by
    simp_rw [mul_assoc] at ⊢
    exact IntegrableOn.continuousOn_mul hη (Complex.reCLM.integrable_comp hm) isCompact_Icc
  have he := IntegrableOn.continuousOn_mul hη herr isCompact_Icc
  have hg := integrable_time_integral_compact_spatial_weight hK
    (integrable_finsetSum Finset.univ fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hgi := IntegrableOn.continuousOn_mul hη hg isCompact_Icc
  have hi := integral_mono_ae (hgi.const_mul ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4))
    (hmain.add (he.const_mul (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3))) (by
      filter_upwards [hcoer, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.pow_apply]
      nlinarith only [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.pow_apply] at hi
  simpa only [integral_add hmain (he.const_mul _), integral_const_mul] using hi


private theorem c9_transpose_orbit_boundary_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ W : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (T s f) (G s)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s.toNNReal j) ∧
      (∀ j, Continuous (fun s : ℝ => G s.toNNReal j)) ∧
      ∀ b c : ℝ, 0 ≤ b → b < c →
      ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c →
        ContinuousOn (deriv η) (Icc b c) →
        (∀ s ∈ Icc b c, 0 ≤ η s) → η b = 0 → η c = 1 →
        ∀ᵐ ω ∂reducedLaw Q,
          ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
            (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
          -(∫ x, φ x ^ 2 * ‖(T c.toNNReal f) (translate x ω)‖ ^ 2) / 2 +
            (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) / 2 +
            (10 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
              (∫ s in Icc b c, η s * (∫ x,
                (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
                  ‖W (s, translate x ω)‖ ^ 2)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨G, hG, _⟩ := hT.existsUnique_continuous_gradient_orbit hP hfg
  have hGc (j : Fin d) : Continuous (fun s : ℝ => G s.toNNReal j) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp
      (hG.2.comp continuous_real_toNNReal)
  choose D hD heD using fun j =>
    EinsteinFull.StronglyMeasurable.exists_joint_l2_representative (hGc j).stronglyMeasurable
  obtain ⟨W, V, hW, hV, heW, heV, htime⟩ :=
    local_time_transpose_ae_physical_weighted_energy hP hT hfg
  refine ⟨fun s j => G s j, W, D, hW, hD, heW, hG.1, heD, hGc, ?_⟩
  have hw : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  intro b c hb hbc φ hφ η hη hηd hηpos hηb hηc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hlocalD (j : Fin d) := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) (hD j)
    (integrable_sq_joint_l2_representative
      (show IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc b c) volume from
        ((hGc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
      (hD j) (heD j))
  have hwI : IntegrableOn (fun s => ‖T s.toNNReal f‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖T s.toNNReal g‖ ^ 2) (Icc b c) volume :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hvI hV heV)
  have hcoer := c9_transpose_ae_joint_cutoff_energy (b := b) (c := c)
    (fun s _ => hT.map_generator hP hfg s.toNNReal) hW hV heW heV (fun s => hG.1 s.toNNReal) hD heD hφ
  filter_upwards [htime b c hb hbc.le, hlocalW, hlocalV, hcoer,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T b.toNNReal f),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (T c.toNNReal f), ae_all_iff.mpr hlocalD] with ω ht hlW hlV hc hUb hUc hlD
  have hineq := c9_transpose_cutoff_energy_time_integral hφ
    (hlW _ hφ.2.1) (hlV _ hφ.2.1) (fun j => hlD j _ hφ.2.1) hηcont hηpos hc
  have hp := (hlW (tsupport φ) hφ.2.1).star.integrable_mul
    (hlV (tsupport φ) hφ.2.1)
  have hpφ : Integrable (fun p : Vec d × ℝ =>
      (φ p.1 : ℂ) ^ 2 * star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
    have hi : Integrable (fun p : Vec d × ℝ =>
        (φ p.1 : ℂ) ^ 2 * (star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω)))
        ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
      rw [Measure.prod_restrict] at hp ⊢
      exact IntegrableOn.continuousOn_mul
        (((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).comp
          continuous_fst).continuousOn hp (hφ.2.1.prod isCompact_Icc)
    simpa only [mul_assoc] using hi
  have hpair : (∫ s in Icc b c, η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) *
        (-V (s, translate x ω))).re) =
      -(∫ s in Icc b c, η s * (∫ x, φ x ^ 2 *
        (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
    calc
      _ = ∫ s in Icc b c, -(η s * (∫ x, φ x ^ 2 *
          (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
        apply integral_congr_ae
        filter_upwards [hpφ.prod_left_ae] with s hs
        rw [physical_cutoff_generator_pairing_eq hs]
        ring
      _ = _ := by rw [integral_div, integral_neg]
  have hres (F : Vec d → ℝ) :
      (∫ x in tsupport φ, φ x ^ 2 * F x) = ∫ x, φ x ^ 2 * F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have htemporal := c9_transpose_spatial_weighted_energy hbc.le hφ.2.1
    (hlW _ hφ.2.1) (hlV _ hφ.2.1) (hUb _ hφ.2.1) (hUc _ hφ.2.1)
    hφ.1.continuous hη hηd (by
      filter_upwards [ht (tsupport φ) hφ.2.1] with x hx
      exact hx η hη)
  simp_rw [hres] at htemporal
  rw [hpair, htemporal, hηb, hηc, zero_mul, one_mul, sub_zero] at hineq
  linarith only [hineq]


private theorem c9_conditional_graph_gap_gradient_cylinder
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B H : ℝ, 0 < B ∧ 0 < H ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (b e t : ℝ), 0 ≤ b → b < e → e ≤ t →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R → ∀ A : Set (FieldPair d),
      let L := Real.exp (2 * Λ₀) * Λ₀
      (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ r}, ∫ s in Icc e t,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) ≤
      4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
        (∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨B, hB, hcut⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨H, hH, htime⟩ := exists_physical_gap_temporal_cutoff
  refine ⟨B, H, hB, hH, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f g hfg b e t hb hbe het z r R hr hrR A L
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  have hbt : b < t := hbe.trans_le het
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  obtain ⟨G, W, D, hW, hD, heW, hG, heD, hGc, henergy⟩ :=
    c9_transpose_orbit_boundary_energy hP hT hfg
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcut z r R hr hrR
  obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime b e hbe
  have hηc : ContinuousOn η (Icc b t) := hη.continuous.continuousOn
  have hηd : ContinuousOn (deriv η) (Icc b t) :=
    (hη.continuous_deriv (by simp)).continuousOn
  have hηac : AbsolutelyContinuousOnInterval η b t :=
    (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hwI : IntegrableOn (fun s => ‖T s.toNNReal f‖ ^ 2) (Icc b t) volume :=
    (((hT.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hiD j : IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc b t) volume :=
    ((hGc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate μ (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalD j := ae_locally_memLp_joint_spatial_translate μ (reducedLaw_stationary Q) (hD j)
    (integrable_sq_joint_l2_representative (hiD j) (hD j) (heD j))
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hS : IsCompact S := isCompact_physical_euclidean_closedBall z r
  have hSK : S ⊆ K := fun x hx => hx.trans hrR.le
  have hineq : ∀ᵐ ω ∂μ,
      (∫ s in Icc e t, ∫ x in S, ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
      4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
        (∫ s in Icc b t, ∫ x in K, ‖W (s, translate x ω)‖ ^ 2) := by
    filter_upwards [henergy b t hb hbt φ hφ η hηac hηd
      (fun s _ => (hηbounds s).1) hηb (hηone t het), hlocalW,
      ae_all_iff.mpr hlocalD] with ω he hlW hlD
    exact physical_spacetime_caccioppoli_of_cutoff_energy
      (d := d) (b := b) (c := t) (L := L) (C := 10 * L ^ 3)
      (A := ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2) (T := H / (e - b))
      (ζ := ζ) (J := Icc e t) (W := fun q => W (q.2, translate q.1 ω))
      (D := fun j q => D j (q.2, translate q.1 ω))
      (U := fun x => (T t.toNNReal f) (translate x ω)) (φ := φ) (η := η)
      hK hS.measurableSet hSK hL (by positivity) measurableSet_Icc
      (fun s hs => ⟨hbe.le.trans hs.1, hs.2⟩) (hlW K hK) (fun j => hlD j K hK)
      hφ hφrange (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
      (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x) hηc hηd
      (fun s _ => hηbounds s) (fun s hs => by rw [hηone s hs.1]) he
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hS.measure_lt_top (μ := volume)⟩
  have hiDE j : IntegrableOn (fun s : ℝ => ‖G s.toNNReal j‖ ^ 2) (Icc e t) volume :=
    ((hGc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hFD := translated_conditional_gradient_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc e t)) (volume.restrict S) hiDE hD heD
  have hFW := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc b t)) (volume.restrict K) hwI hW heW
  have hm := setIntegral_mono_ae (s := A) hFD.1.restrict
    (hFW.1.const_mul (4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
      (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)))).restrict hineq
  rw [integral_const_mul, hFD.2 A, hFW.2.2 A] at hm
  have he j x :
      (∫ s in Icc e t, ∫ ω in A, ‖(G s.toNNReal j) (translate x ω)‖ ^ 2 ∂μ) =
        ∫ s in Icc e t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hg : complexTransposeGradientOrbit Q T f s = WithLp.toLp 2 (G s.toNNReal) :=
      complexTransposeGradientOrbit_eq ((lt_of_le_of_lt hb hbe).trans_le hs.1) (hG s.toNNReal)
    rw [hg]
  simpa only [he] using hm

/-- Arbitrary-gap cylinder dissipation for every actual transpose datum,
including derivative data outside the generator domain. The estimate may be
tested on any environment event. -/
theorem local_time_transpose_conditional_allData_gap_gradient_cylinder
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B H : ℝ, 0 < B ∧ 0 < H ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ f : Lp ℂ 2 (reducedLaw Q),
    ∀ (b e t : ℝ), 0 ≤ b → b < e → e ≤ t →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R → ∀ A : Set (FieldPair d),
      let L := Real.exp (2 * Λ₀) * Λ₀
      (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ r}, ∫ s in Icc e t,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) ≤
      4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
        (∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨B, H, hB, hH, hcyl⟩ := c9_conditional_graph_gap_gradient_cylinder d
  refine ⟨B, H, hB, hH, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f b e t hb hbe het z r R hr hrR A L
  have ht : 0 < t := (lt_of_le_of_lt hb hbe).trans_le het
  let K₁ := {x : Vec d | euclideanNorm (x - z) ≤ r}
  let K₂ := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let : IsFiniteMeasure (volume.restrict K₁) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z r).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict K₂) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z R).measure_lt_top (μ := volume)⟩
  have hm : (volume.restrict (Ioc (0 : ℝ) (⟨t, ht.le⟩ : ℝ≥0))).restrict (Icc e t) =
      volume.restrict (Icc e t) := by
    rw [Measure.restrict_restrict measurableSet_Icc]
    congr 1
    exact inter_eq_left.mpr fun s hs => ⟨(lt_of_le_of_lt hb hbe).trans_le hs.1, hs.2⟩
  have hl (j : Fin d) :
      Tendsto (fun n => ∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
        ‖(complexTransposeGradientOrbit Q T
          (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) atTop
        (𝓝 (∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2 ∂reducedLaw Q)) := by
    have hj := local_time_transpose_conditional_gradient_cylinder_tendsto
      hP hT f ⟨t, ht.le⟩ (Icc e t) A j (volume.restrict K₁)
    have he (v : Lp ℂ 2 (reducedLaw Q)) :
        (∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2
            ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t)) =
        ∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
          ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2 ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hm]
    change Tendsto (fun n => ∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
      ‖(complexTransposeGradientOrbit Q T
        (complexTransposeResolventApproximation Q i ζ n f) s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t)) atTop
      (𝓝 (∫ x in K₁, ∫ s in Icc e t, ∫ ω in A,
        ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q ∂volume.restrict (Ioc (0 : ℝ) t))) at hj
    simpa only [he] using hj
  have hleft := tendsto_finsetSum Finset.univ (fun j _ => hl j)
  have hright := (transpose_conditional_iterated_cylinder_tendsto hP hT
    (tendsto_complexTransposeResolventApproximation Q i ζ f) b t
    (volume.restrict K₂) A).const_mul
      (4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)))
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun n =>
    hcyl hP hT (complexTransposeResolventApproximation_graph Q i ζ n f)
      b e t hb hbe het z r R hr hrR A)

private theorem c9_integrable_sq_joint_ae_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ᵐ t ∂ν, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable (fun p => ‖U p‖ ^ 2) (ν.prod μ) := by
  apply (integrable_prod_iff (hU.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨?_, ?_⟩
  · filter_upwards [heq] with t ht
    exact ((Lp.memLp (u t)).norm.integrable_sq).congr
      (ht.symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
  apply hu.congr
  filter_upwards [heq] with t ht
  have hn : ‖u t‖ ^ 2 = ∫ ω, ‖(u t) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [ht] with ω hω
  simp only [hω, Real.norm_eq_abs]
  exact (abs_of_nonneg (sq_nonneg ‖(u t) ω‖)).symm

private theorem c9_conditional_quadratic_average_ae_fubini
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SFinite ν]
    {u : X → Lp ℂ 2 μ} (hu : Integrable (fun x => ‖u x‖ ^ 2) ν)
    {U : X × Ω → ℂ} (hU : Measurable U)
    (heU : ∀ᵐ x ∂ν, (fun ω => U (x, ω)) =ᵐ[μ] u x) :
    Integrable (fun ω => ∫ x, ‖U (x, ω)‖ ^ 2 ∂ν) μ ∧
      ∀ A : Set Ω,
        (∫ ω in A, ∫ x, ‖U (x, ω)‖ ^ 2 ∂ν ∂μ) =
          ∫ x, ∫ ω in A, ‖u x ω‖ ^ 2 ∂μ ∂ν := by
  have hi := c9_integrable_sq_joint_ae_representative hu hU heU
  refine ⟨hi.integral_prod_right, fun A => ?_⟩
  have hA : Integrable (fun p : X × Ω => ‖U p‖ ^ 2) (ν.prod (μ.restrict A)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [← integral_integral_swap hA]
  apply integral_congr_ae
  filter_upwards [heU] with x hx
  exact integral_congr_ae
    ((ae_restrict_of_ae hx).mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)

private theorem c9_translated_conditional_ae_cylinder_fubini
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) [SFinite ν] (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    {u : S → Lp ℂ 2 μ} (hu : Integrable (fun s => ‖u s‖ ^ 2) ν)
    {U : S × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ᵐ s ∂ν, (fun ω => U (s, ω)) =ᵐ[μ] u s) :
    Integrable (fun ω => ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν) μ ∧
    (∀ᵐ ω ∂μ, Integrable (fun q : S × Vec d => ‖U (q.1, translate q.2 ω)‖ ^ 2) (ν.prod κ)) ∧
    ∀ A : Set (FieldPair d),
      (∫ ω in A, ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν ∂μ) =
        ∫ x, ∫ s, ∫ ω in A, ‖(u s) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
  let v := fun q : S × Vec d => complexTranslation μ hμ q.2 (u q.1)
  let V := fun p : (S × Vec d) × FieldPair d => U (p.1.1, translate p.1.2 p.2)
  have hV : Measurable V := hU.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  have hv : Integrable (fun q => ‖v q‖ ^ 2) (ν.prod κ) := by
    simpa only [v, norm_complexTranslation] using hu.comp_fst κ
  have heV : ∀ᵐ q : S × Vec d ∂ν.prod κ, (fun ω => V (q, ω)) =ᵐ[μ] v q := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae heU] with q hq
    filter_upwards [(measurePreserving_translate μ hμ q.2).quasiMeasurePreserving.ae
      hq, coeFn_complexTranslation μ hμ q.2 (u q.1)] with ω huω hτω
    exact huω.trans hτω.symm
  have hi := c9_integrable_sq_joint_ae_representative hv hV heV
  have hpair : (fun ω => ∫ q, ‖V (q, ω)‖ ^ 2 ∂ν.prod κ) =ᵐ[μ]
      fun ω => ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν := by
    filter_upwards [hi.prod_left_ae] with ω hω
    exact integral_prod _ hω
  have hf := c9_conditional_quadratic_average_ae_fubini μ (ν.prod κ) hv hV heV
  refine ⟨hf.1.congr hpair, hi.prod_left_ae, fun A => ?_⟩
  rw [← integral_congr_ae (ae_restrict_of_ae hpair), hf.2 A]
  have hA : Integrable (fun p : (S × Vec d) × FieldPair d => ‖V p‖ ^ 2)
      ((ν.prod κ).prod (μ.restrict A)) :=
    hi.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have heq : (fun q : S × Vec d => ∫ ω in A, ‖v q ω‖ ^ 2 ∂μ) =ᵐ[ν.prod κ]
      fun q => ∫ ω in A, ‖V (q, ω)‖ ^ 2 ∂μ := by
    filter_upwards [heV] with q hq
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hq] with ω hω
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hω.symm
  rw [integral_congr_ae heq, integral_prod_symm _ hA.integral_prod_left]
  apply integral_congr_ae
  filter_upwards with x
  apply integral_congr_ae
  filter_upwards [heU] with s hs
  exact integral_congr_ae
    ((ae_restrict_of_ae ((measurePreserving_translate μ hμ x).quasiMeasurePreserving.ae
      hs)).mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)

private theorem c9_translated_conditional_ae_gradient_cylinder_fubini
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) [SFinite ν] (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    {u : Fin d → S → Lp ℂ 2 μ}
    (hu : ∀ j, Integrable (fun s => ‖u j s‖ ^ 2) ν)
    {U : Fin d → S × FieldPair d → ℂ} (hU : ∀ j, Measurable (U j))
    (heU : ∀ j, ∀ᵐ s ∂ν, (fun ω => U j (s, ω)) =ᵐ[μ] u j s) :
    Integrable (fun ω => ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν) μ ∧
    (∀ᵐ ω ∂μ, Integrable (fun q : S × Vec d =>
      ∑ j, ‖U j (q.1, translate q.2 ω)‖ ^ 2) (ν.prod κ)) ∧
    ∀ A : Set (FieldPair d),
      (∫ ω in A, ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν ∂μ) =
        ∑ j, ∫ x, ∫ s, ∫ ω in A, ‖(u j s) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
  have h j := c9_translated_conditional_ae_cylinder_fubini μ hμ ν κ (hu j) (hU j) (heU j)
  have he : (fun ω => ∫ s, ∫ x, ∑ j, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν) =ᵐ[μ]
      fun ω => ∑ j, ∫ s, ∫ x, ‖U j (s, translate x ω)‖ ^ 2 ∂κ ∂ν := by
    filter_upwards [ae_all_iff.mpr (fun j => (h j).2.1)] with ω hω
    rw [← integral_finsetSum Finset.univ (fun j _ => (hω j).integral_prod_left)]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => (hω j).prod_right_ae)] with s hs
    exact integral_finsetSum Finset.univ (fun j _ => hs j)
  refine ⟨(integrable_finsetSum Finset.univ (fun j _ => (h j).1)).congr he.symm, ?_, fun A => ?_⟩
  · filter_upwards [ae_all_iff.mpr (fun j => (h j).2.1)] with ω hω
    exact integrable_finsetSum Finset.univ (fun j _ => hω j)
  rw [integral_congr_ae (ae_restrict_of_ae he),
    integral_finsetSum Finset.univ (fun j _ => (h j).1.restrict (s := A))]
  exact Finset.sum_congr rfl (fun j _ => (h j).2.2 A)


/-- Conditional nested-ball interpolation for the genuine transpose
orbit and its derivative, retaining both lower-order force terms. -/
theorem local_time_transpose_conditional_derivative_ball_output_young
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {b t : ℝ}, 0 ≤ b → b ≤ t →
    ∀ {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R → ∀ ε : ℝ, 0 < ε →
    ∀ A : Set (FieldPair d),
      let L := Real.exp (2 * Λ₀) * Λ₀
      (1 / 2 : ℝ) * (∫ x in {x | euclideanNorm (x - z) ≤ r}, ∫ s in Icc b t,
        ∫ ω in A, ‖(T s.toNNReal g) (translate x ω)‖ ^ 2 ∂reducedLaw Q) ≤
      ε * (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
        ∫ ω in A, ‖(complexTransposeGradientOrbit Q T g s j) (translate x ω)‖ ^ 2
          ∂reducedLaw Q) +
      (1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / (R - r) ^ 2) *
        (((d : ℝ) ^ 2 * L ^ 2 / 2) *
          (∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
            ∫ ω in A, ‖(complexTransposeGradientOrbit Q T f s j) (translate x ω)‖ ^ 2
              ∂reducedLaw Q) +
          2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 *
            (∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
              ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q)) := by
  obtain ⟨B, hB, hy⟩ := local_time_transpose_derivative_ball_output_young d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ b t hb hbt P T hP hT f g hfg z r R hr hrR ε hε A L
  let μ := reducedLaw Q
  let ν := volume.restrict (Icc b t)
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let : IsFiniteMeasure (volume.restrict S) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z r).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict K) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z R).measure_lt_top (μ := volume)⟩
  obtain ⟨W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hineq⟩ := hy hb hbt hP hT hfg
  have hi v : Integrable (fun s : ℝ => ‖T s.toNNReal v‖ ^ 2) ν :=
    (((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (μ := (volume : Measure ℝ)) (K := Icc b t) isCompact_Icc
  have henergy v := hT.gradientOrbit_horizon_energy hP v ⟨t, hb.trans hbt⟩
  simp only [restrict_Ioc_eq_restrict_Icc] at henergy
  have hsub : Icc b t ⊆ Icc (0 : ℝ) t := fun s hs => ⟨hb.trans hs.1, hs.2⟩
  have hmem v : MemLp (complexTransposeGradientOrbit Q T v) 2 ν :=
    (henergy v).1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hcomp v j : Integrable (fun s : ℝ => ‖complexTransposeGradientOrbit Q T v s j‖ ^ 2) ν := by
    apply (timeLp_component_integrable_sq ((hmem v).toLp _) j).congr
    filter_upwards [(hmem v).coeFn_toLp] with s hs
    rw [hs]
  have hWF := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    ν (volume.restrict K) (hi f) hW heW
  have hVF := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    ν (volume.restrict S) (hi g) hV heV
  have hDF := c9_translated_conditional_ae_gradient_cylinder_fubini μ (reducedLaw_stationary Q)
    ν (volume.restrict K) (hcomp f) hD (fun j => heD.mono fun s hs => hs j)
  have hEF := c9_translated_conditional_ae_gradient_cylinder_fubini μ (reducedLaw_stationary Q)
    ν (volume.restrict K) (hcomp g) hE (fun j => heE.mono fun s hs => hs j)
  let α := (d : ℝ) ^ 2 * L ^ 2 / 2
  let β := 2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2
  let C := 1 / (4 * ε) + 4 * (d : ℝ) * B ^ 2 / (R - r) ^ 2
  have hpoly : ∀ᵐ ω ∂μ,
      (∫ s in Icc b t, ∫ x in K, α * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
        β * ‖W (s, translate x ω)‖ ^ 2) =
      α * (∫ s in Icc b t, ∫ x in K, ∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
        β * (∫ s in Icc b t, ∫ x in K, ‖W (s, translate x ω)‖ ^ 2) := by
    filter_upwards [hDF.2.1, hWF.2.1] with ω hiD hiW
    have hprod := integral_prod _ ((hiD.const_mul α).add (hiW.const_mul β))
    have hadd := integral_add (hiD.const_mul α) (hiW.const_mul β)
    simp only [Pi.add_apply, Pi.mul_apply] at hprod hadd
    rw [← hprod, hadd, integral_const_mul, integral_const_mul,
      integral_prod _ hiD, integral_prod _ hiW]
  have hm := setIntegral_mono_ae (s := A) (hVF.1.const_mul (1 / 2 : ℝ)).restrict
    ((hEF.1.const_mul ε).add (((hDF.1.const_mul α).add (hWF.1.const_mul β)).const_mul C)).restrict (by
      filter_upwards [hineq z r R hr hrR ε hε, hpoly] with ω hyω hpω
      rw [hpω] at hyω
      exact hyω)
  have hadd := integral_add ((hEF.1.const_mul ε).restrict (s := A))
    ((((hDF.1.const_mul α).add (hWF.1.const_mul β)).const_mul C).restrict (s := A))
  have hsplit := integral_add ((hDF.1.const_mul α).restrict (s := A))
    ((hWF.1.const_mul β).restrict (s := A))
  simp only [Pi.add_apply, Pi.mul_apply] at hadd hsplit hm
  rw [integral_const_mul, hadd, integral_const_mul, integral_const_mul,
    hsplit, integral_const_mul, integral_const_mul,
    hVF.2.2 A, hEF.2.2 A, hDF.2.2 A, hWF.2.2 A] at hm
  exact hm

/-- One-step conditional interpolation for the genuine transpose derivative.
The outer derivative mass has an arbitrarily small coefficient. -/
theorem local_time_transpose_conditional_derivative_interpolation
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B H Y : ℝ, 0 < B ∧ 0 < H ∧ 0 < Y ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (b e t : ℝ), 0 ≤ b → b < e → e ≤ t →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R →
    ∀ θ : ℝ, 0 < θ → ∀ A : Set (FieldPair d),
      let M := fun (v : Lp ℂ 2 (reducedLaw Q)) (ρ a : ℝ) =>
        ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∫ s in Icc a t,
          ∫ ω in A, ‖(T s.toNNReal v) (translate x ω)‖ ^ 2 ∂reducedLaw Q
      let q := (r + R) / 2
      let L := Real.exp (2 * Λ₀) * Λ₀
      let K := 4 * L * (H / (e - b) / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - q) ^ 2))
      let ε := θ / (2 * K)
      let C := 1 / (4 * ε) + 4 * (d : ℝ) * Y ^ 2 / (q - r) ^ 2
      M g r e ≤ θ * M g R b + 2 * C *
        (((d : ℝ) ^ 2 * L ^ 2 / 2) * K * M f R b +
          (2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2) * M f q e) := by
  obtain ⟨B, H, hB, hH, hcacc⟩ :=
    local_time_transpose_conditional_allData_gap_gradient_cylinder d
  obtain ⟨Y, hY, hyoung⟩ := local_time_transpose_conditional_derivative_ball_output_young d
  refine ⟨B, H, Y, hB, hH, hY, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f g hfg b e t hb hbe het z r R hr hrR θ hθ A
    M q L K ε C
  have hrq : r < q := by dsimp [q]; linarith
  have hqR : q < R := by dsimp [q]; linarith
  have hq : 0 < q := hr.trans hrq
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hK : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) hL)
      (add_pos_of_pos_of_nonneg
        (div_pos (div_pos hH (sub_pos.mpr hbe)) (by norm_num)) (by positivity))
  have hε : 0 < ε := div_pos hθ (mul_pos (by norm_num) hK)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let N := fun (v : Lp ℂ 2 (reducedLaw Q)) =>
    ∑ j, ∫ x in {x | euclideanNorm (x - z) ≤ q}, ∫ s in Icc e t,
      ∫ ω in A, ‖(complexTransposeGradientOrbit Q T v s j) (translate x ω)‖ ^ 2
        ∂reducedLaw Q
  let α := (d : ℝ) ^ 2 * L ^ 2 / 2
  let β := 2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hf : N f ≤ K * M f R b := hcacc hP hT f b e t hb hbe het z q R hq hqR A
  have hg : N g ≤ K * M g R b := hcacc hP hT g b e t hb hbe het z q R hq hqR A
  have hy : (1 / 2 : ℝ) * M g r e ≤ ε * N g + C * (α * N f + β * M f q e) :=
    hyoung (hb.trans hbe.le) het hP hT hfg z r q hr hrq ε hε A
  have hcoef : 2 * ε * K = θ := by
    dsimp [ε]
    field_simp
  calc
    M g r e = 2 * ((1 / 2 : ℝ) * M g r e) := by ring
    _ ≤ 2 * (ε * N g + C * (α * N f + β * M f q e)) :=
      mul_le_mul_of_nonneg_left hy (by norm_num)
    _ ≤ 2 * (ε * (K * M g R b) + C * (α * (K * M f R b) + β * M f q e)) := by
      gcongr
    _ = (2 * ε * K) * M g R b + 2 * C * (α * K * M f R b + β * M f q e) := by ring
    _ = θ * M g R b + 2 * C * (α * K * M f R b + β * M f q e) := by rw [hcoef]

private theorem c9_conditional_orbit_mass_integrable
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (v : Lp ℂ 2 (reducedLaw Q))
    (b t : ℝ) (κ : Measure (Vec d)) [IsFiniteMeasure κ] (A : Set (FieldPair d)) :
    Integrable (fun q : ℝ × Vec d => ∫ ω in A,
      ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂reducedLaw Q)
      ((volume.restrict (Icc b t)).prod κ) := by
  let μ := reducedLaw Q
  have he (q : ℝ × Vec d) : (∫ ω in A,
      ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ) =
      ‖localTimeLpRestrict μ A
        (complexTranslation μ (reducedLaw_stationary Q) q.2 (T q.1.toNNReal v))‖ ^ 2 := by
    rw [localTimeLpRestrict_norm_sq]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (coeFn_complexTranslation μ
      (reducedLaw_stationary Q) q.2 (T q.1.toNNReal v))] with ω hω
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hω.symm
  change Integrable (fun q : ℝ × Vec d => ∫ ω in A,
    ‖(T q.1.toNNReal v) (translate q.2 ω)‖ ^ 2 ∂μ) _
  simp_rw [he]
  have hc := ((localTimeLpRestrict_continuous μ A).comp
    ((continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
      (continuous_snd.prodMk (((hT.continuous_apply hP v).comp
        continuous_real_toNNReal).comp continuous_fst)))).norm.pow 2
  have ht : Integrable (fun s : ℝ => ‖T s.toNNReal v‖ ^ 2)
      (volume.restrict (Icc b t)) :=
    (((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  apply (ht.comp_fst κ).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    apply pow_le_pow_left₀ (norm_nonneg _)
    exact (localTimeLpRestrict_norm_le μ A _).trans (norm_complexTranslation _ _ _ _).le

private theorem c9_conditional_orbit_mass_mono
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (v : Lp ℂ 2 (reducedLaw Q))
    (z : Vec d) {r R b e t : ℝ} (hrR : r ≤ R) (hbe : b ≤ e)
    (A : Set (FieldPair d)) :
    (∫ x in {x | euclideanNorm (x - z) ≤ r}, ∫ s in Icc e t,
      ∫ ω in A, ‖(T s.toNNReal v) (translate x ω)‖ ^ 2 ∂reducedLaw Q) ≤
    ∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
      ∫ ω in A, ‖(T s.toNNReal v) (translate x ω)‖ ^ 2 ∂reducedLaw Q := by
  let κ := volume.restrict {x : Vec d | euclideanNorm (x - z) ≤ R}
  let : IsFiniteMeasure κ := ⟨by simpa only [κ, Measure.restrict_apply_univ] using
    (isCompact_physical_euclidean_closedBall z R).measure_lt_top (μ := volume)⟩
  have hi := c9_conditional_orbit_mass_integrable hP hT v b t κ A
  have hm : (volume.restrict (Icc e t)).prod
      (volume.restrict {x : Vec d | euclideanNorm (x - z) ≤ r}) ≤
      (volume.restrict (Icc b t)).prod κ :=
    Measure.prod_mono (Measure.restrict_mono (Icc_subset_Icc_left hbe) le_rfl)
      (Measure.restrict_mono (fun _ hx => hx.trans hrR) le_rfl)
  rw [← integral_prod_symm _ (hi.mono_measure hm), ← integral_prod_symm _ hi]
  exact integral_mono_measure hm
    (ae_of_all _ fun _ => integral_nonneg fun _ => sq_nonneg _) hi

private theorem c9_derivative_residual_scale
    {L N Z B H Y δ h u : ℝ} (hL : 0 ≤ L) (hN : 0 ≤ N) (hZ : 0 ≤ Z)
    (hH : 0 ≤ H) (hδ : 0 < δ) (hh : 0 < h) (hu : 1 ≤ u) :
    let K := fun (a r : ℝ) => 4 * L * (H / a / 2 +
      10 * L ^ 3 * (Z + N * B ^ 2 / r ^ 2))
    let C := fun (a r : ℝ) => 16 * K a r + 4 * N * Y ^ 2 / r ^ 2
    let α := N ^ 2 * L ^ 2 / 2
    let β := 2 * N * L ^ 2 * Z
    2 * C (δ / u ^ 2) (h / u) * (α * K (δ / u ^ 2) (h / u) + β) ≤
      (2 * C δ h * (α * K δ h + β)) * u ^ 4 := by
  intro K C α β
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu
  have he : K (δ / u ^ 2) (h / u) = u ^ 2 * K δ h -
      (u ^ 2 - 1) * (40 * L ^ 4 * Z) := by
    dsimp [K]
    field_simp
    ring
  have hk : K (δ / u ^ 2) (h / u) ≤ u ^ 2 * K δ h := by
    rw [he]
    exact sub_le_self _ (by positivity)
  have hs : 4 * N * Y ^ 2 / (h / u) ^ 2 = u ^ 2 * (4 * N * Y ^ 2 / h ^ 2) := by
    field_simp
  have hc : C (δ / u ^ 2) (h / u) ≤ u ^ 2 * C δ h := by
    dsimp [C]
    rw [hs]
    nlinarith only [hk]
  have ha : α * K (δ / u ^ 2) (h / u) + β ≤ u ^ 2 * (α * K δ h + β) := by
    have hfirst := mul_le_mul_of_nonneg_left hk (show 0 ≤ α by dsimp [α]; positivity)
    have hlast : β ≤ u ^ 2 * β := le_mul_of_one_le_left (by dsimp [β]; positivity) hu2
    nlinarith only [hfirst, hlast]
  calc
    _ ≤ 2 * (u ^ 2 * C δ h) * (u ^ 2 * (α * K δ h + β)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hc (by norm_num)) ha
        (by dsimp [α, β, K]; positivity) (by dsimp [C, K]; positivity)
    _ = _ := by ring

/-- Conditional derivative cylinder estimate after absorption of the outer
transpose derivative mass. Only the original orbit remains on the right. -/
theorem local_time_transpose_conditional_derivative_cylinder_absorption
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B H Y : ℝ, 0 < B ∧ 0 < H ∧ 0 < Y ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (b e t : ℝ), 0 ≤ b → b < e → e ≤ t →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R → ∀ A : Set (FieldPair d),
      let L := Real.exp (2 * Λ₀) * Λ₀
      let δ := 3 * (e - b) / 4
      let h := (R - r) / 4
      let K := 4 * L * (H / δ / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / h ^ 2))
      let C := 16 * K + 4 * (d : ℝ) * Y ^ 2 / h ^ 2
      (∫ x in {x | euclideanNorm (x - z) ≤ r}, ∫ s in Icc e t,
        ∫ ω in A, ‖(T s.toNNReal g) (translate x ω)‖ ^ 2 ∂reducedLaw Q) ≤
      4 * C * (((d : ℝ) ^ 2 * L ^ 2 / 2) * K +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2) *
        (∫ x in {x | euclideanNorm (x - z) ≤ R}, ∫ s in Icc b t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨B, H, Y, hB, hH, hY, hstep⟩ :=
    local_time_transpose_conditional_derivative_interpolation d
  refine ⟨B, H, Y, hB, hH, hY, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f g hfg b e t hb hbe het z r R hr hrR A L δ h K C
  let M := fun (v : Lp ℂ 2 (reducedLaw Q)) (ρ a : ℝ) =>
    ∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∫ s in Icc a t,
      ∫ ω in A, ‖(T s.toNNReal v) (translate x ω)‖ ^ 2 ∂reducedLaw Q
  let τ : ℕ → ℝ := fun n => b + (e - b) / (4 : ℝ) ^ n
  let ρ : ℕ → ℝ := fun n => R - (R - r) / (2 : ℝ) ^ n
  let σ : ℕ → ℝ := fun n => (ρ n + ρ (n + 1)) / 2
  let k := fun (a x : ℝ) => 4 * L * (H / a / 2 +
    10 * L ^ 3 * (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / x ^ 2))
  let c := fun (a x : ℝ) => 16 * k a x + 4 * (d : ℝ) * Y ^ 2 / x ^ 2
  let α := (d : ℝ) ^ 2 * L ^ 2 / 2
  let β := 2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hpow (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]; norm_num
  have hτb (n : ℕ) : b < τ n := by
    dsimp [τ]
    exact lt_add_of_pos_right b (div_pos (sub_pos.mpr hbe) (by positivity))
  have hτe (n : ℕ) : τ n ≤ e := by
    have hi := div_le_self (sub_nonneg.mpr hbe.le)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) : 1 ≤ (4 : ℝ) ^ n)
    dsimp [τ]; linarith only [hi]
  have hτgap (n : ℕ) : τ n - τ (n + 1) = δ / ((2 : ℝ) ^ n) ^ 2 := by
    dsimp [τ, δ]; rw [hpow n, pow_succ]; field_simp; ring
  have hτstep (n : ℕ) : τ (n + 1) < τ n := by
    have hp : 0 < δ / ((2 : ℝ) ^ n) ^ 2 := by positivity
    linarith only [hτgap n, hp]
  have hρr (n : ℕ) : r ≤ ρ n := by
    have hi := div_le_self (sub_nonneg.mpr hrR.le)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    dsimp [ρ]; linarith only [hi]
  have hρR (n : ℕ) : ρ n < R := by
    dsimp [ρ]
    exact sub_lt_self R (div_pos (sub_pos.mpr hrR) (by positivity))
  have hσleft (n : ℕ) : σ n - ρ n = h / (2 : ℝ) ^ n := by
    dsimp [σ, ρ, h]; rw [pow_succ]; field_simp; ring
  have hσright (n : ℕ) : ρ (n + 1) - σ n = h / (2 : ℝ) ^ n := by
    dsimp [σ, ρ, h]; rw [pow_succ]; field_simp; ring
  have hρσ (n : ℕ) : ρ n < σ n := by
    have hp : 0 < h / (2 : ℝ) ^ n := by positivity
    linarith only [hσleft n, hp]
  have hσρ (n : ℕ) : σ n < ρ (n + 1) := by
    have hp : 0 < h / (2 : ℝ) ^ n := by positivity
    linarith only [hσright n, hp]
  let F : ℕ → ℝ := fun n => M g (ρ n) (τ n)
  let MW := M f R b
  let E := 2 * C * (α * K + β)
  have hMW : 0 ≤ MW := integral_nonneg fun _ => integral_nonneg fun _ =>
    integral_nonneg fun _ => sq_nonneg _
  have hE : 0 ≤ E := by dsimp [E, C, K, α, β]; positivity
  have hbounded (n : ℕ) : F n ≤ M g R b :=
    c9_conditional_orbit_mass_mono hP hT g z (hρR n).le (hτb n).le A
  have hrec (n : ℕ) : F n ≤ (1 / 32 : ℝ) * F (n + 1) + (E * MW) * 16 ^ n := by
    let Δ := δ / ((2 : ℝ) ^ n) ^ 2
    let x := h / (2 : ℝ) ^ n
    have hΔ : 0 < Δ := by dsimp [Δ]; positivity
    have hx : 0 < x := by dsimp [x]; positivity
    have hk : 0 < k Δ x := by dsimp [k]; positivity
    have hc : 0 ≤ c Δ x := by dsimp [c, k]; positivity
    have hα : 0 ≤ α := by dsimp [α]; positivity
    have hβ : 0 ≤ β := by dsimp [β]; positivity
    have hn := hstep hP hT hfg (τ (n + 1)) (τ n) t
      (hb.trans (hτb _).le) (hτstep n) ((hτe n).trans het)
      z (ρ n) (ρ (n + 1)) (hr.trans_le (hρr n))
      ((hρσ n).trans (hσρ n)) (1 / 32) (by norm_num) A
    dsimp only at hn
    rw [hτgap n, hσright n] at hn
    change F n ≤ (1 / 32 : ℝ) * F (n + 1) +
      2 * (1 / (4 * ((1 / 32 : ℝ) / (2 * k Δ x))) +
        4 * (d : ℝ) * Y ^ 2 / (σ n - ρ n) ^ 2) *
        (α * k Δ x * M f (ρ (n + 1)) (τ (n + 1)) + β * M f (σ n) (τ n)) at hn
    have hinv : 1 / (4 * ((1 / 32 : ℝ) / (2 * k Δ x))) = 16 * k Δ x := by
      field_simp; ring
    rw [hinv, hσleft] at hn
    change F n ≤ (1 / 32 : ℝ) * F (n + 1) +
      2 * c Δ x * (α * k Δ x * M f (ρ (n + 1)) (τ (n + 1)) + β * M f (σ n) (τ n)) at hn
    have hm₁ : M f (ρ (n + 1)) (τ (n + 1)) ≤ MW :=
      c9_conditional_orbit_mass_mono hP hT f z (hρR _).le (hτb _).le A
    have hm₂ : M f (σ n) (τ n) ≤ MW :=
      c9_conditional_orbit_mass_mono hP hT f z ((hσρ n).trans (hρR _)).le (hτb _).le A
    have hmass : α * k Δ x * M f (ρ (n + 1)) (τ (n + 1)) + β * M f (σ n) (τ n) ≤
        (α * k Δ x + β) * MW := by
      calc
        _ ≤ α * k Δ x * MW + β * MW := add_le_add
          (mul_le_mul_of_nonneg_left hm₁ (mul_nonneg hα hk.le))
          (mul_le_mul_of_nonneg_left hm₂ hβ)
        _ = _ := by ring
    have hscale := c9_derivative_residual_scale (B := B) (Y := Y)
      hL.le (Nat.cast_nonneg d) (sq_nonneg ‖ζ‖) hH.le hδ hh
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    change 2 * c Δ x * (α * k Δ x + β) ≤ E * ((2 : ℝ) ^ n) ^ 4 at hscale
    have hp16 : ((2 : ℝ) ^ n) ^ 4 = (16 : ℝ) ^ n := by
      rw [← pow_mul, Nat.mul_comm n 4, pow_mul]; norm_num
    rw [hp16] at hscale
    have herr : 2 * c Δ x *
        (α * k Δ x * M f (ρ (n + 1)) (τ (n + 1)) + β * M f (σ n) (τ n)) ≤
        (E * MW) * 16 ^ n := by
      calc
        _ ≤ 2 * c Δ x * ((α * k Δ x + β) * MW) :=
          mul_le_mul_of_nonneg_left hmass (mul_nonneg (by norm_num) hc)
        _ = (2 * c Δ x * (α * k Δ x + β)) * MW := by ring
        _ ≤ (E * 16 ^ n) * MW := mul_le_mul_of_nonneg_right hscale hMW
        _ = _ := by ring
    exact hn.trans (add_le_add (le_refl _) herr)
  have habs := local_time_cylinder_mass_absorption F (mul_nonneg hE hMW) hbounded hrec
  have hz : F 0 = M g r e := by
    simp only [F, τ, ρ, pow_zero, div_one, add_sub_cancel, sub_sub_cancel]
  rw [hz] at habs
  convert habs using 1 <;> dsimp [E, MW] <;> ring

/-- The absorbed conditional estimate is an almost-everywhere physical
cylinder estimate for any joint representatives of the two actual orbits. -/
theorem local_time_transpose_ae_derivative_cylinder_of_representatives
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B H Y : ℝ, 0 < B ∧ 0 < H ∧ 0 < Y ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ W V : ℝ × FieldPair d → ℂ, Measurable W → Measurable V →
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal g) →
    ∀ (b e t : ℝ), 0 ≤ b → b < e → e ≤ t →
    ∀ (z : Vec d) (r R : ℝ), 0 < r → r < R →
      let L := Real.exp (2 * Λ₀) * Λ₀
      let δ := 3 * (e - b) / 4
      let h := (R - r) / 4
      let K := 4 * L * (H / δ / 2 + 10 * L ^ 3 *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / h ^ 2))
      let C := 16 * K + 4 * (d : ℝ) * Y ^ 2 / h ^ 2
      ∀ᵐ ω ∂reducedLaw Q,
        (∫ s in Icc e t, ∫ x in {x | euclideanNorm (x - z) ≤ r},
          ‖V (s, translate x ω)‖ ^ 2) ≤
        4 * C * (((d : ℝ) ^ 2 * L ^ 2 / 2) * K +
          2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2) *
          (∫ s in Icc b t, ∫ x in {x | euclideanNorm (x - z) ≤ R},
            ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, H, Y, hB, hH, hY, hcyl⟩ :=
    local_time_transpose_conditional_derivative_cylinder_absorption d
  refine ⟨B, H, Y, hB, hH, hY, ?_⟩
  intro Λ₀ r₀ Q i ζ P T hP hT f g hfg W V hW hV heW heV
    b e t hb hbe het z r R hr hrR L δ h K C
  let μ := reducedLaw Q
  let : IsProbabilityMeasure μ := reducedLaw_probability Q
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  let U := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let : IsFiniteMeasure (volume.restrict S) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z r).measure_lt_top (μ := volume)⟩
  let : IsFiniteMeasure (volume.restrict U) := ⟨by
    simpa only [Measure.restrict_apply_univ] using
      (isCompact_physical_euclidean_closedBall z R).measure_lt_top (μ := volume)⟩
  have hi (v : Lp ℂ 2 μ) (a : ℝ) : Integrable (fun s : ℝ => ‖T s.toNNReal v‖ ^ 2)
      (volume.restrict (Icc a t)) :=
    (((hT.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc
  have hWF := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc b t)) (volume.restrict U) (hi f b) hW heW
  have hVF := translated_conditional_cylinder_fubini μ (reducedLaw_stationary Q)
    (volume.restrict (Icc e t)) (volume.restrict S) (hi g e) hV heV
  apply ae_le_of_forall_setIntegral_le hVF.1 (hWF.1.const_mul _)
  intro A _ _
  rw [integral_const_mul, hVF.2.2 A, hWF.2.2 A]
  exact hcyl hP hT hfg b e t hb hbe het z r R hr hrR A

/-- Fubini for translated joint orbit representatives and arbitrary environment events. -/
theorem local_time_transpose_conditional_cylinder_fubini
    {d : ℕ} {S : Type*} [MeasurableSpace S]
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (ν : Measure S) [SFinite ν] (κ : Measure (Vec d)) [IsFiniteMeasure κ]
    {u : S → Lp ℂ 2 μ} (hu : Integrable (fun s => ‖u s‖ ^ 2) ν)
    {U : S × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[μ] u s) :
    Integrable (fun ω => ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν) μ ∧
    (∀ᵐ ω ∂μ, Integrable (fun q : S × Vec d => ‖U (q.1, translate q.2 ω)‖ ^ 2) (ν.prod κ)) ∧
    ∀ A : Set (FieldPair d),
      (∫ ω in A, ∫ s, ∫ x, ‖U (s, translate x ω)‖ ^ 2 ∂κ ∂ν ∂μ) =
        ∫ x, ∫ s, ∫ ω in A, ‖(u s) (translate x ω)‖ ^ 2 ∂μ ∂ν ∂κ := by
  exact translated_conditional_cylinder_fubini μ hμ ν κ hu hU heU

end EinsteinFull.Blueprint
