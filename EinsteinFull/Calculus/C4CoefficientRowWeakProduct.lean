import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.ComplexForceDriftSupport
import EinsteinFull.Calculus.ComplexLpChainSupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Integration by parts for an actual coefficient row and two horizontal H¹ functions. -/
theorem coefficient_row_weak_product
    {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (hβ : IsReducedDriftObservation Q hQ β)
    (u v : Lp ℂ 2 (reducedLaw Q)) (G V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V)
    (l : Fin d)
    : (∫ ω, (∑ k : Fin d, (ω.1 0 l k : ℂ) * G k ω) * v ω ∂reducedLaw Q) =
      -(∫ ω, u ω * (∑ k : Fin d, (ω.1 0 l k : ℂ) * V k ω) ∂reducedLaw Q) -
        2 * (∫ ω, β l ω * u ω * v ω ∂reducedLaw Q) := by
  classical
  have hprod (j k i : Fin d) (v V : Lp ℂ 2 (reducedLaw Q))
      (hV : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i v V) :
      ∃ H : Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) i
          (complexCoefficientMul Q j k v) H ∧
        (H : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
          (ω.1 0 j k : ℂ) * V ω +
            (coordinateDerivative i (fun x => ω.1 x j k) 0 : ℂ) * v ω := by
    classical
    have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
    let μ := reducedLaw Q
    let T := complexTranslation μ (reducedLaw_stationary Q)
    let M := complexCoefficientMul Q j k
    let A (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
      (T (t • unitVector i)).toContinuousLinearMap.comp
        (M.comp (T (-(t • unitVector i))).toContinuousLinearMap)
    have hAe (t : ℝ) (f : Lp ℂ 2 μ) : A t f =ᵐ[μ] fun ω =>
        (ω.1 (t • unitVector i) j k : ℂ) * f ω := by
      have hm := (measurePreserving_translate μ (reducedLaw_stationary Q) (t • unitVector i)).quasiMeasurePreserving
      have hc := hm.ae (complexCoefficientMul_coe Q j k (T (-(t • unitVector i)) f))
      have ht := hm.ae (coeFn_complexTranslation μ (reducedLaw_stationary Q)
        (-(t • unitVector i)) f)
      filter_upwards [coeFn_complexTranslation μ (reducedLaw_stationary Q)
        (t • unitVector i) (M (T (-(t • unitVector i)) f)), hc, ht] with ω h1 h2 h3
      change (M (T (-(t • unitVector i)) f)) (translate (t • unitVector i) ω) =
        ((translate (t • unitVector i) ω).1 0 j k : ℂ) *
          (T (-(t • unitVector i)) f) (translate (t • unitVector i) ω) at h2
      change (T (-(t • unitVector i)) f) (translate (t • unitVector i) ω) =
        f (translate (-(t • unitVector i)) (translate (t • unitVector i) ω)) at h3
      change T (t • unitVector i) (M (T (-(t • unitVector i)) f)) ω = _
      rw [h1, h2, h3]
      simp only [translate_add, neg_add_cancel, translate_zero, translate_matrix, add_zero]
    have hA0 (f : Lp ℂ 2 μ) : A 0 f = M f := by
      simp only [A, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        zero_smul, neg_zero, complexTranslation_zero, T]
    have hAn (t : ℝ) (f : Lp ℂ 2 μ) :
        ‖A t f‖ ≤ ‖M‖ * ‖f‖ := by
      change ‖T _ (M (T _ f))‖ ≤ _
      rw [norm_complexTranslation]
      exact (M.le_opNorm _).trans_eq (by rw [norm_complexTranslation])
    have hAc (f : Lp ℂ 2 μ) : Continuous (fun t : ℝ => A t f) := by
      have hx : Continuous (fun t : ℝ => t • unitVector i) :=
        continuous_id.smul continuous_const
      have hi := (continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
        (hx.neg.prodMk (continuous_const : Continuous (fun _ : ℝ => f)))
      exact (continuous_complexTranslation μ (reducedLaw_stationary Q)).comp
        (hx.prodMk (M.continuous.comp hi))
    let dc : FieldPair d → ℝ := fun ω => coordinateDerivative i (fun x => ω.1 x j k) 0
    have horb (ω : FieldPair d) : orbit (fun η : FieldPair d => η.1 0 j k) ω =
        (fun x => ω.1 x j k) := by
      funext x
      simp only [orbit, translate_matrix, add_zero]
    have hdcm : MemLp (fun ω => (dc ω : ℂ)) ∞ μ := by
      have hh := Complex.ofRealCLM.comp_memLp'
        (timeFlux_coefficient_jets_memLp_top hQ j k [i])
      change MemLp (fun ω => (horizontalDerivative i
        (fun η : FieldPair d => η.1 0 j k) ω : ℂ)) ∞ μ at hh
      simpa only [horizontalDerivative, horb] using hh
    have hRmem : MemLp (fun ω => (dc ω : ℂ) * v ω) 2 μ :=
      hdcm.fun_mul (Lp.memLp v)
    let R : Lp ℂ 2 μ := hRmem.toLp (fun ω => (dc ω : ℂ) * v ω)
    obtain ⟨B, hB, hb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ j k
    obtain ⟨S, _, hs⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
      node_eq_u2E_reduced_u2D_bounds_of_deps d D
    have hcurve : ∀ᵐ ω ∂μ, ∀ s : ℝ,
        HasDerivAt (fun t : ℝ => ω.1 (t • unitVector i) j k)
          (coordinateDerivative i (fun x => ω.1 x j k) (s • unitVector i)) s := by
      filter_upwards [hs Q hQ] with ω hω s
      convert ((hω.1.1 j k).differentiable (by simp) (s • unitVector i)).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_id' s).smul_const (unitVector i)) using 1 <;>
        simp only [one_smul, coordinateDerivative, Function.comp_def]
    have hbound : ∀ᵐ ω ∂μ, ∀ x : Vec d,
        |coordinateDerivative i (fun y => ω.1 y j k) x| ≤ B [i] := by
      filter_upwards [hb [i]] with ω hω x
      simpa only [orbit_iteratedHorizontalDerivative, coordinateIterate, horb] using hω x
    let q (t : ℝ) (ω : FieldPair d) : ℂ :=
      ((t⁻¹ * (ω.1 (t • unitVector i) j k - ω.1 0 j k) : ℝ) : ℂ) * v ω
    have hqbound (t : ℝ) (ht : t ≠ 0) : ∀ᵐ ω ∂μ,
        ‖q t ω‖ ≤ B [i] * ‖v ω‖ := by
      filter_upwards [hcurve, hbound] with ω hd hbω
      have hl : ‖ω.1 (t • unitVector i) j k - ω.1 0 j k‖ ≤ B [i] * ‖t‖ := by
        simpa only [zero_smul, sub_zero] using
          Convex.norm_image_sub_le_of_norm_deriv_le
            (fun s _ => (hd s).differentiableAt)
            (fun s _ => by rw [(hd s).deriv]; exact hbω _)
            convex_univ (mem_univ 0) (mem_univ t)
      have hq : |t⁻¹ * (ω.1 (t • unitVector i) j k - ω.1 0 j k)| ≤ B [i] := by
        rw [abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr ht), mul_comm]
        exact hl
      simpa only [q, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul] using
        mul_le_mul_of_nonneg_right hq (norm_nonneg (v ω))
    have hR : Tendsto (fun t : ℝ => (t : ℂ)⁻¹ • (A t v - M v))
        (𝓝[≠] (0 : ℝ)) (𝓝 R) := by
      apply tendsto_complexLp_of_dominated
        (F := q) (f := fun ω => (dc ω : ℂ) * v ω)
        (b := fun ω => 2 * B [i] * ‖v ω‖)
      · intro t
        filter_upwards [Lp.coeFn_smul (t : ℂ)⁻¹ (A t v - M v),
          Lp.coeFn_sub (A t v) (M v), hAe t v, complexCoefficientMul_coe Q j k v]
          with ω h1 h2 h3 h4
        change M v ω = _ at h4
        simp only [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul,
          q, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_sub]
        ring
      · exact hRmem.coeFn_toLp
      · convert ((Lp.memLp v).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul
          ((2 * B [i]) ^ 2) using 1
        simp only [mul_pow]
      · filter_upwards [self_mem_nhdsWithin] with t ht
        filter_upwards [hqbound t ht, hbound] with ω hq hbω
        have hd : |dc ω| ≤ B [i] := hbω 0
        calc
          ‖q t ω - (dc ω : ℂ) * v ω‖ ≤ ‖q t ω‖ + ‖(dc ω : ℂ) * v ω‖ := norm_sub_le _ _
          _ ≤ B [i] * ‖v ω‖ + B [i] * ‖v ω‖ := by
            gcongr
            simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
              mul_le_mul_of_nonneg_right hd (norm_nonneg (v ω))
          _ = _ := by ring
      · filter_upwards [hcurve] with ω hω
        have hd := (hω 0).tendsto_slope_zero
        simp only [zero_smul, zero_add, smul_eq_mul] at hd
        exact ((Complex.continuous_ofReal.tendsto _).comp hd).mul_const (v ω)
    have hfirst : Tendsto (fun t : ℝ =>
        A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v)))
        (𝓝[≠] (0 : ℝ)) (𝓝 (M V)) := by
      have hz : Tendsto (fun t : ℝ =>
          A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v) - V))
          (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        apply tendsto_zero_iff_norm_tendsto_zero.mpr
        apply squeeze_zero' (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (Filter.Eventually.of_forall fun t => hAn t _)
        simpa only [mul_zero] using
          ((tendsto_iff_norm_sub_tendsto_zero.mp hV).const_mul ‖M‖)
      have hc : Tendsto (fun t : ℝ => A t V) (𝓝[≠] (0 : ℝ)) (𝓝 (A 0 V)) :=
        ((hAc V).tendsto 0).mono_left nhdsWithin_le_nhds
      rw [hA0] at hc
      convert hz.add hc using 1
      · funext t
        rw [map_sub, sub_add_cancel]
      · simp only [zero_add]
    refine ⟨M V + R, ?_, ?_⟩
    · have hl := hfirst.add hR
      apply hl.congr'
      exact Filter.Eventually.of_forall fun t => by
        change A t ((t : ℂ)⁻¹ • (T (t • unitVector i) v - v)) +
          (t : ℂ)⁻¹ • (A t v - M v) = (t : ℂ)⁻¹ • (T (t • unitVector i) (M v) - M v)
        rw [map_smul, map_sub]
        have he : A t (T (t • unitVector i) v) = T (t • unitVector i) (M v) := by
          change T _ (M (T _ (T _ v))) = _
          rw [complexTranslation_neg_cancel]
        rw [he]
        module
    · filter_upwards [Lp.coeFn_add (M V) R, complexCoefficientMul_coe Q j k V,
        hRmem.coeFn_toLp] with ω h1 h2 h3
      change M V ω = _ at h2
      change R ω = _ at h3
      simp only [h1, Pi.add_apply, h2, h3, dc]

  choose H hH hHe using fun k => hprod l k k v (V k) (hV k)
  let a (k : Fin d) (ω : FieldPair d) : ℂ := (ω.1 0 l k : ℂ)
  let da (k : Fin d) (ω : FieldPair d) : ℂ :=
    (coordinateDerivative k (fun x => ω.1 x l k) 0 : ℂ)
  have hrow : ∀ᵐ ω ∂reducedLaw Q, (∑ k, da k ω) = 2 * β l ω := by
    obtain ⟨Λ, A, B, _, _, _, _, hb⟩ :=
      node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity Q.ellipticity_parameter
    filter_upwards [(hb d D.dependenceRange Q).2.2, hβ l] with ω hω hobs
    have hsym (k : Fin d) : (fun x => ω.1 x l k) = (fun x => ω.1 x k l) := by
      funext x
      exact congrArg (fun M : Mat d => M k l) (hω.1 x).1
    dsimp only [da]
    simp_rw [hsym]
    rw [hobs]
    push_cast
    ring
  have hL (k : Fin d) : Integrable (fun ω => a k ω * G k ω * v ω) (reducedLaw Q) := by
    apply ((Lp.memLp (G k)).integrable_mul
      (Lp.memLp (complexCoefficientMul Q l k v))).congr
    filter_upwards [complexCoefficientMul_coe Q l k v] with ω hω
    dsimp only [Pi.mul_apply, a]
    rw [hω]
    ring
  have hR (k : Fin d) : Integrable (fun ω => u ω * a k ω * V k ω) (reducedLaw Q) := by
    apply ((Lp.memLp u).integrable_mul
      (Lp.memLp (complexCoefficientMul Q l k (V k)))).congr
    filter_upwards [complexCoefficientMul_coe Q l k (V k)] with ω hω
    dsimp only [Pi.mul_apply, a]
    rw [hω]
    ring
  have hD (k : Fin d) : Integrable (fun ω => da k ω * u ω * v ω) (reducedLaw Q) := by
    apply ((Lp.memLp u).integrable_mul
      (Lp.memLp (H k - complexCoefficientMul Q l k (V k)))).congr
    filter_upwards [Lp.coeFn_sub (H k) (complexCoefficientMul Q l k (V k)),
      hHe k, complexCoefficientMul_coe Q l k (V k)] with ω h1 h2 h3
    dsimp only [Pi.mul_apply, da]
    rw [h1, Pi.sub_apply, h2, h3]
    ring
  have hb : Integrable (fun ω => β l ω * u ω * v ω) (reducedLaw Q) := by
    apply ((integrable_finsetSum Finset.univ (fun k _ => hD k)).const_mul
      (1 / 2 : ℂ)).congr
    filter_upwards [hrow] with ω hω
    rw [← Finset.sum_mul, ← Finset.sum_mul, hω]
    ring
  have hik (k : Fin d) :
      (∫ ω, a k ω * G k ω * v ω ∂reducedLaw Q) =
        -(∫ ω, u ω * a k ω * V k ω ∂reducedLaw Q) -
          ∫ ω, da k ω * u ω * v ω ∂reducedLaw Q := by
    calc
      _ = ∫ ω, G k ω * complexCoefficientMul Q l k v ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [complexCoefficientMul_coe Q l k v] with ω hω
        dsimp only [a]
        rw [hω]
        ring
      _ = -(∫ ω, u ω * H k ω ∂reducedLaw Q) :=
        (complexHorizontalDerivatives_integration_by_parts (hG k) (hH k)).2.2
      _ = -((∫ ω, u ω * a k ω * V k ω ∂reducedLaw Q) +
          ∫ ω, da k ω * u ω * v ω ∂reducedLaw Q) := by
        congr 1
        calc
          _ = ∫ ω, (u ω * a k ω * V k ω + da k ω * u ω * v ω) ∂reducedLaw Q := by
            apply integral_congr_ae
            filter_upwards [hHe k] with ω hω
            rw [hω]
            dsimp only [a, da]
            ring
          _ = _ := integral_add (hR k) (hD k)
      _ = _ := by ring
  have hDs : (∑ k, ∫ ω, da k ω * u ω * v ω ∂reducedLaw Q) =
      2 * ∫ ω, β l ω * u ω * v ω ∂reducedLaw Q := by
    rw [← integral_finsetSum _ (fun k _ => hD k), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hrow] with ω hω
    rw [← Finset.sum_mul, ← Finset.sum_mul, hω]
    ring
  have hLs : (∫ ω, (∑ k, a k ω * G k ω) * v ω ∂reducedLaw Q) =
      ∑ k, ∫ ω, a k ω * G k ω * v ω ∂reducedLaw Q := by
    simp_rw [Finset.sum_mul]
    exact integral_finsetSum _ (fun k _ => hL k)
  have hRs : (∫ ω, u ω * (∑ k, a k ω * V k ω) ∂reducedLaw Q) =
      ∑ k, ∫ ω, u ω * a k ω * V k ω ∂reducedLaw Q := by
    simp_rw [Finset.mul_sum, ← mul_assoc]
    exact integral_finsetSum _ (fun k _ => hR k)
  change (∫ ω, (∑ k, a k ω * G k ω) * v ω ∂reducedLaw Q) =
    -(∫ ω, u ω * (∑ k, a k ω * V k ω) ∂reducedLaw Q) -
      2 * (∫ ω, β l ω * u ω * v ω ∂reducedLaw Q)
  rw [hLs, hRs]
  simp_rw [hik, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [hDs]

end EinsteinFull.Blueprint
