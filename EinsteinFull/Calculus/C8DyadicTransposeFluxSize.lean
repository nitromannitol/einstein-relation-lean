import EinsteinFull.Calculus.C10DyadicGradientFluxSize
import EinsteinFull.Calculus.C4SmoothedDuhamelSupport
import EinsteinFull.Calculus.ComplexPhysicalWeakTimeSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Calculus.C10DyadicLargeWindowProjection
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Structural Euclidean column bound, retaining the literal force multiplier. -/
theorem dyadic_transpose_coefficient_column_bound
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (ζ : ℂ) (H : Lp ℂ 2 (reducedLaw Q)) :
    Real.sqrt (∑ j : Fin d, ‖(-2 * ζ) • complexCoefficientMul Q j i H‖^2) ≤
      2 * (d : ℝ) * (Real.exp (2 * Λ) * Λ) * ‖ζ‖ * ‖H‖ := by
  let K := Real.exp (2 * Λ) * Λ
  have hcoord (j : Fin d) :
      ‖(-2 * ζ) • complexCoefficientMul Q j i H‖ ≤ 2 * ‖ζ‖ * K * ‖H‖ := by
    rw [norm_smul, norm_mul]
    have hc := ((complexCoefficientMul Q j i).le_opNorm H).trans
      (mul_le_mul_of_nonneg_right (norm_complexCoefficientMul_le Q j i) (norm_nonneg H))
    calc
      ‖(-2 : ℂ)‖ * ‖ζ‖ * ‖complexCoefficientMul Q j i H‖ ≤
          ‖(-2 : ℂ)‖ * ‖ζ‖ * (K * ‖H‖) :=
        mul_le_mul_of_nonneg_left hc (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = _ := by norm_num; ring
  calc
    _ ≤ ∑ j : Fin d, ‖(-2 * ζ) • complexCoefficientMul Q j i H‖ := by
      apply Real.sqrt_le_iff.mpr
      exact ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _),
        Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)⟩
    _ ≤ ∑ _j : Fin d, 2 * ‖ζ‖ * K * ‖H‖ := Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; dsimp only [K]; ring

/-- On the force window the actual transpose primitive costs one inverse square root.
The primitive remains explicit; no scalar decay premise is introduced. -/
theorem dyadic_transpose_flux_primitive_reduction
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ)
    (Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (s u : ℝ≥0) (hs : 1 ≤ (s : ℝ))
    (hζ : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2) :
    Real.sqrt (∑ j : Fin d,
      ‖(-2 * ζ) • complexCoefficientMul Q j i
        (∫ t in Set.Icc (s : ℝ) (u : ℝ),
          transposeEndpoint Q i Pdag β t.toNNReal)‖^2) ≤
      (4 * (d : ℝ) * (Real.exp (2 * Λ) * Λ)) *
        ‖∫ t in Set.Icc (s : ℝ) (u : ℝ),
          transposeEndpoint Q i Pdag β t.toNNReal‖ / Real.sqrt (s : ℝ) := by
  have hspos : 0 < (s : ℝ) := lt_of_lt_of_le zero_lt_one hs
  have hsqrt : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
  have hforce : ‖ζ‖ ≤ 2 / Real.sqrt (s : ℝ) := by
    apply (le_div_iff₀ hsqrt).mpr
    exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith))
      (norm_nonneg ζ)).trans hζ
  let K := Real.exp (2 * Λ) * Λ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  apply (dyadic_transpose_coefficient_column_bound Q i ζ _).trans
  calc
    _ ≤ 2 * (d : ℝ) * K * (2 / Real.sqrt (s : ℝ)) *
        ‖∫ t in Set.Icc (s : ℝ) (u : ℝ), transposeEndpoint Q i Pdag β t.toNNReal‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hforce (by positivity)) (norm_nonneg _)
    _ = _ := by dsimp only [K]; ring

/-- Moving the actual transpose primitive to the second bilinear slot gives
an actual forward primitive. Both integration endpoints are retained. -/
theorem dyadic_transpose_primitive_pairing
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (g : Lp ℂ 2 (reducedLaw Q))
    (s u : ℝ≥0) :
    c4EndpointPairing Q
      (∫ t in Set.Icc (s : ℝ) (u : ℝ), transposeEndpoint Q i Pdag β t.toNNReal) g =
      c4EndpointPairing Q (β i)
        (∫ t in Set.Icc (s : ℝ) (u : ℝ), P t.toNNReal g) := by
  have hTi : IntegrableOn (fun t : ℝ => Pdag t.toNNReal (β i))
      (Set.Icc (s : ℝ) (u : ℝ)) :=
    ((hPd.continuous_apply hP (β i)).comp continuous_real_toNNReal).integrableOn_Icc
  have hPi : IntegrableOn (fun t : ℝ => P t.toNNReal g)
      (Set.Icc (s : ℝ) (u : ℝ)) :=
    ((hP.2.2.1 g).comp continuous_real_toNNReal).integrableOn_Icc
  calc
    _ = ∫ t in Set.Icc (s : ℝ) (u : ℝ),
        c4EndpointPairing Q (Pdag t.toNNReal (β i)) g :=
      (((c4EndpointPairing Q).flip g).integral_comp_comm hTi).symm
    _ = ∫ t in Set.Icc (s : ℝ) (u : ℝ),
        c4EndpointPairing Q (β i) (P t.toNNReal g) := by
      apply integral_congr_ae
      exact ae_of_all _ fun t => by
        simpa only [c4EndpointPairing_apply, mul_comm] using (hPd t.toNNReal g (β i)).symm
    _ = _ := (c4EndpointPairing Q (β i)).integral_comp_comm hPi

/-- The forward primitive on a positive dyadic interval has the actual
integrated all-data horizontal gradient. -/
theorem dyadic_forward_primitive_gradient
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (g : Lp ℂ 2 (reducedLaw Q)) (s u : ℝ≥0) (hs : 0 < (s : ℝ)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ t in Set.Icc (s : ℝ) (u : ℝ), P t.toNNReal g)
      (fun k => ∫ t in Set.Icc (s : ℝ) (u : ℝ), (hP.gradientOrbit g t) k) := by
  intro k
  let T := PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k
  have hf : IntegrableOn (fun t : ℝ => P t.toNNReal g)
      (Set.Icc (s : ℝ) (u : ℝ)) :=
    ((hP.2.2.1 g).comp continuous_real_toNNReal).integrableOn_Icc
  have hg : IntegrableOn (fun t : ℝ => (hP.gradientOrbit g t) k)
      (Set.Icc (s : ℝ) (u : ℝ)) :=
    IntegrableOn.mono_set (T.integrable_comp (hP.integrableOn_gradientOrbit g u))
      (Icc_subset_Icc s.coe_nonneg le_rfl)
  apply HasComplexHorizontalDerivative.integral_of_ae hf hg
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact hP.gradientOrbit_spec g (hs.trans_le ht.1) k

/-- Weak divergence of the actual initial drift against the actual forward
primitive identifies the transpose primitive pairing without scalar premises. -/
theorem dyadic_transpose_primitive_drift_pairing
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (g : Lp ℂ 2 (reducedLaw Q)) (s u : ℝ≥0) (hs : 0 < (s : ℝ)) :
    c4EndpointPairing Q
      (∫ t in Set.Icc (s : ℝ) (u : ℝ), transposeEndpoint Q i Pdag β t.toNNReal) g =
      -(1 / 2 : ℂ) * ∫ ω, ∑ k, (ω.1 0 k i : ℂ) *
        (∫ t in Set.Icc (s : ℝ) (u : ℝ), (hP.gradientOrbit g t) k) ω ∂reducedLaw Q := by
  rw [dyadic_transpose_primitive_pairing hP hPd, c4EndpointPairing_apply]
  exact hβ.integral_mul i _ _ (dyadic_forward_primitive_gradient hP g s u hs)

/-- The full transpose generator applied to the constant density is the actual
force-weighted drift. The drift observation is used through weak divergence. -/
theorem dyadic_transpose_generator_const
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i : Fin d) (ζ : ℂ) :
    let := reducedLaw_probability Q
    IsComplexTransposeGeneratorPair Q i ζ (Lp.const 2 (reducedLaw Q) 1)
      ((-2 * ζ) • β i) := by
  let := reducedLaw_probability Q
  refine ⟨fun _ => 0,
    hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) 1, ?_⟩
  intro v V hV
  have hl : (∫ ω, ((-2 * ζ) • β i) ω * v ω ∂reducedLaw Q) =
      (-2 * ζ) * ∫ ω, β i ω * v ω ∂reducedLaw Q := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul (-2 * ζ) (β i)] with ω hω
    simp only [hω, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have ha : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω * V j ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]
  have hb : (∫ ω, Lp.const 2 (reducedLaw Q) (1 : ℂ) ω *
      (∑ j, (ω.1 0 j i : ℂ) * V j ω) ∂reducedLaw Q) =
      ∫ ω, ∑ j, (ω.1 0 j i : ℂ) * V j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, one_mul]
  rw [hl, ha, hb, hβ.integral_mul i v V hV]
  ring

/-- The actual force-weighted drift primitive is the increment of the transpose
orbit of the constant density. -/
theorem dyadic_transpose_primitive_const_increment
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) (s u : ℝ≥0) (hsu : s ≤ u) :
    let := reducedLaw_probability Q
    (-2 * ζ) • (∫ t in Set.Icc (s : ℝ) (u : ℝ),
      transposeEndpoint Q i Pdag β t.toNNReal) =
      Pdag u (Lp.const 2 (reducedLaw Q) 1) -
        Pdag s (Lp.const 2 (reducedLaw Q) 1) := by
  let := reducedLaw_probability Q
  have hcont : Continuous (fun t : ℝ => Pdag t.toNNReal ((-2 * ζ) • β i)) :=
    (hPd.continuous_apply hP _).comp continuous_real_toNNReal
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (0 : ℝ) (s : ℝ))
    (hcont.intervalIntegrable (μ := volume) (s : ℝ) (u : ℝ))
  rw [hPd.integral_orbit_eq_sub hP (dyadic_transpose_generator_const hβ i ζ) s,
    hPd.integral_orbit_eq_sub hP (dyadic_transpose_generator_const hβ i ζ) u] at hsum
  have hi : (∫ t in (s : ℝ)..(u : ℝ), Pdag t.toNNReal ((-2 * ζ) • β i)) =
      Pdag u (Lp.const 2 (reducedLaw Q) 1) -
        Pdag s (Lp.const 2 (reducedLaw Q) 1) := by
    calc
      _ = (Pdag u (Lp.const 2 (reducedLaw Q) 1) - Lp.const 2 (reducedLaw Q) 1) -
          (Pdag s (Lp.const 2 (reducedLaw Q) 1) - Lp.const 2 (reducedLaw Q) 1) :=
        eq_sub_of_add_eq' hsum
      _ = _ := by abel
  rw [intervalIntegral.integral_of_le (show (s : ℝ) ≤ (u : ℝ) from hsu),
    ← integral_Icc_eq_integral_Ioc] at hi
  simpa only [transposeEndpoint, map_smul, integral_smul] using hi

/- SUPERVISOR EXACT TARGET; replace this comment with proved declaration.
theorem dyadic_transpose_flux_size
    (henergy : node_e_u3A_energy_u2D_targetStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2*s →
        ‖ζ‖ * Real.sqrt (2*(s : ℝ)) ≤ 2 →
      Real.sqrt (∑ j : Fin d,
        ‖(-2 * ζ) • complexCoefficientMul Q j ⟨0, by omega⟩
          (∫ r in Set.Icc (s : ℝ) (u : ℝ),
            transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal)‖^2) ≤
        C * (s : ℝ) ^ (-(d : ℝ)/4) := by
-/
end EinsteinFull.Blueprint
