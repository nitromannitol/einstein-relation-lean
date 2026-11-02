import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.S4GeneratorBridgeSupport
open MeasureTheory Filter
open scoped Topology NNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation
theorem response_observations_uniform_bounds
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
        (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β →
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
        (∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ C) ∧
        ∀ (lam : ℝ) (j : Fin d), ∀ᵐ ω ∂reducedLaw Q,
          ‖(β j + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) j) ω‖ ≤
            C * (1 + |lam|) := by
  let E : ℝ := Real.exp (2 * D.ellipticity)
  let M : ℝ := E * D.ellipticity
  let K : ℝ≥0 := Real.toNNReal
    (E * (2 * D.ellipticity ^ 2 + D.ellipticity) * Real.sqrt d)
  let B : ℝ := (1 / 2 : ℝ) * (d * (K : ℝ))
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  have hE : 0 < E := Real.exp_pos _
  have hM : 0 ≤ M := (mul_pos hE hΛ).le
  have hB : 0 ≤ B := by positivity
  let C : ℝ := 1 + E + M + B
  have hEC : E ≤ C := by dsimp [C]; linarith
  have hMC : M ≤ C := by dsimp [C]; linarith
  have hBC : B ≤ C := by dsimp [C]; linarith
  refine ⟨C, by dsimp [C]; linarith, ?_⟩
  intro Q hQ β a μ hβ ha hμ
  have hμphys := ae_of_ae_map Probability.measurable_reduce.aemeasurable hμ
  have hclock : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ C := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_le (Lp.stronglyMeasurable μ).measurable.norm measurable_const)).mpr
    filter_upwards [Q.regular, hμphys] with ω hω heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    change |Real.exp (-2 * ω.2 0)| ≤ C
    rw [abs_of_pos (Real.exp_pos _)]
    apply le_trans _ hEC
    apply Real.exp_le_exp.mpr
    have := (abs_le.mp (hω.2.1 0)).1
    linarith
  have hbetabound (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ‖β j ω‖ ≤ C := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_le (Lp.stronglyMeasurable (β j)).measurable.norm measurable_const)).mpr
    have hb := ae_of_ae_map Probability.measurable_reduce.aemeasurable (hβ j)
    filter_upwards [Q.regular, hb] with ω hω heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_matrixDivDrift_le (reducedCoefficient ω)
      (reducedCoefficient_lipschitz hΛ hω) 0 j).trans hBC
  have habound (i j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ‖a i j ω‖ ≤ C := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_le (Lp.stronglyMeasurable (a i j)).measurable.norm measurable_const)).mpr
    have hac := ae_of_ae_map Probability.measurable_reduce.aemeasurable (ha i j)
    filter_upwards [Q.regular, hac] with ω hω heq
    rw [heq, Complex.norm_real, Real.norm_eq_abs]
    exact (abs_reducedCoefficient_le hΛ hω 0 i j).trans hMC
  refine ⟨hclock, ?_⟩
  intro lam j
  let i : Fin d := ⟨0, by omega⟩
  filter_upwards [hbetabound j, habound i j,
    Lp.coeFn_add (β j) ((lam : ℂ) • a i j),
    Lp.coeFn_smul (lam : ℂ) (a i j)] with ω hb hac hadd hsmul
  change ‖(β j + (lam : ℂ) • a i j) ω‖ ≤ C * (1 + |lam|)
  rw [hadd]
  change ‖β j ω + ((lam : ℂ) • a i j) ω‖ ≤ C * (1 + |lam|)
  rw [hsmul]
  calc
    ‖β j ω + (lam : ℂ) • a i j ω‖ ≤ ‖β j ω‖ + ‖(lam : ℂ) • a i j ω‖ := norm_add_le _ _
    _ = ‖β j ω‖ + |lam| * ‖a i j ω‖ := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ C + |lam| * C := add_le_add hb (mul_le_mul_of_nonneg_left hac (abs_nonneg _))
    _ = C * (1 + |lam|) := by ring
end EinsteinFull.Blueprint
