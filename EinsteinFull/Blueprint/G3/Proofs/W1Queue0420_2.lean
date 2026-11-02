import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_cauchy
import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_dyadic_u2D_increments
import EinsteinFull.Blueprint.G3.node_e_u3A_local_u2D_av
import EinsteinFull.Blueprint.G3.node_stationary_u2D_analytic_u2D_semigroup_u23_flux
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Calculus.IsotropicGaussianSupport
import EinsteinFull.Work.W4.ActualLateForceHomogeneousPropagationProof
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

section Flux

variable {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
  (Q : EnvironmentLaw d Λ₀ r₀) (ζ : ℂ)
  (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
  (β : Fin d → Lp ℂ 2 (reducedLaw Q))
  (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))

/-- The strong gradients and literal fluxes do not depend on the witnesses
chosen by the dyadic and analytic dependencies. -/
theorem finiteTimeFlux_unique
    {G F H K : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (hK : IsFiniteTimeFlux hd Q ζ P Pdag β a μ H K) : G = H ∧ F = K := by
  obtain ⟨hG, hU, hgrad, hF⟩ := hF
  obtain ⟨hH, hV, hgradH, hK⟩ := hK
  have hGH : G = H := by
    funext t ν j
    exact (hgrad t ν j).unique (hgradH t ν j)
  refine ⟨hGH, ?_⟩
  subst H
  funext t ν j
  exact Lp.ext ((hF t ν j).trans (hK t ν j).symm)

/-- At time zero the actual finite-time flux is the coefficient column,
including for the transpose index. -/
theorem finiteTimeFlux_zero
    {G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F)
    (ν : FluxIndex d) (j : Fin d) :
    F 0 ν j = a j (ν.elim id (fun _ => ⟨0, by omega⟩)) := by
  obtain ⟨hG, hU, _hgrad, hF⟩ := hF
  apply Lp.ext
  filter_upwards [hF 0 ν j, Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω hz
  change (0 : Lp ℂ 2 (reducedLaw Q)) ω = 0 at hz
  simp only [finiteTimeFluxObservation, NNReal.coe_zero, Set.Icc_self, integral_singleton, measureReal_def,
    measure_singleton, ENNReal.toReal_zero, zero_smul] at hω
  cases ν <;> simpa only [Sum.elim_inl, Sum.elim_inr, hz, mul_zero,
    Finset.sum_const_zero, add_zero, sub_zero] using hω

end Flux

/-- A holomorphic averaged flux is differentiable at every point of the
closed inner disc. The enclosing open disc also contains its boundary. -/
theorem differentiableAt_of_scaled_disc {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) (t : ℝ)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * Real.sqrt t < 3})
    (ζ : ℂ) (hζ : ‖ζ‖ * Real.sqrt t ≤ 1) : DifferentiableAt ℂ f ζ := by
  apply hf.differentiableAt
  exact (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds
    (lt_of_le_of_lt hζ (by norm_num))

/-- The extended averaging seminorm bound is precisely the uniform weighted
Euclidean bound on the literal Gaussian averages, with no finiteness coercion. -/
theorem gaussianAveragingSeminorm_le_iff {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Fin d → Lp ℂ 2 (reducedLaw Q))
    (C : ℝ) (hC : 0 ≤ C) :
    gaussianAveragingSeminorm hd Q F ≤ ENNReal.ofReal C ↔
      ∀ ρ : ℝ, 1 ≤ ρ →
        ρ ^ ((d : ℝ) / 2) * Real.sqrt (∑ j : Fin d,
          ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (F j)‖ ^ 2) ≤ C := by
  simp only [gaussianAveragingSeminorm, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hC]

/-- The dyadic dependency controls every actual flux witness. In particular
its estimates apply to the single family supplied by the analytic dependency. -/
theorem finiteTimeFlux_dyadic_bounds
    (hdyadic : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
      (‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖ ^ 2) ≤ C ∧
        ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, IsComplexLocalObservation Q (C * n) (V j)) ∧
          Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤
            C * Real.exp (-c * (n : ℝ) ^ 2)) ∧
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
        ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
        ∃ Y B : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, (Y j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
            fun ω => ∑ k : Fin d, a j k ω *
              (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k) ω) ∧
          (∀ j, (B j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
            fun ω => ν.elim (fun _ => 0) (fun _ =>
              -2 * ζ * a j ⟨0, by omega⟩ ω *
                (∫ r in Set.Icc (s : ℝ) (u : ℝ),
                  transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)) ∧
          (∀ j, F u ν j - F s ν j = Y j + B j) ∧
          Real.sqrt (∑ j : Fin d, ‖Y j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
          Real.sqrt (∑ j : Fin d, ‖B j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
          ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
            (∀ j, IsComplexLocalObservation Q (C * n * Real.sqrt (s : ℝ)) (V j)) ∧
            Real.sqrt (∑ j : Fin d, ‖F u ν j - F s ν j - V j‖ ^ 2) ≤
              C * (2 + (s : ℝ)) ^ N * Real.exp (-c * (n : ℝ) ^ 2)
 := by
  intro d hd D
  obtain ⟨C, c, N, hC, hc, hdyadic⟩ := hdyadic d hd D
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hflux
  obtain ⟨H, K, hK, hunit, hinc⟩ :=
    hdyadic Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
  obtain ⟨rfl, rfl⟩ := finiteTimeFlux_unique hd Q ζ P Pdag β a μ hK hflux
  exact ⟨hunit, hinc⟩

/-- Analyticity transfers to any actual flux family, so the differentiability
clause in the Cauchy target needs no choice of new fluxes or averaging radius. -/
theorem finiteTimeFlux_averaged_differentiableAt
    (hanalytic : node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ P Pdag : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)) →
      (∀ ζ, IsComplexTransposeSemigroup Q (P ζ) (Pdag ζ)) →
    ∀ G F : ℂ → ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ζ, IsFiniteTimeFlux hd Q ζ (P ζ) (Pdag ζ) β a μ (G ζ) (F ζ)) →
      let A := fun (ζ : ℂ) (t : ℝ≥0) (ν : FluxIndex d) (ρ : ℝ) (j : Fin d) =>
        ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
            (centeredComplexLp Q (F ζ t ν j))
      ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) → ∀ (ν : FluxIndex d) (ρ : ℝ),
        1 ≤ ρ → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 1 →
        ∀ j : Fin d, DifferentiableAt ℂ (fun z => A z t ν ρ j) ζ := by
  intro d hd D Q hQ β a μ hβ ha hμ P Pdag hP hPdag G F hflux
  obtain ⟨C, N, _hC, hanalytic⟩ := hanalytic d hd D
  obtain ⟨H, K, hK, _hhol, hA, _hbound⟩ :=
    hanalytic Q hQ β a μ hβ ha hμ P Pdag hP hPdag
  have hKF : K = F := by
    funext ζ
    exact (finiteTimeFlux_unique hd Q ζ (P ζ) (Pdag ζ) β a μ (hK ζ) (hflux ζ)).2
  subst K
  dsimp only
  intro t ht ν ρ hρ ζ hζ j
  exact differentiableAt_of_scaled_disc _ (t : ℝ)
    (hA t (lt_of_lt_of_le (by norm_num) ht) ν ρ hρ j).1 ζ hζ

/-- Cauchy's estimate with a spatial weight fixed before taking the force
derivative. The constant is independent of the positive weight. -/
theorem weighted_cauchy_deriv_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) (b w M : ℝ) (hb : 0 < b) (hw : 0 < w)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * b < 3})
    (hbound : ∀ z : ℂ, ‖z‖ * b ≤ 2 → w * ‖f z‖ ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ * b ≤ 1) : w * ‖deriv f ζ‖ ≤ M * b := by
  have hdisc (z : ℂ) (hz : z ∈ Metric.closedBall ζ b⁻¹) : ‖z‖ * b ≤ 2 := by
    have hz' : ‖z - ζ‖ ≤ b⁻¹ := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz
    calc
      ‖z‖ * b ≤ (‖z - ζ‖ + ‖ζ‖) * b :=
        mul_le_mul_of_nonneg_right (norm_le_norm_sub_add z ζ) hb.le
      _ = ‖z - ζ‖ * b + ‖ζ‖ * b := add_mul _ _ _
      _ ≤ b⁻¹ * b + 1 := add_le_add (mul_le_mul_of_nonneg_right hz' hb.le) hζ
      _ = 2 := by rw [inv_mul_cancel₀ hb.ne']; norm_num
  have hder : ‖deriv f ζ‖ ≤ (M / w) / b⁻¹ := by
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (inv_pos.mpr hb)
    · apply hf.diffContOnCl_ball
      intro z hz
      exact lt_of_le_of_lt (hdisc z hz) (by norm_num)
    · intro z hz
      apply (le_div_iff₀ hw).mpr
      simpa only [mul_comm] using hbound z (hdisc z (Metric.sphere_subset_closedBall hz))
  calc
    w * ‖deriv f ζ‖ ≤ w * ((M / w) / b⁻¹) := mul_le_mul_of_nonneg_left hder hw.le
    _ = M * b := by rw [div_inv_eq_mul]; field_simp [hw.ne']

/-- Integrating the weighted Cauchy bound along the force segment retains
the same spatial weight and yields the factor `‖ζ‖`. -/
theorem weighted_cauchy_sub_zero_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (f : ℂ → E) (b w M : ℝ) (hb : 0 < b) (hw : 0 < w)
    (hf : DifferentiableOn ℂ f {z | ‖z‖ * b < 3})
    (hbound : ∀ z : ℂ, ‖z‖ * b ≤ 2 → w * ‖f z‖ ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ * b ≤ 1) : w * ‖f ζ - f 0‖ ≤ M * ‖ζ‖ * b := by
  have hinner (z : ℂ) (hz : z ∈ Metric.closedBall 0 b⁻¹) : ‖z‖ * b ≤ 1 := by
    have hz' : ‖z‖ ≤ b⁻¹ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    calc
      ‖z‖ * b ≤ b⁻¹ * b := mul_le_mul_of_nonneg_right hz' hb.le
      _ = 1 := inv_mul_cancel₀ hb.ne'
  have hdiff (z : ℂ) (hz : z ∈ Metric.closedBall 0 b⁻¹) : DifferentiableAt ℂ f z := by
    apply hf.differentiableAt
    exact (isOpen_lt (continuous_norm.mul continuous_const) continuous_const).mem_nhds
      (lt_of_le_of_lt (hinner z hz) (by norm_num))
  have hder (z : ℂ) (hz : z ∈ Metric.closedBall 0 b⁻¹) : ‖deriv f z‖ ≤ M * b / w := by
    apply (le_div_iff₀ hw).mpr
    simpa only [mul_comm] using weighted_cauchy_deriv_le f b w M hb hw hf hbound z (hinner z hz)
  have hzero : (0 : ℂ) ∈ Metric.closedBall 0 b⁻¹ := Metric.mem_closedBall_self (inv_nonneg.mpr hb.le)
  have hz : ζ ∈ Metric.closedBall 0 b⁻¹ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    simpa only [one_div] using (le_div_iff₀ hb).mpr hζ
  have hsub := (convex_closedBall (0 : ℂ) b⁻¹).norm_image_sub_le_of_norm_deriv_le
    hdiff hder hzero hz
  simp only [sub_zero] at hsub
  calc
    w * ‖f ζ - f 0‖ ≤ w * ((M * b / w) * ‖ζ‖) := mul_le_mul_of_nonneg_left hsub hw.le
    _ = M * ‖ζ‖ * b := by field_simp [hw.ne']

/-- Each coordinate is bounded by the explicit Euclidean norm, with the
same coordinate carrier as the frozen averaging seminorm. -/
theorem norm_le_euclidean {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (v : Fin d → E) (j : Fin d) :
    ‖v j‖ ≤ Real.sqrt (∑ k : Fin d, ‖v k‖ ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg (v j))]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖)
    (Finset.mem_univ j))

/-- A weighted coordinate bound yields a Euclidean bound with only the
structural dimension factor; no supremum norm is used. -/
theorem weighted_euclidean_le {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (v : Fin d → E) (w M : ℝ) (hw : 0 ≤ w)
    (hv : ∀ j, w * ‖v j‖ ≤ M) :
    w * Real.sqrt (∑ j : Fin d, ‖v j‖ ^ 2) ≤ d * M := by
  have hs : Real.sqrt (∑ j : Fin d, ‖v j‖ ^ 2) ≤ ∑ j : Fin d, ‖v j‖ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨Finset.sum_nonneg (fun j _ => norm_nonneg (v j)),
      Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg (v j))⟩
  calc
    w * Real.sqrt (∑ j : Fin d, ‖v j‖ ^ 2) ≤ w * ∑ j : Fin d, ‖v j‖ :=
      mul_le_mul_of_nonneg_left hs hw
    _ = ∑ j : Fin d, w * ‖v j‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _j : Fin d, M := Finset.sum_le_sum (fun j _ => hv j)
    _ = d * M := by simp

/-- Coordinatewise Cauchy estimates preserve the spatial weight in the
explicit Euclidean norm. The dimension loss is structural. -/
theorem weighted_euclidean_cauchy_deriv_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → Fin d → E) (b w M : ℝ) (hb : 0 < b) (hw : 0 < w)
    (hf : ∀ j, DifferentiableOn ℂ (fun z => f z j) {z | ‖z‖ * b < 3})
    (hbound : ∀ z : ℂ, ‖z‖ * b ≤ 2 →
      w * Real.sqrt (∑ j : Fin d, ‖f z j‖ ^ 2) ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ * b ≤ 1) :
    w * Real.sqrt (∑ j : Fin d, ‖deriv (fun z => f z j) ζ‖ ^ 2) ≤ d * M * b := by
  have hcoord (z : ℂ) (hz : ‖z‖ * b ≤ 2) (j : Fin d) : w * ‖f z j‖ ≤ M :=
    (mul_le_mul_of_nonneg_left (norm_le_euclidean (f z) j) hw.le).trans (hbound z hz)
  calc
    w * Real.sqrt (∑ j : Fin d, ‖deriv (fun z => f z j) ζ‖ ^ 2) ≤ d * (M * b) :=
      weighted_euclidean_le _ w (M * b) hw.le (fun j =>
        weighted_cauchy_deriv_le _ b w M hb hw (hf j) (fun z hz => hcoord z hz j) ζ hζ)
    _ = d * M * b := (mul_assoc _ _ _).symm

/-- The force-segment estimate holds for the Euclidean vector of Gaussian
averages with one constant independent of the averaging radius. -/
theorem weighted_euclidean_cauchy_sub_zero_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : ℂ → Fin d → E) (b w M : ℝ) (hb : 0 < b) (hw : 0 < w)
    (hf : ∀ j, DifferentiableOn ℂ (fun z => f z j) {z | ‖z‖ * b < 3})
    (hbound : ∀ z : ℂ, ‖z‖ * b ≤ 2 →
      w * Real.sqrt (∑ j : Fin d, ‖f z j‖ ^ 2) ≤ M)
    (ζ : ℂ) (hζ : ‖ζ‖ * b ≤ 1) :
    w * Real.sqrt (∑ j : Fin d, ‖f ζ j - f 0 j‖ ^ 2) ≤ d * M * ‖ζ‖ * b := by
  have hcoord (z : ℂ) (hz : ‖z‖ * b ≤ 2) (j : Fin d) : w * ‖f z j‖ ≤ M :=
    (mul_le_mul_of_nonneg_left (norm_le_euclidean (f z) j) hw.le).trans (hbound z hz)
  calc
    w * Real.sqrt (∑ j : Fin d, ‖f ζ j - f 0 j‖ ^ 2) ≤ d * (M * ‖ζ‖ * b) :=
      weighted_euclidean_le _ w (M * ‖ζ‖ * b) hw.le (fun j =>
        weighted_cauchy_sub_zero_le _ b w M hb hw (hf j) (fun z hz => hcoord z hz j) ζ hζ)
    _ = d * M * ‖ζ‖ * b := by ring

/-- Centering and the literal isotropic Gaussian average distribute over
subtraction. Both spatial Bochner integrals are genuinely integrable. -/
theorem centered_isotropicAverage_sub {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (U V : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q (U - V))) =
    (∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q U)) -
    (∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (centeredComplexLp Q V)) := by
  have hc : centeredComplexLp Q (U - V) = centeredComplexLp Q U - centeredComplexLp Q V := by
    simpa only [centeredComplexLpCLM_apply] using (centeredComplexLpCLM Q).map_sub U V
  simp only [hc, map_sub, smul_sub]
  have hs : 0 < ρ ^ 2 := sq_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ)
  exact integral_sub (integrable_isotropicGaussian_integrand Q _ hs _)
    (integrable_isotropicGaussian_integrand Q _ hs _)

/-- The analytic step for the actual centered Gaussian averages: an outer
seminorm estimate gives the inner Euclidean derivative estimate and the
centered force-difference seminorm estimate, uniformly in spatial radius.
The outer estimate remains a separate dyadic/local-averaging obligation. -/
theorem centered_isotropicAverage_cauchy_bounds {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : ℂ → Fin d → Lp ℂ 2 (reducedLaw Q))
    (t M : ℝ) (ht : 0 < t) (hM : 0 ≤ M)
    (hbound : ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt t ≤ 2 →
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F ζ j)) ≤
        ENNReal.ofReal M) :
    let A := fun (ζ : ℂ) (ρ : ℝ) (j : Fin d) =>
      ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (centeredComplexLp Q (F ζ j))
    (∀ ρ : ℝ, 1 ≤ ρ → ∀ j : Fin d,
      DifferentiableOn ℂ (fun ζ => A ζ ρ j) {ζ | ‖ζ‖ * Real.sqrt t < 3}) →
    (∀ ρ : ℝ, 1 ≤ ρ → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt t ≤ 1 →
      (∀ j, DifferentiableAt ℂ (fun z => A z ρ j) ζ) ∧
      ρ ^ ((d : ℝ) / 2) * Real.sqrt (∑ j : Fin d,
        ‖deriv (fun z => A z ρ j) ζ‖ ^ 2) ≤ d * M * Real.sqrt t) ∧
    (∀ ζ : ℂ, ‖ζ‖ * Real.sqrt t ≤ 1 →
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F ζ j - F 0 j)) ≤
        ENNReal.ofReal (d * M * ‖ζ‖ * Real.sqrt t)) := by
  intro A hhol
  have hb : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have houter (ρ : ℝ) (hρ : 1 ≤ ρ) (ζ : ℂ) (hζ : ‖ζ‖ * Real.sqrt t ≤ 2) :
      ρ ^ ((d : ℝ) / 2) * Real.sqrt (∑ j : Fin d, ‖A ζ ρ j‖ ^ 2) ≤ M :=
    (gaussianAveragingSeminorm_le_iff hd Q _ M hM).mp (hbound ζ hζ) ρ hρ
  constructor
  · intro ρ hρ ζ hζ
    refine ⟨fun j => differentiableAt_of_scaled_disc _ t (hhol ρ hρ j) ζ hζ, ?_⟩
    exact weighted_euclidean_cauchy_deriv_le (fun z j => A z ρ j)
      (Real.sqrt t) (ρ ^ ((d : ℝ) / 2)) M hb
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ) _) (hhol ρ hρ)
      (houter ρ hρ) ζ hζ
  · intro ζ hζ
    apply (gaussianAveragingSeminorm_le_iff hd Q _ _ (by positivity)).mpr
    intro ρ hρ
    have havg (j : Fin d) := centered_isotropicAverage_sub Q ρ hρ (F ζ j) (F 0 j)
    simp_rw [havg]
    exact weighted_euclidean_cauchy_sub_zero_le (fun z j => A z ρ j)
      (Real.sqrt t) (ρ ^ ((d : ℝ) / 2)) M hb
      (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hρ) _) (hhol ρ hρ)
      (houter ρ hρ) ζ hζ

/-- A fixed structural dilation of time changes the logarithmic bound by
only a structural multiplicative constant, uniformly for all times at least one. -/
theorem exists_log_scaled_le (B : ℝ) (hB : 1 ≤ B) :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℝ, 1 ≤ s →
      Real.log (2 + B ^ 2 * s) ≤ K * Real.log (2 + s) := by
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hBpos : 0 < B ^ 2 := zero_lt_one.trans_le hBsq
  have hlB : 0 ≤ Real.log (B ^ 2) := Real.log_nonneg hBsq
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  let k := Real.log (B ^ 2) / Real.log 3
  have hk : 0 ≤ k := div_nonneg hlB hl3.le
  refine ⟨1 + k, by positivity, ?_⟩
  intro s hs
  have hspos : 0 < 2 + s := by linarith only [hs]
  have hlog : Real.log 3 ≤ Real.log (2 + s) :=
    Real.log_le_log (by norm_num) (by linarith only [hs])
  have hconstant : Real.log (B ^ 2) ≤ k * Real.log (2 + s) := by
    calc
      _ = k * Real.log 3 := by dsimp [k]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog hk
  calc
    Real.log (2 + B ^ 2 * s) ≤ Real.log (B ^ 2 * (2 + s)) :=
      Real.log_le_log (by positivity) (by nlinarith only [hBsq])
    _ = Real.log (B ^ 2) + Real.log (2 + s) :=
      Real.log_mul hBpos.ne' hspos.ne'
    _ ≤ k * Real.log (2 + s) + Real.log (2 + s) := add_le_add hconstant le_rfl
    _ = (1 + k) * Real.log (2 + s) := by ring

/-- Centering a genuine joint-local observation preserves its locality. -/
theorem isComplexLocalObservation_centered {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q))
    (hU : IsComplexLocalObservation Q R U) :
    IsComplexLocalObservation Q R (centeredComplexLp Q U) := by
  obtain ⟨f, hf, heq⟩ := hU
  refine ⟨fun ω => f ω - ∫ η, U η ∂reducedLaw Q, hf.sub measurable_const, ?_⟩
  filter_upwards [heq, coeFn_centeredComplexLp Q U] with ω hω hc
  rw [hω]
  exact hc.symm

/-- Actual reduced-law centering is bounded on the explicit Euclidean
coordinate norm by a law-independent factor two. -/
theorem euclidean_centered_le_two {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (Y : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Real.sqrt (∑ j : Fin d, ‖centeredComplexLp Q (Y j)‖ ^ 2) ≤
      2 * Real.sqrt (∑ j : Fin d, ‖Y j‖ ^ 2) := by
  have hnorm (j : Fin d) : ‖centeredComplexLp Q (Y j)‖ ≤ 2 * ‖Y j‖ := by
    calc
      _ = ‖centeredComplexLpCLM Q (Y j)‖ := congrArg norm (centeredComplexLpCLM_apply Q _).symm
      _ ≤ ‖centeredComplexLpCLM Q‖ * ‖Y j‖ := (centeredComplexLpCLM Q).le_opNorm _
      _ ≤ 2 * ‖Y j‖ := mul_le_mul_of_nonneg_right
        (norm_centeredComplexLpCLM_le_two Q) (norm_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg ‖Y j‖)), Finset.mul_sum]
  exact Finset.sum_le_sum (fun j _ => by
    simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (hnorm j) 2)

/-- Absorb the structural localization-radius multiplier in the dyadic
bounds into the local-averaging scale. All new constants still precede the
law, time and field. The logarithmic bound retains the original time. -/
theorem local_averaging_scaled
    (hlocal : node_e_u3A_local_u2D_avStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (B c A₀ a : ℝ) (hB : 1 ≤ B) (hc : 0 < c) (hA₀ : 0 < A₀) (ha : 0 ≤ a) :
    ∃ C : ℝ, ∃ M₀ : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (s m A : ℝ), 1 ≤ s → 0 ≤ m → 0 ≤ A →
      m ≤ A₀ * s ^ (-(d : ℝ) / 4) → A ≤ A₀ * (2 + s) ^ a →
    ∀ Y : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, (∫ ω, Y j ω ∂reducedLaw Q) = 0) →
      Real.sqrt (∑ j, ‖Y j‖ ^ 2) ≤ m →
      (∀ n : ℕ, 1 ≤ n → ∃ Yloc : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j, IsComplexLocalObservation Q (B * n * Real.sqrt s) (Yloc j)) ∧
        Real.sqrt (∑ j, ‖Y j - Yloc j‖ ^ 2) ≤
          A * Real.exp (-c * (n : ℝ) ^ 2)) →
      gaussianAveragingSeminorm hd Q Y ≤
        ENNReal.ofReal (C * Real.log (2 + s) ^ M₀) := by
  let A₁ := A₀ * max 1 ((B ^ 2) ^ ((d : ℝ) / 4))
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hBsq : 1 ≤ B ^ 2 := one_le_pow₀ hB
  have hA₁ : 0 < A₁ := mul_pos hA₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  have hA₀₁ : A₀ ≤ A₁ := by
    exact le_mul_of_one_le_right hA₀.le (le_max_left _ _)
  have hAfac : A₀ * (B ^ 2) ^ ((d : ℝ) / 4) ≤ A₁ :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hA₀.le
  obtain ⟨C, M₀, hC, hav⟩ := (hlocal d hd D).2 c A₁ a hc hA₁ ha
  obtain ⟨K, hK, hlog⟩ := exists_log_scaled_le B hB
  refine ⟨C ^ 2 * K ^ M₀, M₀, by positivity, ?_⟩
  intro Q s m A hs hm hA hms hAs Y hmean hnorm hloc
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsS : s ≤ B ^ 2 * s := le_mul_of_one_le_left hspos.le hBsq
  have hS : 1 ≤ B ^ 2 * s := hs.trans hsS
  have hcancel : (B ^ 2) ^ ((d : ℝ) / 4) * (B ^ 2) ^ (-(d : ℝ) / 4) = 1 := by
    rw [← Real.rpow_add (sq_pos_of_pos hBpos)]
    have hexp : (d : ℝ) / 4 + -(d : ℝ) / 4 = 0 := by ring
    rw [hexp, Real.rpow_zero]
  have hmS : m ≤ A₁ * (B ^ 2 * s) ^ (-(d : ℝ) / 4) := by
    calc
      m ≤ A₀ * s ^ (-(d : ℝ) / 4) := hms
      _ = (A₀ * (B ^ 2) ^ ((d : ℝ) / 4)) *
          (B ^ 2 * s) ^ (-(d : ℝ) / 4) := by
        rw [Real.mul_rpow (sq_nonneg B) hspos.le]
        symm
        calc
          _ = A₀ * ((B ^ 2) ^ ((d : ℝ) / 4) *
              (B ^ 2) ^ (-(d : ℝ) / 4)) * s ^ (-(d : ℝ) / 4) := by ring
          _ = _ := by rw [hcancel, mul_one]
      _ ≤ A₁ * (B ^ 2 * s) ^ (-(d : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right hAfac (Real.rpow_nonneg (by positivity) _)
  have hAS : A ≤ A₁ * (2 + B ^ 2 * s) ^ a := by
    exact hAs.trans (mul_le_mul hA₀₁
      (Real.rpow_le_rpow (by positivity) (add_le_add le_rfl hsS) ha)
      (Real.rpow_nonneg (by positivity) _) hA₁.le)
  have hlocS (n : ℕ) (hn : 1 ≤ n) := hloc n hn
  have hrad (n : ℕ) : (n : ℝ) * Real.sqrt (B ^ 2 * s) = B * n * Real.sqrt s := by
    rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hBpos.le]
    ring
  have hresult := hav Q (B ^ 2 * s) m A hS hm hA hmS hAS Y hmean hnorm (by
    intro n hn
    obtain ⟨Yloc, hYloc, herr⟩ := hlocS n hn
    refine ⟨Yloc, ?_, herr⟩
    intro j
    rw [hrad]
    exact hYloc j)
  apply hresult.2.2.2.trans
  apply ENNReal.ofReal_le_ofReal
  calc
    C ^ 2 * Real.log (2 + B ^ 2 * s) ^ M₀ ≤
        C ^ 2 * (K * Real.log (2 + s)) ^ M₀ :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀
        (Real.log_nonneg (by nlinarith only [hS])) (hlog s hs) M₀) (sq_nonneg C)
    _ = (C ^ 2 * K ^ M₀) * Real.log (2 + s) ^ M₀ := by rw [mul_pow]; ring

/-- The rescaled local-averaging estimate applies directly to uncentered
dyadic increments and their actual local approximants. Centering preserves
locality and increases both Euclidean L2 bounds by at most two. -/
theorem local_averaging_scaled_centered
    (hlocal : node_e_u3A_local_u2D_avStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (B c A₀ a : ℝ) (hB : 1 ≤ B) (hc : 0 < c) (hA₀ : 0 < A₀) (ha : 0 ≤ a) :
    ∃ C : ℝ, ∃ M₀ : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (s m A : ℝ), 1 ≤ s → 0 ≤ m → 0 ≤ A →
      m ≤ A₀ * s ^ (-(d : ℝ) / 4) → A ≤ A₀ * (2 + s) ^ a →
    ∀ Y : Fin d → Lp ℂ 2 (reducedLaw Q),
      Real.sqrt (∑ j, ‖Y j‖ ^ 2) ≤ m →
      (∀ n : ℕ, 1 ≤ n → ∃ Yloc : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j, IsComplexLocalObservation Q (B * n * Real.sqrt s) (Yloc j)) ∧
        Real.sqrt (∑ j, ‖Y j - Yloc j‖ ^ 2) ≤
          A * Real.exp (-c * (n : ℝ) ^ 2)) →
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (Y j)) ≤
        ENNReal.ofReal (C * Real.log (2 + s) ^ M₀) := by
  obtain ⟨C, M₀, hC, hav⟩ :=
    local_averaging_scaled hlocal d hd D B c (2 * A₀) a hB hc (by positivity) ha
  refine ⟨C, M₀, hC, ?_⟩
  intro Q s m A hs hm hA hms hAs Y hnorm hloc
  apply hav Q s (2 * m) (2 * A) hs (by positivity) (by positivity)
    (by nlinarith only [hms]) (by nlinarith only [hAs])
    (fun j => centeredComplexLp Q (Y j)) (fun j => integral_centeredComplexLp Q _)
  · exact (euclidean_centered_le_two Q Y).trans (mul_le_mul_of_nonneg_left hnorm (by norm_num))
  · intro n hn
    obtain ⟨Yloc, hYloc, herr⟩ := hloc n hn
    refine ⟨fun j => centeredComplexLp Q (Yloc j),
      fun j => isComplexLocalObservation_centered Q _ _ (hYloc j), ?_⟩
    have heq (j : Fin d) : centeredComplexLp Q (Y j) - centeredComplexLp Q (Yloc j) =
        centeredComplexLp Q (Y j - Yloc j) := by
      simpa only [centeredComplexLpCLM_apply] using ((centeredComplexLpCLM Q).map_sub (Y j) (Yloc j)).symm
    simp_rw [heq]
    calc
      _ ≤ 2 * Real.sqrt (∑ j : Fin d, ‖Y j - Yloc j‖ ^ 2) := euclidean_centered_le_two Q _
      _ ≤ 2 * (A * Real.exp (-c * (n : ℝ) ^ 2)) := mul_le_mul_of_nonneg_left herr (by norm_num)
      _ = (2 * A) * Real.exp (-c * (n : ℝ) ^ 2) := (mul_assoc _ _ _).symm

/-- Each actual centered time-flux increment has the logarithmic averaging
bound obtained by consuming exactly the dyadic and local-averaging Props.
The same structural constant controls the initial unit interval and every
admissible later dyadic interval, for every actual flux witness. -/
theorem finiteTimeFlux_increment_averaging
    (hdyadic : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt)
    (hlocal : node_e_u3A_local_u2D_avStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
      (‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d,
        gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F 1 ν j - F 0 ν j)) ≤
          ENNReal.ofReal (C * Real.log 3 ^ M)) ∧
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
        ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
        gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F u ν j - F s ν j)) ≤
          ENNReal.ofReal (C * Real.log (2 + (s : ℝ)) ^ M) := by
  intro d hd D
  obtain ⟨B, c, N, hB, hc, hdy⟩ := finiteTimeFlux_dyadic_bounds hdyadic d hd D
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let A₀ : ℝ := 2 * d * B
  have hA₀ : 0 < A₀ := by dsimp [A₀]; positivity
  have hBA₀ : B ≤ A₀ := by dsimp [A₀]; nlinarith only [hdreal, hBpos]
  obtain ⟨C, M, hC, hav⟩ :=
    local_averaging_scaled_centered hlocal d hd D B c A₀ N hB hc hA₀ (by positivity)
  refine ⟨C, M, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hflux
  obtain ⟨hunit, hinc⟩ := hdy Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hflux
  constructor
  · intro hζ ν
    obtain ⟨hnorm, hloc⟩ := hunit hζ ν
    have hbound : gaussianAveragingSeminorm hd Q
        (fun j => centeredComplexLp Q (F 1 ν j - F 0 ν j)) ≤
        ENNReal.ofReal (C * Real.log (2 + (1 : ℝ)) ^ M) := by
      apply hav Q 1 B B (by norm_num) hBpos.le hBpos.le
        (by simpa only [Real.one_rpow, mul_one] using hBA₀)
        (hBA₀.trans (le_mul_of_one_le_right hA₀.le
          (Real.one_le_rpow (by norm_num) (by positivity)))) _ hnorm
      intro n hn
      simpa only [Real.sqrt_one, mul_one] using hloc n hn
    norm_num only [show (2 : ℝ) + 1 = 3 by norm_num] at hbound
    exact hbound
  · intro s u hs hsu hus hζ ν
    obtain ⟨Y, B', _hYeq, _hBeq, hsum, hY, hB', hloc⟩ := hinc s u hs hsu hus hζ ν
    have hnorm : Real.sqrt (∑ j : Fin d, ‖F u ν j - F s ν j‖ ^ 2) ≤
        A₀ * (s : ℝ) ^ (-(d : ℝ) / 4) := by
      have hj (j : Fin d) : 1 * ‖F u ν j - F s ν j‖ ≤
          2 * B * (s : ℝ) ^ (-(d : ℝ) / 4) := by
        rw [one_mul, hsum j]
        exact (norm_add_le _ _).trans (by
          have hYj := (norm_le_euclidean Y j).trans hY
          have hBj := (norm_le_euclidean B' j).trans hB'
          linarith only [hYj, hBj])
      have hv := weighted_euclidean_le (fun j => F u ν j - F s ν j)
        1 (2 * B * (s : ℝ) ^ (-(d : ℝ) / 4)) zero_le_one hj
      simpa only [one_mul, A₀, mul_assoc, mul_left_comm] using hv
    apply hav Q s (A₀ * (s : ℝ) ^ (-(d : ℝ) / 4))
      (B * (2 + (s : ℝ)) ^ N) hs (by positivity) (by positivity) le_rfl
      (by rw [Real.rpow_natCast]; exact mul_le_mul_of_nonneg_right hBA₀ (by positivity))
      _ hnorm hloc

/-- An actual coefficient observation has the structural stationary L2 bound
of the coefficient multiplier applied to the constant one. -/
theorem reducedCoefficientObservation_norm_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (j i : Fin d) :
    ‖a j i‖ ≤ Real.exp (2 * Λ₀) * Λ₀ := by
  letI := reducedLaw_probability Q
  have heq : a j i = complexCoefficientMul Q j i (Lp.const 2 (reducedLaw Q) 1) := by
    apply Lp.ext
    filter_upwards [ha j i, complexCoefficientMul_coe Q j i
      (Lp.const 2 (reducedLaw Q) 1), Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)]
      with ω haω hm hc
    simpa only [haω, hc, Function.const_apply, mul_one] using hm.symm
  rw [heq]
  calc
    _ ≤ ‖complexCoefficientMul Q j i‖ * ‖Lp.const 2 (reducedLaw Q) (1 : ℂ)‖ :=
      (complexCoefficientMul Q j i).le_opNorm _
    _ ≤ (Real.exp (2 * Λ₀) * Λ₀) * 1 :=
      mul_le_mul (norm_complexCoefficientMul_le Q j i)
        (by simpa using Lp.norm_const_le (2 : ℝ≥0∞) (reducedLaw Q) (1 : ℂ))
        (norm_nonneg _)
        (mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter))
    _ = _ := mul_one _

/-- The literal origin entry is measurable in the joint fields on the unit
Euclidean ball, so every actual coefficient observation is local there. -/
theorem reducedCoefficientObservation_local {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (j i : Fin d) :
    IsComplexLocalObservation Q 1 (a j i) := by
  have h0 : (0 : Vec d) ∈ {x : Vec d | euclideanNorm x < 1} := by
    simp only [Set.mem_setOf_eq, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
      zero_mul, Finset.sum_const_zero, Real.sqrt_zero]
    norm_num
  have heval : Measurable[localSigma {x : Vec d | euclideanNorm x < 1}]
      (fun ω : FieldPair d => (ω.1 0, ω.2 0)) := by
    rw [measurable_iff_comap_le]
    exact le_iSup (fun y : {x : Vec d | euclideanNorm x < 1} => MeasurableSpace.comap
      (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance) ⟨0, h0⟩
  have hentry : Measurable (fun p : Mat d × ℝ => (p.1 j i : ℂ)) :=
    Complex.measurable_ofReal.comp (continuous_fst.matrix_elem j i).measurable
  exact ⟨fun ω => (ω.1 0 j i : ℂ), hentry.comp heval, (ha j i).symm⟩

/-- The local-averaging dependency bounds the centered initial coefficient
column by one structural constant chosen before the actual law and column. -/
theorem coefficientColumn_averaging
    (hlocal : node_e_u3A_local_u2D_avStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → ∀ i : Fin d,
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (a j i)) ≤
        ENNReal.ofReal C := by
  intro d hd D
  obtain ⟨C, hC, hav⟩ := (hlocal d hd D).1
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  refine ⟨C * (2 * d * K), by positivity, ?_⟩
  intro Q a ha i
  have hnorm : Real.sqrt (∑ j : Fin d, ‖a j i‖ ^ 2) ≤ d * K := by
    simpa only [one_mul] using weighted_euclidean_le (fun j => a j i) 1 K
      zero_le_one (fun j => by simpa only [one_mul] using reducedCoefficientObservation_norm_le Q a ha j i)
  have hav' := hav Q 1 le_rfl (fun j => centeredComplexLp Q (a j i))
    (fun j => integral_centeredComplexLp Q _) (fun j =>
      isComplexLocalObservation_centered Q 1 _ (reducedCoefficientObservation_local Q a ha j i))
  apply hav'.trans
  apply ENNReal.ofReal_le_ofReal
  simp only [Real.one_rpow, mul_one]
  exact mul_le_mul_of_nonneg_left
    ((euclidean_centered_le_two Q (fun j => a j i)).trans
      (by nlinarith only [hnorm])) hC.le

/-- Backward halving bounds a normed orbit using only intervals whose doubled
lower endpoint stays below the final horizon. -/
theorem norm_le_dyadic_count {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (T B : ℝ) (hT : 2 ≤ T) (hB : 0 ≤ B)
    (hinc : ∀ s u : ℝ, 1 ≤ s → s ≤ u → u ≤ 2 * s → 2 * s ≤ T →
      ‖f u - f s‖ ≤ B) :
    ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ T → u ≤ (2 : ℝ) ^ (n + 1) →
      ‖f u‖ ≤ ‖f 1‖ + (n + 1 : ℕ) * B := by
  have hnorm (s u : ℝ) (hs : 1 ≤ s) (hsu : s ≤ u) (hus : u ≤ 2 * s)
      (hst : 2 * s ≤ T) : ‖f u‖ ≤ ‖f s‖ + B := by
    calc
      _ = ‖f s + (f u - f s)‖ := by congr 1; abel
      _ ≤ ‖f s‖ + ‖f u - f s‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (hinc s u hs hsu hus hst)
  intro n
  induction n with
  | zero =>
    intro u hu huT hu2
    simpa using hnorm 1 u le_rfl hu (by simpa using hu2) (by simpa using hT)
  | succ n ih =>
    intro u hu huT hun
    by_cases hu2 : u ≤ 2
    · have hv := hnorm 1 u le_rfl hu (by simpa using hu2) (by simpa using hT)
      have hn : (1 : ℝ) ≤ (n + 1 + 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ n + 1 + 1)
      calc
        _ ≤ ‖f 1‖ + B := hv
        _ ≤ _ := by push_cast; nlinarith only [hB, hn]
    · have hs : 1 ≤ u / 2 := by linarith only [hu2]
      have hsT : u / 2 ≤ T := by linarith only [huT, hu]
      have hsn : u / 2 ≤ (2 : ℝ) ^ (n + 1) := by
        rw [pow_succ] at hun
        linarith only [hun]
      have hv := hnorm (u / 2) u hs (by linarith only [hu]) (by linarith) (by linarith only [huT])
      have hw := ih (u / 2) hs hsT hsn
      push_cast at *
      linarith only [hv, hw]

/-- The number of halving intervals is logarithmic in the horizon. -/
theorem exists_dyadic_count_log (T : ℝ) (hT : 2 ≤ T) :
    ∃ n : ℕ, T ≤ (2 : ℝ) ^ (n + 1) ∧
      (n + 3 : ℕ) ≤ (1 / Real.log 2 + 3 / Real.log 4) * Real.log (2 + T) := by
  obtain ⟨n, hn, hTn⟩ := exists_nat_pow_near (by linarith only [hT] : 1 ≤ T)
    (by norm_num : (1 : ℝ) < 2)
  refine ⟨n, hTn.le, ?_⟩
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlog : (n : ℝ) * Real.log 2 ≤ Real.log (2 + T) := by
    calc
      _ = Real.log ((2 : ℝ) ^ n) := (Real.log_pow _ _).symm
      _ ≤ Real.log T := Real.log_le_log (by positivity) hn
      _ ≤ _ := Real.log_le_log (by linarith only [hT]) (by linarith)
  have hnlog : (n : ℝ) ≤ Real.log (2 + T) / Real.log 2 :=
    (le_div_iff₀ hl2).mpr hlog
  have hlower : Real.log 4 ≤ Real.log (2 + T) :=
    Real.log_le_log (by norm_num) (by linarith only [hT])
  have h3 : (3 : ℝ) ≤ (3 / Real.log 4) * Real.log (2 + T) := by
    calc
      _ = (3 / Real.log 4) * Real.log 4 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlower (by positivity)
  push_cast
  simp only [div_eq_mul_inv] at hnlog h3 ⊢
  nlinarith only [hnlog, h3]

/-- A common bound for the initial field, unit increment and all admissible
later increments sums to a logarithmic averaging bound at the horizon. -/
theorem gaussianAveragingSeminorm_dyadic {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (F : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 2 ≤ (t : ℝ))
    (B : ℝ) (hB : 0 ≤ B)
    (hzero : gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F 0 j)) ≤
      ENNReal.ofReal B)
    (hunit : gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F 1 j - F 0 j)) ≤
      ENNReal.ofReal B)
    (hinc : ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s → 2 * (s : ℝ) ≤ t →
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F u j - F s j)) ≤
        ENNReal.ofReal B) :
    gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F t j)) ≤
      ENNReal.ofReal (d * (1 / Real.log 2 + 3 / Real.log 4) * Real.log (2 + t) * B) := by
  let K := 1 / Real.log 2 + 3 / Real.log 4
  have hK : 0 < K := by dsimp [K]; positivity
  have hlogt : 0 < Real.log (2 + (t : ℝ)) := Real.log_pos (by linarith only [ht])
  obtain ⟨n, htn, hnlog⟩ := exists_dyadic_count_log t ht
  apply (gaussianAveragingSeminorm_le_iff hd Q _ _ (by
    change 0 ≤ d * K * Real.log (2 + (t : ℝ)) * B
    positivity)).mpr
  intro ρ hρ
  let w := ρ ^ ((d : ℝ) / 2)
  have hw : 0 < w := Real.rpow_pos_of_pos (by linarith only [hρ]) _
  let A := fun (u : ℝ≥0) (j : Fin d) =>
    ∫ x : Vec d, (Correctors.euclideanHeatKernel (ρ ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (centeredComplexLp Q (F u j))
  have hincr (s u : ℝ≥0) (h : gaussianAveragingSeminorm hd Q
      (fun j => centeredComplexLp Q (F u j - F s j)) ≤ ENNReal.ofReal B)
      (j : Fin d) : w * ‖A u j - A s j‖ ≤ B := by
    have hb := (gaussianAveragingSeminorm_le_iff hd Q _ B hB).mp h ρ hρ
    have heq (j : Fin d) := centered_isotropicAverage_sub Q ρ hρ (F u j) (F s j)
    simp_rw [heq] at hb
    exact (mul_le_mul_of_nonneg_left (norm_le_euclidean (fun j => A u j - A s j) j) hw.le).trans hb
  have hzeroj (j : Fin d) : w * ‖A 0 j‖ ≤ B := by
    have hb := (gaussianAveragingSeminorm_le_iff hd Q _ B hB).mp hzero ρ hρ
    exact (mul_le_mul_of_nonneg_left (norm_le_euclidean (A 0) j) hw.le).trans hb
  suffices h : w * Real.sqrt (∑ j : Fin d, ‖A t j‖ ^ 2) ≤
      d * (K * Real.log (2 + (t : ℝ)) * B) by
    simpa only [mul_assoc, K, A, w] using h
  apply weighted_euclidean_le (A t) w (K * Real.log (2 + t) * B) hw.le
  intro j
  let f : ℝ → Lp ℂ 2 (reducedLaw Q) := fun u => w • A u.toNNReal j
  have hfnorm (u : ℝ) : ‖f u‖ = w * ‖A u.toNNReal j‖ := by
    simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos hw]
  have hfone : ‖f 1‖ ≤ 2 * B := by
    have hdiff : ‖f 1 - f 0‖ ≤ B := by
      simpa only [f, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hw,
        Real.toNNReal_one, Real.toNNReal_zero] using hincr 0 1 hunit j
    have hfzero : ‖f 0‖ ≤ B := by simpa only [hfnorm, Real.toNNReal_zero] using hzeroj j
    have heq : f 1 = f 0 + (f 1 - f 0) := by abel
    rw [heq]
    exact (norm_add_le _ _).trans (by linarith only [hfzero, hdiff])
  have hstep (s u : ℝ) (hs : 1 ≤ s) (hsu : s ≤ u) (hus : u ≤ 2 * s)
      (hst : 2 * s ≤ t) : ‖f u - f s‖ ≤ B := by
    have hs0 : 0 ≤ s := by linarith only [hs]
    have hu0 : 0 ≤ u := hs0.trans hsu
    have h := hincr s.toNNReal u.toNNReal
      (hinc s.toNNReal u.toNNReal (by simpa only [Real.coe_toNNReal _ hs0] using hs)
        (Real.toNNReal_le_toNNReal hsu)
        (by exact_mod_cast (by simpa only [Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ hu0] using hus :
          (u.toNNReal : ℝ) ≤ 2 * (s.toNNReal : ℝ)))
        (by simpa only [Real.coe_toNNReal _ hs0] using hst)) j
    simpa only [f, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hw] using h
  have hf := norm_le_dyadic_count f t B ht hB hstep n t (by linarith only [ht]) le_rfl htn
  have hfinal : ‖f t‖ ≤ K * Real.log (2 + t) * B := by
    calc
      _ ≤ 2 * B + (n + 1 : ℕ) * B := hf.trans (add_le_add hfone le_rfl)
      _ = (n + 3 : ℕ) * B := by push_cast; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hnlog hB
  simpa only [hfnorm, Real.toNNReal_coe] using hfinal

/-- Summing the actual initial column and dyadic increments gives the outer
force-disc estimate, uniformly for every actual finite-time flux witness. -/
theorem finiteTimeFlux_outer_averaging
    (hdyadic : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt)
    (hlocal : node_e_u3A_local_u2D_avStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ M : ℕ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
      IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
    ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ∀ ν : FluxIndex d,
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F t ν j)) ≤
        ENNReal.ofReal (C * Real.log (2 + (t : ℝ)) ^ M) := by
  intro d hd D
  obtain ⟨C₀, hC₀, hzero⟩ := coefficientColumn_averaging hlocal d hd D
  obtain ⟨C₁, M, hC₁, hinc⟩ := finiteTimeFlux_increment_averaging hdyadic hlocal d hd D
  let K := 1 / Real.log 2 + 3 / Real.log 4
  let A := C₀ / Real.log 3 ^ M + C₁
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hA : 0 < A := by dsimp [A]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  refine ⟨d * K * A, M + 1, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hflux t ht hζ ν
  obtain ⟨hunit, hdy⟩ := hinc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hflux
  have hlower : Real.log 3 ≤ Real.log (2 + (t : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith only [ht])
  have hlogt : 0 < Real.log (2 + (t : ℝ)) := hlog3.trans_le hlower
  have hpow : Real.log 3 ^ M ≤ Real.log (2 + (t : ℝ)) ^ M :=
    pow_le_pow_left₀ hlog3.le hlower M
  have hC₀A : C₀ ≤ A * Real.log (2 + (t : ℝ)) ^ M := by
    calc
      _ = (C₀ / Real.log 3 ^ M) * Real.log 3 ^ M := by field_simp
      _ ≤ (C₀ / Real.log 3 ^ M) * Real.log (2 + (t : ℝ)) ^ M :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [A]; linarith only [hC₁]) (by positivity)
  have hC₁A : C₁ ≤ A := by
    dsimp [A]
    exact le_add_of_nonneg_left (by positivity)
  have hB : 0 ≤ A * Real.log (2 + (t : ℝ)) ^ M := by positivity
  have hbound := gaussianAveragingSeminorm_dyadic hd Q (fun u j => F u ν j) t ht
    (A * Real.log (2 + (t : ℝ)) ^ M) hB
  have hzero' : gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F 0 ν j)) ≤
      ENNReal.ofReal (A * Real.log (2 + (t : ℝ)) ^ M) := by
    simp_rw [finiteTimeFlux_zero hd Q ζ P Pdag β a μ hflux]
    exact (hzero Q a ha _).trans (ENNReal.ofReal_le_ofReal hC₀A)
  have hζunit : ‖ζ‖ ≤ 2 := by
    have hsqrt : 1 ≤ Real.sqrt (t : ℝ) := Real.one_le_sqrt.mpr (by linarith only [ht])
    nlinarith only [hζ, hsqrt, norm_nonneg ζ]
  have hunit' := (hunit hζunit ν).trans (ENNReal.ofReal_le_ofReal
    ((mul_le_mul_of_nonneg_left hpow hC₁.le).trans
      (mul_le_mul_of_nonneg_right hC₁A (by positivity))))
  have hdy' (s u : ℝ≥0) (hs : 1 ≤ (s : ℝ)) (hsu : s ≤ u) (hus : u ≤ 2 * s)
      (hst : 2 * (s : ℝ) ≤ t) :
      gaussianAveragingSeminorm hd Q (fun j => centeredComplexLp Q (F u ν j - F s ν j)) ≤
        ENNReal.ofReal (A * Real.log (2 + (t : ℝ)) ^ M) := by
    have hζs : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 :=
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hst) (norm_nonneg ζ)).trans hζ
    have hsT : (s : ℝ) ≤ t := by linarith only [hs, hst]
    have hl : Real.log (2 + (s : ℝ)) ≤ Real.log (2 + (t : ℝ)) :=
      Real.log_le_log (by linarith only [hs]) (by linarith only [hsT])
    exact (hdy s u hs hsu hus hζs ν).trans (ENNReal.ofReal_le_ofReal
      ((mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (Real.log_nonneg (by linarith only [hs])) hl M) hC₁.le).trans
        (mul_le_mul_of_nonneg_right hC₁A (by positivity))))
  have hfinal := hbound hzero' hunit' hdy'
  convert hfinal using 1
  congr 1
  dsimp only [K]
  rw [pow_succ]
  ring

/-- The exact Cauchy graph reduction: local averaging and actual dyadic
increments give the outer bound; holomorphy gives both inner estimates. -/
theorem node_p_u3A_late_u23_cauchy_of_deps
    (hdyadic : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt)
    (hlocal : node_e_u3A_local_u2D_avStmt)
    (hanalytic : node_stationary_u2D_analytic_u2D_semigroup_u23_fluxStmt) :
    node_p_u3A_late_u23_cauchyStmt := by
  intro d hd D
  obtain ⟨C, M, hC, houter⟩ := finiteTimeFlux_outer_averaging hdyadic hlocal d hd D
  obtain ⟨C', N, _hC', han⟩ := hanalytic d hd D
  have hdreal : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  refine ⟨d * C, M, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPdag
  obtain ⟨G, F, hflux, _hholF, hholA, _hpoly⟩ := han Q hQ β a μ hβ ha hμ P Pdag hP hPdag
  refine ⟨G, F, hflux, ?_⟩
  dsimp only
  have hout (t : ℝ≥0) (ht : 2 ≤ (t : ℝ)) (ν : FluxIndex d) (ζ : ℂ)
      (hζ : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2) :=
    houter Q hQ β a μ hβ ha hμ ζ (P ζ) (Pdag ζ) (hP ζ) (hPdag ζ)
      (G ζ) (F ζ) (hflux ζ) t ht hζ ν
  have hcauchy (t : ℝ≥0) (ht : 2 ≤ (t : ℝ)) (ν : FluxIndex d) :=
    centered_isotropicAverage_cauchy_bounds hd Q (fun ζ j => F ζ t ν j)
      t (C * Real.log (2 + (t : ℝ)) ^ M) (by linarith only [ht])
      (mul_nonneg hC.le (pow_nonneg (Real.log_nonneg (by linarith only [ht])) _))
      (hout t ht ν) (fun ρ hρ j => (hholA t (by linarith only [ht]) ν ρ hρ j).1)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht ν ζ hζ
    exact (hout t ht ν ζ hζ).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hC.le hdreal)
        (pow_nonneg (Real.log_nonneg (by linarith only [ht])) _)))
  · intro t ht ν ρ hρ ζ hζ
    obtain ⟨hdiff, hderiv⟩ := (hcauchy t ht ν).1 ρ hρ ζ hζ
    refine ⟨hdiff, ?_⟩
    convert hderiv using 1
    ring
  · intro t ht ν ζ hζ
    have hdiff := (hcauchy t ht ν).2 ζ hζ
    convert hdiff using 1
    congr 1
    ring

end EinsteinFull.Blueprint
