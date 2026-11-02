import EinsteinFull.Blueprint.G3.node_l_u3A_late_u2D_propagation_u23_unsmoothing
import EinsteinFull.Blueprint.G3.node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamel
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeBoundSupport
import EinsteinFull.Work.W4.HomogeneousAllDataHorizontalSmoothingSupport
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
Intermediate unsmoothing tools for `paper/main.tex:1148–1158`.
The endpoint estimates below consume the actual Hölder and scalar graph
contracts. Real propagation forces reduce to the unforced Gaussian by actual
stationary translations. Their terminal-time Hessian and homogeneous unsmoothing
bounds are proved below using the literal mesoscopic endpoint. Complex-force
kernel splitting supplies the Hessian and homogeneous unsmoothing bounds.
The exact three-premise graph reduction is assembled at the end.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.LateUnsmoothing
open EinsteinRelation

/-- The source smoothing exponent can be chosen before the law and force. -/
theorem exists_smoothing_exponent {ε δ h L : ℝ}
    (hε : 0 < ε) (hδ : δ < 1 / 2) (hhL : 0 < h + L) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ b < ε * (1 - δ) / (2 * (h + L)) := by
  have hx : 0 < ε * (1 - δ) / (2 * (h + L)) :=
    div_pos (mul_pos hε (by linarith)) (by positivity)
  obtain ⟨b, hb, hb'⟩ := exists_between (lt_min zero_lt_one hx)
  exact ⟨b, hb, (lt_min_iff.mp hb').1, (lt_min_iff.mp hb').2⟩

/-- The fraction of the endpoint time represented by the smoothing time. -/
theorem smoothing_ratio {T b : ℝ} (hT : 0 < T) :
    T ^ (1 - b) / T = T ^ (-b) := by
  conv_lhs => rhs; rw [← Real.rpow_one T]
  rw [← Real.rpow_sub hT]
  congr 1
  ring

/-- The Hölder gain at the actual mesoscopic scale has the source exponent. -/
theorem smoothing_gain {T b α : ℝ} (hT : 0 < T) :
    (T ^ (1 - b) / T) ^ (α / 2) = T ^ (-(b * α / 2)) := by
  rw [smoothing_ratio hT, ← Real.rpow_mul hT.le]
  congr 1
  ring

/-- Every indexed endpoint is one of the literal scalar endpoints. -/
theorem indexedEndpoint_mem {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) :
    indexedEndpoint hd Q ν ζ P Pdag β a μ t ∈
      endpointCollection Q ⟨0, by omega⟩ ζ P Pdag β a μ t := by
  rcases ν with j | b
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨j, rfl⟩)
  · cases b
    · exact Set.mem_union_right _ rfl
    · exact Set.mem_union_left _ (Set.mem_union_left _ rfl)

/-- Specialize the Hölder contract to the actual reduced L2 norm. Constants
are still chosen before the law, endpoints, complex force and times. -/
theorem endpoint_unsmoothing_of_holder
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C Cp : ℝ, 0 < α ∧ 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
    ∀ q : ℝ, 0 < q → q ≤ 1 / 16 → ∀ hqt : 0 < q * (t : ℝ),
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - gaussianAverage hd Q
        (q * (t : ℝ)) hqt (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
        C * q ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)‖ := by
  obtain ⟨α, hα, hh⟩ := hholder d hd D
  obtain ⟨C, Cp, hC, hCp, hh⟩ := hh 2 le_rfl
  refine ⟨α, C, Cp, hα, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht q hq hq' hqt
  have h := ((hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht).2
    q hq hq' hqt).2
  simp only [ENNReal.ofReal_ofNat, ← Lp.norm_def] at h
  rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  exact h

/-- At the manuscript scale `s=t^(1-b)`, the Hölder contract gives the
literal source gain `t^(-b*α/2)`. The small-ratio condition will be enforced
by the final structural lower time threshold. -/
theorem endpoint_mesoscopic_unsmoothing
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C Cp : ℝ, 0 < α ∧ 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (b : ℝ), (t : ℝ) ^ (-b) ≤ 1 / 16 →
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - gaussianAverage hd Q
        ((t : ℝ) ^ (1 - b)) (Real.rpow_pos_of_pos ht _)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
        C * (t : ℝ) ^ (-(b * α / 2)) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          ‖indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)‖ := by
  obtain ⟨α, C, Cp, hα, hC, hCp, hh⟩ := endpoint_unsmoothing_of_holder hholder d hd D
  refine ⟨α, C, Cp, hα, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht b hsmall
  have hq : 0 < (t : ℝ) ^ (1 - b) / (t : ℝ) :=
    div_pos (Real.rpow_pos_of_pos ht _) ht
  have hqt : (t : ℝ) ^ (1 - b) / (t : ℝ) * (t : ℝ) = (t : ℝ) ^ (1 - b) :=
    div_mul_cancel₀ _ ht.ne'
  have hqtpos : 0 < (t : ℝ) ^ (1 - b) / (t : ℝ) * (t : ℝ) := mul_pos hq ht
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht
    ((t : ℝ) ^ (1 - b) / (t : ℝ)) hq
    (by rwa [smoothing_ratio ht]) hqtpos
  simpa only [hqt, smoothing_gain ht] using! h

/-- The scalar contract bounds every indexed endpoint in the wide force
window, using the actual endpoint collection rather than a substitute family. -/
theorem endpoint_decay_of_scalar (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ η C Cp t₀ : ℝ, 0 < η ∧ 0 < C ∧ 0 < Cp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η →
    ∀ ν : EndpointIndex d,
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤
        C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          ((t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨a₀, η, _, _, hη, hh⟩ := hscalar d hd D
  obtain ⟨C, Cp, t₀, Cder, hC, hCp, ht₀, _, hh⟩ := hh 2 le_rfl
  refine ⟨η, C, Cp, t₀, hη, hC, hCp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν
  have h := ((hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).2
    t ht hζ hwindow (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (indexedEndpoint_mem hd Q ν ζ P Pdag β a μ t)).1.2
  simpa only [ENNReal.ofReal_ofNat, ← Lp.norm_def] using! h

/-- Consume both graph contracts at the literal eighth-time endpoint. This
is the actual unsmoothing estimate before absorbing scaled-force polynomials
and rescaling the eighth-time powers. The stated force restrictions are the
standing scalar window at that eighth time, not an assumed endpoint estimate. -/
theorem endpoint_unsmoothing_decay
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α η A Ap B Bp t₀ : ℝ,
      0 < α ∧ 0 < η ∧ 1 ≤ A ∧ 0 < Ap ∧ 0 < B ∧ 0 < Bp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (b : ℝ), (t : ℝ) ^ (-b) ≤ 1 / 16 →
      t₀ ≤ ((t / 8 : ℝ≥0) : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (((t / 8 : ℝ≥0) : ℝ)) ≤ (((t / 8 : ℝ≥0) : ℝ)) ^ η →
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t - gaussianAverage hd Q
        ((t : ℝ) ^ (1 - b)) (Real.rpow_pos_of_pos ht _)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
        (A * (t : ℝ) ^ (-(b * α / 2)) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ A *
          Real.exp (Ap * ‖ζ‖ ^ 2 * (t : ℝ))) *
        (B * Real.exp (Bp * ‖ζ‖ ^ 2 * (((t / 8 : ℝ≥0) : ℝ))) *
          (((((t / 8 : ℝ≥0) : ℝ))) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (((t / 8 : ℝ≥0) : ℝ)) ^ (-(d : ℝ) / 4))) := by
  obtain ⟨α, A, Ap, hα, hA, hAp, hh⟩ := endpoint_mesoscopic_unsmoothing hholder d hd D
  obtain ⟨η, B, Bp, t₀, hη, hB, hBp, ht₀, hs⟩ := endpoint_decay_of_scalar hscalar d hd D
  refine ⟨α, η, A, Ap, B, Bp, t₀, hα, hη, hA, hAp, hB, hBp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht b hsmall htime hζ hwindow
  apply (hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht b hsmall).trans
  apply mul_le_mul_of_nonneg_left
    (hs Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag (t / 8) htime hζ hwindow ν)
  exact mul_nonneg (mul_nonneg
    (mul_nonneg (zero_le_one.trans hA) (Real.rpow_nonneg ht.le _))
    (Real.rpow_nonneg (by positivity) _)) (Real.exp_pos _).le

/-- All positive smoothing exponents eventually satisfy the Hölder scale
restriction, with a lower threshold chosen independently of the law. -/
theorem exists_smoothing_threshold {b : ℝ} (hb : 0 < b) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → T ^ (-b) ≤ 1 / 16 := by
  have hevent : ∀ᶠ T : ℝ in Filter.atTop, T ^ (-b) < 1 / 16 :=
    (tendsto_rpow_neg_atTop hb).eventually (gt_mem_nhds (by norm_num))
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨max 2 t, le_max_left _ _, fun T hT =>
    (ht T ((le_max_right _ _).trans hT)).le⟩

/-- Polynomial scaled-force factors can be absorbed into the same quadratic
exponential as in the manuscript, with explicit constants. -/
theorem scaled_force_polynomial_le {x A : ℝ} (hx : 0 ≤ x) (hA : 0 ≤ A) :
    (1 + x) ^ A ≤ (2 : ℝ) ^ A * Real.exp (A * x ^ 2) := by
  have hbase : 1 + x ≤ 2 * Real.exp (x ^ 2) := by
    have he := Real.add_one_le_exp (x ^ 2)
    nlinarith only [he, sq_nonneg (x - 1 / 2)]
  calc
    _ ≤ (2 * Real.exp (x ^ 2)) ^ A :=
      Real.rpow_le_rpow (by positivity) hbase hA
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le,
        ← Real.exp_mul, mul_comm (x ^ 2) A]

/-- The literal Gaussian average distributes over subtraction. Integrability
comes from the proved anisotropic homogeneous kernel calculus. -/
theorem gaussianAverage_sub {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (U V : Lp ℂ 2 (reducedLaw Q)) :
    gaussianAverage hd Q s hs (U - V) =
      gaussianAverage hd Q s hs U - gaussianAverage hd Q s hs V := by
  simp only [gaussianAverage, map_sub, smul_sub]
  exact integral_sub
    (integrable_homogeneousAverage_integrand Q ⟨0, by omega⟩ s hs 0 U)
    (integrable_homogeneousAverage_integrand Q ⟨0, by omega⟩ s hs 0 V)

/-- The three manuscript errors bound the comparison in the actual L2 space. -/
theorem comparison_le_three_errors {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (U V : Lp ℂ 2 (reducedLaw Q)) :
    ‖U - V‖ ≤ ‖U - gaussianAverage hd Q s hs U‖ +
      ‖gaussianAverage hd Q s hs (U - V)‖ + ‖V - gaussianAverage hd Q s hs V‖ := by
  have heq : U - V = (U - gaussianAverage hd Q s hs U) +
      gaussianAverage hd Q s hs (U - V) - (V - gaussianAverage hd Q s hs V) := by
    rw [gaussianAverage_sub]
    abel
  calc
    _ = ‖(U - gaussianAverage hd Q s hs U) +
        gaussianAverage hd Q s hs (U - V) - (V - gaussianAverage hd Q s hs V)‖ :=
      congrArg norm heq
    _ ≤ _ := (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)

/-- Weakening each of the three error exponents keeps every smaller gain. -/
theorem sum_errors_le {T h ρ g₁ g₂ g₃ C₁ C₂ C₃ X : ℝ}
    (hT : 1 ≤ T) (hX : 0 ≤ X)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hC₃ : 0 ≤ C₃)
    (h₁ : ρ ≤ g₁) (h₂ : ρ ≤ g₂) (h₃ : ρ ≤ g₃) :
    C₁ * X * T ^ (-h - g₁) + C₂ * X * T ^ (-h - g₂) +
      C₃ * X * T ^ (-h - g₃) ≤ (C₁ + C₂ + C₃) * X * T ^ (-h - ρ) := by
  have hp (g : ℝ) (hg : ρ ≤ g) : T ^ (-h - g) ≤ T ^ (-h - ρ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith only [hg])
  calc
    _ ≤ C₁ * X * T ^ (-h - ρ) + C₂ * X * T ^ (-h - ρ) +
        C₃ * X * T ^ (-h - ρ) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left (hp g₁ h₁) (mul_nonneg hC₁ hX))
        (mul_le_mul_of_nonneg_left (hp g₂ h₂) (mul_nonneg hC₂ hX)))
        (mul_le_mul_of_nonneg_left (hp g₃ h₃) (mul_nonneg hC₃ hX))
    _ = _ := by ring

/-- Normalize the scalar bound at the eighth time to the terminal time. -/
theorem eighth_time_decay_le {T z k : ℝ} (hT : 0 < T) (hz : 0 ≤ z) :
    (T / 8) ^ (-(1 / 2 + k)) + z * (T / 8) ^ (-k) ≤
      ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k) *
        (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k)) := by
  have hscale (r : ℝ) : (T / 8) ^ (-r) = (8 : ℝ) ^ r * T ^ (-r) := by
    rw [Real.div_rpow hT.le (by norm_num : (0 : ℝ) ≤ 8),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8), div_inv_eq_mul, mul_comm]
  have hpower : T ^ (-k) = Real.sqrt T * T ^ (-(1 / 2 + k)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hT]
    congr 1
    ring
  rw [hscale, hscale, hpower]
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) (1 / 2 + k)
  have hq := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) k
  have ht := Real.rpow_pos_of_pos hT (-(1 / 2 + k))
  have hx : 0 ≤ z * Real.sqrt T := mul_nonneg hz (Real.sqrt_nonneg _)
  nlinarith only [mul_nonneg (mul_nonneg hp.le hx) ht.le, mul_nonneg hq.le ht.le]

/-- The explicit Hölder/scalar product has the exact terminal-time gain.
The absorbing constant is independent of time, force and smoothing gain. -/
theorem exists_endpoint_absorption_constant {A Ap B Bp k : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hBp : 0 < Bp) :
    ∃ C : ℝ, 0 < C ∧ ∀ (T z g : ℝ), 0 < T → 0 ≤ z →
      (A * T ^ (-g) * (1 + z * Real.sqrt T) ^ A * Real.exp (Ap * z ^ 2 * T)) *
        (B * Real.exp (Bp * z ^ 2 * (T / 8)) *
          ((T / 8) ^ (-(1 / 2 + k)) + z * (T / 8) ^ (-k))) ≤
      C * Real.exp (C * z ^ 2 * T) * T ^ (-(1 / 2 + k) - g) := by
  let D := (8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k
  let K := A * B * D * (2 : ℝ) ^ (A + 1)
  let R := A + 1 + Ap + Bp
  have hD : 0 < D := by dsimp [D]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  let C := max K R
  have hC : 0 < C := hK.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T z g hT hz
  have hx : 0 < 1 + z * Real.sqrt T := by positivity
  have hy : 0 ≤ z ^ 2 * T := mul_nonneg (sq_nonneg _) hT.le
  have hpoly := scaled_force_polynomial_le (mul_nonneg hz (Real.sqrt_nonneg T))
    (show 0 ≤ A + 1 by linarith)
  have hexp : Real.exp (Ap * z ^ 2 * T) * Real.exp (Bp * z ^ 2 * (T / 8)) ≤
      Real.exp ((Ap + Bp) * (z ^ 2 * T)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg hBp.le hy]
  have hpower : T ^ (-g) * T ^ (-(1 / 2 + k)) = T ^ (-(1 / 2 + k) - g) := by
    rw [← Real.rpow_add hT]
    congr 1
    ring
  calc
    _ ≤ (A * T ^ (-g) * (1 + z * Real.sqrt T) ^ A * Real.exp (Ap * z ^ 2 * T)) *
        (B * Real.exp (Bp * z ^ 2 * (T / 8)) *
          (D * (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k)))) := by
      apply mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (eighth_time_decay_le hT hz) (by positivity))
      positivity
    _ = A * B * D * (1 + z * Real.sqrt T) ^ (A + 1) *
        (Real.exp (Ap * z ^ 2 * T) * Real.exp (Bp * z ^ 2 * (T / 8))) *
          T ^ (-(1 / 2 + k) - g) := by
      rw [Real.rpow_add hx, Real.rpow_one, ← hpower]
      ring
    _ ≤ A * B * D * ((2 : ℝ) ^ (A + 1) *
        Real.exp ((A + 1) * (z * Real.sqrt T) ^ 2)) *
          Real.exp ((Ap + Bp) * (z ^ 2 * T)) * T ^ (-(1 / 2 + k) - g) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpoly (by positivity)) hexp
        (by positivity) (by positivity)
    _ = K * Real.exp (R * z ^ 2 * T) * T ^ (-(1 / 2 + k) - g) := by
      have hsq : (z * Real.sqrt T) ^ 2 = z ^ 2 * T := by
        rw [mul_pow, Real.sq_sqrt hT.le]
      rw [hsq]
      dsimp [K, R]
      rw [show (A + 1 + Ap + Bp) * z ^ 2 * T =
        (A + 1) * (z ^ 2 * T) + (Ap + Bp) * (z ^ 2 * T) by ring, Real.exp_add]
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul (le_max_left K R) _ (Real.exp_pos _).le hC.le
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_right (le_max_right K R) hy

/-- Both force windows are eventually below every positive power, with an
arbitrary positive structural prefactor. -/
theorem eventually_force_window_le_rpow {η K : ℝ} (hη : 0 < η) (hK : 0 < K)
    (C₀ : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ x : ℝ,
      (x ≤ 2 ∨ x ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) → x ≤ K * T ^ η := by
  have hlog := ((isLittleO_log_rpow_rpow_atTop (1 / 4 : ℝ) hη).const_mul_left
    C₀).bound hK
  have hconst := (tendsto_rpow_atTop hη).eventually_ge_atTop (2 / K)
  filter_upwards [hlog, hconst, Filter.eventually_ge_atTop (0 : ℝ)] with T hlog hc hT
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hT _)] at hlog
  intro x hx
  rcases hx with hx | hx
  · exact hx.trans (by simpa only [mul_comm] using! (div_le_iff₀ hK).mp hc)
  · exact hx.trans ((le_abs_self _).trans hlog)

/-- A single structural lower time threshold makes either source force
window admissible for the scalar estimate at the actual eighth time. -/
theorem exists_scalar_window_threshold {η : ℝ} (hη : 0 < η) (C₀ t₀ : ℝ) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
      t₀ ≤ T / 8 ∧ ‖ζ‖ ≤ 1 ∧ ‖ζ‖ * Real.sqrt (T / 8) ≤ (T / 8) ^ η := by
  have heighth := eventually_force_window_le_rpow hη
    (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 8) η)) C₀
  have hsqrt := eventually_force_window_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
    zero_lt_one C₀
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (heighth.and hsqrt)
  refine ⟨max 2 (max (8 * t₀) R), le_max_left _ _, ?_⟩
  intro T hT ζ hζ
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have htime : 8 * t₀ ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT)
  have hTR : R ≤ T := (le_max_right _ _).trans ((le_max_right _ _).trans hT)
  have hx : ‖ζ‖ * Real.sqrt T ≤ 2 ∨
      ‖ζ‖ * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ) := by
    rcases hζ with hζ | ⟨lam, rfl, hlam⟩
    · exact Or.inl hζ
    · exact Or.inr (by simpa using! hlam)
  have hsmall := (hR T hTR).2 _ hx
  have hscale := (hR T hTR).1 _ hx
  rw [one_mul, ← Real.sqrt_eq_rpow] at hsmall
  have hnorm : ‖ζ‖ ≤ 1 := by
    have hroot := Real.sqrt_pos.2 hTpos
    nlinarith only [hsmall, hroot]
  refine ⟨by linarith, hnorm, ?_⟩
  calc
    _ ≤ ‖ζ‖ * Real.sqrt T := mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by linarith)) (norm_nonneg _)
    _ ≤ ((8 : ℝ) ^ η)⁻¹ * T ^ η := hscale
    _ = (T / 8) ^ η := by
      rw [Real.div_rpow hTpos.le (by norm_num : (0 : ℝ) ≤ 8)]
      ring

/-- The first source unsmoothing inequality, with the actual endpoint and
Gaussian average. All constants precede the law and both force windows. -/
theorem endpoint_unsmoothing_in_source_window
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α : ℝ, 0 < α ∧ ∀ b : ℝ, 0 < b → ∀ C₀ : ℝ,
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ (T : ℝ) (hT : 1 < T), T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal - gaussianAverage hd Q
        (T ^ (1 - b)) (Real.rpow_pos_of_pos (by linarith) _)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal)‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) *
          T ^ (-(1 / 2 + (d : ℝ) / 4) - b * α / 2) := by
  obtain ⟨α, η, A, Ap, B, Bp, t₀, hα, hη, hA, hAp, hB, hBp, ht₀, hh⟩ :=
    endpoint_unsmoothing_decay hholder hscalar d hd D
  obtain ⟨C, hC, hbound⟩ := exists_endpoint_absorption_constant
    (Ap := Ap) (k := (d : ℝ) / 4) hA hB hBp
  refine ⟨α, hα, ?_⟩
  intro b hb C₀
  obtain ⟨R, hRtwo, hR⟩ := exists_smoothing_threshold hb
  obtain ⟨S, hStwo, hS⟩ := exists_scalar_window_threshold hη C₀ t₀
  refine ⟨C, max R S, hC, hRtwo.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hlarge ζ hζ P Pdag hP hPdag ν
  have hTpos : 0 < T := by linarith
  have hsmall := hR T ((le_max_left _ _).trans hlarge)
  obtain ⟨htime, hnorm, hwindow⟩ := hS T ((le_max_right _ _).trans hlarge) ζ hζ
  have hcast : (T.toNNReal : ℝ) = T := Real.coe_toNNReal _ hTpos.le
  have heighth : ((T.toNNReal / 8 : ℝ≥0) : ℝ) = T / 8 := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat, hcast]
  have he := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν T.toNNReal
    (by rwa [hcast]) b (by rwa [hcast]) (by rwa [heighth]) hnorm
    (by rwa [heighth])
  simp only [hcast, heighth] at he
  exact he.trans (by
    simpa only [neg_div] using! hbound T ‖ζ‖ (b * α / 2) hTpos (norm_nonneg _))

/-- Translation of an integrable stationary kernel is translation of its average. -/
theorem stationary_kernel_shift {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (K : Vec d → ℂ) (a : Vec d)
    (F : Lp ℂ 2 (reducedLaw Q))
    (hK : Integrable (fun x => K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F)) :
    (∫ x : Vec d, K (x - a) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) =
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
      (∫ x : Vec d, K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  calc
    _ = ∫ x : Vec d, K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (x + a) F := by
      simpa only [add_sub_cancel_right] using!
        (integral_add_right_eq_self (fun x : Vec d => K (x - a) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) a).symm
    _ = _ := by
      change _ = (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        ).toContinuousLinearMap _
      rw [← ContinuousLinearMap.integral_comp_comm _ hK]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul, complexTranslation_add,
          add_comm x a]

/-- Every spatial derivative of a real-force kernel is a real translation. -/
theorem iteratedFDeriv_real_force {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (z : ℝ)
    (k : ℕ) (x : Vec d) :
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs (z : ℂ)) x =
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0)
        (x - (z * s) • (homogenizedCoefficient Q).mulVec (unitVector i)) := by
  have he : homogenizedGaussianKernel Q i s hs (z : ℂ) =
      fun y => homogenizedGaussianKernel Q i s hs 0
        (y - (z * s) • (homogenizedCoefficient Q).mulVec (unitVector i)) :=
    funext (homogenizedGaussianKernel_realForce_eq_translate Q i s hs z)
  rw [he, iteratedFDeriv_comp_sub]

/-- Real homogeneous derivative averages are translations of the unforced average. -/
theorem homogeneousDerivativeAverage_real_force {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (z : ℝ)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs (z : ℂ) k dirs F =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
        ((z * s) • (homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩))
        (gaussianDerivativeAverage hd Q s hs k dirs F) := by
  unfold homogeneousDerivativeAverage gaussianDerivativeAverage
  simp only [← Complex.ofReal_neg, iteratedFDeriv_real_force]
  have he (x : Vec d) : -x - (-z * s) •
      (homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩) =
      -(x - (z * s) • (homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩)) := by
    simp only [neg_mul, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  simp_rw [he]
  exact stationary_kernel_shift Q _ _ F
    (integrable_gaussianDerivativeAverage_integrand hd Q s hs k dirs F)

/-- Every real drift preserves the norm of the unforced derivative average. -/
theorem norm_homogeneousDerivativeAverage_real_force {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (z : ℝ)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs (z : ℂ) k dirs F‖ =
      ‖gaussianDerivativeAverage hd Q s hs k dirs F‖ := by
  rw [homogeneousDerivativeAverage_real_force hd, norm_complexTranslation]

/-- A real-force homogeneous average is the actual translation of its unforced average. -/
theorem homogeneousAverage_real_force {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (z : ℝ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q ⟨0, by omega⟩ s hs (z : ℂ) F =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
        ((z * s) • (homogenizedCoefficient Q).mulVec (unitVector ⟨0, by omega⟩))
        (gaussianAverage hd Q s hs F) := by
  unfold homogeneousAverage gaussianAverage
  simp_rw [homogenizedGaussianKernel_realForce_eq_translate]
  exact stationary_kernel_shift Q _ _ F
    (integrable_homogeneousAverage_integrand Q ⟨0, by omega⟩ s hs 0 F)

/-- Scalar Gaussian decay controls every real-drift homogeneous Hessian.
The endpoint force may still be complex; the propagation drift is any real number. -/
theorem real_homogeneous_hessian_of_scalar
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ a₀ η C Cp t₀ : ℝ,
      0 < a₀ ∧ a₀ < 1 ∧ 0 < η ∧ 0 < C ∧ 0 < Cp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η → ∀ ν : EndpointIndex d,
    ∀ (z : ℝ) (dirs : Fin 2 → Fin d) (s : ℝ), 2 * a₀ * (t : ℝ) ≤ s →
    ∀ hs : 0 < s,
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs (z : ℂ) 2 dirs
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
        C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * s ^ (-1 : ℝ) *
          (s ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) := by
  obtain ⟨a₀, η, ha₀, ha₀', hη, hh⟩ := hscalar d hd D
  obtain ⟨C, Cp, t₀, Cder, _, hCp, ht₀, hCder, hh⟩ := hh 2 le_rfl
  refine ⟨a₀, η, Cder 2, Cp, t₀, ha₀, ha₀', hη, hCder 2, hCp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν z dirs s hst hs
  rw [norm_homogeneousDerivativeAverage_real_force hd]
  have h := (((hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).2
    t ht hζ hwindow (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (indexedEndpoint_mem hd Q ν ζ P Pdag β a μ t)).2.2 2 dirs s hst hs).2
  simpa only [ENNReal.ofReal_ofNat, ← Lp.norm_def, Nat.cast_ofNat,
    neg_div, show -(2 : ℝ) / 2 = -1 by norm_num] using h

/-- Unforced Gaussian averaging commutes with the stationary translations. -/
theorem gaussianAverage_translation {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (a : Vec d)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    gaussianAverage hd Q s hs
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a F) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        (gaussianAverage hd Q s hs F) := by
  change homogeneousAverage Q ⟨0, by omega⟩ s hs 0 _ =
    complexTranslation _ _ a (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 F)
  rw [complexTranslation_homogeneousAverage]
  unfold homogeneousAverage
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [← complexTranslation_add, add_comm x a]

/-- Real drift preserves the norm of the homogeneous unsmoothing error. -/
theorem norm_real_homogeneous_unsmoothing {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (z : ℝ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q ⟨0, by omega⟩ t ht (z : ℂ) F -
        gaussianAverage hd Q s hs
          (homogeneousAverage Q ⟨0, by omega⟩ t ht (z : ℂ) F)‖ =
      ‖gaussianAverage hd Q t ht F -
        gaussianAverage hd Q s hs (gaussianAverage hd Q t ht F)‖ := by
  rw [homogeneousAverage_real_force hd, gaussianAverage_translation,
    ← map_sub, norm_complexTranslation]

/-- Positive-time Gaussian increments have the actual inverse-time operator bound. -/
theorem gaussianAverage_increment_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianAverage hd Q (t + s) (add_pos ht hs) F - gaussianAverage hd Q t ht F‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * t⁻¹ * ‖F‖ * s := by
  let f : ℝ → Lp ℂ 2 (reducedLaw Q) := fun u =>
    homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 ⟨max u 0, le_max_right _ _⟩ F
  have hdiff : ∀ u ∈ Set.Icc t (t + s), DifferentiableAt ℝ f u := by
    intro u hu
    exact (hasDerivAt_homogeneousGaussianEvolution_time Q ⟨0, by omega⟩ 0 F u
      (ht.trans_le hu.1)).differentiableAt
  have hbound : ∀ u ∈ Set.Icc t (t + s), ‖deriv f u‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * t⁻¹ * ‖F‖ := by
    intro u hu
    have h := norm_deriv_homogeneousGaussianEvolution_time_le Q ⟨0, by omega⟩ 0 F u
      (ht.trans_le hu.1)
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_mul, add_zero, Real.exp_zero, mul_one] at h
    exact h.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (inv_anti₀ ht hu.1) (homogeneousGaussianTimeDerivativeBound_pos d Λ).le)
      (norm_nonneg F))
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound
    (convex_Icc t (t + s)) (Set.left_mem_Icc.mpr (by linarith))
    (Set.right_mem_Icc.mpr (by linarith))
  have he (u : ℝ) (hu : 0 < u) : f u = gaussianAverage hd Q u hu F := by
    dsimp only [f]
    erw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 _
      (by simpa only [max_eq_left hu.le] using! hu)]
    simp only [max_eq_left hu.le]
    rfl
  simpa only [he (t + s) (add_pos ht hs), he t ht, add_sub_cancel_left,
    Real.norm_eq_abs, abs_of_pos hs] using h

/-- Unforced unsmoothing uses a half-time smoothed datum rather than its original norm. -/
theorem gaussianAverage_unsmoothing_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianAverage hd Q t ht F -
        gaussianAverage hd Q s hs (gaussianAverage hd Q t ht F)‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t / 2)⁻¹ *
        ‖gaussianAverage hd Q (t / 2) (by positivity) F‖ * s := by
  have hhalf : 0 < t / 2 := by positivity
  have hadd (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
      gaussianAverage hd Q u hu (gaussianAverage hd Q v hv F) =
        gaussianAverage hd Q (u + v) (add_pos hu hv) F :=
    homogeneousAverage_add Q ⟨0, by omega⟩ u v hu hv 0 F
  have h := gaussianAverage_increment_le hd Q (t / 2) s hhalf hs
    (gaussianAverage hd Q (t / 2) hhalf F)
  rw [hadd, hadd] at h
  rw [hadd]
  have he : t / 2 + s + t / 2 = s + t := by ring
  have he' : t / 2 + t / 2 = t := by ring
  simpa only [he, he', norm_sub_rev] using! h
/-- Every signed real drift has the same half-time unsmoothing estimate. -/
theorem real_homogeneous_unsmoothing_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (t s : ℝ) (ht : 0 < t) (hs : 0 < s) (z : ℝ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q ⟨0, by omega⟩ t ht (z : ℂ) F -
        gaussianAverage hd Q s hs
          (homogeneousAverage Q ⟨0, by omega⟩ t ht (z : ℂ) F)‖ ≤
      homogeneousGaussianTimeDerivativeBound d Λ * (t / 2)⁻¹ *
        ‖gaussianAverage hd Q (t / 2) (by positivity) F‖ * s := by
  rw [norm_real_homogeneous_unsmoothing hd]
  exact gaussianAverage_unsmoothing_le hd Q t s ht hs F

/-- The scalar contract supplies the smoothed endpoint norm in the real-drift estimate. -/
theorem real_homogeneous_unsmoothing_of_scalar
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ a₀ η C Cp t₀ : ℝ,
      0 < a₀ ∧ a₀ < 1 ∧ 0 < η ∧ 0 < C ∧ 0 < Cp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η → ∀ ν : EndpointIndex d,
    ∀ (z u s : ℝ) (hu : 0 < u) (hs : 0 < s), a₀ * (t : ℝ) ≤ u / 2 →
      ‖homogeneousAverage Q ⟨0, by omega⟩ u hu (z : ℂ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) -
        gaussianAverage hd Q s hs
          (homogeneousAverage Q ⟨0, by omega⟩ u hu (z : ℂ)
            (indexedEndpoint hd Q ν ζ P Pdag β a μ t))‖ ≤
        C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * (u / 2)⁻¹ *
          ((u / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (u / 2) ^ (-(d : ℝ) / 4)) * s := by
  obtain ⟨a₀, η, ha₀, ha₀', hη, hh⟩ := hscalar d hd D
  obtain ⟨C, Cp, t₀, Cder, hC, hCp, ht₀, _, hh⟩ := hh 2 le_rfl
  let B := homogeneousGaussianTimeDerivativeBound d D.ellipticity
  have hB : 0 < B := homogeneousGaussianTimeDerivativeBound_pos _ _
  refine ⟨a₀, η, B * C, Cp, t₀, ha₀, ha₀', hη, mul_pos hB hC, hCp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν z u s hu hs hsu
  have h := (((hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).2
    t ht hζ hwindow (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (indexedEndpoint_mem hd Q ν ζ P Pdag β a μ t)).2.1 (u / 2) hsu
    (by positivity)).2
  simp only [ENNReal.ofReal_ofNat, ← Lp.norm_def] at h
  have hh := real_homogeneous_unsmoothing_le hd Q u s hu hs z
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
  refine hh.trans ?_
  calc
    _ ≤ B * (u / 2)⁻¹ *
        (C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          ((u / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (u / 2) ^ (-(d : ℝ) / 4))) * s := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by positivity)) hs.le
    _ = _ := by ring

/-- Every positive comparable time has the eighth-time scalar decay bound. -/
theorem comparable_time_decay_le {T u z k : ℝ} (hT : 0 < T) (hu : T / 8 ≤ u)
    (hz : 0 ≤ z) (hk : 0 ≤ k) :
    u ^ (-(1 / 2 + k)) + z * u ^ (-k) ≤
      ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k) *
        (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k)) := by
  apply le_trans _ (eighth_time_decay_le hT hz)
  exact add_le_add
    (Real.rpow_le_rpow_of_nonpos (by positivity) hu (by linarith))
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (by positivity) hu
      (by linarith)) hz)

/-- The inverse comparable time supplies one full terminal-time derivative gain. -/
theorem comparable_time_derivative_decay_le {T u z k : ℝ} (hT : 0 < T)
    (hu : T / 8 ≤ u) (hz : 0 ≤ z) (hk : 0 ≤ k) :
    u⁻¹ * (u ^ (-(1 / 2 + k)) + z * u ^ (-k)) ≤
      (8 * ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k)) *
        (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k) - 1) := by
  have hu' : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hi : u⁻¹ ≤ 8 * T⁻¹ := by
    simpa only [inv_div, div_eq_mul_inv, mul_inv_rev, inv_inv] using!
      inv_anti₀ (by positivity) hu
  have hp : T⁻¹ * T ^ (-(1 / 2 + k)) = T ^ (-(1 / 2 + k) - 1) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hT]
    congr 1
    ring
  calc
    _ ≤ (8 * T⁻¹) *
        (((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k) *
          (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k))) :=
      mul_le_mul hi (comparable_time_decay_le hT hu hz hk) (by positivity) (by positivity)
    _ = _ := by rw [← hp]; ring

/-- The source force windows are scalar-admissible at the literal mesoscopic time. -/
theorem exists_mesoscopic_scalar_threshold {η δ : ℝ} (hη : 0 < η)
    (hδ : 0 < δ) (hδ' : δ < 1 / 2) (C₀ t₀ : ℝ) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
      t₀ ≤ T ^ (1 - δ) ∧ ‖ζ‖ ≤ 1 ∧
        ‖ζ‖ * Real.sqrt (T ^ (1 - δ)) ≤ (T ^ (1 - δ)) ^ η ∧
        T ^ (1 - δ) ≤ T / 4 := by
  have hexp : 0 < 1 - δ := by linarith
  have htime : ∀ᶠ T : ℝ in Filter.atTop, t₀ ≤ T ^ (1 - δ) :=
    (tendsto_rpow_atTop hexp).eventually (Filter.eventually_ge_atTop t₀)
  have hscale := eventually_force_window_le_rpow (mul_pos hexp hη) zero_lt_one C₀
  have hnorm := eventually_force_window_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
    zero_lt_one C₀
  have hsmall : ∀ᶠ T : ℝ in Filter.atTop, T ^ (-δ) ≤ 1 / 4 :=
    (tendsto_rpow_neg_atTop hδ).eventually
      (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp (htime.and (hscale.and (hnorm.and hsmall)))
  refine ⟨max 2 R, le_max_left _ _, ?_⟩
  intro T hT ζ hζ
  have hTtwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTpos : 0 < T := by linarith
  have hh := hR T ((le_max_right _ _).trans hT)
  have hx : ‖ζ‖ * Real.sqrt T ≤ 2 ∨
      ‖ζ‖ * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ) := by
    rcases hζ with hζ | ⟨lam, rfl, hlam⟩
    · exact Or.inl hζ
    · exact Or.inr (by simpa using! hlam)
  have hn := hh.2.2.1 _ hx
  rw [one_mul, ← Real.sqrt_eq_rpow] at hn
  have htau : T ^ (1 - δ) ≤ T := by
    simpa only [Real.rpow_one] using! Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T)
      (show 1 - δ ≤ 1 by linarith)
  refine ⟨hh.1, ?_, ?_, ?_⟩
  · have hroot := Real.sqrt_pos.mpr hTpos
    nlinarith only [hn, hroot]
  · calc
      _ ≤ ‖ζ‖ * Real.sqrt T :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htau) (norm_nonneg _)
      _ ≤ T ^ ((1 - δ) * η) := by simpa only [one_mul] using! hh.2.1 _ hx
      _ = _ := Real.rpow_mul hTpos.le _ _
  · have he : T ^ (1 - δ) = T * T ^ (-δ) := by
      calc
        _ = T ^ (1 : ℝ) * T ^ (-δ) := by
          rw [← Real.rpow_add hTpos]
          congr 1
        _ = _ := by rw [Real.rpow_one]
    rw [he]
    nlinarith only [mul_le_mul_of_nonneg_left hh.2.2.2 hTpos.le]

/-- Uniform absorption for the scalar derivative profile at any comparable time. -/
theorem exists_comparable_derivative_absorption_constant {B Cp k : ℝ}
    (hB : 0 < B) (hCp : 0 < Cp) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T u τ z s : ℝ, 0 < T → T / 8 ≤ u → τ ≤ T →
      0 ≤ z → 0 ≤ s →
      B * Real.exp (Cp * z ^ 2 * τ) * u⁻¹ *
          (u ^ (-(1 / 2 + k)) + z * u ^ (-k)) * s ≤
        C * Real.exp (C * z ^ 2 * T) * T ^ (-(1 / 2 + k) - 1) * s := by
  let K := 16 * B * ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k)
  let C := max K (Cp + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 < C := hK.trans_le (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro T u τ z s hT hu hτ hz hs
  have hy : 0 ≤ z ^ 2 * T := mul_nonneg (sq_nonneg _) hT.le
  have hx := scaled_force_polynomial_le
    (mul_nonneg hz (Real.sqrt_nonneg T)) (by norm_num : (0 : ℝ) ≤ 1)
  have hx2 : (z * Real.sqrt T) ^ 2 = z ^ 2 * T := by
    rw [mul_pow, Real.sq_sqrt hT.le]
  simp only [Real.rpow_one, one_mul, hx2] at hx
  have hexp : Real.exp (Cp * z ^ 2 * τ) ≤ Real.exp (Cp * z ^ 2 * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hτ (by positivity))
  have hu' : 0 < u := lt_of_lt_of_le (by positivity) hu
  have hdecay := comparable_time_derivative_decay_le hT hu hz hk
  have hprod : Real.exp (Cp * z ^ 2 * T) * Real.exp (z ^ 2 * T) =
      Real.exp ((Cp + 1) * z ^ 2 * T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = B * Real.exp (Cp * z ^ 2 * τ) *
        (u⁻¹ * (u ^ (-(1 / 2 + k)) + z * u ^ (-k))) * s := by ring
    _ ≤ B * Real.exp (Cp * z ^ 2 * T) *
        ((8 * ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k)) *
          (1 + z * Real.sqrt T) * T ^ (-(1 / 2 + k) - 1)) * s := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul
        (mul_le_mul_of_nonneg_left hexp hB.le) hdecay (by positivity) (by positivity)) hs
    _ ≤ B * Real.exp (Cp * z ^ 2 * T) *
        ((8 * ((8 : ℝ) ^ (1 / 2 + k) + (8 : ℝ) ^ k)) *
          (2 * Real.exp (z ^ 2 * T)) * T ^ (-(1 / 2 + k) - 1)) * s := by
      gcongr
    _ = K * (Real.exp (Cp * z ^ 2 * T) * Real.exp (z ^ 2 * T)) *
        T ^ (-(1 / 2 + k) - 1) * s := by dsimp only [K]; ring
    _ = K * Real.exp ((Cp + 1) * z ^ 2 * T) * T ^ (-(1 / 2 + k) - 1) * s := by
      rw [hprod]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hs
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hT.le _)
      apply mul_le_mul (le_max_left _ _) _ (Real.exp_pos _).le hC.le
      apply Real.exp_le_exp.mpr
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_right (le_max_right K (Cp + 1)) hy

/-- The actual homogeneous unsmoothing inequality on the real-propagation branch.
The endpoint force may occupy either source force window. -/
theorem real_homogeneous_unsmoothing_in_source_window
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (b C₀ : ℝ) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ T : ℝ, ∀ hT : 1 < T, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d) (z : ℝ),
      let τ := T ^ (1 - δ)
      let s := T ^ (1 - b)
      let ht : 0 < T - τ := by
        have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith)
        linarith
      let hs : 0 < s := Real.rpow_pos_of_pos (by linarith) _
      let V := homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht (z : ℂ)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)
      ‖V - gaussianAverage hd Q s hs V‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b) := by
  obtain ⟨a₀, η, B, Bp, t₀, _, ha₀, hη, hB, hBp, ht₀, hh⟩ :=
    real_homogeneous_unsmoothing_of_scalar hscalar d hd D
  obtain ⟨C, hC, habsorb⟩ := exists_comparable_derivative_absorption_constant
    hB hBp (by positivity : 0 ≤ (d : ℝ) / 4)
  obtain ⟨T₀, hT₀, hthreshold⟩ := exists_mesoscopic_scalar_threshold hη hδ hδ' C₀ t₀
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hTT ζ hζ P Pdag hP hPdag ν z
  dsimp only
  have hTpos : 0 < T := by linarith
  have hτpos : 0 < T ^ (1 - δ) := Real.rpow_pos_of_pos hTpos _
  have hτcast : (Real.toNNReal (T ^ (1 - δ)) : ℝ) = T ^ (1 - δ) :=
    Real.coe_toNNReal _ hτpos.le
  obtain ⟨htime, hnorm, hwindow, hsmall⟩ := hthreshold T hTT ζ hζ
  have hprop : 0 < T - T ^ (1 - δ) := by linarith
  have hrange : a₀ * T ^ (1 - δ) ≤ (T - T ^ (1 - δ)) / 2 := by
    have h := mul_le_mul_of_nonneg_right ha₀.le hτpos.le
    nlinarith only [h, hsmall, hτpos]
  have hs : 0 < T ^ (1 - b) := Real.rpow_pos_of_pos hTpos _
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
    (T ^ (1 - δ)).toNNReal (by rwa [hτcast]) hnorm (by rwa [hτcast]) ν z
    (T - T ^ (1 - δ)) (T ^ (1 - b)) hprop hs (by rwa [hτcast])
  simp only [hτcast] at h
  have ha := habsorb T ((T - T ^ (1 - δ)) / 2) (T ^ (1 - δ)) ‖ζ‖
    (T ^ (1 - b)) hTpos (by linarith) (by linarith) (norm_nonneg _) hs.le
  have he : T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) * T ^ (1 - b) =
      T ^ (-(1 / 2 + (d : ℝ) / 4) - b) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  exact h.trans (by simpa only [mul_assoc, he, neg_div] using! ha)

/-- Terminal-time homogeneous Hessian decay for every signed real propagation force. -/
theorem real_homogeneous_hessian_in_source_window
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (C₀ : ℝ) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ T : ℝ, ∀ hT : 1 < T, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d) (z : ℝ),
    ∀ dirs : Fin 2 → Fin d,
      let τ := T ^ (1 - δ)
      let ht : 0 < T - τ := by
        have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith)
        linarith
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) ht (z : ℂ) 2 dirs
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) := by
  obtain ⟨a₀, η, B, Bp, t₀, _, ha₀, hη, hB, hBp, ht₀, hh⟩ :=
    real_homogeneous_hessian_of_scalar hscalar d hd D
  obtain ⟨C, hC, habsorb⟩ := exists_comparable_derivative_absorption_constant
    hB hBp (by positivity : 0 ≤ (d : ℝ) / 4)
  obtain ⟨T₀, hT₀, hthreshold⟩ := exists_mesoscopic_scalar_threshold hη hδ hδ' C₀ t₀
  refine ⟨C, T₀, hC, hT₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hTT ζ hζ P Pdag hP hPdag ν z dirs
  dsimp only
  have hTpos : 0 < T := by linarith
  have hτpos : 0 < T ^ (1 - δ) := Real.rpow_pos_of_pos hTpos _
  have hτcast : (Real.toNNReal (T ^ (1 - δ)) : ℝ) = T ^ (1 - δ) :=
    Real.coe_toNNReal _ hτpos.le
  obtain ⟨htime, hnorm, hwindow, hsmall⟩ := hthreshold T hTT ζ hζ
  have hprop : 0 < T - T ^ (1 - δ) := by linarith
  have hrange : 2 * a₀ * T ^ (1 - δ) ≤ T - T ^ (1 - δ) := by
    have h := mul_le_mul_of_nonneg_right ha₀.le hτpos.le
    nlinarith only [h, hsmall, hτpos]
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
    (T ^ (1 - δ)).toNNReal (by rwa [hτcast]) hnorm (by rwa [hτcast]) ν z dirs
    (T - T ^ (1 - δ)) (by rwa [hτcast]) hprop
  simp only [hτcast] at h
  have ha := habsorb T (T - T ^ (1 - δ)) (T ^ (1 - δ)) ‖ζ‖ 1 hTpos
    (by linarith) (by linarith) (norm_nonneg _) zero_le_one
  have hi : (T - T ^ (1 - δ)) ^ (-1 : ℝ) = (T - T ^ (1 - δ))⁻¹ :=
    Real.rpow_neg_one _
  exact h.trans (by simpa only [mul_one, hi, neg_div] using! ha)

/-- The prescribed smoothing choice absorbs the complete mesoscopic Duhamel loss. -/
theorem smoothed_duhamel_gain_le {T h L b ε δ ρ : ℝ} (hT : 1 ≤ T)
    (hhL : 0 < h + L) (hb : b < ε * (1 - δ) / (2 * (h + L)))
    (hρ : ρ < ε * (1 - δ) / 2) :
    T ^ (-h) * T ^ (b * (h + L)) * (T ^ (1 - δ)) ^ (-ε) ≤ T ^ (-h - ρ) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hb' := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hhL)).mp hb
  rw [← Real.rpow_mul hTpos.le, ← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
  apply Real.rpow_le_rpow_of_exponent_le hT
  nlinarith only [hb', hρ]

open Filter Set
open scoped Topology BigOperators

variable {d : ℕ} {Λ r : ℝ}
attribute [local instance] reducedLaw_probability

/-- The literal spatial kernel is entire in its force parameter. -/
theorem differentiable_force_kernel (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (x : Vec d) :
    Differentiable ℂ (fun z => homogenizedGaussianKernel Q i s hs z x) := by
  unfold homogenizedGaussianKernel
  fun_prop

/-- A common integrable bound on force discs for the unit kernel and its force derivative. -/
theorem exists_integrable_unit_kernel_force_majorant
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (R : ℝ) :
    ∃ b : Vec d → ℝ, Integrable b ∧
      (∀ x z, ‖z‖ ≤ R →
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ b x) ∧
      (∀ x z, ‖z‖ ≤ R →
        ‖deriv (fun w => homogenizedGaussianKernel Q i 1 zero_lt_one w x) z‖ ≤ b x) := by
  let n := (volume : Measure (Vec d)).integrablePower
  let M (m : ℕ) := gaussianSchwartzBound d Λ m *
    Real.exp (gaussianSchwartzBound d Λ m * (1 + (R + 1)) ^ 2)
  let b (x : Vec d) := (2 : ℝ) ^ n * (M 0 + M n) * (1 + ‖x‖) ^ (-(n : ℝ))
  have hb (x : Vec d) (z : ℂ) (hz : ‖z‖ ≤ R + 1) :
      ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ b x := by
    have hw (m : ℕ) := (homogenizedGaussianKernel_weighted_coordinate_bounds
      Q i 1 zero_lt_one (by norm_num) le_rfl z x m).1
    have hM (m : ℕ) : (1 + euclideanNorm x) ^ m *
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ M m := by
      apply (hw m).trans
      apply mul_le_mul_of_nonneg_left _ (gaussianSchwartzBound_pos d Λ Q.ellipticity_parameter m).le
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ (gaussianSchwartzBound_pos d Λ Q.ellipticity_parameter m).le
      exact pow_le_pow_left₀ (by positivity) (add_le_add_right hz 1) 2
    have h0 := hM 0
    simp only [pow_zero, one_mul] at h0
    have hn : ‖x‖ ^ (0 + n) *
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one z x‖ ≤ M n := by
      simp only [zero_add]
      apply (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg x)
          ((norm_vec_le_euclideanNorm x).trans (le_add_of_nonneg_left zero_le_one)) n)
        (norm_nonneg _)).trans
      exact hM n
    simpa only [pow_zero, one_mul] using!
      pow_mul_le_of_le_of_pow_mul_le (norm_nonneg x) (norm_nonneg _) h0 hn
  refine ⟨b, (Measure.integrable_pow_neg_integrablePower (volume : Measure (Vec d))).const_mul _,
    (fun x z hz => hb x z (hz.trans (by linarith))), ?_⟩
  intro x z hz
  have H := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1
    (by norm_num : (0 : ℝ) < 1)
    (differentiable_force_kernel Q i 1 zero_lt_one x).differentiableOn.diffContOnCl
    (fun w hw => hb x w (by
      have ht := norm_add_le (w - z) z
      have he : ‖w - z‖ = 1 := by simpa only [Metric.mem_sphere, dist_eq_norm] using! hw
      rw [sub_add_cancel, he] at ht
      linarith))
  simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, one_pow, div_one] using! H

/-- The unit-kernel integral along any scaled stationary translation orbit is entire. -/
theorem differentiable_unit_kernel_integral
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (c : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Differentiable ℂ (fun z => ∫ x : Vec d,
      homogenizedGaussianKernel Q i 1 zero_lt_one z x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f) := by
  let K (z : ℂ) (x : Vec d) :=
    homogenizedGaussianKernel Q i 1 zero_lt_one z x
  let U (x : Vec d) := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f
  have hU : Continuous U :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      ((continuous_id.const_smul c).prodMk continuous_const)
  have hK : Continuous (fun p : Vec d × ℂ => K p.2 p.1) := by unfold K homogenizedGaussianKernel; fun_prop
  have hD (z : ℂ) : AEStronglyMeasurable (fun x => deriv (fun w => K w x) z) :=
    ((stronglyMeasurable_deriv_with_param (f := fun x w => K w x) hK).comp_measurable
      (measurable_id.prodMk (measurable_const (a := z)))).aestronglyMeasurable
  intro z
  obtain ⟨b, hb, h0, h1⟩ := exists_integrable_unit_kernel_force_majorant Q i (‖z‖ + 1)
  have hbound (w : ℂ) (hw : w ∈ Metric.ball z 1) : ‖w‖ ≤ ‖z‖ + 1 := by
    have ht := norm_add_le (w - z) z
    have he : ‖w - z‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using! hw
    rw [sub_add_cancel] at ht
    linarith
  have hmeas (w : ℂ) : AEStronglyMeasurable (fun x => K w x • U x) :=
    (((hK.comp (continuous_id.prodMk continuous_const)).fun_smul hU).aestronglyMeasurable)
  have hint : Integrable (fun x => K z x • U x) := by
    apply (hb.mul_const ‖f‖).mono' (hmeas z)
    filter_upwards with x
    rw [norm_smul, norm_complexTranslation]
    exact mul_le_mul_of_nonneg_right (h0 x z (by linarith [norm_nonneg z])) (norm_nonneg f)
  have H := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds z zero_lt_one)
    (Eventually.of_forall hmeas) hint ((hD z).fun_smul hU.aestronglyMeasurable)
    (Eventually.of_forall fun x w hw => by
      rw [norm_smul, norm_complexTranslation]
      exact mul_le_mul_of_nonneg_right (h1 x w (hbound w hw)) (norm_nonneg f))
    (hb.mul_const ‖f‖)
    (Eventually.of_forall fun x w _ =>
      ((differentiable_force_kernel Q i 1 zero_lt_one x w).hasDerivAt.smul_const (U x)))
  exact H.2.differentiableAt

/-- Parabolic scaling of the actual stationary average, including its translation orbit. -/
theorem homogeneousAverage_eq_scaled
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i s hs ζ f = ∫ x : Vec d,
      homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (Real.sqrt s • x) f := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  have hd (x : Vec d) := homogenizedGaussianKernel_scale Q i c 1 hc zero_lt_one ζ x
  simp only [mul_one, hcs] at hd
  have he := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => homogenizedGaussianKernel Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) c
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _))] at he
  simp only [hd, mul_smul, Complex.coe_smul] at he
  erw [integral_smul] at he
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero d hc.ne')) he).symm

/-- The actual positive-time stationary Gaussian average is entire in force. -/
theorem differentiable_force_homogeneousAverage
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Differentiable ℂ (fun z => homogeneousAverage Q i s hs z f) := by
  simp_rw [homogeneousAverage_eq_scaled]
  exact (differentiable_unit_kernel_integral Q i (Real.sqrt s) f).comp
    (differentiable_id.mul_const (Real.sqrt s : ℂ))
/-- A half-time unforced inner Gaussian retains the full complex propagation drift. -/
theorem homogeneousAverage_half_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q ⟨0, by omega⟩ s hs ζ f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianAverage hd Q (s / 2) (half_pos hs) f) := by
  let F (z : ℂ) := homogeneousAverage Q ⟨0, by omega⟩ s hs z f
  let G (z : ℂ) := homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * z)
    (gaussianAverage hd Q (s / 2) (half_pos hs) f)
  have hf : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    (differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ s hs f).analyticAt z
  have hg : AnalyticOnNhd ℂ G Set.univ := fun z _ =>
    ((differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f)).comp
        (differentiable_id.const_mul 2)).analyticAt z
  have hr (z : ℝ) : F (z : ℂ) = G (z : ℂ) := by
    dsimp only [F, G]
    rw [show (2 : ℂ) * (z : ℂ) = ((2 * z : ℝ) : ℂ) by push_cast; rfl]
    rw [homogeneousAverage_real_force hd, homogeneousAverage_real_force hd]
    have hsum := homogeneousAverage_add Q ⟨0, by omega⟩ (s / 2) (s / 2)
      (half_pos hs) (half_pos hs) 0 f
    change gaussianAverage hd Q (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f) =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2 + s / 2) _ 0 f at hsum
    have he : s / 2 + s / 2 = s := by ring
    simp only [he] at hsum
    change gaussianAverage hd Q (s / 2) (half_pos hs)
      (gaussianAverage hd Q (s / 2) (half_pos hs) f) = gaussianAverage hd Q s hs f at hsum
    rw [hsum, show 2 * z * (s / 2) = z * s by ring]
  have hc : (0 : ℂ) ∈ closure ({z | F z = G z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hr _, ?_⟩, ?_⟩
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hε))
    · simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
  exact hf.eqOn_of_preconnected_of_mem_closure hg isPreconnected_univ (mem_univ 0) hc
    (mem_univ ζ)
/-- Entire Banach-valued functions agreeing on the real axis agree everywhere. -/
theorem eq_of_entire_of_real {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F G : ℂ → E} (hF : Differentiable ℂ F)
    (hG : Differentiable ℂ G) (hreal : ∀ x : ℝ, F (x : ℂ) = G (x : ℂ)) : F = G := by
  have hf : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hg : AnalyticOnNhd ℂ G Set.univ := fun z _ => hG.analyticAt z
  have hc : (0 : ℂ) ∈ closure ({z | F z = G z} \ {0}) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨((ε / 2 : ℝ) : ℂ), ⟨hreal _, ?_⟩, ?_⟩
    · change ((ε / 2 : ℝ) : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (ne_of_gt (half_pos hε))
    · simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
  exact funext fun z => hf.eqOn_of_preconnected_of_mem_closure hg isPreconnected_univ
    (mem_univ 0) hc (mem_univ z)

/-- Unforced smoothing commutes with the literal complex-force homogeneous propagation. -/
theorem gaussianAverage_homogeneousAverage_commute {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianAverage hd Q s hs (homogeneousAverage Q ⟨0, by omega⟩ t ht ζ f) =
      homogeneousAverage Q ⟨0, by omega⟩ t ht ζ (gaussianAverage hd Q s hs f) := by
  have h := eq_of_entire_of_real
    ((homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0).differentiable.comp
      (differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ t ht f))
    (differentiable_force_homogeneousAverage Q ⟨0, by omega⟩ t ht
      (gaussianAverage hd Q s hs f)) (fun z => by
        change gaussianAverage hd Q s hs (homogeneousAverage Q ⟨0, by omega⟩ t ht (z : ℂ) f) = _
        rw [homogeneousAverage_real_force hd, homogeneousAverage_real_force hd,
          gaussianAverage_translation]
        congr 1
        change homogeneousAverage Q ⟨0, by omega⟩ s hs 0
          (homogeneousAverage Q ⟨0, by omega⟩ t ht 0 f) =
          homogeneousAverage Q ⟨0, by omega⟩ t ht 0
            (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 f)
        rw [homogeneousAverage_add, homogeneousAverage_add]
        congr 1; ring)
  exact congrFun h ζ

/-- Complex unsmoothing retains an inner unforced Gaussian before the scalar decay is used. -/
theorem homogeneous_unsmoothing_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (t s : ℝ) (ht : 0 < t) (hs : 0 < s)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q ⟨0, by omega⟩ t ht ζ f -
        gaussianAverage hd Q s hs (homogeneousAverage Q ⟨0, by omega⟩ t ht ζ f)‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * t) *
        (homogeneousGaussianTimeDerivativeBound d Λ * (t / 4)⁻¹ *
          ‖gaussianAverage hd Q (t / 4) (by positivity) f‖ * s) := by
  rw [homogeneousAverage_half_split hd Q t ht ζ f,
    gaussianAverage_homogeneousAverage_commute hd Q s (t / 2) hs (half_pos ht)]
  let A := homogeneousAverageCLM Q ⟨0, by omega⟩ (t / 2) (half_pos ht) (2 * ζ)
  change ‖A (gaussianAverage hd Q (t / 2) (half_pos ht) f) -
    A (gaussianAverage hd Q s hs (gaussianAverage hd Q (t / 2) (half_pos ht) f))‖ ≤ _
  rw [← map_sub]
  calc
    _ ≤ ‖A‖ * ‖gaussianAverage hd Q (t / 2) (half_pos ht) f -
        gaussianAverage hd Q s hs (gaussianAverage hd Q (t / 2) (half_pos ht) f)‖ :=
      A.le_opNorm _
    _ ≤ _ := by
      have he : sourceReducedBound Λ * ‖2 * ζ‖ ^ 2 * (t / 2) / 2 =
          sourceReducedBound Λ * ‖ζ‖ ^ 2 * t := by
        rw [norm_mul]
        norm_num
        ring
      apply mul_le_mul
      · simpa only [he] using! (norm_homogeneousAverageCLM_le Q ⟨0, by omega⟩ (t / 2) (half_pos ht) (2 * ζ))
      · simpa only [show t / 2 / 2 = t / 4 by ring] using!
        gaussianAverage_unsmoothing_le hd Q (t / 2) s (half_pos ht) hs f
      · exact norm_nonneg _
      · exact (Real.exp_pos _).le

/-- Scalar decay for the inner Gaussian controls unsmoothing for every complex propagation force. -/
theorem homogeneous_unsmoothing_of_scalar
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ a₀ η C Cp t₀ : ℝ,
      0 < a₀ ∧ a₀ < 1 ∧ 0 < η ∧ 0 < C ∧ 0 < Cp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η → ∀ ν : EndpointIndex d,
    ∀ (z : ℂ) (u s : ℝ) (hu : 0 < u) (hs : 0 < s), a₀ * (t : ℝ) ≤ u / 4 →
      ‖homogeneousAverage Q ⟨0, by omega⟩ u hu z
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) -
        gaussianAverage hd Q s hs
          (homogeneousAverage Q ⟨0, by omega⟩ u hu z
            (indexedEndpoint hd Q ν ζ P Pdag β a μ t))‖ ≤
        C * Real.exp (sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * u) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * (u / 4)⁻¹ *
          ((u / 4) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (u / 4) ^ (-(d : ℝ) / 4)) * s := by
  obtain ⟨a₀, η, ha₀, ha₀', hη, hh⟩ := hscalar d hd D
  obtain ⟨C, Cp, t₀, Cder, hC, hCp, ht₀, _, hh⟩ := hh 2 le_rfl
  let B := homogeneousGaussianTimeDerivativeBound d D.ellipticity
  have hB : 0 < B := homogeneousGaussianTimeDerivativeBound_pos _ _
  refine ⟨a₀, η, B * C, Cp, t₀, ha₀, ha₀', hη, mul_pos hB hC, hCp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν z u s hu hs hsu
  have h := (((hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).2
    t ht hζ hwindow (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (indexedEndpoint_mem hd Q ν ζ P Pdag β a μ t)).2.1 (u / 4) hsu
    (by positivity)).2
  simp only [ENNReal.ofReal_ofNat, ← Lp.norm_def] at h
  have hh := homogeneous_unsmoothing_le hd Q u s hu hs z
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
  refine hh.trans ?_
  calc
    _ ≤ Real.exp (sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * u) *
        (B * (u / 4)⁻¹ *
          (C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            ((u / 4) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * (u / 4) ^ (-(d : ℝ) / 4))) * s) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h (by positivity)) hs.le
    _ = _ := by ring

/-- Terminal-time homogeneous unsmoothing for every propagation force of at most the endpoint force norm. -/
theorem homogeneous_unsmoothing_in_source_window
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (b C₀ : ℝ) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ T : ℝ, ∀ hT : 1 < T, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d) (z : ℂ), ‖z‖ ≤ ‖ζ‖ →
      let τ := T ^ (1 - δ)
      let s := T ^ (1 - b)
      let ht : 0 < T - τ := by
        have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith)
        linarith
      let hs : 0 < s := Real.rpow_pos_of_pos (by linarith) _
      let V := homogeneousAverage Q ⟨0, by omega⟩ (T - τ) ht z
        (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)
      ‖V - gaussianAverage hd Q s hs V‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b) := by
  obtain ⟨a₀, η, B, Bp, t₀, _, ha₀, hη, hB, hBp, ht₀, hh⟩ :=
    homogeneous_unsmoothing_of_scalar hscalar d hd D
  obtain ⟨C, hC, habsorb⟩ := exists_comparable_derivative_absorption_constant
    hB hBp (by positivity : 0 ≤ (d : ℝ) / 4)
  obtain ⟨T₀, hT₀, hthreshold⟩ := exists_mesoscopic_scalar_threshold hη hδ hδ' C₀ t₀
  obtain ⟨T₁, hT₁, hsmalltime⟩ := exists_smoothing_threshold hδ
  let S := |sourceReducedBound D.ellipticity|
  refine ⟨C + S, max T₀ T₁, by positivity, hT₀.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hTT ζ hζ P Pdag hP hPdag ν z hz
  dsimp only
  have hTpos : 0 < T := by linarith
  have hτpos : 0 < T ^ (1 - δ) := Real.rpow_pos_of_pos hTpos _
  have hτcast : (Real.toNNReal (T ^ (1 - δ)) : ℝ) = T ^ (1 - δ) :=
    Real.coe_toNNReal _ hτpos.le
  obtain ⟨htime, hnorm, hwindow, hsmall⟩ := hthreshold T ((le_max_left _ _).trans hTT) ζ hζ
  have hprop : 0 < T - T ^ (1 - δ) := by linarith
  have hsmall' : T ^ (1 - δ) ≤ T / 16 := by
    have hx := hsmalltime T ((le_max_right _ _).trans hTT)
    rw [← smoothing_ratio hTpos] at hx
    exact (div_le_iff₀ hTpos).mp hx |>.trans_eq (by ring)
  have hrange : a₀ * T ^ (1 - δ) ≤ (T - T ^ (1 - δ)) / 4 := by
    have h := mul_le_mul_of_nonneg_right ha₀.le hτpos.le
    nlinarith only [h, hsmall', hτpos]
  have hs : 0 < T ^ (1 - b) := Real.rpow_pos_of_pos hTpos _
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
    (T ^ (1 - δ)).toNNReal (by rwa [hτcast]) hnorm (by rwa [hτcast]) ν z
    (T - T ^ (1 - δ)) (T ^ (1 - b)) hprop hs (by rwa [hτcast])
  simp only [hτcast] at h
  have ha := habsorb T ((T - T ^ (1 - δ)) / 4) (T ^ (1 - δ)) ‖ζ‖
    (T ^ (1 - b)) hTpos (by linarith) (by linarith) (norm_nonneg _) hs.le
  have he : T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) * T ^ (1 - b) =
      T ^ (-(1 / 2 + (d : ℝ) / 4) - b) := by
    rw [← Real.rpow_add hTpos]
    congr 1
    ring
  have hprofile : B * Real.exp (Bp * ‖ζ‖ ^ 2 * T ^ (1 - δ)) *
      ((T - T ^ (1 - δ)) / 4)⁻¹ *
        (((T - T ^ (1 - δ)) / 4) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * ((T - T ^ (1 - δ)) / 4) ^ (-(d : ℝ) / 4)) * T ^ (1 - b) ≤
      C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b) := by
    simpa only [mul_assoc, he, neg_div] using! ha
  have hexp : Real.exp (sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * (T - T ^ (1 - δ))) ≤
      Real.exp (S * ‖ζ‖ ^ 2 * T) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ S * ‖z‖ ^ 2 * (T - T ^ (1 - δ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) hprop.le
      _ ≤ S * ‖ζ‖ ^ 2 * T := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (abs_nonneg _)
        · linarith
        · exact hprop.le
        · positivity
  have hbound := mul_le_mul hexp hprofile (by positivity)
    (Real.exp_pos _).le
  refine h.trans (le_trans (by convert hbound using 1; ring) ?_)
  rw [show Real.exp (S * ‖ζ‖ ^ 2 * T) *
      (C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b)) =
      C * Real.exp ((C + S) * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - b) by
        rw [show (C + S) * ‖ζ‖ ^ 2 * T =
          C * ‖ζ‖ ^ 2 * T + S * ‖ζ‖ ^ 2 * T by ring, Real.exp_add]
        ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _))
      (Real.exp_pos _).le) (Real.rpow_nonneg hTpos.le _)


/-- Stationary Schwartz averaging commutes with actual spatial translations. -/
theorem stationarySchwartzAverage_translation (Q : EnvironmentLaw d Λ r)
    (ψ : SchwartzMap (Vec d) ℂ) (a : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q ψ (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a (stationarySchwartzAverage Q ψ f) := by
  unfold stationarySchwartzAverage
  change _ = (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap
    (∫ x : Vec d, ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  rw [← (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap.integral_comp_comm
    (integrable_stationarySchwartzAverage_integrand Q ψ f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [map_smul]
    change ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
    rw [← complexTranslation_add, ← complexTranslation_add, add_comm x a]

/-- A Schwartz average preserves any existing strong horizontal derivative. -/
theorem horizontalDerivative_stationarySchwartzAverage
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f) (stationarySchwartzAverage Q ψ g) := by
  let A := stationarySchwartzAverageCLM Q ψ
  have h := (A.continuous.tendsto g).comp hf
  change Tendsto (fun t : ℝ => A ((t : ℂ)⁻¹ •
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (A g)) at h
  unfold HasComplexHorizontalDerivative
  simpa only [map_smul, map_sub, A, stationarySchwartzAverageCLM_apply,
    stationarySchwartzAverage_translation] using h

/-- Spatial integration by parts identifies the derivative kernel on an existing horizontal jet. -/
theorem stationarySchwartzAverage_horizontalDerivative
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    stationarySchwartzAverage Q ψ g =
      stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  have hg (x : Vec d) : HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
    have hd := (((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hf.hasDerivAt_orbit 0)
    simp only [zero_smul, complexTranslation_zero] at hd
    change HasDerivAt (fun t : ℝ => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f))
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) 0 at hd
    simpa only [HasLineDerivAt, ← complexTranslation_add] using! hd
  have hk (x : Vec d) : HasLineDerivAt ℝ (fun y => ψ (-y)) (-D (-x)) x (unitVector j) := by
    convert ((ψ.hasFDerivAt (-x)).comp x ((hasFDerivAt_id x).neg)).hasLineDerivAt (unitVector j) using 1 <;>
      (try simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]) <;> rfl
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (by simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, Pi.neg_apply] using! (integrable_stationarySchwartzAverage_integrand Q D f).neg)
    (integrable_stationarySchwartzAverage_integrand Q ψ g)
    (integrable_stationarySchwartzAverage_integrand Q ψ f) (fun x _ => hk x) (fun x _ => hg x)
  simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, integral_neg, neg_neg, stationarySchwartzAverage, D] using! hi

/-- Every stationary Schwartz average has the literal differentiated-kernel horizontal derivative. -/
theorem stationarySchwartzAverage_hasHorizontalDerivative
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f)
      (stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f) := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  let S := {u : Lp ℂ 2 (reducedLaw Q) |
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ u) (stationarySchwartzAverage Q D u)}
  have hclosed : IsClosed S :=
    (isClosed_complexHorizontalDerivative_graph (reducedLaw Q) (reducedLaw_stationary Q) j).preimage
      ((stationarySchwartzAverageCLM Q ψ).continuous.prodMk (stationarySchwartzAverageCLM Q D).continuous)
  have hsub : {u | IsComplexHorizontallySmooth Q u} ⊆ S := by
    intro u hu
    obtain ⟨J, hJ0, hJ⟩ := hu
    have hjet : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j u (J [j]) := by
      simpa only [hJ0] using! hJ [] j
    have he := stationarySchwartzAverage_horizontalDerivative Q j ψ hjet
    change HasComplexHorizontalDerivative _ _ _ _ _
    rw [← he]
    exact horizontalDerivative_stationarySchwartzAverage Q j ψ hjet
  exact hclosed.closure_subset (closure_mono hsub (dense_complexHorizontallySmooth Q f))

/-- The actual complex-force kernel at arbitrary positive time as a Schwartz test. -/
noncomputable def positiveTimeGaussianSchwartz (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) : SchwartzMap (Vec d) ℂ :=
  let c := Real.sqrt s
  let L := (LinearEquiv.smulOfNeZero (M := Vec d) ℝ c⁻¹
    (inv_ne_zero (Real.sqrt_pos.mpr hs).ne')).toContinuousLinearEquiv
  (((c ^ d)⁻¹ : ℝ) : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L
    (homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl (ζ * (c : ℂ)))

/-- The Schwartz representation evaluates to the literal anisotropic complex-force kernel. -/
theorem positiveTimeGaussianSchwartz_apply (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    positiveTimeGaussianSchwartz Q i s hs ζ x = homogenizedGaussianKernel Q i s hs ζ x := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  change (((c ^ d)⁻¹ : ℝ) : ℂ) *
    homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl (ζ * (c : ℂ)) (c⁻¹ • x) = _
  have he := homogenizedGaussianKernel_scale Q i c 1 hc zero_lt_one ζ (c⁻¹ • x)
  simpa only [mul_one, hcs, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    homogenizedGaussianSchwartz_apply] using he.symm

/-- The backwards Schwartz kernel represents the actual forward stationary average. -/
theorem stationarySchwartzAverage_positiveTimeGaussian (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q (positiveTimeGaussianSchwartz Q i s hs (-ζ)) f =
      homogeneousAverage Q i s hs ζ f := by
  unfold stationarySchwartzAverage homogeneousAverage
  simp_rw [positiveTimeGaussianSchwartz_apply, homogenizedGaussianKernel_neg_force, neg_neg]

/-- Every two-direction homogeneous derivative average is the actual second horizontal derivative. -/
theorem homogeneousAverage_hasHorizontalJet_two
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 2 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 1)
        (homogeneousAverage Q i s hs ζ f) g ∧
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 0) g
        (homogeneousDerivativeAverage Q i s hs ζ 2 dirs f) := by
  let K := positiveTimeGaussianSchwartz Q i s hs (-ζ)
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector (dirs 1))).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  refine ⟨stationarySchwartzAverage Q D f, ?_, ?_⟩
  · have h := stationarySchwartzAverage_hasHorizontalDerivative Q (dirs 1) K f
    rwa [stationarySchwartzAverage_positiveTimeGaussian] at h
  · have h := stationarySchwartzAverage_hasHorizontalDerivative Q (dirs 0) D f
    convert h using 1
    unfold homogeneousDerivativeAverage stationarySchwartzAverage
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    dsimp only
    congr 1
    have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs (-ζ) :=
      funext (positiveTimeGaussianSchwartz_apply Q i s hs (-ζ))
    rw [← he, ← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv (f := K)]
    simp only [LineDeriv.iteratedLineDerivOp_succ_left, LineDeriv.iteratedLineDerivOp_zero]
    rfl

/-- Complex-force Hessians retain a half-time unforced differentiated average. -/
theorem homogeneousDerivativeAverage_two_half_split {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (dirs : Fin 2 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs ζ 2 dirs f =
      homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 2 dirs f) := by
  obtain ⟨g, hg, hg'⟩ := homogeneousAverage_hasHorizontalJet_two Q ⟨0, by omega⟩ s hs ζ dirs f
  obtain ⟨h, hh, hh'⟩ := homogeneousAverage_hasHorizontalJet_two Q ⟨0, by omega⟩
    (s / 2) (half_pos hs) 0 dirs f
  have hfirst := hh.homogeneousAverage ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
  have he : g = homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ) h := by
    apply hg.unique
    change HasComplexHorizontalDerivative _ _ _
      (homogeneousAverage Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
        (gaussianAverage hd Q (s / 2) (half_pos hs) f)) _ at hfirst
    rwa [← homogeneousAverage_half_split hd Q s hs ζ f] at hfirst
  rw [he] at hg'
  have hsecond := hh'.homogeneousAverage ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * ζ)
  have hfinal := hg'.unique hsecond
  simpa only [homogeneousDerivativeAverage, neg_zero, gaussianDerivativeAverage] using! hfinal

/-- Scalar smoothing yields complex-force Hessian decay with an explicit drift exponential. -/
theorem homogeneous_hessian_of_scalar
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ a₀ η C Cp t₀ : ℝ,
      0 < a₀ ∧ a₀ < 1 ∧ 0 < η ∧ 0 < C ∧ 0 < Cp ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η → ∀ ν : EndpointIndex d,
    ∀ (z : ℂ) (dirs : Fin 2 → Fin d) (s : ℝ), 4 * a₀ * (t : ℝ) ≤ s →
    ∀ hs : 0 < s,
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ s hs z 2 dirs
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤
        Real.exp (sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * s) *
          (C * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) * (s / 2) ^ (-1 : ℝ) *
            ((s / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * (s / 2) ^ (-(d : ℝ) / 4))) := by
  obtain ⟨a₀, η, C, Cp, t₀, ha₀, ha₀', hη, hC, hCp, ht₀, hh⟩ :=
    real_homogeneous_hessian_of_scalar hscalar d hd D
  refine ⟨a₀, η, C, Cp, t₀, ha₀, ha₀', hη, hC, hCp, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν z dirs s hst hs
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ hwindow ν 0 dirs
    (s / 2) (by linarith) (half_pos hs)
  rw [norm_homogeneousDerivativeAverage_real_force hd] at h
  rw [homogeneousDerivativeAverage_two_half_split hd Q s hs z dirs]
  have he : sourceReducedBound D.ellipticity * ‖2 * z‖ ^ 2 * (s / 2) / 2 =
      sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * s := by
    rw [norm_mul]
    norm_num
    ring
  have hnorm := (homogeneousAverageCLM Q ⟨0, by omega⟩ (s / 2) (half_pos hs) (2 * z)).le_opNorm
    (gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) 2 dirs
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t))
  refine hnorm.trans ?_
  apply mul_le_mul
  · simpa only [he] using! norm_homogeneousAverageCLM_le Q ⟨0, by omega⟩
      (s / 2) (half_pos hs) (2 * z)
  · exact h
  · exact norm_nonneg _
  · exact (Real.exp_pos _).le

/-- Terminal-time Hessian decay for all propagation forces of at most the endpoint force norm. -/
theorem homogeneous_hessian_in_source_window
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) (C₀ : ℝ) :
    ∃ C T₀ : ℝ, 0 < C ∧ 2 ≤ T₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ T : ℝ, ∀ hT : 1 < T, T₀ ≤ T → ∀ ζ : ℂ,
      (‖ζ‖ * Real.sqrt T ≤ 2 ∨ ∃ lam : ℝ, ζ = (lam : ℂ) ∧
        |lam| * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d) (z : ℂ),
      ‖z‖ ≤ ‖ζ‖ → ∀ dirs : Fin 2 → Fin d,
      let τ := T ^ (1 - δ)
      let ht : 0 < T - τ := by
        have := Real.rpow_lt_self_of_one_lt hT (show 1 - δ < 1 by linarith)
        linarith
      ‖homogeneousDerivativeAverage Q ⟨0, by omega⟩ (T - τ) ht z 2 dirs
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal)‖ ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) := by
  obtain ⟨a₀, η, B, Bp, t₀, _, ha₀, hη, hB, hBp, ht₀, hh⟩ :=
    homogeneous_hessian_of_scalar hscalar d hd D
  obtain ⟨C, hC, habsorb⟩ := exists_comparable_derivative_absorption_constant
    hB hBp (by positivity : 0 ≤ (d : ℝ) / 4)
  obtain ⟨T₀, hT₀, hthreshold⟩ := exists_mesoscopic_scalar_threshold hη hδ hδ' C₀ t₀
  obtain ⟨T₁, _, hsmalltime⟩ := exists_smoothing_threshold hδ
  let S := |sourceReducedBound D.ellipticity|
  refine ⟨C + S, max T₀ T₁, by positivity, hT₀.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hTT ζ hζ P Pdag hP hPdag ν z hz dirs
  dsimp only
  have hTpos : 0 < T := by linarith
  have hτpos : 0 < T ^ (1 - δ) := Real.rpow_pos_of_pos hTpos _
  have hτcast : (Real.toNNReal (T ^ (1 - δ)) : ℝ) = T ^ (1 - δ) :=
    Real.coe_toNNReal _ hτpos.le
  obtain ⟨htime, hnorm, hwindow, hsmall⟩ := hthreshold T ((le_max_left _ _).trans hTT) ζ hζ
  have hprop : 0 < T - T ^ (1 - δ) := by linarith
  have hsmall' : T ^ (1 - δ) ≤ T / 16 := by
    have hx := hsmalltime T ((le_max_right _ _).trans hTT)
    rw [← smoothing_ratio hTpos] at hx
    exact (div_le_iff₀ hTpos).mp hx |>.trans_eq (by ring)
  have hrange : 4 * a₀ * T ^ (1 - δ) ≤ T - T ^ (1 - δ) := by
    have h := mul_le_mul_of_nonneg_right ha₀.le hτpos.le
    nlinarith only [h, hsmall', hτpos]
  have h := hh Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
    (T ^ (1 - δ)).toNNReal (by rwa [hτcast]) hnorm (by rwa [hτcast]) ν z dirs
    (T - T ^ (1 - δ)) (by rwa [hτcast]) hprop
  simp only [hτcast] at h
  have ha := habsorb T ((T - T ^ (1 - δ)) / 2) (T ^ (1 - δ)) ‖ζ‖
    1 hTpos (by linarith) (by linarith) (norm_nonneg _) zero_le_one
  have hi : ((T - T ^ (1 - δ)) / 2) ^ (-1 : ℝ) = ((T - T ^ (1 - δ)) / 2)⁻¹ :=
    Real.rpow_neg_one _
  have hprofile : B * Real.exp (Bp * ‖ζ‖ ^ 2 * T ^ (1 - δ)) *
      ((T - T ^ (1 - δ)) / 2) ^ (-1 : ℝ) *
        (((T - T ^ (1 - δ)) / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * ((T - T ^ (1 - δ)) / 2) ^ (-(d : ℝ) / 4)) ≤
      C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) := by
    simpa only [mul_one, hi, neg_div] using! ha
  have hexp : Real.exp (sourceReducedBound D.ellipticity * ‖z‖ ^ 2 * (T - T ^ (1 - δ))) ≤
      Real.exp (S * ‖ζ‖ ^ 2 * T) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ S * ‖z‖ ^ 2 * (T - T ^ (1 - δ)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _)) hprop.le
      _ ≤ S * ‖ζ‖ ^ 2 * T := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (abs_nonneg _)
        · linarith
        · exact hprop.le
        · positivity
  have hbound := mul_le_mul hexp hprofile (by positivity) (Real.exp_pos _).le
  refine h.trans (hbound.trans ?_)
  rw [show Real.exp (S * ‖ζ‖ ^ 2 * T) *
      (C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1)) =
      C * Real.exp ((C + S) * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - 1) by
        rw [show (C + S) * ‖ζ‖ ^ 2 * T =
          C * ‖ζ‖ ^ 2 * T + S * ‖ζ‖ ^ 2 * T by ring, Real.exp_add]
        ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg _))
      (Real.exp_pos _).le) (Real.rpow_nonneg hTpos.le _)

end EinsteinFull.Blueprint.LateUnsmoothing

namespace EinsteinFull.Blueprint.LateUnsmoothing
open EinsteinRelation

/-- Enlarge only the exponential constant in a nonnegative error profile. -/
theorem error_exponential_le {A C x y : ℝ} (hA : 0 ≤ A) (hAC : A ≤ C)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    A * Real.exp (A * x) * y ≤ A * Real.exp (C * x) * y := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAC hx)) hA) hy

/-- Enlarge the coefficient and exponential constant of an error profile together. -/
theorem error_constant_le {A C x y : ℝ} (hA : 0 ≤ A) (hAC : A ≤ C)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    A * Real.exp (A * x) * y ≤ C * Real.exp (C * x) * y := by
  exact (error_exponential_le hA hAC hx hy).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le) hy)

/-- Both endpoint drift signs preserve the exact complex force norm. -/
theorem norm_endpoint_signed_force {d : ℕ} (ν : EndpointIndex d) (ζ : ℂ) :
    ‖(endpointDriftSign ν : ℂ) * ζ‖ = ‖ζ‖ := by
  rcases ν with j | b
  · simp [endpointDriftSign]
  · cases b <;> simp [endpointDriftSign]
end EinsteinFull.Blueprint.LateUnsmoothing

namespace EinsteinFull.Blueprint
open EinsteinRelation LateUnsmoothing

/-- The exact late-propagation unsmoothing contract follows from its three graph parents. -/
theorem node_l_u3A_late_u2D_propagation_u23_unsmoothing_of_deps
    (hsmoothed : node_l_u3A_late_u2D_propagation_u23_smoothed_u2D_duhamelStmt)
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (hscalar : node_p_u3A_scalarStmt) :
    node_l_u3A_late_u2D_propagation_u23_unsmoothingStmt := by
  intro d hd D
  obtain ⟨ε, η, L, hε, _, hL, hm⟩ := hsmoothed d hd D
  obtain ⟨α, hα, hu⟩ := endpoint_unsmoothing_in_source_window hholder hscalar d hd D
  refine ⟨ε, α, hε, hα, ?_⟩
  intro δ hδ hδ'
  have hhL : 0 < 1 / 2 + (d : ℝ) / 4 + L := by positivity
  obtain ⟨b, hb, hb', hbound⟩ := exists_smoothing_exponent hε hδ' hhL
  refine ⟨b, hb, hb', ?_⟩
  intro ρ _ hρε hρα hρb C₀ hC₀
  obtain ⟨CU, TU, hCU, hTU, hu⟩ := hu b hb C₀
  obtain ⟨CH, TH, hCH, hTH, hh⟩ := homogeneous_hessian_in_source_window hscalar d hd D δ hδ hδ' C₀
  obtain ⟨CV, TV, hCV, hTV, hv⟩ :=
    homogeneous_unsmoothing_in_source_window hscalar d hd D δ hδ hδ' b C₀
  obtain ⟨CM, TM, hCM, hTM, hm⟩ := hm δ hδ hδ' b hb hb' hbound C₀ hC₀
  let C := CU + CH + CV + CM
  let T₀ := max TU (max TH (max TV TM))
  have hCUC : CU ≤ C := by dsimp [C]; linarith
  have hCHC : CH ≤ C := by dsimp [C]; linarith
  have hCVC : CV ≤ C := by dsimp [C]; linarith
  have hCMC : CM ≤ C := by dsimp [C]; linarith
  refine ⟨C, T₀, by dsimp [C]; positivity, hTU.trans (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ T hT hTT ζ hζ P Pdag hP hPdag ν
  have hUT : TU ≤ T := (le_max_left _ _).trans hTT
  have hHT : TH ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hTT)
  have hVT : TV ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hTT))
  have hMT : TM ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hTT))
  have hu := hu Q hQ β a μ hβ ha hμ T hT hUT ζ hζ P Pdag hP hPdag ν
  have hv := hv Q hQ β a μ hβ ha hμ T hT hVT ζ hζ P Pdag hP hPdag ν
    ((endpointDriftSign ν : ℂ) * ζ) (norm_endpoint_signed_force ν ζ).le
  have hh := hh Q hQ β a μ hβ ha hμ T hT hHT ζ hζ P Pdag hP hPdag ν
    ((endpointDriftSign ν : ℂ) * ζ) (norm_endpoint_signed_force ν ζ).le
  have hm := (hm Q hQ β a μ hβ ha hμ T hT hMT ζ hζ P Pdag hP hPdag ν).2.2
  dsimp only at hu hv hh hm ⊢
  have hTpos : 0 < T := by linarith
  have hx : 0 ≤ ‖ζ‖ ^ 2 * T := mul_nonneg (sq_nonneg _) hTpos.le
  have hpow (g : ℝ) : 0 ≤ T ^ (-(1 / 2 + (d : ℝ) / 4) - g) :=
    Real.rpow_nonneg hTpos.le _
  have henlarge (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (g : ℝ) :
      A * Real.exp (A * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - g) ≤
      C * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - g) := by
    simpa only [mul_assoc] using! error_constant_le hA hAC hx (hpow g)
  refine ⟨hu.trans (henlarge CU hCU.le hCUC _), fun dirs =>
    (hh dirs).trans (henlarge CH hCH.le hCHC _),
    hv.trans (henlarge CV hCV.le hCVC _), ?_⟩
  have hgain := mul_le_mul_of_nonneg_left
    (smoothed_duhamel_gain_le hT.le hhL hbound hρε)
    (mul_nonneg hCM.le (Real.exp_pos (CM * ‖ζ‖ ^ 2 * T)).le)
  simp only [← mul_assoc] at hgain
  have hm' := hm.trans hgain
  have hexpenlarge (A : ℝ) (hA : 0 ≤ A) (hAC : A ≤ C) (g : ℝ) :
      A * Real.exp (A * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - g) ≤
      A * Real.exp (C * ‖ζ‖ ^ 2 * T) * T ^ (-(1 / 2 + (d : ℝ) / 4) - g) := by
    simpa only [mul_assoc] using! error_exponential_le hA hAC hx (hpow g)
  have hu' := hu.trans (hexpenlarge CU hCU.le hCUC _)
  have hv' := hv.trans (hexpenlarge CV hCV.le hCVC _)
  have hm'' := hm'.trans (hexpenlarge CM hCM.le hCMC _)
  have hsum := sum_errors_le (h := 1 / 2 + (d : ℝ) / 4)
    hT.le (Real.exp_pos (C * ‖ζ‖ ^ 2 * T)).le hCU.le hCM.le hCV.le
    hρα.le (le_refl ρ) hρb.le
  have hcoeff : CU + CM + CV ≤ C := by dsimp [C]; linarith
  exact (comparison_le_three_errors hd Q _ _ _ _).trans
    ((add_le_add (add_le_add hu' hm'') hv').trans (hsum.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le) (hpow ρ))))
end EinsteinFull.Blueprint
