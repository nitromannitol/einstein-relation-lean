import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Blueprint.G3.node_p_u3A_profile_u23_static_u2D_comparison
import EinsteinFull.Blueprint.G3.node_e_u3A_fourier

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation MeasureTheory Filter
open scoped NNReal Topology

private abbrev profileTestValues {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : ℂ) :=
  let first : Fin d := ⟨0, by omega⟩
  let kernel := fun (w : ℂ) => homogenizedGaussianKernel Q first (1 / 2) (by norm_num) w
  let kernelDeriv := fun (w : ℂ) (j : Fin d) (x : Vec d) =>
    iteratedFDeriv ℝ 1 (kernel w) (-x) (fun _ => unitVector j)
  fun (ν : EndpointIndex d) (x : Vec d) (a : JointObservationIndex d) =>
    match ν, a with
    | .inr true, .inl (j,k) => if k = first then (1 / 2 : ℂ) * kernelDeriv z j x else 0
    | .inl i, .inl (j,k) => if k = i then
        (1 / 2 : ℂ) * kernelDeriv (-z) j x +
          (if j = first then z * kernel z x else 0) else 0
    | .inr false, .inr () => z * kernel z x
    | _, _ => 0

private lemma profile_covariances (hfourier : node_e_u3A_fourierStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (covariance selected : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ)
    (hZ : IsJointObservation Q Z) (hc : IsJointCovariance Q Z covariance)
    (hs : IsJointCovariance Q Z selected) (z : ℂ)
    (F : EndpointIndex d → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (hF : ∀ ν x a, F ν x a = profileTestValues hd Q z ν x a) :
    (∀ i : Fin d, (∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
      F (.inr true) x a * (selected a b : ℂ) * F (.inl i) x b) =
        velocityGaussianProfile hd Q covariance i z) ∧
    (∫ x : Vec d, ∑ a : JointObservationIndex d, ∑ b : JointObservationIndex d,
      F (.inr true) x a * (selected a b : ℂ) * F (.inr false) x b) =
        clockGaussianProfile hd Q covariance z := by
  have he (ν : EndpointIndex d) := tendsto_nhds_unique
    (hs (F (.inr true)) (F ν)) (hc (F (.inr true)) (F ν))
  have hf := hfourier d hd D Q hQ Z covariance hZ hc z
  dsimp only at hf
  constructor
  · intro i
    rw [he (.inl i)]
    simp_rw [hF]
    exact (hf.1 i).2
  · rw [he (.inr false)]
    simp_rw [hF]
    exact hf.2.2.1

private lemma sqrt_power (t p : ℝ) (ht : 0 ≤ t) :
    Real.sqrt t ^ p = t ^ (p / 2) :=
  (Real.rpow_div_two_eq_sqrt p ht).symm

/-- Assemble the exact Gaussian-profile reduction at the two prescribed force windows. -/
theorem node_p_u3A_profile_of_deps
    (hstatic : node_p_u3A_profile_u23_static_u2D_comparisonStmt)
    (hfourier : node_e_u3A_fourierStmt) : node_p_u3A_profileStmt := by
  intro d hd D
  obtain ⟨εcov, εbridge, C, hεcov, hεbridge, hC, hw⟩ :=
    hstatic d hd D (2 * d + 11) (by omega)
  let ε := min εcov εbridge
  have hε : 0 < ε := lt_min hεcov hεbridge
  refine ⟨ε / 2, C, half_pos hε, hC, ?_, ?_⟩
  · intro Q hQ β a μ Z covariance hβ ha hμ hZ hc
    refine ⟨?_, ?_, ?_⟩
    · intro i z
      simp only [velocityGaussianProfile, neg_sq]
    · intro z
      simp only [clockGaussianProfile, neg_sq]
    · intro t ht ζ hζ P hP i
      obtain ⟨Cw, R₀, _hCw, _hR₀, hh⟩ := hw 1 zero_lt_one
      obtain ⟨selected, hh⟩ := hh Q hQ
      obtain ⟨hs, hh⟩ := hh Z hZ
      obtain ⟨F, hF, _hFN, hh⟩ := hh (ζ * (Real.sqrt (t : ℝ) : ℂ))
      have hR : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hR2 : 2 ≤ Real.sqrt (t : ℝ) := by
        nlinarith [Real.sq_sqrt t.coe_nonneg]
      have hdiv : ζ * (Real.sqrt (t : ℝ) : ℂ) / (Real.sqrt (t : ℝ) : ℂ) = ζ :=
        mul_div_cancel_right₀ ζ (Complex.ofReal_ne_zero.mpr hR.ne')
      have htime : ((Real.sqrt (t : ℝ) ^ 2).toNNReal) = t := by
        rw [Real.sq_sqrt t.coe_nonneg, Real.toNNReal_coe]
      have hcovs := profile_covariances hfourier d hd D Q hQ Z covariance selected hZ hc hs
        (ζ * (Real.sqrt (t : ℝ) : ℂ)) F hF
      obtain ⟨_hm, _hc, hh⟩ := hh (Real.sqrt (t : ℝ)) hR hR2
      dsimp only at hh
      rw [hdiv] at hh
      have he := (hh β a μ hQ hβ ha hμ P hP i).1 (by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR] using hζ)
      rw [htime, hcovs.1 i, hcovs.2] at he
      have hp : Real.sqrt (t : ℝ) ^ (-(d : ℝ) - 2) =
          (t : ℝ) ^ (-1 - (d : ℝ) / 2) := by
        rw [sqrt_power _ _ t.coe_nonneg]
        congr 1
        ring
      have hpe : Real.sqrt (t : ℝ) ^ (-(d : ℝ) - 2 - ε) =
          (t : ℝ) ^ (-1 - (d : ℝ) / 2 - ε / 2) := by
        rw [sqrt_power _ _ t.coe_nonneg]
        congr 1
        ring
      rw [hp, hpe] at he
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        mul_assoc, mul_comm, mul_left_comm] using he
  · intro C₀ hC₀
    obtain ⟨Cw, R₀, hCw, hR₀, hh⟩ := hw C₀ hC₀
    refine ⟨Cw, R₀ ^ 2, hCw, ?_, ?_⟩
    · nlinarith
    · intro Q hQ β a μ Z covariance hβ ha hμ hZ hc t ht lam hlam P hP i
      obtain ⟨selected, hh⟩ := hh Q hQ
      obtain ⟨hs, hh⟩ := hh Z hZ
      obtain ⟨F, hF, _hFN, hh⟩ := hh ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ))
      have hR : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr (by nlinarith)
      have hR0 : R₀ ≤ Real.sqrt (t : ℝ) := by
        nlinarith [Real.sq_sqrt t.coe_nonneg]
      have hdiv : (lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ) / (Real.sqrt (t : ℝ) : ℂ) = lam :=
        mul_div_cancel_right₀ (lam : ℂ) (Complex.ofReal_ne_zero.mpr hR.ne')
      have htime : ((Real.sqrt (t : ℝ) ^ 2).toNNReal) = t := by
        rw [Real.sq_sqrt t.coe_nonneg, Real.toNNReal_coe]
      have hcovs := profile_covariances hfourier d hd D Q hQ Z covariance selected hZ hc hs
        ((lam : ℂ) * (Real.sqrt (t : ℝ) : ℂ)) F hF
      obtain ⟨_hm, _hc, hh⟩ := hh (Real.sqrt (t : ℝ)) hR (hR₀.trans hR0)
      dsimp only at hh
      rw [hdiv] at hh
      have he := (hh β a μ hQ hβ ha hμ P hP i).2 hR0 ⟨lam * Real.sqrt (t : ℝ), by
        push_cast
        rfl, by simpa only [abs_mul, abs_of_pos hR] using hlam⟩
      rw [htime, hcovs.1 i, hcovs.2] at he
      have hp : Real.sqrt (t : ℝ) ^ (-(d : ℝ) - 2) =
          (t : ℝ) ^ (-1 - (d : ℝ) / 2) := by
        rw [sqrt_power _ _ t.coe_nonneg]
        congr 1
        ring
      have hpe : Real.sqrt (t : ℝ) ^ (-(d : ℝ) - 2 - ε) =
          (t : ℝ) ^ (-1 - (d : ℝ) / 2 - ε / 2) := by
        rw [sqrt_power _ _ t.coe_nonneg]
        congr 1
        ring
      rw [hp, hpe] at he
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        mul_assoc, mul_comm, mul_left_comm] using he

end EinsteinFull.Blueprint
