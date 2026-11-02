import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Calculus.ComplexZeroForceFluxSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinRelation.Clock.CentredClockField
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual positive-time gradient used in the gradient-limit node is
coordinatewise Bochner integrable on every finite horizon, including zero. -/
theorem finiteXi_gradient_integrableOn_Icc
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (j : Fin d) :
    IntegrableOn (fun s : ℝ => hP.gradientOrbit f s j) (Icc (0 : ℝ) (t : ℝ)) :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
    (hP.integrableOn_gradientOrbit f t)

/-- Half-time smoothing acts on the centered actual endpoint. Constants are
annihilated by the horizontal gradient, so no drift mean identity is needed. -/
theorem finiteXi_gradient_half_time
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 0 < t) :
    hP.forcedGradient t ht (P t f) =
      hP.forcedGradient t ht (centeredComplexLp Q (P t f)) := by
  apply WithLp.ofLp_injective 2
  apply (hP.forcedGradient_spec t ht (P t f)).centered.unique
  simpa only [hP.centered_apply] using
    hP.forcedGradient_centered_spec t ht (centeredComplexLp Q (P t f))

/-- Euclidean stationary-L2 gradient control by the centered half-time orbit.
The coefficient constant is structural and no desired decay is assumed. -/
theorem finiteXi_gradient_double_time_bound
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 0 < t) :
    Real.sqrt (∑ j : Fin d, ‖hP.gradientOrbit f ((t + t : ℝ≥0) : ℝ) j‖ ^ 2) ≤
      (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) / Real.sqrt (t : ℝ)) *
        ‖centeredComplexLp Q (P t f)‖ := by
  have h2 : (0 : ℝ) < ((t + t : ℝ≥0) : ℝ) := by positivity
  rw [← PiLp.norm_eq_of_L2]
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos h2, Real.toNNReal_coe]
  rw [hP.forcedGradient_add t ht t, ContinuousLinearMap.comp_apply,
    finiteXi_gradient_half_time hP f t ht]
  apply ((hP.forcedGradient t ht).le_opNorm _).trans
  have hb := hP.norm_forcedGradient_le t ht
  simp only [complexForceShift, norm_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero, mul_one] at hb
  exact mul_le_mul_of_nonneg_right hb (norm_nonneg _)

private theorem coefficient_clock_observations
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∃ (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a ∧ IsReducedClockObservation Q μ := by
  letI := reducedLaw_probability Q
  have ha (j k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
      2 (reducedLaw Q) := (memLp_reduced_coefficient_complex Q j k).mono_exponent le_top
  have hm : MemLp (fun ω : FieldPair d => (ω.2 0 : ℂ)) 2 (reducedLaw Q) := by
    apply (memLp_top_of_bound
      (Complex.continuous_ofReal.comp Clock.continuous_clockAtOrigin).aestronglyMeasurable
      (sourceReducedBound Λ₀) ?_).mono_exponent le_top
    filter_upwards [Clock.ae_abs_clockAtOrigin_le Q] with ω hω
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hω
  exact ⟨fun j k => (ha j k).toLp _, hm.toLp _,
    fun j k => (ha j k).coeFn_toLp, hm.coeFn_toLp⟩

/-- The prescribed scalar dependency supplies actual centered unforced drift
endpoint decay, with its structural constant chosen before the law and datum. -/
theorem finiteXi_centered_drift_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
    ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) → ∀ j : Fin d,
      ‖centeredComplexLp Q (P t (β j))‖ ≤
        C * (t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  obtain ⟨a₀, η₀, ha₀, ha₁, hη, hs⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, hDp, ht₀, hCder, hs⟩ := hs 2 le_rfl
  refine ⟨C, hC, ?_⟩
  intro Q hQ β hβ P hP t ht j
  obtain ⟨a, μ, ha, hμ⟩ := coefficient_clock_observations Q
  have hb := (hs Q hQ β a μ hβ ha hμ 0 P
    (fun s => complexL2Transpose (reducedLaw Q) (P s)) hP
    (isComplexTransposeSemigroup_complexL2Transpose Q P)).1 t ht (by simp)
  have hj : (eLpNorm
      (velocityEndpoint Q ⟨0, by omega⟩ j 0 P β a t : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
      ∑ k : Fin d, (eLpNorm
        (velocityEndpoint Q ⟨0, by omega⟩ k 0 P β a t : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal := by
    exact Finset.single_le_sum (s := Finset.univ)
      (f := fun k : Fin d => (eLpNorm
        (velocityEndpoint Q ⟨0, by omega⟩ k 0 P β a t : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal)
      (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ j)
  have he := hb.2
  have hz₁ := ENNReal.toReal_nonneg (a := eLpNorm
    (transposeEndpoint Q ⟨0, by omega⟩
      (fun s => complexL2Transpose (reducedLaw Q) (P s)) β t : FieldPair d → ℂ)
    (ENNReal.ofReal 2) (reducedLaw Q))
  have hz₂ := ENNReal.toReal_nonneg (a := eLpNorm
    (clockEndpoint Q 0 P μ t : FieldPair d → ℂ) (ENNReal.ofReal 2) (reducedLaw Q))
  have he' : ‖centeredComplexLp Q (P t (β j))‖ =
      (eLpNorm (velocityEndpoint Q ⟨0, by omega⟩ j 0 P β a t : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal := by
    simp only [velocityEndpoint, zero_smul, add_zero, ENNReal.ofReal_ofNat, Lp.norm_def]
  rw [he']
  linarith only [hj, he, hz₁, hz₂]

/-- Structural integrable power decay for the actual drift gradient at doubled
time. The factor two is retained here to keep the semigroup factorization literal. -/
theorem finiteXi_gradient_doubled_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) → ∀ j : Fin d,
      Real.sqrt (∑ k : Fin d,
        ‖hP.gradientOrbit
          (β j) ((t + t : ℝ≥0) : ℝ) k‖ ^ 2) ≤
        C * (t : ℝ) ^ (-1 - (d : ℝ) / 4) := by
  obtain ⟨C, hC, hdec⟩ := finiteXi_centered_drift_decay hscalar d hd D
  let K := 2 * Real.sqrt (Real.exp (2 * D.ellipticity) * D.ellipticity)
  have hK : 0 < K := by
    dsimp [K]
    have hD := D.one_le_ellipticity
    positivity
  refine ⟨K * C, mul_pos hK hC, ?_⟩
  intro Q hQ β hβ P hP t ht j
  have htpos : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht
  have hb := finiteXi_gradient_double_time_bound hP (β j) t (by exact_mod_cast htpos)
  have hd' := hdec Q hQ β hβ P hP t ht j
  apply hb.trans
  calc
    _ ≤ (K / Real.sqrt (t : ℝ)) *
        (C * (t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4))) :=
      mul_le_mul_of_nonneg_left hd' (by positivity)
    _ = (K * C) * (t : ℝ) ^ (-1 - (d : ℝ) / 4) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg htpos.le]
      have he : (- (1 / 2 : ℝ)) + -(1 / 2 + (d : ℝ) / 4) =
          -1 - (d : ℝ) / 4 := by ring
      rw [← he, Real.rpow_add htpos]
      ring

/-- The doubled-time estimate gives a structural power majorant on the literal
real-time gradient orbit, for all times at least two. -/
theorem finiteXi_gradient_tail_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∀ r : ℝ, 2 ≤ r → ∀ j : Fin d,
      ‖hP.gradientOrbit (β j) r‖ ≤ C * r ^ (-1 - (d : ℝ) / 4) := by
  obtain ⟨C, hC, hdec⟩ := finiteXi_gradient_doubled_decay hscalar d hd D
  refine ⟨C * (1 / 2 : ℝ) ^ (-1 - (d : ℝ) / 4),
    mul_pos hC (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro Q hQ β hβ P hP r hr j
  let t : ℝ≥0 := r.toNNReal / 2
  have hrpos : 0 < r := by linarith
  have ht : (t : ℝ) = r / 2 := by simp only [t, NNReal.coe_div,
    Real.coe_toNNReal r hrpos.le, NNReal.coe_ofNat]
  have htr : ((t + t : ℝ≥0) : ℝ) = r := by rw [NNReal.coe_add, ht]; ring
  have hb := hdec Q hQ β hβ P hP t (by rw [ht]; linarith) j
  rw [htr, ← PiLp.norm_eq_of_L2, ht] at hb
  apply hb.trans_eq
  rw [div_eq_mul_inv, Real.mul_rpow hrpos.le (by norm_num : (0 : ℝ) ≤ 2⁻¹)]
  ring_nf

/-- The literal drift observation has a structural stationary L2 bound. -/
theorem finiteXi_drift_norm_bound
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (j : Fin d) :
    ‖β j‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
  letI := reducedLaw_probability Q
  have hD := D.one_le_ellipticity
  have hB : 0 ≤ (1 / 2 : ℝ) * d *
      reducedLipschitzConstant D.ellipticity := by
    unfold reducedLipschitzConstant
    positivity
  have hb := Lp.norm_le_of_ae_bound (f := β j) hB (by
    filter_upwards [hβ.ae_eq_cdiv j, ae_abs_cdiv_le_reduced Q j] with ω hω hbound
    rw [hω]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num :
      (0 : ℝ) < 1 / 2)]
    nlinarith only [hbound])
  simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one,
    Real.one_rpow, one_mul] using hb

/-- A uniform bound on the compact interval between one and two uses the
actual drift observation, without an additional local-regularity premise. -/
theorem finiteXi_gradient_compact_bound
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i 0 P) (r : ℝ) (hr : 1 ≤ r) (j : Fin d) :
    ‖hP.gradientOrbit (β j) r‖ ≤
      (2 * Real.sqrt (Real.exp (2 * D.ellipticity) * D.ellipticity)) *
        ((1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity) := by
  have hrpos : 0 < r := by linarith
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hrpos]
  have hb := hP.norm_forcedGradient_le r.toNNReal (Real.toNNReal_pos.mpr hrpos)
  simp only [complexForceShift, norm_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero, mul_one, Real.coe_toNNReal r hrpos.le] at hb
  have hs : 1 ≤ Real.sqrt r := by
    simpa using Real.sqrt_le_sqrt hr
  have hK : 0 ≤ 2 * Real.sqrt (Real.exp (2 * D.ellipticity) * D.ellipticity) := by
    positivity
  have hb' := hb.trans (div_le_self hK hs)
  exact ((hP.forcedGradient r.toNNReal (Real.toNNReal_pos.mpr hrpos)).le_opNorm _).trans
    (mul_le_mul hb' (finiteXi_drift_norm_bound D Q hQ β hβ j) (norm_nonneg _) hK)

/-- The gradient decay has the source's lower threshold one and a structural
constant chosen before the environment law. -/
theorem finiteXi_gradient_decay
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∀ r : ℝ, 1 ≤ r → ∀ j : Fin d,
      ‖hP.gradientOrbit (β j) r‖ ≤ C * r ^ (-1 - (d : ℝ) / 4) := by
  obtain ⟨C, hC, htail⟩ := finiteXi_gradient_tail_decay hscalar d hd D
  let B := (2 * Real.sqrt (Real.exp (2 * D.ellipticity) * D.ellipticity)) *
    ((1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity)
  have hD := D.one_le_ellipticity
  have hB : 0 ≤ B := by dsimp [B, reducedLipschitzConstant]; positivity
  let A := B / (2 : ℝ) ^ (-1 - (d : ℝ) / 4)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨C + A, by positivity, ?_⟩
  intro Q hQ β hβ P hP r hr j
  have hrpos : 0 < r := by linarith
  by_cases hr₂ : 2 ≤ r
  · exact (htail Q hQ β hβ P hP r hr₂ j).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + A) (Real.rpow_nonneg hrpos.le _))
  · have hb := finiteXi_gradient_compact_bound D Q hQ β hβ P hP r hr j
    have hp : (2 : ℝ) ^ (-1 - (d : ℝ) / 4) ≤ r ^ (-1 - (d : ℝ) / 4) :=
      Real.rpow_le_rpow_of_nonpos hrpos (le_of_not_ge hr₂) (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
    have hpow : (2 : ℝ) ^ (-1 - (d : ℝ) / 4) ≠ 0 :=
      (Real.rpow_pos_of_pos (by norm_num) _).ne'
    calc
      _ ≤ B := hb
      _ = A * (2 : ℝ) ^ (-1 - (d : ℝ) / 4) := by dsimp [A]; field_simp
      _ ≤ A * r ^ (-1 - (d : ℝ) / 4) := mul_le_mul_of_nonneg_left hp hA
      _ ≤ (C + A) * r ^ (-1 - (d : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hrpos.le _)

/-- Scalar decay and the actual finite-window smoothing producer yield the
full infinite-horizon coordinate Bochner integrability, including time zero. -/
theorem finiteXi_gradient_integrableOn_Ici
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P) (i j : Fin d) :
    IntegrableOn (fun r : ℝ => hP.gradientOrbit (β i) r j) (Ici 0) := by
  obtain ⟨C, _hC, hdec⟩ := finiteXi_gradient_tail_decay hscalar d hd D
  have he : -1 - (d : ℝ) / 4 < -1 := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hint : IntegrableOn (fun r : ℝ => hP.gradientOrbit (β i) r j) (Ioi 2) := by
    apply ((integrableOn_Ioi_rpow_of_lt he (by norm_num : (0 : ℝ) < 2)).const_mul C).mono'
    · have hc : ContinuousOn (fun r : ℝ => hP.gradientOrbit (β i) r j) (Ioi 2) :=
        (PiLp.proj (𝕜 := ℂ) 2 _ j).continuous.comp_continuousOn
          ((hP.continuousOn_gradientOrbit (β i)).mono (by
            intro r hr
            exact lt_trans (by norm_num : (0 : ℝ) < 2) hr))
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact (PiLp.norm_apply_le (hP.gradientOrbit (β i) r) j).trans
        (hdec Q hQ β hβ P hP r hr.le i)
  have hfin := finiteXi_gradient_integrableOn_Icc hP (β i) 2 j
  have hunion : Icc (0 : ℝ) 2 ∪ Ioi 2 = Ici 0 := by
    ext r
    simp only [mem_union, mem_Icc, mem_Ioi, mem_Ici]
    constructor
    · rintro (⟨h, _⟩ | h) <;> linarith
    · intro h
      by_cases h' : r ≤ 2
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr (lt_of_not_ge h')
  rw [← hunion, integrableOn_union]
  exact ⟨hfin, hint⟩

/-- Actual finite-time gradient integrals converge in stationary complex L2
in every dimension covered by the paper. No potential identification is used. -/
theorem finiteXi_gradient_integral_tendsto
    (hscalar : node_p_u3A_scalarStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P) (i j : Fin d) :
    Tendsto (fun τ : ℝ => ∫ r in Icc (0 : ℝ) τ, hP.gradientOrbit (β i) r j)
      atTop (𝓝 (∫ r in Ici (0 : ℝ), hP.gradientOrbit (β i) r j)) := by
  have hsets : (⋃ τ : ℝ, Icc (0 : ℝ) τ) = Ici 0 := by
    ext r
    simp only [mem_iUnion, mem_Icc, mem_Ici]
    exact ⟨fun ⟨_, h, _⟩ => h, fun h => ⟨r, h, le_rfl⟩⟩
  have ht := tendsto_setIntegral_of_monotone
    (f := fun r : ℝ => hP.gradientOrbit (β i) r j)
    (fun τ : ℝ => measurableSet_Icc (a := 0) (b := τ))
    (fun a b hab => Icc_subset_Icc_right hab)
    (hsets ▸ finiteXi_gradient_integrableOn_Ici hscalar d hd D Q hQ β hβ P hP i j)
  simpa only [hsets] using ht

/-- The actual unforced drift gradient, including its initial-time trace,
is integrable and has a stationary L2 integral limit. The two binders are
exactly the ordered graph dependencies. Positive-time witnesses come from
the local dependency and the initial trace from the adopted smooth orbit. -/
theorem node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limit_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (hlocal : node_l_u3A_forced_u2D_localStmt) :
    node_l_u3A_finite_u2D_xi_u23_gradient_u2D_limitStmt := by
  intro d hd D
  obtain ⟨C, hC, hdec⟩ := finiteXi_gradient_decay hscalar d hd D
  refine ⟨C, hC, ?_⟩
  intro Q hQ β hβ P hP
  obtain ⟨a, μ, ha, hμ⟩ := coefficient_clock_observations Q
  obtain ⟨α, Cdet, c, N, _hα, _hCdet, _hc, hl⟩ := hlocal d hd D
  obtain ⟨Cl, Cp, _hCl, _hCp, hl⟩ := hl 2 le_rfl
  have hexlocal (i : Fin d) : ∃ K : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P t (β i)) (K t) := by
    obtain ⟨K, V, hK, _hb, _hloc, _hpt⟩ := hl Q hQ β a μ hβ ha hμ 0 P
      (fun t => complexL2Transpose (reducedLaw Q) (P t)) hP
      (isComplexTransposeSemigroup_complexL2Transpose Q P) (.inl i)
    refine ⟨K, fun t ht => ?_⟩
    simpa only [uncenteredEndpoint, zero_smul, add_zero] using (hK t ht).2.1
  choose K hK using hexlocal
  have hex (i : Fin d) : ∃ H : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, Continuous (fun t => H t j)) ∧
      ∀ t, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t (β i)) (H t) := by
    obtain ⟨H, hc, hg⟩ := timeFlux_forward_continuous_gradient hβ ha hP i
    exact ⟨H, hc, by simpa only [zero_smul, add_zero] using hg⟩
  choose H _hHc hH using hex
  let G : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q) :=
    fun r i => if r = 0 then H i r else K i r
  have hG (r : ℝ≥0) (i : Fin d) :
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r (β i)) (G r i) := by
    by_cases hr : r = 0
    · simpa only [G, if_pos hr] using hH i r
    · simpa only [G, if_neg hr] using hK i r
        (NNReal.coe_pos.mpr (lt_of_le_of_ne (zero_le (a := r)) (Ne.symm hr)))
  have heq (r : ℝ) (hr : 0 < r) (i : Fin d) :
      G r.toNNReal i = fun j => hP.gradientOrbit (β i) r j :=
    (hG r.toNNReal i).unique (hP.gradientOrbit_spec (β i) hr)
  have heqae (s : Set ℝ) (hs : MeasurableSet s) (hs0 : s ⊆ Ici 0) (i j : Fin d) :
      (fun r : ℝ => G r.toNNReal i j) =ᵐ[volume.restrict s]
        (fun r : ℝ => hP.gradientOrbit (β i) r j) := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℝ)), ae_restrict_mem hs]
      with r hr hrs
    exact congrFun (heq r (lt_of_le_of_ne (hs0 hrs) (Ne.symm hr)) i) j
  refine ⟨G, hG, ?_, ?_⟩
  · intro r hr i
    have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one hr
    have he := heq (r : ℝ) hrpos i
    rw [Real.toNNReal_coe] at he
    rw [he, ← PiLp.norm_eq_of_L2]
    exact hdec Q hQ β hβ P hP (r : ℝ) hr i
  · intro i
    refine ⟨fun j => (finiteXi_gradient_integrableOn_Ici hscalar d hd D Q hQ β hβ P hP i j).congr
      (heqae (Ici 0) measurableSet_Ici Subset.rfl i j).symm, ?_⟩
    refine ⟨fun j => ∫ r in Ici (0 : ℝ), hP.gradientOrbit (β i) r j, ?_⟩
    intro j
    have hint (τ : ℝ) : (∫ r in Icc (0 : ℝ) τ, G r.toNNReal i j) =
        ∫ r in Icc (0 : ℝ) τ, hP.gradientOrbit (β i) r j :=
      integral_congr_ae (heqae (Icc 0 τ) measurableSet_Icc (fun _ h => h.1) i j)
    simp_rw [hint]
    exact finiteXi_gradient_integral_tendsto hscalar d hd D Q hQ β hβ P hP i j

end EinsteinFull.Blueprint
