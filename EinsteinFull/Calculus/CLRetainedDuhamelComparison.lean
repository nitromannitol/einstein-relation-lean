import EinsteinFull.Calculus.U7PhysicalDivergenceTails
import EinsteinFull.Calculus.SunaS4ForcedLocality
import EinsteinFull.Calculus.S5GaussianSupport
import EinsteinFull.Calculus.S1CovarianceL2Support
import EinsteinFull.Calculus.U4PhysicalQuantitativeC1
import EinsteinFull.Calculus.U8QuantitativeSobolev

/-! Retained-coefficient Duhamel comparison for `e:forced-locality`,
`paper/main.tex:715`. Two physical evolutions whose coefficients agree on a
ball are compared through the weak Duhamel identity. The test datum lies in
the inner half ball, so the transpose side has Gaussian gradient and value
tails on the coefficient defect; the other side contributes only its
integrated energy. Every statement is deterministic in the coefficient fields. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation Blueprint

/-- Half of a Gaussian factor absorbs the inverse square root of time. -/
theorem clr_inv_sqrt_exp_le {c ρ τ : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hτ : 0 < τ) :
    (Real.sqrt τ)⁻¹ * Real.exp (-(c * ρ ^ 2 / τ)) ≤ (Real.sqrt c * ρ)⁻¹ := by
  set X := c * ρ ^ 2 / τ with hXdef
  have hX : 0 < X := by positivity
  have hsX : Real.sqrt X = Real.sqrt c * ρ / Real.sqrt τ := by
    rw [hXdef, Real.sqrt_div' _ hτ.le, Real.sqrt_mul hc.le, Real.sqrt_sq hρ.le]
  have hle : Real.sqrt X ≤ Real.exp X := by
    have h1 := Real.add_one_le_exp X
    have h2 : Real.sqrt X ≤ 1 + X := by
      nlinarith [Real.sq_sqrt hX.le, Real.sqrt_nonneg X]
    linarith
  have hsXpos : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hτs : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  rw [Real.exp_neg]
  calc (Real.sqrt τ)⁻¹ * (Real.exp X)⁻¹ ≤ (Real.sqrt τ)⁻¹ * (Real.sqrt X)⁻¹ :=
        mul_le_mul_of_nonneg_left ((inv_le_inv₀ (Real.exp_pos X) hsXpos).mpr hle)
          (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (Real.sqrt c * ρ)⁻¹ := by
        rw [hsX]
        have : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
        field_simp

/-- A singular Gaussian tail at any time up to `T` is bounded by one
nonsingular envelope at time `T`. -/
theorem clr_tail_envelope {C c x ρ τ T R : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hx : 0 ≤ x)
    (hρ : 0 < ρ) (hτ : 0 < τ) (hτT : τ ≤ T) (hR : 0 ≤ R) :
    C * ((Real.sqrt τ)⁻¹ + x) * Real.exp (C * x ^ 2 * τ - c * ρ ^ 2 / τ) * R ≤
      C * ((Real.sqrt (c / 2) * ρ)⁻¹ + x) *
        Real.exp (C * x ^ 2 * T - (c / 2) * ρ ^ 2 / T) * R := by
  have hsplit : Real.exp (C * x ^ 2 * τ - c * ρ ^ 2 / τ) =
      Real.exp (C * x ^ 2 * τ - (c / 2) * ρ ^ 2 / τ) *
        Real.exp (-((c / 2) * ρ ^ 2 / τ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hmono : Real.exp (C * x ^ 2 * τ - (c / 2) * ρ ^ 2 / τ) ≤
      Real.exp (C * x ^ 2 * T - (c / 2) * ρ ^ 2 / T) := by
    apply Real.exp_le_exp.mpr
    have h1 : C * x ^ 2 * τ ≤ C * x ^ 2 * T :=
      mul_le_mul_of_nonneg_left hτT (by positivity)
    have h2 : (c / 2) * ρ ^ 2 / T ≤ (c / 2) * ρ ^ 2 / τ :=
      div_le_div_of_nonneg_left (by positivity) hτ hτT
    linarith
  have hsing := clr_inv_sqrt_exp_le (c := c / 2) (by positivity) hρ hτ
  have hdec : Real.exp (-((c / 2) * ρ ^ 2 / τ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have : 0 ≤ (c / 2) * ρ ^ 2 / τ := by positivity
    linarith
  have hpre : ((Real.sqrt τ)⁻¹ + x) * Real.exp (-((c / 2) * ρ ^ 2 / τ)) ≤
      (Real.sqrt (c / 2) * ρ)⁻¹ + x := by
    rw [add_mul]
    have := mul_le_of_le_one_right hx hdec
    linarith
  rw [hsplit]
  calc C * ((Real.sqrt τ)⁻¹ + x) * (Real.exp (C * x ^ 2 * τ - (c / 2) * ρ ^ 2 / τ) *
        Real.exp (-((c / 2) * ρ ^ 2 / τ))) * R
      = C * (((Real.sqrt τ)⁻¹ + x) * Real.exp (-((c / 2) * ρ ^ 2 / τ))) *
          Real.exp (C * x ^ 2 * τ - (c / 2) * ρ ^ 2 / τ) * R := by ring
    _ ≤ C * ((Real.sqrt (c / 2) * ρ)⁻¹ + x) *
          Real.exp (C * x ^ 2 * T - (c / 2) * ρ ^ 2 / T) * R := by
        gcongr

/-- The restricted L² norm of a scalar class, in indicator and integral form. -/
theorem clr_indicator_norm_eq_sqrt {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    (eLpNorm (E.indicator (fun x => u x)) 2 volume).toReal =
      Real.sqrt (∫ x in E, ‖u x‖ ^ 2) := by
  have hm : MemLp (fun x => u x) 2 (volume.restrict E) :=
    (Lp.memLp u).mono_measure Measure.restrict_le_self
  have hsq : ((eLpNorm (E.indicator (fun x => u x)) 2 volume).toReal) ^ 2 =
      ∫ x in E, ‖u x‖ ^ 2 := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hE]
    rw [← eLpNorm_norm (fun x => u x) hm.aestronglyMeasurable]
    exact PDE.toReal_eLpNorm_two_sq_eq_integral_sq hm.norm
  rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg]

/-- The restriction of a physical class to a measurable set, as a bounded map. -/
theorem clr_restriction_map {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E) :
    ∃ W : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ u, ‖W u‖ = Real.sqrt (∫ x in E, ‖u x‖ ^ 2) := by
  classical
  let w : Vec d → ℝ := E.indicator (fun _ => 1)
  have hw : Measurable w := measurable_const.indicator hE
  have hwbound : ∀ x, |w x| ≤ 1 := by
    intro x
    by_cases hx : x ∈ E
    · simp [w, hx]
    · simp [w, hx]
  refine ⟨s5Mul (volume : Measure (Vec d)) hw (by norm_num) hwbound, fun u => ?_⟩
  rw [s5Mul_norm, ← clr_indicator_norm_eq_sqrt E hE u]
  congr 1
  apply eLpNorm_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ E
  · simp [w, hx]
  · simp [w, hx]

/-- Cauchy–Schwarz for a bounded matrix defect paired with two gradients on a
measurable region; only the second gradient is restricted. -/
theorem clr_defect_pair_le {d : ℕ} (E : Set (Vec d))
    (m : Fin d → Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hmm : ∀ j k, Measurable (m j k)) (hmb : ∀ j k x, |m j k x| ≤ B)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x in E, ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x‖ ≤
      (d : ℝ) * B * Real.sqrt (∑ k, ‖G k‖ ^ 2) *
        Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2) := by
  classical
  let MG : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun j k =>
    s5Mul volume (hmm j k) hB (hmb j k) (G k)
  have hMGc (j k : Fin d) : (MG j k : Vec d → ℂ) =ᵐ[volume]
      fun x => (m j k x : ℂ) * G k x := s5Mul_coe volume (hmm j k) hB (hmb j k) (G k)
  have hMGn (j k : Fin d) : ‖MG j k‖ ≤ B * ‖G k‖ :=
    c7_s5Mul_norm_le_of_ae (hmm j k) hB (hmb j k) hB (G k)
      (Eventually.of_forall fun x _ => hmb j k x)
  have hr : (volume : Measure (Vec d)).restrict E ≤ volume := Measure.restrict_le_self
  let ℓ : Fin d → ℝ := fun j => Calculus.S1.l2Size (volume.restrict E) (fun x => H j x)
  have hint (j k : Fin d) : Integrable (fun x => MG j k x * H j x) (volume.restrict E) :=
    ((Lp.memLp (MG j k)).mono_measure hr).integrable_mul ((Lp.memLp (H j)).mono_measure hr)
  have hrew : (∫ x in E, ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x) =
      ∑ j, ∑ k, ∫ x in E, MG j k x * H j x := by
    have hae : (fun x => ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x) =ᵐ[volume.restrict E]
        fun x => ∑ j, ∑ k, MG j k x * H j x := by
      have hall : ∀ᵐ x ∂volume, ∀ j k, MG j k x = (m j k x : ℂ) * G k x := by
        rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k; exact hMGc j k
      filter_upwards [ae_restrict_of_ae hall] with x hx
      simp only [hx]
    rw [integral_congr_ae hae, integral_finsetSum _ (fun j _ =>
      integrable_finset_sum _ (fun k _ => hint j k))]
    exact Finset.sum_congr rfl (fun j _ => integral_finsetSum _ (fun k _ => hint j k))
  have hpair (j k : Fin d) : ‖∫ x in E, MG j k x * H j x‖ ≤ B * ‖G k‖ * ℓ j := by
    refine (Calculus.S1.norm_integral_mul_le_l2Size ((Lp.memLp (MG j k)).mono_measure hr)
      ((Lp.memLp (H j)).mono_measure hr)).trans ?_
    have hs : Calculus.S1.l2Size (volume.restrict E) (fun x => MG j k x) ≤ ‖MG j k‖ := by
      rw [← Calculus.S1.l2Size_lp (MG j k)]
      apply Real.sqrt_le_sqrt
      exact integral_mono_measure hr (Eventually.of_forall fun x => sq_nonneg ‖MG j k x‖)
        (Lp.memLp (MG j k)).norm.integrable_sq
    exact mul_le_mul_of_nonneg_right (hs.trans (hMGn j k)) (Calculus.S1.l2Size_nonneg _)
  have hℓ : ∑ j, ℓ j ^ 2 = ∫ x in E, ∑ j, ‖H j x‖ ^ 2 := by
    have hm (j : Fin d) : MemLp (fun x => H j x) 2 (volume.restrict E) :=
      (Lp.memLp (H j)).mono_measure hr
    rw [integral_finsetSum _ (fun j _ => (hm j).integrable_norm_pow (by norm_num))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)
  have hcs (a : Fin d → ℝ) : ∑ j, a j ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ j, a j ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) a
    simpa [mul_comm] using h
  have hGn : 0 ≤ ∑ k, ‖G k‖ := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hℓn : 0 ≤ ∑ j, ℓ j := Finset.sum_nonneg fun j _ => Calculus.S1.l2Size_nonneg _
  calc ‖∫ x in E, ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x‖
      ≤ ∑ j, ∑ k, ‖∫ x in E, MG j k x * H j x‖ := by
        rw [hrew]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j, ∑ k, B * ‖G k‖ * ℓ j :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hpair j k
    _ = B * (∑ k, ‖G k‖) * (∑ j, ℓ j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ B * (Real.sqrt (d : ℝ) * Real.sqrt (∑ k, ‖G k‖ ^ 2)) *
          (Real.sqrt (d : ℝ) * Real.sqrt (∑ j, ℓ j ^ 2)) := by
        gcongr
        · exact hcs _
        · exact hcs _
    _ = (d : ℝ) * B * Real.sqrt (∑ k, ‖G k‖ ^ 2) *
          Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2) := by
        rw [← hℓ]
        have hd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = d :=
          Real.mul_self_sqrt (Nat.cast_nonneg d)
        calc B * (Real.sqrt (d : ℝ) * Real.sqrt (∑ k, ‖G k‖ ^ 2)) *
              (Real.sqrt (d : ℝ) * Real.sqrt (∑ j, ℓ j ^ 2))
            = (Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ)) * B *
                Real.sqrt (∑ k, ‖G k‖ ^ 2) * Real.sqrt (∑ j, ℓ j ^ 2) := by ring
          _ = _ := by rw [hd]

/-- Cauchy–Schwarz for a bounded force-column defect paired with a restricted
scalar class. -/
theorem clr_defect_column_le {d : ℕ} (E : Set (Vec d))
    (m : Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hmm : ∀ j, Measurable (m j)) (hmb : ∀ j x, |m j x| ≤ B)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (V : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x in E, (∑ j, (m j x : ℂ) * G j x) * V x‖ ≤
      (d : ℝ) * B * Real.sqrt (∑ k, ‖G k‖ ^ 2) * Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := by
  classical
  let MG : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun j =>
    s5Mul volume (hmm j) hB (hmb j) (G j)
  have hMGc (j : Fin d) : (MG j : Vec d → ℂ) =ᵐ[volume]
      fun x => (m j x : ℂ) * G j x := s5Mul_coe volume (hmm j) hB (hmb j) (G j)
  have hMGn (j : Fin d) : ‖MG j‖ ≤ B * ‖G j‖ :=
    c7_s5Mul_norm_le_of_ae (hmm j) hB (hmb j) hB (G j)
      (Eventually.of_forall fun x _ => hmb j x)
  have hr : (volume : Measure (Vec d)).restrict E ≤ volume := Measure.restrict_le_self
  have hint (j : Fin d) : Integrable (fun x => MG j x * V x) (volume.restrict E) :=
    ((Lp.memLp (MG j)).mono_measure hr).integrable_mul ((Lp.memLp V).mono_measure hr)
  have hrew : (∫ x in E, (∑ j, (m j x : ℂ) * G j x) * V x) =
      ∑ j, ∫ x in E, MG j x * V x := by
    have hae : (fun x => (∑ j, (m j x : ℂ) * G j x) * V x) =ᵐ[volume.restrict E]
        fun x => ∑ j, MG j x * V x := by
      have hall : ∀ᵐ x ∂volume, ∀ j, MG j x = (m j x : ℂ) * G j x := by
        rw [ae_all_iff]; exact hMGc
      filter_upwards [ae_restrict_of_ae hall] with x hx
      simp only [hx, Finset.sum_mul]
    rw [integral_congr_ae hae, integral_finsetSum _ (fun j _ => hint j)]
  have hℓ : Calculus.S1.l2Size (volume.restrict E) (fun x => V x) =
      Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := rfl
  have hpair (j : Fin d) : ‖∫ x in E, MG j x * V x‖ ≤
      B * ‖G j‖ * Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := by
    refine (Calculus.S1.norm_integral_mul_le_l2Size ((Lp.memLp (MG j)).mono_measure hr)
      ((Lp.memLp V).mono_measure hr)).trans ?_
    have hs : Calculus.S1.l2Size (volume.restrict E) (fun x => MG j x) ≤ ‖MG j‖ := by
      rw [← Calculus.S1.l2Size_lp (MG j)]
      apply Real.sqrt_le_sqrt
      exact integral_mono_measure hr (Eventually.of_forall fun x => sq_nonneg ‖MG j x‖)
        (Lp.memLp (MG j)).norm.integrable_sq
    rw [← hℓ]
    exact mul_le_mul_of_nonneg_right (hs.trans (hMGn j)) (Calculus.S1.l2Size_nonneg _)
  have hcs : ∑ j, ‖G j‖ ≤ Real.sqrt (d : ℝ) * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
    have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ => (1 : ℝ)) (fun j => ‖G j‖)
    simpa [mul_comm] using h
  have hsd : Real.sqrt (d : ℝ) ≤ d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast h
      calc Real.sqrt (d : ℝ) ≤ Real.sqrt ((d : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
        _ = d := Real.sqrt_sq (Nat.cast_nonneg d)
  have hV0 : 0 ≤ Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := Real.sqrt_nonneg _
  calc ‖∫ x in E, (∑ j, (m j x : ℂ) * G j x) * V x‖
      ≤ ∑ j, ‖∫ x in E, MG j x * V x‖ := by rw [hrew]; exact norm_sum_le _ _
    _ ≤ ∑ j, B * ‖G j‖ * Real.sqrt (∫ x in E, ‖V x‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => hpair j
    _ = B * (∑ j, ‖G j‖) * Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ B * ((d : ℝ) * Real.sqrt (∑ j, ‖G j‖ ^ 2)) * Real.sqrt (∫ x in E, ‖V x‖ ^ 2) := by
        gcongr
        exact hcs.trans (mul_le_mul_of_nonneg_right hsd (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- Points of the inner half ball are separated from the outer region. -/
theorem clr_half_ball_separation {d : ℕ} (z : Vec d) (ρ : ℝ) :
    ∀ x ∈ {x : Vec d | euclideanNorm (x - z) < ρ / 2},
      ∀ y ∈ {y : Vec d | ρ ≤ euclideanNorm (y - z)}, ρ / 2 ≤ euclideanNorm (x - y) := by
  intro x hx y hy
  simp only [Set.mem_setOf_eq] at hx hy
  have htri : euclideanNorm (y - z) ≤ euclideanNorm (y - x) + euclideanNorm (x - z) := by
    have h := TimeChange.euclideanNorm_add_le (y - x) (x - z)
    simpa only [sub_add_sub_cancel] using h
  have hs : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (x - y)
    simpa [neg_sub] using h
  rw [hs] at htri
  linarith

/-- The outer region of a ball is measurable. -/
theorem clr_outer_measurable {d : ℕ} (z : Vec d) (ρ : ℝ) :
    MeasurableSet {x : Vec d | ρ ≤ euclideanNorm (x - z)} := by
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact (isClosed_le continuous_const hn).measurableSet

/-- Gradient and value tails of a time-averaged transpose orbit with data in
the inner half ball, uniform over evolution times with `σ + ε ≤ T`. -/
theorem clr_transpose_averaged_tail (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d) (M : ℕ → ℝ), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ (T : ℝ) (σ ε : ℝ≥0), 0 < σ → 0 < ε → (σ : ℝ) + ε ≤ T →
    ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
    ∀ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → v x = 0) →
    ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) (Pdag σ (s4PhysicalTimeAverage Pdag v ε)) H ∧
      Real.sqrt (∫ x in {x : Vec d | ρ ≤ euclideanNorm (x - z)}, ∑ j, ‖H j x‖ ^ 2) ≤
        C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * T - (c / 2) * ρ ^ 2 / T) * ‖v‖ ∧
      Real.sqrt (∫ x in {x : Vec d | ρ ≤ euclideanNorm (x - z)},
          ‖Pdag σ (s4PhysicalTimeAverage Pdag v ε) x‖ ^ 2) ≤
        Real.exp (C * ‖ζ‖ ^ 2 * T - (c / 2) * ρ ^ 2 / T) * ‖v‖ := by
  obtain ⟨Cg, cg, hCg, hcg, htail⟩ :=
    u7_physical_transpose_gradient_off_diagonal_integral d Λ hΛ
  have hΛ0 : 0 < Λ := by linarith
  let C₀ : ℝ := 5 * Λ ^ 3
  have hC₀ : 0 < C₀ := by positivity
  let C : ℝ := max Cg C₀
  let c : ℝ := min cg (1 / (16 * C₀))
  have hC : 1 ≤ C := hCg.trans (le_max_left _ _)
  have hc : 0 < c := lt_min hcg (by positivity)
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω M hell hsmooth i ζ P Pdag hP hPdag T σ ε hσ hε hσT z ρ hρ v hv
  classical
  let E : Set (Vec d) := {x : Vec d | ρ ≤ euclideanNorm (x - z)}
  have hE : MeasurableSet E := clr_outer_measurable z ρ
  have hεr : (0 : ℝ) < ε := hε
  have hσr : (0 : ℝ) < σ := hσ
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have hell' := s5Elliptic_of_isElliptic hΛ hell
  obtain ⟨Tg, hTg⟩ := c7_physical_gradient_operator hΛ hell hsmooth hP hPdag Pdag
    (by simp) σ hσ
  obtain ⟨L, hL⟩ := u7_localized_gradient_linear_map E hE
  obtain ⟨W, hW⟩ := clr_restriction_map E hE
  have hu : Continuous (fun s : ℝ => Pdag s.toNNReal v) :=
    (hPdag.2.2.1 v).comp continuous_real_toNNReal
  have hi : IntervalIntegrable (fun s : ℝ => Pdag s.toNNReal v) volume 0 ε :=
    hu.intervalIntegrable _ _
  have hcomp (s : ℝ) : Pdag σ (Pdag s.toNNReal v) = Pdag (σ + s.toNNReal) v := by
    rw [hPdag.2.1]
    rfl
  -- envelope for every intermediate time
  let Env : ℝ := Real.exp (C * ‖ζ‖ ^ 2 * T - (c / 2) * ρ ^ 2 / T)
  have htime (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) ε) :
      0 < ((σ + s.toNNReal : ℝ≥0) : ℝ) ∧ ((σ + s.toNNReal : ℝ≥0) : ℝ) ≤ T := by
    have hs' : s ∈ Set.Ioc (0 : ℝ) ε := by simpa only [Set.uIoc_of_le hεr.le] using hs
    have hs0 : 0 ≤ s := hs'.1.le
    simp only [NNReal.coe_add, Real.coe_toNNReal _ hs0]
    constructor <;> linarith [hs'.2]
  have hgradbound : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖L (Tg (Pdag s.toNNReal v))‖ ≤
      C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) * Env * ‖v‖ := by
    intro s hs
    obtain ⟨hτ, hτT⟩ := htime s hs
    have hpos : 0 < σ + s.toNNReal := by exact_mod_cast hτ
    obtain ⟨G, hG, hGb⟩ := htail ω hell i ζ P Pdag hPdag (σ + s.toNNReal) hpos z ρ hρ v hv
    have hT' := hTg (Pdag s.toNNReal v)
    rw [hcomp s] at hT'
    have heq := physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ hT' hG
    rw [hL, heq]
    refine hGb.trans ?_
    have hmono : Cg * ((Real.sqrt ((σ + s.toNNReal : ℝ≥0) : ℝ))⁻¹ + ‖ζ‖) *
        Real.exp (Cg * ‖ζ‖ ^ 2 * ((σ + s.toNNReal : ℝ≥0) : ℝ) -
          cg * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ)) * ‖v‖ ≤
        C * ((Real.sqrt ((σ + s.toNNReal : ℝ≥0) : ℝ))⁻¹ + ‖ζ‖) *
        Real.exp (C * ‖ζ‖ ^ 2 * ((σ + s.toNNReal : ℝ≥0) : ℝ) -
          c * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ)) * ‖v‖ := by
      have hCgC : Cg ≤ C := le_max_left _ _
      have hcc : c ≤ cg := min_le_left _ _
      gcongr
      all_goals assumption
    refine hmono.trans ?_
    exact clr_tail_envelope (by linarith) hc (norm_nonneg ζ) hρ hτ hτT (norm_nonneg v)
  have hvalbound : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖W (Pdag σ (Pdag s.toNNReal v))‖ ≤
      Env * ‖v‖ := by
    intro s hs
    obtain ⟨hτ, hτT⟩ := htime s hs
    rw [hcomp s, hW]
    have hWt : ∀ (q : ℝ) (ψ : Vec d → ℝ), (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
        ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume →
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) *
            (Pdag (σ + s.toNNReal) f) x) 2 volume ∧
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) *
            (Pdag (σ + s.toNNReal) f) x) 2 volume).toReal ≤
            Real.exp (C₀ * (‖ζ‖ ^ 2 + q ^ 2) * ((σ + s.toNNReal : ℝ≥0) : ℝ)) *
              (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal :=
      fun q ψ hψ f hf => s5_weighted_transpose hell' hmeas i ζ hPdag (σ + s.toNNReal) q hψ f hf
    have hv0 : ∀ᵐ x ∂(volume : Measure (Vec d)),
        x ∉ {x : Vec d | euclideanNorm (x - z) < ρ / 2} → v x = 0 := by
      filter_upwards [hv] with x hx hxE
      exact hx (le_of_not_gt hxE)
    obtain ⟨-, hg⟩ := s5_gaussian_of_weighted hC₀ hτ (Pdag (σ + s.toNNReal)) hWt
      {x : Vec d | euclideanNorm (x - z) < ρ / 2} E hE (ρ / 2) (by positivity)
      (clr_half_ball_separation z ρ) v hv0
    rw [clr_indicator_norm_eq_sqrt E hE] at hg
    refine hg.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg v))
    apply Real.exp_le_exp.mpr
    have hT : 0 < T := hτ.trans_le hτT
    have h1 : C₀ * ‖ζ‖ ^ 2 * ((σ + s.toNNReal : ℝ≥0) : ℝ) ≤ C * ‖ζ‖ ^ 2 * T :=
      mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)) hτT
        hτ.le (by positivity)
    have h2 : (c / 2) * ρ ^ 2 / T ≤ 1 / (4 * C₀) * (ρ / 2) ^ 2 /
        ((σ + s.toNNReal : ℝ≥0) : ℝ) := by
      have hcC : c ≤ 1 / (16 * C₀) := min_le_right _ _
      have hA : (c / 2) * ρ ^ 2 / T ≤ c * ρ ^ 2 / T := by
        apply div_le_div_of_nonneg_right _ hT.le
        nlinarith [sq_nonneg ρ]
      have hB : c * ρ ^ 2 / T ≤ c * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hτ hτT
      have hD : c * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ) ≤
          1 / (16 * C₀) * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ) := by
        apply div_le_div_of_nonneg_right _ hτ.le
        exact mul_le_mul_of_nonneg_right hcC (sq_nonneg ρ)
      have hE' : 1 / (16 * C₀) * ρ ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ) =
          1 / (4 * C₀) * (ρ / 2) ^ 2 / ((σ + s.toNNReal : ℝ≥0) : ℝ) := by
        field_simp
        ring
      linarith
    linarith
  -- the averaged orbit and its gradient
  have havg : Pdag σ (s4PhysicalTimeAverage Pdag v ε) =
      ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), Pdag σ (Pdag s.toNNReal v) := by
    rw [s4PhysicalTimeAverage, map_smul, (Pdag σ).intervalIntegral_comp_comm hi]
  have hscale (B : ℝ) (X : ℝ → ℝ) (hX : ∀ s ∈ Set.uIoc (0 : ℝ) ε, X s ≤ B)
      {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F]
      (g : ℝ → F) (hgX : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖g s‖ ≤ X s) :
      ‖((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), g s‖ ≤ B := by
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖g s‖ ≤ B := fun s hs => (hgX s hs).trans (hX s hs)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hεr]
    rw [sub_zero, abs_of_pos hεr] at hint
    calc (ε : ℝ)⁻¹ * ‖∫ s in (0 : ℝ)..(ε : ℝ), g s‖ ≤ (ε : ℝ)⁻¹ * (B * ε) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hεr.le)
      _ = B := by field_simp
  refine ⟨Tg (s4PhysicalTimeAverage Pdag v ε), hTg _, ?_, ?_⟩
  · rw [← hL]
    have hrep : L (Tg (s4PhysicalTimeAverage Pdag v ε)) =
        ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), L (Tg (Pdag s.toNNReal v)) := by
      have h1 := (L.comp Tg).intervalIntegral_comp_comm hi
      simp only [ContinuousLinearMap.comp_apply] at h1
      rw [s4PhysicalTimeAverage, map_smul, map_smul, ← h1]
    rw [hrep]
    exact hscale _ _ hgradbound (fun s => L (Tg (Pdag s.toNNReal v))) (fun s _ => le_rfl)
  · rw [← hW, havg]
    have hi2 : IntervalIntegrable (fun s : ℝ => Pdag σ (Pdag s.toNNReal v)) volume 0 ε :=
      ((Pdag σ).continuous.comp hu).intervalIntegrable _ _
    have hrep : W (((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), Pdag σ (Pdag s.toNNReal v)) =
        ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), W (Pdag σ (Pdag s.toNNReal v)) := by
      rw [map_smul, ← W.intervalIntegral_comp_comm hi2]
    rw [hrep]
    exact hscale _ _ hvalbound (fun s => W (Pdag σ (Pdag s.toNNReal v))) (fun s _ => le_rfl)

/-- The forward physical evolution has the structural L² growth bound. -/
theorem clr_forward_growth {d : ℕ} {a : Vec d → Mat d} {Λ : ℝ}
    (hell : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
    (hmeas : ∀ j k, Measurable fun x => a x j k) {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P) (t : ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖P t f‖ ≤ Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * t) * ‖f‖ := by
  have hψ : ∀ x y : Vec d, |(fun _ : Vec d => (0 : ℝ)) x - (fun _ : Vec d => (0 : ℝ)) y| ≤
      euclideanNorm (x - y) := by
    intro x y
    simp only [sub_self, abs_zero]
    unfold euclideanNorm
    exact Real.sqrt_nonneg _
  have hf : MemLp (fun x => ((Real.exp (0 * (fun _ : Vec d => (0 : ℝ)) x) : ℝ) : ℂ) * f x)
      2 volume := by
    simpa using Lp.memLp f
  have h := (s5_weighted_forward hell hmeas i ζ hP t 0 hψ f hf).2
  simp only [mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  rw [Lp.norm_def, Lp.norm_def]
  convert h using 3

/-- Arithmetic for the integrated energy of a time-averaged forward orbit. -/
theorem clr_energy_arith {Λ a F I z S e1 e2 : ℝ} (hΛ : 0 < Λ) (ha0 : 0 ≤ a) (hF : 0 ≤ F)
    (ha : a ≤ e1 * F) (hzS : z * S ≤ e2) (he1 : 1 ≤ e1)
    (he2 : 1 ≤ e2)
    (hI : I ≤ 4 * Λ * (a / 2 + 40 * Λ ^ 3 * z * (S * (e1 * a)))) :
    I ≤ (2 * Λ + 160 * Λ ^ 4) * (e1 * e2 * e1) * F := by
  have he1F : 0 ≤ e1 * F := mul_nonneg (by linarith) hF
  have h1 : a ≤ e1 * e2 * e1 * F := by
    have hq : 1 ≤ e2 * e1 := one_le_mul_of_one_le_of_one_le he2 he1
    have : e1 * F ≤ (e2 * e1) * (e1 * F) := le_mul_of_one_le_left he1F hq
    calc a ≤ e1 * F := ha
      _ ≤ (e2 * e1) * (e1 * F) := this
      _ = e1 * e2 * e1 * F := by ring
  have h2 : z * (S * (e1 * a)) ≤ e2 * e1 * (e1 * F) := by
    have hzS' : z * S * (e1 * a) ≤ e2 * (e1 * a) :=
      mul_le_mul_of_nonneg_right hzS (mul_nonneg (by linarith) ha0)
    have h3 : e2 * (e1 * a) ≤ e2 * (e1 * (e1 * F)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact mul_le_mul_of_nonneg_left ha (by linarith)
    calc z * (S * (e1 * a)) = z * S * (e1 * a) := by ring
      _ ≤ e2 * (e1 * (e1 * F)) := hzS'.trans h3
      _ = e2 * e1 * (e1 * F) := by ring
  have hA := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 160 * Λ ^ 4)
  have hB := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Λ)
  have hexp : 4 * Λ * (a / 2 + 40 * Λ ^ 3 * z * (S * (e1 * a))) =
      2 * Λ * a + 160 * Λ ^ 4 * (z * (S * (e1 * a))) := by ring
  have hexp2 : (2 * Λ + 160 * Λ ^ 4) * (e1 * e2 * e1) * F =
      2 * Λ * (e1 * e2 * e1 * F) + 160 * Λ ^ 4 * (e2 * e1 * (e1 * F)) := by ring
  linarith

/-- The time-averaged forward orbit of an elliptic field has the structural
integrated gradient energy. -/
theorem clr_averaged_forward_energy {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω' : FieldPair d)
    (hell' : IsElliptic Λ ω'.1) {i : Fin d} {ζ : ℂ}
    {P' : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP' : IsPhysicalComplexSemigroup ω'.1 i ζ P') (f : Lp ℂ 2 (volume : Measure (Vec d)))
    {S : ℝ} (hS : 0 < S) (ε : ℝ≥0) (hε : 0 < ε) (hεS : (ε : ℝ) ≤ S) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl)
        (P' s.toNNReal (s4PhysicalTimeAverage P' f ε)) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      (∫ s in (0 : ℝ)..S, ∑ j, ‖G s j‖ ^ 2) ≤
        (2 * Λ + 160 * Λ ^ 4) * Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2 := by
  have hΛ0 : 0 < Λ := by linarith
  have hεr : (0 : ℝ) < ε := hε
  set C₀ : ℝ := 5 * Λ ^ 3 with hC₀def
  have hC₀ : 0 < C₀ := by positivity
  have hcont (j k : Fin d) : Continuous fun x => ω'.1 x j k := ω'.1.continuous.matrix_elem j k
  have hmemL (j k : Fin d) : MemLp (fun x => (ω'.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω'.1 Λ hΛ0 hell' hcont j k
  have hell'' := s5Elliptic_of_isElliptic hΛ hell'
  have hmeas' : ∀ j k, Measurable fun x => ω'.1 x j k := fun j k => (hcont j k).measurable
  have hone : S5Weight (fun _ : Vec d => (1 : ℝ)) 1 0 :=
    ⟨contDiff_const, zero_le_one, le_rfl, by simp, fun x => by
      simp [s5Nrm, coordinateDerivative]⟩
  have hW₁ : ∀ u : Lp ℂ 2 (volume : Measure (Vec d)),
      ‖s5Mul volume hone.measurable hone.B_nonneg hone.bound u‖ = ‖u‖ := by
    intro u
    rw [s5Mul_norm, Lp.norm_def]
    simp
  have hgrowth : ∀ (s : ℝ≥0) (g : Lp ℂ 2 (volume : Measure (Vec d))),
      ‖P' s g‖ ≤ Real.exp (C₀ * ‖ζ‖ ^ 2 * s) * ‖g‖ :=
    fun s g => clr_forward_growth hell'' hmeas' hP' s g
  have hav := crudeEnergy_physical_forward_averaged_orbit hP' f ε
  have hgen : IsPhysicalComplexGeneratorPair ω'.1 i ζ (s4PhysicalTimeAverage P' f ε)
      (((ε : ℝ) : ℂ)⁻¹ • (P' ε f - f)) := by
    have h0 := hav.2.2.2 0
    simp only [hP'.1, ContinuousLinearMap.id_apply] at h0
    exact h0
  set fε := s4PhysicalTimeAverage P' f ε with hfεdef
  obtain ⟨G, hG, hGc, hGE⟩ := u7_forward_orbit_integrated_weighted_gradient ω'.1 i ζ
    hmemL hΛ hell'' hmeas' hone P' hP' hgen
  refine ⟨G, hG, hGc, ?_⟩
  have hGE' := hGE S.toNNReal
  simp only [hW₁, Real.coe_toNNReal _ hS.le] at hGE'
  have hK0 : 5 * (2 * Λ) ^ 3 * ((0 : ℝ) ^ 2 + ‖ζ‖ ^ 2) = 40 * Λ ^ 3 * ‖ζ‖ ^ 2 := by ring
  rw [hK0] at hGE'
  -- norm of the averaged datum
  have hfε : ‖fε‖ ≤ Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) ε, ‖P' s.toNNReal f‖ ≤
        Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      intro s hs
      have hs' : s ∈ Set.Ioc (0 : ℝ) ε := by simpa only [Set.uIoc_of_le hεr.le] using hs
      refine (hgrowth _ f).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg f))
      apply Real.exp_le_exp.mpr
      rw [Real.coe_toNNReal _ hs'.1.le]
      exact mul_le_mul_of_nonneg_left (hs'.2.trans hεS) (by positivity)
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hfεdef, s4PhysicalTimeAverage, norm_smul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hεr]
    rw [sub_zero, abs_of_pos hεr] at hint
    calc (ε : ℝ)⁻¹ * ‖∫ s in (0 : ℝ)..(ε : ℝ), P' s.toNNReal f‖
        ≤ (ε : ℝ)⁻¹ * (Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ * ε) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr hεr.le)
      _ = Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ := by field_simp
  -- mass of the averaged orbit
  have hmass : (∫ s in (0 : ℝ)..S, ‖P' s.toNNReal fε‖ ^ 2) ≤
      S * (Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ ^ 2) := by
    have hb : ∀ s ∈ Set.uIoc (0 : ℝ) S, ‖‖P' s.toNNReal fε‖ ^ 2‖ ≤
        Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ ^ 2 := by
      intro s hs
      have hs' : s ∈ Set.Ioc (0 : ℝ) S := by simpa only [Set.uIoc_of_le hS.le] using hs
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : ‖P' s.toNNReal fε‖ ≤ Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ := by
        refine (hgrowth _ fε).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
        apply Real.exp_le_exp.mpr
        rw [Real.coe_toNNReal _ hs'.1.le]
        exact mul_le_mul_of_nonneg_left hs'.2 (by positivity)
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc ‖P' s.toNNReal fε‖ ^ 2 ≤ (Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖) ^ 2 := h2
        _ = Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ ^ 2 := by
          rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [sub_zero, abs_of_pos hS] at h
    have hnn : 0 ≤ ∫ s in (0 : ℝ)..S, ‖P' s.toNNReal fε‖ ^ 2 :=
      intervalIntegral.integral_nonneg hS.le (fun s _ => sq_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h
    linarith
  have hI : (∫ s in (0 : ℝ)..S, ∑ j, ‖G s j‖ ^ 2) ≤
      4 * Λ * (‖fε‖ ^ 2 / 2 + 40 * Λ ^ 3 * ‖ζ‖ ^ 2 *
        (S * (Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ ^ 2))) := by
    have hstep : (Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..S, ∑ j, ‖G s j‖ ^ 2) ≤
        ‖fε‖ ^ 2 / 2 + 40 * Λ ^ 3 * ‖ζ‖ ^ 2 *
          (S * (Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖fε‖ ^ 2)) := by
      have h := mul_le_mul_of_nonneg_left hmass
        (by positivity : (0 : ℝ) ≤ 40 * Λ ^ 3 * ‖ζ‖ ^ 2)
      have hS2 : 0 ≤ ‖P' S.toNNReal fε‖ ^ 2 := sq_nonneg _
      linarith
    have h4 : (4 * Λ) * ((Λ⁻¹ / 4) * (∫ s in (0 : ℝ)..S, ∑ j, ‖G s j‖ ^ 2)) =
        ∫ s in (0 : ℝ)..S, ∑ j, ‖G s j‖ ^ 2 := by field_simp
    rw [← h4]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  have hfε2 : ‖fε‖ ^ 2 ≤ Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hfε 2
    calc ‖fε‖ ^ 2 ≤ (Real.exp (C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖) ^ 2 := h
      _ = Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hz : ‖ζ‖ ^ 2 * S ≤ Real.exp (‖ζ‖ ^ 2 * S) := by
    have := Real.add_one_le_exp (‖ζ‖ ^ 2 * S)
    linarith
  have hfin := clr_energy_arith hΛ0 (sq_nonneg ‖fε‖) (sq_nonneg ‖f‖) hfε2
    hz (Real.one_le_exp (by positivity)) (Real.one_le_exp (by positivity)) hI
  have hsplit : Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) * Real.exp (‖ζ‖ ^ 2 * S) *
      Real.exp (2 * C₀ * ‖ζ‖ ^ 2 * S) = Real.exp ((4 * C₀ + 1) * ‖ζ‖ ^ 2 * S) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  rw [hsplit] at hfin
  exact hfin

/-- Cauchy–Schwarz in time for the square root of a continuous density. -/
theorem clr_interval_integral_sqrt_le {S Y : ℝ} (hS : 0 < S) (hY : 0 < Y) {X : ℝ → ℝ}
    (hX : Continuous X) (hX0 : ∀ t, 0 ≤ X t) (hXY : (∫ t in (0 : ℝ)..S, X t) ≤ Y) :
    (∫ t in (0 : ℝ)..S, Real.sqrt (X t)) ≤ Real.sqrt (S * Y) := by
  set lam : ℝ := Real.sqrt S / Real.sqrt Y with hlamdef
  have hsSpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr hS
  have hsYpos : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hlam : 0 < lam := div_pos hsSpos hsYpos
  have hgs : ∀ t, Real.sqrt (X t) ≤ (lam * X t + lam⁻¹) / 2 := by
    intro t
    have hsq : Real.sqrt (X t) ^ 2 = X t := Real.sq_sqrt (hX0 t)
    have h1 : 0 ≤ (lam * Real.sqrt (X t) - 1) ^ 2 := sq_nonneg _
    have h2 : lam * (lam * X t + lam⁻¹) = lam ^ 2 * Real.sqrt (X t) ^ 2 + 1 := by
      rw [hsq]; field_simp
    have h3 : lam * (2 * Real.sqrt (X t)) ≤ lam * (lam * X t + lam⁻¹) := by nlinarith
    have h4 : 2 * Real.sqrt (X t) ≤ lam * X t + lam⁻¹ := le_of_mul_le_mul_left h3 hlam
    linarith
  have hXi : IntervalIntegrable X volume 0 S := hX.intervalIntegrable _ _
  have hmono : (∫ t in (0 : ℝ)..S, Real.sqrt (X t)) ≤
      ∫ t in (0 : ℝ)..S, (lam * X t + lam⁻¹) / 2 :=
    intervalIntegral.integral_mono_on hS.le
      ((Real.continuous_sqrt.comp hX).intervalIntegrable _ _)
      (((hXi.const_mul lam).add intervalIntegrable_const).div_const 2)
      (fun t _ => hgs t)
  have hval : (∫ t in (0 : ℝ)..S, (lam * X t + lam⁻¹) / 2) =
      (lam * (∫ t in (0 : ℝ)..S, X t) + lam⁻¹ * S) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (hXi.const_mul lam) intervalIntegrable_const, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    simp [mul_comm]
  rw [hval] at hmono
  refine hmono.trans ?_
  have hY' : lam * (∫ t in (0 : ℝ)..S, X t) ≤ lam * Y := mul_le_mul_of_nonneg_left hXY hlam.le
  have hsS : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS.le
  have hsY : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY.le
  have hlamY : lam * Y = Real.sqrt S * Real.sqrt Y := by
    rw [hlamdef, div_mul_eq_mul_div, div_eq_iff hsYpos.ne']
    linear_combination (-Real.sqrt S) * (Real.mul_self_sqrt hY.le)
  have hlamS : lam⁻¹ * S = Real.sqrt S * Real.sqrt Y := by
    rw [hlamdef, inv_div, div_mul_eq_mul_div, div_eq_iff hsSpos.ne']
    linear_combination (-Real.sqrt Y) * (Real.mul_self_sqrt hS.le)
  rw [Real.sqrt_mul hS.le]
  linarith

/-- The literal Duhamel defect of two elliptic fields on a measurable region is
controlled by the full first gradient and the restricted second gradient and value. -/
theorem clr_duhamel_defect_le {d : ℕ} (E : Set (Vec d))
    (a b : Vec d → Mat d) {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (ha : ∀ j k, Continuous fun x => a x j k) (hb : ∀ j k, Continuous fun x => b x j k)
    (hab : ∀ x j k, |a x j k| ≤ Λ ∧ |b x j k| ≤ Λ) (i : Fin d) (ζ : ℂ)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (V : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖-(1 / 2 : ℂ) * (∫ x in E, ∑ j, ∑ k, ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
      ζ * (∫ x in E, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * V x)‖ ≤
      d * Λ * Real.sqrt (∑ k, ‖G k‖ ^ 2) *
        (Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2) +
          2 * ‖ζ‖ * Real.sqrt (∫ x in E, ‖V x‖ ^ 2)) := by
  let m : Fin d → Fin d → Vec d → ℝ := fun j k x => a x j k - b x j k
  have hmm : ∀ j k, Measurable (m j k) := fun j k => ((ha j k).sub (hb j k)).measurable
  have hmb : ∀ j k x, |m j k x| ≤ 2 * Λ := by
    intro j k x
    refine (abs_sub _ _).trans ?_
    linarith [(hab x j k).1, (hab x j k).2]
  have hI1 : (∫ x in E, ∑ j, ∑ k, ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) =
      ∫ x in E, ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x := by
    congr 1; funext x; simp only [m, Complex.ofReal_sub]
  have hI2 : (∫ x in E, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * V x) =
      ∫ x in E, (∑ j, (((fun j x => m j i x) j x : ℝ) : ℂ) * G j x) * V x := by
    congr 1; funext x; simp only [m, Complex.ofReal_sub]
  rw [hI1, hI2]
  have hb1 := clr_defect_pair_le E m (by positivity) hmm hmb G H
  have hb2 := clr_defect_column_le E (fun j x => m j i x) (by positivity)
    (fun j => hmm j i) (fun j x => hmb j i x) G V
  set g := Real.sqrt (∑ k, ‖G k‖ ^ 2)
  set th := Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2)
  set tv := Real.sqrt (∫ x in E, ‖V x‖ ^ 2)
  set I1 := ∫ x in E, ∑ j, ∑ k, (m j k x : ℂ) * G k x * H j x
  set I2 := ∫ x in E, (∑ j, (((fun j x => m j i x) j x : ℝ) : ℂ) * G j x) * V x
  have hhalf : ‖-(1 / 2 : ℂ)‖ = 1 / 2 := by simp
  calc ‖-(1 / 2 : ℂ) * I1 + ζ * I2‖ ≤ ‖-(1 / 2 : ℂ) * I1‖ + ‖ζ * I2‖ := norm_add_le _ _
    _ = 1 / 2 * ‖I1‖ + ‖ζ‖ * ‖I2‖ := by rw [norm_mul, norm_mul, hhalf]
    _ ≤ 1 / 2 * ((d : ℝ) * (2 * Λ) * g * th) + ‖ζ‖ * ((d : ℝ) * (2 * Λ) * g * tv) := by
        gcongr
    _ = d * Λ * g * (th + 2 * ‖ζ‖ * tv) := by ring

/-- Duhamel comparison of two physical forward evolutions whose coefficients
agree on a ball. Tested against data in the inner half ball, the difference is
bounded by the transpose tails of the first field and the integrated energy of
the second. -/
theorem clr_retained_duhamel_pairing (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d) (M : ℕ → ℝ), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag P' : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
    ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 0 < S → ∀ f v : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → v x = 0) →
      ‖(∫ x, P' S.toNNReal f x * v x) - ∫ x, P S.toNNReal f x * v x‖ ≤
        d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) * ‖v‖ *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2)) := by
  obtain ⟨Ct, ct, hCt, hct, htail⟩ := clr_transpose_averaged_tail d Λ hΛ
  refine ⟨Ct, ct, hCt, hct, ?_⟩
  intro ω ω' M hell hsmooth hell' i ζ P Pdag P' hP hPdag hP' z ρ hρ hagree S hS f v hv
  classical
  have hΛ0 : 0 < Λ := by linarith
  set R : ℝ := (Real.sqrt (ct / 2) * ρ)⁻¹ with hRdef
  set Env : ℝ := Real.exp (Ct * ‖ζ‖ ^ 2 * (2 * S) - (ct / 2) * ρ ^ 2 / (2 * S)) with hEnvdef
  set Y₀ : ℝ := (2 * Λ + 160 * Λ ^ 4) *
    Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2 with hY₀def
  set K₁ : ℝ := d * Λ * (Ct * (R + ‖ζ‖) + 2 * ‖ζ‖) * Env * ‖v‖ with hK₁def
  have hK₁ : 0 ≤ K₁ := by positivity
  by_cases hf0 : ‖f‖ = 0
  · have hf : f = 0 := norm_eq_zero.mp hf0
    subst hf
    simp only [map_zero]
    rw [sub_self, norm_zero]
    positivity
  have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg f) (Ne.symm hf0)
  have hY₀ : 0 < Y₀ := by positivity
  let A : Set (Vec d) := {x : Vec d | euclideanNorm (x - z) < ρ}
  let E : Set (Vec d) := {x : Vec d | ρ ≤ euclideanNorm (x - z)}
  have hAc : Aᶜ = E := by ext x; simp [A, E, not_lt]
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hA : MeasurableSet A := (isOpen_lt hn continuous_const).measurableSet
  have hcont (ω₀ : FieldPair d) (j k : Fin d) : Continuous fun x => ω₀.1 x j k :=
    ω₀.1.continuous.matrix_elem j k
  have hmemL (ω₀ : FieldPair d) (h : IsElliptic Λ ω₀.1) (j k : Fin d) :
      MemLp (fun x => (ω₀.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω₀.1 Λ hΛ0 h (hcont ω₀) j k
  have hab : ∀ x ∈ A, ω'.1 x = ω.1 x := fun x hx => hagree x hx
  obtain ⟨D, -, hDspec, hlim⟩ := s4_physical_localized_duhamel_averaging_limit
    (hmemL ω' hell') (hmemL ω hell) hP' hPdag A hA hab f v S hS
  have hpair (u w : Lp ℂ 2 (volume : Measure (Vec d))) :
      s4PhysicalMassPairing u w = ∫ x, u x * w x :=
    (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral u w
  have htrans : (∫ x, f x * Pdag S.toNNReal v x) = ∫ x, P S.toNNReal f x * v x :=
    (hPdag.2.2.2.2 S.toNNReal f v).symm
  rw [hpair, hpair, htrans] at hlim
  have hentry : ∀ x j k, |ω'.1 x j k| ≤ Λ ∧ |ω.1 x j k| ≤ Λ := fun x j k =>
    ⟨Correctors.IsElliptic.entry_abs_le hΛ0 hell' x j k,
      Correctors.IsElliptic.entry_abs_le hΛ0 hell x j k⟩
  have hbound : ∀ ε : ℝ≥0, 0 < ε → (ε : ℝ) ≤ S →
      ‖∫ t in (0 : ℝ)..S, D ε t‖ ≤ K₁ * Real.sqrt (S * Y₀) := by
    intro ε hε hεS
    obtain ⟨G, hG, hGc, hY⟩ := clr_averaged_forward_energy hΛ ω' hell' hP' f hS ε hε hεS
    set g : ℝ → ℝ := fun t => Real.sqrt (∑ j, ‖G t j‖ ^ 2) with hgdef
    have hXc : Continuous (fun t => ∑ j, ‖G t j‖ ^ 2) :=
      continuous_finsetSum _ fun j _ => ((hGc j).norm).pow 2
    have hgc : Continuous g := Real.continuous_sqrt.comp hXc
    have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) S, ‖D ε t‖ ≤ K₁ * g t := by
      intro t ht
      obtain ⟨G', H', hG', hH', hDt⟩ := hDspec ε t ht.1 ht.2
      have hGG : G' = G t := physicalH1Graph_gradient_unique volume (Or.inl rfl)
        (P' t.toNNReal (s4PhysicalTimeAverage P' f ε)) G' (G t) hG' (hG t)
      have hσ : 0 < (S - t).toNNReal := by
        rw [Real.toNNReal_pos]; linarith [ht.2]
      have hσT : ((S - t).toNNReal : ℝ) + ε ≤ 2 * S := by
        rw [Real.coe_toNNReal _ (by linarith [ht.2])]
        linarith [ht.1]
      obtain ⟨H, hH, hHb, hVb⟩ := htail ω M hell hsmooth i ζ P Pdag hP hPdag (2 * S)
        (S - t).toNNReal ε hσ hε hσT z ρ hρ v hv
      have hHH : H' = H := physicalH1Graph_gradient_unique volume (Or.inl rfl)
        (Pdag (S - t).toNNReal (s4PhysicalTimeAverage Pdag v ε)) H' H hH' hH
      rw [hDt, hGG, hHH, hAc]
      refine (clr_duhamel_defect_le E ω'.1 ω.1 hΛ0.le (hcont ω') (hcont ω) hentry i ζ
        (G t) H (Pdag (S - t).toNNReal (s4PhysicalTimeAverage Pdag v ε))).trans ?_
      have hg0 : 0 ≤ g t := Real.sqrt_nonneg _
      have hsum : Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2) + 2 * ‖ζ‖ *
          Real.sqrt (∫ x in E, ‖Pdag (S - t).toNNReal (s4PhysicalTimeAverage Pdag v ε) x‖ ^ 2) ≤
          (Ct * (R + ‖ζ‖) + 2 * ‖ζ‖) * Env * ‖v‖ := by
        have h2 := mul_le_mul_of_nonneg_left hVb (by positivity : (0 : ℝ) ≤ 2 * ‖ζ‖)
        have : (Ct * (R + ‖ζ‖) + 2 * ‖ζ‖) * Env * ‖v‖ =
            Ct * (R + ‖ζ‖) * Env * ‖v‖ + 2 * ‖ζ‖ * (Env * ‖v‖) := by ring
        rw [this]
        exact add_le_add hHb h2
      calc (d : ℝ) * Λ * Real.sqrt (∑ k, ‖G t k‖ ^ 2) *
            (Real.sqrt (∫ x in E, ∑ j, ‖H j x‖ ^ 2) + 2 * ‖ζ‖ *
              Real.sqrt (∫ x in E,
                ‖Pdag (S - t).toNNReal (s4PhysicalTimeAverage Pdag v ε) x‖ ^ 2))
          ≤ (d : ℝ) * Λ * g t * ((Ct * (R + ‖ζ‖) + 2 * ‖ζ‖) * Env * ‖v‖) := by
            gcongr
        _ = K₁ * g t := by rw [hK₁def]; ring
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ S := by
      rw [ae_iff]
      simp
    have hint1 : ‖∫ t in (0 : ℝ)..S, D ε t‖ ≤ ∫ t in (0 : ℝ)..S, K₁ * g t := by
      apply intervalIntegral.norm_integral_le_of_norm_le hS.le
      · filter_upwards [hne] with t htS ht
        exact hpt t ⟨ht.1, lt_of_le_of_ne ht.2 htS⟩
      · exact (continuous_const.mul hgc).intervalIntegrable _ _
    have hint2 : (∫ t in (0 : ℝ)..S, g t) ≤ Real.sqrt (S * Y₀) :=
      clr_interval_integral_sqrt_le hS hY₀ hXc
        (fun t => Finset.sum_nonneg fun j _ => sq_nonneg _) hY
    calc ‖∫ t in (0 : ℝ)..S, D ε t‖ ≤ ∫ t in (0 : ℝ)..S, K₁ * g t := hint1
      _ = K₁ * ∫ t in (0 : ℝ)..S, g t := intervalIntegral.integral_const_mul _ _
      _ ≤ K₁ * Real.sqrt (S * Y₀) := mul_le_mul_of_nonneg_left hint2 hK₁
  have hSpos : (0 : ℝ≥0) < S.toNNReal := Real.toNNReal_pos.mpr hS
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0),
      ‖∫ t in (0 : ℝ)..S, D ε t‖ ≤ K₁ * Real.sqrt (S * Y₀) := by
    have h1' : ∀ᶠ ε in 𝓝 (0 : ℝ≥0), ε < S.toNNReal := Iio_mem_nhds hSpos
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ε < S.toNNReal := nhdsWithin_le_nhds h1'
    filter_upwards [h1, self_mem_nhdsWithin] with ε hεS hε0
    apply hbound ε hε0
    have := (NNReal.coe_lt_coe.mpr hεS).le
    rwa [Real.coe_toNNReal _ hS.le] at this
  exact le_of_tendsto hlim.norm hev

/-- Local L² form of the retained Duhamel comparison on the inner half ball. -/
theorem clr_retained_local_l2 (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d) (M : ℕ → ℝ), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag P' : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
    ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 0 < S → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      Real.sqrt (∫ x in {x : Vec d | euclideanNorm (x - z) < ρ / 2},
          ‖(P' S.toNNReal f - P S.toNNReal f) x‖ ^ 2) ≤
        d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2)) := by
  obtain ⟨C, c, hC, hc, hpair⟩ := clr_retained_duhamel_pairing d Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' M hell hsmooth hell' i ζ P Pdag P' hP hPdag hP' z ρ hρ hagree S hS f
  classical
  set w := P' S.toNNReal f - P S.toNNReal f with hwdef
  set B : Set (Vec d) := {x : Vec d | euclideanNorm (x - z) < ρ / 2} with hBdef
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hB : MeasurableSet B := (isOpen_lt hn continuous_const).measurableSet
  set Kb := d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
      Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
      Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
        Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S) * ‖f‖ ^ 2)) with hKbdef
  have hKb : 0 ≤ Kb := by positivity
  -- the conjugate test datum
  have hmv : MemLp (B.indicator (star (fun x => w x))) 2 volume :=
    (Lp.memLp w).star.indicator hB
  set v : Lp ℂ 2 (volume : Measure (Vec d)) := hmv.toLp _ with hvdef
  have hvc : (v : Vec d → ℂ) =ᵐ[volume] B.indicator (star (fun x => w x)) := hmv.coeFn_toLp
  have hvsupp : ∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → v x = 0 := by
    filter_upwards [hvc] with x hx hxB
    rw [hx, Set.indicator_of_notMem]
    simp only [hBdef, Set.mem_setOf_eq, not_lt]
    exact hxB
  have hbound := hpair ω ω' M hell hsmooth hell' i ζ P Pdag P' hP hPdag hP' z ρ hρ hagree
    S hS f v hvsupp
  -- identify both sides
  set Q : ℝ := ∫ x in B, ‖w x‖ ^ 2 with hQdef
  have hQ0 : 0 ≤ Q := integral_nonneg fun x => sq_nonneg _
  have hint1 : Integrable (fun x => P' S.toNNReal f x * v x) volume :=
    (Lp.memLp _).integrable_mul (Lp.memLp v)
  have hint2 : Integrable (fun x => P S.toNNReal f x * v x) volume :=
    (Lp.memLp _).integrable_mul (Lp.memLp v)
  have hlhs : (∫ x, P' S.toNNReal f x * v x) - ∫ x, P S.toNNReal f x * v x = (Q : ℂ) := by
    rw [← integral_sub hint1 hint2]
    have hae : (fun x => P' S.toNNReal f x * v x - P S.toNNReal f x * v x) =ᵐ[volume]
        B.indicator (fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ)) := by
      filter_upwards [hvc, Lp.coeFn_sub (P' S.toNNReal f) (P S.toNNReal f)] with x hx hw
      rw [← sub_mul, hx]
      by_cases hxB : x ∈ B
      · rw [Set.indicator_of_mem hxB, Set.indicator_of_mem hxB]
        have hwx : P' S.toNNReal f x - P S.toNNReal f x = w x := by rw [hw]; rfl
        rw [hwx]
        simp only [Pi.star_apply, RCLike.star_def]
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
      · rw [Set.indicator_of_notMem hxB, Set.indicator_of_notMem hxB, mul_zero]
    rw [integral_congr_ae hae, integral_indicator hB, integral_complex_ofReal]
  have hvnorm : ‖v‖ = Real.sqrt Q := by
    rw [Lp.norm_def, eLpNorm_congr_ae hvc]
    have heq : eLpNorm (B.indicator (star (fun x => w x))) 2 volume =
        eLpNorm (B.indicator (fun x => w x)) 2 volume := by
      refine eLpNorm_congr_norm_ae hmv.aestronglyMeasurable
        ((Lp.memLp w).indicator hB).aestronglyMeasurable ?_
      filter_upwards with x
      by_cases hxB : x ∈ B
      · simp [Set.indicator_of_mem hxB]
      · simp [Set.indicator_of_notMem hxB]
    rw [heq, clr_indicator_norm_eq_sqrt B hB w]
  rw [hlhs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ0, hvnorm] at hbound
  -- conclude from `Q ≤ Kb * sqrt Q`
  have hsQ : Real.sqrt Q ^ 2 = Q := Real.sq_sqrt hQ0
  have hKb' : Q ≤ Kb * Real.sqrt Q := by
    calc Q ≤ _ := hbound
      _ = Kb * Real.sqrt Q := by rw [hKbdef]; ring
  by_cases hQz : Real.sqrt Q = 0
  · rw [hQz]; exact hKb
  have hQpos : 0 < Real.sqrt Q := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hQz)
  have : Real.sqrt Q * Real.sqrt Q ≤ Kb * Real.sqrt Q := by nlinarith
  exact le_of_mul_le_mul_right this hQpos

/-- Weak physical gradients of a difference. -/
theorem clr_physicalH1_sub {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u - v) (fun j => G j - H j) := by
  have hneg {j : Fin d} {f g : Vec d → ℝ}
      (h : HasWeakPartialDerivative Set.univ j f g) :
      HasWeakPartialDerivative Set.univ j (fun x => -f x) (fun x => -g x) := by
    refine ⟨fun x hx => (h.1 x hx).neg, fun x hx => (h.2.1 x hx).neg, ?_⟩
    intro φ hφ
    simp only [neg_mul, integral_neg, h.2.2 φ hφ]
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x - v x) (fun j x => G j x - H j x)
    (Lp.coeFn_sub _ _) (fun _ => Lp.coeFn_sub _ _)).mpr
  constructor
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_re, Complex.neg_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hneg (hv.1 j))
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_im, Complex.neg_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hneg (hv.2 j))

/-- The local L² comparison bound in one-exponential form, for unit-or-larger
radii and bounded force. -/
theorem clr_local_l2_simplify {d : ℕ} {Λ C c ρ S z f : ℝ} (hΛ : 0 < Λ) (hC : 0 ≤ C)
    (hc : 0 < c) (hρ : 1 ≤ ρ) (hS : 0 < S) (hz : z ≤ 4) (hf : 0 ≤ f) :
    d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + z) + 2 * z) *
        Real.exp (C * z ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
        Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
          Real.exp ((4 * (5 * Λ ^ 3) + 1) * z ^ 2 * S) * f ^ 2)) ≤
      (d * Λ * (C * ((Real.sqrt (c / 2))⁻¹ + 4) + 8) * Real.sqrt (2 * Λ + 160 * Λ ^ 4)) *
        Real.sqrt S *
        Real.exp ((2 * C + (4 * (5 * Λ ^ 3) + 1) / 2) * z ^ 2 * S - (c / 4) * ρ ^ 2 / S) *
        f := by
  have hsc : 0 < Real.sqrt (c / 2) := Real.sqrt_pos.mpr (by positivity)
  have hR : (Real.sqrt (c / 2) * ρ)⁻¹ ≤ (Real.sqrt (c / 2))⁻¹ := by
    apply inv_anti₀ hsc
    nlinarith
  have hpre : C * ((Real.sqrt (c / 2) * ρ)⁻¹ + z) + 2 * z ≤
      C * ((Real.sqrt (c / 2))⁻¹ + 4) + 8 := by
    have : C * ((Real.sqrt (c / 2) * ρ)⁻¹ + z) ≤ C * ((Real.sqrt (c / 2))⁻¹ + 4) :=
      mul_le_mul_of_nonneg_left (add_le_add hR hz) hC
    linarith
  set E₀ := 2 * Λ + 160 * Λ ^ 4
  have hE₀ : 0 ≤ E₀ := by positivity
  set a := (4 * (5 * Λ ^ 3) + 1) * z ^ 2 * S
  have hsqrt : Real.sqrt (S * (E₀ * Real.exp a * f ^ 2)) =
      Real.sqrt S * Real.sqrt E₀ * Real.exp (a / 2) * f := by
    have he : Real.exp a = Real.exp (a / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; ring_nf
    rw [he, show S * (E₀ * Real.exp (a / 2) ^ 2 * f ^ 2) =
      (S * E₀) * (Real.exp (a / 2) * f) ^ 2 by ring]
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hS.le]
    ring
  rw [hsqrt]
  have hexp : Real.exp (C * z ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) * Real.exp (a / 2) =
      Real.exp ((2 * C + (4 * (5 * Λ ^ 3) + 1) / 2) * z ^ 2 * S - (c / 4) * ρ ^ 2 / S) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + z) + 2 * z) *
        Real.exp (C * z ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
        (Real.sqrt S * Real.sqrt E₀ * Real.exp (a / 2) * f)
      = d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + z) + 2 * z) * Real.sqrt E₀ * Real.sqrt S *
          (Real.exp (C * z ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
            Real.exp (a / 2)) * f := by ring
    _ ≤ d * Λ * (C * ((Real.sqrt (c / 2))⁻¹ + 4) + 8) * Real.sqrt E₀ * Real.sqrt S *
          (Real.exp (C * z ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
            Real.exp (a / 2)) * f := by
        gcongr
    _ = _ := by rw [hexp]

/-- Final arithmetic of the local C¹ interpolation. -/
theorem clr_interp_final {X L R K θ p q g F : ℝ} (hK : 0 ≤ K) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hL0 : 0 ≤ L) (hR0 : 0 ≤ R) (hF : 0 ≤ F)
    (hL : L ≤ Real.exp p * F) (hR : R ≤ Real.exp q * F)
    (hp : p ≤ g) (hpq : θ * p + (1 - θ) * q ≤ g)
    (hX : X ≤ K * (L ^ θ * R ^ (1 - θ) + L)) :
    X ≤ 2 * K * Real.exp g * F := by
  have h1 : L ^ θ ≤ (Real.exp p * F) ^ θ := Real.rpow_le_rpow hL0 hL hθ.le
  have h2 : R ^ (1 - θ) ≤ (1 * Real.exp q * F) ^ (1 - θ) := by
    rw [one_mul]; exact Real.rpow_le_rpow hR0 hR (by linarith)
  have hcommon := u4_interpolation_common_exponential 1 p q g 0 θ F le_rfl hF hθ hθ1
    (by linarith) (by linarith)
  have hstep : L ^ θ * R ^ (1 - θ) + L ≤
      (Real.exp p * F) ^ θ * (1 * Real.exp q * F) ^ (1 - θ) + Real.exp p * F := by
    apply add_le_add _ hL
    exact mul_le_mul h1 h2 (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg (by positivity) _)
  have := mul_le_mul_of_nonneg_left (hstep.trans hcommon) hK
  simp only [Real.exp_zero, mul_one] at this
  calc X ≤ _ := hX
    _ ≤ K * ((1 + 1) * Real.exp g * F) := this
    _ = 2 * K * Real.exp g * F := by ring

/-- A unit ball around a point well inside a larger ball lies inside it. -/
theorem clr_unit_ball_subset {d : ℕ} {x z : Vec d} {ρ : ℝ}
    (hx : euclideanNorm (x - z) + 1 ≤ ρ / 2) :
    {y : Vec d | euclideanNorm (x - y) < 1} ⊆ {y : Vec d | euclideanNorm (y - z) < ρ / 2} := by
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  have htri : euclideanNorm (y - z) ≤ euclideanNorm (y - x) + euclideanNorm (x - z) := by
    have h := TimeChange.euclideanNorm_add_le (y - x) (x - z)
    simpa only [sub_add_sub_cancel] using h
  have hs : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (x - y)
    simpa [neg_sub] using h
  linarith

/-- The unit-ball L² size of a representative is at most the restricted L² size
on any containing measurable set. -/
theorem clr_unit_ball_l2_le {d : ℕ} (w : Vec d → ℂ) (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (hw : w =ᵐ[volume] (u : Vec d → ℂ)) (x : Vec d) (B : Set (Vec d))
    (hsub : {y : Vec d | euclideanNorm (x - y) < 1} ⊆ B) :
    (eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator w) 2 volume).toReal ≤
      Real.sqrt (∫ y in B, ‖u y‖ ^ 2) := by
  have hn : Continuous (fun y : Vec d => euclideanNorm (x - y)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  set U : Set (Vec d) := {y : Vec d | euclideanNorm (x - y) < 1}
  have hU : MeasurableSet U := (isOpen_lt hn continuous_const).measurableSet
  have hcongr : eLpNorm (U.indicator w) 2 volume = eLpNorm (U.indicator (fun y => u y)) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [hw] with y hy
    by_cases hyU : y ∈ U
    · simp [Set.indicator_of_mem hyU, hy]
    · simp [Set.indicator_of_notMem hyU]
  rw [hcongr, clr_indicator_norm_eq_sqrt U hU u]
  apply Real.sqrt_le_sqrt
  apply setIntegral_mono_set
  · exact ((Lp.memLp u).integrable_norm_pow (by norm_num)).integrableOn
  · exact Eventually.of_forall fun y => sq_nonneg _
  · exact Eventually.of_forall hsub

/-- Exponent bookkeeping for the pointwise retained comparison. -/
theorem clr_pointwise_final {Ki K₀ Cp Cmax θ cl ρ S z L Rch X F : ℝ} (hKi : 0 < Ki)
    (hK₀ : 0 ≤ K₀) (hθ : 0 < θ) (hθ1 : θ < 1) (hcl : 0 < cl) (hS : 0 < S)
    (hF : 0 ≤ F) (hL0 : 0 ≤ L) (hR0 : 0 ≤ Rch)
    (hLb : L ≤ Real.exp (Cp * z ^ 2 * S - (cl / 4) * ρ ^ 2 / S) * (K₀ * (2 + S) * F))
    (hRb : Rch ≤ Real.exp (Cmax * z ^ 2 * S) * (K₀ * (2 + S) * F))
    (hX : X ≤ Ki * (L ^ θ * Rch ^ (1 - θ) + L)) :
    X ≤ max 1 (max (2 * Ki * K₀) (max Cp Cmax)) * (2 + S) *
      Real.exp (max 1 (max (2 * Ki * K₀) (max Cp Cmax)) * z ^ 2 * S -
        θ * (cl / 4) * ρ ^ 2 / S) * F := by
  set Cg := max Cp Cmax
  set Cf := max 1 (max (2 * Ki * K₀) Cg)
  set a : ℝ := (cl / 4) * ρ ^ 2 / S
  set y : ℝ := z ^ 2 * S
  have hy : 0 ≤ y := by positivity
  have ha : 0 ≤ a := by positivity
  set g : ℝ := Cg * y - θ * a
  have hF₀ : 0 ≤ K₀ * (2 + S) * F := by positivity
  have hp : Cp * z ^ 2 * S - (cl / 4) * ρ ^ 2 / S ≤ g := by
    have h1 : Cp * y ≤ Cg * y := mul_le_mul_of_nonneg_right (le_max_left _ _) hy
    have h2 : θ * a ≤ a := by nlinarith
    have he : Cp * z ^ 2 * S - (cl / 4) * ρ ^ 2 / S = Cp * y - a := by ring
    rw [he]
    linarith
  have hpq : θ * (Cp * z ^ 2 * S - (cl / 4) * ρ ^ 2 / S) + (1 - θ) * (Cmax * z ^ 2 * S) ≤ g := by
    have key : g - (θ * (Cp * z ^ 2 * S - (cl / 4) * ρ ^ 2 / S) + (1 - θ) * (Cmax * z ^ 2 * S)) =
        θ * ((Cg - Cp) * y) + (1 - θ) * ((Cg - Cmax) * y) := by ring
    have h1 : 0 ≤ θ * ((Cg - Cp) * y) :=
      mul_nonneg hθ.le (mul_nonneg (sub_nonneg.mpr (le_max_left _ _)) hy)
    have h2 : 0 ≤ (1 - θ) * ((Cg - Cmax) * y) :=
      mul_nonneg (by linarith) (mul_nonneg (sub_nonneg.mpr (le_max_right _ _)) hy)
    linarith
  have hfin := clr_interp_final hKi.le hθ hθ1 hL0 hR0 hF₀ hLb hRb hp hpq hX
  refine hfin.trans ?_
  have hCf1 : 2 * Ki * K₀ ≤ Cf := (le_max_left _ _).trans (le_max_right _ _)
  have hCf2 : Cg ≤ Cf := (le_max_right _ _).trans (le_max_right _ _)
  have hexp : Real.exp g ≤ Real.exp (Cf * z ^ 2 * S - θ * (cl / 4) * ρ ^ 2 / S) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hCf2 hy
    have he1 : Cf * z ^ 2 * S - θ * (cl / 4) * ρ ^ 2 / S = Cf * y - θ * a := by ring
    rw [he1]
    linarith
  have hE0 : 0 ≤ Real.exp g := (Real.exp_pos _).le
  calc 2 * Ki * Real.exp g * (K₀ * (2 + S) * F)
      = (2 * Ki * K₀) * (2 + S) * Real.exp g * F := by ring
    _ ≤ Cf * (2 + S) * Real.exp (Cf * z ^ 2 * S - θ * (cl / 4) * ρ ^ 2 / S) * F := by
        apply mul_le_mul_of_nonneg_right _ hF
        apply mul_le_mul _ hexp hE0 (by positivity)
        exact mul_le_mul_of_nonneg_right hCf1 (by linarith)

/-- Pointwise C¹ comparison of two physical forward evolutions whose
coefficients agree on a ball, for bounded force and times at least one. -/
theorem clr_retained_pointwise (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ (P Pdag P' P'dag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ P' P'dag →
    ∀ (z : Vec d) (ρ : ℝ), 1 ≤ ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 1 ≤ S → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ w : Vec d → ℂ, ContDiff ℝ 1 w ∧
      w =ᵐ[volume] ((P' S.toNNReal f - P S.toNNReal f : Lp ℂ 2 (volume : Measure (Vec d))) :
        Vec d → ℂ) ∧
      ∀ x, euclideanNorm (x - z) + 1 ≤ ρ / 2 →
        ‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) ≤
          C * (2 + S) * Real.exp (C * ‖ζ‖ ^ 2 * S - c * ρ ^ 2 / S) * ‖f‖ := by
  obtain ⟨Cl, cl, hCl, hcl, hloc⟩ := clr_retained_local_l2 d Λ hΛ
  obtain ⟨A, hA, hMA⟩ := u4Quant_finite_derivative_bound M (d + 3)
  obtain ⟨A', hA', hMA'⟩ := u4Quant_finite_derivative_bound M' (d + 3)
  obtain ⟨Cu, hCu, hu⟩ := u4Quant_physical_positive_time_derivatives (M := M) (d := d)
    hΛ A hA (d + 1)
  obtain ⟨Cu', hCu', hu'⟩ := u4Quant_physical_positive_time_derivatives (M := M') (d := d)
    hΛ A' hA' (d + 1)
  obtain ⟨Cs, hCs, hsob⟩ := u8_physical_high_weak_derivatives_C1_representative d
  obtain ⟨Ki, θ, hKi, hθ, hθ1, hinterp⟩ :=
    u4_local_C1_interpolation_of_global_chain u8_global_C1_interpolation_of_weak_derivative_chain d
  have hΛ0 : 0 < Λ := by linarith
  set KL : ℝ := d * Λ * (Cl * ((Real.sqrt (cl / 2))⁻¹ + 4) + 8) *
    Real.sqrt (2 * Λ + 160 * Λ ^ 4) with hKLdef
  have hKL : 0 ≤ KL := by positivity
  set Kc : ℝ := (Cu + Cu') * 2 ^ (d + 2) with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  set K₀ : ℝ := max KL Kc with hK₀def
  set Cmax : ℝ := max Cu Cu' with hCmaxdef
  set Cp : ℝ := 2 * Cl + (4 * (5 * Λ ^ 3) + 1) / 2 with hCpdef
  refine ⟨max 1 (max (2 * Ki * K₀) (max Cp Cmax)), θ * (cl / 4), le_max_left _ _,
    by positivity, ?_⟩
  intro ω ω' hell hsmooth hell' hsmooth' i ζ hζ P Pdag P' P'dag hP hPdag hP' hP'dag
    z ρ hρ hagree S hS f
  have hSpos : 0 < S := by linarith
  have hSt : (0 : ℝ≥0) < S.toNNReal := Real.toNNReal_pos.mpr hSpos
  have hScoe : ((S.toNNReal : ℝ≥0) : ℝ) = S := Real.coe_toNNReal _ hSpos.le
  obtain ⟨F, -, hF0, -, hF, -, hFb, -⟩ := hu hell hsmooth hζ
    (fun k hk => hMA k (by omega)) P Pdag hP hPdag f S.toNNReal hSt
  obtain ⟨F', -, hF0', -, hF', -, hFb', -⟩ := hu' hell' hsmooth' hζ
    (fun k hk => hMA' k (by omega)) P' P'dag hP' hP'dag f S.toNNReal hSt
  let Fw : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun p => F' p - F p
  have hFw0 : Fw [] = P' S.toNNReal f - P S.toNNReal f := by
    simp only [Fw, hF0, hF0']
  have hgraph : ∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
      (Fw p) (fun j => Fw (p ++ [j])) := fun p hp =>
    clr_physicalH1_sub (hF' p (by omega)) (hF p (by omega))
  set Rch : ℝ := Kc * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ with hRchdef
  have hRch : 0 ≤ Rch := by positivity
  have hinvS : (1 + (S.toNNReal : ℝ)⁻¹) ^ (d + 1 + 1) ≤ 2 ^ (d + 2) := by
    rw [hScoe]
    have hinv : S⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS
    have hb : 0 ≤ 1 + S⁻¹ := by positivity
    exact pow_le_pow_left₀ hb (by linarith) _
  have hexpS (C' : ℝ) (hC' : C' ≤ Cmax) :
      Real.exp (C' * ‖ζ‖ ^ 2 * (S.toNNReal : ℝ)) ≤ Real.exp (Cmax * ‖ζ‖ ^ 2 * S) := by
    rw [hScoe]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC' (sq_nonneg _)) hSpos.le
  have hbound : ∀ p, p.length ≤ d + 3 → ‖Fw p‖ ≤ Rch := by
    intro p hp
    have h1 := hFb p (by omega)
    have h2 := hFb' p (by omega)
    have hsum : ‖Fw p‖ ≤ ‖F' p‖ + ‖F p‖ := norm_sub_le _ _
    have e1 : Cu * (1 + (S.toNNReal : ℝ)⁻¹) ^ (d + 1 + 1) *
        Real.exp (Cu * ‖ζ‖ ^ 2 * (S.toNNReal : ℝ)) * ‖f‖ ≤
        Cu * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinvS (by linarith))
        (hexpS Cu (le_max_left _ _)) (Real.exp_pos _).le (by positivity)
    have e2 : Cu' * (1 + (S.toNNReal : ℝ)⁻¹) ^ (d + 1 + 1) *
        Real.exp (Cu' * ‖ζ‖ ^ 2 * (S.toNNReal : ℝ)) * ‖f‖ ≤
        Cu' * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinvS (by linarith))
        (hexpS Cu' (le_max_right _ _)) (Real.exp_pos _).le (by positivity)
    have : Rch = Cu' * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ +
        Cu * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      rw [hRchdef, hKcdef]; ring
    rw [this]
    linarith [h1.trans e1, h2.trans e2]
  obtain ⟨wbc, hwC1, hwae, -⟩ := hsob Fw Rch hRch hgraph hbound
  refine ⟨wbc, hwC1, by rw [← hFw0]; exact hwae, ?_⟩
  intro x hx
  have hint := hinterp Fw Rch hRch hgraph hbound wbc hwC1 hwae x
  dsimp only at hint
  -- the local L² factor
  set Bz : Set (Vec d) := {y : Vec d | euclideanNorm (y - z) < ρ / 2}
  have hn : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hBz : MeasurableSet Bz := (isOpen_lt hn continuous_const).measurableSet
  have hL1 := clr_unit_ball_l2_le (⇑wbc) (Fw []) hwae x Bz (clr_unit_ball_subset hx)
  rw [hFw0] at hL1
  have hL2 := hloc ω ω' M hell hsmooth hell' i ζ P Pdag P' hP hPdag hP' z ρ (by linarith)
    hagree S hSpos f
  have hL3 := clr_local_l2_simplify (d := d) hΛ0 (by linarith : (0 : ℝ) ≤ Cl) hcl hρ hSpos
    hζ (norm_nonneg f)
  set L := (eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator ⇑wbc) 2 volume).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hF₀ : 0 ≤ K₀ * (2 + S) * ‖f‖ := by positivity
  have hsS : Real.sqrt S ≤ 2 + S := by nlinarith [Real.sq_sqrt hSpos.le, Real.sqrt_nonneg S]
  have hLb : L ≤ Real.exp (Cp * ‖ζ‖ ^ 2 * S - (cl / 4) * ρ ^ 2 / S) * (K₀ * (2 + S) * ‖f‖) := by
    refine hL1.trans (hL2.trans (hL3.trans ?_))
    rw [← hKLdef]
    have hKK : KL * Real.sqrt S ≤ K₀ * (2 + S) :=
      mul_le_mul (le_max_left _ _) hsS (Real.sqrt_nonneg _) (by positivity)
    calc KL * Real.sqrt S * Real.exp (Cp * ‖ζ‖ ^ 2 * S - (cl / 4) * ρ ^ 2 / S) * ‖f‖
        = (KL * Real.sqrt S) * Real.exp (Cp * ‖ζ‖ ^ 2 * S - (cl / 4) * ρ ^ 2 / S) * ‖f‖ := by
          ring
      _ ≤ (K₀ * (2 + S)) * Real.exp (Cp * ‖ζ‖ ^ 2 * S - (cl / 4) * ρ ^ 2 / S) * ‖f‖ := by
          gcongr
      _ = _ := by ring
  have hRb : Rch ≤ Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * (K₀ * (2 + S) * ‖f‖) := by
    rw [hRchdef]
    have hKK : Kc ≤ K₀ * (2 + S) := by
      have : K₀ ≤ K₀ * (2 + S) := le_mul_of_one_le_right (by positivity) (by linarith)
      exact (le_max_right _ _).trans this
    calc Kc * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖
        ≤ (K₀ * (2 + S)) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by gcongr
      _ = _ := by ring
  exact clr_pointwise_final hKi (le_max_of_le_left hKL) hθ hθ1 hcl hSpos
    (norm_nonneg f) hL0 hRch hLb hRb hint

end EinsteinFull
