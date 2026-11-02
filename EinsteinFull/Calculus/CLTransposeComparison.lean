import EinsteinFull.Calculus.CLRetainedDuhamelComparison

/-! Retained comparison for the transpose endpoint, `paper/main.tex:715`.
Data in the inner half ball are handled by duality from the forward Duhamel
comparison; data outside it are Gaussian small near the centre for each
evolution separately. Local C¹ interpolation then gives the pointwise bound.
Deterministic in both fields. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation Blueprint

/-- Global L² comparison of two transpose evolutions whose coefficients agree on
a ball, for data in the inner half ball. -/
theorem clr_transpose_global_l2 (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d) (M : ℕ → ℝ), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag P' P'dag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ P' P'dag →
    ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 0 < S → ∀ h : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → h x = 0) →
      ‖P'dag S.toNNReal h - Pdag S.toNNReal h‖ ≤
        d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) * ‖h‖ *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) := by
  obtain ⟨C, c, hC, hc, hpair⟩ := clr_retained_duhamel_pairing d Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' M hell hsmooth hell' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ hρ hagree S hS h hh
  classical
  set w := P'dag S.toNNReal h - Pdag S.toNNReal h with hwdef
  have hmv : MemLp (star (fun x => w x)) 2 volume := (Lp.memLp w).star
  set f : Lp ℂ 2 (volume : Measure (Vec d)) := hmv.toLp _ with hfdef
  have hfc : (f : Vec d → ℂ) =ᵐ[volume] star (fun x => w x) := hmv.coeFn_toLp
  have hb := hpair ω ω' M hell hsmooth hell' i ζ P Pdag P' hP hPdag hP' z ρ hρ hagree S hS f h hh
  set E : ℝ := (2 * Λ + 160 * Λ ^ 4) * Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S)
    with hEdef
  have hE : 0 ≤ E := by positivity
  have hsq : Real.sqrt (S * (E * ‖f‖ ^ 2)) = Real.sqrt (S * E) * ‖f‖ := by
    rw [show S * (E * ‖f‖ ^ 2) = (S * E) * ‖f‖ ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rw [hsq] at hb
  have ht1 : (∫ x, P' S.toNNReal f x * h x) = ∫ x, f x * P'dag S.toNNReal h x :=
    hP'dag.2.2.2.2 S.toNNReal f h
  have ht2 : (∫ x, P S.toNNReal f x * h x) = ∫ x, f x * Pdag S.toNNReal h x :=
    hPdag.2.2.2.2 S.toNNReal f h
  have hint1 : Integrable (fun x => f x * P'dag S.toNNReal h x) volume :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hint2 : Integrable (fun x => f x * Pdag S.toNNReal h x) volume :=
    (Lp.memLp _).integrable_mul (Lp.memLp _)
  have hlhs : (∫ x, P' S.toNNReal f x * h x) - ∫ x, P S.toNNReal f x * h x =
      ((‖w‖ ^ 2 : ℝ) : ℂ) := by
    rw [ht1, ht2, ← integral_sub hint1 hint2]
    have hae : (fun x => f x * P'dag S.toNNReal h x - f x * Pdag S.toNNReal h x) =ᵐ[volume]
        fun x => ((‖w x‖ ^ 2 : ℝ) : ℂ) := by
      filter_upwards [hfc, Lp.coeFn_sub (P'dag S.toNNReal h) (Pdag S.toNNReal h)] with x hx hw
      rw [← mul_sub, hx]
      have hwx : P'dag S.toNNReal h x - Pdag S.toNNReal h x = w x := by rw [hw]; rfl
      rw [hwx]
      simp only [Pi.star_apply, RCLike.star_def]
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [integral_congr_ae hae, integral_complex_ofReal]
    congr 1
    rw [← Calculus.S1.l2Size_lp w]
    unfold Calculus.S1.l2Size
    rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
  have hfn : ‖f‖ = ‖w‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae hfc, Lp.norm_def]
    congr 1
    refine eLpNorm_congr_norm_ae hmv.aestronglyMeasurable (Lp.memLp w).aestronglyMeasurable ?_
    filter_upwards with x
    simp
  rw [hlhs, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hfn] at hb
  set Kb := d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
    Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) * ‖h‖ * Real.sqrt (S * E)
    with hKbdef
  have hKb : 0 ≤ Kb := by positivity
  have hb' : ‖w‖ * ‖w‖ ≤ Kb * ‖w‖ := by
    calc ‖w‖ * ‖w‖ = ‖w‖ ^ 2 := by ring
      _ ≤ _ := hb
      _ = Kb * ‖w‖ := by rw [hKbdef]; ring
  by_cases hw0 : ‖w‖ = 0
  · rw [hw0]; exact hKb
  have hwpos : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  exact le_of_mul_le_mul_right hb' hwpos

/-- Points of an inner quarter ball are separated from the outer half region. -/
theorem clr_quarter_separation {d : ℕ} (z : Vec d) (ρ : ℝ) :
    ∀ x ∈ {x : Vec d | ρ / 2 ≤ euclideanNorm (x - z)},
      ∀ y ∈ {y : Vec d | euclideanNorm (y - z) < ρ / 4}, ρ / 4 ≤ euclideanNorm (x - y) := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq] at hx hy
  have htri : euclideanNorm (x - z) ≤ euclideanNorm (x - y) + euclideanNorm (y - z) := by
    have h := TimeChange.euclideanNorm_add_le (x - y) (y - z)
    simpa only [sub_add_sub_cancel] using h
  linarith

/-- Local L² comparison of two transpose evolutions on the inner quarter ball,
for arbitrary data. -/
theorem clr_transpose_local_l2 (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d) (M : ℕ → ℝ), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 →
    ∀ (i : Fin d) (ζ : ℂ)
      (P Pdag P' P'dag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ P' →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ P' P'dag →
    ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      (∀ x, euclideanNorm (x - z) < ρ → ω'.1 x = ω.1 x) →
    ∀ (S : ℝ), 0 < S → ∀ h : Lp ℂ 2 (volume : Measure (Vec d)),
      Real.sqrt (∫ x in {x : Vec d | euclideanNorm (x - z) < ρ / 4},
          ‖(P'dag S.toNNReal h - Pdag S.toNNReal h) x‖ ^ 2) ≤
        (d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) +
          2 * Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S -
            (1 / (4 * (5 * Λ ^ 3))) * (ρ / 4) ^ 2 / S)) * ‖h‖ := by
  obtain ⟨C, c, hC, hc, hglob⟩ := clr_transpose_global_l2 d Λ hΛ
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' M hell hsmooth hell' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ hρ hagree S hS h
  classical
  have hΛ0 : 0 < Λ := by linarith
  have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  set Bh : Set (Vec d) := {x : Vec d | euclideanNorm (x - z) < ρ / 2} with hBhdef
  set Bq : Set (Vec d) := {x : Vec d | euclideanNorm (x - z) < ρ / 4} with hBqdef
  set Eo : Set (Vec d) := {x : Vec d | ρ / 2 ≤ euclideanNorm (x - z)} with hEodef
  have hBh : MeasurableSet Bh := (isOpen_lt hn continuous_const).measurableSet
  have hBq : MeasurableSet Bq := (isOpen_lt hn continuous_const).measurableSet
  -- splitting the datum
  let wgt : Vec d → ℝ := Bh.indicator (fun _ => 1)
  have hwm : Measurable wgt := measurable_const.indicator hBh
  have hwb : ∀ x, |wgt x| ≤ 1 := by
    intro x; by_cases hx : x ∈ Bh <;> simp [wgt, hx]
  set h₁ := s5Mul volume hwm (by norm_num) hwb h with hh₁def
  have hh₁c := s5Mul_coe volume hwm (by norm_num) hwb h
  have hh₁n : ‖h₁‖ ≤ ‖h‖ := by
    have := c7_s5Mul_norm_le_of_ae hwm (by norm_num) hwb (by norm_num : (0:ℝ) ≤ 1) h
      (Eventually.of_forall fun x _ => hwb x)
    simpa using this
  set h₂ := h - h₁ with hh₂def
  have hh₂n : ‖h₂‖ ≤ ‖h‖ := by
    have h1 := c7_s5Mul_norm_le_of_ae (w := fun x => 1 - wgt x) (B := 1)
      (measurable_const.sub hwm) (by norm_num : (0:ℝ) ≤ 1)
      (fun x => by by_cases hx : x ∈ Bh <;> simp [wgt, hx]) (by norm_num : (0:ℝ) ≤ 1) h
      (Eventually.of_forall fun x _ => by by_cases hx : x ∈ Bh <;> simp [wgt, hx])
    have heq : h₂ = s5Mul volume (w := fun x => 1 - wgt x) (B := 1) (measurable_const.sub hwm)
        (by norm_num) (fun x => by by_cases hx : x ∈ Bh <;> simp [wgt, hx]) h := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_sub h h₁, hh₁c,
        s5Mul_coe volume (w := fun x => 1 - wgt x) (B := 1) (measurable_const.sub hwm) (by norm_num)
          (fun x => by by_cases hx : x ∈ Bh <;> simp [wgt, hx]) h] with x h1 h2 h3
      rw [h3, h1, Pi.sub_apply, h2]
      push_cast; ring
    rw [heq]; simpa using h1
  have hh₁supp : ∀ᵐ x ∂volume, ρ / 2 ≤ euclideanNorm (x - z) → h₁ x = 0 := by
    filter_upwards [hh₁c] with x hx hxo
    rw [hx]
    have : x ∉ Bh := by simp only [hBhdef, Set.mem_ofPred_eq, not_lt]; exact hxo
    simp [wgt, this]
  have hh₂supp : ∀ᵐ x ∂volume, x ∉ Eo → h₂ x = 0 := by
    filter_upwards [Lp.coeFn_sub h h₁, hh₁c] with x h1 h2 hxE
    have hxB : x ∈ Bh := by
      simp only [hEodef, Set.mem_ofPred_eq, not_le] at hxE
      exact hxE
    rw [h1, Pi.sub_apply, h2]
    simp [wgt, hxB]
  -- the restriction map on the quarter ball
  obtain ⟨W, hW⟩ := clr_restriction_map Bq hBq
  have hdecomp : P'dag S.toNNReal h - Pdag S.toNNReal h =
      (P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁) +
        (P'dag S.toNNReal h₂ - Pdag S.toNNReal h₂) := by
    have : h = h₁ + h₂ := by rw [hh₂def]; abel
    conv_lhs => rw [this]
    simp only [map_add]
    abel
  rw [← hW, hdecomp, map_add]
  have hglob' := hglob ω ω' M hell hsmooth hell' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ hρ
    hagree S hS h₁ hh₁supp
  -- off-diagonal for each transpose evolution
  have hell2 := s5Elliptic_of_isElliptic hΛ hell
  have hell2' := s5Elliptic_of_isElliptic hΛ hell'
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have hmeas' : ∀ j k, Measurable fun x => ω'.1 x j k := fun j k =>
    (ω'.1.continuous.matrix_elem j k).measurable
  have hC₀ : 0 < 5 * Λ ^ 3 := by positivity
  have hSt : 0 < ((S.toNNReal : ℝ≥0) : ℝ) := by rw [Real.coe_toNNReal _ hS.le]; exact hS
  have hoff (a : Vec d → Mat d) (hea : ∀ x, S5Elliptic (fun j k => a x j k) Λ)
      (hma : ∀ j k, Measurable fun x => a x j k)
      (Q Qdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
      (hQd : IsPhysicalComplexTransposeSemigroup a i ζ Q Qdag) :
      ‖W (Qdag S.toNNReal h₂)‖ ≤ Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S -
            (1 / (4 * (5 * Λ ^ 3))) * (ρ / 4) ^ 2 / S) * ‖h‖ := by
    rw [hW, ← clr_indicator_norm_eq_sqrt Bq hBq]
    have hWt : ∀ (q : ℝ) (ψ : Vec d → ℝ), (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
        ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume →
          MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (Qdag S.toNNReal f) x) 2 volume ∧
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (Qdag S.toNNReal f) x)
            2 volume).toReal ≤
            Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * ((S.toNNReal : ℝ≥0) : ℝ)) *
              (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal :=
      fun q ψ hψ f hf => s5_weighted_transpose hea hma i ζ hQd S.toNNReal q hψ f hf
    have hg := (s5_gaussian_of_weighted hC₀ hSt (Qdag S.toNNReal) hWt Eo Bq hBq (ρ / 4)
      (by positivity) (clr_quarter_separation z ρ) h₂ hh₂supp).2
    rw [Real.coe_toNNReal _ hS.le] at hg
    exact hg.trans (mul_le_mul_of_nonneg_left hh₂n (Real.exp_pos _).le)
  have hW1 : ‖W (P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁)‖ ≤
      ‖P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁‖ := by
    rw [hW, ← Calculus.S1.l2Size_lp]
    apply Real.sqrt_le_sqrt
    exact setIntegral_le_integral ((Lp.memLp _).integrable_norm_pow (by norm_num))
      (Eventually.of_forall fun x => sq_nonneg _)
  have h2a := hoff ω'.1 hell2' hmeas' P' P'dag hP'dag
  have h2b := hoff ω.1 hell2 hmeas P Pdag hPdag
  set Kg := d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) with hKgdef
  have hglob'' : ‖P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁‖ ≤ Kg * ‖h‖ := by
    refine hglob'.trans ?_
    rw [hKgdef]
    have hK0 : 0 ≤ d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S)) := by positivity
    have hs0 : 0 ≤ Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) := Real.sqrt_nonneg _
    calc _ = (d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S))) * ‖h₁‖ *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) := by ring
      _ ≤ (d * Λ * (C * ((Real.sqrt (c / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (C * ‖ζ‖ ^ 2 * (2 * S) - (c / 2) * ρ ^ 2 / (2 * S))) * ‖h‖ *
          Real.sqrt (S * ((2 * Λ + 160 * Λ ^ 4) *
            Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S))) := by gcongr
      _ = _ := by ring
  calc ‖W (P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁) +
        W (P'dag S.toNNReal h₂ - Pdag S.toNNReal h₂)‖
      ≤ ‖W (P'dag S.toNNReal h₁ - Pdag S.toNNReal h₁)‖ +
          (‖W (P'dag S.toNNReal h₂)‖ + ‖W (Pdag S.toNNReal h₂)‖) := by
        refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [map_sub]
        exact norm_sub_le _ _
    _ ≤ Kg * ‖h‖ + (Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S -
            (1 / (4 * (5 * Λ ^ 3))) * (ρ / 4) ^ 2 / S) * ‖h‖ +
          Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S -
            (1 / (4 * (5 * Λ ^ 3))) * (ρ / 4) ^ 2 / S) * ‖h‖) :=
        add_le_add (hW1.trans hglob'') (add_le_add h2a h2b)
    _ = _ := by ring


/-- Arithmetic combining a Gaussian term and two Davies terms. -/
theorem clr_two_term_bound {L T D F KL K₀ S ex : ℝ} (hF : 0 ≤ F) (hS : 0 ≤ S)
    (hKL : 0 ≤ KL) (hex : 0 ≤ ex)
    (hL : L ≤ (T + 2 * D) * F) (hT : T * F ≤ KL * Real.sqrt S * ex * F) (hD : D ≤ ex)
    (hK : KL + 2 ≤ K₀) : L ≤ ex * (K₀ * (2 + S) * F) := by
  have hsS : Real.sqrt S ≤ 2 + S := by nlinarith [Real.sq_sqrt hS, Real.sqrt_nonneg S]
  have h2D : 2 * D * F ≤ 2 * ex * F := by nlinarith
  have hsum : KL * Real.sqrt S + 2 ≤ K₀ * (2 + S) := by
    have h1 : KL * Real.sqrt S ≤ KL * (2 + S) := mul_le_mul_of_nonneg_left hsS hKL
    have h2 : (KL + 2) * (2 + S) ≤ K₀ * (2 + S) := mul_le_mul_of_nonneg_right hK (by linarith)
    nlinarith
  calc L ≤ (T + 2 * D) * F := hL
    _ = T * F + 2 * D * F := by ring
    _ ≤ KL * Real.sqrt S * ex * F + 2 * ex * F := add_le_add hT h2D
    _ = ex * F * (KL * Real.sqrt S + 2) := by ring
    _ ≤ ex * F * (K₀ * (2 + S)) := mul_le_mul_of_nonneg_left hsum (mul_nonneg hex hF)
    _ = ex * (K₀ * (2 + S) * F) := by ring


/-- A unit ball around a point well inside a quarter ball lies inside it. -/
theorem clr_unit_ball_subset_quarter {d : ℕ} {x z : Vec d} {ρ : ℝ}
    (hx : euclideanNorm (x - z) + 1 ≤ ρ / 4) :
    {y : Vec d | euclideanNorm (x - y) < 1} ⊆ {y : Vec d | euclideanNorm (y - z) < ρ / 4} := by
  intro y hy
  change euclideanNorm (x - y) < 1 at hy
  change euclideanNorm (y - z) < ρ / 4
  have htri : euclideanNorm (y - z) ≤ euclideanNorm (y - x) + euclideanNorm (x - z) := by
    have h := TimeChange.euclideanNorm_add_le (y - x) (x - z)
    simpa only [sub_add_sub_cancel] using h
  have hs : euclideanNorm (y - x) = euclideanNorm (x - y) := by
    have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (x - y)
    simpa [neg_sub] using h
  linarith

/-- Monotonicity of a Gaussian-type exponential in its two rates. -/
theorem clr_exp_mono {A A' B B' y q : ℝ} (hy : 0 ≤ y) (hq : 0 ≤ q) (hA : A ≤ A')
    (hB : B' ≤ B) : Real.exp (A * y - B * q) ≤ Real.exp (A' * y - B' * q) := by
  apply Real.exp_le_exp.mpr
  have h1 := mul_le_mul_of_nonneg_right hA hy
  have h2 := mul_le_mul_of_nonneg_right hB hq
  linarith


/-- Two bounded weak derivative chains control the local C¹ size of the
difference of their values through its local L² size. -/
theorem clr_difference_chain_C1 (d : ℕ) :
    ∃ Ki θ : ℝ, 0 < Ki ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (F F' : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) (R R' : ℝ), 0 ≤ R → 0 ≤ R' →
      (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F' p) (fun j => F' (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) → (∀ p, p.length ≤ d + 3 → ‖F' p‖ ≤ R') →
    ∃ w : Vec d → ℂ, ContDiff ℝ 1 w ∧
      w =ᵐ[volume] ((F' [] - F [] : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) ∧
      ∀ x, ‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) ≤
        Ki * ((eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator w) 2
            volume).toReal ^ θ * (R + R') ^ (1 - θ) +
          (eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator w) 2 volume).toReal) := by
  obtain ⟨Cs, hCs, hsob⟩ := u8_physical_high_weak_derivatives_C1_representative d
  obtain ⟨Ki, θ, hKi, hθ, hθ1, hinterp⟩ :=
    u4_local_C1_interpolation_of_global_chain u8_global_C1_interpolation_of_weak_derivative_chain d
  refine ⟨Ki, θ, hKi, hθ, hθ1, ?_⟩
  intro F F' R R' hR hR' hF hF' hFb hFb'
  let Fw : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun p => F' p - F p
  have hgraph : ∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
      (Fw p) (fun j => Fw (p ++ [j])) := fun p hp =>
    clr_physicalH1_sub (hF' p hp) (hF p hp)
  have hbound : ∀ p, p.length ≤ d + 3 → ‖Fw p‖ ≤ R + R' := by
    intro p hp
    have h1 := hFb p hp
    have h2 := hFb' p hp
    have hsum : ‖Fw p‖ ≤ ‖F' p‖ + ‖F p‖ := norm_sub_le _ _
    linarith
  have hRR : 0 ≤ R + R' := by linarith
  obtain ⟨wbc, hwC1, hwae, -⟩ := hsob Fw (R + R') hRR hgraph hbound
  refine ⟨wbc, hwC1, hwae, fun x => ?_⟩
  have hint := hinterp Fw (R + R') hRR hgraph hbound wbc hwC1 hwae x
  exact hint

/-- Pointwise C¹ comparison of two physical transpose evolutions whose
coefficients agree on a ball, for bounded force and times at least one. -/
theorem clr_transpose_pointwise (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
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
      w =ᵐ[volume] ((P'dag S.toNNReal f - Pdag S.toNNReal f :
        Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) ∧
      ∀ x, euclideanNorm (x - z) + 1 ≤ ρ / 4 →
        ‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) ≤
          C * (2 + S) * Real.exp (C * ‖ζ‖ ^ 2 * S - c * ρ ^ 2 / S) * ‖f‖ := by
  obtain ⟨Cl, cl, hCl, hcl, hloc⟩ := clr_transpose_local_l2 d Λ hΛ
  obtain ⟨A, hA, hMA⟩ := u4Quant_finite_derivative_bound M (d + 3)
  obtain ⟨A', hA', hMA'⟩ := u4Quant_finite_derivative_bound M' (d + 3)
  obtain ⟨Cu, hCu, hu⟩ := u4Quant_physical_positive_time_derivatives (M := M) (d := d)
    hΛ A hA (d + 1)
  obtain ⟨Cu', hCu', hu'⟩ := u4Quant_physical_positive_time_derivatives (M := M') (d := d)
    hΛ A' hA' (d + 1)
  obtain ⟨Ki, θ, hKi, hθ, hθ1, hdiff⟩ := clr_difference_chain_C1 d
  have hΛ0 : 0 < Λ := by linarith
  set KL : ℝ := d * Λ * (Cl * ((Real.sqrt (cl / 2))⁻¹ + 4) + 8) *
    Real.sqrt (2 * Λ + 160 * Λ ^ 4) with hKLdef
  have hKL : 0 ≤ KL := by positivity
  set Kc : ℝ := (Cu + Cu') * 2 ^ (d + 2) with hKcdef
  have hKc : 0 ≤ Kc := by positivity
  set K₀ : ℝ := max (KL + 2) Kc with hK₀def
  set Cmax : ℝ := max Cu Cu' with hCmaxdef
  set Cp0 : ℝ := 2 * Cl + (4 * (5 * Λ ^ 3) + 1) / 2 with hCp0def
  set Cp : ℝ := max Cp0 (5 * Λ ^ 3) with hCpdef
  set cD : ℝ := 1 / (4 * (5 * Λ ^ 3)) / 16 with hcDdef
  have hcD : 0 < cD := by rw [hcDdef]; positivity
  set cl' : ℝ := min cl (4 * cD) with hcl'def
  have hcl' : 0 < cl' := lt_min hcl (by positivity)
  refine ⟨max 1 (max (2 * Ki * K₀) (max Cp Cmax)), θ * (cl' / 4), le_max_left _ _,
    by positivity, ?_⟩
  intro ω ω' hell hsmooth hell' hsmooth' i ζ hζ P Pdag P' P'dag hP hPdag hP' hP'dag
    z ρ hρ hagree S hS f
  have hSpos : 0 < S := by linarith
  have hSt : (0 : ℝ≥0) < S.toNNReal := Real.toNNReal_pos.mpr hSpos
  have hScoe : ((S.toNNReal : ℝ≥0) : ℝ) = S := Real.coe_toNNReal _ hSpos.le
  obtain ⟨-, F, -, hF0, -, hF, -, hFb⟩ := hu hell hsmooth hζ
    (fun k hk => hMA k (by omega)) P Pdag hP hPdag f S.toNNReal hSt
  obtain ⟨-, F', -, hF0', -, hF', -, hFb'⟩ := hu' hell' hsmooth' hζ
    (fun k hk => hMA' k (by omega)) P' P'dag hP' hP'dag f S.toNNReal hSt
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
  set R₁ : ℝ := Cu * (1 + (S.toNNReal : ℝ)⁻¹) ^ (d + 1 + 1) *
      Real.exp (Cu * ‖ζ‖ ^ 2 * (S.toNNReal : ℝ)) * ‖f‖ with hR₁def
  set R₂ : ℝ := Cu' * (1 + (S.toNNReal : ℝ)⁻¹) ^ (d + 1 + 1) *
      Real.exp (Cu' * ‖ζ‖ ^ 2 * (S.toNNReal : ℝ)) * ‖f‖ with hR₂def
  have hR₁ : 0 ≤ R₁ := by positivity
  have hR₂ : 0 ≤ R₂ := by positivity
  obtain ⟨wbc, hwC1, hwae, hwint⟩ := hdiff F F' R₁ R₂ hR₁ hR₂
    (fun p hp => hF p (by omega)) (fun p hp => hF' p (by omega))
    (fun p hp => hFb p (by omega)) (fun p hp => hFb' p (by omega))
  set Rch : ℝ := Kc * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ with hRchdef
  have hRch : 0 ≤ Rch := by positivity
  have hRR : R₁ + R₂ ≤ Rch := by
    have e1 : R₁ ≤ Cu * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinvS (by linarith))
        (hexpS Cu (le_max_left _ _)) (Real.exp_pos _).le (by positivity)
    have e2 : R₂ ≤ Cu' * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hinvS (by linarith))
        (hexpS Cu' (le_max_right _ _)) (Real.exp_pos _).le (by positivity)
    have : Rch = Cu * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ +
        Cu' * 2 ^ (d + 2) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by
      rw [hRchdef, hKcdef]; ring
    rw [this]
    exact add_le_add e1 e2
  have hFw0 : (F' [] - F [] : Lp ℂ 2 (volume : Measure (Vec d))) =
      P'dag S.toNNReal f - Pdag S.toNNReal f := by rw [hF0, hF0']
  refine ⟨wbc, hwC1, by rw [← hFw0]; exact hwae, ?_⟩
  intro x hx
  have hint0 := hwint x
  have hint : ‖wbc x‖ + Real.sqrt (∑ j, ‖fderiv ℝ wbc x (unitVector j)‖ ^ 2) ≤
      Ki * ((eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator wbc) 2
          volume).toReal ^ θ * Rch ^ (1 - θ) +
        (eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator wbc) 2 volume).toReal) := by
    refine hint0.trans (mul_le_mul_of_nonneg_left (add_le_add ?_ le_rfl) hKi.le)
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (add_nonneg hR₁ hR₂) hRR
      (sub_nonneg.mpr hθ1.le)) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  -- the local L² factor
  set Bz : Set (Vec d) := {y : Vec d | euclideanNorm (y - z) < ρ / 4}
  have hn : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hBz : MeasurableSet Bz := (isOpen_lt hn continuous_const).measurableSet
  have hsub : {y : Vec d | euclideanNorm (x - y) < 1} ⊆ Bz := clr_unit_ball_subset_quarter hx
  have hL1 := clr_unit_ball_l2_le (wbc) (F' [] - F []) hwae x Bz hsub
  rw [hFw0] at hL1
  have hL2 := hloc ω ω' M hell hsmooth hell' i ζ P Pdag P' P'dag hP hPdag hP' hP'dag z ρ
    (by linarith) hagree S hSpos f
  have hL3 := clr_local_l2_simplify (d := d) hΛ0 (by linarith : (0 : ℝ) ≤ Cl) hcl hρ hSpos
    hζ (norm_nonneg f)
  set L := (eLpNorm ({y : Vec d | euclideanNorm (x - y) < 1}.indicator wbc) 2 volume).toReal
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hF₀ : 0 ≤ K₀ * (2 + S) * ‖f‖ := by positivity
  set E₀ : ℝ := (2 * Λ + 160 * Λ ^ 4) * Real.exp ((4 * (5 * Λ ^ 3) + 1) * ‖ζ‖ ^ 2 * S)
    with hE₀def
  have hsq : Real.sqrt (S * E₀) * ‖f‖ = Real.sqrt (S * (E₀ * ‖f‖ ^ 2)) := by
    have h' : Real.sqrt (S * (E₀ * ‖f‖ ^ 2)) = Real.sqrt (S * E₀) * ‖f‖ := by
      rw [show S * (E₀ * ‖f‖ ^ 2) = (S * E₀) * ‖f‖ ^ 2 by ring,
        Real.sqrt_mul (show 0 ≤ S * E₀ by positivity), Real.sqrt_sq (norm_nonneg _)]
    exact h'.symm
  set ex : ℝ := Real.exp (Cp * ‖ζ‖ ^ 2 * S - (cl' / 4) * ρ ^ 2 / S) with hexdef
  have hzS : 0 ≤ ‖ζ‖ ^ 2 * S := by positivity
  have hρ2 : 0 ≤ ρ ^ 2 / S := by positivity
  have hex1 : Real.exp (Cp0 * ‖ζ‖ ^ 2 * S - (cl / 4) * ρ ^ 2 / S) ≤ ex := by
    have e1 : Cp0 * ‖ζ‖ ^ 2 * S - cl / 4 * ρ ^ 2 / S =
        Cp0 * (‖ζ‖ ^ 2 * S) - cl / 4 * (ρ ^ 2 / S) := by ring
    have e2 : Cp * ‖ζ‖ ^ 2 * S - cl' / 4 * ρ ^ 2 / S =
        Cp * (‖ζ‖ ^ 2 * S) - cl' / 4 * (ρ ^ 2 / S) := by ring
    rw [hexdef, e1, e2]
    exact clr_exp_mono hzS hρ2 (le_max_left _ _)
      (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num))
  have hex2 : Real.exp (5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S -
      (1 / (4 * (5 * Λ ^ 3))) * (ρ / 4) ^ 2 / S) ≤ ex := by
    have e1 : 5 * Λ ^ 3 * ‖ζ‖ ^ 2 * S - 1 / (4 * (5 * Λ ^ 3)) * (ρ / 4) ^ 2 / S =
        5 * Λ ^ 3 * (‖ζ‖ ^ 2 * S) - cD * (ρ ^ 2 / S) := by rw [hcDdef]; ring
    have e2 : Cp * ‖ζ‖ ^ 2 * S - cl' / 4 * ρ ^ 2 / S =
        Cp * (‖ζ‖ ^ 2 * S) - cl' / 4 * (ρ ^ 2 / S) := by ring
    rw [hexdef, e1, e2]
    exact clr_exp_mono hzS hρ2 (le_max_right _ _)
      (by
        have h := min_le_right cl (4 * cD)
        rw [← hcl'def] at h
        linarith only [h])
  have hLb : L ≤ ex * (K₀ * (2 + S) * ‖f‖) := by
    refine clr_two_term_bound (norm_nonneg f) hSpos.le hKL (Real.exp_pos _).le
      (hL1.trans hL2) ?_ hex2 (le_max_left _ _)
    have heq : d * Λ * (Cl * ((Real.sqrt (cl / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (Cl * ‖ζ‖ ^ 2 * (2 * S) - (cl / 2) * ρ ^ 2 / (2 * S)) *
          Real.sqrt (S * E₀) * ‖f‖ =
        d * Λ * (Cl * ((Real.sqrt (cl / 2) * ρ)⁻¹ + ‖ζ‖) + 2 * ‖ζ‖) *
          Real.exp (Cl * ‖ζ‖ ^ 2 * (2 * S) - (cl / 2) * ρ ^ 2 / (2 * S)) *
          Real.sqrt (S * (E₀ * ‖f‖ ^ 2)) := by
      rw [← hsq]; ring
    rw [heq]
    refine hL3.trans ?_
    rw [← hKLdef]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hex1 (by positivity))
      (norm_nonneg f)
  have hRb : Rch ≤ Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * (K₀ * (2 + S) * ‖f‖) := by
    rw [hRchdef]
    have hKK : Kc ≤ K₀ * (2 + S) := by
      have : K₀ ≤ K₀ * (2 + S) := le_mul_of_one_le_right (by positivity) (by linarith)
      exact (le_max_right _ _).trans this
    calc Kc * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖
        ≤ (K₀ * (2 + S)) * Real.exp (Cmax * ‖ζ‖ ^ 2 * S) * ‖f‖ := by gcongr
      _ = _ := by ring
  exact clr_pointwise_final hKi (le_max_of_le_left (by linarith)) hθ hθ1 hcl' hSpos
    (norm_nonneg f) hL0 hRch hLb hRb hint

end EinsteinFull
