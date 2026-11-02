import EinsteinFull.Calculus.SunaS3PointKernelAssembly
import EinsteinFull.Calculus.S5GaussianSupport
import EinsteinFull.Calculus.S5OffDiagonalSupport
import EinsteinFull.Calculus.CLTimeRescale

/-! Deterministic point-kernel bounds, `paper/main.tex:713`. The point-kernel
construction uses the law only to obtain ellipticity and derivative bounds of
one field. Here those are hypotheses on an arbitrary field, so the bounds apply
to retained and rescaled fields with constants depending only on the dimension,
the ellipticity and the derivative bounds. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation Blueprint

/-- Deterministic positive-time C¹ smoothing for bounded force. -/
theorem clr_det_C1 (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (ω : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < (t : ℝ) →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d, ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (1 + (t : ℝ)⁻¹) ^ N * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
  obtain ⟨Cs, hCs, hs⟩ := u8_physical_high_weak_derivatives_C1_representative d
  obtain ⟨A, hA, hMA⟩ := u4Quant_finite_derivative_bound M (d + 4)
  obtain ⟨B, hB, hb⟩ := u4Quant_physical_positive_time_derivatives (M := M) (d := d)
    hΛ A hA (d + 2)
  let K : ℝ := max 1 (((d : ℝ) + 1) * Cs)
  let C : ℝ := max B (K * B)
  have hK : 1 ≤ K := le_max_left _ _
  have hC : 1 ≤ C := hB.trans (le_max_left _ _)
  refine ⟨C, d + 3, hC, ?_⟩
  intro ω hell hsm i ζ hζ P Pdag hP hPdag S hS t ht f
  have ht' : 0 < t := by exact_mod_cast ht
  obtain ⟨F₁, J₁, hF₀, hJ₀, hF₁, hJ₁, hFb₁, hJb₁⟩ := hb hell hsm hζ
    (fun k hk => hMA k (by omega)) P Pdag hP hPdag f t ht'
  have hchain : ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = S t f ∧
      (∀ p, p.length < d + 2 + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F p) (fun j => F (p ++ [j]))) ∧
      ∀ p, p.length ≤ d + 2 + 2 → ‖F p‖ ≤
        B * (1 + (t : ℝ)⁻¹) ^ (d + 2 + 1) * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl
    · exact ⟨F₁, hF₀, hF₁, hFb₁⟩
    · exact ⟨J₁, hJ₀, hJ₁, hJb₁⟩
  obtain ⟨F, hF0, hF, hFb⟩ := hchain
  let R : ℝ := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
    Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF' : ∀ p, p.length < d + 4 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])) := by
    intro p hp; apply hF; omega
  have hFb' : ∀ p, p.length ≤ d + 4 → ‖F p‖ ≤ R := by
    intro p hp; apply hFb; omega
  obtain ⟨u, hu, hue, hub⟩ := hs F R hR (fun p hp => hF' p (by omega))
    (fun p hp => hFb' p (by omega))
  have hcoord := u4Quant_sobolev_coordinate_bound Cs R hR hs F hF' hFb' u hu hue
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hF0] using hue
  · intro x
    have ha : 0 ≤ Cs * R := mul_nonneg hCs.le hR
    have hsums : (∑ j : Fin d, ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤
        (d : ℝ) * (Cs * R) ^ 2 := by
      calc
        _ ≤ ∑ _j : Fin d, (Cs * R) ^ 2 := Finset.sum_le_sum (fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (hcoord x j) 2)
        _ = _ := by simp
    have hsqrt : Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤ (d : ℝ) * (Cs * R) := by
      apply (Real.sqrt_le_iff).2
      constructor
      · positivity
      · rcases Nat.eq_zero_or_pos d with hd0 | hd0
        · subst hd0; simp
        · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
          nlinarith [sq_nonneg (Cs * R)]
    have hpoint : ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (u : Vec d → ℂ) x (unitVector j)‖ ^ 2) ≤ K * R := by
      have hv := u.norm_coe_le_norm x
      have hk := le_max_right (1 : ℝ) (((d : ℝ) + 1) * Cs)
      nlinarith [mul_le_mul_of_nonneg_right hk hR]
    exact hpoint.trans (by simpa only [R, C] using
      (u4Quant_C1_constant_inflation K B hB (d + 3) (t : ℝ) (‖ζ‖ ^ 2) ‖f‖
        ht (sq_nonneg _) (norm_nonneg f)))

/-- Deterministic Gaussian off-diagonal bound on a unit ball. -/
theorem clr_det_unit_ball_L2 (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d), IsElliptic Λ ω.1 →
    ∀ (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))),
    IsPhysicalComplexSemigroup ω.1 i ζ P →
    IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ (E : Set (Vec d)), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∀ (x : Vec d) (ell : ℝ),
    (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
    (eLpNorm ({z : Vec d | euclideanNorm (x - z) < 1}.indicator (fun z => S t f z))
        2 volume).toReal ≤
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖ := by
  have hΛ0 : 0 < Λ := by linarith
  have hC : 0 < 5 * Λ ^ 3 := by positivity
  refine ⟨5 * Λ ^ 3, 1 / (4 * (5 * Λ ^ 3)), ?_, by positivity, ?_⟩
  · have h1 : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ
    linarith
  intro ω hell i ζ P Pdag hP hPd S hS t ht E hE f hf x ell hsep
  have hell' := s5Elliptic_of_isElliptic hΛ hell
  have hmeas : ∀ j k, Measurable fun x => ω.1 x j k := fun j k =>
    (ω.1.continuous.matrix_elem j k).measurable
  have ht' : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hS' : S = P ∨ S = Pdag := by simpa using hS
  have hW : ∀ (q : ℝ) (ψ : Vec d → ℝ), (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume →
        MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S t f) x) 2 volume ∧
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S t f) x) 2 volume).toReal ≤
            Real.exp (5 * Λ ^ 3 * (‖ζ‖ ^ 2 + q ^ 2) * (t : ℝ)) *
              (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal := by
    intro q ψ hψ f hf
    rcases hS' with rfl | rfl
    · exact s5_weighted_forward hell' hmeas i ζ hP t q hψ f hf
    · exact s5_weighted_transpose hell' hmeas i ζ hPd t q hψ f hf
  have hcont : Continuous (fun z : Vec d => euclideanNorm (x - z)) :=
    (Entropy.continuous_euclideanNorm' (d := d)).comp (continuous_const.sub continuous_id)
  have hB : MeasurableSet {z : Vec d | euclideanNorm (x - z) < 1} :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hdist : ∀ y ∈ E, ∀ z ∈ {z : Vec d | euclideanNorm (x - z) < 1},
      max (ell - 1) 0 ≤ euclideanNorm (y - z) := by
    intro y hy z hz
    apply max_le
    · have htri := TimeChange.euclideanNorm_add_le (x - z) (z - y)
      rw [sub_add_sub_cancel, ← neg_sub y z, Entropy.euclideanNorm_neg'] at htri
      have hy' := hsep y hy
      change euclideanNorm (x - z) < 1 at hz
      linarith
    · exact Real.sqrt_nonneg _
  exact (s5_gaussian_of_weighted hC ht' (S t) hW E _ hB
    (max (ell - 1) 0) (le_max_right _ _) hdist f hf).2

/-- Deterministic local C¹ interpolation of a positive-time evolution. -/
theorem clr_det_local_interpolation (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ B K θ : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (ω : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    let R := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d,
      let L : ℝ := (eLpNorm
        ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ K * (L ^ θ * R ^ (1 - θ) + L) := by
  obtain ⟨Cs, _, hs⟩ := u8_physical_high_weak_derivatives_C1_representative d
  obtain ⟨K, θ, hK, hθ, hθ1, hl⟩ :=
    u4_local_C1_interpolation_of_global_chain u8_global_C1_interpolation_of_weak_derivative_chain d
  obtain ⟨A, hA, hMA⟩ := u4Quant_finite_derivative_bound M (d + 4)
  obtain ⟨B, hB, hb⟩ := u4Quant_physical_positive_time_derivatives (M := M) (d := d)
    hΛ A hA (d + 2)
  refine ⟨B, K, θ, hB, hK, hθ, hθ1, ?_⟩
  intro ω hell hsm i ζ hζ P Pdag hP hPdag S hS t ht f
  dsimp only
  obtain ⟨F₁, J₁, hF₀, hJ₀, hF₁, hJ₁, hFb₁, hJb₁⟩ := hb hell hsm hζ
    (fun k hk => hMA k (by omega)) P Pdag hP hPdag f t ht
  have hchain : ∃ F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
      F [] = S t f ∧
      (∀ p, p.length < d + 2 + 2 → IsPhysicalH1Graph volume (Or.inl rfl)
        (F p) (fun j => F (p ++ [j]))) ∧
      ∀ p, p.length ≤ d + 2 + 2 → ‖F p‖ ≤
        B * (1 + (t : ℝ)⁻¹) ^ (d + 2 + 1) * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ := by
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hS
    rcases hS with rfl | rfl
    · exact ⟨F₁, hF₀, hF₁, hFb₁⟩
    · exact ⟨J₁, hJ₀, hJ₁, hJb₁⟩
  obtain ⟨F, hF0, hF, hFb⟩ := hchain
  let R : ℝ := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
    Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF' : ∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])) := by
    intro p hp
    exact hF p (by omega)
  have hFb' : ∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R := by
    intro p hp
    exact hFb p (by omega)
  obtain ⟨u, hu, hue, _⟩ := hs F R hR hF' hFb'
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hF0] using hue
  · exact hl F R hR hF' hFb' u hu hue

/-- Deterministic localized C¹ interpolation combined with the unit-ball
off-diagonal bound. -/
theorem clr_det_local_C1_interpolated (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ B K θ C c : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ E : Set (Vec d), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    let R := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ (x : Vec d) (ell : ℝ),
      (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
      let A := Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
        c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ K * (A ^ θ * R ^ (1 - θ) + A) := by
  obtain ⟨B, K, θ, hB, hK, hθ, hθ1, hI⟩ := clr_det_local_interpolation d Λ hΛ M
  obtain ⟨C, c, hC, hc, hO⟩ := clr_det_unit_ball_L2 d Λ hΛ
  refine ⟨B, K, θ, C, c, hB, hK, hθ, hθ1, hC, hc, ?_⟩
  intro ω hell hsm i ζ hζ P Pdag hP hPdag S hS t ht E hE f hf
  have hIω := hI ω hell hsm
  have hOω := hO ω hell
  dsimp only
  obtain ⟨u, hu, hue, hub⟩ := hIω i ζ hζ P Pdag hP hPdag S hS t ht f
  refine ⟨u, hu, hue, ?_⟩
  intro x ell hsep
  have hbound := hOω i ζ P Pdag hP hPdag S hS t ht E hE f hf x ell hsep
  have heq : ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) =ᵐ[volume]
      ({z : Vec d | euclideanNorm (x - z) < 1}.indicator (fun z => S t f z)) := by
    filter_upwards [hue] with z hz
    by_cases hzB : euclideanNorm (x - z) < 1 <;> simp [Set.indicator, hzB, hz]
  have hL : (eLpNorm ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal ≤
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖ := by
    rw [eLpNorm_congr_ae heq]
    exact hbound
  have hp := Real.rpow_le_rpow (ENNReal.toReal_nonneg) hL hθ.le
  have hR : 0 ≤ (B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖) ^ (1 - θ) := Real.rpow_nonneg (by positivity) _
  exact (hub x).trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hp hR) hL) hK.le)


/-- Deterministic localized C¹ Gaussian bound at times at least one. -/
theorem clr_det_local_C1_gaussian (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
    ∀ E : Set (Vec d), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ (x : Vec d) (ell : ℝ), 0 ≤ ell →
      (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ell ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨B, K, θ, C, c, hB, hK, hθ, hθ1, hC, hc, h⟩ :=
    clr_det_local_C1_interpolated d Λ hΛ M
  let m : ℝ := B * 2 ^ (d + 3)
  let C' : ℝ := max (max B C) (max 1 (K * (m + 1) * Real.exp c))
  have hm : 1 ≤ m := by
    dsimp [m]
    have hp : 1 ≤ (2 : ℝ) ^ (d + 3) := one_le_pow₀ (by norm_num)
    nlinarith
  have hC' : 1 ≤ C' := (le_max_left 1 _).trans (le_max_right _ _)
  have hC'B : B ≤ C' := (le_max_left B C).trans (le_max_left _ _)
  have hC'C : C ≤ C' := (le_max_right B C).trans (le_max_left _ _)
  have hC'K : K * (m + 1) * Real.exp c ≤ C' :=
    (le_max_right 1 _).trans (le_max_right _ _)
  refine ⟨C', θ * c / 2, 0, hC', by positivity, ?_⟩
  intro ω hell hsm i ζ hζ P Pdag hP hPdag S hS t ht E hE f hf
  have hω := h ω hell hsm
  have htpos : 0 < (t : ℝ) := by linarith
  obtain ⟨u, hu, hue, hub⟩ := hω i ζ hζ P Pdag hP hPdag S hS t
    (by exact_mod_cast htpos) E hE f hf
  refine ⟨u, hu, hue, ?_⟩
  intro x ell hell hsep
  have hinv : (t : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ htpos).2 ht
  have hbase : 0 ≤ 1 + (t : ℝ)⁻¹ := by positivity
  have hpow : (1 + (t : ℝ)⁻¹) ^ (d + 3) ≤ (2 : ℝ) ^ (d + 3) :=
    pow_le_pow_left₀ hbase (by linarith) _
  let p : ℝ := C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)
  let q : ℝ := B * ‖ζ‖ ^ 2 * (t : ℝ)
  let g : ℝ := C' * ‖ζ‖ ^ 2 * (t : ℝ) - (θ * c / 2) * ell ^ 2 / (t : ℝ)
  have hR : B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖ ≤
      m * Real.exp q * ‖f‖ := by
    dsimp [m]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ B))
        (Real.exp_pos q).le) (norm_nonneg _)
  have hR0 : 0 ≤ B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖ := by positivity
  have hrpow := Real.rpow_le_rpow hR0 hR (by linarith : 0 ≤ 1 - θ)
  have hpq0 := u4_unit_ball_gaussian_exponent B C c θ (‖ζ‖ ^ 2) (t : ℝ) ell
    hc.le hθ.le hθ1.le (sq_nonneg _) ht hell
  have hmax : max B C ≤ C' := max_le hC'B hC'C
  have hzt : 0 ≤ ‖ζ‖ ^ 2 * (t : ℝ) := by positivity
  have hpq : θ * p + (1 - θ) * q ≤ g + c := by
    dsimp [p, q, g]
    have := mul_nonneg (sub_nonneg.mpr hmax) hzt
    nlinarith
  have hp0 := u4_unit_ball_gaussian_exponent C C c 1 (‖ζ‖ ^ 2) (t : ℝ) ell
    hc.le (by norm_num) (by norm_num) (sq_nonneg _) ht hell
  have hdecay : 0 ≤ (1 - θ) * c * ell ^ 2 / (t : ℝ) := by positivity
  have hp : p ≤ g + c := by
    dsimp [p, g]
    simp only [max_self] at hp0
    have := mul_nonneg (sub_nonneg.mpr hC'C) hzt
    simp only [div_eq_mul_inv] at hp0 hdecay ⊢
    nlinarith
  have hscalar := u4_interpolation_common_exponential m p q g c θ ‖f‖
    hm (norm_nonneg _) hθ hθ1 hp hpq
  have hfirst := hub x ell hsep
  dsimp only at hfirst
  have hstep : ‖u x‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
      K * ((Real.exp p * ‖f‖) ^ θ * (m * Real.exp q * ‖f‖) ^ (1 - θ) +
        Real.exp p * ‖f‖) := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    change (Real.exp p * ‖f‖) ^ θ *
      (B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖) ^ (1 - θ) +
      Real.exp p * ‖f‖ ≤ _
    exact add_le_add
      (mul_le_mul_of_nonneg_left hrpow
        (Real.rpow_nonneg (mul_nonneg (Real.exp_pos p).le (norm_nonneg f)) θ)) (le_refl _)
  have hlast := mul_le_mul_of_nonneg_left hscalar hK.le
  have hcoeff := mul_le_mul_of_nonneg_right hC'K
    (mul_nonneg (Real.exp_pos g).le (norm_nonneg f))
  dsimp [g] at hstep hlast hcoeff ⊢
  simp only [pow_zero, mul_one]
  nlinarith

/-- Deterministic point-kernel bounds: the conclusion of the point-kernel node
for any smooth elliptic field, with constants depending only on the dimension,
the ellipticity and the derivative bounds. -/
theorem clr_det_point_kernel (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (env : FieldPair d), IsElliptic Λ env.1 → IsSmoothWithBounds M env →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup env.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup env.1 i ζ P Pdag →
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ H ∈ [K, fun t x y => K t y x],
      ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) →
        ContDiff ℝ 1 (fun z : Vec d × Vec d => H t z.1 z.2) ∧
        (∀ x y : Vec d,
          ‖H t x y‖ +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ^ 2) +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t x z) y (unitVector j)‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
              c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
          AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
          let u := fun x => ∫ y, H t x y * f y
          Differentiable ℝ u ∧ ∀ x : Vec d,
            Integrable (fun y => H t x y * f y) ∧
            (∀ j : Fin d,
              Integrable (fun y =>
                fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
              fderiv ℝ u x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
            ‖u x‖ + Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) := by
  obtain ⟨C₁, N₁, hC₁, hc1⟩ := clr_det_C1 d Λ hΛ M
  obtain ⟨C₀, c₀, N₀, hC₀, hc₀, hlocalized⟩ := clr_det_local_C1_gaussian d Λ hΛ M
  let b := c₀ / 2
  let W : ℝ := 1 + Real.sqrt d
  let A : ℝ := 4 * W * C₀^2
  let M : ℝ := Real.sqrt (Real.pi / b)^d
  let C : ℝ := max 1 (max C₀ (max A (W*A*M)))
  have hb : 0 < b := by dsimp [b]; linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAC : A ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hWAMC : W*A*M ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨C, b, N₀+N₀+d, hC, hb, ?_⟩
  intro env hell hsm
  have hsmooth := hc1 env hell hsm
  have hlocal := hlocalized env hell hsm
  intro i ζ hζ P Pdag hP hPdag
  have hsmooth' : ∀ S ∈ [P,Pdag], ∀ s : ℝ≥0, 0 < s →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (S s f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖^2) ≤ A * ‖f‖ := by
    intro S hS s hs
    refine ⟨C₁ * (1 + (s:ℝ)⁻¹)^N₁ * (2+(s:ℝ))^N₁ *
      Real.exp (C₁*‖ζ‖^2*(s:ℝ)), ?_, ?_⟩
    · positivity
    · exact hsmooth i ζ hζ P Pdag hP hPdag S hS s (by exact_mod_cast hs)
  obtain ⟨K, hpair, hlarge⟩ := s3_all_time_kernel_of_localized env.1 i ζ P Pdag
    hP hPdag hsmooth' C₀ c₀ N₀ (by linarith) (hlocal i ζ hζ P Pdag hP hPdag)
  refine ⟨K, hpair, ?_⟩
  intro H hH t ht
  have htpos : 0 < (t:ℝ) := by linarith
  let T : ℝ := (t:ℝ)
  let q : ℝ := ‖ζ‖^2
  let G : ℝ := A * (2+T)^(N₀+N₀) * Real.exp (C₀*q*T)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hbt : 0 < b/T := div_pos hb htpos
  have hraw : ∀ x y, ‖K t x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖^2) +
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector j)‖^2) ≤
      G * Real.exp (-(b/T)*euclideanNorm (x-y)^2) := by
    intro x y
    convert (hlarge t ht).2 x y using 1; dsimp [G, A, W, b, T, q]
    rw [show C₀*‖ζ‖^2*(t:ℝ) - (c₀/2)*euclideanNorm (x-y)^2/(t:ℝ) =
      C₀*‖ζ‖^2*(t:ℝ) + (-(c₀/2)*euclideanNorm (x-y)^2/(t:ℝ)) by ring,
      Real.exp_add]
    ring
  have horient : (fun x y => H t x y) ∈ [K t, fun x y => K t y x] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hH ⊢
    rcases hH with rfl | rfl <;> simp
  obtain ⟨hjoint, hbound, haction⟩ :=
    s3_both_bounded_data_actions (K t) G (b/T) hG hbt (hlarge t ht).1 hraw _ horient
  refine ⟨hjoint, ?_, ?_⟩
  · intro x y
    apply (hbound x y).trans
    have h := s3_enlarge_gaussian_bound A C C₀ q T b (euclideanNorm (x-y))
      (N₀+N₀) d hA hAC hC₀C (by dsimp [q]; positivity) htpos.le
    convert h using 1; dsimp [G, T, q]
    rw [show C₀*‖ζ‖^2*(t:ℝ)-b*euclideanNorm (x-y)^2/(t:ℝ) =
      C₀*‖ζ‖^2*(t:ℝ) + (-(b/(t:ℝ))*euclideanNorm (x-y)^2) by ring,
      Real.exp_add]
    ring
  · intro f B hB hf hfb
    obtain ⟨hderiv, hbound⟩ := haction f B hB hf hfb
    refine ⟨hderiv, ?_⟩
    intro x
    obtain ⟨hint, hj, hestimate⟩ := hbound x
    refine ⟨hint, hj, hestimate.trans ?_⟩
    have hmass := s3_absorb_gaussian_mass (W*A) C C₀ q T b (N₀+N₀) d
      (mul_nonneg hW hA) hb htpos (by dsimp [q]; positivity)
      (by simpa [M] using hWAMC) hC₀C
    have hmassB := mul_le_mul_of_nonneg_right hmass hB
    convert hmassB using 1; dsimp [G, W, T, q]; ring

/-- Halving the coefficient field, keeping the clock field. -/
noncomputable def clrHalfPair {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  (⟨fun x => ((1 / 2 : ℝ≥0) : ℝ) • ω.1 x, by fun_prop⟩, ω.2)

theorem clrHalfPair_coe {d : ℕ} (ω : FieldPair d) :
    ((clrHalfPair ω).1 : Vec d → Mat d) = fun x => ((1 / 2 : ℝ≥0) : ℝ) • ω.1 x := rfl

/-- The halved field is elliptic with twice the constant. -/
theorem clrHalfPair_elliptic {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d}
    (h : IsElliptic Λ ω.1) : IsElliptic (2 * Λ) (clrHalfPair ω).1 := by
  have hΛ0 : 0 < Λ := by linarith
  have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  intro x
  obtain ⟨hs, hξ⟩ := h x
  have hdot (ξ : Vec d) : dot ξ ((((1 / 2 : ℝ≥0) : ℝ) • ω.1 x).mulVec ξ) =
      (1 / 2) * dot ξ ((ω.1 x).mulVec ξ) := by
    rw [Matrix.smul_mulVec, hhalf]
    unfold dot
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  refine ⟨?_, fun ξ => ?_⟩
  · change (((1 / 2 : ℝ≥0) : ℝ) • ω.1 x).transpose = ((1 / 2 : ℝ≥0) : ℝ) • ω.1 x
    rw [Matrix.transpose_smul, hs]
  · change (2 * Λ)⁻¹ * euclideanSq ξ ≤ dot ξ ((((1 / 2 : ℝ≥0) : ℝ) • ω.1 x).mulVec ξ) ∧
      dot ξ ((((1 / 2 : ℝ≥0) : ℝ) • ω.1 x).mulVec ξ) ≤ 2 * Λ * euclideanSq ξ
    rw [hdot]
    obtain ⟨hlo, hhi⟩ := hξ ξ
    have hsq : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    constructor
    · have : (2 * Λ)⁻¹ * euclideanSq ξ = (1 / 2) * (Λ⁻¹ * euclideanSq ξ) := by
        rw [mul_inv]; ring
      rw [this]
      linarith
    · nlinarith

/-- The halved field keeps the derivative bounds. -/
theorem clrHalfPair_smooth {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (h : IsSmoothWithBounds M ω) : IsSmoothWithBounds M (clrHalfPair ω) := by
  obtain ⟨⟨hs1, hs2⟩, hb⟩ := h
  have hhalf : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  refine ⟨⟨fun j k => ?_, hs2⟩, fun k hk => ?_⟩
  · change ContDiff ℝ (⊤ : ℕ∞) (fun x => ((1 / 2 : ℝ≥0) : ℝ) • ω.1 x j k)
    exact (hs1 j k).const_smul _
  · obtain ⟨A, B, hA, hB, hAB, h1, h2⟩ := hb k hk
    refine ⟨A / 2, B, by positivity, hB, by linarith, ?_, h2⟩
    intro x v ξ
    have hder (i j : Fin d) : iteratedFDeriv ℝ k (fun y => (clrHalfPair ω).1 y i j) x v =
        (1 / 2 : ℝ) * iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v := by
      change iteratedFDeriv ℝ k (fun y => ((1 / 2 : ℝ≥0) : ℝ) • ω.1 y i j) x v = _
      rw [iteratedFDeriv_const_smul_apply'
        ((hs1 i j).contDiffAt.of_le (by exact_mod_cast le_top)), hhalf]
      rfl
    have hmv : Matrix.mulVec (fun i j => iteratedFDeriv ℝ k (fun y => (clrHalfPair ω).1 y i j)
        x v) ξ = (1 / 2 : ℝ) • Matrix.mulVec (fun i j =>
          iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) ξ := by
      funext i
      simp only [Matrix.mulVec, dotProduct, hder, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hmv, TimeChange.euclideanNorm_smul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have := h1 x v ξ
    calc 1 / 2 * euclideanNorm (Matrix.mulVec (fun i j =>
          iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) ξ)
        ≤ 1 / 2 * (A * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ) := by gcongr
      _ = A / 2 * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ := by ring

/-- Deterministic point-kernel bounds at all times at least one, through the
halved field at doubled time. -/
theorem clr_det_point_kernel_unit (d : ℕ) (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M : ℕ → ℝ) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (env : FieldPair d), IsElliptic Λ env.1 → IsSmoothWithBounds M env →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup env.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup env.1 i ζ P Pdag →
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel P Pdag K ∧
      ∀ H ∈ [K, fun t x y => K t y x], ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) →
        ContDiff ℝ 1 (fun z : Vec d × Vec d => H t z.1 z.2) ∧
        (∀ x y : Vec d,
          ‖H t x y‖ +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t z y) x (unitVector j)‖ ^ 2) +
            Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ (fun z => H t x z) y (unitVector j)‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
              c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
          AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
          let u := fun x => ∫ y, H t x y * f y
          Differentiable ℝ u ∧ ∀ x : Vec d,
            Integrable (fun y => H t x y * f y) ∧
            (∀ j : Fin d,
              Integrable (fun y =>
                fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
              fderiv ℝ u x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => H t z y) x (unitVector j) * f y) ∧
            ‖u x‖ + Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) := by
  obtain ⟨C₀, c₀, N, hC₀, hc₀, hk⟩ := clr_det_point_kernel d hd (2 * Λ) (by linarith) M
  refine ⟨2 ^ N * (2 * C₀), c₀ / 2, N, ?_, by positivity, ?_⟩
  · have h1 : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
    nlinarith
  intro env hell hsm i ζ hζ P Pdag hP hPdag
  have hκ : (0 : ℝ≥0) < 1 / 2 := by norm_num
  obtain ⟨hP2, hPdag2⟩ := clr_physical_time_rescale (1 / 2 : ℝ≥0) hκ hP hPdag
  obtain ⟨K₀, hK₀, hb⟩ := hk (clrHalfPair env) (clrHalfPair_elliptic hΛ hell)
    (clrHalfPair_smooth hsm) i ζ hζ _ _ hP2 hPdag2
  have hhalf (t : ℝ≥0) : (1 / 2 : ℝ≥0) * (2 * t) = t := by
    rw [← mul_assoc]; norm_num
  refine ⟨fun t => K₀ (2 * t), ?_, ?_⟩
  · intro t ht f
    have h2 : 0 < 2 * t := by positivity
    have h := hK₀ (2 * t) h2 f
    simp only [hhalf] at h
    exact h
  · have key : ∀ H₀ ∈ [K₀, fun t x y => K₀ t y x], ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) →
            ContDiff ℝ 1 (fun z : Vec d × Vec d => H₀ (2 * t) z.1 z.2) ∧
            (∀ x y : Vec d,
              ‖H₀ (2 * t) x y‖ +
                Real.sqrt (∑ j : Fin d,
                  ‖fderiv ℝ (fun z => H₀ (2 * t) z y) x (unitVector j)‖ ^ 2) +
                Real.sqrt (∑ j : Fin d,
                  ‖fderiv ℝ (fun z => H₀ (2 * t) x z) y (unitVector j)‖ ^ 2) ≤
              (2 ^ N * (2 * C₀)) * (2 + (t : ℝ)) ^ N *
                Real.exp ((2 ^ N * (2 * C₀)) * ‖ζ‖ ^ 2 * (t : ℝ) -
                  (c₀ / 2) * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
            (∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
              AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
              let u := fun x => ∫ y, H₀ (2 * t) x y * f y
              Differentiable ℝ u ∧ ∀ x : Vec d,
                Integrable (fun y => H₀ (2 * t) x y * f y) ∧
                (∀ j : Fin d,
                  Integrable (fun y =>
                    fderiv ℝ (fun z => H₀ (2 * t) z y) x (unitVector j) * f y) ∧
                  fderiv ℝ u x (unitVector j) =
                    ∫ y, fderiv ℝ (fun z => H₀ (2 * t) z y) x (unitVector j) * f y) ∧
                ‖u x‖ + Real.sqrt (∑ j : Fin d,
                  ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
                  (2 ^ N * (2 * C₀)) * (2 + (t : ℝ)) ^ N * Real.exp ((2 ^ N * (2 * C₀)) * ‖ζ‖ ^ 2 * (t : ℝ)) * B)  := by
      intro H₀ hH₀ t ht
      have ht2 : 2 ≤ ((2 * t : ℝ≥0) : ℝ) := by push_cast; linarith
      obtain ⟨hj, hbd, hact⟩ := hb H₀ hH₀ (2 * t) ht2
      have htpos : 0 < (t : ℝ) := by linarith
      have hpow : (2 + ((2 * t : ℝ≥0) : ℝ)) ^ N ≤ 2 ^ N * (2 + (t : ℝ)) ^ N := by
        rw [← mul_pow]
        apply pow_le_pow_left₀ (by positivity)
        push_cast; linarith
      have hexp (r : ℝ) (hr : 0 ≤ r) :
          Real.exp (C₀ * ‖ζ‖ ^ 2 * ((2 * t : ℝ≥0) : ℝ) - c₀ * r / ((2 * t : ℝ≥0) : ℝ)) ≤
          Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ) - c₀ / 2 * r / (t : ℝ)) := by
        apply Real.exp_le_exp.mpr
        push_cast
        have h1 : c₀ * r / (2 * (t : ℝ)) = c₀ / 2 * r / (t : ℝ) := by field_simp
        have h2 : C₀ * ‖ζ‖ ^ 2 * (2 * (t : ℝ)) ≤ 2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ) := by
          have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
          have hz : 0 ≤ 2 * C₀ * ‖ζ‖ ^ 2 * (t : ℝ) := by positivity
          nlinarith
        linarith
      have hCbig : C₀ ≤ 2 ^ N * (2 * C₀) := by
        have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
        nlinarith
      refine ⟨hj, fun x y => (hbd x y).trans ?_, fun f B hB hf hfb => ?_⟩
      · calc C₀ * (2 + ((2 * t : ℝ≥0) : ℝ)) ^ N * Real.exp (C₀ * ‖ζ‖ ^ 2 * ((2 * t : ℝ≥0) : ℝ) -
              c₀ * euclideanNorm (x - y) ^ 2 / ((2 * t : ℝ≥0) : ℝ))
            ≤ C₀ * (2 ^ N * (2 + (t : ℝ)) ^ N) * Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ) -
              c₀ / 2 * euclideanNorm (x - y) ^ 2 / (t : ℝ)) :=
              mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith)) (hexp _ (sq_nonneg _))
                (Real.exp_pos _).le (by positivity)
          _ ≤ 2 ^ N * (2 * C₀) * (2 + (t : ℝ)) ^ N * Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 *
              (t : ℝ) - c₀ / 2 * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := by
              have hE : 0 ≤ Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ) -
                c₀ / 2 * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := (Real.exp_pos _).le
              have hT : 0 ≤ (2 + (t : ℝ)) ^ N := by positivity
              nlinarith [mul_nonneg hT hE, mul_nonneg (mul_nonneg hT hE) (by positivity : (0:ℝ) ≤ 2 ^ N * C₀)]
      · obtain ⟨hd', hx⟩ := hact f B hB hf hfb
        refine ⟨hd', fun x => ?_⟩
        obtain ⟨h1, h2, h3⟩ := hx x
        refine ⟨h1, h2, h3.trans ?_⟩
        have he : Real.exp (C₀ * ‖ζ‖ ^ 2 * ((2 * t : ℝ≥0) : ℝ)) ≤
            Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
          have := hexp 0 le_rfl
          simpa using this
        calc C₀ * (2 + ((2 * t : ℝ≥0) : ℝ)) ^ N * Real.exp (C₀ * ‖ζ‖ ^ 2 *
              ((2 * t : ℝ≥0) : ℝ)) * B
            ≤ C₀ * (2 ^ N * (2 + (t : ℝ)) ^ N) *
              Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) * B :=
              mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by linarith))
                he (Real.exp_pos _).le (by positivity)) hB
          _ ≤ 2 ^ N * (2 * C₀) * (2 + (t : ℝ)) ^ N *
              Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
              have hE : 0 ≤ Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) := (Real.exp_pos _).le
              have hT : 0 ≤ (2 + (t : ℝ)) ^ N := by positivity
              have hX : 0 ≤ (2 + (t : ℝ)) ^ N * Real.exp (2 ^ N * (2 * C₀) * ‖ζ‖ ^ 2 * (t : ℝ)) * B :=
                by positivity
              nlinarith [mul_nonneg hX (by positivity : (0:ℝ) ≤ 2 ^ N * C₀)]

    intro H hH t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl
    · exact key K₀ (by simp) t ht
    · exact key (fun t x y => K₀ t y x) (by simp) t ht
end EinsteinFull
