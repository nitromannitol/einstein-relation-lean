import EinsteinFull.Calculus.C9TubeSignedDyadicGainTransport
import EllipticRegularity.Parabolic.WeakHarnack.Geometry

open EinsteinRelation EinsteinFull.External.Source.GMP

namespace EinsteinFull.Calculus

/-- Positive cylinders with the time coordinate first. -/
def sbxBPositiveCoverCylinder (d : ℕ) (σ : ℝ) : Set (ℝ × Vec d) :=
  {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.posCyl d σ}

/-- The smaller positive cylinder lies in the product unit ball. -/
theorem sbxB_positiveCylinder_norm_le_one (d : ℕ) (σ : ℝ)
    (hσ₁ : 1 / 2 ≤ σ) (hσ₂ : σ ≤ 1) :
    ∀ z ∈ sbxBPositiveCoverCylinder d σ, ‖z‖ ≤ 1 := by
  intro z hz
  change z.2 ∈ PDE.euclideanBall (0 : Vec d) (1 / 2 + (σ - 1 / 2) / 2) ∧
    z.1 ∈ Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4) at hz
  have hr : 0 < 1 / 2 + (σ - 1 / 2) / 2 := by linarith
  rw [← c8_sourceBall_eq_euclideanBall 0 hr] at hz
  have hzspace : euclideanNorm (z.2 - 0) < 1 / 2 + (σ - 1 / 2) / 2 := hz.1
  rw [norm_prod_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  · have hh := c18_norm_le_euclideanNorm z.2
    simp only [sub_zero] at hzspace
    linarith

/-- Every centre in the smaller positive cylinder has the required outer buffer. -/
theorem sbxB_positiveCylinder_outer (d : ℕ) (σ σ' : ℝ)
    (hlo : 1 / 2 ≤ σ') (hlt : σ' < σ) (hhi : σ ≤ 1)
    (q : ℝ × Vec d) (hq : q ∈ sbxBPositiveCoverCylinder d σ') :
    let η := (σ - σ') / 64
    Set.Ioo (q.1 - η ^ 2) (q.1 + η ^ 2) ×ˢ sourceBall q.2 (2 * η) ⊆
      sbxBPositiveCoverCylinder d σ := by
  dsimp only
  change q.2 ∈ PDE.euclideanBall (0 : Vec d) (1 / 2 + (σ' - 1 / 2) / 2) ∧
    q.1 ∈ Set.Ioo (-3 / 4 - (σ' - 1 / 2) / 4) (-1 / 2 + (σ' - 1 / 2) / 4) at hq
  have hr' : 0 < 1 / 2 + (σ' - 1 / 2) / 2 := by linarith
  have hr : 0 < 1 / 2 + (σ - 1 / 2) / 2 := by linarith
  rw [← c8_sourceBall_eq_euclideanBall 0 hr'] at hq
  intro z hz
  change z.2 ∈ PDE.euclideanBall (0 : Vec d) (1 / 2 + (σ - 1 / 2) / 2) ∧
    z.1 ∈ Set.Ioo (-3 / 4 - (σ - 1 / 2) / 4) (-1 / 2 + (σ - 1 / 2) / 4)
  rw [← c8_sourceBall_eq_euclideanBall 0 hr]
  have hqspace : euclideanNorm (q.2 - 0) < 1 / 2 + (σ' - 1 / 2) / 2 := hq.1
  have hzspace : euclideanNorm (z.2 - q.2) < 2 * ((σ - σ') / 64) := hz.2
  have hgap : 0 < σ - σ' := sub_pos.mpr hlt
  have hgaple : σ - σ' ≤ 1 := by linarith
  have ht : ((σ - σ') / 64) ^ 2 ≤ (σ - σ') / 4 := by nlinarith [sq_nonneg (σ - σ')]
  have htri := TimeChange.euclideanNorm_add_le (z.2 - q.2) (q.2 - 0)
  have heq : z.2 - 0 = (z.2 - q.2) + (q.2 - 0) := by abel
  constructor
  · change euclideanNorm (z.2 - 0) < _
    rw [heq]
    linarith [hqspace, hzspace]
  · constructor <;> linarith [hq.2.1, hq.2.2, hz.1.1, hz.1.2]

/-- Quadratic internal nets yield finite buffered covers at any fitting scale. -/
theorem sbxB_positiveCylinder_cover_of_scale (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ (n : ℕ) (σ σ' : ℝ),
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      δ * (1 / 4 : ℝ) ^ n ≤ ((σ - σ') / 64) ^ 2 / 4 →
      ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤ ((σ - σ') / 64) / 2 →
      ∃ F : Finset (ℝ × Vec d), F.card ≤ C * B ^ n ∧
        (∀ q ∈ F, Set.Ioo (q.1 - ((σ - σ') / 64) ^ 2)
          (q.1 + ((σ - σ') / 64) ^ 2) ×ˢ
          sourceBall q.2 (2 * ((σ - σ') / 64)) ⊆ sbxBPositiveCoverCylinder d σ) ∧
        ∀ x ∈ sbxBPositiveCoverCylinder d σ', ∃ q ∈ F,
          x ∈ Set.Ioo (q.1 - ((σ - σ') / 64) ^ 2 / 4)
            (q.1 + ((σ - σ') / 64) ^ 2 / 4) ×ˢ
            sourceBall q.2 (((σ - σ') / 64) / 2) := by
  obtain ⟨C, B, hnet⟩ := c9_uniform_quadratic_internal_nets (E := ℝ × Vec d) δ hδ
  refine ⟨C, B, ?_⟩
  intro n σ σ' hlo hlt hhi htime hspace
  obtain ⟨F, hcard, hcenters, hcover⟩ := hnet n (sbxBPositiveCoverCylinder d σ')
    (sbxB_positiveCylinder_norm_le_one d σ' hlo (le_trans (le_of_lt hlt) hhi))
  refine ⟨F, hcard, ?_, ?_⟩
  · intro q hq
    exact sbxB_positiveCylinder_outer d σ σ' hlo hlt hhi q (hcenters q hq)
  · intro x hx
    obtain ⟨q, hq, hdist⟩ := hcover x hx
    exact ⟨q, hq, c9_product_metric_ball_in_inner_parabolic_cylinder d x q
      _ _ htime hspace hdist⟩

/-- A fixed dimension-dependent net tolerance fits a gap at a dyadic scale. -/
theorem sbxB_positiveCylinder_scale (d n : ℕ) (g : ℝ)
    (hg : 0 < g) (hg1 : g ≤ 1) (hq : (1 / 2 : ℝ) ^ n ≤ g) :
    let δ : ℝ := 1 / (32768 * ((d : ℝ) + 1))
    δ * (1 / 4 : ℝ) ^ n ≤ (g / 64) ^ 2 / 4 ∧
    ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤ (g / 64) / 2 := by
  dsimp only
  let D : ℝ := (d : ℝ) + 1
  have hD : 1 ≤ D := by dsimp [D]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hDp : 0 < D := by linarith
  have hδ : 1 / (32768 * D) ≤ (1 / 16384 : ℝ) := by
    rw [div_le_iff₀ (by positivity : 0 < 32768 * D)]
    nlinarith
  have hDδ : D * (1 / (32768 * D)) = 1 / 32768 := by field_simp
  have hqpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
  have hp : (1 / 4 : ℝ) ^ n = ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [hp]
  change (1 / (32768 * D)) * ((1 / 2 : ℝ) ^ n) ^ 2 ≤ _ ∧
    D * ((1 / (32768 * D)) * ((1 / 2 : ℝ) ^ n) ^ 2) ≤ _
  have hsq : ((1 / 2 : ℝ) ^ n) ^ 2 ≤ g ^ 2 := by nlinarith
  have hsqg : ((1 / 2 : ℝ) ^ n) ^ 2 ≤ g := by nlinarith
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hδ (sq_nonneg ((1 / 2 : ℝ) ^ n))]
  · rw [← mul_assoc, hDδ]
    nlinarith

/-- A geometric net bound is polynomial in the inverse gap. -/
theorem sbxB_positiveCylinder_card_bound (C B n : ℕ) (g : ℝ)
    (hg : 0 < g) (hq : g / 2 ≤ (1 / 2 : ℝ) ^ n) :
    ((C * B ^ n : ℕ) : ℝ) ≤
      ((max C 1 : ℕ) : ℝ) * (2 : ℝ) ^ (B + 1) * g ^ (-(B + 1 : ℝ)) := by
  let m := B + 1
  have hm : (B : ℝ) ≤ (2 : ℝ) ^ m := by
    have hnat : B ≤ 2 ^ m := by
      exact (Nat.le_of_lt B.lt_two_pow_self).trans (Nat.pow_le_pow_right (by decide) (by dsimp [m]; omega))
    exact_mod_cast hnat
  have hbase : (2 : ℝ) ^ n ≤ 2 / g := by
    have hpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    have hgp : 0 < g / 2 := by positivity
    have hi : ((1 / 2 : ℝ) ^ n)⁻¹ ≤ (g / 2)⁻¹ := (inv_le_inv₀ hpos hgp).2 hq
    simpa only [inv_pow, one_div, inv_inv, inv_div] using hi
  have hp : (B : ℝ) ^ n ≤ (2 / g) ^ m := by
    calc
      (B : ℝ) ^ n ≤ ((2 : ℝ) ^ m) ^ n := pow_le_pow_left₀ (by positivity) hm _
      _ = ((2 : ℝ) ^ n) ^ m := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ (2 / g) ^ m := pow_le_pow_left₀ (by positivity) hbase _
  have hC : (C : ℝ) ≤ (max C 1 : ℕ) := by exact_mod_cast (Nat.le_max_left C 1)
  rw [Nat.cast_mul, Nat.cast_pow]
  calc
    (C : ℝ) * (B : ℝ) ^ n ≤ ((max C 1 : ℕ) : ℝ) * (2 / g) ^ m :=
      mul_le_mul hC hp (by positivity) (by positivity)
    _ = ((max C 1 : ℕ) : ℝ) * (2 : ℝ) ^ (B + 1) * g ^ (-(B + 1 : ℝ)) := by
      have he : (B + 1 : ℝ) = ((B + 1 : ℕ) : ℝ) := by norm_num
      rw [he, Real.rpow_neg hg.le, Real.rpow_natCast]
      simp only [div_eq_mul_inv, mul_pow, m]
      ring

/-- Positive cylinders admit buffered parabolic covers of polynomial size. -/
theorem sbxB_positiveCylinder_polynomial_cover (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ σ σ' : ℝ,
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∃ F : Finset (ℝ × Vec d),
        (∀ x ∈ sbxBPositiveCoverCylinder d σ', ∃ q ∈ F,
          x ∈ Set.Ioo (q.1 - ((σ - σ') / 64) ^ 2 / 4)
            (q.1 + ((σ - σ') / 64) ^ 2 / 4) ×ˢ
            sourceBall q.2 (((σ - σ') / 64) / 2)) ∧
        (∀ q ∈ F, Set.Ioo (q.1 - ((σ - σ') / 64) ^ 2)
          (q.1 + ((σ - σ') / 64) ^ 2) ×ˢ
          sourceBall q.2 (2 * ((σ - σ') / 64)) ⊆ sbxBPositiveCoverCylinder d σ) ∧
        (F.card : ℝ) ≤ N * (σ - σ') ^ (-b) := by
  let δ : ℝ := 1 / (32768 * ((d : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, B, hcover⟩ := sbxB_positiveCylinder_cover_of_scale d δ hδ
  refine ⟨((max C 1 : ℕ) : ℝ) * (2 : ℝ) ^ (B + 1), (B + 1 : ℝ), ?_, ?_, ?_⟩
  · have hC : (1 : ℝ) ≤ (max C 1 : ℕ) := by exact_mod_cast (Nat.le_max_right C 1)
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (B + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  · positivity
  · intro σ σ' hlo hlt hhi
    have hg : 0 < σ - σ' := sub_pos.mpr hlt
    have hg1 : σ - σ' ≤ 1 := by linarith
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hg hg1
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    have hqlo : (σ - σ') / 2 ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith
    have hscale := sbxB_positiveCylinder_scale d (k + 1) (σ - σ') hg hg1 (le_of_lt hklo)
    obtain ⟨F, hcard, houter, hsmall⟩ := hcover (k + 1) σ σ' hlo hlt hhi hscale.1 hscale.2
    refine ⟨F, hsmall, houter, ?_⟩
    have hc : (F.card : ℝ) ≤ ((C * B ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    exact hc.trans (sbxB_positiveCylinder_card_bound C B (k + 1) _ hg hqlo)

#print axioms sbxB_positiveCylinder_polynomial_cover

end EinsteinFull.Calculus
