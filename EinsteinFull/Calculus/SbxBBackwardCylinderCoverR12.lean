import EinsteinFull.Calculus.SbxBPositiveCylinderCoverR11

open EinsteinRelation EinsteinFull.External.Source.GMP

namespace EinsteinFull.Calculus

/-- A time-first presentation of a backward cylinder. -/
def sbxBBackCylinder (d : ℕ) (b R : ℝ) : Set (ℝ × Vec d) :=
  Set.Ioc b 0 ×ˢ sourceBall (0 : Vec d) R

/-- A clipped backward cylinder; both intervals include their terminal time. -/
def sbxBBackPiece {d : ℕ} (q : ℝ × Vec d) (r : ℝ) : Set (ℝ × Vec d) :=
  Set.Ioc (min 0 (q.1 + r ^ 2 / 8) - r ^ 2)
    (min 0 (q.1 + r ^ 2 / 8)) ×ˢ sourceBall q.2 r

/-- The half backward cylinder corresponding to `sbxBBackPiece`. -/
def sbxBBackHalfPiece {d : ℕ} (q : ℝ × Vec d) (r : ℝ) : Set (ℝ × Vec d) :=
  Set.Ioc (min 0 (q.1 + r ^ 2 / 8) - r ^ 2 / 4)
    (min 0 (q.1 + r ^ 2 / 8)) ×ˢ sourceBall q.2 (r / 2)

/-- Nets at a parabolic scale give backward covers, including time zero. -/
theorem sbxB_backward_cover_of_scale (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ (n : ℕ) (b b' R R' r : ℝ),
      (∀ q ∈ sbxBBackCylinder d b' R', ‖q‖ ≤ 1) →
      0 < r → r ^ 2 ≤ b' - b → 2 * r ≤ R - R' →
      δ * (1 / 4 : ℝ) ^ n ≤ (r / 2) ^ 2 / 4 →
      ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤ (r / 2) / 2 →
      ∃ F : Finset (ℝ × Vec d), F.card ≤ C * B ^ n ∧
        (∀ q ∈ F, sbxBBackPiece q r ⊆ sbxBBackCylinder d b R) ∧
        ∀ x ∈ sbxBBackCylinder d b' R', ∃ q ∈ F, x ∈ sbxBBackHalfPiece q r := by
  obtain ⟨C, B, hnet⟩ := c9_uniform_quadratic_internal_nets (E := ℝ × Vec d) δ hδ
  refine ⟨C, B, ?_⟩
  intro n b b' R R' r hbounded hr htgap hsgap htime hspace
  obtain ⟨F, hcard, hcenters, hcover⟩ := hnet n (sbxBBackCylinder d b' R') hbounded
  refine ⟨F, hcard, ?_, ?_⟩
  · intro q hq z hz
    have hq' := hcenters q hq
    have hqtime : b' < q.1 ∧ q.1 ≤ 0 := hq'.1
    have htop : min 0 (q.1 + r ^ 2 / 8) ≤ 0 := min_le_left _ _
    have htop' : q.1 ≤ min 0 (q.1 + r ^ 2 / 8) :=
      le_min hqtime.2 (by nlinarith [sq_nonneg r])
    have hs : euclideanNorm (z.2 - q.2) < r := hz.2
    have hqspace : euclideanNorm (q.2 - 0) < R' := hq'.2
    have htri := TimeChange.euclideanNorm_add_le (z.2 - q.2) (q.2 - 0)
    have heq : z.2 - 0 = (z.2 - q.2) + (q.2 - 0) := by abel
    refine ⟨⟨by linarith [hz.1.1], le_trans hz.1.2 htop⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < R
    rw [heq]
    linarith
  · intro x hx
    obtain ⟨q, hq, hdist⟩ := hcover x hx
    have hsmall := c9_product_metric_ball_in_inner_parabolic_cylinder d x q
      (r / 2) (δ * (1 / 4 : ℝ) ^ n) htime hspace hdist
    have htop : x.1 ≤ min 0 (q.1 + r ^ 2 / 8) := by
      apply le_min hx.1.2
      nlinarith [hsmall.1.2, sq_nonneg r]
    have hbottom : min 0 (q.1 + r ^ 2 / 8) - r ^ 2 / 4 < x.1 := by
      have htop' := min_le_right 0 (q.1 + r ^ 2 / 8)
      nlinarith [hsmall.1.1, sq_nonneg r]
    refine ⟨q, hq, ⟨⟨hbottom, htop⟩, ?_⟩⟩
    change euclideanNorm (x.2 - q.2) < r / 2
    have hs : euclideanNorm (x.2 - q.2) < (r / 2) / 2 := hsmall.2
    linarith

/-- A dimension-dependent polynomial bound for buffered backward covers. -/
theorem sbxB_backward_polynomial_cover (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ (g t t' R R' : ℝ),
      0 < g → g ≤ 1 →
      (∀ q ∈ sbxBBackCylinder d t' R', ‖q‖ ≤ 1) →
      (g / 32) ^ 2 ≤ t' - t → 2 * (g / 32) ≤ R - R' →
      ∃ F : Finset (ℝ × Vec d),
        (∀ x ∈ sbxBBackCylinder d t' R', ∃ q ∈ F, x ∈ sbxBBackHalfPiece q (g / 32)) ∧
        (∀ q ∈ F, sbxBBackPiece q (g / 32) ⊆ sbxBBackCylinder d t R) ∧
        (F.card : ℝ) ≤ N * g ^ (-b) := by
  let δ : ℝ := 1 / (32768 * ((d : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, B, hcover⟩ := sbxB_backward_cover_of_scale d δ hδ
  refine ⟨((max C 1 : ℕ) : ℝ) * (2 : ℝ) ^ (B + 1), (B + 1 : ℝ), ?_, ?_, ?_⟩
  · have hC : (1 : ℝ) ≤ (max C 1 : ℕ) := by exact_mod_cast (Nat.le_max_right C 1)
    have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (B + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  · positivity
  · intro g t t' R R' hg hg1 hbounded ht hs
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near_of_lt_one hg hg1
      (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 / 2 : ℝ) < 1 by norm_num)
    have hqlo : g / 2 ≤ (1 / 2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith
    have hscale := sbxB_positiveCylinder_scale d (k + 1) g hg hg1 (le_of_lt hklo)
    have htime : δ * (1 / 4 : ℝ) ^ (k + 1) ≤ (g / 32 / 2) ^ 2 / 4 := by
      dsimp [δ]
      convert hscale.1 using 1; ring
    have hspace : ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ (k + 1)) ≤ (g / 32 / 2) / 2 := by
      dsimp [δ]
      convert hscale.2 using 1; ring
    obtain ⟨F, hcard, houter, hsmall⟩ := hcover (k + 1) t t' R R' (g / 32)
      hbounded (by positivity) ht hs htime hspace
    refine ⟨F, hsmall, houter, ?_⟩
    have hc : (F.card : ℝ) ≤ ((C * B ^ (k + 1) : ℕ) : ℝ) := by exact_mod_cast hcard
    exact hc.trans (sbxB_positiveCylinder_card_bound C B (k + 1) _ hg hqlo)

/-- Unit product-norm bound for cylinders lying in the unit time-space box. -/
theorem sbxB_backCylinder_norm_le_one (d : ℕ) (t R : ℝ)
    (ht : -1 ≤ t) (hR : R ≤ 1) :
    ∀ q ∈ sbxBBackCylinder d t R, ‖q‖ ≤ 1 := by
  intro q hq
  rw [norm_prod_le_iff]
  constructor
  · rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hq.1.1], by linarith [hq.1.2]⟩
  · have h := c18_norm_le_euclideanNorm q.2
    have hs : euclideanNorm (q.2 - 0) < R := hq.2
    simp only [sub_zero] at hs
    linarith

/-- The time-first cylinders are exactly the two source cylinders. -/
theorem sbxB_backCylinder_eq_neg (d : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    sbxBBackCylinder d (-5 / 16 - (σ - 1 / 2) / 16) (5 / 8 + (σ - 1 / 2) / 4) =
      {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d σ} := by
  have hr : 0 < 5 / 8 + (σ - 1 / 2) / 4 := by linarith
  ext z
  simp only [sbxBBackCylinder, PDE.Parabolic.WeakHarnack.negCyl, Set.mem_prod,
    Set.mem_ofPred_eq, ← c8_sourceBall_eq_euclideanBall 0 hr, and_comm]

/-- The time-first inner cylinders are exactly the source inner cylinders. -/
theorem sbxB_backCylinder_eq_negInner (d : ℕ) (σ : ℝ) (hσ : 1 / 2 ≤ σ) :
    sbxBBackCylinder d (-1 / 4 - (σ - 1 / 2) / 8) (1 / 2 + (σ - 1 / 2) / 4) =
      {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d σ} := by
  have hr : 0 < 1 / 2 + (σ - 1 / 2) / 4 := by linarith
  ext z
  simp only [sbxBBackCylinder, PDE.Parabolic.WeakHarnack.negCylInner, Set.mem_prod,
    Set.mem_ofPred_eq, ← c8_sourceBall_eq_euclideanBall 0 hr, and_comm]

/-- Both negative source cylinders admit polynomially many half-backward pieces.
Every corresponding full backward piece remains inside its outer cylinder,
including at the common terminal time. -/
theorem sbxB_negative_polynomial_backward_covers (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ σ σ' : ℝ,
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ inner : Bool,
      let A : ℝ → Set (ℝ × Vec d) := fun s =>
        if inner then {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d s}
        else {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d s}
      ∃ F : Finset (ℝ × Vec d),
        (∀ x ∈ A σ', ∃ q ∈ F, x ∈ sbxBBackHalfPiece q ((σ - σ') / 32)) ∧
        (∀ q ∈ F, sbxBBackPiece q ((σ - σ') / 32) ⊆ A σ) ∧
        (F.card : ℝ) ≤ N * (σ - σ') ^ (-b) := by
  obtain ⟨N, b, hN, hb, hcover⟩ := sbxB_backward_polynomial_cover d
  refine ⟨N, b, hN, hb, ?_⟩
  intro σ σ' hlo hlt hhi inner
  have hloσ : 1 / 2 ≤ σ := by linarith
  have hg : 0 < σ - σ' := sub_pos.mpr hlt
  have hg1 : σ - σ' ≤ 1 := by linarith
  have hsquare : ((σ - σ') / 32) ^ 2 ≤ (σ - σ') / 16 := by
    nlinarith [sq_nonneg (σ - σ')]
  cases inner
  · dsimp only [Bool.false_eq_true, ↓reduceIte]
    rw [← sbxB_backCylinder_eq_neg d σ' hlo, ← sbxB_backCylinder_eq_neg d σ hloσ]
    apply hcover (σ - σ') _ _ _ _ hg hg1
    · apply sbxB_backCylinder_norm_le_one
      · linarith
      · linarith
    · linarith
    · linarith
  · dsimp only [↓reduceIte]
    rw [← sbxB_backCylinder_eq_negInner d σ' hlo, ← sbxB_backCylinder_eq_negInner d σ hloσ]
    apply hcover (σ - σ') _ _ _ _ hg hg1
    · apply sbxB_backCylinder_norm_le_one
      · linarith
      · linarith
    · linarith
    · linarith

#print axioms sbxB_negative_polynomial_backward_covers

end EinsteinFull.Calculus
