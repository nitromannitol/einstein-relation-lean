import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open EinsteinRelation

namespace EinsteinFull.Calculus

/-- A time interval can be subdivided so that the duration of each substep is
below both native time caps and the squared spatial increment is no larger
than that duration. -/
theorem b_exists_capped_native_substeps (h r δ S D : ℝ)
    (hh : 0 < h) (hr : 0 < r) (hδ : 0 < δ) (hS : 0 < S) (_hD : 0 ≤ D) :
    ∃ n : ℕ, 0 < n ∧ 0 < h / (n : ℝ) ∧
      h / (n : ℝ) ≤ δ * r ^ 2 ∧ h / (n : ℝ) ≤ S ^ 2 / 64 ∧
      (D / (n : ℝ)) ^ 2 ≤ h / (n : ℝ) := by
  have hcap₁ : 0 < δ * r ^ 2 := by positivity
  have hcap₂ : 0 < S ^ 2 / 64 := by positivity
  have ha : 0 ≤ h / (δ * r ^ 2) := by positivity
  have hb : 0 ≤ h / (S ^ 2 / 64) := by positivity
  have hc : 0 ≤ D ^ 2 / h := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt
    (1 + h / (δ * r ^ 2) + h / (S ^ 2 / 64) + D ^ 2 / h)
  have hnpos : 0 < (n : ℝ) := by linarith
  have hnNat : 0 < n := by exact_mod_cast hnpos
  have ha' : h / (δ * r ^ 2) ≤ (n : ℝ) := by linarith
  have hb' : h / (S ^ 2 / 64) ≤ (n : ℝ) := by linarith
  have hc' : D ^ 2 / h ≤ (n : ℝ) := by linarith
  refine ⟨n, hnNat, div_pos hh hnpos, ?_, ?_, ?_⟩
  · apply (div_le_iff₀ hnpos).2
    nlinarith [(div_le_iff₀ hcap₁).1 ha']
  · apply (div_le_iff₀ hnpos).2
    nlinarith [(div_le_iff₀ hcap₂).1 hb']
  · rw [div_pow]
    apply (div_le_iff₀ (pow_pos hnpos 2)).2
    calc
      D ^ 2 ≤ (n : ℝ) * h := (div_le_iff₀ hh).1 hc'
      _ = (h / (n : ℝ)) * (n : ℝ) ^ 2 := by
        field_simp

/-- The points at equally spaced parameters of a Euclidean segment. -/
@[nolint defsWithUnderscore]
noncomputable def b_tube_segment_center {d : ℕ} (x y : Vec d) (n k : ℕ) : Vec d :=
  (1 - (k : ℝ) / (n : ℝ)) • x + ((k : ℝ) / (n : ℝ)) • y

/-- Distances on a segment scale by the absolute change of parameter. -/
theorem b_tube_segment_distance {d : ℕ} (x y : Vec d) (u v : ℝ) :
    euclideanNorm ((1-v) • x + v • y - ((1-u) • x + u • y)) =
      |v-u| * euclideanNorm (y-x) := by
  have hid : (1-v) • x + v • y - ((1-u) • x + u • y) =
      (v-u) • (y-x) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hid, TimeChange.euclideanNorm_smul]

/-- Consecutive centers have native squared distance whenever the segment
length and the subdivision satisfy the corresponding scalar bound. -/
theorem b_equispaced_segment_step {d : ℕ} (x y : Vec d) (n k : ℕ)
    (D τ : ℝ) (hn : 0 < n) (hD : 0 ≤ D)
    (hxy : euclideanNorm (y-x) ≤ D) (hτ : (D / (n : ℝ)) ^ 2 ≤ τ) :
    euclideanNorm (b_tube_segment_center x y n (k+1) -
      b_tube_segment_center x y n k) ^ 2 ≤ τ := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgap : ((k+1 : ℕ) : ℝ) / (n : ℝ) - (k : ℝ) / (n : ℝ) =
      (n : ℝ)⁻¹ := by
    push_cast
    ring
  have hnonneg : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
  have hratio : (n : ℝ)⁻¹ * euclideanNorm (y-x) ≤ D / (n : ℝ) := by
    rw [div_eq_mul_inv, mul_comm D]
    exact mul_le_mul_of_nonneg_left hxy (inv_nonneg.mpr hn'.le)
  have hratio0 : 0 ≤ (n : ℝ)⁻¹ * euclideanNorm (y-x) :=
    mul_nonneg (inv_nonneg.mpr hn'.le) hnonneg
  have hD0 : 0 ≤ D / (n : ℝ) := div_nonneg hD hn'.le
  calc
    euclideanNorm (b_tube_segment_center x y n (k+1) -
        b_tube_segment_center x y n k) ^ 2 =
        ((n : ℝ)⁻¹ * euclideanNorm (y-x)) ^ 2 := by
      dsimp [b_tube_segment_center]
      rw [b_tube_segment_distance, hgap, abs_of_nonneg (inv_nonneg.mpr hn'.le)]
    _ ≤ (D / (n : ℝ)) ^ 2 := by nlinarith
    _ ≤ τ := hτ

/-- A straight segment between two points with an interior margin retains
that margin throughout the segment, in the Euclidean norm. -/
theorem b_tube_segment_inside_margin {d : ℕ} (center x y : Vec d)
    (R ε u : ℝ) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hx : euclideanNorm (x-center) + ε < R)
    (hy : euclideanNorm (y-center) + ε < R) :
    euclideanNorm ((1-u) • x + u • y - center) + ε < R := by
  have hu : 0 ≤ 1-u := by linarith
  have hid : (1-u) • x + u • y - center =
      (1-u) • (x-center) + u • (y-center) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have htri := TimeChange.euclideanNorm_add_le ((1-u) • (x-center)) (u • (y-center))
  rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
    abs_of_nonneg hu, abs_of_nonneg hu0] at htri
  have hbound : (1-u) * euclideanNorm (x-center) +
      u * euclideanNorm (y-center) + ε < R := by
    by_cases h : u = 0
    · subst u; simpa using hx
    · have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm h)
      have hy' := mul_lt_mul_of_pos_left hy hu'
      have hx' := mul_le_mul_of_nonneg_left hx.le hu
      nlinarith
  rw [hid]
  linarith

/-- All equally spaced centers, including the endpoints, retain the given
interior margin. -/
theorem b_equispaced_segment_inside_margin {d : ℕ} (center x y : Vec d)
    (n k : ℕ) (R ε : ℝ) (hn : 0 < n) (hk : k ≤ n)
    (hx : euclideanNorm (x-center) + ε < R)
    (hy : euclideanNorm (y-center) + ε < R) :
    euclideanNorm (b_tube_segment_center x y n k - center) + ε < R := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hk' : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hk
  apply b_tube_segment_inside_margin center x y R ε ((k : ℝ) / (n : ℝ))
  · positivity
  · exact (div_le_one hn').2 hk'
  · exact hx
  · exact hy

/-- A single subdivision count works for both renewal mesh times, `1/N` and
`2/N`, with the same two native caps and displacement bound. -/
theorem b_two_renewal_meshes_have_capped_native_substeps
    (N : ℕ) (hN : 0 < N) (r δ S D : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hS : 0 < S) (hD : 0 ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∀ j : ℕ, j = 2 ∨ j = 3 →
      let τ : ℝ := (((j : ℝ) - 1) / (N : ℝ)) / (n : ℝ)
      0 < τ ∧ τ ≤ δ * r ^ 2 ∧ τ ≤ S ^ 2 / 64 ∧
        (D / (n : ℝ)) ^ 2 ≤ τ := by
  have hN' : 0 < (N : ℝ) := by exact_mod_cast hN
  have h₁ : 0 < (1 : ℝ) / (N : ℝ) := by positivity
  obtain ⟨n, hn, ht, hcap₁, hcap₂, hdist⟩ :=
    b_exists_capped_native_substeps (1 / (N : ℝ)) r (δ / 2) (S / 2) D
      h₁ hr (by positivity) (by positivity) hD
  refine ⟨n, hn, ?_⟩
  intro j hj
  rcases hj with rfl | rfl
  · norm_num only [Nat.cast_ofNat] at ⊢
    constructor
    · simpa using ht
    constructor
    · nlinarith
    constructor
    · nlinarith
    · simpa using hdist
  · have hdouble : ((2 : ℝ) / (N : ℝ)) / (n : ℝ) =
        2 * (((1 : ℝ) / (N : ℝ)) / (n : ℝ)) := by ring
    norm_num only [Nat.cast_ofNat] at ⊢
    rw [hdouble]
    constructor
    · positivity
    constructor
    · nlinarith
    constructor
    · nlinarith
    · linarith

/-- The equispaced segment starts and ends at the prescribed points. -/
theorem b_tube_segment_center_endpoints {d : ℕ} (x y : Vec d) (n : ℕ)
    (hn : 0 < n) :
    b_tube_segment_center x y n 0 = x ∧ b_tube_segment_center x y n n = y := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  constructor <;> simp [b_tube_segment_center, hn']

/-- A ball of the margin radius around any equispaced center stays in the
larger Euclidean ball. -/
theorem b_equispaced_segment_margin_ball {d : ℕ} (center x y z : Vec d)
    (n k : ℕ) (R ε : ℝ) (hn : 0 < n) (hk : k ≤ n)
    (hx : euclideanNorm (x-center) + ε < R)
    (hy : euclideanNorm (y-center) + ε < R)
    (hz : euclideanNorm (z - b_tube_segment_center x y n k) < ε) :
    euclideanNorm (z-center) < R := by
  have hmargin := b_equispaced_segment_inside_margin center x y n k R ε hn hk hx hy
  have htri := TimeChange.euclideanNorm_add_le
    (z - b_tube_segment_center x y n k) (b_tube_segment_center x y n k - center)
  have hid : z - b_tube_segment_center x y n k +
      (b_tube_segment_center x y n k - center) = z-center := by abel
  rw [hid] at htri
  linarith

/-- The same shared subdivision can reserve a factor sixteen in the squared
center spacing, leaving room for intermediate integration balls. -/
theorem b_two_renewal_meshes_have_spaced_native_substeps
    (N : ℕ) (hN : 0 < N) (r δ S D : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hS : 0 < S) (hD : 0 ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∀ j : ℕ, j = 2 ∨ j = 3 →
      let τ : ℝ := (((j : ℝ) - 1) / (N : ℝ)) / (n : ℝ)
      0 < τ ∧ τ ≤ δ * r ^ 2 ∧ τ ≤ S ^ 2 / 64 ∧
        (D / (n : ℝ)) ^ 2 ≤ τ / 16 := by
  obtain ⟨n, hn, hsteps⟩ := b_two_renewal_meshes_have_capped_native_substeps
    N hN r δ S (4*D) hr hδ hS (by positivity)
  refine ⟨n, hn, ?_⟩
  intro j hj
  obtain ⟨ht, hcap₁, hcap₂, hdist⟩ := hsteps j hj
  refine ⟨ht, hcap₁, hcap₂, ?_⟩
  have hscale : (4 * D / (n : ℝ)) ^ 2 = 16 * (D / (n : ℝ)) ^ 2 := by ring
  rw [hscale] at hdist
  linarith

/-- One count controls both renewal mesh times and the center spacing for
all segments with the prescribed common Euclidean length bound. -/
theorem b_two_renewal_meshes_equispaced_chain
    (N : ℕ) (hN : 0 < N) (r δ S D : ℝ)
    (hr : 0 < r) (hδ : 0 < δ) (hS : 0 < S) (hD : 0 ≤ D) :
    ∃ n : ℕ, 0 < n ∧ ∀ j : ℕ, j = 2 ∨ j = 3 →
      let τ : ℝ := (((j : ℝ) - 1) / (N : ℝ)) / (n : ℝ)
      0 < τ ∧ τ ≤ δ * r ^ 2 ∧ τ ≤ S ^ 2 / 64 ∧
        ∀ {d : ℕ} (x y : Vec d) (k : ℕ), euclideanNorm (y-x) ≤ D →
          euclideanNorm (b_tube_segment_center x y n (k+1) -
            b_tube_segment_center x y n k) ^ 2 ≤ τ / 16 := by
  obtain ⟨n, hn, hsteps⟩ := b_two_renewal_meshes_have_spaced_native_substeps
    N hN r δ S D hr hδ hS hD
  refine ⟨n, hn, ?_⟩
  intro j hj
  obtain ⟨ht, hcap₁, hcap₂, hdist⟩ := hsteps j hj
  refine ⟨ht, hcap₁, hcap₂, ?_⟩
  intro d x y k hxy
  exact b_equispaced_segment_step x y n k D _ hn hD hxy hdist

/-- Points in consecutive small balls satisfy the quarter-distance hypothesis
used by a native near-diagonal estimate. -/
theorem b_euclideanSq_le_quarter_of_nearby_centers {d : ℕ}
    (z z' a b : Vec d) (ε τ : ℝ) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hεsmall : ε ^ 2 ≤ τ / 256)
    (hcenters : euclideanNorm (b-a) ^ 2 ≤ τ / 16)
    (hz : euclideanNorm (z-a) ≤ ε) (hz' : euclideanNorm (z'-b) ≤ ε) :
    euclideanSq (z'-z) ≤ τ / 4 := by
  have htri₁ := TimeChange.euclideanNorm_add_le (z'-b) (b-a)
  have htri₂ := TimeChange.euclideanNorm_add_le ((z'-b) + (b-a)) (a-z)
  have hid : (z'-b) + (b-a) + (a-z) = z'-z := by abel
  rw [hid] at htri₂
  have hreverse : euclideanNorm (a-z) = euclideanNorm (z-a) := by
    have hsub : a-z = (-1 : ℝ) • (z-a) := by
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsub, TimeChange.euclideanNorm_smul]
    norm_num
  rw [hreverse] at htri₂
  have hn : 0 ≤ euclideanNorm (z'-z) := Real.sqrt_nonneg _
  have hc : 0 ≤ euclideanNorm (b-a) := Real.sqrt_nonneg _
  have hsum : 0 ≤ 2*ε + euclideanNorm (b-a) := by positivity
  have hnle : euclideanNorm (z'-z) ≤ 2*ε + euclideanNorm (b-a) := by linarith
  have hsqle : euclideanNorm (z'-z) ^ 2 ≤ (2*ε + euclideanNorm (b-a)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnle) (add_nonneg hsum hn)]
  have hbound : euclideanNorm (z'-z) ^ 2 ≤ τ / 4 := by
    nlinarith [sq_nonneg (euclideanNorm (b-a) - 2*ε)]
  have heuc : 0 ≤ euclideanSq (z'-z) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have heq : euclideanNorm (z'-z) ^ 2 = euclideanSq (z'-z) := Real.sq_sqrt heuc
  rwa [heq] at hbound

/-- The standard radius of the intermediate balls satisfies the small-ball
condition used in the quarter-distance estimate. -/
theorem b_native_quarter_ball_radius (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ Real.sqrt (τ / 4) / 8 ∧ (Real.sqrt (τ / 4) / 8) ^ 2 ≤ τ / 256 := by
  constructor
  · positivity
  · rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ τ / 4)]
    norm_num
    linarith

end EinsteinFull.Calculus
