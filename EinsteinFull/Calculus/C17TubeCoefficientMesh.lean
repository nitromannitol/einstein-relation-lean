import EinsteinFull.Regeneration.BoundedForceCoefficients
import EinsteinRelation.Diffusion.GMPFamily
import PDEFoundation.Measure.BallVolume

namespace EinsteinFull
open EinsteinRelation MeasureTheory ProbabilityTheory

/-- Uniform weighted coefficient bounds on a Euclidean ball, for the actual
reduced field and every signed force. -/
theorem c17_uniform_tube_weighted_coefficients {d : ℕ} (L B : ℝ) (hL : 1 ≤ L) (hB : 0 < B) :
 ∃ C : ℝ, 1 ≤ C ∧ ∀ ω : FieldPair d, IsRegular L ω → ∀ (i : Fin d) (lam : ℝ) (x : Vec d), euclideanNorm x < B →
 let rho := fun y : Vec d => Real.exp (2 * y i)
 let alpha := fun y : Vec d => (rho y / 2) • reducedCoefficient ω (lam⁻¹ • y)
 C⁻¹ ≤ rho x ∧ rho x ≤ C ∧ (alpha x).transpose = alpha x ∧ ∀ v : Vec d,
 C⁻¹ * euclideanSq v ≤ dot v ((alpha x).mulVec v) ∧ dot v ((alpha x).mulVec v) ≤ C * euclideanSq v := by
  let C := 2 * sourceReducedBound L * Real.exp (2 * B)
  have hK := one_le_sourceReducedBound hL
  have hE : 1 ≤ Real.exp (2 * B) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hC : 1 ≤ C := by
    dsimp [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro ω hω i lam x hx
  have h := (Regeneration.boundedForceCoefficient_elliptic hL hB.le ω hω i lam).2.2 x
  rw [Regeneration.boundedForceDensity_eq i x hx.le,
    Regeneration.boundedForceCoefficient_eq ω i lam x hx.le] at h
  dsimp only [Regeneration.boundedForceKappa] at h
  dsimp only [C]
  simpa only [inv_inv] using h

/-- A single deterministic mesh controls both tube curves. -/
theorem c17_two_tube_fixed_mesh {d : ℕ} (i : Fin d) (l : ℝ) (hl : 0 < l) :
 let eps := l/32
 let gamma2 := fun u : ℝ => min ((25*l/4)*u) (25*l/8) • unitVector i
 let gamma3 := fun u : ℝ => if u ≤ 1 then 0 else gamma2 (u-1)
 let gamma := fun j : ℕ => if j=2 then gamma2 else gamma3
 ∃ N : ℕ, 0 < N ∧ ∀ j : ℕ, j=2 ∨ j=3 →
 let h : ℝ := ((j:ℝ)-1)/N
 0 < h ∧ (N:ℝ)*h=(j:ℝ)-1 ∧
 (∀ u : ℝ, 0 ≤ u → u ≤ (j:ℝ)-1 → euclideanNorm (gamma j u)+eps < 4*l) ∧
 (∀ k : ℕ, k<N → ∀ u : ℝ, (k:ℝ)*h ≤ u → u ≤ (k+1:ℕ)*h → euclideanNorm (gamma j u-gamma j ((k:ℝ)*h)) ≤ eps/16) := by
  let a : ℝ := 25*l/4
  let b : ℝ := 25*l/8
  let f : ℝ → ℝ := fun u => min (a*u) b
  let g : ℝ → ℝ := fun u => if u ≤ 1 then 0 else f (u-1)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hf (u : ℝ) (hu : 0 ≤ u) : 0 ≤ f u ∧ f u ≤ b := by
    exact ⟨le_min (mul_nonneg ha hu) hb, min_le_right _ _⟩
  have hfl (u v : ℝ) (huv : u ≤ v) : 0 ≤ f v - f u ∧ f v - f u ≤ a*(v-u) := by
    dsimp [f]
    rw [min_def, min_def]
    split_ifs <;> constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.mpr huv)]
  have hg (u : ℝ) (hu : 0 ≤ u) : 0 ≤ g u ∧ g u ≤ b := by
    dsimp [g]
    split_ifs with h
    · exact ⟨le_refl _, hb⟩
    · exact hf _ (by linarith)
  have hgl (u v : ℝ) (huv : u ≤ v) : 0 ≤ g v - g u ∧ g v - g u ≤ a*(v-u) := by
    dsimp [g]
    split_ifs with hv hu
    · constructor <;> nlinarith [mul_nonneg ha (sub_nonneg.mpr huv)]
    · linarith
    · have hh := hfl 0 (v-1) (by linarith)
      have hf0 : f 0 = 0 := by simp [f, hb]
      rw [hf0] at hh
      have hp := mul_nonneg ha (show 0 ≤ 1-u by linarith)
      constructor <;> nlinarith
    · have hh := hfl (u-1) (v-1) (by linarith)
      constructor <;> nlinarith
  have hn : euclideanNorm (unitVector i : Vec d) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  have hgamma3 (u : ℝ) : (if u ≤ 1 then (0 : Vec d) else f (u-1) • unitVector i) = g u • unitVector i := by
    simp only [g]
    split_ifs <;> simp
  refine ⟨6400, by norm_num, ?_⟩
  intro j hj
  have hjval : (j : ℝ) = 2 ∨ (j : ℝ) = 3 := by rcases hj with rfl | rfl <;> simp
  have hh : 0 < ((j:ℝ)-1)/6400 := by rcases hjval with h | h <;> rw [h] <;> norm_num
  refine ⟨hh, by ring, ?_, ?_⟩
  · intro u hu hu'
    have hf' := hf u hu
    have hg' := hg u hu
    rcases hj with rfl | rfl
    · change euclideanNorm (f u • unitVector i) + l/32 < 4*l
      rw [TimeChange.euclideanNorm_smul, hn, mul_one, abs_of_nonneg hf'.1]
      dsimp [b] at hf'
      linarith [hf'.2]
    · change euclideanNorm (if u ≤ 1 then (0 : Vec d) else f (u-1) • unitVector i) + l/32 < 4*l
      rw [hgamma3, TimeChange.euclideanNorm_smul, hn, mul_one, abs_of_nonneg hg'.1]
      dsimp [b] at hg'
      linarith [hg'.2]
  · intro k hk u hku huk
    have hku0 : 0 ≤ (k:ℝ)*(((j:ℝ)-1)/6400) := mul_nonneg (Nat.cast_nonneg _) hh.le
    have hd : u - (k:ℝ)*(((j:ℝ)-1)/6400) ≤ ((j:ℝ)-1)/6400 := by
      push_cast at huk
      nlinarith
    have hf' := hfl ((k:ℝ)*(((j:ℝ)-1)/6400)) u hku
    have hg' := hgl ((k:ℝ)*(((j:ℝ)-1)/6400)) u hku
    have hbound : a * (u - (k:ℝ)*(((j:ℝ)-1)/6400)) ≤ l/32/16 := by
      have ht := mul_le_mul_of_nonneg_left hd ha
      rcases hjval with h | h <;> rw [h] at ht ⊢ <;> dsimp [a] at ht ⊢ <;> nlinarith
    rcases hj with rfl | rfl
    · change euclideanNorm (f u • unitVector i - f ((k:ℝ)*((2-1)/6400)) • unitVector i) ≤ l/32/16
      norm_num at hf' hbound ⊢
      rw [← sub_smul, TimeChange.euclideanNorm_smul, hn, mul_one, abs_of_nonneg (sub_nonneg.mpr hf'.1)]
      linarith [hf'.2, hbound]
    · change euclideanNorm ((if u ≤ 1 then (0 : Vec d) else f (u-1) • unitVector i) - (if (k:ℝ)*((3-1)/6400) ≤ 1 then (0 : Vec d) else f ((k:ℝ)*((3-1)/6400)-1) • unitVector i)) ≤ l/32/16
      norm_num at hg' hbound ⊢
      rw [hgamma3, hgamma3, ← sub_smul, TimeChange.euclideanNorm_smul, hn, mul_one, abs_of_nonneg (sub_nonneg.mpr hg'.1)]
      linarith [hg'.2, hbound]

/-- Common mesh and coefficient bounds for both deterministic tube curves. -/
theorem c17_uniform_coefficient_mesh_prefix {d : ℕ} (L l : ℝ) (hL : 1 ≤ L) (hl : 0 < l) (i : Fin d) :
 let eps := l/32
 let gamma2 := fun u : ℝ => min ((25*l/4)*u) (25*l/8) • unitVector i
 let gamma3 := fun u : ℝ => if u ≤ 1 then 0 else gamma2 (u-1)
 let gamma := fun j : ℕ => if j=2 then gamma2 else gamma3
 ∃ B C : ℝ, ∃ N : ℕ, 0 < B ∧ 1 ≤ C ∧ 0 < N ∧
 (∀ j : ℕ, j=2 ∨ j=3 → let h : ℝ := ((j:ℝ)-1)/N; 0 < h ∧ (N:ℝ)*h=(j:ℝ)-1 ∧
 (∀ u : ℝ, 0 ≤ u → u ≤ (j:ℝ)-1 → euclideanNorm (gamma j u)+eps < B) ∧
 (∀ k : ℕ, k<N → ∀ u : ℝ, (k:ℝ)*h ≤ u → u ≤ (k+1:ℕ)*h → euclideanNorm (gamma j u-gamma j ((k:ℝ)*h)) ≤ eps/16)) ∧
 ∀ ω : FieldPair d, IsRegular L ω → ∀ (lam : ℝ) (x : Vec d), euclideanNorm x < B →
 let rho := fun y : Vec d => Real.exp (2*y i)
 let alpha := fun y : Vec d => (rho y/2) • reducedCoefficient ω (lam⁻¹ • y)
 C⁻¹ ≤ rho x ∧ rho x ≤ C ∧ (alpha x).transpose = alpha x ∧ ∀ v : Vec d,
 C⁻¹*euclideanSq v ≤ dot v ((alpha x).mulVec v) ∧ dot v ((alpha x).mulVec v) ≤ C*euclideanSq v := by
  have hB : 0 < 4*l := by positivity
  obtain ⟨C, hC, hcoeff⟩ := c17_uniform_tube_weighted_coefficients L (4*l) hL hB
  obtain ⟨N, hN, hmesh⟩ := c17_two_tube_fixed_mesh i l hl
  refine ⟨4*l, C, N, hB, hC, hN, hmesh, ?_⟩
  intro ω hω lam x hx
  exact hcoeff ω hω i lam x hx


/-- The common tube mesh and coefficient bounds are uniform over environment laws. -/
theorem c17_annealed_coefficient_mesh_prefix {d : ℕ} (L r₀ l : ℝ) (hl : 0 < l) (i : Fin d) :
 let eps := l/32
 let gamma2 := fun u : ℝ => min ((25*l/4)*u) (25*l/8) • unitVector i
 let gamma3 := fun u : ℝ => if u ≤ 1 then 0 else gamma2 (u-1)
 let gamma := fun j : ℕ => if j=2 then gamma2 else gamma3
 ∃ B C : ℝ, ∃ N : ℕ, 0 < B ∧ 1 ≤ C ∧ 0 < N ∧
 (∀ j : ℕ, j=2 ∨ j=3 → let h : ℝ := ((j:ℝ)-1)/N; 0 < h ∧ (N:ℝ)*h=(j:ℝ)-1 ∧
 (∀ u : ℝ, 0 ≤ u → u ≤ (j:ℝ)-1 → euclideanNorm (gamma j u)+eps < B) ∧
 (∀ k : ℕ, k<N → ∀ u : ℝ, (k:ℝ)*h ≤ u → u ≤ (k+1:ℕ)*h → euclideanNorm (gamma j u-gamma j ((k:ℝ)*h)) ≤ eps/16)) ∧
 ∀ Q : EnvironmentLaw d L r₀, ∀ᵐ ω ∂Q.measure, ∀ (lam : ℝ) (x : Vec d), euclideanNorm x < B →
 let rho := fun y : Vec d => Real.exp (2*y i)
 let alpha := fun y : Vec d => (rho y/2) • reducedCoefficient ω (lam⁻¹ • y)
 C⁻¹ ≤ rho x ∧ rho x ≤ C ∧ (alpha x).transpose = alpha x ∧ ∀ v : Vec d,
 C⁻¹*euclideanSq v ≤ dot v ((alpha x).mulVec v) ∧ dot v ((alpha x).mulVec v) ≤ C*euclideanSq v := by
  by_cases hL : 1 ≤ L
  · obtain ⟨B, C, N, hB, hC, hN, hmesh, hcoeff⟩ :=
      c17_uniform_coefficient_mesh_prefix L l hL hl i
    refine ⟨B, C, N, hB, hC, hN, hmesh, ?_⟩
    intro Q
    filter_upwards [Q.regular] with ω hω
    exact hcoeff ω hω
  · obtain ⟨N, hN, hmesh⟩ := c17_two_tube_fixed_mesh i l hl
    refine ⟨4*l, 1, N, by positivity, le_rfl, hN, hmesh, ?_⟩
    intro Q
    exact (hL Q.ellipticity_parameter).elim


/-- A positive endpoint-volume bound uniform over all Euclidean ball centers. -/
theorem c17_uniform_endpoint_volume_eta {d : ℕ} (eps cstar : ℝ)
    (heps : 0 < eps) (hcstar : 0 < cstar) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ c : Vec d,
      ENNReal.ofReal eta ≤ ENNReal.ofReal cstar *
        volume {y : Vec d | euclideanNorm (y-c) < eps/16} := by
  have hr : 0 < eps / 16 := by positivity
  let v := (volume (PDE.euclideanBall (0 : Vec d) (eps / 16))).toReal
  have hv : 0 < v := PDE.volume_euclideanBall_toReal_pos 0 hr
  refine ⟨min 1 (cstar * v), lt_min (by norm_num) (mul_pos hcstar hv),
    min_le_left _ _, ?_⟩
  intro c
  have hball : PDE.euclideanBall c (eps / 16) =
      {y : Vec d | euclideanNorm (y-c) < eps/16} := by
    ext y
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr
  have hvol : (volume (PDE.euclideanBall c (eps / 16))).toReal = v := by
    dsimp [v]
    rw [PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos c hr,
      PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) hr]
  calc
    ENNReal.ofReal (min 1 (cstar * v)) ≤ ENNReal.ofReal (cstar * v) :=
      ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal cstar * volume (PDE.euclideanBall c (eps / 16)) := by
      rw [ENNReal.ofReal_mul hcstar.le, ← hvol,
        ENNReal.ofReal_toReal (PDE.volume_euclideanBall_ne_top c hr.le)]
    _ = _ := by rw [hball]

/-- Endpoint domination yields a uniform lower bound for one tube piece. -/
theorem c17_piece_mass_of_endpoint_domination {d : ℕ} (eps cstar : ℝ)
    (heps : 0 < eps) (hcstar : 0 < cstar) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧ ∀ (mu : Measure (Path d)) (lam h : ℝ)
      (c cnext : Vec d),
      (∀ A : Set (Vec d), MeasurableSet A →
        A ⊆ {y | euclideanNorm (y-cnext) < eps/16} →
        ENNReal.ofReal cstar * volume A ≤
          mu {Y | (∀ u : NNReal, (u:ℝ) ≤ h →
            euclideanNorm (lam • Y ((u:ℝ)/lam^2).toNNReal-c) < eps/2) ∧
            lam • Y (h/lam^2).toNNReal ∈ A}) →
      ENNReal.ofReal eta ≤
        mu {Y | (∀ u : NNReal, (u:ℝ) ≤ h →
          euclideanNorm (lam • Y ((u:ℝ)/lam^2).toNNReal-c) < eps/2) ∧
          euclideanNorm (lam • Y (h/lam^2).toNNReal-cnext) < eps/16} := by
  obtain ⟨eta, heta, heta1, hvolume⟩ :=
    c17_uniform_endpoint_volume_eta (d := d) eps cstar heps hcstar
  refine ⟨eta, heta, heta1, ?_⟩
  intro mu lam h c cnext hdom
  have hr : 0 < eps / 16 := by positivity
  have hball : PDE.euclideanBall cnext (eps / 16) =
      {y : Vec d | euclideanNorm (y-cnext) < eps/16} := by
    ext y
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr
  have hmeas : MeasurableSet {y : Vec d | euclideanNorm (y-cnext) < eps/16} := by
    rw [← hball]
    exact PDE.measurableSet_euclideanBall cnext (eps / 16)
  exact (hvolume cnext).trans (hdom _ hmeas (Set.Subset.rfl))

end EinsteinFull
