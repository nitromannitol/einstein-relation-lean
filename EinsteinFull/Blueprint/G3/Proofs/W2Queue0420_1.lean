import EinsteinFull.Blueprint.G3.node_p_u3A_profile_u23_static_u2D_comparison
import EinsteinFull.Blueprint.Roots.node_p_u3A_covariance
import EinsteinFull.Blueprint.Roots.node_h_u3A_forced
import EinsteinFull.Blueprint.G4.Proofs.W2Queue0145_2
import EinsteinFull.Calculus.GaussianModelTestScalingSupport
import EinsteinFull.Calculus.SchwartzNormSupport

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation MeasureTheory Filter
open scoped NNReal Topology BigOperators

/-- The actual joint Schwartz tests for the three kinds of model endpoints. -/
def w2ProfileTests {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : ℂ) :
    EndpointIndex d → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))
  | .inl i => profileVelocityTest hd Q i z
  | .inr true => profileTransposeTest hd Q z
  | .inr false => profileClockTest hd Q z

/-- Coordinate values agree with the literal backward-kernel convention in the contract. -/
theorem w2ProfileTests_apply {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (z : ℂ) (ν : EndpointIndex d)
    (x : Vec d) (a : JointObservationIndex d) :
    let first : Fin d := ⟨0, by omega⟩
    let kernel := fun (w : ℂ) => homogenizedGaussianKernel Q first (1 / 2) (by norm_num) w
    let kernelDeriv := fun (w : ℂ) (j : Fin d) (x : Vec d) =>
      iteratedFDeriv ℝ 1 (kernel w) (-x) (fun _ => unitVector j)
    w2ProfileTests hd Q z ν x a = match ν, a with
      | .inr true, .inl (j,k) => if k = first then (1 / 2 : ℂ) * kernelDeriv z j x else 0
      | .inl i, .inl (j,k) => if k = i then
          (1 / 2 : ℂ) * kernelDeriv (-z) j x +
            (if j = first then z * kernel z x else 0) else 0
      | .inr false, .inr () => z * kernel z x
      | _, _ => 0 := by
  classical
  dsimp only
  have hder (w : ℂ) (j : Fin d) :
      iteratedFDeriv ℝ 1 (homogenizedGaussianKernel Q ⟨0, by omega⟩
        (1 / 2) (by norm_num) w) (-x) (fun _ => unitVector j) =
      -fderiv ℝ (homogenizedGaussianKernel Q ⟨0, by omega⟩
        (1 / 2) (by norm_num) (-w)) x (unitVector j) := by
    rw [iteratedFDeriv_one_apply]
    simpa only [neg_neg] using!
      fderiv_homogenizedGaussianKernel_neg_force_neg Q ⟨0, by omega⟩ j
        (1 / 2) (by norm_num) (-w) x
  have hsum (v : Fin d → SchwartzMap (Vec d)
      (EuclideanSpace ℂ (JointObservationIndex d))) (b : JointObservationIndex d) :
      (∑ j, v j) x b = ∑ j, v j x b := by
    induction Finset.univ (α := Fin d) using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, SchwartzMap.zero_apply, PiLp.zero_apply]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, SchwartzMap.add_apply,
        PiLp.add_apply, ih]
  cases ν with
  | inl i =>
    cases a with
    | inl jk =>
      rcases jk with ⟨j,k⟩
      by_cases hk : k = i
      · subst k
        simp [w2ProfileTests, profileVelocityTest, hsum, jointCoordinateSchwartz_apply, hder, PiLp.smul_apply,
          profileGaussianDerivativeSchwartz_apply, profileGaussianSchwartz_apply]
        ring
      · simp [w2ProfileTests, profileVelocityTest, hsum, jointCoordinateSchwartz_apply, PiLp.smul_apply, hk]
    | inr u =>
      simp [w2ProfileTests, profileVelocityTest, hsum, jointCoordinateSchwartz_apply, PiLp.smul_apply]
  | inr b =>
    cases b with
    | false =>
      cases a with
      | inl jk => simp [w2ProfileTests, profileClockTest, jointCoordinateSchwartz_apply,
          PiLp.smul_apply]
      | inr u => cases u; simp [w2ProfileTests, profileClockTest,
          jointCoordinateSchwartz_apply, PiLp.smul_apply, profileGaussianSchwartz_apply]
    | true =>
      cases a with
      | inl jk =>
        rcases jk with ⟨j,k⟩
        by_cases hk : k = (⟨0, by omega⟩ : Fin d)
        · subst k
          simp [w2ProfileTests, profileTransposeTest, hsum, jointCoordinateSchwartz_apply,
            hder, PiLp.smul_apply, profileGaussianDerivativeSchwartz_apply]
          ring
        · simp [w2ProfileTests, profileTransposeTest, hsum, jointCoordinateSchwartz_apply,
            PiLp.smul_apply, hk]
      | inr u =>
        simp [w2ProfileTests, profileTransposeTest, hsum, jointCoordinateSchwartz_apply,
          PiLp.smul_apply]

/-- Exact parabolic scaling, simultaneously for the actual velocity, transpose and clock. -/
theorem w2ProfileTests_model {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R : ℝ) (hR : 0 < R) (z : ℂ) (ν : EndpointIndex d) :
    (match ν with
      | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
      | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
      | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))) =
    ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) •
      scaledJointPairing Q R hR Z (w2ProfileTests hd Q z ν) := by
  have hz : z / (R : ℂ) * (R : ℂ) = z :=
    div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hR.ne')
  cases ν with
  | inl i =>
    simpa only [hz, w2ProfileTests] using!
      modelVelocityEndpoint_eq_scaled_profileTest hd Q Z i R hR (z / (R : ℂ))
  | inr b =>
    cases b
    · simpa only [hz, w2ProfileTests] using!
        modelClockEndpoint_eq_scaled_profileTest hd Q Z R hR (z / (R : ℂ))
    · simpa only [hz, w2ProfileTests] using!
        modelTransposeEndpoint_eq_scaled_profileTest hd Q Z R hR (z / (R : ℂ))

private lemma integral_smul_pair {Ω : Type*} [MeasurableSpace Ω] (m : Measure Ω)
    (c : ℂ) (f g : Lp ℂ 2 m) :
    (∫ ω, (c • f) ω * (c • g) ω ∂m) =
      (c * c) * ∫ ω, f ω * g ω ∂m := by
  calc
    _ = ∫ ω, (c * c) * (f ω * g ω) ∂m := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with ω hf hg
      rw [hf, hg]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

/-- Covariance scaling applies to all endpoint tests, including the transpose self-pairing.
The covariance witness is chosen before the observation and the force. -/
theorem w2ProfileTests_covariance_rate
    (hcovariance : node_p_u3A_covarianceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∃ covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ,
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      IsJointCovariance Q Z covariance ∧
      ∀ (z : ℂ) (R : ℝ) (hR : 0 < R), 2 ≤ R → ∀ ν : EndpointIndex d,
      let F := w2ProfileTests hd Q z
      let model : EndpointIndex d → Lp ℂ 2 (reducedLaw Q) := fun ν => match ν with
        | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
      ‖(∫ ω, model (.inr true) ω * model ν ω ∂reducedLaw Q) -
        ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) * jointTestCovariance covariance
          (F (.inr true)) (F ν)‖ ≤
        C * schwartzTestNorm N (F (.inr true)) * schwartzTestNorm N (F ν) *
          R ^ (-(d : ℝ) - 2 - ε) := by
  obtain ⟨ε, C, hε, hC, hcov⟩ := hcovariance d hd D N hN
  refine ⟨ε, C, hε, hC, ?_⟩
  intro Q hQ
  obtain ⟨covariance, _, _, hr⟩ := hcov Q hQ
  refine ⟨covariance, ?_⟩
  intro Z hZ
  have hrate := hr Z hZ
  have hc : IsJointCovariance Q Z covariance :=
    w2_jointCovariance_of_rate Q Z covariance N ε C hε (by
      intro R hR F G
      rw [jointTestCovariance_eq_integral]
      exact hrate R hR F G)
  refine ⟨hc, ?_⟩
  intro z R hR hR2 ν
  dsimp only
  have ht := w2ProfileTests_model hd Q Z R hR z (.inr true)
  dsimp only at ht
  rw [w2ProfileTests_model hd Q Z R hR z ν, ht, integral_smul_pair]
  have hscale :
      ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
        ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) =
      ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hR]
    congr 2
    ring
  rw [hscale, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hR _)]
  have hr' := hrate R hR2 (w2ProfileTests hd Q z (.inr true)) (w2ProfileTests hd Q z ν)
  rw [← jointTestCovariance_eq_integral] at hr'
  calc
    _ ≤ R ^ (-(d : ℝ) - 2) *
        (C * schwartzTestNorm N (w2ProfileTests hd Q z (.inr true)) *
          schwartzTestNorm N (w2ProfileTests hd Q z ν) * R ^ (-ε)) :=
      mul_le_mul_of_nonneg_left hr' (Real.rpow_pos_of_pos hR _).le
    _ = _ := by
      rw [show -(d : ℝ) - 2 - ε = (-(d : ℝ) - 2) + (-ε) by ring,
        Real.rpow_add hR]
      ring

/-- Every fixed continuous scalar Schwartz seminorm has a structural Gaussian bound.
The constant precedes the law, spatial coordinate and arbitrary complex force. -/
theorem w2_gaussian_continuous_seminorm_bound (d : ℕ) (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀)
    (q : Seminorm ℂ (SchwartzMap (Vec d) ℂ)) (hq : Continuous q) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (z : ℂ),
      q (profileGaussianSchwartz Q i z) ≤ K * Real.exp (K * (1 + ‖z‖) ^ 2) := by
  classical
  obtain ⟨s, C, hC, hb⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℂ (Vec d) ℂ) q hq
  let B : ℝ := 1 + ∑ mn ∈ s, gaussianSchwartzOrderBound d Λ₀ mn.1 mn.2
  have hterm (mn : ℕ × ℕ) : 0 ≤ gaussianSchwartzOrderBound d Λ₀ mn.1 mn.2 :=
    (gaussianSchwartzOrderBound_pos d Λ₀ hΛ mn.1 mn.2).le
  have hB : 0 < B := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg (fun mn _ => hterm mn))
  have hCB : 0 < (C : ℝ) * B :=
    mul_pos (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC)) hB
  let K : ℝ := B + (C : ℝ) * B
  have hK : 0 < K := add_pos hB hCB
  have hBK : B ≤ K := le_add_of_nonneg_right hCB.le
  have hCK : (C : ℝ) * B ≤ K := le_add_of_nonneg_left hB.le
  refine ⟨K, hK, ?_⟩
  intro r₀ Q i z
  let f := profileGaussianSchwartz Q i z
  have hs (mn : ℕ × ℕ) (hmn : mn ∈ s) :
      SchwartzMap.seminorm ℂ mn.1 mn.2 f ≤ B * Real.exp (B * (1 + ‖z‖) ^ 2) := by
    have ht : gaussianSchwartzOrderBound d Λ₀ mn.1 mn.2 ≤ B := by
      exact (Finset.single_le_sum (fun mn _ => hterm mn) hmn).trans
        (le_add_of_nonneg_left zero_le_one)
    exact (seminorm_homogenizedGaussianSchwartz_le Q i (1 / 2) (by norm_num)
      le_rfl (by norm_num) z mn.1 mn.2).trans
      (mul_le_mul ht (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht (sq_nonneg _)))
        (Real.exp_pos _).le hB.le)
  have hs' : (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) f ≤
      B * Real.exp (B * (1 + ‖z‖) ^ 2) :=
    Seminorm.finset_sup_apply_le (mul_pos hB (Real.exp_pos _)).le hs
  calc
    q f ≤ (C • s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) f := hb f
    _ = (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (Vec d) ℂ)) f := rfl
    _ ≤ (C : ℝ) * (B * Real.exp (B * (1 + ‖z‖) ^ 2)) :=
      mul_le_mul_of_nonneg_left hs' C.coe_nonneg
    _ = ((C : ℝ) * B) * Real.exp (B * (1 + ‖z‖) ^ 2) := by ring
    _ ≤ K * Real.exp (K * (1 + ‖z‖) ^ 2) :=
      mul_le_mul hCK (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBK (sq_nonneg _)))
        (Real.exp_pos _).le hK.le

/-- A finite continuous seminorm dominating the contract's Euclidean weighted norm. -/
def w2ProfileSeminorm (d N : ℕ) :
    Seminorm ℂ (SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :=
  ∑ mn ∈ Finset.Iic (N, N), SchwartzMap.seminorm ℂ mn.1 mn.2

/-- Continuity permits applying the scalar Gaussian bound after the fixed
coordinate embeddings and spatial derivative maps. -/
theorem continuous_w2ProfileSeminorm (d N : ℕ) : Continuous (w2ProfileSeminorm d N) := by
  classical
  unfold w2ProfileSeminorm
  induction Finset.Iic (N, N) using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Seminorm.coe_zero] using! continuous_const
  | @insert mn s hmn ih =>
    rw [Finset.sum_insert hmn, Seminorm.coe_add]
    exact ((schwartz_withSeminorms ℂ (Vec d)
      (EuclideanSpace ℂ (JointObservationIndex d))).continuous_seminorm mn).add ih

/-- Preserve the Euclidean weight explicitly when passing to ordinary Schwartz seminorms. -/
theorem schwartzTestNorm_le_w2ProfileSeminorm {d : ℕ} (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    schwartzTestNorm N F ≤ ((d : ℝ) + 1) ^ N * 2 ^ N * w2ProfileSeminorm d N F := by
  apply csSup_le (schwartzTestNorm_set_nonempty N F)
  rintro q ⟨k, dirs, x, rfl⟩
  have hpartial :
      ‖iteratedFDeriv ℝ k.val (fun y => F y) x (fun j => unitVector (dirs j))‖ ≤
      ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖ := by
    simpa only [unitVector, Pi.norm_single, norm_one, Finset.prod_const_one, mul_one]
      using (iteratedFDeriv ℝ k.val (fun y => F y) x).le_opNorm
        (fun j => unitVector (dirs j))
  have hw : 1 + euclideanNorm x ≤ ((d : ℝ) + 1) * (1 + ‖x‖) := by
    have he := euclideanNorm_le_dimension_mul_norm x
    nlinarith only [he, Nat.cast_nonneg (α := ℝ) d]
  have hsup : (Finset.Iic (N, N)).sup
      (fun mn => SchwartzMap.seminorm ℂ mn.1 mn.2) F ≤ w2ProfileSeminorm d N F :=
    Seminorm.finset_sup_le_sum _ _ F
  calc
    _ ≤ (((d : ℝ) + 1) * (1 + ‖x‖)) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖ := by
      gcongr
      exact add_nonneg zero_le_one (Real.sqrt_nonneg _)
    _ = ((d : ℝ) + 1) ^ N * ((1 + ‖x‖) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖) := by rw [mul_pow, mul_assoc]
    _ ≤ ((d : ℝ) + 1) ^ N * (2 ^ N * (Finset.Iic (N, N)).sup
        (fun mn => SchwartzMap.seminorm ℂ mn.1 mn.2) F) :=
      mul_le_mul_of_nonneg_left
        (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (N, N)) le_rfl
          (Nat.le_of_lt_succ k.isLt) F x) (by positivity)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hsup (by positivity)

/-- Pulling a fixed finite family of continuous maps back to scalar Schwartz space
retains a Gaussian bound with its constant chosen before the law. -/
theorem w2_gaussian_map_family_bound (d N : ℕ) (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀)
    {ι : Type*} [Fintype ι]
    (T : ι → SchwartzMap (Vec d) ℂ →L[ℂ]
      SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (z : ℂ) (a : ι),
      w2ProfileSeminorm d N (T a (profileGaussianSchwartz Q i z)) ≤
        K * Real.exp (K * (1 + ‖z‖) ^ 2) := by
  classical
  have hb (a : ι) := w2_gaussian_continuous_seminorm_bound d Λ₀ hΛ
    ((w2ProfileSeminorm d N).comp (T a).toLinearMap)
    ((continuous_w2ProfileSeminorm d N).comp (T a).continuous)
  choose K hK hb using hb
  let C := 1 + ∑ a, K a
  have hC : 0 < C := add_pos_of_pos_of_nonneg zero_lt_one
    (Finset.sum_nonneg fun a _ => (hK a).le)
  have hKC (a : ι) : K a ≤ C :=
    (Finset.single_le_sum (fun a _ => (hK a).le) (Finset.mem_univ a)).trans
      (le_add_of_nonneg_left zero_le_one)
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i z a
  exact (hb a r₀ Q i z).trans (mul_le_mul (hKC a)
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hKC a) (sq_nonneg _)))
    (Real.exp_pos _).le hC.le)

/-- The coordinate embeddings and their first spatial derivatives are fixed
continuous maps, independent of the law and force. -/
def w2ProfileCoordinateMap (d : ℕ) (a : JointObservationIndex d) (j : Option (Fin d)) :
    SchwartzMap (Vec d) ℂ →L[ℂ]
      SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  let embed := SchwartzMap.bilinLeftCLM (ContinuousLinearMap.lsmul ℂ ℂ)
    (Function.HasTemperateGrowth.const (EuclideanSpace.single a (1 : ℂ)))
  match j with
  | none => embed
  | some k => embed.comp (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Vec d) ℂ) (unitVector k))

/-- Uniform structural bound for the literal endpoint tests in the prescribed
Euclidean weighted Schwartz norm. -/
theorem w2ProfileTests_norm_bound (d : ℕ) (hd : 2 ≤ d) (N : ℕ)
    (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (z : ℂ) (ν : EndpointIndex d),
      schwartzTestNorm N (w2ProfileTests hd Q z ν) ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) := by
  classical
  obtain ⟨K, hK, hb⟩ := w2_gaussian_map_family_bound d N Λ₀ hΛ
    (fun a : JointObservationIndex d × Option (Fin d) => w2ProfileCoordinateMap d a.1 a.2)
  let A : ℝ := ((d : ℝ) + 1) ^ N * 2 ^ N
  let B : ℝ := ((d : ℝ) + 1) * K
  let C : ℝ := 1 + A * B + K
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A * B ≤ C := by dsimp [C]; linarith
  have hKC : K + 1 ≤ C := by dsimp [C]; nlinarith [mul_pos hA hB]
  refine ⟨C, hC, ?_⟩
  intro r₀ Q z ν
  let q := w2ProfileSeminorm d N
  let f := profileGaussianSchwartz Q (⟨0, by omega⟩ : Fin d)
  let E := K * Real.exp (K * (1 + ‖z‖) ^ 2)
  have hE : 0 ≤ E := (mul_pos hK (Real.exp_pos _)).le
  have hcoord (a : JointObservationIndex d) : q (jointCoordinateSchwartz a (f z)) ≤ E :=
    hb r₀ Q _ z (a, none)
  have hder (a : JointObservationIndex d) (j : Fin d) (w : ℂ) :
      q (jointCoordinateSchwartz a (profileGaussianDerivativeSchwartz Q
        ⟨0, by omega⟩ j w)) ≤ K * Real.exp (K * (1 + ‖w‖) ^ 2) :=
    hb r₀ Q _ w (a, some j)
  have hsum (k : Fin d) (w : ℂ) :
      q (∑ j : Fin d, jointCoordinateSchwartz (.inl (j,k))
        (profileGaussianDerivativeSchwartz Q ⟨0, by omega⟩ j w)) ≤
        (d : ℝ) * (K * Real.exp (K * (1 + ‖w‖) ^ 2)) := by
    calc
      _ ≤ ∑ j : Fin d, q (jointCoordinateSchwartz (.inl (j,k))
          (profileGaussianDerivativeSchwartz Q ⟨0, by omega⟩ j w)) := by
        induction Finset.univ (α := Fin d) using Finset.induction_on with
        | empty => simp
        | @insert j s hj ih =>
          rw [Finset.sum_insert hj, Finset.sum_insert hj]
          exact (map_add_le_add q _ _).trans (add_le_add le_rfl ih)
      _ ≤ ∑ _j : Fin d, K * Real.exp (K * (1 + ‖w‖) ^ 2) :=
        Finset.sum_le_sum fun j _ => hder _ j w
      _ = _ := by simp
  have hhalf : ‖(-1 / 2 : ℂ)‖ ≤ 1 := by norm_num
  have htest : q (w2ProfileTests hd Q z ν) ≤ B * (1 + ‖z‖) *
      Real.exp (K * (1 + ‖z‖) ^ 2) := by
    have hs := hsum (⟨0, by omega⟩ : Fin d) (-z)
    simp only [norm_neg] at hs
    have hdiv (k : Fin d) : q ((-1 / 2 : ℂ) • ∑ j : Fin d,
        jointCoordinateSchwartz (.inl (j,k))
          (profileGaussianDerivativeSchwartz Q ⟨0, by omega⟩ j z)) ≤ (d : ℝ) * E := by
      rw [map_smul_eq_mul]
      exact (mul_le_mul_of_nonneg_right hhalf (apply_nonneg q _)).trans
        (by simpa only [one_mul] using! hsum k z)
    cases ν with
    | inl i =>
      have hc : q (z • jointCoordinateSchwartz (.inl (⟨0, by omega⟩, i)) (f z)) ≤
          ‖z‖ * E := by
        rw [map_smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hcoord _) (norm_nonneg z)
      have ht := (map_add_le_add q _ _).trans (add_le_add (hdiv i) hc)
      change q (profileVelocityTest hd Q i z) ≤ _
      dsimp only [profileVelocityTest] at *
      dsimp [B, E] at *
      nlinarith [norm_nonneg z, Nat.cast_nonneg (α := ℝ) d,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg z), Real.exp_pos (K * (1 + ‖z‖)^2)]
    | inr b =>
      cases b
      · change q (z • jointCoordinateSchwartz (.inr ()) (f z)) ≤ _
        rw [map_smul_eq_mul]
        have ht := mul_le_mul_of_nonneg_left (hcoord (.inr ())) (norm_nonneg z)
        dsimp [B, E] at *
        nlinarith [norm_nonneg z, Nat.cast_nonneg (α := ℝ) d,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg z), Real.exp_pos (K * (1 + ‖z‖)^2)]
      · change q ((-1 / 2 : ℂ) • _) ≤ _
        rw [map_smul_eq_mul]
        have ht := (mul_le_mul_of_nonneg_right hhalf (apply_nonneg q _)).trans
          (by simpa only [one_mul] using! hs)
        dsimp [B, E] at *
        nlinarith [norm_nonneg z, Nat.cast_nonneg (α := ℝ) d,
          mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (norm_nonneg z), Real.exp_pos (K * (1 + ‖z‖)^2)]
  have hzexp : 1 + ‖z‖ ≤ Real.exp ((1 + ‖z‖) ^ 2) := by
    have he := Real.add_one_le_exp ((1 + ‖z‖) ^ 2)
    nlinarith [norm_nonneg z]
  calc
    _ ≤ A * q (w2ProfileTests hd Q z ν) := schwartzTestNorm_le_w2ProfileSeminorm N _
    _ ≤ A * (B * (1 + ‖z‖) * Real.exp (K * (1 + ‖z‖) ^ 2)) :=
      mul_le_mul_of_nonneg_left htest hA.le
    _ ≤ (A * B) * Real.exp ((K + 1) * (1 + ‖z‖) ^ 2) := by
      rw [add_mul, one_mul, Real.exp_add]
      nlinarith [mul_le_mul_of_nonneg_left hzexp
        (mul_nonneg (mul_pos hA hB).le (Real.exp_pos (K * (1+‖z‖)^2)).le)]
    _ ≤ _ := mul_le_mul hAC
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hKC (sq_nonneg _)))
      (Real.exp_pos _).le hC.le

private lemma profile_exp_mono {A B : ℝ} (hA : 0 ≤ A) (hAB : A ≤ B) (z : ℂ) :
    A * Real.exp (A * (1 + ‖z‖) ^ 2) ≤ B * Real.exp (B * (1 + ‖z‖) ^ 2) :=
  mul_le_mul hAB (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_right hAB (sq_nonneg _))) (Real.exp_pos _).le (hA.trans hAB)

private lemma profile_exp_add {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : A + 2 * B ≤ C) (z : ℂ) :
    A * Real.exp (A * (1 + ‖z‖) ^ 2) +
      2 * (B * Real.exp (B * (1 + ‖z‖) ^ 2)) ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) := by
  have hAC : A ≤ C := by linarith
  have hBC : B ≤ C := by linarith
  have ha := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hAC (sq_nonneg ((1:ℝ)+‖z‖)))
  have hb := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hBC (sq_nonneg ((1:ℝ)+‖z‖)))
  nlinarith [mul_le_mul_of_nonneg_left ha hA,
    mul_le_mul_of_nonneg_left hb hB,
    mul_le_mul_of_nonneg_right hC (Real.exp_pos (C*(1+‖z‖)^2)).le]

/-- One structural envelope controls both the test norm and its scaled static
covariance error, with the covariance chosen before the observation and force. -/
theorem w2ProfileTests_static_bound
    (hcovariance : node_p_u3A_covarianceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧
    (∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (z : ℂ) (ν : EndpointIndex d),
      schwartzTestNorm N (w2ProfileTests hd Q z ν) ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2)) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∃ covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ,
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      IsJointCovariance Q Z covariance ∧
      ∀ (z : ℂ) (R : ℝ) (hR : 0 < R), 2 ≤ R → ∀ ν : EndpointIndex d,
      let model : EndpointIndex d → Lp ℂ 2 (reducedLaw Q) := fun ν => match ν with
        | .inl i => modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
        | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
      ‖(∫ ω, model (.inr true) ω * model ν ω ∂reducedLaw Q) -
        ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) * jointTestCovariance covariance
          (w2ProfileTests hd Q z (.inr true)) (w2ProfileTests hd Q z ν)‖ ≤
        C * Real.exp (C * (1 + ‖z‖) ^ 2) * R ^ (-(d : ℝ) - 2 - ε) := by
  obtain ⟨ε, A, hε, hA, hr⟩ := w2ProfileTests_covariance_rate hcovariance d hd D N hN
  obtain ⟨G, hG, hg⟩ := w2ProfileTests_norm_bound d hd N D.ellipticity D.one_le_ellipticity
  let C := 1 + A * G ^ 2 + 2 * G
  have hC : 0 < C := by dsimp [C]; positivity
  have hGC : G ≤ C := by dsimp [C]; nlinarith [mul_nonneg hA.le (sq_nonneg G)]
  have hAC : A * G ^ 2 ≤ C := by dsimp [C]; linarith
  have h2GC : 2 * G ≤ C := by dsimp [C]; nlinarith [mul_nonneg hA.le (sq_nonneg G)]
  refine ⟨ε, C, hε, hC, ?_, ?_⟩
  · intro Q z ν
    exact (hg _ Q z ν).trans (profile_exp_mono hG.le hGC z)
  intro Q hQ
  obtain ⟨covariance, hc⟩ := hr Q hQ
  refine ⟨covariance, ?_⟩
  intro Z hZ
  obtain ⟨hcov, hb⟩ := hc Z hZ
  refine ⟨hcov, ?_⟩
  intro z R hR hR2 ν
  have hn (μ : EndpointIndex d) := hg _ Q z μ
  have hnn (μ : EndpointIndex d) : 0 ≤ schwartzTestNorm N (w2ProfileTests hd Q z μ) :=
    by
      obtain ⟨v, k, dirs, x, rfl⟩ := schwartzTestNorm_set_nonempty N
        (w2ProfileTests hd Q z μ)
      exact (mul_nonneg (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) _) (norm_nonneg _)).trans
        (le_csSup (schwartzTestNorm_set_bddAbove N _) ⟨k, dirs, x, rfl⟩)
  have he : 0 ≤ G * Real.exp (G * (1 + ‖z‖) ^ 2) := by positivity
  have hprod : A * schwartzTestNorm N (w2ProfileTests hd Q z (.inr true)) *
      schwartzTestNorm N (w2ProfileTests hd Q z ν) ≤
      C * Real.exp (C * (1 + ‖z‖) ^ 2) := by
    calc
      _ ≤ A * (G * Real.exp (G * (1 + ‖z‖) ^ 2)) *
          (G * Real.exp (G * (1 + ‖z‖) ^ 2)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hn _) hA.le) (hn ν) (hnn ν)
          (mul_nonneg hA.le he)
      _ = (A * G ^ 2) * Real.exp ((2 * G) * (1 + ‖z‖) ^ 2) := by
        rw [show (2 * G) * (1 + ‖z‖) ^ 2 =
          G * (1 + ‖z‖) ^ 2 + G * (1 + ‖z‖) ^ 2 by ring, Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul hAC (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right h2GC (sq_nonneg _))) (Real.exp_pos _).le hC.le
  exact (hb z R hR hR2 ν).trans
    (mul_le_mul_of_nonneg_right hprod (Real.rpow_pos_of_pos hR _).le)

private lemma profile_error_triangle (u v m n c e : ℂ) :
    ‖u - c‖ + ‖v - e‖ ≤ (‖u - m‖ + ‖v - n‖) + (‖m - c‖ + ‖n - e‖) := by
  exact add_le_add (norm_sub_le_norm_sub_add_norm_sub u m c)
    (norm_sub_le_norm_sub_add_norm_sub v n e) |>.trans_eq (by ring)

/-- The static Gaussian covariance comparison and the forced bridge combine
with the minimum of their gains, retaining the complete prescribed witnesses. -/
theorem node_p_u3A_profile_u23_static_u2D_comparison_of_deps
    (hcovariance : node_p_u3A_covarianceStmt)
    (hforced : node_h_u3A_forcedStmt) :
    node_p_u3A_profile_u23_static_u2D_comparisonStmt := by
  intro d hd D N hN
  obtain ⟨εcov, S, hεcov, hS, hnorm, hstatic⟩ :=
    w2ProfileTests_static_bound hcovariance d hd D N hN
  obtain ⟨εbridge, A, hεbridge, hA, hdisc, hwindow, _⟩ := hforced d hd D
  let C := A + 2 * S + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hSC : S ≤ C := by dsimp [C]; linarith
  have hsumC : A + 2 * S ≤ C := by dsimp [C]; linarith
  refine ⟨εcov, εbridge, C, hεcov, hεbridge, hC, ?_⟩
  intro C₀ hC₀
  obtain ⟨W, R₀, hW, hR₀, hw⟩ := hwindow C₀ hC₀
  let Cw := W + 2 * S + 1
  have hCw : 0 < Cw := by dsimp [Cw]; positivity
  have hsumCw : W + 2 * S ≤ Cw := by dsimp [Cw]; linarith
  refine ⟨Cw, R₀, hCw, hR₀, ?_⟩
  intro Q hQ
  obtain ⟨covariance, hc⟩ := hstatic Q hQ
  refine ⟨covariance, ?_⟩
  intro Z hZ
  obtain ⟨hcov, hs⟩ := hc Z hZ
  refine ⟨hcov, ?_⟩
  intro z
  refine ⟨w2ProfileTests hd Q z, ?_, ?_, ?_⟩
  · exact w2ProfileTests_apply hd Q z
  · intro ν
    exact (hnorm Q z ν).trans (profile_exp_mono hS.le hSC z)
  intro R hR hR2
  dsimp only
  simp_rw [← jointTestCovariance_eq_integral]
  refine ⟨w2ProfileTests_model hd Q Z R hR z, ?_, ?_⟩
  · intro ν
    exact (hs z R hR hR2 ν).trans
      (mul_le_mul_of_nonneg_right (profile_exp_mono hS.le hSC z)
        (Real.rpow_pos_of_pos hR _).le)
  intro β a μ hQβ hβ ha hμ P hP i
  let model : EndpointIndex d → Lp ℂ 2 (reducedLaw Q) := fun ν => match ν with
    | .inl k => modelVelocityEndpoint hd Q Z k (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
    | .inr true => modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
    | .inr false => modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) (z / (R : ℂ))
  let cov := fun ν => ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) *
    jointTestCovariance covariance (w2ProfileTests hd Q z (.inr true)) (w2ProfileTests hd Q z ν)
  let u := velocityCorrelation Q (⟨0, by omega⟩ : Fin d) i (z / (R : ℂ)) P β a (R ^ 2).toNNReal
  let v := clockCorrelation Q (⟨0, by omega⟩ : Fin d) (z / (R : ℂ)) P β μ (R ^ 2).toNNReal
  let error := ‖u - cov (.inl i)‖ + ‖v - cov (.inr false)‖
  let power := R ^ (-(d : ℝ) - 2 - min εcov εbridge)
  have hpower : 0 ≤ power := (Real.rpow_pos_of_pos hR _).le
  have hcovpower : R ^ (-(d : ℝ) - 2 - εcov) ≤ power :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith [min_le_left εcov εbridge])
  have hbridgepower : R ^ (-(d : ℝ) - 2 - εbridge) ≤ power :=
    Real.rpow_le_rpow_of_exponent_le (by linarith)
      (by linarith [min_le_right εcov εbridge])
  have hstat (ν : EndpointIndex d) :
      ‖(∫ ω, model (.inr true) ω * model ν ω ∂reducedLaw Q) - cov ν‖ ≤
        S * Real.exp (S * (1 + ‖z‖) ^ 2) * power :=
    (hs z R hR hR2 ν).trans (mul_le_mul_of_nonneg_left hcovpower (by positivity))
  have ht : error ≤ forcedComparisonError hd Q R hR z i P β a μ Z +
      2 * (S * Real.exp (S * (1 + ‖z‖) ^ 2) * power) := by
    have htriangle := profile_error_triangle u v
      (∫ ω, model (.inr true) ω * model (.inl i) ω ∂reducedLaw Q)
      (∫ ω, model (.inr true) ω * model (.inr false) ω ∂reducedLaw Q)
      (cov (.inl i)) (cov (.inr false))
    have hsv := hstat (.inl i)
    have hsc := hstat (.inr false)
    change error ≤ forcedComparisonError hd Q R hR z i P β a μ Z +
      (‖(∫ ω, model (.inr true) ω * model (.inl i) ω ∂reducedLaw Q) - cov (.inl i)‖ +
       ‖(∫ ω, model (.inr true) ω * model (.inr false) ω ∂reducedLaw Q) - cov (.inr false)‖)
      at htriangle
    linarith
  have combine (B H : ℝ) (hB : 0 ≤ B) (hBH : B + 2 * S ≤ H)
      (hb : forcedComparisonError hd Q R hR z i P β a μ Z ≤
        B * Real.exp (B * (1 + ‖z‖) ^ 2) * R ^ (-(d : ℝ) - 2 - εbridge)) :
      error ≤ H * Real.exp (H * (1 + ‖z‖) ^ 2) * power := by
    have hb' := hb.trans (mul_le_mul_of_nonneg_left hbridgepower
      (mul_nonneg hB (Real.exp_pos _).le))
    have he := mul_le_mul_of_nonneg_right (profile_exp_add hB hS.le hBH z) hpower
    nlinarith only [ht, hb', he]
  change (‖z‖ ≤ 2 → error ≤ C * Real.exp (C * (1 + ‖z‖) ^ 2) * power) ∧
    (R₀ ≤ R → (∃ x : ℝ, z = (x : ℂ) ∧ |x| ≤ C₀ * Real.log R ^ (1 / 4 : ℝ)) →
      error ≤ Cw * Real.exp (Cw * (1 + ‖z‖) ^ 2) * power)
  constructor
  · intro hz
    exact combine A C hA.le hsumC
      (hdisc Q hQβ β a μ Z hβ ha hμ hZ R hR hR2 z hz P hP i)
  · intro hRwindow hz
    obtain ⟨x, rfl, hx⟩ := hz
    exact combine W Cw hW.le hsumCw
      (hw Q hQβ β a μ Z hβ ha hμ hZ R hR hRwindow x hx P hP i)

end EinsteinFull.Blueprint
