import EinsteinFull.Calculus.C5TestCLTSupport
import Mathlib.Analysis.Complex.OperatorNorm

open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM MeasureTheory ProbabilityTheory
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.Calculus.C5TestCLT
open EinsteinFull.External.Source.AKM EinsteinRelation.ReductionImageV3
open scoped ENNReal

noncomputable section
namespace EinsteinFull.Blueprint

/-- The matrix coordinates satisfy the same-order Schwartz test CLT bound. -/
theorem matrix_test_clt (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (N : ℕ) (hN : 2*d+10 < N) :
    ∃ C : ℝ, 0 < C ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
    ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
    ∀ (R : ℝ) (hR : 1 ≤ R)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))),
      (∀ x, F x (.inr ()) = 0) →
      ‖scaledJointPairing Q R (by linarith) Z F‖ ≤ C * schwartzTestNorm N F := by
  classical
  let r := D.dependenceRange
  have hr1 : 1 ≤ r := D.one_le_dependenceRange
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  let e : Vec d ≃L[ℝ] Vec d :=
    (Units.mk0 r hr.ne') • ContinuousLinearEquiv.refl ℝ (Vec d)
  let rescale : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) →L[ℂ]
      SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e
  have hrescale (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (x : Vec d) : rescale F x = F (r • x) := rfl
  have hnorm_rescale (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      schwartzTestNorm N (rescale F) ≤ r ^ N * schwartzTestNorm N F := by
    apply csSup_le (schwartzTestNorm_set_nonempty N (rescale F))
    rintro q ⟨k, dirs, x, rfl⟩
    have hder : iteratedFDeriv ℝ k.val (fun y => rescale F y) x =
        r ^ k.val • iteratedFDeriv ℝ k.val (fun y => F y) (r • x) := by
      exact congrFun (iteratedFDeriv_comp_const_smul r (F.smooth k.val)) x
    rw [hder, smul_apply, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le _)]
    have hx0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hw : (1 + euclideanNorm x) ^ N ≤ (1 + euclideanNorm (r • x)) ^ N := by
      rw [euclideanNorm_smul r hr.le]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [hr1, hx0]
    have hp : r ^ k.val ≤ r ^ N := pow_le_pow_right₀ hr1 (by omega)
    calc
      _ ≤ r ^ N * ((1 + euclideanNorm (r • x)) ^ N *
          ‖iteratedFDeriv ℝ k.val (fun y => F y) (r • x) (fun j => unitVector (dirs j))‖) := by
        calc
          _ ≤ (1 + euclideanNorm (r • x)) ^ N * (r ^ N *
              ‖iteratedFDeriv ℝ k.val (fun y => F y) (r • x) (fun j => unitVector (dirs j))‖) := by
            gcongr
            exact pow_nonneg (add_nonneg zero_le_one
              (show 0 ≤ euclideanNorm (r • x) from Real.sqrt_nonneg _)) _
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (schwartz_weighted_iterated_basis_le (by omega) F dirs (r • x)) (pow_nonneg hr.le _)
  have htransfer (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (hZ : IsJointObservation Q Z)
      (R : ℝ) (hR : 1 ≤ R) (j i : Fin d)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ)
      (χ : Vec d → ℝ) (hχ : IsSpatialTest (originBall d 1) χ)
      (c : ℝ) (hc : 4 ≤ c)
      (hq : MemLp (fun ω : {ω : FieldPair d // IsRegular D.ellipticity ω} =>
        R ^ (-(d : ℝ) / 2) * ∫ y,
          commutatorObservation Q j i (translate (r • y) (reduce ω.1)) *
            (χ ((R * c)⁻¹ • y) * ℓ (rescale F (R⁻¹ • y))))
        2 (physicalReferenceLaw Q)) :
      ‖scaledComplexClockPairing Q R (Z (.inl (j,i)))
        (fun x => ((χ ((r * c)⁻¹ • x) * ℓ (F x) : ℝ) : ℂ))‖ =
        r ^ d * ‖hq.toLp _‖ := by
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    have hc0 : 0 < c := by linarith
    let f : Vec d → ℝ := fun x => χ ((r * c)⁻¹ • x) * ℓ (F x)
    have hfc : Continuous f := by
      have hχc := hχ.1.continuous
      fun_prop
    have hfcs : HasCompactSupport f :=
      (hχ.2.1.comp_homeomorph
        (Homeomorph.smulOfNeZero (r * c)⁻¹ (inv_ne_zero (mul_pos hr hc0).ne'))).mul_right
    have hf : Integrable f := hfc.integrable_of_hasCompactSupport hfcs
    have hp := (measurePreserving_physical_reduce Q).quasiMeasurePreserving.ae_eq_comp
      (scaledComplexClockPairing_real_observation Q hR0 (Z (.inl (j,i))) (hZ.1 j i) hfc hf)
    let g := fun ω : {ω : FieldPair d // IsRegular D.ellipticity ω} =>
      R ^ (-(d : ℝ) / 2) * ∫ y,
        commutatorObservation Q j i (translate (r • y) (reduce ω.1)) *
          (χ ((R * c)⁻¹ • y) * ℓ (rescale F (R⁻¹ • y)))
    have hg : MemLp (fun ω => r ^ d * g ω) 2 (physicalReferenceLaw Q) :=
      hq.const_smul (r ^ d)
    have heq : ∀ᵐ ω ∂physicalReferenceLaw Q,
        scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => (f x : ℂ))
          (reduce ω.1) = ((r ^ d * g ω : ℝ) : ℂ) := by
      filter_upwards [hp] with ω hω
      simp only [Function.comp_apply] at hω
      rw [hω]
      congr 1
      let H : Vec d → ℝ := fun x => f (R⁻¹ • x) * commutatorObservation Q j i (translate x (reduce ω.1))
      have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure (Vec d)) H r (hR := hr.le)
      simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hi
      have hi' : (∫ x, H x) = r ^ d * ∫ y, H (r • y) := by
        rw [hi]
        field_simp [hr.ne']
      change R ^ (-(d : ℝ) / 2) * (∫ x, H x) = _
      rw [hi']
      dsimp only [g]
      rw [← mul_assoc, mul_comm (R ^ (-(d : ℝ) / 2)) (r ^ d), mul_assoc]
      congr 2
      apply integral_congr_ae
      filter_upwards [] with y
      dsimp only [H, f]
      rw [hrescale]
      have hscale : (r * c)⁻¹ * (R⁻¹ * r) = (R * c)⁻¹ := by
        field_simp [hr.ne', hR0.ne', hc0.ne']
      simp only [smul_smul]
      rw [hscale, mul_comm R⁻¹ r]
      ring
    have hn := norm_complexLp_eq_real_toLp_of_pullback
      (measurePreserving_physical_reduce Q)
      (scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => (f x : ℂ))) hg heq
    rw [hn]
    change ‖hg.toLp ((r ^ d) • g)‖ = _
    rw [MemLp.toLp_const_smul _ hq, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hr.le _)]
  obtain ⟨η, χ, a, ha, hη, hχ, hη01, hone, hχdef, hχa⟩ := exists_dyadic_cutoff_pair d
  let m := d + 1
  let p := m + d
  have hm : (d : ℝ) / 2 < m := by
    dsimp [m]
    push_cast
    linarith only [Nat.cast_nonneg (α := ℝ) d]
  have hmN : m ≤ N := by dsimp [m]; omega
  have hpN : p + 1 ≤ N := by dsimp [p, m]; omega
  obtain ⟨Cη, hCη, hbη⟩ := canonical_commutator_schwartz_cutoff_L2
    d hd D.ellipticity D.one_le_ellipticity m hm hη (le_refl (0 : ℝ))
      (fun x _ => Real.sqrt_nonneg _)
  obtain ⟨Cχ, hCχ, hbχ⟩ := canonical_commutator_schwartz_cutoff_L2
    d hd D.ellipticity D.one_le_ellipticity m hm hχ ha.le hχa
  let Kη := 2 * r ^ d * Cη * r ^ N
  let Kχ := 2 * r ^ d * Cχ * r ^ N
  let B := Kη * 4 ^ p + 2 * Kχ * (a ^ N)⁻¹
  have hKη : 0 < Kη := by dsimp [Kη]; positivity
  have hKχ : 0 < Kχ := by dsimp [Kχ]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨(d : ℝ) ^ 2 * B + 1, by positivity, ?_⟩
  intro Q hQ Z hZ R hR F hclock
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hcoordinate (j i : Fin d) :
      ‖scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => F x (.inl (j,i)))‖ ≤
        B * schwartzTestNorm N F := by
    have hbound (θ : Vec d → ℝ) (hθ : IsSpatialTest (originBall d 1) θ)
        (b : ℝ) (hb : 0 ≤ b) (C : ℝ) (hC : 0 < C)
        (htest : ∀ ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ,
          ‖ℓ‖ ≤ 1 → ∀ c : ℝ, 4 ≤ c →
            ∃ hq : MemLp (fun ω : {ω : FieldPair d // IsRegular D.ellipticity ω} =>
              R ^ (-(d : ℝ) / 2) * ∫ y,
                commutatorObservation Q j i (translate (r • y) (reduce ω.1)) *
                  (θ ((R * c)⁻¹ • y) * ℓ (rescale F (R⁻¹ • y))))
                2 (physicalReferenceLaw Q),
              ‖hq.toLp _‖ ≤ C * c ^ p * schwartzTestNorm N (rescale F) / (1 + c * b) ^ N)
        (c : ℝ) (hc : 4 ≤ c) :
        ‖scaledComplexClockPairing Q R (Z (.inl (j,i)))
          (fun x => (θ ((r * c)⁻¹ • x) : ℂ) * F x (.inl (j,i)))‖ ≤
          (2 * r ^ d * C * r ^ N) * c ^ p * schwartzTestNorm N F / (1 + c * b) ^ N := by
      let π : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℂ :=
        PiLp.proj 2 (fun _ : JointObservationIndex d => ℂ) (.inl (j,i))
      have hπ : ‖π‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound π (by norm_num)
        intro v
        change ‖v (.inl (j,i))‖ ≤ 1 * ‖v‖
        simpa only [one_mul] using PiLp.norm_apply_le v (.inl (j,i))
      let ℓr := Complex.reCLM.comp π
      let ℓi := Complex.imCLM.comp π
      have hℓr : ‖ℓr‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa only [Complex.reCLM_norm, one_mul] using hπ)
      have hℓi : ‖ℓi‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by simpa only [Complex.imCLM_norm, one_mul] using hπ)
      have hreal (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
          ‖scaledComplexClockPairing Q R (Z (.inl (j,i)))
            (fun x => ((θ ((r * c)⁻¹ • x) * ℓ (F x) : ℝ) : ℂ))‖ ≤
            r ^ d * C * r ^ N * c ^ p * schwartzTestNorm N F / (1 + c * b) ^ N := by
        obtain ⟨hq, hqb⟩ := htest ℓ hℓ c hc
        rw [htransfer Q Z hZ R hR j i F ℓ θ hθ c hc hq]
        have hden : 0 < (1 + c * b) ^ N := by
          have hc0 : 0 < c := by linarith
          positivity
        calc
          _ ≤ r ^ d * (C * c ^ p * schwartzTestNorm N (rescale F) / (1 + c * b) ^ N) :=
            mul_le_mul_of_nonneg_left hqb (pow_nonneg hr.le _)
          _ ≤ r ^ d * (C * c ^ p * (r ^ N * schwartzTestNorm N F) / (1 + c * b) ^ N) := by
            gcongr
            exact hnorm_rescale F
          _ = _ := by ring
      let f : Vec d → ℂ := fun x => (θ ((r * c)⁻¹ • x) : ℂ) * F x (.inl (j,i))
      have hfc : Continuous f := by have hθc := hθ.1.continuous; fun_prop
      have hfcs : HasCompactSupport f :=
        ((hθ.2.1.comp_homeomorph (Homeomorph.smulOfNeZero (r * c)⁻¹
          (inv_ne_zero (mul_pos hr (by linarith : 0 < c)).ne'))).comp_left
          (show (↑(0 : ℝ) : ℂ) = 0 from Complex.ofReal_zero)).mul_right
      have hf : Integrable f := hfc.integrable_of_hasCompactSupport hfcs
      have heq : scaledComplexClockPairing Q R (Z (.inl (j,i))) f =
          scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => ((f x).re : ℂ)) +
            Complex.I • scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => ((f x).im : ℂ)) := by
        unfold scaledComplexClockPairing
        rw [complexClockSpatialPairing_re_im Q _ (hf.comp_smul (inv_ne_zero hR0.ne'))
          (hfc.comp (continuous_id.const_smul R⁻¹)), smul_add, smul_comm _ Complex.I]
      have hfr : (fun x => ((f x).re : ℂ)) =
          fun x => ((θ ((r * c)⁻¹ • x) * ℓr (F x) : ℝ) : ℂ) := by
        funext x
        simp [f, ℓr, π, Complex.mul_re]
      have hfi : (fun x => ((f x).im : ℂ)) =
          fun x => ((θ ((r * c)⁻¹ • x) * ℓi (F x) : ℝ) : ℂ) := by
        funext x
        simp [f, ℓi, π, Complex.mul_im]
      change ‖scaledComplexClockPairing Q R (Z (.inl (j,i))) f‖ ≤ _
      rw [heq]
      calc
        _ ≤ ‖scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => ((f x).re : ℂ))‖ +
            ‖Complex.I • scaledComplexClockPairing Q R (Z (.inl (j,i))) (fun x => ((f x).im : ℂ))‖ := norm_add_le _ _
        _ ≤ _ := by
          rw [norm_smul, Complex.norm_I, one_mul, hfr, hfi]
          have hrb := hreal ℓr hℓr
          have hib := hreal ℓi hℓi
          exact (add_le_add hrb hib).trans_eq (by ring)
    have hcenter := hbound η hη 0 (le_refl _) Cη hCη
      (fun ℓ hℓ c hc => hbη r Q N hmN R hR j i (rescale F) ℓ hℓ c hc) 4 (le_refl _)
    have hpieces (n : ℕ) := hbound χ hχ a ha.le Cχ hCχ
      (fun ℓ hℓ c hc => hbχ r Q N hmN R hR j i (rescale F) ℓ hℓ c hc)
      (8 * (2 : ℝ) ^ n) (by have hh := one_le_pow₀ (n := n) (by norm_num : (1 : ℝ) ≤ 2); nlinarith)
    let b : ℕ → ℝ := fun n => Kχ * schwartzTestNorm N F *
      ((8 * (2 : ℝ) ^ n) ^ p / (1 + (8 * (2 : ℝ) ^ n) * a) ^ N)
    have hs : Summable b := (summable_dyadic_schwartz_decay hpN ha (by norm_num : (1 : ℝ) ≤ 8)).mul_left _
    have hsum : (∑' n, b n) ≤ 2 * Kχ * (a ^ N)⁻¹ * schwartzTestNorm N F := by
      dsimp only [b]
      rw [tsum_mul_left]
      have hh := mul_le_mul_of_nonneg_left
        (tsum_dyadic_schwartz_decay_le hpN ha (by norm_num : (1 : ℝ) ≤ 8))
        (mul_nonneg hKχ.le (clockSchwartz_norm_nonneg N F))
      exact hh.trans_eq (by ring)
    have hmain := norm_scaledComplexClockPairing_le_of_dyadic_cutoff Q hR0 (Z (.inl (j,i))) F
      (.inl (j,i)) (η := fun x => η (r⁻¹ • x)) (χ := fun x => χ (r⁻¹ • x))
      (hη.1.continuous.comp (continuous_id.const_smul r⁻¹))
      (by simpa using hone 0 (by simp [euclideanNorm, euclideanSq, dot]; positivity))
      (fun x => hη01 _) (fun x => by simpa only [smul_smul, mul_comm] using hχdef (r⁻¹ • x))
      4 hs (B := Kη * 4 ^ p * schwartzTestNorm N F)
      (by simpa only [mul_zero, zero_mul, add_zero, one_pow, div_one, Kη, mul_inv_rev, smul_smul, mul_comm] using hcenter)
      (fun n => by
        have hh := hpieces n
        have he (x : Vec d) : r⁻¹ • (((2 : ℝ) ^ (n+1))⁻¹ • ((4 : ℝ)⁻¹ • x)) =
            (r * (8 * (2 : ℝ) ^ n))⁻¹ • x := by
          simp only [pow_succ, mul_inv_rev, smul_smul]
          congr 1
          ring
        simpa only [he, b, Kχ, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hh)
    calc
      _ ≤ Kη * 4 ^ p * schwartzTestNorm N F + ∑' n, b n := hmain
      _ ≤ Kη * 4 ^ p * schwartzTestNorm N F +
          2 * Kχ * (a ^ N)⁻¹ * schwartzTestNorm N F := add_le_add le_rfl hsum
      _ = B * schwartzTestNorm N F := by dsimp only [B]; ring
  have hmain := norm_scaledJointPairing_le_coordinate_sum Q hR0 Z F
  have hzero : scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ())) = 0 := by
    simp [scaledComplexClockPairing, complexClockSpatialPairing, hclock]
  rw [hzero, norm_zero, add_zero] at hmain
  calc
    _ ≤ ∑ p : Fin d × Fin d, ‖scaledComplexClockPairing Q R (Z (.inl p)) (fun x => F x (.inl p))‖ := hmain
    _ ≤ ∑ _p : Fin d × Fin d, B * schwartzTestNorm N F :=
      Finset.sum_le_sum fun p _ => hcoordinate p.1 p.2
    _ = (d : ℝ) ^ 2 * B * schwartzTestNorm N F := by simp [pow_two, mul_assoc]
    _ ≤ ((d : ℝ) ^ 2 * B + 1) * schwartzTestNorm N F := by
      nlinarith only [clockSchwartz_norm_nonneg N F]

end EinsteinFull.Blueprint
