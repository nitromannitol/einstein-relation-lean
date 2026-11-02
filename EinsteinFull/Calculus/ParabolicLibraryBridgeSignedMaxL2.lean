import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedMax

/-!
# Signed local maximum principle with an `L²` right-hand side

The Moser iteration of `ParabolicLibraryBridgeSignedMax` is rerun with starting exponent `p₀ = 2`
(allowed because the reverse Hölder step holds for every `p ≥ (d+1)/d`), giving
`ess sup |u| ≤ C ‖u‖_{L²}` on `B_{3/8} × (-11/16, 0)` in terms of `B_{1/2} × (-3/4, 0)`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.SignedLocalMax

open MeasureTheory Set Filter Topology Finset PDE PDE.Parabolic.LocalMax

theorem moser_iteration_essSup_Zp (d : ℕ) (hd : 0 < d) (p0 : ℝ) (hp0 : 0 < p0) (A : ℝ)
    (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d × ℝ → ℝ,
      AEMeasurable f (volume.restrict (moserCylZ d (1 / 2) (-3 / 4))) →
      (∀ p : ℝ, p0 ≤ p → ∀ r ρ T T' : ℝ, 3 / 8 ≤ r → r < ρ → ρ ≤ 1 / 2 →
        -3 / 4 ≤ T → T < T' → T' ≤ -11 / 16 →
        ∫⁻ z in moserCylZ d r T', ENNReal.ofReal (f z) ^ (p * (((d : ℝ) + 2) / d)) ≤
          ENNReal.ofReal (A * (1 / (ρ - r) ^ 2 + 1 / (T' - T))) ^ (((d : ℝ) + 2) / d) *
            (∫⁻ z in moserCylZ d ρ T, ENNReal.ofReal (f z) ^ p) ^ (((d : ℝ) + 2) / d)) →
      essSup (fun z => ENNReal.ofReal (f z)) (volume.restrict (moserCylZ d (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C *
          (∫⁻ z in moserCylZ d (1 / 2) (-3 / 4), ENNReal.ofReal (f z) ^ p0) ^ p0⁻¹ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ, χ = ((d : ℝ) + 2) / d := ⟨_, rfl⟩
  have hχ1 : 1 < χ := by
    rw [hχdef, lt_div_iff₀ hd0]; linarith
  have hA' : 1 ≤ 1280 * A := by linarith
  set S₁ := χ / (χ - 1) / p0
  set S₂ := χ / (χ - 1) ^ 2 / p0
  refine ⟨(1280 * A) ^ S₁ * 4 ^ S₂, mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by norm_num) _), fun f hf hstep => ?_⟩
  rw [← hχdef] at hstep
  set p : ℕ → ℝ := fun k => p0 * χ ^ k with hpdef
  set rr : ℕ → ℝ := fun k => 3 / 8 + ((2 : ℝ) ^ k)⁻¹ / 8 with hrr
  set TT : ℕ → ℝ := fun k => -11 / 16 - ((2 : ℝ) ^ k)⁻¹ / 16 with hTT
  set J : ℕ → ℝ≥0∞ := fun k => ∫⁻ z in moserCylZ d (rr k) (TT k), ENNReal.ofReal (f z) ^ p k
    with hJ
  have hu1 : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ k := fun k => one_le_pow₀ (by norm_num)
  have hinv : ∀ k : ℕ, ((2 : ℝ) ^ k)⁻¹ ≤ 1 := fun k => inv_le_one_of_one_le₀ (hu1 k)
  have hinvpos : ∀ k : ℕ, 0 < ((2 : ℝ) ^ k)⁻¹ := fun k => inv_pos.2 (by positivity)
  have hpk : ∀ k, 0 < p k := fun k => mul_pos hp0 (pow_pos (by linarith) _)
  have hpχ : ∀ k, p (k + 1) = p k * χ := fun k => by simp only [hpdef]; ring
  have hstepJ : ∀ k, J (k + 1) ≤
      ENNReal.ofReal (1280 * A * 4 ^ k) ^ χ * J k ^ χ := by
    intro k
    have hu := hu1 k
    have hrk : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge : p0 ≤ p k := by
      have : (1 : ℝ) ≤ χ ^ k := one_le_pow₀ hχ1.le
      simp only [hpdef]; nlinarith
    have hi := hinv k
    have hi' := hinvpos k
    have hi2 : ((2 : ℝ) ^ (k + 1))⁻¹ = (2 * 2 ^ k)⁻¹ := by rw [hrk]
    have hh : ((2 : ℝ) ^ (k + 1))⁻¹ = ((2 : ℝ) ^ k)⁻¹ / 2 := by
      rw [pow_succ]; field_simp
    have key := hstep (p k) hge (rr (k + 1)) (rr k) (TT k) (TT (k + 1))
      (by simp only [hrr]; linarith [hinvpos (k + 1)])
      (by simp only [hrr]; linarith [hinvpos (k + 1)])
      (by simp only [hrr]; linarith)
      (by simp only [hTT]; linarith)
      (by simp only [hTT]; linarith [hinvpos (k + 1)])
      (by simp only [hTT]; linarith [hinvpos (k + 1)])
    have hconst := step_const_le (u := 2 ^ k) hA hu
    have e4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    have hmono : ENNReal.ofReal (A * (1 / (rr k - rr (k + 1)) ^ 2 + 1 / (TT (k + 1) - TT k))) ≤
        ENNReal.ofReal (1280 * A * 4 ^ k) := by
      apply ENNReal.ofReal_le_ofReal
      rw [e4]
      simp only [hrr, hTT, hi2]
      simpa [hrk] using hconst
    calc J (k + 1) = ∫⁻ z in moserCylZ d (rr (k + 1)) (TT (k + 1)),
          ENNReal.ofReal (f z) ^ (p k * χ) := by simp only [hJ, hpχ]
      _ ≤ _ := key.trans (by gcongr)
  have hmain := iterate_bound (J := J) (p := p) (a := fun k => 1280 * A * 4 ^ k) (by linarith)
    hpk hpχ (fun k => by positivity) hstepJ
  have hprod : ∀ k, ∏ j ∈ range k, (1280 * A * 4 ^ j) ^ (p j)⁻¹ ≤ (1280 * A) ^ S₁ * 4 ^ S₂ :=
    fun k => PDE.DGNMMoser.prod_geometric_le hχ1 hp0 hA' (by norm_num) k
  set Q : Set (Vec d × ℝ) := moserCylZ d (3 / 8) (-11 / 16) with hQ
  have hfin : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_moserCylZ_ne_top d (by norm_num) _).lt_top⟩
  have hQsub : ∀ k, Q ⊆ moserCylZ d (rr k) (TT k) := fun k =>
    moserCylZ_mono d (by norm_num) (by simp only [hrr]; linarith [hinvpos k])
      (by simp only [hTT]; linarith [hinvpos k])
  have hQbig : Q ⊆ moserCylZ d (1 / 2) (-3 / 4) :=
    moserCylZ_mono d (by norm_num) (by norm_num) (by norm_num)
  have hfm : AEMeasurable f (volume.restrict Q) :=
    hf.mono_measure (Measure.restrict_mono hQbig le_rfl)
  set g : Vec d × ℝ → ℝ := fun z => max (f z) 0 with hg
  have hgm : AEMeasurable g (volume.restrict Q) := hfm.max aemeasurable_const
  have hgo : (fun z => ENNReal.ofReal (g z)) = fun z => ENNReal.ofReal (f z) := by
    funext z; simp only [hg]; rcases le_total (f z) 0 with h | h <;> simp [h]
  have hgen : ∀ z, ‖g z‖ₑ = ENNReal.ofReal (f z) := fun z => by
    rw [Real.enorm_eq_ofReal (le_max_right _ _), ← congrFun hgo z]
  have hptend : Tendsto p atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hχ1).const_mul_atTop hp0
  have h0 : J 0 = ∫⁻ z in moserCylZ d (1 / 2) (-3 / 4), ENNReal.ofReal (f z) ^ p0 := by
    simp only [hJ, hrr, hTT, hpdef]; norm_num
  have hbound := PDE.DGNMMoser.essSup_ofReal_le_of_eLpNorm_le (μ := volume.restrict Q) (f := g)
    hgm hptend
    (B := ENNReal.ofReal ((1280 * A) ^ S₁ * 4 ^ S₂) * J 0 ^ (p 0)⁻¹) (fun k => by
      have hq0 : ENNReal.ofReal (p k) ≠ 0 := by simpa using hpk k
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top
        hgm.aestronglyMeasurable, ENNReal.toReal_ofReal (hpk k).le]
      simp only [hgen]
      calc (∫⁻ z in Q, ENNReal.ofReal (f z) ^ p k) ^ (1 / p k) ≤ J k ^ (p k)⁻¹ := by
            rw [one_div]
            refine ENNReal.rpow_le_rpow ?_ (inv_nonneg.2 (hpk k).le)
            exact lintegral_mono_set (hQsub k)
        _ ≤ ENNReal.ofReal (∏ j ∈ range k, (1280 * A * 4 ^ j) ^ (p j)⁻¹) * J 0 ^ (p 0)⁻¹ :=
            hmain k
        _ ≤ _ := by gcongr; exact hprod k)
  rw [hgo] at hbound
  have e0 : p 0 = p0 := by simp [hpdef]
  rw [e0, h0] at hbound
  exact hbound

/-- Signed local maximum principle with an `L²` right-hand side, up to the top time. -/
theorem signed_local_max_L2 (d : ℕ) (hd : 0 < d) {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hstep : PowerStepPropS d C₀) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ C₁ : ℝ, 0 < C₁ ∧ ∀ (a : ParCoeffField d),
      IsParabolicCoeff 1 Lam a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ u : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution a (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u →
      essSup (fun z => ENNReal.ofReal |u.toFun z|)
          (volume.restrict (moserCylZ d (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C₁ *
          (∫⁻ z in moserCylZ d (1 / 2) (-3 / 4),
            ENNReal.ofReal |u.toFun z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set A : ℝ := max 1 (C₀ * Lam * ((d : ℝ) + 3) ^ 2) with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  obtain ⟨C₁, hC₁, hmoser⟩ := moser_iteration_essSup_Zp d hd 2 (by norm_num) A hA1
  refine ⟨C₁, hC₁, fun a ha u hu => ?_⟩
  set Q := moserCylZ d (1 / 2) (-3 / 4) with hQ
  have hsub : Q ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 := by
    intro z hz
    refine ⟨euclideanBall_mono (by norm_num) (by norm_num) hz.1, ?_⟩
    exact ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩
  have hmeas_u : AEMeasurable u.toFun (volume.restrict Q) :=
    (u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hsub le_rfl)).aemeasurable
  have hVfin : volume Q ≠ ⊤ := volume_moserCylZ_ne_top d (by norm_num) _
  have hChi : (0 : ℝ) < ((d : ℝ) + 2) / d := by positivity
  have hshift : ∀ ε : ℝ, 0 < ε →
      essSup (fun z => ENNReal.ofReal |u.toFun z|)
          (volume.restrict (moserCylZ d (3 / 8) (-11 / 16)))
        ≤ ENNReal.ofReal C₁ *
          (∫⁻ z in Q, ENNReal.ofReal (|u.toFun z| + ε) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
    intro ε hε
    have hfm : AEMeasurable (fun z => |u.toFun z| + ε) (volume.restrict Q) :=
      hmeas_u.abs.add_const ε
    have hε' := hmoser (fun z => |u.toFun z| + ε) hfm (by
      intro p hp r ρ T T' hr hrρ hρ hT hTT' hT'
      have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
      have hpd : ((d : ℝ) + 1) / d ≤ p := by
        refine le_trans ?_ hp
        rw [div_le_iff₀ hd0]
        linarith
      have key := hstep Lam hLam a ha u hu ε hε p hp1 r ρ T T' 0 (by linarith)
        hrρ (by linarith) (by linarith) hTT' (by linarith) le_rfl
      refine key.trans ?_
      have hS : 0 ≤ 1 / (ρ - r) ^ 2 + 1 / (T' - T) := by
        have : 0 < ρ - r := by linarith
        have : 0 < T' - T := by linarith
        positivity
      have hc : C₀ * Lam * (2 + p / (p - 1)) ^ 2 ≤ A :=
        (step_const_bound hd hC₀ hLam hpd).trans (le_max_right _ _)
      exact mul_le_mul' (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hc hS)) hChi.le) le_rfl)
    refine le_trans (essSup_mono_ae (f := fun z => ENNReal.ofReal |u.toFun z|)
      (g := fun z => ENNReal.ofReal (|u.toFun z| + ε))
      (Filter.Eventually.of_forall fun z => ?_)) hε'
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmink : ∀ ε : ℝ, 0 < ε →
      (∫⁻ z in Q, ENNReal.ofReal (|u.toFun z| + ε) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ ≤
        (∫⁻ z in Q, ENNReal.ofReal |u.toFun z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ +
          ENNReal.ofReal ε * volume Q ^ (2 : ℝ)⁻¹ := by
    intro ε hε
    have hm := ENNReal.lintegral_Lp_add_le (μ := volume.restrict Q)
      (f := fun z => ENNReal.ofReal |u.toFun z|) (g := fun _ => ENNReal.ofReal ε)
      hmeas_u.abs.ennreal_ofReal aemeasurable_const (by norm_num : (1 : ℝ) ≤ 2)
    simp only [one_div] at hm
    have h2 : (ENNReal.ofReal ε ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ = ENNReal.ofReal ε := by
      rw [← ENNReal.rpow_mul, mul_inv_cancel₀ (by norm_num), ENNReal.rpow_one]
    have hconst : (∫⁻ _ in Q, ENNReal.ofReal ε ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ =
        ENNReal.ofReal ε * volume Q ^ (2 : ℝ)⁻¹ := by
      rw [lintegral_const, Measure.restrict_apply_univ,
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity), h2]
    refine le_trans (ENNReal.rpow_le_rpow ?_ (by positivity)) (hm.trans (le_of_eq ?_))
    · refine lintegral_mono fun z => ENNReal.rpow_le_rpow ?_ (by norm_num)
      simpa using ENNReal.ofReal_add_le (p := |u.toFun z|) (q := ε)
    · rw [hconst]
  have hK : ENNReal.ofReal C₁ * volume Q ^ (2 : ℝ)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) hVfin)
  refine le_of_forall_pos_le_add_mul hK fun ε hε => ?_
  refine (hshift ε hε).trans ?_
  calc ENNReal.ofReal C₁ * (∫⁻ z in Q, ENNReal.ofReal (|u.toFun z| + ε) ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹
      ≤ ENNReal.ofReal C₁ * ((∫⁻ z in Q, ENNReal.ofReal |u.toFun z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ +
          ENNReal.ofReal ε * volume Q ^ (2 : ℝ)⁻¹) := by gcongr; exact hmink ε hε
    _ = _ := by ring

end EinsteinFull.SignedLocalMax
