import EinsteinRelation.Sharpness.SharpVelocityFromFukushima
import EinsteinRelation.Diffusion.VelocityTimeChangeGMP
import EinsteinRelation.Clock.CentredClockField

/-! # Step 3 of Proposition 7.1: the clock identity

Source: `paper/main.tex` 1251-1267. For the sharp environment, the drift of the first coordinate
is `b₁ = ½ D·(a e₁) + λ a₁₁ = (μ - 1)/δ + λ a₁₁` (the definition of `μ` in
`eq.sharp-coefficients`). By `QuenchedDriftMartingaleStep` and Step 2, the time averages of `b₁`
along the reduced path converge to `ℓ(λ)·e₁ = λ`. The time averages of `μ` converge to the clock rate
`η`, by the GMP velocity time change. So the time averages of `a₁₁` converge to
`A = 1 + (1 - η)/(δλ)`, and `η = 1 - δλ(A - 1)` (`sharpClockIdentityStep_of_inputs`).
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

open EinsteinRelation.External.GantertSection7Support

noncomputable section

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-- Time averages of a bounded continuous function that converge along `t = (n+1)²` converge
along all times. -/
theorem tendsto_average_of_tendsto_sq {f : ℝ → ℝ} (hfc : Continuous f) {B : ℝ}
    (hB : ∀ u, |f u| ≤ B) {L : ℝ}
    (h : Tendsto (fun n : ℕ => (∫ u in (0 : ℝ)..((n : ℝ) + 1) ^ 2, f u) / ((n : ℝ) + 1) ^ 2)
      atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => (∫ u in (0 : ℝ)..t, f u) / t) atTop (𝓝 L) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hii : ∀ a b : ℝ, IntervalIntegrable f volume a b := fun a b =>
    hfc.intervalIntegrable a b
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp h (ε / 2) (by positivity)
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℕ, 12 * B / ε < K₀ := exists_nat_gt _
  refine ⟨((max (N₁ + 1) (K₀ + 1) : ℕ) : ℝ) ^ 2, fun t ht => ?_⟩
  set k : ℕ := ⌊Real.sqrt t⌋₊ with hkdef
  have hmax1 : (1 : ℝ) ≤ ((max (N₁ + 1) (K₀ + 1) : ℕ) : ℝ) := by
    exact_mod_cast le_trans (Nat.le_add_left 1 N₁) (le_max_left _ _)
  have ht1 : 1 ≤ t := le_trans (by nlinarith) ht
  have ht0 : 0 < t := by linarith
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hk_le : (k : ℝ) ≤ Real.sqrt t := Nat.floor_le (Real.sqrt_nonneg _)
  have hk_lt : Real.sqrt t < k + 1 := Nat.lt_floor_add_one _
  have hkmax : max (N₁ + 1) (K₀ + 1) ≤ k := by
    rw [hkdef, Nat.le_floor_iff (Real.sqrt_nonneg _)]
    rw [show ((max (N₁ + 1) (K₀ + 1) : ℕ) : ℝ) = Real.sqrt ((((max (N₁ + 1) (K₀ + 1)) : ℕ) : ℝ) ^ 2)
      from (Real.sqrt_sq (Nat.cast_nonneg _)).symm]
    exact Real.sqrt_le_sqrt ht
  have hk1 : 1 ≤ k := le_trans (Nat.le_add_left 1 N₁) ((le_max_left _ _).trans hkmax)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  set n : ℕ := k - 1 with hndef
  have hnk : ((n : ℝ) + 1) = k := by
    rw [hndef, Nat.cast_sub hk1]; ring
  set T : ℝ := ((n : ℝ) + 1) ^ 2 with hTdef
  have hT : T = (k : ℝ) ^ 2 := by rw [hTdef, hnk]
  have hTt : T ≤ t := by
    rw [hT]
    calc (k : ℝ) ^ 2 ≤ Real.sqrt t ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hk_le 2
      _ = t := hsq
  have htT : t < ((k : ℝ) + 1) ^ 2 := by
    calc t = Real.sqrt t ^ 2 := hsq.symm
      _ < ((k : ℝ) + 1) ^ 2 := pow_lt_pow_left₀ hk_lt (Real.sqrt_nonneg _) (by norm_num)
  have hTpos : 0 < T := by rw [hT]; positivity
  have hnN : N₁ ≤ n := by
    have := (le_max_left (N₁ + 1) (K₀ + 1)).trans hkmax
    omega
  have hkK : K₀ + 1 ≤ k := (le_max_right _ _).trans hkmax
  -- The difference between the averages at `t` and at `T`.
  set F : ℝ → ℝ := fun s => ∫ u in (0 : ℝ)..s, f u with hFdef
  have hFT : |F t - F T| ≤ B * (t - T) := by
    have hsplit : F t - F T = ∫ u in T..t, f u := by
      simp only [hFdef]
      rw [← intervalIntegral.integral_add_adjacent_intervals (hii 0 T) (hii T t)]
      ring
    rw [hsplit]
    have h1 : ‖∫ u in T..t, f u‖ ≤ B * |t - T| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
        rw [Real.norm_eq_abs]; exact hB u
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ t - T by linarith)] at h1
    exact h1
  have hFTb : |F T| ≤ B * T := by
    have h1 : ‖∫ u in (0 : ℝ)..T, f u‖ ≤ B * |T - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
        rw [Real.norm_eq_abs]; exact hB u
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hTpos] at h1
    exact h1
  have hdiff : |F t / t - F T / T| ≤ 2 * B * (t - T) / t := by
    have e : F t / t - F T / T = (F t - F T) / t + F T * (T - t) / (t * T) := by
      field_simp; ring
    rw [e]
    calc |(F t - F T) / t + F T * (T - t) / (t * T)|
        ≤ |(F t - F T) / t| + |F T * (T - t) / (t * T)| := abs_add_le _ _
      _ ≤ B * (t - T) / t + B * T * (t - T) / (t * T) := by
          gcongr
          · rw [abs_div, abs_of_pos ht0]; exact div_le_div_of_nonneg_right hFT ht0.le
          · rw [abs_div, abs_mul, abs_of_pos (mul_pos ht0 hTpos),
              abs_of_nonpos (show T - t ≤ 0 by linarith), neg_sub]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hFTb (by linarith))
              (by positivity)
      _ = 2 * B * (t - T) / t := by field_simp; ring
  have hsmall : 2 * B * (t - T) / t < ε / 2 := by
    have hgap : t - T ≤ 2 * k + 1 := by rw [hT]; nlinarith
    have hK : 12 * B / ε < k := lt_of_lt_of_le hK₀ (by exact_mod_cast (Nat.le_succ K₀).trans hkK)
    rw [div_lt_iff₀ hε] at hK
    rw [div_lt_iff₀ ht0]
    have hkt : (k : ℝ) ^ 2 ≤ t := by rw [← hT]; exact hTt
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have e1 : 2 * B * (t - T) ≤ 2 * B * (2 * k + 1) :=
      mul_le_mul_of_nonneg_left hgap (by positivity)
    have e2 : 2 * B * (2 * k + 1) ≤ 6 * B * k := by
      nlinarith [mul_nonneg hB0 (sub_nonneg.mpr hk1R)]
    have e3 : 6 * B * k < ε / 2 * (k : ℝ) ^ 2 := by
      nlinarith [mul_lt_mul_of_pos_left hK hkpos]
    have e4 : ε / 2 * (k : ℝ) ^ 2 ≤ ε / 2 * t := mul_le_mul_of_nonneg_left hkt (by positivity)
    linarith
  have hTL := hN₁ n hnN
  rw [Real.dist_eq] at hTL ⊢
  calc |F t / t - L| ≤ |F t / t - F T / T| + |F T / T - L| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hdiff.trans hsmall.le) hTL
    _ = ε := by ring

/-- The pointwise column divergence is Borel measurable on field pairs. -/
theorem measurable_cdiv (i : Fin d) : Measurable (DriftH5.cdiv (d := d) i) := by
  unfold DriftH5.cdiv
  refine Finset.measurable_sum _ fun j _ => ?_
  have hc : Continuous (Function.uncurry fun (w : FieldPair d) (x : Vec d) => (w.1 x) j i) :=
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem
      j i
  exact (measurable_fderiv_apply_const_with_param ℝ hc (unitVector j)).comp
    (measurable_id.prodMk measurable_const)

/-- **The sharp identity at the origin**: `½ D·(a e₁) = (μ - 1)/δ` under the reduced law of a sharp
environment (the definition of `μ` in `eq.sharp-coefficients`). -/
theorem ae_half_cdiv_eq_of_sharp (hd : 2 ≤ d) {Λ₀ r₀ δ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hsharp : IsSharpLaw hd δ Q) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      (1 / 2 : ℝ) * DriftH5.cdiv (⟨0, by omega⟩ : Fin d) w = (w.2 0 - 1) / δ := by
  obtain ⟨hδ, ε, P, hgrad, hμ, -, hQP⟩ := hsharp
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  have hpm := measurable_sharpPhysicalPair i₀ δ ε hgrad hμ
  have hset : MeasurableSet {w : FieldPair d | (1 / 2 : ℝ) * DriftH5.cdiv i₀ w = (w.2 0 - 1) / δ} :=
    measurableSet_eq_fun ((measurable_cdiv i₀).const_mul _)
      ((((continuous_eval_const (0 : Vec d)).comp continuous_snd).measurable.sub_const 1).div_const δ)
  unfold Carriers.reducedReferenceLaw
  refine (ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hset).2 ?_
  rw [hQP]
  refine (ae_map_iff hpm.aemeasurable
    (hset.preimage (Probability.measurable_reduce (d := d)))).2 (ae_of_all _ fun W => ?_)
  simp only [Set.mem_setOf_eq]
  set ψ : Vec d → ℝ := fun y => ε * seedField d W y with hψdef
  have hdens : ∀ x, 0 < densityField i₀ δ ψ x := fun x => by linarith [(hμ W x).1]
  have hred : ∀ x, (reduce (sharpPhysicalPair i₀ δ ε hgrad hμ W)).1 x = coefficientField i₀ ψ x :=
    fun x => reducedCoefficient_physicalEnvironment i₀ δ ψ _ _ x (hdens x)
  have hclock : (reduce (sharpPhysicalPair i₀ δ ε hgrad hμ W)).2 0 = densityField i₀ δ ψ 0 :=
    physicalEnvironment_clockDensity i₀ δ ψ _ _ 0 (hdens 0)
  rw [hclock]
  unfold DriftH5.cdiv densityField divergence coordinateDerivative
  have hfun : ∀ k : Fin d, (fun x => ((reduce (sharpPhysicalPair i₀ δ ε hgrad hμ W)).1 x) k i₀) =
      fun y => ((coefficientField i₀ ψ y).mulVec (unitVector i₀)) k := by
    intro k
    funext y
    rw [hred]
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  simp only [hfun]
  field_simp
  ring

/-- **Step 3 of Proposition 7.1** (`eq.sharp-clock`, `paper/main.tex` 1251-1267): for the sharp law
and every GMP reduced family, at each force `0 < λ ≤ 1` the time averages of `a₁₁` along the
reduced paths converge almost surely to the deterministic `A = 1 + (1 - η)/(δλ)`, and the clock rate
is `η = 1 - δλ(A - 1)`. Here `η` is the clock rate of the GMP velocity time change. -/
theorem sharpClockIdentityStep_of_inputs (hFOT : FukushimaDecompositionInput)
    (hPF : External.GMPPhysicalFamilyExistence) (hTC : External.GMPTimeChangeLaw)
    (hVX : External.GMPVelocityExistence) (hPos : External.GMPPhysicalVelocityPositive)
    (hRV : External.GMPReducedVelocityExistence) (hd : 2 ≤ d) : SharpClockIdentityStep hd := by
  intro Λ₀ r₀ δ Q hsharp P' hP' lam hl0 hl1
  have hδ : 0 < δ := hsharp.1
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  obtain ⟨P, hP⟩ := hPF d hd Λ₀ r₀ Q
  obtain ⟨vX, hvX⟩ := hVX d hd Λ₀ r₀ Q P hP lam hl0 hl1
  obtain ⟨vY, hvY, -⟩ := hRV d hd Λ₀ r₀ Q P' hP' lam hl0 hl1
  have hposX := hPos d hd Λ₀ r₀ Q P hP lam hl0 hl1 vX hvX
  obtain ⟨-, hclock⟩ := gmp_velocity_timeChange hd Q P P' hP hP'
    (hTC d hd Λ₀ r₀ Q P P' hP hP') hl0 hl1 hvX hvY hposX
  set η := dot (unitVector i₀) vY / dot (unitVector i₀) vX with hηdef
  have hvY1 : dot vY (unitVector i₀) = lam :=
    sharpVelocityStep_of_fukushima hFOT hd Λ₀ r₀ δ Q hsharp P' hP' lam hl0 hl1 vY hvY
  have hvYi : vY i₀ = lam := by
    rw [← hvY1]; simp [dot, unitVector, Pi.single_apply]
  set A : ℝ := 1 + (1 - η) / (δ * lam) with hAdef
  have hηA : 1 - δ * lam * (A - 1) = η := by
    rw [hAdef]; field_simp; ring
  refine ⟨A, ?_, ?_⟩
  swap
  · rw [hηA]; exact hclock
  have hQref := Clock.isStationary_reducedReferenceLaw Q
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  obtain ⟨C, hC⟩ := quenchedDriftMartingaleStep_of_fukushima hFOT d hd Λ₀ r₀ Q P' hP' lam hl0 hl1
    hQref i₀ (DriftH5.cdiv i₀) (DriftH5.hasWeakHorizontalDivergence_reducedColumn Q hQref i₀)
  set T : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 with hTdef
  have hT : ∀ n, 0 < T n := fun n => by positivity
  have hCall := ae_all_iff.mpr fun n => hC (T n) (hT n).le
  set b₂ : FieldPair d → ℝ := fun w => (w.2 0 - 1) / δ + lam * (w.1 0) i₀ i₀ with hb₂def
  have hb : velocityDrift hd lam i₀ (DriftH5.cdiv i₀) =ᵐ[Carriers.reducedReferenceLaw Q] b₂ := by
    filter_upwards [ae_half_cdiv_eq_of_sharp hd Q hsharp] with w hw
    unfold velocityDrift
    rw [hw]
    rfl
  have hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw (P' lam)) := hP' lam hl0.le hl1
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) := by
    filter_upwards [hGMP] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    haveI := r.pathLaw_isMarkovKernel
    rw [hr]
    infer_instance
  have hver := ae_all_iff.mpr fun n =>
    ae_driftMartingalePart_eq hd Q hl0.le hl1 (P' lam) hprob hGMP hb i₀ (hT n).le
  filter_upwards [hCall, hver, hvY, hclock, hGMP] with ω hCω hverω hvYω hclockω hGω
  obtain ⟨hω', r, hr⟩ := hGω
  haveI := r.pathLaw_isMarkovKernel
  haveI : IsProbabilityMeasure (P' lam (0, ω)) := by rw [show P' lam (0, ω) = r.pathLaw 0 from hr]; infer_instance
  -- Borel–Cantelli for the martingale part along `T n`.
  have hX : ∀ᵐ γ ∂(P' lam (0, ω)), Tendsto (fun n =>
      driftMartingalePart (velocityDrift hd lam i₀ (DriftH5.cdiv i₀)) i₀ (T n) (ω, γ) / T n)
      atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_sum_integral_sq _ (fun n => ?_) (fun n => C / ((n : ℝ) + 1) ^ 2)
      (fun n => ?_) (fun n => ?_) ?_
    · exact (continuous_id.div_const (T n)).comp_aestronglyMeasurable
        (hCω n).1.aestronglyMeasurable
    · refine ((hCω n).1.integrable_sq.div_const (T n ^ 2)).congr (ae_of_all _ fun γ => ?_)
      simp only [div_pow]
    · have heq : ∫ γ, (driftMartingalePart (velocityDrift hd lam i₀ (DriftH5.cdiv i₀)) i₀ (T n)
            (ω, γ) / T n) ^ 2 ∂(P' lam (0, ω)) =
          (∫ γ, driftMartingalePart (velocityDrift hd lam i₀ (DriftH5.cdiv i₀)) i₀ (T n) (ω, γ) ^ 2
            ∂(P' lam (0, ω))) / T n ^ 2 := by
        rw [← integral_div]
        exact integral_congr_ae (ae_of_all _ fun γ => by simp only [div_pow])
      rw [heq, div_le_iff₀ (by positivity)]
      calc ∫ γ, driftMartingalePart (velocityDrift hd lam i₀ (DriftH5.cdiv i₀)) i₀ (T n) (ω, γ) ^ 2
            ∂(P' lam (0, ω)) ≤ C * T n := (hCω n).2
        _ = C / ((n : ℝ) + 1) ^ 2 * T n ^ 2 := by simp only [hTdef]; field_simp
    · have h := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr
        (by norm_num))
      have h' : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        refine h.congr fun n => ?_
        push_cast
        ring
      simpa [div_eq_mul_one_div C] using h'.mul_left C
  have hver' : ∀ᵐ γ ∂(P' lam (0, ω)), ∀ n,
      driftMartingalePart (velocityDrift hd lam i₀ (DriftH5.cdiv i₀)) i₀ (T n) (ω, γ) =
        driftMartingalePart b₂ i₀ (T n) (ω, γ) := ae_all_iff.mpr hverω
  have hvYω' : ∀ᵐ γ ∂(P' lam (0, ω)), HasPathVelocity γ vY := hvYω
  filter_upwards [hX, hver', hvYω', hclockω] with γ hXγ hvγ hvelγ hclγ
  -- The deterministic limit along the path.
  set f : ℝ → ℝ := fun u => sharpA11 hd ω (γ u.toNNReal) with hfdef
  set m : ℝ → ℝ := fun u => clockDensity ω (γ u.toNNReal) with hmdef
  have hγc : Continuous fun u : ℝ => γ u.toNNReal := γ.continuous.comp continuous_real_toNNReal
  have hfc : Continuous f := by
    have h1 : Continuous fun x : Vec d => reducedCoefficient ω x i₀ i₀ :=
      ((reduce ω).1.continuous.matrix_elem i₀ i₀)
    exact h1.comp hγc
  have hmc : Continuous m := (reduce ω).2.continuous.comp hγc
  have hK : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le one_pos (one_le_sourceReducedBound Q.ellipticity_parameter)
  have hfB : ∀ u, |f u| ≤ sourceReducedBound Λ₀ := fun u =>
    abs_entry_le_of_isRegular hK hω' (γ u.toNNReal) i₀ i₀
  have hTtop : Tendsto T atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp this
  have hTnn : Tendsto (fun n => (T n).toNNReal) atTop atTop :=
    (tendsto_real_toNNReal_atTop).comp hTtop
  have hcoord : Tendsto (fun n => γ (T n).toNNReal i₀ / T n) atTop (𝓝 lam) := by
    have h1 := ((continuous_apply i₀).tendsto vY).comp (hvelγ.comp hTnn)
    rw [hvYi] at h1
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, Real.coe_toNNReal _ (hT n).le]
    ring
  have hclT : Tendsto (fun n => (∫ u in (0 : ℝ)..T n, m u) / T n) atTop (𝓝 η) := by
    refine (hclγ.comp hTnn).congr fun n => ?_
    simp only [Function.comp_apply, Clock.coe_physicalPathClock, Clock.pathClock,
      Real.coe_toNNReal _ (hT n).le, hmdef]
  have hdmpT : Tendsto (fun n => driftMartingalePart b₂ i₀ (T n) (ω, γ) / T n) atTop (𝓝 0) :=
    hXγ.congr fun n => by rw [hvγ n]
  have hobs : ∀ u : ℝ, b₂ (Carriers.reducedObservationAt u.toNNReal (ω, γ)) =
      (m u - 1) / δ + lam * f u := by
    intro u
    show ((translate (γ u.toNNReal) (reduce ω)).2 0 - 1) / δ +
        lam * (translate (γ u.toNNReal) (reduce ω)).1 0 i₀ i₀ = _
    rw [translate_scalar, translate_matrix, add_zero]
    rfl
  have hident : ∀ n, (∫ u in (0 : ℝ)..T n, f u) / T n =
      ((γ (T n).toNNReal i₀ / T n - driftMartingalePart b₂ i₀ (T n) (ω, γ) / T n) -
        ((∫ u in (0 : ℝ)..T n, m u) / T n - 1) / δ) / lam := by
    intro n
    have hTn := (hT n).ne'
    have hint : ∫ u in (0 : ℝ)..T n, b₂ (Carriers.reducedObservationAt u.toNNReal (ω, γ)) =
        ((∫ u in (0 : ℝ)..T n, m u) - T n) / δ + lam * ∫ u in (0 : ℝ)..T n, f u := by
      simp only [hobs]
      rw [intervalIntegral.integral_add
        (((hmc.sub continuous_const).div_const δ).intervalIntegrable _ _)
        ((continuous_const.mul hfc).intervalIntegrable _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_sub (hmc.intervalIntegrable _ _) intervalIntegrable_const,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp
    unfold driftMartingalePart
    rw [hint]
    field_simp
    ring
  have hfT : Tendsto (fun n => (∫ u in (0 : ℝ)..T n, f u) / T n) atTop (𝓝 A) := by
    simp only [hident]
    have h := ((hcoord.sub hdmpT).sub ((hclT.sub_const 1).div_const δ)).div_const lam
    convert h using 2
    rw [hAdef]
    field_simp
    ring
  have hall := tendsto_average_of_tendsto_sq hfc hfB hfT
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b.toNNReal, fun a ha => by
      have := (Real.toNNReal_le_iff_le_coe).mp ha; linarith⟩
  refine (hall.comp hcoe).congr fun t => ?_
  simp only [Function.comp_apply, sharpTimeAverageA11, hfdef]

end EinsteinRelation.Sharpness
