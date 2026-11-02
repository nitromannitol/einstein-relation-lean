import EinsteinFull.Calculus.C16SourceExponentialMax
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.Mobility.VelocityRateFromSteps

/-! Assembly of the exponential integrability of the coordinate maximum of the reduced source
law from the stopped coordinate exponential moments. -/

namespace EinsteinFull
open EinsteinRelation MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

/-- If the path starts inside the ball and reaches norm `R` by time `T`, then the truncated exit
position has norm at least `R`. -/
theorem c16_max_exit_norm_ge {d : ℕ} {R : ℝ} {T : ℝ≥0} {γ : Path d}
    (h0 : euclideanNorm (γ 0) < R) {t : ℝ≥0} (ht : t ≤ T)
    (hR : R ≤ euclideanNorm (γ t)) :
    R ≤ euclideanNorm (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
      {y : Vec d | euclideanNorm y < R} T γ)) := by
  set U : Set (Vec d) := {y : Vec d | euclideanNorm y < R} with hUdef
  have hU : IsOpen U := isOpen_lt
    (EinsteinFull.Calculus.Feller.continuous_euclideanNorm d) continuous_const
  have hnot : γ t ∉ U := fun h => absurd hR (not_le.mpr h)
  have hle : MarkovProcess.ContinuousPath.exitTime U γ ≤ (t : ℝ≥0∞) :=
    MarkovProcess.ContinuousPath.exitTime_le_of_notMem U γ t hnot
  have hleT : MarkovProcess.ContinuousPath.exitTime U γ ≤ (T : ℝ≥0∞) :=
    hle.trans (by exact_mod_cast ht)
  have hfin : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hleT
  have hfr := MarkovProcess.ContinuousPath.coordinate_exitTime_mem_frontier U hU γ h0 hfin
  have heq : MarkovProcess.ContinuousPath.exitTimeTrunc U T γ =
      (MarkovProcess.ContinuousPath.exitTime U γ).toNNReal := by
    have hc := MarkovProcess.ContinuousPath.coe_exitTimeTrunc U T γ
    have hm : min (MarkovProcess.ContinuousPath.exitTimeTop U γ) (T : WithTop ℝ≥0) =
        MarkovProcess.ContinuousPath.exitTime U γ := min_eq_left hleT
    rw [hm] at hc
    have : ((MarkovProcess.ContinuousPath.exitTime U γ).toNNReal : ℝ≥0∞) =
        MarkovProcess.ContinuousPath.exitTime U γ := ENNReal.coe_toNNReal hfin
    exact ENNReal.coe_injective (hc.trans this.symm)
  rw [heq]
  rw [hU.frontier_eq] at hfr
  exact not_lt.mp hfr.2

/-- Some coordinate of a vector of Euclidean norm at least `R` has size at least `R / d`. -/
theorem c16_max_exists_coord_ge {d : ℕ} (hd : 1 ≤ d) {R : ℝ} {y : Vec d}
    (hy : R ≤ euclideanNorm y) : ∃ j : Fin d, R / d ≤ |y j| := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hsum : ∑ _j : Fin d, R / d ≤ ∑ j, |y j| := by
    calc ∑ _j : Fin d, R / d = R := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ euclideanNorm y := hy
      _ ≤ ∑ j, |y j| := euclideanNorm_le_sum_abs y
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨j, hj⟩

/-- A two-sided exponential bound for a quantity of absolute value at least `r`. -/
theorem c16_max_exp_ge {q r u : ℝ} (hq : 0 ≤ q) (hu : r ≤ |u|) :
    Real.exp (q * r) ≤ Real.exp (q * u) + Real.exp ((-q) * u) := by
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h] at hu
    exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hu hq)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)
  · rw [abs_of_nonpos h] at hu
    refine (Real.exp_le_exp.mpr ?_).trans (le_add_of_nonneg_left (Real.exp_pos _).le)
    nlinarith

/-- Pointwise domination of the exit-event indicator by two-sided stopped exponentials. -/
theorem c16_max_indicator_le {d : ℕ} (hd : 1 ≤ d) {x : Vec d} {R q : ℝ} (hq : 0 ≤ q)
    {T : ℝ≥0} {γ : Path d} (h0 : γ 0 = x) (hxR : euclideanNorm x < R)
    {t : ℝ≥0} (ht : t ≤ T) (hR : R ≤ euclideanNorm (γ t)) :
    1 ≤ ∑ j : Fin d, (Real.exp (q * ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} T γ)) j - x j)) +
      Real.exp ((-q) * ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
        {y : Vec d | euclideanNorm y < R} T γ)) j - x j))) *
      Real.exp (-(q * (R / d - euclideanNorm x))) := by
  have hn := c16_max_exit_norm_ge (T := T) (h0 ▸ hxR) ht hR
  obtain ⟨j, hj⟩ := c16_max_exists_coord_ge hd hn
  set y := γ (MarkovProcess.ContinuousPath.exitTimeTrunc
    {y : Vec d | euclideanNorm y < R} T γ) with hy
  have hxj : |x j| ≤ euclideanNorm x := Regeneration.coordinate_abs_le_euclideanNorm x j
  have hu : R / d - euclideanNorm x ≤ |y j - x j| := by
    have := abs_sub_abs_le_abs_sub (y j) (x j)
    linarith
  have h1 := c16_max_exp_ge hq hu
  have hterm : 1 ≤ (Real.exp (q * (y j - x j)) + Real.exp ((-q) * (y j - x j))) *
      Real.exp (-(q * (R / d - euclideanNorm x))) := by
    have hpos := Real.exp_pos (-(q * (R / d - euclideanNorm x)))
    have : Real.exp (q * (R / d - euclideanNorm x)) *
        Real.exp (-(q * (R / d - euclideanNorm x))) = 1 := by
      rw [← Real.exp_add]; simp
    calc (1 : ℝ) = Real.exp (q * (R / d - euclideanNorm x)) *
          Real.exp (-(q * (R / d - euclideanNorm x))) := this.symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hpos.le
  refine hterm.trans ?_
  exact Finset.single_le_sum (f := fun j => (Real.exp (q * (y j - x j)) +
      Real.exp ((-q) * (y j - x j))) * Real.exp (-(q * (R / d - euclideanNorm x))))
    (fun j _ => mul_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      (Real.exp_pos _).le) (Finset.mem_univ j)


/-- Tail bound for an exit event from the two-sided stopped exponential moments. -/
theorem c16_max_tail_aux {d : ℕ} (hd : 1 ≤ d) {x : Vec d} {P : Measure (Path d)}
    [IsProbabilityMeasure P] (hP0 : ∀ᵐ γ ∂P, γ 0 = x) {R q B : ℝ} (hq : 0 ≤ q)
    (hxR : euclideanNorm x < R) {T : ℝ≥0} {E : Set (Path d)} (hE : MeasurableSet E)
    (hEsub : ∀ γ ∈ E, ∃ t : ℝ≥0, t ≤ T ∧ R ≤ euclideanNorm (γ t))
    (hmom : ∀ (j : Fin d) (σ : ℝ), (σ = q ∨ σ = -q) →
      Integrable (fun γ : Path d => Real.exp (σ *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) j - x j))) P ∧
      (∫ γ : Path d, Real.exp (σ *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) j - x j)) ∂P) ≤ B) :
    P.real E ≤ 2 * d * B * Real.exp (-(q * (R / d - euclideanNorm x))) := by
  set c := Real.exp (-(q * (R / d - euclideanNorm x))) with hc
  set Y : Fin d → Path d → ℝ := fun j γ => (γ (MarkovProcess.ContinuousPath.exitTimeTrunc
    {y : Vec d | euclideanNorm y < R} T γ)) j - x j with hY
  have hI1 (j : Fin d) : Integrable (fun γ => Real.exp (q * Y j γ)) P :=
    (hmom j q (Or.inl rfl)).1
  have hI2 (j : Fin d) : Integrable (fun γ => Real.exp ((-q) * Y j γ)) P :=
    (hmom j (-q) (Or.inr rfl)).1
  have hG : Integrable (fun γ => ∑ j : Fin d,
      (Real.exp (q * Y j γ) + Real.exp ((-q) * Y j γ)) * c) P :=
    integrable_finsetSum _ fun j _ => ((hI1 j).add (hI2 j)).mul_const c
  have hind : Integrable (E.indicator (fun _ : Path d => (1 : ℝ))) P :=
    (integrable_const (1 : ℝ)).indicator hE
  have hle : (∫ γ, E.indicator (fun _ : Path d => (1 : ℝ)) γ ∂P) ≤
      ∫ γ, ∑ j : Fin d, (Real.exp (q * Y j γ) + Real.exp ((-q) * Y j γ)) * c ∂P := by
    refine integral_mono_ae hind hG ?_
    filter_upwards [hP0] with γ hγ
    by_cases hmem : γ ∈ E
    · obtain ⟨t, ht, hRt⟩ := hEsub γ hmem
      rw [Set.indicator_of_mem hmem]
      exact c16_max_indicator_le hd hq hγ hxR ht hRt
    · rw [Set.indicator_of_notMem hmem]
      exact Finset.sum_nonneg fun j _ => mul_nonneg
        (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le
  have hint : (∫ γ, ∑ j : Fin d,
      (Real.exp (q * Y j γ) + Real.exp ((-q) * Y j γ)) * c ∂P) ≤ 2 * d * B * c := by
    have hint1 (j : Fin d) : Integrable
        (fun γ => (Real.exp (q * Y j γ) + Real.exp ((-q) * Y j γ)) * c) P :=
      ((hI1 j).add (hI2 j)).mul_const c
    rw [integral_finsetSum _ fun j _ => hint1 j]
    have hj (j : Fin d) : (∫ γ, (Real.exp (q * Y j γ) + Real.exp ((-q) * Y j γ)) * c ∂P) ≤
        2 * B * c := by
      rw [integral_mul_const, integral_add (hI1 j) (hI2 j)]
      have h1 := (hmom j q (Or.inl rfl)).2
      have h2 := (hmom j (-q) (Or.inr rfl)).2
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    calc _ ≤ ∑ _j : Fin d, 2 * B * c := Finset.sum_le_sum fun j _ => hj j
      _ = 2 * d * B * c := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [← integral_indicator_one hE]
  exact hle.trans hint


/-- A nonnegative measurable function with an exponential tail has integrable exponential of
any smaller rate. -/
theorem c16_max_integrable_of_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {S : Ω → ℝ} (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    {K κ a : ℝ} (hK : 0 ≤ K) (ha : 0 < a) (hκ : a < κ)
    (htail : ∀ s : ℝ, 0 ≤ s → P.real {ω | s ≤ S ω} ≤ K * Real.exp (-(κ * s))) :
    Integrable (fun ω => Real.exp (a * S ω)) P := by
  have hmeas : Measurable (fun ω => Real.exp (a * S ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hS)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  have hsets (n : ℕ) : MeasurableSet {ω | (n : ℝ) ≤ S ω} := measurableSet_le measurable_const hS
  have key : ∀ ω, ENNReal.ofReal (Real.exp (a * S ω)) ≤ ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
        {ω | (n : ℝ) ≤ S ω}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    refine le_trans ?_ (ENNReal.le_tsum ⌊S ω⌋₊)
    have hmem : ω ∈ {ω' | ((⌊S ω⌋₊ : ℕ) : ℝ) ≤ S ω'} := Nat.floor_le (hS0 ω)
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (S ω)).le ha.le))
  have hlin : (∫⁻ ω, ENNReal.ofReal (Real.exp (a * S ω)) ∂P) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
        P {ω | (n : ℝ) ≤ S ω} := by
    refine (lintegral_mono key).trans ?_
    rw [lintegral_tsum fun n => ((measurable_one.indicator (hsets n)).const_mul _).aemeasurable]
    refine le_of_eq (tsum_congr fun n => ?_)
    rw [lintegral_const_mul _ (measurable_one.indicator (hsets n)),
      lintegral_indicator_one (hsets n)]
  have hterm (n : ℕ) : ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
      P {ω | (n : ℝ) ≤ S ω} ≤ ENNReal.ofReal ((K * Real.exp a) *
        Real.exp (a - κ) ^ n) := by
    rw [← ofReal_measureReal (measure_ne_top P _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := mul_le_mul_of_nonneg_left (htail n n.cast_nonneg) (Real.exp_pos (a * ((n : ℝ) + 1))).le
    refine h1.trans (le_of_eq ?_)
    calc Real.exp (a * ((n : ℝ) + 1)) * (K * Real.exp (-(κ * n))) =
          K * (Real.exp (a * ((n : ℝ) + 1)) * Real.exp (-(κ * n))) := by ring
      _ = K * (Real.exp a * Real.exp (n * (a - κ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ = _ := by rw [Real.exp_nat_mul]; ring
  have hsum : Summable (fun n : ℕ => (K * Real.exp a) * Real.exp (a - κ) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; linarith)).mul_left _
  calc _ ≤ _ := hlin
    _ ≤ ∑' n : ℕ, ENNReal.ofReal ((K * Real.exp a) * Real.exp (a - κ) ^ n) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℕ, (K * Real.exp a) * Real.exp (a - κ) ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => mul_nonneg (mul_nonneg hK (Real.exp_pos _).le)
            (pow_nonneg (Real.exp_pos _).le n)) hsum).symm
    _ < ⊤ := ENNReal.ofReal_lt_top


/-- The coordinate maximum is attained at some time in the compact interval. -/
theorem c16_max_exists_attain {d : ℕ} (i : Fin d) (x : Vec d) (T : ℝ≥0) (γ : Path d) :
    ∃ t : ℝ≥0, t ≤ T ∧ sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) =
      |(γ t) i - x i| := by
  have hc : Continuous (fun t : ℝ≥0 => |(γ t) i - x i|) :=
    (((continuous_apply i).comp γ.continuous).sub continuous_const).abs
  have hmem := (isCompact_Icc.image hc).sSup_mem
    (Set.Nonempty.image _ (⟨0, le_rfl, bot_le⟩ : (Set.Icc (0 : ℝ≥0) T).Nonempty))
  obtain ⟨t, ht, hteq⟩ := hmem
  exact ⟨t, ht.2, hteq.symm⟩

/-- The coordinate maximum is nonnegative. -/
theorem c16_max_nonneg {d : ℕ} (i : Fin d) (x : Vec d) (T : ℝ≥0) (γ : Path d) :
    0 ≤ sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T) := by
  obtain ⟨t, -, ht⟩ := c16_max_exists_attain i x T γ
  rw [ht]; exact abs_nonneg _

/-- Exponential tail of the coordinate maximum for the reduced source law. -/
theorem c16_max_tail_reduced
    {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ}
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (hΛ : 0 < Λ₀) (i : Fin d)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    {q : ℝ} (hq : 0 ≤ q) (T : ℝ≥0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → P.real {γ : Path d | s ≤
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)} ≤
        K * Real.exp (-(q / d * s)) := by
  have : IsProbabilityMeasure P := hP.1
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hP' (j : Fin d) : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) j 0)) x P := by
    have h : forcedDrift (reducedCoefficient ω) i 0 = forcedDrift (reducedCoefficient ω) j 0 := by
      funext y k; simp [forcedDrift]
    rwa [h] at hP
  have hmo : ∀ (j : Fin d) (σ : ℝ), ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), euclideanNorm x < R →
      ∀ T : ℝ≥0, Integrable (fun γ : Path d => Real.exp (σ *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) j - x j))) P ∧
      (∫ γ : Path d, Real.exp (σ *
        ((γ (MarkovProcess.ContinuousPath.exitTimeTrunc
          {y : Vec d | euclideanNorm y < R} T γ)) j - x j)) ∂P)
        ≤ Real.exp (C * (T : ℝ)) :=
    fun j σ => c16_reduced_textbook_stopped_coordinate_exp_moment hΛ hω j (hP' j) σ
  choose Cf hCf0 hCf using hmo
  set C : ℝ := ∑ j : Fin d, (Cf j q + Cf j (-q)) with hC
  have hCle (j : Fin d) : Cf j q ≤ C ∧ Cf j (-q) ≤ C := by
    have h1 : Cf j q + Cf j (-q) ≤ C := Finset.single_le_sum
      (f := fun j => Cf j q + Cf j (-q)) (fun j _ => add_nonneg (hCf0 j q) (hCf0 j (-q)))
      (Finset.mem_univ j)
    have := hCf0 j q; have := hCf0 j (-q)
    constructor <;> linarith
  have hB (j : Fin d) (σ : ℝ) (hσ : σ = q ∨ σ = -q) : Real.exp (Cf j σ * (T : ℝ)) ≤
      Real.exp (C * (T : ℝ)) := by
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ T.coe_nonneg)
    rcases hσ with rfl | rfl
    · exact (hCle j).1
    · exact (hCle j).2
  set n := euclideanNorm x with hn
  have hn0 : 0 ≤ n := Real.sqrt_nonneg _
  set B := Real.exp (C * (T : ℝ)) with hBdef
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  refine ⟨2 * d * B * Real.exp (q * (n / d + n)) + Real.exp (q / d * (2 * n)), by positivity, ?_⟩
  intro s hs
  have hSm : Measurable (fun γ : Path d =>
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) :=
    (c16_continuous_coordinate_max i x T).measurable
  have hE : MeasurableSet {γ : Path d | s ≤
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)} := measurableSet_le measurable_const hSm
  have hrest : 0 ≤ Real.exp (-(q / d * s)) := (Real.exp_pos _).le
  rcases le_or_gt s (2 * n) with hsn | hsn
  · -- small `s`: trivial bound
    have h1 : P.real {γ : Path d | s ≤
        sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)} ≤ 1 := measureReal_le_one
    have h2 : (1 : ℝ) ≤ Real.exp (q / d * (2 * n)) * Real.exp (-(q / d * s)) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by
        have : 0 ≤ q / d := div_nonneg hq hdpos.le
        nlinarith)
    have h3 : 0 ≤ 2 * d * B * Real.exp (q * (n / d + n)) := by positivity
    nlinarith [mul_nonneg h3 hrest]
  · -- large `s`
    have hR : n < s - n := by linarith
    have hEsub : ∀ γ ∈ {γ : Path d | s ≤
        sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)},
        ∃ t : ℝ≥0, t ≤ T ∧ s - n ≤ euclideanNorm (γ t) := by
      intro γ hγ
      obtain ⟨t, htT, hteq⟩ := c16_max_exists_attain i x T γ
      refine ⟨t, htT, ?_⟩
      have hγ' : s ≤ |(γ t) i - x i| := by rw [← hteq]; exact hγ
      have h1 := abs_sub (γ t i) (x i)
      have h2 : |γ t i| ≤ euclideanNorm (γ t) := Regeneration.coordinate_abs_le_euclideanNorm _ i
      have h3 : |x i| ≤ n := Regeneration.coordinate_abs_le_euclideanNorm _ i
      linarith
    have ht := c16_max_tail_aux hd hP.2.1 hq hR hE hEsub
      (fun j σ hσ => ⟨(hCf j σ (s - n) hR T).1,
        (hCf j σ (s - n) hR T).2.trans (hB j σ hσ)⟩)
    rw [← hn] at ht
    have heq : Real.exp (-(q * ((s - n) / d - n))) =
        Real.exp (q * (n / d + n)) * Real.exp (-(q / d * s)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq, ← mul_assoc] at ht
    exact ht.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.exp_pos _).le) hrest)


/-- The exponential of the absolute coordinate maximum of the reduced source law is integrable
for every real rate. -/
theorem c16_reduced_textbook_exp_coordinate_max_integrable
    {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P) (a : ℝ) (T : ℝ≥0) :
    Integrable (fun γ : Path d => Real.exp (a *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))) P := by
  have : IsProbabilityMeasure P := hP.1
  have hSm : Measurable (fun γ : Path d =>
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) :=
    (c16_continuous_coordinate_max i x T).measurable
  rcases le_or_gt a 0 with ha | ha
  · refine Integrable.mono' (integrable_const (1 : ℝ))
      (Real.measurable_exp.comp (measurable_const.mul hSm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun γ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg ha (c16_max_nonneg i x T γ))
  · have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    obtain ⟨K, hK, htail⟩ := c16_max_tail_reduced hd hω hΛ i hP
      (q := 2 * a * d) (by positivity) T
    have hκ : 2 * a * d / d = 2 * a := by field_simp
    rw [hκ] at htail
    exact c16_max_integrable_of_tail hSm (fun γ => c16_max_nonneg i x T γ) hK ha
      (by linarith) htail

end EinsteinFull
