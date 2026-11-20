import EinsteinFull.External.DFGW.MartingaleMaximal
import EinsteinFull.External.DFGW.DynkinDyadicMaximal

/-! # Doob tail bounds for martingale excursions

Doob's maximal inequality, restricted to the event of a large excursion, bounds the probability
that a martingale exceeds a threshold `a` by `4 / a ^ 2` times the terminal second moment on the
event where the terminal value exceeds `a / 2`. The bound extends by monotone convergence to all
dyadic times of a bounded interval.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

section Discrete

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}

/-- A large discrete martingale excursion is controlled by the terminal second moment on the
event where the terminal value exceeds half the threshold. -/
theorem measureReal_martingale_max_le_tail (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (n : ℕ) (hM2 : MemLp (M n) 2 P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ k ≤ n, a ≤ |M k ω|} ≤
      4 / a ^ 2 * ∫ ω in {ω | a / 2 ≤ |M n ω|}, (M n ω) ^ 2 ∂P := by
  let B : ℕ → Ω → ℝ := fun k ω => |M k ω|
  have hB : Submartingale B ℱ P := by
    have h := hM.submartingale.sup hM.neg.submartingale
    convert h using 1
    ext k ω
    simp [B, abs_eq_max_neg]
  have hBnonneg : 0 ≤ B := fun _ _ => abs_nonneg _
  let q : ℝ≥0 := ⟨a, ha.le⟩
  let A : Set Ω := {ω | (q : ℝ) ≤
    (Finset.range (n + 1)).sup' (Finset.nonempty_range_add_one) (fun k => B k ω)}
  have hA : A = {ω | ∃ k ≤ n, a ≤ |M k ω|} := by
    ext ω
    simp only [A, B, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, q]
    rfl
  have hmax := maximal_ineq hB hBnonneg (ε := q) n
  have hMn : Measurable (M n) := ((hM.stronglyMeasurable n).mono (ℱ.le n)).measurable
  let C : Set Ω := {ω | a / 2 ≤ |M n ω|}
  have hC : MeasurableSet C := measurableSet_le measurable_const (continuous_abs.measurable.comp hMn)
  have hsq : Integrable (fun ω => M n ω ^ 2) P := hM2.integrable_sq
  have hind : Integrable (C.indicator fun ω => M n ω ^ 2) P := hsq.indicator hC
  have hpt : ∀ ω, |M n ω| ≤ a / 2 + 2 / a * C.indicator (fun ω => M n ω ^ 2) ω := by
    intro ω
    by_cases hω : ω ∈ C
    · rw [Set.indicator_of_mem hω]
      have h1 : a / 2 ≤ |M n ω| := hω
      have h2 : |M n ω| * a ≤ |M n ω| * (2 * |M n ω|) :=
        mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      have h3 : |M n ω| ≤ 2 / a * M n ω ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ ha]
        nlinarith [sq_abs (M n ω)]
      have h4 : 0 ≤ a / 2 := by positivity
      linarith
    · rw [Set.indicator_of_notMem hω]
      have h1 : |M n ω| < a / 2 := lt_of_not_ge hω
      linarith
  have hMint : Integrable (fun ω => |M n ω|) P := (hM2.integrable one_le_two).abs
  have hleft : a * P.real A ≤ ∫ ω in A, |M n ω| ∂P := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmax
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal
      (integral_nonneg fun ω => abs_nonneg _)] at ht
    exact ht
  have hright : (∫ ω in A, |M n ω| ∂P) ≤
      a / 2 * P.real A + 2 / a * ∫ ω in C, M n ω ^ 2 ∂P := by
    have hmono : (∫ ω in A, |M n ω| ∂P) ≤
        ∫ ω in A, (a / 2 + 2 / a * C.indicator (fun ω => M n ω ^ 2) ω) ∂P :=
      setIntegral_mono hMint.integrableOn
        ((integrable_const _).add (hind.const_mul _)).integrableOn hpt
    have hsplit : (∫ ω in A, (a / 2 + 2 / a * C.indicator (fun ω => M n ω ^ 2) ω) ∂P) =
        a / 2 * P.real A + 2 / a * ∫ ω in A, C.indicator (fun ω => M n ω ^ 2) ω ∂P := by
      rw [integral_add (integrable_const _).integrableOn (hind.const_mul _).integrableOn,
        setIntegral_const, integral_const_mul, smul_eq_mul, mul_comm (P.real A)]
    have hsub : (∫ ω in A, C.indicator (fun ω => M n ω ^ 2) ω ∂P) ≤
        ∫ ω in C, M n ω ^ 2 ∂P := by
      rw [← integral_indicator hC]
      exact setIntegral_le_integral hind (ae_of_all _ fun ω =>
        Set.indicator_nonneg (fun ω _ => sq_nonneg (M n ω)) ω)
    have h2a : 0 ≤ 2 / a := by positivity
    rw [hsplit] at hmono
    nlinarith
  have key : a / 2 * P.real A ≤ 2 / a * ∫ ω in C, M n ω ^ 2 ∂P := by linarith
  have hfinal : P.real A ≤ 4 / a ^ 2 * ∫ ω in C, M n ω ^ 2 ∂P := by
    calc
      P.real A = 2 / a * (a / 2 * P.real A) := by field_simp
      _ ≤ 2 / a * (2 / a * ∫ ω in C, M n ω ^ 2 ∂P) := by gcongr
      _ = 4 / a ^ 2 * ∫ ω in C, M n ω ^ 2 ∂P := by ring
  rw [hA] at hfinal
  exact hfinal

end Discrete

section Dyadic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}

/-- A large excursion of a continuous-time martingale over all dyadic times of `[0, t]` is
controlled by the terminal second moment on the event where the terminal value exceeds half the
threshold. -/
theorem measureReal_dyadic_martingale_max_le_tail (M : ℝ≥0 → Ω → ℝ) (hM : Martingale M ℱ P)
    (t : ℝ≥0) (hM2 : MemLp (M t) 2 P) {a : ℝ} (ha : 0 < a) :
    P.real {ω | ∃ r k, k ≤ 2 ^ r ∧ a ≤ |M (dyadicGridTime t r k) ω|} ≤
      4 / a ^ 2 * ∫ ω in {ω | a / 2 ≤ |M t ω|}, (M t ω) ^ 2 ∂P := by
  let A : ℕ → Set Ω := fun r => {ω | ∃ k ≤ 2 ^ r, a ≤ |M (dyadicGridTime t r k) ω|}
  have hgrid (r : ℕ) : P.real (A r) ≤
      4 / a ^ 2 * ∫ ω in {ω | a / 2 ≤ |M t ω|}, (M t ω) ^ 2 ∂P := by
    let u : ℝ≥0 := t / ((2 ^ r : ℕ) : ℝ≥0)
    let F : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
      { seq := fun k => ℱ (k • u)
        mono' := fun _ _ h => ℱ.mono (nsmul_le_nsmul_left (show 0 ≤ u from bot_le) h)
        le' := fun k => ℱ.le (k • u) }
    let X : ℕ → Ω → ℝ := fun k ω => M (k • u) ω
    have hX : Martingale X F P := by
      constructor
      · intro k
        exact hM.stronglyMeasurable (k • u)
      · intro k l hkl
        exact hM.condExp_ae_eq (nsmul_le_nsmul_left (show 0 ≤ u from bot_le) hkl)
    have hlast : (2 ^ r : ℕ) • u = t := dyadicGridTime_last t r
    have hX2 : MemLp (X (2 ^ r)) 2 P := by
      change MemLp (M ((2 ^ r : ℕ) • u)) 2 P
      rw [hlast]
      exact hM2
    have h := measureReal_martingale_max_le_tail X hX (2 ^ r) hX2 ha
    change P.real {ω | ∃ k ≤ 2 ^ r, a ≤ |M (dyadicGridTime t r k) ω|} ≤ _
    simpa only [X, u, dyadicGridTime, hlast] using h
  have hmono : Monotone A := by
    apply monotone_nat_of_le_succ
    intro r ω hω
    obtain ⟨k, hk, hval⟩ := hω
    refine ⟨2 * k, by rw [pow_succ]; omega, ?_⟩
    rwa [dyadicGridTime_succ]
  have hU : {ω | ∃ r k, k ≤ 2 ^ r ∧ a ≤ |M (dyadicGridTime t r k) ω|} = ⋃ r, A r := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, A]
  have hlim := tendsto_measure_iUnion_atTop (μ := P) hmono
  have hreal : Tendsto (fun r => P.real (A r)) atTop (𝓝 (P.real (⋃ r, A r))) :=
    (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hlim
  rw [hU]
  exact le_of_tendsto' hreal hgrid

end Dyadic

end EinsteinFull.External.DFGW
