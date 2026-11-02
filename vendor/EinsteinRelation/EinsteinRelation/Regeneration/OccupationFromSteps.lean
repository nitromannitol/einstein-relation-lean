import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Density.LaplaceDensityExistence
import EinsteinRelation.Density.LaplaceDensityIntegral
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ProbabilityPart
import EinsteinRelation.Probability.ValidAnnealedLawSupport
import EinsteinRelation.Regeneration.LaplaceOccupationTransfer
import EinsteinRelation.Regeneration.Measurability
import EinsteinRelation.Regeneration.OccupationRegenerationSum
import EinsteinRelation.Regeneration.RenewalCarriers
import EinsteinRelation.Regeneration.TrialBounds

/-!
# Proposition 3.2 from its two regeneration steps

Proposition 3.2 (`regen.occupation`, `paper/main.tex` lines 439–501) bounds the occupation of
the environment seen from the particle, in time and under the exponential-time density `ρ_s`.
Its proof has three steps (lines 471–496):

* Step 1 (`regen.first-reward`): the coupled expected occupation of the first regeneration
  interval `[0, τ₁)` is at most `C Δ ‖G‖_{L^p(Q)}`, with `Δ = λ⁻²`. This is `FirstRewardStep`.
* Step 2: for every `k ≥ 1` the coupled expected occupation of `[τ_k, τ_{k+1})` is at most
  `C Δ ‖G‖_{L^p(Q)}`. This is `LaterIntervalsStep`.
* Step 3: the pathwise bound `τ_k ≥ 2kΔ` covers `[0, T]` by the intervals with index at most
  `⌊T/(2Δ)⌋₊`, which gives the factor `T/(2Δ) + 1`.

The resolvent bound follows from the time bound by the Laplace transfer of
`LaplaceOccupationTransfer`. The steps are stated on the coupled annealed law
`Regeneration.annealedCoupledLaw`; the physical law of Proposition 3.2 is its path marginal.

Regeneration times may be infinite. Intervals are therefore described by their `ℝ≥0∞`
endpoints, so no almost-sure finiteness of the times is needed.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace EinsteinRelation

/-! ## Regeneration intervals with extended endpoints -/

/-- The real times `t ≥ 0` with `a ≤ ofReal t < b`, the interval `[a, b)` of the integrals
`∫_{τ_k}^{τ_{k+1}}` in Proposition 3.2. The endpoints lie in `ℝ≥0∞`, so `τ_{k+1} = ∞` is
allowed. -/
def regenInterval (a b : ℝ≥0∞) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ a ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < b}

theorem mem_regenInterval {a b : ℝ≥0∞} {t : ℝ} :
    t ∈ regenInterval a b ↔ 0 ≤ t ∧ a ≤ ENNReal.ofReal t ∧ ENNReal.ofReal t < b :=
  Iff.rfl

theorem measurableSet_regenInterval (a b : ℝ≥0∞) : MeasurableSet (regenInterval a b) := by
  have h0 : MeasurableSet {t : ℝ | 0 ≤ t} := measurableSet_le measurable_const measurable_id
  have h1 : MeasurableSet {t : ℝ | a ≤ ENNReal.ofReal t} :=
    measurableSet_le measurable_const ENNReal.measurable_ofReal
  have h2 : MeasurableSet {t : ℝ | ENNReal.ofReal t < b} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have h : regenInterval a b = {t : ℝ | 0 ≤ t} ∩
      ({t : ℝ | a ≤ ENNReal.ofReal t} ∩ {t : ℝ | ENNReal.ofReal t < b}) :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  exact h0.inter (h1.inter h2)

/-- Covering of `[0, T]` by the intervals `[τ k, τ (k+1))` with `k ≤ ⌊T/(2Δ)⌋₊`, from the
lower bounds `ofReal (2kΔ) ≤ τ k`. For `t ∈ [0, T]`, the index is the least `n` with
`ofReal t < τ n`, minus one. -/
theorem regenInterval_cover (τ : ℕ → ℝ≥0∞) (hτ0 : τ 0 = 0) (Δ : ℝ) (hΔ : 0 < Δ)
    (hlow : ∀ k : ℕ, ENNReal.ofReal (2 * (k : ℝ) * Δ) ≤ τ k) (T : ℝ) :
    Set.Icc 0 T ⊆ ⋃ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1), regenInterval (τ k) (τ (k + 1)) := by
  classical
  intro t ht
  obtain ⟨ht0, htT⟩ := ht
  have h2Δ : 0 < 2 * Δ := by linarith
  have hfloor : T / (2 * Δ) < (⌊T / (2 * Δ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkey : T / (2 * Δ) * (2 * Δ) = T := div_mul_cancel₀ T h2Δ.ne'
  have hT1 : T < ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * (2 * Δ) := by
    have h5 := mul_lt_mul_of_pos_right hfloor h2Δ
    rw [hkey] at h5
    exact h5
  have hT2 : T < 2 * ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * Δ := by
    calc T < ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * (2 * Δ) := hT1
      _ = 2 * ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * Δ := by ring
  have hN : (0 : ℝ) < (⌊T / (2 * Δ)⌋₊ : ℝ) + 1 := by positivity
  have hpos : 0 < 2 * ((⌊T / (2 * Δ)⌋₊ : ℝ) + 1) * Δ :=
    mul_pos (mul_pos two_pos hN) hΔ
  have hcast : ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ) = (⌊T / (2 * Δ)⌋₊ : ℝ) + 1 := Nat.cast_succ _
  have hlow' := hlow (⌊T / (2 * Δ)⌋₊ + 1)
  rw [hcast] at hlow'
  have hlast : ENNReal.ofReal t < τ (⌊T / (2 * Δ)⌋₊ + 1) :=
    lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htT)
      (lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hpos).2 hT2) hlow')
  have hex : ∃ n : ℕ, ENNReal.ofReal t < τ n := ⟨⌊T / (2 * Δ)⌋₊ + 1, hlast⟩
  have hspec : ENNReal.ofReal t < τ (Nat.find hex) := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, hτ0] at hspec
    exact ENNReal.not_lt_zero hspec
  have hle : Nat.find hex ≤ ⌊T / (2 * Δ)⌋₊ + 1 := Nat.find_min' hex hlast
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hmin : ¬ ENNReal.ofReal t < τ m := Nat.find_min hex (by omega)
  have hτm : τ m ≤ ENNReal.ofReal t := not_lt.1 hmin
  have hlt : ENNReal.ofReal t < τ (m + 1) := by
    rw [← hm]
    exact hspec
  have hmN : m < ⌊T / (2 * Δ)⌋₊ + 1 := by omega
  exact Set.mem_iUnion₂.2 ⟨m, Finset.mem_range.2 hmN, mem_regenInterval.2 ⟨ht0, hτm, hlt⟩⟩

/-- Step 3 for a fixed path: the integral over `[0, T]` is at most the sum of the integrals over
the regeneration intervals with index at most `⌊T/(2Δ)⌋₊`. -/
theorem lintegral_regenInterval_cover_le (g : ℝ → ℝ≥0∞) (τ : ℕ → ℝ≥0∞) (hτ0 : τ 0 = 0)
    (Δ : ℝ) (hΔ : 0 < Δ) (hlow : ∀ k : ℕ, ENNReal.ofReal (2 * (k : ℝ) * Δ) ≤ τ k) (T : ℝ) :
    (∫⁻ t in Set.Icc 0 T, g t) ≤
      ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1), ∫⁻ t in regenInterval (τ k) (τ (k + 1)), g t :=
  (lintegral_mono_set (regenInterval_cover τ hτ0 Δ hΔ hlow T)).trans
    (lintegral_biUnion_range_le g (fun k => regenInterval (τ k) (τ (k + 1)))
      (Finset.range (⌊T / (2 * Δ)⌋₊ + 1)))

/-- The joint set `{(ω, t) : 0 ≤ t, a ω ≤ ofReal t < b ω}`. -/
def regenIntervalSet {Ω : Type*} (a b : Ω → ℝ≥0∞) : Set (Ω × ℝ) :=
  {p | 0 ≤ p.2 ∧ a p.1 ≤ ENNReal.ofReal p.2 ∧ ENNReal.ofReal p.2 < b p.1}

theorem measurableSet_regenIntervalSet {Ω : Type*} [MeasurableSpace Ω] (a b : Ω → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b) : MeasurableSet (regenIntervalSet a b) := by
  have h : regenIntervalSet a b = {p : Ω × ℝ | 0 ≤ p.2} ∩
      ({p : Ω × ℝ | a p.1 ≤ ENNReal.ofReal p.2} ∩ {p : Ω × ℝ | ENNReal.ofReal p.2 < b p.1}) :=
    Set.ext fun _ => Iff.rfl
  rw [h]
  have h0 : MeasurableSet {p : Ω × ℝ | 0 ≤ p.2} :=
    measurableSet_le measurable_const measurable_snd
  have h1 : MeasurableSet {p : Ω × ℝ | a p.1 ≤ ENNReal.ofReal p.2} :=
    measurableSet_le (ha.comp measurable_fst) (ENNReal.measurable_ofReal.comp measurable_snd)
  have h2 : MeasurableSet {p : Ω × ℝ | ENNReal.ofReal p.2 < b p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hb.comp measurable_fst)
  exact h0.inter (h1.inter h2)

/-- Measurability in `ω` of the integral over the random regeneration interval. -/
theorem measurable_lintegral_regenInterval {Ω : Type*} [MeasurableSpace Ω]
    (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2) (a b : Ω → ℝ≥0∞)
    (ha : Measurable a) (hb : Measurable b) :
    Measurable fun ω => ∫⁻ t in regenInterval (a ω) (b ω), g ω t := by
  have hS : MeasurableSet (regenIntervalSet a b) := measurableSet_regenIntervalSet a b ha hb
  have hind : Measurable ((regenIntervalSet a b).indicator fun p : Ω × ℝ => g p.1 p.2) :=
    hg.indicator hS
  have hEq : ∀ ω : Ω, (∫⁻ t in regenInterval (a ω) (b ω), g ω t) =
      ∫⁻ t, (regenIntervalSet a b).indicator (fun p : Ω × ℝ => g p.1 p.2) (ω, t) := by
    intro ω
    have hint : (∫⁻ t in regenInterval (a ω) (b ω), g ω t) =
        ∫⁻ t, (regenInterval (a ω) (b ω)).indicator (g ω) t :=
      (lintegral_indicator (measurableSet_regenInterval (a ω) (b ω)) (g ω)).symm
    rw [hint]
    refine lintegral_congr fun t => ?_
    by_cases h : t ∈ regenInterval (a ω) (b ω)
    · have h' : (ω, t) ∈ regenIntervalSet a b := h
      rw [Set.indicator_of_mem h, Set.indicator_of_mem h']
    · have h' : (ω, t) ∉ regenIntervalSet a b := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h']
  have hfeq : (fun ω => ∫⁻ t in regenInterval (a ω) (b ω), g ω t) = fun ω =>
      ∫⁻ t, (regenIntervalSet a b).indicator (fun p : Ω × ℝ => g p.1 p.2) (ω, t) :=
    funext hEq
  rw [hfeq]
  exact hind.lintegral_prod_right'

/-- Step 3 in expectation. If every regeneration interval has expected integral at most `M`,
then the expected integral over `[0, T]` is at most `ofReal (T/(2Δ) + 1) * M`. -/
theorem lintegral_regenerationSum_le {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    (g : Ω → ℝ → ℝ≥0∞) (hg : Measurable fun p : Ω × ℝ => g p.1 p.2)
    (Δ : ℝ) (hΔ : 0 < Δ) (τ : ℕ → Ω → ℝ≥0∞) (hτ : ∀ k : ℕ, Measurable (τ k))
    (hτ0 : ∀ ω, τ 0 ω = 0) (hlow : ∀ (ω : Ω) (k : ℕ), ENNReal.ofReal (2 * (k : ℝ) * Δ) ≤ τ k ω)
    (M : ℝ≥0∞) (hM : ∀ k : ℕ, (∫⁻ ω, (∫⁻ t in regenInterval (τ k ω) (τ (k + 1) ω), g ω t) ∂P) ≤ M)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, g ω t) ∂P) ≤ ENNReal.ofReal (T / (2 * Δ) + 1) * M := by
  have hmeas : ∀ k : ℕ, Measurable fun ω => ∫⁻ t in regenInterval (τ k ω) (τ (k + 1) ω), g ω t :=
    fun k => measurable_lintegral_regenInterval g hg (τ k) (τ (k + 1)) (hτ k) (hτ (k + 1))
  calc (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, g ω t) ∂P)
      ≤ ∫⁻ ω, ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1),
          (∫⁻ t in regenInterval (τ k ω) (τ (k + 1) ω), g ω t) ∂P :=
        lintegral_mono fun ω =>
          lintegral_regenInterval_cover_le (g ω) (fun k => τ k ω) (hτ0 ω) Δ hΔ (hlow ω) T
    _ = ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1),
          ∫⁻ ω, (∫⁻ t in regenInterval (τ k ω) (τ (k + 1) ω), g ω t) ∂P :=
        lintegral_finset_sum _ fun k _ => hmeas k
    _ ≤ ∑ k ∈ Finset.range (⌊T / (2 * Δ)⌋₊ + 1), M := Finset.sum_le_sum fun k _ => hM k
    _ = ((⌊T / (2 * Δ)⌋₊ + 1 : ℕ) : ℝ≥0∞) * M := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (T / (2 * Δ) + 1) * M :=
        mul_le_mul_of_nonneg_right (card_floor_succ_le_ofReal Δ hΔ T hT) zero_le

/-! ## Real arithmetic and the Laplace step -/

/-- The regeneration spacing as a product: `ofReal (2kΔ) = k · (2Δ)` in `ℝ≥0∞`. -/
theorem ofReal_two_mul_natCast_mul (Δ : ℝ≥0) (k : ℕ) :
    ENNReal.ofReal (2 * (k : ℝ) * (Δ : ℝ)) = (k : ℝ≥0∞) * (2 * (Δ : ℝ≥0∞)) := by
  rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * (k : ℝ) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
  ring

/-- The constant bookkeeping of Step 3: `(T/(2Δ) + 1) · C Δ ≤ C (T + Δ)` for `C ≥ 0`. -/
theorem ofReal_occupation_factor (C Δ T : ℝ) (hC : 0 ≤ C) (hΔ : 0 < Δ) (hT : 0 ≤ T)
    (E : ℝ≥0∞) :
    ENNReal.ofReal (T / (2 * Δ) + 1) * (ENNReal.ofReal (C * Δ) * E) ≤
      ENNReal.ofReal (C * (T + Δ)) * E := by
  have hx : 0 ≤ T / (2 * Δ) + 1 := by
    have := div_nonneg hT (by linarith : (0 : ℝ) ≤ 2 * Δ)
    linarith
  rw [← mul_assoc, ← ENNReal.ofReal_mul hx]
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  have hfrac : T / (2 * Δ) * Δ = T / 2 := by
    rw [div_mul_eq_mul_div, div_eq_div_iff (mul_ne_zero two_ne_zero hΔ.ne') two_ne_zero]
    ring
  have hexp : (T / (2 * Δ) + 1) * (C * Δ) = C * (T / 2) + C * Δ := by
    calc (T / (2 * Δ) + 1) * (C * Δ) = C * (T / (2 * Δ) * Δ) + C * Δ := by ring
      _ = C * (T / 2) + C * Δ := by rw [hfrac]
  have hCT : C * (T / 2) ≤ C * T := mul_le_mul_of_nonneg_left (by linarith) hC
  have hsum : C * (T + Δ) = C * T + C * Δ := by ring
  rw [hexp, hsum]
  linarith

/-- The absolute value of a measurable real function is measurable. -/
theorem measurable_abs_real : Measurable fun a : ℝ => |a| :=
  _root_.continuous_abs.measurable

/-- The observed integrand `(t, z) ↦ ofReal |G(ω_t)|` is jointly measurable. -/
theorem measurable_observation_abs {d : ℕ} (G : FieldPair d → ℝ) (hG : Measurable G) :
    Measurable fun z : ℝ × (FieldPair d × Path d) =>
      ENNReal.ofReal |G (Carriers.reducedObservationAt z.1.toNNReal z.2)| :=
  ENNReal.measurable_ofReal.comp
    ((measurable_abs_real.comp hG).comp (laplaceDensity_measurable_observation (d := d)))

/-- The occupation integral `z ↦ ∫_{[0,T]} ofReal |G(ω_t)| dt` is measurable. -/
theorem measurable_occupation_integral {d : ℕ} (G : FieldPair d → ℝ) (hG : Measurable G)
    (T : ℝ) :
    Measurable fun z : FieldPair d × Path d =>
      ∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)| := by
  have hsw : Measurable fun p : (FieldPair d × Path d) × ℝ => (p.2, p.1) :=
    measurable_snd.prodMk measurable_fst
  have hcomp := (measurable_observation_abs G hG).comp hsw
  have hswap : Measurable fun p : (FieldPair d × Path d) × ℝ =>
      ENNReal.ofReal |G (Carriers.reducedObservationAt p.2.toNNReal p.1)| := hcomp
  exact hswap.lintegral_prod_right'

/-- Exchange of the time and environment integrals for the observed occupation. -/
theorem lintegral_occupation_swap {d : ℕ} (G : FieldPair d → ℝ) (hG : Measurable G)
    (μ : MeasureTheory.Measure (FieldPair d × Path d)) [IsFiniteMeasure μ] (T : ℝ) :
    (∫⁻ t in Set.Icc (0 : ℝ) T, (∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)| ∂μ))
      = ∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|) ∂μ :=
  lintegral_lintegral_swap
    (f := fun (t : ℝ) (z : FieldPair d × Path d) =>
      ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
    (measurable_observation_abs G hG).aemeasurable

/-- The exponential-time integral as a Lebesgue integral over `[0, ∞)` against the density
`r e^{-rℓ}`, for a measurable nonnegative integrand. -/
theorem lintegral_expMeasure_eq_Ici (r : ℝ) (H : ℝ → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ℓ, H ℓ ∂(ProbabilityTheory.expMeasure r)) =
      ∫⁻ ℓ in Set.Ici (0 : ℝ), ENNReal.ofReal (r * Real.exp (-r * ℓ)) * H ℓ := by
  have hexp : ProbabilityTheory.expMeasure r =
      (volume : Measure ℝ).withDensity (ProbabilityTheory.exponentialPDF r) := rfl
  have hpdf : Measurable (ProbabilityTheory.exponentialPDF r) :=
    ENNReal.measurable_ofReal.comp (ProbabilityTheory.measurable_exponentialPDFReal r)
  rw [hexp, lintegral_withDensity_eq_lintegral_mul _ hpdf hH,
    ← lintegral_indicator (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))]
  refine lintegral_congr fun ℓ => ?_
  show ProbabilityTheory.exponentialPDF r ℓ * H ℓ =
    (Set.Ici (0 : ℝ)).indicator (fun ℓ => ENNReal.ofReal (r * Real.exp (-r * ℓ)) * H ℓ) ℓ
  by_cases h : 0 ≤ ℓ
  · have hmem : ℓ ∈ Set.Ici (0 : ℝ) := Set.mem_Ici.2 h
    rw [Set.indicator_of_mem hmem, ProbabilityTheory.exponentialPDF_of_nonneg h]
    simp only [neg_mul]
  · have hnot : ℓ ∉ Set.Ici (0 : ℝ) := fun hm => h (Set.mem_Ici.1 hm)
    rw [Set.indicator_of_notMem hnot, ProbabilityTheory.exponentialPDF_of_neg (not_le.1 h),
      zero_mul]

/-- The reduced Laplace-density identity at the level of lower integrals: the density-weighted
integral of `|G|` equals the exponential-time integral of the fixed-time occupation. -/
theorem lintegral_mul_density_eq_laplace {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hP0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q P hP0 s rho)
    (G : FieldPair d → ℝ) (hG : Measurable G) :
    (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(Measure.map reduce Q)) =
      ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (s.1 * Real.exp (-s.1 * t)) *
        (∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|
          ∂(Carriers.annealedCoordinateJoint Q P hP0)) := by
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P hP0
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure s.2
  obtain ⟨hρ, -, hlaw⟩ := hrho
  have hm : Measurable fun w => ENNReal.ofReal (rho w) := ENNReal.measurable_ofReal.comp hρ
  have hGm : Measurable fun w => ENNReal.ofReal |G w| :=
    ENNReal.measurable_ofReal.comp (measurable_abs_real.comp hG)
  have hH : Measurable fun z : ℝ × (FieldPair d × Path d) =>
      ENNReal.ofReal |G (Carriers.reducedObservationAt z.1.toNNReal z.2)| :=
    measurable_observation_abs G hG
  have hLint : Measurable fun ℓ : ℝ => ∫⁻ y, ENNReal.ofReal |G (Carriers.reducedObservationAt ℓ.toNNReal y)|
      ∂(Carriers.annealedCoordinateJoint Q P hP0) :=
    hH.lintegral_prod_right'
  calc (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(Measure.map reduce Q))
      = ∫⁻ w, ENNReal.ofReal |G w| ∂((Measure.map reduce Q).withDensity
          fun w => ENNReal.ofReal (rho w)) :=
        (lintegral_withDensity_eq_lintegral_mul _ hm hGm).symm
    _ = ∫⁻ w, ENNReal.ofReal |G w| ∂(Carriers.reducedLaplaceObservedLaw Q P hP0 s) := by
        rw [hlaw]
    _ = ∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt z.1.toNNReal z.2)|
          ∂((ProbabilityTheory.expMeasure s.1).prod (Carriers.annealedCoordinateJoint Q P hP0)) := by
        unfold Carriers.reducedLaplaceObservedLaw
        exact lintegral_map hGm laplaceDensity_measurable_observation
    _ = ∫⁻ ℓ, (∫⁻ y, ENNReal.ofReal |G (Carriers.reducedObservationAt ℓ.toNNReal y)|
          ∂(Carriers.annealedCoordinateJoint Q P hP0)) ∂(ProbabilityTheory.expMeasure s.1) :=
        lintegral_prod (fun z : ℝ × (FieldPair d × Path d) =>
          ENNReal.ofReal |G (Carriers.reducedObservationAt z.1.toNNReal z.2)|) hH.aemeasurable
    _ = ∫⁻ t in Set.Ici (0 : ℝ), ENNReal.ofReal (s.1 * Real.exp (-s.1 * t)) *
          (∫⁻ y, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal y)|
            ∂(Carriers.annealedCoordinateJoint Q P hP0)) :=
        lintegral_expMeasure_eq_Ici s.1
          (fun ℓ : ℝ => ∫⁻ y, ENNReal.ofReal |G (Carriers.reducedObservationAt ℓ.toNNReal y)|
            ∂(Carriers.annealedCoordinateJoint Q P hP0)) hLint

/-! ## The coupled law and the physical law -/

/-- The coupled annealed law has the physical path-and-environment law as its marginal. The
origin fibres of the coupled kernel are probability measures whose path marginal is the origin
law `P`, `Q`-almost surely. -/
theorem lintegral_annealedCoupledLaw_path {d : ℕ} (Q : MeasureTheory.Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : Regeneration.CoupledQuenchedLaws d) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω))
    (hmarg : ∀ᵐ ω ∂Q, Measure.map Prod.fst (Regeneration.originCoupledLaw K ω) = originLaw P ω)
    (hP0 : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    (F : FieldPair d × Path d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ωz, F (ωz.1, ωz.2.1) ∂(Regeneration.annealedCoupledLaw Q K) =
      ∫⁻ ωγ, F ωγ ∂(Carriers.annealedCoordinateJoint Q P hP0) := by
  have hpath : Measurable fun p : FieldPair d × Regeneration.CoupledSample d => (p.1, p.2.1) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hF' : Measurable fun p : FieldPair d × Regeneration.CoupledSample d => F (p.1, p.2.1) :=
    hF.comp hpath
  have hfst : Measurable (Prod.fst : Regeneration.CoupledSample d → Path d) := measurable_fst
  calc ∫⁻ ωz, F (ωz.1, ωz.2.1) ∂(Regeneration.annealedCoupledLaw Q K)
      = ∫⁻ a, (∫⁻ b, F (a, b.1)
          ∂(Probability.probabilityPart (Regeneration.originCoupledLaw K) a)) ∂Q := by
        unfold Regeneration.annealedCoupledLaw
        exact MeasureTheory.Measure.lintegral_compProd hF'
    _ = ∫⁻ a, (∫⁻ γ, F (a, γ) ∂(originLaw P a)) ∂Q := by
        refine lintegral_congr_ae ?_
        filter_upwards [Probability.probabilityPart_ae_eq Q (Regeneration.originCoupledLaw K) hprob,
          hmarg] with a ha hma
        have hFa : Measurable fun γ : Path d => F (a, γ) :=
          hF.comp (measurable_const.prodMk measurable_id)
        show (∫⁻ b, F (a, b.1) ∂(Probability.probabilityPart (Regeneration.originCoupledLaw K) a)) =
          ∫⁻ γ, F (a, γ) ∂(originLaw P a)
        rw [ha, ← hma, lintegral_map hFa hfst]
    _ = ∫⁻ ωγ, F ωγ ∂(Carriers.annealedCoordinateJoint Q P hP0) :=
        (Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral Q
          (originLaw P) hP0 F hF).symm

/-! ## The two step inequalities -/

/-- Step 1 of Proposition 3.2 (`regen.first-reward`, `paper/main.tex` lines 471–474): the
coupled expected occupation of the first regeneration interval `[0, τ₁)` under the coupled law
is at most `C Δ ‖G‖_{L^p(Q)}`, with `Δ = λ⁻²`. -/
def FirstRewardStep {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l p C : ℝ) (K : Regeneration.CoupledQuenchedLaws d) (G : FieldPair d → ℝ) : Prop :=
  (∫⁻ ωz, (∫⁻ t in regenInterval 0
      (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) 1),
      ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
      ∂(Regeneration.annealedCoupledLaw Q.measure K)) ≤
    ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
      eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)

/-- Step 2 of Proposition 3.2 (paper/main.tex lines 477–490): for every `k ≥ 1`, the coupled
expected occupation of the later regeneration interval `[τ_k, τ_{k+1})` is at most
`C Δ ‖G‖_{L^p(Q)}`. -/
def LaterIntervalsStep {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l p C : ℝ) (K : Regeneration.CoupledQuenchedLaws d) (G : FieldPair d → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k →
    (∫⁻ ωz, (∫⁻ t in regenInterval
        (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
          (Regeneration.Renewal.forceCoord hd) k)
        (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
          (Regeneration.Renewal.forceCoord hd) (k + 1)),
        ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
        ∂(Regeneration.annealedCoupledLaw Q.measure K)) ≤
      ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
        eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)

/-! ## Coupled regeneration times and the step bounds -/

/-- The regeneration times vanish at index zero, pathwise. -/
theorem regenerationTime_zero_eq {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (z : Regeneration.CoupledSample d)
    (i : Fin d) : Regeneration.regenerationTime Δ lam R z i 0 = 0 :=
  rfl

/-- Each coupled regeneration time is measurable in the environment-path pair. -/
theorem measurable_coupledRegenerationTime {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (k : ℕ) :
    Measurable fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) k := by
  have hsnd : Measurable fun ωz : FieldPair d × Regeneration.CoupledSample d => ωz.2 :=
    measurable_snd
  have hcomp := (Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam)
    lam (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp hsnd
  exact hcomp

/-- The observed integrand along the coupled sample, jointly in the time and the sample. -/
theorem measurable_coupledObservation {d : ℕ} (G : FieldPair d → ℝ) (hG : Measurable G) :
    Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ =>
      ENNReal.ofReal |G (Carriers.reducedObservationAt p.2.toNNReal (p.1.1, p.1.2.1))| := by
  have hmap : Measurable fun p : (FieldPair d × Regeneration.CoupledSample d) × ℝ =>
      (p.2, (p.1.1, p.1.2.1)) :=
    measurable_snd.prodMk ((measurable_fst.comp measurable_fst).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))
  have hcomp := (measurable_observation_abs G hG).comp hmap
  exact hcomp

/-- The coupled regeneration times satisfy the lower bound `τ k ≥ 2kΔ`, in `ℝ≥0∞`. -/
theorem coupledRegenerationTime_lower {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (hlam : 0 < lam)
    (hR : 0 < l / lam) (hΔ : 0 < Regeneration.Renewal.regenDelta lam)
    (ωz : FieldPair d × Regeneration.CoupledSample d) (k : ℕ) :
    ENNReal.ofReal (2 * (k : ℝ) * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) ≤
      Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) k := by
  rw [ofReal_two_mul_natCast_mul]
  exact Regeneration.nat_two_step_le_regenerationTime (Regeneration.Renewal.regenDelta lam) hΔ
    lam (l / lam) hlam hR ωz.2 (Regeneration.Renewal.forceCoord hd) k

/-- With `τ 0 = 0` pathwise, the first regeneration interval `[τ 0, τ 1)` is `[0, τ 1)`. -/
theorem lintegral_regenInterval_zero_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) (g : Ω → ℝ → ℝ≥0∞) (τ : ℕ → Ω → ℝ≥0∞)
    (hτ0 : ∀ ω, τ 0 ω = 0) :
    (∫⁻ ω, (∫⁻ t in regenInterval (τ 0 ω) (τ 1 ω), g ω t) ∂P) =
      ∫⁻ ω, (∫⁻ t in regenInterval 0 (τ 1 ω), g ω t) ∂P :=
  lintegral_congr fun ω => by simp only [hτ0]

/-- Steps 1 and 2 bound every coupled regeneration interval. Step 1 covers index `k = 0`,
because `τ 0 = 0` pathwise. -/
theorem coupled_regenInterval_bound {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l p C : ℝ) (K : Regeneration.CoupledQuenchedLaws d)
    (G : FieldPair d → ℝ)
    (hfirst : FirstRewardStep hd Q lam l p C K G)
    (hlater : LaterIntervalsStep hd Q lam l p C K G) (k : ℕ) :
    (∫⁻ ωz, (∫⁻ t in regenInterval
        (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
          (Regeneration.Renewal.forceCoord hd) k)
        (Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
          (Regeneration.Renewal.forceCoord hd) (k + 1)),
        ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
        ∂(Regeneration.annealedCoupledLaw Q.measure K)) ≤
      ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
        eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
  unfold FirstRewardStep at hfirst
  unfold LaterIntervalsStep at hlater
  cases k with
  | zero =>
    have h0 := lintegral_regenInterval_zero_eq (Regeneration.annealedCoupledLaw Q.measure K)
      (fun ωz t => ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
      (fun k ωz => Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) ωz.2 (Regeneration.Renewal.forceCoord hd) k)
      (fun ωz => regenerationTime_zero_eq _ _ _ _ _)
    exact h0.trans_le hfirst
  | succ n => exact hlater (n + 1) (by omega)

/-- The time bound of Proposition 3.2 (`regen.occupation-time`) from the two step inequalities,
for one `T > 0`. -/
theorem occupation_time_of_steps {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l p C : ℝ) (hl : 0 < l) (hlam : 0 < lam) (hC : 0 ≤ C)
    (K : Regeneration.CoupledQuenchedLaws d) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω))
    (hmarg : ∀ᵐ ω ∂Q.measure,
      Measure.map Prod.fst (Regeneration.originCoupledLaw K ω) = originLaw P ω)
    (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (G : FieldPair d → ℝ) (hG : Measurable G)
    (hfirst : FirstRewardStep hd Q lam l p C K G)
    (hlater : LaterIntervalsStep hd Q lam l p C K G)
    (T : ℝ) (hT : 0 < T) :
    (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
      ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) ≤
      ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
        eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
  have hΔeq : ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) = (lam ^ 2)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.2 (sq_nonneg lam))
  have hΔr : 0 < ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) := by
    rw [hΔeq]
    exact inv_pos.2 (pow_pos hlam 2)
  have hΔ0 : 0 < Regeneration.Renewal.regenDelta lam := NNReal.coe_pos.1 hΔr
  have hR : 0 < l / lam := div_pos hl hlam
  have hsum := lintegral_regenerationSum_le (Regeneration.annealedCoupledLaw Q.measure K)
    (fun ωz t => ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
    (measurable_coupledObservation G hG) ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) hΔr
    (fun k ωz => Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      ωz.2 (Regeneration.Renewal.forceCoord hd) k)
    (measurable_coupledRegenerationTime hd lam l) (fun ωz => regenerationTime_zero_eq _ _ _ _ _)
    (fun ωz k => coupledRegenerationTime_lower hd lam l hlam hR hΔ0 ωz k)
    (ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
      eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q))
    (coupled_regenInterval_bound hd Q lam l p C K G hfirst hlater) T hT.le
  have hfac := ofReal_occupation_factor C ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ) T hC
    hΔr hT.le (eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q))
  calc (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
        ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
      ∂(Carriers.annealedCoordinateJoint Q.measure P hP0))
      = ∫⁻ ωz, (∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal (ωz.1, ωz.2.1))|)
          ∂(Regeneration.annealedCoupledLaw Q.measure K) :=
        (lintegral_annealedCoupledLaw_path Q.measure K P hprob hmarg hP0
          (fun z => ∫⁻ t in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
          (measurable_occupation_integral G hG T)).symm
    _ ≤ ENNReal.ofReal (T / (2 * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) + 1) *
          (ENNReal.ofReal (C * ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)) := hsum
    _ ≤ ENNReal.ofReal (C * (T + ((Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ))) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := hfac
    _ = ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
        rw [hΔeq]

/-- Proposition 3.2 (`regen.occupation`, `paper/main.tex` lines 439–501), with the constant `C`
and the two step inequalities supplied. Both conclusions hold for every `T > 0` and every
exponential rate `s > 0`:
the occupation-time bound (`regen.occupation-time`) and the density bound
(`regen.occupation-resolvent`). -/
theorem occupation_of_steps {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ p C : ℝ) (hl : 0 < l) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hC : 0 ≤ C) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ hlam.le hlam1 P K)
    (hP0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (G : FieldPair d → ℝ)
    (hG : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G)
    (hfirst : FirstRewardStep hd Q lam l p C K G)
    (hlater : LaterIntervalsStep hd Q lam l p C K G) :
    ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
      (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) ≤
          ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) ∧
      ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q.measure P hP0 s rho →
        (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(Carriers.reducedReferenceLaw Q)) ≤
          ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
  have hG' : Measurable G := hG.mono (Probability.localSigma_le_borel _) le_rfl
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) :=
    hK.1.1
  have hmarg : ∀ᵐ ω ∂Q.measure,
      Measure.map Prod.fst (Regeneration.originCoupledLaw K ω) = originLaw P ω :=
    hK.2.1.1
  have hocc_time : ∀ T : ℝ, 0 < T →
      (∫⁻ z, (∫⁻ t in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) ≤
          ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) :=
    fun T hT => occupation_time_of_steps hd Q lam l p C hl hlam hC K P hprob hmarg hP0 G hG'
      hfirst hlater T hT
  intro T hT s
  refine ⟨hocc_time T hT, fun rho hrho => ?_⟩
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q.measure P hP0
  have hocc : ∀ T' : ℝ, 0 < T' →
      (∫⁻ t in Set.Icc (0 : ℝ) T', (∫⁻ z,
          ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0))) ≤
          ENNReal.ofReal (C * (T' + (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) := by
    intro T' hT'
    rw [lintegral_occupation_swap G hG' (Carriers.annealedCoordinateJoint Q.measure P hP0) T']
    exact hocc_time T' hT'
  have hgm : Measurable fun ℓ : ℝ => ∫⁻ z,
      ENNReal.ofReal |G (Carriers.reducedObservationAt ℓ.toNNReal z)|
        ∂(Carriers.annealedCoordinateJoint Q.measure P hP0) :=
    (measurable_observation_abs G hG').lintegral_prod_right'
  have hres := laplace_occupation_transfer lam C
    (eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)) hlam hC
    (fun t => ∫⁻ z, ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|
      ∂(Carriers.annealedCoordinateJoint Q.measure P hP0)) hgm hocc s.1 s.2
  exact (lintegral_mul_density_eq_laplace Q.measure P hP0 s rho hrho G hG').trans_le hres

end EinsteinRelation

end
