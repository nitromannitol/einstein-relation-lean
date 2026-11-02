import EinsteinFull.Calculus.C20UnforcedClockRate
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull.Blueprint

/-- Nonnegative maximum of the first `n` orbit partial sums, including zero. -/
private def clockPartialMax {α : Type*} (T : α → α) (f : α → ℝ) : ℕ → α → ℝ
  | 0, _ => 0
  | n + 1, x => max 0 (f x + clockPartialMax T f n (T x))

private lemma clockPartialMax_nonneg {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) : 0 ≤ clockPartialMax T f n x := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

private lemma clockPartialMax_mono {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) : clockPartialMax T f n x ≤ clockPartialMax T f (n + 1) x := by
  induction n generalizing x with
  | zero => exact clockPartialMax_nonneg T f 1 x
  | succ n ih =>
    exact max_le_max le_rfl (add_le_add le_rfl (ih (T x)))

private lemma clock_sum_le_partialMax {α : Type*} (T : α → α) (f : α → ℝ)
    (n k : ℕ) (hk : k ≤ n) (x : α) :
    birkhoffSum T f k x ≤ clockPartialMax T f n x := by
  induction n generalizing k x with
  | zero =>
    have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    exact le_rfl
  | succ n ih =>
    cases k with
    | zero => exact clockPartialMax_nonneg T f (n + 1) x
    | succ k =>
      rw [birkhoffSum_succ_apply']
      exact (add_le_add le_rfl (ih k (Nat.le_of_succ_le_succ hk) (T x))).trans
        (le_max_right _ _)

private lemma clockPartialMax_attained {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) :
    clockPartialMax T f n x = 0 ∨
      ∃ k ≤ n, clockPartialMax T f n x = birkhoffSum T f k x := by
  induction n generalizing x with
  | zero => exact Or.inl rfl
  | succ n ih =>
    by_cases h : f x + clockPartialMax T f n (T x) ≤ 0
    · exact Or.inl (max_eq_left h)
    · right
      have hm : clockPartialMax T f (n + 1) x =
          f x + clockPartialMax T f n (T x) := max_eq_right (le_of_not_ge h)
      rcases ih (T x) with hz | ⟨k, hk, heq⟩
      · refine ⟨1, Nat.succ_le_succ (Nat.zero_le n), ?_⟩
        simpa only [hz, add_zero, birkhoffSum_one_apply] using hm
      · refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
        rw [hm, heq, birkhoffSum_succ_apply']

private lemma clockPartialMax_pos_iff {α : Type*} (T : α → α) (f : α → ℝ)
    (n : ℕ) (x : α) :
    0 < clockPartialMax T f n x ↔ ∃ k ≤ n, 0 < birkhoffSum T f k x := by
  constructor
  · intro h
    rcases clockPartialMax_attained T f n x with hz | ⟨k, hk, heq⟩
    · exact False.elim ((ne_of_gt h) hz)
    · exact ⟨k, hk, heq ▸ h⟩
  · rintro ⟨k, hk, h⟩
    exact h.trans_le (clock_sum_le_partialMax T f n k hk x)

private lemma clockPartialMax_integrable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (clockPartialMax T f n) μ := by
  induction n with
  | zero => exact integrable_zero α ℝ μ
  | succ n ih =>
    exact (integrable_zero α ℝ μ).sup
      (hf.add (hT.integrable_comp_of_integrable ih))

/-- Finite Hopf maximal ergodic inequality. The set includes precisely those
points with a positive orbit partial sum of length at most `N`. No invertibility
or pointwise measurability of the integrable observable is required. -/
theorem clock_finite_maximal_ergodic {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {T : α → α} (hT : MeasurePreserving T μ μ)
    {f : α → ℝ} (hf : Integrable f μ) (N : ℕ) :
    0 ≤ ∫ x in {x | ∃ n ≤ N, 0 < birkhoffSum T f n x}, f x ∂μ := by
  let M := clockPartialMax T f N
  let E := {x | 0 < M x}
  have hM : Integrable M μ := clockPartialMax_integrable hT hf N
  have hMT : Integrable (fun x => M (T x)) μ :=
    hT.integrable_comp_of_integrable hM
  have hE : NullMeasurableSet E μ :=
    nullMeasurableSet_lt aemeasurable_const hM.aemeasurable
  have hbound : ∀ x, M x - M (T x) ≤ E.indicator f x := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hpos : 0 < clockPartialMax T f N x := hx
      cases N with
      | zero => exact False.elim ((lt_irrefl 0) hpos)
      | succ n =>
        have hsum : 0 < f x + clockPartialMax T f n (T x) :=
          (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
        have heq : M x = f x + clockPartialMax T f n (T x) :=
          max_eq_right hsum.le
        have hle := clockPartialMax_mono T f n (T x)
        change clockPartialMax T f n (T x) ≤ M (T x) at hle
        linarith only [heq, hle]
    · rw [Set.indicator_of_notMem hx]
      have hz : M x = 0 := le_antisymm (le_of_not_gt hx)
        (clockPartialMax_nonneg T f N x)
      rw [hz, zero_sub]
      exact neg_nonpos.mpr (clockPartialMax_nonneg T f N (T x))
  have hinv : (∫ x, M (T x) ∂μ) = ∫ x, M x ∂μ := by
    have hm : AEStronglyMeasurable M (Measure.map T μ) :=
      hT.map_eq.symm ▸ hM.aestronglyMeasurable
    exact (integral_map hT.measurable.aemeasurable hm).symm.trans
      (congrArg (fun ν => ∫ x, M x ∂ν) hT.map_eq)
  have hineq := integral_mono (hM.sub hMT) (hf.indicator₀ hE) hbound
  change (∫ x, M x - M (T x) ∂μ) ≤ ∫ x, E.indicator f x ∂μ at hineq
  rw [integral_sub hM hMT, hinv, sub_self, integral_indicator₀ hE] at hineq
  have hsets : E = {x | ∃ n ≤ N, 0 < birkhoffSum T f n x} := by
    ext x
    exact clockPartialMax_pos_iff T f N x
  rwa [hsets] at hineq

private lemma clock_birkhoffSum_integrable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (n : ℕ) :
    Integrable (birkhoffSum T f n) μ := by
  induction n with
  | zero => simpa only [birkhoffSum_zero] using integrable_zero Ω ℝ μ
  | succ n ih =>
    simpa only [birkhoffSum_succ', Function.comp_def, Pi.add_apply] using
      hf.add (hT.integrable_comp_of_integrable ih)

private lemma clock_sum_birkhoffSum_sub_shift {Ω : Type*} (T : Ω → Ω)
    (f : Ω → ℝ) (n : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range n, birkhoffSum T f k ω) -
      (∑ k ∈ Finset.range n, birkhoffSum T f k (T ω)) =
        (n : ℝ) * f ω - birkhoffSum T f n ω := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero,
      zero_mul, birkhoffSum_zero_apply, sub_self]
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.cast_add,
      Nat.cast_one, birkhoffSum_succ_apply']
    linarith only [ih]

/-- A vanishing L¹ Birkhoff average gives arbitrarily accurate integrable
coboundaries, by averaging the preceding orbit partial sums. -/
theorem clock_coboundary_approximation_of_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ) (hf : Integrable f μ)
    (hmean : Tendsto (fun n : ℕ => ∫ ω,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∃ g : Ω → ℝ, Integrable g μ ∧
      (∫ ω, |f ω - (g ω - g (T ω))| ∂μ) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := (hmean.eventually (gt_mem_nhds hε)).exists
  let H : Ω → ℝ := fun ω =>
    ∑ k ∈ Finset.range (N + 1), birkhoffSum T f k ω
  let g : Ω → ℝ := fun ω => H ω / ((N : ℝ) + 1)
  have hH : Integrable H μ :=
    integrable_finsetSum _ (fun k _ => clock_birkhoffSum_integrable hT hf k)
  refine ⟨g, hH.div_const _, ?_⟩
  have hden : (N : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
  have hres (ω : Ω) : f ω - (g ω - g (T ω)) =
      birkhoffSum T f (N + 1) ω / ((N : ℝ) + 1) := by
    have htel := clock_sum_birkhoffSum_sub_shift T f (N + 1) ω
    change H ω - H (T ω) = ((N + 1 : ℕ) : ℝ) * f ω -
      birkhoffSum T f (N + 1) ω at htel
    rw [Nat.cast_add, Nat.cast_one] at htel
    change f ω - (H ω / ((N : ℝ) + 1) - H (T ω) / ((N : ℝ) + 1)) = _
    calc
      _ = (((N : ℝ) + 1) * f ω - (H ω - H (T ω))) / ((N : ℝ) + 1) := by
        field_simp [hden]
      _ = _ := by rw [htel]; ring
  simpa only [hres] using hN

private lemma clock_coboundary_average_ae {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (g : Ω → ℝ) (hg : Integrable g μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ =>
      birkhoffSum T (fun x => g x - g (T x)) (n + 1) ω / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
  have horbit := c20_integrable_orbit_div_nat_ae μ T hT (fun x => g (T x))
    (hT.integrable_comp_of_integrable hg)
  filter_upwards [horbit] with ω hω
  have hconst : Tendsto (fun n : ℕ => g ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds (x := g ω)).mul
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htel (n : ℕ) :
      birkhoffSum T (fun x => g x - g (T x)) n ω = g ω - g ((T^[n]) ω) := by
    induction n with
    | zero => simp only [birkhoffSum_zero_apply, Function.iterate_zero_apply, sub_self]
    | succ n ih =>
      rw [birkhoffSum_succ_apply, ih, Function.iterate_succ_apply']
      ring
  have hlim := hconst.sub hω
  simpa only [sub_zero, htel, sub_div, Function.iterate_succ_apply'] using hlim

/-- L¹ decay of orbit averages implies almost-everywhere decay, using dense
coboundaries and the weak L¹ maximal estimate. -/
theorem clock_pointwise_of_l1_mean_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω → Ω)
    (hT : MeasurePreserving T μ μ) (f : Ω → ℝ)
    (hmf : Measurable f) (hf : Integrable f μ)
    (hmean : Tendsto (fun n : ℕ => ∫ ω,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ∂μ) Filter.atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1))
      Filter.atTop (𝓝 0) := by
  have hevent (ε : ℝ) (hε : 0 < ε) :
      ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop,
        |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ≤ ε := by
    let A : Set Ω := {ω | ¬ ∀ᶠ n : ℕ in atTop,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ≤ ε}
    have hA : μ.real A = 0 := by
      have hnonpos : (ε / 2) * μ.real A ≤ 0 := by
        by_contra hpos
        have hδ : 0 < (ε / 2) * μ.real A := lt_of_not_ge hpos
        obtain ⟨g, hg, happrox⟩ := clock_coboundary_approximation_of_mean_zero
          μ T hT f hf hmean _ hδ
        let g' := hg.aestronglyMeasurable.mk g
        have heq : g =ᵐ[μ] g' := hg.aestronglyMeasurable.ae_eq_mk
        have hmg' : Measurable g' := hg.aestronglyMeasurable.measurable_mk
        have hg' : Integrable g' μ := hg.congr heq
        let c : Ω → ℝ := fun x => g' x - g' (T x)
        let r : Ω → ℝ := fun x => f x - c x
        have hmc : Measurable c := hmg'.sub (hmg'.comp hT.measurable)
        have hc : Integrable c μ := hg'.sub (hT.integrable_comp_of_integrable hg')
        have hmr : Measurable r := hmf.sub hmc
        have hr : Integrable r μ := hf.sub hc
        have hsmall : (∫ x, ‖r x‖ ∂μ) < (ε / 2) * μ.real A := by
          have hcomp := hT.quasiMeasurePreserving.ae_eq_comp heq
          have hint : (fun x => ‖r x‖) =ᵐ[μ]
              (fun x => |f x - (g x - g (T x))|) := by
            filter_upwards [heq, hcomp] with x hx hTx
            change g (T x) = g' (T x) at hTx
            simp only [r, c, Real.norm_eq_abs, hx, hTx]
          rw [integral_congr_ae hint]
          exact happrox
        let B : Set Ω := {ω | ∃ k : ℕ,
          (k : ℝ) * (ε / 2) < ‖birkhoffSum T r k ω‖}
        let N : Set Ω := {ω | ¬ Tendsto (fun n : ℕ =>
          birkhoffSum T c (n + 1) ω / ((n : ℝ) + 1)) atTop (𝓝 0)}
        have hN : μ N = 0 := by
          exact ae_iff.1 (clock_coboundary_average_ae μ T hT g' hg')
        have hsub : A ⊆ B ∪ N := by
          intro ω hω
          by_contra hnot
          have hB : ω ∉ B := fun hb => hnot (Or.inl hb)
          have hlim : Tendsto (fun n : ℕ =>
              birkhoffSum T c (n + 1) ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
            by_contra hn
            exact hnot (Or.inr hn)
          have hcsmall : ∀ᶠ n : ℕ in atTop,
              |birkhoffSum T c (n + 1) ω / ((n : ℝ) + 1)| < ε / 2 := by
            simpa only [Real.dist_eq, sub_zero] using
              (tendsto_iff_dist_tendsto_zero.1 hlim).eventually
                (gt_mem_nhds (half_pos hε))
          apply hω
          filter_upwards [hcsmall] with n hn
          have hden : 0 < (n : ℝ) + 1 := by positivity
          have hres : |birkhoffSum T r (n + 1) ω / ((n : ℝ) + 1)| ≤ ε / 2 := by
            rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
            have hb : ¬ (((n + 1 : ℕ) : ℝ) * (ε / 2) <
                ‖birkhoffSum T r (n + 1) ω‖) := fun hb => hB ⟨n + 1, hb⟩
            simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, mul_comm] using
              le_of_not_gt hb
          have hsplit : birkhoffSum T f (n + 1) ω =
              birkhoffSum T r (n + 1) ω + birkhoffSum T c (n + 1) ω := by
            have hs := birkhoffSum_sub_apply T f c (n + 1) ω
            change birkhoffSum T r (n + 1) ω = _ at hs
            linarith only [hs]
          rw [hsplit, add_div]
          exact (abs_add_le _ _).trans (by linarith only [hres, hn])
        have hmono : μ.real A ≤ μ.real B := by
          calc
            μ.real A ≤ μ.real (B ∪ N) := measureReal_mono hsub
            _ ≤ μ.real B + μ.real N := measureReal_union_le _ _
            _ = μ.real B := by rw [(measureReal_eq_zero_iff).2 hN, add_zero]
        have hmax := c20_birkhoff_abs_maximal_measure_bound hT hmr hr
          (le_of_lt (half_pos hε))
        have hbound := (mul_le_mul_of_nonneg_left hmono
          (le_of_lt (half_pos hε))).trans hmax
        exact (not_lt_of_ge hbound) hsmall
      apply le_antisymm _ measureReal_nonneg
      exact le_of_not_gt fun hApos =>
        (not_lt_of_ge hnonpos) (mul_pos (half_pos hε) hApos)
    exact ae_iff.2 ((measureReal_eq_zero_iff).1 hA)
  have hall : ∀ᵐ ω ∂μ, ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |birkhoffSum T f (n + 1) ω / ((n : ℝ) + 1)| ≤ 1 / ((k : ℝ) + 1) := by
    rw [ae_all_iff]
    intro k
    exact hevent _ (by positivity)
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero]
  exact (hN n hn).trans_lt hk

end EinsteinFull.Blueprint
