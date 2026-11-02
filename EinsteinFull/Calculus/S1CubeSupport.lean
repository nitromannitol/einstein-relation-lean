import EinsteinFull.Work.W7.ClockFiniteRangeSupport

/-! Elementary geometry of the open cubes `clockBlockCube x L = x + (-L/2, L/2)^d`:
monotonicity, translation, the strip decomposition and the dyadic tiling of the
cube of side `2L` into the `2^d` children of side `L` centred at `(± L/2, ..., ± L/2)`. -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem mem_clockBlockCube_iff {x y : Vec d} {L : ℝ} :
    y ∈ clockBlockCube x L ↔ ∀ j, x j - L / 2 < y j ∧ y j < x j + L / 2 := by
  simp only [clockBlockCube, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ioo]

theorem clockBlockCube_mono' (x : Vec d) {a b : ℝ} (hab : a ≤ b) :
    clockBlockCube x a ⊆ clockBlockCube x b := by
  intro y hy
  rw [mem_clockBlockCube_iff] at hy ⊢
  intro j
  exact ⟨by linarith [(hy j).1], by linarith [(hy j).2]⟩

theorem add_mem_clockBlockCube_add_iff {c x y : Vec d} {L : ℝ} :
    c + y ∈ clockBlockCube (c + x) L ↔ y ∈ clockBlockCube x L := by
  simp only [mem_clockBlockCube_iff, Pi.add_apply]
  constructor
  · intro h j
    exact ⟨by linarith [(h j).1], by linarith [(h j).2]⟩
  · intro h j
    exact ⟨by linarith [(h j).1], by linarith [(h j).2]⟩

theorem setIntegral_clockBlockCube_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec d → E) (c x : Vec d) (L : ℝ) :
    ∫ y in clockBlockCube (c + x) L, g y = ∫ y in clockBlockCube x L, g (c + y) := by
  rw [← integral_indicator (measurableSet_clockBlockCube _ _),
    ← integral_indicator (measurableSet_clockBlockCube _ _),
    ← integral_add_left_eq_self (f := (clockBlockCube (c + x) L).indicator g) c]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (clockBlockCube (c + x) L).indicator g (c + y) =
    (clockBlockCube x L).indicator (fun y => g (c + y)) y
  by_cases h : y ∈ clockBlockCube x L
  · have h' : c + y ∈ clockBlockCube (c + x) L := add_mem_clockBlockCube_add_iff.2 h
    rw [Set.indicator_of_mem h', Set.indicator_of_mem h]
  · have h' : c + y ∉ clockBlockCube (c + x) L := fun h'' => h (add_mem_clockBlockCube_add_iff.1 h'')
    rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]

theorem volume_clockBlockCube_lt_top (x : Vec d) (L : ℝ) :
    volume (clockBlockCube x L) < ⊤ := by
  have : clockBlockCube x L ⊆ clockBlockCube x (max L 0) :=
    clockBlockCube_mono' x (le_max_left _ _)
  calc volume (clockBlockCube x L) ≤ volume (clockBlockCube x (max L 0)) := measure_mono this
    _ = ENNReal.ofReal ((max L 0) ^ d) := volume_clockBlockCube x (le_max_right _ _)
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- Centers of the `2^d` children of the cube of side `2L` at the origin. -/
noncomputable def childCenter (L : ℝ) (j : Fin d → Fin 2) : Vec d :=
  fun i => if j i = 0 then -L / 2 else L / 2

theorem clockBlockCube_children_disjoint {L : ℝ} {j k : Fin d → Fin 2} (hjk : j ≠ k) :
    Disjoint (clockBlockCube (childCenter L j) L) (clockBlockCube (childCenter L k) L) := by
  rw [Set.disjoint_left]
  intro y hy hy'
  rw [mem_clockBlockCube_iff] at hy hy'
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hjk
  have h1 := hy i
  have h2 := hy' i
  simp only [childCenter] at h1 h2
  have hcases : (j i = 0 ∧ k i ≠ 0) ∨ (j i ≠ 0 ∧ k i = 0) := by
    revert hi
    generalize j i = a
    generalize k i = b
    fin_cases a <;> fin_cases b <;> simp
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp only [ha, hb, if_true, if_false] at h1 h2
    linarith [h1.2, h2.1]
  · simp only [ha, hb, if_true, if_false] at h1 h2
    linarith [h1.1, h2.2]

theorem clockBlockCube_child_subset (L : ℝ) (j : Fin d → Fin 2) :
    clockBlockCube (childCenter L j) L ⊆ clockBlockCube 0 (2 * L) := by
  intro y hy
  rw [mem_clockBlockCube_iff] at hy ⊢
  intro i
  have h := hy i
  simp only [childCenter] at h
  simp only [Pi.zero_apply]
  split_ifs at h
  · exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem clockBlockCube_two_ae_eq (L : ℝ) :
    clockBlockCube 0 (2 * L) =ᵐ[volume] ⋃ j : Fin d → Fin 2, clockBlockCube (childCenter L j) L := by
  have hne : ∀ᵐ y : Vec d ∂volume, ∀ i, y i ≠ 0 := by
    rw [ae_all_iff]
    intro i
    rw [volume_pi]
    exact Measure.ae_eval_ne (fun _ : Fin d => (volume : Measure ℝ)) i 0
  rw [Filter.eventuallyEq_set]
  filter_upwards [hne] with y hy
  constructor
  · intro hmem
    rw [mem_clockBlockCube_iff] at hmem
    refine Set.mem_iUnion.2 ⟨fun i => if y i < 0 then 0 else 1, ?_⟩
    rw [mem_clockBlockCube_iff]
    intro i
    have h := hmem i
    simp only [Pi.zero_apply] at h
    simp only [childCenter]
    by_cases hneg : y i < 0
    · simp only [hneg, if_true]
      exact ⟨by linarith [h.1], by linarith⟩
    · have hpos : 0 < y i := lt_of_le_of_ne (not_lt.1 hneg) (Ne.symm (hy i))
      have h10 : ¬ ((1 : Fin 2) = 0) := by decide
      simp only [hneg, h10, ite_false]
      exact ⟨by linarith, by linarith [h.2]⟩
  · intro hmem
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hmem
    exact clockBlockCube_child_subset L j hj

theorem setIntegral_clockBlockCube_two {g : Vec d → ℝ} {L : ℝ}
    (hg : IntegrableOn g (clockBlockCube 0 (2 * L))) :
    ∫ y in clockBlockCube 0 (2 * L), g y =
      ∑ j : Fin d → Fin 2, ∫ y in clockBlockCube (childCenter L j) L, g y := by
  rw [setIntegral_congr_set (clockBlockCube_two_ae_eq L)]
  refine integral_iUnion_fintype (fun j => measurableSet_clockBlockCube _ _)
    (fun j k hjk => clockBlockCube_children_disjoint hjk) (fun j => ?_)
  exact hg.mono_set (clockBlockCube_child_subset L j)

end EinsteinFull.Calculus.S1
