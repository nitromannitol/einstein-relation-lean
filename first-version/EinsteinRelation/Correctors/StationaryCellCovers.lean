import EinsteinRelation.External.AKMCorrectorOscillation
import EinsteinRelation.Correctors.FiniteCoverMoments

/-! Unit-scale spatial covering for `paper/main.tex:724-731`. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

open Set
open Finset

/-- A uniform finite number of centered lattice cells covers each radius-four ball. -/
theorem euclideanBall_four_cell_cover {d : ℕ} (z : Vec d) :
    ∃ s : Finset (LatticeIndex d), s.card ≤ 11 ^ d ∧
      ball z 4 ⊆ ⋃ k ∈ s, {x : Vec d | x - latticeShift k ∈ unitCell d} := by
  have h_card_interval (a : ℝ) : card (Icc (⌊a - 4.5⌋ + 1 : ℤ) (⌈a + 4.5⌉ - 1)) ≤ 9 := by
    rw [Int.card_Icc]
    have h_le : (⌈a + 4.5⌉ - 1 : ℤ) + 1 - (⌊a - 4.5⌋ + 1) ≤ (9 : ℤ) := by
      have hceil_eq : (⌈a + 4.5⌉ : ℤ) = (⌈a - 4.5⌉ : ℤ) + (9 : ℤ) := by
        calc
          (⌈a + 4.5⌉ : ℤ) = (⌈(a - 4.5) + (9 : ℤ)⌉ : ℤ) := by congr 1; norm_num; ring
          _ = (⌈a - 4.5⌉ : ℤ) + (9 : ℤ) := by rw [Int.ceil_add_intCast]
      have hceil_le_floor_add_one : (⌈a - 4.5⌉ : ℤ) ≤ ⌊a - 4.5⌋ + 1 := by
        exact mod_cast Int.ceil_le_floor_add_one (a - 4.5)
      omega
    have h_nonneg : 0 ≤ (⌈a + 4.5⌉ - 1 : ℤ) + 1 - (⌊a - 4.5⌋ + 1) := by
      have h_lt : (a - 4.5 : ℝ) < a + 4.5 := by nlinarith
      have h_floor_lt_ceil : (⌊a - 4.5⌋ : ℝ) < (⌈a + 4.5⌉ : ℝ) := by
        exact mod_cast Int.floor_lt_ceil_of_lt h_lt
      have h_floor_lt_ceil_int : (⌊a - 4.5⌋ : ℤ) < ⌈a + 4.5⌉ := by exact mod_cast h_floor_lt_ceil
      omega
    omega
  let I (i : Fin d) : Finset ℤ := Icc (⌊z i - 4.5⌋ + 1) (⌈z i + 4.5⌉ - 1)
  have hI_card (i : Fin d) : (I i).card ≤ 9 := h_card_interval (z i)
  let s : Finset (LatticeIndex d) := Fintype.piFinset I
  have hs_card : s.card ≤ 9 ^ d := by
    calc
      s.card = ∏ i : Fin d, (I i).card := by
        rw [Fintype.card_piFinset]
      _ ≤ ∏ i : Fin d, 9 := by
        refine Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i hi => hI_card i)
      _ = 9 ^ d := by simp
  have hs_card_11 : s.card ≤ 11 ^ d := by
    refine le_trans hs_card ?_
    have h9_le_11 : 9 ≤ 11 := by norm_num
    exact Nat.pow_le_pow_left h9_le_11 d
  refine ⟨s, hs_card_11, ?_⟩
  intro x hx
  rw [ball, Set.mem_setOf_eq] at hx
  have hx_comp (i : Fin d) : |x i - z i| < 4 := by
    have h_sq_bound : (x i - z i) ^ 2 ≤ euclideanSq (x - z) := by
      unfold euclideanSq dot
      calc
        (x i - z i) ^ 2 = ∑ j : Fin d, (if j = i then (x i - z i) ^ 2 else 0) := by
          simp
        _ ≤ ∑ j : Fin d, (x j - z j) ^ 2 := Finset.sum_le_sum (fun j _ => by
          by_cases hji : j = i
          · subst hji; simp
          · simp [hji, pow_two_nonneg])
        _ = euclideanSq (x - z) := by
          simp [euclideanSq, dot, sq]
    have h_sq_lt_16 : (x i - z i) ^ 2 < 16 := by
      have h_euclideanSq_lt_16 : euclideanSq (x - z) < 16 := by
        have h_nonneg : 0 ≤ euclideanSq (x - z) := by
          unfold euclideanSq dot
          apply Finset.sum_nonneg
          intro j _
          apply mul_self_nonneg
        have h_sqrt_lt : Real.sqrt (euclideanSq (x - z)) < 4 := hx
        have h_sq_eq : (Real.sqrt (euclideanSq (x - z))) ^ 2 = euclideanSq (x - z) :=
          Real.sq_sqrt h_nonneg
        have h_sqrt_nonneg : 0 ≤ Real.sqrt (euclideanSq (x - z)) := Real.sqrt_nonneg _
        nlinarith
      nlinarith
    have h_abs_sq_eq : |x i - z i| ^ 2 = (x i - z i) ^ 2 := by
      simp
    have h_abs_sq_lt_16 : |x i - z i| ^ 2 < 16 := by
      rw [h_abs_sq_eq]
      exact h_sq_lt_16
    have h_abs_nonneg : 0 ≤ |x i - z i| := abs_nonneg _
    nlinarith
  let k (i : Fin d) : ℤ := ⌊x i + 1/2⌋
  have hk_mem_I (i : Fin d) : k i ∈ I i := by
    have h_lower : (z i - 4.5 : ℝ) < (k i : ℝ) := by
      have hx_lower : z i - 4 < x i := by
        have h_abs_lt : -4 < x i - z i := by
          have := abs_lt.mp (hx_comp i)
          exact this.1
        linarith
      have h_floor_gt : x i - 1/2 < (k i : ℝ) := by
        have h := Int.lt_floor_add_one (x i + 1/2)
        dsimp [k]
        linarith
      linarith
    have h_upper : (k i : ℝ) < z i + 4.5 := by
      have hx_upper : x i < z i + 4 := by
        have h_abs_lt : x i - z i < 4 := by
          have := abs_lt.mp (hx_comp i)
          exact this.2
        linarith
      have h_floor_le : (k i : ℝ) ≤ x i + 1/2 := by
        dsimp [k]
        exact mod_cast Int.floor_le (x i + 1/2)
      linarith
    rw [Finset.mem_Icc]
    have h_lower_int : ⌊z i - 4.5⌋ + 1 ≤ k i := by
      have h_floor_lt : (⌊z i - 4.5⌋ : ℝ) < (k i : ℝ) := by
        have h_floor_le : (⌊z i - 4.5⌋ : ℝ) ≤ z i - 4.5 := by
          exact mod_cast Int.floor_le (z i - 4.5)
        linarith
      exact mod_cast h_floor_lt
    have h_upper_int : k i ≤ ⌈z i + 4.5⌉ - 1 := by
      have h_lt_ceil : (k i : ℝ) < (⌈z i + 4.5⌉ : ℝ) := by
        have h_le_ceil : z i + 4.5 ≤ (⌈z i + 4.5⌉ : ℝ) := by
          exact mod_cast Int.le_ceil (z i + 4.5)
        linarith
      have h_lt_ceil_int : k i < ⌈z i + 4.5⌉ := by exact mod_cast h_lt_ceil
      omega
    exact ⟨h_lower_int, h_upper_int⟩
  have hx_cell : x - latticeShift (fun i => k i) ∈ unitCell d := by
    rw [unitCell]
    intro i hi
    have h_floor_le : (k i : ℝ) ≤ x i + 1/2 := by
      dsimp [k]
      exact mod_cast Int.floor_le (x i + 1/2)
    have h_lt_floor_add_one : x i + 1/2 < (k i : ℝ) + 1 := by
      dsimp [k]
      have h := Int.lt_floor_add_one (x i + 1/2)
      exact h
    have h_lower : -1/2 ≤ x i - (k i : ℝ) := by linarith
    have h_upper : x i - (k i : ℝ) < 1/2 := by linarith
    exact Set.mem_Ico.mpr ⟨h_lower, h_upper⟩
  have hk_mem_s : (fun i => k i) ∈ s := by
    rw [Fintype.mem_piFinset]
    intro i
    exact hk_mem_I i
  refine Set.mem_biUnion hk_mem_s ?_
  rw [Set.mem_setOf_eq]
  simpa [latticeShift] using hx_cell

/-- Stationarity transports positive cell integrals without an
integrability assumption or a totalized Bochner integral. -/
theorem stationary_cell_lintegral_moment_translation {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (hP : LawHypotheses P)
    (F : Coefficient d K → Vec d → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F))
    (hs : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F a (x + latticeShift z) = F (translateCoefficient (latticeShift z) a) x)
    (z : LatticeIndex d) (q : ℝ) :
    (∫⁻ a, (∫⁻ x in {x : Vec d | x - latticeShift z ∈ unitCell d},
      F a x ∂volume) ^ q ∂P) =
      ∫⁻ a, (∫⁻ x in unitCell d, F a x ∂volume) ^ q ∂P := by
  have hcell : MeasurableSet (unitCell d) := by
    exact MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico
  have hshift : MeasurableSet {x : Vec d | x - latticeShift z ∈ unitCell d} :=
    hcell.preimage (measurable_id.sub measurable_const)
  have hpre : (fun x : Vec d => x + latticeShift z) ⁻¹'
      {x : Vec d | x - latticeShift z ∈ unitCell d} = unitCell d := by
    ext x
    simp only [Set.mem_preimage, Set.mem_setOf_eq, add_sub_cancel_right]
  have hspace (a : Coefficient d K) :
      (∫⁻ x in {x : Vec d | x - latticeShift z ∈ unitCell d}, F a x ∂volume) =
        ∫⁻ x in unitCell d, F a (x + latticeShift z) ∂volume := by
    have hm := (measurePreserving_add_right (volume : Measure (Vec d)) (latticeShift z)).setLIntegral_comp_preimage (f := F a) hshift
        (hF.comp (measurable_const.prodMk measurable_id))
    simpa only [hpre] using hm.symm
  let f (a : Coefficient d K) := (∫⁻ x in unitCell d, F a x ∂volume) ^ q
  have hf : Measurable f :=
    (hF.lintegral_prod_right (ν := volume.restrict (unitCell d))).pow_const q
  have heq : (fun a => (∫⁻ x in {x : Vec d | x - latticeShift z ∈ unitCell d},
      F a x ∂volume) ^ q) =ᵐ[P] (fun a => f (translateCoefficient (latticeShift z) a)) := by
    filter_upwards [hs z] with a ha
    rw [hspace]
    congr 1
    exact lintegral_congr_ae (ae_restrict_of_ae ha)
  rw [lintegral_congr_ae heq]
  exact (show MeasurePreserving (translateCoefficient (latticeShift z)) P P from
    ⟨measurable_translateCoefficient _, hP.2.1 z⟩).lintegral_comp hf

/-- A stationary positive field's cell moments control its radius-four
ball moments uniformly in the center. This is a moment of the spatial
integral; it does not exchange the spatial and stochastic exponents. -/
theorem stationary_ball_four_lintegral_moment_le {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (hP : LawHypotheses P)
    (F : Coefficient d K → Vec d → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F))
    (hs : ∀ z : LatticeIndex d, ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F a (x + latticeShift z) = F (translateCoefficient (latticeShift z) a) x)
    (q : ℝ) (hq : 1 ≤ q) (B : ℝ≥0∞)
    (hb : (∫⁻ a, (∫⁻ x in unitCell d, F a x ∂volume) ^ q ∂P) ≤ B)
    (z : Vec d) :
    (∫⁻ a, (∫⁻ x in ball z 4, F a x ∂volume) ^ q ∂P) ≤
      ((11 ^ d : ℕ) : ℝ≥0∞) ^ (q - 1) * (((11 ^ d : ℕ) : ℝ≥0∞) * B) := by
  obtain ⟨s, hsCard, hcover⟩ := euclideanBall_four_cell_cover z
  have hcast : (s.card : ℝ≥0∞) ≤ ((11 ^ d : ℕ) : ℝ≥0∞) := by exact_mod_cast hsCard
  calc
    _ ≤ (s.card : ℝ≥0∞) ^ (q - 1) *
        ∑ k ∈ s, ∫⁻ a, (∫⁻ x in {x : Vec d | x - latticeShift k ∈ unitCell d},
          F a x ∂volume) ^ q ∂P :=
      lintegral_setLIntegral_rpow_le_finite_cover P volume s _ _ hcover F hF q hq
    _ ≤ (s.card : ℝ≥0∞) ^ (q - 1) * ∑ _k ∈ s, B := by
      exact mul_le_mul_right (Finset.sum_le_sum fun k _ =>
        (stationary_cell_lintegral_moment_translation hP F hF hs k q).le.trans hb) _
    _ = (s.card : ℝ≥0∞) ^ (q - 1) * ((s.card : ℝ≥0∞) * B) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul'
      (ENNReal.rpow_le_rpow hcast (by linarith)) (mul_le_mul_left hcast B)

end EinsteinRelation.Correctors

