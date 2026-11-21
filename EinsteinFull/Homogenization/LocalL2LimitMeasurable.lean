import EinsteinFull.Homogenization.LocalL2Limit

/-!
# Measurable dependence of the selected `L²_loc` limit on a parameter

If a family of sequences `D ω p x` is jointly measurable in the parameter `ω` and the space
variable `x`, then so is the selected limit `locL2Limit (D ω) x`. The selection indices are
measurable in `ω` because each Cauchy condition is a countable intersection of sublevel sets of
measurable `L²` norms. This is the measurability of the heat-selected flux corrector of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*, (6.7), in
the coefficient field.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.External.AKM

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Evaluation at a measurable index. -/
theorem measurable_of_nat_index {β : Type*} [MeasurableSpace β] {c : Ω → ℕ} (hc : Measurable c)
    {F : ℕ → Ω → β} (hF : ∀ n, Measurable (F n)) : Measurable (fun ω => F (c ω) ω) := by
  intro s hs
  have h : (fun ω => F (c ω) ω) ⁻¹' s = ⋃ n, (c ⁻¹' {n}) ∩ (F n ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_singleton_iff]
    exact ⟨fun h => ⟨c ω, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [h]
  exact MeasurableSet.iUnion fun n => (hc (measurableSet_singleton n)).inter (hF n hs)

variable {D : Ω → ℕ → Vec d → ℝ}

theorem measurable_eLpNorm_sub (hD : ∀ p, Measurable (fun z : Ω × Vec d => D z.1 p z.2))
    (p q : ℕ) (μ : Measure (Vec d)) [SFinite μ] :
    Measurable (fun ω => eLpNorm (fun x => D ω p x - D ω q x) 2 μ) := by
  have hF : Measurable (fun z : Ω × Vec d => ‖D z.1 p z.2 - D z.1 q z.2‖ₑ ^ (2 : ℝ)) :=
    ((hD p).sub (hD q)).enorm.pow_const _
  have hsec : ∀ ω, AEStronglyMeasurable (fun x => D ω p x - D ω q x) μ := fun ω =>
    (((hD p).comp (measurable_const.prodMk measurable_id)).sub
      ((hD q).comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have h : (fun ω => eLpNorm (fun x => D ω p x - D ω q x) 2 μ) = fun ω =>
      (∫⁻ x, ‖D ω p x - D ω q x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := by
    funext ω
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hsec ω)]
    simp only [ENNReal.toReal_ofNat]
  rw [h]
  exact hF.lintegral_prod_right'.pow_const _

theorem measurableSet_cauchyAt (hD : ∀ p, Measurable (fun z : Ω × Vec d => D z.1 p z.2))
    (k N : ℕ) : MeasurableSet {ω | CauchyAt (D ω) k N} := by
  have h : {ω | CauchyAt (D ω) k N} = ⋂ p, ⋂ q, {ω | N ≤ p → N ≤ q →
      eLpNorm (fun x => D ω p x - D ω q x) 2 (volume.restrict (ball 0 (k : ℝ))) ≤
        (2⁻¹ : ℝ≥0∞) ^ k} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, CauchyAt]
  rw [h]
  refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun q => ?_
  by_cases hp : N ≤ p
  · by_cases hq : N ≤ q
    · simp only [hp, hq, true_implies]
      exact measurableSet_le (measurable_eLpNorm_sub hD p q _) measurable_const
    · simp only [hq, false_implies, implies_true, ofPred_true, MeasurableSet.univ]
  · simp only [hp, false_implies, ofPred_true, MeasurableSet.univ]

theorem measurable_cauchyIndex (hD : ∀ p, Measurable (fun z : Ω × Vec d => D z.1 p z.2))
    (k : ℕ) : Measurable (fun ω => cauchyIndex (D ω) k) := by
  classical
  set A : ℕ → Set Ω := fun N => {ω | CauchyAt (D ω) k N} with hA
  have hAm : ∀ N, MeasurableSet (A N) := measurableSet_cauchyAt hD k
  refine measurable_to_countable' fun n => ?_
  have h : (fun ω => cauchyIndex (D ω) k) ⁻¹' {n} =
      ((⋃ N, A N) ∩ (A n ∩ ⋂ m ∈ Finset.range n, (A m)ᶜ)) ∪
        ((⋃ N, A N)ᶜ ∩ {_ω | n = 0}) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iUnion,
      mem_iInter, mem_compl_iff, Finset.mem_range, mem_ofPred_eq, hA, not_exists]
    unfold cauchyIndex
    split_ifs with hex
    · rw [Nat.find_eq_iff]
      constructor
      · intro ⟨h1, h2⟩
        exact Or.inl ⟨hex, h1, fun m hm => h2 m hm⟩
      · rintro (⟨-, h1, h2⟩ | ⟨h1, -⟩)
        · exact ⟨h1, fun m hm => h2 m hm⟩
        · exact absurd hex (not_exists.mpr h1)
    · constructor
      · intro h
        exact Or.inr ⟨not_exists.mp hex, h.symm⟩
      · rintro (⟨h1, -⟩ | ⟨-, h2⟩)
        · exact absurd h1 hex
        · exact h2.symm
  rw [h]
  refine ((MeasurableSet.iUnion hAm).inter ((hAm n).inter ?_)).union
    ((MeasurableSet.iUnion hAm).compl.inter ?_)
  · exact MeasurableSet.biInter (Finset.range n).countable_toSet fun m _ => (hAm m).compl
  · by_cases hn : n = 0
    · simp only [hn, ofPred_true, MeasurableSet.univ]
    · simp only [hn, ofPred_false, MeasurableSet.empty]

theorem measurable_cumCauchyIndex (hD : ∀ p, Measurable (fun z : Ω × Vec d => D z.1 p z.2))
    (k : ℕ) : Measurable (fun ω => cumCauchyIndex (D ω) k) := by
  unfold cumCauchyIndex
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sup_singleton]
    exact measurable_cauchyIndex hD 0
  | succ k ih =>
    simp_rw [Finset.range_add_one (n := k + 1), Finset.sup_insert]
    have h1 := measurable_cauchyIndex hD (k + 1)
    refine measurable_to_countable' fun n => ?_
    have h : (fun ω => cauchyIndex (D ω) (k + 1) ⊔
        (Finset.range (k + 1)).sup (cauchyIndex (D ω))) ⁻¹' {n} =
        ⋃ a ∈ Finset.range (n + 1), ⋃ b ∈ Finset.range (n + 1),
          if a ⊔ b = n then (fun ω => cauchyIndex (D ω) (k + 1)) ⁻¹' {a} ∩
            (fun ω => (Finset.range (k + 1)).sup (cauchyIndex (D ω))) ⁻¹' {b} else ∅ := by
      ext ω
      simp only [mem_preimage, mem_singleton_iff, mem_iUnion, Finset.mem_range]
      constructor
      · intro h
        refine ⟨cauchyIndex (D ω) (k + 1), by omega, (Finset.range (k + 1)).sup
          (cauchyIndex (D ω)), by omega, ?_⟩
        simp only [h, ↓reduceIte]
        exact ⟨rfl, rfl⟩
      · rintro ⟨a, -, b, -, hab⟩
        split_ifs at hab with hn
        · obtain ⟨ha, hb⟩ := hab
          simp only [mem_preimage, mem_singleton_iff] at ha hb
          rw [ha, hb, hn]
        · exact absurd hab (notMem_empty ω)
    rw [h]
    refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet fun a _ =>
      MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet fun b _ => ?_
    split_ifs
    · exact (h1 (measurableSet_singleton a)).inter (ih (measurableSet_singleton b))
    · exact MeasurableSet.empty

/-- **The selected `L²_loc` limit is jointly measurable in the parameter.** -/
theorem measurable_locL2Limit_param (hD : ∀ p, Measurable (fun z : Ω × Vec d => D z.1 p z.2)) :
    Measurable (fun z : Ω × Vec d => locL2Limit (D z.1) z.2) := by
  unfold locL2Limit
  refine Measurable.limsup fun k => ?_
  exact measurable_of_nat_index ((measurable_cumCauchyIndex hD k).comp measurable_fst) hD

end EinsteinFull.Homogenization
