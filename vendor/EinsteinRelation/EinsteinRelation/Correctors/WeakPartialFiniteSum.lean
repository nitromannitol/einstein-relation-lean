import EinsteinRelation.Correctors.WeakPartialAddition

namespace EinsteinRelation.Correctors

/-- Weak spatial derivatives commute with finite sums of corrector bands
(`paper/main.tex:1060–1072`). -/
theorem hasWeakPartialDerivative_finset_sum {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {j : Fin d} (s : Finset ι)
    {f g : ι → Vec d → ℝ}
    (h : ∀ i ∈ s, HasWeakPartialDerivative U j (f i) (g i)) :
    HasWeakPartialDerivative U j (fun x => ∑ i ∈ s, f i x)
      (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MeasureTheory.locallyIntegrableOn_zero,
      MeasureTheory.locallyIntegrableOn_zero, by intro φ hφ; simp⟩
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using
      hasWeakPartialDerivative_add (h i (Finset.mem_insert_self i s))
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

end EinsteinRelation.Correctors
