import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Source: `paper/main.tex:808–816,833–848`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem setIntegral_time_triangle_swap {a b : ℝ} (F : ℝ × ℝ → ℝ)
    (hF : IntegrableOn F (Set.Icc a b ×ˢ Set.Icc a b) (volume.prod volume)) :
    (∫ t in Set.Icc a b, ∫ s in Set.Icc a t, F (s,t)) =
      ∫ s in Set.Icc a b, ∫ t in Set.Icc s b, F (s,t) := by
  obtain ⟨K, hKfun⟩ : ∃ K : ℝ × ℝ → ℝ, K = {p : ℝ × ℝ | p.1 ≤ p.2}.indicator F :=
    ⟨_, rfl⟩
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hKint : Integrable K
      ((volume.restrict (Set.Icc a b)).prod (volume.restrict (Set.Icc a b))) := by
    rw [hKfun, Measure.prod_restrict]
    exact Integrable.indicator hF hmeas
  have key := integral_integral_swap (f := fun s t => K (s,t)) hKint
  have hL : ∀ t ∈ Set.Icc a b,
      ∫ s in Set.Icc a t, F (s,t) = ∫ s in Set.Icc a b, K (s,t) := by
    intro t ht
    have hpt : (fun s => K (s,t)) = (Set.Iic t).indicator (fun s => F (s,t)) := by
      funext s
      by_cases h : s ≤ t <;> simp [hKfun, Set.indicator_apply, h]
    have hset : Set.Icc a b ∩ Set.Iic t = Set.Icc a t := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, h3.trans ht.2⟩, h3⟩
    rw [hpt, setIntegral_indicator measurableSet_Iic, hset]
  have hR : ∀ s ∈ Set.Icc a b,
      ∫ t in Set.Icc s b, F (s,t) = ∫ t in Set.Icc a b, K (s,t) := by
    intro s hs
    have hpt : (fun t => K (s,t)) = (Set.Ici s).indicator (fun t => F (s,t)) := by
      funext t
      by_cases h : s ≤ t <;> simp [hKfun, Set.indicator_apply, h]
    have hset : Set.Icc a b ∩ Set.Ici s = Set.Icc s b := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h3, h2⟩
        exact ⟨⟨hs.1.trans h3, h2⟩, h3⟩
    rw [hpt, setIntegral_indicator measurableSet_Ici, hset]
  calc (∫ t in Set.Icc a b, ∫ s in Set.Icc a t, F (s,t))
      = ∫ t in Set.Icc a b, ∫ s in Set.Icc a b, K (s,t) :=
        setIntegral_congr_fun measurableSet_Icc (fun t ht => hL t ht)
    _ = ∫ s in Set.Icc a b, ∫ t in Set.Icc a b, K (s,t) := key.symm
    _ = ∫ s in Set.Icc a b, ∫ t in Set.Icc s b, F (s,t) :=
        setIntegral_congr_fun measurableSet_Icc (fun s hs => (hR s hs).symm)

end EinsteinRelation.Correctors
