import EinsteinRelation.External.AKMCorrectorOscillation
import Mathlib.Order.Filter.AtTopBot.Prod

/-! Source: `paper/main.tex:722,756`. Separate endpoint errors preserve
the independent two-cutoff local L² limit. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A cofinal change of the two cutoff indices preserves the selected
limit when each endpoint contributes an error vanishing in local L². -/
theorem local_L2_limit_of_independent_endpoint_errors
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (U V : ℕ → ℕ → X → ℝ) (g : X → ℝ)
    (E F : ℕ → X → ℝ) (a b : ℕ → ℕ)
    (ha : Tendsto a atTop atTop) (hb : Tendsto b atTop atTop)
    (hU : ∀ m n, MemLp (U m n) 2 μ) (hg : MemLp g 2 μ)
    (hE : ∀ m, MemLp (E m) 2 μ) (hF : ∀ n, MemLp (F n) 2 μ)
    (hV : ∀ m n, V m n =ᵐ[μ] fun x => U (a m) (b n) x + E m x + F n x)
    (hlim : Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => U mn.1 mn.2 x - g x) 2 μ) atTop (𝓝 0))
    (hElim : Tendsto (fun m => eLpNorm (E m) 2 μ) atTop (𝓝 0))
    (hFlim : Tendsto (fun n => eLpNorm (F n) 2 μ) atTop (𝓝 0)) :
    (∀ m n, MemLp (V m n) 2 μ) ∧
    Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => V mn.1 mn.2 x - g x) 2 μ) atTop (𝓝 0) := by
  have hab : Tendsto (Prod.map a b) atTop atTop := by
    simpa only [prod_atTop_atTop_eq] using ha.prodMap hb
  have hUl := hlim.comp hab
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hEl := hElim.comp hfst
  have hFl := hFlim.comp hsnd
  refine ⟨fun m n => (memLp_congr_ae (hV m n)).mpr (((hU (a m) (b n)).add (hE m)).add (hF n)), ?_⟩
  have hupper : Tendsto (fun mn : ℕ × ℕ =>
      eLpNorm (fun x => U (a mn.1) (b mn.2) x - g x) 2 μ +
        eLpNorm (E mn.1) 2 μ + eLpNorm (F mn.2) 2 μ) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, Prod.map_fst, Prod.map_snd, zero_add] using
      (hUl.add hEl).add hFl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (g := fun _ : ℕ × ℕ => (0 : ℝ≥0∞)) tendsto_const_nhds hupper
    (fun _ => zero_le _) ?_
  intro mn
  change eLpNorm (fun x => V mn.1 mn.2 x - g x) 2 μ ≤
    eLpNorm (fun x => U (a mn.1) (b mn.2) x - g x) 2 μ +
      eLpNorm (E mn.1) 2 μ + eLpNorm (F mn.2) 2 μ
  have heq : (fun x => V mn.1 mn.2 x - g x) =ᵐ[μ]
      fun x => (U (a mn.1) (b mn.2) x - g x) + E mn.1 x + F mn.2 x := by
    filter_upwards [hV mn.1 mn.2] with x hx
    rw [hx]
    ring
  rw [eLpNorm_congr_ae heq]
  exact (eLpNorm_add_le (((hU (a mn.1) (b mn.2)).sub hg).add (hE mn.1)).aestronglyMeasurable
    (hF mn.2).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
      (add_le_add (eLpNorm_add_le ((hU (a mn.1) (b mn.2)).sub hg).aestronglyMeasurable
        (hE mn.1).aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) le_rfl)

end EinsteinRelation.Correctors
