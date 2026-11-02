import EinsteinFull.Calculus.C8PhysicalTransposeMeasurability
import EinsteinFull.Calculus.C3PhysicalTransposeSemigroupGraph
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
/-- The physical evolution action is jointly measurable in environment, time and data. -/
theorem physical_evolution_action_jointly_measurable
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (K : ℝ)
    (P : Ω → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hPc : ∀ ω f, Continuous (fun t : ℝ≥0 => P ω t f))
    (hPn : ∀ ω t, ‖P ω t‖ ≤ Real.exp (K*(t : ℝ))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    (∀ t f, Measurable (fun ω => P ω t f)) →
    Measurable (fun p : Ω × (ℝ≥0 × Lp ℂ 2 (volume : Measure (Vec d))) =>
      P p.1 p.2.1 p.2.2) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  intro hPm
  have htime (f : Lp ℂ 2 (volume : Measure (Vec d))) :
      Measurable (fun p : ℝ≥0 × Ω => P p.2 p.1 f) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => hPc ω f) (fun t => hPm t f)
  have hdata : Measurable
      (fun p : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × Ω) =>
        P p.2.2 p.2.1 p.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun p : ℝ≥0 × Ω =>
        ((P p.2 p.1).lipschitzWith_of_opNorm_le
          (K := ⟨Real.exp (K * (p.1 : ℝ)), (Real.exp_pos _).le⟩)
          (hPn p.2 p.1)).continuous) htime
  exact hdata.comp (measurable_snd.snd.prodMk
    (measurable_snd.fst.prodMk measurable_fst))
end EinsteinFull.Blueprint
