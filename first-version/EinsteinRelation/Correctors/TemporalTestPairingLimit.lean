import EinsteinRelation.Correctors.TemporalScalarAverageLimit
import EinsteinRelation.Correctors.CompactTestPairingContinuity
import EinsteinRelation.Correctors.ParabolicTemporalWeakGradient

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Actual temporal averaging commutes with a compact spatial test pairing.
Source: `paper/main.tex:798–806`. -/
theorem temporal_average_test_pairing_eq {d : ℕ} {a b : ℝ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] {u : ℝ × Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ U)))
    {ρ : ℝ → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ x in U, (∫ s in Set.Ioo a b, ρ s * u (s,x)) * ψ x) =
      ∫ s in Set.Ioo a b, ρ s * (∫ x in U, u (s,x) * ψ x) := by
  let μ := volume.restrict (Set.Ioo a b)
  let ν := volume.restrict U
  have hp : volume.restrict (Set.Ioo a b ×ˢ U) = μ.prod ν := by
    simp only [μ,ν,Measure.volume_eq_prod,Measure.prod_restrict]
  haveI : IsFiniteMeasure (volume.restrict (Set.Ioo a b ×ˢ U)) := by
    rw [hp]
    infer_instance
  obtain ⟨C,hC⟩ := hρc.exists_bound_of_continuous hρ
  obtain ⟨D,hD⟩ := hψ.2.1.exists_bound_of_continuous hψ.1.continuous
  have hi : Integrable (fun z : ℝ × Vec d => (ρ z.1 * u z) * ψ z.2) (μ.prod ν) := by
    rw [← hp]
    have hu1 := hu.integrable (by norm_num)
    have hr := hu1.mul_bdd ((hρ.measurable.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => hC z.1)
    have hs := hr.mul_bdd ((hψ.1.continuous.measurable.comp measurable_snd).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => hD z.2)
    simpa only [Function.comp_apply,mul_comm] using hs
  calc
    _ = ∫ x in U, ∫ s in Set.Ioo a b, (ρ s * u (s,x)) * ψ x := by
      simp_rw [integral_mul_const]
    _ = ∫ s in Set.Ioo a b, ∫ x in U, (ρ s * u (s,x)) * ψ x :=
      (integral_integral_swap hi).symm
    _ = _ := by
      simp_rw [mul_assoc,integral_const_mul]

/-- One-sided temporal regularization recovers all actual compact spatial
pairings at the prescribed endpoint. Source: `paper/main.tex:798–806`. -/
theorem temporal_test_pairing_tendsto {d : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] {u : ℝ × Vec d → ℝ}
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    (huL : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ U)))
    {ρ : ℕ → ℝ → ℝ} (hρ : ∀ k, Continuous (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k s, 0 ≤ ρ k s) (hρ1 : ∀ k, (∫ s, ρ k s) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hεb : ∀ k, ε k ≤ (b-a)/2)
    (hsupp : ∀ k, tsupport (ρ k) ⊆ Set.Ioo 0 (ε k))
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    Tendsto (fun k => ∫ x in U,
      (∫ s in Set.Ioo a b, ρ k (b-s) * u (s,x)) * ψ x)
      atTop (𝓝 (∫ x in U, u (b,x) * ψ x)) := by
  have heq t : (∫ x in U, u (t,x) * ψ x) = ∫ x, u (t,x) * ψ x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : ψ x = 0 := by
      by_contra hz
      exact hx (hψ.2.2 (subset_tsupport ψ hz))
    rw [hz,mul_zero]
  have hc : ContinuousOn (fun t => ∫ x in U, u (t,x) * ψ x) (Set.Icc a b) := by
    simp_rw [heq]
    exact (continuousOn_compact_test_pairing u hu hψ.1.continuous hψ.2.1).mono
      (fun t ht => ha.trans_le ht.1)
  have ht := tendsto_one_sided_interval_average hab hc hρ0 hρ1 hε hεb hsupp
  have havg k : (∫ x in U, (∫ s in Set.Ioo a b, ρ k (b-s) * u (s,x)) * ψ x) =
      ∫ s in Set.Ioo a b, ρ k (b-s) * (∫ x in U, u (s,x) * ψ x) :=
    temporal_average_test_pairing_eq huL
      ((hρ k).comp (continuous_const.sub continuous_id))
      ((hρc k).comp_homeomorph (Homeomorph.subLeft b)) hψ
  simpa only [havg] using ht

end EinsteinRelation.Correctors
