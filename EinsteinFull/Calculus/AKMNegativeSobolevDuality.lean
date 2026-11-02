import EinsteinFull.External.Source.AKMNegativeSobolev
import EinsteinRelation.External.AKMEnergyDensity

/-! Duality consequences of the actual normalized compact-test supremum.
These proofs use no stochastic or PDE input. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.External.Source.AKM
open EinsteinRelation EinsteinRelation.External.AKM

/-- A bound on the extended dual norm is exactly a bound on all normalized
smooth compactly supported tests. No real conversion of the supremum occurs. -/
theorem negativeIntegerSobolevNorm_le_iff {d m : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {c : ℝ≥0∞} :
    negativeIntegerSobolevNorm m U f ≤ c ↔
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ → integerSobolevTestNorm m U ψ ≤ 1 →
        ENNReal.ofReal |⨍ x in U, f x * ψ x ∂volume| ≤ c := by
  constructor
  · intro h ψ hψ hn
    exact (le_iSup_of_le ⟨ψ, hψ, hn⟩ le_rfl).trans h
  · intro h
    exact iSup_le fun ψ => h ψ.1 ψ.2.1 ψ.2.2

/-- Each coordinate test may be chosen separately. Summing the actual
normalized pairings is bounded by the component-sum vector dual norm. -/
theorem normalized_vector_test_pairing_le {d m : ℕ} {U : Set (Vec d)}
    (F : Vec d → Vec d) (ψ : Fin d → Vec d → ℝ)
    (hψ : ∀ j, IsSpatialTest U (ψ j))
    (hn : ∀ j, integerSobolevTestNorm m U (ψ j) ≤ 1) :
    ENNReal.ofReal (∑ j : Fin d, |⨍ x in U, F x j * ψ j x ∂volume|) ≤
      vectorNegativeIntegerSobolevNorm m U F := by
  rw [ENNReal.ofReal_sum_of_nonneg fun j _ => abs_nonneg _]
  exact Finset.sum_le_sum fun j _ =>
    negativeIntegerSobolevNorm_le_iff.mp le_rfl (ψ j) (hψ j) (hn j)

/-- One majorant for the gradient and centered flux controls both families
of compact tests on the same sample. Taking the positive part of the real
majorant is necessary even if its extended norm vanishes. -/
theorem normalized_two_field_pairing_le {d m : ℕ} {U : Set (Vec d)}
    (F G : Vec d → Vec d) {z : ℝ}
    (hz : vectorNegativeIntegerSobolevNorm m U F +
      vectorNegativeIntegerSobolevNorm m U G ≤ ENNReal.ofReal z)
    (ψ χ : Fin d → Vec d → ℝ)
    (hψ : ∀ j, IsSpatialTest U (ψ j))
    (hnψ : ∀ j, integerSobolevTestNorm m U (ψ j) ≤ 1)
    (hχ : ∀ j, IsSpatialTest U (χ j))
    (hnχ : ∀ j, integerSobolevTestNorm m U (χ j) ≤ 1) :
    (∑ j : Fin d, |⨍ x in U, F x j * ψ j x ∂volume|) +
      (∑ j : Fin d, |⨍ x in U, G x j * χ j x ∂volume|) ≤ max z 0 := by
  apply (ENNReal.ofReal_le_ofReal_iff (le_max_right z 0)).mp
  rw [ENNReal.ofReal_add (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
  exact (add_le_add (normalized_vector_test_pairing_le F ψ hψ hnψ)
    (normalized_vector_test_pairing_le G χ hχ hnχ)).trans
      (hz.trans (ENNReal.ofReal_le_ofReal (le_max_left z 0)))

/-- The source `O_1(θ)` majorant gives a quantitative second-moment bound
for every pair of normalized compact-test families. No measurability of an
extended supremum or conversion of an infinite norm is required. -/
theorem two_field_pairing_second_moment_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {d m : ℕ} {U : Set (Vec d)}
    (F G : Ω → Vec d → Vec d) {Z : Ω → ℝ} {θ : ℝ}
    (hZ : OsBound P Z 1 θ)
    (hz : ∀ᵐ ω ∂P, vectorNegativeIntegerSobolevNorm m U (F ω) +
      vectorNegativeIntegerSobolevNorm m U (G ω) ≤ ENNReal.ofReal (Z ω))
    (ψ χ : Fin d → Vec d → ℝ)
    (hψ : ∀ j, IsSpatialTest U (ψ j))
    (hnψ : ∀ j, integerSobolevTestNorm m U (ψ j) ≤ 1)
    (hχ : ∀ j, IsSpatialTest U (χ j))
    (hnχ : ∀ j, integerSobolevTestNorm m U (χ j) ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal
      (((∑ j : Fin d, |⨍ x in U, F ω x j * ψ j x ∂volume|) +
        (∑ j : Fin d, |⨍ x in U, G ω x j * χ j x ∂volume|)) ^ 2) ∂P) ≤
      ENNReal.ofReal (8 * θ ^ 2) := by
  have hm := hZ.moment_pos_le (show (0 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at hm
  have hmono :
      (∫⁻ ω, ENNReal.ofReal
        (((∑ j : Fin d, |⨍ x in U, F ω x j * ψ j x ∂volume|) +
          (∑ j : Fin d, |⨍ x in U, G ω x j * χ j x ∂volume|)) ^ 2) ∂P) ≤
        ∫⁻ ω, ENNReal.ofReal ((max (Z ω) 0) ^ 2) ∂P := by
    apply lintegral_mono_ae
    filter_upwards [hz] with ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
      (add_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.sum_nonneg fun _ _ => abs_nonneg _))
      (normalized_two_field_pairing_le (F ω) (G ω) hω ψ χ hψ hnψ hχ hnχ) 2)
  exact hmono.trans (by
    simpa only [show 2 * θ ^ 2 * (2 : ℝ) ^ 2 = 8 * θ ^ 2 by ring] using hm)

end EinsteinFull.External.Source.AKM
