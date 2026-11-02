import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.Correctors.HorizontalGeneratorsIbP

/-! # Extending the divergence identity from the horizontal core

Source: `paper/main.tex:245–249,916–928`. The existing simultaneous
H¹ core approximation extends the L² divergence pairing to every test
in the full generator-domain definition.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:245–249,916–928`. An L² divergence identity
on the bounded orbit-smooth core extends to all strong generator tests. -/
theorem weakHorizontalDivergence_of_core {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {W : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hW : ∀ i, MemLp (fun ω => W ω i) 2 Q) (hh : MemLp h 2 Q)
    (hcore : ∀ F : FieldPair d → ℝ, IsHorizontalTest F →
      (∫ ω, ∑ i, W ω i * horizontalDerivative i F ω ∂Q) =
        -(∫ ω, h ω * F ω ∂Q)) :
    HasWeakHorizontalDivergence Q hQ W h := by
  refine ⟨fun i => (hW i).integrable one_le_two, hh.integrable one_le_two, ?_⟩
  intro F _hF DF hDF
  let D : FieldPair d → Vec d := fun ω i => DF i ω
  have hDm : Measurable D := Measurable.of_eval fun i =>
    (Lp.stronglyMeasurable (DF i)).measurable
  have hFweak : HasWeakHorizontalGradient Q hQ F D := by
    refine ⟨(Lp.memLp F).integrable one_le_two,
      fun i => (Lp.memLp (DF i)).integrable one_le_two, ?_⟩
    intro i H DH _hH hDH
    have hp := horizontalGenerators_integration_by_parts Q hQ i H DH F (DF i) hDH (hDF i)
    simpa only [mul_comm] using hp.2.2
  haveI : Fact ((1 : ENNReal) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨T, G, hT, _hGm, hTG, hTF, hTFc, hGD, hGDc⟩ :=
    Entropy.exists_test_approximation hQ (q := 2) ENNReal.ofNat_ne_top hFweak
      (Lp.memLp F) (fun i => Lp.memLp (DF i)) (Lp.stronglyMeasurable F).measurable hDm
  have hT2 (n : ℕ) : MemLp (T n) 2 Q :=
    Entropy.memLp_of_sub_add (hTF n) (Lp.memLp F)
  have hG2 (n : ℕ) (i : Fin d) : MemLp (fun ω => G n ω i) 2 Q :=
    Entropy.memLp_of_sub_add (hGD n i) (Lp.memLp (DF i))
  have heq (n : ℕ) :
      (∑ i, ∫ ω, W ω i * G n ω i ∂Q) = -(∫ ω, h ω * T n ω ∂Q) := by
    rw [← integral_finset_sum Finset.univ (f := fun i ω => W ω i * G n ω i)
      (fun i _ => (hW i).integrable_mul (hG2 n i))]
    calc
      _ = ∫ ω, ∑ i, W ω i * horizontalDerivative i (T n) ω ∂Q := by
        apply integral_congr_ae
        filter_upwards [hTG n] with ω hω
        simp only [hω]
      _ = _ := hcore (T n) (hT n)
  have hleft : Tendsto (fun n => ∑ i, ∫ ω, W ω i * G n ω i ∂Q) atTop
      (𝓝 (∑ i, ∫ ω, W ω i * DF i ω ∂Q)) :=
    tendsto_finset_sum _ fun i _ =>
      Entropy.tendsto_integral_mul_of_eLpNorm_two (hW i) (fun n => hG2 n i)
        (Lp.memLp (DF i)) (hGDc i)
  have hright : Tendsto (fun n => -(∫ ω, h ω * T n ω ∂Q)) atTop
      (𝓝 (-(∫ ω, h ω * F ω ∂Q))) :=
    (Entropy.tendsto_integral_mul_of_eLpNorm_two hh hT2 (Lp.memLp F) hTFc).neg
  rw [integral_finset_sum Finset.univ (f := fun i ω => W ω i * DF i ω)
    (fun i _ => (hW i).integrable_mul (Lp.memLp (DF i)))]
  exact tendsto_nhds_unique (hleft.congr heq) hright

end EinsteinRelation.Correctors
