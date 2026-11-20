import EinsteinFull.Homogenization.SourceResponseColoring
import EinsteinRelation.Probability.ColoredHoeffding

/-!
# Concentration of response averages

Finite-range independence and the uniform response bound yield moment bounds
for sums of centered response energies on same-scale triadic cubes. This is an
elementary fluctuation estimate for the Chapter 2 response in Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open EinsteinRelation.Clock

/-- The expectation of a response satisfies the same bounds as the response. -/
theorem expected_sourceResponseJ_cube_bounds {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    0 ≤ (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) ∧
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) ≤
      (K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q := by
  refine ⟨integral_nonneg (fun a => (sourceResponseJ_cube_bounds hK a Q k hk p q).1), ?_⟩
  have h := integral_mono_ae (integrable_sourceResponseJ_cube hK P Q k hk p q)
    (integrable_const ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q))
    (ae_of_all P fun a => (sourceResponseJ_cube_bounds hK a Q k hk p q).2)
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- The centered sum of responses over distinct same-scale cubes satisfies a
finite-range Hoeffding moment bound. -/
theorem eLpNorm_sum_centered_sourceResponseJ_le {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (Q : ι → TriadicCube d) (n : ℕ) (hscale : ∀ i, (Q i).scale = n)
    (hinj : Function.Injective fun i => (Q i).index)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) (m : ℝ) (hm : 1 ≤ m) :
    eLpNorm (fun a => ∑ i, (Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) p q -
      ∫ b, Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn b (Book.Ch02.cubeDomain (Q i)) k hk) p q ∂P))
      (ENNReal.ofReal m) P ≤
      ENNReal.ofReal ((Fintype.card (Fin d → ZMod 3) : ℝ) *
        EinsteinRelation.Probability.hoeffdingMomentConst m ^ (1 / m) *
        ((Fintype.card ι : ℝ) *
          ((K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q) ^ 2) ^
          (1 / 2 : ℝ)) := by
  classical
  let X : ι → Coefficient d K → ℝ := fun i a =>
    Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) p q
  let B : ℝ := (K / 2) * EinsteinRelation.euclideanSq (-p) + vecNormSq q - vecDot p q
  let col : ι → Fin (Fintype.card (Fin d → ZMod 3)) := fun i =>
    Fintype.equivFin (Fin d → ZMod 3) (heatCubeColour 3 (Q i).index)
  have hmeas : ∀ i, Measurable (fun a => X i a - ∫ b, X i b ∂P) := by
    intro i
    exact ((measurable_sourceResponseJ_cube (Q i) k hk p q).mono
      (coefficientLocalSigma_le_coefficientSigma _) le_rfl).sub measurable_const
  have hbound : ∀ i, ∀ᵐ a ∂P, |X i a - ∫ b, X i b ∂P| ≤ B := by
    intro i
    have hmean := expected_sourceResponseJ_cube_bounds hK P (Q i) k hk p q
    filter_upwards [] with a
    have hx := sourceResponseJ_cube_bounds hK a (Q i) k hk p q
    change 0 ≤ X i a ∧ X i a ≤ B at hx
    change 0 ≤ (∫ b, X i b ∂P) ∧ (∫ b, X i b ∂P) ≤ B at hmean
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hmean : ∀ i, ∫ a, (X i a - ∫ b, X i b ∂P) ∂P = 0 := by
    intro i
    rw [integral_sub (integrable_sourceResponseJ_cube hK P (Q i) k hk p q)
      (integrable_const _), integral_const, probReal_univ, one_smul, sub_self]
  have hindep : ∀ c (s : Finset ι), (∀ i ∈ s, col i = c) →
      ProbabilityTheory.iIndepFun (fun i : s => fun a => X i a - ∫ b, X i b ∂P) P := by
    intro c s hs
    let c' := (Fintype.equivFin (Fin d → ZMod 3)).symm c
    let f : s → {i : ι // heatCubeColour 3 (Q i).index = c'} := fun i =>
      ⟨i, (Fintype.equivFin (Fin d → ZMod 3)).injective (by
        change col i = (Fintype.equivFin (Fin d → ZMod 3)) c'
        simpa only [c', Equiv.apply_symm_apply] using hs i i.property)⟩
    have hf : Function.Injective f := by
      intro i j h
      have he : (f i).val = (f j).val := congrArg Subtype.val h
      exact Subtype.ext he
    have h := (iIndepFun_sourceResponseJ_colour P hP Q n hscale hinj k hk
      (fun _ => p) (fun _ => q) c').precomp hf
    exact h.comp (fun i t => t - ∫ b, X i b ∂P) (fun _ => measurable_id.sub_const _)
  have h := EinsteinRelation.Probability.eLpNorm_tsum_le_colored (μ := P) col
    (fun i a => X i a - ∫ b, X i b ∂P) hmeas (fun _ => B) hindep hbound hmean
    Summable.of_finite (fun _ => Summable.of_finite) m hm
  simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, X, B] using h

end EinsteinFull.Homogenization
