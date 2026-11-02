import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.Environment.EuclideanLipschitz
import Mathlib.MeasureTheory.Function.L2Space

/-! # Zero oscillations force a zero weak gradient

Source: `paper/main.tex:693-698,727-729`. Every compactly supported test
fits inside a ball on which the potential is almost everywhere constant.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A vanishing centered second moment identifies the scalar function. -/
theorem ae_eq_average_of_zero_centered_square {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (u : A → ℝ) (hu : MemLp u 2 μ)
    (hz : (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) = 0) :
    u =ᵐ[μ] fun _ => ⨍ y, u y ∂μ := by
  have hi := (hu.sub (memLp_const (⨍ y, u y ∂μ))).integrable_sq
  have hzero : (∫ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) = 0 := by
    rw [← measure_smul_average μ, hz, smul_zero]
  have he := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all μ fun x => sq_nonneg (u x - ⨍ y, u y ∂μ)) hi).mp hzero
  filter_upwards [he] with x hx
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp hx)

/-- Vanishing centered oscillations on all large balls annihilate a weak gradient. -/
theorem weakGradient_zero_of_large_ball_zero_oscillation {d : ℕ}
    (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hweak : HasWeakGradient Set.univ u g)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (X : ℝ) (hX : 0 < X)
    (hzero : ∀ r : ℝ, X ≤ r →
      (⨍ x in ball 0 r, (u x - ⨍ y in ball 0 r, u y ∂volume)^2 ∂volume) = 0) :
    g =ᵐ[volume] (fun _ => 0) := by
  have hi : ∀ i : Fin d, (fun x => g x i) =ᵐ[volume] (fun _ => 0) := by
    intro i
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (by simpa only [locallyIntegrableOn_univ] using (hweak i).2.1)
    intro ψ hψ hψc
    obtain ⟨B, hBpos, hB⟩ := hψc.isCompact.isBounded.exists_pos_norm_le
    let R := max X (((d : ℝ) + 1) * (B + 1))
    have hXR : X ≤ R := le_max_left _ _
    have hR : 0 < R := hX.trans_le hXR
    have hsupport : tsupport ψ ⊆ ball (0 : Vec d) R := by
      intro x hx
      change euclideanNorm (x - 0) < R
      rw [sub_zero]
      exact ((euclideanNorm_le_dimension_mul_norm x).trans_lt
        (mul_lt_mul_of_pos_left ((hB x hx).trans_lt (lt_add_one B)) (by positivity))).trans_le
        (le_max_right _ _)
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
      simpa using (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2⟩
    let c := ⨍ y in ball 0 R, u y ∂volume
    have heq : u =ᵐ[volume.restrict (ball 0 R)] fun _ => c :=
      ae_eq_average_of_zero_centered_square _ u (hu R hR) (hzero R hXR)
    have hw := ((hweak i).restrict_subset (Set.subset_univ _) MeasurableSet.univ).congr_ae
      heq Filter.EventuallyEq.rfl
    have hc : HasWeakPartialDerivative Set.univ i (fun _ : Vec d => c) (fun _ => 0) := by
      have hd : coordinateDerivative i (fun _ : Vec d => c) = (fun _ => 0) := by
        funext x
        simp [coordinateDerivative]
      rw [← hd]
      exact hasWeakPartialDerivative_of_contDiff i (fun _ : Vec d => c) contDiff_const
    have htest : IsSpatialTest (ball 0 R) ψ := ⟨hψ, hψc, hsupport⟩
    have he := hw.2.2 ψ htest
    rw [((hc.restrict_subset (Set.subset_univ _) MeasurableSet.univ).2.2 ψ htest)] at he
    have hz : (∫ x in ball 0 R, g x i * ψ x) = 0 := by
      simpa using (neg_inj.mp he).symm
    have hfull : (∫ x in ball 0 R, g x i * ψ x) = ∫ x, g x i * ψ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      simp only [(notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hsupport ht))).self_of_nhds,
        Pi.zero_apply, mul_zero]
    simpa only [hfull, smul_eq_mul, mul_comm] using hz
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact funext hx

end EinsteinRelation.Correctors
