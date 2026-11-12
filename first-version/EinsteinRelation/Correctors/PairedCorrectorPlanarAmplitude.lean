import EinsteinRelation.Correctors.PairedPDESkewAmplitude
import EinsteinRelation.Correctors.PairedPDEPlanarContinuity
import EinsteinRelation.Correctors.PlanarCenteredSkewNorm

/-! # Joint scalar and skew estimates for paired planar correctors

Source: `paper/main.tex:869–875`. Both centered quantities are estimated
by the same ordinary paired energy. The independent skew entry is converted
to the full Frobenius norm, and the constant precedes every radius and field.
Continuous point representatives are explicit; weak identities alone do not
identify prescribed point values.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

private theorem memLp_vector_of_euclideanNorm {U : Set (Vec 2)}
    {u : Vec 2 → ℝ} {G : Vec 2 → Vec 2} (hg : HasWeakGradient U u G)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U)) :
    MemLp G 2 (volume.restrict U) := by
  have hm : AEStronglyMeasurable G (volume.restrict U) :=
    (aemeasurable_pi_lambda _ fun j =>
      (hg j).2.1.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  apply hG.of_le hm
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (show 0 ≤ euclideanNorm (G x) from Real.sqrt_nonneg _)]
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  change (G x j)^2 ≤ ∑ k : Fin 2, G x k * G x k
  rw [sq]
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)

/-- The actual difference of two scalar correctors and two skew correctors
has one joint centered-amplitude estimate. Coefficient continuity discharges
the measurability of the dual coefficient, and subtraction discharges its
homogeneous equation. Source: `paper/main.tex:869–875`. -/
theorem paired_planar_centered_correctors_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (a₁ a₂ : Vec 2 → Mat 2) (e m : Vec 2)
        (φ₁ φ₂ : Vec 2 → ℝ) (G₁ G₂ : Vec 2 → Vec 2)
        (S₁ S₂ : Vec 2 → Mat 2),
        IsElliptic L a₁ → Continuous a₁ →
        Set.EqOn a₁ a₂ (ball 0 (2*R)) →
        MemLp φ₁ 2 (volume.restrict (ball 0 (2*R))) →
        MemLp φ₂ 2 (volume.restrict (ball 0 (2*R))) →
        MemLp (fun x => euclideanNorm (G₁ x - G₂ x)) 2
          (volume.restrict (ball 0 (2*R))) →
        HasWeakGradient (ball 0 (2*R)) φ₁ G₁ →
        HasWeakGradient (ball 0 (2*R)) φ₂ G₂ →
        HasWeakDivergence (ball 0 (2*R))
          (fun x => (a₁ x).mulVec (e + G₁ x)) (fun _ => 0) →
        HasWeakDivergence (ball 0 (2*R))
          (fun x => (a₂ x).mulVec (e + G₂ x)) (fun _ => 0) →
        (∀ x, (S₁ x).transpose = -(S₁ x)) →
        (∀ x, (S₂ x).transpose = -(S₂ x)) →
        HasWeakRowDivergence (ball 0 (2*R)) S₁
          (fun x => (a₁ x).mulVec (e + G₁ x) - m) →
        HasWeakRowDivergence (ball 0 (2*R)) S₂
          (fun x => (a₂ x).mulVec (e + G₂ x) - m) →
        MemLp (fun x => S₁ x 0 1 - S₂ x 0 1) 2 (volume.restrict (ball 0 (2*R))) →
        ContinuousOn (fun x => φ₁ x - φ₂ x) (ball 0 R) →
        ContinuousOn (fun x => S₁ x 0 1 - S₂ x 0 1) (ball 0 R) →
        ∀ w : Vec 2 → ℝ, Integrable w volume →
          Integrable (fun x => w x * (φ₁ x - φ₂ x)) volume →
          (∀ a b, Integrable (fun x => w x * (S₁ x a b - S₂ x a b)) volume) →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 → Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R,
            |(φ₁ x₀ - φ₂ x₀) - ∫ x, w x * (φ₁ x - φ₂ x)| +
              frobeniusNorm (Matrix.of (fun a b =>
                (S₁ x₀ a b - S₂ x₀ a b) - ∫ x, w x * (S₁ x a b - S₂ x a b))) ≤
              C*R * vectorRms volume (ball 0 (2*R)) (fun x => G₁ x - G₂ x) := by
  obtain ⟨Cφ, hCφ, hφ⟩ := paired_harmonic_centered_amplitude_planar_of_gt h817 hP
    (inv_pos.mpr hL) (by positivity : 0 < ((2 : ℝ)+1)*L)
  obtain ⟨CS, hCS, hS⟩ := planar_skew_centered_amplitude_of_gt h817 hP hL
  refine ⟨Cφ + Real.sqrt 2 * CS, by positivity, ?_⟩
  intro R hR a₁ a₂ e m φ₁ φ₂ G₁ G₂ S₁ S₂ ha hc heq hφ₁ hφ₂ hG
    hg₁ hg₂ hd₁ hd₂ hs₁ hs₂ hrow₁ hrow₂ hS2 hφcont hScont
    w hw hwφ hwS hw0 hw1 hws x₀ hx₀
  have hU := paired_isOpen_ball (0 : Vec 2) (2*R)
  have hpair := paired_corrector_harmonic hU heq e hg₁ hg₂ hd₁ hd₂
  have hweak : WeakSolution (ball 0 (2*R)) a₁ (fun x => φ₁ x - φ₂ x)
      (fun x => G₁ x - G₂ x) :=
    ⟨hφ₁.sub hφ₂, memLp_vector_of_euclideanNorm hpair.1 hG, hpair⟩
  have hbφ := hφ R hR a₁ _ _
    (ellipticBound_of_isElliptic hL ha (fun i j =>
      ((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable) _)
    hweak hφcont w hw hwφ hw0 hw1 hws x₀ hx₀
  have hpS := paired_planar_fluxCorrector_harmonic hU hL ha heq e m
    hg₁ hg₂ hs₁ hs₂ hrow₁ hrow₂
  have hbS := hS R hR a₁ _ _ _ ha
    (fun i j => ((continuous_apply j).comp ((continuous_apply i).comp
      (continuous_planar_dual hL ha hc))).measurable)
    hpS.1 (fun _ _ => rfl) hpS.2 hS2 hG hScont w hw (hwS 0 1) hw0 hw1 hws x₀ hx₀
  have hskew (x : Vec 2) : (S₁ x - S₂ x).transpose = -(S₁ x - S₂ x) := by
    rw [Matrix.transpose_sub, hs₁ x, hs₂ x]
    abel
  have hcenter := transpose_centered_skew volume (fun x => S₁ x - S₂ x) w x₀
    (hskew x₀) (ae_of_all _ hskew)
  have hnorm := frobeniusNorm_planar_skew _ hcenter
  change frobeniusNorm (Matrix.of (fun a b =>
    (S₁ x₀ a b - S₂ x₀ a b) - ∫ x, w x * (S₁ x a b - S₂ x a b))) = _ at hnorm
  rw [hnorm]
  change |_ - _| + Real.sqrt 2 * |(S₁ x₀ 0 1 - S₂ x₀ 0 1) -
    ∫ x, w x * (S₁ x 0 1 - S₂ x 0 1)| ≤ _
  calc
    _ ≤ Cφ*R * vectorRms volume (ball 0 (2*R)) (fun x => G₁ x - G₂ x) +
        Real.sqrt 2 * (CS*R * vectorRms volume (ball 0 (2*R)) (fun x => G₁ x - G₂ x)) :=
      add_le_add hbφ (mul_le_mul_of_nonneg_left hbS (Real.sqrt_nonneg _))
    _ = _ := by ring

end EinsteinRelation.Correctors
