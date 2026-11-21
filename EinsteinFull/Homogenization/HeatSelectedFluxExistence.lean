import EinsteinFull.Homogenization.HeatFormulaLargeTime
import EinsteinFull.Homogenization.LocalL2Limit
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Existence of the heat-selected flux gradient

Let `g` be a vector field whose components are locally square integrable, have Gaussian moments,
and whose Hessian heat convolutions decay like `t^(-1-κ)` at large times on the parabolic region.
Then the truncations of the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, converge in `L²` on every ball as both time
cutoffs are removed, and the explicitly selected limit is a heat-selected flux gradient in the
sense of `IsHeatSelectedFluxGradient`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

variable {d : ℕ}

/-- The hypotheses under which the heat formula (6.7) selects a flux gradient. -/
structure HeatFormulaHypotheses (g : Vec d → Vec d) : Prop where
  measurable : ∀ k, Measurable (fun y => g y k)
  memLp_ball : ∀ k (R : ℝ), MemLp (fun y => g y k) 2 (volume.restrict (ball 0 R))
  moments : ∀ k, HasGaussianMoments (fun y => g y k)
  decay : ∀ k a b, HasHeatHessianDecay (fun y => g y k) a b

theorem natCast_succ_inv_le_natCast_succ (m n : ℕ) : ((m + 1 : ℕ) : ℝ)⁻¹ ≤ ((n + 1 : ℕ) : ℝ) :=
  (natCast_succ_inv_le_one m).trans (one_le_natCast_succ n)

/-- The selected heat gradient: the `L²_loc` limit of the diagonal truncations of (6.7). -/
noncomputable def heatSelectedGradient (g : Vec d → Vec d) (j k : Fin d) (x : Vec d) : Vec d :=
  fun l => locL2Limit (fun p x => iteratedAKMHeatGradientTruncation g p p j k l x) x

namespace HeatFormulaHypotheses

variable {g : Vec d → Vec d} (hg : HeatFormulaHypotheses g)
include hg

theorem spaceIntegral_eq {t : ℝ} (ht : 0 < t) (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral g t j k l x =
      heatHessianConv t j l (fun y => g y k) x - heatHessianConv t k l (fun y => g y j) x := by
  unfold akmHeatGradientSpaceIntegral heatHessianConv
  simp_rw [akmHeatGradientDensity_eq_mixedHessian g t ht j k l x]
  rw [← integral_sub ((hg.moments k).integrable_heatHessian_mul ht j l (hg.measurable k) x)
    ((hg.moments j).integrable_heatHessian_mul ht k l (hg.measurable j) x)]
  congr 1
  funext y
  ring

theorem integrable_density {t : ℝ} (ht : 0 < t) (j k l : Fin d) (x : Vec d) :
    Integrable (fun y => akmHeatGradientDensity g t j k l x y) volume := by
  simp_rw [akmHeatGradientDensity_eq_mixedHessian g t ht j k l x]
  refine (((hg.moments k).integrable_heatHessian_mul ht j l (hg.measurable k) x).sub
    ((hg.moments j).integrable_heatHessian_mul ht k l (hg.measurable j) x)).congr
    (Filter.Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply]
  ring

theorem truncation_eq (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n j k l x =
      heatHessianTruncation m n j l (fun y => g y k) x -
        heatHessianTruncation m n k l (fun y => g y j) x := by
  unfold iteratedAKMHeatGradientTruncation heatHessianTruncation heatHessianWindow
    iteratedHeatTimeWindow
  rw [← integral_sub ((hg.moments k).integrableOn_heatHessianConv (natCast_succ_inv_pos m) j l
    (hg.measurable k) x) ((hg.moments j).integrableOn_heatHessianConv (natCast_succ_inv_pos m)
      k l (hg.measurable j) x)]
  exact setIntegral_congr_fun measurableSet_Icc fun t ht =>
    hg.spaceIntegral_eq (lt_of_lt_of_le (natCast_succ_inv_pos m) ht.1) j k l x

theorem integrableOn_spaceIntegral (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    Integrable (fun t => akmHeatGradientSpaceIntegral g t j k l x)
      (volume.restrict (Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) := by
  refine (((hg.moments k).integrableOn_heatHessianConv (natCast_succ_inv_pos m) j l
    (hg.measurable k) x).sub ((hg.moments j).integrableOn_heatHessianConv
      (natCast_succ_inv_pos m) k l (hg.measurable j) x)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact (hg.spaceIntegral_eq (lt_of_lt_of_le (natCast_succ_inv_pos m) ht.1) j k l x).symm

theorem measurable_truncation (m n : ℕ) (j k l : Fin d) :
    Measurable (fun x => iteratedAKMHeatGradientTruncation g m n j k l x) := by
  have h : (fun x => iteratedAKMHeatGradientTruncation g m n j k l x) =
      fun x => heatHessianTruncation m n j l (fun y => g y k) x -
        heatHessianTruncation m n k l (fun y => g y j) x :=
    funext (hg.truncation_eq m n j k l)
  rw [h]
  exact ((stronglyMeasurable_heatHessianWindow (natCast_succ_inv_pos m) j l
    (hg.measurable k)).measurable).sub
    ((stronglyMeasurable_heatHessianWindow (natCast_succ_inv_pos m) k l
      (hg.measurable j)).measurable)

theorem memLp_truncation (m n : ℕ) (j k l : Fin d) (ρ : ℝ) :
    MemLp (fun x => iteratedAKMHeatGradientTruncation g m n j k l x) 2
      (volume.restrict (ball 0 ρ)) := by
  have h : (fun x => iteratedAKMHeatGradientTruncation g m n j k l x) =
      fun x => heatHessianTruncation m n j l (fun y => g y k) x -
        heatHessianTruncation m n k l (fun y => g y j) x :=
    funext (hg.truncation_eq m n j k l)
  rw [h]
  exact ((hg.moments k).memLp_heatHessianWindow (natCast_succ_inv_pos m)
    (natCast_succ_inv_le_natCast_succ m n) j l (hg.measurable k) ρ).sub
      ((hg.moments j).memLp_heatHessianWindow (natCast_succ_inv_pos m)
        (natCast_succ_inv_le_natCast_succ m n) k l (hg.measurable j) ρ)

/-- **Joint Cauchy property** of the truncations of (6.7) on balls. -/
theorem exists_eLpNorm_truncation_sub_le (j k l : Fin d) (ρ : ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ m n m' n' : ℕ, N ≤ m → N ≤ n → N ≤ m' → N ≤ n' →
      eLpNorm (fun x => iteratedAKMHeatGradientTruncation g m n j k l x -
        iteratedAKMHeatGradientTruncation g m' n' j k l x) 2 (volume.restrict (ball 0 ρ)) ≤ δ := by
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨N₁, h₁⟩ := exists_eLpNorm_heatHessianTruncation_sub_le (hg.measurable k)
    (hg.memLp_ball k) (hg.moments k) (hg.decay k j l) ρ hδ2
  obtain ⟨N₂, h₂⟩ := exists_eLpNorm_heatHessianTruncation_sub_le (hg.measurable j)
    (hg.memLp_ball j) (hg.moments j) (hg.decay j k l) ρ hδ2
  refine ⟨max N₁ N₂, fun m n m' n' hm hn hm' hn' => ?_⟩
  have hsplit : (fun x => iteratedAKMHeatGradientTruncation g m n j k l x -
      iteratedAKMHeatGradientTruncation g m' n' j k l x) =
      (fun x => heatHessianTruncation m n j l (fun y => g y k) x -
        heatHessianTruncation m' n' j l (fun y => g y k) x) -
      (fun x => heatHessianTruncation m n k l (fun y => g y j) x -
        heatHessianTruncation m' n' k l (fun y => g y j) x) := by
    funext x
    simp only [Pi.sub_apply, hg.truncation_eq]
    ring
  rw [hsplit]
  refine (eLpNorm_sub_le (by norm_num)).trans ?_
  calc _ ≤ δ / 2 + δ / 2 := add_le_add
        (h₁ m n m' n' ((le_max_left _ _).trans hm) ((le_max_left _ _).trans hn)
          ((le_max_left _ _).trans hm') ((le_max_left _ _).trans hn'))
        (h₂ m n m' n' ((le_max_right _ _).trans hm) ((le_max_right _ _).trans hn)
          ((le_max_right _ _).trans hm') ((le_max_right _ _).trans hn'))
    _ = δ := ENNReal.add_halves δ

theorem isLocL2Cauchy_diagonal (j k l : Fin d) :
    IsLocL2Cauchy (fun p x => iteratedAKMHeatGradientTruncation g p p j k l x) := by
  intro ρ δ hδ
  obtain ⟨N, hN⟩ := hg.exists_eLpNorm_truncation_sub_le j k l ρ hδ
  exact ⟨N, fun p q hp hq => hN p p q q hp hp hq hq⟩

theorem tendsto_eLpNorm_diagonal (j k l : Fin d) (ρ : ℝ) :
    Tendsto (fun p => eLpNorm (fun x => iteratedAKMHeatGradientTruncation g p p j k l x -
      heatSelectedGradient g j k x l) 2 (volume.restrict (ball 0 ρ))) atTop (𝓝 0) :=
  (hg.isLocL2Cauchy_diagonal j k l).tendsto_eLpNorm
    (fun p => hg.measurable_truncation p p j k l) ρ

theorem measurable_heatSelectedGradient (j k l : Fin d) :
    Measurable (fun x => heatSelectedGradient g j k x l) :=
  measurable_locL2Limit fun p => hg.measurable_truncation p p j k l

theorem memLp_heatSelectedGradient (j k l : Fin d) (ρ : ℝ) :
    MemLp (fun x => heatSelectedGradient g j k x l) 2 (volume.restrict (ball 0 ρ)) := by
  obtain ⟨p, hp⟩ := eventually_atTop.mp
    ((ENNReal.tendsto_nhds_zero.mp (hg.tendsto_eLpNorm_diagonal j k l ρ)) 1 one_pos)
  have hdiff : MemLp (fun x => iteratedAKMHeatGradientTruncation g p p j k l x -
      heatSelectedGradient g j k x l) 2 (volume.restrict (ball 0 ρ)) :=
    lt_of_le_of_lt (hp p le_rfl) ENNReal.one_lt_top
  have h := (hg.memLp_truncation p p j k l ρ).sub hdiff
  refine h.congr_norm ?_ (Filter.Eventually.of_forall fun x => ?_) |>.mono_measure le_rfl
  · exact (hg.measurable_heatSelectedGradient j k l).aestronglyMeasurable
  · simp only [Pi.sub_apply, sub_sub_cancel]

end HeatFormulaHypotheses

/-- **Existence of the heat-selected flux gradient.** -/
theorem HeatFormulaHypotheses.isHeatSelectedFluxGradient {g : Vec d → Vec d}
    (hg : HeatFormulaHypotheses g) :
    IsHeatSelectedFluxGradient g (heatSelectedGradient g) := by
  intro j k l R
  refine ⟨fun m n => Filter.Eventually.of_forall fun x => ⟨?_, hg.integrableOn_spaceIntegral m n
    j k l x⟩, fun m n => hg.memLp_truncation m n j k l _,
    hg.memLp_heatSelectedGradient j k l _, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact hg.integrable_density (lt_of_lt_of_le (natCast_succ_inv_pos m) ht.1) j k l x
  · rw [ENNReal.tendsto_nhds_zero]
    intro δ hδ
    have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
    obtain ⟨N₁, hN₁⟩ := hg.exists_eLpNorm_truncation_sub_le j k l ((R : ℝ) + 1) hδ2
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp
      (hg.tendsto_eLpNorm_diagonal j k l ((R : ℝ) + 1))) (δ / 2) hδ2)
    refine eventually_atTop.mpr ⟨(N₁, N₁), fun mn hmn => ?_⟩
    have hm : N₁ ≤ mn.1 := hmn.1
    have hn : N₁ ≤ mn.2 := hmn.2
    set p := max N₁ N₂
    have hsplit : (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x -
        heatSelectedGradient g j k x l) =
        (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x -
          iteratedAKMHeatGradientTruncation g p p j k l x) +
        (fun x => iteratedAKMHeatGradientTruncation g p p j k l x -
          heatSelectedGradient g j k x l) := by
      funext x
      simp only [Pi.add_apply]
      ring
    rw [hsplit]
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    calc _ ≤ δ / 2 + δ / 2 := add_le_add
          (hN₁ mn.1 mn.2 p p hm hn (le_max_left _ _) (le_max_left _ _))
          (hN₂ p (le_max_right _ _))
      _ = δ := ENNReal.add_halves δ

end EinsteinFull.Homogenization
