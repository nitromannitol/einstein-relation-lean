import EinsteinRelation.Correctors.AKMHeatKernelBounds
import EinsteinRelation.Correctors.ParabolicGlobalCutoffEnergy
import EinsteinRelation.Correctors.ParabolicGradientMeasurability
import EinsteinRelation.Correctors.CutoffEnergyFatou
import EinsteinRelation.Correctors.PositiveTimeCutoff
import EinsteinRelation.Correctors.ParabolicTensorCutoff
import EinsteinRelation.Correctors.AKMHeatKernelConsequences
import EinsteinRelation.Correctors.PairedPDEGradientEnergyTransfer
import EinsteinRelation.Correctors.AKMHeatKernelCutoffs

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Gaussian decay and cutoff Caccioppoli give whole-space gradient energy
on every compact positive-time strip. Source: `paper/main.tex:787–792,850`;
AKM Proposition E.1, (E.7)–(E.8). -/
theorem akm_heatKernel_global_gradient_memLp {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (h : HeatKernelProperties A P X Y H C)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (y : Vec d) :
    AEStronglyMeasurable (fun z : ℝ × Vec d => X z.1 z.2 y)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) ∧
    MemLp (fun z : ℝ × Vec d => euclideanNorm (X z.1 z.2 y)) 2
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
  have hGm := parabolic_gradient_aestronglyMeasurable
    (fun R hR => (h.2.2.1 y).1 a b R ha hab hR)
  refine ⟨hGm, ?_⟩
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  obtain ⟨η, M, hη, hηc, hηs, hηb, hηone, hM, hηD⟩ := exists_positive_time_plateau ha hab
  obtain ⟨χ, B, hB, hχ, hχb, hχlim, hχD⟩ := akm_exists_scaled_cutoffs d
  have hχabs (n : ℕ) (x : Vec d) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (hχb n x).1]
    exact (hχb n x).2
  have hχDb (n : ℕ) (x : Vec d) : ‖gradient (χ n) x‖ ≤ B := by
    apply (hχD n x).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
    exact le_mul_of_one_le_right hB (by exact_mod_cast (show 1 ≤ n+1 by omega))
  let E := 2*M + 4*K^2*d*B^2
  let C := E * ∫ z in Set.Ioo (a/2) (b+a/2) ×ˢ (Set.univ : Set (Vec d)), P z.1 z.2 y ^ 2
  have he (n : ℕ) := parabolic_global_cutoff_energy hK measurableSet_Ioo measurableSet_Ioo
    (show Set.Ioo a b ⊆ Set.Ioo (a/2) (b+a/2) from fun t ht => by
      constructor <;> linarith [ht.1, ht.2])
    (fun R hR => (h.2.2.1 y).1 (a/2) (b+a/2) R (half_pos ha) (by linarith) hR)
    (akm_heatKernel_strip_memLp hK h (half_pos ha) y)
    hη hηc (by simpa only [isOpen_Ioo.interior_eq] using hηs)
    (fun t ht => hηone t ⟨ht.1.le, ht.2.le⟩)
    (hχ n).1 (hχ n).2 (show 0 ≤ E by dsimp [E]; positivity)
    (fun z _ => parabolic_tensor_cutoff_error_bound K hη (hχ n).1 hM hB
      (fun t => by rw [abs_of_nonneg (hηb t).1]; exact (hηb t).2)
      hηD (hχabs n) (hχDb n) z)
  have hi (n : ℕ) : Integrable
      (fun z : ℝ × Vec d => χ n z.2 ^ 2 * euclideanNorm (X z.1 z.2 y) ^ 2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using (he n).1
  have hC (n : ℕ) :
      (∫ z in Set.Ioo a b ×ˢ Set.univ, χ n z.2 ^ 2 * euclideanNorm (X z.1 z.2 y) ^ 2) ≤ C := by
    simpa only [C, euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using (he n).2
  exact (memLp_two_of_cutoff_energy_bound (hnorm.comp_aestronglyMeasurable hGm)
    (Filter.Eventually.of_forall (fun z => hχlim z.2)) hi hC).1

end EinsteinRelation.Correctors
