import EinsteinRelation.Correctors.WeakDivergenceH1Testing
import EinsteinRelation.Correctors.AKMHeatKernelCutoffs

/-! # Whole-space H¹ testing of an L² divergence

Source: the E.1 massive-resolvent uniqueness argument,
`paper/main.tex:777–782,840`. Compact cutoffs are removed by dominated
convergence in each L² product.
-/
open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- A global L² divergence can be tested against every actual global H¹
function. Source: `paper/main.tex:777–782,840`. -/
theorem sol04_weakDivergence_test_H1 {d : ℕ}
    {F G : Vec d → Vec d} {h u : Vec d → ℝ}
    (hdiv : HasWeakDivergence Set.univ F h)
    (hw : HasWeakGradient Set.univ u G)
    (hu : MemLp u 2 volume)
    (hG : ∀ i, MemLp (fun x => G x i) 2 volume)
    (hF : ∀ i, MemLp (fun x => F x i) 2 volume)
    (hh : MemLp h 2 volume) :
    (∫ x, dot (F x) (G x)) = -(∫ x, h x * u x) := by
  obtain ⟨χ,C,hC,hχ,hb,hl,hD⟩ := akm_exists_scaled_cutoffs d
  have htest n : IsSpatialTest Set.univ (χ n) :=
    ⟨(hχ n).1,(hχ n).2,Set.subset_univ _⟩
  have hloc {f : Vec d → ℝ} (hf : MemLp f 2 volume) {ψ : Vec d → ℝ}
      (hp : IsSpatialTest Set.univ ψ) : MemLp (fun x => ψ x * f x) 2 volume := by
    exact memLp_mul_spatialTest_univ MeasurableSet.univ
      (by simpa only [Measure.restrict_univ] using hf) hp
  have hDb n x i : |coordinateDerivative i (χ n) x| ≤ C := by
    have hc : |coordinateDerivative i (χ n) x| ≤ C / (n+1 : ℕ) := by
      exact (norm_le_pi_norm (gradient (χ n) x) i).trans (hD n x)
    exact hc.trans (div_le_self hC (by norm_cast; omega))
  have hDl x i : Tendsto (fun n => coordinateDerivative i (χ n) x) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_)
      (show Tendsto (fun n : ℕ => C / (n+1 : ℕ)) atTop (𝓝 0) from by
        simpa only [Nat.cast_add,Nat.cast_one,mul_zero,div_eq_mul_inv,one_mul] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C)
    exact (norm_le_pi_norm (gradient (χ n) x) i).trans (hD n x)
  have hi n i : Integrable
      (fun x => F x i * (χ n x * G x i + u x * coordinateDerivative i (χ n) x)) := by
    exact (hF i).integrable_mul
      ((hloc (hG i) (htest n)).add
        (by simpa only [mul_comm] using
          hloc hu (isSpatialTest_coordinateDerivative (htest n) i)))
  have hEq n :
      (∫ x, dot (F x) (fun j => χ n x * G x j + u x * coordinateDerivative j (χ n) x)) =
        -(∫ x, h x * (χ n x * u x)) :=
    weakDivergence_test_compact_H1 hdiv (hasWeakGradient_mul_spatialTest hw (htest n))
      (hloc hu (htest n)) ((hχ n).2.mul_right)
      (fun j => (hloc (hG j) (htest n)).add (by
        simpa only [mul_comm] using
          hloc hu (isSpatialTest_coordinateDerivative (htest n) j))) hF hh
  have hlim i : Tendsto
      (fun n => ∫ x, F x i * (χ n x * G x i + u x * coordinateDerivative i (χ n) x))
      atTop (𝓝 (∫ x, F x i * G x i)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => |F x i * G x i| + C * |F x i * u x|)
    · intro n
      exact (hi n i).aestronglyMeasurable
    · exact ((hF i).integrable_mul (hG i)).abs.add
        (((hF i).integrable_mul hu).abs.const_mul C)
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs,mul_add]
      calc
        |F x i * (χ n x * G x i) + F x i * (u x * coordinateDerivative i (χ n) x)| ≤
            |F x i * (χ n x * G x i)| + |F x i * (u x * coordinateDerivative i (χ n) x)| := abs_add_le _ _
        _ ≤ |F x i * G x i| + C * |F x i * u x| := by
          have hχa : |χ n x| ≤ 1 := by simpa only [abs_of_nonneg (hb n x).1] using (hb n x).2
          have hd := hDb n x i
          rw [show F x i * (χ n x * G x i) = χ n x * (F x i * G x i) by ring,
            show F x i * (u x * coordinateDerivative i (χ n) x) =
              coordinateDerivative i (χ n) x * (F x i * u x) by ring]
          simpa only [abs_mul,one_mul] using
            add_le_add (mul_le_mul_of_nonneg_right hχa (abs_nonneg (F x i * G x i)))
              (mul_le_mul_of_nonneg_right hd (abs_nonneg (F x i * u x)))
    · filter_upwards with x
      simpa only [one_mul,mul_zero,add_zero] using
        tendsto_const_nhds.mul (((hl x).mul_const (G x i)).add
          ((hDl x i).const_mul (u x)))
  have hr : Tendsto (fun n => ∫ x, h x * (χ n x * u x)) atTop (𝓝 (∫ x, h x * u x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |h x * u x|)
    · intro n
      exact (hh.integrable_mul (hloc hu (htest n))).aestronglyMeasurable
    · exact (hh.integrable_mul hu).abs
    · intro n
      filter_upwards with x
      rw [Real.norm_eq_abs,show h x * (χ n x * u x) = χ n x * (h x * u x) by ring,abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (by simpa only [abs_of_nonneg (hb n x).1] using (hb n x).2)
    · filter_upwards with x
      simpa only [one_mul] using tendsto_const_nhds.mul ((hl x).mul_const (u x))
  have he n : (∑ i, ∫ x, F x i * (χ n x * G x i + u x * coordinateDerivative i (χ n) x)) =
      -(∫ x, h x * (χ n x * u x)) := by
    rw [← integral_finset_sum _ (fun i _ => hi n i)]
    exact hEq n
  have heq := tendsto_nhds_unique
    (tendsto_finset_sum Finset.univ (fun i _ => hlim i))
    (hr.neg.congr (fun n => (he n).symm))
  unfold dot
  rw [integral_finset_sum _ (f := fun i x => F x i * G x i)
    (fun i _ => (hF i).integrable_mul (hG i))]
  exact heq

end EinsteinRelation.Correctors
