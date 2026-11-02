import EinsteinFull.Calculus.PhysicalH1WeightedIntegrationSupport
import EinsteinRelation.Correctors.PairedSpatialCutoff
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! Full-space cutoff exhaustion of the literal physical weighted H1 graph.
The Euclidean reference cutoff and its scaling estimate are reused from the
pinned EinsteinRelation library. No boundary trace identification is used. -/

open MeasureTheory Filter
open scoped ENNReal Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The genuine smooth product rule on either of the physical reference measures. -/
theorem physicalH1Graph_mul_smooth_weighted {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ m)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ m)
    (v : Lp ℂ 2 m) (H : Fin d → Lp ℂ 2 m)
    (hv : IsPhysicalH1Graph m hm v H) :
    ∃ (w : Lp ℂ 2 m) (J : Fin d → Lp ℂ 2 m),
      IsPhysicalH1Graph m hm w J ∧
      (w : Vec d → ℂ) =ᵐ[m] (fun x => (φ x : ℂ) * v x) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[m]
        (fun x => (φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ)) := by
  have hw : MemLp (fun x => (φ x : ℂ) * v x) 2 m := hφb.fun_mul (Lp.memLp v)
  have hJ (j : Fin d) : MemLp (fun x => (φ x : ℂ) * H j x +
      v x * (coordinateDerivative j φ x : ℂ)) 2 m :=
    (hφb.fun_mul (Lp.memLp (H j))).add ((Lp.memLp v).fun_mul (hDφ j))
  let w := hw.toLp _
  let J (j : Fin d) := (hJ j).toLp _
  refine ⟨w, J, ?_, hw.coeFn_toLp, fun j => (hJ j).coeFn_toLp⟩
  rw [isPhysicalH1Graph_iff_representatives m hm
    w J _ _ hw.coeFn_toLp (fun j => (hJ j).coeFn_toLp)]
  constructor
  · intro j
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using
      Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (hv.1 j) hφ
  · intro j
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero] using
      Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (hv.2 j) hφ

/-- Euclidean cutoffs exhaust space with a single derivative constant before all scales. -/
theorem exists_physical_euclidean_cutoffs (d : ℕ) :
    ∃ (χ : ℕ → Vec d → ℝ) (D : ℝ), 0 < D ∧
      (∀ n : ℕ, IsSpatialTest (External.AKM.originBall d (4 * ((n : ℝ) + 1))) (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) ∧
      ∀ n x, euclideanSq (gradient (χ n) x) ≤ (D / ((n : ℝ) + 1)) ^ 2 := by
  obtain ⟨D, hD, h⟩ := Correctors.exists_paired_euclidean_spatial_cutoff d
  choose χ hχ using fun n : ℕ => h (n + 1) (by positivity)
  refine ⟨χ, D, hD, fun n => (hχ n).1, fun n => (hχ n).2.1, ?_,
    fun n => (hχ n).2.2.2⟩
  intro x
  have ht : Tendsto (fun n : ℕ => 2 * ((n : ℝ) + 1)) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).const_mul_atTop zero_lt_two
  have he : ∀ᶠ n : ℕ in atTop, χ n x = 1 :=
    (ht.eventually (eventually_gt_atTop (euclideanNorm x))).mono
      (fun n hn => (hχ n).2.2.1 x hn)
  exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)

/-- Dominated convergence in L2, for the actual measure (which need not be finite). -/
theorem tendsto_eLpNorm_two_of_dominated {α : Type*} [MeasurableSpace α]
    (m : Measure α) (f : ℕ → α → ℂ) (b : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) m) (hb : MemLp b 2 m)
    (hbound : ∀ n, ∀ᵐ x ∂m, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂m, Tendsto (fun n => f n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (f n) 2 m) atTop (𝓝 0) := by
  have hi : (∫⁻ x, ‖b x‖ₑ ^ (2 : ℝ) ∂m) ≠ ⊤ := by
    exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) hb).ne
  have hbound' (n : ℕ) :
      (fun x => ‖f n x‖ₑ ^ (2 : ℝ)) ≤ᵐ[m] (fun x => ‖b x‖ₑ ^ (2 : ℝ)) := by
    filter_upwards [hbound n] with x hx
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self _))
  have hlim' : ∀ᵐ x ∂m, Tendsto (fun n => ‖f n x‖ₑ ^ (2 : ℝ)) atTop (𝓝 0) := by
    filter_upwards [hlim] with x hx
    simpa only [Function.comp_apply, enorm_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)] using!
      (ENNReal.continuous_rpow_const (y := (2 : ℝ))).continuousAt.tendsto.comp hx.enorm
  have ht : Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂m) atTop (𝓝 0) := by
    simpa only [lintegral_zero] using
      (tendsto_lintegral_of_dominated_convergence' (f := fun _ => 0)
        (fun x => ‖b x‖ₑ ^ (2 : ℝ))
        (fun n => (hf n).enorm.pow_const 2) hbound' hi hlim')
  have hE (n : ℕ) : eLpNorm (f n) 2 m =
      (∫⁻ x, ‖f n x‖ₑ ^ (2 : ℝ) ∂m) ^ (1 / (2 : ℝ)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hf n)] <;> simp only [ENNReal.toReal_ofNat]
  simp only [hE]
  simpa only [Function.comp_apply, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using!
    (ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).continuousAt.tendsto.comp ht

private theorem cutoff_coordinate_bound {d : ℕ} {φ : Vec d → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ x, euclideanSq (gradient φ x) ≤ B ^ 2)
    (j : Fin d) (x : Vec d) : |coordinateDerivative j φ x| ≤ B := by
  have hs : (coordinateDerivative j φ x) ^ 2 ≤ euclideanSq (gradient φ x) := by
    change (gradient φ x j) ^ 2 ≤ ∑ k : Fin d, gradient φ x k * gradient φ x k
    simpa only [pow_two] using Finset.single_le_sum
      (fun k (_ : k ∈ Finset.univ) => mul_self_nonneg (gradient φ x k)) (Finset.mem_univ j)
  exact (sq_le_sq₀ (abs_nonneg _) hB).mp (by simpa only [sq_abs] using hs.trans (h x))

private theorem tendsto_L2_of_representatives {d : ℕ} (m : Measure (Vec d))
    (w : ℕ → Lp ℂ 2 m) (u : Lp ℂ 2 m) (f : ℕ → Vec d → ℂ)
    (hf : ∀ n, (w n : Vec d → ℂ) =ᵐ[m] f n)
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 m) atTop (𝓝 0)) :
    Tendsto w atTop (𝓝 u) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' w u).mpr
  convert h using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [hf n] with x hx
  exact congrArg (fun z => z - u x) hx

/-- Every full physical H1 pair has compactly supported H1 approximants, with
both value and the full finite Euclidean gradient converging in the actual L2
measure. The signed force is unrestricted. -/
theorem physicalH1Graph_exists_compact_exhaustion {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m) (hu : IsPhysicalH1Graph m hm u G) :
    ∃ (χ : ℕ → Vec d → ℝ) (w : ℕ → Lp ℂ 2 m)
      (J : ℕ → Fin d → Lp ℂ 2 m),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n, IsPhysicalH1Graph m hm (w n) (J n)) ∧
      (∀ n, (w n : Vec d → ℂ) =ᵐ[m] fun x => (χ n x : ℂ) * u x) ∧
      (∀ n j, (J n j : Vec d → ℂ) =ᵐ[m] fun x =>
        (χ n x : ℂ) * G j x + u x * (coordinateDerivative j (χ n) x : ℂ)) ∧
      (∀ n, ∀ᵐ x ∂m, x ∉ tsupport (χ n) → w n x = 0 ∧ ∀ j, J n j x = 0) ∧
      (∀ j, Tendsto (fun n => eLpNorm
        (fun x => u x * (coordinateDerivative j (χ n) x : ℂ)) 2 m) atTop (𝓝 0)) ∧
      Tendsto w atTop (𝓝 u) ∧
      (∀ j, Tendsto (fun n => J n j) atTop (𝓝 (G j))) ∧
      Tendsto (fun n => ∑ j : Fin d, ‖J n j - G j‖ ^ 2) atTop (𝓝 0) := by
  obtain ⟨χ, D, hD, htest, hχb, hχlim, hgrad⟩ := exists_physical_euclidean_cutoffs d
  have hcoord (n : ℕ) (j : Fin d) (x : Vec d) :
      |coordinateDerivative j (χ n) x| ≤ D / ((n : ℝ) + 1) :=
    cutoff_coordinate_bound (by positivity) (hgrad n) j x
  have hcoordD (n : ℕ) (j : Fin d) (x : Vec d) :
      |coordinateDerivative j (χ n) x| ≤ D := by
    exact (hcoord n j x).trans (div_le_self hD.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
  have hχinf (n : ℕ) : MemLp (fun x => (χ n x : ℂ)) ∞ m := by
    apply memLp_top_of_bound ((Complex.continuous_ofReal.comp (htest n).1.continuous).aestronglyMeasurable) 1
    exact Eventually.of_forall fun x => by
      simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb n x).1] using (hχb n x).2
  have hdcont (n : ℕ) (j : Fin d) : Continuous (coordinateDerivative j (χ n)) :=
    ((contDiff_infty_iff_fderiv.mp (htest n).1).2.clm_apply contDiff_const).continuous
  have hdinf (n : ℕ) (j : Fin d) :
      MemLp (fun x => (coordinateDerivative j (χ n) x : ℂ)) ∞ m := by
    apply memLp_top_of_bound ((Complex.continuous_ofReal.comp (hdcont n j)).aestronglyMeasurable) D
    exact Eventually.of_forall fun x => by simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using hcoordD n j x
  choose w J hw hwr hJr using fun n =>
    physicalH1Graph_mul_smooth_weighted m hm (χ n) (htest n).1 (hχinf n) (hdinf n) u G hu
  have hdlim (j : Fin d) (x : Vec d) :
      Tendsto (fun n => coordinateDerivative j (χ n) x) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => hcoord n j x)
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul D
    simpa only [div_eq_mul_inv, one_mul, one_div, mul_zero] using ht
  have hderivlim (j : Fin d) : Tendsto (fun n => eLpNorm
      (fun x => u x * (coordinateDerivative j (χ n) x : ℂ)) 2 m) atTop (𝓝 0) := by
    apply tendsto_eLpNorm_two_of_dominated m _ (fun x => D * ‖u x‖)
    · intro n
      exact (Lp.memLp u).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp (hdcont n j)).aestronglyMeasurable
    · exact (Lp.memLp u).norm.const_mul D
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        simpa only [mul_comm D] using
          mul_le_mul_of_nonneg_left (hcoordD n j x) (norm_nonneg (u x))
    · exact Eventually.of_forall fun x => by
        simpa only [Function.comp_apply, Complex.ofReal_zero, mul_zero] using
          ((Complex.continuous_ofReal.tendsto 0).comp (hdlim j x)).const_mul (u x)
  have hwlim : Tendsto w atTop (𝓝 u) := by
    apply tendsto_L2_of_representatives m w u _ hwr
    apply tendsto_eLpNorm_two_of_dominated m _ (fun x => ‖u x‖)
    · intro n
      exact (((Complex.continuous_ofReal.comp (htest n).1.continuous).aestronglyMeasurable).mul
        (Lp.memLp u).aestronglyMeasurable).sub (Lp.memLp u).aestronglyMeasurable
    · exact (Lp.memLp u).norm
    · intro n
      exact Eventually.of_forall fun x => by
        have heq : (χ n x : ℂ) * u x - u x = ((χ n x : ℂ) - 1) * u x := by ring
        rw [heq, norm_mul]
        have hc : ‖(χ n x : ℂ) - 1‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hχb n x).1], by linarith [(hχb n x).2]⟩
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (norm_nonneg (u x))
    · exact Eventually.of_forall fun x => by
        simpa only [Function.comp_apply, Complex.ofReal_one, one_mul, sub_self] using
          (((Complex.continuous_ofReal.tendsto 1).comp (hχlim x)).mul_const (u x)).sub_const (u x)
  have hJlim (j : Fin d) : Tendsto (fun n => J n j) atTop (𝓝 (G j)) := by
    apply tendsto_L2_of_representatives m (fun n => J n j) (G j) _ (fun n => hJr n j)
    apply tendsto_eLpNorm_two_of_dominated m _ (fun x => ‖G j x‖ + D * ‖u x‖)
    · intro n
      exact ((((Complex.continuous_ofReal.comp (htest n).1.continuous).aestronglyMeasurable).mul
        (Lp.memLp (G j)).aestronglyMeasurable).add ((Lp.memLp u).aestronglyMeasurable.mul
        ((Complex.continuous_ofReal.comp (hdcont n j)).aestronglyMeasurable))).sub (Lp.memLp (G j)).aestronglyMeasurable
    · exact (Lp.memLp (G j)).norm.add ((Lp.memLp u).norm.const_mul D)
    · intro n
      exact Eventually.of_forall fun x => by
        have hc : ‖(χ n x : ℂ) - 1‖ ≤ 1 := by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          exact abs_le.mpr ⟨by linarith [(hχb n x).1], by linarith [(hχb n x).2]⟩
        have heq : (χ n x : ℂ) * G j x + u x * (coordinateDerivative j (χ n) x : ℂ) - G j x =
            ((χ n x : ℂ) - 1) * G j x + u x * (coordinateDerivative j (χ n) x : ℂ) := by ring
        rw [heq]
        apply (norm_add_le _ _).trans
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have h1 := mul_le_mul_of_nonneg_right hc (norm_nonneg (G j x))
        have h2 := mul_le_mul_of_nonneg_left (hcoordD n j x) (norm_nonneg (u x))
        nlinarith only [h1, h2]
    · exact Eventually.of_forall fun x => by
        have h1 := ((Complex.continuous_ofReal.tendsto 1).comp (hχlim x)).mul_const (G j x)
        have h2 := ((Complex.continuous_ofReal.tendsto 0).comp (hdlim j x)).const_mul (u x)
        simpa only [Function.comp_apply, Complex.ofReal_one, one_mul, Complex.ofReal_zero, mul_zero, add_zero, sub_self] using
          (h1.add h2).sub_const (G j x)
  refine ⟨χ, w, J, fun n => ⟨(htest n).1, (htest n).2.1⟩, hw, hwr, hJr, ?_, hderivlim, hwlim, hJlim, ?_⟩
  · intro n
    filter_upwards [hwr n, ae_all_iff.mpr (hJr n)] with x hx hy
    intro hxoff
    have hz : χ n x = 0 := image_eq_zero_of_notMem_tsupport hxoff
    have hdz (j : Fin d) : coordinateDerivative j (χ n) x = 0 := by
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxoff, ContinuousLinearMap.zero_apply]
    simp only [hx, hy, hz, Complex.ofReal_zero, zero_mul, hdz, mul_zero, add_zero, implies_true, and_self]
  · have ht := tendsto_finset_sum Finset.univ fun j _ =>
      (((hJlim j).sub_const (G j)).norm.pow 2)
    simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using ht

end EinsteinFull
