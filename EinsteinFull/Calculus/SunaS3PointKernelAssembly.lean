import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_point_u2D_kernel
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonal
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds_u23_derivatives
import Mathlib.Analysis.Calculus.FDeriv.Partial
import EinsteinFull.Calculus.SunaS3PhysicalPointKernel
import EinsteinFull.Calculus.U4PhysicalQuantitativeC1
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

open MeasureTheory
open scoped BigOperators NNReal ENNReal ContDiff
namespace EinsteinFull
open EinsteinRelation

/-- The Euclidean Gaussian is integrable on the original coordinate carrier. -/
theorem s3_euclidean_gaussian_integrable (d : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-b * euclideanNorm x ^ 2)) volume := by
  have hproduct (x : Vec d) : Real.exp (-b * euclideanNorm x ^ 2) =
      ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    have hsq : euclideanNorm x ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))]
      simp only [pow_two]
    rw [hsq, Finset.mul_sum, Real.exp_sum]
  simp_rw [hproduct]
  exact Integrable.fintype_prod_dep (fun _ => integrable_exp_neg_mul_sq hb)

/-- Its exact mass gives the scale-dependent constant for bounded data. -/
theorem s3_euclidean_gaussian_integral (d : ℕ) (b : ℝ) :
    (∫ x : Vec d, Real.exp (-b * euclideanNorm x ^ 2)) =
      Real.sqrt (Real.pi / b) ^ d := by
  have hproduct (x : Vec d) : Real.exp (-b * euclideanNorm x ^ 2) =
      ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    have hsq : euclideanNorm x ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))]
      simp only [pow_two]
    rw [hsq, Finset.mul_sum, Real.exp_sum]
  simp_rw [hproduct]
  calc
    _ = (∫ y : ℝ, Real.exp (-b * y ^ 2)) ^ d := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_volume_eq_pow (ι := Fin d)
          (fun y : ℝ => Real.exp (-b * y ^ 2)))
    _ = _ := congrArg (fun a : ℝ => a ^ d) (integral_gaussian b)

end EinsteinFull



open MeasureTheory Filter
open scoped Topology
namespace EinsteinFull
open EinsteinRelation

/-- A local integrable majorant justifies differentiating the actual kernel
integral and taking coordinate derivatives under the integral sign. -/
theorem s3_kernel_integral_derivative_of_local_bound {d : ℕ}
    (K : Vec d → Vec d → ℂ) (f : Vec d → ℂ) (x : Vec d)
    (F' : Vec d → Vec d → (Vec d →L[ℝ] ℂ))
    (hF : ∀ z, AEStronglyMeasurable (fun y => K z y * f y) volume)
    (hi : Integrable (fun y => K x y * f y) volume)
    (hF' : AEStronglyMeasurable (F' x) volume)
    (hd : ∀ z y, HasFDerivAt (fun w => K w y * f y) (F' z y) z)
    (hbound : ∃ s : Set (Vec d), s ∈ 𝓝 x ∧ ∃ B : Vec d → ℝ,
      Integrable B volume ∧ ∀ᵐ y ∂volume, ∀ z ∈ s, ‖F' z y‖ ≤ B y) :
    HasFDerivAt (fun z => ∫ y, K z y * f y) (∫ y, F' x y) x ∧
      ∀ v : Vec d,
        fderiv ℝ (fun z => ∫ y, K z y * f y) x v = ∫ y, F' x y v := by
  obtain ⟨s, hs, B, hB, hmajor⟩ := hbound
  have hx : x ∈ s := mem_of_mem_nhds hs
  have hF'i : Integrable (F' x) volume :=
    hB.mono' hF' (hmajor.mono fun y hy => hy x hx)
  have hdiff : HasFDerivAt (fun z => ∫ y, K z y * f y) (∫ y, F' x y) x :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le hs
      (Eventually.of_forall hF) hi hF' hmajor hB
      (ae_of_all _ fun y z _ => hd z y)
  refine ⟨hdiff, fun v => ?_⟩
  rw [hdiff.fderiv, ContinuousLinearMap.integral_apply hF'i]

end EinsteinFull



namespace EinsteinFull
open EinsteinRelation

/-- A Gaussian in a bounded neighborhood has a fixed integrable Gaussian envelope. -/
theorem s3_gaussian_local_majorant {d : ℕ} (b R : ℝ) (hb : 0 ≤ b) (hR : 0 ≤ R)
    (x z y : Vec d) (hz : euclideanNorm (z - x) ≤ R) :
    Real.exp (-b * euclideanNorm (z - y) ^ 2) ≤
      Real.exp (b * R ^ 2) * Real.exp (-(b / 2) * euclideanNorm (x - y) ^ 2) := by
  have htri := TimeChange.euclideanNorm_add_le (x - z) (z - y)
  have hadd : x - z + (z - y) = x - y := by abel
  rw [hadd, ← neg_sub z x, Entropy.euclideanNorm_neg'] at htri
  have hn1 : 0 ≤ euclideanNorm (z - x) := Real.sqrt_nonneg _
  have hn2 : 0 ≤ euclideanNorm (z - y) := Real.sqrt_nonneg _
  have hn3 : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have htri_sq : euclideanNorm (x - y) ^ 2 ≤
      (euclideanNorm (z - x) + euclideanNorm (z - y)) ^ 2 :=
    (sq_le_sq₀ hn3 (add_nonneg hn1 hn2)).mpr htri
  have hR_sq : euclideanNorm (z - x) ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hn1 hR).mpr hz
  have hsquare : euclideanNorm (x - y) ^ 2 ≤
      2 * euclideanNorm (z - y) ^ 2 + 2 * R ^ 2 := by
    nlinarith [sq_nonneg (euclideanNorm (z - x) - euclideanNorm (z - y))]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg hb (sub_nonneg.mpr hsquare)]

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- The Gaussian majorant for all points in a fixed Euclidean neighborhood is integrable. -/
theorem s3_gaussian_local_majorant_integrable {d : ℕ} (b R : ℝ)
    (hb : 0 < b) (hR : 0 ≤ R) (x : Vec d) :
    ∃ G : Vec d → ℝ, Integrable G volume ∧
      ∀ z y : Vec d, euclideanNorm (z - x) ≤ R →
        Real.exp (-b * euclideanNorm (z - y) ^ 2) ≤ G y := by
  let G : Vec d → ℝ := fun y => Real.exp (b * R ^ 2) *
    Real.exp (-(b / 2) * euclideanNorm (x - y) ^ 2)
  have hb' : 0 < b / 2 := by positivity
  have hshift : Integrable (fun y : Vec d =>
      Real.exp (-(b / 2) * euclideanNorm (x - y) ^ 2)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (s3_euclidean_gaussian_integrable d (b / 2) hb')
  refine ⟨G, hshift.const_mul _, ?_⟩
  intro z y hz
  exact s3_gaussian_local_majorant b R hb.le hR x z y hz

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter
open scoped Topology

/-- A Gaussian derivative bound supplies the neighborhood majorant required
for differentiation of the bounded-data kernel action. -/
theorem s3_gaussian_operator_local_bound {d : ℕ} (F : Vec d → Vec d → (Vec d →L[ℝ] ℂ))
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (x : Vec d)
    (hF : ∀ᵐ y ∂volume, ∀ z, ‖F z y‖ ≤ A * Real.exp (-b * euclideanNorm (z - y) ^ 2)) :
    ∃ s : Set (Vec d), s ∈ 𝓝 x ∧ ∃ G : Vec d → ℝ,
      Integrable G volume ∧ ∀ᵐ y ∂volume, ∀ z ∈ s, ‖F z y‖ ≤ G y := by
  obtain ⟨G, hG, hmajor⟩ := s3_gaussian_local_majorant_integrable b 1 hb (by norm_num) x
  let s : Set (Vec d) := {z | euclideanNorm (z - x) < 1}
  have hsopen : IsOpen s :=
    isOpen_lt (Entropy.continuous_euclideanNorm'.comp (continuous_id.sub continuous_const))
      continuous_const
  have hx : x ∈ s := by simp [s, euclideanNorm, euclideanSq, dot]
  refine ⟨s, hsopen.mem_nhds hx, fun y => A * G y, hG.const_mul A, ?_⟩
  filter_upwards [hF] with y hy
  intro z hz
  exact (hy z).trans (mul_le_mul_of_nonneg_left (hmajor z y (le_of_lt hz)) hA)

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

/-- Gaussian derivative decay justifies differentiation of the kernel integral. -/
theorem s3_kernel_integral_derivative_of_gaussian_bound {d : ℕ}
    (K : Vec d → Vec d → ℂ) (f : Vec d → ℂ) (x : Vec d)
    (F' : Vec d → Vec d → (Vec d →L[ℝ] ℂ))
    (hF : ∀ z, AEStronglyMeasurable (fun y => K z y * f y) volume)
    (hi : Integrable (fun y => K x y * f y) volume)
    (hF' : AEStronglyMeasurable (F' x) volume)
    (hd : ∀ z y, HasFDerivAt (fun w => K w y * f y) (F' z y) z)
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hbound : ∀ᵐ y ∂volume, ∀ z, ‖F' z y‖ ≤ A * Real.exp (-b * euclideanNorm (z - y) ^ 2)) :
    HasFDerivAt (fun z => ∫ y, K z y * f y) (∫ y, F' x y) x ∧
      ∀ v : Vec d, fderiv ℝ (fun z => ∫ y, K z y * f y) x v = ∫ y, F' x y v := by
  exact s3_kernel_integral_derivative_of_local_bound K f x F' hF hi hF' hd
    (s3_gaussian_operator_local_bound F' A b hA hb x hbound)

end EinsteinFull

namespace EinsteinFull

/-- Gaussian mass grows at most polynomially in the positive time scale. -/
theorem s3_sqrt_le_one_add (t : ℝ) (ht : 0 ≤ t) : Real.sqrt t ≤ 1 + t := by
  have hs := Real.sq_sqrt ht
  nlinarith [sq_nonneg (Real.sqrt t - 1 / 2)]

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

/-- An almost-everywhere Gaussian envelope makes a measurable kernel row integrable. -/
theorem s3_integrable_of_gaussian_bound {d : ℕ} (g : Vec d → ℂ) (x : Vec d)
    (A b : ℝ) (hb : 0 < b) (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ y ∂volume, ‖g y‖ ≤ A * Real.exp (-b * euclideanNorm (x - y) ^ 2)) :
    Integrable g volume := by
  have hshift : Integrable (fun y : Vec d =>
      Real.exp (-b * euclideanNorm (x - y) ^ 2)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (s3_euclidean_gaussian_integrable d b hb)
  exact (hshift.const_mul A).mono' hg hbound

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- The Gaussian mass is independent of its spatial center. -/
theorem s3_shifted_gaussian_integral (d : ℕ) (b : ℝ) (x : Vec d) :
    (∫ y : Vec d, Real.exp (-b * euclideanNorm (x - y) ^ 2)) =
      Real.sqrt (Real.pi / b) ^ d := by
  have hm : MeasurableEmbedding (fun y : Vec d => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  calc
    _ = ∫ y : Vec d, Real.exp (-b * euclideanNorm y ^ 2) :=
      (volume.measurePreserving_sub_left x).integral_comp hm _
    _ = _ := s3_euclidean_gaussian_integral d b

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

/-- Integrating an almost-everywhere Gaussian bound gives its exact mass factor. -/
theorem s3_integral_norm_le_gaussian_mass {d : ℕ} (g : Vec d → ℂ) (x : Vec d)
    (A b : ℝ) (hb : 0 < b) (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ y ∂volume, ‖g y‖ ≤ A * Real.exp (-b * euclideanNorm (x - y) ^ 2)) :
    ‖∫ y, g y‖ ≤ A * Real.sqrt (Real.pi / b) ^ d := by
  have hgi := s3_integrable_of_gaussian_bound g x A b hb hg hbound
  have hmajor : Integrable (fun y : Vec d =>
      A * Real.exp (-b * euclideanNorm (x - y) ^ 2)) volume :=
    ((volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (s3_euclidean_gaussian_integrable d b hb)).const_mul A
  calc
    ‖∫ y, g y‖ ≤ ∫ y, ‖g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Vec d, A * Real.exp (-b * euclideanNorm (x - y) ^ 2) :=
      integral_mono_ae hgi.norm hmajor hbound
    _ = A * Real.sqrt (Real.pi / b) ^ d := by rw [integral_const_mul, s3_shifted_gaussian_integral]

end EinsteinFull

namespace EinsteinFull

/-- The Gaussian mass factor is controlled by a polynomial in time. -/
theorem s3_gaussian_mass_polynomial_bound (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (d : ℕ) :
    Real.sqrt (a * t) ^ d ≤ Real.sqrt a ^ d * (1 + t) ^ d := by
  rw [Real.sqrt_mul ha, mul_pow]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.sqrt_nonneg t) (s3_sqrt_le_one_add t ht) d) (by positivity)

/-- Gaussian mass at spatial scale `a / t` grows polynomially in time. -/
theorem s3_gaussian_mass_time_bound (a t : ℝ) (ha : 0 < a) (ht : 0 < t) (d : ℕ) :
    Real.sqrt (Real.pi / (a / t)) ^ d ≤ Real.sqrt (Real.pi / a) ^ d * (2 + t) ^ d := by
  have heq : Real.pi / (a / t) = (Real.pi / a) * t := by
    field_simp
  rw [heq]
  have h := s3_gaussian_mass_polynomial_bound (Real.pi / a) t
    (div_nonneg Real.pi_pos.le ha.le) ht.le d
  refine h.trans ?_
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (Real.sqrt_nonneg _) _)
  exact pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 + t by linarith)
    (show 1 + t ≤ 2 + t by linarith) d

end EinsteinFull



namespace EinsteinFull
open EinsteinRelation

/-- Every intermediate point is separated from at least one endpoint by half
    the endpoint distance. This is the geometric split for the semigroup. -/
theorem s3_split_endpoint_separation {d : ℕ} (x y z : Vec d) :
    euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z) ∨
      euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z) := by
  have htri := TimeChange.euclideanNorm_add_le (x - z) (z - y)
  have hadd : x - z + (z - y) = x - y := by abel
  rw [hadd, ← neg_sub y z, Entropy.euclideanNorm_neg'] at htri
  by_contra h
  push Not at h
  linarith

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation

/-- A measurable intermediate region is separated from the second endpoint,
    while its complement is separated from the first endpoint. -/
theorem s3_split_measurable_region {d : ℕ} (x y : Vec d) :
    ∃ E : Set (Vec d), MeasurableSet E ∧
      (∀ z ∈ E, euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z)) ∧
      (∀ z ∉ E, euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z)) := by
  let E : Set (Vec d) := {z | euclideanNorm (x - z) < euclideanNorm (x - y) / 2}
  have hopen : IsOpen E :=
    isOpen_lt (Entropy.continuous_euclideanNorm'.comp (continuous_const.sub continuous_id))
      continuous_const
  refine ⟨E, hopen.measurableSet, ?_, ?_⟩
  · intro z hz
    rcases s3_split_endpoint_separation x y z with h | h
    · exact False.elim (not_le_of_gt hz h)
    · exact h
  · intro z hz
    exact le_of_not_gt hz

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Continuous locally integrable physical kernel rows are determined by their
    actions on smooth compactly supported real tests. -/
theorem s3_physical_kernel_rows_unique_of_tests {d : ℕ}
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0)
    (hK : ∀ x, Continuous (fun y => K t x y))
    (hJ : ∀ x, Continuous (fun y => J t x y))
    (hKi : ∀ x, LocallyIntegrable (fun y => K t x y) volume)
    (hJi : ∀ x, LocallyIntegrable (fun y => J t x y) volume)
    (htest : ∀ x (g : Vec d → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      (∫ y, g y • K t x y) = ∫ y, g y • J t x y) :
    ∀ x y, K t x y = J t x y := by
  intro x y
  exact congrFun (Measure.eq_of_ae_eq
    (ae_eq_of_integral_contDiff_smul_eq (hKi x) (hJi x) (htest x)) (hK x) (hJ x)) y

end EinsteinFull


open MeasureTheory Filter
namespace EinsteinFull
open EinsteinRelation

/-- A real continuous compactly supported function remains so after complex coercion. -/
theorem s3_test_complex_continuous {d : ℕ} (g : Vec d → ℝ)
    (hg : Continuous g) : Continuous (fun y => (g y : ℂ)) :=
  Complex.continuous_ofReal.comp hg

/-- Complex coercion preserves compact support. -/
theorem s3_test_complex_compactSupport {X : Type*} [TopologicalSpace X] (g : X → ℝ)
    (hs : HasCompactSupport g) : HasCompactSupport (fun y => (g y : ℂ)) :=
  hs.comp_left (g := Complex.ofReal) Complex.ofReal_zero

/-- A compactly supported continuous real test gives a complex L2 function. -/
theorem s3_test_complex_memLp {d : ℕ} (g : Vec d → ℝ)
    (hg : Continuous g) (hs : HasCompactSupport g) :
    MemLp (fun y => (g y : ℂ)) 2 (volume : Measure (Vec d)) :=
  (s3_test_complex_continuous g hg).memLp_of_hasCompactSupport
    (s3_test_complex_compactSupport g hs)

/-- A compactly supported smooth real test has an equivalent complex L2 representative. -/
theorem s3_test_has_complex_L2 {d : ℕ} (g : Vec d → ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    ∃ F : Lp ℂ 2 (volume : Measure (Vec d)),
      (F : Vec d → ℂ) =ᵐ[volume] fun y => (g y : ℂ) := by
  have hfLp := s3_test_complex_memLp g hg.continuous hs
  exact ⟨hfLp.toLp _, MemLp.coeFn_toLp hfLp⟩

/-- Equal L2 kernel actions give equal actions on an equivalent real test. -/
theorem s3_test_actions_eq_of_L2_actions {d : ℕ}
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0)
    (g : Vec d → ℝ) (F : Lp ℂ 2 (volume : Measure (Vec d)))
    (he : (F : Vec d → ℂ) =ᵐ[volume] fun y => (g y : ℂ))
    (ha : (fun x => ∫ y, K t x y * F y) =ᵐ[volume]
      (fun x => ∫ y, J t x y * F y)) :
    (fun x => ∫ y, g y • K t x y) =ᵐ[volume]
      (fun x => ∫ y, g y • J t x y) := by
  filter_upwards [ha] with z hz
  calc
    (∫ y, g y • K t z y) = ∫ y, K t z y * F y := by
      apply integral_congr_ae
      filter_upwards [he] with y hy
      simp [hy, mul_comm]
    _ = ∫ y, J t z y * F y := hz
    _ = ∫ y, g y • J t z y := by
      apply integral_congr_ae
      filter_upwards [he] with y hy
      simp [hy, mul_comm]

/-- Compatible kernels have equal test actions almost everywhere. -/
theorem s3_physical_compatible_test_actions_ae {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0) (ht : 0 < t)
    (hK : IsPhysicalComplexKernel P Pdag K)
    (hJ : IsPhysicalComplexKernel P Pdag J)
    (g : Vec d → ℝ) (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) :
    (fun x => ∫ y, g y • K t x y) =ᵐ[volume]
      (fun x => ∫ y, g y • J t x y) := by
  obtain ⟨F, he⟩ := s3_test_has_complex_L2 g hg hs
  exact s3_test_actions_eq_of_L2_actions K J t g F he
    ((hK t ht F).1.2.symm.trans (hJ t ht F).1.2)


/-- Two compatible physical kernels agree wherever their test actions are
continuous in the starting point. The same argument applies to transposes. -/
theorem s3_physical_compatible_kernel_eq_of_continuous_test_actions {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0) (ht : 0 < t)
    (hK : IsPhysicalComplexKernel P Pdag K)
    (hJ : IsPhysicalComplexKernel P Pdag J)
    (hKrow : ∀ x, Continuous (fun y => K t x y))
    (hJrow : ∀ x, Continuous (fun y => J t x y))
    (hKact : ∀ (g : Vec d → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Continuous (fun x => ∫ y, g y • K t x y))
    (hJact : ∀ (g : Vec d → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Continuous (fun x => ∫ y, g y • J t x y)) :
    ∀ x y, K t x y = J t x y := by
  apply s3_physical_kernel_rows_unique_of_tests K J t hKrow hJrow
    (fun x => (hKrow x).locallyIntegrable) (fun x => (hJrow x).locallyIntegrable)
  intro x g hg hs
  exact congrFun (Measure.eq_of_ae_eq
    (s3_physical_compatible_test_actions_ae P Pdag K J t ht hK hJ g hg hs)
    (hKact g hg hs) (hJact g hg hs)) x

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- The same physical action identification applies to the transposed rows. -/
theorem s3_physical_compatible_transpose_kernel_eq_of_continuous_test_actions {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0) (ht : 0 < t)
    (hK : IsPhysicalComplexKernel P Pdag K)
    (hJ : IsPhysicalComplexKernel P Pdag J)
    (hKrow : ∀ x, Continuous (fun y => K t y x))
    (hJrow : ∀ x, Continuous (fun y => J t y x))
    (hKact : ∀ (g : Vec d → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Continuous (fun x => ∫ y, g y • K t y x))
    (hJact : ∀ (g : Vec d → ℝ), ContDiff ℝ ∞ g → HasCompactSupport g →
      Continuous (fun x => ∫ y, g y • J t y x)) :
    ∀ x y, K t y x = J t y x := by
  exact s3_physical_compatible_kernel_eq_of_continuous_test_actions Pdag P
    (fun t x y => K t y x) (fun t x y => J t y x) t ht hK.transpose hJ.transpose
    hKrow hJrow hKact hJact

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Compactly supported test actions of a jointly continuous kernel are
continuous in the starting point. -/
theorem s3_jointly_continuous_kernel_test_action {d : ℕ}
    (K : Vec d → Vec d → ℂ)
    (hK : Continuous (fun z : Vec d × Vec d => K z.1 z.2))
    (g : Vec d → ℝ) (hg : Continuous g) (hs : HasCompactSupport g) :
    Continuous (fun x => ∫ y, g y • K x y) := by
  have hc : Continuous (fun x => ∫ y in tsupport g, g y • K x y) :=
    continuous_parametric_integral_of_continuous
      ((hg.comp continuous_snd).smul hK) hs
  have he : (fun x => ∫ y in tsupport g, g y • K x y) =
      (fun x => ∫ y, g y • K x y) := by
    funext x
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy, zero_smul]
  exact he ▸ hc

/-- Jointly continuous compatible physical kernels, including a continuous
semigroup split kernel, agree at every pair of points. -/
theorem s3_jointly_continuous_physical_kernels_eq {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K J : ℝ≥0 → Vec d → Vec d → ℂ) (t : ℝ≥0) (ht : 0 < t)
    (hK : IsPhysicalComplexKernel P Pdag K)
    (hJ : IsPhysicalComplexKernel P Pdag J)
    (hKc : Continuous (fun z : Vec d × Vec d => K t z.1 z.2))
    (hJc : Continuous (fun z : Vec d × Vec d => J t z.1 z.2)) :
    ∀ x y, K t x y = J t x y := by
  apply s3_physical_compatible_kernel_eq_of_continuous_test_actions P Pdag K J t ht hK hJ
  · intro x
    exact hKc.comp (continuous_const.prodMk continuous_id)
  · intro x
    exact hJc.comp (continuous_const.prodMk continuous_id)
  · intro g hg hs
    exact s3_jointly_continuous_kernel_test_action (K t) hKc g hg.continuous hs
  · intro g hg hs
    exact s3_jointly_continuous_kernel_test_action (J t) hJc g hg.continuous hs

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- A jointly continuous split kernel at one positive time agrees pointwise
with any jointly continuous compatible kernel of the physical evolution. -/
theorem s3_physical_split_kernel_identification {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (K : Vec d → Vec d → ℂ) (J : ℝ≥0 → Vec d → Vec d → ℂ)
    (t : ℝ≥0) (ht : 0 < t) (hJ : IsPhysicalComplexKernel P Pdag J)
    (hK : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
        (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
      ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
        (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y))
    (hKc : Continuous (fun z : Vec d × Vec d => K z.1 z.2))
    (hJc : Continuous (fun z : Vec d × Vec d => J t z.1 z.2)) :
    ∀ x y, K x y = J t x y := by
  classical
  let K' : ℝ≥0 → Vec d → Vec d → ℂ := fun s => if s = t then K else J s
  have hK' : IsPhysicalComplexKernel P Pdag K' := by
    intro s hs f
    by_cases h : s = t
    · subst s
      simpa only [K', ite_eq_left rfl] using hK f
    · simpa only [K', ite_eq_right h] using hJ s hs f
  have hKc' : Continuous (fun z : Vec d × Vec d => K' t z.1 z.2) := by
    simpa only [K', ite_eq_left rfl] using hKc
  have he := s3_jointly_continuous_physical_kernels_eq P Pdag K' J t ht hK' hJ hKc' hJc
  simpa only [K', ite_eq_left rfl] using he

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- The explicit forward/transpose semigroup split agrees pointwise with a
jointly continuous compatible physical kernel. -/
theorem s3_explicit_semigroup_split_kernel_identification {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0) (hs : 0 < s + s)
    (hsplit : P (s + s) = (P s).comp (P s))
    (hsplitdag : Pdag (s + s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, (P s f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hF : ∀ f, (Pdag s f : Vec d → ℂ) =ᵐ[volume] fun x => F x f)
    (J : ℝ≥0 → Vec d → Vec d → ℂ) (hJ : IsPhysicalComplexKernel P Pdag J)
    (hKc : Continuous (fun z : Vec d × Vec d =>
      E z.1 (star ((InnerProductSpace.toDual ℂ _).symm (F z.2)))))
    (hJc : Continuous (fun z : Vec d × Vec d => J (s + s) z.1 z.2)) :
    ∀ x y, E x (star ((InnerProductSpace.toDual ℂ _).symm (F y))) =
      J (s + s) x y := by
  exact s3_physical_split_kernel_identification P Pdag _ J (s + s) hs hJ
    (s3_semigroup_split_explicit_compatible_rows P Pdag s hsplit hsplitdag
      htranspose E F hE hF) hKc hJc

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation Filter
open scoped Topology NNReal BigOperators

/-- Uniformly bounded operators which vary pointwise continuously can be
applied to a continuously varying vector. This is the weak/strong continuity
step for derivative evaluation functionals in a split kernel. -/
theorem s3_continuous_apply_of_pointwise_and_uniform_bound
    {X E F : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (L : X → E →L[ℂ] F) (v : X → E) (A : ℝ)
    (hA : ∀ x, ‖L x‖ ≤ A)
    (hL : ∀ e, Continuous (fun x => L x e)) (hv : Continuous v) :
    Continuous (fun x => L x (v x)) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hv0 : Filter.Tendsto (fun y => v y - v x) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self] using (hv.tendsto x).sub
      (tendsto_const_nhds : Tendsto (fun _ : X => v x) (𝓝 x) (𝓝 (v x)))
  have hbound : Filter.Tendsto (fun y => A * ‖v y - v x‖) (𝓝 x) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hv0.norm
  have hsmall : Filter.Tendsto (fun y => L y (v y - v x)) (𝓝 x) (𝓝 0) :=
    squeeze_zero_norm (fun y => ((L y).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hA y) (norm_nonneg _))) hbound
  have hfixed : Tendsto (fun y => L y (v x)) (𝓝 x) (𝓝 (L x (v x))) := (hL (v x)).tendsto x
  change Tendsto (fun y => L y (v y)) (𝓝 x) (𝓝 (L x (v x)))
  convert hsmall.add hfixed using 1 <;> simp only [map_sub, sub_add_cancel, zero_add]

/-- The coordinate derivative evaluations are pointwise continuous and
uniformly bounded, as a consequence of the quantitative C¹ smoothing. -/
theorem s3_coordinate_derivative_evaluations {d : ℕ}
    (T : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) →L[ℂ]
      MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (Vec d)))
    (A : ℝ) (hA : 0 ≤ A)
    (hrep : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[MeasureTheory.volume] (T f : Vec d → ℂ) ∧ ∀ y,
        ‖u y‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u y (unitVector j)‖ ^ 2) ≤
          A * ‖f‖)
    (j : Fin d) :
    ∃ D : Vec d → (MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure (Vec d)) →L[ℂ] ℂ),
      (∀ x, ‖D x‖ ≤ A) ∧
      (∀ f, Continuous (fun x => D x f)) ∧
      (∀ x f u, ContDiff ℝ 1 u → u =ᵐ[MeasureTheory.volume] (T f : Vec d → ℂ) →
        D x f = fderiv ℝ u x (unitVector j)) := by
  classical
  choose D hD hDrep using fun x => (c18_evaluations_of_euclidean_C1_bound T x A hA hrep).2 j
  refine ⟨D, hD, ?_, hDrep⟩
  intro f
  obtain ⟨u, hu, huf, _⟩ := hrep f
  have heq : (fun x => D x f) = fun x => fderiv ℝ u x (unitVector j) := by
    funext x
    exact hDrep x f u hu huf
  rw [heq]
  exact (hu.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- For the finite coordinate carrier, continuity on the coordinate basis
implies continuity in operator norm of the full real derivative. -/
theorem s3_continuous_operator_of_coordinate_continuity {X : Type*}
    [TopologicalSpace X] {d : ℕ} (D : X → Vec d →L[ℝ] ℂ)
    (h : ∀ j : Fin d, Continuous (fun z => D z (unitVector j))) :
    Continuous D := by
  classical
  have hrepr : D = fun z => ∑ j : Fin d,
      ContinuousLinearMap.smulRightL ℝ (Vec d) ℂ
        (ContinuousLinearMap.proj j) (D z (unitVector j)) := by
    funext z
    ext v
    have hv : v = ∑ j : Fin d, v j • unitVector j := by
      ext i
      simp [unitVector, Finset.sum_apply, Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    conv_lhs => rw [hv, map_sum]
    simp [map_smul]
  rw [hrepr]
  apply continuous_finsetSum
  intro j hj
  exact (ContinuousLinearMap.smulRightL ℝ (Vec d) ℂ
    (ContinuousLinearMap.proj j)).continuous.comp (h j)

/-- Continuous partial derivatives upgrade separately differentiable kernel
sections to joint C¹ regularity. -/
theorem s3_joint_C1_of_continuous_partial_derivatives {d : ℕ}
    (K : Vec d → Vec d → ℂ)
    (Dx Dy : Vec d × Vec d → (Vec d →L[ℝ] ℂ))
    (hx : ∀ z, HasFDerivAt (fun x => K x z.2) (Dx z) z.1)
    (hy : ∀ z, HasFDerivAt (fun y => K z.1 y) (Dy z) z.2)
    (hcx : Continuous Dx) (hcy : Continuous Dy) :
    ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) := by
  apply contDiff_one_iff_hasFDerivAt.mpr
  refine ⟨fun z => (Dx z).coprod (Dy z), ?_, ?_⟩
  · have h : (fun z => (Dx z).coprod (Dy z)) =
        fun z => (Dx z).comp (ContinuousLinearMap.fst ℝ (Vec d) (Vec d)) +
          (Dy z).comp (ContinuousLinearMap.snd ℝ (Vec d) (Vec d)) := by
      funext z
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.coprod_apply, add_apply,
        ContinuousLinearMap.comp_apply]; rfl
    rw [h]
    exact (hcx.clm_comp continuous_const).add (hcy.clm_comp continuous_const)
  · intro z
    exact (hasStrictFDerivAt_uncurry_coprod (f := K)
      (f₁ := fun x y => Dx (x, y)) (f₂ := fun x y => Dy (x, y))
      (Filter.Eventually.of_forall hx) (Filter.Eventually.of_forall hy)
      hcx.continuousAt hcy.continuousAt).hasFDerivAt

end EinsteinFull


open MeasureTheory
open scoped NNReal BigOperators
namespace EinsteinFull
open EinsteinRelation

/-- A compatible kernel at every positive time, assembled from half-time
quantitative smoothing of the actual physical semigroup and its transpose. -/
theorem s3_kernel_of_quantitative_smoothing {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (hsmooth : ∀ S ∈ [P, Pdag], ∀ s : ℝ≥0, 0 < s →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (S s f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 0 < t →
        Continuous (fun z : Vec d × Vec d => K t z.1 z.2) ∧
        (∀ y, ContDiff ℝ 1 (fun x => K t x y)) ∧
        (∀ x, ContDiff ℝ 1 (fun y => K t x y)) := by
  classical
  have hkernel : ∀ t : ℝ≥0, 0 < t → ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      Continuous (fun z : Vec d × Vec d => K z.1 z.2) ∧
      (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      (∀ x, ContDiff ℝ 1 (fun y => K x y)) := by
    intro t ht
    have hs : 0 < t / 2 := div_pos ht (by norm_num)
    obtain ⟨A, hA, hE⟩ := hsmooth P (by simp) (t / 2) hs
    obtain ⟨B, hB, hF⟩ := hsmooth Pdag (by simp) (t / 2) hs
    obtain ⟨K, ha, hc, hx, hy, _⟩ :=
      s3_quantitative_C1_jointly_continuous_split_kernel P Pdag (t / 2)
        (hP.2.1 _ _) (hPdag.2.1 _ _) (hPdag.2.2.2.2 _) A B hA hB hE hF
    refine ⟨K, ?_, hc, hx, hy⟩
    simpa only [add_halves] using ha
  let K : ℝ≥0 → Vec d → Vec d → ℂ := fun t =>
    if ht : 0 < t then Classical.choose (hkernel t ht) else 0
  refine ⟨K, ?_, ?_⟩
  · intro t ht f
    simpa only [K, dite_eq_left ht] using (Classical.choose_spec (hkernel t ht)).1 f
  · intro t ht
    simpa only [K, dite_eq_left ht] using (Classical.choose_spec (hkernel t ht)).2

end EinsteinFull


open MeasureTheory Filter
open scoped Topology
namespace EinsteinFull
open EinsteinRelation

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter
open scoped Topology NNReal BigOperators

/-- Candidate joint regularity upgrade for the actual Riesz split kernel. -/
theorem s3_split_kernel_joint_C1_of_evaluations {d : ℕ}
    (T U : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hrepT : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ y,
      ‖u y‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u y (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hrepU : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (U f : Vec d → ℂ) ∧ ∀ y,
      ‖u y‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u y (unitVector j)‖ ^ 2) ≤ B * ‖f‖)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hEa : ∀ f, (T f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hFa : ∀ f, (U f : Vec d → ℂ) =ᵐ[volume] fun x => F x f)
    (hEc : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hFc : ∀ f, ContDiff ℝ 1 (fun x => F x f))
    (hEt : Continuous E) (hFt : Continuous F) :
    ContDiff ℝ 1 (fun z : Vec d × Vec d =>
      E z.1 (s3BilinearRieszMap (F z.2))) := by
  classical
  choose DE hDEb hDEc hDEv using fun j : Fin d =>
    s3_coordinate_derivative_evaluations T A hA hrepT j
  choose DF hDFb hDFc hDFv using fun j : Fin d =>
    s3_coordinate_derivative_evaluations U B hB hrepU j
  let K : Vec d → Vec d → ℂ := fun x y => E x (s3BilinearRieszMap (F y))
  have hsym (x y : Vec d) : K x y = F y (s3BilinearRieszMap (E x)) := by
    simpa [K, s3BilinearRieszMap] using s3_riesz_bilinear_symmetry (E x) (F y)
  have hxcoord (j : Fin d) : Continuous (fun z : Vec d × Vec d =>
      fderiv ℝ (fun x => K x z.2) z.1 (unitVector j)) := by
    have hc := s3_continuous_apply_of_pointwise_and_uniform_bound
      (fun z : Vec d × Vec d => DE j z.1)
      (fun z : Vec d × Vec d => s3BilinearRieszMap (F z.2)) A
      (fun z => hDEb j z.1) (fun f => (hDEc j f).comp continuous_fst)
      (s3BilinearRieszMap.continuous.comp (hFt.comp continuous_snd))
    convert hc using 1
    funext z
    exact (hDEv j z.1 _ _ (hEc _) (hEa _).symm).symm
  have hycoord (j : Fin d) : Continuous (fun z : Vec d × Vec d =>
      fderiv ℝ (fun y => K z.1 y) z.2 (unitVector j)) := by
    have hc := s3_continuous_apply_of_pointwise_and_uniform_bound
      (fun z : Vec d × Vec d => DF j z.2)
      (fun z : Vec d × Vec d => s3BilinearRieszMap (E z.1)) B
      (fun z => hDFb j z.2) (fun f => (hDFc j f).comp continuous_snd)
      (s3BilinearRieszMap.continuous.comp (hEt.comp continuous_fst))
    convert hc using 1
    funext z
    have heq : (fun y => K z.1 y) = fun y => F y (s3BilinearRieszMap (E z.1)) :=
      funext (hsym z.1)
    rw [heq]
    exact (hDFv j z.2 _ _ (hFc _) (hFa _).symm).symm
  have hx := s3_continuous_operator_of_coordinate_continuity
    (fun z : Vec d × Vec d => fderiv ℝ (fun x => K x z.2) z.1) hxcoord
  have hy := s3_continuous_operator_of_coordinate_continuity
    (fun z : Vec d × Vec d => fderiv ℝ (fun y => K z.1 y) z.2) hycoord
  apply s3_joint_C1_of_continuous_partial_derivatives K
    (fun z => fderiv ℝ (fun x => K x z.2) z.1)
    (fun z => fderiv ℝ (fun y => K z.1 y) z.2)
  · intro z
    exact ((hEc _).differentiable (by norm_num) z.1).hasFDerivAt
  · intro z
    have heq : (fun y => K z.1 y) = fun y => F y (s3BilinearRieszMap (E z.1)) :=
      funext (hsym z.1)
    rw [heq]
    exact ((hFc _).differentiable (by norm_num) z.2).hasFDerivAt
  · exact hx
  · exact hy

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter
open scoped Topology

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

end EinsteinFull

namespace EinsteinFull

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter

end EinsteinFull

namespace EinsteinFull

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation
open scoped BigOperators

/-- Uniform bounds on the value and coordinate derivatives control the full
    Euclidean gradient appearing in the bounded-data kernel statement. -/
theorem s3_value_gradient_le_of_coordinate_bounds {d : ℕ}
    (u : Vec d → ℂ) (x : Vec d) (M : ℝ) (hM : 0 ≤ M)
    (hu : ‖u x‖ ≤ M)
    (hdu : ∀ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ≤ M) :
    ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
      (1 + Real.sqrt d) * M := by
  have hs : (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
      (d : ℝ) * M ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, M ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact (sq_le_sq₀ (norm_nonneg _) hM).mpr (hdu j)
      _ = _ := by simp
  have hsq := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq_eq_abs, abs_of_nonneg hM] at hsq
  nlinarith

end EinsteinFull


open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Restrict physical L² data to a measurable spatial region. -/
noncomputable def s3LpRestrict {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) : Lp ℂ 2 (volume : Measure (Vec d)) :=
  ((Lp.memLp f).indicator hE).toLp (E.indicator fun z => f z)

/-- Restriction to a measurable set vanishes almost everywhere outside it. -/
theorem s3_lpRestrict_supported {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∀ᵐ z ∂volume, z ∉ E → s3LpRestrict E hE f z = 0 := by
  filter_upwards [((Lp.memLp f).indicator hE).coeFn_toLp] with z hz hnot
  change ((Lp.memLp f).indicator hE).toLp (E.indicator fun z => f z) z = 0
  rw [hz, Set.indicator_of_notMem hnot]

/-- Restriction does not increase the L² norm. -/
theorem s3_lpRestrict_norm_le {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) : ‖s3LpRestrict E hE f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [((Lp.memLp f).indicator hE).coeFn_toLp] with z hz
  change ‖((Lp.memLp f).indicator hE).toLp (E.indicator fun z => f z) z‖ ≤ ‖f z‖
  rw [hz]
  exact norm_indicator_le_norm_self _ _

/-- Restrictions to a set and its complement recover the original L² function. -/
theorem s3_lpRestrict_add_compl {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    s3LpRestrict E hE f + s3LpRestrict Eᶜ hE.compl f = f := by
  apply Lp.ext
  filter_upwards [((Lp.memLp f).indicator hE).coeFn_toLp,
    ((Lp.memLp f).indicator hE.compl).coeFn_toLp,
    Lp.coeFn_add (s3LpRestrict E hE f) (s3LpRestrict Eᶜ hE.compl f)] with z hz1 hz2 hz3
  rw [hz3]
  change s3LpRestrict E hE f z + s3LpRestrict Eᶜ hE.compl f z = f z
  change s3LpRestrict E hE f z = _ at hz1
  change s3LpRestrict Eᶜ hE.compl f z = _ at hz2
  rw [hz1, hz2]
  by_cases hz : z ∈ E <;> simp [hz]

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Spatial restriction as a contractive complex-linear L² operator. -/
noncomputable def s3LpRestrictCLM {d : ℕ} (E : Set (Vec d)) (hE : MeasurableSet E) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) := by
  let L : Lp ℂ 2 (volume : Measure (Vec d)) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
    { toFun := s3LpRestrict E hE
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [((Lp.memLp (f + g)).indicator hE).coeFn_toLp,
          ((Lp.memLp f).indicator hE).coeFn_toLp, ((Lp.memLp g).indicator hE).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add (s3LpRestrict E hE f) (s3LpRestrict E hE g),
          AEEqFun.coeFn_add f.val g.val] with z hz1 hz2 hz3 hz4 hz5 hz6
        change s3LpRestrict E hE (f + g) z = _
        change s3LpRestrict E hE (f + g) z = _ at hz1
        change s3LpRestrict E hE f z = _ at hz2
        change s3LpRestrict E hE g z = _ at hz3
        rw [hz1]
        rw [hz5]
        change _ = s3LpRestrict E hE f z + s3LpRestrict E hE g z
        rw [hz2, hz3]
        by_cases hz : z ∈ E <;> simp [hz, hz4, hz6]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [((Lp.memLp (c • f)).indicator hE).coeFn_toLp,
          ((Lp.memLp f).indicator hE).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (s3LpRestrict E hE f)] with z hz1 hz2 hz3 hz4
        change s3LpRestrict E hE (c • f) z = _
        change s3LpRestrict E hE (c • f) z = _ at hz1
        change s3LpRestrict E hE f z = _ at hz2
        change s3LpRestrict E hE (c • f) z = (c • s3LpRestrict E hE f) z
        rw [hz1, hz4]
        change _ = c • (s3LpRestrict E hE f) z
        rw [hz2]
        by_cases hz : z ∈ E <;> simp [hz, hz3] }
  exact L.mkContinuous 1 (fun f => by change ‖s3LpRestrict E hE f‖ ≤ 1 * ‖f‖; simpa using s3_lpRestrict_norm_le E hE f)

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- A measurable spatial restriction is its own bilinear transpose. -/
theorem s3_lpRestrictCLM_bilinear_transpose {d : ℕ} (E : Set (Vec d))
    (hE : MeasurableSet E) (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ z, s3LpRestrictCLM E hE f z * g z) =
      ∫ z, f z * s3LpRestrictCLM E hE g z := by
  apply integral_congr_ae
  filter_upwards [((Lp.memLp f).indicator hE).coeFn_toLp,
    ((Lp.memLp g).indicator hE).coeFn_toLp] with z hz1 hz2
  change s3LpRestrict E hE f z * g z = f z * s3LpRestrict E hE g z
  change s3LpRestrict E hE f z = _ at hz1
  change s3LpRestrict E hE g z = _ at hz2
  rw [hz1, hz2]
  by_cases hz : z ∈ E <;> simp [hz]

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Restriction may be moved between the two evaluation functionals in the
    bilinear split-kernel pairing. -/
theorem s3_lpRestrict_bilinear_pairing {d : ℕ} (E : Set (Vec d))
    (hE : MeasurableSet E)
    (L M : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
    L (s3LpRestrictCLM E hE (s3BilinearRieszMap M)) =
      M (s3LpRestrictCLM E hE (s3BilinearRieszMap L)) := by
  let r := s3LpRestrictCLM E hE
  have hr := s3_lpRestrictCLM_bilinear_transpose E hE
  have hl := (s3_evaluation_comp_bilinear_transpose L r r hr
    (s3BilinearRieszMap M)).2
  have hm := (s3_evaluation_comp_bilinear_transpose M r r hr
    (s3BilinearRieszMap L)).2
  change L (r (s3BilinearRieszMap M)) = _ at hl
  change M (r (s3BilinearRieszMap L)) = _ at hm
  change L (r (s3BilinearRieszMap M)) = M (r (s3BilinearRieszMap L))
  rw [hl, hm]
  apply integral_congr_ae
  filter_upwards [((Lp.memLp (s3BilinearRieszMap L)).indicator hE).coeFn_toLp,
    ((Lp.memLp (s3BilinearRieszMap M)).indicator hE).coeFn_toLp] with z hz1 hz2
  change s3LpRestrict E hE (s3BilinearRieszMap L) z *
      s3BilinearRieszMap M z =
    s3LpRestrict E hE (s3BilinearRieszMap M) z * s3BilinearRieszMap L z
  change s3LpRestrict E hE (s3BilinearRieszMap L) z = _ at hz1
  change s3LpRestrict E hE (s3BilinearRieszMap M) z = _ at hz2
  rw [hz1, hz2]
  by_cases hz : z ∈ E <;> simp [hz, mul_comm]

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Split the Riesz pairing over a region and its complement. Localized
    evaluation bounds on the two regions give the off-diagonal estimate. -/
theorem s3_split_riesz_pairing_bound {d : ℕ} (E : Set (Vec d))
    (hE : MeasurableSet E)
    (L M : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (a b : ℝ)
    (hL : ∀ f, ‖L (s3LpRestrictCLM E hE f)‖ ≤ a * ‖f‖)
    (hM : ∀ f, ‖M (s3LpRestrictCLM Eᶜ hE.compl f)‖ ≤ b * ‖f‖) :
    ‖L (s3BilinearRieszMap M)‖ ≤ a * ‖M‖ + b * ‖L‖ := by
  have hn (N : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) :
      ‖s3BilinearRieszMap N‖ = ‖N‖ := by
    change ‖star ((InnerProductSpace.toDual ℂ _).symm N)‖ = ‖N‖
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star _), eLpNorm_star,
      ← Lp.norm_def, (InnerProductSpace.toDual ℂ _).symm.norm_map]
  have hsplit := s3_lpRestrict_add_compl E hE (s3BilinearRieszMap M)
  change s3LpRestrictCLM E hE (s3BilinearRieszMap M) +
    s3LpRestrictCLM Eᶜ hE.compl (s3BilinearRieszMap M) = _ at hsplit
  calc
    ‖L (s3BilinearRieszMap M)‖ =
        ‖L (s3LpRestrictCLM E hE (s3BilinearRieszMap M)) +
          M (s3LpRestrictCLM Eᶜ hE.compl (s3BilinearRieszMap L))‖ := by
      conv_lhs => rw [← hsplit, map_add, s3_lpRestrict_bilinear_pairing Eᶜ hE.compl L M]
    _ ≤ ‖L (s3LpRestrictCLM E hE (s3BilinearRieszMap M))‖ +
        ‖M (s3LpRestrictCLM Eᶜ hE.compl (s3BilinearRieszMap L))‖ := norm_add_le _ _
    _ ≤ a * ‖M‖ + b * ‖L‖ := by
      simpa only [hn] using add_le_add (hL (s3BilinearRieszMap M)) (hM (s3BilinearRieszMap L))

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- Two localized evaluation estimates give pointwise decay of their split
    Riesz kernel at half the endpoint separation. -/
theorem s3_split_riesz_pairing_of_separation {d : ℕ} (x y : Vec d)
    (L M : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ) (a b : ℝ)
    (hL : ∀ (E : Set (Vec d)) (hE : MeasurableSet E),
      (∀ z ∈ E, euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z)) →
      ∀ f, ‖L (s3LpRestrictCLM E hE f)‖ ≤ a * ‖f‖)
    (hM : ∀ (E : Set (Vec d)) (hE : MeasurableSet E),
      (∀ z ∈ E, euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z)) →
      ∀ f, ‖M (s3LpRestrictCLM E hE f)‖ ≤ b * ‖f‖) :
    ‖L (s3BilinearRieszMap M)‖ ≤ a * ‖M‖ + b * ‖L‖ := by
  obtain ⟨E, hE, hnear, hfar⟩ := s3_split_measurable_region x y
  apply s3_split_riesz_pairing_bound Eᶜ hE.compl L M a b
  · exact hL Eᶜ hE.compl hfar
  · simpa only [compl_compl] using hM E hE hnear

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped BigOperators

/-- A localized representative estimate applies to the canonical evaluation
    and to every one of its coordinate derivative evaluations. -/
theorem s3_localized_evaluation_of_representative {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (D : Fin d → Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hEa : ∀ f, (T f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hEc : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hD : ∀ j x f u, ContDiff ℝ 1 u → u =ᵐ[volume] (T f : Vec d → ℂ) →
      D j x f = fderiv ℝ u x (unitVector j))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (x : Vec d) (A : ℝ)
    (hrep : ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖) :
    ‖E x f‖ ≤ A * ‖f‖ ∧ ∀ j, ‖D j x f‖ ≤ A * ‖f‖ := by
  obtain ⟨u, hu, huf, hb⟩ := hrep
  have heq : (fun x => E x f) = u :=
    Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d)))
      ((hEa f).symm.trans huf.symm) (hEc f).continuous hu.continuous
  constructor
  · rw [congrFun heq x]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hb
  · intro j
    rw [hD j x f u hu huf]
    have hs : ‖fderiv ℝ u x (unitVector j)‖ ^ 2 ≤
        ∑ k : Fin d, ‖fderiv ℝ u x (unitVector k)‖ ^ 2 :=
      Finset.single_le_sum (f := fun k : Fin d => ‖fderiv ℝ u x (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hr := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hr
    exact hr.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans hb)

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory

/-- The separated Riesz estimate applies simultaneously to a split kernel
    and both of its coordinate gradients. -/
theorem s3_split_kernel_coordinate_decay {d : ℕ} (x y : Vec d)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (DE DF : Fin d → Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (A B a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hEn : ‖E x‖ ≤ A) (hFn : ‖F y‖ ≤ B)
    (hDEn : ∀ j, ‖DE j x‖ ≤ A) (hDFn : ∀ j, ‖DF j y‖ ≤ B)
    (hEloc : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
      (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z)) →
      ∀ f, ‖E x (s3LpRestrictCLM S hS f)‖ ≤ a * ‖f‖)
    (hFloc : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
      (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z)) →
      ∀ f, ‖F y (s3LpRestrictCLM S hS f)‖ ≤ b * ‖f‖)
    (hDEloc : ∀ j (S : Set (Vec d)) (hS : MeasurableSet S),
      (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z)) →
      ∀ f, ‖DE j x (s3LpRestrictCLM S hS f)‖ ≤ a * ‖f‖)
    (hDFloc : ∀ j (S : Set (Vec d)) (hS : MeasurableSet S),
      (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z)) →
      ∀ f, ‖DF j y (s3LpRestrictCLM S hS f)‖ ≤ b * ‖f‖)
    (hDE : ∀ j f, fderiv ℝ (fun z => E z f) x (unitVector j) = DE j x f)
    (hDF : ∀ j f, fderiv ℝ (fun z => F z f) y (unitVector j) = DF j y f) :
    let K := fun x y => E x (s3BilinearRieszMap (F y))
    ‖K x y‖ ≤ a * B + b * A ∧
    (∀ j, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ≤ a * B + b * A) ∧
    (∀ j, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ≤ a * B + b * A) := by
  have hn (L M : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
      (hL : ‖L‖ ≤ A) (hM : ‖M‖ ≤ B)
      (hLl : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
        (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (x - z)) →
        ∀ f, ‖L (s3LpRestrictCLM S hS f)‖ ≤ a * ‖f‖)
      (hMl : ∀ (S : Set (Vec d)) (hS : MeasurableSet S),
        (∀ z ∈ S, euclideanNorm (x - y) / 2 ≤ euclideanNorm (y - z)) →
        ∀ f, ‖M (s3LpRestrictCLM S hS f)‖ ≤ b * ‖f‖) :
      ‖L (s3BilinearRieszMap M)‖ ≤ a * B + b * A :=
    (s3_split_riesz_pairing_of_separation x y L M a b hLl hMl).trans
      (add_le_add (mul_le_mul_of_nonneg_left hM ha) (mul_le_mul_of_nonneg_left hL hb))
  constructor
  · exact hn (E x) (F y) hEn hFn hEloc hFloc
  constructor
  · intro j
    rw [hDE]
    exact hn (DE j x) (F y) (hDEn j) hFn (hDEloc j) hFloc
  · intro j
    have heq : (fun z => E x (s3BilinearRieszMap (F z))) =
        fun z => F z (s3BilinearRieszMap (E x)) := by
      funext z
      exact s3_riesz_bilinear_symmetry (E x) (F z)
    rw [heq, hDF]
    rw [show DF j y (s3BilinearRieszMap (E x)) = E x (s3BilinearRieszMap (DF j y)) by
      simpa [s3BilinearRieszMap] using s3_riesz_bilinear_symmetry (DF j y) (E x)]
    exact hn (E x) (DF j y) hEn (hDFn j) hEloc (hDFloc j)

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation
open scoped BigOperators

/-- Coordinate bounds imply the simultaneous value and two Euclidean
    gradient bound used by the point-kernel statement. -/
theorem s3_kernel_two_gradients_of_coordinate_bounds {d : ℕ}
    (K : Vec d → Vec d → ℂ) (x y : Vec d) (M : ℝ) (hM : 0 ≤ M)
    (hK : ‖K x y‖ ≤ M)
    (hx : ∀ j : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ≤ M)
    (hy : ∀ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ≤ M) :
    ‖K x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
        (2 * (1 + Real.sqrt d)) * M := by
  have h1 := s3_value_gradient_le_of_coordinate_bounds (fun z => K z y) x M hM hK hx
  have h2 := s3_value_gradient_le_of_coordinate_bounds (fun z => K x z) y M hM hK hy
  have hn := norm_nonneg (K x y)
  nlinarith

end EinsteinFull


open MeasureTheory
open scoped NNReal
namespace EinsteinFull
open EinsteinRelation

/-- Select compatible forward and transpose kernels at all positive times,
retaining any supplied pointwise property at large times. -/
theorem s3_select_time_kernels {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ≥0 → (Vec d → Vec d → ℂ) → Prop)
    (h : ∀ t : ℝ≥0, 0 < t → ∃ k : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => k x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => k y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k y x * f y)) ∧
      (2 ≤ (t : ℝ) → R t k)) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → R t (K t) := by
  classical
  let K : ℝ≥0 → Vec d → Vec d → ℂ := fun t =>
    if ht : 0 < t then Classical.choose (h t ht) else 0
  refine ⟨K, ?_, ?_⟩
  · intro t ht f
    simpa only [K, dite_eq_left ht] using (Classical.choose_spec (h t ht)).1 f
  · intro t ht
    have ht' : 0 < t := by exact_mod_cast (show (0 : ℝ) < t from by linarith)
    simpa only [K, dite_eq_left ht'] using (Classical.choose_spec (h t ht')).2 ht

end EinsteinFull


-- Depends on GaussianIntegrability and BoundedGradientSum support.
namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter
open scoped BigOperators

/-- Integrable Gaussian value and derivative envelopes control the bounded-data
integral and its full Euclidean gradient. -/
theorem s3_bounded_kernel_value_gradient {d : ℕ}
    (K : Vec d → Vec d → ℂ) (f : Vec d → ℂ) (x : Vec d)
    (A b B : ℝ) (hA : 0 ≤ A) (hb : 0 < b) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f volume) (hfb : ∀ᵐ y ∂volume, ‖f y‖ ≤ B)
    (hK : ∀ y, ‖K x y‖ ≤ A * Real.exp (-b * euclideanNorm (x - y)^2))
    (hD : ∀ j : Fin d, ∀ y,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ≤
        A * Real.exp (-b * euclideanNorm (x - y)^2))
    (hm : Continuous (fun y => K x y))
    (hmd : ∀ j : Fin d, Continuous (fun y => fderiv ℝ (fun z => K z y) x (unitVector j)))
    (hint : ∀ j : Fin d, fderiv ℝ (fun z => ∫ y, K z y * f y) x (unitVector j) =
      ∫ y, fderiv ℝ (fun z => K z y) x (unitVector j) * f y) :
    ‖∫ y, K x y * f y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => ∫ y, K z y * f y) x (unitVector j)‖ ^ 2) ≤
      (1 + Real.sqrt d) * ((A * B) * Real.sqrt (Real.pi / b) ^ d) := by
  have hAB : 0 ≤ A * B := mul_nonneg hA hB
  have hbound (g : Vec d → ℂ) (hg : Continuous g)
      (hgb : ∀ y, ‖g y‖ ≤ A * Real.exp (-b * euclideanNorm (x - y)^2)) :
      ‖∫ y, g y * f y‖ ≤ (A * B) * Real.sqrt (Real.pi / b)^d := by
    apply s3_integral_norm_le_gaussian_mass _ x (A * B) b hb (hg.aestronglyMeasurable.mul hf)
    filter_upwards [hfb] with y hy
    change ‖g y * f y‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (A * Real.exp (-b * euclideanNorm (x - y)^2)) * B :=
        mul_le_mul (hgb y) hy (norm_nonneg _) (mul_nonneg hA (Real.exp_nonneg _))
      _ = (A * B) * Real.exp (-b * euclideanNorm (x - y)^2) := by ring
  apply s3_value_gradient_le_of_coordinate_bounds _ x _ (by positivity)
  · exact hbound _ hm hK
  · intro j
    rw [hint j]
    exact hbound _ (hmd j) (hD j)

end EinsteinFull


-- Depends on LpRestriction.lean and LocalizedEvaluation.lean.
namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped BigOperators

/-- Localized estimates for supported data imply localized bounds for the
canonical value and derivative evaluations applied to restricted data. -/
theorem s3_restricted_evaluations_of_localized_representatives {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (E : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (D : Fin d → Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hEa : ∀ f, (T f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hEc : ∀ f, ContDiff ℝ 1 (fun x => E x f))
    (hD : ∀ j x f u, ContDiff ℝ 1 u → u =ᵐ[volume] (T f : Vec d → ℂ) →
      D j x f = fderiv ℝ u x (unitVector j))
    (S : Set (Vec d)) (hS : MeasurableSet S) (x : Vec d) (A : ℝ) (hA : 0 ≤ A)
    (hloc : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ S → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖) :
    ∀ f, ‖E x (s3LpRestrictCLM S hS f)‖ ≤ A * ‖f‖ ∧
      ∀ j, ‖D j x (s3LpRestrictCLM S hS f)‖ ≤ A * ‖f‖ := by
  intro f
  have hr := s3_localized_evaluation_of_representative T E D hEa hEc hD
    (s3LpRestrictCLM S hS f) x A (hloc _ (s3_lpRestrict_supported S hS f))
  have hn : ‖s3LpRestrictCLM S hS f‖ ≤ ‖f‖ := s3_lpRestrict_norm_le S hS f
  exact ⟨hr.1.trans (mul_le_mul_of_nonneg_left hn hA),
    fun j => (hr.2 j).trans (mul_le_mul_of_nonneg_left hn hA)⟩

end EinsteinFull


-- Depends on JointC1, SplitJointC1, RestrictionEvaluations and SplitKernelDecay.
namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal BigOperators

/-- Localized representatives for both half-time actions give a jointly C¹
split kernel with simultaneous value and coordinate-gradient decay. -/
theorem s3_localized_split_kernel {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) (hsplit : P (s+s) = (P s).comp (P s))
    (hsplitdag : Pdag (s+s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (A : ℝ) (hA : 0 ≤ A)
    (hrep : ∀ T ∈ [P s, Pdag s], ∀ f, ∃ u : Vec d → ℂ,
      ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (L : Vec d → Vec d → ℝ) (hL : ∀ x y, 0 ≤ L x y)
    (hloc : ∀ T ∈ [P s, Pdag s], ∀ S : Set (Vec d), MeasurableSet S →
      ∀ x y, (∀ z ∈ S, euclideanNorm (x-y)/2 ≤ euclideanNorm (x-z)) →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), (∀ᵐ z ∂volume, z ∉ S → f z = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ L x y * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
        (2 * (1 + Real.sqrt d)) * (L x y * A + L y x * A) := by
  classical
  have hE := hrep (P s) (by simp)
  have hF := hrep (Pdag s) (by simp)
  obtain ⟨E, hEn, hEa, hEc, hEb⟩ := s3_evaluations_of_quantitative_C1_representatives (P s) A hA hE
  obtain ⟨F, hFn, hFa, hFc, hFb⟩ := s3_evaluations_of_quantitative_C1_representatives (Pdag s) A hA hF
  choose DE hDEb hDEc hDEv using fun j : Fin d => s3_coordinate_derivative_evaluations (P s) A hA hE j
  choose DF hDFb hDFc hDFv using fun j : Fin d => s3_coordinate_derivative_evaluations (Pdag s) A hA hF j
  let K : Vec d → Vec d → ℂ := fun x y => E x (s3BilinearRieszMap (F y))
  refine ⟨K, ?_, ?_, ?_⟩
  · simpa [K, s3BilinearRieszMap] using s3_semigroup_split_explicit_compatible_rows P Pdag s hsplit hsplitdag htranspose E F hEa hFa
  · exact s3_split_kernel_joint_C1_of_evaluations (P s) (Pdag s) A A hA hA hE hF E F hEa hFa hEc hFc
      (s3_quantitative_evaluations_continuous E A hA hEc hEb)
      (s3_quantitative_evaluations_continuous F A hA hFc hFb)
  · intro x y
    have hEl (S : Set (Vec d)) (hS : MeasurableSet S)
        (hsep : ∀ z ∈ S, euclideanNorm (x-y)/2 ≤ euclideanNorm (x-z)) :
        ∀ f, ‖E x (s3LpRestrictCLM S hS f)‖ ≤ L x y * ‖f‖ ∧
          ∀ j, ‖DE j x (s3LpRestrictCLM S hS f)‖ ≤ L x y * ‖f‖ :=
      s3_restricted_evaluations_of_localized_representatives (P s) E DE hEa hEc hDEv
        S hS x (L x y) (hL x y) (hloc (P s) (by simp) S hS x y hsep)
    have hFl (S : Set (Vec d)) (hS : MeasurableSet S)
        (hsep : ∀ z ∈ S, euclideanNorm (x-y)/2 ≤ euclideanNorm (y-z)) :
        ∀ f, ‖F y (s3LpRestrictCLM S hS f)‖ ≤ L y x * ‖f‖ ∧
          ∀ j, ‖DF j y (s3LpRestrictCLM S hS f)‖ ≤ L y x * ‖f‖ := by
      apply s3_restricted_evaluations_of_localized_representatives (Pdag s) F DF hFa hFc hDFv
        S hS y (L y x) (hL y x)
      apply hloc (Pdag s) (by simp) S hS y x
      intro z hz
      have hs : euclideanNorm (y-x) = euclideanNorm (x-y) := by
        rw [← neg_sub x y, Entropy.euclideanNorm_neg']
      simpa [hs] using hsep z hz
    have hcoord := s3_split_kernel_coordinate_decay x y E F DE DF A A (L x y) (L y x)
      (hL x y) (hL y x) (hEn x) (hFn y) (fun j => hDEb j x) (fun j => hDFb j y)
      (fun S hS hsep f => (hEl S hS hsep f).1)
      (fun S hS hsep f => (hFl S hS hsep f).1)
      (fun j S hS hsep f => (hEl S hS hsep f).2 j)
      (fun j S hS hsep f => (hFl S hS hsep f).2 j)
      (fun j f => (hDEv j x f _ (hEc f) (hEa f).symm).symm)
      (fun j f => (hDFv j y f _ (hFc f) (hFa f).symm).symm)
    exact s3_kernel_two_gradients_of_coordinate_bounds K x y _
      (add_nonneg (mul_nonneg (hL x y) hA) (mul_nonneg (hL y x) hA)) hcoord.1 hcoord.2.1 hcoord.2.2

end EinsteinFull


namespace EinsteinFull

/-- Multiplying a global half-time factor by a localized half-time factor
preserves Gaussian decay while adding the exponential growth exponents. -/
theorem s3_gaussian_half_time_product (A z w : ℝ) :
    (A * Real.exp (z - w)) * (A * Real.exp z) =
      A ^ 2 * Real.exp (2 * z - w) := by
  have he : (z - w) + z = 2 * z - w := by ring
  calc
    _ = A ^ 2 * (Real.exp (z - w) * Real.exp z) := by ring
    _ = _ := by rw [← Real.exp_add, he]

/-- Squared polynomial factors at half time are bounded by a full-time
polynomial whenever the half time is nonnegative. -/
theorem s3_half_time_polynomial (s : ℝ) (hs : 0 ≤ s) (N : ℕ) :
    ((2 + s) ^ N) ^ 2 ≤ (2 + (s + s)) ^ (N + N) := by
  rw [← pow_mul, show N * 2 = N + N by omega]
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-- A larger nonnegative structural constant absorbs both a prefactor and
exponential force growth. -/
theorem s3_absorb_exponential_growth (A k C q t : ℝ)
    (hA : 0 ≤ A) (hAC : A ≤ C) (hkC : k ≤ C) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    A * Real.exp (k * q * t) ≤ C * Real.exp (C * q * t) := by
  have he : Real.exp (k * q * t) ≤ Real.exp (C * q * t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hkC hq) ht
  exact mul_le_mul hAC he (Real.exp_pos _).le (hA.trans hAC)

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation

/-- Joint C¹ regularity makes each first-variable directional derivative
continuous as a function of the second spatial variable. -/
theorem s3_joint_C1_first_partial_continuous {d : ℕ} (K : Vec d → Vec d → ℂ)
    (hK : ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2))
    (x v : Vec d) : Continuous (fun y => fderiv ℝ (fun z => K z y) x v) := by
  have heq (y : Vec d) : fderiv ℝ (fun z => K z y) x v =
      fderiv ℝ (fun z : Vec d × Vec d => K z.1 z.2) (x,y) (v,0) := by
    have h := ((hK.differentiable (by norm_num) (x,y)).hasFDerivAt.comp x
      ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const y x))).fderiv
    have hv := congrArg (fun F : Vec d →L[ℝ] ℂ => F v) h
    change fderiv ℝ (fun z => K z y) x v = _ at hv
    exact hv
  have hc : Continuous (fun y : Vec d =>
      fderiv ℝ (fun z : Vec d × Vec d => K z.1 z.2) (x,y) (v,0)) :=
    ((hK.continuous_fderiv (by norm_num)).comp (continuous_const.prodMk continuous_id)).clm_apply
      continuous_const
  convert hc using 1
  funext y
  exact heq y

/-- Joint C¹ regularity makes the first-variable derivative continuous as an
operator when the second spatial variable varies. -/
theorem s3_joint_C1_first_fderiv_continuous {d : ℕ} (K : Vec d → Vec d → ℂ)
    (hK : ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2)) (x : Vec d) :
    Continuous (fun y => fderiv ℝ (fun z => K z y) x) :=
  s3_continuous_operator_of_coordinate_continuity _
    (fun j => s3_joint_C1_first_partial_continuous K hK x (unitVector j))

end EinsteinFull


-- Depends on Gaussian support, JointPartialContinuity and BoundedKernelEstimate.
namespace EinsteinFull
open EinsteinRelation MeasureTheory Filter
open scoped BigOperators

/-- A jointly C¹ kernel with Gaussian value and first-gradient bounds acts on
bounded measurable data by a differentiable integral with Gaussian mass bound. -/
theorem s3_bounded_data_action_of_gaussian {d : ℕ}
    (K : Vec d → Vec d → ℂ)
    (hK : ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2))
    (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hbound : ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤
      A * Real.exp (-b * euclideanNorm (x-y)^2))
    (f : Vec d → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hf : AEStronglyMeasurable f volume) (hfb : ∀ᵐ y ∂volume, ‖f y‖ ≤ B) :
    let u := fun x => ∫ y, K x y * f y
    Differentiable ℝ u ∧ ∀ x : Vec d,
      Integrable (fun y => K x y * f y) ∧
      (∀ j : Fin d, Integrable (fun y => fderiv ℝ (fun z => K z y) x (unitVector j) * f y) ∧
        fderiv ℝ u x (unitVector j) = ∫ y, fderiv ℝ (fun z => K z y) x (unitVector j) * f y) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        (1 + Real.sqrt d) * ((A * B) * Real.sqrt (Real.pi / b)^d) := by
  classical
  have hk (x : Vec d) : Continuous (fun y => K x y) :=
    hK.continuous.comp (continuous_const.prodMk continuous_id)
  have hval (x y : Vec d) : ‖K x y‖ ≤ A * Real.exp (-b * euclideanNorm (x-y)^2) :=
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hbound x y)
  have hgrad (x y : Vec d) : Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤
      A * Real.exp (-b * euclideanNorm (x-y)^2) :=
    (le_add_of_nonneg_left (norm_nonneg _)).trans (hbound x y)
  have hcoord (x y : Vec d) (j : Fin d) :
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ≤
        A * Real.exp (-b * euclideanNorm (x-y)^2) := by
    have hs : ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2 ≤
        ∑ k : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector k)‖ ^ 2 :=
      Finset.single_le_sum (f := fun k : Fin d => ‖fderiv ℝ (fun z => K z y) x (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hs' := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs'
    exact hs'.trans (hgrad x y)
  have hlocal (x : Vec d) :
      HasFDerivAt (fun z => ∫ y, K z y * f y)
          (∫ y, f y • fderiv ℝ (fun z => K z y) x) x ∧
      Integrable (fun y => K x y * f y) ∧
      (∀ j : Fin d, Integrable (fun y => fderiv ℝ (fun z => K z y) x (unitVector j) * f y) ∧
        fderiv ℝ (fun z => ∫ y, K z y * f y) x (unitVector j) =
          ∫ y, fderiv ℝ (fun z => K z y) x (unitVector j) * f y) := by
    let F' : Vec d → Vec d → (Vec d →L[ℝ] ℂ) :=
      fun z y => f y • fderiv ℝ (fun w => K w y) z
    have hmeas (z : Vec d) : AEStronglyMeasurable (fun y => K z y * f y) volume :=
      (hk z).aestronglyMeasurable.mul hf
    have hboundVal : ∀ᵐ y ∂volume, ‖K x y * f y‖ ≤
        (A*B) * Real.exp (-b * euclideanNorm (x-y)^2) := by
      filter_upwards [hfb] with y hy
      rw [norm_mul]
      calc
        _ ≤ (A * Real.exp (-b * euclideanNorm (x-y)^2)) * B :=
          mul_le_mul (hval x y) hy (norm_nonneg _) (by positivity)
        _ = _ := by ring
    have hi := s3_integrable_of_gaussian_bound _ x (A*B) b hb (hmeas x) hboundVal
    have hFmeas : AEStronglyMeasurable (F' x) volume :=
      hf.smul (s3_joint_C1_first_fderiv_continuous K hK x).aestronglyMeasurable
    have hdiff (z y : Vec d) : HasFDerivAt (fun w => K w y * f y) (F' z y) z := by
      have hc : ContDiff ℝ 1 (fun w => K w y) := hK.comp
        (contDiff_id.prodMk contDiff_const)
      convert ((hc.differentiable (by norm_num) z).hasFDerivAt.const_smul (f y)) using 1
      · ext w; simp [smul_eq_mul, mul_comm]
    have hmajor : ∀ᵐ y ∂volume, ∀ z, ‖F' z y‖ ≤
        ((d : ℝ) * A * B) * Real.exp (-b * euclideanNorm (z-y)^2) := by
      filter_upwards [hfb] with y hy
      intro z
      have hd := s3_fderiv_norm_le_of_coordinate_gradient (fun w => K w y) z
        (A * Real.exp (-b * euclideanNorm (z-y)^2)) (by positivity) (hgrad z y)
      calc
        ‖F' z y‖ = ‖f y‖ * ‖fderiv ℝ (fun w => K w y) z‖ := norm_smul _ _
        _ ≤ B * ((d : ℝ) * (A * Real.exp (-b * euclideanNorm (z-y)^2))) :=
          mul_le_mul hy hd (norm_nonneg _) hB
        _ = _ := by ring
    have hd := s3_kernel_integral_derivative_of_gaussian_bound K f x F' hmeas hi hFmeas hdiff
      ((d : ℝ) * A * B) b (by positivity) hb hmajor
    refine ⟨hd.1, hi, ?_⟩
    intro j
    have hcoordMeas : AEStronglyMeasurable
        (fun y => fderiv ℝ (fun z => K z y) x (unitVector j) * f y) volume :=
      (s3_joint_C1_first_partial_continuous K hK x (unitVector j)).aestronglyMeasurable.mul hf
    have hcoordBound : ∀ᵐ y ∂volume,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j) * f y‖ ≤
          (A * B) * Real.exp (-b * euclideanNorm (x-y)^2) := by
      filter_upwards [hfb] with y hy
      rw [norm_mul]
      calc
        _ ≤ (A * Real.exp (-b * euclideanNorm (x-y)^2)) * B :=
          mul_le_mul (hcoord x y j) hy (norm_nonneg _) (by positivity)
        _ = _ := by ring
    refine ⟨s3_integrable_of_gaussian_bound _ x (A*B) b hb hcoordMeas hcoordBound, ?_⟩
    simpa [F', smul_eq_mul, mul_comm] using hd.2 (unitVector j)
  refine ⟨fun x => (hlocal x).1.differentiableAt, fun x => ?_⟩
  refine ⟨(hlocal x).2.1, (hlocal x).2.2, ?_⟩
  exact s3_bounded_kernel_value_gradient K f x A b B hA hb hB hf hfb
    (hval x) (fun j y => hcoord x y j) (hk x)
    (fun j => s3_joint_C1_first_partial_continuous K hK x (unitVector j))
    (fun j => ((hlocal x).2.2 j).2)

end EinsteinFull


-- Depends on s3_gaussian_mass_polynomial_bound.
namespace EinsteinFull

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped BigOperators

/-- Spatial transposition preserves joint C¹ regularity and the Gaussian
estimate with both coordinate gradients. -/
theorem s3_swap_kernel_C1_gaussian {d : ℕ} (K : Vec d → Vec d → ℂ)
    (A b : ℝ)
    (hK : ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2))
    (hbound : ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
      A * Real.exp (-b * euclideanNorm (x-y)^2)) :
    ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.2 z.1) ∧
    ∀ x y, ‖K y x‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K y z) x (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K z x) y (unitVector j)‖ ^ 2) ≤
      A * Real.exp (-b * euclideanNorm (x-y)^2) := by
  constructor
  · exact hK.comp (contDiff_snd.prodMk contDiff_fst)
  · intro x y
    have hs : euclideanNorm (y-x) = euclideanNorm (x-y) := by
      rw [← neg_sub x y, Entropy.euclideanNorm_neg']
    have h := hbound y x
    rw [hs] at h
    linarith

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped BigOperators

/-- The localized representative estimate includes the global estimate by
choosing the whole space and zero separation. -/
theorem s3_global_representative_of_localized {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (A c t : ℝ)
    (hloc : ∀ (E : Set (Vec d)), MeasurableSet E →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          A * Real.exp (-c * ell^2 / t) * ‖f‖) :
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x, ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖^2) ≤ A * ‖f‖ := by
  intro f
  obtain ⟨u, hu, huf, hb⟩ := hloc Set.univ MeasurableSet.univ f (by simp)
  refine ⟨u, hu, huf, fun x => ?_⟩
  simpa using hb x 0 (le_refl 0) (fun y _ => Real.sqrt_nonneg _)

end EinsteinFull
namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal BigOperators

/-- Localized Gaussian smoothing of both actions yields a compatible joint C¹
split kernel with Gaussian decay of its value and both coordinate gradients. -/
theorem s3_split_kernel_of_localized_gaussian {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) (hsplit : P (s+s) = (P s).comp (P s))
    (hsplitdag : Pdag (s+s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (A b : ℝ) (hA : 0 ≤ A)
    (hloc : ∀ T ∈ [P s, Pdag s], ∀ E : Set (Vec d), MeasurableSet E →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          A * Real.exp (-b * ell^2) * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
        (2 * (1 + Real.sqrt d)) *
          ((A * Real.exp (-b * (euclideanNorm (x-y)/2)^2)) * A +
           (A * Real.exp (-b * (euclideanNorm (y-x)/2)^2)) * A) := by
  have hrep : ∀ T ∈ [P s, Pdag s], ∀ f, ∃ u : Vec d → ℂ,
      ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖ := by
    intro T hT
    apply s3_global_representative_of_localized T A b 1
    intro E hE f hf
    obtain ⟨u, hu, huf, hb⟩ := hloc T hT E hE f hf
    refine ⟨u, hu, huf, ?_⟩
    intro x ell hell hsep
    simpa using hb x ell hell hsep
  let L : Vec d → Vec d → ℝ := fun x y => A * Real.exp (-b * (euclideanNorm (x-y)/2)^2)
  have hL : ∀ x y, 0 ≤ L x y := fun x y => mul_nonneg hA (Real.exp_pos _).le
  have hlocal : ∀ T ∈ [P s, Pdag s], ∀ E : Set (Vec d), MeasurableSet E →
      ∀ x y, (∀ z ∈ E, euclideanNorm (x-y)/2 ≤ euclideanNorm (x-z)) →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)), (∀ᵐ z ∂volume, z ∉ E → f z = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ L x y * ‖f‖ := by
    intro T hT E hE x y hsep f hf
    obtain ⟨u, hu, huf, hb⟩ := hloc T hT E hE f hf
    refine ⟨u, hu, huf, ?_⟩
    exact hb x _ (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) hsep
  simpa [L] using s3_localized_split_kernel P Pdag s hsplit hsplitdag htranspose A hA hrep L hL hlocal

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal

/-- Combine compatible kernels at every positive time with kernels satisfying
an additional large-time property. -/
theorem s3_select_large_time_kernels {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ≥0 → (Vec d → Vec d → ℂ) → Prop)
    (hsmall : ∀ t : ℝ≥0, 0 < t → ∃ k : Vec d → Vec d → ℂ,
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => k x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => k y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k y x * f y))
    (hlarge : ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ∃ k : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => k x y * f y)) ∧
          (P t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => k y x * f y)) ∧
          (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, k y x * f y)) ∧ R t k) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → R t (K t) := by
  classical
  apply s3_select_time_kernels P Pdag R
  intro t ht
  by_cases htlarge : 2 ≤ (t : ℝ)
  · obtain ⟨k, hk, hR⟩ := hlarge t htlarge
    exact ⟨k, hk, fun _ => hR⟩
  · obtain ⟨k, hk⟩ := hsmall t ht
    exact ⟨k, hk, fun h => False.elim (htlarge h)⟩

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation

/-- Normalize the symmetric two-region split into one Gaussian factor. -/
theorem s3_split_gaussian_factor {d : ℕ} (A b : ℝ) (x y : Vec d) :
    (2 * (1 + Real.sqrt d)) *
      ((A * Real.exp (-b * (euclideanNorm (x-y)/2)^2)) * A +
       (A * Real.exp (-b * (euclideanNorm (y-x)/2)^2)) * A) =
    (4 * (1 + Real.sqrt d) * A^2) *
      Real.exp (-(b/4) * euclideanNorm (x-y)^2) := by
  have hs : euclideanNorm (y-x) = euclideanNorm (x-y) := by
    rw [← neg_sub x y, Entropy.euclideanNorm_neg']
  rw [hs]
  have he : -b * (euclideanNorm (x-y)/2)^2 =
      -(b/4) * euclideanNorm (x-y)^2 := by ring
  rw [he]
  ring

end EinsteinFull

namespace EinsteinFull

/-- Half-time localization at half the separation gives full-time Gaussian
rate c / 2. -/
theorem s3_half_time_gaussian_scale (c s r : ℝ) (hs : s ≠ 0) :
    -((c / s) / 4) * r^2 = -(c / 2) * r^2 / (s+s) := by
  have hs2 : s + s ≠ 0 := by
    intro h
    apply hs
    linarith
  field_simp
  all_goals ring

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal BigOperators

/-- The split kernel has a single normalized Gaussian bound. -/
theorem s3_split_kernel_of_localized_gaussian_normalized {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) (hsplit : P (s+s) = (P s).comp (P s))
    (hsplitdag : Pdag (s+s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (A b : ℝ) (hA : 0 ≤ A)
    (hloc : ∀ T ∈ [P s, Pdag s], ∀ E : Set (Vec d), MeasurableSet E →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          A * Real.exp (-b * ell^2) * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
        (4 * (1 + Real.sqrt d) * A^2) *
          Real.exp (-(b/4) * euclideanNorm (x-y)^2) := by
  obtain ⟨K, hpair, hjoint, hbound⟩ :=
    s3_split_kernel_of_localized_gaussian P Pdag s hsplit hsplitdag htranspose A b hA hloc
  refine ⟨K, hpair, hjoint, ?_⟩
  intro x y
  rw [← s3_split_gaussian_factor A b x y]
  exact hbound x y

end EinsteinFull

namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped BigOperators

/-- A joint Gaussian kernel estimate supplies bounded-data actions in both
spatial orientations. -/
theorem s3_both_bounded_data_actions {d : ℕ}
    (K : Vec d → Vec d → ℂ) (A b : ℝ) (hA : 0 ≤ A) (hb : 0 < b)
    (hK : ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2))
    (hbound : ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
      Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
      A * Real.exp (-b * euclideanNorm (x-y)^2)) :
    ∀ H ∈ [K, fun x y => K y x],
      ContDiff ℝ 1 (fun z : Vec d × Vec d => H z.1 z.2) ∧
      (∀ x y, ‖H x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H x z) y (unitVector j)‖ ^ 2) ≤
        A * Real.exp (-b * euclideanNorm (x-y)^2)) ∧
      ∀ (f : Vec d → ℂ) (B : ℝ), 0 ≤ B →
        AEStronglyMeasurable f volume → (∀ᵐ y ∂volume, ‖f y‖ ≤ B) →
        let u := fun x => ∫ y, H x y * f y
        Differentiable ℝ u ∧ ∀ x : Vec d,
          Integrable (fun y => H x y * f y) ∧
          (∀ j : Fin d,
            Integrable (fun y => fderiv ℝ (fun z => H z y) x (unitVector j) * f y) ∧
            fderiv ℝ u x (unitVector j) =
              ∫ y, fderiv ℝ (fun z => H z y) x (unitVector j) * f y) ∧
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            (1 + Real.sqrt d) * ((A * B) * Real.sqrt (Real.pi / b)^d) := by
  intro H hH
  have hswap := s3_swap_kernel_C1_gaussian K A b hK hbound
  have hjoint : ContDiff ℝ 1 (fun z : Vec d × Vec d => H z.1 z.2) ∧
      ∀ x y, ‖H x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => H x z) y (unitVector j)‖ ^ 2) ≤
        A * Real.exp (-b * euclideanNorm (x-y)^2) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hH
    rcases hH with rfl | rfl
    · exact ⟨hK, hbound⟩
    · exact hswap
  refine ⟨hjoint.1, hjoint.2, ?_⟩
  intro f B hB hf hfb
  apply s3_bounded_data_action_of_gaussian H hjoint.1 A b hA hb
  · intro x y
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hjoint.2 x y)
  · exact hB
  · exact hf
  · exact hfb

end EinsteinFull



namespace EinsteinFull

/-- Absorb a Gaussian-mass polynomial into a structural prefactor, preserving
force growth and the combined time exponent. -/
theorem s3_absorb_mass_polynomial (a b C k q t : ℝ) (m n : ℕ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : a * b ≤ C) (hk : k ≤ C)
    (hq : 0 ≤ q) (ht : 0 ≤ t) :
    (a * (2 + t)^m * Real.exp (k*q*t)) * (b * (2+t)^n) ≤
      C * (2+t)^(m+n) * Real.exp (C*q*t) := by
  have hp : 0 ≤ (2+t)^(m+n) := by positivity
  have hCe : 0 ≤ C := (mul_nonneg ha hb).trans hC
  have he : Real.exp (k*q*t) ≤ Real.exp (C*q*t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hq) ht
  have hc : a*b * (2+t)^(m+n) ≤ C * (2+t)^(m+n) :=
    mul_le_mul_of_nonneg_right hC hp
  have := mul_le_mul hc he (Real.exp_pos _).le (mul_nonneg hCe hp)
  convert this using 1; rw [pow_add]; ring

end EinsteinFull

namespace EinsteinFull

/-- Squaring the half-time smoothing factor gives a full-time polynomial
and exactly the full-time force exponent. -/
theorem s3_half_time_smoothing_prefactor (C q s : ℝ) (N : ℕ) (d : ℕ)
    (hs : 0 ≤ s) :
    4 * (1 + Real.sqrt d) *
        (C * (2+s)^N * Real.exp (C*q*s))^2 ≤
      (4 * (1 + Real.sqrt d) * C^2) * (2+(s+s))^(N+N) *
        Real.exp (C*q*(s+s)) := by
  have hpoly : ((2+s)^N)^2 ≤ (2+(s+s))^(N+N) := by
    rw [← pow_mul, show N * 2 = N + N by omega]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hexp : (Real.exp (C*q*s))^2 = Real.exp (C*q*(s+s)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (4 * (1 + Real.sqrt d) * C^2) * ((2+s)^N)^2 *
        Real.exp (C*q*(s+s)) := by rw [← hexp]; ring
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpoly (by positivity)) (Real.exp_pos _).le

end EinsteinFull

namespace EinsteinFull

/-- The mass of a Gaussian of rate `c / t` is absorbed into the same
structural constant and into an additional dimension-degree time factor. -/
theorem s3_absorb_gaussian_mass (D C k q t c : ℝ) (n d : ℕ)
    (hD : 0 ≤ D) (hc : 0 < c) (ht : 0 < t) (hq : 0 ≤ q)
    (hC : D * Real.sqrt (Real.pi / c)^d ≤ C) (hk : k ≤ C) :
    (D * (2+t)^n * Real.exp (k*q*t)) *
        Real.sqrt (Real.pi / (c/t))^d ≤
      C * (2+t)^(n+d) * Real.exp (C*q*t) := by
  have hmass : Real.sqrt (Real.pi / (c/t))^d ≤
      Real.sqrt (Real.pi / c)^d * (2+t)^d :=
    s3_gaussian_mass_time_bound c t hc ht d
  have hpref : 0 ≤ D * (2+t)^n * Real.exp (k*q*t) := by positivity
  calc
    _ ≤ (D * (2+t)^n * Real.exp (k*q*t)) *
        (Real.sqrt (Real.pi / c)^d * (2+t)^d) :=
          mul_le_mul_of_nonneg_left hmass hpref
    _ ≤ _ := s3_absorb_mass_polynomial D (Real.sqrt (Real.pi / c)^d)
      C k q t n d hD (by positivity) hC hk hq ht.le

end EinsteinFull

namespace EinsteinFull

/-- Enlarge the structural prefactor, time exponent and force-growth rate
while retaining the same Gaussian off-diagonal decay. -/
theorem s3_enlarge_gaussian_bound (D C k q t c r : ℝ) (n d : ℕ)
    (hD : 0 ≤ D) (hDC : D ≤ C) (hk : k ≤ C) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    D * (2+t)^n * Real.exp (k*q*t-c*r^2/t) ≤
      C * (2+t)^(n+d) * Real.exp (C*q*t-c*r^2/t) := by
  have hpow : 1 ≤ (2+t)^d := one_le_pow₀ (by linarith)
  have hbase : 0 ≤ D * (2+t)^n * Real.exp (k*q*t) := by positivity
  have hsmall : D * (2+t)^n * Real.exp (k*q*t) ≤
      (D * (2+t)^n * Real.exp (k*q*t)) * (1 * (2+t)^d) := by
    simpa only [one_mul, mul_one] using mul_le_mul_of_nonneg_left hpow hbase
  have hbig := s3_absorb_mass_polynomial D 1 C k q t n d hD (by norm_num)
    (by simpa using hDC) hk hq ht
  have hgrowth := hsmall.trans hbig
  calc
    _ = (D * (2+t)^n * Real.exp (k*q*t)) * Real.exp (-(c*r^2/t)) := by
      rw [show k*q*t-c*r^2/t = k*q*t + (-(c*r^2/t)) by ring, Real.exp_add]
      ring
    _ ≤ (C * (2+t)^(n+d) * Real.exp (C*q*t)) * Real.exp (-(c*r^2/t)) :=
      mul_le_mul_of_nonneg_right hgrowth (Real.exp_pos _).le
    _ = _ := by
      rw [show C*q*t-c*r^2/t = C*q*t + (-(c*r^2/t)) by ring, Real.exp_add]
      ring

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal BigOperators

/-- Localized half-time smoothing produces a jointly C¹ kernel with a
full-time Gaussian estimate and an explicit structural prefactor. -/
theorem s3_large_time_split_of_localized {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) (hs : 0 < (s : ℝ))
    (hsplit : P (s+s) = (P s).comp (P s))
    (hsplitdag : Pdag (s+s) = (Pdag s).comp (Pdag s))
    (htranspose : ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (∫ x, P s f x * g x) = ∫ x, f x * Pdag s g x)
    (C c q : ℝ) (N : ℕ) (hC : 0 ≤ C)
    (hloc : ∀ T ∈ [P s, Pdag s], ∀ E : Set (Vec d), MeasurableSet E →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          C * (2+(s:ℝ))^N * Real.exp (C*q*(s:ℝ)-c*ell^2/(s:ℝ)) * ‖f‖) :
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (s+s) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) +
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤
        (4 * (1 + Real.sqrt d) * C^2) * (2+((s+s):ℝ))^(N+N) *
          Real.exp (C*q*((s+s):ℝ) - (c/2)*euclideanNorm (x-y)^2/((s+s):ℝ)) := by
  let A := C * (2+(s:ℝ))^N * Real.exp (C*q*(s:ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlocal : ∀ T ∈ [P s, Pdag s], ∀ E : Set (Vec d), MeasurableSet E →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          A * Real.exp (-(c/(s:ℝ)) * ell^2) * ‖f‖ := by
    intro T hT E hE f hf
    obtain ⟨u, hu, huf, hb⟩ := hloc T hT E hE f hf
    refine ⟨u, hu, huf, ?_⟩
    intro x ell hell hsep
    have he : C*q*(s:ℝ)-c*ell^2/(s:ℝ) =
        C*q*(s:ℝ) + (-(c/(s:ℝ))*ell^2) := by ring
    convert hb x ell hell hsep using 1; simp only [A, he, Real.exp_add]; ring
  obtain ⟨K, hpair, hjoint, hbound⟩ :=
    s3_split_kernel_of_localized_gaussian_normalized P Pdag s hsplit hsplitdag
      htranspose A (c/(s:ℝ)) hA hlocal
  refine ⟨K, hpair, hjoint, ?_⟩
  intro x y
  have hcoef := s3_half_time_smoothing_prefactor C q (s:ℝ) N d hs.le
  have hscale := s3_half_time_gaussian_scale c (s:ℝ) (euclideanNorm (x-y)) (ne_of_gt hs)
  calc
    _ ≤ (4 * (1 + Real.sqrt d) * A^2) *
        Real.exp (-((c/(s:ℝ))/4)*euclideanNorm (x-y)^2) := hbound x y
    _ ≤ ((4 * (1 + Real.sqrt d) * C^2) * (2+((s+s):ℝ))^(N+N) *
        Real.exp (C*q*((s+s):ℝ))) *
        Real.exp (-(c/2)*euclideanNorm (x-y)^2/((s+s):ℝ)) := by
          rw [hscale]
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          simpa only [A, NNReal.coe_add] using hcoef
    _ = _ := by
      rw [show C*q*((s+s):ℝ) - (c/2)*euclideanNorm (x-y)^2/((s+s):ℝ) =
        C*q*((s+s):ℝ) + (-(c/2)*euclideanNorm (x-y)^2/((s+s):ℝ)) by ring,
        Real.exp_add]
      ring

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory
open scoped NNReal BigOperators

/-- Choose compatible kernels at all positive times, with a quantitative
joint C¹ Gaussian estimate at times at least two. -/
theorem s3_all_time_kernel_of_localized {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (hsmooth : ∀ S ∈ [P,Pdag], ∀ s : ℝ≥0, 0 < s →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (S s f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖^2) ≤ A * ‖f‖)
    (C c : ℝ) (N : ℕ) (hC : 0 ≤ C)
    (hloc : ∀ S ∈ [P,Pdag], ∀ s : ℝ≥0, 1 ≤ (s:ℝ) →
      ∀ E : Set (Vec d), MeasurableSet E → ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
      ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧ u =ᵐ[volume] (S s f : Vec d → ℂ) ∧
      ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
        (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
        ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
          C * (2+(s:ℝ))^N * Real.exp (C*‖ζ‖^2*(s:ℝ)-c*ell^2/(s:ℝ)) * ‖f‖) :
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ, IsPhysicalComplexKernel P Pdag K ∧
      ∀ t : ℝ≥0, 2 ≤ (t:ℝ) →
        ContDiff ℝ 1 (fun z : Vec d × Vec d => K t z.1 z.2) ∧
        ∀ x y, ‖K t x y‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖^2) +
          Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector j)‖^2) ≤
          (4*(1+Real.sqrt d)*C^2) * (2+(t:ℝ))^(N+N) *
            Real.exp (C*‖ζ‖^2*(t:ℝ)-(c/2)*euclideanNorm (x-y)^2/(t:ℝ)) := by
  obtain ⟨Ksmall, hsmall, _⟩ :=
    s3_kernel_of_quantitative_smoothing a i ζ P Pdag hP hPdag hsmooth
  let R : ℝ≥0 → (Vec d → Vec d → ℂ) → Prop := fun t K =>
    ContDiff ℝ 1 (fun z : Vec d × Vec d => K z.1 z.2) ∧
      ∀ x y, ‖K x y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖^2) +
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖^2) ≤
        (4*(1+Real.sqrt d)*C^2) * (2+(t:ℝ))^(N+N) *
          Real.exp (C*‖ζ‖^2*(t:ℝ)-(c/2)*euclideanNorm (x-y)^2/(t:ℝ))
  apply s3_select_large_time_kernels P Pdag R
  · intro t ht
    exact ⟨Ksmall t, hsmall t ht⟩
  · intro t ht
    have hs : 0 < ((t/2 : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    have hs1 : 1 ≤ ((t/2 : ℝ≥0) : ℝ) := by
      simp only [NNReal.coe_div, NNReal.coe_ofNat]
      linarith
    obtain ⟨K, hpair, hK⟩ := s3_large_time_split_of_localized P Pdag (t/2)
      hs (hP.2.1 _ _) (hPdag.2.1 _ _) (hPdag.2.2.2.2 _)
      C c (‖ζ‖^2) N hC (by
        intro S hS
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
        rcases hS with rfl | rfl
        · exact hloc P (by simp) (t/2) hs1
        · exact hloc Pdag (by simp) (t/2) hs1)
    refine ⟨K, ?_, ?_⟩
    · simpa only [add_halves] using hpair
    · have ht2 : ((t/2 : ℝ≥0) : ℝ) + ((t/2 : ℝ≥0) : ℝ) = (t : ℝ) := by
        exact_mod_cast add_halves t
      simpa only [R, ht2] using hK

end EinsteinFull


namespace EinsteinFull
open EinsteinRelation MeasureTheory Blueprint
open scoped NNReal ENNReal BigOperators

/-- Quantitative C¹ smoothing and localized Gaussian estimates assemble the
physical point-kernel statement from its three original dependencies. -/
theorem s3_point_kernel_of_C1_and_deps
    (hC1 : ∀ (_hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (_htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (_hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (_hd : 2 ≤ d) (D : StructuralData d),
∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ env ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup env.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup env.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < (t : ℝ) →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d, ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖)
    (hloc : ∀ (d : ℕ), 2 ≤ d → ∀ D : StructuralData d,
  ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
  ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q → ∀ᵐ env ∂reducedLaw Q,
  ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
  ∀ P Pdag : ℝ≥0 → Lp ℂ 2 volume →L[ℂ] Lp ℂ 2 volume,
    IsPhysicalComplexSemigroup env.1 i ζ P →
    IsPhysicalComplexTransposeSemigroup env.1 i ζ P Pdag →
  ∀ S ∈ [P,Pdag], ∀ t : ℝ≥0, 1 ≤ (t:ℝ) →
  ∀ E : Set (Vec d), MeasurableSet E → ∀ f : Lp ℂ 2 volume,
    (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ x : Vec d, ∀ ell : ℝ, 0 ≤ ell →
      (∀ y ∈ E, ell ≤ euclideanNorm (x-y)) →
      ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖^2) ≤
      C * (2+(t:ℝ))^N *
      Real.exp (C*‖ζ‖^2*(t:ℝ)-c*ell^2/(t:ℝ)) * ‖f‖) :
  node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt →
  node_e_u3A_local_u2D_timeStmt → node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt →
  node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt := by
  intro hoff htime hder d hd D
  obtain ⟨C₁, N₁, hC₁, hc1⟩ := hC1 hoff htime hder d hd D
  obtain ⟨C₀, c₀, N₀, hC₀, hc₀, hlocalized⟩ := hloc d hd D
  let b := c₀ / 2
  let W : ℝ := 1 + Real.sqrt d
  let A : ℝ := 4 * W * C₀^2
  let M : ℝ := Real.sqrt (Real.pi / b)^d
  let C : ℝ := max 1 (max C₀ (max A (W*A*M)))
  have hb : 0 < b := by dsimp [b]; linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 1 ≤ C := le_max_left _ _
  have hC₀C : C₀ ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hAC : A ≤ C := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hWAMC : W*A*M ≤ C := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨C, b, N₀+N₀+d, hC, hb, ?_⟩
  intro Q hQ
  filter_upwards [hc1 Q hQ, hlocalized Q hQ] with env hsmooth hlocal
  intro i ζ hζ P Pdag hP hPdag
  have hsmooth' : ∀ S ∈ [P,Pdag], ∀ s : ℝ≥0, 0 < s →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
          u =ᵐ[volume] (S s f : Vec d → ℂ) ∧ ∀ x,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖^2) ≤ A * ‖f‖ := by
    intro S hS s hs
    refine ⟨C₁ * (1 + (s:ℝ)⁻¹)^N₁ * (2+(s:ℝ))^N₁ *
      Real.exp (C₁*‖ζ‖^2*(s:ℝ)), ?_, ?_⟩
    · positivity
    · exact hsmooth i ζ hζ P Pdag hP hPdag S hS s (by exact_mod_cast hs)
  obtain ⟨K, hpair, hlarge⟩ := s3_all_time_kernel_of_localized env.1 i ζ P Pdag
    hP hPdag hsmooth' C₀ c₀ N₀ (by linarith) (hlocal i ζ hζ P Pdag hP hPdag)
  refine ⟨K, hpair, ?_⟩
  intro H hH t ht
  have htpos : 0 < (t:ℝ) := by linarith
  let T : ℝ := (t:ℝ)
  let q : ℝ := ‖ζ‖^2
  let G : ℝ := A * (2+T)^(N₀+N₀) * Real.exp (C₀*q*T)
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hbt : 0 < b/T := div_pos hb htpos
  have hraw : ∀ x y, ‖K t x y‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖^2) +
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector j)‖^2) ≤
      G * Real.exp (-(b/T)*euclideanNorm (x-y)^2) := by
    intro x y
    convert (hlarge t ht).2 x y using 1; dsimp [G, A, W, b, T, q]
    rw [show C₀*‖ζ‖^2*(t:ℝ) - (c₀/2)*euclideanNorm (x-y)^2/(t:ℝ) =
      C₀*‖ζ‖^2*(t:ℝ) + (-(c₀/2)*euclideanNorm (x-y)^2/(t:ℝ)) by ring,
      Real.exp_add]
    ring
  have horient : (fun x y => H t x y) ∈ [K t, fun x y => K t y x] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hH ⊢
    rcases hH with rfl | rfl <;> simp
  obtain ⟨hjoint, hbound, haction⟩ :=
    s3_both_bounded_data_actions (K t) G (b/T) hG hbt (hlarge t ht).1 hraw _ horient
  refine ⟨hjoint, ?_, ?_⟩
  · intro x y
    apply (hbound x y).trans
    have h := s3_enlarge_gaussian_bound A C C₀ q T b (euclideanNorm (x-y))
      (N₀+N₀) d hA hAC hC₀C (by dsimp [q]; positivity) htpos.le
    convert h using 1; dsimp [G, T, q]
    rw [show C₀*‖ζ‖^2*(t:ℝ)-b*euclideanNorm (x-y)^2/(t:ℝ) =
      C₀*‖ζ‖^2*(t:ℝ) + (-(b/(t:ℝ))*euclideanNorm (x-y)^2) by ring,
      Real.exp_add]
    ring
  · intro f B hB hf hfb
    obtain ⟨hderiv, hbound⟩ := haction f B hB hf hfb
    refine ⟨hderiv, ?_⟩
    intro x
    obtain ⟨hint, hj, hestimate⟩ := hbound x
    refine ⟨hint, hj, hestimate.trans ?_⟩
    have hmass := s3_absorb_gaussian_mass (W*A) C C₀ q T b (N₀+N₀) d
      (mul_nonneg hW hA) hb htpos (by dsimp [q]; positivity)
      (by simpa [M] using hWAMC) hC₀C
    have hmassB := mul_le_mul_of_nonneg_right hmass hB
    convert hmassB using 1; dsimp [G, W, T, q]; ring


/-- The global interpolation and localized estimates give the point-kernel
reduction with its original three dependencies. -/
theorem s3_point_kernel_of_global_interpolation :
    node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt →
    node_e_u3A_local_u2D_timeStmt →
    node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt →
    node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt := by
  intro hoff htime hder
  exact s3_point_kernel_of_C1_and_deps
    (u4_physical_evolution_L2_C1_of_Sobolev
      u8_physical_high_weak_derivatives_C1_representative)
    (u4_physical_local_C1_gaussian_of_global_chain
      u8_global_C1_interpolation_of_weak_derivative_chain hoff hder)
    hoff htime hder


end EinsteinFull
