import EinsteinFull.Calculus.CarverSFluxGaussianGain
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Algebraic checks for transferring the actual stationary flux blocks to a
Gaussian-controlled Schwartz test. These lemmas do not assert the general-test
gain or extend the independent-block dependency to new cutoffs. -/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma c3_gaussian_kernel_ne_zero {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs 0 x ≠ 0 := by
  rw [homogenizedGaussianKernel_zero_eq_ofReal]
  apply Complex.ofReal_ne_zero.mpr
  apply ne_of_gt
  unfold anisotropicGaussian
  exact mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.sqrt_pos.mpr (det_homogenizedCoefficient_pos Q))) (Real.exp_pos _)

/-- Factoring a test by a nonvanishing kernel produces a different cutoff at
each block center. The spatial shift in the ratio is part of the identity. -/
lemma c3_test_block_ratio_identity {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (χ : Vec d → ℝ)
    (ψ : SchwartzMap (Vec d) ℂ) (i : Fin d) (s : ℝ) (hs : 0 < s) (z : Vec d)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    let kernel := homogenizedGaussianKernel Q i s hs 0
    (∫ y : Vec d, ((χ (y - z) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F) =
    ∫ y : Vec d,
      (((χ (y - z) : ℂ) * (ψ (-(y - z) - z) /
        kernel (-(y - z) - z))) * kernel (-y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F := by
  dsimp only
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    have hshift : -(y - z) - z = -y := by abel
    rw [hshift, mul_assoc, div_mul_cancel₀ _ (c3_gaussian_kernel_ne_zero Q i hs (-y))]

/-- If the ratio-modified blocks are all translates of one cutoff, then the
ratio has equal values on the corresponding lattice coset at every point
where the original cutoff is nonzero. -/
lemma c3_single_ratio_cutoff_requires_lattice_invariance {d : ℕ}
    (r : ℝ) (χ : Vec d → ℝ) (g θ : Vec d → ℂ)
    (htranslate : ∀ (z : Fin d → ℤ) (u : Vec d),
      θ u = (χ u : ℂ) * g (-u - fun j => r * (z j : ℝ)))
    (u : Vec d) (hu : χ u ≠ 0) (z : Fin d → ℤ) :
    g (-u - fun j => r * (z j : ℝ)) = g (-u) := by
  have hzero := htranslate (0 : Fin d → ℤ) u
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero] at hzero
  change θ u = (χ u : ℂ) * g (-u - (0 : Vec d)) at hzero
  rw [sub_zero] at hzero
  have he : (χ u : ℂ) * g (-u - fun j => r * (z j : ℝ)) =
      (χ u : ℂ) * g (-u) := (htranslate z u).symm.trans hzero
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hu) he

/-- Even a constant rescaling of the actual partition rescales its lattice
sum. A bound on the multiplying ratio alone does not supply V2's partition
identity. -/
lemma c3_scaled_flux_partition_tsum {d : ℕ} {r : ℝ} (hr : 0 < r)
    (c : ℝ) (y : Vec d) :
    (∑' z : Fin d → ℤ,
      c * fluxPartitionCutoff r (y - fun j => r * (z j : ℝ))) = c := by
  simpa only [mul_one] using
    ((flux_partition_cutoff_partition hr y).mul_left c).tsum_eq

/-- A lattice coboundary has zero sum, so it preserves the periodization of a
partition. Summability is the usual prerequisite for reindexing the series. -/
lemma c3_lattice_coboundary_hasSum_zero {d : ℕ}
    {E : Type*} [NormedAddCommGroup E]
    (f : (Fin d → ℤ) → E) (hf : Summable f) (v : Fin d → ℤ) :
    HasSum (fun z => f z - f (z + v)) 0 := by
  have hshift : HasSum (fun z => f (z + v)) (∑' z, f z) :=
    (Equiv.addRight v).hasSum_iff.mpr hf.hasSum
  simpa only [sub_self] using hf.hasSum.sub hshift

/-- A compactly supported function has a summable restriction to every
translated lattice with nonzero spacing. -/
lemma c3_compact_lattice_summable {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (h : Vec d → E) (hh : HasCompactSupport h) (r : ℝ) (hr : r ≠ 0)
    (y : Vec d) :
    Summable (fun z : Fin d → ℤ => h (y - fun i => r * (z i : ℝ))) := by
  have hcast : Topology.IsClosedEmbedding
      (fun z : Fin d → ℤ => fun i => (z i : ℝ)) :=
    Topology.IsClosedEmbedding.piMap (fun _ => Real.isClosedEmbedding_intCast)
  have hemb : Topology.IsClosedEmbedding
      (fun z : Fin d → ℤ => y - fun i => r * (z i : ℝ)) :=
    (Homeomorph.subLeft y).isClosedEmbedding.comp
      ((Homeomorph.smulOfNeZero r hr).isClosedEmbedding.comp hcast)
  have hcompact := hh.comp_isClosedEmbedding hemb
  exact summable_of_hasFiniteSupport
    (hcompact.finite_of_discrete.subset (subset_tsupport _))

/-- Spatial lattice differences of compact cutoffs have periodization zero. -/
lemma c3_compact_lattice_coboundary_hasSum_zero {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (h : Vec d → E) (hh : HasCompactSupport h)
    (r : ℝ) (hr : r ≠ 0) (y : Vec d) (v : Fin d → ℤ) :
    HasSum (fun z : Fin d → ℤ =>
      h (y - fun i => r * (z i : ℝ)) -
        h ((y - fun i => r * (z i : ℝ)) - fun i => r * (v i : ℝ))) 0 := by
  have hshift (z : Fin d → ℤ) :
      (y - fun i => r * (z i : ℝ)) - (fun i => r * (v i : ℝ)) =
        y - fun i => r * ((z + v) i : ℝ) := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Int.cast_add]
    ring
  simpa only [hshift] using
    c3_lattice_coboundary_hasSum_zero _ (c3_compact_lattice_summable h hh r hr y) v

/-- Adding a compact lattice coboundary to the actual partition preserves its
sum exactly. Cutoff size and derivative bounds are separate requirements. -/
lemma c3_flux_partition_perturbation_hasSum {d : ℕ} (h : Vec d → ℝ)
    (hh : HasCompactSupport h) {r : ℝ} (hr : 0 < r)
    (y : Vec d) (v : Fin d → ℤ) (c : ℝ) :
    HasSum (fun z : Fin d → ℤ =>
      fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) +
        c * (h (y - fun i => r * (z i : ℝ)) -
          h ((y - fun i => r * (z i : ℝ)) - fun i => r * (v i : ℝ)))) 1 := by
  simpa only [mul_zero, add_zero] using
    (flux_partition_cutoff_partition hr y).add
      ((c3_compact_lattice_coboundary_hasSum_zero h hh r hr.ne' y v).mul_left c)

/-- Two distinct lattice translates are part of the same nonnegative
partition, so their pointwise sum is at most one. -/
lemma c3_flux_partition_two_translate_le_one {d : ℕ} {r : ℝ} (hr : 0 < r)
    (j : Fin d) (u : Vec d) :
    fluxPartitionCutoff r u +
      fluxPartitionCutoff r (u - r • unitVector j) ≤ 1 := by
  classical
  let e : Fin d → ℤ := Pi.single j 1
  have he : (0 : Fin d → ℤ) ≠ e := by
    intro heq
    have hj := congrFun heq j
    exact (zero_ne_one : (0 : ℤ) ≠ 1) (by
      simpa only [e, Pi.zero_apply, Pi.single_eq_same] using hj)
  have hcenter : (fun k => r * (e k : ℝ)) = r • unitVector j := by
    ext k
    simp [e, unitVector, Pi.single_apply]
  have hzero : (fun k => r * ((0 : Fin d → ℤ) k : ℝ)) = (0 : Vec d) := by
    ext k
    simp only [Pi.zero_apply, Int.cast_zero, mul_zero]
  have hsum := flux_partition_cutoff_partition hr u
  have htwo := hsum.summable.sum_le_tsum {0, e}
    (fun z _ => flux_partition_cutoff_nonneg r (u - fun k => r * (z k : ℝ)))
  rw [hsum.tsum_eq] at htwo
  simpa only [Finset.sum_pair he, hzero, sub_zero, hcenter] using htwo

/-- Averaging two lattice translates leaves a uniform amplitude margin for
the zero-periodization perturbations used above. -/
lemma c3_flux_partition_average_abs_le_half {d : ℕ} {r : ℝ} (hr : 0 < r)
    (j : Fin d) (u : Vec d) :
    |(fluxPartitionCutoff r u +
      fluxPartitionCutoff r (u - r • unitVector j)) / 2| ≤ 1 / 2 := by
  have hnonneg := add_nonneg (flux_partition_cutoff_nonneg r u)
    (flux_partition_cutoff_nonneg r (u - r • unitVector j))
  rw [abs_of_nonneg (div_nonneg hnonneg (by norm_num))]
  exact div_le_div_of_nonneg_right (c3_flux_partition_two_translate_le_one hr j u)
    (by norm_num)

/-- The first derivative of the actual Gaussian converts two cutoff
coboundaries into a local multiplier. This identity is the algebraic step
needed to recover general tests while preserving partition periodization. -/
lemma c3_gaussian_derivative_coboundary_identity {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (h : Vec d → ℂ) (u v : Vec d) :
    let kernel := homogenizedGaussianKernel Q i s hs 0
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    fderiv ℝ kernel (-u) (unitVector j) * (h u - h (u - v)) -
        kernel (-u) * (slope u * h u - slope (u - v) * h (u - v)) =
      -slope v * kernel (-u) * h (u - v) := by
  dsimp only
  rw [fderiv_homogenizedGaussianKernel_zero_coordinate,
    Matrix.mulVec_neg, Pi.neg_apply, neg_neg,
    Matrix.mulVec_sub, Pi.sub_apply]
  push_cast
  ring

/-- Every local multiplier is recovered algebraically from two cutoff
coboundaries against the actual Gaussian and its first derivative. The shift
is one lattice step in coordinate `j`; its slope is nonzero by ellipticity. -/
lemma c3_gaussian_derivative_recovers_cutoff {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) (f : Vec d → ℂ) (u : Vec d) :
    let kernel := homogenizedGaussianKernel Q i s hs 0
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let v := r • unitVector j
    let h := fun w : Vec d => f (w + v) / (slope v * kernel (-(w + v)))
    kernel (-u) * (slope u * h u - slope (u - v) * h (u - v)) -
      fderiv ℝ kernel (-u) (unitVector j) * (h u - h (u - v)) = f u := by
  let kernel := homogenizedGaussianKernel Q i s hs 0
  let slope := fun w : Vec d =>
    ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
  let v := r • unitVector j
  let h := fun w : Vec d => f (w + v) / (slope v * kernel (-(w + v)))
  change kernel (-u) * (slope u * h u - slope (u - v) * h (u - v)) -
    fderiv ℝ kernel (-u) (unitVector j) * (h u - h (u - v)) = f u
  have hentry : ((homogenizedCoefficient Q)⁻¹).mulVec v j =
      r * ((homogenizedCoefficient Q)⁻¹) j j := by
    dsimp only [v]
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have hslope : slope v ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    rw [hentry]
    exact (div_pos (mul_pos hr (posDef_homogenizedCoefficient Q).inv.diag_pos) hs).ne'
  have hkernel : kernel (-u) ≠ 0 := c3_gaussian_kernel_ne_zero Q i hs (-u)
  have hcancel : (slope v * kernel (-u)) * h (u - v) = f u := by
    dsimp only [h]
    rw [sub_add_cancel]
    exact mul_div_cancel₀ _ (mul_ne_zero hslope hkernel)
  have hidentity := c3_gaussian_derivative_coboundary_identity Q i j s hs h u v
  change fderiv ℝ kernel (-u) (unitVector j) * (h u - h (u - v)) -
    kernel (-u) * (slope u * h u - slope (u - v) * h (u - v)) =
      -slope v * kernel (-u) * h (u - v) at hidentity
  calc
    _ = -(-slope v * kernel (-u) * h (u - v)) := by rw [← hidentity]; ring
    _ = (slope v * kernel (-u)) * h (u - v) := by ring
    _ = f u := hcancel

/-- The quotient used to recover a local multiplier retains compact support;
the denominator introduces no additional support. -/
lemma c3_shifted_gaussian_quotient_hasCompactSupport {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (hf : HasCompactSupport f) (v : Vec d) (c : ℂ) :
    HasCompactSupport (fun w : Vec d =>
      f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))) := by
  apply (hf.comp_homeomorph (Homeomorph.addRight v)).mono
  intro w hw
  change f (w + v) ≠ 0
  intro hz
  apply hw
  change f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v))) = 0
  rw [hz, zero_div]

/-- The linear slope in the actual Gaussian derivative is smooth on the
original coordinate carrier. -/
lemma c3_gaussian_slope_contDiff {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)) := by
  unfold Matrix.mulVec dotProduct
  fun_prop

/-- The shifted quotient in the recovery identity is smooth when its constant
factor is nonzero. Positivity of the actual Gaussian handles every point. -/
lemma c3_shifted_gaussian_quotient_contDiff {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d)
    (c : ℂ) (hc : c ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d =>
      f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))) := by
  have hshift : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => w + v) :=
    contDiff_id.add contDiff_const
  have hkernel := (contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0).comp
    hshift.neg
  simpa only [div_eq_mul_inv] using! (hf.comp hshift).mul
    ((contDiff_const.mul hkernel).inv fun w =>
      mul_ne_zero hc (c3_gaussian_kernel_ne_zero Q i hs (-(w + v))))

/-- Both complex coboundaries appearing in the recovery identity are smooth
and compactly supported. This assertion introduces no bounds depending on a
chosen environment or a chosen test. -/
lemma c3_gaussian_recovery_coboundaries_regular {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (v : Vec d) (c : ℂ) (hc : c ≠ 0) :
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let h := fun w : Vec d =>
      f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))
    ContDiff ℝ (⊤ : ℕ∞) (fun w => h w - h (w - v)) ∧
      HasCompactSupport (fun w => h w - h (w - v)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun w => slope w * h w - slope (w - v) * h (w - v)) ∧
      HasCompactSupport (fun w => slope w * h w - slope (w - v) * h (w - v)) := by
  dsimp only
  have hh := c3_shifted_gaussian_quotient_contDiff Q i s hs f hf v c hc
  have hhc := c3_shifted_gaussian_quotient_hasCompactSupport Q i s hs f hfc v c
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => w - v) :=
    contDiff_id.sub contDiff_const
  have hsh := (c3_gaussian_slope_contDiff Q j s).mul hh
  have hshc : HasCompactSupport (fun w : Vec d =>
      (((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)) *
        (f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v))))) :=
    hhc.mul_left
  exact ⟨hh.sub (hh.comp hsub),
    hhc.sub (hhc.comp_homeomorph (Homeomorph.subRight v)),
    hsh.sub (hsh.comp hsub),
    hshc.sub (hshc.comp_homeomorph (Homeomorph.subRight v))⟩

/-- The recovery differences enlarge the local multiplier's support by at
most one lattice step. Multiplication by the Gaussian slope adds no support. -/
lemma c3_gaussian_recovery_coboundaries_support {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (ρ : ℝ)
    (hf : Function.support f ⊆ {w : Vec d | euclideanNorm w ≤ ρ})
    (v : Vec d) (c : ℂ) :
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let h := fun w : Vec d =>
      f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))
    Function.support (fun w => h w - h (w - v)) ⊆
        {w : Vec d | euclideanNorm w ≤ ρ + euclideanNorm v} ∧
      Function.support (fun w => slope w * h w - slope (w - v) * h (w - v)) ⊆
        {w : Vec d | euclideanNorm w ≤ ρ + euclideanNorm v} := by
  dsimp only
  have hvanish (w : Vec d) (hw : ¬euclideanNorm w ≤ ρ + euclideanNorm v) :
      f w = 0 ∧ f (w + v) = 0 := by
    constructor
    · by_contra hfw
      exact hw ((hf hfw).trans (le_add_of_nonneg_right (Real.sqrt_nonneg _)))
    · by_contra hfw
      apply hw
      have htri := TimeChange.euclideanNorm_add_le (w + v) (-v)
      have hneg : euclideanNorm (-v) = euclideanNorm v := by
        simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
          TimeChange.euclideanNorm_smul (-1 : ℝ) v
      have hfρ : euclideanNorm (w + v) ≤ ρ := hf hfw
      calc
        euclideanNorm w = euclideanNorm ((w + v) + (-v)) := by
          rw [add_neg_cancel_right]
        _ ≤ euclideanNorm (w + v) + euclideanNorm (-v) := htri
        _ = euclideanNorm (w + v) + euclideanNorm v := by rw [hneg]
        _ ≤ ρ + euclideanNorm v := add_le_add hfρ le_rfl
  constructor <;> intro w hw <;> by_contra hout
  all_goals
    obtain ⟨hfw, hfv⟩ := hvanish w hout
    exact hw (by simp only [hfv, sub_add_cancel, hfw, zero_div, mul_zero, sub_self])

/-- Differentiating the actual shifted quotient retains the inverse covariance
and the constant normalization. The two shifts in the denominator are literal. -/
lemma c3_shifted_gaussian_quotient_fderiv_coordinate {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d)
    (c : ℂ) (hc : c ≠ 0) (w : Vec d) :
    fderiv ℝ (fun u : Vec d =>
        f (u + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(u + v)))) w
        (unitVector j) =
      fderiv ℝ f (w + v) (unitVector j) /
          (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v))) +
        (((((homogenizedCoefficient Q)⁻¹).mulVec (w + v) j / s : ℝ) : ℂ)) *
          (f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))) := by
  let kernel := homogenizedGaussianKernel Q i s hs 0
  have hshift : DifferentiableAt ℝ (fun u : Vec d => u + v) w :=
    differentiableAt_id.add_const v
  have hneg := hshift.neg
  have hnegder : fderiv ℝ (fun u : Vec d => -(u + v)) w =
      -ContinuousLinearMap.id ℝ (Vec d) :=
    ((hasFDerivAt_id w).add_const v).neg.fderiv
  have hK := ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0).differentiable
    (by simp)).differentiableAt (x := -(w + v))
  have hfs := ((hf.differentiable (by simp)).differentiableAt (x := w + v)).comp w hshift
  have hKs := hK.comp w hneg
  have hden := hKs.const_mul c
  have hn := mul_ne_zero hc (c3_gaussian_kernel_ne_zero Q i hs (-(w + v)))
  have hi := (differentiableAt_inv (𝕜 := ℝ) hn).comp w hden
  have hfsder : fderiv ℝ (fun u : Vec d => f (u + v)) w (unitVector j) =
      fderiv ℝ f (w + v) (unitVector j) := by
    rw [fderiv_fun_comp w ((hf.differentiable (by simp)).differentiableAt) hshift]
    simp only [fderiv_add_const, fderiv_fun_id, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply]
  have hKsder : fderiv ℝ (fun u : Vec d => kernel (-(u + v))) w (unitVector j) =
      -(((((homogenizedCoefficient Q)⁻¹).mulVec (w + v) j / s : ℝ) : ℂ)) *
        kernel (-(w + v)) := by
    dsimp only [kernel]
    erw [fderiv_fun_comp w hK hneg]
    change fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-(w + v))
      (fderiv ℝ (fun u : Vec d => -(u + v)) w (unitVector j)) = _
    rw [hnegder]
    simp only [neg_apply, ContinuousLinearMap.id_apply, map_neg]
    rw [fderiv_homogenizedGaussianKernel_zero_coordinate,
      Matrix.mulVec_neg, Pi.neg_apply]
    push_cast
    ring
  simp only [div_eq_mul_inv]
  erw [fderiv_fun_mul hfs hi, fderiv_comp w (differentiableAt_inv hn) hden,
    fderiv_inv' hn]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, Function.comp_apply]
  change f (w + v) *
      -((c * kernel (-(w + v)))⁻¹ *
        fderiv ℝ (fun u : Vec d => c * kernel (-(u + v))) w (unitVector j) *
        (c * kernel (-(w + v)))⁻¹) +
      (c * kernel (-(w + v)))⁻¹ *
        fderiv ℝ (fun u : Vec d => f (u + v)) w (unitVector j) = _
  rw [hfsder]
  erw [fderiv_const_mul hKs c]
  simp only [smul_apply, smul_eq_mul]
  erw [hKsder]
  dsimp only [kernel] at *
  field_simp [hn]
  ring

/-- The pointwise size of the recovery quotient displays its normalization
and its actual Gaussian denominator explicitly. -/
lemma c3_shifted_gaussian_quotient_norm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (v : Vec d) (c : ℂ) (w : Vec d) :
    ‖f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))‖ =
      ‖f (w + v)‖ / (‖c‖ * ‖homogenizedGaussianKernel Q i s hs 0 (-(w + v))‖) := by
  rw [norm_div, norm_mul]

/-- The quotient derivative estimate keeps the actual inverse-covariance
slope and every scale factor. It is a pointwise estimate, before normalization
to a real partition perturbation. -/
lemma c3_shifted_gaussian_quotient_fderiv_norm_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d)
    (c : ℂ) (hc : c ≠ 0) (w : Vec d) :
    ‖fderiv ℝ (fun u : Vec d =>
        f (u + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(u + v)))) w
        (unitVector j)‖ ≤
      (‖fderiv ℝ f (w + v) (unitVector j)‖ +
          |((homogenizedCoefficient Q)⁻¹).mulVec (w + v) j / s| * ‖f (w + v)‖) /
        (‖c‖ * ‖homogenizedGaussianKernel Q i s hs 0 (-(w + v))‖) := by
  rw [c3_shifted_gaussian_quotient_fderiv_coordinate Q i j s hs f hf v c hc w]
  calc
    _ ≤ ‖fderiv ℝ f (w + v) (unitVector j) /
          (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))‖ +
        ‖(((((homogenizedCoefficient Q)⁻¹).mulVec (w + v) j / s : ℝ) : ℂ)) *
          (f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v))))‖ :=
      norm_add_le _ _
    _ = _ := by
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        norm_div, norm_mul]
      ring

/-- The normalization in the actual recovery identity has size proportional
to the lattice spacing divided by the auxiliary Gaussian time. -/
lemma c3_gaussian_slope_lattice_step_norm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) :
    ‖(((((homogenizedCoefficient Q)⁻¹).mulVec (r • unitVector j) j / s : ℝ) : ℂ))‖ =
      r * ((homogenizedCoefficient Q)⁻¹) j j / s := by
  have hentry : ((homogenizedCoefficient Q)⁻¹).mulVec (r • unitVector j) j =
      r * ((homogenizedCoefficient Q)⁻¹) j j := by
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    congr 1
    simp only [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Complex.norm_real, Real.norm_eq_abs, hentry,
    abs_of_pos (div_pos (mul_pos hr (posDef_homogenizedCoefficient Q).inv.diag_pos) hs)]

/-- The inverse normalization has the explicit Gaussian-time over
lattice-spacing loss; ellipticity controls the remaining diagonal factor. -/
lemma c3_gaussian_slope_lattice_step_inv_norm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) :
    ‖(((((homogenizedCoefficient Q)⁻¹).mulVec (r • unitVector j) j / s : ℝ) : ℂ))‖⁻¹ =
      s / (r * ((homogenizedCoefficient Q)⁻¹) j j) := by
  rw [c3_gaussian_slope_lattice_step_norm Q j s hs r hr, inv_div]

/-- Ellipticity bounds the inverse recovery normalization uniformly in the
environment law, with precisely the auxiliary-time over lattice-spacing loss. -/
lemma c3_gaussian_slope_lattice_step_inv_norm_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) :
    ‖(((((homogenizedCoefficient Q)⁻¹).mulVec (r • unitVector j) j / s : ℝ) : ℂ))‖⁻¹ ≤
      sourceReducedBound Λ * (s / r) := by
  have hlow : (sourceReducedBound Λ)⁻¹ ≤ ((homogenizedCoefficient Q)⁻¹) j j := by
    simpa [unitVector, euclideanSq, dot, Matrix.mulVec, dotProduct,
      Pi.single_apply, mul_ite, ite_mul] using
      (homogenizedCoefficient_inv_quadratic_bounds Q (unitVector j)).1
  have hinv : (((homogenizedCoefficient Q)⁻¹) j j)⁻¹ ≤ sourceReducedBound Λ := by
    have hK : 0 < sourceReducedBound Λ := by
      unfold sourceReducedBound
      exact mul_pos (Real.exp_pos _)
        (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
    simpa only [one_div, inv_inv] using
      one_div_le_one_div_of_le (inv_pos.mpr hK) hlow
  rw [c3_gaussian_slope_lattice_step_inv_norm Q j s hs r hr]
  calc
    s / (r * ((homogenizedCoefficient Q)⁻¹) j j) =
        (((homogenizedCoefficient Q)⁻¹) j j)⁻¹ * (s / r) := by ring
    _ ≤ sourceReducedBound Λ * (s / r) :=
      mul_le_mul_of_nonneg_right hinv (div_nonneg hs.le hr.le)

/-- A multiplier in the canonical partition's sharp support gives recovery
coboundaries inside the larger radius allowed by independent blocks. -/
lemma c3_gaussian_recovery_coboundaries_lattice_support {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr : 0 < r) (f : Vec d → ℂ)
    (hf : Function.support f ⊆
      {w : Vec d | euclideanNorm w ≤ 2 * Real.sqrt (d : ℝ) * r}) (c : ℂ) :
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let v := r • unitVector j
    let h := fun w : Vec d =>
      f (w + v) / (c * homogenizedGaussianKernel Q i s hs 0 (-(w + v)))
    Function.support (fun w => h w - h (w - v)) ⊆
        {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      Function.support (fun w => slope w * h w - slope (w - v) * h (w - v)) ⊆
        {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
  have hb := c3_gaussian_recovery_coboundaries_support Q i j s hs f
    (2 * Real.sqrt (d : ℝ) * r) hf (r • unitVector j) c
  have hv : euclideanNorm (r • unitVector j) = r := by
    rw [TimeChange.euclideanNorm_smul, euclideanNorm_unitVector_eq_one,
      abs_of_pos hr, mul_one]
  have hrad : 2 * Real.sqrt (d : ℝ) * r + euclideanNorm (r • unitVector j) ≤
      (2 * Real.sqrt (d : ℝ) + 2) * r := by
    rw [hv]
    linarith
  exact ⟨fun _ hw => (hb.1 hw).trans hrad, fun _ hw => (hb.2 hw).trans hrad⟩

/-- The inverse actual Gaussian has the expected positive quadratic
exponent. This formula is used only on the compact recovery support. -/
lemma c3_gaussian_kernel_inv_norm {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    ‖homogenizedGaussianKernel Q i s hs 0 x‖⁻¹ =
      (2 * Real.pi * s) ^ ((d : ℝ) / 2) *
        Real.sqrt (homogenizedCoefficient Q).det *
          Real.exp (dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) / (2 * s)) := by
  have hpos : 0 < anisotropicGaussian (homogenizedCoefficient Q) s x := by
    unfold anisotropicGaussian
    exact mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _)
      (Real.sqrt_pos.mpr (det_homogenizedCoefficient_pos Q))) (Real.exp_pos _)
  rw [homogenizedGaussianKernel_zero_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hpos]
  have hp : (2 * Real.pi * s) ^ (-(d : ℝ) / 2) =
      ((2 * Real.pi * s) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi * s)]
    congr 1
    ring
  have he : -(∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) /
      (2 * s) = -(dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) / (2 * s)) := by
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    ring
  unfold anisotropicGaussian
  rw [hp, he, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

/-- On a ball of radius a fixed multiple of the Gaussian length, its inverse
is bounded by the dimensional scale, uniformly over the actual environment
law. In particular the recovery construction introduces no exponential loss
in the lattice spacing when auxiliary time is its square. -/
lemma c3_gaussian_kernel_local_inv_norm_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (R : ℝ) (x : Vec d) (hx : euclideanNorm x ≤ R * Real.sqrt s) :
    ‖homogenizedGaussianKernel Q i s hs 0 x‖⁻¹ ≤
      ((2 * Real.pi) ^ ((d : ℝ) / 2) *
        Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
        Real.exp (sourceReducedBound Λ * R ^ 2 / 2)) * s ^ ((d : ℝ) / 2) := by
  have hK : 0 < sourceReducedBound Λ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _)
      (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
  have hsq : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hx2 : euclideanSq x ≤ R ^ 2 * s := by
    rw [← hsq]
    calc
      _ ≤ (R * Real.sqrt s) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hx 2
      _ = R ^ 2 * s := by rw [mul_pow, Real.sq_sqrt hs.le]
  have hq := (homogenizedCoefficient_inv_quadratic_bounds Q x).2.trans
    (mul_le_mul_of_nonneg_left hx2 hK.le)
  have hqdiv : dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) / (2 * s) ≤
      sourceReducedBound Λ * R ^ 2 / 2 := by
    calc
      _ ≤ (sourceReducedBound Λ * (R ^ 2 * s)) / (2 * s) :=
        div_le_div_of_nonneg_right hq (by positivity)
      _ = _ := by field_simp [hs.ne']
  have hdet : Real.sqrt (homogenizedCoefficient Q).det ≤
      Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) := by
    apply Real.sqrt_le_sqrt
    have hcoord (y : Vec d) (j : Fin d) : |y j| ≤ euclideanNorm y := by
      have hysq : euclideanNorm y ^ 2 = euclideanSq y := by
        apply Real.sq_sqrt
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun k _ => mul_self_nonneg (y k)
      apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
      rw [sq_abs]
      change y j ^ 2 ≤ euclideanNorm y ^ 2
      rw [hysq]
      simpa only [euclideanSq, dot, pow_two] using
        Finset.single_le_sum (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)
    have hentry (j k : Fin d) : |homogenizedCoefficient Q j k| ≤ sourceReducedBound Λ := by
      have hb := (hcoord ((homogenizedCoefficient Q).mulVec (unitVector k)) j).trans
        (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
      simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using hb
    exact (le_abs_self _).trans (by
      simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using!
        Matrix.det_le (abv := AbsoluteValue.abs) hentry)
  rw [c3_gaussian_kernel_inv_norm Q i s hs x]
  calc
    _ ≤ (2 * Real.pi * s) ^ ((d : ℝ) / 2) *
        Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
          Real.exp (sourceReducedBound Λ * R ^ 2 / 2) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left hdet (Real.rpow_nonneg (by positivity) _))
        (Real.exp_le_exp.mpr hqdiv) (Real.exp_pos _).le (by positivity)
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ 2 * Real.pi) hs.le]
      ring

/-- At auxiliary time equal to the squared lattice spacing, the inverse
Gaussian on the local support costs exactly a factor `r ^ d`. -/
lemma c3_gaussian_kernel_lattice_inv_norm_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (r : ℝ) (hr : 0 < r)
    (R : ℝ) (x : Vec d) (hx : euclideanNorm x ≤ R * r) :
    ‖homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 x‖⁻¹ ≤
      ((2 * Real.pi) ^ ((d : ℝ) / 2) *
        Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
        Real.exp (sourceReducedBound Λ * R ^ 2 / 2)) * r ^ d := by
  have hscale : (r ^ 2) ^ ((d : ℝ) / 2) = r ^ d := by
    calc
      _ = (r ^ (2 : ℝ)) ^ ((d : ℝ) / 2) :=
        congrArg (fun t : ℝ => t ^ ((d : ℝ) / 2)) (Real.rpow_natCast r 2).symm
      _ = r ^ ((2 : ℝ) * ((d : ℝ) / 2)) :=
        (Real.rpow_mul hr.le _ _).symm
      _ = r ^ (d : ℝ) := by congr 1; ring
      _ = r ^ d := Real.rpow_natCast _ _
  simpa only [hscale] using c3_gaussian_kernel_local_inv_norm_le Q i (r ^ 2)
    (sq_pos_of_pos hr) R x (by simpa only [Real.sqrt_sq hr.le] using hx)

/-- The actual recovery quotient has a uniform amplitude bound. The displayed
constant depends only on dimension, ellipticity and the support radius ratio;
the spacing loss beyond the Gaussian volume factor is a single factor `r`. -/
lemma c3_gaussian_recovery_quotient_amplitude_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (r : ℝ) (hr : 0 < r)
    (R A : ℝ) (hA : 0 ≤ A) (f : Vec d → ℂ)
    (hf : Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ R * r})
    (hval : ∀ x, ‖f x‖ ≤ A) (w : Vec d) :
    let s := r ^ 2
    let v := r • unitVector j
    let c : ℂ := ((((homogenizedCoefficient Q)⁻¹).mulVec v j / s : ℝ) : ℂ)
    ‖f (w + v) / (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))‖ ≤
      ((2 * Real.pi) ^ ((d : ℝ) / 2) *
        Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
        Real.exp (sourceReducedBound Λ * R ^ 2 / 2)) *
          sourceReducedBound Λ * A * r ^ (d + 1) := by
  let E := (2 * Real.pi) ^ ((d : ℝ) / 2) *
    Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
    Real.exp (sourceReducedBound Λ * R ^ 2 / 2)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 < sourceReducedBound Λ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _)
      (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
  dsimp only
  by_cases hfw : f (w + r • unitVector j) = 0
  · rw [hfw, zero_div, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hE hK.le) hA) (pow_nonneg hr.le _)
  have hx : euclideanNorm (-(w + r • unitVector j)) ≤ R * r := by
    have hneg : euclideanNorm (-(w + r • unitVector j)) =
        euclideanNorm (w + r • unitVector j) := by
      simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
        TimeChange.euclideanNorm_smul (-1 : ℝ) (w + r • unitVector j)
    rw [hneg]
    exact hf hfw
  have hk := c3_gaussian_kernel_lattice_inv_norm_le Q i r hr R
    (-(w + r • unitVector j)) hx
  have hrdiv : r ^ 2 / r = r := by field_simp [hr.ne']
  have hc := c3_gaussian_slope_lattice_step_inv_norm_le Q j (r ^ 2)
    (sq_pos_of_pos hr) r hr
  rw [hrdiv] at hc
  calc
    _ = ‖f (w + r • unitVector j)‖ *
        ‖homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0
          (-(w + r • unitVector j))‖⁻¹ *
        ‖(((((homogenizedCoefficient Q)⁻¹).mulVec (r • unitVector j) j / r ^ 2 : ℝ) : ℂ))‖⁻¹ := by
      rw [norm_div, norm_mul]
      ring
    _ ≤ A * (E * r ^ d) * (sourceReducedBound Λ * r) :=
      mul_le_mul
        (mul_le_mul (hval _) hk (inv_nonneg.mpr (norm_nonneg _)) hA)
        hc (inv_nonneg.mpr (norm_nonneg _))
        (mul_nonneg hA (mul_nonneg hE (pow_nonneg hr.le _)))
    _ = E * sourceReducedBound Λ * A * r ^ (d + 1) := by rw [pow_succ]; ring

/-- Differentiation does not enlarge a closed Euclidean support bound. -/
lemma c3_fderiv_support_euclidean_ball {d : ℕ} (f : Vec d → ℂ) (ρ : ℝ)
    (hf : Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ ρ}) (v : Vec d) :
    Function.support (fun x => fderiv ℝ f x v) ⊆
      {x : Vec d | euclideanNorm x ≤ ρ} := by
  have hclosed : IsClosed {x : Vec d | euclideanNorm x ≤ ρ} := by
    apply isClosed_le _ continuous_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  intro x hx
  exact closure_minimal hf hclosed
    ((tsupport_fderiv_apply_subset ℝ v) (subset_closure hx))

/-- Coordinate bounds control the Euclidean length of a complex gradient. -/
lemma c3_complex_coordinate_length_le {d : ℕ} (v : Fin d → ℂ)
    (A : ℝ) (hA : 0 ≤ A) (hv : ∀ j, ‖v j‖ ≤ A) :
    Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt (d : ℝ) * A := by
  calc
    _ ≤ Real.sqrt (∑ _j : Fin d, A ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2
    _ = Real.sqrt (d : ℝ) * A := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hA]

/-- The inverse covariance controls the actual Gaussian logarithmic slope. -/
lemma c3_gaussian_slope_coordinate_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    |((homogenizedCoefficient Q)⁻¹).mulVec x j / s| ≤
      sourceReducedBound Λ * euclideanNorm x / s := by
  rw [abs_div, abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  have hc : |((homogenizedCoefficient Q)⁻¹).mulVec x j| ≤
      euclideanNorm ((homogenizedCoefficient Q)⁻¹.mulVec x) := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm ((homogenizedCoefficient Q)⁻¹.mulVec x) j).trans
        (norm_vec_le_euclideanNorm _)
  exact hc.trans (homogenizedCoefficient_inv_mulVec_bound Q x)

/-- The coordinate derivative of the linear Gaussian slope is the literal
inverse-covariance entry divided by time. -/
lemma c3_gaussian_slope_fderiv_coordinate {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j k : Fin d) (s : ℝ) (w : Vec d) :
    fderiv ℝ (fun x : Vec d =>
        ((((homogenizedCoefficient Q)⁻¹).mulVec x j / s : ℝ) : ℂ)) w (unitVector k) =
      ((((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ) := by
  let L : Vec d →L[ℝ] ℂ := ∑ l : Fin d,
    (((((homogenizedCoefficient Q)⁻¹) j l / s : ℝ) : ℂ)) •
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj l))
  have he : (fun x : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec x j / s : ℝ) : ℂ)) = L := by
    ext x
    simp only [L, sum_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
      Finset.sum_div, Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, L.hasFDerivAt.fderiv]
  simp [L, unitVector, Pi.single_apply, apply_ite]

/-- The quotient's coordinate derivatives have the expected volume factor
at auxiliary time `r ^ 2`. Both the test derivative and inverse-covariance
slope contributions are retained. -/
lemma c3_gaussian_recovery_quotient_fderiv_le {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i j : Fin d) (r : ℝ) (hr : 0 < r)
    (R A B : ℝ) (hR : 0 ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfs : Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ R * r})
    (hval : ∀ x, ‖f x‖ ≤ A)
    (hgrad : ∀ x k, ‖fderiv ℝ f x (unitVector k)‖ ≤ B / r)
    (w : Vec d) (k : Fin d) :
    let s := r ^ 2
    let v := r • unitVector j
    let c : ℂ := ((((homogenizedCoefficient Q)⁻¹).mulVec v j / s : ℝ) : ℂ)
    let E := (2 * Real.pi) ^ ((d : ℝ) / 2) *
      Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
      Real.exp (sourceReducedBound Λ * R ^ 2 / 2)
    ‖fderiv ℝ (fun u : Vec d =>
        f (u + v) / (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(u + v))))
        w (unitVector k)‖ ≤
      E * sourceReducedBound Λ * (B + sourceReducedBound Λ * R * A) * r ^ d := by
  let E := (2 * Real.pi) ^ ((d : ℝ) / 2) *
    Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ) ^ d) *
    Real.exp (sourceReducedBound Λ * R ^ 2 / 2)
  let v := r • unitVector j
  let c : ℂ := ((((homogenizedCoefficient Q)⁻¹).mulVec v j / r ^ 2 : ℝ) : ℂ)
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hK : 0 < sourceReducedBound Λ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
  have hc : c ≠ 0 := by
    apply norm_pos_iff.mp
    rw [c3_gaussian_slope_lattice_step_norm Q j (r ^ 2) (sq_pos_of_pos hr) r hr]
    exact div_pos (mul_pos hr (posDef_homogenizedCoefficient Q).inv.diag_pos)
      (sq_pos_of_pos hr)
  change ‖fderiv ℝ (fun u : Vec d => f (u + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(u + v))))
    w (unitVector k)‖ ≤ _
  by_cases hx : euclideanNorm (w + v) ≤ R * r
  · have hneg : euclideanNorm (-(w + v)) = euclideanNorm (w + v) := by
      simpa only [neg_one_smul, abs_neg, abs_one, one_mul] using
        TimeChange.euclideanNorm_smul (-1 : ℝ) (w + v)
    have hk := c3_gaussian_kernel_lattice_inv_norm_le Q i r hr R (-(w + v))
      (by simpa only [hneg] using hx)
    have hc' := c3_gaussian_slope_lattice_step_inv_norm_le Q j (r ^ 2)
      (sq_pos_of_pos hr) r hr
    have hrdiv : r ^ 2 / r = r := by field_simp [hr.ne']
    rw [hrdiv] at hc'
    have hslope : |((homogenizedCoefficient Q)⁻¹).mulVec (w + v) k / r ^ 2| ≤
        sourceReducedBound Λ * R / r := by
      calc
        _ ≤ sourceReducedBound Λ * euclideanNorm (w + v) / r ^ 2 :=
          c3_gaussian_slope_coordinate_le Q k (r ^ 2) (sq_pos_of_pos hr) (w + v)
        _ ≤ sourceReducedBound Λ * (R * r) / r ^ 2 :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx hK.le) (sq_nonneg r)
        _ = _ := by field_simp [hr.ne']
    calc
      _ ≤ (‖fderiv ℝ f (w + v) (unitVector k)‖ +
          |((homogenizedCoefficient Q)⁻¹).mulVec (w + v) k / r ^ 2| * ‖f (w + v)‖) /
          (‖c‖ * ‖homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v))‖) :=
        c3_shifted_gaussian_quotient_fderiv_norm_le Q i k (r ^ 2) (sq_pos_of_pos hr)
          f hf v c hc w
      _ = (‖fderiv ℝ f (w + v) (unitVector k)‖ +
          |((homogenizedCoefficient Q)⁻¹).mulVec (w + v) k / r ^ 2| * ‖f (w + v)‖) *
          ‖homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v))‖⁻¹ * ‖c‖⁻¹ := by
        ring
      _ ≤ (B / r + (sourceReducedBound Λ * R / r) * A) *
          (E * r ^ d) * (sourceReducedBound Λ * r) := by
        apply mul_le_mul _ hc' (inv_nonneg.mpr (norm_nonneg _))
          (mul_nonneg (add_nonneg (div_nonneg hB hr.le)
            (mul_nonneg (div_nonneg (mul_nonneg hK.le hR) hr.le) hA))
            (mul_nonneg hE (pow_nonneg hr.le _)))
        apply mul_le_mul _ hk (inv_nonneg.mpr (norm_nonneg _))
          (add_nonneg (div_nonneg hB hr.le)
            (mul_nonneg (div_nonneg (mul_nonneg hK.le hR) hr.le) hA))
        exact add_le_add (hgrad _ _) (mul_le_mul hslope (hval _)
          (norm_nonneg _) (div_nonneg (mul_nonneg hK.le hR) hr.le))
      _ = _ := by dsimp only [E]; field_simp [hr.ne']
  · have hfzero : f (w + v) = 0 := by
      by_contra h
      exact hx (hfs h)
    have hd : fderiv ℝ f (w + v) (unitVector k) = 0 := by
      by_contra h
      exact hx (c3_fderiv_support_euclidean_ball f (R * r) hfs (unitVector k) h)
    rw [c3_shifted_gaussian_quotient_fderiv_coordinate Q i k (r ^ 2)
      (sq_pos_of_pos hr) f hf v c hc w, hfzero, hd]
    simp only [zero_div, mul_zero, add_zero, norm_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hE hK.le)
      (add_nonneg hB (mul_nonneg (mul_nonneg hK.le hR) hA))) (pow_nonneg hr.le _)

/-- A lattice difference costs a factor of two in value and a factor of
`2 * sqrt d` when coordinate derivative bounds are converted to length. -/
lemma c3_lattice_coboundary_bounds {d : ℕ} (f : Vec d → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : Vec d) (A B : ℝ)
    (_hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ x, ‖f x‖ ≤ A)
    (hgrad : ∀ x k, ‖fderiv ℝ f x (unitVector k)‖ ≤ B) :
    (∀ x, ‖f x - f (x - v)‖ ≤ 2 * A) ∧
      (∀ x, Real.sqrt (∑ k : Fin d,
        ‖fderiv ℝ (fun y => f y - f (y - v)) x (unitVector k)‖ ^ 2) ≤
          2 * Real.sqrt (d : ℝ) * B) := by
  have hd := hf.differentiable (by norm_num)
  constructor
  · intro x
    exact (norm_sub_le _ _).trans (by linarith [hval x, hval (x - v)])
  · intro x
    have hc (k : Fin d) :
        ‖fderiv ℝ (fun y => f y - f (y - v)) x (unitVector k)‖ ≤ 2 * B := by
      rw [fderiv_fun_sub (hd x) ((differentiableAt_comp_sub v).mpr (hd (x - v))),
        fderiv_comp_sub]
      simp only [sub_apply]
      exact (norm_sub_le _ _).trans (by linarith [hgrad x k, hgrad (x - v) k])
    convert c3_complex_coordinate_length_le _ (2 * B) (by positivity) hc using 1; ring

/-- A closed support bound for a shifted quotient uses exactly one lattice
step, without a reciprocal-kernel support assumption. -/
lemma c3_shifted_quotient_support_ball {d : ℕ} (f g : Vec d → ℂ)
    (R r : ℝ) (hr : 0 < r) (j : Fin d)
    (hf : Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ R * r}) :
    Function.support (fun w => f (w + r • unitVector j) / g w) ⊆
      {w : Vec d | euclideanNorm w ≤ (R + 1) * r} := by
  intro w hw
  have hfw : f (w + r • unitVector j) ≠ 0 := by
    intro h
    exact hw (by simp only [h, zero_div])
  have hv : euclideanNorm (-(r • unitVector j)) = r := by
    rw [show -(r • unitVector j) = (-r) • unitVector j by simp,
      TimeChange.euclideanNorm_smul, euclideanNorm_unitVector_eq_one,
      abs_neg, abs_of_pos hr, mul_one]
  calc
    _ = euclideanNorm ((w + r • unitVector j) + (-(r • unitVector j))) := by
      rw [add_neg_cancel_right]
    _ ≤ euclideanNorm (w + r • unitVector j) + euclideanNorm (-(r • unitVector j)) :=
      TimeChange.euclideanNorm_add_le _ _
    _ ≤ R * r + r := add_le_add (hf hfw) hv.le
    _ = _ := by ring

/-- The slope product has uniform value and coordinate derivative bounds on
the support ball of the actual recovery quotient. -/
lemma c3_gaussian_slope_mul_bounds {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (s : ℝ) (hs : 0 < s)
    (ρ H L : ℝ) (hρ : 0 ≤ ρ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (h : Vec d → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhs : Function.support h ⊆ {x : Vec d | euclideanNorm x ≤ ρ})
    (hval : ∀ x, ‖h x‖ ≤ H)
    (hgrad : ∀ x k, ‖fderiv ℝ h x (unitVector k)‖ ≤ L) :
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    (∀ w, ‖slope w * h w‖ ≤ sourceReducedBound Λ * ρ / s * H) ∧
      (∀ w k, ‖fderiv ℝ (fun x => slope x * h x) w (unitVector k)‖ ≤
        sourceReducedBound Λ / s * H + sourceReducedBound Λ * ρ / s * L) := by
  let slope := fun w : Vec d =>
    ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
  have hK : 0 < sourceReducedBound Λ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
  have hslope (w : Vec d) (hw : euclideanNorm w ≤ ρ) :
      ‖slope w‖ ≤ sourceReducedBound Λ * ρ / s := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact (c3_gaussian_slope_coordinate_le Q j s hs w).trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw hK.le) hs.le)
  have hd := hh.differentiable (by norm_num)
  have hsmooth := (c3_gaussian_slope_contDiff Q j s).differentiable (by norm_num)
  have hder (w : Vec d) (k : Fin d) :
      fderiv ℝ (fun x => slope x * h x) w (unitVector k) =
        slope w * fderiv ℝ h w (unitVector k) +
          h w * (((((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ)) := by
    erw [fderiv_fun_mul (hsmooth w) (hd w)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    rw [c3_gaussian_slope_fderiv_coordinate]
  have hentry (k : Fin d) :
      ‖(((((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ))‖ ≤
        sourceReducedBound Λ / s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hs]
    exact div_le_div_of_nonneg_right (abs_homogenizedCoefficient_inv_entry_le Q j k) hs.le
  dsimp only
  constructor
  · intro w
    by_cases hw : euclideanNorm w ≤ ρ
    · rw [norm_mul]
      exact mul_le_mul (hslope w hw) (hval w) (norm_nonneg _)
        (div_nonneg (mul_nonneg hK.le hρ) hs.le)
    · have hz : h w = 0 := by
        by_contra hn
        exact hw (hhs hn)
      rw [hz, mul_zero, norm_zero]
      positivity
  · intro w k
    rw [hder]
    by_cases hw : euclideanNorm w ≤ ρ
    · calc
        _ ≤ ‖slope w‖ * ‖fderiv ℝ h w (unitVector k)‖ +
            ‖h w‖ * ‖(((((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ))‖ := by
          simpa only [norm_mul] using
            norm_add_le (slope w * fderiv ℝ h w (unitVector k))
              (h w * (((((homogenizedCoefficient Q)⁻¹) j k / s : ℝ) : ℂ)))
        _ ≤ (sourceReducedBound Λ * ρ / s) * L + H * (sourceReducedBound Λ / s) :=
          add_le_add
            (mul_le_mul (hslope w hw) (hgrad w k) (norm_nonneg _)
              (div_nonneg (mul_nonneg hK.le hρ) hs.le))
            (mul_le_mul (hval w) (hentry k) (norm_nonneg _) hH)
        _ = _ := by ring
    · have hz : h w = 0 := by
        by_contra hn
        exact hw (hhs hn)
      have hdz : fderiv ℝ h w (unitVector k) = 0 := by
        by_contra hn
        exact hw (c3_fderiv_support_euclidean_ball h ρ hhs (unitVector k) hn)
      rw [hz, hdz, mul_zero, zero_mul, add_zero, norm_zero]
      positivity

/-- Both actual Gaussian recovery coboundaries have structural bounds at every
positive lattice scale. The Euclidean gradient lengths retain their distinct
volume powers. -/
theorem c3_gaussian_recovery_coboundaries_uniform_bounds
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ R * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
    let s := r ^ 2
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ₀ := fun w : Vec d => h w - h (w - v)
    let δ₁ := fun w : Vec d => slope w * h w - slope (w - v) * h (w - v)
    (∀ w, ‖δ₀ w‖ ≤ C * A * r ^ (d + 1)) ∧
    (∀ w, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ δ₀ w (unitVector k)‖ ^ 2) ≤
      C * (A + B) * r ^ d) ∧
    (∀ w, ‖δ₁ w‖ ≤ C * A * r ^ d) ∧
    (∀ w, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ δ₁ w (unitVector k)‖ ^ 2) ≤
      C * (A + B) * r ^ (d - 1)) := by
  let K := sourceReducedBound D.ellipticity
  let E := (2 * Real.pi) ^ ((d : ℝ) / 2) *
    Real.sqrt ((d.factorial : ℝ) * K ^ d) * Real.exp (K * R ^ 2 / 2)
  let a := E * K
  let b := 1 + K * R
  let t := K * (R + 1)
  let c₀ := 2 * a
  let c₁ := 2 * Real.sqrt (d : ℝ) * a * b
  let c₂ := 2 * t * a
  let c₃ := 2 * Real.sqrt (d : ℝ) * (K * a + t * a * b)
  let C := 1 + c₀ + c₁ + c₂ + c₃
  have hK : 0 < K := by
    dsimp only [K]
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [D.one_le_ellipticity, sq_nonneg D.ellipticity])
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have ha : 0 ≤ a := mul_nonneg hE hK.le
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hc₀ : 0 ≤ c₀ := by dsimp only [c₀]; positivity
  have hc₁ : 0 ≤ c₁ := by dsimp only [c₁]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp only [c₂]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hC : 0 < C := by dsimp only [C]; linarith
  have hC₀ : c₀ ≤ C := by dsimp only [C]; linarith
  have hC₁ : c₁ ≤ C := by dsimp only [C]; linarith
  have hC₂ : c₂ ≤ C := by dsimp only [C]; linarith
  have hC₃ : c₃ ≤ C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro Q i j r hr A B hA hB f hf hfs hval hgrad
  let v := r • unitVector j
  let slope := fun w : Vec d =>
    ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
  let c := slope v
  let h := fun w : Vec d => f (w + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
  change (∀ w, ‖h w - h (w - v)‖ ≤ C * A * r ^ (d + 1)) ∧
    (∀ w, Real.sqrt (∑ k : Fin d,
      ‖fderiv ℝ (fun x => h x - h (x - v)) w (unitVector k)‖ ^ 2) ≤
        C * (A + B) * r ^ d) ∧
    (∀ w, ‖slope w * h w - slope (w - v) * h (w - v)‖ ≤ C * A * r ^ d) ∧
    (∀ w, Real.sqrt (∑ k : Fin d,
      ‖fderiv ℝ (fun x => slope x * h x - slope (x - v) * h (x - v))
        w (unitVector k)‖ ^ 2) ≤ C * (A + B) * r ^ (d - 1))
  have hc : c ≠ 0 := by
    apply norm_pos_iff.mp
    rw [c3_gaussian_slope_lattice_step_norm Q j (r ^ 2) (sq_pos_of_pos hr) r hr]
    exact div_pos (mul_pos hr (posDef_homogenizedCoefficient Q).inv.diag_pos)
      (sq_pos_of_pos hr)
  have hh : ContDiff ℝ (⊤ : ℕ∞) h :=
    c3_shifted_gaussian_quotient_contDiff Q i (r ^ 2) (sq_pos_of_pos hr) f hf v c hc
  have hhs : Function.support h ⊆ {w : Vec d | euclideanNorm w ≤ (R + 1) * r} :=
    c3_shifted_quotient_support_ball f _ R r hr j hfs
  have hcoord (x : Vec d) (k : Fin d) :
      ‖fderiv ℝ f x (unitVector k)‖ ≤ B / r :=
    (Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun l _ => sq_nonneg
      ‖fderiv ℝ f x (unitVector l)‖) (Finset.mem_univ k))).trans (hgrad x)
  have hab : B + K * R * A ≤ b * (A + B) := by
    dsimp only [b]
    nlinarith [mul_nonneg (mul_nonneg hK.le hR) hB]
  have hhval (w : Vec d) : ‖h w‖ ≤ a * A * r ^ (d + 1) :=
    c3_gaussian_recovery_quotient_amplitude_le Q i j r hr R A hA f hfs hval w
  have hhgrad (w : Vec d) (k : Fin d) :
      ‖fderiv ℝ h w (unitVector k)‖ ≤ a * b * (A + B) * r ^ d := by
    calc
      _ ≤ a * (B + K * R * A) * r ^ d :=
        c3_gaussian_recovery_quotient_fderiv_le Q i j r hr R A B hR hA hB
          f hf hfs hval hcoord w k
      _ ≤ a * (b * (A + B)) * r ^ d :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hab ha) (pow_nonneg hr.le _)
      _ = _ := by ring
  have hproduct := c3_gaussian_slope_mul_bounds Q j (r ^ 2) (sq_pos_of_pos hr)
    ((R + 1) * r) (a * A * r ^ (d + 1)) (a * b * (A + B) * r ^ d)
    (by positivity) (by positivity) (by positivity) h hh hhs hhval hhgrad
  have hrpow : r ^ d = r ^ (d - 1) * r := by
    conv_lhs => rw [show d = (d - 1) + 1 by omega]
    rw [pow_succ]
  have hpval (w : Vec d) : ‖slope w * h w‖ ≤ t * a * A * r ^ d := by
    calc
      _ ≤ K * ((R + 1) * r) / r ^ 2 * (a * A * r ^ (d + 1)) := hproduct.1 w
      _ = _ := by dsimp only [t]; rw [pow_succ r d]; field_simp [hr.ne']
  have hpgrad (w : Vec d) (k : Fin d) :
      ‖fderiv ℝ (fun x => slope x * h x) w (unitVector k)‖ ≤
        (K * a + t * a * b) * (A + B) * r ^ (d - 1) := by
    calc
      _ ≤ K / r ^ 2 * (a * A * r ^ (d + 1)) +
          K * ((R + 1) * r) / r ^ 2 * (a * b * (A + B) * r ^ d) := hproduct.2 w k
      _ = (K * a * A + t * a * b * (A + B)) * r ^ (d - 1) := by
        dsimp only [t]
        rw [pow_succ r d]
        simp only [hrpow]
        field_simp [hr.ne']
      _ ≤ (K * a * (A + B) + t * a * b * (A + B)) * r ^ (d - 1) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr.le _)
        exact add_le_add (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hB)
          (mul_nonneg hK.le ha)) le_rfl
      _ = _ := by ring
  have hδ₀ := c3_lattice_coboundary_bounds h hh v (a * A * r ^ (d + 1))
    (a * b * (A + B) * r ^ d) (by positivity) (by positivity) hhval hhgrad
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => slope x * h x) :=
    (c3_gaussian_slope_contDiff Q j (r ^ 2)).mul hh
  have hδ₁ := c3_lattice_coboundary_bounds (fun x => slope x * h x) hsmooth v
    (t * a * A * r ^ d) ((K * a + t * a * b) * (A + B) * r ^ (d - 1))
    (by positivity) (by positivity) hpval hpgrad
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w
    calc
      _ ≤ 2 * (a * A * r ^ (d + 1)) := hδ₀.1 w
      _ = c₀ * A * r ^ (d + 1) := by dsimp only [c₀]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₀ hA) (pow_nonneg hr.le _)
  · intro w
    calc
      _ ≤ 2 * Real.sqrt (d : ℝ) * (a * b * (A + B) * r ^ d) := hδ₀.2 w
      _ = c₁ * (A + B) * r ^ d := by dsimp only [c₁]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₁ (add_nonneg hA hB)) (pow_nonneg hr.le _)
  · intro w
    calc
      _ ≤ 2 * (t * a * A * r ^ d) := hδ₁.1 w
      _ = c₂ * A * r ^ d := by dsimp only [c₂]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₂ hA) (pow_nonneg hr.le _)
  · intro w
    calc
      _ ≤ 2 * Real.sqrt (d : ℝ) *
          ((K * a + t * a * b) * (A + B) * r ^ (d - 1)) := hδ₁.2 w
      _ = c₃ * (A + B) * r ^ (d - 1) := by dsimp only [c₃]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hC₃ (add_nonneg hA hB)) (pow_nonneg hr.le _)

/-- A norm-controlled real-linear projection preserves cutoff bounds, including
the Euclidean length of the coordinate derivative vector. -/
lemma c3_complex_cutoff_real_projection {d : ℕ} (f : Vec d → ℂ)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ z, |L z| ≤ ‖z‖)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f)
    (ρ A B : ℝ)
    (hsupp : Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ ρ})
    (hval : ∀ x, ‖f x‖ ≤ A)
    (hgrad : ∀ x, Real.sqrt (∑ k : Fin d,
      ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => L (f x)) ∧
    HasCompactSupport (fun x => L (f x)) ∧
    Function.support (fun x => L (f x)) ⊆ {x : Vec d | euclideanNorm x ≤ ρ} ∧
    (∀ x, |L (f x)| ≤ A) ∧
    (∀ x, Real.sqrt (∑ k : Fin d,
      |fderiv ℝ (fun x => L (f x)) x (unitVector k)| ^ 2) ≤ B) := by
  refine ⟨L.contDiff.comp hf, ?_, ?_, fun x => (hL (f x)).trans (hval x), ?_⟩
  · exact hcompact.comp_left (map_zero L)
  · intro x hx
    apply hsupp
    intro hzero
    exact hx (by simp [hzero])
  · intro x
    have hderiv (k : Fin d) :
        fderiv ℝ (fun x => L (f x)) x (unitVector k) =
          L (fderiv ℝ f x (unitVector k)) := by
      have h := L.hasFDerivAt.comp x
        ((hf.differentiable (by norm_num) x).hasFDerivAt)
      change fderiv ℝ (L ∘ f) x (unitVector k) = _
      rw [h.fderiv]
      rfl
    calc
      _ ≤ Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro k _
        rw [hderiv]
        exact pow_le_pow_left₀ (abs_nonneg _) (hL _) 2
      _ ≤ B := hgrad x

/-- Real projections of compact complex lattice differences periodize to zero. -/
lemma c3_projected_lattice_coboundary_hasSum_zero {d : ℕ} (f : Vec d → ℂ)
    (hf : HasCompactSupport f) (L : ℂ →L[ℝ] ℝ) (r : ℝ) (hr : r ≠ 0)
    (y : Vec d) (v : Fin d → ℤ) :
    HasSum (fun z : Fin d → ℤ =>
      L (f (y - fun i => r * (z i : ℝ)) -
        f ((y - fun i => r * (z i : ℝ)) - fun i => r * (v i : ℝ)))) 0 := by
  simpa only [map_sub] using
    c3_compact_lattice_coboundary_hasSum_zero (fun x => L (f x))
      (hf.comp_left (map_zero L)) r hr y v

/-- Both real-linear components of the actual Gaussian recovery differences
have the same uniform bounds and zero lattice periodization. -/
theorem c3_gaussian_recovery_projected_coboundaries
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ 2 * Real.sqrt (d : ℝ) * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
        ∀ (L : ℂ →L[ℝ] ℝ), (∀ z, |L z| ≤ ‖z‖) →
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ₀ := fun w : Vec d => L (h w - h (w - v))
    let δ₁ := fun w : Vec d => L (slope w * h w - slope (w - v) * h (w - v))
    let good := fun (δ : Vec d → ℝ) (a b : ℝ) =>
      ContDiff ℝ (⊤ : ℕ∞) δ ∧ HasCompactSupport δ ∧
      Function.support δ ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ x, |δ x| ≤ a) ∧
      (∀ x, Real.sqrt (∑ k : Fin d, (fderiv ℝ δ x (unitVector k)) ^ 2) ≤ b) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ => δ (y - fun k => r * (z k : ℝ))) 0
    good δ₀ (C * A * r ^ (d + 1)) (C * (A + B) * r ^ d) ∧
      good δ₁ (C * A * r ^ d) (C * (A + B) * r ^ (d - 1)) := by
  obtain ⟨C, hC, hbound⟩ := c3_gaussian_recovery_coboundaries_uniform_bounds
    d hd D (2 * Real.sqrt (d : ℝ)) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro Q i j r hr A B hA hB f hf hfc hfs hval hgrad L hL
  let v := r • unitVector j
  let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
  let c := slope v
  let h := fun w : Vec d => f (w + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
  have hc : c ≠ 0 := by
    apply norm_ne_zero_iff.mp
    dsimp only [c, slope, v]
    rw [c3_gaussian_slope_lattice_step_norm Q j (r ^ 2) (sq_pos_of_pos hr) r hr]
    exact ne_of_gt (div_pos (mul_pos hr (posDef_homogenizedCoefficient Q).inv.diag_pos)
      (sq_pos_of_pos hr))
  have hreg := c3_gaussian_recovery_coboundaries_regular Q i j (r ^ 2)
    (sq_pos_of_pos hr) f hf hfc v c hc
  have hsupp := c3_gaussian_recovery_coboundaries_lattice_support Q i j (r ^ 2)
    (sq_pos_of_pos hr) r hr f hfs c
  have hb := hbound Q i j r hr A B hA hB f hf hfs hval hgrad
  have hhcompact : HasCompactSupport h :=
    c3_shifted_gaussian_quotient_hasCompactSupport Q i (r ^ 2)
      (sq_pos_of_pos hr) f hfc v c
  have hcenter : (fun k => r * ((Pi.single j 1 : Fin d → ℤ) k : ℝ)) = v := by
    ext k
    simp [v, unitVector, Pi.single_apply]
  have hzero₀ (y : Vec d) := c3_projected_lattice_coboundary_hasSum_zero
    h hhcompact L r hr.ne' y (Pi.single j 1)
  have hzero₁ (y : Vec d) := c3_projected_lattice_coboundary_hasSum_zero
    (fun w => slope w * h w) hhcompact.mul_left L r hr.ne' y (Pi.single j 1)
  have hp₀ := c3_complex_cutoff_real_projection (fun w => h w - h (w - v)) L hL
    hreg.1 hreg.2.1 _ _ _ hsupp.1 hb.1 hb.2.1
  have hp₁ := c3_complex_cutoff_real_projection
    (fun w => slope w * h w - slope (w - v) * h (w - v)) L hL
    hreg.2.2.1 hreg.2.2.2 _ _ _ hsupp.2 hb.2.2.1 hb.2.2.2
  refine ⟨⟨hp₀.1, hp₀.2.1, hp₀.2.2.1, hp₀.2.2.2.1, ?_, ?_⟩,
    ⟨hp₁.1, hp₁.2.1, hp₁.2.2.1, hp₁.2.2.2.1, ?_, ?_⟩⟩
  · simpa only [sq_abs] using hp₀.2.2.2.2
  · intro y; simpa only [hcenter] using hzero₀ y
  · simpa only [sq_abs] using hp₁.2.2.2.2
  · intro y; simpa only [hcenter] using hzero₁ y

/-- Multiplying a smooth complex test by the canonical partition cutoff gives
the sharp support and physical-scale bounds required by recovery. -/
lemma c3_flux_cutoff_complex_product_bounds {d : ℕ} (r : ℝ) (hr : 0 < r)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (ψ : Vec d → ℂ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψval : ∀ x, ‖ψ x‖ ≤ A)
    (hψgrad : ∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B / r) :
    let f := fun x => (fluxPartitionCutoff r x : ℂ) * ψ x
    ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧
    Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ 2 * Real.sqrt (d : ℝ) * r} ∧
    (∀ x, ‖f x‖ ≤ A) ∧
    (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤
      (Real.sqrt (d : ℝ) * (A + B)) / r) := by
  let χ : Vec d → ℂ := fun x => (fluxPartitionCutoff r x : ℂ)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    Complex.ofRealCLM.contDiff.comp (flux_partition_cutoff_contDiff r)
  have hχc : HasCompactSupport χ :=
    (flux_partition_cutoff_hasCompactSupport hr).comp_left (g := Complex.ofReal) rfl
  have hχval (x : Vec d) : ‖χ x‖ ≤ 1 := by
    dsimp only [χ]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (flux_partition_cutoff_nonneg r x)]
    exact flux_partition_cutoff_le_one r x
  have hχder (x : Vec d) (k : Fin d) :
      ‖fderiv ℝ χ x (unitVector k)‖ ≤ 1 / r := by
    have h := Complex.ofRealCLM.hasFDerivAt.comp x
      (((flux_partition_cutoff_contDiff r).differentiable (by norm_num) x).hasFDerivAt)
    change ‖fderiv ℝ (Complex.ofRealCLM ∘ fluxPartitionCutoff r) x (unitVector k)‖ ≤ _
    rw [h.fderiv]
    change ‖((fderiv ℝ (fluxPartitionCutoff r) x (unitVector k) : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact flux_partition_cutoff_coord_deriv_le hr x k
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * ψ x) ∧ _
  refine ⟨hχ.mul hψ, hχc.mul_right, ?_, ?_, ?_⟩
  · intro x hx
    apply flux_partition_cutoff_support_sharp hr
    intro hzero
    exact hx (by simp [hzero])
  · intro x
    rw [norm_mul]
    calc
      ‖χ x‖ * ‖ψ x‖ ≤ 1 * A := mul_le_mul (hχval x) (hψval x) (norm_nonneg _) zero_le_one
      _ = A := one_mul _
  · intro x
    have hcoord (k : Fin d) :
        ‖fderiv ℝ (fun x => χ x * ψ x) x (unitVector k)‖ ≤ (A + B) / r := by
      rw [fderiv_fun_mul ((hχ.differentiable (by norm_num)) x)
        ((hψ.differentiable (by norm_num)) x)]
      simp only [add_apply, smul_apply, smul_eq_mul]
      calc
        _ ≤ ‖χ x * fderiv ℝ ψ x (unitVector k)‖ +
            ‖ψ x * fderiv ℝ χ x (unitVector k)‖ := norm_add_le _ _
        _ = ‖χ x‖ * ‖fderiv ℝ ψ x (unitVector k)‖ +
            ‖ψ x‖ * ‖fderiv ℝ χ x (unitVector k)‖ := by rw [norm_mul, norm_mul]
        _ ≤ 1 * (B / r) + A * (1 / r) := add_le_add
          (mul_le_mul (hχval x) (hψgrad x k) (norm_nonneg _) zero_le_one)
          (mul_le_mul (hψval x) (hχder x k) (norm_nonneg _) hA)
        _ = (A + B) / r := by ring
    convert c3_complex_coordinate_length_le _ ((A + B) / r)
      (div_nonneg (add_nonneg hA hB) hr.le) hcoord using 1; ring


/-- A single polynomial envelope absorbs the powers occurring in both
Gaussian recovery coboundaries, uniformly across small and large scales. -/
lemma c3_recovery_polynomial_envelope (d k : ℕ) (hk : k ≤ d + 1)
    (r C₀ C A B : ℝ) (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀)
    (hC : C₀ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    C₀ * (A + B) * r ^ k ≤ C * (1 + A + B) * (1 + r) ^ (d + 1) := by
  have hCnonneg : 0 ≤ C := hC₀.trans hC
  have hbase : 1 ≤ 1 + r := by linarith
  have hp : r ^ k ≤ (1 + r) ^ (d + 1) :=
    (pow_le_pow_left₀ hr (by linarith : r ≤ 1 + r) k).trans
      (pow_le_pow_right₀ hbase hk)
  have hcoef : C₀ * (A + B) ≤ C * (1 + A + B) := by
    calc
      C₀ * (A + B) ≤ C * (A + B) :=
        mul_le_mul_of_nonneg_right hC (add_nonneg hA hB)
      _ ≤ C * (1 + A + B) :=
        mul_le_mul_of_nonneg_left (by linarith) hCnonneg
  exact mul_le_mul hcoef hp (pow_nonneg hr _) (mul_nonneg hCnonneg (by linarith))


/-- Dividing a smooth real test by a positive constant divides the Euclidean
length of its coordinate derivative vector by the same constant. -/
lemma c3_real_cutoff_scaled_coordinate_length {d : ℕ} (g : Vec d → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (M : ℝ) (hM : 0 < M) (x : Vec d) :
    Real.sqrt (∑ k : Fin d,
      (fderiv ℝ (fun w => g w / M) x (unitVector k)) ^ 2) =
      Real.sqrt (∑ k : Fin d, (fderiv ℝ g x (unitVector k)) ^ 2) / M := by
  have hderiv (k : Fin d) :
      fderiv ℝ (fun w => g w / M) x (unitVector k) =
        fderiv ℝ g x (unitVector k) / M := by
    have h := fderiv_const_mul ((hg.differentiable (by norm_num)) x) M⁻¹
    have hh := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) h
    simpa only [div_eq_mul_inv, smul_apply, smul_eq_mul,
      mul_comm] using hh
  calc
    _ = Real.sqrt ((∑ k : Fin d, (fderiv ℝ g x (unitVector k)) ^ 2) / M ^ 2) := by
      congr 1
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k _
      rw [hderiv, div_pow]
    _ = _ := by
      rw [Real.sqrt_div (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
        Real.sqrt_sq_eq_abs, abs_of_pos hM]


/-- Normalize a real compact cutoff while preserving its support and its zero
lattice periodization. The two inputs express the unnormalized half-bounds. -/
lemma c3_normalize_real_lattice_cutoff {d : ℕ} (g : Vec d → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hc : HasCompactSupport g)
    (ρ r M a b : ℝ) (hr : 0 < r) (hM : 0 < M)
    (hs : Function.support g ⊆ {x : Vec d | euclideanNorm x ≤ ρ})
    (hv : ∀ x, |g x| ≤ a)
    (hd : ∀ x, Real.sqrt (∑ k : Fin d,
      (fderiv ℝ g x (unitVector k)) ^ 2) ≤ b)
    (ha : a ≤ M / 2) (hb : b * r ≤ M / 2)
    (hz : ∀ y, HasSum (fun z : Fin d → ℤ =>
      g (y - fun k => r * (z k : ℝ))) 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => g x / M) ∧
    HasCompactSupport (fun x => g x / M) ∧
    Function.support (fun x => g x / M) ⊆ {x : Vec d | euclideanNorm x ≤ ρ} ∧
    (∀ x, |g x / M| ≤ 1 / 2) ∧
    (∀ x, Real.sqrt (∑ k : Fin d,
      (fderiv ℝ (fun w => g w / M) x (unitVector k)) ^ 2) ≤ 1 / (2 * r)) ∧
    ∀ y, HasSum (fun z : Fin d → ℤ =>
      g (y - fun k => r * (z k : ℝ)) / M) 0 := by
  refine ⟨hg.div_const M, ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp_left (g := fun x : ℝ => x / M) (by simp)
  · intro x hx
    apply hs
    intro hzero
    exact hx (by simp [hzero])
  · intro x
    rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
    linarith [hv x]
  · intro x
    rw [c3_real_cutoff_scaled_coordinate_length g hg M hM x, div_le_iff₀ hM]
    rw [show 1 / (2 * r) * M = M / (2 * r) by ring]
    apply (le_div_iff₀ (by positivity : 0 < 2 * r)).2
    have hh := mul_le_mul_of_nonneg_right (hd x) hr.le
    linarith
  · intro y
    simpa only [div_eq_mul_inv, zero_mul] using (hz y).mul_right M⁻¹


/-- The common normalizer dominates both values and the scale-weighted
coordinate gradients of the two Gaussian recovery differences. -/
lemma c3_recovery_normalizer_half_bounds (d : ℕ) (hd : 2 ≤ d)
    (r C₀ C A B : ℝ) (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀)
    (hC : C₀ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let M := 2 * C * (1 + A + B) * (1 + r) ^ (d + 1)
    C₀ * A * r ^ (d + 1) ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ d) * r ≤ M / 2 ∧
    C₀ * A * r ^ d ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ (d - 1)) * r ≤ M / 2 := by
  let P := C * (1 + A + B) * (1 + r) ^ (d + 1)
  have he₁ : C₀ * (A + B) * r ^ (d + 1) ≤ P :=
    c3_recovery_polynomial_envelope d (d + 1) (le_refl _) r C₀ C A B hr hC₀ hC hA hB
  have he₂ : C₀ * (A + B) * r ^ d ≤ P :=
    c3_recovery_polynomial_envelope d d (Nat.le_succ _) r C₀ C A B hr hC₀ hC hA hB
  have ha : C₀ * A ≤ C₀ * (A + B) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₀
  have hv₁ : C₀ * A * r ^ (d + 1) ≤ P :=
    (mul_le_mul_of_nonneg_right ha (pow_nonneg hr _)).trans he₁
  have hv₂ : C₀ * A * r ^ d ≤ P :=
    (mul_le_mul_of_nonneg_right ha (pow_nonneg hr _)).trans he₂
  have hg₁ : (C₀ * (A + B) * r ^ d) * r ≤ P := by
    calc
      _ = C₀ * (A + B) * r ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ P := he₁
  have hg₂ : (C₀ * (A + B) * r ^ (d - 1)) * r ≤ P := by
    have hd' : d - 1 + 1 = d := by omega
    calc
      _ = C₀ * (A + B) * r ^ (d - 1 + 1) := by rw [pow_succ]; ring
      _ = C₀ * (A + B) * r ^ d := by rw [hd']
      _ ≤ P := he₂
  have hP : (2 * C * (1 + A + B) * (1 + r) ^ (d + 1)) / 2 = P := by
    dsimp only [P]
    ring
  dsimp only
  rw [hP]
  exact ⟨hv₁, hg₁, hv₂, hg₂⟩


theorem c3_gaussian_recovery_normalized_real_coboundaries
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)  :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
    let s := r ^ 2
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ : Bool → Vec d → ℂ := fun b w => if b then
      slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
    let M := 2 * C * (1 + A + B) * (1 + r) ^ (d + 1)
    let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
      (if q then (δ b w).im else (δ b w).re) / M
    ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
      Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ w, |θ b q w| ≤ 1 / 2) ∧
      (∀ w, Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤ 1 / (2 * r)) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ =>
        θ b q (y - fun k => r * (z k : ℝ))) 0 := by
  obtain ⟨C₀, hC₀, hprojected⟩ := c3_gaussian_recovery_projected_coboundaries d hd D
  let C := max 1 C₀
  have hC : C₀ ≤ C := le_max_right _ _
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  refine ⟨C, hC1, ?_⟩
  intro Q i j r hr A B hA hB f hf hfc hfs hval hgrad
  let v := r • unitVector j
  let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
  let c := slope v
  let h := fun w : Vec d => f (w + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
  let M := 2 * C * (1 + A + B) * (1 + r) ^ (d + 1)
  have hM : 0 < M := by dsimp only [M]; positivity
  have hhalf := c3_recovery_normalizer_half_bounds d hd r C₀ C A B hr.le hC₀.le hC hA hB
  change C₀ * A * r ^ (d + 1) ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ d) * r ≤ M / 2 ∧
    C₀ * A * r ^ d ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ (d - 1)) * r ≤ M / 2 at hhalf
  dsimp only
  intro b q
  let L : ℂ →L[ℝ] ℝ := if q then Complex.imCLM else Complex.reCLM
  have hL : ∀ z, |L z| ≤ ‖z‖ := by
    intro z
    cases q <;> simp [L, Complex.abs_re_le_norm, Complex.abs_im_le_norm]
  have hp := hprojected Q i j r hr A B hA hB f hf hfc hfs hval hgrad L hL
  let g₀ := fun w : Vec d => L (h w - h (w - v))
  let g₁ := fun w : Vec d => L (slope w * h w - slope (w - v) * h (w - v))
  have hn₀ := c3_normalize_real_lattice_cutoff g₀ hp.1.1 hp.1.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M (C₀ * A * r ^ (d + 1))
    (C₀ * (A + B) * r ^ d) hr hM hp.1.2.2.1 hp.1.2.2.2.1
    hp.1.2.2.2.2.1 hhalf.1 hhalf.2.1 hp.1.2.2.2.2.2
  have hn₁ := c3_normalize_real_lattice_cutoff g₁ hp.2.1 hp.2.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M (C₀ * A * r ^ d)
    (C₀ * (A + B) * r ^ (d - 1)) hr hM hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hhalf.2.2.1 hhalf.2.2.2 hp.2.2.2.2.2.2
  cases b with
  | false =>
    cases q <;> simpa only [g₀, L, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₀
  | true =>
    cases q <;> simpa only [g₁, L, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₁


/-- The sharp two-power envelope controls the intermediate lattice scale. -/
lemma c3_recovery_sharp_power_envelope (d : ℕ) (hd : 2 ≤ d)
    (r : ℝ) (hr : 0 ≤ r) :
    r ^ d ≤ r ^ (d + 1) + r ^ (d - 1) := by
  have hd' : d - 1 + 1 = d := by omega
  have hpow₁ : r ^ d = r ^ (d - 1) * r := by
    conv_lhs => rw [← hd']
    rw [pow_succ]
  have hpow₂ : r ^ (d + 1) = r ^ (d - 1) * r ^ 2 := by
    rw [pow_succ, hpow₁]
    ring
  have hscalar : r ≤ r ^ 2 + 1 := by nlinarith [sq_nonneg (r - 1 / 2)]
  have hmul := mul_le_mul_of_nonneg_left hscalar (pow_nonneg hr (d - 1))
  rw [hpow₁, hpow₂]
  nlinarith [hmul]

/-- Sharp scale half-bounds for the two projected recovery differences. -/
lemma c3_recovery_sharp_normalizer_half_bounds (d : ℕ) (hd : 2 ≤ d)
    (r C₀ C A B : ℝ) (hr : 0 ≤ r) (hC₀ : 0 ≤ C₀)
    (hC : C₀ ≤ C) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let M := 2 * C * (1 + A + B) * (r ^ (d + 1) + r ^ (d - 1))
    C₀ * A * r ^ (d + 1) ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ d) * r ≤ M / 2 ∧
    C₀ * A * r ^ d ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ (d - 1)) * r ≤ M / 2 := by
  let S := r ^ (d + 1) + r ^ (d - 1)
  let P := C * (1 + A + B) * S
  have hp₁ : r ^ (d + 1) ≤ S := by
    dsimp only [S]
    linarith [pow_nonneg hr (d - 1)]
  have hp₂ : r ^ d ≤ S := c3_recovery_sharp_power_envelope d hd r hr
  have hCnonneg : 0 ≤ C := hC₀.trans hC
  have hab : 0 ≤ A + B := add_nonneg hA hB
  have hcoef : C₀ * (A + B) ≤ C * (1 + A + B) := by
    calc
      _ ≤ C * (A + B) := mul_le_mul_of_nonneg_right hC hab
      _ ≤ C * (1 + A + B) := mul_le_mul_of_nonneg_left (by linarith) hCnonneg
  have ha : C₀ * A ≤ C₀ * (A + B) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₀
  have henvelope (k : ℕ) (hk : r ^ k ≤ S) : C₀ * (A + B) * r ^ k ≤ P := by
    exact mul_le_mul hcoef hk (pow_nonneg hr _) (mul_nonneg hCnonneg (by linarith))
  have he₁ := henvelope (d + 1) hp₁
  have he₂ := henvelope d hp₂
  have hv₁ : C₀ * A * r ^ (d + 1) ≤ P :=
    (mul_le_mul_of_nonneg_right ha (pow_nonneg hr _)).trans he₁
  have hv₂ : C₀ * A * r ^ d ≤ P :=
    (mul_le_mul_of_nonneg_right ha (pow_nonneg hr _)).trans he₂
  have hg₁ : (C₀ * (A + B) * r ^ d) * r ≤ P := by
    calc
      _ = C₀ * (A + B) * r ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ P := he₁
  have hg₂ : (C₀ * (A + B) * r ^ (d - 1)) * r ≤ P := by
    have hd' : d - 1 + 1 = d := by omega
    calc
      _ = C₀ * (A + B) * r ^ (d - 1 + 1) := by rw [pow_succ]; ring
      _ = C₀ * (A + B) * r ^ d := by rw [hd']
      _ ≤ P := he₂
  have hP : (2 * C * (1 + A + B) * (r ^ (d + 1) + r ^ (d - 1))) / 2 = P := by
    dsimp only [P, S]
    ring
  dsimp only
  rw [hP]
  exact ⟨hv₁, hg₁, hv₂, hg₂⟩


/-- Sharp-scale normalization of the actual projected recovery cutoffs. -/
theorem c3_gaussian_recovery_normalized_real_coboundaries_sharp_scale
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)  :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
    let s := r ^ 2
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ : Bool → Vec d → ℂ := fun b w => if b then
      slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
    let M := 2 * C * (1 + A + B) * (r ^ (d + 1) + r ^ (d - 1))
    let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
      (if q then (δ b w).im else (δ b w).re) / M
    ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
      Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ w, |θ b q w| ≤ 1 / 2) ∧
      (∀ w, Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤ 1 / (2 * r)) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ =>
        θ b q (y - fun k => r * (z k : ℝ))) 0 := by
  obtain ⟨C₀, hC₀, hprojected⟩ := c3_gaussian_recovery_projected_coboundaries d hd D
  let C := max 1 C₀
  have hC : C₀ ≤ C := le_max_right _ _
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  refine ⟨C, hC1, ?_⟩
  intro Q i j r hr A B hA hB f hf hfc hfs hval hgrad
  let v := r • unitVector j
  let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
  let c := slope v
  let h := fun w : Vec d => f (w + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
  let M := 2 * C * (1 + A + B) * (r ^ (d + 1) + r ^ (d - 1))
  have hM : 0 < M := by dsimp only [M]; positivity
  have hhalf := c3_recovery_sharp_normalizer_half_bounds d hd r C₀ C A B hr.le hC₀.le hC hA hB
  change C₀ * A * r ^ (d + 1) ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ d) * r ≤ M / 2 ∧
    C₀ * A * r ^ d ≤ M / 2 ∧
    (C₀ * (A + B) * r ^ (d - 1)) * r ≤ M / 2 at hhalf
  dsimp only
  intro b q
  let L : ℂ →L[ℝ] ℝ := if q then Complex.imCLM else Complex.reCLM
  have hL : ∀ z, |L z| ≤ ‖z‖ := by
    intro z
    cases q <;> simp [L, Complex.abs_re_le_norm, Complex.abs_im_le_norm]
  have hp := hprojected Q i j r hr A B hA hB f hf hfc hfs hval hgrad L hL
  let g₀ := fun w : Vec d => L (h w - h (w - v))
  let g₁ := fun w : Vec d => L (slope w * h w - slope (w - v) * h (w - v))
  have hn₀ := c3_normalize_real_lattice_cutoff g₀ hp.1.1 hp.1.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M (C₀ * A * r ^ (d + 1))
    (C₀ * (A + B) * r ^ d) hr hM hp.1.2.2.1 hp.1.2.2.2.1
    hp.1.2.2.2.2.1 hhalf.1 hhalf.2.1 hp.1.2.2.2.2.2
  have hn₁ := c3_normalize_real_lattice_cutoff g₁ hp.2.1 hp.2.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M (C₀ * A * r ^ d)
    (C₀ * (A + B) * r ^ (d - 1)) hr hM hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hhalf.2.2.1 hhalf.2.2.2 hp.2.2.2.2.2.2
  cases b with
  | false =>
    cases q <;> simpa only [g₀, L, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₀
  | true =>
    cases q <;> simpa only [g₁, L, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₁

/-- Split-scale normalization of the actual projected recovery cutoffs. -/
theorem c3_gaussian_recovery_normalized_real_coboundaries_split_scale
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)  :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
    let s := r ^ 2
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ : Bool → Vec d → ℂ := fun b w => if b then
      slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
    let M : Bool → ℝ := fun b => 2 * C * (1 + A + B) * (if b then r ^ d else r ^ (d + 1))
    let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
      (if q then (δ b w).im else (δ b w).re) / M b
    ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
      Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ w, |θ b q w| ≤ 1 / 2) ∧
      (∀ w, Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤ 1 / (2 * r)) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ =>
        θ b q (y - fun k => r * (z k : ℝ))) 0 := by
  obtain ⟨C₀, hC₀, hprojected⟩ := c3_gaussian_recovery_projected_coboundaries d hd D
  let C := max 1 C₀
  have hC : C₀ ≤ C := le_max_right _ _
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCpos : 0 < C := by linarith
  refine ⟨C, hC1, ?_⟩
  intro Q i j r hr A B hA hB f hf hfc hfs hval hgrad
  let v := r • unitVector j
  let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / r ^ 2 : ℝ) : ℂ)
  let c := slope v
  let h := fun w : Vec d => f (w + v) /
    (c * homogenizedGaussianKernel Q i (r ^ 2) (sq_pos_of_pos hr) 0 (-(w + v)))
  let M₀ := 2 * C * (1 + A + B) * r ^ (d + 1)
  let M₁ := 2 * C * (1 + A + B) * r ^ d
  have hM₀ : 0 < M₀ := by dsimp only [M₀]; positivity
  have hM₁ : 0 < M₁ := by dsimp only [M₁]; positivity
  have hcoef : C₀ * (A + B) ≤ C * (1 + A + B) := by
    calc
      _ ≤ C * (A + B) := mul_le_mul_of_nonneg_right hC (add_nonneg hA hB)
      _ ≤ C * (1 + A + B) := mul_le_mul_of_nonneg_left (by linarith) hCpos.le
  have ha : C₀ * A ≤ C₀ * (A + B) :=
    mul_le_mul_of_nonneg_left (by linarith) hC₀.le
  have hhalf₀ : C₀ * A * r ^ (d + 1) ≤ M₀ / 2 ∧
      (C₀ * (A + B) * r ^ d) * r ≤ M₀ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr.le (d + 1))
    have hv := mul_le_mul_of_nonneg_right ha (pow_nonneg hr.le (d + 1))
    have hM : M₀ / 2 = C * (1 + A + B) * r ^ (d + 1) := by
      dsimp only [M₀]; ring
    rw [hM]
    constructor
    · exact hv.trans hh
    · calc
        _ = C₀ * (A + B) * r ^ (d + 1) := by rw [pow_succ]; ring
        _ ≤ _ := hh
  have hhalf₁ : C₀ * A * r ^ d ≤ M₁ / 2 ∧
      (C₀ * (A + B) * r ^ (d - 1)) * r ≤ M₁ / 2 := by
    have hh := mul_le_mul_of_nonneg_right hcoef (pow_nonneg hr.le d)
    have hv := mul_le_mul_of_nonneg_right ha (pow_nonneg hr.le d)
    have hd' : d - 1 + 1 = d := by omega
    have hM : M₁ / 2 = C * (1 + A + B) * r ^ d := by
      dsimp only [M₁]; ring
    rw [hM]
    constructor
    · exact hv.trans hh
    · calc
        _ = C₀ * (A + B) * r ^ (d - 1 + 1) := by rw [pow_succ]; ring
        _ = C₀ * (A + B) * r ^ d := by rw [hd']
        _ ≤ _ := hh
  dsimp only
  intro b q
  let L : ℂ →L[ℝ] ℝ := if q then Complex.imCLM else Complex.reCLM
  have hL : ∀ z, |L z| ≤ ‖z‖ := by
    intro z
    cases q <;> simp [L, Complex.abs_re_le_norm, Complex.abs_im_le_norm]
  have hp := hprojected Q i j r hr A B hA hB f hf hfc hfs hval hgrad L hL
  let g₀ := fun w : Vec d => L (h w - h (w - v))
  let g₁ := fun w : Vec d => L (slope w * h w - slope (w - v) * h (w - v))
  have hn₀ := c3_normalize_real_lattice_cutoff g₀ hp.1.1 hp.1.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M₀ (C₀ * A * r ^ (d + 1))
    (C₀ * (A + B) * r ^ d) hr hM₀ hp.1.2.2.1 hp.1.2.2.2.1
    hp.1.2.2.2.2.1 hhalf₀.1 hhalf₀.2 hp.1.2.2.2.2.2
  have hn₁ := c3_normalize_real_lattice_cutoff g₁ hp.2.1 hp.2.2.1
    ((2 * Real.sqrt (d : ℝ) + 2) * r) r M₁ (C₀ * A * r ^ d)
    (C₀ * (A + B) * r ^ (d - 1)) hr hM₁ hp.2.2.2.1 hp.2.2.2.2.1
    hp.2.2.2.2.2.1 hhalf₁.1 hhalf₁.2 hp.2.2.2.2.2.2
  cases b with
  | false =>
    cases q <;> simpa only [g₀, L, M₀, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₀
  | true =>
    cases q <;> simpa only [g₁, L, M₁, Bool.false_eq_true, Bool.true_eq_false,
      ↓reduceIte, Complex.reCLM_apply, Complex.imCLM_apply] using hn₁

/-- Averaging a partition with its lattice translate and adding a
zero-periodization perturbation preserves the partition identity. -/
lemma c3_flux_averaged_partition_perturbation_hasSum {d : ℕ}
    {r : ℝ} (hr : 0 < r) (j : Fin d) (δ : Vec d → ℝ)
    (hzδ : ∀ y, HasSum (fun z : Fin d → ℤ =>
      δ (y - fun k => r * (z k : ℝ))) 0) (y : Vec d) :
    HasSum (fun z : Fin d → ℤ =>
      (fluxPartitionCutoff r (y - fun k => r * (z k : ℝ)) +
        fluxPartitionCutoff r ((y - fun k => r * (z k : ℝ)) -
          r • unitVector j)) / 2 + δ (y - fun k => r * (z k : ℝ))) 1 := by
  have hshift : HasSum (fun z : Fin d → ℤ =>
      fluxPartitionCutoff r ((y - fun k => r * (z k : ℝ)) -
        r • unitVector j)) 1 := by
    convert flux_partition_cutoff_partition hr (y - r • unitVector j) using 1
    ext z
    congr 1
    abel
  have h := ((flux_partition_cutoff_partition hr y).add hshift).div_const 2
  have h' := h.add (hzδ y)
  norm_num at h' ⊢
  exact h'

/-- Regularity and the amplitude margin of the perturbed averaged cutoff. -/
lemma c3_flux_averaged_partition_perturbation_regular {d : ℕ}
    {r : ℝ} (hr : 0 < r) (j : Fin d) (δ : Vec d → ℝ)
    (hδ : ContDiff ℝ (⊤ : ℕ∞) δ) (hcδ : HasCompactSupport δ)
    (hvδ : ∀ x, |δ x| ≤ 1 / 2) :
    let χ : Vec d → ℝ := fun x =>
      (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2 + δ x
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ ∀ x, |χ x| ≤ 1 := by
  dsimp only
  have h := flux_partition_cutoff_contDiff (d := d) r
  have hc := flux_partition_cutoff_hasCompactSupport (d := d) hr
  have hsub : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => x - r • unitVector j) :=
    contDiff_id.sub contDiff_const
  refine ⟨((h.add (h.comp hsub)).div_const 2).add hδ, ?_, ?_⟩
  · have ha := hc.add (hc.comp_homeomorph (Homeomorph.subRight (r • unitVector j)))
    have hb := ha.mul_right (f' := fun _ : Vec d => (2 : ℝ)⁻¹)
    change HasCompactSupport (fun x : Vec d =>
      (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) * (2 : ℝ)⁻¹) at hb
    have hb' : HasCompactSupport (fun x : Vec d =>
        (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2) := by
      simpa only [div_eq_mul_inv, Pi.mul_apply, Pi.add_apply, Function.comp_def] using hb
    exact hb'.add hcδ
  · intro x
    exact (abs_add_le _ _).trans (by linarith [c3_flux_partition_average_abs_le_half hr j x, hvδ x])

/-- The translated cutoff remains inside the prescribed radius, using the
sharp support radius of the original cutoff. -/
lemma c3_flux_averaged_partition_perturbation_support {d : ℕ}
    {r : ℝ} (hr : 0 < r) (j : Fin d) (δ : Vec d → ℝ)
    (hsδ : Function.support δ ⊆
      {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r}) :
    Function.support (fun x : Vec d =>
      (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2 + δ x) ⊆
      {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
  intro x hx
  by_contra hout
  have h₀ : fluxPartitionCutoff r x = 0 := by
    by_contra h
    have hh := flux_partition_cutoff_support hr h
    exact hout hh
  have hv : euclideanNorm (r • unitVector j) = r := by
    rw [TimeChange.euclideanNorm_smul, euclideanNorm_unitVector_eq_one, abs_of_pos hr, mul_one]
  have h₁ : fluxPartitionCutoff r (x - r • unitVector j) = 0 := by
    by_contra h
    have hh := flux_partition_cutoff_support_sharp hr h
    have ht := TimeChange.euclideanNorm_add_le (x - r • unitVector j) (r • unitVector j)
    have he : (x - r • unitVector j) + r • unitVector j = x := sub_add_cancel _ _
    rw [he, hv] at ht
    apply hout
    change euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r
    change euclideanNorm (x - r • unitVector j) ≤ 2 * Real.sqrt (d : ℝ) * r at hh
    nlinarith only [hh, ht, hr]
  have h₂ : δ x = 0 := by
    by_contra h
    exact hout (hsδ h)
  exact hx (by simp only [h₀, h₁, h₂, zero_add, zero_div])

/-- The actual cutoff has the sharp coordinate-derived Euclidean gradient
bound before the larger admissibility constant is applied. -/
lemma c3_flux_partition_cutoff_gradient_sharp {d : ℕ} {r : ℝ}
    (hr : 0 < r) (x : Vec d) :
    Real.sqrt (∑ k : Fin d, (fderiv ℝ (fluxPartitionCutoff r) x (unitVector k)) ^ 2) ≤
      Real.sqrt (d : ℝ) / r := by
  have hs : ∑ k : Fin d, (fderiv ℝ (fluxPartitionCutoff r) x (unitVector k)) ^ 2 ≤
      (d : ℝ) * (1 / r) ^ 2 := by
    calc
      _ ≤ ∑ _k : Fin d, (1 / r) ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have hh := pow_le_pow_left₀
          (abs_nonneg (fderiv ℝ (fluxPartitionCutoff r) x (unitVector k)))
          (flux_partition_cutoff_coord_deriv_le hr x k) 2
        simpa only [sq_abs] using hh
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((d : ℝ) * (1 / r) ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt (d : ℝ) / r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by positivity : 0 ≤ 1 / r)]
      ring

/-- The averaged cutoff and the perturbation obey the prescribed Euclidean
coordinate gradient bound. -/
lemma c3_flux_averaged_partition_perturbation_gradient {d : ℕ}
    {r : ℝ} (hr : 0 < r) (j : Fin d) (δ : Vec d → ℝ)
    (hδ : ContDiff ℝ (⊤ : ℕ∞) δ)
    (hgδ : ∀ x, Real.sqrt (∑ k : Fin d, (fderiv ℝ δ x (unitVector k)) ^ 2) ≤ 1 / (2 * r))
    (x : Vec d) :
    Real.sqrt (∑ k : Fin d,
      (fderiv ℝ (fun y : Vec d =>
        (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - r • unitVector j)) / 2 + δ y)
        x (unitVector k)) ^ 2) ≤ (2 * Real.sqrt (d : ℝ) + 2) / r := by
  let f : Vec d → ℝ := fluxPartitionCutoff r
  let v : Vec d := r • unitVector j
  let a : Vec d := fun k => fderiv ℝ f x (unitVector k)
  let b : Vec d := fun k => fderiv ℝ f (x - v) (unitVector k)
  let c : Vec d := fun k => fderiv ℝ δ x (unitVector k)
  have hf : Differentiable ℝ f := (flux_partition_cutoff_contDiff r).differentiable (by norm_num)
  have hd : Differentiable ℝ δ := hδ.differentiable (by norm_num)
  have hab : DifferentiableAt ℝ (fun y : Vec d => f y + f (y - v)) x :=
    (hf x).add ((differentiableAt_comp_sub v).mpr (hf (x - v)))
  have hder (k : Fin d) :
      fderiv ℝ (fun y : Vec d => (f y + f (y - v)) / 2 + δ y) x (unitVector k) =
        ((2 : ℝ)⁻¹ • (a + b) + c) k := by
    rw [show (fun y : Vec d => (f y + f (y - v)) / 2 + δ y) =
      (fun y : Vec d => (2 : ℝ)⁻¹ • (f y + f (y - v)) + δ y) by
        ext y; simp only [smul_eq_mul, div_eq_mul_inv]; ring]
    change (fderiv ℝ (fun y => ((2 : ℝ)⁻¹ • (fun z : Vec d => f z + f (z - v))) y + δ y) x)
      (unitVector k) = _
    rw [fderiv_fun_add (hab.const_smul _) (hd x), fderiv_const_smul hab (2 : ℝ)⁻¹,
      fderiv_fun_add (hf x) ((differentiableAt_comp_sub v).mpr (hf (x - v))),
      fderiv_comp_sub]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Pi.add_apply, Pi.smul_apply, a, b, c]
  have ha : euclideanNorm a ≤ Real.sqrt (d : ℝ) / r := by
    simpa only [euclideanNorm, euclideanSq, dot, pow_two, a] using
      c3_flux_partition_cutoff_gradient_sharp hr x
  have hb : euclideanNorm b ≤ Real.sqrt (d : ℝ) / r := by
    simpa only [euclideanNorm, euclideanSq, dot, pow_two, b, v] using
      c3_flux_partition_cutoff_gradient_sharp hr (x - v)
  have hc : euclideanNorm c ≤ 1 / (2 * r) := by
    simpa only [euclideanNorm, euclideanSq, dot, pow_two, c] using hgδ x
  have htri := TimeChange.euclideanNorm_add_le ((2 : ℝ)⁻¹ • (a + b)) c
  have habtri := TimeChange.euclideanNorm_add_le a b
  rw [TimeChange.euclideanNorm_smul, abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹)] at htri
  have hbound : euclideanNorm ((2 : ℝ)⁻¹ • (a + b) + c) ≤
      (2 * Real.sqrt (d : ℝ) + 2) / r := by
    have hsqrt := Real.sqrt_nonneg (d : ℝ)
    have hinv : 0 < 1 / r := one_div_pos.mpr hr
    rw [div_eq_mul_inv] at ha hb ⊢
    rw [show 1 / (2 * r) = (2 : ℝ)⁻¹ * r⁻¹ by field_simp [ne_of_gt hr]] at hc
    have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
    nlinarith [mul_nonneg hsqrt hi]
  convert hbound using 1
  simp only [euclideanNorm, euclideanSq, dot, pow_two, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, hder, f, v]

/-- The averaged actual partition remains admissible after a smooth,
small, zero-periodization perturbation. -/
theorem c3_flux_averaged_partition_perturbation_admissible
    {d : ℕ} (r : ℝ) (hr : 0 < r) (j : Fin d) (δ : Vec d → ℝ)
    (hδ : ContDiff ℝ (⊤ : ℕ∞) δ) (hcδ : HasCompactSupport δ)
    (hsδ : Function.support δ ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
    (hvδ : ∀ x, |δ x| ≤ 1 / 2)
    (hgδ : ∀ x, Real.sqrt (∑ k : Fin d, (fderiv ℝ δ x (unitVector k)) ^ 2) ≤ 1 / (2 * r))
    (hzδ : ∀ y, HasSum (fun z : Fin d → ℤ => δ (y - fun k => r * (z k : ℝ))) 0) :
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let χ : Vec d → ℝ := fun x =>
      (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2 + δ x
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      Function.support χ ⊆ {x : Vec d | euclideanNorm x ≤ R * r} ∧
      (∀ x, |χ x| ≤ 1) ∧
      (∀ x, Real.sqrt (∑ k : Fin d, (fderiv ℝ χ x (unitVector k)) ^ 2) ≤ R / r) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ => χ (y - fun k => r * (z k : ℝ))) 1 := by
  dsimp only
  obtain ⟨hsmooth, hcompact, hvalue⟩ :=
    c3_flux_averaged_partition_perturbation_regular hr j δ hδ hcδ hvδ
  exact ⟨hsmooth, hcompact, c3_flux_averaged_partition_perturbation_support hr j δ hsδ,
    hvalue, c3_flux_averaged_partition_perturbation_gradient hr j δ hδ hgδ,
    c3_flux_averaged_partition_perturbation_hasSum hr j δ hzδ⟩

/-- The average of two actual partition cutoffs is admissible. -/
theorem c3_flux_averaged_baseline_partition_admissible {d : ℕ} (r : ℝ) (hr : 0 < r) (j : Fin d) :
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let χ : Vec d → ℝ := fun x =>
      (fluxPartitionCutoff r x + fluxPartitionCutoff r (x - r • unitVector j)) / 2
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      Function.support χ ⊆ {x : Vec d | euclideanNorm x ≤ R * r} ∧
      (∀ x, |χ x| ≤ 1) ∧
      (∀ x, Real.sqrt (∑ k : Fin d, (fderiv ℝ χ x (unitVector k)) ^ 2) ≤ R / r) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ => χ (y - fun k => r * (z k : ℝ))) 1 := by
  have h := c3_flux_averaged_partition_perturbation_admissible r hr j (0 : Vec d → ℝ)
    contDiff_const HasCompactSupport.zero (by simp) (by simp)
    (by
      intro x
      simp [fderiv_zero, le_of_lt hr])
    (by intro y; simpa using (hasSum_zero : HasSum (fun _ : Fin d → ℤ => (0 : ℝ)) 0))
  simpa using h


theorem c3_gaussian_recovery_split_partitions_admissible
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)  :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (r : ℝ) (hr : 0 < r) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
        (f : Vec d → ℂ), ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        Function.support f ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} →
        (∀ x, ‖f x‖ ≤ A) →
        (∀ x, Real.sqrt (∑ k : Fin d, ‖fderiv ℝ f x (unitVector k)‖ ^ 2) ≤ B / r) →
    let s := r ^ 2
    let v := r • unitVector j
    let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let c := slope v
    let h := fun w : Vec d => f (w + v) /
      (c * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
    let δ : Bool → Vec d → ℂ := fun b w => if b then
      slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
    let M : Bool → ℝ := fun b => 2 * C * (1 + A + B) * (if b then r ^ d else r ^ (d + 1))
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
      (fluxPartitionCutoff r w + fluxPartitionCutoff r (w - v)) / 2 +
        (if q then (δ b w).im else (δ b w).re) / M b
    ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
      Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ R * r} ∧
      (∀ w, |θ b q w| ≤ 1) ∧
      (∀ w, Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤ R / r) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ =>
        θ b q (y - fun k => r * (z k : ℝ))) 1 := by
  obtain ⟨C, hC, hsplit⟩ := c3_gaussian_recovery_normalized_real_coboundaries_split_scale d hd D
  refine ⟨C, hC, ?_⟩
  intro Q i j r hr A B hA hB f hf hfc hfs hval hgrad
  have h := hsplit Q i j r hr A B hA hB f hf hfc hfs hval hgrad
  dsimp only at h ⊢
  intro b q
  obtain ⟨hs, hc, hsupport, hv, hg, hz⟩ := h b q
  exact c3_flux_averaged_partition_perturbation_admissible r hr j _ hs hc hsupport hv hg hz


/-- Pointwise reconstruction using independently normalized real and imaginary
parts of the two Gaussian coboundaries. -/
lemma c3_cutoff_schwartz_site_recovery_split
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) (i j : Fin d)
    (r W : ℝ) (M : Bool → ℝ) (hr : 0 < r) (hW : 0 < W)
    (hM : ∀ b, M b ≠ 0) (χ : Vec d → ℝ) (ψ : SchwartzMap (Vec d) ℂ)
    (z y : Vec d) (baseline : Vec d → ℝ) :
    let f := fun u : Vec d => (χ u : ℂ) * ψ (-(u + z))
    let s := r ^ 2
    let kernel := homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0
    let slope := fun w : Vec d =>
      ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
    let v := r • unitVector j
    let g := fun w : Vec d => f w / (W : ℂ)
    let h := fun w : Vec d => g (w + v) / (slope v * kernel (-(w + v)))
    let δ : Bool → Vec d → ℂ := fun b w => if b then
      slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
    let θ : Bool → Bool → Vec d → ℝ := fun b q w => baseline w +
      (if q then (δ b w).im else (δ b w).re) / M b
    (χ (y - z) : ℂ) * ψ (-y) =
      ((W * M true : ℝ) : ℂ) * kernel (-(y - z)) *
        (((θ true false (y - z) - baseline (y - z) : ℝ) : ℂ) +
          Complex.I * ((θ true true (y - z) - baseline (y - z) : ℝ) : ℂ)) -
      ((W * M false : ℝ) : ℂ) * fderiv ℝ kernel (-(y - z)) (unitVector j) *
        (((θ false false (y - z) - baseline (y - z) : ℝ) : ℂ) +
          Complex.I * ((θ false true (y - z) - baseline (y - z) : ℝ) : ℂ)) := by
  dsimp only
  have hrec := c3_gaussian_derivative_recovers_cutoff Q i j (r ^ 2)
    (sq_pos_of_pos hr) r hr (fun w => (χ w : ℂ) * ψ (-(w + z)) / (W : ℂ)) (y - z)
  dsimp only at hrec
  simp only [Bool.false_eq_true, ↓reduceIte, add_sub_cancel_left, sub_add_cancel,
    Complex.ofReal_mul, Complex.ofReal_div] at ⊢ hrec
  have hmt : (M true : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM true)
  have hmf : (M false : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM false)
  have hw : (W : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hW.ne'
  simp only [← mul_div_assoc, ← add_div, mul_comm Complex.I, Complex.re_add_im] at ⊢
  field_simp [hmt, hmf] at ⊢
  simp only [mul_comm Complex.I, Complex.re_add_im] at ⊢
  have hrec' := congrArg (fun a : ℂ => (W : ℂ) * a) hrec
  rw [mul_div_cancel₀ _ hw] at hrec'
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv] at hrec' ⊢
  linear_combination -hrec'

end EinsteinFull.Blueprint
