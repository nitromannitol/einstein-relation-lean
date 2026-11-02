import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Correctors.ReducedOperatorLipschitz
import EinsteinRelation.Environment.Bounds
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Prod

/-! # Weak horizontal divergence of the reduced coefficient column

For an environment law `Q`, the reduced coefficient `x ↦ exp(-2V(x)) a₀(x)` has `i`-th column
`x ↦ a(x) e_i`. Under the reduced reference law this column has weak horizontal divergence
`cdiv i = ∑_j ∂_{e_j} a_{ji}` at the origin.

The argument has four steps:

* The columns are Lipschitz with a constant depending only on `Λ₀`. Rademacher's theorem and a
  Fubini argument with stationarity show that the partial derivatives exist at the origin for
  almost every coefficient.
* For a horizontally smooth test `F` with L² derivative `D`, the pairing with a bounded column
  is a limit of difference quotients. Stationarity moves the translation onto the column.
* The slopes of the column converge to its directional derivative, and they are dominated by the
  Lipschitz constant times `|F|`.
* Summing over the coordinates gives the weak identity for `cdiv i`.
-/

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

namespace EinsteinRelation

namespace DriftH5

/-- The divergence at the origin of the `i`-th column of the coefficient: the sum over `j` of the
directional derivative along `e_j` of the entry `x ↦ (w.1 x) j i`. -/
noncomputable def cdiv {d : ℕ} (i : Fin d) (w : FieldPair d) : ℝ :=
  ∑ j, (fderiv ℝ (fun x => (w.1 x) j i) 0) (unitVector j)

/-! ### Euclidean and matrix helpers -/

private theorem abs_coord_le_euclid {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

private theorem euclid_le_sum_abs {d : ℕ} (v : Vec d) :
    euclideanNorm v ≤ ∑ j, |v j| := by
  unfold euclideanNorm euclideanSq dot
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc v j * v j = |v j| * |v j| := (abs_mul_abs_self _).symm
    _ ≤ |v j| * ∑ k, |v k| :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun k => |v k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j))
          (abs_nonneg _)

private theorem euclid_smul {d : ℕ} (t : ℝ) (v : Vec d) :
    euclideanNorm (t • v) = |t| * euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  have h : ∑ j, (t • v) j * (t • v) j = (t * t) * ∑ j, v j * v j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h, Real.sqrt_mul (mul_self_nonneg t), Real.sqrt_mul_self_eq_abs]

private theorem euclid_unitVector {d : ℕ} (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem euclid_neg_smul_unit {d : ℕ} (t : ℝ) (k : Fin d) :
    euclideanNorm (-(t • unitVector k)) = |t| := by
  rw [← neg_smul, euclid_smul, euclid_unitVector, mul_one, abs_neg]

private theorem mulVec_unitVector_apply {d : ℕ} (M : Mat d) (i k : Fin d) :
    (M.mulVec (unitVector i)) k = M k i := by
  simp [unitVector, Matrix.mulVec_single_one]

/-- Every entry of a regular coefficient is bounded by its ellipticity constant. -/
private theorem abs_entry_le_of_regular {d : ℕ} {L : ℝ} {ω : FieldPair d} (hL : 0 < L)
    (hω : IsRegular L ω) (x : Vec d) (j i : Fin d) : |ω.1 x j i| ≤ L := by
  have h1 := Correctors.isElliptic_mulVec_euclideanNorm_le hL hω.1 x (unitVector i)
  have h2 := abs_coord_le_euclid ((ω.1 x).mulVec (unitVector i)) j
  rw [mulVec_unitVector_apply] at h2
  rw [euclid_unitVector, mul_one] at h1
  exact h2.trans h1

/-- A coordinate-wise Lipschitz bound in the Euclidean norm gives a Lipschitz bound for the
supremum metric of the domain. -/
private theorem lipschitzWith_of_euclid {d : ℕ} {g : Vec d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ x y : Vec d, |g x - g y| ≤ K * euclideanNorm (x - y)) :
    LipschitzWith (K * d).toNNReal g := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [Real.dist_eq]
  have hsum : ∑ j, |(x - y) j| ≤ d * dist x y := by
    rw [dist_eq_norm]
    calc ∑ j, |(x - y) j| ≤ ∑ _j : Fin d, ‖x - y‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (x - y) j
      _ = d * ‖x - y‖ := by simp
  calc |g x - g y| ≤ K * euclideanNorm (x - y) := h x y
    _ ≤ K * ∑ j, |(x - y) j| := mul_le_mul_of_nonneg_left (euclid_le_sum_abs _) hK
    _ ≤ K * (d * dist x y) := mul_le_mul_of_nonneg_left hsum hK
    _ = K * d * dist x y := by ring

/-- Real estimate for a difference quotient: `|t⁻¹ (a - b)| ≤ K` when `|a - b| ≤ K |t|`. -/
private theorem abs_slope_le {t a b K : ℝ} (ht : t ≠ 0) (hK : 0 ≤ K)
    (hab : |a - b| ≤ K * |t|) : |t⁻¹ * (a - b)| ≤ K := by
  have hpos : 0 < |t| := abs_pos.mpr ht
  rw [abs_mul, abs_inv]
  calc |t|⁻¹ * |a - b| ≤ |t|⁻¹ * (K * |t|) :=
        mul_le_mul_of_nonneg_left hab (inv_nonneg.mpr hpos.le)
    _ = K := by
        rw [mul_comm K, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]

/-! ### Differentiability of coefficient columns -/

/-- The slope of a function at the origin along the direction `-e` is its directional derivative
along `-e`. -/
private theorem tendsto_slope_dir {d : ℕ} (g : Vec d → ℝ) (e : Vec d)
    (hg : DifferentiableAt ℝ g 0) :
    Tendsto (fun t : ℝ => t⁻¹ * (g (-(t • e)) - g 0)) (𝓝[≠] (0 : ℝ))
      (𝓝 (-(fderiv ℝ g 0 e))) := by
  have hf : HasDerivAt (fun t : ℝ => t • -e) (-e) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const (-e)
  have hg' : HasFDerivAt g (fderiv ℝ g 0) ((0 : ℝ) • -e) := by
    rw [zero_smul]
    exact hg.hasFDerivAt
  have hc : HasDerivAt (g ∘ fun t : ℝ => t • -e) (fderiv ℝ g 0 (-e)) 0 :=
    hg'.comp_hasDerivAt 0 hf
  have hs := hasDerivAt_iff_tendsto_slope_zero.mp hc
  rw [map_neg] at hs
  refine Filter.Tendsto.congr (fun t => ?_) hs
  simp only [Function.comp, zero_add, zero_smul, smul_neg, neg_zero, smul_eq_mul]

/-- A Lipschitz function has a directional derivative at the origin bounded by its Lipschitz
constant. -/
private theorem abs_deriv_le_of_lipschitz {d : ℕ} {g : Vec d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hg : DifferentiableAt ℝ g 0)
    (hLip : ∀ x y : Vec d, |g x - g y| ≤ K * euclideanNorm (x - y)) (k : Fin d) :
    |fderiv ℝ g 0 (unitVector k)| ≤ K := by
  have hT : Tendsto (fun t : ℝ => |t⁻¹ * (g (-(t • unitVector k)) - g 0)|) (𝓝[≠] (0 : ℝ))
      (𝓝 |-(fderiv ℝ g 0 (unitVector k))|) :=
    ((continuous_abs : Continuous fun a : ℝ => |a|).tendsto _).comp
      (tendsto_slope_dir g (unitVector k) hg)
  have hle : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t⁻¹ * (g (-(t • unitVector k)) - g 0)| ≤ K := by
    refine eventually_nhdsWithin_of_forall fun t ht => abs_slope_le (Set.mem_compl_singleton_iff.mp ht) hK ?_
    have h := hLip (-(t • unitVector k)) 0
    rwa [sub_zero, euclid_neg_smul_unit] at h
  have h := le_of_tendsto hT hle
  rwa [abs_neg] at h

/-- Translation of the variable of a function corresponds to translation of the origin in the
differentiability condition. -/
private theorem differentiableAt_shift_iff {d : ℕ} (h : Vec d → ℝ) (y : Vec d) :
    DifferentiableAt ℝ (fun z => h (y + z)) 0 ↔ DifferentiableAt ℝ h y := by
  constructor
  · intro hd
    have h1 : DifferentiableAt ℝ (fun z => h (y + z)) ((fun z : Vec d => z - y) y) := by
      show DifferentiableAt ℝ (fun z => h (y + z)) (y - y)
      rw [sub_self]
      exact hd
    have h2 : DifferentiableAt ℝ (fun z : Vec d => z - y) y := differentiableAt_id.sub_const y
    have h3 : DifferentiableAt ℝ ((fun z => h (y + z)) ∘ fun z : Vec d => z - y) y :=
      DifferentiableAt.comp (f := fun z : Vec d => z - y) y h1 h2
    have hfun : ((fun z => h (y + z)) ∘ fun z : Vec d => z - y) = h := by
      funext z
      show h (y + (z - y)) = h z
      congr 1
      abel
    rw [hfun] at h3
    exact h3
  · intro hh
    have h1 : DifferentiableAt ℝ h (y + 0) := by
      rw [add_zero]
      exact hh
    have h2 : DifferentiableAt ℝ (fun z : Vec d => y + z) 0 :=
      (differentiableAt_const y).add differentiableAt_id
    exact h1.comp 0 h2

/-- The points `(w, x)` at which the `(j, i)` entry of the coefficient `w` is not differentiable
in `x`. -/
private def nondiffSet {d : ℕ} (j i : Fin d) : Set (FieldPair d × Vec d) :=
  {p | DifferentiableAt ℝ (fun y => p.1.1 y j i) p.2}ᶜ

/-- The coefficient pairs at which the `(j, i)` entry is not differentiable at the origin. -/
private def originSlice {d : ℕ} (j i : Fin d) : Set (FieldPair d) :=
  (fun w : FieldPair d => (w, (0 : Vec d))) ⁻¹' nondiffSet j i

private theorem continuous_entry {d : ℕ} (x : Vec d) (j i : Fin d) :
    Continuous fun ω : FieldPair d => ω.1 x j i := by
  have h1 : Continuous fun ω : FieldPair d => ω.1 x :=
    (continuous_eval_const x).comp continuous_fst
  exact (continuous_apply i).comp ((continuous_apply j).comp h1)

private theorem continuous_entry_uncurry {d : ℕ} (j i : Fin d) :
    Continuous (Function.uncurry fun (ω : FieldPair d) (x : Vec d) => ω.1 x j i) := by
  have h1 : Continuous fun p : FieldPair d × Vec d => p.1.1 p.2 :=
    continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
  exact (continuous_apply i).comp ((continuous_apply j).comp h1)

/-- Almost every coefficient has a column that is differentiable at the origin. The coefficient
is taken from a stationary law; the column is Lipschitz with constant `K` almost surely. -/
private theorem ae_differentiableAt_zero_of_stationary {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (j i : Fin d) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ w ∂μ, ∀ x y : Vec d, |w.1 x j i - w.1 y j i| ≤ K * euclideanNorm (x - y)) :
    ∀ᵐ w ∂μ, DifferentiableAt ℝ (fun y => w.1 y j i) 0 := by
  have hNm : MeasurableSet (nondiffSet j i) :=
    (measurableSet_of_differentiableAt_with_param ℝ (continuous_entry_uncurry j i)).compl
  -- Rademacher's theorem on each orbit: the non-differentiability set is Lebesgue-null.
  have hsl : ∀ᵐ w ∂μ, (volume : Measure (Vec d)) (Prod.mk w ⁻¹' nondiffSet j i) = 0 := by
    filter_upwards [hK] with w hw
    have hLip : LipschitzWith (K * d).toNNReal (fun y => w.1 y j i) :=
      lipschitzWith_of_euclid hK0 hw
    have hae : ∀ᵐ x ∂(volume : Measure (Vec d)), DifferentiableAt ℝ (fun y => w.1 y j i) x :=
      hLip.ae_differentiableAt
    exact ae_iff.mp hae
  have hM0 : MeasurableSet (originSlice j i) := by
    unfold originSlice
    exact hNm.preimage (measurable_id.prodMk measurable_const)
  have hshift : ∀ (y : Vec d) (w : FieldPair d),
      (w, y) ∈ nondiffSet j i ↔ (translate y w, (0 : Vec d)) ∈ nondiffSet j i := by
    intro y w
    show ¬ DifferentiableAt ℝ (fun z => w.1 z j i) y ↔
      ¬ DifferentiableAt ℝ (fun z => (translate y w).1 z j i) 0
    exact (differentiableAt_shift_iff (fun z => w.1 z j i) y).not.symm
  have hpre : ∀ y : Vec d, (fun w : FieldPair d => (w, y)) ⁻¹' nondiffSet j i =
      translate y ⁻¹' originSlice j i := by
    intro y
    ext w
    exact hshift y w
  -- Stationarity: each vertical slice has the same measure as the origin slice.
  have hslice : ∀ y : Vec d, μ ((fun w : FieldPair d => (w, y)) ⁻¹' nondiffSet j i) =
      μ (originSlice j i) := by
    intro y
    have hT : μ.map (translate y) (originSlice j i) = μ (translate y ⁻¹' originSlice j i) :=
      Measure.map_apply (Probability.measurable_translate y) hM0
    rw [hμ y] at hT
    rw [hpre y]
    exact hT.symm
  have hvol : (volume : Measure (Vec d)) Set.univ ≠ 0 :=
    (IsOpen.measure_pos (volume : Measure (Vec d)) isOpen_univ Set.univ_nonempty).ne'
  have hout : (μ.prod (volume : Measure (Vec d))) (nondiffSet j i) = 0 := by
    calc (μ.prod (volume : Measure (Vec d))) (nondiffSet j i)
        = ∫⁻ w, (volume : Measure (Vec d)) (Prod.mk w ⁻¹' nondiffSet j i) ∂μ :=
          Measure.prod_apply hNm
      _ = ∫⁻ _, 0 ∂μ := lintegral_congr_ae (hsl.mono fun w hw => hw)
      _ = 0 := lintegral_zero
  have hout2 : (μ.prod (volume : Measure (Vec d))) (nondiffSet j i) =
      μ (originSlice j i) * (volume : Measure (Vec d)) Set.univ := by
    calc (μ.prod (volume : Measure (Vec d))) (nondiffSet j i)
        = ∫⁻ y, μ ((fun w : FieldPair d => (w, y)) ⁻¹' nondiffSet j i)
            ∂(volume : Measure (Vec d)) := Measure.prod_apply_symm hNm
      _ = ∫⁻ _, μ (originSlice j i) ∂(volume : Measure (Vec d)) :=
          lintegral_congr fun y => hslice y
      _ = μ (originSlice j i) * (volume : Measure (Vec d)) Set.univ := lintegral_const _
  have hc0 : μ (originSlice j i) = 0 := by
    have h := hout.symm.trans hout2
    exact (mul_eq_zero.mp h.symm).resolve_right hvol
  exact ae_iff.mpr hc0

/-! ### Reduced coefficients on the reduced reference law -/

private noncomputable def reducedLip (Λ₀ : ℝ) : ℝ := Real.exp (2 * Λ₀) * (Λ₀ + 2 * Λ₀ ^ 2)

private noncomputable def reducedBound (Λ₀ : ℝ) : ℝ := Real.exp (2 * Λ₀) * Λ₀

private theorem reducedLip_nonneg {Λ₀ : ℝ} (hΛ : 1 ≤ Λ₀) : 0 ≤ reducedLip Λ₀ := by
  unfold reducedLip
  have := sq_nonneg Λ₀
  exact mul_nonneg (Real.exp_pos _).le (by linarith)

private theorem continuous_entry_closed {d : ℕ} (i : Fin d) (K : ℝ) :
    IsClosed {w : FieldPair d | ∀ j : Fin d, ∀ x y : Vec d,
      |w.1 x j i - w.1 y j i| ≤ K * euclideanNorm (x - y)} := by
  simp only [Set.setOf_forall]
  refine isClosed_iInter fun j => isClosed_iInter fun x => isClosed_iInter fun y => ?_
  exact isClosed_le ((continuous_entry x j i).sub (continuous_entry y j i)).abs continuous_const

private theorem isClosed_entryBound {d : ℕ} (i : Fin d) (B : ℝ) :
    IsClosed {w : FieldPair d | ∀ j : Fin d, |w.1 0 j i| ≤ B} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun j => isClosed_le (continuous_entry 0 j i).abs continuous_const

/-- The closed set of coefficient pairs whose column `i` has the reduced Lipschitz constant and
whose entries at the origin are bounded by the reduced bound. -/
private def reducedColumnSet {d : ℕ} (Λ₀ : ℝ) (i : Fin d) : Set (FieldPair d) :=
  {w | ∀ j : Fin d, ∀ x y : Vec d,
      |w.1 x j i - w.1 y j i| ≤ reducedLip Λ₀ * euclideanNorm (x - y)} ∩
    {w | ∀ j : Fin d, |w.1 0 j i| ≤ reducedBound Λ₀}

private theorem isClosed_reducedColumnSet {d : ℕ} (Λ₀ : ℝ) (i : Fin d) :
    IsClosed (reducedColumnSet Λ₀ i) :=
  (continuous_entry_closed i (reducedLip Λ₀)).inter (isClosed_entryBound i (reducedBound Λ₀))

private theorem reduce_mem_reducedColumnSet {d : ℕ} {Λ₀ : ℝ} (hΛ : 1 ≤ Λ₀) {η : FieldPair d}
    (hη : IsRegular Λ₀ η) (i : Fin d) : reduce η ∈ reducedColumnSet Λ₀ i := by
  have hΛ0 : 0 < Λ₀ := by linarith
  refine ⟨?_, ?_⟩
  · intro j x y
    have hL := Correctors.reducedCoefficient_operatorLipschitz hΛ hη x y (unitVector i)
    rw [euclid_unitVector, mul_one] at hL
    have hc := abs_coord_le_euclid
      ((reducedCoefficient η x - reducedCoefficient η y).mulVec (unitVector i)) j
    rw [mulVec_unitVector_apply, Matrix.sub_apply] at hc
    exact hc.trans hL
  · intro j
    have hc := clockDensity_bounds η 0 Λ₀ (hη.2.1 0)
    show |reducedCoefficient η 0 j i| ≤ reducedBound Λ₀
    rw [reducedCoefficient, Matrix.smul_apply, smul_eq_mul, abs_mul,
      abs_of_pos (clockDensity_pos η 0)]
    exact mul_le_mul hc.2 (abs_entry_le_of_regular hΛ0 hη 0 j i) (abs_nonneg _)
      (Real.exp_pos _).le

/-- Transfer of the reduced column bounds from the physical regularity event through `reduce`. -/
private theorem ae_reducedColumnSet {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, w ∈ reducedColumnSet Λ₀ i := by
  unfold Carriers.reducedReferenceLaw
  refine (ae_map_iff (p := fun w => w ∈ reducedColumnSet Λ₀ i)
    (Probability.measurable_reduce (d := d)).aemeasurable
    (isClosed_reducedColumnSet Λ₀ i).measurableSet).2 ?_
  filter_upwards [Q.regular] with η hη
  exact reduce_mem_reducedColumnSet Q.ellipticity_parameter hη i

/-! ### Translations and difference quotients -/

private theorem integral_mul_eq_inner {d : ℕ} {μ : Measure (FieldPair d)}
    (V : FieldPair d → ℝ) (hV : MemLp V 2 μ) (G : Lp ℝ 2 μ) :
    ∫ w, V w * G w ∂μ = inner ℝ (hV.toLp V) G := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hV.coeFn_toLp] with w hw
  simp only [hw]
  simp [RCLike.inner_apply, mul_comm]

/-- Stationarity moves a translation from one factor of a product onto the other factor. -/
private theorem integral_mul_translate_eq {d : ℕ} {μ : Measure (FieldPair d)}
    (hμ : IsStationary μ) (s : Vec d) {φ ψ : FieldPair d → ℝ} (hφ : Measurable φ)
    (hψ : AEStronglyMeasurable ψ μ) :
    ∫ w, φ w * ψ (translate s w) ∂μ = ∫ w, φ (translate (-s) w) * ψ w ∂μ := by
  have hT : Measurable (translate s) := Probability.measurable_translate s
  have hTm : Measurable (translate (-s)) := Probability.measurable_translate (-s)
  have hinv : ∀ w : FieldPair d, translate (-s) (translate s w) = w := fun w => by
    rw [translate_add, neg_add_cancel, translate_zero]
  have hfm : AEStronglyMeasurable (fun w => φ (translate (-s) w) * ψ w)
      (Measure.map (translate s) μ) := by
    rw [hμ s]
    exact ((hφ.comp hTm).aestronglyMeasurable).mul hψ
  have key : ∫ w, φ (translate (-s) w) * ψ w ∂μ =
      ∫ w, φ (translate (-s) (translate s w)) * ψ (translate s w) ∂μ := by
    have h := integral_map hT.aemeasurable hfm
    rw [hμ s] at h
    exact h
  calc ∫ w, φ w * ψ (translate s w) ∂μ
      = ∫ w, φ (translate (-s) (translate s w)) * ψ (translate s w) ∂μ := by
        simp only [hinv]
    _ = ∫ w, φ (translate (-s) w) * ψ w ∂μ := key.symm

private theorem integrable_translate_lp {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (s : Vec d) (F : Lp ℝ 2 μ) :
    Integrable (fun w => F (translate s w)) μ :=
  ((Lp.memLp (translationLp μ hμ s F)).integrable (by norm_num)).congr
    (coeFn_translationLp μ hμ s F)

private theorem coeFn_smul_translateLp_sub {d : ℕ} {μ : Measure (FieldPair d)}
    (hμ : IsStationary μ) (F : Lp ℝ 2 μ) (c : ℝ) (s : Vec d) :
    ∀ᵐ w ∂μ, (c • (translationLp μ hμ s F - F)) w = c * (F (translate s w) - F w) := by
  filter_upwards [Lp.coeFn_smul c (translationLp μ hμ s F - F),
    Lp.coeFn_sub (translationLp μ hμ s F) F, coeFn_translationLp μ hμ s F] with w h1 h2 h3
  rw [h1, Pi.smul_apply, smul_eq_mul, h2, Pi.sub_apply, h3]

/-- The pairing of a bounded column with a scaled difference quotient of `F` equals the pairing of
the shifted column difference with `F`. -/
private theorem integral_column_mul_translate_sub {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (k i : Fin d) {K B : ℝ}
    (hK : ∀ᵐ w ∂μ, ∀ x y : Vec d, |w.1 x k i - w.1 y k i| ≤ K * euclideanNorm (x - y))
    (hB : ∀ᵐ w ∂μ, |w.1 0 k i| ≤ B) (F : Lp ℝ 2 μ) (c : ℝ) (s : Vec d) :
    ∫ w, w.1 0 k i * (c • (translationLp μ hμ s F - F)) w ∂μ =
      ∫ w, (c * (w.1 (-s) k i - w.1 0 k i)) * F w ∂μ := by
  have hVm : Measurable (fun w : FieldPair d => w.1 0 k i) := (continuous_entry 0 k i).measurable
  have hFi : Integrable (⇑F) μ := (Lp.memLp F).integrable (by norm_num)
  have hBae : ∀ᵐ w ∂μ, ‖w.1 0 k i‖ ≤ B := by
    filter_upwards [hB] with w hw
    rw [Real.norm_eq_abs]
    exact hw
  have hI1 : Integrable (fun w : FieldPair d => w.1 0 k i * F (translate s w)) μ :=
    Integrable.bdd_mul (integrable_translate_lp hμ s F) hVm.aestronglyMeasurable hBae
  have hI2 : Integrable (fun w : FieldPair d => w.1 0 k i * F w) μ :=
    Integrable.bdd_mul hFi hVm.aestronglyMeasurable hBae
  have hI3 : Integrable (fun w : FieldPair d => w.1 (-s) k i * F w) μ := by
    have hbd : ∀ᵐ w ∂μ, ‖w.1 (-s) k i‖ ≤ B + K * euclideanNorm (-s) := by
      filter_upwards [hK, hB] with w hk hb
      rw [Real.norm_eq_abs]
      have h1 := hk (-s) 0
      rw [sub_zero] at h1
      have h2 := abs_sub_abs_le_abs_sub (w.1 (-s) k i) (w.1 0 k i)
      linarith
    exact Integrable.bdd_mul hFi (continuous_entry (-s) k i).aestronglyMeasurable hbd
  have hS1 : ∫ w, w.1 0 k i * F (translate s w) ∂μ = ∫ w, w.1 (-s) k i * F w ∂μ := by
    rw [integral_mul_translate_eq hμ s hVm (Lp.aestronglyMeasurable F)]
    simp only [translate_matrix, add_zero]
  calc ∫ w, w.1 0 k i * (c • (translationLp μ hμ s F - F)) w ∂μ
      = ∫ w, c * (w.1 0 k i * F (translate s w) - w.1 0 k i * F w) ∂μ :=
        integral_congr_ae (by
          filter_upwards [coeFn_smul_translateLp_sub hμ F c s] with w hw
          simp only [hw]
          ring)
    _ = c * ∫ w, (w.1 0 k i * F (translate s w) - w.1 0 k i * F w) ∂μ :=
        integral_const_mul _ _
    _ = c * (∫ w, w.1 0 k i * F (translate s w) ∂μ - ∫ w, w.1 0 k i * F w ∂μ) := by
        rw [integral_sub hI1 hI2]
    _ = c * (∫ w, w.1 (-s) k i * F w ∂μ - ∫ w, w.1 0 k i * F w ∂μ) := by
        rw [hS1]
    _ = c * ∫ w, (w.1 (-s) k i * F w - w.1 0 k i * F w) ∂μ := by
        rw [integral_sub hI3 hI2]
    _ = ∫ w, c * (w.1 (-s) k i * F w - w.1 0 k i * F w) ∂μ :=
        (integral_const_mul _ _).symm
    _ = ∫ w, (c * (w.1 (-s) k i - w.1 0 k i)) * F w ∂μ := by
        congr 1
        funext w
        ring

/-- Per-coordinate weak identity: for a horizontally smooth pairing with `F` and L² derivative
`D` in direction `k`, `∫ a_{ki} D = -∫ ∂_k a_{ki} F`. -/
private theorem integral_column_mul_deriv {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (k i : Fin d) {K B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ w ∂μ, ∀ x y : Vec d, |w.1 x k i - w.1 y k i| ≤ K * euclideanNorm (x - y))
    (hB : ∀ᵐ w ∂μ, |w.1 0 k i| ≤ B) (F D : Lp ℝ 2 μ)
    (hD : HasHorizontalLpDerivative μ hμ k F D) :
    ∫ w, w.1 0 k i * D w ∂μ =
      -∫ w, fderiv ℝ (fun y => w.1 y k i) 0 (unitVector k) * F w ∂μ := by
  have hdiff : ∀ᵐ w ∂μ, DifferentiableAt ℝ (fun y => w.1 y k i) 0 :=
    ae_differentiableAt_zero_of_stationary hμ k i hK0 hK
  have hVm : Measurable (fun w : FieldPair d => w.1 0 k i) := (continuous_entry 0 k i).measurable
  have hBae : ∀ᵐ w ∂μ, ‖w.1 0 k i‖ ≤ B := by
    filter_upwards [hB] with w hw
    rw [Real.norm_eq_abs]
    exact hw
  have hVL : MemLp (fun w : FieldPair d => w.1 0 k i) 2 μ :=
    MemLp.of_bound hVm.aestronglyMeasurable B hBae
  have hD' : Tendsto (fun t : ℝ => t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F))
      (𝓝[≠] (0 : ℝ)) (𝓝 D) := hD
  have hL2 : Tendsto (fun t : ℝ => inner ℝ (hVL.toLp (fun w : FieldPair d => w.1 0 k i))
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (inner ℝ (hVL.toLp (fun w : FieldPair d => w.1 0 k i)) D)) :=
    tendsto_const_nhds.inner hD'
  have hS : ∀ t : ℝ, inner ℝ (hVL.toLp (fun w : FieldPair d => w.1 0 k i))
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)) =
      ∫ w, (t⁻¹ * (w.1 (-(t • unitVector k)) k i - w.1 0 k i)) * F w ∂μ := by
    intro t
    rw [← integral_mul_eq_inner _ hVL]
    exact integral_column_mul_translate_sub hμ k i hK hB F t⁻¹ (t • unitVector k)
  have hDCT : Tendsto
      (fun t : ℝ => ∫ w, (t⁻¹ * (w.1 (-(t • unitVector k)) k i - w.1 0 k i)) * F w ∂μ)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ w, -(fderiv ℝ (fun y => w.1 y k i) 0 (unitVector k)) * F w ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => K * |F w|) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun t => ?_
      have hc : Continuous fun w : FieldPair d =>
          t⁻¹ * (w.1 (-(t • unitVector k)) k i - w.1 0 k i) :=
        continuous_const.mul ((continuous_entry (-(t • unitVector k)) k i).sub
          (continuous_entry 0 k i))
      exact hc.measurable.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
    · refine eventually_nhdsWithin_of_forall fun t ht => ?_
      have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
      filter_upwards [hK] with w hw
      have h := hw (-(t • unitVector k)) 0
      rw [sub_zero, euclid_neg_smul_unit] at h
      rw [Real.norm_eq_abs, abs_mul (t⁻¹ * (w.1 (-(t • unitVector k)) k i - w.1 0 k i)) (F w)]
      exact mul_le_mul_of_nonneg_right (abs_slope_le ht0 hK0 h) (abs_nonneg _)
    · exact ((Lp.memLp F).integrable (by norm_num)).abs.const_mul K
    · filter_upwards [hdiff] with w hw
      exact (tendsto_slope_dir (fun y => w.1 y k i) (unitVector k) hw).mul_const (F w)
  have hL1 : Tendsto (fun t : ℝ => inner ℝ (hVL.toLp (fun w : FieldPair d => w.1 0 k i))
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ w, -(fderiv ℝ (fun y => w.1 y k i) 0 (unitVector k)) * F w ∂μ)) :=
    hDCT.congr fun t => (hS t).symm
  have hEq := tendsto_nhds_unique hL2 hL1
  rw [integral_mul_eq_inner _ hVL D, hEq]
  simp only [neg_mul, integral_neg]

/-- Per-coordinate weak identity for a bounded measurable factor `φ` whose orbit increments along
`e_k` are Lipschitz and whose orbit is differentiable at the origin: for an L² derivative `D` of `F`
in direction `k`, `∫ φ D = -∫ ∂_k φ F`. -/
theorem integral_mul_deriv_of_orbit {d : ℕ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hμ : IsStationary μ) (k : Fin d) {φ : FieldPair d → ℝ}
    (hφ : Measurable φ) {K B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ᵐ w ∂μ, ∀ t : ℝ, |φ (translate (-(t • unitVector k)) w) - φ w| ≤ K * |t|)
    (hB : ∀ᵐ w ∂μ, |φ w| ≤ B)
    (hdiff : ∀ᵐ w ∂μ, DifferentiableAt ℝ (fun y => φ (translate y w)) 0)
    (F D : Lp ℝ 2 μ) (hD : HasHorizontalLpDerivative μ hμ k F D) :
    ∫ w, φ w * D w ∂μ =
      -∫ w, fderiv ℝ (fun y => φ (translate y w)) 0 (unitVector k) * F w ∂μ := by
  have hBae : ∀ᵐ w ∂μ, ‖φ w‖ ≤ B := by
    filter_upwards [hB] with w hw
    rw [Real.norm_eq_abs]
    exact hw
  have hVL : MemLp φ 2 μ := MemLp.of_bound hφ.aestronglyMeasurable B hBae
  have hFi : Integrable (⇑F) μ := (Lp.memLp F).integrable (by norm_num)
  have hS : ∀ t : ℝ, inner ℝ (hVL.toLp φ)
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)) =
      ∫ w, (t⁻¹ * (φ (translate (-(t • unitVector k)) w) - φ w)) * F w ∂μ := by
    intro t
    rw [← integral_mul_eq_inner _ hVL]
    have hI1 : Integrable (fun w => φ w * F (translate (t • unitVector k) w)) μ :=
      Integrable.bdd_mul (integrable_translate_lp hμ (t • unitVector k) F) hφ.aestronglyMeasurable
        hBae
    have hI2 : Integrable (fun w => φ w * F w) μ :=
      Integrable.bdd_mul hFi hφ.aestronglyMeasurable hBae
    have hI3 : Integrable (fun w => φ (translate (-(t • unitVector k)) w) * F w) μ := by
      have hbd : ∀ᵐ w ∂μ, ‖φ (translate (-(t • unitVector k)) w)‖ ≤ B + K * |t| := by
        filter_upwards [hK, hB] with w hk hb
        rw [Real.norm_eq_abs]
        have h1 := hk t
        have h2 := abs_sub_abs_le_abs_sub (φ (translate (-(t • unitVector k)) w)) (φ w)
        linarith
      exact Integrable.bdd_mul hFi
        (hφ.comp (Probability.measurable_translate _)).aestronglyMeasurable hbd
    have hS1 : ∫ w, φ w * F (translate (t • unitVector k) w) ∂μ =
        ∫ w, φ (translate (-(t • unitVector k)) w) * F w ∂μ :=
      integral_mul_translate_eq hμ (t • unitVector k) hφ (Lp.aestronglyMeasurable F)
    calc ∫ w, φ w * (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)) w ∂μ
        = ∫ w, t⁻¹ * (φ w * F (translate (t • unitVector k) w) - φ w * F w) ∂μ :=
          integral_congr_ae (by
            filter_upwards [coeFn_smul_translateLp_sub hμ F t⁻¹ (t • unitVector k)] with w hw
            simp only [hw]
            ring)
      _ = t⁻¹ * (∫ w, φ w * F (translate (t • unitVector k) w) ∂μ - ∫ w, φ w * F w ∂μ) := by
          rw [integral_const_mul, integral_sub hI1 hI2]
      _ = t⁻¹ * (∫ w, φ (translate (-(t • unitVector k)) w) * F w ∂μ - ∫ w, φ w * F w ∂μ) := by
          rw [hS1]
      _ = ∫ w, (t⁻¹ * (φ (translate (-(t • unitVector k)) w) - φ w)) * F w ∂μ := by
          rw [← integral_sub hI3 hI2, ← integral_const_mul]
          congr 1
          funext w
          ring
  have hD' : Tendsto (fun t : ℝ => t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F))
      (𝓝[≠] (0 : ℝ)) (𝓝 D) := hD
  have hL2 : Tendsto (fun t : ℝ => inner ℝ (hVL.toLp φ)
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (inner ℝ (hVL.toLp φ) D)) :=
    tendsto_const_nhds.inner hD'
  have hDCT : Tendsto
      (fun t : ℝ => ∫ w, (t⁻¹ * (φ (translate (-(t • unitVector k)) w) - φ w)) * F w ∂μ)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ w, -(fderiv ℝ (fun y => φ (translate y w)) 0 (unitVector k)) * F w ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun w => K * |F w|) ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall fun t => ?_
      have hc : Measurable fun w : FieldPair d =>
          t⁻¹ * (φ (translate (-(t • unitVector k)) w) - φ w) :=
        measurable_const.mul ((hφ.comp (Probability.measurable_translate _)).sub hφ)
      exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable F)
    · refine eventually_nhdsWithin_of_forall fun t ht => ?_
      have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp ht
      filter_upwards [hK] with w hw
      rw [Real.norm_eq_abs, abs_mul (t⁻¹ * (φ (translate (-(t • unitVector k)) w) - φ w)) (F w)]
      exact mul_le_mul_of_nonneg_right (abs_slope_le ht0 hK0 (hw t)) (abs_nonneg _)
    · exact ((Lp.memLp F).integrable (by norm_num)).abs.const_mul K
    · filter_upwards [hdiff] with w hw
      have h := (tendsto_slope_dir (fun y => φ (translate y w)) (unitVector k) hw).mul_const (F w)
      simpa only [translate_zero] using h
  have hL1 : Tendsto (fun t : ℝ => inner ℝ (hVL.toLp φ)
      (t⁻¹ • (translationLp μ hμ (t • unitVector k) F - F)))
      (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ w, -(fderiv ℝ (fun y => φ (translate y w)) 0 (unitVector k)) * F w ∂μ)) :=
    hDCT.congr fun t => (hS t).symm
  have hEq := tendsto_nhds_unique hL2 hL1
  rw [integral_mul_eq_inner _ hVL D, hEq]
  simp only [neg_mul, integral_neg]

/-- Almost every reduced coefficient has entries with Lipschitz increments from the origin, bounded
at the origin, and differentiable at the origin with bounded derivatives. -/
theorem ae_entry_regular {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) :
    ∃ L B : ℝ, 0 ≤ L ∧ 0 ≤ B ∧ ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ j i : Fin d,
      (∀ (k : Fin d) (t : ℝ), |w.1 (-(t • unitVector k)) j i - w.1 0 j i| ≤ L * |t|) ∧
      |w.1 0 j i| ≤ B ∧ DifferentiableAt ℝ (fun y => w.1 y j i) 0 ∧
      ∀ k : Fin d, |fderiv ℝ (fun y => w.1 y j i) 0 (unitVector k)| ≤ L := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  have hK0 : 0 ≤ reducedLip Λ₀ := reducedLip_nonneg Q.ellipticity_parameter
  refine ⟨reducedLip Λ₀, max (reducedBound Λ₀) 0, hK0, le_max_right _ _, ?_⟩
  rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro i
  have hLip : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      ∀ x y : Vec d, |w.1 x j i - w.1 y j i| ≤ reducedLip Λ₀ * euclideanNorm (x - y) := by
    filter_upwards [ae_reducedColumnSet Q i] with w hw
    exact hw.1 j
  filter_upwards [ae_reducedColumnSet Q i, ae_differentiableAt_zero_of_stationary hQ j i hK0 hLip]
    with w hw hd
  refine ⟨fun k t => ?_, (hw.2 j).trans (le_max_left _ _), hd, fun k =>
    abs_deriv_le_of_lipschitz hK0 hd (hw.1 j) k⟩
  have h := hw.1 j (-(t • unitVector k)) 0
  rwa [sub_zero, euclid_neg_smul_unit] at h

/-! ### The weak divergence of the reduced column -/

/-- The weak horizontal divergence of the `i`-th column `x ↦ a(x) e_i` of the reduced
coefficient, under the reduced reference law, is `cdiv i`. The column is Lipschitz with a constant
depending only on `Λ₀`; the Lipschitz bound and the bound at the origin come from the regularity of
the physical environment through `reduce`. -/
theorem hasWeakHorizontalDivergence_reducedColumn {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q))
    (i : Fin d) :
    HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ
      (fun w : FieldPair d => (w.1 0).mulVec (unitVector i)) (cdiv i) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  have hΛ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hK0 : 0 ≤ reducedLip Λ₀ := reducedLip_nonneg hΛ
  have hgood := ae_reducedColumnSet Q i
  have hLip : ∀ k : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      ∀ x y : Vec d, |w.1 x k i - w.1 y k i| ≤ reducedLip Λ₀ * euclideanNorm (x - y) := by
    intro k
    filter_upwards [hgood] with w hw
    exact hw.1 k
  have hBd : ∀ k : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      |w.1 0 k i| ≤ reducedBound Λ₀ := by
    intro k
    filter_upwards [hgood] with w hw
    exact hw.2 k
  have hdiff : ∀ j : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      DifferentiableAt ℝ (fun y => w.1 y j i) 0 :=
    fun j => ae_differentiableAt_zero_of_stationary hQ j i hK0 (hLip j)
  have hGbd : ∀ j : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      ‖fderiv ℝ (fun y => w.1 y j i) 0 (unitVector j)‖ ≤ reducedLip Λ₀ := by
    intro j
    filter_upwards [hdiff j, hLip j] with w hd hl
    rw [Real.norm_eq_abs]
    exact abs_deriv_le_of_lipschitz hK0 hd hl j
  have hmeasG : ∀ j : Fin d,
      Measurable (fun w : FieldPair d => fderiv ℝ (fun y => w.1 y j i) 0 (unitVector j)) := by
    intro j
    have h := measurable_fderiv_apply_const_with_param ℝ
      (continuous_entry_uncurry j i) (unitVector j)
    have hpair : Measurable (fun w : FieldPair d => (w, (0 : Vec d))) :=
      measurable_id.prodMk measurable_const
    exact h.comp hpair
  have hmeas : Measurable (cdiv i) := by
    unfold cdiv
    exact Finset.measurable_sum _ fun j _ => hmeasG j
  refine ⟨fun k => ?_, ?_, fun F _hF DF hDF => ?_⟩
  · simp only [mulVec_unitVector_apply]
    exact Integrable.of_bound (continuous_entry 0 k i).aestronglyMeasurable (reducedBound Λ₀)
      (by
        filter_upwards [hBd k] with w hw
        rw [Real.norm_eq_abs]
        exact hw)
  · refine Integrable.of_bound hmeas.aestronglyMeasurable ((d : ℝ) * reducedLip Λ₀) ?_
    filter_upwards [ae_all_iff.mpr hGbd] with w hw
    unfold cdiv
    calc ‖∑ j, (fderiv ℝ (fun x => (w.1 x) j i) 0) (unitVector j)‖
        ≤ ∑ j, ‖(fderiv ℝ (fun x => (w.1 x) j i) 0) (unitVector j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin d, reducedLip Λ₀ := Finset.sum_le_sum fun j _ => hw j
      _ = (d : ℝ) * reducedLip Λ₀ := by simp
  · have hFi : Integrable (⇑F) (Carriers.reducedReferenceLaw Q) :=
      (Lp.memLp F).integrable (by norm_num)
    have hint : ∀ k : Fin d,
        Integrable (fun w : FieldPair d => w.1 0 k i * DF k w)
          (Carriers.reducedReferenceLaw Q) := fun k =>
      Integrable.bdd_mul (c := reducedBound Λ₀) ((Lp.memLp (DF k)).integrable (by norm_num))
        (continuous_entry 0 k i).aestronglyMeasurable (by
          filter_upwards [hBd k] with w hw
          rw [Real.norm_eq_abs]
          exact hw)
    have hintG : ∀ j : Fin d,
        Integrable (fun w : FieldPair d => fderiv ℝ (fun y => w.1 y j i) 0 (unitVector j) * F w)
          (Carriers.reducedReferenceLaw Q) := fun j =>
      Integrable.bdd_mul (c := reducedLip Λ₀) hFi (hmeasG j).aestronglyMeasurable (hGbd j)
    simp only [mulVec_unitVector_apply]
    rw [integral_finset_sum _ fun k _ => hint k]
    rw [Finset.sum_congr rfl fun k _ =>
      integral_column_mul_deriv hQ k i hK0 (hLip k) (hBd k) F (DF k) (hDF k)]
    unfold cdiv
    simp only [Finset.sum_mul]
    rw [integral_finset_sum _ fun j _ => hintG j, Finset.sum_neg_distrib]

/-- Almost every reduced coefficient has every entry of column `i` differentiable at the origin
(Rademacher's theorem on each orbit and stationarity). -/
theorem ae_differentiableAt_reducedColumn {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (j i : Fin d) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, DifferentiableAt ℝ (fun y => w.1 y j i) 0 := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  refine ae_differentiableAt_zero_of_stationary hQ j i (reducedLip_nonneg Q.ellipticity_parameter) ?_
  filter_upwards [ae_reducedColumnSet Q i] with w hw
  exact hw.1 j

/-- The entries of the reduced coefficient at the origin are bounded almost surely. -/
theorem exists_ae_abs_entry_le (d : ℕ) (Λ₀ r₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Q : EnvironmentLaw d Λ₀ r₀,
      ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ j k : Fin d, |w.1 0 j k| ≤ C := by
  refine ⟨max (reducedBound Λ₀) 0, le_max_right _ _, fun Q => ?_⟩
  rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k
  filter_upwards [ae_reducedColumnSet Q k] with w hw
  exact (hw.2 j).trans (le_max_left _ _)

/-- The pointwise divergence of a column is bounded almost surely. -/
theorem exists_ae_abs_cdiv_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (i : Fin d) :
    ∃ B : ℝ, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, |cdiv i w| ≤ B := by
  refine ⟨d * reducedLip Λ₀, ?_⟩
  have hK0 : 0 ≤ reducedLip Λ₀ := reducedLip_nonneg Q.ellipticity_parameter
  filter_upwards [ae_all_iff.mpr fun j => ae_differentiableAt_reducedColumn Q hQ j i,
    ae_reducedColumnSet Q i] with w hd hw
  unfold cdiv
  calc |∑ j, (fderiv ℝ (fun x => (w.1 x) j i) 0) (unitVector j)|
      ≤ ∑ j, |(fderiv ℝ (fun x => (w.1 x) j i) 0) (unitVector j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, reducedLip Λ₀ :=
        Finset.sum_le_sum fun j _ => abs_deriv_le_of_lipschitz hK0 (hd j) (hw.1 j) j
    _ = d * reducedLip Λ₀ := by simp

end DriftH5

end EinsteinRelation
