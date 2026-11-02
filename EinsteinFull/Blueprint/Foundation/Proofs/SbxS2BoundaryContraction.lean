import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability
import PDEFoundation.Geometry.EuclideanBall
import Mathlib.Algebra.QuadraticDiscriminant
import Homogenization.Sobolev.Foundations.PoincareZeroTrace
import PDEFoundation.Measure.BallVolume
import PDEFoundation.Measure.EuclideanVectorIntegral
import PDEFoundation.Sobolev.H1.Basic
import PDEFoundation.Sobolev.W1p.Mean
import PDEFoundation.Sobolev.Inequalities.ConvexPoincare
import Mathlib.MeasureTheory.Group.Measure
import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.BoundaryB
import SuperdiffusionCLT.Section7.Analytic.DeGiorgi.Boundary
import PDEFoundation.PDE.DGNM.ProductTest
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.Order.Lattice
import PDEFoundation.Sobolev.Cutoff.Ball
import PDEFoundation.PDE.DGNM.Composites
import PDEFoundation.PDE.DGNM.ChainTests
import PDEFoundation.Measure.HolderRestriction
import PDEFoundation.Measure.Superlevel
import PDEFoundation.Sobolev.H1.CutoffEnergy
import PDEFoundation.Sobolev.Inequalities.ZeroBoundarySobolevPower
import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpace

/-!
Support for the boundary contraction at `paper/main.tex:370–375`.
The native coordinate carrier and explicit Euclidean gradient norm are retained.
The final one-sided contraction uses geometry-dependent constants chosen before
the PDE data. These support lemmas do not close the tube probability node.
-/

open MeasureTheory PDE
open scoped ENNReal Topology

namespace EinsteinFull.Blueprint.SbxS2Boundary

/-- Squared distances of two points reflected about `z`. -/
theorem reflected_sq_dist_sum {d : ℕ} (c z x : Vec d) :
    euclideanSqDist x c + euclideanSqDist (z + z - x) c =
      2 * euclideanSqDist z c + 2 * euclideanSqDist x z := by
  simp only [euclideanSqDist, vecNormSq_eq_sum_sq, Pi.sub_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Reflection about the centre preserves a round ball, with its native norm. -/
theorem reflection_mem_ball {d : ℕ} (z x : Vec d) (r : ℝ) :
    z + z - x ∈ euclideanBall z r ↔ x ∈ euclideanBall z r := by
  have heq : z + z - x - z = -(x - z) := by abel
  change vecNormSq (z + z - x - z) < r ^ 2 ↔ vecNormSq (x - z) < r ^ 2
  rw [heq, vecNormSq_neg]

/-- A round ball centred outside an open round ball has at least half its
volume outside. Subadditivity permits the reflected pieces to overlap. -/
theorem ball_exterior_half_volume_of_not_mem {d : ℕ} (c z : Vec d) (R r : ℝ)
    (hz : z ∉ euclideanBall c R) :
    volume (euclideanBall z r) ≤
      2 * volume (euclideanBall z r \ euclideanBall c R) := by
  let E := euclideanBall z r \ euclideanBall c R
  let f : Vec d → Vec d := fun x => z + z - x
  have hE : MeasurableSet E :=
    (isOpen_euclideanBall z r).measurableSet.diff
      (isOpen_euclideanBall c R).measurableSet
  have hcover : euclideanBall z r ⊆ E ∪ f ⁻¹' E := by
    intro x hx
    by_cases hxc : x ∈ euclideanBall c R
    · right
      refine ⟨(reflection_mem_ball z x r).2 hx, ?_⟩
      intro hfc
      have hz' : R ^ 2 ≤ euclideanSqDist z c := le_of_not_gt hz
      have hx' : euclideanSqDist x c < R ^ 2 := hxc
      have hf' : euclideanSqDist (z + z - x) c < R ^ 2 := hfc
      have hid := reflected_sq_dist_sum c z x
      have hnn := euclideanSqDist_nonneg x z
      linarith
    · exact Or.inl ⟨hx, hxc⟩
  have hpres : MeasurePreserving f volume volume :=
    Measure.measurePreserving_sub_left volume (z + z)
  calc
    volume (euclideanBall z r) ≤ volume (E ∪ f ⁻¹' E) := measure_mono hcover
    _ ≤ volume E + volume (f ⁻¹' E) := measure_union_le _ _
    _ = volume E + volume E := by rw [hpres.measure_preimage hE.nullMeasurableSet]
    _ = 2 * volume E := (two_mul _).symm

/-- Exterior half-volume at every frontier point of an open Euclidean ball. -/
theorem ball_exterior_half_volume {d : ℕ} (c z : Vec d) (R r : ℝ)
    (hz : z ∈ frontier (euclideanBall c R)) :
    volume (euclideanBall z r) ≤
      2 * volume (euclideanBall z r \ euclideanBall c R) := by
  apply ball_exterior_half_volume_of_not_mem c z R r
  exact hz.2 ∘ fun h => (isOpen_euclideanBall c R).interior_eq.symm ▸ h

/-- Finite-volume exponent reduction keeps the chosen weak gradient exactly. -/
def h1ToW11 {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeOn U)]
    (q : H1Function U) : W1pFunction U 1 where
  toFun := q.toFun
  grad := q.grad
  memLp := q.memL2.mono_exponent (by norm_num)
  gradMemLp := fun i => (q.gradMemL2 i).mono_exponent (by norm_num)
  hasWeakGradient := q.hasWeakGradient

/-- A nonnegative integrable function vanishing on half the mass is controlled
by twice its deviation from its arithmetic mean. The zero set need only be
null measurable, as is appropriate for Sobolev representatives. -/
theorem integral_le_two_integral_abs_sub_average
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {q : α → ℝ} (hqint : Integrable q μ) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpos : μ Set.univ ≠ 0)
    (hhalf : μ Set.univ ≤ 2 * μ {x | q x = 0}) :
    (∫ x, q x ∂μ) ≤
      2 * ∫ x, |q x - (μ Set.univ).toReal⁻¹ * ∫ y, q y ∂μ| ∂μ := by
  let m := (μ Set.univ).toReal⁻¹ * ∫ x, q x ∂μ
  have hm : 0 ≤ m := mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg_of_ae hq)
  have hv : (μ Set.univ).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos (measure_ne_top μ Set.univ)).ne'
  have hid : (μ Set.univ).toReal * m = ∫ x, q x ∂μ := by
    dsimp only [m]
    rw [← mul_assoc, mul_inv_cancel₀ hv, one_mul]
  have hZ : NullMeasurableSet {x | q x = 0} μ :=
    hqint.aestronglyMeasurable.nullMeasurableSet_eq_fun aestronglyMeasurable_const
  have hhalf' : (μ Set.univ).toReal ≤ 2 * (μ {x | q x = 0}).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.mul_ne_top (by norm_num) (measure_ne_top μ _)) hhalf
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat] using h
  have hdev : Integrable (fun x => |q x - m|) μ :=
    (hqint.sub (integrable_const m)).abs
  have heq : (fun x => |q x - m|) =ᵐ[μ.restrict {x | q x = 0}] fun _ => m := by
    filter_upwards [ae_restrict_mem₀ hZ] with x hx
    rw [hx, zero_sub, abs_neg, abs_of_nonneg hm]
  have hzero : (μ {x | q x = 0}).toReal * m ≤ ∫ x, |q x - m| ∂μ := by
    calc
      (μ {x | q x = 0}).toReal * m = ∫ _ in {x | q x = 0}, m ∂μ := by
        rw [setIntegral_const]
        rfl
      _ = ∫ x in {x | q x = 0}, |q x - m| ∂μ := (integral_congr_ae heq).symm
      _ ≤ ∫ x, |q x - m| ∂μ :=
        setIntegral_le_integral hdev (Filter.Eventually.of_forall fun _ => abs_nonneg _)
  calc
    (∫ x, q x ∂μ) = (μ Set.univ).toReal * m := hid.symm
    _ ≤ (2 * (μ {x | q x = 0}).toReal) * m :=
      mul_le_mul_of_nonneg_right hhalf' hm
    _ ≤ 2 * ∫ x, |q x - m| ∂μ := by linarith only [hzero]

/-- Half-zero `L¹` Poincaré on a round ball, with an explicit dimension-only
constant and the actual Euclidean magnitude of the chosen weak gradient. -/
theorem half_zero_ball_l1_poincare {d : ℕ} (z : Vec d) {s : ℝ} (hs : 0 < s)
    (q : H1Function (euclideanBall z s))
    (hq : ∀ᵐ x ∂(volume.restrict (euclideanBall z s)), 0 ≤ q.toFun x)
    (hz : volume (euclideanBall z s) ≤
      2 * (volume.restrict (euclideanBall z s)) {x | q.toFun x = 0}) :
    (∫ x in euclideanBall z s, q.toFun x) ≤
      (2 : ℝ) ^ (d + 2) * s *
        ∫ x in euclideanBall z s, vecEuclideanNorm (q.grad x) := by
  let U := euclideanBall z s
  let : IsFiniteMeasure (volumeOn U) := isFiniteMeasure_volumeOn_euclideanBall z hs.le
  let v : W1pFunction U 1 := h1ToW11 q
  have hvint := v.integrableOn
  have hgint : Integrable (fun x => vecEuclideanNorm (q.grad x)) (volumeOn U) :=
    integrable_vecEuclideanNorm_of_coord q.grad (fun i => (v.gradMemLp i).integrable le_rfl)
  have hmean := v.meanZeroOn_subAverage (volume_euclideanBall_pos z hs)
    (volume_euclideanBall_ne_top z hs.le).lt_top
  have hp := meanZeroPoincare_on_euclideanBall_unnormalized (p := 1) le_rfl z hs
  rw [ENNReal.ofReal_one] at hp
  have hp := hp v.subAverage hmean
  have hdevint := v.subAverage.integrableOn
  have hleft : (eLpNormOn U 1 v.subAverage.toFun).toReal =
      ∫ x in U, |q.toFun x - integralAverage U q.toFun| := by
    rw [eLpNormOn, eLpNorm_one_eq_lintegral_enorm hdevint.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hdevint.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change ‖v.subAverage.toFun x‖ = _
      rw [Real.norm_eq_abs, show v.subAverage.toFun x =
        q.toFun x - integralAverage U q.toFun from W1pFunction.subAverage_apply v x]
  have hright : (euclideanFieldELpNormOn U 1 v.subAverage.grad).toReal =
      ∫ x in U, vecEuclideanNorm (q.grad x) := by
    have heq : v.subAverage.grad = q.grad := by
      funext x
      exact W1pFunction.subAverage_grad v x
    rw [heq, euclideanFieldELpNormOn, eLpNormOn,
      eLpNorm_one_eq_lintegral_enorm hgint.aestronglyMeasurable,
      ← integral_norm_eq_lintegral_enorm hgint.aestronglyMeasurable]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x =>
      Real.norm_of_nonneg (vecEuclideanNorm_nonneg _)
  have hgradfin : euclideanFieldELpNormOn U 1 v.subAverage.grad ≠ ⊤ := by
    have heq : v.subAverage.grad = q.grad := by
      funext x
      exact W1pFunction.subAverage_grad v x
    rw [heq]
    exact (memLp_one_iff_integrable.mpr hgint).eLpNorm_ne_top
  have hp' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgradfin) hp
  rw [hleft, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hright] at hp'
  have hqint : Integrable q.toFun (volumeOn U) := hvint
  have habsorb := integral_le_two_integral_abs_sub_average (volumeOn U) hqint hq
    (by simpa only [volumeOn, Measure.restrict_apply_univ] using
      (volume_euclideanBall_pos z hs).ne')
    (by simpa only [U, volumeOn, Measure.restrict_apply_univ] using hz)
  change (∫ x in U, q.toFun x) ≤ _
  have habsorb' : (∫ x in U, q.toFun x) ≤
      2 * ∫ x in U, |q.toFun x - integralAverage U q.toFun| := by
    simpa only [volumeOn, Measure.restrict_apply_univ, integralAverage] using habsorb
  calc
    (∫ x in U, q.toFun x) ≤
        2 * ∫ x in U, |q.toFun x - integralAverage U q.toFun| := habsorb'
    _ ≤ 2 * ((2 : ℝ) ^ d * (2 * s) *
        ∫ x in U, vecEuclideanNorm (q.grad x)) := mul_le_mul_of_nonneg_left hp' (by norm_num)
    _ = _ := by rw [pow_add]; norm_num; ring

open SuperdiffusionCLT.Section7

/-- Energy-adapted Young estimate for an anisotropic elliptic matrix. -/
theorem elliptic_cutoff_cross_bound {d : ℕ} {lam Lam η v : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ ζ : Vec d) :
    |2 * η * v * vecDot (matVecMul A ξ) ζ| ≤
      (η ^ 2 * vecDot ξ (matVecMul A ξ)) / 2 +
        2 * Lam * v ^ 2 * vecNormSq ζ := by
  have hflux := vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA ξ
  have hdot := sq_vecDot_le_vecNormSq_mul_vecNormSq (matVecMul A ξ) ζ
  have hE : 0 ≤ vecDot ξ (matVecMul A ξ) :=
    (mul_nonneg hA.lam_pos.le (vecNormSq_nonneg ξ)).trans (hA.coercive ξ)
  have hfac : 0 ≤ 4 * η ^ 2 * v ^ 2 := by positivity
  have hsq : (2 * η * v * vecDot (matVecMul A ξ) ζ) ^ 2 ≤
      (η ^ 2 * vecDot ξ (matVecMul A ξ)) * (4 * Lam * v ^ 2 * vecNormSq ζ) := by
    calc
      _ = (4 * η ^ 2 * v ^ 2) * vecDot (matVecMul A ξ) ζ ^ 2 := by ring
      _ ≤ (4 * η ^ 2 * v ^ 2) *
          (vecNormSq (matVecMul A ξ) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left hdot hfac
      _ ≤ (4 * η ^ 2 * v ^ 2) *
          ((Lam * vecDot ξ (matVecMul A ξ)) * vecNormSq ζ) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hflux (vecNormSq_nonneg ζ)) hfac
      _ = _ := by ring
  have hyoung := abs_le_add_halves_of_sq_le_mul hsq
    (mul_nonneg (sq_nonneg η) hE)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hA.Lam_pos.le)
      (sq_nonneg v)) (vecNormSq_nonneg ζ))
  linarith only [hyoung]

/-- Pointwise coercivity for the actual level-test gradient. No boundary
regularity or weak equation is used in this algebraic estimate. -/
theorem level_test_energy_bound {d : ℕ} {U : Set (Vec d)} {lam Lam : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix lam Lam A) (u : Homogenization.H1Function U)
    (k : ℝ) (η : Vec d → ℝ) (x : Vec d) :
    (lam / 2) * (η x ^ 2 * vecNormSq (posPartGrad u k x)) ≤
      vecDot (matVecMul A (u.grad x)) (levelTest u k η x) +
        2 * Lam * (max (u.toFun x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η x)) := by
  classical
  by_cases hx : k < u.toFun x
  · have hmem : x ∈ {y | k < u.toFun y} := hx
    have hcross := elliptic_cutoff_cross_bound
      (η := η x) (v := max (u.toFun x - k) 0) hA (u.grad x)
      (classicalGradient η x)
    have hcoer := mul_le_mul_of_nonneg_left (hA.coercive (u.grad x)) (sq_nonneg (η x))
    change (lam / 2) * (η x ^ 2 * vecNormSq (posPartGrad u k x)) ≤
      Homogenization.vecDot (matVecMul A (u.grad x)) (levelTest u k η x) +
        2 * Lam * (max (u.toFun x - k) 0 ^ 2 * vecNormSq (classicalGradient η x))
    simp only [posPartGrad, levelTest, Set.indicator_of_mem hmem,
      Homogenization.vecDot_add_right, Homogenization.vecDot_smul_right]
    change _ ≤ η x ^ 2 * vecDot (matVecMul A (u.grad x)) (u.grad x) +
      (2 * max (u.toFun x - k) 0 * η x) *
        vecDot (matVecMul A (u.grad x)) (classicalGradient η x) + _
    rw [vecDot_comm (matVecMul A (u.grad x)) (u.grad x)]
    have hneg := neg_abs_le (2 * η x * max (u.toFun x - k) 0 *
      vecDot (matVecMul A (u.grad x)) (classicalGradient η x))
    nlinarith only [hcross, hcoer, hneg]
  · have hmem : x ∉ {y | k < u.toFun y} := hx
    have hv : max (u.toFun x - k) 0 = 0 := max_eq_right (by linarith only [not_lt.mp hx])
    simp only [posPartGrad, levelTest, Set.indicator_of_notMem hmem, hv,
      zero_mul, zero_smul, add_zero,
      zero_pow (by decide : 2 ≠ 0), mul_zero]
    simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]

/-- Forced boundary level energy on the original open domain. The cutoff
need not be supported inside the domain: the nonnegative level makes its
product with the positive part a legal `H¹₀(U)` test. The forcing integral
is retained with its actual absolute value. -/
theorem forced_boundary_level_caccioppoli {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) {κ : ℝ}
    (hκ : 0 < κ) {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (w : Homogenization.H10Function U) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict U))
    {F : ℝ} (hfF : ∀ᵐ x ∂(volume.restrict U), |f x| ≤ F)
    (hw : IsWeakSolutionOn A U w.toH1Function f (fun _ => 0))
    {k : ℝ} (hk : 0 ≤ k) {I O : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) :
    (∫ x in U, η.toFun x ^ 2 *
      vecNormSq ({y | k < w.toH1Function.toFun y}.indicator
        w.toH1Function.grad x)) ≤
      2 * κ⁻¹ * (∫ x in U, |f x| * η.toFun x ^ 2 *
        max (w.toH1Function.toFun x - k) 0) +
      4 * κ⁻¹ ^ 2 * (∫ x in U,
        max (w.toH1Function.toFun x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) := by
  classical
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let u := w.toH1Function
  let v : Vec d → ℝ := fun x => max (u.toFun x - k) 0
  let E : Vec d → ℝ := fun x => η.toFun x ^ 2 * vecNormSq (posPartGrad u k x)
  let D : Vec d → ℝ := fun x => v x ^ 2 * vecNormSq (classicalGradient η.toFun x)
  obtain ⟨φ, hφf, hφg⟩ := exists_levelTest_h10 hU hfin w hk η.smooth η.hasCompactSupport
  have hηtop : MemLpOn U ⊤ η.toFun :=
    DGNM.memLpOn_top_of_contDiff η.smooth η.hasCompactSupport
  have hv : MemL2On U v := memL2On_positivePart_of_nonneg u hk
  have hEvec : MemVectorL2On U (fun x => η.toFun x • posPartGrad u k x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (posPartGrad_gradMemL2 u k i).fun_mul hηtop
  have hEint : IntegrableOn E U := by
    simpa only [E, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hEvec
  have hDvec : MemVectorL2On U (fun x => v x • classicalGradient η.toFun x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using hv.fun_mul
      (DGNM.memLpOn_top_classicalGradient η.smooth η.hasCompactSupport i)
  have hDint : IntegrableOn D U := by
    simpa only [D, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hDvec
  have hflux := integrableOn_vecDot_of_memVectorL2On
    (memVectorL2On_matVecMul_of_isEllipticFieldOn hA u.gradMemL2)
    φ.toH1Function.gradMemL2
  have hφint : IntegrableOn φ.toH1Function.toFun U :=
    φ.toH1Function.memL2.integrable (by norm_num)
  have hforce := hφint.bdd_mul hf (by simpa only [Real.norm_eq_abs] using hfF)
  have habsforce := hφint.bdd_mul (show AEStronglyMeasurable (fun x => |f x|) (volumeOn U) from
    by simpa only [Real.norm_eq_abs] using hf.norm)
    (by simpa only [Real.norm_eq_abs, abs_abs] using hfF)
  have hpoint : ∀ᵐ x ∂volumeOn U,
      (κ / 2) * E x ≤
        vecDot (matVecMul (A x) (u.grad x)) (φ.toH1Function.grad x) + 2 * κ⁻¹ * D x := by
    filter_upwards [ae_restrict_mem hU.measurableSet, hφg] with x hx hgrad
    rw [hgrad]
    exact level_test_energy_bound (hA.elliptic hx) u k η.toFun x
  have hbound := integral_mono_ae (hEint.const_mul (κ / 2))
    (hflux.add (hDint.const_mul (2 * κ⁻¹))) hpoint
  dsimp only [Pi.add_apply] at hbound
  rw [integral_add hflux (hDint.const_mul (2 * κ⁻¹)),
    integral_const_mul, integral_const_mul] at hbound
  have hweak := hw φ
  simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at hweak
  change (∫ x in U, vecDot (matVecMul (A x) (u.grad x))
    (φ.toH1Function.grad x)) = (∫ x in U, f x * φ.toH1Function.toFun x) at hweak
  rw [hweak] at hbound
  have hforce_le : (∫ x in U, f x * φ.toH1Function.toFun x) ≤
      ∫ x in U, |f x| * η.toFun x ^ 2 * v x := by
    have hle := integral_mono_ae hforce habsforce
      (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (le_abs_self (f x))
        (by rw [hφf]; exact mul_nonneg (sq_nonneg _) (le_max_right _ _)))
    simpa only [hφf, mul_assoc, v, u] using hle
  have hfinal : (∫ x in U, E x) ≤
      2 * κ⁻¹ * (∫ x in U, |f x| * η.toFun x ^ 2 * v x) +
        4 * κ⁻¹ ^ 2 * (∫ x in U, D x) := by
    apply (mul_le_mul_iff_right₀ (show 0 < κ / 2 by positivity)).mp
    calc
      _ ≤ (∫ x in U, f x * φ.toH1Function.toFun x) +
          2 * κ⁻¹ * (∫ x in U, D x) := hbound
      _ ≤ (∫ x in U, |f x| * η.toFun x ^ 2 * v x) +
          2 * κ⁻¹ * (∫ x in U, D x) := add_le_add hforce_le le_rfl
      _ = _ := by field_simp [hκ.ne']; ring
  exact hfinal

/-- Transport between the two installed representative Sobolev interfaces,
preserving both the value and the weak gradient. -/
def h1FromHomogenization {d : ℕ} {U : Set (Vec d)}
    (q : Homogenization.H1Function U) : H1Function U where
  toFun := q.toFun
  grad := q.grad
  memL2 := q.memL2
  gradMemL2 := q.gradMemL2
  hasWeakGradient := q.hasWeakGradient

/-- The positive part of the genuine zero extension has the half-zero
Poincaré bound in every ball centred on the original ball's boundary.
Its gradient is the truncated original gradient extended by zero. -/
theorem zero_extended_level_l1_poincare {d : ℕ} (c z : Vec d) (R : ℝ)
    {s : ℝ} (hs : 0 < s) (hz : z ∈ frontier (euclideanBall c R))
    (w : Homogenization.H10Function (euclideanBall c R)) {k : ℝ} (hk : 0 ≤ k) :
    (∫ x in euclideanBall z s,
      max ((euclideanBall c R).indicator w.toH1Function.toFun x - k) 0) ≤
      (2 : ℝ) ^ (d + 2) * s *
        ∫ x in euclideanBall z s, vecEuclideanNorm
          ({y | k < (euclideanBall c R).indicator w.toH1Function.toFun y}.indicator
            ((euclideanBall c R).indicator w.toH1Function.grad) x) := by
  classical
  let B := euclideanBall c R
  let V := euclideanBall z s
  have hB : IsOpen B := isOpen_euclideanBall c R
  have hV : IsOpen V := isOpen_euclideanBall z s
  let W := zeroExtCube hB hV w
  let q := positivePartOpen hV W k (memL2On_positivePart_of_nonneg W hk)
  have hzero : V \ B ⊆ {x | q.toFun x = 0} := by
    intro x hx
    change max (B.indicator w.toH1Function.toFun x - k) 0 = 0
    rw [Set.indicator_of_notMem hx.2, zero_sub, max_eq_right (neg_nonpos.mpr hk)]
  have hext : volume (V \ B) = (volume.restrict V) (V \ B) := by
    rw [Measure.restrict_apply (hV.measurableSet.diff hB.measurableSet),
      Set.inter_eq_left.mpr Set.sdiff_subset]
  have hhalf : volume V ≤ 2 * (volume.restrict V) {x | q.toFun x = 0} := calc
    volume V ≤ 2 * volume (V \ B) := ball_exterior_half_volume c z R s hz
    _ = 2 * (volume.restrict V) (V \ B) := by rw [hext]
    _ ≤ _ := mul_le_mul_of_nonneg_left (measure_mono hzero) (by norm_num)
  exact half_zero_ball_l1_poincare z hs (h1FromHomogenization q)
    (Filter.Eventually.of_forall fun x => le_max_right _ _) hhalf

/-- The clipped two-level strip, using the actual Sobolev gradient. -/
noncomputable def levelStrip {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : Homogenization.H1Function U) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Homogenization.H1Function U :=
  positivePartOpen hU u a (memL2On_positivePart_of_nonneg u ha) -
    positivePartOpen hU u b (memL2On_positivePart_of_nonneg u hb)

/-- Subtracting the strict truncation gradients retains the upper endpoint. -/
theorem levelStrip_grad {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : Homogenization.H1Function U) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (levelStrip hU u ha (ha.trans hab)).grad =
      {x | a < u.toFun x ∧ u.toFun x ≤ b}.indicator u.grad := by
  classical
  rw [levelStrip, Homogenization.H1Function.sub_grad]
  funext x
  change {y | a < u.toFun y}.indicator u.grad x -
    {y | b < u.toFun y}.indicator u.grad x = _
  by_cases hax : a < u.toFun x
  · by_cases hbx : b < u.toFun x
    · simp only [Set.mem_ofPred_eq, hax, hbx, not_le.mpr hbx, and_false,
        Set.indicator_of_mem, Set.indicator_of_notMem, sub_self, not_false_eq_true]
    · simp only [Set.mem_ofPred_eq, hax, hbx, le_of_not_gt hbx, and_self,
        Set.indicator_of_mem, Set.indicator_of_notMem, sub_zero, not_false_eq_true]
  · have hbx : ¬ b < u.toFun x := fun h => hax (hab.trans_lt h)
    simp only [Set.mem_ofPred_eq, hax, hbx, false_and,
      Set.indicator_of_notMem, sub_self, not_false_eq_true]

/-- Cauchy--Schwarz in the real integral form used by the strip estimate. -/
theorem integral_sq_le_mass_mul_integral_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : MemLp g 2 μ) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x) :
    (∫ x, g x ∂μ) ^ 2 ≤ (μ Set.univ).toReal * ∫ x, g x ^ 2 ∂μ := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by constructor <;> norm_num)
    hgn (Filter.Eventually.of_forall fun _ => zero_le_one)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) μ from by simpa using hg)
    (memLp_const (1 : ℝ))
  simp only [mul_one, Real.rpow_two, one_pow, integral_const, smul_eq_mul,
    mul_one, ← Real.sqrt_eq_rpow] at hholder
  have hsq := mul_self_le_mul_self (integral_nonneg_of_ae hgn) hholder
  have hmul (x y : ℝ) : x * y * (x * y) = x ^ 2 * y ^ 2 := by ring
  rw [← pow_two, hmul, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
    Real.sq_sqrt (measureReal_nonneg (μ := μ) (s := Set.univ)), mul_comm] at hsq
  exact hsq

/-- One finite level strip on a half-zero ball. The energy is that of the
lower truncation, and the strip includes its upper endpoint. -/
theorem half_zero_ball_level_strip_sq {d : ℕ} (z : Vec d) {s : ℝ} (hs : 0 < s)
    (u : Homogenization.H1Function (euclideanBall z s))
    (hhalf : volume (euclideanBall z s) ≤
      2 * (volume.restrict (euclideanBall z s)) {x | u.toFun x = 0})
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) ^ 2 * ((volume.restrict (euclideanBall z s)) {x | b < u.toFun x}).toReal ^ 2 ≤
      ((2 : ℝ) ^ (d + 2) * s) ^ 2 *
        (∫ x in euclideanBall z s, vecNormSq (posPartGrad u a x)) *
        ((volume.restrict (euclideanBall z s))
          {x | a < u.toFun x ∧ u.toFun x ≤ b}).toReal := by
  classical
  let V := euclideanBall z s
  let μ := volume.restrict V
  let S := {x | a < u.toFun x ∧ u.toFun x ≤ b}
  let T := {x | b < u.toFun x}
  let : IsFiniteMeasure μ := isFiniteMeasure_volumeOn_euclideanBall z hs.le
  let q := levelStrip (isOpen_euclideanBall z s) u ha (ha.trans hab)
  have hqf (x : Vec d) : q.toFun x =
      max (u.toFun x - a) 0 - max (u.toFun x - b) 0 := by
    simp only [q, levelStrip, Homogenization.H1Function.sub_toFun]
    rfl
  have hqn (x : Vec d) : 0 ≤ q.toFun x := by
    rw [hqf]
    exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)
  have hqzero : {x | u.toFun x = 0} ⊆ {x | q.toFun x = 0} := by
    intro x hx
    rw [Set.mem_ofPred_eq, hqf, hx, zero_sub, zero_sub,
      max_eq_right (neg_nonpos.mpr ha), max_eq_right (neg_nonpos.mpr (ha.trans hab)), sub_self]
  have hqhalf : volume V ≤ 2 * μ {x | q.toFun x = 0} :=
    hhalf.trans (mul_le_mul_right (measure_mono hqzero) 2)
  have hp := half_zero_ball_l1_poincare z hs (h1FromHomogenization q)
    (Filter.Eventually.of_forall hqn) hqhalf
  have hT : NullMeasurableSet T μ := nullMeasurableSet_lt
    aemeasurable_const u.memL2.aemeasurable
  have hS : NullMeasurableSet S μ := (nullMeasurableSet_lt
    aemeasurable_const u.memL2.aemeasurable).inter
      (nullMeasurableSet_le u.memL2.aemeasurable aemeasurable_const)
  have hqint : Integrable q.toFun μ := q.memL2.integrable (by norm_num)
  have hmass : (b - a) * (μ T).toReal ≤ ∫ x, q.toFun x ∂μ := by
    have hle : (∫ x in T, b - a ∂μ) ≤ ∫ x in T, q.toFun x ∂μ := by
      apply setIntegral_mono_on₀ (integrable_const _).integrableOn hqint.integrableOn hT
      intro x hx
      have hxb : b < u.toFun x := hx
      rw [hqf, max_eq_left (by linarith), max_eq_left (by linarith)]
      linarith
    calc
      _ = ∫ x in T, b - a ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]; rfl
      _ ≤ ∫ x in T, q.toFun x ∂μ := hle
      _ ≤ ∫ x, q.toFun x ∂μ := setIntegral_le_integral hqint
        (Filter.Eventually.of_forall hqn)
  have hg : MemLp (fun x => vecEuclideanNorm (posPartGrad u a x)) 2 μ :=
    (h1FromHomogenization
      (positivePartOpen (isOpen_euclideanBall z s) u a
        (memL2On_positivePart_of_nonneg u ha))).gradMemL2.memLp_vecEuclideanNorm
  have hgrad (x : Vec d) : vecEuclideanNorm (q.grad x) =
      S.indicator (fun y => vecEuclideanNorm (posPartGrad u a y)) x := by
    rw [show q.grad = S.indicator u.grad from levelStrip_grad _ u ha hab]
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact congrArg vecEuclideanNorm (Set.indicator_of_mem (show x ∈ {y | a < u.toFun y} from hx.1) u.grad).symm
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      exact vecEuclideanNorm_eq_zero_iff.mpr rfl
  have hid : (∫ x, vecEuclideanNorm (q.grad x) ∂μ) =
      ∫ x in S, vecEuclideanNorm (posPartGrad u a x) ∂μ := by
    simp_rw [hgrad]
    exact integral_indicator₀ hS
  have hcs := integral_sq_le_mass_mul_integral_sq (μ.restrict S)
    (hg.restrict S) (Filter.Eventually.of_forall fun x => vecEuclideanNorm_nonneg _)
  rw [Measure.restrict_apply_univ] at hcs
  have henergy : (∫ x in S, vecEuclideanNorm (posPartGrad u a x) ^ 2 ∂μ) ≤
      ∫ x, vecNormSq (posPartGrad u a x) ∂μ := by
    simp_rw [vecEuclideanNorm_sq]
    exact setIntegral_le_integral
      (by simpa only [vecEuclideanNorm_sq] using hg.integrable_sq)
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
  have hbound : (b - a) * (μ T).toReal ≤
      ((2 : ℝ) ^ (d + 2) * s) *
        ∫ x in S, vecEuclideanNorm (posPartGrad u a x) ∂μ := by
    have hp' : (∫ x, q.toFun x ∂μ) ≤
        ((2 : ℝ) ^ (d + 2) * s) * ∫ x, vecEuclideanNorm (q.grad x) ∂μ := hp
    rw [hid] at hp'
    exact hmass.trans hp'
  have hsq := mul_self_le_mul_self
    (mul_nonneg (sub_nonneg.mpr hab) ENNReal.toReal_nonneg) hbound
  have hcs' := hcs.trans (mul_le_mul_of_nonneg_left henergy ENNReal.toReal_nonneg)
  have hfinal := hsq.trans
    (by simpa only [← pow_two, mul_pow] using
      mul_le_mul_of_nonneg_left hcs' (sq_nonneg ((2 : ℝ) ^ (d + 2) * s)))
  convert hfinal using 1 <;> ring

/-- Finite disjoint-strip summation. A common bound on lower-level energy
relative to the squared level gap gives an explicit `1/N` squared-measure
bound; no infinite iteration or boundedness of `u` is assumed. -/
theorem half_zero_ball_finite_level_decay {d : ℕ} (z : Vec d) {s : ℝ} (hs : 0 < s)
    (u : Homogenization.H1Function (euclideanBall z s))
    (hhalf : volume (euclideanBall z s) ≤
      2 * (volume.restrict (euclideanBall z s)) {x | u.toFun x = 0})
    (N : ℕ) (k : ℕ → ℝ) (hk : StrictMono k) (hk0 : 0 ≤ k 0)
    {E : ℝ} (hE : 0 ≤ E)
    (henergy : ∀ j < N, (∫ x in euclideanBall z s,
      vecNormSq (posPartGrad u (k j) x)) ≤ E * (k (j + 1) - k j) ^ 2) :
    (N : ℝ) * ((volume.restrict (euclideanBall z s)) {x | k N < u.toFun x}).toReal ^ 2 ≤
      ((2 : ℝ) ^ (d + 2) * s) ^ 2 * E * (volume (euclideanBall z s)).toReal := by
  classical
  let μ := volume.restrict (euclideanBall z s)
  let S : ℕ → Set (Vec d) := fun j => {x | k j < u.toFun x ∧ u.toFun x ≤ k (j + 1)}
  let A : ℕ → Set (Vec d) := fun j => {x | k j < u.toFun x}
  let C := ((2 : ℝ) ^ (d + 2) * s) ^ 2 * E
  let : IsFiniteMeasure μ := isFiniteMeasure_volumeOn_euclideanBall z hs.le
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) hE
  have hstep (j : ℕ) (hj : j < N) : (μ (A (j + 1))).toReal ^ 2 ≤ C * (μ (S j)).toReal := by
    have hgap : 0 < k (j + 1) - k j := sub_pos.mpr (hk (Nat.lt_succ_self j))
    have h := half_zero_ball_level_strip_sq z hs u hhalf
      (hk0.trans (hk.monotone (Nat.zero_le j))) (hk.monotone (Nat.le_succ j))
    have h' := h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (henergy j hj) (sq_nonneg _)) ENNReal.toReal_nonneg)
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hgap)).mp
    convert h' using 1 <;> dsimp only [C, A, S, μ] <;> ring
  have hdisjoint : Set.PairwiseDisjoint (↑(Finset.range N)) S := by
    intro i _ j _ hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    rcases lt_or_gt_of_ne hij with h | h
    · have hle := hk.monotone (Nat.succ_le_of_lt h)
      have hi : u.toFun x ≤ k (i + 1) := hxi.2
      have hj : k j < u.toFun x := hxj.1
      linarith
    · have hle := hk.monotone (Nat.succ_le_of_lt h)
      have hj : u.toFun x ≤ k (j + 1) := hxj.2
      have hi : k i < u.toFun x := hxi.1
      linarith
  have hS (j : ℕ) : NullMeasurableSet (S j) μ :=
    (nullMeasurableSet_lt aemeasurable_const u.memL2.aemeasurable).inter
      (nullMeasurableSet_le u.memL2.aemeasurable aemeasurable_const)
  have hsum : (∑ j ∈ Finset.range N, (μ (S j)).toReal) ≤ (μ Set.univ).toReal := by
    rw [← ENNReal.toReal_sum (fun j _ => measure_ne_top μ (S j))]
    exact ENNReal.toReal_mono (measure_ne_top μ _)
      (sum_measure_le_measure_univ (fun j _ => hS j) hdisjoint.aedisjoint)
  have hnest (j : ℕ) (hj : j < N) : (μ (A N)).toReal ^ 2 ≤ (μ (A (j + 1))).toReal ^ 2 := by
    apply pow_le_pow_left₀ ENNReal.toReal_nonneg
    exact measureReal_mono (fun x hx => (hk.monotone (Nat.succ_le_of_lt hj)).trans_lt hx)
  calc
    _ = ∑ _j ∈ Finset.range N, (μ (A N)).toReal ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rfl
    _ ≤ ∑ j ∈ Finset.range N, C * (μ (S j)).toReal :=
      Finset.sum_le_sum fun j hj => (hnest j (Finset.mem_range.mp hj)).trans
        (hstep j (Finset.mem_range.mp hj))
    _ = C * ∑ j ∈ Finset.range N, (μ (S j)).toReal := (Finset.mul_sum _ _ _).symm
    _ ≤ C * (μ Set.univ).toReal := mul_le_mul_of_nonneg_left hsum hC
    _ = _ := by rw [show μ Set.univ = volume (euclideanBall z s) from
        Measure.restrict_apply_univ _]

/-- The finite-strip estimate for the genuine zero extension at a boundary
point. The energy hypothesis is local lower-truncation energy, to be supplied
by `forced_boundary_level_caccioppoli` on the original domain. -/
theorem zero_extended_finite_level_decay {d : ℕ} (c z : Vec d) (R : ℝ)
    {s : ℝ} (hs : 0 < s) (hz : z ∈ frontier (euclideanBall c R))
    (w : Homogenization.H10Function (euclideanBall c R))
    (N : ℕ) (k : ℕ → ℝ) (hk : StrictMono k) (hk0 : 0 ≤ k 0)
    {E : ℝ} (hE : 0 ≤ E)
    (henergy : ∀ j < N, (∫ x in euclideanBall z s,
      vecNormSq ({y | k j < (euclideanBall c R).indicator w.toH1Function.toFun y}.indicator
        ((euclideanBall c R).indicator w.toH1Function.grad) x)) ≤
          E * (k (j + 1) - k j) ^ 2) :
    (N : ℝ) * ((volume.restrict (euclideanBall z s))
      {x | k N < (euclideanBall c R).indicator w.toH1Function.toFun x}).toReal ^ 2 ≤
      ((2 : ℝ) ^ (d + 2) * s) ^ 2 * E * (volume (euclideanBall z s)).toReal := by
  let B := euclideanBall c R
  let V := euclideanBall z s
  let W := zeroExtCube (isOpen_euclideanBall c R) (isOpen_euclideanBall z s) w
  have hzero : V \ B ⊆ {x | W.toFun x = 0} := by
    intro x hx
    exact Set.indicator_of_notMem hx.2 _
  have hext : volume (V \ B) = (volume.restrict V) (V \ B) := by
    rw [Measure.restrict_apply ((isOpen_euclideanBall z s).measurableSet.diff
      (isOpen_euclideanBall c R).measurableSet), Set.inter_eq_left.mpr Set.sdiff_subset]
  have hhalf : volume V ≤ 2 * (volume.restrict V) {x | W.toFun x = 0} := calc
    _ ≤ 2 * volume (V \ B) := ball_exterior_half_volume c z R s hz
    _ = 2 * (volume.restrict V) (V \ B) := by rw [hext]
    _ ≤ _ := mul_le_mul_right (measure_mono hzero) 2
  exact half_zero_ball_finite_level_decay z hs W hhalf N k hk hk0 hE henergy

/-- Local energy of the genuine zero extension, obtained solely by testing
the forced equation on its original domain. The cutoff is one on `V`. -/
theorem forced_zero_extended_level_energy {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hfin : volume U ≠ ⊤) {κ : ℝ}
    (hκ : 0 < κ) {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (w : Homogenization.H10Function U) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict U))
    {F : ℝ} (hfF : ∀ᵐ x ∂(volume.restrict U), |f x| ≤ F)
    (hw : IsWeakSolutionOn A U w.toH1Function f (fun _ => 0))
    {k : ℝ} (hk : 0 ≤ k) {O : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff V O K) :
    (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) ≤
      2 * κ⁻¹ * (∫ x in U, |f x| * η.toFun x ^ 2 *
        max (w.toH1Function.toFun x - k) 0) +
      4 * κ⁻¹ ^ 2 * (∫ x in U,
        max (w.toH1Function.toFun x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) := by
  classical
  let u := w.toH1Function
  let e := fun x => vecNormSq (posPartGrad u k x)
  let eη := fun x => η.toFun x ^ 2 * e x
  have hηtop : MemLpOn U ⊤ η.toFun :=
    DGNM.memLpOn_top_of_contDiff η.smooth η.hasCompactSupport
  have hEvec : MemVectorL2On U (fun x => η.toFun x • posPartGrad u k x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (posPartGrad_gradMemL2 u k i).fun_mul hηtop
  have hEint : IntegrableOn eη U := by
    simpa only [eη, e, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hEvec
  have hlocal : (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) =
      ∫ x in V, U.indicator eη x := by
    apply setIntegral_congr_fun hV.measurableSet
    intro x hx
    change vecNormSq ({y | k < U.indicator u.toFun y}.indicator
      (U.indicator u.grad) x) = U.indicator eη x
    by_cases hxU : x ∈ U <;>
      simp [Set.indicator_apply, Set.mem_ofPred_eq, hxU, eη, e, posPartGrad,
        η.eq_one_on_inner x hx, vecNormSq, vecDot]
  calc
    _ = ∫ x in V, U.indicator eη x := hlocal
    _ = ∫ x in U, V.indicator eη x := by
      rw [integral_indicator hU.measurableSet, integral_indicator hV.measurableSet,
        Measure.restrict_restrict hU.measurableSet,
        Measure.restrict_restrict hV.measurableSet, Set.inter_comm]
    _ = ∫ x in V, eη x ∂(volume.restrict U) := integral_indicator hV.measurableSet
    _ ≤ ∫ x in U, eη x := setIntegral_le_integral hEint
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
    _ ≤ _ := forced_boundary_level_caccioppoli hU hfin hκ hA w f hf hfF hw hk η

/-- A local amplitude bound on the cutoff support gives a quantitative
forced energy estimate. The volume is only that of `U ∩ O`, and the forcing
contribution is retained explicitly. -/
theorem forced_zero_extended_level_energy_bounded {d : ℕ} {U V O : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hO : MeasurableSet O)
    (hfin : volume U ≠ ⊤) {κ : ℝ} (hκ : 0 < κ)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (w : Homogenization.H10Function U) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict U))
    {F : ℝ} (hF : 0 ≤ F) (hfF : ∀ᵐ x ∂(volume.restrict U), |f x| ≤ F)
    (hw : IsWeakSolutionOn A U w.toH1Function f (fun _ => 0))
    {k a K : ℝ} (hk : 0 ≤ k)
    (η : QuantitativeSmoothCutoff V O K)
    (hbound : ∀ᵐ x ∂(volume.restrict U), x ∈ O →
      max (w.toH1Function.toFun x - k) 0 ≤ a) :
    (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) ≤
      (2 * κ⁻¹ * F * a + 4 * κ⁻¹ ^ 2 * a ^ 2 * K ^ 2) *
        ((volume.restrict U) O).toReal := by
  classical
  let μ := volume.restrict U
  let v := fun x => max (w.toH1Function.toFun x - k) 0
  let : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using hfin.lt_top⟩
  have hforce : (∫ x, |f x| * η.toFun x ^ 2 * v x ∂μ) ≤
      F * a * (μ O).toReal := by
    have hle := integral_mono_of_nonneg (μ := μ)
      (f := fun x => |f x| * η.toFun x ^ 2 * v x)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (le_max_right _ _))
      ((integrable_const (F * a)).indicator hO) ?_
    · simpa only [integral_indicator hO, setIntegral_const, smul_eq_mul, measureReal_def, mul_comm] using hle
    · filter_upwards [hfF, hbound] with x hfx hbx
      by_cases hx : x ∈ O
      · rw [Set.indicator_of_mem hx]
        have hη : η.toFun x ^ 2 ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (η.nonneg x) (η.le_one x) 2
        have hmul := mul_le_mul (mul_le_mul hfx hη (sq_nonneg _) hF)
          (hbx hx) (le_max_right _ _) (mul_nonneg hF zero_le_one)
        simpa only [mul_one] using hmul
      · rw [Set.indicator_of_notMem hx, η.eq_zero_of_not_mem_outer hx,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]
  have hgrad : (∫ x, v x ^ 2 * vecNormSq (classicalGradient η.toFun x) ∂μ) ≤
      a ^ 2 * K ^ 2 * (μ O).toReal := by
    have hle := integral_mono_of_nonneg (μ := μ)
      (f := fun x => v x ^ 2 * vecNormSq (classicalGradient η.toFun x))
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
      ((integrable_const (a ^ 2 * K ^ 2)).indicator hO) ?_
    · simpa only [integral_indicator hO, setIntegral_const, smul_eq_mul, measureReal_def, mul_comm] using hle
    · filter_upwards [hbound] with x hbx
      by_cases hx : x ∈ O
      · rw [Set.indicator_of_mem hx]
        have hg : vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
          rw [← vecEuclideanNorm_sq]
          exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (η.gradient_bound x) 2
        exact mul_le_mul (pow_le_pow_left₀ (le_max_right _ _) (hbx hx) 2) hg
          (vecNormSq_nonneg _) (sq_nonneg a)
      · rw [Set.indicator_of_notMem hx, η.classicalGradient_eq_zero_of_not_mem_outer hx]
        simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]
  calc
    _ ≤ 2 * κ⁻¹ * (∫ x, |f x| * η.toFun x ^ 2 * v x ∂μ) +
        4 * κ⁻¹ ^ 2 * (∫ x, v x ^ 2 * vecNormSq (classicalGradient η.toFun x) ∂μ) :=
      forced_zero_extended_level_energy hU hV hfin hκ hA w f hf hfF hw hk η
    _ ≤ 2 * κ⁻¹ * (F * a * (μ O).toReal) +
        4 * κ⁻¹ ^ 2 * (a ^ 2 * K ^ 2 * (μ O).toReal) :=
      add_le_add (mul_le_mul_of_nonneg_left hforce (by positivity))
        (mul_le_mul_of_nonneg_left hgrad (by positivity))
    _ = _ := by ring

/-- Finite boundary superlevel decay at dyadic levels. The small-forcing
condition is used in the original-domain energy estimate at every level.
The local bound `H` is explicit; no boundedness follows from the `H¹` data alone. -/
theorem forced_zero_extended_dyadic_level_decay {d : ℕ}
    (c z : Vec d) (R : ℝ) (hR : 0 ≤ R) {r : ℝ} (hr : 0 < r)
    (hz : z ∈ frontier (euclideanBall c R)) {κ : ℝ} (hκ : 0 < κ)
    {K H : ℝ} (hH : 0 < H) (N : ℕ)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A)
    (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (euclideanBall c R)))
    {F : ℝ} (hF : 0 ≤ F)
    (hfF : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F)
    (hw : IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0))
    (η : QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) K)
    (hbound : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
      x ∈ euclideanBall z r → w.toH1Function.toFun x ≤ H)
    (hsmall : κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N) :
    (N : ℝ) * ((volume.restrict (euclideanBall z (r / 2)))
      {x | H - H / (2 : ℝ) ^ N <
        (euclideanBall c R).indicator w.toH1Function.toFun x}).toReal ^ 2 ≤
      ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
        (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
          ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
        (volume (euclideanBall z (r / 2))).toReal := by
  let a : ℕ → ℝ := fun j => H / (2 : ℝ) ^ j
  let k : ℕ → ℝ := fun j => H - a j
  let C : ℝ := 2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2
  let m : ℝ := ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal
  have ha (j : ℕ) : 0 < a j := div_pos hH (pow_pos (by norm_num) _)
  have hasucc (j : ℕ) : a (j + 1) = a j / 2 := by
    dsimp [a]
    rw [pow_succ, div_mul_eq_div_div]
  have hgap (j : ℕ) : k (j + 1) - k j = a j / 2 := by
    dsimp [k]
    rw [hasucc]
    ring
  have hk : StrictMono k := strictMono_nat_of_lt_succ fun j => by
    have := ha j
    have := hgap j
    linarith
  have hk0 : k 0 = 0 := by simp [k, a]
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : 0 ≤ m := ENNReal.toReal_nonneg
  have henergy (j : ℕ) (hj : j < N) :
      (∫ x in euclideanBall z (r / 2),
        vecNormSq ({y | k j < (euclideanBall c R).indicator w.toH1Function.toFun y}.indicator
          ((euclideanBall c R).indicator w.toH1Function.grad) x)) ≤
        (4 * C * m) * (k (j + 1) - k j) ^ 2 := by
    have haj : a N ≤ a j := div_le_div_of_nonneg_left hH.le
      (pow_pos (by norm_num) _) (pow_le_pow_right₀ (by norm_num) hj.le)
    have hforce : κ⁻¹ * F ≤ a j / r ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
      calc
        κ⁻¹ * F * r ^ 2 = κ⁻¹ * r ^ 2 * F := by ring
        _ ≤ a N := hsmall
        _ ≤ a j := haj
    have hbj : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → max (w.toH1Function.toFun x - k j) 0 ≤ a j := by
      filter_upwards [hbound] with x hx hxO
      apply max_le
      · dsimp [k]
        linarith [hx hxO]
      · exact (ha j).le
    have hkpos : 0 ≤ k j := by simpa only [hk0] using hk.monotone (Nat.zero_le j)
    have henergy := forced_zero_extended_level_energy_bounded
      (isOpen_euclideanBall c R) (isOpen_euclideanBall z (r / 2))
      (isOpen_euclideanBall z r).measurableSet (volume_euclideanBall_ne_top c hR)
      hκ hA w f hf hF hfF hw hkpos η hbj
    have hcoef : 2 * κ⁻¹ * F * a j + 4 * κ⁻¹ ^ 2 * a j ^ 2 * K ^ 2 ≤
        C * a j ^ 2 := calc
      _ = 2 * a j * (κ⁻¹ * F) + 4 * κ⁻¹ ^ 2 * a j ^ 2 * K ^ 2 := by ring
      _ ≤ 2 * a j * (a j / r ^ 2) + 4 * κ⁻¹ ^ 2 * a j ^ 2 * K ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hforce
          (show 0 ≤ 2 * a j from mul_nonneg (by norm_num) (ha j).le)) le_rfl
      _ = C * a j ^ 2 := by dsimp [C]; ring
    calc
      _ ≤ (2 * κ⁻¹ * F * a j + 4 * κ⁻¹ ^ 2 * a j ^ 2 * K ^ 2) * m := henergy
      _ ≤ (C * a j ^ 2) * m := mul_le_mul_of_nonneg_right hcoef hm
      _ = (4 * C * m) * (k (j + 1) - k j) ^ 2 := by rw [hgap]; ring
  exact zero_extended_finite_level_decay c z R (half_pos hr) hz w N k hk
    (by rw [hk0]) (by positivity) henergy

/-- Truncating at `k` and then testing at a nonnegative level `t` gives
exactly the original test at `k + t`, including its strict gradient indicator. -/
theorem positivePart_levelTest {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : Homogenization.H1Function U) (k : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - k) 0))
    {t : ℝ} (ht : 0 ≤ t) (η : Vec d → ℝ) (x : Vec d) :
    levelTest (positivePartOpen hU u k hmem) t η x =
      levelTest u (k + t) η x := by
  classical
  by_cases hx : k < u.toFun x
  · have hmax : max (u.toFun x - k) 0 = u.toFun x - k :=
      max_eq_left (sub_nonneg.mpr hx.le)
    have hiff : t < u.toFun x - k ↔ k + t < u.toFun x := by constructor <;> intro h <;> linarith
    simp only [levelTest, positivePartOpen, posPartGrad, Set.mem_ofPred_eq,
      Set.indicator_apply, hmax, hx, hiff, ↓reduceIte]
    rw [sub_sub]
  · have hmax : max (u.toFun x - k) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (not_lt.mp hx))
    have hxt : ¬ k + t < u.toFun x := by linarith [not_lt.mp hx]
    have hmax' : max (u.toFun x - (k + t)) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (not_lt.mp hxt))
    simp only [levelTest, positivePartOpen, posPartGrad, Set.mem_ofPred_eq,
      Set.indicator_apply, hmax, hmax', hx, hxt, not_lt.mpr ht,
      zero_sub, max_eq_right (neg_nonpos.mpr ht), ↓reduceIte,
      mul_zero, zero_mul, zero_smul, add_zero]

/-- The truncated gradient can replace the original gradient in its level
flux: the common test vanishes wherever the gradients differ. -/
theorem positivePart_level_flux {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (u : Homogenization.H1Function U) (k : ℝ)
    (hmem : MemL2On U (fun x => max (u.toFun x - k) 0))
    {t : ℝ} (ht : 0 ≤ t) (η : Vec d → ℝ) (a : Mat d) (x : Vec d) :
    Homogenization.vecDot (Homogenization.matVecMul a ((positivePartOpen hU u k hmem).grad x))
        (levelTest (positivePartOpen hU u k hmem) t η x) =
      Homogenization.vecDot (Homogenization.matVecMul a (u.grad x)) (levelTest u (k + t) η x) := by
  classical
  rw [positivePart_levelTest hU u k hmem ht]
  by_cases hx : k < u.toFun x
  · simp only [positivePartOpen, posPartGrad, Set.indicator_apply, Set.mem_ofPred_eq, hx, ↓reduceIte]
  · have hxt : ¬ k + t < u.toFun x := by linarith [not_lt.mp hx]
    have hmax : max (u.toFun x - (k + t)) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr (not_lt.mp hxt))
    simp only [levelTest, Set.indicator_apply, Set.mem_ofPred_eq, hxt, ↓reduceIte, hmax,
      mul_zero, zero_mul, zero_smul, add_zero, Homogenization.vecDot_zero_right]

/-- Shifted boundary identity for the positive part of the actual zero
extension. All tests come from the original `H¹₀(U)` equation. -/
theorem shifted_boundary_level_identity {d : ℕ} {U Q : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) (hQ : IsOpen Q)
    (w : Homogenization.H10Function U) (a : CoeffField d) (c : Mat d)
    (f : Vec d → ℝ)
    (hw : IsWeakSolutionOn a U w.toH1Function f (fun _ => 0))
    {k t : ℝ} (hk : 0 ≤ k) (ht : 0 ≤ t)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Q) :
    let W := zeroExtCube hU hQ w
    let v := positivePartOpen hQ W k (memL2On_positivePart_of_nonneg W hk)
    (∫ x in Q, Homogenization.vecDot (Homogenization.matVecMul (boundaryCoeff U c a x) (v.grad x))
        (levelTest v t η x)) =
      ∫ x in Q, U.indicator f x * (η x ^ 2 * max (v.toFun x - t) 0) := by
  dsimp only
  have hmax (x : Vec d) :
      max (max ((zeroExtCube hU hQ w).toFun x - k) 0 - t) 0 =
        max ((zeroExtCube hU hQ w).toFun x - (k + t)) 0 := by
    by_cases hx : k ≤ (zeroExtCube hU hQ w).toFun x
    · rw [max_eq_left (sub_nonneg.mpr hx), sub_sub]
    · have hinner : max ((zeroExtCube hU hQ w).toFun x - k) 0 = 0 :=
        max_eq_right (by linarith [not_le.mp hx])
      rw [hinner, zero_sub, max_eq_right (neg_nonpos.mpr ht),
        max_eq_right (by linarith [not_le.mp hx])]
  simp_rw [positivePart_level_flux hQ _ k _ ht]
  have hid := boundary_level_identity hU hfin hQ w a c f (fun _ => 0) hw
    (add_nonneg hk ht) hη hηc hηs
  have hg : U.indicator (fun _ : Vec d => (0 : Vec d)) = fun _ => 0 := by
    funext x
    by_cases hx : x ∈ U <;> simp [Set.indicator_apply, hx]
  simpa only [positivePartOpen, hmax, hg,
    Homogenization.vecDot_zero_left, integral_zero, add_zero] using hid

/-- Amplitude times square root of superlevel measure bounds the actual
`L²` norm. Null measurability suffices; no measurable representative is chosen. -/
theorem positivePart_eLpNorm_two_le {d : ℕ} {U : Set (Vec d)}
    (u : Homogenization.H1Function U) {k a : ℝ} (ha : 0 ≤ a)
    (hbound : ∀ᵐ x ∂(volume.restrict U), max (u.toFun x - k) 0 ≤ a) :
    eLpNorm (fun x => max (u.toFun x - k) 0) 2 (volume.restrict U) ≤
      ENNReal.ofReal a * ((volume.restrict U) {x | k < u.toFun x}) ^ (1 / 2 : ℝ) := by
  classical
  let T := {x | k < u.toFun x}
  have hT : NullMeasurableSet T (volume.restrict U) :=
    nullMeasurableSet_lt aemeasurable_const u.memL2.aemeasurable
  calc
    _ ≤ eLpNorm (T.indicator (fun _ => a)) 2 (volume.restrict U) := by
      apply eLpNorm_mono_ae
        ((u.memL2.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
          aestronglyMeasurable_const)
      filter_upwards [hbound] with x hx
      by_cases hxT : x ∈ T
      · rw [Set.indicator_of_mem hxT, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (le_max_right _ _), abs_of_nonneg ha]
        exact hx
      · rw [Set.indicator_of_notMem hxT]
        have hz : max (u.toFun x - k) 0 = 0 :=
          max_eq_right (sub_nonpos.mpr (not_lt.mp hxT))
        simpa only [Pi.sup_apply, Pi.sub_apply, hz, norm_zero, le_refl]
    _ = _ := by
      rw [eLpNorm_indicator_const hT (by norm_num) (by norm_num),
        ← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ha]
      norm_num
      rfl

/-- A finite level-decay estimate gives the fourth-root `L²` gain. The
division by `N` is legitimate only for a positive number of strips. -/
theorem positivePart_eLpNorm_two_le_of_level_decay {d : ℕ} {U : Set (Vec d)}
    (hfin : volume U ≠ ⊤) (u : Homogenization.H1Function U)
    {k a B : ℝ} (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N)
    (hbound : ∀ᵐ x ∂(volume.restrict U), max (u.toFun x - k) 0 ≤ a)
    (hdecay : (N : ℝ) * ((volume.restrict U) {x | k < u.toFun x}).toReal ^ 2 ≤ B) :
    eLpNorm (fun x => max (u.toFun x - k) 0) 2 (volume.restrict U) ≤
      ENNReal.ofReal (a * Real.sqrt (Real.sqrt (B / (N : ℝ)))) := by
  let : IsFiniteMeasure (volume.restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin.lt_top⟩
  let m := (volume.restrict U) {x | k < u.toFun x}
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hm : m.toReal ≤ Real.sqrt (B / (N : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    apply (le_div_iff₀ hNr).mpr
    simpa only [mul_comm] using hdecay
  have hmen : m ≤ ENNReal.ofReal (Real.sqrt (B / (N : ℝ))) := by
    calc
      m = ENNReal.ofReal m.toReal :=
        (ENNReal.ofReal_toReal (show m ≠ ⊤ from measure_ne_top _ _)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hm
  calc
    _ ≤ ENNReal.ofReal a * m ^ (1 / 2 : ℝ) :=
      positivePart_eLpNorm_two_le u ha hbound
    _ ≤ ENNReal.ofReal a *
        (ENNReal.ofReal (Real.sqrt (B / (N : ℝ)))) ^ (1 / 2 : ℝ) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num),
        ← Real.sqrt_eq_rpow, ENNReal.ofReal_mul ha]

/-- The installed De Giorgi estimate transported to a shifted positive part
of the actual zero extension. Its constant is chosen before the PDE data. -/
theorem shifted_boundary_deGiorgi_bound {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {lam Lam : ℝ}, 0 < lam → lam ≤ Lam →
    ∀ {U : Set (Vec d)} {a : CoeffField d} (hU : IsOpen U), volume U ≠ ⊤ →
      IsEllipticFieldOn lam Lam U a →
    ∀ (z : Vec d) {L : ℝ}, 0 < L →
    ∀ (w : Homogenization.H10Function U) (f : Vec d → ℝ),
      IsWeakSolutionOn a U w.toH1Function f (fun _ => 0) →
    ∀ {k : ℝ}, 0 ≤ k →
      eLpNorm (fun x => max ((zeroExtCube hU (Homogenization.isOpen_axisCube z L) w).toFun x - k) 0)
          ⊤ (volume.restrict (halfCube z L)) ≤
        ENNReal.ofReal (C * (Lam / lam) ^ deGiorgiPower d) *
          (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
              eLpNorm (fun x => max ((zeroExtCube hU (Homogenization.isOpen_axisCube z L) w).toFun x - k) 0)
                2 (volume.restrict (Homogenization.axisCube z L)) +
            ENNReal.ofReal (L ^ 2 / lam) *
              eLpNorm (U.indicator f) ⊤ (volume.restrict (Homogenization.axisCube z L))) := by
  obtain ⟨C, hC, hmain⟩ := deGiorgi_eLpNorm_bound hd
  refine ⟨C, hC, ?_⟩
  intro lam Lam hlam hlamLam U a hU hfin hEll z L hL w f hw k hk
  let Q := Homogenization.axisCube z L
  let hQ := Homogenization.isOpen_axisCube z L
  let W := zeroExtCube hU hQ w
  let v := positivePartOpen hQ W k (memL2On_positivePart_of_nonneg W hk)
  have hEll' := isEllipticFieldOn_boundaryCoeff hU.measurableSet hQ.measurableSet
    hlam hlamLam hEll
  have hlevel (t : ℝ) (ht : 0 ≤ t) {η : Vec d → ℝ}
      (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
      (hηs : tsupport η ⊆ Q) :
      (∫ x in Q, Homogenization.vecDot
        (Homogenization.matVecMul (boundaryCoeff U (Homogenization.scalarMatrix lam) a x) (v.grad x))
          (levelTest v t η x)) =
        (∫ x in Q, U.indicator f x * (η x ^ 2 * max (v.toFun x - t) 0)) +
          ∫ x in Q, Homogenization.vecDot (0 : Vec d) (levelTest v t η x) := by
    simpa only [Homogenization.vecDot_zero_left, integral_zero, add_zero] using
      shifted_boundary_level_identity hU hfin hQ w a (Homogenization.scalarMatrix lam) f hw hk ht hη hηc hηs
  have hbound := hmain z hL hEll' v (U.indicator f) (fun _ => 0)
    aestronglyMeasurable_const hlevel
  have hv (x : Vec d) : max (v.toFun x) 0 = max (W.toFun x - k) 0 :=
    max_eq_left (le_max_right _ _)
  have hg : (fun _ : Vec d => eucNorm (0 : Vec d)) = fun _ => (0 : ℝ) := by
    funext x
    simp [eucNorm, Homogenization.vecNormSq, Homogenization.vecDot]
  simpa only [hv, hg, eLpNorm_fun_zero, mul_zero, add_zero] using hbound

/-- The forced finite-strip estimate and the actual local amplitude give
`L²` smallness of the dyadically shifted zero extension on the inner ball. -/
theorem forced_zero_extended_dyadic_l2_smallness {d : ℕ}
    (c z : Vec d) (R : ℝ) (hR : 0 ≤ R) {r : ℝ} (hr : 0 < r)
    (hz : z ∈ frontier (euclideanBall c R)) {κ : ℝ} (hκ : 0 < κ)
    {K H : ℝ} (hH : 0 < H) {N : ℕ} (hN : 0 < N)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A)
    (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (euclideanBall c R)))
    {F : ℝ} (hF : 0 ≤ F)
    (hfF : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F)
    (hw : IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0))
    (η : QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) K)
    (hbound : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
      x ∈ euclideanBall z r → w.toH1Function.toFun x ≤ H)
    (hsmall : κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N) :
    let B := ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
      (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
      (volume (euclideanBall z (r / 2))).toReal
    eLpNorm (fun x => max ((euclideanBall c R).indicator w.toH1Function.toFun x -
        (H - H / (2 : ℝ) ^ N)) 0) 2 (volume.restrict (euclideanBall z (r / 2))) ≤
      ENNReal.ofReal (H / (2 : ℝ) ^ N * Real.sqrt (Real.sqrt (B / (N : ℝ)))) := by
  let U := euclideanBall c R
  let V := euclideanBall z (r / 2)
  let W := zeroExtCube (isOpen_euclideanBall c R) (isOpen_euclideanBall z (r / 2)) w
  have hVU : V ⊆ euclideanBall z r :=
    euclideanBall_mono (half_pos hr).le (by linarith)
  have hglobal : ∀ᵐ x ∂volume, x ∈ U →
      x ∈ euclideanBall z r → w.toH1Function.toFun x ≤ H :=
    (ae_restrict_iff' (isOpen_euclideanBall c R).measurableSet).mp hbound
  have hW : ∀ᵐ x ∂(volume.restrict V),
      max (W.toFun x - (H - H / (2 : ℝ) ^ N)) 0 ≤ H / (2 : ℝ) ^ N := by
    filter_upwards [ae_restrict_of_ae hglobal, ae_restrict_mem (isOpen_euclideanBall z (r / 2)).measurableSet]
      with x hx hxV
    have htop : W.toFun x ≤ H := by
      change U.indicator w.toH1Function.toFun x ≤ H
      by_cases hxU : x ∈ U
      · rw [Set.indicator_of_mem hxU]
        exact hx hxU (hVU hxV)
      · rw [Set.indicator_of_notMem hxU]
        exact hH.le
    exact max_le (by linarith only [htop]) (by positivity)
  have hdecay := forced_zero_extended_dyadic_level_decay c z R hR hr hz hκ hH N
    hA w f hf hF hfF hw η hbound hsmall
  exact positivePart_eLpNorm_two_le_of_level_decay
    (volume_euclideanBall_ne_top z (half_pos hr).le) W (by positivity) hN hW hdecay

/-- Transport of the finite-strip estimate to a strict one-sided boundary
contraction. The displayed scale inequality involves only geometry and
ellipticity; it is imposed before the coefficient field and PDE data. -/
theorem forced_zero_extended_dyadic_contraction {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c z : Vec d) (R : ℝ), 0 ≤ R →
    ∀ {r : ℝ}, 0 < r → z ∈ frontier (euclideanBall c R) →
    ∀ {κ : ℝ}, 0 < κ → κ ≤ κ⁻¹ →
    ∀ (K : ℝ) {N : ℕ}, 0 < N →
    ∀ (q : Vec d) {L : ℝ}, 0 < L → Homogenization.axisCube q L ⊆ euclideanBall z (r / 2) →
      (let B := ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
        (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
          ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
        (volume (euclideanBall z (r / 2))).toReal
       C * (κ⁻¹ / κ) ^ deGiorgiPower d *
         (L ^ (-(d : ℝ) / 2) * Real.sqrt (Real.sqrt (B / (N : ℝ))) +
           L ^ 2 / r ^ 2) ≤ 1 / 2) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ (η : QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) K)
      {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → w.toH1Function.toFun x ≤ H) →
      κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N →
      ∀ᵐ x ∂(volume.restrict (halfCube q L)),
        (euclideanBall c R).indicator w.toH1Function.toFun x ≤
          H - H / (2 * (2 : ℝ) ^ N) := by
  obtain ⟨C, hC, hDG⟩ := shifted_boundary_deGiorgi_bound hd
  refine ⟨C, hC, ?_⟩
  intro c z R hR r hr hz κ hκ hκLam K N hN q L hL hCube hscale A hA w f hf
    F hF hfF hw η H hH hbound hsmall
  let U := euclideanBall c R
  let Q := Homogenization.axisCube q L
  let W := zeroExtCube (isOpen_euclideanBall c R) (Homogenization.isOpen_axisCube q L) w
  let a := H / (2 : ℝ) ^ N
  let B := ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
    (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
      ((volume.restrict U) (euclideanBall z r)).toReal) *
    (volume (euclideanBall z (r / 2))).toReal
  let D := Real.sqrt (Real.sqrt (B / (N : ℝ)))
  let T := C * (κ⁻¹ / κ) ^ deGiorgiPower d
  let v := fun x => max (W.toFun x - (H - a)) 0
  have ha : 0 < a := by dsimp [a]; positivity
  have haH : a ≤ H := by
    apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) ^ N)).mpr
    exact le_mul_of_one_le_right hH.le (one_le_pow₀ (by norm_num))
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hscale' : T * (L ^ (-(d : ℝ) / 2) * D + L ^ 2 / r ^ 2) ≤ 1 / 2 := hscale
  have hL2 : eLpNorm v 2 (volume.restrict Q) ≤ ENNReal.ofReal (a * D) := by
    calc
      _ ≤ eLpNorm v 2 (volume.restrict (euclideanBall z (r / 2))) :=
        eLpNorm_mono_measure v (Measure.restrict_mono hCube le_rfl)
      _ ≤ _ := forced_zero_extended_dyadic_l2_smallness c z R hR hr hz hκ hH hN
        hA w f hf hF hfF hw η hbound hsmall
  have hfI : AEStronglyMeasurable (U.indicator f) volume :=
    (aestronglyMeasurable_indicator_iff (isOpen_euclideanBall c R).measurableSet).mpr hf
  have hfglobal : ∀ᵐ x ∂volume, x ∈ U → |f x| ≤ F :=
    (ae_restrict_iff' (isOpen_euclideanBall c R).measurableSet).mp hfF
  have hfnorm : eLpNorm (U.indicator f) ⊤ (volume.restrict Q) ≤ ENNReal.ofReal F := by
    rw [eLpNorm_exponent_top hfI.restrict]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [ae_restrict_of_ae hfglobal] with x hx
    by_cases hxU : x ∈ U
    · simpa only [Set.indicator_of_mem hxU, Real.norm_eq_abs] using hx hxU
    · simpa only [Set.indicator_of_notMem hxU, norm_zero] using hF
  have hforce : L ^ 2 / κ * F ≤ L ^ 2 / r ^ 2 * a := by
    calc
      _ = L ^ 2 / r ^ 2 * (κ⁻¹ * r ^ 2 * F) := by
        field_simp
        <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsmall (by positivity)
  have hreal : T * (L ^ (-(d : ℝ) / 2) * (a * D) + L ^ 2 / κ * F) ≤ a / 2 := by
    calc
      _ ≤ T * (L ^ (-(d : ℝ) / 2) * (a * D) + L ^ 2 / r ^ 2 * a) := by
        gcongr
      _ = a * (T * (L ^ (-(d : ℝ) / 2) * D + L ^ 2 / r ^ 2)) := by ring
      _ ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left hscale' ha.le
      _ = _ := by ring
  have hnorm : eLpNorm v ⊤ (volume.restrict (halfCube q L)) ≤ ENNReal.ofReal (a / 2) := by
    calc
      _ ≤ ENNReal.ofReal T * (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
          eLpNorm v 2 (volume.restrict Q) + ENNReal.ofReal (L ^ 2 / κ) *
          eLpNorm (U.indicator f) ⊤ (volume.restrict Q)) :=
        hDG hκ hκLam (isOpen_euclideanBall c R) (volume_euclideanBall_ne_top c hR)
          hA q hL w f hw (sub_nonneg.mpr haH)
      _ ≤ ENNReal.ofReal T * (ENNReal.ofReal (L ^ (-(d : ℝ) / 2)) *
          ENNReal.ofReal (a * D) + ENNReal.ofReal (L ^ 2 / κ) * ENNReal.ofReal F) := by
        gcongr
      _ = ENNReal.ofReal (T * (L ^ (-(d : ℝ) / 2) * (a * D) + L ^ 2 / κ * F)) := by
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ (-(d : ℝ) / 2)),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ L ^ 2 / κ),
          ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul hT]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hreal
  filter_upwards [ae_le_eLpNormEssSup (f := v) (μ := volume.restrict (halfCube q L))]
    with x hx
  have hxv : v x ≤ a / 2 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ a / 2)).mp
    calc
      ENNReal.ofReal (v x) = ‖v x‖ₑ := by
        rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      _ ≤ _ := hx.trans (eLpNormEssSup_le_eLpNorm_top.trans hnorm)
  have hraw := (le_max_left (W.toFun x - (H - a)) 0).trans hxv
  change U.indicator w.toH1Function.toFun x ≤ H - H / (2 * (2 : ℝ) ^ N)
  have hhalf : H / (2 * (2 : ℝ) ^ N) = a / 2 := by dsimp [a]; ring
  rw [hhalf]
  change W.toFun x ≤ _
  linarith only [hraw]

/-- A finite dyadic depth makes the fourth-root level-measure factor small. -/
theorem exists_nat_fourth_root_le (B : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 0 < N ∧ Real.sqrt (Real.sqrt (B / (N : ℝ))) ≤ ε := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ε ^ 4)
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hquot : B / ε ^ 4 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact hn.le.trans (by simp only [Nat.cast_add, Nat.cast_one]; linarith)
  have hB : B / ((n + 1 : ℕ) : ℝ) ≤ ε ^ 4 := by
    apply (div_le_iff₀ hN).mpr
    have := (div_le_iff₀ (pow_pos hε 4)).mp hquot
    nlinarith only [this]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨hε.le, (Real.sqrt_le_iff).mpr ⟨sq_nonneg ε, ?_⟩⟩
  nlinarith only [hB]

/-- Choose the depth using only the numerical coefficients in the transported
De Giorgi estimate. In particular, the choice precedes all PDE data. -/
theorem exists_dyadic_contraction_depth {T E b B : ℝ}
    (hT : 0 < T) (hE : 0 < E) (hb : T * b < 1 / 2) :
    ∃ N : ℕ, 0 < N ∧
      T * (E * Real.sqrt (Real.sqrt (B / (N : ℝ))) + b) ≤ 1 / 2 := by
  let ε := (1 / 2 - T * b) / (T * E)
  have hε : 0 < ε := div_pos (sub_pos.mpr hb) (mul_pos hT hE)
  obtain ⟨N, hN, hroot⟩ := exists_nat_fourth_root_le B hε
  refine ⟨N, hN, ?_⟩
  have hεeq : T * E * ε = 1 / 2 - T * b := by
    dsimp [ε]
    field_simp
  calc
    _ ≤ T * (E * ε + b) := by gcongr
    _ = 1 / 2 := by nlinarith only [hεeq]

/-- On every sufficiently small boundary cube, a dyadic depth chosen before
the coefficient and PDE data gives a strict one-sided contraction. -/
theorem exists_forced_zero_extended_dyadic_contraction {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c z : Vec d) (R : ℝ), 0 ≤ R →
    ∀ {r : ℝ}, 0 < r → z ∈ frontier (euclideanBall c R) →
    ∀ {κ : ℝ}, 0 < κ → κ ≤ κ⁻¹ →
    ∀ (K : ℝ) (q : Vec d) {L : ℝ}, 0 < L →
      Homogenization.axisCube q L ⊆ euclideanBall z (r / 2) →
      C * (κ⁻¹ / κ) ^ deGiorgiPower d * (L ^ 2 / r ^ 2) < 1 / 2 →
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ (η : QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) K)
      {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → w.toH1Function.toFun x ≤ H) →
      κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N →
      ∀ᵐ x ∂(volume.restrict (halfCube q L)),
        (euclideanBall c R).indicator w.toH1Function.toFun x ≤
          θ * H := by
  obtain ⟨C, hC, hmain⟩ := forced_zero_extended_dyadic_contraction hd
  refine ⟨C, hC, ?_⟩
  intro c z R hR r hr hz κ hκ hκLam K q L hL hCube hgeom
  let B := ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
    (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
      ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
    (volume (euclideanBall z (r / 2))).toReal
  obtain ⟨N, hN, hscale⟩ := exists_dyadic_contraction_depth
    (T := C * (κ⁻¹ / κ) ^ deGiorgiPower d) (E := L ^ (-(d : ℝ) / 2))
    (b := L ^ 2 / r ^ 2) (B := B) (by positivity) (by positivity) hgeom
  let θ := 1 - 1 / (2 * (2 : ℝ) ^ N)
  have hden : 1 < 2 * (2 : ℝ) ^ N := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    linarith
  have hθpos : 0 < θ := sub_pos.mpr ((div_lt_one (by positivity)).mpr hden)
  have hθlt : θ < 1 := sub_lt_self _ (by positivity)
  refine ⟨N, hN, θ, hθpos, hθlt, ?_⟩
  intro A hA w f hf F hF hfF hw η H hH hbound hsmall
  have hb := hmain c z R hR hr hz hκ hκLam K hN q hL hCube hscale
    hA w f hf hF hfF hw η hH hbound hsmall
  filter_upwards [hb] with x hx
  calc
    _ ≤ H - H / (2 * (2 : ℝ) ^ N) := hx
    _ = θ * H := by dsimp [θ]; ring

/-- Sign change preserves the coefficient and negates both forcing terms in
the original-domain weak formulation, without changing the test space. -/
theorem weak_solution_neg {d : ℕ} {U : Set (Vec d)} {A : CoeffField d}
    {u : Homogenization.H1Function U} {f : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : IsWeakSolutionOn A U u f g) :
    IsWeakSolutionOn A U (-u) (fun x => -f x) (fun x => -g x) := by
  intro φ
  simp only [Homogenization.H1Function.neg_grad, Homogenization.matVecMul_neg,
    Homogenization.vecDot_neg_left, neg_mul, integral_neg, hu φ, neg_add]

/-- Negation of an actual zero-trace function uses its negated weak gradient. -/
theorem h10_neg_toH1Function {d : ℕ} {U : Set (Vec d)}
    (w : Homogenization.H10Function U) :
    (-w).toH1Function = -w.toH1Function := rfl

/-- The same geometric depth and contraction factor control both signs of
the zero extension. The amplitude is an actual local essential bound. -/
theorem exists_forced_zero_extended_dyadic_abs_contraction {d : ℕ} (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (c z : Vec d) (R : ℝ), 0 ≤ R →
    ∀ {r : ℝ}, 0 < r → z ∈ frontier (euclideanBall c R) →
    ∀ {κ : ℝ}, 0 < κ → κ ≤ κ⁻¹ →
    ∀ (K : ℝ) (q : Vec d) {L : ℝ}, 0 < L →
      Homogenization.axisCube q L ⊆ euclideanBall z (r / 2) →
      C * (κ⁻¹ / κ) ^ deGiorgiPower d * (L ^ 2 / r ^ 2) < 1 / 2 →
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ (_η : QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) K)
      {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N →
      ∀ᵐ x ∂(volume.restrict (halfCube q L)),
        |(euclideanBall c R).indicator w.toH1Function.toFun x| ≤ θ * H := by
  obtain ⟨C, hC, hmain⟩ := exists_forced_zero_extended_dyadic_contraction hd
  refine ⟨C, hC, ?_⟩
  intro c z R hR r hr hz κ hκ hκLam K q L hL hCube hgeom
  obtain ⟨N, hN, θ, hθ, hθ1, hb⟩ :=
    hmain c z R hR hr hz hκ hκLam K q hL hCube hgeom
  refine ⟨N, hN, θ, hθ, hθ1, ?_⟩
  intro A hA w f hf F hF hfF hw η H hH hbound hsmall
  have hpos := hb hA w f hf hF hfF hw η hH
    (hbound.mono fun x hx hxB => (le_abs_self _).trans (hx hxB)) hsmall
  have hnegw : IsWeakSolutionOn A (euclideanBall c R) (-w).toH1Function
      (fun x => -f x) (fun _ => 0) := by
    simpa only [h10_neg_toH1Function, neg_zero] using weak_solution_neg hw
  have hneg := hb hA (-w) (fun x => -f x) hf.neg hF
    (by simpa only [abs_neg] using hfF) hnegw η hH
    (by
      filter_upwards [hbound] with x hx hxB
      simpa only [h10_neg_toH1Function, Homogenization.H1Function.neg_toFun] using
        (neg_le_abs (w.toH1Function.toFun x)).trans (hx hxB)) hsmall
  filter_upwards [hpos, hneg] with x hp hn
  apply abs_le.mpr
  refine ⟨?_, hp⟩
  have heq : (euclideanBall c R).indicator (-w).toH1Function.toFun x =
      -(euclideanBall c R).indicator w.toH1Function.toFun x := by
    by_cases hx : x ∈ euclideanBall c R
    · simp only [Set.indicator_of_mem hx, h10_neg_toH1Function,
        Homogenization.H1Function.neg_toFun]
    · simp only [Set.indicator_of_notMem hx, neg_zero]
  rw [heq] at hn
  exact neg_le.mp hn

/-- A centered axis cube lies in the round ball at the quantitative
Euclidean scale; the ambient supremum norm is not used in the estimate. -/
theorem centered_axisCube_subset_euclideanBall {d : ℕ} (z : Vec d)
    {L r : ℝ} (hscale : (d : ℝ) * L ^ 2 < r ^ 2) :
    Homogenization.axisCube (fun i => z i - L / 2) L ⊆ euclideanBall z (r / 2) := by
  intro x hx
  have hcoord (i : Fin d) : (x i - z i) ^ 2 ≤ (L / 2) ^ 2 := by
    have hi := (Set.mem_pi.mp hx) i (Set.mem_univ i)
    have hlo : 0 ≤ x i - z i + L / 2 := by linarith only [hi.1]
    have hhi : 0 ≤ L / 2 - (x i - z i) := by linarith only [hi.2]
    nlinarith only [mul_nonneg hlo hhi]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  change euclideanSqDist x z < (r / 2) ^ 2
  rw [euclideanSqDist, vecNormSq_eq_sum_sq]
  simp only [Pi.sub_apply]
  nlinarith only [hsum, hscale]

/-- A centered half cube contains its center at every positive scale. -/
theorem center_mem_halfCube {d : ℕ} (z : Vec d) {L : ℝ} (hL : 0 < L) :
    z ∈ halfCube (fun i => z i - L / 2) L := by
  change ∀ i ∈ (Set.univ : Set (Fin d)),
    z i ∈ Set.Ioo ((z i - L / 2) + L / 4) ((z i - L / 2) + L / 4 + L / 2)
  intro i _
  constructor <;> linarith only [hL]

/-- A genuine smooth cutoff at every boundary center has gradient bound
`64/r` in the explicit Euclidean norm. -/
noncomputable def boundaryBallCutoff {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    QuantitativeSmoothCutoff (euclideanBall z (r / 2)) (euclideanBall z r) (64 / r) := by
  have hK : 32 / (r - r / 2) = 64 / r := by ring
  exact hK ▸ quantitativeBallCutoff z (r := r / 2) (R := r) (by positivity) (by linarith)

/-- A common side length can meet the Euclidean inclusion and the
De Giorgi geometric smallness condition before any PDE data is given. -/
theorem exists_boundary_cube_side (d : ℕ) {T r : ℝ} (hT : 0 ≤ T) (hr : 0 < r) :
    ∃ L : ℝ, 0 < L ∧ (d : ℝ) * L ^ 2 < r ^ 2 ∧
      T * (L ^ 2 / r ^ 2) < 1 / 2 := by
  let a : ℝ := 4 * ((d : ℝ) + 1) * (T + 1)
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : 1 < a := by dsimp [a]; nlinarith only [mul_nonneg hd hT, hd, hT]
  have hda : (d : ℝ) < a := by dsimp [a]; nlinarith only [mul_nonneg hd hT, hd, hT]
  have hTa : 2 * T < a := by dsimp [a]; nlinarith only [mul_nonneg hd hT, hd, hT]
  let L := r / a
  have hL : 0 < L := div_pos hr (by linarith)
  have hLa : L * a = r := div_mul_cancel₀ r (by linarith)
  have hLr : L < r := by nlinarith only [mul_lt_mul_of_pos_left ha hL, hLa]
  have hdL : (d : ℝ) * L < r := by
    nlinarith only [mul_lt_mul_of_pos_right hda hL, hLa]
  have hTL : 2 * T * L < r := by
    nlinarith only [mul_lt_mul_of_pos_right hTa hL, hLa]
  refine ⟨L, hL, ?_, ?_⟩
  · have h1 := mul_le_mul_of_nonneg_left hLr.le (mul_nonneg hd hL.le)
    have h2 := mul_lt_mul_of_pos_right hdL hr
    nlinarith only [h1, h2]
  · have h1 := mul_le_mul_of_nonneg_left hLr.le (by positivity : 0 ≤ 2 * T * L)
    have h2 := mul_lt_mul_of_pos_right hTL hr
    rw [show T * (L ^ 2 / r ^ 2) = T * L ^ 2 / r ^ 2 by ring]
    apply (div_lt_iff₀ (sq_pos_of_pos hr)).mpr
    nlinarith only [h1, h2]

/-- A round ball of a quarter side is contained in the centered half cube.
The comparison uses squared Euclidean coordinate bounds. -/
theorem euclideanBall_subset_centered_halfCube {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) :
    euclideanBall z (L / 4) ⊆ halfCube (fun i => z i - L / 2) L := by
  intro x hx
  change ∀ i ∈ (Set.univ : Set (Fin d)),
    x i ∈ Set.Ioo ((z i - L / 2) + L / 4) ((z i - L / 2) + L / 4 + L / 2)
  intro i _
  have hi : |x i - z i| < L / 4 :=
    abs_lt_of_sq_lt_sq ((sq_coord_sub_le_euclideanSqDist x z i).trans_lt hx)
      (by positivity)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hi
  constructor <;> linarith only [hlo, hhi]

/-- The actual round-ball boundary admits a finite cover by centered half
cubes of one common side length, whose full cubes lie in the prescribed
round neighborhoods. The smaller Euclidean balls also cover the boundary,
and the same exterior half-volume bound holds at every center. -/
theorem exists_finite_boundary_cube_cover {d : ℕ} (c : Vec d) {R r L : ℝ}
    (hR : 0 ≤ R) (hL : 0 < L) (hscale : (d : ℝ) * L ^ 2 < r ^ 2) :
    ∃ s : Finset (Vec d),
      (∀ z ∈ s, z ∈ frontier (euclideanBall c R)) ∧
      frontier (euclideanBall c R) ⊆ ⋃ z ∈ s, euclideanBall z (L / 4) ∧
      frontier (euclideanBall c R) ⊆ ⋃ z ∈ s, halfCube (fun i => z i - L / 2) L ∧
      (∀ z ∈ s, Homogenization.axisCube (fun i => z i - L / 2) L ⊆
        euclideanBall z (r / 2)) ∧
      (∀ z ∈ s, volume (euclideanBall z r) ≤
        2 * volume (euclideanBall z r \ euclideanBall c R)) := by
  classical
  let S := frontier (euclideanBall c R)
  have hclosed : closure (euclideanBall c R) ⊆ euclideanClosedBall c R :=
    closure_minimal (fun _ hx => (show euclideanSqDist _ c ≤ R ^ 2 from le_of_lt hx))
      (isClosed_euclideanClosedBall c R)
  have hcompact : IsCompact S :=
    (isCompact_euclideanClosedBall c hR).of_isClosed_subset isClosed_frontier
      (frontier_subset_closure.trans hclosed)
  let cell : S → Set (Vec d) := fun z => euclideanBall z.1 (L / 4)
  have hcover : S ⊆ ⋃ z : S, cell z := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, center_mem_euclideanBall x (by positivity)⟩
  obtain ⟨t, ht⟩ := hcompact.elim_finite_subcover cell
    (fun z => isOpen_euclideanBall _ _) hcover
  let s : Finset (Vec d) := t.image Subtype.val
  have hs (z : Vec d) (hz : z ∈ s) : z ∈ S := by
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    exact y.2
  have hballCover : S ⊆ ⋃ z ∈ s, euclideanBall z (L / 4) := by
    intro x hx
    have hx' : x ∈ ⋃ z ∈ t, cell z := ht hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨z, hz, hxz⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨z.1, Set.mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, hxz⟩⟩
  refine ⟨s, hs, hballCover, ?_, ?_, ?_⟩
  · intro x hx
    have hx' := hballCover hx
    simp only [Set.mem_iUnion] at hx' ⊢
    obtain ⟨z, hz, hxz⟩ := hx'
    exact ⟨z, hz, euclideanBall_subset_centered_halfCube z hL hxz⟩
  · intro z _
    exact centered_axisCube_subset_euclideanBall z hscale
  · intro z hz
    exact ball_exterior_half_volume c z R r (hs z hz)

/-- The boundary energy mass is bounded independently of the domain and
the boundary center, with its exact Euclidean scaling retained. -/
theorem restricted_ball_volume_toReal_le {d : ℕ} (c z : Vec d) (R : ℝ)
    {r : ℝ} (hr : 0 < r) :
    ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal ≤
      r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal := by
  calc
    _ ≤ (volume (euclideanBall z r)).toReal :=
      ENNReal.toReal_mono (volume_euclideanBall_ne_top z hr.le)
        (Measure.restrict_apply_le _ _)
    _ = _ := volume_euclideanBall_toReal_eq_unit_mul_of_pos z hr

/-- Exact scale cancellation in the boundary strip-energy coefficient. -/
theorem scaled_boundary_decay_algebra (d : ℕ) {r : ℝ} (hr : 0 < r) (a b V : ℝ) :
    (a * (r / 2)) ^ 2 *
      (4 * (2 / r ^ 2 + b * (64 / r) ^ 2) * (r ^ d * V)) *
      ((r / 2) ^ d * V) =
    (r ^ d) ^ 2 * ((a * (1 / 2)) ^ 2 * (4 * (2 + b * 64 ^ 2) * V) *
      ((1 / 2) ^ d * V)) := by
  simp only [div_pow, one_pow]
  field_simp

/-- The normalized fourth-root decay factor is invariant under dilation. -/
theorem scaled_fourth_root_factor (d : ℕ) {ℓ r : ℝ} (hℓ : 0 < ℓ) (hr : 0 < r)
    (B : ℝ) (N : ℕ) :
    (ℓ * r) ^ (-(d : ℝ) / 2) *
      Real.sqrt (Real.sqrt ((r ^ d) ^ 2 * B / (N : ℝ))) =
    ℓ ^ (-(d : ℝ) / 2) * Real.sqrt (Real.sqrt (B / (N : ℝ))) := by
  rw [mul_div_assoc, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg hr.le d), Real.sqrt_mul (pow_nonneg hr.le d),
    Real.mul_rpow hℓ.le hr.le]
  have hsqrt : Real.sqrt (r ^ d) = r ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [hsqrt]
  have hc : r ^ (-(d : ℝ) / 2) * r ^ ((d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add hr]
    simp only [neg_div, neg_add_cancel, Real.rpow_zero]
  calc
    _ = ℓ ^ (-(d : ℝ) / 2) *
        (r ^ (-(d : ℝ) / 2) * r ^ ((d : ℝ) / 2)) *
        Real.sqrt (Real.sqrt (B / (N : ℝ))) := by ring
    _ = _ := by rw [hc, mul_one]

/-- One dimensionless cube scale, dyadic depth, and strict two-sided
contraction factor work at every boundary point of every Euclidean ball.
The witnesses depend only on dimension and ellipticity, preceding even the
neighborhood radius as well as the ball and the PDE data. -/
theorem exists_uniform_boundary_abs_contraction {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ (d : ℝ) * ℓ ^ 2 < 1 ∧
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
    ∀ {r : ℝ}, 0 < r →
    ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∀ (z : Vec d), z ∈ frontier (euclideanBall c R) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N →
      ∀ᵐ x ∂(volume.restrict (halfCube (fun i => z i - ℓ * r / 2) (ℓ * r))),
        |(euclideanBall c R).indicator w.toH1Function.toFun x| ≤ θ * H := by
  obtain ⟨C, hC, hmain⟩ := forced_zero_extended_dyadic_contraction hd
  let T := C * (κ⁻¹ / κ) ^ deGiorgiPower d
  have hT : 0 < T := by dsimp [T]; positivity
  obtain ⟨ℓ, hℓ, hdim, hgeom⟩ := exists_boundary_cube_side d hT.le (by norm_num : (0 : ℝ) < 1)
  simp only [one_pow, div_one] at hdim hgeom
  let V := (volume (euclideanBall (0 : Vec d) 1)).toReal
  let B := ((2 : ℝ) ^ (d + 2) * (1 / 2)) ^ 2 *
    (4 * (2 + 4 * κ⁻¹ ^ 2 * 64 ^ 2) * V) * ((1 / 2) ^ d * V)
  obtain ⟨N, hN, hNscale⟩ := exists_dyadic_contraction_depth
    (E := ℓ ^ (-(d : ℝ) / 2)) (B := B) hT (by positivity) hgeom
  let θ := 1 - 1 / (2 * (2 : ℝ) ^ N)
  have hden : 1 < 2 * (2 : ℝ) ^ N := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
    linarith
  refine ⟨ℓ, hℓ, hdim, N, hN, θ,
    sub_pos.mpr ((div_lt_one (by positivity)).mpr hden),
    sub_lt_self _ (by positivity), ?_⟩
  intro r hr c R hR z hz A hA w f hf F hF hfF hw H hH hbound hsmall
  let L := ℓ * r
  let K := 64 / r
  have hL : 0 < L := mul_pos hℓ hr
  have hdimr : (d : ℝ) * L ^ 2 < r ^ 2 := by
    dsimp only [L]
    nlinarith only [mul_lt_mul_of_pos_right hdim (sq_pos_of_pos hr)]
  have hBz : ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
      (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
      (volume (euclideanBall z (r / 2))).toReal ≤ (r ^ d) ^ 2 * B := by
    calc
      _ ≤ ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
          (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) * (r ^ d * V)) *
          ((r / 2) ^ d * V) := by
        rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos z (by positivity : 0 < r / 2)]
        gcongr
        exact restricted_ball_volume_toReal_le c z R hr
      _ = _ := scaled_boundary_decay_algebra d hr ((2 : ℝ) ^ (d + 2)) (4 * κ⁻¹ ^ 2) V
  have hscale : (let Bz := ((2 : ℝ) ^ (d + 2) * (r / 2)) ^ 2 *
      (4 * (2 / r ^ 2 + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        ((volume.restrict (euclideanBall c R)) (euclideanBall z r)).toReal) *
      (volume (euclideanBall z (r / 2))).toReal
      T * (L ^ (-(d : ℝ) / 2) * Real.sqrt (Real.sqrt (Bz / (N : ℝ))) +
        L ^ 2 / r ^ 2) ≤ 1 / 2) := by
    calc
      _ ≤ T * (L ^ (-(d : ℝ) / 2) *
          Real.sqrt (Real.sqrt ((r ^ d) ^ 2 * B / (N : ℝ))) + L ^ 2 / r ^ 2) := by gcongr
      _ = T * (ℓ ^ (-(d : ℝ) / 2) * Real.sqrt (Real.sqrt (B / (N : ℝ))) + ℓ ^ 2) := by
        rw [scaled_fourth_root_factor d hℓ hr]
        congr 2
        dsimp only [L]
        field_simp
      _ ≤ _ := hNscale
  have hb := hmain c z R hR hr hz hκ hκLam K hN
    (fun i => z i - L / 2) hL (centered_axisCube_subset_euclideanBall z hdimr) hscale hA
  have hpos := hb w f hf hF hfF hw (boundaryBallCutoff z hr) hH
    (hbound.mono fun x hx hxB => (le_abs_self _).trans (hx hxB)) hsmall
  have hnegw : IsWeakSolutionOn A (euclideanBall c R) (-w).toH1Function
      (fun x => -f x) (fun _ => 0) := by
    simpa only [h10_neg_toH1Function, neg_zero] using weak_solution_neg hw
  have hneg := hb (-w) (fun x => -f x) hf.neg hF
    (by simpa only [abs_neg] using hfF) hnegw (boundaryBallCutoff z hr) hH
    (by
      filter_upwards [hbound] with x hx hxB
      simpa only [h10_neg_toH1Function, Homogenization.H1Function.neg_toFun] using
        (neg_le_abs (w.toH1Function.toFun x)).trans (hx hxB)) hsmall
  filter_upwards [hpos, hneg] with x hp hn
  have heq : (euclideanBall c R).indicator (-w).toH1Function.toFun x =
      -(euclideanBall c R).indicator w.toH1Function.toFun x := by
    by_cases hx : x ∈ euclideanBall c R
    · simp only [Set.indicator_of_mem hx, h10_neg_toH1Function,
        Homogenization.H1Function.neg_toFun]
    · simp only [Set.indicator_of_notMem hx, neg_zero]
  rw [heq] at hn
  have hθeq : H - H / (2 * (2 : ℝ) ^ N) = θ * H := by dsimp [θ]; ring
  rw [hθeq] at hp hn
  exact abs_le.mpr ⟨neg_le.mp hn, hp⟩

/-- The local two-sided contraction holds throughout one finite Euclidean
cover of the boundary. The scale, depth, and factor are chosen from dimension
and ellipticity; the centers are chosen from geometry before all PDE data. -/
theorem exists_uniform_boundary_cover_abs_contraction {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∃ N : ℕ, 0 < N ∧
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
    ∀ {r : ℝ}, 0 < r → ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∃ s : Finset (Vec d),
      (∀ z ∈ s, z ∈ frontier (euclideanBall c R)) ∧
      frontier (euclideanBall c R) ⊆ ⋃ z ∈ s, euclideanBall z (ℓ * r / 4) ∧
      (∀ z ∈ s, Homogenization.axisCube (fun i => z i - ℓ * r / 2) (ℓ * r) ⊆
        euclideanBall z (r / 2)) ∧
      (∀ z ∈ s, volume (euclideanBall z r) ≤
        2 * volume (euclideanBall z r \ euclideanBall c R)) ∧
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ z ∈ s, ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      κ⁻¹ * r ^ 2 * F ≤ H / (2 : ℝ) ^ N →
      ∀ᵐ x ∂(volume.restrict (⋃ z ∈ s, euclideanBall z (ℓ * r / 4))),
        |(euclideanBall c R).indicator w.toH1Function.toFun x| ≤ θ * H := by
  obtain ⟨ℓ, hℓ, hdim, N, hN, θ, hθ, hθ1, hb⟩ :=
    exists_uniform_boundary_abs_contraction hd hκ hκLam
  refine ⟨ℓ, hℓ, N, hN, θ, hθ, hθ1, ?_⟩
  intro r hr c R hR
  have hL : 0 < ℓ * r := mul_pos hℓ hr
  have hdimr : (d : ℝ) * (ℓ * r) ^ 2 < r ^ 2 := by
    nlinarith only [mul_lt_mul_of_pos_right hdim (sq_pos_of_pos hr)]
  obtain ⟨s, hs, hballCover, _, hinc, hhalf⟩ :=
    exists_finite_boundary_cube_cover c hR hL hdimr
  refine ⟨s, hs, hballCover, hinc, hhalf, ?_⟩
  intro A hA w f hf F hF hfF hw H hH hbound hsmall
  apply (ae_restrict_biUnion_finset_iff _ s _).mpr
  intro z hz
  exact ae_restrict_of_ae_restrict_of_subset
    (euclideanBall_subset_centered_halfCube z hL)
    (hb hr c R hR z (hs z hz) hA w f hf hF hfF hw hH (hbound z hz) hsmall)

/-- A Euclidean boundary-ball step with an explicit forcing floor. The
radius ratio and contraction factor depend only on dimension and ellipticity.
The floor removes the small-forcing restriction from the input amplitude. -/
theorem exists_uniform_boundary_ball_forced_contraction {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q ^ 2 ≤ θ ∧
    ∀ {r : ℝ}, 0 < r →
    ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∀ (z : Vec d), z ∈ frontier (euclideanBall c R) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z (q * r) →
        |w.toH1Function.toFun x| ≤ θ * max H ((2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) := by
  obtain ⟨ℓ, hℓ, _, N, hN, θ, hθ, hθ1, hb⟩ :=
    exists_uniform_boundary_abs_contraction hd hκ hκLam
  let q := min (ℓ / 4) (θ / 2)
  have hq : 0 < q := lt_min (by positivity) (by positivity)
  have hqθ : q ≤ θ / 2 := min_le_right _ _
  have hq1 : q < 1 := by linarith only [hqθ, hθ1]
  have hq2 : q ^ 2 ≤ θ := by nlinarith only [hq.le, hqθ, hq1.le]
  refine ⟨q, hq, hq1, N, hN, θ, hθ, hθ1, hq2, ?_⟩
  intro r hr c R hR z hz A hA w f hf F hF hfF hw H hH hbound
  let M := max H ((2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F)
  have hM : 0 < M := hH.trans_le (le_max_left _ _)
  have hsmall : κ⁻¹ * r ^ 2 * F ≤ M / (2 : ℝ) ^ N := by
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ N)).mpr
    calc
      _ = (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F := by ring
      _ ≤ M := le_max_right _ _
  have hc := hb hr c R hR z hz hA w f hf hF hfF hw hM
    (hbound.mono fun _ hx hxB => (hx hxB).trans (le_max_left _ _)) hsmall
  have hinc : euclideanBall z (q * r) ⊆
      halfCube (fun i => z i - ℓ * r / 2) (ℓ * r) :=
    (euclideanBall_mono (mul_nonneg hq.le hr.le)
      (by nlinarith only [mul_le_mul_of_nonneg_right (min_le_left (ℓ / 4) (θ / 2)) hr.le])).trans
        (euclideanBall_subset_centered_halfCube z (mul_pos hℓ hr))
  have hball := ae_restrict_of_ae_restrict_of_subset hinc hc
  have hglobal := (ae_restrict_iff' (isOpen_euclideanBall z (q * r)).measurableSet).mp hball
  filter_upwards [ae_restrict_of_ae hglobal,
    ae_restrict_mem (isOpen_euclideanBall c R).measurableSet] with x hx hxD hxB
  simpa only [Set.indicator_of_mem hxD] using hx hxB

/-- The squared spatial scale decays at least as fast as the amplitude.
Consequently one initial forcing allowance dominates every subsequent floor. -/
theorem geometric_boundary_forcing_floor {q θ κ H F r : ℝ}
    (hqθ : q ^ 2 ≤ θ) (hκ : 0 < κ) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (N n : ℕ) :
    (2 : ℝ) ^ N * κ⁻¹ * (r * q ^ n) ^ 2 * F ≤
      θ ^ n * (H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) := by
  have hS : 0 ≤ (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F := by positivity
  have hp : (q ^ n) ^ 2 ≤ θ ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg q) hqθ n
  calc
    _ = ((2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) * (q ^ n) ^ 2 := by ring
    _ ≤ ((2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) * θ ^ n := mul_le_mul_of_nonneg_left hp hS
    _ ≤ θ ^ n * (H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) := by
      have hθ : 0 ≤ θ := (sq_nonneg q).trans hqθ
      nlinarith only [mul_nonneg (pow_nonneg hθ n) hH]

/-- Quantitative decay at all geometric scales for the same actual zero-trace
weak solution. There is one exceptional null set for all scales. The initial
local amplitude is explicit; the estimate does not supply an eigenfunction
amplitude bound or identify a killed process with a PDE realization. -/
theorem exists_uniform_boundary_geometric_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧
    ∃ N : ℕ, 0 < N ∧ ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q ^ 2 ≤ θ ∧
    ∀ {r : ℝ}, 0 < r →
    ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∀ (z : Vec d), z ∈ frontier (euclideanBall c R) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), ∀ n : ℕ,
        x ∈ euclideanBall z (r * q ^ n) →
        |w.toH1Function.toFun x| ≤
          θ ^ n * (H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) := by
  obtain ⟨q, hq, hq1, N, hN, θ, hθ, hθ1, hqθ, hb⟩ :=
    exists_uniform_boundary_ball_forced_contraction hd hκ hκLam
  refine ⟨q, hq, hq1, N, hN, θ, hθ, hθ1, hqθ, ?_⟩
  intro r hr c R hR z hz A hA w f hf F hF hfF hw H hH hbound
  let M := H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F
  have hM : 0 < M := add_pos_of_pos_of_nonneg hH (by positivity)
  apply ae_all_iff.mpr
  intro n
  induction n with
  | zero =>
      simpa only [pow_zero, mul_one, one_mul] using
        (hbound.mono fun _ hx hxB => (hx hxB).trans
          (show H ≤ M from le_add_of_nonneg_right (by positivity)))
  | succ n ih =>
      have hfloor : (2 : ℝ) ^ N * κ⁻¹ * (r * q ^ n) ^ 2 * F ≤ θ ^ n * M :=
        geometric_boundary_forcing_floor hqθ hκ hH.le hF N n
      have hstep := hb (mul_pos hr (pow_pos hq n)) c R hR z hz hA w f hf hF hfF hw
        (mul_pos (pow_pos hθ n) hM) ih
      have hrad : q * (r * q ^ n) = r * q ^ (n + 1) := by rw [pow_succ]; ring
      rw [max_eq_left hfloor, hrad] at hstep
      have hamp : θ * (θ ^ n * M) = θ ^ (n + 1) * M := by rw [pow_succ]; ring
      rw [hamp] at hstep
      exact hstep

/-- Positive geometric ratios determine a positive power-law exponent. -/
theorem exists_geometric_decay_exponent {q θ : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    ∃ α : ℝ, 0 < α ∧ q ^ α = θ := by
  refine ⟨Real.log θ / Real.log q,
    div_pos_of_neg_of_neg (Real.log_neg hθ hθ1) (Real.log_neg hq hq1), ?_⟩
  rw [Real.rpow_def_of_pos hq]
  have hc : Real.log q * (Real.log θ / Real.log q) = Real.log θ := by
    field_simp [(Real.log_neg hq hq1).ne]
  rw [hc, Real.exp_log hθ]

/-- Every intermediate relative radius is controlled by a geometric scale,
with at most one inverse contraction factor lost in its power estimate. -/
theorem exists_geometric_scale_power_bound {q θ α t : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hθ : 0 < θ) (hα : 0 ≤ α)
    (hqα : q ^ α = θ) (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ n : ℕ, t ≤ q ^ n ∧ θ ^ n ≤ t ^ α / θ := by
  obtain ⟨n, hlo, hhi⟩ := exists_nat_pow_near_of_lt_one ht ht1 hq hq1
  refine ⟨n, hhi, (le_div_iff₀ hθ).mpr ?_⟩
  have heq : (q ^ (n + 1)) ^ α = θ ^ (n + 1) := by
    rw [← Real.rpow_natCast_mul hq.le, mul_comm (↑(n + 1) : ℝ),
      Real.rpow_mul_natCast hq.le, hqα]
  calc
    _ = θ ^ (n + 1) := (pow_succ θ n).symm
    _ = (q ^ (n + 1)) ^ α := heq.symm
    _ ≤ t ^ α := Real.rpow_le_rpow (pow_nonneg hq.le _) hlo.le hα

/-- Power-law boundary decay on every Euclidean radius below the initial
radius, simultaneously outside one null set. The constants and exponent
precede the domain, radius, boundary center, coefficients, and weak solution.
Only the initial local amplitude and the actual bounded forcing enter the
right-hand side. -/
theorem exists_uniform_boundary_power_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧
    ∀ {r : ℝ}, 0 < r →
    ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∀ (z : Vec d), z ∈ frontier (euclideanBall c R) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
      ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), ∀ s : ℝ,
        0 < s → s ≤ r → x ∈ euclideanBall z s →
        |w.toH1Function.toFun x| ≤
          C * (s / r) ^ α * (H + κ⁻¹ * r ^ 2 * F) := by
  obtain ⟨q, hq, hq1, N, _, θ, hθ, hθ1, _, hb⟩ :=
    exists_uniform_boundary_geometric_decay hd hκ hκLam
  obtain ⟨α, hα, hqα⟩ := exists_geometric_decay_exponent hq hq1 hθ hθ1
  refine ⟨α, (2 : ℝ) ^ N / θ, hα, by positivity, ?_⟩
  intro r hr c R hR z hz A hA w f hf F hF hfF hw H hH hbound
  have hgeom := hb hr c R hR z hz hA w f hf hF hfF hw hH hbound
  have hM : 0 ≤ H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F := by positivity
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ N := one_le_pow₀ (by norm_num)
  have hamp : H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F ≤
      (2 : ℝ) ^ N * (H + κ⁻¹ * r ^ 2 * F) := by
    nlinarith only [mul_le_mul_of_nonneg_right htwo hH.le]
  filter_upwards [hgeom] with x hx s hs hsr hxs
  obtain ⟨n, hscale, hpower⟩ := exists_geometric_scale_power_bound hq hq1 hθ hα.le hqα
    (div_pos hs hr) ((div_le_one hr).mpr hsr)
  have hrad : s ≤ r * q ^ n := by
    simpa only [mul_comm r] using (div_le_iff₀ hr).mp hscale
  calc
    _ ≤ θ ^ n * (H + (2 : ℝ) ^ N * κ⁻¹ * r ^ 2 * F) :=
      hx n (euclideanBall_mono hs.le hrad hxs)
    _ ≤ ((s / r) ^ α / θ) * ((2 : ℝ) ^ N * (H + κ⁻¹ * r ^ 2 * F)) :=
      mul_le_mul hpower hamp hM (by positivity)
    _ = _ := by ring

/-- An AE bound for a weak function transfers to its continuous
representative on an open set. Positivity of volume on nonempty open sets
rules out exceptional values of the representative. -/
theorem abs_le_on_open_of_ae_bound {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {v w : Vec d → ℝ} (hv : ContinuousOn v U)
    (hvw : v =ᵐ[volume.restrict U] w) {K : ℝ}
    (hw : ∀ᵐ x ∂(volume.restrict U), |w x| ≤ K) :
    ∀ x ∈ U, |v x| ≤ K := by
  have heq : (fun x => min |v x| K) =ᵐ[volume.restrict U] (fun x => |v x|) := by
    filter_upwards [hvw, hw] with x hx hbound
    exact min_eq_left (hx ▸ hbound)
  have heqOn := Measure.eqOn_open_of_ae_eq heq hU
    (hv.abs.inf continuousOn_const) hv.abs
  intro x hx
  exact min_eq_left_iff.mp (heqOn hx)

/-- The single-null-set, all-radii boundary estimate yields pointwise
estimates at every interior point of the same continuous representative. -/
theorem boundary_power_bound_continuous_representative {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {v w : Vec d → ℝ}
    (hv : ContinuousOn v U) (hvw : v =ᵐ[volume.restrict U] w)
    {z : Vec d} {r α C M : ℝ}
    (hbound : ∀ᵐ x ∂(volume.restrict U), ∀ s : ℝ,
      0 < s → s ≤ r → x ∈ euclideanBall z s → |w x| ≤ C * (s / r) ^ α * M) :
    ∀ s : ℝ, 0 < s → s ≤ r → ∀ x ∈ U, x ∈ euclideanBall z s →
      |v x| ≤ C * (s / r) ^ α * M := by
  intro s hs hsr x hx hxs
  have hsub : U ∩ euclideanBall z s ⊆ U := Set.inter_subset_left
  have heq := ae_restrict_of_ae_restrict_of_subset hsub hvw
  have hb := ae_restrict_of_ae_restrict_of_subset hsub hbound
  have hball : ∀ᵐ y ∂(volume.restrict (U ∩ euclideanBall z s)),
      y ∈ U ∩ euclideanBall z s := ae_restrict_mem (hU.inter
        (isOpen_euclideanBall z s)).measurableSet
  have hlocal : ∀ᵐ y ∂(volume.restrict (U ∩ euclideanBall z s)),
      |w y| ≤ C * (s / r) ^ α * M := by
    filter_upwards [hb, hball] with y hy hymem
    exact hy s hs hsr hymem.2
  exact abs_le_on_open_of_ae_bound (hU.inter (isOpen_euclideanBall z s))
    (hv.mono hsub) heq hlocal x ⟨hx, hxs⟩

/-- A positive power of the relative radius vanishes at radius zero.
The local amplitude and forcing enter only through the fixed multiplier. -/
theorem boundary_power_modulus_tendsto_zero {r α : ℝ} (hα : 0 < α) (C M : ℝ) :
    Filter.Tendsto (fun s : ℝ => C * (s / r) ^ α * M) (𝓝 0) (𝓝 0) := by
  have hdiv : Filter.Tendsto (fun s : ℝ => s / r) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, zero_div] using (Filter.tendsto_id :
      Filter.Tendsto (fun s : ℝ => s) (𝓝 0) (𝓝 0)).div_const r
  simpa only [mul_zero, zero_mul] using
    (hdiv.rpow_const_nhds_zero hα).const_mul C |>.mul_const M

/-- A radius can be chosen below the initial radius with arbitrarily small
power modulus. The choice does not involve the weak solution's point values. -/
theorem exists_small_boundary_power_modulus {r α : ℝ} (hr : 0 < r) (hα : 0 < α)
    (C M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : ℝ, 0 < s ∧ s ≤ r ∧ C * (s / r) ^ α * M < ε := by
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0, C * (s / r) ^ α * M < ε :=
    ((boundary_power_modulus_tendsto_zero hα C M).eventually
      (gt_mem_nhds hε)).filter_mono nhdsWithin_le_nhds
  have hradius : ∀ᶠ s : ℝ in 𝓝[>] 0, s < r :=
    (gt_mem_nhds hr).filter_mono nhdsWithin_le_nhds
  obtain ⟨s, hs, hsr, hsbound⟩ :=
    (eventually_mem_nhdsWithin.and (hradius.and hsmall)).exists
  exact ⟨s, hs, hsr.le, hsbound⟩

/-- Interior pointwise power decay gives a genuine zero limit of the zero
extension, along all ambient approaches to the boundary point. -/
theorem tendsto_zero_indicator_of_boundary_power_bound {d : ℕ} {U : Set (Vec d)}
    {v : Vec d → ℝ} {z : Vec d} {r α C M : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hbound : ∀ s : ℝ, 0 < s → s ≤ r → ∀ x ∈ U, x ∈ euclideanBall z s →
      |v x| ≤ C * (s / r) ^ α * M) :
    Filter.Tendsto (U.indicator v) (𝓝 z) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨s, hs, hsr, hsmall⟩ := exists_small_boundary_power_modulus hr hα C M hε
  have hzball : z ∈ euclideanBall z s := by
    change euclideanSqDist z z < s ^ 2
    rw [euclideanSqDist_self]
    exact sq_pos_of_pos hs
  filter_upwards [(isOpen_euclideanBall z s).mem_nhds hzball] with x hx
  rw [Real.dist_eq, sub_zero]
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU]
    exact (hbound s hs hsr x hxU hx).trans_lt hsmall
  · rw [Set.indicator_of_notMem hxU, abs_zero]
    exact hε

/-- At a point outside the domain, the preceding zero limit is continuity
of the actual zero extension. No continuity of the weak representative is
assumed outside the open domain. -/
theorem continuousAt_indicator_of_boundary_power_bound {d : ℕ} {U : Set (Vec d)}
    {v : Vec d → ℝ} {z : Vec d} (hz : z ∉ U)
    {r α C M : ℝ} (hr : 0 < r) (hα : 0 < α)
    (hbound : ∀ s : ℝ, 0 < s → s ≤ r → ∀ x ∈ U, x ∈ euclideanBall z s →
      |v x| ≤ C * (s / r) ^ α * M) :
    ContinuousAt (U.indicator v) z := by
  change Filter.Tendsto (U.indicator v) (𝓝 z) (𝓝 (U.indicator v z))
  rw [Set.indicator_of_notMem hz]
  exact tendsto_zero_indicator_of_boundary_power_bound hr hα hbound

/-- Uniform boundary decay for a genuine interior continuous representative
of the same forced H10 solution, with continuous zero extension at the chosen
boundary point. Constants precede the geometry and all PDE data; the local
initial amplitude is retained. This does not produce the interior representative. -/
theorem exists_uniform_boundary_representative_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) :
    ∃ α C : ℝ, 0 < α ∧ 0 < C ∧
    ∀ {r : ℝ}, 0 < r →
    ∀ (c : Vec d) (R : ℝ), 0 ≤ R →
    ∀ (z : Vec d), z ∈ frontier (euclideanBall c R) →
    ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A →
    ∀ (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ),
      AEStronglyMeasurable f (volume.restrict (euclideanBall c R)) →
    ∀ {F : ℝ}, 0 ≤ F →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F) →
      IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0) →
    ∀ {H : ℝ}, 0 < H →
      (∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H) →
    ∀ v : Vec d → ℝ, ContinuousOn v (euclideanBall c R) →
      v =ᵐ[volume.restrict (euclideanBall c R)] w.toH1Function.toFun →
      (∀ s : ℝ, 0 < s → s ≤ r → ∀ x ∈ euclideanBall c R,
        x ∈ euclideanBall z s →
        |v x| ≤ C * (s / r) ^ α * (H + κ⁻¹ * r ^ 2 * F)) ∧
      ContinuousAt ((euclideanBall c R).indicator v) z := by
  obtain ⟨α, C, hα, hC, hdecay⟩ := exists_uniform_boundary_power_decay hd hκ hκLam
  refine ⟨α, C, hα, hC, ?_⟩
  intro r hr c R hR z hz A hA w f hf F hF hfF hw H hH hbound v hv hvw
  have hpoint := boundary_power_bound_continuous_representative
    (isOpen_euclideanBall c R) hv hvw
    (hdecay hr c R hR z hz hA w f hf hF hfF hw hH hbound)
  refine ⟨hpoint, continuousAt_indicator_of_boundary_power_bound ?_ hr hα hpoint⟩
  exact hz.2 ∘ fun h => (isOpen_euclideanBall c R).interior_eq.symm ▸ h

/-- Continuity inside the domain and at its frontier suffices for global
continuity of the zero extension. Away from the frontier, the extension is
locally either the representative or the zero function. -/
theorem continuous_indicator_of_continuousAt_frontier {d : ℕ} {U : Set (Vec d)}
    {v : Vec d → ℝ} (hv : ContinuousOn v U)
    (hfront : ∀ z ∈ frontier U, ContinuousAt (U.indicator v) z) :
    Continuous (U.indicator v) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z ∈ frontier U
  · exact hfront z hz
  · exact (hv.mono interior_subset).continuousAt_indicator hz

/-- A genuine continuous representative of a locally bounded forced H10
solution has a globally continuous zero extension. Local amplitudes may vary
along the boundary. The extension agrees AE on the whole ambient space with
the same H10 function's canonical zero extension. -/
theorem continuous_zero_extension_of_locally_bounded_weak_solution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹)
    {c : Vec d} {R : ℝ} (hR : 0 ≤ R) {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A)
    (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (euclideanBall c R)))
    {F : ℝ} (hF : 0 ≤ F)
    (hfF : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F)
    (hw : IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0))
    (hlocal : ∀ z ∈ frontier (euclideanBall c R), ∃ r H : ℝ,
      0 < r ∧ 0 < H ∧ ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
        x ∈ euclideanBall z r → |w.toH1Function.toFun x| ≤ H)
    {v : Vec d → ℝ} (hv : ContinuousOn v (euclideanBall c R))
    (hvw : v =ᵐ[volume.restrict (euclideanBall c R)] w.toH1Function.toFun) :
    Continuous ((euclideanBall c R).indicator v) ∧
      (euclideanBall c R).indicator v =ᵐ[volume] w.zeroExtension := by
  refine ⟨continuous_indicator_of_continuousAt_frontier hv ?_, ?_⟩
  · obtain ⟨α, C, _, _, hdecay⟩ :=
      exists_uniform_boundary_representative_decay hd hκ hκLam
    intro z hz
    obtain ⟨r, H, hr, hH, hbound⟩ := hlocal z hz
    exact (hdecay hr c R hR z hz hA w f hf hF hfF hw hH hbound v hv hvw).2
  · exact (ae_eq_restrict_iff_indicator_ae_eq (measurableSet_euclideanBall c R)).mp hvw

/-- A global AE amplitude bound supplies all local boundary amplitudes for
the continuous zero extension API. In particular, no global pointwise bound
on the weak function is needed. -/
theorem continuous_zero_extension_of_bounded_weak_solution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹)
    {c : Vec d} {R : ℝ} (hR : 0 ≤ R) {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ (euclideanBall c R) A)
    (w : Homogenization.H10Function (euclideanBall c R)) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (euclideanBall c R)))
    {F : ℝ} (hF : 0 ≤ F)
    (hfF : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)), |f x| ≤ F)
    (hw : IsWeakSolutionOn A (euclideanBall c R) w.toH1Function f (fun _ => 0))
    {H : ℝ} (hH : 0 < H)
    (hbound : ∀ᵐ x ∂(volume.restrict (euclideanBall c R)),
      |w.toH1Function.toFun x| ≤ H)
    {v : Vec d → ℝ} (hv : ContinuousOn v (euclideanBall c R))
    (hvw : v =ᵐ[volume.restrict (euclideanBall c R)] w.toH1Function.toFun) :
    Continuous ((euclideanBall c R).indicator v) ∧
      (euclideanBall c R).indicator v =ᵐ[volume] w.zeroExtension := by
  apply continuous_zero_extension_of_locally_bounded_weak_solution hd hκ hκLam hR hA
    w f hf hF hfF hw ?_ hv hvw
  intro z _
  refine ⟨1, H, zero_lt_one, hH, ?_⟩
  filter_upwards [hbound] with x hx _
  exact hx

/-- Boundary level energy with L² forcing on the original open domain. The cutoff
need not be supported inside the domain: the nonnegative level makes its
product with the positive part a legal `H¹₀(U)` test. The forcing integral
is retained with its actual absolute value. Neither the forcing nor the
solution is assumed essentially bounded. -/
theorem l2_forced_boundary_level_caccioppoli {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) {κ : ℝ}
    (hκ : 0 < κ) {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (w : Homogenization.H10Function U) (f : Vec d → ℝ)
    (hf : MemL2On U f)
    (hw : IsWeakSolutionOn A U w.toH1Function f (fun _ => 0))
    {k : ℝ} (hk : 0 ≤ k) {I O : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) :
    (∫ x in U, η.toFun x ^ 2 *
      vecNormSq ({y | k < w.toH1Function.toFun y}.indicator
        w.toH1Function.grad x)) ≤
      2 * κ⁻¹ * (∫ x in U, |f x| * η.toFun x ^ 2 *
        max (w.toH1Function.toFun x - k) 0) +
      4 * κ⁻¹ ^ 2 * (∫ x in U,
        max (w.toH1Function.toFun x - k) 0 ^ 2 *
          vecNormSq (classicalGradient η.toFun x)) := by
  classical
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let u := w.toH1Function
  let v : Vec d → ℝ := fun x => max (u.toFun x - k) 0
  let E : Vec d → ℝ := fun x => η.toFun x ^ 2 * vecNormSq (posPartGrad u k x)
  let D : Vec d → ℝ := fun x => v x ^ 2 * vecNormSq (classicalGradient η.toFun x)
  obtain ⟨φ, hφf, hφg⟩ := exists_levelTest_h10 hU hfin w hk η.smooth η.hasCompactSupport
  have hηtop : MemLpOn U ⊤ η.toFun :=
    DGNM.memLpOn_top_of_contDiff η.smooth η.hasCompactSupport
  have hv : MemL2On U v := memL2On_positivePart_of_nonneg u hk
  have hEvec : MemVectorL2On U (fun x => η.toFun x • posPartGrad u k x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (posPartGrad_gradMemL2 u k i).fun_mul hηtop
  have hEint : IntegrableOn E U := by
    simpa only [E, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hEvec
  have hDvec : MemVectorL2On U (fun x => v x • classicalGradient η.toFun x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using hv.fun_mul
      (DGNM.memLpOn_top_classicalGradient η.smooth η.hasCompactSupport i)
  have hDint : IntegrableOn D U := by
    simpa only [D, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hDvec
  have hflux := integrableOn_vecDot_of_memVectorL2On
    (memVectorL2On_matVecMul_of_isEllipticFieldOn hA u.gradMemL2)
    φ.toH1Function.gradMemL2
  have hforce := integrableOn_mul_of_memL2On hf φ.toH1Function.memL2
  have habsf : MemL2On U (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have habsforce := integrableOn_mul_of_memL2On habsf φ.toH1Function.memL2
  have hpoint : ∀ᵐ x ∂volumeOn U,
      (κ / 2) * E x ≤
        vecDot (matVecMul (A x) (u.grad x)) (φ.toH1Function.grad x) + 2 * κ⁻¹ * D x := by
    filter_upwards [ae_restrict_mem hU.measurableSet, hφg] with x hx hgrad
    rw [hgrad]
    exact level_test_energy_bound (hA.elliptic hx) u k η.toFun x
  have hbound := integral_mono_ae (hEint.const_mul (κ / 2))
    (hflux.add (hDint.const_mul (2 * κ⁻¹))) hpoint
  dsimp only [Pi.add_apply] at hbound
  rw [integral_add hflux (hDint.const_mul (2 * κ⁻¹)),
    integral_const_mul, integral_const_mul] at hbound
  have hweak := hw φ
  simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at hweak
  change (∫ x in U, vecDot (matVecMul (A x) (u.grad x))
    (φ.toH1Function.grad x)) = (∫ x in U, f x * φ.toH1Function.toFun x) at hweak
  rw [hweak] at hbound
  have hforce_le : (∫ x in U, f x * φ.toH1Function.toFun x) ≤
      ∫ x in U, |f x| * η.toFun x ^ 2 * v x := by
    have hle := integral_mono_ae hforce habsforce
      (Filter.Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (le_abs_self (f x))
        (by rw [hφf]; exact mul_nonneg (sq_nonneg _) (le_max_right _ _)))
    simpa only [hφf, mul_assoc, v, u] using hle
  have hfinal : (∫ x in U, E x) ≤
      2 * κ⁻¹ * (∫ x in U, |f x| * η.toFun x ^ 2 * v x) +
        4 * κ⁻¹ ^ 2 * (∫ x in U, D x) := by
    apply (mul_le_mul_iff_right₀ (show 0 < κ / 2 by positivity)).mp
    calc
      _ ≤ (∫ x in U, f x * φ.toH1Function.toFun x) +
          2 * κ⁻¹ * (∫ x in U, D x) := hbound
      _ ≤ (∫ x in U, |f x| * η.toFun x ^ 2 * v x) +
          2 * κ⁻¹ * (∫ x in U, D x) := add_le_add hforce_le le_rfl
      _ = _ := by field_simp [hκ.ne']; ring
  exact hfinal



/-- The positive-level forcing product is a quadratic truncation energy,
even when the original eigenfunction is signed. -/
theorem abs_mul_positivePart {u k : ℝ} (hk : 0 ≤ k) :
    |u| * max (u - k) 0 = max (u - k) 0 ^ 2 + k * max (u - k) 0 := by
  by_cases hu : u ≤ k
  · rw [max_eq_right (sub_nonpos.mpr hu)]
    ring
  · have hku : k < u := lt_of_not_ge hu
    rw [abs_of_nonneg (hk.trans hku.le), max_eq_left (sub_nonneg.mpr hku.le)]
    ring

/-- Eigenfunction level energy from its actual weak variational equation.
The density and ellipticity bounds precede all eigenfunction data. In
particular, no global amplitude bound is used to control `λ ρ u`.
Both right-hand integrals are localized to the cutoff support set. -/
theorem eigenfunction_boundary_level_energy {d : ℕ} {U I O : Set (Vec d)}
    (hU : IsOpen U) (hO : MeasurableSet O) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    {k K : ℝ} (hk : 0 ≤ k) (η : QuantitativeSmoothCutoff I O K) :
    let v : Vec d → ℝ := fun x => max (w.toH1Function.toFun x - k) 0
    (∫ x in U, η.toFun x ^ 2 * vecNormSq
      ({y | k < w.toH1Function.toFun y}.indicator w.toH1Function.grad x)) ≤
      (2 * κ⁻¹ * eigenvalue * M + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        (∫ x in U ∩ O, v x ^ 2) +
      (2 * κ⁻¹ * eigenvalue * M * k) * (∫ x in U ∩ O, v x) := by
  classical
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let v : Vec d → ℝ := fun x => max (w.toH1Function.toFun x - k) 0
  change _ ≤ (2 * κ⁻¹ * eigenvalue * M + 4 * κ⁻¹ ^ 2 * K ^ 2) *
    (∫ x in U ∩ O, v x ^ 2) +
    (2 * κ⁻¹ * eigenvalue * M * k) * (∫ x in U ∩ O, v x)
  have hv : MemL2On U v := memL2On_positivePart_of_nonneg w.toH1Function hk
  have hv1 : IntegrableOn v U := hv.integrable (by norm_num)
  have hv2 : IntegrableOn (fun x => v x ^ 2) U := hv.integrable_sq
  have hq : IntegrableOn (fun x => v x ^ 2 + k * v x) U := hv2.add (hv1.const_mul k)
  have hρtop : MemLpOn U ⊤ ρ :=
    memLp_top_of_bound hρ M (by simpa only [Real.norm_eq_abs] using hρM)
  have hf : MemL2On U (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) := by
    have hprod : MemL2On U (fun x => w.toH1Function.toFun x * ρ x) :=
      w.toH1Function.memL2.fun_mul hρtop
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hprod.const_mul eigenvalue
  have hforce : (∫ x in U, |eigenvalue * ρ x * w.toH1Function.toFun x| *
      η.toFun x ^ 2 * v x) ≤
      eigenvalue * M * ((∫ x in U ∩ O, v x ^ 2) + k * ∫ x in U ∩ O, v x) := by
    have hle := integral_mono_of_nonneg (μ := volume.restrict U)
      (f := fun x => |eigenvalue * ρ x * w.toH1Function.toFun x| * η.toFun x ^ 2 * v x)
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _)) (le_max_right _ _))
      ((hq.const_mul (eigenvalue * M)).indicator hO) ?_
    · simpa only [integral_indicator hO, Measure.restrict_restrict hO,
        Set.inter_comm O U, integral_const_mul,
        integral_add (hv2.mono_set Set.inter_subset_left)
          ((hv1.mono_set Set.inter_subset_left).const_mul k)] using hle
    · filter_upwards [hρM] with x hρx
      by_cases hx : x ∈ O
      · rw [Set.indicator_of_mem hx]
        have hη : η.toFun x ^ 2 ≤ 1 := by
          simpa only [one_pow] using pow_le_pow_left₀ (η.nonneg x) (η.le_one x) 2
        have hq0 : 0 ≤ v x ^ 2 + k * v x :=
          add_nonneg (sq_nonneg _) (mul_nonneg hk (le_max_right _ _))
        calc
          _ = (eigenvalue * |ρ x| * (v x ^ 2 + k * v x)) * η.toFun x ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg hEigenvalue]
            have hid := abs_mul_positivePart (u := w.toH1Function.toFun x) hk
            change |w.toH1Function.toFun x| * v x = v x ^ 2 + k * v x at hid
            rw [← hid]
            ring
          _ ≤ (eigenvalue * M * (v x ^ 2 + k * v x)) * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hρx hEigenvalue) hq0) hη (sq_nonneg _)
              (mul_nonneg (mul_nonneg hEigenvalue hM) hq0)
          _ = _ := mul_one _
      · rw [Set.indicator_of_notMem hx, η.eq_zero_of_not_mem_outer hx,
          zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_mul]
  have hgrad : (∫ x in U, v x ^ 2 * vecNormSq (classicalGradient η.toFun x)) ≤
      K ^ 2 * ∫ x in U ∩ O, v x ^ 2 := by
    have hle := integral_mono_of_nonneg (μ := volume.restrict U)
      (f := fun x => v x ^ 2 * vecNormSq (classicalGradient η.toFun x))
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
      ((hv2.const_mul (K ^ 2)).indicator hO) ?_
    · simpa only [integral_indicator hO, Measure.restrict_restrict hO,
        Set.inter_comm O U, integral_const_mul] using hle
    · exact Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ O
        · rw [Set.indicator_of_mem hx]
          have hg : vecNormSq (classicalGradient η.toFun x) ≤ K ^ 2 := by
            rw [← vecEuclideanNorm_sq]
            exact pow_le_pow_left₀ (vecEuclideanNorm_nonneg _) (η.gradient_bound x) 2
          simpa only [mul_comm] using mul_le_mul_of_nonneg_left hg (sq_nonneg (v x))
        · rw [Set.indicator_of_notMem hx]
          change v x ^ 2 * vecNormSq (classicalGradient η.toFun x) ≤ 0
          rw [η.classicalGradient_eq_zero_of_not_mem_outer hx]
          simp only [vecNormSq, vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, le_refl]
  calc
    _ ≤ 2 * κ⁻¹ * (∫ x in U, |eigenvalue * ρ x * w.toH1Function.toFun x| *
        η.toFun x ^ 2 * v x) +
        4 * κ⁻¹ ^ 2 * (∫ x in U, v x ^ 2 * vecNormSq (classicalGradient η.toFun x)) :=
      l2_forced_boundary_level_caccioppoli hU hfin hκ hA w _ hf hw hk η
    _ ≤ 2 * κ⁻¹ * (eigenvalue * M *
        ((∫ x in U ∩ O, v x ^ 2) + k * ∫ x in U ∩ O, v x)) +
        4 * κ⁻¹ ^ 2 * (K ^ 2 * ∫ x in U ∩ O, v x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hforce (by positivity))
        (mul_le_mul_of_nonneg_left hgrad (by positivity))
    _ = _ := by ring

/-- The inner-ball energy of the actual zero extension is bounded by the
original-domain cutoff energy. No differential equation is needed here. -/
theorem zero_extended_level_energy_le_cutoff {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V)
    (w : Homogenization.H10Function U)
    (k : ℝ) {O : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff V O K) :
    (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) ≤
      ∫ x in U, η.toFun x ^ 2 * vecNormSq (posPartGrad w.toH1Function k x) := by
  classical
  let u := w.toH1Function
  let e := fun x => vecNormSq (posPartGrad u k x)
  let eη := fun x => η.toFun x ^ 2 * e x
  have hηtop : MemLpOn U ⊤ η.toFun :=
    DGNM.memLpOn_top_of_contDiff η.smooth η.hasCompactSupport
  have hEvec : MemVectorL2On U (fun x => η.toFun x • posPartGrad u k x) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using
      (posPartGrad_gradMemL2 u k i).fun_mul hηtop
  have hEint : IntegrableOn eη U := by
    simpa only [eη, e, PDE.vecNormSq_smul] using integrableOn_vecNormSq_of_memVectorL2On hEvec
  have hlocal : (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) =
      ∫ x in V, U.indicator eη x := by
    apply setIntegral_congr_fun hV.measurableSet
    intro x hx
    change vecNormSq ({y | k < U.indicator u.toFun y}.indicator
      (U.indicator u.grad) x) = U.indicator eη x
    by_cases hxU : x ∈ U <;>
      simp [Set.indicator_apply, Set.mem_ofPred_eq, hxU, eη, e, posPartGrad,
        η.eq_one_on_inner x hx, vecNormSq, vecDot]
  calc
    _ = ∫ x in V, U.indicator eη x := hlocal
    _ = ∫ x in U, V.indicator eη x := by
      rw [integral_indicator hU.measurableSet, integral_indicator hV.measurableSet,
        Measure.restrict_restrict hU.measurableSet,
        Measure.restrict_restrict hV.measurableSet, Set.inter_comm]
    _ = ∫ x in V, eη x ∂(volume.restrict U) := integral_indicator hV.measurableSet
    _ ≤ ∫ x in U, eη x := setIntegral_le_integral hEint
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))


/-- Raising the level controls both eigenfunction forcing terms by the
quadratic energy at the preceding level. The level ratio is explicit. -/
theorem positivePart_sq_add_level_mul_le {u k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) :
    max (u - l) 0 ^ 2 + l * max (u - l) 0 ≤
      (l / (l - k)) * max (u - k) 0 ^ 2 := by
  have hl : 0 ≤ l := hk.trans hkl.le
  have hgap : 0 < l - k := sub_pos.mpr hkl
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hgap).mpr
  by_cases hu : u ≤ l
  · rw [max_eq_right (sub_nonpos.mpr hu)]
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, zero_mul]
    exact mul_nonneg hl (sq_nonneg _)
  · have hlu : l < u := lt_of_not_ge hu
    rw [max_eq_left (sub_nonneg.mpr hlu.le),
      max_eq_left (sub_nonneg.mpr (hkl.trans hlu).le)]
    nlinarith only [mul_nonneg hk (sq_nonneg (u - l)),
      mul_nonneg (mul_nonneg hl hgap.le) (sub_nonneg.mpr hlu.le),
      mul_nonneg hl (sq_nonneg (l - k))]

/-- A normalized weighted eigenfunction has a uniform unweighted L² bound.
Only the actual density bounds and weighted normalization are used. -/
theorem integral_sq_le_of_weighted_normalization {d : ℕ} {U : Set (Vec d)}
    {κ M : ℝ} (hκ : 0 < κ) {ρ u : Vec d → ℝ}
    (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρlower : ∀ᵐ x ∂(volume.restrict U), κ ≤ ρ x)
    (hρupper : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (hu : MemL2On U u) (hnorm : (∫ x in U, ρ x * u x ^ 2) = 1) :
    (∫ x in U, u x ^ 2) ≤ κ⁻¹ := by
  have hweighted : IntegrableOn (fun x => ρ x * u x ^ 2) U := by
    simpa only [IntegrableOn, volumeOn, mul_comm] using hu.integrable_sq.bdd_mul hρ
      (by simpa only [Real.norm_eq_abs] using hρupper)
  have hbound := integral_mono_ae (hu.integrable_sq.const_mul κ) hweighted
    (hρlower.mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg (u x)))
  rw [integral_const_mul, hnorm] at hbound
  rw [← one_div]
  exact (le_div_iff₀ hκ).mpr (by simpa only [mul_comm] using hbound)

/-- The eigenfunction level energy estimate passes to the genuine zero
extension on any inner open set, including balls meeting the boundary. -/
theorem eigenfunction_zero_extended_level_energy {d : ℕ} {U V O : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hO : MeasurableSet O) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    {k K : ℝ} (hk : 0 ≤ k) (η : QuantitativeSmoothCutoff V O K) :
    let v : Vec d → ℝ := fun x => max (w.toH1Function.toFun x - k) 0
    (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) k x)) ≤
      (2 * κ⁻¹ * eigenvalue * M + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        (∫ x in U ∩ O, v x ^ 2) +
      (2 * κ⁻¹ * eigenvalue * M * k) * (∫ x in U ∩ O, v x) := by
  exact (zero_extended_level_energy_le_cutoff hU hV w k η).trans
    (eigenfunction_boundary_level_energy hU hO hfin hκ hM hA hρ hρM w hEigenvalue hw hk η)


/-- A genuine two-level recurrence for the same zero-trace eigenfunction.
The higher-level gradient energy depends only on the lower-level quadratic
tail. Its eigenvalue and cutoff-radius factors remain explicit. -/
theorem eigenfunction_zero_extended_two_level_energy {d : ℕ} {U V O : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (hO : MeasurableSet O) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    {k l K : ℝ} (hk : 0 ≤ k) (hkl : k < l) (η : QuantitativeSmoothCutoff V O K) :
    (∫ x in V, vecNormSq (posPartGrad (zeroExtCube hU hV w) l x)) ≤
      (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        ∫ x in U ∩ O, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  let : IsFiniteMeasure (volumeOn U) :=
    ⟨by simpa only [volumeOn, Measure.restrict_apply_univ] using hfin.lt_top⟩
  let vk : Vec d → ℝ := fun x => max (w.toH1Function.toFun x - k) 0
  let vl : Vec d → ℝ := fun x => max (w.toH1Function.toFun x - l) 0
  have hl : 0 ≤ l := hk.trans hkl.le
  have hvk : MemL2On U vk := memL2On_positivePart_of_nonneg w.toH1Function hk
  have hvl : MemL2On U vl := memL2On_positivePart_of_nonneg w.toH1Function hl
  have hvk2U : IntegrableOn (fun x => vk x ^ 2) U := hvk.integrable_sq
  have hvl2U : IntegrableOn (fun x => vl x ^ 2) U := hvl.integrable_sq
  have hvl1U : IntegrableOn vl U := hvl.integrable (by norm_num)
  have hvk2 : IntegrableOn (fun x => vk x ^ 2) (U ∩ O) :=
    hvk2U.mono_set Set.inter_subset_left
  have hvl2 : IntegrableOn (fun x => vl x ^ 2) (U ∩ O) :=
    hvl2U.mono_set Set.inter_subset_left
  have hvl1 : IntegrableOn vl (U ∩ O) :=
    hvl1U.mono_set Set.inter_subset_left
  have hsq : (∫ x in U ∩ O, vl x ^ 2) ≤ ∫ x in U ∩ O, vk x ^ 2 := by
    apply integral_mono_ae hvl2 hvk2
    exact Filter.Eventually.of_forall fun x =>
      pow_le_pow_left₀ (le_max_right _ _)
        (max_le_max (sub_le_sub_left hkl.le _) le_rfl) 2
  have hforce : (∫ x in U ∩ O, vl x ^ 2) + l * (∫ x in U ∩ O, vl x) ≤
      (l / (l - k)) * ∫ x in U ∩ O, vk x ^ 2 := by
    rw [← integral_const_mul, ← integral_add hvl2 (hvl1.const_mul l),
      ← integral_const_mul]
    exact integral_mono_ae (hvl2.add (hvl1.const_mul l))
      (hvk2.const_mul (l / (l - k)))
      (Filter.Eventually.of_forall fun _ => positivePart_sq_add_level_mul_le hk hkl)
  calc
    _ ≤ (2 * κ⁻¹ * eigenvalue * M + 4 * κ⁻¹ ^ 2 * K ^ 2) *
        (∫ x in U ∩ O, vl x ^ 2) +
        (2 * κ⁻¹ * eigenvalue * M * l) * (∫ x in U ∩ O, vl x) :=
      eigenfunction_zero_extended_level_energy hU hV hO hfin hκ hM hA hρ hρM w
        hEigenvalue hw hl η
    _ = (2 * κ⁻¹ * eigenvalue * M) *
        ((∫ x in U ∩ O, vl x ^ 2) + l * (∫ x in U ∩ O, vl x)) +
        (4 * κ⁻¹ ^ 2 * K ^ 2) * (∫ x in U ∩ O, vl x ^ 2) := by ring
    _ ≤ (2 * κ⁻¹ * eigenvalue * M) *
        ((l / (l - k)) * ∫ x in U ∩ O, vk x ^ 2) +
        (4 * κ⁻¹ ^ 2 * K ^ 2) * (∫ x in U ∩ O, vk x ^ 2) :=
      add_le_add (mul_le_mul_of_nonneg_left hforce (by positivity))
        (mul_le_mul_of_nonneg_left hsq (by positivity))
    _ = _ := by ring

/-- Concentric Euclidean balls give the exact inverse-square radius gap in
the two-level recurrence. The balls may meet the original boundary. -/
theorem eigenfunction_zero_extended_ball_two_level_energy {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec d) {r s k l : ℝ} (hr : 0 ≤ r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) :
    (∫ x in euclideanBall z r, vecNormSq
      (posPartGrad (zeroExtCube hU (isOpen_euclideanBall z r) w) l x)) ≤
      (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
        4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) *
        ∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  exact eigenfunction_zero_extended_two_level_energy hU (isOpen_euclideanBall z r)
    (isOpen_euclideanBall z s).measurableSet hfin hκ hM hA hρ hρM w hEigenvalue hw
    hk hkl (quantitativeBallCutoff z hr hrs)

/-- Negating an actual eigenfunction preserves its eigenvalue and density.
Thus the level estimates also apply to its negative tail. -/
theorem eigenfunction_weak_solution_neg {d : ℕ} {U : Set (Vec d)}
    {A : CoeffField d} {ρ : Vec d → ℝ} (w : Homogenization.H10Function U)
    {eigenvalue : ℝ}
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0)) :
    IsWeakSolutionOn A U (-w).toH1Function
      (fun x => eigenvalue * ρ x * (-w).toH1Function.toFun x) (fun _ => 0) := by
  simpa only [h10_neg_toH1Function, Homogenization.H1Function.neg_toFun,
    mul_neg, neg_zero] using weak_solution_neg hw

/-- Weighted normalization bounds every positive-level boundary-ball energy
without a supremum premise. This is an energy bound, before the Sobolev and
level iteration needed to obtain an amplitude estimate. -/
theorem normalized_eigenfunction_zero_extended_ball_level_energy
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρlower : ∀ᵐ x ∂(volume.restrict U), κ ≤ ρ x)
    (hρupper : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in U, ρ x * w.toH1Function.toFun x ^ 2) = 1)
    (z : Vec d) {r s l : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hl : 0 < l) :
    (∫ x in euclideanBall z r, vecNormSq
      (posPartGrad (zeroExtCube hU (isOpen_euclideanBall z r) w) l x)) ≤
      (2 * κ⁻¹ * eigenvalue * M + 4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) * κ⁻¹ := by
  have hu2 : IntegrableOn (fun x => w.toH1Function.toFun x ^ 2) U :=
    w.toH1Function.memL2.integrable_sq
  have hv2 : IntegrableOn (fun x => max (w.toH1Function.toFun x - 0) 0 ^ 2) U :=
    (memL2On_positivePart_of_nonneg w.toH1Function (le_refl 0)).integrable_sq
  have htail : (∫ x in U ∩ euclideanBall z s,
      max (w.toH1Function.toFun x - 0) 0 ^ 2) ≤ ∫ x in U, w.toH1Function.toFun x ^ 2 := by
    calc
      _ ≤ ∫ x in U ∩ euclideanBall z s, w.toH1Function.toFun x ^ 2 := by
        apply integral_mono_ae (hv2.mono_set Set.inter_subset_left)
          (hu2.mono_set Set.inter_subset_left)
        exact Filter.Eventually.of_forall fun x => by
          have hx : max (w.toH1Function.toFun x - 0) 0 ≤ |w.toH1Function.toFun x| :=
            max_le (by simpa only [sub_zero] using le_abs_self (w.toH1Function.toFun x))
              (abs_nonneg _)
          simpa only [sq_abs] using pow_le_pow_left₀ (le_max_right _ _) hx 2
      _ ≤ _ := setIntegral_mono_set hu2
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall fun _ hx => hx.1)
  have hnormbound := integral_sq_le_of_weighted_normalization hκ hρ hρlower hρupper
    w.toH1Function.memL2 hnorm
  have he := eigenfunction_zero_extended_ball_two_level_energy hU hfin hκ hM hA hρ
    hρupper w hEigenvalue hw z hr hrs (le_refl 0) hl
  simp only [sub_zero, div_self (ne_of_gt hl), mul_one] at he
  have htailbound : (∫ x in U ∩ euclideanBall z s,
      max (w.toH1Function.toFun x) 0 ^ 2) ≤ κ⁻¹ := by
    simpa only [sub_zero] using htail.trans hnormbound
  exact he.trans (mul_le_mul_of_nonneg_left htailbound (by positivity))

/-- Transfer an actual supported smooth approximation to the compatible
Homogenization carrier, preserving both representatives exactly. -/
def h10ToHomogenization {d : ℕ} {U : Set (Vec d)}
    (v : PDE.H10Function U) : Homogenization.H10Function U where
  toH1Function :=
    { toFun := v.toH1Function.toFun
      grad := v.toH1Function.grad
      memL2 := v.toH1Function.memL2
      gradMemL2 := v.toH1Function.gradMemL2
      hasWeakGradient := v.toH1Function.hasWeakGradient }
  approx := v.approx
  approx_smooth := v.approx_smooth
  approx_hasCompactSupport := v.approx_hasCompactSupport
  approx_support_subset := v.approx_support_subset
  tendsto_approx := v.tendsto_approx
  tendsto_approx_grad := v.tendsto_approx_grad

/-- Add the positive regularization without changing the weak gradient. -/
noncomputable def regularizedH1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U)
    (ε : ℝ) : PDE.H1Function U := by
  letI := hU.isFiniteMeasure_volumeOn
  exact (h1FromHomogenization u).addConst ε

@[simp]
theorem regularizedH1_toFun {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U) (ε : ℝ) :
    (regularizedH1 hU u ε).toFun = fun x => u.toFun x + ε := rfl

@[simp]
theorem regularizedH1_grad {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U) (ε : ℝ) :
    (regularizedH1 hU u ε).grad = u.grad := by
  letI := hU.isFiniteMeasure_volumeOn
  funext x
  exact PDE.H1Function.grad_addConst (h1FromHomogenization u) ε x

/-- The denominator bound is derived from nonnegativity, for every positive
regularization; no positive lower bound for the eigenfunction is assumed. -/
theorem regularizedH1_lower {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x) (ε : ℝ) :
    ∀ᵐ x ∂volumeOn U, ε ≤ regularizedH1 hU u ε x := by
  filter_upwards [hu] with x hx
  change ε ≤ u.toFun x + ε
  exact le_add_of_nonneg_left hx

/-- Genuine weak chain rule for the regularized logarithm. The chosen
Euclidean gradient is literal, so its square is integrable. -/
theorem exists_regularized_log_h1 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : PDE.H1Function U,
      v.toFun = (fun x => Real.log (u.toFun x + ε)) ∧
      v.grad = (fun x => (u.toFun x + ε)⁻¹ • u.grad x) := by
  refine ⟨DGNM.logOfLowerBound hU (regularizedH1 hU u ε) hε
    (regularizedH1_lower hU u hu ε), rfl, ?_⟩
  simp only [DGNM.logOfLowerBound_grad, regularizedH1_grad]
  rfl

/-- The reciprocal test `η²/(u+ε)` belongs to the actual zero-trace
Sobolev space. This includes the supported smooth approximation, rather
than positing admissibility of a formal test gradient. -/
theorem exists_regularized_reciprocal_test {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x) {ε : ℝ} (hε : 0 < ε)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    ∃ φ : Homogenization.H10Function U,
      φ.toH1Function.toFun = (fun x => η x ^ 2 * (u.toFun x + ε)⁻¹) ∧
      φ.toH1Function.grad = (fun x =>
        (-(η x ^ 2) * ((u.toFun x + ε) ^ 2)⁻¹) • u.grad x +
          (2 * η x * (u.toFun x + ε)⁻¹) • classicalGradient η x) := by
  let v := DGNM.invOfLowerBound hU (regularizedH1 hU u ε) hε
    (regularizedH1_lower hU u hu ε)
  let φ := v.mulContDiffHasCompactSupportToH10 hU (DGNM.contDiff_sq hη)
    (DGNM.hasCompactSupport_sq hηc) (DGNM.tsupport_sq_subset hηU)
  refine ⟨h10ToHomogenization φ, rfl, ?_⟩
  change φ.toH1Function.grad = _
  rw [PDE.H1Function.mulContDiffHasCompactSupportToH10_grad]
  simp only [v, DGNM.invOfLowerBound_grad, regularizedH1_grad,
    DGNM.classicalGradient_sq hη]
  funext x i
  change η x ^ 2 * (-((u.toFun x + ε) ^ 2)⁻¹ * u.grad x i) +
    (u.toFun x + ε)⁻¹ * (2 * η x * classicalGradient η x i) = _
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Pointwise logarithmic absorption for an anisotropic matrix. The
reciprocal-test flux remains on the left with its actual sign. -/
theorem regularized_log_test_pointwise_bound {d : ℕ} {κ t η : ℝ}
    {A : Mat d} (hA : IsEllipticMatrix κ κ⁻¹ A) (g ζ : Vec d) :
    (κ / 2) * (η ^ 2 * vecNormSq (t⁻¹ • g)) +
      vecDot (matVecMul A g)
        ((-(η ^ 2) * (t ^ 2)⁻¹) • g + (2 * η * t⁻¹) • ζ) ≤
      2 * κ⁻¹ * vecNormSq ζ := by
  have hcross := elliptic_cutoff_cross_bound (η := η) (v := 1) hA (t⁻¹ • g) ζ
  have hcoer := mul_le_mul_of_nonneg_left (hA.coercive (t⁻¹ • g)) (sq_nonneg η)
  have hflux : vecDot (matVecMul A g)
        ((-(η ^ 2) * (t ^ 2)⁻¹) • g + (2 * η * t⁻¹) • ζ) =
      -(η ^ 2 * vecDot (t⁻¹ • g) (matVecMul A (t⁻¹ • g))) +
        2 * η * vecDot (matVecMul A (t⁻¹ • g)) ζ := by
    simp only [DGNM.vecDot_add_right, DGNM.vecDot_smul_right, DGNM.matVecMul_smul,
      DGNM.vecDot_smul_left, inv_pow]
    rw [vecDot_comm g (matVecMul A g)]
    ring
  rw [hflux]
  simp only [mul_one, one_pow] at hcross
  have hcross' := (le_abs_self (2 * η * vecDot (matVecMul A (t⁻¹ • g)) ζ)).trans hcross
  nlinarith only [hcoer, hcross']

/-- Logarithmic Caccioppoli with the actual forcing retained. Its test is
constructed in `H¹₀`; the logarithmic gradient is a genuine weak gradient.
No positive lower bound on `u`, nor any bound on `f`, is required. -/
theorem regularized_log_energy_with_forcing {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {κ : ℝ}
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x) (f : Vec d → ℝ)
    (hf : MemL2On U f) (hw : IsWeakSolutionOn A U u f (fun _ => 0))
    {ε : ℝ} (hε : 0 < ε) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
      vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) U ∧
    IntegrableOn (fun x => f x * η x ^ 2 * (u.toFun x + ε)⁻¹) U ∧
    (κ / 2) * (∫ x in U, η x ^ 2 *
      vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) +
      (∫ x in U, f x * η x ^ 2 * (u.toFun x + ε)⁻¹) ≤
      2 * κ⁻¹ * (∫ x in U, vecNormSq (classicalGradient η x)) := by
  obtain ⟨v, -, hvg⟩ := exists_regularized_log_h1 hU u hu hε
  obtain ⟨φ, hφf, hφg⟩ := exists_regularized_reciprocal_test hU u hu hε hη hηc hηU
  have hηtop : MemLpOn U ⊤ η := DGNM.memLpOn_top_of_contDiff hη hηc
  have hEvec : MemVectorL2On U (fun x => η x • ((u.toFun x + ε)⁻¹ • u.grad x)) := by
    intro i
    have hi : MemL2On U (fun x => v.grad x i * η x) := (v.gradMemL2 i).fun_mul hηtop
    rw [hvg] at hi
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hi
  have hE : IntegrableOn (fun x => η x ^ 2 *
      vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) U := by
    simpa only [PDE.vecNormSq_smul] using
      integrableOn_vecNormSq_of_memVectorL2On hEvec
  have hD := integrableOn_vecNormSq_of_memVectorL2On
    (DGNM.memVectorL2On_classicalGradient (U := U) hη hηc)
  have hF := integrableOn_mul_of_memL2On hf φ.toH1Function.memL2
  rw [hφf] at hF
  simp only [← mul_assoc] at hF
  have hflux := integrableOn_vecDot_of_memVectorL2On
    (memVectorL2On_matVecMul_of_isEllipticFieldOn hA u.gradMemL2)
    φ.toH1Function.gradMemL2
  have hp : ∀ᵐ x ∂volumeOn U,
      (κ / 2) * (η x ^ 2 * vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) +
        vecDot (matVecMul (A x) (u.grad x)) (φ.toH1Function.grad x) ≤
        2 * κ⁻¹ * vecNormSq (classicalGradient η x) := by
    filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    rw [hφg]
    exact regularized_log_test_pointwise_bound (hA.elliptic hx) _ _
  have hb := integral_mono_ae ((hE.const_mul (κ / 2)).add hflux)
    (hD.const_mul (2 * κ⁻¹)) hp
  dsimp only [Pi.add_apply] at hb
  rw [integral_add (hE.const_mul (κ / 2)) hflux, integral_const_mul,
    integral_const_mul] at hb
  have heq := hw φ
  simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at heq
  change (∫ x in U, vecDot (matVecMul (A x) (u.grad x))
    (φ.toH1Function.grad x)) = (∫ x in U, f x * φ.toH1Function.toFun x) at heq
  rw [heq, hφf] at hb
  exact ⟨hE, hF, by simpa only [← mul_assoc] using hb⟩

/-- The actual weighted eigenvalue term is retained in the logarithmic
estimate, for each regularization. The bound is uniform in that parameter. -/
theorem eigenfunction_regularized_log_energy {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {κ : ℝ}
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x)
    {ρ : Vec d → ℝ} {M eigenvalue : ℝ}
    (hρ : AEStronglyMeasurable ρ (volumeOn U))
    (hρbound : ∀ᵐ x ∂volumeOn U, |ρ x| ≤ M)
    (hw : IsWeakSolutionOn A U u (fun x => eigenvalue * ρ x * u.toFun x) (fun _ => 0))
    {ε : ℝ} (hε : 0 < ε) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    IntegrableOn (fun x => η x ^ 2 *
      vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) U ∧
    IntegrableOn (fun x => eigenvalue * ρ x * u.toFun x * η x ^ 2 *
      (u.toFun x + ε)⁻¹) U ∧
    (κ / 2) * (∫ x in U, η x ^ 2 *
      vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) +
      (∫ x in U, eigenvalue * ρ x * u.toFun x * η x ^ 2 * (u.toFun x + ε)⁻¹) ≤
      2 * κ⁻¹ * (∫ x in U, vecNormSq (classicalGradient η x)) := by
  have hρtop : MemLpOn U ⊤ ρ :=
    memLp_top_of_bound hρ M (by simpa only [Real.norm_eq_abs] using hρbound)
  have hf : MemL2On U (fun x => eigenvalue * ρ x * u.toFun x) := by
    have hp : MemL2On U (fun x => u.toFun x * ρ x) := u.memL2.fun_mul hρtop
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hp.const_mul eigenvalue
  exact regularized_log_energy_with_forcing hU hA u hu _ hf hw hε hη hηc hηU

/-- Euclidean logarithmic Caccioppoli for a nonnegative weighted
eigenfunction. The constant depends only on ellipticity, not on the
eigenvalue, weight, eigenfunction, or regularization. -/
theorem eigenfunction_regularized_log_energy_euclidean {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {κ : ℝ} (hκ : 0 < κ)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x)
    {ρ : Vec d → ℝ} {M eigenvalue : ℝ}
    (hρ : AEStronglyMeasurable ρ (volumeOn U))
    (hρbound : ∀ᵐ x ∂volumeOn U, |ρ x| ≤ M)
    (hρnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x) (heigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U u (fun x => eigenvalue * ρ x * u.toFun x) (fun _ => 0))
    {ε : ℝ} (hε : 0 < ε) {η : Vec d → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηU : tsupport η ⊆ U) :
    (∫ x in U, η x ^ 2 * vecNormSq ((u.toFun x + ε)⁻¹ • u.grad x)) ≤
      4 * κ⁻¹ ^ 2 * (∫ x in U, vecNormSq (classicalGradient η x)) := by
  obtain ⟨-, -, hb⟩ := eigenfunction_regularized_log_energy hU hA u hu hρ hρbound
    hw hε hη hηc hηU
  have hforce : 0 ≤ ∫ x in U, eigenvalue * ρ x * u.toFun x * η x ^ 2 *
      (u.toFun x + ε)⁻¹ := by
    apply integral_nonneg_of_ae
    filter_upwards [hu, hρnonneg] with x hx hρx
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg heigenvalue hρx) hx)
      (sq_nonneg _)) (inv_nonneg.mpr (by linarith))
  apply (mul_le_mul_iff_right₀ (show 0 < κ / 2 by positivity)).mp
  calc
    _ ≤ 2 * κ⁻¹ * ∫ x in U, vecNormSq (classicalGradient η x) := by linarith only [hb, hforce]
    _ = _ := by field_simp [hκ.ne']; ring

/-- Absolute values are admissible in the actual zero-trace space. The
gradient representative is identified a.e., including the zero level. -/
theorem exists_abs_h10 {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) (w : Homogenization.H10Function U) :
    ∃ v : Homogenization.H10Function U,
      v.toH1Function.toFun = (fun x => |w.toH1Function.toFun x|) ∧
      ∀ᵐ x ∂volumeOn U, v.toH1Function.grad x =
        if 0 < w.toH1Function.toFun x then w.toH1Function.grad x else -w.toH1Function.grad x := by
  let p₀ := positivePartOpen hU w.toH1Function 0
    (memL2On_positivePart_of_nonneg w.toH1Function (le_refl 0))
  obtain ⟨p, hp⟩ := SuperdiffusionCLT.Section7.memH10_positivePart hU hfin w (le_refl 0)
  have hpg : ∀ᵐ x ∂volumeOn U, ∀ i, p.toH1Function.grad x i = p₀.grad x i :=
    ae_all_iff.mpr (fun i => Homogenization.gradCoord_ae_eq_of_toFun_eq hU
      p.toH1Function p₀ hp i)
  let v : Homogenization.H10Function U := (2 : ℝ) • p - w
  refine ⟨v, ?_, ?_⟩
  · change (fun x => 2 * p.toH1Function.toFun x + (-1) * w.toH1Function.toFun x) = _
    rw [hp]
    funext x
    change 2 * max (w.toH1Function.toFun x - 0) 0 + (-1) * w.toH1Function.toFun x = _
    rcases le_total 0 (w.toH1Function.toFun x) with hx | hx
    · rw [sub_zero, max_eq_left hx, abs_of_nonneg hx]; ring
    · rw [sub_zero, max_eq_right hx, abs_of_nonpos hx]; ring
  · filter_upwards [hpg] with x hx
    funext i
    change 2 * p.toH1Function.grad x i + (-1) * w.toH1Function.grad x i = _
    rw [hx i]
    by_cases hpos : 0 < w.toH1Function.toFun x
    · simp [p₀, positivePartOpen, posPartGrad, hpos]; ring
    · simp [p₀, positivePartOpen, posPartGrad, hpos]

/-- Absolute-value replacement preserves every weighted square norm and
the actual anisotropic Dirichlet energy. Thus it preserves a variational
minimum whenever that minimum has been established for the input. This
does not assert that an arbitrary eigenfunction is a first eigenfunction. -/
theorem exists_abs_h10_preserving_energy {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (hfin : volume U ≠ ⊤) (w : Homogenization.H10Function U) :
    ∃ v : Homogenization.H10Function U,
      v.toH1Function.toFun = (fun x => |w.toH1Function.toFun x|) ∧
      (∀ x, 0 ≤ v.toH1Function.toFun x) ∧
      (∀ ρ : Vec d → ℝ, (∫ x in U, ρ x * v.toH1Function.toFun x ^ 2) =
        ∫ x in U, ρ x * w.toH1Function.toFun x ^ 2) ∧
      (∀ A : CoeffField d, (∫ x in U, vecDot (v.toH1Function.grad x)
          (matVecMul (A x) (v.toH1Function.grad x))) =
        ∫ x in U, vecDot (w.toH1Function.grad x) (matVecMul (A x) (w.toH1Function.grad x))) := by
  obtain ⟨v, hv, hvg⟩ := exists_abs_h10 hU hfin w
  refine ⟨v, hv, (fun x => by rw [hv]; exact abs_nonneg _), ?_, ?_⟩
  · intro ρ
    simp only [hv, sq_abs]
  · intro A
    apply integral_congr_ae
    filter_upwards [hvg] with x hx
    rw [hx]
    split_ifs with hpos
    · rfl
    · rw [show -w.toH1Function.grad x = (-1 : ℝ) • w.toH1Function.grad x by simp]
      simp only [DGNM.matVecMul_smul, DGNM.vecDot_smul_left, DGNM.vecDot_smul_right]
      ring

/-- Denominator and quotient bounds used uniformly in the positive
regularization. In particular the source eigenvalue term is dominated
without any lower bound for the eigenfunction. -/
theorem regularized_quotient_bounds {t ε : ℝ} (ht : 0 ≤ t) (hε : 0 < ε) :
    0 < t + ε ∧ 0 ≤ t * (t + ε)⁻¹ ∧ t * (t + ε)⁻¹ ≤ 1 := by
  have hden : 0 < t + ε := by positivity
  refine ⟨hden, mul_nonneg ht (inv_nonneg.mpr hden.le), ?_⟩
  rw [← div_eq_mul_inv]
  exact (div_le_one hden).mpr (by linarith)

/-- The regularized quotient converges to the positive-set indicator;
there is no implicit assumption that the zero set is negligible. -/
theorem regularized_quotient_tendsto {t : ℝ} (ht : 0 ≤ t) {ε : ℕ → ℝ}
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => t * (t + ε n)⁻¹) Filter.atTop
      (nhds (if 0 < t then (1 : ℝ) else 0)) := by
  by_cases hpos : 0 < t
  · have hsum : Filter.Tendsto (fun n => t + ε n) Filter.atTop (nhds t) := by
      simpa only [add_zero] using tendsto_const_nhds.add hε
    simpa only [hpos, ite_true, mul_inv_cancel₀ hpos.ne'] using
      ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => t) Filter.atTop (nhds t)).mul
        (hsum.inv₀ hpos.ne'))
  · have ht0 : t = 0 := le_antisymm (not_lt.mp hpos) ht
    simpa only [ht0, zero_mul, lt_self_iff_false, ite_false] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))

/-- Dominated-convergence bookkeeping for the regularized source term.
The integrable coefficient can be signed. On the zero set the limit is
zero, rather than the coefficient itself. -/
theorem regularized_quotient_integral_tendsto {d : ℕ} {U : Set (Vec d)}
    (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x)
    {b : Vec d → ℝ} (hb : IntegrableOn b U) {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, b x * (u.toFun x * (u.toFun x + ε n)⁻¹))
      Filter.atTop (nhds (∫ x in U, if 0 < u.toFun x then b x else 0)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => |b x|) ?_ ?_ ?_ ?_
  · intro n
    exact (hb.aestronglyMeasurable.aemeasurable.mul
      (u.memL2.aemeasurable.mul (u.memL2.aemeasurable.add aemeasurable_const).inv)).aestronglyMeasurable
  · simpa only [Real.norm_eq_abs] using hb.norm
  · intro n
    filter_upwards [hu] with x hx
    obtain ⟨-, hq0, hq1⟩ := regularized_quotient_bounds hx (hεpos n)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq0, mul_one] using
      (mul_le_mul_of_nonneg_left hq1 (abs_nonneg (b x)))
  · filter_upwards [hu] with x hx
    simpa only [mul_ite, mul_one, mul_zero] using
      (tendsto_const_nhds.mul (regularized_quotient_tendsto hx hε))

/-- The actual weighted eigenvalue term has its justified regularization
limit. A positive ground-state theorem is needed to remove the indicator. -/
theorem eigenfunction_regularized_log_forcing_tendsto {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (u : Homogenization.H1Function U)
    (hu : ∀ᵐ x ∂volumeOn U, 0 ≤ u.toFun x)
    {ρ : Vec d → ℝ} {M eigenvalue : ℝ}
    (hρ : AEStronglyMeasurable ρ (volumeOn U))
    (hρbound : ∀ᵐ x ∂volumeOn U, |ρ x| ≤ M)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n)
    (hε : Filter.Tendsto ε Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U,
      eigenvalue * ρ x * u.toFun x * η x ^ 2 * (u.toFun x + ε n)⁻¹)
      Filter.atTop (nhds (∫ x in U, if 0 < u.toFun x then eigenvalue * ρ x * η x ^ 2 else 0)) := by
  letI := hU.isFiniteMeasure_volumeOn
  have hρtop : MemLpOn U ⊤ ρ :=
    memLp_top_of_bound hρ M (by simpa only [Real.norm_eq_abs] using hρbound)
  have hρ2 : MemL2On U ρ := hρtop.mono_exponent (by simp)
  have hη2 : MemL2On U (fun x => η x ^ 2) :=
    ((DGNM.contDiff_sq hη).continuous.memLp_of_hasCompactSupport
      (DGNM.hasCompactSupport_sq hηc)).restrict U
  have hb : IntegrableOn (fun x => eigenvalue * ρ x * η x ^ 2) U :=
    integrableOn_mul_of_memL2On (hρ2.const_mul eigenvalue) hη2
  have ht := regularized_quotient_integral_tendsto u hu hb hεpos hε
  convert ht using 1
  congr 1
  funext n
  congr 1
  funext x
  ring

/-- Lower the exponent of the actual value and native weak gradient on a
finite-volume domain. Neither representative changes. -/
def h1ToSubcritical {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeOn U)] (u : PDE.H1Function U)
    {p : ℝ} (hp : p ≤ 2) : W1pFunction U (ENNReal.ofReal p) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2.mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hp)
  gradMemLp := fun i => (u.gradMemL2 i).mono_exponent
    (by simpa using ENNReal.ofReal_le_ofReal hp)
  hasWeakGradient := u.hasWeakGradient

/-- Finite-volume Holder comparison passes actual L2 convergence to any
positive subcritical exponent. -/
theorem tendsto_eLpNorm_subcritical {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeOn U)] {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2)
    {F : ℕ → Vec d → ℝ}
    (hF : Filter.Tendsto (fun n => eLpNorm (F n) 2 (volumeOn U))
      Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => eLpNorm (F n) (ENNReal.ofReal p) (volumeOn U))
      Filter.atTop (𝓝 0) := by
  let C : ℝ≥0∞ := (volumeOn U) Set.univ ^ (1 / p - 1 / 2)
  have hC : C ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg
    (sub_nonneg.mpr (one_div_le_one_div_of_le hp hp2)) (measure_ne_top _ _)
  have hu : Filter.Tendsto
      (fun n => eLpNorm (F n) 2 (volumeOn U) * C) Filter.atTop (𝓝 0) := by
    simpa only [zero_mul] using ENNReal.Tendsto.mul_const hF (Or.inr hC)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hu (fun _ => bot_le)
  intro n
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
    (q := ENNReal.ofReal (2 : ℝ)) (ENNReal.ofReal_le_ofReal hp2)
    (ENNReal.ofReal_pos.mpr hp) (f := F n) (μ := volumeOn U)
  convert hb using 1 <;> norm_num [C, ENNReal.toReal_ofReal hp.le]

/-- The same supported smooth approximants give subcritical zero trace;
this explicitly supplies the Sobolev theorem's approximation obligation. -/
def h10SubcriticalApproximation {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volumeOn U)] (u : PDE.H10Function U)
    {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (h1ToSubcritical u.toH1Function hp2).SupportedSmoothApproximation where
  approx := u.approx
  approx_smooth := u.approx_smooth
  approx_hasCompactSupport := u.approx_hasCompactSupport
  approx_tsupport_subset := u.approx_support_subset
  tendsto_value := tendsto_eLpNorm_subcritical hp hp2 u.tendsto_approx
  tendsto_grad := fun i => tendsto_eLpNorm_subcritical hp hp2 (u.tendsto_approx_grad i)

/-- The genuine planar subcritical choice p=4/3 gives q=4; the explicit
finite-volume factor converts its Euclidean gradient norm back to L2. -/
theorem h10_planar_sobolev {U : Set (Vec 2)}
    [IsFiniteMeasure (volumeOn U)] (u : PDE.H10Function U) :
    eLpNorm u.toFun 4 (volumeOn U) ≤
      ENNReal.ofReal (2 * sobolevWholeSpaceConstant 2) *
        (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volumeOn U) *
          (volumeOn U) Set.univ ^ (1 / 4 : ℝ)) := by
  let v := h1ToSubcritical u.toH1Function (p := 4 / 3) (by norm_num)
  have ha : v.HasSupportedSmoothApproximation :=
    ⟨h10SubcriticalApproximation u (by norm_num : (0 : ℝ) < 4 / 3) (by norm_num)⟩
  have hs := eLpNorm_sobolevConjugate_le_of_supportedSmoothApproximation
    (by norm_num : 2 ≤ 2) (by norm_num : (1 : ℝ) ≤ 4 / 3)
    (by norm_num : (4 / 3 : ℝ) < 2) v ha.some
  have hq : sobolevConjugate 2 (4 / 3) = 4 := by norm_num [sobolevConjugate]
  have hg := eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos
    (by norm_num : ENNReal.ofReal (4 / 3 : ℝ) ≤ 2)
    (by norm_num : (0 : ℝ≥0∞) < ENNReal.ofReal (4 / 3 : ℝ))
    (f := fun x => vecEuclideanNorm (u.grad x)) (μ := volumeOn U)
  norm_num at hg
  norm_num only [Nat.cast_ofNat] at hs
  rw [hq] at hs
  have hs' : eLpNorm u.toFun 4 (volumeOn U) ≤
      ENNReal.ofReal (2 * sobolevWholeSpaceConstant 2) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x))
          (ENNReal.ofReal (4 / 3 : ℝ)) (volumeOn U) := by
    simpa only [v, h1ToSubcritical, mul_comm, ENNReal.ofReal_ofNat] using hs
  exact hs'.trans (mul_le_mul_right (by convert hg using 1 <;> norm_num)
    (ENNReal.ofReal (2 * sobolevWholeSpaceConstant 2)))

/-- A supported cutoff of the actual positive part, with its own smooth
approximation, ready for both planar and critical Sobolev inequalities. -/
noncomputable def cutoffPositivePartH10 {d : ℕ} {V I O : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (u : Homogenization.H1Function V)
    (k : ℝ) {K : ℝ} (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V) :
    PDE.H10Function V :=
  ((h1FromHomogenization u).positivePartSubConst hV k).mulCutoffToH10 hV η hOV

@[simp]
theorem cutoffPositivePartH10_toFun {d : ℕ} {V I O : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (u : Homogenization.H1Function V)
    (k : ℝ) {K : ℝ} (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V) :
    (cutoffPositivePartH10 hV u k η hOV).toFun =
      fun x => η x * max (u.toFun x - k) 0 := by
  simp only [cutoffPositivePartH10, H1Function.mulCutoffToH10_toFun,
    H1Function.positivePartSubConst_toFun]
  rfl

/-- The cutoff carrier retains the exact Euclidean product-energy estimate. -/
theorem cutoffPositivePartH10_energy {d : ℕ} {V I O : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (u : Homogenization.H1Function V)
    (k : ℝ) {K : ℝ} (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V) :
    (∫ x in V, vecNormSq ((cutoffPositivePartH10 hV u k η hOV).grad x)) ≤
      2 * (∫ x in V, η x ^ 2 * vecNormSq (posPartGrad u k x)) +
        2 * K ^ 2 * (∫ x in O, max (u.toFun x - k) 0 ^ 2) := by
  simpa only [cutoffPositivePartH10, H1Function.positivePartSubConst_toFun,
    H1Function.positivePartSubConst_grad, h1FromHomogenization, posPartGrad] using
    H1Function.setIntegral_vecNormSq_mulCutoffToH10_grad_le
      ((h1FromHomogenization u).positivePartSubConst hV k) η hV hOV

/-- The critical Sobolev bridge for the actual cutoff/truncation carrier. -/
theorem cutoffPositivePartH10_sobolev {d : ℕ} (hd : 3 ≤ d)
    {V I O : Set (Vec d)} (hV : IsOpenBoundedConvexDomain V)
    (u : Homogenization.H1Function V) (k : ℝ) {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V) :
    (∫ x in V, |η x * max (u.toFun x - k) 0| ^ (sobolevConjugate d 2)) ^
        (2 / sobolevConjugate d 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        (2 * (∫ x in V, η x ^ 2 * vecNormSq (posPartGrad u k x)) +
          2 * K ^ 2 * (∫ x in O, max (u.toFun x - k) 0 ^ 2)) := by
  have hs := setIntegral_abs_rpow_sobolevConjugate_two_rpow_two_div_le hd
    (cutoffPositivePartH10 hV u k η hOV)
  rw [cutoffPositivePartH10_toFun] at hs
  exact hs.trans (mul_le_mul_of_nonneg_left
    (cutoffPositivePartH10_energy hV u k η hOV) (sq_nonneg _))


/-- Nonnegative truncation commutes exactly with zero extension in the
squared integral. The domain is intersected, with no boundary regularity. -/
theorem zero_extended_positivePart_sq_integral {d : ℕ} {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) (w : Homogenization.H10Function U)
    {k : ℝ} (hk : 0 ≤ k) :
    (∫ x in V, max ((zeroExtCube hU hV w).toFun x - k) 0 ^ 2) =
      ∫ x in U ∩ V, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  classical
  have heq : (fun x => max ((zeroExtCube hU hV w).toFun x - k) 0 ^ 2) =
      U.indicator (fun x => max (w.toH1Function.toFun x - k) 0 ^ 2) := by
    funext x
    by_cases hx : x ∈ U
    · simp only [zeroExtCube_toFun, Set.indicator_of_mem hx]
    · simp only [zeroExtCube_toFun, Set.indicator_of_notMem hx, zero_sub,
        max_eq_right (neg_nonpos.mpr hk), zero_pow (by decide : 2 ≠ 0)]
  rw [heq, integral_indicator hU.measurableSet, Measure.restrict_restrict hU.measurableSet]

/-- Removing a cutoff costs only its explicit gradient bound. -/
theorem cutoffPositivePartH10_energy_le {d : ℕ} {V I O : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (u : Homogenization.H1Function V)
    {k : ℝ} (hk : 0 ≤ k) {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V) :
    (∫ x in V, vecNormSq ((cutoffPositivePartH10 hV u k η hOV).grad x)) ≤
      2 * (∫ x in V, vecNormSq (posPartGrad u k x)) +
        2 * K ^ 2 * (∫ x in V, max (u.toFun x - k) 0 ^ 2) := by
  have hEint : IntegrableOn (fun x => vecNormSq (posPartGrad u k x)) V :=
    integrableOn_vecNormSq_of_memVectorL2On (posPartGrad_gradMemL2 u k)
  have hweighted : (∫ x in V, η x ^ 2 * vecNormSq (posPartGrad u k x)) ≤
      ∫ x in V, vecNormSq (posPartGrad u k x) := by
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _))
      hEint
    exact Filter.Eventually.of_forall fun x => by
      have hη : η x ^ 2 ≤ 1 := by nlinarith [η.nonneg x, η.le_one x]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hη (vecNormSq_nonneg (posPartGrad u k x))
  have htail : (∫ x in O, max (u.toFun x - k) 0 ^ 2) ≤
      ∫ x in V, max (u.toFun x - k) 0 ^ 2 :=
    setIntegral_mono_set (memL2On_positivePart_of_nonneg u hk).integrable_sq
      (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hOV hx)
  exact (cutoffPositivePartH10_energy hV u k η hOV).trans
    (add_le_add (mul_le_mul_of_nonneg_left hweighted (by norm_num))
      (mul_le_mul_of_nonneg_left htail (by positivity)))

/-- Raising the level and shrinking the set decrease the actual zero-extended
quadratic tail, including for balls crossing the original boundary. -/
theorem zero_extended_positivePart_sq_integral_le {d : ℕ} {U V W : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V)
    (w : Homogenization.H10Function U) (hVW : V ⊆ W)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k ≤ l) :
    (∫ x in V, max ((zeroExtCube hU hV w).toFun x - l) 0 ^ 2) ≤
      ∫ x in U ∩ W, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  rw [zero_extended_positivePart_sq_integral hU hV w (hk.trans hkl)]
  have hi : IntegrableOn (fun x => max (w.toH1Function.toFun x - k) 0 ^ 2) U :=
    (memL2On_positivePart_of_nonneg w.toH1Function hk).integrable_sq
  have hlevel : (∫ x in U ∩ V, max (w.toH1Function.toFun x - l) 0 ^ 2) ≤
      ∫ x in U ∩ V, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (hi.mono_set Set.inter_subset_left)
    exact Filter.Eventually.of_forall fun x =>
      pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 (sub_le_sub_left hkl _)) 2
  exact hlevel.trans (setIntegral_mono_set (hi.mono_set Set.inter_subset_left)
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
    (Filter.Eventually.of_forall fun x hx => ⟨hx.1, hVW hx.2⟩))

/-- Sobolev energy for an actual eigenfunction cutoff. All forcing and
radius/level factors come from the checked weak-equation estimate. -/
theorem eigenfunction_zero_extended_cutoff_sobolev {d : ℕ} (hd : 3 ≤ d)
    {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec d) {r s k l : ℝ} (hr : 0 < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) {I O : Set (Vec d)} {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ euclideanBall z r) :
    (∫ x in euclideanBall z r,
      |η x * max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0| ^
        (sobolevConjugate d 2)) ^ (2 / sobolevConjugate d 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * K ^ 2) *
        ∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  let hV := isOpenBoundedConvexDomain_euclideanBall z hr
  let u := zeroExtCube hU (isOpen_euclideanBall z r) w
  have hs := setIntegral_abs_rpow_sobolevConjugate_two_rpow_two_div_le hd
    (cutoffPositivePartH10 hV u l η hOV)
  rw [cutoffPositivePartH10_toFun] at hs
  have he := cutoffPositivePartH10_energy_le hV u (hk.trans hkl.le) η hOV
  have hE := eigenfunction_zero_extended_ball_two_level_energy hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z hr.le hrs hk hkl
  have hT := zero_extended_positivePart_sq_integral_le hU (isOpen_euclideanBall z r)
    w (euclideanBall_mono hr.le hrs.le) hk hkl.le
  have hbound := he.trans (add_le_add
    (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * K ^ 2)))
  have hfinal := hs.trans (mul_le_mul_of_nonneg_left hbound (sq_nonneg _))
  convert hfinal using 1 <;> ring


/-- Restricted Holder and the actual superlevel measure give the nonlinear
tail step for a supported positive-part cutoff, at any exponent above two. -/
theorem cutoffPositivePartH10_two_level_holder {d : ℕ} {V I O : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hfin : volume V ≠ ⊤)
    (hI : MeasurableSet I) (hIV : I ⊆ V) (u : Homogenization.H1Function V)
    {k l : ℝ} (hk : 0 ≤ k) (hkl : k < l) {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ V)
    {q : ℝ} (hq : 2 < q)
    (hcrit : MemLp (cutoffPositivePartH10 hV u l η hOV).toFun
      (ENNReal.ofReal q) (volumeOn V)) :
    (∫ x in I, max (u.toFun x - l) 0 ^ 2) ≤
      (∫ x in V, |η x * max (u.toFun x - l) 0| ^ q) ^ (2 / q) *
        ((∫ x in I, max (u.toFun x - k) 0 ^ 2) / (l - k) ^ 2) ^ (1 - 2 / q) := by
  classical
  let f := (cutoffPositivePartH10 hV u l η hOV).toFun
  let S := I ∩ {x | l < u.toFun x}
  have hSV : S ⊆ V := fun x hx => hIV hx.1
  have hSI : S ⊆ I := Set.inter_subset_left
  have hqpos : 0 < q := lt_trans (by norm_num) hq
  have hAfin : volume S < ⊤ := (measure_mono hSV).trans_lt hfin.lt_top
  have hcritS : MemLp f (ENNReal.ofReal q) (volume.restrict S) :=
    hcrit.mono_measure (Measure.restrict_mono hSV le_rfl)
  have hqInt : IntegrableOn (fun x => |f x| ^ q) V := by
    simpa only [IntegrableOn, Real.norm_eq_abs, ENNReal.toReal_ofReal hqpos.le]
      using hcrit.integrable_norm_rpow
        (ENNReal.ofReal_ne_zero_iff.mpr hqpos) ENNReal.ofReal_ne_top
  have hholder := setIntegral_abs_rpow_le_setIntegral_abs_rpow_rpow_mul_measure_toReal_rpow
    (by norm_num : (0 : ℝ) < 2) hq hAfin hcritS
  have hqmono : (∫ x in S, |f x| ^ q) ^ (2 / q) ≤
      (∫ x in V, |f x| ^ q) ^ (2 / q) := by
    apply Real.rpow_le_rpow (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _)
    · exact setIntegral_mono_set hqInt
        (Filter.Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg _) _)
        (Filter.Eventually.of_forall fun x hx => hSV hx)
    · positivity
  have hlow : IntegrableOn (fun x => max (u.toFun x - k) 0 ^ 2) I :=
    (show IntegrableOn (fun x => max (u.toFun x - k) 0 ^ 2) V volume from
      (memL2On_positivePart_of_nonneg u hk).integrable_sq).mono_set hIV
  have huI : AEStronglyMeasurable u.toFun (volume.restrict I) :=
    u.memL2.aestronglyMeasurable.mono_measure (Measure.restrict_mono hIV le_rfl)
  have hlevel : NullMeasurableSet {x | l < u.toFun x} (volume.restrict I) :=
    aestronglyMeasurable_const.nullMeasurableSet_lt huI
  have hsuper := sq_mul_measure_inter_superlevel_toReal_le_setIntegral_sq hkl hlevel hlow
  have hmeasure : (volume S).toReal ≤
      (∫ x in I, max (u.toFun x - k) 0 ^ 2) / (l - k) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (sub_pos.mpr hkl))).2
    simpa only [S, mul_comm] using hsuper
  have hβ : 0 ≤ 1 - 2 / q := sub_nonneg.mpr ((div_le_one hqpos).mpr hq.le)
  have hmeasurePow := Real.rpow_le_rpow ENNReal.toReal_nonneg hmeasure hβ
  have hleft : (∫ x in I, max (u.toFun x - l) 0 ^ 2) = ∫ x in S, f x ^ 2 := by
    calc
      _ = ∫ x in I, f x ^ 2 := by
        apply setIntegral_congr_fun hI
        intro x hx
        simp only [f, cutoffPositivePartH10_toFun, η.eq_one_on_inner x hx, one_mul]
      _ = _ := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hI hSI
        intro x hx
        have hxl : u.toFun x ≤ l := by
          exact not_lt.mp fun h => hx.2 ⟨hx.1, h⟩
        simp only [f, cutoffPositivePartH10_toFun, max_eq_right (sub_nonpos.mpr hxl),
          mul_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [hleft]
  have hholder' : (∫ x in S, f x ^ 2) ≤
      (∫ x in S, |f x| ^ q) ^ (2 / q) * (volume S).toReal ^ (1 - 2 / q) := by
    simpa only [Real.rpow_two, sq_abs] using hholder
  have hstep := hholder'.trans (mul_le_mul_of_nonneg_right hqmono (by positivity))
  have hfinal := hstep.trans (mul_le_mul_of_nonneg_left hmeasurePow
    (Real.rpow_nonneg (integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg _) _) _))
  simpa only [f, cutoffPositivePartH10_toFun] using hfinal


/-- Finiteness of the critical norm follows from the actual zero-boundary
Sobolev estimate and the actual Euclidean L2 gradient. -/
theorem h10_memLp_critical {d : ℕ} (hd : 3 ≤ d) {V : Set (Vec d)}
    (v : PDE.H10Function V) :
    MemLp v.toFun (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn V) := by
  have hg : euclideanFieldELpNormOn V 2 v.grad ≠ ⊤ := by
    simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn] using
      v.gradMemL2.memLp_vecEuclideanNorm.eLpNorm_ne_top
  apply lt_of_le_of_lt (by
    simpa only [eLpNormOn] using
      eLpNormOn_sobolevConjugate_two_le_euclideanFieldELpNormOn hd v)
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.coe_ne_top hg)

/-- The actual eigenfunction satisfies a superlinear two-level tail estimate.
The cutoff may meet the original boundary; no essential-supremum premise is used. -/
theorem eigenfunction_zero_extended_cutoff_two_level_tail {d : ℕ} (hd : 3 ≤ d)
    {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec d) {r s k l : ℝ} (hr : 0 < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) {I O : Set (Vec d)} {K : ℝ}
    (hI : MeasurableSet I) (hIV : I ⊆ euclideanBall z r)
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ euclideanBall z r) :
    (∫ x in I, max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0 ^ 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * K ^ 2) *
        (∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) *
        ((∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) /
          (l - k) ^ 2) ^ (2 / (d : ℝ)) := by
  let hV := isOpenBoundedConvexDomain_euclideanBall z hr
  let u := zeroExtCube hU (isOpen_euclideanBall z r) w
  let T := ∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2
  have hdreal : (2 : ℝ) < d := by exact_mod_cast (show 2 < d by omega)
  have hq : 2 < sobolevConjugate d 2 := by
    unfold sobolevConjugate
    apply (lt_div_iff₀ (sub_pos.mpr hdreal)).mpr
    nlinarith
  have hβ : 1 - 2 / sobolevConjugate d 2 = 2 / (d : ℝ) := by
    rw [two_div_sobolevConjugate_two hd]
    field_simp
    ring
  have hH := cutoffPositivePartH10_two_level_holder hV (volume_euclideanBall_ne_top z hr.le)
    hI hIV u hk hkl η hOV hq (h10_memLp_critical hd (cutoffPositivePartH10 hV u l η hOV))
  have hS := eigenfunction_zero_extended_cutoff_sobolev hd hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z hr hrs hk hkl η hOV
  have hlowInt : IntegrableOn (fun x => max (u.toFun x - k) 0 ^ 2)
      (euclideanBall z r) volume := (memL2On_positivePart_of_nonneg u hk).integrable_sq
  have hT : (∫ x in I, max (u.toFun x - k) 0 ^ 2) ≤ T :=
    (setIntegral_mono_set hlowInt (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hIV hx)).trans
      (zero_extended_positivePart_sq_integral_le hU (isOpen_euclideanBall z r) w
        (euclideanBall_mono hr.le hrs.le) hk (le_refl k))
  rw [hβ] at hH
  have hmeasurePow := Real.rpow_le_rpow
    (div_nonneg (integral_nonneg fun x => sq_nonneg _) (sq_nonneg (l - k)))
    (div_le_div_of_nonneg_right hT (sq_nonneg (l - k)))
    (by positivity : 0 ≤ 2 / (d : ℝ))
  have hstep := hH.trans (mul_le_mul_of_nonneg_right hS
    (by positivity : 0 ≤ ((∫ x in I, max (u.toFun x - k) 0 ^ 2) /
      (l - k) ^ 2) ^ (2 / (d : ℝ))))
  have hl : 0 ≤ l := hk.trans hkl.le
  have hgap : 0 < l - k := sub_pos.mpr hkl
  exact hstep.trans (mul_le_mul_of_nonneg_left hmeasurePow (by positivity))

/-- Three concentric radii specialize the actual two-level estimate to a
ball recurrence, with both inverse-square radius gaps displayed. -/
theorem eigenfunction_zero_extended_ball_two_level_tail {d : ℕ} (hd : 3 ≤ d)
    {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec d) {a r s k l : ℝ} (ha : 0 ≤ a) (har : a < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) :
    (∫ x in U ∩ euclideanBall z a, max (w.toH1Function.toFun x - l) 0 ^ 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2) *
        (∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) *
        ((∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) /
          (l - k) ^ 2) ^ (2 / (d : ℝ)) := by
  have h := eigenfunction_zero_extended_cutoff_two_level_tail hd hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z (ha.trans_lt har) hrs hk hkl
    (isOpen_euclideanBall z a).measurableSet (euclideanBall_mono ha har.le)
    (quantitativeBallCutoff z ha har) (Set.Subset.refl _)
  have heq := zero_extended_positivePart_sq_integral hU (isOpen_euclideanBall z a) w
    (hk.trans hkl.le)
  change (∫ x in euclideanBall z a,
    max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0 ^ 2) = _ at heq
  rw [heq] at h
  exact h


/-- The actual supported planar carrier has finite L4 norm. -/
theorem h10_memLp_planar {V : Set (Vec 2)} [IsFiniteMeasure (volumeOn V)]
    (v : PDE.H10Function V) : MemLp v.toFun 4 (volumeOn V) := by
  apply lt_of_le_of_lt (h10_planar_sobolev v)
  exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.mul_ne_top v.gradMemL2.memLp_vecEuclideanNorm.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _))))

/-- The planar integral-power Sobolev estimate retains the finite-volume
factor. All extended-real norms are proved finite before taking real values. -/
theorem h10_planar_sobolev_energy {V : Set (Vec 2)} [IsFiniteMeasure (volumeOn V)]
    (v : PDE.H10Function V) :
    (∫ x in V, |v.toFun x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (2 * sobolevWholeSpaceConstant 2) ^ 2 *
        (∫ x in V, vecNormSq (v.grad x)) * (volume V).toReal ^ (1 / 2 : ℝ) := by
  have hg := v.gradMemL2.memLp_vecEuclideanNorm
  have hvol : (volumeOn V) Set.univ = volume V := by simp [volumeOn]
  have hB : ENNReal.ofReal (2 * sobolevWholeSpaceConstant 2) *
      (eLpNorm (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn V) *
        (volumeOn V) Set.univ ^ (1 / 4 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top hg.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)))
  have hC : 0 ≤ 2 * sobolevWholeSpaceConstant 2 :=
    mul_nonneg (by norm_num) (sobolevWholeSpaceConstant_pos 2).le
  have hn := ENNReal.toReal_mono hB (h10_planar_sobolev v)
  have hn' : (eLpNorm v.toFun 4 (volumeOn V)).toReal ≤
      (2 * sobolevWholeSpaceConstant 2) *
        ((eLpNorm (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn V)).toReal *
          (volume V).toReal ^ (1 / 4 : ℝ)) := by
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
      ← ENNReal.toReal_rpow, hvol] using hn
  have hfour : (eLpNorm v.toFun 4 (volumeOn V)).toReal ^ (4 : ℝ) =
      ∫ x in V, |v.toFun x| ^ (4 : ℝ) := by
    simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using
      toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
        (f := v.toFun) (μ := volumeOn V) (by norm_num : (0 : ℝ) < 4)
        (by simpa only [ENNReal.ofReal_ofNat] using h10_memLp_planar v)
  have hvalue : (∫ x in V, |v.toFun x| ^ (4 : ℝ)) ^ (1 / 2 : ℝ) =
      (eLpNorm v.toFun 4 (volumeOn V)).toReal ^ 2 := by
    rw [← hfour, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  have hgrad : (eLpNorm (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn V)).toReal ^ 2 =
      ∫ x in V, vecNormSq (v.grad x) := by
    simpa only [vecEuclideanNorm_sq] using toReal_eLpNorm_two_sq_eq_integral_sq hg
  have hvolpow : ((volume V).toReal ^ (1 / 4 : ℝ)) ^ 2 =
      (volume V).toReal ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul ENNReal.toReal_nonneg]
    norm_num
  rw [hvalue]
  calc
    _ ≤ ((2 * sobolevWholeSpaceConstant 2) *
        ((eLpNorm (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn V)).toReal *
          (volume V).toReal ^ (1 / 4 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ ENNReal.toReal_nonneg hn' 2
    _ = _ := by simp only [mul_pow, hgrad, hvolpow]; ring

/-- The planar eigenfunction cutoff estimate uses the subcritical L4
carrier and retains its explicit square-root volume factor. -/
theorem eigenfunction_zero_extended_cutoff_planar_sobolev
    {U : Set (Vec 2)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField 2} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec 2 → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec 2) {r s k l : ℝ} (hr : 0 < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) {I O : Set (Vec 2)} {K : ℝ}
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ euclideanBall z r) :
    (∫ x in euclideanBall z r,
      |η x * max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0| ^
        (4 : ℝ)) ^ (1 / 2 : ℝ) ≤
      (2 * sobolevWholeSpaceConstant 2) ^ 2 *
        (volume (euclideanBall z r)).toReal ^ (1 / 2 : ℝ) *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * K ^ 2) *
        ∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2 := by
  letI := isFiniteMeasure_volumeOn_euclideanBall z hr.le
  let hV := isOpenBoundedConvexDomain_euclideanBall z hr
  let u := zeroExtCube hU (isOpen_euclideanBall z r) w
  have hs := h10_planar_sobolev_energy (cutoffPositivePartH10 hV u l η hOV)
  rw [cutoffPositivePartH10_toFun] at hs
  have he := cutoffPositivePartH10_energy_le hV u (hk.trans hkl.le) η hOV
  have hE := eigenfunction_zero_extended_ball_two_level_energy hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z hr.le hrs hk hkl
  have hT := zero_extended_positivePart_sq_integral_le hU (isOpen_euclideanBall z r)
    w (euclideanBall_mono hr.le hrs.le) hk hkl.le
  have hbound := he.trans (add_le_add
    (mul_le_mul_of_nonneg_left hE (by norm_num : (0 : ℝ) ≤ 2))
    (mul_le_mul_of_nonneg_left hT (by positivity : 0 ≤ 2 * K ^ 2)))
  have hfinal := hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbound (sq_nonneg _)) (by positivity))
  convert hfinal using 1 <;> ring

/-- The planar actual-eigenfunction two-level estimate is superlinear with
exponent one half, obtained from q=4 rather than a critical p=2 endpoint. -/
theorem eigenfunction_zero_extended_cutoff_planar_two_level_tail
    {U : Set (Vec 2)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField 2} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec 2 → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec 2) {r s k l : ℝ} (hr : 0 < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) {I O : Set (Vec 2)} {K : ℝ}
    (hI : MeasurableSet I) (hIV : I ⊆ euclideanBall z r)
    (η : QuantitativeSmoothCutoff I O K) (hOV : O ⊆ euclideanBall z r) :
    (∫ x in I, max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0 ^ 2) ≤
      (2 * sobolevWholeSpaceConstant 2) ^ 2 *
        (volume (euclideanBall z r)).toReal ^ (1 / 2 : ℝ) *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * K ^ 2) *
        (∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) *
        ((∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) /
          (l - k) ^ 2) ^ (1 / 2 : ℝ) := by
  letI := isFiniteMeasure_volumeOn_euclideanBall z hr.le
  let hV := isOpenBoundedConvexDomain_euclideanBall z hr
  let u := zeroExtCube hU (isOpen_euclideanBall z r) w
  let T := ∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2
  have hH := cutoffPositivePartH10_two_level_holder hV (volume_euclideanBall_ne_top z hr.le)
    hI hIV u hk hkl η hOV (by norm_num : (2 : ℝ) < 4)
    (by simpa only [ENNReal.ofReal_ofNat] using
      (h10_memLp_planar (cutoffPositivePartH10 hV u l η hOV)))
  simp only [show (2 : ℝ) / 4 = 1 / 2 by norm_num,
    show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hH
  have hS := eigenfunction_zero_extended_cutoff_planar_sobolev hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z hr hrs hk hkl η hOV
  have hlowInt : IntegrableOn (fun x => max (u.toFun x - k) 0 ^ 2)
      (euclideanBall z r) volume := (memL2On_positivePart_of_nonneg u hk).integrable_sq
  have hT : (∫ x in I, max (u.toFun x - k) 0 ^ 2) ≤ T :=
    (setIntegral_mono_set hlowInt (Filter.Eventually.of_forall fun x => sq_nonneg _)
      (Filter.Eventually.of_forall fun x hx => hIV hx)).trans
      (zero_extended_positivePart_sq_integral_le hU (isOpen_euclideanBall z r) w
        (euclideanBall_mono hr.le hrs.le) hk (le_refl k))
  have hmeasurePow := Real.rpow_le_rpow
    (div_nonneg (integral_nonneg fun x => sq_nonneg _) (sq_nonneg (l - k)))
    (div_le_div_of_nonneg_right hT (sq_nonneg (l - k))) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hstep := hH.trans (mul_le_mul_of_nonneg_right hS
    (by positivity : 0 ≤ ((∫ x in I, max (u.toFun x - k) 0 ^ 2) /
      (l - k) ^ 2) ^ (1 / 2 : ℝ)))
  have hl : 0 ≤ l := hk.trans hkl.le
  have hgap : 0 < l - k := sub_pos.mpr hkl
  exact hstep.trans (mul_le_mul_of_nonneg_left hmeasurePow (by positivity))

/-- The planar three-radius recurrence retains the subcritical Sobolev
volume factor and the exact eigenfunction energy coefficients. -/
theorem eigenfunction_zero_extended_ball_planar_two_level_tail
    {U : Set (Vec 2)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ M : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    {A : CoeffField 2} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    {ρ : Vec 2 → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
    (hρM : ∀ᵐ x ∂(volume.restrict U), |ρ x| ≤ M)
    (w : Homogenization.H10Function U) {eigenvalue : ℝ} (hEigenvalue : 0 ≤ eigenvalue)
    (hw : IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0))
    (z : Vec 2) {a r s k l : ℝ} (ha : 0 ≤ a) (har : a < r) (hrs : r < s)
    (hk : 0 ≤ k) (hkl : k < l) :
    (∫ x in U ∩ euclideanBall z a, max (w.toH1Function.toFun x - l) 0 ^ 2) ≤
      (2 * sobolevWholeSpaceConstant 2) ^ 2 *
        (volume (euclideanBall z r)).toReal ^ (1 / 2 : ℝ) *
        (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
          4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2) *
        (∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) *
        ((∫ x in U ∩ euclideanBall z s, max (w.toH1Function.toFun x - k) 0 ^ 2) /
          (l - k) ^ 2) ^ (1 / 2 : ℝ) := by
  have h := eigenfunction_zero_extended_cutoff_planar_two_level_tail hU hfin hκ hM hA
    hρ hρM w hEigenvalue hw z (ha.trans_lt har) hrs hk hkl
    (isOpen_euclideanBall z a).measurableSet (euclideanBall_mono ha har.le)
    (quantitativeBallCutoff z ha har) (Set.Subset.refl _)
  have heq := zero_extended_positivePart_sq_integral hU (isOpen_euclideanBall z a) w
    (hk.trans hkl.le)
  change (∫ x in euclideanBall z a,
    max ((zeroExtCube hU (isOpen_euclideanBall z r) w).toFun x - l) 0 ^ 2) = _ at heq
  rw [heq] at h
  exact h


/-- The literal anisotropic Dirichlet pairing, on the existing H¹ carrier. -/
noncomputable def dirichletEnergyPairing {d : ℕ} {U : Set (Vec d)}
    (A : CoeffField d) (u v : Homogenization.H1Function U) : ℝ :=
  ∫ x in U, vecDot (matVecMul (A x) (u.grad x)) (v.grad x)

/-- The literal weighted L² pairing; the reference measure remains Lebesgue. -/
noncomputable def weightedL2Pairing {d : ℕ} {U : Set (Vec d)}
    (ρ : Vec d → ℝ) (u v : Homogenization.H1Function U) : ℝ :=
  ∫ x in U, ρ x * u.toFun x * v.toFun x

/-- Uniform ellipticity supplies integrability of every actual energy cross term. -/
theorem dirichletEnergyPairing_integrable {d : ℕ} {U : Set (Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u v : Homogenization.H1Function U) :
    IntegrableOn (fun x => vecDot (matVecMul (A x) (u.grad x)) (v.grad x)) U :=
  integrableOn_vecDot_of_memVectorL2On
    (memVectorL2On_matVecMul_of_isEllipticFieldOn hA u.gradMemL2) v.gradMemL2

/-- Bounded measurable weights supply integrability of every mass cross term. -/
theorem weightedL2Pairing_integrable {d : ℕ} {U : Set (Vec d)}
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (u v : Homogenization.H1Function U) :
    IntegrableOn (fun x => ρ x * u.toFun x * v.toFun x) U := by
  have hu : MemL2On U (fun x => ρ x * u.toFun x) := by
    simpa only [mul_comm] using u.memL2.fun_mul hρ
  exact integrableOn_mul_of_memL2On hu v.memL2

/-- Linearity of the actual energy pairing in its first argument. -/
theorem dirichletEnergyPairing_add_smul_left {d : ℕ} {U : Set (Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u v w : Homogenization.H1Function U) (t : ℝ) :
    dirichletEnergyPairing A (u + t • v) w =
      dirichletEnergyPairing A u w + t * dirichletEnergyPairing A v w := by
  unfold dirichletEnergyPairing
  change (∫ x in U, Homogenization.vecDot
    (Homogenization.matVecMul (A x) (u.grad x + t • v.grad x)) (w.grad x)) = _
  simp only [Homogenization.matVecMul_add, Homogenization.matVecMul_smul,
    Homogenization.vecDot_add_left, Homogenization.vecDot_smul_left]
  change (∫ x in U, PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (w.grad x) +
    t * PDE.vecDot (PDE.matVecMul (A x) (v.grad x)) (w.grad x)) = _
  rw [integral_add (dirichletEnergyPairing_integrable hA u w)
    ((dirichletEnergyPairing_integrable hA v w).const_mul t), integral_const_mul]

/-- Linearity of the actual energy pairing in its test argument. -/
theorem dirichletEnergyPairing_add_smul_right {d : ℕ} {U : Set (Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (u v w : Homogenization.H1Function U) (t : ℝ) :
    dirichletEnergyPairing A u (v + t • w) =
      dirichletEnergyPairing A u v + t * dirichletEnergyPairing A u w := by
  unfold dirichletEnergyPairing
  change (∫ x in U, Homogenization.vecDot
    (Homogenization.matVecMul (A x) (u.grad x)) (v.grad x + t • w.grad x)) = _
  simp only [Homogenization.vecDot_add_right, Homogenization.vecDot_smul_right]
  change (∫ x in U, PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (v.grad x) +
    t * PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (w.grad x)) = _
  rw [integral_add (dirichletEnergyPairing_integrable hA u v)
    ((dirichletEnergyPairing_integrable hA u w).const_mul t), integral_const_mul]

/-- Linearity of the actual weighted pairing in its first argument. -/
theorem weightedL2Pairing_add_smul_left {d : ℕ} {U : Set (Vec d)}
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (u v w : Homogenization.H1Function U) (t : ℝ) :
    weightedL2Pairing ρ (u + t • v) w =
      weightedL2Pairing ρ u w + t * weightedL2Pairing ρ v w := by
  unfold weightedL2Pairing
  change (∫ x in U, ρ x * (u.toFun x + t * v.toFun x) * w.toFun x) = _
  have hp (x : Vec d) : ρ x * (u.toFun x + t * v.toFun x) * w.toFun x =
      ρ x * u.toFun x * w.toFun x + t * (ρ x * v.toFun x * w.toFun x) := by ring
  simp_rw [hp]
  rw [integral_add (weightedL2Pairing_integrable hρ u w)
    ((weightedL2Pairing_integrable hρ v w).const_mul t), integral_const_mul]

/-- Linearity of the actual weighted pairing in its test argument. -/
theorem weightedL2Pairing_add_smul_right {d : ℕ} {U : Set (Vec d)}
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (u v w : Homogenization.H1Function U) (t : ℝ) :
    weightedL2Pairing ρ u (v + t • w) =
      weightedL2Pairing ρ u v + t * weightedL2Pairing ρ u w := by
  unfold weightedL2Pairing
  change (∫ x in U, ρ x * u.toFun x * (v.toFun x + t * w.toFun x)) = _
  have hp (x : Vec d) : ρ x * u.toFun x * (v.toFun x + t * w.toFun x) =
      ρ x * u.toFun x * v.toFun x + t * (ρ x * u.toFun x * w.toFun x) := by ring
  simp_rw [hp]
  rw [integral_add (weightedL2Pairing_integrable hρ u v)
    ((weightedL2Pairing_integrable hρ u w).const_mul t), integral_const_mul]

/-- Symmetric coefficients give the symmetric energy pairing, a.e. on the
actual domain. No isotropy is imposed. -/
theorem dirichletEnergyPairing_symm {d : ℕ} {U : Set (Vec d)}
    {A : CoeffField d} (hA : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    (u v : Homogenization.H1Function U) :
    dirichletEnergyPairing A u v = dirichletEnergyPairing A v u := by
  apply integral_congr_ae
  filter_upwards [hA] with x hx
  change Homogenization.vecDot (Homogenization.matVecMul (A x) (u.grad x)) (v.grad x) =
    Homogenization.vecDot (Homogenization.matVecMul (A x) (v.grad x)) (u.grad x)
  rw [Homogenization.vecDot_comm, Homogenization.vecDot_comm _ (u.grad x)]
  exact Homogenization.vecDot_matVecMul_comm_of_isSymm hx (v.grad x) (u.grad x)

/-- Symmetry of the actual weighted L² pairing does not need positivity. -/
theorem weightedL2Pairing_symm {d : ℕ} {U : Set (Vec d)}
    (ρ : Vec d → ℝ) (u v : Homogenization.H1Function U) :
    weightedL2Pairing ρ u v = weightedL2Pairing ρ v u := by
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- A quadratic polynomial nonnegative in every signed direction has zero
linear coefficient when its constant coefficient vanishes. -/
theorem quadratic_direction_linear_eq_zero {a b : ℝ}
    (h : ∀ t : ℝ, 0 ≤ a * t ^ 2 + 2 * b * t) : b = 0 := by
  have hd := discrim_le_zero (a := a) (b := 2 * b) (c := 0)
    (fun t => by simpa only [pow_two, add_zero] using h t)
  simp only [discrim, mul_zero, sub_zero] at hd
  nlinarith [sq_nonneg (2 * b)]

/-- The genuine Rayleigh lower bound and equality at one H¹₀ vector imply
its weak weighted eigenvalue equation against every actual H¹₀ test. The
proof varies the vector in every signed real direction. This is a variation
bridge, not a theorem asserting that a minimizer has been produced. -/
theorem rayleigh_minimizer_weak_solution {d : ℕ} {U : Set (Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ) {eigenvalue : ℝ}
    (w : Homogenization.H10Function U)
    (hmin : ∀ v : Homogenization.H10Function U,
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
        dirichletEnergyPairing A v.toH1Function v.toH1Function)
    (heq : dirichletEnergyPairing A w.toH1Function w.toH1Function =
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function) :
    IsWeakSolutionOn A U w.toH1Function
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) := by
  intro v
  have hdir := quadratic_direction_linear_eq_zero
    (a := dirichletEnergyPairing A v.toH1Function v.toH1Function -
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function)
    (b := dirichletEnergyPairing A w.toH1Function v.toH1Function -
      eigenvalue * weightedL2Pairing ρ w.toH1Function v.toH1Function) ?_
  · change dirichletEnergyPairing A w.toH1Function v.toH1Function = _
    simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero]
    rw [show (fun x => eigenvalue * ρ x * w.toH1Function.toFun x *
        v.toH1Function.toFun x) =
        (fun x => eigenvalue * (ρ x * w.toH1Function.toFun x *
          v.toH1Function.toFun x)) by funext x; ring, integral_const_mul]
    exact sub_eq_zero.mp hdir
  · intro t
    have hh := hmin (w + t • v)
    change eigenvalue * weightedL2Pairing ρ
      (w.toH1Function + t • v.toH1Function) (w.toH1Function + t • v.toH1Function) ≤
      dirichletEnergyPairing A (w.toH1Function + t • v.toH1Function)
        (w.toH1Function + t • v.toH1Function) at hh
    rw [dirichletEnergyPairing_add_smul_left hA,
      dirichletEnergyPairing_add_smul_right hA,
      dirichletEnergyPairing_add_smul_right hA,
      dirichletEnergyPairing_symm hAsymm v.toH1Function w.toH1Function,
      weightedL2Pairing_add_smul_left hρ, weightedL2Pairing_add_smul_right hρ,
      weightedL2Pairing_add_smul_right hρ,
      weightedL2Pairing_symm ρ v.toH1Function w.toH1Function, heq] at hh
    nlinarith only [hh]


/-- Scaling both arguments scales the actual energy quadratically. -/
theorem dirichletEnergyPairing_smul_self {d : ℕ} {U : Set (Vec d)}
    (A : CoeffField d) (u : Homogenization.H1Function U) (t : ℝ) :
    dirichletEnergyPairing A (t • u) (t • u) =
      t ^ 2 * dirichletEnergyPairing A u u := by
  unfold dirichletEnergyPairing
  change (∫ x in U, vecDot (matVecMul (A x) (t • u.grad x)) (t • u.grad x)) = _
  simp only [DGNM.matVecMul_smul, DGNM.vecDot_smul_left, DGNM.vecDot_smul_right]
  simp_rw [← mul_assoc, ← pow_two]
  exact integral_const_mul _ _

/-- Scaling both arguments scales the actual weighted square norm quadratically. -/
theorem weightedL2Pairing_smul_self {d : ℕ} {U : Set (Vec d)}
    (ρ : Vec d → ℝ) (u : Homogenization.H1Function U) (t : ℝ) :
    weightedL2Pairing ρ (t • u) (t • u) = t ^ 2 * weightedL2Pairing ρ u u := by
  unfold weightedL2Pairing
  change (∫ x in U, ρ x * (t * u.toFun x) * (t * u.toFun x)) = _
  have hp (x : Vec d) : ρ x * (t * u.toFun x) * (t * u.toFun x) =
      t ^ 2 * (ρ x * u.toFun x * u.toFun x) := by ring
  simp_rw [hp]
  exact integral_const_mul _ _

/-- Ellipticity makes the actual Dirichlet energy nonnegative. -/
theorem dirichletEnergyPairing_self_nonneg {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {κ : ℝ} {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ U A) (u : Homogenization.H1Function U) :
    0 ≤ dirichletEnergyPairing A u u := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  rw [PDE.vecDot_comm]
  exact (mul_nonneg (hA.elliptic hx).lam_pos.le (vecNormSq_nonneg _)).trans
    ((hA.elliptic hx).coercive _)

/-- Normalizing every positive-mass vector proves the homogeneous Rayleigh
bound from the minimum over the genuine weighted unit sphere. Zero-mass
vectors are handled by ellipticity, without dividing by their mass. -/
theorem rayleigh_lower_bound_of_normalized_minimum {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {κ : ℝ} {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ U A) {ρ : Vec d → ℝ}
    (hρnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x) {eigenvalue : ℝ}
    (hmin : ∀ v : Homogenization.H10Function U,
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 →
        eigenvalue ≤ dirichletEnergyPairing A v.toH1Function v.toH1Function)
    (v : Homogenization.H10Function U) :
    eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
      dirichletEnergyPairing A v.toH1Function v.toH1Function := by
  let m := weightedL2Pairing ρ v.toH1Function v.toH1Function
  have hm : 0 ≤ m := by
    apply integral_nonneg_of_ae
    filter_upwards [hρnonneg] with x hx
    change (0 : ℝ) ≤ ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x
    simpa only [mul_assoc, ← pow_two] using mul_nonneg hx (sq_nonneg (v.toH1Function.toFun x))
  by_cases hm0 : m = 0
  · change eigenvalue * m ≤ _
    rw [hm0, mul_zero]
    exact dirichletEnergyPairing_self_nonneg hU hA v.toH1Function
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    have hs : (Real.sqrt m)⁻¹ ^ 2 = m⁻¹ := by
      rw [inv_pow, Real.sq_sqrt hm]
    let z : Homogenization.H10Function U := (Real.sqrt m)⁻¹ • v
    have hz : weightedL2Pairing ρ z.toH1Function z.toH1Function = 1 := by
      change weightedL2Pairing ρ ((Real.sqrt m)⁻¹ • v.toH1Function)
        ((Real.sqrt m)⁻¹ • v.toH1Function) = _
      rw [weightedL2Pairing_smul_self, hs]
      exact inv_mul_cancel₀ hm0
    have hh := hmin z hz
    change eigenvalue ≤ dirichletEnergyPairing A ((Real.sqrt m)⁻¹ • v.toH1Function)
      ((Real.sqrt m)⁻¹ • v.toH1Function) at hh
    rw [dirichletEnergyPairing_smul_self, hs] at hh
    have hh' := mul_le_mul_of_nonneg_right hh hmpos.le
    change eigenvalue * m ≤ _
    calc
      _ ≤ (m⁻¹ * dirichletEnergyPairing A v.toH1Function v.toH1Function) * m := hh'
      _ = _ := by field_simp

/-- A normalized minimum of the actual weighted Rayleigh quotient has the
weak eigenvalue equation; the eigenvalue is its literal Dirichlet energy. -/
theorem normalized_rayleigh_minimizer_weak_solution {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {κ : ℝ} {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (hρnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x)
    (w : Homogenization.H10Function U)
    (hnorm : weightedL2Pairing ρ w.toH1Function w.toH1Function = 1)
    (hmin : ∀ v : Homogenization.H10Function U,
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 →
        dirichletEnergyPairing A w.toH1Function w.toH1Function ≤
          dirichletEnergyPairing A v.toH1Function v.toH1Function) :
    IsWeakSolutionOn A U w.toH1Function
      (fun x => dirichletEnergyPairing A w.toH1Function w.toH1Function *
        ρ x * w.toH1Function.toFun x) (fun _ => 0) := by
  apply rayleigh_minimizer_weak_solution hA hAsymm hρ w
    (rayleigh_lower_bound_of_normalized_minimum hU.measurableSet hA hρnonneg hmin)
  rw [hnorm, mul_one]

/-- Absolute value of an actual normalized Rayleigh minimizer is again a
normalized minimizer, and therefore is a genuine nonnegative weak
representative at the same eigenvalue. No equation for the absolute value
of an arbitrary eigenfunction, negligible zero set, or strict pointwise
positivity is assumed. The attainment premise remains explicit. -/
theorem exists_nonnegative_normalized_rayleigh_minimizer {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) {κ : ℝ} {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (hρnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x)
    (w : Homogenization.H10Function U)
    (hnorm : weightedL2Pairing ρ w.toH1Function w.toH1Function = 1)
    (hmin : ∀ v : Homogenization.H10Function U,
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 →
        dirichletEnergyPairing A w.toH1Function w.toH1Function ≤
          dirichletEnergyPairing A v.toH1Function v.toH1Function) :
    ∃ v : Homogenization.H10Function U,
      v.toH1Function.toFun = (fun x => |w.toH1Function.toFun x|) ∧
      (∀ x, 0 ≤ v.toH1Function.toFun x) ∧
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 ∧
      dirichletEnergyPairing A v.toH1Function v.toH1Function =
        dirichletEnergyPairing A w.toH1Function w.toH1Function ∧
      (∀ z : Homogenization.H10Function U,
        dirichletEnergyPairing A w.toH1Function w.toH1Function *
          weightedL2Pairing ρ z.toH1Function z.toH1Function ≤
            dirichletEnergyPairing A z.toH1Function z.toH1Function) ∧
      IsWeakSolutionOn A U v.toH1Function
        (fun x => dirichletEnergyPairing A w.toH1Function w.toH1Function *
          ρ x * v.toH1Function.toFun x) (fun _ => 0) := by
  obtain ⟨v, hv, hvnonneg, hvmass, hvenergy⟩ := exists_abs_h10_preserving_energy hU hfin w
  have hnormv : weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 := by
    simpa only [weightedL2Pairing, mul_assoc, ← pow_two] using (hvmass ρ).trans
      (by simpa only [weightedL2Pairing, mul_assoc, ← pow_two] using hnorm)
  have henergy : dirichletEnergyPairing A v.toH1Function v.toH1Function =
      dirichletEnergyPairing A w.toH1Function w.toH1Function := by
    simpa only [dirichletEnergyPairing, PDE.vecDot_comm] using hvenergy A
  have hlower := rayleigh_lower_bound_of_normalized_minimum hU.measurableSet hA hρnonneg hmin
  refine ⟨v, hv, hvnonneg, hnormv, henergy, hlower, ?_⟩
  apply rayleigh_minimizer_weak_solution hA hAsymm hρ v hlower
  rw [henergy, hnormv, mul_one]


/-- A zero-trace vector with weighted square norm one has strictly positive
actual Dirichlet energy on a bounded open convex domain. This uses the
proved zero-trace Poincaré inequality, not positivity of an eigenfunction. -/
theorem dirichletEnergyPairing_pos_of_normalized {d : ℕ} [NeZero d]
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {κ : ℝ} (hκ : 0 < κ) {A : CoeffField d}
    (hA : IsEllipticFieldOn κ κ⁻¹ U A) {ρ : Vec d → ℝ}
    (w : Homogenization.H10Function U)
    (hnorm : weightedL2Pairing ρ w.toH1Function w.toH1Function = 1) :
    0 < dirichletEnergyPairing A w.toH1Function w.toH1Function := by
  have hE := dirichletEnergyPairing_self_nonneg hU.isOpen.measurableSet hA w.toH1Function
  apply lt_of_le_of_ne hE
  intro heq
  have hgradint := integrableOn_vecNormSq_of_memVectorL2On w.toH1Function.gradMemL2
  have hbound : κ * (∫ x in U, vecNormSq (w.toH1Function.grad x)) ≤
      dirichletEnergyPairing A w.toH1Function w.toH1Function := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hgradint.const_mul κ)
      (dirichletEnergyPairing_integrable hA w.toH1Function w.toH1Function)
    filter_upwards [ae_restrict_mem hU.isOpen.measurableSet] with x hx
    simpa only [PDE.vecDot_comm] using (hA.elliptic hx).coercive (w.toH1Function.grad x)
  have hg0 : (∫ x in U, vecNormSq (w.toH1Function.grad x)) = 0 := by
    have hgn : 0 ≤ ∫ x in U, vecNormSq (w.toH1Function.grad x) :=
      integral_nonneg fun x => vecNormSq_nonneg _
    rw [← heq] at hbound
    nlinarith only [hbound, hκ, hgn]
  have hga : ∀ᵐ x ∂volumeOn U, w.toH1Function.grad x = 0 := by
    have hz := (integral_eq_zero_iff_of_nonneg (fun x => vecNormSq_nonneg
      (w.toH1Function.grad x)) hgradint).mp hg0
    filter_upwards [hz] with x hx
    exact PDE.vecNormSq_eq_zero hx
  have hgclass : w.toH1Function.gradToVectorL2 = 0 := by
    apply Lp.ext
    filter_upwards [w.toH1Function.coeFn_gradToVectorL2, hga,
      Lp.coeFn_zero (E := Homogenization.Vec d) (p := 2)
        (μ := volumeOn U)] with x hx hg hz
    rw [hx, hg, hz]
    rfl
  have hwclass := Homogenization.H10Function.toScalarL2_eq_zero_of_gradToVectorL2_eq_zero_of_exists_poincare_constant
    (Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hU)
    w hgclass
  have hwzero : ∀ᵐ x ∂volumeOn U, w.toH1Function.toFun x = 0 := by
    have hc := w.toH1Function.coeFn_toScalarL2
    rw [hwclass] at hc
    filter_upwards [hc, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := volumeOn U)] with x hx hz
    exact hx.symm.trans hz
  have hm0 : weightedL2Pairing ρ w.toH1Function w.toH1Function = 0 := by
    unfold weightedL2Pairing
    calc
      _ = ∫ _x in U, (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [hwzero] with x hx
        simp only [hx, mul_zero]
      _ = 0 := by simp only [integral_zero]
  exact zero_ne_one (hm0.symm.trans hnorm)



/-- A diverging spectral enumeration has an attained minimum, independently of
its order. This does not assert the all-vector Rayleigh inequality. -/
theorem exists_minimum_of_tendsto_atTop (eigenvalue : ℕ → ℝ)
    (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop) :
    ∃ n, ∀ k, eigenvalue n ≤ eigenvalue k := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hlim.eventually (Filter.eventually_ge_atTop (eigenvalue 0)))
  obtain ⟨n, hn, hmin⟩ := Set.exists_min_image (Set.Iic N) eigenvalue
    (Set.finite_Iic N) ⟨0, Nat.zero_le N⟩
  refine ⟨n, fun k => ?_⟩
  by_cases hk : k ≤ N
  · exact hmin k hk
  · exact (hmin 0 (Nat.zero_le N)).trans (hN k (by omega))

/-- Conditional variational producer on the actual anisotropic domain: once
attainment on the weighted unit sphere is proved, its absolute value supplies a
normalized nonnegative weak eigenfunction with positive eigenvalue and the
all-vector Rayleigh inequality. Attainment is explicitly an input. -/
theorem exists_positive_nonnegative_normalized_rayleigh_eigenfunction
    {d : ℕ} [NeZero d] {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    (hfin : volume U ≠ ⊤) {κ : ℝ} (hκ : 0 < κ)
    {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (hρnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x)
    (w : Homogenization.H10Function U)
    (hnorm : weightedL2Pairing ρ w.toH1Function w.toH1Function = 1)
    (hmin : ∀ z : Homogenization.H10Function U,
      weightedL2Pairing ρ z.toH1Function z.toH1Function = 1 →
        dirichletEnergyPairing A w.toH1Function w.toH1Function ≤
          dirichletEnergyPairing A z.toH1Function z.toH1Function) :
    ∃ (eigenvalue : ℝ) (v : Homogenization.H10Function U),
      0 < eigenvalue ∧ (∀ x, 0 ≤ v.toH1Function.toFun x) ∧
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 ∧
      dirichletEnergyPairing A v.toH1Function v.toH1Function = eigenvalue ∧
      (∀ z : Homogenization.H10Function U,
        eigenvalue * weightedL2Pairing ρ z.toH1Function z.toH1Function ≤
          dirichletEnergyPairing A z.toH1Function z.toH1Function) ∧
      IsWeakSolutionOn A U v.toH1Function
        (fun x => eigenvalue * ρ x * v.toH1Function.toFun x) (fun _ => 0) := by
  obtain ⟨v, _hv, hvnonneg, hnormv, henergy, hlower, hweak⟩ :=
    exists_nonnegative_normalized_rayleigh_minimizer hU.isOpen hfin hA hAsymm hρ
      hρnonneg w hnorm hmin
  exact ⟨dirichletEnergyPairing A w.toH1Function w.toH1Function, v,
    dirichletEnergyPairing_pos_of_normalized hU hκ hA w hnorm,
    hvnonneg, hnormv, henergy, hlower, hweak⟩

/-- A compact positive energy inverse attains the Rayleigh minimum. The lower
bound tests the nonnegative energy at `v - μ⁻¹ S (J v)`, and therefore applies
to every energy-space vector rather than only to an enumerated eigenbasis. -/
theorem exists_normalized_rayleigh_minimizer_of_compact_inverse
    {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (B : V →L[ℝ] V →L[ℝ] ℝ) (J : V →L[ℝ] H) (S : H →L[ℝ] V)
    (hBnonneg : ∀ v, 0 ≤ B v v) (hBsymm : ∀ u v, B u v = B v u)
    (hsolve : ∀ f v, B (S f) v = inner ℝ f (J v))
    (hcompact : IsCompactOperator (J.comp S)) (hsa : IsSelfAdjoint (J.comp S))
    (hpos : ∀ f, f ≠ 0 → 0 < inner ℝ f (J (S f)))
    (hne : J.comp S ≠ 0) :
    ∃ (eigenvalue : ℝ) (u : V), 0 < eigenvalue ∧ ‖J u‖ = 1 ∧
      B u u = eigenvalue ∧
      (∀ v : V, eigenvalue * ‖J v‖ ^ 2 ≤ B v v) ∧
      ∀ v : V, B u v = eigenvalue * inner ℝ (J u) (J v) := by
  obtain ⟨μ, e, hμnorm, henorm, he⟩ :=
    TubeProbability.CompactSpectrum.aux_exists_eigenvector_of_compact_selfAdjoint
      (J.comp S) hsa hcompact hne
  have he0 : e ≠ 0 := by
    intro hz
    simpa [hz] using henorm
  have hμ : 0 < μ := by
    have hp := hpos e he0
    change 0 < inner ℝ e ((J.comp S) e) at hp
    simpa only [he, real_inner_smul_right, real_inner_self_eq_norm_sq,
      henorm, one_pow, mul_one] using hp
  have hμeq : μ = ‖J.comp S‖ := by
    rcases hμnorm with hp | hn
    · exact hp
    · have := norm_nonneg (J.comp S)
      exfalso
      linarith
  let u := S (μ⁻¹ • e)
  have hJu : J u = e := by
    change J (S (μ⁻¹ • e)) = e
    rw [map_smul, map_smul]
    change μ⁻¹ • ((J.comp S) e) = e
    rw [he, smul_smul, inv_mul_cancel₀ hμ.ne', one_smul]
  have hweak (v : V) : B u v = μ⁻¹ * inner ℝ (J u) (J v) := by
    rw [hJu]
    exact (hsolve (μ⁻¹ • e) v).trans (real_inner_smul_left _ _ _)
  refine ⟨μ⁻¹, u, inv_pos.mpr hμ, ?_, ?_, ?_, hweak⟩
  · rw [hJu, henorm]
  · rw [hweak, real_inner_self_eq_norm_sq, hJu, henorm, one_pow, mul_one]
  · intro v
    let w := S (J v)
    have hwv : B w v = ‖J v‖ ^ 2 := by
      rw [hsolve, real_inner_self_eq_norm_sq]
    have hvw : B v w = ‖J v‖ ^ 2 := (hBsymm v w).trans hwv
    have hww : B w w ≤ μ * ‖J v‖ ^ 2 := by
      rw [hsolve]
      calc
        inner ℝ (J v) (J w) ≤ ‖J v‖ * ‖J w‖ := real_inner_le_norm _ _
        _ ≤ ‖J v‖ * (‖J.comp S‖ * ‖J v‖) :=
          mul_le_mul_of_nonneg_left ((J.comp S).le_opNorm (J v)) (norm_nonneg _)
        _ = μ * ‖J v‖ ^ 2 := by rw [← hμeq]; ring
    have hq := hBnonneg (v - μ⁻¹ • w)
    have hexpand : B (v - μ⁻¹ • w) (v - μ⁻¹ • w) =
        B v v - 2 * μ⁻¹ * ‖J v‖ ^ 2 + (μ⁻¹) ^ 2 * B w w := by
      simp only [map_sub, map_smul, sub_apply,
        smul_apply, smul_eq_mul, hwv, hvw]
      ring
    rw [hexpand] at hq
    have hupper : (μ⁻¹) ^ 2 * B w w ≤ μ⁻¹ * ‖J v‖ ^ 2 := by
      calc
        (μ⁻¹) ^ 2 * B w w ≤ (μ⁻¹) ^ 2 * (μ * ‖J v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hww (sq_nonneg _)
        _ = μ⁻¹ * ‖J v‖ ^ 2 := by field_simp
    linarith

/-- The actual weighted Euclidean source ball has a positive normalized first
energy eigenvector and the Rayleigh lower bound over the whole completed
Dirichlet energy space. No ordering of spectral indices is used. -/
theorem exists_dirichletHilbert_rayleigh_minimizer {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : EinsteinRelation.Vec d → ℝ}
    {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := TubeProbability.dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℝ) (u : TubeProbability.DirichletHilbertSpace (d := d) R hR),
      0 < eigenvalue ∧ ‖J u‖ = 1 ∧
      (∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
        EinsteinRelation.dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => u.val (some i) x)) = eigenvalue ∧
      (∀ v : TubeProbability.DirichletHilbertSpace (d := d) R hR,
        eigenvalue * ‖J v‖ ^ 2 ≤
          ∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
            EinsteinRelation.dot ((α x).mulVec (fun i => v.val (some i) x))
              (fun i => v.val (some i) x)) ∧
      ∀ v : TubeProbability.DirichletHilbertSpace (d := d) R hR,
        (∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R,
          EinsteinRelation.dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue * inner ℝ (J u) (J v) := by
  dsimp only
  let J := TubeProbability.dirichletHilbertInclusion ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1)
  obtain ⟨c, hc, B, hbound, hform⟩ :=
    TubeProbability.exists_dirichletHilbert_energyForm hd hκ h R hR
  obtain ⟨_c, _hc, S, hcompact, hsa, hinj, _hdense, hpos, _hnorm, hvar⟩ :=
    TubeProbability.exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  have hnonneg (v : TubeProbability.DirichletHilbertSpace (d := d) R hR) :
      0 ≤ B v v := (mul_nonneg hc.le (sq_nonneg _)).trans (hbound v)
  have hsymm (u v : TubeProbability.DirichletHilbertSpace (d := d) R hR) :
      B u v = B v u := by
    rw [hform, hform]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have hsym : (α x).IsSymm := (h.2.2 x).2.2.1
      have he := hsym.dotProduct_mulVec_comm
        (x := fun i => v.val (some i) x) (y := fun i => u.val (some i) x)
      rw [dotProduct_comm, dotProduct_comm (fun i => u.val (some i) x)] at he
      exact he
  have hsolve (f : Lp ℝ 2 (EinsteinFull.External.Source.GMP.dirichletVolume ρ R))
      (v : TubeProbability.DirichletHilbertSpace (d := d) R hR) :
      B (S f) v = inner ℝ f (J v) := by
    rw [hform]
    exact (hvar f (S f)).mp rfl v
  have hne : J.comp S ≠ 0 := by
    intro hz
    haveI : Subsingleton (Lp ℝ 2 (EinsteinFull.External.Source.GMP.dirichletVolume ρ R)) :=
      ⟨fun f g => hinj (by change (J.comp S) f = (J.comp S) g; rw [hz]; rfl)⟩
    exact TubeProbability.not_finiteDimensional_dirichletVolume
      (by omega) hκ h R hR (inferInstance)
  obtain ⟨eigenvalue, u, heigenvalue, hunorm, hue, hlower, hweak⟩ :=
    exists_normalized_rayleigh_minimizer_of_compact_inverse B J S hnonneg hsymm
      hsolve hcompact hsa hpos hne
  refine ⟨eigenvalue, u, heigenvalue, hunorm, ?_, ?_, ?_⟩
  · rw [← hform]
    exact hue
  · intro v
    rw [← hform]
    exact hlower v
  · intro v
    rw [← hform]
    exact hweak v

section DirichletTransport

open SubdiffusiveProcess TubeProbability

/-- Continuous restriction of the cube coordinate classes to the actual source ball. -/
noncomputable def sourceBallL2Restriction {d : ℕ} (R : ℝ) (hR : 0 < R) :
    DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))
      →L[ℝ] DomainL2 (dirichletBall (d := d) R) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    rw [one_smul]
    apply Measure.restrict_mono_set
    exact sourceBall_subset_cube R hR)

/-- Restriction keeps the original cube representative almost everywhere. -/
theorem sourceBallL2Restriction_coe {d : ℕ} (R : ℝ) (hR : 0 < R)
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR))) :
    (sourceBallL2Restriction R hR f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] f := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (show volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d)) ≤
        1 • volume.restrict (centeredCube (0 : SpatialCoordinates d) (2 * R)
          (mul_pos two_pos hR) : Set (SpatialCoordinates d)) by
      rw [one_smul]
      apply Measure.restrict_mono_set
      exact sourceBall_subset_cube R hR) f

/-- The value and all coordinate gradients, restricted to the source ball. -/
noncomputable def dirichletHilbertBallData {d : ℕ} (R : ℝ) (hR : 0 < R) :
    HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR)) →L[ℝ] SobolevData (dirichletBall (d := d) R) :=
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let L := sourceBallL2Restriction (d := d) R hR
  ((L.comp (ContinuousLinearMap.fst ℝ (DomainL2 Q) (Fin d → DomainL2 Q))).prod
    (ContinuousLinearMap.pi fun i : Fin d =>
      L.comp ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ (DomainL2 Q) (Fin d → DomainL2 Q))))).comp
      (hilbertToSobolev Q)

/-- Restriction preserves the closure of smooth ball-supported data, including
its zero trace on the ball itself. -/
theorem dirichletHilbertBallData_mem_killedSobolevGraph {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR) :
    dirichletHilbertBallData R hR u.val ∈ killedSobolevGraph (dirichletBall R) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let L := sourceBallL2Restriction (d := d) R hR
  let F := dirichletHilbertBallData (d := d) R hR
  have hrep (f : DomainL2 Q) :
      (L f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] f :=
    sourceBallL2Restriction_coe R hR f
  have hmap (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
      F (dirichletSmoothData R hR φ) = smoothSobolevData φ := by
    apply Prod.ext
    · change L (testL2 (dirichletTestInCube R hR φ)) = testL2 φ
      apply Lp.ext
      have ht : (testL2 (dirichletTestInCube R hR φ) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] φ :=
        ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR)
          (testL2_coeFn (dirichletTestInCube R hR φ))
      filter_upwards [hrep (testL2 (dirichletTestInCube R hR φ)), ht,
        testL2_coeFn φ] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
    · funext i
      change L (testPartialL2 (dirichletTestInCube R hR φ) i) = testPartialL2 φ i
      apply Lp.ext
      have ht : (testPartialL2 (dirichletTestInCube R hR φ) i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
            (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
        ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR)
          (testPartialL2_coeFn (dirichletTestInCube R hR φ) i)
      filter_upwards [hrep (testPartialL2 (dirichletTestInCube R hR φ) i), ht,
        testPartialL2_coeFn φ i] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
  have hc : IsClosed ((killedSobolevGraph (dirichletBall (d := d) R)).comap
      F.toLinearMap : Set (HilbertSobolevData Q)) :=
    isClosed_killedSobolevGraph.preimage F.continuous
  have hrange : LinearMap.range (dirichletSmoothData R hR) ≤
      (killedSobolevGraph (dirichletBall R)).comap F.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    apply Submodule.mem_comap.mpr
    rw [show F.toLinearMap (dirichletSmoothData R hR φ) = smoothSobolevData φ from hmap φ]
    exact smoothSobolevData_mem_killed φ
  exact (Submodule.topologicalClosure_minimal _ hrange hc) u.property

/-- Every vector in the completed source-ball energy space has an actual native
H10 representative on that same ball, preserving values and gradients a.e. -/
theorem exists_nativeH10_of_dirichletHilbert {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ v : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R),
      v.toH1Function.toFun =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
        (fun x => u.val none x) ∧
      ∀ i : Fin d, (fun x => v.toH1Function.grad x i)
        =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] (fun x => u.val (some i) x) := by
  obtain ⟨v, hv, hg⟩ := exists_nativeH10Function_of_killedSobolevGraph
    ⟨dirichletHilbertBallData R hR u.val,
      dirichletHilbertBallData_mem_killedSobolevGraph R hR u⟩
  refine ⟨v, ?_, ?_⟩
  · rw [show v.toH1Function.toFun = _ from hv]
    exact sourceBallL2Restriction_coe R hR (u.val none)
  · intro i
    rw [hg]
    exact sourceBallL2Restriction_coe R hR (u.val (some i))

/-- Every native H10 function on the source ball belongs to the completed
Dirichlet energy space after zero extension to its containing cube. The same
smooth ball-supported sequence witnesses membership in the completion. -/
theorem exists_dirichletHilbert_of_nativeH10 {d : ℕ}
    (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function
      (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (fun x => u.val none x) =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
        v.toH1Function.toFun ∧
      ∀ i : Fin d, (fun x => u.val (some i) x)
        =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] (fun x => v.toH1Function.grad x i) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let w := v.extendByZeroToOpenSuperset (dirichletBall R).isOpen.measurableSet
    Q.isOpen (sourceBall_subset_cube R hR)
  let φ : ℕ → TestFunction (dirichletBall (d := d) R) ℝ ⊤ := fun n =>
    ⟨v.approx n, v.approx_smooth n, v.approx_hasCompactSupport n,
      v.approx_support_subset n⟩
  let f : SobolevData Q :=
    (w.toH1Function.memL2.toLp _, fun i => (w.toH1Function.gradMemL2 i).toLp _)
  have hval : Filter.Tendsto
      (fun n => (smoothSobolevData (dirichletTestInCube R hR (φ n))).1)
      Filter.atTop (nhds f.1) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (dirichletTestInCube R hR (φ n) : SpatialCoordinates d → ℝ))
      (fun n => (dirichletTestInCube R hR (φ n)).contDiff.continuous.memLp_of_hasCompactSupport
        (dirichletTestInCube R hR (φ n)).hasCompactSupport)
      w.toH1Function.toFun w.toH1Function.memL2).mpr w.tendsto_approx
  have hgrad (i : Fin d) : Filter.Tendsto
      (fun n => (smoothSobolevData (dirichletTestInCube R hR (φ n))).2 i)
      Filter.atTop (nhds (f.2 i)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => fderiv ℝ (dirichletTestInCube R hR (φ n) : SpatialCoordinates d → ℝ)
        x (Pi.single i 1))
      (fun n => ((dirichletTestInCube R hR (φ n)).contDiff.continuous_fderiv_apply
        (by simp)).comp (continuous_id.prodMk continuous_const)
        |>.memLp_of_hasCompactSupport
          ((dirichletTestInCube R hR (φ n)).hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)))
      (fun x => w.toH1Function.grad x i) (w.toH1Function.gradMemL2 i)).mpr
    change Filter.Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (v.approx n) x (Pi.single i 1) - w.toH1Function.grad x i)
      2 (volume.restrict (Q : Set (SpatialCoordinates d)))) Filter.atTop (nhds 0)
    exact w.tendsto_approx_grad i
  have hlim : Filter.Tendsto (fun n => dirichletSmoothData R hR (φ n))
      Filter.atTop (nhds (sobolevToHilbert Q f)) :=
    (sobolevToHilbert Q).continuous.continuousAt.tendsto.comp
      (hval.prodMk_nhds (tendsto_pi_nhds.mpr hgrad))
  have hmem : sobolevToHilbert Q f ∈ dirichletHilbertSubmodule R hR := by
    change sobolevToHilbert Q f ∈
      closure (Set.range (dirichletSmoothData (d := d) R hR))
    apply mem_closure_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => ⟨φ n, rfl⟩
  let u : DirichletHilbertSpace (d := d) R hR := ⟨sobolevToHilbert Q f, hmem⟩
  refine ⟨u, ?_, ?_⟩
  · have hv : (fun x => u.val none x) =ᵐ[volume.restrict (Q : Set _)]
        w.toH1Function.toFun := MemLp.coeFn_toLp w.toH1Function.memL2
    have hvball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) hv
    filter_upwards [hvball, ae_restrict_mem (dirichletBall R).isOpen.measurableSet]
      with x hx hxb
    rw [hx]
    exact Set.indicator_of_mem hxb _
  · intro i
    have hg : (fun x => u.val (some i) x) =ᵐ[volume.restrict (Q : Set _)]
        (fun x => w.toH1Function.grad x i) :=
      MemLp.coeFn_toLp (w.toH1Function.gradMemL2 i)
    have hgball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) hg
    filter_upwards [hgball, ae_restrict_mem (dirichletBall R).isOpen.measurableSet]
      with x hx hxb
    rw [hx]
    change ((dirichletBall (d := d) R : Set _).indicator v.toH1Function.grad) x i = _
    rw [Set.indicator_of_mem hxb]

/-- The weighted inclusion norm is the literal native weighted L2 mass. -/
theorem dirichletHilbert_norm_sq_eq_weightedL2Pairing {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : EinsteinRelation.Vec d → ℝ}
    {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (v : Homogenization.H10Function (EinsteinFull.External.Source.GMP.sourceBall 0 R))
    (hv : v.toH1Function.toFun =ᵐ[volume.restrict
      (dirichletBall (d := d) R : Set (SpatialCoordinates d))] (fun x => u.val none x)) :
    ‖dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u‖ ^ 2 =
      weightedL2Pairing ρ v.toH1Function v.toH1Function := by
  have hac : volume.restrict (EinsteinFull.External.Source.GMP.sourceBall 0 R) ≪
      EinsteinFull.External.Source.GMP.dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hJu := hac.ae_le (dirichletHilbertInclusion_coe ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) u)
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  change (∫ x, _ ∂(volume.restrict
    (EinsteinFull.External.Source.GMP.sourceBall 0 R)).withDensity
      (fun x => ENNReal.ofReal (ρ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hJu, hv] with x hx hvx
  simp only [RCLike.inner_apply, conj_trivial,
    ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
  change ρ x * (_ * _) = ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x
  rw [hx]
  change ρ x * (u.val none x * u.val none x) =
    ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x
  rw [← hvx]
  ring

/-- Native and completed representatives have the same anisotropic energy. -/
theorem dirichletHilbert_energy_eq_dirichletEnergyPairing {d : ℕ}
    (R : ℝ) (hR : 0 < R) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (u : DirichletHilbertSpace (d := d) R hR)
    (v : Homogenization.H10Function (EinsteinFull.External.Source.GMP.sourceBall 0 R))
    (hg : ∀ i : Fin d, (fun x => v.toH1Function.grad x i)
      =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
        (fun x => u.val (some i) x)) :
    (∫ x in EinsteinFull.External.Source.GMP.sourceBall 0 R,
      EinsteinRelation.dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => u.val (some i) x)) =
      dirichletEnergyPairing α v.toH1Function v.toH1Function := by
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr hg] with x hx
  have he : (fun i => u.val (some i) x) = v.toH1Function.grad x :=
    funext fun i => (hx i).symm
  rw [he]
  rfl

/-- Attainment and the all-vector Rayleigh bound on actual native H10 functions
on the anisotropic weighted Euclidean source ball. -/
theorem exists_nativeH10_sourceBall_rayleigh_minimizer {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : EinsteinRelation.Vec d → ℝ}
    {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (eigenvalue : ℝ) (u : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)),
      0 < eigenvalue ∧ weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      dirichletEnergyPairing α u.toH1Function u.toH1Function = eigenvalue ∧
      ∀ v : Homogenization.H10Function (EinsteinFull.External.Source.GMP.sourceBall 0 R),
        eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
          dirichletEnergyPairing α v.toH1Function v.toH1Function := by
  obtain ⟨eigenvalue, u, heigenvalue, hunorm, huenergy, hlower, _hweak⟩ :=
    exists_dirichletHilbert_rayleigh_minimizer hd hκ h R hR
  obtain ⟨v, hv, hvg⟩ := exists_nativeH10_of_dirichletHilbert R hR u
  have hmass := dirichletHilbert_norm_sq_eq_weightedL2Pairing hκ h R hR u v hv
  have henergy := dirichletHilbert_energy_eq_dirichletEnergyPairing R hR α u v hvg
  refine ⟨eigenvalue, v, heigenvalue, ?_, henergy.symm.trans huenergy, ?_⟩
  · rw [← hmass, hunorm, one_pow]
  · intro z
    obtain ⟨w, hw, hwg⟩ := exists_dirichletHilbert_of_nativeH10 R hR z
    have hzmass := dirichletHilbert_norm_sq_eq_weightedL2Pairing hκ h R hR w z hw.symm
    have hzenergy := dirichletHilbert_energy_eq_dirichletEnergyPairing R hR α w z
      (fun i => (hwg i).symm)
    rw [← hzmass, ← hzenergy]
    exact hlower w

/-- Source symmetric ellipticity implies the native inverse-coercivity
convention, with the safe internal lower scale `κ ^ 3`. -/
theorem source_uniformlyElliptic_isEllipticFieldOn {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : EinsteinRelation.Vec d → ℝ}
    {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    {U : Set (EinsteinRelation.Vec d)} (hU : MeasurableSet U) :
    PDE.IsEllipticFieldOn (κ ^ 3) (κ ^ 3)⁻¹ U α := by
  classical
  have hk1 := (TubeProbability.DimensionLift.lifted_ellipticity_scale_comparison hκ h).1
  have hk3 : κ ^ 3 ≤ κ := by
    have hk2 := mul_le_mul_of_nonneg_left hk1 hκ.le
    nlinarith [mul_le_mul_of_nonneg_left hk2 hκ.le]
  refine ⟨?_, ?_⟩
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hm : Measurable (fun x => α x i j) := by
      let : MeasurableSpace (EinsteinRelation.Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      let : BorelSpace (EinsteinRelation.Mat d) := EinsteinRelation.instBorelSpaceMat d
      exact ((continuous_id : Continuous (id : EinsteinRelation.Mat d → EinsteinRelation.Mat d)).matrix_elem i j).measurable.comp h.2.1
    exact hm.piecewise hU measurable_const
  · intro x _hx
    refine ⟨pow_pos hκ 3,
      hk3.trans (TubeProbability.DimensionLift.lifted_ellipticity_scale_comparison hκ h).2, ?_, ?_⟩
    · intro ξ
      have hb : κ * PDE.vecNormSq ξ ≤ PDE.vecDot ξ (PDE.matVecMul (α x) ξ) := by
        simpa only [PDE.vecNormSq, PDE.vecDot, PDE.matVecMul,
          Matrix.mulVec, dotProduct, EinsteinRelation.dot,
          EinsteinRelation.euclideanSq, pow_two] using ((h.2.2 x).2.2.2 ξ).1
      exact (mul_le_mul_of_nonneg_right hk3 (PDE.vecNormSq_nonneg ξ)).trans hb
    · intro ξ
      simpa only [inv_inv, PDE.vecNormSq, PDE.vecDot, PDE.matVecMul,
        Matrix.mulVec, dotProduct, EinsteinRelation.dot,
        EinsteinRelation.euclideanSq, pow_two] using
        TubeProbability.DimensionLift.inverse_quadratic_lower hκ (α x) (h.2.2 x).2.2.1
          (fun ξ => ((h.2.2 x).2.2.2 ξ).1)
          (fun ξ => ((h.2.2 x).2.2.2 ξ).2) ξ

/-- The actual anisotropic weighted source ball has a positive first Rayleigh
eigenvalue and a normalized nonnegative native weak eigenfunction. The
all-vector inequality is retained for every native H10 test. -/
theorem exists_sourceBall_first_nonnegative_weak_eigenfunction {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : EinsteinRelation.Vec d → ℝ}
    {α : EinsteinRelation.Vec d → EinsteinRelation.Mat d}
    (h : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (eigenvalue : ℝ) (u : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)),
      0 < eigenvalue ∧ (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      dirichletEnergyPairing α u.toH1Function u.toH1Function = eigenvalue ∧
      (∀ v : Homogenization.H10Function (EinsteinFull.External.Source.GMP.sourceBall 0 R),
        eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
          dirichletEnergyPairing α v.toH1Function v.toH1Function) ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (EinsteinFull.External.Source.GMP.sourceBall 0 R)
        u.toH1Function (fun x => eigenvalue * ρ x * u.toH1Function.toFun x)
        (fun _ => 0) := by
  obtain ⟨eigenvalue, w, heigenvalue, hnorm, heq, hlower⟩ :=
    exists_nativeH10_sourceBall_rayleigh_minimizer hd hκ h R hR
  have hU : IsOpen (EinsteinFull.External.Source.GMP.sourceBall
      (0 : EinsteinRelation.Vec d) R) := (dirichletBall (d := d) R).isOpen
  have hfin : volume (EinsteinFull.External.Source.GMP.sourceBall
      (0 : EinsteinRelation.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (sourceBall_subset_cube R hR))
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ h hU.measurableSet
  have hρ := (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ h
    (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall 0 R))).1
  have hmin (z : Homogenization.H10Function
      (EinsteinFull.External.Source.GMP.sourceBall 0 R))
      (hz : weightedL2Pairing ρ z.toH1Function z.toH1Function = 1) :
      dirichletEnergyPairing α w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing α z.toH1Function z.toH1Function := by
    rw [heq]
    simpa only [hz, mul_one] using hlower z
  obtain ⟨v, _hvabs, hvnonneg, hvnorm, hvenergy, hvlower, hvweak⟩ :=
    exists_nonnegative_normalized_rayleigh_minimizer hU hfin hA
      (ae_of_all _ fun x => (h.2.2 x).2.2.1) hρ
      (ae_of_all _ fun x => hκ.le.trans (h.2.2 x).1) w hnorm hmin
  refine ⟨eigenvalue, v, heigenvalue, hvnonneg, hvnorm, hvenergy.trans heq, ?_, ?_⟩
  · simpa only [heq] using hvlower
  · simpa only [heq] using hvweak


end DirichletTransport

/-- Normalizing the actual geometric tail by the square of the target
amplitude leaves a recurrence coefficient independent of that amplitude. -/
theorem normalized_geometric_tail_step {β C K T Tnext : ℝ}
    (hβ : 0 ≤ β) (hK : 0 < K) (hT : 0 ≤ T) (n : ℕ)
    (hstep : Tnext ≤ C * (4 : ℝ) ^ n * T *
      (T / (K / (4 * (2 : ℝ) ^ n)) ^ 2) ^ β) :
    Tnext / K ^ 2 ≤ (C * (16 : ℝ) ^ β) *
      ((4 : ℝ) ^ (1 + β)) ^ (n : ℝ) * (T / K ^ 2) ^ (1 + β) := by
  have ht : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have ht2 : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hquot : T / (K / (4 * (2 : ℝ) ^ n)) ^ 2 =
      16 * (4 : ℝ) ^ n * (T / K ^ 2) := by
    rw [div_pow, mul_pow, ht2]
    field_simp
    <;> ring
  have hX : 0 ≤ T / K ^ 2 := div_nonneg hT (sq_nonneg K)
  have hF : (4 : ℝ) ^ n * ((4 : ℝ) ^ n) ^ β =
      ((4 : ℝ) ^ (1 + β)) ^ (n : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 4),
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  calc
    Tnext / K ^ 2 ≤ (C * (4 : ℝ) ^ n * T *
        (T / (K / (4 * (2 : ℝ) ^ n)) ^ 2) ^ β) / K ^ 2 :=
      div_le_div_of_nonneg_right hstep (sq_nonneg K)
    _ = _ := by
      rw [hquot, Real.mul_rpow (by positivity : (0 : ℝ) ≤ 16 * (4 : ℝ) ^ n) hX,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n),
        Real.rpow_add_of_nonneg hX (by norm_num : (0 : ℝ) ≤ 1) hβ, Real.rpow_one]
      rw [← hF]
      ring

/-- Vanishing geometric positive-tail masses give the spatial almost-everywhere
bound on the limiting ball; all integrability comes from the actual H¹ vector. -/
theorem ae_le_of_ball_tail_tendsto_zero {d : ℕ} {U : Set (Vec d)}
    (w : Homogenization.H1Function U) (z : Vec d) {r K : ℝ} (hr : 0 ≤ r) (hK : 0 ≤ K)
    (radius level : ℕ → ℝ) (hradius : ∀ n, r ≤ radius n)
    (hlevel : ∀ n, 0 ≤ level n ∧ level n ≤ K)
    (hlim : Filter.Tendsto (fun n => ∫ x in U ∩ euclideanBall z (radius n),
      max (w.toFun x - level n) 0 ^ 2) Filter.atTop (𝓝 0)) :
    ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z r), w.toFun x ≤ K := by
  have hle (n : ℕ) : (∫ x in U ∩ euclideanBall z r,
      max (w.toFun x - K) 0 ^ 2) ≤
      ∫ x in U ∩ euclideanBall z (radius n), max (w.toFun x - level n) 0 ^ 2 := by
    have hsmall : U ∩ euclideanBall z r ⊆ U ∩ euclideanBall z (radius n) :=
      Set.inter_subset_inter_right U (euclideanBall_mono hr (hradius n))
    have hint := (memL2On_positivePart_of_nonneg w (hlevel n).1).integrable_sq
    calc
      _ ≤ ∫ x in U ∩ euclideanBall z r, max (w.toFun x - level n) 0 ^ 2 := by
        apply integral_mono_ae
          ((memL2On_positivePart_of_nonneg w hK).integrable_sq.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
          (hint.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
        exact Filter.Eventually.of_forall fun x => pow_le_pow_left₀ (le_max_right _ _)
          (max_le_max (sub_le_sub_left (hlevel n).2 _) le_rfl) 2
      _ ≤ _ := setIntegral_mono_set (hint.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hsmall hx)
  have hz : (∫ x in U ∩ euclideanBall z r, max (w.toFun x - K) 0 ^ 2) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hle) (integral_nonneg fun x => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _)
    ((memL2On_positivePart_of_nonneg w hK).integrable_sq.mono_measure
      (Measure.restrict_mono Set.inter_subset_left le_rfl))).mp hz
  filter_upwards [hae] with x hx
  have hzero := (pow_eq_zero_iff two_ne_zero).mp hx
  linarith only [le_max_left (w.toFun x - K) 0, hzero]


/-- The geometric radii and levels used in the actual ball recurrence have
strictly positive gaps and a coefficient bounded by a fixed dyadic factor. -/
theorem geometric_ball_tail_coefficient {R K t p q : ℝ}
    (hR : 0 < R) (hK : 0 < K) (ht : 1 ≤ t) (hp : 0 ≤ p) :
    0 ≤ R + R / (2 * t) ∧
    R + R / (2 * t) < R + 3 * R / (4 * t) ∧
    R + 3 * R / (4 * t) < R + R / t ∧
    R + R / t ≤ 2 * R ∧
    0 ≤ K - K / (2 * t) ∧
    K - K / (2 * t) < K - K / (4 * t) ∧
    (K - K / (4 * t)) - (K - K / (2 * t)) = K / (4 * t) ∧
    p * ((K - K / (4 * t)) / ((K - K / (4 * t)) - (K - K / (2 * t)))) +
      q * ((32 / ((R + R / t) - (R + 3 * R / (4 * t)))) ^ 2 +
        (32 / ((R + 3 * R / (4 * t)) - (R + R / (2 * t)))) ^ 2) ≤
      (4 * p + 2 * q * (128 / R) ^ 2 + 1) * t ^ 2 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht0 : t ≠ 0 := htpos.ne'
  have hR0 : R ≠ 0 := hR.ne'
  have hK0 : K ≠ 0 := hK.ne'
  have hgap1 : (R + R / t) - (R + 3 * R / (4 * t)) = R / (4 * t) := by field_simp <;> ring
  have hgap2 : (R + 3 * R / (4 * t)) - (R + R / (2 * t)) = R / (4 * t) := by field_simp <;> ring
  have hgapK : (K - K / (4 * t)) - (K - K / (2 * t)) = K / (4 * t) := by field_simp <;> ring
  have hgap : 0 < R / (4 * t) := by positivity
  have hlevel : 0 ≤ K - K / (2 * t) := by
    have hh : K / (2 * t) ≤ K := (div_le_iff₀ (by positivity)).2 (by nlinarith)
    linarith only [hh]
  have hradius : R + R / t ≤ 2 * R := by
    have hh : R / t ≤ R := (div_le_iff₀ htpos).2 (by nlinarith)
    linarith only [hh]
  refine ⟨by positivity, by linarith only [hgap2, hgap],
    by linarith only [hgap1, hgap], hradius, hlevel,
    by linarith only [hgapK, div_pos hK (show 0 < 4 * t by positivity)], hgapK, ?_⟩
  rw [hgap1, hgap2, hgapK]
  have hratio : (K - K / (4 * t)) / (K / (4 * t)) = 4 * t - 1 := by
    field_simp
    <;> ring
  have hradiusratio : 32 / (R / (4 * t)) = (128 / R) * t := by field_simp <;> norm_num
  rw [hratio, hradiusratio, mul_pow]
  have htp : 4 * t - 1 ≤ 4 * t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have hh := mul_le_mul_of_nonneg_left htp hp
  nlinarith only [hh, sq_nonneg t]

/-- Source-independent numerical amplitude choice. The tail recurrence still
refers to the actual H¹ representative, radii and levels; its initial value
is obtained from the genuine L² bound, rather than an added smallness premise. -/
theorem exists_ae_bound_of_geometric_ball_tails {β C L R : ℝ}
    (hβ : 0 < β) (hC : 0 < C) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} {U : Set (Vec d)}
      (w : Homogenization.H1Function U) (z : Vec d),
      (∫ x in U, w.toFun x ^ 2) ≤ L →
      (∀ n : ℕ,
        (∫ x in U ∩ euclideanBall z (R + R / (2 : ℝ) ^ (n + 1)),
          max (w.toFun x - (K - K / (2 * (2 : ℝ) ^ (n + 1)))) 0 ^ 2) ≤
        C * (4 : ℝ) ^ n *
          (∫ x in U ∩ euclideanBall z (R + R / (2 : ℝ) ^ n),
            max (w.toFun x - (K - K / (2 * (2 : ℝ) ^ n))) 0 ^ 2) *
          ((∫ x in U ∩ euclideanBall z (R + R / (2 : ℝ) ^ n),
            max (w.toFun x - (K - K / (2 * (2 : ℝ) ^ n))) 0 ^ 2) /
            (K / (4 * (2 : ℝ) ^ n)) ^ 2) ^ β) →
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), w.toFun x ≤ K := by
  let A0 : ℝ := C * (16 : ℝ) ^ β
  have hA0 : 0 < A0 := by positivity
  let D : ℝ := Real.sqrt ((A0 * ((4 : ℝ) ^ (1 + β)) ^ (1 / β)) ^ (1 / β)) ^ 2
  have hD : 0 ≤ D := sq_nonneg _
  let K : ℝ := Real.sqrt (D * L) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hKsq : D * L ≤ K ^ 2 := by
    have hs := Real.sq_sqrt (mul_nonneg hD hL)
    have hn := Real.sqrt_nonneg (D * L)
    dsimp only [K]
    nlinarith only [hs, hn]
  refine ⟨K, hK, ?_⟩
  intro d U w z hnorm hstep
  let radius : ℕ → ℝ := fun n => R + R / (2 : ℝ) ^ n
  let level : ℕ → ℝ := fun n => K - K / (2 * (2 : ℝ) ^ n)
  let T : ℕ → ℝ := fun n => ∫ x in U ∩ euclideanBall z (radius n),
    max (w.toFun x - level n) 0 ^ 2
  have hl (n : ℕ) : 0 ≤ level n ∧ level n ≤ K := by
    have ht : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hh := (geometric_ball_tail_coefficient hR hK ht (p := 0) (q := 0)
      le_rfl).2.2.2.2.1
    exact ⟨hh, sub_le_self K (by positivity)⟩
  have hT (n : ℕ) : 0 ≤ T n := integral_nonneg fun x => sq_nonneg _
  have hT0 : T 0 ≤ L := by
    have hint := (memL2On_positivePart_of_nonneg w (hl 0).1).integrable_sq
    calc
      T 0 ≤ ∫ x in U ∩ euclideanBall z (radius 0), w.toFun x ^ 2 := by
        apply integral_mono_ae (hint.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
          (w.memL2.integrable_sq.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl))
        exact Filter.Eventually.of_forall fun x => by
          have hh : max (w.toFun x - level 0) 0 ≤ |w.toFun x| :=
            max_le ((sub_le_self _ (hl 0).1).trans (le_abs_self _)) (abs_nonneg _)
          simpa only [sq_abs] using pow_le_pow_left₀ (le_max_right _ _) hh 2
      _ ≤ ∫ x in U, w.toFun x ^ 2 := setIntegral_mono_set w.memL2.integrable_sq
        (Filter.Eventually.of_forall fun x => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hx.1)
      _ ≤ L := hnorm
  let X : ℕ → ℝ := fun n => T n / K ^ 2
  have hX (n : ℕ) : 0 ≤ X n := div_nonneg (hT n) (sq_nonneg K)
  have hrec (n : ℕ) : X (n + 1) ≤ A0 * (1 : ℝ) ^ 2 *
      ((4 : ℝ) ^ (1 + β)) ^ (n : ℝ) * X n ^ (1 + β) := by
    simpa only [one_pow, mul_one, A0, X, T, radius, level] using
      normalized_geometric_tail_step hβ.le hK (hT n) n (hstep n)
  have hinit : Real.sqrt ((A0 * ((4 : ℝ) ^ (1 + β)) ^ (1 / β)) ^ (1 / β)) ^ 2 *
      ((1 : ℝ) ^ (1 / β)) ^ 2 * X 0 ≤ 1 := by
    simp only [Real.one_rpow, one_pow, mul_one]
    change D * (T 0 / K ^ 2) ≤ 1
    rw [← mul_div_assoc, div_le_one (sq_pos_of_pos hK)]
    exact (mul_le_mul_of_nonneg_left hT0 hD).trans hKsq
  have hlim := normalized_decay hβ hA0 (by norm_num : (0 : ℝ) < 1) hX hrec hinit
  have hTlim : Filter.Tendsto T Filter.atTop (𝓝 0) := by
    have hh := hlim.mul_const (K ^ 2)
    simpa only [X, div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos hK)), zero_mul] using hh
  apply ae_le_of_ball_tail_tendsto_zero w z hR.le hK.le radius level
    (fun n => le_add_of_nonneg_right (by positivity)) hl hTlim


/-- Specialization of the actual three-radius inequality to decreasing
geometric radii and increasing geometric levels. The amplitude is chosen
before the domain, coefficients, representative and ball centre. -/
theorem exists_ae_upper_of_three_radius_eigenfunction_tails
    {β S κ M eigenvalue L R : ℝ} (hβ : 0 < β) (hS : 0 ≤ S)
    (hκ : 0 < κ) (hM : 0 ≤ M) (heigenvalue : 0 ≤ eigenvalue)
    (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {d : ℕ} {U : Set (Vec d)}
      (w : Homogenization.H1Function U) (z : Vec d),
      (∫ x in U, w.toFun x ^ 2) ≤ L →
      (∀ {a r s k l : ℝ}, 0 ≤ a → a < r → r < s → s ≤ 2 * R →
        0 ≤ k → k < l →
        (∫ x in U ∩ euclideanBall z a, max (w.toFun x - l) 0 ^ 2) ≤
          S * (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
            4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2) *
          (∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) *
          ((∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) /
            (l - k) ^ 2) ^ β) →
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), w.toFun x ≤ K := by
  let p : ℝ := 4 * κ⁻¹ * eigenvalue * M
  let q : ℝ := 4 * κ⁻¹ ^ 2 + 1
  let D : ℝ := 4 * p + 2 * q * (128 / R) ^ 2 + 1
  have hp : 0 ≤ p := by positivity
  have hq : 0 ≤ q := by positivity
  have hD : 0 < D := by positivity
  obtain ⟨K, hK, hmain⟩ := exists_ae_bound_of_geometric_ball_tails
    hβ (mul_pos (show 0 < S + 1 by positivity) hD) hL hR
  refine ⟨K, hK, ?_⟩
  intro d U w z hnorm hstep
  apply hmain w z hnorm
  intro n
  let t : ℝ := (2 : ℝ) ^ n
  have ht : 1 ≤ t := one_le_pow₀ (by norm_num)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht2 : t ^ 2 = (4 : ℝ) ^ n := by
    dsimp only [t]
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  obtain ⟨ha, har, hrs, hs, hk, hkl, hgap, hc⟩ :=
    geometric_ball_tail_coefficient hR hK ht hp
  let a := R + R / (2 * t)
  let r := R + 3 * R / (4 * t)
  let s := R + R / t
  let k := K - K / (2 * t)
  let l := K - K / (4 * t)
  have h := hstep ha har hrs hs hk hkl
  change l - k = K / (4 * t) at hgap
  have hgap1 : s - r = R / (4 * t) := by dsimp only [s, r]; field_simp <;> ring
  have hgap2 : r - a = R / (4 * t) := by dsimp only [r, a]; field_simp <;> ring
  have hcoeff : 2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
      4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2 ≤ D * t ^ 2 := by
    change _ ≤ (4 * p + 2 * q * (128 / R) ^ 2 + 1) * t ^ 2
    have heq : 2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
        4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2 =
        p * (l / (l - k)) + q * ((32 / (s - r)) ^ 2 + (32 / (r - a)) ^ 2) := by
      rw [hgap1, hgap2]
      dsimp only [p, q]
      ring
    rw [heq]
    exact hc
  have hScoeff : S * (2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
      4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2) ≤
      (S + 1) * D * t ^ 2 := by
    calc
      _ ≤ S * (D * t ^ 2) := mul_le_mul_of_nonneg_left hcoeff hS
      _ ≤ (S + 1) * (D * t ^ 2) := mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right zero_le_one) (by positivity)
      _ = _ := by ring
  have hnext := h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hScoeff (integral_nonneg fun x => sq_nonneg _))
    (Real.rpow_nonneg (div_nonneg (integral_nonneg fun x => sq_nonneg _)
      (sq_nonneg (l - k))) β))
  have hanext : R + R / (2 : ℝ) ^ (n + 1) = a := by
    dsimp only [a, t]
    rw [pow_succ]
    ring
  have hlnext : K - K / (2 * (2 : ℝ) ^ (n + 1)) = l := by
    dsimp only [l, t]
    rw [pow_succ]
    ring
  rw [hanext, hlnext]
  change (∫ x in U ∩ euclideanBall z a, max (w.toFun x - l) 0 ^ 2) ≤
    (S + 1) * D * (4 : ℝ) ^ n *
      (∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) *
      ((∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) /
        (K / (4 * t)) ^ 2) ^ β
  change (∫ x in U ∩ euclideanBall z a, max (w.toFun x - l) 0 ^ 2) ≤
    (S + 1) * D * t ^ 2 *
      (∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) *
      ((∫ x in U ∩ euclideanBall z s, max (w.toFun x - k) 0 ^ 2) /
        (l - k) ^ 2) ^ β at hnext
  simpa only [hgap, ht2] using hnext

/-- A genuine zero-trace weak eigenfunction has a uniform upper amplitude
on every radius-R ball in dimension at least three. The numerical L² bound
and the eigenvalue precede all coefficient fields and eigenfunctions. -/
theorem exists_eigenfunction_ball_upper_amplitude_of_three_le {d : ℕ} (hd : 3 ≤ d)
    {κ M eigenvalue L R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (heigenvalue : 0 ≤ eigenvalue) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U),
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      (∫ x in U, w.toH1Function.toFun x ^ 2) ≤ L → ∀ z : Vec d,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), w.toH1Function.toFun x ≤ K := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨K, hK, hmain⟩ := exists_ae_upper_of_three_radius_eigenfunction_tails
    (div_pos (by norm_num : (0 : ℝ) < 2) hdpos)
    (sq_nonneg (zeroBoundarySobolevConstantTwo d : ℝ)) hκ hM heigenvalue hL hR
  refine ⟨K, hK, ?_⟩
  intro U hU hfin A hA ρ hρ hρM w hw hnorm z
  apply hmain w.toH1Function z hnorm
  intro a r s k l ha har hrs _hs hk hkl
  exact eigenfunction_zero_extended_ball_two_level_tail hd hU hfin hκ hM hA
    hρ hρM w heigenvalue hw z ha har hrs hk hkl


/-- In the plane the actual square-root volume factor is bounded by the
volume of the outer geometric ball before the coefficients and vector are
chosen. The spatial measure remains Lebesgue throughout the iteration. -/
theorem exists_eigenfunction_ball_upper_amplitude_planar
    {κ M eigenvalue L R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (heigenvalue : 0 ≤ eigenvalue) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec 2)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField 2} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec 2 → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U),
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      (∫ x in U, w.toH1Function.toFun x ^ 2) ≤ L → ∀ z : Vec 2,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), w.toH1Function.toFun x ≤ K := by
  let S : ℝ := (2 * sobolevWholeSpaceConstant 2) ^ 2 *
    (volume (euclideanBall (0 : Vec 2) (2 * R))).toReal ^ (1 / 2 : ℝ)
  have hS : 0 ≤ S := by positivity
  obtain ⟨K, hK, hmain⟩ := exists_ae_upper_of_three_radius_eigenfunction_tails
    (by norm_num : (0 : ℝ) < 1 / 2) hS hκ hM heigenvalue hL hR
  refine ⟨K, hK, ?_⟩
  intro U hU hfin A hA ρ hρ hρM w hw hnorm z
  apply hmain w.toH1Function z hnorm
  intro a r s k l ha har hrs hs hk hkl
  have hr : 0 < r := ha.trans_lt har
  have h2R : 0 < 2 * R := by positivity
  have hvol : volume (euclideanBall z r) ≤ volume (euclideanBall (0 : Vec 2) (2 * R)) := by
    calc
      _ ≤ volume (euclideanBall z (2 * R)) :=
        measure_mono (euclideanBall_mono hr.le (hrs.le.trans hs))
      _ = _ := by rw [volume_euclideanBall_eq_unit_mul_of_pos z h2R,
        volume_euclideanBall_eq_unit_mul_of_pos (0 : Vec 2) h2R]
  have hvolpow := Real.rpow_le_rpow ENNReal.toReal_nonneg
    (ENNReal.toReal_mono (volume_euclideanBall_ne_top (0 : Vec 2) h2R.le) hvol)
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hconst := mul_le_mul_of_nonneg_left hvolpow
    (sq_nonneg (2 * sobolevWholeSpaceConstant 2))
  have hl : 0 ≤ l := hk.trans hkl.le
  have hgap : 0 < l - k := sub_pos.mpr hkl
  have hcoef : 0 ≤ 2 * (2 * κ⁻¹ * eigenvalue * M * (l / (l - k)) +
      4 * κ⁻¹ ^ 2 * (32 / (s - r)) ^ 2) + 2 * (32 / (r - a)) ^ 2 := by positivity
  have htail := eigenfunction_zero_extended_ball_planar_two_level_tail hU hfin hκ hM hA
    hρ hρM w heigenvalue hw z ha har hrs hk hkl
  exact htail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hcoef)
      (integral_nonneg fun x => sq_nonneg _))
    (Real.rpow_nonneg (div_nonneg (integral_nonneg fun x => sq_nonneg _)
      (sq_nonneg (l - k))) (1 / 2)))

/-- The same numerically chosen amplitude controls both signs of a genuine
weak eigenfunction. No positivity of its representative is assumed. -/
theorem exists_eigenfunction_ball_abs_amplitude {d : ℕ} (hd : 2 ≤ d)
    {κ M eigenvalue L R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (heigenvalue : 0 ≤ eigenvalue) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U),
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      (∫ x in U, w.toH1Function.toFun x ^ 2) ≤ L → ∀ z : Vec d,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), |w.toH1Function.toFun x| ≤ K := by
  have hupper : ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U),
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      (∫ x in U, w.toH1Function.toFun x ^ 2) ≤ L → ∀ z : Vec d,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), w.toH1Function.toFun x ≤ K := by
    by_cases hd2 : d = 2
    · subst d
      exact exists_eigenfunction_ball_upper_amplitude_planar hκ hM heigenvalue hL hR
    · exact exists_eigenfunction_ball_upper_amplitude_of_three_le (by omega)
        hκ hM heigenvalue hL hR
  obtain ⟨K, hK, hmain⟩ := hupper
  refine ⟨K, hK, ?_⟩
  intro U hU hfin A hA ρ hρ hρM w hw hnorm z
  have hpos := hmain hU hfin hA hρ hρM w hw hnorm z
  have hnormneg : (∫ x in U, (-w).toH1Function.toFun x ^ 2) ≤ L := by
    simpa only [h10_neg_toH1Function, Homogenization.H1Function.neg_toFun,
      Pi.neg_apply, neg_sq] using hnorm
  have hneg := hmain hU hfin hA hρ hρM (-w) (eigenfunction_weak_solution_neg w hw) hnormneg z
  filter_upwards [hpos, hneg] with x hp hn
  apply abs_le.mpr
  refine ⟨?_, hp⟩
  have hn' : -w.toH1Function.toFun x ≤ K := by
    simpa only [h10_neg_toH1Function, Homogenization.H1Function.neg_toFun,
      Pi.neg_apply] using hn
  linarith only [hn']

/-- A fixed smooth cutoff on the literal source ball supplies a native
zero-trace trial vector with strictly positive unweighted mass. -/
theorem exists_sourceBall_nativeH10_positive_mass {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ v : Homogenization.H10Function
      (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R),
      0 < ∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R,
        v.toH1Function.toFun x ^ 2 := by
  rw [← TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : Vec d) hR]
  let η := quantitativeBallCutoff (0 : Vec d)
    (show 0 ≤ R / 2 by positivity) (show R / 2 < R by linarith)
  let v : Homogenization.H10Function (euclideanBall (0 : Vec d) R) :=
    Homogenization.H10Function.ofContDiff (isOpen_euclideanBall 0 R)
      η.smooth η.hasCompactSupport η.tsupport_subset
  have hsub : euclideanBall (0 : Vec d) (R / 2) ⊆
      Function.support (fun x => v.toH1Function.toFun x ^ 2) := by
    intro x hx
    change η.toFun x ^ 2 ≠ 0
    rw [η.eq_one_on_inner x hx]
    norm_num
  have hball : euclideanBall (0 : Vec d) (R / 2) ⊆ euclideanBall 0 R :=
    euclideanBall_mono (by positivity) (by linarith)
  have hμ : (volume.restrict (euclideanBall (0 : Vec d) R))
      (euclideanBall 0 (R / 2)) = volume (euclideanBall (0 : Vec d) (R / 2)) := by
    rw [Measure.restrict_apply (isOpen_euclideanBall 0 (R / 2)).measurableSet,
      Set.inter_eq_left.mpr hball]
  have hpos : 0 < ∫ x in euclideanBall (0 : Vec d) R, v.toH1Function.toFun x ^ 2 := by
    apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg _)
      v.toH1Function.memL2.integrable_sq).2
    exact (hμ.symm ▸ volume_euclideanBall_pos (0 : Vec d) (by positivity)).trans_le
      (measure_mono hsub)
  exact ⟨v, hpos⟩

/-- The first Rayleigh value is bounded before either coefficient field is
chosen, using a fixed nonzero native trial vector and the actual anisotropic
quadratic-form bounds. No eigenvalue bound is added as an external input. -/
theorem exists_sourceBall_uniform_rayleigh_upper {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E : ℝ, 0 < E ∧ ∀ {ρ : Vec d → ℝ} {α : Vec d → EinsteinRelation.Mat d},
      EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α →
      ∀ {eigenvalue : ℝ}, 0 ≤ eigenvalue →
      (∀ v : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R),
        eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
          dirichletEnergyPairing α v.toH1Function v.toH1Function) →
      eigenvalue ≤ E := by
  obtain ⟨v, hv⟩ := exists_sourceBall_nativeH10_positive_mass (d := d) hR
  let I := ∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R,
    v.toH1Function.toFun x ^ 2
  let G := ∫ x in EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R,
    vecNormSq (v.toH1Function.grad x)
  have hG : 0 ≤ G := integral_nonneg fun x => vecNormSq_nonneg _
  let E := κ⁻¹ * G / (κ * I) + 1
  have hI : 0 < I := hv
  have hE : 0 < E := by dsimp only [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro ρ α h eigenvalue heigenvalue hlower
  have hU : IsOpen (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R) :=
    (TubeProbability.dirichletBall (d := d) R).isOpen
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ h hU.measurableSet
  have hρ := (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ h
    (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R))).1
  have hmass : κ * I ≤ weightedL2Pairing ρ v.toH1Function v.toH1Function := by
    rw [weightedL2Pairing, ← integral_const_mul]
    apply integral_mono_ae (v.toH1Function.memL2.integrable_sq.const_mul κ)
      (weightedL2Pairing_integrable hρ v.toH1Function v.toH1Function)
    filter_upwards [] with x
    have hh := mul_le_mul_of_nonneg_right (h.2.2 x).1 (sq_nonneg (v.toH1Function.toFun x))
    simpa only [pow_two, mul_assoc] using hh
  have henergy : dirichletEnergyPairing α v.toH1Function v.toH1Function ≤ κ⁻¹ * G := by
    rw [dirichletEnergyPairing, ← integral_const_mul]
    apply integral_mono_ae (dirichletEnergyPairing_integrable hA v.toH1Function v.toH1Function)
      ((integrableOn_vecNormSq_of_memVectorL2On v.toH1Function.gradMemL2).const_mul κ⁻¹)
    filter_upwards [] with x
    have hh := ((h.2.2 x).2.2.2 (v.toH1Function.grad x)).2
    simpa only [PDE.vecNormSq, PDE.vecDot, PDE.matVecMul, Matrix.mulVec,
      dotProduct, EinsteinRelation.dot, EinsteinRelation.euclideanSq, pow_two,
      mul_comm] using hh
  have hbound := (mul_le_mul_of_nonneg_left hmass heigenvalue).trans ((hlower v).trans henergy)
  have he : eigenvalue ≤ κ⁻¹ * G / (κ * I) := (le_div_iff₀ (mul_pos hκ hI)).2 hbound
  exact he.trans (le_add_of_nonneg_right zero_le_one)

/-- A structural upper bound on the actual eigenvalue suffices for one
amplitude chosen before the coefficients and eigenfunction. The auxiliary
scaled weight appears only inside this proof of the upper estimate. -/
theorem exists_eigenfunction_ball_abs_amplitude_of_eigenvalue_le {d : ℕ} (hd : 2 ≤ d)
    {κ M E L R : ℝ} (hκ : 0 < κ) (hM : 0 ≤ M)
    (hE : 0 ≤ E) (hL : 0 ≤ L) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U) {eigenvalue : ℝ},
      0 ≤ eigenvalue → eigenvalue ≤ E →
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      (∫ x in U, w.toH1Function.toFun x ^ 2) ≤ L → ∀ z : Vec d,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), |w.toH1Function.toFun x| ≤ K := by
  have hEpos : 0 < E + 1 := by linarith
  obtain ⟨K, hK, hmain⟩ := exists_eigenfunction_ball_abs_amplitude hd hκ hM hEpos.le hL hR
  refine ⟨K, hK, ?_⟩
  intro U hU hfin A hA ρ hρ hρM w eigenvalue he heE hw hnorm z
  let c := eigenvalue / (E + 1)
  have hc : 0 ≤ c := div_nonneg he hEpos.le
  have hc1 : c ≤ 1 := (div_le_one hEpos).2 (heE.trans (by linarith))
  have hρc : AEStronglyMeasurable (fun x => c * ρ x) (volume.restrict U) := hρ.const_mul c
  have hρcM : ∀ᵐ x ∂volume.restrict U, |c * ρ x| ≤ M := by
    filter_upwards [hρM] with x hx
    rw [abs_mul, abs_of_nonneg hc]
    exact (mul_le_mul_of_nonneg_left hx hc).trans
      ((mul_le_mul_of_nonneg_right hc1 hM).trans_eq (one_mul M))
  have hforcing : (fun x => (E + 1) * (c * ρ x) * w.toH1Function.toFun x) =
      (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) := by
    funext x
    dsimp only [c]
    field_simp [hEpos.ne'] <;> ring
  apply hmain hU hfin hA hρc hρcM w ?_ hnorm z
  rw [hforcing]
  exact hw

/-- Weighted normalization gives the numerical initial L² bound used by
the geometric iteration. Its amplitude depends only on the density lower
bound, ellipticity, density upper bound, eigenvalue bound and radius. -/
theorem exists_normalized_eigenfunction_ball_abs_amplitude {d : ℕ} (hd : 2 ≤ d)
    {κ m M E R : ℝ} (hκ : 0 < κ) (hm : 0 < m) (hM : 0 ≤ M)
    (hE : 0 ≤ E) (hR : 0 < R) :
    ∃ K : ℝ, 0 < K ∧ ∀ {U : Set (Vec d)} (hU : IsOpen U) (hfin : volume U ≠ ⊤)
      {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
      {ρ : Vec d → ℝ} (hρ : AEStronglyMeasurable ρ (volume.restrict U))
      (hρlower : ∀ᵐ x ∂volume.restrict U, m ≤ ρ x)
      (hρM : ∀ᵐ x ∂volume.restrict U, |ρ x| ≤ M)
      (w : Homogenization.H10Function U) {eigenvalue : ℝ},
      0 ≤ eigenvalue → eigenvalue ≤ E →
      IsWeakSolutionOn A U w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      weightedL2Pairing ρ w.toH1Function w.toH1Function = 1 → ∀ z : Vec d,
      ∀ᵐ x ∂volume.restrict (U ∩ euclideanBall z R), |w.toH1Function.toFun x| ≤ K := by
  obtain ⟨K, hK, hmain⟩ := exists_eigenfunction_ball_abs_amplitude_of_eigenvalue_le
    hd hκ hM hE (inv_nonneg.mpr hm.le) hR
  refine ⟨K, hK, ?_⟩
  intro U hU hfin A hA ρ hρ hρlower hρM w eigenvalue he heE hw hnorm z
  apply hmain hU hfin hA hρ hρM w he heE hw ?_ z
  apply integral_sq_le_of_weighted_normalization hm hρ hρlower hρM w.toH1Function.memL2
  simpa only [weightedL2Pairing, pow_two, mul_assoc] using hnorm

/-- The genuine first source-ball eigenfunction can be chosen nonnegative,
weighted-normalized and bounded almost everywhere, with both numerical
bounds fixed before the actual density and anisotropic coefficient field. -/
theorem exists_sourceBall_first_nonnegative_bounded_weak_eigenfunction {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E K : ℝ, 0 < E ∧ 0 < K ∧
      ∀ {ρ : Vec d → ℝ} {α : Vec d → EinsteinRelation.Mat d},
      EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α →
      ∃ (eigenvalue : ℝ) (u : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R)),
        0 < eigenvalue ∧ eigenvalue ≤ E ∧ (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
        weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
        dirichletEnergyPairing α u.toH1Function u.toH1Function = eigenvalue ∧
        (∀ v : Homogenization.H10Function (EinsteinFull.External.Source.GMP.sourceBall 0 R),
          eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
            dirichletEnergyPairing α v.toH1Function v.toH1Function) ∧
        IsWeakSolutionOn α (EinsteinFull.External.Source.GMP.sourceBall 0 R)
          u.toH1Function (fun x => eigenvalue * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
        ∀ᵐ x ∂volume.restrict (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R),
          |u.toH1Function.toFun x| ≤ K := by
  obtain ⟨E, hE, hupper⟩ := exists_sourceBall_uniform_rayleigh_upper (d := d) hκ hR
  obtain ⟨K, hK, hamp⟩ := exists_normalized_eigenfunction_ball_abs_amplitude
    hd (pow_pos hκ 3) hκ (inv_nonneg.mpr hκ.le) hE.le hR
  refine ⟨E, K, hE, hK, ?_⟩
  intro ρ α h
  obtain ⟨eigenvalue, u, he, hnonneg, hnorm, henergy, hlower, hweak⟩ :=
    exists_sourceBall_first_nonnegative_weak_eigenfunction hd hκ h R hR
  have heE := hupper h he.le hlower
  refine ⟨eigenvalue, u, he, heE, hnonneg, hnorm, henergy, hlower, hweak, ?_⟩
  have hU : IsOpen (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R) :=
    (TubeProbability.dirichletBall (d := d) R).isOpen
  have hfin : volume (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ h hU.measurableSet
  have hρ : AEStronglyMeasurable ρ
      (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R)) :=
    h.1.aestronglyMeasurable
  have hρlower : ∀ᵐ x ∂volume.restrict
      (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R), κ ≤ ρ x :=
    ae_of_all _ fun x => (h.2.2 x).1
  have hρM : ∀ᵐ x ∂volume.restrict
      (EinsteinFull.External.Source.GMP.sourceBall (0 : Vec d) R), |ρ x| ≤ κ⁻¹ :=
    ae_of_all _ fun x => (abs_of_nonneg (hκ.le.trans (h.2.2 x).1)).trans_le (h.2.2 x).2.1
  have hb := hamp hU hfin hA hρ hρlower hρM u he.le heE hweak hnorm (0 : Vec d)
  simpa only [TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : Vec d) hR,
    Set.inter_self] using hb

/-- A normalized weak eigenfunction with a structural eigenvalue bound
satisfies the finite boundary-cover contraction. The cover and all numerical
choices precede the fields and the actual eigenfunction; its forcing bound
and smallness are proved from its amplitude rather than assumed. -/
theorem exists_normalized_eigenfunction_boundary_cover_contraction {d : ℕ} (hd : 2 ≤ d)
    {κ m M E R : ℝ} (hκ : 0 < κ) (hκLam : κ ≤ κ⁻¹) (hm : 0 < m)
    (hM : 0 ≤ M) (hE : 0 ≤ E) (hR : 0 < R) :
    ∃ K ℓ r θ : ℝ, 0 < K ∧ 0 < ℓ ∧ 0 < r ∧ 0 < θ ∧ θ < 1 ∧
      ∃ s : Finset (Vec d),
        (∀ z ∈ s, z ∈ frontier (euclideanBall (0 : Vec d) R)) ∧
        frontier (euclideanBall (0 : Vec d) R) ⊆ ⋃ z ∈ s, euclideanBall z (ℓ * r / 4) ∧
        ∀ {A : CoeffField d}, IsEllipticFieldOn κ κ⁻¹ (euclideanBall (0 : Vec d) R) A →
        ∀ {ρ : Vec d → ℝ}, AEStronglyMeasurable ρ (volume.restrict (euclideanBall (0 : Vec d) R)) →
        (∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) R), m ≤ ρ x) →
        (∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) R), |ρ x| ≤ M) →
        ∀ (w : Homogenization.H10Function (euclideanBall (0 : Vec d) R)) {eigenvalue : ℝ},
        0 ≤ eigenvalue → eigenvalue ≤ E →
        IsWeakSolutionOn A (euclideanBall (0 : Vec d) R) w.toH1Function
          (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
        weightedL2Pairing ρ w.toH1Function w.toH1Function = 1 →
        ∀ᵐ x ∂volume.restrict (⋃ z ∈ s, euclideanBall z (ℓ * r / 4)),
          |(euclideanBall (0 : Vec d) R).indicator w.toH1Function.toFun x| ≤ θ * K := by
  obtain ⟨K, hK, hamp⟩ := exists_normalized_eigenfunction_ball_abs_amplitude
    hd hκ hm hM hE hR
  obtain ⟨ℓ, hℓ, N, _hN, θ, hθ, hθ1, hcover⟩ :=
    exists_uniform_boundary_cover_abs_contraction hd hκ hκLam
  let r := Real.sqrt (κ / ((2 : ℝ) ^ N * (E * M + 1)))
  have hEM : 0 < E * M + 1 := by positivity
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  obtain ⟨s, hs, hscover, _hcubes, _hhalf, hcontract⟩ := hcover hr (0 : Vec d) R hR.le
  refine ⟨K, ℓ, r, θ, hK, hℓ, hr, hθ, hθ1, s, hs, hscover, ?_⟩
  intro A hA ρ hρ hρlower hρM w eigenvalue he heE hw hnorm
  have hbound := hamp (isOpen_euclideanBall 0 R) (volume_euclideanBall_ne_top 0 hR.le)
    hA hρ hρlower hρM w he heE hw hnorm (0 : Vec d)
  simp only [Set.inter_self] at hbound
  let f := fun x => eigenvalue * ρ x * w.toH1Function.toFun x
  let F := E * M * K
  have hf : AEStronglyMeasurable f (volume.restrict (euclideanBall (0 : Vec d) R)) :=
    (hρ.const_mul eigenvalue).mul w.toH1Function.memL2.aestronglyMeasurable
  have hF : 0 ≤ F := by positivity
  have hfF : ∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) R), |f x| ≤ F := by
    filter_upwards [hρM, hbound] with x hρx hwx
    dsimp only [f, F]
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    exact mul_le_mul (mul_le_mul heE hρx (abs_nonneg _) hE) hwx
      (abs_nonneg _) (mul_nonneg hE hM)
  have hsmall : κ⁻¹ * r ^ 2 * F ≤ K / (2 : ℝ) ^ N := by
    have hratio : E * M / (E * M + 1) ≤ 1 := (div_le_one hEM).2 (by linarith)
    calc
      _ = (E * M / (E * M + 1)) * (K / (2 : ℝ) ^ N) := by
        dsimp only [r, F]
        rw [Real.sq_sqrt (by positivity)]
        field_simp [hκ.ne', hEM.ne']
        <;> ring
      _ ≤ 1 * (K / (2 : ℝ) ^ N) := mul_le_mul_of_nonneg_right hratio (by positivity)
      _ = _ := one_mul _
  apply hcontract hA w f hf hF hfF hw hK ?_ hsmall
  intro z hz
  exact hbound.mono fun x hx _ => hx

/-- A normalized weighted square retains at least the stated mass on a
measurable interior set when the bounded complement is sufficiently small. -/
theorem normalized_weighted_mass_on_interior {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {S : Set X} (hS : MeasurableSet S)
    {ρ u : X → ℝ} {M K : ℝ} (hM : 0 ≤ M)
    (hi : Integrable (fun x => ρ x * (u x) ^ 2) μ)
    (hnorm : ∫ x, ρ x * (u x) ^ 2 ∂μ = 1)
    (hρ : ∀ᵐ x ∂μ.restrict Sᶜ, ρ x ≤ M)
    (hu : ∀ᵐ x ∂μ.restrict Sᶜ, |u x| ≤ K) :
    1 - μ.real Sᶜ * (M * K ^ 2) ≤ ∫ x in S, ρ x * (u x) ^ 2 ∂μ := by
  have hb : ∀ᵐ x ∂μ.restrict Sᶜ, ρ x * (u x) ^ 2 ≤ M * K ^ 2 := by
    filter_upwards [hρ, hu] with x hxρ hxu
    have hsquare : (u x) ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (u x)) hxu 2
    exact (mul_le_mul_of_nonneg_right hxρ (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsquare hM)
  have htail := integral_mono_ae hi.restrict (integrable_const (M * K ^ 2)) hb
  rw [integral_const] at htail
  simp only [smul_eq_mul, Measure.real, Measure.restrict_apply_univ] at htail
  have hsplit := integral_add_compl hS hi
  rw [hnorm] at hsplit
  change 1 - (μ Sᶜ).toReal * (M * K ^ 2) ≤ _
  linarith only [hsplit, htail]

/-- A concentric Euclidean boundary layer can have arbitrarily small volume.
The radius depends only on the dimension, outer radius and desired volume. -/
theorem exists_small_euclideanBall_boundary_layer {d : ℕ} (c : Vec d)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      volume.real (euclideanBall c R \ euclideanBall c r) < ε := by
  let V := (volume (euclideanBall (0 : Vec d) 1)).toReal
  have hcont : Continuous (fun t : ℝ => t ^ d * V) :=
    (continuous_id.pow d).mul continuous_const
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.1 hcont.continuousAt ε hε
  let a := min R δ / 2
  have ha : 0 < a := by dsimp only [a]; positivity
  have haR : a < R := by
    have hmin := min_le_left R δ
    dsimp only [a]
    linarith only [hmin, hR]
  have haδ : a < δ := by
    have hmin := min_le_right R δ
    dsimp only [a]
    linarith only [hmin, hδ]
  let r := R - a
  have hr : 0 < r := by dsimp only [r]; linarith only [haR]
  have hrR : r < R := by dsimp only [r]; linarith only [ha]
  have hdist : dist r R < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by dsimp only [r]; linarith only [ha.le])]
    dsimp only [r]
    linarith only [haδ]
  have hvol := hδbound hdist
  rw [Real.dist_eq] at hvol
  have hsub : euclideanBall c r ⊆ euclideanBall c R := by
    intro x hx
    change euclideanSqDist x c < r ^ 2 at hx
    change euclideanSqDist x c < R ^ 2
    nlinarith only [hx, hr, hrR]
  refine ⟨r, hr, hrR, ?_⟩
  rw [measureReal_sdiff hsub (isOpen_euclideanBall c r).measurableSet
    (volume_euclideanBall_ne_top c hR.le)]
  change (volume (euclideanBall c R)).toReal - (volume (euclideanBall c r)).toReal < ε
  rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos c hR,
    volume_euclideanBall_toReal_eq_unit_mul_of_pos c hr]
  dsimp only [V] at hvol
  have := (abs_lt.mp hvol).1
  linarith only [this]


/-- A uniform amplitude bound and weighted normalization force at least half
of the mass into a structurally chosen concentric interior ball. -/
theorem exists_interior_ball_of_normalized_weighted_mass {d : ℕ} (c : Vec d)
    {R M K : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∀ {ρ u : Vec d → ℝ},
        Integrable (fun x => ρ x * (u x) ^ 2) (volume.restrict (euclideanBall c R)) →
        (∫ x in euclideanBall c R, ρ x * (u x) ^ 2) = 1 →
        (∀ᵐ x ∂volume.restrict (euclideanBall c R), ρ x ≤ M) →
        (∀ᵐ x ∂volume.restrict (euclideanBall c R), |u x| ≤ K) →
        (1 : ℝ) / 2 ≤ ∫ x in euclideanBall c r,
          ρ x * (u x) ^ 2 ∂(volume.restrict (euclideanBall c R)) := by
  let B := M * K ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hden : 0 < 2 * (B + 1) := by positivity
  obtain ⟨r, hr, hrR, hsmall⟩ :=
    exists_small_euclideanBall_boundary_layer c hR (show 0 < 1 / (2 * (B + 1)) by positivity)
  refine ⟨r, hr, hrR, ?_⟩
  intro ρ u hi hnorm hρ hu
  let μ := volume.restrict (euclideanBall c R)
  let S := euclideanBall c r
  have hS : MeasurableSet S := (isOpen_euclideanBall c r).measurableSet
  letI : IsFiniteMeasure μ :=
    ⟨by simpa only [μ, Measure.restrict_apply_univ] using
      (volume_euclideanBall_ne_top c hR.le).lt_top⟩
  have hmass := normalized_weighted_mass_on_interior μ hS hM hi hnorm
    (ae_restrict_of_ae hρ) (ae_restrict_of_ae hu)
  have hmeas : μ.real Sᶜ = volume.real (euclideanBall c R \ S) := by
    simp only [Measure.real, μ, Measure.restrict_apply hS.compl, Set.inter_comm,
      Set.diff_eq]
  rw [hmeas] at hmass
  change volume.real (euclideanBall c R \ S) < 1 / (2 * (B + 1)) at hsmall
  have hvol : 0 ≤ volume.real (euclideanBall c R \ S) := ENNReal.toReal_nonneg
  have hbound : volume.real (euclideanBall c R \ S) * B ≤ 1 / 2 := by
    have ht := (lt_div_iff₀ hden).mp hsmall
    nlinarith only [ht, hvol]
  change 1 - volume.real (euclideanBall c R \ S) * B ≤ _ at hmass
  linarith only [hmass, hbound]


/-- A compact concentric ball has a finite cover by balls with centers in a
larger concentric interior ball. The cover is independent of the integrand. -/
theorem exists_finite_interior_ball_cover {d : ℕ} (c : Vec d)
    {r₀ r s : ℝ} (hr₀ : 0 ≤ r₀) (hr : r₀ < r) (hs : 0 < s) :
    ∃ t : Finset (Vec d),
      (∀ z ∈ t, z ∈ euclideanBall c r) ∧
      euclideanClosedBall c r₀ ⊆ ⋃ z ∈ t, euclideanBall z s := by
  classical
  let S := euclideanClosedBall c r₀
  let cell : S → Set (Vec d) := fun z => euclideanBall z.1 s
  have hcover : S ⊆ ⋃ z : S, cell z := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, center_mem_euclideanBall x hs⟩
  obtain ⟨u, hu⟩ := (isCompact_euclideanClosedBall c hr₀).elim_finite_subcover cell
    (fun z => isOpen_euclideanBall _ _) hcover
  let t : Finset (Vec d) := u.image Subtype.val
  refine ⟨t, ?_, ?_⟩
  · intro z hz
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hz
    change euclideanSqDist y.1 c < r ^ 2
    have hy : euclideanSqDist y.1 c ≤ r₀ ^ 2 := y.2
    nlinarith only [hy, hr₀, hr]
  · intro x hx
    have hx' : x ∈ ⋃ z ∈ u, cell z := hu hx
    simp only [Set.mem_iUnion] at hx'
    obtain ⟨z, hz, hxz⟩ := hx'
    exact Set.mem_iUnion.mpr ⟨z.1, Set.mem_iUnion.mpr
      ⟨Finset.mem_image.mpr ⟨z, hz, rfl⟩, hxz⟩⟩

/-- A finite cover of a set carrying positive mass contains a member with
mass bounded below by a constant depending only on the size of the cover. -/
theorem exists_cover_member_with_mass {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (S : Set α) (t : Finset ι)
    (U : ι → Set α) {m : ℝ} (hm : 0 < m)
    (hcover : S ⊆ ⋃ i ∈ t, U i) (hmass : m ≤ μ.real S) :
    ∃ i ∈ t, m / ((t.card : ℝ) + 1) ≤ μ.real (U i) := by
  classical
  have hd : 0 < (t.card : ℝ) + 1 := by positivity
  have hp : 0 < m / ((t.card : ℝ) + 1) := div_pos hm hd
  have htotal : m ≤ ∑ i ∈ t, μ.real (U i) :=
    hmass.trans ((measureReal_mono hcover (measure_ne_top μ _)).trans
      (measureReal_biUnion_finset_le t U))
  by_contra! h
  have hsum : (∑ i ∈ t, μ.real (U i)) ≤
      (t.card : ℝ) * (m / ((t.card : ℝ) + 1)) := by
    calc
      _ ≤ ∑ _i ∈ t, m / ((t.card : ℝ) + 1) :=
        Finset.sum_le_sum (fun i hi => (h i hi).le)
      _ = _ := by simp [nsmul_eq_mul]
  have heq : ((t.card : ℝ) + 1) * (m / ((t.card : ℝ) + 1)) = m := by
    field_simp
  nlinarith only [htotal, hsum, hp, heq]


/-- A finite measurable cover of positive nonnegative integral mass has a
member carrying a uniform fraction of that mass. -/
theorem exists_cover_member_with_integral_mass {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : Integrable f μ)
    (hf0 : 0 ≤ᵐ[μ] f) (S : Set α) (hS : MeasurableSet S)
    (t : Finset ι) (U : ι → Set α) (hU : ∀ i ∈ t, MeasurableSet (U i))
    {m : ℝ} (hm : 0 < m) (hcover : S ⊆ ⋃ i ∈ t, U i)
    (hmass : m ≤ ∫ x in S, f x ∂μ) :
    ∃ i ∈ t, m / ((t.card : ℝ) + 1) ≤ ∫ x in U i, f x ∂μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.lintegral_lt_top.ne
  have heq (A : Set α) (hA : MeasurableSet A) :
      ν.real A = ∫ x in A, f x ∂μ := by
    dsimp only [ν, Measure.real]
    rw [withDensity_apply _ hA, integral_eq_lintegral_of_nonneg_ae
      (ae_restrict_of_ae hf0) (hf.aestronglyMeasurable.restrict)]
  obtain ⟨i, hi, hmassi⟩ := exists_cover_member_with_mass ν S t U hm hcover
    (by rwa [heq S hS])
  exact ⟨i, hi, by simpa only [heq (U i) (hU i hi)] using hmassi⟩


/-- Uniform normalization and amplitude bounds provide a positive seed mass
in a ball whose center stays inside a structurally fixed concentric ball. -/
theorem exists_uniform_interior_seed_mass {d : ℕ} (c : Vec d)
    {R M K : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ r s m : ℝ, 0 < r ∧ 0 < s ∧ r + 4 * s ≤ R ∧ 0 < m ∧
      ∀ {ρ u : Vec d → ℝ},
        Integrable (fun x => ρ x * (u x) ^ 2) (volume.restrict (euclideanBall c R)) →
        (∫ x in euclideanBall c R, ρ x * (u x) ^ 2) = 1 →
        (∀ᵐ x ∂volume.restrict (euclideanBall c R), 0 ≤ ρ x) →
        (∀ᵐ x ∂volume.restrict (euclideanBall c R), ρ x ≤ M) →
        (∀ᵐ x ∂volume.restrict (euclideanBall c R), |u x| ≤ K) →
        ∃ z ∈ euclideanBall c r,
          m ≤ ∫ x in euclideanBall z s, ρ x * (u x) ^ 2 := by
  obtain ⟨r₀, hr₀, hr₀R, hmass⟩ :=
    exists_interior_ball_of_normalized_weighted_mass c hR hM
  let r := (r₀ + R) / 2
  let s := (R - r) / 4
  have hr₀r : r₀ < r := by dsimp [r]; linarith
  have hr : 0 < r := lt_trans hr₀ hr₀r
  have hs : 0 < s := by dsimp [s, r]; linarith
  have hmargin : r + 4 * s ≤ R := by dsimp [s]; linarith
  obtain ⟨t, ht, hcover⟩ := exists_finite_interior_ball_cover c hr₀.le hr₀r hs
  let m : ℝ := (1 / 2) / ((t.card : ℝ) + 1)
  have hm : 0 < m := by dsimp [m]; positivity
  refine ⟨r, s, m, hr, hs, hmargin, hm, ?_⟩
  intro ρ u hi hnorm hρ0 hρM hu
  have hf0 : 0 ≤ᵐ[volume.restrict (euclideanBall c R)]
      (fun x => ρ x * (u x) ^ 2) := by
    filter_upwards [hρ0] with x hx
    exact mul_nonneg hx (sq_nonneg _)
  have hcover' : euclideanBall c r₀ ⊆ ⋃ z ∈ t, euclideanBall z s := by
    apply Set.Subset.trans ?_ hcover
    intro x hx
    change euclideanSqDist x c ≤ r₀ ^ 2
    exact (show euclideanSqDist x c < r₀ ^ 2 from hx).le
  obtain ⟨z, hzt, hzmass⟩ := exists_cover_member_with_integral_mass
    (volume.restrict (euclideanBall c R)) (fun x => ρ x * (u x) ^ 2)
    hi hf0 (euclideanBall c r₀) (isOpen_euclideanBall c r₀).measurableSet
    t (fun z => euclideanBall z s) (fun z _ => (isOpen_euclideanBall z s).measurableSet)
    (by norm_num : (0 : ℝ) < 1 / 2) hcover' (hmass hi hnorm hρM hu)
  have hz := ht z hzt
  have hsub : euclideanBall z s ⊆ euclideanBall c R := by
    apply euclideanBall_subset_of_center_norm_add_le hs hR
    rw [TubeProbability.DimensionLift.pde_ball_eq_sourceBall c hr] at hz
    change Homogenization.euclideanNorm (z - c) < r at hz
    change vecEuclideanNorm (z - c) < r at hz
    linarith only [hz, hmargin, hs]
  refine ⟨z, hz, ?_⟩
  simpa only [m, Measure.restrict_restrict_of_subset hsub] using hzmass


open EinsteinRelation EinsteinFull.External.Source.GMP

/-- Normalized, bounded nonnegative source-ball eigenfunctions have a
uniform positive amplitude on a structural concentric interior ball. -/
theorem exists_uniform_sourceBall_eigenfunction_interior_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R K : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ r a : ℝ, 0 < r ∧ r < R ∧ 0 < a ∧
      ∀ (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : PDE.Vec d → ℝ) (g : PDE.Vec d → PDE.Vec d),
        MemLp u 2 (volume.restrict (sourceBall 0 R)) →
        (∀ i, MemLp (fun x => g x i) 2 (volume.restrict (sourceBall 0 R))) →
        HasWeakGradient (sourceBall 0 R) u g →
        ∀ eigenvalue : ℝ, 0 ≤ eigenvalue →
        (∀ ψ : PDE.Vec d → ℝ, IsSpatialTest (sourceBall 0 R) ψ →
          (∫ x in sourceBall 0 R, dot ((α x).mulVec (g x))
            (fun i => fderiv ℝ ψ x (unitVector i))) =
            eigenvalue * ∫ x in sourceBall 0 R, (ρ x * u x) * ψ x) →
        (∀ᵐ x ∂volume.restrict (sourceBall 0 R), 0 ≤ u x) →
        (∫ x in sourceBall 0 R, ρ x * (u x) ^ 2) = 1 →
        (∀ᵐ x ∂volume.restrict (sourceBall 0 R), |u x| ≤ K) →
        ∀ᵐ x ∂volume.restrict (sourceBall 0 r), a ≤ u x := by
  obtain ⟨C, hC, hharnack⟩ :=
    TubeProbability.DimensionLift.exists_sourceBall_eigenfunction_interior_lower_of_seed_mass d hd
  obtain ⟨r, s, m, hr, hs, hmargin, hm, hseed⟩ :=
    exists_uniform_interior_seed_mass (0 : PDE.Vec d) hR (inv_nonneg.mpr hκ.le) (K := K)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * r / s)
  have hstep : 2 * r < (n : ℝ) * s := (div_lt_iff₀ hs).mp hn
  have hnpos : 0 < n := by
    have hnreal : (0 : ℝ) < n := lt_of_le_of_lt (by positivity : 0 ≤ 2 * r / s) hn
    exact_mod_cast hnreal
  let H := Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))
  let a := Real.sqrt (m / (κ⁻¹ * volume.real (euclideanBall (0 : PDE.Vec d) s))) /
    H ^ (n + 1) / H ^ (n + 1)
  have hH : 0 < H := Real.exp_pos _
  have hvol : 0 < volume.real (euclideanBall (0 : PDE.Vec d) s) :=
    volume_euclideanBall_toReal_pos 0 hs
  have ha : 0 < a := by
    dsimp only [a]
    exact div_pos (div_pos (Real.sqrt_pos.2 (div_pos hm (mul_pos (inv_pos.mpr hκ) hvol)))
      (pow_pos hH _)) (pow_pos hH _)
  refine ⟨r, a, hr, by linarith only [hmargin, hs], ha, ?_⟩
  intro ρ α hell u g hu hg hw eigenvalue he hweak hu0 hnorm hub
  have hballR := TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hR
  have hint : Integrable (fun x => ρ x * (u x) ^ 2)
      (volume.restrict (euclideanBall (0 : PDE.Vec d) R)) := by
    rw [hballR]
    exact hu.integrable_sq.mul_of_top_right
      (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top
        hκ hell (volume.restrict (sourceBall 0 R))).1
  obtain ⟨z, hz, hmass⟩ := hseed hint (by simpa only [hballR] using hnorm)
    (by rw [hballR]; exact ae_of_all _ (fun x => hκ.le.trans (hell.2.2 x).1))
    (by rw [hballR]; exact ae_of_all _ (fun x => (hell.2.2 x).2.1))
    (by simpa only [hballR] using hub)
  have hballr := TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hr
  have hballs := TubeProbability.DimensionLift.pde_ball_eq_sourceBall z hs
  have hresult := hharnack κ hκ ρ α hell 0 R hR u g hu hg hw eigenvalue he hweak hu0
    r s hr hs hmargin n hnpos hstep z (by simpa only [hballr] using hz)
    m hm (by simpa only [hballs] using hmass)
  have hvol_eq : volume.real (sourceBall z s) = volume.real (euclideanBall (0 : PDE.Vec d) s) := by
    rw [← hballs]
    simp only [Measure.real, volume_euclideanBall_toReal_eq_unit_mul_of_pos _ hs]
  simpa only [hvol_eq, H, a] using hresult.2


/-- The bounded first native Dirichlet eigenfunction itself has a uniform
positive lower bound on a concentric interior ball. -/
theorem exists_sourceBall_first_eigenfunction_uniform_interior_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E K r a : ℝ, 0 < E ∧ 0 < K ∧ 0 < r ∧ r < R ∧ 0 < a ∧
      ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      IsUniformlyElliptic κ ρ α →
      ∃ (eigenvalue : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R)),
        0 < eigenvalue ∧ eigenvalue ≤ E ∧ (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
        weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
        dirichletEnergyPairing α u.toH1Function u.toH1Function = eigenvalue ∧
        (∀ v : Homogenization.H10Function (sourceBall 0 R),
          eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
            dirichletEnergyPairing α v.toH1Function v.toH1Function) ∧
        IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
          (fun x => eigenvalue * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
        (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R), |u.toH1Function.toFun x| ≤ K) ∧
        ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ u.toH1Function.toFun x := by
  obtain ⟨E, K, hE, hK, hex⟩ :=
    exists_sourceBall_first_nonnegative_bounded_weak_eigenfunction hd hκ hR
  obtain ⟨r, a, hr, hrR, ha, hlower⟩ :=
    exists_uniform_sourceBall_eigenfunction_interior_lower hd hκ hR (K := K)
  refine ⟨E, K, r, a, hE, hK, hr, hrR, ha, ?_⟩
  intro ρ α hell
  obtain ⟨eigenvalue, u, he, heE, hu0, hnorm, henergy, hmin, hweak, hub⟩ := hex hell
  refine ⟨eigenvalue, u, he, heE, hu0, hnorm, henergy, hmin, hweak, hub, ?_⟩
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  letI : IsFiniteMeasure (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hfin
  have hwg : HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
      u.toH1Function.toFun u.toH1Function.grad := by
    intro i
    refine ⟨(show IntegrableOn u.toH1Function.toFun (sourceBall 0 R) volume from
      u.toH1Function.memL2.integrable (by norm_num)).locallyIntegrableOn,
      (show IntegrableOn (fun x => u.toH1Function.grad x i) (sourceBall 0 R) volume from
        (u.toH1Function.gradMemL2 i).integrable (by norm_num)).locallyIntegrableOn, ?_⟩
    intro ψ hψ
    simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
      u.toH1Function.hasWeakGradient i ψ hψ.1 hψ.2.1 hψ.2.2
  apply hlower ρ α hell u.toH1Function.toFun u.toH1Function.grad
    u.toH1Function.memL2 u.toH1Function.gradMemL2 hwg eigenvalue he.le
  · intro ψ hψ
    let φ : TestFunction (TubeProbability.dirichletBall (d := d) R) ℝ ⊤ :=
      ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
    exact TubeProbability.native_weakEigenEquation_on_smooth R u eigenvalue hweak φ
  · exact ae_of_all _ hu0
  · simpa only [weightedL2Pairing, pow_two, mul_assoc] using hnorm
  · exact hub


open EinsteinRelation ProbabilityTheory TubeProbability TubeProbability.DimensionLift
open scoped NNReal

/-- Uniform interior mass of the first native eigenfunction gives a structural
lower bound for its associated spectral heat pairing. -/
theorem exists_uniform_sourceBall_native_heat_pairing {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ (E r a : ℝ) (_hE : 0 < E) (hr : 0 < r) (_hrR : r < R) (_ha : 0 < a),
      ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}, ∀ (hell : IsUniformlyElliptic κ ρ α),
      ∀ T : ℝ≥0, ∃ (eig : ℝ)
        (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R)),
        0 < eig ∧ eig ≤ E ∧
        weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
        IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
          (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
        (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
          a ≤ u.toH1Function.toFun x) ∧
        ∃ (eigenvalue : ℕ → ℝ)
        (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n),
        ∀ t : ℝ≥0, t ≤ T →
          let hs : MeasurableSet (sourceBall (0 : PDE.Vec d) r) := by
            rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr]
            exact (PDE.isOpen_euclideanBall 0 r).measurableSet
          letI : IsFiniteMeasure (dirichletVolume ρ R) :=
            dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
          let w := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
          Real.exp (-E * T) * (a * (κ * (r ^ d * volume.real (sourceBall (0 : PDE.Vec d) 1)))) ^ 2 ≤
            inner ℝ w (SpectralHeat.heatOperator b eigenvalue hpos t w) := by
  obtain ⟨E, K, r, a, hE, hK, hr, hrR, ha, hex⟩ :=
    exists_sourceBall_first_eigenfunction_uniform_interior_lower hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell T
  obtain ⟨eig, u, heig, heE, hu0, hnorm, henergy, hmin, hweak, hub, hlower⟩ := hex hell
  have hsub : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R := by
    rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr,
      ← pde_ball_eq_sourceBall (0 : PDE.Vec d) hR]
    exact PDE.euclideanBall_mono hr.le hrR.le
  refine ⟨eig, u, heig, heE, hnorm, hweak, hlower, ?_⟩
  apply exists_native_weakEigenfunction_heat_pairing_scaled hd hκ hell R hR u eig E
    heig.le heE hweak ?_ 0 r hr hsub a ha.le hlower T
  simpa only [weightedL2Pairing] using hnorm


/-- Uniform interior mass of the first native eigenfunction gives a structural
lower bound for the pairing of two spectral heat evolutions on a time interval. -/
theorem exists_uniform_sourceBall_native_heat_pairing_two_times {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ (E r a : ℝ) (_hE : 0 < E) (hr : 0 < r) (_hrR : r < R) (_ha : 0 < a),
      ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}, ∀ (hell : IsUniformlyElliptic κ ρ α),
      ∀ T : ℝ≥0, ∃ (eig : ℝ)
        (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R)),
        0 < eig ∧ eig ≤ E ∧
        weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
        IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
          (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
        (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
          a ≤ u.toH1Function.toFun x) ∧
        ∃ (eigenvalue : ℕ → ℝ)
        (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n),
        ∀ s t : ℝ≥0, s + t ≤ T →
          let hs : MeasurableSet (sourceBall (0 : PDE.Vec d) r) := by
            rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr]
            exact (PDE.isOpen_euclideanBall 0 r).measurableSet
          letI : IsFiniteMeasure (dirichletVolume ρ R) :=
            dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
          let w := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
          Real.exp (-E * T) * (a * (κ * (r ^ d * volume.real (sourceBall (0 : PDE.Vec d) 1)))) ^ 2 ≤
            inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s w)
              (SpectralHeat.heatOperator b eigenvalue hpos t w) := by
  obtain ⟨E, K, r, a, hE, hK, hr, hrR, ha, hex⟩ :=
    exists_sourceBall_first_eigenfunction_uniform_interior_lower hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell T
  obtain ⟨eig, u, heig, heE, hu0, hnorm, henergy, hmin, hweak, hub, hlower⟩ := hex hell
  have hsub : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R := by
    rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr,
      ← pde_ball_eq_sourceBall (0 : PDE.Vec d) hR]
    exact PDE.euclideanBall_mono hr.le hrR.le
  refine ⟨eig, u, heig, heE, hnorm, hweak, hlower, ?_⟩
  apply exists_native_weakEigenfunction_heat_pairing_two_times_scaled hd hκ hell R hR u eig E
    heig.le heE hweak ?_ 0 r hr hsub a ha.le hlower T
  simpa only [weightedL2Pairing] using hnorm



/-- The coefficients of two Hilbert-space vectors have an absolutely summable pairing. -/
theorem hilbert_basis_abs_inner_summable {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (b : HilbertBasis ℕ ℝ H) (f g : H) :
    Summable (fun n : ℕ => |inner ℝ (b.repr f n) (b.repr g n)|) := by
  have hs : Summable (fun n : ℕ => inner ℝ (b.repr f n) (b.repr g n)) :=
    lp.summable_inner (b.repr f) (b.repr g)
  exact hs.abs

/-- Cross pairings of indicator functions have an absolutely summable spectral
expansion with the actual eigenfunction integrals over each set. -/
theorem indicator_heat_cross_series {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) :
    let a := indicatorConstLp 2 hA hμA (1 : ℝ)
    let c := indicatorConstLp 2 hB hμB (1 : ℝ)
    Summable (fun n => |(∫ x in A, b n x ∂μ) *
      (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))|) ∧
    inner ℝ a (SpectralHeat.heatOperator b eigenvalue hpos t c) =
      ∑' n, (∫ x in A, b n x ∂μ) *
        (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ)) := by
  let a := indicatorConstLp 2 hA hμA (1 : ℝ)
  let c := indicatorConstLp 2 hB hμB (1 : ℝ)
  have hc (n : ℕ) : b.repr a n = ∫ x in A, b n x ∂μ := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact L2.inner_indicatorConstLp_one hA hμA (b n)
  have hd (n : ℕ) : b.repr c n = ∫ x in B, b n x ∂μ := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact L2.inner_indicatorConstLp_one hB hμB (b n)
  have hterm (n : ℕ) : inner ℝ (b.repr a n)
      (b.repr (SpectralHeat.heatOperator b eigenvalue hpos t c) n) =
      (∫ x in A, b n x ∂μ) *
        (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ)) := by
    rw [SpectralHeat.heatOperator_repr, hc, hd]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
    ring
  constructor
  · have heq : (fun n : ℕ => |inner ℝ (b.repr a n)
        (b.repr (SpectralHeat.heatOperator b eigenvalue hpos t c) n)|) =
        (fun n : ℕ => |(∫ x in A, b n x ∂μ) *
          (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))|) :=
      funext (fun n => congrArg abs (hterm n))
    rw [← heq]
    exact hilbert_basis_abs_inner_summable b a
      (SpectralHeat.heatOperator b eigenvalue hpos t c)
  · rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
    exact tsum_congr hterm

/-- Finite spectral truncations control arbitrary cross pairings uniformly in time. -/
theorem heat_cross_finite_tail {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop)
    (M : ℝ) : ∃ N : ℕ, ∀ (t : ℝ≥0) (f g : H),
      |inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t g) -
        inner ℝ f (∑ n ∈ Finset.range N,
          Real.exp (-eigenvalue n * t) • (b.repr g n • b n))| ≤
        Real.exp (-M * t) * ‖f‖ * ‖g‖ := by
  obtain ⟨N, hN⟩ := SpectralHeat.heatOperator_finite_tail b eigenvalue hpos hlim M
  refine ⟨N, fun t f g => ?_⟩
  rw [← inner_sub_right]
  calc
    |inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t g -
        ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * t) • (b.repr g n • b n))| ≤
        ‖f‖ * ‖SpectralHeat.heatOperator b eigenvalue hpos t g -
        ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * t) • (b.repr g n • b n)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (Real.exp (-M * t) * ‖g‖) :=
      mul_le_mul_of_nonneg_left (hN t g) (norm_nonneg _)
    _ = Real.exp (-M * t) * ‖f‖ * ‖g‖ := by ring


/-- The finite-tail cross-pairing error for two indicators is controlled by
both weighted set masses, with the cutoff chosen before time and the sets. -/
theorem indicator_heat_cross_finite_tail {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop) (M : ℝ) :
    ∃ N : ℕ, ∀ (t : ℝ≥0) (A B : Set X)
      (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞),
      let a := indicatorConstLp 2 hA hμA (1 : ℝ)
      let c := indicatorConstLp 2 hB hμB (1 : ℝ)
      |inner ℝ a (SpectralHeat.heatOperator b eigenvalue hpos t c) -
        inner ℝ a (∑ n ∈ Finset.range N,
          Real.exp (-eigenvalue n * t) • (b.repr c n • b n))| ≤
        Real.exp (-M * t) * Real.sqrt (μ.real A) * Real.sqrt (μ.real B) := by
  obtain ⟨N, hN⟩ := heat_cross_finite_tail b eigenvalue hpos hlim M
  refine ⟨N, fun t A B hA hB hμA hμB => ?_⟩
  have hnormA : ‖indicatorConstLp 2 hA hμA (1 : ℝ)‖ = Real.sqrt (μ.real A) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  have hnormB : ‖indicatorConstLp 2 hB hμB (1 : ℝ)‖ = Real.sqrt (μ.real B) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  simpa only [hnormA, hnormB] using hN t
    (indicatorConstLp 2 hA hμA (1 : ℝ)) (indicatorConstLp 2 hB hμB (1 : ℝ))


/-- The indicator truncation bound written using the eigenfunction integrals. -/
theorem indicator_heat_cross_finite_sum {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop) (M : ℝ) :
    ∃ N : ℕ, ∀ (t : ℝ≥0) (A B : Set X)
      (hA : MeasurableSet A) (hB : MeasurableSet B)
      (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞),
      let a := indicatorConstLp 2 hA hμA (1 : ℝ)
      let c := indicatorConstLp 2 hB hμB (1 : ℝ)
      |inner ℝ a (SpectralHeat.heatOperator b eigenvalue hpos t c) -
        ∑ n ∈ Finset.range N, (∫ x in A, b n x ∂μ) *
          (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))| ≤
        Real.exp (-M * t) * Real.sqrt (μ.real A) * Real.sqrt (μ.real B) := by
  obtain ⟨N, hN⟩ := indicator_heat_cross_finite_tail μ b eigenvalue hpos hlim M
  refine ⟨N, fun t A B hA hB hμA hμB => ?_⟩
  let a := indicatorConstLp 2 hA hμA (1 : ℝ)
  let c := indicatorConstLp 2 hB hμB (1 : ℝ)
  have hc (n : ℕ) : b.repr a n = ∫ x in A, b n x ∂μ := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact L2.inner_indicatorConstLp_one hA hμA (b n)
  have hd (n : ℕ) : b.repr c n = ∫ x in B, b n x ∂μ := by
    rw [b.repr_apply_apply, real_inner_comm]
    exact L2.inner_indicatorConstLp_one hB hμB (b n)
  have heq : inner ℝ a (∑ n ∈ Finset.range N,
      Real.exp (-eigenvalue n * t) • (b.repr c n • b n)) =
      ∑ n ∈ Finset.range N, (∫ x in A, b n x ∂μ) *
        (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ)) := by
    simp only [inner_sum, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro n hn
    rw [← hc, ← hd]
    simp only [b.repr_apply_apply]
    rw [real_inner_comm (b n) a]
    ring
  rw [← heq]
  exact hN t A B hA hB hμA hμB


/-- Cross pairings and finite-mode errors for the genuine weighted Dirichlet basis. -/
theorem exists_dirichletHilbert_indicator_cross_series_and_tail {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let μ := dirichletVolume ρ R
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (hpos : ∀ n, 0 ≤ eigenvalue n),
      (∀ n, 0 < eigenvalue n) ∧ Filter.Tendsto eigenvalue Filter.atTop Filter.atTop ∧
      (∀ n, b n = J (u n)) ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ (t : ℝ≥0) (A B : Set (PDE.Vec d))
        (hA : MeasurableSet A) (hB : MeasurableSet B)
        (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞),
        let a := indicatorConstLp 2 hA hμA (1 : ℝ)
        let c := indicatorConstLp 2 hB hμB (1 : ℝ)
        Summable (fun n => |(∫ x in A, b n x ∂μ) *
          (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))|) ∧
        inner ℝ a (SpectralHeat.heatOperator b eigenvalue hpos t c) =
          ∑' n, (∫ x in A, b n x ∂μ) *
            (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ)) ∧
        |inner ℝ a (SpectralHeat.heatOperator b eigenvalue hpos t c) -
          ∑ n ∈ Finset.range N, (∫ x in A, b n x ∂μ) *
            (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))| ≤
          Real.exp (-M * t) * Real.sqrt (μ.real A) * Real.sqrt (μ.real B) := by
  dsimp only
  obtain ⟨eigenvalue, u, b, hpos, hp, hlim, hb, _⟩ :=
    exists_dirichletHilbert_heat_finite_tail hd hκ h R hR
  refine ⟨eigenvalue, u, b, hpos, hp, hlim, hb, ?_⟩
  intro M
  obtain ⟨N, hN⟩ := indicator_heat_cross_finite_sum (dirichletVolume ρ R)
    b eigenvalue hpos hlim M
  refine ⟨N, fun t A B hA hB hμA hμB => ?_⟩
  exact ⟨(indicator_heat_cross_series (dirichletVolume ρ R) A B hA hB hμA hμB
    b eigenvalue hpos t).1,
    (indicator_heat_cross_series (dirichletVolume ρ R) A B hA hB hμA hμB
      b eigenvalue hpos t).2, hN t A B hA hB hμA hμB⟩


/-- A spectral minimum and gap coexist with the finite indicator pairing
estimate for the same basis and eigenvalue sequence. -/
theorem indicator_heat_cross_finite_sum_with_gap {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop) :
    ∃ (j : ℕ) (δ : ℝ), 0 < δ ∧ (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ (t : ℝ≥0) (A B : Set X)
        (hA : MeasurableSet A) (hB : MeasurableSet B)
        (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞),
        |inner ℝ (indicatorConstLp 2 hA hμA (1 : ℝ))
          (SpectralHeat.heatOperator b eigenvalue hpos t
            (indicatorConstLp 2 hB hμB (1 : ℝ))) -
          ∑ n ∈ Finset.range N, (∫ x in A, b n x ∂μ) *
            (Real.exp (-eigenvalue n * t) * (∫ x in B, b n x ∂μ))| ≤
          Real.exp (-M * t) * Real.sqrt (μ.real A) * Real.sqrt (μ.real B) := by
  obtain ⟨j, hj, δ, hδ, hgap⟩ := TubeProbability.spectral_minimum_and_gap eigenvalue hlim
  exact ⟨j, δ, hδ, hj, hgap, indicator_heat_cross_finite_sum μ b eigenvalue hpos hlim⟩

#print axioms indicator_heat_cross_finite_sum_with_gap

/-- Both signed parts of an actual Rayleigh minimizer are minimizers, including
zero parts. No normalization or simplicity assumption is needed. -/
theorem rayleigh_minimizer_parts {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤)
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : PDE.Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ) {eigenvalue : ℝ}
    (w : Homogenization.H10Function U)
    (hmin : ∀ v : Homogenization.H10Function U,
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
        dirichletEnergyPairing A v.toH1Function v.toH1Function)
    (heq : dirichletEnergyPairing A w.toH1Function w.toH1Function =
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function) :
    ∃ p n : Homogenization.H10Function U,
      p.toH1Function.toFun = (fun x => max (w.toH1Function.toFun x) 0) ∧
      n.toH1Function.toFun = (fun x => max (-w.toH1Function.toFun x) 0) ∧
      dirichletEnergyPairing A p.toH1Function p.toH1Function =
        eigenvalue * weightedL2Pairing ρ p.toH1Function p.toH1Function ∧
      dirichletEnergyPairing A n.toH1Function n.toH1Function =
        eigenvalue * weightedL2Pairing ρ n.toH1Function n.toH1Function ∧
      IsWeakSolutionOn A U p.toH1Function
        (fun x => eigenvalue * ρ x * p.toH1Function.toFun x) (fun _ => 0) ∧
      IsWeakSolutionOn A U n.toH1Function
        (fun x => eigenvalue * ρ x * n.toH1Function.toFun x) (fun _ => 0) := by
  obtain ⟨v, hv, _, hm, hE⟩ := exists_abs_h10_preserving_energy hU hfin w
  have hmass : weightedL2Pairing ρ v.toH1Function v.toH1Function =
      weightedL2Pairing ρ w.toH1Function w.toH1Function := by
    simpa only [weightedL2Pairing, mul_assoc, ← pow_two] using hm ρ
  have henergy : dirichletEnergyPairing A v.toH1Function v.toH1Function =
      dirichletEnergyPairing A w.toH1Function w.toH1Function := by
    simpa only [dirichletEnergyPairing, PDE.vecDot_comm] using hE A
  have hs (t : ℝ) :
      dirichletEnergyPairing A (v.toH1Function + t • w.toH1Function)
          (v.toH1Function + t • w.toH1Function) -
        eigenvalue * weightedL2Pairing ρ (v.toH1Function + t • w.toH1Function)
          (v.toH1Function + t • w.toH1Function) =
      (2 * t) * (dirichletEnergyPairing A v.toH1Function w.toH1Function -
        eigenvalue * weightedL2Pairing ρ v.toH1Function w.toH1Function) := by
    rw [dirichletEnergyPairing_add_smul_left hA,
      dirichletEnergyPairing_add_smul_right hA,
      dirichletEnergyPairing_add_smul_right hA,
      dirichletEnergyPairing_symm hAsymm w.toH1Function v.toH1Function,
      weightedL2Pairing_add_smul_left hρ, weightedL2Pairing_add_smul_right hρ,
      weightedL2Pairing_add_smul_right hρ,
      weightedL2Pairing_symm ρ w.toH1Function v.toH1Function, henergy, hmass, heq]
    ring
  have hp := hmin (v + (1 : ℝ) • w)
  have hn := hmin (v + (-1 : ℝ) • w)
  change eigenvalue * weightedL2Pairing ρ (v.toH1Function + (1 : ℝ) • w.toH1Function)
    (v.toH1Function + (1 : ℝ) • w.toH1Function) ≤
    dirichletEnergyPairing A (v.toH1Function + (1 : ℝ) • w.toH1Function)
      (v.toH1Function + (1 : ℝ) • w.toH1Function) at hp
  change eigenvalue * weightedL2Pairing ρ (v.toH1Function + (-1 : ℝ) • w.toH1Function)
    (v.toH1Function + (-1 : ℝ) • w.toH1Function) ≤
    dirichletEnergyPairing A (v.toH1Function + (-1 : ℝ) • w.toH1Function)
      (v.toH1Function + (-1 : ℝ) • w.toH1Function) at hn
  have hc : dirichletEnergyPairing A v.toH1Function w.toH1Function -
      eigenvalue * weightedL2Pairing ρ v.toH1Function w.toH1Function = 0 := by
    have hp' := hs 1
    have hn' := hs (-1)
    linarith only [hp, hn, hp', hn']
  have he (t : ℝ) : dirichletEnergyPairing A (v.toH1Function + t • w.toH1Function)
      (v.toH1Function + t • w.toH1Function) = eigenvalue *
      weightedL2Pairing ρ (v.toH1Function + t • w.toH1Function)
        (v.toH1Function + t • w.toH1Function) := by
    have hh := hs t
    rw [hc, mul_zero] at hh
    exact sub_eq_zero.mp hh
  let p : Homogenization.H10Function U := (1 / 2 : ℝ) • (v + (1 : ℝ) • w)
  let n : Homogenization.H10Function U := (1 / 2 : ℝ) • (v + (-1 : ℝ) • w)
  have hep : dirichletEnergyPairing A p.toH1Function p.toH1Function =
      eigenvalue * weightedL2Pairing ρ p.toH1Function p.toH1Function := by
    change dirichletEnergyPairing A ((1 / 2 : ℝ) • (v.toH1Function + (1 : ℝ) • w.toH1Function))
      ((1 / 2 : ℝ) • (v.toH1Function + (1 : ℝ) • w.toH1Function)) =
      eigenvalue * weightedL2Pairing ρ ((1 / 2 : ℝ) • (v.toH1Function + (1 : ℝ) • w.toH1Function))
        ((1 / 2 : ℝ) • (v.toH1Function + (1 : ℝ) • w.toH1Function))
    rw [dirichletEnergyPairing_smul_self, weightedL2Pairing_smul_self, he 1]
    ring
  have hen : dirichletEnergyPairing A n.toH1Function n.toH1Function =
      eigenvalue * weightedL2Pairing ρ n.toH1Function n.toH1Function := by
    change dirichletEnergyPairing A ((1 / 2 : ℝ) • (v.toH1Function + (-1 : ℝ) • w.toH1Function))
      ((1 / 2 : ℝ) • (v.toH1Function + (-1 : ℝ) • w.toH1Function)) =
      eigenvalue * weightedL2Pairing ρ ((1 / 2 : ℝ) • (v.toH1Function + (-1 : ℝ) • w.toH1Function))
        ((1 / 2 : ℝ) • (v.toH1Function + (-1 : ℝ) • w.toH1Function))
    rw [dirichletEnergyPairing_smul_self, weightedL2Pairing_smul_self, he (-1)]
    ring
  refine ⟨p, n, ?_, ?_, hep, hen,
    rayleigh_minimizer_weak_solution hA hAsymm hρ p hmin hep,
    rayleigh_minimizer_weak_solution hA hAsymm hρ n hmin hen⟩
  · funext x
    change (1 / 2 : ℝ) * (v.toH1Function.toFun x + 1 * w.toH1Function.toFun x) = _
    rw [hv]
    dsimp only
    rcases le_total 0 (w.toH1Function.toFun x) with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx]; ring
    · rw [abs_of_nonpos hx, max_eq_right hx]; ring
  · funext x
    change (1 / 2 : ℝ) * (v.toH1Function.toFun x + (-1) * w.toH1Function.toFun x) = _
    rw [hv]
    dsimp only
    rcases le_total 0 (w.toH1Function.toFun x) with hx | hx
    · rw [abs_of_nonneg hx, max_eq_right (neg_nonpos.mpr hx)]; ring
    · rw [abs_of_nonpos hx, max_eq_left (neg_nonneg.mpr hx)]; ring

#print axioms rayleigh_minimizer_parts

/-- Two normalized bounded nonnegative source-ball eigenfunctions cannot be
almost everywhere disjoint: their common structural interior ball has positive
volume and both admit positive lower bounds there. -/
theorem sourceBall_normalized_eigenfunctions_not_ae_disjoint {d : ℕ}
    (hd : 2 ≤ d) {κ R K : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : Fin 2 → PDE.Vec d → ℝ) (g : Fin 2 → PDE.Vec d → PDE.Vec d)
    (eigenvalue : Fin 2 → ℝ)
    (hu : ∀ j, MemLp (u j) 2 (volume.restrict (sourceBall 0 R)))
    (hg : ∀ j i, MemLp (fun x => g j x i) 2 (volume.restrict (sourceBall 0 R)))
    (hw : ∀ j, HasWeakGradient (sourceBall 0 R) (u j) (g j))
    (he : ∀ j, 0 ≤ eigenvalue j)
    (hweak : ∀ j (ψ : PDE.Vec d → ℝ), IsSpatialTest (sourceBall 0 R) ψ →
      (∫ x in sourceBall 0 R, dot ((α x).mulVec (g j x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue j * ∫ x in sourceBall 0 R, (ρ x * u j x) * ψ x)
    (hpos : ∀ j, ∀ᵐ x ∂volume.restrict (sourceBall 0 R), 0 ≤ u j x)
    (hnorm : ∀ j, (∫ x in sourceBall 0 R, ρ x * (u j x) ^ 2) = 1)
    (hbound : ∀ j, ∀ᵐ x ∂volume.restrict (sourceBall 0 R), |u j x| ≤ K) :
    ¬ ∀ᵐ x ∂volume.restrict (sourceBall 0 R), u 0 x * u 1 x = 0 := by
  obtain ⟨r, a, hr, hrR, ha, hlower⟩ :=
    exists_uniform_sourceBall_eigenfunction_interior_lower hd hκ hR (K := K)
  have h0 := hlower ρ α hell (u 0) (g 0) (hu 0) (hg 0) (hw 0)
    (eigenvalue 0) (he 0) (hweak 0) (hpos 0) (hnorm 0) (hbound 0)
  have h1 := hlower ρ α hell (u 1) (g 1) (hu 1) (hg 1) (hw 1)
    (eigenvalue 1) (he 1) (hweak 1) (hpos 1) (hnorm 1) (hbound 1)
  have hsub : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall 0 R := by
    rw [← TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hr,
      ← TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hR]
    intro x hx
    change euclideanSqDist x 0 < r ^ 2 at hx
    change euclideanSqDist x 0 < R ^ 2
    nlinarith only [hx, hr, hrR]
  have hmeasure : volume (sourceBall (0 : PDE.Vec d) r) ≠ 0 := by
    have hv := volume_euclideanBall_toReal_pos (0 : PDE.Vec d) hr
    rw [TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hr] at hv
    intro hz
    simp only [hz, ENNReal.toReal_zero, lt_self_iff_false] at hv
  intro hdisjoint
  have hdsmall := ae_restrict_of_ae_restrict_of_subset hsub hdisjoint
  have hfalse : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), False := by
    filter_upwards [h0, h1, hdsmall] with x hx0 hx1 hx
    have : 0 < u 0 x * u 1 x := mul_pos (lt_of_lt_of_le ha hx0) (lt_of_lt_of_le ha hx1)
    linarith only [this, hx]
  have hne : (ae (volume.restrict (sourceBall (0 : PDE.Vec d) r))).NeBot :=
    ae_neBot.mpr (mt Measure.restrict_eq_zero.mp hmeasure)
  exact hne.ne (Filter.eventually_false_iff_eq_bot.mp hfalse)

#print axioms sourceBall_normalized_eigenfunctions_not_ae_disjoint


/-- A positive-mass Rayleigh minimizer can be normalized by a positive
scalar while retaining its eigenvalue equation and pointwise sign. -/
theorem normalize_nonnegative_rayleigh_minimizer {d : ℕ} {U : Set (PDE.Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hAsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : PDE.Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ) {eigenvalue : ℝ}
    (w : Homogenization.H10Function U)
    (hpos : ∀ x, 0 ≤ w.toH1Function.toFun x)
    (hmass : 0 < weightedL2Pairing ρ w.toH1Function w.toH1Function)
    (hmin : ∀ v : Homogenization.H10Function U,
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
        dirichletEnergyPairing A v.toH1Function v.toH1Function)
    (heq : dirichletEnergyPairing A w.toH1Function w.toH1Function =
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function) :
    ∃ (c : ℝ) (v : Homogenization.H10Function U),
      0 < c ∧ v = c • w ∧ (∀ x, 0 ≤ v.toH1Function.toFun x) ∧
      weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 ∧
      dirichletEnergyPairing A v.toH1Function v.toH1Function = eigenvalue ∧
      IsWeakSolutionOn A U v.toH1Function
        (fun x => eigenvalue * ρ x * v.toH1Function.toFun x) (fun _ => 0) := by
  let m := weightedL2Pairing ρ w.toH1Function w.toH1Function
  let c := (Real.sqrt m)⁻¹
  let v : Homogenization.H10Function U := c • w
  have hc : 0 < c := inv_pos.mpr (Real.sqrt_pos.mpr hmass)
  have hs : c ^ 2 = m⁻¹ := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hmass.le]
  have hvnorm : weightedL2Pairing ρ v.toH1Function v.toH1Function = 1 := by
    change weightedL2Pairing ρ (c • w.toH1Function) (c • w.toH1Function) = 1
    rw [weightedL2Pairing_smul_self, hs]
    exact inv_mul_cancel₀ hmass.ne'
  have hveq : dirichletEnergyPairing A v.toH1Function v.toH1Function =
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function := by
    change dirichletEnergyPairing A (c • w.toH1Function) (c • w.toH1Function) =
      eigenvalue * weightedL2Pairing ρ (c • w.toH1Function) (c • w.toH1Function)
    rw [dirichletEnergyPairing_smul_self, weightedL2Pairing_smul_self, heq]
    ring
  refine ⟨c, v, hc, rfl, ?_, hvnorm, ?_,
    rayleigh_minimizer_weak_solution hA hAsymm hρ v hmin hveq⟩
  · intro x
    change 0 ≤ c * w.toH1Function.toFun x
    exact mul_nonneg hc.le (hpos x)
  · simpa only [hvnorm, mul_one] using hveq

#print axioms normalize_nonnegative_rayleigh_minimizer


/-- For a strictly positive density, zero weighted mass is equivalent to
vanishing almost everywhere. -/
theorem weightedL2Pairing_self_eq_zero_iff_ae {d : ℕ} {U : Set (PDE.Vec d)}
    {ρ : PDE.Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (hρpos : ∀ᵐ x ∂volumeOn U, 0 < ρ x)
    (w : Homogenization.H1Function U) :
    weightedL2Pairing ρ w w = 0 ↔ ∀ᵐ x ∂volumeOn U, w.toFun x = 0 := by
  have hnonneg : ∀ᵐ x ∂volumeOn U, 0 ≤ ρ x * w.toFun x * w.toFun x := by
    filter_upwards [hρpos] with x hx
    simpa only [mul_assoc, ← pow_two] using mul_nonneg hx.le (sq_nonneg (w.toFun x))
  rw [weightedL2Pairing, integral_eq_zero_iff_of_nonneg_ae hnonneg
    (weightedL2Pairing_integrable hρ w w)]
  constructor
  · intro hz
    filter_upwards [hρpos, hz] with x hx hxz
    have hsq : w.toFun x ^ 2 = 0 := by
      have : ρ x * w.toFun x ^ 2 = 0 := by simpa only [Pi.zero_apply, pow_two, mul_assoc] using hxz
      exact (mul_eq_zero.mp this).resolve_left hx.ne'
    exact (pow_eq_zero_iff two_ne_zero).mp hsq
  · intro hz
    filter_upwards [hz] with x hx
    simp only [hx, mul_zero, Pi.zero_apply]

#print axioms weightedL2Pairing_self_eq_zero_iff_ae


/-- Native bounded nonnegative normalized source-ball eigenfunctions overlap
on a set of positive measure. -/
theorem sourceBall_native_normalized_eigenfunctions_not_ae_disjoint {d : ℕ}
    (hd : 2 ≤ d) {κ R K : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : Fin 2 → Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (eigenvalue : Fin 2 → ℝ) (he : ∀ j, 0 ≤ eigenvalue j)
    (hweak : ∀ j, IsWeakSolutionOn α (sourceBall 0 R) (u j).toH1Function
      (fun x => eigenvalue j * ρ x * (u j).toH1Function.toFun x) (fun _ => 0))
    (hpos : ∀ j x, 0 ≤ (u j).toH1Function.toFun x)
    (hnorm : ∀ j, weightedL2Pairing ρ (u j).toH1Function (u j).toH1Function = 1)
    (hbound : ∀ j, ∀ᵐ x ∂volume.restrict (sourceBall 0 R),
      |(u j).toH1Function.toFun x| ≤ K) :
    ¬ ∀ᵐ x ∂volume.restrict (sourceBall 0 R),
      (u 0).toH1Function.toFun x * (u 1).toH1Function.toFun x = 0 := by
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  let : IsFiniteMeasure (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hfin
  apply sourceBall_normalized_eigenfunctions_not_ae_disjoint hd hκ hR ρ α hell
    (fun j => (u j).toH1Function.toFun) (fun j => (u j).toH1Function.grad)
    eigenvalue (fun j => (u j).toH1Function.memL2)
    (fun j => (u j).toH1Function.gradMemL2) ?_ he ?_ ?_ ?_ hbound
  · intro j i
    refine ⟨(show IntegrableOn (u j).toH1Function.toFun (sourceBall 0 R) volume from
      (u j).toH1Function.memL2.integrable (by norm_num)).locallyIntegrableOn,
      (show IntegrableOn (fun x => (u j).toH1Function.grad x i) (sourceBall 0 R) volume from
        ((u j).toH1Function.gradMemL2 i).integrable (by norm_num)).locallyIntegrableOn, ?_⟩
    intro ψ hψ
    simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
      (u j).toH1Function.hasWeakGradient i ψ hψ.1 hψ.2.1 hψ.2.2
  · intro j ψ hψ
    let φ : TestFunction (TubeProbability.dirichletBall (d := d) R) ℝ ⊤ :=
      ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
    exact TubeProbability.native_weakEigenEquation_on_smooth R (u j) (eigenvalue j) (hweak j) φ
  · intro j
    exact ae_of_all _ (hpos j)
  · intro j
    simpa only [weightedL2Pairing, pow_two, mul_assoc] using hnorm j

#print axioms sourceBall_native_normalized_eigenfunctions_not_ae_disjoint


/-- Every normalized native weak eigenfunction on the source ball has a
uniform absolute bound when its eigenvalue has a prescribed upper bound. -/
theorem exists_sourceBall_normalized_eigenfunction_abs_bound {d : ℕ}
    (hd : 2 ≤ d) {κ R E : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hE : 0 ≤ E) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (w : Homogenization.H10Function (sourceBall 0 R))
      (eigenvalue : ℝ), 0 ≤ eigenvalue → eigenvalue ≤ E →
      IsWeakSolutionOn α (sourceBall 0 R) w.toH1Function
        (fun x => eigenvalue * ρ x * w.toH1Function.toFun x) (fun _ => 0) →
      weightedL2Pairing ρ w.toH1Function w.toH1Function = 1 →
      ∀ᵐ x ∂volume.restrict (sourceBall 0 R), |w.toH1Function.toFun x| ≤ K := by
  obtain ⟨K, hK, hamp⟩ := exists_normalized_eigenfunction_ball_abs_amplitude
    hd (pow_pos hκ 3) hκ (inv_nonneg.mpr hκ.le) hE hR
  refine ⟨K, hK, ?_⟩
  intro ρ α hell w eigenvalue he heE hweak hnorm
  have hU : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (TubeProbability.dirichletBall (d := d) R).isOpen
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ hell hU.measurableSet
  have hρ : AEStronglyMeasurable ρ (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
    hell.1.aestronglyMeasurable
  have hρlower : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R), κ ≤ ρ x :=
    ae_of_all _ fun x => (hell.2.2 x).1
  have hρM : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R), |ρ x| ≤ κ⁻¹ :=
    ae_of_all _ fun x =>
      (abs_of_nonneg (hκ.le.trans (hell.2.2 x).1)).trans_le (hell.2.2 x).2.1
  have hb := hamp hU hfin hA hρ hρlower hρM w he heE hweak hnorm (0 : PDE.Vec d)
  simpa only [TubeProbability.DimensionLift.pde_ball_eq_sourceBall (0 : PDE.Vec d) hR,
    Set.inter_self] using hb

#print axioms exists_sourceBall_normalized_eigenfunction_abs_bound


/-- Every native source-ball Rayleigh minimizer has one sign almost
 everywhere. -/
theorem sourceBall_rayleigh_minimizer_one_sign {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α) {eigenvalue : ℝ} (he : 0 ≤ eigenvalue)
    (w : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (hmin : ∀ v : Homogenization.H10Function (sourceBall 0 R),
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function ≤
        dirichletEnergyPairing α v.toH1Function v.toH1Function)
    (heq : dirichletEnergyPairing α w.toH1Function w.toH1Function =
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function) :
    (∀ᵐ x ∂volume.restrict (sourceBall 0 R), 0 ≤ w.toH1Function.toFun x) ∨
    (∀ᵐ x ∂volume.restrict (sourceBall 0 R), w.toH1Function.toFun x ≤ 0) := by
  have hU : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (TubeProbability.dirichletBall (d := d) R).isOpen
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ hell hU.measurableSet
  have hρ := (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell
    (volume.restrict (sourceBall (0 : PDE.Vec d) R))).1
  have hsymm : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), (α x).IsSymm :=
    ae_of_all _ fun x => (hell.2.2 x).2.2.1
  have hρpos : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), 0 < ρ x :=
    ae_of_all _ fun x => hκ.trans_le (hell.2.2 x).1
  obtain ⟨p, n, hp, hn, hpe, hne, _, _⟩ :=
    rayleigh_minimizer_parts hU hfin hA hsymm hρ w hmin heq
  have hp0 : ∀ x, 0 ≤ p.toH1Function.toFun x := by
    intro x
    rw [hp]
    exact le_max_right _ _
  have hn0 : ∀ x, 0 ≤ n.toH1Function.toFun x := by
    intro x
    rw [hn]
    exact le_max_right _ _
  have hmass0 (v : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R)) :
      0 ≤ weightedL2Pairing ρ v.toH1Function v.toH1Function := by
    apply integral_nonneg_of_ae
    filter_upwards [hρpos] with x hx
    change 0 ≤ ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x
    simpa only [mul_assoc, ← pow_two] using mul_nonneg hx.le (sq_nonneg _)
  by_cases hpz : weightedL2Pairing ρ p.toH1Function p.toH1Function = 0
  · right
    have hpzero := (weightedL2Pairing_self_eq_zero_iff_ae hρ hρpos p.toH1Function).mp hpz
    filter_upwards [hpzero] with x hx
    rw [hp] at hx
    exact le_trans (le_max_left _ _) (le_of_eq hx)
  by_cases hnz : weightedL2Pairing ρ n.toH1Function n.toH1Function = 0
  · left
    have hnzero := (weightedL2Pairing_self_eq_zero_iff_ae hρ hρpos n.toH1Function).mp hnz
    filter_upwards [hnzero] with x hx
    rw [hn] at hx
    have : -w.toH1Function.toFun x ≤ 0 := le_trans (le_max_left _ _) (le_of_eq hx)
    linarith
  · have hpm : 0 < weightedL2Pairing ρ p.toH1Function p.toH1Function :=
      lt_of_le_of_ne (hmass0 p) (Ne.symm hpz)
    have hnm : 0 < weightedL2Pairing ρ n.toH1Function n.toH1Function :=
      lt_of_le_of_ne (hmass0 n) (Ne.symm hnz)
    obtain ⟨cp, vp, hcp, hvp, hvpp, hvpn, _, hvpw⟩ :=
      normalize_nonnegative_rayleigh_minimizer hA hsymm hρ p hp0 hpm hmin hpe
    obtain ⟨cn, vn, hcn, hvn, hvnp, hvnn, _, hvnw⟩ :=
      normalize_nonnegative_rayleigh_minimizer hA hsymm hρ n hn0 hnm hmin hne
    obtain ⟨K, _, hbound⟩ := exists_sourceBall_normalized_eigenfunction_abs_bound hd hκ hR he
    let u : Fin 2 → Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R) :=
      ![vp, vn]
    have hdisjoint : ∀ᵐ x ∂volume.restrict (sourceBall 0 R),
        (u 0).toH1Function.toFun x * (u 1).toH1Function.toFun x = 0 := by
      apply ae_of_all
      intro x
      change vp.toH1Function.toFun x * vn.toH1Function.toFun x = 0
      rw [hvp, hvn]
      change (cp * p.toH1Function.toFun x) * (cn * n.toH1Function.toFun x) = 0
      rw [hp, hn]
      dsimp only
      rcases le_total 0 (w.toH1Function.toFun x) with hx | hx
      · rw [max_eq_right (neg_nonpos.mpr hx)]; ring
      · rw [max_eq_right hx]; ring
    exfalso
    apply sourceBall_native_normalized_eigenfunctions_not_ae_disjoint hd (K := K) hκ hR ρ α hell u
      (fun _ => eigenvalue) (fun _ => he) ?_ ?_ ?_ ?_ hdisjoint
    · intro j
      fin_cases j <;> simp only [u] <;> assumption
    · intro j
      fin_cases j <;> simp only [u] <;> assumption
    · intro j
      fin_cases j <;> simp only [u] <;> assumption
    · intro j
      fin_cases j <;> simp only [u]
      · exact hbound ρ α hell vp eigenvalue he le_rfl hvpw hvpn
      · exact hbound ρ α hell vn eigenvalue he le_rfl hvnw hvnn

#print axioms sourceBall_rayleigh_minimizer_one_sign

/-- Linear combinations of vectors attaining the same Rayleigh minimum
also attain that minimum. -/
theorem rayleigh_minimizer_add_smul {d : ℕ} {U : Set (PDE.Vec d)}
    {κ : ℝ} {A : CoeffField d} (hA : IsEllipticFieldOn κ κ⁻¹ U A)
    (hsymm : ∀ᵐ x ∂volumeOn U, (A x).IsSymm)
    {ρ : PDE.Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ) {eigenvalue : ℝ}
    (u v : Homogenization.H10Function U)
    (hmin : ∀ w : Homogenization.H10Function U,
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing A w.toH1Function w.toH1Function)
    (hu : dirichletEnergyPairing A u.toH1Function u.toH1Function =
      eigenvalue * weightedL2Pairing ρ u.toH1Function u.toH1Function)
    (hv : dirichletEnergyPairing A v.toH1Function v.toH1Function =
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function) (t : ℝ) :
    dirichletEnergyPairing A (u + t • v).toH1Function (u + t • v).toH1Function =
      eigenvalue * weightedL2Pairing ρ (u + t • v).toH1Function (u + t • v).toH1Function := by
  have hw := rayleigh_minimizer_weak_solution hA hsymm hρ u hmin hu v
  have hc : dirichletEnergyPairing A u.toH1Function v.toH1Function =
      eigenvalue * weightedL2Pairing ρ u.toH1Function v.toH1Function := by
    change dirichletEnergyPairing A u.toH1Function v.toH1Function = _ at hw
    simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at hw
    rw [show (fun x => eigenvalue * ρ x * u.toH1Function.toFun x *
        v.toH1Function.toFun x) =
        (fun x => eigenvalue * (ρ x * u.toH1Function.toFun x *
          v.toH1Function.toFun x)) by funext x; ring, integral_const_mul] at hw
    exact hw
  change dirichletEnergyPairing A (u.toH1Function + t • v.toH1Function)
      (u.toH1Function + t • v.toH1Function) =
    eigenvalue * weightedL2Pairing ρ (u.toH1Function + t • v.toH1Function)
      (u.toH1Function + t • v.toH1Function)
  rw [dirichletEnergyPairing_add_smul_left hA,
    dirichletEnergyPairing_add_smul_right hA,
    dirichletEnergyPairing_add_smul_right hA,
    dirichletEnergyPairing_symm hsymm v.toH1Function u.toH1Function,
    weightedL2Pairing_add_smul_left hρ, weightedL2Pairing_add_smul_right hρ,
    weightedL2Pairing_add_smul_right hρ,
    weightedL2Pairing_symm ρ v.toH1Function u.toH1Function, hu, hv, hc]
  ring

#print axioms rayleigh_minimizer_add_smul

/-- On a finite domain, a one-signed function with zero integral against a
strictly positive bounded density vanishes almost everywhere. -/
theorem one_sign_weighted_integral_eq_zero_iff_ae {d : ℕ} {U : Set (PDE.Vec d)}
    [IsFiniteMeasure (volumeOn U)] {ρ : PDE.Vec d → ℝ} (hρ : MemLpOn U ⊤ ρ)
    (hρpos : ∀ᵐ x ∂volumeOn U, 0 < ρ x)
    (w : Homogenization.H1Function U)
    (hsign : (∀ᵐ x ∂volumeOn U, 0 ≤ w.toFun x) ∨
      (∀ᵐ x ∂volumeOn U, w.toFun x ≤ 0)) :
    (∫ x in U, ρ x * w.toFun x) = 0 ↔ ∀ᵐ x ∂volumeOn U, w.toFun x = 0 := by
  have hmem : MemL2On U (fun x => ρ x * w.toFun x) := by
    simpa only [mul_comm] using w.memL2.fun_mul hρ
  have hint : IntegrableOn (fun x => ρ x * w.toFun x) U :=
    hmem.integrable (by norm_num)
  constructor
  · intro hz
    have hzero : ∀ᵐ x ∂volumeOn U, ρ x * w.toFun x = 0 := by
      rcases hsign with hp | hn
      · apply (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp hz
        filter_upwards [hρpos, hp] with x hx hw
        exact mul_nonneg hx.le hw
      · have hzneg : (∫ x in U, -(ρ x * w.toFun x)) = 0 := by
          rw [integral_neg, hz, neg_zero]
        have hnint := hint.neg
        have hnzero := (integral_eq_zero_iff_of_nonneg_ae (f := fun x => -(ρ x * w.toFun x))
          (by filter_upwards [hρpos, hn] with x hx hw
              exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hx.le hw)) hnint).mp hzneg
        filter_upwards [hnzero] with x hx
        simpa only [Pi.zero_apply, neg_eq_zero] using hx
    filter_upwards [hρpos, hzero] with x hx hw
    exact (mul_eq_zero.mp hw).resolve_left hx.ne'
  · intro hz
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with x hx
    simp only [hx, mul_zero, Pi.zero_apply]

#print axioms one_sign_weighted_integral_eq_zero_iff_ae

/-- The actual first Rayleigh eigenspace on a source ball is one-dimensional
up to almost-everywhere equality. -/
theorem sourceBall_rayleigh_minimizers_proportional {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α) {eigenvalue : ℝ} (he : 0 ≤ eigenvalue)
    (u v : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (hmin : ∀ w : Homogenization.H10Function (sourceBall 0 R),
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing α w.toH1Function w.toH1Function)
    (hu : dirichletEnergyPairing α u.toH1Function u.toH1Function =
      eigenvalue * weightedL2Pairing ρ u.toH1Function u.toH1Function)
    (hv : dirichletEnergyPairing α v.toH1Function v.toH1Function =
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function)
    (hunonzero : ¬ ∀ᵐ x ∂volumeOn (sourceBall 0 R), u.toH1Function.toFun x = 0) :
    ∃ c : ℝ, ∀ᵐ x ∂volumeOn (sourceBall 0 R),
      v.toH1Function.toFun x = c * u.toH1Function.toFun x := by
  have hU : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (TubeProbability.dirichletBall (d := d) R).isOpen
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (TubeProbability.sourceBall_subset_cube R hR))
  let : IsFiniteMeasure (volumeOn (sourceBall (0 : PDE.Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hfin
  have hA := source_uniformlyElliptic_isEllipticFieldOn hκ hell hU.measurableSet
  have hρ := (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell
    (volume.restrict (sourceBall (0 : PDE.Vec d) R))).1
  have hsymm : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), (α x).IsSymm :=
    ae_of_all _ fun x => (hell.2.2 x).2.2.1
  have hρpos : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), 0 < ρ x :=
    ae_of_all _ fun x => hκ.trans_le (hell.2.2 x).1
  have hsignu := sourceBall_rayleigh_minimizer_one_sign hd hκ hR ρ α hell he u hmin hu
  have hui : (∫ x in sourceBall 0 R, ρ x * u.toH1Function.toFun x) ≠ 0 := by
    intro hz
    exact hunonzero ((one_sign_weighted_integral_eq_zero_iff_ae hρ hρpos u.toH1Function hsignu).mp hz)
  let c : ℝ := (∫ x in sourceBall 0 R, ρ x * v.toH1Function.toFun x) /
    (∫ x in sourceBall 0 R, ρ x * u.toH1Function.toFun x)
  let z := v + (-c) • u
  have hzenergy := rayleigh_minimizer_add_smul hA hsymm hρ v u hmin hv hu (-c)
  have hzsign := sourceBall_rayleigh_minimizer_one_sign hd hκ hR ρ α hell he z hmin hzenergy
  have hint (w : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R)) :
      IntegrableOn (fun x => ρ x * w.toH1Function.toFun x) (sourceBall 0 R) := by
    have hm : MemL2On (sourceBall (0 : PDE.Vec d) R)
        (fun x => ρ x * w.toH1Function.toFun x) := by
      simpa only [mul_comm] using w.toH1Function.memL2.fun_mul hρ
    exact hm.integrable (by norm_num)
  have hzi : (∫ x in sourceBall 0 R, ρ x * z.toH1Function.toFun x) = 0 := by
    change (∫ x in sourceBall 0 R, ρ x *
      (v.toH1Function.toFun x + (-c) * u.toH1Function.toFun x)) = 0
    simp_rw [show ∀ x, ρ x * (v.toH1Function.toFun x + (-c) * u.toH1Function.toFun x) =
      ρ x * v.toH1Function.toFun x + (-c) * (ρ x * u.toH1Function.toFun x) by
        intro x; ring]
    rw [integral_add (hint v) ((hint u).const_mul (-c)), integral_const_mul]
    dsimp only [c]
    field_simp
    ring
  have hz := (one_sign_weighted_integral_eq_zero_iff_ae hρ hρpos z.toH1Function hzsign).mp hzi
  refine ⟨c, ?_⟩
  filter_upwards [hz] with x hx
  change v.toH1Function.toFun x + (-c) * u.toH1Function.toFun x = 0 at hx
  linarith

#print axioms sourceBall_rayleigh_minimizers_proportional

/-- The weighted projection onto a normalized first mode leaves a zero
remainder almost everywhere for every first Rayleigh minimizer. -/
theorem sourceBall_first_mode_weighted_orthogonal_remainder_ae_zero
    {d : ℕ} (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α) {eigenvalue : ℝ} (he : 0 ≤ eigenvalue)
    (u v : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (hmin : ∀ w : Homogenization.H10Function (sourceBall 0 R),
      eigenvalue * weightedL2Pairing ρ w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing α w.toH1Function w.toH1Function)
    (hu : dirichletEnergyPairing α u.toH1Function u.toH1Function =
      eigenvalue * weightedL2Pairing ρ u.toH1Function u.toH1Function)
    (hv : dirichletEnergyPairing α v.toH1Function v.toH1Function =
      eigenvalue * weightedL2Pairing ρ v.toH1Function v.toH1Function)
    (hnorm : weightedL2Pairing ρ u.toH1Function u.toH1Function = 1) :
    ∀ᵐ x ∂volumeOn (sourceBall 0 R),
      (v + (-(weightedL2Pairing ρ v.toH1Function u.toH1Function)) • u).toH1Function.toFun x = 0 := by
  have hρ := (TubeProbability.DimensionLift.uniformlyElliptic_coefficients_memLp_top hκ hell
    (volume.restrict (sourceBall (0 : PDE.Vec d) R))).1
  have hρpos : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), 0 < ρ x :=
    ae_of_all _ fun x => hκ.trans_le (hell.2.2 x).1
  have hunonzero : ¬ ∀ᵐ x ∂volumeOn (sourceBall 0 R), u.toH1Function.toFun x = 0 := by
    intro hz
    have hm := (weightedL2Pairing_self_eq_zero_iff_ae hρ hρpos u.toH1Function).mpr hz
    linarith
  obtain ⟨c, hc⟩ := sourceBall_rayleigh_minimizers_proportional hd hκ hR ρ α hell he
    u v hmin hu hv hunonzero
  have hcval : weightedL2Pairing ρ v.toH1Function u.toH1Function = c := by
    calc
      weightedL2Pairing ρ v.toH1Function u.toH1Function =
          ∫ x in sourceBall 0 R, c * (ρ x * u.toH1Function.toFun x * u.toH1Function.toFun x) := by
        unfold weightedL2Pairing
        apply integral_congr_ae
        filter_upwards [hc] with x hx
        rw [hx]
        ring
      _ = c * weightedL2Pairing ρ u.toH1Function u.toH1Function := integral_const_mul _ _
      _ = c := by rw [hnorm, mul_one]
  filter_upwards [hc] with x hx
  change v.toH1Function.toFun x +
    (-(weightedL2Pairing ρ v.toH1Function u.toH1Function)) * u.toH1Function.toFun x = 0
  rw [hcval, hx]
  ring

#print axioms sourceBall_first_mode_weighted_orthogonal_remainder_ae_zero

/-- Every vector in the complete minimum projection is proportional to the
weighted representative of a normalized native minimum. -/
theorem sourceBall_complete_minimum_projection_proportional {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (he : 0 ≤ eig)
    (hS : ∀ n ∈ S, eigenvalue n = eig)
    (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hg : (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun)
    (hmin : ∀ w : Homogenization.H10Function (sourceBall 0 R),
      eig * weightedL2Pairing ρ w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing α w.toH1Function w.toH1Function)
    (hu : dirichletEnergyPairing α u.toH1Function u.toH1Function =
      eig * weightedL2Pairing ρ u.toH1Function u.toH1Function)
    (hnorm : weightedL2Pairing ρ u.toH1Function u.toH1Function = 1)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ∃ c : ℝ, (∑ n ∈ S, b.repr f n • b n) = c • g := by
  obtain ⟨v, hv, hw⟩ := finite_spectral_projection_native hd hκ hell R hR
    eigenvalue vs b hb hvar S eig hS f
  have hvenergy : dirichletEnergyPairing α v.toH1Function v.toH1Function =
      eig * weightedL2Pairing ρ v.toH1Function v.toH1Function := by
    simpa only [dirichletEnergyPairing, weightedL2Pairing, PDE.vecDot,
      PDE.matVecMul, Matrix.mulVec, dotProduct, dot] using
      native_weakEigenfunction_energy_eq R eig v hw
  have hρ := (uniformlyElliptic_coefficients_memLp_top hκ hell
    (volume.restrict (sourceBall (0 : PDE.Vec d) R))).1
  have hρpos : ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R), 0 < ρ x :=
    ae_of_all _ fun x => hκ.trans_le (hell.2.2 x).1
  have hunonzero : ¬ ∀ᵐ x ∂volumeOn (sourceBall (0 : PDE.Vec d) R),
      u.toH1Function.toFun x = 0 := by
    intro hz
    have hm := (weightedL2Pairing_self_eq_zero_iff_ae hρ hρpos u.toH1Function).mpr hz
    linarith
  obtain ⟨c, hc⟩ := sourceBall_rayleigh_minimizers_proportional hd hκ hR ρ α hell he
    u v hmin hu hvenergy hunonzero
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  refine ⟨c, ?_⟩
  apply Lp.ext
  filter_upwards [hv, hg, hac.ae_le hc, Lp.coeFn_smul c g] with x hx hy hz hs
  simpa only [hs, Pi.smul_apply, smul_eq_mul, hy] using hx.trans hz

#print axioms sourceBall_complete_minimum_projection_proportional

/-- A unit vector fixed by a finite spectral projection identifies that
projection whenever its complete range is contained in the vector's span. -/
theorem finite_projection_eq_unit_rank_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (S : Finset ℕ) (g : H)
    (hg : g = ∑ n ∈ S, b.repr g n • b n) (hnorm : ‖g‖ = 1)
    (hspan : ∀ f : H, ∃ c : ℝ, (∑ n ∈ S, b.repr f n • b n) = c • g)
    (f : H) : (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g := by
  obtain ⟨c, hc⟩ := hspan f
  have hself : inner ℝ g g = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  have hpair : inner ℝ f g = inner ℝ (∑ n ∈ S, b.repr f n • b n) g := by
    calc
      inner ℝ f g = ∑ n ∈ S, b.repr f n * b.repr g n := by
        rw [TubeProbability.lowest_eigenspace_coefficient_eq_projection, ← hg]
      _ = inner ℝ (∑ n ∈ S, b.repr f n • b n) g := by
        simp only [sum_inner, real_inner_smul_left, b.repr_apply_apply]
  rw [hc, real_inner_smul_left, hself, mul_one] at hpair
  rw [hc, hpair]

#print axioms finite_projection_eq_unit_rank_one

/-- The full minimum spectral coefficient for two indicators is the product
of their pairings with the same unit ground vector. -/
theorem finite_projection_indicator_pairing {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (S : Finset ℕ)
    (g : Lp ℝ 2 μ)
    (hproj : ∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞) :
    (∑ n ∈ S, b.repr (indicatorConstLp 2 hA hμA (1 : ℝ)) n *
      b.repr (indicatorConstLp 2 hB hμB (1 : ℝ)) n) =
      (∫ x in A, g x ∂μ) * (∫ x in B, g x ∂μ) := by
  rw [TubeProbability.lowest_eigenspace_coefficient_eq_projection, hproj,
    real_inner_smul_right]
  rw [L2.inner_indicatorConstLp_one, L2.inner_indicatorConstLp_one]
  ring

#print axioms finite_projection_indicator_pairing

/-- The complete actual minimum projection is the rank-one projection onto
the weighted representative of the native normalized ground mode. -/
theorem sourceBall_complete_minimum_projection_rank_one {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (he : 0 ≤ eig)
    (hS : ∀ n, n ∈ S ↔ eigenvalue n = eig)
    (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R)
      u.toH1Function (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0))
    (hmin : ∀ w : Homogenization.H10Function (sourceBall 0 R),
      eig * weightedL2Pairing ρ w.toH1Function w.toH1Function ≤
        dirichletEnergyPairing α w.toH1Function w.toH1Function)
    (hnorm : weightedL2Pairing ρ u.toH1Function u.toH1Function = 1) :
    ∃ g : Lp ℝ 2 (dirichletVolume ρ R),
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧
      ‖g‖ = 1 ∧ ∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g := by
  obtain ⟨g, hg, hgproj, _⟩ := native_weakEigenfunction_eq_finite_spectral_projection
    hd hκ hell R hR eigenvalue vs b hb hvar S eig hS u hweak
  have hu : dirichletEnergyPairing α u.toH1Function u.toH1Function =
      eig * weightedL2Pairing ρ u.toH1Function u.toH1Function := by
    simpa only [dirichletEnergyPairing, weightedL2Pairing, PDE.vecDot,
      PDE.matVecMul, Matrix.mulVec, dotProduct, dot] using
      native_weakEigenfunction_energy_eq R eig u hweak
  have hgself : inner ℝ g g = 1 := by
    rw [dirichletVolume_inner_eq_native hκ hell R g g _ _ hg hg]
    exact hnorm
  have hgnorm : ‖g‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hgself
    nlinarith [norm_nonneg g]
  refine ⟨g, hg, hgnorm, ?_⟩
  intro f
  apply finite_projection_eq_unit_rank_one b S g hgproj hgnorm
  intro z
  exact sourceBall_complete_minimum_projection_proportional hd hκ hR ρ α hell
    eigenvalue vs b hb hvar S eig he (fun n hn => (hS n).1 hn) u g hg hmin hu hnorm z

#print axioms sourceBall_complete_minimum_projection_rank_one

/-- The native ground mode pairs with an interior ball by at least its
Euclidean volume times the density and amplitude lower bounds. -/
theorem sourceBall_ground_indicator_pairing_lower {d : ℕ}
    {κ R r : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (g : Lp ℝ 2 (dirichletVolume ρ R)) (u : PDE.Vec d → ℝ)
    (hgu : (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u)
    (a : ℝ) (ha : 0 ≤ a)
    (hinner : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ u x)
    (c : PDE.Vec d) (s : ℝ) (hs : 0 < s)
    (hsub : sourceBall c s ⊆ sourceBall (0 : PDE.Vec d) r)
    (hsubR : sourceBall c s ⊆ sourceBall (0 : PDE.Vec d) R) :
    a * (κ * volume.real (sourceBall c s)) ≤
      ∫ x in sourceBall c s, g x ∂dirichletVolume ρ R := by
  let : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hf : dirichletVolume ρ R (sourceBall c s) ≠ ∞ := measure_ne_top _ _
  have hlow : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c s), a ≤ g x :=
    dirichletVolume_restrict_ae_lower_of_native ρ R g u hgu _ a
      (ae_restrict_of_ae_restrict_of_subset hsub hinner)
  have hi := integral_mono_ae (integrableOn_const hf :
    IntegrableOn (fun _ : PDE.Vec d => a) (sourceBall c s) (dirichletVolume ρ R))
    (integrableOn_Lp_of_measure_ne_top g fact_one_le_two_ennreal.elim hf) hlow
  have hm : a * (dirichletVolume ρ R).real (sourceBall c s) ≤
      ∫ x in sourceBall c s, g x ∂dirichletVolume ρ R := by
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using hi
  exact (mul_le_mul_of_nonneg_left
    (sourceBall_dirichletVolume_real_lower ρ R hR κ⁻¹ κ hκ.le
      (fun x _ => (hell.2.2 x).2.1) (fun x _ => (hell.2.2 x).1) c s hs hsubR) ha).trans hm

#print axioms sourceBall_ground_indicator_pairing_lower

/-- The complete rank-one minimum projection gives a cross-indicator heat
lower bound after the explicit, generally coefficient-dependent gap time. -/
theorem indicator_heat_cross_rank_one_lower {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (hlim : Filter.Tendsto eigenvalue Filter.atTop Filter.atTop)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n)
    (S : Finset ℕ) (hS : ∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j)
    (g : Lp ℝ 2 μ)
    (hproj : ∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g)
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hμA : μ A ≠ ∞) (hμB : μ B ≠ ∞) (t : ℝ≥0) :
    let f := indicatorConstLp 2 hA hμA (1 : ℝ)
    let k := indicatorConstLp 2 hB hμB (1 : ℝ)
    let c := (∫ x in A, g x ∂μ) * (∫ x in B, g x ∂μ)
    0 < c → Real.log (1 + 2 * (‖f‖ * ‖k‖) / c) / δ ≤ (t : ℝ) →
      Real.exp (-eigenvalue j * (t : ℝ)) * (c / 2) ≤
        inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t k) := by
  dsimp only
  intro hc ht
  obtain ⟨S', hS', htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    hpos hlim j δ hδ hgap
  have hSS : S' = S := by
    ext n
    exact (hS' n).trans (hS n).symm
  subst S'
  have h := htail 0 t (indicatorConstLp 2 hA hμA (1 : ℝ))
    (indicatorConstLp 2 hB hμB (1 : ℝ))
  rw [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply,
    finite_projection_indicator_pairing μ b S g hproj A B hA hB hμA hμB] at h
  simp only [NNReal.coe_zero, zero_add] at h
  exact exponential_tail_lower_bound (eigenvalue j) δ _ _ _ _ hδ hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht h

#print axioms indicator_heat_cross_rank_one_lower

/-- A common native ground mode controls heat between two interior balls.
The constants E, r and a are structural; the gap and time threshold are
chosen after the coefficients. -/
theorem exists_sourceBall_cross_heat_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E r a : ℝ, 0 < E ∧ 0 < r ∧ r < R ∧ 0 < a ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
        a ≤ u.toH1Function.toFun x) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧
      ‖g‖ = 1 ∧
      ∀ (c₁ c₂ : PDE.Vec d) (s₁ s₂ : ℝ) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂),
      sourceBall c₁ s₁ ⊆ sourceBall (0 : PDE.Vec d) r →
      sourceBall c₂ s₂ ⊆ sourceBall (0 : PDE.Vec d) r →
      let A := sourceBall c₁ s₁
      let B := sourceBall c₂ s₂
      let hA : MeasurableSet A := by
        change MeasurableSet (sourceBall c₁ s₁)
        rw [← pde_ball_eq_sourceBall c₁ hs₁]
        exact (PDE.isOpen_euclideanBall c₁ s₁).measurableSet
      let hB : MeasurableSet B := by
        change MeasurableSet (sourceBall c₂ s₂)
        rw [← pde_ball_eq_sourceBall c₂ hs₂]
        exact (PDE.isOpen_euclideanBall c₂ s₂).measurableSet
      letI : IsFiniteMeasure (dirichletVolume ρ R) :=
        dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      let f := indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)
      let k := indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ)
      let C := (a * (κ * volume.real A)) * (a * (κ * volume.real B))
      let c := (∫ x in A, g x ∂dirichletVolume ρ R) *
        (∫ x in B, g x ∂dirichletVolume ρ R)
      0 < C ∧ C ≤ c ∧
      (∀ t : ℝ≥0,
        |inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t k) -
          Real.exp (-eig * (t : ℝ)) * c| ≤
          Real.exp (-(eig + δ) * (t : ℝ)) * (‖f‖ * ‖k‖)) ∧
      ∀ t : ℝ≥0,
        Real.log (1 + 2 * (‖f‖ * ‖k‖) / c) / δ ≤ (t : ℝ) →
        Real.exp (-eig * (t : ℝ)) * (C / 2) ≤
          inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t k) := by
  obtain ⟨E, K, r, a, hE, hK, hr, hrR, ha, hex⟩ :=
    exists_sourceBall_first_eigenfunction_uniform_interior_lower hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, heig, heE, hu0, hnorm, henergy, hmin, hweak, hub, hlower⟩ := hex hell
  obtain ⟨eigenvalue, vs, j, δ, hδ, hp, hlim, ho, hs, hj, hgap, hvar⟩ :=
    exists_dirichletHilbert_spectral_minimum_and_gap hd hκ hell R hR
  let b := HilbertBasis.mk ho (le_of_eq hs.symm)
  have hb (n : ℕ) : b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (vs n) :=
    congrFun (HilbertBasis.coe_mk ho (le_of_eq hs.symm)) n
  have hvarb (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) w) := by
    rw [hb]
    exact hvar n w
  have hnorm' : (∫ x in sourceBall (0 : PDE.Vec d) R,
      ρ x * u.toH1Function.toFun x * u.toH1Function.toFun x) = 1 := by
    simpa only [weightedL2Pairing] using hnorm
  have hmin' : ∀ w : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R),
      eig * (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x) := by
    simpa only [weightedL2Pairing, dirichletEnergyPairing, PDE.vecDot,
      PDE.matVecMul, Matrix.mulVec, dotProduct, dot] using hmin
  obtain ⟨v, hv, ⟨n, hn⟩, hsupport⟩ :=
    native_weakEigenfunction_spectral_coordinate hd hκ hell R hR eigenvalue vs b hb hvarb
      u eig hweak hnorm'
  have hneig : eigenvalue n = eig := by
    by_contra hne
    exact hn (hsupport n hne)
  have heq : eigenvalue j = eig := le_antisymm ((hj n).trans_eq hneig)
    (native_rayleigh_lower_le_spectral_value hκ hell R hR eigenvalue vs b hb hvarb eig hmin' j)
  obtain ⟨S, hS, htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    (fun n => (hp n).le) hlim j δ hδ hgap
  have hSeig (n : ℕ) : n ∈ S ↔ eigenvalue n = eig := by
    simpa only [heq] using hS n
  obtain ⟨g, hgu, hgnorm, hproj⟩ := sourceBall_complete_minimum_projection_rank_one
    hd hκ hR ρ α hell eigenvalue vs b hb hvarb S eig heig.le hSeig u hweak hmin hnorm
  refine ⟨eig, u, eigenvalue, b, (fun n => (hp n).le), j, δ, g,
    heig, heE, heq, hδ, hnorm, hu0, hweak, hlower, hgap, hgu, hgnorm, ?_⟩
  intro c₁ c₂ s₁ s₂ hs₁ hs₂ hsub₁ hsub₂
  have hsubR : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R := by
    rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr,
      ← pde_ball_eq_sourceBall (0 : PDE.Vec d) hR]
    exact PDE.euclideanBall_mono hr.le hrR.le
  have h₁ := sourceBall_ground_indicator_pairing_lower hκ hR ρ α hell g u.toH1Function.toFun
    hgu a ha.le hlower c₁ s₁ hs₁ hsub₁ (hsub₁.trans hsubR)
  have h₂ := sourceBall_ground_indicator_pairing_lower hκ hR ρ α hell g u.toH1Function.toFun
    hgu a ha.le hlower c₂ s₂ hs₂ hsub₂ (hsub₂.trans hsubR)
  have hv₁ : 0 < volume.real (sourceBall c₁ s₁) := by
    rw [← pde_ball_eq_sourceBall c₁ hs₁]
    exact volume_euclideanBall_toReal_pos c₁ hs₁
  have hv₂ : 0 < volume.real (sourceBall c₂ s₂) := by
    rw [← pde_ball_eq_sourceBall c₂ hs₂]
    exact volume_euclideanBall_toReal_pos c₂ hs₂
  dsimp only
  have hc₁ : 0 < a * (κ * volume.real (sourceBall c₁ s₁)) := by positivity
  have hc₂ : 0 < a * (κ * volume.real (sourceBall c₂ s₂)) := by positivity
  have hc : (a * (κ * volume.real (sourceBall c₁ s₁))) *
      (a * (κ * volume.real (sourceBall c₂ s₂))) ≤
      (∫ x in sourceBall c₁ s₁, g x ∂dirichletVolume ρ R) *
        (∫ x in sourceBall c₂ s₂, g x ∂dirichletVolume ρ R) :=
    mul_le_mul h₁ h₂ hc₂.le (hc₁.le.trans h₁)
  refine ⟨mul_pos hc₁ hc₂, hc, ?_, ?_⟩
  · intro t
    have hA : MeasurableSet (sourceBall c₁ s₁) := by
      rw [← pde_ball_eq_sourceBall c₁ hs₁]
      exact (PDE.isOpen_euclideanBall c₁ s₁).measurableSet
    have hB : MeasurableSet (sourceBall c₂ s₂) := by
      rw [← pde_ball_eq_sourceBall c₂ hs₂]
      exact (PDE.isOpen_euclideanBall c₂ s₂).measurableSet
    let _ : IsFiniteMeasure (dirichletVolume ρ R) :=
      dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
    have hμA := measure_ne_top (dirichletVolume ρ R) (sourceBall c₁ s₁)
    have hμB := measure_ne_top (dirichletVolume ρ R) (sourceBall c₂ s₂)
    have ht := htail 0 t (indicatorConstLp 2 hA hμA (1 : ℝ))
      (indicatorConstLp 2 hB hμB (1 : ℝ))
    rw [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply,
      finite_projection_indicator_pairing (dirichletVolume ρ R) b S g hproj
        (sourceBall c₁ s₁) (sourceBall c₂ s₂) hA hB hμA hμB] at ht
    simpa only [NNReal.coe_zero, zero_add, heq] using ht
  · intro t ht
    have hpositive := (mul_pos hc₁ hc₂).trans_le hc
    have h := indicator_heat_cross_rank_one_lower (dirichletVolume ρ R) b eigenvalue
      (fun n => (hp n).le) hlim j δ hδ hgap S hS g hproj _ _ _ _ _ _ t hpositive ht
    rw [heq] at h
    exact (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hc (by norm_num))
      (Real.exp_pos _).le).trans h

#print axioms exists_sourceBall_cross_heat_lower

/-- A single gap-dependent time controls all pairs whose ground coefficients
and tail norms have common bounds. -/
theorem exponential_tail_uniform_lower
    (E eig δ C M : ℝ) (hE : eig ≤ E) (hδ : 0 < δ)
    (hC : 0 < C) (hM : 0 ≤ M)
    (c N τ x : ℝ) (hc : C ≤ c) (hN : 0 ≤ N) (hNM : N ≤ M)
    (hτ : 0 ≤ τ) (ht : Real.log (1 + 2 * M / C) / δ ≤ τ)
    (h : |x - Real.exp (-eig * τ) * c| ≤
      Real.exp (-(eig + δ) * τ) * N) :
    Real.exp (-E * τ) * (C / 2) ≤ x := by
  have hcpos : 0 < c := hC.trans_le hc
  have hratio : 2 * N / c ≤ 2 * M / C := by
    apply (div_le_div_iff₀ hcpos hC).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hNM) hC.le,
      mul_nonneg (sub_nonneg.mpr hc) hM]
  have hlog : Real.log (1 + 2 * N / c) ≤ Real.log (1 + 2 * M / C) := by
    apply Real.log_le_log (by positivity)
    linarith
  have ht' : Real.log (1 + 2 * N / c) / δ ≤ τ :=
    (div_le_div_of_nonneg_right hlog hδ.le).trans ht
  have hx := exponential_tail_lower_bound eig δ c N τ x hδ hcpos hN ht' h
  have he : Real.exp (-E * τ) ≤ Real.exp (-eig * τ) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hcoeff : C / 2 ≤ c / 2 := by linarith
  exact (mul_le_mul he hcoeff (by positivity) (Real.exp_pos _).le).trans hx

#print axioms exponential_tail_uniform_lower

open SubdiffusiveProcess

/-- The indicator norm is bounded uniformly by the density bound and the
volume of the fixed containing cube. -/
theorem sourceBall_indicator_norm_structural_bound {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (A : Set (PDE.Vec d)) (hA : MeasurableSet A) :
    letI : IsFiniteMeasure (dirichletVolume ρ R) :=
      dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
    ‖indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)‖ ≤
      Real.sqrt (κ⁻¹ * volume.real
        (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
          Set (SpatialCoordinates d))) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let ν : Measure (PDE.Vec d) := ENNReal.ofReal κ⁻¹ • volume.restrict (Q : Set _)
  let : IsFiniteMeasure (volume.restrict (Q : Set (PDE.Vec d))) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  let : IsFiniteMeasure ν :=
    (volume.restrict (Q : Set (PDE.Vec d))).smul_finite ENNReal.ofReal_ne_top
  let : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hm : (dirichletVolume ρ R).real A ≤ ν.real A :=
    ENNReal.toReal_mono (measure_ne_top ν A)
      ((dirichletVolume_le_cube ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)) A)
  have hν : ν.real A ≤ κ⁻¹ * volume.real (Q : Set (PDE.Vec d)) := by
    calc
      ν.real A ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ A)
      _ = _ := by simp [ν, ENNReal.toReal_ofReal (inv_nonneg.mpr hκ.le)]
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
  simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  exact Real.sqrt_le_sqrt (hm.trans hν)

#print axioms sourceBall_indicator_norm_structural_bound

end EinsteinFull.Blueprint.SbxS2Boundary

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_sourceBall_native_heat_pairing_two_times
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_sourceBall_native_heat_pairing

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_sourceBall_first_eigenfunction_uniform_interior_lower
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_sourceBall_eigenfunction_interior_lower
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_interior_seed_mass
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_cover_member_with_integral_mass
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_cover_member_with_mass

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.reflected_sq_dist_sum
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.reflection_mem_ball
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.ball_exterior_half_volume_of_not_mem
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.ball_exterior_half_volume
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h1ToW11
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.integral_le_two_integral_abs_sub_average
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.half_zero_ball_l1_poincare
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.elliptic_cutoff_cross_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.level_test_energy_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_boundary_level_caccioppoli
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h1FromHomogenization
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.zero_extended_level_l1_poincare

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.levelStrip
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.levelStrip_grad
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.integral_sq_le_mass_mul_integral_sq
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.half_zero_ball_level_strip_sq

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.half_zero_ball_finite_level_decay
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.zero_extended_finite_level_decay

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_zero_extended_level_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_zero_extended_level_energy_bounded

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_zero_extended_dyadic_level_decay

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.positivePart_levelTest
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.positivePart_level_flux
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.shifted_boundary_level_identity
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.positivePart_eLpNorm_two_le
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.positivePart_eLpNorm_two_le_of_level_decay
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.shifted_boundary_deGiorgi_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_zero_extended_dyadic_l2_smallness
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.forced_zero_extended_dyadic_contraction
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_nat_fourth_root_le
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_dyadic_contraction_depth
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_forced_zero_extended_dyadic_contraction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weak_solution_neg
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10_neg_toH1Function
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_forced_zero_extended_dyadic_abs_contraction
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.centered_axisCube_subset_euclideanBall
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.center_mem_halfCube
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.boundaryBallCutoff
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_boundary_cube_side
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_finite_boundary_cube_cover
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.euclideanBall_subset_centered_halfCube
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.restricted_ball_volume_toReal_le
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.scaled_boundary_decay_algebra
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.scaled_fourth_root_factor
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_abs_contraction
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_cover_abs_contraction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_ball_forced_contraction
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.geometric_boundary_forcing_floor
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_geometric_decay

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_geometric_decay_exponent
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_geometric_scale_power_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_power_decay

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.abs_le_on_open_of_ae_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.boundary_power_bound_continuous_representative
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.boundary_power_modulus_tendsto_zero
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_small_boundary_power_modulus
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.tendsto_zero_indicator_of_boundary_power_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.continuousAt_indicator_of_boundary_power_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_uniform_boundary_representative_decay

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.continuous_indicator_of_continuousAt_frontier
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.continuous_zero_extension_of_locally_bounded_weak_solution
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.continuous_zero_extension_of_bounded_weak_solution

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.l2_forced_boundary_level_caccioppoli

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.abs_mul_positivePart
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_boundary_level_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.zero_extended_level_energy_le_cutoff

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.positivePart_sq_add_level_mul_le
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.integral_sq_le_of_weighted_normalization
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_level_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_two_level_energy
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_ball_two_level_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_weak_solution_neg
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.normalized_eigenfunction_zero_extended_ball_level_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularized_log_test_pointwise_bound
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_abs_h10
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_abs_h10_preserving_energy
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularized_quotient_bounds
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularized_quotient_tendsto
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularized_quotient_integral_tendsto
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_regularized_log_forcing_tendsto
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_regularized_log_energy
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_regularized_log_energy_euclidean
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularized_log_energy_with_forcing
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10ToHomogenization
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularizedH1
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularizedH1_toFun
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularizedH1_grad
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.regularizedH1_lower
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_regularized_log_h1
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_regularized_reciprocal_test

#lint

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h1ToSubcritical
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.tendsto_eLpNorm_subcritical
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10SubcriticalApproximation
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10_planar_sobolev
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10_toFun
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10_energy
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10_sobolev

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.zero_extended_positivePart_sq_integral

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10_energy_le

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.zero_extended_positivePart_sq_integral_le

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_cutoff_sobolev

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.cutoffPositivePartH10_two_level_holder

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10_memLp_critical

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_cutoff_two_level_tail

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_ball_two_level_tail

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10_memLp_planar

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.h10_planar_sobolev_energy

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_cutoff_planar_sobolev

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_cutoff_planar_two_level_tail

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.eigenfunction_zero_extended_ball_planar_two_level_tail


#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_integrable

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing_integrable

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_add_smul_left

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_add_smul_right

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing_add_smul_left

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing_add_smul_right

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_symm

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing_symm

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.quadratic_direction_linear_eq_zero

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.rayleigh_minimizer_weak_solution


#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_smul_self

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.weightedL2Pairing_smul_self

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_self_nonneg

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.rayleigh_lower_bound_of_normalized_minimum

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.normalized_rayleigh_minimizer_weak_solution

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_nonnegative_normalized_rayleigh_minimizer

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletEnergyPairing_pos_of_normalized

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_minimum_of_tendsto_atTop

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_positive_nonnegative_normalized_rayleigh_eigenfunction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_normalized_rayleigh_minimizer_of_compact_inverse
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_dirichletHilbert_rayleigh_minimizer

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.sourceBallL2Restriction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletHilbertBallData

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletHilbertBallData_mem_killedSobolevGraph

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_nativeH10_of_dirichletHilbert

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.sourceBallL2Restriction_coe
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_dirichletHilbert_of_nativeH10

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletHilbert_norm_sq_eq_weightedL2Pairing

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.dirichletHilbert_energy_eq_dirichletEnergyPairing

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_nativeH10_sourceBall_rayleigh_minimizer

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.source_uniformlyElliptic_isEllipticFieldOn

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_sourceBall_first_nonnegative_weak_eigenfunction
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.normalized_geometric_tail_step
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.ae_le_of_ball_tail_tendsto_zero

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.geometric_ball_tail_coefficient
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_ae_bound_of_geometric_ball_tails

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_ae_upper_of_three_radius_eigenfunction_tails
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_eigenfunction_ball_upper_amplitude_of_three_le

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_eigenfunction_ball_upper_amplitude_planar
#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_eigenfunction_ball_abs_amplitude

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_sourceBall_nativeH10_positive_mass

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_sourceBall_uniform_rayleigh_upper

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_eigenfunction_ball_abs_amplitude_of_eigenvalue_le

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_normalized_eigenfunction_ball_abs_amplitude

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_sourceBall_first_nonnegative_bounded_weak_eigenfunction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_normalized_eigenfunction_boundary_cover_contraction

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.normalized_weighted_mass_on_interior

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_small_euclideanBall_boundary_layer

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_interior_ball_of_normalized_weighted_mass

#print axioms EinsteinFull.Blueprint.SbxS2Boundary.exists_finite_interior_ball_cover
