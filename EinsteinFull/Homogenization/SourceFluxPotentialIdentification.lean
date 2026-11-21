import EinsteinFull.Homogenization.HeatPotentialEstimate
import EinsteinFull.Homogenization.SourceFluxCorrectorExistence
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Calculus.ZeroWeakGradientConstant
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Flux potentials of source correctors are the heat-selected potential up to constants

The heat selection (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, determines the flux gradient almost everywhere, as
the square-mean limit of the same truncations. Hence the potential of every flux corrector of a
source corrector differs from the heat-selected potential of the measurable representative of the
centered flux by a constant in each entry, and the two have the same oscillation on every ball.
The normalized oscillation is the oscillation divided by the square root of the volume.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

variable {d : ℕ}

theorem iUnion_ball_natCast_add_one :
    ⋃ R : ℕ, ball (0 : Vec d) ((R : ℝ) + 1) = univ := by
  refine eq_univ_of_forall fun x => mem_iUnion.mpr ?_
  obtain ⟨R, hR⟩ := exists_nat_gt (euclideanNorm x)
  refine ⟨R, ?_⟩
  show euclideanNorm (x - 0) < (R : ℝ) + 1
  rw [sub_zero]
  linarith

/-- The heat selection determines the flux gradient almost everywhere. -/
theorem isHeatSelectedFluxGradient_ae_unique {g : Vec d → Vec d}
    {F G : Fin d → Fin d → Vec d → Vec d}
    (hF : IsHeatSelectedFluxGradient g F) (hG : IsHeatSelectedFluxGradient g G) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k l, F j k x l = G j k x l := by
  refine ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => ?_
  have hlocal (R : ℕ) : (fun x => F j k x l) =ᵐ[
      volume.restrict (ball 0 ((R : ℝ) + 1))] (fun x => G j k x l) := by
    have hFl := hF j k l R
    have hGl := hG j k l R
    exact tendstoInMeasure_ae_unique
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hFl.2.2.2)
      (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hGl.2.2.2)
  have h := (ae_restrict_iUnion_iff _ _).mpr hlocal
  simpa only [iUnion_ball_natCast_add_one, Measure.restrict_univ] using h

/-- **Every flux corrector is the heat-selected potential up to constants.** -/
theorem SourceFluxCorrector.ae_potential_eq_add_const (hd : 2 ≤ d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} {φ : SourceCorrector P e}
    (S : SourceFluxCorrector φ) :
    ∀ᵐ a ∂P, HeatFormulaHypotheses (representativeFlux φ a) → ∀ j k, ∃ c : ℝ,
      (fun x => S.potential a x j k) =ᵐ[volume]
        fun x => heatSelectedPotential (representativeFlux φ a) x j k + c := by
  filter_upwards [S.heat_selected, S.weak_gradient] with a hS hwS
  intro hg j k
  have hT := isHeatSelectedFluxGradient_congr_ae (representativeFlux_ae_eq φ a)
    hg.isHeatSelectedFluxGradient
  have hgrad := isHeatSelectedFluxGradient_ae_unique hS hT
  have hweakT : HasWeakGradient Set.univ
      (fun x => heatSelectedPotential (representativeFlux φ a) x j k) (S.grad a j k) := by
    apply hasWeakGradient_congr_ae isOpen_univ (hg.hasWeakGradient_heatSelectedPotential hd j k)
      (ae_eq_refl _)
    rw [Measure.restrict_univ]
    filter_upwards [hgrad] with x hx
    ext l
    exact (hx j k l).symm
  have hweak := hasWeakGradient_sub (hwS j k) hweakT
  have hloc : LocallyIntegrable (fun x => S.potential a x j k -
      heatSelectedPotential (representativeFlux φ a) x j k) volume :=
    locallyIntegrableOn_univ.mp (hweak ⟨0, by omega⟩).1
  obtain ⟨c, hc⟩ := EinsteinRelation.ae_eq_const_of_zero_weak_gradient hloc
    (fun l ψ hψ => by
      have h := (hweak l).2.2 ψ hψ
      simpa only [Measure.restrict_univ, Pi.sub_apply, sub_self, zero_mul,
        integral_zero, neg_zero] using h)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change S.potential a x j k - heatSelectedPotential (representativeFlux φ a) x j k = c at hx
  linarith

theorem oscBall_congr_ae {r : ℝ} {u w : Vec d → ℝ} (h : u =ᵐ[volume] w) :
    oscBall r u = oscBall r w := by
  unfold oscBall
  have havg : ⨍ y in ball 0 r, u y = ⨍ y in ball 0 r, w y := by
    rw [setAverage_eq, setAverage_eq, integral_congr_ae (ae_restrict_of_ae h)]
  rw [havg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae h] with x hx
  rw [hx]

theorem oscBall_eq_of_ae_eq_add_const {r : ℝ} (hr : 0 < r) {u v : Vec d → ℝ} {c : ℝ}
    (h : u =ᵐ[volume] fun x => v x + c) (hv : IntegrableOn v (ball 0 r) volume) :
    oscBall r u = oscBall r v := by
  have h' : u =ᵐ[volume] fun x => v x - (-c) := by
    filter_upwards [h] with x hx
    rw [hx, sub_neg_eq_add]
  rw [oscBall_congr_ae h', oscBall_sub_const hr hv]

theorem sqrt_setAverage_sq_eq_oscBall_div {r : ℝ} (u : Vec d → ℝ) :
    Real.sqrt (⨍ x in ball 0 r, |u x - ⨍ y in ball 0 r, u y| ^ 2) =
      oscBall r u / Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
  unfold oscBall
  rw [setAverage_eq volume (fun x => |u x - ⨍ y in ball 0 r, u y| ^ 2) (ball 0 r), smul_eq_mul,
    Real.sqrt_mul (inv_nonneg.mpr measureReal_nonneg), Real.sqrt_inv, div_eq_inv_mul]

/-- The normalized Frobenius oscillation is controlled by the normalized oscillations of the
entries. -/
theorem sqrt_setAverage_frobeniusNorm_sq_le {r B : ℝ} (hr : 0 < r) (hB : 0 ≤ B)
    {U : Vec d → Mat d}
    (hU : ∀ j k, MemLp (fun x => U x j k) 2 (volume.restrict (ball 0 r)))
    (hosc : ∀ j k, Real.sqrt (⨍ x in ball 0 r,
      |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2) ≤ B) :
    Real.sqrt (⨍ x in ball 0 r, frobeniusNorm (U x -
      Matrix.of fun i j => ⨍ y in ball 0 r, U y i j) ^ 2) ≤ d * B := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  have hint : ∀ j k, Integrable (fun x => |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2)
      (volume.restrict (ball 0 r)) := fun j k => by
    have h := ((hU j k).sub (memLp_const (⨍ y in ball 0 r, U y j k))).integrable_sq
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, sq_abs]
  have hpt : ∀ x, frobeniusNorm (U x - Matrix.of fun i j => ⨍ y in ball 0 r, U y i j) ^ 2 =
      ∑ j, ∑ k, |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2 := by
    intro x
    rw [frobeniusNorm, Real.sq_sqrt (frobeniusSq_nonneg _), frobeniusSq]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.sub_apply, Matrix.of_apply, sq_abs]
    ring
  have hsum : ⨍ x in ball 0 r, frobeniusNorm (U x -
      Matrix.of fun i j => ⨍ y in ball 0 r, U y i j) ^ 2 =
      ∑ j, ∑ k, ⨍ x in ball 0 r, |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2 := by
    simp_rw [hpt]
    rw [setAverage_eq volume (fun x => ∑ j, ∑ k, |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2)
        (ball 0 r),
      integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hint j k,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact (setAverage_eq volume (fun x => |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2)
      (ball 0 r)).symm
  have hentry : ∀ j k, ⨍ x in ball 0 r, |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2 ≤ B ^ 2 :=
    fun j k => (Real.sqrt_le_left hB).mp (hosc j k)
  have htot : ⨍ x in ball 0 r, frobeniusNorm (U x -
      Matrix.of fun i j => ⨍ y in ball 0 r, U y i j) ^ 2 ≤ (d * B) ^ 2 := by
    rw [hsum]
    calc ∑ j, ∑ k, ⨍ x in ball 0 r, |U x j k - ⨍ y in ball 0 r, U y j k| ^ 2
        ≤ ∑ _j : Fin d, ∑ _k : Fin d, B ^ 2 :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hentry j k
      _ = (d * B) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  calc Real.sqrt (⨍ x in ball 0 r, frobeniusNorm (U x -
        Matrix.of fun i j => ⨍ y in ball 0 r, U y i j) ^ 2)
      ≤ Real.sqrt ((d * B) ^ 2) := Real.sqrt_le_sqrt htot
    _ = d * B := Real.sqrt_sq (by positivity)

end EinsteinFull.Homogenization
