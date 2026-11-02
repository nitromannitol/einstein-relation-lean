import EinsteinRelation.External.GilbargTrudinger
import EinsteinRelation.Mobility.CorrectorGradientMoments
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Interior regularity and the stationary canonical gradient

Source: `paper/main.tex:727-729`. The GT estimates are kept separate from
the internal existence of a regular harmonic representative and from the
ordinary ball Poincaré inequality. Both internal facts remain explicit Props.
In particular, GT 8.32 is not used to manufacture its own regularity hypothesis.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

private theorem isOpen_euclideanBall {d : ℕ} (x : Vec d) (R : ℝ) : IsOpen (ball x R) := by
  unfold ball euclideanNorm euclideanSq dot
  exact isOpen_lt (by fun_prop) continuous_const

private theorem euclideanNorm_ofLp {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanNorm x.ofLp = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold euclideanNorm euclideanSq dot
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.norm_eq_abs, pow_two]
  exact (abs_mul_abs_self (x i)).symm

private theorem euclideanSq_ofLp {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) :
    euclideanSq x.ofLp = ‖x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

/-- An almost-everywhere bound on an open set upgrades to every point for
a continuous representative. This does not change an arbitrary L² representative. -/
theorem abs_le_on_open_of_ae {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ} {M : ℝ}
    (hU : IsOpen U) (hu : ContinuousOn u U)
    (h : ∀ᵐ x ∂volume.restrict U, |u x| ≤ M) : ∀ x ∈ U, |u x| ≤ M := by
  have heq : (fun x => max |u x| M) =ᵐ[volume.restrict U] (fun _ => M) :=
    h.mono fun _ hx => max_eq_right hx
  have hpoint := Measure.eqOn_open_of_ae_eq heq hU (hu.abs.sup continuousOn_const) continuousOn_const
  intro x hx
  exact (le_max_left _ _).trans_eq (hpoint hx)

/-- The coordinate-to-Euclidean measure transport in the unit-energy
definition, once the spatial gradient identity is supplied. -/
theorem canonicalUnitEnergy_eq_of_gradient_ae {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (ω : FieldPair d) (g : Vec d → Vec d)
    (hg : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
      g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp) :
    Real.sqrt (⨍ x in ball 0 1, euclideanSq (g x) ∂volume) =
      canonicalCorrectorUnitEnergy Q i ω := by
  let f : Vec d → ℝ := fun x => euclideanSq (correctorUnitVector i +
    (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp
  have hpre : (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹' ball 0 1 =
      Metric.ball 0 1 := by
    ext x
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, sub_zero, Metric.mem_ball,
      dist_zero_right, euclideanNorm_ofLp]
  have hmp := (PiLp.volume_preserving_ofLp (Fin d)).restrict_preimage
    (isOpen_euclideanBall (0 : Vec d) 1).measurableSet
  have hchange := hmp.integral_comp
    (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).measurableEmbedding f
  rw [hpre] at hchange
  have hvolume : volume (ball (0 : Vec d) 1) =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
    rw [← hpre]
    exact ((PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
      (isOpen_euclideanBall (0 : Vec d) 1).measurableSet.nullMeasurableSet).symm
  unfold canonicalCorrectorUnitEnergy
  congr 1
  have hgeq : (fun x => euclideanSq (g x)) =ᵐ[volume.restrict (ball 0 1)] f :=
    hg.mono fun _ hx => congrArg euclideanSq hx
  simp only [average_eq, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  rw [integral_congr_ae hgeq, hvolume]
  change _ * (∫ x in ball 0 1, f x ∂volume) = _
  rw [← hchange]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ fun x => euclideanSq_ofLp _

/-- The ordinary internal Poincaré obligation on a Euclidean unit ball.
The left norm is unnormalized (as in GT); the right norm is normalized
(as in `canonicalCorrectorUnitEnergy`). No environment or corrector occurs
in this statement. It is not registered as a permitted external input. -/
def UnitBallPoincare : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∃ C : ℝ, 0 < C ∧
    ∀ (u : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp u 2 (volume.restrict (ball 0 1)) →
      MemLp g 2 (volume.restrict (ball 0 1)) → HasWeakGradient (ball 0 1) u g →
      (∫ x in ball 0 1, u x ∂volume) = 0 →
      Real.sqrt (∫ x in ball 0 1, |u x| ^ 2 ∂volume) ≤
        C * Real.sqrt (⨍ x in ball 0 1, euclideanSq (g x) ∂volume)

/-- Internal spatial realization of the affine-corrector potential, centered
by its unit-ball mean. The weak equation is required on each smaller ball;
the coefficients are the actual reduced sample `ω.1`. The common exponent
and coefficient bounds are uniform in the environment law.

The a.e. spatial identity alone does not determine the value of an L²
representative at the origin; `gradient_origin` supplies the required
a.e. environment identity with the continuous spatial representative.
Constructing this representative and proving these identities are internal
obligations, not consequences postulated of the GT estimates. -/
structure HarmonicRepresentative {d : ℕ} {L r₀ lam Λ K α : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (ω : FieldPair d) where
  potential : Vec d → ℝ
  grad : Vec d → Vec d
  weak_solution : ∀ R : ℝ, 0 < R → R ≤ 1 → WeakSolution (ball 0 R) ω.1 potential grad
  regular : C1Alpha (ball 0 1) α potential grad
  centered : (∫ x in ball 0 1, potential x ∂volume) = 0
  elliptic : EllipticBound (ball 0 1) ω.1 lam Λ
  holder : ∀ i j, HolderBound (ball 0 1) α (fun x => ω.1 x i j) K
  gradient_spatial : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
    grad x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (translate x ω)).ofLp
  gradient_origin : grad 0 = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp

/-- Uniform existence of the preceding regular harmonic realization.
This is an unresolved internal Prop, not a literature contract. -/
def CanonicalHarmonicRealization : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ),
    ∃ lam Λ K α : ℝ, 0 < lam ∧ 0 < Λ ∧ 0 < K ∧ 0 < α ∧ α < 1 ∧
      ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        Nonempty (HarmonicRepresentative (lam := lam) (Λ := Λ) (K := K) (α := α) Q i ω)

private theorem HolderBound.mono {d : ℕ} {U V : Set (Vec d)} {α K : ℝ} {f : Vec d → ℝ}
    (h : HolderBound U α f K) (hVU : V ⊆ U) : HolderBound V α f K := by
  obtain ⟨S, H, hS, hH, hK, hsup, hhold⟩ := h
  exact ⟨S, H, hS, hH, hK, fun x hx => hsup x (hVU hx),
    fun x hx y hy => hhold x (hVU hx) y (hVU hy)⟩

private theorem C1Alpha.mono {d : ℕ} {U V : Set (Vec d)} {α : ℝ}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : C1Alpha U α u g) (hVU : V ⊆ U) : C1Alpha V α u g := by
  obtain ⟨hderiv, K, hK⟩ := h
  exact ⟨fun x hx => hderiv x (hVU hx), K, fun i => HolderBound.mono (hK i) hVU⟩

/-- GT 8.17 and 8.32 imply the former `hregularity` estimate once the
regular harmonic realization and the general ball Poincaré inequality are
proved. The application, centering, spatial-volume transport and passage
from an a.e. scalar bound to the continuous representative are proved here. -/
theorem canonical_gradient_le_unitEnergy_of_gt
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (hreal : CanonicalHarmonicRealization) (hPoincare : UnitBallPoincare) :
    ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ), ∃ C : ℝ, 0 ≤ C ∧
      ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        ‖correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω‖ ≤
          C * canonicalCorrectorUnitEnergy Q i ω := by
  intro d hd L r₀
  obtain ⟨lam, Λ, K, α, hlam, hΛ, hK, hα, hα1, hrep⟩ := hreal d hd L r₀
  obtain ⟨CP, hCP, hP⟩ := hPoincare d hd
  obtain ⟨CB, hCB, hB⟩ := h817 d hd lam Λ 2 hlam hΛ (by norm_num)
  obtain ⟨CS, hCS, hS⟩ := h832 d hd lam K α (1 / 4) hlam hK hα hα1 (by norm_num)
  let F := CB * (1 / 2 : ℝ) ^ (-(d : ℝ) / 2)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨CS * F * CP, by positivity, fun Q i => ?_⟩
  filter_upwards [hrep Q i] with ω hω
  obtain ⟨R⟩ := hω
  have hhalf : ball (0 : Vec d) (1 / 2 : ℝ) ⊆ ball 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < 1
    exact lt_trans (show euclideanNorm (x - 0) < (1 / 2 : ℝ) from hx) (by norm_num)
  have hweak := R.weak_solution 1 zero_lt_one le_rfl
  have hmoser := hB (ball 0 1) (isOpen_euclideanBall 0 1) ω.1 R.elliptic
    R.potential R.grad hweak 0 (1 / 2) (by norm_num)
    (by norm_num) (by simpa using hweak.1)
  have hbound_ae : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) (1 / 2 : ℝ)),
      |R.potential x| ≤ F * Real.sqrt (∫ z in ball 0 1, |R.potential z| ^ 2 ∂volume) := by
    simpa only [show 2 * (1 / 2 : ℝ) = 1 by norm_num, Real.rpow_two,
      Real.sqrt_eq_rpow, F] using hmoser
  have hcont : ContinuousOn R.potential (ball (0 : Vec d) (1 / 2 : ℝ)) :=
    fun x hx => (R.regular.1 x (hhalf hx)).continuousAt.continuousWithinAt
  have hbound := abs_le_on_open_of_ae (isOpen_euclideanBall 0 (1 / 2)) hcont hbound_ae
  have hgrad := hS ω.1
    (fun x hx => (R.elliptic.2 x (hhalf (by norm_num at hx ⊢; exact hx))).1)
    (fun i j => by simpa only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using HolderBound.mono (R.holder i j) hhalf)
    R.potential R.grad (by
      simpa only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using
        R.weak_solution (1 / 2) (by norm_num) (by norm_num))
    (by simpa only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using
      C1Alpha.mono R.regular hhalf)
    (F * Real.sqrt (∫ z in ball 0 1, |R.potential z| ^ 2 ∂volume)) (by positivity)
    (by simpa only [show 2 * (1 / 4 : ℝ) = 1 / 2 by norm_num] using hbound)
    0 (by simp [ball, euclideanNorm, euclideanSq, dot])
  have hPbound := hP R.potential R.grad hweak.1 hweak.2.1 hweak.2.2.1 R.centered
  rw [canonicalUnitEnergy_eq_of_gradient_ae Q i ω R.grad R.gradient_spatial] at hPbound
  rw [R.gradient_origin, euclideanNorm_ofLp] at hgrad
  nlinarith [mul_le_mul_of_nonneg_left hPbound (mul_nonneg hCS.le hF)]

end EinsteinRelation.Correctors

