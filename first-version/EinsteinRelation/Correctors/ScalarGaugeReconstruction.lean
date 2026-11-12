import EinsteinRelation.Correctors.NormalizedScalarCorrectorUniqueness
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Scalar correctors from another potential of the same gradient

Source: `paper/main.tex:724-731`. An actual weak potential of the same
gradient differs by a constant. Its local Sobolev membership and centered
sublinearity follow from the original potential.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport
open NormalizedScalarCorrectorUniqueness

/-- Equal global weak gradients determine scalar potentials modulo constants. -/
theorem weakPotentials_differ_by_constant {d : ℕ} (hd : 0 < d)
    {u v : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : HasWeakGradient Set.univ u G) (hv : HasWeakGradient Set.univ v G) :
    ∃ c : ℝ, u =ᵐ[volume] (fun x => v x + c) := by
  have hl : LocallyIntegrable (fun x => u x - v x) volume :=
    (locallyIntegrableOn_univ.mp (hu ⟨0, hd⟩).1).sub
      (locallyIntegrableOn_univ.mp (hv ⟨0, hd⟩).1)
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hl
    (fun j η hη => integral_sub_mul_coordinateDerivative_eq_zero hu hv j hη)
  refine ⟨c, hc.mono ?_⟩
  intro x hx
  change u x - v x = c at hx
  linarith

/-- Spatial constants cancel from centered normalized L² oscillations. -/
theorem centered_square_average_eq_of_gauge {d : ℕ} {u v : Vec d → ℝ}
    (c : ℝ) (heq : u =ᵐ[volume] (fun x => v x + c))
    (R : ℝ) (hR : 0 < R) (hv : MemLp v 2 (volume.restrict (ball 0 R))) :
    (⨍ x in ball 0 R, (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume) =
      ⨍ x in ball 0 R, (v x - ⨍ y in ball 0 R, v y ∂volume)^2 ∂volume := by
  let μ := volume.restrict (ball (0 : Vec d) R)
  have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr hvol.2.ne
  letI : NeZero μ := ⟨by
    intro hz
    have hm : μ Set.univ = 0 := by rw [hz]; simp
    simp only [μ, Measure.restrict_apply_univ] at hm
    exact hvol.1.ne' hm⟩
  have havg : (⨍ y, u y ∂μ) = (⨍ y, v y ∂μ) + c := by
    rw [average_congr (ae_restrict_of_ae heq)]
    change (∫ y, v y + c ∂(μ Set.univ)⁻¹ • μ) = _
    rw [integral_add (hv.integrable (by norm_num)).to_average
      (integrable_const c).to_average]
    exact congrArg ((⨍ y, v y ∂μ) + ·) (average_const μ c)
  change (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) = _
  rw [havg]
  apply average_congr
  filter_upwards [ae_restrict_of_ae heq] with x hx
  rw [hx]
  congr 1
  ring

/-- A new actual potential of an existing gradient inherits the full scalar
corrector carrier; no sublinearity or uniqueness assumption is added. -/
noncomputable def correctorWithPotential {d : ℕ} (hd : 0 < d) {K : ℝ}
    {P : Measure (Coefficient d K)} {e : Vec d} (φ : Corrector P e)
    (u : Coefficient d K → Vec d → ℝ)
    (hw : ∀ᵐ a ∂P, HasWeakGradient Set.univ (u a) (φ.grad a)) :
    Corrector P e where
  potential := u
  grad := φ.grad
  measurable_grad := φ.measurable_grad
  weak_gradient := hw
  locally_square_integrable := by
    filter_upwards [hw, φ.weak_gradient, φ.locally_square_integrable] with a hu hv hloc
    obtain ⟨c, hc⟩ := weakPotentials_differ_by_constant hd hu hv
    intro R hR
    have hvol := ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict.mpr hvol.2.ne
    exact ⟨(memLp_congr_ae (ae_restrict_of_ae hc)).mpr ((hloc R hR).1.add (memLp_const c)),
      (hloc R hR).2⟩
  stationary := φ.stationary
  harmonic := φ.harmonic
  sublinear := by
    filter_upwards [hw, φ.weak_gradient, φ.locally_square_integrable, φ.sublinear]
      with a hu hv hloc hsub
    obtain ⟨c, hc⟩ := weakPotentials_differ_by_constant hd hu hv
    apply hsub.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [centered_square_average_eq_of_gauge c hc R hR (hloc R hR).1]
  cell_integrable := φ.cell_integrable

end EinsteinRelation.Correctors
