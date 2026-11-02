import EinsteinRelation.Correctors.GTTwoBallCoefficientSupport
import EinsteinRelation.Correctors.RegularPotentialOrigin
import EinsteinRelation.Calculus.WeakRepresentativeOperations

/-!
# Regularizing the canonical spatial weak potential

Source: `paper/main.tex:693-698,727-729`. GT Corollary 8.36 supplies
regular representatives on the unit ball from a scalar Sobolev solution
on the doubled ball. Null-set replacement preserves the weak equation,
and stationarity supplies the value of the gradient at the origin.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

private theorem measurableSet_ball {d : ℕ} (R : ℝ) :
    MeasurableSet (ball (0 : Vec d) R) := by
  apply IsOpen.measurableSet
  unfold ball euclideanNorm euclideanSq dot
  exact isOpen_lt (by fun_prop) continuous_const

/-- GT regularity discharges the regular-representative part of the
canonical harmonic realization. The remaining hypothesis is existence
of the actual scalar weak potential, without a regularity assumption. -/
theorem canonicalHarmonicRealization_of_gt_and_weak_potentials
    (h836 : InteriorRegularRepresentative)
    (hpot : ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ)
      (Q : EnvironmentLaw d L r₀) (i : Fin d), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
        WeakSolution (ball 0 2) ω.1 u g ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 2),
          g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp)) :
    CanonicalHarmonicRealization := by
  apply canonicalHarmonicRealization_of_spatial_regular_potentials
  intro d hd L r₀ Q i
  have hL : 0 ≤ L := zero_le_one.trans Q.ellipticity_parameter
  have hB : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    apply mul_pos (Real.exp_pos _)
    positivity
  have hK : 0 < sourceReducedBound L +
      2 * (Real.exp (2 * L) * (L + 2 * L ^ 2)) := by positivity
  filter_upwards [hpot d hd L r₀ Q i, reduced_gt_twoBall_coefficient_hypotheses Q]
    with ω hω hcoeff
  obtain ⟨u, g, hweak, hgradient⟩ := hω
  obtain ⟨v, h, hreg, hv, hh⟩ := h836 d hd
    (sourceReducedBound L)⁻¹ _ (1 / 2) 1 (inv_pos.mpr hB) hK
    (by norm_num) (by norm_num) zero_lt_one ω.1
    (by simpa only [mul_one] using fun x hx => (hcoeff.1.2 x hx).1)
    (by simpa only [mul_one] using hcoeff.2)
    u g (by simpa only [mul_one] using hweak)
  have h12 : ball (0 : Vec d) 1 ⊆ ball 0 2 := fun x hx =>
    (show euclideanNorm (x - 0) < 1 from hx).trans (by norm_num)
  have hw1 := weakSolution_congr_ae hv hh
    (weakSolution_restrict_subset (measurableSet_ball 2) h12 hweak)
  refine ⟨v, h, ?_, hreg, ?_⟩
  · intro R _ hR
    exact weakSolution_restrict_subset (measurableSet_ball 1)
      (fun _ hx => lt_of_lt_of_le hx hR) hw1
  · exact hh.trans (hgradient.filter_mono
      (ae_mono (Measure.restrict_mono_set volume h12)))

end EinsteinRelation.Correctors
