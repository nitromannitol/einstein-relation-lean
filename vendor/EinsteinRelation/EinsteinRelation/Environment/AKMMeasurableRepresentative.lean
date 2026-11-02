import EinsteinRelation.Environment.AKMTestIntegralSupport
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# A jointly measurable representative of raw AKM coefficients

Source: `paper/main.tex:693-698,727-729`; AKM (0.7)--(0.8), p. xvii.
The observation sigma algebra does not make raw point evaluation measurable.
Smooth test observations and Lebesgue differentiation provide a representative
which agrees spatially almost everywhere for every coefficient, for every law.
-/

open MeasureTheory Filter Topology
open scoped Convolution
noncomputable section
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-- A sequence of normalized smooth averaging kernels with bounded radius ratio. -/
def representativeBump (d n : ℕ) : ContDiffBump (0 : Vec d) where
  rIn := 1 / ((n : ℝ) + 1) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

/-- A translated averaging kernel, an admissible source coefficient observation. -/
def representativeTest {d : ℕ} (x : Vec d) (n : ℕ) : SmoothCompactTest d :=
  ⟨fun y => (representativeBump d n).normed volume (x - y),
    (representativeBump d n).contDiff_normed.comp (contDiff_const.sub contDiff_id),
    (representativeBump d n).hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)⟩

/-- Smoothed observations are continuous in their spatial center. -/
theorem continuous_representative_observation {d : ℕ} {K : ℝ}
    (n : ℕ) (i j : Fin d) (a : Coefficient d K) :
    Continuous (fun x => testIntegral a (representativeTest x n) i j) := by
  have h := ((representativeBump d n).hasCompactSupport_normed (μ := volume)).continuous_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) ((representativeBump d n).continuous_normed (μ := volume))
    (a.locally_integrable i j)
  change Continuous (fun x => ∫ y, (representativeBump d n).normed volume (x - y) *
    a.field y i j ∂volume)
  convert h using 1
  funext x
  exact (convolution_lsmul_swap (μ := (volume : Measure (Vec d)))
    (f := (representativeBump d n).normed volume)
    (g := fun y => a.field y i j) (x := x)).symm

attribute [local irreducible] representativeTest testIntegral

/-- Joint measurability of one smoothed matrix entry on the source sigma algebra. -/
theorem measurable_representative_observation {d : ℕ} {K : ℝ}
    (n : ℕ) (i j : Fin d) :
    Measurable (fun p : Coefficient d K × Vec d =>
      testIntegral p.1 (representativeTest p.2 n) i j) := by
  have hm : Measurable (fun p : Vec d × Coefficient d K =>
      testIntegral p.2 (representativeTest p.1 n) i j) :=
    measurable_uncurry_of_continuous_of_measurable
      (u := fun (x : Vec d) (a : Coefficient d K) =>
        testIntegral a (representativeTest x n) i j)
      (continuous_representative_observation n i j)
      (fun x => measurable_testIntegral (representativeTest x n) i j)
  have hs : Measurable (Prod.swap : Coefficient d K × Vec d → Vec d × Coefficient d K) :=
    measurable_swap
  exact hm.comp hs

/-- For each coefficient separately the smooth observations recover the raw
field almost everywhere, without continuity of that field. -/
theorem ae_tendsto_representative_observation {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (i j : Fin d) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), Tendsto
      (fun n => testIntegral a (representativeTest x n) i j) atTop (𝓝 (a x i j)) := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      (representativeBump d n).rOut ≤ (2 : ℝ) * (representativeBump d n).rIn := by
    filter_upwards with n
    dsimp only [representativeBump]
    linarith
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (μ := (volume : Measure (Vec d))) (φ := representativeBump d)
    tendsto_one_div_add_atTop_nhds_zero_nat hratio (a.locally_integrable i j)
  simpa only [convolution_eq_swap, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    testIntegral, representativeTest] using h

/-- The entrywise limit superior fixes a measurable representative of every
raw coefficient's spatial almost-everywhere class. -/
def coefficientRepresentative {d : ℕ} {K : ℝ} (a : Coefficient d K) (x : Vec d) : Mat d :=
  fun i j => limsup (fun n => testIntegral a (representativeTest x n) i j) atTop

/-- Joint measurability holds for every law on the original source carrier. -/
theorem measurable_coefficientRepresentative {d : ℕ} {K : ℝ} :
    Measurable (fun p : Coefficient d K × Vec d => coefficientRepresentative p.1 p.2) := by
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_pi_iff.mpr
  intro j
  exact Measurable.limsup (fun n => measurable_representative_observation n i j)

/-- The representative has the same spatial field class for every coefficient,
not just almost surely under a particular stationary law. -/
theorem coefficientRepresentative_ae_eq {d : ℕ} {K : ℝ} (a : Coefficient d K) :
    coefficientRepresentative a =ᵐ[volume] a.field := by
  have h := ae_all_iff.mpr (fun i => ae_all_iff.mpr
    (fun j => ae_tendsto_representative_observation a i j))
  filter_upwards [h] with x hx
  funext i j
  exact (hx i j).limsup_eq

end EinsteinRelation.Environment.AKMTestIntegralSupport
