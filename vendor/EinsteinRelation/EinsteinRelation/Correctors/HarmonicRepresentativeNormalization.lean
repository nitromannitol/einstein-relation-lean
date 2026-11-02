import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import EinsteinRelation.Correctors.BallPoincareTransfer
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Centering the samplewise harmonic potential

Source: `paper/main.tex:727-729`. Subtracting the ball mean preserves the
weak harmonic equation, its actual gradient and its Hölder regularity.
The coefficient bounds are supplied by the actual reduced image. Existence
of the regular potential and its identification with the stationary gradient
remain separate internal obligations.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

private theorem integral_coordinateDerivative_eq_zero {d : ℕ} {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (i : Fin d) :
    (∫ x, coordinateDerivative i φ x) = 0 := by
  obtain ⟨K, hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp) (𝕂 := ℝ)
  have h := (LipschitzWith.const (α := Vec d) (1 : ℝ)).integral_lineDeriv_mul_eq
    (μ := volume) hK hφc (unitVector i)
  have hconst : ∀ x, lineDeriv ℝ (fun _ : Vec d => (1 : ℝ)) x (unitVector i) = 0 :=
    fun _ => by simp [lineDeriv]
  have hneg : ∀ x, lineDeriv ℝ φ x (-unitVector i) = -coordinateDerivative i φ x := by
    intro x
    rw [((hφ.differentiable (by simp)) x).lineDeriv_eq_fderiv, map_neg]
    rfl
  simp only [hconst, zero_mul, integral_zero, hneg, mul_one, integral_neg] at h
  exact neg_eq_zero.mp h.symm

private theorem coordinateDerivative_eq_zero_outside {d : ℕ} {U : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest U φ) (i : Fin d) (x : Vec d) (hx : x ∉ U) :
    coordinateDerivative i φ x = 0 := by
  have hnot : x ∉ tsupport φ := fun h => hx (hφ.2.2 h)
  have hz : fderiv ℝ φ x = 0 := by
    by_contra hn
    exact hnot (support_fderiv_subset ℝ (by simpa only [Function.mem_support] using hn))
  simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply]

/-- Subtracting a scalar constant preserves the genuine Sobolev weak equation.
No value of an arbitrary Sobolev representative is evaluated at a fixed point. -/
theorem weakSolution_sub_const {d : ℕ} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)] {a : Vec d → Mat d}
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (h : WeakSolution U a u g) (c : ℝ) :
    WeakSolution U a (fun x => u x - c) g := by
  refine ⟨h.1.sub (memLp_const c), h.2.1, ?_, h.2.2.2⟩
  intro i
  refine ⟨(h.2.2.1 i).1.sub ((locallyIntegrable_const c).locallyIntegrableOn U),
    (h.2.2.1 i).2.1, ?_⟩
  intro φ hφ
  have hd : Continuous (coordinateDerivative i φ) := by
    exact (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (coordinateDerivative i φ) :=
    hφ.2.1.fderiv_apply ℝ (unitVector i)
  obtain ⟨B, hB⟩ := hdc.exists_bound_of_continuous hd
  have hint : Integrable (fun x => u x * coordinateDerivative i φ x)
      (volume.restrict U) :=
    (h.1.integrable (by norm_num)).mul_bdd hd.aestronglyMeasurable
      (ae_of_all _ hB)
  have hdi : Integrable (coordinateDerivative i φ) (volume.restrict U) :=
    (hd.integrable_of_hasCompactSupport hdc).restrict
  have hzero : (∫ x in U, coordinateDerivative i φ x) = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (coordinateDerivative_eq_zero_outside hφ i)]
    exact integral_coordinateDerivative_eq_zero hφ.1 hφ.2.1 i
  simp_rw [sub_mul]
  rw [integral_sub hint (hdi.const_mul c), integral_const_mul, hzero, mul_zero, sub_zero]
  exact (h.2.2.1 i).2.2 φ hφ

private theorem regular_sub_const {d : ℕ} {U : Set (Vec d)} {α : ℝ}
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : C1Alpha U α u g) (c : ℝ) :
    C1Alpha U α (fun x => u x - c) g := by
  refine ⟨fun x hx => ?_, h.2⟩
  simpa only [sub_zero] using (h.1 x hx).sub_const c

/-- Centering by the actual unit-ball mean gives zero integral. -/
theorem integral_unitBall_sub_average_eq_zero {d : ℕ} {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (ball 0 1))) :
    (∫ x in ball 0 1, (u x - ⨍ z in ball 0 1, u z ∂volume) ∂volume) = 0 := by
  have hV := unitBall_volume_pos_finite d
  have hfin : volume (ball (0 : Vec d) 1) ≠ ⊤ := by
    exact (ENNReal.toReal_pos_iff.mp hV).2.ne
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr hfin
  rw [integral_sub (hu.integrable (by norm_num)) (integrable_const _)]
  simp only [integral_const, Measure.restrict_apply_univ, smul_eq_mul, average_eq,
    Measure.real]
  have hVne : (volume (ball (0 : Vec d) 1)).toReal ≠ 0 := hV.ne'
  rw [← mul_assoc, mul_inv_cancel₀ hVne, one_mul, sub_self]

/-- The centering and uniform coefficient part of the canonical harmonic
realization is internal. The remaining premise asks for a regular weak
potential and the two actual gradient identities; it is not an external input. -/
theorem canonicalHarmonicRealization_of_regular_potentials
    (hpot : ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ)
      (Q : EnvironmentLaw d L r₀) (i : Fin d), ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∃ (u : Vec d → ℝ) (g : Vec d → Vec d),
        (∀ R : ℝ, 0 < R → R ≤ 1 → WeakSolution (ball 0 R) ω.1 u g) ∧
        C1Alpha (ball 0 1) (1 / 2) u g ∧
        (∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1),
          g x = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ω)).ofLp) ∧
        g 0 = (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) ω).ofLp) :
    CanonicalHarmonicRealization := by
  intro d hd L r₀
  let B : ℝ := sourceReducedBound L
  let A : ℝ := Real.exp (2 * L) * (L + 2 * L ^ 2)
  have hB : 0 < B := by
    apply mul_pos (Real.exp_pos _)
    nlinarith only [sq_nonneg (6 * L + 1)]
  have hK : 0 < B + 2 * A := by
    have hp : 0 < 7 * L ^ 2 + 3 * L + 1 := by
      nlinarith only [sq_nonneg (14 * L + 3)]
    have heq : B + 2 * A = Real.exp (2 * L) * (7 * L ^ 2 + 3 * L + 1) := by
      dsimp [B, A, sourceReducedBound]
      ring
    rw [heq]
    exact mul_pos (Real.exp_pos _) hp
  refine ⟨B⁻¹, ((d : ℝ) + 1) * B, B + 2 * A, 1 / 2, inv_pos.mpr hB,
    mul_pos (by positivity) hB, hK, by norm_num, by norm_num, ?_⟩
  intro Q i
  filter_upwards [hpot d hd L r₀ Q i, reduced_gt_coefficient_hypotheses Q] with ω hω hcoeff
  obtain ⟨u, g, hweak, hregular, hspatial, horigin⟩ := hω
  let c : ℝ := ⨍ z in ball (0 : Vec d) 1, u z ∂volume
  refine ⟨{
    potential := fun x => u x - c
    grad := g
    weak_solution := ?_
    regular := regular_sub_const hregular c
    centered := integral_unitBall_sub_average_eq_zero (hweak 1 zero_lt_one le_rfl).1
    elliptic := hcoeff.1
    holder := hcoeff.2
    gradient_spatial := hspatial
    gradient_origin := horigin
  }⟩
  intro R hR hR1
  have hfin : volume (ball (0 : Vec d) 1) ≠ ⊤ :=
    (ENNReal.toReal_pos_iff.mp (unitBall_volume_pos_finite d)).2.ne
  have hsub : ball (0 : Vec d) R ⊆ ball 0 1 :=
    fun _ hx => lt_of_lt_of_le hx hR1
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top hfin (measure_mono hsub))
  exact weakSolution_sub_const (hweak R hR hR1) c

end EinsteinRelation.Correctors

