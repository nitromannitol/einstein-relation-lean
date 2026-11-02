import EinsteinFull.Calculus.S2ReducedErgodicitySupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Calculus.ComplexRadialTransposeSupport
import EinsteinFull.Calculus.ComplexTransposeContinuitySupport
import EinsteinFull.Calculus.ComplexTransposeSupport

/-!
# The non-path clauses of the unforced and real-force semigroup nodes

All clauses of `stationary-environment#unforced-process` and
`e:generators#real-semigroup` that do not involve quenched path laws, for the
actual constructed evolution `forcedComplexEvolution`: contraction and mean
preservation at zero force, symmetry, the fixed space, the zero-energy
characterization of constants, and the real-force transpose clauses.
-/

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

theorem complexForceShift_zero_force (d : ℕ) (Λ₀ : ℝ) : complexForceShift d Λ₀ 0 = 0 := by
  simp [complexForceShift]

/-- The zero-force evolution is a contraction. -/
theorem norm_forcedComplexEvolution_zero_apply_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖forcedComplexEvolution Q i 0 t f‖ ≤ ‖f‖ := by
  have h := norm_forcedComplexEvolution_le Q i 0 t
  rw [complexForceShift_zero_force, zero_mul, Real.exp_zero] at h
  calc ‖forcedComplexEvolution Q i 0 t f‖ ≤ ‖forcedComplexEvolution Q i 0 t‖ * ‖f‖ :=
        (forcedComplexEvolution Q i 0 t).le_opNorm f
    _ ≤ 1 * ‖f‖ := by gcongr
    _ = ‖f‖ := one_mul _

/-- At zero force the actual bilinear transpose of the evolution is the evolution itself. -/
theorem isComplexTransposeSemigroup_forcedComplexEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    IsComplexTransposeSemigroup Q (forcedComplexEvolution Q i 0)
      (forcedComplexEvolution Q i 0) := by
  have hP := isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0
  have hT := isComplexTransposeSemigroup_complexL2Transpose Q (forcedComplexEvolution Q i 0)
  have hTE : IsComplexEnvironmentSemigroup Q i 0
      (fun t => complexL2Transpose (reducedLaw Q) (forcedComplexEvolution Q i 0 t)) :=
    ⟨hT.zero hP, hT.add hP, hT.continuous_apply hP, fun f g =>
      (hT.tendsto_slope_iff hP f g).trans (isComplexTransposeGeneratorPair_zero_iff Q i f g)⟩
  have heq := hTE.unique hP
  rw [heq] at hT
  exact hT

/-- The zero-force evolution preserves the reduced-law mean. -/
theorem integral_forcedComplexEvolution_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, forcedComplexEvolution Q i 0 t f ω ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q :=
  (isComplexTransposeSemigroup_forcedComplexEvolution_zero Q i).integral_eq
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0) t f

/-- The fixed space of the zero-force evolution is exactly the constants. -/
theorem forcedComplexEvolution_zero_fixed_iff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (i : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∀ t : ℝ≥0, forcedComplexEvolution Q i 0 t f = f) ↔
      ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c := by
  letI := reducedLaw_probability Q
  have hP := isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0
  constructor
  · intro h
    have hg : IsComplexGeneratorPair Q i 0 f 0 := by
      refine (hP.2.2.2 f 0).mp ?_
      simp only [h, sub_self, smul_zero]
      exact tendsto_const_nhds
    obtain ⟨G, hG, hb⟩ := hg.unforced_coercive
    simp only [inner_zero_right, Complex.zero_re, neg_zero] at hb
    have hK : 0 < (Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 2 :=
      div_pos (inv_pos.mpr (mul_pos (Real.exp_pos _)
        (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter))) two_pos
    have hs : ∑ j, ‖G j‖ ^ 2 ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      exact absurd hb (not_le.mpr (mul_pos hK hpos))
    have hG0 := eq_zero_of_sum_norm_sq_le_zero G hs
    subst hG0
    exact exists_const_of_horizontalGradient_zero Q hd f hG
  · rintro ⟨c, hc⟩ t
    have hf : f = Lp.const 2 (reducedLaw Q) c :=
      Lp.ext (hc.trans (Lp.coeFn_const 2 (reducedLaw Q) c).symm)
    rw [hf]
    exact hP.map_const t c

/-- Zero horizontal Dirichlet energy forces an actual gradient class to be constant. -/
theorem exists_const_of_zero_energy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hd : 2 ≤ d) (f : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (h : (∫ ω, (∑ j : Fin d, ∑ k : Fin d,
      (ω.1 0 j k : ℂ) * G k ω * star (G j ω)).re ∂reducedLaw Q) = 0) :
    ∃ c : ℂ, f =ᵐ[reducedLaw Q] fun _ => c := by
  have hG0 := horizontalGradient_eq_zero_of_energy_eq_zero Q G h
  subst hG0
  exact exists_const_of_horizontalGradient_zero Q hd f hG

/-- The real-force clauses of `e:generators#real-semigroup` that do not involve path laws. -/
theorem realForce_semigroup_clauses {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) :
    let P := forcedComplexEvolution Q i (lam : ℂ)
    let Pdag := fun t => complexL2Transpose (reducedLaw Q) (P t)
    IsComplexEnvironmentSemigroup Q i (lam : ℂ) P ∧
    IsComplexTransposeSemigroup Q P Pdag ∧
    (∀ f : Lp ℂ 2 (reducedLaw Q), Continuous (fun t : ℝ≥0 => Pdag t f)) ∧
    (∀ f g : Lp ℂ 2 (reducedLaw Q),
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (Pdag t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexTransposeGeneratorPair Q i (lam : ℂ) f g) := by
  intro P Pdag
  have hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P :=
    isComplexEnvironmentSemigroup_forcedComplexEvolution Q i (lam : ℂ)
  have hT : IsComplexTransposeSemigroup Q P Pdag :=
    isComplexTransposeSemigroup_complexL2Transpose Q P
  exact ⟨hP, hT, fun f => continuous_complexL2Transpose_forcedComplexEvolution_apply Q i _ f,
    fun f g => hT.tendsto_slope_iff hP f g⟩

end EinsteinFull
