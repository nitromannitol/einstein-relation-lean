import EinsteinFull.Regeneration.SlabOpenComparison
import EinsteinFull.Calculus.C8GMPRealizationExists

/-!
# Ellipticity of the rescaled GMP coefficient

Affine rescaling preserves the source ellipticity bounds. On a bounded
domain, the physical unit-force weight preserves ellipticity as well.
-/

open MeasureTheory Set PDE EinsteinRelation

namespace EinsteinFull.Regeneration

/-- The source coefficient after translating and rescaling the spatial variable. -/
noncomputable def gmpRescaledCoefficient {d : ℕ}
    (ω : FieldPair d) (y : PDE.Vec d) (μ : ℝ) : PDE.CoeffField d :=
  fun x => ω.1 (y + μ⁻¹ • x)

/-- Affine rescaling preserves the continuity of the source coefficient. -/
theorem continuous_gmpRescaledCoefficient {d : ℕ}
    (ω : FieldPair d) (y : PDE.Vec d) (μ : ℝ) :
    Continuous (gmpRescaledCoefficient ω y μ) := by
  have hscale : Continuous (fun x : PDE.Vec d => μ⁻¹ • x) := by
    change Continuous ((fun _ : PDE.Vec d => μ⁻¹) • (fun x : PDE.Vec d => x))
    exact continuous_const.smul continuous_id
  exact ω.1.continuous.comp (continuous_const.add hscale)

/-- Source ellipticity is unchanged by affine spatial rescaling. -/
theorem gmpRescaledCoefficient_elliptic {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (y : PDE.Vec d) (μ : ℝ) (x : PDE.Vec d) :
    PDE.IsEllipticMatrix Λ⁻¹ Λ (gmpRescaledCoefficient ω y μ x) :=
  EinsteinFull.Blueprint.gmpRegular_ellipticMatrix hΛ ω hω (y + μ⁻¹ • x)

/-- The rescaled source coefficient remains symmetric. -/
theorem gmpRescaledCoefficient_symm {d : ℕ} {Λ : ℝ}
    (ω : FieldPair d) (hω : IsRegular Λ ω) (y : PDE.Vec d) (μ : ℝ) (x : PDE.Vec d) :
    (gmpRescaledCoefficient ω y μ x).IsSymm :=
  (hω.1 (y + μ⁻¹ • x)).1

/-- The weighted rescaled coefficient has an ellipticity bound on any bounded open domain. -/
theorem gmpRescaledCoefficient_weighted_elliptic
    {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (y : PDE.Vec d) (μ : ℝ) (i : Fin d) {U : Set (PDE.Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U) :
    ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (2 * x i) • gmpRescaledCoefficient ω y μ x) := by
  classical
  obtain ⟨M, hM, hcoord⟩ := hU.isBoundedDomain
  let a := gmpRescaledCoefficient ω y μ
  let w : PDE.Vec d → ℝ := fun x => Real.exp (2 * x i)
  have ha : Continuous a := continuous_gmpRescaledCoefficient ω y μ
  have hw : Continuous w := Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))
  have hmeas : Measurable (fun x j k => if x ∈ U then (w x • a x) j k else 0) := by
    refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => ?_
    exact ((continuous_apply k).comp ((continuous_apply j).comp (hw.smul ha))).measurable.piecewise
      hU.isOpen.measurableSet measurable_const
  refine ⟨Real.exp (-2 * M) * Λ⁻¹, Real.exp (2 * M) * Λ, hmeas, ?_⟩
  intro x hx
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hxcoord := abs_le.mp (hcoord x hx i)
  have hlo : Real.exp (-2 * M) ≤ w x := by
    apply Real.exp_le_exp.mpr
    linarith [hxcoord.1]
  have hhi : w x ≤ Real.exp (2 * M) := by
    apply Real.exp_le_exp.mpr
    linarith [hxcoord.2]
  exact (PDE.isEllipticMatrix_smul (Real.exp_pos (2 * x i))
    (gmpRescaledCoefficient_elliptic hΛ ω hω y μ x)).mono
      (mul_pos (Real.exp_pos _) (inv_pos.mpr hΛpos))
      (mul_le_mul_of_nonneg_right hlo (inv_nonneg.mpr hΛpos.le))
      (mul_le_mul_of_nonneg_right hhi hΛpos.le)

end EinsteinFull.Regeneration
