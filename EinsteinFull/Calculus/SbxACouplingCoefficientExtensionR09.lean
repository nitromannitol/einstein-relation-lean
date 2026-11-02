import EinsteinFull.Calculus.SbxAPhysicalWeightBoundsR09
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Environment.EuclideanLipschitz

open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP

namespace EinsteinFull.Calculus

/-- The actual normalized physical coefficients admit globally elliptic extensions
with a constant uniform in the coupling scale, signed force and environment. -/
theorem a_coupling_uniform_coefficient_extension {d : ℕ} (hd : 2 ≤ d)
    (Λ l : ℝ) (hΛ : 1 ≤ Λ) (hl : 0 < l) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 ∧ ∀ (R lam : ℝ), 0 < R → l = |lam| * R →
      ∀ (c : Vec d) (ω : FieldPair d), IsRegular Λ ω →
      ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α ∧
        ∀ z ∈ sourceBall c (6 * R),
          ρ z = s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c ∧
          α z = (physicalForceWeight hd lam c)⁻¹ • s4PhysicalAlpha hd ω lam z := by
  let L := Real.exp (-12*l - 2*Λ)
  let U := Real.exp (12*l + 2*Λ)
  let A := (1/2 : ℝ) * L * Λ⁻¹
  let B := (1/2 : ℝ) * U * Λ
  have hL : 0 < L := Real.exp_pos _
  have hU : 0 < U := Real.exp_pos _
  have hΛpos : 0 < Λ := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let κ := min 1 (min L (min U⁻¹ (min A B⁻¹)))
  have hk : 0 < κ := by dsimp [κ]; positivity
  have hk1 : κ ≤ 1 := min_le_left _ _
  have hkL : κ ≤ L := (min_le_right _ _).trans (min_le_left _ _)
  have hkU : κ ≤ U⁻¹ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hkA : κ ≤ A := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hkB : κ ≤ B⁻¹ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hUκ : U ≤ κ⁻¹ := by
    have h := inv_le_inv₀ (inv_pos.mpr hU) hk |>.2 hkU
    simpa using h
  have hBκ : B ≤ κ⁻¹ := by
    have h := inv_le_inv₀ (inv_pos.mpr hB) hk |>.2 hkB
    simpa using h
  refine ⟨κ, hk, hk1, ?_⟩
  intro R lam hR hlR c ω hω
  let q : Vec d → ℝ := fun z => max (-6*l) (min (6*l) (lam * ((z-c) (firstCoordinateIndex hd))))
  let ρ : Vec d → ℝ := fun z => Real.exp (2*q z - 2*ω.2 z)
  let α : Vec d → Mat d := fun z => ((1/2 : ℝ)*ρ z) • ω.1 z
  have hqlo (z : Vec d) : -6*l ≤ q z := le_max_left _ _
  have hqhi (z : Vec d) : q z ≤ 6*l := by
    apply max_le <;> [linarith; exact min_le_left _ _]
  have hρ (z : Vec d) : L ≤ ρ z ∧ ρ z ≤ U := by
    have hv := abs_le.mp (hω.2.1 z)
    constructor
    · change Real.exp (-12*l - 2*Λ) ≤ Real.exp (2*q z - 2*ω.2 z)
      apply Real.exp_le_exp.mpr
      linarith [hqlo z]
    · change Real.exp (2*q z - 2*ω.2 z) ≤ Real.exp (12*l + 2*Λ)
      apply Real.exp_le_exp.mpr
      linarith [hqhi z]
  have hqcont : Continuous q := by
    dsimp [q]
    fun_prop
  have hVcont : Continuous ω.2 :=
    (lipschitzWith_of_euclidean_bound Λ hΛpos.le hω.2.2.2).continuous
  have hρcont : Continuous ρ := by
    dsimp [ρ]
    fun_prop
  have hacont : Continuous ω.1 := continuous_pi fun i => continuous_pi fun j =>
    (lipschitzWith_of_euclidean_bound Λ hΛpos.le (hω.2.2.1.entry_bound i j)).continuous
  have hαcont : Continuous α := by
    dsimp [α]
    exact (continuous_const.mul hρcont).smul hacont
  refine ⟨ρ, α, ⟨hρcont.measurable, ?_, ?_⟩, ?_⟩
  · let : MeasurableSpace (Vec d) := MeasurableSpace.pi
    let : BorelSpace (Vec d) := Pi.borelSpace
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    exact hαcont.measurable
  · intro z
    refine ⟨hkL.trans (hρ z).1, (hρ z).2.trans hUκ, ?_, ?_⟩
    · dsimp [α]
      rw [(hω.1 z).1]
    · intro v
      have hsq : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have he := (hω.1 z).2 v
      have hnorm : 0 ≤ ρ z := hL.le.trans (hρ z).1
      have hlow : 0 ≤ Λ⁻¹ * euclideanSq v := mul_nonneg (inv_nonneg.mpr hΛpos.le) hsq
      have hdot : dot v ((α z).mulVec v) = ((1/2 : ℝ) * ρ z) * dot v ((ω.1 z).mulVec v) := by
        simp only [α, Matrix.smul_mulVec, dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hdot]
      have hlo := mul_le_mul_of_nonneg_right (hρ z).1 hlow
      have hlo' := mul_le_mul_of_nonneg_left he.1 hnorm
      have hhi := mul_le_mul_of_nonneg_right (hρ z).2 (mul_nonneg hΛpos.le hsq)
      have hhi' := mul_le_mul_of_nonneg_left he.2 hnorm
      have hka := mul_le_mul_of_nonneg_right hkA hsq
      have hbk := mul_le_mul_of_nonneg_right hBκ hsq
      dsimp [A, B] at hka hbk
      constructor <;> nlinarith only [hlo, hlo', hhi, hhi', hka, hbk]
  · intro z hz
    have hz' : euclideanNorm (z-c) < 6*R := hz
    have hg : |lam| * euclideanNorm (z-c) ≤ 6*l := by
      calc
        _ ≤ |lam| * (6*R) := mul_le_mul_of_nonneg_left hz'.le (abs_nonneg lam)
        _ = 6*l := by rw [hlR]; ring
    have hc := coordinate_abs_le_euclideanNorm (z-c) (firstCoordinateIndex hd)
    have habs : |lam * ((z-c) (firstCoordinateIndex hd))| ≤ 6*l := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left hc (abs_nonneg lam)).trans hg
    have hqeq : q z = lam * ((z-c) (firstCoordinateIndex hd)) := by
      change max (-6*l) (min (6*l) (lam * ((z-c) (firstCoordinateIndex hd)))) = _
      rw [min_eq_right (abs_le.mp habs).2]
      apply max_eq_right
      linarith [(abs_le.mp habs).1]
    have hρeq : ρ z = s4PhysicalRho hd ω lam z / physicalForceWeight hd lam c := by
      dsimp [ρ]
      rw [hqeq, s4PhysicalRho, physicalReversibleDensity_eq_source_formula,
        physicalForceWeight, ← Real.exp_sub]
      congr 1
      simp only [Pi.sub_apply]
      ring
    refine ⟨hρeq, ?_⟩
    dsimp [α, s4PhysicalAlpha]
    rw [hρeq, smul_smul]
    congr 1
    ring

#print axioms a_coupling_uniform_coefficient_extension

end EinsteinFull.Calculus
