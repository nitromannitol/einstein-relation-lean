import EinsteinRelation.Correctors.ReducedEnergyIdentity
import EinsteinRelation.Correctors.AKMCanonicalColumnScalarDecay

/-! # Decay of the actual reduced-law column residual

Source: `paper/main.tex:800–808`. The specified-flow scalar decay estimate
transfers to any actual reduced-law endpoint realization. Its constant
precedes the environment law. No pointwise choice of a stationary
representative is made.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The actual normalized endpoint residual tends strongly to zero along
positive integer times. Source: `paper/main.tex:800–808`; AKM (9.7). -/
theorem column_residual_L2_decay
    (hdecay : ParabolicSemigroupKernelDecay)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u p.1 p.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ f : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q),
      (∀ n, ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f n (translate x (reduce ω.1)) = ((ellipticityScale L)⁻¹*r₀⁻¹) *
          u (project (r₀ := r₀) Q.ellipticity_parameter ω) ((n : ℝ)+1,r₀⁻¹ • x)) →
      (∀ n, ‖f n‖ ≤ C*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4)) ∧
      Tendsto f atTop (𝓝 0) := by
  obtain ⟨B,hB,hscalar⟩ := parabolicSemigroupKernelDecay_canonical_column_moments
    hdecay d hd (AKMUpperEllipticity L) 1 (one_lt_AKMUpperEllipticity hL)
      (by norm_num) (by norm_num)
  let c : ℝ := (ellipticityScale L)⁻¹*r₀⁻¹
  let C : ℝ := 1+|c| *B 2
  have hB2 : 0 < B 2 := hB 2 (by norm_num)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C,hC,?_⟩
  intro Q i u G hu hflow f he
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  have hvol : 0 < (volume (originBall d 1)).toReal := by
    simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d 1 zero_lt_one
  let ν : Measure (Vec d) := (volume (originBall d 1))⁻¹ • volume.restrict (originBall d 1)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel (ENNReal.toReal_pos_iff.mp hvol).1.ne'
      (ENNReal.toReal_pos_iff.mp hvol).2.ne⟩
  have hν : ν ≪ volume :=
    Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)
  have hn (n : ℕ) : (1 : ℝ) ≤ (n : ℝ)+1 := by
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hnorm (n : ℕ) : ‖f n‖ ≤ C*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4) := by
    let D : Coefficient d (AKMUpperEllipticity L) → Vec d → ℝ :=
      fun A x => c*u A ((n : ℝ)+1,x)
    have hDm : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => D p.1 p.2) :=
      measurable_const.mul (hu.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd)))
    have he' : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        f n (translate (r₀ • x) (reduce ω.1)) =
          D (project (r₀ := r₀) Q.ellipticity_parameter ω) x := by
      filter_upwards [he n] with ω hω
      filter_upwards [(Measure.quasiMeasurePreserving_smul
        (volume : Measure (Vec d)) hr).ae hω] with x hx
      simpa only [D,c,smul_smul,inv_mul_cancel₀ hr,one_smul] using hx
    have hb (x : Vec d) : eLpNorm (fun A => D A x) 2 (actualCoefficientLaw Q) ≤
        ENNReal.ofReal (|c| *(B 2*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4))) := by
      have hs := (hscalar (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)
        i u G hu hflow 2 (by norm_num) _ (hn n) x).2
      change eLpNorm (c • (fun A => u A ((n : ℝ)+1,x))) 2 _ ≤ _
      rw [eLpNorm_const_smul]
      have hs' : eLpNorm (fun A => u A ((n : ℝ)+1,x)) 2 (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (B 2*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by simpa using hs
      refine (mul_le_mul_right hs' _).trans_eq ?_
      rw [← ofReal_norm_eq_enorm,Real.norm_eq_abs,← ENNReal.ofReal_mul (abs_nonneg c)]
    have hh := eLpNorm_le_of_coefficient_point_moments Q (f n)
      (Lp.stronglyMeasurable (f n)).measurable D hDm ν hν he' hb
    rw [← Lp.enorm_def,← ofReal_norm_eq_enorm] at hh
    have hn0 : 0 ≤ (n : ℝ)+1 := (hn n).trans' zero_le_one
    have hD0 : 0 ≤ |c| *(B 2*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by positivity
    have hh' := (ENNReal.ofReal_le_ofReal_iff hD0).mp hh
    apply hh'.trans
    dsimp only [C]
    nlinarith [Real.rpow_nonneg hn0 (-(1 : ℝ)/2-(d : ℝ)/4)]
  refine ⟨hnorm,?_⟩
  have ht : Tendsto (fun n : ℕ => (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hp : 0 < (1 : ℝ)/2+(d : ℝ)/4 := by positivity
  have hb0 : Tendsto (fun n : ℕ => C*((n : ℝ)+1)^(-(1 : ℝ)/2-(d : ℝ)/4)) atTop (𝓝 0) := by
    simpa only [neg_add_rev,add_comm,neg_div,sub_eq_add_neg,mul_zero] using
      (tendsto_const_nhds (x := C)).mul ((tendsto_rpow_neg_atTop hp).comp ht)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun n => norm_nonneg (f n)) hnorm hb0)

end EinsteinRelation.Correctors
