import EinsteinRelation.Correctors.L2WeightedParameterCurve

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The literal weighted parameter integral has its actual differentiable
L² realization. Source: `paper/main.tex:798–806`; temporal regularization. -/
theorem exists_differentiable_L2_finite_integral {Ω X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) [IsFiniteMeasure μ] (ν : Measure X) [IsFiniteMeasure ν]
    {f : Ω × X → ℝ} (hf : MemLp f 2 (μ.prod ν))
    (m m' : ℝ → Ω × X → ℝ)
    (hm : ∀ t, AEStronglyMeasurable (m t) (μ.prod ν))
    (hm' : ∀ t, AEStronglyMeasurable (m' t) (μ.prod ν))
    (hd : ∀ t z, HasDerivAt (fun s => m s z) (m' t z) t)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hb : ∀ t z, |m t z| ≤ C) (hb' : ∀ t z, |m' t z| ≤ D) :
    ∃ F F' : ℝ → Lp ℝ 2 ν,
      (∀ t, (F t : X → ℝ) =ᵐ[ν] fun x => ∫ ω, m t (ω,x) * f (ω,x) ∂μ) ∧
      (∀ t, (F' t : X → ℝ) =ᵐ[ν] fun x => ∫ ω, m' t (ω,x) * f (ω,x) ∂μ) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  by_cases hzero : μ = 0
  · subst μ
    refine ⟨fun _ => 0,fun _ => 0,?_,?_,?_⟩
    · intro t
      simpa using (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν))
    · intro t
      simpa using (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := ν))
    · intro t
      exact hasDerivAt_const t 0
  have hmass : μ Set.univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hzero
  have hfin : μ Set.univ ≠ ⊤ := measure_ne_top μ _
  let c := (μ Set.univ)⁻¹
  let π : Measure Ω := c • μ
  haveI : IsProbabilityMeasure π := ⟨by
    simp only [π,Measure.smul_apply,smul_eq_mul,c]
    exact ENNReal.inv_mul_cancel hmass hfin⟩
  have hp : π.prod ν = c • (μ.prod ν) := Measure.prod_smul_left c
  have hfπ : MemLp f 2 (π.prod ν) := by
    rw [hp]
    exact hf.smul_measure (ENNReal.inv_ne_top.mpr hmass)
  have hmπ t : AEStronglyMeasurable (m t) (π.prod ν) := by
    rw [hp]
    exact (hm t).smul_measure c
  have hmπ' t : AEStronglyMeasurable (m' t) (π.prod ν) := by
    rw [hp]
    exact (hm' t).smul_measure c
  obtain ⟨F,F',hF,hF',hder⟩ := exists_differentiable_L2_parameter_integral
    π ν hfπ m m' hmπ hmπ' hd hC hD hb hb'
  let M := (μ Set.univ).toReal
  have hM0 : M ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hmass,hfin⟩
  have havg (k : Ω → ℝ) : M * (∫ ω, k ω ∂π) = ∫ ω, k ω ∂μ := by
    rw [show π = c • μ from rfl,integral_smul_measure]
    simp only [smul_eq_mul,c,ENNReal.toReal_inv]
    change M * (M⁻¹ * _) = _
    rw [← mul_assoc,mul_inv_cancel₀ hM0,one_mul]
  refine ⟨fun t => M • F t,fun t => M • F' t,?_,?_,?_⟩
  · intro t
    filter_upwards [Lp.coeFn_smul M (F t),hF t] with x h1 h2
    rw [h1]
    change M * _ = _
    rw [h2]
    exact havg _
  · intro t
    filter_upwards [Lp.coeFn_smul M (F' t),hF' t] with x h1 h2
    rw [h1]
    change M * _ = _
    rw [h2]
    exact havg _
  · intro t
    exact (hder t).const_smul M

end EinsteinRelation.Correctors
