import EinsteinRelation.Correctors.PhysicalCouplingNormalizedDissipation
import EinsteinRelation.Correctors.PhysicalCouplingScalarProfile
import EinsteinRelation.Correctors.PairedEnergyMomentDecay

/-! # Probability decay of the actual paired dissipation

Source: `paper/main.tex:834–855`. The probability energy estimate is
instantiated with the same actual canonical column flow. Initial traces
and the scalar profile near time zero are derived, and spatial volume
normalization is literal. Constants precede the environment and coupling.
-/

open MeasureTheory Set
open scoped ENNReal Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The actual weighted dissipation at time scale `4R²` has the sharp
probability moment rate. The sole scalar decay premise concerns the same
specified canonical flow at large times. Source: `paper/main.tex:834–855`. -/
theorem physicalCoupling_paired_canonical_energy_moment_decay
    (d n : ℕ) (hd : 2 ≤ d) (hn : 1+(d : ℝ)/2 < (n : ℝ))
    (L r₀ C D : ℝ) (hC : 0 ≤ C) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ p : ℝ, 2 ≤ p →
      (∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ μ : Measure (PhysicalField d L × PhysicalField d L), IsProbabilityMeasure μ →
      MeasurePreserving Prod.fst μ (physicalReferenceLaw Q) →
      MeasurePreserving Prod.snd μ (physicalReferenceLaw Q) →
      ∀ (R : ℝ), 1 ≤ R → ∀ U : Set (Vec d), IsOpen U → IsCompact (closure U) →
      ∀ [IsFiniteMeasure (volume.restrict U)], 0 < volume.real U →
      (∀ᵐ A ∂μ, Set.EqOn (project (r₀ := r₀) Q.ellipticity_parameter A.1) (project (r₀ := r₀) Q.ellipticity_parameter A.2) U) →
      ∀ χ : Vec d → ℝ, IsSpatialTest U χ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, euclideanSq (gradient χ x) ≤ (D/R)^2) →
      let F := fun A => Real.sqrt ((4*R^2) * ∫ t in Icc (0 : ℝ) (4*R^2),
        ⨍ x in U, χ x^(2*n) * euclideanSq (G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x)))
      MemLp F (ENNReal.ofReal p) μ ∧
        eLpNorm F (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (B*R^(-(d : ℝ)/2)) := by
  obtain ⟨M,hM,hprofile⟩ := physicalCoupling_canonical_column_coupled_profile d L r₀ C hC
  let K : ℝ := 4*(n : ℝ)^2*(AKMUpperEllipticity L)^2*D^2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨B,hB,hbound⟩ := paired_energy_moment_decay d n hd hn hK hM.le
  refine ⟨B,hB,?_⟩
  intro Q i u G hum hGm hflow p hp hlate μ hμ hfst hsnd R hR U hU hUc _ hUpos hEq χ hχ hχb hχD
  generalize hπdef : project (d := d) (r₀ := r₀) Q.ellipticity_parameter = π at hEq ⊢
  have hEq' := hEq
  rw [← hπdef] at hEq'
  have hπ : MeasurePreserving π (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
    hπdef ▸ measurePreserving_akmProject Q
  have hGmPhys : Measurable (fun z : PhysicalField d L × (ℝ × Vec d) =>
      G (π z.1) z.2) :=
    hGm.comp (hπ.measurable.prodMap measurable_id)
  letI : IsProbabilityMeasure μ := hμ
  have hR0 : 0 < R := zero_lt_one.trans_le hR
  have hT : 0 < 4*R^2 := by positivity
  have hU0 : volume U ≠ 0 := by
    intro h
    simp [Measure.real, h] at hUpos
  have hUfin : volume U ≠ ∞ := by
    simpa only [Measure.restrict_apply_univ] using
      (measure_ne_top (volume.restrict U) Set.univ)
  let ν : Measure (Vec d) := (volume U)⁻¹ • volume.restrict U
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hU0 hUfin⟩
  let a := fun z : ℝ × (PhysicalField d L × PhysicalField d L) =>
    Real.sqrt (∫ x, (u (π z.2.1) (z.1,x) - u (π z.2.2) (z.1,x))^2 ∂ν)
  have ha := hprofile Q i u G hum hflow p hp hlate μ hμ hfst hsnd ν inferInstance
  rw [hπdef] at ha
  let H : ℝ → ℝ := fun t => M*(1+max t 0)^(-(1 : ℝ)/2-(d : ℝ)/4)
  have hHm : Measurable H :=
    measurable_const.mul ((measurable_const.add (measurable_id.max measurable_const)).pow_const _)
  have hH (t : ℝ) : 0 ≤ H t := by dsimp [H]; positivity
  have hHprofile (t : ℝ) (ht : 0 ≤ t) :
      H t ≤ M*(1+t)^(-(1 : ℝ)/2-(d : ℝ)/4) := by simp [H,max_eq_left ht]
  let E := fun A : PhysicalField d L × PhysicalField d L =>
    ∫ t in Icc (0 : ℝ) (4*R^2), ⨍ x in U,
      χ x^(2*n) * euclideanSq (G (π A.1) (t,x) - G (π A.2) (t,x))
  have hEpos (A) : 0 ≤ E A := by
    dsimp only [E]
    apply integral_nonneg
    intro t
    change 0 ≤ ⨍ x in U, χ x^(2*n) * euclideanSq (G (π A.1) (t,x) - G (π A.2) (t,x))
    rw [setAverage_eq']
    exact integral_nonneg fun x => mul_nonneg (pow_nonneg (hχb x).1 _) (euclideanSq_nonneg_coords _)
  have hEm : Measurable E := by
    have hg : Measurable (fun z : ((PhysicalField d L × PhysicalField d L) × ℝ) × Vec d =>
        G (π z.1.1.1) (z.1.2,z.2) - G (π z.1.1.2) (z.1.2,z.2)) :=
      (hGmPhys.comp (measurable_fst.fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).sub
        (hGmPhys.comp (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd)))
    have hsq : Measurable (fun z : ((PhysicalField d L × PhysicalField d L) × ℝ) × Vec d => euclideanSq
        (G (π z.1.1.1) (z.1.2,z.2) - G (π z.1.1.2) (z.1.2,z.2))) := by
      unfold euclideanSq dot
      exact Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp hg).mul ((measurable_pi_apply j).comp hg)
    have he := ((hχ.1.continuous.measurable.comp measurable_snd).pow_const (2*n)).mul hsq
    have hsp := he.stronglyMeasurable.integral_prod_right' (ν := ν)
    simpa only [E,setAverage_eq'] using hsp.integral_prod_right'.measurable
  have hn2 : 2 ≤ n := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hn' : (2 : ℝ) < n := by linarith
    exact_mod_cast hn'.le
  have henergy : ∀ᵐ A ∂μ, E A ≤ (K/R^2 *
      ∫ t in Icc (0 : ℝ) (4*R^2), a (t,A)^(2/(n : ℝ)))^n := by
    have hr := physicalCoupling_paired_canonical_normalized_dissipation_le Q i u G
      hflow μ hfst hsnd hU hUc hUpos hEq' hT hχ hχb hχD n hn2
    have hr' := hr
    rw [hπdef] at hr'
    have hsqrt (t : ℝ) (A) : a (t,A)^(2/(n : ℝ)) =
        (⨍ x in U, (u (π A.1) (t,x)-u (π A.2) (t,x))^2)^((n : ℝ)⁻¹) := by
      rw [setAverage_eq']
      dsimp [a]
      rw [show 2/(n : ℝ) = (2 : ℝ)*(n : ℝ)⁻¹ by ring,
        Real.rpow_mul (Real.sqrt_nonneg _), Real.rpow_two,
        Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    have hfactor : 4*(n : ℝ)^2*(AKMUpperEllipticity L)^2*(D/R)^2 = K/R^2 := by
      dsimp [K]
      ring
    simpa only [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc,
      hfactor,hsqrt,E] using hr'
  apply hbound μ p hp R hR H hHm hH hHprofile a ha.1
    (fun _ => Real.sqrt_nonneg _) (fun t ht => ?_)
    (fun A => Real.sqrt ((4*R^2)*E A)) E
    ((measurable_const.mul hEm).sqrt) (fun _ => Real.sqrt_nonneg _)
    (ae_of_all _ hEpos) henergy
    (ae_of_all _ fun A => le_of_eq (Real.sq_sqrt (mul_nonneg hT.le (hEpos A))))
  simpa only [H,max_eq_left ht.le] using (ha.2 t ht).2

end EinsteinRelation.Correctors
