import EinsteinRelation.Correctors.CanonicalSpatialSubsequence
import EinsteinRelation.Correctors.SpatialRmsFatou

/-! # Spatial RMS tails of the actual canonical stationary gradient

Source: `paper/main.tex:800–808,842–849`. Finite actual column increments
converge spatially to the canonical gradient. Their stochastic spatial
RMS estimates pass through this limit by Fatou's lemma.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A prescribed spatial-ball decay bound for the actual column flow
controls the canonical stationary remainder on that same ball. The
canonical identification and initial time energy are derived internally.
Source: `paper/main.tex:800–808,842–849`. -/
theorem canonical_column_ball_rms_remainder
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L)
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hu : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u p.1 p.2))
    (hG : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => G p.1 p.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (hweak : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
      HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x)))
    {m C α T ρ : ℝ} (hm : 1 ≤ m) (hC : 0 < C) (hα : 0 < α)
    (hT : 1 ≤ T) (hρ : 0 < ρ)
    (hb : ∀ t : ℝ, 1 ≤ t →
      eLpNorm (fun A => vectorRms volume (originBall d ρ) (fun x => G A (t,x)))
        (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤ ENNReal.ofReal (C*t^(-1-α))) :
    let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
    let F := fun (ω : PhysicalField d L) (x : Vec d) =>
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • x) (reduce ω.1)) -
        ∫ t in Ioo 0 T, WithLp.toLp 2
          (G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x))
    (∀ᵐ ω ∂physicalReferenceLaw Q, MemLp (F ω) 2 ν) ∧
      MemLp (fun ω => Real.sqrt (∫ x, ‖F ω x‖^2 ∂ν)) (ENNReal.ofReal m)
        (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖F ω x‖^2 ∂ν)) (ENNReal.ofReal m)
        (physicalReferenceLaw Q) ≤ ENNReal.ofReal ((C/α)*T^(-α)) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  let ν : Measure (Vec d) := (volume (originBall d ρ))⁻¹ • volume.restrict (originBall d ρ)
  have hv := ENNReal.toReal_pos_iff.mp (show 0 < (volume (originBall d ρ)).toReal by
    simpa only [originBall,ball,sub_zero] using ball_volume_pos_finite d ρ hρ)
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv.1.ne' hv.2.ne⟩
  have hν : ν ≪ volume :=
    Measure.smul_absolutelyContinuous.trans (Measure.restrict_le_self.absolutelyContinuous)
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hJG : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => J (G z.1 z.2)) := J.continuous.measurable.comp hG
  have hK : 0 < AKMUpperEllipticity L :=
    zero_lt_one.trans (one_lt_AKMUpperEllipticity Q.ellipticity_parameter)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hsq (v : Vec d) : ‖J v‖^2 = euclideanSq v := by
    change ‖WithLp.toLp 2 v‖^2 = _
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
    exact Real.sq_sqrt (euclideanSq_nonneg_fisher _)
  obtain ⟨s,hs,hlim⟩ := exists_actual_column_subseq_canonical_gradient
    hdecay hreg d hd L r₀ hL Q i u G hu hG hflow hweak
  obtain ⟨N,hN⟩ := exists_nat_gt T
  let S : ℕ → ℝ := fun n => (s (n+N) : ℝ)+1
  have hTS (n : ℕ) : T ≤ S n := by
    have hn : N ≤ s (n+N) := (Nat.le_add_left N n).trans (hs.id_le _)
    have hnR : (N : ℝ) ≤ s (n+N) := by exact_mod_cast hn
    dsimp only [S]
    linarith
  let H : ℝ → Coefficient d (AKMUpperEllipticity L) × Vec d → EuclideanSpace ℝ (Fin d) :=
    fun τ z => ∫ t in Ioo 0 τ, J (G z.1 (t,z.2))
  have hHm (τ : ℝ) : Measurable (H τ) :=
    (hJG.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))).stronglyMeasurable.integral_prod_right'.measurable
  have hπ : Measurable (fun z : PhysicalField d L × Vec d =>
      (project (r₀ := r₀) Q.ellipticity_parameter z.1,z.2)) :=
    (measurePreserving_akmProject Q).measurable.prodMap measurable_id
  let f : ℕ → PhysicalField d L × Vec d → EuclideanSpace ℝ (Fin d) :=
    fun n z => H (S n) (project (r₀ := r₀) Q.ellipticity_parameter z.1,z.2) -
      H T (project (r₀ := r₀) Q.ellipticity_parameter z.1,z.2)
  have hfm (n : ℕ) : Measurable (f n) := ((hHm (S n)).comp hπ).sub ((hHm T).comp hπ)
  have hcanonicalm : Measurable (fun z : PhysicalField d L × Vec d =>
      (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • z.2) (reduce z.1.1))) :=
    (Lp.stronglyMeasurable (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).measurable.comp
      (Probability.continuous_translate.measurable.comp
      ((measurable_const.smul measurable_snd).prodMk
        ((measurePreserving_physicalReduction Q).measurable.comp measurable_fst)))
  let g : PhysicalField d L × Vec d → EuclideanSpace ℝ (Fin d) := fun z =>
    (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate (r₀ • z.2) (reduce z.1.1)) -
      H T (project (r₀ := r₀) Q.ellipticity_parameter z.1,z.2)
  have hgm : Measurable g := hcanonicalm.sub ((hHm T).comp hπ)
  have hinc (n : ℕ) := by
    apply initial_gradient_increment_moment (actualCoefficientLaw Q) ν
      (fun z => J (G z.1 z.2)) hJG
      (ENNReal.one_le_ofReal.mpr hm) ENNReal.ofReal_ne_top hC hα hT0 (hTS n)
    · filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
        with A hA hbA
      exact semigroup_initial_euclidean_energy hK hA.1
        (hG.comp (measurable_const.prodMk measurable_id)) hbA (hT0.trans_le (hTS n)) hρ
    · filter_upwards [hflow] with A hA
      have hl := semigroupSolution_gradient_tail_slice_memLp hA.1
        (hG.comp (measurable_const.prodMk measurable_id)) hT0 hρ
      filter_upwards [hl] with t ht
      exact J.toContinuousLinearMap.comp_memLp' (ht.smul_measure (ENNReal.inv_ne_top.mpr hv.1.ne'))
    · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
      simpa only [hsq,vectorRms,setAverage_eq'] using hb t (hT.trans ht.le)
  have hloc (n : ℕ) : ∀ᵐ ω ∂physicalReferenceLaw Q, MemLp (fun x => f n (ω,x)) 2 ν :=
    (measurePreserving_akmProject Q).quasiMeasurePreserving.ae (hinc n).1
  have hbnd (n : ℕ) : eLpNorm (fun ω => Real.sqrt (∫ x, ‖f n (ω,x)‖^2 ∂ν))
      (ENNReal.ofReal m) (physicalReferenceLaw Q) ≤ ENNReal.ofReal ((C/α)*T^(-α)) := by
    have hM : Measurable (fun A => Real.sqrt (∫ x, ‖H (S n) (A,x)-H T (A,x)‖^2 ∂ν)) :=
      ((((hHm (S n)).sub (hHm T)).norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
    simpa only [f,H,Function.comp_def] using
      (eLpNorm_comp_measurePreserving hM.aestronglyMeasurable (measurePreserving_akmProject Q)).trans_le (hinc n).2
  have hcoord : ∀ n, ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ x ∂volume,
      (H (S n) (project (r₀ := r₀) Q.ellipticity_parameter ω,x)).ofLp =
        fun j => ∫ t in Ioo 0 (S n),
          G (project (r₀ := r₀) Q.ellipticity_parameter ω) (t,x) j := by
    intro n
    have hc : ∀ᵐ A ∂actualCoefficientLaw Q, ∀ᵐ x ∂volume,
        (H (S n) (A,x)).ofLp = fun j => ∫ t in Ioo 0 (S n), G A (t,x) j := by
      filter_upwards [hflow,ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow]
        with A hA hbA
      filter_upwards [semigroup_initial_euclidean_coordinates hK hA.1
        (hG.comp (measurable_const.prodMk measurable_id)) hbA (hT0.trans_le (hTS n))]
        with x hx
      exact hx (S n) le_rfl
    exact (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hc
  apply spatial_rms_moment_le_of_ae_tendsto (physicalReferenceLaw Q) ν f g hfm hgm
    (zero_lt_one.trans_le hm) hloc hbnd
  filter_upwards [hlim,ae_all_iff.mpr hcoord] with ω hω hcω
  filter_upwards [hω.filter_mono hν.ae_le,
    (ae_all_iff.mpr hcω).filter_mono hν.ae_le] with x hx hcx
  have hshift : Tendsto (fun n => n+N) atTop atTop := tendsto_add_atTop_nat N
  have hlim' := (hx.comp hshift).sub_const
    (H T (project (r₀ := r₀) Q.ellipticity_parameter ω,x))
  apply hlim'.congr
  intro n
  congr 1
  apply WithLp.ofLp_injective
  exact (hcx n).symm

end EinsteinRelation.Correctors
