import EinsteinFull.Calculus.CLRetainedDuhamelComparison
import EinsteinFull.Calculus.CLDeterministicPointKernel
import EinsteinFull.Calculus.CLLargeForce
import EinsteinFull.Calculus.C7EndpointUniformProjection
import EinsteinFull.Calculus.C1ShortTimeClockEndpointProjection
import EinsteinFull.Calculus.C1CrudeEnergyLargeTime
import EinsteinFull.Calculus.C25EndpointLocalObservation
import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.S1SharpRegular
import EinsteinFull.Blueprint.G2.Proofs.C1CrudeEnergy
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environment
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi

/-! Large-time locality of the forward and clock endpoints, `paper/main.tex:715`.
The actual orbit is the physical kernel convolution of its stationary datum;
cutting the datum off at a large radius costs a Gaussian tail, and replacing the
coefficients outside a smaller ball costs the retained Duhamel comparison. The
retained evolution is locally measurable, so shrinking averages give the local
observation. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull
open EinsteinRelation Blueprint

/-- A locally measurable family of retained forward evolutions of given data,
retaining the transpose evolution of each retained field. -/
theorem clr_retained_measurable_pair_evolution {d : ℕ} (χ : C(Vec d, ℝ)) (U : Set (Vec d))
    (hχ : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ) (i : Fin d) (ζ : ℂ)
    (fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr) :
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ ((EinsteinRelation.localSigma U).prod inferInstance) (borel _)
        (Function.uncurry V) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Prdag ∧
          ∀ t, V ω t = Pr t (fr ω) := by
  classical
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have hgood : MeasurableSet
      {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ} := by
    have hc : IsClosed {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      have he : {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} =
          ⋂ x : Vec d,
            ((⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | ω.1 x j k = ω.1 x k j}) ∩
              ⋂ ξ : Fin d → ℝ,
                ({ω : FieldPair d | Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil (ω.1 x) ξ ξ} ∩
                 {ω : FieldPair d | s5Bil (ω.1 x) ξ ξ ≤ Λ * ∑ j, ξ j ^ 2})) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h x
          exact ⟨(h x).symm, fun ξ => ⟨(h x).lower ξ, (h x).upper ξ⟩⟩
        · intro h x
          exact ⟨hΛ, (h x).1, fun ξ => ((h x).2 ξ).1, fun ξ => ((h x).2 ξ).2⟩
      rw [he]
      apply isClosed_iInter
      intro x
      refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k => ?_)
        (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
      · apply isClosed_eq <;> fun_prop
      · apply isClosed_le continuous_const
        unfold s5Bil
        fun_prop
      · apply isClosed_le _ continuous_const
        unfold s5Bil
        fun_prop
    have hcm : @MeasurableSet (FieldPair d) (borel _)
        {ω | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact hc.measurableSet
    exact hcm.preimage (ForcedLocality.measurable_retainedPair χ U hχ)
  obtain ⟨Pr, Prdag, hPr, _, hmPr, _⟩ :=
    short_time_clock_retained_physical_evolution χ U hχ Λ hΛ i ζ
  let good := {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let Ω := {ω : FieldPair d // ω ∈ good}
  let V (ω : FieldPair d) (t : ℝ≥0) :=
    if h : ω ∈ good then Pr ⟨ω, h⟩ t (fr ω) else 0
  refine ⟨V, ?_, ?_⟩
  · let s : Set (FieldPair d × ℝ≥0) := {q | q.1 ∈ good}
    have hs : MeasurableSet s := hgood.preimage measurable_fst
    have hv : Measurable (fun q : s => (⟨q.val.1, q.property⟩ : Ω)) :=
      (measurable_subtype_coe.fst).subtype_mk
    have ht : Measurable (fun q : s => q.val.2) := measurable_subtype_coe.snd
    have hf : Measurable (fun q : s => fr q.val.1) :=
      hfr.comp measurable_subtype_coe.fst
    exact Measurable.dite (hmPr.comp (hv.prodMk (ht.prodMk hf))) measurable_const hs
  · intro ω hω
    exact ⟨Pr ⟨ω, hω⟩, Prdag ⟨ω, hω⟩, (hPr ⟨ω, hω⟩).1, (hPr ⟨ω, hω⟩).2,
      fun t => dite_eq_left hω⟩

/-- The Euclidean Gaussian is integrable on the coordinate carrier. -/
theorem clr_gaussian_integrable (d : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-b * euclideanNorm x ^ 2)) volume := by
  have hproduct (x : Vec d) : Real.exp (-b * euclideanNorm x ^ 2) =
      ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    have hsq : euclideanNorm x ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))]
      simp only [pow_two]
    rw [hsq, Finset.mul_sum, Real.exp_sum]
  simp_rw [hproduct]
  exact Integrable.fintype_prod_dep (fun _ => integrable_exp_neg_mul_sq hb)

/-- The exact Euclidean Gaussian mass. -/
theorem clr_gaussian_integral (d : ℕ) (b : ℝ) :
    (∫ x : Vec d, Real.exp (-b * euclideanNorm x ^ 2)) = Real.sqrt (Real.pi / b) ^ d := by
  have hproduct (x : Vec d) : Real.exp (-b * euclideanNorm x ^ 2) =
      ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
    have hsq : euclideanNorm x ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))]
      simp only [pow_two]
    rw [hsq, Finset.mul_sum, Real.exp_sum]
  simp_rw [hproduct]
  calc
    _ = (∫ y : ℝ, Real.exp (-b * y ^ 2)) ^ d := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_volume_eq_pow (ι := Fin d)
          (fun y : ℝ => Real.exp (-b * y ^ 2)))
    _ = _ := congrArg (fun a : ℝ => a ^ d) (integral_gaussian b)

/-- An almost-everywhere Gaussian majorant centered at `x` bounds the integral by
the Gaussian mass. -/
theorem clr_integral_le_gaussian_mass {d : ℕ} (g : Vec d → ℂ) (x : Vec d)
    (A b : ℝ) (hb : 0 < b) (hg : AEStronglyMeasurable g volume)
    (hbound : ∀ᵐ y ∂volume, ‖g y‖ ≤ A * Real.exp (-b * euclideanNorm (x - y) ^ 2)) :
    Integrable g volume ∧ ‖∫ y, g y‖ ≤ A * Real.sqrt (Real.pi / b) ^ d := by
  have hm : MeasurableEmbedding (fun y : Vec d => x - y) :=
    (Homeomorph.subLeft x).measurableEmbedding
  have hshift : Integrable (fun y : Vec d =>
      Real.exp (-b * euclideanNorm (x - y) ^ 2)) volume :=
    (volume.measurePreserving_sub_left x).integrable_comp_of_integrable
      (clr_gaussian_integrable d b hb)
  have hmajor : Integrable (fun y : Vec d =>
      A * Real.exp (-b * euclideanNorm (x - y) ^ 2)) volume := hshift.const_mul A
  have hgi : Integrable g volume := hmajor.mono' hg hbound
  refine ⟨hgi, ?_⟩
  have hmass : (∫ y : Vec d, Real.exp (-b * euclideanNorm (x - y) ^ 2)) =
      Real.sqrt (Real.pi / b) ^ d := by
    calc
      _ = ∫ y : Vec d, Real.exp (-b * euclideanNorm y ^ 2) :=
        (volume.measurePreserving_sub_left x).integral_comp hm _
      _ = _ := clr_gaussian_integral d b
  calc
    ‖∫ y, g y‖ ≤ ∫ y, ‖g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : Vec d, A * Real.exp (-b * euclideanNorm (x - y) ^ 2) :=
      integral_mono_ae hgi.norm hmajor hbound
    _ = A * Real.sqrt (Real.pi / b) ^ d := by rw [integral_const_mul, hmass]

/-- The far part of a Gaussian kernel convolution with bounded data, for
centers in the unit ball and a cutoff equal to one on a ball of radius `r ≥ 2`. -/
theorem clr_far_kernel_tail {d : ℕ} (K : Vec d → Vec d → ℂ) (g : Vec d → ℂ)
    (χ : Vec d → ℝ) {A c t B r : ℝ} (hc : 0 < c) (ht : 0 < t) (hr : 2 ≤ r)
    (hK : ∀ x y, ‖K x y‖ ≤ A * Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t)))
    (hg : ∀ᵐ y ∂volume, ‖g y‖ ≤ B) (hχ : ∀ y, euclideanNorm y ≤ r → χ y = 1)
    (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1) (x : Vec d) (hx : euclideanNorm x ≤ r / 2)
    (hmeas : AEStronglyMeasurable (fun y => K x y * (((1 - χ y : ℝ)) : ℂ) * g y) volume) :
    Integrable (fun y => K x y * (((1 - χ y : ℝ)) : ℂ) * g y) volume ∧
    ‖∫ y, K x y * (((1 - χ y : ℝ)) : ℂ) * g y‖ ≤
      A * B * Real.exp (-(c * r ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (c / (2 * t))) ^ d := by
  have hb : 0 < c / (2 * t) := by positivity
  apply clr_integral_le_gaussian_mass _ x _ _ hb hmeas
  filter_upwards [hg] with y hgy
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hK x y)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  have hB : 0 ≤ B := (norm_nonneg _).trans hgy
  by_cases hy : euclideanNorm y ≤ r
  · rw [hχ y hy]
    simp only [sub_self, Complex.ofReal_zero, mul_zero, zero_mul, norm_zero]
    positivity
  · have hy' : r < euclideanNorm y := lt_of_not_ge hy
    have htri : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      have h := TimeChange.euclideanNorm_add_le (y - x) x
      simpa only [sub_add_cancel] using h
    have hs : euclideanNorm (y - x) = euclideanNorm (x - y) := by
      have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (x - y)
      simpa [neg_sub] using h
    rw [hs] at htri
    have hfar : r / 2 ≤ euclideanNorm (x - y) := by linarith
    have hsq : r ^ 2 / 4 ≤ euclideanNorm (x - y) ^ 2 := by
      have h0 : 0 ≤ r / 2 := by linarith
      nlinarith [pow_le_pow_left₀ h0 hfar 2]
    have hsplit : Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t)) ≤
        Real.exp (-(c * r ^ 2 / (8 * t))) *
          Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 : c * r ^ 2 / (8 * t) ≤ c * euclideanNorm (x - y) ^ 2 / (2 * t) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ c * (8 * t))]
      have h2 : c * euclideanNorm (x - y) ^ 2 / t =
          c * euclideanNorm (x - y) ^ 2 / (2 * t) +
            (c / (2 * t)) * euclideanNorm (x - y) ^ 2 := by
        field_simp
        ring
      rw [h2]
      linarith
    have hχ1 : ‖(((1 - χ y : ℝ)) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [(hχb y).1, (hχb y).2]
    calc ‖K x y * (((1 - χ y : ℝ)) : ℂ) * g y‖
        = ‖K x y‖ * ‖(((1 - χ y : ℝ)) : ℂ)‖ * ‖g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ (A * Real.exp (-(c * euclideanNorm (x - y) ^ 2 / t))) * 1 * B := by
          gcongr
          exact hK x y
      _ ≤ (A * (Real.exp (-(c * r ^ 2 / (8 * t))) *
            Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2))) * 1 * B := by
          gcongr
      _ = A * B * Real.exp (-(c * r ^ 2 / (8 * t))) *
            Real.exp (-(c / (2 * t)) * euclideanNorm (x - y) ^ 2) := by ring

/-- The actual endpoint orbit of bounded stationary data is the convolution with
an actual physical kernel carrying the point-kernel Gaussian bound. -/
theorem clr_forward_orbit_kernel
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange), HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ), 0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      ∃ (S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)))
        (K : ℝ≥0 → Vec d → Vec d → ℂ),
        IsPhysicalComplexSemigroup ω.1 i ζ S ∧
        IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag ∧
        IsPhysicalComplexKernel S Sdag K ∧
        (∀ x y, ‖K t x y‖ ≤ C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ x, Continuous (fun y => K t x y)) ∧
        (∀ᵐ y ∂volume, ‖f (translate y ω)‖ ≤ B) ∧
        ((fun x => (P t f) (translate x ω)) =ᵐ[volume]
          fun x => ∫ y, K t x y * f (translate y ω)) ∧
        (∀ x y (j : Fin d), ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ≤
          C * (2 + (t : ℝ)) ^ N *
            Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ))) ∧
        (∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
          (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
          Differentiable ℝ (fun x => ∫ y, K t x y * h y) ∧ ∀ x : Vec d,
            Integrable (fun y => K t x y * h y) ∧
            ∀ j : Fin d,
              Integrable (fun y => fderiv ℝ (fun z => K t z y) x (unitVector j) * h y) ∧
              fderiv ℝ (fun x => ∫ y, K t x y * h y) x (unitVector j) =
                ∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) * h y) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  set Λa : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity with hΛadef
  have hΛa : 1 ≤ Λa := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp (by linarith [D.one_le_ellipticity])
    rw [hΛadef]; nlinarith [D.one_le_ellipticity]
  obtain ⟨M, -, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  obtain ⟨C, c, N, hC, hc, hdet⟩ := clr_det_point_kernel_unit_all d hd Λa hΛa M
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ f B hB hf i ζ P hP t ht
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  obtain ⟨S, Sdag, hpair, _hm, hSm, _hSdagm⟩ :=
    crudeEnergy_ae_exists_measurable_physical_pair Q i ζ
  have hS := hpair.mono fun _ h => h.1
  obtain ⟨F, _hFm, hF, hconv⟩ :=
    crudeEnergy_exists_forward_cutoff_gaussian_approximation_allLp hP f S hS hSm
  let L : ℝ := 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3
  have happrox := hconv (t : ℝ) L (by linarith) (le_refl _)
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ, horbit, hpair, hF, happrox]
    with ω hellω hsmω hfω hpairω hFω haω
  obtain ⟨K, hK, hreg⟩ := hdet ω hellω hsmω i ζ (S ω) (Sdag ω) hpairω.1 hpairω.2
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hb := (hreg K (by simp) t ht).2.2
    (fun y => f (translate y ω)) B hB hfm hfω
  have hKb : ∀ x y, ‖K t x y‖ ≤ C * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := by
    intro x y
    have h := (hreg K (by simp) t ht).2.1 x y
    have h1 : 0 ≤ Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ^ 2) :=
      Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector j)‖ ^ 2) :=
      Real.sqrt_nonneg _
    linarith
  have hKc : ∀ x, Continuous (fun y => K t x y) := by
    intro x
    have hc2 := ((hreg K (by simp) t ht).1).continuous
    exact hc2.comp (continuous_const.prodMk continuous_id)
  have hKg : ∀ x y (j : Fin d), ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ≤
      C * (2 + (t : ℝ)) ^ N *
        Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * euclideanNorm (x - y) ^ 2 / (t : ℝ)) := by
    intro x y j
    have h := (hreg K (by simp) t ht).2.1 x y
    have hj : ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ≤
        Real.sqrt (∑ k : Fin d, ‖fderiv ℝ (fun z => K t z y) x (unitVector k)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun k _ => sq_nonneg
        ‖fderiv ℝ (fun z => K t z y) x (unitVector k)‖) (Finset.mem_univ j))
    have h1 : 0 ≤ ‖K t x y‖ := norm_nonneg _
    have h2 : 0 ≤ Real.sqrt (∑ k : Fin d, ‖fderiv ℝ (fun z => K t x z) y (unitVector k)‖ ^ 2) :=
      Real.sqrt_nonneg _
    linarith
  have hdat : ∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
      (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
      Differentiable ℝ (fun x => ∫ y, K t x y * h y) ∧ ∀ x : Vec d,
        Integrable (fun y => K t x y * h y) ∧
        ∀ j : Fin d,
          Integrable (fun y => fderiv ℝ (fun z => K t z y) x (unitVector j) * h y) ∧
          fderiv ℝ (fun x => ∫ y, K t x y * h y) x (unitVector j) =
            ∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) * h y := by
    intro h B' hB' hm hhB
    have hb' := (hreg K (by simp) t ht).2.2 h B' hB' hm hhB
    exact ⟨hb'.1, fun x => ⟨(hb'.2 x).1, fun j => (hb'.2 x).2.1 j⟩⟩
  refine ⟨S ω, Sdag ω, K, hpairω.1, hpairω.2, hK, hKb, hKc, hfω, ?_, hKg, hdat⟩
  apply crudeEnergy_physical_cutoff_kernel_identification hK
    (show 0 < t by exact_mod_cast (show (0 : ℝ) < t by linarith)) hFω
    (ae_of_all _ fun x => (hb.2 x).1) L
  · simpa using haω.1
  · simpa using haω.2

/-- Membership in the normalized unit ball in Euclidean-norm form. -/
theorem clr_mem_unit_ball {d : ℕ} {x : Vec d}
    (hx : x ∈ PDE.euclideanBall (0 : PDE.Vec d) 1) : euclideanNorm x < 1 := by
  have h := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num : (0 : ℝ) < 1)).1 hx
  simpa only [sub_zero, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
    euclideanNorm, euclideanSq, dot] using h

/-- For one environment: the orbit of bounded data minus the retained
evolution of its cut-off datum, on the unit ball. -/
theorem clr_forward_retained_orbit_error (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (S Sdag Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ S →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ Pr →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ Pr Prdag →
    ∀ (K : ℝ≥0 → Vec d → Vec d → ℂ), IsPhysicalComplexKernel S Sdag K →
    ∀ (t : ℝ≥0) (A k : ℝ), 1 ≤ (t : ℝ) → 0 < k →
      (∀ x y, ‖K t x y‖ ≤ A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) →
      (∀ x, Continuous (fun y => K t x y)) →
    ∀ (g : Vec d → ℂ) (B : ℝ), AEStronglyMeasurable g volume → (∀ᵐ y ∂volume, ‖g y‖ ≤ B) →
    ∀ (χ : Vec d → ℝ) (r : ℝ), 4 ≤ r → Continuous χ →
      (∀ y, euclideanNorm y ≤ r → χ y = 1) → (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) →
      (∀ x, euclideanNorm x < r → ω'.1 x = ω.1 x) →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun y => (χ y : ℂ) * g y) →
    ∀ o : Vec d → ℂ, o =ᵐ[volume] (fun x => ∫ y, K t x y * g y) →
      ∀ᵐ x ∂(volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) 1)),
        ‖o x - (Pr t fr) x‖ ≤
          A * B * Real.exp (-(k * r ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (k / (2 * t))) ^ d +
          C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖ := by
  obtain ⟨C, c, hC, hc, hpt⟩ := clr_retained_pointwise_all d Λ hΛ M M'
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag hS hSdag hPr hPrdag K hK
    t A k ht hk hKb hKc g B hg hgB χ r hr hχc hχ1 hχb hagree fr hfr o ho
  have htpos : 0 < (t : ℝ) := by linarith
  have ht0 : 0 < t := by exact_mod_cast htpos
  have htt : ((t : ℝ)).toNNReal = t := Real.toNNReal_coe
  obtain ⟨w, -, hwae, hwb⟩ := hpt ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag
    hS hSdag hPr hPrdag 0 r (by linarith) (fun x hx => hagree x (by simpa using hx))
    (t : ℝ) (by linarith) fr
  rw [htt] at hwae
  have hSk := (hK t ht0 fr).1.2
  have hsub := Lp.coeFn_sub (Pr t fr) (S t fr)
  have hmeasK (x : Vec d) : AEStronglyMeasurable (fun y => K t x y) volume :=
    (hKc x).aestronglyMeasurable
  have hgauss (x : Vec d) (h : Vec d → ℂ) (hh : AEStronglyMeasurable h volume)
      (hhB : ∀ᵐ y ∂volume, ‖h y‖ ≤ B) :
      Integrable (fun y => K t x y * h y) volume := by
    have hb : 0 < k / t := by positivity
    refine (clr_integral_le_gaussian_mass (fun y => K t x y * h y) x (A * B) (k / t) hb
      ((hmeasK x).mul hh) ?_).1
    filter_upwards [hhB] with y hy
    rw [norm_mul]
    have hA : 0 ≤ A := by
      have := (norm_nonneg _).trans (hKb x y)
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    have he : Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t)) =
        Real.exp (-(k / t) * euclideanNorm (x - y) ^ 2) := by
      congr 1; ring
    calc ‖K t x y‖ * ‖h y‖ ≤ (A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) * B :=
          mul_le_mul (hKb x y) hy (norm_nonneg _) (by positivity)
      _ = A * B * Real.exp (-(k / t) * euclideanNorm (x - y) ^ 2) := by rw [he]; ring
  have hχm : Measurable χ := hχc.measurable
  have hχg : AEStronglyMeasurable (fun y => (χ y : ℂ) * g y) volume :=
    (Complex.continuous_ofReal.comp hχc).aestronglyMeasurable.mul hg
  have hχgB : ∀ᵐ y ∂volume, ‖(χ y : ℂ) * g y‖ ≤ B := by
    filter_upwards [hgB] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb y).1]
    nlinarith [(hχb y).2, norm_nonneg (g y)]
  filter_upwards [ae_restrict_of_ae ho, ae_restrict_of_ae hwae, ae_restrict_of_ae hSk,
    ae_restrict_of_ae hsub, ae_restrict_mem (PDE.isOpen_euclideanBall _ _).measurableSet]
    with x hox hwx hSx hsx hxB
  have hx1 : euclideanNorm x < 1 := clr_mem_unit_ball hxB
  -- the far tail
  have hmeas_tail : AEStronglyMeasurable (fun y => K t x y * (((1 - χ y : ℝ)) : ℂ) * g y) volume :=
    ((hmeasK x).mul (Complex.continuous_ofReal.comp
      (continuous_const.sub hχc)).aestronglyMeasurable).mul hg
  obtain ⟨-, htail⟩ := clr_far_kernel_tail (fun x y => K t x y) g χ hk htpos
    (by linarith) hKb hgB hχ1 hχb x (by linarith) hmeas_tail
  -- the retained comparison
  have hwb' := hwb x (by simp only [sub_zero]; linarith)
  -- identities
  have hint1 := hgauss x g hg hgB
  have hint2 := hgauss x (fun y => (χ y : ℂ) * g y) hχg hχgB
  have hfrint : (∫ y, K t x y * fr y) = ∫ y, K t x y * ((χ y : ℂ) * g y) := by
    apply integral_congr_ae
    filter_upwards [hfr] with y hy
    rw [hy]
  have hdiff : (∫ y, K t x y * g y) - ∫ y, K t x y * ((χ y : ℂ) * g y) =
      ∫ y, K t x y * (((1 - χ y : ℝ)) : ℂ) * g y := by
    rw [← integral_sub hint1 hint2]
    congr 1
    funext y
    push_cast
    ring
  have hkey : o x - (Pr t fr) x =
      (∫ y, K t x y * (((1 - χ y : ℝ)) : ℂ) * g y) - w x := by
    have hw' : w x = (Pr t fr) x - (S t fr) x := by rw [hwx, hsx, Pi.sub_apply]
    rw [hw', hox, ← hdiff, hSx, hfrint]
    ring
  rw [hkey]
  refine (norm_sub_le _ _).trans ?_
  have hw0 : ‖w x‖ ≤ C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖ := by
    have h0 : 0 ≤ Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) := Real.sqrt_nonneg _
    linarith [hwb']
  exact add_le_add htail hw0

/-- The forward and clock endpoint data along the spatial orbit, in terms of the
actual coefficient field. -/
theorem clr_forward_clock_spatial_datum
    {d : ℕ} (hd : 2 ≤ d) (S : StructuralData d)
    (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ) (ν : Fin d ⊕ Unit) :
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (translate x ω) = match ν with
        | Sum.inl j =>
            ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
              (fun y => ω.1 y k j) x : ℝ) : ℂ) + ζ * (ω.1 x ⟨0, by omega⟩ j : ℂ))
        | Sum.inr _ => ζ * (ω.2 x : ℂ) := by
  intro f
  let := reducedLaw_probability Q
  cases ν with
  | inl j =>
      let f₀ : FieldPair d → ℂ := fun ω =>
        ((((1 / 2 : ℝ) * ∑ k : Fin d, coordinateDerivative k
          (fun y => ω.1 y k j) 0 : ℝ) : ℂ) + ζ * (ω.1 0 ⟨0, by omega⟩ j : ℂ))
      have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q] f₀ := by
        filter_upwards [Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
          Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j), hβ j, ha ⟨0, by omega⟩ j]
          with ω h1 h2 h3 h4
        change (β j + ζ • a ⟨0, by omega⟩ j : Lp ℂ 2 (reducedLaw Q)) ω = _
        rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4]
        rfl
      have hf₀ : Measurable f₀ := by
        have hdm (k : Fin d) : Measurable (fun ω : FieldPair d =>
            coordinateDerivative k (fun y => ω.1 y k j) 0) :=
          (measurable_fderiv_apply_const_with_param ℝ
            (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y k j)
            (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
              |>.matrix_elem k j) (unitVector k)).comp (measurable_id.prodMk measurable_const)
        exact (Complex.measurable_ofReal.comp
          ((Finset.measurable_sum _ fun k _ => hdm k).const_mul (1 / 2 : ℝ))).add
            ((by fun_prop : Measurable (fun ω : FieldPair d =>
              (ω.1 0 ⟨0, by omega⟩ j : ℂ))).const_mul ζ)
      filter_upwards [ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
        (Lp.stronglyMeasurable f).measurable hf₀ hf] with ω hω
      filter_upwards [hω] with x hx
      rw [hx]
      have hshift (k : Fin d) : coordinateDerivative k
          (fun y => (translate x ω).1 y k j) 0 =
            coordinateDerivative k (fun y => ω.1 y k j) x := by
        have hh := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : Vec d => ω.1 y k j)
          (x := (0 : Vec d)) x
        rw [add_zero] at hh
        exact congrArg (fun A : Vec d →L[ℝ] ℝ => A (unitVector k)) hh
      dsimp only [f₀]
      simp_rw [hshift]
      simp only [translate_matrix, add_zero]
  | inr u =>
      have hf : (f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (fun ω => ζ * (ω.2 0 : ℂ)) := by
        filter_upwards [Lp.coeFn_smul ζ μ, hμ] with ω h1 h2
        change (ζ • μ : Lp ℂ 2 (reducedLaw Q)) ω = _
        rw [h1, Pi.smul_apply, h2]
        rfl
      filter_upwards [ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
        (Lp.stronglyMeasurable f).measurable
        (by fun_prop : Measurable (fun ω : FieldPair d => ζ * (ω.2 0 : ℂ))) hf] with ω hω
      filter_upwards [hω] with x hx
      simpa only [translate_scalar, add_zero] using hx

/-- The L² size of bounded data cut off inside a ball of radius `2r`. -/
theorem clr_cutoff_data_norm_le {d : ℕ} (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    (χ : Vec d → ℝ) (g : Vec d → ℂ) {B r : ℝ} (hr : 0 < r)
    (hfr : (fr : Vec d → ℂ) =ᵐ[volume] fun y => (χ y : ℂ) * g y)
    (hg : ∀ᵐ y ∂volume, ‖g y‖ ≤ B) (hχb : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1)
    (hχ0 : ∀ y, 2 * r ≤ euclideanNorm y → χ y = 0) :
    ‖fr‖ ≤ B * Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * r ^ 2))) ^ d) := by
  have hb : 0 < 1 / (4 * r ^ 2) := by positivity
  have hB : 0 ≤ B := by
    obtain ⟨y, hy⟩ := hg.exists
    exact (norm_nonneg _).trans hy
  rw [← Calculus.S1.l2Size_lp fr]
  unfold Calculus.S1.l2Size
  have hmaj : ∀ᵐ y ∂volume, ‖fr y‖ ^ 2 ≤
      B ^ 2 * Real.exp 1 * Real.exp (-(1 / (4 * r ^ 2)) * euclideanNorm y ^ 2) := by
    filter_upwards [hfr, hg] with y hy hgy
    rw [hy, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb y).1]
    by_cases hyr : 2 * r ≤ euclideanNorm y
    · rw [hχ0 y hyr]
      simp only [zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
    · have hlt : euclideanNorm y < 2 * r := lt_of_not_ge hyr
      have hn0 : 0 ≤ euclideanNorm y := by unfold euclideanNorm; exact Real.sqrt_nonneg _
      have hsq : euclideanNorm y ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ hn0 hlt.le 2
      have hexp : 1 ≤ Real.exp 1 * Real.exp (-(1 / (4 * r ^ 2)) * euclideanNorm y ^ 2) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp
        have : (1 / (4 * r ^ 2)) * euclideanNorm y ^ 2 ≤ 1 := by
          rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
          nlinarith
        linarith
      have h1 : (χ y * ‖g y‖) ^ 2 ≤ B ^ 2 := by
        have h0 : 0 ≤ χ y * ‖g y‖ := mul_nonneg (hχb y).1 (norm_nonneg _)
        have h2 : χ y * ‖g y‖ ≤ B := by nlinarith [(hχb y).2, norm_nonneg (g y)]
        exact pow_le_pow_left₀ h0 h2 2
      calc (χ y * ‖g y‖) ^ 2 ≤ B ^ 2 * 1 := by rw [mul_one]; exact h1
        _ ≤ B ^ 2 * (Real.exp 1 * Real.exp (-(1 / (4 * r ^ 2)) * euclideanNorm y ^ 2)) :=
            mul_le_mul_of_nonneg_left hexp (sq_nonneg B)
        _ = _ := by ring
  have hint : Integrable (fun y : Vec d =>
      B ^ 2 * Real.exp 1 * Real.exp (-(1 / (4 * r ^ 2)) * euclideanNorm y ^ 2)) volume :=
    (clr_gaussian_integrable d _ hb).const_mul _
  have hle := integral_mono_ae ((Lp.memLp fr).integrable_norm_pow (by norm_num)) hint hmaj
  rw [integral_const_mul, clr_gaussian_integral] at hle
  calc Real.sqrt (∫ y, ‖fr y‖ ^ 2) ≤
        Real.sqrt (B ^ 2 * Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * r ^ 2))) ^ d) :=
        Real.sqrt_le_sqrt hle
    _ = B * Real.sqrt (Real.exp 1 * Real.sqrt (Real.pi / (1 / (4 * r ^ 2))) ^ d) := by
        rw [mul_assoc, Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

/-- A cutoff vanishing outside a Euclidean ball has compact support. -/
theorem clr_hasCompactSupport_of_ball {d : ℕ} (χ : Vec d → ℝ) (R : ℝ)
    (h : ∀ x, R ≤ euclideanNorm x → χ x = 0) : HasCompactSupport χ := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) (max R 0))
  intro x hx
  apply h
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have hle : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (by unfold euclideanNorm; exact Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    unfold euclideanNorm euclideanSq dot
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    have := Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
    simpa [sq] using this
  linarith [le_max_left R 0]

/-- Large-time locality of the forward and clock endpoints with bounded force,
with the explicit kernel-tail and retained-comparison error. -/
theorem clr_forward_clock_locality_raw
    (hcut : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ (C₁ c₁ C₂ c₂ B₀ : ℝ) (N₁ : ℕ), 1 ≤ C₁ ∧ 0 < c₁ ∧ 1 ≤ C₂ ∧ 0 < c₂ ∧ 0 < B₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, 40 ≤ ρ →
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖(P t f) ω - V ω‖ ≤ 2 *
        (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * B₀ *
            Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) *
            Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d +
          C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 10) ^ 2 / t) *
            (B₀ * Real.sqrt (Real.exp 1 *
              Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d))) := by
  obtain ⟨Λc, Mc, Kc, hΛc, -, χf, hχf, hret⟩ := hcut d D
  obtain ⟨C₁, c₁, N₁, hC₁, hc₁, hbridge⟩ := clr_forward_orbit_kernel d hd D
  obtain ⟨B₀, hB₀, hdata⟩ := crudeEnergy_initial_data_bound d hd D
  obtain ⟨M, -, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  set Λa : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity with hΛadef
  have hΛa : 1 ≤ Λa := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp (by linarith [D.one_le_ellipticity])
    rw [hΛadef]; nlinarith [D.one_le_ellipticity]
  set Λ : ℝ := max Λa Λc with hΛdef
  have hΛ : 1 ≤ Λ := hΛa.trans (le_max_left _ _)
  obtain ⟨C₂, c₂, hC₂, hc₂, herr1⟩ := clr_forward_retained_orbit_error d Λ hΛ M Mc
  refine ⟨C₁, c₁, C₂, c₂, B₀, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f t ht ρ hρ
  let := reducedLaw_probability Q
  set r : ℝ := ρ / 10 with hrdef
  have hr4 : 4 ≤ r := by rw [hrdef]; linarith
  have hr1 : 1 ≤ r := by linarith
  obtain ⟨hχs, hχb, hχone, hχzero, -⟩ := hχf 0 r hr1
  let χ : C(Vec d, ℝ) := ⟨χf 0 r, hχs.continuous⟩
  have hχone' : ∀ y, euclideanNorm y ≤ r → χ y = 1 := fun y hy =>
    hχone y (by simpa using hy)
  have hχzero' : ∀ y, 2 * r ≤ euclideanNorm y → χ y = 0 := fun y hy =>
    hχzero y (by simpa using hy)
  have hχb' : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := hχb
  have hcompact : HasCompactSupport χ := clr_hasCompactSupport_of_ball χ (2 * r) hχzero'
  obtain ⟨_, -, hcuts⟩ := short_time_compatible_euclidean_cutoffs d
  obtain ⟨-, θ, -, hθs, -, -, -, -, -, -, -, hθone, -, hθsupport, -, -⟩ :=
    hcuts ρ (by linarith)
  let U : Set (Vec d) := {x : Vec d | euclideanNorm x < ρ}
  let W : Set (Vec d) := {x : Vec d | euclideanNorm x < ρ / 2}
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  have hW : IsOpen W := isOpen_lt hnorm continuous_const
  have hχW : ∀ x, χ x ≠ 0 → x ∈ W := by
    intro x hx
    by_contra hxW
    apply hx
    apply hχzero'
    simp only [W, Set.mem_ofPred_eq, not_lt] at hxW
    linarith
  have hχU : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    apply hχzero'
    simp only [U, Set.mem_ofPred_eq, not_lt] at hx
    linarith
  obtain ⟨fr, -, hfrm, -, hefr, -⟩ := short_time_forward_clock_cutoff_measurable_evolution χ θ
    hcompact hθs U W hθsupport hW (fun x hx => hθone x hx.le) hχW Λ hΛ ⟨0, by omega⟩ ζ ν
  obtain ⟨Vf, hVm, hVact⟩ := clr_retained_measurable_pair_evolution χ U hχU Λ hΛ
    ⟨0, by omega⟩ ζ fr hfrm
  have hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) (fun ω => Vf ω t) := hVm.comp (measurable_id.prodMk measurable_const)
  have hfB : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B₀ := by
    obtain ⟨hv, -, hc⟩ := hdata Q hQ β a μ hβ ha hμ ζ hζ
    cases ν with
    | inl j => exact hv j
    | inr u => exact hc
  have hsp := clr_forward_clock_spatial_datum hd D Q hQ β a μ hβ ha hμ ζ ν
  have hε : 0 ≤ C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * B₀ *
            Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) *
            Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d +
          C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 10) ^ 2 / t) *
            (B₀ * Real.sqrt (Real.exp 1 *
              Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d)) := by positivity
  refine c25_local_observation_of_retained_spatial_bound Q ρ _ 1 hε one_pos (P t f)
    (P t f) (Lp.stronglyMeasurable _).measurable (ae_of_all _ fun _ => rfl)
    (fun ω => Vf ω t) hVt ?_
  filter_upwards [hbridge Q hQ f B₀ hB₀.le hfB ⟨0, by omega⟩ ζ P hP t ht, hret Q hQ,
    c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ, hsp] with ω hbr hretω hellω hsmω hspω
  obtain ⟨S, Sdag, K, hS, hSdag, hK, hKb, hKc, hgB, ho, -, -⟩ := hbr
  obtain ⟨ωloc, h1, h2, -, -, hellloc, -, hsmloc⟩ := hretω 0 r hr1
  have hloc : ωloc = ForcedLocality.retainedPair χ ω := by
    apply Prod.ext
    · ext x : 1
      rw [h1 x]
      rfl
    · ext x : 1
      rw [h2 x]
      rfl
  rw [hloc] at hellloc hsmloc
  have hellΛ : IsElliptic Λ ω.1 := Calculus.S1.isElliptic_mono (by linarith) (le_max_left _ _) hellω
  have hellΛr : IsElliptic Λ (ForcedLocality.retainedPair χ ω).1 :=
    Calculus.S1.isElliptic_mono (by linarith) (le_max_right _ _) hellloc
  have hgood : ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    fun x => s5Elliptic_of_isElliptic hΛ hellΛr x
  obtain ⟨Pr, Prdag, hPr, hPrdag, hVeq⟩ := hVact ω hgood
  have hfrχ : (fr ω : Vec d → ℂ) =ᵐ[volume] fun y => (χ y : ℂ) * f (translate y ω) := by
    filter_upwards [hefr ω hsmω.1, hspω] with x h1 h2
    rw [h1, h2]
    cases ν with
    | inl j => rfl
    | inr u => dsimp only [Sum.elim]; ring
  have hagree : ∀ x, euclideanNorm x < r → (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    fun x hx => (ForcedLocality.retainedPair_eq_at χ ω (hχone' x hx.le)).1
  have hgm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hKb' : ∀ x y, ‖K t x y‖ ≤ (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
      Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := by
    intro x y
    refine (hKb x y).trans (le_of_eq ?_)
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have hmain := herr1 ω (ForcedLocality.retainedPair χ ω) hellΛ hsmω hellΛr hsmloc
    ⟨0, by omega⟩ ζ S Sdag Pr Prdag hS hSdag hPr hPrdag K hK t _ c₁ ht hc₁ hKb' hKc
    (fun y => f (translate y ω)) B₀ hgm hgB χ r hr4 χ.continuous hχone' hχb' hagree
    (fr ω) hfrχ (fun x => (P t f) (translate x ω)) ho
  have hfrn := clr_cutoff_data_norm_le (fr ω) χ (fun y => f (translate y ω))
    (by linarith) hfrχ hgB hχb' hχzero'
  filter_upwards [hmain] with x hx
  rw [hVeq t]
  refine hx.trans ?_
  exact add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_left hfrn (by positivity))

/-- Minkowski's inequality for the Euclidean norm of nonnegative coordinates. -/
theorem clr_sqrt_sum_sq_add_le {d : ℕ} (a b : Fin d → ℝ) :
    Real.sqrt (∑ j, (a j + b j) ^ 2) ≤ Real.sqrt (∑ j, a j ^ 2) + Real.sqrt (∑ j, b j ^ 2) := by
  have hA : 0 ≤ ∑ j, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hB : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
  have hexp : ∑ j, (a j + b j) ^ 2 = ∑ j, a j ^ 2 + 2 * ∑ j, a j * b j + ∑ j, b j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsq : (Real.sqrt (∑ j, a j ^ 2) + Real.sqrt (∑ j, b j ^ 2)) ^ 2 =
      ∑ j, a j ^ 2 + 2 * (Real.sqrt (∑ j, a j ^ 2) * Real.sqrt (∑ j, b j ^ 2)) +
        ∑ j, b j ^ 2 := by
    rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]; ring
  calc Real.sqrt (∑ j, (a j + b j) ^ 2)
      ≤ Real.sqrt ((Real.sqrt (∑ j, a j ^ 2) + Real.sqrt (∑ j, b j ^ 2)) ^ 2) := by
        apply Real.sqrt_le_sqrt
        rw [hexp, hsq]
        linarith
    _ = _ := Real.sqrt_sq (by positivity)

/-- For one environment: the orbit minus the retained evolution is almost
everywhere a differentiable function with value and gradient bounds on the
ball of radius two. -/
theorem clr_forward_retained_orbit_C1_error (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (M M' : ℕ → ℝ) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (ω ω' : FieldPair d), IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      IsElliptic Λ ω'.1 → IsSmoothWithBounds M' ω' →
    ∀ (i : Fin d) (ζ : ℂ),
    ∀ (S Sdag Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 i ζ S →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag →
      IsPhysicalComplexSemigroup ω'.1 i ζ Pr →
      IsPhysicalComplexTransposeSemigroup ω'.1 i ζ Pr Prdag →
    ∀ (K : ℝ≥0 → Vec d → Vec d → ℂ), IsPhysicalComplexKernel S Sdag K →
    ∀ (t : ℝ≥0) (A k : ℝ), 1 ≤ (t : ℝ) → 0 < k →
      (∀ x y, ‖K t x y‖ ≤ A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) →
      (∀ x y (j : Fin d), ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ≤
        A * Real.exp (-(k * euclideanNorm (x - y) ^ 2 / t))) →
      (∀ (h : Vec d → ℂ) (B' : ℝ), 0 ≤ B' → AEStronglyMeasurable h volume →
        (∀ᵐ y ∂volume, ‖h y‖ ≤ B') →
        Differentiable ℝ (fun x => ∫ y, K t x y * h y) ∧ ∀ x : Vec d,
          Integrable (fun y => K t x y * h y) ∧
          ∀ j : Fin d,
            Integrable (fun y => fderiv ℝ (fun z => K t z y) x (unitVector j) * h y) ∧
            fderiv ℝ (fun x => ∫ y, K t x y * h y) x (unitVector j) =
              ∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) * h y) →
    ∀ (g : Vec d → ℂ) (B : ℝ), 0 ≤ B → AEStronglyMeasurable g volume →
      (∀ᵐ y ∂volume, ‖g y‖ ≤ B) →
    ∀ (χ : Vec d → ℝ) (r : ℝ), 6 ≤ r → Continuous χ →
      (∀ y, euclideanNorm y ≤ r → χ y = 1) → (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) →
      (∀ x, euclideanNorm x < r → ω'.1 x = ω.1 x) →
    ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun y => (χ y : ℂ) * g y) →
    ∀ o : Vec d → ℂ, o =ᵐ[volume] (fun x => ∫ y, K t x y * g y) →
    ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
      (fun x => o x - (Pr t fr) x) =ᵐ[volume] E ∧
      ∀ x, euclideanNorm x ≤ 2 →
        ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤
          (1 + d) * (A * B * Real.exp (-(k * r ^ 2 / (8 * t))) *
            Real.sqrt (Real.pi / (k / (2 * t))) ^ d) +
          C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖ := by
  obtain ⟨C, c, hC, hc, hpt⟩ := clr_retained_pointwise_all d Λ hΛ M M'
  refine ⟨C, c, hC, hc, ?_⟩
  intro ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag hS hSdag hPr hPrdag K hK
    t A k ht hk hKb hKg hdat g B hB hg hgB χ r hr hχc hχ1 hχb hagree fr hfr o ho
  have htpos : 0 < (t : ℝ) := by linarith
  have ht0 : 0 < t := by exact_mod_cast htpos
  have htt : ((t : ℝ)).toNNReal = t := Real.toNNReal_coe
  obtain ⟨w, hwC1, hwae, hwb⟩ := hpt ω ω' hell hsmooth hell' hsmooth' i ζ S Sdag Pr Prdag
    hS hSdag hPr hPrdag 0 r (by linarith) (fun x hx => hagree x (by simpa using hx))
    (t : ℝ) (by linarith) fr
  rw [htt] at hwae
  have hwd : Differentiable ℝ w := hwC1.differentiable one_ne_zero
  have hχg : AEStronglyMeasurable (fun y => (χ y : ℂ) * g y) volume :=
    (Complex.continuous_ofReal.comp hχc).aestronglyMeasurable.mul hg
  have hχgB : ∀ᵐ y ∂volume, ‖(χ y : ℂ) * g y‖ ≤ B := by
    filter_upwards [hgB] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hχb y).1]
    nlinarith [(hχb y).2, norm_nonneg (g y)]
  have h1χ : AEStronglyMeasurable (fun y => (((1 - χ y : ℝ)) : ℂ) * g y) volume :=
    (Complex.continuous_ofReal.comp (continuous_const.sub hχc)).aestronglyMeasurable.mul hg
  have h1χB : ∀ᵐ y ∂volume, ‖(((1 - χ y : ℝ)) : ℂ) * g y‖ ≤ B := by
    filter_upwards [hgB] with y hy
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [(hχb y).2])]
    nlinarith [(hχb y).1, norm_nonneg (g y)]
  obtain ⟨hdg, hig⟩ := hdat g B hB hg hgB
  obtain ⟨hdχ, hiχ⟩ := hdat (fun y => (χ y : ℂ) * g y) B hB hχg hχgB
  obtain ⟨-, hi1⟩ := hdat (fun y => (((1 - χ y : ℝ)) : ℂ) * g y) B hB h1χ h1χB
  set ug : Vec d → ℂ := fun x => ∫ y, K t x y * g y with hugdef
  set uχ : Vec d → ℂ := fun x => ∫ y, K t x y * ((χ y : ℂ) * g y) with huχdef
  let T : Vec d → ℂ := fun x => ug x - uχ x
  have hTd : Differentiable ℝ T := hdg.sub hdχ
  -- the tail and its derivative as kernel integrals of the far datum
  have hTval (x : Vec d) : T x = ∫ y, K t x y * ((((1 - χ y : ℝ)) : ℂ) * g y) := by
    change (∫ y, K t x y * g y) - (∫ y, K t x y * ((χ y : ℂ) * g y)) = _
    rw [← integral_sub (hig x).1 (hiχ x).1]
    congr 1; funext y; push_cast; ring
  have hTder (x : Vec d) (j : Fin d) : fderiv ℝ T x (unitVector j) =
      ∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) * ((((1 - χ y : ℝ)) : ℂ) * g y) := by
    change fderiv ℝ (fun x => ug x - uχ x) x (unitVector j) = _
    have hfun : (fun x => ug x - uχ x) = ug - uχ := rfl
    rw [hfun, fderiv_sub (hdg x) (hdχ x), sub_apply, ((hig x).2 j).2,
      ((hiχ x).2 j).2, ← integral_sub ((hig x).2 j).1 ((hiχ x).2 j).1]
    congr 1; funext y; push_cast; ring
  refine ⟨fun x => T x - w x, hTd.sub hwd, ?_, ?_⟩
  · have hSk := (hK t ht0 fr).1.2
    have hsub := Lp.coeFn_sub (Pr t fr) (S t fr)
    filter_upwards [ho, hwae, hSk, hsub] with x hox hwx hSx hsx
    have hfrint : (∫ y, K t x y * fr y) = ∫ y, K t x y * ((χ y : ℂ) * g y) := by
      apply integral_congr_ae
      filter_upwards [hfr] with y hy
      rw [hy]
    have hw' : w x = (Pr t fr) x - (S t fr) x := by rw [hwx, hsx, Pi.sub_apply]
    change o x - (Pr t fr) x = (ug x - uχ x) - w x
    rw [hw', hox, hSx, hfrint]
    ring
  · intro x hx
    have hx' : euclideanNorm x ≤ r / 2 := by linarith
    have hmeas0 : AEStronglyMeasurable
        (fun y => K t x y * (((1 - χ y : ℝ)) : ℂ) * g y) volume := by
      have := (hi1 x).1.aestronglyMeasurable
      simpa only [mul_assoc] using this
    obtain ⟨-, htail⟩ := clr_far_kernel_tail (fun x y => K t x y) g χ hk htpos
      (by linarith) hKb hgB hχ1 hχb x hx' hmeas0
    set τ := A * B * Real.exp (-(k * r ^ 2 / (8 * t))) * Real.sqrt (Real.pi / (k / (2 * t))) ^ d
      with hτdef
    have hτ0 : 0 ≤ τ := (norm_nonneg _).trans htail
    have hTx : ‖T x‖ ≤ τ := by
      rw [hTval]
      simpa only [mul_assoc] using htail
    have hTj (j : Fin d) : ‖fderiv ℝ T x (unitVector j)‖ ≤ τ := by
      rw [hTder]
      have hmeasj : AEStronglyMeasurable
          (fun y => fderiv ℝ (fun z => K t z y) x (unitVector j) *
            (((1 - χ y : ℝ)) : ℂ) * g y) volume := by
        have := ((hi1 x).2 j).1.aestronglyMeasurable
        simpa only [mul_assoc] using this
      obtain ⟨-, h⟩ := clr_far_kernel_tail
        (fun x y => fderiv ℝ (fun z => K t z y) x (unitVector j)) g χ hk htpos
        (by linarith) (fun x y => hKg x y j) hgB hχ1 hχb x hx' hmeasj
      rw [← hτdef] at h
      calc ‖∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) *
            ((((1 - χ y : ℝ)) : ℂ) * g y)‖
          = ‖∫ y, fderiv ℝ (fun z => K t z y) x (unitVector j) *
              (((1 - χ y : ℝ)) : ℂ) * g y‖ := by simp only [mul_assoc]
        _ ≤ τ := h
    have hwx := hwb x (by simp only [sub_zero]; linarith)
    set Wb := C * (2 + (t : ℝ)) * Real.exp (C * ‖ζ‖ ^ 2 * t - c * r ^ 2 / t) * ‖fr‖
    have hTg : Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ d * τ := by
      have h2 : (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ (d * τ) ^ 2 := by
        calc (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ ∑ _j : Fin d, τ ^ 2 :=
              Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hTj j) 2
          _ = d * τ ^ 2 := by simp
          _ ≤ (d * τ) ^ 2 := by
              rcases Nat.eq_zero_or_pos d with h | h
              · simp [h]
              · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast h
                nlinarith [sq_nonneg τ]
      calc Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) ≤ Real.sqrt ((d * τ) ^ 2) :=
            Real.sqrt_le_sqrt h2
        _ = d * τ := Real.sqrt_sq (by positivity)
    have hderE (j : Fin d) : fderiv ℝ (fun x => T x - w x) x (unitVector j) =
        fderiv ℝ T x (unitVector j) - fderiv ℝ w x (unitVector j) := by
      have hfun : (fun x => T x - w x) = T - w := rfl
      rw [hfun, fderiv_sub (hTd x) (hwd x), sub_apply]
    have hgradE : Real.sqrt (∑ j, ‖fderiv ℝ (fun x => T x - w x) x (unitVector j)‖ ^ 2) ≤
        Real.sqrt (∑ j, ‖fderiv ℝ T x (unitVector j)‖ ^ 2) +
          Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2) := by
      refine le_trans ?_ (clr_sqrt_sum_sq_add_le (fun j => ‖fderiv ℝ T x (unitVector j)‖)
        (fun j => ‖fderiv ℝ w x (unitVector j)‖))
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro j _
      rw [hderE]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    have hval : ‖T x - w x‖ ≤ τ + ‖w x‖ := (norm_sub_le _ _).trans (by linarith)
    have hτd : τ + d * τ = (1 + d) * τ := by ring
    calc ‖T x - w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ (fun x => T x - w x) x (unitVector j)‖ ^ 2)
        ≤ (τ + ‖w x‖) + (d * τ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2)) := by
          linarith [hgradE, hTg]
      _ = (1 + d) * τ + (‖w x‖ + Real.sqrt (∑ j, ‖fderiv ℝ w x (unitVector j)‖ ^ 2)) := by
          ring
      _ ≤ (1 + d) * τ + Wb := by linarith [hwx]

/-- Bounds of the initial data at every force. -/
theorem clr_initial_data_bound_all (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      (∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q,
        ‖(β j + ζ • a ⟨0, by omega⟩ j) ω‖ ≤ B * (1 + ‖ζ‖)) ∧
      (∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q, ‖β j ω‖ ≤ B) ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖(ζ • μ) ω‖ ≤ B * (1 + ‖ζ‖)) := by
  obtain ⟨K, hK, hb⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨K, hK, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ
  obtain ⟨hβb, hab, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  refine ⟨fun j => ?_, hβb, ?_⟩
  · filter_upwards [hβb j, hab ⟨0, by omega⟩ j,
      Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
      Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j)] with ω hβω haω hadd hsmul
    simp only [Pi.add_apply, Pi.smul_apply] at hadd hsmul
    rw [hadd, hsmul]
    calc
      _ ≤ ‖β j ω‖ + ‖ζ • a ⟨0, by omega⟩ j ω‖ := norm_add_le _ _
      _ = ‖β j ω‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ j ω‖ := by rw [norm_smul]
      _ ≤ K + ‖ζ‖ * K := add_le_add hβω (mul_le_mul_of_nonneg_left haω (norm_nonneg _))
      _ = K * (1 + ‖ζ‖) := by ring
  · filter_upwards [hμb, Lp.coeFn_smul ζ μ] with ω hω hsmul
    simp only [Pi.smul_apply] at hsmul
    rw [hsmul, norm_smul]
    have := mul_le_mul_of_nonneg_left hω (norm_nonneg ζ)
    nlinarith

/-- The locally measurable retained family of the forward and clock endpoints
with bounded force at large time, and the differentiable error of the actual
orbit on the ball of radius two. -/
theorem clr_forward_clock_retained_family
    (hcut : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ (C₁ c₁ C₂ c₂ B₀ : ℝ) (N₁ : ℕ), 1 ≤ C₁ ∧ 0 < c₁ ∧ 1 ≤ C₂ ∧ 0 < c₂ ∧ 0 < B₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, 60 ≤ ρ →
    ∃ Vt : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
        (borel _) Vt ∧
      ∀ᵐ ω ∂reducedLaw Q, ∃ E : Vec d → ℂ, Differentiable ℝ E ∧
        (fun x => (P t f) (translate x ω) - Vt ω x) =ᵐ[volume] E ∧
        ∀ x, euclideanNorm x ≤ 2 →
          ‖E x‖ + Real.sqrt (∑ j, ‖fderiv ℝ E x (unitVector j)‖ ^ 2) ≤
            (1 + d) * (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * (B₀ * (1 + ‖ζ‖)) *
              Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) *
              Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
            C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 10) ^ 2 / t) *
              (B₀ * (1 + ‖ζ‖) * Real.sqrt (Real.exp 1 *
                Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d)) := by
  obtain ⟨Λc, Mc, Kc, hΛc, -, χf, hχf, hret⟩ := hcut d D
  obtain ⟨C₁, c₁, N₁, hC₁, hc₁, hbridge⟩ := clr_forward_orbit_kernel d hd D
  obtain ⟨B₀, hB₀, hdata⟩ := clr_initial_data_bound_all d hd D
  obtain ⟨M, -, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  set Λa : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity with hΛadef
  have hΛa : 1 ≤ Λa := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) :=
      Real.one_le_exp (by linarith [D.one_le_ellipticity])
    rw [hΛadef]; nlinarith [D.one_le_ellipticity]
  set Λ : ℝ := max Λa Λc with hΛdef
  have hΛ : 1 ≤ Λ := hΛa.trans (le_max_left _ _)
  obtain ⟨C₂, c₂, hC₂, hc₂, herr1⟩ := clr_forward_retained_orbit_C1_error d Λ hΛ M Mc
  refine ⟨C₁, c₁, C₂, c₂, B₀, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P hP ν f t ht ρ hρ
  set B₁ : ℝ := B₀ * (1 + ‖ζ‖) with hB₁def
  have hB₁ : 0 < B₁ := by positivity
  let := reducedLaw_probability Q
  set r : ℝ := ρ / 10 with hrdef
  have hr4 : 6 ≤ r := by rw [hrdef]; linarith
  have hr1 : 1 ≤ r := by linarith
  obtain ⟨hχs, hχb, hχone, hχzero, -⟩ := hχf 0 r hr1
  let χ : C(Vec d, ℝ) := ⟨χf 0 r, hχs.continuous⟩
  have hχone' : ∀ y, euclideanNorm y ≤ r → χ y = 1 := fun y hy =>
    hχone y (by simpa using hy)
  have hχzero' : ∀ y, 2 * r ≤ euclideanNorm y → χ y = 0 := fun y hy =>
    hχzero y (by simpa using hy)
  have hχb' : ∀ y, 0 ≤ χ y ∧ χ y ≤ 1 := hχb
  have hcompact : HasCompactSupport χ := clr_hasCompactSupport_of_ball χ (2 * r) hχzero'
  obtain ⟨_, -, hcuts⟩ := short_time_compatible_euclidean_cutoffs d
  obtain ⟨-, θ, -, hθs, -, -, -, -, -, -, -, hθone, -, hθsupport, -, -⟩ :=
    hcuts ρ (by linarith)
  let U : Set (Vec d) := {x : Vec d | euclideanNorm x < ρ}
  let W : Set (Vec d) := {x : Vec d | euclideanNorm x < ρ / 2}
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun k _ => (continuous_apply k).mul (continuous_apply k))
  have hW : IsOpen W := isOpen_lt hnorm continuous_const
  have hχW : ∀ x, χ x ≠ 0 → x ∈ W := by
    intro x hx
    by_contra hxW
    apply hx
    apply hχzero'
    simp only [W, Set.mem_ofPred_eq, not_lt] at hxW
    linarith
  have hχU : ∀ x, x ∉ U → χ x = 0 := by
    intro x hx
    apply hχzero'
    simp only [U, Set.mem_ofPred_eq, not_lt] at hx
    linarith
  obtain ⟨fr, -, hfrm, -, hefr, -⟩ := short_time_forward_clock_cutoff_measurable_evolution χ θ
    hcompact hθs U W hθsupport hW (fun x hx => hθone x hx.le) hχW Λ hΛ ⟨0, by omega⟩ ζ ν
  obtain ⟨Vf, hVm, hVact⟩ := clr_retained_measurable_pair_evolution χ U hχU Λ hΛ
    ⟨0, by omega⟩ ζ fr hfrm
  have hVt : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) (fun ω => Vf ω t) := hVm.comp (measurable_id.prodMk measurable_const)
  have hfB : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B₁ := by
    obtain ⟨hv, -, hc⟩ := hdata Q hQ β a μ hβ ha hμ ζ
    cases ν with
    | inl j => exact hv j
    | inr u => exact hc
  have hsp := clr_forward_clock_spatial_datum hd D Q hQ β a μ hβ ha hμ ζ ν
  refine ⟨fun ω => Vf ω t, hVt, ?_⟩
  filter_upwards [hbridge Q hQ f B₁ hB₁.le hfB ⟨0, by omega⟩ ζ P hP t ht, hret Q hQ,
    c4_ae_reduced_physical_elliptic Q, hsmooth Q hQ, hsp] with ω hbr hretω hellω hsmω hspω
  obtain ⟨S, Sdag, K, hS, hSdag, hK, hKb, hKc, hgB, ho, hKg, hdat⟩ := hbr
  obtain ⟨ωloc, h1, h2, -, -, hellloc, -, hsmloc⟩ := hretω 0 r hr1
  have hloc : ωloc = ForcedLocality.retainedPair χ ω := by
    apply Prod.ext
    · ext x : 1
      rw [h1 x]
      rfl
    · ext x : 1
      rw [h2 x]
      rfl
  rw [hloc] at hellloc hsmloc
  have hellΛ : IsElliptic Λ ω.1 :=
    Calculus.S1.isElliptic_mono (by linarith) (le_max_left _ _) hellω
  have hellΛr : IsElliptic Λ (ForcedLocality.retainedPair χ ω).1 :=
    Calculus.S1.isElliptic_mono (by linarith) (le_max_right _ _) hellloc
  have hgood : ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ :=
    fun x => s5Elliptic_of_isElliptic hΛ hellΛr x
  obtain ⟨Pr, Prdag, hPr, hPrdag, hVeq⟩ := hVact ω hgood
  have hfrχ : (fr ω : Vec d → ℂ) =ᵐ[volume] fun y => (χ y : ℂ) * f (translate y ω) := by
    filter_upwards [hefr ω hsmω.1, hspω] with x h1 h2
    rw [h1, h2]
    cases ν with
    | inl j => rfl
    | inr u => dsimp only [Sum.elim]; ring
  have hagree : ∀ x, euclideanNorm x < r → (ForcedLocality.retainedPair χ ω).1 x = ω.1 x :=
    fun x hx => (ForcedLocality.retainedPair_eq_at χ ω (hχone' x hx.le)).1
  have hgm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hexp (x y : Vec d) : C₁ * (2 + (t : ℝ)) ^ N₁ *
      Real.exp (C₁ * ‖ζ‖ ^ 2 * (t : ℝ) - c₁ * euclideanNorm (x - y) ^ 2 / (t : ℝ)) =
      (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
        Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := by
    rw [sub_eq_add_neg, Real.exp_add]
    ring
  have hKb' : ∀ x y, ‖K t x y‖ ≤ (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
      Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := fun x y =>
    (hKb x y).trans (le_of_eq (hexp x y))
  have hKg' : ∀ x y (j : Fin d), ‖fderiv ℝ (fun z => K t z y) x (unitVector j)‖ ≤
      (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t)) *
        Real.exp (-(c₁ * euclideanNorm (x - y) ^ 2 / t)) := fun x y j =>
    (hKg x y j).trans (le_of_eq (hexp x y))
  obtain ⟨E, hEd, hEae, hEb⟩ := herr1 ω (ForcedLocality.retainedPair χ ω) hellΛ hsmω hellΛr
    hsmloc ⟨0, by omega⟩ ζ S Sdag Pr Prdag hS hSdag hPr hPrdag K hK t _ c₁ ht hc₁ hKb' hKg'
    hdat (fun y => f (translate y ω)) B₁ hB₁.le hgm hgB χ r hr4 χ.continuous hχone' hχb'
    hagree (fr ω) hfrχ (fun x => (P t f) (translate x ω)) ho
  have hfrn := clr_cutoff_data_norm_le (fr ω) χ (fun y => f (translate y ω))
    (by linarith) hfrχ hgB hχb' hχzero'
  refine ⟨E, hEd, ?_, ?_⟩
  · simpa only [hVeq t] using hEae
  · intro x hx
    refine (hEb x hx).trans ?_
    exact add_le_add (le_of_eq rfl) (mul_le_mul_of_nonneg_left hfrn (by positivity))

/-- A limsup squeezed between two sequences with a common limit. -/
theorem clr_real_limsup_error {a b : ℕ → ℝ} {l ε : ℝ}
    (ha : Tendsto a atTop (𝓝 l)) (hab : ∀ n, |a n - b n| ≤ ε) :
    |l - limsup b atTop| ≤ ε := by
  have hlo : (fun n => a n - ε) ≤ᶠ[atTop] b :=
    Eventually.of_forall fun n => by have h := (abs_le.mp (hab n)).2; linarith
  have hhi : b ≤ᶠ[atTop] (fun n => a n + ε) :=
    Eventually.of_forall fun n => by have h := (abs_le.mp (hab n)).1; linarith
  have htl := ha.sub_const ε
  have htu := ha.add_const ε
  have hbb := htu.isBoundedUnder_le.mono_le hhi
  have hbl := htl.isBoundedUnder_ge.mono_ge hlo
  have hl := limsup_le_limsup hlo htl.isCoboundedUnder_le hbb
  have hu := limsup_le_limsup hhi hbl.isCoboundedUnder_le htu.isBoundedUnder_le
  rw [htl.limsup_eq] at hl
  rw [htu.limsup_eq] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Local approximations of an L²-convergent sequence give a local
approximation of the limit, with the error doubled. -/
theorem clr_local_observation_of_tendsto {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (ρ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (f : Lp ℂ 2 (reducedLaw Q))
    (F : ℕ → Lp ℂ 2 (reducedLaw Q)) (hF : Tendsto F atTop (𝓝 f))
    (hloc : ∀ n, ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖F n ω - V ω‖ ≤ ε) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖f ω - V ω‖ ≤ 2 * ε := by
  let := reducedLaw_probability Q
  choose V hVloc hVe using hloc
  choose A hA hAe using hVloc
  have hm : TendstoInMeasure (reducedLaw Q) (fun n => (F n : FieldPair d → ℂ)) atTop f := by
    exact tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hF)
  obtain ⟨φ, -, hconv⟩ := hm.exists_seq_tendsto_ae
  let v : FieldPair d → ℂ := fun ω =>
    (limsup (fun n => (A (φ n) ω).re) atTop : ℝ) +
      (limsup (fun n => (A (φ n) ω).im) atTop : ℝ) * Complex.I
  have hvloc : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] v :=
    (Complex.measurable_ofReal.comp
      (.limsup fun n => Complex.measurable_re.comp (hA (φ n)))).add
      ((Complex.measurable_ofReal.comp
        (.limsup fun n => Complex.measurable_im.comp (hA (φ n)))).mul measurable_const)
  have hvm : Measurable v := hvloc.mono (Probability.localSigma_le_borel _) le_rfl
  have herrall : ∀ᵐ ω ∂reducedLaw Q, ∀ n, ‖F n ω - A n ω‖ ≤ ε := by
    rw [ae_all_iff]
    intro n
    filter_upwards [hVe n, hAe n] with ω h1 h2
    rw [h2]
    exact h1
  have he : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - v ω‖ ≤ 2 * ε := by
    filter_upwards [hconv, herrall] with ω hc hb
    have hre := clr_real_limsup_error
      ((Complex.continuous_re.tendsto (f ω)).comp hc) (fun n =>
        (Complex.abs_re_le_norm (F (φ n) ω - A (φ n) ω)).trans (hb (φ n)))
    have him := clr_real_limsup_error
      ((Complex.continuous_im.tendsto (f ω)).comp hc) (fun n =>
        (Complex.abs_im_le_norm (F (φ n) ω - A (φ n) ω)).trans (hb (φ n)))
    have hre' : |(f ω - v ω).re| ≤ ε := by simpa [v] using hre
    have him' : |(f ω - v ω).im| ≤ ε := by simpa [v] using him
    calc
      ‖f ω - v ω‖ ≤ |(f ω - v ω).re| + |(f ω - v ω).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ε + |ε| := add_le_add hre' (him'.trans (le_abs_self ε))
      _ = 2 * ε := by rw [abs_of_nonneg hε]; ring
  have hdiff : MemLp (fun ω => f ω - v ω) 2 (reducedLaw Q) :=
    MemLp.of_bound ((Lp.stronglyMeasurable f).measurable.sub hvm).aestronglyMeasurable
      (2 * ε) he
  have hmem : MemLp v 2 (reducedLaw Q) := by
    convert (Lp.memLp f).sub hdiff using 1
    funext ω
    simp only [Pi.sub_apply, sub_sub_cancel]
  refine ⟨hmem.toLp v, ⟨v, hvloc, hmem.coeFn_toLp.symm⟩, ?_⟩
  filter_upwards [he, hmem.coeFn_toLp] with ω hω heω
  simpa only [heω] using hω

/-- Mean value bound along a coordinate line inside the ball of radius two. -/
theorem clr_coordinate_increment_le {d : ℕ} {E : Vec d → ℂ} (hE : Differentiable ℝ E)
    (j : Fin d) {ε : ℝ}
    (hb : ∀ y, euclideanNorm y ≤ 2 → ‖fderiv ℝ E y (unitVector j)‖ ≤ ε)
    {x : Vec d} (hx : euclideanNorm x ≤ 1) {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ‖E (x + h • unitVector j) - E x‖ ≤ ε * h := by
  let γ : ℝ → ℂ := fun s => E (x + s • unitVector j)
  have hγ (s : ℝ) : HasDerivAt γ (fderiv ℝ E (x + s • unitVector j) (unitVector j)) s := by
    have hline := (((hasDerivAt_id s).smul_const (unitVector j)).const_add x)
    simpa only [Function.comp_def, id_eq, one_smul] using
      (hE (x + s • unitVector j)).hasFDerivAt.comp_hasDerivAt s hline
  have hbd : ∀ s ∈ Set.Ico (0 : ℝ) h,
      ‖fderiv ℝ E (x + s • unitVector j) (unitVector j)‖ ≤ ε := by
    intro s hs
    apply hb
    have htri := TimeChange.euclideanNorm_add_le x (s • unitVector j)
    rw [TimeChange.euclideanNorm_smul, euclideanNorm_unitVector, abs_of_nonneg hs.1] at htri
    linarith [hs.2]
  have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := γ) (a := 0) (b := h)
    (fun s _ => (hγ s).hasDerivWithinAt) hbd h ⟨h0, le_rfl⟩
  simpa [γ] using hmv

/-- Large-time gradient locality of the forward and clock endpoints with bounded
force: every component of an actual horizontal gradient has a local
approximation with the error of the retained family. -/
theorem clr_forward_clock_gradient_locality_raw
    (hcut : node_l_u3A_forced_u2D_local_u23_cutoff_u2D_environmentStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ (C₁ c₁ C₂ c₂ B₀ : ℝ) (N₁ : ℕ), 1 ≤ C₁ ∧ 0 < c₁ ∧ 1 ≤ C₂ ∧ 0 < c₂ ∧ 0 < B₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ∀ ρ : ℝ, 60 ≤ ρ →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G →
    ∀ j : Fin d, ∃ H : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ H ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖G j ω - H ω‖ ≤ 2 * (2 *
        ((1 + d) * (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * (B₀ * (1 + ‖ζ‖)) *
              Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) *
              Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
            C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 10) ^ 2 / t) *
              (B₀ * (1 + ‖ζ‖) * Real.sqrt (Real.exp 1 *
                Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d)))) := by
  obtain ⟨C₁, c₁, C₂, c₂, B₀, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, hfam⟩ :=
    clr_forward_clock_retained_family hcut d hd D
  refine ⟨C₁, c₁, C₂, c₂, B₀, N₁, hC₁, hc₁, hC₂, hc₂, hB₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P hP ν f t ht ρ hρ G hG j
  let := reducedLaw_probability Q
  obtain ⟨Vt, hVt, hE⟩ := hfam Q hQ β a μ hβ ha hμ ζ P hP ν t ht ρ hρ
  set εF : ℝ := (1 + d) * (C₁ * (2 + (t : ℝ)) ^ N₁ * Real.exp (C₁ * ‖ζ‖ ^ 2 * t) * (B₀ * (1 + ‖ζ‖)) *
              Real.exp (-(c₁ * (ρ / 10) ^ 2 / (8 * t))) *
              Real.sqrt (Real.pi / (c₁ / (2 * t))) ^ d) +
            C₂ * (2 + (t : ℝ)) * Real.exp (C₂ * ‖ζ‖ ^ 2 * t - c₂ * (ρ / 10) ^ 2 / t) *
              (B₀ * (1 + ‖ζ‖) * Real.sqrt (Real.exp 1 *
                Real.sqrt (Real.pi / (1 / (4 * (ρ / 10) ^ 2))) ^ d)) with hεFdef
  have hεF : 0 ≤ εF := by positivity
  set hs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2) with hsdef
  have hspos (n : ℕ) : 0 < hs n := by simp only [hsdef]; positivity
  have hsle (n : ℕ) : hs n ≤ 1 := by
    simp only [hsdef]
    rw [div_le_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have hstend : Tendsto hs atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
      exact (tendsto_const_nhds (x := (1 : ℝ))).div_atTop hden
    · exact Eventually.of_forall fun n => ne_of_gt (hspos n)
  let Qs := reducedLaw_stationary Q
  let U : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n =>
    ((hs n : ℝ) : ℂ)⁻¹ • (complexTranslation (reducedLaw Q) Qs (hs n • unitVector j) (P t f) -
      P t f)
  have hUlim : Tendsto U atTop (𝓝 (G j)) := (hG j).comp hstend
  have h2ε : 0 ≤ 2 * εF := by positivity
  apply clr_local_observation_of_tendsto Q ρ h2ε (G j) U hUlim
  intro n
  set h := hs n with hhdef
  have hh0 : 0 < h := hspos n
  have hh1 : h ≤ 1 := hsle n
  have hmp := measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector j)
  let Tl : Lp ℂ 2 (volume : Measure (Vec d)) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
    Lp.compMeasurePreservingₗᵢ (p := 2) ℂ (fun x : Vec d => x + h • unitVector j) hmp
  let Vn : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
    ((h : ℝ) : ℂ)⁻¹ • (Tl (Vt ω) - Vt ω)
  have hVn : @Measurable _ _ (EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ})
      (borel _) Vn := by
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
    have hc0 : Continuous (fun L : Lp ℂ 2 (volume : Measure (Vec d)) => Tl L - L) :=
      Tl.continuous.sub continuous_id
    have hc : Continuous (fun L : Lp ℂ 2 (volume : Measure (Vec d)) =>
        ((h : ℝ) : ℂ)⁻¹ • (Tl L - L)) := hc0.const_smul (((h : ℝ) : ℂ)⁻¹)
    exact hc.measurable.comp hVt
  let F0 : FieldPair d → ℂ := fun ω => (P t f) ω
  have hF0 : Measurable F0 := (Lp.stronglyMeasurable _).measurable
  let Fn : FieldPair d → ℂ := fun ω =>
    ((h : ℝ) : ℂ)⁻¹ * (F0 (translate (h • unitVector j) ω) - F0 ω)
  have hFn : Measurable Fn := by
    apply Measurable.const_mul
    exact (hF0.comp (Probability.continuous_translate.measurable.comp
      (measurable_const.prodMk measurable_id))).sub hF0
  have heFn : Fn =ᵐ[reducedLaw Q] (U n : FieldPair d → ℂ) := by
    filter_upwards [Lp.coeFn_smul (((h : ℝ) : ℂ)⁻¹)
        (complexTranslation (reducedLaw Q) Qs (h • unitVector j) (P t f) - P t f),
      Lp.coeFn_sub (complexTranslation (reducedLaw Q) Qs (h • unitVector j) (P t f)) (P t f),
      coeFn_complexTranslation (reducedLaw Q) Qs (h • unitVector j) (P t f)] with ω h1 h2 h3
    change Fn ω = (((h : ℝ) : ℂ)⁻¹ • (complexTranslation (reducedLaw Q) Qs (h • unitVector j)
      (P t f) - P t f)) ω
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3]
    rfl
  refine c25_local_observation_of_retained_spatial_bound Q ρ εF 1 hεF one_pos (U n) Fn hFn
    heFn Vn hVn ?_
  filter_upwards [hE] with ω hEω
  obtain ⟨E, hEd, hEae, hEb⟩ := hEω
  have hEae' : (fun x => (P t f) (translate (x + h • unitVector j) ω) -
      Vt ω (x + h • unitVector j)) =ᵐ[volume] fun x => E (x + h • unitVector j) :=
    hmp.quasiMeasurePreserving.ae_eq_comp hEae
  have hVnc : (Vn ω : Vec d → ℂ) =ᵐ[volume] fun x =>
      ((h : ℝ) : ℂ)⁻¹ * (Vt ω (x + h • unitVector j) - Vt ω x) := by
    filter_upwards [Lp.coeFn_smul (((h : ℝ) : ℂ)⁻¹) (Tl (Vt ω) - Vt ω),
      Lp.coeFn_sub (Tl (Vt ω)) (Vt ω), Lp.coeFn_compMeasurePreserving (Vt ω) hmp]
      with x h1 h2 h3
    change (((h : ℝ) : ℂ)⁻¹ • (Tl (Vt ω) - Vt ω)) x = _
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply]
    change ((h : ℝ) : ℂ)⁻¹ • ((Lp.compMeasurePreserving (fun x : Vec d => x + h • unitVector j)
      hmp (Vt ω)) x - (Vt ω) x) = _
    rw [h3]
    rfl
  have hgradb : ∀ y, euclideanNorm y ≤ 2 → ‖fderiv ℝ E y (unitVector j)‖ ≤ εF := by
    intro y hy
    have hj : ‖fderiv ℝ E y (unitVector j)‖ ≤
        Real.sqrt (∑ k : Fin d, ‖fderiv ℝ E y (unitVector k)‖ ^ 2) :=
      Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun k _ => sq_nonneg
        ‖fderiv ℝ E y (unitVector k)‖) (Finset.mem_univ j))
    have := hEb y hy
    linarith [norm_nonneg (E y)]
  filter_upwards [ae_restrict_of_ae hEae, ae_restrict_of_ae hEae', ae_restrict_of_ae hVnc,
    ae_restrict_mem (PDE.isOpen_euclideanBall _ _).measurableSet] with x h1 h2 h3 hxB
  have hx1 : euclideanNorm x < 1 := clr_mem_unit_ball hxB
  have hinc := clr_coordinate_increment_le hEd j hgradb hx1.le hh0.le hh1
  have htr : translate (h • unitVector j) (translate x ω) =
      translate (x + h • unitVector j) ω := by
    rw [translate_add, add_comm]
  have hkey : Fn (translate x ω) - Vn ω x =
      ((h : ℝ) : ℂ)⁻¹ * (E (x + h • unitVector j) - E x) := by
    rw [h3]
    change ((h : ℝ) : ℂ)⁻¹ * ((P t f) (translate (h • unitVector j) (translate x ω)) -
      (P t f) (translate x ω)) - _ = _
    rw [htr]
    have e1 : E (x + h • unitVector j) = (P t f) (translate (x + h • unitVector j) ω) -
        Vt ω (x + h • unitVector j) := h2.symm
    have e2 : E x = (P t f) (translate x ω) - Vt ω x := h1.symm
    rw [e1, e2]
    ring
  rw [hkey, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh0]
  calc h⁻¹ * ‖E (x + h • unitVector j) - E x‖ ≤ h⁻¹ * (εF * h) :=
        mul_le_mul_of_nonneg_left hinc (inv_nonneg.mpr hh0.le)
    _ = εF := by field_simp

end EinsteinFull
