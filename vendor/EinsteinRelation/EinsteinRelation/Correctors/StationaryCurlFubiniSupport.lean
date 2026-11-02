import EinsteinRelation.Calculus.ClosedPotentialOrbitCurlSupport
import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors.StationaryCurlFubini

open EinsteinRelation.Correctors.StationarySpatialRealization

variable {d : ℕ}

private def coordinateLp (Q : Measure (FieldPair d)) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →L[ℝ] Lp ℝ 2 Q :=
  (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2 Q

/-- The ordinary samplewise spatial pairing agrees almost everywhere with its Bochner-valued
`L²(Q)` orbit pairing. The spatial integral is supported on the compact support of `a`, where the
actual translated representative is square integrable on the product. -/
theorem ae_samplewise_pairing_eq_orbit_pairing
    [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (i : Fin d)
    (a : Vec d → ℝ) (ha : Continuous a) (hac : HasCompactSupport a) :
    (fun ω => (∫ x : Vec d, a x • translationLp Q hQ x (coordinateLp Q i G) ∂volume) ω) =ᵐ[Q]
      fun ω => ∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume := by
  let K : Set (Vec d) := tsupport a
  have hK : IsCompact K := by simpa [K, HasCompactSupport] using hac
  have hKmeas : MeasurableSet K := hK.measurableSet
  let ν : Measure (Vec d) := volume.restrict K
  have hνK : ν = volume.restrict K := rfl
  letI : IsFiniteMeasure ν := (isFiniteMeasure_restrict).2 hK.measure_ne_top
  let R : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := EuclideanSpace.proj i
  let f : Vec d × FieldPair d → ℝ := fun p => R (spatialRealization G p)
  have hGprod : MemLp (spatialRealization G) 2 (ν.prod Q) :=
    memLp_spatialRealization_prod hQ ν G
  have hfprod : MemLp f 2 (ν.prod Q) := by
    exact R.comp_memLp' hGprod
  have hfint : Integrable f (ν.prod Q) :=
    hfprod.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  obtain ⟨C, hC⟩ := ha.bounded_above_of_compact_support hac
  have hC_nonneg : 0 ≤ C := (norm_nonneg (a 0)).trans (hC 0)
  have hAint : Integrable (fun p : Vec d × FieldPair d => a p.1 * f p) (ν.prod Q) := by
    refine Integrable.mono' (hfint.norm.const_mul C) ?_ ?_
    · exact (ha.measurable.comp measurable_fst).aestronglyMeasurable.mul hfprod.aestronglyMeasurable
    · filter_upwards [] with p
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC p.1) (norm_nonneg (f p))
  have hIndAint (s : Set (FieldPair d)) (hs : MeasurableSet s) :
      Integrable (fun p : Vec d × FieldPair d =>
        Set.indicator s (fun _ => (1 : ℝ)) p.2 * (a p.1 * f p)) (ν.prod Q) := by
    refine Integrable.mono' hAint.norm ?_ ?_
    · exact ((measurable_const.indicator hs).comp measurable_snd).aestronglyMeasurable.mul
        ((ha.measurable.comp measurable_fst).aestronglyMeasurable.mul hfprod.aestronglyMeasurable)
    · filter_upwards [] with p
      by_cases hp : p.2 ∈ s
      · simp [Set.indicator, hp, Real.norm_eq_abs]
      · have hzero : Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) p.2 = 0 :=
          Set.indicator_of_notMem hp _
        rw [hzero, zero_mul]
        simpa using (norm_nonneg (a p.1 * f p))
  let coord : Lp ℝ 2 Q := coordinateLp Q i G
  let P : Lp ℝ 2 Q := ∫ x : Vec d, a x • translationLp Q hQ x coord ∂volume
  let F : FieldPair d → ℝ := fun ω => R (G ω)
  have hF : MemLp F 2 Q := R.comp_memLp' (Lp.memLp G)
  have hFcoord : hF.toLp F = coord := by
    apply Lp.ext
    filter_upwards [hF.coeFn_toLp, R.coeFn_compLpL G] with ω h₁ h₂
    exact h₁.trans h₂.symm
  have htrans (x : Vec d) :
      translationLp Q hQ x coord =ᵐ[Q] fun ω => f (x, ω) := by
    rw [← hFcoord, translationLp_toLp]
    exact (hF.comp_measurePreserving (measurePreserving_translate Q hQ x)).coeFn_toLp
  have hcont : Continuous (fun x : Vec d => translationLp Q hQ x coord) :=
    (continuous_translationLp Q hQ).comp (continuous_id.prodMk continuous_const)
  have horbitInt : Integrable (fun x : Vec d => a x • translationLp Q hQ x coord) volume :=
    (ha.smul hcont).integrable_of_hasCompactSupport hac.smul_right
  have hsampleν : Integrable (fun ω : FieldPair d => ∫ x : Vec d, a x * f (x, ω) ∂ν) Q :=
    hAint.integral_prod_right
  have hνsample (ω : FieldPair d) :
      (∫ x : Vec d, a x * f (x, ω) ∂ν) =
        ∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume := by
    have hzero : ∀ x, x ∉ K → a x * f (x, ω) = 0 := by
      intro x hx
      have ha0 : a x = 0 := by
        exact (notMem_tsupport_iff_eventuallyEq.mp hx).self_of_nhds
      simp [ha0]
    change (∫ x in K, a x * f (x, ω) ∂volume) = _
    calc
      ∫ x in K, a x * f (x, ω) ∂volume = ∫ x, a x * f (x, ω) ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero hzero
      _ = ∫ x, a x * (G (translate x ω)).ofLp i ∂volume := by
        apply integral_congr_ae
        exact ae_of_all _ fun x => rfl
  have hsampleFull : Integrable
      (fun ω : FieldPair d => ∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume) Q := by
    exact hsampleν.congr (ae_of_all Q hνsample)
  have hpair (s : Set (FieldPair d)) (hs : MeasurableSet s) :
      ∫ ω in s, P ω ∂Q =
      ∫ ω in s, (∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume) ∂Q := by
    let hχ : MemLp (Set.indicator s (fun _ : FieldPair d => (1 : ℝ))) 2 Q :=
      memLp_indicator_const 2 hs 1 (Or.inr (measure_ne_top Q s))
    let χ : Lp ℝ 2 Q := hχ.toLp (Set.indicator s fun _ => (1 : ℝ))
    have hsetIntegral (I : Lp ℝ 2 Q) :
        ∫ ω in s, I ω ∂Q = inner ℝ χ I := by
      calc
        ∫ ω in s, I ω ∂Q = ∫ ω, Set.indicator s I ω ∂Q := by
          rw [integral_indicator hs]
        _ = ∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * I ω ∂Q := by
          apply integral_congr_ae
          filter_upwards [] with ω
          by_cases hω : ω ∈ s <;> simp [Set.indicator, hω]
        _ = inner ℝ χ I := by
          symm
          rw [L2.inner_def]
          apply integral_congr_ae
          filter_upwards [hχ.coeFn_toLp] with ω hω
          rw [hω, RCLike.inner_apply, conj_trivial]
          ring
    have hBvol : inner ℝ χ P =
          ∫ x : Vec d, a x *
            (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂volume := by
      change inner ℝ χ (∫ x : Vec d, a x • translationLp Q hQ x coord ∂volume) = _
      rw [← integral_inner (𝕜 := ℝ) horbitInt χ]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      change inner ℝ χ (a x • translationLp Q hQ x coord) = _
      rw [real_inner_smul_right, L2.inner_def]
      refine congrArg (fun z : ℝ => a x * z) ?_
      have hT' : translationLp Q hQ x coord =ᵐ[Q] fun ω => f (x, ω) := htrans x
      refine integral_congr_ae ?_
      filter_upwards [hχ.coeFn_toLp, hT'] with ω hχω hω
      rw [hχω, hω, RCLike.inner_apply, conj_trivial]
      ring
    have hB : inner ℝ χ P =
          ∫ x : Vec d, a x *
            (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂ν := by
      rw [hBvol]
      change (∫ x : Vec d, a x *
          (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q)
          ∂volume) = ∫ x in K, a x *
            (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂volume
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      have ha0 : a x = 0 := by
        exact (notMem_tsupport_iff_eventuallyEq.mp hx).self_of_nhds
      simp [ha0]
    have hFub :
        (∫ x : Vec d, a x *
          (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂ν) =
        ∫ ω in s, (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q := by
      have hswap := integral_integral_swap
        (f := fun x ω => Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω *
          (a x * f (x, ω))) (hIndAint s hs)
      calc
        (∫ x : Vec d, a x *
            (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂ν) =
            ∫ x : Vec d, ∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω *
              (a x * f (x, ω)) ∂Q ∂ν := by
                apply integral_congr_ae
                filter_upwards [] with x
                change a x * (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω *
                  f (x, ω) ∂Q) = _
                rw [← integral_const_mul]
                apply integral_congr_ae
                filter_upwards [] with ω
                ring
        _ = ∫ ω, ∫ x : Vec d, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω *
              (a x * f (x, ω)) ∂ν ∂Q := hswap
        _ = ∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω *
              (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q := by
                refine integral_congr_ae (ae_of_all _ fun ω => ?_)
                change (∫ x : Vec d, (Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω) *
                  (a x * f (x, ω)) ∂ν) =
                  (Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω) *
                    (∫ x : Vec d, a x * f (x, ω) ∂ν)
                rw [← integral_const_mul]
        _ = ∫ ω in s, (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q := by
                calc
                  ∫ ω, (Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω) *
                      (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q =
                      ∫ ω, Set.indicator s
                        (fun ω => ∫ x : Vec d, a x * f (x, ω) ∂ν) ω ∂Q := by
                          apply integral_congr_ae
                          filter_upwards [] with ω
                          by_cases hω : ω ∈ s <;> simp [Set.indicator, hω]
                  _ = ∫ ω in s, (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q := by
                          rw [integral_indicator hs]
    calc
      ∫ ω in s, P ω ∂Q = inner ℝ χ P := hsetIntegral P
      _ = ∫ x : Vec d, a x *
          (∫ ω, Set.indicator s (fun _ : FieldPair d => (1 : ℝ)) ω * f (x, ω) ∂Q) ∂ν := hB
      _ = ∫ ω in s, (∫ x : Vec d, a x * f (x, ω) ∂ν) ∂Q := hFub
      _ = ∫ ω in s, (∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume) ∂Q := by
          apply integral_congr_ae
          exact ae_of_all (Q.restrict s) hνsample
  change (fun ω => P ω) =ᵐ[Q]
    (fun ω => ∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume)
  have hPint : Integrable (fun ω => P ω) Q :=
    (Lp.memLp P).integrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply Integrable.ae_eq_of_forall_setIntegral_eq
    (fun ω => P ω)
    (fun ω => ∫ x : Vec d, a x * (G (translate x ω)).ofLp i ∂volume)
    hPint hsampleFull
  intro s hs _
  exact hpair s hs

end EinsteinRelation.Correctors.StationaryCurlFubini

end
