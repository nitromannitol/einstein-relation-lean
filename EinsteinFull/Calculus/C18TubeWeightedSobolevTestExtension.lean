import Mathlib.Analysis.Calculus.Deriv.Prod
import EinsteinFull.Calculus.C18TubeWeightedTimeMollification
import EinsteinFull.Calculus.C20TubeWeightedNonlinearEnergyLimit
import EinsteinFull.Calculus.C17TubeNonlinearTestApproximation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory EinsteinRelation
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- Uniform ellipticity bounds the density and every matrix coefficient in
essential supremum with respect to any spatial measure. -/
theorem c18_elliptic_coefficients_memLp_top {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (μ : Measure (Vec d)) :
    MemLp ρ ∞ μ ∧ ∀ i j, MemLp (fun x => α x i j) ∞ μ := by
  have hα : IsElliptic κ⁻¹ α := by
    intro x
    simpa only [inv_inv] using (hell.2.2 x).2.2
  refine ⟨memLp_top_of_bound hell.1.aestronglyMeasurable κ⁻¹ ?_, ?_⟩
  · apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (hell.2.2 x).1)] using
      (hell.2.2 x).2.1
  · intro i j
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    have hm : Measurable (fun x => α x i j) :=
      ((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        hell.2.1
    apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
    apply ae_of_all
    intro x
    have he := PiLp.norm_apply_le
      (WithLp.toLp 2 ((α x).mulVec (unitVector j)) : EuclideanSpace ℝ (Fin d)) i
    have hn := Correctors.isElliptic_mulVec_euclideanNorm_le (inv_pos.mpr hκ)
      hα x (unitVector j)
    rw [TimeChange.euclideanNorm_eq_norm_toLp] at hn
    have hv : ((α x).mulVec (unitVector j)) i = α x i j := by
      change dotProduct (fun k => α x i k) (Pi.single j 1) = _
      rw [dotProduct_single, mul_one]
    have hu : euclideanNorm (unitVector j) = 1 := by
      simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
    simpa only [PiLp.toLp_apply, hv, Real.norm_eq_abs, hu, mul_one] using he.trans hn

/-- Pulling the coefficient fields back along a measurable spatial projection
preserves their essential boundedness for any measure on the source. -/
theorem c18_elliptic_coefficients_comp_memLp_top {d : ℕ} {κ : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x : Ω → Vec d)
    (hx : AEMeasurable x μ) (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α) :
    MemLp (fun z => ρ (x z)) ∞ μ ∧
      ∀ i j, MemLp (fun z => α (x z) i j) ∞ μ := by
  obtain ⟨hρ, hα⟩ := c18_elliptic_coefficients_memLp_top hκ hell (Measure.map x μ)
  exact ⟨hρ.comp_of_map hx, fun i j => (hα i j).comp_of_map hx⟩

/-- A forward difference quotient of the solution is square integrable on the
smaller cylinder. No time differentiability of the solution is assumed. -/
theorem c18_weighted_caloric_forward_difference_memLp {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    MemLp (fun z => (u (z.1 + h, z.2) - u z) / h) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
  have hshift := (c18_memLp_forward_shift (c18_sourceBall_measurable y r)
    hhsmall (show h ∈ Set.Icc 0 h from ⟨le_of_lt hh, le_rfl⟩) hu.1).1
  have hbase := (c18_memLp_forward_shift (c18_sourceBall_measurable y r)
    hhsmall (show (0 : ℝ) ∈ Set.Icc 0 h from ⟨le_rfl, le_of_lt hh⟩) hu.1).1
  have hbase' : MemLp u 2 (volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)) := by
    simpa only [add_zero] using hbase
  simpa only [div_eq_mul_inv, Pi.sub_apply] using (hshift.sub hbase').mul_const h⁻¹

/-- A locally integrable scalar function has an almost-everywhere derivative
of its forward integral, equal to the difference of its endpoint values. -/
theorem c18_forward_integral_ae_hasDerivAt {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (h : ℝ) :
    ∀ᵐ t ∂volume, HasDerivAt (fun t => ∫ s in (0 : ℝ)..h, f (t + s))
      (f (t + h) - f t) t := by
  have hi (a b : ℝ) : IntervalIntegrable f volume a b :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
  have hd := LocallyIntegrable.ae_hasDerivAt_integral hf
  have hdshift := (measurePreserving_add_right (volume : Measure ℝ) h).quasiMeasurePreserving.ae hd
  filter_upwards [hd, hdshift] with t ht hth
  have heq : (fun t : ℝ => ∫ s in (0 : ℝ)..h, f (t + s)) =
      (fun t => (∫ s in (0 : ℝ)..(t + h), f s) - ∫ s in (0 : ℝ)..t, f s) := by
    funext t
    rw [show (fun s : ℝ => f (t + s)) = (fun s => f (s + t)) by
      funext s; rw [add_comm], intervalIntegral.integral_comp_add_right]
    simp only [zero_add, add_comm h]
    exact (intervalIntegral.integral_interval_sub_left (hi 0 (t + h)) (hi 0 t)).symm
  rw [heq]
  simpa only [Function.comp_def, Pi.sub_def, id_eq, mul_one, add_comm] using
    ((hth 0).comp t ((hasDerivAt_id t).add_const h)).sub (ht 0)

/-- The endpoint derivative formula on the inner interval requires only
integrability on the original time interval. -/
theorem c18_forward_integral_local_ae_hasDerivAt {f : ℝ → ℝ} {h : ℝ}
    (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasDerivAt (fun t => ∫ s in (0 : ℝ)..h, f (t + s))
        (f (t + h) - f t) t := by
  let g := (Set.Ioo (-1 : ℝ) 1).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  have hd := c18_forward_integral_ae_hasDerivAt hg.locallyIntegrable h
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with t ht htm
  have htm0 : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    simpa only [add_zero] using c18_forward_time_mem hhsmall htm ⟨le_rfl, hh⟩
  have htmh : t + h ∈ Set.Ioo (-1 : ℝ) 1 := c18_forward_time_mem hhsmall htm ⟨hh, le_rfl⟩
  have heq : (fun t => ∫ s in (0 : ℝ)..h, g (t + s)) =ᶠ[nhds t]
      (fun t => ∫ s in (0 : ℝ)..h, f (t + s)) := by
    filter_upwards [isOpen_Ioo.mem_nhds htm] with q hq
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
    exact Set.indicator_of_mem (c18_forward_time_mem hhsmall hq hs') f
  have ht' := ht.congr_of_eventuallyEq heq.symm
  simpa only [g, Set.indicator_of_mem htm0, Set.indicator_of_mem htmh] using ht'

/-- Almost every spatial slice of the solution has the finite-difference
derivative of its forward time average on the inner interval. -/
theorem c18_weighted_caloric_forward_ae_time_derivative {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : EinsteinRelation.Vec d → ℝ)
    (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d) (y : EinsteinRelation.Vec d)
    (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    ∀ᵐ x ∂volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r),
      ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
        HasDerivAt (fun t => ρ x * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)))
          (ρ x * ((u (t + h, x) - u (t, x)) / h)) t := by
  letI := c18_sourceCylinder_isFiniteMeasure y r
  have hi : Integrable u ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  have hx' : IntegrableOn (fun t => u (t, x)) (Set.Ioo (-1 : ℝ) 1) volume := hx
  filter_upwards [c18_forward_integral_local_ae_hasDerivAt hx' (le_of_lt hh) hhsmall] with t ht
  simpa only [div_eq_mul_inv, mul_comm h⁻¹] using (ht.const_mul h⁻¹).const_mul (ρ x)

/-- Backward time translates of inner-cylinder tests are admissible on the
original cylinder for each shift in the forward averaging interval. -/
theorem c18_forward_shift_test_admissible {d : ℕ} {h s r : ℝ}
    (hhsmall : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    (y : EinsteinRelation.Vec d) (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × EinsteinRelation.Vec d => ψ (z.1 - s, z.2)) ∧
    HasCompactSupport (fun z : ℝ × EinsteinRelation.Vec d => ψ (z.1 - s, z.2)) ∧
    tsupport (fun z : ℝ × EinsteinRelation.Vec d => ψ (z.1 - s, z.2)) ⊆
      interior (Set.Ioo (-1 : ℝ) 1) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r := by
  let e : (ℝ × EinsteinRelation.Vec d) ≃ₜ (ℝ × EinsteinRelation.Vec d) :=
    Homeomorph.addRight (-s, 0)
  have he (z : ℝ × EinsteinRelation.Vec d) : e z = (z.1 - s, z.2) := by
    ext <;> simp [e, sub_eq_add_neg]
  have heq : (fun z : ℝ × EinsteinRelation.Vec d => ψ (z.1 - s, z.2)) = ψ ∘ e := by
    funext z
    simp only [Function.comp_apply, he]
  refine ⟨hψ.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd), ?_, ?_⟩
  · rw [heq]
    exact hc.comp_homeomorph e
  · rw [heq, tsupport_comp_eq_preimage]
    intro z hz
    have hz' := hsp hz
    rw [interior_Ioo]
    have hzspace : z.2 ∈ EinsteinFull.External.Source.GMP.sourceBall y r := by
      simpa only [he] using hz'.2
    refine ⟨?_, hzspace⟩
    have hztime : z.1 - s ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      simpa only [he] using hz'.1
    rcases hztime with ⟨hl, hr⟩
    rcases hs with ⟨hs0, hsh⟩
    constructor <;> linarith

/-- The original weighted weak equation applies to every backward translate
of a smooth test on the inner cylinder. -/
theorem c18_weighted_caloric_translated_test {d : ℕ} {h s r : ℝ}
    (hhsmall : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (y : EinsteinRelation.Vec d) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * u z) * fderiv ℝ (fun q : ℝ × EinsteinRelation.Vec d => ψ (q.1 - s, q.2)) z (1, 0) +
        EinsteinRelation.dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ (fun q : ℝ × EinsteinRelation.Vec d => ψ (q.1 - s, q.2)) z
            (0, EinsteinRelation.unitVector j))) = 0 := by
  obtain ⟨hd, hcompact, hsupport⟩ := c18_forward_shift_test_admissible hhsmall hs y ψ hψ hc hsp
  exact hu.2.2.2.2 _ hd hcompact hsupport

/-- Time translation commutes with the full Fréchet derivative of a test. -/
theorem c18_fderiv_backward_time_shift {d : ℕ}
    (ψ : ℝ × EinsteinRelation.Vec d → ℝ) (s : ℝ)
    (z : ℝ × EinsteinRelation.Vec d) :
    fderiv ℝ (fun q : ℝ × EinsteinRelation.Vec d => ψ (q.1 - s, q.2)) z =
      fderiv ℝ ψ (z.1 - s, z.2) := by
  have he : (fun q : ℝ × EinsteinRelation.Vec d => ψ (q.1 - s, q.2)) =
      (fun q => ψ (q + (-s, 0))) := by
    funext q
    rcases q with ⟨t, x⟩
    simp [sub_eq_add_neg]
  rw [he, fderiv_comp_add_right]
  rcases z with ⟨t, x⟩
  simp [sub_eq_add_neg]

/-- The derivative of a test vanishes off its prescribed cylinder. -/
theorem c18_fderiv_eq_zero_off_test_cylinder {d : ℕ} {r : ℝ}
    (y : EinsteinRelation.Vec d) (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)
    (z : ℝ × EinsteinRelation.Vec d)
    (hz : z ∉ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    fderiv ℝ ψ z = 0 := by
  have hs : z ∉ Function.support (fderiv ℝ ψ) := fun h => hz (hsp (support_fderiv_subset ℝ h))
  simpa only [Function.mem_support, not_not] using hs

/-- The translated weak equation expressed using derivatives of the original test. -/
theorem c18_weighted_caloric_translated_test_derivatives {d : ℕ} {h s r : ℝ}
    (hhsmall : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (y : EinsteinRelation.Vec d) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * u z) * fderiv ℝ ψ (z.1 - s, z.2) (1, 0) +
        EinsteinRelation.dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ (z.1 - s, z.2)
            (0, EinsteinRelation.unitVector j))) = 0 := by
  simpa only [c18_fderiv_backward_time_shift] using
    c18_weighted_caloric_translated_test hhsmall hs ρ α y u G hu ψ hψ hc hsp

/-- Translate a cylinder integral back to the smaller cylinder when its
integrand vanishes outside the time translate of that cylinder. -/
theorem c18_integral_backward_time_translate {d : ℕ} {h s r : ℝ}
    (hhsmall : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    (y : EinsteinRelation.Vec d) (F : ℝ × EinsteinRelation.Vec d → ℝ)
    (hzero : ∀ z, (z.1 - s, z.2) ∉
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r → F z = 0) :
    (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r, F z) =
      ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r, F (z.1 + s, z.2) := by
  let S := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
    EinsteinFull.External.Source.GMP.sourceBall y r
  let T := Set.Ioo (-1 : ℝ) 1 ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r
  let e : (ℝ × EinsteinRelation.Vec d) ≃ₜ (ℝ × EinsteinRelation.Vec d) :=
    Homeomorph.addRight (s, 0)
  have he (z : ℝ × EinsteinRelation.Vec d) : e z = (z.1 + s, z.2) := by
    ext <;> simp [e]
  have himage : e '' S ⊆ T := by
    rintro z ⟨q, hq, rfl⟩
    rw [he]
    exact ⟨c18_forward_time_mem hhsmall hq.1 hs, hq.2⟩
  have hz : ∀ z ∈ T \ (e '' S), F z = 0 := by
    intro z hz
    apply hzero
    intro hq
    apply hz.2
    refine ⟨(z.1 - s, z.2), hq, ?_⟩
    rw [he]
    simp
  have hrestrict : (∫ z in T, F z) = ∫ z in e '' S, F z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (measurableSet_Ioo.prod (c18_sourceBall_measurable y r)) himage hz
  have heq : (e : ℝ × EinsteinRelation.Vec d → ℝ × EinsteinRelation.Vec d) =
      Prod.map (fun t : ℝ => t + s) id := by
    funext z
    exact he z
  have hpres : MeasurePreserving e (volume : Measure (ℝ × EinsteinRelation.Vec d)) volume := by
    rw [heq]
    simpa only [← Measure.volume_eq_prod ℝ (EinsteinRelation.Vec d)] using
      ((measurePreserving_add_right (volume : Measure ℝ) s).prod
        (MeasurePreserving.id (volume : Measure (EinsteinRelation.Vec d))))
  rw [hrestrict, hpres.setIntegral_image_emb e.measurableEmbedding]
  apply setIntegral_congr_fun (measurableSet_Ioo.prod (c18_sourceBall_measurable y r))
  intro z hz
  change F (e z) = F (z.1 + s, z.2)
  rw [he]

/-- The translated weak equation after changing variables to the inner cylinder. -/
theorem c18_weighted_caloric_forward_shifted_equation {d : ℕ} {h s r : ℝ}
    (hhsmall : h ≤ 1 / 4) (hs : s ∈ Set.Icc 0 h)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (y : EinsteinRelation.Vec d) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * u (z.1 + s, z.2)) * fderiv ℝ ψ z (1, 0) +
        EinsteinRelation.dot ((α z.2).mulVec (G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, EinsteinRelation.unitVector j))) = 0 := by
  let F : ℝ × EinsteinRelation.Vec d → ℝ := fun z =>
    -(ρ z.2 * u z) * fderiv ℝ ψ (z.1 - s, z.2) (1, 0) +
      EinsteinRelation.dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ (z.1 - s, z.2) (0, EinsteinRelation.unitVector j))
  have hzero : ∀ z, (z.1 - s, z.2) ∉
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r → F z = 0 := by
    intro z hz
    have hd := c18_fderiv_eq_zero_off_test_cylinder y ψ hsp (z.1 - s, z.2) hz
    simp [F, hd, EinsteinRelation.dot]
  have ht := c18_weighted_caloric_translated_test_derivatives hhsmall hs ρ α y u G hu ψ hψ hc hsp
  change (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ
    EinsteinFull.External.Source.GMP.sourceBall y r, F z) = 0 at ht
  rw [c18_integral_backward_time_translate hhsmall hs y F hzero] at ht
  simpa [F] using ht

/-- Fubini averages the shifted weak equation, provided its actual integrand
is jointly integrable over the shift interval and inner cylinder. -/
theorem c18_weighted_caloric_forward_averaged_equation_of_integrable
    {d : ℕ} {h r : ℝ} (hhsmall : h ≤ 1 / 4)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (y : EinsteinRelation.Vec d) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × EinsteinRelation.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)
    (hint : Integrable (fun p : ℝ × (ℝ × EinsteinRelation.Vec d) =>
      -(ρ p.2.2 * u (p.2.1 + p.1, p.2.2)) * fderiv ℝ ψ p.2 (1, 0) +
        EinsteinRelation.dot ((α p.2.2).mulVec (G (p.2.1 + p.1, p.2.2)))
          (fun j => fderiv ℝ ψ p.2 (0, EinsteinRelation.unitVector j)))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
          EinsteinFull.External.Source.GMP.sourceBall y r)))) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ∫ s in Set.Ioc (0 : ℝ) h,
        -(ρ z.2 * u (z.1 + s, z.2)) * fderiv ℝ ψ z (1, 0) +
          EinsteinRelation.dot ((α z.2).mulVec (G (z.1 + s, z.2)))
            (fun j => fderiv ℝ ψ z (0, EinsteinRelation.unitVector j))) = 0 := by
  rw [← integral_integral_swap hint]
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  exact c18_weighted_caloric_forward_shifted_equation hhsmall ⟨le_of_lt hs.1, hs.2⟩
    ρ α y u G hu ψ hψ hc hsp

/-- A derivative of a compactly supported smooth test is essentially bounded
after any almost-everywhere measurable change of variables. -/
theorem c18_test_fderiv_comp_memLp_top {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (q : Ω → ℝ × Vec d) (hq : AEMeasurable q μ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (v : ℝ × Vec d) :
    MemLp (fun z => fderiv ℝ ψ (q z) v) ∞ μ := by
  have ht : MemLp (fun z => fderiv ℝ ψ z v) ∞ (Measure.map q μ) :=
    ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hc.fderiv_apply ℝ v) _
  exact ht.comp_of_map hq

/-- Uniform ellipticity and the solution's L² data make the shifted weak
equation integrable jointly in the averaging shift and the cylinder. -/
theorem c18_weighted_caloric_shifted_integrand_integrable {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    Integrable (fun p : ℝ × (ℝ × Vec d) =>
      -(ρ p.2.2 * u (p.2.1 + p.1, p.2.2)) * fderiv ℝ ψ p.2 (1, 0) +
        dot ((α p.2.2).mulVec (G (p.2.1 + p.1, p.2.2)))
          (fun j => fderiv ℝ ψ p.2 (0, unitVector j)))
      ((volume.restrict (Set.Ioc (0 : ℝ) h)).prod
        (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
          EinsteinFull.External.Source.GMP.sourceBall y r))) := by
  let μ := (volume.restrict (Set.Ioc (0 : ℝ) h)).prod
    (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r))
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hU := c18_memLp_forward_joint (c18_sourceBall_measurable y r) hhsmall hu.1
  have hG := c18_memLp_forward_joint (c18_sourceBall_measurable y r) hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  have hcoeff := c18_elliptic_coefficients_comp_memLp_top μ
    (fun p : ℝ × (ℝ × Vec d) => p.2.2) (measurable_snd.comp measurable_snd).aemeasurable
    hκ hell
  have ht (v : ℝ × Vec d) := c18_test_fderiv_comp_memLp_top μ
    (fun p : ℝ × (ℝ × Vec d) => p.2) measurable_snd.aemeasurable ψ hψ hc v
  have hρu : MemLp (fun p : ℝ × (ℝ × Vec d) =>
      ρ p.2.2 * u (p.2.1 + p.1, p.2.2)) 2 μ := hcoeff.1.mul hU
  have hmass : MemLp (fun p : ℝ × (ℝ × Vec d) =>
      -(ρ p.2.2 * u (p.2.1 + p.1, p.2.2)) * fderiv ℝ ψ p.2 (1, 0)) 2 μ :=
    hρu.neg.mul (ht (1, 0))
  have hαG (i j : Fin d) : MemLp (fun p : ℝ × (ℝ × Vec d) =>
      α p.2.2 i j * G (p.2.1 + p.1, p.2.2) j) 2 μ :=
    (hcoeff.2 i j).mul (hG.eval j)
  have hflux (i j : Fin d) : MemLp (fun p : ℝ × (ℝ × Vec d) =>
      (α p.2.2 i j * G (p.2.1 + p.1, p.2.2) j) *
        fderiv ℝ ψ p.2 (0, unitVector i)) 2 μ :=
    (hαG i j).mul (ht (0, unitVector i))
  have hsum := memLp_finsetSum Finset.univ (fun i _ =>
    memLp_finsetSum Finset.univ (fun j _ => hflux i j))
  have htotal := hmass.add hsum
  convert htotal.integrable (by norm_num) using 1
  ext p
  simp [dot, Matrix.mulVec, dotProduct, Finset.sum_mul]

/-- Averaging the actual weighted weak equation requires no additional
integrability hypothesis beyond uniform ellipticity and the solution data. -/
theorem c18_weighted_caloric_forward_averaged_equation {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ∫ s in Set.Ioc (0 : ℝ) h,
        -(ρ z.2 * u (z.1 + s, z.2)) * fderiv ℝ ψ z (1, 0) +
          dot ((α z.2).mulVec (G (z.1 + s, z.2)))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  exact c18_weighted_caloric_forward_averaged_equation_of_integrable hhsmall ρ α y u G hu
    ψ hψ hc hsp (c18_weighted_caloric_shifted_integrand_integrable hκ hhsmall ρ α hell y u G hu ψ hψ hc)

/-- The flux pairing with fixed coefficients and test gradient is a continuous
linear functional of the spatial gradient. -/
def c18FluxPairingCLM {d : ℕ} (A : Mat d) (v : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ i, ∑ j, (A i j * v i) • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ)

/-- A fixed flux pairing commutes with Bochner integration. -/
theorem c18_integral_flux_pairing {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Mat d) (v : Vec d) (F : Ω → Vec d)
    (hF : Integrable F μ) :
    (∫ s, dot (A.mulVec (F s)) v ∂μ) = dot (A.mulVec (∫ s, F s ∂μ)) v := by
  have heq (w : Vec d) : c18FluxPairingCLM A v w = dot (A.mulVec w) v := by
    simp [c18FluxPairingCLM, dot, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, mul_comm, mul_left_comm]
  simp_rw [← heq]
  exact (c18FluxPairingCLM A v).integral_comp_comm hF

/-- The averaged weighted equation with the time and flux averages separated. -/
theorem c18_weighted_caloric_forward_averaged_equation_split {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * (∫ s in Set.Ioc (0 : ℝ) h, u (z.1 + s, z.2))) *
          fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (∫ s in Set.Ioc (0 : ℝ) h, G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  have hj := c18_weighted_caloric_forward_joint_integrable hhsmall ρ α y u G hu
  have hU := hj.1.swap.prod_right_ae
  have hG := hj.2.swap.prod_right_ae
  have heq : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r),
      (∫ s in Set.Ioc (0 : ℝ) h,
        -(ρ z.2 * u (z.1 + s, z.2)) * fderiv ℝ ψ z (1, 0) +
          dot ((α z.2).mulVec (G (z.1 + s, z.2)))
            (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      -(ρ z.2 * (∫ s in Set.Ioc (0 : ℝ) h, u (z.1 + s, z.2))) *
          fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (∫ s in Set.Ioc (0 : ℝ) h, G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
    filter_upwards [hU, hG] with z hUz hGz
    change Integrable (fun s => u (z.1 + s, z.2)) (volume.restrict (Set.Ioc 0 h)) at hUz
    change Integrable (fun s => G (z.1 + s, z.2)) (volume.restrict (Set.Ioc 0 h)) at hGz
    let L := c18FluxPairingCLM (α z.2) (fun j => fderiv ℝ ψ z (0, unitVector j))
    have hflux : Integrable (fun s => dot ((α z.2).mulVec (G (z.1 + s, z.2)))
        (fun j => fderiv ℝ ψ z (0, unitVector j))) (volume.restrict (Set.Ioc 0 h)) := by
      have hL := L.integrable_comp hGz
      simpa [L, c18FluxPairingCLM, dot, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm] using hL
    have hmass : Integrable (fun s => -(ρ z.2 * u (z.1 + s, z.2)) *
        fderiv ℝ ψ z (1, 0)) (volume.restrict (Set.Ioc 0 h)) := by
      simpa only [Pi.neg_apply] using ((hUz.const_mul (ρ z.2)).neg.mul_const (fderiv ℝ ψ z (1, 0)))
    rw [integral_add hmass hflux,
      integral_mul_const, integral_neg, integral_const_mul,
      c18_integral_flux_pairing _ _ _ _ hGz]
  rw [← integral_congr_ae heq]
  exact c18_weighted_caloric_forward_averaged_equation hκ hhsmall ρ α hell y u G hu ψ hψ hc hsp

/-- The normalized forward averages satisfy the original density-weighted
spacetime test equation on the smaller cylinder. -/
theorem c18_weighted_caloric_forward_average_weak_equation {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
          fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  have heq := c18_weighted_caloric_forward_averaged_equation_split hκ hhsmall ρ α hell
    y u G hu ψ hψ hc hsp
  simp only [intervalIntegral.integral_of_le hh] 
  have hid : (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in Set.Ioc (0 : ℝ) h, u (z.1 + s, z.2))) *
          fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in Set.Ioc (0 : ℝ) h, G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      fun z => h⁻¹ * (-(ρ z.2 * (∫ s in Set.Ioc (0 : ℝ) h, u (z.1 + s, z.2))) *
          fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (∫ s in Set.Ioc (0 : ℝ) h, G (z.1 + s, z.2)))
          (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
    funext z
    simp [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_comm, mul_left_comm]
    ring_nf
    simp_rw [Finset.mul_sum]
    simp only [mul_assoc]
  rw [hid, integral_const_mul, heq, mul_zero]

/-- Forward Steklov averaging preserves the weighted caloric equation on the
smaller time interval, with its actual spatial weak gradient. -/
theorem c18_weighted_caloric_forward_steklov {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G) :
    EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) (EinsteinFull.External.Source.GMP.sourceBall y r)
      (fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))
      (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) := by
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have havg := c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu
  refine ⟨havg.1, ?_, havg.2, ?_, ?_⟩
  · exact (c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
      (c18_weighted_caloric_gradient_memLp ρ α u G hu)).aestronglyMeasurable
  · exact c18_weighted_caloric_forward_average_ae_weakGradient hh hhsmall ρ α y u G hu
  · intro ψ hψ hc hsp
    apply c18_weighted_caloric_forward_average_weak_equation hκ hh.le hhsmall ρ α hell y u G hu ψ hψ hc
    simpa only [interior_Ioo] using hsp

/-- A forward time integral is absolutely continuous on every compact interval
when the original scalar function is locally integrable. -/
theorem c18_forward_integral_absolutelyContinuous {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (h a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..h, f (t + s)) a b := by
  have hi (c d : ℝ) : IntervalIntegrable f volume c d :=
    intervalIntegrable_iff.mpr
      ((hf.integrableOn_isCompact isCompact_uIcc).mono_set Set.uIoc_subset_uIcc)
  have hshift : IntervalIntegrable (fun t => f (t + h)) volume a b :=
    (IntervalIntegrable.comp_add_right_iff).mpr (hi (a + h) (b + h))
  have hd : IntervalIntegrable (fun t => f (t + h) - f t) volume a b :=
    hshift.sub (hi a b)
  have hac := hd.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => ∫ s in (0 : ℝ)..h, f (a + s)) a b :=
    (LipschitzWith.const _).lipschitzOnWith.absolutelyContinuousOnInterval
  apply (hconst.add hac).congr
  intro t ht
  have hincr := c18_forward_integral_increment (hi a (a + h)) (hi t (t + h)) (hi a t)
  simp only [Pi.add_apply]
  linarith

/-- Local integrability on the original time interval suffices for absolute
continuity of forward averages on compact subintervals of the inner interval. -/
theorem c18_forward_integral_local_absolutelyContinuous {f : ℝ → ℝ} {h a b : ℝ}
    (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    (hab : Set.uIcc a b ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in (0 : ℝ)..h, f (t + s)) a b := by
  let g := (Set.Ioo (-1 : ℝ) 1).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  apply (c18_forward_integral_absolutelyContinuous hg.locallyIntegrable h a b).congr
  intro t ht
  apply intervalIntegral.integral_congr
  intro s hs
  have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
  exact Set.indicator_of_mem (c18_forward_time_mem hhsmall (hab ht) hs') f

/-- Integration by parts for a forward integral uses its actual endpoint
difference and needs only local integrability of the original function. -/
theorem c18_forward_integral_integration_by_parts {f ψ : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) (h a b : ℝ)
    (hψ : AbsolutelyContinuousOnInterval ψ a b) (ha : ψ a = 0) (hb : ψ b = 0) :
    (∫ t in a..b, (∫ s in (0 : ℝ)..h, f (t + s)) * deriv ψ t) =
      -∫ t in a..b, (f (t + h) - f t) * ψ t := by
  let F : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..h, f (t + s)
  have hF := c18_forward_integral_absolutelyContinuous hf h a b
  have hparts := hF.integral_mul_deriv_eq_deriv_mul hψ
  have heq : (∫ t in a..b, deriv F t * ψ t) =
      ∫ t in a..b, (f (t + h) - f t) * ψ t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [c18_forward_integral_ae_hasDerivAt hf h] with t ht htmem
    rw [ht.deriv]
  rw [heq, ha, hb] at hparts
  simpa [F] using hparts

/-- Integration by parts on an inner compact interval requires only the
original interval's integrability, with no global extension assumption. -/
theorem c18_forward_integral_local_integration_by_parts {f ψ : ℝ → ℝ} {h a b : ℝ}
    (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4)
    (hab : Set.uIcc a b ⊆ Set.Icc (-(1 / 2 : ℝ)) (1 / 2))
    (hψ : AbsolutelyContinuousOnInterval ψ a b) (ha : ψ a = 0) (hb : ψ b = 0) :
    (∫ t in a..b, (∫ s in (0 : ℝ)..h, f (t + s)) * deriv ψ t) =
      -∫ t in a..b, (f (t + h) - f t) * ψ t := by
  let g := (Set.Ioo (-1 : ℝ) 1).indicator f
  have hg : Integrable g volume := hf.integrable_indicator measurableSet_Ioo
  have hparts := c18_forward_integral_integration_by_parts hg.locallyIntegrable h a b hψ ha hb
  have heq (t : ℝ) (ht : t ∈ Set.uIcc a b) :
      (∫ s in (0 : ℝ)..h, g (t + s)) = ∫ s in (0 : ℝ)..h, f (t + s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Set.Icc (0 : ℝ) h := by simpa [Set.uIcc_of_le hh] using hs
    have hmem : t + s ∈ Set.Ioo (-1 : ℝ) 1 := by
      have ht' := hab ht
      constructor <;> linarith [ht'.1, ht'.2, hs'.1, hs'.2]
    exact Set.indicator_of_mem hmem f
  have heq₁ : (∫ t in a..b, (∫ s in (0 : ℝ)..h, g (t + s)) * deriv ψ t) =
      ∫ t in a..b, (∫ s in (0 : ℝ)..h, f (t + s)) * deriv ψ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [heq t ht]
  have heq₂ : (∫ t in a..b, (g (t + h) - g t) * ψ t) =
      ∫ t in a..b, (f (t + h) - f t) * ψ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' := hab ht
    have ht0 : t ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht'.1, ht'.2]
    have hth : t + h ∈ Set.Ioo (-1 : ℝ) 1 := by constructor <;> linarith [ht'.1, ht'.2]
    simp only [g, Set.indicator_of_mem ht0, Set.indicator_of_mem hth]
  rw [heq₁, heq₂] at hparts
  exact hparts

/-- On every spatial slice, a smooth cylinder-supported test converts the
forward average's time derivative to the actual finite difference. -/
theorem c18_forward_integral_smooth_test_slice {d : ℕ} {h r : ℝ}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4) (y x : Vec d)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Ioo (-1 : ℝ) 1) volume)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
        (∫ s in (0 : ℝ)..h, f (t + s)) * fderiv ℝ ψ (t, x) (1, 0)) =
      -∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ), (f (t + h) - f t) * ψ (t, x) := by
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ψ (t, x)) :=
    hψ.comp (contDiff_id.prodMk contDiff_const)
  have hzero (t : ℝ) (ht : t ∉ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) : ψ (t, x) = 0 := by
    have hn : (t, x) ∉ tsupport ψ := fun hm => ht (hsp hm).1
    exact image_eq_zero_of_notMem_tsupport hn
  have hderiv (t : ℝ) : deriv (fun t : ℝ => ψ (t, x)) t =
      fderiv ℝ ψ (t, x) (1, 0) := by
    have hd := ((hψ.differentiable (by simp)) (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    exact hd.deriv
  have hparts := c18_forward_integral_local_integration_by_parts hf hh hhsmall
    (a := -(1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by simp [Set.uIcc_of_le])
    (hslice.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    (hzero _ (by simp)) (hzero _ (by simp))
  simpa only [hderiv] using hparts

/-- Almost every spatial slice of a weighted solution satisfies the smooth-test
time integration-by-parts identity on the inner interval. -/
theorem c18_weighted_caloric_forward_smooth_test_ae_slice {d : ℕ} {h r : ℝ}
    (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 4) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    ∀ᵐ x ∂volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r),
      (∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          (∫ s in (0 : ℝ)..h, u (t + s, x)) * fderiv ℝ ψ (t, x) (1, 0)) =
        -∫ t in (-(1 / 2 : ℝ))..(1 / 2 : ℝ),
          (u (t + h, x) - u (t, x)) * ψ (t, x) := by
  letI := c18_sourceCylinder_isFiniteMeasure y r
  have hi : Integrable u ((volume.restrict (Set.Ioo (-1 : ℝ) 1)).prod
      (volume.restrict (EinsteinFull.External.Source.GMP.sourceBall y r))) := by
    rw [Measure.prod_restrict]
    exact memLp_one_iff_integrable.mp (hu.1.mono_exponent (by norm_num))
  filter_upwards [hi.prod_left_ae] with x hx
  exact c18_forward_integral_smooth_test_slice hh hhsmall y x (fun t => u (t, x)) hx ψ hψ hsp

/-- The weighted time term of a forward average equals the pairing with its
actual forward difference, for every smooth compact cylinder test. -/
theorem c18_weighted_caloric_forward_time_pairing {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) =
    ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z := by
  let I := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  let μ := (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hρ := (c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell).1
  have hψtop : MemLp ψ ∞ μ := hψ.continuous.memLp_top_of_hasCompactSupport hc μ
  have hdt := c18_test_fderiv_comp_memLp_top μ id measurable_id.aemeasurable ψ hψ hc (1, 0)
  have havg := (c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu).1
  have hdiff := c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu
  have hleft : Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) μ := by
    have hm0 : MemLp (fun z : ℝ × Vec d =>
      ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) 2 μ := hρ.mul havg
    have hm : MemLp (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) 2 μ := hm0.neg.mul hdt
    exact hm.integrable (by norm_num)
  have hright : Integrable (fun z : ℝ × Vec d =>
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) μ := by
    have hm0 : MemLp (fun z : ℝ × Vec d =>
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)) 2 μ := hρ.mul hdiff
    have hm : MemLp (fun z : ℝ × Vec d =>
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) 2 μ := hm0.mul hψtop
    exact hm.integrable (by norm_num)
  have hleft' : Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hleft
  have hright' : Integrable (fun z : ℝ × Vec d =>
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z)
      ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hright
  change (∫ z, _ ∂μ) = ∫ z, _ ∂μ
  rw [show μ = (volume.restrict I).prod (volume.restrict U) by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]]
  rw [integral_prod_symm _ hleft', integral_prod_symm _ hright']
  apply integral_congr_ae
  filter_upwards [c18_weighted_caloric_forward_smooth_test_ae_slice hh.le hhsmall ρ α y u G hu ψ hψ hsp]
    with x hx
  have hx' := congrArg (fun a : ℝ => -(ρ x * h⁻¹) * a) hx
  simp only [intervalIntegral.integral_of_le (show (-(1 / 2 : ℝ)) ≤ 1 / 2 by norm_num),
    ← restrict_Ioo_eq_restrict_Ioc, ← integral_neg, ← integral_const_mul] at hx'
  convert hx' using 1 <;> apply integral_congr_ae <;> filter_upwards [] with t <;>
    (try simp only [div_eq_mul_inv]) <;> ring

/-- The forward time difference and averaged flux satisfy the weighted
weak equation against every smooth compactly supported spacetime test. -/
theorem c18_weighted_caloric_forward_difference_weak_equation {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
        (fun j => fderiv ℝ ψ z (0, unitVector j))) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hcoeff := c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell
  have ht (v : ℝ × Vec d) := c18_test_fderiv_comp_memLp_top μ id
    measurable_id.aemeasurable ψ hψ hc v
  have havg := (c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu).1
  have hG := c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  have hρu : MemLp (fun z : ℝ × Vec d =>
      ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) 2 μ := hcoeff.1.mul havg
  have hmass : Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) μ := by
    have hm : MemLp (fun z : ℝ × Vec d =>
      -(ρ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        fderiv ℝ ψ z (1, 0)) 2 μ := hρu.neg.mul (ht (1, 0))
    exact hm.integrable (by norm_num)
  have hαG (i j : Fin d) : MemLp (fun z : ℝ × Vec d =>
      α z.2 i j * (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) j) 2 μ :=
    (hcoeff.2 i j).mul (hG.eval j)
  have hflux (i j : Fin d) : MemLp (fun z : ℝ × Vec d =>
      (α z.2 i j * (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) j) *
        fderiv ℝ ψ z (0, unitVector i)) 2 μ :=
    (hαG i j).mul (ht (0, unitVector i))
  have hsum := memLp_finsetSum Finset.univ (fun i _ =>
    memLp_finsetSum Finset.univ (fun j _ => hflux i j))
  have hfluxint : Integrable (fun z : ℝ × Vec d =>
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
        (fun j => fderiv ℝ ψ z (0, unitVector j))) μ := by
    convert hsum.integrable (by norm_num) using 1
    ext z
    simp [dot, Matrix.mulVec, dotProduct, Finset.sum_mul]
  have heq := c18_weighted_caloric_forward_average_weak_equation hκ hh.le hhsmall
    ρ α hell y u G hu ψ hψ hc hsp
  change (∫ z, _ ∂μ) = 0 at heq
  rw [integral_add hmass hfluxint] at heq
  rw [c18_weighted_caloric_forward_time_pairing hκ hh hhsmall ρ α hell y u G hu ψ hψ hc hsp] at heq
  exact heq

/-- Convergence in the L² seminorm implies convergence of the squared error integral. -/
theorem c18_integral_sq_tendsto_of_eLpNorm {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} (e : ι → Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (e n) 2 μ)
    (hl : Filter.Tendsto (fun n => eLpNorm (e n) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, |e n x| ^ 2 ∂μ) l (nhds 0) := by
  have hn : Filter.Tendsto (fun n => (eLpNorm (e n) 2 μ).toReal) l (nhds 0) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hl)
  have hs := hn.pow 2
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hs
  apply hs.congr'
  filter_upwards [he] with n hn'
  rw [hn'.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs, Real.rpow_two]
  have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
  rw [hhalf, ← Real.sqrt_eq_rpow, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  exact Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (|e n x|))

/-- An L² error converging to zero has a vanishing pairing with fixed L² data. -/
theorem c18_integral_abs_mul_tendsto_of_eLpNorm {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} (e : ι → Ω → ℝ) (g : Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (e n) 2 μ) (hg : MemLp g 2 μ)
    (hl : Filter.Tendsto (fun n => eLpNorm (e n) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, |e n x| * |g x| ∂μ) l (nhds 0) :=
  c20_integral_abs_mul_fixed_L2_tendsto_zero e g he hg
    (c18_integral_sq_tendsto_of_eLpNorm e he hl)

/-- Fixed L² data pair continuously with errors converging to zero in L². -/
theorem c18_integral_mul_tendsto_zero_of_eLpNorm {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} (e : ι → Ω → ℝ) (g : Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (e n) 2 μ) (hg : MemLp g 2 μ)
    (hl : Filter.Tendsto (fun n => eLpNorm (e n) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, e n x * g x ∂μ) l (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hu := c18_integral_abs_mul_tendsto_of_eLpNorm e g he hg hl
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall fun n => norm_nonneg _
  · filter_upwards with n
    calc
      ‖∫ x, e n x * g x ∂μ‖ ≤ ∫ x, ‖e n x * g x‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ x, |e n x| * |g x| ∂μ := by simp only [Real.norm_eq_abs, abs_mul]

/-- L² convergence passes through integration against a fixed L² function. -/
theorem c18_integral_mul_tendsto_of_eLpNorm {Ω ι : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {l : Filter ι} (f : ι → Ω → ℝ) (u g : Ω → ℝ)
    (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (he : ∀ᶠ n in l, MemLp (fun x => f n x - u x) 2 μ)
    (hl : Filter.Tendsto (fun n => eLpNorm (fun x => f n x - u x) 2 μ) l (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, f n x * g x ∂μ) l
      (nhds (∫ x, u x * g x ∂μ)) := by
  have h := c18_integral_mul_tendsto_zero_of_eLpNorm (fun n x => f n x - u x) g he hg hl
  have hadd := h.add (tendsto_const_nhds (x := ∫ x, u x * g x ∂μ))
  simp only [zero_add] at hadd
  apply hadd.congr'
  filter_upwards [he] with n hn
  have hf : MemLp (f n) 2 μ := by
    have ha := hn.add hu
    convert ha using 1
    ext x
    simp
  have hi : Integrable (fun x => f n x * g x) μ := hf.integrable_mul hg
  have hj : Integrable (fun x => u x * g x) μ := hu.integrable_mul hg
  have heq : (fun x => (f n x - u x) * g x) =
      (fun x => f n x * g x - u x * g x) := by
    funext x
    ring
  rw [heq]
  rw [integral_sub hi hj]
  ring

/-- The forward-difference equation extends to compactly supported spatial
Sobolev tests on the centered source cylinder. -/
@[nolint unusedArguments]
theorem c18_weighted_caloric_forward_difference_sobolev_test {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall 0 r) u G)
    (ψ : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall 0 r)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall 0 r)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall 0 r)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall 0 r)
        (fun x => ψ (t,x)) (fun x => H (t,x)))
    (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall 0 r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall 0 r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall 0 r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) (H z)) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall 0 r)
  letI := c18_smallSourceCylinder_isFiniteMeasure (0 : Vec d) r
  obtain ⟨v, hv, hvlim, hVlim⟩ := c17_spacetime_spatial_sobolev_test_density
    ψ H hψ hHm hH hgrad hc hsp
  let K : ℝ × Vec d → Vec d := fun z =>
    (α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))
  let D : ℝ × Vec d → ℝ := fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)
  let V : ℕ → ℝ × Vec d → Vec d := fun n z =>
    (fun j => fderiv ℝ (v n) z (0, unitVector j)) - H z
  have hcoeff := c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell
  have hD : MemLp D 2 μ := hcoeff.1.mul
    (c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α 0 u G hu)
  have hG := c18_memLp_forward_average (c18_sourceBall_measurable (0 : Vec d) r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  have hKi (i : Fin d) : MemLp (fun z => K z i) 2 μ := by
    have hαG (j : Fin d) : MemLp (fun z : ℝ × Vec d =>
        α z.2 i j * (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) j) 2 μ :=
      (hcoeff.2 i j).mul (hG.eval j)
    have hs := memLp_finsetSum Finset.univ (fun j _ => hαG j)
    convert hs using 1
    ext z
    simp [K, Matrix.mulVec, dotProduct]
  have hHi (i : Fin d) : MemLp (fun z => H z i) 2 μ := by
    apply hH.mono' ((continuous_apply i).comp_aestronglyMeasurable hHm)
    exact ae_of_all _ fun z => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (H z)) i)
  have hvi (n : ℕ) (i : Fin d) : MemLp
      (fun z => fderiv ℝ (v n) z (0, unitVector i)) 2 μ := by
    exact (c18_test_fderiv_comp_memLp_top μ id measurable_id.aemeasurable
      (v n) (hv n).1 (hv n).2.1 (0, unitVector i)).mono_exponent (by norm_num)
  have hVm (n : ℕ) : AEStronglyMeasurable (V n) μ := by
    apply AEStronglyMeasurable.sub _ hHm
    exact (aemeasurable_pi_iff.mpr (fun i => (hvi n i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hVcoord (i : Fin d) : Filter.Tendsto
      (fun n => eLpNorm (fun z => V n z i) 2 μ) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVlim
      (fun n => bot_le)
    intro n
    apply eLpNorm_mono_real ((continuous_apply i).comp_aestronglyMeasurable (hVm n))
    intro z
    simpa only [Real.norm_eq_abs, TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (V n z)) i)
  have hmasslim := c18_integral_mul_tendsto_of_eLpNorm v ψ D hψ hD
    (Filter.Eventually.of_forall fun n =>
      ((hv n).1.continuous.memLp_top_of_hasCompactSupport (hv n).2.1 μ).mono_exponent
        (by norm_num) |>.sub hψ) hvlim
  have hfluxlim (i : Fin d) := c18_integral_mul_tendsto_of_eLpNorm
    (fun n z => fderiv ℝ (v n) z (0, unitVector i)) (fun z => H z i)
    (fun z => K z i) (hHi i) (hKi i)
    (Filter.Eventually.of_forall fun n => (hvi n i).sub (hHi i)) (hVcoord i)
  have hlim := hmasslim.add (tendsto_finsetSum Finset.univ (fun i _ => hfluxlim i))
  have heq (n : ℕ) :
      (∫ z, v n z * D z ∂μ) + ∑ i : Fin d,
        ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ = 0 := by
    have h := c18_weighted_caloric_forward_difference_weak_equation hκ hh hhsmall
      ρ α hell 0 u G hu (v n) (hv n).1 (hv n).2.1 (hv n).2.2
    have hf : (∫ z, dot (K z) (fun i => fderiv ℝ (v n) z (0, unitVector i)) ∂μ) =
        ∑ i : Fin d, ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ := by
      have hs := integral_finset_sum Finset.univ (fun i _ => (hvi n i).integrable_mul (hKi i))
      simp only [Pi.mul_apply] at hs
      rw [← hs]
      apply integral_congr_ae
      filter_upwards with z
      simp [dot, mul_comm]
    change (∫ z, D z * v n z ∂μ) +
      (∫ z, dot (K z) (fun i => fderiv ℝ (v n) z (0, unitVector i)) ∂μ) = 0 at h
    rw [hf] at h
    simpa only [mul_comm] using h
  have hz : Filter.Tendsto (fun n => (∫ z, v n z * D z ∂μ) +
      ∑ i : Fin d, ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ)
      Filter.atTop (nhds 0) := by
    simpa only [heq] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) _ _)
  have hf : (∫ z, dot (K z) (H z) ∂μ) =
      ∑ i : Fin d, ∫ z, H z i * K z i ∂μ := by
    have hs := integral_finset_sum Finset.univ (fun i _ => (hHi i).integrable_mul (hKi i))
    simp only [Pi.mul_apply] at hs
    rw [← hs]
    apply integral_congr_ae
    filter_upwards with z
    simp [dot, mul_comm]
  have hfinal := tendsto_nhds_unique hlim hz
  change (∫ z, D z * ψ z ∂μ) + (∫ z, dot (K z) (H z) ∂μ) = 0
  rw [hf]
  simpa only [mul_comm] using hfinal


/-- Pass the forward-difference equation through a joint Sobolev approximation. -/
theorem c18_weighted_caloric_forward_difference_of_test_approximation {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)))
    (v : ℕ → ℝ × Vec d → ℝ)
    (hv : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
      tsupport (v n) ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)
    (hvlim : Filter.Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r))) Filter.atTop (nhds 0))
    (hVlim : Filter.Tendsto (fun n => eLpNorm (fun z => euclideanNorm
      ((fun j => fderiv ℝ (v n) z (0, unitVector j)) - H z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r))) Filter.atTop (nhds 0)) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) (H z)) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  let K : ℝ × Vec d → Vec d := fun z =>
    (α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))
  let D : ℝ × Vec d → ℝ := fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)
  let V : ℕ → ℝ × Vec d → Vec d := fun n z =>
    (fun j => fderiv ℝ (v n) z (0, unitVector j)) - H z
  have hcoeff := c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell
  have hD : MemLp D 2 μ := hcoeff.1.mul
    (c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu)
  have hG := c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  have hKi (i : Fin d) : MemLp (fun z => K z i) 2 μ := by
    have hαG (j : Fin d) : MemLp (fun z : ℝ × Vec d =>
        α z.2 i j * (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) j) 2 μ :=
      (hcoeff.2 i j).mul (hG.eval j)
    have hs := memLp_finsetSum Finset.univ (fun j _ => hαG j)
    convert hs using 1
    ext z
    simp [K, Matrix.mulVec, dotProduct]
  have hHi (i : Fin d) : MemLp (fun z => H z i) 2 μ := by
    apply hH.mono' ((continuous_apply i).comp_aestronglyMeasurable hHm)
    exact ae_of_all _ fun z => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (H z)) i)
  have hvi (n : ℕ) (i : Fin d) : MemLp
      (fun z => fderiv ℝ (v n) z (0, unitVector i)) 2 μ := by
    exact (c18_test_fderiv_comp_memLp_top μ id measurable_id.aemeasurable
      (v n) (hv n).1 (hv n).2.1 (0, unitVector i)).mono_exponent (by norm_num)
  have hVm (n : ℕ) : AEStronglyMeasurable (V n) μ := by
    apply AEStronglyMeasurable.sub _ hHm
    exact (aemeasurable_pi_iff.mpr (fun i => (hvi n i).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hVcoord (i : Fin d) : Filter.Tendsto
      (fun n => eLpNorm (fun z => V n z i) 2 μ) Filter.atTop (nhds 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hVlim
      (fun n => bot_le)
    intro n
    apply eLpNorm_mono_real ((continuous_apply i).comp_aestronglyMeasurable (hVm n))
    intro z
    simpa only [Real.norm_eq_abs, TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (V n z)) i)
  have hmasslim := c18_integral_mul_tendsto_of_eLpNorm v ψ D hψ hD
    (Filter.Eventually.of_forall fun n =>
      ((hv n).1.continuous.memLp_top_of_hasCompactSupport (hv n).2.1 μ).mono_exponent
        (by norm_num) |>.sub hψ) hvlim
  have hfluxlim (i : Fin d) := c18_integral_mul_tendsto_of_eLpNorm
    (fun n z => fderiv ℝ (v n) z (0, unitVector i)) (fun z => H z i)
    (fun z => K z i) (hHi i) (hKi i)
    (Filter.Eventually.of_forall fun n => (hvi n i).sub (hHi i)) (hVcoord i)
  have hlim := hmasslim.add (tendsto_finsetSum Finset.univ (fun i _ => hfluxlim i))
  have heq (n : ℕ) :
      (∫ z, v n z * D z ∂μ) + ∑ i : Fin d,
        ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ = 0 := by
    have h := c18_weighted_caloric_forward_difference_weak_equation hκ hh hhsmall
      ρ α hell y u G hu (v n) (hv n).1 (hv n).2.1 (hv n).2.2
    have hf : (∫ z, dot (K z) (fun i => fderiv ℝ (v n) z (0, unitVector i)) ∂μ) =
        ∑ i : Fin d, ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ := by
      have hs := integral_finset_sum Finset.univ (fun i _ => (hvi n i).integrable_mul (hKi i))
      simp only [Pi.mul_apply] at hs
      rw [← hs]
      apply integral_congr_ae
      filter_upwards with z
      simp [dot, mul_comm]
    change (∫ z, D z * v n z ∂μ) +
      (∫ z, dot (K z) (fun i => fderiv ℝ (v n) z (0, unitVector i)) ∂μ) = 0 at h
    rw [hf] at h
    simpa only [mul_comm] using h
  have hz : Filter.Tendsto (fun n => (∫ z, v n z * D z ∂μ) +
      ∑ i : Fin d, ∫ z, fderiv ℝ (v n) z (0, unitVector i) * K z i ∂μ)
      Filter.atTop (nhds 0) := by
    simpa only [heq] using (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) _ _)
  have hf : (∫ z, dot (K z) (H z) ∂μ) =
      ∑ i : Fin d, ∫ z, H z i * K z i ∂μ := by
    have hs := integral_finset_sum Finset.univ (fun i _ => (hHi i).integrable_mul (hKi i))
    simp only [Pi.mul_apply] at hs
    rw [← hs]
    apply integral_congr_ae
    filter_upwards with z
    simp [dot, mul_comm]
  have hfinal := tendsto_nhds_unique hlim hz
  change (∫ z, D z * ψ z ∂μ) + (∫ z, dot (K z) (H z) ∂μ) = 0
  rw [hf]
  simpa only [mul_comm] using hfinal

/-- The actual nonlinear cutoff test is admissible in the forward-difference equation. -/
@[nolint unusedArguments]
theorem c18_weighted_caloric_forward_difference_nonlinear_test {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (w : ℝ × Vec d → ℝ) (W : ℝ × Vec d → Vec d)
    (hw : MemLp w 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hWm : AEStronglyMeasurable W (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hW : MemLp (fun z => euclideanNorm (W z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall y r)
        (fun x => w (t,x)) (fun x => W (t,x)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * (θ z * F (w z))) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)))
        (θ z • (deriv F (w z) • W z) +
          F (w z) • (fun j => fderiv ℝ θ z (0,unitVector j)))) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  let Q : ℝ → ℝ := fun s => F s - F 0
  have hQ : ContDiff ℝ 1 Q := hF.sub contDiff_const
  have hQder (s : ℝ) : deriv Q s = deriv F s := by
    simp [Q, deriv_sub (hF.differentiable (by simp) s) (differentiableAt_const _)]
  have hq : MemLp (fun z => Q (w z)) 2 μ := by
    change MemLp (Q ∘ w) 2 μ
    exact (PDE.lipschitzWith_of_abs_deriv_le hM (hQ.differentiable (by simp))
      (fun s => by simpa only [hQder] using hFM s)).comp_memLp (by simp [Q]) hw
  have hf : MemLp (fun z => F (w z)) 2 μ := by
    have hc : MemLp (fun _ : ℝ × Vec d => F 0) 2 μ := memLp_const _
    convert hq.add hc using 1
    ext z
    simp [Q]
  let D : ℝ × Vec d → Vec d := fun z j => fderiv ℝ θ z (0, unitVector j)
  have hθtop : MemLp θ ⊤ μ := hθ.continuous.memLp_top_of_hasCompactSupport hθc μ
  have hψ : MemLp (fun z => θ z * F (w z)) 2 μ := by
    simpa only [mul_comm] using hf.fun_mul hθtop
  have hderm : AEStronglyMeasurable (fun z => deriv F (w z)) μ :=
    hF.continuous_deriv_one.comp_aestronglyMeasurable hw.aestronglyMeasurable
  have hdertop : MemLp (fun z => deriv F (w z)) ⊤ μ := by
    apply memLp_top_of_bound hderm M
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFM (w z)
  have hDcont (j : Fin d) : Continuous (fun z => D z j) := by
    dsimp [D]
    exact ((contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const).continuous
  have hDtop (j : Fin d) : MemLp (fun z => D z j) ⊤ μ :=
    (hDcont j).memLp_top_of_hasCompactSupport (hθc.fderiv_apply ℝ (0,unitVector j)) μ
  have hcoord (j : Fin d) : MemLp (fun z => W z j) 2 μ := by
    apply hW.mono' ((continuous_apply j).comp_aestronglyMeasurable hWm)
    exact ae_of_all _ fun z => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (W z)) j)
  let H : ℝ × Vec d → Vec d := fun z => θ z • (deriv F (w z) • W z) + F (w z) • D z
  have hHi (j : Fin d) : MemLp (fun z => H z j) 2 μ := by
    have h1 : MemLp (fun z => deriv F (w z) * W z j) 2 μ := by
      simpa only [mul_comm] using (hcoord j).fun_mul hdertop
    have h2 : MemLp (fun z => θ z * (deriv F (w z) * W z j)) 2 μ := by
      simpa only [mul_comm] using h1.fun_mul hθtop
    convert h2.add (hf.fun_mul (hDtop j)) using 1
  have hvec : MemLp (fun z => (WithLp.toLp 2 (H z) : EuclideanSpace ℝ (Fin d))) 2 μ :=
    memLp_piLp_iff.mpr hHi
  have hH : MemLp (fun z => euclideanNorm (H z)) 2 μ := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hvec.norm
  have hHm : AEStronglyMeasurable H μ :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable hvec.aestronglyMeasurable
  obtain ⟨v, hv, hvlim, hVlim⟩ := c17_nonlinear_spacetime_test_approximation_at_center
    w W hw hWm hW hgrad F hF M hM hFM θ hθ hθc hθs
  exact c18_weighted_caloric_forward_difference_of_test_approximation hκ hh hhsmall
    ρ α y hell u G hu _ H hψ hHm hH v hv hvlim hVlim

/-- The nonlinear test formed from the actual forward average satisfies the
forward-difference equation on any source cylinder. -/
theorem c18_weighted_caloric_forward_difference_average_nonlinear_test
    {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ EinsteinFull.External.Source.GMP.sourceBall y r) :
    let w := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let W := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * (θ z * F (w z))) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      dot ((α z.2).mulVec (W z))
        (θ z • (deriv F (w z) • W z) +
          F (w z) • (fun j => fderiv ℝ θ z (0,unitVector j)))) = 0 := by
  have hw := c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu
  exact c18_weighted_caloric_forward_difference_nonlinear_test hκ hr hh hhsmall
    ρ α y hell u G hu _ _ hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 F hF M hM hFM θ hθ hθc hθs


/-- The forward-difference equation holds for Sobolev tests at any center. -/
@[nolint unusedArguments]
theorem c18_weighted_caloric_forward_difference_sobolev_test_at_center {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α (Set.Ioo (-1) 1)
      (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (ψ : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d)
    (hψ : MemLp ψ 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hHm : AEStronglyMeasurable H (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasWeakGradient (EinsteinFull.External.Source.GMP.sourceBall y r)
        (fun x => ψ (t,x)) (fun x => H (t,x)))
    (hc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * ψ z) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) (H z)) = 0 := by
  obtain ⟨v, hv, hvlim, hVlim⟩ := c17_spacetime_spatial_sobolev_test_density_at_center
    ψ H hψ hHm hH hgrad hc hsp
  exact c18_weighted_caloric_forward_difference_of_test_approximation hκ hh hhsmall
    ρ α y hell u G hu ψ H hψ hHm hH v hv hvlim hVlim

end EinsteinFull.Calculus
