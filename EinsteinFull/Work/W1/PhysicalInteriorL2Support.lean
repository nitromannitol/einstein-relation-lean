import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# The actual physical interior L² carrier

For an open domain, the closure of the values of the constructed zero-boundary
Sobolev graphs consists of all physical L² functions vanishing off the domain.
The reverse inclusion follows by separation with smooth interior tests, without
assuming a density theorem or identifying any killed process.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support EinsteinRelation.SpatialDirichlet

noncomputable section

/-- Every value in the physical interior closure vanishes off its domain. -/
theorem physicalZeroBoundaryL2_zero_off {d : ℕ} (U : Set (Vec d)) (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ U → f x = 0 := by
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  have hzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∀ n, x ∉ U → u n x = 0 := by
    apply ae_all_iff.mpr
    intro n
    obtain ⟨v, hv⟩ := hu n
    rw [← hv]
    have hvzero := (withDensity_absolutelyContinuous volume
      (fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x))).ae_le
      (physicalH1ZeroBoundary_value_zero_off U hd lam v.1 v.property)
    filter_upwards [physicalZeroBoundaryValue_ae_eq U hd ω lam L hω v, hvzero]
      with x hx hz hxU
    exact hx.trans (hz hxU)
  obtain ⟨ns, _, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  filter_upwards [hzero, hns] with x hx ht hxU
  have ht0 : Tendsto (fun n => u (ns n) x) atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun n => u (ns n) x) = fun _ : ℕ => (0 : ℝ) :=
      funext (fun n => hx (ns n) hxU)
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht ht0

/-- Orthogonality to all interior graph values forces vanishing inside the open domain. -/
theorem physicalZeroBoundaryL2_orthogonal_zero_on {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ (physicalZeroBoundaryL2 U hd ω lam L hω)ᗮ) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∈ U → f x = 0 := by
  letI : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    densityWeightedMeasure_locallyFinite _ (physicalReversibleDensity_continuous ω hd lam)
  apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
  intro φ hφ hφc hφU
  let u : physicalH1ZeroBoundary U hd lam :=
    ⟨physicalH1SmoothTest hd lam φ hφ hφc,
      physicalH1SmoothTest_mem_zeroBoundary U hd lam φ ⟨hφ, hφc, hφU⟩⟩
  have hvalue : physicalZeroBoundaryValue U hd ω lam L hω u
      =ᵐ[physicalReversibleMeasure ω hd lam] φ := by
    apply (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u).trans
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mpr
    exact (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp (physicalH1SmoothTest_value hd lam φ hφ hφc)
  have hz := (Submodule.mem_orthogonal _ f).mp hf _
    (physicalZeroBoundaryValue_mem_L2 U hd ω lam L hω u)
  rw [L2.inner_def] at hz
  calc
    (∫ x, φ x • f x ∂physicalReversibleMeasure ω hd lam) =
        ∫ x, inner ℝ (physicalZeroBoundaryValue U hd ω lam L hω u x) (f x)
          ∂physicalReversibleMeasure ω hd lam := by
      apply integral_congr_ae
      filter_upwards [hvalue] with x hx
      simp only [hx, RCLike.inner_apply, conj_trivial, smul_eq_mul]
      ring
    _ = 0 := hz

/-- For open domains the interior value closure is exactly physical L² supported in the domain.
This proves the needed density rather than taking it as an additional hypothesis. -/
theorem mem_physicalZeroBoundaryL2_iff_zero_off {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    f ∈ physicalZeroBoundaryL2 U hd ω lam L hω ↔
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ U → f x = 0 := by
  constructor
  · exact physicalZeroBoundaryL2_zero_off U hd ω lam L hω f
  · intro hf
    have heq := (physicalZeroBoundaryL2 U hd ω lam L hω).orthogonal_orthogonal_eq_closure
    rw [(physicalZeroBoundaryL2_isClosed U hd ω lam L hω).submodule_topologicalClosure_eq]
      at heq
    rw [← heq, Submodule.mem_orthogonal']
    intro g hg
    have hgzero := physicalZeroBoundaryL2_orthogonal_zero_on U hU hd ω lam L hω g hg
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [hf, hgzero] with x hx hy
    change inner ℝ (f x) (g x) = 0
    by_cases hxU : x ∈ U
    · rw [hy hxU, inner_zero_right]
    · rw [hx hxU, inner_zero_left]

/-- The previously constructed orthogonal projection is literal restriction to the open domain,
extended by zero. The boundary convention is exactly membership in `U`. -/
theorem physicalZeroBoundaryProjection_ae_eq_indicator {d : ℕ} (U : Set (Vec d))
    (hU : IsOpen U) (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalZeroBoundaryProjection U hd ω lam L hω f
      =ᵐ[physicalReversibleMeasure ω hd lam] U.indicator f := by
  classical
  have hout := physicalZeroBoundaryL2_zero_off U hd ω lam L hω
    (physicalZeroBoundaryProjection U hd ω lam L hω f)
    (physicalZeroBoundaryProjection_mem U hd ω lam L hω f)
  have hin := physicalZeroBoundaryL2_orthogonal_zero_on U hU hd ω lam L hω
    (f - physicalZeroBoundaryProjection U hd ω lam L hω f)
    ((physicalZeroBoundaryL2 U hd ω lam L hω).sub_starProjection_mem_orthogonal f)
  filter_upwards [hout, hin, Lp.coeFn_sub f (physicalZeroBoundaryProjection U hd ω lam L hω f)]
    with x hx hy hsub
  by_cases hxU : x ∈ U
  · rw [Set.indicator_of_mem hxU]
    exact (sub_eq_zero.mp (hsub.symm.trans (hy hxU))).symm
  · rw [Set.indicator_of_notMem hxU]
    exact hx hxU

/-- The two physical value maps of the same graph have the same Lebesgue representative. -/
theorem physicalZeroBoundaryValue_ae_eq_volume {d : ℕ} (U : Set (Vec d))
    (hd : 2 ≤ d) (ω : FieldPair d) (lam L : ℝ) (hω : IsRegular L ω)
    (u : physicalH1ZeroBoundary U hd lam) :
    physicalZeroBoundaryValue U hd ω lam L hω u =ᵐ[volume]
      densityWeightedH1SpaceValue u.1 :=
  (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _).mp
      (physicalZeroBoundaryValue_ae_eq U hd ω lam L hω u)

/-- The canonical local isometry is identity on the actual function classes.
Two subsequence limits transport the equality from the dense graph values to
every interior datum. Neither a representative identification nor a process
locality assertion is assumed. -/
theorem physicalZeroBoundaryLocalIsometry_ae_eq {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    (physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f).val
      =ᵐ[volume] f.val := by
  let T := physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω'
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp
    (denseRange_physicalZeroBoundaryInteriorValue U hd ω lam L hω f)
  have hrep : ∀ n, (T (u n)).val =ᵐ[volume] (u n).val := by
    intro n
    obtain ⟨v, hv⟩ := hu n
    rw [← hv]
    rw [show T (physicalZeroBoundaryInteriorValue U hd ω lam L hω v) =
      physicalZeroBoundaryInteriorValue U hd ω' lam L' hω' v from
      physicalZeroBoundaryLocalIsometry_value U hU hd ω ω' heq lam L L' hω hω' v]
    exact (physicalZeroBoundaryValue_ae_eq_volume U hd ω' lam L' hω' v).trans
      (physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω v).symm
  have hlim₁ : Tendsto (fun n => (u n).val) atTop (𝓝 f.val) :=
    (continuous_subtype_val.tendsto f).comp hlim
  have hlim₂ : Tendsto (fun n => (T (u n)).val) atTop (𝓝 (T f).val) :=
    (continuous_subtype_val.tendsto (T f)).comp ((T.continuous.tendsto f).comp hlim)
  obtain ⟨ns, hnsmono, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hlim₁).exists_seq_tendsto_ae
  obtain ⟨ms, hmsmono, hms⟩ := (tendstoInMeasure_of_tendsto_Lp
    (hlim₂.comp hnsmono.tendsto_atTop)).exists_seq_tendsto_ae
  have hnsvol := (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _).mp hns
  have hmsvol := (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω' hd lam) (physicalReversibleDensity_continuous ω' hd lam)
    (physicalReversibleDensity_pos ω' hd lam) _).mp hms
  have hrepall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ n, (T (u n)).val x = (u n).val x :=
    ae_all_iff.mpr hrep
  filter_upwards [hnsvol, hmsvol, hrepall] with x hx hy hz
  have hy' : Tendsto (fun n => (u (ns (ms n))).val x) atTop (𝓝 ((T f).val x)) := by
    simpa only [Function.comp_apply, hz] using hy
  exact tendsto_nhds_unique hy' (hx.comp hmsmono.tendsto_atTop)

/-- Equal interior function representatives are the canonical comparison of the two data. -/
theorem physicalZeroBoundaryLocalIsometry_eq_of_ae_eq {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (f : physicalZeroBoundaryL2 U hd ω lam L hω)
    (g : physicalZeroBoundaryL2 U hd ω' lam L' hω') (hfg : f.val =ᵐ[volume] g.val) :
    physicalZeroBoundaryLocalIsometry U hU hd ω ω' heq lam L L' hω hω' f = g := by
  apply Subtype.ext
  apply Lp.ext
  apply (ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω' hd lam) (physicalReversibleDensity_continuous ω' hd lam)
    (physicalReversibleDensity_pos ω' hd lam) _).mpr
  exact (physicalZeroBoundaryLocalIsometry_ae_eq U hU hd ω ω' heq lam L L' hω hω' f).trans hfg

/-- The actual physical interior evolutions agree as function classes for the same data.
This conclusion concerns the constructed evolutions; no GMP killed-law identification
or exceptional-start upgrade is included. -/
theorem physicalZeroBoundaryEvolution_ae_eq_of_physical_eqOn {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (hd : 2 ≤ d) (ω ω' : FieldPair d)
    (heq : ∀ x ∈ U, ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x) (lam L L' : ℝ)
    (hL : 1 ≤ L) (hL' : 1 ≤ L') (hω : IsRegular L ω) (hω' : IsRegular L' ω')
    (t : ℝ≥0) (f : physicalZeroBoundaryL2 U hd ω lam L hω)
    (g : physicalZeroBoundaryL2 U hd ω' lam L' hω') (hfg : f.val =ᵐ[volume] g.val) :
    (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f).val =ᵐ[volume]
      (physicalZeroBoundaryEvolution U hd ω' lam L' hL' hω' t g).val := by
  have h := physicalZeroBoundaryLocalIsometry_ae_eq U hU hd ω ω' heq lam L L' hω hω'
    (physicalZeroBoundaryEvolution U hd ω lam L hL hω t f)
  rw [physicalZeroBoundaryEvolution_localIsometry U hU hd ω ω' heq lam L L' hL hL' hω hω',
    physicalZeroBoundaryLocalIsometry_eq_of_ae_eq U hU hd ω ω' heq lam L L' hω hω' f g hfg] at h
  exact h.symm

end

end EinsteinFull
