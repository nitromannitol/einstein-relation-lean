import EinsteinRelation.Correctors.ConditionalCopyPlanarMoments
import EinsteinRelation.Correctors.CanonicalGradientMomentBounds
import EinsteinRelation.Correctors.CanonicalGradientCopyMoments
import EinsteinRelation.Correctors.NestedCopyMoments
import EinsteinRelation.Correctors.VectorRmsBallMoments
open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM StationarySpatialRealization NormalizedSpatialRepresentativeSupport
local instance planarEnergyDim : Fact (2 ≤ 2) := ⟨by decide⟩
attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance planarEnergyRestrictionMeasurableSpace (U : Set (Vec 2)) : MeasurableSpace C(U, Mat 2) := borel C(U, Mat 2)

/-- Nested conditioning and spatial averaging reduce the planar energy
bound to the point-gradient copy estimate. Small radii use Lemma 5.1.
Source: `paper/main.tex:864–886`. -/
theorem exists_planar_copy_energy_bound_of_gradient_copy_bounds
    (H51 : CorrectorGradientMoments) (L r₀ m : ℝ) (hm : 2 ≤ m)
    (hgradient : ∃ C : ℝ, ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point 2) (i : Fin 2),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat 2) ×
        (FieldPair 2 × FieldPair 2) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C/R)) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point 2) (i : Fin 2),
      MemLp (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ∧
      eLpNorm (conditionalCopyGradientRms Q R y i) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (B/R) := by
  obtain ⟨Cg,hCg⟩ := hgradient
  obtain ⟨G,hG,hGb⟩ := exists_canonicalGradient_moment_bound H51 (by decide : 2 ≤ 2) L r₀ hm
  let B : ℝ := 4*(max Cg 0+G)+1
  have hB : 0 < B := by dsimp only [B]; positivity
  refine ⟨B,hB,?_⟩
  intro Q R hR y i
  have hRp : 0 < R := zero_lt_one.trans_le hR
  let μ := reducedEnvironmentLaw Q
  let U := conditionalCorrectorBall R y
  let P := reducedConditionalCopyLaw μ U
  letI : IsProbabilityMeasure P := (reducedConditionalCopy_properties μ U
    (isOpen_conditionalCorrectorBall R y)).1
  have hGb' : eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω))
      (ENNReal.ofReal m) μ ≤ ENNReal.ofReal G := by
    simpa only [conditionalCorrectorGradient, WithLp.ofLp_zero] using hGb Q i
  let F : (C(U, Mat 2) × (FieldPair 2 × FieldPair 2)) × Vec 2 → Vec 2 := fun z =>
    conditionalCorrectorGradient Q i (WithLp.toLp 2 (z.2+y.ofLp)) z.1.2.1 -
      conditionalCorrectorGradient Q i (WithLp.toLp 2 (z.2+y.ofLp)) z.1.2.2
  have hFm : Measurable F := by
    have hgrad := (PiLp.continuous_ofLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp
      (measurable_spatialRealization (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin 2)) 2 μ))
    exact (hgrad.comp ((measurable_snd.add_const y.ofLp).prodMk
      (measurable_fst.comp (measurable_snd.comp measurable_fst)))).sub
      (hgrad.comp ((measurable_snd.add_const y.ofLp).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have hslices (x : Vec 2) (hx : x ∈ ball 0 (2*R)) :
      MemLp (fun z => euclideanNorm (F (z,x))) (ENNReal.ofReal m) P ∧
      eLpNorm (fun z => euclideanNorm (F (z,x))) (ENNReal.ofReal m) P ≤ ENNReal.ofReal (B/R) := by
    let q := WithLp.toLp 2 (x+y.ofLp)
    obtain ⟨hmem,hbound⟩ := canonicalGradientCopy_moment_le Q i q U
      (isOpen_conditionalCorrectorBall R y) (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ m)) hG hGb'
    refine ⟨hmem,?_⟩
    by_cases hlarge : 2 ≤ R
    · let V := conditionalCorrectorBall (R/2) q
      have hhalf : 1 ≤ R/2 := by linarith
      have hVU : V ⊆ U := by
        intro z hz
        change dist (WithLp.toLp 2 z) q < 8*(R/2) at hz
        change dist (WithLp.toLp 2 z) y < 8*R
        have hxq : dist q y < 2*R := by
          rw [dist_eq_norm, show q-y = WithLp.toLp 2 x by simp [q],
            ← TimeChange.euclideanNorm_eq_norm_toLp]
          simpa only [ball,sub_zero,Set.mem_setOf_eq] using hx
        have htri := dist_triangle (WithLp.toLp 2 z) q y
        linarith
      let f : FieldPair 2 → EuclideanSpace ℝ (Fin 2) := fun ω =>
        spatialRealization (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin 2)) 2 μ) (x+y.ofLp,ω)
      have hfm : Measurable f := (measurable_spatialRealization _).comp
        (measurable_const.prodMk measurable_id)
      have hfi : Integrable f μ := (memLp_canonicalGradient_slice Q i (x+y.ofLp)).integrable one_le_two
      have hmono := eLpNorm_reducedCopy_difference_le_of_subset μ V U
        (isOpen_conditionalCorrectorBall (R/2) q) (isOpen_conditionalCorrectorBall R y)
        hVU f hfm hfi (ENNReal.one_le_ofReal.mpr (by linarith : 1 ≤ m)) ENNReal.ofReal_ne_top
      have heq (S : Set (Vec 2)) :
          eLpNorm (fun z : C(S, Mat 2) × (FieldPair 2 × FieldPair 2) =>
            f z.2.1-f z.2.2) (ENNReal.ofReal m) (reducedConditionalCopyLaw μ S) =
          eLpNorm (fun z : C(S, Mat 2) × (FieldPair 2 × FieldPair 2) =>
            euclideanNorm (conditionalCorrectorGradient Q i q z.2.1-
              conditionalCorrectorGradient Q i q z.2.2)) (ENNReal.ofReal m)
            (reducedConditionalCopyLaw μ S) := by
        rw [← eLpNorm_norm]
        apply eLpNorm_congr_ae
        exact Filter.Eventually.of_forall fun z => by
          change ‖f z.2.1-f z.2.2‖ = euclideanNorm
            (conditionalCorrectorGradient Q i q z.2.1-conditionalCorrectorGradient Q i q z.2.2)
          rw [TimeChange.euclideanNorm_eq_norm_toLp]
          rfl
      rw [heq U,heq V] at hmono
      have hbound' := hmono.trans (mul_le_mul_right (hCg Q (R/2) hhalf q i) 2)
      change eLpNorm (fun z => euclideanNorm (F (z,x))) (ENNReal.ofReal m) P ≤ _ at hbound'
      refine hbound'.trans ?_
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal (2 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      have hCB : 4*Cg ≤ B := by dsimp only [B]; nlinarith [le_max_left Cg 0]
      calc 2*(Cg/(R/2)) = (4*Cg)/R := by ring
           _ ≤ B/R := div_le_div_of_nonneg_right hCB hRp.le
    · refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
      have hBR : 2*G*R ≤ B := by
        dsimp only [B]
        nlinarith [le_max_right Cg 0, mul_nonneg hG (show 0 ≤ 2-R by linarith)]
      exact (le_div_iff₀ hRp).mpr hBR
  obtain ⟨hmem,hbound⟩ := vectorRms_ball_moment_of_uniform_slices P (2*R) (by positivity)
    hm (div_nonneg hB.le hRp.le) F hFm hslices
  exact ⟨hmem,hbound⟩
end EinsteinRelation.Correctors
