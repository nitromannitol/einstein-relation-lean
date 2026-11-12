import EinsteinRelation.Correctors.CanonicalGlobalWeakPotential
import EinsteinRelation.Correctors.BallMeanSquareComparison
import EinsteinRelation.Correctors.WeakPotentialSubtraction
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.ScalarPotentialApproxEuclidean
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

/-!
# Jointly measurable scalar corrector potentials

Source: `paper/main.tex:688-698,754-758,901-906`. Proposition 5.3 conditions
the scalar corrector, minus its `ζ_R` average, on coefficient balls; this uses
one scalar potential that is jointly measurable in the environment and the
spatial point. The rapid horizontal approximations of a closed stationary
gradient, centered on the unit ball, converge pointwise almost everywhere to
the unit-ball normalized weak potential. Their limit is therefore an explicit
measurable potential; no measurable selection is used.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger StationarySpatialRealization

/-- A unit-ball mean-zero function is controlled on a larger ball by its weak
gradient. Source: the Poincaré inequality cited at `paper/main.tex:718`. -/
theorem integral_sq_le_of_unitBall_integral_eq_zero (hP : BallPoincareEstimate)
    {d : ℕ} (hd : 2 ≤ d) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Vec d → ℝ) (g : Vec d → Vec d),
      MemLp w 2 (volume.restrict (ball 0 R)) → MemLp g 2 (volume.restrict (ball 0 R)) →
      HasWeakGradient (ball 0 R) w g → (∫ x in ball (0 : Vec d) 1, w x) = 0 →
      ∫ x in ball (0 : Vec d) R, w x ^ 2 ≤
        C * ∫ x in ball (0 : Vec d) R, euclideanSq (g x) := by
  obtain ⟨C₀, hC₀, hest⟩ := hP d hd
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  set V₁ := volume.real (ball (0 : Vec d) 1) with hV₁def
  set V := volume.real (ball (0 : Vec d) R) with hVdef
  have hV₁ : 0 < V₁ := unitBall_volume_pos_finite d
  have hV : 0 < V := ball_volume_pos_finite d R hR0
  have hsub : ball (0 : Vec d) 1 ⊆ ball 0 R := fun x hx => lt_of_lt_of_le hx hR
  have hfin1 : volume (ball (0 : Vec d) 1) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hV₁).2.ne
  have hfinR : volume (ball (0 : Vec d) R) ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hV).2.ne
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) 1)) :=
    isFiniteMeasure_restrict.mpr hfin1
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hfinR
  refine ⟨(2 + 2 * V / V₁) * (C₀ * R) ^ 2, by positivity, ?_⟩
  intro w g hw hg hwg hmean
  set c := ⨍ x in ball (0 : Vec d) R, w x ∂volume with hcdef
  set A := ∫ x in ball (0 : Vec d) R, (w x - c) ^ 2 with hAdef
  set B := ∫ x in ball (0 : Vec d) R, euclideanSq (g x) with hBdef
  have hwc : MemLp (fun x => w x - c) 2 (volume.restrict (ball (0 : Vec d) R)) :=
    hw.sub (memLp_const c)
  have hA0 : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x => by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hPA : A ≤ (C₀ * R) ^ 2 * B := by
    have h := hest 0 R hR0 w g hw hg hwg
    simp only [sq_abs] at h
    have hs : Real.sqrt A ^ 2 ≤ (C₀ * R * Real.sqrt B) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rwa [Real.sq_sqrt hA0, mul_pow, Real.sq_sqrt hB0] at hs
  -- The unit-ball mean of `w - c` is `-c`, so Jensen bounds `c²`.
  have hc2 : c ^ 2 ≤ A / V₁ := by
    have hwc1 : MemLp (fun x => w x - c) 2 (volume.restrict (ball (0 : Vec d) 1)) :=
      hwc.mono_measure (Measure.restrict_mono_set volume hsub)
    have hm : (volume.restrict (ball (0 : Vec d) 1)).real Set.univ ≠ 0 := by
      simpa only [measureReal_restrict_apply_univ] using hV₁.ne'
    have hj := sq_average_le_average_sq (volume.restrict (ball (0 : Vec d) 1)) hm hwc1
    have hint1 : Integrable w (volume.restrict (ball (0 : Vec d) 1)) :=
      (hw.mono_measure (Measure.restrict_mono_set volume hsub)).integrable one_le_two
    have havg : (⨍ x in ball (0 : Vec d) 1, (w x - c) ∂volume) = -c := by
      rw [average_eq, integral_sub hint1 (integrable_const c), hmean, integral_const]
      simp only [measureReal_restrict_apply_univ, smul_eq_mul, zero_sub]
      rw [← hV₁def]
      field_simp
    have hsq : (⨍ x in ball (0 : Vec d) 1, (w x - c) ^ 2 ∂volume) ≤ A / V₁ := by
      rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul, ← hV₁def,
        inv_mul_eq_div]
      apply div_le_div_of_nonneg_right _ hV₁.le
      exact setIntegral_mono_set ((memLp_two_iff_integrable_sq hwc.aestronglyMeasurable).mp hwc)
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ hx => hsub hx)
    rw [havg, neg_sq] at hj
    exact hj.trans hsq
  have hsplit : ∫ x in ball (0 : Vec d) R, w x ^ 2 ≤ 2 * A + 2 * (c ^ 2 * V) := by
    have hi : Integrable (fun x => (w x - c) ^ 2) (volume.restrict (ball (0 : Vec d) R)) :=
      (memLp_two_iff_integrable_sq hwc.aestronglyMeasurable).mp hwc
    calc ∫ x in ball (0 : Vec d) R, w x ^ 2
        ≤ ∫ x in ball (0 : Vec d) R, (2 * (w x - c) ^ 2 + 2 * c ^ 2) := by
          apply integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _)
            ((hi.const_mul 2).add (integrable_const _))
          refine ae_of_all _ fun x => ?_
          change w x ^ 2 ≤ 2 * (w x - c) ^ 2 + 2 * c ^ 2
          nlinarith [sq_nonneg (w x - 2 * c)]
      _ = 2 * A + 2 * (c ^ 2 * V) := by
          rw [integral_add (hi.const_mul 2) (integrable_const _), integral_const_mul,
            integral_const, measureReal_restrict_apply_univ, smul_eq_mul, ← hVdef]
          ring
  have hcV : c ^ 2 * V ≤ V / V₁ * A := by
    calc c ^ 2 * V ≤ A / V₁ * V := mul_le_mul_of_nonneg_right hc2 hV.le
      _ = V / V₁ * A := by ring
  calc ∫ x in ball (0 : Vec d) R, w x ^ 2 ≤ 2 * A + 2 * (c ^ 2 * V) := hsplit
    _ ≤ 2 * A + 2 * (V / V₁ * A) := by linarith [hcV]
    _ = (2 + 2 * V / V₁) * A := by ring
    _ ≤ (2 + 2 * V / V₁) * ((C₀ * R) ^ 2 * B) :=
        mul_le_mul_of_nonneg_left hPA (by positivity)
    _ = (2 + 2 * V / V₁) * (C₀ * R) ^ 2 * B := by ring

/-- A geometrically rapid `L²` approximation of a stationary field has almost
surely summable squared spatial errors on every finite spatial measure. -/
theorem ae_summable_spatial_sq_error {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (F : ℕ → Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hF : ∀ n, ‖F n - G‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∀ᵐ ω ∂Q, Summable (fun n =>
      ∫ x, ‖F n (translate x ω) - G (translate x ω)‖ ^ 2 ∂ν) := by
  let H : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x, ‖F n (translate x ω) - G (translate x ω)‖ ^ 2 ∂ν
  have hcalc (n : ℕ) := integral_spatial_sq_norm_eq_volume_mul Q hQ ν (F n) G
  have hnonneg (n : ℕ) (ω : FieldPair d) : 0 ≤ H n ω :=
    integral_nonneg fun _ => sq_nonneg _
  let H' : ℕ → FieldPair d → ℝ := fun n ω => 2 ^ n * H n ω
  have hint (n : ℕ) : Integrable (H' n) Q := (hcalc n).1.const_mul _
  have hs : Summable (fun n => ∫ ω, ‖H' n ω‖ ∂Q) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) ?_
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (ν Set.univ).toReal)
    intro n
    have hmean : (∫ ω, ‖H' n ω‖ ∂Q) = 2 ^ n * ((ν Set.univ).toReal * ‖F n - G‖ ^ 2) := by
      rw [← (hcalc n).2, ← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      exact Real.norm_of_nonneg (mul_nonneg (by positivity) (hnonneg n ω))
    rw [hmean]
    have hsq : ‖F n - G‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hF n) 2
    calc 2 ^ n * ((ν Set.univ).toReal * ‖F n - G‖ ^ 2)
        ≤ 2 ^ n * ((ν Set.univ).toReal * ((1 / 2 : ℝ) ^ n) ^ 2) := by gcongr
      _ = (ν Set.univ).toReal * (1 / 2 : ℝ) ^ n := by
        rw [← pow_mul, mul_comm n 2, pow_mul]
        have h2 : (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ 2) ^ n = (1 / 2 : ℝ) ^ n := by
          rw [← mul_pow]
          norm_num
        calc 2 ^ n * ((ν Set.univ).toReal * ((1 / 2 : ℝ) ^ 2) ^ n)
            = (ν Set.univ).toReal * (2 ^ n * ((1 / 2 : ℝ) ^ 2) ^ n) := by ring
          _ = (ν Set.univ).toReal * (1 / 2 : ℝ) ^ n := by rw [h2]
  filter_upwards [ae_tendsto_zero_of_summable_integral_norm Q H' hint hs] with ω hω
  refine Summable.of_norm_bounded_eventually_nat summable_geometric_two ?_
  filter_upwards [hω.eventually (gt_mem_nhds one_pos)] with n hn
  have hn' : 2 ^ n * H n ω < 1 := hn
  rw [Real.norm_of_nonneg (hnonneg n ω)]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hsplit : H n ω = (2 ^ n)⁻¹ * (2 ^ n * H n ω) := by field_simp
  rw [hsplit, one_div, inv_pow]
  calc (2 ^ n)⁻¹ * (2 ^ n * H n ω) ≤ (2 ^ n)⁻¹ * 1 := by gcongr
    _ = (2 ^ n)⁻¹ := mul_one _

private theorem measurableSet_ball_zero {d : ℕ} (R : ℝ) :
    MeasurableSet (ball (0 : Vec d) R) := by
  unfold ball euclideanNorm euclideanSq dot
  exact (isOpen_lt (by fun_prop) continuous_const).measurableSet

/-- A closed stationary gradient has a jointly measurable scalar weak potential
with zero unit-ball integral on one full-measure event. The potential is the
pointwise limit of the unit-ball centered rapid horizontal approximations.
Source: `paper/main.tex:693-698,901-906`. -/
theorem exists_measurable_unitBall_weakPotential (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    ∃ φ : FieldPair d → Vec d → ℝ, StronglyMeasurable (Function.uncurry φ) ∧
      ∀ᵐ ω ∂Q, HasWeakGradient Set.univ (φ ω) (fun x => (G (translate x ω)).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp (φ ω) 2 (volume.restrict (ball 0 R))) ∧
        (∫ x in ball (0 : Vec d) 1, φ ω x) = 0 := by
  have hd : 2 ≤ d := Fact.out
  obtain ⟨f, hf, hsample⟩ := exists_samplewise_scalar_gradient_approximation Q hQ G hG
  let D := fun n => horizontalEuclideanGradient Q hQ (f n)
  let u : ℕ → FieldPair d → Vec d → ℝ := fun n ω x => (f n : Lp ℝ 2 Q) (translate x ω)
  let v : ℕ → FieldPair d → Vec d → ℝ := fun n ω x =>
    u n ω x - ⨍ y in ball (0 : Vec d) 1, u n ω y ∂volume
  have hu (n : ℕ) : StronglyMeasurable (Function.uncurry (u n)) :=
    (Lp.stronglyMeasurable (f n : Lp ℝ 2 Q)).comp_measurable
      (Probability.continuous_translate.measurable.comp measurable_swap)
  have hv (n : ℕ) : StronglyMeasurable (Function.uncurry (v n)) := by
    have hm : StronglyMeasurable (fun ω => ⨍ y in ball (0 : Vec d) 1, u n ω y ∂volume) := by
      simp only [average_eq]
      exact ((hu n).integral_prod_right (ν := volume.restrict (ball (0 : Vec d) 1))).const_smul
        ((volume.restrict (ball (0 : Vec d) 1)).real Set.univ)⁻¹
    exact (hu n).sub (hm.comp_measurable measurable_fst)
  refine ⟨fun ω x => limUnder atTop (fun n => v n ω x),
    (by exact StronglyMeasurable.limUnder (l := atTop) hv), ?_⟩
  have hfinball (R : ℝ) (hR : 0 < R) : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2.ne
  have hsum (k : ℕ) := by
    haveI := hfinball ((k : ℝ) + 1) (by positivity)
    exact ae_summable_spatial_sq_error Q hQ (volume.restrict (ball (0 : Vec d) ((k : ℝ) + 1)))
      D G hf
  filter_upwards [ae_all_iff.mpr hsum, hsample,
    ae_exists_global_spatial_weakPotential_of_closed_gradient hP Q hQ G hG,
    ae_spatialRealization_memLp_on_all_compacts hQ G,
    ae_all_iff.mpr (fun n => ae_spatialRealization_memLp_on_all_compacts hQ (D n))]
    with ω hS hsω hpot hGL hDL
  obtain ⟨hW, hL, -⟩ := hsω
  obtain ⟨w, hw, hwL, hw1⟩ := hpot
  have hconv (k : ℕ) : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((k : ℝ) + 1))),
      Tendsto (fun n => v n ω x) atTop (𝓝 (w x)) := by
    set R : ℝ := (k : ℝ) + 1 with hRdef
    have hR : 1 ≤ R := by rw [hRdef]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
    haveI := hfinball R hR0
    obtain ⟨C, hC, hpoinc⟩ := integral_sq_le_of_unitBall_integral_eq_zero hP hd R hR
    have hK := euclideanBall_subset_coordinateClosedBall (d := d) R hR0.le
    have hKm := Measure.restrict_mono_set volume hK
    have hcoord (H : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
        (hH : ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x : Vec d => H (translate x ω)) 2 (volume.restrict K)) :
        MemLp (fun x => (H (translate x ω)).ofLp) 2 (volume.restrict (ball (0 : Vec d) R)) := by
      apply memLp_pi_iff.mpr
      intro j
      exact ((hH _ (isCompact_closedBall (0 : Vec d) R)).mono_measure hKm).eval_piLp j
    have hvL (n : ℕ) : MemLp (v n ω) 2 (volume.restrict (ball 0 R)) :=
      ((hL n _ (isCompact_closedBall (0 : Vec d) R)).mono_measure hKm).sub (memLp_const _)
    have hweak (n : ℕ) : HasWeakGradient (ball 0 R) (fun x => v n ω x - w x)
        (fun x => (D n (translate x ω)).ofLp - (G (translate x ω)).ofLp) := by
      have h1 : HasWeakGradient (ball 0 R) (v n ω) (fun x => (D n (translate x ω)).ofLp) :=
        fun j => ((hasWeakGradient_sub_const Set.univ (hW n) _) j).restrict_subset
          (Set.subset_univ _) MeasurableSet.univ
      have h2 : HasWeakGradient (ball 0 R) w (fun x => (G (translate x ω)).ofLp) :=
        fun j => (hw j).restrict_subset (Set.subset_univ _) MeasurableSet.univ
      exact hasWeakGradient_sub_of_memLp _ _ _ _ _ (hvL n) (hwL R hR0)
        (hcoord (D n) (hDL n)) (hcoord G hGL) h1 h2
    have hsub1 : ball (0 : Vec d) 1 ⊆ ball 0 R := fun x hx => lt_of_lt_of_le hx hR
    have hmean (n : ℕ) : (∫ x in ball (0 : Vec d) 1, (v n ω x - w x)) = 0 := by
      haveI := hfinball 1 one_pos
      have hu1 : MemLp (u n ω) 2 (volume.restrict (ball (0 : Vec d) 1)) :=
        ((hL n _ (isCompact_closedBall (0 : Vec d) R)).mono_measure hKm).mono_measure
          (Measure.restrict_mono_set volume hsub1)
      have hv1 : Integrable (v n ω) (volume.restrict (ball (0 : Vec d) 1)) :=
        ((hvL n).mono_measure (Measure.restrict_mono_set volume hsub1)).integrable one_le_two
      have hw1' : Integrable w (volume.restrict (ball (0 : Vec d) 1)) :=
        ((hwL R hR0).mono_measure (Measure.restrict_mono_set volume hsub1)).integrable one_le_two
      rw [integral_sub hv1 hw1', hw1, sub_zero]
      exact integral_unitBall_sub_average_eq_zero hu1
    have hbound (n : ℕ) : ∫ x in ball (0 : Vec d) R, (v n ω x - w x) ^ 2 ≤
        C * ∫ x in ball (0 : Vec d) R, ‖D n (translate x ω) - G (translate x ω)‖ ^ 2 := by
      have h := hpoinc (fun x => v n ω x - w x)
        (fun x => (D n (translate x ω)).ofLp - (G (translate x ω)).ofLp) ((hvL n).sub (hwL R hR0))
        ((hcoord (D n) (hDL n)).sub (hcoord G hGL)) (hweak n) (hmean n)
      simpa only [ScalarPotentialApproximation.euclideanSq_ofLp_sub_eq_norm_sq] using h
    have hint (n : ℕ) : Integrable (fun x => (v n ω x - w x) ^ 2)
        (volume.restrict (ball (0 : Vec d) R)) :=
      (memLp_two_iff_integrable_sq ((hvL n).sub (hwL R hR0)).aestronglyMeasurable).mp
        ((hvL n).sub (hwL R hR0))
    have hs : Summable (fun n => ∫ x in ball (0 : Vec d) R, ‖(v n ω x - w x) ^ 2‖) := by
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _)
        (fun n => ?_) ((hS k).mul_left C)
      calc (∫ x in ball (0 : Vec d) R, ‖(v n ω x - w x) ^ 2‖)
          = ∫ x in ball (0 : Vec d) R, (v n ω x - w x) ^ 2 :=
            integral_congr_ae (ae_of_all _ fun x => Real.norm_of_nonneg (sq_nonneg _))
        _ ≤ _ := hbound n
    filter_upwards [ae_tendsto_zero_of_summable_integral_norm _ _ hint hs] with x hx
    have habs : Tendsto (fun n => |v n ω x - w x|) atTop (𝓝 0) := by
      have h := hx.sqrt
      simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using h
    exact tendsto_sub_nhds_zero_iff.mp ((tendsto_zero_iff_abs_tendsto_zero _).mpr habs)
  have hall : ∀ᵐ x ∂volume, Tendsto (fun n => v n ω x) atTop (𝓝 (w x)) := by
    have h := ae_all_iff.mpr (fun k : ℕ =>
      (ae_restrict_iff' (measurableSet_ball_zero (d := d) ((k : ℝ) + 1))).mp (hconv k))
    filter_upwards [h] with x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (euclideanNorm x)
    apply hx k
    change euclideanNorm (x - 0) < (k : ℝ) + 1
    rw [sub_zero]
    linarith
  have heq : (fun x => limUnder atTop (fun n => v n ω x)) =ᵐ[volume] w :=
    hall.mono fun x hx => hx.limUnder_eq
  refine ⟨?_, fun R hR => ?_, ?_⟩
  · exact hasWeakGradient_congr_ae isOpen_univ hw
      (by rw [Measure.restrict_univ]; exact heq.symm) (ae_eq_refl _)
  · exact (memLp_congr_ae (ae_restrict_of_ae heq)).mpr (hwL R hR)
  · rw [integral_congr_ae (ae_restrict_of_ae heq)]
    exact hw1

/-- The canonical scalar corrector gradient has a jointly measurable potential,
normalized by its unit-ball integral. Source: `paper/main.tex:693-698`. -/
theorem exists_measurable_canonical_scalar_potential (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : FieldPair d → Vec d → ℝ, StronglyMeasurable (Function.uncurry φ) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q,
        HasWeakGradient Set.univ (φ ω) (fun x => (spatialRealization
          (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) (x, ω)).ofLp) ∧
        (∀ R : ℝ, 0 < R → MemLp (φ ω) 2 (volume.restrict (ball 0 R))) ∧
        (∫ x in ball (0 : Vec d) 1, φ ω x) = 0 :=
  exists_measurable_unitBall_weakPotential hP (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) _ (canonicalCorrectorGradient Q i).property

open NormalizedSpatialRepresentativeSupport in
/-- For every source mollifier, radius and center, the canonical scalar
corrector has a jointly measurable representative normalized by its `ζ_R`
average, `paper/main.tex:754-758`. The predicate is the production twin of the
frozen scalar-corrector meaning, with the identical body. -/
theorem exists_normalizedCanonicalScalarCorrector (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) :
    ∃ φ : FieldPair d → Point d → ℝ,
      NormalizedScalarPhysicalLawTransportSupport.IsNormalizedCanonicalScalarCorrector
        Q i ζ R hR y φ := by
  obtain ⟨φ₀, hm, hφ₀⟩ := exists_measurable_canonical_scalar_potential hP Q i
  let m : FieldPair d → ℝ := fun ω =>
    ∫ x : Point d, sourceScaledMollifierKernel ζ R y x • φ₀ ω (WithLp.ofLp x)
  have hofLp : Measurable (WithLp.ofLp : Point d → Vec d) :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).measurable
  refine ⟨fun ω x => φ₀ ω (WithLp.ofLp x) - m ω, ?_, ?_⟩
  · have hm0 : Measurable (fun p : Vec d × FieldPair d => φ₀ p.2 p.1) :=
      hm.measurable.comp measurable_swap
    have hj : StronglyMeasurable (fun q : FieldPair d × Point d =>
        sourceScaledMollifierKernel ζ R y q.2 • φ₀ q.1 (WithLp.ofLp q.2)) :=
      ((continuous_sourceScaledMollifierKernel ζ R y).measurable.comp
        measurable_snd).stronglyMeasurable.smul
        (hm.comp_measurable (measurable_fst.prodMk (hofLp.comp measurable_snd)))
    have hmm : Measurable m := (hj.integral_prod_right' (ν := volume)).measurable
    exact hm0.sub (hmm.comp measurable_snd)
  · have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
    filter_upwards [hφ₀] with ω hω
    obtain ⟨hw, -, -⟩ := hω
    have hloc : LocallyIntegrable (φ₀ ω) volume :=
      locallyIntegrableOn_univ.mp (hw ⟨0, hd⟩).1
    have hlocP : LocallyIntegrable (fun x : Point d => φ₀ ω (WithLp.ofLp x)) volume := by
      have hmap : Measure.map (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)) volume =
          (volume : Measure (Vec d)) :=
        (PiLp.volume_preserving_ofLp (Fin d)).map_eq
      have h := (locallyIntegrable_map_homeomorph (PiLp.homeomorph 2 (fun _ : Fin d => ℝ))
        (f := φ₀ ω) (μ := (volume : Measure (Point d)))).mp (by rw [hmap]; exact hloc)
      exact h
    let ψ₀ : ScalarSpatialPotential d := ⟨fun x : Point d => φ₀ ω (WithLp.ofLp x), hlocP⟩
    have hLI : LocallyIntegrable (fun x : Point d => φ₀ ω (WithLp.ofLp x) - m ω) volume :=
      hlocP.sub (locallyIntegrable_const _)
    refine ⟨hLI, ?_, ?_⟩
    · exact hasWeakGradient_sub_const Set.univ hw (m ω)
    · rw [sourceMollifierNormalize_mk]
      apply Quotient.sound
      have hmean : mollifierMean (sourceScaledSpatialKernel ζ R y hR)
          (⟨fun x : Point d => φ₀ ω (WithLp.ofLp x) - m ω, hLI⟩ : ScalarSpatialPotential d) =
            0 :=
        integral_sourceMollifierCenteredRepresentative_eq_zero ζ R hR y ψ₀
      change (fun x => (φ₀ ω (WithLp.ofLp x) - m ω) - mollifierMean _ _) =ᵐ[volume] _
      rw [hmean]
      exact Filter.Eventually.of_forall fun x => sub_zero _

end EinsteinRelation.Correctors
