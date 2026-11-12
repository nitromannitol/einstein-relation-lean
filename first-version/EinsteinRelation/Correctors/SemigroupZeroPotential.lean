import EinsteinRelation.Correctors.SemigroupZeroEnergy
import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationFiniteTime

/-! # Finite-time potentials with lower endpoint zero

Source: `paper/main.tex:800–808`. Local energy through zero permits integration
of the actual parabolic gradient from zero. No value of the gradient at time
zero is prescribed or used.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem initial_time_union {T : ℝ} (hT : 0 < T) :
    (⋃ n : ℕ, Set.Ioo (T / ((n : ℝ)+2)) T) = Set.Ioo 0 T := by
  ext t
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, ht⟩
    exact ⟨(div_pos hT (by positivity)).trans ht.1,ht.2⟩
  · intro ht
    obtain ⟨n, hn⟩ := exists_nat_gt (T/t)
    refine Set.mem_iUnion.mpr ⟨n,?_,ht.2⟩
    apply (div_lt_iff₀ (by positivity)).2
    have hh := (div_lt_iff₀ ht.1).mp hn
    nlinarith only [hh,ht.1]

/-- Joint measurability and the spatial weak equations extend to the full
initial strip by countable exhaustion. Source: `paper/main.tex:800–808`. -/
theorem semigroup_initial_strip_data
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    AEStronglyMeasurable u (volume.restrict (Set.Ioo 0 T ×ˢ originBall d R)) ∧
    AEStronglyMeasurable G (volume.restrict (Set.Ioo 0 T ×ˢ originBall d R)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T),
        HasWeakGradient (originBall d R) (fun x => u (t,x)) (fun x => G (t,x)) := by
  have hs (n : ℕ) := hsol.2.1 (T/((n:ℝ)+2)) T R
    (div_pos hT (by positivity))
    (div_lt_self hT (by have := Nat.cast_nonneg (α := ℝ) n; linarith)) hR
  have hc := initial_time_union hT
  have hp : Set.Ioo 0 T ×ˢ originBall d R =
      ⋃ n : ℕ, Set.Ioo (T/((n:ℝ)+2)) T ×ˢ originBall d R := by
    rw [← hc, Set.iUnion_prod_const]
  refine ⟨?_,?_,?_⟩
  · rw [hp]
    exact aestronglyMeasurable_iUnion_iff.mpr fun n => (hs n).1.aestronglyMeasurable
  · rw [hp]
    exact aestronglyMeasurable_iUnion_iff.mpr fun n => (hs n).2.1
  · rw [← hc]
    exact (ae_restrict_iUnion_iff _ _).mpr fun n => (hs n).2.2.2.1

/-- A bounded actual semigroup has the local L² energy class through zero.
Source: `paper/main.tex:800–808,842–844`. -/
theorem semigroup_initial_strip_memLp
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    MemLp u 2 (volume.restrict (Set.Ioo 0 T ×ˢ originBall d R)) ∧
    MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo 0 T ×ˢ originBall d R)) := by
  let S := Set.Ioo 0 T ×ˢ originBall d R
  have hc := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  letI : IsFiniteMeasure (volume.restrict S) := by
    dsimp only [S]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    infer_instance
  obtain ⟨hum,hGm,_⟩ := semigroup_initial_strip_data hsol hT hR
  have hS : MeasurableSet S := measurableSet_Ioo.prod (by
    unfold originBall euclideanNorm euclideanSq dot
    exact measurableSet_lt (by fun_prop) measurable_const)
  have hu : MemLp u ∞ (volume.restrict S) := memLp_top_of_bound hum B (by
    filter_upwards [ae_restrict_mem hS] with z hz
    simpa only [Real.norm_eq_abs] using hb z.1 hz.1.1 z.2)
  refine ⟨hu.mono_exponent le_top,?_⟩
  have he := semigroup_gradient_energy_integrable_through_zero hK hsol hb hT hR
  apply (memLp_two_iff_integrable_sq _).mpr
  · simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using he
  · apply (Real.continuous_sqrt.comp_aestronglyMeasurable _)
    simpa only [euclideanSq, dot] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun j _ =>
        ((continuous_apply j).comp_aestronglyMeasurable hGm).mul
          ((continuous_apply j).comp_aestronglyMeasurable hGm))

/-- The actual weak PDE and its local energy class hold on the entire initial
strip. Source: `paper/main.tex:800–808,842–844`. -/
theorem semigroup_parabolic_from_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T R : ℝ} (hT : 0 < T) (hR : 0 < R) :
    IsParabolicSolution A (Set.Ioo 0 T) (originBall d R) u G := by
  obtain ⟨hu,hG⟩ := semigroup_initial_strip_memLp hK hsol hb hT hR
  obtain ⟨_,hGm,hw⟩ := semigroup_initial_strip_data hsol hT hR
  refine ⟨hu,hGm,hG,hw,?_⟩
  intro ψ hψ hψc hsupp
  have hs : tsupport ψ ⊆ Set.Ioo 0 T ×ˢ originBall d R := by
    simpa only [interior_Ioo] using hsupp
  obtain ⟨c,hc,hct⟩ := hψc.isCompact.exists_forall_le'
    continuous_fst.continuousOn (fun z hz => (hs hz).1.1)
  let a := min (c/2) (T/2)
  have ha : 0 < a := lt_min (half_pos hc) (half_pos hT)
  have haT : a < T := (min_le_right _ _).trans_lt (half_lt_self hT)
  have hsmall : tsupport ψ ⊆ Set.Ioo a T ×ˢ originBall d R := by
    intro z hz
    exact ⟨⟨((min_le_left _ _).trans_lt (half_lt_self hc)).trans_le (hct z hz),
      (hs hz).1.2⟩,(hs hz).2⟩
  let F := fun z : ℝ × Vec d => -(u z) * fderiv ℝ ψ z (1,0) +
    dot ((A z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0,unitVector j))
  have hz (z : ℝ × Vec d) (hnot : z ∉ tsupport ψ) : F z = 0 := by
    simp [F, fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot, dot]
  have hbig : (∫ z in Set.Ioo 0 T ×ˢ originBall d R, F z) = ∫ z, F z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hn => hz z (fun h => hn (hs h)))
  have hsm : (∫ z in Set.Ioo a T ×ˢ originBall d R, F z) = ∫ z, F z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hn => hz z (fun h => hn (hsmall h)))
  change (∫ z in Set.Ioo 0 T ×ˢ originBall d R, F z) = 0
  rw [hbig, ← hsm]
  exact (hsol.2.1 a T R ha haT hR).2.2.2.2 ψ hψ hψc
    (by simpa only [interior_Ioo] using hsmall)

/-- Integration from zero yields the literal spatial weak potential of the
actual gradient flow. Source: `paper/main.tex:800–808`. -/
theorem semigroup_integrated_gradient_from_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {B : ℝ} (hb : ∀ t, 0 < t → ∀ x, |u (t,x)| ≤ B)
    {T : ℝ} (hT : 0 < T) :
    HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo 0 T, u (t,x))
      (fun x j => ∫ t in Set.Ioo 0 T, G (t,x) j) := by
  apply hasWeakGradient_univ_of_balls
  intro n
  let R : ℝ := (n:ℝ)+1
  have hR : 0 < R := by positivity
  have hc := isCompact_closure_originBall d R
  letI : IsFiniteMeasure (volume.restrict (originBall d R)) := isFiniteMeasure_restrict.mpr
    (ne_top_of_le_ne_top (hc.measure_ne_top (μ := volume)) (measure_mono subset_closure))
  have hh := parabolicSolution_integrated_gradient
    (semigroup_parabolic_from_zero hK hsol hb hT hR)
  simpa only [R, originBall, ball, sub_zero] using hh

end EinsteinRelation.Correctors
