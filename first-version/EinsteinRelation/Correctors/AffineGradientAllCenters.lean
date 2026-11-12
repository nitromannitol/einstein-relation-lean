import EinsteinRelation.Correctors.GTAffineLocalGradient
import EinsteinRelation.Correctors.SpatialWeakTranslation
import EinsteinRelation.Correctors.SpatialBallTranslation
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

open Set

/-- Source: `paper/main.tex:727-731`. Translation of the established
radius-four affine gradient estimate, preserving all coefficient constants. -/
theorem scalar_corrector_affine_local_gradient_bound_at_center_of_GT
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) (hd : 2 ≤ d) (lam Λ K α : ℝ)
    (hlam : 0 < lam) (hΛ : 0 < Λ) (hK : 0 < K)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : Vec d) (a : Vec d → Mat d),
      EllipticBound (ball z 4) a lam Λ →
      (∀ i j, HolderBound (ball z 4) α (fun x => a x i j) K) →
      ∀ (u : Vec d → ℝ) (g : Vec d → Vec d) (i : Fin d) (c : ℝ),
        MemLp (fun x => u x - c) 2 (volume.restrict (ball z 4)) →
        WeakSolution (ball z 4) a
          (fun x => x i - z i + u x - c) (fun x => unitVector i + g x) →
        ∀ᵐ x ∂volume.restrict (ball z 1),
          euclideanNorm (unitVector i + g x) ≤ C * (1 +
            Real.sqrt (∫ y in ball z 4, |u y - c| ^ 2 ∂volume)) := by
  -- Obtain the constant C from the existing theorem for center 0
  obtain ⟨C, hC, hC'⟩ := scalar_corrector_affine_local_gradient_bound_of_GT
    h817 h832 h836 d hd lam Λ K α hlam hΛ hK hα hα1
  refine ⟨C, hC, ?_⟩
  intro z a ha hholder u g i c hu hw
  -- Define translated coefficient function
  let a' : Vec d → Mat d := fun x => a (x + z)
  -- Show EllipticBound for a' on ball 0 4
  have ha' : EllipticBound (ball (0 : Vec d) 4) a' lam Λ := by
    rcases ha with ⟨hmeas, hellip⟩
    refine ⟨?_, ?_⟩
    · intro i j
      exact (hmeas i j).comp (measurable_add_const z)
    · intro x hx
      have hx' : x + z ∈ ball z 4 := by
        simpa [ball, sub_add_cancel] using hx
      exact hellip (x + z) hx'
  -- Show HolderBound for a' on ball 0 4
  have hh' : ∀ i j, HolderBound (ball (0 : Vec d) 4) α (fun x => a' x i j) K := by
    intro i j
    have h := hholder i j
    rcases h with ⟨S, H, hS0, hH0, hsum, hsup, hhold⟩
    refine ⟨S, H, hS0, hH0, hsum, ?_, ?_⟩
    · intro x hx
      apply hsup (x + z)
      simpa [ball, sub_add_cancel] using hx
    · intro x hx y hy
      have hx' : x + z ∈ ball z 4 := by
        simpa [ball, sub_add_cancel] using hx
      have hy' : y + z ∈ ball z 4 := by
        simpa [ball, sub_add_cancel] using hy
      simpa [sub_add_add_cancel] using hhold (x + z) hx' (y + z) hy'
  -- Define translated u and g
  let u' : Vec d → ℝ := fun x => u (x + z)
  let g' : Vec d → Vec d := fun x => g (x + z)
  have hu' : MemLp (fun x => u' x - c) 2 (volume.restrict (ball (0 : Vec d) 4)) :=
    hu.comp_measurePreserving (measurePreserving_add_center_ball z 4)
  have hU : IsOpen (ball z 4) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  have hpre : (fun x : Vec d => x - -z) ⁻¹' ball z 4 = ball 0 4 := by
    ext x
    simp [ball, sub_neg_eq_add]
  have hfun : (fun x : Vec d => (x - -z) i - z i + u (x - -z) - c) =
      (fun x => x i + u' x - c) := by
    ext x
    simp [u', sub_neg_eq_add]
  have hw' : WeakSolution (ball (0 : Vec d) 4) a'
      (fun x => x i + u' x - c) (fun x => unitVector i + g' x) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · convert hw.1.comp_measurePreserving (measurePreserving_add_center_ball z 4) using 1
      ext x
      simp [u']
    · exact hw.2.1.comp_measurePreserving (measurePreserving_add_center_ball z 4)
    · intro j
      have ht := hasWeakPartialDerivative_translate hU (hw.2.2.1 j) (-z)
      rw [hpre, hfun] at ht
      simpa only [sub_neg_eq_add] using ht
    · have ht := hasWeakDivergence_translate hU hw.2.2.2 (-z)
      rw [hpre] at ht
      simpa only [sub_neg_eq_add] using ht
  have hb := hC' a' ha' hh' u' g' i c hu' hw'
  have hi : (∫ x in ball 0 4, |u' x - c| ^ 2 ∂volume) =
      ∫ x in ball z 4, |u x - c| ^ 2 ∂volume := by
    exact (measurePreserving_add_center_ball z 4).integral_comp
      (Homeomorph.addRight z).measurableEmbedding (fun x => |u x - c| ^ 2)
  rw [hi] at hb
  have hmp : MeasurePreserving (fun x : Vec d => x - z)
      (volume.restrict (ball z 1)) (volume.restrict (ball 0 1)) := by
    refine ⟨measurable_sub_const z, ?_⟩
    rw [← (measurePreserving_add_center_ball z 1).map_eq,
      Measure.map_map (measurable_sub_const z) (measurable_add_const z)]
    simp only [Function.comp_def, add_sub_cancel_right, Measure.map_id']
  have ht := hmp.quasiMeasurePreserving.ae hb
  simpa only [u', g', sub_add_cancel] using ht
end EinsteinRelation.Correctors
