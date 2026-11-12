import EinsteinRelation.Correctors.SpatialBallLocalL2Support
import EinsteinRelation.Correctors.PoissonLocalBound
import EinsteinRelation.Correctors.SpatialBallTranslation
import EinsteinRelation.Correctors.SpatialWeakTranslation
import EinsteinRelation.Calculus.WeakGradientSubtraction
import EinsteinRelation.Correctors.WeakGradientCentering

open MeasureTheory

/-! ## Helper lemmas -/

namespace EinsteinRelation.Correctors

open External.AKM External.GilbargTrudinger

/-- Source: `paper/main.tex:733-745`. Translation and scalar gauge invariance
of the established local Poisson bound. -/
theorem poisson_local_bound_at_center_of_GT
    (h817 : LocalBoundednessEstimate) (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : Vec d → ℝ) (g F : Vec d → Vec d),
      HasWeakGradient Set.univ u g →
      HasWeakDivergence Set.univ (fun x => g x - F x) (fun _ => 0) →
      Measurable F →
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) →
      (∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R))) →
      ∀ (z : Vec d) (c M : ℝ), 0 < M →
      (∀ᵐ x ∂volume.restrict (ball z 1), euclideanNorm (F x) ≤ M) →
      ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
        |u x - c| ≤ C * (Real.sqrt (∫ y in ball z 1, |u y - c| ^ 2) + M) := by
  obtain ⟨C, hCpos, hC⟩ := poisson_local_bound_of_GT h817 d hd
  refine ⟨C, hCpos, ?_⟩
  intro u g F hw hJ hFmeas hu hg z c M hM hFbound
  -- Translated functions: shift by z and subtract c from u
  let u0 : Vec d → ℝ := fun x => u (x + z) - c
  let g0 : Vec d → Vec d := fun x => g (x + z)
  let F0 : Vec d → Vec d := fun x => F (x + z)
  -- 1. HasWeakGradient for u0, g0
  have hw0 : HasWeakGradient Set.univ u0 g0 := by
    have hw_translated : HasWeakGradient Set.univ (fun x => u (x + z)) (fun x => g (x + z)) :=
      hasWeakGradient_translation u g hw z
    simpa [u0] using hasWeakGradient_sub_const Set.univ hw_translated c
  -- 2. HasWeakDivergence for g0 - F0
  have hJ0 : HasWeakDivergence Set.univ (fun x => g0 x - F0 x) (fun _ => 0) := by
    have hJ_translated : HasWeakDivergence Set.univ (fun x => (g - F) (x + z)) (fun _ => 0) := by
      have := hasWeakDivergence_translate isOpen_univ hJ (-z)
      simpa [sub_eq_add_neg, add_comm] using this
    simpa [g0, F0] using hJ_translated
  -- 3. Measurable F0
  have hF0meas : Measurable F0 :=
    hFmeas.comp (measurable_add_const z)
  -- 4. MemLp conditions for u0, g0 on ball 0 R
  have hu0 : ∀ R : ℝ, 0 < R → MemLp u0 2 (volume.restrict (ball (0 : Vec d) R)) := by
    intro R hR
    have h_mem : MemLp (fun x => u (x + z)) 2 (volume.restrict (ball (0 : Vec d) R)) :=
      memLp_two_on_euclidean_balls_translation u hu z R hR
    haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
      isFiniteMeasure_restrict_euclideanBall 0 R hR
    have h_const : MemLp (fun _ : Vec d => c) 2 (volume.restrict (ball (0 : Vec d) R)) :=
      memLp_const c
    dsimp [u0]
    exact h_mem.sub h_const
  have hg0 : ∀ R : ℝ, 0 < R → MemLp g0 2 (volume.restrict (ball (0 : Vec d) R)) := by
    intro R hR
    exact memLp_two_on_euclidean_balls_translation g hg z R hR
  -- 5. Bound on F0 on ball 0 1, translated from the hypothesis on ball z 1
  have hF0bound : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) 1), euclideanNorm (F0 x) ≤ M := by
    have hmp := measurePreserving_add_center_ball z 1
    simpa [F0] using hmp.quasiMeasurePreserving.ae hFbound
  -- Apply the existing theorem at the origin
  have h_origin := hC u0 g0 F0 hw0 hJ0 hF0meas M hM hF0bound (hu0 1 (by norm_num)) (hg0 1 (by norm_num))
  -- Integral equality: ∫ y in ball 0 1, |u0 y| ^ 2 = ∫ y in ball z 1, |u y - c| ^ 2
  have h_int_eq : (∫ y in ball (0 : Vec d) 1, |u0 y| ^ 2) = (∫ y in ball z 1, |u y - c| ^ 2) := by
    have hmp := measurePreserving_add_center_ball z 1
    have h := hmp.integral_comp (Homeomorph.addRight z).measurableEmbedding (fun x => |u x - c| ^ 2)
    simpa [u0, sq_abs] using h
  -- Rewrite h_origin using h_int_eq
  have h_origin' : ∀ᵐ x ∂volume.restrict (ball (0 : Vec d) (1 / 4)),
      |u (x + z) - c| ≤ C * (Real.sqrt (∫ y in ball z 1, |u y - c| ^ 2) + M) := by
    filter_upwards [h_origin] with x hx
    rw [h_int_eq] at hx
    exact hx
  -- Translate back from ball 0 (1/4) to ball z (1/4) via x ↦ x - z
  have h_result : ∀ᵐ x ∂volume.restrict (ball z (1 / 4)),
      |u x - c| ≤ C * (Real.sqrt (∫ y in ball z 1, |u y - c| ^ 2) + M) := by
    let e : (Vec d) ≃ᵐ (Vec d) :=
      { toFun := fun x => x + z
        invFun := fun x => x - z
        left_inv := by intro x; simp
        right_inv := by intro x; simp
        measurable_toFun := (measurable_add_const z)
        measurable_invFun := (measurable_sub_const z) }
    have hmp_center := measurePreserving_add_center_ball z (1 / 4)
    have hmp_e : MeasurePreserving e (volume.restrict (ball (0 : Vec d) (1 / 4))) (volume.restrict (ball z (1 / 4))) := by
      simpa [e] using hmp_center
    have hmp_inv : MeasurePreserving (fun x : Vec d => x - z)
        (volume.restrict (ball z (1 / 4))) (volume.restrict (ball (0 : Vec d) (1 / 4))) := by
      simpa [e] using hmp_e.symm
    simpa [sub_add_cancel] using
      hmp_inv.quasiMeasurePreserving.ae h_origin'
  exact h_result
end EinsteinRelation.Correctors
