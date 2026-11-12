import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.Topology.MetricSpace.Bounded

/-! # Exhausting bounded weak-equation domains

Source: `paper/main.tex:926–938`. Local spatial integrability and
weak equations on an increasing sequence of balls suffice for a whole-space
equation. This avoids imposing global spatial integrability on stationary
fields.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:926–938`. Weak equations checked on every
bounded ball hold on the whole spatial domain. -/
theorem hasWeakPartialDerivative_univ_of_ball {d : ℕ} (i : Fin d)
    (f g : Vec d → ℝ)
    (h : ∀ n : ℕ, HasWeakPartialDerivative (Metric.ball 0 ((n : ℝ) + 1)) i f g) :
    HasWeakPartialDerivative Set.univ i f g := by
  have h_loc_f : LocallyIntegrableOn f Set.univ volume := by
    refine locallyIntegrableOn_univ.mpr ?_
    rw [locallyIntegrable_iff]
    intro K hK
    have h_bdd : Bornology.IsBounded K := hK.isBounded
    rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_bdd with ⟨R, hR⟩
    rcases exists_nat_gt R with ⟨n, hn⟩
    have hR_lt : R < (n : ℝ) + 1 := by
      linarith
    have h_sub : K ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
      hR.trans (Metric.closedBall_subset_ball hR_lt)
    exact ((h n).1.integrableOn_compact_subset h_sub hK)
  have h_loc_g : LocallyIntegrableOn g Set.univ volume := by
    refine locallyIntegrableOn_univ.mpr ?_
    rw [locallyIntegrable_iff]
    intro K hK
    have h_bdd : Bornology.IsBounded K := hK.isBounded
    rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_bdd with ⟨R, hR⟩
    rcases exists_nat_gt R with ⟨n, hn⟩
    have hR_lt : R < (n : ℝ) + 1 := by
      linarith
    have h_sub : K ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
      hR.trans (Metric.closedBall_subset_ball hR_lt)
    exact ((h n).2.1.integrableOn_compact_subset h_sub hK)
  refine ⟨h_loc_f, h_loc_g, ?_⟩
  intro φ hφ
  have h_tsupport_compact : IsCompact (tsupport φ) := hφ.2.1
  have h_tsupport_bdd : Bornology.IsBounded (tsupport φ) := h_tsupport_compact.isBounded
  rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_tsupport_bdd with ⟨R, hR⟩
  rcases exists_nat_gt R with ⟨n, hn⟩
  have hR_lt : R < (n : ℝ) + 1 := by
    linarith
  have h_tsupport_sub_ball : tsupport φ ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_ball hR_lt)
  have hφ_ball : IsSpatialTest (Metric.ball 0 ((n : ℝ) + 1)) φ :=
    ⟨hφ.1, hφ.2.1, h_tsupport_sub_ball⟩
  have heq := (h n).2.2 φ hφ_ball
  have h_compl_f (x : Vec d) (hx : x ∉ Metric.ball 0 ((n : ℝ) + 1)) :
      f x * coordinateDerivative i φ x = 0 := by
    have hx_not_tsupport : x ∉ tsupport φ := fun hx' => hx (h_tsupport_sub_ball hx')
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx_not_tsupport,
      ContinuousLinearMap.zero_apply, mul_zero]
  have h_compl_g (x : Vec d) (hx : x ∉ Metric.ball 0 ((n : ℝ) + 1)) :
      g x * φ x = 0 := by
    have hx_not_tsupport : x ∉ tsupport φ := fun hx' => hx (h_tsupport_sub_ball hx')
    rw [image_eq_zero_of_notMem_tsupport hx_not_tsupport, mul_zero]
  calc
    (∫ x in Set.univ, f x * coordinateDerivative i φ x) =
        (∫ x, f x * coordinateDerivative i φ x) := by rw [setIntegral_univ]
    _ = (∫ x in Metric.ball 0 ((n : ℝ) + 1), f x * coordinateDerivative i φ x) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) h_compl_f).symm
    _ = -(∫ x in Metric.ball 0 ((n : ℝ) + 1), g x * φ x) := heq
    _ = -(∫ x, g x * φ x) :=
      congrArg Neg.neg (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) h_compl_g)
    _ = -(∫ x in Set.univ, g x * φ x) := by rw [setIntegral_univ]

/-- Source: `paper/main.tex:926–938`. The exhaustion step for divergence. -/
theorem hasWeakDivergence_univ_of_ball {d : ℕ} (F : Vec d → Vec d) (g : Vec d → ℝ)
    (h : ∀ n : ℕ, HasWeakDivergence (Metric.ball 0 ((n : ℝ) + 1)) F g) :
    HasWeakDivergence Set.univ F g := by
  have h_loc_F (j : Fin d) : LocallyIntegrableOn (fun x => F x j) Set.univ volume := by
    refine locallyIntegrableOn_univ.mpr ?_
    rw [locallyIntegrable_iff]
    intro K hK
    have h_bdd : Bornology.IsBounded K := hK.isBounded
    rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_bdd with ⟨R, hR⟩
    rcases exists_nat_gt R with ⟨n, hn⟩
    have hR_lt : R < (n : ℝ) + 1 := by
      linarith
    have h_sub : K ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
      hR.trans (Metric.closedBall_subset_ball hR_lt)
    exact ((h n).1 j).integrableOn_compact_subset h_sub hK
  have h_loc_g : LocallyIntegrableOn g Set.univ volume := by
    refine locallyIntegrableOn_univ.mpr ?_
    rw [locallyIntegrable_iff]
    intro K hK
    have h_bdd : Bornology.IsBounded K := hK.isBounded
    rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_bdd with ⟨R, hR⟩
    rcases exists_nat_gt R with ⟨n, hn⟩
    have hR_lt : R < (n : ℝ) + 1 := by
      linarith
    have h_sub : K ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
      hR.trans (Metric.closedBall_subset_ball hR_lt)
    exact ((h n).2.1).integrableOn_compact_subset h_sub hK
  refine ⟨h_loc_F, h_loc_g, ?_⟩
  intro φ hφ
  have h_tsupport_compact : IsCompact (tsupport φ) := hφ.2.1
  have h_tsupport_bdd : Bornology.IsBounded (tsupport φ) := h_tsupport_compact.isBounded
  rcases (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp h_tsupport_bdd with ⟨R, hR⟩
  rcases exists_nat_gt R with ⟨n, hn⟩
  have hR_lt : R < (n : ℝ) + 1 := by
    linarith
  have h_tsupport_sub_ball : tsupport φ ⊆ Metric.ball 0 ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_ball hR_lt)
  have hφ_ball : IsSpatialTest (Metric.ball 0 ((n : ℝ) + 1)) φ :=
    ⟨hφ.1, hφ.2.1, h_tsupport_sub_ball⟩
  have heq := (h n).2.2 φ hφ_ball
  have h_compl_F (x : Vec d) (hx : x ∉ Metric.ball 0 ((n : ℝ) + 1)) :
      dot (F x) (gradient φ x) = 0 := by
    have hx_not_tsupport : x ∉ tsupport φ := fun hx' => hx (h_tsupport_sub_ball hx')
    have h_grad_zero : gradient φ x = 0 := by
      ext i
      simp only [gradient, coordinateDerivative,
        fderiv_of_notMem_tsupport (𝕜 := ℝ) hx_not_tsupport,
        ContinuousLinearMap.zero_apply, Pi.zero_apply]
    rw [h_grad_zero]
    simp [dot]
  have h_compl_g (x : Vec d) (hx : x ∉ Metric.ball 0 ((n : ℝ) + 1)) :
      g x * φ x = 0 := by
    have hx_not_tsupport : x ∉ tsupport φ := fun hx' => hx (h_tsupport_sub_ball hx')
    rw [image_eq_zero_of_notMem_tsupport hx_not_tsupport, mul_zero]
  calc
    (∫ x in Set.univ, dot (F x) (gradient φ x)) =
        (∫ x, dot (F x) (gradient φ x)) := by rw [setIntegral_univ]
    _ = (∫ x in Metric.ball 0 ((n : ℝ) + 1), dot (F x) (gradient φ x)) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) h_compl_F).symm
    _ = -(∫ x in Metric.ball 0 ((n : ℝ) + 1), g x * φ x) := heq
    _ = -(∫ x, g x * φ x) :=
      congrArg Neg.neg (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) h_compl_g)
    _ = -(∫ x in Set.univ, g x * φ x) := by rw [setIntegral_univ]

/-- Source: `paper/main.tex:926–938`. Whole-space gradient from
bounded-ball weak gradients. -/
theorem hasWeakGradient_univ_of_ball {d : ℕ} (f : Vec d → ℝ) (G : Vec d → Vec d)
    (h : ∀ n : ℕ, HasWeakGradient (Metric.ball 0 ((n : ℝ) + 1)) f G) :
    HasWeakGradient Set.univ f G := fun i =>
  hasWeakPartialDerivative_univ_of_ball i f (fun x => G x i) (fun n => h n i)

/-- Source: `paper/main.tex:926–938`. Whole-space row divergence from
bounded-ball weak row-divergence equations. -/
theorem hasWeakRowDivergence_univ_of_ball {d : ℕ}
    (S : Vec d → Mat d) (g : Vec d → Vec d)
    (h : ∀ n : ℕ, HasWeakRowDivergence (Metric.ball 0 ((n : ℝ) + 1)) S g) :
    HasWeakRowDivergence Set.univ S g := fun i =>
  hasWeakDivergence_univ_of_ball (fun x k => S x i k) (fun x => g x i) (fun n => h n i)

end EinsteinRelation.Correctors
