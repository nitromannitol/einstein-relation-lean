import EinsteinFull.Calculus.S4ReducedCoefficientSupport

open EinsteinRelation MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull

theorem c25_reduced_force_potential_bounded {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) :
    Measurable (fun x : Vec d =>
      lam * forcedDrift (reducedCoefficient ω) i 0 x i +
      (lam ^ 2 / 2) * reducedCoefficient ω x i i) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Vec d,
      |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
        (lam ^ 2 / 2) * reducedCoefficient ω x i i| ≤ M := by
  obtain ⟨hc, _, ⟨A, hA⟩, _, hm, ⟨B, hB⟩⟩ := reduced_svHypotheses hΛ hω i 0
  constructor
  · exact (measurable_const.mul (measurable_pi_apply i |>.comp hm)).add
      (measurable_const.mul (((continuous_apply i).comp ((continuous_apply i).comp hc)).measurable))
  · refine ⟨|lam| * |B| + |lam ^ 2 / 2| * |A|, by positivity, ?_⟩
    intro x
    calc
      |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
          (lam ^ 2 / 2) * reducedCoefficient ω x i i| ≤
          |lam| * |forcedDrift (reducedCoefficient ω) i 0 x i| +
          |lam ^ 2 / 2| * |reducedCoefficient ω x i i| := by
            rw [← abs_mul, ← abs_mul]
            exact abs_add_le _ _
      _ ≤ |lam| * |B| + |lam ^ 2 / 2| * |A| := by
        exact add_le_add (mul_le_mul_of_nonneg_left ((hB x i).trans (le_abs_self B)) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left ((hA x i i).trans (le_abs_self A)) (abs_nonneg _))

theorem c25_reduced_force_path_potential_integrable {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (γ : Path d) (T : ℝ≥0),
      IntegrableOn (fun s : ℝ =>
        lam * forcedDrift (reducedCoefficient ω) i 0 (γ s.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ s.toNNReal) i i)
        (Set.Ioc (0 : ℝ) (T : ℝ)) ∧
      |∫ s in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ s.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ s.toNNReal) i i)| ≤ M * (T : ℝ) := by
  obtain ⟨hm, M, hM, hb⟩ := c25_reduced_force_potential_bounded hΛ hω i lam
  refine ⟨M, hM, fun γ T => ?_⟩
  have hmeas : Measurable (fun s : ℝ =>
      lam * forcedDrift (reducedCoefficient ω) i 0 (γ s.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ s.toNNReal) i i) :=
    hm.comp (γ.continuous.measurable.comp continuous_real_toNNReal.measurable)
  have hfinite : volume (Set.Ioc (0 : ℝ) (T : ℝ)) < ∞ := by simp
  constructor
  · exact IntegrableOn.of_bound hfinite hmeas.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs] using hb (γ s.toNNReal))
  · have h := norm_setIntegral_le_of_norm_le_const (f := fun s : ℝ =>
        lam * forcedDrift (reducedCoefficient ω) i 0 (γ s.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ s.toNNReal) i i) (C := M) hfinite
        (fun s _ => by simpa only [Real.norm_eq_abs] using hb (γ s.toNNReal))
    simpa only [Real.norm_eq_abs, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero] using h

theorem c25_reduced_force_path_weight_measurable {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (T : ℝ≥0) :
    Measurable (fun γ : Path d => Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)))) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ γ : Path d,
      Real.exp (-M * (T : ℝ)) ≤ Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ∧
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ≤
        Real.exp (M * (T : ℝ)) := by
  obtain ⟨hm, _⟩ := c25_reduced_force_potential_bounded hΛ hω i lam
  have heval : Continuous (fun p : Path d × ℝ => p.1 p.2.toNNReal) :=
    (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))
  have hjoint : Measurable (fun p : Path d × ℝ =>
      lam * forcedDrift (reducedCoefficient ω) i 0 (p.1 p.2.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (p.1 p.2.toNNReal) i i) :=
    hm.comp heval.measurable
  constructor
  · exact Real.continuous_exp.measurable.comp
      (hjoint.stronglyMeasurable.integral_prod_right'.measurable.neg)
  · obtain ⟨M, hM, hb⟩ := c25_reduced_force_path_potential_integrable hΛ hω i lam
    refine ⟨M, hM, fun γ => ?_⟩
    have h := (abs_le.mp (hb γ T).2)
    constructor <;> apply Real.exp_le_exp.mpr <;> linarith

theorem c25_reduced_force_localized_weight_bounds {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (T : ℝ≥0) :
    Measurable (fun γ : Path d =>
      Real.exp (lam * (γ T i - γ 0 i)) *
        Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
          (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)))) ∧
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) (γ : Path d), |γ T i - γ 0 i| ≤ R →
      Real.exp (-|lam| * R - M * (T : ℝ)) ≤
        Real.exp (lam * (γ T i - γ 0 i)) *
          Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
              (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ∧
      Real.exp (lam * (γ T i - γ 0 i)) *
          Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
              (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ≤
        Real.exp (|lam| * R + M * (T : ℝ)) := by
  obtain ⟨hm, M, hM, hb⟩ := c25_reduced_force_path_weight_measurable hΛ hω i lam T
  have he : Measurable (fun γ : Path d => Real.exp (lam * (γ T i - γ 0 i))) := by
    apply Real.continuous_exp.measurable.comp
    have ht : Continuous (fun γ : Path d => γ T i) :=
      (continuous_apply i).comp (continuous_eval_const T)
    have hz : Continuous (fun γ : Path d => γ 0 i) :=
      (continuous_apply i).comp (continuous_eval_const 0)
    exact measurable_const.mul (ht.sub hz).measurable
  refine ⟨he.mul hm, M, hM, ?_⟩
  intro R γ hR
  have hprod : |lam * (γ T i - γ 0 i)| ≤ |lam| * R := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hR (abs_nonneg lam)
  have hprod' := abs_le.mp hprod
  obtain ⟨hl, hu⟩ := hb γ
  constructor
  · have harg : -|lam| * R - M * (T : ℝ) =
        -(|lam| * R) + (-M * (T : ℝ)) := by ring
    rw [harg, Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr hprod'.1) hl (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _))
  · rw [Real.exp_add]
    exact mul_le_mul (Real.exp_le_exp.mpr hprod'.2) hu (le_of_lt (Real.exp_pos _))
      (le_of_lt (Real.exp_pos _))


theorem c25_reduced_force_path_weight_stronglyAdapted {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
    {ω : FieldPair d} (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) :
    let V := fun y : Vec d => lam * forcedDrift (reducedCoefficient ω) i 0 y i +
      (lam ^ 2 / 2) * reducedCoefficient ω y i i
    StronglyAdapted (pathFiltration d) (fun t : ℝ≥0 => fun γ : Path d =>
      Real.exp (-(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), V (γ u.toNNReal)))) := by
  dsimp only
  intro t
  letI : MeasurableSpace (Path d) := pathFiltration d t
  have hcoord (s : ℝ≥0) (hs : s ≤ t) : Measurable (fun γ : Path d => γ s) := by
    have ha := (Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) s).measurable
    exact ha.mono ((pathFiltration d).mono hs) le_rfl
  have heval : Measurable (fun p : ℝ × Path d => p.2 (min p.1.toNNReal t)) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (u := fun (u : ℝ) (γ : Path d) => γ (min u.toNNReal t)) ?_ ?_
    · intro γ
      exact γ.continuous.comp (continuous_real_toNNReal.min continuous_const)
    · intro u
      exact hcoord _ (min_le_right _ _)
  have hm := (c25_reduced_force_potential_bounded hΛ hω i lam).1
  have hjoint : Measurable (fun p : Path d × ℝ =>
      lam * forcedDrift (reducedCoefficient ω) i 0 (p.1 (min p.2.toNNReal t)) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (p.1 (min p.2.toNNReal t)) i i) :=
    hm.comp (heval.comp measurable_swap)
  have hint := hjoint.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioc (0 : ℝ) (t : ℝ)))
  apply Measurable.stronglyMeasurable
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  convert hint.measurable using 1
  funext γ
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  have hu' : u.toNNReal ≤ t := by
    exact Real.toNNReal_le_iff_le_coe.2 hu.2
  simp only [min_eq_left hu']

end EinsteinFull
