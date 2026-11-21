import EinsteinFull.Regeneration.DowncrossingMaximum
import EinsteinFull.Regeneration.ExponentialTailMoment

/-!
# Exponential maximum moment before downcrossing

A uniform exponential backward-crossing estimate gives the uniform exponential
moment of the running maximum at a finite downcrossing in GMP (5.25).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstHittingBelow coordinateMaximum

/-- Scaled running maximum at the first downcrossing, with value zero if it never occurs. -/
noncomputable def downcrossingMaximum {d : ℕ} (lam R : ℝ) (i : Fin d) (γ : Path d) : ℝ :=
  {γ | firstHittingBelow γ i (-R) ≠ ⊤}.indicator
    (fun γ => lam * coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal) γ

/-- The first lower crossing is measurable as a function of the path. -/
theorem measurable_first_downcrossing {d : ℕ} (R : ℝ) (i : Fin d) :
    Measurable (fun γ : Path d => firstHittingBelow γ i (-R)) := by
  have hp : Measurable (fun γ : Path d => ((-R : ℝ), γ)) :=
    measurable_const.prodMk measurable_id
  exact (measurable_firstHittingBelow (d := d) i).comp hp

/-- The running maximum at the first lower crossing is measurable. -/
theorem measurable_maximum_at_downcrossing {d : ℕ} (R : ℝ) (i : Fin d) :
    Measurable (fun γ : Path d => coordinateMaximum γ i
      (firstHittingBelow γ i (-R)).toNNReal) := by
  exact (measurable_coordinateMaximum i).comp
    ((measurable_first_downcrossing R i).ennreal_toNNReal.prodMk measurable_id)

/-- The stopped scaled maximum is measurable. -/
theorem measurable_downcrossingMaximum {d : ℕ} (lam R : ℝ) (i : Fin d) :
    Measurable (downcrossingMaximum lam R i) := by
  have hm : Measurable (fun γ : Path d => lam * coordinateMaximum γ i
      (firstHittingBelow γ i (-R)).toNNReal) :=
    measurable_const.mul (measurable_maximum_at_downcrossing R i)
  have hE : MeasurableSet {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤} :=
    (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl
  exact hm.indicator hE

/-- The stopped scaled maximum is nonnegative for a nonnegative scale. -/
theorem downcrossingMaximum_nonneg {d : ℕ} (lam R : ℝ) (i : Fin d)
    (hlam : 0 ≤ lam) (γ : Path d) : 0 ≤ downcrossingMaximum lam R i γ := by
  by_cases h : firstHittingBelow γ i (-R) ≠ ⊤
  · rw [downcrossingMaximum, Set.indicator_of_mem (show γ ∈ {γ | firstHittingBelow γ i (-R) ≠ ⊤} from h)]
    exact mul_nonneg hlam (coordinateMaximum_nonneg γ i _)
  · rw [downcrossingMaximum, Set.indicator_of_notMem (show γ ∉ {γ | firstHittingBelow γ i (-R) ≠ ⊤} from h)]

/-- A uniform backward-crossing estimate bounds the scaled running maximum. -/
theorem downcrossing_maximum_tail {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlam : 0 < lam) (h1 : lam ≤ 1)
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (i : Fin d) (R κ C : ℝ)
    (hR : 0 ≤ R) (hκ : 0 < κ) (hC : 0 ≤ C)
    (hback : ∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
      ENNReal.ofReal (C * Real.exp (-κ * lam * u))) :
    ∀ t : ℝ, 0 ≤ t → (G.pathLaw x).real {γ | t ≤ downcrossingMaximum lam R i γ} ≤
      max C 1 * Real.exp (-((κ / 2) * t)) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let P := G.pathLaw x
  let S := downcrossingMaximum lam R i
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    simpa only [mul_zero, neg_zero, Real.exp_zero, mul_one] using
      (measureReal_le_one : P.real {γ | (0 : ℝ) ≤ S γ} ≤ 1).trans (le_max_right C 1)
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let b : ℝ := t / (2 * lam)
    have hb : 0 < b := by dsimp [b]; positivity
    have hsub : {γ | t ≤ S γ} ⊆ {γ | firstHittingBelow γ i (-R) ≠ ⊤ ∧
        b < coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal} := by
      intro γ hγ
      change t ≤ downcrossingMaximum lam R i γ at hγ
      have hf : firstHittingBelow γ i (-R) ≠ ⊤ := by
        intro htop
        rw [downcrossingMaximum, Set.indicator_of_notMem
          (show γ ∉ {γ | firstHittingBelow γ i (-R) ≠ ⊤} from fun hf => hf htop)] at hγ
        linarith
      refine ⟨hf, ?_⟩
      rw [downcrossingMaximum, Set.indicator_of_mem
        (show γ ∈ {γ | firstHittingBelow γ i (-R) ≠ ⊤} from hf)] at hγ
      dsimp [b]
      apply (div_lt_iff₀ (by positivity : 0 < 2 * lam)).2
      nlinarith
    have hbound := maximum_before_downcrossing_le_of_uniform_crossing hd ω lam Λ hΛ hω
      hlam.le h1 G x i R b (ENNReal.ofReal (C * Real.exp (-κ * lam * (R + b))))
      (fun y => by simpa only [neg_add_rev] using hback y (R + b) (add_nonneg hR hb.le))
    have hμ : P.real {γ | t ≤ S γ} ≤ C * Real.exp (-κ * lam * (R + b)) := by
      have hle := (measure_mono hsub).trans hbound
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      simpa only [measureReal_def, ENNReal.toReal_ofReal
        (mul_nonneg hC (Real.exp_pos _).le)] using hreal
    calc
      _ ≤ C * Real.exp (-κ * lam * (R + b)) := hμ
      _ ≤ max C 1 * Real.exp (-((κ / 2) * t)) := by
        have he : -κ * lam * (R + b) ≤ -((κ / 2) * t) := by
          have heq : -κ * lam * (R + b) = -(κ * lam * R) - (κ / 2) * t := by
            dsimp [b]
            field_simp
            ring
          rw [heq]
          have hn : 0 ≤ κ * lam * R := mul_nonneg (mul_nonneg hκ.le hlam.le) hR
          linarith
        exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hC).trans
          (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.exp_pos _).le)

/-- The scaled maximum has a uniform exponential moment under the backward-crossing estimate. -/
theorem downcrossing_maximum_exponential_moment {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlam : 0 < lam) (h1 : lam ≤ 1)
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (i : Fin d) (R κ C a : ℝ)
    (hR : 0 ≤ R) (hκ : 0 < κ) (hC : 0 ≤ C) (ha : 0 < a) (haκ : a < κ / 2)
    (hback : ∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
      ENNReal.ofReal (C * Real.exp (-κ * lam * u))) :
    Integrable (fun γ => Real.exp (a * downcrossingMaximum lam R i γ)) (G.pathLaw x) ∧
      (∫ γ, Real.exp (a * downcrossingMaximum lam R i γ) ∂G.pathLaw x) ≤
        max C 1 * Real.exp a / (1 - Real.exp (a - κ / 2)) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hS := measurable_downcrossingMaximum (d := d) lam R i
  have hS0 := downcrossingMaximum_nonneg lam R i hlam.le
  exact exponential_moment_le_of_tail (G.pathLaw x) (downcrossingMaximum lam R i) hS hS0
    (max C 1) (κ / 2) a (le_max_of_le_left hC) ha haκ
    (downcrossing_maximum_tail hd ω lam Λ hΛ hω hlam h1 G x i R κ C hR hκ hC hback)

/-- The finite-downcrossing exponential moment in GMP (5.25) is uniformly bounded. -/
theorem downcrossing_overshoot_exponential_moment {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hlam : 0 < lam) (h1 : lam ≤ 1)
    (G : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam hlam.le h1) (x : Vec d) (i : Fin d) (R κ C a : ℝ)
    (hR : 0 ≤ R) (hκ : 0 < κ) (hC : 0 ≤ C) (ha : 0 < a) (haκ : a < κ / 2)
    (hback : ∀ y u, 0 ≤ u → G.pathLaw y {γ | firstHittingBelow γ i (-u) ≠ ⊤} ≤
      ENNReal.ofReal (C * Real.exp (-κ * lam * u))) :
    let E := {γ : Path d | firstHittingBelow γ i (-R) ≠ ⊤}
    let F := fun γ : Path d => Real.exp (a * lam *
      coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
    Integrable (E.indicator F) (G.pathLaw x) ∧
      (∫ γ, E.indicator F γ ∂G.pathLaw x) ≤
        max C 1 * Real.exp a / (1 - Real.exp (a - κ / 2)) := by
  dsimp only
  let E : Set (Path d) := {γ | firstHittingBelow γ i (-R) ≠ ⊤}
  let F : Path d → ℝ := fun γ => Real.exp (a * lam *
    coordinateMaximum γ i (firstHittingBelow γ i (-R)).toNNReal)
  let H : Path d → ℝ := fun γ => Real.exp (a * downcrossingMaximum lam R i γ)
  have hE : MeasurableSet E :=
    (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl
  obtain ⟨hH, hbound⟩ := downcrossing_maximum_exponential_moment hd ω lam Λ hΛ hω
    hlam h1 G x i R κ C a hR hκ hC ha haκ hback
  have heq : E.indicator F = E.indicator H := by
    funext γ
    by_cases hγ : γ ∈ E
    · rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hγ]
      dsimp only [F, H, downcrossingMaximum]
      rw [Set.indicator_of_mem hγ]
      congr 1
      ring
    · simp only [Set.indicator_of_notMem hγ]
  have hi : Integrable (E.indicator F) (G.pathLaw x) := by
    rw [heq]
    exact hH.indicator hE
  refine ⟨hi, (integral_mono_ae hi hH ?_).trans hbound⟩
  filter_upwards [] with γ
  by_cases hγ : γ ∈ E
  · rw [heq, Set.indicator_of_mem hγ]
  · rw [heq, Set.indicator_of_notMem hγ]
    exact (Real.exp_pos _).le

end EinsteinFull.Regeneration
