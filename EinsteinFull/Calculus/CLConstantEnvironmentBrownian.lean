import EinsteinFull.Calculus.CLConstantEnvironmentEvolution
import Mathlib.Data.Fin.Tuple.Sort

/-!
# In a constant environment the reduced diffusion is Brownian

In a translation invariant environment the reduced coefficient is a constant matrix `A`, and every
solution of the reduced martingale problem from the origin is the Brownian law with covariance
`A`: the characteristic function of `ξ · γ_t` against a past-measurable phase decays by
`exp (-½ (t - s) ξ · A ξ)`, and for increasing times the finite-dimensional characteristic
functions follow by induction on the number of times; for arbitrary times the times are sorted.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem stronglyMeasurable_eval_pathFiltration {u s : ℝ≥0} (hus : u ≤ s) :
    StronglyMeasurable[pathFiltration d s] (fun γ : Path d => γ u) := by
  have h : StronglyMeasurable[pathFiltration d u] (fun γ : Path d => γ u) :=
    Filtration.stronglyAdapted_natural (fun t => (measurable_pathPosition t).stronglyMeasurable) u
  exact h.mono ((pathFiltration d).mono hus)

theorem complex_exp_I_ofReal (x : ℝ) :
    Complex.exp (Complex.I * (x : ℂ)) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I := by
  rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem dot_add_left (u v w : Vec d) : dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem dot_zero_left (w : Vec d) : dot 0 w = 0 := by
  simp [dot]

theorem dot_add_right_vec (e u v : Vec d) : dot e (u + v) = dot e u + dot e v := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- Expansion of a weighted quadratic sum after adding `v` at the index `L₀`. -/
theorem quad_update {m : ℕ} (A : Mat d) (W : Fin m → Fin m → ℝ) (L₀ : Fin m) (u : Fin m → Vec d)
    (v : Vec d) :
    ∑ k, ∑ l, W k l * dot (u k + if k = L₀ then v else 0)
        (A.mulVec (u l + if l = L₀ then v else 0)) =
      ∑ k, ∑ l, W k l * dot (u k) (A.mulVec (u l)) + ∑ k, W k L₀ * dot (u k) (A.mulVec v) +
        ∑ l, W L₀ l * dot v (A.mulVec (u l)) + W L₀ L₀ * dot v (A.mulVec v) := by
  have e : ∀ k l, W k l * dot (u k + if k = L₀ then v else 0)
      (A.mulVec (u l + if l = L₀ then v else 0)) =
      W k l * dot (u k) (A.mulVec (u l)) + (if l = L₀ then W k l * dot (u k) (A.mulVec v) else 0) +
        (if k = L₀ then W k l * dot v (A.mulVec (u l)) else 0) +
        (if k = L₀ then (if l = L₀ then W k l * dot v (A.mulVec v) else 0) else 0) := by
    intro k l
    rw [Matrix.mulVec_add, dot_add_left, dot_add_right_vec, dot_add_right_vec]
    by_cases hk : k = L₀ <;> by_cases hl : l = L₀ <;>
      simp [hk, hl, Matrix.mulVec_zero, dot_zero_left, dot_zero_right] <;> ring
  simp_rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Finset.sum_comm (f := fun k l => if k = L₀ then W k l * dot v (A.mulVec (u l)) else 0)]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const_zero]

/-- Splitting the last index off a quadratic sum with `min` weights. -/
theorem quad_split_last {m : ℕ} (A : Mat d) (T : Fin (m + 1) → ℝ) (ξ : Fin (m + 1) → Vec d) :
    ∑ k, ∑ l, min (T k) (T l) * dot (ξ k) (A.mulVec (ξ l)) =
      ∑ k : Fin m, ∑ l : Fin m, min (T k.castSucc) (T l.castSucc) *
          dot (ξ k.castSucc) (A.mulVec (ξ l.castSucc)) +
        ∑ k : Fin m, min (T k.castSucc) (T (Fin.last m)) *
          dot (ξ k.castSucc) (A.mulVec (ξ (Fin.last m))) +
        ∑ l : Fin m, min (T (Fin.last m)) (T l.castSucc) *
          dot (ξ (Fin.last m)) (A.mulVec (ξ l.castSucc)) +
        min (T (Fin.last m)) (T (Fin.last m)) * dot (ξ (Fin.last m)) (A.mulVec (ξ (Fin.last m))) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.sum_univ_castSucc (n := m), Finset.sum_add_distrib]
  ring

section Brownian

variable {c : FieldPair d} (hc : ∀ x, translate x c = c) {Λ₀ : ℝ} (hΛ : 0 < Λ₀)
  (hω : IsRegular Λ₀ c) (hs : IsSmoothFieldPair c) (i : Fin d) {P : Measure (Path d)}
  (hP : SolvesMartingaleProblem (reducedGenerator i c 0) 0 P)

include hc hΛ hω hs hP in
/-- One step of the characteristic function: against a phase measurable at time `s`, the phase
`ξ · γ_t` decays by `exp (-½ (t - s) ξ · A ξ)`. -/
theorem integral_exp_dot_evolution (ξ : Vec d) {s : ℝ≥0} {S : Path d → ℝ}
    (hS : StronglyMeasurable[pathFiltration d s] S) {t : ℝ≥0} (hst : s ≤ t) :
    ∫ γ, Complex.exp (Complex.I * ((dot ξ (γ t) + S γ : ℝ) : ℂ)) ∂P =
      (Real.exp (-((1 / 2 : ℝ) * dot ξ ((reducedCoefficient c 0).mulVec ξ)) * ((t : ℝ) - s)) :
        ℂ) * ∫ γ, Complex.exp (Complex.I * ((dot ξ (γ s) + S γ : ℝ) : ℂ)) ∂P := by
  have : IsProbabilityMeasure P := hP.1
  have hSm : Measurable S := (hS.mono ((pathFiltration d).le s)).measurable
  have hcS : StronglyMeasurable[pathFiltration d s] (fun γ => Real.cos (S γ)) :=
    Real.continuous_cos.comp_stronglyMeasurable hS
  have hsS : StronglyMeasurable[pathFiltration d s] (fun γ => Real.sin (S γ)) :=
    Real.continuous_sin.comp_stronglyMeasurable hS
  have Ecc := integral_mul_eigen_evolution hΛ hω hs i hP (contDiff_cos_dot ξ)
    (abs_fderiv_cos_dot_le ξ) (fun y => Real.abs_cos_le_one _) (reducedGenerator_cos_dot hc hs i ξ)
    hcS (fun γ => Real.abs_cos_le_one _) hst
  have Ecs := integral_mul_eigen_evolution hΛ hω hs i hP (contDiff_sin_dot ξ)
    (abs_fderiv_sin_dot_le ξ) (fun y => Real.abs_sin_le_one _) (reducedGenerator_sin_dot hc hs i ξ)
    hcS (fun γ => Real.abs_cos_le_one _) hst
  have Esc := integral_mul_eigen_evolution hΛ hω hs i hP (contDiff_cos_dot ξ)
    (abs_fderiv_cos_dot_le ξ) (fun y => Real.abs_cos_le_one _) (reducedGenerator_cos_dot hc hs i ξ)
    hsS (fun γ => Real.abs_sin_le_one _) hst
  have Ess := integral_mul_eigen_evolution hΛ hω hs i hP (contDiff_sin_dot ξ)
    (abs_fderiv_sin_dot_le ξ) (fun y => Real.abs_sin_le_one _) (reducedGenerator_sin_dot hc hs i ξ)
    hsS (fun γ => Real.abs_sin_le_one _) hst
  have hint : ∀ (u : ℝ≥0) (F G : ℝ → ℝ), Continuous F → Continuous G → (∀ x, |F x| ≤ 1) →
      (∀ x, |G x| ≤ 1) → Integrable (fun γ => F (S γ) * G (dot ξ (γ u))) P := by
    intro u F G hF hG hFb hGb
    refine Integrable.of_bound ((hF.measurable.comp hSm).mul (hG.measurable.comp
      ((contDiff_dot ξ).continuous.measurable.comp
        (continuous_eval_const u).measurable))).aestronglyMeasurable 1
      (ae_of_all _ fun γ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |F (S γ)| * |G (dot ξ (γ u))| ≤ 1 * 1 :=
          mul_le_mul (hFb _) (hGb _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hdec : ∀ u : ℝ≥0, ∫ γ, Complex.exp (Complex.I * ((dot ξ (γ u) + S γ : ℝ) : ℂ)) ∂P =
      ((∫ γ, Real.cos (S γ) * Real.cos (dot ξ (γ u)) ∂P -
          ∫ γ, Real.sin (S γ) * Real.sin (dot ξ (γ u)) ∂P : ℝ) : ℂ) +
        ((∫ γ, Real.cos (S γ) * Real.sin (dot ξ (γ u)) ∂P +
          ∫ γ, Real.sin (S γ) * Real.cos (dot ξ (γ u)) ∂P : ℝ) : ℂ) * Complex.I := by
    intro u
    have icc := hint u _ _ Real.continuous_cos Real.continuous_cos Real.abs_cos_le_one
      Real.abs_cos_le_one
    have iss := hint u _ _ Real.continuous_sin Real.continuous_sin Real.abs_sin_le_one
      Real.abs_sin_le_one
    have ics := hint u _ _ Real.continuous_cos Real.continuous_sin Real.abs_cos_le_one
      Real.abs_sin_le_one
    have isc := hint u _ _ Real.continuous_sin Real.continuous_cos Real.abs_sin_le_one
      Real.abs_cos_le_one
    have e1 : ∀ γ : Path d, Complex.exp (Complex.I * ((dot ξ (γ u) + S γ : ℝ) : ℂ)) =
        ((Real.cos (S γ) * Real.cos (dot ξ (γ u)) - Real.sin (S γ) * Real.sin (dot ξ (γ u)) :
          ℝ) : ℂ) + ((Real.cos (S γ) * Real.sin (dot ξ (γ u)) +
            Real.sin (S γ) * Real.cos (dot ξ (γ u)) : ℝ) : ℂ) * Complex.I := by
      intro γ
      rw [complex_exp_I_ofReal, Real.cos_add, Real.sin_add]
      congr 2 <;> ring_nf
    simp_rw [e1]
    rw [integral_add (icc.sub iss).ofReal ((ics.add isc).ofReal.mul_const _), integral_mul_const,
      integral_complex_ofReal, integral_complex_ofReal, integral_sub icc iss,
      integral_add ics isc]
  rw [hdec t, hdec s, Ecc, Esc, Ecs, Ess]
  push_cast
  ring

include hc hΛ hω hs hP in
/-- The characteristic function at one time. -/
theorem integral_exp_dot_one (ξ : Vec d) (t : ℝ≥0) :
    ∫ γ, Complex.exp (Complex.I * ((dot ξ (γ t) : ℝ) : ℂ)) ∂P =
      (Real.exp (-((1 / 2 : ℝ) * dot ξ ((reducedCoefficient c 0).mulVec ξ)) * (t : ℝ)) : ℂ) := by
  have : IsProbabilityMeasure P := hP.1
  have h := integral_exp_dot_evolution hc hΛ hω hs i hP ξ (s := 0) (S := fun _ => 0)
    stronglyMeasurable_const (t := t) bot_le
  simp only [add_zero, NNReal.coe_zero, sub_zero] at h
  rw [h]
  have h0 : ∫ γ, Complex.exp (Complex.I * ((dot ξ (γ 0) : ℝ) : ℂ)) ∂P = 1 := by
    have e : (fun γ : Path d => Complex.exp (Complex.I * ((dot ξ (γ 0) : ℝ) : ℂ))) =ᵐ[P]
        fun _ => 1 := by
      filter_upwards [hP.2.1] with γ hγ
      rw [hγ, dot_zero_right]
      simp
    rw [integral_congr_ae e]
    simp
  rw [h0, mul_one]

include hc hΛ hω hs hP in
/-- The finite-dimensional characteristic functions for increasing times. -/
theorem integral_exp_fdd_monotone : ∀ (n : ℕ) (t : Fin n → ℝ≥0), Monotone t →
    ∀ ξ : Fin n → Vec d,
      ∫ γ, Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k)) : ℝ) : ℂ)) ∂P =
        (Real.exp (-(1 / 2 : ℝ) * ∑ k, ∑ l, min (t k : ℝ) (t l) *
          dot (ξ k) ((reducedCoefficient c 0).mulVec (ξ l))) : ℂ) := by
  have : IsProbabilityMeasure P := hP.1
  set A := reducedCoefficient c 0 with hA
  have hsucc : ∀ n : ℕ, ∀ (t : Fin (n + 1) → ℝ≥0), Monotone t → ∀ ξ : Fin (n + 1) → Vec d,
      ∫ γ, Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k)) : ℝ) : ℂ)) ∂P =
        (Real.exp (-(1 / 2 : ℝ) * ∑ k, ∑ l, min (t k : ℝ) (t l) *
          dot (ξ k) (A.mulVec (ξ l))) : ℂ) := by
    intro n
    induction n with
    | zero =>
      intro t _ ξ
      simp only [Fin.sum_univ_succ, Finset.univ_eq_empty, Finset.sum_empty, add_zero, min_self]
      rw [integral_exp_dot_one hc hΛ hω hs i hP (ξ 0) (t 0)]
      congr 2
      ring
    | succ n ih =>
      intro t ht ξ
      let L : Fin (n + 2) := Fin.last (n + 1)
      let tc : Fin (n + 1) → ℝ≥0 := fun k => t k.castSucc
      let ξc : Fin (n + 1) → Vec d := fun k => ξ k.castSucc
      have htc : Monotone tc := ht.comp Fin.strictMono_castSucc.monotone
      let τ : ℝ≥0 := tc (Fin.last n)
      have hτL : τ ≤ t L := ht (Fin.castSucc_lt_last _).le
      have hkτ : ∀ k, tc k ≤ τ := fun k => htc (Fin.le_last k)
      have hkL : ∀ k, tc k ≤ t L := fun k => (hkτ k).trans hτL
      let S : Path d → ℝ := fun γ => ∑ k, dot (ξc k) (γ (tc k))
      have hS : StronglyMeasurable[pathFiltration d τ] S :=
        Finset.stronglyMeasurable_fun_sum _ fun k _ =>
          (contDiff_dot (ξc k)).continuous.comp_stronglyMeasurable
            (stronglyMeasurable_eval_pathFiltration (hkτ k))
      have hsplit : ∀ γ : Path d, (∑ k, dot (ξ k) (γ (t k))) = dot (ξ L) (γ (t L)) + S γ :=
        fun γ => by rw [Fin.sum_univ_castSucc, add_comm]
      simp_rw [hsplit]
      rw [integral_exp_dot_evolution hc hΛ hω hs i hP (ξ L) hS hτL]
      let ξ'' : Fin (n + 1) → Vec d := fun k => ξc k + if k = Fin.last n then ξ L else 0
      have hmerge : ∀ γ : Path d, dot (ξ L) (γ τ) + S γ = ∑ k, dot (ξ'' k) (γ (tc k)) := by
        intro γ
        simp only [ξ'', dot_add_left, Finset.sum_add_distrib, S]
        rw [add_comm]
        congr 1
        have : ∀ k, dot (if k = Fin.last n then ξ L else 0) (γ (tc k)) =
            if k = Fin.last n then dot (ξ L) (γ (tc k)) else 0 := fun k => by
          split_ifs <;> simp [dot_zero_left]
        simp_rw [this, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rfl
      simp_rw [hmerge]
      rw [ih tc htc ξ'', ← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      simp only [ξ'']
      rw [quad_update A (fun k l => min (tc k : ℝ) (tc l)) (Fin.last n) ξc (ξ L),
        quad_split_last A (fun k => (t k : ℝ)) ξ]
      have h1 : ∀ k : Fin (n + 1), min (tc k : ℝ) (tc (Fin.last n)) = tc k := fun k =>
        min_eq_left (NNReal.coe_le_coe.2 (hkτ k))
      have h2 : ∀ l : Fin (n + 1), min (tc (Fin.last n) : ℝ) (tc l) = tc l := fun l =>
        min_eq_right (NNReal.coe_le_coe.2 (hkτ l))
      have h3 : ∀ k : Fin (n + 1), min (t k.castSucc : ℝ) (t (Fin.last (n + 1))) =
          t k.castSucc := fun k => min_eq_left (NNReal.coe_le_coe.2 (hkL k))
      have h4 : ∀ l : Fin (n + 1), min (t (Fin.last (n + 1)) : ℝ) (t l.castSucc) =
          t l.castSucc := fun l => min_eq_right (NNReal.coe_le_coe.2 (hkL l))
      simp only [h1, h2, min_self]
      simp only [h3, h4]
      simp only [tc, ξc, τ, L]
      ring
  intro n
  cases n with
  | zero =>
    intro t _ ξ
    simp
  | succ n => exact hsucc n

include hc hΛ hω hs hP in
/-- The finite-dimensional characteristic functions at arbitrary times. -/
theorem integral_exp_fdd (n : ℕ) (t : Fin n → ℝ≥0) (ξ : Fin n → Vec d) :
    ∫ γ, Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k)) : ℝ) : ℂ)) ∂P =
      (Real.exp (-(1 / 2 : ℝ) * ∑ k, ∑ l, min (t k : ℝ) (t l) *
        dot (ξ k) ((reducedCoefficient c 0).mulVec (ξ l))) : ℂ) := by
  let σ := Tuple.sort t
  have h := integral_exp_fdd_monotone hc hΛ hω hs i hP n (t ∘ σ) (Tuple.monotone_sort t)
    (ξ ∘ σ)
  have e1 : ∀ γ : Path d, (∑ k, dot ((ξ ∘ σ) k) (γ ((t ∘ σ) k))) = ∑ k, dot (ξ k) (γ (t k)) :=
    fun γ => Equiv.sum_comp σ (fun k => dot (ξ k) (γ (t k)))
  have e2 : (∑ k, ∑ l, min ((t ∘ σ) k : ℝ) ((t ∘ σ) l) *
      dot ((ξ ∘ σ) k) ((reducedCoefficient c 0).mulVec ((ξ ∘ σ) l))) =
      ∑ k, ∑ l, min (t k : ℝ) (t l) * dot (ξ k) ((reducedCoefficient c 0).mulVec (ξ l)) := by
    rw [← Equiv.sum_comp σ (fun k => ∑ l, min (t k : ℝ) (t l) *
      dot (ξ k) ((reducedCoefficient c 0).mulVec (ξ l)))]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact Equiv.sum_comp σ (fun l => min (t (σ k) : ℝ) (t l) *
      dot (ξ (σ k)) ((reducedCoefficient c 0).mulVec (ξ l)))
  simp_rw [e1] at h
  rw [e2] at h
  exact h

include hc hΛ hω hs hP in
/-- In a constant environment every solution of the reduced martingale problem from the origin
is the Brownian law with covariance the reduced coefficient. -/
theorem isBrownianLaw_of_constant : IsBrownianLaw (reducedCoefficient c 0) P := by
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨κ, hκ, hell⟩ := reducedCoefficient_elliptic hΛ hω
  refine ⟨hP.1, reducedCoefficient_symm hω 0, fun ξ => ?_, hP.2.1, fun n t ξ => ?_⟩
  · refine le_trans ?_ (hell 0 ξ)
    have : 0 ≤ euclideanSq ξ := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg _
    positivity
  · have h := integral_exp_fdd hc hΛ hω hs i hP n t ξ
    push_cast at h ⊢
    rw [h]

end Brownian

end EinsteinFull.Blueprint
