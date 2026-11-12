import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Calculus.HorizontalCore
import EinsteinRelation.Calculus.HorizontalTranslationLp
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Module
import Mathlib.Topology.Instances.Matrix

/-! # Calculus of the weak horizontal predicates

Source `paper/main.tex:240–249`. The weak gradient, the weak divergence and the reduced generator
equation of `Calculus/EnvironmentWeakCalculus.lean` are closed under real linear combinations and
contain the zero field. Coordinate translations commute on the L² generator domain, so the
horizontal generators commute on pairs of directions, and derivatives of horizontally smooth tests
are horizontally smooth. The weak divergence of a coefficient column `a e_i` is obtained by
integration by parts along translation orbits, for coefficients whose orbits are differentiable
with bounded coordinate derivatives. No estimate, existence result or conclusion of the paper is
assumed here.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-! ### Essential bounds and integrability -/

/-- A horizontally smooth test is essentially bounded. -/
theorem ae_bound_of_isHorizontallySmoothTest {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {F : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F) : ∃ M : ℝ, ∀ᵐ ω ∂Q, |F ω| ≤ M := by
  obtain ⟨G, hG, M, hM⟩ := hF []
  have hGF : G = F := hG
  rw [hGF] at hM
  exact ⟨M, hM⟩

/-- The horizontal derivative of a horizontally smooth test is essentially bounded. -/
theorem ae_bound_of_hasHorizontalLpDerivative {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {i : Fin d} {F G : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F)
    (hG : HasHorizontalLpDerivative Q hQ i F G) : ∃ M : ℝ, ∀ᵐ ω ∂Q, |G ω| ≤ M := by
  obtain ⟨G', hG', M, hM⟩ := hF [i]
  have hG'' : ∃ F', HasIteratedHorizontalLpDerivative Q hQ [] F F' ∧
      HasHorizontalLpDerivative Q hQ i F' G' := hG'
  obtain ⟨F', hF'0, hF'1⟩ := hG''
  have hF'eq : F' = F := hF'0
  rw [hF'eq] at hF'1
  have hGG : G' = G := HasHorizontalLpDerivative.unique hF'1 hG
  rw [hGG] at hM
  exact ⟨M, hM⟩

/-- Integrability of `u · g` for an integrable scalar field `u` and an essentially bounded `g`. -/
theorem integrable_mul_of_ae_bound {Q : Measure (FieldPair d)} {u : FieldPair d → ℝ}
    (hu : Integrable u Q) {g : Lp ℝ 2 Q} {M : ℝ} (hg : ∀ᵐ ω ∂Q, |g ω| ≤ M) :
    Integrable (fun ω => u ω * g ω) Q :=
  hu.mul_bdd (c := M) (Lp.aestronglyMeasurable g)
    (hg.mono fun ω hω => by rw [Real.norm_eq_abs]; exact hω)

/-- Bound of a product of two essentially bounded real functions. -/
theorem ae_norm_mul_le {Q : Measure (FieldPair d)} {x y : FieldPair d → ℝ} {M C : ℝ}
    (hx : ∀ᵐ ω ∂Q, |x ω| ≤ M) (hy : ∀ᵐ ω ∂Q, |y ω| ≤ C) :
    ∀ᵐ ω ∂Q, ‖x ω * y ω‖ ≤ max M 0 * max C 0 := by
  filter_upwards [hx, hy] with ω h1 h2
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (h1.trans (le_max_left M 0)) (h2.trans (le_max_left C 0)) (abs_nonneg _)
    (le_max_right M 0)

/-! ### Linear combinations of integrals and finite sums -/

theorem integral_lincomb_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {w u v : Ω → ℝ}
    (c₁ c₂ : ℝ) (hu : Integrable u μ) (hv : Integrable v μ)
    (hw : ∀ ω, w ω = c₁ * u ω + c₂ * v ω) :
    ∫ ω, w ω ∂μ = c₁ * ∫ ω, u ω ∂μ + c₂ * ∫ ω, v ω ∂μ :=
  calc ∫ ω, w ω ∂μ = ∫ ω, (c₁ * u ω + c₂ * v ω) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall hw)
    _ = ∫ ω, c₁ * u ω ∂μ + ∫ ω, c₂ * v ω ∂μ :=
        integral_add (hu.const_mul c₁) (hv.const_mul c₂)
    _ = c₁ * ∫ ω, u ω ∂μ + c₂ * ∫ ω, v ω ∂μ := by
        rw [integral_const_mul, integral_const_mul]

theorem sum_lincomb_mul {ι : Type*} (s : Finset ι) (c₁ c₂ : ℝ) (x y z : ι → ℝ) :
    ∑ i ∈ s, (c₁ * x i + c₂ * y i) * z i = c₁ * ∑ i ∈ s, x i * z i + c₂ * ∑ i ∈ s, y i * z i := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_sum_lincomb {d : ℕ} (c₁ c₂ : ℝ) (x : Fin d → Fin d → ℝ) (y z : Fin d → ℝ) :
    ∑ i, ∑ j, x i j * (c₁ * y j + c₂ * z j) =
      c₁ * ∑ i, ∑ j, x i j * y j + c₂ * ∑ i, ∑ j, x i j * z j := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_sum_lincomb {d : ℕ} (F c₁ c₂ : ℝ) (a y z : Fin d → ℝ) :
    F * ∑ j, a j * (c₁ * y j + c₂ * z j) =
      c₁ * (F * ∑ j, a j * y j) + c₂ * (F * ∑ j, a j * z j) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The coordinate entries of the coefficient at the origin are measurable. -/
theorem measurable_coeff_entry {d : ℕ} (j k : Fin d) :
    Measurable (fun η : FieldPair d => η.1 0 j k) := by
  have hc : Continuous (fun η : FieldPair d => η.1 0) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_fst
  exact (hc.matrix_elem j k).measurable

/-- The orbit of a coefficient entry at the origin is the entry of the coefficient field. -/
theorem orbit_coeff_entry {d : ℕ} (j k : Fin d) (ω : FieldPair d) :
    orbit (fun η : FieldPair d => η.1 0 j k) ω = fun y => ω.1 y j k := by
  funext y
  simp only [orbit, translate_matrix, add_zero]

/-- Integrability of `∑ᵢ V_i · Dᵢ F` for a horizontally smooth test `F`. -/
theorem integrable_sum_mul_derivative {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} (hV : ∀ i, Integrable (fun ω => V ω i) Q)
    {F : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F) {DF : Fin d → Lp ℝ 2 Q}
    (hDF : ∀ i, HasHorizontalLpDerivative Q hQ i F (DF i)) :
    Integrable (fun ω => ∑ i : Fin d, V ω i * DF i ω) Q := by
  refine integrable_finset_sum _ fun i _ => ?_
  obtain ⟨N, hN⟩ := ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
  exact integrable_mul_of_ae_bound (hV i) hN

/-- Integrability of the double sum `∑ᵢ∑ⱼ Dᵢ F · a_{ij} · D_j` for a bounded coefficient. -/
theorem integrable_double_sum_flux {Q : Measure (FieldPair d)} {C : ℝ}
    (hC : ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C) {DF : Fin d → Lp ℝ 2 Q}
    (hN : ∀ i, ∃ N : ℝ, ∀ᵐ ω ∂Q, |DF i ω| ≤ N) {D : FieldPair d → Vec d}
    (hD : ∀ j, Integrable (fun ω => D ω j) Q) :
    Integrable (fun ω => ∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * D ω j) Q := by
  refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
  obtain ⟨N, hNi⟩ := hN i
  have hX : AEStronglyMeasurable (fun ω => DF i ω * (ω.1 0) i j) Q :=
    (Lp.aestronglyMeasurable (DF i)).mul (measurable_coeff_entry i j).aestronglyMeasurable
  exact (hD j).bdd_mul hX (ae_norm_mul_le hNi (hC.mono fun ω hω => hω i j))

/-- Integrability of `F · ∑ⱼ a_{j i₁} · D_j` for a bounded coefficient and bounded `F`. -/
theorem integrable_scalar_flux {Q : Measure (FieldPair d)} {C M : ℝ} (i : Fin d)
    (hC : ∀ᵐ ω ∂Q, ∀ j k : Fin d, |ω.1 0 j k| ≤ C) {F : Lp ℝ 2 Q}
    (hF : ∀ᵐ ω ∂Q, |F ω| ≤ M) {D : FieldPair d → Vec d}
    (hD : ∀ j, Integrable (fun ω => D ω j) Q) :
    Integrable (fun ω => F ω * ∑ j : Fin d, (ω.1 0) j i * D ω j) Q := by
  have hrw : (fun ω => F ω * ∑ j : Fin d, (ω.1 0) j i * D ω j) =
      fun ω => ∑ j : Fin d, F ω * (ω.1 0) j i * D ω j := by
    funext ω
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrw]
  refine integrable_finset_sum _ fun j _ => ?_
  have hX : AEStronglyMeasurable (fun ω => F ω * (ω.1 0) j i) Q :=
    (Lp.aestronglyMeasurable F).mul (measurable_coeff_entry j i).aestronglyMeasurable
  exact (hD j).bdd_mul hX (ae_norm_mul_le hF (hC.mono fun ω hω => hω j i))

/-! ### Weak horizontal gradient -/

/-- Linear combinations of weak horizontal gradients are weak horizontal gradients. -/
theorem HasWeakHorizontalGradient.lincomb {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f₁ f₂ : FieldPair d → ℝ} {D₁ D₂ : FieldPair d → Vec d} (c₁ c₂ : ℝ)
    (h₁ : HasWeakHorizontalGradient Q hQ f₁ D₁) (h₂ : HasWeakHorizontalGradient Q hQ f₂ D₂) :
    HasWeakHorizontalGradient Q hQ (fun ω => c₁ * f₁ ω + c₂ * f₂ ω)
      (fun ω => c₁ • D₁ ω + c₂ • D₂ ω) := by
  obtain ⟨hf₁, hD₁, hw₁⟩ := h₁
  obtain ⟨hf₂, hD₂, hw₂⟩ := h₂
  refine ⟨(hf₁.const_mul c₁).add (hf₂.const_mul c₂), fun i => ?_, fun i F G hF hG => ?_⟩
  · exact ((hD₁ i).const_mul c₁).add ((hD₂ i).const_mul c₂)
  · obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
    obtain ⟨N, hN⟩ := ae_bound_of_hasHorizontalLpDerivative hF hG
    have eF : ∫ ω, (c₁ * f₁ ω + c₂ * f₂ ω) * G ω ∂Q =
        c₁ * ∫ ω, f₁ ω * G ω ∂Q + c₂ * ∫ ω, f₂ ω * G ω ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_mul_of_ae_bound hf₁ hN)
        (integrable_mul_of_ae_bound hf₂ hN) (fun ω => by ring)
    have eD : ∫ ω, (c₁ • D₁ ω + c₂ • D₂ ω) i * F ω ∂Q =
        c₁ * ∫ ω, D₁ ω i * F ω ∂Q + c₂ * ∫ ω, D₂ ω i * F ω ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_mul_of_ae_bound (hD₁ i) hM)
        (integrable_mul_of_ae_bound (hD₂ i) hM)
        (fun ω => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring)
    show (∫ ω, (c₁ * f₁ ω + c₂ * f₂ ω) * G ω ∂Q) =
      -(∫ ω, (c₁ • D₁ ω + c₂ • D₂ ω) i * F ω ∂Q)
    linear_combination eF + eD + c₁ * hw₁ i F G hF hG + c₂ * hw₂ i F G hF hG

/-- The zero field is a weak horizontal gradient of the zero field. -/
theorem HasWeakHorizontalGradient.zero {Q : Measure (FieldPair d)} {hQ : IsStationary Q} :
    HasWeakHorizontalGradient Q hQ (fun _ => 0) (fun _ => 0) := by
  refine ⟨by simp, fun i => by simp, fun i F G _ _ => ?_⟩
  simp

/-- Sums of weak horizontal gradients are weak horizontal gradients. -/
theorem HasWeakHorizontalGradient.add {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f₁ f₂ : FieldPair d → ℝ} {D₁ D₂ : FieldPair d → Vec d}
    (h₁ : HasWeakHorizontalGradient Q hQ f₁ D₁) (h₂ : HasWeakHorizontalGradient Q hQ f₂ D₂) :
    HasWeakHorizontalGradient Q hQ (fun ω => f₁ ω + f₂ ω) (fun ω => D₁ ω + D₂ ω) := by
  simpa only [one_mul, one_smul] using HasWeakHorizontalGradient.lincomb 1 1 h₁ h₂

/-- Real multiples of weak horizontal gradients are weak horizontal gradients. -/
theorem HasWeakHorizontalGradient.smul {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f : FieldPair d → ℝ} {D : FieldPair d → Vec d} (c : ℝ)
    (h : HasWeakHorizontalGradient Q hQ f D) :
    HasWeakHorizontalGradient Q hQ (fun ω => c * f ω) (fun ω => c • D ω) := by
  simpa only [zero_mul, add_zero, zero_smul] using
    HasWeakHorizontalGradient.lincomb c 0 h (HasWeakHorizontalGradient.zero (Q := Q) (hQ := hQ))

/-! ### Weak horizontal divergence -/

/-- Linear combinations of weak horizontal divergences are weak horizontal divergences. -/
theorem HasWeakHorizontalDivergence.lincomb {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V₁ V₂ : FieldPair d → Vec d} {h₁ h₂ : FieldPair d → ℝ} (c₁ c₂ : ℝ)
    (e₁ : HasWeakHorizontalDivergence Q hQ V₁ h₁) (e₂ : HasWeakHorizontalDivergence Q hQ V₂ h₂) :
    HasWeakHorizontalDivergence Q hQ (fun ω => c₁ • V₁ ω + c₂ • V₂ ω)
      (fun ω => c₁ * h₁ ω + c₂ * h₂ ω) := by
  obtain ⟨hV₁, hh₁, hw₁⟩ := e₁
  obtain ⟨hV₂, hh₂, hw₂⟩ := e₂
  refine ⟨fun i => ?_, (hh₁.const_mul c₁).add (hh₂.const_mul c₂), fun F hF DF hDF => ?_⟩
  · exact ((hV₁ i).const_mul c₁).add ((hV₂ i).const_mul c₂)
  · obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
    have eV : ∫ ω, (∑ i : Fin d, (c₁ • V₁ ω + c₂ • V₂ ω) i * DF i ω) ∂Q =
        c₁ * ∫ ω, (∑ i : Fin d, V₁ ω i * DF i ω) ∂Q +
          c₂ * ∫ ω, (∑ i : Fin d, V₂ ω i * DF i ω) ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_sum_mul_derivative hV₁ hF hDF)
        (integrable_sum_mul_derivative hV₂ hF hDF)
        (fun ω => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact sum_lincomb_mul _ c₁ c₂ _ _ _)
    have eh : ∫ ω, (c₁ * h₁ ω + c₂ * h₂ ω) * F ω ∂Q =
        c₁ * ∫ ω, h₁ ω * F ω ∂Q + c₂ * ∫ ω, h₂ ω * F ω ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_mul_of_ae_bound hh₁ hM)
        (integrable_mul_of_ae_bound hh₂ hM) (fun ω => by ring)
    show (∫ ω, (∑ i : Fin d, (c₁ • V₁ ω + c₂ • V₂ ω) i * DF i ω) ∂Q) =
      -(∫ ω, (c₁ * h₁ ω + c₂ * h₂ ω) * F ω ∂Q)
    linear_combination eV + eh + c₁ * hw₁ F hF DF hDF + c₂ * hw₂ F hF DF hDF

/-- The zero field is a weak horizontal divergence of the zero field. -/
theorem HasWeakHorizontalDivergence.zero {Q : Measure (FieldPair d)} {hQ : IsStationary Q} :
    HasWeakHorizontalDivergence Q hQ (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun i => by simp, by simp, fun F _ DF _ => ?_⟩
  simp

/-- Sums of weak horizontal divergences are weak horizontal divergences. -/
theorem HasWeakHorizontalDivergence.add {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V₁ V₂ : FieldPair d → Vec d} {h₁ h₂ : FieldPair d → ℝ}
    (e₁ : HasWeakHorizontalDivergence Q hQ V₁ h₁) (e₂ : HasWeakHorizontalDivergence Q hQ V₂ h₂) :
    HasWeakHorizontalDivergence Q hQ (fun ω => V₁ ω + V₂ ω) (fun ω => h₁ ω + h₂ ω) := by
  simpa only [one_mul, one_smul] using HasWeakHorizontalDivergence.lincomb 1 1 e₁ e₂

/-- Real multiples of weak horizontal divergences are weak horizontal divergences. -/
theorem HasWeakHorizontalDivergence.smul {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} {h : FieldPair d → ℝ} (c : ℝ)
    (e : HasWeakHorizontalDivergence Q hQ V h) :
    HasWeakHorizontalDivergence Q hQ (fun ω => c • V ω) (fun ω => c * h ω) := by
  simpa only [zero_mul, add_zero, zero_smul] using
    HasWeakHorizontalDivergence.lincomb c 0 e (HasWeakHorizontalDivergence.zero (Q := Q) (hQ := hQ))

/-! ### Weak form of the reduced generator equation -/

/-- Linear combinations of solutions of the reduced generator equation are solutions, provided the
coefficient at the origin is essentially bounded. The bound is the boundedness of the reduced
coefficient on the carrier law, and it makes the bilinear integrands integrable. -/
theorem SatisfiesReducedGeneratorEquation.lincomb {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {lam : ℝ} {i₁ : Fin d}
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    {f₁ f₂ : FieldPair d → ℝ} {D₁ D₂ : FieldPair d → Vec d} {h₁ h₂ : FieldPair d → ℝ}
    {G₁ G₂ : FieldPair d → Vec d} (c₁ c₂ : ℝ)
    (e₁ : SatisfiesReducedGeneratorEquation Q hQ lam f₁ D₁ h₁ G₁ i₁)
    (e₂ : SatisfiesReducedGeneratorEquation Q hQ lam f₂ D₂ h₂ G₂ i₁) :
    SatisfiesReducedGeneratorEquation Q hQ lam (fun ω => c₁ * f₁ ω + c₂ * f₂ ω)
      (fun ω => c₁ • D₁ ω + c₂ • D₂ ω) (fun ω => c₁ * h₁ ω + c₂ * h₂ ω)
      (fun ω => c₁ • G₁ ω + c₂ • G₂ ω) i₁ := by
  obtain ⟨C, hC⟩ := hA
  obtain ⟨hw₁, hh₁, hG₁, he₁⟩ := e₁
  obtain ⟨hw₂, hh₂, hG₂, he₂⟩ := e₂
  refine ⟨HasWeakHorizontalGradient.lincomb c₁ c₂ hw₁ hw₂,
    (hh₁.const_mul c₁).add (hh₂.const_mul c₂), fun i => ?_, fun F hF DF hDF => ?_⟩
  · exact ((hG₁ i).const_mul c₁).add ((hG₂ i).const_mul c₂)
  · obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
    have hN : ∀ i, ∃ N : ℝ, ∀ᵐ ω ∂Q, |DF i ω| ≤ N := fun i =>
      ae_bound_of_hasHorizontalLpDerivative hF (hDF i)
    have eA : ∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j *
          (c₁ • D₁ ω + c₂ • D₂ ω) j) ∂Q =
        c₁ * ∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * D₁ ω j) ∂Q +
          c₂ * ∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * D₂ ω j) ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_double_sum_flux hC hN hw₁.2.1)
        (integrable_double_sum_flux hC hN hw₂.2.1)
        (fun ω => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact sum_sum_lincomb c₁ c₂ (fun i j => DF i ω * (ω.1 0) i j) (D₁ ω) (D₂ ω))
    have eB : ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * (c₁ • D₁ ω + c₂ • D₂ ω) j) ∂Q =
        c₁ * ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * D₁ ω j) ∂Q +
          c₂ * ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * D₂ ω j) ∂Q :=
      integral_lincomb_ae c₁ c₂
        (integrable_scalar_flux i₁ hC (hM.mono fun ω hω => hω) hw₁.2.1)
        (integrable_scalar_flux i₁ hC (hM.mono fun ω hω => hω) hw₂.2.1)
        (fun ω => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact mul_sum_lincomb (F ω) c₁ c₂ _ _ _)
    have eC : ∫ ω, (c₁ * h₁ ω + c₂ * h₂ ω) * F ω ∂Q =
        c₁ * ∫ ω, h₁ ω * F ω ∂Q + c₂ * ∫ ω, h₂ ω * F ω ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_mul_of_ae_bound hh₁ hM)
        (integrable_mul_of_ae_bound hh₂ hM) (fun ω => by ring)
    have eG : ∫ ω, (∑ i : Fin d, (c₁ • G₁ ω + c₂ • G₂ ω) i * DF i ω) ∂Q =
        c₁ * ∫ ω, (∑ i : Fin d, G₁ ω i * DF i ω) ∂Q +
          c₂ * ∫ ω, (∑ i : Fin d, G₂ ω i * DF i ω) ∂Q :=
      integral_lincomb_ae c₁ c₂ (integrable_sum_mul_derivative hG₁ hF hDF)
        (integrable_sum_mul_derivative hG₂ hF hDF)
        (fun ω => by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          exact sum_lincomb_mul _ c₁ c₂ _ _ _)
    have he₁' := he₁ F hF DF hDF
    have he₂' := he₂ F hF DF hDF
    show -(1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j *
          (c₁ • D₁ ω + c₂ • D₂ ω) j) ∂Q) +
        lam * (∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₁ * (c₁ • D₁ ω + c₂ • D₂ ω) j) ∂Q) =
      (∫ ω, (c₁ * h₁ ω + c₂ * h₂ ω) * F ω ∂Q) -
        (∫ ω, (∑ i : Fin d, (c₁ • G₁ ω + c₂ • G₂ ω) i * DF i ω) ∂Q)
    linear_combination (-(1 / 2 : ℝ)) * eA + lam * eB - eC + eG + c₁ * he₁' + c₂ * he₂'

/-- The zero field solves the reduced generator equation. -/
theorem SatisfiesReducedGeneratorEquation.zero {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {lam : ℝ} {i₁ : Fin d} :
    SatisfiesReducedGeneratorEquation Q hQ lam (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) i₁ := by
  refine ⟨HasWeakHorizontalGradient.zero, by simp, fun i => by simp, fun F _ DF _ => ?_⟩
  simp

/-- Sums of solutions of the reduced generator equation are solutions. -/
theorem SatisfiesReducedGeneratorEquation.add {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {lam : ℝ} {i₁ : Fin d}
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C)
    {f₁ f₂ : FieldPair d → ℝ} {D₁ D₂ : FieldPair d → Vec d} {h₁ h₂ : FieldPair d → ℝ}
    {G₁ G₂ : FieldPair d → Vec d}
    (e₁ : SatisfiesReducedGeneratorEquation Q hQ lam f₁ D₁ h₁ G₁ i₁)
    (e₂ : SatisfiesReducedGeneratorEquation Q hQ lam f₂ D₂ h₂ G₂ i₁) :
    SatisfiesReducedGeneratorEquation Q hQ lam (fun ω => f₁ ω + f₂ ω)
      (fun ω => D₁ ω + D₂ ω) (fun ω => h₁ ω + h₂ ω) (fun ω => G₁ ω + G₂ ω) i₁ := by
  simpa only [one_mul, one_smul] using
    SatisfiesReducedGeneratorEquation.lincomb hA 1 1 e₁ e₂

/-- Real multiples of solutions of the reduced generator equation are solutions. -/
theorem SatisfiesReducedGeneratorEquation.smul {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {lam : ℝ} {i₁ : Fin d}
    (hA : ∃ C : ℝ, ∀ᵐ ω ∂Q, ∀ i j : Fin d, |ω.1 0 i j| ≤ C) (c : ℝ)
    {f : FieldPair d → ℝ} {D : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    {G : FieldPair d → Vec d}
    (e : SatisfiesReducedGeneratorEquation Q hQ lam f D h G i₁) :
    SatisfiesReducedGeneratorEquation Q hQ lam (fun ω => c * f ω)
      (fun ω => c • D ω) (fun ω => c * h ω) (fun ω => c • G ω) i₁ := by
  simpa only [zero_mul, add_zero, zero_smul] using
    SatisfiesReducedGeneratorEquation.lincomb hA c 0 e
      (SatisfiesReducedGeneratorEquation.zero (lam := lam) (i₁ := i₁) (Q := Q) (hQ := hQ))

/-! ### Derivatives of horizontally smooth tests -/

/-- Coordinate iterates ending in `j` transfer to the derivative `G` of `F` in direction `j`. -/
theorem hasIteratedHorizontalLpDerivative_of_append {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {F G : Lp ℝ 2 Q} {j : Fin d}
    (hG : HasHorizontalLpDerivative Q hQ j F G) :
    ∀ (c : List (Fin d)) (g : Lp ℝ 2 Q), HasIteratedHorizontalLpDerivative Q hQ (c ++ [j]) F g →
      HasIteratedHorizontalLpDerivative Q hQ c G g := by
  intro c
  induction c with
  | nil =>
    intro g hg
    obtain ⟨h, hh₀, hh₁⟩ := hg
    have hhF : h = F := hh₀
    rw [hhF] at hh₁
    show g = G
    exact HasHorizontalLpDerivative.unique hh₁ hG
  | cons i rest ih =>
    intro g hg
    obtain ⟨h, hh₀, hh₁⟩ := hg
    exact ⟨h, ih h hh₀, hh₁⟩

/-- The horizontal derivative of a horizontally smooth test is horizontally smooth. -/
theorem IsHorizontallySmoothTest.derivative {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {F G : Lp ℝ 2 Q} {j : Fin d} (hF : IsHorizontallySmoothTest Q hQ F)
    (hG : HasHorizontalLpDerivative Q hQ j F G) : IsHorizontallySmoothTest Q hQ G := by
  intro c
  obtain ⟨g, hg, M, hM⟩ := hF (c ++ [j])
  exact ⟨g, hasIteratedHorizontalLpDerivative_of_append hG c g hg, M, hM⟩

/-! ### Commutation of coordinate difference quotients -/

/-- The difference quotient of the L² translation group in coordinate `i` at step `t`. -/
noncomputable def hDiffQuot (Q : Measure (FieldPair d)) (hQ : IsStationary Q) (i : Fin d) (t : ℝ)
    (f : Lp ℝ 2 Q) : Lp ℝ 2 Q :=
  t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)

theorem hasHorizontalLpDerivative_iff_tendsto {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {i : Fin d} {f g : Lp ℝ 2 Q} :
    HasHorizontalLpDerivative Q hQ i f g ↔
      Tendsto (fun t : ℝ => hDiffQuot Q hQ i t f) (𝓝[≠] (0 : ℝ)) (𝓝 g) :=
  Iff.rfl

theorem continuous_hDiffQuot {Q : Measure (FieldPair d)} (hQ : IsStationary Q) (i : Fin d)
    (t : ℝ) : Continuous (fun Z : Lp ℝ 2 Q => hDiffQuot Q hQ i t Z) := by
  unfold hDiffQuot
  exact continuous_const.smul ((translationLp Q hQ (t • unitVector i)).continuous.sub continuous_id)

theorem translationLp_comm {Q : Measure (FieldPair d)} (hQ : IsStationary Q) (x y : Vec d)
    (f : Lp ℝ 2 Q) :
    translationLp Q hQ x (translationLp Q hQ y f) = translationLp Q hQ y (translationLp Q hQ x f) := by
  rw [← translationLp_add, ← translationLp_add, add_comm]

theorem hDiffQuot_comm {Q : Measure (FieldPair d)} (hQ : IsStationary Q) (i k : Fin d) (t s : ℝ)
    (f : Lp ℝ 2 Q) :
    hDiffQuot Q hQ i t (hDiffQuot Q hQ k s f) = hDiffQuot Q hQ k s (hDiffQuot Q hQ i t f) := by
  unfold hDiffQuot
  simp only [map_smul, map_sub]
  rw [translationLp_comm hQ (t • unitVector i) (s • unitVector k) f]
  module

/-- The coordinate-`j` group derivative of the curve `r ↦ T_{r e_j} X` at every point. -/
theorem hasDerivAt_translationLp_coord {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {j : Fin d} {X Y : Lp ℝ 2 Q} (hX : HasHorizontalLpDerivative Q hQ j X Y) (u : ℝ) :
    HasDerivAt (fun r : ℝ => translationLp Q hQ (r • unitVector j) X)
      (translationLp Q hQ (u • unitVector j) Y) u := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hT := ((translationLp Q hQ (u • unitVector j)).continuous.tendsto Y).comp
    (hasHorizontalLpDerivative_iff_tendsto.mp hX)
  refine hT.congr (fun t => ?_)
  show translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ j t X) =
    t⁻¹ • (translationLp Q hQ ((u + t) • unitVector j) X -
      translationLp Q hQ (u • unitVector j) X)
  unfold hDiffQuot
  rw [add_smul, translationLp_add, map_smul, map_sub]

/-- Mean-value estimate for the difference quotient of a horizontal derivative. -/
theorem norm_hDiffQuot_sub_le {Q : Measure (FieldPair d)} {hQ : IsStationary Q} {j : Fin d}
    {X Y : Lp ℝ 2 Q} (hX : HasHorizontalLpDerivative Q hQ j X Y) {t C : ℝ} (ht : t ≠ 0)
    (hC : ∀ u ∈ Metric.closedBall (0 : ℝ) |t|,
      ‖translationLp Q hQ (u • unitVector j) Y - Y‖ ≤ C) :
    ‖hDiffQuot Q hQ j t X - Y‖ ≤ C := by
  have hg : ∀ u ∈ Metric.closedBall (0 : ℝ) |t|, HasDerivWithinAt
      (fun r : ℝ => translationLp Q hQ (r • unitVector j) X - r • Y)
      (translationLp Q hQ (u • unitVector j) Y - Y) (Metric.closedBall (0 : ℝ) |t|) u := by
    intro u _
    have h1 := (hasDerivAt_translationLp_coord hX u).sub ((hasDerivAt_id' u).smul_const Y)
    rw [one_smul] at h1
    exact h1.hasDerivWithinAt
  have h0_mem : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) |t| :=
    Metric.mem_closedBall_self (abs_nonneg t)
  have ht_mem : t ∈ Metric.closedBall (0 : ℝ) |t| := Metric.mem_closedBall.mpr (by simp)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hC
    (convex_closedBall (0 : ℝ) |t|) h0_mem ht_mem
  have hB : ‖translationLp Q hQ (t • unitVector j) X - t • Y - X‖ ≤ C * |t| := by
    simpa only [zero_smul, translationLp_zero, sub_zero, Real.norm_eq_abs] using hb
  have key : hDiffQuot Q hQ j t X - Y = t⁻¹ • (translationLp Q hQ (t • unitVector j) X - t • Y - X) := by
    unfold hDiffQuot
    simp only [smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
    abel
  rw [key, norm_smul, Real.norm_eq_abs, abs_inv]
  have hat : |t| ≠ 0 := abs_ne_zero.mpr ht
  calc |t|⁻¹ * ‖translationLp Q hQ (t • unitVector j) X - t • Y - X‖
      ≤ |t|⁻¹ * (C * |t|) := mul_le_mul_of_nonneg_left hB (by positivity)
    _ = C := by rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ hat, one_mul]

/-- **Commutation of horizontal generators.** If `F` has generator derivatives `G_j` in direction
`j` and `G_k` in direction `k`, and these have derivatives `H` (in direction `k`, from `G_j`) and
`H'` (in direction `j`, from `G_k`), then `H = H'`. The translation groups in the two directions
commute, so the mean-value estimate for the `j`-difference quotient of `k`-difference quotients is
uniform in the step of the `k`-difference quotient, and the two limits are identified. -/
theorem horizontal_derivative_comm {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {j k : Fin d} {F Gj Gk H H' : Lp ℝ 2 Q}
    (hj : HasHorizontalLpDerivative Q hQ j F Gj) (hk : HasHorizontalLpDerivative Q hQ k Gj H)
    (hk' : HasHorizontalLpDerivative Q hQ k F Gk) (hj' : HasHorizontalLpDerivative Q hQ j Gk H') :
    H = H' := by
  have hjF : Tendsto (fun t : ℝ => hDiffQuot Q hQ j t F) (𝓝[≠] (0 : ℝ)) (𝓝 Gj) := hj
  have hkF : Tendsto (fun s : ℝ => hDiffQuot Q hQ k s F) (𝓝[≠] (0 : ℝ)) (𝓝 Gk) := hk'
  have hkG : Tendsto (fun s : ℝ => hDiffQuot Q hQ k s Gj) (𝓝[≠] (0 : ℝ)) (𝓝 H) := hk
  -- The `j`-derivative of `hDiffQuot k s F` is `hDiffQuot k s Gj`, by commutation.
  have hstep : ∀ s : ℝ, HasHorizontalLpDerivative Q hQ j (hDiffQuot Q hQ k s F)
      (hDiffQuot Q hQ k s Gj) := by
    intro s
    rw [hasHorizontalLpDerivative_iff_tendsto]
    have h := ((continuous_hDiffQuot hQ k s).tendsto Gj).comp hjF
    exact h.congr fun t => (hDiffQuot_comm hQ j k t s F).symm
  -- Continuity of the translation orbit of `H` in direction `j` at the origin.
  have hcont : Tendsto (fun y : ℝ => translationLp Q hQ (y • unitVector j) H) (𝓝 (0 : ℝ))
      (𝓝 H) := by
    have h1 := tendsto_translationLp_zero Q hQ H
    have h2 : Tendsto (fun y : ℝ => y • unitVector j) (𝓝 (0 : ℝ)) (𝓝 (0 : Vec d)) := by
      have hc : Continuous (fun y : ℝ => y • unitVector j) :=
        continuous_id.smul continuous_const
      simpa using hc.tendsto (0 : ℝ)
    exact h1.comp h2
  have hmod : ∀ ε > 0, ∃ δ > 0, ∀ u : ℝ, |u| < δ →
      ‖translationLp Q hQ (u • unitVector j) H - H‖ < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδH⟩ := Metric.eventually_nhds_iff.mp (Metric.tendsto_nhds.mp hcont ε hε)
    refine ⟨δ, hδ, fun u hu => ?_⟩
    have h := hδH (show dist u 0 < δ by rw [Real.dist_eq, sub_zero]; exact hu)
    rwa [dist_eq_norm] at h
  -- Uniform estimate in the step `s` of the `k`-quotient, for each small step `t` in direction `j`.
  have hK : ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, t ≠ 0 → |t| < δ →
      ‖hDiffQuot Q hQ j t Gk - H‖ ≤ ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδH⟩ := hmod ε hε
    refine ⟨δ, hδ, fun t ht hδt => ?_⟩
    have hbound : ∀ s : ℝ,
        ‖hDiffQuot Q hQ j t (hDiffQuot Q hQ k s F) - hDiffQuot Q hQ k s Gj‖ ≤
          2 * ‖hDiffQuot Q hQ k s Gj - H‖ + ε := by
      intro s
      apply norm_hDiffQuot_sub_le (hstep s) ht
      intro u hu
      have hu' : |u| < δ := by
        have h1 := Metric.mem_closedBall.mp hu
        rw [Real.dist_eq, sub_zero] at h1
        linarith
      have hH := hδH u hu'
      have e : translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ k s Gj) -
            hDiffQuot Q hQ k s Gj =
          translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ k s Gj - H) +
            (translationLp Q hQ (u • unitVector j) H - H) - (hDiffQuot Q hQ k s Gj - H) := by
        rw [map_sub]
        abel
      have h1 := norm_sub_le
        (translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ k s Gj - H) +
          (translationLp Q hQ (u • unitVector j) H - H)) (hDiffQuot Q hQ k s Gj - H)
      have h2 := norm_add_le (translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ k s Gj - H))
        (translationLp Q hQ (u • unitVector j) H - H)
      have h3 := norm_translationLp Q hQ (u • unitVector j) (hDiffQuot Q hQ k s Gj - H)
      rw [e]
      linarith
    have hA : Tendsto (fun s : ℝ =>
        ‖hDiffQuot Q hQ j t (hDiffQuot Q hQ k s F) - hDiffQuot Q hQ k s Gj‖)
        (𝓝[≠] (0 : ℝ)) (𝓝 ‖hDiffQuot Q hQ j t Gk - H‖) := by
      have hA1 := ((continuous_hDiffQuot hQ j t).tendsto Gk).comp hkF
      exact (hA1.sub hkG).norm
    have hB : Tendsto (fun s : ℝ => 2 * ‖hDiffQuot Q hQ k s Gj - H‖ + ε) (𝓝[≠] (0 : ℝ))
        (𝓝 (2 * ‖H - H‖ + ε)) := by
      have hH0 : Tendsto (fun s : ℝ => hDiffQuot Q hQ k s Gj - H) (𝓝[≠] (0 : ℝ))
          (𝓝 (H - H)) := hkG.sub (tendsto_const_nhds : Tendsto (fun _ : ℝ => H) _ (𝓝 H))
      exact ((hH0.norm).const_mul 2).add (tendsto_const_nhds : Tendsto (fun _ : ℝ => ε) _ (𝓝 ε))
    have hfin := le_of_tendsto_of_tendsto' hA hB hbound
    rw [sub_self, norm_zero, mul_zero, zero_add] at hfin
    exact hfin
  -- The `j`-difference quotients of `Gk` converge to `H`.
  have hlim : Tendsto (fun t : ℝ => hDiffQuot Q hQ j t Gk) (𝓝[≠] (0 : ℝ)) (𝓝 H) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδ, hδK⟩ := hK (ε / 2) (half_pos hε)
    have hab : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), |t| < δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with t ht
      simpa [Real.dist_eq] using ht
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (0 : ℝ), |t| < δ :=
      eventually_nhdsWithin_of_eventually_nhds hab
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have ht0 : t ≠ 0 := Set.mem_compl_singleton_iff.mp htne
    show dist (hDiffQuot Q hQ j t Gk) H < ε
    rw [dist_eq_norm]
    exact lt_of_le_of_lt (hδK t ht0 ht) (by linarith)
  have hj'' := hasHorizontalLpDerivative_iff_tendsto.mp hj'
  exact (tendsto_nhds_unique hj'' hlim).symm

/-! ### Integration by parts along translation orbits -/

/-- Pairing with a square-integrable scalar field, as a continuous linear functional on `L²`. -/
noncomputable def boundedPairing (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (f : FieldPair d → ℝ) (hf : MemLp f 2 Q) : Lp ℝ 2 Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing Q 2 2 (hf.toLp f)

theorem boundedPairing_apply (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (f : FieldPair d → ℝ) (hf : MemLp f 2 Q) (g : Lp ℝ 2 Q) :
    boundedPairing Q f hf g = ∫ ω, f ω * g ω ∂Q := by
  unfold boundedPairing
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hf] with ω hω
  simp only [hω, ContinuousLinearMap.mul_apply']

/-- Change of variables under a stationary law, for an a.e. strongly measurable observable. -/
theorem integral_translate_aestronglyMeasurable (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) (g : FieldPair d → ℝ) (hg : AEStronglyMeasurable g Q) :
    ∫ ω, g (translate x ω) ∂Q = ∫ ω, g ω ∂Q := by
  have hmeas : AEMeasurable (translate x) Q :=
    (measurePreserving_translate Q hQ x).measurable.aemeasurable
  have hfm : AEStronglyMeasurable g (Measure.map (translate x) Q) := by
    rw [hQ x]
    exact hg
  calc ∫ ω, g (translate x ω) ∂Q = ∫ ω, g ω ∂(Measure.map (translate x) Q) :=
        (integral_map hmeas hfm).symm
    _ = ∫ ω, g ω ∂Q := by rw [hQ x]

theorem measurable_orbit_point {d : ℕ} {f : FieldPair d → ℝ} (hf : Measurable f) (x : Vec d) :
    Measurable (fun ω : FieldPair d => orbit f ω x) :=
  hf.comp (Probability.measurable_translate x)

/-- The orbit difference quotient in coordinate `i`: `s⁻¹ (f(T_{-s e_i} ω) - f ω)`. -/
noncomputable def orbitDiffQuot {d : ℕ} (f : FieldPair d → ℝ) (i : Fin d) (s : ℝ)
    (ω : FieldPair d) : ℝ :=
  s⁻¹ * (orbit f ω ((-s) • unitVector i) - orbit f ω 0)

theorem measurable_orbitDiffQuot {d : ℕ} {f : FieldPair d → ℝ} (hf : Measurable f) (i : Fin d)
    (s : ℝ) : Measurable (fun ω => orbitDiffQuot f i s ω) := by
  unfold orbitDiffQuot
  exact measurable_const.mul ((measurable_orbit_point hf _).sub (measurable_orbit_point hf _))

/-- Slope of a real function at `0` along the reflected parameter. -/
theorem tendsto_slope_neg (k : ℝ → ℝ) (k' : ℝ) (hk : HasDerivAt k k' 0) :
    Tendsto (fun s : ℝ => s⁻¹ * (k (-s) - k 0)) (𝓝[≠] (0 : ℝ)) (𝓝 (-k')) := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hk0 : HasDerivAt k k' ((fun s : ℝ => -s) 0) := by simpa using hk
  have hc : HasDerivAt (fun s : ℝ => k (-s)) (k' * -1) 0 := HasDerivAt.comp 0 hk0 hneg
  have h2 := hasDerivAt_iff_tendsto_slope_zero.mp hc
  rw [mul_neg_one] at h2
  refine h2.congr (fun s => ?_)
  simp [smul_eq_mul]

theorem tendsto_orbitDiffQuot {d : ℕ} (f : FieldPair d → ℝ) (i : Fin d) (ω : FieldPair d)
    (hd : ∀ x, DifferentiableAt ℝ (orbit f ω) x) :
    Tendsto (fun s : ℝ => orbitDiffQuot f i s ω) (𝓝[≠] (0 : ℝ))
      (𝓝 (-horizontalDerivative i f ω)) := by
  have hk : HasDerivAt (fun u : ℝ => orbit f ω (u • unitVector i))
      (horizontalDerivative i f ω) 0 := by
    have h := hasDerivAt_orbit_line i f ω 0 (hd _)
    rw [zero_smul] at h
    exact h
  refine (tendsto_slope_neg _ _ hk).congr (fun s => ?_)
  unfold orbitDiffQuot
  simp only [zero_smul]

/-- The orbit difference quotient is bounded by the uniform bound on the coordinate derivative. -/
theorem abs_orbitDiffQuot_le {d : ℕ} (f : FieldPair d → ℝ) (i : Fin d) (ω : FieldPair d) {C : ℝ}
    (hd : ∀ x, DifferentiableAt ℝ (orbit f ω) x)
    (hC : ∀ x, |coordinateDerivative i (orbit f ω) x| ≤ C) {s : ℝ} (hs : s ≠ 0) :
    |orbitDiffQuot f i s ω| ≤ C := by
  have hline : ∀ u : ℝ, HasDerivWithinAt (fun r : ℝ => orbit f ω (r • unitVector i))
      (coordinateDerivative i (orbit f ω) (u • unitVector i)) Set.univ u := fun u =>
    (hasDerivAt_orbit_line i f ω u (hd _)).hasDerivWithinAt
  have hbound : ∀ u ∈ (Set.univ : Set ℝ),
      ‖coordinateDerivative i (orbit f ω) (u • unitVector i)‖ ≤ C := fun u _ => by
    rw [Real.norm_eq_abs]
    exact hC _
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := C) (fun u _ => hline u)
    hbound convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ (-s))
  have hb2 : |orbit f ω ((-s) • unitVector i) - orbit f ω 0| ≤ C * |s| := by
    simpa only [Real.norm_eq_abs, zero_smul, sub_zero, abs_neg] using hb
  unfold orbitDiffQuot
  rw [abs_mul, abs_inv]
  calc |s|⁻¹ * |orbit f ω ((-s) • unitVector i) - orbit f ω 0|
      ≤ |s|⁻¹ * (C * |s|) := mul_le_mul_of_nonneg_left hb2 (by positivity)
    _ = C := by rw [mul_comm C, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hs), one_mul]

/-- The pairing of `L²` with a bounded field against the difference quotient equals the integral
against the orbit difference quotient of that field. -/
theorem boundedPairing_hDiffQuot {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {i : Fin d} {f : FieldPair d → ℝ} (hf : MemLp f 2 Q)
    (hfm : Measurable f) {F : Lp ℝ 2 Q} {M : ℝ} (hM : ∀ᵐ ω ∂Q, |F ω| ≤ M) (s : ℝ) :
    boundedPairing Q f hf (hDiffQuot Q hQ i s F) =
      ∫ ω, F ω * orbitDiffQuot f i s ω ∂Q := by
  have hf1 : Integrable f Q := MemLp.integrable one_le_two hf
  set y := -(s • unitVector i) with hy
  have hfT : Integrable (fun ω => f (translate y ω)) Q :=
    (MeasurePreserving.integrable_comp (measurePreserving_translate Q hQ y)
      hf1.aestronglyMeasurable).mpr hf1
  have hA : Integrable (fun ω => f (translate y ω) * F ω) Q :=
    hfT.mul_bdd (c := M) (Lp.aestronglyMeasurable F) (hM.mono fun ω hω => by
      rw [Real.norm_eq_abs]; exact hω)
  have hB : Integrable (fun ω => f ω * F ω) Q := integrable_mul_of_ae_bound hf1 hM
  have hcancel : ∀ ω, translate y (translate (s • unitVector i) ω) = ω := fun ω => by
    rw [hy, translate_add, neg_add_cancel, translate_zero]
  have hT : ∫ ω, f ω * (translationLp Q hQ (s • unitVector i) F) ω ∂Q =
      ∫ ω, f (translate y ω) * F ω ∂Q := by
    have hg : AEStronglyMeasurable (fun η => f (translate y η) * F η) Q :=
      ((hfm.comp (Probability.measurable_translate y)).aestronglyMeasurable).mul
        (Lp.aestronglyMeasurable F)
    calc ∫ ω, f ω * (translationLp Q hQ (s • unitVector i) F) ω ∂Q
        = ∫ ω, f ω * F (translate (s • unitVector i) ω) ∂Q :=
          integral_congr_ae (by
            filter_upwards [coeFn_translationLp Q hQ (s • unitVector i) F] with ω hω
            rw [hω])
      _ = ∫ ω, (fun η => f (translate y η) * F η) (translate (s • unitVector i) ω) ∂Q :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω => by
            show f ω * F (translate (s • unitVector i) ω) =
              f (translate y (translate (s • unitVector i) ω)) * F (translate (s • unitVector i) ω)
            rw [hcancel ω])
      _ = ∫ ω, f (translate y ω) * F ω ∂Q :=
          integral_translate_aestronglyMeasurable Q hQ (s • unitVector i) _ hg
  have hP : boundedPairing Q f hf (hDiffQuot Q hQ i s F) =
      s⁻¹ * (boundedPairing Q f hf (translationLp Q hQ (s • unitVector i) F) -
        boundedPairing Q f hf F) := by
    unfold hDiffQuot
    rw [map_smul, map_sub, smul_eq_mul]
  have hneg : (-s) • unitVector i = y := neg_smul s (unitVector i)
  have hsplit : s⁻¹ * (∫ ω, f (translate y ω) * F ω ∂Q - ∫ ω, f ω * F ω ∂Q) =
      ∫ ω, F ω * orbitDiffQuot f i s ω ∂Q := by
    rw [← integral_sub hA hB, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [orbitDiffQuot, hneg, orbit, translate_zero]
    ring
  rw [hP, boundedPairing_apply Q f hf, boundedPairing_apply Q f hf, hT]
  exact hsplit

/-- **Integration by parts along orbits.** For a square-integrable scalar field `f` whose orbits are
differentiable with uniformly bounded coordinate derivative in direction `i`, and a bounded `F`
with `L²` generator derivative `G` in direction `i`, one has `E[f G] = -E[(∂_i f) F]`. -/
theorem integral_mul_horizontalDerivative_eq_neg (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} (i : Fin d) {f : FieldPair d → ℝ}
    (hf : MemLp f 2 Q) (hfm : Measurable f)
    (hfd : ∀ ω, ∀ x, DifferentiableAt ℝ (orbit f ω) x) {C : ℝ}
    (hC : ∀ ω x, |coordinateDerivative i (orbit f ω) x| ≤ C) {F G : Lp ℝ 2 Q}
    (hFb : ∃ M : ℝ, ∀ᵐ ω ∂Q, |F ω| ≤ M) (hG : HasHorizontalLpDerivative Q hQ i F G) :
    ∫ ω, f ω * G ω ∂Q = -∫ ω, horizontalDerivative i f ω * F ω ∂Q := by
  obtain ⟨M, hM⟩ := hFb
  have hid : ∀ s : ℝ, boundedPairing Q f hf (hDiffQuot Q hQ i s F) =
      ∫ ω, F ω * orbitDiffQuot f i s ω ∂Q :=
    fun s => boundedPairing_hDiffQuot hf hfm hM s
  -- Dominated convergence for the orbit difference quotients.
  have hdct : Tendsto (fun s : ℝ => ∫ ω, F ω * orbitDiffQuot f i s ω ∂Q) (𝓝[≠] (0 : ℝ))
      (𝓝 (∫ ω, F ω * (-horizontalDerivative i f ω) ∂Q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => max M 0 * max C 0) ?_ ?_
      (integrable_const _) ?_
    · exact Filter.Eventually.of_forall fun s =>
        (Lp.aestronglyMeasurable F).mul (measurable_orbitDiffQuot hfm i s).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact ae_norm_mul_le hM (Filter.Eventually.of_forall fun ω =>
        abs_orbitDiffQuot_le f i ω (hfd ω) (hC ω) (Set.mem_compl_singleton_iff.mp hs))
    · exact Filter.Eventually.of_forall fun ω =>
        (tendsto_orbitDiffQuot f i ω (hfd ω)).const_mul (F ω)
  have hG' : Tendsto (fun s : ℝ => hDiffQuot Q hQ i s F) (𝓝[≠] (0 : ℝ)) (𝓝 G) :=
    hG
  have hlim : Tendsto (fun s : ℝ => boundedPairing Q f hf (hDiffQuot Q hQ i s F))
      (𝓝[≠] (0 : ℝ)) (𝓝 (boundedPairing Q f hf G)) :=
    ((boundedPairing Q f hf).continuous.tendsto G).comp hG'
  have hlim2 : Tendsto (fun s : ℝ => ∫ ω, F ω * orbitDiffQuot f i s ω ∂Q) (𝓝[≠] (0 : ℝ))
      (𝓝 (boundedPairing Q f hf G)) := by
    simpa only [hid] using hlim
  have heq := tendsto_nhds_unique hlim2 hdct
  rw [boundedPairing_apply Q f hf] at heq
  rw [heq, ← integral_neg]
  congr 1
  funext ω
  ring

/-- **Weak divergence of a coefficient column.** Let `a = ω.1 0` be the coefficient at the origin.
If each entry `x ↦ ω.1 x j k` is differentiable, its coordinate derivatives are bounded uniformly in
`ω`, `x`, and the entries are square-integrable, then the column field `a e_i` has weak horizontal
divergence `h(ω) = ∑ⱼ ∂ⱼ (ω.1 x)_{j i}` at `x = 0`. The proof is orbit integration by parts in each
coordinate. The Lipschitz case needs the same argument along lines, with differentiability holding
almost everywhere on each line; it is not covered here. -/
theorem hasWeakHorizontalDivergence_mulVec_unitVector (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} (i : Fin d)
    (hC1 : ∀ (ω : FieldPair d) (j k : Fin d), Differentiable ℝ (fun x : Vec d => ω.1 x j k))
    (hCb : ∃ C : ℝ, ∀ (ω : FieldPair d) (j k : Fin d) (x : Vec d),
      |coordinateDerivative j (fun y : Vec d => ω.1 y j k) x| ≤ C)
    (hmem : ∀ j k : Fin d, MemLp (fun ω : FieldPair d => ω.1 0 j k) 2 Q) :
    HasWeakHorizontalDivergence Q hQ (fun ω => (ω.1 0).mulVec (unitVector i))
      (fun ω => ∑ j : Fin d, coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0) := by
  obtain ⟨C, hC⟩ := hCb
  have hvec : ∀ (ω : FieldPair d) (j : Fin d), ((ω.1 0).mulVec (unitVector i)) j = ω.1 0 j i := by
    intro ω j
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  have hdiff : ∀ (j k : Fin d) (ω : FieldPair d) (x : Vec d),
      DifferentiableAt ℝ (orbit (fun η : FieldPair d => η.1 0 j k) ω) x := by
    intro j k ω x
    rw [orbit_coeff_entry j k ω]
    exact hC1 ω j k x
  have hbd : ∀ (j k : Fin d) (ω : FieldPair d) (x : Vec d),
      |coordinateDerivative j (orbit (fun η : FieldPair d => η.1 0 j k) ω) x| ≤ C := by
    intro j k ω x
    rw [orbit_coeff_entry j k ω]
    exact hC ω j k x
  have hhd : ∀ (j : Fin d) (ω : FieldPair d),
      horizontalDerivative j (fun η : FieldPair d => η.1 0 j i) ω =
        coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0 := by
    intro j ω
    unfold horizontalDerivative
    rw [orbit_coeff_entry j i ω]
  have hint_entry : ∀ j : Fin d, Integrable (fun ω : FieldPair d => ω.1 0 j i) Q := fun j =>
    MemLp.integrable one_le_two (hmem j i)
  have hint_hd : ∀ j : Fin d, Integrable
      (fun ω : FieldPair d => horizontalDerivative j (fun η : FieldPair d => η.1 0 j i) ω) Q := by
    intro j
    refine Integrable.of_bound (measurable_horizontalDerivative j _ (measurable_coeff_entry j i)
      (fun ω => hdiff j i ω 0)).aestronglyMeasurable C (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact hbd j i ω 0
  refine ⟨fun j => ?_, ?_, fun F hF DF hDF => ?_⟩
  · simp only [hvec]
    exact hint_entry j
  · have hfun : (fun ω : FieldPair d => ∑ j : Fin d, coordinateDerivative j
          (fun y : Vec d => ω.1 y j i) 0) =
        fun ω => ∑ j : Fin d, horizontalDerivative j (fun η : FieldPair d => η.1 0 j i) ω := by
      funext ω
      simp only [hhd]
    show Integrable (fun ω : FieldPair d => ∑ j : Fin d, coordinateDerivative j
      (fun y : Vec d => ω.1 y j i) 0) Q
    rw [hfun]
    exact integrable_finset_sum _ fun j _ => hint_hd j
  · obtain ⟨M, hM⟩ := ae_bound_of_isHorizontallySmoothTest hF
    have hIBP : ∀ j : Fin d, ∫ ω, ((ω.1 0).mulVec (unitVector i)) j * DF j ω ∂Q =
        -∫ ω, coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0 * F ω ∂Q := by
      intro j
      have h := integral_mul_horizontalDerivative_eq_neg Q j (hmem j i)
        (measurable_coeff_entry j i) (fun ω x => hdiff j i ω x) (C := C)
        (fun ω x => hbd j i ω x) ⟨M, hM⟩ (hDF j)
      simp only [hvec, hhd] at h ⊢
      exact h
    have hV : ∀ j : Fin d, Integrable
        (fun ω : FieldPair d => ((ω.1 0).mulVec (unitVector i)) j * DF j ω) Q := by
      intro j
      obtain ⟨N, hN⟩ := ae_bound_of_hasHorizontalLpDerivative hF (hDF j)
      simp only [hvec]
      exact integrable_mul_of_ae_bound (hint_entry j) hN
    have hHF : ∀ j : Fin d, Integrable
        (fun ω : FieldPair d => coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0 * F ω) Q := by
      intro j
      have h := integrable_mul_of_ae_bound (hint_hd j) hM
      simp only [hhd] at h
      exact h
    have hsumV : (∫ ω, (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) ∂Q) =
        ∑ j : Fin d, ∫ ω, ((ω.1 0).mulVec (unitVector i)) j * DF j ω ∂Q :=
      integral_finset_sum _ fun j _ => hV j
    have hsumH : (∫ ω, (∑ j : Fin d, coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0) *
          F ω ∂Q) =
        ∑ j : Fin d, ∫ ω, coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0 * F ω ∂Q := by
      simp only [Finset.sum_mul]
      exact integral_finset_sum _ fun j _ => hHF j
    show (∫ ω, (∑ j : Fin d, ((ω.1 0).mulVec (unitVector i)) j * DF j ω) ∂Q) =
      -(∫ ω, (∑ j : Fin d, coordinateDerivative j (fun y : Vec d => ω.1 y j i) 0) * F ω ∂Q)
    rw [hsumV, hsumH, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hIBP j

end EinsteinRelation

end
