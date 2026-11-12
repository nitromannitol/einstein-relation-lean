import EinsteinRelation.Correctors.EuclideanCoordinateCharacterization
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Linear
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Calculus

open MeasureTheory
open WithLp
open Filter
open scoped RealInnerProductSpace
namespace EinsteinRelation.Correctors

/-- Assemble differentiable scalar L² coordinate curves into the actual
Euclidean-valued L² curve. Source: `paper/main.tex:798–806`; temporal smoothing. -/
theorem exists_differentiable_L2_euclidean_curve {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (f f' : ℝ → Fin d → Lp ℝ 2 μ)
    (hf : ∀ t i, HasDerivAt (fun s => f s i) (f' t i) t) :
    ∃ F F' : ℝ → Lp (EuclideanSpace ℝ (Fin d)) 2 μ,
      (∀ t i, (fun ω => F t ω i) =ᵐ[μ] (f t i : Ω → ℝ)) ∧
      (∀ t i, (fun ω => F' t ω i) =ᵐ[μ] (f' t i : Ω → ℝ)) ∧
      ∀ t, HasDerivAt F (F' t) t := by
  classical
  let e (i : Fin d) : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (Pi.single i 1)
  let J (i : Fin d) : Lp ℝ 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin d)) 2 μ :=
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).compLpL 2 μ
  have hJ (v : Fin d → Lp ℝ 2 μ) (j : Fin d) :
      (fun ω => (∑ i, J i (v i)) ω j) =ᵐ[μ] (v j : Ω → ℝ) := by
    have hi i := ((ContinuousLinearMap.id ℝ ℝ).smulRight (e i)).coeFn_compLpL (v i)
    have hsum (S : Finset (Fin d)) :
        ((∑ i ∈ S, J i (v i) : Lp (EuclideanSpace ℝ (Fin d)) 2 μ) : Ω → EuclideanSpace ℝ (Fin d)) =ᵐ[μ]
          fun ω => ∑ i ∈ S, J i (v i) ω := by
      induction S using Finset.induction_on with
      | empty => simpa using (Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin d)) (p := 2) (μ := μ))
      | @insert i S hi hind =>
        simp only [Finset.sum_insert hi]
        exact (Lp.coeFn_add _ _).trans (Filter.EventuallyEq.rfl.add hind)
    filter_upwards [hsum Finset.univ,
      ae_all_iff.mpr hi] with ω hsum hω
    rw [hsum]
    simp only [WithLp.ofLp_sum,Finset.sum_apply]
    have hω' (i : Fin d) : J i (v i) ω = (v i ω) • e i := hω i
    simp only [hω',PiLp.smul_apply,smul_eq_mul]
    simp [e,Pi.single_apply,mul_ite]
  refine ⟨fun t => ∑ i, J i (f t i), fun t => ∑ i, J i (f' t i),
    fun t i => hJ (f t) i, fun t i => hJ (f' t) i, ?_⟩
  intro t
  simpa only [Finset.sum_apply,Function.comp_def] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ => (J i).hasFDerivAt.comp_hasDerivAt t (hf t i))

end EinsteinRelation.Correctors
