import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.L2BoundedMultiplier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Bounded measurable symmetric coefficient entries define their actual
continuous L² energy form. Source: `paper/main.tex:798–806`; temporal energy. -/
theorem exists_L2_matrix_energy_form {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {d : ℕ} (a : Ω → Mat d)
    (ha : ∀ i j, AEStronglyMeasurable (fun ω => a ω i j) μ)
    (hsymm : ∀ᵐ ω ∂μ, (a ω).transpose = a ω)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ ω ∂μ, ∀ i j, |a ω i j| ≤ M) :
    ∃ B : Lp (EuclideanSpace ℝ (Fin d)) 2 μ →L[ℝ]
        Lp (EuclideanSpace ℝ (Fin d)) 2 μ →L[ℝ] ℝ,
      (∀ f g, B f g = B g f) ∧
      ∀ f g, B f g = ∫ ω, dot ((a ω).mulVec (f ω).ofLp) (g ω).ofLp ∂μ := by
  classical
  let H := Lp (EuclideanSpace ℝ (Fin d)) 2 μ
  let S := Lp ℝ 2 μ
  let C (i : Fin d) : H →L[ℝ] S :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2 μ
  have hC (i : Fin d) (f : H) :
      (C i f : Ω → ℝ) =ᵐ[μ] fun ω => (f ω).ofLp i :=
    by
      have h := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL
        (f : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
      exact h
  choose T hT hTr using fun i j =>
    exists_L2_bounded_multiplier_map μ (fun ω => a ω i j) (ha i j) hM
      (hb.mono fun ω hω => hω i j)
  let b (i j : Fin d) : H →L[ℝ] H →L[ℝ] ℝ :=
    ((ContinuousLinearMap.precompR H (innerSL ℝ : S →L[ℝ] S →L[ℝ] ℝ)).flip (C i)).comp
      ((T i j).comp (C j))
  have hbij (i j : Fin d) (f g : H) :
      b i j f g = ∫ ω, a ω i j * (f ω).ofLp j * (g ω).ofLp i ∂μ := by
    change inner ℝ (T i j (C j f)) (C i g) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hTr i j (C j f),hC j f,hC i g] with ω h1 h2 h3
    simp only [RCLike.inner_apply,conj_trivial,h1,h2,h3,mul_comm]
  have hint (i j : Fin d) (f g : H) :
      Integrable (fun ω => a ω i j * (f ω).ofLp j * (g ω).ofLp i) μ := by
    apply ((Lp.memLp (T i j (C j f))).integrable_mul (Lp.memLp (C i g))).congr
    filter_upwards [hTr i j (C j f),hC j f,hC i g] with ω h1 h2 h3
    simp only [Pi.mul_apply,h1,h2,h3]
  let B : H →L[ℝ] H →L[ℝ] ℝ := ∑ i, ∑ j, b i j
  have hB (f g : H) : B f g = ∫ ω, dot ((a ω).mulVec (f ω).ofLp) (g ω).ofLp ∂μ := by
    change (∑ i, ∑ j, b i j) f g = _
    have he (i : Fin d) : (∑ j, b i j f g) =
        ∫ ω, ∑ j, a ω i j * (f ω).ofLp j * (g ω).ofLp i ∂μ := by
      simp_rw [hbij]
      exact (integral_finset_sum Finset.univ (fun j _ => hint i j f g)).symm
    simp only [ContinuousLinearMap.sum_apply,he]
    rw [← integral_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun j _ => hint i j f g))]
    apply integral_congr_ae
    filter_upwards with ω
    simp only [dot,Matrix.mulVec,dotProduct,Finset.sum_mul]
  refine ⟨B,?_,hB⟩
  intro f g
  rw [hB,hB]
  apply integral_congr_ae
  filter_upwards [hsymm] with ω hω
  change dotProduct ((a ω).mulVec (f ω).ofLp) (g ω).ofLp =
    dotProduct ((a ω).mulVec (g ω).ofLp) (f ω).ofLp
  rw [dotProduct_comm,Matrix.dotProduct_mulVec,← Matrix.vecMul_transpose,hω]

end EinsteinRelation.Correctors
