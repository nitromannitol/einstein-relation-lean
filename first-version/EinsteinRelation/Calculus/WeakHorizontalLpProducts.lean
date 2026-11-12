import EinsteinRelation.Calculus.WeakHorizontalProducts
import EinsteinRelation.Calculus.WeakCalculusAlgebra
import EinsteinRelation.Entropy.EllipticRegularity

/-! # Products of square-integrable weak horizontal fields

Source: `paper/main.tex:1044–1069`, Steps 3 and 4 of Proposition 6.1.
The product of two fields with square-integrable weak gradients has the usual
integrable weak gradient. No boundedness of either field is required: the proof
uses the existing approximation in the horizontal Sobolev norm.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-- A bounded scalar multiplier preserves an `L²` moment. -/
theorem memLp_mul_of_ae_bound {Ω : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 Q) (hgm : AEStronglyMeasurable g Q)
    {B : ℝ} (hg : ∀ᵐ ω ∂Q, |g ω| ≤ B) : MemLp (fun ω => f ω * g ω) 2 Q := by
  refine (hf.const_mul B).of_le (hf.1.mul hgm) ?_
  filter_upwards [hg] with ω hω
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  exact (mul_le_mul_of_nonneg_left hω (abs_nonneg _)).trans
    (by rw [mul_comm (|f ω|) B]; exact mul_le_mul_of_nonneg_right (le_abs_self B) (abs_nonneg _))

/-- Weak gradients are unchanged by almost-everywhere changes of representatives. -/
theorem HasWeakHorizontalGradient.congr_ae {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f f' : FieldPair d → ℝ} {Df Df' : FieldPair d → Vec d}
    (hf : HasWeakHorizontalGradient Q hQ f Df) (hff' : f =ᵐ[Q] f')
    (hDD' : Df =ᵐ[Q] Df') : HasWeakHorizontalGradient Q hQ f' Df' := by
  refine ⟨hf.1.congr hff', fun i => (hf.2.1 i).congr
    (hDD'.mono fun ω hω => congrFun hω i), fun i F G hF hG => ?_⟩
  calc
    (∫ ω, f' ω * G ω ∂Q) = ∫ ω, f ω * G ω ∂Q :=
      integral_congr_ae (hff'.mono fun ω hω => by dsimp only; rw [hω])
    _ = -(∫ ω, Df ω i * F ω ∂Q) := hf.2.2 i F G hF hG
    _ = -(∫ ω, Df' ω i * F ω ∂Q) := by
      congr 1
      exact integral_congr_ae (hDD'.mono fun ω hω => by dsimp only; rw [hω])

/-- The strong translation generators give a weak gradient on representatives. -/
theorem hasWeakHorizontalGradient_of_generators {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℝ 2 Q)
    (Df : Fin d → Lp ℝ 2 Q) (hf : ∀ i, HasHorizontalLpDerivative Q hQ i f (Df i)) :
    HasWeakHorizontalGradient Q hQ (fun ω => f ω) (fun ω i => Df i ω) := by
  refine ⟨(Lp.memLp f).integrable one_le_two,
    fun i => (Lp.memLp (Df i)).integrable one_le_two, fun i F G _ hG => ?_⟩
  have h := (Correctors.horizontalGenerators_integration_by_parts Q hQ i f (Df i) F G
    (hf i) hG).2.2
  linarith only [h]

/-- Product rule for two square-integrable weak horizontal fields, with
square-integrable gradients (`paper/main.tex:1044–1054`). -/
theorem HasWeakHorizontalGradient.mul_of_memLp_two {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q}
    {f g : FieldPair d → ℝ} {Df Dg : FieldPair d → Vec d}
    (hf : HasWeakHorizontalGradient Q hQ f Df) (hg : HasWeakHorizontalGradient Q hQ g Dg)
    (hfm : Measurable f) (hgm : Measurable g) (hDfm : Measurable Df) (hDgm : Measurable Dg)
    (hf2 : MemLp f 2 Q) (hg2 : MemLp g 2 Q)
    (hDf2 : ∀ i, MemLp (fun ω => Df ω i) 2 Q)
    (hDg2 : ∀ i, MemLp (fun ω => Dg ω i) 2 Q) :
    HasWeakHorizontalGradient Q hQ (fun ω => f ω * g ω)
      (fun ω i => g ω * Df ω i + f ω * Dg ω i) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  obtain ⟨gn, Dgn, hgn, -, hDgn, -, hgnlim, hDgnsub, hDgnlim⟩ :=
    Entropy.exists_test_approximation hQ (q := 2) ENNReal.ofNat_ne_top hg hg2 hDg2 hgm hDgm
  have hgn2 : ∀ n, MemLp (gn n) 2 Q := fun n => (hgn n).memLp Q 2
  have hDgn2 : ∀ n i, MemLp (fun ω => Dgn n ω i) 2 Q := fun n i =>
    Entropy.memLp_of_sub_add (hDgnsub n i) (hDg2 i)
  have hgi : ∀ i, Integrable (fun ω => g ω * Df ω i + f ω * Dg ω i) Q :=
    fun i => (hg2.integrable_mul (hDf2 i)).add (hf2.integrable_mul (hDg2 i))
  refine ⟨hf2.integrable_mul hg2, hgi, fun i F G hFs hG => ?_⟩
  obtain ⟨A, hA⟩ := ae_bound_of_isHorizontallySmoothTest hFs
  obtain ⟨B, hB⟩ := ae_bound_of_hasHorizontalLpDerivative hFs hG
  have hfF2 := memLp_mul_of_ae_bound hf2 (Lp.aestronglyMeasurable F) hA
  have hfG2 := memLp_mul_of_ae_bound hf2 (Lp.aestronglyMeasurable G) hB
  have hDfF2 := memLp_mul_of_ae_bound (hDf2 i) (Lp.aestronglyMeasurable F) hA
  have hleft := Entropy.tendsto_integral_mul_of_eLpNorm_two hfG2 hgn2 hg2 hgnlim
  have hright₁ := Entropy.tendsto_integral_mul_of_eLpNorm_two hDfF2 hgn2 hg2 hgnlim
  have hright₂ := Entropy.tendsto_integral_mul_of_eLpNorm_two hfF2 (fun n => hDgn2 n i)
    (hDg2 i) (hDgnlim i)
  have heq : ∀ n, (∫ ω, (f ω * G ω) * gn n ω ∂Q) =
      -((∫ ω, (Df ω i * F ω) * gn n ω ∂Q) +
        ∫ ω, (f ω * F ω) * Dgn n ω i ∂Q) := by
    intro n
    have hw := (hf.mul_horizontalTest hfm hDfm (hgn n)).2.2 i F G hFs hG
    have e₁ : (∫ ω, (f ω * gn n ω) * G ω ∂Q) =
        ∫ ω, (f ω * G ω) * gn n ω ∂Q := by
      congr 1
      funext ω
      ring
    have e₂ : (∫ ω, (gn n ω * Df ω i + f ω * horizontalDerivative i (gn n) ω) * F ω ∂Q) =
        (∫ ω, (Df ω i * F ω) * gn n ω ∂Q) +
          ∫ ω, (f ω * F ω) * Dgn n ω i ∂Q := by
      calc
        _ = ∫ ω, ((Df ω i * F ω) * gn n ω + (f ω * F ω) * Dgn n ω i) ∂Q := by
          apply integral_congr_ae
          filter_upwards [hDgn n] with ω hω
          rw [hω i]
          ring
        _ = _ := integral_add (hDfF2.integrable_mul (hgn2 n))
          (hfF2.integrable_mul (hDgn2 n i))
    rwa [e₁, e₂] at hw
  have hlim := tendsto_nhds_unique (hleft.congr heq) ((hright₁.add hright₂).neg)
  have e₁ : (∫ ω, (f ω * g ω) * G ω ∂Q) = ∫ ω, (f ω * G ω) * g ω ∂Q := by
    congr 1
    funext ω
    ring
  have e₂ : (∫ ω, (g ω * Df ω i + f ω * Dg ω i) * F ω ∂Q) =
      (∫ ω, (Df ω i * F ω) * g ω ∂Q) + ∫ ω, (f ω * F ω) * Dg ω i ∂Q := by
    calc
      _ = ∫ ω, ((Df ω i * F ω) * g ω + (f ω * F ω) * Dg ω i) ∂Q := by
        congr 1
        funext ω
        ring
      _ = _ := integral_add (hDfF2.integrable_mul hg2) (hfF2.integrable_mul (hDg2 i))
  rw [e₁, e₂]
  exact hlim

end EinsteinRelation
