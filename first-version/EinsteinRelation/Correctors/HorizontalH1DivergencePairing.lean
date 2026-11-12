import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport
import EinsteinRelation.Correctors.HorizontalGeneratorsIbP
import EinsteinRelation.Entropy.EllipticRegularity

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:808–816,926–938`. The full horizontal
weak-divergence equation is the variational pairing against every H¹
function, with the actual Euclidean L² gradient. -/
theorem horizontalH1_inner_gradient_eq_neg_of_div {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (h : Lp ℝ 2 Q)
    (hdiv : HasWeakHorizontalDivergence Q hQ (fun ω i => W ω i) h) :
    inner ℝ (horizontalEuclideanGradient Q hQ f) W =
      -inner ℝ (f : Lp ℝ 2 Q) h := by
  have hcoord : ∀ i, MemLp (fun ω => W ω i) 2 Q := fun i =>
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).comp_memLp'
      (Lp.memLp W)
  have hweak : HasWeakHorizontalGradient Q hQ (f : Lp ℝ 2 Q)
      (fun ω i => horizontalH1Gradient Q hQ f i ω) := by
    refine ⟨(Lp.memLp (f : Lp ℝ 2 Q)).integrable one_le_two,
      fun i => (Lp.memLp (horizontalH1Gradient Q hQ f i)).integrable one_le_two, ?_⟩
    intro i H DH _hH hDH
    have hp := horizontalGenerators_integration_by_parts Q hQ i H DH
      (f : Lp ℝ 2 Q) (horizontalH1Gradient Q hQ f i) hDH
      (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i)
    simpa only [mul_comm] using hp.2.2
  have hp := Entropy.sum_integral_mul_eq_neg_of_div hQ
    (Lp.stronglyMeasurable (f : Lp ℝ 2 Q)).measurable
    (Lp.memLp (f : Lp ℝ 2 Q))
    (measurable_pi_lambda _ fun i =>
      (Lp.stronglyMeasurable (horizontalH1Gradient Q hQ f i)).measurable)
    (fun i => Lp.memLp (horizontalH1Gradient Q hQ f i)) hweak hdiv hcoord (Lp.memLp h)
  rw [L2.inner_def, L2.inner_def]
  calc
    (∫ ω, inner ℝ (horizontalEuclideanGradient Q hQ f ω) (W ω) ∂Q) =
        ∫ ω, ∑ i, W ω i * horizontalH1Gradient Q hQ f i ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.2 (horizontalEuclideanGradient_coordinates Q hQ f)]
        with ω hω
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, hω]
    _ = ∑ i, ∫ ω, W ω i * horizontalH1Gradient Q hQ f i ω ∂Q :=
      integral_finset_sum _ fun i _ =>
        (hcoord i).integrable_mul (Lp.memLp (horizontalH1Gradient Q hQ f i))
    _ = -(∫ ω, h ω * (f : Lp ℝ 2 Q) ω ∂Q) := hp
    _ = _ := by simp only [RCLike.inner_apply, conj_trivial]

theorem horizontalH1_gradient_pairing_of_divergence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (h : Lp ℝ 2 Q)
    (hdiv : HasWeakHorizontalDivergence Q hQ (fun ω i => W ω i) h) :
    inner ℝ (horizontalEuclideanGradient Q hQ f) W =
      -inner ℝ (f : Lp ℝ 2 Q) h := by
  exact horizontalH1_inner_gradient_eq_neg_of_div Q hQ f W h hdiv

end EinsteinRelation.Correctors
