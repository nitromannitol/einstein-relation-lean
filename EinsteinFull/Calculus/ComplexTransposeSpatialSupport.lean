import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinFull.Calculus.ComplexTransposeResolventSupport

/-!
# Physical divergence of the actual bilinear transpose graph

The force belongs inside the conservative flux `a G - 2*zeta*a e_i*f`.
The actual horizontal transpose graph supplies the divergence equation on
one event before all compact spatial tests. No negative-force forward
identification or spatial regularity beyond the full graph is assumed.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

private theorem coefficient_measurable (j k : Fin d) :
    Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
  (Complex.continuous_ofReal.comp
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable

/-- The full bilinear transpose graph has its literal conservative horizontal
flux, with the derivative on every weak test in the force term. -/
theorem IsComplexTransposeGeneratorPair.horizontal_flux
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, ∑ j, ((∑ k, (ω.1 0 j k : ℂ) * G k ω) -
      2 * ζ * (ω.1 0 j i : ℂ) * f ω) * V j ω ∂reducedLaw Q) =
      -(∫ ω, (2 : ℂ) * g ω * v ω ∂reducedLaw Q) := by
  obtain ⟨H, hH, hw⟩ := hfg
  have hHG : H = G := hH.unique hG
  subst H
  have hp : Integrable (fun ω => ∑ j, ∑ k,
      (ω.1 0 j k : ℂ) * G k ω * V j ω) (reducedLaw Q) := by
    simpa only [Pi.mul_apply, Finset.sum_mul] using integrable_finset_sum Finset.univ
      (fun j _ => (memLp_complex_coefficient_flux Q G j).integrable_mul (Lp.memLp (V j)))
  have hd : Integrable (fun ω => f ω * (∑ j, (ω.1 0 j i : ℂ) * V j ω))
      (reducedLaw Q) := by
    have hj (j : Fin d) : Integrable (fun ω => (ω.1 0 j i : ℂ) * (f ω * V j ω))
        (reducedLaw Q) :=
      ((Lp.memLp f).integrable_mul (Lp.memLp (V j))).mul_of_top_right
        (memLp_reduced_coefficient_complex Q j i)
    have he : (fun ω => f ω * (∑ j, (ω.1 0 j i : ℂ) * V j ω)) =
        (fun ω => ∑ j, (ω.1 0 j i : ℂ) * (f ω * V j ω)) := by
      funext ω
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact integrable_finset_sum _ fun j _ => hj j
  have he : (fun ω => ∑ j, ((∑ k, (ω.1 0 j k : ℂ) * G k ω) -
      2 * ζ * (ω.1 0 j i : ℂ) * f ω) * V j ω) =
      (fun ω => (∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * V j ω) -
        (2 * ζ) * (f ω * (∑ j, (ω.1 0 j i : ℂ) * V j ω))) := by
    funext ω
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he, integral_sub hp (hd.const_mul (2 * ζ)), integral_const_mul]
  have hg : (∫ ω, (2 : ℂ) * g ω * v ω ∂reducedLaw Q) =
      2 * (∫ ω, g ω * v ω ∂reducedLaw Q) := by
    simp only [mul_assoc, integral_const_mul]
  rw [hg]
  linear_combination 2 * hw v V hV

/-- The actual bilinear transpose graph gives one spatial divergence event
before all compact smooth tests. The entire conservative flux is retained. -/
theorem IsComplexTransposeGeneratorPair.spatial_flux_all_tests
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        (∫ x, g (translate x ω) * (φ x : ℂ)) =
          -(1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
              2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
                (coordinateDerivative j φ x : ℂ)) := by
  let F : Fin d → FieldPair d → ℂ := fun j ω =>
    (∑ k, (ω.1 0 j k : ℂ) * G k ω) - 2 * ζ * (ω.1 0 j i : ℂ) * f ω
  have hFm (j : Fin d) : Measurable (F j) :=
    (Finset.measurable_sum _ fun k _ => (coefficient_measurable j k).mul
      (Lp.stronglyMeasurable _).measurable).sub
        ((measurable_const.mul (coefficient_measurable j i)).mul
          (Lp.stronglyMeasurable f).measurable)
  have hF (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    have ha := (Lp.memLp (complexCoefficientMul Q j i f)).ae_eq
      (complexCoefficientMul_coe Q j i f)
    simpa only [F, mul_assoc] using!
      (memLp_complex_coefficient_flux Q G j).sub (ha.const_mul (2 * ζ))
  have hh : MemLp (fun ω => (2 : ℂ) * g ω) 2 (reducedLaw Q) := (Lp.memLp g).const_mul 2
  have he := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F (fun ω => (2 : ℂ) * g ω) hFm
    (measurable_const.mul (Lp.stronglyMeasurable g).measurable) hF hh
    (fun v V hV => by simpa only [F, mul_assoc] using hfg.horizontal_flux hG v V hV)
  filter_upwards [he] with ω he
  intro φ hφ hφc
  have he := he φ hφ hφc
  simp only [F, translate_matrix, add_zero] at he
  simp only [mul_assoc, integral_const_mul] at he ⊢
  linear_combination (1 / 2 : ℂ) * he

/-- The full transpose graph supplies its gradient internally before the
single common spatial weak-equation event. -/
theorem IsComplexTransposeGeneratorPair.exists_spatial_flux_all_tests
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, g (translate x ω) * (φ x : ℂ)) =
            -(1 / 2 : ℂ) * (∫ x, ∑ j,
              ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
                2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
                  (coordinateDerivative j φ x : ℂ)) := by
  have hex := hfg
  obtain ⟨G, hG, _⟩ := hex
  exact ⟨G, hG, hfg.spatial_flux_all_tests hG⟩

end EinsteinFull
