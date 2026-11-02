import EinsteinFull.Blueprint.G4.node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients
import EinsteinFull.Blueprint.Foundation.node_e_u3A_generators_u23_real_u2D_semigroup
import EinsteinFull.Blueprint.Foundation.node_corrector_u2D_construction
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup

open MeasureTheory Filter
open scoped Topology BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Correctors

private theorem gradient_components {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {f : Lp ℂ 2 μ} {V : Fin d → Lp ℂ 2 μ}
    (hV : HasComplexHorizontalGradient μ hμ f V)
    (him : horizontalEuclideanGradient μ hμ
      (complexHorizontalRealPart hV Complex.imCLM) = 0) :
    ∀ᵐ ω ∂μ, ∀ k,
      horizontalEuclideanGradient μ hμ (complexHorizontalRealPart hV Complex.reCLM) ω k =
        (V k ω).re ∧ (V k ω).im = 0 := by
  have hi := complexHorizontalRealPart_gradient_ae hV Complex.imCLM
  rw [him] at hi
  filter_upwards [complexHorizontalRealPart_gradient_ae hV Complex.reCLM,
    hi, Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 μ] with ω hr hi hz
  intro k
  refine ⟨hr k, ?_⟩
  change Complex.imCLM (V k ω) = 0
  rw [← hi k, hz]
  rfl

private theorem gradient_energy_integral {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (R g : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (hparts : ∀ᵐ ω ∂reducedLaw Q, ∀ k, R ω k = (V k ω).re ∧ (V k ω).im = 0) :
    (∫ ω, ∑ j : Fin d, ∑ k : Fin d, ω.1 0 j k *
      (((V j ω).re - g ω j) * ((V k ω).re - g ω k) +
        (V j ω).im * (V k ω).im) ∂reducedLaw Q) =
      inner ℝ (R - g) (reducedOriginCoefficientAction Q (R - g)) := by
  erw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hparts, Lp.coeFn_sub R g,
    reducedOriginCoefficientAction_coeFn Q (R - g)] with ω hp hsub hA
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change _ = ∑ j, (reducedOriginCoefficientAction Q (R - g) ω) j * (R - g) ω j
  simp only [hA, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  erw [hsub]
  simp only [Pi.sub_apply, PiLp.sub_apply]
  change _ = ω.1 0 j k * (R ω k - g ω k) * (R ω j - g ω j)
  rw [(hp j).1, (hp k).1, (hp j).2, (hp k).2]
  ring

private theorem tendsto_gradient_energy {d : ℕ} {Λ r : ℝ} {ι : Type*}
    (Q : EnvironmentLaw d Λ r) (V : ι → Fin d → Lp ℂ 2 (reducedLaw Q))
    (R : ι → Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) {l : Filter ι}
    (hparts : ∀ s, ∀ᵐ ω ∂reducedLaw Q, ∀ k,
      R s ω k = (V s k ω).re ∧ (V s k ω).im = 0)
    (hr : Tendsto R l (𝓝 g)) :
    Tendsto (fun s => ∫ ω, ∑ j : Fin d, ∑ k : Fin d, ω.1 0 j k *
      (((V s j ω).re - g ω j) * ((V s k ω).re - g ω k) +
        (V s j ω).im * (V s k ω).im) ∂reducedLaw Q) l (𝓝 0) := by
  have hz : Tendsto (fun s => R s - g) l (𝓝 0) := by
    simpa only [sub_self] using! hr.sub_const g
  have he := hz.inner (𝕜 := ℝ) ((reducedOriginCoefficientAction Q).continuous.tendsto 0 |>.comp hz)
  simp only [Function.comp_def, map_zero, inner_zero_right, inner_zero_left, inner_self_eq_zero] at he
  erw [inner_zero_left] at he
  have he' : Tendsto (fun s => inner ℝ (R s - g)
      (reducedOriginCoefficientAction Q (R s - g))) l (𝓝 0) := by
    simpa only [Function.comp_def] using! he
  apply he'.congr'
  exact Eventually.of_forall fun s => (gradient_energy_integral Q (V s) (R s) g (hparts s)).symm

/-- The actual massive gradients converge in the literal anisotropic energy.
The adopted variational proof supplies the two prescribed graph dependencies
internally; their exact binders are retained for graph composition. -/
@[nolint unusedArguments]
theorem node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradients_of_deps
    (_hsemigroup : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    (_hcorrector : node_corrector_u2D_constructionStmt) :
    node_e_u3A_linear_u2D_velocity_u23_massive_u2D_gradientsStmt := by
  intro d hd D Q hQ β hβ first i
  let G (s : Set.Ioi (0 : ℝ)) :=
    unforcedComplexResolventGradient Q first s.val s.property (β i)
  let R (s : Set.Ioi (0 : ℝ)) :=
    unforcedComplexResolventRealGradient Q first s.val s.property (β i) Complex.reCLM
  let g := correctorGradient Q i
  refine ⟨G, fun s => hasComplexHorizontalGradient_unforcedComplexResolvent
    Q first s.val s.property (β i), ?_⟩
  have hs : Tendsto (fun s : Set.Ioi (0 : ℝ) => s.val)
      (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 0) :=
    tendsto_comap.mono_right nhdsWithin_le_nhds
  have hr : Tendsto R (Filter.comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 g) :=
    hβ.tendsto_real_resolvent_gradient first i (fun s : Set.Ioi (0 : ℝ) => s.val) (fun s => s.property) hs
  exact tendsto_gradient_energy Q G R g (fun s => gradient_components
    (hasComplexHorizontalGradient_unforcedComplexResolvent Q first s.val s.property (β i))
    (hβ.resolvent_imaginary_gradient_eq_zero first i s.val s.property)) hr

end EinsteinFull.Blueprint
