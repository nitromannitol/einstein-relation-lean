import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_identity
import EinsteinFull.Blueprint.G3.node_e_u3A_sublinear_u2D_pair
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedDerivatives
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds
import EinsteinFull.Calculus.S1FluxIdentitySupport
import EinsteinFull.Calculus.S1FluxIdentityPath
import EinsteinFull.Calculus.S1FluxIdentityCore
import EinsteinFull.Calculus.S1FluxIdentityEndpoint
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinRelation.Correctors.P53SourceSkewHeatSmoothedDivergence
import EinsteinFull.Work.W2.CorrectorReuseSupport

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- A continuous function is locally `L²` on every Euclidean ball. -/
theorem fluxId_memLp_ball {d : ℕ} {f : Vec d → ℝ} (hf : Continuous f) (R : ℝ) :
    MemLp f 2 (volume.restrict {x : Vec d | euclideanNorm x < R}) := by
  have hn : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hT : MeasurableSet {x : Vec d | euclideanNorm x < R} :=
    measurableSet_lt hn.measurable measurable_const
  have hsub : {x : Vec d | euclideanNorm x < R} ⊆ Metric.closedBall (0 : Vec d) |R| := by
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (abs_nonneg R)]
    intro j
    rw [Real.norm_eq_abs]
    have hxj : x j ^ 2 ≤ euclideanSq x := by
      have : x j ^ 2 ≤ ∑ i, x i * x i := by
        rw [sq]
        exact Finset.single_le_sum (f := fun i => x i * x i)
          (fun i _ => mul_self_nonneg _) (Finset.mem_univ j)
      exact this
    exact (Real.abs_le_sqrt hxj).trans ((le_of_lt hx).trans (le_abs_self R))
  haveI : IsFiniteMeasure (volume.restrict {x : Vec d | euclideanNorm x < R}) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (Metric.isBounded_closedBall.subset hsub).measure_lt_top⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec d) |R|).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hT]
  exact Filter.Eventually.of_forall fun x hx => hC x (hsub hx)

/-- The reduced coefficient is almost surely smooth and symmetric. -/
theorem fluxId_reduced_regular {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    ∀ᵐ ω ∂reducedLaw Q, (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
      ∀ x, (ω.1 x).transpose = ω.1 x := by
  obtain ⟨M, -, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hsym : ∀ᵐ ω ∂reducedLaw Q, ∀ x, (ω.1 x).transpose = ω.1 x := by
    apply (Probability.measurableEmbedding_reduce d).ae_map_iff.mpr
    filter_upwards [Q.regular] with ω hω x
    change (clockDensity ω x • ω.1 x).transpose = clockDensity ω x • ω.1 x
    rw [Matrix.transpose_smul, (hω.1 x).1]
  filter_upwards [hM Q hQ, hsym] with ω hs hsy
  exact ⟨hs.1.1, hsy⟩

/-- Local `L²`, antisymmetry and the weak corrector identities of `e:flux-identity`. -/
theorem fluxId_part1 {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (φ : Fin d → FieldPair d → Vec d → ℝ) (S0 : Fin d → FieldPair d → Vec d → Mat d)
    (hgood : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (φ i ω) ∧
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S0 i ω x j k)) ∧
      (∀ x, (S0 i ω x).transpose = -(S0 i ω x)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∀ j : Fin d, fderiv ℝ (φ i ω) x (unitVector j) =
          correctorGradient Q i (translate x ω) j) ∧
        ∀ j : Fin d,
          (∑ k : Fin d, fderiv ℝ (fun y => S0 i ω y k j) x (unitVector k)) =
            ((ω.1 x).mulVec (unitVector i +
              WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
                homogenizedCoefficient Q j i)
    (S : Fin d → Fin d → Fin d → FieldPair d → Vec d → ℝ)
    (hS : ∀ i k j ω x, S i k j ω x = S0 i ω x k j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      (∀ R : ℝ, 0 < R →
        MemLp (φ i ω) 2 (volume.restrict {x : Vec d | euclideanNorm x < R}) ∧
        ∀ k j, MemLp (S i k j ω) 2
          (volume.restrict {x : Vec d | euclideanNorm x < R})) ∧
      (∀ k j x, S i k j ω x = -S i j k ω x) ∧
      (∀ θ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ → HasCompactSupport θ →
        (∀ j : Fin d,
          (∫ x, φ i ω x * fderiv ℝ θ x (unitVector j)) =
            -(∫ x, correctorGradient Q i (translate x ω) j * θ x)) ∧
        (∀ j : Fin d,
          (∑ k : Fin d, ∫ x, S i k j ω x * fderiv ℝ θ x (unitVector k)) =
            -(∫ x, ((∑ l : Fin d, ω.1 x j l *
              (unitVector i l + correctorGradient Q i (translate x ω) l)) -
                homogenizedCoefficient Q j i) * θ x))) := by
  filter_upwards [hgood] with ω hg i
  obtain ⟨hφ, hS', hanti, hident⟩ := hg i
  refine ⟨fun R _ => ⟨fluxId_memLp_ball (hφ.continuous) R, fun k j => ?_⟩, ?_, ?_⟩
  · have hfun : S i k j ω = fun x => S0 i ω x k j := funext (hS i k j ω)
    rw [hfun]
    exact fluxId_memLp_ball ((hS' k j).continuous) _
  · intro k j x
    simp only [hS]
    have := congrFun (congrFun (hanti x) j) k
    simpa [Matrix.transpose_apply] using this
  · intro θ hθ hθc
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [fluxId_ibp_real (unitVector j) hφ hθ hθc, neg_inj]
      refine integral_congr_ae ?_
      filter_upwards [hident] with x hx
      rw [hx.1 j]
    · have h2 : ∀ k, ∫ x, S i k j ω x * fderiv ℝ θ x (unitVector k) =
          -∫ x, fderiv ℝ (fun y => S0 i ω y k j) x (unitVector k) * θ x := fun k => by
        simp only [hS]
        exact fluxId_ibp_real (unitVector k) (hS' k j) hθ hθc
      rw [Finset.sum_congr rfl (fun k _ => h2 k), Finset.sum_neg_distrib,
        ← integral_finsetSum _ (fun k _ => fluxId_integrable_fderiv_mul (hS' k j) hθ hθc _),
        neg_inj]
      refine integral_congr_ae ?_
      filter_upwards [hident] with x hx
      exact (Finset.sum_mul _ _ _).symm.trans (congrArg (fun t => t * θ x) (hx.2 j))

/-- The exact smooth identity of `e:flux-identity` for almost every environment. -/
theorem fluxId_part2 {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hreg : ∀ᵐ ω ∂reducedLaw Q, (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
      ∀ x, (ω.1 x).transpose = ω.1 x)
    (φ : Fin d → FieldPair d → Vec d → ℝ) (S0 : Fin d → FieldPair d → Vec d → Mat d)
    (hgood : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      ContDiff ℝ (⊤ : ℕ∞) (φ i ω) ∧
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S0 i ω x j k)) ∧
      (∀ x, (S0 i ω x).transpose = -(S0 i ω x)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∀ j : Fin d, fderiv ℝ (φ i ω) x (unitVector j) =
          correctorGradient Q i (translate x ω) j) ∧
        ∀ j : Fin d,
          (∑ k : Fin d, fderiv ℝ (fun y => S0 i ω y k j) x (unitVector k)) =
            ((ω.1 x).mulVec (unitVector i +
              WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
                homogenizedCoefficient Q j i)
    (S : Fin d → Fin d → Fin d → FieldPair d → Vec d → ℝ)
    (hS : ∀ i k j ω x, S i k j ω x = S0 i ω x k j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      ∀ (cφ : ℝ) (cS : Fin d → Fin d → ℝ),
        (∀ k j, cS k j = -cS j k) →
      ∀ (F : Vec d → Fin d → ℂ),
        (∀ j, ContDiff ℝ (⊤ : ℕ∞) (fun x => F x j)) →
      ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        let aF := fun (x : Vec d) (j : Fin d) =>
          ∑ l : Fin d, (ω.1 x j l : ℂ) * F x l
        let divAF := fun x : Vec d =>
          ∑ j : Fin d, fderiv ℝ (fun y => aF y j) x (unitVector j)
        (∫ x, (∑ j : Fin d,
          ((ω.1 x i j - homogenizedCoefficient Q i j : ℝ) : ℂ) * F x j) * ψ x) =
          (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
          (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) *
            (∑ k : Fin d, aF x k * fderiv ℝ ψ x (unitVector k))) -
          (∫ x, ∑ k : Fin d, ∑ j : Fin d,
            ((S i k j ω x - cS k j : ℝ) : ℂ) * F x j *
              fderiv ℝ ψ x (unitVector k)) -
          (∫ x, (∑ k : Fin d, ∑ j : Fin d,
            ((S i k j ω x - cS k j : ℝ) : ℂ) *
              fderiv ℝ (fun y => F y j) x (unitVector k)) * ψ x) := by
  filter_upwards [hreg, hgood] with ω hr hg i cφ cS _ F hF ψ hψ hψc
  obtain ⟨hφ, hS', _, hident⟩ := hg i
  have key := fluxId_concrete i (fun x => ω.1 x) hr.1 hr.2 (homogenizedCoefficient Q)
    (homogenizedCoefficient_transpose (Q := Q)) (φ i ω) hφ (fun k j x => S0 i ω x k j)
    (fun k j => hS' k j) (fun x j => correctorGradient Q i (translate x ω) j)
    (hident.mono fun x hx j => hx.1 j) (hident.mono fun x hx j => hx.2 j) cφ cS F hF ψ hψ hψc
  simp only [hS]
  exact key

/-- The endpoint part of `e:flux-identity`, from the proved centered equations. -/
theorem fluxId_endpoint {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (S0 : Fin d → FieldPair d → Vec d → Mat d)
    (hgood : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S0 i ω x j k)) ∧
      (∀ x, (S0 i ω x).transpose = -(S0 i ω x)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        ∀ j : Fin d,
          (∑ k : Fin d, fderiv ℝ (fun y => S0 i ω y k j) x (unitVector k)) =
            ((ω.1 x).mulVec (unitVector i +
              WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
                homogenizedCoefficient Q j i)
    (φ : Fin d → FieldPair d → Vec d → ℝ)
    (hφs : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞) (φ i ω) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        fderiv ℝ (φ i ω) x (unitVector j) = correctorGradient Q i (translate x ω) j)
    (hreg : ∀ᵐ ω ∂reducedLaw Q, (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
      ∀ x, (ω.1 x).transpose = ω.1 x)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (U t) (G t) (J t)) ∧
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        DifferentiableAt ℝ (fun r : ℝ => U r.toNNReal) (t : ℝ) ∧
        ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
        ∀ (cφ : ℝ) (cS : Fin d → Fin d → ℝ), (∀ k j, cS k j = -cS j k) →
        ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          let u := fun x : Vec d => U t (translate x ω)
          let g := fun (x : Vec d) (j : Fin d) => G t j (translate x ω)
          let ut := fun x : Vec d =>
            deriv (fun r : ℝ => U r.toNNReal) (t : ℝ) (translate x ω)
          let c := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
          let F := fun (x : Vec d) (j : Fin d) => g x j -
            match ν with
            | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
            | _ => 0
          let divAF := fun x : Vec d => 2 * ut x +
            match ν with
            | .inr true => 0
            | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
                (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
          (∫ x, J t i (translate x ω) * ψ x) =
            (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
            (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) *
              (∑ k : Fin d, (∑ j : Fin d, (ω.1 x k j : ℂ) * F x j) *
                fderiv ℝ ψ x (unitVector k))) -
            (∫ x, ∑ k : Fin d, ∑ j : Fin d,
              ((S0 i ω x k j - cS k j : ℝ) : ℂ) * F x j *
                fderiv ℝ ψ x (unitVector k)) +
            match ν with
            | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
                ((S0 i ω x k ⟨0, by omega⟩ - cS k ⟨0, by omega⟩ : ℝ) : ℂ) *
                  g x k) * ψ x)
            | _ => 0 := by
  intro U
  haveI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  choose! G J V h using node_e_u3A_centered_u2D_equations_of_deps d hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hT ν
  refine ⟨G, J, fun t ht => (h t ht).1, fun t ht => ?_⟩
  obtain ⟨hflux, hder, -, he⟩ := h t ht
  refine ⟨hder.differentiableAt, ?_⟩
  have hdU : deriv (fun r : ℝ => U r.toNNReal) (t : ℝ) = V t := hder.deriv
  have hmean : ∀ k, ∫ ω, G t k ω ∂reducedLaw Q = 0 := fun k => (hflux.1 k).integral_eq_zero
  have hsymm0 : ∀ᵐ ω ∂reducedLaw Q, (ω.1 0).transpose = ω.1 0 :=
    hreg.mono fun ω hω => hω.2 0
  have hAs : ∀ j l, homogenizedCoefficient Q j l = homogenizedCoefficient Q l j := fun j l => by
    have := congrFun (congrFun (homogenizedCoefficient_transpose (Q := Q)) l) j
    simpa [Matrix.transpose_apply] using this
  have hJae : ∀ᵐ ω ∂reducedLaw Q, ∀ j, J t j ω = ∑ k,
      (((ω.1 0 j k : ℝ) : ℂ) - (homogenizedCoefficient Q j k : ℂ)) *
        (G t k ω - match (generalizing := false) ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U t ω
          | _ => 0) := by
    filter_upwards [ae_all_iff.mpr fun j => hflux.2 j,
      ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ha j k] with ω h1 h2 j
    refine (h1 j).trans ?_
    exact Finset.sum_congr rfl fun k _ => by
      rw [h2 j k]
      cases ν with
      | inl j => rfl
      | inr b => cases b <;> rfl
  have hJtr := EinsteinRelation.Correctors.ae_ae_translate_of_ae (reducedLaw Q)
    (reducedLaw_stationary Q) hJae
  have hmeanJ : fluxIdEps ζ ν = 0 → ∫ ω, J t ⟨0, by omega⟩ ω ∂reducedLaw Q =
      ∫ ω, ∑ k, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q := by
    intro hε
    refine fluxId_meanJ Q ⟨0, by omega⟩ a ha hsymm0 (homogenizedCoefficient Q) (G t) hmean
      (J t ⟨0, by omega⟩) ((hflux.2 ⟨0, by omega⟩).mono fun ω hω => ?_)
    refine hω.trans ?_
    exact Finset.sum_congr rfl fun k _ => by
      cases ν with
      | inl j => ring
      | inr b =>
        cases b
        · ring
        · have hz : ζ = 0 := by
            change 2 * ζ = 0 at hε
            exact (mul_eq_zero.mp hε).resolve_left (by norm_num)
          rw [hz]
          ring
  filter_upwards [hreg, hgood, hφs, hJtr, fluxId_ae_gradient Q (U t) (G t) hflux.1,
    fluxId_ae_locInt Q (U t), fluxId_ae_locInt Q (V t),
    ae_all_iff.mpr fun m => fluxId_ae_locInt Q (G t m),
    ae_all_iff.mpr fun j => fluxId_ae_locInt Q (J t j), he]
    with ω hr hgd hφω hJω hGc hUl hVl hGl hJl hheω
  intro i cφ cS hcS ψ hψ hψc u g ut c F divAF
  obtain ⟨hS', hanti, hident⟩ := hgd i
  obtain ⟨hφ, hφG⟩ := hφω i
  have hSanti' : ∀ k j x, S0 i ω x k j = -S0 i ω x j k := fun k j x => by
    have := congrFun (congrFun (hanti x) j) k
    simpa [Matrix.transpose_apply] using this
  have hFmatch : ∀ j x, F x j = g x j -
      fluxIdEps ζ ν * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x := fun j x =>
    congrArg (fun t' => g x j - t') (fluxId_Fmatch ζ ν _ _)
  have hJrel : ∀ k, ∀ᵐ x ∂(volume : Measure (Vec d)), J t k (translate x ω) =
      ∑ j, ((ω.1 x k j - homogenizedCoefficient Q k j : ℝ) : ℂ) * F x j := fun k =>
    hJω.mono fun x hx => by
      beta_reduce
      rw [hx k]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [F, g, u, translate_matrix, add_zero, Complex.ofReal_sub]
  have he' : ∀ φ' : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ' → HasCompactSupport φ' →
      (∫ x, V t (translate x ω) * (φ' x : ℂ)) +
        (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) * g x k *
          (fderiv ℝ φ' x (unitVector j) : ℂ)) -
        ((endpointDriftSign ν : ℂ) * ζ) * (∫ x, (∑ j,
          (homogenizedCoefficient Q j (⟨0, by omega⟩ : Fin d) : ℂ) * g x j) * (φ' x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, J t j (translate x ω) * (fderiv ℝ φ' x (unitVector j) : ℂ)) +
        (fluxIdKf ν * ζ) * (∫ x, (J t (⟨0, by omega⟩ : Fin d) (translate x ω) -
          ∫ ω', J t (⟨0, by omega⟩ : Fin d) ω' ∂reducedLaw Q) * (φ' x : ℂ)) := by
    intro φ' hφ' hφc'
    exact (hheω φ' hφ' hφc').trans (congrArg
      (fun t' => -(1 / 2 : ℂ) * (∫ x, ∑ j, J t j (translate x ω) *
        (fderiv ℝ φ' x (unitVector j) : ℂ)) + t')
      (fluxId_Kmatch ζ ν (∫ x, (J t (⟨0, by omega⟩ : Fin d) (translate x ω) -
          ∫ ω', J t (⟨0, by omega⟩ : Fin d) ω' ∂reducedLaw Q) * (φ' x : ℂ))))
  have hDm : ∀ᵐ x ∂(volume : Measure (Vec d)),
      2 * V t (translate x ω) -
        (2 * ((endpointDriftSign ν : ℂ) * ζ) + fluxIdEps ζ ν) *
          ∑ j, (homogenizedCoefficient Q j (⟨0, by omega⟩ : Fin d) : ℂ) * g x j -
        2 * (fluxIdKf ν * ζ) * (J t (⟨0, by omega⟩ : Fin d) (translate x ω) -
          ∫ ω', J t (⟨0, by omega⟩ : Fin d) ω' ∂reducedLaw Q) = divAF x := by
    filter_upwards [hJrel ⟨0, by omega⟩] with x hJx
    have hutx : ut x = V t (translate x ω) := by
      simp only [ut]
      rw [hdU]
    refine Eq.trans ?_ (congrArg (fun t' => 2 * ut x + t')
      (fluxId_Dmatch ν (2 * c - 2 * ζ * (∑ k : Fin d,
        (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)))).symm
    rw [hutx]
    rcases fluxId_cases ζ ν with ⟨hε, hkf, hds⟩ | ⟨hε, hkf, hds⟩
    · rw [hε, hkf, hds]
      have f1 : ∑ j, (homogenizedCoefficient Q j (⟨0, by omega⟩ : Fin d) : ℂ) * g x j =
          ∑ j, (homogenizedCoefficient Q (⟨0, by omega⟩ : Fin d) j : ℂ) * g x j :=
        Finset.sum_congr rfl fun j _ => by rw [hAs j]
      have f2 : ∑ k : Fin d, (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k =
          ∑ j : Fin d, (ω.1 x ⟨0, by omega⟩ j : ℂ) * g x j :=
        Finset.sum_congr rfl fun k _ => by
          have := congrFun (congrFun (hr.2 x) k) ⟨0, by omega⟩
          simp only [Matrix.transpose_apply] at this
          rw [this]
      have hFfwd : ∀ j, F x j = g x j := fun j => by rw [hFmatch j x, hε]; ring
      have f3 : J t (⟨0, by omega⟩ : Fin d) (translate x ω) =
          (∑ j : Fin d, (ω.1 x ⟨0, by omega⟩ j : ℂ) * g x j) -
            ∑ j : Fin d, (homogenizedCoefficient Q (⟨0, by omega⟩ : Fin d) j : ℂ) * g x j := by
        have e : ∑ j, ((ω.1 x ⟨0, by omega⟩ j - homogenizedCoefficient Q ⟨0, by omega⟩ j : ℝ) : ℂ) *
            F x j = ∑ j, ((ω.1 x ⟨0, by omega⟩ j : ℂ) * g x j -
              (homogenizedCoefficient Q ⟨0, by omega⟩ j : ℂ) * g x j) :=
          Finset.sum_congr rfl fun j _ => by rw [hFfwd j]; push_cast; ring
        rw [hJx, e, Finset.sum_sub_distrib]
      have f4 : c = ζ * ∫ ω', J t (⟨0, by omega⟩ : Fin d) ω' ∂reducedLaw Q := by
        simp only [c]
        rw [hmeanJ hε]
      linear_combination (-2 * ζ) * f1 + (-2 * ζ) * f3 + (2 * ζ) * f2 + (-2 : ℂ) * f4
    · rw [hε, hkf, hds]
      ring
  have hcore := fluxId_core i ⟨0, by omega⟩ (fun x => ω.1 x) hr.1 hr.2
    (homogenizedCoefficient Q) (homogenizedCoefficient_transpose (Q := Q)) (φ i ω) hφ
    (fun k j x => S0 i ω x k j) hS' hSanti' (fun x j => correctorGradient Q i (translate x ω) j)
    (hφG.mono fun x hx j => hx j) (hident.mono fun x hx j => hx j) cφ cS hcS
    (u := fun x => U t (translate x ω)) (V := fun x => V t (translate x ω))
    (g := fun m x => g x m) (Fv := fun j x => F x j) (J := fun j x => J t j (translate x ω))
    (fluxIdEps ζ ν) ((endpointDriftSign ν : ℂ) * ζ) (fluxIdKf ν * ζ)
    (∫ ω', J t (⟨0, by omega⟩ : Fin d) ω' ∂reducedLaw Q) hUl hGl hVl hJl hFmatch hGc hJrel he'
    divAF hDm (ψ := ψ) ⟨hψ, hψc⟩ _ (fluxId_Lmatch ζ ν _)
  exact hcore

/-- Spatial potentials and the endpoint weak-flux identity, from the sublinear pair. -/
theorem node_e_u3A_flux_u2D_identity_of_deps (hsp : node_e_u3A_sublinear_u2D_pairStmt) :
    node_e_u3A_flux_u2D_identityStmt := by
  intro d hd D Q hQ
  obtain ⟨κ₀, C₀, c₀, -, -, -, -, hspQ⟩ := hsp d hd D
  obtain ⟨φ, S0, hgood, -⟩ := hspQ Q hQ
  have hreg := fluxId_reduced_regular D Q hQ
  have p1 := fluxId_part1 Q φ S0 hgood (fun i k j ω x => S0 i ω x k j)
    (fun _ _ _ _ _ => rfl)
  have p2 := fluxId_part2 Q hreg φ S0 hgood (fun i k j ω x => S0 i ω x k j)
    (fun _ _ _ _ _ => rfl)
  refine ⟨φ, fun i k j ω x => S0 i ω x k j, ?_, ?_⟩
  · filter_upwards [p1, p2] with ω h1 h2 i
    exact ⟨(h1 i).1, (h1 i).2.1, (h1 i).2.2, h2 i⟩
  · intro hQ' β a μ hβ ha hμ ζ P Pdag hP hT ν
    exact fluxId_endpoint hd Q hQ' S0
      (hgood.mono fun ω h i => ⟨(h i).2.1, (h i).2.2.1, (h i).2.2.2.mono fun x hx => hx.2⟩) φ
      (hgood.mono fun ω h i => ⟨(h i).1, (h i).2.2.2.mono fun x hx j => hx.1 j⟩)
      hreg β a μ hβ ha hμ ζ P Pdag hP hT ν

end EinsteinFull.Blueprint
