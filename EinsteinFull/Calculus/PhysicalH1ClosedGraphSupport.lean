import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinRelation.Calculus.WeightedH1ClosedGraphSupport

/-!
# Closed complex physical H1 graphs

The real and imaginary parts are transported to the blueprint's proved real
weighted weak-gradient graph. A finite sum of coordinate inclusions gives
the Euclidean gradient carrier used there; its representatives are identified
almost everywhere before applying closedness. No change of the public
coordinate carrier or norm is made.

Reuses `Calculus/WeightedH1ClosedGraphSupport.lean` and
`Calculus/WeightedH1QuotientSupport.lean` from EinsteinRelation at revision
`7748a8e9000034825873768d309be8915ae53b07`.
-/

open MeasureTheory
open scoped ENNReal Topology

noncomputable section

namespace EinsteinFull

open EinsteinRelation
open EinsteinRelation.SpatialDirichlet

private def gradientPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) : Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  ∑ j : Fin d, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).comp L).compLp (G j)

private theorem gradientPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (gradientPart m L) := by
  apply continuous_finset_sum
  intro j _
  let T := (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).comp L
  exact (T.compLpL 2 m).continuous.comp (continuous_apply j)

private theorem gradientPart_coe {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) :
    ∀ᵐ x ∂m, ∀ j : Fin d, (gradientPart m L G x) j = L (G j x) := by
  classical
  let f (j : Fin d) := ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).comp L).compLp (G j)
  have hsum (s : Finset (Fin d)) :
      ⇑(∑ j ∈ s, f j) =ᵐ[m] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using! (Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 m)
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hx hi
      rw [hx]
      change f j x + (∑ k ∈ s, f k) x = _
      rw [hi]
  have hf : ∀ᵐ x ∂m, ∀ j : Fin d,
      f j x = L (G j x) • EuclideanSpace.single j (1 : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    exact (((ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).comp L).coeFn_compLp (G j))
  filter_upwards [hsum Finset.univ, hf] with x hx hfx
  intro j
  change (WithLp.ofLp ((∑ k : Fin d, f k) x)) j = _
  rw [hx]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j) (∑ k : Fin d, f k x) = _
  rw [map_sum]
  simp only [PiLp.projₗ_apply, hfx, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem weightedGraph_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (v : Lp ℝ 2 (densityWeightedMeasure ρ))
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    (v, g) ∈ densityWeightedWeakGraphSet ρ hρ hρpos ↔
      ∀ j : Fin d, HasWeakPartialDerivative Set.univ j v (fun x => g x j) := by
  constructor
  · intro hp
    exact (densityWeightedGraphOfPair ρ hρ hρpos (v, g) hp).distributionalGradient
  · intro h
    let u : WeightedSobolevGraph (densityWeightedMeasure ρ) := {
      value := v
      weakGradient := g
      value_memLp := Lp.memLp v
      gradient_memLp := Lp.memLp g
      distributionalGradient := h
    }
    have heq : densityWeightedGraphPair ρ u = (v, g) :=
      Prod.ext (Lp.ext (Lp.memLp v).coeFn_toLp) (Lp.ext (Lp.memLp g).coeFn_toLp)
    rw [← heq]
    exact densityWeightedGraphPair_mem_weakGraphSet ρ hρ hρpos u

private def graphPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 m × (Fin d → Lp ℂ 2 m)) :
    Lp ℝ 2 m × Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  (L.compLp p.1, gradientPart m L p.2)

private theorem graphPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (graphPart m L) :=
  ((L.compLpL 2 m).continuous.comp continuous_fst).prodMk
    ((gradientPart_continuous m L).comp continuous_snd)

private theorem graphPart_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 (densityWeightedMeasure ρ) ×
      (Fin d → Lp ℂ 2 (densityWeightedMeasure ρ))) :
    graphPart (densityWeightedMeasure ρ) L p ∈ densityWeightedWeakGraphSet ρ hρ hρpos ↔
      ∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => L (p.1 x)) (fun x => L (p.2 j x)) := by
  rw [weightedGraph_mem_iff]
  apply forall_congr'
  intro j
  have hv : (volume : Measure (Vec d)) ≪ densityWeightedMeasure ρ := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp hρ.measurable).aemeasurable
    · exact Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hρpos x)).ne'
  exact hasWeakPartialDerivative_congr_of_absolutelyContinuous (densityWeightedMeasure ρ) hv j
    (L.coeFn_compLp p.1) ((gradientPart_coe (densityWeightedMeasure ρ) L p.2).mono
      fun x hx => hx j)

/-- The full complex weak-gradient graph is closed for every positive continuous density. -/
theorem isClosed_complex_weightedH1Graph {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    IsClosed {p : Lp ℂ 2 (densityWeightedMeasure ρ) ×
      (Fin d → Lp ℂ 2 (densityWeightedMeasure ρ)) |
      (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => (p.1 x).re) (fun x => (p.2 j x).re)) ∧
      (∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => (p.1 x).im) (fun x => (p.2 j x).im))} := by
  have hr := (densityWeightedWeakGraphSet_isClosed ρ hρ hρpos).preimage
    (graphPart_continuous (densityWeightedMeasure ρ) Complex.reCLM)
  have hi := (densityWeightedWeakGraphSet_isClosed ρ hρ hρpos).preimage
    (graphPart_continuous (densityWeightedMeasure ρ) Complex.imCLM)
  convert hr.inter hi using 1
  ext p
  change (_ ∧ _) ↔ (_ ∈ _ ∧ _ ∈ _)
  simp only [Set.mem_preimage]
  rw [graphPart_mem_iff, graphPart_mem_iff]
  rfl

/-- Both public physical H1 graphs are closed in the full L2 product. -/
theorem isClosed_physicalH1Graph {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam) :
    IsClosed {p : Lp ℂ 2 m × (Fin d → Lp ℂ 2 m) | IsPhysicalH1Graph m hm p.1 p.2} := by
  rcases hm with rfl | ⟨i, lam, rfl⟩
  · have h := isClosed_complex_weightedH1Graph (fun _ : Vec d => 1)
      continuous_const (fun _ => zero_lt_one)
    have hmeasure : densityWeightedMeasure (fun _ : Vec d => 1) = (volume : Measure (Vec d)) := by
      simp [densityWeightedMeasure]
    rw [hmeasure] at h
    exact h
  · exact isClosed_complex_weightedH1Graph (fun x : Vec d => Real.exp (2 * lam * x i))
      (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i)))
      (fun _ => Real.exp_pos _)

/-- Weak gradients of the same physical L2 class agree as L2 classes. -/
theorem physicalH1Graph_gradient_unique {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (u : Lp ℂ 2 m) (G H : Fin d → Lp ℂ 2 m)
    (hG : IsPhysicalH1Graph m hm u G) (hH : IsPhysicalH1Graph m hm u H) : G = H := by
  have hreal := weakGradients_ae_eq_of_value_ae_eq
    (Filter.Eventually.of_forall fun _ => rfl) hG.1 hH.1
  have himag := weakGradients_ae_eq_of_value_ae_eq
    (Filter.Eventually.of_forall fun _ => rfl) hG.2 hH.2
  have hmv : m ≪ (volume : Measure (Vec d)) := by
    rcases hm with rfl | ⟨i, lam, rfl⟩
    · exact Measure.AbsolutelyContinuous.rfl
    · exact physicalForceMeasure_absolutelyContinuous i lam
  funext j
  apply Lp.ext
  filter_upwards [hmv.ae_eq hreal, hmv.ae_eq himag] with x hx hy
  exact Complex.ext (congrFun hx j) (congrFun hy j)

/-- Strong limits of actual physical value-gradient pairs preserve the weak derivative. -/
theorem physicalH1Graph_of_tendsto {d : ℕ} (m : Measure (Vec d))
    (hm : m = volume ∨ ∃ (i : Fin d) (lam : ℝ), m = physicalForceMeasure i lam)
    (p : ℕ → Lp ℂ 2 m × (Fin d → Lp ℂ 2 m))
    (q : Lp ℂ 2 m × (Fin d → Lp ℂ 2 m))
    (hp : ∀ n, IsPhysicalH1Graph m hm (p n).1 (p n).2)
    (hlim : Filter.Tendsto p Filter.atTop (𝓝 q)) :
    IsPhysicalH1Graph m hm q.1 q.2 :=
  (isClosed_physicalH1Graph m hm).mem_of_tendsto hlim (Filter.Eventually.of_forall hp)

end EinsteinFull
