import EinsteinRelation.Calculus.WeightedH1HilbertSupport
import EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport
import EinsteinRelation.Environment.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- The exponential tilt density in the force direction. -/
def sourceForceWeight {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) : ℝ :=
  Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩)

/-- The reduced source density for the full weighted H¹ graph. -/
def sourceReducedDensity {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) : ℝ :=
  sourceForceWeight hd lam x

/-- The physical source density for the form and value pairing. -/
def sourcePhysicalDensity {d : ℕ} (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (x : Vec d) : ℝ :=
  sourceForceWeight hd lam x * clockDensity ω x

theorem continuousSourceReducedDensity {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    Continuous (sourceReducedDensity hd lam) := by
  unfold sourceReducedDensity sourceForceWeight
  fun_prop

theorem positiveSourceReducedDensity {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) :
    0 < sourceReducedDensity hd lam x := by
  unfold sourceReducedDensity sourceForceWeight
  exact Real.exp_pos _

theorem continuousSourcePhysicalDensity {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam : ℝ) : Continuous (sourcePhysicalDensity ω hd lam) := by
  unfold sourcePhysicalDensity sourceForceWeight clockDensity
  fun_prop

theorem positiveSourcePhysicalDensity {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) : 0 < sourcePhysicalDensity ω hd lam x := by
  unfold sourcePhysicalDensity
  exact mul_pos (Real.exp_pos _) (clockDensity_pos ω x)

/-- Pointwise domination of weighted densities gives the corresponding measure domination. -/
theorem densityWeightedMeasure_le_const_smul {d : ℕ} (ρ σ : Vec d → ℝ)
    (hσ : Measurable σ)
    (K : ℝ) (hK : 0 ≤ K) (hρσ : ∀ x, ρ x ≤ K * σ x) :
    densityWeightedMeasure ρ ≤ ENNReal.ofReal K • densityWeightedMeasure σ := by
  unfold densityWeightedMeasure
  have hdens : (fun x => ENNReal.ofReal (ρ x)) ≤ᵐ[volume]
      (fun x => ENNReal.ofReal K * ENNReal.ofReal (σ x)) := by
    filter_upwards [] with x
    calc
      ENNReal.ofReal (ρ x) ≤ ENNReal.ofReal (K * σ x) :=
        ENNReal.ofReal_le_ofReal (hρσ x)
      _ = ENNReal.ofReal K * ENNReal.ofReal (σ x) := ENNReal.ofReal_mul hK
  have h := withDensity_mono hdens
  calc
    volume.withDensity (fun x => ENNReal.ofReal (ρ x)) ≤
        volume.withDensity (fun x => ENNReal.ofReal K * ENNReal.ofReal (σ x)) := h
    _ = ENNReal.ofReal K • volume.withDensity (fun x => ENNReal.ofReal (σ x)) := by
      rw [show (fun x => ENNReal.ofReal K * ENNReal.ofReal (σ x)) =
        ENNReal.ofReal K • (fun x => ENNReal.ofReal (σ x)) from by
          funext x
          simp [smul_eq_mul]]
      change volume.withDensity (ENNReal.ofReal K • (ENNReal.ofReal ∘ σ)) =
        ENNReal.ofReal K • volume.withDensity (ENNReal.ofReal ∘ σ)
      exact withDensity_smul (μ := volume) (r := ENNReal.ofReal K)
        (ENNReal.measurable_ofReal.comp hσ)

/-- The square of an `L²` norm is the integral of the pointwise norm square. -/
theorem l2_norm_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : Measure α} (u : Lp E 2 m) :
    ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 ∂m := by
  calc
    ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ x, inner ℝ (u x) (u x) ∂m := L2.inner_def u u
    _ = ∫ x, ‖u x‖ ^ 2 ∂m := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [real_inner_self_eq_norm_sq]

/-- A pointwise nonnegative integral respects measure domination, with the scalar written
as a real constant. -/
theorem integral_le_const_mul_of_measure_le {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) (K : ℝ) (hK : 0 ≤ K)
    (hμ : μ ≤ ENNReal.ofReal K • ν) (f : α → ℝ)
    (hf : 0 ≤ᵐ[ν] f) (hfi : Integrable f ν) :
    ∫ x, f x ∂μ ≤ K * ∫ x, f x ∂ν := by
  calc
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂(ENNReal.ofReal K • ν) :=
      integral_mono_measure hμ (Measure.ae_smul_measure hf (ENNReal.ofReal K))
        (hfi.smul_measure ENNReal.ofReal_ne_top)
    _ = K * ∫ x, f x ∂ν := by
      rw [integral_smul_measure]
      simp [smul_eq_mul, ENNReal.toReal_ofReal hK]

/-- The physical density is bounded above by the reduced source density, with the
constant supplied by the bounded potential. -/
theorem sourcePhysicalDensity_le_reduced_mul {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω) (x : Vec d) :
    sourcePhysicalDensity ω hd lam x ≤ Real.exp (2 * L) * sourceReducedDensity hd lam x := by
  have hclock := (clockDensity_bounds ω x L (hω.2.1 x)).2
  unfold sourcePhysicalDensity sourceReducedDensity sourceForceWeight
  calc
    _ ≤ Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩) *
        Real.exp (2 * L) :=
      mul_le_mul_of_nonneg_left hclock (Real.exp_pos _).le
    _ = _ := by ring

/-- The reduced source density is bounded above by the physical density, with the
constant supplied by the bounded potential. -/
theorem sourceReducedDensity_le_physical_mul {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω) (x : Vec d) :
    sourceReducedDensity hd lam x ≤ Real.exp (2 * L) * sourcePhysicalDensity ω hd lam x := by
  have hclock := (clockDensity_bounds ω x L (hω.2.1 x)).1
  have hfactor : 1 ≤ Real.exp (2 * L) * clockDensity ω x := by
    have hexp : 1 = Real.exp (2 * L) * Real.exp (-2 * L) := by
      rw [← Real.exp_add]
      norm_num
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hclock (Real.exp_pos _).le
  unfold sourceReducedDensity sourcePhysicalDensity sourceForceWeight
  calc
    Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩) =
        Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩) * 1 := by ring
    _ ≤ Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩) *
        (Real.exp (2 * L) * clockDensity ω x) :=
      mul_le_mul_of_nonneg_left hfactor (Real.exp_pos _).le
    _ = Real.exp (2 * L) *
        (Real.exp (2 * lam * x ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩) *
          clockDensity ω x) := by ring

/-- The actual physical weighted measure is controlled by the reduced graph measure. -/
theorem sourcePhysicalMeasure_le_reduced {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω) :
    densityWeightedMeasure (sourcePhysicalDensity ω hd lam) ≤
      ENNReal.ofReal (Real.exp (2 * L)) •
        densityWeightedMeasure (sourceReducedDensity hd lam) := by
  apply densityWeightedMeasure_le_const_smul _ _
    (continuousSourceReducedDensity hd lam).measurable (Real.exp (2 * L))
    (le_of_lt (Real.exp_pos _))
  exact sourcePhysicalDensity_le_reduced_mul ω hd lam L hω

/-- The reduced graph measure is controlled by the actual physical weighted measure. -/
theorem sourceReducedMeasure_le_physical {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω) :
    densityWeightedMeasure (sourceReducedDensity hd lam) ≤
      ENNReal.ofReal (Real.exp (2 * L)) •
        densityWeightedMeasure (sourcePhysicalDensity ω hd lam) := by
  apply densityWeightedMeasure_le_const_smul _ _
    (continuousSourcePhysicalDensity ω hd lam).measurable (Real.exp (2 * L))
    (le_of_lt (Real.exp_pos _))
  exact sourceReducedDensity_le_physical_mul ω hd lam L hω

/-- The weighted value-gradient representative in the full source graph. -/
def densityWeightedH1SpacePair {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    Lp ℝ 2 (densityWeightedMeasure ρ) ×
      Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toFun u.1

/-- Every point of the closed graph subspace is an actual weighted weak-gradient pair. -/
theorem densityWeightedH1SpacePair_mem {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedH1SpacePair u ∈ densityWeightedWeakGraphSet ρ hρ hρpos := by
  change densityWeightedH1SpacePair u ∈ densityWeightedWeakGraphSubmodule ρ hρ hρpos
  exact u.2

/-- The source weak-gradient representative reconstructed from a full graph element. -/
def densityWeightedH1SpaceRepresentative {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    WeightedSobolevGraph (densityWeightedMeasure ρ) :=
  densityWeightedGraphOfPair ρ hρ hρpos (densityWeightedH1SpacePair u)
    (densityWeightedH1SpacePair_mem u)

/-- The graph representative has exactly the value and gradient encoded by the closed
full-H¹ carrier. -/
theorem densityWeightedH1SpaceRepresentative_pair {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    densityWeightedGraphPair ρ (densityWeightedH1SpaceRepresentative ρ hρ hρpos u) =
      densityWeightedH1SpacePair u := by
  simpa [densityWeightedH1SpaceRepresentative] using
    densityWeightedGraphPair_graphOfPair ρ hρ hρpos (densityWeightedH1SpacePair u)
      (densityWeightedH1SpacePair_mem u)

/-- The norm of the full reduced-H¹ carrier is the sum of the value and gradient integrals
of its actual weak-gradient representative. -/
theorem densityWeightedH1Space_norm_sq_integral {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    ‖u‖ ^ 2 =
      (∫ x, (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value x ^ 2 ∂
        densityWeightedMeasure ρ) +
      ∫ x, ‖(densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient x‖ ^ 2 ∂
        densityWeightedMeasure ρ := by
  rw [densityWeightedH1Space_norm_sq]
  have hp := densityWeightedH1SpaceRepresentative_pair u
  have hv : densityWeightedH1SpaceValue u =
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value_memLp.toLp
        (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value := by
    exact (congrArg Prod.fst hp).symm
  have hg : densityWeightedH1SpaceGradient u =
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).gradient_memLp.toLp
        (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient := by
    exact (congrArg Prod.snd hp).symm
  have hvint : ‖densityWeightedH1SpaceValue u‖ ^ 2 =
      ∫ x, (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value x ^ 2 ∂
        densityWeightedMeasure ρ := by
    rw [hv, l2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value_memLp.coeFn_toLp]
      with x hx
    simp only [Real.norm_eq_abs]
    rw [hx]
    exact sq_abs _
  have hgint : ‖densityWeightedH1SpaceGradient u‖ ^ 2 =
      ∫ x, ‖(densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient x‖ ^ 2 ∂
        densityWeightedMeasure ρ := by
    rw [hg, l2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).gradient_memLp.coeFn_toLp]
      with x hx
    rw [hx]
  rw [hvint, hgint]

/-- A source reduced-H¹ element reconstructed as an actual graph element for the physical
reference measure. The graph domain remains the reduced-density domain. -/
def sourcePhysicalGraph {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    WeightedSobolevGraph (densityWeightedMeasure σ) := by
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  have hKtop : ENNReal.ofReal K ≠ ∞ := ENNReal.ofReal_ne_top
  exact ⟨g.value, g.weakGradient,
    g.value_memLp.of_measure_le_smul hKtop hMeasure,
    g.gradient_memLp.of_measure_le_smul hKtop hMeasure,
    g.distributionalGradient⟩

/-- The resolvent's physical weighted value in the source reduced-H¹ domain. -/
def sourcePhysicalValue {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    Lp ℝ 2 (densityWeightedMeasure σ) :=
  let g := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  g.value_memLp.toLp g.value

/-- The literal physical weighted Dirichlet form on every test in the reduced source graph. -/
def sourcePhysicalDirichletForm {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (A : Vec d → Mat d) (u v : densityWeightedH1Submodule ρ hρ hρpos) : ℝ :=
  weightedSpatialForm A
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u)
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v)

private theorem euclideanSq_ofLp_eq_norm_sq {d : ℕ}
    (u : EuclideanSpace ℝ (Fin d)) :
    euclideanSq (WithLp.ofLp u) = ‖u‖ ^ 2 := by
  change euclideanSq u.ofLp = ‖u‖ ^ 2
  rw [EuclideanSpace.norm_sq_eq]
  simp [euclideanSq, dot, Real.norm_eq_abs, pow_two]

/-- The physical weighted value pairing is the literal integral of the representative square. -/
theorem sourcePhysicalValue_inner_self_eq_integral {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x} {σ : Vec d → ℝ} {K : ℝ}
    {hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ}
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    inner ℝ (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u) =
      ∫ x, (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x ^ 2 ∂
        densityWeightedMeasure σ := by
  rw [real_inner_self_eq_norm_sq]
  change ‖(sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.toLp
      (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value‖ ^ 2 = _
  rw [l2_norm_sq_eq_integral_norm_sq]
  apply integral_congr_ae
  filter_upwards [
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.coeFn_toLp]
    with x hx
  simp only [Real.norm_eq_abs]
  rw [hx]
  exact sq_abs _

/-- A positive-rate resolvent equation on the full source reduced-H¹ graph, with physical
forcing, physical value pairing, and physical Dirichlet measure. -/
def HasSourcePhysicalVariationalResolvent {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ)
    (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (A : Vec d → Mat d) (α : ℝ) (f : Lp ℝ 2 (densityWeightedMeasure σ))
    (u : densityWeightedH1Submodule ρ hρ hρpos) : Prop :=
  0 < α ∧ ∀ v : densityWeightedH1Submodule ρ hρ hρpos,
    α * inner ℝ (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
        (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v) +
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure A u v =
        inner ℝ f (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v)

/-- The source-derived coercivity constant is strictly positive at every positive rate. -/
theorem sourcePhysicalResolvent_coercivity_constant_pos (L α : ℝ)
    (hL : 1 ≤ L) (hα : 0 < α) :
    0 < Real.exp (-2 * L) * min α ((1 / 2 : ℝ) * L⁻¹) := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  exact mul_pos (Real.exp_pos _)
    (lt_min hα (mul_pos (by norm_num) (inv_pos.mpr hLpos)))

/-- The physical resolvent bilinear form is coercive on the complete full reduced-H¹ graph.
Its constant comes from the bounded clock and physical ellipticity; the value and gradient
terms use the actual physical weighted measure. -/
theorem sourcePhysicalResolvent_coercive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam L α : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω) (hα : 0 < α)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (Real.exp (-2 * L) * min α ((1 / 2 : ℝ) * L⁻¹)) * ‖u‖ ^ 2 ≤
      α * inner ℝ
          (sourcePhysicalValue (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
            (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u)
          (sourcePhysicalValue (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
            (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u) +
        sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u u := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let κ := Real.exp (-2 * L)
  let b := (1 / 2 : ℝ) * L⁻¹
  let μρ := densityWeightedMeasure ρ
  let μσ := densityWeightedMeasure σ
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : μσ ≤ ENNReal.ofReal K • μρ := by
    dsimp [μσ, μρ, σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  let hReverseMeasure : μρ ≤ ENNReal.ofReal K • μσ := by
    dsimp [μρ, μσ, ρ, σ, K]
    exact sourceReducedMeasure_le_physical ω hd lam L hω
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gp := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hκ : 0 < κ := Real.exp_pos _
  have hκK : κ * K = 1 := by
    dsimp [κ, K]
    calc
      Real.exp (-2 * L) * Real.exp (2 * L) = Real.exp ((-2 * L) + (2 * L)) :=
        (Real.exp_add _ _).symm
      _ = 1 := by rw [show (-2 * L) + (2 * L) = 0 by ring, Real.exp_zero]
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hb : 0 < b := by
    dsimp [b]
    exact mul_pos (by norm_num) (inv_pos.mpr hLpos)
  have hmin0 : 0 ≤ min α b := le_of_lt (lt_min hα hb)
  have hvalInt : Integrable (fun x => g.value x ^ 2) μσ := by
    refine (gp.value_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    have e : ‖gp.value x‖ ^ 2 = gp.value x ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
    exact e
  have hgradInt : Integrable (fun x => ‖g.weakGradient x‖ ^ 2) μσ := by
    exact gp.gradient_memLp.integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hvalNonneg : 0 ≤ᵐ[μσ] fun x => g.value x ^ 2 := by
    filter_upwards [] with x
    exact sq_nonneg _
  have hgradNonneg : 0 ≤ᵐ[μσ] fun x => ‖g.weakGradient x‖ ^ 2 := by
    filter_upwards [] with x
    positivity
  have hredVal :
      (∫ x, g.value x ^ 2 ∂μρ) ≤ K * ∫ x, g.value x ^ 2 ∂μσ :=
    integral_le_const_mul_of_measure_le μρ μσ K hK hReverseMeasure
      (fun x => g.value x ^ 2) hvalNonneg hvalInt
  have hredGrad :
      (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) ≤
        K * ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ :=
    integral_le_const_mul_of_measure_le μρ μσ K hK hReverseMeasure
      (fun x => ‖g.weakGradient x‖ ^ 2) hgradNonneg hgradInt
  have hκredVal : κ * (∫ x, g.value x ^ 2 ∂μρ) ≤
      ∫ x, g.value x ^ 2 ∂μσ := by
    calc
      κ * (∫ x, g.value x ^ 2 ∂μρ) ≤ κ * (K * ∫ x, g.value x ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_left hredVal hκ.le
      _ = ∫ x, g.value x ^ 2 ∂μσ := by rw [← mul_assoc, hκK, one_mul]
  have hκredGrad : κ * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) ≤
      ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ := by
    calc
      κ * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) ≤
          κ * (K * ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_left hredGrad hκ.le
      _ = ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ := by rw [← mul_assoc, hκK, one_mul]
  have hvalueInner : inner ℝ
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u) =
        ∫ x, g.value x ^ 2 ∂μσ := by
    exact
      sourcePhysicalValue_inner_self_eq_integral (ρ := ρ) (hρ := hρ)
        (hρpos := hρpos) (σ := σ) (K := K) (hMeasure := hMeasure) u
  have hformInt : Integrable (weightedFormIntegrand ω.1 gp gp) μσ := by
    exact physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω gp gp
  have henergyPoint : ∀ x, b * ‖gp.weakGradient x‖ ^ 2 ≤
      weightedFormIntegrand ω.1 gp gp x := by
    intro x
    have hEll := (hω.1 x).2 (WithLp.ofLp (gp.weakGradient x))
    have hnorm := euclideanSq_ofLp_eq_norm_sq (gp.weakGradient x)
    unfold weightedFormIntegrand
    calc
      b * ‖gp.weakGradient x‖ ^ 2 =
          (1 / 2 : ℝ) * (L⁻¹ * euclideanSq (WithLp.ofLp (gp.weakGradient x))) := by
        dsimp [b]
        rw [hnorm]
        ring
      _ ≤ (1 / 2 : ℝ) * dot (WithLp.ofLp (gp.weakGradient x))
          ((ω.1 x).mulVec (WithLp.ofLp (gp.weakGradient x))) :=
        mul_le_mul_of_nonneg_left hEll.1 (by norm_num)
  have hformLower : b * (∫ x, ‖gp.weakGradient x‖ ^ 2 ∂μσ) ≤
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u u := by
    have hm := integral_mono_ae (hgradInt.const_mul b) hformInt
      (Filter.Eventually.of_forall henergyPoint)
    rw [integral_const_mul] at hm
    exact hm
  have hphysValNonneg : 0 ≤ ∫ x, g.value x ^ 2 ∂μσ :=
    integral_nonneg_of_ae hvalNonneg
  have hphysGradNonneg : 0 ≤ ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ :=
    integral_nonneg_of_ae hgradNonneg
  have hvalueTerm : (κ * min α b) * (∫ x, g.value x ^ 2 ∂μρ) ≤
      α * (∫ x, g.value x ^ 2 ∂μσ) := by
    calc
      (κ * min α b) * (∫ x, g.value x ^ 2 ∂μρ) =
          min α b * (κ * ∫ x, g.value x ^ 2 ∂μρ) := by ring
      _ ≤ min α b * (∫ x, g.value x ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_left hκredVal hmin0
      _ ≤ α * (∫ x, g.value x ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_right (min_le_left α b) hphysValNonneg
  have hgradientTerm : (κ * min α b) *
        (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) ≤
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u u := by
    calc
      (κ * min α b) * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) =
          min α b * (κ * ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) := by ring
      _ ≤ min α b * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_left hκredGrad hmin0
      _ ≤ b * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μσ) :=
        mul_le_mul_of_nonneg_right (min_le_right α b) hphysGradNonneg
      _ ≤ _ := hformLower
  calc
    (κ * min α b) * ‖u‖ ^ 2 =
        (κ * min α b) *
          ((∫ x, g.value x ^ 2 ∂μρ) +
            ∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) := by
      rw [densityWeightedH1Space_norm_sq_integral]
    _ ≤ α * (∫ x, g.value x ^ 2 ∂μσ) +
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u u := by
      calc
        _ = (κ * min α b) * (∫ x, g.value x ^ 2 ∂μρ) +
            (κ * min α b) * (∫ x, ‖g.weakGradient x‖ ^ 2 ∂μρ) := by ring
        _ ≤ _ := add_le_add hvalueTerm hgradientTerm
    _ = α * inner ℝ
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u) +
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u u := by
      rw [← hvalueInner]

end

end EinsteinRelation.SpatialDirichlet

