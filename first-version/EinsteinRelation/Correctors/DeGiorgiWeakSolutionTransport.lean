import Mathlib
import EinsteinRelation.External.GilbargTrudinger
import DeGiorgi.WeakFormulation.SolutionInterfaces
import EinsteinRelation.Correctors.DeGiorgiBallPreimage
import EinsteinRelation.Correctors.DeGiorgiSobolevWitness
import EinsteinRelation.Correctors.DeGiorgiHomogeneousFromDivergence
import EinsteinRelation.Correctors.DeGiorgiWeakDivergenceTransport
open MeasureTheory Filter
open scoped Topology ENNReal

/-! # Weak solutions on balls as De Giorgi homogeneous solutions

A repository weak solution on a set `U` restricts to every subset `V ⊆ U`: the weak
gradient and the weak divergence are inherited, because test functions supported in `V`
are test functions on `U` and their derivatives vanish outside `V`. The restricted
solution on a Euclidean ball is then transported to the De Giorgi weak formulation on
`Metric.ball`, where the flux `a ∇u` has zero weak divergence and bounded entries.
-/

namespace EinsteinRelation.Correctors

/-- A set integral over a subset `V ⊆ U` equals the set integral over `U` when the
integrand vanishes off `V`. Neither set is assumed measurable: both integrals agree with
the whole-space integral of the same function. -/
private lemma setIntegral_eq_of_forall_notMem_of_subset {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) {G : Vec d → ℝ} (hG : ∀ x, x ∉ V → G x = 0) :
    ∫ x in V, G x = ∫ x in U, G x := by
  have hV : ∫ x in V, G x = ∫ x, G x := setIntegral_eq_integral_of_forall_compl_eq_zero hG
  have hU : ∫ x in U, G x = ∫ x, G x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hG x fun hxV => hx (hVU hxV)
  exact hV.trans hU.symm

/-- A spatial test function supported in `V` vanishes outside `V`. -/
private lemma test_eq_zero_of_notMem {d : ℕ} {V : Set (Vec d)} {φ : Vec d → ℝ}
    (hφ : IsSpatialTest V φ) {x : Vec d} (hx : x ∉ V) : φ x = 0 :=
  (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hφ.2.2 ht))).self_of_nhds

/-- The coordinate derivative of a spatial test function vanishes outside its support. -/
private lemma coordinateDerivative_eq_zero_of_notMem {d : ℕ} {V : Set (Vec d)}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest V φ) (i : Fin d) {x : Vec d} (hx : x ∉ V) :
    coordinateDerivative i φ x = 0 := by
  simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ (fun ht => hx (hφ.2.2 ht)),
    ContinuousLinearMap.zero_apply]

/-- A weak partial derivative on `U` is a weak partial derivative on each subset `V ⊆ U`. -/
private lemma hasWeakPartialDerivative_of_subset {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) {i : Fin d} {f g : Vec d → ℝ}
    (h : HasWeakPartialDerivative U i f g) : HasWeakPartialDerivative V i f g := by
  refine ⟨h.1.mono_set hVU, h.2.1.mono_set hVU, ?_⟩
  intro φ hφ
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have hz1 : ∀ x, x ∉ V → f x * coordinateDerivative i φ x = 0 := fun x hx => by
    rw [coordinateDerivative_eq_zero_of_notMem hφ i hx, mul_zero]
  have hz2 : ∀ x, x ∉ V → g x * φ x = 0 := fun x hx => by
    rw [test_eq_zero_of_notMem hφ hx, mul_zero]
  have e1 : ∫ x in V, f x * coordinateDerivative i φ x =
      ∫ x in U, f x * coordinateDerivative i φ x :=
    setIntegral_eq_of_forall_notMem_of_subset hVU hz1
  have e2 : ∫ x in V, g x * φ x = ∫ x in U, g x * φ x :=
    setIntegral_eq_of_forall_notMem_of_subset hVU hz2
  rw [e1, e2]
  exact h.2.2 φ hφU

/-- A weak divergence on `U` is a weak divergence on each subset `V ⊆ U`. -/
private lemma hasWeakDivergence_of_subset {d : ℕ} {U V : Set (Vec d)}
    (hVU : V ⊆ U) {F : Vec d → Vec d} {k : Vec d → ℝ}
    (hw : HasWeakDivergence U F k) : HasWeakDivergence V F k := by
  refine ⟨fun i => (hw.1 i).mono_set hVU, hw.2.1.mono_set hVU, ?_⟩
  intro φ hφ
  have hφU : IsSpatialTest U φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩
  have hz1 : ∀ x, x ∉ V → dot (F x) (gradient φ x) = 0 := fun x hx => by
    have hg : gradient φ x = 0 :=
      funext fun i => coordinateDerivative_eq_zero_of_notMem hφ i hx
    simp only [hg, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  have hz2 : ∀ x, x ∉ V → k x * φ x = 0 := fun x hx => by
    rw [test_eq_zero_of_notMem hφ hx, mul_zero]
  have e1 : ∫ x in V, dot (F x) (gradient φ x) =
      ∫ x in U, dot (F x) (gradient φ x) :=
    setIntegral_eq_of_forall_notMem_of_subset hVU hz1
  have e2 : ∫ x in V, k x * φ x = ∫ x in U, k x * φ x :=
    setIntegral_eq_of_forall_notMem_of_subset hVU hz2
  rw [e1, e2]
  exact hw.2.2 φ hφU

/-- A Gilbarg–Trudinger weak solution on `U` is one on each subset `V ⊆ U`. -/
private lemma weakSolution_of_subset {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {a : Vec d → Mat d} {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : External.GilbargTrudinger.WeakSolution U a u g) :
    External.GilbargTrudinger.WeakSolution V a u g :=
  ⟨hw.1.mono_measure (Measure.restrict_mono_set volume hVU),
    hw.2.1.mono_measure (Measure.restrict_mono_set volume hVU),
    fun i => hasWeakPartialDerivative_of_subset hVU (hw.2.2.1 i),
    hasWeakDivergence_of_subset hVU hw.2.2.2⟩

/-- Every entry of a matrix is bounded by `|Λ|` when the sum of the squares of all its
entries is at most `Λ ^ 2`. -/
private lemma abs_entry_le_abs_of_sum_sq_le {d : ℕ} {M : Mat d} {Λ : ℝ}
    (h : ∑ i, ∑ j, |M i j| ^ 2 ≤ Λ ^ 2) (i j : Fin d) : |M i j| ≤ |Λ| := by
  have hrow : |M i j| ^ 2 ≤ ∑ j', |M i j'| ^ 2 :=
    Finset.single_le_sum (f := fun j' => |M i j'| ^ 2) (fun j' _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hall : ∑ j', |M i j'| ^ 2 ≤ ∑ i', ∑ j', |M i' j'| ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', |M i' j'| ^ 2)
      (fun i' _ => Finset.sum_nonneg fun j' _ => sq_nonneg _) (Finset.mem_univ i)
  have hsq : M i j ^ 2 ≤ Λ ^ 2 := by
    have h2 : |M i j| ^ 2 ≤ Λ ^ 2 := hrow.trans (hall.trans h)
    rwa [sq_abs] at h2
  exact sq_le_sq.mp hsq

/-- A Gilbarg–Trudinger weak solution, restricted to a Euclidean ball inside its domain,
is a homogeneous De Giorgi weak solution of the coefficient field `a ∘ ofLp` on that ball. -/
theorem isHomogeneousWeakSolution_of_weakSolution {d : ℕ} [NeZero d] {U : Set (Vec d)}
    {a : Vec d → Mat d} {lam Λ : ℝ}
    (ha : External.GilbargTrudinger.EllipticBound U a lam Λ)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hsol : External.GilbargTrudinger.WeakSolution U a u g)
    {y : Vec d} {R : ℝ} (hB : External.AKM.ball y R ⊆ U)
    (A : DeGiorgi.EllipticCoeff d
      (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R))
    (hA : A.a = fun x => a (WithLp.ofLp x)) :
    DeGiorgi.IsHomogeneousWeakSolution A (fun x => u (WithLp.ofLp x)) := by
  have hV := weakSolution_of_subset hB hsol
  have hw0 := exists_memW1pWitness_of_hasWeakGradient hV.1 hV.2.1 hV.2.2.1
  rw [preimage_ofLp_ball] at hw0
  obtain ⟨hw, hwg⟩ := hw0
  have hdiv0 := hasWeakDiv_of_hasWeakDivergence hV.2.2.2
  rw [preimage_ofLp_ball] at hdiv0
  have hF : (fun x : EuclideanSpace ℝ (Fin d) => DeGiorgi.matMulE (A.a x) (hw.weakGrad x)) =
      fun x => WithLp.toLp 2 ((a (WithLp.ofLp x)).mulVec (g (WithLp.ofLp x))) := by
    funext x
    have hAx : A.a x = a (WithLp.ofLp x) := congrFun hA x
    have hwx : hw.weakGrad x = WithLp.toLp 2 (g (WithLp.ofLp x)) := congrFun hwg x
    rw [hAx, hwx]
    rfl
  have hdiv : DeGiorgi.HasWeakDiv (fun _ : EuclideanSpace ℝ (Fin d) => (0 : ℝ))
      (fun x => DeGiorgi.matMulE (A.a x) (hw.weakGrad x))
      (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R) := by
    rw [hF]
    exact hdiv0
  have hK : ∀ x ∈ Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R,
      ∀ i j, |A.a x i j| ≤ |Λ| := by
    intro x hx i j
    have hxB : WithLp.ofLp x ∈ External.AKM.ball y R := by
      have hx' : x ∈ (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → Vec d) ⁻¹'
          External.AKM.ball y R := by
        rw [preimage_ofLp_ball]
        exact hx
      exact hx'
    have hAx : A.a x = a (WithLp.ofLp x) := congrFun hA x
    rw [hAx]
    exact abs_entry_le_abs_of_sum_sq_le (ha.2 (WithLp.ofLp x) (hB hxB)).2 i j
  have hΩ : IsOpen (Metric.ball (WithLp.toLp 2 y : EuclideanSpace ℝ (Fin d)) R) :=
    Metric.isOpen_ball
  exact isHomogeneousWeakSolution_of_hasWeakDiv hΩ A hK hw hdiv

end EinsteinRelation.Correctors
