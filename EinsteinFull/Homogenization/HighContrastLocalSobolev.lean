import HCPoly.Provider.Regularity.CorrectorGlobalH1sLoc
import HCPoly.Analytic.NormEquivalence
import HCPoly.Analytic.EuclideanAmbient

/-!
# Local coefficient-weighted Sobolev membership of global `H¹_loc` functions

A function on `ℝ^d` with a weak gradient, square integrable together with its gradient on
every bounded set, belongs to the local weighted Sobolev class `H¹_{s,loc}` of Armstrong,
Kuusi and Loher, *Homogenization at a polynomial scale in high contrast*, for every coefficient
field that is uniformly elliptic almost everywhere: on each ball, smooth approximation in the
unweighted `H¹` norm on a containing cube transfers to the weighted norm.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open _root_.Homogenization hiding euclideanBall
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem cubeScaleFactor_originCube (n : ℕ) :
    cubeScaleFactor (originCube d (n : ℤ)) = (3 : ℝ) ^ n := by
  simp [cubeScaleFactor, originCube, zpow_natCast]

theorem mem_openCubeSet_originCube_iff {n : ℕ} {x : Vec d} :
    x ∈ openCubeSet (originCube d (n : ℤ)) ↔ ∀ i, |x i| < (3 : ℝ) ^ n / 2 := by
  have hdef : x ∈ openCubeSet (originCube d (n : ℤ)) ↔ ∀ i,
      (((originCube d (n : ℤ)).index i : ℝ) - 1 / 2) * cubeScaleFactor (originCube d (n : ℤ)) <
          x i ∧
        x i < (((originCube d (n : ℤ)).index i : ℝ) + 1 / 2) *
          cubeScaleFactor (originCube d (n : ℤ)) := Iff.rfl
  rw [hdef, cubeScaleFactor_originCube]
  have hidx (i : Fin d) : ((originCube d (n : ℤ)).index i : ℝ) = 0 := by
    simp [originCube]
  simp only [hidx, abs_lt]
  constructor
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]
  · intro h i
    have := h i
    constructor <;> linarith [this.1, this.2]

theorem sq_le_vecNormSq (x : Vec d) (i : Fin d) : x i ^ 2 ≤ vecNormSq x := by
  change x i ^ 2 ≤ ∑ j, x j * x j
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

theorem euclideanBall_subset_openCubeSet_originCube {R : ℝ} {n : ℕ} (hR0 : 0 ≤ R)
    (hR : R ≤ (3 : ℝ) ^ n / 2) :
    HighContrast.euclideanBall d R ⊆ openCubeSet (originCube d (n : ℤ)) := by
  intro x hx
  have hx' : vecNormSq x < R ^ 2 := by
    simpa [HighContrast.euclideanBall, euclideanBallAt] using hx
  rw [mem_openCubeSet_originCube_iff]
  intro i
  have hi := sq_le_vecNormSq x i
  have habs : |x i| < R := abs_lt_of_sq_lt_sq (lt_of_le_of_lt hi hx') hR0
  linarith

/-- A global weak-gradient pair, square integrable on bounded sets, is in the local
weighted Sobolev class of any almost-everywhere uniformly elliptic coefficient field. -/
theorem memH1sLoc_of_hasWeakGradientOn {b : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ᵐ x ∂volume, IsEllipticMatrix lam Lam (b x))
    {v : Vec d → ℝ} {Dv : Vec d → Vec d}
    (hmeas : IsMeasurableGradientPair volume v Dv)
    (hweak : HasWeakGradientOn Set.univ v Dv)
    (hL2 : ∀ n : ℕ, MemL2On (openCubeSet (originCube d (n : ℤ))) v ∧
      GradMemL2On (openCubeSet (originCube d (n : ℤ))) Dv) :
    MemH1sLoc b v Dv := by
  refine ⟨hmeas, fun R hR => ?_⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * R) (by norm_num : (1 : ℝ) < 3)
  have hRn : R ≤ (3 : ℝ) ^ n / 2 := by linarith
  let U := openCubeSet (originCube d (n : ℤ))
  have hU : IsOpenBoundedConvexDomain U := isOpenBoundedConvexDomain_openCubeSet _
  have hBU : HighContrast.euclideanBall d R ⊆ U := euclideanBall_subset_openCubeSet_originCube hR.le hRn
  have hweakU : HasWeakGradientOn U v Dv :=
    hweak.restrict hU.isOpen (Set.subset_univ _)
  let u : H1Function U := ⟨v, Dv, (hL2 n).1, (hL2 n).2, hweakU⟩
  have hball : Metric.closedBall (0 : Vec d) ((3 : ℝ) ^ n / 4) ⊆ U := by
    intro x hx
    have hx' : ‖x‖ ≤ (3 : ℝ) ^ n / 4 := by simpa using hx
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hi : |x i| ≤ (3 : ℝ) ^ n / 4 := by
      have := norm_le_pi_norm x i
      rw [Real.norm_eq_abs] at this
      linarith
    have hpos : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
    linarith
  obtain ⟨w, hw, hlim⟩ :=
    exists_contDiff_tendsto_h1NormSqOnUnweighted_sub hU u hball (by positivity)
  refine ⟨(hweak.restrict (HighContrast.isOpen_euclideanBall d R) (Set.subset_univ _)),
    w, hw, ?_⟩
  rw [tendsto_h1sNormSqOn_sub_zero_iff_restrict (Lam := Lam) hlam (ae_restrict_of_ae hell)]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun k => ?_)
  exact h1NormSqOnUnweighted_mono hBU _ _

end EinsteinFull.Homogenization
