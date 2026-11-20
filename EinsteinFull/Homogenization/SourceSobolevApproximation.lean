import EinsteinFull.Homogenization.L2Convergence
import EinsteinFull.Homogenization.WeakGradientBridge
import Homogenization.Sobolev.H1.BasicLemmas

/-!
# Zero-boundary approximations

The scalar approximation in the Dirichlet competitor space of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, (1.7), converges in the L² seminorm.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation

/-- The smooth approximants in a source zero-boundary Sobolev witness converge
in the L² seminorm to its scalar function. -/
theorem sourceH01_exists_scalar_approx {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : External.AKM.SourceH01 U u g) :
    ∃ v : ℕ → Vec d → ℝ, (∀ n, IsSpatialTest U (v n)) ∧
      Tendsto (fun n => eLpNorm (fun x => v n x - u x) 2 (volume.restrict U))
        atTop (𝓝 0) ∧
      Tendsto (fun n => ∫ x in U, euclideanSq (gradient (v n) x - g x) ∂volume)
        atTop (𝓝 0) := by
  obtain ⟨v, hv, hscalar, hgrad⟩ := h.2.2.2
  refine ⟨v, hv, ?_, hgrad⟩
  apply (tendsto_integral_sq_iff_eLpNorm ?_).mp hscalar
  intro n
  have hmem := (_root_.Homogenization.H10Function.ofContDiff hU
    (hv n).1 (hv n).2.1 (hv n).2.2).toH1Function.memL2
  exact hmem.sub h.1

/-- A source zero-boundary witness determines a CoarseGraining zero-boundary
Sobolev function with exactly the same function and gradient. -/
theorem sourceH01_exists_h10 {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (h : External.AKM.SourceH01 U u g) :
    ∃ w : _root_.Homogenization.H10Function U,
      w.toH1Function.toFun = u ∧ w.toH1Function.grad = g := by
  obtain ⟨v, hv, hscalar, hgrad⟩ := sourceH01_exists_scalar_approx hU h
  have hcoord (n : ℕ) (i : Fin d) :
      MemLp (fun x => gradient (v n) x i - g x i) 2 (volume.restrict U) := by
    have hs := (_root_.Homogenization.H10Function.ofContDiff hU
      (hv n).1 (hv n).2.1 (hv n).2.2).toH1Function.gradMemL2 i
    have hg := (MeasureTheory.memLp_pi_iff.mp h.2.1) i
    change MemLp ((fun x => gradient (v n) x i) - fun x => g x i) 2 (volume.restrict U)
    simpa only [Pi.sub_apply, gradient, coordinateDerivative, unitVector,
      _root_.Homogenization.H10Function.ofContDiff,
      _root_.Homogenization.H1Function.ofContDiff, _root_.Homogenization.basisVec] using
      hs.sub hg
  have hsum (n : ℕ) : Integrable
      (fun x => euclideanSq (gradient (v n) x - g x)) (volume.restrict U) := by
    simpa only [euclideanSq, dot, Pi.sub_apply, ← pow_two] using
      (integrable_finsetSum Finset.univ fun i _ => (hcoord n i).integrable_sq)
  have hcoord_tendsto (i : Fin d) :
      Tendsto (fun n => eLpNorm (fun x => gradient (v n) x i - g x i) 2
        (volume.restrict U)) atTop (𝓝 0) := by
    apply (tendsto_integral_sq_iff_eLpNorm (fun n => hcoord n i)).mp
    apply squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _)
      (fun n => ?_) hgrad
    apply integral_mono (hcoord n i).integrable_sq (hsum n)
    intro x
    simp only [euclideanSq, dot, Pi.sub_apply, ← pow_two]
    exact Finset.single_le_sum
      (f := fun j => (gradient (v n) x j - g x j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  refine ⟨{ toH1Function := sourceH01ToH1 h
            approx := v
            approx_smooth := fun n => (hv n).1
            approx_hasCompactSupport := fun n => (hv n).2.1
            approx_support_subset := fun n => (hv n).2.2
            tendsto_approx := hscalar
            tendsto_approx_grad := ?_ }, rfl, rfl⟩
  intro i
  simpa only [gradient, coordinateDerivative, unitVector,
    _root_.Homogenization.basisVec, sourceH01ToH1] using hcoord_tendsto i

/-- A CoarseGraining zero-boundary Sobolev function satisfies the source
competitor definition on an open domain. -/
theorem h10_sourceH01 {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    (w : _root_.Homogenization.H10Function U) :
    External.AKM.SourceH01 U w.toH1Function.toFun w.toH1Function.grad := by
  refine ⟨w.toH1Function.memL2, ?_, h1_hasWeakGradient w.toH1Function, ?_⟩
  · exact MeasureTheory.memLp_pi_iff.mpr w.toH1Function.gradMemL2
  · refine ⟨w.approx, fun n => ⟨w.approx_smooth n, w.approx_hasCompactSupport n,
      w.approx_support_subset n⟩, ?_, ?_⟩
    · apply (tendsto_integral_sq_iff_eLpNorm ?_).mpr w.tendsto_approx
      intro n
      have hs := (_root_.Homogenization.H10Function.ofContDiff hU
        (w.approx_smooth n) (w.approx_hasCompactSupport n)
        (w.approx_support_subset n)).toH1Function.memL2
      exact hs.sub w.toH1Function.memL2
    · have hcoord (n : ℕ) (i : Fin d) :
          MemLp (fun x => gradient (w.approx n) x i - w.toH1Function.grad x i) 2
            (volume.restrict U) := by
        have hs := (_root_.Homogenization.H10Function.ofContDiff hU
          (w.approx_smooth n) (w.approx_hasCompactSupport n)
          (w.approx_support_subset n)).toH1Function.gradMemL2 i
        change MemLp ((fun x => gradient (w.approx n) x i) -
          fun x => w.toH1Function.grad x i) 2 (volume.restrict U)
        simpa only [gradient, coordinateDerivative, unitVector,
          _root_.Homogenization.H10Function.ofContDiff,
          _root_.Homogenization.H1Function.ofContDiff, _root_.Homogenization.basisVec] using
          hs.sub (w.toH1Function.gradMemL2 i)
      have hc (i : Fin d) : Tendsto
          (fun n => ∫ x in U, (gradient (w.approx n) x i - w.toH1Function.grad x i) ^ 2 ∂volume)
          atTop (𝓝 0) := by
        apply (tendsto_integral_sq_iff_eLpNorm (fun n => hcoord n i)).mpr
        simpa only [gradient, coordinateDerivative, unitVector,
          _root_.Homogenization.basisVec] using w.tendsto_approx_grad i
      have hsum := tendsto_finsetSum Finset.univ (fun i _ => hc i)
      simp only [Finset.sum_const_zero] at hsum
      apply hsum.congr
      intro n
      rw [← integral_finsetSum]
      · apply integral_congr_ae
        filter_upwards with x
        simp only [euclideanSq, dot, Pi.sub_apply, ← pow_two]
      · intro i _
        exact (hcoord n i).integrable_sq

/-- The source and CoarseGraining zero-boundary competitor spaces have the
same functions and weak gradients on every open domain. -/
theorem sourceH01_iff_exists_h10 {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} :
    External.AKM.SourceH01 U u g ↔ ∃ w : _root_.Homogenization.H10Function U,
      w.toH1Function.toFun = u ∧ w.toH1Function.grad = g := by
  constructor
  · exact sourceH01_exists_h10 hU
  · rintro ⟨w, rfl, rfl⟩
    exact h10_sourceH01 hU w

end EinsteinFull.Homogenization
