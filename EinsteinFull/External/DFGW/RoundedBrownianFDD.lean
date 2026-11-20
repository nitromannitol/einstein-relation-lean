import EinsteinFull.External.DFGW.RoundedBrownianProjection
import LatticeProb.Prob.CramerWold

/-! # Joint finite-dimensional limits on the unit interval

The scalar projected limits yield joint convergence at finitely many rounded grid times.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Rounded grid values converge jointly to Brownian values at finitely many times in `[0,1]`. -/
theorem tendstoInDistribution_rounded_martingale_fdd
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) (hPfin : P Set.univ ≠ ⊤)
    (N : ℝ≥0 → C(ℝ, S) → Vec d) (hN : Martingale N Draft.dfgwPast P)
    (hN2 : ∀ t, MemLp (N t) 2 P)
    (hstat : ∀ s t, (fun η => N (s + t) η - N s η) =ᵐ[P]
      fun η => N t (Draft.dfgwShift s η))
    (D : Mat d) (hD : D.transpose = D)
    (hcov : ∀ e : Vec d, dot e (D.mulVec e) = ∫ η, dot e (N 1 η) ^ 2 ∂P)
    (W : Measure (Path d)) (hW : IsBrownianLaw D W)
    (m : ℕ) (t : Fin m → ℝ≥0) (ht : ∀ j, t j ≤ 1) :
    letI : IsProbabilityMeasure P := hP.probability
    letI : IsProbabilityMeasure W := hW.1
    TendstoInDistribution (fun (n : ℕ) η j => (Real.sqrt (n + 1))⁻¹ •
      N ⌊(t j : ℝ) * (n + 1 : ℝ)⌋₊ η) atTop
      (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure W := hW.1
  let equiv : EuclideanSpace ℝ (Fin m × Fin d) ≃L[ℝ] (Fin m × Fin d → ℝ) :=
    EuclideanSpace.equiv (Fin m × Fin d) ℝ
  let X : ℕ → C(ℝ, S) → EuclideanSpace ℝ (Fin m × Fin d) := fun n η =>
    equiv.symm (fun p => (Real.sqrt (n + 1))⁻¹ *
      N ⌊(t p.1 : ℝ) * (n + 1 : ℝ)⌋₊ η p.2)
  let Z : Path d → EuclideanSpace ℝ (Fin m × Fin d) := fun γ =>
    equiv.symm (fun p => γ (t p.1) p.2)
  have hX (n : ℕ) : AEMeasurable (X n) P := by
    apply equiv.symm.continuous.measurable.comp_aemeasurable
    apply Measurable.aemeasurable
    apply measurable_pi_iff.mpr
    intro p
    have h := (hN.stronglyAdapted (⌊(t p.1 : ℝ) * (n + 1 : ℝ)⌋₊ : ℝ≥0)).mono
      (Draft.dfgwPast.le _)
    exact measurable_const.mul ((measurable_pi_apply p.2).comp h.measurable)
  have hZ : Continuous Z := by
    apply equiv.symm.continuous.comp
    apply continuous_pi
    intro p
    exact (continuous_apply p.2).comp (continuous_eval_const (t p.1))
  have hinner (v : EuclideanSpace ℝ (Fin m × Fin d)) :
      TendstoInDistribution (fun n η => (inner ℝ (X n η) v : ℝ)) atTop
        (fun γ => (inner ℝ (Z γ) v : ℝ)) (fun _ => P) W := by
    let e : Fin m → Vec d := fun j i => equiv v (j, i)
    have h := tendstoInDistribution_sum_rounded_martingale_brownian
      hP hcoord hμ hPfin N hN hN2 hstat D hD hcov W hW m t e ht
    convert h using 1
    · funext n η
      simp only [X, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      change (∑ p : Fin m × Fin d, equiv v p * ((Real.sqrt (n + 1))⁻¹ *
        N ⌊(t p.1 : ℝ) * (n + 1 : ℝ)⌋₊ η p.2)) = _
      rw [← Finset.univ_product_univ, Finset.sum_product]
      simp only [dot, e, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    · funext γ
      simp only [Z, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      change (∑ p : Fin m × Fin d, equiv v p * γ (t p.1) p.2) = _
      rw [← Finset.univ_product_univ, Finset.sum_product]
      simp only [dot, e]
  have hjoint := LatticeProb.CramerWold.tendstoInDistribution_of_forall_inner
    X Z P W hX hZ.measurable.aemeasurable hinner
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin m × Fin d) =>
      fun j i => equiv x (j, i)) := by
    apply continuous_pi
    intro j
    apply continuous_pi
    intro i
    exact (continuous_apply (j, i)).comp equiv.continuous
  have hresult := hjoint.continuous_comp hcont
  refine TendstoInDistribution.congr ?_ ?_ hresult
  · intro n
    filter_upwards with η
    funext j i
    simp only [Function.comp_apply, X, ContinuousLinearEquiv.apply_symm_apply,
      Pi.smul_apply, smul_eq_mul]
  · filter_upwards with γ
    funext j i
    simp only [Function.comp_apply, Z, ContinuousLinearEquiv.apply_symm_apply]

end EinsteinFull.External.DFGW
