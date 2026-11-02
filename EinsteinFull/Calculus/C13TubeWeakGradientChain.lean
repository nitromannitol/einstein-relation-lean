import EinsteinFull.Calculus.C13TubeNativeCutoffProduct
import PDEFoundation.Sobolev.Ch4.ChainRule

open EinsteinRelation MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The native weak gradient obeys the bounded C¹ chain rule on an open set. -/
theorem c13_native_weak_gradient_bounded_C1_chain {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) (u : Vec d → ℝ) (G : Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict U))
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0) (M : ℝ) (hM : 0 ≤ M)
    (hdF : ∀ r : ℝ, |deriv F r| ≤ M) :
    MemLp (fun x => F (u x)) 2 (volume.restrict U) ∧
    MemLp (fun x => euclideanNorm ((deriv F (u x)) • G x)) 2 (volume.restrict U) ∧
    HasWeakGradient U (fun x => F (u x)) (fun x => deriv F (u x) • G x) := by
  have hcoord (i : Fin d) : MemLp (fun x => G x i) 2 (volume.restrict U) := by
    apply hG.mono' (hw i).2.1.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (G x)) i)
  have hpde : PDE.HasWeakGradientOn U u G := by
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, PDE.basisVec, unitVector] using
      (hw i).2.2 φ ⟨hφ, hc, hs⟩
  let w : PDE.H1Function U := ⟨u, G, hu, hcoord, hpde⟩
  have hlip := PDE.lipschitzWith_of_abs_deriv_le hM (hF.differentiable (by simp)) hdF
  have hf : MemLp (fun x => F (u x)) 2 (volume.restrict U) := by
    change MemLp (F ∘ u) 2 (volume.restrict U)
    exact hlip.comp_memLp hF0 hu
  have hg : PDE.GradMemL2On U (fun x i => deriv F (u x) * G x i) :=
    PDE.Ch4Infra.gradMemL2_comp_of_deriv_bounded w hF hM hdF
  have hvec : MemLp (fun x => (WithLp.toLp 2 (deriv F (u x) • G x) :
      EuclideanSpace ℝ (Fin d))) 2 (volume.restrict U) := by
    apply memLp_piLp_iff.mpr
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul] using hg i
  have hweak : PDE.HasWeakGradientOn U (fun x => F (u x))
      (fun x i => deriv F (u x) * G x i) := by
    refine PDE.Ch4Infra.hasWeakGradientOn_of_local_ball hU
      (PDE.Ch4Infra.locallyIntegrableOn_of_memL2On hf)
      (fun i => PDE.Ch4Infra.locallyIntegrableOn_of_memL2On (hg i)) ?_
    intro x hx
    obtain ⟨r, hr, hsub⟩ := PDE.Ch4Infra.exists_ball_subset hU hx
    exact ⟨r, hr, hsub, PDE.H1Function.hasWeakGradient_comp_contDiff_of_deriv_bounded
      (PDE.Ch4Infra.isOpenBoundedConvexDomain_ball x r)
      (w.restrict Metric.isOpen_ball hsub) hF hM hdF⟩
  refine ⟨hf, ?_, ?_⟩
  · simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hvec.norm
  · intro i
    refine ⟨PDE.Ch4Infra.locallyIntegrableOn_of_memL2On hf, PDE.Ch4Infra.locallyIntegrableOn_of_memL2On (hg i), ?_⟩
    intro φ hφ
    simpa only [coordinateDerivative, PDE.basisVec, unitVector, Pi.smul_apply, smul_eq_mul] using
      hweak i φ hφ.1 hφ.2.1 hφ.2.2

end EinsteinFull.Calculus
