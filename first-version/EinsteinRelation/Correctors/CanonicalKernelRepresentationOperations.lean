import EinsteinRelation.Correctors.AKMFlowScaling
import EinsteinRelation.External.AKMKernelSemigroup

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Scaling the datum scales the same canonical flow, with the same
kernel. Source: AKM (9.2); `paper/main.tex:787–792,850`. -/
theorem canonicalKernelRepresentation_const_mul {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d} {u : ℝ × Vec d → ℝ}
    (hrep : HasCanonicalKernelRepresentation A g u) (c : ℝ) :
    HasCanonicalKernelRepresentation A (fun x => c • g x) (fun z => c*u z) := by
  obtain ⟨C,P,X,Y,H,hC,hP,hrep⟩ := hrep
  refine ⟨C,P,X,Y,H,hC,hP,?_⟩
  intro t ht x
  have hid (y : Vec d) : dot (c • g y) (Y t x y) = c*dot (g y) (Y t x y) := by
    simp only [dot,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  simp_rw [hid]
  exact ⟨(hrep t ht x).1.const_mul c,by rw [(hrep t ht x).2,integral_const_mul,mul_neg]⟩

/-- Changing a vector datum on a null set preserves its canonical flow.
Source: AKM (9.2); `paper/main.tex:787–792,850`. -/
theorem canonicalKernelRepresentation_initialFlux_congr_ae {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g h : Vec d → Vec d} {u : ℝ × Vec d → ℝ}
    (hrep : HasCanonicalKernelRepresentation A g u) (heq : g =ᵐ[volume] h) :
    HasCanonicalKernelRepresentation A h u := by
  obtain ⟨C,P,X,Y,H,hC,hP,hrep⟩ := hrep
  refine ⟨C,P,X,Y,H,hC,hP,?_⟩
  intro t ht x
  have hd : (fun y => dot (g y) (Y t x y)) =ᵐ[volume] (fun y => dot (h y) (Y t x y)) :=
    heq.mono fun y hy => by
      change dot (g y) (Y t x y) = dot (h y) (Y t x y)
      rw [hy]
  exact ⟨(hrep t ht x).1.congr hd,(hrep t ht x).2.trans (by rw [integral_congr_ae hd])⟩

end EinsteinRelation.Correctors
