import EinsteinFull.Calculus.C4PhysicalOrbitGradientContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology Interval
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem timePrimitive_weak_smul {d : ℕ} {j : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative univ j f g) (c : ℝ) :
    HasWeakPartialDerivative univ j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨h.1.smul c, h.2.1.smul c, ?_⟩
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [h.2.2 φ hφ]
  ring

private theorem timePrimitive_graph_smul {d : ℕ} (c : ℝ)
    {u : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (h : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (c • u) (c • G) := by
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => c • u x) (fun j x => c • G j x)
    (Lp.coeFn_smul c u) (fun j => Lp.coeFn_smul c (G j))).mpr
  exact ⟨fun j => by simpa only [Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using
        timePrimitive_weak_smul (h.1 j) c,
    fun j => by simpa only [Complex.real_smul, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using
        timePrimitive_weak_smul (h.2 j) c⟩

private theorem timePrimitive_graph_add {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u + v) (G + H) := by
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x + v x) (fun j x => G j x + H j x)
    (Lp.coeFn_add u v) (fun j => Lp.coeFn_add (G j) (H j))).mpr
  exact ⟨fun j => by simpa only [Complex.add_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j),
    fun j => by simpa only [Complex.add_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)⟩

/-- Integration of a continuous physical H1 curve preserves its actual weak gradient. -/
theorem physicalH1Graph_intervalIntegral
    {d : ℕ}
    (u : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : Continuous u) (hG : ∀ j, Continuous (fun t => G t j))
    (hgraph : ∀ t, IsPhysicalH1Graph volume (Or.inl rfl) (u t) (G t))
    (s t : ℝ) :
    IsPhysicalH1Graph volume (Or.inl rfl)
      (∫ r in s..t, u r) (fun j => ∫ r in s..t, G r j) := by
  let E := Lp ℂ 2 (volume : Measure (Vec d))
  let S : Submodule ℝ (E × (Fin d → E)) := {
    carrier := {p | IsPhysicalH1Graph volume (Or.inl rfl) p.1 p.2}
    zero_mem' := by
      change IsPhysicalH1Graph volume (Or.inl rfl) 0 0
      simpa only [zero_smul] using timePrimitive_graph_smul 0 (hgraph 0)
    add_mem' := fun hp hq => timePrimitive_graph_add hp hq
    smul_mem' := fun c _ hp => timePrimitive_graph_smul c hp }
  have hclosed : IsClosed (S : Set (E × (Fin d → E))) :=
    isClosed_physicalH1Graph volume (Or.inl rfl)
  have : CompleteSpace S := hclosed.completeSpace_coe
  let f : ℝ → S := fun r => ⟨(u r, G r), hgraph r⟩
  have hf : Continuous f := (hu.prodMk (continuous_pi hG)).subtype_mk _
  let q : S := ∫ r in s..t, f r
  have hval : q.val.1 = ∫ r in s..t, u r := by
    exact ((ContinuousLinearMap.fst ℝ E (Fin d → E)).comp S.subtypeL
      |>.intervalIntegral_comp_comm (hf.intervalIntegrable s t)).symm
  have hgrad (j : Fin d) : q.val.2 j = ∫ r in s..t, G r j := by
    exact (((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ E (Fin d → E))).comp S.subtypeL
      |>.intervalIntegral_comp_comm (hf.intervalIntegrable s t)).symm
  have hq := q.property
  change IsPhysicalH1Graph volume (Or.inl rfl) q.val.1 q.val.2 at hq
  rw [hval, show q.val.2 = (fun j => ∫ r in s..t, G r j) from funext hgrad] at hq
  exact hq
end EinsteinFull.Blueprint
