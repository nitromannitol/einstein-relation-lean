import EinsteinRelation.Correctors.MeasurableFundamentalGradient
import EinsteinRelation.Correctors.FundamentalPositiveRepresentative

/-! # Jointly measurable spatial derivatives of an E.1 kernel

Source: AKM Proposition E.1, (E.1), pp. 499–501;
`paper/main.tex:787–792,850`. Recovering weak derivatives of the continuous
scalar kernel avoids assuming that its given derivative representatives
were chosen measurably in the initial point.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The first spatial derivative of an E.1 kernel has a jointly measurable
version, retaining every actual fundamental-solution equation and initial
trace. Source: `paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_exists_measurable_spatial_gradient
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C) :
    ∃ Z : ℝ → Vec d → Vec d → Vec d,
      Measurable (fun z : ℝ × (Vec d × Vec d) => Z z.1 z.2.1 z.2.2) ∧
      (∀ y, IsFundamentalSolution A y
        (fun z => P z.1 z.2 y) (fun z => Z z.1 z.2 y)) ∧
      ∀ y, ∀ᵐ t ∂volume.restrict (Set.Ioi 0),
        ((fun x => Z t x y) =ᵐ[volume] (fun x => X t x y)) ∧
        HasWeakGradient Set.univ (fun x => P t x y) (fun x => Z t x y) := by
  classical
  let p : ℝ × (Vec d × Vec d) → ℝ := fun z =>
    if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0
  have hpm : Measurable p := by
    convert hP.1.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      (measurableSet_Ioi.prod MeasurableSet.univ) using 1
    funext z
    change (if 0 < z.1 then P z.1 z.2.1 z.2.2 else 0) =
      (if z ∈ Set.Ioi 0 ×ˢ Set.univ then P z.1 z.2.1 z.2.2 else 0)
    simp only [Set.mem_prod,Set.mem_Ioi,Set.mem_univ,and_true]
  let u : Vec d → ℝ × Vec d → ℝ := fun y z => p (z.1,(z.2,y))
  have hum : Measurable (fun z : Vec d × (ℝ × Vec d) => u z.1 z.2) :=
    hpm.comp (measurable_snd.fst.prodMk (measurable_snd.snd.prodMk measurable_fst))
  have hs : ∀ y, IsFundamentalSolution A y (u y) (fun z => X z.1 z.2 y) := by
    intro y
    apply fundamentalSolution_scalar_congr_positive (hP.2.2.1 y)
    intro t ht x
    simp only [u,p,if_pos ht]
  obtain ⟨R,hRm,hRsol,hReq⟩ := exists_measurable_fundamentalFamily_gradient
    (fun _ : Vec d => A) id u (fun y z => X z.1 z.2 y) hum hs
  let Z : ℝ → Vec d → Vec d → Vec d := fun t x y => R y (t,x)
  refine ⟨Z,?_,?_,?_⟩
  · exact hRm.comp (measurable_snd.snd.prodMk (measurable_fst.prodMk measurable_snd.fst))
  · intro y
    apply fundamentalSolution_scalar_congr_positive (hRsol y)
    intro t ht x
    simp only [u,p,if_pos ht]
  · intro y
    filter_upwards [hReq y,ae_restrict_mem measurableSet_Ioi] with t ht htpos
    refine ⟨ht.1,?_⟩
    have ht0 : 0 < t := htpos
    convert ht.2 using 1
    funext x
    simp only [u,p,if_pos ht0]

end EinsteinRelation.Correctors
