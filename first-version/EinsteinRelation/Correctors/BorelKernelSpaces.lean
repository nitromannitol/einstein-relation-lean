import EinsteinRelation.Environment.AKMContinuousReconstruction
import EinsteinRelation.External.AKMHeatKernel

/-! # Polish spaces for coefficient-parametrized continuous kernels

Source: `paper/main.tex:693–698,777–784,842`; AKM (0.6), (0.11),
and Proposition E.1. Continuous normalized elliptic fields form a closed
subspace of the compact-open coefficient space. Kernels are continuous
functions of strictly positive time and both spatial variables.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace EinsteinRelation.Correctors.BorelKernel

open Environment.AKMTestIntegralSupport

local instance {d : ℕ} : PolishSpace (CoefficientField d) :=
  Localization.coefficientField_polish d

/-- Continuous fields satisfying precisely the normalized coefficient
bounds. Source: `paper/main.tex:693–698`; AKM (0.6). -/
def ellipticFields (d : ℕ) (K : ℝ) : Set (CoefficientField d) :=
  {F | (∀ x, (F x).transpose = F x) ∧
    ∀ x ξ, euclideanSq ξ ≤ dot ξ ((F x).mulVec ξ) ∧
      dot ξ ((F x).mulVec ξ) ≤ K * euclideanSq ξ}

/-- The normalized continuous coefficient carrier is closed in compact-open
topology. Source: `paper/main.tex:693–698`. -/
theorem isClosed_ellipticFields (d : ℕ) (K : ℝ) :
    IsClosed (ellipticFields d K) := by
  have hc (x ξ : Vec d) :
      Continuous (fun F : CoefficientField d => dot ξ ((F x).mulVec ξ)) := by
    unfold dot
    exact continuous_finset_sum _ fun i _ => continuous_const.mul
      ((continuous_apply i).comp
        ((continuous_eval_const x).matrix_mulVec continuous_const))
  have heq : ellipticFields d K =
      (⋂ x : Vec d, {F : CoefficientField d | (F x).transpose = F x}) ∩
      ⋂ x : Vec d, ⋂ ξ : Vec d,
        ({F : CoefficientField d | euclideanSq ξ ≤ dot ξ ((F x).mulVec ξ)} ∩
        {F : CoefficientField d | dot ξ ((F x).mulVec ξ) ≤ K * euclideanSq ξ}) := by
    ext F
    simp only [ellipticFields, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  exact (isClosed_iInter fun x => isClosed_eq
    (continuous_eval_const x).matrix_transpose (continuous_eval_const x)).inter
      (isClosed_iInter fun x => isClosed_iInter fun ξ =>
        (isClosed_le continuous_const (hc x ξ)).inter
          (isClosed_le (hc x ξ) continuous_const))

/-- A continuous representative of an actual AKM coefficient.
Source: `paper/main.tex:693–698`. -/
abbrev ContinuousCoefficient (d : ℕ) (K : ℝ) := ellipticFields d K

instance continuousCoefficientPolish (d : ℕ) (K : ℝ) :
    PolishSpace (ContinuousCoefficient d K) :=
  (isClosed_ellipticFields d K).polishSpace

/-- The continuous carrier maps to the existing AKM carrier, with identical
pointwise coefficients. Source: `paper/main.tex:693–698`. -/
def toCoefficient {d : ℕ} {K : ℝ} (A : ContinuousCoefficient d K) : Coefficient d K where
  field := A.1
  locally_integrable := fun i j =>
    ((continuous_apply j).comp ((continuous_apply i).comp A.1.continuous)).locallyIntegrable
  symmetric := A.2.1
  elliptic := A.2.2

/-- Positive-time space for the E.1 kernel, with both spatial variables.
Source: `paper/main.tex:777–784,842`. -/
abbrev KernelDomain (d : ℕ) := Set.Ioi (0 : ℝ) × (Vec d × Vec d)

instance kernelDomainPolish (d : ℕ) : PolishSpace (KernelDomain d) := by
  letI : PolishSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.polishSpace
  infer_instance

instance kernelDomainLocallyCompact (d : ℕ) : LocallyCompactSpace (KernelDomain d) := by
  letI : LocallyCompactSpace (Set.Ioi (0 : ℝ)) := isOpen_Ioi.locallyCompactSpace
  infer_instance

/-- Continuous kernels with compact-open topology, retaining positive-time
point values. Source: `paper/main.tex:777–784,842`. -/
abbrev ContinuousKernel (d : ℕ) := C(KernelDomain d, ℝ)

instance kernelPolish (d : ℕ) : PolishSpace (ContinuousKernel d) := by
  infer_instance

instance kernelMeasurableSpace (d : ℕ) : MeasurableSpace (ContinuousKernel d) :=
  borel (ContinuousKernel d)

instance kernelBorelSpace (d : ℕ) : BorelSpace (ContinuousKernel d) := ⟨rfl⟩

/-- Extend a continuous positive-time kernel by zero to all times.
Source: `paper/main.tex:777–784,842`. -/
def extendKernel {d : ℕ} (P : ContinuousKernel d) (t : ℝ) (x y : Vec d) : ℝ :=
  if ht : 0 < t then P (⟨t, ht⟩, (x, y)) else 0

/-- The extension agrees with the original continuous kernel at positive
times. Source: `paper/main.tex:777–784,842`. -/
theorem extendKernel_pos {d : ℕ} (P : ContinuousKernel d)
    (t : ℝ) (ht : 0 < t) (x y : Vec d) :
    extendKernel P t x y = P (⟨t, ht⟩, (x, y)) := dif_pos ht

/-- Evaluation of a continuous kernel is jointly measurable, including its
zero extension at nonpositive times. Source: `paper/main.tex:777–784,842`. -/
theorem measurable_extendKernel (d : ℕ) :
    Measurable (fun z : ContinuousKernel d × (ℝ × (Vec d × Vec d)) =>
      extendKernel z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let s : Set (ContinuousKernel d × (ℝ × (Vec d × Vec d))) := {z | 0 < z.2.1}
  have hs : MeasurableSet s := measurableSet_lt measurable_const measurable_snd.fst
  let q : s → ContinuousKernel d × KernelDomain d :=
    fun z => (z.1.1, (⟨z.1.2.1, z.2⟩, z.1.2.2))
  have hq : Measurable q :=
    measurable_subtype_coe.fst.prodMk
      ((measurable_subtype_coe.snd.fst.subtype_mk).prodMk measurable_subtype_coe.snd.snd)
  have he : Measurable (fun z : ContinuousKernel d × KernelDomain d => z.1 z.2) :=
    (continuous_fst.eval continuous_snd).measurable
  exact Measurable.dite (he.comp hq) measurable_const hs

end EinsteinRelation.Correctors.BorelKernel
