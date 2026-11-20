import EinsteinFull.Regeneration.SlabCutoffPerturbation
import PDEFoundation.Sobolev.H1.Pairing

/-!
# Weighted Sobolev densities on slab boxes

The force weight is bounded on a box, so Sobolev gradient energies and the
continuous profile error are integrable there.
-/

open MeasureTheory Set PDE

namespace EinsteinFull.Regeneration

/-- The weighted squared norm of an `L²` vector field is integrable on a box. -/
theorem integrableOn_box_weighted_vecNormSq {d : ℕ} {U : Set (PDE.Vec d)}
    (a b : PDE.Vec d) (i : Fin d) (s : ℝ) (hs : 0 ≤ s)
    (hsub : PDE.axisBox a b ⊆ U) (v : PDE.Vec d → PDE.Vec d)
    (hv : PDE.MemVectorL2On U v) :
    IntegrableOn (fun x => Real.exp (s * x i) * PDE.vecNormSq (v x)) (PDE.axisBox a b) := by
  have hraw : IntegrableOn (fun x => PDE.vecNormSq (v x)) (PDE.axisBox a b) :=
    (PDE.integrableOn_vecNormSq_of_memVectorL2On hv).mono_set hsub
  have hw : Measurable (fun x : PDE.Vec d => Real.exp (s * x i)) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).measurable
  have hbound : ∀ᵐ x ∂(volume.restrict (PDE.axisBox a b)),
      ‖Real.exp (s * x i)‖ ≤ Real.exp (s * b i) := by
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox a b).measurableSet] with x hx
    have hi := hx i (Set.mem_univ i)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hi.2.le hs)
  exact hraw.bdd_mul hw.aestronglyMeasurable hbound

/-- A continuous profile difference has integrable weighted squared error on a box. -/
theorem integrableOn_box_weighted_profile_error {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U) (hcont : Continuous u.toFun)
    (a b : PDE.Vec (n + 1)) (i : Fin (n + 1)) (L s : ℝ) :
    IntegrableOn (fun x => Real.exp (s * x i) *
      (slabBoundaryProfile hU i L x - u x) ^ 2) (PDE.axisBox a b) := by
  have hprof : Continuous (slabBoundaryProfile hU i L).toFun := by
    have heq : (slabBoundaryProfile hU i L).toFun =
        fun x => min (max (x i + L) 0) 1 := by
      funext x
      exact slabBoundaryProfile_apply hU i L x
    rw [heq]
    exact (((continuous_apply i).add continuous_const).max continuous_const).min continuous_const
  have hfunc : Continuous (fun x : PDE.Vec (n + 1) => Real.exp (s * x i) *
      (slabBoundaryProfile hU i L x - u x) ^ 2) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply i))).mul
      ((hprof.sub hcont).pow 2)
  have hQ : PDE.axisBox a b ⊆ Icc a b := by
    intro x hx
    constructor <;> intro j
    · exact (hx j (Set.mem_univ j)).1.le
    · exact (hx j (Set.mem_univ j)).2.le
  exact (hfunc.continuousOn.integrableOn_compact isCompact_Icc).mono_set hQ

end EinsteinFull.Regeneration
