import EinsteinFull.Regeneration.SlabSliceEnergy
import EinsteinFull.Regeneration.SlabProfileEnergy
import EinsteinFull.Regeneration.SlabBoundaryProfile
import PDEFoundation.PDE.DGNM.Bridge

/-!
# Energy lower bound on the central slab

The central-cube comparison and right-face boundary value give the line
increments used in Gantert–Mathieu–Piatnitski, equation (4.12).
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The positive half-slab over the unit transverse cube. -/
noncomputable def centralSlabMeasure (n : ℕ) (L : ℝ) :
    Measure (ℝ × (Fin n → ℝ)) :=
  (volume.restrict (Ioc 0 L)).prod
    (volume.restrict (Icc (fun _ => (-1 : ℝ)) (fun _ => 1)))

/-- The nonnegative force weight preserves the coercive coordinate-energy bound. -/
theorem weighted_energy_coercive_coordinate {d : ℕ} (i : Fin d)
    (s t lam Λ : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (A : PDE.Mat d) (hA : PDE.IsEllipticMatrix lam Λ A) (v : PDE.Vec d) :
    lam * (v i) ^ 2 ≤ PDE.vecDot (PDE.matVecMul (Real.exp (s * t) • A) v) v := by
  have hcoord : (v i) ^ 2 ≤ PDE.vecNormSq v := PDE.sq_apply_le_vecNormSq v i
  have hlow := hA.coercive v
  have hbase : lam * (v i) ^ 2 ≤ PDE.vecDot v (PDE.matVecMul A v) :=
    (mul_le_mul_of_nonneg_left hcoord hA.lam_pos.le).trans hlow
  have hbase0 : 0 ≤ PDE.vecDot v (PDE.matVecMul A v) :=
    (mul_nonneg hA.lam_pos.le (sq_nonneg _)).trans hbase
  have hweight : 1 ≤ Real.exp (s * t) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (mul_nonneg hs ht)
  have hm : PDE.matVecMul (Real.exp (s * t) • A) v =
      Real.exp (s * t) • PDE.matVecMul A v := Matrix.smul_mulVec _ _ _
  rw [hm, PDE.DGNM.vecDot_smul_left, PDE.vecDot_comm]
  nlinarith

/-- A central-cube gap and right-face value force the source energy lower bound. -/
theorem central_slab_energy_lower_of_weak_slices
    (n : ℕ) (L c lam : ℝ) (hL : 0 < L) (hc : 0 ≤ c) (hlam : 0 ≤ lam)
    (u g ρ : ℝ × (Fin n → ℝ) → ℝ)
    (hu : MemLp u 2 (centralSlabMeasure n L))
    (hg : MemLp g 2 (centralSlabMeasure n L))
    (hρ : Integrable ρ (centralSlabMeasure n L))
    (hslice : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      ContinuousOn (fun t => u (t, z)) (Icc 0 L) ∧
      PDE.HasWeakDerivOnIoo 0 L (fun t => u (t, z)) (fun t => g (t, z)) ∧
      c ≤ 1 - u (0, z) ∧ u (L, z) = 1)
    (hcoercive : ∀ᵐ p ∂(centralSlabMeasure n L), lam * g p ^ 2 ≤ ρ p) :
    lam * (c ^ 2 * (2 : ℝ) ^ n) ≤ L * ∫ p, ρ p ∂(centralSlabMeasure n L) := by
  let V : Set (Fin n → ℝ) := Icc (fun _ => -1) (fun _ => 1)
  let ν : Measure (Fin n → ℝ) := volume.restrict V
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr isCompact_Icc.measure_lt_top.ne
  have hmeasure : ν.real univ = (2 : ℝ) ^ n := by
    have h := volume_transverse_cube n 1 (by norm_num)
    simpa [ν, V, measureReal_def] using h
  have hgap : ∀ᵐ z ∂ν,
      ContinuousOn (fun t => u (t, z)) (Icc 0 L) ∧
      PDE.HasWeakDerivOnIoo 0 L (fun t => u (t, z)) (fun t => g (t, z)) ∧
      c ≤ |u (L, z) - u (0, z)| := by
    filter_upwards [hslice] with z ⟨hcont, hweak, hcenter, hface⟩
    refine ⟨hcont, hweak, ?_⟩
    rw [hface]
    exact hcenter.trans (le_abs_self _)
  have h := slab_coercive_energy_lower_of_weak_slices_of_memLp ν L c lam
    hL hc hlam u g ρ hu hg hρ hgap hcoercive
  simpa only [hmeasure, centralSlabMeasure, ν, V] using h

end EinsteinFull.Regeneration
