import EinsteinFull.Regeneration.CoordinateWeightedError
import PDEFoundation.Sobolev.H1.Pairing

/-!
# Weighted gradient and elliptic energy on coordinate sections

The coercivity estimate controls the full weighted gradient on every finite
transverse section of a coordinate slab.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The full weighted gradient energy is bounded by the coefficient energy. -/
theorem coordinate_weighted_gradient_le_energy
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (u : PDE.H1Function U) (i : Fin (n + 1)) (a b s lam Λ : ℝ)
    (hs : 0 ≤ s)
    (K : Set (Fin n → ℝ)) (hK : MeasurableSet K) (hKfinite : volume K ≠ ∞)
    (hsub : coordinateIntervalBox n i a b K ⊆ U)
    (A : PDE.CoeffField (n + 1))
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (A x)) :
    Integrable (fun p => Real.exp (s * p.1) * PDE.vecNormSq (u.grad (centralSlabPoint n i p)))
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    Integrable (fun p => PDE.vecDot
      (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p)))
      ((volume.restrict (Icc a b)).prod (volume.restrict K)) ∧
    lam * (∫ p, Real.exp (s * p.1) * PDE.vecNormSq (u.grad (centralSlabPoint n i p))
      ∂((volume.restrict (Icc a b)).prod (volume.restrict K))) ≤
      ∫ p, PDE.vecDot (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p))
        ∂((volume.restrict (Icc a b)).prod (volume.restrict K)) := by
  let ν : Measure (Fin n → ℝ) := volume.restrict K
  let : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hKfinite
  let μ : Measure (ℝ × (Fin n → ℝ)) := (volume.restrict (Icc a b)).prod ν
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  let V : Set (ℝ × (Fin n → ℝ)) := Ioc a b ×ˢ K
  let W := coordinateIntervalBox n i a b K
  have hpres : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have hpre : e ⁻¹' W = V := by
    ext p
    simp [W, coordinateIntervalBox, e, V]
  have hWmeas : MeasurableSet W := (measurableSet_Ioc.prod hK).preimage
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).measurable
  have hm : (volume : Measure (ℝ × (Fin n → ℝ))).restrict V = μ := by
    dsimp only [V, μ, ν]
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  have hpresW := hpres.restrict_preimage hWmeas
  rw [hpre, hm] at hpresW
  have hg : Integrable (fun p => PDE.vecNormSq (u.grad (centralSlabPoint n i p))) μ := by
    have h : Integrable (fun p => PDE.vecNormSq (u.grad (e p))) μ := by
      rw [← hm, ← hpre]
      exact (hpres.integrableOn_comp_preimage e.measurableEmbedding).2
        ((PDE.integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2).mono_set hsub)
    exact h
  have hw : Measurable (fun p : ℝ × (Fin n → ℝ) => Real.exp (s * p.1)) :=
    Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)
  have hwbound : ∀ᵐ p ∂μ, ‖Real.exp (s * p.1)‖ ≤ Real.exp (s * b) := by
    have h := (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Icc a b))
      (ν := ν)).ae (ae_restrict_mem measurableSet_Icc)
    filter_upwards [h] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp.2 hs)
  have hgweight : Integrable (fun p => Real.exp (s * p.1) *
      PDE.vecNormSq (u.grad (centralSlabPoint n i p))) μ :=
    hg.bdd_mul hw.aestronglyMeasurable hwbound
  obtain ⟨lam', Λ', hEll'⟩ := hEll
  let energy : PDE.Vec (n + 1) → ℝ := fun x =>
    PDE.vecDot (PDE.matVecMul (Real.exp (s * x i) • A x) (u.grad x)) (u.grad x)
  have henergyU : IntegrableOn energy U := by
    simpa only [energy, PDE.vecDot_comm] using
      PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll' u.gradMemL2
  have henergy : Integrable (fun p =>
      PDE.vecDot (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p))) μ := by
    have h : Integrable (fun p => energy (e p)) μ := by
      rw [← hm, ← hpre]
      exact (hpres.integrableOn_comp_preimage e.measurableEmbedding).2 (henergyU.mono_set hsub)
    convert h using 1
    funext p
    have hecoord : (e p) i = p.1 := by
      simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]
    simp only [energy, centralSlabPoint, hecoord]
    rfl
  have hAe : ∀ᵐ p ∂μ, PDE.IsEllipticMatrix lam Λ (A (centralSlabPoint n i p)) :=
    hpresW.quasiMeasurePreserving.ae (ae_restrict_of_ae_restrict_of_subset hsub hA)
  have hpoint : ∀ᵐ p ∂μ,
      lam * (Real.exp (s * p.1) * PDE.vecNormSq (u.grad (centralSlabPoint n i p))) ≤
        PDE.vecDot (PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
          (u.grad (centralSlabPoint n i p))) (u.grad (centralSlabPoint n i p)) := by
    filter_upwards [hAe] with p hp
    have hbase := hp.coercive (u.grad (centralSlabPoint n i p))
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (s * p.1)).le
    have hmat : PDE.matVecMul (Real.exp (s * p.1) • A (centralSlabPoint n i p))
        (u.grad (centralSlabPoint n i p)) = Real.exp (s * p.1) •
          PDE.matVecMul (A (centralSlabPoint n i p)) (u.grad (centralSlabPoint n i p)) :=
      Matrix.smul_mulVec _ _ _
    rw [hmat, PDE.DGNM.vecDot_smul_left, PDE.vecDot_comm]
    nlinarith
  refine ⟨hgweight, henergy, ?_⟩
  have hcompare := integral_mono_ae (hgweight.const_mul lam) henergy hpoint
  rw [integral_const_mul] at hcompare
  exact hcompare

end EinsteinFull.Regeneration
