import EinsteinFull.Regeneration.SlabShellEstimate
import EinsteinFull.Regeneration.SlabShellProduct
import EinsteinFull.Regeneration.SlabComparisonError
import EinsteinFull.Regeneration.SlabComparisonGradient

/-!
# Weighted error bounds on the physical slab shell

The transverse shell product estimates control the actual physical shell
errors by the weighted coefficient energy and the boundary-layer mass.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The value and gradient errors on the physical shell obey the bounds used
in the slab energy iteration. -/
theorem slab_shell_errors_le_energy
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s lam Λ : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s) (hlam : 0 < lam)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L) (w : ℝ)
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (hKcube : slabShellSection i a b w ⊆
      Icc (fun _ => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))))
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hzero : ∀ x, 0 ≤ u x) (hone : ∀ x, u x ≤ 1)
    (hface : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (L, z)) = 1)
    (A : PDE.CoeffField (n + 1))
    (hEll : ∃ lam' Λ', PDE.IsEllipticFieldOn lam' Λ' U
      (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x)) :
    let Q := PDE.axisBox a b
    let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
    let p := slabBoundaryProfile hU i L
    let T : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) * (u x - p x) ^ 2
    let S : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) *
      (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x))
    let A₀ : ℝ := Real.exp s * 2 ^ n * Real.exp (-(s * L / (n + 1)))
    IntegrableOn T (Q \ I) ∧ IntegrableOn S (Q \ I) ∧
    IntegrableOn (slabWeightedEnergy A s i u.grad) (Q \ I) ∧
    lam * (∫ x in Q \ I, T x) ≤ lam * A₀ + (2 * L) ^ 2 *
      (∫ x in Q \ I, slabWeightedEnergy A s i u.grad x) ∧
    lam * (∫ x in Q \ I, S x) ≤ lam * A₀ +
      ∫ x in Q \ I, slabWeightedEnergy A s i u.grad x := by
  dsimp only
  let K := slabShellSection i a b w
  have ⟨hKm, hKfinite⟩ := slabShellSection_measurable_finite i a b w
  have hKclosed := slabShellSection_subset_closed i a b w
  have hsub : coordinateIntervalBox n i (-L) L K ⊆ U := by
    intro x hx
    apply hclosed
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Icc (a i) (b i)) ∧ _
    change ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i x).1 ∈
      Ioc (-L) L) ∧ _ at hx
    refine ⟨?_, hKclosed hx.2⟩
    simpa only [ha, hb, mem_Icc, mem_Ioc] using ⟨hx.1.1.le, hx.1.2⟩
  have hfaceK : ∀ᵐ z ∂(volume.restrict K), u (centralSlabPoint n i (L, z)) = 1 :=
    ae_restrict_of_ae_restrict_of_subset hKclosed hface
  have hT := slab_comparison_error_le_energy hU u i L s lam Λ hL hs hlam K hKm hKfinite
    hKcube hsub hr hball hcont hzero hone hfaceK A hEll hA
  have hS := slab_comparison_gradient_le_energy hU u i L s lam Λ hL hs hlam K hKm hKfinite
    hKcube hsub A hEll hA
  let Q := PDE.axisBox a b
  let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
  let p := slabBoundaryProfile hU i L
  let μ := (volume.restrict (Icc (-L) L)).prod (volume.restrict K)
  have hEeq : (∫ x in Q \ I, slabWeightedEnergy A s i u.grad x) =
      ∫ q, PDE.vecDot (PDE.matVecMul (Real.exp (s * q.1) • A (centralSlabPoint n i q))
        (u.grad (centralSlabPoint n i q))) (u.grad (centralSlabPoint n i q)) ∂μ := by
    rw [integral_slab_shell_eq_product, ha, hb]
    apply integral_congr_ae
    filter_upwards with q
    dsimp only [slabWeightedEnergy, matrixEnergy]
    rw [(centralSlabPoint_coord n i q.1 q.2).1]
  have hTeq : (∫ x in Q \ I, Real.exp (s * x i) * (u x - p x) ^ 2) =
      ∫ q, Real.exp (s * q.1) * (u (centralSlabPoint n i q) -
        p (centralSlabPoint n i q)) ^ 2 ∂μ := by
    rw [integral_slab_shell_eq_product, ha, hb]
    apply integral_congr_ae
    filter_upwards with q
    rw [(centralSlabPoint_coord n i q.1 q.2).1]
  have hSeq : (∫ x in Q \ I, Real.exp (s * x i) *
      (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x))) =
      ∫ q, Real.exp (s * q.1) * (PDE.vecNormSq (u.grad (centralSlabPoint n i q)) +
        PDE.vecNormSq (p.grad (centralSlabPoint n i q))) ∂μ := by
    rw [integral_slab_shell_eq_product, ha, hb]
    apply integral_congr_ae
    filter_upwards with q
    rw [(centralSlabPoint_coord n i q.1 q.2).1]
  have hQsub : Q ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have ht : IntegrableOn (fun x => Real.exp (s * x i) * (u x - p x) ^ 2) (Q \ I) := by
    have h := integrableOn_box_weighted_profile_error hU u hcont a b i L s
    have heq : (fun x => Real.exp (s * x i) * (u x - p x) ^ 2) =
        (fun x => Real.exp (s * x i) * (p x - u x) ^ 2) := by
      funext x
      congr 1
      ring
    rw [heq]
    exact h.mono_set sdiff_subset
  have hs' : IntegrableOn (fun x => Real.exp (s * x i) *
      (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x))) (Q \ I) := by
    have hu := integrableOn_box_weighted_vecNormSq a b i s hs hQsub u.grad u.gradMemL2
    have hp := integrableOn_box_weighted_vecNormSq a b i s hs hQsub p.grad p.gradMemL2
    have heq : (fun x => Real.exp (s * x i) *
        (PDE.vecNormSq (u.grad x) + PDE.vecNormSq (p.grad x))) =
        (fun x => Real.exp (s * x i) * PDE.vecNormSq (u.grad x)) +
        (fun x => Real.exp (s * x i) * PDE.vecNormSq (p.grad x)) := by
      funext x
      simp only [Pi.add_apply, mul_add]
    rw [heq]
    exact (hu.add hp).mono_set sdiff_subset
  have he : IntegrableOn (slabWeightedEnergy A s i u.grad) (Q \ I) := by
    obtain ⟨lam', Λ', hEll'⟩ := hEll
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll' u.gradMemL2
    have heq : slabWeightedEnergy A s i u.grad = fun x =>
        PDE.vecDot (u.grad x) (PDE.matVecMul (Real.exp (s * x i) • A x) (u.grad x)) := by
      funext x
      dsimp [slabWeightedEnergy, matrixEnergy]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h.mono_set (sdiff_subset.trans hQsub)
  refine ⟨ht, hs', he, ?_, ?_⟩
  · rw [hTeq, hEeq]
    exact hT.2.2
  · rw [hSeq, hEeq]
    exact hS.2

end EinsteinFull.Regeneration
