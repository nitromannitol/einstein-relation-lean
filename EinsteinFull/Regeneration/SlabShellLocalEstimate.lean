import EinsteinFull.Regeneration.SlabTransverseLocalMinimality
import EinsteinFull.Regeneration.SlabShellEstimate
import EinsteinFull.Regeneration.SlabNestedBoxes
import EinsteinFull.Regeneration.SlabWeightedIntegrability
import EinsteinFull.Regeneration.ShellEnergyIntegration

/-!
# Weighted energy estimate on a transverse slab inset

The explicit cutoff competitor and its shell error bounds yield an energy
estimate on the smaller transverse box.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The integrated shell estimate for the explicit slab cutoff competitor. -/
theorem slab_inset_energy_le_shell_errors_of_local_solution
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (hL : 1 ≤ L) (hs : 0 ≤ s)
    (a b : PDE.Vec (n + 1)) (ha : a i = -L) (hb : b i = L)
    (w : ℝ) (hw : 0 < w)
    (hQ : PDE.IsOpenBoundedConvexDomain (PDE.axisBox a b))
    (hclosed : closedCoordinateBox i a b (a i) (b i) ⊆ U)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) (hδpos : ∀ k, 0 < δ k)
    (hthin : ∀ k, a i + δ k < b i - δ k)
    {x₀ : PDE.Vec (n + 1)} {r : ℝ} (hr : 0 < r)
    (hball : Metric.closedBall x₀ r ⊆ U) (hcont : Continuous u.toFun)
    (hleft : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (a i, z)) = 0)
    (hright : ∀ᵐ z ∂(volume.restrict (transverseClosedBox i a b)),
      u (centralSlabPoint n i (b i, z)) = 1)
    (A : PDE.CoeffField (n + 1)) (lam Λ lam' Λ' : ℝ)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
      (PDE.axisBox a b)
      (u.restrict hQ.isOpen ((axisBox_subset_closedCoordinateBox i a b).trans hclosed)) 0 0)
    (hEll : PDE.IsEllipticFieldOn lam' Λ' (PDE.axisBox a b)
      (fun x => Real.exp (s * x i) • A x))
    (hA : ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)), PDE.IsEllipticMatrix lam Λ (A x))
    (hsym : ∀ᵐ x ∂(PDE.volumeOn (PDE.axisBox a b)), (A x).IsSymm) :
    let Q := PDE.axisBox a b
    let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
    let p := slabBoundaryProfile hU i L
    let T : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) * (p x - u x) ^ 2
    let S : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) *
      (PDE.vecNormSq (p.grad x) + PDE.vecNormSq (u.grad x))
    let K : ℝ := (32 * (n + 1 : ℝ)) / w
    IntegrableOn (slabWeightedEnergy A s i u.grad) Q ∧
    IntegrableOn (slabWeightedEnergy A s i p.grad) Q ∧
    IntegrableOn T (Q \ I) ∧ IntegrableOn S (Q \ I) ∧
    (∫ x in I, slabWeightedEnergy A s i u.grad x) ≤
      (∫ x in Q, slabWeightedEnergy A s i p.grad x) +
      Λ * (K ^ 2 + K) * (∫ x in Q \ I, T x) +
      2 * Λ * K * ∫ x in Q \ I, S x := by
  dsimp only
  let Q := PDE.axisBox a b
  let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
  let p := slabBoundaryProfile hU i L
  let η := slabTransverseCutoff i a b w hw
  let K : ℝ := (32 * (n + 1 : ℝ)) / w
  let B : PDE.CoeffField (n + 1) := fun x => Real.exp (s * x i) • A x
  let eu : PDE.Vec (n + 1) → ℝ := slabWeightedEnergy A s i u.grad
  let ep : PDE.Vec (n + 1) → ℝ := slabWeightedEnergy A s i p.grad
  let ec : PDE.Vec (n + 1) → ℝ := fun x => matrixEnergy (B x)
    (u.grad x + (slabCutoffPerturbation hU u i L η).grad x)
  let T : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) * (p x - u x) ^ 2
  let S : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) *
    (PDE.vecNormSq (p.grad x) + PDE.vecNormSq (u.grad x))
  have hQI : I ⊆ Q := slabInsetBox_subset i a b w hw.le
  have hQsub : Q ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have hsymB : ∀ᵐ x ∂(PDE.volumeOn Q), (B x).IsSymm := by
    filter_upwards [hsym] with x hx
    exact hx.smul _
  have hmin := slab_energy_le_transverse_competitor_of_local_solution hU u i L hL a b ha hb w hw hQ hclosed
    δ hδ hδpos hthin hr hball hcont hleft hright B lam' Λ' hsol hEll hsymB
  have hec : IntegrableOn ec Q := hmin.1
  have hmin' : (∫ x in Q, eu x) ≤ ∫ x in Q, ec x := by
    simpa only [eu, ec, slabWeightedEnergy, matrixEnergy, B, Q, η] using hmin.2
  let uQ := u.restrict hQ.isOpen hQsub
  let pQ := p.restrict hQ.isOpen hQsub
  have heu : IntegrableOn eu Q := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll uQ.gradMemL2
    have heq : eu = fun x => PDE.vecDot (uQ.grad x) (PDE.matVecMul (B x) (uQ.grad x)) := by
      funext x
      dsimp only [eu, slabWeightedEnergy, matrixEnergy, uQ, PDE.H1Function.restrict_grad, B]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h
  have hep : IntegrableOn ep Q := by
    have h := PDE.integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll pQ.gradMemL2
    have heq : ep = fun x => PDE.vecDot (pQ.grad x) (PDE.matVecMul (B x) (pQ.grad x)) := by
      funext x
      dsimp only [ep, slabWeightedEnergy, matrixEnergy, pQ, PDE.H1Function.restrict_grad, B]
      rw [PDE.vecDot_comm]
    rw [heq]
    exact h
  have ht : IntegrableOn T (Q \ I) :=
    (integrableOn_box_weighted_profile_error hU u hcont a b i L s).mono_set sdiff_subset
  have hs' : IntegrableOn S (Q \ I) := by
    have hp := integrableOn_box_weighted_vecNormSq a b i s hs hQsub p.grad p.gradMemL2
    have hu := integrableOn_box_weighted_vecNormSq a b i s hs hQsub u.grad u.gradMemL2
    have hsum := hp.add hu
    have heq : S = (fun x => Real.exp (s * x i) * PDE.vecNormSq (p.grad x)) +
        (fun x => Real.exp (s * x i) * PDE.vecNormSq (u.grad x)) := by
      funext x
      simp only [S, Pi.add_apply, mul_add]
    rw [heq]
    exact hsum.mono_set sdiff_subset
  have hplateau : ∀ᵐ x ∂(volume.restrict I), ec x = ep x := by
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox _ _).measurableSet] with x hx
    have hone : η x = 1 := slabTransverseCutoff_eq_one_on_inset i a b w hw hx
    have hgrad := slabCutoff_competitor_grad_of_eq_one hU u i L η x hone
    dsimp only [ec, ep, slabWeightedEnergy]
    rw [hgrad]
  have hshell : ∀ᵐ x ∂(volume.restrict (Q \ I)),
      ec x ≤ ep x + eu x + Λ * (K ^ 2 + K) * T x + 2 * Λ * K * S x := by
    have hAs : ∀ᵐ x ∂(volume.restrict (Q \ I)), PDE.IsEllipticMatrix lam Λ (A x) :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset hA
    have hSyms : ∀ᵐ x ∂(volume.restrict (Q \ I)), (A x).IsSymm :=
      ae_restrict_of_ae_restrict_of_subset sdiff_subset hsym
    filter_upwards [ae_restrict_mem (hQ.measurableSet.diff (PDE.isOpen_axisBox _ _).measurableSet),
      hAs, hSyms] with x hx hxA hxSym
    have hpoint := slab_cutoff_pointwise_energy_le_squared hU u i L s a b w hw x hx.1
      (A x) lam Λ hxA hxSym
    dsimp only [ec, ep, eu, T, S, slabWeightedEnergy, B, K, p, η] at *
    simp only [matrixEnergy_smul_matrix] at hpoint ⊢
    nlinarith [hpoint]
  have hbound := inner_energy_le_profile_add_shell_errors volume Q I hQ.measurableSet
    (PDE.isOpen_axisBox _ _).measurableSet hQI eu ep ec T S (Λ * (K ^ 2 + K)) (2 * Λ * K)
    heu hep hec ht hs' hmin' hplateau hshell
  exact ⟨heu, hep, ht, hs', hbound⟩

end EinsteinFull.Regeneration
