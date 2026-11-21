import EinsteinFull.Regeneration.SlabSquaredCutoff
import EinsteinFull.Regeneration.SlabAbsorptionIntegration
import EinsteinFull.Regeneration.SlabShellLocalEstimate

/-!
# Boundary Caccioppoli estimate on a slab

The squared transverse cutoff and local energy minimality control the energy
on an inset by the comparison-profile energy and the cutoff value error.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A locally harmonic slab function has controlled energy on a transverse inset. -/
theorem slab_inset_energy_le_profile_and_value_error
    {n : ℕ} {U : Set (PDE.Vec (n + 1))}
    (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U)
    (i : Fin (n + 1)) (L s : ℝ) (hL : 1 ≤ L)
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
    let α := (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * (n + 1 : ℝ)) / w) ^ 2)
    IntegrableOn (slabWeightedEnergy A s i u.grad) I ∧
    (∫ x in I, slabWeightedEnergy A s i u.grad x) ≤
      3 * (∫ x in Q, slabWeightedEnergy A s i p.grad x) +
      2 * α * ∫ x in Q, Real.exp (s * x i) * (p x - u x) ^ 2 := by
  dsimp only
  let Q := PDE.axisBox a b
  let I := PDE.axisBox (slabInsetLower i a w) (slabInsetUpper i b w)
  let p := slabBoundaryProfile hU i L
  let η := slabTransverseCutoff i a b w hw
  let B : PDE.CoeffField (n + 1) := fun x => Real.exp (s * x i) • A x
  let eu : PDE.Vec (n + 1) → ℝ := slabWeightedEnergy A s i u.grad
  let ep : PDE.Vec (n + 1) → ℝ := slabWeightedEnergy A s i p.grad
  let ec : PDE.Vec (n + 1) → ℝ := fun x => matrixEnergy (B x)
    (u.grad x + (slabCutoffPerturbation hU u i L η.sq).grad x)
  let t : PDE.Vec (n + 1) → ℝ := fun x => Real.exp (s * x i) * (p x - u x) ^ 2
  let α : ℝ := (Λ + 4 * Λ ^ 2 / lam) * (4 * ((32 * (n + 1 : ℝ)) / w) ^ 2)
  have hIQ : I ⊆ Q := slabInsetBox_subset i a b w hw.le
  have hQU : Q ⊆ U := (axisBox_subset_closedCoordinateBox i a b).trans hclosed
  have hsymB : ∀ᵐ x ∂(PDE.volumeOn Q), (B x).IsSymm := by
    filter_upwards [hsym] with x hx
    exact hx.smul _
  have hlateral : ∀ j : Fin (n + 1), j ≠ i → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ x ∈ Q, x ∈ boxFaceCollars a b j ρ → η.sq x = 0 := by
    intro j hji
    refine ⟨w / 2, by positivity, ?_⟩
    intro x _ hx
    change η x ^ 2 = 0
    rw [show η x = 0 from slabTransverseCutoff_lateral_zero i a b w hw j hji x hx]
    norm_num
  have hmin := slab_energy_le_cutoff_competitor_of_local_solution hU u i L hL η.sq
    a b ha hb hQ hclosed δ hδ hδpos hthin hr hball hcont hleft hright hlateral B lam' Λ' hsol hEll hsymB
  have hec : IntegrableOn ec Q := hmin.1
  have hmin' : (∫ x in Q, eu x) ≤ ∫ x in Q, ec x := by
    simpa only [eu, ec, slabWeightedEnergy, matrixEnergy, B, Q, η] using hmin.2
  let uQ := u.restrict hQ.isOpen hQU
  let pQ := p.restrict hQ.isOpen hQU
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
  have ht : IntegrableOn t Q := integrableOn_box_weighted_profile_error hU u hcont a b i L s
  have hpoint : ∀ᵐ x ∂(volume.restrict Q),
      ec x ≤ (1 - η x ^ 2 / 2) * eu x + (3 * η x ^ 2 / 2) * ep x + α * t x := by
    filter_upwards [ae_restrict_mem hQ.measurableSet, hA, hsym] with x hx hxA hxSym
    have h := slab_squared_cutoff_pointwise_energy_le hU u i L s a b w hw x hx (A x) lam Λ hxA hxSym
    dsimp only [ec, eu, ep, t, α, slabWeightedEnergy, B, η, p] at *
    simp only [matrixEnergy_smul_matrix] at h ⊢
    nlinarith only [h]
  have hnonneg : ∀ᵐ x ∂(volume.restrict Q), 0 ≤ eu x ∧ 0 ≤ ep x := by
    filter_upwards [ae_restrict_mem hQ.measurableSet] with x hx
    have he := hEll.elliptic hx
    constructor
    · have h := he.coercive (u.grad x)
      have h0 := mul_nonneg he.lam_pos.le (PDE.vecNormSq_nonneg (u.grad x))
      exact h0.trans (by simpa only [eu, slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using h)
    · have h := he.coercive (p.grad x)
      have h0 := mul_nonneg he.lam_pos.le (PDE.vecNormSq_nonneg (p.grad x))
      exact h0.trans (by simpa only [ep, slabWeightedEnergy, matrixEnergy, PDE.vecDot_comm] using h)
  have hinner : ∀ᵐ x ∂(volume.restrict I),
      ec x ≤ (1 / 2 : ℝ) * eu x + (3 / 2 : ℝ) * ep x + α * t x := by
    have hp := ae_restrict_of_ae_restrict_of_subset hIQ hpoint
    filter_upwards [ae_restrict_mem (PDE.isOpen_axisBox _ _).measurableSet, hp] with x hx hp
    have hone : η x = 1 := slabTransverseCutoff_eq_one_on_inset i a b w hw hx
    rw [hone] at hp
    norm_num at hp
    linarith
  have hshell : ∀ᵐ x ∂(volume.restrict (Q \ I)),
      ec x ≤ eu x + (3 / 2 : ℝ) * ep x + α * t x := by
    have hp := ae_restrict_of_ae_restrict_of_subset (show Q \ I ⊆ Q from sdiff_subset) hpoint
    have hn := ae_restrict_of_ae_restrict_of_subset (show Q \ I ⊆ Q from sdiff_subset) hnonneg
    filter_upwards [hp, hn] with x hp hn
    have hη0 := η.nonneg x
    have hη1 := η.le_one x
    have hs : η x ^ 2 ≤ 1 := by nlinarith
    have ha := mul_nonneg (sq_nonneg (η x)) hn.1
    have hb := mul_nonneg (sub_nonneg.mpr hs) hn.2
    nlinarith [hp, ha, hb]
  have hresult := inner_energy_le_of_absorption volume Q I hQ.measurableSet
    (PDE.isOpen_axisBox _ _).measurableSet hIQ eu ep ec t α heu hep hec ht hmin' hinner hshell
  exact ⟨heu.mono_set hIQ, hresult⟩

end EinsteinFull.Regeneration
