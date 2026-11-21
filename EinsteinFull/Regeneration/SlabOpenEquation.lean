import EinsteinFull.Regeneration.SlabLocalPDEComparison

/-!
# Restriction of the force-slab equation

A single weak equation in the open force slab supplies the local equations
needed for the slab energy iteration and Harnack comparison.
-/

open MeasureTheory Set PDE
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- The part of an ambient domain lying strictly between the force faces. -/
def openForceSlab {d : ℕ} (U : Set (PDE.Vec d)) (i : Fin d) (L : ℝ) :
    Set (PDE.Vec d) :=
  U ∩ {x | x i ∈ Ioo (-L) L}

/-- The force slab is open when the ambient domain is open. -/
theorem isOpen_openForceSlab {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (i : Fin d) (L : ℝ) : IsOpen (openForceSlab U i L) := by
  exact hU.inter (isOpen_Ioo.preimage (continuous_apply i))

/-- A weak equation on an open subdomain restricts compatibly with an ambient
Sobolev representative to every smaller open subdomain. -/
theorem weak_solution_restrict_from_subdomain {d : ℕ}
    {U V W : Set (PDE.Vec d)} {u : PDE.H1Function U} {a : PDE.CoeffField d}
    {f : PDE.Vec d → ℝ} {F : PDE.Vec d → PDE.Vec d}
    (hV : IsOpen V) (hW : IsOpen W) (hVU : V ⊆ U) (hWV : W ⊆ V)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a V (u.restrict hV hVU) f F) :
    PDE.IsWeakDivergenceFormL2SolutionOn a W (u.restrict hW (hWV.trans hVU)) f F := by
  have h := weak_divergence_form_l2_solution_restrict hsol hV hW hWV
  have heq : (u.restrict hV hVU).restrict hW hWV = u.restrict hW (hWV.trans hVU) := by
    apply PDE.H1Function.ext <;> rfl
  rwa [heq] at h

/-- A centered comparison box lies in the open force slab whenever it lies in
the ambient domain. -/
theorem centeredSlabBox_subset_openForceSlab {d : ℕ} {U : Set (PDE.Vec d)}
    (i : Fin d) (L R : ℝ) (hsub : centeredSlabBox i L R ⊆ U) :
    centeredSlabBox i L R ⊆ openForceSlab U i L := by
  intro x hx
  refine ⟨hsub hx, ?_⟩
  change x i ∈ Ioo (-L) L
  have hi := hx i (mem_univ i)
  simpa only [centeredSlabLower, centeredSlabUpper, ite_true] using hi

/-- Comparison balls lie strictly between the force faces for sufficiently
large slab width. -/
theorem central_comparison_ball_subset_openForceSlab (n : ℕ) (i : Fin (n + 1))
    (L : ℝ) (z : Fin n → ℝ) {U : Set (PDE.Vec (n + 1))}
    (hL : Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) ≤ L)
    (hsub : PDE.euclideanBall
      ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
      (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U) :
    PDE.euclideanBall
      ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
      (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ openForceSlab U i L := by
  let R : ℝ := Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))
  let center : PDE.Vec (n + 1) :=
    (1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z))
  have hR : 0 < R := by dsimp [R]; positivity
  have hc : center i = 0 := by
    simp [center, (centralSlabPoint_coord n i 0 z).1]
  intro x hx
  refine ⟨hsub hx, ?_⟩
  have hdist := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hR).1 hx
  have hi := (PDE.abs_apply_le_vecEuclideanNorm (x - center) i).trans_lt hdist
  simp only [Pi.sub_apply, hc, sub_zero] at hi
  have hi' := abs_lt.mp hi
  change -L < x i ∧ x i < L
  constructor <;> linarith

/-- The slab comparison follows from one equation on the open force slab,
provided the initial energy estimate and boundary values hold. -/
theorem exists_slab_width_of_initial_energy_and_open_equation
    (n : ℕ) (s lam Λ D : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ (U : Set (PDE.Vec (n + 1)))
      (hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U) (i : Fin (n + 1)),
      coordinateSlabBox n i s L ⊆ U →
      ∀ {x₀ : PDE.Vec (n + 1)} {r : ℝ}, 0 < r → Metric.closedBall x₀ r ⊆ U →
      Continuous u.toFun → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1))))),
        u (centralSlabPoint n i (-L, z)) = 0) →
      (∀ᵐ z ∂(volume.restrict
        (Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
          (fun _ => Real.exp (s * L / (n + 1))))),
        u (centralSlabPoint n i (L, z)) = 1) →
      ∀ (A : PDE.CoeffField (n + 1)) (lam' Λ' : ℝ),
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (openForceSlab U i L)
        (u.restrict (isOpen_openForceSlab hU.isOpen i L) inter_subset_left) 0 0 →
      PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x) →
      (∀ j k, AEMeasurable (fun x => A x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x)) →
      (∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) →
      (∫ x in centeredSlabBox i L (slabGeometricRadius n s L 0),
        slabWeightedEnergy A s i u.grad x) ≤
        D * Real.exp ((s * (2 * ((n + 1 : ℕ) : ℝ) - 1) / (n + 1)) * L) →
      (2 / 3 : ℝ) ≤ u 0 := by
  obtain ⟨Lbase, hbase⟩ :=
    exists_slab_width_of_initial_energy_and_local_equations n s lam Λ D hs hlam hΛ
  obtain ⟨Lside, _, hsides⟩ := exists_large_slab_sides n s hs
  refine ⟨max Lbase Lside, ?_⟩
  intro L hL U hU u i hsource x₀ r hr hball hcont hzero hone hleft hright
    A lam' Λ' hsol hEll hmeas hA hsym hinit
  have hLb : Lbase ≤ L := (le_max_left _ _).trans hL
  have hLs : Lside ≤ L := (le_max_right _ _).trans hL
  obtain ⟨hside, htrans⟩ := hsides L hLs
  have hV := isOpen_openForceSlab hU.isOpen i L
  have hboxes : ∀ j < 2 * (n + 1), ∃ hQU :
      centeredSlabBox i L (slabGeometricRadius n s L j) ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (centeredSlabBox i L (slabGeometricRadius n s L j))
        (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0 := by
    intro j _
    let R := slabGeometricRadius n s L j
    have hclosed := centeredSlab_closed_subset_source i s L R (slabGeometricRadius_le_source n s L j)
    have hbox := axisBox_subset_closedCoordinateBox i (centeredSlabLower i L R)
      (centeredSlabUpper i L R)
    have hbox' : centeredSlabBox i L R ⊆
        closedCoordinateBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) (-L) L := by
      simpa only [centeredSlabBox, centeredSlabLower, centeredSlabUpper, ite_true] using hbox
    have hQU : centeredSlabBox i L R ⊆ U := hbox'.trans (hclosed.trans hsource)
    have hQV := centeredSlabBox_subset_openForceSlab i L R hQU
    refine ⟨hQU, ?_⟩
    exact weak_solution_restrict_from_subdomain hV (PDE.isOpen_axisBox _ _)
      inter_subset_left hQV hsol
  have hballs : ∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
      ∀ hBU : PDE.euclideanBall
        ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
        (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
        (PDE.euclideanBall
          ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
          (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))))
        (u.restrict (PDE.isOpen_euclideanBall _ _) hBU) 0 0 := by
    intro z _ hBU
    have hR : Real.sqrt (8 * ((n + 1 : ℕ) : ℝ)) ≤ L := by linarith
    have hBV := central_comparison_ball_subset_openForceSlab n i L z hR hBU
    exact weak_solution_restrict_from_subdomain hV (PDE.isOpen_euclideanBall _ _)
      inter_subset_left hBV hsol
  exact hbase L hLb U hU u i hsource hr hball hcont hzero hone hleft hright
    A lam' Λ' hboxes hballs hEll hmeas hA hsym hinit

end EinsteinFull.Regeneration
