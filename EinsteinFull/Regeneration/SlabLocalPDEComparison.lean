import EinsteinFull.Regeneration.SlabActualLocalIteration
import EinsteinFull.Regeneration.SlabLocalHarnackSobolev
import EinsteinFull.Regeneration.SlabCentralTerminal

/-!
# Slab comparison from the energy iteration

Harnack's central energy lower bound and the iterated upper bound force the
center value of a bounded weighted solution above the source threshold.
-/

open Filter MeasureTheory Set PDE
open scoped ENNReal Topology

namespace EinsteinFull.Regeneration

/-- Under the initial energy estimate, a bounded weighted weak solution with
the source face values has center value at least `2/3` in sufficiently wide slabs. -/
theorem exists_slab_width_of_initial_energy_and_local_equations
    (n : ℕ) (s lam Λ D : ℝ) (hs : 0 < s) (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ (U : Set (PDE.Vec (n + 1)))
      (_hU : PDE.IsOpenBoundedConvexDomain U) (u : PDE.H1Function U) (i : Fin (n + 1)),
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
      (∀ j < 2 * (n + 1), ∃ hQU :
        centeredSlabBox i L (slabGeometricRadius n s L j) ⊆ U,
        PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
          (centeredSlabBox i L (slabGeometricRadius n s L j))
          (u.restrict (PDE.isOpen_axisBox _ _) hQU) 0 0) →
      (∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
        ∀ hBU : PDE.euclideanBall
          ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
          (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U,
        PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (s * x i) • A x)
          (PDE.euclideanBall
            ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
            (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))))
          (u.restrict (PDE.isOpen_euclideanBall _ _) hBU) 0 0) →
      PDE.IsEllipticFieldOn lam' Λ' U (fun x => Real.exp (s * x i) • A x) →
      (∀ j k, AEMeasurable (fun x => A x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(PDE.volumeOn U), PDE.IsEllipticMatrix lam Λ (A x)) →
      (∀ᵐ x ∂(PDE.volumeOn U), (A x).IsSymm) →
      (∫ x in centeredSlabBox i L (slabGeometricRadius n s L 0),
        slabWeightedEnergy A s i u.grad x) ≤
        D * Real.exp ((s * (2 * ((n + 1 : ℕ) : ℝ) - 1) / (n + 1)) * L) →
      (2 / 3 : ℝ) ≤ u 0 := by
  obtain ⟨c, hc, hlower⟩ := exists_central_slab_energy_lower_of_local_harnack n lam Λ s hlam hΛ hs
  let c₀ : ℝ := lam * (c ^ 2 * (2 : ℝ) ^ n)
  have hc₀ : 0 < c₀ := by dsimp [c₀]; positivity
  obtain ⟨Lupper, hupper⟩ := exists_slab_width_of_local_energy_recurrence n s lam Λ D c₀
    hs hlam (hlam.le.trans hΛ) hc₀
  obtain ⟨Lradius, hLradius, hradius⟩ := exists_large_terminal_slab_radius n s hs
  obtain ⟨Lside, hLside, hsides⟩ := exists_large_slab_sides n s hs
  refine ⟨max Lupper (max Lradius Lside), ?_⟩
  intro L hL U hU u i hsource x₀ r hr hball hcont hzero hone hleft hright A lam' Λ'
    hsolBoxes hsolBalls hEll hmeas hA hsym hinit
  have hLu : Lupper ≤ L := (le_max_left _ _).trans hL
  have hLr : Lradius ≤ L := ((le_max_left _ _).trans (le_max_right _ _)).trans hL
  have hLs : Lside ≤ L := ((le_max_right _ _).trans (le_max_right _ _)).trans hL
  have hLpos : 0 < L := hLside.trans_le hLs
  have hRt : 1 < slabGeometricRadius n s L (2 * (n + 1)) := hradius L hLr
  have hRsource : 1 ≤ Real.exp (s * L / (n + 1)) :=
    hRt.le.trans (slabGeometricRadius_le_source n s L (2 * (n + 1)))
  have hunit : Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1) ⊆
      Icc (fun _ : Fin n => -Real.exp (s * L / (n + 1)))
        (fun _ => Real.exp (s * L / (n + 1))) := by
    intro z hz
    constructor <;> intro j
    · have hj := hz.1 j
      linarith
    · have hj := hz.2 j
      linarith
  have hfaceUnit : ∀ᵐ z ∂(volume.restrict (Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1))),
      u (centralSlabPoint n i (L, z)) = 1 :=
    ae_restrict_of_ae_restrict_of_subset hunit hright
  have hcentral : coordinateCentralSlab n i L ⊆ U :=
    (coordinateCentralSlab_subset_slabBox n i s L hLpos.le hRsource).trans hsource
  obtain ⟨hside, htrans⟩ := hsides L hLs
  have hballs : ∀ z ∈ Icc (fun _ : Fin n => (-1 : ℝ)) (fun _ => 1),
      PDE.euclideanBall
        ((1 / 2 : ℝ) • ((0 : PDE.Vec (n + 1)) + centralSlabPoint n i (0, z)))
        (Real.sqrt (8 * ((n + 1 : ℕ) : ℝ))) ⊆ U := by
    intro z hz
    exact (central_comparison_ball_subset_slab_box n i s L z hz hside htrans).trans hsource
  have hterminalSub : centeredSlabBox i L (slabGeometricRadius n s L (2 * (n + 1))) ⊆ U := by
    let R := slabGeometricRadius n s L (2 * (n + 1))
    have hclosed := centeredSlab_closed_subset_source i s L R (slabGeometricRadius_le_source n s L _)
    have hbox := axisBox_subset_closedCoordinateBox i (centeredSlabLower i L R)
      (centeredSlabUpper i L R)
    have hbox' : centeredSlabBox i L R ⊆
        closedCoordinateBox i (centeredSlabLower i L R) (centeredSlabUpper i L R) (-L) L := by
      simpa only [centeredSlabBox, centeredSlabLower, centeredSlabUpper, ite_true] using hbox
    exact hbox'.trans (hclosed.trans hsource)
  by_contra hclaim
  have hsmall : u 0 < (2 / 3 : ℝ) := lt_of_not_ge hclaim
  have hlow := hlower i L hLpos A u hU hcentral ⟨x₀, r, hr, hball⟩ hballs
    ⟨lam', Λ', hEll⟩ hmeas hA hsolBalls hcont hone hsmall hfaceUnit
  have hcentralLe := central_slab_energy_le_centered i L
    (slabGeometricRadius n s L (2 * (n + 1))) s hLpos hRt u A lam' Λ' hterminalSub hEll
  have hhigh := hupper L hLu U hU u i hsource hr hball hcont hzero hone hleft hright
    A lam' Λ' hsolBoxes hEll hA hsym hinit
  have hscale := mul_le_mul_of_nonneg_left hcentralLe hLpos.le
  change c₀ ≤ L * (∫ x in coordinateCentralSlab n i L, slabWeightedEnergy A s i u.grad x) at hlow
  linarith

end EinsteinFull.Regeneration
