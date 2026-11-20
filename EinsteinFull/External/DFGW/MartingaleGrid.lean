import EinsteinFull.External.DFGW.MartingaleMaximal

/-! # Martingale excursions on finite time grids

The discrete maximal estimate applies to any increasing finite sample of a martingale indexed by
an arbitrary ordered time set.
-/

open MeasureTheory

namespace EinsteinFull.External.DFGW

variable {Ω ι : Type*} [MeasurableSpace Ω] [Preorder ι]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ℱ : Filtration ι (inferInstance : MeasurableSpace Ω)}

/-- A martingale sampled along an increasing time grid has its squared maximal-excursion
probability bounded by the terminal second moment. -/
theorem sq_measureReal_martingale_max_on_grid_le
    (M : ι → Ω → ℝ) (hM : Martingale M ℱ P) (t : ℕ → ι) (ht : Monotone t)
    (n : ℕ) (hM2 : MemLp (M (t n)) 2 P) {ε : ℝ} (hε : 0 ≤ ε) :
    (ε * P.real {ω | ∃ k ≤ n, ε ≤ |M (t k) ω|}) ^ 2 ≤
      ∫ ω, (M (t n) ω) ^ 2 ∂P := by
  let G : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    { seq := fun k => ℱ (t k)
      mono' := fun _ _ h => ℱ.mono (ht h)
      le' := fun k => ℱ.le (t k) }
  have hsample : Martingale (fun k => M (t k)) G P :=
    ⟨fun k => hM.stronglyAdapted (t k), fun i j hij => hM.2 (t i) (t j) (ht hij)⟩
  exact sq_measureReal_martingale_max_le (fun k => M (t k)) hsample n hM2 hε

end EinsteinFull.External.DFGW
