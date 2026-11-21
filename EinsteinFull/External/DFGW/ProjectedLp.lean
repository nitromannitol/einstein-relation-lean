import EinsteinFull.External.DFGW.MartingaleCovariance

/-! # Scalar projections in `L²`

The `L²` vector of a scalar projection is the corresponding linear combination of coordinate
`L²` vectors.
-/

open MeasureTheory EinsteinRelation
open scoped BigOperators

namespace EinsteinFull.External.DFGW

variable {S : Type*} [MeasurableSpace S] {μ : Measure S} {d : ℕ}

/-- Scalar projection commutes with passage from an observable to its `L²` class. -/
theorem projected_toLp_eq_sum (φ : S → Vec d) (hφ : MemLp φ 2 μ) (e : Vec d)
    (hg : MemLp (fun x => dot e (φ x)) 2 μ) :
    hg.toLp (fun x => dot e (φ x)) =
      ∑ i : Fin d, e i • ((hφ.eval i).toLp (fun x => φ x i)) := by
  let v : Fin d → Lp ℝ 2 μ := fun i => e i • ((hφ.eval i).toLp (fun x => φ x i))
  change hg.toLp (fun x => dot e (φ x)) = ∑ i : Fin d, v i
  apply Lp.ext
  have hvi : ∀ᵐ x ∂μ, ∀ i : Fin d, v i x = e i * φ x i := by
    rw [ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (e i) ((hφ.eval i).toLp (fun x => φ x i)),
      MemLp.coeFn_toLp (hφ.eval i)] with x hs hi
    rw [hs]
    change e i * ((hφ.eval i).toLp (fun x => φ x i)) x = _
    rw [hi]
  filter_upwards [MemLp.coeFn_toLp hg, Lp.coeFn_finsetSum Finset.univ v, hvi] with x hx hs hvx
  rw [hx, hs]
  simp only [Finset.sum_apply, dot, hvx]

end EinsteinFull.External.DFGW
