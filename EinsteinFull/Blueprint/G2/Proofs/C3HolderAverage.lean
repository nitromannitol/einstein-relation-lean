import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Calculus.C1BootstrapAverageSupport
import EinsteinFull.Calculus.C3HolderAverageSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The local-time dependency already supplies finite moments for the actual
endpoint and its earlier slice. Anisotropic Gaussian averaging preserves these
moments, hence so does the exact unsmoothing difference. This is only the
membership part of `e:holder-average`; the quantitative decay remains open. -/
theorem holder_average_memLp_of_local_time
    (hlocal : node_e_u3A_local_u2D_timeStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
    let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
    MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨C, Cp, _, _, hbounds⟩ := hlocal d hd D p hp
  obtain ⟨G, V, _, henergy⟩ := hbounds Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨(henergy t ht).1, ?_⟩
  intro b _hb _hb16 hbt
  have h8t : 0 < ((8 * t : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    positivity
  have hU := (henergy (8 * t) h8t).1
  rw [mul_div_cancel_left₀ t (by norm_num : (8 : ℝ≥0) ≠ 0)] at hU
  have hH := (bootstrap_average_homogeneous_Lp Q ⟨0, by omega⟩
    (b * (t : ℝ)) hbt 0 p hp
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) hU).1
  change MemLp (gaussianAverage hd Q (b * (t : ℝ)) hbt
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q) at hH
  exact hU.sub hH

end EinsteinFull.Blueprint
