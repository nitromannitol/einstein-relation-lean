import EinsteinFull.External.DFGW.InvariantConstant
import Mathlib.Dynamics.Ergodic.Ergodic

/-! # Ergodicity of trajectory time shifts

Every positive time shift on the stationary reversible trajectory space is ergodic.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Every positive time shift is ergodic under the stationary trajectory law. -/
theorem ergodic_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (hμ : μ Set.univ ≠ ⊤) {t : ℝ≥0} (ht : 0 < t) :
    Ergodic (Draft.dfgwShift (S := S) t) P := by
  let : IsProbabilityMeasure P := hP.probability
  let hshift : MeasurePreserving (Draft.dfgwShift (S := S) t) P P :=
    ⟨measurable_shift _, hP.stationary _⟩
  refine ⟨hshift, ?_⟩
  refine ⟨?_⟩
  intro A hA hAinv
  let Z : Lp ℝ 2 P := indicatorConstLp 2 hA (measure_ne_top P A) (1 : ℝ)
  have hZ : Z =ᵐ[P] A.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn
  have hZshift : Lp.compMeasurePreserving _ hshift Z = Z := by
    have hZ' := hshift.quasiMeasurePreserving.ae hZ
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving Z hshift, hZ', hZ] with η ha hb hc
    simp only [Function.comp_apply] at ha hb
    rw [ha, hb, hc]
    have hmem : Draft.dfgwShift (S := S) t η ∈ A ↔ η ∈ A := by
      change η ∈ (Draft.dfgwShift (S := S) t) ⁻¹' A ↔ η ∈ A
      rw [hAinv]
    by_cases hη : η ∈ A <;> simp [hη, hmem]
  have hmean := fixed_shift_eq_mean hP hcoord hμ (measure_ne_top P Set.univ) ht Z hZshift
  have hmeanAE : Z =ᵐ[P] indicatorConstLp 2 MeasurableSet.univ
      (measure_ne_top P Set.univ) (∫ η, Z η ∂P) :=
    (congrArg (fun z : Lp ℝ 2 P => (z : C(ℝ, S) → ℝ)) hmean).eventuallyEq
  have hconst : Z =ᵐ[P] fun _ => ∫ η, Z η ∂P := by
    refine hmeanAE.trans ?_
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
      (hμs := measure_ne_top P Set.univ) (c := ∫ η, Z η ∂P)] with η hη
    simpa only [Set.indicator_univ] using hη
  have hind : A.indicator (fun _ => (1 : ℝ)) =ᵐ[P] fun _ => ∫ η, Z η ∂P := hZ.symm.trans hconst
  apply eventuallyEmptyOrUniv_iff.mpr
  by_cases hc : (∫ η, Z η ∂P) = 0
  · right
    filter_upwards [hind] with η hη
    intro hmem
    simp [hmem, hc] at hη
  · left
    filter_upwards [hind] with η hη
    by_contra hmem
    apply hc
    simpa [hmem] using hη.symm

end EinsteinFull.External.DFGW
