import EinsteinFull.External.DFGW.GridPastFiltration
import EinsteinFull.External.DFGW.ShiftedPastSigma

/-! # Past measurability of shift-invariant observables

A time-shift-invariant integrable trajectory observable is measurable, up to a null set, with
respect to the past coordinate sigma-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An integrable observable invariant under all negative grid shifts is past measurable
up to a null set. -/
theorem aestronglyMeasurable_past_of_grid_invariant
    (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    {t : ℝ≥0} (ht : 0 < t) (f : C(ℝ, S) → ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable f)
    (hinv : ∀ n : ℕ, f ∘ Draft.dfgwShift (-((n • t : ℝ≥0) : ℝ)) =ᵐ[P] f) :
    AEStronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic 0)] f P := by
  let : IsProbabilityMeasure P := hP.probability
  let U (n : ℕ) : ℝ := ((n • t : ℝ≥0) : ℝ)
  let g (n : ℕ) : C(ℝ, S) → ℝ :=
    P[f | gridPast t n] ∘ Draft.dfgwShift (-U n)
  have hg (n : ℕ) : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic 0)] (g n) := by
    have h : StronglyMeasurable[MeasurableSpace.comap (Draft.dfgwShift (S := S) (-U n))
        (Draft.dfgwCoordSigma (Set.Iic (U n)))] (g n) := by
      apply StronglyMeasurable.comp_measurable (f := P[f | gridPast t n])
      · exact stronglyMeasurable_condExp
      · exact comap_measurable _
    rw [comap_shift_past_at, add_neg_cancel] at h
    exact h
  have hlim : Tendsto (fun n : ℕ => eLpNorm (P[f | gridPast t n] - f) 1 P) atTop (𝓝 0) := by
    apply hf.tendsto_eLpNorm_condExp
    rw [iSup_gridPast hcoord ht]
    exact hfm
  have hnorm (n : ℕ) : eLpNorm (g n - f) 1 P = eLpNorm (P[f | gridPast t n] - f) 1 P := by
    let V := P[f | gridPast t n] - f
    have hV : AEStronglyMeasurable V P :=
      ((stronglyMeasurable_condExp.mono ((gridPast (S := S) t).le n)).sub hfm).aestronglyMeasurable
    have hshift : MeasurePreserving (Draft.dfgwShift (S := S) (-U n)) P P :=
      ⟨measurable_shift _, hP.stationary _⟩
    have heq : g n - f =ᵐ[P] V ∘ Draft.dfgwShift (-U n) := by
      filter_upwards [hinv n] with η hη
      simp only [Pi.sub_apply, Function.comp_apply, g, V] at hη ⊢
      rw [hη]
    exact (eLpNorm_congr_ae heq).trans (eLpNorm_comp_measurePreserving hV hshift)
  have hlim' : Tendsto (fun n : ℕ => eLpNorm (g n - f) 1 P) atTop (𝓝 0) := by
    simpa only [hnorm] using hlim
  have hmeasure : TendstoInMeasure P g atTop f :=
    tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (by simp) (by simp) hlim'
  obtain ⟨ns, _, hns⟩ := hmeasure.exists_seq_tendsto_ae
  let v : C(ℝ, S) → ℝ := fun η => limUnder atTop (fun n => g (ns n) η)
  have hv : StronglyMeasurable[Draft.dfgwCoordSigma (Set.Iic 0)] v :=
    @StronglyMeasurable.limUnder ℕ C(ℝ, S) ℝ (Draft.dfgwCoordSigma (Set.Iic 0))
      inferInstance inferInstance atTop inferInstance (fun n => g (ns n)) inferInstance
      inferInstance (fun n => hg (ns n))
  refine ⟨v, hv, ?_⟩
  filter_upwards [hns] with η hη
  exact (Tendsto.limUnder_eq hη).symm

end EinsteinFull.External.DFGW
