import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Local weak coordinate derivatives of the same scalar function agree.
Source: `paper/main.tex:788–800`; identification of recovered time slices. -/
theorem weakPartialDerivative_ae_eq_on_open {d : ℕ}
    {U : Set (Vec d)} (hU : IsOpen U) {i : Fin d}
    {u g h : Vec d → ℝ}
    (hg : HasWeakPartialDerivative U i u g)
    (hh : HasWeakPartialDerivative U i u h) :
    g =ᵐ[volume.restrict U] h := by
  rcases hg with ⟨hu_int, hg_int, hg_eq⟩
  rcases hh with ⟨hu_int', hh_int, hh_eq⟩
  have h_diff_int : LocallyIntegrableOn (g - h) U volume :=
    hg_int.sub hh_int
  have h_zero : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x, φ x • (g - h) x ∂volume = 0 := by
    intro φ φ_diff φ_supp φ_tsupp
    have hspatial : IsSpatialTest U φ := ⟨φ_diff, φ_supp, φ_tsupp⟩
    have h_eq_int : (∫ x in U, g x * φ x) = (∫ x in U, h x * φ x) := by
      linarith [hg_eq φ hspatial, hh_eq φ hspatial]
    have h_compl : ∀ x, x ∉ U → φ x * (g x - h x) = 0 := by
      intro x hx
      have hx' : x ∉ tsupport φ := by
        contrapose! hx
        exact φ_tsupp hx
      rw [image_eq_zero_of_notMem_tsupport hx', zero_mul]
    have h_int_φg : IntegrableOn (fun x => φ x * g x) U volume := by
      have h_int_tsupport : IntegrableOn (fun x => φ x * g x) (tsupport φ) volume := by
        simpa [mul_comm] using
          (hg_int.integrableOn_compact_subset φ_tsupp φ_supp).mul_continuousOn
            (φ_diff.continuous.continuousOn) φ_supp
      have h_support : Function.support (fun x => φ x * g x) ⊆ tsupport φ := by
        intro x hx
        by_contra! hx'
        have hφzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx'
        have hzero : (fun x => φ x * g x) x = 0 := by
          simp [hφzero]
        have : (fun x => φ x * g x) x ≠ 0 := by
          simpa [Function.mem_support] using hx
        exact this hzero
      have h_int : Integrable (fun x => φ x * g x) volume := by
        rwa [integrableOn_iff_integrable_of_support_subset h_support] at h_int_tsupport
      exact h_int.integrableOn
    have h_int_φh : IntegrableOn (fun x => φ x * h x) U volume := by
      have h_int_tsupport : IntegrableOn (fun x => φ x * h x) (tsupport φ) volume := by
        simpa [mul_comm] using
          (hh_int.integrableOn_compact_subset φ_tsupp φ_supp).mul_continuousOn
            (φ_diff.continuous.continuousOn) φ_supp
      have h_support : Function.support (fun x => φ x * h x) ⊆ tsupport φ := by
        intro x hx
        by_contra! hx'
        have hφzero : φ x = 0 := image_eq_zero_of_notMem_tsupport hx'
        have hzero : (fun x => φ x * h x) x = 0 := by
          simp [hφzero]
        have : (fun x => φ x * h x) x ≠ 0 := by
          simpa [Function.mem_support] using hx
        exact this hzero
      have h_int : Integrable (fun x => φ x * h x) volume := by
        rwa [integrableOn_iff_integrable_of_support_subset h_support] at h_int_tsupport
      exact h_int.integrableOn
    calc
      ∫ x, φ x • (g - h) x ∂volume
          = ∫ x, φ x * (g x - h x) ∂volume := by simp
      _ = ∫ x in U, φ x * (g x - h x) ∂volume := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero h_compl]
      _ = ∫ x in U, (g x * φ x - h x * φ x) ∂volume := by
        refine setIntegral_congr_fun hU.measurableSet ?_
        intro x hx
        ring
      _ = (∫ x in U, (g x * φ x) ∂volume) - (∫ x in U, (h x * φ x) ∂volume) := by
        simpa [mul_comm] using integral_sub h_int_φg h_int_φh
      _ = (∫ x in U, g x * φ x ∂volume) - (∫ x in U, h x * φ x ∂volume) := rfl
      _ = (∫ x in U, g x * φ x ∂volume) - (∫ x in U, g x * φ x ∂volume) := by rw [h_eq_int]
      _ = 0 := by ring
  have h_ae_zero : ∀ᵐ x ∂volume, x ∈ U → (g - h) x = 0 :=
    hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero h_diff_int h_zero
  have h_ae_eq : g =ᵐ[volume.restrict U] h := by
    have htemp : (g - h) =ᵐ[volume.restrict U] 0 := by
      apply (ae_restrict_iff' hU.measurableSet).mpr
      filter_upwards [h_ae_zero] with x hx
      intro hxU
      simpa [sub_eq_zero] using hx hxU
    filter_upwards [htemp] with x hx
    simpa [sub_eq_zero] using hx
  exact h_ae_eq

end EinsteinRelation.Correctors
