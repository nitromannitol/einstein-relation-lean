import EinsteinRelation.Environment.CountableSmoothTestApproximation
import EinsteinRelation.Environment.AKMCoefficientObservationUniqueness

open MeasureTheory
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-- A countable smooth test family determines locally integrable coefficient fields
(`paper/main.tex:699–704`, AKM (0.11)). -/
theorem exists_countable_locally_integrable_determining_tests (d : ℕ) :
    ∃ u : ℕ → SmoothCompactTest d, ∀ f g : Vec d → ℝ,
      LocallyIntegrable f volume → LocallyIntegrable g volume →
      (∀ n, (∫ x, (u n).toFun x * f x ∂volume) =
        ∫ x, (u n).toFun x * g x ∂volume) → f =ᵐ[volume] g := by
  obtain ⟨u, hu⟩ := exists_countable_locally_integrable_zero_tests d
  refine ⟨u, fun f g hf hg h_eq => ?_⟩
  have h_diff : LocallyIntegrable (f - g) volume := hf.sub hg
  have h_int_zero : ∀ n, (∫ x, (u n).toFun x * (f - g) x ∂volume) = 0 := by
    intro n
    have h_int_f : Integrable (fun x => (u n).toFun x * f x) volume :=
      hf.integrable_smul_left_of_hasCompactSupport
        (u n).smooth.continuous (u n).compact
    have h_int_g : Integrable (fun x => (u n).toFun x * g x) volume :=
      hg.integrable_smul_left_of_hasCompactSupport
        (u n).smooth.continuous (u n).compact
    calc
      (∫ x, (u n).toFun x * (f - g) x ∂volume)
          = (∫ x, (u n).toFun x * (f x - g x) ∂volume) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        simp
      _ = (∫ x, ((u n).toFun x * f x) - ((u n).toFun x * g x) ∂volume) := by
        refine integral_congr_ae ?_
        filter_upwards with x
        ring
      _ = (∫ x, (u n).toFun x * f x ∂volume) - (∫ x, (u n).toFun x * g x ∂volume) := by
        rw [integral_sub h_int_f h_int_g]
      _ = 0 := by rw [h_eq n, sub_self]
  have h_ae_zero : f - g =ᵐ[volume] 0 := hu (f - g) h_diff h_int_zero
  filter_upwards [h_ae_zero] with x hx
  exact sub_eq_zero.mp hx

end EinsteinRelation.Environment.AKMTestIntegralSupport
