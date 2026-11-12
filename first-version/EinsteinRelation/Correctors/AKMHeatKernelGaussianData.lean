import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Gaussian integrability of bounded initial data

Source: AKM Proposition E.1, (E.10), p. 501; `paper/main.tex:850`.
The Gaussian weight is integrated on the actual coordinate carrier.
-/

open MeasureTheory
open Set
namespace EinsteinRelation.Correctors

/-- The Gaussian kernel `x ↦ exp(-euclideanSq (x - y))` is integrable on `Vec d`. -/
lemma integrable_gaussian_kernel {d : ℕ} (y : Vec d) :
    Integrable (fun x : Vec d => Real.exp (-euclideanSq (x - y))) volume := by
  have h_one_pos : 0 < (1 : ℝ) := by norm_num
  have h_coord (i : Fin d) : Integrable (fun (x : ℝ) => Real.exp (-1 * ((x : ℝ) - y i) ^ 2)) volume := by
    have h_base : Integrable (fun (x : ℝ) => Real.exp (-1 * x ^ 2)) volume :=
      integrable_exp_neg_mul_sq h_one_pos
    have h_map : Measure.map (fun (x : ℝ) => x - y i) volume = volume := by
      simpa [sub_eq_add_neg] using map_add_right_eq_self volume (-y i)
    have h_base_mapped : Integrable (fun (x : ℝ) => Real.exp (-1 * x ^ 2))
        (Measure.map (fun (x : ℝ) => x - y i) volume) :=
      h_map.symm ▸ h_base
    have h_comp : Integrable ((fun (x : ℝ) => Real.exp (-1 * x ^ 2)) ∘ (fun (x : ℝ) => x - y i)) volume :=
      h_base_mapped.comp_aemeasurable ((measurable_id.sub measurable_const).aemeasurable)
    simpa [h_map] using h_comp
  have h_prod : Integrable (fun (x : Vec d) => ∏ i : Fin d, Real.exp (-1 * (x i - y i) ^ 2))
      (Measure.pi (fun (_ : Fin d) => (volume : Measure ℝ))) :=
    Integrable.fintype_prod h_coord
  have h_eq : (fun (x : Vec d) => ∏ i : Fin d, Real.exp (-1 * (x i - y i) ^ 2)) =ᵐ[volume]
      (fun x : Vec d => Real.exp (-euclideanSq (x - y))) := by
    filter_upwards with x
    simp only [euclideanSq, dot, Pi.sub_apply]
    calc
      ∏ i : Fin d, Real.exp (-1 * (x i - y i) ^ 2)
          = Real.exp (∑ i : Fin d, (-1 * (x i - y i) ^ 2)) := by
        rw [Real.exp_sum]
      _ = Real.exp (-∑ i : Fin d, ((x i - y i) ^ 2)) := by
        simp [Finset.sum_neg_distrib, mul_comm]
      _ = Real.exp (-∑ i : Fin d, (x i - y i) * (x i - y i)) := by
        simp [sq]
      _ = Real.exp (-euclideanSq (x - y)) := rfl
  simpa [volume] using h_prod.congr h_eq

/-- A bounded measurable datum obeys (E.10) with k=1 at every center.
Source: paper/main.tex:850; AKM Proposition E.1, p. 501. -/
theorem akm_bounded_gaussian_integrable {d : ℕ} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hb : ∀ᵐ x ∂volume, |f x| ≤ B) (y : Vec d) :
    Integrable (fun x => |f x| * Real.exp (-euclideanSq (x - y))) volume := by
  have h_gaussian : Integrable (fun x : Vec d => Real.exp (-euclideanSq (x - y))) volume :=
    integrable_gaussian_kernel y
  have h_abs : AEStronglyMeasurable (fun x => |f x|) volume :=
    continuous_abs.comp_aestronglyMeasurable hf
  have h_bound : ∀ᵐ x ∂volume, ‖(fun x => |f x|) x‖ ≤ B := by
    filter_upwards [hb] with x hx
    simpa [Real.norm_eq_abs] using hx
  have h_mul : Integrable (fun x => Real.exp (-euclideanSq (x - y)) * |f x|) volume :=
    h_gaussian.mul_bdd h_abs h_bound
  simpa [mul_comm] using h_mul
end EinsteinRelation.Correctors
