import EinsteinFull.Calculus.C12TubeNashSemigroupRowSmoothing

open MeasureTheory PDE EinsteinFull.External.Source.GMP
open EinsteinRelation
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped ENNReal NNReal

noncomputable section
namespace EinsteinFull.Calculus

/-- A structural all-time bound for the native weighted spectral heat kernel. -/
theorem spectral_heat_native_nash_kernel_upper {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (R : ℝ) (hR : 0 < R) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ (ρ : PDE.Vec d → ℝ)
      (α : PDE.Vec d → EinsteinRelation.Mat d) (h : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
      Filter.Tendsto s.eigenvalue Filter.atTop Filter.atTop →
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) →
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) →
      ∀ (t : ℝ), 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        |∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
          s.eigenfunction n y| ≤ CN * t ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hdec⟩ := spectral_heat_native_L1_L2_decay hd hκ
  let A : ℝ := 4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ))) / 4
  let p : ℝ := -(d : ℝ) / 2
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ p, Real.rpow_pos_of_pos hA _, ?_⟩
  intro ρ α h s vs hs hb hvar t ht x hx y hy
  let q : ℝ≥0 := ⟨t / 4, by positivity⟩
  have hq : 0 < q := by change 0 < t / 4; positivity
  have hrow (z : PDE.Vec d) (hz : z ∈ sourceBall 0 R) :
      ‖spectralHeatRow s (t / 2) z‖ ^ 2 ≤ A ^ p * t ^ p := by
    have hm := spectral_heat_native_row_L1_le_one hd hκ h R hR s vs hs hb hvar q hq z hz
    have hh := hdec R hR ρ α h s vs hb hvar (spectralHeatRow s q z) 1
      (by norm_num) hm q hq
    have hr := spectral_heat_operator_row hd hκ h hR s q q (by exact_mod_cast hq) z hz
    rw [hr] at hh
    have hqval : (q : ℝ) = t / 4 := rfl
    have he : (q : ℝ) + q = t / 2 := by rw [hqval]; ring
    rw [he] at hh
    have he' : (4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) *
        (1 : ℝ) ^ (4 / (d : ℝ)))) * (q : ℝ) = A * t := by
      rw [hqval, Real.one_rpow, mul_one]
      dsimp [A]; ring
    rw [he', Real.mul_rpow hA.le ht.le] at hh
    exact hh
  have hx' := hrow x hx
  have hy' := hrow y hy
  have hi := abs_real_inner_le_norm (spectralHeatRow s (t / 2) x)
    (spectralHeatRow s (t / 2) y)
  rw [spectral_heat_row_inner_closedBall hd hκ h hR s (t / 2) (t / 2)
    (by positivity) (by positivity) x y (subset_closure hx) (subset_closure hy)] at hi
  have htt : t / 2 + t / 2 = t := by ring
  rw [htt] at hi
  have hn1 := norm_nonneg (spectralHeatRow s (t / 2) x)
  have hn2 := norm_nonneg (spectralHeatRow s (t / 2) y)
  have hab : ‖spectralHeatRow s (t / 2) x‖ * ‖spectralHeatRow s (t / 2) y‖ ≤
      A ^ p * t ^ p := by nlinarith [sq_nonneg (‖spectralHeatRow s (t / 2) x‖ - ‖spectralHeatRow s (t / 2) y‖)]
  exact hi.trans (by simpa only [p] using hab)

#print axioms spectral_heat_native_nash_kernel_upper

/-- The same bound for the Lebesgue density, including the actual weight at y. -/
theorem spectral_heat_native_nash_density_upper {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (R : ℝ) (hR : 0 < R) :
    ∃ CN : ℝ, 0 < CN ∧ ∀ (ρ : PDE.Vec d → ℝ)
      (α : PDE.Vec d → EinsteinRelation.Mat d) (h : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
      Filter.Tendsto s.eigenvalue Filter.atTop Filter.atTop →
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) →
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) →
      ∀ (t : ℝ), 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        |ρ y * (∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x *
          s.eigenfunction n y)| ≤ CN * t ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hbound⟩ := spectral_heat_native_nash_kernel_upper hd hκ R hR
  refine ⟨κ⁻¹ * C, mul_pos (inv_pos.mpr hκ) hC, ?_⟩
  intro ρ α h s vs hs hb hvar t ht x hx y hy
  have hk := hbound ρ α h s vs hs hb hvar t ht x hx y hy
  have hρ : 0 ≤ ρ y := le_trans hκ.le (h.2.2 y).1
  have hρbound : ρ y ≤ κ⁻¹ := (h.2.2 y).2.1
  have hpow : 0 ≤ t ^ (-(d : ℝ) / 2) := Real.rpow_nonneg ht.le _
  rw [abs_mul, abs_of_nonneg hρ]
  calc
    _ ≤ ρ y * (C * t ^ (-(d : ℝ) / 2)) := mul_le_mul_of_nonneg_left hk hρ
    _ ≤ κ⁻¹ * (C * t ^ (-(d : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hρbound (mul_nonneg hC.le hpow)
    _ = (κ⁻¹ * C) * t ^ (-(d : ℝ) / 2) := by ring

#print axioms spectral_heat_native_nash_density_upper

end EinsteinFull.Calculus
