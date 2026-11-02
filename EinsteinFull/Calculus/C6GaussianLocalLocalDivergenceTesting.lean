import EinsteinFull.Calculus.C6GaussianLocalDivergenceTesting
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
theorem physical_gaussian_locally_h1_divergence_testing
    {d : ℕ} (r : ℝ) (hr : 0 < r)
    (P : Fin d → Vec d → ℂ) (q v : Vec d → ℂ) (H : Fin d → Vec d → ℂ)
    (hdivre : HasWeakDivergence Set.univ (fun x j => (P j x).re) (fun x => (q x).re))
    (hdivim : HasWeakDivergence Set.univ (fun x j => (P j x).im) (fun x => (q x).im))
    (hvre : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (v x).re) (fun x => (H j x).re))
    (hvim : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (v x).im) (fun x => (H j x).im))
    (hP : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * P j x) 2 volume)
    (hq : MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * q x) 2 volume)
    (hv : MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * v x) 2 volume)
    (hH : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*r)) : ℂ) * H j x) 2 volume) :
    (∫ x : Vec d, (Real.exp (-euclideanSq x/r) : ℂ) * q x * v x) =
      -(∫ x : Vec d, ∑ j,
        P j x * ((Real.exp (-euclideanSq x/r) : ℂ) * H j x +
          ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) * v x)) := by
  classical
  have hscale : 2 * (2 * r) = 4 * r := by ring
  have hr' : 0 < 2 * r := mul_pos (by norm_num) hr
  obtain ⟨u, K, hu, hueq, hKeq⟩ := physical_gaussian_local_h1_realization
    (2*r) hr' v H hvre hvim (by simpa only [hscale] using hv)
    (fun j => by simpa only [hscale] using hH j)
  have htest := physical_gaussian_local_divergence_testing (2*r) hr' P q
    hdivre hdivim (fun j => by simpa only [hscale] using hP j)
    (by simpa only [hscale] using hq) u K hu
  have hw (x : Vec d) :
      (Real.exp (-euclideanSq x / (2*r)) : ℂ) *
        (Real.exp (-euclideanSq x / (2*r)) : ℂ) =
      (Real.exp (-euclideanSq x / r) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    field_simp
    ring
  have hd (x : Vec d) (j : Fin d) :
      (Real.exp (-euclideanSq x / (2*r)) : ℂ) *
          ((-2*x j/(2*r)*Real.exp (-euclideanSq x/(2*r)) : ℝ) : ℂ) +
        ((-2*x j/(2*r)*Real.exp (-euclideanSq x/(2*r)) : ℝ) : ℂ) *
          (Real.exp (-euclideanSq x / (2*r)) : ℂ) =
      ((-2*x j/r*Real.exp (-euclideanSq x/r) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_neg,
      Complex.ofReal_ofNat]
    calc
      _ = ((-2 : ℂ) * (x j : ℂ) / ((2 : ℂ) * (r : ℂ)) +
          (-2 : ℂ) * (x j : ℂ) / ((2 : ℂ) * (r : ℂ))) *
          ((Real.exp (-euclideanSq x/(2*r)) : ℂ) *
            (Real.exp (-euclideanSq x/(2*r)) : ℂ)) := by ring
      _ = _ := by
        rw [hw]
        congr 1
        field_simp
        ring
  calc
    _ = (∫ x : Vec d, (Real.exp (-euclideanSq x/(2*r)) : ℂ) * q x * u x) := by
      apply integral_congr_ae
      filter_upwards [hueq] with x hx
      rw [hx]
      linear_combination -(q x * v x) * hw x
    _ = _ := htest
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hueq, ae_all_iff.mpr hKeq] with x hx hKx
      apply Finset.sum_congr rfl
      intro j _
      rw [hx, hKx j]
      congr 1
      linear_combination H j x * hw x + v x * hd x j
end EinsteinFull.Blueprint
