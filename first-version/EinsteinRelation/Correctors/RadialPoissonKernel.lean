import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import EinsteinRelation.Environment.Basic
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # Compactly supported radial Poisson kernels

Step 1 of Proposition 6.1 (`paper/main.tex` lines 1009-1022) needs the kernels
`K_r = Γ * (θ_r - θ_{2r})` to have compact support. After the change of variables
`x = A^{1/2} z` this reduces to the Newtonian potential of a radial source with zero
integral, which vanishes outside a ball containing the support of the source.

This file proves that statement from an explicit radial ODE, without fundamental
solution theory. For a profile `g : ℝ → ℝ` and a radius `ρ₀ > 0` such that `g = 0` on
`[ρ₀, ∞)` and `∫_0^{ρ₀} g(t) t^{d-1} dt = 0`, put

* `w(s) = s^{1-d} ∫_0^s g(t) t^{d-1} dt` (the radial flux; `w(0) = 0`),
* `u(ρ) = -∫_ρ^{ρ₀} w(s) ds` (the radial potential).

Then `u = 0` on `[ρ₀, ∞)`, `u' = w`, and `u'' + (d-1)/ρ u' = g` on `(0, ∞)`.
The function `U(x) = u(‖x‖)` is a compactly supported `C²` function on `ℝ^d` with
`∑ᵢ ∂ᵢ² U(x) = g(‖x‖)`. Near the origin `g` is assumed constant, which holds for
`φ_r - φ_{2r}` when the radial profile `φ` is constant near `0`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-! ## The radial ODE on `(0, ∞)` -/

/-- The radial mass `∫_0^s g(t) t^{d-1} dt`. -/
noncomputable def radialMass (d : ℕ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..s, g t * t ^ (d - 1)

/-- The radial flux `w(s) = s^{1-d} ∫_0^s g(t) t^{d-1} dt`. The factor `(s^{d-1})⁻¹`
vanishes at `s = 0` when `d ≥ 2`, so `w(0) = 0`. -/
noncomputable def radialFlux (d : ℕ) (g : ℝ → ℝ) (s : ℝ) : ℝ :=
  (s ^ (d - 1))⁻¹ * radialMass d g s

/-- The radial potential `u(ρ) = -∫_ρ^{ρ₀} w(s) ds`. -/
noncomputable def radialPotential (d : ℕ) (g : ℝ → ℝ) (ρ₀ ρ : ℝ) : ℝ :=
  -∫ s in ρ..ρ₀, radialFlux d g s

/-- Real algebra for the derivative of the flux: the two terms of the derivative of
`(Qρ)⁻¹ M` combine into the right-hand side of the radial equation. -/
private theorem flux_deriv_algebra (ρ Q M G n : ℝ) (hρ : ρ ≠ 0) (hQ : Q ≠ 0) :
    -(n * Q) / (Q * ρ) ^ 2 * M + (Q * ρ)⁻¹ * (G * (Q * ρ)) = G - n / ρ * ((Q * ρ)⁻¹ * M) := by
  field_simp <;> ring

/-- Real algebra for the flux bound: `P⁻¹ (M (P s / D)) = M s / D`. -/
private theorem flux_bound_algebra (P s M D : ℝ) (hP : P ≠ 0) :
    P⁻¹ * (M * (P * s / D)) = M * s / D := by
  have h1 : M * (P * s / D) = P * (M * s / D) := by ring
  rw [h1, inv_mul_cancel_left₀ hP]

/-- The power integral `∫_0^s c t^{d-1} dt = c s^d / d` for `d ≥ 2`. -/
theorem integral_const_mul_pow_eq {d : ℕ} (hd : 2 ≤ d) (c s : ℝ) :
    ∫ t in (0 : ℝ)..s, c * t ^ (d - 1) = c * (s ^ d / d) := by
  have hd1 : d - 1 + 1 = d := by omega
  have hdR : ((d - 1 : ℕ) : ℝ) + 1 = (d : ℝ) := by exact_mod_cast hd1
  rw [intervalIntegral.integral_const_mul, integral_pow, hd1, hdR,
    zero_pow (by omega : d ≠ 0), sub_zero]

/-- The radial mass has derivative `g(s) s^{d-1}` at every point, for continuous `g`. -/
theorem radialMass_hasDerivAt {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) (s : ℝ) :
    HasDerivAt (radialMass d g) (g s * s ^ (d - 1)) s := by
  have hcont : Continuous fun t : ℝ => g t * t ^ (d - 1) := hg.mul (continuous_pow (d - 1))
  unfold radialMass
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt

/-- The radial flux is differentiable on `(0, ∞)` with derivative
`g - (d-1) ρ⁻¹ w`, which is the radial equation `u'' + (d-1)/ρ u' = g` for `u' = w`. -/
theorem radialFlux_hasDerivAt {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g) {ρ : ℝ}
    (hρ : 0 < ρ) :
    HasDerivAt (radialFlux d g) (g ρ - ((d : ℝ) - 1) / ρ * radialFlux d g ρ) ρ := by
  have hpow : ρ ^ (d - 1) = ρ ^ (d - 1 - 1) * ρ := by
    rw [← pow_succ]
    congr 1
    omega
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
  have hinv : HasDerivAt (fun s : ℝ => (s ^ (d - 1))⁻¹)
      (-(((d - 1 : ℕ) : ℝ) * ρ ^ (d - 1 - 1)) / (ρ ^ (d - 1)) ^ 2) ρ :=
    (hasDerivAt_pow (d - 1) ρ).inv (pow_ne_zero _ hρ.ne')
  have hflux : HasDerivAt (radialFlux d g)
      (-(((d - 1 : ℕ) : ℝ) * ρ ^ (d - 1 - 1)) / (ρ ^ (d - 1)) ^ 2 * radialMass d g ρ
        + (ρ ^ (d - 1))⁻¹ * (g ρ * ρ ^ (d - 1))) ρ :=
    hinv.mul (radialMass_hasDerivAt hg ρ)
  refine hflux.congr_deriv ?_
  unfold radialFlux
  rw [hcast, hpow]
  exact flux_deriv_algebra ρ _ _ _ _ hρ.ne' (pow_ne_zero _ hρ.ne')

/-- The radial potential is the integral of the flux from `ρ₀` to `r`. -/
theorem radialPotential_eq_integral (d : ℕ) (g : ℝ → ℝ) (ρ₀ r : ℝ) :
    radialPotential d g ρ₀ r = ∫ s in ρ₀..r, radialFlux d g s := by
  unfold radialPotential
  exact (intervalIntegral.integral_symm r ρ₀).symm

/-- The radial potential has derivative `w` at every `ρ > 0`. -/
theorem radialPotential_hasDerivAt {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (hρ : 0 < ρ) :
    HasDerivAt (radialPotential d g ρ₀) (radialFlux d g ρ) ρ := by
  have hint : radialPotential d g ρ₀ = fun r => ∫ s in ρ₀..r, radialFlux d g s := by
    funext r
    exact radialPotential_eq_integral d g ρ₀ r
  have hcontOn : ContinuousOn (radialFlux d g) (Set.uIcc ρ₀ ρ) := by
    intro x hx
    have hxpos : 0 < x := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact (radialFlux_hasDerivAt hd hg hxpos).continuousAt.continuousWithinAt
  have hmeas : StronglyMeasurableAtFilter (radialFlux d g) (nhds ρ) :=
    ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioi 0) isOpen_Ioi
      (fun x hx => (radialFlux_hasDerivAt hd hg (Set.mem_Ioi.mp hx)).continuousAt) ρ
      (Set.mem_Ioi.mpr hρ)
  rw [hint]
  exact intervalIntegral.integral_hasDerivAt_right (ContinuousOn.intervalIntegrable hcontOn)
    hmeas (radialFlux_hasDerivAt hd hg hρ).continuousAt

/-- The radial mass stays zero beyond `ρ₀` when `g` vanishes on `[ρ₀, ∞)` and the mass
on `[0, ρ₀]` is zero. -/
theorem radialMass_eq_zero_of_ge {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {ρ₀ : ℝ}
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0) {s : ℝ}
    (hs : ρ₀ ≤ s) : radialMass d g s = 0 := by
  have hcont : Continuous fun t : ℝ => g t * t ^ (d - 1) := hg.mul (continuous_pow (d - 1))
  have hA : IntervalIntegrable (fun t : ℝ => g t * t ^ (d - 1)) MeasureTheory.volume 0 ρ₀ :=
    hcont.intervalIntegrable 0 ρ₀
  have hB : IntervalIntegrable (fun t : ℝ => g t * t ^ (d - 1)) MeasureTheory.volume ρ₀ s :=
    hcont.intervalIntegrable ρ₀ s
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
  have htail : ∫ t in ρ₀..s, g t * t ^ (d - 1) = 0 := by
    have hcongr : ∫ t in ρ₀..s, g t * t ^ (d - 1) = ∫ _ in ρ₀..s, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hs] at ht
      simp [hzero t ht.1]
    rw [hcongr, intervalIntegral.integral_zero]
  unfold radialMass at hmass ⊢
  rw [← hsplit, hmass, htail, add_zero]

/-- The radial flux vanishes beyond `ρ₀`. -/
theorem radialFlux_eq_zero_of_ge {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {ρ₀ : ℝ}
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0) {s : ℝ}
    (hs : ρ₀ ≤ s) : radialFlux d g s = 0 := by
  unfold radialFlux
  rw [radialMass_eq_zero_of_ge hg hzero hmass hs, mul_zero]

/-- The radial potential vanishes on `[ρ₀, ∞)`. -/
theorem radialPotential_eq_zero_of_ge {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {ρ₀ ρ : ℝ}
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0) (hρ : ρ₀ ≤ ρ) :
    radialPotential d g ρ₀ ρ = 0 := by
  have hcongr : ∫ s in ρ..ρ₀, radialFlux d g s = ∫ _ in ρ..ρ₀, (0 : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have h1 : ρ₀ ≤ t := by
      rw [Set.uIcc_comm, Set.uIcc_of_le hρ] at ht
      exact ht.1
    exact radialFlux_eq_zero_of_ge hg hzero hmass h1
  unfold radialPotential
  rw [hcongr, intervalIntegral.integral_zero, neg_zero]

/-- The radial flux is bounded by `M s / d` when `|g| ≤ M` on `[0, ∞)`. -/
theorem radialFlux_abs_le {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g) {M : ℝ}
    (hM : ∀ t : ℝ, 0 ≤ t → |g t| ≤ M) {s : ℝ} (hs : 0 ≤ s) :
    |radialFlux d g s| ≤ M * s / d := by
  rcases hs.eq_or_lt with h0 | hpos
  · subst h0
    have hd1 : d - 1 ≠ 0 := by omega
    simp [radialFlux, radialMass, hd1]
  · have hPpos : 0 < s ^ (d - 1) := pow_pos hpos _
    have hcont : Continuous fun t : ℝ => g t * t ^ (d - 1) := hg.mul (continuous_pow (d - 1))
    have hcabs : Continuous fun t : ℝ => |g t * t ^ (d - 1)| := continuous_abs.comp hcont
    have hcM : Continuous fun t : ℝ => M * t ^ (d - 1) :=
      continuous_const.mul (continuous_pow (d - 1))
    have hmono : ∫ t in (0 : ℝ)..s, |g t * t ^ (d - 1)|
        ≤ ∫ t in (0 : ℝ)..s, M * t ^ (d - 1) := by
      refine intervalIntegral.integral_mono_on hpos.le (hcabs.intervalIntegrable _ _)
        (hcM.intervalIntegrable _ _) ?_
      intro t ht
      show |g t * t ^ (d - 1)| ≤ M * t ^ (d - 1)
      rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1 (d - 1))]
      exact mul_le_mul_of_nonneg_right (hM t ht.1) (pow_nonneg ht.1 (d - 1))
    have hmass : |radialMass d g s| ≤ M * (s ^ d / d) := by
      unfold radialMass
      calc |∫ t in (0 : ℝ)..s, g t * t ^ (d - 1)|
          ≤ ∫ t in (0 : ℝ)..s, |g t * t ^ (d - 1)| :=
            intervalIntegral.abs_integral_le_integral_abs hpos.le
        _ ≤ ∫ t in (0 : ℝ)..s, M * t ^ (d - 1) := hmono
        _ = M * (s ^ d / d) := integral_const_mul_pow_eq hd M s
    have hsd : s ^ d = s ^ (d - 1) * s := by
      rw [← pow_succ]
      congr 1
      omega
    calc |radialFlux d g s| = (s ^ (d - 1))⁻¹ * |radialMass d g s| := by
          unfold radialFlux
          rw [abs_mul, abs_of_pos (inv_pos.mpr hPpos)]
      _ ≤ (s ^ (d - 1))⁻¹ * (M * (s ^ d / d)) :=
          mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hPpos.le)
      _ = M * s / d := by
          rw [hsd]
          exact flux_bound_algebra _ _ _ _ hPpos.ne'

/-! ## The flat zone at the origin

Near the origin the profile is assumed constant, `g = g(0)` on `[0, ε)`. On this zone the
flux is linear and the potential is a constant plus a multiple of `r²`. -/

/-- On the flat zone the radial mass is `g(0) s^d / d`. -/
theorem radialMass_eq_of_flat {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {ε : ℝ}
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) {s : ℝ} (hs0 : 0 ≤ s) (hsε : s < ε) :
    radialMass d g s = g 0 * (s ^ d / d) := by
  have hcongr : ∫ t in (0 : ℝ)..s, g t * t ^ (d - 1)
      = ∫ t in (0 : ℝ)..s, g 0 * t ^ (d - 1) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hs0] at ht
    simp [hflat t ht.1 (lt_of_le_of_lt ht.2 hsε)]
  unfold radialMass
  rw [hcongr, integral_const_mul_pow_eq hd]

/-- On the flat zone the flux is `g(0) s / d`. -/
theorem radialFlux_eq_linear_of_flat {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {ε : ℝ}
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) {s : ℝ} (hs0 : 0 ≤ s) (hsε : s < ε) :
    radialFlux d g s = g 0 * s / d := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    have hd1 : d - 1 ≠ 0 := by omega
    simp [radialFlux, radialMass, hd1]
  · have hPpos : 0 < s ^ (d - 1) := pow_pos hpos _
    have hsd : s ^ d = s ^ (d - 1) * s := by
      rw [← pow_succ]
      congr 1
      omega
    unfold radialFlux
    rw [radialMass_eq_of_flat hd hflat hs0 hsε, hsd]
    exact flux_bound_algebra _ _ _ _ hPpos.ne'

/-- On the flat zone the potential is `C + g(0) r² / (2d)` for a constant `C`. -/
theorem radialPotential_eq_quadratic_of_flat {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : Continuous g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r < ε →
      radialPotential d g ρ₀ r = C + g 0 * r ^ 2 / (2 * d) := by
  refine ⟨radialPotential d g ρ₀ (ε / 2) - g 0 * (ε / 2) ^ 2 / (2 * d), fun r hr0 hrε => ?_⟩
  have hm : 0 < ε / 2 := by linarith
  have hmem : ∀ s ∈ Set.uIcc (ε / 2) r, 0 ≤ s ∧ s < ε := by
    intro s hs
    rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
  have hcontA : ContinuousOn (radialFlux d g) (Set.uIcc ρ₀ (ε / 2)) := by
    intro x hx
    have hxpos : 0 < x := by
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    exact (radialFlux_hasDerivAt hd hg hxpos).continuousAt.continuousWithinAt
  have hlin : Continuous fun s : ℝ => g 0 / d * s := continuous_const.mul continuous_id
  have hcontB : ContinuousOn (radialFlux d g) (Set.uIcc (ε / 2) r) := by
    refine ContinuousOn.congr hlin.continuousOn ?_
    intro s hs
    obtain ⟨h0, hs'⟩ := hmem s hs
    show radialFlux d g s = g 0 / d * s
    rw [radialFlux_eq_linear_of_flat hd hflat h0 hs']
    ring
  have hIA : IntervalIntegrable (radialFlux d g) MeasureTheory.volume ρ₀ (ε / 2) :=
    ContinuousOn.intervalIntegrable hcontA
  have hIB : IntervalIntegrable (radialFlux d g) MeasureTheory.volume (ε / 2) r :=
    ContinuousOn.intervalIntegrable hcontB
  have hsplit : ∫ s in ρ₀..r, radialFlux d g s
      = (∫ s in ρ₀..(ε / 2), radialFlux d g s) + ∫ s in (ε / 2)..r, radialFlux d g s :=
    (intervalIntegral.integral_add_adjacent_intervals hIA hIB).symm
  have hcongr : ∫ s in (ε / 2)..r, radialFlux d g s = ∫ s in (ε / 2)..r, g 0 / d * s := by
    apply intervalIntegral.integral_congr
    intro s hs
    obtain ⟨h0, hs'⟩ := hmem s hs
    show radialFlux d g s = g 0 / d * s
    rw [radialFlux_eq_linear_of_flat hd hflat h0 hs']
    ring
  have hlinear : ∫ s in (ε / 2)..r, g 0 / d * s = g 0 / d * ((r ^ 2 - (ε / 2) ^ 2) / 2) := by
    rw [intervalIntegral.integral_const_mul, integral_id]
  simp only [radialPotential_eq_integral]
  rw [hsplit, hcongr, hlinear]
  ring

/-! ## Smoothness of the radial potential on `(0, ∞)` -/

/-- The radial mass is `C¹` on the whole line. -/
theorem radialMass_contDiff_one {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiff ℝ 1 (radialMass d g) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun s => (radialMass_hasDerivAt hg s).differentiableAt, ?_⟩
  have hderiv : deriv (radialMass d g) = fun s => g s * s ^ (d - 1) := by
    funext s
    exact (radialMass_hasDerivAt hg s).deriv
  rw [hderiv]
  exact hg.mul (continuous_pow (d - 1))

/-- The radial flux is `C¹` at every `r > 0`. -/
theorem radialFlux_contDiffAt {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ 1 (radialFlux d g) r := by
  unfold radialFlux
  exact ((contDiff_id.pow (d - 1)).contDiffAt.inv (pow_ne_zero _ hr.ne')).mul
    (radialMass_contDiff_one hg).contDiffAt

/-- The radial flux is `C¹` on `(0, ∞)`. -/
theorem radialFlux_contDiffOn {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) :
    ContDiffOn ℝ 1 (radialFlux d g) (Set.Ioi 0) :=
  fun r hr => (radialFlux_contDiffAt hg (Set.mem_Ioi.mp hr)).contDiffWithinAt

/-- The radial potential is `C²` on `(0, ∞)`, since its derivative is the `C¹` flux. -/
theorem radialPotential_contDiffOn {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ContDiffOn ℝ 2 (radialPotential d g ρ₀) (Set.Ioi 0) := by
  refine (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioi).2 ⟨?_, ?_, ?_⟩
  · intro r hr
    exact ((radialPotential_hasDerivAt hd hg hρ₀ (Set.mem_Ioi.mp hr)).differentiableAt
      ).differentiableWithinAt
  · intro h
    exact absurd h WithTop.one_ne_top
  · refine (radialFlux_contDiffOn (d := d) hg).congr ?_
    intro r hr
    exact (radialPotential_hasDerivAt hd hg hρ₀ (Set.mem_Ioi.mp hr)).deriv

/-! ## The radial kernel on `Vec d` -/

/-- The radial kernel `U(x) = u(‖x‖)` on `Vec d`. -/
noncomputable def radialKernel (d : ℕ) (g : ℝ → ℝ) (ρ₀ : ℝ) (x : Vec d) : ℝ :=
  radialPotential d g ρ₀ (euclideanNorm x)

/-- The second partial derivative `∂ᵢ² U(x)` along the coordinate direction `e_i`. -/
noncomputable def secondPartial {d : ℕ} (U : Vec d → ℝ) (i : Fin d) (x : Vec d) : ℝ :=
  fderiv ℝ (fun y => fderiv ℝ U y (unitVector i)) x (unitVector i)

/-- The squared Euclidean norm is the sum of the squared coordinates. -/
theorem euclideanNorm_sq_eq {d : ℕ} (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x := by
  have h : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  unfold euclideanNorm
  exact Real.sq_sqrt h

/-- A nonzero vector has positive squared Euclidean norm. -/
theorem euclideanSq_pos_of_ne_zero {d : ℕ} {x : Vec d} (hx : x ≠ 0) : 0 < euclideanSq x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  have hpos : 0 < x i * x i := mul_self_pos.mpr (by simpa using hi)
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => x j * x j)
    (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))

/-- A nonzero vector has positive Euclidean norm. -/
theorem euclideanNorm_pos_of_ne_zero {d : ℕ} {x : Vec d} (hx : x ≠ 0) :
    0 < euclideanNorm x :=
  Real.sqrt_pos.mpr (euclideanSq_pos_of_ne_zero hx)

/-- The Euclidean norm of the origin vanishes. -/
theorem euclideanNorm_zero_vec (d : ℕ) : euclideanNorm (0 : Vec d) = 0 := by
  unfold euclideanNorm euclideanSq dot
  simp

/-- The Euclidean norm is nonnegative. -/
theorem radialEuclideanNorm_nonneg {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- Each coordinate is bounded by the Euclidean norm. -/
theorem abs_coord_le_euclideanNorm {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  unfold euclideanSq dot
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

/-- The squared Euclidean norm is a polynomial, hence smooth. -/
theorem euclideanSq_contDiff {d : ℕ} (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : Vec d => euclideanSq x) := by
  unfold euclideanSq dot
  exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)

/-- The Euclidean norm is continuous. -/
theorem euclideanNorm_continuous {d : ℕ} : Continuous (fun x : Vec d => euclideanNorm x) :=
  (euclideanSq_contDiff (d := d) 0).continuous.sqrt

/-- The Euclidean norm is smooth away from the origin. -/
theorem euclideanNorm_contDiffAt {d : ℕ} (n : WithTop ℕ∞) {x : Vec d}
    (hx : 0 < euclideanNorm x) : ContDiffAt ℝ n euclideanNorm x := by
  have hS : euclideanSq x ≠ 0 := by
    rw [← euclideanNorm_sq_eq]
    exact pow_ne_zero 2 hx.ne'
  unfold euclideanNorm
  exact (euclideanSq_contDiff (d := d) n).contDiffAt.sqrt hS

/-- Expansion of the squared norm along a coordinate line. -/
theorem euclideanSq_add_smul_unitVector {d : ℕ} (x : Vec d) (i : Fin d) (t : ℝ) :
    euclideanSq (x + t • unitVector i) = euclideanSq x + 2 * x i * t + t ^ 2 := by
  have hsum : ∑ j, x j * unitVector i j = x i := by
    simp [unitVector, Pi.single_apply]
  have hsq : ∑ j, unitVector i j * unitVector i j = 1 := by
    simp [unitVector, Pi.single_apply]
  have hexp : ∀ j, (x + t • unitVector i) j * (x + t • unitVector i) j
      = x j * x j + 2 * t * (x j * unitVector i j)
        + t ^ 2 * (unitVector i j * unitVector i j) := by
    intro j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  show ∑ j, (x + t • unitVector i) j * (x + t • unitVector i) j
    = ∑ j, x j * x j + 2 * x i * t + t ^ 2
  simp only [hexp, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, hsq]
  ring

/-- A quadratic polynomial in `t` has derivative `b` at `0`. -/
theorem hasDerivAt_quadratic_line (a b : ℝ) :
    HasDerivAt (fun t : ℝ => a + b * t + t ^ 2) b 0 := by
  have hc : HasDerivAt (fun _ : ℝ => a) 0 (0 : ℝ) := hasDerivAt_const _ _
  have hid : HasDerivAt (fun t : ℝ => t) 1 (0 : ℝ) := hasDerivAt_id' _
  have h := (hc.add (hid.const_mul b)).add (hasDerivAt_pow 2 (0 : ℝ))
  exact h.congr_deriv (by simp)

/-- The derivative of `f` along the line `t ↦ x + t v` at `0` is `Df(x) v`. -/
theorem hasDerivAt_fderiv_line {d : ℕ} {f : Vec d → ℝ} {x : Vec d} (v : Vec d)
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).smul_const v).const_add x
  exact HasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) (hl := hf.hasFDerivAt) (hf := hline)
    (hy := by simp)

/-- The Euclidean norm along a coordinate line, at a point where it is positive. -/
theorem hasDerivAt_euclideanNorm_line {d : ℕ} {x : Vec d} (hx : 0 < euclideanNorm x)
    (i : Fin d) :
    HasDerivAt (fun t : ℝ => euclideanNorm (x + t • unitVector i))
      (x i / euclideanNorm x) 0 := by
  have hS : euclideanSq x ≠ 0 := by
    rw [← euclideanNorm_sq_eq]
    exact pow_ne_zero 2 hx.ne'
  have hsq := (hasDerivAt_quadratic_line (euclideanSq x) (2 * x i)).sqrt (by simpa using hS)
  have hfun : (fun t : ℝ => euclideanNorm (x + t • unitVector i))
      = fun t : ℝ => Real.sqrt (euclideanSq x + 2 * x i * t + t ^ 2) := by
    funext t
    unfold euclideanNorm
    rw [euclideanSq_add_smul_unitVector]
  rw [hfun]
  refine hsq.congr_deriv ?_
  have h0 : euclideanSq x + 2 * x i * 0 + 0 ^ 2 = euclideanSq x := by ring
  rw [h0]
  unfold euclideanNorm
  exact mul_div_mul_left _ _ two_ne_zero

/-- The explicit flux-times-coordinate-ratio along a coordinate line. -/
theorem hasDerivAt_flux_line {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {x : Vec d} (hx : 0 < euclideanNorm x) (i : Fin d) :
    HasDerivAt (fun t : ℝ => radialFlux d g (euclideanNorm (x + t • unitVector i))
        * ((x + t • unitVector i) i / euclideanNorm (x + t • unitVector i)))
      ((g (euclideanNorm x) - ((d : ℝ) - 1) / euclideanNorm x * radialFlux d g (euclideanNorm x))
          * (x i / euclideanNorm x) * (x i / euclideanNorm x)
        + radialFlux d g (euclideanNorm x)
          * ((1 * euclideanNorm x - x i * (x i / euclideanNorm x)) / euclideanNorm x ^ 2)) 0 := by
  have hA := hasDerivAt_euclideanNorm_line hx i
  have hF := HasDerivAt.comp_of_eq (x := (0 : ℝ)) (hh₂ := radialFlux_hasDerivAt hd hg hx)
    (hh := hA) (hy := by simp)
  have hc : HasDerivAt (fun t : ℝ => (x + t • unitVector i) i) 1 0 := by
    have hfun : (fun t : ℝ => (x + t • unitVector i) i) = fun t : ℝ => x i + t := by
      funext t
      simp [unitVector]
    rw [hfun]
    exact (hasDerivAt_id' _).const_add (x i)
  have hQ : HasDerivAt
      (fun t : ℝ => (x + t • unitVector i) i / euclideanNorm (x + t • unitVector i))
      ((1 * euclideanNorm x - x i * (x i / euclideanNorm x)) / euclideanNorm x ^ 2) 0 := by
    have h := hc.div hA (by simp only [zero_smul, add_zero]; exact hx.ne')
    refine h.congr_deriv ?_
    simp only [zero_smul, add_zero]
  have hprod := hF.mul hQ
  refine hprod.congr_deriv ?_
  simp only [zero_smul, add_zero, Function.comp_apply]

/-- On `{y : ‖y‖ > 0}` the coordinate derivative of the radial kernel is the explicit
flux times `y_i / ‖y‖`. -/
theorem fderiv_radialKernel_unitVector {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {y : Vec d} (hy : 0 < euclideanNorm y) (i : Fin d) :
    fderiv ℝ (radialKernel d g ρ₀) y (unitVector i)
      = radialFlux d g (euclideanNorm y) * (y i / euclideanNorm y) := by
  have hN : DifferentiableAt ℝ euclideanNorm y :=
    (euclideanNorm_contDiffAt 1 hy).differentiableAt le_rfl
  have hdiff : DifferentiableAt ℝ (radialKernel d g ρ₀) y :=
    (radialPotential_hasDerivAt hd hg hρ₀ hy).differentiableAt.comp y hN
  have hy0 : euclideanNorm y = (fun t : ℝ => euclideanNorm (y + t • unitVector i)) 0 := by
    simp
  have hline : HasDerivAt (fun t : ℝ => radialKernel d g ρ₀ (y + t • unitVector i))
      (radialFlux d g (euclideanNorm y) * (y i / euclideanNorm y)) 0 := by
    have h := HasDerivAt.comp_of_eq (x := (0 : ℝ))
      (hh₂ := radialPotential_hasDerivAt hd hg hρ₀ hy) (hh := hasDerivAt_euclideanNorm_line hy i)
      (hy := hy0)
    exact h
  exact (hasDerivAt_fderiv_line (unitVector i) hdiff).unique hline

/-- Algebra for one coordinate of the second derivative. -/
private theorem laplacian_term_algebra (A F r a : ℝ) (hr : r ≠ 0) :
    A * (a / r) * (a / r) + F * ((1 * r - a * (a / r)) / r ^ 2)
      = (A / r ^ 2 - F / r ^ 3) * (a * a) + F / r := by
  (field_simp; ring)

/-- The second partial derivative of the radial kernel at a point with `‖x‖ > 0`. -/
theorem secondPartial_radialKernel_of_pos {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : Continuous g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {x : Vec d} (hx : 0 < euclideanNorm x)
    (i : Fin d) :
    secondPartial (radialKernel d g ρ₀) i x
      = (g (euclideanNorm x) - ((d : ℝ) - 1) / euclideanNorm x * radialFlux d g (euclideanNorm x))
          * (x i / euclideanNorm x) * (x i / euclideanNorm x)
        + radialFlux d g (euclideanNorm x)
          * ((1 * euclideanNorm x - x i * (x i / euclideanNorm x)) / euclideanNorm x ^ 2) := by
  have hopen : IsOpen {y : Vec d | 0 < euclideanNorm y} :=
    isOpen_lt continuous_const euclideanNorm_continuous
  have hFG : (fun y => fderiv ℝ (radialKernel d g ρ₀) y (unitVector i))
      =ᶠ[nhds x] (fun y : Vec d => radialFlux d g (euclideanNorm y) * (y i / euclideanNorm y)) :=
    Filter.eventually_of_mem (hopen.mem_nhds (show x ∈ {y : Vec d | 0 < euclideanNorm y} from hx))
      (fun y hy => fderiv_radialKernel_unitVector hd hg hρ₀ hy i)
  have hflux := radialFlux_contDiffAt (d := d) hg hx
  have hNc : ContDiffAt ℝ 1 euclideanNorm x := euclideanNorm_contDiffAt 1 hx
  have hfN : ContDiffAt ℝ 1 (fun y : Vec d => radialFlux d g (euclideanNorm y)) x :=
    hflux.comp x hNc
  have hyi : ContDiffAt ℝ 1 (fun y : Vec d => y i) x := (contDiff_apply ℝ ℝ i).contDiffAt
  have hdiv : ContDiffAt ℝ 1 (fun y : Vec d => y i / euclideanNorm y) x :=
    hyi.div hNc hx.ne'
  have hGdiff : DifferentiableAt ℝ
      (fun y : Vec d => radialFlux d g (euclideanNorm y) * (y i / euclideanNorm y)) x :=
    (hfN.mul hdiv).differentiableAt le_rfl
  unfold secondPartial
  rw [hFG.fderiv_eq]
  exact (hasDerivAt_fderiv_line (unitVector i) hGdiff).unique
    (hasDerivAt_flux_line hd hg hx i)

/-- The Laplacian of the radial kernel at a point with `‖x‖ > 0` is `g(‖x‖)`. -/
theorem laplacian_radialKernel_of_pos {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {x : Vec d} (hx : 0 < euclideanNorm x) :
    ∑ i, secondPartial (radialKernel d g ρ₀) i x = g (euclideanNorm x) := by
  have hr0 : euclideanNorm x ≠ 0 := hx.ne'
  have hsq : ∑ i, x i * x i = euclideanNorm x ^ 2 := (euclideanNorm_sq_eq x).symm
  simp only [secondPartial_radialKernel_of_pos hd hg hρ₀ hx,
    laplacian_term_algebra _ _ _ _ hr0, Finset.sum_add_distrib, ← Finset.mul_sum,
    hsq, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  (field_simp; ring)

/-- The origin of the flat zone: the kernel equals a constant plus `g(0)‖y‖²/(2d)` on the
ball `{‖y‖ < ε}`. -/
theorem radialKernel_eq_quadratic_of_flat {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ∃ C : ℝ, ∀ z : Vec d, euclideanNorm z < ε →
      radialKernel d g ρ₀ z = C + g 0 * euclideanSq z / (2 * d) := by
  obtain ⟨C, hC⟩ := radialPotential_eq_quadratic_of_flat hd hg hρ₀ hε hflat
  refine ⟨C, fun z hz => ?_⟩
  unfold radialKernel
  rw [hC _ (radialEuclideanNorm_nonneg z) hz, euclideanNorm_sq_eq]

/-- The gradient-free coordinate derivative of the flat-zone quadratic. -/
theorem fderiv_quadratic_unitVector {d : ℕ} (C a : ℝ) (y : Vec d) (i : Fin d) :
    fderiv ℝ (fun z : Vec d => C + a * euclideanSq z / (2 * d)) y (unitVector i)
      = a * (2 * y i) / (2 * d) := by
  have hc : ContDiff ℝ 1 (fun z : Vec d => C + a * euclideanSq z / (2 * d)) :=
    contDiff_const.add ((contDiff_const.mul (euclideanSq_contDiff (d := d) 1)).div_const _)
  have hdiff : DifferentiableAt ℝ (fun z : Vec d => C + a * euclideanSq z / (2 * d)) y :=
    hc.differentiable le_rfl y
  have hline := hasDerivAt_fderiv_line (x := y) (unitVector i) hdiff
  have hexpl : HasDerivAt (fun t : ℝ => C + a * euclideanSq (y + t • unitVector i) / (2 * d))
      (a * (2 * y i) / (2 * d)) 0 := by
    have h := (((hasDerivAt_quadratic_line (euclideanSq y) (2 * y i)).const_mul a).div_const
      (2 * (d : ℝ))).const_add C
    simp only [euclideanSq_add_smul_unitVector]
    exact h
  exact hline.unique hexpl

/-- The second partial derivative of the kernel at the origin. -/
theorem secondPartial_radialKernel_zero {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) (i : Fin d) :
    secondPartial (radialKernel d g ρ₀) i 0 = g 0 * 2 / (2 * d) := by
  obtain ⟨C, hC⟩ := radialKernel_eq_quadratic_of_flat hd hg hρ₀ hε hflat
  have hO : IsOpen {y : Vec d | euclideanNorm y < ε} :=
    isOpen_lt euclideanNorm_continuous continuous_const
  have h0O : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < ε} := by
    show euclideanNorm (0 : Vec d) < ε
    rw [euclideanNorm_zero_vec]
    exact hε
  have hFU : ∀ y ∈ {y : Vec d | euclideanNorm y < ε},
      fderiv ℝ (radialKernel d g ρ₀) y (unitVector i)
        = fderiv ℝ (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) y (unitVector i) := by
    intro y hy
    have heq : radialKernel d g ρ₀
        =ᶠ[nhds y] (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) :=
      Filter.eventually_of_mem (hO.mem_nhds hy) (fun z hz => hC z hz)
    rw [heq.fderiv_eq]
  have hFF : (fun y => fderiv ℝ (radialKernel d g ρ₀) y (unitVector i))
      =ᶠ[nhds 0] (fun y : Vec d =>
        fderiv ℝ (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) y (unitVector i)) :=
    Filter.eventually_of_mem (hO.mem_nhds h0O) (fun y hy => hFU y hy)
  unfold secondPartial
  rw [hFF.fderiv_eq]
  have hfun : (fun y : Vec d =>
      fderiv ℝ (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) y (unitVector i))
      = fun y : Vec d => g 0 * (2 * y i) / (2 * d) := by
    funext y
    exact fderiv_quadratic_unitVector C (g 0) y i
  rw [hfun]
  have hc : ContDiff ℝ 1 (fun y : Vec d => g 0 * (2 * y i) / (2 * d)) :=
    (contDiff_const.mul (contDiff_const.mul (contDiff_apply ℝ ℝ i))).div_const _
  have hcoord : ∀ t : ℝ, (0 + t • unitVector i) i = t := by
    intro t
    simp [unitVector]
  have hexpl : HasDerivAt (fun t : ℝ => g 0 * (2 * (0 + t • unitVector i) i) / (2 * d))
      (g 0 * 2 / (2 * d)) 0 := by
    simp only [hcoord]
    have h := (((hasDerivAt_id' (0 : ℝ)).const_mul (2 : ℝ)).const_mul (g 0)).div_const
      (2 * (d : ℝ))
    exact h.congr_deriv (by ring)
  have hdiff : DifferentiableAt ℝ (fun y : Vec d => g 0 * (2 * y i) / (2 * d)) 0 :=
    hc.differentiable le_rfl 0
  exact (hasDerivAt_fderiv_line (x := (0 : Vec d)) (unitVector i) hdiff).unique hexpl

/-- The radial kernel is smooth near the origin, since it is a quadratic polynomial there. -/
theorem radialKernel_contDiffAt_zero {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ContDiffAt ℝ 2 (radialKernel d g ρ₀) 0 := by
  obtain ⟨C, hC⟩ := radialKernel_eq_quadratic_of_flat hd hg hρ₀ hε hflat
  have hO : IsOpen {y : Vec d | euclideanNorm y < ε} :=
    isOpen_lt euclideanNorm_continuous continuous_const
  have h0O : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < ε} := by
    show euclideanNorm (0 : Vec d) < ε
    rw [euclideanNorm_zero_vec]
    exact hε
  have hEv : radialKernel d g ρ₀
      =ᶠ[nhds 0] (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) :=
    Filter.eventually_of_mem (hO.mem_nhds h0O) (fun z hz => hC z hz)
  have hP : ContDiff ℝ 2 (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) :=
    contDiff_const.add ((contDiff_const.mul (euclideanSq_contDiff (d := d) 2)).div_const _)
  exact hP.contDiffAt.congr_of_eventuallyEq hEv

/-- The radial kernel is `C²` away from the origin. -/
theorem radialKernel_contDiffAt_of_pos {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : Continuous g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {x : Vec d} (hx : 0 < euclideanNorm x) :
    ContDiffAt ℝ 2 (radialKernel d g ρ₀) x :=
  ((radialPotential_contDiffOn hd hg hρ₀).contDiffAt (Ioi_mem_nhds hx)).comp x
    (euclideanNorm_contDiffAt 2 hx)

/-- The radial kernel vanishes outside the closed ball of radius `ρ₀`. -/
theorem radialKernel_eq_zero_of_ge {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {ρ₀ : ℝ}
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0) {x : Vec d}
    (hx : ρ₀ ≤ euclideanNorm x) : radialKernel d g ρ₀ x = 0 :=
  radialPotential_eq_zero_of_ge hg hzero hmass hx

/-- The radial kernel has compact support, contained in the box `[-ρ₀, ρ₀]^d`. -/
theorem radialKernel_hasCompactSupport {d : ℕ} {g : ℝ → ℝ} (hg : Continuous g) {ρ₀ : ℝ}
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0) :
    HasCompactSupport (radialKernel d g ρ₀) := by
  refine HasCompactSupport.intro
    (isCompact_univ_pi fun _ : Fin d => isCompact_Icc (a := -ρ₀) (b := ρ₀)) ?_
  intro x hx
  obtain ⟨i, hi⟩ : ∃ i, x i ∉ Set.Icc (-ρ₀) ρ₀ := by
    by_contra h
    push_neg at h
    exact hx (fun i _ => h i)
  have hlt : ρ₀ < |x i| := by
    by_contra hc
    exact hi (abs_le.mp (not_lt.mp hc))
  exact radialKernel_eq_zero_of_ge hg hzero hmass
    (le_trans hlt.le (abs_coord_le_euclideanNorm x i))

/-- Step 1 of Proposition 6.1 in radial form. For `d ≥ 2` and a profile `g` smooth on `ℝ`
with `g = 0` on `[ρ₀, ∞)`, zero mass `∫_0^{ρ₀} g(t) t^{d-1} dt = 0`, and `g` constant on
`[0, ε)`, the function `U(x) = u(‖x‖)` is `C²`, compactly supported in the closed ball of
radius `ρ₀`, and satisfies `∑ᵢ ∂ᵢ² U(x) = g(‖x‖)`. -/
theorem radialKernel_spec {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0)
    (hmass : radialMass d g ρ₀ = 0) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ContDiff ℝ 2 (radialKernel d g ρ₀) ∧ HasCompactSupport (radialKernel d g ρ₀) ∧
      (∀ x : Vec d, ρ₀ ≤ euclideanNorm x → radialKernel d g ρ₀ x = 0) ∧
      ∀ x : Vec d, ∑ i, secondPartial (radialKernel d g ρ₀) i x = g (euclideanNorm x) := by
  have hgc : Continuous g := hg.continuous
  refine ⟨?_, radialKernel_hasCompactSupport hgc hzero hmass,
    fun x hx => radialKernel_eq_zero_of_ge hgc hzero hmass hx, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      exact radialKernel_contDiffAt_zero hd hgc hρ₀ hε hflat
    · exact radialKernel_contDiffAt_of_pos hd hgc hρ₀ (euclideanNorm_pos_of_ne_zero hx)
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp only [euclideanNorm_zero_vec, secondPartial_radialKernel_zero hd hgc hρ₀ hε hflat]
      have hD : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · exact laplacian_radialKernel_of_pos hd hgc hρ₀ (euclideanNorm_pos_of_ne_zero hx)

/-! ## Scaling

For `r > 0` the profile `t ↦ r^{-d} g(t/r)` produces the kernel `r^{2-d} U(x/r)`: the
rescaled kernel is the radial kernel of the rescaled profile at radius `r ρ₀`. -/

/-- The rescaled profile `t ↦ r^{-d} g(t/r)`. -/
noncomputable def scaledProfile (d : ℕ) (r : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  (r ^ d)⁻¹ * g (t / r)

/-- The rescaled profile is smooth when `g` is. -/
theorem scaledProfile_contDiff {d : ℕ} {r : ℝ} {g : ℝ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledProfile d r g) :=
  contDiff_const.mul (hg.comp (contDiff_id.div_const r))

/-- The rescaled profile vanishes beyond `r ρ₀`. -/
theorem scaledProfile_eq_zero_of_ge {d : ℕ} {r ρ₀ : ℝ} {g : ℝ → ℝ} (hr : 0 < r)
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) {t : ℝ} (ht : r * ρ₀ ≤ t) :
    scaledProfile d r g t = 0 := by
  unfold scaledProfile
  rw [hzero (t / r) ((le_div_iff₀ hr).mpr (by linarith)), mul_zero]

/-- The rescaled profile is constant on `[0, r ε)`. -/
theorem scaledProfile_flat {d : ℕ} {r ε : ℝ} {g : ℝ → ℝ} (hr : 0 < r)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ∀ t : ℝ, 0 ≤ t → t < r * ε → scaledProfile d r g t = scaledProfile d r g 0 := by
  intro t ht0 htε
  unfold scaledProfile
  rw [hflat (t / r) (div_nonneg ht0 hr.le) ((div_lt_iff₀ hr).mpr (by linarith)), zero_div]

/-- The radial mass is invariant under the rescaling `s ↦ r s`. -/
theorem radialMass_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (s : ℝ) : radialMass d (scaledProfile d r g) (r * s) = radialMass d g s := by
  have hr0 : r ≠ 0 := hr.ne'
  have hcomp : ∫ x in (0 : ℝ)..s, scaledProfile d r g (r * x) * (r * x) ^ (d - 1)
      = r⁻¹ • ∫ x in (r * 0)..(r * s), scaledProfile d r g x * x ^ (d - 1) :=
    intervalIntegral.integral_comp_mul_left (fun t : ℝ => scaledProfile d r g t * t ^ (d - 1)) hr0
  have hpt : ∀ x : ℝ, scaledProfile d r g (r * x) * (r * x) ^ (d - 1)
      = (r ^ d)⁻¹ * r ^ (d - 1) * (g x * x ^ (d - 1)) := by
    intro x
    unfold scaledProfile
    rw [mul_div_cancel_left₀ x hr0, mul_pow]
    ring
  have hint : ∫ x in (0 : ℝ)..s, scaledProfile d r g (r * x) * (r * x) ^ (d - 1)
      = (r ^ d)⁻¹ * r ^ (d - 1) * ∫ x in (0 : ℝ)..s, g x * x ^ (d - 1) := by
    simp only [hpt]
    exact intervalIntegral.integral_const_mul _ _
  rw [mul_zero] at hcomp
  have hL : ∫ x in (0 : ℝ)..(r * s), scaledProfile d r g x * x ^ (d - 1)
      = r * ∫ x in (0 : ℝ)..s, scaledProfile d r g (r * x) * (r * x) ^ (d - 1) := by
    rw [hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  have hrd : r ^ d = r ^ (d - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  unfold radialMass
  rw [hL, hint, hrd]
  field_simp <;> ring

/-- The flux scales as `w_r(r s) = r^{1-d} w(s)`. -/
theorem radialFlux_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (s : ℝ) : radialFlux d (scaledProfile d r g) (r * s) = (r ^ (d - 1))⁻¹ * radialFlux d g s := by
  unfold radialFlux
  rw [radialMass_scaledProfile hd hr s, mul_pow, mul_inv]
  ring

/-- The radial potential scales as `u_r(r ρ) = r^{2-d} u(ρ)`. -/
theorem radialPotential_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (ρ₀ ρ : ℝ) :
    radialPotential d (scaledProfile d r g) (r * ρ₀) (r * ρ)
      = (r ^ (d - 2))⁻¹ * radialPotential d g ρ₀ ρ := by
  have hr0 : r ≠ 0 := hr.ne'
  rw [radialPotential_eq_integral, radialPotential_eq_integral]
  have hcomp : ∫ x in ρ₀..ρ, radialFlux d (scaledProfile d r g) (r * x)
      = r⁻¹ • ∫ x in (r * ρ₀)..(r * ρ), radialFlux d (scaledProfile d r g) x :=
    intervalIntegral.integral_comp_mul_left (radialFlux d (scaledProfile d r g)) hr0
  have hflux : ∫ x in ρ₀..ρ, radialFlux d (scaledProfile d r g) (r * x)
      = (r ^ (d - 1))⁻¹ * ∫ x in ρ₀..ρ, radialFlux d g x := by
    simp only [radialFlux_scaledProfile hd hr]
    exact intervalIntegral.integral_const_mul _ _
  have hL : ∫ x in (r * ρ₀)..(r * ρ), radialFlux d (scaledProfile d r g) x
      = r * ∫ x in ρ₀..ρ, radialFlux d (scaledProfile d r g) (r * x) := by
    rw [hcomp, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  have hpow : r ^ (d - 1) = r ^ (d - 2) * r := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hL, hflux, hpow]
  field_simp <;> ring

/-- The rescaled kernel is `r^{2-d} U(x/r)`. -/
theorem radialKernel_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (ρ₀ : ℝ) (x : Vec d) :
    radialKernel d (scaledProfile d r g) (r * ρ₀) x
      = (r ^ (d - 2))⁻¹ * radialKernel d g ρ₀ (r⁻¹ • x) := by
  have hN : euclideanNorm x = r * (r⁻¹ * euclideanNorm x) := by
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
  have key := radialPotential_scaledProfile (g := g) hd hr ρ₀ (r⁻¹ * euclideanNorm x)
  rw [← hN] at key
  unfold radialKernel
  rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
  exact key

/-- The rescaled kernel as a function on `Vec d`. -/
theorem radialKernel_scaledProfile_fun {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ} (hr : 0 < r)
    (ρ₀ : ℝ) :
    radialKernel d (scaledProfile d r g) (r * ρ₀)
      = fun x : Vec d => (r ^ (d - 2))⁻¹ * radialKernel d g ρ₀ (r⁻¹ • x) :=
  funext fun x => radialKernel_scaledProfile hd hr ρ₀ x

/-- `L¹` scaling of the kernel: `‖U_r‖_{L¹} = r² ‖U‖_{L¹}`. -/
theorem integral_abs_radialKernel_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (ρ₀ : ℝ) :
    ∫ x : Vec d, |radialKernel d (scaledProfile d r g) (r * ρ₀) x|
      = r ^ 2 * ∫ x : Vec d, |radialKernel d g ρ₀ x| := by
  have h1 : ∀ x : Vec d, |radialKernel d (scaledProfile d r g) (r * ρ₀) x|
      = (r ^ (d - 2))⁻¹ * |radialKernel d g ρ₀ (r⁻¹ • x)| := by
    intro x
    rw [radialKernel_scaledProfile hd hr, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hr _))]
  have habs : |((r⁻¹) ^ d)⁻¹| = r ^ d := by
    rw [inv_pow, inv_inv, abs_of_pos (pow_pos hr d)]
  have hcomp : ∫ x : Vec d, |radialKernel d g ρ₀ (r⁻¹ • x)|
      = r ^ d * ∫ x : Vec d, |radialKernel d g ρ₀ x| := by
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Vec d))
      (fun y : Vec d => |radialKernel d g ρ₀ y|) r⁻¹
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul, habs] at h
    exact h
  have hdpow : r ^ d = r ^ (d - 2) * r ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  simp only [h1]
  rw [MeasureTheory.integral_const_mul, hcomp, hdpow]
  field_simp <;> ring

/-- `L¹` scaling of the gradient: `‖∇U_r‖_{L¹} = r ‖∇U‖_{L¹}`, with `∇U` the Fréchet
derivative and the norm the operator norm. -/
theorem integral_norm_fderiv_radialKernel_scaledProfile {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    {r : ℝ} (hr : 0 < r) {ρ₀ : ℝ} (hU : ContDiff ℝ 2 (radialKernel d g ρ₀)) :
    ∫ x : Vec d, ‖fderiv ℝ (radialKernel d (scaledProfile d r g) (r * ρ₀)) x‖
      = r * ∫ x : Vec d, ‖fderiv ℝ (radialKernel d g ρ₀) x‖ := by
  have hdiff : Differentiable ℝ (radialKernel d g ρ₀) := hU.differentiable one_le_two
  have hderiv : ∀ x : Vec d, fderiv ℝ (radialKernel d (scaledProfile d r g) (r * ρ₀)) x
      = (r ^ (d - 2))⁻¹ • (r⁻¹ • fderiv ℝ (radialKernel d g ρ₀) (r⁻¹ • x)) := by
    intro x
    rw [radialKernel_scaledProfile_fun hd hr ρ₀]
    have hs : HasFDerivAt (fun y : Vec d => r⁻¹ • y)
        (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
      (hasFDerivAt_id x).const_smul r⁻¹
    have hcomp : HasFDerivAt (fun y : Vec d => (r ^ (d - 2))⁻¹ * radialKernel d g ρ₀ (r⁻¹ • y))
        ((r ^ (d - 2))⁻¹ • ((fderiv ℝ (radialKernel d g ρ₀) (r⁻¹ • x)).comp
          (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)))) x :=
      ((hdiff (r⁻¹ • x)).hasFDerivAt.comp x hs).const_mul _
    rw [hcomp.fderiv]
    congr 1
    ext v
    simp
  have hnorm : ∀ x : Vec d, ‖fderiv ℝ (radialKernel d (scaledProfile d r g) (r * ρ₀)) x‖
      = (r ^ (d - 2))⁻¹ * (r⁻¹ * ‖fderiv ℝ (radialKernel d g ρ₀) (r⁻¹ • x)‖) := by
    intro x
    rw [hderiv x]
    simp only [norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hr (d - 2))), abs_of_pos (inv_pos.mpr hr)]
  have hcomp2 : ∫ x : Vec d, ‖fderiv ℝ (radialKernel d g ρ₀) (r⁻¹ • x)‖
      = r ^ d * ∫ x : Vec d, ‖fderiv ℝ (radialKernel d g ρ₀) x‖ := by
    have habs : |((r⁻¹) ^ d)⁻¹| = r ^ d := by
      rw [inv_pow, inv_inv, abs_of_pos (pow_pos hr d)]
    have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure (Vec d))
      (fun y : Vec d => ‖fderiv ℝ (radialKernel d g ρ₀) y‖) r⁻¹
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, smul_eq_mul, habs] at h
    exact h
  have hdpow : r ^ d = r ^ (d - 2) * r ^ 2 := by
    rw [← pow_add]
    congr 1
    omega
  simp only [hnorm]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hcomp2, hdpow]
  field_simp <;> ring

/-- Scaling of the radial kernel (Step 2 of Proposition 6.1). For `r > 0`, the rescaled kernel
`U_r(x) = r^{2-d} U(x/r)` is the radial kernel of the profile `r^{-d} g(·/r)` at radius `r ρ₀`.
It solves `∑ᵢ ∂ᵢ² U_r(x) = r^{-d} g(‖x‖/r)`, and its `L¹` norms satisfy
`‖U_r‖_{L¹} = r² ‖U‖_{L¹}` and `‖∇U_r‖_{L¹} = r ‖∇U‖_{L¹}`. -/
theorem radialKernel_scaled_spec {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0)
    (hmass : radialMass d g ρ₀ = 0) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) {r : ℝ} (hr : 0 < r) :
    (∀ x : Vec d, ∑ i, secondPartial (radialKernel d (scaledProfile d r g) (r * ρ₀)) i x
        = (r ^ d)⁻¹ * g (euclideanNorm x / r)) ∧
      (∫ x : Vec d, |radialKernel d (scaledProfile d r g) (r * ρ₀) x|
        = r ^ 2 * ∫ x : Vec d, |radialKernel d g ρ₀ x|) ∧
      (∫ x : Vec d, ‖fderiv ℝ (radialKernel d (scaledProfile d r g) (r * ρ₀)) x‖
        = r * ∫ x : Vec d, ‖fderiv ℝ (radialKernel d g ρ₀) x‖) := by
  have hmass' : radialMass d (scaledProfile d r g) (r * ρ₀) = 0 :=
    (radialMass_scaledProfile hd hr ρ₀).trans hmass
  have hspec := radialKernel_spec hd (scaledProfile_contDiff hg) (mul_pos hr hρ₀)
    (fun t ht => scaledProfile_eq_zero_of_ge hr hzero ht) hmass' (mul_pos hr hε)
    (scaledProfile_flat hr hflat)
  have hU := (radialKernel_spec hd hg hρ₀ hzero hmass hε hflat).1
  exact ⟨fun x => hspec.2.2.2 x, integral_abs_radialKernel_scaledProfile hd hr ρ₀,
    integral_norm_fderiv_radialKernel_scaledProfile hd hr hU⟩

end EinsteinRelation.Correctors
