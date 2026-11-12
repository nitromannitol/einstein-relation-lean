import EinsteinRelation.Correctors.RadialPoissonKernel
import EinsteinRelation.Correctors.KernelDerivativeScaling

/-! # Smoothness of the compact radial Poisson kernel

Source: `paper/main.tex:1009–1036`, Steps 1–2 of Proposition 6.1.
The explicit radial ODE construction is smooth to every finite order when its
source profile is smooth and constant near the origin. In particular, its
fourth derivatives can be used in the heat-transfer estimates.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The radial mass of a smooth profile is smooth on the whole real line
(`paper/main.tex:1009–1018`). -/
theorem radialMass_contDiff {d : ℕ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    ContDiff ℝ (⊤ : ℕ∞) (radialMass d g) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun s => (radialMass_hasDerivAt hg.continuous s).differentiableAt, ?_⟩
  have hderiv : deriv (radialMass d g) = fun s => g s * s ^ (d - 1) :=
    funext fun s => (radialMass_hasDerivAt hg.continuous s).deriv
  rw [hderiv]
  exact hg.mul (contDiff_id.pow (d - 1))

/-- Away from zero the radial flux of a smooth profile is smooth
(`paper/main.tex:1009–1018`). -/
theorem radialFlux_contDiffAt_infty {d : ℕ} {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {r : ℝ} (hr : 0 < r) :
    ContDiffAt ℝ (⊤ : ℕ∞) (radialFlux d g) r := by
  unfold radialFlux
  exact ((contDiff_id.pow (d - 1)).contDiffAt.inv (pow_ne_zero _ hr.ne')).mul
    (radialMass_contDiff hg).contDiffAt

/-- The radial potential is smooth on the positive half-line
(`paper/main.tex:1009–1018`). -/
theorem radialPotential_contDiffOn_infty {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialPotential d g ρ₀) (Set.Ioi 0) := by
  apply (contDiffOn_infty_iff_deriv_of_isOpen isOpen_Ioi).mpr
  refine ⟨fun r hr =>
    (radialPotential_hasDerivAt hd hg.continuous hρ₀ hr).differentiableAt.differentiableWithinAt,
    ?_⟩
  have hw : ContDiffOn ℝ (⊤ : ℕ∞) (radialFlux d g) (Set.Ioi 0) :=
    fun r hr => (radialFlux_contDiffAt_infty hg hr).contDiffWithinAt
  exact hw.congr fun r hr => (radialPotential_hasDerivAt hd hg.continuous hρ₀ hr).deriv

/-- The flat source profile makes the radial kernel a quadratic polynomial near
zero, so it is smooth there (`paper/main.tex:1009–1018`). -/
theorem radialKernel_contDiffAt_zero_infty {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : Continuous g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) (radialKernel d g ρ₀) 0 := by
  obtain ⟨C, hC⟩ := radialKernel_eq_quadratic_of_flat hd hg hρ₀ hε hflat
  have hO : IsOpen {y : Vec d | euclideanNorm y < ε} :=
    isOpen_lt euclideanNorm_continuous continuous_const
  have h0O : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < ε} := by
    simpa only [Set.mem_setOf_eq, euclideanNorm_zero_vec] using hε
  have hEv : radialKernel d g ρ₀
      =ᶠ[nhds 0] (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) :=
    Filter.eventually_of_mem (hO.mem_nhds h0O) (fun z hz => hC z hz)
  have hP : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec d => C + g 0 * euclideanSq z / (2 * d)) :=
    contDiff_const.add ((contDiff_const.mul
      (euclideanSq_contDiff (d := d) (⊤ : ℕ∞))).div_const _)
  exact hP.contDiffAt.congr_of_eventuallyEq hEv

/-- The radial Poisson kernel is smooth to every finite order, including across
the origin (`paper/main.tex:1009–1018`). -/
theorem radialKernel_contDiff {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {ε : ℝ} (hε : 0 < ε)
    (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0) :
    ContDiff ℝ (⊤ : ℕ∞) (radialKernel d g ρ₀) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    exact radialKernel_contDiffAt_zero_infty hd hg.continuous hρ₀ hε hflat
  · have hpos := euclideanNorm_pos_of_ne_zero hx
    exact ((radialPotential_contDiffOn_infty hd hg hρ₀).contDiffAt
      (Ioi_mem_nhds hpos)).comp x (euclideanNorm_contDiffAt (⊤ : ℕ∞) hpos)

/-- All derivative orders in the kernel bound, with the constant fixed before
the scale (`paper/main.tex:1015–1018`). -/
theorem radialKernel_scaled_derivative_bounds {d : ℕ} (hd : 2 ≤ d) {g : ℝ → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀)
    (hzero : ∀ t : ℝ, ρ₀ ≤ t → g t = 0) (hmass : radialMass d g ρ₀ = 0)
    {ε : ℝ} (hε : 0 < ε) (hflat : ∀ t : ℝ, 0 ≤ t → t < ε → g t = g 0)
    (cs : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordinateIterate cs
        (radialKernel d (scaledProfile d r g) (r * ρ₀))) volume ∧
      (∫ x : Vec d, |coordinateIterate cs
        (radialKernel d (scaledProfile d r g) (r * ρ₀)) x|) =
          C * (r ^ 2 / r ^ cs.length) := by
  have hU := radialKernel_contDiff hd hg hρ₀ hε hflat
  refine ⟨∫ x : Vec d, |coordinateIterate cs (radialKernel d g ρ₀) x|,
    integral_nonneg fun x => abs_nonneg _, ?_⟩
  intro r hr
  have hscaled := radialKernel_contDiff hd (scaledProfile_contDiff (d := d) hg) (mul_pos hr hρ₀)
    (mul_pos hr hε) (scaledProfile_flat (d := d) hr hflat)
  have hcompact := radialKernel_hasCompactSupport (scaledProfile_contDiff (d := d) hg).continuous
    (fun t ht => scaledProfile_eq_zero_of_ge hr hzero ht)
    ((radialMass_scaledProfile hd hr ρ₀).trans hmass)
  refine ⟨KernelCalculus.integrable_coordinateIterate hscaled hcompact cs, ?_⟩
  rw [radialKernel_scaledProfile_fun hd hr ρ₀,
    KernelCalculus.integral_abs_coordinateIterate_scaled hU hd hr, mul_comm]

end EinsteinRelation.Correctors
