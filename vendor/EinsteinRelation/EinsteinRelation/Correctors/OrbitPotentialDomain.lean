import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Calculus.HorizontalTranslationLp
import EinsteinRelation.Calculus.Generator
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Environment.ReductionEmbedding
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! # Orbit potentials as the potential-gradient domain

This file proves the orbit-potential characterization of the closed stationary potential-gradient
domain `correctorPotentialDomain`. A bounded measurable stationary field whose translation orbits
are gradients of uniformly bounded `C¹` potentials has a reduced `L²` representative in that
domain.

The proof is constructive. For a bounded smooth unit bump `ρ` and a scale `R`, the averaged
potential `ω ↦ ∫ ρ(z) Φ_ω(R z) dz`, where `Φ_ω` is the orbit potential normalized at the origin,
has horizontal derivatives equal to the `ρ`-average of the orbit gradient minus the gradient. The
`ρ`-average of the orbit gradient tends to zero in `L²`, by integrating the derivative of the bounded
potential against the spreading bump. -/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Correctors

noncomputable section

/-! ### Coordinate and dot-product bounds -/

private theorem orbit_abs_coord_le {d : ℕ} (g : Vec d) {c : ℝ} (hg : euclideanNorm g ≤ c)
    (i : Fin d) : |g i| ≤ c := by
  refine le_trans ?_ hg
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  unfold euclideanSq dot
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)

private theorem orbit_abs_dot_le {d : ℕ} (y g : Vec d) {c : ℝ} (hg : ∀ i, |g i| ≤ c) :
    |dot y g| ≤ (∑ i, |y i|) * c := by
  unfold dot
  calc |∑ i, y i * g i| ≤ ∑ i, |y i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |y i| * |g i| := by simp only [abs_mul]
    _ ≤ ∑ i, |y i| * c :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hg i) (abs_nonneg _)
    _ = (∑ i, |y i|) * c := by rw [Finset.sum_mul]

private theorem abs_inv_mul_le_of_abs_le {t X C : ℝ} (ht : t ≠ 0) (h : |X| ≤ C * |t|) :
    |t⁻¹ * X| ≤ C := by
  rw [abs_mul, abs_inv, inv_mul_le_iff₀ (abs_pos.mpr ht), mul_comm]
  exact h

/-! ### The orbit potential along rays -/

/-- The orbit gradient `G` integrated along the segment from the origin to `y`, read at the
translated environment `ω`. For an orbit whose gradient is `G`, this is the potential
`φ y - φ 0`. -/
def orbitRayPotential {d : ℕ} (G : FieldPair d → Vec d) (ω : FieldPair d) (y : Vec d) : ℝ :=
  ∫ u in (0 : ℝ)..1, dot y (G (translate (u • y) ω))

private theorem orbitRayPotential_zero {d : ℕ} (G : FieldPair d → Vec d) (ω : FieldPair d) :
    orbitRayPotential G ω 0 = 0 := by
  simp [orbitRayPotential, dot]

private theorem fderiv_apply_eq_dot_gradient {d : ℕ} (ψ : Vec d → ℝ) (x v : Vec d) :
    fderiv ℝ ψ x v = dot v (gradient ψ x) := by
  have hv : v = ∑ i, v i • unitVector i := by
    ext j
    simp [unitVector, Pi.single_apply]
  calc fderiv ℝ ψ x v = fderiv ℝ ψ x (∑ i, v i • unitVector i) := congrArg (fderiv ℝ ψ x) hv
    _ = ∑ i, v i * fderiv ℝ ψ x (unitVector i) := by
      simp [map_sum, smul_eq_mul]
    _ = dot v (gradient ψ x) := by
      simp [dot, gradient, coordinateDerivative]

private theorem hasDerivAt_ray {d : ℕ} {ψ : Vec d → ℝ} (hψ : Differentiable ℝ ψ) (y : Vec d)
    (u : ℝ) : HasDerivAt (fun u : ℝ => ψ (u • y)) (fderiv ℝ ψ (u • y) y) u := by
  have h1 : HasDerivAt (fun u : ℝ => u • y) y u := by
    simpa using (hasDerivAt_id' u).smul_const y
  exact (hψ (u • y)).hasFDerivAt.comp_hasDerivAt u h1

private theorem integral_ray_fderiv {d : ℕ} {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (y : Vec d) :
    ∫ u in (0 : ℝ)..1, fderiv ℝ ψ (u • y) y = ψ y - ψ 0 := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hcont : Continuous (fun u : ℝ => fderiv ℝ ψ (u • y) y) :=
    ((hψ.continuous_fderiv (by norm_num)).comp (continuous_id.smul continuous_const)).clm_apply
      continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun u : ℝ => ψ (u • y)) (f' := fun u : ℝ => fderiv ℝ ψ (u • y) y)
    (fun u _ => hasDerivAt_ray hd y u) (hcont.intervalIntegrable 0 1)
  simpa using hFTC

/-- A `C¹` potential of the orbit gradient equals the orbit ray potential up to its value at `0`. -/
private theorem orbitRayPotential_eq_sub {d : ℕ} {G : FieldPair d → Vec d} {ω : FieldPair d}
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hgrad : ∀ x, gradient ψ x = G (translate x ω))
    (y : Vec d) : orbitRayPotential G ω y = ψ y - ψ 0 := by
  rw [← integral_ray_fderiv hψ y]
  unfold orbitRayPotential
  apply intervalIntegral.integral_congr
  intro u _
  show dot y (G (translate (u • y) ω)) = fderiv ℝ ψ (u • y) y
  rw [fderiv_apply_eq_dot_gradient, hgrad]

private theorem orbitRayPotential_translate {d : ℕ} {G : FieldPair d → Vec d} {ω : FieldPair d}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hgrad : ∀ x, gradient φ x = G (translate x ω))
    (s y : Vec d) :
    orbitRayPotential G (translate s ω) y =
      orbitRayPotential G ω (y + s) - orbitRayPotential G ω s := by
  have hψ : ContDiff ℝ 1 (fun z : Vec d => φ (z + s)) := hφ.comp (contDiff_id.add contDiff_const)
  have hgrad' : ∀ z, gradient (fun z : Vec d => φ (z + s)) z = G (translate z (translate s ω)) := by
    intro z
    rw [translate_add, ← hgrad]
    have hD : fderiv ℝ (fun z : Vec d => φ (z + s)) z = fderiv ℝ φ (z + s) :=
      fderiv_comp_add_right s
    funext i
    show fderiv ℝ (fun z : Vec d => φ (z + s)) z (unitVector i) =
      fderiv ℝ φ (z + s) (unitVector i)
    rw [hD]
  rw [orbitRayPotential_eq_sub hψ hgrad' y, orbitRayPotential_eq_sub hφ hgrad (y + s),
    orbitRayPotential_eq_sub hφ hgrad s]
  simp only [zero_add]
  ring

private theorem continuous_orbitRayPotential {d : ℕ} {G : FieldPair d → Vec d} {ω : FieldPair d}
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ) (hgrad : ∀ x, gradient φ x = G (translate x ω)) :
    Continuous (fun y => orbitRayPotential G ω y) := by
  have h : (fun y => orbitRayPotential G ω y) = fun y => φ y - φ 0 := by
    funext y
    exact orbitRayPotential_eq_sub hφ hgrad y
  rw [h]
  exact hφ.continuous.sub continuous_const

private theorem continuous_orbitRayPotential_shift {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) (R : ℝ) (c : Vec d) :
    Continuous (fun z : Vec d => orbitRayPotential G ω (R • z + c)) :=
  (continuous_orbitRayPotential hφ hgrad).comp ((continuous_const_smul R).add continuous_const)

private theorem hasDerivAt_line {d : ℕ} {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ) (y v : Vec d)
    (u : ℝ) : HasDerivAt (fun u : ℝ => φ (y + u • v)) (fderiv ℝ φ (y + u • v) v) u := by
  have h1 : HasDerivAt (fun u : ℝ => y + u • v) v u := by
    simpa using ((hasDerivAt_id' u).smul_const v).const_add y
  exact (hφ (y + u • v)).hasFDerivAt.comp_hasDerivAt u h1

private theorem abs_sub_le_of_hasDerivAt_bound {g g' : ℝ → ℝ} {C : ℝ}
    (hg : ∀ u, HasDerivAt g (g' u) u) (hb : ∀ u, |g' u| ≤ C) (s : ℝ) :
    |g s - g 0| ≤ C * |s| := by
  have h : ‖g s - g 0‖ ≤ C * ‖s - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun u _ => (hg u).differentiableAt)
      (fun u _ => by rw [(hg u).deriv, Real.norm_eq_abs]; exact hb u)
      convex_univ (Set.mem_univ 0) (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using h

/-- Lipschitz control of the orbit ray potential along a coordinate direction. -/
private theorem abs_orbitRayPotential_line_sub_le {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) {C : ℝ} (i : Fin d)
    (hb : ∀ x, |G (translate x ω) i| ≤ C) (y : Vec d) (s : ℝ) :
    |orbitRayPotential G ω (y + s • unitVector i) - orbitRayPotential G ω y| ≤ C * |s| := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hder : ∀ u : ℝ, |fderiv ℝ φ (y + u • unitVector i) (unitVector i)| ≤ C := by
    intro u
    have h := hb (y + u • unitVector i)
    rw [← hgrad] at h
    exact h
  have key := abs_sub_le_of_hasDerivAt_bound
    (g := fun u : ℝ => φ (y + u • unitVector i))
    (g' := fun u : ℝ => fderiv ℝ φ (y + u • unitVector i) (unitVector i)) (C := C)
    (fun u => hasDerivAt_line hd y (unitVector i) u) hder s
  rw [orbitRayPotential_eq_sub hφ hgrad (y + s • unitVector i),
    orbitRayPotential_eq_sub hφ hgrad y]
  simp only [zero_smul, add_zero] at key
  have e : φ (y + s • unitVector i) - φ 0 - (φ y - φ 0) = φ (y + s • unitVector i) - φ y := by
    ring
  rw [e]
  exact key

private theorem abs_orbitRayPotential_axis_le {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) {C : ℝ} (i : Fin d)
    (hb : ∀ x, |G (translate x ω) i| ≤ C) (t : ℝ) :
    |orbitRayPotential G ω (t • unitVector i)| ≤ C * |t| := by
  have h := abs_orbitRayPotential_line_sub_le hφ hgrad i hb 0 t
  rw [zero_add, orbitRayPotential_zero, sub_zero] at h
  exact h

/-- The orbit gradient at a point is the slope of the orbit ray potential along a coordinate. -/
private theorem tendsto_orbitRayPotential_slope {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) (i : Fin d) (y : Vec d) :
    Tendsto (fun t : ℝ => t⁻¹ * (orbitRayPotential G ω (y + t • unitVector i) -
        orbitRayPotential G ω y)) (𝓝[≠] 0) (𝓝 (G (translate y ω) i)) := by
  have hd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hfun : (fun s : ℝ => orbitRayPotential G ω (y + s • unitVector i)) =
      fun s : ℝ => φ (y + s • unitVector i) - φ 0 := by
    funext s
    exact orbitRayPotential_eq_sub hφ hgrad _
  have hder : fderiv ℝ φ (y + (0 : ℝ) • unitVector i) (unitVector i) = G (translate y ω) i := by
    rw [zero_smul, add_zero, ← hgrad y]
    rfl
  have hD : HasDerivAt (fun s : ℝ => orbitRayPotential G ω (y + s • unitVector i))
      (G (translate y ω) i) 0 := by
    rw [hfun, ← hder]
    exact (hasDerivAt_line hd y (unitVector i) 0).sub_const (φ 0)
  refine hD.tendsto_slope_zero.congr' (Eventually.of_forall fun t => ?_)
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]

/-! ### Measurability of the orbit potential and of its bump averages -/

private theorem measurable_orbitRayPotential {d : ℕ} {G : FieldPair d → Vec d}
    (hG : Measurable G) :
    Measurable (fun p : FieldPair d × Vec d => orbitRayPotential G p.1 p.2) := by
  have hc : Continuous (fun q : (FieldPair d × Vec d) × ℝ => translate (q.2 • q.1.2) q.1.1) :=
    Probability.continuous_translate.comp
      ((continuous_snd.smul (continuous_snd.comp continuous_fst)).prodMk
        (continuous_fst.comp continuous_fst))
  have hGm : Measurable (fun q : (FieldPair d × Vec d) × ℝ => G (translate (q.2 • q.1.2) q.1.1)) :=
    hG.comp hc.measurable
  have hdot : Measurable (fun q : (FieldPair d × Vec d) × ℝ =>
      dot q.1.2 (G (translate (q.2 • q.1.2) q.1.1))) := by
    unfold dot
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_fst)).mul
        ((measurable_pi_apply i).comp hGm)
  have hS := hdot.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
  have heq : (fun p : FieldPair d × Vec d => orbitRayPotential G p.1 p.2) =
      fun x => ∫ u, dot x.2 (G (translate (u • x.2) x.1)) ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    funext x
    unfold orbitRayPotential
    rw [intervalIntegral.integral_of_le zero_le_one]
  rw [heq]
  exact hS.measurable

private theorem measurable_smoothedPotential_aux {d : ℕ} {G : FieldPair d → Vec d}
    (hG : Measurable G) {ρ : Vec d → ℝ} (hρ : Continuous ρ) (R : ℝ) :
    Measurable (fun ω : FieldPair d => ∫ z, ρ z * orbitRayPotential G ω (R • z)) := by
  have hjoint : Measurable (fun q : FieldPair d × Vec d =>
      ρ q.2 * orbitRayPotential G q.1 (R • q.2)) :=
    (hρ.measurable.comp measurable_snd).mul
      ((measurable_orbitRayPotential hG).comp
        (measurable_fst.prodMk ((continuous_const_smul R).measurable.comp measurable_snd)))
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

private theorem measurable_coordinateAvg {d : ℕ} {G : FieldPair d → Vec d} (hG : Measurable G)
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (R : ℝ) (i : Fin d) :
    Measurable (fun ω : FieldPair d => ∫ z, ρ z * G (translate (R • z) ω) i) := by
  have hc : Continuous (fun q : FieldPair d × Vec d => translate (R • q.2) q.1) :=
    Probability.continuous_translate.comp
      (((continuous_const_smul R).comp continuous_snd).prodMk continuous_fst)
  have hjoint : Measurable (fun q : FieldPair d × Vec d =>
      ρ q.2 * G (translate (R • q.2) q.1) i) :=
    (hρ.measurable.comp measurable_snd).mul
      ((measurable_pi_apply i).comp (hG.comp hc.measurable))
  exact hjoint.stronglyMeasurable.integral_prod_right'.measurable

/-! ### The smoothed potential and its bounds -/

/-- The bump-smoothed orbit potential at scale `R`. -/
def smoothedPotential {d : ℕ} (G : FieldPair d → Vec d) (ρ : Vec d → ℝ) (R : ℝ)
    (ω : FieldPair d) : ℝ :=
  ∫ z, ρ z * orbitRayPotential G ω (R • z)

/-- A uniform bound for the smoothed potential, with the constant `1/4` for the gradient. -/
def smoothedBound {d : ℕ} (ρ : Vec d → ℝ) (R : ℝ) : ℝ :=
  ∫ z, ρ z * ((∑ i, |(R • z) i|) * (1 / 4))

private theorem integrable_mul_cs_right {d : ℕ} {A B : Vec d → ℝ} (hA : Continuous A)
    (hB : Continuous B) (hBc : HasCompactSupport B) : Integrable (fun z => A z * B z) :=
  (hA.mul hB).integrable_of_hasCompactSupport (hBc.mul_left (f := A))

private theorem integrable_mul_cs_left {d : ℕ} {A B : Vec d → ℝ} (hA : Continuous A)
    (hAc : HasCompactSupport A) (hB : Continuous B) : Integrable (fun z => A z * B z) :=
  (hA.mul hB).integrable_of_hasCompactSupport (hAc.mul_right (f' := B))

private theorem abs_orbitRayPotential_le {d : ℕ} (G : FieldPair d → Vec d) {c : ℝ}
    (hG : ∀ ω i, |G ω i| ≤ c) (ω : FieldPair d) (y : Vec d) :
    |orbitRayPotential G ω y| ≤ (∑ i, |y i|) * c := by
  unfold orbitRayPotential
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (C := (∑ i, |y i|) * c) (f := fun u : ℝ => dot y (G (translate (u • y) ω)))
    (fun u _ => by
      rw [Real.norm_eq_abs]
      exact orbit_abs_dot_le y _ (fun i => hG _ i))
  simpa [Real.norm_eq_abs] using h

private theorem continuous_abs_coord_smul {d : ℕ} (R : ℝ) (i : Fin d) :
    Continuous (fun z : Vec d => |(R • z) i|) := by
  have hR : Continuous (fun z : Vec d => R • z) := continuous_const_smul R
  exact ((continuous_apply i).comp hR).abs

private theorem abs_smoothedPotential_le {d : ℕ} (G : FieldPair d → Vec d)
    {ρ : Vec d → ℝ} (hρC : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hρnn : ∀ z, 0 ≤ ρ z) (hG : ∀ ω i, |G ω i| ≤ 1 / 4) (R : ℝ) (ω : FieldPair d) :
    |smoothedPotential G ρ R ω| ≤ smoothedBound ρ R := by
  have hA : Continuous (fun z : Vec d => (∑ i, |(R • z) i|) * (1 / 4)) :=
    (continuous_finset_sum _ fun i _ => continuous_abs_coord_smul R i).mul continuous_const
  have hint := integrable_mul_cs_left hρC hρc hA
  have hpt : ∀ z, ‖ρ z * orbitRayPotential G ω (R • z)‖ ≤
      ρ z * ((∑ i, |(R • z) i|) * (1 / 4)) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn z)]
    exact mul_le_mul_of_nonneg_left (abs_orbitRayPotential_le G hG ω (R • z)) (hρnn z)
  have h := norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
  unfold smoothedPotential smoothedBound
  rw [Real.norm_eq_abs] at h
  exact h

/-- The bump average of the orbit gradient is bounded by `1/4`. -/
private theorem abs_coordAvg_le {d : ℕ} {G : FieldPair d → Vec d} {ρ : Vec d → ℝ}
    (hρC : Continuous ρ) (hρc : HasCompactSupport ρ) (hρnn : ∀ z, 0 ≤ ρ z)
    (hρint : ∫ z, ρ z = 1) (hGc : ∀ x i, |G x i| ≤ 1 / 4) (R : ℝ) (ω : FieldPair d)
    (i : Fin d) : |∫ z, ρ z * G (translate (R • z) ω) i| ≤ 1 / 4 := by
  have hpt : ∀ z, ‖ρ z * G (translate (R • z) ω) i‖ ≤ ρ z * (1 / 4) := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρnn z)]
    exact mul_le_mul_of_nonneg_left (hGc _ i) (hρnn z)
  have hint : Integrable (fun z => ρ z * (1 / 4 : ℝ)) :=
    integrable_mul_cs_left hρC hρc continuous_const
  have h := norm_integral_le_of_norm_le hint (ae_of_all _ hpt)
  rw [integral_mul_const, hρint, one_mul, Real.norm_eq_abs] at h
  exact h

/-! ### The translation identity for the smoothed potential -/

private theorem smoothedPotential_translate_eq {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) {ρ : Vec d → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hρint : ∫ z, ρ z = 1) (R : ℝ) (v : Vec d) :
    smoothedPotential G ρ R (translate v ω) - smoothedPotential G ρ R ω =
      (∫ z, ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω (R • z))) -
        orbitRayPotential G ω v := by
  have hT : smoothedPotential G ρ R (translate v ω) =
      ∫ z, ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω v) := by
    unfold smoothedPotential
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show ρ z * orbitRayPotential G (translate v ω) (R • z) =
      ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω v)
    rw [orbitRayPotential_translate hφ hgrad v (R • z)]
  have hi1 : Integrable (fun z =>
      ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω v)) :=
    integrable_mul_cs_left hρ hρc
      ((continuous_orbitRayPotential_shift hφ hgrad R v).sub continuous_const)
  have hi2 : Integrable (fun z => ρ z * orbitRayPotential G ω (R • z)) :=
    integrable_mul_cs_left hρ hρc
      ((continuous_orbitRayPotential hφ hgrad).comp (continuous_const_smul R))
  have hi3 : Integrable (fun z =>
      ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω (R • z))) :=
    integrable_mul_cs_left hρ hρc
      ((continuous_orbitRayPotential_shift hφ hgrad R v).sub
        ((continuous_orbitRayPotential hφ hgrad).comp (continuous_const_smul R)))
  have hi4 : Integrable (fun z => ρ z * orbitRayPotential G ω v) :=
    integrable_mul_cs_left hρ hρc continuous_const
  rw [hT]
  unfold smoothedPotential
  rw [← integral_sub hi1 hi2]
  have e1 : ∫ z, (ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω v) -
      ρ z * orbitRayPotential G ω (R • z)) =
      ∫ z, (ρ z * (orbitRayPotential G ω (R • z + v) - orbitRayPotential G ω (R • z)) -
        ρ z * orbitRayPotential G ω v) := by
    congr 1
    funext z
    ring
  rw [e1, integral_sub hi3 hi4, integral_mul_const, hρint, one_mul]

private theorem slope_smoothedPotential_identity {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) {ρ : Vec d → ℝ} (hρ : Continuous ρ)
    (hρc : HasCompactSupport ρ) (hρint : ∫ z, ρ z = 1) (R : ℝ) (i : Fin d) (t : ℝ) :
    t⁻¹ * (smoothedPotential G ρ R (translate (t • unitVector i) ω) -
        smoothedPotential G ρ R ω) =
      (∫ z, ρ z * (t⁻¹ * (orbitRayPotential G ω (R • z + t • unitVector i) -
        orbitRayPotential G ω (R • z)))) - t⁻¹ * orbitRayPotential G ω (t • unitVector i) := by
  rw [smoothedPotential_translate_eq hφ hgrad hρ hρc hρint R (t • unitVector i)]
  have hm : ∫ z, ρ z * (t⁻¹ * (orbitRayPotential G ω (R • z + t • unitVector i) -
      orbitRayPotential G ω (R • z))) = t⁻¹ * ∫ z, ρ z * (orbitRayPotential G ω
        (R • z + t • unitVector i) - orbitRayPotential G ω (R • z)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    ring
  rw [hm]
  ring

private theorem abs_mul_inv_mul_le {r t X : ℝ} (hr : 0 ≤ r) (ht : t ≠ 0)
    (hX : |X| ≤ 1 / 4 * |t|) : |r * (t⁻¹ * X)| ≤ r * (1 / 4) := by
  rw [abs_mul, abs_of_nonneg hr]
  exact mul_le_mul_of_nonneg_left (abs_inv_mul_le_of_abs_le ht hX) hr

/-- The slope of the smoothed potential along a coordinate has the derivative given by the
bump average of the orbit gradient minus the gradient at the origin. -/
private theorem tendsto_smoothedPotential_slope {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) (hGc : ∀ x i, |G (translate x ω) i| ≤ 1 / 4)
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρnn : ∀ z, 0 ≤ ρ z)
    (hρint : ∫ z, ρ z = 1) (R : ℝ) (i : Fin d) :
    Tendsto (fun t : ℝ => t⁻¹ * (smoothedPotential G ρ R (translate (t • unitVector i) ω) -
        smoothedPotential G ρ R ω)) (𝓝[≠] 0)
      (𝓝 ((∫ z, ρ z * G (translate (R • z) ω) i) - G ω i)) := by
  have hlim1 : Tendsto (fun t : ℝ => ∫ z, ρ z * (t⁻¹ * (orbitRayPotential G ω
      (R • z + t • unitVector i) - orbitRayPotential G ω (R • z)))) (𝓝[≠] 0)
      (𝓝 (∫ z, ρ z * G (translate (R • z) ω) i)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z => ρ z * (1 / 4))
    · refine Eventually.of_forall fun t => ?_
      exact (hρ.mul (continuous_const.mul
        (((continuous_orbitRayPotential_shift hφ hgrad R (t • unitVector i)).sub
          ((continuous_orbitRayPotential hφ hgrad).comp (continuous_const_smul R)))))
        ).aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ?_)
      refine ae_of_all _ fun z => ?_
      have hb := abs_orbitRayPotential_line_sub_le hφ hgrad i (fun x => hGc x i) (R • z) t
      rw [Real.norm_eq_abs]
      exact abs_mul_inv_mul_le (hρnn z) (show t ≠ 0 from ht) hb
    · exact integrable_mul_cs_left hρ hρc continuous_const
    · refine ae_of_all _ fun z => ?_
      exact (tendsto_orbitRayPotential_slope hφ hgrad i (R • z)).const_mul (ρ z)
  have hlim2 : Tendsto (fun t : ℝ => t⁻¹ * orbitRayPotential G ω (t • unitVector i)) (𝓝[≠] 0)
      (𝓝 (G ω i)) := by
    have h := tendsto_orbitRayPotential_slope hφ hgrad i 0
    rw [translate_zero] at h
    refine h.congr (fun t => ?_)
    simp only [zero_add, orbitRayPotential_zero, sub_zero]
  have hfin := hlim1.sub hlim2
  exact hfin.congr (fun t => (slope_smoothedPotential_identity hφ hgrad hρ hρc hρint R i t).symm)

/-- Uniform bound for the slope of the smoothed potential along a coordinate. -/
private theorem abs_slope_smoothedPotential_le {d : ℕ} {G : FieldPair d → Vec d}
    {ω : FieldPair d} {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hgrad : ∀ x, gradient φ x = G (translate x ω)) (hGc : ∀ x i, |G (translate x ω) i| ≤ 1 / 4)
    {ρ : Vec d → ℝ} (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρnn : ∀ z, 0 ≤ ρ z)
    (hρint : ∫ z, ρ z = 1) (R : ℝ) (i : Fin d) {t : ℝ} (ht : t ≠ 0) :
    |t⁻¹ * (smoothedPotential G ρ R (translate (t • unitVector i) ω) -
        smoothedPotential G ρ R ω)| ≤ 1 / 2 := by
  rw [slope_smoothedPotential_identity hφ hgrad hρ hρc hρint R i t]
  have hI : |∫ z, ρ z * (t⁻¹ * (orbitRayPotential G ω (R • z + t • unitVector i) -
      orbitRayPotential G ω (R • z)))| ≤ 1 / 4 := by
    have hint : Integrable (fun z => ρ z * (1 / 4 : ℝ)) :=
      integrable_mul_cs_left hρ hρc continuous_const
    have h := norm_integral_le_of_norm_le hint (ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      exact abs_mul_inv_mul_le (hρnn z) ht
        (abs_orbitRayPotential_line_sub_le hφ hgrad i (fun x => hGc x i) (R • z) t))
    rw [integral_mul_const, hρint, one_mul, Real.norm_eq_abs] at h
    exact h
  have hJ : |t⁻¹ * orbitRayPotential G ω (t • unitVector i)| ≤ 1 / 4 :=
    abs_inv_mul_le_of_abs_le ht (abs_orbitRayPotential_axis_le hφ hgrad i (fun x => hGc x i) t)
  have h1 := abs_le.mp hI
  have h2 := abs_le.mp hJ
  exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-! ### Integration by parts for the averaged gradient -/

private theorem fderiv_smul_comp_apply {d : ℕ} {φ : Vec d → ℝ} (hφ : Differentiable ℝ φ)
    (R : ℝ) (z v : Vec d) :
    fderiv ℝ (fun z : Vec d => φ (R • z)) z v = R * fderiv ℝ φ (R • z) v := by
  have hl : HasFDerivAt (fun z : Vec d => R • z) (R • ContinuousLinearMap.id ℝ (Vec d)) z :=
    (hasFDerivAt_id z).const_smul R
  have h : HasFDerivAt (fun z : Vec d => φ (R • z))
      ((fderiv ℝ φ (R • z)).comp (R • ContinuousLinearMap.id ℝ (Vec d))) z :=
    (hφ (R • z)).hasFDerivAt.comp z hl
  rw [h.fderiv]
  simp [smul_eq_mul]

private theorem hasCompactSupport_fderiv_apply {d : ℕ} {ρ : Vec d → ℝ}
    (hρc : HasCompactSupport ρ) (v : Vec d) : HasCompactSupport (fun z => fderiv ℝ ρ z v) :=
  (HasCompactSupport.fderiv (𝕜 := ℝ) hρc).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L v)
    (by simp)

/-- The bump average of the derivative of a bounded `C¹` potential, tested against a fixed
direction, is at most `|M|` times the `L¹` norm of the derivative of the bump, divided by the
scale. -/
private theorem abs_integral_mul_fderiv_le {d : ℕ} {φ ρ : Vec d → ℝ} {M R : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hbd : ∀ x, |φ x| ≤ M) (hρ : ContDiff ℝ 1 ρ)
    (hρc : HasCompactSupport ρ) (hR : 0 < R) (v : Vec d) :
    |∫ z, ρ z * fderiv ℝ φ (R • z) v| ≤ |M| * (∫ z, |fderiv ℝ ρ z v|) * R⁻¹ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hρC : Continuous ρ := hρ.continuous
  have hφC : Continuous φ := hφ.continuous
  have hfd : Differentiable ℝ (fun z : Vec d => φ (R • z)) :=
    hφd.comp (differentiable_id.const_smul R)
  have hfC : Continuous (fun z : Vec d => φ (R • z)) := hφC.comp (continuous_const_smul R)
  have hfder : ∀ z, fderiv ℝ (fun z : Vec d => φ (R • z)) z v = R * fderiv ℝ φ (R • z) v :=
    fun z => fderiv_smul_comp_apply hφd R z v
  have hdρ : Continuous (fun z => fderiv ℝ ρ z v) :=
    (hρ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdφ : Continuous (fun z : Vec d => fderiv ℝ φ (R • z) v) :=
    ((hφ.continuous_fderiv (by norm_num)).comp (continuous_const_smul R)).clm_apply
      continuous_const
  have hdρc : HasCompactSupport (fun z => fderiv ℝ ρ z v) :=
    hasCompactSupport_fderiv_apply hρc v
  have hI1 : Integrable (fun z => φ (R • z) * ρ z) :=
    integrable_mul_cs_right hfC hρC hρc
  have hI2 : Integrable (fun z => φ (R • z) * fderiv ℝ ρ z v) :=
    integrable_mul_cs_right hfC hdρ hdρc
  have hI3 : Integrable (fun z => fderiv ℝ (fun z : Vec d => φ (R • z)) z v * ρ z) := by
    have heq : (fun z => fderiv ℝ (fun z : Vec d => φ (R • z)) z v * ρ z) =
        fun z => (R * fderiv ℝ φ (R • z) v) * ρ z := by
      funext z
      rw [hfder z]
    rw [heq]
    exact integrable_mul_cs_right (continuous_const.mul hdφ) hρC hρc
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun z : Vec d => φ (R • z)) (g := ρ) (v := v) hI3 hI2 hI1
    (fun x _ => hfd x) (fun x _ => hρd x)
  have hIBP' : ∫ z, φ (R • z) * fderiv ℝ ρ z v =
      -∫ z, fderiv ℝ (fun z : Vec d => φ (R • z)) z v * ρ z := hIBP
  have hRHS : ∫ z, fderiv ℝ (fun z : Vec d => φ (R • z)) z v * ρ z =
      R * ∫ z, ρ z * fderiv ℝ φ (R • z) v := by
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [hfder z]
    ring
  have hkey : R * ∫ z, ρ z * fderiv ℝ φ (R • z) v = -∫ z, φ (R • z) * fderiv ℝ ρ z v := by
    linarith [hRHS, hIBP']
  have hI_eq : ∫ z, ρ z * fderiv ℝ φ (R • z) v =
      -(R⁻¹ * ∫ z, φ (R • z) * fderiv ℝ ρ z v) := by
    have h1 : ∫ z, ρ z * fderiv ℝ φ (R • z) v =
        R⁻¹ * (R * ∫ z, ρ z * fderiv ℝ φ (R • z) v) := by
      rw [← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]
    rw [h1, hkey]
    ring
  have hJ : |∫ z, φ (R • z) * fderiv ℝ ρ z v| ≤ |M| * ∫ z, |fderiv ℝ ρ z v| := by
    have hbd' : ∀ z, ‖φ (R • z) * fderiv ℝ ρ z v‖ ≤ |M| * |fderiv ℝ ρ z v| := by
      intro z
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right ((hbd (R • z)).trans (le_abs_self M)) (abs_nonneg _)
    have hint : Integrable (fun z => |fderiv ℝ ρ z v|) :=
      (hdρ.abs).integrable_of_hasCompactSupport
        (hdρc.comp_left (g := fun x : ℝ => |x|) (by simp))
    have h := norm_integral_le_of_norm_le (hint.const_mul |M|) (ae_of_all _ hbd')
    rw [integral_const_mul, Real.norm_eq_abs] at h
    exact h
  calc |∫ z, ρ z * fderiv ℝ φ (R • z) v|
      = R⁻¹ * |∫ z, φ (R • z) * fderiv ℝ ρ z v| := by
        rw [hI_eq, abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hR)]
    _ ≤ R⁻¹ * (|M| * ∫ z, |fderiv ℝ ρ z v|) :=
        mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hR.le)
    _ = |M| * (∫ z, |fderiv ℝ ρ z v|) * R⁻¹ := by ring

/-! ### Bump function and Euclidean bounds -/

private theorem exists_smooth_unit_bump (d : ℕ) :
    ∃ ρ : Vec d → ℝ, ContDiff ℝ 1 ρ ∧ HasCompactSupport ρ ∧ (∀ z, 0 ≤ ρ z) ∧
      ∫ z, ρ z = 1 := by
  let f : ContDiffBump (0 : Vec d) :=
    { rIn := 1, rOut := 2, rIn_pos := one_pos, rIn_lt_rOut := one_lt_two }
  exact ⟨f.normed volume, f.contDiff_normed (μ := volume),
    f.hasCompactSupport_normed (μ := volume), fun z => f.nonneg_normed (μ := volume) z,
    f.integral_normed (μ := volume)⟩

private theorem euclidean_norm_le_of_coord_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ i, |x i| ≤ c) : ‖x‖ ≤ Real.sqrt d * c := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i, ‖x i‖ ^ 2 ≤ (d : ℝ) * c ^ 2 := by
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (x i), h i]
      _ = (d : ℝ) * c ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((d : ℝ) * c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * c := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hc]

/-! ### Probability-measure `L²` bounds and the `L²` dominated convergence -/

private theorem lp_norm_sq_eq_integral_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ ω, ‖u ω‖ ^ 2 ∂μ := by
  calc ‖u‖ ^ 2 = inner ℝ u u := (real_inner_self_eq_norm_sq u).symm
    _ = ∫ ω, inner ℝ (u ω) (u ω) ∂μ := L2.inner_def u u
    _ = ∫ ω, ‖u ω‖ ^ 2 ∂μ :=
        integral_congr_ae (ae_of_all _ fun ω => real_inner_self_eq_norm_sq _)

private theorem lp_norm_sq_eq_integral_sq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (u : Lp ℝ 2 μ) : ‖u‖ ^ 2 = ∫ ω, u ω * u ω ∂μ := by
  rw [lp_norm_sq_eq_integral_norm_sq]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  show ‖u ω‖ ^ 2 = u ω * u ω
  rw [Real.norm_eq_abs, sq_abs, sq]

private theorem lp_norm_le_of_ae_bound_probability {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] (u : Lp E 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᵐ ω ∂μ, ‖u ω‖ ≤ C) : ‖u‖ ≤ C := by
  have hsq : ‖u‖ ^ 2 ≤ C ^ 2 := by
    rw [lp_norm_sq_eq_integral_norm_sq]
    calc ∫ ω, ‖u ω‖ ^ 2 ∂μ ≤ ∫ _ω, C ^ 2 ∂μ :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => sq_nonneg _) (integrable_const _)
            (by
              filter_upwards [h] with ω hω
              nlinarith [norm_nonneg (u ω)])
      _ = C ^ 2 := by simp
  nlinarith [norm_nonneg u]

/-- Convergence in `L²` from almost-everywhere convergence with a uniform bound. -/
private theorem tendsto_Lp_of_ae_tendsto_bounded {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {l : Filter ℝ} [l.IsCountablyGenerated]
    (h : ℝ → Lp ℝ 2 μ) (g : Lp ℝ 2 μ) (k : ℝ → α → ℝ) {C : ℝ}
    (hh : ∀ t, h t =ᵐ[μ] k t) (hkm : ∀ t, AEStronglyMeasurable (k t) μ)
    (hkC : ∀ᶠ t in l, ∀ᵐ ω ∂μ, |k t ω| ≤ C) (hgC : ∀ᵐ ω ∂μ, |g ω| ≤ C)
    (hk : ∀ᵐ ω ∂μ, Tendsto (fun t => k t ω) l (𝓝 (g ω))) :
    Tendsto h l (𝓝 g) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ t, ‖h t - g‖ ^ 2 = ∫ ω, (k t ω - g ω) * (k t ω - g ω) ∂μ := by
    intro t
    rw [lp_norm_sq_eq_integral_sq]
    refine integral_congr_ae ?_
    filter_upwards [hh t, Lp.coeFn_sub (h t) g] with ω h1 h2
    rw [h2, Pi.sub_apply, h1]
  have hdc : Tendsto (fun t => ∫ ω, (k t ω - g ω) * (k t ω - g ω) ∂μ) l (𝓝 0) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := l)
      (fun _ => (2 * C) * (2 * C))
      (F := fun t ω => (k t ω - g ω) * (k t ω - g ω)) (f := fun _ => (0 : ℝ))
      (Eventually.of_forall fun t => ((hkm t).sub (Lp.aestronglyMeasurable g)).mul
        ((hkm t).sub (Lp.aestronglyMeasurable g)))
      (by
        filter_upwards [hkC] with t ht
        filter_upwards [ht, hgC] with ω h1 h2
        have h1' := abs_le.mp h1
        have h2' := abs_le.mp h2
        have hab : |k t ω - g ω| ≤ 2 * C :=
          abs_le.mpr ⟨by linarith [h1'.1, h2'.2], by linarith [h1'.2, h2'.1]⟩
        show ‖(k t ω - g ω) * (k t ω - g ω)‖ ≤ (2 * C) * (2 * C)
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hab hab (abs_nonneg _) (by linarith [abs_nonneg (k t ω - g ω)]))
      (integrable_const _)
      (by
        filter_upwards [hk] with ω hω
        have h0 : Tendsto (fun t => k t ω - g ω) l (𝓝 0) := by
          have h := hω.sub_const (g ω)
          rwa [sub_self] at h
        have h1 := h0.mul h0
        rw [mul_zero] at h1
        exact h1)
    simpa using hlim
  have hfun : (fun t => ‖h t - g‖) =
      fun t => Real.sqrt (∫ ω, (k t ω - g ω) * (k t ω - g ω) ∂μ) := by
    funext t
    rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
  rw [hfun]
  simpa [Function.comp_def] using (Real.continuous_sqrt.tendsto 0).comp hdc

/-- A pointwise limit of difference quotients with a uniform bound gives the horizontal derivative
in `L²`. -/
private theorem hasHorizontalLpDerivative_of_ae {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} (i : Fin d) {F g : FieldPair d → ℝ}
    (hF : MemLp F 2 Q) (hg : MemLp g 2 Q) {C : ℝ}
    (hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun ω => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)) Q)
    (hkC : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ ω ∂Q,
      |t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)| ≤ C)
    (hgC : ∀ᵐ ω ∂Q, |g ω| ≤ C)
    (hlim : ∀ᵐ ω ∂Q, Tendsto (fun t : ℝ => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω))
      (𝓝[≠] 0) (𝓝 (g ω))) :
    HasHorizontalLpDerivative Q hQ i (hF.toLp F) (hg.toLp g) := by
  have hh : ∀ t : ℝ, (t⁻¹ • (translationLp Q hQ (t • unitVector i) (hF.toLp F) - hF.toLp F)) =ᵐ[Q]
      (fun ω => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)) := by
    intro t
    have hT : (translationLp Q hQ (t • unitVector i) (hF.toLp F)) =ᵐ[Q]
        fun ω => F (translate (t • unitVector i) ω) := by
      rw [translationLp_toLp Q hQ (t • unitVector i) hF]
      exact MemLp.coeFn_toLp _
    filter_upwards [Lp.coeFn_smul t⁻¹ (translationLp Q hQ (t • unitVector i) (hF.toLp F) -
        hF.toLp F), Lp.coeFn_sub (translationLp Q hQ (t • unitVector i) (hF.toLp F))
        (hF.toLp F), hT, hF.coeFn_toLp] with ω h1 h2 h3 h4
    rw [h1, Pi.smul_apply, h2, Pi.sub_apply, h3, h4, smul_eq_mul]
  have hgC' : ∀ᵐ ω ∂Q, |(hg.toLp g) ω| ≤ C := by
    filter_upwards [hg.coeFn_toLp, hgC] with ω h1 h2
    rw [h1]
    exact h2
  have hlim' : ∀ᵐ ω ∂Q, Tendsto (fun t : ℝ => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω))
      (𝓝[≠] 0) (𝓝 ((hg.toLp g) ω)) := by
    filter_upwards [hg.coeFn_toLp, hlim] with ω h1 h2
    rw [h1]
    exact h2
  unfold HasHorizontalLpDerivative
  exact tendsto_Lp_of_ae_tendsto_bounded
    (fun t => t⁻¹ • (translationLp Q hQ (t • unitVector i) (hF.toLp F) - hF.toLp F))
    (hg.toLp g) (fun t ω => t⁻¹ * (F (translate (t • unitVector i) ω) - F ω)) hh hmeas hkC hgC'
    hlim'

/-! ### Horizontal gradients from a bounded family of derivatives -/

private theorem horizontalEuclideanGradient_coord_ae {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ)
    (g : Fin d → Lp ℝ 2 Q) (hg : ∀ i, HasHorizontalLpDerivative Q hQ i (f : Lp ℝ 2 Q) (g i))
    (i : Fin d) : ∀ᵐ ω ∂Q, horizontalEuclideanGradient Q hQ f ω i = g i ω := by
  have h1 := horizontalEuclideanGradient_coordinates Q hQ f i
  have h2 : horizontalH1Gradient Q hQ f i = g i :=
    congrFun (horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ f g hg) i
  rw [h2] at h1
  exact h1

/-- A bounded family of horizontal derivatives produces an element of the potential-gradient
domain whose coordinates are the negated derivatives. -/
private theorem exists_domain_of_derivatives {d : ℕ} (Q : Measure (FieldPair d))
    {hQ : IsStationary Q} {F : FieldPair d → ℝ} (hF : MemLp F 2 Q)
    (gf : Fin d → FieldPair d → ℝ) (hg : ∀ i, MemLp (gf i) 2 Q)
    (hH : ∀ i, HasHorizontalLpDerivative Q hQ i (hF.toLp F) ((hg i).toLp (gf i))) :
    ∃ V : Lp (EuclideanSpace ℝ (Fin d)) 2 Q, V ∈ stationaryPotentialGradients Q hQ ∧
      ∀ i, ∀ᵐ ω ∂Q, V ω i = -(gf i ω) := by
  have hW : (-1 : ℝ) • hF.toLp F ∈ horizontalH1 Q hQ :=
    ⟨fun i => (-1 : ℝ) • (hg i).toLp (gf i), fun i => (hH i).smul (-1)⟩
  refine ⟨horizontalEuclideanGradient Q hQ ⟨(-1 : ℝ) • hF.toLp F, hW⟩,
    horizontalEuclideanGradient_mem_stationaryPotentialGradients Q hQ
      ⟨(-1 : ℝ) • hF.toLp F, hW⟩, fun i => ?_⟩
  have h1 := horizontalEuclideanGradient_coord_ae Q hQ ⟨(-1 : ℝ) • hF.toLp F, hW⟩
    (fun j => (-1 : ℝ) • (hg j).toLp (gf j)) (fun j => (hH j).smul (-1)) i
  filter_upwards [h1, Lp.coeFn_smul (-1 : ℝ) ((hg i).toLp (gf i)), (hg i).coeFn_toLp]
    with ω h1ω h2ω h3ω
  have e1 : horizontalEuclideanGradient Q hQ ⟨(-1 : ℝ) • hF.toLp F, hW⟩ ω i =
      (⇑((-1 : ℝ) • (hg i).toLp (gf i))) ω := h1ω
  rw [e1, h2ω, Pi.smul_apply, h3ω, smul_eq_mul]
  ring

/-! ### Transport through the reduction and the approximation -/

/-- The approximation at scale `R`: an element of the potential-gradient domain whose coordinates
are within `|M| (∑ ‖∂ρ‖₁) / R` of the orbit gradient, transported through the reduction. -/
private theorem exists_domain_approx {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G : FieldPair d → Vec d) (M : ℝ) (hGm : Measurable G) (hGc : ∀ x i, |G x i| ≤ 1 / 4)
    (hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x ω))
    (D : FieldPair d → FieldPair d) (hDm : Measurable D) (hDL : Function.LeftInverse D reduce)
    {ρ : Vec d → ℝ} (hρ : ContDiff ℝ 1 ρ) (hρc : HasCompactSupport ρ) (hρnn : ∀ z, 0 ≤ ρ z)
    (hρint : ∫ z, ρ z = 1) {R : ℝ} (hR : 0 < R) :
    ∃ V : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      V ∈ correctorPotentialDomain Q ∧
        ∀ᵐ ω' ∂(reducedEnvironmentLaw Q), ∀ i,
          |V ω' i - G (D ω') i| ≤ |M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) * R⁻¹ := by
  have hρC : Continuous ρ := hρ.continuous
  have hDr : ∀ ω, D (reduce ω) = ω := hDL
  have hμ := reducedEnvironmentLaw_stationary Q
  have hA1 : ∀ᵐ ω' ∂(reducedEnvironmentLaw Q), reduce (D ω') = ω' := by
    refine ((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
      (p := fun ω' => reduce (D ω') = ω')).mpr (ae_of_all _ fun ω => ?_)
    show reduce (D (reduce ω)) = reduce ω
    rw [hDr ω]
  have hA2 : ∀ᵐ ω' ∂(reducedEnvironmentLaw Q), ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧
      (∀ x, |φ x| ≤ M) ∧ ∀ x, gradient φ x = G (translate x (D ω')) := by
    refine ((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
      (p := fun ω' => ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
        ∀ x, gradient φ x = G (translate x (D ω')))).mpr ?_
    filter_upwards [hG] with ω hω
    show ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = G (translate x (D (reduce ω)))
    rw [hDr ω]
    exact hω
  have hkey : ∀ ω' : FieldPair d, reduce (D ω') = ω' → ∀ x, D (translate x ω') =
      translate x (D ω') := by
    intro ω' h1 x
    have := EinsteinRelation.Probability.leftInverse_reduce_translate D hDL (D ω') x
    rwa [h1] at this
  have hFm : Measurable (fun ω' => smoothedPotential G ρ R (D ω')) :=
    (measurable_smoothedPotential_aux hGm hρC R).comp hDm
  have hFmem : MemLp (fun ω' => smoothedPotential G ρ R (D ω')) 2 (reducedEnvironmentLaw Q) :=
    MemLp.of_bound hFm.aestronglyMeasurable (smoothedBound ρ R)
      (ae_of_all _ fun ω' => by
        rw [Real.norm_eq_abs]
        exact abs_smoothedPotential_le G hρC hρc hρnn hGc R (D ω'))
  have hgm : ∀ i, Measurable (fun ω' =>
      (∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i) := fun i =>
    ((measurable_coordinateAvg hGm hρC R i).comp hDm).sub
      ((measurable_pi_apply i).comp (hGm.comp hDm))
  have hgb : ∀ i ω', |(∫ z, ρ z * G (translate (R • z) ω') i) - G ω' i| ≤ 1 / 2 := by
    intro i ω'
    have h1 := abs_le.mp (abs_coordAvg_le hρC hρc hρnn hρint hGc R ω' i)
    have h2 := abs_le.mp (hGc ω' i)
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  have hgmem : ∀ i, MemLp (fun ω' =>
      (∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i) 2 (reducedEnvironmentLaw Q) :=
    fun i => MemLp.of_bound (hgm i).aestronglyMeasurable (1 / 2)
      (ae_of_all _ fun ω' => by
        rw [Real.norm_eq_abs]
        exact hgb i (D ω'))
  have hHor : ∀ i, HasHorizontalLpDerivative (reducedEnvironmentLaw Q) hμ i
      (hFmem.toLp (fun ω' => smoothedPotential G ρ R (D ω')))
      ((hgmem i).toLp (fun ω' => (∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i)) := by
    intro i
    refine hasHorizontalLpDerivative_of_ae i hFmem (hgmem i) (C := 1 / 2) ?_ ?_ ?_ ?_
    · intro t
      have hm1 : Measurable (fun ω' =>
          smoothedPotential G ρ R (D (translate (t • unitVector i) ω'))) :=
        (measurable_smoothedPotential_aux hGm hρC R).comp
          (hDm.comp (Probability.measurable_translate _))
      exact (measurable_const.mul (hm1.sub hFm)).aestronglyMeasurable
    · refine Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => ?_)
      refine (hA1.and hA2).mono fun ω' hω' => ?_
      obtain ⟨h1, φ, hφ, -, hgrad⟩ := hω'
      have hk := hkey ω' h1 (t • unitVector i)
      show |t⁻¹ * (smoothedPotential G ρ R (D (translate (t • unitVector i) ω')) -
        smoothedPotential G ρ R (D ω'))| ≤ 1 / 2
      rw [hk]
      exact abs_slope_smoothedPotential_le hφ hgrad (fun x i => hGc (translate x (D ω')) i)
        hρC hρc hρnn hρint R i (show t ≠ 0 from ht)
    · exact ae_of_all _ fun ω' => hgb i (D ω')
    · refine (hA1.and hA2).mono fun ω' hω' => ?_
      obtain ⟨h1, φ, hφ, -, hgrad⟩ := hω'
      have hk := hkey ω' h1
      have hsimp : (fun t : ℝ => t⁻¹ * (smoothedPotential G ρ R
          (D (translate (t • unitVector i) ω')) - smoothedPotential G ρ R (D ω'))) =
          fun t : ℝ => t⁻¹ * (smoothedPotential G ρ R (translate (t • unitVector i) (D ω')) -
            smoothedPotential G ρ R (D ω')) := by
        funext t
        rw [hk]
      show Tendsto (fun t : ℝ => t⁻¹ * (smoothedPotential G ρ R
          (D (translate (t • unitVector i) ω')) - smoothedPotential G ρ R (D ω')))
        (𝓝[≠] 0) (𝓝 ((∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i))
      rw [hsimp]
      exact tendsto_smoothedPotential_slope hφ hgrad (fun x i => hGc (translate x (D ω')) i)
        hρC hρc hρnn hρint R i
  obtain ⟨V, hVmem, hVc⟩ := exists_domain_of_derivatives (reducedEnvironmentLaw Q) hFmem
    (fun i ω' => (∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i) hgmem hHor
  refine ⟨V, hVmem, ae_all_iff.mpr fun i => ?_⟩
  filter_upwards [hVc i, hA2] with ω' hc h2
  obtain ⟨φ, hφ, hbd, hgrad⟩ := h2
  have hc' : V ω' i = -((∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i) := hc
  have hI : ∫ z, ρ z * G (translate (R • z) (D ω')) i =
      ∫ z, ρ z * fderiv ℝ φ (R • z) (unitVector i) := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show ρ z * G (translate (R • z) (D ω')) i = ρ z * fderiv ℝ φ (R • z) (unitVector i)
    rw [← hgrad (R • z)]
    rfl
  have hbound := abs_integral_mul_fderiv_le hφ hbd hρ hρc hR (unitVector i)
  have hS : ∫ z, |fderiv ℝ ρ z (unitVector i)| ≤ ∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)| :=
    Finset.single_le_sum (f := fun j => ∫ z, |fderiv ℝ ρ z (unitVector j)|)
      (fun j _ => integral_nonneg fun z => abs_nonneg _) (Finset.mem_univ i)
  have hfin : |∫ z, ρ z * G (translate (R • z) (D ω')) i| ≤
      |M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) * R⁻¹ := by
    rw [hI]
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hS (abs_nonneg M)) (inv_nonneg.mpr hR.le))
  rw [hc', show -((∫ z, ρ z * G (translate (R • z) (D ω')) i) - G (D ω') i) - G (D ω') i =
    -(∫ z, ρ z * G (translate (R • z) (D ω')) i) by ring, abs_neg]
  exact hfin

/-! ### The orbit-potential gradient domain -/

/-- The orbit-potential characterization of the closed stationary potential-gradient domain.

If `G` is measurable and bounded by `1/4` pointwise, and almost every translation orbit of `G` is
the gradient of a `C¹` potential bounded by `M`, then every `L²` representative `E` of the reduced
field, meaning `E (reduce ω) = G ω` almost surely, lies in `correctorPotentialDomain Q`. -/
theorem orbitPotentialGradientDomain_holds {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ (G : FieldPair d → Vec d) (M : ℝ),
      Measurable G → (∀ ω, euclideanNorm (G ω) ≤ 1 / 4) →
      (∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
        ∀ x, gradient φ x = G (translate x ω)) →
      ∀ E : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
        (∀ᵐ ω ∂Q.measure, (⇑E) (reduce ω) = (WithLp.toLp 2 (G ω) : EuclideanSpace ℝ (Fin d))) →
        E ∈ correctorPotentialDomain Q := by
  intro G M hGm hGb hG E hpull
  have hGc : ∀ x i, |G x i| ≤ 1 / 4 := fun x i => orbit_abs_coord_le (G x) (hGb x) i
  obtain ⟨ρ, hρ, hρc, hρnn, hρint⟩ := exists_smooth_unit_bump d
  obtain ⟨D, hDm, hDL⟩ := EinsteinRelation.Probability.exists_measurable_leftInverse_reduce d
  have hS0 : 0 ≤ ∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)| :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun z => abs_nonneg _
  have happrox : ∀ n : ℕ, ∃ V : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q),
      V ∈ correctorPotentialDomain Q ∧ ∀ᵐ ω' ∂(reducedEnvironmentLaw Q), ∀ i,
        |V ω' i - G (D ω') i| ≤
          |M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) * ((n : ℝ) + 1)⁻¹ := fun n =>
    exists_domain_approx Q G M hGm hGc hG D hDm hDL hρ hρc hρnn hρint (R := (n : ℝ) + 1)
      (by positivity)
  choose V hVmem hVbd using happrox
  have hEq : ∀ᵐ ω' ∂(reducedEnvironmentLaw Q), ∀ i, (⇑E) ω' i = G (D ω') i := by
    have h1 : ∀ᵐ ω' ∂(Measure.map (reduce (d := d)) Q.measure),
        (⇑E) ω' = (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)) := by
      refine ((EinsteinRelation.Probability.measurableEmbedding_reduce d).ae_map_iff
        (p := fun ω' => (⇑E) ω' = (WithLp.toLp 2 (G (D ω')) : EuclideanSpace ℝ (Fin d)))).mpr ?_
      filter_upwards [hpull] with ω hω
      show (⇑E) (reduce ω) = (WithLp.toLp 2 (G (D (reduce ω))) : EuclideanSpace ℝ (Fin d))
      rw [hDL ω]
      exact hω
    filter_upwards [h1] with ω' h i
    simp [h]
  have hC' : ∀ n : ℕ, 0 ≤ |M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) *
      ((n : ℝ) + 1)⁻¹ := fun n =>
    mul_nonneg (mul_nonneg (abs_nonneg M) hS0) (inv_nonneg.mpr (by positivity))
  have hLp : ∀ n : ℕ, ‖V n - E‖ ≤
      Real.sqrt d * (|M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) * ((n : ℝ) + 1)⁻¹) := by
    intro n
    refine lp_norm_le_of_ae_bound_probability (V n - E)
      (mul_nonneg (Real.sqrt_nonneg _) (hC' n)) ?_
    filter_upwards [Lp.coeFn_sub (V n) E, hVbd n, hEq] with ω' h1 h2 h3
    rw [h1, Pi.sub_apply]
    refine euclidean_norm_le_of_coord_le (V n ω' - E ω') (hC' n) fun i => ?_
    rw [PiLp.sub_apply, h3 i]
    exact h2 i
  have hlim : Tendsto (fun n : ℕ => Real.sqrt d *
      (|M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|) * ((n : ℝ) + 1)⁻¹)) atTop (𝓝 0) := by
    have h1 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (Real.sqrt d * (|M| * (∑ j, ∫ z, |fderiv ℝ ρ z (unitVector j)|)))
    rw [mul_zero] at h1
    refine h1.congr (fun n => ?_)
    simp only [one_div]
    ring
  have hVE : Tendsto (fun n => V n) atTop (𝓝 E) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hLp hlim)
  exact (isClosed_stationaryPotentialGradients (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q)).mem_of_tendsto hVE
    (Eventually.of_forall fun n => hVmem n)

end

end EinsteinRelation.Correctors
