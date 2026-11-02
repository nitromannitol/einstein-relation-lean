import EinsteinFull.Calculus.C18TubeWeightedTimeMollification
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.Calculus.C13TubeNativeCutoffProduct
import EinsteinFull.Calculus.C5TubeWeightedCaccioppoli
import EinsteinFull.Calculus.C18TubeWeightedSobolevTestExtension
import EinsteinFull.Calculus.C11TubeForwardNonlinearTest

open EinsteinRelation MeasureTheory
open EinsteinFull.External.Source.GMP
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- The actual forward difference quotient has square-integrable spatial
sections on almost every time slice of the smaller cylinder. -/
theorem c5_weighted_caloric_forward_difference_L2_slices {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (y : Vec d) (u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      MemLp (fun x => h⁻¹ * (u (t + h, x) - u (t, x))) 2
        (volume.restrict (sourceBall y r)) := by
  have hshift := (c18_memLp_forward_shift (c18_sourceBall_measurable y r)
    hhsmall (show h ∈ Set.Icc 0 h from ⟨le_of_lt hh, le_rfl⟩) hu.1).1
  have hbase := (c18_memLp_forward_shift (c18_sourceBall_measurable y r)
    hhsmall (show (0 : ℝ) ∈ Set.Icc 0 h from ⟨le_rfl, le_of_lt hh⟩) hu.1).1
  have hbase' : MemLp u 2 (volume.restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
    simpa only [add_zero] using hbase
  have hd := (hshift.sub hbase').const_mul h⁻¹
  have hp : (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod
      (volume.restrict (sourceBall y r)) =
      volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hp] at hd
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hd] with t ht
  exact ht

/-- The forward solution and its actual averaged gradient both have spatial
L² sections on the same full-measure set of times. -/
theorem c5_weighted_caloric_forward_average_L2_slices {d : ℕ} {h r : ℝ}
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4) (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (y : Vec d) (u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      MemLp (fun x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)) 2
        (volume.restrict (sourceBall y r)) ∧
      MemLp (fun x => euclideanNorm (h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x))) 2
        (volume.restrict (sourceBall y r)) := by
  obtain ⟨hu', hG'⟩ := c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu
  have hp : (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))).prod
      (volume.restrict (sourceBall y r)) =
      volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hp] at hu' hG'
  filter_upwards [c9_memLp_prod_right_ae _ _ _ hu',
    c9_memLp_prod_right_ae _ _ _ hG'] with t ht hGt
  exact ⟨ht, hGt⟩

/-- The density-weighted finite-difference pairing against the squared cutoff
and the forward solution is integrable on almost every time slice. -/
theorem c5_forward_square_mass_integrable_slices {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      Integrable (fun x => ρ x * (h⁻¹ * (u (t + h, x) - u (t, x))) *
        (χ x ^ 2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x))))
        (volume.restrict (sourceBall y r)) := by
  have hρ : MemLp ρ ∞ (volume.restrict (sourceBall y r)) := by
    apply memLp_top_of_bound hell.1.aestronglyMeasurable κ⁻¹
    apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (hell.2.2 x).1)] using
      (hell.2.2 x).2.1
  have hχtop : MemLp χ ∞ (volume.restrict (sourceBall y r)) :=
    PDE.DGNM.memLpOn_top_of_contDiff hχ hχc
  filter_upwards [c5_weighted_caloric_forward_difference_L2_slices hh hhsmall ρ α y u G hu,
    c5_weighted_caloric_forward_average_L2_slices hh hhsmall ρ α y u G hu] with t hd ha
  have hd' : MemLp (fun x => (h⁻¹ * (u (t + h, x) - u (t, x))) * ρ x) 2
      (volume.restrict (sourceBall y r)) := hd.fun_mul hρ
  have ha₁ : MemLp (fun x => (h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)) * χ x) 2
      (volume.restrict (sourceBall y r)) := ha.1.fun_mul hχtop
  have ha' : MemLp (fun x => (h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)) * χ x * χ x) 2
      (volume.restrict (sourceBall y r)) := ha₁.fun_mul hχtop
  convert hd'.integrable_mul ha' using 1 <;> funext x <;> simp only [Pi.mul_apply] <;> ring

/-- The elliptic flux of a weighted caloric field has square-integrable
spatial coordinates on almost every time slice. -/
theorem c5_weighted_caloric_flux_L2_slices {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) (i : Fin d) :
    ∀ᵐ t ∂volume.restrict I,
      MemLp (fun x => ((α x).mulVec (G (t, x))) i) 2 (volume.restrict U) := by
  apply c9_memLp_prod_right_ae (volume.restrict I) (volume.restrict U)
    (fun z => ((α z.2).mulVec (G z)) i)
  have hs := c5_weighted_caloric_flux_memLp (ρ := ρ) (α := α)
    (I := I) (U := U) (u := u) (G := G) hκ hell hu i
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hs
  exact hs

/-- The averaged gradient has square-integrable flux coordinates on almost
 every spatial slice. -/
@[nolint unusedArguments]
theorem c5_weighted_caloric_forward_flux_L2_slices {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G) :
    ∀ i : Fin d, ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      MemLp (fun x =>
        ((α x).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x))) i) 2
        (volume.restrict (sourceBall y r)) := by
  intro i
  let U : ℝ × Vec d → ℝ := fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
  let V : ℝ × Vec d → Vec d := fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
  have hc : IsWeightedCaloric ρ α (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (sourceBall y r) U V :=
    c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu
  exact c5_weighted_caloric_flux_L2_slices hκ hell hc i

/-- The squared spatial cutoff of the forward solution has its actual weak
spatial gradient and finite L² energy on almost every time slice. -/
theorem c5_forward_square_sobolev_slices {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall y r) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasWeakGradient (sourceBall y r) (fun x => χ x ^ 2 * U t x)
        (fun x j => χ x ^ 2 * V t x j + 2 * χ x * U t x *
          fderiv ℝ χ x (unitVector j)) ∧
      MemLp (fun x => χ x ^ 2 * U t x) 2 (volume.restrict (sourceBall y r)) ∧
      MemLp (fun x => euclideanNorm (fun j => χ x ^ 2 * V t x j +
        2 * χ x * U t x * fderiv ℝ χ x (unitVector j))) 2
          (volume.restrict (sourceBall y r)) := by
  let U : ℝ × Vec d → ℝ := fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
  let V : ℝ × Vec d → Vec d := fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
  have hc : IsWeightedCaloric ρ α (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (sourceBall y r) U V :=
    c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu
  have hopen : IsOpen (sourceBall y r) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall y hr]
    exact PDE.isOpen_euclideanBall _ _
  have hη : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d × ℝ => χ z.1) :=
    hχ.comp contDiff_fst
  have hz : ∀ x ∉ tsupport χ, ∀ t : ℝ, χ x = 0 := by
    intro x hx t
    exact image_eq_zero_of_notMem_tsupport hx
  have hs := c5_signed_squared_cutoff_sobolev_slices hopen hc hη hχc hχU hz
  have hder (x : Vec d) (t : ℝ) (j : Fin d) :
      PDE.parSpaceGrad (fun z : Vec d × ℝ => χ z.1) (x, t) j =
        fderiv ℝ χ x (unitVector j) := by
    have hd := ((hχ.differentiable (by simp)) x).hasFDerivAt.comp (x, t)
      (hasFDerivAt_fst (𝕜 := ℝ))
    change fderiv ℝ (χ ∘ Prod.fst) (x, t) (PDE.basisVec j, 0) = _
    rw [hd.fderiv]
    rfl
  filter_upwards [hs] with t ht
  have hv (x : Vec d) :
      χ x ^ 2 • V (t, x) + U (t, x) •
          (fun j => 2 * χ x * fderiv ℝ χ x (unitVector j)) =
        (fun j => χ x ^ 2 * V (t, x) j + 2 * χ x * U (t, x) *
          fderiv ℝ χ x (unitVector j)) := by
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simpa only [hder, hv] using ht

/-- Both parts of the forward square-test pairing are integrable on almost
 every spatial slice. -/
theorem c5_forward_square_pairing_integrable_slices {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall y r) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      Integrable (fun x => ρ x * (h⁻¹ * (u (t + h, x) - u (t, x))) *
        (χ x ^ 2 * U t x) + dot ((α x).mulVec (V t x))
          (fun j => χ x ^ 2 * V t x j + 2 * χ x * U t x *
            fderiv ℝ χ x (unitVector j))) (volume.restrict (sourceBall y r)) := by
  let U : ℝ → Vec d → ℝ := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
  let V : ℝ → Vec d → Vec d := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
  have hf : ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      ∀ i : Fin d, MemLp (fun x => ((α x).mulVec (V t x)) i) 2
        (volume.restrict (sourceBall y r)) := by
    rw [ae_all_iff]
    exact c5_weighted_caloric_forward_flux_L2_slices hκ hr hh hhsmall ρ α hell y u G hu
  filter_upwards [hf, c5_forward_square_sobolev_slices hκ hr hh hhsmall ρ α hell y u G hu χ hχ hχc hχU,
    c5_forward_square_mass_integrable_slices hκ hh hhsmall ρ α hell y u G hu χ hχ hχc] with t ht hs hm
  let H : Vec d → Vec d := fun x j => χ x ^ 2 * V t x j +
    2 * χ x * U t x * fderiv ℝ χ x (unitVector j)
  have hcoord (j : Fin d) : MemLp (fun x => H x j) 2
      (volume.restrict (sourceBall y r)) := by
    apply hs.2.2.mono' (hs.1 j).2.1.aestronglyMeasurable
    apply ae_of_all
    intro x
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (H x)) j)
  have hflux : Integrable (fun x => dot ((α x).mulVec (V t x)) (H x))
      (volume.restrict (sourceBall y r)) := by
    have hs' := integrable_finset_sum Finset.univ (fun j _ => (ht j).integrable_mul (hcoord j))
    simpa only [dot, Finset.sum_apply, Pi.mul_apply] using hs'
  exact hm.add hflux

/-- The forward square-test pairing is integrable on the full cylinder. -/
@[nolint unusedArguments]
theorem c5_forward_square_pairing_integrable {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    let U := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let V := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    Integrable (fun z => ρ z.2 * (h⁻¹ * (u (z.1 + h, z.2) - u z)) *
      (χ z.2 ^ 2 * U z) + dot ((α z.2).mulVec (V z))
      (fun j => χ z.2 ^ 2 * V z j + 2 * χ z.2 * U z *
        fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  let U : ℝ × Vec d → ℝ := fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
  let V : ℝ × Vec d → Vec d := fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
  have hc : IsWeightedCaloric ρ α (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (sourceBall y r) U V :=
    c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    have ht := hχ.continuous.memLp_top_of_hasCompactSupport hχc (Measure.map Prod.snd μ)
    exact ht.comp_of_map measurable_snd.aemeasurable
  have hχder (j : Fin d) : MemLp (fun z : ℝ × Vec d =>
      fderiv ℝ χ z.2 (unitVector j)) ∞ μ := by
    have ht := ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
      (hχc.fderiv_apply ℝ (unitVector j)) (Measure.map Prod.snd μ)
    exact ht.comp_of_map measurable_snd.aemeasurable
  have hρ := (c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell).1
  have hd := c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu
  have hmass : Integrable (fun z => ρ z.2 * (h⁻¹ * (u (z.1 + h, z.2) - u z)) *
      (χ z.2 ^ 2 * U z)) μ := by
    have ht₁ : MemLp (fun z => U z * χ z.2) 2 μ := hc.1.fun_mul hχtop
    have ht : MemLp (fun z => U z * χ z.2 * χ z.2) 2 μ := ht₁.fun_mul hχtop
    have hdρ : MemLp (fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)) 2 μ := hρ.mul hd
    have hp := hdρ.integrable_mul ht
    convert hp using 1 <;> funext z <;> simp only [Pi.mul_apply, div_eq_mul_inv] <;> ring
  have hV : MemLp V 2 μ := by
    apply hc.2.2.1.mono' hc.2.1
    exact Filter.Eventually.of_forall (fun z => by
      apply pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _) |>.mpr
      intro i
      exact EinsteinRelation.Regeneration.coordinate_abs_le_euclideanNorm (V z) i)
  have hgrad (j : Fin d) : MemLp (fun z => χ z.2 ^ 2 * V z j +
      2 * χ z.2 * U z * fderiv ℝ χ z.2 (unitVector j)) 2 μ := by
    have hv₁ : MemLp (fun z => V z j * χ z.2) 2 μ := (hV.eval j).fun_mul hχtop
    have hv : MemLp (fun z => V z j * χ z.2 * χ z.2) 2 μ := hv₁.fun_mul hχtop
    have hu₁ : MemLp (fun z => U z * χ z.2) 2 μ := hc.1.fun_mul hχtop
    have hu₂ : MemLp (fun z => U z * χ z.2 * fderiv ℝ χ z.2 (unitVector j)) 2 μ :=
      hu₁.fun_mul (hχder j)
    have hu' := hu₂.const_mul 2
    convert hv.add hu' using 1 <;> funext z <;> simp only [Pi.add_apply, Pi.mul_apply] <;> ring
  have hf := c5_weighted_caloric_flux_memLp hκ hell hc
  have hflux : Integrable (fun z => dot ((α z.2).mulVec (V z))
      (fun j => χ z.2 ^ 2 * V z j + 2 * χ z.2 * U z *
        fderiv ℝ χ z.2 (unitVector j))) μ := by
    have hs := integrable_finsetSum Finset.univ (fun j _ => (hf j).integrable_mul (hgrad j))
    simpa only [dot, Finset.sum_apply, Pi.mul_apply] using hs
  exact hmass.add hflux

/-- The spatial square-test pairing is integrable as a function of time. -/
theorem c5_forward_square_pairing_integrable_time {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
    Integrable (fun t => ∫ x in sourceBall y r,
      ρ x * (h⁻¹ * (u (t + h, x) - u (t, x))) * (χ x ^ 2 * U t x) +
      dot ((α x).mulVec (V t x)) (fun j => χ x ^ 2 * V t x j +
        2 * χ x * U t x * fderiv ℝ χ x (unitVector j)))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2))) := by
  have hi := c5_forward_square_pairing_integrable hκ hr hh hhsmall ρ α hell y u G hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  exact hi.integral_prod_left

/-- A time test times the square of a spatial cutoff is a smooth compactly
supported test in the corresponding cylinder. -/
theorem c5_separated_square_cutoff {d : ℕ} {a b r : ℝ} {y : Vec d}
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r) :
    let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
    ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ Set.Ioo a b ×ˢ sourceBall y r := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hs : tsupport θ ⊆ tsupport η ×ˢ tsupport χ := by
    apply closure_minimal _ ((isClosed_tsupport η).prod (isClosed_tsupport χ))
    intro z hz
    have h₁ : η z.1 ≠ 0 := left_ne_zero_of_mul hz
    have h₂ : χ z.2 ≠ 0 := by
      intro hzχ
      simp [θ, hzχ] at hz
    exact ⟨subset_tsupport η h₁, subset_tsupport χ h₂⟩
  refine ⟨(hη.comp contDiff_fst).mul ((hχ.comp contDiff_snd).pow 2),
    (hηc.prod hχc).of_isClosed_subset (isClosed_tsupport θ) hs, ?_⟩
  exact hs.trans (Set.prod_mono hηs hχs)

/-- The spatial derivative of the separated square cutoff. -/
theorem c5_separated_square_cutoff_fderiv {d : ℕ}
    (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    (χ : Vec d → ℝ) (hχ : Differentiable ℝ χ)
    (z : ℝ × Vec d) (j : Fin d) :
    fderiv ℝ (fun w : ℝ × Vec d => η w.1 * χ w.2 ^ 2) z (0, unitVector j) =
      η z.1 * (2 * χ z.2 * fderiv ℝ χ z.2 (unitVector j)) := by
  have h1 := (hη z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hχ z.2).hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ))
  have h3 := h1.mul (h2.mul h2)
  change HasFDerivAt (fun w : ℝ × Vec d => η w.1 * (χ w.2 * χ w.2)) _ z at h3
  have heq : (fun w : ℝ × Vec d => η w.1 * χ w.2 ^ 2) =
      (fun w : ℝ × Vec d => η w.1 * (χ w.2 * χ w.2)) := by
    funext w
    rw [pow_two]
  rw [heq, h3.fderiv]
  simp <;> ring

/-- The density-weighted part of the forward square pairing is integrable
on the whole cylinder. -/
theorem c5_forward_square_mass_integrable {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ) :
    Integrable (fun z : ℝ × Vec d => ρ z.2 * (h⁻¹ * (u (z.1 + h, z.2) - u z)) *
      (χ z.2 ^ 2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  have hχtop : MemLp (fun z : ℝ × Vec d => χ z.2) ∞ μ := by
    have ht := hχ.continuous.memLp_top_of_hasCompactSupport hχc (Measure.map Prod.snd μ)
    exact ht.comp_of_map measurable_snd.aemeasurable
  have hρ := (c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell).1
  have hd := c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu
  have havg := (c18_weighted_caloric_forward_average_memLp hh hhsmall ρ α y u G hu).1
  have ht₁ : MemLp (fun z => (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) * χ z.2) 2 μ :=
    havg.fun_mul hχtop
  have ht : MemLp (fun z => (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) * χ z.2 * χ z.2) 2 μ :=
    ht₁.fun_mul hχtop
  have hdρ : MemLp (fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)) 2 μ := hρ.mul hd
  have hp := hdρ.integrable_mul ht
  convert hp using 1 <;> funext z <;> simp only [Pi.mul_apply, div_eq_mul_inv] <;> ring

/-- The derivative of the quadratic entropy is the identity. -/
theorem c5_quadratic_deriv : deriv (fun s : ℝ => s ^ 2 / 2) = id := by
  funext s
  have hh := ((hasDerivAt_id s).pow 2).div_const 2
  convert hh.deriv using 1 <;> simp <;> ring

/-- The forward square pairing vanishes against any interior time test. -/
theorem c5_forward_square_pairing_time_test {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
    (∫ t in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), η t *
      (∫ x in sourceBall y r,
        ρ x * (h⁻¹ * (u (t + h, x) - u (t, x))) * (χ x ^ 2 * U t x) +
        dot ((α x).mulVec (V t x)) (fun j => χ x ^ 2 * V t x j +
          2 * χ x * U t x * fderiv ℝ χ x (unitVector j)))) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  let U : ℝ × Vec d → ℝ := fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
  let V : ℝ × Vec d → Vec d := fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
  let A : ℝ × Vec d → ℝ := fun z => ρ z.2 * (h⁻¹ * (u (z.1 + h, z.2) - u z)) *
    (χ z.2 ^ 2 * U z)
  let B : ℝ × Vec d → ℝ := fun z => dot ((α z.2).mulVec (V z))
    (fun j => χ z.2 ^ 2 * V z j + 2 * χ z.2 * U z * fderiv ℝ χ z.2 (unitVector j))
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hθ := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have hφ : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hφ₂ : deriv (deriv (fun s : ℝ => s ^ 2 / 2)) = fun _ => (1 : ℝ) := by
    rw [c5_quadratic_deriv]
    funext s
    simp
  have heq := c11_weighted_forward_nonlinear_spacetime_test hκ hr hh hhsmall y ρ α hell u G hu
    (fun s : ℝ => s ^ 2 / 2) hφ 1 (by norm_num)
    (by intro s; rw [hφ₂]; norm_num) θ hθ.1 hθ.2.1 hθ.2.2
  have hA : Integrable A μ := c5_forward_square_mass_integrable hκ hh hhsmall ρ α hell y u G hu χ hχ hχc
  have hAB : Integrable (fun z => A z + B z) μ :=
    c5_forward_square_pairing_integrable hκ hr hh hhsmall ρ α hell y u G hu χ hχ hχc
  have hB : Integrable B μ := by
    convert hAB.sub hA using 1
    ext z
    simp
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.1) ∞ μ := by
    have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hηA : Integrable (fun z => η z.1 * A z) μ := by
    convert hA.mul_of_top_left hηtop using 1 <;> funext z <;> simp only [Pi.mul_apply, mul_comm]
  have hηB : Integrable (fun z => η z.1 * B z) μ := by
    convert hB.mul_of_top_left hηtop using 1 <;> funext z <;> simp only [Pi.mul_apply, mul_comm]
  rw [c5_quadratic_deriv, deriv_id'] at heq
  have heq' : (∫ z, η z.1 * A z ∂μ) + (∫ z, η z.1 * B z ∂μ) = 0 := by
    convert heq using 1
    congr 1
    · apply integral_congr_ae
      filter_upwards with z
      simp only [c5_quadratic_deriv, id_eq, θ, A, U, div_eq_mul_inv]
      ring
    · apply integral_congr_ae
      filter_upwards with z
      simp only [c5_quadratic_deriv, hφ₂, id_eq, θ, B, U, V,
        c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
          (hχ.differentiable (by simp))]
      simp [dot, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
  rw [← integral_add hηA hηB] at heq'
  have he : (fun z => η z.1 * A z + η z.1 * B z) =
      (fun z => η z.1 * (A z + B z)) := by funext z; ring
  rw [he] at heq'
  have hi : Integrable (fun z => η z.1 * (A z + B z)) μ := by
    convert hηA.add hηB using 1 <;> funext z <;> simp only [Pi.add_apply] <;> ring
  dsimp only [μ] at heq' hi
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at heq' hi
  rw [integral_prod _ hi] at heq'
  simpa only [integral_const_mul] using heq'

/-- The forward square pairing vanishes at almost every interior time. -/
theorem c5_weighted_caloric_forward_square_test {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hh1 : h ≤ 1/4)
    (y : Vec d) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall y r) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t+s,x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t+s,x)
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/2 : ℝ) (1/2)),
      (∫ x in sourceBall y r,
        ρ x * (h⁻¹ * (u (t+h,x) - u (t,x))) * (χ x ^ 2 * U t x) +
        dot ((α x).mulVec (V t x))
          (fun j => χ x ^ 2 * V t x j +
            2 * χ x * U t x * fderiv ℝ χ x (unitVector j))) = 0 := by
  have he : (-1 / 2 : ℝ) = -(1 / 2 : ℝ) := by ring
  rw [he]
  apply c11_temporal_pairing_ae_zero _
    (c5_forward_square_pairing_integrable_time hκ hr hh hh1 ρ α hell y u G hcal χ hχ hχc)
  intro η hη hηc hηs
  exact c5_forward_square_pairing_time_test hκ hr hh hh1 ρ α hell y u G hcal χ hχ hχc hχU η hη hηc hηs

end EinsteinFull.Calculus
