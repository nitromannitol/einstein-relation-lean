import EinsteinFull.Calculus.C13TubeWeightedRenormalization
import EinsteinFull.Calculus.C17TubeNonlinearTestApproximation

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- A squared smooth cutoff of the derivative of a bounded-second-derivative
nonlinearity has the literal weak gradient on almost every caloric slice. -/
theorem c11_weighted_caloric_squared_cutoff_deriv_slices {d : ℕ} {I : Set ℝ}
    {U : Set (Vec d)} [IsFiniteMeasure (volume.restrict U)]
    (hU : IsOpen U) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ 2 Φ) (M : ℝ) (hM : 0 ≤ M)
    (hΦ2 : ∀ r, |deriv (deriv Φ) r| ≤ M)
    (χ : Vec d → ℝ) (hχ : IsSpatialTest U χ) :
    ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => χ x ^ 2 * deriv Φ (u (t, x)))
        (fun x j => χ x ^ 2 * deriv (deriv Φ) (u (t, x)) * G (t, x) j +
          2 * χ x * deriv Φ (u (t, x)) * fderiv ℝ χ x (unitVector j)) ∧
      MemLp (fun x => χ x ^ 2 * deriv Φ (u (t, x))) 2 (volume.restrict U) ∧
      MemLp (fun x => euclideanNorm (fun j => χ x ^ 2 * deriv (deriv Φ) (u (t, x)) * G (t, x) j +
        2 * χ x * deriv Φ (u (t, x)) * fderiv ℝ χ x (unitVector j))) 2 (volume.restrict U) := by
  have hχeq : (fun x => χ x ^ 2) = χ * χ := by
    funext x
    simp only [pow_two, Pi.mul_apply]
  have hχ2 : IsSpatialTest U (fun x => χ x ^ 2) := by
    rw [hχeq]
    exact ⟨hχ.1.mul hχ.1, hχ.2.1.mul_right, tsupport_mul_subset_left.trans hχ.2.2⟩
  have hd (x : Vec d) (j : Fin d) :
      fderiv ℝ (fun x => χ x ^ 2) x (unitVector j) =
        2 * χ x * fderiv ℝ χ x (unitVector j) := by
    rw [hχeq]
    rw [fderiv_mul (hχ.1.differentiable (by simp) x) (hχ.1.differentiable (by simp) x)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have heq (t : ℝ) :
      (fun x => χ x ^ 2 • (deriv (deriv Φ) (u (t, x)) • G (t, x)) +
          deriv Φ (u (t, x)) • (fun j => fderiv ℝ (fun x => χ x ^ 2) x (unitVector j))) =
      (fun x j => χ x ^ 2 * deriv (deriv Φ) (u (t, x)) * G (t, x) j +
          2 * χ x * deriv Φ (u (t, x)) * fderiv ℝ χ x (unitVector j)) := by
    funext x j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd]
    ring
  filter_upwards [c13_weighted_caloric_cutoff_deriv_slices hU ρ α u G hu Φ hΦ M hM hΦ2 _ hχ2] with t ht
  simp_rw [congrFun (heq t)] at ht
  exact ht

/-- The literal nonlinear squared-cutoff test for forward Steklov averages
has its expected spatial weak gradient and L² bounds on almost every slice. -/
@[nolint unusedArguments]
theorem c11_weighted_forward_squared_cutoff_deriv_slices {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (y : Vec d) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ) (M : ℝ) (hM : 0 ≤ M)
    (hΦ2 : ∀ r, |deriv (deriv Φ) r| ≤ M)
    (χ : Vec d → ℝ) (hχ : IsSpatialTest (sourceBall y r) χ) :
    let U := fun t x => h⁻¹ * ∫ s in (0 : ℝ)..h, u (t + s, x)
    let V := fun t x => h⁻¹ • ∫ s in (0 : ℝ)..h, G (t + s, x)
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)),
      HasWeakGradient (sourceBall y r) (fun x => χ x ^ 2 * deriv Φ (U t x))
        (fun x j => χ x ^ 2 * deriv (deriv Φ) (U t x) * V t x j +
          2 * χ x * deriv Φ (U t x) * fderiv ℝ χ x (unitVector j)) ∧
      MemLp (fun x => χ x ^ 2 * deriv Φ (U t x)) 2 (volume.restrict (sourceBall y r)) ∧
      MemLp (fun x => euclideanNorm (fun j => χ x ^ 2 * deriv (deriv Φ) (U t x) * V t x j +
        2 * χ x * deriv Φ (U t x) * fderiv ℝ χ x (unitVector j))) 2
          (volume.restrict (sourceBall y r)) := by
  letI : IsFiniteMeasure (volume.restrict (sourceBall y r)) :=
    isFiniteMeasure_restrict.mpr (c18_sourceBall_measure_ne_top y r)
  have hnorm : Continuous (euclideanNorm (d := d)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hball : IsOpen (sourceBall y r) := by
    unfold sourceBall
    exact isOpen_lt (hnorm.comp (continuous_id.sub continuous_const)) continuous_const
  exact c11_weighted_caloric_squared_cutoff_deriv_slices hball ρ α _ _
    (c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu)
    Φ hΦ M hM hΦ2 χ hχ

/-- Every coordinate of a vector error inherits its L² convergence. -/
theorem c11_coordinate_tendsto_of_euclideanNorm {d : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (E : ℕ → Ω → Vec d)
    (hEm : ∀ n, AEStronglyMeasurable (E n) μ)
    (hE : ∀ n, MemLp (fun x => euclideanNorm (E n x)) 2 μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => euclideanNorm (E n x)) 2 μ)
      atTop (𝓝 0)) (i : Fin d) :
    (∀ n, MemLp (fun x => E n x i) 2 μ) ∧
      Tendsto (fun n => eLpNorm (fun x => E n x i) 2 μ) atTop (𝓝 0) := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => E n x i) μ :=
    (continuous_apply i).comp_aestronglyMeasurable (hEm n)
  have hb (n : ℕ) (x : Ω) : ‖E n x i‖ ≤ euclideanNorm (E n x) := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
      (PiLp.norm_apply_le (WithLp.toLp 2 (E n x)) i)
  refine ⟨fun n => (hE n).mono' (hm n) (Filter.Eventually.of_forall (hb n)), ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le)
  intro n
  apply eLpNorm_mono_ae (hm n)
  filter_upwards [] with x
  exact (hb n x).trans (le_abs_self _)

/-- L²-convergent vector errors have vanishing pairings with a fixed L² flux. -/
theorem c11_dot_error_tendsto_zero {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : ℕ → Ω → Vec d) (g : Ω → Vec d)
    (hEm : ∀ n, AEStronglyMeasurable (E n) μ)
    (hE : ∀ n, MemLp (fun x => euclideanNorm (E n x)) 2 μ)
    (ht : Tendsto (fun n => eLpNorm (fun x => euclideanNorm (E n x)) 2 μ)
      atTop (𝓝 0)) (hg : ∀ i, MemLp (fun x => g x i) 2 μ) :
    Tendsto (fun n => ∫ x, dot (E n x) (g x) ∂μ) atTop (𝓝 0) := by
  have hc (i : Fin d) := c11_coordinate_tendsto_of_euclideanNorm μ E hEm hE ht i
  have hlim (i : Fin d) : Tendsto (fun n => ∫ x, E n x i * g x i ∂μ) atTop (𝓝 0) :=
    c18_integral_mul_tendsto_zero_of_eLpNorm (μ := μ) (fun n x => E n x i) (fun x => g x i)
      (Filter.Eventually.of_forall (hc i).1) (hg i) (hc i).2
  have hs := tendsto_finset_sum Finset.univ (fun i _ => hlim i)
  simp only [Finset.sum_const_zero] at hs
  apply hs.congr'
  filter_upwards [] with n
  change (∑ i : Fin d, ∫ x, E n x i * g x i ∂μ) =
    ∫ x, ∑ i : Fin d, E n x i * g x i ∂μ
  symm
  exact integral_finsetSum _ (fun i _ => ((hc i).1 n).integrable_mul (hg i))

/-- Subtracting the derivative at zero supplies the normalized nonlinearity
needed by the spacetime approximation, without changing its derivative. -/
theorem c11_centered_deriv_admissible (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ)
    (M : ℝ) (hΦ2 : ∀ r, |deriv (deriv Φ) r| ≤ M) :
    ContDiff ℝ 1 (fun r => deriv Φ r - deriv Φ 0) ∧
    (deriv Φ 0 - deriv Φ 0 = 0) ∧
    (∀ r, |deriv (fun s => deriv Φ s - deriv Φ 0) r| ≤ M) := by
  have hd : ContDiff ℝ 1 (deriv Φ) := hΦ.deriv'
  refine ⟨hd.sub contDiff_const, sub_self _, ?_⟩
  intro r
  simpa only [deriv_sub_const] using hΦ2 r

/-- Passing a weak equation to a limit of scalar tests and their spatial gradients. -/
theorem c11_weak_pairing_limit {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (ψ a : Ω → ℝ) (H b : Ω → Vec d)
    (e : ℕ → Ω → ℝ) (E : ℕ → Ω → Vec d)
    (hψ : MemLp ψ 2 μ) (ha : MemLp a 2 μ)
    (hH : ∀ i, MemLp (fun x => H x i) 2 μ)
    (hb : ∀ i, MemLp (fun x => b x i) 2 μ)
    (he : ∀ n, MemLp (e n) 2 μ)
    (he0 : Tendsto (fun n => eLpNorm (e n) 2 μ) atTop (𝓝 0))
    (hEm : ∀ n, AEStronglyMeasurable (E n) μ)
    (hE : ∀ n, MemLp (fun x => euclideanNorm (E n x)) 2 μ)
    (hE0 : Tendsto (fun n => eLpNorm (fun x => euclideanNorm (E n x)) 2 μ)
      atTop (𝓝 0))
    (heq : ∀ n, (∫ x, (ψ x + e n x) * a x ∂μ) +
      (∫ x, dot (H x + E n x) (b x) ∂μ) = 0) :
    (∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ) = 0 := by
  have hs := c18_integral_mul_tendsto_zero_of_eLpNorm (μ := μ) e a (Filter.Eventually.of_forall he) ha he0
  have hv := c11_dot_error_tendsto_zero μ E b hEm hE hE0 hb
  have hHi : Integrable (fun x => dot (H x) (b x)) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ => (hH i).integrable_mul (hb i))
  have hEi (n : ℕ) : Integrable (fun x => dot (E n x) (b x)) μ := by
    exact integrable_finsetSum Finset.univ (fun i _ =>
      ((c11_coordinate_tendsto_of_euclideanNorm μ E hEm hE hE0 i).1 n).integrable_mul (hb i))
  have hconst (n : ℕ) :
      ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)) +
      ((∫ x, e n x * a x ∂μ) + (∫ x, dot (E n x) (b x) ∂μ)) = 0 := by
    have h := heq n
    simp only [add_mul, dot, Pi.add_apply, Finset.sum_add_distrib] at h
    have haadd : (∫ x, ψ x * a x + e n x * a x ∂μ) =
        (∫ x, ψ x * a x ∂μ) + (∫ x, e n x * a x ∂μ) := by
      simpa only [Pi.add_apply, Pi.mul_apply] using integral_add (hψ.integrable_mul ha) ((he n).integrable_mul ha)
    have hbadd : (∫ x, dot (H x) (b x) + dot (E n x) (b x) ∂μ) =
        (∫ x, dot (H x) (b x) ∂μ) + (∫ x, dot (E n x) (b x) ∂μ) := by
      simpa only [Pi.add_apply] using integral_add hHi (hEi n)
    rw [haadd] at h
    change (∫ x, ψ x * a x ∂μ) + (∫ x, e n x * a x ∂μ) +
      (∫ x, dot (H x) (b x) + dot (E n x) (b x) ∂μ) = 0 at h
    rw [hbadd] at h
    linarith
  have ht : Tendsto (fun n : ℕ =>
      ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)) +
      ((∫ x, e n x * a x ∂μ) + (∫ x, dot (E n x) (b x) ∂μ)))
      atTop (𝓝 ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ))) := by
    simpa only [add_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        (∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)) atTop
          (𝓝 ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)))).add (hs.add hv))
  have hz : Tendsto (fun n : ℕ =>
      ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)) +
      ((∫ x, e n x * a x ∂μ) + (∫ x, dot (E n x) (b x) ∂μ)))
      atTop (𝓝 0) := by
    have heq' : (fun n : ℕ =>
        ((∫ x, ψ x * a x ∂μ) + (∫ x, dot (H x) (b x) ∂μ)) +
        ((∫ x, e n x * a x ∂μ) + (∫ x, dot (E n x) (b x) ∂μ))) =
        (fun _ : ℕ => (0 : ℝ)) := funext hconst
    rw [heq']
    exact tendsto_const_nhds
  exact tendsto_nhds_unique ht hz

/-- Vanishing against all interior time tests gives a single almost-everywhere
statement for the resulting spatial pairing. -/
theorem c11_temporal_pairing_ae_zero {a b : ℝ} (q : ℝ → ℝ)
    (hq : Integrable q (volume.restrict (Set.Ioo a b)))
    (htest : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      (∫ t in Set.Ioo a b, η t * q t) = 0) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b), q t = 0 := by
  apply (ae_restrict_iff' measurableSet_Ioo).2
  apply isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (show IntegrableOn q (Set.Ioo a b) volume from hq).locallyIntegrableOn
  intro η hη hηc hηs
  have he : (Set.Ioo a b).indicator (fun t => η t * q t) =
      (fun t => η t * q t) := by
    apply Set.indicator_eq_self.mpr
    intro t ht
    apply hηs (subset_closure ?_)
    exact left_ne_zero_of_mul ht
  change (∫ t, η t * q t) = 0
  rw [← he, integral_indicator measurableSet_Ioo]
  exact htest η hη hηc hηs

/-- The weighted forward difference and every coordinate of the averaged
flux are square integrable on the smaller cylinder. -/
theorem c11_forward_weak_coefficients_memLp {d : ℕ} {κ h r : ℝ}
    (hκ : 0 < κ) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G) :
    let μ := (volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
    MemLp (fun z => ρ z.2 * ((u (z.1 + h, z.2) - u z) / h)) 2 μ ∧
    ∀ i, MemLp (fun z => ((α z.2).mulVec
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2))) i) 2 μ := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  have hc := c18_elliptic_coefficients_comp_memLp_top μ Prod.snd
    measurable_snd.aemeasurable hκ hell
  have hd := c18_weighted_caloric_forward_difference_memLp hh hhsmall ρ α y u G hu
  have hG := c18_memLp_forward_average (c18_sourceBall_measurable y r) hh hhsmall
    (c18_weighted_caloric_gradient_memLp ρ α u G hu)
  refine ⟨hc.1.mul hd, ?_⟩
  intro i
  have hαG (j : Fin d) : MemLp (fun z : ℝ × Vec d =>
      α z.2 i j * (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)) j) 2 μ :=
    (hc.2 i j).mul (hG.eval j)
  have hs := memLp_finsetSum Finset.univ (fun j _ => hαG j)
  simpa only [Matrix.mulVec, dotProduct] using hs

/-- The forward difference equation tested with a nonlinear cutoff of the
Steklov average, with its literal spatial gradient. -/
@[nolint unusedArguments]
theorem c11_weighted_forward_nonlinear_spacetime_test {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (y : Vec d) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ 2 Φ) (M : ℝ) (hM : 0 ≤ M)
    (hΦ2 : ∀ s, |deriv (deriv Φ) s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ)
    (hθs : tsupport θ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    let U := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let V := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * ((u (z.1 + h, z.2) - u z) / h) * (θ z * deriv Φ (U z))) +
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      dot ((α z.2).mulVec (V z))
        (θ z • (deriv (deriv Φ) (U z) • V z) +
          deriv Φ (U z) • (fun j => fderiv ℝ θ z (0, unitVector j)))) = 0 := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict
    (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
  letI := c18_smallSourceCylinder_isFiniteMeasure y r
  let U : ℝ × Vec d → ℝ := fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
  let V : ℝ × Vec d → Vec d := fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
  let F : ℝ → ℝ := deriv Φ
  have hF : ContDiff ℝ 1 F := hΦ.deriv'
  have hcal := c18_weighted_caloric_forward_steklov hκ hh hhsmall ρ α hell y u G hu
  change IsWeightedCaloric ρ α _ _ U V at hcal
  obtain ⟨v, hv, hv0, hv1⟩ := c17_nonlinear_spacetime_test_approximation_at_center
    U V hcal.1 hcal.2.1 hcal.2.2.1
    hcal.2.2.2.1 F hF M hM hΦ2 θ hθ hθc hθs
  let Q : ℝ → ℝ := fun s => F s - F 0
  have hQ : ContDiff ℝ 1 Q := hF.sub contDiff_const
  have hQder (s : ℝ) : deriv Q s = deriv F s := by simp [Q, deriv_sub_const]
  have hq : MemLp (fun z => Q (U z)) 2 μ := by
    change MemLp (Q ∘ U) 2 μ
    exact (PDE.lipschitzWith_of_abs_deriv_le hM (hQ.differentiable (by simp))
      (fun s => by simpa only [hQder] using hΦ2 s)).comp_memLp (by simp [Q]) hcal.1
  have hf : MemLp (fun z => F (U z)) 2 μ := by
    have hc : MemLp (fun _ : ℝ × Vec d => F 0) 2 μ := memLp_const _
    convert hq.add hc using 1
    ext z
    simp [Q]
  have hθtop : MemLp θ ⊤ μ := hθ.continuous.memLp_top_of_hasCompactSupport hθc μ
  have hψ : MemLp (fun z => θ z * F (U z)) 2 μ := by
    simpa only [mul_comm] using hf.fun_mul hθtop
  have hderm : AEStronglyMeasurable (fun z => deriv F (U z)) μ :=
    hF.continuous_deriv_one.comp_aestronglyMeasurable hcal.1.aestronglyMeasurable
  have hdertop : MemLp (fun z => deriv F (U z)) ⊤ μ := by
    apply memLp_top_of_bound hderm M
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hΦ2 (U z)
  let D : ℝ × Vec d → Vec d := fun z j => fderiv ℝ θ z (0, unitVector j)
  have hDtop (j : Fin d) : MemLp (fun z => D z j) ⊤ μ := by
    have hc : Continuous (fun z => D z j) := by
      dsimp [D]
      exact ((contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const).continuous
    exact hc.memLp_top_of_hasCompactSupport (hθc.fderiv_apply ℝ (0, unitVector j)) μ
  have hcoord (j : Fin d) : MemLp (fun z => V z j) 2 μ := by
    apply hcal.2.2.1.mono' ((continuous_apply j).comp_aestronglyMeasurable hcal.2.1)
    exact ae_of_all _ fun z => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (V z)) j)
  let H : ℝ × Vec d → Vec d := fun z => θ z • (deriv F (U z) • V z) + F (U z) • D z
  have hHi (j : Fin d) : MemLp (fun z => H z j) 2 μ := by
    have h1 : MemLp (fun z => deriv F (U z) * V z j) 2 μ := by
      simpa only [mul_comm] using (hcoord j).fun_mul hdertop
    have h2 : MemLp (fun z => θ z * (deriv F (U z) * V z j)) 2 μ := by
      simpa only [mul_comm] using h1.fun_mul hθtop
    convert h2.add (hf.fun_mul (hDtop j)) using 1
  have hvec : MemLp (fun z => (WithLp.toLp 2 (H z) : EuclideanSpace ℝ (Fin d))) 2 μ :=
    memLp_piLp_iff.mpr hHi
  have hH : MemLp (fun z => euclideanNorm (H z)) 2 μ := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hvec.norm
  have hHm : AEStronglyMeasurable H μ :=
    (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable hvec.aestronglyMeasurable
  exact c18_weighted_caloric_forward_difference_of_test_approximation hκ hh hhsmall
    ρ α y hell u G hu _ _ hψ hHm hH v hv hv0 hv1

end EinsteinFull.Calculus
