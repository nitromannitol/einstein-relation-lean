import EinsteinFull.Calculus.C5TubeForwardSquareTest
import EinsteinFull.Calculus.C13TubeWeightedEnergyTrace
import EinsteinFull.Calculus.C13TubeGeneralChainAssembly
import EinsteinFull.Calculus.C18TubeNonlinearCompactTimeLimits
import EinsteinFull.Calculus.C20TubeNonlinearWeakPairingLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

/-- A weighted caloric solution remains caloric on a smaller time set. -/
theorem c5_weighted_caloric_time_mono {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {I J : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U) (hJI : J ⊆ I)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) : IsWeightedCaloric ρ α J U u G := by
  have hsub : J ×ˢ U ⊆ I ×ˢ U := Set.prod_mono hJI Set.Subset.rfl
  have hmeasure := Measure.restrict_mono_set (volume : Measure (ℝ × Vec d)) hsub
  refine ⟨hu.1.mono_measure hmeasure, hu.2.1.mono_measure hmeasure,
    hu.2.2.1.mono_measure hmeasure, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hJI hu.2.2.2.1
  · intro ψ hψ hc hs
    have hs' : tsupport ψ ⊆ interior I ×ˢ U :=
      hs.trans (Set.prod_mono (interior_mono hJI) Set.Subset.rfl)
    have hz (z : ℝ × Vec d) (hz : z ∈ (I ×ˢ U) \ (J ×ˢ U)) :
        fderiv ℝ ψ z = 0 := by
      apply fderiv_of_notMem_tsupport ℝ
      intro hz'
      have hh := hs hz'
      exact hz.2 ⟨interior_subset hh.1, hh.2⟩
    have heq : (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      ∫ z in J ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.prod hU) hsub
      intro z hz'
      simp [hz z hz', dot]
    rw [← heq]
    exact hu.2.2.2.2 ψ hψ hc hs'

/-- A bounded time multiplier can be moved through the spatial integral of
an integrable spacetime function on a product cylinder. -/
theorem c5_integral_time_multiplier_spacetime {d : ℕ} (I : Set ℝ)
    (U : Set (Vec d)) (f : ℝ × Vec d → ℝ)
    (hf : Integrable f (volume.restrict (I ×ˢ U)))
    (w : ℝ → ℝ) (hw : MemLp (fun z : ℝ × Vec d => w z.1) ∞
      (volume.restrict (I ×ˢ U))) :
    (∫ z in I ×ˢ U, w z.1 * f z) =
      ∫ t in I, w t * ∫ x in U, f (t, x) := by
  have hfw : Integrable (fun z : ℝ × Vec d => w z.1 * f z)
      (volume.restrict (I ×ˢ U)) := by
    convert hf.mul_of_top_left hw using 1 <;> funext z <;> simp only [Pi.mul_apply, mul_comm]
  have hp : (volume.restrict I).prod (volume.restrict U) =
      (volume : Measure (ℝ × Vec d)).restrict (I ×ˢ U) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hp] at hfw ⊢
  rw [integral_prod _ hfw]
  apply integral_congr_ae
  filter_upwards with t
  rw [integral_const_mul]

/-- The spacetime and time-sliced forms of a distributional energy balance
are equivalent when the two actual integrands are integrable. -/
theorem c5_spacetime_balance_iff_time_sliced {d : ℕ} (I : Set ℝ)
    (U : Set (Vec d)) (mass flux : ℝ × Vec d → ℝ)
    (hmass : Integrable mass (volume.restrict (I ×ˢ U)))
    (hflux : Integrable flux (volume.restrict (I ×ˢ U)))
    (w v : ℝ → ℝ)
    (hw : MemLp (fun z : ℝ × Vec d => w z.1) ∞ (volume.restrict (I ×ˢ U)))
    (hv : MemLp (fun z : ℝ × Vec d => v z.1) ∞ (volume.restrict (I ×ˢ U))) :
    (∫ z in I ×ˢ U, w z.1 * mass z) =
        2 * (∫ z in I ×ˢ U, v z.1 * flux z) ↔
      (∫ t in I, w t * ∫ x in U, mass (t, x)) =
        2 * (∫ t in I, v t * ∫ x in U, flux (t, x)) := by
  rw [c5_integral_time_multiplier_spacetime I U mass hmass w hw,
    c5_integral_time_multiplier_spacetime I U flux hflux v hv]

/-- The time derivative of a separated square cutoff retains the literal
one-dimensional time derivative. -/
theorem c5_separated_square_cutoff_time_fderiv {d : ℕ}
    (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    (χ : Vec d → ℝ) (hχ : Differentiable ℝ χ) (z : ℝ × Vec d) :
    fderiv ℝ (fun w : ℝ × Vec d => η w.1 * χ w.2 ^ 2) z (1, 0) =
      deriv η z.1 * χ z.2 ^ 2 := by
  have h1 := (hη z.1).hasFDerivAt.comp z (hasFDerivAt_fst (𝕜 := ℝ))
  have h2 := (hχ z.2).hasFDerivAt.comp z (hasFDerivAt_snd (𝕜 := ℝ))
  have h3 := h1.mul (h2.mul h2)
  change HasFDerivAt (fun w : ℝ × Vec d => η w.1 * (χ w.2 * χ w.2)) _ z at h3
  have heq : (fun w : ℝ × Vec d => η w.1 * χ w.2 ^ 2) =
      (fun w : ℝ × Vec d => η w.1 * (χ w.2 * χ w.2)) := by
    funext w
    rw [pow_two]
  rw [heq, h3.fderiv]
  simp [fderiv_apply_one_eq_deriv] <;> ring

/-- The square-test flux is the cutoff energy plus its signed cross term. -/
theorem c5_square_cutoff_flux_identity {d : ℕ} (α : Mat d) (V D : Vec d)
    (η χ u : ℝ) :
    dot (α.mulVec V) (fun j => η * (χ ^ 2 * V j + 2 * χ * u * D j)) =
      η * (χ ^ 2 * dot (α.mulVec V) V + 2 * χ * u * dot (α.mulVec V) D) := by
  simp only [dot, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring


/-- The forward averages obey the weighted square balance on the unit cylinder. -/
theorem c5_forward_square_spacetime_balance {d : ℕ} {κ r h : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    let U := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)
    let V := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1 + s, z.2)
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * U z ^ 2)) =
    2 * (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      η z.1 * (χ z.2 ^ 2 * dot ((α z.2).mulVec (V z)) (V z) +
      2 * χ z.2 * U z * dot ((α z.2).mulVec (V z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))) := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hθ := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have hF : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hF2 : deriv (deriv (fun s : ℝ => s ^ 2 / 2)) = fun _ => (1 : ℝ) := by
    rw [c5_quadratic_deriv]
    funext s
    simp
  have he := c13_weighted_forward_C2_renormalized_identity hκ hr hh hhsmall
    ρ α hell y u G hu (fun s : ℝ => s ^ 2 / 2) hF 1 (by norm_num)
    (by intro s; rw [hF2]; norm_num) θ hθ.1 hθ.2.1 hθ.2.2
  rw [hF2, c5_quadratic_deriv] at he
  dsimp only at he ⊢
  have ht : (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      ρ z.2 * ((h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) ^ 2 / 2) *
        fderiv ℝ θ z (1, 0)) =
      (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      (deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 *
        (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) ^ 2)) / 2) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [show fderiv ℝ θ z (1, 0) = deriv η z.1 * χ z.2 ^ 2 from
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp)) z]
    ring
  rw [ht, integral_div] at he
  have hf : (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
        (θ z • (1 • (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) +
          (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) •
            (fun j => fderiv ℝ θ z (0, unitVector j)))) =
      (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      η z.1 * (χ z.2 ^ 2 * dot ((α z.2).mulVec
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) +
        2 * χ z.2 * (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (fun j => fderiv ℝ χ z.2 (unitVector j)))) := by
    apply integral_congr_ae
    filter_upwards with z
    simp only [θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp))]
    convert c5_square_cutoff_flux_identity (α z.2)
      (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))
      (fun j => fderiv ℝ χ z.2 (unitVector j)) (η z.1) (χ z.2)
      (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) using 1 <;>
      congr 2 <;> funext j <;> simp <;> ring
  simp only [id_eq, one_smul] at he hf
  rw [hf] at he
  linarith


/-- An actual weighted spacetime square balance yields its time-sliced form. -/
theorem c5_weighted_square_time_slice_of_spacetime {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hs : (∫ z in I ×ˢ U, deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)) =
      2 * ∫ z in I ×ˢ U, η z.1 *
        (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
          2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
            (fun j => fderiv ℝ χ z.2 (unitVector j)))) :
    (∫ t in I, deriv η t * ∫ x in U, ρ x * χ x ^ 2 * u (t,x) ^ 2) =
      2 * ∫ t in I, η t * ∫ x in U,
        χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
          2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
  let μ : Measure (ℝ × Vec d) := volume.restrict (I ×ˢ U)
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.1) ∞ μ := by
    have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hdtop : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞ μ := by
    have ht := (hη.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hηc.deriv (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  exact (c5_spacetime_balance_iff_time_sliced I U
    (fun z => ρ z.2 * χ z.2 ^ 2 * u z ^ 2)
    (fun z => χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
    (c13_weighted_cutoff_mass_integrable hκ ρ α hell I U u G hu χ hχ hχc)
    (c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell I U u G hu χ hχ hχc)
    (deriv η) η hdtop hηtop).mp hs


/-- The quadratic renormalized weak equation gives the square balance for a
separated test on any caloric cylinder. -/
theorem c5_weighted_square_balance_of_quadratic_renormalized {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (I : Set ℝ) (U : Set (Vec d))
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α I U u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hr : let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2;
      -(∫ z in I ×ˢ U, ρ z.2 * (u z ^ 2 / 2) * fderiv ℝ θ z (1, 0)) +
      (∫ z in I ×ˢ U, dot ((α z.2).mulVec (G z))
        (θ z • G z + u z • (fun j => fderiv ℝ θ z (0, unitVector j)))) = 0) :
    (∫ t in I, deriv η t * ∫ x in U, ρ x * χ x ^ 2 * u (t,x) ^ 2) =
      2 * ∫ t in I, η t * ∫ x in U,
        χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
          2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
  apply c5_weighted_square_time_slice_of_spacetime hκ ρ α hell I U u G hu χ hχ hχc η hη hηc
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  dsimp only at hr
  have ht : (∫ z in I ×ˢ U, ρ z.2 * (u z ^ 2 / 2) * fderiv ℝ θ z (1, 0)) =
      (∫ z in I ×ˢ U, (deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)) / 2) := by
    apply integral_congr_ae
    filter_upwards with z
    rw [show fderiv ℝ θ z (1, 0) = deriv η z.1 * χ z.2 ^ 2 from
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp)) z]
    ring
  have hf : (∫ z in I ×ˢ U, dot ((α z.2).mulVec (G z))
        (θ z • G z + u z • (fun j => fderiv ℝ θ z (0, unitVector j)))) =
      (∫ z in I ×ˢ U, η z.1 * (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
        2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)))) := by
    apply integral_congr_ae
    filter_upwards with z
    simp only [θ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp))]
    convert c5_square_cutoff_flux_identity (α z.2) (G z)
      (fun j => fderiv ℝ χ z.2 (unitVector j)) (η z.1) (χ z.2) (u z) using 1 <;>
      congr 2 <;> funext j <;> simp <;> ring
  change -(∫ z in I ×ˢ U, ρ z.2 * (u z ^ 2 / 2) * fderiv ℝ θ z (1, 0)) + _ = 0 at hr
  rw [ht, integral_div, hf] at hr
  linarith


/-- The mass and gradient-energy terms for a separated square cutoff have the
actual compact-interval forward-average limits. -/
theorem c5_square_cutoff_mass_gradient_limits {d : ℕ} {κ r a b : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b) :
    let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * (uh h z ^ 2 / 2)) * fderiv ℝ θ z (1,0))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1,0))) ∧
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      dot ((α z.2).mulVec (Gh h z)) (Gh h z) * θ z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
        dot ((α z.2).mulVec (G z)) (G z) * θ z)) := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hθ := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have hF : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hF2 : deriv (deriv (fun s : ℝ => s ^ 2 / 2)) = fun _ => (1 : ℝ) := by
    rw [c5_quadratic_deriv]
    funext s
    simp
  have hb : ∀ s, |deriv (deriv (fun s : ℝ => s ^ 2 / 2)) s| ≤ (1 : ℝ) := by
    intro s
    rw [hF2]
    norm_num
  dsimp only
  constructor
  · exact c18_weighted_forward_nonlinear_scalar_limit_compact hκ hab ρ α hell y u hu.1
      (fun s : ℝ => s ^ 2 / 2) hF 1 (by norm_num) hb θ hθ.1 hθ.2.1 hθ.2.2
  · have ht := c20_weighted_forward_nonlinear_gradient_energy_integral_limit_compact
      hκ hr hab ρ α hell y u G hu.1 hu.2.1 hu.2.2.1
      (fun s : ℝ => s ^ 2 / 2) hF 1 (by norm_num) hb θ hθ.1 hθ.2.1 hθ.2.2
    simpa only [hF2, one_mul] using ht


/-- The signed cross term in the square-cutoff flux converges in L¹ under
forward averaging on an arbitrary time interval. -/
theorem c5_square_cutoff_cross_limit {d : ℕ} {κ r a b : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b) :
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      |2 * η z.1 * χ z.2 * uh h z * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)) -
       2 * η z.1 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j))|) (𝓝[>] 0) (𝓝 0) := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have hθ := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have hF : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hF2 : deriv (deriv (fun s : ℝ => s ^ 2 / 2)) = fun _ => (1 : ℝ) := by
    rw [c5_quadratic_deriv]
    funext s
    simp
  have hb : ∀ s, |deriv (deriv (fun s : ℝ => s ^ 2 / 2)) s| ≤ (1 : ℝ) := by
    intro s
    rw [hF2]
    norm_num
  have ht := c18_weighted_forward_nonlinear_flux_derivative_limit_compact
    hκ hr hab ρ α hell y u G hu.1 hu.2.1 hu.2.2.1
    (fun s : ℝ => s ^ 2 / 2) hF 1 (by norm_num) hb θ hθ.1 hθ.2.1 hθ.2.2
  rw [c5_quadratic_deriv] at ht
  dsimp only at ht ⊢
  convert ht using 1
  funext h
  apply integral_congr_ae
  filter_upwards with z
  simp only [id_eq, θ, c5_separated_square_cutoff_fderiv η
    (hη.differentiable (by simp)) χ (hχ.differentiable (by simp))]
  simp only [dot, Finset.mul_sum]
  congr 1
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring

/-- The arbitrary-interval averaged quadratic pairing required for square balance. -/
@[nolint defsWithUnderscore]
def c5_forward_square_pairing_zero {d : ℕ} {r a b : ℝ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (y : Vec d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (χ : Vec d → ℝ) (η : ℝ → ℝ) : Prop :=
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  ∀ᶠ h : ℝ in 𝓝[>] 0,
    let uh := fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    (∫ z in Set.Ioo a b ×ˢ sourceBall y r,
      -(ρ z.2 * (uh z ^ 2 / 2)) * fderiv ℝ θ z (1,0) +
      uh z * dot ((α z.2).mulVec (Gh z))
        (fun j => fderiv ℝ θ z (0,unitVector j)) +
      dot ((α z.2).mulVec (Gh z)) (Gh z) * θ z) = 0

/-- The checked averaged limits turn the forward pairing identity into the
quadratic distributional balance on any time interval. -/
theorem c5_weighted_square_balance_of_forward_pairing {d : ℕ} {κ r a b : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b)
    (hfwd : c5_forward_square_pairing_zero (r := r) (a := a) (b := b) ρ α y u G χ η) :
    (∫ t in Set.Ioo a b, deriv η t * ∫ x in sourceBall y r, ρ x * χ x ^ 2 * u (t,x) ^ 2) =
      2 * ∫ t in Set.Ioo a b, η t * ∫ x in sourceBall y r,
        χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
          2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
            (fun j => fderiv ℝ χ x (unitVector j)) := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  let S : Set (ℝ × Vec d) := Set.Ioo a b ×ˢ sourceBall y r
  let A : ℝ × Vec d → ℝ := fun z => deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)
  let B : ℝ × Vec d → ℝ := fun z => η z.1 *
    (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
  have hθ := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have hF : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hF2 : deriv (deriv (fun s : ℝ => s ^ 2 / 2)) = fun _ => (1 : ℝ) := by
    rw [c5_quadratic_deriv]
    funext s
    simp
  have hlim := c20_weighted_forward_nonlinear_weak_pairing_limit_compact hκ hr hab
    ρ α hell y u G hu.1 hu.2.1 hu.2.2.1 (fun s : ℝ => s ^ 2 / 2) hF 1
    (by norm_num) (by intro s; rw [hF2]; norm_num) θ hθ.1 hθ.2.1 hθ.2.2
  rw [hF2, c5_quadratic_deriv] at hlim
  simp only [id_eq, one_mul] at hlim
  have hz := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hfwd.mono fun _ h => h.symm))
  have hdtop : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞ (volume.restrict S) := by
    have ht := (hη.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hηc.deriv (Measure.map Prod.fst (volume.restrict S))
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.1) ∞ (volume.restrict S) := by
    have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc
      (Measure.map Prod.fst (volume.restrict S))
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hA : Integrable A (volume.restrict S) := by
    convert (c13_weighted_cutoff_mass_integrable hκ ρ α hell _ _ u G hu χ hχ hχc).mul_of_top_left hdtop using 1 <;> funext z <;> simp [A, mul_comm]
  have hB : Integrable B (volume.restrict S) := by
    convert (c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell _ _ u G hu χ hχ hχc).mul_of_top_left hηtop using 1 <;> funext z <;> simp [B, mul_comm]
  have heq : (fun z => -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1,0) +
      u z * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ θ z (0,unitVector j)) +
      dot ((α z.2).mulVec (G z)) (G z) * θ z) = fun z => -A z / 2 + B z := by
    funext z
    rw [show fderiv ℝ θ z (1,0) = deriv η z.1 * χ z.2 ^ 2 from
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp)) z]
    have hc : u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ θ z (0,unitVector j)) =
      (2 * η z.1 * χ z.2 * u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
      simp only [θ, c5_separated_square_cutoff_fderiv η
        (hη.differentiable (by simp)) χ (hχ.differentiable (by simp)), dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hc]
    dsimp [A, B, θ]
    ring
  change (∫ z in S, -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1,0) +
      u z * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ θ z (0,unitVector j)) +
      dot ((α z.2).mulVec (G z)) (G z) * θ z) = 0 at hz
  rw [heq] at hz
  have hi := integral_add (hA.neg.div_const 2) hB
  simp only [Pi.add_apply, Pi.div_apply, Pi.neg_apply] at hi
  rw [hi, integral_div, integral_neg] at hz
  apply c5_weighted_square_time_slice_of_spacetime hκ ρ α hell _ _ u G hu χ hχ hχc η hη hηc
  change (∫ z in S, A z) = 2 * ∫ z in S, B z
  linarith

/-- The square pairing is unchanged when the time domain is enlarged beyond
    the support of the time test. -/
theorem c5_square_pairing_restrict_time {d : ℕ} {a b c e : ℝ}
    (hsub : Set.Ioo c e ⊆ Set.Ioo a b) (U : Set (Vec d)) (hU : MeasurableSet U)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (χ : Vec d → ℝ) (η : ℝ → ℝ) (hη : Differentiable ℝ η)
    (hχ : Differentiable ℝ χ) (hs : tsupport η ⊆ Set.Ioo c e) :
    let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
    (∫ z in Set.Ioo a b ×ˢ U,
      -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1,0) +
      u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ θ z (0,unitVector j)) +
      dot ((α z.2).mulVec (G z)) (G z) * θ z) =
    ∫ z in Set.Ioo c e ×ˢ U,
      -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1,0) +
      u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ θ z (0,unitVector j)) +
      dot ((α z.2).mulVec (G z)) (G z) * θ z := by
  dsimp only
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (measurableSet_Ioo.prod hU) (Set.prod_mono hsub Set.Subset.rfl)
  intro z hz
  have hnot : z.1 ∉ tsupport η := by
    intro ht
    exact hz.2 ⟨hs ht, hz.1.2⟩
  have he : η z.1 = 0 := image_eq_zero_of_notMem_tsupport hnot
  have hd : deriv η z.1 = 0 := deriv_of_notMem_tsupport hnot
  have hspace : (fun j => fderiv ℝ (fun w : ℝ × Vec d => η w.1 * χ w.2 ^ 2)
      z (0, unitVector j)) = 0 := by
    funext j
    rw [c5_separated_square_cutoff_fderiv η hη χ hχ]
    simp [he]
  rw [c5_separated_square_cutoff_time_fderiv η hη χ hχ, hspace]
  simp [he, hd, dot]

/-- The forward square pairing vanishes for tests supported in the middle
    half of the caloric time interval. -/
theorem c5_forward_square_pairing_zero_of_middle_support {d : ℕ} {κ r a b : ℝ}
    (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχs : tsupport χ ⊆ sourceBall y r)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hmid : tsupport η ⊆ Set.Ioo ((a+b)/2 - ((b-a)/2)/2)
      ((a+b)/2 + ((b-a)/2)/2)) :
    c5_forward_square_pairing_zero (r := r) (a := a) (b := b) ρ α y u G χ η := by
  let l : ℝ := (a+b)/2 - ((b-a)/2)/2
  let v : ℝ := (a+b)/2 + ((b-a)/2)/2
  have hsub : Set.Ioo l v ⊆ Set.Ioo a b := by
    intro t ht
    dsimp [l, v] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hηs : tsupport η ⊆ Set.Ioo a b := hmid.trans hsub
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  have ht := c5_separated_square_cutoff η hη hηc hηs χ hχ hχc hχs
  have htm := c5_separated_square_cutoff η hη hηc hmid χ hχ hχc hχs
  have hF : ContDiff ℝ 2 (fun s : ℝ => s ^ 2 / 2) := by fun_prop
  have hd : ∀ q, |deriv (deriv (fun s : ℝ => s ^ 2 / 2)) q| ≤ (1 : ℝ) := by
    intro q
    rw [c5_quadratic_deriv]
    simp
  have hz := c13_physical_middle_forward_C2_eventually_zero hκ hr hab ρ α hell
    y u G hu (fun s => s ^ 2 / 2) hF 1 (by norm_num) hd θ ht.1 ht.2.1 ht.2.2 htm.2.2
  have hU : MeasurableSet (sourceBall y r) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall y hr]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  filter_upwards [hz] with h hh
  have hrestrict := c5_square_pairing_restrict_time hsub (sourceBall y r) hU ρ α
    (fun z => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))
    (fun z => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))
    χ η (hη.differentiable (by simp)) (hχ.differentiable (by simp)) hmid
  dsimp only [c5_forward_square_pairing_zero]
  rw [hrestrict]
  simpa [c5_quadratic_deriv] using hh

/-- The quadratic renormalization identity yields the distributional square balance. -/
theorem c5_weighted_square_distributional_balance {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b, deriv η t *
      ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * u (t,x) ^ 2) =
    2 * ∫ t in Set.Ioo a b, η t * ∫ x in sourceBall 0 R,
      χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
      2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
        (fun j => fderiv ℝ χ x (unitVector j)) := by
  let θ : ℝ × Vec d → ℝ := fun z => η z.1 * χ z.2 ^ 2
  obtain ⟨hθ, hθc, hθs⟩ := c5_separated_square_cutoff η hη hηc hηI χ hχ hχc hχU
  have hF : ContDiff ℝ 2 (fun q : ℝ => q ^ 2 / 2) := by fun_prop
  have hder : ∀ q : ℝ, |deriv (deriv (fun q : ℝ => q ^ 2 / 2)) q| ≤ 1 := by
    intro q
    rw [c5_quadratic_deriv]
    simp
  have hren := c13_actual_weighted_caloric_renormalization hκ hR hab ρ α hell u G hcal
    (fun q : ℝ => q ^ 2 / 2) hF (by norm_num) 1 (by norm_num) hder θ hθ hθc hθs
  have hdid : deriv id = fun _ : ℝ => 1 := by
    funext x
    exact (hasDerivAt_id x).deriv
  simp only [c5_quadratic_deriv, hdid, id_eq, one_mul] at hren
  let μ : Measure (ℝ × Vec d) := volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)
  let A : ℝ × Vec d → ℝ := fun z => deriv η z.1 * (ρ z.2 * χ z.2 ^ 2 * u z ^ 2)
  let B : ℝ × Vec d → ℝ := fun z => η z.1 *
    (χ z.2 ^ 2 * dot ((α z.2).mulVec (G z)) (G z) +
      2 * χ z.2 * u z * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ χ z.2 (unitVector j)))
  have hηtop : MemLp (fun z : ℝ × Vec d => η z.1) ∞ μ := by
    have ht := hη.continuous.memLp_top_of_hasCompactSupport hηc (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hdtop : MemLp (fun z : ℝ × Vec d => deriv η z.1) ∞ μ := by
    have ht := (hη.continuous_deriv (by simp)).memLp_top_of_hasCompactSupport
      hηc.deriv (Measure.map Prod.fst μ)
    exact ht.comp_of_map measurable_fst.aemeasurable
  have hA : Integrable A μ := by
    convert (c13_weighted_cutoff_mass_integrable hκ ρ α hell _ _ u G hcal χ hχ hχc).mul_of_top_left hdtop using 1
    funext z
    simp [A, Pi.mul_apply, mul_comm]
  have hB : Integrable B μ := by
    convert (c13_weighted_cutoff_energy_flux_integrable hκ ρ α hell _ _ u G hcal χ hχ hχc).mul_of_top_left hηtop using 1
    funext z
    simp [B, Pi.mul_apply, mul_comm]
  have hpoint (z : ℝ × Vec d) :
      -(ρ z.2 * (u z ^ 2 / 2)) * fderiv ℝ θ z (1, 0) +
        u z * dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ θ z (0, unitVector j)) +
        dot ((α z.2).mulVec (G z)) (G z) * θ z = -(A z / 2) + B z := by
    rw [show fderiv ℝ θ z (1, 0) = deriv η z.1 * χ z.2 ^ 2 from
      c5_separated_square_cutoff_time_fderiv η (hη.differentiable (by simp)) χ
        (hχ.differentiable (by simp)) z]
    simp only [θ, c5_separated_square_cutoff_fderiv η (hη.differentiable (by simp)) χ
      (hχ.differentiable (by simp))]
    have hd : dot ((α z.2).mulVec (G z))
        (fun j => η z.1 * (2 * χ z.2 * fderiv ℝ χ z.2 (unitVector j))) =
        (2 * η z.1 * χ z.2) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ χ z.2 (unitVector j)) := by
      simp only [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hd]
    dsimp [A, B]
    ring
  have hz : (∫ z, -(A z / 2) + B z ∂μ) = 0 := by
    convert hren using 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => (hpoint z).symm)
  change (∫ z, (-(fun z => A z / 2)) z + B z ∂μ) = 0 at hz
  rw [integral_add (hA.div_const _).neg hB] at hz
  simp only [Pi.neg_apply] at hz
  rw [integral_neg, integral_div] at hz
  apply c5_weighted_square_time_slice_of_spacetime hκ ρ α hell _ _ u G hcal χ hχ hχc η hη hηc
  change (∫ z, A z ∂μ) = 2 * ∫ z, B z ∂μ
  linarith

end EinsteinFull.Calculus
