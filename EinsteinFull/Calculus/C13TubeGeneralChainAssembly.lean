import EinsteinFull.Calculus.C13TubeWeightedEnergyTrace
import EinsteinFull.Calculus.C13TubeEllipticityTransport
import EinsteinFull.Calculus.C20TubeNonlinearWeakPairingLimit
import EinsteinFull.Calculus.C20TubeFiniteTestLocalization
import EinsteinFull.Calculus.C18TubeCompactTimePartition

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- On the middle half-cylinder, the combined forward nonlinear pairing vanishes
whenever that pairing is integrable. -/
theorem c13_forward_C2_combined_pairing_eq_zero
    {d : ℕ} {κ r h : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (hh : 0 < h) (hhsmall : h ≤ 1 / 4)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r)
    (htotal : Integrable (fun z : ℝ × Vec d =>
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r))) :
    (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z) = 0 := by
  let S := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r
  let T : ℝ × Vec d → ℝ := fun z => -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0)
  let B : ℝ × Vec d → ℝ := fun z => dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
    (ψ z • (deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) • (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) +
     deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) • (fun j => fderiv ℝ ψ z (0,unitVector j)))
  have ht : Integrable T (volume.restrict S) := by
    convert (c13_weighted_forward_nonlinear_time_term_integrable hκ (le_of_lt hh)
      (by linarith) ρ α hell y u G hu F hF M hM hder ψ hψ hψc).neg using 1 <;>
      funext z <;> dsimp [T] <;> ring
  have hid : (fun z => T z + B z) = (fun z =>
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) * dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) * dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2))) (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z) := by
    funext z
    simp only [T, B, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [add_assoc, add_right_inj, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hb : Integrable B (volume.restrict S) := by
    have hs := htotal.sub ht
    convert hs using 1 <;> funext z
    have hz := congrFun hid z
    simp only [Pi.sub_apply] at *
    linarith
  change (∫ z in S, _) = 0
  rw [← hid, integral_add ht hb]
  have hforward := c13_weighted_forward_C2_renormalized_identity hκ hr hh hhsmall
    ρ α hell y u G hu F hF M hM hder ψ hψ hψc hsp
  have htform : T = (fun z => -(ρ z.2 * F (h⁻¹ *
      ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) * fderiv ℝ ψ z (1,0))) := by
    funext z
    dsimp [T]
    ring
  rw [htform, integral_neg]
  simpa only [B, S] using hforward

/-- The combined forward nonlinear pairing vanishes for all sufficiently
small positive averaging times on the middle half-cylinder. -/
theorem c13_forward_C2_combined_pairing_eventually_zero
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hsp : tsupport ψ ⊆ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
        -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
        deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z) = 0 := by
  let S : Set (ℝ × Vec d) := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r
  have hle : volume.restrict S ≤ volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall y r) :=
    Measure.restrict_mono_set volume (by
      intro z hz
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩)
  have hi := c20_tested_forward_nonlinear_eventually_integrable hκ
    (by norm_num : (-(1 / 2 : ℝ)) < 1 / 2) ρ α hell y u G
    (hu.1.mono_measure hle) (hu.2.1.mono_measure hle) (hu.2.2.1.mono_measure hle)
    F hF M hM hder ψ hψ hψc hsp
  have hp : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h ∧ h ≤ 1 / 4 := by
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4)).filter_mono nhdsWithin_le_nhds] with h hh hs
    exact ⟨hh, le_of_lt hs⟩
  filter_upwards [hi, hp] with h htotal hh
  exact c13_forward_C2_combined_pairing_eq_zero hκ hr hh.1 hh.2 ρ α hell y u G hu
    F hF M hM hder ψ hψ hψc hsp htotal

/-- Affine rescaling of time commutes with the forward average of an actual
spacetime field, for scalar or vector-valued fields. -/
theorem c13_forward_average_spacetime_affine_time
    {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : ℝ × Vec d → E) (c τ h : ℝ) (hτ : τ ≠ 0) (z : ℝ × Vec d) :
    h⁻¹ • (∫ s in (0 : ℝ)..h, v (c + τ * (z.1 + s), z.2)) =
      (τ * h)⁻¹ • (∫ s in (0 : ℝ)..(τ * h), v (c + τ * z.1 + s, z.2)) := by
  simpa only [mul_add, add_assoc] using
    (c20_forward_average_affine_time (fun t => v (t, z.2)) (c + τ * z.1) τ h hτ)

/-- Scaling the time derivative and the diffusion matrix by the same factor
scales the complete nonlinear weak-pairing integrand by that factor. -/
theorem c13_nonlinear_pairing_scale {d : ℕ} (τ ρ v Dt p : ℝ)
    (α : Mat d) (V D : Vec d) (F : ℝ → ℝ) :
    -(ρ * F v) * (τ * Dt) + deriv F v * dot ((τ • α).mulVec V) D +
      deriv (deriv F) v * dot ((τ • α).mulVec V) V * p =
    τ * (-(ρ * F v) * Dt + deriv F v * dot (α.mulVec V) D +
      deriv (deriv F) v * dot (α.mulVec V) V * p) := by
  have hd (W : Vec d) : dot ((τ • α).mulVec V) W = τ * dot (α.mulVec V) W := by
    rw [Matrix.smul_mulVec]
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hd D, hd V]
  ring

/-- Pointwise transport of the complete averaged nonlinear pairing under the
standard affine normalization of a time interval. -/
theorem c13_forward_nonlinear_pairing_normalize_time {d : ℕ} {a b : ℝ}
    (hab : a < b) (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (F : ℝ → ℝ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U)
    (h : ℝ) (z : ℝ × Vec d) :
    let c := (a+b)/2
    let τ := (b-a)/2
    let φ : ℝ × Vec d → ℝ := fun z => ψ (c + τ*z.1, z.2)
    let uh := h⁻¹ * (∫ s in (0 : ℝ)..h, u (c + τ*(z.1+s), z.2))
    let Gh := h⁻¹ • (∫ s in (0 : ℝ)..h, G (c + τ*(z.1+s), z.2))
    let t := (c + τ*z.1, z.2)
    let up := (τ*h)⁻¹ * (∫ s in (0 : ℝ)..(τ*h), u (t.1+s, t.2))
    let Gp := (τ*h)⁻¹ • (∫ s in (0 : ℝ)..(τ*h), G (t.1+s, t.2));
    -(ρ z.2 * F uh) * fderiv ℝ φ z (1,0) +
      deriv F uh * dot (((τ • α z.2)).mulVec Gh)
        (fun j => fderiv ℝ φ z (0,unitVector j)) +
      deriv (deriv F) uh * dot (((τ • α z.2)).mulVec Gh) Gh * φ z =
    τ * (-(ρ t.2 * F up) * fderiv ℝ ψ t (1,0) +
      deriv F up * dot ((α t.2).mulVec Gp)
        (fun j => fderiv ℝ ψ t (0,unitVector j)) +
      deriv (deriv F) up * dot ((α t.2).mulVec Gp) Gp * ψ t) := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : τ ≠ 0 := ne_of_gt (by dsimp [τ]; linarith)
  have htest := c13_normalized_time_test hab ψ hψ hc hs
  have hu := c13_forward_average_spacetime_affine_time u c τ h hτ z
  have hG := c13_forward_average_spacetime_affine_time G c τ h hτ z
  simp only [smul_eq_mul] at hu
  dsimp only at htest ⊢
  have htime := htest.2.2.2.1 z
  change fderiv ℝ (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) z (1,0) =
    τ * fderiv ℝ ψ (c + τ*z.1, z.2) (1,0) at htime
  have hD : (fun j => fderiv ℝ (fun z : ℝ × Vec d => ψ (c + τ*z.1, z.2)) z (0,unitVector j)) =
      (fun j => fderiv ℝ ψ (c + τ*z.1, z.2) (0,unitVector j)) := by
    funext j
    exact htest.2.2.2.2 z j
  rw [hu, hG, htime, hD]
  exact c13_nonlinear_pairing_scale τ (ρ z.2)
    ((τ*h)⁻¹ * ∫ s in (0 : ℝ)..(τ*h), u (c + τ*z.1+s,z.2))
    (fderiv ℝ ψ (c + τ*z.1,z.2) (1,0)) (ψ (c + τ*z.1,z.2)) (α z.2)
    ((τ*h)⁻¹ • ∫ s in (0 : ℝ)..(τ*h), G (c + τ*z.1+s,z.2))
    (fun j => fderiv ℝ ψ (c + τ*z.1,z.2) (0,unitVector j)) F

/-- Change variables under a positive affine time map on any time slab. -/
theorem c13_affine_time_integral {d : ℕ} (c τ l r : ℝ) (hτ : 0 < τ)
    (U : Set (Vec d)) (f : ℝ × Vec d → ℝ) :
    τ * (∫ z in Set.Ioo l r ×ˢ U, f (c + τ*z.1, z.2)) =
      ∫ z in Set.Ioo (c + τ*l) (c + τ*r) ×ˢ U, f z := by
  have hl : c + τ*l - c = τ*l := by ring
  have hr : c + τ*r - c = τ*r := by ring
  have ht := c13_time_translation_measurePreserving (d := d) c (c + τ*l) (c + τ*r) U
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+c, z.2)) := by
    convert (Homeomorph.addRight (c, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨t,x⟩
    simp
  have hi := ht.integral_comp he f
  rw [hl, hr] at hi
  have hs := PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
    (EinsteinFull.c5_time_scale_embedding (d := d) hτ)
    (EinsteinFull.c5_time_scale_map_cylinder hτ l r U)
    (fun z => f (z.1+c, z.2))
  rw [hi] at hs
  simp only [ENNReal.toReal_ofReal (inv_pos.mpr hτ).le, smul_eq_mul] at hs
  have hs' : (∫ z in Set.Ioo l r ×ˢ U, f (c + τ*z.1, z.2)) =
      τ⁻¹ * ∫ z in Set.Ioo (c + τ*l) (c + τ*r) ×ˢ U, f z := by
    simpa only [add_comm] using hs
  rw [hs', ← mul_assoc, mul_inv_cancel₀ hτ.ne', one_mul]

/-- Transport an integrand whose pointwise affine-time change includes the
Jacobian factor. No integrability premise is needed for this identity. -/
theorem c13_affine_time_integral_of_pointwise {d : ℕ}
    (c τ l r : ℝ) (hτ : 0 < τ) (U : Set (Vec d))
    (f g : ℝ × Vec d → ℝ)
    (hfg : ∀ z, g z = τ * f (c + τ*z.1, z.2)) :
    (∫ z in Set.Ioo l r ×ˢ U, g z) =
      ∫ z in Set.Ioo (c + τ*l) (c + τ*r) ×ˢ U, f z := by
  calc
    (∫ z in Set.Ioo l r ×ˢ U, g z) =
        ∫ z in Set.Ioo l r ×ˢ U, τ * f (c + τ*z.1, z.2) := by
      apply integral_congr_ae
      filter_upwards with z
      exact hfg z
    _ = τ * (∫ z in Set.Ioo l r ×ˢ U, f (c + τ*z.1, z.2)) :=
      integral_const_mul τ _
    _ = ∫ z in Set.Ioo (c + τ*l) (c + τ*r) ×ˢ U, f z :=
      c13_affine_time_integral c τ l r hτ U f

/-- The normalized forward pairing vanishes eventually for any test whose
pullback is supported in the middle half of the normalized time interval. -/
theorem c13_normalized_forward_C2_eventually_zero
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hmid : tsupport (fun z : ℝ × Vec d => ψ ((a+b)/2 + ((b-a)/2)*z.1, z.2)) ⊆
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r) :
    let c := (a+b)/2
    let τ := (b-a)/2
    let v : ℝ × Vec d → ℝ := fun z => u (c + τ*z.1,z.2)
    let H : ℝ × Vec d → Vec d := fun z => G (c + τ*z.1,z.2)
    let φ : ℝ × Vec d → ℝ := fun z => ψ (c + τ*z.1,z.2)
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ sourceBall y r,
        -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2))) * fderiv ℝ φ z (1,0) +
        deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2)) *
          dot (((τ • α z.2)).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)))
            (fun j => fderiv ℝ φ z (0,unitVector j)) +
        deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2)) *
          dot (((τ • α z.2)).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)))
            (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)) * φ z) = 0 := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  obtain ⟨κ', hκ', he⟩ := EinsteinFull.c13_uniform_ellipticity_affine_time_transport κ τ hκ hτ
  have hell' : IsUniformlyElliptic κ' ρ (fun x => τ • α x) := by
    simpa only [add_zero] using he ρ α hell 0
  have hv := c13_weighted_caloric_normalize_time hab (sourceBall y r) ρ α u G hu
  have ht := c13_normalized_time_test hab ψ hψ hψc hs
  exact c13_forward_C2_combined_pairing_eventually_zero hκ' hr ρ (fun x => τ • α x)
    hell' y (fun z => u (c + τ*z.1,z.2)) (fun z => G (c + τ*z.1,z.2)) hv
    F hF M hM hder (fun z => ψ (c + τ*z.1,z.2)) ht.1 ht.2.1 hmid

/-- A test supported in the physical middle half pulls back to the
normalized middle half. -/
theorem c13_normalized_middle_time_support {d : ℕ} {a b : ℝ}
    (hab : a < b) (U : Set (Vec d)) (ψ : ℝ × Vec d → ℝ)
    (hs : tsupport ψ ⊆
      Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ U) :
    tsupport (fun z : ℝ × Vec d => ψ ((a+b)/2 + ((b-a)/2)*z.1, z.2)) ⊆
      Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have hc : Continuous (fun z : ℝ × Vec d => (c + τ*z.1, z.2)) := by fun_prop
  intro z hz
  have hp := tsupport_comp_subset_preimage ψ hc hz
  have hh := hs hp
  change (c - τ/2 < c + τ*z.1 ∧ c + τ*z.1 < c + τ/2) ∧ z.2 ∈ U at hh
  change (-(1/2 : ℝ) < z.1 ∧ z.1 < 1/2) ∧ z.2 ∈ U
  exact ⟨⟨by nlinarith [hh.1.1], by nlinarith [hh.1.2]⟩, hh.2⟩

/-- Integral transport of the complete nonlinear forward pairing. -/
theorem c13_forward_nonlinear_pairing_integral_normalize_time {d : ℕ} {a b : ℝ}
    (hab : a < b) (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (F : ℝ → ℝ)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ U)
    (h l r : ℝ) :
    let c := (a+b)/2
    let τ := (b-a)/2
    let φ : ℝ × Vec d → ℝ := fun z => ψ (c + τ*z.1,z.2)
    let v : ℝ × Vec d → ℝ := fun z => u (c + τ*z.1,z.2)
    let H : ℝ × Vec d → Vec d := fun z => G (c + τ*z.1,z.2)
    (∫ z in Set.Ioo l r ×ˢ U,
      -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2))) * fderiv ℝ φ z (1,0) +
      deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2)) *
        dot (((τ • α z.2)).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)))
          (fun j => fderiv ℝ φ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, v (z.1+s,z.2)) *
        dot (((τ • α z.2)).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)))
          (h⁻¹ • ∫ s in (0 : ℝ)..h, H (z.1+s,z.2)) * φ z) =
    ∫ z in Set.Ioo (c + τ*l) (c + τ*r) ×ˢ U,
      -(ρ z.2 * F ((τ*h)⁻¹ * ∫ s in (0 : ℝ)..(τ*h), u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F ((τ*h)⁻¹ * ∫ s in (0 : ℝ)..(τ*h), u (z.1+s,z.2)) *
        dot ((α z.2).mulVec ((τ*h)⁻¹ • ∫ s in (0 : ℝ)..(τ*h), G (z.1+s,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) ((τ*h)⁻¹ * ∫ s in (0 : ℝ)..(τ*h), u (z.1+s,z.2)) *
        dot ((α z.2).mulVec ((τ*h)⁻¹ • ∫ s in (0 : ℝ)..(τ*h), G (z.1+s,z.2)))
          ((τ*h)⁻¹ • ∫ s in (0 : ℝ)..(τ*h), G (z.1+s,z.2)) * ψ z := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  apply c13_affine_time_integral_of_pointwise c τ l r hτ U
  intro z
  exact c13_forward_nonlinear_pairing_normalize_time hab U ρ α u G F ψ hψ hc hs h z

/-- The forward pairing vanishes on the physical middle slab for every
sufficiently small positive averaging time. -/
theorem c13_physical_middle_forward_C2_eventually_zero
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hmid : tsupport ψ ⊆
      Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ sourceBall y r) :
    let c := (a+b)/2
    let τ := (b-a)/2
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ z in Set.Ioo (c - τ/2) (c + τ/2) ×ˢ sourceBall y r,
        -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
        deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z) = 0 := by
  let c : ℝ := (a+b)/2
  let τ : ℝ := (b-a)/2
  have hτ : 0 < τ := by dsimp [τ]; linarith
  have htest := c13_normalized_middle_time_support hab (sourceBall y r) ψ hmid
  have hn := c13_normalized_forward_C2_eventually_zero hκ hr hab ρ α hell y u G hu
    F hF M hM hder ψ hψ hψc hs htest
  have htend : Tendsto (fun h : ℝ => h / τ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Tendsto (fun h : ℝ => h / τ) (𝓝 0) (𝓝 0) := by
        simpa only [id_eq, zero_div] using (continuous_id.div_const τ).tendsto (0 : ℝ)
      exact hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact div_pos hh hτ
  filter_upwards [htend.eventually hn] with h hh
  have hi := c13_forward_nonlinear_pairing_integral_normalize_time hab (sourceBall y r)
    ρ α u G F ψ hψ hψc hs (h/τ) (-(1/2 : ℝ)) (1/2)
  have hhτ : τ * (h/τ) = h := by field_simp [ne_of_gt hτ]
  dsimp only at hi hh
  rw [hhτ] at hi
  have hl : c + τ * (-(1/2 : ℝ)) = c - τ/2 := by ring
  have hr' : c + τ * (1/2 : ℝ) = c + τ/2 := by ring
  rw [hl, hr'] at hi
  exact hi.symm.trans hh

/-- The forward nonlinear pairing depends only on a region containing the test support. -/
theorem c13_forward_pairing_restrict {d : ℕ}
    (s t : Set (ℝ × Vec d)) (ht : MeasurableSet t) (hst : s ⊆ t)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (F : ℝ → ℝ) (ψ : ℝ × Vec d → ℝ) (hψ : tsupport ψ ⊆ s) (h : ℝ) :
    (∫ z in t,
      -(ρ z.2 * F (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)))
          (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)) * ψ z) =
    (∫ z in s,
      -(ρ z.2 * F (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2))) * fderiv ℝ ψ z (1,0) +
      deriv F (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (h⁻¹ * ∫ r in (0 : ℝ)..h, u (z.1+r,z.2)) *
        dot ((α z.2).mulVec (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)))
          (h⁻¹ • ∫ r in (0 : ℝ)..h, G (z.1+r,z.2)) * ψ z) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero ht hst
  intro z hz
  have hn : z ∉ tsupport ψ := fun hz' => hz.2 (hψ hz')
  simp [fderiv_of_notMem_tsupport ℝ hn, image_eq_zero_of_notMem_tsupport hn, dot]

/-- Weighted caloricity restricts to a smaller time interval. -/
theorem c13_weighted_caloric_time_mono {d : ℕ} {ρ : Vec d → ℝ}
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
    have heq : (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      ∫ z in J ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.prod hU) hsub
      intro z hz
      have hn : z ∉ tsupport ψ := by
        intro hz'
        have hh := hs hz'
        exact hz.2 ⟨interior_subset hh.1, hh.2⟩
      simp [fderiv_of_notMem_tsupport ℝ hn, dot]
    rw [← heq]
    exact hu.2.2.2.2 ψ hψ hc hs'

/-- The local forward identity holds on every measurable containing region. -/
theorem c13_forward_C2_eventually_zero_on_superset
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hmid : tsupport ψ ⊆
      Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ sourceBall y r) 
    (t : Set (ℝ × Vec d)) (ht : MeasurableSet t)
    (hsub : Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ
      sourceBall y r ⊆ t) :
    let c := (a+b)/2
    let τ := (b-a)/2
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      (∫ z in t,
        -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
        deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z) = 0 := by
  have hz := c13_physical_middle_forward_C2_eventually_zero hκ hr hab ρ α hell y u G hu
    F hF M hM hder ψ hψ hψc hs hmid
  filter_upwards [hz] with h hh
  have heq := c13_forward_pairing_restrict _ t ht hsub ρ α u G F ψ hmid h
  exact heq.trans hh

/-- A combined limit vanishes when the test is localized to a middle slab. -/
theorem c13_local_combined_limit_eq_zero
    {d : ℕ} {κ r a b : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ q, |deriv (deriv F) q| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall y r)
    (hmid : tsupport ψ ⊆
      Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ sourceBall y r) 
    (t : Set (ℝ × Vec d)) (ht : MeasurableSet t)
    (hsub : Set.Ioo ((a+b)/2 - ((b-a)/2)/2) ((a+b)/2 + ((b-a)/2)/2) ×ˢ
      sourceBall y r ⊆ t)
    (L : ℝ) (hlim : Tendsto (fun h : ℝ => (∫ z in t,
        -(ρ z.2 * F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2))) * fderiv ℝ ψ z (1,0) +
        deriv F (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)) *
          dot ((α z.2).mulVec (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)))
            (h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)) * ψ z)) (𝓝[>] 0) (𝓝 L)) : L = 0 := by
  have hz := c13_forward_C2_eventually_zero_on_superset hκ hr hab ρ α hell y u G hu
    F hF M hM hder ψ hψ hψc hs hmid t ht hsub
  have hzero := tendsto_const_nhds.congr' (hz.mono fun h hh => hh.symm)
  exact tendsto_nhds_unique hlim hzero

@[nolint unusedArguments]
theorem c13_actual_weighted_caloric_renormalization_of_combined_limit {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    (hcombined : ∀ (ψ : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    let uh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ * ∫ s in (0 : ℝ)..h, u (z.1+s,z.2)
    let Gh := fun h : ℝ => fun z : ℝ × Vec d => h⁻¹ • ∫ s in (0 : ℝ)..h, G (z.1+s,z.2)
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (uh h z)) * fderiv ℝ ψ z (1,0) +
        deriv F (uh h z) * dot ((α z.2).mulVec (Gh h z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (uh h z) * dot ((α z.2).mulVec (Gh h z)) (Gh h z) * ψ z)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
        -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
        deriv F (u z) * dot ((α z.2).mulVec (G z))
          (fun j => fderiv ℝ ψ z (0,unitVector j)) +
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z))) :
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  classical
  intro ψ hψ hψc hs
  let K : Set ℝ := Prod.fst '' tsupport ψ
  have hK : IsCompact K := hψc.image continuous_fst
  have hKI : K ⊆ Set.Ioo a b := by
    rintro x ⟨z, hz, rfl⟩
    exact (hs hz).1
  obtain ⟨n, η, t, r, hw, hη, hpart⟩ := c18_compact_time_partition hab K hK hKI
  let φ : Fin n → ℝ × Vec d → ℝ := fun i z => η i z.1 * ψ z
  have hφ (i : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (φ i) :=
    ((hη i).1.comp contDiff_fst).mul hψ
  have hφc (i : Fin n) : HasCompactSupport (φ i) := hψc.mul_left
  have hφs (i : Fin n) : tsupport (φ i) ⊆ Set.Ioo a b ×ˢ sourceBall 0 R :=
    tsupport_mul_subset_right.trans hs
  have hmiddle (i : Fin n) : tsupport (φ i) ⊆
      Set.Ioo (((t i - 2*r i)+(t i + 2*r i))/2 -
        (((t i + 2*r i)-(t i - 2*r i))/2)/2)
        (((t i - 2*r i)+(t i + 2*r i))/2 +
        (((t i + 2*r i)-(t i - 2*r i))/2)/2) ×ˢ sourceBall 0 R := by
    intro z hz
    have hzη : z.1 ∈ tsupport (η i) :=
      tsupport_comp_subset_preimage (η i) continuous_fst (tsupport_mul_subset_left hz)
    have htime := (hη i).2.2 hzη
    have hspace := (hφs i hz).2
    exact ⟨⟨by linarith [htime.1], by linarith [htime.2]⟩, hspace⟩
  have hlocal (i : Fin n) : (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ (φ i) z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ (φ i) z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * φ i z) = 0 := by
    have hr := (hw i).1
    have hsmall : t i - 2*r i < t i + 2*r i := by linarith
    have hsub := (hw i).2
    have hcal' := c13_weighted_caloric_time_mono measurableSet_Ioo
      (c20_sourceBall_measurable 0 R) hsub hcal
    have hmid := hmiddle i
    have hs' : tsupport (φ i) ⊆ Set.Ioo (t i - 2*r i) (t i + 2*r i) ×ˢ sourceBall 0 R := by
      intro z hz
      have hz' := hmid hz
      exact ⟨⟨by linarith [hz'.1.1], by linarith [hz'.1.2]⟩, hz'.2⟩
    have hsub' : Set.Ioo (((t i - 2*r i)+(t i + 2*r i))/2 -
        (((t i + 2*r i)-(t i - 2*r i))/2)/2)
        (((t i - 2*r i)+(t i + 2*r i))/2 +
        (((t i + 2*r i)-(t i - 2*r i))/2)/2) ×ˢ sourceBall (0 : Vec d) R ⊆
        Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R := by
      intro z hz
      apply And.intro ?_ hz.2
      apply hsub
      exact ⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩
    exact c13_local_combined_limit_eq_zero hκ hR hsmall ρ α hell 0 u G hcal'
      F hF M hM hder (φ i) (hφ i) (hφc i) hs' hmid _
      (measurableSet_Ioo.prod (c20_sourceBall_measurable 0 R)) hsub' _
      (hcombined (φ i) (hφ i) (hφc i) (hφs i))
  have hi (i : Fin n) := c18_tested_nonlinear_pairing_integrable hκ hR hab ρ α hell 0 u G
    hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder (φ i) (hφ i) (hφc i) (hφs i)
  apply c20_weighted_finite_test_localization ρ α u G F η ψ
    (fun z hz => hpart z.1 ⟨z, hz, rfl⟩) (fun i => (hφ i).differentiable (by simp)) hi
    (fun _ => Set.Ioo a b ×ˢ sourceBall 0 R) (fun _ => Set.Subset.rfl) hφs hlocal

/-- The weighted caloric chain rule follows from the checked combined limit. -/
theorem c13_actual_weighted_caloric_renormalization {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M)
    (hder : ∀ r, |deriv (deriv F) r| ≤ M)
    :
    ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
    tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R →
    (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R,
      -(ρ z.2 * F (u z)) * fderiv ℝ ψ z (1,0) +
      deriv F (u z) * dot ((α z.2).mulVec (G z))
        (fun j => fderiv ℝ ψ z (0,unitVector j)) +
      deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z) = 0 := by
  apply c13_actual_weighted_caloric_renormalization_of_combined_limit
    hκ hR hab ρ α hell u G hcal F hF hF0 M hM hder
  intro ψ hψ hψc hs
  exact c20_weighted_forward_nonlinear_weak_pairing_limit_compact hκ hR hab ρ α hell 0 u G
    hcal.1 hcal.2.1 hcal.2.2.1 F hF M hM hder ψ hψ hψc hs

end EinsteinFull.Calculus
