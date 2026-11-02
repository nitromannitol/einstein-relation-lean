import EinsteinFull.Calculus.C13TubePointwiseC2Energy
import EinsteinFull.Calculus.C13TubeSmallPositivePower

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped Topology

namespace EinsteinFull.Calculus

/-- A continuous function bounded below almost everywhere on the open cylinder is
bounded below at every point of the cylinder. -/
theorem c13_cylinder_lower_bound_of_ae {d : ℕ} {R a b ε : ℝ}
    (u : ℝ × Vec d → ℝ)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (hpos : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R), ε ≤ u z) :
    ∀ z ∈ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ε ≤ u z := by
  have hU : IsOpen (sourceBall (0 : Vec d) R) := by
    have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp (continuous_finsetSum _
        (fun j _ => (continuous_apply j).mul (continuous_apply j)))
    unfold sourceBall
    exact isOpen_lt (hc.comp (continuous_id.sub continuous_const)) continuous_const
  have heq : (fun z => max ε (u z)) =ᵐ[volume.restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)] u := by
    filter_upwards [hpos] with z hz
    exact max_eq_right hz
  have h := Measure.eqOn_open_of_ae_eq heq (isOpen_Ioo.prod hU)
    (continuous_max.comp_continuousOn (continuousOn_const.prodMk hu)) hu
  intro z hz
  exact (max_eq_right_iff.mp (h hz))

/-- A continuous composition localized by a smooth cutoff has integrable weighted mass. -/
theorem c13_weighted_cutoff_composition_integrable {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α) (u : ℝ × Vec d → ℝ)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (F : ℝ → ℝ) (hF : Continuous F) (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ sourceBall 0 R) (t : ℝ) (ht : t ∈ Set.Ioo a b) :
    IntegrableOn (fun x => ρ x * χ x ^ 2 * F (u (t,x))) (sourceBall 0 R) := by
  have hU : IsOpen (sourceBall (0 : Vec d) R) := by
    have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp (continuous_finsetSum _
        (fun j _ => (continuous_apply j).mul (continuous_apply j)))
    unfold sourceBall
    exact isOpen_lt (hc.comp (continuous_id.sub continuous_const)) continuous_const
  let H : Vec d → ℝ := fun x => χ x * (χ x * F (u (t,x)))
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ sourceBall (0 : Vec d) R
    · have hu' : ContinuousAt u (t,x) :=
        hu.continuousAt ((isOpen_Ioo.prod hU).mem_nhds ⟨ht,hx⟩)
      have hv : ContinuousAt (fun y : Vec d => u (t,y)) x :=
        hu'.comp (continuous_const.prodMk continuous_id).continuousAt
      exact hχ.continuous.continuousAt.mul
        (hχ.continuous.continuousAt.mul (hF.continuousAt.comp hv))
    · have hxK : x ∉ tsupport χ := fun hxK => hx (hχU hxK)
      have hn : ∀ᶠ y : Vec d in 𝓝 x, y ∉ tsupport χ :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds hxK
      apply (continuousAt_const : ContinuousAt (fun _ : Vec d => (0 : ℝ)) x).congr_of_eventuallyEq
      filter_upwards [hn] with y hy
      simp only [H, image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hHc : HasCompactSupport H := hχc.mul_right
  have hi : Integrable H := hH.integrable_of_hasCompactSupport hHc
  have hw := hi.bdd_mul (c := κ⁻¹) hell.1.aestronglyMeasurable
    (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (hell.2.2 x).1)] using
        (hell.2.2 x).2.1))
  have hw' : IntegrableOn (fun x => ρ x * H x) (sourceBall 0 R) := hw.restrict
  convert hw' using 1
  funext x
  dsimp [H]
  ring

/-- The every-time small-power balance with the normalized extension's constant retained. -/
theorem c13_small_power_shifted_energy_every_time {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hpos : ∀ z ∈ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ c : ℝ, ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (t,x)) p - c)) -
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (s,x)) p - c)) =
      -(∫ r in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * (p*(p-1)*Real.rpow (u (r,x)) (p-2)) *
          dot ((α x).mulVec (G (r,x))) (G (r,x)) +
        2 * χ x * (p * Real.rpow (u (r,x)) (p-1)) *
          dot ((α x).mulVec (G (r,x))) (fun j => fderiv ℝ χ x (unitVector j))) := by
  obtain ⟨F, c, M, hF, hF0, hM, hb, hval, hd, hdd⟩ :=
    c13_small_positive_power_normalized_extension ε p hε hp hp1
  refine ⟨c, ?_⟩
  intro s hs t ht
  have he := c13_actual_weighted_C2_energy_every_time hκ hR hab ρ α hell u G hcal hu
    F hF hF0 M hM (fun x => (hb x).2) χ hχ hχc hχU s hs t ht
  have hm (v : ℝ) (hv : v ∈ Set.Ioo a b) :
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (v,x))) =
      ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (v,x)) p - c) := by
    apply setIntegral_congr_fun (c20_sourceBall_measurable 0 R)
    intro x hx
    dsimp only
    rw [hval _ (hpos (v,x) ⟨hv,hx⟩)]
  rw [hm t ht, hm s hs] at he
  have hf : (∫ r in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * deriv (deriv F) (u (r,x)) * dot ((α x).mulVec (G (r,x))) (G (r,x)) +
        2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
          (fun j => fderiv ℝ χ x (unitVector j))) =
      ∫ r in s..t, ∫ x in sourceBall 0 R,
        χ x ^ 2 * (p*(p-1)*Real.rpow (u (r,x)) (p-2)) *
          dot ((α x).mulVec (G (r,x))) (G (r,x)) +
        2 * χ x * (p * Real.rpow (u (r,x)) (p-1)) *
          dot ((α x).mulVec (G (r,x))) (fun j => fderiv ℝ χ x (unitVector j)) := by
    apply intervalIntegral.integral_congr_uIoo
    intro r hr
    have hr' : r ∈ Set.Ioo a b := ⟨lt_of_lt_of_le (lt_min hs.1 ht.1) (le_of_lt hr.1),
      lt_of_le_of_lt (le_of_lt hr.2) (max_lt hs.2 ht.2)⟩
    apply setIntegral_congr_fun (c20_sourceBall_measurable 0 R)
    intro x hx
    dsimp only
    rw [hd _ (hpos (r,x) ⟨hr',hx⟩), hdd _ (hpos (r,x) ⟨hr',hx⟩)]
  rw [hf] at he
  exact he

/-- The literal small-positive-power energy balance holds at every interior time. -/
theorem c13_small_power_energy_every_time {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hpos : ∀ z ∈ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R, ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) -
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (s,x)) p) =
    ∫ r in s..t, ∫ x in sourceBall 0 R,
      p*(1-p)*χ x^2*Real.rpow (u (r,x)) (p-2)*dot ((α x).mulVec (G (r,x))) (G (r,x)) -
      2*p*χ x*Real.rpow (u (r,x)) (p-1)*dot ((α x).mulVec (G (r,x)))
        (fun j => fderiv ℝ χ x (unitVector j)) := by
  obtain ⟨c, hc⟩ := c13_small_power_shifted_energy_every_time hκ hR hab ρ α hell u G
    hcal hu ε p hε hp hp1 hpos χ hχ hχc hχU
  intro s hs t ht
  have hm (v : ℝ) (hv : v ∈ Set.Ioo a b) :
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * (Real.rpow (u (v,x)) p - c)) =
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (v,x)) p) -
      (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * c) := by
    have hi := c13_weighted_cutoff_composition_integrable hκ ρ α hell u hu
      (fun x => Real.rpow x p) (Real.continuous_rpow_const hp.le) χ hχ hχc hχU v hv
    have hj := c13_weighted_cutoff_composition_integrable hκ ρ α hell u hu
      (fun _ => c) continuous_const χ hχ hχc hχU v hv
    have heq : (fun x => ρ x * χ x ^ 2 * (Real.rpow (u (v,x)) p - c)) =
        (fun x => ρ x * χ x ^ 2 * Real.rpow (u (v,x)) p - ρ x * χ x ^ 2 * c) := by
      funext x; ring
    rw [heq, integral_sub hi hj]
  have he := hc s hs t ht
  rw [hm t ht, hm s hs] at he
  have hf : -(∫ r in s..t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * (p*(p-1)*Real.rpow (u (r,x)) (p-2)) *
        dot ((α x).mulVec (G (r,x))) (G (r,x)) +
      2 * χ x * (p * Real.rpow (u (r,x)) (p-1)) *
        dot ((α x).mulVec (G (r,x))) (fun j => fderiv ℝ χ x (unitVector j))) =
      ∫ r in s..t, ∫ x in sourceBall 0 R,
      p*(1-p)*χ x^2*Real.rpow (u (r,x)) (p-2)*dot ((α x).mulVec (G (r,x))) (G (r,x)) -
      2*p*χ x*Real.rpow (u (r,x)) (p-1)*dot ((α x).mulVec (G (r,x)))
        (fun j => fderiv ℝ χ x (unitVector j)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro r hr
    dsimp only
    rw [← integral_neg]
    apply setIntegral_congr_fun (c20_sourceBall_measurable 0 R)
    intro x hx
    dsimp only
    ring
  rw [hf] at he
  linarith

/-- The same balance follows from an almost-everywhere lower bound. -/
theorem c13_small_power_energy_every_time_of_ae {d : ℕ} {κ R a b : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ContinuousOn u (Set.Ioo a b ×ˢ sourceBall 0 R))
    (ε p : ℝ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (hpos : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) -
    (∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (s,x)) p) =
    ∫ r in s..t, ∫ x in sourceBall 0 R,
      p*(1-p)*χ x^2*Real.rpow (u (r,x)) (p-2)*dot ((α x).mulVec (G (r,x))) (G (r,x)) -
      2*p*χ x*Real.rpow (u (r,x)) (p-1)*dot ((α x).mulVec (G (r,x)))
        (fun j => fderiv ℝ χ x (unitVector j)) :=
  c13_small_power_energy_every_time hκ hR hab ρ α hell u G hcal hu ε p hε hp hp1
    (c13_cylinder_lower_bound_of_ae u hu hpos) χ hχ hχc hχU

end EinsteinFull.Calculus
