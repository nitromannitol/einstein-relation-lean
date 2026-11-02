import EinsteinFull.Calculus.SbxBBackwardInverseGainR11
import EinsteinFull.Calculus.C17TubeInverseGainRadiusAlgebra

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

/-- The actual weighted equation pulls back to the backward unit cylinder. -/
theorem b_backward_caloric_rescale {d : ℕ} (t : ℝ) (y : Vec d) {r : ℝ}
    (hr : 0 < r) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo (t-r^2) t) (sourceBall y r) u G) :
    IsWeightedCaloric (fun x => ρ (y+r • x)) (fun x => α (y+r • x))
      (Set.Ioo (-1) 0) (sourceBall 0 1)
      (fun z => u (t+r^2*z.1, y+r • z.2))
      (fun z => r • G (t+r^2*z.1, y+r • z.2)) := by
  have ht := c13_weighted_caloric_time_translation t (t-r^2) t (sourceBall y r) ρ α u G hu
  have ht' : IsWeightedCaloric ρ α (Set.Ioo ((r^2)*(-1)) ((r^2)*0))
      (sourceBall y r) (fun z => u (z.1+t,z.2)) (fun z => G (z.1+t,z.2)) := by
    simpa using ht
  have hs := EinsteinFull.c5_time_scale_weighted_caloric (sq_pos_of_pos hr) ht'
  have he := c17_spatial_affine_caloric_energy y hr hs
  have hf : IsWeightedCaloric (fun x => ρ (y+r • x)) (fun x => α (y+r • x))
      (Set.Ioo (-1) 0) (sourceBall 0 1)
      (fun z => u (r^2*z.1+t, y+r • z.2))
      (fun z => r • G (r^2*z.1+t, y+r • z.2)) := by
    refine ⟨he.1, he.2.1, he.2.2, c17_spatial_affine_caloric_gradients y hr hs, ?_⟩
    intro ψ hψ hc hsup
    apply c17_spatial_affine_weak_identity y hr hs ψ hψ hc
    simpa only [interior_Ioo] using hsup
  simpa only [add_comm] using hf

/-- The affine preimage of a backward cylinder, with arbitrary spatial radius. -/
theorem b_backward_cylinder_preimage {d : ℕ} (y : Vec d) {r : ℝ}
    (hr : 0 < r) (a s : ℝ) :
    (fun z : ℝ × Vec d => (r^2*z.1, y+r • z.2)) ⁻¹'
      (Set.Ioo (r^2*a) 0 ×ˢ sourceBall y (r*s)) =
    Set.Ioo a 0 ×ˢ sourceBall (0 : Vec d) s := by
  ext ⟨t,x⟩
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, sourceBall,
    Set.mem_ofPred_eq, add_sub_cancel_left, sub_zero,
    TimeChange.euclideanNorm_smul, abs_of_pos hr]
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  constructor <;> rintro ⟨⟨h1,h2⟩,h3⟩ <;> constructor
  · constructor <;> nlinarith
  · nlinarith
  · constructor <;> nlinarith
  · nlinarith

/-- Backward gain at a fixed terminal time, with the sharp radius factor. -/
theorem b_backward_negative_power_gain_at_zero
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (y : Vec d) (r : ℝ), 0 < r →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-r^2) 0) (sourceBall y r) u G →
    ∀ ε p : ℝ, 0 < ε → 0 < p →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r), ε ≤ u z) →
    eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
      (volume.restrict (Set.Ioo (-(r^2)/4) 0 ×ˢ sourceBall y (r/2))) ≤
    ((C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) * ENNReal.ofReal (Real.rpow r (-(2/p)))) *
      eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r)) := by
  obtain ⟨C, hC, hgain⟩ := b_backward_negative_power_sobolev_gain_from_energy d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro y r hr ρ α hell u G hcal ε p hε hp hu
  have he : IsUniformlyElliptic κ (fun x => ρ (y+r • x)) (fun x => α (y+r • x)) :=
    ⟨hell.1.comp (c17_spatial_affine_embedding y hr).measurable,
      hell.2.1.comp (c17_spatial_affine_embedding y hr).measurable, fun x => hell.2.2 _⟩
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (r^2*z.1, y+r • z.2)
  have hemb : MeasurableEmbedding F :=
    ((Homeomorph.smulOfNeZero (r^2) (ne_of_gt (sq_pos_of_pos hr))).prodCongr
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y))).measurableEmbedding
  have hm : Measure.map F volume =
      (ENNReal.ofReal |(r^2)⁻¹| * ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume : Measure (ℝ × Vec d)) := by
    change Measure.map (Prod.map (fun s : ℝ => r^2*s) (fun x : Vec d => y+r • x)) volume = _
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.map_prod_map _ _
      (measurable_const_mul _) (c17_spatial_affine_embedding y hr).measurable,
      show (fun s : ℝ => r^2*s) = (fun s : ℝ => 0 + r^2*s) by ext; simp,
      c20_map_volume_affine_time 0 (r^2) (ne_of_gt (sq_pos_of_pos hr)),
      c17_spatial_affine_map_volume y hr, Measure.prod_smul_left, Measure.prod_smul_right,
      ← smul_smul, ← Measure.volume_eq_prod]
  have hpre : F ⁻¹' (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r) =
      Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall (0 : Vec d) 1 := by
    simpa [F] using b_backward_cylinder_preimage y hr (-1) 1
  have hmap : Measure.map F (volume.restrict
      (Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall (0 : Vec d) 1)) =
      (ENNReal.ofReal |(r^2)⁻¹| * ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume.restrict (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r)) := by
    rw [← hpre, ← Measure.restrict_map hemb.measurable
      (measurableSet_Ioo.prod (c17_isOpen_sourceBall y r).measurableSet), hm, Measure.restrict_smul]
  have hu' : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall (0 : Vec d) 1),
      ε ≤ u (F z) := by
    apply (hemb.ae_map_iff (p := fun z => ε ≤ u z)
      (μ := volume.restrict (Set.Ioo (-1 : ℝ) 0 ×ˢ sourceBall (0 : Vec d) 1))).mp
    rw [hmap]
    exact Measure.ae_smul_measure hu _
  have hc := b_backward_caloric_rescale 0 y hr ρ α u G (by simpa using hcal)
  have h := hgain _ _ he _ _ hc ε p hε hp (by simpa [F] using hu')
  simp only [zero_add] at h
  have hs := c17_parabolic_eLpNorm_preimage y hr
    (Set.Ioo (-(r^2)/4) 0 ×ˢ sourceBall y (r/2))
    (measurableSet_Ioo.prod (c17_isOpen_sourceBall y (r/2)).measurableSet)
    (ENNReal.ofReal (p * (((d : ℝ)+2)/d))) (fun z => (u z)⁻¹)
  have hl := c17_parabolic_eLpNorm_preimage y hr
    (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r)
    (measurableSet_Ioo.prod (c17_isOpen_sourceBall y r).measurableSet)
    (ENNReal.ofReal p) (fun z => (u z)⁻¹)
  dsimp only at hs hl
  have hsmall : F ⁻¹' (Set.Ioo (-(r^2)/4) 0 ×ˢ sourceBall y (r/2)) =
      Set.Ioo (-1/4 : ℝ) 0 ×ˢ sourceBall (0 : Vec d) (1/2) := by
    convert b_backward_cylinder_preimage y hr (-1/4) (1/2) using 1 <;> congr 3
    all_goals ring
  change eLpNorm ((fun z => (u z)⁻¹) ∘ F) _ (volume.restrict (F ⁻¹' _)) = _ at hs hl
  rw [hsmall] at hs
  rw [hpre] at hl
  simp only [Function.comp_def, F] at hs hl
  rw [hs, hl, c17_parabolic_jacobian_combine d r hr] at h
  let J : ℝ≥0∞ := ENNReal.ofReal ((r ^ (d+2))⁻¹)
  let q : ℝ≥0∞ := ENNReal.ofReal (p * (((d : ℝ)+2)/d))
  have hJ0 : J ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  have hJtop : J ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq0 : J ^ (1/q).toReal ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hJ0) hJtop).ne'
  have hqtop : J ^ (1/q).toReal ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hJ0 hJtop
  have hh := mul_le_mul' (le_refl ((J ^ (1/q).toReal)⁻¹)) h
  rw [← mul_assoc, ENNReal.inv_mul_cancel hq0 hqtop, one_mul] at hh
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hratio := c17_parabolic_gain_ennreal_ratio d p r hdpos hp hr
  change (J ^ (1/q).toReal)⁻¹ * J ^ (1/ENNReal.ofReal p).toReal = _ at hratio
  calc
    _ ≤ (J ^ (1/q).toReal)⁻¹ * ((C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) *
        (J ^ (1/ENNReal.ofReal p).toReal *
          eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p)
            (volume.restrict (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r)))) := hh
    _ = _ := by rw [← hratio]; ac_rfl

/-- Translation in time preserves unnormalized cylinder norms. -/
theorem b_backward_time_shift_eLpNorm {d : ℕ} (t a b : ℝ)
    (U : Set (Vec d)) (p : ℝ≥0∞) (f : ℝ × Vec d → ℝ) :
    eLpNorm (fun z => f (t + z.1, z.2)) p
      (volume.restrict (Set.Ioo a b ×ˢ U)) =
    eLpNorm f p (volume.restrict (Set.Ioo (t+a) (t+b) ×ˢ U)) := by
  have he : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+t, z.2)) := by
    convert (Homeomorph.addRight (t, (0 : Vec d))).measurableEmbedding using 1
    funext z
    rcases z with ⟨s, x⟩
    simp
  have hm := c13_time_translation_measurePreserving (d := d) t (t+a) (t+b) U
  have hm' : Measure.map (fun z : ℝ × Vec d => (z.1+t, z.2))
      (volume.restrict (Set.Ioo a b ×ˢ U)) =
      volume.restrict (Set.Ioo (t+a) (t+b) ×ˢ U) := by
    simpa only [add_sub_cancel_left] using hm.map_eq
  have hn := he.eLpNorm_map_measure (g := f) (p := p)
    (μ := volume.restrict (Set.Ioo a b ×ˢ U))
  rw [hm'] at hn
  simpa only [Function.comp_def, add_comm] using hn.symm

/-- Weighted inverse-power gain on translated backward parabolic cylinders. -/
theorem b_backward_negative_power_gain_scaled
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (t : ℝ) (y : Vec d) (r : ℝ), 0 < r →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (t-r^2) t) (sourceBall y r) u G →
    ∀ ε p : ℝ, 0 < ε → 0 < p →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (t-r^2) t ×ˢ sourceBall y r), ε ≤ u z) →
    eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
      (volume.restrict (Set.Ioo (t-(r^2)/4) t ×ˢ sourceBall y (r/2))) ≤
    ((C * ENNReal.ofReal ((1+p)^2)) ^ (1/p) * ENNReal.ofReal (Real.rpow r (-(2/p)))) *
      eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (t-r^2) t ×ˢ sourceBall y r)) := by
  obtain ⟨C, hC, hgain⟩ := b_backward_negative_power_gain_at_zero d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro t y r hr ρ α hell u G hcal ε p hε hp hu
  have hc := c13_weighted_caloric_time_translation t (t-r^2) t (sourceBall y r) ρ α u G hcal
  have hc' : IsWeightedCaloric ρ α (Set.Ioo (-r^2) 0) (sourceBall y r)
      (fun z => u (t+z.1,z.2)) (fun z => G (t+z.1,z.2)) := by
    simpa only [sub_sub_cancel_left, sub_self, add_comm] using hc
  have hm := c13_time_translation_measurePreserving (d := d) t (t-r^2) t (sourceBall y r)
  have hu' : ∀ᵐ z ∂volume.restrict (Set.Ioo (-r^2) 0 ×ˢ sourceBall y r),
      ε ≤ u (t+z.1, z.2) := by
    have h := hm.quasiMeasurePreserving.ae hu
    simpa only [sub_sub_cancel_left, sub_self, add_comm] using h
  have h := hgain y r hr ρ α hell _ _ hc' ε p hε hp hu'
  have hs := b_backward_time_shift_eLpNorm t (-(r^2)/4) 0
    (sourceBall y (r/2)) (ENNReal.ofReal (p * (((d : ℝ)+2)/d))) (fun z => (u z)⁻¹)
  have hl := b_backward_time_shift_eLpNorm t (-r^2) 0
    (sourceBall y r) (ENNReal.ofReal p) (fun z => (u z)⁻¹)
  rw [hs, hl] at h
  simpa only [sub_eq_add_neg, add_zero, neg_div] using h


end EinsteinFull.Calculus
