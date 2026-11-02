import EinsteinFull.Calculus.C17TubeParabolicEnergyScaling
import EinsteinFull.Calculus.C20TubeWeightedGradientEnergyLimit

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The full parabolic affine map on the smaller cylinder has a positive Jacobian. -/
theorem c17_parabolic_small_cylinder_map {d : ℕ} (y : Vec d) {r : ℝ} (hr : 0 < r) :
    Measure.map (fun z : ℝ × Vec d => (r^2*z.1, y+r • z.2))
      (volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2))) =
      (ENNReal.ofReal |(r^2)⁻¹| * ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)) •
      (volume : Measure (ℝ × Vec d)).restrict
        (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2)) := by
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (r^2*z.1, y+r • z.2)
  have hf : Measurable F := ((measurable_const_mul (r^2)).comp measurable_fst).prodMk
    ((measurable_const_add y).comp ((measurable_const_smul r).comp measurable_snd))
  have hp : F ⁻¹' (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2)) =
      Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2) := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, F, sourceBall, Set.mem_ofPred_eq,
      add_sub_cancel_left, sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos hr,
      Set.mem_Ioo]
    have hs : 0 < r^2 := sq_pos_of_pos hr
    constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> constructor
    · constructor <;> nlinarith
    · nlinarith
    · constructor <;> nlinarith
    · nlinarith
  have hm : Measure.map F volume =
      (ENNReal.ofReal |(r^2)⁻¹| * ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹)) •
      (volume : Measure (ℝ × Vec d)) := by
    change Measure.map (Prod.map (fun t : ℝ => r^2*t) (fun x : Vec d => y+r • x)) volume = _
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.map_prod_map _ _
      (measurable_const_mul _) (c17_spatial_affine_embedding y hr).measurable,
      show (fun t : ℝ => r^2*t) = (fun t : ℝ => 0 + r^2*t) by ext; simp,
      c20_map_volume_affine_time 0 (r^2) (ne_of_gt (sq_pos_of_pos hr)),
      c17_spatial_affine_map_volume y hr, Measure.prod_smul_left, Measure.prod_smul_right,
      ← smul_smul, ← Measure.volume_eq_prod]
  change Measure.map F (volume.restrict _) = _
  rw [← hp, ← Measure.restrict_map hf (measurableSet_Ioo.prod
    (c17_isOpen_sourceBall y (r/2)).measurableSet), hm, Measure.restrict_smul]

/-- A unit-cylinder estimate scales to every positive radius. -/
@[nolint unusedArguments]
theorem c17_scaled_local_max_of_unit_bound
 (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
 (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
   IsUniformlyElliptic κ ρ α →
   ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
   IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
   essSup (fun z => ENNReal.ofReal |u z|)
    (volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
   ENNReal.ofReal (C * Real.sqrt
    (∫ z in Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
 (y : Vec d) (r : ℝ) (hr : 0 < r)
 (ρ : Vec d → ℝ) (α : Vec d → Mat d)
 (hell : IsUniformlyElliptic κ ρ α)
 (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
 (hcal : IsWeightedCaloric ρ α (Set.Ioo (-r^2) (r^2)) (sourceBall y r) u G) :
 essSup (fun z => ENNReal.ofReal |u z|)
  (volume.restrict (Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2))) ≤
 ENNReal.ofReal (C * Real.sqrt
  ((r^(d+2))⁻¹ * ∫ z in Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r, |u z|^2)) := by
  have he : IsUniformlyElliptic κ (fun x => ρ (y+r • x)) (fun x => α (y+r • x)) := by
    exact ⟨hell.1.comp (c17_spatial_affine_embedding y hr).measurable,
      hell.2.1.comp (c17_spatial_affine_embedding y hr).measurable, fun x => hell.2.2 _⟩
  have hc := c17_weighted_caloric_parabolic_rescale 0 y hr ρ α u G (by simpa using hcal)
  simp only [zero_add] at hc
  have hu := hunit _ _ he _ _ hc
  have hi := c17_parabolic_integral_rescale y hr (-1) 1 (fun z => |u z|^2)
  simp only [mul_neg, mul_one] at hi
  have hp : r^2 * r^d = r^(d+2) := by rw [pow_add]; ring
  rw [hp] at hi
  rw [hi] at hu
  have hemb : MeasurableEmbedding (fun z : ℝ × Vec d => (r^2*z.1, y+r • z.2)) := by
    exact ((Homeomorph.smulOfNeZero (r^2) (ne_of_gt (sq_pos_of_pos hr))).prodCongr
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft y))).measurableEmbedding
  have hn : ENNReal.ofReal |(r^2)⁻¹| * ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) ≠ 0 := by
    apply mul_ne_zero <;> apply ENNReal.ofReal_ne_zero_iff.mpr <;> positivity
  have hs := hemb.essSup_map_measure (g := fun z => ENNReal.ofReal |u z|)
    (μ := volume.restrict (Set.Ioo (-1/4:ℝ) (1/4) ×ˢ sourceBall 0 (1/2)))
  rw [c17_parabolic_small_cylinder_map y hr, essSup_ennreal_smul_measure hn] at hs
  exact hs.trans_le hu

end EinsteinFull.Calculus
