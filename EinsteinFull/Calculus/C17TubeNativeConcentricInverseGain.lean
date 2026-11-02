import EinsteinFull.Calculus.C17TubeInverseGainRadiusAlgebra
import EinsteinFull.Calculus.C9TubeNativeCutoffSurvival
import EinsteinFull.Calculus.C18TubeCaloricTimeTranslation
import EinsteinFull.Calculus.C11TubeWeightedZeroPastRepresentative
import EinsteinFull.Calculus.C8TubeWeightedParabolicPoincare
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped ENNReal Topology

namespace EinsteinFull.Calculus

/-- Transfer a unit inverse gain to a concentric physical cylinder. -/
theorem c17_native_inverse_gain_concentric_radius {d : ℕ} (y : Vec d) {r R p C : ℝ}
    (hd : 0 < (d : ℝ)) (hp : 0 < p) (hR : 0 < R) (hrR : r < R)
    (hC : 0 ≤ C) (u : ℝ × Vec d → ℝ) :
    let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
    let q : ℝ := p * (((d : ℝ)+2)/d)
    eLpNorm ((fun z => (u z)⁻¹) ∘ F) (ENNReal.ofReal q) (volume.restrict
      (Set.Ioo (-((r/R)^2)) ((r/R)^2) ×ˢ sourceBall (0 : Vec d) (r/R))) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-r/R) (-(2/p)))) *
        eLpNorm ((fun z => (u z)⁻¹) ∘ F) (ENNReal.ofReal p) (volume.restrict
          (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)) →
    eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal q) (volume.restrict
      (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r)) ≤
      ENNReal.ofReal (C * Real.rpow (R-r) (-(2/p))) *
        eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p) (volume.restrict
          (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)) :=
  c17_inverse_gain_concentric_radius y hd hp hR hrR hC u

/-- A full unit-cylinder weighted-caloric gain yields the physical-cylinder gain. -/
theorem c17_native_weighted_caloric_inverse_gain_concentric
    {d : ℕ} {κ p C : ℝ} (hd : 0 < (d : ℝ)) (hp : 0 < p) (hC : 0 ≤ C)
    (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (v : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) v H →
      ∀ ε : ℝ, 0 < ε →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), ε ≤ v z) →
      ∀ s : ℝ, 0 < s → s < 1 →
      eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
        (volume.restrict (Set.Ioo (-(s^2)) (s^2) ×ˢ sourceBall (0 : Vec d) s)) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-s) (-(2/p)))) *
        eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)))
    (y : Vec d) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (hrR : r < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-(R^2)) (R^2)) (sourceBall y R) u G)
    (ε : ℝ) (hε : 0 < ε)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R), ε ≤ u z) :
    eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
      (volume.restrict (Set.Ioo (-(r^2)) (r^2) ×ˢ sourceBall y r)) ≤
      ENNReal.ofReal (C * Real.rpow (R-r) (-(2/p))) *
        eLpNorm (fun z => (u z)⁻¹) (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)) := by
  have he : IsUniformlyElliptic κ (fun x => ρ (y+R • x)) (fun x => α (y+R • x)) :=
    ⟨hell.1.comp (c17_spatial_affine_embedding y hR).measurable,
      hell.2.1.comp (c17_spatial_affine_embedding y hR).measurable, fun x => hell.2.2 _⟩
  have hc := c17_weighted_caloric_parabolic_rescale 0 y hR ρ α u G (by simpa using hcal)
  simp only [zero_add] at hc
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (R^2*z.1, y+R • z.2)
  have hemb : MeasurableEmbedding F := by
    exact ((Homeomorph.smulOfNeZero (R^2) (ne_of_gt (sq_pos_of_pos hR))).prodCongr
      ((Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft y))).measurableEmbedding
  have hm : Measure.map F volume =
      (ENNReal.ofReal |(R^2)⁻¹| * ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume : Measure (ℝ × Vec d)) := by
    change Measure.map (Prod.map (fun t : ℝ => R^2*t) (fun x : Vec d => y+R • x)) volume = _
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.map_prod_map _ _
      (measurable_const_mul _) (c17_spatial_affine_embedding y hR).measurable,
      show (fun t : ℝ => R^2*t) = (fun t : ℝ => 0 + R^2*t) by ext; simp,
      c20_map_volume_affine_time 0 (R^2) (ne_of_gt (sq_pos_of_pos hR)),
      c17_spatial_affine_map_volume y hR, Measure.prod_smul_left, Measure.prod_smul_right,
      ← smul_smul, ← Measure.volume_eq_prod]
  have hmap : Measure.map F (volume.restrict
      (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) =
      (ENNReal.ofReal |(R^2)⁻¹| * ENNReal.ofReal (|R ^ Module.finrank ℝ (Vec d)|⁻¹)) •
        (volume.restrict (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R)) := by
    have hpre : F ⁻¹' (Set.Ioo (-(R^2)) (R^2) ×ˢ sourceBall y R) =
        Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
      simpa only [F, div_self hR.ne', one_pow] using
        c17_concentric_cylinder_preimage y hR R
    rw [← hpre, ← Measure.restrict_map hemb.measurable
      (measurableSet_Ioo.prod (c17_isOpen_sourceBall y R).measurableSet), hm, Measure.restrict_smul]
  have hu' : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      ε ≤ u (R^2*z.1, y+R • z.2) := by
    change ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      ε ≤ u (F z)
    apply (hemb.ae_map_iff (p := fun z => ε ≤ u z)
      (μ := volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1))).mp
    rw [hmap]
    exact Measure.ae_smul_measure hu _
  apply c17_native_inverse_gain_concentric_radius y hd hp hR hrR hC u
  exact hunit _ _ he _ _ hc ε hε hu' (r/R) (div_pos hr hR) ((div_lt_one hR).2 hrR)

/-- The conditional unit gain applies to the actual positive-time spectral row,
    after centering time and adding a positive constant. -/
@[nolint unusedArguments]
theorem c17_native_spectral_row_inverse_gain
    {d : ℕ} (hd : 2 ≤ d) {κ p C : ℝ} (hκ : 0 < κ) (hp : 0 < p)
    (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (v : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) v H →
      ∀ ε : ℝ, 0 < ε →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1), ε ≤ v z) →
      ∀ a : ℝ, 0 < a → a < 1 →
      eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
        (volume.restrict (Set.Ioo (-(a^2)) (a^2) ×ˢ sourceBall (0 : Vec d) a)) ≤
      (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-a) (-(2/p)))) *
        eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)))
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α 1)
    (u : ℕ → DirichletHilbertSpace (d := d) 1 (by norm_num))
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ 1 (by norm_num) κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n (w : DirichletHilbertSpace (d := d) 1 (by norm_num)), (∫ x in sourceBall (0 : Vec d) 1,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ 1 (by norm_num) κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ 1 (by norm_num) κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (τ : ℝ) (hτ : 0 < τ) (x : Vec d) (hx : x ∈ sourceBall 0 1)
    (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (ha1 : a < 1) :
    let v : ℝ × Vec d → ℝ := fun z =>
      (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (1 + z.1)) *
        s.eigenfunction n z.2 * s.eigenfunction n y) *
          spectralHeatRow s τ x y ∂dirichletVolume ρ 1) + ε
    eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal (p * (((d : ℝ)+2)/d)))
      (volume.restrict (Set.Ioo (-(a^2)) (a^2) ×ˢ sourceBall (0 : Vec d) a)) ≤
    (ENNReal.ofReal C * ENNReal.ofReal (Real.rpow (1-a) (-(2/p)))) *
      eLpNorm (fun z => (v z)⁻¹) (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-1) 1 ×ˢ sourceBall (0 : Vec d) 1)) := by
  let w : ℝ × Vec d → ℝ := fun z => ∫ y,
    (∑' n, Real.exp (-s.eigenvalue n * z.1) * s.eigenfunction n z.2 *
      s.eigenfunction n y) * spectralHeatRow s τ x y ∂dirichletVolume ρ 1
  obtain ⟨G, hG⟩ := c9_native_kernel_action_weighted_caloric hd hκ (by norm_num : (0:ℝ) < 1)
    hell s u hs hb hv (spectralHeatRow s τ x) 2 (by norm_num)
  have heq (z : ℝ × Vec d) (hz : z ∈ Set.Ioo (0 : ℝ) 2 ×ˢ sourceBall (0 : Vec d) 1) :
      w z = ∑' n, Real.exp (-s.eigenvalue n * (z.1 + τ)) *
        s.eigenfunction n x * s.eigenfunction n z.2 := by
    calc
      w z = inner ℝ (spectralHeatRow s z.1 z.2) (spectralHeatRow s τ x) := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ hell (by norm_num) s z.1 hz.1.1 z.2 hz.2] with y hy
        change spectralHeatRow s z.1 z.2 y = _ at hy
        simp only [w, RCLike.inner_apply, conj_trivial, hy, mul_comm]
      _ = _ := by
        rw [spectral_heat_row_inner hd hκ hell (by norm_num) s z.1 τ hz.1.1 hτ z.2 x hz.2 hx]
        apply tsum_congr
        intro n
        ring
  have hc : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1)
      (fun z => w (1+z.1,z.2)) (fun z => G (1+z.1,z.2)) := by
    apply c18_weighted_caloric_time_translate ρ α (-1) 1 1 (sourceBall 0 1) w G
    norm_num [w] at hG ⊢
    exact hG
  have hn : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      0 ≤ w (1+z.1,z.2) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
      (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet)] with z hz
    have hz' : (1+z.1,z.2) ∈ Set.Ioo (0 : ℝ) 2 ×ˢ sourceBall (0 : Vec d) 1 := by
      exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
    rw [heq _ hz']
    have ht : 0 < 1+z.1+τ := by linarith [hz.1.1]
    simpa only [Real.coe_toNNReal _ ht.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ hell 1 (by norm_num) s hs u hb hv).2
        (1+z.1+τ).toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht)
        x hx z.2 hz.2
  have hfinite : volume (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) ≠ ⊤ := by
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioo (-1 : ℝ) 1)) :=
      isFiniteMeasure_restrict.mpr (by simp)
    haveI : IsFiniteMeasure (volume.restrict (sourceBall (0 : Vec d) 1)) :=
      isFiniteMeasure_restrict.mpr (by
        rw [c8_sourceBall_eq_euclideanBall 0 (by norm_num)]
        exact PDE.volume_euclideanBall_ne_top 0 (by norm_num))
    haveI : IsFiniteMeasure (volume.restrict
        (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
      infer_instance
    simpa only [Measure.restrict_apply_univ] using
      (measure_ne_top (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1)) Set.univ)
  have hc' := c11_weighted_caloric_sub_const hκ hell hfinite hc (-ε)
  have hn' : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      ε ≤ w (1+z.1,z.2) - (-ε) := by
    filter_upwards [hn] with z hz
    linarith
  simpa only [sub_neg_eq_add] using hunit ρ α hell _ _ hc' ε hε hn' a ha ha1

/-- A pointwise multiplicity bound controls the sum of local moments. -/
theorem c17_lintegral_sum_le_of_bounded_overlap {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (U : Finset I) (V : I → Set X) (A : Set X)
    (hV : ∀ i ∈ U, MeasurableSet (V i)) (hA : MeasurableSet A)
    (K : ℝ≥0∞) (f : X → ℝ≥0∞) (hf : AEMeasurable f μ)
    (hoverlap : ∀ x, (∑ i ∈ U, (V i).indicator (fun _ => (1 : ℝ≥0∞)) x) ≤
      K * A.indicator (fun _ => (1 : ℝ≥0∞)) x) :
    (∑ i ∈ U, ∫⁻ x in V i, f x ∂μ) ≤ K * ∫⁻ x in A, f x ∂μ := by
  classical
  calc
    (∑ i ∈ U, ∫⁻ x in V i, f x ∂μ) =
        ∫⁻ x, ∑ i ∈ U, (V i).indicator f x ∂μ := by
      rw [lintegral_finsetSum' U (fun i hi => hf.indicator (hV i hi))]
      apply Finset.sum_congr rfl
      intro i hi
      rw [lintegral_indicator (hV i hi)]
    _ ≤ ∫⁻ x, K * A.indicator f x ∂μ := by
      apply lintegral_mono
      intro x
      change (∑ i ∈ U, (V i).indicator f x) ≤ K * A.indicator f x
      have heq : (∑ i ∈ U, (V i).indicator f x) =
          (∑ i ∈ U, (V i).indicator (fun _ => (1 : ℝ≥0∞)) x) * f x := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hx : x ∈ V i <;> simp [Set.indicator, hx]
      rw [heq]
      have h : (∑ i ∈ U, (V i).indicator (fun _ => (1 : ℝ≥0∞)) x) * f x ≤
          (K * A.indicator (fun _ => (1 : ℝ≥0∞)) x) * f x := by
        gcongr
        exact hoverlap x
      convert h using 1
      by_cases hx : x ∈ A <;> simp [Set.indicator, hx, mul_assoc]
    _ = K * ∫⁻ x in A, f x ∂μ := by
      rw [lintegral_const_mul'' K (hf.indicator hA), lintegral_indicator hA]

/-- A separated family of centers near one point has uniformly bounded size. -/
theorem c17_card_separated_near_point {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U : Finset E) (x : E)
    (r : ℝ) (hr : 0 < r) (hnear : ∀ y ∈ U, ‖y - x‖ ≤ 2 * r)
    (hsep : ∀ y ∈ U, ∀ z ∈ U, y ≠ z → r ≤ ‖y - z‖) :
    U.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let F : E → E := fun y => r⁻¹ • (y - x)
  have hF : Function.Injective F := by
    intro y z h
    have hh := congrArg (fun w : E => r • w) h
    dsimp only [F] at hh
    simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hh
    have hh' := congrArg (fun w : E => w + x) hh
    simpa using hh'
  have hn (y : E) (hy : y ∈ U) : ‖F y‖ ≤ 2 := by
    dsimp [F]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
    apply (div_le_iff₀ hr).2
    simpa only [mul_comm] using hnear y hy
  have hs (y z : E) (hy : y ∈ U) (hz : z ∈ U) (hyz : y ≠ z) :
      1 ≤ ‖F y - F z‖ := by
    have heq : F y - F z = r⁻¹ • (y - z) := by
      dsimp [F]
      rw [← smul_sub]
      congr 1
      abel
    rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
    apply (le_div_iff₀ hr).2
    simpa using hsep y hy z hz hyz
  have hcard : (U.image F).card ≤ 5 ^ Module.finrank ℝ E := by
    apply Besicovitch.card_le_of_separated
    · intro a ha
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      exact hn y hy
    · intro a ha b hb hab
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hb
      exact hs y z hy hz (fun h => hab (congrArg F h))
  simpa only [Finset.card_image_of_injective U hF] using hcard

end EinsteinFull.Calculus
