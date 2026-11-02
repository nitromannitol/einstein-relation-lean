import EinsteinFull.Calculus.C12TubeWeightedGaussianUpper
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- The literal spectral row square is controlled by the supplied kernel mass. -/
theorem c9_supplied_literal_row_sq_le_kernel_mass {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (h : IsUniformlyElliptic κ ρ α)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
      (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
      (s : DirichletSpectralResolution ρ α R)
      (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
        ∀ y ∈ sourceBall (0 : Vec d) R,
          K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
            s.eigenfunction n x * s.eigenfunction n y)
      (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
      (B : Set (Vec d)) (hB : MeasurableSet B) (hBb : B ⊆ sourceBall 0 R),
      (∫ y in B, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y)^2 ∂dirichletVolume ρ R) ≤
        C * t ^ (-(d : ℝ) / 2) * ∫ y in B, K t x y := by
  obtain ⟨C, hC, hbound⟩ := c12_supplied_restricted_row_L2_sq_le_mass hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK s hs t ht x hx B hB hBb
  let row := spectralHeatRow s t x
  let f := B.indicator fun y => row y
  have hf : MemLp f 2 (dirichletVolume ρ R) := (Lp.memLp row).indicator hB
  have hnorm : ‖hf.toLp f‖ ^ 2 = ∫ y, f y ^ 2 ∂dirichletVolume ρ R := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hrow : (∫ y in B, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n y)^2 ∂dirichletVolume ρ R) =
      ‖hf.toLp f‖ ^ 2 := by
    rw [hnorm, ← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx] with y hy
    change row y = _ at hy
    by_cases hyB : y ∈ B
    · simp only [Set.indicator_of_mem hyB, f]
      rw [hy]
    · simp [f, hyB]
  rw [hrow, ← c12_supplied_row_mass_eq_kernel_mass hd hκ hR h K s hs t ht x hx B hB hBb]
  exact hbound R hR ρ α h K G hK s hs t ht x hx B hB

/-- Separated kernel masses, scaled by any fixed real power, vanish almost everywhere on the dyadic sequence. -/
theorem c9_supplied_dyadic_scaled_mass_ae_zero {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y))
    (q : ℝ) (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
      Tendsto (fun n : ℕ => (t₀ / (4 : ℝ)^n) ^ (-q) *
        ∫ y in B, K (t₀ / (4 : ℝ)^n) x y) atTop (𝓝 0) := by
  let t (n : ℕ) : ℝ := t₀ / (4 : ℝ)^n
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htlim : Tendsto t atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).const_mul t₀
      simpa [t, div_eq_mul_inv, inv_pow] using h
    · exact Filter.Eventually.of_forall fun n => ht n
  let q' := q + 1
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : MemLp (fun _ : Vec d => (1 : ℝ)) 2 (dirichletVolume ρ R) := memLp_const 1
  obtain ⟨s, hs⟩ := c12_supplied_kernel_heat_action_L2 hκ h K G hK
  let f : Lp ℝ 2 (dirichletVolume ρ R) := (hv.indicator hB).toLp (B.indicator fun _ => 1)
  let g (n : ℕ) : Lp ℝ 2 (dirichletVolume ρ R) :=
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun i => (s.eigenvalue_pos i).le) ⟨t n, (ht n).le⟩ f
  let u (n : ℕ) : Lp ℝ 2 (dirichletVolume ρ R) :=
    (t n) ^ (-q') • ((Lp.memLp (g n)).indicator hA).toLp (A.indicator fun x => g n x)
  have hg (n : ℕ) : (fun x => g n x) =ᵐ[dirichletVolume ρ R]
      fun x => ∫ y in B, K (t n) x y := by
    filter_upwards [hs ⟨t n, (ht n).le⟩ (ht n) f] with x hx
    change g n x = ∫ y in sourceBall (0 : Vec d) R, K (t n) x y * f y at hx
    rw [hx, c12_restricted_input_kernel_integral hκ h B hB hBb (fun _ => 1) hv]
    simp
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt
      (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  have hnorm (n : ℕ) : ‖u n‖ ^ 2 = (t n) ^ (-(2*q')) *
      (∫ x in A, ρ x * (∫ y in B, K (t n) x y)^2) := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (ht n).le _), mul_pow,
      c12_dirichlet_restricted_norm_sq hκ h A hA hAb (fun x => g n x) (Lp.memLp (g n))]
    have hr : ((t n) ^ (-q')) ^ (2 : ℕ) = (t n) ^ (-(2*q')) := by
      rw [pow_two, ← Real.rpow_add (ht n)]
      congr 1 <;> ring
    rw [hr]
    congr 1
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hAb (hac.ae_le (hg n))] with x hx
    rw [hx]
  have hsq : Tendsto (fun n => ‖u n‖ ^ 2) atTop (𝓝 0) := by
    simp_rw [hnorm]
    exact (c12_supplied_separated_kernel_mass_polynomial_decay hd hκ hR h K G hK
      A B hA hB hAb hBb δ hδ hsep (2*q')).comp htlim
  have hvnorm : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.tendsto 0 |>.comp hsq
    convert hh using 1
    · funext n
      exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp
  let v (n : ℕ) : Lp ℝ 2 (dirichletVolume ρ R) := t n • u n
  have hvbound : ∀ᶠ n in atTop, ‖v n‖ ≤ t n := by
    filter_upwards [hvnorm.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hn
    dsimp [v]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (ht n)]
    nlinarith [norm_nonneg (u n), ht n]
  have htSum : Summable t := by
    have h := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num)).mul_left t₀
    simpa [t, div_eq_mul_inv, inv_pow] using h
  have hvsum : Summable (fun n => ‖v n‖) := by
    apply htSum.of_norm_bounded_eventually_nat
    filter_upwards [hvbound] with n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hn
  have hvtop : (∑' n, ‖v n‖ₑ) ≠ ∞ := tsum_enorm_ne_top_iff_summable_norm.2 hvsum
  have hae := Lp.hasSum_coeFn_tsum hvtop
  have hrep : ∀ᵐ x ∂dirichletVolume ρ R, ∀ n, x ∈ A →
      v n x = (t n) ^ (-q) * ∫ y in B, K (t n) x y := by
    have he : ∀ n, ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
        v n x = (t n) ^ (-q) * ∫ y in B, K (t n) x y := by
      intro n
      filter_upwards [Lp.coeFn_smul (t n) (u n), Lp.coeFn_smul ((t n) ^ (-q'))
        (((Lp.memLp (g n)).indicator hA).toLp (A.indicator fun x => g n x)),
        ((Lp.memLp (g n)).indicator hA).coeFn_toLp, hg n] with x hx hy hz hw hxA
      change v n x = _
      rw [hx]
      change t n * u n x = _
      rw [hy]
      change t n * ((t n) ^ (-q') * (((Lp.memLp (g n)).indicator hA).toLp
        (A.indicator fun x => g n x)) x) = _
      rw [hz, Set.indicator_of_mem hxA, hw]
      have hp : t n * (t n) ^ (-q') = (t n) ^ (-q) := by
        calc
          t n * (t n) ^ (-q') = (t n) ^ (1 : ℝ) * (t n) ^ (-q') := by
            rw [Real.rpow_one]
          _ = (t n) ^ (-q) := by
            rw [← Real.rpow_add (ht n)]
            congr 1
            dsimp [q']
            ring
      rw [← mul_assoc, hp]
    exact ae_all_iff.mpr he
  filter_upwards [hae, hrep] with x hx hr hxA
  have hz : Tendsto (fun n => v n x) atTop (𝓝 0) := hx.summable.tendsto_atTop_zero
  exact hz.congr' (Filter.Eventually.of_forall fun n => hr n hxA)

/-- Off-diagonal squared spectral rows vanish along the full dyadic sequence. -/
theorem c9_native_offdiagonal_row_L2_dyadic_zero {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (s : DirichletSpectralResolution ρ α R)
    (hs : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAb : A ⊆ sourceBall 0 R) (hBb : B ⊆ sourceBall 0 R)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y))
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    ∀ᵐ x ∂dirichletVolume ρ R, x ∈ A →
      Tendsto (fun n : ℕ => ∫ y in B,
        (∑' i, Real.exp (-s.eigenvalue i * (t₀ / (4 : ℝ)^n)) *
          s.eigenfunction i x * s.eigenfunction i y)^2 ∂dirichletVolume ρ R)
        atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := c9_supplied_literal_row_sq_le_kernel_mass hd hκ
  filter_upwards [c9_supplied_dyadic_scaled_mass_ae_zero hd hκ hR h K G hK
    A B hA hB hAb hBb δ hδ hsep ((d : ℝ) / 2) t₀ ht₀] with x hx hxA
  have hlim := (hx hxA).const_mul C
  have hlim' : Tendsto (fun n : ℕ => C * (t₀ / (4 : ℝ)^n) ^ (-(d : ℝ) / 2) *
      ∫ y in B, K (t₀ / (4 : ℝ)^n) x y) atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero, neg_div] using hlim
  apply squeeze_zero' _ _ hlim'
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun y => sq_nonneg _
  · exact Filter.Eventually.of_forall fun n =>
      hbound R hR ρ α h K G hK s hs (t₀ / (4 : ℝ)^n)
        (by positivity) x (hAb hxA) B hB hBb

end EinsteinFull.Calculus
