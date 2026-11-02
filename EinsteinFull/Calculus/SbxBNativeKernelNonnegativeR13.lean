import EinsteinFull.Calculus.SbxBNativeSpectralCompactnessR06

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull.Calculus
open EinsteinRelation External.Source.GMP Blueprint.TubeProbability
open Blueprint.TubeProbability.DimensionLift Blueprint.SbxS3UniformCrossHeat

noncomputable section

/-- Positivity preservation of the actual native spectral heat operator. -/
def br13NativeSpectralHeatPositive {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R : ℝ} (s : DirichletSpectralResolution ρ α R) : Prop :=
  ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
    (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
    ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
      SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t f x

/-- A continuous native spectral kernel is nonnegative at every interior pair
when its actual weighted heat operator preserves nonnegative data. -/
theorem br13_native_kernel_nonnegative_of_heat_positive {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hpositive : br13NativeSpectralHeatPositive s)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (x y : Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    0 ≤ ρ y * ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n x * s.eigenfunction n y := by
  classical
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun z _ => (hell.2.2 z).2.1)
  let row : Vec d → ℝ := fun z => ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
    s.eigenfunction i x * s.eigenfunction i z
  have hc : ContinuousOn row (sourceBall 0 R) := by
    apply (spectral_heat_continuousOn hd hκ hell hR s hs).comp
      (continuousOn_const.prodMk (continuousOn_const.prodMk continuousOn_id))
    intro z hz
    exact ⟨ht, hx, hz⟩
  have hrow : 0 ≤ row y := by
    by_contra hn
    have hneg : row y < 0 := lt_of_not_ge hn
    let V := sourceBall (0 : Vec d) R ∩ row ⁻¹' Set.Iio 0
    have hV : IsOpen V := hc.isOpen_inter_preimage (dirichletBall (d := d) R).isOpen isOpen_Iio
    obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV y ⟨hy, hneg⟩
    let B := Metric.ball y r
    have hB : IsOpen B := Metric.isOpen_ball
    have hsub : B ⊆ sourceBall 0 R := hrV.trans Set.inter_subset_left
    have hpos : 0 < dirichletVolume ρ R B :=
      dirichletVolume_open_pos hκ hell R hB hsub ⟨y, Metric.mem_ball_self hr⟩
    let f : Lp ℝ 2 (dirichletVolume ρ R) :=
      indicatorConstLp 2 hB.measurableSet (measure_ne_top _ _) (1 : ℝ)
    have hf : (∀ᵐ z ∂dirichletVolume ρ R, 0 ≤ f z) ∧
        HasCompactSupport (B.indicator (fun _ => (1 : ℝ))) := by
      constructor
      · filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB.measurableSet)
          (hμs := measure_ne_top (dirichletVolume ρ R) B) (c := (1 : ℝ))] with z hz
        rw [show f z = B.indicator (fun _ => (1 : ℝ)) z from hz]
        by_cases hzB : z ∈ B <;> simp [hzB]
      · apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall y r)
        exact Set.support_indicator_subset.trans Metric.ball_subset_closedBall
    have ha := hpositive t f hf.1
    have he := spectral_heat_operator_ae_kernel_action hd hκ hell hR s t ht f
    have hac : ∀ᵐ z ∂dirichletVolume ρ R,
        0 ≤ ∫ w, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i z * s.eigenfunction i w) * f w ∂dirichletVolume ρ R := by
      filter_upwards [ha, he] with z hz heq
      rw [← heq]
      exact hz
    let act : Vec d → ℝ := fun z => ∫ w, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i z * s.eigenfunction i w) * f w ∂dirichletVolume ρ R
    have hactc : ContinuousOn act (sourceBall 0 R) :=
      spectral_heat_action_continuousOn hd hκ hell hR s hs t ht f
    have haction : 0 ≤ act x := by
      by_contra hn'
      have hlt : act x < 0 := lt_of_not_ge hn'
      let W := sourceBall (0 : Vec d) R ∩ act ⁻¹' Set.Iio 0
      have hW : IsOpen W := hactc.isOpen_inter_preimage (dirichletBall (d := d) R).isOpen isOpen_Iio
      have hzero : dirichletVolume ρ R W = 0 := by
        apply measure_mono_null _ (ae_iff.mp hac)
        intro z hz
        exact not_le_of_gt hz.2
      exact (ne_of_gt (dirichletVolume_open_pos hκ hell R hW
        Set.inter_subset_left ⟨x, hx, hlt⟩)) hzero
    have hint : Integrable row (dirichletVolume ρ R) :=
      (spectral_heat_row_memLp hd hκ hell hR s t ht x hx).integrable (by norm_num)
    let g : Vec d → ℝ := B.indicator (fun z => -row z)
    have hg : Integrable g (dirichletVolume ρ R) := hint.neg.indicator hB.measurableSet
    have hgn : 0 ≤ g := by
      intro z
      by_cases hz : z ∈ B
      · simp only [g, Set.indicator_of_mem hz]
        exact neg_nonneg.mpr (hrV hz).2.le
      · simp [g, hz]
    have hsupport : B ⊆ Function.support g := by
      intro z hz
      simp only [Function.mem_support, g, Set.indicator_of_mem hz]
      exact neg_ne_zero.mpr (ne_of_lt (hrV hz).2)
    have hgpos : 0 < ∫ z, g z ∂dirichletVolume ρ R :=
      (integral_pos_iff_support_of_nonneg hgn hg).2 (lt_of_lt_of_le hpos (measure_mono hsupport))
    have heq : (∫ z, row z * f z ∂dirichletVolume ρ R) =
        -(∫ z, g z ∂dirichletVolume ρ R) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hB.measurableSet)
        (hμs := measure_ne_top (dirichletVolume ρ R) B) (c := (1 : ℝ))] with z hz
      rw [show f z = B.indicator (fun _ => (1 : ℝ)) z from hz]
      by_cases hzB : z ∈ B <;> simp [g, hzB]
    change 0 ≤ ∫ z, row z * f z ∂dirichletVolume ρ R at haction
    linarith
  exact mul_nonneg (hκ.le.trans (hell.2.2 y).1) hrow

#print axioms br13_native_kernel_nonnegative_of_heat_positive

end
end EinsteinFull.Calculus
