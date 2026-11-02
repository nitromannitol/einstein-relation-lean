import EinsteinRelation.SpatialDirichlet.PhysicalResolventSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

private theorem physicalMemLp_norm_sq_le_of_measure_le {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (σ ρ : Vec d → ℝ) (K : ℝ)
    (hK : 0 ≤ K)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (f : Vec d → E)
    (hfσ : MemLp f 2 (densityWeightedMeasure σ))
    (hfρ : MemLp f 2 (densityWeightedMeasure ρ)) :
    ‖hfσ.toLp f‖ ^ 2 ≤ K * ∫ x, ‖f x‖ ^ 2 ∂densityWeightedMeasure ρ := by
  rw [l2_norm_sq_eq_integral_norm_sq]
  have hcoe := hfσ.coeFn_toLp
  have hnonneg : 0 ≤ᵐ[densityWeightedMeasure ρ] fun x => ‖f x‖ ^ 2 := by
    filter_upwards [] with x
    positivity
  have hint : Integrable (fun x => ‖f x‖ ^ 2) (densityWeightedMeasure ρ) :=
    hfρ.integrable_norm_pow (by norm_num : 2 ≠ 0)
  calc
    ∫ x, ‖hfσ.toLp f x‖ ^ 2 ∂densityWeightedMeasure σ =
        ∫ x, ‖f x‖ ^ 2 ∂densityWeightedMeasure σ := by
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
    _ ≤ K * ∫ x, ‖f x‖ ^ 2 ∂densityWeightedMeasure ρ :=
      integral_le_const_mul_of_measure_le
        (densityWeightedMeasure σ) (densityWeightedMeasure ρ) K hK hMeasure
        (fun x => ‖f x‖ ^ 2) hnonneg hint

private theorem dot_ofLp_eq_inner {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    dot (WithLp.ofLp v) (WithLp.ofLp w) = inner ℝ v w := by
  simp [dot, PiLp.inner_apply, RCLike.inner_apply, mul_comm]

private theorem physicalWeightedFormIntegrand_norm_le {d : ℕ}
    (ω : FieldPair d) (L : ℝ) (hL : 1 ≤ L) (hω : IsRegular L ω)
    {m : Measure (Vec d)} (u v : WeightedSobolevGraph m) (x : Vec d) :
    ‖weightedFormIntegrand ω.1 u v x‖ ≤
      (L / 2) * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by
  have hop : ∀ x ξ, euclideanNorm ((ω.1 x).mulVec ξ) ≤ L * euclideanNorm ξ := by
    intro x ξ
    exact Correctors.isElliptic_mulVec_euclideanNorm_le
      (lt_of_lt_of_le zero_lt_one hL) hω.1 x ξ
  have huNorm : euclideanNorm (WithLp.ofLp (u.weakGradient x)) =
      ‖u.weakGradient x‖ := TimeChange.euclideanNorm_eq_norm_toLp _
  have hvNorm : euclideanNorm (WithLp.ofLp (v.weakGradient x)) =
      ‖v.weakGradient x‖ := TimeChange.euclideanNorm_eq_norm_toLp _
  have hA : ‖(WithLp.toLp 2
      ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))) :
        EuclideanSpace ℝ (Fin d))‖ ≤ L * ‖v.weakGradient x‖ := by
    calc
      ‖(WithLp.toLp 2
          ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))) :
            EuclideanSpace ℝ (Fin d))‖ =
          euclideanNorm ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))) :=
        (TimeChange.euclideanNorm_eq_norm_toLp _).symm
      _ ≤ L * euclideanNorm (WithLp.ofLp (v.weakGradient x)) := hop x _
      _ = L * ‖v.weakGradient x‖ := by rw [hvNorm]
  have hdot : dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))) =
      inner ℝ (u.weakGradient x) (WithLp.toLp 2
        ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x)))) := by
    rw [← dot_ofLp_eq_inner]
  have hdotBound : |dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x)))| ≤
        L * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by
    rw [hdot]
    calc
      |inner ℝ (u.weakGradient x) (WithLp.toLp 2
          ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))))| ≤
          ‖u.weakGradient x‖ * ‖(WithLp.toLp 2
            ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x))) :
              EuclideanSpace ℝ (Fin d))‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖u.weakGradient x‖ * (L * ‖v.weakGradient x‖) :=
        mul_le_mul_of_nonneg_left hA (norm_nonneg _)
      _ = L * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by ring
  have hLhalf : 0 ≤ L / 2 := by linarith
  calc
    ‖weightedFormIntegrand ω.1 u v x‖ =
        (1 / 2 : ℝ) * |dot (WithLp.ofLp (u.weakGradient x))
          ((ω.1 x).mulVec (WithLp.ofLp (v.weakGradient x)))| := by
      simp [weightedFormIntegrand, Real.norm_eq_abs]
    _ ≤ (1 / 2 : ℝ) *
        (L * (‖u.weakGradient x‖ * ‖v.weakGradient x‖)) :=
      mul_le_mul_of_nonneg_left hdotBound (by norm_num)
    _ = (L / 2) * (‖u.weakGradient x‖ * ‖v.weakGradient x‖) := by ring

/-- The mass-plus-Dirichlet form of the physical resolvent is bounded on the full
force-weighted H¹ graph. The constant is explicit and follows from the bounded clock
and the actual ellipticity and boundedness of the physical coefficient. -/
theorem sourcePhysicalResolventForm_bounded {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L α : ℝ) (hL : 1 ≤ L)
    (hω : IsRegular L ω) (hα : 0 < α)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    |α * inner ℝ
        (sourcePhysicalValue (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) u)
        (sourcePhysicalValue (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) v) +
      sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v| ≤
      Real.exp (2 * L) * (α + L / 2) * ‖u‖ * ‖v‖ := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let μρ := densityWeightedMeasure ρ
  let μσ := densityWeightedMeasure σ
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : μσ ≤ ENNReal.ofReal K • μρ := by
    dsimp [μσ, μρ, σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  let gU := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gV := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let pU := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  let pV := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v
  have hK : 0 ≤ K := (Real.exp_pos _).le
  have hExpSquared : Real.exp L * Real.exp L = K := by
    dsimp [K]
    rw [← Real.exp_add]
    congr 1
    ring
  have hExpNormSq (w : densityWeightedH1Submodule ρ hρ hρpos) :
      (Real.exp L * ‖w‖) ^ 2 = K * ‖w‖ ^ 2 := by
    rw [pow_two]
    calc
      Real.exp L * ‖w‖ * (Real.exp L * ‖w‖) =
          (Real.exp L * Real.exp L) * ‖w‖ ^ 2 := by ring
      _ = K * ‖w‖ ^ 2 := by rw [hExpSquared]
  have hredValueU : ∫ x, ‖gU.value x‖ ^ 2 ∂μρ ≤ ‖u‖ ^ 2 := by
    have hvalueNonneg : 0 ≤ᵐ[μρ] fun x => ‖gU.value x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hgradNonneg : 0 ≤ᵐ[μρ] fun x => ‖gU.weakGradient x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hvalueIntegralNonneg := integral_nonneg_of_ae hvalueNonneg
    have hgradIntegralNonneg := integral_nonneg_of_ae hgradNonneg
    calc
      _ ≤ (∫ x, ‖gU.value x‖ ^ 2 ∂μρ) +
          ∫ x, ‖gU.weakGradient x‖ ^ 2 ∂μρ := le_add_of_nonneg_right hgradIntegralNonneg
      _ = ‖u‖ ^ 2 := by
        simpa [gU, μρ, ρ, hρ, hρpos, Real.norm_eq_abs, sq_abs] using
          (densityWeightedH1Space_norm_sq_integral u).symm
  have hredValueV : ∫ x, ‖gV.value x‖ ^ 2 ∂μρ ≤ ‖v‖ ^ 2 := by
    have hvalueNonneg : 0 ≤ᵐ[μρ] fun x => ‖gV.value x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hgradNonneg : 0 ≤ᵐ[μρ] fun x => ‖gV.weakGradient x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hvalueIntegralNonneg := integral_nonneg_of_ae hvalueNonneg
    have hgradIntegralNonneg := integral_nonneg_of_ae hgradNonneg
    calc
      _ ≤ (∫ x, ‖gV.value x‖ ^ 2 ∂μρ) +
          ∫ x, ‖gV.weakGradient x‖ ^ 2 ∂μρ := le_add_of_nonneg_right hgradIntegralNonneg
      _ = ‖v‖ ^ 2 := by
        simpa [gV, μρ, ρ, hρ, hρpos, Real.norm_eq_abs, sq_abs] using
          (densityWeightedH1Space_norm_sq_integral v).symm
  have hredGradU : ∫ x, ‖gU.weakGradient x‖ ^ 2 ∂μρ ≤ ‖u‖ ^ 2 := by
    have hvalueNonneg : 0 ≤ᵐ[μρ] fun x => ‖gU.value x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hgradNonneg : 0 ≤ᵐ[μρ] fun x => ‖gU.weakGradient x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hvalueIntegralNonneg := integral_nonneg_of_ae hvalueNonneg
    calc
      _ ≤ (∫ x, ‖gU.value x‖ ^ 2 ∂μρ) +
          ∫ x, ‖gU.weakGradient x‖ ^ 2 ∂μρ := le_add_of_nonneg_left hvalueIntegralNonneg
      _ = ‖u‖ ^ 2 := by
        simpa [gU, μρ, ρ, hρ, hρpos, Real.norm_eq_abs, sq_abs] using
          (densityWeightedH1Space_norm_sq_integral u).symm
  have hredGradV : ∫ x, ‖gV.weakGradient x‖ ^ 2 ∂μρ ≤ ‖v‖ ^ 2 := by
    have hvalueNonneg : 0 ≤ᵐ[μρ] fun x => ‖gV.value x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hgradNonneg : 0 ≤ᵐ[μρ] fun x => ‖gV.weakGradient x‖ ^ 2 := by
      filter_upwards [] with x
      positivity
    have hvalueIntegralNonneg := integral_nonneg_of_ae hvalueNonneg
    calc
      _ ≤ (∫ x, ‖gV.value x‖ ^ 2 ∂μρ) +
          ∫ x, ‖gV.weakGradient x‖ ^ 2 ∂μρ := le_add_of_nonneg_left hvalueIntegralNonneg
      _ = ‖v‖ ^ 2 := by
        simpa [gV, μρ, ρ, hρ, hρpos, Real.norm_eq_abs, sq_abs] using
          (densityWeightedH1Space_norm_sq_integral v).symm
  have hvalSqU : ‖pU.value_memLp.toLp pU.value‖ ^ 2 ≤ K * ‖u‖ ^ 2 := by
    calc
      _ ≤ K * ∫ x, ‖gU.value x‖ ^ 2 ∂μρ :=
        physicalMemLp_norm_sq_le_of_measure_le σ ρ K hK hMeasure gU.value
          pU.value_memLp gU.value_memLp
      _ ≤ K * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hredValueU hK
  have hvalSqV : ‖pV.value_memLp.toLp pV.value‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
    calc
      _ ≤ K * ∫ x, ‖gV.value x‖ ^ 2 ∂μρ :=
        physicalMemLp_norm_sq_le_of_measure_le σ ρ K hK hMeasure gV.value
          pV.value_memLp gV.value_memLp
      _ ≤ K * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hredValueV hK
  have hgradSqU : ‖pU.gradient_memLp.toLp pU.weakGradient‖ ^ 2 ≤ K * ‖u‖ ^ 2 := by
    calc
      _ ≤ K * ∫ x, ‖gU.weakGradient x‖ ^ 2 ∂μρ :=
        physicalMemLp_norm_sq_le_of_measure_le σ ρ K hK hMeasure gU.weakGradient
          pU.gradient_memLp gU.gradient_memLp
      _ ≤ K * ‖u‖ ^ 2 := mul_le_mul_of_nonneg_left hredGradU hK
  have hgradSqV : ‖pV.gradient_memLp.toLp pV.weakGradient‖ ^ 2 ≤ K * ‖v‖ ^ 2 := by
    calc
      _ ≤ K * ∫ x, ‖gV.weakGradient x‖ ^ 2 ∂μρ :=
        physicalMemLp_norm_sq_le_of_measure_le σ ρ K hK hMeasure gV.weakGradient
          pV.gradient_memLp gV.gradient_memLp
      _ ≤ K * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_left hredGradV hK
  have hValueNormU : ‖pU.value_memLp.toLp pU.value‖ ≤ Real.exp L * ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
    rw [hExpNormSq]
    exact hvalSqU
  have hValueNormV : ‖pV.value_memLp.toLp pV.value‖ ≤ Real.exp L * ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
    rw [hExpNormSq]
    exact hvalSqV
  have hGradientNormU : ‖pU.gradient_memLp.toLp pU.weakGradient‖ ≤ Real.exp L * ‖u‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
    rw [hExpNormSq]
    exact hgradSqU
  have hGradientNormV : ‖pV.gradient_memLp.toLp pV.weakGradient‖ ≤ Real.exp L * ‖v‖ := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))).mp
    rw [hExpNormSq]
    exact hgradSqV
  have hValueProduct :
      ‖pU.value_memLp.toLp pU.value‖ * ‖pV.value_memLp.toLp pV.value‖ ≤
        K * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ (Real.exp L * ‖u‖) * (Real.exp L * ‖v‖) :=
        mul_le_mul hValueNormU hValueNormV (norm_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
      _ = K * ‖u‖ * ‖v‖ := by
        calc
          (Real.exp L * ‖u‖) * (Real.exp L * ‖v‖) =
              (Real.exp L * Real.exp L) * ‖u‖ * ‖v‖ := by ring
          _ = K * ‖u‖ * ‖v‖ := by rw [hExpSquared]
  have hGradientProduct :
      ‖pU.gradient_memLp.toLp pU.weakGradient‖ *
        ‖pV.gradient_memLp.toLp pV.weakGradient‖ ≤ K * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ (Real.exp L * ‖u‖) * (Real.exp L * ‖v‖) :=
        mul_le_mul hGradientNormU hGradientNormV (norm_nonneg _)
          (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))
      _ = K * ‖u‖ * ‖v‖ := by
        calc
          (Real.exp L * ‖u‖) * (Real.exp L * ‖v‖) =
              (Real.exp L * Real.exp L) * ‖u‖ * ‖v‖ := by ring
          _ = K * ‖u‖ * ‖v‖ := by rw [hExpSquared]
  have hphysicalFormIntegrable : Integrable (weightedFormIntegrand ω.1 pU pV) μσ :=
    physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω pU pV
  have hgradientProductIntegrable : Integrable
      (fun x => ‖pU.weakGradient x‖ * ‖pV.weakGradient x‖) μσ :=
    pU.gradient_memLp.norm.integrable_mul pV.gradient_memLp.norm
  have hgradientMajorantIntegrable : Integrable
      (fun x => (L / 2) * (‖pU.weakGradient x‖ * ‖pV.weakGradient x‖)) μσ := by
    exact (hgradientProductIntegrable.const_mul (L / 2)).congr
      (ae_of_all _ fun x => by ring)
  have hpointwise : ∀ x, ‖weightedFormIntegrand ω.1 pU pV x‖ ≤
      (L / 2) * (‖pU.weakGradient x‖ * ‖pV.weakGradient x‖) := by
    intro x
    exact physicalWeightedFormIntegrand_norm_le ω L hL hω pU pV x
  have hformProduct : ∫ x, ‖pU.weakGradient x‖ * ‖pV.weakGradient x‖ ∂μσ ≤
      ‖pU.gradient_memLp.toLp pU.weakGradient‖ *
        ‖pV.gradient_memLp.toLp pV.weakGradient‖ := by
    have hU : MemLp pU.weakGradient (ENNReal.ofReal (2 : ℝ)) μσ := by
      simpa using pU.gradient_memLp
    have hV : MemLp pV.weakGradient (ENNReal.ofReal (2 : ℝ)) μσ := by
      simpa using pV.gradient_memLp
    have hholder := integral_mul_norm_le_Lp_mul_Lq
      (μ := μσ) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
      hU hV
    have hrootU :
        (∫ x, ‖pU.weakGradient x‖ ^ (2 : ℝ) ∂μσ) ^ (1 / (2 : ℝ)) =
          ‖pU.gradient_memLp.toLp pU.weakGradient‖ := by
      have hcoe := pU.gradient_memLp.coeFn_toLp
      have hIntegral :
          ∫ x, ‖pU.weakGradient x‖ ^ (2 : ℝ) ∂μσ =
            ∫ x, ‖pU.gradient_memLp.toLp pU.weakGradient x‖ ^ 2 ∂μσ := by
        apply integral_congr_ae
        filter_upwards [hcoe] with x hx
        rw [← hx]
        exact Real.rpow_two _
      rw [← Real.sqrt_eq_rpow, hIntegral, ← l2_norm_sq_eq_integral_norm_sq]
      exact Real.sqrt_sq (norm_nonneg _)
    have hrootV :
        (∫ x, ‖pV.weakGradient x‖ ^ (2 : ℝ) ∂μσ) ^ (1 / (2 : ℝ)) =
          ‖pV.gradient_memLp.toLp pV.weakGradient‖ := by
      have hcoe := pV.gradient_memLp.coeFn_toLp
      have hIntegral :
          ∫ x, ‖pV.weakGradient x‖ ^ (2 : ℝ) ∂μσ =
            ∫ x, ‖pV.gradient_memLp.toLp pV.weakGradient x‖ ^ 2 ∂μσ := by
        apply integral_congr_ae
        filter_upwards [hcoe] with x hx
        rw [← hx]
        exact Real.rpow_two _
      rw [← Real.sqrt_eq_rpow, hIntegral, ← l2_norm_sq_eq_integral_norm_sq]
      exact Real.sqrt_sq (norm_nonneg _)
    calc
      _ ≤ (∫ x, ‖pU.weakGradient x‖ ^ (2 : ℝ) ∂μσ) ^ (1 / (2 : ℝ)) *
          (∫ x, ‖pV.weakGradient x‖ ^ (2 : ℝ) ∂μσ) ^ (1 / (2 : ℝ)) := by
        simpa [ENNReal.ofReal_ofNat] using hholder
      _ = _ := congrArg₂ (fun a b : ℝ => a * b) hrootU hrootV
  have hformAbs :
      |sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v| ≤
        (L / 2) * (K * ‖u‖ * ‖v‖) := by
    change |weightedSpatialForm ω.1 pU pV| ≤ _
    rw [weightedSpatialForm]
    calc
      |∫ x, weightedFormIntegrand ω.1 pU pV x ∂μσ| ≤
          ∫ x, ‖weightedFormIntegrand ω.1 pU pV x‖ ∂μσ := by
        simpa [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (weightedFormIntegrand ω.1 pU pV))
      _ ≤ ∫ x, (L / 2) *
          (‖pU.weakGradient x‖ * ‖pV.weakGradient x‖) ∂μσ :=
        integral_mono_ae hphysicalFormIntegrable.norm hgradientMajorantIntegrable
          (Filter.Eventually.of_forall hpointwise)
      _ = (L / 2) *
          ∫ x, ‖pU.weakGradient x‖ * ‖pV.weakGradient x‖ ∂μσ := by
        rw [integral_const_mul]
      _ ≤ (L / 2) *
          (‖pU.gradient_memLp.toLp pU.weakGradient‖ *
            ‖pV.gradient_memLp.toLp pV.weakGradient‖) :=
        mul_le_mul_of_nonneg_left hformProduct (by linarith)
      _ ≤ (L / 2) * (K * ‖u‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left hGradientProduct (by linarith)
  have hmassAbs :
      |inner ℝ
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v)| ≤ K * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure u‖ *
          ‖sourcePhysicalValue ρ hρ hρpos σ K hMeasure v‖ := abs_real_inner_le_norm _ _
      _ = ‖pU.value_memLp.toLp pU.value‖ * ‖pV.value_memLp.toLp pV.value‖ := rfl
      _ ≤ K * ‖u‖ * ‖v‖ := hValueProduct
  have hmassTerm :
      |α * inner ℝ
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v)| ≤
        α * (K * ‖u‖ * ‖v‖) := by
    rw [abs_mul, abs_of_nonneg hα.le]
    exact mul_le_mul_of_nonneg_left hmassAbs hα.le
  have hformTerm :
      |sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v| ≤
        (L / 2) * (K * ‖u‖ * ‖v‖) := hformAbs
  have hsum := abs_add_le
    (α * inner ℝ (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
      (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v))
    (sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v)
  calc
    _ ≤ |α * inner ℝ (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u)
          (sourcePhysicalValue ρ hρ hρpos σ K hMeasure v)| +
        |sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v| := hsum
    _ ≤ α * (K * ‖u‖ * ‖v‖) + (L / 2) * (K * ‖u‖ * ‖v‖) :=
      add_le_add hmassTerm hformTerm
    _ = Real.exp (2 * L) * (α + L / 2) * ‖u‖ * ‖v‖ := by
      dsimp [K]
      ring

end EinsteinRelation.SpatialDirichlet

