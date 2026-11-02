import EinsteinFull.Calculus.C8DyadicTransposeFluxSize

open MeasureTheory Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Within the force window the actual transpose endpoint propagates from
its value at the beginning of the window with a structural constant. -/
theorem c2_transpose_endpoint_propagation_window
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (s v : ℝ≥0)
    (hs : 0 < (s : ℝ)) (hsv : s ≤ v) (hvs : v ≤ 2 * s)
    (hz : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2) :
    ‖transposeEndpoint Q i Pdag β v‖ ≤
      Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
        ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2) *
      ‖transposeEndpoint Q i Pdag β s‖ := by
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 < K := mul_pos (Real.exp_pos _) (by linarith [D.one_le_ellipticity])
  have hforce : ‖ζ‖^2 * (s : ℝ) ≤ 2 := by
    have hh := (sq_le_sq₀ (by positivity : 0 ≤ ‖ζ‖ * Real.sqrt (2 * (s : ℝ)))
      (by norm_num : (0 : ℝ) ≤ 2)).mpr hz
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * (s : ℝ))] at hh
    nlinarith only [hh]
  have hv : v = (v - s) + s := (tsub_add_cancel_of_le hsv).symm
  have hprop : ‖transposeEndpoint Q i Pdag β v‖ ≤
      Real.exp (complexForceShift d D.ellipticity ζ * ((v : ℝ) - (s : ℝ))) *
        ‖transposeEndpoint Q i Pdag β s‖ := by
    calc
      _ = ‖Pdag (v-s) (transposeEndpoint Q i Pdag β s)‖ := by
        conv_lhs => rw [transposeEndpoint, hv, hPd.add hP]
        rfl
      _ ≤ ‖Pdag (v-s)‖ * ‖transposeEndpoint Q i Pdag β s‖ := (Pdag (v-s)).le_opNorm _
      _ ≤ _ := by
        rw [← NNReal.coe_sub hsv]
        exact mul_le_mul_of_nonneg_right (hPd.norm_le hP _) (norm_nonneg _)
  have hshift : Real.exp (complexForceShift d D.ellipticity ζ * ((v : ℝ) - (s : ℝ))) ≤
      Real.exp (2 * K * ((d : ℝ) * K)^2) := by
    apply Real.exp_le_exp.mpr
    have hvu : (v : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hvs
    calc
      _ ≤ complexForceShift d D.ellipticity ζ * (s : ℝ) :=
        mul_le_mul_of_nonneg_left (by linarith only [hvu]) (complexForceShift_nonneg Q ζ)
      _ = (K * ((d : ℝ) * K)^2) * (‖ζ‖^2 * (s : ℝ)) := by
        dsimp only [complexForceShift, K]; ring
      _ ≤ (K * ((d : ℝ) * K)^2) * 2 :=
        mul_le_mul_of_nonneg_left hforce (by positivity)
      _ = _ := by ring
  exact hprop.trans (mul_le_mul_of_nonneg_right hshift (norm_nonneg _))

/-- The actual density increment is controlled by its initial transpose
endpoint and the length of the force-weighted time window. -/
theorem c2_density_increment_bound_by_initial_endpoint
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) (s u : ℝ≥0)
    (hs : 0 < (s : ℝ)) (hsu : s ≤ u) (hus : u ≤ 2 * s)
    (hz : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2) :
    let := reducedLaw_probability Q
    ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) - Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ ≤
      2 * ‖ζ‖ * (s : ℝ) *
        (Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
          ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2) *
          ‖transposeEndpoint Q i Pdag β s‖) := by
  let := reducedLaw_probability Q
  let E := Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
    ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2)
  have hsu' : (s : ℝ) ≤ (u : ℝ) := by exact_mod_cast hsu
  have hus' : (u : ℝ) ≤ 2 * (s : ℝ) := by exact_mod_cast hus
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (s : ℝ) (u : ℝ)) :
      ‖transposeEndpoint Q i Pdag β t.toNNReal‖ ≤
        E * ‖transposeEndpoint Q i Pdag β s‖ := by
    have hst : s ≤ t.toNNReal := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal ht.1
    have hts : t.toNNReal ≤ 2 * s := by
      have hh : t ≤ (2 * s : ℝ≥0) := ht.2.trans hus'
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hh
    exact c2_transpose_endpoint_propagation_window hP hPd β s t.toNNReal hs hst hts hz
  have hnorm := norm_setIntegral_le_of_norm_le_const
    (f := fun t : ℝ => transposeEndpoint Q i Pdag β t.toNNReal)
    (C := E * ‖transposeEndpoint Q i Pdag β s‖)
    (isCompact_Icc.measure_lt_top (μ := volume)) hbound
  rw [Real.volume_real_Icc_of_le hsu'] at hnorm
  have hint : ‖∫ t in Set.Icc (s : ℝ) (u : ℝ),
      transposeEndpoint Q i Pdag β t.toNNReal‖ ≤
        (E * ‖transposeEndpoint Q i Pdag β s‖) * (s : ℝ) := by
    exact hnorm.trans (mul_le_mul_of_nonneg_left (by linarith only [hus'])
      (by dsimp only [E]; positivity))
  dsimp only
  rw [← dyadic_transpose_primitive_const_increment hβ hP hPd s u hsu, norm_smul, norm_mul]
  calc
    _ ≤ ‖(-2 : ℂ)‖ * ‖ζ‖ *
        ((E * ‖transposeEndpoint Q i Pdag β s‖) * (s : ℝ)) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by dsimp only [E]; norm_num; ring

/-- An endpoint decay estimate yields the corresponding density increment rate
through the force-weighted primitive identity. -/
theorem c2_dyadic_density_increment_of_endpoint_decay
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) (s u : ℝ≥0)
    (hs : 0 < (s : ℝ)) (hsu : s ≤ u) (hus : u ≤ 2 * s)
    (hz : ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2) (A : ℝ) (hA : 0 ≤ A)
    (hend : ‖transposeEndpoint Q i Pdag β s‖ ≤
      A * (s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4))) :
    let := reducedLaw_probability Q
    ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) - Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ ≤
      4 * Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
        ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2) *
        A * (s : ℝ) ^ (-(d : ℝ) / 4) := by
  let E := Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
    ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2)
  have hforce : ‖ζ‖ * Real.sqrt (s : ℝ) ≤ 2 := by
    calc
      _ ≤ ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [s.coe_nonneg])) (norm_nonneg _)
      _ ≤ 2 := hz
  have hscale : (s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) * (s : ℝ) =
      Real.sqrt (s : ℝ) * (s : ℝ) ^ (-(d : ℝ) / 4) := by
    calc
      _ = (s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) * (s : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = (s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4) + 1) := (Real.rpow_add hs _ _).symm
      _ = (s : ℝ) ^ ((1 / 2 : ℝ) + (-(d : ℝ) / 4)) := by congr 1; ring
      _ = _ := by rw [Real.sqrt_eq_rpow, Real.rpow_add hs]
  have hb := c2_density_increment_bound_by_initial_endpoint hβ hP hPd s u hs hsu hus hz
  dsimp only at hb ⊢
  calc
    _ ≤ 2 * ‖ζ‖ * (s : ℝ) * (E * ‖transposeEndpoint Q i Pdag β s‖) := hb
    _ ≤ 2 * ‖ζ‖ * (s : ℝ) * (E * (A * (s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hend (Real.exp_pos _).le) (by positivity)
    _ = (2 * E * A) * (‖ζ‖ * Real.sqrt (s : ℝ)) * (s : ℝ) ^ (-(d : ℝ) / 4) := by
      calc
        _ = (2 * E * A * ‖ζ‖) * ((s : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) * (s : ℝ)) := by ring
        _ = _ := by rw [hscale]; ring
    _ ≤ 4 * E * A * (s : ℝ) ^ (-(d : ℝ) / 4) := by
      have hh := mul_le_mul_of_nonneg_left hforce (show 0 ≤ 2 * E * A by positivity)
      have hp := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hs.le (-(d : ℝ) / 4))
      nlinarith only [hp]


end EinsteinFull.Blueprint
