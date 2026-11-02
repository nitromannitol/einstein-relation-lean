import EinsteinFull.Calculus.SbxBLocalizedCutoffDefectR07

open EinsteinRelation EinsteinFull.External.Source.GMP MeasureTheory SubdiffusiveProcess Filter Set
open scoped ENNReal NNReal Topology
open EinsteinFull.Blueprint.TubeProbability

namespace EinsteinFull.Calculus

/-- Optimizing a family of Young estimates, including vanishing energies. -/
private theorem br12_young_optimize (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (h : ∀ a : ℝ, 0 < a → z ≤ a ^ 2 * x + a⁻¹ ^ 2 * y) :
    z ^ 2 ≤ 4 * x * y := by
  by_cases hz0 : z = 0
  · simpa only [hz0, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hx) hy)
  have hzp : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  by_cases hy0 : y = 0
  · subst y
    let a := Real.sqrt (z / (2 * (x + 1)))
    have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
    have ha2 : a ^ 2 = z / (2 * (x + 1)) := Real.sq_sqrt (by positivity)
    have hb := h a ha
    simp only [mul_zero, add_zero] at hb
    rw [ha2] at hb
    have hd : 0 < 2 * (x + 1) := by positivity
    have he : z / (2 * (x + 1)) * x = (z * x) / (2 * (x + 1)) := by ring
    rw [he] at hb
    have hb' := (le_div_iff₀ hd).mp hb
    nlinarith
  · have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
    let a := Real.sqrt (2 * y / z)
    have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
    have ha2 : a ^ 2 = 2 * y / z := Real.sq_sqrt (by positivity)
    have hainv : a⁻¹ ^ 2 = (2 * y / z)⁻¹ := by rw [inv_pow, ha2]
    have hb := h a ha
    rw [ha2, hainv] at hb
    have he : (2 * y / z) * x + (2 * y / z)⁻¹ * y =
        (2 * x * y) / z + z / 2 := by field_simp
    rw [he] at hb
    have hb' := mul_le_mul_of_nonneg_right hb hzp.le
    field_simp at hb'
    nlinarith

/-- The pointwise Young inequality for the native forcing integrates from zero. -/
theorem br12_integrated_native_force_young {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) (A B : Set (Vec d))
    (hA : MeasurableSet A) (hB : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hv : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      x ∉ A → ∀ i : Fin d, v.val (some i) x = 0)
    (T : ℝ) (hT : 0 < T) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      κ * (∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t) ≤
        Real.exp (-(δ ^ 2) / (8 * (4 * κ⁻¹ ^ 2) * T)) * ‖f‖ ^ 2 ∧
      ∀ a : ℝ, 0 < a →
        |inner ℝ (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) T.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) -
        inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v)| ≤
        κ⁻¹ * (a ^ 2 * (∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t) +
          a⁻¹ ^ 2 * T * (∫ x in A, euclideanSq (fun i => v.val (some i) x)
            ∂(volume.restrict (sourceBall (0 : Vec d) R)))) := by
  obtain ⟨Q, hQc, hQ, hQd, hGi, hG⟩ :=
    br07_supplied_spectral_separated_gradient_bound hd hκ h R hR s A B hA hB δ hδ hsep f hf T hT
  obtain ⟨Q', hQ'c, hQ', hpair⟩ := br07_supplied_spectral_weak_pairing_zero hd hκ h R hR s
  have hsame : Q' = Q := by
    funext t ht
    apply ContinuousLinearMap.ext
    intro g
    apply injective_dirichletHilbertInclusion hκ h R hR
    exact congrArg (fun L => L g) ((hQ' t ht).trans (hQ t ht).symm)
  subst Q'
  refine ⟨Q, hQ, hG, ?_⟩
  intro a ha
  obtain ⟨hfi, hpair⟩ := hpair f v T hT
  let G := br07_native_restricted_gradient R hR A Q f
  let E := ∫ x in A, euclideanSq (fun i => v.val (some i) x)
    ∂(volume.restrict (sourceBall (0 : Vec d) R))
  let F := br07_native_test_force (α := α) R hR Q f v
  have hGi' : IntegrableOn G (Set.Ioc 0 T) := hGi
  have hfi' : IntegrableOn F (Set.Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT.le).1 hfi
  have hmajor : IntegrableOn (fun t => κ⁻¹ * (a ^ 2 * G t + a⁻¹ ^ 2 * E)) (Set.Ioc 0 T) :=
    ((hGi'.const_mul (a ^ 2)).add (integrableOn_const (measure_Ioc_lt_top.ne))).const_mul κ⁻¹
  have hpoint : ∀ᵐ t ∂volume.restrict (Set.Ioc 0 T),
      |F t| ≤ κ⁻¹ * (a ^ 2 * G t + a⁻¹ ^ 2 * E) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact br07_native_test_force_restricted_bound hd hκ h R hR A hA Q f v hv a ha t ht.1
  have hmono := integral_mono_ae hfi'.norm hmajor hpoint
  have hnorm := norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc 0 T)) F
  rw [intervalIntegral.integral_of_le hT.le] at hpair
  rw [hpair, abs_neg]
  calc
    |∫ t in Set.Ioc 0 T, F t| ≤ ∫ t in Set.Ioc 0 T, |F t| := by
      simpa only [Real.norm_eq_abs] using hnorm
    _ ≤ ∫ t in Set.Ioc 0 T, κ⁻¹ * (a ^ 2 * G t + a⁻¹ ^ 2 * E) := hmono
    _ = κ⁻¹ * (a ^ 2 * (∫ t in 0..T, G t) + a⁻¹ ^ 2 * T * E) := by
      rw [integral_const_mul, integral_add (hGi'.const_mul _) (integrableOn_const (measure_Ioc_lt_top.ne)),
        integral_const_mul, integral_const, intervalIntegral.integral_of_le hT.le]
      rw [measureReal_restrict_apply_univ, Real.volume_real_Ioc_of_le hT.le]
      simp only [sub_zero, smul_eq_mul]
      ring

/-- The optimized integrated native weak-forcing estimate, with the
separated initial-data gradient estimate for the same spectral lift. -/
theorem br12_integrated_annular_force_squared {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) (A B : Set (Vec d))
    (hA : MeasurableSet A) (hB : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hv : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      x ∉ A → ∀ i : Fin d, v.val (some i) x = 0)
    (T : ℝ) (hT : 0 < T) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      κ * (∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t) ≤
        Real.exp (-(δ ^ 2) / (8 * (4 * κ⁻¹ ^ 2) * T)) * ‖f‖ ^ 2 ∧
      |inner ℝ (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) T.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) -
        inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v)| ^ 2 ≤
        4 * κ⁻¹ ^ 2 * T * (∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t) *
          (∫ x in A, euclideanSq (fun i => v.val (some i) x)
            ∂(volume.restrict (sourceBall (0 : Vec d) R))) := by
  obtain ⟨Q, hQ, hgrad, hyoung⟩ :=
    br12_integrated_native_force_young hd hκ h R hR s A B hA hB δ hδ hsep f hf v hv T hT
  refine ⟨Q, hQ, hgrad, ?_⟩
  let X := ∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t
  let E := ∫ x in A, euclideanSq (fun i => v.val (some i) x)
    ∂(volume.restrict (sourceBall (0 : Vec d) R))
  let D := inner ℝ (SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) T.toNNReal f)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) -
    inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v)
  have hsq : ∀ w : Vec d, 0 ≤ euclideanSq w := by
    intro w
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hX : 0 ≤ X := by
    apply intervalIntegral.integral_nonneg_of_forall hT.le
    intro t
    unfold br07_native_restricted_gradient
    split
    · exact integral_nonneg fun x => hsq _
    · exact le_refl _
  have hE : 0 ≤ E := integral_nonneg fun x => hsq _
  have hh : ∀ a : ℝ, 0 < a → κ * |D| ≤ a ^ 2 * X + a⁻¹ ^ 2 * (T * E) := by
    intro a ha
    have hb := mul_le_mul_of_nonneg_left (hyoung a ha) hκ.le
    have hk : κ * κ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hκ)
    dsimp only [D, X, E] at ⊢
    calc
      _ ≤ κ * (κ⁻¹ * (a ^ 2 * (∫ t in 0..T, br07_native_restricted_gradient R hR A Q f t) +
          a⁻¹ ^ 2 * T * (∫ x in A, euclideanSq (fun i => v.val (some i) x)
            ∂(volume.restrict (sourceBall (0 : Vec d) R))))) := hb
      _ = _ := by rw [← mul_assoc, hk, one_mul]; ring
  have ho := br12_young_optimize X (T * E) (κ * |D|) hX (mul_nonneg hT.le hE)
    (mul_nonneg hκ.le (abs_nonneg D)) hh
  have ho' := mul_le_mul_of_nonneg_left ho (sq_nonneg κ⁻¹)
  have hc : κ⁻¹ ^ 2 * (κ * |D|) ^ 2 = |D| ^ 2 := by
    field_simp [ne_of_gt hκ]
  rw [hc] at ho'
  change |D| ^ 2 ≤ 4 * κ⁻¹ ^ 2 * T * X * E
  calc
    _ ≤ κ⁻¹ ^ 2 * (4 * X * (T * E)) := ho'
    _ = _ := by ring

#print axioms br12_integrated_annular_force_squared
#print axioms br12_integrated_native_force_young

end EinsteinFull.Calculus
