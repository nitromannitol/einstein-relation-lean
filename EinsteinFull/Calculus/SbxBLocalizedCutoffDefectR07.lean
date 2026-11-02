import EinsteinFull.Calculus.C12TubeWeightedDaviesGaffney

open EinsteinRelation EinsteinFull.External.Source.GMP MeasureTheory SubdiffusiveProcess Filter Set
open scoped ENNReal NNReal Topology
open EinsteinFull.Blueprint.TubeProbability

namespace EinsteinFull.Calculus

/-- The double-weight Dirichlet form retains half of its gradient coercivity
at the cost of a quadratic logarithmic-gradient term. -/
theorem br07_double_weight_form_coercive {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hκ : 0 < κ) (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) (u m : ℝ) :
    (κ / 2) * m ^ 2 * euclideanSq p -
        (2 * κ⁻¹ * euclideanSq q) * (m * u) ^ 2 ≤
      dot ((α x).mulVec p) (m ^ 2 • (p + (2 * u) • q)) := by
  have hcost := c12_davies_double_weight_form_bound hκ h x p q (2 * u) m
  have hp : κ * euclideanSq p ≤ dot ((α x).mulVec p) p := by
    have he := ((h.2.2 x).2.2.2 p).1
    change κ * euclideanSq p ≤ p ⬝ᵥ (α x).mulVec p at he
    change κ * euclideanSq p ≤ ((α x).mulVec p) ⬝ᵥ p
    rwa [dotProduct_comm]
  have hscale := mul_le_mul_of_nonneg_left hp (sq_nonneg m)
  change -(κ⁻¹ * euclideanSq q) * (m * (2 * u)) ^ 2 ≤
    ((α x).mulVec p) ⬝ᵥ (m ^ 2 • (p + (2 * (2 * u)) • q)) at hcost
  change (κ / 2) * m ^ 2 * euclideanSq p -
      (2 * κ⁻¹ * euclideanSq q) * (m * u) ^ 2 ≤
    ((α x).mulVec p) ⬝ᵥ (m ^ 2 • (p + (2 * u) • q))
  simp only [dotProduct_smul, dotProduct_add, smul_eq_mul] at hcost ⊢
  change m ^ 2 * (κ * euclideanSq p) ≤
    m ^ 2 * (((α x).mulVec p) ⬝ᵥ p) at hscale
  nlinarith

/-- Density ellipticity controls the cost of the logarithmic-gradient term. -/
theorem br07_double_weight_form_coercive_density {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hκ : 0 < κ) (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) (u m L : ℝ) (hq : euclideanSq q ≤ L ^ 2) :
    (κ / 2) * m ^ 2 * euclideanSq p -
        (2 * κ⁻¹ ^ 2 * L ^ 2) * ρ x * (m * u) ^ 2 ≤
      dot ((α x).mulVec p) (m ^ 2 • (p + (2 * u) • q)) := by
  have hk : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hρ : 1 ≤ κ⁻¹ * ρ x := by
    have hh := mul_le_mul_of_nonneg_left (h.2.2 x).1 hk
    simpa only [inv_mul_cancel₀ (ne_of_gt hκ)] using hh
  have hphase : κ⁻¹ * euclideanSq q ≤ κ⁻¹ * L ^ 2 :=
    mul_le_mul_of_nonneg_left hq hk
  have hcost : κ⁻¹ * euclideanSq q ≤ (κ⁻¹ * L ^ 2) * (κ⁻¹ * ρ x) :=
    hphase.trans (le_mul_of_one_le_right (mul_nonneg hk (sq_nonneg L)) hρ)
  have hscaled := mul_le_mul_of_nonneg_right hcost (sq_nonneg (m * u))
  have hform := br07_double_weight_form_coercive hκ h x p q u m
  nlinarith

/-- Smooth exponential weights preserve integrability of the squared native
gradient on the source ball. -/
theorem br07_weighted_native_gradient_integrable {d : ℕ}
    (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ)
    (u : DirichletHilbertSpace (d := d) R hR) :
    Integrable (fun x => Real.exp ((2 * lam) * φ x) *
      euclideanSq (fun i => u.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hg : Integrable (fun x => euclideanSq (fun i => u.val (some i) x))
      (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    simpa only [euclideanSq, dot, dotProduct, ← pow_two] using
      (integrable_finsetSum Finset.univ (fun i _ => (Lp.memLp (u.val (some i))).integrable_sq))
  have hle : volume.restrict (sourceBall (0 : Vec d) R) ≤
      volume.restrict (Q : Set (SpatialCoordinates d)) :=
    Measure.restrict_mono_set volume (sourceBall_subset_cube R hR)
  have hgball := hg.mono_measure hle
  let m : Vec d → ℝ := fun x => Real.exp ((2 * lam) * φ x)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := (contDiff_const.mul hφ).exp
  obtain ⟨C, _, hb, _⟩ := c12_smooth_weight_cube_bounds R hR m hm
  have hmtop : MemLp m ∞ (volume.restrict (sourceBall (0 : Vec d) R)) := by
    apply memLp_top_of_bound hm.continuous.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
    simpa only [Real.norm_eq_abs] using hb x (sourceBall_subset_cube R hR hx)
  have hh := hgball.mul_of_top_left hmtop
  change Integrable (fun x => euclideanSq (fun i => u.val (some i) x) * m x)
    (volume.restrict (sourceBall (0 : Vec d) R)) at hh
  simpa only [m, mul_comm] using hh

/-- The native double-weight test controls both the weighted gradient and
the cost of the exponential weight. -/
theorem br07_native_double_weight_form_coercive {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ v w : DirichletHilbertSpace (d := d) R hR,
      ((dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] (fun x => Real.exp (lam * φ x) * u.val none x)) ∧
      (∀ i, (w.val (some i) : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        fun x => Real.exp ((2 * lam) * φ x) * u.val (some i) x +
          (Real.exp ((2 * lam) * φ x) * ((2 * lam) * fderiv ℝ φ x (Pi.single i 1))) * u.val none x) ∧
      (κ / 2) * (∫ x in sourceBall (0 : Vec d) R,
        Real.exp ((2 * lam) * φ x) * euclideanSq (fun i => u.val (some i) x)) -
        (2 * κ⁻¹ ^ 2 * L ^ 2) * ‖dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) v‖ ^ 2 ≤
        ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x) := by
  obtain ⟨M, hM0, _, hMdir⟩ :=
    c12_exponential_multiplier_preserves_dirichlet R hR φ hφ lam
  obtain ⟨N, _, hN1, hNdir⟩ :=
    c12_exponential_multiplier_preserves_dirichlet R hR φ hφ (2 * lam)
  let v : DirichletHilbertSpace (d := d) R hR := ⟨M u.val, hMdir u⟩
  let w : DirichletHilbertSpace (d := d) R hR := ⟨N u.val, hNdir u⟩
  have hle := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono_set volume (sourceBall_subset_cube (d := d) R hR))).ae_le
  have hv := (hM0 u.val).filter_mono hle
  have hw := (ae_all_iff.mpr fun i : Fin d => (hN1 u.val i).filter_mono hle)
  have hgrad := br07_weighted_native_gradient_integrable R hR φ hφ lam u
  have hcost := c12_dirichlet_value_square_integrable hκ h R hR v
  have hform := c12_dirichlet_gradient_form_integrable hκ h R hR u w
  have hpoint : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      (κ / 2) * (Real.exp ((2 * lam) * φ x) *
        euclideanSq (fun i => u.val (some i) x)) -
        (2 * κ⁻¹ ^ 2 * L ^ 2) * (ρ x * (v.val none x) ^ 2) ≤
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x) := by
    filter_upwards [hv, hw, hq] with x hvx hwx hqx
    have he : (fun i => w.val (some i) x) =
        (Real.exp (lam * φ x)) ^ 2 •
          ((fun i => u.val (some i) x) +
            (2 * u.val none x) • (fun i => lam * fderiv ℝ φ x (Pi.single i 1))) := by
      ext i
      change (N u.val (some i)) x = _
      rw [hwx i]
      rw [show (2 * lam) * φ x = lam * φ x + lam * φ x by ring, Real.exp_add]
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [he]
    have hb := br07_double_weight_form_coercive_density hκ h x
      (fun i => u.val (some i) x)
      (fun i => lam * fderiv ℝ φ x (Pi.single i 1))
      (u.val none x) (Real.exp (lam * φ x)) L hqx
    change (M u.val none) x = _ at hvx
    rw [hvx]
    rw [show (2 * lam) * φ x = lam * φ x + lam * φ x by ring, Real.exp_add]
    convert hb using 1 <;> ring
  have hint := integral_mono_ae ((hgrad.const_mul _).sub (hcost.const_mul _)) hform hpoint
  simp only [Pi.sub_apply] at hint
  rw [integral_sub (hgrad.const_mul _) (hcost.const_mul _), integral_const_mul,
    integral_const_mul] at hint
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hJ := dirichletHilbertInclusion_coe ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) v
  have hsq : ‖J v‖ ^ 2 = ∫ x in sourceBall (0 : Vec d) R, ρ x * (v.val none x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    rw [DimensionLift.dirichletVolume_inner_eq_native hκ h R (J v) (J v)
      (fun x => v.val none x) (fun x => v.val none x) hJ hJ]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  refine ⟨v, w, ?_, ?_, ?_⟩
  · have hac := (Measure.absolutelyContinuous_of_le_smul
      (dirichletVolume_le_cube ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1))).ae_le
    exact hJ.trans ((hM0 u.val).filter_mono hac)
  · intro i
    exact (hN1 u.val i).filter_mono hle
  · simpa only [← hsq] using hint

/-- The supplied spectral heat flow dissipates weighted native gradient
energy, up to the quadratic cost of the phase. -/
theorem br07_supplied_spectral_heat_weighted_gradient_derivative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R))
      (Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t),
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R))
        (v : DirichletHilbertSpace (d := d) R hR),
        HasDerivAt (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ)) ∧
      ∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ∃ e : ℝ, HasDerivAt (fun r : ℝ => ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)‖ ^ 2) e (t : ℝ) ∧
        e + κ * (∫ x in sourceBall (0 : Vec d) R,
          Real.exp ((2 * lam) * φ x) *
            euclideanSq (fun i => (Q t ht f).val (some i) x)) ≤
        (4 * κ⁻¹ ^ 2 * L ^ 2) * ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f)‖ ^ 2 := by
  classical
  choose u hu hv using fun n =>
    c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR h s n
  have hb : ∀ n, EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    intro n
    rw [show EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      (s.square_integrable n).toLp (s.eigenfunction n) from
        congrFun (HilbertBasis.coe_mk s.orthonormal
          (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  obtain ⟨M, T, hdir, Q, _, hM1, hT, hQ, hderiv⟩ :=
    c12_spectral_heat_weighted_energy_derivative hd hκ h R hR s u hb hv φ hφ lam
  obtain ⟨Q₀, hQc, hQ₀⟩ :=
    EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectral_heat_native_weakFlow
      hd hκ h R hR s u hb hv
  have hQeq (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
      Q t ht f = Q₀ t ht f := by
    apply injective_dirichletHilbertInclusion hκ h R hR
    exact congrArg (fun F : _ →L[ℝ] _ => F f) ((hQ t ht).trans (hQ₀ t ht).1.symm)
  refine ⟨T, Q, hT, ?_, hQ, ?_, ?_⟩
  · intro f
    have heq : (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f) =
        (fun t : {t : ℝ≥0 // 0 < t} => Q₀ t.val t.property f) := by
      funext t
      exact hQeq t.val t.property f
    rw [heq]
    exact hQc f
  · intro t ht f v
    rw [hQeq t ht f]
    exact (hQ₀ t ht).2.2 f v
  intro t ht f
  let z := Q t ht f
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨v, w, hvw, hw, hbound⟩ :=
    br07_native_double_weight_form_coercive hκ h R hR φ hφ lam L hq z
  have hJz := dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) z
  have hvT : J v = T (J z) := by
    apply Lp.ext
    filter_upwards [hvw, hT (J z), hJz] with x hvx htx hzx
    change (J v) x = _ at hvx
    change (J z) x = (z.val none) x at hzx
    rw [hvx, htx, hzx]
  have hle := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_mono_set volume (sourceBall_subset_cube (d := d) R hR))).ae_le
  have hforms : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => z.val (some i) x)) (fun i => w.val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => z.val (some i) x)) (fun i => (M z.val) (some i) x) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hw,
      ae_all_iff.mpr (fun i : Fin d => (hM1 z.val i).filter_mono hle)] with x hwx hmx
    congr 1
    ext i
    exact (hwx i).trans (hmx i).symm
  have hfactor : J z = SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t f := by
    exact congrArg (fun F : _ →L[ℝ] _ => F f) (hQ t ht)
  rw [hvT, hfactor, hforms] at hbound
  refine ⟨_, hderiv t ht f, ?_⟩
  linarith

/-- Integrating a differential energy inequality retains the gradient term.
The explicit integrability hypothesis is a separate analytic prerequisite. -/
theorem br07_integrate_energy_dissipation
    (E G : ℝ → ℝ) (a b c κ : ℝ) (hab : a ≤ b)
    (hE : ContinuousOn E (Set.Icc a b))
    (hG : IntegrableOn G (Set.Icc a b))
    (hderiv : ∀ t ∈ Set.Ioo a b, ∃ e, HasDerivAt E e t ∧
      e + κ * G t ≤ c * E t) :
    κ * (∫ t in a..b, G t) ≤
      E a - E b + c * (∫ t in a..b, E t) := by
  classical
  let D : ℝ → ℝ := fun t => deriv E t
  have hD (t : ℝ) (ht : t ∈ Set.Ioo a b) :
      HasDerivWithinAt E (D t) (Set.Ioi t) t ∧
        D t ≤ c * E t - κ * G t := by
    obtain ⟨e, he, hb⟩ := hderiv t ht
    have hde : D t = e := he.deriv
    exact ⟨hde ▸ he.hasDerivWithinAt, by rw [hde]; linarith⟩
  have hi : IntegrableOn (fun t => c * E t - κ * G t) (Set.Icc a b) :=
    (hE.integrableOn_Icc.const_mul c).sub (hG.const_mul κ)
  have hh := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hab hE
    (fun t ht => (hD t ht).1) hi (fun t ht => (hD t ht).2)
  have hEi : IntervalIntegrable E volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hE.integrableOn_Icc
  have hGi := (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hG
  rw [intervalIntegral.integral_sub (hEi.const_mul c) (hGi.const_mul κ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hh
  linarith

/-- A smooth exponential weight defines a continuous quadratic form on the
native value-gradient carrier. -/
theorem br07_weighted_gradient_continuous_form {d : ℕ}
    (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ B : DirichletHilbertSpace (d := d) R hR →L[ℝ]
        DirichletHilbertSpace (d := d) R hR →L[ℝ] ℝ,
      ∀ u, B u u = ∫ x in sourceBall (0 : Vec d) R,
        Real.exp ((2 * lam) * φ x) * euclideanSq (fun i => u.val (some i) x) := by
  classical
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let m : Vec d → ℝ := fun x => Real.exp ((2 * lam) * φ x)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := (contDiff_const.mul hφ).exp
  obtain ⟨C, hC, hb, _⟩ := c12_smooth_weight_cube_bounds R hR m hm
  let a : Vec d → Option (Fin d) → Option (Fin d) → ℝ := fun x i j =>
    if i = j ∧ i ≠ none then m x else 0
  have ha (i j : Option (Fin d)) : AEStronglyMeasurable (fun x => a x i j) μ := by
    dsimp only [a]
    split_ifs
    · exact hm.continuous.aestronglyMeasurable
    · exact aestronglyMeasurable_const
  have hbound : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ C := by
    filter_upwards [ae_restrict_mem Q.isOpen.measurableSet] with x hx i j
    dsimp only [a]
    split_ifs
    · exact hb x hx
    · simpa only [abs_zero] using hC
  obtain ⟨D, hD⟩ := exists_coordinateL2Form μ a ha hC hbound
  let S := (dirichletHilbertSubmodule (d := d) R hR).subtypeL
  let B := D.bilinearComp S S
  refine ⟨B, ?_⟩
  intro u
  change D u.val u.val = _
  rw [hD]
  have hpoint (x : Vec d) :
      (∑ i, ∑ j, a x i j * u.val j x * u.val i x) =
        m x * euclideanSq (fun i => u.val (some i) x) := by
    simp only [a, Fintype.sum_option, ne_eq, not_true_eq_false, and_false,
      ↓reduceIte, zero_mul, Finset.sum_const_zero, zero_add, Option.some_ne_none,
      not_false_eq_true, and_true, Option.some.injEq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, euclideanSq, dot, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [hpoint]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero Q.isOpen.measurableSet.nullMeasurableSet
    (sourceBall_subset_cube R hR)
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ∀ i : Fin d, x ∉ sourceBall (0 : Vec d) R → u.val (some i) x = 0 :=
    ae_all_iff.mpr (fun i => dirichletHilbert_coordinate_zero_exterior R hR u (some i))
  filter_upwards [ae_imp_of_ae_restrict hz] with x hx hxs
  have he : (fun i => u.val (some i) x) = 0 := funext (fun i => hx hxs.1 i hxs.2)
  rw [he]
  simp [euclideanSq, dot]

/-- The weighted gradient of the native lift, extended by zero at nonpositive times. -/
@[nolint defsWithUnderscore]
noncomputable def br07_native_weighted_gradient {d : ℕ} {ρ : Vec d → ℝ}
    (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ) (lam : ℝ)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    ∫ x in sourceBall (0 : Vec d) R, Real.exp ((2 * lam) * φ x) *
      euclideanSq (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x)
  else 0

/-- Continuity of the native lift gives integrability of its literal weighted
gradient on every compact interval separated from zero. -/
theorem br07_native_weighted_gradient_integrableOn {d : ℕ} {ρ : Vec d → ℝ}
    (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (hQ : ∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (br07_native_weighted_gradient R hR φ lam Q f) (Set.Icc a b) := by
  obtain ⟨B, hB⟩ := br07_weighted_gradient_continuous_form R hR φ hφ lam
  let V : Set.Icc a b → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q t.val.toNNReal (Real.toNNReal_pos.mpr (ha.trans_le t.property.1)) f
  let W : Set.Icc a b → {t : ℝ≥0 // 0 < t} := fun t =>
    ⟨t.val.toNNReal, Real.toNNReal_pos.mpr (ha.trans_le t.property.1)⟩
  have hW : Continuous W :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  have hV : Continuous V := by
    simpa only [V, W, Function.comp_def] using (hQ f).comp hW
  have hC : Continuous (fun t : Set.Icc a b => B (V t) (V t)) :=
    (B.continuous.comp hV).clm_apply hV
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_iff_continuous_restrict.mpr
  have heq : (fun t : Set.Icc a b => br07_native_weighted_gradient R hR φ lam Q f t.val) =
      (fun t : Set.Icc a b => B (V t) (V t)) := by
    funext t
    have ht : 0 < t.val := ha.trans_le t.property.1
    rw [hB]
    simp only [br07_native_weighted_gradient, dif_pos ht, V]
  change Continuous (fun t : Set.Icc a b =>
    br07_native_weighted_gradient R hR φ lam Q f t.val)
  rw [heq]
  exact hC

/-- A nonnegative time density with uniformly bounded positive-time integrals
is integrable up to the zero endpoint. -/
theorem br07_integrableOn_Ioc_zero_of_uniform_bound
    (G : ℝ → ℝ) (b M : ℝ) (hb : 0 < b)
    (hG : ∀ a, 0 < a → IntegrableOn G (Set.Icc a b))
    (hpos : ∀ t, 0 < t → 0 ≤ G t)
    (hbound : ∀ a, 0 < a → a ≤ b → (∫ t in a..b, G t) ≤ M) :
    IntegrableOn G (Set.Ioc 0 b) := by
  let a : ℕ → ℝ := fun n => b * (((n : ℝ) + 1)⁻¹)
  have ha (n : ℕ) : 0 < a n := by
    dsimp [a]
    positivity
  have hab (n : ℕ) : a n ≤ b := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (by positivity)).2 hn
    nlinarith
  have hat : Filter.Tendsto a Filter.atTop (nhds 0) := by
    simpa only [a, mul_zero, one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul b
  apply integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
    (I := M) (a := a) (l := Filter.atTop)
  · intro n
    exact (hG (a n) (ha n)).mono_set Set.Ioc_subset_Icc_self
  · exact hat
  · apply Filter.Eventually.of_forall
    intro n
    have heq : (∫ t in Set.Ioc (a n) b, ‖G t‖) =
        ∫ t in Set.Ioc (a n) b, G t := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact Real.norm_of_nonneg (hpos t ((ha n).trans ht.1))
    rw [heq, ← intervalIntegral.integral_of_le (hab n)]
    exact hbound (a n) (ha n) (hab n)

/-- Positive-time dissipation and a continuous nonnegative energy give
integrability of the dissipation up to time zero. -/
theorem br07_dissipation_integrableOn_zero
    (E G : ℝ → ℝ) (b c κ : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (hκ : 0 < κ)
    (hE : Continuous E) (hEpos : ∀ t, 0 ≤ E t)
    (hG : ∀ a, 0 < a → IntegrableOn G (Set.Icc a b))
    (hGpos : ∀ t, 0 < t → 0 ≤ G t)
    (henergy : ∀ a, 0 < a → a ≤ b → κ * (∫ t in a..b, G t) ≤
      E a - E b + c * (∫ t in a..b, E t)) :
    IntegrableOn G (Set.Ioc 0 b) := by
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) b)).bddAbove_image
    hE.continuousOn
  let B := max B₀ 0
  have hB : 0 ≤ B := le_max_right _ _
  have hEB (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b) : E t ≤ B :=
    (hB₀ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  apply br07_integrableOn_Ioc_zero_of_uniform_bound G b ((B + c * b * B) / κ) hb hG hGpos
  intro a ha hab
  have hEint : IntervalIntegrable E volume a b := hE.intervalIntegrable a b
  have hi : (∫ t in a..b, E t) ≤ b * B := by
    have hi' := intervalIntegral.integral_mono_on hab hEint
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => B) volume a b)
      (fun t ht => hEB t ⟨ha.le.trans ht.1, ht.2⟩)
    rw [intervalIntegral.integral_const] at hi'
    simp only [smul_eq_mul] at hi'
    nlinarith [mul_nonneg ha.le hB]
  have hea := hEB a ⟨ha.le, hab⟩
  have heb := hEpos b
  have he := henergy a ha hab
  apply (le_div_iff₀ hκ).2
  nlinarith [mul_le_mul_of_nonneg_left hi hc]

/-- The supplied spectral flow's differential estimate integrates on every
positive interval, using continuity of its native lift. -/
theorem br07_supplied_spectral_heat_gradient_integral {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R))
      (Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t),
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R))
        (v : DirichletHilbertSpace (d := d) R hR),
        HasDerivAt (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ)) ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (a b : ℝ), 0 < a → a ≤ b →
        κ * (∫ t in a..b, br07_native_weighted_gradient R hR φ lam Q f t) ≤
          ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) a.toNNReal f)‖ ^ 2 -
          ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) b.toNNReal f)‖ ^ 2 +
          (4 * κ⁻¹ ^ 2 * L ^ 2) * (∫ t in a..b, ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)‖ ^ 2) := by
  obtain ⟨T, Q, hT, hQc, hQ, hweak, hderiv⟩ :=
    br07_supplied_spectral_heat_weighted_gradient_derivative hd hκ h R hR s φ hφ lam L hq
  refine ⟨T, Q, hT, hQc, hQ, hweak, ?_⟩
  intro f a b ha hab
  have hG := br07_native_weighted_gradient_integrableOn R hR φ hφ lam Q hQc f a b ha
  let E : ℝ → ℝ := fun t => ‖T (SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)‖ ^ 2
  have hE : Continuous E :=
    ((T.continuous.comp ((SpectralHeat.heatOperator_continuous
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal)).norm).pow 2
  apply br07_integrate_energy_dissipation E
    (br07_native_weighted_gradient R hR φ lam Q f) a b (4 * κ⁻¹ ^ 2 * L ^ 2) κ hab
    hE.continuousOn hG
  intro t ht
  have ht0 : 0 < t := ha.trans ht.1
  obtain ⟨e, he, hb⟩ := hderiv t.toNNReal (Real.toNNReal_pos.mpr ht0) f
  rw [Real.toNNReal_of_nonneg ht0.le] at he
  refine ⟨e, he, ?_⟩
  simpa only [E, br07_native_weighted_gradient, dif_pos ht0] using hb

/-- The supplied native spectral flow has integrable weighted gradient all
the way to zero time, with the same multiplier and native lift. -/
theorem br07_supplied_spectral_heat_gradient_integrable_zero {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R))
      (Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t),
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R))
        (v : DirichletHilbertSpace (d := d) R hR),
        HasDerivAt (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ)) ∧
      (∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (a b : ℝ), 0 < a → a ≤ b →
        κ * (∫ t in a..b, br07_native_weighted_gradient R hR φ lam Q f t) ≤
          ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) a.toNNReal f)‖ ^ 2 -
          ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) b.toNNReal f)‖ ^ 2 +
          (4 * κ⁻¹ ^ 2 * L ^ 2) * (∫ t in a..b, ‖T (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)‖ ^ 2)) ∧
      (∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (b : ℝ), 0 < b →
        IntegrableOn (br07_native_weighted_gradient R hR φ lam Q f) (Set.Ioc 0 b)) := by
  obtain ⟨T, Q, hT, hQc, hQ, hweak, henergy⟩ :=
    br07_supplied_spectral_heat_gradient_integral hd hκ h R hR s φ hφ lam L hq
  refine ⟨T, Q, hT, hQc, hQ, hweak, henergy, ?_⟩
  intro f b hb
  let E : ℝ → ℝ := fun t => ‖T (SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)‖ ^ 2
  have hE : Continuous E :=
    ((T.continuous.comp ((SpectralHeat.heatOperator_continuous
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal)).norm).pow 2
  apply br07_dissipation_integrableOn_zero E
    (br07_native_weighted_gradient R hR φ lam Q f) b (4 * κ⁻¹ ^ 2 * L ^ 2) κ
    hb (by positivity) hκ hE (fun t => sq_nonneg _) ?_ ?_ ?_
  · intro a ha
    exact br07_native_weighted_gradient_integrableOn R hR φ hφ lam Q hQc f a b ha
  · intro t ht
    rw [br07_native_weighted_gradient, dif_pos ht]
    apply integral_nonneg
    intro x
    apply mul_nonneg (Real.exp_pos _).le
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  · intro a ha hab
    exact henergy f a b ha hab

private theorem br07_dissipation_inequality_zero (E G : ℝ → ℝ) (b c κ : ℝ) (hb : 0 < b) (hE : Continuous E) (hG : IntegrableOn G (Ioc 0 b)) (henergy : ∀ a, 0 < a → a ≤ b → κ * (∫ t in a..b, G t) ≤ E a - E b + c * (∫ t in a..b, E t)) : κ * (∫ t in 0..b, G t) ≤ E 0 - E b + c * (∫ t in 0..b, E t) := by
  let a : ℕ → ℝ := fun n => b * (((n : ℝ) + 1)⁻¹)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hab (n : ℕ) : a n ≤ b := by
    dsimp [a]
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hi : ((n : ℝ) + 1)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).2 hn; nlinarith
  have hat : Tendsto a atTop (𝓝 0) := by simpa only [a, mul_zero, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul b
  have haw : Tendsto a atTop (𝓝[Icc 0 b] 0) := tendsto_nhdsWithin_iff.mpr ⟨hat, Eventually.of_forall fun n => ⟨(ha n).le, hab n⟩⟩
  have hgi : IntervalIntegrable G volume 0 b := (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hG
  have hgc : ContinuousOn (fun x => ∫ t in x..b, G t) (Icc 0 b) := by
    have hh := intervalIntegral.continuousOn_primitive_interval' hgi (right_mem_uIcc : b ∈ Set.uIcc (0 : ℝ) b); rw [uIcc_of_le hb.le] at hh; convert hh.neg using 1 <;> ext x <;> exact intervalIntegral.integral_symm b x
  have hec : ContinuousOn (fun x => ∫ t in x..b, E t) (Icc 0 b) := by
    have hei : IntervalIntegrable E volume 0 b := hE.intervalIntegrable 0 b; have hh := intervalIntegral.continuousOn_primitive_interval' hei (right_mem_uIcc : b ∈ Set.uIcc (0 : ℝ) b)
    rw [uIcc_of_le hb.le] at hh; convert hh.neg using 1 <;> ext x <;> exact intervalIntegral.integral_symm b x
  have h0 : (0 : ℝ) ∈ Icc 0 b := ⟨le_rfl, hb.le⟩; have hl := (Filter.Tendsto.comp (hgc 0 h0) haw).const_mul κ; have hr : Tendsto (fun n : ℕ => E (a n) - E b + c * (∫ t in (a n)..b, E t)) atTop (𝓝 (E 0 - E b + c * (∫ t in 0..b, E t))) := (((hE.tendsto 0).comp hat).sub tendsto_const_nhds).add ((Filter.Tendsto.comp (hec 0 h0) haw).const_mul c)
  exact le_of_tendsto_of_tendsto hl hr (Eventually.of_forall fun n => henergy (a n) (ha n) (hab n))
private theorem br07_dissipation_bounded (E G : ℝ → ℝ) (b c κ M : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (hE : Continuous E) (hG : IntegrableOn G (Ioc 0 b)) (hEpos : 0 ≤ E b) (hupper : ∀ t ∈ Icc 0 b, E t ≤ M) (henergy : ∀ a, 0 < a → a ≤ b → κ * (∫ t in a..b, G t) ≤ E a - E b + c * (∫ t in a..b, E t)) : κ * (∫ t in 0..b, G t) ≤ (1 + c * b) * M := by
  have hi : (∫ t in 0..b, E t) ≤ b * M := by
    have hi := intervalIntegral.integral_mono_on hb.le (hE.intervalIntegrable 0 b) (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume 0 b) hupper
    simpa using hi
  have hh := br07_dissipation_inequality_zero E G b c κ hb hE hG henergy
  have h0 := hupper 0 ⟨le_rfl, hb.le⟩; nlinarith [mul_le_mul_of_nonneg_left hi hc]
private theorem br07_supplied_weighted_energy_same_multiplier {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ) (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R)) (hT : ∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] fun x => Real.exp (lam * φ x) * f x) : ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)), ‖T (SpectralHeat.heatOperator (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f)‖ ^ 2 ≤ Real.exp ((2 * (κ⁻¹ ^ 2 * L ^ 2)) * (t : ℝ)) * ‖T f‖ ^ 2 := by
  obtain ⟨U, hU, hbound⟩ := c12_supplied_spectral_heat_weighted_energy_bound hd hκ h R hR s φ hφ lam L hq
  have hUT : U = T := by apply ContinuousLinearMap.ext; intro f; exact Lp.ext ((hU f).trans (hT f).symm)
  simpa only [hUT] using hbound
private theorem br07_dissipation_exp_bounded (E G : ℝ → ℝ) (b c κ M : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (hM : 0 ≤ M) (hE : Continuous E) (hG : IntegrableOn G (Ioc 0 b)) (hEpos : 0 ≤ E b) (hupper : ∀ t ∈ Icc 0 b, E t ≤ Real.exp (c * t) * M) (henergy : ∀ a, 0 < a → a ≤ b → κ * (∫ t in a..b, G t) ≤ E a - E b + c * (∫ t in a..b, E t)) : κ * (∫ t in 0..b, G t) ≤ (1 + c * b) * (Real.exp (c * b) * M) := by
  apply br07_dissipation_bounded E G b c κ (Real.exp (c * b) * M) hb hc hE hG hEpos _ henergy
  intro t ht; exact (hupper t ht).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hc)) hM)
private theorem br07_restrict_gradient_by_phase {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X) (φ g : X → ℝ) (lam a : ℝ) (hlam : 0 ≤ lam) (hg : Integrable g (μ.restrict A)) (hw : Integrable (fun x => Real.exp (2 * lam * φ x) * g x) μ) (hgp : ∀ᵐ x ∂μ, 0 ≤ g x) (hφ : ∀ᵐ x ∂μ.restrict A, a ≤ φ x) : (∫ x in A, g x ∂μ) ≤ Real.exp (-2 * lam * a) * ∫ x, Real.exp (2 * lam * φ x) * g x ∂μ := by
  have hp : ∀ᵐ x ∂μ.restrict A, g x ≤ Real.exp (-2 * lam * a) * (Real.exp (2 * lam * φ x) * g x) := by
    filter_upwards [ae_restrict_of_ae hgp, hφ] with x hgx hφx
    have he : (1 : ℝ) ≤ Real.exp (-2 * lam * a) * Real.exp (2 * lam * φ x) := by
      rw [← Real.exp_add, ← Real.exp_zero]; apply Real.exp_le_exp.mpr; nlinarith [mul_le_mul_of_nonneg_left hφx hlam]
    nlinarith [mul_le_mul_of_nonneg_right he hgx]
  have hi := integral_mono_ae hg (hw.restrict.const_mul (Real.exp (-2 * lam * a))) hp
  rw [integral_const_mul] at hi
  exact hi.trans (mul_le_mul_of_nonneg_left (integral_mono_measure Measure.restrict_le_self (hgp.mono fun x hx => mul_nonneg (Real.exp_pos _).le hx) hw) (Real.exp_pos _).le)
private theorem br07_optimize_dissipation_exponent (a δ t : ℝ) (ha : 0 < a) (ht : 0 < t) : let lam := δ / (4 * a * t); (1 + a * lam ^ 2 * t) * Real.exp (-lam * δ + a * lam ^ 2 * t) ≤ Real.exp (-(δ ^ 2) / (8 * a * t)) := by
  dsimp; calc
    _ ≤ Real.exp (a * (δ / (4 * a * t)) ^ 2 * t) * Real.exp (-(δ / (4 * a * t)) * δ + a * (δ / (4 * a * t)) ^ 2 * t) := mul_le_mul_of_nonneg_right (by simpa only [add_comm] using Real.add_one_le_exp (a * (δ / (4 * a * t)) ^ 2 * t)) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; field_simp [ne_of_gt ha, ne_of_gt ht] <;> ring
private theorem br07_separated_energy_from_weighted {X : Type*} [MeasurableSpace X] (μ : Measure X) (A : Set X) (φ g : X → ℝ) (κ a δ t M : ℝ) (hκ : 0 ≤ κ) (ha : 0 < a) (hδ : 0 ≤ δ) (ht : 0 < t) (hM : 0 ≤ M) (hg : Integrable g (μ.restrict A)) (hgp : ∀ᵐ x ∂μ, 0 ≤ g x) (hφ : ∀ᵐ x ∂μ.restrict A, 3 * δ / 4 ≤ φ x) (hw : ∀ lam : ℝ, 0 ≤ lam → Integrable (fun x => Real.exp (2 * lam * φ x) * g x) μ) (hbound : ∀ lam : ℝ, 0 ≤ lam → κ * (∫ x, Real.exp (2 * lam * φ x) * g x ∂μ) ≤ (1 + a * lam ^ 2 * t) * Real.exp (a * lam ^ 2 * t + lam * δ / 2) * M) : κ * (∫ x in A, g x ∂μ) ≤ Real.exp (-(δ ^ 2) / (8 * a * t)) * M := by
  let lam := δ / (4 * a * t); have hlam : 0 ≤ lam := (by dsimp [lam]; positivity); have hp := br07_restrict_gradient_by_phase μ A φ g lam (3 * δ / 4) hlam hg (hw lam hlam) hgp hφ
  have hfirst : κ * (∫ x in A, g x ∂μ) ≤ Real.exp (-2 * lam * (3 * δ / 4)) * ((1 + a * lam ^ 2 * t) * Real.exp (a * lam ^ 2 * t + lam * δ / 2) * M) := by nlinarith [mul_le_mul_of_nonneg_left hp hκ, mul_le_mul_of_nonneg_left (hbound lam hlam) (Real.exp_pos (-2 * lam * (3 * δ / 4))).le]
  have he : Real.exp (-2 * lam * (3 * δ / 4)) * ((1 + a * lam ^ 2 * t) * Real.exp (a * lam ^ 2 * t + lam * δ / 2) * M) = ((1 + a * lam ^ 2 * t) * Real.exp (-lam * δ + a * lam ^ 2 * t)) * M := by have hexp : Real.exp (-2 * lam * (3 * δ / 4)) * Real.exp (a * lam ^ 2 * t + lam * δ / 2) = Real.exp (-lam * δ + a * lam ^ 2 * t) := (by rw [← Real.exp_add]; congr 1; ring); rw [← hexp]; ring
  rw [he] at hfirst; exact hfirst.trans (mul_le_mul_of_nonneg_right (br07_optimize_dissipation_exponent a δ t ha ht) hM)
private theorem br07_supplied_spectral_lift_unique {d : ℕ} {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R) (Q₁ Q₂ : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR) (h₁ : ∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q₁ t ht) = SpectralHeat.heatOperator (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) (h₂ : ∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q₂ t ht) = SpectralHeat.heatOperator (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) : Q₁ = Q₂ := by funext t ht; apply ContinuousLinearMap.ext; intro f; apply injective_dirichletHilbertInclusion hκ h R hR; exact congrArg (fun A => A f) ((h₁ t ht).trans (h₂ t ht).symm)
private theorem br07_initial_phase_square_bound {d : ℕ} {μ : Measure (Vec d)} (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (φ : Vec d → ℝ) (lam δ : ℝ) (hlam : 0 ≤ lam) (hT : ∀ f, (T f : Vec d → ℝ) =ᵐ[μ] fun x => Real.exp (lam * φ x) * f x) (B : Set (Vec d)) (hφ : ∀ x ∈ B, φ x ≤ δ / 4) (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, x ∉ B → f x = 0) : ‖T f‖ ^ 2 ≤ Real.exp (lam * δ / 2) * ‖f‖ ^ 2 := by have hn := c12_phase_multiplier_norm_upper T φ lam (δ / 4) hlam hT B hφ f hf; have hsq := (sq_le_sq₀ (norm_nonneg (T f)) (by positivity : 0 ≤ Real.exp (lam * (δ / 4)) * ‖f‖)).2 hn; rw [mul_pow, ← Real.exp_nat_mul] at hsq; convert hsq using 1 <;> congr 1 <;> push_cast <;> ring

/-- A single native lift has the weighted gradient estimate for every
nonnegative phase parameter, with the initial mass supported in `B`. -/
theorem br07_supplied_spectral_weighted_gradient_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hgrad : ∀ x, PDE.vecEuclideanNorm (PDE.classicalGradient φ x) ≤ 1)
    (B : Set (Vec d)) (δ : ℝ) (hB : ∀ x ∈ B, φ x ≤ δ / 4)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ lam : ℝ, 0 ≤ lam → ∀ b : ℝ, 0 < b →
        IntegrableOn (br07_native_weighted_gradient R hR φ lam Q f) (Set.Ioc 0 b) ∧
        κ * (∫ t in 0..b, br07_native_weighted_gradient R hR φ lam Q f t) ≤
          (1 + (4 * κ⁻¹ ^ 2 * lam ^ 2) * b) *
            Real.exp ((4 * κ⁻¹ ^ 2 * lam ^ 2) * b + lam * δ / 2) * ‖f‖ ^ 2 := by
  have hzero : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => (0 : ℝ) * fderiv ℝ φ x (Pi.single i 1)) ≤ (0 : ℝ) ^ 2 :=
    ae_of_all _ (fun x => c12_unit_gradient_weight_bound φ hgrad 0 x)
  obtain ⟨T₀, Q, hT₀, hQc₀, hQ, hw₀, he₀, hi₀⟩ :=
    br07_supplied_spectral_heat_gradient_integrable_zero hd hκ h R hR s φ hφ 0 0 hzero
  refine ⟨Q, hQc₀, hQ, ?_⟩
  intro lam hlam b hb
  have hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ lam ^ 2 :=
    ae_of_all _ (c12_unit_gradient_weight_bound φ hgrad lam)
  obtain ⟨T, Q', hT, hQc, hQ', hw, he, hi⟩ :=
    br07_supplied_spectral_heat_gradient_integrable_zero hd hκ h R hR s φ hφ lam lam hq
  have hsame : Q' = Q := br07_supplied_spectral_lift_unique hκ h R hR s Q' Q hQ' hQ
  subst Q'
  refine ⟨hi f b hb, ?_⟩
  let c : ℝ := 4 * κ⁻¹ ^ 2 * lam ^ 2
  let E : ℝ → ℝ := fun t => ‖T (SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t.toNNReal f)‖ ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hE : Continuous E :=
    ((T.continuous.comp ((SpectralHeat.heatOperator_continuous
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal)).norm).pow 2
  have hweighted := br07_supplied_weighted_energy_same_multiplier hd hκ h R hR s φ hφ lam lam hq T hT
  have hupper : ∀ t ∈ Icc 0 b, E t ≤ Real.exp (c * t) * ‖T f‖ ^ 2 := by
    intro t ht
    have h := hweighted t.toNNReal f
    rw [Real.coe_toNNReal _ ht.1] at h
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply Real.exp_le_exp.mpr
    dsimp [c]
    nlinarith [sq_nonneg κ⁻¹, sq_nonneg lam, mul_nonneg (sq_nonneg κ⁻¹) (sq_nonneg lam),
      mul_nonneg (mul_nonneg (sq_nonneg κ⁻¹) (sq_nonneg lam)) ht.1]
  have hdiss := br07_dissipation_exp_bounded E
    (br07_native_weighted_gradient R hR φ lam Q f) b c κ (‖T f‖ ^ 2)
    hb hc (sq_nonneg _) hE (hi f b hb) (sq_nonneg _) hupper (by
      intro a ha hab
      simpa only [E, c] using he f a b ha hab)
  have hinit := br07_initial_phase_square_bound T φ lam δ hlam hT B hB f hf
  calc
    _ ≤ (1 + c * b) * (Real.exp (c * b) * ‖T f‖ ^ 2) := hdiss
    _ ≤ (1 + c * b) * (Real.exp (c * b) * (Real.exp (lam * δ / 2) * ‖f‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)
        (by positivity)
    _ = _ := by rw [Real.exp_add]; dsimp [c]; ring

/-- A lower phase bound on a measurable spatial set extracts its native
Dirichlet energy from the global exponentially weighted energy. -/
theorem br07_native_gradient_phase_restriction {d : ℕ}
    (R : ℝ) (hR : 0 < R) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (A : Set (Vec d)) (hA : MeasurableSet A)
    (a lam : ℝ) (hlam : 0 ≤ lam) (hphase : ∀ x ∈ A, a ≤ φ x)
    (u : DirichletHilbertSpace (d := d) R hR) :
    (∫ x in A, euclideanSq (fun i => u.val (some i) x)
      ∂(volume.restrict (sourceBall (0 : Vec d) R))) ≤
      Real.exp (-2 * lam * a) *
        ∫ x in sourceBall (0 : Vec d) R,
          Real.exp (2 * lam * φ x) * euclideanSq (fun i => u.val (some i) x) := by
  have hg : Integrable (fun x => euclideanSq (fun i => u.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    simpa only [mul_zero, zero_mul, Real.exp_zero, one_mul] using
      br07_weighted_native_gradient_integrable R hR φ hφ 0 u
  have hw := br07_weighted_native_gradient_integrable R hR φ hφ lam u
  have hnonneg : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      0 ≤ euclideanSq (fun i => u.val (some i) x) := by
    apply ae_of_all
    intro x
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hp : ∀ᵐ x ∂(volume.restrict (sourceBall (0 : Vec d) R)).restrict A, a ≤ φ x := by
    filter_upwards [ae_restrict_mem hA] with x hx
    exact hphase x hx
  exact br07_restrict_gradient_by_phase _ A φ _ lam a hlam hg.restrict hw hnonneg hp

/-- Restricting the native Dirichlet energy to a measurable set gives a
continuous quadratic form on the value-gradient carrier. -/
theorem br07_restricted_gradient_continuous_form {d : ℕ}
    (R : ℝ) (hR : 0 < R) (A : Set (Vec d)) (hA : MeasurableSet A) :
    ∃ D : DirichletHilbertSpace (d := d) R hR →L[ℝ]
        DirichletHilbertSpace (d := d) R hR →L[ℝ] ℝ,
      ∀ u, D u u = ∫ x in A, euclideanSq (fun i => u.val (some i) x)
        ∂(volume.restrict (sourceBall (0 : Vec d) R)) := by
  classical
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let m : Vec d → ℝ := A.indicator (fun _ => 1)
  let a : Vec d → Option (Fin d) → Option (Fin d) → ℝ := fun x i j =>
    if i = j ∧ i ≠ none then m x else 0
  have ha (i j : Option (Fin d)) : AEStronglyMeasurable (fun x => a x i j) μ := by
    dsimp only [a]
    split_ifs
    · exact aestronglyMeasurable_const.indicator hA
    · exact aestronglyMeasurable_const
  have hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ 1 := by
    apply ae_of_all
    intro x i j
    dsimp only [a]
    split_ifs
    · by_cases hx : x ∈ A <;> simp [m, hx]
    · norm_num
  obtain ⟨F, hF⟩ := exists_coordinateL2Form μ a ha (by norm_num) hb
  let S := (dirichletHilbertSubmodule (d := d) R hR).subtypeL
  refine ⟨F.bilinearComp S S, ?_⟩
  intro u
  change F u.val u.val = _
  rw [hF]
  have hpoint (x : Vec d) :
      (∑ i, ∑ j, a x i j * u.val j x * u.val i x) =
        m x * euclideanSq (fun i => u.val (some i) x) := by
    simp only [a, Fintype.sum_option, ne_eq, not_true_eq_false, and_false,
      ↓reduceIte, zero_mul, Finset.sum_const_zero, zero_add, Option.some_ne_none,
      not_false_eq_true, and_true, Option.some.injEq, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, euclideanSq, dot, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    ring
  simp_rw [hpoint]
  have hm : (fun x => m x * euclideanSq (fun i => u.val (some i) x)) =
      A.indicator (fun x => euclideanSq (fun i => u.val (some i) x)) := by
    funext x
    by_cases hx : x ∈ A <;> simp [m, hx]
  rw [hm]
  change (∫ x in (Q : Set (SpatialCoordinates d)),
    A.indicator (fun x => euclideanSq (fun i => u.val (some i) x)) x) = _
  rw [← integral_indicator hA]
  apply setIntegral_eq_of_subset_of_ae_sdiff_eq_zero Q.isOpen.measurableSet.nullMeasurableSet
    (sourceBall_subset_cube R hR)
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ∀ i : Fin d, x ∉ sourceBall (0 : Vec d) R → u.val (some i) x = 0 :=
    ae_all_iff.mpr (fun i => dirichletHilbert_coordinate_zero_exterior R hR u (some i))
  filter_upwards [ae_imp_of_ae_restrict hz] with x hx hxs
  have he : (fun i => u.val (some i) x) = 0 := funext (fun i => hx hxs.1 i hxs.2)
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA, he]; simp [euclideanSq, dot]
  · simp [hxA]

/-- The native Dirichlet energy restricted to a spatial set at positive times. -/
@[nolint defsWithUnderscore]
noncomputable def br07_native_restricted_gradient {d : ℕ} {ρ : Vec d → ℝ}
    (R : ℝ) (hR : 0 < R) (A : Set (Vec d))
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (t : ℝ) : ℝ :=
  if ht : 0 < t then
    ∫ x in A, euclideanSq (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val
      (some i) x) ∂(volume.restrict (sourceBall (0 : Vec d) R))
  else 0

/-- The restricted energy is integrable on positive-time compact intervals. -/
theorem br07_native_restricted_gradient_integrableOn {d : ℕ} {ρ : Vec d → ℝ}
    (R : ℝ) (hR : 0 < R) (A : Set (Vec d)) (hA : MeasurableSet A)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (hQ : ∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (a b : ℝ) (ha : 0 < a) :
    IntegrableOn (br07_native_restricted_gradient R hR A Q f) (Set.Icc a b) := by
  obtain ⟨D, hD⟩ := br07_restricted_gradient_continuous_form R hR A hA
  let V : Set.Icc a b → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q t.val.toNNReal (Real.toNNReal_pos.mpr (ha.trans_le t.property.1)) f
  let W : Set.Icc a b → {t : ℝ≥0 // 0 < t} := fun t =>
    ⟨t.val.toNNReal, Real.toNNReal_pos.mpr (ha.trans_le t.property.1)⟩
  have hW : Continuous W :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  have hV : Continuous V := by
    simpa only [V, W, Function.comp_def] using (hQ f).comp hW
  have hC : Continuous (fun t : Set.Icc a b => D (V t) (V t)) :=
    (D.continuous.comp hV).clm_apply hV
  apply ContinuousOn.integrableOn_Icc
  apply continuousOn_iff_continuous_restrict.mpr
  have heq : (fun t : Set.Icc a b => br07_native_restricted_gradient R hR A Q f t.val) =
      (fun t : Set.Icc a b => D (V t) (V t)) := by
    funext t
    have ht : 0 < t.val := ha.trans_le t.property.1
    rw [hD]
    simp only [br07_native_restricted_gradient, dif_pos ht, V]
  change Continuous (fun t : Set.Icc a b => br07_native_restricted_gradient R hR A Q f t.val)
  rw [heq]
  exact hC

/-- A restricted native energy is integrable up to zero whenever the full
unweighted energy is integrable there. -/
@[nolint unusedArguments]
theorem br07_native_restricted_gradient_integrable_zero {d : ℕ} {ρ : Vec d → ℝ}
    (R : ℝ) (hR : 0 < R) (A : Set (Vec d)) (hA : MeasurableSet A)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (hQ : ∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (b : ℝ) (hb : 0 < b)
    (hfull : IntegrableOn (br07_native_weighted_gradient R hR φ 0 Q f) (Set.Ioc 0 b)) :
    IntegrableOn (br07_native_restricted_gradient R hR A Q f) (Set.Ioc 0 b) := by
  let G := br07_native_restricted_gradient R hR A Q f
  let H := br07_native_weighted_gradient R hR φ 0 Q f
  have hpos : ∀ t, 0 < t → 0 ≤ G t := by
    intro t ht
    simp only [G, br07_native_restricted_gradient, dif_pos ht]
    apply integral_nonneg
    intro x
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hle : ∀ t, 0 < t → G t ≤ H t := by
    intro t ht
    have h := br07_native_gradient_phase_restriction R hR (fun _ => 0) contDiff_const A hA 0 0
      (le_refl 0) (fun x hx => le_refl 0)
      (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f)
    simpa [G, H, br07_native_restricted_gradient, br07_native_weighted_gradient, ht] using h
  apply br07_integrableOn_Ioc_zero_of_uniform_bound G b (∫ t in Set.Ioc 0 b, H t) hb
  · exact fun a ha => br07_native_restricted_gradient_integrableOn R hR A hA Q hQ f a b ha
  · exact hpos
  · intro a ha hab
    have hsub : Set.Ioc a b ⊆ Set.Ioc 0 b := fun t ht => ⟨ha.trans ht.1, ht.2⟩
    have hGi : IntervalIntegrable G volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
        (br07_native_restricted_gradient_integrableOn R hR A hA Q hQ f a b ha)
    have hHi : IntervalIntegrable H volume a b :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 (hfull.mono_set hsub)
    have hi := intervalIntegral.integral_mono_on hab hGi hHi
      (fun t ht => hle t (ha.trans_le ht.1))
    simp only [intervalIntegral.integral_of_le hab] at hi
    rw [intervalIntegral.integral_of_le hab]
    exact hi.trans (integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (ae_of_all _ (fun t => by
        by_cases ht : 0 < t
        · exact le_trans (hpos t ht) (hle t ht)
        · simp [H, br07_native_weighted_gradient, ht])) hfull)

/-- Exponentially small native gradient energy on a set separated from the
support of the initial datum. -/
theorem br07_supplied_spectral_separated_gradient_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) (A B : Set (Vec d))
    (hA : MeasurableSet A) (hB : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0) (b : ℝ) (hb : 0 < b) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t) (v : DirichletHilbertSpace (d := d) R hR),
        HasDerivAt (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ)) ∧
      IntegrableOn (br07_native_restricted_gradient R hR A Q f) (Set.Ioc 0 b) ∧
      κ * (∫ t in 0..b, br07_native_restricted_gradient R hR A Q f t) ≤
        Real.exp (-(δ ^ 2) / (8 * (4 * κ⁻¹ ^ 2) * b)) * ‖f‖ ^ 2 := by
  obtain ⟨φ, hφ, hgrad, hAφ, hBφ⟩ := c12_smooth_separating_phase A B hB δ hδ hsep
  obtain ⟨Q, hQ, hheat, hweighted⟩ :=
    br07_supplied_spectral_weighted_gradient_bound hd hκ h R hR s φ hφ hgrad B δ hBφ f hf
  have hG := br07_native_restricted_gradient_integrable_zero R hR A hA φ hφ Q hQ f b hb
    ((hweighted 0 (le_refl 0) b hb).1)
  have hzero : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => (0 : ℝ) * fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x
        (Pi.single i 1)) ≤ (0 : ℝ) ^ 2 := by
    filter_upwards [] with x
    simp [euclideanSq, dot]
  obtain ⟨T₀, Q₀, hT₀, hQc₀, hheat₀, hderiv, hdiss⟩ :=
    br07_supplied_spectral_heat_weighted_gradient_derivative hd hκ h R hR s
      (fun _ => 0) contDiff_const 0 0 hzero
  have hQeq : Q₀ = Q := br07_supplied_spectral_lift_unique hκ h R hR s Q₀ Q hheat₀ hheat
  subst Q₀
  refine ⟨Q, hQ, hheat, (fun t ht v => hderiv t ht f v), hG, ?_⟩
  let a : ℝ := 4 * κ⁻¹ ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  let lam : ℝ := δ / (4 * a * b)
  have hlam : 0 ≤ lam := by dsimp [lam]; positivity
  let G := br07_native_restricted_gradient R hR A Q f
  let H := br07_native_weighted_gradient R hR φ lam Q f
  have hH := (hweighted lam hlam b hb).1
  have hGi : IntervalIntegrable G volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hG
  have hHi : IntervalIntegrable H volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hH
  have hp : ∀ t ∈ Set.Icc 0 b, G t ≤ Real.exp (-2 * lam * (3 * δ / 4)) * H t := by
    intro t ht
    by_cases htp : 0 < t
    · have hr := br07_native_gradient_phase_restriction R hR φ hφ A hA
        (3 * δ / 4) lam hlam hAφ (Q t.toNNReal (Real.toNNReal_pos.mpr htp) f)
      simpa only [G, H, br07_native_restricted_gradient, br07_native_weighted_gradient,
        dif_pos htp] using hr
    · simp [G, H, br07_native_restricted_gradient, br07_native_weighted_gradient, htp]
  have hi := intervalIntegral.integral_mono_on hb.le hGi
    (hHi.const_mul (Real.exp (-2 * lam * (3 * δ / 4)))) hp
  rw [intervalIntegral.integral_const_mul] at hi
  have hw := (hweighted lam hlam b hb).2
  change κ * (∫ t in 0..b, H t) ≤
    (1 + a * lam ^ 2 * b) * Real.exp (a * lam ^ 2 * b + lam * δ / 2) * ‖f‖ ^ 2 at hw
  change κ * (∫ t in 0..b, G t) ≤ _
  have hfirst : κ * (∫ t in 0..b, G t) ≤
      Real.exp (-2 * lam * (3 * δ / 4)) *
        ((1 + a * lam ^ 2 * b) * Real.exp (a * lam ^ 2 * b + lam * δ / 2) * ‖f‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hi hκ.le,
      mul_le_mul_of_nonneg_left hw (Real.exp_pos (-2 * lam * (3 * δ / 4))).le]
  have he : Real.exp (-2 * lam * (3 * δ / 4)) *
      ((1 + a * lam ^ 2 * b) * Real.exp (a * lam ^ 2 * b + lam * δ / 2) * ‖f‖ ^ 2) =
      ((1 + a * lam ^ 2 * b) * Real.exp (-lam * δ + a * lam ^ 2 * b)) * ‖f‖ ^ 2 := by
    have hexp : Real.exp (-2 * lam * (3 * δ / 4)) *
        Real.exp (a * lam ^ 2 * b + lam * δ / 2) =
        Real.exp (-lam * δ + a * lam ^ 2 * b) := by rw [← Real.exp_add]; congr 1; ring
    rw [← hexp]
    ring
  rw [he] at hfirst
  exact hfirst.trans (mul_le_mul_of_nonneg_right
    (br07_optimize_dissipation_exponent a δ b ha hb) (sq_nonneg _))

/-- The elliptic cross term is bounded by the sum of its Euclidean energies. -/
theorem br07_elliptic_cross_energy_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) :
    |dot ((α x).mulVec p) q| ≤ κ⁻¹ * (euclideanSq p + euclideanSq q) := by
  have hplus := c12_davies_double_weight_form_bound hκ h x p q (1 / 2) 1
  have hminus := c12_davies_double_weight_form_bound hκ h x p q (-(1 / 2)) 1
  have hu := ((h.2.2 x).2.2.2 p).2
  change p ⬝ᵥ (α x).mulVec p ≤ κ⁻¹ * euclideanSq p at hu
  rw [dotProduct_comm] at hu
  change -(κ⁻¹ * euclideanSq q) * (1 * (1 / 2)) ^ 2 ≤
    ((α x).mulVec p) ⬝ᵥ (1 ^ 2 • (p + (2 * (1 / 2)) • q)) at hplus
  change -(κ⁻¹ * euclideanSq q) * (1 * (-(1 / 2))) ^ 2 ≤
    ((α x).mulVec p) ⬝ᵥ (1 ^ 2 • (p + (2 * (-(1 / 2))) • q)) at hminus
  simp only [one_pow, one_smul, dotProduct_add, dotProduct_smul, smul_eq_mul] at hplus hminus
  have hq : 0 ≤ κ⁻¹ * euclideanSq q := by
    apply mul_nonneg (inv_nonneg.mpr hκ.le)
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  change |((α x).mulVec p) ⬝ᵥ q| ≤ κ⁻¹ * (euclideanSq p + euclideanSq q)
  apply abs_le.mpr
  constructor <;> nlinarith

/-- Rescaling the two arguments gives the energy inequality needed for
separated forcing. -/
theorem br07_elliptic_cross_energy_bound_scaled {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) (a : ℝ) (ha : 0 < a) :
    |dot ((α x).mulVec p) q| ≤ κ⁻¹ *
      (a ^ 2 * euclideanSq p + a⁻¹ ^ 2 * euclideanSq q) := by
  have hs (c : ℝ) (v : Vec d) : euclideanSq (c • v) = c ^ 2 * euclideanSq v := by
    simp only [euclideanSq, dot, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have he : dot ((α x).mulVec (a • p)) (a⁻¹ • q) = dot ((α x).mulVec p) q := by
    change ((α x).mulVec (a • p)) ⬝ᵥ (a⁻¹ • q) = ((α x).mulVec p) ⬝ᵥ q
    simp only [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
  have hh := br07_elliptic_cross_energy_bound hκ h x (a • p) (a⁻¹ • q)
  rw [he, hs, hs] at hh
  exact hh

#print axioms br07_elliptic_cross_energy_bound_scaled

/-- The native elliptic pairing with a fixed test, extended by zero at
nonpositive times. -/
@[nolint defsWithUnderscore]
noncomputable def br07_native_test_force {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (R : ℝ) (hR : 0 < R)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (v : DirichletHilbertSpace (d := d) R hR)
    (t : ℝ) : ℝ :=
  if ht : 0 < t then
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (Q t.toNNReal (Real.toNNReal_pos.mpr ht) f).val (some i) x))
        (fun i => v.val (some i) x)
  else 0

/-- The supplied spectral action satisfies the integrated native weak-flow
identity on every compact time interval away from zero. -/
theorem br07_supplied_spectral_weak_pairing_interval {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R))
        (v : DirichletHilbertSpace (d := d) R hR) (a b : ℝ), 0 < a → a ≤ b →
        IntervalIntegrable (br07_native_test_force (α := α) R hR Q f v) volume a b ∧
        inner ℝ (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) b.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) -
        inner ℝ (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) a.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) =
        -(∫ t in a..b, br07_native_test_force (α := α) R hR Q f v t) := by
  have hzero : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => (0 : ℝ) * fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x
        (Pi.single i 1)) ≤ (0 : ℝ) ^ 2 := by
    filter_upwards [] with x
    simp [euclideanSq, dot]
  obtain ⟨T, Q, hT, hQ, hheat, hderiv, hdiss⟩ :=
    br07_supplied_spectral_heat_weighted_gradient_derivative hd hκ h R hR s
      (fun _ => 0) contDiff_const 0 0 hzero
  obtain ⟨c, hc, D, hDcoerc, hD⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨Q, hQ, hheat, ?_⟩
  intro f v a b ha hab
  let V : Set.Icc a b → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q t.val.toNNReal (Real.toNNReal_pos.mpr (ha.trans_le t.property.1)) f
  let W : Set.Icc a b → {t : ℝ≥0 // 0 < t} := fun t =>
    ⟨t.val.toNNReal, Real.toNNReal_pos.mpr (ha.trans_le t.property.1)⟩
  have hW : Continuous W :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  have hV : Continuous V := by
    simpa only [V, W, Function.comp_def] using (hQ f).comp hW
  have hC : Continuous (fun t : Set.Icc a b => D (V t) v) :=
    (D.continuous.comp hV).clm_apply continuous_const
  have hforce : IntegrableOn (br07_native_test_force (α := α) R hR Q f v) (Set.Icc a b) := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_iff_continuous_restrict.mpr
    have heq : (fun t : Set.Icc a b => br07_native_test_force (α := α) R hR Q f v t.val) =
        (fun t : Set.Icc a b => D (V t) v) := by
      funext t
      have ht : 0 < t.val := ha.trans_le t.property.1
      rw [hD]
      simp only [br07_native_test_force, dif_pos ht, V]
    change Continuous (fun t : Set.Icc a b => br07_native_test_force (α := α) R hR Q f v t.val)
    rw [heq]
    exact hC
  have hi : IntervalIntegrable (br07_native_test_force (α := α) R hR Q f v) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 hforce
  refine ⟨hi, ?_⟩
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun r => inner ℝ (SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
    (f' := fun t => -br07_native_test_force (α := α) R hR Q f v t)
    (fun t ht => by
      have htp : 0 < t := ha.trans_le ((Set.uIcc_of_le hab ▸ ht).1)
      have hd := hderiv t.toNNReal (Real.toNNReal_pos.mpr htp) f v
      simpa only [Real.coe_toNNReal _ htp.le, br07_native_test_force, dif_pos htp] using hd)
    hi.neg
  rw [intervalIntegral.integral_neg] at he
  exact he.symm

/-- The native weak forcing is integrable up to the initial time whenever
its full gradient energy is integrable. -/
@[nolint unusedArguments]
theorem br07_native_test_force_integrable_zero {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (hQ : ∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f))
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (v : DirichletHilbertSpace (d := d) R hR)
    (b : ℝ) (hb : 0 < b)
    (hfull : IntegrableOn (br07_native_weighted_gradient R hR (fun _ => 0) 0 Q f)
      (Set.Ioc 0 b)) :
    IntegrableOn (br07_native_test_force (α := α) R hR Q f v) (Set.Ioc 0 b) := by
  obtain ⟨c, hc, D, hDcoerc, hD⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  let V : Set.Ioi (0 : ℝ) → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q t.val.toNNReal (Real.toNNReal_pos.mpr t.property) f
  let W : Set.Ioi (0 : ℝ) → {t : ℝ≥0 // 0 < t} := fun t =>
    ⟨t.val.toNNReal, Real.toNNReal_pos.mpr t.property⟩
  have hW : Continuous W :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  have hV : Continuous V := by
    simpa only [V, W, Function.comp_def] using (hQ f).comp hW
  have hC : Continuous (fun t : Set.Ioi (0 : ℝ) => D (V t) v) :=
    (D.continuous.comp hV).clm_apply continuous_const
  have hcont : ContinuousOn (br07_native_test_force (α := α) R hR Q f v) (Set.Ioi 0) := by
    apply continuousOn_iff_continuous_restrict.mpr
    have heq : (fun t : Set.Ioi (0 : ℝ) => br07_native_test_force (α := α) R hR Q f v t.val) =
        (fun t : Set.Ioi (0 : ℝ) => D (V t) v) := by
      funext t
      have ht : 0 < t.val := t.property
      rw [hD]
      simp only [br07_native_test_force, dif_pos ht, V]
    change Continuous (fun t : Set.Ioi (0 : ℝ) => br07_native_test_force (α := α) R hR Q f v t.val)
    rw [heq]
    exact hC
  let C : ℝ := ∫ x in sourceBall (0 : Vec d) R, euclideanSq (fun i => v.val (some i) x)
  have hv : Integrable (fun x => euclideanSq (fun i => v.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    simpa using br07_weighted_native_gradient_integrable R hR (fun _ => 0) contDiff_const 0 v
  have hmajor : IntegrableOn (fun t => κ⁻¹ *
      (br07_native_weighted_gradient R hR (fun _ => 0) 0 Q f t + C)) (Set.Ioc 0 b) :=
    (hfull.add (integrableOn_const (measure_Ioc_lt_top.ne))).const_mul κ⁻¹
  apply hmajor.mono' ((hcont.mono Set.Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htp : 0 < t := ht.1
  let u := Q t.toNNReal (Real.toNNReal_pos.mpr htp) f
  have hu : Integrable (fun x => euclideanSq (fun i => u.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    simpa using br07_weighted_native_gradient_integrable R hR (fun _ => 0) contDiff_const 0 u
  have hform := c12_dirichlet_gradient_form_integrable hκ h R hR u v
  have hi := integral_mono_ae hform.norm ((hu.add hv).const_mul κ⁻¹)
    (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply] using
        br07_elliptic_cross_energy_bound hκ h x (fun i => u.val (some i) x)
          (fun i => v.val (some i) x)))
  have htriangle := norm_integral_le_integral_norm (μ := volume.restrict (sourceBall (0 : Vec d) R))
    (fun x => dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x))
  simp only [Pi.add_apply, Pi.mul_apply] at hi
  rw [integral_const_mul, integral_add hu hv] at hi
  simpa [br07_native_test_force, br07_native_weighted_gradient, htp, u, C,
    Real.norm_eq_abs] using htriangle.trans hi

/-- The supplied spectral flow satisfies its native weak identity from the
initial time, with an absolutely integrable forcing term. -/
theorem br07_supplied_spectral_weak_pairing_zero {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ (Q : (t : ℝ≥0) → 0 < t → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ]
        DirichletHilbertSpace (d := d) R hR),
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ t ht, (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s)
            s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R))
        (v : DirichletHilbertSpace (d := d) R hR) (b : ℝ), 0 < b →
        IntervalIntegrable (br07_native_test_force (α := α) R hR Q f v) volume 0 b ∧
        inner ℝ (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) b.toNNReal f)
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) -
        inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v) =
        -(∫ t in 0..b, br07_native_test_force (α := α) R hR Q f v t) := by
  have hzero : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => (0 : ℝ) * fderiv ℝ (fun _ : Vec d => (0 : ℝ)) x
        (Pi.single i 1)) ≤ (0 : ℝ) ^ 2 := by
    filter_upwards [] with x
    simp [euclideanSq, dot]
  obtain ⟨T, Q, hT, hQ, hheat, hderiv, hdiss, henergy⟩ :=
    br07_supplied_spectral_heat_gradient_integrable_zero hd hκ h R hR s
      (fun _ => 0) contDiff_const 0 0 hzero
  refine ⟨Q, hQ, hheat, ?_⟩
  intro f v b hb
  have hfi := br07_native_test_force_integrable_zero hd hκ h R hR Q hQ f v b hb
    (henergy f b hb)
  have hi : IntervalIntegrable (br07_native_test_force (α := α) R hR Q f v) volume 0 b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hb.le).2 hfi
  refine ⟨hi, ?_⟩
  let F : ℝ → ℝ := fun r => inner ℝ (SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)
    (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v)
  have hF : Continuous F :=
    ((SpectralHeat.heatOperator_continuous
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal).inner continuous_const
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb
    (f := F) (f' := fun t => -br07_native_test_force (α := α) R hR Q f v t)
    (fun t ht => by
      have htp : 0 < t := ht.1
      have hh := hderiv t.toNNReal (Real.toNNReal_pos.mpr htp) f v
      simpa only [F, Real.coe_toNNReal _ htp.le, br07_native_test_force, dif_pos htp] using hh)
    hi.neg ((hF.continuousAt.mono_left nhdsWithin_le_nhds))
    ((hF.continuousAt.mono_left nhdsWithin_le_nhds))
  rw [intervalIntegral.integral_neg] at hFTC
  simpa only [F, Real.toNNReal_zero, SpectralHeat.heatOperator_zero,
    ContinuousLinearMap.id_apply] using hFTC.symm

/-- A native test with gradient supported in a measurable set pairs only with
    the gradient energy on that set. -/
@[nolint unusedArguments]
theorem br07_native_test_force_restricted_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (v : DirichletHilbertSpace (d := d) R hR)
    (hv : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      x ∉ A → ∀ i : Fin d, v.val (some i) x = 0)
    (a : ℝ) (ha : 0 < a) (t : ℝ) (ht : 0 < t) :
    |br07_native_test_force (α := α) R hR Q f v t| ≤ κ⁻¹ *
      (a ^ 2 * br07_native_restricted_gradient R hR A Q f t + a⁻¹ ^ 2 *
        (∫ x in A, euclideanSq (fun i => v.val (some i) x)
          ∂(volume.restrict (sourceBall (0 : Vec d) R)))) := by
  let μ := volume.restrict (sourceBall (0 : Vec d) R)
  let u := Q t.toNNReal (Real.toNNReal_pos.mpr ht) f
  let F : Vec d → ℝ := fun x => dot ((α x).mulVec (fun i => u.val (some i) x))
    (fun i => v.val (some i) x)
  have hu : Integrable (fun x => euclideanSq (fun i => u.val (some i) x)) μ := by
    simpa [μ] using br07_weighted_native_gradient_integrable R hR (fun _ => 0) contDiff_const 0 u
  have hvg : Integrable (fun x => euclideanSq (fun i => v.val (some i) x)) μ := by
    simpa [μ] using br07_weighted_native_gradient_integrable R hR (fun _ => 0) contDiff_const 0 v
  have hform : Integrable F μ := by
    simpa [F, μ] using c12_dirichlet_gradient_form_integrable hκ h R hR u v
  have he : (∫ x, F x ∂μ) = ∫ x in A, F x ∂μ := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    by_cases hxa : x ∈ A
    · simp [hxa]
    · have hz : (fun i => v.val (some i) x) = 0 := funext (hx hxa)
      simp only [Set.indicator_of_notMem hxa]
      change dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => v.val (some i) x) = 0
      rw [hz]
      simp [dot]
  have hi := integral_mono_ae (μ := μ.restrict A) (hform.restrict (s := A)).norm
    ((((hu.restrict (s := A)).const_mul (a ^ 2)).add ((hvg.restrict (s := A)).const_mul (a⁻¹ ^ 2))).const_mul κ⁻¹)
    (ae_of_all _ (fun x => by
      simpa only [F, Real.norm_eq_abs, Pi.add_apply, Pi.mul_apply] using
        br07_elliptic_cross_energy_bound_scaled hκ h x
          (fun i => u.val (some i) x) (fun i => v.val (some i) x) a ha))
  have htriangle := norm_integral_le_integral_norm (μ := μ.restrict A) F
  simp only [Pi.add_apply, Pi.mul_apply] at hi
  rw [integral_const_mul, integral_add ((hu.restrict (s := A)).const_mul _) ((hvg.restrict (s := A)).const_mul _),
    integral_const_mul, integral_const_mul] at hi
  have hf : br07_native_test_force (α := α) R hR Q f v t = ∫ x, F x ∂μ := by
    simp only [br07_native_test_force, dif_pos ht, F, u, μ]
  rw [hf, he]
  simpa only [br07_native_restricted_gradient, dif_pos ht, u, μ, Real.norm_eq_abs] using
    htriangle.trans hi

#print axioms br07_native_test_force_restricted_bound

#print axioms br07_supplied_spectral_weak_pairing_zero

#print axioms br07_native_test_force_integrable_zero

#print axioms br07_elliptic_cross_energy_bound
#print axioms br07_supplied_spectral_weak_pairing_interval

#print axioms br07_supplied_spectral_separated_gradient_bound

#print axioms br07_restricted_gradient_continuous_form
#print axioms br07_native_gradient_phase_restriction

#print axioms br07_supplied_spectral_weighted_gradient_bound

#print axioms br07_supplied_spectral_heat_gradient_integrable_zero

#print axioms br07_supplied_spectral_heat_gradient_integral

#print axioms br07_integrate_energy_dissipation

#print axioms br07_weighted_native_gradient_integrable
#print axioms br07_double_weight_form_coercive_density
#print axioms br07_native_double_weight_form_coercive
#print axioms br07_supplied_spectral_heat_weighted_gradient_derivative
#print axioms br07_double_weight_form_coercive

end EinsteinFull.Calculus
