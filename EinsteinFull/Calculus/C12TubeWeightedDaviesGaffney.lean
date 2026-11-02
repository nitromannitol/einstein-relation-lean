import EinsteinFull.Calculus.C12TubeNativeNashKernelUpper
import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace
import EllipticRegularity.Parabolic.Cauchy.Weights.TruncatedDistance

open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability SubdiffusiveProcess MeasureTheory TopologicalSpace
open Filter

open scoped ENNReal NNReal BigOperators Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- Smooth Euclidean distance gives a uniform positive phase gap between
separated sets, while retaining unit Euclidean gradient bound. -/
theorem c12_smooth_separating_phase {d : ℕ} (A B : Set (Vec d))
    (hB : B.Nonempty) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y)) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ x, PDE.vecEuclideanNorm (PDE.classicalGradient φ x) ≤ 1) ∧
      (∀ x ∈ A, 3 * δ / 4 ≤ φ x) ∧
      (∀ y ∈ B, φ y ≤ δ / 4) := by
  let D := PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance B δ
  have hlimit : Tendsto (fun n : ℕ => Real.sqrt d * PDE.unitConvexApproxScale n)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul PDE.tendsto_unitConvexApproxScale_zero)
  have hevent : ∀ᶠ n : ℕ in atTop, Real.sqrt d * PDE.unitConvexApproxScale n < δ / 4 :=
    (tendsto_order.1 hlimit).2 _ (by positivity)
  obtain ⟨n, hn⟩ := hevent.exists
  let φ := PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify B δ n
  obtain ⟨hsmooth, _, hgrad, herr⟩ :=
    PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_properties hB hδ.le n
  refine ⟨φ, hsmooth, hgrad, ?_, ?_⟩
  · intro x hx
    have hdist : δ ≤ PDE.Parabolic.Cauchy.Weights.euclideanSetDistance B x := by
      apply le_csInf
      · obtain ⟨y, hy⟩ := hB
        exact ⟨PDE.vecEuclideanNorm (x - y), ⟨⟨y, hy⟩, rfl⟩⟩
      · rintro _ ⟨y, rfl⟩
        exact hsep x hx y y.property
    have hD : D x = δ := by
      dsimp [D, PDE.Parabolic.Cauchy.Weights.truncatedEuclideanSetDistance]
      exact min_eq_left hdist
    have he := (abs_le.mp (herr x)).1
    change -(Real.sqrt d * PDE.unitConvexApproxScale n) ≤ φ x - D x at he
    rw [hD] at he
    linarith
  · intro y hy
    exact (PDE.Parabolic.Cauchy.Weights.truncatedDistanceMollify_le_of_mem
      hB hδ.le n hy).trans (le_of_lt hn)

#print axioms c12_smooth_separating_phase

/-- A unit Euclidean gradient bounds the logarithmic gradient of every
exponential phase in the native Dirichlet form. -/
theorem c12_unit_gradient_weight_bound {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ∀ x, PDE.vecEuclideanNorm (PDE.classicalGradient φ x) ≤ 1)
    (lam : ℝ) (x : Vec d) :
    euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ lam ^ 2 := by
  have hn : PDE.vecNormSq (PDE.classicalGradient φ x) ≤ 1 := by
    have hs := (sq_le_sq₀ (PDE.vecEuclideanNorm_nonneg _) (by norm_num)).2 (hφ x)
    simpa only [PDE.vecEuclideanNorm_sq, one_pow] using hs
  change PDE.vecNormSq (lam • PDE.classicalGradient φ x) ≤ lam ^ 2
  rw [PDE.vecNormSq_smul]
  nlinarith [sq_nonneg lam]

#print axioms c12_unit_gradient_weight_bound

/-- Optimize the exponential parameter in a Davies weighted energy bound. -/
theorem c12_davies_optimize_exponent (a δ t : ℝ) (ha : 0 < a)
    (hδ : 0 < δ) (ht : 0 < t) :
    ∃ lam : ℝ, 0 < lam ∧
      Real.exp (-2 * lam * δ + a * lam ^ 2 * t) =
        Real.exp (-(δ ^ 2) / (a * t)) := by
  refine ⟨δ / (a * t), by positivity, ?_⟩
  congr 1
  field_simp
  <;> ring

/-- The symmetric Dirichlet form cancels the cross terms of an exponential
weight. This is the pointwise algebra behind the Davies energy estimate. -/
theorem c12_davies_form_cancel {d : ℕ} (M : Mat d) (hM : M.IsSymm)
    (p q : Vec d) (u : ℝ) :
    dot (M.mulVec (p - u • q)) (p + u • q) =
      dot (M.mulVec p) p - u ^ 2 * dot (M.mulVec q) q := by
  have hs := hM.dotProduct_mulVec_comm (x := p) (y := q)
  change (M.mulVec (p - u • q)) ⬝ᵥ (p + u • q) =
    (M.mulVec p) ⬝ᵥ p - u ^ 2 * ((M.mulVec q) ⬝ᵥ q)
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_add,
    sub_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm p, dotProduct_comm q] at hs
  rw [hs]
  ring

/-- Ellipticity controls the cost of conjugating the native form. -/
theorem c12_davies_form_lower_bound {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (x p q : Vec d) (u : ℝ) :
    κ * euclideanSq p - u ^ 2 * (κ⁻¹ * euclideanSq q) ≤
      dot ((α x).mulVec (p - u • q)) (p + u • q) := by
  rw [c12_davies_form_cancel (α x) (h.2.2 x).2.2.1]
  have hp := ((h.2.2 x).2.2.2 p).1
  have hq := ((h.2.2 x).2.2.2 q).2
  change κ * euclideanSq p ≤ p ⬝ᵥ (α x).mulVec p at hp
  change q ⬝ᵥ (α x).mulVec q ≤ κ⁻¹ * euclideanSq q at hq
  rw [dotProduct_comm] at hp hq
  have hcost := mul_le_mul_of_nonneg_left hq (sq_nonneg u)
  change κ * euclideanSq p - u ^ 2 * (κ⁻¹ * euclideanSq q) ≤
    ((α x).mulVec p) ⬝ᵥ p - u ^ 2 * (((α x).mulVec q) ⬝ᵥ q)
  linarith

/-- Pointwise cost of the double-weight test, expressed in terms of the
once-weighted value. Here `q` is the logarithmic gradient of the weight. -/
theorem c12_davies_double_weight_form_bound {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hκ : 0 < κ) (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) (u m : ℝ) :
    -(κ⁻¹ * euclideanSq q) * (m * u) ^ 2 ≤
      dot ((α x).mulVec p) (m ^ 2 • (p + (2 * u) • q)) := by
  let r : Vec d := p + u • q
  have hr1 : r - u • q = p := by
    ext i
    simp only [r, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hr2 : r + u • q = p + (2 * u) • q := by
    ext i
    simp only [r, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hform := c12_davies_form_lower_bound h x r q u
  rw [hr1, hr2] at hform
  have hn : 0 ≤ κ * euclideanSq r :=
    mul_nonneg hκ.le (PDE.vecNormSq_nonneg r)
  have hcost : -(u ^ 2 * (κ⁻¹ * euclideanSq q)) ≤
      dot ((α x).mulVec p) (p + (2 * u) • q) := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hcost (sq_nonneg m)
  change -(κ⁻¹ * euclideanSq q) * (m * u) ^ 2 ≤
    ((α x).mulVec p) ⬝ᵥ (m ^ 2 • (p + (2 * u) • q))
  rw [dotProduct_smul, smul_eq_mul]
  change m ^ 2 * -(u ^ 2 * (κ⁻¹ * euclideanSq q)) ≤
    m ^ 2 * (((α x).mulVec p) ⬝ᵥ (p + (2 * u) • q)) at hscaled
  convert hscaled using 1 <;> ring

/-- Ellipticity of both the matrix and density converts the phase-gradient
cost to a multiple of the weighted value squared. -/
theorem c12_davies_double_weight_density_bound {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hκ : 0 < κ) (h : IsUniformlyElliptic κ ρ α)
    (x p q : Vec d) (u m L : ℝ) (hq : euclideanSq q ≤ L ^ 2) :
    -(κ⁻¹ ^ 2 * L ^ 2) * ρ x * (m * u) ^ 2 ≤
      dot ((α x).mulVec p) (m ^ 2 • (p + (2 * u) • q)) := by
  have hk : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hρ : 1 ≤ κ⁻¹ * ρ x := by
    have hh := mul_le_mul_of_nonneg_left (h.2.2 x).1 hk
    simpa only [inv_mul_cancel₀ (ne_of_gt hκ)] using hh
  have hphase : κ⁻¹ * euclideanSq q ≤ κ⁻¹ * L ^ 2 :=
    mul_le_mul_of_nonneg_left hq hk
  have hcost : κ⁻¹ * euclideanSq q ≤ (κ⁻¹ * L ^ 2) * (κ⁻¹ * ρ x) :=
    hphase.trans (le_mul_of_one_le_right (mul_nonneg hk (sq_nonneg L)) hρ)
  have hscaled := neg_le_neg (mul_le_mul_of_nonneg_right hcost (sq_nonneg (m * u)))
  calc
    _ ≤ -(κ⁻¹ * euclideanSq q) * (m * u) ^ 2 := by
      convert hscaled using 1 <;> ring
    _ ≤ _ := c12_davies_double_weight_form_bound hκ h x p q u m

/-- The gradient part of the native Dirichlet form is integrable for any
pair of native Dirichlet functions. -/
theorem c12_dirichlet_gradient_form_integrable {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u v : DirichletHilbertSpace (d := d) R hR) :
    Integrable (fun x => dot ((α x).mulVec (fun i => u.val (some i) x))
      (fun i => v.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
  have h1 := DimensionLift.dirichletHilbert_scaled_form_integrable hκ h R hR 1 u v
  have h0 := DimensionLift.dirichletHilbert_scaled_form_integrable hκ h R hR 0 u v
  apply (h1.sub h0).congr
  filter_upwards [] with x
  simp only [Pi.sub_apply, one_mul, zero_mul, add_zero]
  ring

#print axioms c12_dirichlet_gradient_form_integrable

/-- The density-weighted square of a native Dirichlet value is integrable
on the source ball. -/
theorem c12_dirichlet_value_square_integrable {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    Integrable (fun x => ρ x * (u.val none x) ^ 2)
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
  have hi := DimensionLift.dirichletHilbert_scaled_form_integrable hκ h R hR 0 u u
  convert hi using 1 <;> simp [pow_two, mul_assoc]

#print axioms c12_dirichlet_value_square_integrable

/-- Integrating the pointwise Davies estimate gives the corresponding lower
bound for the native form, once both sides are integrable. -/
theorem c12_davies_integrated_double_weight_bound {d : ℕ} {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hκ : 0 < κ) (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (p q : Vec d → Vec d) (u m : Vec d → ℝ) (L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (q x) ≤ L ^ 2)
    (hcost : Integrable (fun x => ρ x * (m x * u x) ^ 2)
      (volume.restrict (sourceBall (0 : Vec d) R)))
    (hform : Integrable (fun x => dot ((α x).mulVec (p x))
      (m x ^ 2 • (p x + (2 * u x) • q x)))
      (volume.restrict (sourceBall (0 : Vec d) R))) :
    -(κ⁻¹ ^ 2 * L ^ 2) * (∫ x in sourceBall (0 : Vec d) R,
      ρ x * (m x * u x) ^ 2) ≤
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (p x)) (m x ^ 2 • (p x + (2 * u x) • q x)) := by
  rw [← integral_const_mul]
  apply integral_mono_ae (hcost.const_mul _) hform
  filter_upwards [hq] with x hx
  simpa only [mul_assoc] using
    c12_davies_double_weight_density_bound hκ h x (p x) (q x) (u x) (m x) L hx

#print axioms c12_davies_integrated_double_weight_bound

#print axioms c12_davies_double_weight_density_bound

#print axioms c12_davies_double_weight_form_bound

/-- A bounded linear operation preserving smooth zero-boundary data also
preserves the actual completed Dirichlet space. -/
theorem c12_dirichlet_closure_preserved {d : ℕ} (R : ℝ) (hR : 0 < R)
    (M : HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR)) →L[ℝ]
      HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)))
    (hM : ∀ φ, M (dirichletSmoothData (d := d) R hR φ) ∈ dirichletHilbertSubmodule (d := d) R hR)
    (u : DirichletHilbertSpace (d := d) R hR) :
    M u.val ∈ dirichletHilbertSubmodule (d := d) R hR := by
  let S := dirichletHilbertSubmodule (d := d) R hR
  have hc : IsClosed (M ⁻¹' (S : Set (HilbertSobolevData
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))))) :=
    (isClosed_dirichletHilbertSubmodule (d := d) R hR).preimage M.continuous
  have hr : LinearMap.range (dirichletSmoothData (d := d) R hR) ≤ S.comap M.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    exact hM φ
  exact (Submodule.topologicalClosure_minimal _ hr hc) u.property

private theorem c12_l2_multiplier {Ω : Type*} [MeasurableSpace Ω]
    [TopologicalSpace Ω] [BorelSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ) (hm : Continuous m)
    {C : ℝ} (hC : 0 ≤ C) (hbμ : ∀ᵐ ω ∂μ, |m ω| ≤ C) :
    ∃ T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, ‖T‖ ≤ C ∧
      ∀ f, (T f : Ω → ℝ) =ᵐ[μ] fun ω => m ω * f ω := by
  have hmμ := hm.aestronglyMeasurable (μ := μ)
  have h_mem (f : Lp ℝ 2 μ) : MemLp (fun ω => m ω * f ω) 2 μ :=
    (Lp.memLp f).of_le_mul
      (hmμ.mul (Lp.aestronglyMeasurable f))
      (by
        filter_upwards [hbμ] with ω hω
        simp_rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
  let T_lin : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun f => (h_mem f).toLp (fun ω => m ω * f ω)
      map_add' := fun f g => by
        apply Lp.ext
        have h1 := MemLp.coeFn_toLp (h_mem (f + g))
        have h2 := MemLp.coeFn_toLp (h_mem f)
        have h3 := MemLp.coeFn_toLp (h_mem g)
        have h_add := Lp.coeFn_add ((h_mem f).toLp (fun ω => m ω * f ω))
                                     ((h_mem g).toLp (fun ω => m ω * g ω))
        have h_pointwise : (fun ω => m ω * (f + g) ω) =ᵐ[μ]
            (fun ω => m ω * f ω) + (fun ω => m ω * g ω) := by
          filter_upwards [Lp.coeFn_add f g] with ω hω
          rw [hω]
          simp [Pi.add_apply, mul_add]
        exact h1.trans (h_pointwise.trans ((h2.add h3).symm.trans h_add.symm))
      map_smul' := fun r f => by
        apply Lp.ext
        have h1 := MemLp.coeFn_toLp (h_mem (r • f))
        have h2 := MemLp.coeFn_toLp (h_mem f)
        have h_smul := Lp.coeFn_smul r ((h_mem f).toLp (fun ω => m ω * f ω))
        have h_pointwise : (fun ω => m ω * (r • f) ω) =ᵐ[μ]
            r • (fun ω => m ω * f ω) := by
          filter_upwards [Lp.coeFn_smul r f] with ω hω
          rw [hω]
          simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]
        exact h1.trans (h_pointwise.trans ((h2.const_smul r).symm.trans h_smul.symm)) }
  have h_bound : ∀ f : Lp ℝ 2 μ, ‖T_lin f‖ ≤ C * ‖f‖ := by
    intro f
    have hT_eq : T_lin f = (h_mem f).toLp (fun ω => m ω * f ω) := rfl
    rw [hT_eq]
    rw [Lp.norm_toLp]
    have h_enorm : eLpNorm (fun ω => m ω * f ω) 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 μ :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul (h_mem f).aestronglyMeasurable
        (by
          filter_upwards [hbμ] with ω hω
          simp_rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
        2
    have h_fin1 : eLpNorm (fun ω => m ω * f ω) 2 μ ≠ ∞ :=
      (h_mem f).eLpNorm_ne_top
    have h_fin2 : eLpNorm f 2 μ ≠ ∞ :=
      (Lp.memLp f).eLpNorm_ne_top
    calc
      ENNReal.toReal (eLpNorm (fun ω => m ω * f ω) 2 μ) ≤
          ENNReal.toReal (ENNReal.ofReal C * eLpNorm f 2 μ) :=
        ((ENNReal.toReal_le_toReal h_fin1 (by finiteness)).mpr h_enorm)
      _ = ENNReal.toReal (ENNReal.ofReal C) * ENNReal.toReal (eLpNorm f 2 μ) := by
        rw [ENNReal.toReal_mul]
      _ = C * ENNReal.toReal (eLpNorm f 2 μ) := by
        rw [ENNReal.toReal_ofReal hC]
      _ = C * ‖f‖ := by rw [Lp.norm_def]
  refine ⟨LinearMap.mkContinuous T_lin C h_bound, ?_, ?_⟩
  · -- The operator norm bound follows from `h_bound`.
    exact LinearMap.mkContinuous_norm_le _ hC h_bound
  · -- The almost-everywhere equality.
    intro f
    have hT_eq : (LinearMap.mkContinuous T_lin C h_bound) f = (h_mem f).toLp (fun ω => m ω * f ω) := rfl
    rw [hT_eq]
    simp [MemLp.coeFn_toLp (h_mem f)]


/-- Bounded smooth coefficients act continuously on the native value-gradient
carrier with the product-rule form. -/
theorem c12_graph_multiplier {d : ℕ} (Ω : Opens (SpatialCoordinates d))
    (m : SpatialCoordinates d → ℝ) (g : Fin d → SpatialCoordinates d → ℝ)
    (hm : Continuous m) (hg : ∀ i, Continuous (g i))
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x ∈ (Ω : Set _), |m x| ≤ C)
    (hgb : ∀ i, ∀ x ∈ (Ω : Set _), |g i x| ≤ C) :
    ∃ M : HilbertSobolevData Ω →L[ℝ] HilbertSobolevData Ω,
      (∀ u, (M u none : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
        fun x => m x * u none x) ∧
      (∀ u i, (M u (some i) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (Ω : Set _)]
        fun x => m x * u (some i) x + g i x * u none x) := by
  let μ := volume.restrict (Ω : Set (SpatialCoordinates d))
  have hΩ : ∀ᵐ x ∂μ, x ∈ (Ω : Set _) := ae_restrict_mem Ω.2.measurableSet
  have hbm : ∀ᵐ x ∂μ, |m x| ≤ C := hΩ.mono hb
  obtain ⟨T, _, hT⟩ := c12_l2_multiplier μ m hm hC hbm
  have hgi (i : Fin d) := c12_l2_multiplier μ (g i) (hg i) hC (hΩ.mono (hgb i))
  choose U hU using hgi
  let E := (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Option (Fin d) => DomainL2 Ω))
  let P (j : Option (Fin d)) : HilbertSobolevData Ω →L[ℝ] DomainL2 Ω :=
    (ContinuousLinearMap.proj j).comp E.toContinuousLinearMap
  let V : HilbertSobolevData Ω →L[ℝ] (Option (Fin d) → DomainL2 Ω) :=
    ContinuousLinearMap.pi (fun j => match j with
      | none => T.comp (P none)
      | some i => T.comp (P (some i)) + (U i).comp (P none))
  let M : HilbertSobolevData Ω →L[ℝ] HilbertSobolevData Ω :=
    E.symm.toContinuousLinearMap.comp V
  refine ⟨M, ?_, ?_⟩
  · intro u
    exact hT (u none)
  · intro u i
    have he := Lp.coeFn_add (T (u (some i))) (U i (u none))
    filter_upwards [he, hT (u (some i)), (hU i).2 (u none)] with x hx ht hu
    change (T (u (some i)) + U i (u none)) x = _
    rw [hx]
    simp only [Pi.add_apply]
    rw [ht, hu]

/-- Smooth bounded weights preserve the completed native Dirichlet graph. -/
theorem c12_smooth_multiplier_preserves_dirichlet {d : ℕ}
    (R : ℝ) (hR : 0 < R) (m : SpatialCoordinates d → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (C : ℝ) (hC : 0 ≤ C)
    (hb : ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR) : Set _), |m x| ≤ C)
    (hgb : ∀ i, ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR) : Set _), |fderiv ℝ m x (Pi.single i 1)| ≤ C) :
    ∃ M : HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) →L[ℝ] HilbertSobolevData
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)),
      (∀ u, (M u none : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => m x * u none x) ∧
      (∀ u i, (M u (some i) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => m x * u (some i) x + fderiv ℝ m x (Pi.single i 1) * u none x) ∧
      (∀ u : DirichletHilbertSpace (d := d) R hR,
        M u.val ∈ dirichletHilbertSubmodule (d := d) R hR) := by
  classical
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let g (i : Fin d) (x : SpatialCoordinates d) := fderiv ℝ m x (Pi.single i 1)
  have hg (i : Fin d) : Continuous (g i) := by
    exact (hm.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk continuous_const)
  obtain ⟨M, hM0, hM1⟩ := c12_graph_multiplier Q m g hm.continuous hg C hC hb hgb
  refine ⟨M, hM0, hM1, ?_⟩
  intro u
  apply c12_dirichlet_closure_preserved R hR M
  intro φ
  let ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
    ⟨fun x => m x * φ x, hm.mul φ.contDiff,
      φ.hasCompactSupport.mul_left, tsupport_mul_subset_right.trans φ.tsupport_subset⟩
  have heq : M (dirichletSmoothData R hR φ) = dirichletSmoothData R hR ψ := by
    apply PiLp.ext
    intro j
    cases j with
    | none =>
      apply Lp.ext
      filter_upwards [hM0 (dirichletSmoothData R hR φ),
        testL2_coeFn (dirichletTestInCube R hR φ),
        testL2_coeFn (dirichletTestInCube R hR ψ)] with x h1 h2 h3
      change (M (dirichletSmoothData R hR φ) none) x =
        (testL2 (dirichletTestInCube R hR ψ)) x
      rw [h1]
      change m x * (testL2 (dirichletTestInCube R hR φ)) x =
        (testL2 (dirichletTestInCube R hR ψ)) x
      rw [h2, h3]
      rfl
    | some i =>
      apply Lp.ext
      filter_upwards [hM1 (dirichletSmoothData R hR φ) i,
        testPartialL2_coeFn (dirichletTestInCube R hR φ) i,
        testL2_coeFn (dirichletTestInCube R hR φ),
        testPartialL2_coeFn (dirichletTestInCube R hR ψ) i] with x h1 h2 h3 h4
      change (M (dirichletSmoothData R hR φ) (some i)) x =
        (testPartialL2 (dirichletTestInCube R hR ψ) i) x
      rw [h1]
      change m x * (testPartialL2 (dirichletTestInCube R hR φ) i) x +
        g i x * (testL2 (dirichletTestInCube R hR φ)) x =
          (testPartialL2 (dirichletTestInCube R hR ψ) i) x
      rw [h2, h3, h4]
      change m x * fderiv ℝ φ x (Pi.single i 1) +
        fderiv ℝ m x (Pi.single i 1) * φ x =
          fderiv ℝ (m * (φ : SpatialCoordinates d → ℝ)) x (Pi.single i 1)
      rw [fderiv_mul (hm.differentiable (by simp) x)
        (φ.contDiff.differentiable (by simp) x)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
  rw [heq]
  exact (LinearMap.range (dirichletSmoothData R hR)).le_topologicalClosure ⟨ψ, rfl⟩

/-- Smooth weights and their coordinate derivatives are uniformly bounded on
 the containing cube, including when the spatial dimension is zero. -/
theorem c12_smooth_weight_cube_bounds {d : ℕ} (R : ℝ) (hR : 0 < R)
    (m : SpatialCoordinates d → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ x ∈ (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR) : Set _), |m x| ≤ C) ∧
      (∀ i, ∀ x ∈ (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR) : Set _), |fderiv ℝ m x (Pi.single i 1)| ≤ C) := by
  classical
  let Q : Set (SpatialCoordinates d) :=
    (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)
  have hc : IsCompact (closure Q) :=
    (centeredCube_isBounded (0 : SpatialCoordinates d) (mul_pos two_pos hR)).isCompact_closure
  have hb : ∀ f : SpatialCoordinates d → ℝ, Continuous f →
      ∃ B : ℝ, ∀ x ∈ Q, |f x| ≤ B := by
    intro f hf
    obtain ⟨B, hB⟩ := bddAbove_def.mp (hc.bddAbove_image hf.norm.continuousOn)
    exact ⟨B, fun x hx => by
      simpa only [Real.norm_eq_abs] using hB _ ⟨x, subset_closure hx, rfl⟩⟩
  obtain ⟨B, hB⟩ := hb m hm.continuous
  have hderiv (i : Fin d) : Continuous (fun x => fderiv ℝ m x (Pi.single i 1)) :=
    (hm.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hex (i : Fin d) := hb (fun x => fderiv ℝ m x (Pi.single i 1)) (hderiv i)
  choose D hD using hex
  let C := |B| + ∑ i : Fin d, |D i|
  have hsum : 0 ≤ ∑ i : Fin d, |D i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C, add_nonneg (abs_nonneg _) hsum, ?_, ?_⟩
  · intro x hx
    calc
      |m x| ≤ B := hB x hx
      _ ≤ |B| := le_abs_self B
      _ ≤ C := le_add_of_nonneg_right hsum
  · intro i x hx
    have hi : |D i| ≤ ∑ j : Fin d, |D j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (D j)) (Finset.mem_univ i)
    calc
      |fderiv ℝ m x (Pi.single i 1)| ≤ D i := hD i x hx
      _ ≤ |D i| := le_abs_self _
      _ ≤ ∑ j : Fin d, |D j| := hi
      _ ≤ C := le_add_of_nonneg_left (abs_nonneg B)

/-- Exponentiating a smooth phase gives a native Dirichlet multiplier with
 the exact coordinate gradient needed for conjugated energy estimates. -/
theorem c12_exponential_multiplier_preserves_dirichlet {d : ℕ}
    (R : ℝ) (hR : 0 < R) (φ : SpatialCoordinates d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ M : HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) →L[ℝ] HilbertSobolevData
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)),
      (∀ u, (M u none : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp (lam * φ x) * u none x) ∧
      (∀ u i, (M u (some i) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp (lam * φ x) * u (some i) x +
          (Real.exp (lam * φ x) * (lam * fderiv ℝ φ x (Pi.single i 1))) * u none x) ∧
      (∀ u : DirichletHilbertSpace (d := d) R hR,
        M u.val ∈ dirichletHilbertSubmodule (d := d) R hR) := by
  let m (x : SpatialCoordinates d) := Real.exp (lam * φ x)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := (contDiff_const.mul hφ).exp
  obtain ⟨C, hC, hb, hgb⟩ := c12_smooth_weight_cube_bounds R hR m hm
  obtain ⟨M, hM0, hM1, hMdir⟩ :=
    c12_smooth_multiplier_preserves_dirichlet R hR m hm C hC hb hgb
  refine ⟨M, hM0, ?_, hMdir⟩
  intro u i
  filter_upwards [hM1 u i] with x hx
  have hd : fderiv ℝ m x (Pi.single i 1) =
      Real.exp (lam * φ x) * (lam * fderiv ℝ φ x (Pi.single i 1)) := by
    dsimp only [m]
    rw [fderiv_exp ((hφ.differentiable (by simp) x).const_mul lam),
      fderiv_const_mul (hφ.differentiable (by simp) x) lam]
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  simpa only [m, hd] using hx

/-- A smooth exponential phase also acts boundedly on the actual weighted
Dirichlet L² space. The bound uses only the bounded spatial domain. -/
theorem c12_exponential_weighted_l2_multiplier {d : ℕ}
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      ∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x := by
  let m (x : SpatialCoordinates d) := Real.exp (lam * φ x)
  have hm : ContDiff ℝ (⊤ : ℕ∞) m := (contDiff_const.mul hφ).exp
  obtain ⟨C, hC, hb, _⟩ := c12_smooth_weight_cube_bounds R hR m hm
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R := by
    apply (withDensity_absolutelyContinuous _ _).ae_le
    exact ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet
  have hbound : ∀ᵐ x ∂dirichletVolume ρ R, |m x| ≤ C :=
    hball.mono (fun x hx => hb x (sourceBall_subset_cube R hR hx))
  obtain ⟨T, _, hT⟩ := c12_l2_multiplier (dirichletVolume ρ R) m hm.continuous hC hbound
  exact ⟨T, hT⟩

/-- The weighted L² pairing of two once-weighted functions equals pairing
against the twice-weighted test function. -/
theorem c12_exponential_weighted_l2_pairing {d : ℕ}
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ T S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      (∀ f, (S f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp ((2 * lam) * φ x) * f x) ∧
      ∀ f g, inner ℝ (T f) (T g) = inner ℝ f (S g) := by
  obtain ⟨T, hT⟩ := c12_exponential_weighted_l2_multiplier ρ R hR φ hφ lam
  obtain ⟨S, hS⟩ := c12_exponential_weighted_l2_multiplier ρ R hR φ hφ (2 * lam)
  refine ⟨T, S, hT, hS, ?_⟩
  intro f g
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hT f, hT g, hS g] with x hf hg hs
  simp only [RCLike.inner_apply, conj_trivial, hf, hg, hs]
  rw [show (2 * lam) * φ x = lam * φ x + lam * φ x by ring, Real.exp_add]
  ring

#print axioms c12_exponential_weighted_l2_pairing

/-- The graph multiplier commutes with the actual inclusion into weighted
L². In particular, the weighted value remains a native Dirichlet test. -/
theorem c12_exponential_inclusion_commutes {d : ℕ}
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ (M : HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) →L[ℝ] HilbertSobolevData
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)))
      (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R))
      (hdir : ∀ u : DirichletHilbertSpace (d := d) R hR,
        M u.val ∈ dirichletHilbertSubmodule (d := d) R hR),
      (∀ u, (M u none : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp (lam * φ x) * u none x) ∧
      (∀ u i, (M u (some i) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp (lam * φ x) * u (some i) x +
          (Real.exp (lam * φ x) * (lam * fderiv ℝ φ x (Pi.single i 1))) * u none x) ∧
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      ∀ u : DirichletHilbertSpace (d := d) R hR,
        dirichletHilbertInclusion ρ R hR C hρ ⟨M u.val, hdir u⟩ =
          T (dirichletHilbertInclusion ρ R hR C hρ u) := by
  obtain ⟨M, hM0, hM1, hdir⟩ := c12_exponential_multiplier_preserves_dirichlet R hR φ hφ lam
  obtain ⟨T, hT⟩ := c12_exponential_weighted_l2_multiplier ρ R hR φ hφ lam
  refine ⟨M, T, hdir, hM0, hM1, hT, ?_⟩
  intro u
  apply Lp.ext
  have hac := (Measure.absolutelyContinuous_of_le_smul
    (dirichletVolume_le_cube ρ R hR C hρ)).ae_le
  have hM0' := (hM0 u.val).filter_mono hac
  have hJ1 := dirichletHilbertInclusion_coe ρ R hR C hρ ⟨M u.val, hdir u⟩
  have hJ0 := dirichletHilbertInclusion_coe ρ R hR C hρ u
  filter_upwards [hM0', hJ1, hJ0, hT (dirichletHilbertInclusion ρ R hR C hρ u)] with x hm hj1 hj0 ht
  change (dirichletHilbertInclusion ρ R hR C hρ ⟨M u.val, hdir u⟩) x = _
  change (dirichletHilbertInclusion ρ R hR C hρ ⟨M u.val, hdir u⟩) x = (M u.val none) x at hj1
  change (dirichletHilbertInclusion ρ R hR C hρ u) x = (u.val none) x at hj0
  rw [hj1, hm, ht, hj0]

#print axioms c12_exponential_inclusion_commutes

/-- The chain rule for the squared norm after applying a bounded weight.
The pairing identity is supplied by the native Dirichlet weak equation. -/
theorem c12_weighted_norm_sq_hasDerivAt
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (u : ℝ → H) (u' : H) (t q : ℝ)
    (hu : HasDerivAt u u' t)
    (hpair : inner ℝ (T (u t)) (T u') = -q) :
    HasDerivAt (fun s => ‖T (u s)‖ ^ 2) (-2 * q) t := by
  have hd := (T.hasFDerivAt.comp_hasDerivAt t hu).norm_sq
  simpa only [Function.comp_apply, hpair, mul_neg, neg_mul] using hd

/-- A fixed-test weak evolution identity gives the derivative of the weighted
energy when the double weight of the current state is that test. -/
theorem c12_weighted_energy_of_weak_test
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T S : H →L[ℝ] H) (u : ℝ → H) (u' w : H) (t q : ℝ)
    (hu : HasDerivAt u u' t)
    (hpair : ∀ f g, inner ℝ (T f) (T g) = inner ℝ f (S g))
    (hw : S (u t) = w)
    (hweak : HasDerivAt (fun s => inner ℝ (u s) w) (-q) t) :
    HasDerivAt (fun s => ‖T (u s)‖ ^ 2) (-2 * q) t := by
  have hd := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hu
  change HasDerivAt (fun s : ℝ => inner ℝ w (u s)) (inner ℝ w u') t at hd
  have hd' : HasDerivAt (fun s => inner ℝ (u s) w) (inner ℝ u' w) t := by
    simpa only [real_inner_comm] using hd
  have hi : inner ℝ u' w = -q := hd'.unique hweak
  apply c12_weighted_norm_sq_hasDerivAt T u u' t q hu
  rw [real_inner_comm, hpair, hw, hi]

/-- The native double-weight test has the Davies lower bound, with its
cost expressed as the weighted L² norm. -/
theorem c12_native_double_weight_form_bound {d : ℕ}
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
      -(κ⁻¹ ^ 2 * L ^ 2) * ‖dirichletHilbertInclusion ρ R hR κ⁻¹
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
  have hcost := c12_dirichlet_value_square_integrable hκ h R hR v
  have hform := c12_dirichlet_gradient_form_integrable hκ h R hR u w
  have hpoint : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      -(κ⁻¹ ^ 2 * L ^ 2) * (ρ x * (v.val none x) ^ 2) ≤
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
    have hb := c12_davies_double_weight_density_bound hκ h x
      (fun i => u.val (some i) x)
      (fun i => lam * fderiv ℝ φ x (Pi.single i 1))
      (u.val none x) (Real.exp (lam * φ x)) L hqx
    change (M u.val none) x = _ at hvx
    rw [hvx]
    convert hb using 1 <;> ring
  have hint := integral_mono_ae (hcost.const_mul (-(κ⁻¹ ^ 2 * L ^ 2))) hform hpoint
  rw [integral_const_mul] at hint
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

#print axioms c12_native_double_weight_form_bound

/-- The actual spectral heat flow has the double-weight Dirichlet form as
its weighted-energy derivative at every positive time. -/
theorem c12_spectral_heat_weighted_energy_derivative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam : ℝ) :
    ∃ (M : HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) →L[ℝ] HilbertSobolevData
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)))
      (T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R))
      (hdir : ∀ v : DirichletHilbertSpace (d := d) R hR,
        M v.val ∈ dirichletHilbertSubmodule (d := d) R hR)
      (Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR),
      (∀ v, (M v none : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp ((2 * lam) * φ x) * v none x) ∧
      (∀ v i, (M v (some i) : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict
          (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) : Set _)]
        fun x => Real.exp ((2 * lam) * φ x) * v (some i) x +
          (Real.exp ((2 * lam) * φ x) * ((2 * lam) * fderiv ℝ φ x (Pi.single i 1))) * v none x) ∧
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      (∀ (t : ℝ≥0) (ht : 0 < t),
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)).comp (Q t ht) =
          SpectralHeat.heatOperator
            (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t) ∧
      ∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        HasDerivAt (fun r : ℝ => ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)‖ ^ 2)
          (-2 * (∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => (M (Q t ht f).val) (some i) x))) (t : ℝ) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨M, U, hdir, hM0, hM1, hU, hcomm⟩ :=
    c12_exponential_inclusion_commutes ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) φ hφ (2 * lam)
  obtain ⟨T, S, hT, hS, hpair⟩ := c12_exponential_weighted_l2_pairing ρ R hR φ hφ lam
  have hSU : S = U := by
    apply ContinuousLinearMap.ext
    intro f
    apply Lp.ext
    exact (hS f).trans (hU f).symm
  obtain ⟨Q, _, hQ⟩ :=
    EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectral_heat_native_weakFlow
      hd hκ h R hR s u hb hvar
  refine ⟨M, T, hdir, Q, hM0, hM1, hT, (fun t ht => (hQ t ht).1), ?_⟩
  intro t ht f
  let v : DirichletHilbertSpace (d := d) R hR := ⟨M (Q t ht f).val, hdir (Q t ht f)⟩
  have hfactor : J (Q t ht f) = SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t f := by
    exact congrArg (fun L : _ →L[ℝ] _ => L f) (hQ t ht).1
  have hw : S (SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) ((t : ℝ).toNNReal) f) = J v := by
    rw [Real.toNNReal_coe, ← hfactor, hSU]
    exact (hcomm (Q t ht f)).symm
  have hd := SpectralHeat.heatOperator_hasDerivAt
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    s.eigenvalue_pos t ht f
  exact c12_weighted_energy_of_weak_test T S _ _ (J v) (t : ℝ) _ hd hpair hw
    ((hQ t ht).2.2 f v)

/-- The native spectral heat energy satisfies the Davies differential
inequality for every smooth phase of bounded logarithmic gradient. -/
theorem c12_spectral_heat_weighted_energy_inequality {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      ∀ (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ∃ e : ℝ, HasDerivAt (fun r : ℝ => ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)‖ ^ 2) e (t : ℝ) ∧
          e ≤ (2 * (κ⁻¹ ^ 2 * L ^ 2)) * ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f)‖ ^ 2 := by
  obtain ⟨M, T, hdir, Q, _, hM1, hT, hQ, hderiv⟩ :=
    c12_spectral_heat_weighted_energy_derivative hd hκ h R hR s u hb hvar φ hφ lam
  refine ⟨T, hT, ?_⟩
  intro t ht f
  let z := Q t ht f
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨v, w, hv, hw, hbound⟩ := c12_native_double_weight_form_bound hκ h R hR φ hφ lam L hq z
  have hJz := dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) z
  have hvT : J v = T (J z) := by
    apply Lp.ext
    filter_upwards [hv, hT (J z), hJz] with x hvx htx hzx
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

/-- A continuous energy whose positive-time derivative is at most a multiple
of the energy satisfies the corresponding exponential estimate from time zero. -/
theorem c12_energy_gronwall (E : ℝ → ℝ) (a : ℝ)
    (hE : Continuous E)
    (hderiv : ∀ t : ℝ, 0 < t → ∃ e, HasDerivAt E e t ∧ e ≤ a * E t)
    (t : ℝ) (ht : 0 ≤ t) :
    E t ≤ Real.exp (a * t) * E 0 := by
  let F : ℝ → ℝ := fun x => Real.exp (-a * x) * E x
  have hF : Continuous F := (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hE
  have hdiff : ∀ x ∈ interior (Set.Ici (0 : ℝ)), DifferentiableAt ℝ F x := by
    intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    obtain ⟨e, he, _⟩ := hderiv x hx'
    exact ((((hasDerivAt_id x).const_mul (-a)).exp).mul he).differentiableAt
  have hnonpos : ∀ x ∈ interior (Set.Ici (0 : ℝ)), deriv F x ≤ 0 := by
    intro x hx
    have hx' : 0 < x := by simpa only [interior_Ici, Set.mem_Ioi] using hx
    obtain ⟨e, he, heb⟩ := hderiv x hx'
    have hd := (((hasDerivAt_id x).const_mul (-a)).exp).mul he
    change HasDerivAt F _ x at hd
    have hid : deriv F x = Real.exp (-a * x) * (e - a * E x) := by
      rw [hd.deriv]
      simp only [id_eq]
      ring
    rw [hid]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (sub_nonpos.mpr heb)
  have hant : AntitoneOn F (Set.Ici (0 : ℝ)) :=
    antitoneOn_of_deriv_nonpos (convex_Ici 0) hF.continuousOn
      (fun x hx => (hdiff x hx).differentiableWithinAt) hnonpos
  have hh := hant (show (0 : ℝ) ∈ Set.Ici 0 from Set.mem_Ici.mpr le_rfl) (show t ∈ Set.Ici 0 from Set.mem_Ici.mpr ht) ht
  change Real.exp (-a * t) * E t ≤ Real.exp (-a * 0) * E 0 at hh
  simp only [mul_zero, Real.exp_zero, one_mul] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (a * t)).le
  have hexp : Real.exp (a * t) * Real.exp (-a * t) = 1 := by
    rw [← Real.exp_add]
    simp
  calc
    E t = Real.exp (a * t) * (Real.exp (-a * t) * E t) := by rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (a * t) * E 0 := hh'

#print axioms c12_energy_gronwall

/-- The spectral flow obeys the exponential Davies bound for each smooth
phase, starting from its actual weighted initial value. -/
theorem c12_spectral_heat_weighted_energy_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f)‖ ^ 2 ≤
        Real.exp ((2 * (κ⁻¹ ^ 2 * L ^ 2)) * (t : ℝ)) * ‖T f‖ ^ 2 := by
  obtain ⟨T, hT, hineq⟩ :=
    c12_spectral_heat_weighted_energy_inequality hd hκ h R hR s u hb hvar φ hφ lam L hq
  refine ⟨T, hT, ?_⟩
  intro t f
  let E : ℝ → ℝ := fun r => ‖T (SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) r.toNNReal f)‖ ^ 2
  have hE : Continuous E := by
    exact ((T.continuous.comp ((SpectralHeat.heatOperator_continuous
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) f).comp continuous_real_toNNReal)).norm).pow 2
  have hEderiv : ∀ r : ℝ, 0 < r → ∃ e, HasDerivAt E e r ∧
      e ≤ (2 * (κ⁻¹ ^ 2 * L ^ 2)) * E r := by
    intro r hr
    have hr' : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr
    obtain ⟨e, he, hb⟩ := hineq r.toNNReal hr' f
    rw [Real.toNNReal_of_nonneg hr.le] at he
    refine ⟨e, he, ?_⟩
    exact hb
  have hh := c12_energy_gronwall E (2 * (κ⁻¹ ^ 2 * L ^ 2)) hE hEderiv t t.property
  simpa only [E, Real.toNNReal_coe, Real.toNNReal_zero, SpectralHeat.heatOperator_zero,
    ContinuousLinearMap.id_apply] using hh

#print axioms c12_spectral_heat_weighted_energy_bound

/-- The weighted energy bound applies to the supplied kernel's own spectral
resolution, using its native Dirichlet eigenfunction lifts. -/
theorem c12_supplied_spectral_heat_weighted_energy_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (lam L : ℝ)
    (hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ L ^ 2) :
    ∃ T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      (∀ f, (T f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun x => Real.exp (lam * φ x) * f x) ∧
      ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ‖T (SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f)‖ ^ 2 ≤
        Real.exp ((2 * (κ⁻¹ ^ 2 * L ^ 2)) * (t : ℝ)) * ‖T f‖ ^ 2 := by
  classical
  choose u hu hv using fun n => c16_supplied_eigenfunction_dirichletEquation hd hκ hR h s n
  have hb : ∀ n, EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    intro n
    rw [show EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s n =
      (s.square_integrable n).toLp (s.eigenfunction n) from
        congrFun (HilbertBasis.coe_mk s.orthonormal
          (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  exact c12_spectral_heat_weighted_energy_bound hd hκ h R hR s u hb hv φ hφ lam L hq

#print axioms c12_supplied_spectral_heat_weighted_energy_bound

/-- Multiplying an L² function supported where the phase is bounded above
costs at most the corresponding exponential factor. -/
theorem c12_phase_multiplier_norm_upper {d : ℕ} {μ : Measure (Vec d)}
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (φ : Vec d → ℝ) (lam b : ℝ)
    (hlam : 0 ≤ lam)
    (hT : ∀ f, (T f : Vec d → ℝ) =ᵐ[μ] fun x => Real.exp (lam * φ x) * f x)
    (B : Set (Vec d)) (hφ : ∀ x ∈ B, φ x ≤ b)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, x ∉ B → f x = 0) :
    ‖T f‖ ≤ Real.exp (lam * b) * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT f, hf] with x hx hfx
  rw [hx, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  by_cases hxB : x ∈ B
  · exact mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hφ x hxB) hlam)) (norm_nonneg _)
  · rw [hfx hxB, norm_zero, mul_zero, mul_zero]

/-- A lower phase bound controls a restricted L² output by the weighted
full output. -/
theorem c12_phase_multiplier_norm_lower {d : ℕ} {μ : Measure (Vec d)}
    (T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (φ : Vec d → ℝ) (lam a : ℝ)
    (hlam : 0 ≤ lam)
    (hT : ∀ f, (T f : Vec d → ℝ) =ᵐ[μ] fun x => Real.exp (lam * φ x) * f x)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hφ : ∀ x ∈ A, a ≤ φ x)
    (g : Lp ℝ 2 μ) :
    ‖((Lp.memLp g).indicator hA).toLp (A.indicator fun x => g x)‖ ≤
      Real.exp (-lam * a) * ‖T g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hT g, ((Lp.memLp g).indicator hA).coeFn_toLp] with x hx hi
  rw [hi, hx]
  by_cases hxA : x ∈ A
  · rw [Set.indicator_of_mem hxA, norm_mul]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : (1 : ℝ) ≤ Real.exp (-lam * a) * Real.exp (lam * φ x) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left (hφ x hxA) hlam]
    have hm := mul_le_mul_of_nonneg_right he (abs_nonneg (g x))
    nlinarith
  · simp only [Set.indicator_of_notMem hxA, norm_zero]
    positivity

#print axioms c12_phase_multiplier_norm_upper
#print axioms c12_phase_multiplier_norm_lower

/-- The supplied spectral heat flow has a separated-set L² bound before
optimizing the exponential parameter. -/
theorem c12_supplied_spectral_heat_separated_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : B.Nonempty)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (lam : ℝ) (hlam : 0 ≤ lam) (t : ℝ≥0)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0) :
    ‖((Lp.memLp (SpectralHeat.heatOperator
        (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t f)).indicator hA).toLp
        (A.indicator fun x => SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x)‖ ^ 2 ≤
      Real.exp (-lam * δ + 2 * (κ⁻¹ ^ 2 * lam ^ 2) * (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨φ, hφ, hgrad, hφA, hφB⟩ := c12_smooth_separating_phase A B hB δ hδ hsep
  have hq : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      euclideanSq (fun i => lam * fderiv ℝ φ x (Pi.single i 1)) ≤ lam ^ 2 :=
    Filter.Eventually.of_forall (c12_unit_gradient_weight_bound φ hgrad lam)
  obtain ⟨T, hT, henergy⟩ :=
    c12_supplied_spectral_heat_weighted_energy_bound hd hκ h R hR s φ hφ lam lam hq
  let g := SpectralHeat.heatOperator
    (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) t f
  have hlo := c12_phase_multiplier_norm_lower T φ lam (3 * δ / 4) hlam hT A hA hφA g
  have hup := c12_phase_multiplier_norm_upper T φ lam (δ / 4) hlam hT B hφB f hf
  have hlo2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).2 hlo
  have hup2 := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (norm_nonneg _))).2 hup
  have he := henergy t f
  change ‖T g‖ ^ 2 ≤ _ at he
  have hexp : (Real.exp (-lam * (3 * δ / 4))) ^ 2 *
      (Real.exp ((2 * (κ⁻¹ ^ 2 * lam ^ 2)) * (t : ℝ)) *
        (Real.exp (lam * (δ / 4))) ^ 2) =
      Real.exp (-lam * δ + 2 * (κ⁻¹ ^ 2 * lam ^ 2) * (t : ℝ)) := by
    have h1 : Real.exp (-lam * (3 * δ / 4)) ^ 2 =
        Real.exp (-lam * (3 * δ / 4) + -lam * (3 * δ / 4)) := by
      rw [pow_two, ← Real.exp_add]
    have h2 : Real.exp (lam * (δ / 4)) ^ 2 =
        Real.exp (lam * (δ / 4) + lam * (δ / 4)) := by
      rw [pow_two, ← Real.exp_add]
    rw [h1, h2, ← Real.exp_add, ← Real.exp_add]
    congr 1 <;> ring
  calc
    _ ≤ (Real.exp (-lam * (3 * δ / 4))) ^ 2 * ‖T g‖ ^ 2 := by
      simpa only [mul_pow] using hlo2
    _ ≤ (Real.exp (-lam * (3 * δ / 4))) ^ 2 *
        (Real.exp ((2 * (κ⁻¹ ^ 2 * lam ^ 2)) * (t : ℝ)) * ‖T f‖ ^ 2) :=
      mul_le_mul_of_nonneg_left he (sq_nonneg _)
    _ ≤ (Real.exp (-lam * (3 * δ / 4))) ^ 2 *
        (Real.exp ((2 * (κ⁻¹ ^ 2 * lam ^ 2)) * (t : ℝ)) *
          ((Real.exp (lam * (δ / 4))) ^ 2 * ‖f‖ ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa only [mul_pow] using hup2
    _ = (Real.exp (-lam * (3 * δ / 4)) ^ 2 *
        (Real.exp ((2 * (κ⁻¹ ^ 2 * lam ^ 2)) * (t : ℝ)) *
          Real.exp (lam * (δ / 4)) ^ 2)) * ‖f‖ ^ 2 := by ring
    _ = _ := by rw [hexp]

#print axioms c12_supplied_spectral_heat_separated_bound

/-- Optimizing the phase gives Gaussian decay for the supplied spectral heat
flow between separated sets. -/
theorem c12_supplied_spectral_heat_davies_gaffney {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : B.Nonempty)
    (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x - y))
    (t : ℝ≥0) (ht : 0 < t) (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0) :
    ‖((Lp.memLp (SpectralHeat.heatOperator
        (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t f)).indicator hA).toLp
        (A.indicator fun x => SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x)‖ ^ 2 ≤
      Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * (t : ℝ))) * ‖f‖ ^ 2 := by
  have ha : 0 < 2 * κ⁻¹ ^ 2 := by positivity
  have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
  obtain ⟨lam, hlam, he⟩ := c12_davies_optimize_exponent
    (2 * κ⁻¹ ^ 2) (δ / 2) (t : ℝ) ha (by positivity) ht'
  have hb := c12_supplied_spectral_heat_separated_bound hd hκ h R hR s
    A B hA hB δ hδ hsep lam hlam.le t f hf
  have he' : Real.exp (-lam * δ + 2 * (κ⁻¹ ^ 2 * lam ^ 2) * (t : ℝ)) =
      Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * (t : ℝ))) := by
    have hl : -lam * δ + 2 * (κ⁻¹ ^ 2 * lam ^ 2) * (t : ℝ) =
        -2 * lam * (δ / 2) + (2 * κ⁻¹ ^ 2) * lam ^ 2 * (t : ℝ) := by ring
    rw [hl, he]
    congr 1
    ring
  rw [he'] at hb
  exact hb

#print axioms c12_supplied_spectral_heat_davies_gaffney

/-- The squared weighted L² norm of a restricted function is its weighted
Lebesgue integral over that set. -/
theorem c12_dirichlet_restricted_norm_sq {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hAb : A ⊆ sourceBall 0 R)
    (f : Vec d → ℝ) (hf : MemLp f 2 (dirichletVolume ρ R)) :
    ‖(hf.indicator hA).toLp (A.indicator f)‖ ^ 2 =
      ∫ x in A, ρ x * f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  calc
    _ = ∫ x, (A.indicator f x) ^ 2 ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [(hf.indicator hA).coeFn_toLp] with x hx
      rw [hx]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
    _ = ∫ x in sourceBall (0 : Vec d) R,
        ρ x * (A.indicator f x) ^ 2 := by
      change (∫ x, (A.indicator f x) ^ 2 ∂(volume.restrict
        (sourceBall (0 : Vec d) R)).withDensity (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards with x
      simp only [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
    _ = ∫ x in sourceBall (0 : Vec d) R,
        A.indicator (fun x => ρ x * f x ^ 2) x := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : x ∈ A <;> simp [hx]
    _ = ∫ x in A, ρ x * f x ^ 2 := by
      rw [integral_indicator hA, Measure.restrict_restrict hA]
      rw [Set.inter_eq_left.mpr hAb]

#print axioms c12_dirichlet_restricted_norm_sq

/-- The supplied kernel acts on every weighted L² input through its own
spectral semigroup, with the source's Lebesgue-density normalization. -/
theorem c12_supplied_kernel_heat_action_L2 {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    ∃ s : DirichletSpectralResolution ρ α R,
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        (fun x => SpectralHeat.heatOperator
          (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x) =ᵐ[dirichletVolume ρ R]
        fun x => ∫ y in sourceBall (0 : Vec d) R, K t x y * f y := by
  obtain ⟨s, hs⟩ := hK.2
  have hsumm : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hs t ht x hx y hy).1
  refine ⟨s, ?_⟩
  intro t ht f
  have hB : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hxball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hB)
  filter_upwards [c16_supplied_spectral_heat_operator_ae_kernel_action
    s hsumm t ht f, hxball] with x hx hxb
  rw [hx]
  change (∫ y, (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
    s.eigenfunction n x * s.eigenfunction n y) * f y ∂(volume.restrict
      (sourceBall (0 : Vec d) R)).withDensity (fun y => ENNReal.ofReal (ρ y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hB] with y hy
  simp only [ENNReal.toReal_ofReal (hκ.le.trans (hell.2.2 y).1), smul_eq_mul,
    (hs (t : ℝ) ht x hxb y hy).2]
  ring

#print axioms c12_supplied_kernel_heat_action_L2

/-- Restricting the weighted L² input to a measurable subset restricts the
supplied kernel integral to that subset. -/
theorem c12_restricted_input_kernel_integral {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (B : Set (Vec d)) (hB : MeasurableSet B) (hBb : B ⊆ sourceBall 0 R)
    (v : Vec d → ℝ) (hv : MemLp v 2 (dirichletVolume ρ R))
    (F : Vec d → ℝ) :
    (∫ y in sourceBall (0 : Vec d) R,
      F y * ((hv.indicator hB).toLp (B.indicator v)) y) =
      ∫ y in B, F y * v y := by
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    change volume.restrict (sourceBall (0 : Vec d) R) ≪
      (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun y => ENNReal.ofReal (ρ y))
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun y => ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
  calc
    _ = ∫ y in sourceBall (0 : Vec d) R, F y * (B.indicator v y) := by
      apply integral_congr_ae
      filter_upwards [hac.ae_le ((hv.indicator hB).coeFn_toLp)] with y hy
      rw [hy]
    _ = ∫ y in sourceBall (0 : Vec d) R, B.indicator (fun y => F y * v y) y := by
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ B <;> simp [hy]
    _ = ∫ y in B, F y * v y := by
      rw [integral_indicator hB, Measure.restrict_restrict hB, Set.inter_eq_left.mpr hBb]

#print axioms c12_restricted_input_kernel_integral

/-- Native weighted Davies–Gaffney estimate for the supplied spectral kernel
in the dimensions covered by the native weak-flow construction. -/
theorem c12_native_weighted_davies_gaffney_of_two_le
    (d : ℕ) (hd : 2 ≤ d) (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (A B : Set (Vec d)), MeasurableSet A → MeasurableSet B →
      A ⊆ sourceBall 0 R → B ⊆ sourceBall 0 R →
      ∀ (δ t : ℝ), 0 < δ → 0 < t →
      (∀ x ∈ A, ∀ y ∈ B, δ ≤ euclideanNorm (x-y)) →
      ∀ (v : Vec d → ℝ), MemLp v 2 (dirichletVolume ρ R) →
      (∫ x in A, ρ x * (∫ y in B, K t x y * v y)^2) ≤
        Real.exp (-(δ^2)/((8 * κ⁻¹ ^ 2)*t)) * (∫ y in B, ρ y * (v y)^2) := by
  refine ⟨8 * κ⁻¹ ^ 2, by positivity, ?_⟩
  intro ρ α h K G hK A B hA hB hAb hBb δ t hδ ht hsep v hv
  by_cases hne : B.Nonempty
  · obtain ⟨s, hs⟩ := c12_supplied_kernel_heat_action_L2 hκ h K G hK
    let τ : ℝ≥0 := ⟨t, ht.le⟩
    let f : Lp ℝ 2 (dirichletVolume ρ R) := (hv.indicator hB).toLp (B.indicator v)
    let g := SpectralHeat.heatOperator
      (EinsteinFull.Blueprint.SbxS3UniformCrossHeat.spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) τ f
    have hf : ∀ᵐ x ∂dirichletVolume ρ R, x ∉ B → f x = 0 := by
      filter_upwards [(hv.indicator hB).coeFn_toLp] with x hx hxB
      change ((hv.indicator hB).toLp (B.indicator v)) x = 0
      rw [hx, Set.indicator_of_notMem hxB]
    have hb := c12_supplied_spectral_heat_davies_gaffney hd hκ h R hR s
      A B hA hne δ hδ hsep τ (by exact_mod_cast ht) f hf
    change ‖((Lp.memLp g).indicator hA).toLp (A.indicator fun x => g x)‖ ^ 2 ≤
      Real.exp (-(δ ^ 2) / ((8 * κ⁻¹ ^ 2) * t)) * ‖f‖ ^ 2 at hb
    have hin : ‖f‖ ^ 2 = ∫ y in B, ρ y * v y ^ 2 :=
      c12_dirichlet_restricted_norm_sq hκ h B hB hBb v hv
    have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
      change volume.restrict (sourceBall (0 : Vec d) R) ≪
        (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
          (fun y => ENNReal.ofReal (ρ y))
      apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
      exact ae_of_all _ fun y => ne_of_gt
        (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 y).1))
    have hout : ‖((Lp.memLp g).indicator hA).toLp (A.indicator fun x => g x)‖ ^ 2 =
        ∫ x in A, ρ x * (∫ y in B, K t x y * v y) ^ 2 := by
      rw [c12_dirichlet_restricted_norm_sq hκ h A hA hAb (fun x => g x) (Lp.memLp g)]
      apply integral_congr_ae
      have he := hs τ (show 0 < (τ : ℝ) from ht) f
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hAb (hac.ae_le he)] with x hx
      change g x = _ at hx
      rw [hx]
      congr 2
      exact c12_restricted_input_kernel_integral hκ h B hB hBb v hv (fun y => K t x y)
    rw [hout, hin] at hb
    exact hb
  · have hBempty : B = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    simp [hBempty]

#print axioms c12_native_weighted_davies_gaffney_of_two_le



#print axioms c12_spectral_heat_weighted_energy_inequality

#print axioms c12_spectral_heat_weighted_energy_derivative

#print axioms c12_weighted_energy_of_weak_test

#print axioms c12_weighted_norm_sq_hasDerivAt
#print axioms c12_exponential_weighted_l2_multiplier

#print axioms c12_exponential_multiplier_preserves_dirichlet

#print axioms c12_smooth_weight_cube_bounds

#print axioms c12_smooth_multiplier_preserves_dirichlet

#print axioms c12_graph_multiplier

#print axioms c12_dirichlet_closure_preserved

#print axioms c12_davies_form_lower_bound

#print axioms c12_davies_form_cancel

#print axioms c12_davies_optimize_exponent

end EinsteinFull.Calculus
