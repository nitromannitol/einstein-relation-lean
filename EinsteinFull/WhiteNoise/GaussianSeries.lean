import Mathlib

/-!
# Gaussian series in a Hilbert space

`gaussSeq ι` is the law of an `ι`-indexed family `(ξ k)` of independent standard Gaussians. For a
real Hilbert space `V` and `v : ι → V` with `∑ k, ‖v k‖ ^ 2 < ∞`, the maps `a ↦ ξ k • a` form an
orthogonal family of isometries into `L²(gaussSeq ι; V)`, so `∑ k, ξ k • v k` converges there,
and for every `w : V` the characteristic function of `⟪w, ∑ k, ξ k • v k⟫` is
`r ↦ exp (-(1 / 2) * r ^ 2 * ∑ k, ⟪w, v k⟫ ^ 2)` (`integral_cexp_inner_tsum`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex
open scoped InnerProductSpace RealInnerProductSpace ENNReal

noncomputable section

namespace EinsteinFull.WhiteNoise

variable {ι : Type*}

/-- The law of an `ι`-indexed family of independent standard Gaussians. -/
abbrev gaussSeq (ι : Type*) : Measure (ι → ℝ) :=
  Measure.infinitePi (fun _ : ι => gaussianReal 0 1)

lemma memLp_coord (k : ι) : MemLp (fun ω : ι → ℝ => ω k) 2 (gaussSeq ι) :=
  (memLp_id_gaussianReal 2).comp_measurePreserving
    (measurePreserving_eval_infinitePi (fun _ : ι => gaussianReal 0 1) k)

lemma integral_sq_gaussianReal_zero_one : ∫ x, x * x ∂(gaussianReal 0 1) = 1 := by
  have h := variance_id_gaussianReal (μ := 0) (v := 1)
  rw [variance_eq_integral measurable_id.aemeasurable] at h
  simpa [integral_id_gaussianReal, sq] using h

lemma integral_coord_mul_self (k : ι) : ∫ ω, ω k * ω k ∂(gaussSeq ι) = 1 := by
  rw [← integral_sq_gaussianReal_zero_one,
    ← Measure.infinitePi_map_eval (fun _ : ι => gaussianReal 0 1) k,
    integral_map (measurable_pi_apply k).aemeasurable (by fun_prop)]

lemma integral_coord_mul_coord_of_ne {k j : ι} (h : k ≠ j) :
    ∫ ω, ω k * ω j ∂(gaussSeq ι) = 0 := by
  have hmap := Measure.infinitePi_map_eval_prod (P := fun _ : ι => gaussianReal 0 1) h
  have : ∫ p, p.1 * p.2 ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = 0 := by
    rw [integral_prod_mul (fun x => x) (fun y => y), integral_id_gaussianReal, zero_mul]
  rw [← hmap, integral_map (by fun_prop) (by fun_prop)] at this
  exact this

/-- Characteristic function of a finite linear combination of the coordinates. -/
lemma integral_cexp_finsum (s : Finset ι) (c : ι → ℝ) (r : ℝ) :
    ∫ ω, cexp (I * r * ((∑ k ∈ s, c k * ω k : ℝ) : ℂ)) ∂(gaussSeq ι) =
      cexp (((-(1 / 2 : ℝ)) * r ^ 2 * ∑ k ∈ s, c k ^ 2 : ℝ) : ℂ) := by
  have hmap := Measure.infinitePi_map_restrict (μ := fun _ : ι => gaussianReal 0 1) (I := s)
  set F : (s → ℝ) → ℂ := fun z => ∏ k : s, cexp (I * r * ((c k * z k : ℝ) : ℂ)) with hF
  have hfun : (fun ω : ι → ℝ => cexp (I * r * ((∑ k ∈ s, c k * ω k : ℝ) : ℂ))) =
      fun ω => F (s.restrict ω) := by
    funext ω
    simp only [hF, Finset.restrict]
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_coe_sort s]
    push_cast
    rw [Finset.mul_sum]
  rw [hfun, ← integral_map (Finset.measurable_restrict s).aemeasurable
    (by rw [hmap]; exact (by fun_prop : Continuous F).aestronglyMeasurable), hmap, hF,
    integral_fintype_prod_eq_prod (fun (k : s) (t : ℝ) => cexp (I * r * ((c k * t : ℝ) : ℂ)))]
  have hk : ∀ k : s, ∫ t, cexp (I * r * ((c k * t : ℝ) : ℂ)) ∂(gaussianReal 0 1) =
      cexp (((-(1 / 2 : ℝ)) * r ^ 2 * c k ^ 2 : ℝ) : ℂ) := by
    intro k
    have h := charFun_gaussianReal (μ := 0) (v := 1) (r * c k)
    rw [charFun_apply_real] at h
    convert h using 2
    · funext t; congr 1; push_cast; ring
    · push_cast; ring
  rw [Finset.prod_congr rfl (fun k _ => hk k), ← Complex.exp_sum, ← Finset.sum_coe_sort s]
  congr 1
  push_cast
  rw [Finset.mul_sum]

lemma integrable_cexp_mul (P : Measure (ι → ℝ)) [IsProbabilityMeasure P] {Y : (ι → ℝ) → ℝ}
    (hY : AEStronglyMeasurable Y P) (r : ℝ) :
    Integrable (fun ω => cexp (I * r * (Y ω : ℂ))) P := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all _ fun ω => ?_)
  · exact (by fun_prop : Continuous fun x : ℝ => cexp (I * r * (x : ℂ))
      ).comp_aestronglyMeasurable hY
  · rw [show I * r * (Y ω : ℂ) = ((r * Y ω : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]

lemma norm_cexp_sub_cexp_le (a b : ℝ) : ‖cexp (I * a) - cexp (I * b)‖ ≤ |a - b| := by
  have h : cexp (I * a) - cexp (I * b) = cexp (I * b) * (cexp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, ← Complex.exp_add]; push_cast; ring_nf
  rw [h, norm_mul, show I * (b : ℂ) = (b : ℂ) * I by ring, Complex.norm_exp_ofReal_mul_I, one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

lemma integral_norm_le_norm_L2 (P : Measure (ι → ℝ)) [IsProbabilityMeasure P]
    (f : Lp ℝ 2 P) : ∫ ω, ‖f ω‖ ∂P ≤ ‖f‖ := by
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f), Lp.norm_def,
    ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_lt_top f).ne
    (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

lemma norm_integral_cexp_sub_le (P : Measure (ι → ℝ)) [IsProbabilityMeasure P]
    (Y Z : Lp ℝ 2 P) (r : ℝ) :
    ‖∫ ω, cexp (I * r * (Y ω : ℂ)) ∂P - ∫ ω, cexp (I * r * (Z ω : ℂ)) ∂P‖ ≤ |r| * ‖Y - Z‖ := by
  rw [← integral_sub (integrable_cexp_mul P (Lp.aestronglyMeasurable Y) r)
    (integrable_cexp_mul P (Lp.aestronglyMeasurable Z) r)]
  calc ‖∫ ω, (cexp (I * r * (Y ω : ℂ)) - cexp (I * r * (Z ω : ℂ))) ∂P‖
      ≤ ∫ ω, ‖cexp (I * r * (Y ω : ℂ)) - cexp (I * r * (Z ω : ℂ))‖ ∂P :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |r| * ‖(Y - Z) ω‖ ∂P := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
          ((integrable_norm_iff (Lp.aestronglyMeasurable _)).2
            ((Lp.memLp (Y - Z)).integrable (by norm_num)) |>.const_mul _) ?_
        filter_upwards [Lp.coeFn_sub Y Z] with ω hω
        rw [hω, Pi.sub_apply, Real.norm_eq_abs, mul_assoc, mul_assoc,
          show (r : ℂ) * (Y ω : ℂ) = ((r * Y ω : ℝ) : ℂ) by push_cast; ring,
          show (r : ℂ) * (Z ω : ℂ) = ((r * Z ω : ℝ) : ℂ) by push_cast; ring]
        refine (norm_cexp_sub_cexp_le _ _).trans (le_of_eq ?_)
        rw [← mul_sub, abs_mul]
    _ = |r| * ∫ ω, ‖(Y - Z) ω‖ ∂P := integral_const_mul _ _
    _ ≤ |r| * ‖Y - Z‖ :=
        mul_le_mul_of_nonneg_left (integral_norm_le_norm_L2 P _) (abs_nonneg r)

section Hilbert

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

lemma memLp_coord_smul (k : ι) (a : V) : MemLp (fun ω : ι → ℝ => ω k • a) 2 (gaussSeq ι) :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight a).comp_memLp' (memLp_coord k)

lemma inner_toLp_coord_smul (k j : ι) (a b : V) :
    ⟪(memLp_coord_smul k a).toLp _, (memLp_coord_smul j b).toLp _⟫ =
      (∫ ω, ω k * ω j ∂(gaussSeq ι)) * ⟪a, b⟫ := by
  rw [L2.inner_def]
  have h : (fun ω => ⟪((memLp_coord_smul k a).toLp _ : Lp V 2 (gaussSeq ι)) ω,
      ((memLp_coord_smul j b).toLp _ : Lp V 2 (gaussSeq ι)) ω⟫) =ᵐ[gaussSeq ι]
      fun ω => (ω k * ω j) * ⟪a, b⟫ := by
    filter_upwards [(memLp_coord_smul k a).coeFn_toLp, (memLp_coord_smul j b).coeFn_toLp]
      with ω h1 h2
    rw [h1, h2, real_inner_smul_left, real_inner_smul_right]
    ring
  rw [integral_congr_ae h, integral_mul_const]

/-- The isometry `a ↦ ξ_k • a` from `V` into `L²(gaussSeq ι; V)`. -/
def coordSMul (k : ι) : V →ₗᵢ[ℝ] Lp V 2 (gaussSeq ι) where
  toFun a := (memLp_coord_smul k a).toLp _
  map_add' a b := by
    rw [← MemLp.toLp_add (memLp_coord_smul k a) (memLp_coord_smul k b)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun ω => by simp [smul_add])
  map_smul' c a := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_coord_smul k a)]
    exact MemLp.toLp_congr _ _ (ae_of_all _ fun ω => by simp [smul_comm c (ω k) a])
  norm_map' a := by
    have h := inner_toLp_coord_smul k k a a
    rw [integral_coord_mul_self, one_mul, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq] at h
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

lemma coordSMul_apply (k : ι) (a : V) :
    coordSMul (ι := ι) k a = (memLp_coord_smul k a).toLp _ := rfl

lemma orthogonalFamily_coordSMul :
    OrthogonalFamily ℝ (fun _ : ι => V)
      (fun k => (coordSMul k : V →ₗᵢ[ℝ] Lp V 2 (gaussSeq ι))) := by
  intro k j hkj a b
  rw [coordSMul_apply, coordSMul_apply, inner_toLp_coord_smul,
    integral_coord_mul_coord_of_ne hkj, zero_mul]

lemma summable_coordSMul [CompleteSpace V] {v : ι → V} (hv : Summable fun k => ‖v k‖ ^ 2) :
    Summable fun k => coordSMul k (v k) :=
  (orthogonalFamily_coordSMul.summable_iff_norm_sq_summable v).2 hv

/-- The `k`-th coordinate as an element of `L²(gaussSeq ι)`. -/
def coordLp (k : ι) : Lp ℝ 2 (gaussSeq ι) := (memLp_coord k).toLp _

lemma compLpL_coordSMul (w : V) (k : ι) (a : V) :
    (innerSL ℝ w).compLpL 2 (gaussSeq ι) (coordSMul k a) = ⟪w, a⟫ • coordLp k := by
  apply Lp.ext
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (innerSL ℝ w) (coordSMul k a),
    (memLp_coord_smul k a).coeFn_toLp, Lp.coeFn_smul ⟪w, a⟫ (coordLp k),
    (memLp_coord k).coeFn_toLp] with ω h1 h2 h3 h4
  rw [h1, h3, coordSMul_apply, h2, Pi.smul_apply, coordLp, h4, innerSL_apply_apply,
    real_inner_smul_right, smul_eq_mul, mul_comm]

lemma coeFn_finset_sum_smul_coordLp (s : Finset ι) (c : ι → ℝ) :
    (⇑(∑ k ∈ s, c k • coordLp k : Lp ℝ 2 (gaussSeq ι))) =ᵐ[gaussSeq ι]
      fun ω => ∑ k ∈ s, c k * ω k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 (gaussSeq ι)] with ω h
    rw [h]; rfl
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (c j • coordLp j) (∑ k ∈ s, c k • coordLp k),
      Lp.coeFn_smul (c j) (coordLp j), (memLp_coord j).coeFn_toLp, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, coordLp, h3, h4, smul_eq_mul]

/-- Characteristic function of an `L²` limit of a Gaussian series. -/
theorem integral_cexp_of_hasSum (c : ι → ℝ) (X : Lp ℝ 2 (gaussSeq ι))
    (hX : HasSum (fun k => c k • coordLp k) X) (σ2 : ℝ) (hσ : HasSum (fun k => c k ^ 2) σ2)
    (r : ℝ) :
    ∫ ω, cexp (I * r * (X ω : ℂ)) ∂(gaussSeq ι) = cexp (((-(1 / 2 : ℝ)) * r ^ 2 * σ2 : ℝ) : ℂ) := by
  set Φ : Lp ℝ 2 (gaussSeq ι) → ℂ := fun Y => ∫ ω, cexp (I * r * (Y ω : ℂ)) ∂(gaussSeq ι)
  have hΦ : ∀ s : Finset ι, Φ (∑ k ∈ s, c k • coordLp k) =
      cexp (((-(1 / 2 : ℝ)) * r ^ 2 * ∑ k ∈ s, c k ^ 2 : ℝ) : ℂ) := by
    intro s
    rw [← integral_cexp_finsum s c r]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_finset_sum_smul_coordLp s c] with ω h
    rw [h]
  have h1 : Tendsto (fun s : Finset ι => Φ (∑ k ∈ s, c k • coordLp k)) atTop (𝓝 (Φ X)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hX' := (tendsto_iff_norm_sub_tendsto_zero.1 hX).const_mul |r|
    rw [mul_zero] at hX'
    refine squeeze_zero (fun _ => norm_nonneg _) (fun s => ?_) hX'
    exact norm_integral_cexp_sub_le (gaussSeq ι) _ _ r
  have h2 : Tendsto (fun s : Finset ι => Φ (∑ k ∈ s, c k • coordLp k)) atTop
      (𝓝 (cexp (((-(1 / 2 : ℝ)) * r ^ 2 * σ2 : ℝ) : ℂ))) := by
    simp only [hΦ]
    exact ((by fun_prop : Continuous fun x : ℝ =>
      cexp (((-(1 / 2 : ℝ)) * r ^ 2 * x : ℝ) : ℂ)).tendsto
      σ2).comp hσ
  exact tendsto_nhds_unique h1 h2

/-- Characteristic function of `⟪w, G⟫` for the Gaussian series `G = ∑ ξ_k • v k`. -/
theorem integral_cexp_inner_tsum [CompleteSpace V] (v : ι → V) (hv : Summable fun k => ‖v k‖ ^ 2)
    (w : V) (σ2 : ℝ) (hσ : HasSum (fun k => ⟪w, v k⟫ ^ 2) σ2) (r : ℝ) :
    ∫ ω, cexp (I * r * ((⟪w, ((∑' k, coordSMul k (v k)) : Lp V 2 (gaussSeq ι)) ω⟫ : ℝ) : ℂ))
      ∂(gaussSeq ι) = cexp (((-(1 / 2 : ℝ)) * r ^ 2 * σ2 : ℝ) : ℂ) := by
  set G : Lp V 2 (gaussSeq ι) := ∑' k, coordSMul k (v k)
  have hG : HasSum (fun k => coordSMul k (v k)) G := (summable_coordSMul hv).hasSum
  have hX : HasSum (fun k => ⟪w, v k⟫ • coordLp k) ((innerSL ℝ w).compLpL 2 (gaussSeq ι) G) := by
    have := hG.mapL ((innerSL ℝ w).compLpL 2 (gaussSeq ι))
    simpa only [compLpL_coordSMul] using this
  rw [← integral_cexp_of_hasSum _ _ hX σ2 hσ r]
  refine integral_congr_ae ?_
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (innerSL ℝ w) G] with ω h
  rw [h, innerSL_apply_apply]

end Hilbert

end EinsteinFull.WhiteNoise
