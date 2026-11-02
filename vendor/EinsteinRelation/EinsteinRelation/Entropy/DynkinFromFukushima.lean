import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import EinsteinRelation.Calculus.HorizontalCore
import EinsteinRelation.Calculus.EnvironmentWeakCalculusCore
import EinsteinRelation.Sharpness.SharpA11Limit

/-! # The Dynkin identity for the reduced diffusion

Source: `paper/main.tex` 528-531 (Step 1 of Lemma 4.1) and 660-662 (Lemma 4.3): "the martingale
problem, tested against horizontally smooth functions" and "the martingale identity
`d/dt E^λ[f(ω_t)] = E[p_t L^λ f]`". For a `C²` function `u` with bounded and Lipschitz gradient, the
weak drift of `u` under the force-`λ` Dirichlet form is the spatial generator
`L^λ u = ½ ∑_k ∂_k(∑_j a_{jk} ∂_j u) + λ ∑_j a_{j1} ∂_j u` (`isWeakDrift_spatialGenerator`).
`FukushimaDecompositionInput` (with its mean-zero conclusion) then gives the Dynkin identity
`E₀[u(Y_t)] - u(0) = E₀ ∫₀ᵗ L^λ u(Y_s) ds` for every realization (`dynkin_of_fukushima`).
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

open EinsteinRelation.External.GantertSection7Support

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

/-- The spatial generator `L^λ u = ½ ∑_k ∂_k(∑_j a_{jk} ∂_j u) + λ ∑_j a_{j1} ∂_j u` with the
pointwise (totalized) derivative of the Lipschitz flux. -/
def spatialGenerator (hd : 2 ≤ d) (lam : ℝ) (a : Vec d → Mat d) (u : Vec d → ℝ) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun y => ∑ j, a y j k * fderiv ℝ u y (unitVector j)) x (unitVector k) +
    lam * ∑ j, a x j (firstCoordinateIndex hd) * fderiv ℝ u x (unitVector j)

private theorem dk_abs_coord_le (v : Vec d) (j : Fin d) : |v j| ≤ ‖v‖ := by
  rw [← Real.norm_eq_abs]; exact norm_le_pi_norm v j

/-- The product of two bounded Lipschitz functions is Lipschitz. -/
theorem lipschitzWith_mul_of_bounded {f g : Vec d → ℝ} {Lf Lg : ℝ≥0} {Bf Bg : ℝ}
    (hf : LipschitzWith Lf f) (hg : LipschitzWith Lg g) (hBf : ∀ x, |f x| ≤ Bf)
    (hBg : ∀ x, |g x| ≤ Bg) :
    LipschitzWith (⟨max Bf 0, le_max_right _ _⟩ * Lg + ⟨max Bg 0, le_max_right _ _⟩ * Lf)
      fun x => f x * g x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  simp only [Real.dist_eq, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_mk]
  have hgxy := hg.dist_le_mul x y
  have hfxy := hf.dist_le_mul x y
  rw [Real.dist_eq] at hgxy hfxy
  have e : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
  rw [e]
  calc |f x * (g x - g y) + g y * (f x - f y)| ≤ |f x| * |g x - g y| + |g y| * |f x - f y| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ max Bf 0 * (Lg * dist x y) + max Bg 0 * (Lf * dist x y) := by
        gcongr
        · exact (hBf x).trans (le_max_left _ _)
        · exact (hBg y).trans (le_max_left _ _)
    _ = (max Bf 0 * Lg + max Bg 0 * Lf) * dist x y := by ring

/-- A finite sum of Lipschitz functions is Lipschitz. -/
theorem lipschitzWith_finset_sum {ι : Type*} (s : Finset ι) {g : ι → Vec d → ℝ} {L : ι → ℝ≥0}
    (hg : ∀ j, LipschitzWith (L j) (g j)) :
    LipschitzWith (∑ j ∈ s, L j) fun x => ∑ j ∈ s, g j x := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  calc dist (∑ j ∈ s, g j x) (∑ j ∈ s, g j y) ≤ ∑ j ∈ s, dist (g j x) (g j y) :=
        dist_sum_sum_le s _ _
    _ ≤ ∑ j ∈ s, (L j : ℝ) * dist x y := Finset.sum_le_sum fun j _ => (hg j).dist_le_mul x y
    _ = ((∑ j ∈ s, L j : ℝ≥0) : ℝ) * dist x y := by rw [← Finset.sum_mul]; push_cast; rfl

private theorem dk_sum_mul_unitVector (c : Fin d → ℝ) (j : Fin d) :
    ∑ k, c k * (unitVector k) j = c j := by
  simp [unitVector, Pi.single_apply]

/-- **The weak drift of a `C²` function.** For a regular pair with zero potential and a `C²`
function `u` with bounded, Lipschitz gradient, the spatial generator is the weak drift:
`½ ∫ ∇u · a ∇v dm_λ = -∫ (L^λ u) v dm_λ` for every compactly supported `C¹` function `v`. -/
theorem isWeakDrift_spatialGenerator (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K) {ω : FieldPair d}
    (hω : IsRegular K ω) (hV : ∀ x, ω.2 x = 0) (lam : ℝ) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u)
    {M : ℝ} {L : ℝ≥0} (hdu : ∀ x j, |fderiv ℝ u x (unitVector j)| ≤ M)
    (hLu : ∀ j, LipschitzWith L fun x => fderiv ℝ u x (unitVector j)) :
    IsWeakDrift hd ω lam u (spatialGenerator hd lam ω.1 u) := by
  intro v hv hvc
  rw [integral_physicalReversibleMeasure_of_zero_potential hd hV,
    integral_physicalReversibleMeasure_of_zero_potential hd hV]
  set ρ := physicalForceWeight hd lam with hρdef
  set i₀ := firstCoordinateIndex hd with hi₀
  set f : Fin d → Vec d → ℝ := fun k y => ∑ j, ω.1 y j k * fderiv ℝ u y (unitVector j) with hfdef
  set g : Vec d → ℝ := fun x => ρ x * v x with hgdef
  have hρd := hasFDerivAt_physicalForceWeight hd lam
  have hvd : ∀ x, HasFDerivAt v (fderiv ℝ v x) x :=
    fun x => ((hv.differentiable one_ne_zero) x).hasFDerivAt
  have hgd : ∀ x, HasFDerivAt g (ρ x • fderiv ℝ v x +
      v x • (ρ x • ((2 * lam) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ)
        i₀))) x := fun x => (hρd x).mul (hvd x)
  have hg : ContDiff ℝ 1 g := (contDiff_physicalForceWeight hd lam).mul hv
  have hgc : HasCompactSupport g := hvc.mul_left
  have hgcont : Continuous g := hg.continuous
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgc
  have hdg : ∀ x k, fderiv ℝ g x (unitVector k) =
      ρ x * fderiv ℝ v x (unitVector k) + v x * (ρ x * (2 * lam * (unitVector k) i₀)) := by
    intro x k
    rw [(hgd x).fderiv]
    simp [smul_eq_mul]
  have hduc : ∀ j, Continuous fun x => fderiv ℝ u x (unitVector j) := fun j =>
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have hentc : ∀ j k : Fin d, Continuous fun y => ω.1 y j k := fun j k =>
    ω.1.continuous.matrix_elem j k
  have hfc : ∀ k, Continuous (f k) := fun k =>
    continuous_finset_sum _ fun j _ => (hentc j k).mul (hduc j)
  have hdgc : ∀ k, Continuous fun x => fderiv ℝ g x (unitVector k) := fun k =>
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgs : ∀ k, HasCompactSupport fun x => fderiv ℝ g x (unitVector k) := fun k =>
    (hgc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) rfl
  have hI1 : ∀ k, Integrable fun x => f k x * fderiv ℝ g x (unitVector k) := fun k =>
    ((hfc k).mul (hdgc k)).integrable_of_hasCompactSupport (hdgs k).mul_left
  have hI3 : Integrable fun x => f i₀ x * g x :=
    ((hfc i₀).mul hgcont).integrable_of_hasCompactSupport hgc.mul_left
  -- Lipschitz bounds for the fluxes `f k`.
  have hfL : ∀ k, ∃ C : ℝ≥0, LipschitzWith C (f k) := by
    intro k
    have hj : ∀ j, LipschitzWith
        (⟨max K 0, le_max_right _ _⟩ * L + ⟨max M 0, le_max_right _ _⟩ * (K * d).toNNReal)
        fun y => ω.1 y j k * fderiv ℝ u y (unitVector j) := fun j =>
      lipschitzWith_mul_of_bounded (lipschitzWith_entry_of_isRegular hK.le hω j k) (hLu j)
        (fun y => abs_entry_le_of_isRegular hK hω y j k) (fun y => hdu y j)
    exact ⟨_, lipschitzWith_finset_sum Finset.univ hj⟩
  choose Cf hCf using hfL
  have hI2 : ∀ k, Integrable fun x => fderiv ℝ (f k) x (unitVector k) * g x := fun k =>
    hgint.bdd_mul (measurable_fderiv_apply_const ℝ (f k) (unitVector k)).aestronglyMeasurable
      (ae_of_all _ fun x => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hCf k)) (norm_nonneg _)))
  have hIBP : ∀ k, ∫ x, f k x * fderiv ℝ g x (unitVector k) =
      -∫ x, fderiv ℝ (f k) x (unitVector k) * g x := by
    intro k
    obtain ⟨Cg, hgL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg one_ne_zero
    have h := (hCf k).integral_lineDeriv_mul_eq (μ := volume) hgL hgc (unitVector k)
    have hl1 : ∫ x, lineDeriv ℝ (f k) x (unitVector k) * g x =
        ∫ x, fderiv ℝ (f k) x (unitVector k) * g x :=
      integral_congr_ae (((hCf k).ae_differentiableAt (μ := volume)).mono fun x hx => by
        simp only [hx.lineDeriv_eq_fderiv])
    have hl2 : ∀ x, lineDeriv ℝ g x (-unitVector k) = -fderiv ℝ g x (unitVector k) := fun x => by
      rw [(hgd x).differentiableAt.lineDeriv_eq_fderiv, map_neg]
    rw [hl1] at h
    simp only [hl2, neg_mul, integral_neg] at h
    rw [h, neg_neg]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  have hE1 : ∀ x, ρ x * ((1 / 2 : ℝ) * dot (spatialGradient u x)
      ((ω.1 x).mulVec (spatialGradient v x))) =
      ∑ k, (1 / 2 : ℝ) * (f k x * fderiv ℝ g x (unitVector k)) - lam * (f i₀ x * g x) := by
    intro x
    have hdot : dot (spatialGradient u x) ((ω.1 x).mulVec (spatialGradient v x)) =
        ∑ k, f k x * fderiv ℝ v x (unitVector k) := by
      simp only [dot, spatialGradient, Matrix.mulVec, dotProduct, hfdef, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
    have hlam' : lam * (f i₀ x * g x) = ∑ k, lam * (f k x * g x) * (unitVector k) i₀ :=
      (dk_sum_mul_unitVector (fun k => lam * (f k x * g x)) i₀).symm
    rw [hdot, hlam', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdg x k]
    simp only [hgdef]
    ring
  have hE2 : ∀ x, ρ x * (spatialGenerator hd lam ω.1 u x * v x) =
      ∑ k, (1 / 2 : ℝ) * (fderiv ℝ (f k) x (unitVector k) * g x) + lam * (f i₀ x * g x) := by
    intro x
    unfold spatialGenerator
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [hgdef, hfdef]
    ring
  rw [integral_congr_ae (ae_of_all _ hE1), integral_congr_ae (ae_of_all _ hE2),
    integral_sub (integrable_finset_sum _ fun k _ => (hI1 k).const_mul _) (hI3.const_mul _),
    integral_add (integrable_finset_sum _ fun k _ => (hI2 k).const_mul _) (hI3.const_mul _),
    integral_finset_sum _ fun k _ => (hI1 k).const_mul _,
    integral_finset_sum _ fun k _ => (hI2 k).const_mul _]
  simp only [integral_const_mul, hIBP, mul_neg, Finset.sum_neg_distrib]
  ring

/-- The fluxes `∑_j a_{jk} ∂_j u` of a regular coefficient and a function with bounded, Lipschitz
gradient are Lipschitz. -/
theorem exists_lipschitzWith_flux {K : ℝ} (hK : 0 < K) {ω : FieldPair d} (hω : IsRegular K ω)
    {u : Vec d → ℝ} {M : ℝ} {L : ℝ≥0} (hdu : ∀ x j, |fderiv ℝ u x (unitVector j)| ≤ M)
    (hLu : ∀ j, LipschitzWith L fun x => fderiv ℝ u x (unitVector j)) (k : Fin d) :
    ∃ C : ℝ≥0, LipschitzWith C fun y => ∑ j, ω.1 y j k * fderiv ℝ u y (unitVector j) := by
  have hj : ∀ j, LipschitzWith
      (⟨max K 0, le_max_right _ _⟩ * L + ⟨max M 0, le_max_right _ _⟩ * (K * d).toNNReal)
      fun y => ω.1 y j k * fderiv ℝ u y (unitVector j) := fun j =>
    lipschitzWith_mul_of_bounded (lipschitzWith_entry_of_isRegular hK.le hω j k) (hLu j)
      (fun y => abs_entry_le_of_isRegular hK hω y j k) (fun y => hdu y j)
  exact ⟨_, lipschitzWith_finset_sum Finset.univ hj⟩

/-- The spatial generator is measurable and bounded. -/
theorem measurable_spatialGenerator (hd : 2 ≤ d) (lam : ℝ) (a : C(Vec d, Mat d)) {u : Vec d → ℝ}
    (hu : ContDiff ℝ 1 u) : Measurable (spatialGenerator hd lam a u) := by
  unfold spatialGenerator
  have hduc : ∀ j, Continuous fun x => fderiv ℝ u x (unitVector j) := fun j =>
    (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    measurable_fderiv_apply_const ℝ _ _)).add (measurable_const.mul ?_)
  exact (continuous_finset_sum _ fun j _ =>
    (a.continuous.matrix_elem j _).mul (hduc j)).measurable

theorem exists_abs_spatialGenerator_le (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K) {ω : FieldPair d}
    (hω : IsRegular K ω) (lam : ℝ) {u : Vec d → ℝ} {M : ℝ} {L : ℝ≥0}
    (hdu : ∀ x j, |fderiv ℝ u x (unitVector j)| ≤ M)
    (hLu : ∀ j, LipschitzWith L fun x => fderiv ℝ u x (unitVector j)) :
    ∃ B : ℝ, ∀ x, |spatialGenerator hd lam ω.1 u x| ≤ B := by
  choose C hC using exists_lipschitzWith_flux hK hω hdu hLu
  refine ⟨(1 / 2) * ∑ k, (C k : ℝ) * ‖unitVector (d := d) k‖ + |lam| * ∑ _j : Fin d, K * |M|,
    fun x => ?_⟩
  unfold spatialGenerator
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => ?_)) (by norm_num)
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hC k)) (norm_nonneg _))
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _)
    rw [abs_mul]
    exact mul_le_mul (abs_entry_le_of_isRegular hK hω x j _) ((hdu x j).trans (le_abs_self M))
      (abs_nonneg _) hK.le

private theorem dk_euclid_le_sum_abs (v : Vec d) : euclideanNorm v ≤ ∑ j, |v j| := by
  unfold euclideanNorm euclideanSq dot
  rw [Real.sqrt_le_iff]
  refine ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  rw [sq, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  calc v j * v j = |v j| * |v j| := (abs_mul_abs_self _).symm
    _ ≤ |v j| * ∑ k, |v k| :=
        mul_le_mul_of_nonneg_left
          (Finset.single_le_sum (f := fun k => |v k|) (fun k _ => abs_nonneg _) (Finset.mem_univ j))
          (abs_nonneg _)

/-- Weak drifts are stable under Lebesgue-almost-everywhere modification. -/
theorem IsWeakDrift.congr_ae {hd : 2 ≤ d} {ω : FieldPair d} {lam : ℝ} {u b b' : Vec d → ℝ}
    (hb : IsWeakDrift hd ω lam u b) (hbb : ∀ᵐ x ∂(volume : Measure (Vec d)), b x = b' x) :
    IsWeakDrift hd ω lam u b' := by
  intro v hv hvc
  rw [hb v hv hvc]
  congr 1
  refine integral_congr_ae ?_
  have hac : physicalReversibleMeasure ω hd lam ≪ volume := withDensity_absolutelyContinuous _ _
  filter_upwards [hac.ae_le hbb] with x hx
  rw [hx]

/-- **The Dynkin identity for one environment, for a given weak drift** (`paper/main.tex` 528-531
and 660-662): for every GMP Section 7 realization of a regular pair and every bounded `C²` function
`u` with bounded gradient whose weak drift is the bounded Borel function `b`,
`E₀[u(Y_t)] - u(0) = E₀ ∫₀ᵗ b(Y_s) ds`. -/
theorem dynkin_of_weakDrift (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {K : ℝ}
    (hK1 : 1 ≤ K) {ω : FieldPair d} (hω : IsRegular K ω) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : GantertFixedEnvironmentRealization hd K hK1 ω hω lam h0 h1)
    {u b : Vec d → ℝ} (hu : ContDiff ℝ 1 u) {B M Bb : ℝ} (hub : ∀ x, |u x| ≤ B)
    (hdu : ∀ x j, |fderiv ℝ u x (unitVector j)| ≤ M) (hbm : Measurable b) (hBb : ∀ x, |b x| ≤ Bb)
    (hwd : IsWeakDrift hd ω lam u b) {t : ℝ} (ht : 0 ≤ t) :
    (∫ γ, u (γ t.toNNReal) ∂r.pathLaw 0) - u 0 =
      ∫ γ, (∫ s in (0 : ℝ)..t, b (γ s.toNNReal)) ∂r.pathLaw 0 := by
  haveI := r.pathLaw_isMarkovKernel
  have hG : ∀ x, euclideanNorm (spatialGradient u x) ≤ d * |M| := fun x => by
    refine (dk_euclid_le_sum_abs _).trans ?_
    calc ∑ j, |spatialGradient u x j| ≤ ∑ _j : Fin d, |M| :=
          Finset.sum_le_sum fun j _ => (hdu x j).trans (le_abs_self M)
      _ = d * |M| := by simp
  obtain ⟨hmem, -, hmean⟩ := hFOT d hd K hK1 ω hω lam h0 h1 r u (d * |M|) hu hG
    b hbm ⟨Bb, hBb⟩ hwd t ht
  have hucont : Continuous u := hu.continuous
  have hevalt : Measurable fun γ : Path d => γ t.toNNReal :=
    (continuous_eval_const t.toNNReal).measurable
  have heval0 : Measurable fun γ : Path d => γ 0 := (continuous_eval_const 0).measurable
  have hA : Integrable (fun γ : Path d => u (γ t.toNNReal)) (r.pathLaw 0) :=
    (integrable_const B).mono' (hucont.measurable.comp hevalt).aestronglyMeasurable
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hub _)
  have hB0 : Integrable (fun γ : Path d => u (γ 0)) (r.pathLaw 0) :=
    (integrable_const B).mono' (hucont.measurable.comp heval0).aestronglyMeasurable
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hub _)
  have hMint := hmem.integrable one_le_two
  have hC : Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..t, b (γ s.toNNReal)) (r.pathLaw 0) := by
    refine ((hA.sub hB0).sub hMint).congr (ae_of_all _ fun γ => ?_)
    simp only [Pi.sub_apply, pathMartingalePart]
    ring
  have hstart : ∫ γ, u (γ 0) ∂r.pathLaw 0 = u 0 := by
    rw [integral_congr_ae ((r.pathLaw_starts_at 0).mono fun γ hγ => by
      show u (γ 0) = u 0
      rw [show γ 0 = 0 from hγ])]
    simp
  have hsplit : ∫ γ, pathMartingalePart u b t γ ∂r.pathLaw 0 =
      (∫ γ, u (γ t.toNNReal) ∂r.pathLaw 0) - (∫ γ, u (γ 0) ∂r.pathLaw 0) -
        ∫ γ, (∫ s in (0 : ℝ)..t, b (γ s.toNNReal)) ∂r.pathLaw 0 := by
    have e1 : ∫ γ, (u (γ t.toNNReal) - u (γ 0)) ∂r.pathLaw 0 =
        (∫ γ, u (γ t.toNNReal) ∂r.pathLaw 0) - ∫ γ, u (γ 0) ∂r.pathLaw 0 := integral_sub hA hB0
    have e2 : ∫ γ, (u (γ t.toNNReal) - u (γ 0) - ∫ s in (0 : ℝ)..t, b (γ s.toNNReal)) ∂r.pathLaw 0 =
        (∫ γ, (u (γ t.toNNReal) - u (γ 0)) ∂r.pathLaw 0) -
          ∫ γ, (∫ s in (0 : ℝ)..t, b (γ s.toNNReal)) ∂r.pathLaw 0 := integral_sub (hA.sub hB0) hC
    rw [← e1, ← e2]
    rfl
  rw [hmean, hstart] at hsplit
  linarith

/-- **The Dynkin identity for one environment** with the spatial generator as drift. -/
theorem dynkin_of_fukushima (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {K : ℝ}
    (hK1 : 1 ≤ K) {ω : FieldPair d} (hω : IsRegular K ω) (hV : ∀ x, ω.2 x = 0) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : GantertFixedEnvironmentRealization hd K hK1 ω hω lam h0 h1)
    {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u) {B M : ℝ} {L : ℝ≥0} (hub : ∀ x, |u x| ≤ B)
    (hdu : ∀ x j, |fderiv ℝ u x (unitVector j)| ≤ M)
    (hLu : ∀ j, LipschitzWith L fun x => fderiv ℝ u x (unitVector j)) {t : ℝ} (ht : 0 ≤ t) :
    (∫ γ, u (γ t.toNNReal) ∂r.pathLaw 0) - u 0 =
      ∫ γ, (∫ s in (0 : ℝ)..t, spatialGenerator hd lam ω.1 u (γ s.toNNReal)) ∂r.pathLaw 0 := by
  have hK : 0 < K := lt_of_lt_of_le one_pos hK1
  obtain ⟨Bb, hBb⟩ := exists_abs_spatialGenerator_le hd hK hω lam hdu hLu
  exact dynkin_of_weakDrift hFOT hd hK1 hω h0 h1 r (hu.of_le one_le_two) hub hdu
    (measurable_spatialGenerator hd lam ω.1 (hu.of_le one_le_two)) hBb
    (isWeakDrift_spatialGenerator hd hK hω hV lam hu hdu hLu) ht

/-! ## The annealed law -/

/-- The annealed coordinate joint law is the composition of the environment law with the probability
part of the origin kernel. -/
theorem annealedCoordinateJoint_eq_compProd (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) :
    Carriers.annealedCoordinateJoint Q P op =
      Q.compProd (Probability.probabilityPart (originLaw P)) := by
  have hae := Probability.probabilityPart_ae_eq Q (originLaw P) op
  ext S hS
  have h1 := Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral Q
    (originLaw P) op (S.indicator 1) (measurable_one.indicator hS)
  unfold Carriers.annealedCoordinateJoint
  rw [← lintegral_indicator_one hS, h1, Measure.compProd_apply hS]
  refine lintegral_congr_ae (hae.mono fun ω hω => ?_)
  dsimp only
  rw [hω, ← lintegral_indicator_one (measurable_prodMk_left hS)]
  rfl

/-- The fibre formula for bounded measurable integrands under the annealed coordinate joint law. -/
theorem integral_annealedCoordinateJoint_eq (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    {G : FieldPair d × Path d → ℝ} (hG : Measurable G) {B : ℝ} (hB : ∀ z, |G z| ≤ B) :
    ∫ z, G z ∂(Carriers.annealedCoordinateJoint Q P op) =
      ∫ ω, (∫ γ, G (ω, γ) ∂originLaw P ω) ∂Q := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q P op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure Q
      (originLaw P) op
  have hJ := annealedCoordinateJoint_eq_compProd Q P op
  have hint : Integrable G (Carriers.annealedCoordinateJoint Q P op) :=
    (integrable_const B).mono' hG.aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hB z)
  rw [hJ] at hint ⊢
  rw [Measure.integral_compProd hint]
  refine integral_congr_ae ((Probability.probabilityPart_ae_eq Q (originLaw P) op).mono
    fun ω hω => ?_)
  dsimp only
  rw [hω]

/-! ## The generator on the environment space -/

/-- The operator norm of a linear form on `Vec d` is at most the sum of its values on the unit
vectors. -/
theorem norm_le_sum_abs_unitVector (A : Vec d →L[ℝ] ℝ) : ‖A‖ ≤ ∑ k, |A (unitVector k)| := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun k _ => abs_nonneg _) fun v => ?_
  have hv : v = ∑ k, v k • unitVector k := by
    funext j
    simp [unitVector, Pi.single_apply, Finset.sum_apply]
  conv_lhs => rw [hv]
  rw [map_sum, Real.norm_eq_abs]
  calc |∑ k, A (v k • unitVector k)| ≤ ∑ k, |A (v k • unitVector k)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |v k| * |A (unitVector k)| := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_smul, smul_eq_mul, abs_mul]
    _ ≤ ∑ k, ‖v‖ * |A (unitVector k)| :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (dk_abs_coord_le v k) (abs_nonneg _)
    _ = (∑ k, |A (unitVector k)|) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

/-- A differentiable function with bounded coordinate derivatives is Lipschitz. -/
theorem lipschitzWith_of_coordinateDerivative_le {g : Vec d → ℝ} (hg : Differentiable ℝ g)
    {M : ℝ} (hM : ∀ x k, |fderiv ℝ g x (unitVector k)| ≤ M) :
    LipschitzWith (d * M).toNNReal g := by
  refine lipschitzWith_of_nnnorm_fderiv_le hg fun x => ?_
  have h := (norm_le_sum_abs_unitVector (fderiv ℝ g x)).trans
    (Finset.sum_le_sum fun k _ => hM x k)
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  refine h.trans (le_of_eq_of_le (by simp) (Real.le_coe_toNNReal _))

/-- The reduced generator acting on a horizontal test, in product-rule form:
`L^λ F = ½ ∑_{j,k} (D_k a_{jk} D_j F + a_{jk} D_k D_j F) + λ ∑_j a_{j1} D_j F`, where `D_k a_{jk}` is
the pointwise derivative of the coefficient at the origin. -/
def envGenerator (hd : 2 ≤ d) (lam : ℝ) (F : FieldPair d → ℝ) (w : FieldPair d) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, ∑ j, (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) *
      horizontalDerivative j F w + w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) +
    lam * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w

/-- Along an orbit, the environment generator is the product-rule spatial generator. -/
theorem envGenerator_translate (hd : 2 ≤ d) (lam : ℝ) (F : FieldPair d → ℝ) (w : FieldPair d)
    (x : Vec d) :
    envGenerator hd lam F (translate x w) =
      (1 / 2 : ℝ) * ∑ k, ∑ j, (fderiv ℝ (fun y => w.1 y j k) x (unitVector k) *
          fderiv ℝ (orbit F w) x (unitVector j) +
        w.1 x j k * fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)) +
      lam * ∑ j, w.1 x j (firstCoordinateIndex hd) * fderiv ℝ (orbit F w) x (unitVector j) := by
  have h1 : ∀ j, horizontalDerivative j F (translate x w) = fderiv ℝ (orbit F w) x (unitVector j) :=
    fun j => horizontalDerivative_translate j F w x
  have h2 : ∀ j k, horizontalDerivative k (horizontalDerivative j F) (translate x w) =
      fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k) := by
    intro j k
    rw [horizontalDerivative_translate]
    have : orbit (horizontalDerivative j F) w = fun y => fderiv ℝ (orbit F w) y (unitVector j) :=
      funext fun y => horizontalDerivative_translate j F w y
    rw [this]
    rfl
  have h3 : ∀ j k, fderiv ℝ (fun y => w.1 (x + y) j k) 0 (unitVector k) =
      fderiv ℝ (fun y => w.1 y j k) x (unitVector k) := by
    intro j k
    have h := fderiv_comp_add_left (𝕜 := ℝ) (f := fun z : Vec d => w.1 z j k) (x := (0 : Vec d)) x
    rw [add_zero] at h
    exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) h
  unfold envGenerator
  simp only [h1, h2, translate_matrix, add_zero, h3]

/-- The pointwise derivative of a coefficient entry at the origin is measurable in the field pair. -/
theorem measurable_fderiv_entry_zero (j k : Fin d) (v : Vec d) :
    Measurable fun w : FieldPair d => fderiv ℝ (fun y => w.1 y j k) 0 v := by
  have hc : Continuous (Function.uncurry fun (w : FieldPair d) (x : Vec d) => (w.1 x) j k) :=
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_elem
      j k
  exact (measurable_fderiv_apply_const_with_param ℝ hc v).comp
    (measurable_id.prodMk measurable_const)

/-- The environment generator of a horizontal test is measurable. -/
theorem measurable_envGenerator (hd : 2 ≤ d) (lam : ℝ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) : Measurable (envGenerator hd lam F) := by
  have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  unfold envGenerator
  refine (measurable_const.mul (Finset.measurable_sum _ fun k _ => Finset.measurable_sum _
    fun j _ => ((measurable_fderiv_entry_zero j k _).mul (hF.measurable_derivative j)).add
      ((hentry j k).mul ((hF.horizontalDerivative j).measurable_derivative k)))).add
    (measurable_const.mul (Finset.measurable_sum _ fun j _ =>
      (hentry j _).mul (hF.measurable_derivative j)))

/-- Where the coefficient entries are differentiable, the spatial generator is the product-rule
generator. Hence the two agree Lebesgue-almost everywhere for a Lipschitz coefficient. -/
theorem ae_spatialGenerator_eq_envGenerator (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K) {ω : FieldPair d}
    (hω : IsRegular K ω) (lam : ℝ) {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (w : FieldPair d)
    (hw : ω.1 = w.1) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      spatialGenerator hd lam ω.1 (orbit F w) x = envGenerator hd lam F (translate x w) := by
  have hdiff : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j k : Fin d,
      DifferentiableAt ℝ (fun y => ω.1 y j k) x := by
    rw [ae_all_iff]; intro j; rw [ae_all_iff]; intro k
    exact (lipschitzWith_entry_of_isRegular hK.le hω j k).ae_differentiableAt
  have hus : ContDiff ℝ (⊤ : ℕ∞) (orbit F w) := hF.2.1 w
  have hdu : ∀ j, Differentiable ℝ fun y => fderiv ℝ (orbit F w) y (unitVector j) := fun j =>
    ((hus.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).clm_apply contDiff_const).differentiable
      one_ne_zero
  filter_upwards [hdiff] with x hx
  rw [envGenerator_translate, spatialGenerator]
  rw [← hw]
  congr 2
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfd : ∀ j, HasFDerivAt (fun y => ω.1 y j k * fderiv ℝ (orbit F w) y (unitVector j))
      (ω.1 x j k • fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x +
        fderiv ℝ (orbit F w) x (unitVector j) • fderiv ℝ (fun y => ω.1 y j k) x) x := fun j =>
    (hx j k).hasFDerivAt.mul ((hdu j) x).hasFDerivAt
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hfd j)
  rw [hsum.fderiv]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The derivative bounds of a horizontal test, uniform over environments. -/
theorem IsHorizontalTest.exists_bounds {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) :
    ∃ M0 M1 M2 : ℝ, 0 ≤ M1 ∧ 0 ≤ M2 ∧ (∀ w x, |orbit F w x| ≤ M0) ∧
      (∀ w x j, |fderiv ℝ (orbit F w) x (unitVector j)| ≤ M1) ∧
      (∀ w x j k, |fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)| ≤ M2) := by
  obtain ⟨M0, -, h0⟩ := hF.bound_orbit
  choose M1 hM1 h1 using hF.bound_derivative
  choose M2 hM2 h2 using fun j => (hF.horizontalDerivative j).bound_derivative
  refine ⟨M0, ∑ j, M1 j, ∑ j, ∑ k, M2 j k, Finset.sum_nonneg fun j _ => hM1 j,
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => hM2 j k, h0, fun w x j => ?_,
    fun w x j k => ?_⟩
  · exact (h1 j w x).trans (Finset.single_le_sum (f := M1) (fun j _ => hM1 j) (Finset.mem_univ j))
  · have horb : orbit (EinsteinRelation.horizontalDerivative j F) w =
        fun y => fderiv ℝ (orbit F w) y (unitVector j) := by
      rw [orbit_horizontalDerivative]; rfl
    have h := h2 j k w x
    rw [horb] at h
    refine h.trans ?_
    exact (Finset.single_le_sum (f := fun k => M2 j k) (fun k _ => hM2 j k) (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun j => ∑ k, M2 j k)
        (fun j _ => Finset.sum_nonneg fun k _ => hM2 j k) (Finset.mem_univ j))

/-- On regular environments the environment generator of a horizontal test is bounded, uniformly. -/
theorem exists_abs_envGenerator_le (hd : 2 ≤ d) (lam : ℝ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) {K : ℝ} (hK : 0 < K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (v w : FieldPair d), IsRegular K v → v.1 = w.1 → ∀ x,
      |envGenerator hd lam F (translate x w)| ≤ B := by
  obtain ⟨M0, M1, M2, hM1, hM2, -, h1, h2⟩ := hF.exists_bounds
  set Lk : ℝ := ((K * d).toNNReal : ℝ) * ∑ k : Fin d, ‖unitVector (d := d) k‖ with hLk
  have hLk0 : 0 ≤ Lk := mul_nonneg (NNReal.coe_nonneg _)
    (Finset.sum_nonneg fun k _ => norm_nonneg _)
  refine ⟨(1 / 2) * ∑ _k : Fin d, ∑ _j : Fin d, (Lk * M1 + K * M2) +
      |lam| * ∑ _j : Fin d, K * M1, by positivity, fun v w hv hvw x => ?_⟩
  rw [envGenerator_translate]
  have hent : ∀ y j k, |w.1 y j k| ≤ K := fun y j k => by
    rw [← hvw]; exact abs_entry_le_of_isRegular hK hv y j k
  have hder : ∀ j k, |fderiv ℝ (fun y => w.1 y j k) x (unitVector k)| ≤ Lk := by
    intro j k
    rw [← Real.norm_eq_abs]
    have hL := lipschitzWith_entry_of_isRegular hK.le hv j k
    rw [hvw] at hL
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul (norm_fderiv_le_of_lipschitz ℝ hL)
      (Finset.single_le_sum (f := fun k => ‖unitVector (d := d) k‖) (fun k _ => norm_nonneg _)
        (Finset.mem_univ k)) (norm_nonneg _) (NNReal.coe_nonneg _)
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun k _ => (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun j _ => ?_))) (by norm_num)
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]; exact mul_le_mul (hder j k) (h1 w x j) (abs_nonneg _) hLk0
    · rw [abs_mul]; exact mul_le_mul (hent x j k) (h2 w x j k) (abs_nonneg _) hK.le
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) (abs_nonneg _)
    rw [abs_mul]; exact mul_le_mul (hent x j _) (h1 w x j) (abs_nonneg _) hK.le

/-- The environment generator clamped at the level `B`. -/
def clampedEnvGenerator (hd : 2 ≤ d) (lam B : ℝ) (F : FieldPair d → ℝ) (w : FieldPair d) : ℝ :=
  max (-B) (min B (envGenerator hd lam F w))

theorem clampedEnvGenerator_eq {hd : 2 ≤ d} {lam B : ℝ} {F : FieldPair d → ℝ} {w : FieldPair d}
    (h : |envGenerator hd lam F w| ≤ B) : clampedEnvGenerator hd lam B F w = envGenerator hd lam F w := by
  unfold clampedEnvGenerator
  rw [min_eq_right (abs_le.mp h).2, max_eq_right (abs_le.mp h).1]

theorem abs_clampedEnvGenerator_le {hd : 2 ≤ d} {lam B : ℝ} (hB : 0 ≤ B) (F : FieldPair d → ℝ)
    (w : FieldPair d) : |clampedEnvGenerator hd lam B F w| ≤ B := by
  unfold clampedEnvGenerator
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem measurable_clampedEnvGenerator (hd : 2 ≤ d) (lam B : ℝ) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) : Measurable (clampedEnvGenerator hd lam B F) :=
  measurable_const.max (measurable_const.min (measurable_envGenerator hd lam hF))

/-! ## The annealed Dynkin identity -/

/-- The Dynkin identity on one fibre of the reduced GMP family, for a horizontal test `F` whose
environment generator is bounded by `B` along the orbit of the reduced environment. -/
theorem fibre_dynkin (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {K : ℝ} (hK1 : 1 ≤ K)
    (ω : FieldPair d) (hω' : IsRegular K (zeroPotentialReducedPair ω)) {lam : ℝ} (h0 : 0 ≤ lam)
    (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd K hK1 (zeroPotentialReducedPair ω) hω' lam h0 h1)
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |envGenerator hd lam F (translate x (reduce ω))| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    ∫ γ, (F (Carriers.reducedObservationAt t.toNNReal (ω, γ)) - F (reduce ω)) ∂r.pathLaw 0 =
      ∫ γ, (∫ u in (0 : ℝ)..t,
        clampedEnvGenerator hd lam B F (Carriers.reducedObservationAt u.toNNReal (ω, γ)))
          ∂r.pathLaw 0 := by
  haveI := r.pathLaw_isMarkovKernel
  have hK : 0 < K := lt_of_lt_of_le one_pos hK1
  obtain ⟨M0, M1, M2, -, -, hb0, hb1, hb2⟩ := hF.exists_bounds
  set G := clampedEnvGenerator hd lam B F with hGdef
  have hGm : Measurable G := measurable_clampedEnvGenerator hd lam B hF
  have hGB : ∀ w, |G w| ≤ B := abs_clampedEnvGenerator_le hB0 F
  set w := reduce ω with hwdef
  set ω₀ := zeroPotentialReducedPair ω with hω₀def
  have hw : ω₀.1 = w.1 := rfl
  have hV : ∀ x, ω₀.2 x = 0 := fun x => rfl
  have hus : ContDiff ℝ (⊤ : ℕ∞) (orbit F w) := hF.2.1 w
  have hdiff : ∀ j, Differentiable ℝ fun y => fderiv ℝ (orbit F w) y (unitVector j) := fun j =>
    ((hus.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiff_const).differentiable one_ne_zero
  have hLu : ∀ j, LipschitzWith (d * M2).toNNReal
      fun x => fderiv ℝ (orbit F w) x (unitVector j) :=
    fun j => lipschitzWith_of_coordinateDerivative_le (hdiff j) fun x k => hb2 w x j k
  have hbm : Measurable fun x : Vec d => G (translate x w) :=
    hGm.comp (Probability.continuous_translate.comp
      (continuous_id.prodMk continuous_const)).measurable
  have hbeq : ∀ x, G (translate x w) = envGenerator hd lam F (translate x w) := fun x =>
    clampedEnvGenerator_eq (hB x)
  have hus2 : ContDiff ℝ 2 (orbit F w) := hus.of_le (WithTop.coe_le_coe.mpr le_top)
  have hwd : IsWeakDrift hd ω₀ lam (orbit F w) fun x => G (translate x w) := by
    refine (isWeakDrift_spatialGenerator hd hK hω' hV lam hus2 (hb1 w) hLu).congr_ae ?_
    filter_upwards [ae_spatialGenerator_eq_envGenerator hd hK hω' lam hF w hw] with x hx
    rw [hx, hbeq]
  have hus1 : ContDiff ℝ 1 (orbit F w) := hus2.of_le one_le_two
  have hbB : ∀ x, |G (translate x w)| ≤ B := fun x => hGB _
  have hdyn := dynkin_of_weakDrift (u := orbit F w) (b := fun x => G (translate x w)) hFOT hd hK1
    hω' h0 h1 r hus1 (hb0 w) (hb1 w) hbm hbB hwd ht
  have hA : Integrable (fun γ : Path d => orbit F w (γ t.toNNReal)) (r.pathLaw 0) :=
    (integrable_const M0).mono'
      (hus.continuous.measurable.comp (continuous_eval_const t.toNNReal).measurable).aestronglyMeasurable
      (ae_of_all _ fun γ => by rw [Real.norm_eq_abs]; exact hb0 w _)
  have e1 : (fun γ : Path d =>
      F (Carriers.reducedObservationAt t.toNNReal (ω, γ)) - F w) =
      fun γ => orbit F w (γ t.toNNReal) - orbit F w 0 := by
    funext γ
    rw [orbit_zero]
    rfl
  have e2 : (fun γ : Path d =>
      ∫ u in (0 : ℝ)..t, G (Carriers.reducedObservationAt u.toNNReal (ω, γ))) =
      fun γ => ∫ s in (0 : ℝ)..t, G (translate (γ s.toNNReal) w) := rfl
  rw [e1, e2, integral_sub hA (integrable_const _), integral_const, probReal_univ, one_smul]
  exact hdyn

/-- **The annealed Dynkin identity** for a horizontal test `F` (`paper/main.tex` 660-662):
`E[F(ω_t)] - E[F] = ∫₀ᵗ E[L^λ F(ω_u)] du` for the reduced GMP family, with the environment
generator clamped at a level `B` that it does not exceed along the reduced paths. -/
theorem annealed_dynkin (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (v w : FieldPair d), IsRegular (sourceReducedBound Λ₀) v → v.1 = w.1 → ∀ x,
      |envGenerator hd lam F (translate x w)| ≤ B) {t : ℝ} (ht : 0 ≤ t) :
    Density.observationMean Q.measure P op F t - ∫ w, F w ∂(Carriers.reducedReferenceLaw Q) =
      ∫ u in (0 : ℝ)..t,
        Density.observationMean Q.measure P op (clampedEnvGenerator hd lam B F) u := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure _
      (originLaw P) op
  set J := Carriers.annealedCoordinateJoint Q.measure P op
  obtain ⟨M0, -, -, -, -, hb0, -, -⟩ := hF.exists_bounds
  have hK1 : 1 ≤ sourceReducedBound Λ₀ := one_le_sourceReducedBound Q.ellipticity_parameter
  set G := clampedEnvGenerator hd lam B F with hGdef
  have hGm : Measurable G := measurable_clampedEnvGenerator hd lam B hF
  have hGB : ∀ w, |G w| ≤ B := abs_clampedEnvGenerator_le hB0 F
  have hFm : Measurable F := hF.1
  have hFB : ∀ w, |F w| ≤ M0 := fun w => by simpa using hb0 w 0
  have hobs : ∀ τ : ℝ, Measurable fun z : FieldPair d × Path d =>
      Carriers.reducedObservationAt τ.toNNReal z := fun τ =>
    laplaceDensity_measurable_observation_fixed τ.toNNReal
  have hred : Measurable fun z : FieldPair d × Path d => reduce z.1 :=
    (Probability.measurable_reduce (d := d)).comp measurable_fst
  have hint1 : Integrable (fun z => F (Carriers.reducedObservationAt t.toNNReal z)) J :=
    (integrable_const M0).mono' (hFm.comp (hobs t)).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hFB _)
  have hint2 : Integrable (fun z : FieldPair d × Path d => F (reduce z.1)) J :=
    (integrable_const M0).mono' (hFm.comp hred).aestronglyMeasurable
      (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hFB _)
  have href : ∫ w, F w ∂(Carriers.reducedReferenceLaw Q) = ∫ z, F (reduce z.1) ∂J := by
    rw [integral_annealedCoordinateJoint_eq Q.measure P op (G := fun z => F (reduce z.1))
      (hFm.comp hred) (B := M0) (fun z => hFB _)]
    unfold Carriers.reducedReferenceLaw
    rw [integral_map (Probability.measurable_reduce (d := d)).aemeasurable
      hFm.aestronglyMeasurable]
    refine integral_congr_ae (op.mono fun ω hω => ?_)
    haveI := hω
    show F (reduce ω) = ∫ _γ, F (reduce ω) ∂originLaw P ω
    rw [integral_const, probReal_univ, one_smul]
  have hprim : ∫ u in (0 : ℝ)..t, Density.observationMean Q.measure P op G u =
      ∫ z, (∫ u in (0 : ℝ)..t, G (Carriers.reducedObservationAt u.toNNReal z)) ∂J :=
    (Sharpness.integral_primitive_observation Q.measure P op G hGm hGB ht).symm
  have hobsJ : Measurable fun p : (FieldPair d × Path d) × ℝ =>
      G (Carriers.reducedObservationAt p.2.toNNReal p.1) :=
    hGm.comp (laplaceDensity_measurable_observation.comp measurable_swap)
  have hΦm : Measurable fun z : FieldPair d × Path d =>
      ∫ u in (0 : ℝ)..t, G (Carriers.reducedObservationAt u.toNNReal z) := by
    have hΦeq : (fun z : FieldPair d × Path d =>
        ∫ u in (0 : ℝ)..t, G (Carriers.reducedObservationAt u.toNNReal z)) = fun z =>
        ∫ u in Set.Ioc 0 t, G (Carriers.reducedObservationAt u.toNNReal z) :=
      funext fun z => intervalIntegral.integral_of_le ht
    rw [hΦeq]
    exact ((hobsJ.stronglyMeasurable).integral_prod_right'
      (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 t))).measurable
  have hΦB : ∀ z : FieldPair d × Path d,
      |∫ u in (0 : ℝ)..t, G (Carriers.reducedObservationAt u.toNNReal z)| ≤ B * |t - 0| := by
    intro z
    rw [← Real.norm_eq_abs]
    exact intervalIntegral.norm_integral_le_of_norm_le_const fun u _ => by
      rw [Real.norm_eq_abs]; exact hGB _
  have hdiffm : Measurable fun z : FieldPair d × Path d =>
      F (Carriers.reducedObservationAt t.toNNReal z) - F (reduce z.1) :=
    (hFm.comp (hobs t)).sub (hFm.comp hred)
  have hdiffB : ∀ z : FieldPair d × Path d,
      |F (Carriers.reducedObservationAt t.toNNReal z) - F (reduce z.1)| ≤ M0 + M0 := fun z =>
    (abs_sub _ _).trans (add_le_add (hFB _) (hFB _))
  rw [hprim, href]
  show ∫ z, F (Carriers.reducedObservationAt t.toNNReal z) ∂J - ∫ z, F (reduce z.1) ∂J = _
  rw [← integral_sub hint1 hint2, integral_annealedCoordinateJoint_eq Q.measure P op hdiffm hdiffB,
    integral_annealedCoordinateJoint_eq Q.measure P op hΦm hΦB]
  refine integral_congr_ae (hP.mono fun ω hω => ?_)
  obtain ⟨hω', r, hr⟩ := hω
  dsimp only
  rw [hr]
  exact fibre_dynkin hFOT hd hK1 ω hω' h0 h1 r hF hB0 (hB _ _ hω' rfl) ht

/-- **The Laplace form of the Dynkin identity** (`paper/main.tex` 660-662): for the reduced
Laplace-time density `ρ_s` and a horizontal test `F`, `s E[ρ_s F] - s E[F] = E[ρ_s L^λ F]`, with the
generator clamped as in `annealed_dynkin`. -/
theorem laplace_dynkin (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (v w : FieldPair d), IsRegular (sourceReducedBound Λ₀) v → v.1 = w.1 → ∀ x,
      |envGenerator hd lam F (translate x w)| ≤ B)
    (s : {r : ℝ // 0 < r}) {rho : FieldPair d → ℝ}
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P op s rho) :
    s.1 * (∫ w, rho w * F w ∂(Carriers.reducedReferenceLaw Q)) -
        s.1 * (∫ w, F w ∂(Carriers.reducedReferenceLaw Q)) =
      ∫ w, rho w * clampedEnvGenerator hd lam B F w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P op) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure _
      (originLaw P) op
  obtain ⟨M0, -, -, -, -, hb0, -, -⟩ := hF.exists_bounds
  have hGm : Measurable (clampedEnvGenerator hd lam B F) := measurable_clampedEnvGenerator hd lam B hF
  have hGB : ∀ w, |clampedEnvGenerator hd lam B F w| ≤ B := abs_clampedEnvGenerator_le hB0 F
  have hFm : Measurable F := hF.1
  have hFB : ∀ w, |F w| ≤ M0 := fun w => by simpa using hb0 w 0
  obtain ⟨c, hc⟩ : ∃ c, c = ∫ w, F w ∂(Carriers.reducedReferenceLaw Q) := ⟨_, rfl⟩
  rw [← hc]
  have href : Carriers.reducedReferenceLaw Q = Measure.map reduce Q.measure := rfl
  rw [href]
  have hgB : ∀ w, |F w - c| ≤ M0 + |c| := fun w =>
    (abs_sub _ _).trans (add_le_add (hFB w) le_rfl)
  have hI1 := Density.integral_mul_density_eq_setIntegral_Ici Q.measure P op s rho hrho
    (fun w => F w - c) (hFm.sub measurable_const) hgB
  have hI2 := Density.integral_mul_density_eq_setIntegral_Ici Q.measure P op s rho hrho
    (clampedEnvGenerator hd lam B F) hGm hGB
  have hone := Density.integral_density_eq_one Q.measure P op s rho hrho
  -- On `[0, ∞)`, `E[F(ω_t)] - c = ∫₀ᵗ E[L^λ F(ω_u)] du`.
  have hdyn : ∀ t ∈ Set.Ici (0 : ℝ), s.1 * Real.exp (-(s.1 * t)) *
      (∫ z, (F (Carriers.reducedObservationAt t.toNNReal z) - c)
        ∂(Carriers.annealedCoordinateJoint Q.measure P op)) =
      s.1 * (Real.exp (-(s.1 * t)) * ∫ u in (0 : ℝ)..t,
        Density.observationMean Q.measure P op (clampedEnvGenerator hd lam B F) u) := by
    intro t ht
    have hD := annealed_dynkin hFOT hd Q h0 h1 P op hP hF hB0 hB (t := t) ht
    rw [← hc] at hD
    have hint1 : Integrable (fun z => F (Carriers.reducedObservationAt t.toNNReal z))
        (Carriers.annealedCoordinateJoint Q.measure P op) :=
      (integrable_const M0).mono'
        (hFm.comp (laplaceDensity_measurable_observation_fixed t.toNNReal)).aestronglyMeasurable
        (ae_of_all _ fun z => by rw [Real.norm_eq_abs]; exact hFB _)
    rw [integral_sub hint1 (integrable_const c), integral_const, probReal_univ, one_smul]
    show s.1 * Real.exp (-(s.1 * t)) * (Density.observationMean Q.measure P op F t - c) = _
    rw [hD]
    ring
  have hX : ∫ w, rho w * (F w - c) ∂(Measure.map reduce Q.measure) =
      s.1 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s.1 * t)) * ∫ u in (0 : ℝ)..t,
        Density.observationMean Q.measure P op (clampedEnvGenerator hd lam B F) u := by
    rw [hI1, setIntegral_congr_fun measurableSet_Ici hdyn, integral_Ici_eq_integral_Ioi,
      integral_const_mul]
  have hY : ∫ w, rho w * clampedEnvGenerator hd lam B F w ∂(Measure.map reduce Q.measure) =
      s.1 ^ 2 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s.1 * t)) * ∫ u in (0 : ℝ)..t,
        Density.observationMean Q.measure P op (clampedEnvGenerator hd lam B F) u := by
    rw [hI2, integral_Ici_eq_integral_Ioi]
    have hpull : ∫ t in Set.Ioi (0 : ℝ), s.1 * Real.exp (-(s.1 * t)) *
        (∫ z, clampedEnvGenerator hd lam B F (Carriers.reducedObservationAt t.toNNReal z)
          ∂(Carriers.annealedCoordinateJoint Q.measure P op)) =
        s.1 * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s.1 * t)) *
          Density.observationMean Q.measure P op (clampedEnvGenerator hd lam B F) t := by
      rw [← integral_const_mul]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [Density.observationMean]
      ring
    rw [hpull]
    exact Clock.laplace_eq_laplace_primitive _
      (Density.measurable_integral_reducedObservationAt Q.measure P op _ hGm) B
      (fun t => Density.abs_integral_reducedObservationAt_le Q.measure P op _ hGB t) s.2
  have hρint : Integrable rho (Measure.map reduce Q.measure) :=
    Integrable.of_integral_ne_zero (by rw [hone]; exact one_ne_zero)
  have hρF : Integrable (fun w => rho w * F w) (Measure.map reduce Q.measure) :=
    hρint.mul_bdd hFm.aestronglyMeasurable
      (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hFB w)
  have hsplit : ∫ w, rho w * (F w - c) ∂(Measure.map reduce Q.measure) =
      (∫ w, rho w * F w ∂(Measure.map reduce Q.measure)) - c := by
    have e : (fun w => rho w * (F w - c)) = fun w => rho w * F w - rho w * c :=
      funext fun w => mul_sub _ _ _
    rw [e, integral_sub hρF (hρint.mul_const c), integral_mul_const, hone, one_mul]
  rw [hY, ← mul_sub, ← hsplit, hX]
  ring

/-! ## The weak divergence of the flux of a horizontal test -/

/-- The flux `a D F` of a horizontal test, `Φ_k = ∑_j a_{jk}(0) D_j F`. -/
def testFlux (F : FieldPair d → ℝ) (w : FieldPair d) : Vec d :=
  fun k => ∑ j, w.1 0 j k * horizontalDerivative j F w

/-- The pointwise divergence of the flux, `∑_k ∑_j (∂_k a_{jk}(0) D_j F + a_{jk}(0) D_k D_j F)`. -/
def testFluxDiv (F : FieldPair d → ℝ) (w : FieldPair d) : ℝ :=
  ∑ k, ∑ j, (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
    w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w)

theorem envGenerator_eq_testFluxDiv (hd : 2 ≤ d) (lam : ℝ) (F : FieldPair d → ℝ)
    (w : FieldPair d) :
    envGenerator hd lam F w = (1 / 2) * testFluxDiv F w +
      lam * ∑ j, w.1 0 j (firstCoordinateIndex hd) * horizontalDerivative j F w := rfl

theorem orbit_fluxEntry_eq (F : FieldPair d → ℝ) (j k : Fin d) (w : FieldPair d) :
    (fun y => (translate y w).1 0 j k * horizontalDerivative j F (translate y w)) =
      fun y => w.1 y j k * orbit (horizontalDerivative j F) w y := by
  funext y
  rw [translate_matrix, add_zero]
  rfl

theorem differentiableAt_orbit_fluxEntry {F : FieldPair d → ℝ} (hF : IsHorizontalTest F)
    (j k : Fin d) (w : FieldPair d) (hdw : DifferentiableAt ℝ (fun y => w.1 y j k) 0) :
    DifferentiableAt ℝ
      (fun y => (translate y w).1 0 j k * horizontalDerivative j F (translate y w)) 0 := by
  rw [orbit_fluxEntry_eq]
  exact hdw.mul ((((hF.horizontalDerivative j).2.1 w).differentiable (by simp)).differentiableAt)

/-- The product rule for the orbit of one flux entry, at a point where the coefficient entry is
differentiable. -/
theorem fderiv_orbit_fluxEntry {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) (j k : Fin d)
    (w : FieldPair d) (hdw : DifferentiableAt ℝ (fun y => w.1 y j k) 0) :
    fderiv ℝ (fun y => (translate y w).1 0 j k * horizontalDerivative j F (translate y w)) 0
        (unitVector k) =
      fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
        w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w := by
  have hg : DifferentiableAt ℝ (orbit (horizontalDerivative j F) w) 0 :=
    (((hF.horizontalDerivative j).2.1 w).differentiable (by simp)).differentiableAt
  have hfd : HasFDerivAt (fun y => w.1 y j k * orbit (EinsteinRelation.horizontalDerivative j F) w y)
      (w.1 0 j k • fderiv ℝ (orbit (EinsteinRelation.horizontalDerivative j F) w) 0 +
        orbit (EinsteinRelation.horizontalDerivative j F) w 0 • fderiv ℝ (fun y => w.1 y j k) 0) 0 :=
    hdw.hasFDerivAt.mul hg.hasFDerivAt
  rw [orbit_fluxEntry_eq, hfd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    orbit_zero]
  have h0 : fderiv ℝ (orbit (horizontalDerivative j F) w) 0 (unitVector k) =
      horizontalDerivative k (horizontalDerivative j F) w := rfl
  rw [h0]
  ring

/-- The orbit increments of one flux entry are Lipschitz in the step. -/
theorem abs_fluxEntry_increment_le {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {M1 M2 : ℝ}
    (hb1 : ∀ w x j, |fderiv ℝ (orbit F w) x (unitVector j)| ≤ M1)
    (hb2 : ∀ w x j k,
      |fderiv ℝ (fun y => fderiv ℝ (orbit F w) y (unitVector j)) x (unitVector k)| ≤ M2)
    {L B : ℝ} (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (j k : Fin d) (w : FieldPair d)
    (hinc : ∀ t : ℝ, |w.1 (-(t • unitVector k)) j k - w.1 0 j k| ≤ L * |t|)
    (hbd : |w.1 0 j k| ≤ B) (t : ℝ) :
    |(translate (-(t • unitVector k)) w).1 0 j k *
        horizontalDerivative j F (translate (-(t • unitVector k)) w) -
      w.1 0 j k * horizontalDerivative j F w| ≤
      (L * M1 + B * (((d * M2).toNNReal : ℝ) * ‖unitVector (d := d) k‖)) * |t| := by
  set s : Vec d := -(t • unitVector k) with hsdef
  have hA : (translate s w).1 0 j k = w.1 s j k := by rw [translate_matrix, add_zero]
  have horb : orbit (EinsteinRelation.horizontalDerivative j F) w =
      fun y => fderiv ℝ (orbit F w) y (unitVector j) := by
    rw [orbit_horizontalDerivative]; rfl
  have hus : ContDiff ℝ (⊤ : ℕ∞) (orbit F w) := hF.2.1 w
  have hdiff : Differentiable ℝ fun y => fderiv ℝ (orbit F w) y (unitVector j) :=
    ((hus.fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiff_const).differentiable one_ne_zero
  have hLip := lipschitzWith_of_coordinateDerivative_le hdiff fun x k => hb2 w x j k
  have hgs : horizontalDerivative j F (translate s w) = fderiv ℝ (orbit F w) s (unitVector j) := by
    show orbit (EinsteinRelation.horizontalDerivative j F) w s = _
    rw [horb]
  have hg0 : horizontalDerivative j F w = fderiv ℝ (orbit F w) 0 (unitVector j) := by
    rw [← orbit_zero (EinsteinRelation.horizontalDerivative j F) w, horb]
  have hgL : |fderiv ℝ (orbit F w) s (unitVector j) - fderiv ℝ (orbit F w) 0 (unitVector j)| ≤
      ((d * M2).toNNReal : ℝ) * (|t| * ‖unitVector (d := d) k‖) := by
    have h := hLip.dist_le_mul s 0
    rw [Real.dist_eq, dist_eq_norm, sub_zero, hsdef, norm_neg, norm_smul, Real.norm_eq_abs] at h
    exact h
  have hM1s := hb1 w s j
  rw [hA, hgs, hg0]
  have hsplit : w.1 s j k * fderiv ℝ (orbit F w) s (unitVector j) -
      w.1 0 j k * fderiv ℝ (orbit F w) 0 (unitVector j) =
      (w.1 s j k - w.1 0 j k) * fderiv ℝ (orbit F w) s (unitVector j) +
        w.1 0 j k * (fderiv ℝ (orbit F w) s (unitVector j) -
          fderiv ℝ (orbit F w) 0 (unitVector j)) := by ring
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have h1 : |w.1 s j k - w.1 0 j k| * |fderiv ℝ (orbit F w) s (unitVector j)| ≤ L * |t| * M1 :=
    mul_le_mul (hinc t) hM1s (abs_nonneg _) (mul_nonneg hL0 (abs_nonneg _))
  have h2 : |w.1 0 j k| * |fderiv ℝ (orbit F w) s (unitVector j) -
      fderiv ℝ (orbit F w) 0 (unitVector j)| ≤
      B * (((d * M2).toNNReal : ℝ) * (|t| * ‖unitVector (d := d) k‖)) :=
    mul_le_mul hbd hgL (abs_nonneg _) hB0
  calc _ ≤ L * |t| * M1 + B * (((d * M2).toNNReal : ℝ) * (|t| * ‖unitVector (d := d) k‖)) :=
        add_le_add h1 h2
    _ = (L * M1 + B * (((d * M2).toNNReal : ℝ) * ‖unitVector (d := d) k‖)) * |t| := by ring

/-- **The weak divergence of the flux of a horizontal test** under the reduced reference law:
`D · (a D F) = testFluxDiv F` (`paper/main.tex` 245-249). -/
theorem hasWeakHorizontalDivergence_testFlux {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) :
    HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ (testFlux F)
      (testFluxDiv F) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  obtain ⟨L, Ba, hL0, hBa0, hae⟩ := DriftH5.ae_entry_regular Q hQ
  obtain ⟨M0, M1, M2, hM1, hM2, -, hb1, hb2⟩ := hF.exists_bounds
  have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  have hg1 : ∀ w j, |horizontalDerivative j F w| ≤ M1 := fun w j => hb1 w 0 j
  have hg2 : ∀ w j k, |horizontalDerivative k (horizontalDerivative j F) w| ≤ M2 := by
    intro w j k
    show |fderiv ℝ (orbit (EinsteinRelation.horizontalDerivative j F) w) 0 (unitVector k)| ≤ M2
    rw [orbit_horizontalDerivative]
    exact hb2 w 0 j k
  have hφm : ∀ j k : Fin d,
      Measurable fun w : FieldPair d => w.1 0 j k * horizontalDerivative j F w := fun j k =>
    (hentry j k).mul (hF.measurable_derivative j)
  have hψm : ∀ j k : Fin d, Measurable fun w : FieldPair d =>
      fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
        w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w := fun j k =>
    ((measurable_fderiv_entry_zero j k _).mul (hF.measurable_derivative j)).add
      ((hentry j k).mul ((hF.horizontalDerivative j).measurable_derivative k))
  have hφb : ∀ j k : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      ‖w.1 0 j k * horizontalDerivative j F w‖ ≤ Ba * M1 := fun j k => by
    filter_upwards [hae] with w hw
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hw j k).2.1 (hg1 w j) (abs_nonneg _) hBa0
  have hψb : ∀ j k : Fin d, ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
      ‖fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
        w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w‖ ≤ L * M1 + Ba * M2 :=
    fun j k => by
      filter_upwards [hae] with w hw
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [abs_mul]; exact mul_le_mul ((hw j k).2.2.2 k) (hg1 w j) (abs_nonneg _) hL0
      · rw [abs_mul]; exact mul_le_mul (hw j k).2.1 (hg2 w j k) (abs_nonneg _) hBa0
  refine ⟨fun k => ?_, ?_, fun G _hG DG hDG => ?_⟩
  · have e : (fun w => testFlux F w k) =
        fun w => ∑ j, w.1 0 j k * horizontalDerivative j F w := rfl
    rw [e]
    exact integrable_finset_sum _ fun j _ =>
      Integrable.of_bound (hφm j k).aestronglyMeasurable (Ba * M1) (hφb j k)
  · have e : testFluxDiv F = fun w => ∑ k, ∑ j,
        (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
          w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) := rfl
    rw [e]
    exact integrable_finset_sum _ fun k _ => integrable_finset_sum _ fun j _ =>
      Integrable.of_bound (hψm j k).aestronglyMeasurable (L * M1 + Ba * M2) (hψb j k)
  have hGi : Integrable (⇑G) (Carriers.reducedReferenceLaw Q) :=
    (Lp.memLp G).integrable (by norm_num)
  have hDGi : ∀ k, Integrable (⇑(DG k)) (Carriers.reducedReferenceLaw Q) := fun k =>
    (Lp.memLp (DG k)).integrable (by norm_num)
  have hI1 : ∀ k j : Fin d, Integrable
      (fun w => (w.1 0 j k * horizontalDerivative j F w) * DG k w)
      (Carriers.reducedReferenceLaw Q) := fun k j =>
    Integrable.bdd_mul (hDGi k) (hφm j k).aestronglyMeasurable (hφb j k)
  have hI2 : ∀ k j : Fin d, Integrable
      (fun w => (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
        w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) * G w)
      (Carriers.reducedReferenceLaw Q) := fun k j =>
    Integrable.bdd_mul hGi (hψm j k).aestronglyMeasurable (hψb j k)
  have key : ∀ j k : Fin d,
      ∫ w, (w.1 0 j k * horizontalDerivative j F w) * DG k w ∂Carriers.reducedReferenceLaw Q =
        -∫ w, (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
          w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) * G w
            ∂Carriers.reducedReferenceLaw Q := by
    intro j k
    have hK0 : 0 ≤ L * M1 + Ba * (((d * M2).toNNReal : ℝ) * ‖unitVector (d := d) k‖) :=
      add_nonneg (mul_nonneg hL0 hM1)
        (mul_nonneg hBa0 (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)))
    have hK : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ t : ℝ,
        |(fun w : FieldPair d => w.1 0 j k * horizontalDerivative j F w)
            (translate (-(t • unitVector k)) w) -
          (fun w : FieldPair d => w.1 0 j k * horizontalDerivative j F w) w| ≤
          (L * M1 + Ba * (((d * M2).toNNReal : ℝ) * ‖unitVector (d := d) k‖)) * |t| := by
      filter_upwards [hae] with w hw
      exact fun t => abs_fluxEntry_increment_le hF hb1 hb2 hL0 hBa0 j k w ((hw j k).1 k)
        (hw j k).2.1 t
    have hB : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q,
        |(fun w : FieldPair d => w.1 0 j k * horizontalDerivative j F w) w| ≤ Ba * M1 := by
      filter_upwards [hφb j k] with w hw
      rwa [Real.norm_eq_abs] at hw
    have hdiff : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, DifferentiableAt ℝ
        (fun y => (fun w : FieldPair d => w.1 0 j k * horizontalDerivative j F w)
          (translate y w)) 0 := by
      filter_upwards [hae] with w hw
      exact differentiableAt_orbit_fluxEntry hF j k w (hw j k).2.2.1
    have h := DriftH5.integral_mul_deriv_of_orbit hQ k (hφm j k) hK0 hK hB hdiff G (DG k) (hDG k)
    rw [h]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae] with w hw
    show fderiv ℝ (fun y => (translate y w).1 0 j k * horizontalDerivative j F (translate y w)) 0
        (unitVector k) * G w = _
    rw [fderiv_orbit_fluxEntry hF j k w (hw j k).2.2.1]
  have hL : ∫ w, (∑ k, testFlux F w k * DG k w) ∂Carriers.reducedReferenceLaw Q =
      ∑ k, ∑ j, ∫ w, (w.1 0 j k * horizontalDerivative j F w) * DG k w
        ∂Carriers.reducedReferenceLaw Q := by
    have e : (fun w => ∑ k, testFlux F w k * DG k w) =
        fun w => ∑ k, ∑ j, (w.1 0 j k * horizontalDerivative j F w) * DG k w :=
      funext fun w => Finset.sum_congr rfl fun k _ => by simp only [testFlux, Finset.sum_mul]
    rw [e, integral_finset_sum (f := fun k w => ∑ j, (w.1 0 j k * horizontalDerivative j F w) *
      DG k w) _ fun k _ => integrable_finset_sum _ fun j _ => hI1 k j]
    exact Finset.sum_congr rfl fun k _ => integral_finset_sum _ fun j _ => hI1 k j
  have hR : ∫ w, testFluxDiv F w * G w ∂Carriers.reducedReferenceLaw Q =
      ∑ k, ∑ j, ∫ w, (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) *
        horizontalDerivative j F w +
          w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) * G w
        ∂Carriers.reducedReferenceLaw Q := by
    have e : (fun w => testFluxDiv F w * G w) = fun w => ∑ k, ∑ j,
        (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
          w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) * G w :=
      funext fun w => by simp only [testFluxDiv, Finset.sum_mul]
    rw [e, integral_finset_sum (f := fun k w => ∑ j,
      (fderiv ℝ (fun y => w.1 y j k) 0 (unitVector k) * horizontalDerivative j F w +
        w.1 0 j k * horizontalDerivative k (horizontalDerivative j F) w) * G w)
      _ fun k _ => integrable_finset_sum _ fun j _ => hI2 k j]
    exact Finset.sum_congr rfl fun k _ => integral_finset_sum _ fun j _ => hI2 k j
  rw [hL, hR, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => key j k]
  simp only [Finset.sum_neg_distrib]

end EinsteinRelation
