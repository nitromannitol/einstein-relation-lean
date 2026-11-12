import EinsteinRelation.Sharpness.SharpExampleFromSteps
import EinsteinRelation.Sharpness.HarmonicField
import EinsteinRelation.Sharpness.SharpEnvironmentLaw
import EinsteinRelation.Mobility.QuenchedDriftFromFukushima
import Mathlib.Analysis.PSeries

/-! # Step 2 of Proposition 7.1 from the Fukushima decomposition

Source: `paper/main.tex` 1244-1250. For the sharp environment, `u(x) = x₁ + ψ(x)` satisfies
`a ∇u = e₁` (`eq.sharp-harmonic`), so its weak drift under the force-`λ` Dirichlet form is the
constant `λ`. `FukushimaDecompositionInput` then gives `E₀[(u(Y_t) - u(Y_0) - λ t)²] ≤ K G² t`.
Along `t = (n+1)²` the second moments are summable, so `(u(Y_t) - u(Y_0))/t → λ` almost surely.
Since `ψ` is bounded, every quenched velocity `v` has `v·e₁ = λ` (`sharpVelocityStep_of_fukushima`).
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

open EinsteinRelation.External.GantertSection7Support

noncomputable section

namespace EinsteinRelation.Sharpness

variable {d : ℕ}

/-- A compactly supported `C¹` function has zero mean derivative. -/
theorem integral_fderiv_unitVector_eq_zero {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (k : Fin d) : ∫ x, fderiv ℝ g x (unitVector k) = 0 := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg le_rfl
  have h := (LipschitzWith.const (α := Vec d) (1 : ℝ)).integral_lineDeriv_mul_eq
    (μ := volume) hC hgc (unitVector k)
  have hl1 : ∀ x, lineDeriv ℝ (fun _ : Vec d => (1 : ℝ)) x (unitVector k) = 0 := fun x => by
    simp [lineDeriv]
  have hl2 : ∀ x, lineDeriv ℝ g x (-unitVector k) = -fderiv ℝ g x (unitVector k) := fun x => by
    rw [((hg.differentiable le_rfl) x).lineDeriv_eq_fderiv, map_neg]
  simp only [hl1, zero_mul, integral_zero, hl2, mul_one, integral_neg] at h
  linarith

/-- The reduced coefficient of the sharp physical environment is the constructed coefficient. -/
theorem reducedCoefficient_physicalEnvironment (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (ha : Continuous (physicalCoefficientField i δ ψ)) (hV : Continuous (potentialField i δ ψ))
    (x : Vec d) (hμ : 0 < densityField i δ ψ x) :
    reducedCoefficient (physicalEnvironment i δ ψ ha hV) x = coefficientField i ψ x := by
  unfold reducedCoefficient clockDensity
  exact reduce_physicalCoefficientField i δ ψ x hμ

private theorem sv_dot_mulVec_symm (A : Mat d) (hA : A.transpose = A) (w z : Vec d) :
    dot w (A.mulVec z) = dot (A.mulVec w) z := by
  simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  have h := congrFun (congrFun hA j) k
  simp only [Matrix.transpose_apply] at h
  rw [← h]
  ring

/-- **The weak drift of `x₁ + ψ` is `λ`.** For a smooth `ψ` whose coefficient field satisfies the
harmonic identity `a(e₁ + ∇ψ) = e₁`, the zero-potential pair with coefficient `a` has
`½ ∫ ∇u · a ∇v dm_λ = -∫ λ v dm_λ` for `u = x₁ + ψ`. -/
theorem isWeakDrift_coord_add (hd : 2 ≤ d) {ω : FieldPair d} (hV : ∀ x, ω.2 x = 0)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (lam : ℝ)
    (ha : ∀ x, (ω.1 x).transpose = ω.1 x)
    (hharm : ∀ x, (ω.1 x).mulVec (unitVector (firstCoordinateIndex hd) + gradient ψ x) =
      unitVector (firstCoordinateIndex hd)) :
    IsWeakDrift hd ω lam (fun x => x (firstCoordinateIndex hd) + ψ x) (fun _ => lam) := by
  intro v hv hvc
  set i₀ := firstCoordinateIndex hd with hi₀
  rw [integral_physicalReversibleMeasure_of_zero_potential hd hV,
    integral_physicalReversibleMeasure_of_zero_potential hd hV]
  set ρ := physicalForceWeight hd lam with hρdef
  have hgradu : ∀ x, spatialGradient (fun x => x i₀ + ψ x) x = unitVector i₀ + gradient ψ x := by
    intro x
    funext k
    have hf : HasFDerivAt (fun x : Vec d => x i₀ + ψ x)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i₀ + fderiv ℝ ψ x) x :=
      (hasFDerivAt_apply i₀ x).add ((hψ.differentiable le_rfl) x).hasFDerivAt
    simp only [spatialGradient, Pi.add_apply, gradient, coordinateDerivative]
    rw [hf.fderiv]
    simp [unitVector, Pi.single_apply, eq_comm]
  have hpt : ∀ x, ρ x * ((1 / 2 : ℝ) * dot (spatialGradient (fun x => x i₀ + ψ x) x)
      ((ω.1 x).mulVec (spatialGradient v x))) = (1 / 2 : ℝ) * (ρ x * fderiv ℝ v x (unitVector i₀)) := by
    intro x
    rw [hgradu, sv_dot_mulVec_symm _ (ha x), hharm]
    simp [dot, spatialGradient, unitVector, Pi.single_apply]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  -- Integration by parts against the weight.
  set g : Vec d → ℝ := fun x => ρ x * v x with hgdef
  have hg : ContDiff ℝ 1 g := (contDiff_physicalForceWeight hd lam).mul hv
  have hgc : HasCompactSupport g := hvc.mul_left
  have hdg : ∀ x, fderiv ℝ g x (unitVector i₀) =
      ρ x * fderiv ℝ v x (unitVector i₀) + 2 * lam * (ρ x * v x) := by
    intro x
    have hd' : HasFDerivAt g (ρ x • fderiv ℝ v x + v x • (ρ x •
        ((2 * lam) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i₀))) x :=
      (hasFDerivAt_physicalForceWeight hd lam x).mul ((hv.differentiable le_rfl) x).hasFDerivAt
    rw [hd'.fderiv]
    simp [smul_eq_mul, unitVector]
    ring
  have h0 := integral_fderiv_unitVector_eq_zero hg hgc i₀
  have hI1 : Integrable fun x => ρ x * fderiv ℝ v x (unitVector i₀) :=
    ((physicalForceWeight_continuous hd lam).mul
      ((hv.continuous_fderiv le_rfl).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hvc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector i₀)) rfl).mul_left
  have hI2 : Integrable fun x => ρ x * v x :=
    hg.continuous.integrable_of_hasCompactSupport hgc
  rw [integral_congr_ae (ae_of_all _ hdg), integral_add hI1 ((hI2.const_mul _)),
    integral_const_mul] at h0
  have hrhs : ∫ x, ρ x * (lam * v x) = lam * ∫ x, ρ x * v x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  rw [hrhs]
  linarith

private theorem sv_abs_coord_le (v : Vec d) (j : Fin d) : |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

private theorem sv_euclid_unitVector (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

/-- The gradient of `x ↦ x_i + ψ(x)`. -/
theorem spatialGradient_coord_add {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (i : Fin d) (x : Vec d) :
    spatialGradient (fun x => x i + ψ x) x = unitVector i + gradient ψ x := by
  funext k
  have hf : HasFDerivAt (fun x : Vec d => x i + ψ x)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i + fderiv ℝ ψ x) x :=
    (hasFDerivAt_apply i x).add ((hψ.differentiable le_rfl) x).hasFDerivAt
  simp only [spatialGradient, Pi.add_apply, gradient, coordinateDerivative]
  rw [hf.fderiv]
  simp [unitVector, Pi.single_apply, eq_comm]

/-- Summable second moments give almost-sure convergence to zero. -/
theorem ae_tendsto_zero_of_sum_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (X : ℕ → Ω → ℝ) (hX : ∀ n, AEStronglyMeasurable (X n) μ) (c : ℕ → ℝ)
    (hint : ∀ n, Integrable (fun ω => X n ω ^ 2) μ)
    (hle : ∀ n, ∫ ω, X n ω ^ 2 ∂μ ≤ c n) (hc : Summable c) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hc0 : ∀ n, 0 ≤ c n := fun n => (integral_nonneg fun ω => sq_nonneg (X n ω)).trans (hle n)
  have hlin : ∀ n, ∫⁻ ω, ENNReal.ofReal (X n ω ^ 2) ∂μ ≤ ENNReal.ofReal (c n) := fun n => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n) (ae_of_all _ fun ω => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (hle n)
  have hmeas : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal (X n ω ^ 2)) μ := fun n =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hX n).aemeasurable.pow_const 2)
  have htot : ∫⁻ ω, ∑' n, ENNReal.ofReal (X n ω ^ 2) ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hlin)
    rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hc]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum hmeas) htot] with ω hω
  have h1 : Tendsto (fun n => ENNReal.ofReal (X n ω ^ 2)) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun n => X n ω ^ 2) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa [Function.comp_def, ENNReal.toReal_ofReal (sq_nonneg _)] using this
  have h3 : Tendsto (fun n => |X n ω|) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp h2
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using this
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h3

/-- **Step 2 of Proposition 7.1** (`paper/main.tex` 1244-1250): for the sharp law and every GMP
reduced family, every quenched velocity at force `0 < λ ≤ 1` has first coordinate `λ`. -/
theorem sharpVelocityStep_of_fukushima (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) :
    SharpVelocityStep hd := by
  intro Λ₀ r₀ δ Q hsharp P' hP' lam hl0 hl1 v hv
  obtain ⟨-, ε, P, hgrad, hμ, -, hQP⟩ := hsharp
  set i₀ : Fin d := ⟨0, by omega⟩ with hi₀
  set pair := sharpPhysicalPair i₀ δ ε hgrad hμ with hpairdef
  have hpm : Measurable pair := measurable_sharpPhysicalPair i₀ δ ε hgrad hμ
  haveI : IsProbabilityMeasure P := by
    constructor
    have h := measure_univ (μ := Q.measure)
    rw [hQP, Measure.map_apply hpm MeasurableSet.univ, Set.preimage_univ] at h
    exact h
  have hev : ∀ᵐ ω ∂Q.measure, (∀ᵐ γ ∂(originLaw (P' lam) ω), HasPathVelocity γ v) ∧
      ∃ hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω),
        ∃ r : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀)
          (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω) hω'
          lam hl0.le hl1, P' lam (0, ω) = r.pathLaw 0 :=
    hv.and (hP' lam hl0.le hl1)
  rw [hQP] at hev
  obtain ⟨W, hvel, hω', r, hr⟩ := (ae_of_ae_map hpm.aemeasurable hev).exists
  set ω := pair W with hωdef
  set ψ : Vec d → ℝ := fun y => ε * seedField d W y with hψdef
  have hdens : ∀ x, 0 < densityField i₀ δ ψ x := fun x => by linarith [(hμ W x).1]
  have hred : ∀ x, (zeroPotentialReducedPair ω).1 x = coefficientField i₀ ψ x := fun x =>
    reducedCoefficient_physicalEnvironment i₀ δ ψ _ _ x (hdens x)
  have hjac : ∀ x, jacobianFactor i₀ (gradient ψ x) ≠ 0 := fun x => by
    have h := (abs_le.mp ((sv_abs_coord_le (gradient ψ x) i₀).trans (hgrad W x))).1
    unfold jacobianFactor
    linarith
  have ha : ∀ x, ((zeroPotentialReducedPair ω).1 x).transpose = (zeroPotentialReducedPair ω).1 x :=
    fun x => by rw [hred]; exact coefficient_transpose i₀ _
  have hharm : ∀ x, ((zeroPotentialReducedPair ω).1 x).mulVec
      (unitVector (firstCoordinateIndex hd) + gradient ψ x) = unitVector (firstCoordinateIndex hd) :=
    fun x => by rw [hred]; exact coefficientField_harmonic i₀ ψ x (hjac x)
  have hψ1 : ContDiff ℝ 1 ψ := (sharpSeed_contDiff ε W).of_le (by exact_mod_cast le_top)
  have hψb : ∀ y, |ψ y| ≤ |ε| := fun y => by
    simp only [hψdef, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (abs_seedField_le_one d W y)
  set u : Vec d → ℝ := fun x => x (firstCoordinateIndex hd) + ψ x with hudef
  have hu1 : ContDiff ℝ 1 u := (contDiff_apply ℝ ℝ _).add hψ1
  have hG : ∀ x, euclideanNorm (spatialGradient u x) ≤ 5 / 4 := fun x => by
    rw [spatialGradient_coord_add hψ1]
    refine (TimeChange.euclideanNorm_add_le _ _).trans ?_
    rw [sv_euclid_unitVector]
    have := hgrad W x
    linarith
  have hFOTω := hFOT d hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
    (zeroPotentialReducedPair ω) hω' lam hl0.le hl1 r u (5 / 4) hu1 hG (fun _ => lam)
    measurable_const ⟨|lam|, fun _ => le_rfl⟩
    (isWeakDrift_coord_add hd (fun _ => rfl) hψ1 lam ha hharm)
  -- Borel–Cantelli along `t = (n+1)²`.
  set K' : ℝ := sourceReducedBound Λ₀ * (5 / 4) ^ 2 with hK'def
  set T : ℕ → ℝ := fun n => ((n : ℝ) + 1) ^ 2 with hTdef
  have hT : ∀ n, 0 < T n := fun n => by positivity
  set X : ℕ → Path d → ℝ := fun n γ => pathMartingalePart u (fun _ => lam) (T n) γ / T n
    with hXdef
  haveI := r.pathLaw_isMarkovKernel
  have hXae : ∀ᵐ γ ∂r.pathLaw 0, Tendsto (fun n => X n γ) atTop (𝓝 0) := by
    refine ae_tendsto_zero_of_sum_integral_sq X (fun n => ?_) (fun n => K' / ((n : ℝ) + 1) ^ 2)
      (fun n => ?_) (fun n => ?_) ?_
    · exact (continuous_id.div_const (T n)).comp_aestronglyMeasurable
        (hFOTω (T n) (hT n).le).1.aestronglyMeasurable
    · have := ((hFOTω (T n) (hT n).le).1.integrable_sq).div_const (T n ^ 2)
      refine this.congr (ae_of_all _ fun γ => ?_)
      simp only [hXdef]
      rw [div_pow]
    · have hb := (hFOTω (T n) (hT n).le).2.1
      have heq : ∫ γ, X n γ ^ 2 ∂r.pathLaw 0 =
          (∫ γ, pathMartingalePart u (fun _ => lam) (T n) γ ^ 2 ∂r.pathLaw 0) / T n ^ 2 := by
        rw [← integral_div]
        exact integral_congr_ae (ae_of_all _ fun γ => by simp only [hXdef, div_pow])
      rw [heq, div_le_iff₀ (by positivity)]
      calc ∫ γ, pathMartingalePart u (fun _ => lam) (T n) γ ^ 2 ∂r.pathLaw 0
          ≤ sourceReducedBound Λ₀ * (5 / 4) ^ 2 * T n := hb
        _ = K' / ((n : ℝ) + 1) ^ 2 * T n ^ 2 := by
            simp only [hK'def, hTdef]
            field_simp
    · have h := (summable_nat_add_iff 1).mpr
        ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
      have h' : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        refine h.congr fun n => ?_
        push_cast
        ring
      simpa [div_eq_mul_one_div K'] using h'.mul_left K'
  have hvel' : ∀ᵐ γ ∂r.pathLaw 0, HasPathVelocity γ v := by
    rw [← hr]; exact hvel
  obtain ⟨γ, hγv, hγX, hγ0⟩ := (hvel'.and (hXae.and (r.pathLaw_starts_at 0))).exists
  -- The deterministic limit.
  have hγ0' : γ 0 = 0 := hγ0
  have hTtop : Tendsto T atTop atTop := by
    have : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp this
  have hTnn : Tendsto (fun n => (T n).toNNReal) atTop atTop :=
    (tendsto_real_toNNReal_atTop).comp hTtop
  have hcoord : Tendsto (fun n => (T n)⁻¹ * γ (T n).toNNReal (firstCoordinateIndex hd)) atTop
      (𝓝 (v (firstCoordinateIndex hd))) := by
    have h1 := ((continuous_apply (firstCoordinateIndex hd)).tendsto v).comp (hγv.comp hTnn)
    refine h1.congr fun n => ?_
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul,
      Real.coe_toNNReal _ (hT n).le]
  have hψlim : Tendsto (fun n => (T n)⁻¹ * ψ (γ (T n).toNNReal)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n => (T n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hTtop
    have hb : Tendsto (fun n => |ε| * (T n)⁻¹) atTop (𝓝 0) := by
      simpa using hinv.const_mul |ε|
    refine squeeze_zero_norm (fun n => ?_) hb
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.mpr (hT n)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hψb _) (inv_pos.mpr (hT n)).le
  have hconst : Tendsto (fun n => (T n)⁻¹ * u (γ 0)) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp hTtop).mul_const (u (γ 0))
  have hXform : ∀ n, X n γ = (T n)⁻¹ * γ (T n).toNNReal (firstCoordinateIndex hd) +
      (T n)⁻¹ * ψ (γ (T n).toNNReal) - (T n)⁻¹ * u (γ 0) - lam := by
    intro n
    have hTn := (hT n).ne'
    simp only [hXdef, pathMartingalePart, intervalIntegral.integral_const, sub_zero, smul_eq_mul,
      hudef, hγ0']
    field_simp
  have hlimX : Tendsto (fun n => X n γ) atTop
      (𝓝 (v (firstCoordinateIndex hd) + 0 - 0 - lam)) := by
    simp only [hXform]
    exact ((hcoord.add hψlim).sub hconst).sub tendsto_const_nhds
  have hv0 : v (firstCoordinateIndex hd) - lam = 0 := by
    have := tendsto_nhds_unique hlimX hγX
    linarith
  have hdot : dot v (unitVector (⟨0, by omega⟩ : Fin d)) = v (firstCoordinateIndex hd) := by
    simp [dot, unitVector, Pi.single_apply, firstCoordinateIndex]
  rw [hdot]
  linarith

end EinsteinRelation.Sharpness
