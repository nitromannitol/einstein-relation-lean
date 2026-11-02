import EinsteinRelation.Mobility.DriftDecompositionFromSteps
import EinsteinRelation.Mobility.DriftWeakDivergence
import EinsteinRelation.Mobility.DriftBoundStepProof
import EinsteinRelation.Density.LaplaceDensityExistence
import EinsteinRelation.Correctors.EllipticOperatorBound
import Mathlib.Analysis.Calculus.Rademacher

/-! # `QuenchedDriftMartingaleStep` from the Fukushima decomposition of a coordinate

Source: `paper/main.tex` 1140-1148 and Fukushima, Oshima and Takeda, *Dirichlet Forms and Symmetric
Markov Processes*, 2nd revised and extended edition, de Gruyter 2011, Theorem 5.5.5, p. 275.

The cited input `FukushimaDecompositionInput` is FOT Theorem 5.5.5 for a `C¹` function `u` with
bounded gradient on a GMP Section 7 realization: if a bounded Borel function `b` satisfies
`E^{λ,ω}(u, v) = -∫ b v dm_λ` for every compactly supported `C¹` function `v` (`IsWeakDrift`), then
`u(Y_t) - u(Y_0) - ∫₀ᵗ b(Y_s) ds` is square integrable from the origin with second moment at most
`K |∇u|²_∞ t`. This file proves, for the coordinate `u(x) = x_i`:

* `isWeakDrift_cdiv`: the pointwise spatial divergence `DriftH5.cdiv` gives such a drift,
  by integration by parts of the Lipschitz coefficient against the weight `e^{2λ x₁}`;
* `quenchedDriftMartingaleStep_of_fukushima`: the step for every weak horizontal divergence, since
  any two versions agree almost everywhere under the reduced law, and the reduced environment seen
  at positive times avoids reduced-null sets.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

open EinsteinRelation.External.GantertSection7Support

noncomputable section

namespace EinsteinRelation

open Carriers

variable {d : ℕ}

/-! ## The cited input -/

/-- The spatial gradient `∇u(x)` in coordinates. -/
def spatialGradient (u : Vec d → ℝ) (x : Vec d) : Vec d := fun k => fderiv ℝ u x (unitVector k)

/-- The martingale part `u(γ_t) - u(γ_0) - ∫₀ᵗ b(γ_s) ds` of a path for a function `u` with drift
`b`. -/
def pathMartingalePart (u b : Vec d → ℝ) (t : ℝ) (γ : Path d) : ℝ :=
  u (γ t.toNNReal) - u (γ 0) - ∫ s in (0 : ℝ)..t, b (γ s.toNNReal)

/-- The coordinate martingale part `γ_t·e_i - ∫₀ᵗ b(γ_u) du` of a path for a spatial drift `b`. -/
def spatialMartingalePart (b : Vec d → ℝ) (i : Fin d) (t : ℝ) (γ : Path d) : ℝ :=
  γ t.toNNReal i - ∫ u in (0 : ℝ)..t, b (γ u.toNNReal)

/-- `b` is the drift of `u` in the weak sense:
`E^{λ,ω}(u, v) = ½ ∫ ∇u · a ∇v dm_λ = -∫ b v dm_λ` for every compactly supported `C¹` function
`v`, where `m_λ = physicalReversibleMeasure ω hd lam` is the reversible measure. -/
def IsWeakDrift (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) (u b : Vec d → ℝ) : Prop :=
  ∀ v : Vec d → ℝ, ContDiff ℝ 1 v → HasCompactSupport v →
    ∫ x, (1 / 2 : ℝ) * dot (spatialGradient u x) ((ω.1 x).mulVec (spatialGradient v x))
        ∂physicalReversibleMeasure ω hd lam =
      -∫ x, b x * v x ∂physicalReversibleMeasure ω hd lam

/-- **FOT Theorem 5.5.5 for a `C¹` function with bounded gradient** (Fukushima, Oshima and Takeda
2011, Theorem 5.5.5, p. 275, under the absolute continuity condition (4.2.9), p. 165; GMP 2012,
Section 7, p. 32, and Lemma 7.1, p. 33). For a regular pair `ω` with constant `K`, every GMP
Section 7 realization `r` at force `0 ≤ λ ≤ 1`, every `C¹` function `u` with `|∇u| ≤ G` and every
bounded Borel `b` that is the weak drift of `u`, the process `u(Y_t) - u(Y_0) - ∫₀ᵗ b(Y_s) ds` from
the origin is square integrable with second moment at most `K G² t` and mean zero.

FOT (5.5.8)-(5.5.9) give `u(Y_t) - u(Y_0) = M_t + ∫₀ᵗ b(Y_s) ds` almost surely from every starting
point, and (5.5.11) gives `E_x[M_{t∧τ_G}²] = E_x[∫₀^{t∧τ_G} ∇u·a∇u(Y_s) ds] ≤ K G² t` for every
relatively compact open `G ∋ x`; Fatou's lemma along balls `G ↑ ℝ^d` gives the bound at `t`.
(5.5.10) gives `E_x[M_{t∧τ_G}] = 0`; the uniform `L²` bound makes `M_{t∧τ_G}` uniformly integrable
along balls, so `E₀[M_t] = 0`. The heat-kernel density of the realization is (4.2.9). -/
def FukushimaDecompositionInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (K : ℝ) (hK : 1 ≤ K) (ω : FieldPair d) (hω : IsRegular K ω) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (r : GantertFixedEnvironmentRealization hd K hK ω hω lam h0 h1)
    (u : Vec d → ℝ) (G : ℝ), ContDiff ℝ 1 u → (∀ x, euclideanNorm (spatialGradient u x) ≤ G) →
    ∀ b : Vec d → ℝ, Measurable b → (∃ B : ℝ, ∀ x, |b x| ≤ B) → IsWeakDrift hd ω lam u b →
    ∀ t : ℝ, 0 ≤ t →
      MemLp (pathMartingalePart u b t) 2 (r.pathLaw 0) ∧
        ∫ γ, pathMartingalePart u b t γ ^ 2 ∂r.pathLaw 0 ≤ K * G ^ 2 * t ∧
        ∫ γ, pathMartingalePart u b t γ ∂r.pathLaw 0 = 0

/-! ## Euclidean helpers -/

private theorem qd_abs_coord_le_euclid (v : Vec d) (j : Fin d) : |v j| ≤ euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  have h := Finset.single_le_sum (f := fun k => v k * v k)
    (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)
  simpa only [sq] using h

private theorem qd_euclid_le_sum_abs (v : Vec d) : euclideanNorm v ≤ ∑ j, |v j| := by
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

private theorem qd_euclid_unitVector (i : Fin d) : euclideanNorm (unitVector i) = 1 := by
  change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem qd_mulVec_unitVector_apply (M : Mat d) (i k : Fin d) :
    (M.mulVec (unitVector i)) k = M k i := by
  simp [unitVector]

/-- Every entry of a regular coefficient is bounded by its ellipticity constant. -/
theorem abs_entry_le_of_isRegular {L : ℝ} {ω : FieldPair d} (hL : 0 < L) (hω : IsRegular L ω)
    (x : Vec d) (j i : Fin d) : |ω.1 x j i| ≤ L := by
  have h1 := Correctors.isElliptic_mulVec_euclideanNorm_le hL hω.1 x (unitVector i)
  have h2 := qd_abs_coord_le_euclid ((ω.1 x).mulVec (unitVector i)) j
  rw [qd_mulVec_unitVector_apply] at h2
  rw [qd_euclid_unitVector, mul_one] at h1
  exact h2.trans h1

/-- Every entry of a regular coefficient is Lipschitz for the supremum metric. -/
theorem lipschitzWith_entry_of_isRegular {L : ℝ} {ω : FieldPair d} (hL : 0 ≤ L)
    (hω : IsRegular L ω) (k i : Fin d) :
    LipschitzWith (L * d).toNNReal fun x => ω.1 x k i := by
  refine LipschitzWith.of_dist_le' fun x y => ?_
  rw [Real.dist_eq]
  have hsum : ∑ j, |(x - y) j| ≤ d * dist x y := by
    rw [dist_eq_norm]
    calc ∑ j, |(x - y) j| ≤ ∑ _j : Fin d, ‖x - y‖ :=
          Finset.sum_le_sum fun j _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (x - y) j
      _ = d * ‖x - y‖ := by simp
  have hlip := hω.2.2.1 x y (unitVector i)
  rw [qd_euclid_unitVector, mul_one] at hlip
  have hcoord := qd_abs_coord_le_euclid ((ω.1 x - ω.1 y).mulVec (unitVector i)) k
  rw [qd_mulVec_unitVector_apply, Matrix.sub_apply] at hcoord
  calc |ω.1 x k i - ω.1 y k i| ≤ L * euclideanNorm (x - y) := hcoord.trans hlip
    _ ≤ L * ∑ j, |(x - y) j| := mul_le_mul_of_nonneg_left (qd_euclid_le_sum_abs _) hL
    _ ≤ L * (d * dist x y) := mul_le_mul_of_nonneg_left hsum hL
    _ = L * d * dist x y := by ring

/-! ## The pointwise divergence is a weak coordinate drift -/

/-- The gradient of the coordinate `x ↦ x_i` is `e_i`. -/
theorem spatialGradient_coord (i : Fin d) (x : Vec d) :
    spatialGradient (fun y : Vec d => y i) x = unitVector i := by
  funext k
  simp only [spatialGradient]
  rw [show (fun y : Vec d => y i) = fun y => ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) i y from rfl, ContinuousLinearMap.fderiv]
  simp [unitVector, Pi.single_apply, eq_comm]

/-- The reversible density of a pair with zero potential is the force weight. -/
theorem physicalReversibleDensity_of_zero_potential (hd : 2 ≤ d) {ω : FieldPair d}
    (hV : ∀ x, ω.2 x = 0) (lam : ℝ) (x : Vec d) :
    physicalReversibleDensity ω hd lam x = physicalForceWeight hd lam x := by
  simp [physicalReversibleDensity, clockDensity, hV]

/-- Integrals against the reversible measure of a zero-potential pair are Lebesgue integrals with
the force weight. -/
theorem integral_physicalReversibleMeasure_of_zero_potential (hd : 2 ≤ d) {ω : FieldPair d}
    (hV : ∀ x, ω.2 x = 0) (lam : ℝ) (F : Vec d → ℝ) :
    ∫ x, F x ∂physicalReversibleMeasure ω hd lam = ∫ x, physicalForceWeight hd lam x * F x := by
  have hρ : Measurable fun x => (physicalForceWeight hd lam x).toNNReal :=
    (physicalForceWeight_continuous hd lam).measurable.real_toNNReal
  have hm : physicalReversibleMeasure ω hd lam =
      (volume : Measure (Vec d)).withDensity fun x => ((physicalForceWeight hd lam x).toNNReal : ℝ≥0∞) := by
    unfold physicalReversibleMeasure
    congr 1
    funext x
    rw [physicalReversibleDensity_of_zero_potential hd hV lam x]
    rfl
  rw [hm, integral_withDensity_eq_integral_smul hρ]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul]
  rw [Real.coe_toNNReal _ (show 0 ≤ physicalForceWeight hd lam x from (Real.exp_pos _).le)]

/-- The force weight `e^{2λ x₁}` has derivative `e^{2λ x₁} · 2λ e₁*`. -/
theorem hasFDerivAt_physicalForceWeight (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) :
    HasFDerivAt (physicalForceWeight hd lam)
      (physicalForceWeight hd lam x •
        ((2 * lam) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ)
          (firstCoordinateIndex hd))) x := by
  have h : HasFDerivAt (fun y : Vec d => 2 * lam * y (firstCoordinateIndex hd))
      ((2 * lam) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ)
        (firstCoordinateIndex hd)) x :=
    (hasFDerivAt_apply (firstCoordinateIndex hd) x).const_mul (2 * lam)
  unfold physicalForceWeight
  exact h.exp

/-- The force weight is smooth. -/
theorem contDiff_physicalForceWeight (hd : 2 ≤ d) (lam : ℝ) :
    ContDiff ℝ 1 (physicalForceWeight hd lam) := by
  unfold physicalForceWeight
  exact Real.contDiff_exp.comp (contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd)))

/-- The pointwise divergence of a column, seen from a translated environment, is the pointwise
divergence at the translation point. -/
theorem cdiv_translate (i : Fin d) (ω : FieldPair d) (x : Vec d) :
    DriftH5.cdiv i (translate x ω) = ∑ k, fderiv ℝ (fun y => ω.1 y k i) x (unitVector k) := by
  unfold DriftH5.cdiv
  refine Finset.sum_congr rfl fun k _ => ?_
  have h2 := fderiv_comp_add_left (𝕜 := ℝ) (f := fun z : Vec d => ω.1 z k i) (x := (0 : Vec d)) x
  rw [add_zero] at h2
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) h2

private theorem qd_sum_mul_unitVector (c : Fin d → ℝ) (j : Fin d) :
    ∑ k, c k * (unitVector k) j = c j := by
  simp [unitVector, Pi.single_apply]

/-- **The pointwise divergence is the weak drift of the coordinate.** For a regular pair with zero
potential, `b_i^λ(x) = ½ ∑_k ∂_k a_{ki}(x) + λ a_{1i}(x)`, with the pointwise derivative of the
Lipschitz coefficient, satisfies `½ ∫ e_i · a ∇v dm_λ = -∫ b v dm_λ` for every compactly supported
`C¹` function `v`. This is integration by parts against `g = e^{2λ x₁} v`. -/
theorem isWeakDrift_cdiv (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K) {ω : FieldPair d}
    (hω : IsRegular K ω) (hV : ∀ x, ω.2 x = 0) (lam : ℝ) (i : Fin d) :
    IsWeakDrift hd ω lam (fun y => y i)
      (fun y => velocityDrift hd lam i (DriftH5.cdiv i) (translate y ω)) := by
  intro v hv hvc
  simp only [spatialGradient_coord]
  change ∫ x, (1 / 2 : ℝ) * dot (unitVector i)
      ((ω.1 x).mulVec fun k => fderiv ℝ v x (unitVector k)) ∂physicalReversibleMeasure ω hd lam = _
  rw [integral_physicalReversibleMeasure_of_zero_potential hd hV,
    integral_physicalReversibleMeasure_of_zero_potential hd hV]
  set ρ := physicalForceWeight hd lam with hρdef
  set j0 := firstCoordinateIndex hd with hj0
  set f : Fin d → Vec d → ℝ := fun k x => ω.1 x k i with hfdef
  set g : Vec d → ℝ := fun x => ρ x * v x with hgdef
  have hρd := hasFDerivAt_physicalForceWeight hd lam
  have hvd : ∀ x, HasFDerivAt v (fderiv ℝ v x) x :=
    fun x => ((hv.differentiable one_ne_zero) x).hasFDerivAt
  have hgd : ∀ x, HasFDerivAt g (ρ x • fderiv ℝ v x +
      v x • (ρ x • ((2 * lam) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ)
        j0))) x := fun x => (hρd x).mul (hvd x)
  have hg : ContDiff ℝ 1 g := (contDiff_physicalForceWeight hd lam).mul hv
  have hgc : HasCompactSupport g := hvc.mul_left
  have hgcont : Continuous g := hg.continuous
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgc
  have hdg : ∀ x k, fderiv ℝ g x (unitVector k) =
      ρ x * fderiv ℝ v x (unitVector k) + v x * (ρ x * (2 * lam * (unitVector k) j0)) := by
    intro x k
    rw [(hgd x).fderiv]
    simp [smul_eq_mul]
  have hfc : ∀ k, Continuous (f k) := fun k =>
    (continuous_apply i).comp ((continuous_apply k).comp ω.1.continuous)
  have hdgc : ∀ k, Continuous fun x => fderiv ℝ g x (unitVector k) := fun k =>
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdgs : ∀ k, HasCompactSupport fun x => fderiv ℝ g x (unitVector k) := fun k =>
    (hgc.fderiv ℝ).comp_left (g := fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) rfl
  -- Integrability of the three kinds of terms.
  have hI1 : ∀ k, Integrable fun x => f k x * fderiv ℝ g x (unitVector k) := fun k =>
    ((hfc k).mul (hdgc k)).integrable_of_hasCompactSupport (hdgs k).mul_left
  have hI3 : Integrable fun x => f j0 x * g x :=
    ((hfc j0).mul hgcont).integrable_of_hasCompactSupport hgc.mul_left
  have hfL : ∀ k, LipschitzWith (K * d).toNNReal (f k) := fun k =>
    lipschitzWith_entry_of_isRegular hK.le hω k i
  have hI2 : ∀ k, Integrable fun x => fderiv ℝ (f k) x (unitVector k) * g x := fun k =>
    hgint.bdd_mul (measurable_fderiv_apply_const ℝ (f k) (unitVector k)).aestronglyMeasurable
      (ae_of_all _ fun x => (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hfL k)) (norm_nonneg _)))
  -- Integration by parts for each column entry.
  have hIBP : ∀ k, ∫ x, f k x * fderiv ℝ g x (unitVector k) =
      -∫ x, fderiv ℝ (f k) x (unitVector k) * g x := by
    intro k
    obtain ⟨Cg, hgL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hgc hg one_ne_zero
    have h := (hfL k).integral_lineDeriv_mul_eq (μ := volume) hgL hgc (unitVector k)
    have hl1 : ∫ x, lineDeriv ℝ (f k) x (unitVector k) * g x =
        ∫ x, fderiv ℝ (f k) x (unitVector k) * g x :=
      integral_congr_ae (((hfL k).ae_differentiableAt (μ := volume)).mono fun x hx => by
        simp only [hx.lineDeriv_eq_fderiv])
    have hl2 : ∀ x, lineDeriv ℝ g x (-unitVector k) = -fderiv ℝ g x (unitVector k) := fun x => by
      rw [(hgd x).differentiableAt.lineDeriv_eq_fderiv, map_neg]
    rw [hl1] at h
    simp only [hl2, neg_mul, integral_neg] at h
    rw [h, neg_neg]
    exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  -- The two integrands as sums over the columns.
  have hsym : ∀ x k, ω.1 x i k = f k x := fun x k =>
    congrFun (congrFun ((hω.1 x).1) k) i
  have hE1 : ∀ x, ρ x * ((1 / 2 : ℝ) * dot (unitVector i)
      ((ω.1 x).mulVec fun k => fderiv ℝ v x (unitVector k))) =
      ∑ k, (1 / 2 : ℝ) * (f k x * fderiv ℝ g x (unitVector k)) - lam * (f j0 x * g x) := by
    intro x
    have hdot : dot (unitVector i) ((ω.1 x).mulVec fun k => fderiv ℝ v x (unitVector k)) =
        ∑ k, f k x * fderiv ℝ v x (unitVector k) := by
      simp only [dot, unitVector, Pi.single_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun k _ => by rw [hsym]
    have hlam' : lam * (f j0 x * g x) = ∑ k, lam * (f k x * g x) * (unitVector k) j0 :=
      (qd_sum_mul_unitVector (fun k => lam * (f k x * g x)) j0).symm
    rw [hdot, hlam', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hdg x k]
    simp only [hgdef]
    ring
  have hE2 : ∀ x, ρ x * (velocityDrift hd lam i (DriftH5.cdiv i) (translate x ω) * v x) =
      ∑ k, (1 / 2 : ℝ) * (fderiv ℝ (f k) x (unitVector k) * g x) + lam * (f j0 x * g x) := by
    intro x
    unfold velocityDrift
    rw [cdiv_translate]
    have h0 : (translate x ω).1 0 (firstIdx hd) i = f j0 x := by
      simp only [translate_matrix, add_zero, hfdef]
      rfl
    rw [h0, ← Finset.mul_sum, ← Finset.sum_mul]
    simp only [hgdef, hfdef]
    ring
  rw [integral_congr_ae (ae_of_all _ hE1), integral_congr_ae (ae_of_all _ hE2),
    integral_sub (integrable_finset_sum _ fun k _ => (hI1 k).const_mul _) (hI3.const_mul _),
    integral_add (integrable_finset_sum _ fun k _ => (hI2 k).const_mul _) (hI3.const_mul _),
    integral_finset_sum _ fun k _ => (hI1 k).const_mul _,
    integral_finset_sum _ fun k _ => (hI2 k).const_mul _]
  simp only [integral_const_mul, hIBP, mul_neg, Finset.sum_neg_distrib]
  ring

/-! ## Measurability and boundedness of the pointwise drift -/

/-- The pointwise drift along translations, written with derivatives at the translation point. -/
theorem velocityDrift_cdiv_translate (hd : 2 ≤ d) (lam : ℝ) (i : Fin d) (ω : FieldPair d)
    (y : Vec d) :
    velocityDrift hd lam i (DriftH5.cdiv i) (translate y ω) =
      (1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun z => ω.1 z k i) y (unitVector k) +
        lam * ω.1 y (firstIdx hd) i := by
  unfold velocityDrift
  rw [cdiv_translate]
  simp only [translate_matrix, add_zero]

theorem measurable_velocityDrift_cdiv_translate (hd : 2 ≤ d) (lam : ℝ) (i : Fin d)
    (ω : FieldPair d) :
    Measurable fun y => velocityDrift hd lam i (DriftH5.cdiv i) (translate y ω) := by
  simp only [velocityDrift_cdiv_translate]
  have hentry : Continuous fun y => ω.1 y (firstIdx hd) i :=
    (continuous_apply i).comp ((continuous_apply (firstIdx hd)).comp ω.1.continuous)
  exact (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
    measurable_fderiv_apply_const ℝ _ _)).add (measurable_const.mul hentry.measurable)

theorem exists_abs_velocityDrift_cdiv_translate_le (hd : 2 ≤ d) {K : ℝ} (hK : 0 < K)
    {ω : FieldPair d} (hω : IsRegular K ω) (lam : ℝ) (i : Fin d) :
    ∃ B : ℝ, ∀ y, |velocityDrift hd lam i (DriftH5.cdiv i) (translate y ω)| ≤ B := by
  refine ⟨(1 / 2 : ℝ) * ∑ k : Fin d, ((K * d).toNNReal : ℝ) * ‖unitVector k‖ + |lam| * K,
    fun y => ?_⟩
  rw [velocityDrift_cdiv_translate]
  have hD : ∀ k, |fderiv ℝ (fun z => ω.1 z k i) y (unitVector k)| ≤
      ((K * d).toNNReal : ℝ) * ‖unitVector k‖ := fun k => by
    rw [← Real.norm_eq_abs]
    exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ (lipschitzWith_entry_of_isRegular hK.le hω k i))
      (norm_nonneg _))
  have hsum : |∑ k, fderiv ℝ (fun z => ω.1 z k i) y (unitVector k)| ≤
      ∑ k : Fin d, ((K * d).toNNReal : ℝ) * ‖unitVector k‖ :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hD k)
  calc |(1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun z => ω.1 z k i) y (unitVector k) +
        lam * ω.1 y (firstIdx hd) i|
      ≤ |(1 / 2 : ℝ) * ∑ k, fderiv ℝ (fun z => ω.1 z k i) y (unitVector k)| +
          |lam * ω.1 y (firstIdx hd) i| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ∑ k : Fin d, ((K * d).toNNReal : ℝ) * ‖unitVector k‖ + |lam| * K := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        gcongr
        exact abs_entry_le_of_isRegular hK hω y (firstIdx hd) i

/-! ## Version independence of the drift -/

/-- A measurable functional with zero annealed integral vanishes for almost every environment and
almost every path from the origin. -/
theorem ae_ae_eq_zero_of_lintegral_annealedCoordinateJoint (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω))
    {F : FieldPair d × Path d → ℝ≥0∞} (hF : Measurable F)
    (h0 : ∫⁻ z, F z ∂(annealedCoordinateJoint Q P hprob) = 0) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω), F (ω, γ) = 0 := by
  have hint : ∫⁻ z, F z ∂(annealedCoordinateJoint Q P hprob) =
      ∫⁻ ω, ∫⁻ γ, F (ω, γ) ∂originLaw P ω ∂Q := by
    unfold annealedCoordinateJoint
    exact Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral
      Q (originLaw P) hprob F hF
  have hKae := Probability.probabilityPart_ae_eq Q (originLaw P) hprob
  have hGm : Measurable fun ω => ∫⁻ γ, F (ω, γ) ∂Probability.probabilityPart (originLaw P) ω :=
    hF.lintegral_kernel_prod_right'
  have hG0 : ∫⁻ ω, ∫⁻ γ, F (ω, γ) ∂Probability.probabilityPart (originLaw P) ω ∂Q = 0 := by
    rw [lintegral_congr_ae (hKae.mono fun ω h => by rw [h]), ← hint]
    exact h0
  filter_upwards [(lintegral_eq_zero_iff hGm).mp hG0, hKae] with ω hω hK
  have h1 : ∫⁻ γ, F (ω, γ) ∂originLaw P ω = 0 := by
    rw [← hK]
    exact hω
  filter_upwards [(lintegral_eq_zero_iff (hF.comp measurable_prodMk_left)).mp h1] with γ hγ
  exact hγ

/-- **Version independence.** Two drifts that agree almost everywhere under the reduced law give
the same martingale part, for almost every environment and almost every path, because the reduced
environment seen at positive times avoids reduced-null sets. -/
theorem ae_driftMartingalePart_eq (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {b b' : FieldPair d → ℝ} (hbb : b =ᵐ[reducedReferenceLaw Q] b') (i : Fin d) {t : ℝ}
    (ht : 0 ≤ t) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(originLaw P ω),
      driftMartingalePart b i t (ω, γ) = driftMartingalePart b' i t (ω, γ) := by
  set J := annealedCoordinateJoint Q.measure P hprob
  haveI : IsProbabilityMeasure J :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw P) hprob
  set N := toMeasurable (reducedReferenceLaw Q) {w | b w ≠ b' w}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : Measure.map reduce Q.measure N = 0 := by
    change reducedReferenceLaw Q N = 0
    rw [measure_toMeasurable]
    exact ae_iff.mp hbb
  have hsub : {w | b w ≠ b' w} ⊆ N := subset_toMeasurable _ _
  set H : ℝ × (FieldPair d × Path d) → ℝ≥0∞ :=
    fun p => N.indicator 1 (reducedObservationAt p.1.toNNReal p.2) with hHdef
  have hH : Measurable H :=
    (measurable_one.indicator hNm).comp laplaceDensity_measurable_observation
  set F : FieldPair d × Path d → ℝ≥0∞ := fun z => ∫⁻ u in Set.Ioc 0 t, H (u, z) with hFdef
  have hF : Measurable F := hH.lintegral_prod_left'
  have hslice : ∀ u : ℝ, 0 < u → ∫⁻ z, H (u, z) ∂J = 0 := by
    intro u hu
    have hpre : MeasurableSet {z : FieldPair d × Path d | reducedObservationAt u.toNNReal z ∈ N} :=
      hNm.preimage (laplaceDensity_measurable_observation_fixed u.toNNReal)
    have heq : (fun z => H (u, z)) =
        {z : FieldPair d × Path d | reducedObservationAt u.toNNReal z ∈ N}.indicator 1 := by
      funext z
      show N.indicator 1 (reducedObservationAt u.toNNReal z) = _
      by_cases h : reducedObservationAt u.toNNReal z ∈ N
      · rw [Set.indicator_of_mem h,
          Set.indicator_of_mem (show z ∈ {z | reducedObservationAt u.toNNReal z ∈ N} from h)]
        rfl
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (show z ∉ {z | reducedObservationAt u.toNNReal z ∈ N} from h)]
    rw [heq, lintegral_indicator_one hpre]
    exact laplaceDensity_observed_time_null hd Q h0 h1 P hprob hGMP hNm hN0
      (Real.toNNReal_pos.mpr hu)
  have hF0 : ∫⁻ z, F z ∂J = 0 := by
    simp only [hFdef]
    rw [lintegral_lintegral_swap (f := fun (z : FieldPair d × Path d) (u : ℝ) => H (u, z))
      (ν := (volume : Measure ℝ).restrict (Set.Ioc 0 t)) ((hH.comp measurable_swap).aemeasurable)]
    rw [lintegral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ fun u hu => hslice u hu.1))]
    simp
  filter_upwards [ae_ae_eq_zero_of_lintegral_annealedCoordinateJoint Q.measure P hprob hF hF0]
    with ω hω
  filter_upwards [hω] with γ hγ
  have hzero := (lintegral_eq_zero_iff (hH.comp (measurable_id.prodMk measurable_const))).mp hγ
  have hall : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioc 0 t →
      b (reducedObservationAt u.toNNReal (ω, γ)) = b' (reducedObservationAt u.toNNReal (ω, γ)) := by
    filter_upwards [(ae_restrict_iff' measurableSet_Ioc).mp hzero] with u hu hmem
    have hval : N.indicator 1 (reducedObservationAt u.toNNReal (ω, γ)) = (0 : ℝ≥0∞) := hu hmem
    by_contra hne
    have hN : reducedObservationAt u.toNNReal (ω, γ) ∈ N := hsub hne
    rw [Set.indicator_of_mem hN] at hval
    exact one_ne_zero hval
  unfold driftMartingalePart
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hall] with u hu hmem
  rw [Set.uIoc_of_le ht] at hmem
  exact hu hmem

/-! ## The step -/

/-- **`QuenchedDriftMartingaleStep` from FOT Theorem 5.5.5.** The constant is
`C = sourceReducedBound Λ₀`, uniform in `λ`, `i`, `t` and the version of `D·(a e_i)`. -/
theorem quenchedDriftMartingaleStep_of_fukushima (hFOT : FukushimaDecompositionInput) :
    QuenchedDriftMartingaleStep := by
  intro d hd Λ₀ r₀ Q P' hP' lam hlam hlam1 hQ i divA hdiv
  refine ⟨sourceReducedBound Λ₀, fun t ht => ?_⟩
  have hK1 : 1 ≤ sourceReducedBound Λ₀ := one_le_sourceReducedBound Q.ellipticity_parameter
  have hK : 0 < sourceReducedBound Λ₀ := lt_of_lt_of_le one_pos hK1
  have hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hlam.le hlam1
      (originLaw (P' lam)) := hP' lam hlam.le hlam1
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' lam) ω) := by
    filter_upwards [hGMP] with ω hω
    obtain ⟨_, r, hr⟩ := hω
    haveI := r.pathLaw_isMarkovKernel
    rw [hr]
    infer_instance
  haveI : IsProbabilityMeasure (reducedReferenceLaw Q) := by
    unfold reducedReferenceLaw
    exact inferInstance
  have hae : divA =ᵐ[reducedReferenceLaw Q] DriftH5.cdiv i :=
    hdiv.ae_unique (DriftH5.hasWeakHorizontalDivergence_reducedColumn Q hQ i)
  have hvd : velocityDrift hd lam i divA =ᵐ[reducedReferenceLaw Q]
      velocityDrift hd lam i (DriftH5.cdiv i) :=
    hae.mono fun w hw => by unfold velocityDrift; rw [hw]
  filter_upwards [ae_driftMartingalePart_eq hd Q hlam.le hlam1 (P' lam) hprob hGMP hvd i ht,
    hGMP] with ω hpart hω
  obtain ⟨hω', r, hr⟩ := hω
  set ω₀ := zeroPotentialReducedPair ω
  have hV : ∀ x, ω₀.2 x = 0 := fun x => rfl
  set b : Vec d → ℝ := fun y => velocityDrift hd lam i (DriftH5.cdiv i) (translate y ω₀)
  obtain ⟨hmem0, hbd0, -⟩ := hFOT d hd (sourceReducedBound Λ₀) hK1 ω₀ hω' lam hlam.le hlam1 r
    (fun y => y i) 1 (contDiff_apply ℝ ℝ i)
    (fun x => by rw [spatialGradient_coord, qd_euclid_unitVector]) b
    (measurable_velocityDrift_cdiv_translate hd lam i ω₀)
    (exists_abs_velocityDrift_cdiv_translate_le hd hK hω' lam i)
    (isWeakDrift_cdiv hd hK hω' hV lam i) t ht
  -- From the origin, `γ_0 = 0` almost surely, so the two martingale parts agree.
  have hstart : (fun γ => pathMartingalePart (fun y => y i) b t γ) =ᵐ[r.pathLaw 0]
      fun γ => spatialMartingalePart b i t γ := by
    filter_upwards [r.pathLaw_starts_at 0] with γ hγ
    have h0 : γ 0 i = 0 := by
      have := congrFun hγ i
      simpa [pathPosition] using this
    simp only [pathMartingalePart, spatialMartingalePart, h0, sub_zero]
  have hmem : MemLp (spatialMartingalePart b i t) 2 (r.pathLaw 0) := hmem0.ae_eq hstart
  have hbd : ∫ γ, spatialMartingalePart b i t γ ^ 2 ∂r.pathLaw 0 ≤ sourceReducedBound Λ₀ * t := by
    have hsq : (fun γ => pathMartingalePart (fun y => y i) b t γ ^ 2) =ᵐ[r.pathLaw 0]
        fun γ => spatialMartingalePart b i t γ ^ 2 :=
      hstart.mono fun γ hγ => by
        simp only at hγ ⊢
        rw [hγ]
    rw [← integral_congr_ae hsq]
    simpa using hbd0
  have hspatial : ∀ γ : Path d, driftMartingalePart (velocityDrift hd lam i (DriftH5.cdiv i)) i t
      (ω, γ) = spatialMartingalePart b i t γ := fun γ => rfl
  have hlaw : P' lam (0, ω) = r.pathLaw 0 := hr
  have hpart' : (fun γ => spatialMartingalePart b i t γ) =ᵐ[r.pathLaw 0]
      fun γ => driftMartingalePart (velocityDrift hd lam i divA) i t (ω, γ) := by
    rw [← hlaw]
    filter_upwards [hpart] with γ hγ
    rw [← hspatial, hγ]
  rw [hlaw]
  refine ⟨hmem.ae_eq hpart', ?_⟩
  have hsq : (fun γ => spatialMartingalePart b i t γ ^ 2) =ᵐ[r.pathLaw 0]
      fun γ => driftMartingalePart (velocityDrift hd lam i divA) i t (ω, γ) ^ 2 :=
    hpart'.mono fun γ hγ => by
      simp only at hγ ⊢
      rw [hγ]
  rw [← integral_congr_ae hsq]
  exact hbd

end EinsteinRelation
