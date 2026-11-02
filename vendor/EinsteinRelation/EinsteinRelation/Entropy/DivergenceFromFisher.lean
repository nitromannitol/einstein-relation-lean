import EinsteinRelation.Entropy.FisherCauchySchwarz
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Calculus.EnvironmentWeakCalculusUniqueness
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality

/-!
# Lemma 4.2, first assertion, from Lemma 4.1 and Proposition 3.2

Source: `paper/main.tex` lines 619–633 (`entropy.divergence`, first assertion). The statement is
the production twin of the first assertion of `EinsteinRelation.Frozen.entropyDivergenceV2`.
Its two paper inputs enter as explicit premises:

* `hFisher` is the Fisher bound of Lemma 4.1 (`entropy.fisher`, `paper/main.tex:512–518`);
* `hOcc` is the occupation bound of Proposition 3.2 (`regen.occupation`, `paper/main.tex:439–447`).

The weak gradient is assumed to vanish on `{ρ = 0}` through the premise `hzero`.

The argument applies the Fisher–Cauchy–Schwarz bound
`EinsteinRelation.fisher_cauchy_schwarz_lintegral` to the reduced coefficient `(reduce ω).1 0`,
which is elliptic with constant `sourceReducedBound Λ₀`. The moment `∫ ρ |F|²` is controlled by
the occupation bound applied to `G = |F|²`, and `‖|F|²‖_p = ‖F‖_{2p}²`.
-/

open MeasureTheory
open EinsteinRelation.Carriers

namespace EinsteinRelation.Entropy

/-! ### Measurability of the Euclidean pairing -/

theorem continuous_euclideanSq_vec {d : ℕ} :
    Continuous (fun x : Vec d => euclideanSq x) := by
  unfold euclideanSq dot
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

theorem measurable_euclideanSq_vec {d : ℕ} :
    Measurable (fun x : Vec d => euclideanSq x) :=
  continuous_euclideanSq_vec.measurable

theorem measurable_dot_pair {d : ℕ} :
    Measurable (fun p : Vec d × Vec d => dot p.1 p.2) := by
  unfold dot
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp measurable_fst).mul ((measurable_pi_apply i).comp measurable_snd)

theorem euclideanNorm_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

/-- A field measurable for the σ-algebra of a bounded window is measurable for the ambient
Borel σ-algebra of the field pair. -/
theorem measurable_of_localSigma_vec {d : ℕ} {β : Type*} [MeasurableSpace β] {U : Set (Vec d)}
    {F : FieldPair d → β} (hF : Measurable[localSigma U] F) : Measurable F :=
  hF.mono (Probability.localSigma_le_borel U) le_rfl

/-! ### The reduced coefficient at the origin -/

theorem continuous_coeff_zero {d : ℕ} : Continuous (fun w : FieldPair d => w.1 0) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

theorem measurable_coeff_zero {d : ℕ} : Measurable (fun w : FieldPair d => w.1 0) :=
  continuous_coeff_zero.measurable

theorem continuous_dot_coeff_zero {d : ℕ} (ξ : Vec d) :
    Continuous (fun w : FieldPair d => dot ξ ((w.1 0).mulVec ξ)) := by
  have hmv : Continuous (fun w : FieldPair d => (w.1 0).mulVec ξ) :=
    continuous_coeff_zero.matrix_mulVec continuous_const
  unfold dot
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp hmv)

/-- The two-sided Euclidean ellipticity bounds at the origin form a closed set. -/
theorem isClosed_elliptic_coeff_zero {d : ℕ} (Λ : ℝ) :
    IsClosed {w : FieldPair d | (w.1 0).transpose = w.1 0 ∧
      ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ) ∧
        dot ξ ((w.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ} := by
  have hset : {w : FieldPair d | (w.1 0).transpose = w.1 0 ∧
      ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ) ∧
        dot ξ ((w.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ} =
      {w : FieldPair d | (w.1 0).transpose = w.1 0} ∩
        ⋂ ξ : Vec d, ({w : FieldPair d | Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ)} ∩
          {w : FieldPair d | dot ξ ((w.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ}) := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine IsClosed.inter (isClosed_eq continuous_coeff_zero.matrix_transpose continuous_coeff_zero)
    (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
  · exact isClosed_le continuous_const (continuous_dot_coeff_zero ξ)
  · exact isClosed_le (continuous_dot_coeff_zero ξ) continuous_const

theorem measurableSet_elliptic_coeff_zero {d : ℕ} (Λ : ℝ) :
    MeasurableSet {w : FieldPair d | (w.1 0).transpose = w.1 0 ∧
      ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ) ∧
        dot ξ ((w.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ} :=
  (isClosed_elliptic_coeff_zero Λ).measurableSet

/-- The reduced coefficient at the origin is elliptic with constant `sourceReducedBound Λ₀`
almost surely under the reduced reference law. The bound is transported from the physical
regularity of the environment through `reduce`. -/
theorem ae_reduced_elliptic_zero {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(reducedReferenceLaw Q), (w.1 0).transpose = w.1 0 ∧
      ∀ ξ : Vec d, (sourceReducedBound Λ₀)⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ) ∧
        dot ξ ((w.1 0).mulVec ξ) ≤ sourceReducedBound Λ₀ * euclideanSq ξ := by
  unfold reducedReferenceLaw
  rw [ae_map_iff Probability.measurable_reduce.aemeasurable
    (measurableSet_elliptic_coeff_zero (sourceReducedBound Λ₀))]
  filter_upwards [Q.regular] with ω hω
  exact (sourceReducedBound_support Q.ellipticity_parameter hω).2.1 0

/-- The reduced reference law is a probability measure. -/
instance reducedReferenceLaw_isProbabilityMeasure {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedReferenceLaw Q) :=
  by unfold reducedReferenceLaw; exact inferInstance

theorem sourceReducedBound_pos_of_one_le {L : ℝ} (hL : 1 ≤ L) :
    0 < sourceReducedBound L := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith)

/-! ### Coordinate and zero-set bookkeeping -/

/-- A vector field with integrable coordinates agrees almost everywhere with a measurable one. -/
theorem exists_measurable_ae_vec {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (D : Ω → Vec d) (hD : ∀ i : Fin d, Integrable (fun ω => D ω i) μ) :
    ∃ D' : Ω → Vec d, Measurable D' ∧ D =ᵐ[μ] D' := by
  have hcoord : ∀ i : Fin d, AEStronglyMeasurable (fun ω => D ω i) μ := fun i =>
    (hD i).aestronglyMeasurable
  refine ⟨fun ω i => (hcoord i).mk (fun ω => D ω i) ω, ?_, ?_⟩
  · exact Measurable.of_eval fun i => (hcoord i).stronglyMeasurable_mk.measurable
  · have hall : ∀ᵐ ω ∂μ, ∀ i : Fin d, D ω i = (hcoord i).mk (fun ω => D ω i) ω :=
      ae_all_iff.2 fun i => (hcoord i).ae_eq_mk
    filter_upwards [hall] with ω hω
    funext i
    exact hω i

/-- Coordinatewise almost-everywhere equality gives equality of the vector fields. -/
theorem ae_vec_eq_of_coord {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D D' : Ω → Vec d} (h : ∀ i : Fin d, (fun ω => D ω i) =ᵐ[μ] (fun ω => D' ω i)) :
    D =ᵐ[μ] D' := by
  have hall : ∀ᵐ ω ∂μ, ∀ i : Fin d, D ω i = D' ω i := ae_all_iff.2 h
  filter_upwards [hall] with ω hω
  funext i
  exact hω i

/-- The Fisher integrand only depends on the gradient almost everywhere. -/
theorem lintegral_fisher_congr {d : ℕ} {μ : Measure (FieldPair d)} (rho : FieldPair d → ℝ)
    {D D₀ : FieldPair d → Vec d} (h : D =ᵐ[μ] D₀) :
    (∫⁻ w, ENNReal.ofReal
        (if rho w = 0 then 0 else dot (D w) ((w.1 0).mulVec (D w)) / rho w) ∂μ) =
      ∫⁻ w, ENNReal.ofReal
        (if rho w = 0 then 0 else dot (D₀ w) ((w.1 0).mulVec (D₀ w)) / rho w) ∂μ := by
  apply lintegral_congr_ae
  filter_upwards [h] with w hw
  simp only [hw]

/-- Fisher–Cauchy–Schwarz for the reduced coefficient at the origin. The zero set of `rho` is
handled by the premise `hzero`. -/
theorem cs_dot_bound_reduced {d : ℕ} (μ : Measure (FieldPair d)) {Λ : ℝ} (hΛ : 0 < Λ)
    (hell : ∀ᵐ w ∂μ, (w.1 0).transpose = w.1 0 ∧
      ∀ ξ : Vec d, Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((w.1 0).mulVec ξ) ∧
        dot ξ ((w.1 0).mulVec ξ) ≤ Λ * euclideanSq ξ)
    (rho : FieldPair d → ℝ) (hrho : Measurable rho) (hrho0 : ∀ w, 0 ≤ rho w)
    (D F : FieldPair d → Vec d) (hD : Measurable D) (hF : Measurable F)
    (hzero : ∀ᵐ w ∂μ, rho w = 0 → D w = 0) (K M : ℝ)
    (hK : ∫⁻ w, ENNReal.ofReal
        (if rho w = 0 then 0 else dot (D w) ((w.1 0).mulVec (D w)) / rho w) ∂μ ≤
      ENNReal.ofReal K)
    (hM : ∫⁻ w, ENNReal.ofReal (rho w * euclideanSq (F w)) ∂μ ≤ ENNReal.ofReal M) :
    ∫⁻ w, ENNReal.ofReal |dot (D w) (F w)| ∂μ ≤
      ENNReal.ofReal (Real.sqrt K * Real.sqrt (Λ * M)) :=
  fisher_cauchy_schwarz_lintegral μ Λ hΛ (fun w : FieldPair d => w.1 0) measurable_coeff_zero hell
    rho hrho (Filter.Eventually.of_forall hrho0) D F hD hF hzero K M hK hM

/-! ### Real and extended-real algebra -/

/-- The square-root chain of the Cauchy–Schwarz bound, with the constant `4 B λ²` of Lemma 4.1
and the moment `2 C N²`. -/
theorem sqrt_chain_eq (B C N lam : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hN : 0 ≤ N) (hl : 0 ≤ lam) :
    Real.sqrt (4 * B * lam ^ 2) * Real.sqrt (B * (2 * C * N ^ 2)) =
      2 * B * Real.sqrt (2 * C) * lam * N := by
  have h1 : Real.sqrt (4 * B * lam ^ 2) = 2 * lam * Real.sqrt B := by
    rw [show 4 * B * lam ^ 2 = (2 * lam) ^ 2 * B by ring, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (by linarith : (0 : ℝ) ≤ 2 * lam)]
  have h2 : Real.sqrt (B * (2 * C * N ^ 2)) = Real.sqrt B * (Real.sqrt (2 * C) * N) := by
    rw [Real.sqrt_mul hB, Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 2 * C), Real.sqrt_sq hN]
  rw [h1, h2]
  have hBB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB
  calc 2 * lam * Real.sqrt B * (Real.sqrt B * (Real.sqrt (2 * C) * N))
      = (Real.sqrt B * Real.sqrt B) * (2 * Real.sqrt (2 * C) * lam * N) := by ring
    _ = 2 * B * Real.sqrt (2 * C) * lam * N := by rw [hBB]; ring

/-- The occupation constant `C (1 + s λ⁻²)` is at most `2C` when `s ≤ λ²`. -/
theorem occupation_factor_le {C lam s : ℝ} (hC : 0 ≤ C) (hl : 0 < lam) (hs : s ≤ lam ^ 2) :
    C * (1 + s * (lam ^ 2)⁻¹) ≤ 2 * C := by
  have hpos : 0 < lam ^ 2 := pow_pos hl 2
  have h1 : s * (lam ^ 2)⁻¹ ≤ 1 :=
    calc s * (lam ^ 2)⁻¹ ≤ lam ^ 2 * (lam ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hs (inv_nonneg.mpr hpos.le)
      _ = 1 := mul_inv_cancel₀ hpos.ne'
  have h2 : 1 + s * (lam ^ 2)⁻¹ ≤ 2 := by linarith
  calc C * (1 + s * (lam ^ 2)⁻¹) ≤ C * 2 := mul_le_mul_of_nonneg_left h2 hC
    _ = 2 * C := by ring

/-- The `L²` norm of the squared Euclidean norm: `‖|F|²‖_p = ‖|F|‖_{2p}²`. -/
theorem eLpNorm_euclideanSq_eq {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (F : Ω → Vec d) {p : ℝ} (hp : 0 ≤ p) :
    eLpNorm (fun w => euclideanSq (F w)) (ENNReal.ofReal p) μ =
      eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) μ ^ (2 : ℝ) := by
  have hfun : (fun w => euclideanSq (F w)) = fun w => ‖euclideanNorm (F w)‖ ^ (2 : ℝ) := by
    funext w
    rw [Real.norm_of_nonneg (euclideanNorm_nonneg' (F w)), Real.rpow_two]
    unfold euclideanNorm
    exact (Real.sq_sqrt (euclideanSq_nonneg_fisher _)).symm
  have hexp : ENNReal.ofReal p * ENNReal.ofReal 2 = ENNReal.ofReal (2 * p) := by
    rw [← ENNReal.ofReal_mul hp, mul_comm]
  by_cases hm : AEStronglyMeasurable (fun w => euclideanNorm (F w)) μ
  · rw [hfun, ← hexp]
    exact eLpNorm_norm_rpow (fun w => euclideanNorm (F w)) hm (by norm_num : (0 : ℝ) < 2)
  have hsq : ¬ AEStronglyMeasurable (fun w => euclideanSq (F w)) μ := by
    intro h
    exact hm (Real.continuous_sqrt.comp_aestronglyMeasurable h)
  rw [eLpNorm_of_not_aestronglyMeasurable hsq,
    eLpNorm_of_not_aestronglyMeasurable hm]
  simp

/-- If `|F|` is in `L^{2p}`, then `|F|²` is in `L^p`. -/
theorem memLp_euclideanSq_of {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F : Ω → Vec d} (hFm : Measurable F) {p : ℝ} (hp : 0 ≤ p)
    (hF : MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) μ) :
    MemLp (fun w => euclideanSq (F w)) (ENNReal.ofReal p) μ := by
  rw [memLp_iff, eLpNorm_euclideanSq_eq μ F hp]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hF.eLpNorm_ne_top

/-- The moment bound `∫ ρ |F|² ≤ 2 C N²`, where `N = ‖|F|‖_{2p}`, from the occupation bound. -/
theorem lintegral_rho_sq_le {d : ℕ} {μ : Measure (FieldPair d)} (rho : FieldPair d → ℝ)
    {F : FieldPair d → Vec d} {p C N : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hrho0 : ∀ w, 0 ≤ rho w)
    (hNE : eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) μ =
      ENNReal.ofReal N)
    (hO : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |euclideanSq (F w)| ∂μ ≤
      ENNReal.ofReal (2 * C) * eLpNorm (fun w => euclideanSq (F w)) (ENNReal.ofReal p) μ) :
    ∫⁻ w, ENNReal.ofReal (rho w * euclideanSq (F w)) ∂μ ≤
      ENNReal.ofReal (2 * C * N ^ 2) := by
  have hpt : ∀ w, ENNReal.ofReal (rho w * euclideanSq (F w)) =
      ENNReal.ofReal (rho w) * ENNReal.ofReal |euclideanSq (F w)| := fun w => by
    rw [ENNReal.ofReal_mul (hrho0 w), abs_of_nonneg (euclideanSq_nonneg_fisher _)]
  rw [lintegral_congr hpt]
  refine hO.trans (le_of_eq ?_)
  rw [eLpNorm_euclideanSq_eq μ F hp, hNE, ENNReal.rpow_two, ← ENNReal.ofReal_pow hN,
    ← ENNReal.ofReal_mul (by linarith : (0 : ℝ) ≤ 2 * C)]

/-- Integrated absolute value: `ofReal |∫ f| ≤ ∫⁻ ofReal |f|`. -/
theorem ofReal_abs_integral_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {K : ℝ} (h : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ ≤ ENNReal.ofReal K) :
    ENNReal.ofReal |∫ ω, f ω ∂μ| ≤ ENNReal.ofReal K := by
  calc ENNReal.ofReal |∫ ω, f ω ∂μ| = ‖∫ ω, f ω ∂μ‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
    _ = ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ := lintegral_congr fun ω => Real.enorm_eq_ofReal_abs _
    _ ≤ ENNReal.ofReal K := h

/-! ### The first assertion for fixed data -/

/-- The first assertion of Lemma 4.2 for one environment, one force, one density and one
weak gradient. The constant is `2 B √(2C)` with `B = sourceReducedBound Λ₀`. -/
theorem divergence_fixed_bound {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {hQ : IsStationary (reducedReferenceLaw Q)} {lam s : ℝ} (hl : 0 < lam) (hs : s ≤ lam ^ 2)
    {rho : FieldPair d → ℝ} (hrho : Measurable rho) (hrho0 : ∀ w, 0 ≤ rho w)
    {Drho Drho₀ : FieldPair d → Vec d}
    (hW : HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho)
    (hW₀ : HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho₀)
    (hzero : ∀ᵐ w ∂(reducedReferenceLaw Q), rho w = 0 → Drho w = 0)
    (hK₀ : ∫⁻ w, ENNReal.ofReal
        (if rho w = 0 then 0 else dot (Drho₀ w) ((w.1 0).mulVec (Drho₀ w)) / rho w)
          ∂(reducedReferenceLaw Q) ≤ ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    {F : FieldPair d → Vec d} (hFm : Measurable F) {p C : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hFmem : MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
      (reducedReferenceLaw Q))
    (hOcc : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |euclideanSq (F w)|
        ∂(reducedReferenceLaw Q) ≤
      ENNReal.ofReal (C * (1 + s * (lam ^ 2)⁻¹)) *
        eLpNorm (fun w => euclideanSq (F w)) (ENNReal.ofReal p) (reducedReferenceLaw Q)) :
    Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) ∧
      ENNReal.ofReal |∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q)| ≤
        ENNReal.ofReal (2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C) * lam) *
          eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
            (reducedReferenceLaw Q) := by
  have hΛ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hB : 0 < sourceReducedBound Λ₀ := sourceReducedBound_pos_of_one_le hΛ
  have hB0 : 0 ≤ sourceReducedBound Λ₀ := hB.le
  -- Measurable representative of the gradient, identified with `Drho₀` almost everywhere.
  obtain ⟨Drho', hDm, hDae⟩ := exists_measurable_ae_vec (reducedReferenceLaw Q) Drho
    (fun i => hW.2.1 i)
  have hD₀ : Drho' =ᵐ[reducedReferenceLaw Q] Drho₀ :=
    hDae.symm.trans (ae_vec_eq_of_coord fun i => HasWeakHorizontalGradient.ae_unique hW hW₀ i)
  have hzero' : ∀ᵐ w ∂(reducedReferenceLaw Q), rho w = 0 → Drho' w = 0 := by
    filter_upwards [hzero, hDae] with w h1 h2 h3
    rw [← h2]
    exact h1 h3
  have hK' : ∫⁻ w, ENNReal.ofReal
      (if rho w = 0 then 0 else dot (Drho' w) ((w.1 0).mulVec (Drho' w)) / rho w)
        ∂(reducedReferenceLaw Q) ≤ ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2) :=
    (le_of_eq (lintegral_fisher_congr rho hD₀)).trans hK₀
  -- Occupation bound with the constant `2C`.
  have hOcc' : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |euclideanSq (F w)|
        ∂(reducedReferenceLaw Q) ≤
      ENNReal.ofReal (2 * C) *
        eLpNorm (fun w => euclideanSq (F w)) (ENNReal.ofReal p) (reducedReferenceLaw Q) :=
    hOcc.trans (mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (occupation_factor_le hC hl hs)) (zero_le))
  obtain ⟨N, hN0, hNE⟩ : ∃ N : ℝ, 0 ≤ N ∧
      eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
        (reducedReferenceLaw Q) = ENNReal.ofReal N :=
    ⟨(eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
        (reducedReferenceLaw Q)).toReal, ENNReal.toReal_nonneg,
      (ENNReal.ofReal_toReal hFmem.eLpNorm_ne_top).symm⟩
  have hM := lintegral_rho_sq_le rho hp hC hN0 hrho0 hNE hOcc'
  -- Fisher–Cauchy–Schwarz with the reduced coefficient.
  have hCS := cs_dot_bound_reduced (reducedReferenceLaw Q) hB (ae_reduced_elliptic_zero Q) rho
    hrho hrho0 Drho' F hDm hFm hzero' (4 * sourceReducedBound Λ₀ * lam ^ 2) (2 * C * N ^ 2) hK' hM
  rw [sqrt_chain_eq (sourceReducedBound Λ₀) C N lam hB0 hC hN0 hl.le] at hCS
  have hmeas : Measurable (fun w => dot (Drho' w) (F w)) :=
    measurable_dot_pair.comp (hDm.prodMk hFm)
  have hint' : Integrable (fun w => dot (Drho' w) (F w)) (reducedReferenceLaw Q) := by
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact lt_of_le_of_lt hCS ENNReal.ofReal_lt_top
  have hae : (fun w => dot (Drho' w) (F w)) =ᵐ[reducedReferenceLaw Q]
      (fun w => dot (Drho w) (F w)) :=
    hDae.mono fun w hw => by simp only [hw]
  have hint : Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) :=
    hint'.congr hae
  have hIeq : ∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q) =
      ∫ w, dot (Drho' w) (F w) ∂(reducedReferenceLaw Q) :=
    integral_congr_ae hae.symm
  refine ⟨hint, ?_⟩
  calc ENNReal.ofReal |∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q)|
      = ENNReal.ofReal |∫ w, dot (Drho' w) (F w) ∂(reducedReferenceLaw Q)| := by rw [hIeq]
    _ ≤ ENNReal.ofReal (2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C) * lam * N) :=
        ofReal_abs_integral_le_of_lintegral _ _ hCS
    _ = ENNReal.ofReal (2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C) * lam) *
          ENNReal.ofReal N :=
        ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0)
          (Real.sqrt_nonneg _)) hl.le)
    _ = ENNReal.ofReal (2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C) * lam) *
          eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
            (reducedReferenceLaw Q) := by
        rw [hNE]

/-! ### The divergence bound -/

/-- Lemma 4.2, first assertion (`paper/main.tex:619–633`), conditional on the Fisher bound of
Lemma 4.1 (`hFisher`), the occupation bound of Proposition 3.2 (`hOcc`), and the vanishing of the
weak gradient on `{ρ = 0}` (`hzero`). The conclusion has the quantifier structure of the frozen
`EinsteinRelation.Frozen.entropyDivergenceV2`, restricted to its first assertion; the coordinate
path law input is replaced by its fields `Q.measure`, `P` and `origin_probability`. -/
theorem divergence_bound_of_fisher_occupation (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hFisher : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
        IsReducedLaplaceDensity Q.measure P origin_probability s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho ∧
          Integrable (fun w => euclideanNorm (Drho w)) (reducedReferenceLaw Q) ∧
          (∫⁻ w, ENNReal.ofReal
              (if rho w = 0 then 0 else dot (Drho w) ((w.1 0).mulVec (Drho w)) / rho w)
              ∂(reducedReferenceLaw Q)) ≤
            ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    (hOcc : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d)
          (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
        ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
          (∫⁻ z : FieldPair d × Path d,
              (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
            ∂(annealedCoordinateJoint Q.measure P origin_probability)) ≤
              ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
          ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
            (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
              ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q))
    (hzero : ∀ (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (reducedReferenceLaw Q))
      (rho : FieldPair d → ℝ) (Drho : FieldPair d → Vec d),
      HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
        ∀ᵐ w ∂(reducedReferenceLaw Q), rho w = 0 → Drho w = 0) :
    ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
    ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
      ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
      ∀ Drho : FieldPair d → Vec d,
        HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho →
      ∀ F : FieldPair d → Vec d,
        Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
        MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
          (reducedReferenceLaw Q) →
        Integrable (fun w => dot (Drho w) (F w)) (reducedReferenceLaw Q) ∧
          (ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂(reducedReferenceLaw Q))) ≤
            ENNReal.ofReal (C * lam) *
              eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
                (reducedReferenceLaw Q)) := by
  by_cases h : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  · obtain ⟨hΛ, hr⟩ := h
    obtain ⟨l₀, hl₀, hl⟩ := hOcc d hd Λ₀ r₀ hΛ hr
    refine ⟨l₀, hl₀, fun l hle => ?_⟩
    obtain ⟨p₀, hp₀, hp⟩ := hl l hle
    refine ⟨p₀, hp₀, fun p hpp => ?_⟩
    obtain ⟨C, hC0, hC⟩ := hp p hpp
    refine ⟨2 * sourceReducedBound Λ₀ * Real.sqrt (2 * C),
      mul_nonneg (mul_nonneg (by norm_num) (sourceReducedBound_pos_of_one_le hΛ).le)
        (Real.sqrt_nonneg _), ?_⟩
    intro Q hQ lam hl0 hl1 P origin_probability hGIP s hs rho hrho Drho hW F hFmeas hFmem
    have hlpos : 0 < l := by linarith
    have hsub : {y : Vec d | euclideanNorm y < l / (2 * lam)} ⊆
        {x : Vec d | euclideanNorm x < l / lam} := by
      intro y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      exact lt_of_lt_of_le hy (div_le_div_of_nonneg_left hlpos.le hl0 (by linarith))
    have hFbig : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F :=
      hFmeas.mono (Probability.localSigma_mono hsub) le_rfl
    have hFm : Measurable F := measurable_of_localSigma_vec hFmeas
    obtain ⟨Drho₀, hW₀, -, hK₀⟩ :=
      hFisher d hd Λ₀ r₀ Q hQ lam hl0 hl1 P origin_probability hGIP s rho hrho
    have hGmeas : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}]
        (fun w => euclideanSq (F w)) := measurable_euclideanSq_vec.comp hFbig
    have hp0 : 0 ≤ p := by linarith
    have hGmem : MemLp (fun w => euclideanSq (F w)) (ENNReal.ofReal p)
        (reducedReferenceLaw Q) :=
      memLp_euclideanSq_of _ hFm hp0 hFmem
    have hOccRaw := (hC Q lam hl0 hl1 P origin_probability hGIP _ hGmeas hGmem 1 one_pos s).2
      rho hrho
    exact divergence_fixed_bound Q hl0 hs hrho.1 hrho.2.1 hW hW₀ (hzero Q hQ rho Drho hW) hK₀
      hFm hp0 hC0 hFmem hOccRaw
  · exact ⟨|r₀| + 1, by linarith [le_abs_self r₀, abs_nonneg r₀], fun l _ =>
      ⟨2, by norm_num, fun p _ =>
        ⟨0, le_rfl, fun Q => (h ⟨Q.ellipticity_parameter, Q.range_parameter⟩).elim⟩⟩⟩

end EinsteinRelation.Entropy
