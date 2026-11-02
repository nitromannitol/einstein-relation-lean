import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Correctors.CoefficientLawEllipticity
import EinsteinRelation.Correctors.EllipticOperatorBound
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Entropy.ResolventAssembly
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.TimeChange.Pairing
import Mathlib.MeasureTheory.Function.L2Space

/-! # Lemma 4.3 (`entropy.resolvent`) from the weak resolvent identity

Source: `paper/main.tex:643-675`. The resolvent identity and bound of Lemma 4.3 are derived from
three inputs, each stated as a `Prop` premise with the quantifier prefix of its frozen source:

* `WeakResolventStep`: the weak resolvent identity `s E[ρ_s f] - s E[f] = -½ E[Dρ_s · a Df]
  + λ E[ρ_s a e₁ · Df]` (`entropy.weak.resolvent`, `paper/main.tex:662-666`);
* `DivergenceStatement`: Lemma 4.2 (`entropy.divergence`, `paper/main.tex:619-626`), both
  assertions;
* `OccupationStatement`: Proposition 3.2 (`regen.occupation`, `paper/main.tex:439-447`).

The premises are the production twins of the frozen statements under `EinsteinRelation/Frozen/`
(`EntropyResolventV2`, `EntropyDivergenceV2`, `OccupationV2`). The coordinate-path input is
replaced by its fields `IQ`, `P`, `origin_probability`, as in `EinsteinRelation/Carriers/`. The
frozen field `Q_probability` is omitted: the premise forces `IQ = Q.measure`, which is a
probability measure, so the omitted field carries no information.

`resolvent_of_weak_divergence_occupation` proves `ResolventStatement`, the twin of Lemma 4.3,
from the three premises. The coefficient `a = ω.1 0` is bounded almost everywhere on the reduced
law by the physical ellipticity bound, which gives the integrability used in the algebra.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Entropy

/-- The weak resolvent identity of Lemma 4.3 (`entropy.weak.resolvent`, `paper/main.tex:662-666`),
with the quantifier prefix of the frozen Lemma 4.3. For every `f` with `f`, `Df` in `L^{2p}` that
depend only on the environment in `B_{l/(2λ)}`, and `Df` the weak horizontal gradient of `f`,
`s E[ρ_s f] - s E[f] = -½ E[Dρ_s · a Df] + λ E[ρ_s a e₁ · Df]`. Here `a = ω.1 0` is the reduced
coefficient at the origin, `e₁ = unitVector ⟨0, _⟩`, and `(a e₁) · Df = ∑ⱼ a_{j,0} Df_j` is written
in coordinates, as in `SatisfiesReducedGeneratorEquation`. -/
def WeakResolventStep (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) : Prop :=
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧
  ∀ p : ℝ, p₀ ≤ p → ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (Carriers.reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ (IQ : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂IQ, IsProbabilityMeasure (originLaw P ω)),
    (IQ = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw P)) →
  ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
  ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity IQ P origin_probability s rho →
  ∀ Drho : FieldPair d → Vec d,
    HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho →
  ∀ f : FieldPair d → ℝ, ∀ Df : FieldPair d → Vec d,
    HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ f Df →
    MemLp f (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) →
    MemLp (fun w => euclideanNorm (Df w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] f →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] Df →
    s.1 * (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) -
        s.1 * (∫ w, f w ∂(Carriers.reducedReferenceLaw Q)) =
      -(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j)
          ∂(Carriers.reducedReferenceLaw Q)) +
        lam * (∫ w, rho w * (∑ j : Fin d, (w.1 0) j (⟨0, by omega⟩ : Fin d) * Df w j)
          ∂(Carriers.reducedReferenceLaw Q))

/-- Lemma 4.2 (`entropy.divergence`, `paper/main.tex:619-626`), both assertions, with the
quantifier prefix of the frozen statement `entropyDivergenceV2`. -/
def DivergenceStatement (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) : Prop :=
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧
  ∀ p : ℝ, p₀ ≤ p → ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (Carriers.reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ (IQ : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂IQ, IsProbabilityMeasure (originLaw P ω)),
    (IQ = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw P)) →
  ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
  ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity IQ P origin_probability s rho →
  ∀ Drho : FieldPair d → Vec d,
    HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho →
  ∀ F : FieldPair d → Vec d,
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
    MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) →
    (Integrable (fun w => dot (Drho w) (F w)) (Carriers.reducedReferenceLaw Q) ∧
      ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂(Carriers.reducedReferenceLaw Q))) ≤
        ENNReal.ofReal (C * lam) *
          eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q)) ∧
    ∀ h : FieldPair d → ℝ, MemLp h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) →
      HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ F h →
      Integrable (fun w => rho w * h w) (Carriers.reducedReferenceLaw Q) ∧
        (∫ w, rho w * h w ∂(Carriers.reducedReferenceLaw Q)) =
          -(∫ w, dot (Drho w) (F w) ∂(Carriers.reducedReferenceLaw Q))

/-- Proposition 3.2 (`regen.occupation`, `paper/main.tex:439-447`), with the quantifier prefix of
the frozen statement `occupationV2`. -/
def OccupationStatement (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) : Prop :=
  1 ≤ Λ₀ → 1 ≤ r₀ →
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
  ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
    ∀ (IQ : Measure (FieldPair d)) (P : QuenchedPathLaws d)
      (origin_probability : ∀ᵐ ω ∂IQ, IsProbabilityMeasure (originLaw P ω)),
      (IQ = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
        (originLaw P)) →
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
      MemLp G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) →
    ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
      (∫⁻ z : FieldPair d × Path d,
          (∫⁻ t in Set.Icc (0 : ℝ) T,
            ENNReal.ofReal |G (Carriers.reducedObservationAt t.toNNReal z)|)
        ∂(Carriers.annealedCoordinateJoint IQ P origin_probability)) ≤
        ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) ∧
      ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity IQ P origin_probability s rho →
        (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w|
            ∂(Carriers.reducedReferenceLaw Q)) ≤
          ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
            eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)

/-- The conclusion of Lemma 4.3 (`entropy.resolvent`, `paper/main.tex:643-658`), with the frozen
quantifier prefix of `entropyResolventV2`: the resolvent identity and the bound on `E[ρ_s h]`. -/
def ResolventStatement (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) : Prop :=
  ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧
  ∀ l : ℝ, l₀ ≤ l → ∃ p₀ : ℝ, 1 < p₀ ∧
  ∀ p : ℝ, p₀ ≤ p → ∃ C : ℝ, 0 ≤ C ∧
  ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (Carriers.reducedReferenceLaw Q)),
  ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
  ∀ (IQ : Measure (FieldPair d)) (P : QuenchedPathLaws d)
    (origin_probability : ∀ᵐ ω ∂IQ, IsProbabilityMeasure (originLaw P ω)),
    (IQ = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
      (originLaw P)) →
  ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
  ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity IQ P origin_probability s rho →
  ∀ Drho : FieldPair d → Vec d,
    HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho →
  ∀ f : FieldPair d → ℝ, ∀ Df : FieldPair d → Vec d,
  ∀ h : FieldPair d → ℝ, ∀ G : FieldPair d → Vec d,
    MemLp f (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) →
    MemLp (fun w => euclideanNorm (Df w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) →
    MemLp h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) →
    MemLp (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] f →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] Df →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] h →
    Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] G →
    SatisfiesReducedGeneratorEquation (Carriers.reducedReferenceLaw Q) hQ lam f Df h G
        (⟨0, by omega⟩ : Fin d) →
    (Integrable (fun w => rho w * f w) (Carriers.reducedReferenceLaw Q) ∧
      Integrable (fun w => rho w * h w) (Carriers.reducedReferenceLaw Q) ∧
      Integrable (fun w => dot (Drho w) (G w)) (Carriers.reducedReferenceLaw Q) ∧
      s.1 * (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) -
          s.1 * (∫ w, f w ∂(Carriers.reducedReferenceLaw Q)) =
        (∫ w, rho w * h w ∂(Carriers.reducedReferenceLaw Q)) -
          (∫ w, dot (Drho w) (G w) ∂(Carriers.reducedReferenceLaw Q))) ∧
    ENNReal.ofReal (abs (∫ w, rho w * h w ∂(Carriers.reducedReferenceLaw Q))) ≤
      ENNReal.ofReal (C * s.1) * eLpNorm f (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) +
        ENNReal.ofReal (C * lam) *
          eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q)

/-! ## Euclidean and matrix algebra -/

private theorem euclideanNorm_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

private theorem euclideanNorm_zero' {d : ℕ} : euclideanNorm (0 : Vec d) = 0 := by
  unfold euclideanNorm euclideanSq dot
  simp

private theorem continuous_euclideanNorm' {d : ℕ} : Continuous fun x : Vec d => euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))

private theorem measurable_euclideanNorm_comp' {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {F : Ω → Vec d} (hF : Measurable[m] F) :
    Measurable[m] fun w => euclideanNorm (F w) :=
  continuous_euclideanNorm'.measurable.comp hF

private theorem abs_coord_le_euclideanNorm' {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

private theorem euclideanNorm_comb_le' {d : ℕ} (c : ℝ) (x y : Vec d) :
    euclideanNorm (c • x - y) ≤ |c| * euclideanNorm x + euclideanNorm y := by
  have hneg : -y = (-1 : ℝ) • y := by simp
  have h1 := TimeChange.euclideanNorm_add_le (c • x) ((-1 : ℝ) • y)
  rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul, abs_neg, abs_one,
    one_mul] at h1
  rw [sub_eq_add_neg, hneg]
  exact h1

private theorem dot_sub_right' {d : ℕ} (x y z : Vec d) : dot x (y - z) = dot x y - dot x z := by
  unfold dot
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem dot_smul_right' {d : ℕ} (c : ℝ) (x y : Vec d) :
    dot x (c • y) = c * dot x y := by
  unfold dot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem mulVec_apply_eq_sum' {d : ℕ} (A : Mat d) (x : Vec d) (i : Fin d) :
    A.mulVec x i = ∑ j, A i j * x j := rfl

private theorem dot_mulVec_expand' {d : ℕ} (x : Vec d) (A : Mat d) (y : Vec d) :
    dot x (A.mulVec y) = ∑ i, ∑ j, x i * A i j * y j := by
  unfold dot
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_apply_eq_sum', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private theorem dot_mulVec_unitVector' {d : ℕ} (x : Vec d) (A : Mat d) (i : Fin d) :
    dot x (A.mulVec (unitVector i)) = ∑ j, x j * A j i := by
  unfold dot
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mulVec_apply_eq_sum']
  congr 1
  simp [unitVector, Pi.single_apply]

private theorem double_sum_eq_mulVec' {d : ℕ} (D : Vec d) (A : Mat d) (x : Vec d) :
    ∑ i, ∑ j, D i * A i j * x j = ∑ i, D i * (A.mulVec x) i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mulVec_apply_eq_sum', Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The affine coefficient identity used for the test-function divergence: the vector
`½ a Df - g` paired with a test vector `D`. -/
private theorem sum_affine_mul' {d : ℕ} (A : Mat d) (x g D : Vec d) :
    ∑ i, ((1 / 2 : ℝ) * (A.mulVec x) i - g i) * D i =
      (1 / 2 : ℝ) * (∑ i, ∑ j, D i * A i j * x j) - ∑ i, g i * D i := by
  have h1 : ∀ i, ((1 / 2 : ℝ) * (A.mulVec x) i - g i) * D i =
      (1 / 2 : ℝ) * (D i * (A.mulVec x) i) - g i * D i := fun i => by ring
  simp only [h1]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, double_sum_eq_mulVec']

/-! ## Measurability and integrability -/

private theorem measurable_mulVec_field' {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    (A : Ω → Mat d) (v : Ω → Vec d) (hA : Measurable[m] A) (hv : Measurable[m] v) :
    Measurable[m] fun ω => (A ω).mulVec (v ω) := by
  have hcont : Continuous fun M : Mat d => M := continuous_id
  refine measurable_pi_iff.mpr fun i => ?_
  have hsum : Measurable[m] fun ω => ∑ j, A ω i j * v ω j :=
    Finset.measurable_sum _ fun j _ =>
      ((hcont.matrix_elem i j).measurable.comp hA).mul ((measurable_pi_apply j).comp hv)
  exact hsum

private theorem measurable_coord_comp' {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {F : Ω → Vec d} (hF : Measurable[m] F) (i : Fin d) : Measurable[m] fun w => F w i :=
  (measurable_pi_apply i).comp hF

/-- A vector field is `m`-measurable when each coordinate is, for an arbitrary σ-algebra `m`. The
σ-algebra is an implicit binder, so it unifies with the goal's `localSigma` σ-algebra rather than
synthesizing the global instance on `FieldPair d`. -/
private theorem measurable_of_coord_measurable' {Ω : Type*} {m : MeasurableSpace Ω} {d : ℕ}
    {F : Ω → Vec d} (h : ∀ i : Fin d, Measurable[m] fun w => F w i) : Measurable[m] F :=
  measurable_pi_iff.mpr h

private theorem measurable_coeff_zero_localSigma' {d : ℕ} {U : Set (Vec d)}
    (h0 : (0 : Vec d) ∈ U) : Measurable[localSigma U] fun w : FieldPair d => w.1 0 := by
  have hpair : Measurable[localSigma U] fun w : FieldPair d => (w.1 0, w.2 0) := by
    refine measurable_iff_comap_le.2 ?_
    unfold localSigma
    exact le_iSup_of_le (⟨0, h0⟩ : U) le_rfl
  exact measurable_fst.comp hpair

private theorem memLp_of_norm_le_mul' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {q : ℝ≥0∞} {F g : Ω → ℝ} (hg : MemLp g q μ) (hF : Measurable F)
    (h : ∀ᵐ w ∂μ, ‖F w‖ ≤ g w) : MemLp F q μ :=
  MemLp.mono' hg hF.aestronglyMeasurable h

private theorem memLp_coord' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {F : Ω → Vec d} {q : ℝ≥0∞} (hF : Measurable F)
    (hN : MemLp (fun w => euclideanNorm (F w)) q μ) (i : Fin d) :
    MemLp (fun w => F w i) q μ :=
  memLp_of_norm_le_mul' hN (measurable_coord_comp' hF i)
    (ae_of_all μ fun w => by
      rw [Real.norm_eq_abs]
      exact abs_coord_le_euclideanNorm' (F w) i)

private theorem integrable_mul_memLp_two' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun w => f w * g w) μ := by
  have hbound : Integrable (fun w => (f w ^ 2 + g w ^ 2) / 2) μ :=
    ((hf.integrable_sq).add (hg.integrable_sq)).div_const 2
  refine hbound.mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (ae_of_all μ fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f w), sq_abs (g w), sq_nonneg (|f w| - |g w|)]

/-- Integrability of `ρ G` from a finite occupation integral of `ρ |G|`. -/
private theorem integrable_rho_mul_of_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rho G : Ω → ℝ} (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w) (hGm : Measurable G)
    {q : ℝ≥0∞} (hG : MemLp G q μ) {K : ℝ}
    (hocc : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ ≤
      ENNReal.ofReal K * eLpNorm G q μ) :
    Integrable (fun w => rho w * G w) μ := by
  have hfin : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ < ⊤ :=
    lt_of_le_of_lt hocc
      (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top))
  have hAG : Measurable fun w => |G w| := by
    simpa only [Real.norm_eq_abs] using hGm.norm
  have hnn : ∀ w, 0 ≤ rho w * |G w| := fun w => mul_nonneg (hρ0 w) (abs_nonneg _)
  have hlint : ∫⁻ w, ENNReal.ofReal (rho w * |G w|) ∂μ =
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ :=
    lintegral_congr fun w => ENNReal.ofReal_mul (hρ0 w)
  have hgI : Integrable (fun w => rho w * |G w|) μ := by
    refine ⟨(hρm.mul hAG).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all μ hnn), hlint]
    exact hfin
  refine hgI.mono' (hρm.mul hGm).aestronglyMeasurable (ae_of_all μ fun w => ?_)
  show ‖rho w * G w‖ ≤ rho w * |G w|
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 w)] <;> exact le_rfl

/-- The occupation integral of `ρ |G|` is bounded by the `L^q` norm of `G`. -/
private theorem integral_rho_abs_le' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rho G : Ω → ℝ} (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w) (hGm : Measurable G)
    {K : ℝ} (hK : 0 ≤ K) {q : ℝ≥0∞} (hG : MemLp G q μ)
    (hocc : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ ≤
      ENNReal.ofReal K * eLpNorm G q μ) :
    ∫ w, rho w * |G w| ∂μ ≤ K * (eLpNorm G q μ).toReal := by
  have hAG : Measurable fun w => |G w| := by
    simpa only [Real.norm_eq_abs] using hGm.norm
  have hnn : 0 ≤ᵐ[μ] fun w => rho w * |G w| :=
    ae_of_all μ fun w => mul_nonneg (hρ0 w) (abs_nonneg _)
  have hlint : ∫⁻ w, ENNReal.ofReal (rho w * |G w|) ∂μ =
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ :=
    lintegral_congr fun w => ENNReal.ofReal_mul (hρ0 w)
  have hne : ENNReal.ofReal K * eLpNorm G q μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hρm.mul hAG).aestronglyMeasurable, hlint]
  calc (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂μ).toReal
      ≤ (ENNReal.ofReal K * eLpNorm G q μ).toReal := ENNReal.toReal_mono hne hocc
    _ = K * (eLpNorm G q μ).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]

/-- `L¹` norm bounded by the `L^q` norm on a probability space, for `1 ≤ q`. -/
private theorem integral_abs_le_eLpNorm_toReal' {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hf : MemLp f (ENNReal.ofReal q) μ) :
    ∫ w, |f w| ∂μ ≤ (eLpNorm f (ENNReal.ofReal q) μ).toReal := by
  have hle : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hq
  have h1 : eLpNorm f 1 μ ≤ eLpNorm f (ENNReal.ofReal q) μ := by
    refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hle hf.aestronglyMeasurable).trans ?_
    simp
  have h2 : ∫ w, |f w| ∂μ = (eLpNorm f 1 μ).toReal := by
    have h3 : ∫ w, |f w| ∂μ = ∫ w, ‖f w‖ ∂μ := by simp only [Real.norm_eq_abs]
    rw [h3, integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  rw [h2]
  exact ENNReal.toReal_mono hf.eLpNorm_ne_top h1

private theorem abs_le_mul_toReal_of_ofReal_le' {x c : ℝ} {N : ℝ≥0∞} (hc : 0 ≤ c)
    (hN : N ≠ ⊤) (h : ENNReal.ofReal |x| ≤ ENNReal.ofReal c * N) :
    |x| ≤ c * N.toReal := by
  have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) h
  rwa [ENNReal.toReal_ofReal (abs_nonneg x), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hc] at h'

private theorem ennreal_resolvent_bound' {c C s lam : ℝ} {Nf Ng : ℝ≥0∞} (hNf : Nf ≠ ⊤)
    (hNg : Ng ≠ ⊤) (hCs : 0 ≤ C * s) (hCl : 0 ≤ C * lam)
    (hcb : |c| ≤ C * s * Nf.toReal + C * lam * Ng.toReal) :
    ENNReal.ofReal |c| ≤ ENNReal.ofReal (C * s) * Nf + ENNReal.ofReal (C * lam) * Ng := by
  have h1 : 0 ≤ C * s * Nf.toReal := mul_nonneg hCs ENNReal.toReal_nonneg
  have h2 : 0 ≤ C * lam * Ng.toReal := mul_nonneg hCl ENNReal.toReal_nonneg
  have key : ENNReal.ofReal (C * s * Nf.toReal + C * lam * Ng.toReal) =
      ENNReal.ofReal (C * s) * Nf + ENNReal.ofReal (C * lam) * Ng := by
    rw [ENNReal.ofReal_add h1 h2, ENNReal.ofReal_mul hCs, ENNReal.ofReal_mul hCl,
      ENNReal.ofReal_toReal hNf, ENNReal.ofReal_toReal hNg]
  rw [← key]
  exact ENNReal.ofReal_le_ofReal hcb

/-! ## The reduced coefficient -/

private theorem isProbabilityMeasure_reducedRef' {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
  by unfold Carriers.reducedReferenceLaw; exact inferInstance

private theorem reducedRef_map_fst' {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    (Carriers.reducedReferenceLaw Q).map (fun w : FieldPair d => w.1) =
      coefficientLaw Q.measure := by
  unfold Carriers.reducedReferenceLaw coefficientLaw
  rw [Measure.map_map continuous_fst.measurable
    (EinsteinRelation.Probability.measurable_reduce (d := d))]
  rfl

private theorem ae_reducedRef_isElliptic' {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q),
      IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun x => w.1 x) := by
  have h := Correctors.ae_coefficientLaw_isElliptic Q
  rw [← reducedRef_map_fst' Q] at h
  exact ae_of_ae_map continuous_fst.measurable.aemeasurable h

/-- The reduced coefficient at the origin is bounded almost everywhere by the physical
ellipticity constant `exp(2Λ₀) Λ₀`, in the Euclidean operator norm. -/
private theorem ae_reducedRef_opBound' {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ ξ : Vec d,
      euclideanNorm ((w.1 0).mulVec ξ) ≤ (Real.exp (2 * Λ₀) * Λ₀) * euclideanNorm ξ := by
  have hK : 0 < Real.exp (2 * Λ₀) * Λ₀ :=
    mul_pos (Real.exp_pos _) (by linarith [Q.ellipticity_parameter])
  filter_upwards [ae_reducedRef_isElliptic' Q] with w hw
  intro ξ
  exact Correctors.isElliptic_mulVec_euclideanNorm_le hK hw 0 ξ

/-! ## Core algebra for one instance of the premises -/

/-- The resolvent identity and the bound of Lemma 4.3 for one fixed instance. The premises are
the instances of `WeakResolventStep`, `DivergenceStatement` and `OccupationStatement` at this
environment, force, exponent and resolvent density. -/
theorem resolvent_core {d : ℕ} (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ]
    (hQ : IsStationary μ) (K : ℝ)
    (hop : ∀ᵐ w ∂μ, ∀ ξ : Vec d, euclideanNorm ((w.1 0).mulVec ξ) ≤ K * euclideanNorm ξ)
    (lam l p s CO CD C : ℝ) (i₀ : Fin d) (rho : FieldPair d → ℝ)
    (Drho : FieldPair d → Vec d) (f : FieldPair d → ℝ) (Df : FieldPair d → Vec d)
    (h : FieldPair d → ℝ) (G : FieldPair d → Vec d)
    (hl0 : 0 < lam) (hl : 0 < l) (hp : 1 < p) (hs0 : 0 ≤ s) (hsl : s ≤ lam ^ 2)
    (hCO : 0 ≤ CO) (hCD : 0 ≤ CD) (hC1 : 2 * CO + 1 ≤ C) (hC2 : CD ≤ C)
    (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w)
    (hEq : SatisfiesReducedGeneratorEquation μ hQ lam f Df h G i₀)
    (hfM : MemLp f (ENNReal.ofReal (2 * p)) μ)
    (hDfM : MemLp (fun w => euclideanNorm (Df w)) (ENNReal.ofReal (2 * p)) μ)
    (hhM : MemLp h (ENNReal.ofReal (2 * p)) μ)
    (hGM : MemLp (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ)
    (hfL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] f)
    (hDfL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] Df)
    (hhL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] h)
    (hGL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] G)
    (hWI : s * (∫ w, rho w * f w ∂μ) - s * (∫ w, f w ∂μ) =
      -(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ) +
        lam * (∫ w, rho w * (∑ j : Fin d, (w.1 0) j i₀ * Df w j) ∂μ))
    (hDivF : ∀ F : FieldPair d → Vec d,
      Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] F →
      MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) μ →
      (Integrable (fun w => dot (Drho w) (F w)) μ ∧
        ENNReal.ofReal (abs (∫ w, dot (Drho w) (F w) ∂μ)) ≤
          ENNReal.ofReal (CD * lam) *
            eLpNorm (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) μ) ∧
      ∀ h' : FieldPair d → ℝ, MemLp h' (ENNReal.ofReal (2 * p)) μ →
        HasWeakHorizontalDivergence μ hQ F h' →
        Integrable (fun w => rho w * h' w) μ ∧
          (∫ w, rho w * h' w ∂μ) = -(∫ w, dot (Drho w) (F w) ∂μ))
    (hOccF : ∀ G' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G' →
      MemLp G' (ENNReal.ofReal (2 * p)) μ →
      (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G' w| ∂μ) ≤
        ENNReal.ofReal (CO * (1 + s * (lam ^ 2)⁻¹)) * eLpNorm G' (ENNReal.ofReal (2 * p)) μ) :
    (Integrable (fun w => rho w * f w) μ ∧ Integrable (fun w => rho w * h w) μ ∧
      Integrable (fun w => dot (Drho w) (G w)) μ ∧
      s * (∫ w, rho w * f w ∂μ) - s * (∫ w, f w ∂μ) =
        (∫ w, rho w * h w ∂μ) - (∫ w, dot (Drho w) (G w) ∂μ)) ∧
    ENNReal.ofReal (abs (∫ w, rho w * h w ∂μ)) ≤
      ENNReal.ofReal (C * s) * eLpNorm f (ENNReal.ofReal (2 * p)) μ +
        ENNReal.ofReal (C * lam) *
          eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ := by
  -- Sets and measurability of the local σ-algebras.
  have hcont : Continuous fun M : Mat d => M := continuous_id
  have hlam2 : 0 < lam ^ 2 := pow_pos hl0 2
  have hU0 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm y < l / (2 * lam)} := by
    show euclideanNorm (0 : Vec d) < l / (2 * lam)
    rw [euclideanNorm_zero']
    exact div_pos hl (by linarith)
  have hsub : {y : Vec d | euclideanNorm y < l / (2 * lam)} ⊆
      {x : Vec d | euclideanNorm x < l / lam} := by
    intro y hy
    rw [Set.mem_setOf_eq] at hy ⊢
    exact lt_of_lt_of_le hy (div_le_div_of_nonneg_left hl.le hl0 (by linarith))
  have hMono := Probability.localSigma_mono hsub
  have hfm : Measurable f := hfL.mono (Probability.localSigma_le_borel _) le_rfl
  have hGm : Measurable G := hGL.mono (Probability.localSigma_le_borel _) le_rfl
  have hfLam : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] f :=
    hfL.mono hMono le_rfl
  have hA0L : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}]
      fun w : FieldPair d => w.1 0 :=
    measurable_coeff_zero_localSigma' hU0
  -- The coefficient-times-gradient field `AD = a Df` and the vector field `V = ½ a Df - G`.
  obtain ⟨AD, hAD⟩ : ∃ AD : FieldPair d → Vec d, ∀ w, AD w = (w.1 0).mulVec (Df w) :=
    ⟨fun w => (w.1 0).mulVec (Df w), fun w => rfl⟩
  have hADL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] AD := by
    have e : AD = fun w => (w.1 0).mulVec (Df w) := funext hAD
    rw [e]
    exact measurable_mulVec_field' (fun w : FieldPair d => w.1 0) Df hA0L hDfL
  have hADm : Measurable AD := hADL.mono (Probability.localSigma_le_borel _) le_rfl
  obtain ⟨V, hV⟩ : ∃ V : FieldPair d → Vec d, ∀ w, V w = (1 / 2 : ℝ) • AD w - G w :=
    ⟨fun w => (1 / 2 : ℝ) • AD w - G w, fun w => rfl⟩
  have hVi : ∀ w i, V w i = (1 / 2 : ℝ) * AD w i - G w i := fun w i => by
    simp only [hV w, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hVL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] V := by
    refine measurable_of_coord_measurable' fun i => ?_
    simp only [hVi]
    exact ((measurable_coord_comp' hADL i).const_mul (1 / 2 : ℝ)).sub
      (measurable_coord_comp' hGL i)
  have hVm : Measurable V := hVL.mono (Probability.localSigma_le_borel _) le_rfl
  -- The scalar `cc = a e₁ · Df` and the modified source `ht = h - λ cc`.
  obtain ⟨cc, hcc⟩ : ∃ cc : FieldPair d → ℝ, ∀ w, cc w = ∑ j : Fin d, (w.1 0) j i₀ * Df w j :=
    ⟨fun w => ∑ j : Fin d, (w.1 0) j i₀ * Df w j, fun w => rfl⟩
  have hccL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] cc := by
    have e : cc = fun w => ∑ j : Fin d, (w.1 0) j i₀ * Df w j := funext hcc
    rw [e]
    refine Finset.measurable_sum _ fun j _ => ?_
    exact ((hcont.matrix_elem j i₀).measurable.comp hA0L).mul (measurable_coord_comp' hDfL j)
  have hccm : Measurable cc := hccL.mono (Probability.localSigma_le_borel _) le_rfl
  have hccLam : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] cc :=
    hccL.mono hMono le_rfl
  obtain ⟨ht, hht⟩ : ∃ ht : FieldPair d → ℝ, ∀ w, ht w = h w - lam * cc w :=
    ⟨fun w => h w - lam * cc w, fun w => rfl⟩
  -- Integrability exponents.
  have h2p : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have h1p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hDf2 : MemLp (fun w => euclideanNorm (Df w)) 2 μ := hDfM.mono_exponent h2p
  have hG2 : MemLp (fun w => euclideanNorm (G w)) 2 μ := hGM.mono_exponent h2p
  have hh2 : MemLp h 2 μ := hhM.mono_exponent h2p
  -- Pointwise bounds from the coefficient bound `hop`.
  have hccB : ∀ᵐ w ∂μ, ‖cc w‖ ≤ (K * euclideanNorm (unitVector i₀)) * euclideanNorm (Df w) := by
    filter_upwards [hop] with w hw
    have hcd : cc w = dot (Df w) ((w.1 0).mulVec (unitVector i₀)) := by
      rw [hcc w, dot_mulVec_unitVector']
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    have h1 := TimeChange.abs_dot_le_euclideanNorm (Df w) ((w.1 0).mulVec (unitVector i₀))
    have h2 : euclideanNorm ((w.1 0).mulVec (unitVector i₀)) ≤
        K * euclideanNorm (unitVector i₀) := hw (unitVector i₀)
    rw [Real.norm_eq_abs, hcd]
    calc |dot (Df w) ((w.1 0).mulVec (unitVector i₀))|
        ≤ euclideanNorm (Df w) * euclideanNorm ((w.1 0).mulVec (unitVector i₀)) := h1
      _ ≤ euclideanNorm (Df w) * (K * euclideanNorm (unitVector i₀)) :=
          mul_le_mul_of_nonneg_left h2 (euclideanNorm_nonneg' _)
      _ = (K * euclideanNorm (unitVector i₀)) * euclideanNorm (Df w) := mul_comm _ _
  have hccMq : MemLp cc (ENNReal.ofReal (2 * p)) μ :=
    memLp_of_norm_le_mul' (hDfM.const_mul (K * euclideanNorm (unitVector i₀))) hccm hccB
  have hccMq2 : MemLp cc 2 μ :=
    memLp_of_norm_le_mul' (hDf2.const_mul (K * euclideanNorm (unitVector i₀))) hccm hccB
  have hADB : ∀ᵐ w ∂μ, ∀ i : Fin d, ‖AD w i‖ ≤ K * euclideanNorm (Df w) := by
    filter_upwards [hop] with w hw
    intro i
    have hADn : euclideanNorm (AD w) ≤ K * euclideanNorm (Df w) := by
      rw [hAD w]
      exact hw (Df w)
    rw [Real.norm_eq_abs]
    exact (abs_coord_le_euclideanNorm' (AD w) i).trans hADn
  have hADi2 : ∀ i : Fin d, MemLp (fun w => AD w i) 2 μ := fun i =>
    memLp_of_norm_le_mul' (hDf2.const_mul K) (measurable_coord_comp' hADm i)
      (hADB.mono fun w hw => hw i)
  have hVB : ∀ᵐ w ∂μ, ‖euclideanNorm (V w)‖ ≤
      |(1 / 2 : ℝ)| * (K * euclideanNorm (Df w)) + euclideanNorm (G w) := by
    filter_upwards [hop] with w hw
    have hADn : euclideanNorm (AD w) ≤ K * euclideanNorm (Df w) := by
      rw [hAD w]
      exact hw (Df w)
    rw [Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg' _), hV w]
    refine (euclideanNorm_comb_le' (1 / 2 : ℝ) (AD w) (G w)).trans ?_
    have hm := mul_le_mul_of_nonneg_left hADn (abs_nonneg (1 / 2 : ℝ))
    linarith
  have hgV : MemLp (fun w => |(1 / 2 : ℝ)| * (K * euclideanNorm (Df w)) + euclideanNorm (G w))
      (ENNReal.ofReal (2 * p)) μ :=
    ((hDfM.const_mul K).const_mul |(1 / 2 : ℝ)|).add hGM
  have hVmq : MemLp (fun w => euclideanNorm (V w)) (ENNReal.ofReal (2 * p)) μ :=
    memLp_of_norm_le_mul' hgV (measurable_euclideanNorm_comp' hVm) hVB
  have hhtM : MemLp ht (ENNReal.ofReal (2 * p)) μ := by
    have e : ht = fun w => h w - lam * cc w := funext hht
    rw [e]
    exact hhM.sub (hccMq.const_mul lam)
  have hhtI : Integrable ht μ := MemLp.integrable h1p hhtM
  have hViI : ∀ i : Fin d, Integrable (fun ω => V ω i) μ := fun i => by
    have hA1 : Integrable (fun ω => AD ω i) μ := MemLp.integrable (by norm_num) (hADi2 i)
    refine ((hA1.const_mul (1 / 2 : ℝ)).sub (hEq.2.2.1 i)).congr
      (Filter.Eventually.of_forall fun ω => ?_)
    exact (hVi ω i).symm
  -- The weak divergence identity for `V` against the modified source `ht`.
  have hWDV : HasWeakHorizontalDivergence μ hQ V ht := by
    refine ⟨hViI, hhtI, fun F hF DF hDF => ?_⟩
    have hweak := hEq.2.2.2 F hF DF hDF
    have hDFL2 : ∀ i, MemLp (DF i) 2 μ := fun i => Lp.memLp (DF i)
    have hFL2 : MemLp (⇑F) 2 μ := Lp.memLp F
    have hS1pt : ∀ ω, ∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j =
        ∑ i : Fin d, DF i ω * AD ω i := fun ω => by
      rw [hAD ω]
      exact double_sum_eq_mulVec' (fun i => DF i ω) (ω.1 0) (Df ω)
    have hS1 : Integrable (fun ω => ∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) μ :=
      (integrable_finset_sum _ fun i _ => integrable_mul_memLp_two' (hDFL2 i) (hADi2 i)).congr
        (Filter.Eventually.of_forall fun ω => (hS1pt ω).symm)
    have hS2 : Integrable (fun ω => ∑ i : Fin d, G ω i * DF i ω) μ :=
      integrable_finset_sum _ fun i _ =>
        integrable_mul_memLp_two' (memLp_coord' hGm hG2 i) (hDFL2 i)
    have hhF : Integrable (fun ω => h ω * F ω) μ := integrable_mul_memLp_two' hh2 hFL2
    have hcF : Integrable (fun ω => F ω * cc ω) μ := integrable_mul_memLp_two' hFL2 hccMq2
    have hV' : ∀ ω i, V ω i = (1 / 2 : ℝ) * ((ω.1 0).mulVec (Df ω)) i - G ω i := fun ω i => by
      rw [hVi ω i, hAD ω]
    have P1 : ∀ ω, ∑ i : Fin d, V ω i * DF i ω =
        (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) -
          ∑ i : Fin d, G ω i * DF i ω := by
      intro ω
      simp only [hV' ω]
      exact sum_affine_mul' (ω.1 0) (Df ω) (G ω) (fun i => DF i ω)
    have e1 : ∫ ω, (∑ i : Fin d, V ω i * DF i ω) ∂μ =
        ∫ ω, ((1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) -
          ∑ i : Fin d, G ω i * DF i ω) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall P1)
    have e2 : ∫ ω, ((1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) -
          ∑ i : Fin d, G ω i * DF i ω) ∂μ =
        (1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Df ω j) ∂μ) -
          ∫ ω, (∑ i : Fin d, G ω i * DF i ω) ∂μ := by
      rw [integral_sub (hS1.const_mul _) hS2, integral_const_mul]
    have e3' : ∫ ω, ht ω * F ω ∂μ = ∫ ω, (h ω * F ω - lam * (F ω * cc ω)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hht ω]; ring)
    have e3 : ∫ ω, ht ω * F ω ∂μ = (∫ ω, h ω * F ω ∂μ) - lam * ∫ ω, F ω * cc ω ∂μ := by
      rw [e3', integral_sub hhF (hcF.const_mul lam), integral_const_mul]
    have e4 : ∫ ω, F ω * (∑ j : Fin d, (ω.1 0) j i₀ * Df ω j) ∂μ =
        ∫ ω, F ω * cc ω ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hcc ω])
    rw [e4] at hweak
    rw [e1, e2, e3]
    linarith [hweak]
  -- Apply the divergence premise to `V` and `G`.
  obtain ⟨⟨hdV, -⟩, hρV⟩ := hDivF V hVL hVmq
  obtain ⟨⟨hdG, hdGbd⟩, -⟩ := hDivF G hGL hGM
  obtain ⟨hρht, hρhtEq⟩ := hρV ht hhtM hWDV
  -- The occupation integrability of `ρ f` and `ρ cc`.
  have hρf : Integrable (fun ω => rho ω * f ω) μ :=
    integrable_rho_mul_of_bound hρm hρ0 hfm hfM (hOccF f hfLam hfM)
  have hρc : Integrable (fun ω => rho ω * cc ω) μ :=
    integrable_rho_mul_of_bound hρm hρ0 hccm hccMq (hOccF cc hccLam hccMq)
  have hρh : Integrable (fun ω => rho ω * h ω) μ := by
    have hsum : Integrable (fun ω => rho ω * ht ω + lam * (rho ω * cc ω)) μ :=
      hρht.add (hρc.const_mul lam)
    refine hsum.congr (Filter.Eventually.of_forall fun ω => ?_)
    show rho ω * ht ω + lam * (rho ω * cc ω) = rho ω * h ω
    rw [hht ω]
    ring
  -- The dot-product identity for `Dρ · V`.
  have D1 : ∀ ω, dot (Drho ω) (V ω) =
      (1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, Drho ω i * (ω.1 0) i j * Df ω j) -
        dot (Drho ω) (G ω) := by
    intro ω
    rw [hV ω, dot_sub_right', dot_smul_right', hAD ω, dot_mulVec_expand']
  have hS1ρ : Integrable
      (fun ω => ∑ i : Fin d, ∑ j : Fin d, Drho ω i * (ω.1 0) i j * Df ω j) μ :=
    ((hdV.const_mul 2).add (hdG.const_mul 2)).congr
      (Filter.Eventually.of_forall fun ω => by
        show 2 * dot (Drho ω) (V ω) + 2 * dot (Drho ω) (G ω) =
          ∑ i : Fin d, ∑ j : Fin d, Drho ω i * (ω.1 0) i j * Df ω j
        rw [D1 ω]
        ring)
  have hdVint : ∫ ω, dot (Drho ω) (V ω) ∂μ =
      (1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, Drho ω i * (ω.1 0) i j * Df ω j) ∂μ) -
        ∫ ω, dot (Drho ω) (G ω) ∂μ := by
    have e : ∫ ω, dot (Drho ω) (V ω) ∂μ =
        ∫ ω, ((1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, Drho ω i * (ω.1 0) i j * Df ω j) -
          dot (Drho ω) (G ω)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall D1)
    rw [e, integral_sub (hS1ρ.const_mul _) hdG, integral_const_mul]
  -- The modified source integral `E[ρ ht] = E[ρ h] - λ E[ρ cc]`.
  have e5 : ∫ ω, rho ω * ht ω ∂μ = ∫ ω, (rho ω * h ω - lam * (rho ω * cc ω)) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hht ω]; ring)
  have hρhtInt : ∫ ω, rho ω * ht ω ∂μ =
      (∫ ω, rho ω * h ω ∂μ) - lam * ∫ ω, rho ω * cc ω ∂μ := by
    rw [e5, integral_sub hρh (hρc.const_mul lam), integral_const_mul]
  have e6 : ∫ ω, rho ω * (∑ j : Fin d, (ω.1 0) j i₀ * Df ω j) ∂μ =
      ∫ ω, rho ω * cc ω ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => by simp only [hcc ω])
  rw [e6] at hWI
  -- The arithmetic of the resolvent identity.
  have htest : -(1 / 2 : ℝ) *
        (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ) +
          lam * (∫ ω, rho ω * cc ω ∂μ) =
      (∫ w, rho w * h w ∂μ) - ∫ w, dot (Drho w) (G w) ∂μ := by
    linarith [hρhtInt, hρhtEq, hdVint]
  -- Occupation and divergence bounds in real form.
  have hKnn : 0 ≤ CO * (1 + s * (lam ^ 2)⁻¹) :=
    mul_nonneg hCO (add_nonneg zero_le_one (mul_nonneg hs0 (inv_nonneg.2 hlam2.le)))
  have hsinv : s * (lam ^ 2)⁻¹ ≤ 1 := by
    calc s * (lam ^ 2)⁻¹ ≤ lam ^ 2 * (lam ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hsl (inv_nonneg.2 hlam2.le)
      _ = 1 := mul_inv_cancel₀ hlam2.ne'
  have hKocc : CO * (1 + s * (lam ^ 2)⁻¹) ≤ 2 * CO := by
    nlinarith [mul_nonneg hCO (sub_nonneg.2 hsinv)]
  have hocc : ∫ w, rho w * |f w| ∂μ ≤ (2 * CO) * (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal :=
    (integral_rho_abs_le' hρm hρ0 hfm hKnn hfM (hOccF f hfLam hfM)).trans
      (mul_le_mul_of_nonneg_right hKocc ENNReal.toReal_nonneg)
  have hL1 : ∫ w, |f w| ∂μ ≤ (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal :=
    integral_abs_le_eLpNorm_toReal' (by linarith) hfM
  have ha : |∫ w, rho w * f w ∂μ| ≤ ∫ w, rho w * |f w| ∂μ :=
    abs_integral_weighted_le μ rho f (ae_of_all μ hρ0)
  have hb : |∫ w, f w ∂μ| ≤ ∫ w, |f w| ∂μ := abs_integral_le_integral_abs
  have hdiv : |∫ w, dot (Drho w) (G w) ∂μ| ≤
      (CD * lam) * (eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ).toReal :=
    abs_le_mul_toReal_of_ofReal_le' (mul_nonneg hCD hl0.le) hGM.eLpNorm_ne_top hdGbd
  obtain ⟨hid, hcb⟩ := resolvent_assembly_real
    (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal
    (eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ).toReal
    (2 * CO) CD lam s hs0 hWI htest ha hocc hb hL1 hdiv
  have hC0 : 0 ≤ C := by linarith
  have hcb' : |∫ w, rho w * h w ∂μ| ≤
      C * s * (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal +
        C * lam * (eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ).toReal := by
    have k1 : (2 * CO + 1) * s * (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal ≤
        C * s * (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC1 hs0) ENNReal.toReal_nonneg
    have k2 : CD * lam * (eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ).toReal ≤
        C * lam * (eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p)) μ).toReal :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 hl0.le) ENNReal.toReal_nonneg
    linarith
  refine ⟨⟨hρf, hρh, hdG, hid⟩, ?_⟩
  exact ennreal_resolvent_bound' hfM.eLpNorm_ne_top hGM.eLpNorm_ne_top (mul_nonneg hC0 hs0)
    (mul_nonneg hC0 hl0.le) hcb'

/-! ## Lemma 4.3 from the three premises -/

/-- Lemma 4.3 (`entropy.resolvent`, `paper/main.tex:643-675`), conditional on the weak resolvent
identity (`WeakResolventStep`), the divergence lemma (`DivergenceStatement`), and the occupation
bound (`OccupationStatement`). The witness is `C = 2 CO + 1 + CD`, where `CO` is the occupation
constant and `CD` the divergence constant at the chosen exponent. -/
theorem resolvent_of_weak_divergence_occupation (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hWeak : WeakResolventStep d hd Λ₀ r₀) (hDiv : DivergenceStatement d hd Λ₀ r₀)
    (hOcc : OccupationStatement d hd Λ₀ r₀) : ResolventStatement d hd Λ₀ r₀ := by
  unfold ResolventStatement
  by_cases hΛ : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  · obtain ⟨hΛ₀, hr₀⟩ := hΛ
    obtain ⟨lW, hrW, hW⟩ := hWeak
    obtain ⟨lD, hrD, hD⟩ := hDiv
    obtain ⟨lO, hrO, hO⟩ := hOcc hΛ₀ hr₀
    refine ⟨max (max lW lD) lO,
      by linarith [le_max_left lW lD, le_max_left (max lW lD) lO], ?_⟩
    intro l hl
    have hlW : lW ≤ l := le_trans (le_trans (le_max_left lW lD) (le_max_left _ lO)) hl
    have hlD : lD ≤ l := le_trans (le_trans (le_max_right lW lD) (le_max_left _ lO)) hl
    have hlO : lO ≤ l := le_trans (le_max_right _ lO) hl
    have hlpos : 0 < l := by linarith
    obtain ⟨pW, hpW, hW'⟩ := hW l hlW
    obtain ⟨pD, hpD, hD'⟩ := hD l hlD
    obtain ⟨pO, hpO, hO'⟩ := hO l hlO
    refine ⟨max (max pW pD) pO,
      lt_of_lt_of_le hpW (le_trans (le_max_left pW pD) (le_max_left _ pO)), ?_⟩
    intro p hp
    have hpW' : pW ≤ p := le_trans (le_trans (le_max_left pW pD) (le_max_left _ pO)) hp
    have hpD' : pD ≤ p := le_trans (le_trans (le_max_right pW pD) (le_max_left _ pO)) hp
    have hpO' : pO ≤ p := le_trans (le_max_right _ pO) hp
    obtain ⟨_, _, hWb⟩ := hW' p hpW'
    obtain ⟨CD, hCD, hDb⟩ := hD' p hpD'
    obtain ⟨CO, hCO, hOb⟩ := hO' (2 * p) (by linarith)
    refine ⟨2 * CO + 1 + CD, by linarith, ?_⟩
    intro Q hQ lam hlam hl1 IQ P origin hyp s hs rho hrho Drho hDrho f Df h G
      hfM hDfM hhM hGM hfL hDfL hhL hGL hEq
    obtain ⟨hIQ, hOrig⟩ := hyp
    subst hIQ
    haveI := isProbabilityMeasure_reducedRef' Q
    have hWI := hWb Q hQ lam hlam hl1 Q.measure P origin ⟨rfl, hOrig⟩ s hs rho hrho Drho
      hDrho f Df hEq.1 hfM hDfM hfL hDfL
    exact resolvent_core (Carriers.reducedReferenceLaw Q) hQ
      (Real.exp (2 * Λ₀) * Λ₀) (ae_reducedRef_opBound' Q)
      lam l p s.1 CO CD (2 * CO + 1 + CD) ⟨0, by omega⟩ rho Drho
      f Df h G hlam hlpos (lt_of_lt_of_le hpW hpW') s.2.le hs hCO hCD (by linarith)
      (by linarith) hrho.1 hrho.2.1 hEq hfM hDfM hhM hGM hfL hDfL hhL hGL hWI
      (fun F hF hFm => hDb Q hQ lam hlam hl1 Q.measure P origin ⟨rfl, hOrig⟩ s hs rho hrho
        Drho hDrho F hF hFm)
      (fun G' hG' hG'M => (hOb Q lam hlam hl1 Q.measure P origin ⟨rfl, hOrig⟩ G' hG' hG'M
        1 one_pos s).2 rho hrho)
  · refine ⟨|r₀| + 1, by linarith [le_abs_self r₀, abs_nonneg r₀], fun l _ =>
      ⟨2, by norm_num, fun p _ => ⟨0, le_rfl, fun Q =>
        (hΛ ⟨Q.ellipticity_parameter, Q.range_parameter⟩).elim⟩⟩⟩

end EinsteinRelation.Entropy
