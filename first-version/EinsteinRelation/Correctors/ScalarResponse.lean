import EinsteinRelation.Calculus.EnvironmentWeakCalculus
import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Carriers.ScalarAveragingTwin
import EinsteinRelation.Correctors.HeatSmoothing
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.TimeChange.EuclideanTransport

/-! # The response bound of Proposition 6.1 from the scalar decomposition

Source: `paper/main.tex:978-997` (`scalar.decomposition`, response `eq.scalar-response`) and the
proof of the response in Step 6 (`paper/main.tex:1086-1100`).

The response bound is derived from three inputs:

* the decomposition data `ψ, h, e, Dψ, E, P` of the first conjunct of `ScalarDecompositionTwin`:
  the reduced generator equation of `ψ` with right side `f - e` and flux `-E`, the divergence
  identity of `P` with right side `a e₁·Dψ - h`, the localization on `B_{C₀R}`, and the `L^{2p}`
  bounds;
* Lemma 4.3 (`entropy.resolvent`), in the scale-level form `ResolventAtScale`, applied to `ψ` with
  right side `f - e + λ h` and flux `-E + λ P`;
* the occupation bound (`regen.occupation`), in the scale-level form `OccupationAtScale` at the
  exponent `2p`, applied to `e` and `h`.

`reducedGeneratorEquation_combine` adds `λ h` to the right side and `λ P` to the flux, which is the
identity `L^λ ψ = f - e + λ h + D·(λ P - E)` of the paper.

The theorem `scalarResponse_of_decomposition` takes three premises beyond the first conjunct of the
twin: the localization of `Dψ` and of `f - e` on `B_{C₀R}` (Lemma 4.3 requires measurability of the
right side and of the derivative on the larger ball `B_{l/(2λ)}`), and the existence of a weak
horizontal gradient for every reduced Laplace density under the GMP conditioning of Lemma 4.1
(Lemma 4.3 is stated for each such gradient, and Lemma 4.1 supplies it only under that
conditioning).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

/-! ## Scale-level forms of Lemma 4.3 and of the occupation bound -/

/-- Lemma 4.3 (`entropy.resolvent`, `paper/main.tex:649-664`) at one scale `l`, one exponent `p`
and one constant `CR`. This is the body of `EinsteinRelation.Entropy.ResolventStatement` with the
quantifiers `∃ l₀`, `∀ l ≥ l₀`, `∃ p₀`, `∀ p ≥ p₀` and `∃ C` instantiated at `l`, `p` and `CR`. -/
def ResolventAtScale (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l p CR : ℝ) : Prop :=
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
      ENNReal.ofReal (CR * s.1) * eLpNorm f (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) +
        ENNReal.ofReal (CR * lam) *
          eLpNorm (fun w => euclideanNorm (G w)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q)

/-- The occupation bound (`regen.occupation`, `paper/main.tex:445-453`) at one exponent `p` and one
scale `l`, with constant `CO`: the body of `EinsteinRelation.Entropy.OccupationStatement` with the
quantifiers `∃ l₀`, `∀ l ≥ l₀`, `∃ p₀`, `∀ p ≥ p₀` and `∃ C` instantiated. -/
def OccupationAtScale (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l p CO : ℝ) : Prop :=
  1 ≤ Λ₀ → 1 ≤ r₀ →
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
      ENNReal.ofReal (CO * (T + (lam ^ 2)⁻¹)) *
        eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) ∧
    ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity IQ P origin_probability s rho →
      (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w|
          ∂(Carriers.reducedReferenceLaw Q)) ≤
        ENNReal.ofReal (CO * (1 + s.1 * (lam ^ 2)⁻¹)) *
          eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q)

/-! ## Euclidean and coordinate helpers -/

private theorem euclideanNorm_nonneg_sr {d : ℕ} (x : Vec d) : 0 ≤ euclideanNorm x :=
  Real.sqrt_nonneg _

private theorem euclideanNorm_neg_sr {d : ℕ} (x : Vec d) :
    euclideanNorm (-x) = euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  simp

private theorem continuous_euclideanNorm_sr {d : ℕ} :
    Continuous fun x : Vec d => euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i))

/-- The Euclidean norm of `-x + c • y` is at most `‖x‖ + |c| ‖y‖`. -/
private theorem euclideanNorm_flux_le_sr {d : ℕ} (x y : Vec d) (c : ℝ) :
    euclideanNorm (-x + c • y) ≤ euclideanNorm x + (|c|) * euclideanNorm y := by
  have h := TimeChange.euclideanNorm_add_le (-x) (c • y)
  rw [euclideanNorm_neg_sr, TimeChange.euclideanNorm_smul] at h
  exact h

/-- The dot product with a matrix image of a unit vector reads off a column. -/
private theorem dot_mulVec_unitVector_left_sr {d : ℕ} (A : Mat d) (i : Fin d) (y : Vec d) :
    dot (A.mulVec (unitVector i)) y = ∑ j, A j i * y j := by
  unfold dot
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  show ∑ k, A j k * unitVector i k = A j i
  simp [unitVector, Pi.single_apply]

/-! ## Measurability on the localized σ-algebras -/

/-- A field measurable for a localized σ-algebra is measurable for the Borel σ-algebra of the
field pair. -/
private theorem measurable_global_of_localSigma {d : ℕ} {U : Set (Vec d)} {β : Type*}
    [MeasurableSpace β] {F : FieldPair d → β} (hF : Measurable[localSigma U] F) : Measurable F :=
  hF.mono (Probability.localSigma_le_borel U) le_rfl

/-- The Euclidean norm of a localized vector field is measurable. -/
private theorem measurable_norm_of_localSigma {d : ℕ} {U : Set (Vec d)}
    {F : FieldPair d → Vec d} (hF : Measurable[localSigma U] F) :
    Measurable fun w => euclideanNorm (F w) :=
  measurable_global_of_localSigma
    ((continuous_euclideanNorm_sr (d := d)).measurable.comp hF)

private theorem measurable_add_localSigma_sr {Ω : Type*} {m : MeasurableSpace Ω} {f g : Ω → ℝ}
    (hf : Measurable[m] f) (hg : Measurable[m] g) : Measurable[m] fun w => f w + g w := by
  letI : MeasurableSpace Ω := m
  exact hf.add hg

private theorem measurable_const_mul_localSigma_sr {Ω : Type*} {m : MeasurableSpace Ω}
    {f : Ω → ℝ} (c : ℝ) (hf : Measurable[m] f) : Measurable[m] fun w => c * f w := by
  letI : MeasurableSpace Ω := m
  exact hf.const_mul c

private theorem measurable_flux_localSigma_sr {Ω : Type*} {d : ℕ} {m : MeasurableSpace Ω}
    {E P : Ω → Vec d} (c : ℝ) (hE : Measurable[m] E) (hP : Measurable[m] P) :
    Measurable[m] fun w => -(E w) + c • P w := by
  letI : MeasurableSpace Ω := m
  refine measurable_pi_iff.mpr fun i => ?_
  have h1 : Measurable fun w => E w i := (measurable_pi_apply i).comp hE
  have h2 : Measurable fun w => P w i := (measurable_pi_apply i).comp hP
  exact h1.neg.add (h2.const_mul c)

/-! ## Integrability of bounded products -/

/-- A horizontally smooth test is essentially bounded. -/
private theorem ae_bound_of_smoothTest_sr {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {F : Lp ℝ 2 Q} (hF : IsHorizontallySmoothTest Q hQ F) :
    ∃ M : ℝ, ∀ᵐ ω ∂Q, |F ω| ≤ M := by
  obtain ⟨G, hG, M, hM⟩ := hF []
  have hGF : G = F := hG
  rw [hGF] at hM
  exact ⟨M, hM⟩

/-- The horizontal derivative of a horizontally smooth test is essentially bounded. -/
private theorem ae_bound_of_derivative_sr {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {F D : Lp ℝ 2 Q}
    (hF : IsHorizontallySmoothTest Q hQ F) (hD : HasHorizontalLpDerivative Q hQ i F D) :
    ∃ M : ℝ, ∀ᵐ ω ∂Q, |D ω| ≤ M := by
  obtain ⟨G, hG, M, hM⟩ := hF [i]
  obtain ⟨h0, hh0, hGi⟩ := hG
  have h0F : h0 = F := hh0
  rw [h0F] at hGi
  have hDG : D = G := HasHorizontalLpDerivative.unique hD hGi
  refine ⟨M, ?_⟩
  rw [hDG]
  exact hM

/-- Adding `λ h` to the right side and `λ P` to the flux of the reduced generator equation. If
`ψ` solves the equation with right side `F` and flux `G`, and the divergence identity holds for
`P` with right side `a e₁·Dψ - h`, then `ψ` solves it with right side `F + λ h` and flux `G + λ P`.
The divergence identity is the premise that carries the `λ`-dependence. -/
theorem reducedGeneratorEquation_combine {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {ψ : FieldPair d → ℝ} {Dψ P : FieldPair d → Vec d}
    {F h : FieldPair d → ℝ} {G : FieldPair d → Vec d} {i₁ : Fin d} (lam : ℝ)
    (hEq : SatisfiesReducedGeneratorEquation Q hQ 0 ψ Dψ F G i₁)
    (hDiv : HasWeakHorizontalDivergence Q hQ P
      (fun ω => dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) - h ω))
    (hh : Integrable h Q) :
    SatisfiesReducedGeneratorEquation Q hQ lam ψ Dψ (fun ω => F ω + lam * h ω)
      (fun ω => G ω + lam • P ω) i₁ := by
  obtain ⟨hgrad, hIF, hIG, hid⟩ := hEq
  obtain ⟨hIP, hIh, hdiv⟩ := hDiv
  refine ⟨hgrad, hIF.add (hh.const_mul lam), fun i => ?_, fun F' hF' DF hDF => ?_⟩
  · exact ((hIG i).add ((hIP i).const_mul lam)).congr (ae_of_all _ fun ω => by simp)
  · obtain ⟨MF, hMF⟩ := ae_bound_of_smoothTest_sr hF'
    have hbdD : ∀ i : Fin d, ∃ M : ℝ, ∀ᵐ ω ∂Q, |DF i ω| ≤ M :=
      fun i => ae_bound_of_derivative_sr hF' (hDF i)
    choose MD hMD using hbdD
    have hbF : ∀ᵐ ω ∂Q, ‖F' ω‖ ≤ MF := by
      filter_upwards [hMF] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    have hbD : ∀ i : Fin d, ∀ᵐ ω ∂Q, ‖DF i ω‖ ≤ MD i := by
      intro i
      filter_upwards [hMD i] with ω hω
      rw [Real.norm_eq_abs]
      exact hω
    have hFF : Integrable (fun ω => F ω * F' ω) Q :=
      hIF.mul_bdd (Lp.aestronglyMeasurable F') hbF
    have hhF : Integrable (fun ω => h ω * F' ω) Q :=
      hh.mul_bdd (Lp.aestronglyMeasurable F') hbF
    have hdF : Integrable
        (fun ω => (dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) - h ω) * F' ω) Q :=
      hIh.mul_bdd (Lp.aestronglyMeasurable F') hbF
    have hGD : ∀ i : Fin d, Integrable (fun ω => G ω i * DF i ω) Q := fun i =>
      (hIG i).mul_bdd (Lp.aestronglyMeasurable (DF i)) (hbD i)
    have hPD : ∀ i : Fin d, Integrable (fun ω => P ω i * DF i ω) Q := fun i =>
      (hIP i).mul_bdd (Lp.aestronglyMeasurable (DF i)) (hbD i)
    have hsumG : Integrable (fun ω => ∑ i : Fin d, G ω i * DF i ω) Q :=
      integrable_finset_sum Finset.univ fun i _ => hGD i
    have hsumP : Integrable (fun ω => ∑ i : Fin d, P ω i * DF i ω) Q :=
      integrable_finset_sum Finset.univ fun i _ => hPD i
    have hid' : -(1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Dψ ω j) ∂Q) +
        0 * (∫ ω, F' ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) ∂Q) =
        (∫ ω, F ω * F' ω ∂Q) - ∫ ω, (∑ i : Fin d, G ω i * DF i ω) ∂Q :=
      hid F' hF' DF hDF
    have hdiv' : (∫ ω, (∑ i : Fin d, P ω i * DF i ω) ∂Q) =
        -(∫ ω, (dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) - h ω) * F' ω ∂Q) :=
      hdiv F' hF' DF hDF
    have hY : (∫ ω, F' ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) ∂Q) =
        ∫ ω, dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) * F' ω ∂Q := by
      refine integral_congr_ae (ae_of_all Q fun ω => ?_)
      show F' ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) =
        dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) * F' ω
      rw [dot_mulVec_unitVector_left_sr]
      ring
    have hsplit : (∫ ω, dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) * F' ω ∂Q) =
        (∫ ω, (dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) - h ω) * F' ω ∂Q) +
          ∫ ω, h ω * F' ω ∂Q := by
      rw [← integral_add hdF hhF]
      refine integral_congr_ae (ae_of_all Q fun ω => ?_)
      show dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) * F' ω =
        (dot ((ω.1 (0 : Vec d)).mulVec (unitVector i₁)) (Dψ ω) - h ω) * F' ω + h ω * F' ω
      ring
    have hE5 : (∫ ω, (F ω + lam * h ω) * F' ω ∂Q) =
        (∫ ω, F ω * F' ω ∂Q) + lam * ∫ ω, h ω * F' ω ∂Q := by
      have e1 : (fun ω => (F ω + lam * h ω) * F' ω) =
          fun ω => F ω * F' ω + lam * (h ω * F' ω) := by
        funext ω
        ring
      rw [e1, integral_add hFF (hhF.const_mul lam), integral_const_mul]
    have hE6 : (∫ ω, (∑ i : Fin d, (G ω + lam • P ω) i * DF i ω) ∂Q) =
        (∫ ω, (∑ i : Fin d, G ω i * DF i ω) ∂Q) +
          lam * ∫ ω, (∑ i : Fin d, P ω i * DF i ω) ∂Q := by
      have e2 : (fun ω => ∑ i : Fin d, (G ω + lam • P ω) i * DF i ω) =
          fun ω => (∑ i : Fin d, G ω i * DF i ω) + lam * ∑ i : Fin d, P ω i * DF i ω := by
        funext ω
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e2, integral_add hsumG (hsumP.const_mul lam), integral_const_mul]
    show -(1 / 2 : ℝ) * (∫ ω, (∑ i : Fin d, ∑ j : Fin d, DF i ω * (ω.1 0) i j * Dψ ω j) ∂Q) +
        lam * (∫ ω, F' ω * (∑ j : Fin d, (ω.1 0) j i₁ * Dψ ω j) ∂Q) =
      (∫ ω, (F ω + lam * h ω) * F' ω ∂Q) -
        ∫ ω, (∑ i : Fin d, (G ω + lam • P ω) i * DF i ω) ∂Q
    linear_combination hid' + lam * hY + lam * hsplit + lam * hdiv' - hE5 + hE6

/-! ## Norm and integral bounds for the response -/

/-- Converting `ofReal |c| ≤ ofReal A * x + ofReal B * y` with finite `x, y` to real bounds. -/
private theorem abs_le_of_ofReal_add_le_sr {c A B : ℝ} {x y : ENNReal} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hx : x ≠ ⊤) (hy : y ≠ ⊤)
    (h : ENNReal.ofReal (abs c) ≤ ENNReal.ofReal A * x + ENNReal.ofReal B * y) :
    abs c ≤ A * x.toReal + B * y.toReal := by
  have hax : ENNReal.ofReal A * x ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hx
  have hby : ENNReal.ofReal B * y ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hy
  have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hax, hby⟩) h
  rwa [ENNReal.toReal_ofReal (abs_nonneg c), ENNReal.toReal_add hax hby, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hA, ENNReal.toReal_ofReal hB] at h'

/-- The integral of `ρ |G|` is controlled by the `L^q` norm of `G` through the occupation bound. -/
private theorem integral_rho_abs_le_sr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rho G : Ω → ℝ} (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w) (hGm : Measurable G)
    {K : ℝ} (hK : 0 ≤ K) {q : ENNReal} (hG : MemLp G q μ)
    (hocc : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ ≤
      ENNReal.ofReal K * eLpNorm G q μ) :
    ∫ w, rho w * abs (G w) ∂μ ≤ K * (eLpNorm G q μ).toReal := by
  have hAG : Measurable fun w => abs (G w) := by
    simpa only [Real.norm_eq_abs] using hGm.norm
  have hnn : 0 ≤ᵐ[μ] fun w => rho w * abs (G w) :=
    ae_of_all μ fun w => mul_nonneg (hρ0 w) (abs_nonneg _)
  have hlint : ∫⁻ w, ENNReal.ofReal (rho w * abs (G w)) ∂μ =
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ :=
    lintegral_congr fun w => ENNReal.ofReal_mul (hρ0 w)
  have hne : ENNReal.ofReal K * eLpNorm G q μ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top
  rw [integral_eq_lintegral_of_nonneg_ae hnn (hρm.mul hAG).aestronglyMeasurable, hlint]
  calc (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ).toReal
      ≤ (ENNReal.ofReal K * eLpNorm G q μ).toReal := ENNReal.toReal_mono hne hocc
    _ = K * (eLpNorm G q μ).toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hK]

/-- Integrability of `ρ G` from a finite occupation integral of `ρ |G|`. -/
private theorem integrable_rho_mul_of_occupation_sr {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {rho G : Ω → ℝ} (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w)
    (hGm : Measurable G) {q : ENNReal} (hG : MemLp G q μ) {K : ℝ}
    (hocc : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ ≤
      ENNReal.ofReal K * eLpNorm G q μ) :
    Integrable (fun w => rho w * G w) μ := by
  have hfin : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ < ⊤ :=
    lt_of_le_of_lt hocc
      (lt_top_iff_ne_top.2 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top))
  have hAG : Measurable fun w => abs (G w) := by
    simpa only [Real.norm_eq_abs] using hGm.norm
  have hnn : ∀ w, 0 ≤ rho w * abs (G w) := fun w => mul_nonneg (hρ0 w) (abs_nonneg _)
  have hlint : ∫⁻ w, ENNReal.ofReal (rho w * abs (G w)) ∂μ =
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (G w)) ∂μ :=
    lintegral_congr fun w => ENNReal.ofReal_mul (hρ0 w)
  have hgI : Integrable (fun w => rho w * abs (G w)) μ := by
    refine ⟨(hρm.mul hAG).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all μ hnn), hlint]
    exact hfin
  refine hgI.mono' (hρm.mul hGm).aestronglyMeasurable (ae_of_all μ fun w => ?_)
  show ‖rho w * G w‖ ≤ rho w * abs (G w)
  exact le_of_eq (by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 w)])

/-- The absolute value of the integral of `ρ G` is at most the integral of `ρ |G|`, for `ρ ≥ 0`. -/
private theorem abs_integral_rho_le_sr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rho G : Ω → ℝ} (hρ0 : ∀ w, 0 ≤ rho w) :
    abs (∫ w, rho w * G w ∂μ) ≤ ∫ w, rho w * abs (G w) ∂μ := by
  calc abs (∫ w, rho w * G w ∂μ) = ‖∫ w, rho w * G w ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ w, ‖rho w * G w‖ ∂μ := norm_integral_le_integral_norm _
    _ = ∫ w, rho w * abs (G w) ∂μ :=
      integral_congr_ae (ae_of_all μ fun w =>
        show ‖rho w * G w‖ = rho w * abs (G w) by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 w)])

/-- The `L^q` norm of a flux `-E + c • P` is at most `‖E‖_q + |c| ‖P‖_q`. -/
private theorem eLpNorm_flux_le_sr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {d : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) {E P : Ω → Vec d} (c : ℝ)
    (hEn : Measurable fun w => euclideanNorm (E w))
    (hPn : Measurable fun w => euclideanNorm (P w)) :
    eLpNorm (fun w => euclideanNorm (-(E w) + c • P w)) p μ ≤
      eLpNorm (fun w => euclideanNorm (E w)) p μ +
        ENNReal.ofReal (|c|) * eLpNorm (fun w => euclideanNorm (P w)) p μ := by
  have hpt : ∀ w, ‖euclideanNorm (-(E w) + c • P w)‖ ≤
      euclideanNorm (E w) + (|c|) * euclideanNorm (P w) := fun w => by
    rw [Real.norm_of_nonneg (euclideanNorm_nonneg_sr _)]
    exact euclideanNorm_flux_le_sr (E w) (P w) c
  have hmul : eLpNorm (fun w => (|c|) * euclideanNorm (P w)) p μ =
      ENNReal.ofReal (|c|) * eLpNorm (fun w => euclideanNorm (P w)) p μ := by
    rw [← Real.enorm_eq_ofReal (abs_nonneg c)]
    exact eLpNorm_const_smul (|c|) (fun w => euclideanNorm (P w)) p μ
  calc eLpNorm (fun w => euclideanNorm (-(E w) + c • P w)) p μ
      ≤ eLpNorm (fun w => euclideanNorm (E w) + (|c|) * euclideanNorm (P w)) p μ :=
        eLpNorm_mono_real hpt
    _ ≤ eLpNorm (fun w => euclideanNorm (E w)) p μ +
          eLpNorm (fun w => (|c|) * euclideanNorm (P w)) p μ :=
        eLpNorm_add_le hEn.aestronglyMeasurable ((hPn.const_mul (|c|)).aestronglyMeasurable) hp
    _ = eLpNorm (fun w => euclideanNorm (E w)) p μ +
          ENNReal.ofReal (|c|) * eLpNorm (fun w => euclideanNorm (P w)) p μ := by
      rw [hmul]

/-- The reduced reference law is a probability measure. -/
private theorem isProbabilityMeasure_refLaw_sr {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
  Measure.isProbabilityMeasure_map (Probability.measurable_reduce (d := d)).aemeasurable

/-! ## The response bound in three steps -/

/-- The real algebra of the response bound: the Lemma 4.3 term, the `e` term and the `h` term
combine to the constant `(C_R + 2 C_O) C (sR + λ + λ² R + R⁻¹)`. -/
private theorem response_assembly_sr {CR CO C R lam s IR Ie Ih : ℝ} (hCR : 0 ≤ CR)
    (hCO : 0 ≤ CO) (hC : 0 ≤ C) (hR0 : 0 ≤ R) (hl0 : 0 < lam) (hs0 : 0 ≤ s)
    (hIR : abs IR ≤ CR * s * (C * R) + CR * lam * (C + lam * (C * R)))
    (hIe : abs Ie ≤ CO * 2 * (C * R⁻¹)) (hIh : abs Ih ≤ CO * 2 * C) :
    abs (IR + Ie - lam * Ih) ≤ (CR + 2 * CO) * C * (s * R + lam + lam ^ 2 * R + R⁻¹) := by
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.2 hR0
  have hlh : abs (lam * Ih) ≤ lam * (CO * 2 * C) := by
    rw [abs_mul, abs_of_pos hl0]
    exact mul_le_mul_of_nonneg_left hIh hl0.le
  have hpoly : CR * s * (C * R) + CR * lam * (C + lam * (C * R)) + CO * 2 * (C * R⁻¹) +
      lam * (CO * 2 * C) ≤ (CR + 2 * CO) * C * (s * R + lam + lam ^ 2 * R + R⁻¹) := by
    have e1 : (CR + 2 * CO) * C * (s * R + lam + lam ^ 2 * R + R⁻¹) -
        (CR * s * (C * R) + CR * lam * (C + lam * (C * R)) + CO * 2 * (C * R⁻¹) +
          lam * (CO * 2 * C)) =
        CR * C * R⁻¹ + 2 * (CO * C * (s * R)) + 2 * (CO * C * (lam ^ 2 * R)) := by
      ring
    have n1 : 0 ≤ CR * C * R⁻¹ := mul_nonneg (mul_nonneg hCR hC) hRinv
    have n2 : 0 ≤ CO * C * (s * R) := mul_nonneg (mul_nonneg hCO hC) (mul_nonneg hs0 hR0)
    have n3 : 0 ≤ CO * C * (lam ^ 2 * R) :=
      mul_nonneg (mul_nonneg hCO hC) (mul_nonneg (sq_nonneg lam) hR0)
    linarith only [e1, n1, n2, n3]
  have a1 := abs_le.1 hIR
  have a2 := abs_le.1 hIe
  have a3 := abs_le.1 hlh
  rw [abs_le]
  constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, hpoly]

/-- The occupation bounds for `e` and `h` at the exponent `2p`, in the form used by the response:
the products `ρ e` and `ρ h` are integrable, and their integrals are bounded by the `L^{2p}` norms
of `e` and `h` times the occupation constant. -/
private theorem response_occupation_sr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {rho e h : Ω → ℝ} {q : ENNReal} {CO CE CH s lam : ℝ}
    (hρm : Measurable rho) (hρ0 : ∀ w, 0 ≤ rho w) (hem : Measurable e) (hhm : Measurable h)
    (heN : MemLp e q μ) (hhN : MemLp h q μ) (hCO : 0 ≤ CO) (hs0 : 0 ≤ s)
    (hinv : 0 ≤ (lam ^ 2)⁻¹) (hsl : s * (lam ^ 2)⁻¹ ≤ 1)
    (hocc_e : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (e w)) ∂μ ≤
      ENNReal.ofReal (CO * (1 + s * (lam ^ 2)⁻¹)) * eLpNorm e q μ)
    (hocc_h : ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal (abs (h w)) ∂μ ≤
      ENNReal.ofReal (CO * (1 + s * (lam ^ 2)⁻¹)) * eLpNorm h q μ)
    (hNe : (eLpNorm e q μ).toReal ≤ CE) (hNh : (eLpNorm h q μ).toReal ≤ CH) :
    Integrable (fun w => rho w * e w) μ ∧ Integrable (fun w => rho w * h w) μ ∧
      abs (∫ w, rho w * e w ∂μ) ≤ CO * 2 * CE ∧
      abs (∫ w, rho w * h w ∂μ) ≤ CO * 2 * CH := by
  have hX0 : 0 ≤ s * (lam ^ 2)⁻¹ := mul_nonneg hs0 hinv
  have hK0 : 0 ≤ CO * (1 + s * (lam ^ 2)⁻¹) := mul_nonneg hCO (by linarith only [hX0])
  have hK2 : CO * (1 + s * (lam ^ 2)⁻¹) ≤ CO * 2 :=
    mul_le_mul_of_nonneg_left (by linarith only [hsl]) hCO
  have hIe_int : Integrable (fun w => rho w * e w) μ :=
    integrable_rho_mul_of_occupation_sr hρm hρ0 hem heN hocc_e
  have hIh_int : Integrable (fun w => rho w * h w) μ :=
    integrable_rho_mul_of_occupation_sr hρm hρ0 hhm hhN hocc_h
  refine ⟨hIe_int, hIh_int, ?_, ?_⟩
  · have h1 : abs (∫ w, rho w * e w ∂μ) ≤ ∫ w, rho w * abs (e w) ∂μ :=
      abs_integral_rho_le_sr hρ0
    have h2 : ∫ w, rho w * abs (e w) ∂μ ≤
        CO * (1 + s * (lam ^ 2)⁻¹) * (eLpNorm e q μ).toReal :=
      integral_rho_abs_le_sr hρm hρ0 hem hK0 heN hocc_e
    have h3 : CO * (1 + s * (lam ^ 2)⁻¹) * (eLpNorm e q μ).toReal ≤ CO * 2 * CE :=
      mul_le_mul hK2 hNe ENNReal.toReal_nonneg (by linarith only [hCO])
    linarith only [h1, h2, h3]
  · have h1 : abs (∫ w, rho w * h w ∂μ) ≤ ∫ w, rho w * abs (h w) ∂μ :=
      abs_integral_rho_le_sr hρ0
    have h2 : ∫ w, rho w * abs (h w) ∂μ ≤
        CO * (1 + s * (lam ^ 2)⁻¹) * (eLpNorm h q μ).toReal :=
      integral_rho_abs_le_sr hρm hρ0 hhm hK0 hhN hocc_h
    have h3 : CO * (1 + s * (lam ^ 2)⁻¹) * (eLpNorm h q μ).toReal ≤ CO * 2 * CH :=
      mul_le_mul hK2 hNh ENNReal.toReal_nonneg (by linarith only [hCO])
    linarith only [h1, h2, h3]

/-- Lemma 4.3 applied to `ψ`, with right side `f - e + λ h` and flux `-E + λ P`. It gives the
integrability of `ρ (f - e + λ h)` and the bound on its integral by the `L^{2p}` norms of `ψ`, `P`,
`E`, and `h`. -/
private theorem response_resolvent_sr {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q))
    (M : ℝ → ℝ) (C₀ l p C R CR : ℝ) (hR : 2 ≤ R) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hCR : 0 ≤ CR) (f : FieldPair d → ℝ) (hf : Carriers.IsScalarAveragingField Q M R f)
    (ψ h e : FieldPair d → ℝ) (Dψ E P : FieldPair d → Vec d)
    (hψm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] ψ)
    (hhm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] h)
    (hem : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] e)
    (hEm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] E)
    (hPm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] P)
    (hEq : SatisfiesReducedGeneratorEquation (Carriers.reducedReferenceLaw Q) hQ 0 ψ Dψ
      (fun ω => f ω - e ω) (fun ω => -(E ω)) (⟨0, by omega⟩ : Fin d))
    (hDiv : HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ P
      (fun ω => dot ((ω.1 (0 : Vec d)).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (Dψ ω) - h ω))
    (hψP : eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) +
        eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * R))
    (hDψb : eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * Real.log (2 + R)))
    (hEh : eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) + eLpNorm h (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal C)
    (heb : eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R⁻¹))
    (hDψL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] Dψ)
    (hfeL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}]
        (fun ω => f ω - e ω))
    (hGrad : ∀ (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (P' : QuenchedPathLaws d)
        (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P' ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P') →
        ∀ (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ),
        Carriers.IsReducedLaplaceDensity Q.measure P' op s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho)
    (hRes : ResolventAtScale d hd Λ₀ r₀ l p CR)
    (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (hCl : C₀ * R ≤ l / (2 * lam))
    (P' : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P' ω))
    (hGIMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P'))
    (s : {r : ℝ // 0 < r}) (hs : s.1 ≤ lam ^ 2) (rho : FieldPair d → ℝ)
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P' op s rho) :
    Integrable (fun w => rho w * (f w - e w + lam * h w)) (Carriers.reducedReferenceLaw Q) ∧
      abs (∫ w, rho w * (f w - e w + lam * h w) ∂(Carriers.reducedReferenceLaw Q)) ≤
        CR * s.1 * (C * R) + CR * lam * (C + lam * (C * R)) := by
  obtain ⟨hfm, hfb⟩ := hf
  have hμ : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    isProbabilityMeasure_refLaw_sr Q
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hCR0 : 0 ≤ C * R := mul_nonneg hC hR0
  have hpow : (1 : ENNReal) ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.one_le_ofReal.2 (by linarith only [hp])
  have hs0 : 0 ≤ s.1 := s.2.le
  -- Localization of the fields on the ball of Lemma 4.3.
  have hB1 : {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R} ⊆
      {y : Vec d | euclideanNorm y < l / (2 * lam)} := by
    intro y hy
    simp only [Set.mem_setOf_eq, sub_zero] at hy ⊢
    exact lt_of_lt_of_le hy hCl
  have hψ1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] ψ :=
    hψm.mono (Probability.localSigma_mono hB1) le_rfl
  have hDψ1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] Dψ :=
    hDψL.mono (Probability.localSigma_mono hB1) le_rfl
  have hh1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] h :=
    hhm.mono (Probability.localSigma_mono hB1) le_rfl
  have hfe1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}]
      (fun ω => f ω - e ω) :=
    hfeL.mono (Probability.localSigma_mono hB1) le_rfl
  have hE1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] E :=
    hEm.mono (Probability.localSigma_mono hB1) le_rfl
  have hP1 : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}] P :=
    hPm.mono (Probability.localSigma_mono hB1) le_rfl
  have hLoc : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}]
      (fun ω => f ω - e ω + lam * h ω) :=
    measurable_add_localSigma_sr hfe1 (measurable_const_mul_localSigma_sr lam hh1)
  have hGL : Measurable[localSigma {y : Vec d | euclideanNorm y < l / (2 * lam)}]
      (fun ω => -(E ω) + lam • P ω) :=
    measurable_flux_localSigma_sr lam hE1 hP1
  -- The `L^{2p}` bounds and memberships.
  have hf2 : eLpNorm f (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) < ⊤ := by
    have h0 := hfb (2 * p) (by linarith only [hp]) 0 le_rfl
    have hid0 : heatSmoothed (0 : ℝ) f = f := by
      funext ω
      simp [heatSmoothed]
    rw [hid0] at h0
    exact lt_of_le_of_lt h0 ENNReal.ofReal_lt_top
  have hψfin : eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (le_add_of_nonneg_right (zero_le _)) hψP)
  have hPfin : eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (le_add_of_nonneg_left (zero_le _)) hψP)
  have hEfin : eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (le_add_of_nonneg_right (zero_le _)) hEh)
  have hhfin : eLpNorm h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (le_add_of_nonneg_left (zero_le _)) hEh)
  have hefin : eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top heb
  have hDψfin : eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hDψb
  have hfMem : MemLp f (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hfm).aestronglyMeasurable, hf2⟩
  have hψN : MemLp ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hψm).aestronglyMeasurable, lt_top_iff_ne_top.2 hψfin⟩
  have hDψN : MemLp (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_norm_of_localSigma hDψL).aestronglyMeasurable, lt_top_iff_ne_top.2 hDψfin⟩
  have hhN : MemLp h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hhm).aestronglyMeasurable, lt_top_iff_ne_top.2 hhfin⟩
  have heN : MemLp e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hem).aestronglyMeasurable, lt_top_iff_ne_top.2 hefin⟩
  have hEn : Measurable fun w => euclideanNorm (E w) := measurable_norm_of_localSigma hEm
  have hPn : Measurable fun w => euclideanNorm (P w) := measurable_norm_of_localSigma hPm
  have hflux : eLpNorm (fun w => euclideanNorm (-(E w) + lam • P w))
      (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≤
        eLpNorm (fun w => euclideanNorm (E w)) (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) +
        ENNReal.ofReal (|lam|) * eLpNorm (fun w => euclideanNorm (P w))
          (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    eLpNorm_flux_le_sr hpow lam hEn hPn
  have hGfin : eLpNorm (fun w => euclideanNorm (-(E w) + lam • P w))
      (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.add_ne_top.2 ⟨hEfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPfin⟩) hflux
  have hGN : MemLp (fun w => euclideanNorm (-(E w) + lam • P w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_norm_of_localSigma hGL).aestronglyMeasurable, lt_top_iff_ne_top.2 hGfin⟩
  have hRHSN : MemLp (fun w => f w - e w + lam * h w) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q) :=
    (hfMem.sub heN).add (hhN.const_mul lam)
  -- The generator equation of `ψ` with right side `f - e + λ h` and flux `-E + λ P`.
  have hhI : Integrable h (Carriers.reducedReferenceLaw Q) := hhN.integrable hpow
  have hcomb : SatisfiesReducedGeneratorEquation (Carriers.reducedReferenceLaw Q) hQ lam ψ Dψ
      (fun ω => f ω - e ω + lam * h ω) (fun ω => -(E ω) + lam • P ω)
      (⟨0, by omega⟩ : Fin d) :=
    reducedGeneratorEquation_combine lam hEq hDiv hhI
  -- Lemma 4.3 for `ψ`.
  obtain ⟨Drho, hDrho⟩ := hGrad lam hl0 hl1 P' op hGIMP s rho hrho
  obtain ⟨⟨-, hIRho, -, -⟩, hbd⟩ :=
    hRes Q hQ lam hl0 hl1 Q.measure P' op ⟨rfl, hGIMP⟩ s hs rho hrho Drho hDrho ψ Dψ
      (fun ω => f ω - e ω + lam * h ω) (fun ω => -(E ω) + lam • P ω) hψN hDψN hRHSN hGN
      hψ1 hDψ1 hLoc hGL hcomb
  have hIRho' : Integrable (fun w => rho w * (f w - e w + lam * h w))
      (Carriers.reducedReferenceLaw Q) := hIRho
  have hbd' : ENNReal.ofReal (abs (∫ w, rho w * (f w - e w + lam * h w)
        ∂(Carriers.reducedReferenceLaw Q))) ≤
      ENNReal.ofReal (CR * s.1) * eLpNorm ψ (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) +
        ENNReal.ofReal (CR * lam) *
          eLpNorm (fun w => euclideanNorm (-(E w) + lam • P w)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q) := hbd
  have hIR_abs : abs (∫ w, rho w * (f w - e w + lam * h w)
        ∂(Carriers.reducedReferenceLaw Q)) ≤
      CR * s.1 * (eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q)).toReal +
        CR * lam * (eLpNorm (fun w => euclideanNorm (-(E w) + lam • P w))
          (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q)).toReal :=
    abs_le_of_ofReal_add_le_sr (mul_nonneg hCR hs0) (mul_nonneg hCR hl0.le) hψfin hGfin hbd'
  -- Real bounds on the norms from the decomposition.
  have hNψ : (eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q)).toReal ≤
      C * R :=
    ENNReal.toReal_le_of_le_ofReal hCR0 (le_trans (le_add_of_nonneg_right (zero_le _)) hψP)
  have hNP : (eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q)).toReal ≤ C * R :=
    ENNReal.toReal_le_of_le_ofReal hCR0 (le_trans (le_add_of_nonneg_left (zero_le _)) hψP)
  have hNE : (eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q)).toReal ≤ C :=
    ENNReal.toReal_le_of_le_ofReal hC (le_trans (le_add_of_nonneg_right (zero_le _)) hEh)
  have hNG : (eLpNorm (fun w => euclideanNorm (-(E w) + lam • P w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q)).toReal ≤ C + lam * (C * R) := by
    have h1 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.2 ⟨hEfin, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPfin⟩) hflux
    rw [ENNReal.toReal_add hEfin (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPfin),
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg lam), abs_of_pos hl0] at h1
    have h2 : lam * (eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q)).toReal ≤ lam * (C * R) :=
      mul_le_mul_of_nonneg_left hNP hl0.le
    linarith only [h1, hNE, h2]
  refine ⟨hIRho', ?_⟩
  refine hIR_abs.trans ?_
  have h1 := mul_le_mul_of_nonneg_left hNψ (mul_nonneg hCR hs0)
  have h2 := mul_le_mul_of_nonneg_left hNG (mul_nonneg hCR hl0.le)
  linarith only [h1, h2]

/-- Proposition 6.1, response bound (`scalar.decomposition`, `paper/main.tex:978-997`), derived
from the decomposition data of its first conjunct. For a scale `λ ∈ (0, 1]` with `C₀ R ≤ l/(2λ)`,
every reduced Laplace density `ρ_s` with `s ≤ λ²` satisfies
`|E[ρ_s f]| ≤ (C_R + 2 C_O) C (sR + λ + λ² R + R⁻¹)`, where `C_R` and `C_O` are the constants of
Lemma 4.3 and of the occupation bound, and `C` is the decomposition constant. The response uses
the decomposition with right side `f - e` for `ψ`, the flux `-E`, the divergence identity of `P`,
and the `L^{2p}` bounds. -/
theorem scalarResponse_of_decomposition {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀) (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (M : ℝ → ℝ)
    (C₀ l p C R CR CO : ℝ) (hC₀ : 0 < C₀) (hR : 2 ≤ R) (hp : 1 ≤ p) (hC : 0 ≤ C)
    (hCR : 0 ≤ CR) (hCO : 0 ≤ CO)
    (f : FieldPair d → ℝ) (hf : Carriers.IsScalarAveragingField Q M R f)
    (ψ h e : FieldPair d → ℝ) (Dψ E P : FieldPair d → Vec d)
    (hψm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] ψ)
    (hhm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] h)
    (hem : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] e)
    (hEm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] E)
    (hPm : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] P)
    (hEq : SatisfiesReducedGeneratorEquation (Carriers.reducedReferenceLaw Q) hQ 0 ψ Dψ
      (fun ω => f ω - e ω) (fun ω => -(E ω)) (⟨0, by omega⟩ : Fin d))
    (hDiv : HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ P
      (fun ω => dot ((ω.1 (0 : Vec d)).mulVec (unitVector (⟨0, by omega⟩ : Fin d))) (Dψ ω) - h ω))
    (hψP : eLpNorm ψ (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) +
        eLpNorm (fun ω => euclideanNorm (P ω)) (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * R))
    (hDψb : eLpNorm (fun ω => euclideanNorm (Dψ ω)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal (C * Real.log (2 + R)))
    (hEh : eLpNorm (fun ω => euclideanNorm (E ω)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) + eLpNorm h (ENNReal.ofReal (2 * p))
          (Carriers.reducedReferenceLaw Q) ≤ ENNReal.ofReal C)
    (heb : eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal (C * R⁻¹))
    (hDψL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}] Dψ)
    (hfeL : Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R}]
        (fun ω => f ω - e ω))
    (hGrad : ∀ (lam : ℝ) (hl0 : 0 < lam) (hl1 : lam ≤ 1) (P' : QuenchedPathLaws d)
        (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P' ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P') →
        ∀ (s : {r : ℝ // 0 < r}) (rho : FieldPair d → ℝ),
        Carriers.IsReducedLaplaceDensity Q.measure P' op s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho)
    (hRes : ResolventAtScale d hd Λ₀ r₀ l p CR)
    (hOcc : OccupationAtScale d hd Λ₀ r₀ l (2 * p) CO) :
    ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1, C₀ * R ≤ l / (2 * lam) →
    ∀ Q' : Measure (FieldPair d), IsProbabilityMeasure Q' →
    ∀ (P' : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q', IsProbabilityMeasure (originLaw P' ω)),
      (Q' = Q.measure ∧ IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1
        (originLaw P')) →
    ∀ s : {r : ℝ // 0 < r}, s.1 ≤ lam ^ 2 →
    ∀ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q' P' op s rho →
      Integrable (fun w => rho w * f w) (Carriers.reducedReferenceLaw Q) ∧
        abs (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) ≤
          (CR + 2 * CO) * C * (s.1 * R + lam + lam ^ 2 * R + R⁻¹) := by
  intro lam hl0 hl1 hCl Q' _ P' op hyp s hs rho hrho
  obtain ⟨rfl, hGIMP⟩ := hyp
  obtain ⟨hIRho', hIR⟩ :=
    response_resolvent_sr hd Q hQ M C₀ l p C R CR hR hp hC hCR f hf ψ h e Dψ E P hψm hhm
      hem hEm hPm hEq hDiv hψP hDψb hEh heb hDψL hfeL hGrad hRes lam hl0 hl1 hCl P' op hGIMP s
      hs rho hrho
  have hR0 : 0 ≤ R := le_trans (by norm_num) hR
  have hs0 : 0 ≤ s.1 := s.2.le
  have hinv : 0 ≤ (lam ^ 2)⁻¹ := inv_nonneg.2 (sq_nonneg lam)
  have hsl : s.1 * (lam ^ 2)⁻¹ ≤ 1 := by
    have h1 : s.1 * (lam ^ 2)⁻¹ ≤ lam ^ 2 * (lam ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hs hinv
    rwa [mul_inv_cancel₀ (pow_ne_zero 2 hl0.ne')] at h1
  -- The scale `l` is positive, because `C₀ R > 0` and `C₀ R ≤ l/(2λ)`.
  have hl : 0 < l := by
    have hpos : 0 < l / (2 * lam) :=
      lt_of_lt_of_le (mul_pos hC₀ (by linarith only [hR])) hCl
    exact (div_pos_iff_of_pos_right (by linarith only [hl0])).1 hpos
  have hdivrw : l / (2 * lam) = l / lam / 2 := by ring
  have hq0 : 0 ≤ l / lam := div_nonneg hl.le hl0.le
  have hCl' : C₀ * R ≤ l / lam := by
    rw [hdivrw] at hCl
    linarith only [hCl, hq0]
  have hB2 : {y : Vec d | euclideanNorm (y - (0 : Vec d)) < C₀ * R} ⊆
      {y : Vec d | euclideanNorm y < l / lam} := by
    intro y hy
    simp only [Set.mem_setOf_eq, sub_zero] at hy ⊢
    exact lt_of_lt_of_le hy hCl'
  have he2 : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] e :=
    hem.mono (Probability.localSigma_mono hB2) le_rfl
  have hh2 : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] h :=
    hhm.mono (Probability.localSigma_mono hB2) le_rfl
  have hCRinv : 0 ≤ C * R⁻¹ := mul_nonneg hC (inv_nonneg.2 hR0)
  have hefin : eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top heb
  have hhfin : eLpNorm h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (le_trans (le_add_of_nonneg_left (zero_le _)) hEh)
  have heN : MemLp e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hem).aestronglyMeasurable, lt_top_iff_ne_top.2 hefin⟩
  have hhN : MemLp h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) :=
    ⟨(measurable_global_of_localSigma hhm).aestronglyMeasurable, lt_top_iff_ne_top.2 hhfin⟩
  have hNe : (eLpNorm e (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q)).toReal ≤
      C * R⁻¹ :=
    ENNReal.toReal_le_of_le_ofReal hCRinv heb
  have hNh : (eLpNorm h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q)).toReal ≤ C :=
    ENNReal.toReal_le_of_le_ofReal hC
      (le_trans (le_add_of_nonneg_left (zero_le _)) hEh)
  -- The occupation bound for `e` and `h` at the exponent `2p`.
  have hocc_e := (hOcc hΛ hr Q lam hl0 hl1 Q.measure P' op ⟨rfl, hGIMP⟩ e he2 heN 1 one_pos
    s).2 rho hrho
  have hocc_h := (hOcc hΛ hr Q lam hl0 hl1 Q.measure P' op ⟨rfl, hGIMP⟩ h hh2 hhN 1 one_pos
    s).2 rho hrho
  obtain ⟨hIe_int, hIh_int, hIe_bd, hIh_bd⟩ :=
    response_occupation_sr hrho.1 hrho.2.1 (measurable_global_of_localSigma hem)
      (measurable_global_of_localSigma hhm) heN hhN hCO hs0 hinv hsl hocc_e hocc_h hNe hNh
  -- The integral splits along `ρ f = ρ (f - e + λ h) + ρ e - λ ρ h`.
  have hA : Integrable (fun w => rho w * (f w - e w + lam * h w) + rho w * e w)
      (Carriers.reducedReferenceLaw Q) := hIRho'.add hIe_int
  have hB : Integrable (fun w => lam * (rho w * h w)) (Carriers.reducedReferenceLaw Q) :=
    hIh_int.const_mul lam
  have hC' : Integrable
      (fun w => rho w * (f w - e w + lam * h w) + rho w * e w - lam * (rho w * h w))
      (Carriers.reducedReferenceLaw Q) := hA.sub hB
  have hIf : Integrable (fun w => rho w * f w) (Carriers.reducedReferenceLaw Q) :=
    hC'.congr (ae_of_all _ fun w =>
      show rho w * (f w - e w + lam * h w) + rho w * e w - lam * (rho w * h w) =
        rho w * f w by ring)
  have hint : (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) =
      (∫ w, rho w * (f w - e w + lam * h w) ∂(Carriers.reducedReferenceLaw Q)) +
        (∫ w, rho w * e w ∂(Carriers.reducedReferenceLaw Q)) -
        lam * ∫ w, rho w * h w ∂(Carriers.reducedReferenceLaw Q) := by
    have hD : (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) =
        ∫ w, rho w * (f w - e w + lam * h w) + rho w * e w - lam * (rho w * h w)
          ∂(Carriers.reducedReferenceLaw Q) :=
      integral_congr_ae (ae_of_all _ fun w =>
        show rho w * f w = rho w * (f w - e w + lam * h w) + rho w * e w - lam * (rho w * h w) by
          ring)
    rw [hD, integral_sub hA hB, integral_add hIRho' hIe_int, integral_const_mul]
  refine ⟨hIf, ?_⟩
  rw [hint]
  exact response_assembly_sr hCR hCO hC hR0 hl0 hs0 hIR hIe_bd hIh_bd

end EinsteinRelation.Correctors

end
