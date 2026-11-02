import EinsteinRelation.Sharpness.NoiseKernel
import EinsteinRelation.Sharpness.NoiseIndependence
import EinsteinRelation.Sharpness.NoiseOrthogonality
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

/-! # Joint independence of noise evaluations on finite orthogonal test blocks

Source: `paper/main.tex:1212–1216`, the internal finite-range construction
`h ≔ ζ * tanh(K * W)` in the proof of `sharp.example` (Proposition 7.1). The generic
Gaussian characteristic law `hwhite` is an explicit hypothesis here, sourced from AKM
Definition 5.1 / Proposition 5.14. It is not a premise of the final sharpness statement.

For finite families `F : Fin n → NoiseTest d` and `G : Fin m → NoiseTest d` whose cross
integrals `∫ F i * G j` all vanish, the block `(W (F i))_i` and the block `(W (G j))_j` are
jointly independent. The proof factorizes the joint dual characteristic function directly:
a continuous linear functional on the product of the two blocks restricts to finite
coordinate combinations, samplewise linearity turns each combination into `W` of a single
compact test, and zero cross integrals split the Gaussian variance. Pairwise independence of
single coordinates is not used. Empty families (`n = 0` or `m = 0`) need no separate case.

This is a finite-block step only. It does not give σ-algebra independence of all residual
observations: that step, which uses `ProbabilityTheory.IndepFun.process_indepFun_process`, is a
separate internal obligation and is not claimed here.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Evaluation at a fixed point, as an additive homomorphism on compact smooth tests. -/
private noncomputable def testEvalHom {d : ℕ} (y : Vec d) : NoiseTest d →+ ℝ where
  toFun f := f y
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The pointwise value of a finite real linear combination of compact smooth tests. -/
private theorem block_sum_apply {d n : ℕ} (c : Fin n → ℝ) (F : Fin n → NoiseTest d)
    (y : Vec d) : (∑ i, c i • F i) y = ∑ i, c i * F i y := by
  have h := map_sum (testEvalHom y) (fun i => c i • F i) Finset.univ
  exact h.trans (Finset.sum_congr rfl fun i _ => rfl)

/-- Products of two compact smooth tests are integrable on coordinate space. -/
private theorem block_mul_integrable {d : ℕ} (f g : NoiseTest d) :
    Integrable (fun y : Vec d => f y * g y) := by
  have hfg : HasCompactSupport ((f : Vec d → ℝ) * (g : Vec d → ℝ)) :=
    f.hasCompactSupport.mul_right
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (f.contDiff.continuous).mul (g.contDiff.continuous)
  · exact hfg

/-- Zero integral covariance removes the cross term of `∫ (f + g)²`. -/
private theorem block_sq_integral_add_of_orth {d : ℕ} (f g : NoiseTest d)
    (horth : (∫ y : Vec d, f y * g y) = 0) :
    (∫ y : Vec d, ((f + g) y) ^ 2) = (∫ y : Vec d, (f y) ^ 2) + (∫ y : Vec d, (g y) ^ 2) := by
  have hpt : ∀ y : Vec d, ((f + g) y) ^ 2 =
      (f y) ^ 2 + (2 : ℝ) * (f y * g y) + (g y) ^ 2 := by
    intro y
    change (f y + g y) ^ 2 = (f y) ^ 2 + (2 : ℝ) * (f y * g y) + (g y) ^ 2
    ring
  have h1 : Integrable (fun y : Vec d => (f y) ^ 2) := noiseTest_sq_integrable f
  have h2 : Integrable (fun y : Vec d => (2 : ℝ) * (f y * g y)) :=
    (block_mul_integrable f g).const_mul 2
  have h3 : Integrable (fun y : Vec d => (g y) ^ 2) := noiseTest_sq_integrable g
  have h12 : Integrable (fun y : Vec d => (f y) ^ 2 + (2 : ℝ) * (f y * g y)) :=
    h1.add h2
  simp_rw [hpt]
  rw [integral_add h12 h3, integral_add h1 h2, integral_const_mul, horth]
  ring

/-- The integral of a product of two finite linear combinations of block tests vanishes when
every cross integral of the blocks vanishes. -/
private theorem block_sum_integral_mul_zero {d n m : ℕ} (F : Fin n → NoiseTest d)
    (G : Fin m → NoiseTest d) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (horth : ∀ i j, (∫ y : Vec d, F i y * G j y) = 0) :
    (∫ y : Vec d, ((∑ i, a i • F i) y) * ((∑ j, b j • G j) y)) = 0 := by
  have hpt : ∀ y : Vec d, ((∑ i, a i • F i) y) * ((∑ j, b j • G j) y) =
      ∑ i, ∑ j, (a i * b j) * (F i y * G j y) := by
    intro y
    rw [block_sum_apply, block_sum_apply, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hint : ∀ i j, Integrable (fun y : Vec d => (a i * b j) * (F i y * G j y)) :=
    fun i j => (block_mul_integrable (F i) (G j)).const_mul (a i * b j)
  have hinner : ∀ i, Integrable (fun y : Vec d => ∑ j, (a i * b j) * (F i y * G j y)) :=
    fun i => integrable_finset_sum Finset.univ (fun j _ => hint i j)
  simp_rw [hpt]
  rw [integral_finset_sum Finset.univ (fun i _ => hinner i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_finset_sum Finset.univ (fun j _ => hint i j)]
  apply Finset.sum_eq_zero
  intro j _
  rw [integral_const_mul, horth i j, mul_zero]

/-- A finite linear combination of block tests is evaluated samplewise by `W`. -/
private theorem block_eval_sum {d n : ℕ} (W : NoiseSample d) (c : Fin n → ℝ)
    (F : Fin n → NoiseTest d) :
    W (∑ i, c i • F i) = ∑ i, W (F i) * c i := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  exact mul_comm _ _

/-- The Gaussian characteristic law at a test `f`, read through a real random variable `g`
that equals `W ω f` pointwise. -/
private theorem block_charFun_eq_gauss {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} (W : Ω → NoiseSample d)
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (f : NoiseTest d) (g : Ω → ℝ) (hg : ∀ ω, g ω = W ω f) :
    (∫ ω, Complex.exp (((g ω : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp (((-(1/2 : ℝ))*(1 : ℝ)^2*(∫ y : Vec d, (f y)^2)) : ℂ) := by
  calc (∫ ω, Complex.exp (((g ω : ℝ) : ℂ) * Complex.I) ∂P)
      = ∫ ω, Complex.exp (Complex.I * ((1 : ℝ) : ℂ) * (W ω f : ℂ)) ∂P := by
        congr 1
        funext ω
        congr 1
        rw [hg ω]
        push_cast
        ring
    _ = _ := hwhite f 1

/-- The dual characteristic function of the image of `P` under `X` is the expectation of
`exp (L (X ω) * I)` over `P`. -/
private theorem block_charFunDual_map_eq {Ω : Type*} [MeasurableSpace Ω] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] (P : Measure Ω) {X : Ω → E} (hX : Measurable X)
    (L : StrongDual ℝ E) :
    charFunDual (P.map X) L = ∫ ω, Complex.exp (((L (X ω) : ℝ) : ℂ) * Complex.I) ∂P := by
  have hc : Continuous fun v : E => Complex.exp (((L v : ℝ) : ℂ) * Complex.I) := by
    fun_prop
  rw [charFunDual_apply, integral_map hX.aemeasurable hc.aestronglyMeasurable]

/-- Finite-block independence of noise evaluations on orthogonal compact test families.

Conditional on the generic Gaussian characteristic law `hwhite`, the block `(W (F i))_i` and
the block `(W (G j))_j` are independent whenever every cross integral `∫ F i * G j` vanishes.
The joint factorization is proved here; pairwise independence of single coordinates is not
assumed. This is a finite-range leaf from `paper/main.tex:1212–1216`. -/
theorem indepFun_noise_finite_blocks {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (n m : ℕ) (F : Fin n → NoiseTest d) (G : Fin m → NoiseTest d)
    (horth : ∀ i j, (∫ y : Vec d, F i y * G j y) = 0) :
    ProbabilityTheory.IndepFun (fun ω => fun i : Fin n => W ω (F i))
      (fun ω => fun j : Fin m => W ω (G j)) P := by
  have hX : Measurable (fun ω => fun i : Fin n => W ω (F i)) :=
    Measurable.of_eval fun i => hmeas (F i)
  have hY : Measurable (fun ω => fun j : Fin m => W ω (G j)) :=
    Measurable.of_eval fun j => hmeas (G j)
  have hXY : Measurable (fun ω => ((fun i : Fin n => W ω (F i)),
      (fun j : Fin m => W ω (G j)))) := hX.prodMk hY
  refine (ProbabilityTheory.indepFun_iff_charFunDual_prod hX.aemeasurable
    hY.aemeasurable).2 ?_
  intro L
  show charFunDual (P.map fun ω => ((fun i : Fin n => W ω (F i)),
      (fun j : Fin m => W ω (G j)))) L =
    charFunDual (P.map fun ω => fun i : Fin n => W ω (F i))
        (L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ))) *
      charFunDual (P.map fun ω => fun j : Fin m => W ω (G j))
        (L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin m → ℝ)))
  -- The restrictions of `L` to the two blocks, named so the coordinate expansions stay short.
  obtain ⟨L₁, hL₁⟩ : ∃ L₁ : StrongDual ℝ (Fin n → ℝ),
      L₁ = L.comp (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin m → ℝ)) := ⟨_, rfl⟩
  obtain ⟨L₂, hL₂⟩ : ∃ L₂ : StrongDual ℝ (Fin m → ℝ),
      L₂ = L.comp (ContinuousLinearMap.inr ℝ (Fin n → ℝ) (Fin m → ℝ)) := ⟨_, rfl⟩
  have hL₁x : ∀ x : Fin n → ℝ, L₁ x = L (x, 0) := fun x => by
    rw [hL₁]
    rfl
  have hL₂y : ∀ y : Fin m → ℝ, L₂ y = L (0, y) := fun y => by
    rw [hL₂]
    rfl
  rw [← hL₁, ← hL₂]
  -- Each block restriction is a finite coordinate linear combination.
  obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, ∀ x : Fin n → ℝ, L₁ x = ∑ i, x i * a i := by
    refine ⟨fun i => L₁ (fun j : Fin n => if i = j then (1 : ℝ) else 0), fun x => ?_⟩
    exact (LinearMap.pi_apply_eq_sum_univ L₁.toLinearMap x).trans
      (Finset.sum_congr rfl fun i _ => rfl)
  obtain ⟨b, hb⟩ : ∃ b : Fin m → ℝ, ∀ y : Fin m → ℝ, L₂ y = ∑ j, y j * b j := by
    refine ⟨fun j => L₂ (fun k : Fin m => if j = k then (1 : ℝ) else 0), fun y => ?_⟩
    exact (LinearMap.pi_apply_eq_sum_univ L₂.toLinearMap y).trans
      (Finset.sum_congr rfl fun j _ => rfl)
  have hsplit : ∀ (x : Fin n → ℝ) (y : Fin m → ℝ), L (x, y) = L₁ x + L₂ y := by
    intro x y
    rw [hL₁x, hL₂y, ← map_add]
    congr 1
    ext <;> simp
  -- The two block tests, their orthogonality, and the Gaussian variance split.
  obtain ⟨fA, hfA⟩ : ∃ f : NoiseTest d, f = ∑ i, a i • F i := ⟨_, rfl⟩
  obtain ⟨fB, hfB⟩ : ∃ f : NoiseTest d, f = ∑ j, b j • G j := ⟨_, rfl⟩
  have hAB : (∫ y : Vec d, fA y * fB y) = 0 := by
    rw [hfA, hfB]
    exact block_sum_integral_mul_zero F G a b horth
  have hsq : (∫ y : Vec d, ((fA + fB) y) ^ 2) =
      (∫ y : Vec d, (fA y) ^ 2) + (∫ y : Vec d, (fB y) ^ 2) :=
    block_sq_integral_add_of_orth fA fB hAB
  -- Samplewise identities: each block functional is `W` of its block test.
  have hEvA : ∀ ω, L₁ (fun i : Fin n => W ω (F i)) = W ω fA := by
    intro ω
    rw [ha, hfA, block_eval_sum (W ω) a F]
  have hEvB : ∀ ω, L₂ (fun j : Fin m => W ω (G j)) = W ω fB := by
    intro ω
    rw [hb, hfB, block_eval_sum (W ω) b G]
  have hJoint : ∀ ω, L ((fun i : Fin n => W ω (F i)), (fun j : Fin m => W ω (G j)))
      = W ω (fA + fB) := by
    intro ω
    rw [hsplit, ha, hb, map_add, hfA, hfB, block_eval_sum (W ω) a F,
      block_eval_sum (W ω) b G]
  -- The three Fourier factors, each given by the Gaussian law at a single test.
  have hcharJ : (∫ ω, Complex.exp (((L ((fun i : Fin n => W ω (F i)),
      (fun j : Fin m => W ω (G j))) : ℝ) : ℂ) * Complex.I) ∂P) =
      Complex.exp (((-(1/2 : ℝ))*(1 : ℝ)^2*(∫ y : Vec d, ((fA + fB) y) ^ 2)) : ℂ) :=
    block_charFun_eq_gauss P W hwhite (fA + fB)
      (fun ω => L ((fun i : Fin n => W ω (F i)), (fun j : Fin m => W ω (G j)))) hJoint
  have hcharA : (∫ ω, Complex.exp (((L₁ (fun i : Fin n => W ω (F i)) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      Complex.exp (((-(1/2 : ℝ))*(1 : ℝ)^2*(∫ y : Vec d, (fA y) ^ 2)) : ℂ) :=
    block_charFun_eq_gauss P W hwhite fA (fun ω => L₁ (fun i : Fin n => W ω (F i))) hEvA
  have hcharB : (∫ ω, Complex.exp (((L₂ (fun j : Fin m => W ω (G j)) : ℝ) : ℂ) *
      Complex.I) ∂P) =
      Complex.exp (((-(1/2 : ℝ))*(1 : ℝ)^2*(∫ y : Vec d, (fB y) ^ 2)) : ℂ) :=
    block_charFun_eq_gauss P W hwhite fB (fun ω => L₂ (fun j : Fin m => W ω (G j))) hEvB
  -- Factorize the joint Fourier integral into the two marginal Fourier integrals.
  rw [block_charFunDual_map_eq P hXY L, block_charFunDual_map_eq P hX L₁,
    block_charFunDual_map_eq P hY L₂]
  rw [hcharJ, hcharA, hcharB, ← Complex.exp_add, hsq]
  congr 1
  push_cast
  ring

end EinsteinRelation.Sharpness
