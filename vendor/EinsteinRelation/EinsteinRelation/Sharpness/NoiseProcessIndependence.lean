import EinsteinRelation.Sharpness.NoiseFiniteBlocks
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Process.Basic

/-! # Independence of noise processes on orthogonal compact test families

Source: `paper/main.tex:1212–1216`, the internal finite-range construction
`h ≔ ζ * tanh(K * W)` in the proof of `sharp.example` (Proposition 7.1). The generic Gaussian
characteristic law `hwhite` is an explicit hypothesis here, sourced from AKM Definition 5.1 /
Proposition 5.14, exactly as in `NoiseFiniteBlocks`. It is not a premise of the final sharpness
statement.

For arbitrary index types `S` and `T` and families `F : S → NoiseTest d`, `G : T → NoiseTest d`
whose cross integrals `∫ F i * G j` all vanish, the processes `(W (F i))_{i : S}` and
`(W (G j))_{j : T}` are independent. Each side carries the ordinary `Pi` evaluation σ-algebra.

The proof has three steps:
1. For finite index types, `indepFun_noise_finite_blocks` gives joint independence of the two
   blocks. Each block is enumerated by `Fintype.equivFin` and transported back by
   `ProbabilityTheory.IndepFun.comp` with measurable reindexing maps.
2. For finite subsets `I : Finset S` and `J : Finset T`, this gives joint independence of the
   restricted families `(fun (i : I) ↦ W (F i))` and `(fun (j : J) ↦ W (G j))`.
3. `ProbabilityTheory.IndepFun.process_indepFun_process` assembles these finite-block statements
   into independence of the full processes.

Empty blocks need no separate case: `Fintype.equivFin` covers them, and
`indepFun_noise_finite_blocks` has no positivity premise. Pairwise independence of single
coordinates is never used; the joint factorization in `indepFun_noise_finite_blocks` is the only
analytic input.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Joint independence of the evaluations on two finite-type blocks of compact tests whose cross
integrals vanish. Each block is enumerated by `Fintype.equivFin`, applies the `Fin`-indexed
finite-block theorem, and is transported back along the reindexing maps. -/
private theorem indepFun_noise_fintype_blocks {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    {A B : Type*} [Fintype A] [Fintype B] (F : A → NoiseTest d) (G : B → NoiseTest d)
    (horth : ∀ i j, (∫ y : Vec d, F i y * G j y) = 0) :
    ProbabilityTheory.IndepFun (fun ω (i : A) => W ω (F i))
      (fun ω (j : B) => W ω (G j)) P := by
  have hblock : ProbabilityTheory.IndepFun
      (fun ω (k : Fin (Fintype.card A)) => W ω (F ((Fintype.equivFin A).symm k)))
      (fun ω (l : Fin (Fintype.card B)) => W ω (G ((Fintype.equivFin B).symm l))) P :=
    indepFun_noise_finite_blocks P W hmeas hwhite (Fintype.card A) (Fintype.card B)
      (fun k => F ((Fintype.equivFin A).symm k)) (fun l => G ((Fintype.equivFin B).symm l))
      (fun k l => horth ((Fintype.equivFin A).symm k) ((Fintype.equivFin B).symm l))
  have hφ : Measurable
      (fun v : Fin (Fintype.card A) → ℝ => fun i : A => v (Fintype.equivFin A i)) :=
    Measurable.of_eval fun i => measurable_pi_apply (Fintype.equivFin A i)
  have hψ : Measurable
      (fun v : Fin (Fintype.card B) → ℝ => fun j : B => v (Fintype.equivFin B j)) :=
    Measurable.of_eval fun j => measurable_pi_apply (Fintype.equivFin B j)
  have hcomp : ProbabilityTheory.IndepFun
      ((fun v : Fin (Fintype.card A) → ℝ => fun i : A => v (Fintype.equivFin A i)) ∘
        (fun ω (k : Fin (Fintype.card A)) => W ω (F ((Fintype.equivFin A).symm k))))
      ((fun v : Fin (Fintype.card B) → ℝ => fun j : B => v (Fintype.equivFin B j)) ∘
        (fun ω (l : Fin (Fintype.card B)) => W ω (G ((Fintype.equivFin B).symm l)))) P :=
    ProbabilityTheory.IndepFun.comp hblock hφ hψ
  have hX : (fun v : Fin (Fintype.card A) → ℝ => fun i : A => v (Fintype.equivFin A i)) ∘
        (fun ω (k : Fin (Fintype.card A)) => W ω (F ((Fintype.equivFin A).symm k))) =
      fun ω (i : A) => W ω (F i) := by
    funext ω i
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  have hY : (fun v : Fin (Fintype.card B) → ℝ => fun j : B => v (Fintype.equivFin B j)) ∘
        (fun ω (l : Fin (Fintype.card B)) => W ω (G ((Fintype.equivFin B).symm l))) =
      fun ω (j : B) => W ω (G j) := by
    funext ω j
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [hX, hY] at hcomp
  exact hcomp

/-- Independence of the noise processes indexed by two arbitrary families of compact smooth tests
whose cross integrals all vanish. The two processes carry the ordinary `Pi` evaluation
σ-algebra; the finite-block joint independence is consumed, not pairwise coordinate
independence. -/
theorem indepFun_noise_processes_of_orthogonal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {d : ℕ} (W : Ω → NoiseSample d)
    (hmeas : ∀ f : NoiseTest d, Measurable (fun ω => W ω f))
    (hwhite : ∀ (f : NoiseTest d) (r : ℝ),
      (∫ ω, Complex.exp (Complex.I * (r : ℂ) * (W ω f : ℂ)) ∂P) =
        Complex.exp (((-(1/2 : ℝ))*r^2*∫ y : Vec d, (f y)^2) : ℂ))
    (S T : Type*) (F : S → NoiseTest d) (G : T → NoiseTest d)
    (horth : ∀ i j, (∫ y : Vec d, F i y * G j y) = 0) :
    ProbabilityTheory.IndepFun (fun ω => fun i : S => W ω (F i))
      (fun ω => fun j : T => W ω (G j)) P := by
  refine ProbabilityTheory.IndepFun.process_indepFun_process
    (X := fun i ω => W ω (F i)) (Y := fun j ω => W ω (G j))
    (fun i => hmeas (F i)) (fun j => hmeas (G j)) ?_
  intro I J
  exact indepFun_noise_fintype_blocks P W hmeas hwhite (fun i : I => F i.1) (fun j : J => G j.1)
    (fun i j => horth i.1 j.1)

end EinsteinRelation.Sharpness
