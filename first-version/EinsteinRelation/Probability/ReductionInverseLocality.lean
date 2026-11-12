import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Tactic.Ring
import EinsteinRelation.Probability.ReductionLocality

/-! # Exact inverse transport of the physical-to-reduced environment map

The reduction `reduce (a₀,V) = (exp(-2V) a₀, exp(-2V))` from `paper/main.tex:199–208`
is injective, and the joint observations of the reduced pair on a set `U` generate the
same σ-algebra, pulled back, as the physical joint observations on `U`
(`paper/main.tex:235–242`). At each point the inverse is the Borel map
`(M,r) ↦ (r⁻¹ • M, -(1/2) * log r)`, applied only where the clock density `r` is positive.
No global inverse on `FieldPair d` is defined.
-/

namespace EinsteinRelation.Probability

/-- The pointwise inverse of the reduced value `(M,r) ↦ (r⁻¹ • M, -(1/2) log r)`, used for `r > 0`. -/
private noncomputable def recoverPoint {d : ℕ} (p : Mat d × ℝ) : Mat d × ℝ :=
  (p.2⁻¹ • p.1, -(1 / 2) * Real.log p.2)

/-- The pointwise inverse is Borel measurable on all of `Mat d × ℝ`. -/
private theorem measurable_recoverPoint {d : ℕ} :
    Measurable (recoverPoint (d := d)) := by
  have hsnd : Measurable (fun p : Mat d × ℝ => p.2) := measurable_snd
  have hfst : Measurable (fun p : Mat d × ℝ => p.1) := measurable_fst
  have hsmul : Measurable (fun p : Mat d × ℝ => p.2⁻¹ • p.1) :=
    (hsnd.inv).smul hfst
  have hlog : Measurable (fun p : Mat d × ℝ => -(1 / 2 : ℝ) * Real.log p.2) :=
    (Real.measurable_log.comp hsnd).const_mul (-(1 / 2 : ℝ))
  exact hsmul.prodMk hlog

/-- The pointwise inverse recovers the physical pair, since the clock density is positive. -/
private theorem recover_reduce_apply {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    recoverPoint ((reduce ω).1 x, (reduce ω).2 x) = (ω.1 x, ω.2 x) := by
  have hμ : clockDensity ω x ≠ 0 := (clockDensity_pos ω x).ne'
  have hlog : -(1 / 2 : ℝ) * Real.log (clockDensity ω x) = ω.2 x := by
    unfold clockDensity
    rw [Real.log_exp]
    ring
  show ((clockDensity ω x)⁻¹ • (clockDensity ω x • ω.1 x),
    -(1 / 2 : ℝ) * Real.log (clockDensity ω x)) = (ω.1 x, ω.2 x)
  rw [inv_smul_smul₀ hμ, hlog]

/-- The physical pair is recovered from its reduced image, so the reduction is injective. -/
theorem reduce_injective {d : ℕ} :
    Function.Injective (reduce (d := d)) := by
  intro ω ω' h
  have hpt : ∀ x : Vec d, (ω.1 x, ω.2 x) = (ω'.1 x, ω'.2 x) := by
    intro x
    calc (ω.1 x, ω.2 x) = recoverPoint ((reduce ω).1 x, (reduce ω).2 x) :=
          (recover_reduce_apply ω x).symm
      _ = recoverPoint ((reduce ω').1 x, (reduce ω').2 x) := by rw [h]
      _ = (ω'.1 x, ω'.2 x) := recover_reduce_apply ω' x
  have h1 : ω.1 = ω'.1 := ContinuousMap.ext fun x => congrArg Prod.fst (hpt x)
  have h2 : ω.2 = ω'.2 := ContinuousMap.ext fun x => congrArg Prod.snd (hpt x)
  exact Prod.ext h1 h2

/-- For `x ∈ U`, the σ-algebra of the single observation `(a₀ x, V x)` lies in `localSigma U`. -/
private theorem evalPair_comap_le_localSigma {d : ℕ} {U : Set (Vec d)} {x : Vec d}
    (hx : x ∈ U) :
    MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x, ω.2 x)) inferInstance ≤
      localSigma U := by
  unfold localSigma
  exact le_iSup (fun y : U => MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 y, ω.2 y))
    inferInstance) ⟨x, hx⟩

/-- The evaluation `ω ↦ (ω.1 x, ω.2 x)` is measurable for `localSigma U` when `x ∈ U`. -/
private theorem measurable_evalPair_of_mem {d : ℕ} {U : Set (Vec d)} {x : Vec d}
    (hx : x ∈ U) :
    @Measurable (FieldPair d) (Mat d × ℝ) (localSigma U) inferInstance
      (fun ω : FieldPair d => (ω.1 x, ω.2 x)) :=
  Measurable.of_comap_le (evalPair_comap_le_localSigma hx)

/-- The physical joint σ-algebra on `U` is contained in its pullback along `reduce`. -/
private theorem localSigma_le_comap_reduce {d : ℕ} (U : Set (Vec d)) :
    localSigma U ≤ (localSigma U).comap (reduce (d := d)) := by
  show (⨆ x : U, MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x, ω.2 x)) inferInstance) ≤
    (localSigma U).comap (reduce (d := d))
  refine iSup_le fun x => ?_
  have hE : @Measurable (FieldPair d) (Mat d × ℝ) (localSigma U) inferInstance
      (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) :=
    measurable_evalPair_of_mem x.2
  have hR : @Measurable (FieldPair d) (FieldPair d) ((localSigma U).comap (reduce (d := d)))
      (localSigma U) (reduce (d := d)) :=
    comap_measurable (reduce (d := d))
  have h : @Measurable (FieldPair d) (Mat d × ℝ) ((localSigma U).comap (reduce (d := d)))
      inferInstance
      (fun ω : FieldPair d =>
        recoverPoint ((reduce ω).1 (x : Vec d), (reduce ω).2 (x : Vec d))) :=
    measurable_recoverPoint.comp (hE.comp hR)
  have hfun : (fun ω : FieldPair d =>
      recoverPoint ((reduce ω).1 (x : Vec d), (reduce ω).2 (x : Vec d)))
      = fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d)) :=
    funext fun ω => recover_reduce_apply ω (x : Vec d)
  rw [hfun] at h
  exact Measurable.comap_le h

/-- Pulling back the reduced joint σ-algebra along `reduce` gives back the physical one. -/
theorem localSigma_reduce_comap_eq {d : ℕ} (U : Set (Vec d)) :
    (localSigma U).comap (reduce (d := d)) = localSigma U :=
  le_antisymm (localSigma_reduce_comap_le U) (localSigma_le_comap_reduce U)

end EinsteinRelation.Probability
