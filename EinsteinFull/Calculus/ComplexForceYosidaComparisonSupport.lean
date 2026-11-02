import EinsteinFull.Calculus.ComplexForceYosidaEvolutionSupport
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparing the shifted forced Yosida evolutions

The actual shifted forced resolvents commute. Their bounded Yosida generators and
exponentials therefore commute, giving a comparison estimate controlled by
the generator difference on the initial datum. This is the convergence step
for the stationary semigroup construction, without an additional generation
assumption.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private instance complexOperator_smulComm {d : ℕ} (μ : Measure (FieldPair d)) :
    SMulCommClass ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  smul_comm c A B := by
    apply ContinuousLinearMap.ext
    intro f
    exact (A.map_smul c (B f)).symm

private instance realOperator_smulComm {d : ℕ} (μ : Measure (FieldPair d)) :
    SMulCommClass ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  smul_comm c A B := by
    apply ContinuousLinearMap.ext
    intro f
    exact ((A.restrictScalars ℝ).map_smul c (B f)).symm

private instance complexOperator_scalarTower {d : ℕ} (μ : Measure (FieldPair d)) :
    IsScalarTower ℂ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  smul_assoc c A B := by
    apply ContinuousLinearMap.ext
    intro f
    rfl

private instance realOperator_scalarTower {d : ℕ} (μ : Measure (FieldPair d)) :
    IsScalarTower ℝ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) where
  smul_assoc c A B := by
    apply ContinuousLinearMap.ext
    intro f
    rfl

private instance rationalOperator_normedAlgebra {d : ℕ} (μ : Measure (FieldPair d)) :
    NormedAlgebra ℚ (Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) := .restrictScalars ℚ ℂ _


/-- The bounded Yosida generators at every two approximation indices commute. -/
theorem forcedComplexYosida_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n m : ℕ) :
    Commute (forcedComplexYosida Q i ζ n) (forcedComplexYosida Q i ζ m) := by
  have hR := forcedComplexResolvent_commute Q i ζ
    (complexForceShift d Λ₀ ζ + ((n : ℝ)+1))
    (complexForceShift d Λ₀ ζ + ((m : ℝ)+1))
    (lt_add_of_pos_right _ (by positivity)) (lt_add_of_pos_right _ (by positivity))
  have hB := (hR.smul_left (((n : ℝ)+1 : ℝ) : ℂ)).smul_right
    (((m : ℝ)+1 : ℝ) : ℂ)
  change Commute (forcedComplexResolventApproximation Q i ζ n)
    (forcedComplexResolventApproximation Q i ζ m) at hB
  have hA := (hB.sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.refl 1))
  exact (hA.smul_left (((n : ℝ)+1 : ℝ) : ℂ)).smul_right (((m : ℝ)+1 : ℝ) : ℂ)

/-- A bounded Yosida generator commutes with each bounded Yosida evolution. -/
theorem forcedComplexYosida_commute_evolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n m : ℕ) (t : ℝ) :
    Commute (forcedComplexYosida Q i ζ n) (forcedComplexYosidaEvolution Q i ζ m t) :=
  ((forcedComplexYosida_commute Q i ζ n m).smul_right t).exp_right

/-- The bounded Yosida evolutions commute at all real times and indices. -/
theorem forcedComplexYosidaEvolution_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n m : ℕ) (s t : ℝ) :
    Commute (forcedComplexYosidaEvolution Q i ζ n s)
      (forcedComplexYosidaEvolution Q i ζ m t) :=
  ((forcedComplexYosida_commute_evolution Q i ζ n m t).smul_left s).exp_left

private theorem hasDerivAt_comparison {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n m : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t s : ℝ) :
    HasDerivAt (fun r => forcedComplexYosidaEvolution Q i ζ n (t-r)
      (forcedComplexYosidaEvolution Q i ζ m r f))
      (forcedComplexYosidaEvolution Q i ζ n (t-s)
        (forcedComplexYosidaEvolution Q i ζ m s
          (forcedComplexYosida Q i ζ m f - forcedComplexYosida Q i ζ n f))) s := by
  let A := forcedComplexYosida Q i ζ n
  let B := forcedComplexYosida Q i ζ m
  let T := forcedComplexYosidaEvolution Q i ζ n
  let S := forcedComplexYosidaEvolution Q i ζ m
  have ha : HasDerivAt (fun r => T (t-r)) (-(T (t-s) * A)) s := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t-s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    simpa only [zero_sub, neg_smul, one_smul] using! h
  have hb : HasDerivAt S (S s * B) s := hasDerivAt_exp_smul_const (𝕂 := ℝ) B s
  have hc : A * S s = S s * A :=
    (forcedComplexYosida_commute_evolution Q i ζ n m s).eq
  have hd : HasDerivAt (fun r => T (t-r) * S r)
      (T (t-s) * S s * (B-A)) s := by
    apply (ha.mul hb).congr_deriv
    have halg {α : Type} [Ring α] (X Y Z W : α)
        (h : Y * Z = Z * Y) : -(X * Y) * Z + X * (Z * W) = X * Z * (W - Y) := by
      rw [neg_mul, mul_assoc X Y Z, h]
      noncomm_ring
    exact halg (α := Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (T (t-s)) A (S s) B hc
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (reducedLaw Q)) f).restrictScalars ℝ
  have h := E.hasFDerivAt.comp_hasDerivAt s hd
  exact h

/-- Two actual bounded Yosida evolutions differ by at most time times the initial generator gap. -/
theorem norm_forcedComplexYosidaEvolution_sub_evolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (n m : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 ≤ t) :
    ‖forcedComplexYosidaEvolution Q i ζ n t f - forcedComplexYosidaEvolution Q i ζ m t f‖ ≤
      t * ‖forcedComplexYosida Q i ζ n f - forcedComplexYosida Q i ζ m f‖ := by
  have hd (s : ℝ) (_hs : s ∈ Set.Icc 0 t) :=
    (hasDerivAt_comparison Q i ζ n m f t s).hasDerivWithinAt (s := Set.Icc 0 t)
  have hb (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
      ‖forcedComplexYosidaEvolution Q i ζ n (t-s)
        (forcedComplexYosidaEvolution Q i ζ m s
          (forcedComplexYosida Q i ζ m f - forcedComplexYosida Q i ζ n f))‖ ≤
        ‖forcedComplexYosida Q i ζ m f - forcedComplexYosida Q i ζ n f‖ :=
    (norm_forcedComplexYosidaEvolution_apply_le Q i ζ n _ (t-s)
      (sub_nonneg.mpr hs.2.le)).trans
      (norm_forcedComplexYosidaEvolution_apply_le Q i ζ m _ s hs.1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa only [sub_self, sub_zero, forcedComplexYosidaEvolution_zero,
    ContinuousLinearMap.id_apply, norm_sub_rev, mul_comm] using h

/-- On the full actual generator domain the bounded evolutions form a Cauchy sequence. -/
theorem IsComplexGeneratorPair.cauchySeq_forcedComplexYosidaEvolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => forcedComplexYosidaEvolution Q i ζ n t f) := by
  have hc := hfg.tendsto_forcedComplexYosida.cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < t+1 := by linarith only [ht]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/(t+1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ t * ‖forcedComplexYosida Q i ζ n f - forcedComplexYosida Q i ζ m f‖ :=
      norm_forcedComplexYosidaEvolution_sub_evolution_le Q i ζ n m f t ht
    _ ≤ (t+1) * ‖forcedComplexYosida Q i ζ n f - forcedComplexYosida Q i ζ m f‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- Contractivity and the actual dense generator domain give Cauchy evolutions on every L2 datum. -/
theorem cauchySeq_forcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => forcedComplexYosidaEvolution Q i ζ n t f) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_complexGenerator_domain Q i ζ).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
    (hug.cauchySeq_forcedComplexYosidaEvolution t ht) (ε/3) (by positivity)
  have hb (n : ℕ) : dist (forcedComplexYosidaEvolution Q i ζ n t f)
      (forcedComplexYosidaEvolution Q i ζ n t u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_forcedComplexYosidaEvolution_apply_le Q i ζ n (f-u) t ht
  refine ⟨N, fun n hn m hm => ?_⟩
  calc
    _ ≤ dist (forcedComplexYosidaEvolution Q i ζ n t f)
          (forcedComplexYosidaEvolution Q i ζ n t u) +
        (dist (forcedComplexYosidaEvolution Q i ζ n t u)
          (forcedComplexYosidaEvolution Q i ζ m t u) +
         dist (forcedComplexYosidaEvolution Q i ζ m t u)
          (forcedComplexYosidaEvolution Q i ζ m t f)) :=
      by rw [← add_assoc]; exact dist_triangle4 _ _ _ _
    _ ≤ dist f u + (dist (forcedComplexYosidaEvolution Q i ζ n t u)
          (forcedComplexYosidaEvolution Q i ζ m t u) + dist f u) :=
      add_le_add (hb n) (add_le_add le_rfl (by
        simpa only [dist_comm] using hb m))
    _ < ε := by linarith only [hfu, hN n hn m hm]

end EinsteinFull
