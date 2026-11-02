import EinsteinFull.Calculus.ComplexYosidaEvolutionSupport
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Comparing the actual bounded Yosida evolutions

The actual positive resolvents commute. Their bounded Yosida generators and
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

/-- Positive resolvents of the full actual unforced generator commute. -/
theorem unforcedComplexResolvent_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Commute (unforcedComplexResolvent Q i s hs) (unforcedComplexResolvent Q i t ht) := by
  by_cases he : s = t
  · subst t
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro f
    have hst := unforcedComplexResolvent_identity Q i s t hs ht f
    have hts := unforcedComplexResolvent_identity Q i t s ht hs f
    have hc : ((t - s : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm he))
    apply smul_right_injective (Lp ℂ 2 (reducedLaw Q)) hc
    change ((t - s : ℝ) : ℂ) • unforcedComplexResolvent Q i s hs
      (unforcedComplexResolvent Q i t ht f) =
      ((t - s : ℝ) : ℂ) • unforcedComplexResolvent Q i t ht
        (unforcedComplexResolvent Q i s hs f)
    rw [← hst]
    have hneg : ((t - s : ℝ) : ℂ) = -((s - t : ℝ) : ℂ) := by push_cast; ring
    rw [hneg, neg_smul, ← hts, neg_sub]

/-- The bounded Yosida generators at every two approximation indices commute. -/
theorem unforcedComplexYosida_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n m : ℕ) :
    Commute (unforcedComplexYosida Q i n) (unforcedComplexYosida Q i m) := by
  have hR := unforcedComplexResolvent_commute Q i ((n : ℝ)+1) ((m : ℝ)+1)
    (by positivity) (by positivity)
  have hB := (hR.smul_left (((n : ℝ)+1 : ℝ) : ℂ)).smul_right
    (((m : ℝ)+1 : ℝ) : ℂ)
  change Commute (unforcedComplexResolventApproximation Q i n)
    (unforcedComplexResolventApproximation Q i m) at hB
  have hA := (hB.sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.refl 1))
  exact (hA.smul_left (((n : ℝ)+1 : ℝ) : ℂ)).smul_right (((m : ℝ)+1 : ℝ) : ℂ)

/-- A bounded Yosida generator commutes with each bounded Yosida evolution. -/
theorem unforcedComplexYosida_commute_evolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n m : ℕ) (t : ℝ) :
    Commute (unforcedComplexYosida Q i n) (unforcedComplexYosidaEvolution Q i m t) :=
  ((unforcedComplexYosida_commute Q i n m).smul_right t).exp_right

/-- The bounded Yosida evolutions commute at all real times and indices. -/
theorem unforcedComplexYosidaEvolution_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n m : ℕ) (s t : ℝ) :
    Commute (unforcedComplexYosidaEvolution Q i n s)
      (unforcedComplexYosidaEvolution Q i m t) :=
  ((unforcedComplexYosida_commute_evolution Q i n m t).smul_left s).exp_left

private theorem hasDerivAt_comparison {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n m : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t s : ℝ) :
    HasDerivAt (fun r => unforcedComplexYosidaEvolution Q i n (t-r)
      (unforcedComplexYosidaEvolution Q i m r f))
      (unforcedComplexYosidaEvolution Q i n (t-s)
        (unforcedComplexYosidaEvolution Q i m s
          (unforcedComplexYosida Q i m f - unforcedComplexYosida Q i n f))) s := by
  let A := unforcedComplexYosida Q i n
  let B := unforcedComplexYosida Q i m
  let T := unforcedComplexYosidaEvolution Q i n
  let S := unforcedComplexYosidaEvolution Q i m
  have ha : HasDerivAt (fun r => T (t-r)) (-(T (t-s) * A)) s := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t-s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    simpa only [zero_sub, neg_smul, one_smul] using! h
  have hb : HasDerivAt S (S s * B) s := hasDerivAt_exp_smul_const (𝕂 := ℝ) B s
  have hc : A * S s = S s * A :=
    (unforcedComplexYosida_commute_evolution Q i n m s).eq
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
theorem norm_unforcedComplexYosidaEvolution_sub_evolution_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n m : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) (ht : 0 ≤ t) :
    ‖unforcedComplexYosidaEvolution Q i n t f - unforcedComplexYosidaEvolution Q i m t f‖ ≤
      t * ‖unforcedComplexYosida Q i n f - unforcedComplexYosida Q i m f‖ := by
  have hd (s : ℝ) (_hs : s ∈ Set.Icc 0 t) :=
    (hasDerivAt_comparison Q i n m f t s).hasDerivWithinAt (s := Set.Icc 0 t)
  have hb (s : ℝ) (hs : s ∈ Set.Ico 0 t) :
      ‖unforcedComplexYosidaEvolution Q i n (t-s)
        (unforcedComplexYosidaEvolution Q i m s
          (unforcedComplexYosida Q i m f - unforcedComplexYosida Q i n f))‖ ≤
        ‖unforcedComplexYosida Q i m f - unforcedComplexYosida Q i n f‖ :=
    (norm_unforcedComplexYosidaEvolution_apply_le Q i n _ (t-s)
      (sub_nonneg.mpr hs.2.le)).trans
      (norm_unforcedComplexYosidaEvolution_apply_le Q i m _ s hs.1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa only [sub_self, sub_zero, unforcedComplexYosidaEvolution_zero,
    ContinuousLinearMap.id_apply, norm_sub_rev, mul_comm] using h

/-- On the full actual generator domain the bounded evolutions form a Cauchy sequence. -/
theorem IsComplexGeneratorPair.cauchySeq_unforcedComplexYosidaEvolution
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => unforcedComplexYosidaEvolution Q i n t f) := by
  have hc := hfg.tendsto_unforcedComplexYosida.cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < t+1 := by linarith only [ht]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε/(t+1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ t * ‖unforcedComplexYosida Q i n f - unforcedComplexYosida Q i m f‖ :=
      norm_unforcedComplexYosidaEvolution_sub_evolution_le Q i n m f t ht
    _ ≤ (t+1) * ‖unforcedComplexYosida Q i n f - unforcedComplexYosida Q i m f‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- Contractivity and the actual dense generator domain give Cauchy evolutions on every L2 datum. -/
theorem cauchySeq_unforcedComplexYosidaEvolution {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) (ht : 0 ≤ t) :
    CauchySeq (fun n => unforcedComplexYosidaEvolution Q i n t f) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨u, ⟨g, hug⟩, hfu⟩ :=
    (dense_unforced_complexGenerator_domain Q i).exists_dist_lt f (by positivity : 0 < ε/3)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
    (hug.cauchySeq_unforcedComplexYosidaEvolution t ht) (ε/3) (by positivity)
  have hb (n : ℕ) : dist (unforcedComplexYosidaEvolution Q i n t f)
      (unforcedComplexYosidaEvolution Q i n t u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact norm_unforcedComplexYosidaEvolution_apply_le Q i n (f-u) t ht
  refine ⟨N, fun n hn m hm => ?_⟩
  calc
    _ ≤ dist (unforcedComplexYosidaEvolution Q i n t f)
          (unforcedComplexYosidaEvolution Q i n t u) +
        (dist (unforcedComplexYosidaEvolution Q i n t u)
          (unforcedComplexYosidaEvolution Q i m t u) +
         dist (unforcedComplexYosidaEvolution Q i m t u)
          (unforcedComplexYosidaEvolution Q i m t f)) :=
      by rw [← add_assoc]; exact dist_triangle4 _ _ _ _
    _ ≤ dist f u + (dist (unforcedComplexYosidaEvolution Q i n t u)
          (unforcedComplexYosidaEvolution Q i m t u) + dist f u) :=
      add_le_add (hb n) (add_le_add le_rfl (by
        simpa only [dist_comm] using hb m))
    _ < ε := by linarith only [hfu, hN n hn m hm]

end EinsteinFull
