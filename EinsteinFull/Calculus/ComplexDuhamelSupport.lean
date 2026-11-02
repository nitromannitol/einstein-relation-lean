import EinsteinFull.Calculus.ComplexSemigroupEnergySupport
import EinsteinFull.Calculus.ComplexEvolutionGeneratorSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Variation of constants for the actual stationary complex semigroups

Bounded unforced Yosida evolutions give an integrated identity along the full
forced generator domain. Their strong limit recovers the actual unforced
semigroup and its actual coefficient drift, without an assumed perturbation formula.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- A bounded unforced Yosida generator is the normalized resolvent of the actual output. -/
theorem IsComplexGeneratorPair.unforced_yosida_eq_approximation
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) (n : ℕ) :
    unforcedComplexYosida Q i n f = unforcedComplexResolventApproximation Q i n g := by
  change (((n : ℝ) + 1 : ℝ) : ℂ) •
    ((((n : ℝ) + 1 : ℝ) : ℂ) •
      unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity) f - f) = _
  rw [hfg.unforced_resolvent_error]
  rfl

/-- On its entire actual domain the unforced Yosida output is bounded by the generator output. -/
theorem IsComplexGeneratorPair.norm_unforced_yosida_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) (n : ℕ) :
    ‖unforcedComplexYosida Q i n f‖ ≤ ‖g‖ := by
  rw [hfg.unforced_yosida_eq_approximation]
  exact norm_unforcedComplexResolventApproximation_le Q i n g

private theorem continuous_yosida_operator {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (n : ℕ) :
    Continuous (unforcedComplexYosidaEvolution Q i n) :=
  continuous_iff_continuousAt.mpr fun s =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (unforcedComplexYosida Q i n) s).continuousAt

private theorem hasDerivWithinAt_split_yosida {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (n : ℕ) (t s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt
      (fun r : ℝ => unforcedComplexYosidaEvolution Q i n (t-r) (P r.toNNReal f))
      (unforcedComplexYosidaEvolution Q i n (t-s)
        (P s.toNNReal g - unforcedComplexYosida Q i n (P s.toNNReal f))) (Ici s) s := by
  let A := unforcedComplexYosida Q i n
  let T := unforcedComplexYosidaEvolution Q i n
  have ha : HasDerivAt (fun r => T (t-r)) (-(T (t-s) * A)) s := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (t-s)).scomp s
      ((hasDerivAt_const s t).sub (hasDerivAt_id s))
    simpa only [zero_sub, neg_smul, one_smul, Function.comp_def] using! h
  let R := ContinuousLinearMap.restrictScalarsL ℂ (Lp ℂ 2 (reducedLaw Q))
    (Lp ℂ 2 (reducedLaw Q)) ℝ ℝ
  have hd := (R.hasFDerivAt.comp_hasDerivAt s ha).hasDerivWithinAt.clm_apply
    (hP.hasDerivWithinAt_orbit hfg s hs)
  convert! hd using 1
  change T (t-s) (P s.toNNReal g - A (P s.toNNReal f)) =
    (-(T (t-s) * A)) (P s.toNNReal f) + T (t-s) (P s.toNNReal g)
  rw [map_sub, ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply]
  abel

/-- Exact variation of constants with a bounded unforced Yosida evolution. -/
theorem IsComplexEnvironmentSemigroup.integral_yosida_difference
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (n : ℕ) (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), unforcedComplexYosidaEvolution Q i n (t-s)
      (P s.toNNReal g - unforcedComplexYosida Q i n (P s.toNNReal f))) =
      P t f - unforcedComplexYosidaEvolution Q i n t f := by
  have hu := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv := (hP.2.2.1 g).comp continuous_real_toNNReal
  have hT := (continuous_yosida_operator Q i n).comp ((continuous_const (y := (t : ℝ))).fun_sub continuous_id)
  have hc := hT.clm_apply hu
  have hi := hT.clm_apply (hv.sub ((unforcedComplexYosida Q i n).continuous.comp hu))
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (a := (0 : ℝ)) (b := (t : ℝ)) t.property hc.continuousOn
    (fun s hs => (hasDerivWithinAt_split_yosida hP hfg n t s hs.1.le).mono
      Ioi_subset_Ici_self) (hi.intervalIntegrable 0 t)
  simpa only [Function.comp_apply, id_eq, sub_self, Real.toNNReal_coe, unforcedComplexYosidaEvolution_zero,
    ContinuousLinearMap.id_apply, Real.toNNReal_zero, hP.1, sub_zero] using he

/-- Every complete unforced family is contractive on the actual complex L2 space. -/
theorem IsComplexEnvironmentSemigroup.norm_unforced_apply_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : ‖R t f‖ ≤ ‖f‖ := by
  rw [hR.unique (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i)]
  exact norm_unforcedComplexEvolution_apply_le Q i t f

/-- Strong continuity and contractivity allow both time and L2 datum to vary continuously. -/
theorem IsComplexEnvironmentSemigroup.continuous_unforced_apply
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {α : Type*} [TopologicalSpace α] {τ : α → ℝ≥0}
    {u : α → Lp ℂ 2 (reducedLaw Q)} (ht : Continuous τ) (hu : Continuous u) :
    Continuous (fun x => R (τ x) (u x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : Tendsto (fun y => R (τ y) (u y-u x)) (𝓝 x) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    exact squeeze_zero (fun _ => norm_nonneg _)
      (fun y => hR.norm_unforced_apply_le (τ y) (u y-u x))
      (tendsto_iff_norm_sub_tendsto_zero.mp (hu.tendsto x))
  have hf := ((hR.2.2.1 (u x)).comp ht).tendsto x
  simpa only [Function.comp_apply, map_sub, sub_add_cancel, zero_add] using! hz.add hf

/-- Duhamel's formula uses the actual coefficient drift along the complete forced domain. -/
theorem IsComplexEnvironmentSemigroup.integral_force_drift
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    ζ • (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s))) =
      P t f - R t f := by
  rw [hR.unique (isComplexEnvironmentSemigroup_unforcedComplexEvolution Q i)]
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f
  let v : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal g
  let w : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => v s - ζ • complexForceDrift Q i (G s)
  have hu : Continuous u := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv : Continuous v := (hP.2.2.1 g).comp continuous_real_toNNReal
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG hu hv
  have hwc : Continuous w := hv.sub
    (continuous_const.fun_smul ((complexForceDrift Q i).continuous.comp hGc))
  have hw (s : ℝ) : IsComplexGeneratorPair Q i 0 (u s) (w s) := by
    have h := (hP.map_generator hfg s.toNNReal).change_force 0 (hG s)
    simpa only [zero_sub, neg_smul, ← sub_eq_add_neg, WithLp.toLp_ofLp] using h
  let F : ℕ → ℝ → Lp ℂ 2 (reducedLaw Q) := fun n s =>
    unforcedComplexYosidaEvolution Q i n (t-s) (v s - unforcedComplexYosida Q i n (u s))
  have hFc (n : ℕ) : Continuous (F n) :=
    ((continuous_yosida_operator Q i n).comp
      ((continuous_const (y := (t : ℝ))).fun_sub continuous_id)).clm_apply
      (hv.sub ((unforcedComplexYosida Q i n).continuous.comp hu))
  have hlim : Tendsto (fun n => ∫ s in (0 : ℝ)..(t : ℝ), F n s) atTop
      (𝓝 (∫ s in (0 : ℝ)..(t : ℝ),
        unforcedComplexEvolution Q i (Real.toNNReal (t-s)) (v s-w s))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s => ‖v s‖ + ‖w s‖)
    · exact Eventually.of_forall fun n => (hFc n).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
      exact (norm_unforcedComplexYosidaEvolution_apply_le Q i n _ (t-s)
        (sub_nonneg.mpr hs.2)).trans
          ((norm_sub_le _ _).trans (add_le_add le_rfl ((hw s).norm_unforced_yosida_le n)))
    · exact (hv.norm.add hwc.norm).intervalIntegrable 0 t
    · apply Eventually.of_forall
      intro s hs
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
      have he : ((Real.toNNReal (t-s) : ℝ≥0) : ℝ) = t-s :=
        Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)
      have hl := tendsto_unforcedComplexYosidaEvolution_apply Q i
        (Real.toNNReal (t-s)) ((tendsto_const_nhds (x := v s)).sub (hw s).tendsto_unforcedComplexYosida)
      simpa only [he] using hl
  have he : (∫ s in (0 : ℝ)..(t : ℝ),
      unforcedComplexEvolution Q i (Real.toNNReal (t-s)) (v s-w s)) =
      P t f - unforcedComplexEvolution Q i t f := by
    have hl := (tendsto_const_nhds (x := P t f)).sub
      (tendsto_unforcedComplexYosidaEvolution Q i t f)
    have hn (n : ℕ) : (∫ s in (0 : ℝ)..(t : ℝ), F n s) =
        P t f - unforcedComplexYosidaEvolution Q i n t f :=
      hP.integral_yosida_difference hfg n t
    simp_rw [← hn] at hl
    exact tendsto_nhds_unique hlim hl
  rw [← he, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr
  intro s _
  change ζ • unforcedComplexEvolution Q i (Real.toNNReal (t-s)) (complexForceDrift Q i (G s)) =
    unforcedComplexEvolution Q i (Real.toNNReal (t-s))
      (v s - (v s - ζ • complexForceDrift Q i (G s)))
  rw [sub_sub_cancel, map_smul]

/-- The actual drift in the domain-level Duhamel formula is Bochner integrable. -/
theorem IsComplexEnvironmentSemigroup.intervalIntegrable_force_drift
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    IntervalIntegrable
      (fun s : ℝ => R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s))) volume 0 t := by
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal)
  exact (hR.continuous_unforced_apply
    (continuous_real_toNNReal.comp ((continuous_const (y := (t : ℝ))).fun_sub continuous_id))
    ((complexForceDrift Q i).continuous.comp hGc)).intervalIntegrable 0 t

/-- Duhamel's formula bounds the forced/unforced difference by the actual gradient orbit. -/
theorem IsComplexEnvironmentSemigroup.norm_sub_unforced_le_integral_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : ∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (G s)) (t : ℝ≥0) :
    ‖P t f-R t f‖ ≤ ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
      (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖) := by
  have hGc : Continuous G := continuous_complexHorizontalGradient_of_generator
    (fun s => hP.map_generator hfg s.toNNReal) hG
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal)
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (a := (0 : ℝ)) (b := (t : ℝ)) (μ := volume) t.property
    (Eventually.of_forall fun s _ =>
      (hR.norm_unforced_apply_le (Real.toNNReal (t-s)) _).trans
        (norm_complexForceDrift_apply_le Q i (G s)))
    ((continuous_const.mul hGc.norm).intervalIntegrable 0 t)
  rw [← hP.integral_force_drift hR hfg hG t, norm_smul]
  calc
    _ ≤ ‖ζ‖ * (∫ s in (0 : ℝ)..(t : ℝ),
        ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖G s‖) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg ζ)
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

/-- A full forced-domain datum has one continuous actual gradient orbit satisfying Duhamel at all times. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_orbit_duhamel
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)), Continuous G ∧
      (∀ s, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P s.toNNReal f) (G s)) ∧
      ∀ t : ℝ≥0, P t f = R t f + ζ •
        (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s))) := by
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  refine ⟨G, hGc, hG, fun t => ?_⟩
  rw [hP.integral_force_drift hR hfg hG t, add_sub_cancel]

end EinsteinFull
