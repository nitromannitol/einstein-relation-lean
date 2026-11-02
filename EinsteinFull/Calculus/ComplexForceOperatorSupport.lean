import EinsteinFull.Calculus.ComplexForceResolventSupport

/-!
# Bounded resolvents and closedness of the actual forced stationary generator

The full forced resolvent solutions are bundled as bounded complex linear maps.
The exact graph characterization gives the resolvent identity and closedness.
Their ranges equal the common dense generator domain, without symmetry of the
forced operator. The operator construction follows ComplexGeneratorOperatorSupport.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private def resolventValue {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) := (exists_forced_complexGenerator_resolvent Q i ζ s hs rhs).choose

private theorem resolventValue_spec {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i ζ (resolventValue Q i ζ s hs rhs)
      ((s : ℂ) • resolventValue Q i ζ s hs rhs - rhs) :=
  (exists_forced_complexGenerator_resolvent Q i ζ s hs rhs).choose_spec.1

private def resolventLinearMap {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) where
  toFun := resolventValue Q i ζ s hs
  map_add' := by
    intro f g
    apply IsComplexGeneratorPair.forced_resolvent_unique hs (resolventValue_spec Q i ζ s hs (f+g))
    convert (resolventValue_spec Q i ζ s hs f).add (resolventValue_spec Q i ζ s hs g) using 1
    module
  map_smul' := by
    intro c f
    change resolventValue Q i ζ s hs (c • f) = c • resolventValue Q i ζ s hs f
    apply IsComplexGeneratorPair.forced_resolvent_unique hs (resolventValue_spec Q i ζ s hs (c • f))
    convert (resolventValue_spec Q i ζ s hs f).smul c using 1
    module

private theorem resolventValue_bound {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ‖resolventValue Q i ζ s hs rhs‖ ≤ (s - complexForceShift d Λ₀ ζ)⁻¹ * ‖rhs‖ := by
  have hb := (exists_forced_complexGenerator_resolvent Q i ζ s hs rhs).choose_spec.2
  change (s - complexForceShift d Λ₀ ζ) * ‖resolventValue Q i ζ s hs rhs‖ ≤ ‖rhs‖ at hb
  exact (le_div_iff₀ (sub_pos.mpr hs)).mpr (by simpa only [mul_comm] using hb)
    |>.trans_eq (div_eq_inv_mul _ _)

/-- The shifted resolvent of the actual full forced complex generator graph. -/
def forcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (resolventLinearMap Q i ζ s hs).mkContinuous (s - complexForceShift d Λ₀ ζ)⁻¹
    (resolventValue_bound Q i ζ s hs)

/-- The bundled resolvent solves the full weak generator equation. -/
theorem forcedComplexResolvent_spec {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i ζ (forcedComplexResolvent Q i ζ s hs rhs)
      ((s : ℂ) • forcedComplexResolvent Q i ζ s hs rhs - rhs) :=
  resolventValue_spec Q i ζ s hs rhs

/-- The forced resolvent has the shifted L2 operator norm bound. -/
theorem norm_forcedComplexResolvent_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    ‖forcedComplexResolvent Q i ζ s hs‖ ≤ (s - complexForceShift d Λ₀ ζ)⁻¹ :=
  (forcedComplexResolvent Q i ζ s hs).opNorm_le_bound (inv_pos.mpr (sub_pos.mpr hs)).le
    (resolventValue_bound Q i ζ s hs)

/-- The forced resolvent is injective. -/
theorem forcedComplexResolvent_injective {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) :
    Function.Injective (forcedComplexResolvent Q i ζ s hs) := by
  intro f g he
  have hf := forcedComplexResolvent_spec Q i ζ s hs f
  have hg := forcedComplexResolvent_spec Q i ζ s hs g
  rw [he] at hf
  have hh := hf.unique hg
  exact neg_injective (add_left_cancel (by simpa only [sub_eq_add_neg] using hh))

/-- The actual generator graph is exactly the graph recovered from one shifted forced resolvent. -/
theorem isComplexGeneratorPair_iff_forced_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i ζ f g ↔
      forcedComplexResolvent Q i ζ s hs ((s : ℂ) • f - g) = f := by
  constructor
  · intro h
    apply IsComplexGeneratorPair.forced_resolvent_unique hs
      (forcedComplexResolvent_spec Q i ζ s hs _)
    simpa only [sub_sub_cancel] using h
  · intro h
    have hp := forcedComplexResolvent_spec Q i ζ s hs ((s : ℂ) • f - g)
    rw [h, sub_sub_cancel] at hp
    exact hp

/-- Shifted resolvents of the actual forced graph satisfy the resolvent identity. -/
theorem forcedComplexResolvent_identity {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s t : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (ht : complexForceShift d Λ₀ ζ < t)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    forcedComplexResolvent Q i ζ s hs f - forcedComplexResolvent Q i ζ t ht f =
      ((t - s : ℝ) : ℂ) • forcedComplexResolvent Q i ζ s hs
        (forcedComplexResolvent Q i ζ t ht f) := by
  have he := (isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs _ _).mp
    (forcedComplexResolvent_spec Q i ζ t ht f)
  have ha : (s : ℂ) • forcedComplexResolvent Q i ζ t ht f -
      ((t : ℂ) • forcedComplexResolvent Q i ζ t ht f - f) =
      f + ((s - t : ℝ) : ℂ) • forcedComplexResolvent Q i ζ t ht f := by
    push_cast
    module
  rw [ha, map_add, map_smul] at he
  conv_lhs => rw [← he]
  push_cast
  module

/-- Shifted resolvents of the full actual forced generator commute. -/
theorem forcedComplexResolvent_commute {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s t : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (ht : complexForceShift d Λ₀ ζ < t) :
    Commute (forcedComplexResolvent Q i ζ s hs) (forcedComplexResolvent Q i ζ t ht) := by
  by_cases he : s = t
  · subst t
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro f
    have hst := forcedComplexResolvent_identity Q i ζ s t hs ht f
    have hts := forcedComplexResolvent_identity Q i ζ t s ht hs f
    have hc : ((t - s : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm he))
    apply smul_right_injective (Lp ℂ 2 (reducedLaw Q)) hc
    change ((t - s : ℝ) : ℂ) • forcedComplexResolvent Q i ζ s hs
      (forcedComplexResolvent Q i ζ t ht f) =
      ((t - s : ℝ) : ℂ) • forcedComplexResolvent Q i ζ t ht
        (forcedComplexResolvent Q i ζ s hs f)
    rw [← hst]
    have hneg : ((t - s : ℝ) : ℂ) = -((s - t : ℝ) : ℂ) := by push_cast; ring
    rw [hneg, neg_smul, ← hts, neg_sub]

/-- Every shifted forced resolvent has range exactly the full generator domain. -/
theorem range_forcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) :
    Set.range (forcedComplexResolvent Q i ζ s hs) =
      {f : Lp ℂ 2 (reducedLaw Q) | ∃ g, IsComplexGeneratorPair Q i ζ f g} := by
  ext f
  constructor
  · rintro ⟨rhs, rfl⟩
    exact ⟨_, forcedComplexResolvent_spec Q i ζ s hs rhs⟩
  · rintro ⟨g, hg⟩
    exact ⟨(s : ℂ) • f - g, (isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs f g).mp hg⟩

/-- The forced resolvent has dense range, using the actual common dense domain. -/
theorem denseRange_forcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) :
    DenseRange (forcedComplexResolvent Q i ζ s hs) := by
  change Dense (Set.range (forcedComplexResolvent Q i ζ s hs))
  rw [range_forcedComplexResolvent]
  exact dense_complexGenerator_domain Q i ζ

/-- The full actual forced generator graph is closed in the product L2 topology. -/
theorem isClosed_complexGenerator_graph {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    IsClosed {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexGeneratorPair Q i ζ p.1 p.2} := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
  have he : {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexGeneratorPair Q i ζ p.1 p.2} =
      {p | forcedComplexResolvent Q i ζ s hs ((s : ℂ) • p.1 - p.2) = p.1} := by
    ext p
    exact isComplexGeneratorPair_iff_forced_resolvent Q i ζ s hs p.1 p.2
  rw [he]
  exact isClosed_eq ((forcedComplexResolvent Q i ζ s hs).continuous.comp
    ((continuous_fst.const_smul (s : ℂ)).sub continuous_snd)) continuous_fst

end EinsteinFull
