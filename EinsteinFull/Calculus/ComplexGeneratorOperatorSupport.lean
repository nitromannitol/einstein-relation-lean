import EinsteinFull.Calculus.ComplexGeneratorResolventSupport
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Operator properties of the actual unforced stationary generator

Linearity of the full weak generator graph allows the positive resolvent
solutions to be bundled as bounded complex linear maps. Their exact graph
characterization retains the entire horizontal H1 test domain.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private def principal {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ :=
  fun ω => ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * H j ω

private def flux {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ :=
  fun ω => (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω

private theorem principal_integrable {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) : Integrable (principal Q G H) (reducedLaw Q) := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  have hp := ((Lp.memLp (G k)).integrable_mul (Lp.memLp (H j))).mul_of_top_right
    (memLp_reduced_coefficient_complex Q j k)
  convert hp using 1
  ext ω
  simp only [Pi.mul_apply]
  ring

private theorem flux_integrable {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (flux Q i G v) (reducedLaw Q) := by
  unfold flux
  simp only [Finset.sum_mul]
  apply integrable_finset_sum
  intro j _
  have hp := ((Lp.memLp (G j)).integrable_mul (Lp.memLp v)).mul_of_top_right
    (memLp_reduced_coefficient_complex Q j i)
  convert hp using 1
  ext ω
  simp only [Pi.mul_apply]
  ring

private theorem integral_principal_add {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, principal Q (fun j => G j + H j) V ω ∂reducedLaw Q) =
      (∫ ω, principal Q G V ω ∂reducedLaw Q) +
      ∫ ω, principal Q H V ω ∂reducedLaw Q := by
  rw [← integral_add (principal_integrable Q G V) (principal_integrable Q H V)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_add (G j) (H j)] with ω hω
  simp only [principal, hω, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

private theorem integral_principal_smul {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (c : ℂ) (G V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, principal Q (fun j => c • G j) V ω ∂reducedLaw Q) =
      c * ∫ ω, principal Q G V ω ∂reducedLaw Q := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_smul c (G j)] with ω hω
  simp only [principal, hω, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem integral_flux_add {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, flux Q i (fun j => G j + H j) v ω ∂reducedLaw Q) =
      (∫ ω, flux Q i G v ω ∂reducedLaw Q) + ∫ ω, flux Q i H v ω ∂reducedLaw Q := by
  rw [← integral_add (flux_integrable Q i G v) (flux_integrable Q i H v)]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_add (G j) (H j)] with ω hω
  simp only [flux, hω, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_mul]

private theorem integral_flux_smul {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (c : ℂ) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (v : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, flux Q i (fun j => c • G j) v ω ∂reducedLaw Q) =
      c * ∫ ω, flux Q i G v ω ∂reducedLaw Q := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_smul c (G j)] with ω hω
  simp only [flux, hω, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The full actual weak generator graph is additive, at every complex force. -/
theorem IsComplexGeneratorPair.add {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g h k : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexGeneratorPair Q i ζ f g) (hh : IsComplexGeneratorPair Q i ζ h k) :
    IsComplexGeneratorPair Q i ζ (f + h) (g + k) := by
  obtain ⟨G, hG, hwG⟩ := hf
  obtain ⟨H, hH, hwH⟩ := hh
  refine ⟨fun j => G j + H j, fun j => (hG j).add (hH j), ?_⟩
  intro v V hV
  have hm : (∫ ω, (g + k) ω * v ω ∂reducedLaw Q) =
      (∫ ω, g ω * v ω ∂reducedLaw Q) + ∫ ω, k ω * v ω ∂reducedLaw Q := by
    have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
      (Lp.memLp g).integrable_mul (Lp.memLp v)
    have hk : Integrable (fun ω => k ω * v ω) (reducedLaw Q) :=
      (Lp.memLp k).integrable_mul (Lp.memLp v)
    rw [← integral_add hg hk]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add g k] with ω hω
    simp only [hω, Pi.add_apply, add_mul]
  change _ = -(1/2:ℂ) * (∫ ω, principal Q (fun j => G j + H j) V ω ∂reducedLaw Q) +
    ζ * ∫ ω, flux Q i (fun j => G j + H j) v ω ∂reducedLaw Q
  rw [hm, integral_principal_add, integral_flux_add, hwG v V hV, hwH v V hV]
  unfold principal flux
  ring

/-- The full actual weak generator graph is complex linear in its pair. -/
theorem IsComplexGeneratorPair.smul {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hf : IsComplexGeneratorPair Q i ζ f g) (c : ℂ) :
    IsComplexGeneratorPair Q i ζ (c • f) (c • g) := by
  obtain ⟨G, hG, hwG⟩ := hf
  refine ⟨fun j => c • G j, fun j => (hG j).smul c, ?_⟩
  intro v V hV
  have hm : (∫ ω, (c • g) ω * v ω ∂reducedLaw Q) =
      c * ∫ ω, g ω * v ω ∂reducedLaw Q := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c g] with ω hω
    simp only [hω, Pi.smul_apply, smul_eq_mul]
    ring
  change _ = -(1/2:ℂ) * (∫ ω, principal Q (fun j => c • G j) V ω ∂reducedLaw Q) +
    ζ * ∫ ω, flux Q i (fun j => c • G j) v ω ∂reducedLaw Q
  rw [hm, integral_principal_smul, integral_flux_smul, hwG v V hV]
  unfold principal flux
  ring

private theorem generator_inner_eq_energy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (g : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hw : ∀ v V, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
      (∫ ω, g ω * v ω ∂reducedLaw Q) = -(1/2:ℂ) *
        (∫ ω, principal Q G V ω ∂reducedLaw Q) +
        (0:ℂ) * ∫ ω, flux Q i G v ω ∂reducedLaw Q)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    inner ℂ v g = -(1/2:ℂ) *
      ∫ ω, ∑ j, ∑ k, star (V j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q := by
  have ht := hw (star v) (fun j => star (V j)) (fun j => (hv j).star)
  have hm : (∫ ω, g ω * (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      inner ℂ v g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with ω hω
    change (star v : Lp ℂ 2 (reducedLaw Q)) ω = star (v ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def]
  have he : (∫ ω, principal Q G (fun j => star (V j)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, star (V j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr fun j => Lp.coeFn_star (V j)] with ω hω
    unfold principal
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have hj : (star (V j) : Lp ℂ 2 (reducedLaw Q)) ω = star (V j ω) := hω j
    rw [hj]
    ring
  simpa only [hm, he, zero_mul, add_zero] using ht

private theorem energy_conj_symm {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    star (∫ ω, ∑ j, ∑ k, star (H j ω) * (ω.1 0 j k : ℂ) * G k ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, star (G j ω) * (ω.1 0 j k : ℂ) * H k ω ∂reducedLaw Q := by
  change starRingEnd ℂ _ = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
  have hs (j k : Fin d) : ω.1 0 j k = ω.1 0 k j :=
    congrArg (fun M : Mat d => M k j) (hω 0).1
  have hc (r : ℝ) : star (r : ℂ) = (r : ℂ) := Complex.conj_ofReal r
  simp only [map_sum, map_mul, starRingEnd_apply, star_star, hc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hs k j]
  ring

/-- The full actual unforced generator graph is symmetric for the complex L2 pairing. -/
theorem IsComplexGeneratorPair.unforced_inner_symm {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g h k : Lp ℂ 2 (reducedLaw Q)}
    (hf : IsComplexGeneratorPair Q i 0 f g) (hh : IsComplexGeneratorPair Q i 0 h k) :
    inner ℂ g h = inner ℂ f k := by
  obtain ⟨G, hG, hwG⟩ := hf
  obtain ⟨H, hH, hwH⟩ := hh
  have h1 := generator_inner_eq_energy Q i g G hwG h H hH
  have h2 := generator_inner_eq_energy Q i k H hwH f G hG
  rw [← inner_conj_symm (𝕜 := ℂ) g h, h1, h2, map_mul]
  rw [starRingEnd_apply, starRingEnd_apply, energy_conj_symm]
  congr 1
  norm_num [star_neg, star_div₀]

private def resolventValue {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) := (exists_unforced_complexGenerator_resolvent Q i s hs rhs).choose

private theorem resolventValue_spec {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i 0 (resolventValue Q i s hs rhs)
      ((s : ℂ) • resolventValue Q i s hs rhs - rhs) :=
  (exists_unforced_complexGenerator_resolvent Q i s hs rhs).choose_spec.1

private def resolventLinearMap {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) :
    Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) where
  toFun := resolventValue Q i s hs
  map_add' := by
    intro f g
    apply IsComplexGeneratorPair.unforced_resolvent_unique hs (resolventValue_spec Q i s hs (f+g))
    convert (resolventValue_spec Q i s hs f).add (resolventValue_spec Q i s hs g) using 1
    module
  map_smul' := by
    intro c f
    change resolventValue Q i s hs (c • f) = c • resolventValue Q i s hs f
    apply IsComplexGeneratorPair.unforced_resolvent_unique hs (resolventValue_spec Q i s hs (c • f))
    convert (resolventValue_spec Q i s hs f).smul c using 1
    module

private theorem resolventValue_bound {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ‖resolventValue Q i s hs rhs‖ ≤ s⁻¹ * ‖rhs‖ := by
  have hb := (exists_unforced_complexGenerator_resolvent Q i s hs rhs).choose_spec.2
  change s * ‖resolventValue Q i s hs rhs‖ ≤ ‖rhs‖ at hb
  exact (le_div_iff₀ hs).mpr (by simpa only [mul_comm] using hb) |>.trans_eq (div_eq_inv_mul _ _)

/-- The positive resolvent of the actual full unforced complex generator graph. -/
def unforcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (resolventLinearMap Q i s hs).mkContinuous s⁻¹ (resolventValue_bound Q i s hs)

/-- The bundled resolvent solves the full weak generator equation. -/
theorem unforcedComplexResolvent_spec {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i 0 (unforcedComplexResolvent Q i s hs rhs)
      ((s : ℂ) • unforcedComplexResolvent Q i s hs rhs - rhs) :=
  resolventValue_spec Q i s hs rhs

/-- The positive unforced resolvent has the sharp L2 operator norm bound. -/
theorem norm_unforcedComplexResolvent_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) :
    ‖unforcedComplexResolvent Q i s hs‖ ≤ s⁻¹ :=
  (unforcedComplexResolvent Q i s hs).opNorm_le_bound (inv_pos.mpr hs).le
    (resolventValue_bound Q i s hs)

/-- The positive unforced resolvent is injective. -/
theorem unforcedComplexResolvent_injective {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) :
    Function.Injective (unforcedComplexResolvent Q i s hs) := by
  intro f g he
  have hf := unforcedComplexResolvent_spec Q i s hs f
  have hg := unforcedComplexResolvent_spec Q i s hs g
  rw [he] at hf
  have hh := hf.unique hg
  exact neg_injective (add_left_cancel (by simpa only [sub_eq_add_neg] using hh))

/-- Symmetry of the full unforced graph makes its positive resolvent self-adjoint. -/
theorem unforcedComplexResolvent_isSymmetric {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) :
    (unforcedComplexResolvent Q i s hs).IsSymmetric := by
  intro f g
  have hh := (unforcedComplexResolvent_spec Q i s hs f).unforced_inner_symm
    (unforcedComplexResolvent_spec Q i s hs g)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal] at hh
  linear_combination hh

/-- Every positive unforced resolvent has dense range in the actual complex L2 space. -/
theorem denseRange_unforcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) :
    DenseRange (unforcedComplexResolvent Q i s hs) := by
  let R := unforcedComplexResolvent Q i s hs
  have hR : R.IsSymmetric := unforcedComplexResolvent_isSymmetric Q i s hs
  have hk : LinearMap.ker R.toLinearMap = ⊥ :=
    (LinearMap.ker_eq_bot (f := R.toLinearMap)).mpr
      (unforcedComplexResolvent_injective Q i s hs)
  have hr : (LinearMap.range R.toLinearMap).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, R.orthogonal_range, hR.clm_adjoint_eq, hk]
  change Dense (LinearMap.range R.toLinearMap : Set (Lp ℂ 2 (reducedLaw Q)))
  rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe, hr]
  rfl

/-- The actual generator graph is exactly the graph recovered from one positive resolvent. -/
theorem isComplexGeneratorPair_iff_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexGeneratorPair Q i 0 f g ↔
      unforcedComplexResolvent Q i s hs ((s : ℂ) • f - g) = f := by
  constructor
  · intro h
    apply IsComplexGeneratorPair.unforced_resolvent_unique hs
      (unforcedComplexResolvent_spec Q i s hs _)
    simpa only [sub_sub_cancel] using h
  · intro h
    have hp := unforcedComplexResolvent_spec Q i s hs ((s : ℂ) • f - g)
    rw [h, sub_sub_cancel] at hp
    exact hp

/-- Positive resolvents of the actual unforced graph satisfy the resolvent identity. -/
theorem unforcedComplexResolvent_identity {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    unforcedComplexResolvent Q i s hs f - unforcedComplexResolvent Q i t ht f =
      ((t - s : ℝ) : ℂ) • unforcedComplexResolvent Q i s hs
        (unforcedComplexResolvent Q i t ht f) := by
  have he := (isComplexGeneratorPair_iff_resolvent Q i s hs _ _).mp
    (unforcedComplexResolvent_spec Q i t ht f)
  have ha : (s : ℂ) • unforcedComplexResolvent Q i t ht f -
      ((t : ℂ) • unforcedComplexResolvent Q i t ht f - f) =
      f + ((s - t : ℝ) : ℂ) • unforcedComplexResolvent Q i t ht f := by
    push_cast
    module
  rw [ha, map_add, map_smul] at he
  conv_lhs => rw [← he]
  push_cast
  module

/-- The actual unforced generator graph is closed in the product L2 topology. -/
theorem isClosed_unforced_complexGenerator_graph {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    IsClosed {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexGeneratorPair Q i 0 p.1 p.2} := by
  have he : {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexGeneratorPair Q i 0 p.1 p.2} =
      {p | unforcedComplexResolvent Q i 1 zero_lt_one (p.1 - p.2) = p.1} := by
    ext p
    simpa only [Set.mem_setOf_eq, Complex.ofReal_one, one_smul] using
      isComplexGeneratorPair_iff_resolvent Q i 1 zero_lt_one p.1 p.2
  rw [he]
  exact isClosed_eq ((unforcedComplexResolvent Q i 1 zero_lt_one).continuous.comp
    (continuous_fst.sub continuous_snd)) continuous_fst

/-- The domain of the full actual unforced generator graph is dense. -/
theorem dense_unforced_complexGenerator_domain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    Dense {f : Lp ℂ 2 (reducedLaw Q) | ∃ g, IsComplexGeneratorPair Q i 0 f g} := by
  apply (denseRange_unforcedComplexResolvent Q i 1 zero_lt_one).mono
  rintro f ⟨rhs, rfl⟩
  exact ⟨_, unforcedComplexResolvent_spec Q i 1 zero_lt_one rhs⟩

end EinsteinFull
