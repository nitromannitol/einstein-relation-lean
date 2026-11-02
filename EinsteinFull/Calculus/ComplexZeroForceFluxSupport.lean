import EinsteinFull.Calculus.ComplexMildDuhamelSupport
import EinsteinFull.Work.W2.FiniteCorrectorGraphSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import Mathlib.Analysis.Convex.Integral

/-!
# Actual zero-force weak flux cancellation

The closed strong horizontal derivative graph commutes with finite-measure
Bochner integration. Its application to the actual positive-time gradient orbit
identifies the full primitive gradient, including the integrable singularity at
zero. Actual coefficient multiplication then commutes with that time integral.

The full generator graph and the actual drift integration-by-parts identity give
the source cancellation on every horizontal H1 test. Its literal coefficient flux
is L2 and can be centered under the reduced law. Spatial localization and
finite-range averaging are separate obligations.
-/

open MeasureTheory Filter Set
open scoped NNReal Topology BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Finite-measure Bochner integration preserves the actual closed horizontal derivative graph. -/
theorem HasComplexHorizontalDerivative.integral_of_ae
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    {hQ : IsStationary Q} {i : Fin d} {f g : α → Lp ℂ 2 Q}
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ᵐ x ∂μ, HasComplexHorizontalDerivative Q hQ i (f x) (g x)) :
    HasComplexHorizontalDerivative Q hQ i (∫ x, f x ∂μ) (∫ x, g x ∂μ) := by
  let S : Submodule ℝ (Lp ℂ 2 Q × Lp ℂ 2 Q) :=
    { carrier := {p | HasComplexHorizontalDerivative Q hQ i p.1 p.2}
      zero_mem' := HasComplexHorizontalDerivative.zero Q hQ i
      add_mem' := fun hx hy => hx.add hy
      smul_mem' := fun c x hx => by
        simpa only [Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd,
          RCLike.real_smul_eq_coe_smul (K := ℂ)] using! hx.smul (c : ℂ) }
  by_cases hμ : μ = 0
  · subst μ
    simpa using HasComplexHorizontalDerivative.zero Q hQ i
  letI : NeZero μ := ⟨hμ⟩
  have ha := S.convex.average_mem (isClosed_complexHorizontalDerivative_graph Q hQ i)
    hfg (hf.prodMk hg)
  have hm := S.smul_mem (μ.real univ) ha
  rw [measure_smul_average, integral_pair hf hg] at hm
  exact hm

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- The full Euclidean gradient orbit is Bochner integrable down to time zero. -/
theorem IsComplexEnvironmentSemigroup.integrableOn_gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IntegrableOn (hP.gradientOrbit f) (Icc (0 : ℝ) (t : ℝ)) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  apply ((intervalIntegrable_inv_sqrt t.property).const_mul
    (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)).1.mono'
  · exact ((hP.continuousOn_gradientOrbit f).mono (fun _ hs => hs.1)).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact hP.norm_gradientOrbit_le f hs.1 hs.2

/-- The actual primitive's strong gradient is the time integral of its actual gradients. -/
theorem IsComplexEnvironmentSemigroup.integral_orbit_gradient
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal f)
      (fun k => (∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) := by
  intro k
  let E := PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))
  let T : E →L[ℂ] Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ k
  have hf := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)
  have hg := hP.integrableOn_gradientOrbit f t
  have hkg := T.integrable_comp hg
  have ha : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k
        (P s.toNNReal f) (T (hP.gradientOrbit f s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with s hs hs0
    exact hP.gradientOrbit_spec f (lt_of_le_of_ne hs.1 (Ne.symm hs0)) k
  have hi := HasComplexHorizontalDerivative.integral_of_ae hf hkg ha
  rw [T.integral_comp_comm hg] at hi
  exact hi

/-- Actual coefficient multiplication commutes with the integrated gradient orbit. -/
theorem IsComplexEnvironmentSemigroup.integral_coefficient_gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (j k : Fin d) :
    (∫ s in Icc (0 : ℝ) (t : ℝ),
      complexCoefficientMul Q j k (hP.gradientOrbit f s k)) =
      complexCoefficientMul Q j k ((∫ s in Icc (0 : ℝ) (t : ℝ),
        hP.gradientOrbit f s) k) := by
  let T := (complexCoefficientMul Q j k).comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k)
  exact T.integral_comp_comm (hP.integrableOn_gradientOrbit f t)

/-- Every row of the actual time-dependent coefficient flux is Bochner integrable. -/
theorem IsComplexEnvironmentSemigroup.integrableOn_flux_gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (j : Fin d) :
    IntegrableOn (fun s : ℝ => ∑ k,
      complexCoefficientMul Q j k (hP.gradientOrbit f s k)) (Icc (0 : ℝ) (t : ℝ)) := by
  apply integrable_finset_sum
  intro k _
  exact ((complexCoefficientMul Q j k).comp
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k)).integrable_comp
      (hP.integrableOn_gradientOrbit f t)

/-- The time integral of each actual coefficient-flux row is its multiplier on the primitive gradient. -/
theorem IsComplexEnvironmentSemigroup.integral_flux_gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (j : Fin d) :
    (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ k,
      complexCoefficientMul Q j k (hP.gradientOrbit f s k)) =
      ∑ k, complexCoefficientMul Q j k
        ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) := by
  have hk (k : Fin d) : IntegrableOn (fun s : ℝ =>
      complexCoefficientMul Q j k (hP.gradientOrbit f s k)) (Icc (0 : ℝ) (t : ℝ)) :=
    ((complexCoefficientMul Q j k).comp
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) k)).integrable_comp
        (hP.integrableOn_gradientOrbit f t)
  rw [integral_finset_sum _ (fun k _ => hk k)]
  simp_rw [hP.integral_coefficient_gradientOrbit f t j]

private theorem coeFn_sum_L2 {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {ι : Type*} (s : Finset ι) (f : ι → Lp ℂ 2 μ) :
    (∑ k ∈ s, f k : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∑ k ∈ s, f k ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using! Lp.coeFn_zero ℂ 2 μ
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (f k) (∑ b ∈ s, f b), ih] with ω ha hb
    simpa only [Pi.add_apply, hb] using ha

/-- The actual Bochner flux integral has the literal anisotropic pointwise representative. -/
theorem IsComplexEnvironmentSemigroup.integral_flux_gradientOrbit_coe
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (j : Fin d) :
    (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ k,
      complexCoefficientMul Q j k (hP.gradientOrbit f s k) : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∑ k, (ω.1 0 j k : ℂ) *
        ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k) ω := by
  rw [hP.integral_flux_gradientOrbit f t j]
  filter_upwards [coeFn_sum_L2 (reducedLaw Q) Finset.univ
      (fun k => complexCoefficientMul Q j k
        ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k)),
    ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k
      ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit f s) k))] with ω hs hc
  simpa only [hc] using hs

private theorem principal_integrable (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * H j ω)
      (reducedLaw Q) := by
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

private theorem column_integrable (Q : EnvironmentLaw d Λ₀ r₀)
    (j : Fin d) (V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∑ k, (ω.1 0 k j : ℂ) * V k ω) (reducedLaw Q) := by
  apply integrable_finset_sum
  intro k _
  simpa only [Pi.mul_apply, mul_comm] using!
    ((Lp.memLp (V k)).integrable (by norm_num)).mul_of_top_left
      (memLp_reduced_coefficient_complex Q k j)

/-- Zero force gives the actual weak divergence cancellation on every horizontal H1 test. -/
theorem IsComplexEnvironmentSemigroup.unforced_orbit_weak_flux
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, P t (β j) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ a,
        ((ω.1 0 a j : ℂ) + ∑ b, (ω.1 0 a b : ℂ) *
          ((∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j) s) b) ω) * V a ω
          ∂reducedLaw Q := by
  let G := ∫ s in Icc (0 : ℝ) (t : ℝ), hP.gradientOrbit (β j) s
  obtain ⟨H, hH, hw⟩ := hP.integral_orbit_graph (β j) t
  have hHG : H = fun k => G k := hH.unique (hP.integral_orbit_gradient (β j) t)
  rw [hHG] at hw
  have he := hw v V hV
  simp only [zero_mul, add_zero] at he
  have hsub : (∫ ω, (P t (β j) - β j) ω * v ω ∂reducedLaw Q) =
      (∫ ω, P t (β j) ω * v ω ∂reducedLaw Q) -
        ∫ ω, β j ω * v ω ∂reducedLaw Q := by
    have ha : Integrable (fun ω => P t (β j) ω * v ω) (reducedLaw Q) :=
      (Lp.memLp (P t (β j))).integrable_mul (Lp.memLp v)
    have hb : Integrable (fun ω => β j ω * v ω) (reducedLaw Q) :=
      (Lp.memLp (β j)).integrable_mul (Lp.memLp v)
    rw [← integral_sub ha hb]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (P t (β j)) (β j)] with ω hω
    simp only [hω, Pi.sub_apply, sub_mul]
  rw [hsub, hβ.integral_mul j v V hV] at he
  have hsum : (∫ ω, ∑ a,
        ((ω.1 0 a j : ℂ) + ∑ b, (ω.1 0 a b : ℂ) * G b ω) * V a ω ∂reducedLaw Q) =
      (∫ ω, ∑ a, (ω.1 0 a j : ℂ) * V a ω ∂reducedLaw Q) +
        ∫ ω, ∑ a, ∑ b, (ω.1 0 a b : ℂ) * G b ω * V a ω ∂reducedLaw Q := by
    rw [← integral_add (column_integrable Q j V) (principal_integrable Q G V)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => by
      simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul])
  change _ = -(1 / 2 : ℂ) * ∫ ω, ∑ a,
    ((ω.1 0 a j : ℂ) + ∑ b, (ω.1 0 a b : ℂ) * G b ω) * V a ω ∂reducedLaw Q
  rw [hsum]
  linear_combination he

/-- The source cancellation identity uses the actual time-integrated coefficient flux, including t=0. -/
theorem IsComplexEnvironmentSemigroup.unforced_orbit_weak_flux_timeIntegral
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, P t (β j) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ a,
        ((ω.1 0 a j : ℂ) + (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ b,
          complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b) :
            Lp ℂ 2 (reducedLaw Q)) ω) * V a ω
            ∂reducedLaw Q := by
  rw [hP.unforced_orbit_weak_flux hβ t j v V hV]
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun a =>
    hP.integral_flux_gradientOrbit_coe (β j) t a] with ω hω
  simp only [hω]

/-- Centering an actual L2 flux leaves its weak divergence unchanged. -/
theorem integral_centered_flux_mul_gradient
    (F : Fin d → FieldPair d → ℂ) (hF : ∀ a, MemLp (F a) 2 (reducedLaw Q))
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, ∑ a, (F a ω - ∫ η, F a η ∂reducedLaw Q) * V a ω ∂reducedLaw Q) =
      ∫ ω, ∑ a, F a ω * V a ω ∂reducedLaw Q := by
  have hp (a : Fin d) : Integrable (fun ω => F a ω * V a ω) (reducedLaw Q) :=
    (hF a).integrable_mul (Lp.memLp (V a))
  have hc (a : Fin d) : Integrable (fun ω =>
      (∫ η, F a η ∂reducedLaw Q) * V a ω) (reducedLaw Q) :=
    ((Lp.memLp (V a)).integrable (by norm_num)).const_mul _
  have hs (a : Fin d) : Integrable (fun ω =>
      (F a ω - ∫ η, F a η ∂reducedLaw Q) * V a ω) (reducedLaw Q) := by
    simpa only [sub_mul, Pi.sub_apply] using! (hp a).sub (hc a)
  rw [integral_finset_sum _ (fun a _ => hs a), integral_finset_sum _ (fun a _ => hp a)]
  apply Finset.sum_congr rfl
  intro a _
  simp_rw [sub_mul]
  rw [integral_sub (hp a) (hc a), integral_const_mul, (hV a).integral_eq_zero, mul_zero,
    sub_zero]

/-- The source bracket is genuinely L2 and may be centered under the actual reduced law. -/
theorem IsComplexEnvironmentSemigroup.unforced_orbit_weak_centered_flux
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    let F : Fin d → FieldPair d → ℂ := fun a ω => (ω.1 0 a j : ℂ) +
      (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ b,
        complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b) : Lp ℂ 2 (reducedLaw Q)) ω
    (∀ a, MemLp (F a) 2 (reducedLaw Q)) ∧
    (∫ ω, P t (β j) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ a,
        (F a ω - ∫ η, F a η ∂reducedLaw Q) * V a ω ∂reducedLaw Q := by
  intro F
  have hF (a : Fin d) : MemLp (F a) 2 (reducedLaw Q) :=
    ((memLp_reduced_coefficient_complex Q a j).mono_exponent le_top).add
      (Lp.memLp (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ b,
        complexCoefficientMul Q a b (hP.gradientOrbit (β j) s b)))
  refine ⟨hF, ?_⟩
  rw [integral_centered_flux_mul_gradient F hF v V hV]
  exact hP.unforced_orbit_weak_flux_timeIntegral hβ t j v V hV

/-- The internally constructed zero-force evolution satisfies the actual source weak flux identity. -/
theorem forcedComplexEvolution_unforced_weak_flux
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} (i : Fin d)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (t : ℝ≥0) (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q))
    (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, forcedComplexEvolution Q i 0 t (β j) ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ a,
        ((ω.1 0 a j : ℂ) + (∫ s in Icc (0 : ℝ) (t : ℝ), ∑ b,
          complexCoefficientMul Q a b
            ((isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0).gradientOrbit
              (β j) s b) : Lp ℂ 2 (reducedLaw Q)) ω) * V a ω ∂reducedLaw Q :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0).unforced_orbit_weak_flux_timeIntegral
    hβ t j v V hV

end EinsteinFull
