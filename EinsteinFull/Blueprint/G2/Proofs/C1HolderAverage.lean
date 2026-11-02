import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior
import EinsteinFull.Calculus.C1HolderComparisonSupport
import EinsteinFull.Blueprint.Foundation.Proofs.W1CenteredSource
import EinsteinFull.Calculus.ComplexCenteredWeakTimeSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory Set
open scoped Topology NNReal
open scoped ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open PDE (euclideanBall euclideanClosedBall isCompact_euclideanClosedBall
  euclideanBall_subset_euclideanClosedBall isOpen_euclideanBall)

private theorem holder_norm_le_euclideanNorm {d : ℕ} (x : Vec d) :
    ‖x‖ ≤ euclideanNorm x := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  apply Real.abs_le_sqrt
  unfold euclideanSq dot
  rw [sq]
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)

private theorem holder_cylinder_finite {d : ℕ} (τ r : ℝ) (x : Vec d) :
    IsFiniteMeasure (volume.restrict
      (Set.Ioo (τ - r ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < r})) := by
  apply isFiniteMeasure_restrict.mpr
  have hsub : (Set.Ioo (τ - r ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < r}) ⊆
      Set.Icc (τ - r ^ 2) τ ×ˢ Metric.closedBall x |r| := by
    intro z hz
    refine ⟨⟨hz.1.1.le, hz.1.2.le⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (holder_norm_le_euclideanNorm (z.2 - x)).trans
      (hz.2.le.trans (le_abs_self r))
  exact ((measure_mono hsub).trans_lt
    ((isCompact_Icc.prod (isCompact_closedBall x |r|)).measure_lt_top)).ne

/-- The exact real interior dependency gives the same structural exponent
and constant for a complex weak caloric function. The complex distributional
equations include absolute convergence of their test integrals. Projection
commutes with these integrals; the coefficient field, spatial norm and
normalized cylinders are unchanged.
This does not construct a comparison with prescribed boundary values. -/
theorem holder_average_complex_unforced_interior
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α₀ C : ℝ, 0 < α₀ ∧ α₀ < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (τ : ℝ) (x : Vec d) (r : ℝ), 0 < r →
      let cyl := fun ρ : ℝ =>
        Set.Ioo (τ - ρ ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < ρ}
      ∀ (v : ℝ × Vec d → ℂ) (g : Fin d → ℝ × Vec d → ℂ),
        MemLp v 2 (volume.restrict (cyl r)) →
        (∀ j, MemLp (g j) 2 (volume.restrict (cyl r))) →
        (∀ φ : ℝ × Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ cyl r →
          ∀ j : Fin d,
            IntegrableOn (fun z => fderiv ℝ φ z (0, Pi.single j 1) • v z) (cyl r) ∧
            IntegrableOn (fun z => φ z • g j z) (cyl r) ∧
            (∫ z in cyl r, fderiv ℝ φ z (0, Pi.single j 1) • v z) =
              -(∫ z in cyl r, φ z • g j z)) →
        (∀ φ : ℝ × Vec d → ℝ,
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ cyl r →
          IntegrableOn (fun z => fderiv ℝ φ z (1, 0) • v z) (cyl r) ∧
          IntegrableOn (fun z => ∑ j : Fin d, ∑ k : Fin d,
            (ω.1 z.2 j k * fderiv ℝ φ z (0, Pi.single j 1)) • g k z) (cyl r) ∧
          (∫ z in cyl r, fderiv ℝ φ z (1, 0) • v z) =
            (1 / 2 : ℝ) • (∫ z in cyl r, ∑ j : Fin d, ∑ k : Fin d,
              (ω.1 z.2 j k * fderiv ℝ φ z (0, Pi.single j 1)) • g k z)) →
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
          Real.sqrt (⨍ z in cyl (θ * r),
            ‖v z - (⨍ w in cyl (θ * r), v w)‖ ^ 2) ≤
          C * θ ^ α₀ * Real.sqrt (⨍ z in cyl r,
            ‖v z - (⨍ w in cyl r, v w)‖ ^ 2) := by
  obtain ⟨α₀, C, hα₀, hα₁, hC, hall⟩ := hinterior d hd D
  refine ⟨α₀, C, hα₀, hα₁, hC, ?_⟩
  intro Q hQ
  filter_upwards [hall Q hQ] with ω hω
  intro τ x r hr
  dsimp only
  intro v g hv hg hgrad heq θ hθ hθhalf
  let cyl := fun ρ : ℝ =>
    Set.Ioo (τ - ρ ^ 2) τ ×ˢ {y : Vec d | euclideanNorm (y - x) < ρ}
  have hgradL (L : ℂ →L[ℝ] ℝ) (φ : ℝ × Vec d → ℝ)
      (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ cyl r) (j : Fin d) :
      (∫ z in cyl r, L (v z) * fderiv ℝ φ z (0, Pi.single j 1)) =
        -(∫ z in cyl r, L (g j z) * φ z) := by
    obtain ⟨hleft, hright, hweak⟩ := hgrad φ hφ hc hs j
    have h := congrArg L hweak
    rw [map_neg, ← L.integral_comp_comm hleft, ← L.integral_comp_comm hright] at h
    simpa only [map_smul, smul_eq_mul, mul_comm] using h
  have heqL (L : ℂ →L[ℝ] ℝ) (φ : ℝ × Vec d → ℝ)
      (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
      (hs : tsupport φ ⊆ cyl r) :
      (∫ z in cyl r, L (v z) * fderiv ℝ φ z (1, 0)) =
        (1 / 2 : ℝ) * (∫ z in cyl r,
          ∑ j : Fin d, (∑ k : Fin d, ω.1 z.2 j k * L (g k z)) *
            fderiv ℝ φ z (0, Pi.single j 1)) := by
    obtain ⟨hleft, hright, hweak⟩ := heq φ hφ hc hs
    have h := congrArg L hweak
    rw [map_smul, ← L.integral_comp_comm hleft, ← L.integral_comp_comm hright] at h
    simpa only [map_sum, map_smul, smul_eq_mul, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hre := hω τ x r hr (fun z => (v z).re) (fun j z => (g j z).re)
    hv.re (fun j => (hg j).re) (hgradL Complex.reCLM) (heqL Complex.reCLM) θ hθ hθhalf
  have him := hω τ x r hr (fun z => (v z).im) (fun j z => (g j z).im)
    hv.im (fun j => (hg j).im) (hgradL Complex.imCLM) (heqL Complex.imCLM) θ hθ hθhalf
  have hθrr : θ * r ≤ r :=
    mul_le_of_le_one_left hr.le (hθhalf.trans (by norm_num))
  have hsq : (θ * r) ^ 2 ≤ r ^ 2 :=
    (sq_le_sq₀ (mul_pos hθ hr).le hr.le).2 hθrr
  have hsub : cyl (θ * r) ⊆ cyl r := by
    intro z hz
    refine ⟨⟨?_, hz.1.2⟩, hz.2.trans_le hθrr⟩
    linarith only [hz.1.1, hsq]
  have := holder_cylinder_finite τ (θ * r) x
  have := holder_cylinder_finite τ r x
  exact holder_complex_contraction
    (hv.mono_measure (Measure.restrict_mono_set volume hsub)) hv
    (C * θ ^ α₀) (mul_nonneg (by linarith only [hC]) (Real.rpow_nonneg hθ.le _))
    hre him

/-- The literal centering-source primitive cancels the scalar source in
all endpoint-vanishing temporal tests, including windows beginning at zero. -/
theorem holder_average_source_primitive_pairing
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t : ℝ} (ht : 0 < t) (n : ℕ) (η η' : ℝ → ℝ)
    (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (hzero : η 0 = 0) (hn : η n = 0) :
    (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
      (∫ v in (t / 4)..s, hP.centeringSource f v)) =
      -(∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * hP.centeringSource f s) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hs : IntervalIntegrable (hP.centeringSource f) volume 0 (n : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (Nat.cast_nonneg n)).2
      (by simpa only [NNReal.coe_natCast] using hP.integrableOn_centeringSource f (n : ℝ≥0))
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := (n : ℝ))
    (u := fun s => (η s : ℂ))
    (v := fun s => ∫ v in (t / 4)..s, hP.centeringSource f v)
    (u' := fun s => (η' s : ℂ)) (v' := hP.centeringSource f)
    (Complex.continuous_ofReal.comp hηc).continuousOn
    (continuous_centered_source_primitive hP f (t / 4)).continuousOn
    (fun s _ => (hη s).ofReal_comp)
    (fun s hs => hasDerivAt_centered_source_primitive hP f ht
      (by simpa only [min_eq_left (Nat.cast_nonneg n)] using hs.1))
    ((Complex.continuous_ofReal.comp hη').intervalIntegrable 0 n) hs
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    intervalIntegral.integral_of_le (Nat.cast_nonneg n),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hb
  simp only [hzero, hn, Complex.ofReal_zero, zero_mul, sub_zero, zero_sub] at hb
  exact neg_eq_iff_eq_neg.mp hb.symm

/-- The actual corrected orbit has one environment event for every smooth
separated test. Its scalar centering source cancels exactly; the original
coefficient field, complex force and orbit gradient remain in the equation. -/
theorem holder_average_corrected_joint_weak_time_equation
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t : ℝ} (ht : 0 < t) :
    ∃ (W : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable W ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
          ∫ v in (t / 4)..s, hP.centeringSource f v)) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ,
        (∀ K : Set (Vec d), IsCompact K →
          Integrable (fun p : Vec d × ℝ => W (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Set.Icc (0 : ℝ) (n : ℝ)))) ∧
          ∀ j, Integrable (fun p : Vec d × ℝ => V j (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Set.Icc (0 : ℝ) (n : ℝ))))) ∧
        ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
          η 0 = 0 → η n = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
            W (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            (∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V k (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) -
          ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) *
            (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V j (s, translate x ω))) *
              (φ x : ℂ)) := by
  obtain ⟨U, V, hU, hV, heU, heV, he⟩ :=
    hP.exists_centered_joint_weak_time_equation_all_tests f
  let m : ℝ → ℂ := fun s => ∫ v in (t / 4)..s, hP.centeringSource f v
  have hmc : Continuous m := continuous_centered_source_primitive hP f (t / 4)
  let W : ℝ × FieldPair d → ℂ := fun p => U p + m p.1
  refine ⟨W, V, hU.add (hmc.measurable.comp measurable_fst), hV, ?_, heV, ?_⟩
  · intro s
    filter_upwards [heU s] with ω hω
    exact congrArg (fun z => z + m s) hω
  filter_upwards [he] with ω hω
  intro n
  have hm : IntegrableOn m (Set.Icc (0 : ℝ) (n : ℝ)) volume :=
    hmc.continuousOn.integrableOn_compact isCompact_Icc
  have hmF (K : Set (Vec d)) (hK : IsCompact K) :
      Integrable (fun p : Vec d × ℝ => m p.2)
        ((volume.restrict K).prod (volume.restrict (Set.Icc (0 : ℝ) (n : ℝ)))) := by
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    simpa only [one_mul] using (integrable_const (1 : ℂ) (μ := volume.restrict K)).mul_prod hm
  refine ⟨fun K hK => ⟨((hω n).1 K hK).1.add (hmF K hK), ((hω n).1 K hK).2⟩, ?_⟩
  intro η η' hη hη' hzero hn φ hφ hφc
  let g : ℝ → Set.Icc (0 : ℝ) (n : ℝ) := Set.projIcc (0 : ℝ) (n : ℝ) (by positivity)
  let w : ℝ → ℝ := fun s => η' (g s)
  have hwc : Continuous w := (hη'.comp continuous_subtype_val).comp continuous_projIcc
  obtain ⟨C, hC⟩ := (isCompact_Icc.image hη').isBounded.exists_norm_le
  have hwb (s : ℝ) : ‖w s‖ ≤ C := hC _ ⟨g s, (g s).property, rfl⟩
  have hwint (F : ℝ → ℂ) :
      (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (w s : ℂ) * F s) =
        ∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) * F s := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro s hs
    simp only [w, g, Set.projIcc_of_mem (by positivity : (0 : ℝ) ≤ n) hs]
  have hadd := holderComparison_integral_add_temporal_constant
    (fun K hK => ((hω n).1 K hK).1) hm
    (Complex.continuous_ofReal.comp hφ.continuous)
    (hφc.comp_left (g := Complex.ofReal) rfl) hwc.measurable hwb
  change (∫ x, (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (w s : ℂ) *
      (U (s, translate x ω) + m s)) * (φ x : ℂ)) = _ at hadd
  simp_rw [hwint] at hadd
  change (∫ x, (∫ s in Set.Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
    (U (s, translate x ω) + m s)) * (φ x : ℂ)) = _
  simp only [Function.comp_apply] at hadd
  rw [hadd, (hω n).2 η η' hη hη' hzero hn φ hφ hφc,
    holder_average_source_primitive_pairing hP f ht n η η' hη hη' hzero hn]
  ring

/-- The actual corrected centered orbit satisfies its joint spacetime weak
identity on one environment event, for every smooth compact interior test.
Its coefficients and gradient are the original physical representatives. -/
theorem holder_average_corrected_joint_weak_equation
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t : ℝ} (ht : 0 < t) :
    ∃ (W : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable W ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
          ∫ v in (t / 4)..s, hP.centeringSource f v)) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ,
      ∀ (φ : Vec d × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (n : ℝ) →
      let ν := (volume.restrict (Prod.fst '' tsupport φ)).prod
        (volume.restrict (Set.Icc (0 : ℝ) (n : ℝ)))
      (∫ z, W (z.2, translate z.1 ω) * (fderiv ℝ φ z (0, 1) : ℂ) ∂ν) =
        (∑ j : Fin d, ∫ z, ((1 / 2 : ℂ) *
          (∑ k : Fin d, (ω.1 z.1 j k : ℂ) * V k (z.2, translate z.1 ω))) *
            (fderiv ℝ φ z (unitVector j, 0) : ℂ) ∂ν) +
        ∫ z, (-ζ * (∑ j : Fin d, (ω.1 z.1 j i : ℂ) *
          V j (z.2, translate z.1 ω))) * (φ z : ℂ) ∂ν := by
  obtain ⟨W, V, hW, hV, heW, heV, he⟩ :=
    holder_average_corrected_joint_weak_time_equation hP f ht
  refine ⟨W, V, hW, hV, heW, heV, ?_⟩
  filter_upwards [he] with ω hω
  intro n φ hφ hc hs
  let K : Set (Vec d) := Prod.fst '' tsupport φ
  have hK : IsCompact K := hc.image continuous_fst
  let ν := (volume.restrict K).prod (volume.restrict (Set.Icc (0 : ℝ) (n : ℝ)))
  let u : Vec d × ℝ → ℂ := fun z => W (z.2, translate z.1 ω)
  let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
  let a : Fin d → Fin d → Vec d → ℂ := fun j k x => (ω.1 x j k : ℂ)
  have ha (j k : Fin d) : Continuous (a j k) :=
    Complex.continuous_ofReal.comp
      ((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous))
  have hu : Integrable u ν := ((hω n).1 K hK).1
  have hD (j : Fin d) : Integrable (D j) ν := ((hω n).1 K hK).2 j
  have hrow (j k : Fin d) : Integrable (fun z => a j k z.1 * D k z) ν := by
    simpa only [Function.comp_apply, mul_comm] using
      holderComparison_local_mul_integrable hK (hD k) ((ha j k).comp continuous_fst)
  let G : Fin d → Vec d × ℝ → ℂ := fun j z => ∑ k, a j k z.1 * D k z
  let S : Vec d × ℝ → ℂ := fun z => ∑ j, a j i z.1 * D j z
  have hG j : Integrable (G j) ν := integrable_finsetSum _ (fun k _ => hrow j k)
  have hS : Integrable S ν := integrable_finsetSum _ (fun j _ => by
    simpa only [Function.comp_apply, mul_comm] using
      holderComparison_local_mul_integrable hK (hD j) ((ha j i).comp continuous_fst))
  obtain ⟨δ, hδ, hmargin⟩ := holderComparison_temporal_support_margin hc hs
  apply holderComparison_joint_weak_equation_of_separated hu (hS.const_mul (-ζ))
    (fun j => (hG j).const_mul (1 / 2 : ℂ)) hδ (fun j => unitVector j) hφ hc hmargin
  intro η η' hη hη' hη0 hηn ψ hψ hψc hψs
  have hηc : Continuous η := continuous_iff_continuousAt.mpr
    (fun r => (hη r).continuousAt)
  have hψC : Continuous (fun x => (ψ x : ℂ)) := Complex.continuous_ofReal.comp hψ.continuous
  have hcast (g : Vec d → ℝ) : tsupport (fun x => (g x : ℂ)) = tsupport g := by
    unfold tsupport
    congr 1
    ext x
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  have hψCs : tsupport (fun x => (ψ x : ℂ)) ⊆ K := (hcast ψ).subset.trans hψs
  have hd (j : Fin d) : Continuous (fun x => (coordinateDerivative j ψ x : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const).continuous
  have hds (j : Fin d) : tsupport (fun x => (coordinateDerivative j ψ x : ℂ)) ⊆ K := by
    rw [hcast]
    exact (tsupport_fderiv_apply_subset ℝ (unitVector j)).trans hψs
  have hm j := holderComparison_local_flux_pairing hK hD (a j) (ha j) (hd j) (hds j) hηc
  have hmi j := holderComparison_local_flux_pairing_integrable hK hD
    (a j) (ha j) (hd j) (hds j) hηc
  have hsource := holderComparison_local_flux_pairing hK hD
    (fun j => a j i) (fun j => ha j i) hψC hψCs hηc
  have htime := holderComparison_local_separated_pairing hK hu hψC hψCs hη'
  have heq := (hω n).2 η η' hη hη' hη0 hηn ψ hψ hψc
  change (∫ x, (∫ r in Set.Icc (0 : ℝ) (n : ℝ), (η' r : ℂ) * u (x, r)) *
      (ψ x : ℂ)) = (1 / 2 : ℂ) *
      (∫ x, ∑ j, (∑ k, a j k x * (∫ r in Set.Icc (0 : ℝ) (n : ℝ),
        (η r : ℂ) * D k (x, r))) * (coordinateDerivative j ψ x : ℂ)) -
      ζ * (∫ x, (∑ j, a j i x * (∫ r in Set.Icc (0 : ℝ) (n : ℝ),
        (η r : ℂ) * D j (x, r))) * (ψ x : ℂ)) at heq
  rw [htime, integral_finsetSum _ (fun j _ => hmi j)] at heq
  simp_rw [hm] at heq
  rw [hsource] at heq
  simp only [Complex.ofReal_mul, coordinateDerivative, mul_assoc, integral_const_mul,
    ← Finset.mul_sum, neg_mul, integral_neg, sub_eq_add_neg] at heq ⊢
  exact heq

/-- Local L2 bounds hold for the very representatives used in the corrected
joint equation. The time interval stays away from the initial gradient trace. -/
theorem holder_average_corrected_representatives_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun z : Vec d × ℝ => W (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc b c))) ∧
      ∀ j, MemLp (fun z : Vec d × ℝ => V j (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
  let := reducedLaw_probability Q
  let w : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s =>
    centeredComplexLp Q (P s.toNNReal f) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
  have hwc : Continuous w := by
    have hu : Continuous (fun s : ℝ => centeredComplexLp Q (P s.toNNReal f)) := by
      simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
        (centeredComplexLpCLM Q).continuous.comp
          ((hP.2.2.1 f).comp continuous_real_toNNReal)
    exact hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
      (continuous_centered_source_primitive hP f (t / 4)))
  have hew (s : ℝ) : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s := by
    filter_upwards [heW s,
      Lp.coeFn_add (centeredComplexLp Q (P s.toNNReal f))
        (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)]
      with ω hω hadd hconst
    exact hω.trans (by simp only [w, hadd, Pi.add_apply, hconst, Function.const_apply])
  have hiW : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) :=
    (hwc.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlW := holderComparison_ae_locally_memLp_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hW
    (holderComparison_integrable_sq_joint_l2_representative
      hiW hW hew)
  have hlV (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun z : Vec d × ℝ => V j (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit f s) j) (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit f)
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit f s) j‖ ^ 2) (Icc b c) :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le hb hs.1)).integrableOn_compact
        isCompact_Icc
    exact holderComparison_ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hV j) (holderComparison_integrable_sq_joint_l2_representative hi (hV j) (heV j))
  filter_upwards [hlW, ae_all_iff.mpr hlV] with ω hωW hωV
  exact fun K hK => ⟨hωW K hK, fun j => hωV j K hK⟩

/-- The temporal scalar correction does not change the actual horizontal
gradient of the centered orbit at positive time. -/
theorem holder_average_corrected_gradient_spec
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {s : ℝ} (hs : 0 < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P s.toNNReal f) +
        Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v))
      (hP.gradientOrbit f s) := by
  let := reducedLaw_probability Q
  have hG := hP.centered_gradientOrbit_spec f hs
  have hc := hasComplexHorizontalGradient_const (reducedLaw Q)
    (reducedLaw_stationary Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
  intro j
  simpa only [add_zero] using (hG j).add (hc j)

/-- At each positive time the joint representatives in the physical equation
have their actual spatial weak gradient, on one event for all spatial tests. -/
theorem holder_average_corrected_representatives_spatial
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {s : ℝ} (hs : 0 < s)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d, ∀ ψ : Vec d → ℝ, IsSpatialTest univ ψ →
      (∫ x, W (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
        -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)) := by
  let := reducedLaw_probability Q
  let w : Lp ℂ 2 (reducedLaw Q) := centeredComplexLp Q (P s.toNNReal f) +
    Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
  have hew : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w := by
    filter_upwards [heW,
      Lp.coeFn_add (centeredComplexLp Q (P s.toNNReal f))
        (Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)),
      Lp.coeFn_const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)]
      with ω hω hadd hconst
    exact hω.trans (by simp only [w, hadd, Pi.add_apply, hconst, Function.const_apply])
  have hw := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable w).measurable hew
  have hv j := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hV j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable ((hP.gradientOrbit f s) j)).measurable (heV j)
  filter_upwards [(holder_average_corrected_gradient_spec hP f t hs).ae_spatial_test,
    hw, ae_all_iff.mpr hv] with ω hω hw hv
  intro j ψ hψ
  calc
    _ = ∫ x, w (translate x ω) * (coordinateDerivative j ψ x : ℂ) :=
      integral_congr_ae (hw.mono fun x hx => congrArg (fun q : ℂ => q * _) hx)
    _ = -(∫ x, (hP.gradientOrbit f s) j (translate x ω) * (ψ x : ℂ)) := hω j ψ hψ
    _ = _ := congrArg Neg.neg (integral_congr_ae
      ((hv j).mono fun x hx => congrArg (fun q : ℂ => q * _) hx.symm))


/-- The same physical representatives have local L2 sections on one time event
before every compact spatial region and every gradient component. -/
theorem holder_average_corrected_representatives_memLp_slices
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => W (s, translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => V j (s, translate x ω)) 2 (volume.restrict K) := by
  filter_upwards [holder_average_corrected_representatives_memLp hP f t hb hW hV heW heV]
    with ω hω
  have hshift : Measurable (fun z : Vec d × ℝ => (z.2, translate z.1 ω)) :=
    measurable_snd.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_fst.prodMk measurable_const))
  have hw := holderComparison_ae_slices_memLp (hW.comp hshift)
    (fun K hK => (hω K hK).1)
  have hv j := holderComparison_ae_slices_memLp ((hV j).comp hshift)
    (fun K hK => (hω K hK).2 j)
  filter_upwards [hw, ae_all_iff.mpr hv] with s hsW hsV
  exact fun K hK => ⟨hsW K hK, fun j => hsV j K hK⟩


/-- Fubini puts the actual spatial weak-gradient identity on an environment
first event for each fixed spatial test, throughout a positive time slab. -/
theorem holder_average_corrected_representatives_spatial_fixed_test
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    (j : Fin d) {ψ : Vec d → ℝ} (hψ : IsSpatialTest univ ψ) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (∫ x, W (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
        -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)) := by
  let := reducedLaw_probability Q
  have hshift : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      (q.1.1, translate q.2 q.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  have hd : Continuous (coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const).continuous
  have hA := holderComparison_measurable_spatial_pairing (hW.comp hshift) hd.measurable
  have hB := (holderComparison_measurable_spatial_pairing (hV j |>.comp hshift)
    hψ.1.continuous.measurable).neg
  apply (Measure.ae_ae_comm (p := fun s ω =>
    (∫ x, W (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
      -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)))
    (measurableSet_eq_fun hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact (holder_average_corrected_representatives_spatial hP f t
    (lt_of_lt_of_le hb hs.1) hW hV (heW s) (fun k => heV k s)).mono
      fun ω hω => hω j ψ hψ


/-- On a positive slab, one environment event precedes the time event and
all coordinates and spatial tests for the actual corrected orbit gradient. -/
theorem holder_average_corrected_representatives_spatial_common
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
 :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      ∀ j : Fin d, ∀ ψ : Vec d → ℝ, IsSpatialTest univ ψ →
        (∫ x, W (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
          -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)) := by
  let := reducedLaw_probability Q
  let ν := volume.restrict (Icc b c)
  let u : (FieldPair d × ℝ) × Vec d → ℂ := fun q => W (q.1.2, translate q.2 q.1.1)
  let g : Fin d → (FieldPair d × ℝ) × Vec d → ℂ :=
    fun j q => V j (q.1.2, translate q.2 q.1.1)
  have hshift : Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      (q.1.2, translate q.2 q.1.1)) :=
    (measurable_snd.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hmu : Measurable u := hW.comp hshift
  have hmg j : Measurable (g j) := (hV j).comp hshift
  have hslices := holder_average_corrected_representatives_memLp_slices
    hP f t (b := b) (c := c) hb hW hV heW heV
  have hlu : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (z, x)) 2 (volume.restrict K) := by
    apply (Measure.ae_prod_iff_ae_ae
      (holderComparison_measurableSet_locally_memLp hmu)).mpr
    exact hslices.mono fun ω hω => hω.mono fun s hs => fun K hK => (hs K hK).1
  have hlg j : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => g j (z, x)) 2 (volume.restrict K) := by
    apply (Measure.ae_prod_iff_ae_ae
      (holderComparison_measurableSet_locally_memLp (hmg j))).mpr
    exact hslices.mono fun ω hω => hω.mono fun s hs => fun K hK => (hs K hK).2 j
  have hloc : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (z, x)) 2 (volume.restrict K) ∧
      ∀ j, MemLp (fun x => g j (z, x)) 2 (volume.restrict K) := by
    filter_upwards [hlu, ae_all_iff.mpr hlg] with z hzU hzG
    exact fun K hK => ⟨hzU K hK, fun j => hzG j K hK⟩
  apply Measure.ae_ae_of_ae_prod (μ := reducedLaw Q) (ν := ν)
    (p := fun z : FieldPair d × ℝ => ∀ j : Fin d, ∀ ψ : Vec d → ℝ,
      IsSpatialTest univ ψ →
        (∫ x, u (z, x) * (coordinateDerivative j ψ x : ℂ)) =
          -(∫ x, g j (z, x) * (ψ x : ℂ)))
  apply holderComparison_ae_all_spatial_gradients ((reducedLaw Q).prod ν)
    (fun z x => u (z, x)) (fun z j x => g j (z, x)) hloc
  intro j ψ hψ
  have hd : Continuous (coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const).continuous
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (holderComparison_measurable_spatial_pairing hmu hd.measurable)
    (holderComparison_measurable_spatial_pairing (hmg j)
      hψ.1.continuous.measurable).neg)).mpr
  exact holder_average_corrected_representatives_spatial_fixed_test hP f t hb
    hW hV heW heV j hψ


/-- The actual representatives satisfy the smooth joint weak-gradient
equation on one environment event before every compact joint test. -/
theorem holder_average_corrected_representatives_joint_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
 :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ j : Fin d,
        (∫ z, W (z.2, translate z.1 ω) *
          (fderiv ℝ φ z (unitVector j, 0) : ℂ)
          ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
            (volume.restrict (Icc b c)))) =
          -(∫ z, V j (z.2, translate z.1 ω) * (φ z : ℂ)
            ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
              (volume.restrict (Icc b c)))) := by
  filter_upwards [holder_average_corrected_representatives_memLp hP f t
      (b := b) (c := c) hb hW hV heW heV,
    holder_average_corrected_representatives_spatial_common hP f t
      (b := b) (c := c) hb hW hV heW heV] with ω hL hG
  intro φ hφ hc j
  apply holderComparison_joint_weak_gradient_of_spatial_slices
    (u := fun z => W (z.2, translate z.1 ω))
    (v := fun z => V j (z.2, translate z.1 ω))
    (j := j) (hφ := hφ) (hc := hc)
  · intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (hL K hK).1.integrable (by norm_num)
  · intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((hL K hK).2 j).integrable (by norm_num)
  · exact hG.mono fun s hs => hs j

/-- The actual corrected representatives satisfy every compact C1 spatial
gradient test of the local physical comparison problem. -/
theorem holder_average_corrected_comparison_spatial_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ) {b c : ℝ} (hb : 0 < b)
    {W : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : ∀ j, Measurable (V j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
        ∫ v in (t / 4)..s, hP.centeringSource f v))
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) b c, ∀ j : Fin d,
        (∫ z in euclideanBall x₀ r ×ˢ Ioo b c,
          W (z.2, translate z.1 ω) *
            (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (unitVector j, 0) : ℂ)) =
          -(∫ z in euclideanBall x₀ r ×ˢ Ioo b c,
            V j (z.2, translate z.1 ω) * ((φ.val : Vec d × ℝ → ℝ) z : ℂ)) := by
  filter_upwards [holder_average_corrected_representatives_memLp hP f t
      (b := b) (c := c) hb hW hV heW heV,
    holder_average_corrected_representatives_joint_gradient hP f t
      (b := b) (c := c) hb hW hV heW heV] with ω hL hG
  let K := euclideanClosedBall x₀ r
  have hK : IsCompact K := isCompact_euclideanClosedBall x₀ hr.le
  have hlocal {w : Vec d × ℝ → ℂ}
      (hw : MemLp w 2 ((volume.restrict K).prod (volume.restrict (Icc b c)))) :
      IntegrableOn w (euclideanBall x₀ r ×ˢ Ioo b c) := by
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    have hi := hw.integrable (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hi
    exact hi.mono_measure (Measure.restrict_mono
      (Set.prod_mono (euclideanBall_subset_euclideanClosedBall x₀ r) Ioo_subset_Icc_self)
      le_rfl)
  intro φ j
  exact holderComparison_joint_weak_gradient_C1 (isOpen_euclideanBall x₀ r)
    (hlocal (hL K hK).1) (hlocal ((hL K hK).2 j)) j
    (fun ψ hψ hcψ _ => hG ψ hψ hcψ j)
    φ.val.property.1 φ.val.property.2.1 φ.property

/-- The actual corrected orbit admits jointly measurable local L2
representatives satisfying the compact C1 comparison equations. -/
theorem holder_average_corrected_local_comparison_equations
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t : ℝ} (ht : 0 < t) {b c : ℝ} (hb : 0 < b)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    ∃ (W : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable W ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
        (fun ω => centeredComplexLp Q (P s.toNNReal f) ω +
          ∫ v in (t / 4)..s, hP.centeringSource f v)) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        let Ω := euclideanBall x₀ r ×ˢ Ioo b c
        let u : Vec d × ℝ → ℂ := fun z => W (z.2, translate z.1 ω)
        let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
        let G : Fin d → Vec d × ℝ → ℂ := fun j z =>
          (1 / 2 : ℂ) * ∑ k, (ω.1 z.1 j k : ℂ) * D k z
        let S : Vec d × ℝ → ℂ := fun z => -ζ * ∑ j, (ω.1 z.1 j i : ℂ) * D j z
        MemLp u 2 (volume.restrict Ω) ∧
        (∀ j, MemLp (D j) 2 (volume.restrict Ω)) ∧
        (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) b c, ∀ j,
          (∫ z in Ω, u z *
            (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (unitVector j, 0) : ℂ)) =
            -(∫ z in Ω, D j z * ((φ.val : Vec d × ℝ → ℝ) z : ℂ))) ∧
        (∀ φ : holderComparisonTestSpace d (euclideanBall x₀ r) b c,
          (∫ z in Ω, u z * (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (0, 1) : ℂ)) =
            (∑ j, ∫ z in Ω, G j z *
              (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (unitVector j, 0) : ℂ)) +
            ∫ z in Ω, S z * ((φ.val : Vec d × ℝ → ℝ) z : ℂ)) := by
  obtain ⟨W, V, hW, hV, heW, heV, hE⟩ := holder_average_corrected_joint_weak_equation hP f ht
  refine ⟨W, V, hW, hV, heW, heV, ?_⟩
  obtain ⟨N, hcN⟩ := exists_nat_gt c
  filter_upwards [hE, holder_average_corrected_representatives_memLp hP f t
      (b := b) (c := c) hb hW hV heW heV,
    holder_average_corrected_comparison_spatial_gradient hP f t
      (b := b) (c := c) hb hW hV heW heV hr] with ω hEω hL hgrad
  let Ω := euclideanBall x₀ r ×ˢ Ioo b c
  let K := euclideanClosedBall x₀ r
  have hK : IsCompact K := isCompact_euclideanClosedBall x₀ hr.le
  let u : Vec d × ℝ → ℂ := fun z => W (z.2, translate z.1 ω)
  let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
  let G : Fin d → Vec d × ℝ → ℂ := fun j z =>
    (1 / 2 : ℂ) * ∑ k, (ω.1 z.1 j k : ℂ) * D k z
  let S : Vec d × ℝ → ℂ := fun z => -ζ * ∑ j, (ω.1 z.1 j i : ℂ) * D j z
  have hu : MemLp u 2 (volume.restrict Ω) :=
    holderComparison_memLp_restrict_cylinder (euclideanBall_subset_euclideanClosedBall x₀ r)
      (hL K hK).1
  have hD j : MemLp (D j) 2 (volume.restrict Ω) :=
    holderComparison_memLp_restrict_cylinder (euclideanBall_subset_euclideanClosedBall x₀ r)
      ((hL K hK).2 j)
  refine ⟨hu, hD, hgrad, ?_⟩
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hrestrict {w : Vec d × ℝ → ℂ}
      (hw : Integrable w ((volume.restrict K).prod (volume.restrict (Icc b c)))) :
      IntegrableOn w Ω := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hw
    exact hw.mono_measure (Measure.restrict_mono
      (Set.prod_mono (euclideanBall_subset_euclideanClosedBall x₀ r) Ioo_subset_Icc_self)
      le_rfl)
  have hu1 : IntegrableOn u Ω := hrestrict ((hL K hK).1.integrable (by norm_num))
  have hDK j : Integrable (D j)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    ((hL K hK).2 j).integrable (by norm_num)
  have ha j k : Continuous (fun z : Vec d × ℝ => (ω.1 z.1 j k : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)).comp continuous_fst)
  have hrow j k : IntegrableOn (fun z => (ω.1 z.1 j k : ℂ) * D k z) Ω := by
    simpa only [mul_comm] using hrestrict
      (holderComparison_local_mul_integrable hK (hDK k) (ha j k))
  have hG j : IntegrableOn (G j) Ω :=
    (integrable_finsetSum _ (fun k _ => hrow j k)).const_mul (1 / 2 : ℂ)
  have hsrow j : IntegrableOn (fun z => (ω.1 z.1 j i : ℂ) * D j z) Ω := by
    simpa only [mul_comm] using hrestrict
      (holderComparison_local_mul_integrable hK (hDK j) (ha j i))
  have hS : IntegrableOn S Ω :=
    (integrable_finsetSum _ (fun j _ => hsrow j)).const_mul (-ζ)
  intro φ
  apply holderComparison_joint_weak_heat_C1 (isOpen_euclideanBall x₀ r) hu1 hG hS
    _ φ.val.property.1 φ.val.property.2.1 φ.property
  intro ψ hψ hcψ hsψ
  have he := hEω N ψ hψ hcψ (fun z hz =>
    ⟨Set.mem_univ _, hb.trans (hsψ hz).2.1, (hsψ hz).2.2.trans hcN⟩)
  change (∫ z, u z * (fderiv ℝ ψ z (0, 1) : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod (volume.restrict (Icc 0 (N : ℝ))))) =
    (∑ j, ∫ z, G j z * (fderiv ℝ ψ z (unitVector j, 0) : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod (volume.restrict (Icc 0 (N : ℝ))))) +
    ∫ z, S z * (ψ z : ℂ)
      ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod (volume.restrict (Icc 0 (N : ℝ)))) at he
  simp_rw [holderComparison_joint_derivative_pairing_localize hsψ hb.le hcN.le,
    holderComparison_joint_value_pairing_localize hsψ hb.le hcN.le] at he
  exact he

end EinsteinFull.Blueprint
