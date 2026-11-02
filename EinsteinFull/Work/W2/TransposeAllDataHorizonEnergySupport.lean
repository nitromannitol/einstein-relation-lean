import EinsteinFull.Work.W2.TransposeDomainHorizonEnergySupport
import EinsteinFull.Work.W2.TransposeGeneratorCoreApproximationSupport
import EinsteinFull.Work.W2.TransposeGeneratorClosedGraphSupport
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# All-data finite-horizon transpose gradient energy

Normalized actual transpose resolvents approximate arbitrary complex L² data.
The domain energy estimate on differences makes their Euclidean gradients
Cauchy in time L². Subsequence convergence and the closed horizontal graph
identify the limit. Uniqueness specifies one gradient orbit before choosing
any horizon; its value at nonpositive times is stipulated to be zero.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
open Classical
namespace EinsteinFull
open EinsteinRelation

private instance gradient_secondCountableEither {d : ℕ} (Q : Measure (FieldPair d)) :
    SecondCountableTopologyEither ℝ (PiLp 2 (fun _ : Fin d => Lp ℂ 2 Q)) :=
  secondCountableTopologyEither_of_left _ _

private theorem timeL2_norm_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure ℝ} (F : Lp E 2 μ) :
    ‖F‖ ^ 2 = ∫ s, ‖F s‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

private theorem timeL2_norm_sub_sq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {μ : Measure ℝ} {F G : ℝ → E}
    (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    ‖hF.toLp F - hG.toLp G‖ ^ 2 = ∫ s, ‖F s - G s‖ ^ 2 ∂μ := by
  rw [timeL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hF.toLp F) (hG.toLp G), hF.coeFn_toLp, hG.coeFn_toLp]
    with s hs hf hg
  simp only [hs, Pi.sub_apply, hf, hg]

private theorem cauchySeq_timeL2_of_energy {E V : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup V]
    {u : ℕ → E} {v : ℕ → V} (K : ℝ) (hu : CauchySeq u)
    (hb : ∀ n m, ‖v n - v m‖ ^ 2 ≤ K * ‖u n - u m‖ ^ 2) : CauchySeq v := by
  have hn : Tendsto (fun p : ℕ × ℕ => ‖u p.1 - u p.2‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, Prod.map] using!
      tendsto_uniformity_iff_dist_tendsto_zero.mp (cauchySeq_iff_tendsto.mp hu)
  have he : Tendsto (fun p : ℕ × ℕ => K * ‖u p.1 - u p.2‖ ^ 2) atTop (𝓝 0) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero] using! (hn.pow 2).const_mul K
  have hsq := squeeze_zero (fun p : ℕ × ℕ => sq_nonneg ‖v p.1 - v p.2‖)
    (fun p => hb p.1 p.2) he
  have hl := hsq.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hl
  exact cauchySeq_iff_tendsto.mpr
    (tendsto_uniformity_iff_dist_tendsto_zero.mpr (by simpa only [dist_eq_norm, Prod.map] using! hl))

private theorem ae_gradient_of_timeL2_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {μ : Measure ℝ}
    {T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {u : ℕ → Lp ℂ 2 (reducedLaw Q)} {f : Lp ℂ 2 (reducedLaw Q)}
    {V : ℕ → Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) 2 μ}
    {H : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) 2 μ}
    (hu : Tendsto u atTop (𝓝 f)) (hV : Tendsto V atTop (𝓝 H))
    (hg : ∀ n, ∀ᵐ s ∂μ, HasComplexHorizontalGradient (reducedLaw Q)
      (reducedLaw_stationary Q) (T s.toNNReal (u n)) (V n s)) :
    ∀ᵐ s ∂μ, HasComplexHorizontalGradient (reducedLaw Q)
      (reducedLaw_stationary Q) (T s.toNNReal f) (H s) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hV).exists_seq_tendsto_ae
  filter_upwards [hae, ae_all_iff.mpr hg] with s hs hr
  have hval := ((T s.toNNReal).continuous.tendsto f).comp (hu.comp hns.tendsto_atTop)
  have hgrad := (PiLp.continuous_ofLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))).tendsto
    (H s) |>.comp hs
  exact complexHorizontalGradient_of_tendsto
    (p := fun n => (T s.toNNReal (u (ns n)), (V (ns n) s).ofLp))
    (q := (T s.toNNReal f, (H s).ofLp))
    (Eventually.of_forall (fun n => hr (ns n)))
    (hval.prodMk_nhds hgrad)

/-- Every datum admits an actual Euclidean gradient in time L² on a fixed horizon.
No generator-domain or positive-time regularization premise is imposed. -/
theorem IsComplexTransposeSemigroup.exists_timeL2_gradient_horizon
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ∃ H : Lp (PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))) 2
        (volume.restrict (Ioc (0 : ℝ) t)),
      (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) t),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal f) (H s)) ∧
      ‖H‖ ^ 2 ≤ 2 * (Real.exp (2 * Λ₀) * Λ₀) *
        Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ ^ 2 := by
  let μ := volume.restrict (Ioc (0 : ℝ) t)
  let K := 2 * (Real.exp (2 * Λ₀) * Λ₀) *
    Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ))
  have hK : 0 ≤ K := by
    have hΛ := zero_le_one.trans Q.ellipticity_parameter
    dsimp only [K]
    positivity
  let u := fun n => complexTransposeResolventApproximation Q i ζ n f
  have hgraph := fun n => complexTransposeResolventApproximation_graph Q i ζ n f
  have hex := fun n => hT.exists_gradient_orbit_energy hP (hgraph n)
  choose G hGc hG hGe using hex
  have hM (n : ℕ) : MemLp (G n) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm
      ((hGc n).aestronglyMeasurable.restrict)).mpr
    exact ((hGc n).norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  let V := fun n => (hM n).toLp (G n)
  have hv (n m : ℕ) : ‖V n - V m‖ ^ 2 ≤ K * ‖u n - u m‖ ^ 2 := by
    rw [timeL2_norm_sub_sq]
    dsimp only [μ]
    rw [← intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property]
    have hD (s : ℝ) : HasComplexHorizontalGradient (reducedLaw Q)
        (reducedLaw_stationary Q) (T s.toNNReal (u n - u m)) (G n s - G m s) := by
      rw [map_sub]
      exact (hG n s).sub (hG m s)
    exact hT.integral_gradient_le hP ((hgraph n).sub (hgraph m)) hD t
  have hu : Tendsto u atTop (𝓝 f) := tendsto_complexTransposeResolventApproximation Q i ζ f
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_timeL2_of_energy K hu.cauchySeq hv)
  have hbound (n : ℕ) : ‖V n‖ ^ 2 ≤ K * ‖f‖ ^ 2 := by
    rw [timeL2_norm_sq]
    have heq : (∫ s, ‖V n s‖ ^ 2 ∂μ) = ∫ s, ‖G n s‖ ^ 2 ∂μ :=
      integral_congr_ae ((hM n).coeFn_toLp.mono (fun _ hs => congrArg (fun x => ‖x‖ ^ 2) hs))
    rw [heq]
    dsimp only [μ]
    rw [← intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property]
    exact (hGe n t).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_complexTransposeResolventApproximation_apply_le Q i ζ n f) 2) hK)
  refine ⟨H, ?_, le_of_tendsto (hH.norm.pow 2) (Eventually.of_forall hbound)⟩
  apply ae_gradient_of_timeL2_tendsto hu hH
  intro n
  filter_upwards [(hM n).coeFn_toLp] with s hs
  rw [hs]
  exact hG n s

/-- The unique actual orbit gradient wherever it exists at positive time,
and zero elsewhere. The definition is independent of every finite horizon. -/
def complexTransposeGradientOrbit {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) :
    PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  if h : 0 < s ∧ ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) G then h.2.choose else 0

/-- At positive times admitting a gradient, the horizon-independent choice is that gradient. -/
theorem complexTransposeGradientOrbit_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀}
    {T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {f : Lp ℂ 2 (reducedLaw Q)} {s : ℝ} (hs : 0 < s)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (T s.toNNReal f) G) : complexTransposeGradientOrbit Q T f s = G := by
  have he : 0 < s ∧ ∃ H : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) H := ⟨hs, G, hG⟩
  rw [complexTransposeGradientOrbit, dif_pos he]
  exact WithLp.ofLp_injective 2 (he.2.choose_spec.unique hG)

/-- The prescribed endpoint value entails no H¹ assertion about the initial datum. -/
theorem complexTransposeGradientOrbit_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (f : Lp ℂ 2 (reducedLaw Q)) : complexTransposeGradientOrbit Q T f 0 = 0 := by
  simp only [complexTransposeGradientOrbit, lt_self_iff_false, false_and, dif_neg, not_false_eq_true]

/-- The same orbit on every horizon is a genuine time-L² gradient of the
actual transpose evolution, with structural energy controlled by the datum. -/
theorem IsComplexTransposeSemigroup.gradientOrbit_horizon_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    MemLp (complexTransposeGradientOrbit Q T f) 2 (volume.restrict (Ioc (0 : ℝ) t)) ∧
      (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) t),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal f) (complexTransposeGradientOrbit Q T f s)) ∧
      (∫ s in (0 : ℝ)..(t : ℝ), ‖complexTransposeGradientOrbit Q T f s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨H, hH, hb⟩ := hT.exists_timeL2_gradient_horizon hP f t
  have heq : complexTransposeGradientOrbit Q T f =ᵐ[volume.restrict (Ioc (0 : ℝ) t)] H := by
    filter_upwards [hH, ae_restrict_mem measurableSet_Ioc] with s hs ht
    exact complexTransposeGradientOrbit_eq ht.1 hs
  refine ⟨(Lp.memLp H).ae_eq heq.symm, ?_, ?_⟩
  · filter_upwards [hH, heq] with s hs he
    rwa [he]
  · rw [intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property]
    have hi := integral_congr_ae (heq.mono (fun _ hs => congrArg (fun x => ‖x‖ ^ 2) hs))
    rw [hi, ← timeL2_norm_sq]
    exact hb

/-- The squared gradient is integrable on a closed horizon, including the
stipulated endpoint value. -/
theorem IsComplexTransposeSemigroup.integrableOn_Icc_sq_gradientOrbit
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => ‖complexTransposeGradientOrbit Q T f s‖ ^ 2) (Icc 0 t) ∧
      (∫ s in Icc 0 t, ‖complexTransposeGradientOrbit Q T f s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (2 * complexForceShift d Λ₀ ζ * t) * ‖f‖ ^ 2 := by
  obtain ⟨hm, _, hb⟩ := hT.gradientOrbit_horizon_energy hP f ⟨t, ht⟩
  constructor
  · rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  · rw [integral_Icc_eq_integral_Ioc]
    change (∫ s in (0 : ℝ)..t, ‖complexTransposeGradientOrbit Q T f s‖ ^ 2) ≤ _ at hb
    rwa [intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := t) ht] at hb

/-- Linearity holds almost everywhere on each horizon, without claiming
pointwise H¹ regularization at exceptional times. -/
theorem IsComplexTransposeSemigroup.gradientOrbit_sub_ae
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f g : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    complexTransposeGradientOrbit Q T (f - g) =ᵐ[volume.restrict (Ioc (0 : ℝ) t)]
      fun s => complexTransposeGradientOrbit Q T f s - complexTransposeGradientOrbit Q T g s := by
  filter_upwards [(hT.gradientOrbit_horizon_energy hP f t).2.1,
    (hT.gradientOrbit_horizon_energy hP g t).2.1,
    ae_restrict_mem measurableSet_Ioc] with s hf hg hs
  apply complexTransposeGradientOrbit_eq hs.1
  rw [map_sub]
  exact hf.sub hg

/-- The domain approximations converge to the specified all-data gradient in
actual Euclidean-valued time L² on the entire finite horizon. -/
theorem IsComplexTransposeSemigroup.tendsto_Lp_gradientOrbit_resolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    Tendsto (fun n => (hT.gradientOrbit_horizon_energy hP
      (complexTransposeResolventApproximation Q i ζ n f) t).1.toLp
        (complexTransposeGradientOrbit Q T (complexTransposeResolventApproximation Q i ζ n f)))
      atTop (𝓝 ((hT.gradientOrbit_horizon_energy hP f t).1.toLp
        (complexTransposeGradientOrbit Q T f))) := by
  let u := fun n => complexTransposeResolventApproximation Q i ζ n f
  let V := fun n => (hT.gradientOrbit_horizon_energy hP (u n) t).1.toLp
    (complexTransposeGradientOrbit Q T (u n))
  let H := (hT.gradientOrbit_horizon_energy hP f t).1.toLp (complexTransposeGradientOrbit Q T f)
  have hb (n : ℕ) : ‖V n - H‖ ^ 2 ≤
      (2 * (Real.exp (2 * Λ₀) * Λ₀) * Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ))) *
        ‖u n - f‖ ^ 2 := by
    rw [timeL2_norm_sub_sq]
    have heq := integral_congr_ae ((hT.gradientOrbit_sub_ae hP (u n) f t).symm.mono
      (fun _ hs => congrArg (fun x => ‖x‖ ^ 2) hs))
    rw [heq, ← intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property]
    exact (hT.gradientOrbit_horizon_energy hP (u n - f) t).2.2
  have hl := ((tendsto_complexTransposeResolventApproximation Q i ζ f).sub_const f).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hl
  have hc := hl.const_mul
    (2 * (Real.exp (2 * Λ₀) * Λ₀) * Real.exp (2 * complexForceShift d Λ₀ ζ * (t : ℝ)))
  simp only [mul_zero] at hc
  have he := squeeze_zero (fun n => sq_nonneg ‖V n - H‖) hb hc
  have hn := he.sqrt
  simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- A structural constant chosen before the law, force, datum and horizon. -/
def transposeGradientEnergyConstant (d : ℕ) (Λ₀ : ℝ) : ℝ :=
  1 + 2 * |Real.exp (2 * Λ₀) * Λ₀| +
    2 * |Real.exp (2 * Λ₀) * Λ₀| * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2

/-- The structural constant is positive even for parameters without an environment law. -/
theorem transposeGradientEnergyConstant_pos (d : ℕ) (Λ₀ : ℝ) :
    0 < transposeGradientEnergyConstant d Λ₀ := by
  unfold transposeGradientEnergyConstant
  positivity

/-- All-data true-transpose energy with a structural constant and a single
orbit chosen before every horizon. The gradient relation is almost everywhere
in time; positive-time pointwise H¹ smoothing is not asserted. -/
theorem transpose_fullHorizon_gradient_energy (d : ℕ) (Λ₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
      ∀ f : Lp ℂ 2 (reducedLaw Q),
      ∃ G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
        G 0 = 0 ∧ ∀ t : ℝ≥0,
        MemLp G 2 (volume.restrict (Ioc (0 : ℝ) t)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) t),
          HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
            (T s.toNNReal f) (G s)) ∧
        (∫ s in (0 : ℝ)..(t : ℝ), ‖G s‖ ^ 2) ≤
          C * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖ ^ 2 := by
  refine ⟨transposeGradientEnergyConstant d Λ₀, transposeGradientEnergyConstant_pos d Λ₀, ?_⟩
  intro r₀ Q i ζ P T hP hT f
  refine ⟨complexTransposeGradientOrbit Q T f, complexTransposeGradientOrbit_zero Q T f, ?_⟩
  intro t
  obtain ⟨hm, hg, hb⟩ := hT.gradientOrbit_horizon_energy hP f t
  refine ⟨hm, hg, hb.trans ?_⟩
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  have hC₁ : 2 * K ≤ transposeGradientEnergyConstant d Λ₀ := by
    change 2 * K ≤ 1 + 2 * |K| + 2 * |K| * ((d : ℝ) * K) ^ 2
    rw [abs_of_nonneg hK]
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
      (sq_nonneg ((d : ℝ) * K))]
  have hC₂ : 2 * K * ((d : ℝ) * K) ^ 2 ≤ transposeGradientEnergyConstant d Λ₀ := by
    change 2 * K * ((d : ℝ) * K) ^ 2 ≤ 1 + 2 * |K| + 2 * |K| * ((d : ℝ) * K) ^ 2
    rw [abs_of_nonneg hK]
    linarith
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖f‖)
  apply mul_le_mul hC₁ _ (Real.exp_pos _).le (transposeGradientEnergyConstant_pos d Λ₀).le
  apply Real.exp_le_exp.mpr
  calc
    2 * complexForceShift d Λ₀ ζ * (t : ℝ) =
        (2 * K * ((d : ℝ) * K) ^ 2) * ‖ζ‖ ^ 2 * (t : ℝ) := by
      unfold complexForceShift K
      ring
    _ ≤ transposeGradientEnergyConstant d Λ₀ * ‖ζ‖ ^ 2 * (t : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ (sq_nonneg ‖ζ‖)) t.property

end EinsteinFull
