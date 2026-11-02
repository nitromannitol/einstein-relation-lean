import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof
import EinsteinFull.Calculus.ComplexSemigroupEnergySupport

/-!
# Time averages of the actual stationary complex evolution

Finite-time averages of arbitrary L2 data belong to the full generator domain.
Their generator output is the actual orbit increment. These averages therefore
have physical local H1 realizations. This is a time-averaged spatial result;
joint space-time representatives and the physical divergence equation are
separate obligations.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The vector fundamental theorem on the complete stationary generator domain. -/
theorem IsComplexEnvironmentSemigroup.w6_integral_generator_orbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) :
    (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal g) = P t f - f := by
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.2.2.1 g).comp continuous_real_toNNReal
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (NNReal.coe_nonneg t)
    hu.continuousOn (fun s hs =>
      (hP.hasDerivWithinAt_orbit hfg s hs.1.le).mono Ioi_subset_Ici_self)
    (hv.intervalIntegrable 0 t)
  simpa only [Real.toNNReal_zero, Real.toNNReal_coe, hP.1,
    ContinuousLinearMap.id_apply] using! he

/-- Continuous integration preserves the actual full generator graph, by its
proved resolvent characterization. No physical PDE is required here. -/
theorem complexGeneratorPair_intervalIntegral_on
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)} (hu : Continuous u) (hv : Continuous v)
    (a b : ℝ) (hgraph : ∀ s ∈ uIcc a b, IsComplexGeneratorPair Q i ζ (u s) (v s)) :
    IsComplexGeneratorPair Q i ζ (∫ s in a..b, u s) (∫ s in a..b, v s) := by
  let c := complexForceShift d Λ₀ ζ + 1
  have hc : complexForceShift d Λ₀ ζ < c := lt_add_one _
  let R := forcedComplexResolvent Q i ζ c hc
  apply (isComplexGeneratorPair_iff_forced_resolvent Q i ζ c hc _ _).mpr
  rw [← intervalIntegral.integral_smul, ← intervalIntegral.integral_sub
    ((hu.fun_const_smul (c : ℂ)).intervalIntegrable (μ := volume) a b) (hv.intervalIntegrable (μ := volume) a b)]
  change R (∫ s in a..b, (c : ℂ) • u s - v s) = _
  rw [← R.intervalIntegral_comp_comm
    (((hu.fun_const_smul (c : ℂ)).fun_sub hv).intervalIntegrable (μ := volume) a b)]
  apply intervalIntegral.integral_congr
  intro s hs
  exact (isComplexGeneratorPair_iff_forced_resolvent Q i ζ c hc _ _).mp (hgraph s hs)

/-- The global continuous-graph version of interval integration. -/
theorem complexGeneratorPair_intervalIntegral
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)} (hu : Continuous u) (hv : Continuous v)
    (hgraph : ∀ s, IsComplexGeneratorPair Q i ζ (u s) (v s)) (a b : ℝ) :
    IsComplexGeneratorPair Q i ζ (∫ s in a..b, u s) (∫ s in a..b, v s) :=
  complexGeneratorPair_intervalIntegral_on hu hv a b (fun s _ => hgraph s)

/-- Integration of the true orbit is bounded in the initial datum. -/
def IsComplexEnvironmentSemigroup.timeIntegralCLM
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  let A : Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) :=
    { toFun := fun f => ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f
      map_add' := fun f g => by
        simp only [map_add]
        exact intervalIntegral.integral_add
          (((hP.2.2.1 f).comp continuous_real_toNNReal).intervalIntegrable 0 t)
          (((hP.2.2.1 g).comp continuous_real_toNNReal).intervalIntegrable 0 t)
      map_smul' := fun c f => by simp only [map_smul, RingHom.id_apply,
        intervalIntegral.integral_smul] }
  A.mkContinuous ((t : ℝ) * Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)))
    (fun f => by
      change ‖∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f‖ ≤ _
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0 : ℝ)) (b := (t : ℝ))
        (f := fun s : ℝ => P s.toNNReal f) (C :=
          Real.exp (complexForceShift d Λ₀ ζ * (t : ℝ)) * ‖f‖) (fun s hs => by
          rw [uIoc_of_le (NNReal.coe_nonneg t)] at hs
          have hs0 : 0 ≤ s := hs.1.le
          have hst : (s.toNNReal : ℝ) ≤ t := by
            simpa only [Real.coe_toNNReal', max_eq_left hs0] using! hs.2
          exact ((P s.toNNReal).le_opNorm f).trans
            ((mul_le_mul_of_nonneg_right (hP.norm_le s.toNNReal) (norm_nonneg f)).trans
              (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
                (mul_le_mul_of_nonneg_left hst (complexForceShift_nonneg Q ζ)))
                (norm_nonneg f))))
      simpa only [sub_zero, abs_of_nonneg (NNReal.coe_nonneg t), mul_assoc, mul_comm, mul_left_comm]
        using! hb)

/-- The bounded integration operator is exactly the Bochner orbit integral. -/
theorem IsComplexEnvironmentSemigroup.timeIntegralCLM_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    hP.timeIntegralCLM t f = ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f := rfl

/-- Every L2 datum has a time-integrated orbit in the actual complete generator
domain. In particular the initial datum need not have a horizontal gradient. -/
theorem IsComplexEnvironmentSemigroup.generator_timeIntegral
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IsComplexGeneratorPair Q i ζ (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f)
      (P t f - f) := by
  change IsComplexGeneratorPair Q i ζ (hP.timeIntegralCLM t f) (P t f - f)
  apply (dense_complexGenerator_domain Q i ζ).induction
    (P := fun f => IsComplexGeneratorPair Q i ζ (hP.timeIntegralCLM t f) (P t f - f))
    ?_ ?_ f
  · rintro u ⟨v, huv⟩
    have hi := complexGeneratorPair_intervalIntegral
      ((hP.2.2.1 u).comp continuous_real_toNNReal)
      ((hP.2.2.1 v).comp continuous_real_toNNReal)
      (fun s => hP.map_generator huv s.toNNReal) 0 t
    simp only [Function.comp_apply] at hi
    rw [hP.w6_integral_generator_orbit huv t] at hi
    exact hi
  · exact (isClosed_complexGenerator_graph Q i ζ).preimage
      ((hP.timeIntegralCLM t).continuous.prodMk ((P t).continuous.sub continuous_id))

/-- Any finite nonnegative time window has the correct actual graph output. -/
theorem IsComplexEnvironmentSemigroup.generator_windowIntegral
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ≥0) :
    IsComplexGeneratorPair Q i ζ (∫ s in (a : ℝ)..(b : ℝ), P s.toNNReal f)
      (P b f - P a f) := by
  have ha := (hP.generator_timeIntegral f a).smul (-1)
  have hb := (hP.generator_timeIntegral f b).add ha
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (((hP.2.2.1 f).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) 0 a)
    (((hP.2.2.1 f).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) a b)
  simp only [Function.comp_apply] at hi
  simp only [neg_one_smul] at hb
  convert hb using 1
  · rw [← hi]
    abel
  · abel

/-- Time averages converge to the initial datum in the actual stationary L2
space. This does not assert pointwise time convergence of orbit representatives. -/
theorem IsComplexEnvironmentSemigroup.tendsto_timeAverage
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ => t⁻¹ • (∫ s in (0 : ℝ)..t, P s.toNNReal f))
      (𝓝[≠] 0) (𝓝 f) := by
  have hd := (((hP.2.2.1 f).comp continuous_real_toNNReal).integral_hasStrictDerivAt
    0 0).hasDerivAt
  rw [hasDerivAt_iff_tendsto_slope_zero] at hd
  simpa only [Function.comp_apply, zero_add, intervalIntegral.integral_same, sub_zero, Real.toNNReal_zero,
    hP.1, ContinuousLinearMap.id_apply] using! hd

/-- Compact temporal testing on the true generator domain yields another
actual graph pair. The output has the distributional minus sign. The test is
real; the datum, generator and signed force remain complex. -/
theorem IsComplexEnvironmentSemigroup.generator_timeTest
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    IsComplexGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), η s • P s.toNNReal f)
      (-(∫ s in (0 : ℝ)..(t : ℝ), η' s • P s.toNNReal f)) := by
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.2.2.1 g).comp continuous_real_toNNReal
  have hgraph (s : ℝ) : IsComplexGeneratorPair Q i ζ
      (η s • P s.toNNReal f) (η s • P s.toNNReal g) := by
    simpa only [Complex.coe_smul] using! (hP.map_generator hfg s.toNNReal).smul (η s : ℂ)
  have hg := complexGeneratorPair_intervalIntegral (hηc.fun_smul hu) (hηc.fun_smul hv) hgraph 0 t
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le (NNReal.coe_nonneg t)
    (hηc.fun_smul hu).continuousOn (f' := fun s =>
      η' s • P s.toNNReal f + η s • P s.toNNReal g)
    (fun s hs => by
      simpa only [Pi.smul_def, add_comm] using! ((hη s).hasDerivWithinAt.smul
        (hP.hasDerivWithinAt_orbit hfg s hs.1.le)).mono Ioi_subset_Ici_self)
    (((hη'.fun_smul hu).add (hηc.fun_smul hv)).intervalIntegrable 0 t)
  simp only [ht, hzero, zero_smul, sub_self] at he
  rw [intervalIntegral.integral_add ((hη'.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
    ((hηc.fun_smul hv).intervalIntegrable (μ := volume) 0 t)] at he
  rw [eq_neg_of_add_eq_zero_right he] at hg
  exact hg

/-- Temporal testing for arbitrary initial L2 data, without a generator-domain
assumption. Apply the closed graph to the primitive orbit and integrate by
parts. This is a stationary L2 graph identity, prior to physical Fubini. -/
theorem IsComplexEnvironmentSemigroup.generator_timeTest_allData
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q))
    (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η')
    (t : ℝ≥0) (hzero : η 0 = 0) (ht : η t = 0) :
    IsComplexGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), η s • P s.toNNReal f)
      (-(∫ s in (0 : ℝ)..(t : ℝ), η' s • P s.toNNReal f)) := by
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f
  let U : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hU : ∀ s, HasDerivAt U (u s) s := fun s =>
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hUc : Continuous U := continuous_iff_continuousAt.mpr fun s => (hU s).continuousAt
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hgraph (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) (t : ℝ)) :
      IsComplexGeneratorPair Q i ζ (η' s • U s) (η' s • (u s - f)) := by
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    have hg := (hP.generator_timeIntegral f s.toNNReal).smul (η' s : ℂ)
    simpa only [Real.coe_toNNReal', max_eq_left hs.1, Complex.coe_smul] using! hg
  have hg := complexGeneratorPair_intervalIntegral_on (hη'.fun_smul hUc)
    (hη'.fun_smul (hu.fun_sub continuous_const)) 0 t hgraph
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := (t : ℝ))
    (fun s _ => (hη s).smul (hU s))
    (((hηc.fun_smul hu).add (hη'.fun_smul hUc)).intervalIntegrable 0 t)
  change (∫ s in (0 : ℝ)..(t : ℝ), η s • u s + η' s • U s) =
    η (t : ℝ) • U (t : ℝ) - η 0 • U 0 at he
  simp only [ht, hzero, zero_smul, sub_self] at he
  rw [intervalIntegral.integral_add ((hηc.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
    ((hη'.fun_smul hUc).intervalIntegrable (μ := volume) 0 t)] at he
  have hηi : (∫ s in (0 : ℝ)..(t : ℝ), η' s) = 0 := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (t : ℝ)) (fun s _ => hη s) (hη'.intervalIntegrable 0 t)
    simpa only [ht, hzero, sub_self] using! h
  have hv : (∫ s in (0 : ℝ)..(t : ℝ), η' s • (u s - f)) =
      ∫ s in (0 : ℝ)..(t : ℝ), η' s • u s := by
    simp_rw [smul_sub]
    rw [intervalIntegral.integral_sub ((hη'.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
      ((hη'.fun_smul continuous_const).intervalIntegrable (μ := volume) 0 t),
      intervalIntegral.integral_smul_const, hηi, zero_smul, sub_zero]
  rw [eq_neg_of_add_eq_zero_right he, hv] at hg
  have hn := hg.smul (-1)
  simpa only [neg_one_smul, neg_neg] using! hn

/-- A prescribed countable family of actual time windows has local H1
realizations on a single environment event, simultaneously for all compact sets.
The field being realized is the L2 Bochner time integral; identification with a
samplewise time integral requires a separate joint-representative construction. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_windowIntegrals_spatial
    [Fact (2 ≤ d)] (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℕ → ℝ≥0) :
    ∃ G : ℕ → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ n, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (∫ s in (a n : ℝ)..(b n : ℝ), P s.toNNReal f) (G n)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n,
        let U : Lp ℂ 2 (reducedLaw Q) :=
          ∫ s in (a n : ℝ)..(b n : ℝ), P s.toNNReal f
        HasWeakGradient Set.univ (fun x => (U (translate x ω)).re)
          (fun x j => (G n j (translate x ω)).re) ∧
        HasWeakGradient Set.univ (fun x => (U (translate x ω)).im)
          (fun x j => (G n j (translate x ω)).im) ∧
        ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => U (translate x ω)) 2 (volume.restrict K) ∧
          MemLp (fun x => (P (b n) f - P (a n) f) (translate x ω)) 2
            (volume.restrict K) ∧
          ∀ j, MemLp (fun x => G n j (translate x ω)) 2 (volume.restrict K) := by
  have he (n : ℕ) := (hP.generator_windowIntegral f (a n) (b n)).exists_ae_spatial_gradient
  choose G hG hsp using he
  exact ⟨G, hG, ae_all_iff.mpr hsp⟩

/-- The preceding time-window construction consumes the internally constructed
forced evolution, for arbitrary complex signed force and arbitrary L2 datum. -/
theorem forcedComplexEvolution_generator_windowIntegral
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ≥0) :
    IsComplexGeneratorPair Q i ζ
      (∫ s in (a : ℝ)..(b : ℝ), forcedComplexEvolution Q i ζ s.toNNReal f)
      (forcedComplexEvolution Q i ζ b f - forcedComplexEvolution Q i ζ a f) :=
  (isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ).generator_windowIntegral f a b

end EinsteinFull
