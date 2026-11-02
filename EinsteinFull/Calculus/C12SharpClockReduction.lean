import EinsteinFull.Calculus.C12SharpCorrectorOccupation
import EinsteinFull.Calculus.C6ResponseVelocityCesaro
import EinsteinRelation.Clock.ClockExpectation
import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities
import EinsteinFull.Calculus.S4PathwiseV2Support
import EinsteinFull.Calculus.S4SharpFamilySupport
import EinsteinFull.Calculus.S2SharpClockSupport
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_harmonic
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_fields
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_clock
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

/-- Transport the supplied reduced martingale problem to the white-noise
parameterization before applying the bounded-corrector occupation theorem. -/
theorem sharp_corrector_generator_time_average_zero_ae
    {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∀ᵐ W ∂P,
      ∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W),
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedGenerator (⟨0, by omega⟩ : Fin d)
            (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) lam
            (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0) := by
  rw [hQ] at hY
  have hYnoise := ae_of_ae_map
    (EinsteinFull.Work.W8.measurable_physicalPair (⟨0, by omega⟩ : Fin d)).aemeasurable hY
  filter_upwards [hYnoise] with W hW
  exact sharp_corrector_generator_time_average_zero hd (⟨0, by omega⟩ : Fin d) W lam
    (Y (0, EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W)) hW

/-- For an actual sharp path, its clock rate and the vanishing corrector
occupation determine the coefficient average, with the same signed force. -/
theorem sharp_coefficient_average_of_clock_speed
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (lam : ℝ) (hlam : lam ≠ 0)
    (γ : Path d) (η : ℝ)
    (hclock : Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed
      (EinsteinFull.Work.W8.physicalPair i W) γ η)
    (hgen : Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam
        (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W)
        (γ u.toNNReal) i i) atTop
      (𝓝 (1 + (1 - η) / (EinsteinFull.Work.W8.clockParameter i * lam))) := by
  let ω := EinsteinFull.Work.W8.physicalPair i W
  let δ := EinsteinFull.Work.W8.clockParameter i
  have hδ : δ ≠ 0 := (EinsteinFull.Work.W8.clockParameter_pos i).ne'
  have hc : Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      clockDensity ω (γ u.toNNReal)) atTop (𝓝 η) := by
    have h := hclock.comp tendsto_real_toNNReal_atTop
    apply h.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change (Clock.physicalPathClock ω γ t.toNNReal : ℝ) / (t.toNNReal : ℝ) = _
    simp only [Clock.coe_physicalPathClock, Clock.pathClock, Real.toNNReal_of_nonneg ht,
      div_eq_mul_inv, mul_comm]
    rfl
  have hlim : Tendsto (fun t : ℝ => 1 +
      (1 - t⁻¹ * ∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal)) / (δ * lam) -
      (t⁻¹ * ∫ u in (0 : ℝ)..t, reducedGenerator i ω lam
        (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) / lam) atTop
      (𝓝 (1 + (1 - η) / (δ * lam))) := by
    simpa only [zero_div, sub_zero] using
      (tendsto_const_nhds.add ((tendsto_const_nhds.sub hc).div_const (δ * lam))).sub
        (hgen.div_const lam)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hpath : Continuous (fun u : ℝ => γ u.toNNReal) :=
    γ.continuous.comp continuous_real_toNNReal
  have hμ : IntervalIntegrable (fun u : ℝ => clockDensity ω (γ u.toNNReal)) volume 0 t :=
    ((reduce ω).2.continuous.comp hpath).intervalIntegrable _ _
  have ha : IntervalIntegrable
      (fun u : ℝ => reducedCoefficient ω (γ u.toNNReal) i i) volume 0 t :=
    (((continuous_apply i).comp ((continuous_apply i).comp
      (continuous_reducedCoefficient ω))).comp hpath).intervalIntegrable _ _
  have hidentity : (∫ u in (0 : ℝ)..t, reducedGenerator i ω lam
      (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) =
      (t - ∫ u in (0 : ℝ)..t, clockDensity ω (γ u.toNNReal)) / δ +
        lam * (t - ∫ u in (0 : ℝ)..t, reducedCoefficient ω (γ u.toNNReal) i i) := by
    have hpoint : (fun u : ℝ => reducedGenerator i ω lam
        (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) =
        (fun u : ℝ => (1 - clockDensity ω (γ u.toNNReal)) / δ +
          lam * (1 - reducedCoefficient ω (γ u.toNNReal) i i)) :=
      funext fun u => (sharpClock_identities i W (γ u.toNNReal) lam).2
    rw [hpoint]
    rw [intervalIntegral.integral_add ((intervalIntegrable_const.sub hμ).div_const δ)
      ((intervalIntegrable_const.sub ha).const_mul lam),
      intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub intervalIntegrable_const hμ,
      intervalIntegral.integral_sub intervalIntegrable_const ha]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
  rw [hidentity]
  field_simp
  ring

/-- The average and clock rate obey the exact sharp-clock algebraic relation. -/
theorem sharp_clock_rate_average_relation
    {d : ℕ} (i : Fin d) (lam : ℝ) (hlam : lam ≠ 0) (η : ℝ) :
    η = 1 - EinsteinFull.Work.W8.clockParameter i * lam *
      ((1 + (1 - η) / (EinsteinFull.Work.W8.clockParameter i * lam)) - 1) := by
  have hδ : EinsteinFull.Work.W8.clockParameter i ≠ 0 :=
    (EinsteinFull.Work.W8.clockParameter_pos i).ne'
  field_simp
  ring

/-- A supplied same-law rate yields the deterministic coefficient average on
one common white-noise and path event with the corrector occupation limit. -/
theorem sharp_clock_average_ae_of_rate
    {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    ∃ avg : ℝ,
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg - 1) ∧
      ∀ᵐ W ∂P,
        ∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W),
          Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
            reducedCoefficient (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W)
              (γ u.toNNReal) (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d))
            atTop (𝓝 avg) ∧
          Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
            reducedGenerator (⟨0, by omega⟩ : Fin d)
              (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) lam
              (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0) := by
  let first : Fin d := ⟨0, by omega⟩
  refine ⟨1 + (1 - η) / (EinsteinFull.Work.W8.clockParameter first * lam),
    sharp_clock_rate_average_relation first lam hlam η, ?_⟩
  have hocc := sharp_corrector_generator_time_average_zero_ae hd Q hQ lam Y hY
  rw [HasReducedClockRate, hQ] at hη
  have hrate := ae_of_ae_map
    (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable hη
  filter_upwards [hrate, hocc] with W hWrate hWocc
  filter_upwards [hWrate, hWocc] with γ hγrate hγocc
  exact ⟨sharp_coefficient_average_of_clock_speed first W lam hlam γ η hγrate hγocc, hγocc⟩

private theorem continuous_coefficient_clock (d : ℕ) (i : Fin d) (t : ℝ) :
    Continuous (fun z : FieldPair d × Path d =>
      ∫ u in (0 : ℝ)..t, reducedCoefficient z.1 (z.2 u.toNNReal) i i) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  have ha : Continuous (fun z : (FieldPair d × Path d) × ℝ => (reduce z.1.1).1) :=
    continuous_fst.comp (Probability.continuous_reduce.comp (continuous_fst.comp continuous_fst))
  have hx : Continuous (fun z : (FieldPair d × Path d) × ℝ => z.1.2 z.2.toNNReal) :=
    (continuous_snd.comp continuous_fst).eval (continuous_real_toNNReal.comp continuous_snd)
  exact (continuous_apply i).comp ((continuous_apply i).comp (ha.eval hx))

private theorem coefficient_average_real_of_nat
    {d : ℕ} {Λ : ℝ} {ω : FieldPair d} (hΛ : 0 < Λ) (hω : IsRegular Λ ω)
    (i : Fin d) (γ : Path d) (avg : ℝ)
    (hn : Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(n : ℝ),
      reducedCoefficient ω (γ u.toNNReal) i i) atTop (𝓝 avg)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
      reducedCoefficient ω (γ u.toNNReal) i i) atTop (𝓝 avg) := by
  let f : ℝ → ℝ := fun u => reducedCoefficient ω (γ u.toNNReal) i i
  have hc : Continuous f :=
    ((continuous_apply i).comp ((continuous_apply i).comp
      (continuous_reducedCoefficient ω))).comp (γ.continuous.comp continuous_real_toNNReal)
  have hpos : ∀ u, 0 ≤ f u := by
    intro u
    have h := ((hω.1 (γ u.toNNReal)).2 (unitVector i)).1
    rw [euclideanSq_unitVector, dot_unitVector_mulVec, mul_one] at h
    have ha : 0 ≤ ω.1 (γ u.toNNReal) i i := (inv_pos.mpr hΛ).le.trans h
    exact mul_nonneg (Real.exp_pos _).le ha
  have hspeed : Tendsto (fun t : ℝ≥0 =>
      (∫ u in (0 : ℝ)..(t : ℝ), f u) / (t : ℝ)) atTop (𝓝 avg) := by
    apply Clock.tendsto_div_of_tendsto_natCast
    · intro t
      exact intervalIntegral.integral_nonneg_of_forall t.property hpos
    · intro t u htu
      apply intervalIntegral.integral_mono_interval le_rfl t.property
        (show (t : ℝ) ≤ (u : ℝ) from htu)
      · exact Filter.Eventually.of_forall hpos
      · exact hc.intervalIntegrable _ _
    · simpa only [NNReal.coe_natCast, div_eq_mul_inv, mul_comm] using hn
  apply (hspeed.comp tendsto_real_toNNReal_atTop).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  change (∫ u in (0 : ℝ)..(t.toNNReal : ℝ), f u) / (t.toNNReal : ℝ) = _
  rw [Real.coe_toNNReal t ht]
  exact div_eq_inv_mul _ _

/-- The coefficient-average event descends to the actual environment law.
Integer-time measurability and ellipticity recover every real time. -/
theorem sharp_coefficient_average_ae_of_rate
    {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
      Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
        reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d))
        atTop (𝓝 (1 + (1 - η) /
          (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam))) := by
  let first : Fin d := ⟨0, by omega⟩
  let avg := 1 + (1 - η) / (EinsteinFull.Work.W8.clockParameter first * lam)
  obtain ⟨κ, hκ, hκeq⟩ := response_finite_originLaw Q Y (hY.mono fun _ h => h.1)
  letI := hκ
  let S : Set (FieldPair d × Path d) := {z | Tendsto (fun n : ℕ =>
    (n : ℝ)⁻¹ * ∫ u in (0 : ℝ)..(n : ℝ), reducedCoefficient z.1 (z.2 u.toNNReal) first first)
      atTop (𝓝 avg)}
  have hS : MeasurableSet S := measurableSet_tendsto (𝓝 avg) fun n =>
    ((continuous_coefficient_clock d first (n : ℝ)).const_mul (n : ℝ)⁻¹).measurable
  have hset : MeasurableSet {ω | ∀ᵐ γ ∂κ ω, (ω, γ) ∈ S} := by
    simp only [ae_iff]
    exact measurableSet_eq_fun
      (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) hS.compl) measurable_const
  have hκnoise := ae_of_ae_map
    (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable (hQ ▸ hκeq)
  have hYnoise := ae_of_ae_map
    (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable (hQ ▸ hY)
  change ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η at hη
  have hηnoise := ae_of_ae_map
    (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable (hQ ▸ hη)
  have hnat : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂κ ω, (ω, γ) ∈ S := by
    rw [hQ]
    apply (ae_map_iff (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable hset).mpr
    filter_upwards [hκnoise, hYnoise, hηnoise] with W hWκ hWY hWη
    rw [hWκ]
    have ho := sharp_corrector_generator_time_average_zero hd first W lam _ hWY
    filter_upwards [hWη, ho] with γ hγrate hγocc
    exact (sharp_coefficient_average_of_clock_speed first W lam hlam γ η hγrate hγocc).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [hnat, hκeq, Q.regular] with ω hω hωκ hreg
  rw [hωκ] at hω
  filter_upwards [hω] with γ hγ
  exact coefficient_average_real_of_nat (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
    hreg first γ avg hγ

/-- All probabilistic sharp-clock conclusions follow from a rate for the
supplied law; no further family, uniqueness, or invariant-law input is used. -/
theorem sharp_clock_conclusions_of_rate
    {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    ∃ avg : ℝ,
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg - 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d))
          atTop (𝓝 avg)) ∧
      (∀ᵐ W ∂P,
        ∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W),
          Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
            reducedGenerator (⟨0, by omega⟩ : Fin d)
              (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) lam
              (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0)) := by
  let first : Fin d := ⟨0, by omega⟩
  exact ⟨1 + (1 - η) / (EinsteinFull.Work.W8.clockParameter first * lam),
    sharp_clock_rate_average_relation first lam hlam η,
    sharp_coefficient_average_ae_of_rate hd Q hQ lam hlam Y hY η hη,
    sharp_corrector_generator_time_average_zero_ae hd Q hQ lam Y hY⟩

private theorem sharp_inverseKernel {d : ℕ} (L : ℝ) (κ : QuenchedPathLaws d) :
    ∃ κ' : QuenchedPathLaws d, ∀ (ω : FieldPair d) (hω : IsRegular L ω),
      IsProbabilityMeasure (κ (0, ω)) →
        κ' (0, ω) = (κ (0, ω)).map (timeChangeMap hω) := by
  classical
  let S : Set (Vec d × FieldPair d) := {a | a.1 = 0 ∧ κ a Set.univ = 1}
  have hS : MeasurableSet S := by
    show MeasurableSet ({a : Vec d × FieldPair d | a.1 = 0} ∩ {a | κ a Set.univ = 1})
    exact ((measurableSet_singleton (0 : Vec d)).preimage measurable_fst).inter
      (measurableSet_eq_fun (Kernel.measurable_coe κ MeasurableSet.univ) measurable_const)
  let κ₁ : QuenchedPathLaws d := Kernel.piecewise hS κ 0
  have : IsFiniteKernel κ₁ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
    simp only [κ₁, Kernel.piecewise_apply]
    split_ifs with h
    · exact h.2.le
    · simp
  refine ⟨Kernel.map (Kernel.id ×ₖ κ₁) (timeChangeFamily L), fun ω hω hprob => ?_⟩
  have hmem : ((0 : Vec d), ω) ∈ S := ⟨rfl, measure_univ⟩
  have h1 : κ₁ (0, ω) = κ (0, ω) := by
    simp only [κ₁, Kernel.piecewise_apply, hmem, ite_true]
  rw [Kernel.map_apply _ (measurable_timeChangeFamily d L), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, h1,
    Measure.map_map (measurable_timeChangeFamily d L) measurable_prodMk_left]
  congr 1
  funext γ
  exact dite_eq_left hω

/-- Inverse clocks turn an arbitrary almost-sure reduced family into a physical family.
No pointwise solution selection or martingale-problem uniqueness is needed. -/
private theorem sharp_inverseFamily {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) (i : Fin d)
    (Y : DiffusionFamily d)
    (hY : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y lam (0, ω))) :
    ∃ X : DiffusionFamily d, IsSignedPhysicalFamily i Q X ∧
      ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular D.ellipticity ω,
        X lam (0, ω) = (Y lam (0, ω)).map
          (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  choose X hX using fun lam : ℝ => sharp_inverseKernel D.ellipticity (Y lam)
  refine ⟨X, fun lam => ?_, fun lam => ?_⟩
  · filter_upwards [Q.regular, hsm, hY lam] with ω hreg hs hsol
    rw [hX lam ω hreg hsol.1]
    exact timeChange_solves hΛ hreg hs i lam 0 hsol
  · filter_upwards [Q.regular, hY lam] with ω hreg hsol
    exact ⟨hreg, hX lam ω hreg hsol.1⟩

/-- Splice the supplied law at its force before applying time-change identities.
The auxiliary reduced family is an internal input to this bridge. -/
theorem sharp_clock_rate_of_reducedFamily
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω)
    (b : ℕ → ℝ) (hb : ∀ k : ℕ, 1 ≤ k → 0 < b k)
    (hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω)
    (Y₀ : DiffusionFamily d)
    (hY₀ : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y₀ lam (0, ω)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ η : ℝ, HasReducedClockRate Q Y η := by
  classical
  let PY : DiffusionFamily d := fun l => if l = lam then Y else Y₀ l
  have hPY : ∀ l : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω l)
        0 (PY l (0, ω)) := by
    intro l
    by_cases he : l = lam
    · subst l
      simpa only [PY, ite_true] using hY
    · simpa only [PY, ite_eq_right he] using hY₀ l
  obtain ⟨PX, hPX, hrel⟩ := sharp_inverseFamily D Q hsm
    (⟨0, by omega⟩ : Fin d) PY hPY
  obtain ⟨Λ, -, hall⟩ := htc D.ellipticity D.one_le_ellipticity
  obtain ⟨hrate, -, -⟩ := hall d hd D.dependenceRange b Q D.one_le_dependenceRange hb hsmb
    PX PY hPX hPY hrel
  obtain ⟨η, vX, vY, -, -, hη, -, -, -⟩ := hrate lam hlam
  exact ⟨η, by simpa only [PY, ite_true] using hη⟩

/-- Assemble the probabilistic sharp-clock conclusion from an internal reduced
family, using the actual sharp pushforward law to supply smoothness. -/
theorem sharp_clock_conclusions_of_reducedFamily
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (b : ℕ → ℝ) (hb : ∀ k : ℕ, 1 ≤ k → 0 < b k)
    (hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds b ω)
    (Y₀ : DiffusionFamily d)
    (hY₀ : ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y₀ lam (0, ω)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg - 1) ∧
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient ω (γ u.toNNReal) (⟨0, by omega⟩ : Fin d) (⟨0, by omega⟩ : Fin d))
          atTop (𝓝 avg)) ∧
      (∀ᵐ W ∂P,
        ∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W),
          Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
            reducedGenerator (⟨0, by omega⟩ : Fin d)
              (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d) W) lam
              (EinsteinFull.Work.W8.corrector W) (γ u.toNNReal)) atTop (𝓝 0)) := by
  obtain ⟨η, hη⟩ := sharp_clock_rate_of_reducedFamily htc hd D Q
    (sharp_ae_smooth hd Q hQ) b hb hsmb Y₀ hY₀ lam hlam Y hY
  obtain ⟨avg, havg⟩ := sharp_clock_conclusions_of_rate hd Q hQ lam hlam Y hY η hη
  exact ⟨η, avg, hη, havg⟩

/-- Conditional consumer of the planned foundation family interface. The graph
premises stay explicit; the foundation producer is supplied separately until
its reviewed declaration is available. -/
theorem sharp_clock_of_foundation
    (hFoundationReducedFamily :
      ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
        (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
        (∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) →
        ∃ Y₀ : DiffusionFamily d, ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
            0 (Y₀ lam (0, ω)))
    (hfields : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_clockStmt := by
  intro d hd P hP
  dsimp only
  intro D Q hQ
  obtain ⟨-, -, D', -, -, -, hD'⟩ := hfields d hd
  obtain ⟨Q', hQ', hsm', -⟩ := hD' P hP
  have hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds D'.derivativeBound ω := by
    rw [hQ.trans hQ'.symm]
    exact hsm'
  constructor
  · intro W x lam
    exact sharpClock_identities (⟨0, by omega⟩ : Fin d) W x lam
  · obtain ⟨Y₀, hY₀⟩ := hFoundationReducedFamily d hd D Q (sharp_ae_smooth hd Q hQ)
    intro lam hlam Y hY
    exact sharp_clock_conclusions_of_reducedFamily h2 hd D Q hQ D'.derivativeBound
      D'.derivativeBound_pos hsmb Y₀ hY₀ lam hlam Y hY

/-- The announced pointwise reduced-law witnesses supply the family required by
the sharp clock consumer. This conditional helper gives no graph closure. -/
theorem sharp_clock_of_announced_reduced_foundation
    (c16_reduced_mp_exists : ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ)
      (Q : EnvironmentLaw d L R) (i : Fin d) (lam : ℝ),
      ∃ PY : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)))
    (_h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_clockStmt := by
  classical
  apply sharp_clock_of_foundation ?_ h1 h2
  intro d hd D Q _hsm
  choose Y hY using fun lam : ℝ =>
    c16_reduced_mp_exists d hd D.ellipticity D.dependenceRange Q
      (⟨0, by omega⟩ : Fin d) lam
  exact ⟨Y, hY⟩

end EinsteinFull.Blueprint
