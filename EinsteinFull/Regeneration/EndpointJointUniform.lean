import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.DeterministicRestartJoint
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.FiniteHistoryFiltration
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Probability.ConditionalProbability

/-!
# The uniform successful endpoint for tests of the grid position and the endpoint

GMP Proposition 5.4(ii) (p. 23): on a successful coin, the endpoint of the interval is uniform
on the ball `B^z`, `z` the position at the start of the interval, given the past. The coupling
predicate states this for tests of the endpoint alone. Two finite measures on pairs (start,
endpoint) that agree on rectangles agree, so the statement extends to nonnegative bounded tests
of the start of the interval and the endpoint together, such as functions of the bridge
displacement.
-/

open MeasureTheory ProbabilityTheory Set EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The endpoint ball at `x` is the translate of the endpoint ball at the origin. -/
theorem endpointBall_zero_eq_preimage (i : Fin d) (R : ℝ) (x : Vec d) :
    endpointBall i R 0 = (fun u => x + u) ⁻¹' endpointBall i R x := by
  ext u
  simp only [endpointBall, mem_preimage, mem_ofPred_eq, zero_add, add_sub_add_left_eq_sub]

theorem volume_endpointBall (i : Fin d) (R : ℝ) (x : Vec d) :
    volume (endpointBall i R x) = volume (endpointBall i R 0) := by
  rw [endpointBall_zero_eq_preimage i R x, measure_preimage_add]

theorem measurableSet_endpointBall (i : Fin d) (R : ℝ) (x : Vec d) :
    MeasurableSet (endpointBall i R x) := by
  have hc : Continuous fun y : Vec d => euclideanNorm (y - (x + (9 * R) • unitVector i)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  exact (isOpen_lt hc continuous_const).measurableSet

/-- The endpoint average at `x` is the integral of the translated test against the uniform law
on the endpoint ball at the origin. -/
theorem endpointAverage_eq_integral_cond (i : Fin d) (R : ℝ) (x : Vec d) (f : Vec d → ℝ) :
    endpointAverage i R x f =
      ∫ u, f (x + u) ∂ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R 0) := by
  rw [ProbabilityTheory.cond, integral_smul_measure, endpointAverage]
  have hmp : MeasurePreserving (fun u : Vec d => x + u) volume volume :=
    measurePreserving_add_left volume x
  have he : MeasurableEmbedding (fun u : Vec d => x + u) :=
    (MeasurableEquiv.addLeft x).measurableEmbedding
  have hs := hmp.setIntegral_preimage_emb he f (endpointBall i R x)
  rw [← endpointBall_zero_eq_preimage i R x] at hs
  rw [hs, volume_endpointBall i R x, ENNReal.toReal_inv, smul_eq_mul, div_eq_inv_mul]

theorem endpointAverage_indicator (i : Fin d) (R : ℝ) (x : Vec d) (B : Set (Vec d))
    (hB : MeasurableSet B) (hR0 : volume (endpointBall i R 0) ≠ ⊤)
    (hRpos : volume (endpointBall i R 0) ≠ 0) :
    ENNReal.ofReal (endpointAverage i R x (B.indicator 1)) =
      ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R 0)
        ((fun u => x + u) ⁻¹' B) := by
  rw [endpointAverage_eq_integral_cond]
  have hfin : IsProbabilityMeasure
      (ProbabilityTheory.cond (volume : Measure (Vec d)) (endpointBall i R 0)) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hRpos hR0
  have hfun : (fun u => B.indicator (1 : Vec d → ℝ) (x + u)) =
      ((fun u => x + u) ⁻¹' B).indicator 1 := by
    ext u
    exact (Set.indicator_comp_right (fun u => x + u)).symm
  rw [hfun, integral_indicator_one ((measurable_const_add x) hB), measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- A path coordinate at a time of the window `[0, nΔ]` is measurable for the finite history. -/
theorem measurable_path_finiteHistorySigma (Δ : ℝ≥0) (n : ℕ) (t : ℝ≥0)
    (ht : t ≤ (n : ℝ≥0) * Δ) :
    @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
      (fun z => z.1 t) := by
  rw [measurable_iff_comap_le]
  unfold finiteHistorySigma
  exact le_sup_of_le_left
    (le_iSup_of_le (⟨t, zero_le, ht⟩ : Set.Icc (0 : ℝ≥0) ((n : ℝ≥0) * Δ)) le_rfl)

/-- The uniform successful endpoint extends to nonnegative bounded tests of the start of the
interval and of the endpoint. -/
theorem uniformSuccessfulEndpointAt_joint (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) [IsProbabilityMeasure (K xω)]
    (hU : UniformSuccessfulEndpointAt Δ δ R i K xω) (hδ : 0 ≤ δ)
    (hR0 : volume (endpointBall i R 0) ≠ ⊤) (hRpos : volume (endpointBall i R 0) ≠ 0)
    (n : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (ψ : Vec d × Vec d → ℝ) (hψ : Measurable ψ) (hbψ : BoundedRealTest ψ)
    (hψ0 : ∀ p, 0 ≤ ψ p) :
    (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) *
        ψ (z.1 ((n : ℝ≥0) * Δ), z.1 (((n + 1 : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
      δ * ∫ z, H z * endpointAverage i R (z.1 ((n : ℝ≥0) * Δ))
        (fun y => ψ (z.1 ((n : ℝ≥0) * Δ), y)) ∂K xω := by
  classical
  set t₀ : ℝ≥0 := (n : ℝ≥0) * Δ with ht₀
  set t₁ : ℝ≥0 := ((n + 1 : ℕ) : ℝ≥0) * Δ with ht₁
  set U₀ : Measure (Vec d) := ProbabilityTheory.cond volume (endpointBall i R 0) with hU₀def
  have hU₀ : IsProbabilityMeasure U₀ :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite hRpos hR0
  set coin : CoupledSample d → ℝ := fun z => if z.2 n = true then 1 else 0 with hcoindef
  have hcoin : Measurable coin :=
    Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply n).comp measurable_snd)
      measurable_const) measurable_const measurable_const
  have hcoin0 : ∀ z, 0 ≤ coin z := fun z => by
    simp only [hcoindef]
    split_ifs <;> norm_num
  have hcoin1 : ∀ z, coin z ≤ 1 := fun z => by
    simp only [hcoindef]
    split_ifs <;> norm_num
  have hHm : Measurable H := hH.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
  have he₀ : Measurable fun z : CoupledSample d => z.1 t₀ :=
    (continuous_eval_const t₀).measurable.comp measurable_fst
  have he₁ : Measurable fun z : CoupledSample d => z.1 t₁ :=
    (continuous_eval_const t₁).measurable.comp measurable_fst
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨Cψ, hCψ⟩ := hbψ
  have hHle : ∀ z, H z ≤ max CH 0 := fun z =>
    (le_abs_self _).trans ((hCH z).trans (le_max_left _ _))
  have hψle : ∀ p, ψ p ≤ max Cψ 0 := fun p =>
    (le_abs_self _).trans ((hCψ p).trans (le_max_left _ _))
  set f₁ : CoupledSample d → Vec d × Vec d := fun z => (z.1 t₀, z.1 t₁) with hf₁def
  set f₂ : CoupledSample d × Vec d → Vec d × Vec d := fun p => (p.1.1 t₀, p.1.1 t₀ + p.2)
    with hf₂def
  have hf₁ : Measurable f₁ := he₀.prodMk he₁
  have hf₂ : Measurable f₂ := (he₀.comp measurable_fst).prodMk
    ((he₀.comp measurable_fst).add measurable_snd)
  set w₁ : CoupledSample d → ℝ≥0 := fun z => (H z * coin z).toNNReal with hw₁def
  set w₂ : CoupledSample d → ℝ≥0 := fun z => (δ * H z).toNNReal with hw₂def
  have hw₁ : Measurable w₁ := (hHm.mul hcoin).real_toNNReal
  have hw₂ : Measurable w₂ := (measurable_const.mul hHm).real_toNNReal
  set μ₁ := (K xω).withDensity fun z => (w₁ z : ℝ≥0∞) with hμ₁def
  set μ₂ := (K xω).withDensity fun z => (w₂ z : ℝ≥0∞) with hμ₂def
  have hw₁le : ∀ z, (w₁ z : ℝ≥0∞) ≤ ENNReal.ofReal (max CH 0) := fun z =>
    ENNReal.ofReal_le_ofReal (by nlinarith [hHle z, hcoin1 z, hcoin0 z, hH0 z])
  have hw₂le : ∀ z, (w₂ z : ℝ≥0∞) ≤ ENNReal.ofReal (δ * max CH 0) := fun z =>
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hHle z) hδ)
  have hμ₁ : IsFiniteMeasure μ₁ := by
    refine ⟨?_⟩
    rw [hμ₁def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_mono hw₁le).trans_lt (by simp [lintegral_const])
  have hμ₂ : IsFiniteMeasure μ₂ := by
    refine ⟨?_⟩
    rw [hμ₂def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_mono hw₂le).trans_lt (by simp [lintegral_const])
  set m₁ := μ₁.map f₁ with hm₁def
  set m₂ := (μ₂.prod U₀).map f₂ with hm₂def
  have hm₁ : IsFiniteMeasure m₁ := Measure.isFiniteMeasure_map μ₁ f₁
  have hm₂ : IsFiniteMeasure m₂ := Measure.isFiniteMeasure_map (μ₂.prod U₀) f₂
  have hm₁E : ∀ E : Set (Vec d × Vec d), MeasurableSet E →
      m₁ E = ∫⁻ z, (f₁ ⁻¹' E).indicator (fun z => (w₁ z : ℝ≥0∞)) z ∂K xω := by
    intro E hE
    rw [hm₁def, Measure.map_apply hf₁ hE, hμ₁def, withDensity_apply _ (hf₁ hE),
      lintegral_indicator (hf₁ hE)]
  have hm₂E : ∀ E : Set (Vec d × Vec d), MeasurableSet E →
      m₂ E = ∫⁻ z, (w₂ z : ℝ≥0∞) * U₀ (Prod.mk z ⁻¹' (f₂ ⁻¹' E)) ∂K xω := by
    intro E hE
    rw [hm₂def, Measure.map_apply hf₂ hE, Measure.prod_apply (hf₂ hE), hμ₂def,
      lintegral_withDensity_eq_lintegral_mul _ hw₂.coe_nnreal_ennreal
        (measurable_measure_prodMk_left (hf₂ hE))]
    rfl
  have hind01 : ∀ (S : Set (Vec d)) (y : Vec d),
      0 ≤ S.indicator (1 : Vec d → ℝ) y ∧ S.indicator (1 : Vec d → ℝ) y ≤ 1 := by
    intro S y
    by_cases h : y ∈ S <;> simp [h]
  have havg0 : ∀ (x : Vec d) (f : Vec d → ℝ), (∀ y, 0 ≤ f y) → 0 ≤ endpointAverage i R x f :=
    fun x f hf => div_nonneg (setIntegral_nonneg (measurableSet_endpointBall i R x)
      fun y _ => hf y) ENNReal.toReal_nonneg
  have hrect : ∀ A B : Set (Vec d), MeasurableSet A → MeasurableSet B →
      m₁ (A ×ˢ B) = m₂ (A ×ˢ B) := by
    intro A B hA hB
    set HA : CoupledSample d → ℝ := fun z => H z * A.indicator 1 (z.1 t₀) with hHAdef
    have hHA0 : ∀ z, 0 ≤ HA z := fun z => mul_nonneg (hH0 z) (hind01 A _).1
    have hHAle : ∀ z, HA z ≤ max CH 0 := fun z =>
      (mul_le_of_le_one_right (hH0 z) (hind01 A _).2).trans (hHle z)
    have hHA : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance HA :=
      hH.mul ((measurable_one.indicator hA).comp
        (measurable_path_finiteHistorySigma Δ n t₀ le_rfl))
    have hHAm : Measurable HA := hHA.mono (Probability.finiteHistorySigma_le Δ n) le_rfl
    have hid := hU n HA (B.indicator 1) hHA
      ⟨max CH 0, fun z => by rw [abs_of_nonneg (hHA0 z)]; exact hHAle z⟩
      (measurable_one.indicator hB)
      ⟨1, fun y => by rw [abs_of_nonneg (hind01 B y).1]; exact (hind01 B y).2⟩
    have hint₁ : Integrable (fun z => HA z * coin z * B.indicator 1 (z.1 t₁)) (K xω) := by
      refine Integrable.of_bound ((hHAm.mul hcoin).mul
        ((measurable_one.indicator hB).comp he₁)).aestronglyMeasurable (max CH 0)
        (ae_of_all _ fun z => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (hHA0 z) (hcoin0 z))
        (hind01 B _).1)]
      calc HA z * coin z * B.indicator 1 (z.1 t₁) ≤ HA z * 1 * 1 :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hcoin1 z) (hHA0 z)) (hind01 B _).2
              (hind01 B _).1 (by rw [mul_one]; exact hHA0 z)
        _ ≤ max CH 0 := by rw [mul_one, mul_one]; exact hHAle z
    have hint₂ : Integrable (fun z => δ * (HA z * endpointAverage i R (z.1 t₀) (B.indicator 1)))
        (K xω) := by
      have havgm : Measurable fun z : CoupledSample d =>
          endpointAverage i R (z.1 t₀) (B.indicator 1) := by
        have : (fun z : CoupledSample d => endpointAverage i R (z.1 t₀) (B.indicator 1)) =
            fun z => (U₀ ((fun u => z.1 t₀ + u) ⁻¹' B)).toReal := by
          funext z
          rw [← endpointAverage_indicator i R (z.1 t₀) B hB hR0 hRpos,
            ENNReal.toReal_ofReal (havg0 _ _ fun y => (hind01 B y).1)]
        rw [this]
        refine Measurable.ennreal_toReal ?_
        have hs : MeasurableSet {p : CoupledSample d × Vec d | p.1.1 t₀ + p.2 ∈ B} :=
          ((he₀.comp measurable_fst).add measurable_snd) hB
        exact measurable_measure_prodMk_left hs
      refine Integrable.of_bound (measurable_const.mul (hHAm.mul havgm)).aestronglyMeasurable
        (δ * max CH 0) (ae_of_all _ fun z => ?_)
      have havg1 : endpointAverage i R (z.1 t₀) (B.indicator 1) ≤ 1 := by
        rw [← ENNReal.toReal_ofReal (havg0 _ _ fun y => (hind01 B y).1),
          endpointAverage_indicator i R (z.1 t₀) B hB hR0 hRpos]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by
          rw [ENNReal.ofReal_one]; exact prob_le_one)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hδ (mul_nonneg (hHA0 z)
        (havg0 _ _ fun y => (hind01 B y).1)))]
      exact mul_le_mul_of_nonneg_left ((mul_le_of_le_one_right (hHA0 z) havg1).trans
        (hHAle z)) hδ
    rw [hm₁E _ (hA.prod hB), hm₂E _ (hA.prod hB)]
    have h₁ : (fun z => (f₁ ⁻¹' (A ×ˢ B)).indicator (fun z => (w₁ z : ℝ≥0∞)) z) =
        fun z => ENNReal.ofReal (HA z * coin z * B.indicator 1 (z.1 t₁)) := by
      funext z
      by_cases hz₀ : z.1 t₀ ∈ A <;> by_cases hz₁ : z.1 t₁ ∈ B <;>
        simp [f₁, hz₀, hz₁, HA, w₁, ENNReal.ofReal]
    have h₂ : (fun z => (w₂ z : ℝ≥0∞) * U₀ (Prod.mk z ⁻¹' (f₂ ⁻¹' (A ×ˢ B)))) =
        fun z => ENNReal.ofReal (δ * (HA z * endpointAverage i R (z.1 t₀) (B.indicator 1))) := by
      funext z
      have hsec : Prod.mk z ⁻¹' (f₂ ⁻¹' (A ×ˢ B)) =
          if z.1 t₀ ∈ A then (fun u => z.1 t₀ + u) ⁻¹' B else ∅ := by
        ext u
        by_cases hz : z.1 t₀ ∈ A <;> simp [f₂, hz]
      rw [hsec]
      by_cases hz : z.1 t₀ ∈ A
      · rw [ite_eq_left hz, ← endpointAverage_indicator i R (z.1 t₀) B hB hR0 hRpos]
        change ENNReal.ofReal (δ * H z) * _ = _
        rw [← ENNReal.ofReal_mul (mul_nonneg hδ (hH0 z))]
        congr 1
        simp only [HA, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
        ring
      · simp [hz, HA]
    rw [h₁, h₂, ← ofReal_integral_eq_lintegral_ofReal hint₁ (ae_of_all _ fun z =>
      mul_nonneg (mul_nonneg (hHA0 z) (hcoin0 z)) (hind01 B _).1),
      ← ofReal_integral_eq_lintegral_ofReal hint₂ (ae_of_all _ fun z =>
      mul_nonneg hδ (mul_nonneg (hHA0 z) (havg0 _ _ fun y => (hind01 B y).1))),
      integral_const_mul, ← hid]
  have hm : m₁ = m₂ := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨A, hA, B, hB, rfl⟩
      exact hrect A B hA hB
    · rw [← univ_prod_univ]
      exact hrect _ _ MeasurableSet.univ MeasurableSet.univ
  have hL : (∫ z, H z * (if z.2 n = true then (1 : ℝ) else 0) * ψ (z.1 t₀, z.1 t₁) ∂K xω) =
      ∫ p, ψ p ∂m₁ := by
    rw [hm₁def, integral_map hf₁.aemeasurable hψ.aestronglyMeasurable, hμ₁def,
      integral_withDensity_eq_integral_smul hw₁]
    congr 1
    funext z
    have hw : ((w₁ z : ℝ≥0) : ℝ) = H z * coin z :=
      Real.coe_toNNReal _ (mul_nonneg (hH0 z) (hcoin0 z))
    rw [NNReal.smul_def, smul_eq_mul, hw]
  have hint : Integrable (fun p => ψ (f₂ p)) (μ₂.prod U₀) := by
    have : IsFiniteMeasure (μ₂.prod U₀) := inferInstance
    exact Integrable.of_bound (hψ.comp hf₂).aestronglyMeasurable (max Cψ 0)
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 _)]; exact hψle _)
  have hR : (∫ p, ψ p ∂m₂) =
      δ * ∫ z, H z * endpointAverage i R (z.1 t₀) (fun y => ψ (z.1 t₀, y)) ∂K xω := by
    rw [hm₂def, integral_map hf₂.aemeasurable hψ.aestronglyMeasurable, integral_prod _ hint,
      hμ₂def, integral_withDensity_eq_integral_smul hw₂, ← integral_const_mul]
    congr 1
    funext z
    rw [endpointAverage_eq_integral_cond]
    have hw : ((w₂ z : ℝ≥0) : ℝ) = δ * H z := Real.coe_toNNReal _ (mul_nonneg hδ (hH0 z))
    rw [NNReal.smul_def, smul_eq_mul, hw, mul_assoc]
  rw [hL, hm, hR]

/-- The restart at the end of a successful interval and the uniform endpoint, for a future test
multiplied by a function of the endpoint displacement over the interval: the displacement is
uniform on the endpoint ball at the origin, jointly with the future from the endpoint. -/
theorem integral_future_endpoint_eq_uniformEndpointAverage (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) [IsProbabilityMeasure (K xω)]
    (hRestart : DeterministicRestartAt Δ K xω)
    (hUniform : UniformSuccessfulEndpointAt Δ δ R i K xω) (hδ : 0 ≤ δ)
    (hR0 : volume (endpointBall i R 0) ≠ ⊤) (hRpos : volume (endpointBall i R 0) ≠ 0)
    (m : ℕ) (hprob : ∀ᵐ z ∂K xω,
      IsProbabilityMeasure (K (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), xω.2)))
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y)
    (Ψ : Vec d × CoupledSample d → ℝ) (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) (hB0 : ∀ y, 0 ≤ B y)
    (hBeq : ∀ᵐ z ∂K xω,
      B (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) =
        ∫ w, Ψ (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), w)
          ∂K (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), xω.2)) :
    (∫ z, H z * (if z.2 m = true then (1 : ℝ) else 0) *
      g (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - z.1 ((m : ℝ≥0) * Δ)) *
      Ψ (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ),
        sampleTimeShift Δ z (((m + 1 : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
      δ * ∫ z, H z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => g (y - z.1 ((m : ℝ≥0) * Δ)) * B y) ∂K xω := by
  classical
  set t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ with htdef
  set s : ℝ≥0 := (m : ℝ≥0) * Δ with hsdef
  have hst : s ≤ t := by
    simp only [hsdef, htdef]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) zero_le
  let F : CoupledSample d × CoupledSample d → ℝ := fun q =>
    H q.1 * (if q.1.2 m = true then 1 else 0) * g (q.1.1 t - q.1.1 s) * Ψ (q.1.1 t, q.2)
  have hHfull := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have ht' : Measurable fun q : CoupledSample d × CoupledSample d => q.1.1 t :=
    (continuous_eval_const t).measurable.comp measurable_fst.fst
  have hs' : Measurable fun q : CoupledSample d × CoupledSample d => q.1.1 s :=
    (continuous_eval_const s).measurable.comp measurable_fst.fst
  have hF : Measurable F := by
    exact (((hHfull.comp measurable_fst).mul
      (Measurable.ite (((measurable_pi_apply m).comp measurable_fst.snd)
        (measurableSet_singleton true)) measurable_const measurable_const)).mul
      (hg.comp (ht'.sub hs'))).mul (hΨ.comp (ht'.prodMk measurable_snd))
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨Cg, hCg⟩ := hbg
  obtain ⟨CP, hCP⟩ := hbΨ
  have hbF : BoundedRealTest F := by
    refine ⟨max CH 0 * max Cg 0 * max CP 0, fun q => ?_⟩
    dsimp only [F]
    have hc : |(if q.1.2 m = true then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    rw [abs_mul, abs_mul, abs_mul]
    calc |H q.1| * |(if q.1.2 m = true then (1 : ℝ) else 0)| * |g (q.1.1 t - q.1.1 s)| *
          |Ψ (q.1.1 t, q.2)| ≤ max CH 0 * 1 * max Cg 0 * max CP 0 := by
          gcongr
          · exact (hCH _).trans (le_max_left _ _)
          · exact (hCg _).trans (le_max_left _ _)
          · exact (hCP _).trans (le_max_left _ _)
      _ = max CH 0 * max Cg 0 * max CP 0 := by ring
  have hHstop : ∀ z, H (Probability.stoppedHistorySample Δ (m + 1) z) = H z :=
    Probability.finiteHistory_test_stopped Δ (m + 1) H
      (hH.mono (finiteHistorySigma_mono Δ (Nat.le_succ m)) le_rfl)
  have hFstop : ∀ z w,
      F (Probability.stoppedHistorySample Δ (m + 1) z, w) =
        H z * (if z.2 m = true then 1 else 0) * g (z.1 t - z.1 s) * Ψ (z.1 t, w) := by
    intro z w
    dsimp only [F]
    rw [hHstop, Probability.stoppedHistorySample_bit Δ (m + 1) z m (Nat.lt_succ_self m),
      Probability.stoppedHistorySample_path Δ (m + 1) z t le_rfl,
      Probability.stoppedHistorySample_path Δ (m + 1) z s hst]
  have heq := integral_joint_of_deterministicRestartAt Δ K xω hRestart (m + 1)
    hprob F hF hbF
  simp_rw [hFstop, integral_const_mul] at heq
  refine heq.trans ?_
  have hjoint := uniformSuccessfulEndpointAt_joint Δ δ R i K xω hUniform hδ hR0 hRpos m H hH
    ⟨CH, hCH⟩ hH0 (fun p => g (p.2 - p.1) * B p.2)
    ((hg.comp (measurable_snd.sub measurable_fst)).mul (hB.comp measurable_snd))
    ⟨max Cg 0 * max (Classical.choose hbB) 0, fun p => by
      rw [abs_mul]
      exact mul_le_mul ((hCg _).trans (le_max_left _ _))
        ((Classical.choose_spec hbB _).trans (le_max_left _ _)) (abs_nonneg _)
        (le_max_right _ _)⟩
    (fun p => mul_nonneg (hg0 _) (hB0 _))
  refine (integral_congr_ae ?_).trans hjoint
  filter_upwards [hBeq] with z hz
  rw [← hz]
  ring

end EinsteinFull.Regeneration
