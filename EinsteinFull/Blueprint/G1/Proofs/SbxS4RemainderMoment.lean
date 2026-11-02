import EinsteinFull.Blueprint.Foundation.node_e_u3A_generators_u23_real_u2D_semigroup
import EinsteinRelation.Diffusion.GMPFamilyAPI
import EinsteinFull.Calculus.ComplexForceSemigroupSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Calculus.C3RemainderMomentSupport
import EinsteinFull.Blueprint.G1.node_rt_u3A_remainder_u2D_moment
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import EinsteinRelation.Correctors.SpatialWeakLocalization
import PDEFoundation.Sobolev.Ch4.LipschitzTest
import EinsteinFull.Work.W5.GantertWeightedFormDynkinProof
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.C8GMPMartingale
import EinsteinFull.Work.W1.GMPFullPastRestartSupport
import EinsteinFull.Calculus.S4CountableBasicSupport
import EinsteinFull.Calculus.S4MartingaleVarianceSupport
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
The deterministic-time remainder estimate on the actual supplied coupling.
A large power makes the stationary evolution growth as small as needed;
the real semigroup identifies the supplied GMP endpoint law, and the regeneration
tails control conditioning on the no-return event.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull

open EinsteinRelation

/-- The positive power of a genuine finite-moment observable belongs to complex L². -/
theorem sbxS4_memLp_power {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) μ) :
    MemLp (fun x => ((‖F x‖ ^ q : ℝ) : ℂ)) 2 μ := by
  have hm := (hF.aestronglyMeasurable.norm.aemeasurable.pow_const q).aestronglyMeasurable
  have hc := (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
  apply memLp_iff.mpr
  have heq : eLpNorm (fun x => ((‖F x‖ ^ q : ℝ) : ℂ)) 2 μ =
      eLpNorm (fun x => ‖F x‖ ^ q) 2 μ :=
    eLpNorm_congr_norm_ae hc hm (Filter.Eventually.of_forall fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs])
  rw [heq, eLpNorm_norm_rpow F hF.aestronglyMeasurable hq]
  exact ENNReal.rpow_lt_top_of_nonneg hq.le hF.eLpNorm_ne_top

/-- The actual L² class of the positive power, retaining the given observable. -/
def sbxS4PowerLift {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) μ) : Lp ℂ 2 μ :=
  (sbxS4_memLp_power hq hF).toLp (fun x => ((‖F x‖ ^ q : ℝ) : ℂ))

/-- The power lift represents the literal pointwise power almost everywhere. -/
theorem sbxS4PowerLift_coeFn {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) μ) :
    (sbxS4PowerLift hq hF : α → ℂ) =ᵐ[μ] fun x => ((‖F x‖ ^ q : ℝ) : ℂ) :=
  (sbxS4_memLp_power hq hF).coeFn_toLp

/-- The L² norm of the power lift is the corresponding power of the original norm. -/
theorem sbxS4PowerLift_norm {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {F : α → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) μ) :
    ‖sbxS4PowerLift hq hF‖ = (eLpNorm F (2 * ENNReal.ofReal q) μ).toReal ^ q := by
  rw [sbxS4PowerLift, Lp.norm_toLp]
  have hm := (hF.aestronglyMeasurable.norm.aemeasurable.pow_const q).aestronglyMeasurable
  have hc := (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
  rw [eLpNorm_congr_norm_ae hc hm (Filter.Eventually.of_forall fun x => by
    rw [Complex.norm_real, Real.norm_eq_abs]),
    eLpNorm_norm_rpow F hF.aestronglyMeasurable hq, ENNReal.toReal_rpow]

/-- The actual stationary evolution controls its bilinear L² pairing. -/
theorem sbxS4_semigroup_pairing_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (t : ℝ≥0)
    (F G : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ ω, F ω * forcedComplexEvolution Q i (lam : ℂ) t G ω ∂reducedLaw Q‖ ≤
      Real.exp (complexForceShift d Λ₀ (lam : ℂ) * (t : ℝ)) * ‖F‖ * ‖G‖ := by
  rw [← inner_complexL2Conjugation_eq_integral_mul]
  calc
    _ ≤ ‖complexL2Conjugation (reducedLaw Q) F‖ *
        ‖forcedComplexEvolution Q i (lam : ℂ) t G‖ := norm_inner_le_norm _ _
    _ ≤ ‖F‖ * (Real.exp (complexForceShift d Λ₀ (lam : ℂ) * (t : ℝ)) * ‖G‖) := by
      rw [norm_complexL2Conjugation]
      exact mul_le_mul_of_nonneg_left
        (norm_forcedComplexEvolution_apply_le Q i (lam : ℂ) t G) (norm_nonneg F)
    _ = _ := by ring

/-- Rooting a high-power pairing divides the force growth rate by the power.
No path-law identification or Girsanov estimate is a premise. -/
theorem sbxS4_semigroup_power_pairing_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (t : ℝ≥0)
    {F G : FieldPair d → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) (reducedLaw Q))
    (hG : MemLp G (2 * ENNReal.ofReal q) (reducedLaw Q)) :
    ‖∫ ω, sbxS4PowerLift hq hF ω *
      forcedComplexEvolution Q i (lam : ℂ) t (sbxS4PowerLift hq hG) ω
        ∂reducedLaw Q‖ ^ q⁻¹ ≤
      Real.exp (complexForceShift d Λ₀ (lam : ℂ) * (t : ℝ) / q) *
        (eLpNorm F (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal *
        (eLpNorm G (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal := by
  have h := Real.rpow_le_rpow (norm_nonneg _)
    (sbxS4_semigroup_pairing_bound Q i lam t (sbxS4PowerLift hq hF)
      (sbxS4PowerLift hq hG)) (inv_pos.mpr hq).le
  rw [sbxS4PowerLift_norm, sbxS4PowerLift_norm,
    Real.mul_rpow (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ENNReal.toReal_nonneg _))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    Real.mul_rpow (Real.exp_pos _).le (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← Real.rpow_mul ENNReal.toReal_nonneg,
    ← Real.rpow_mul ENNReal.toReal_nonneg, mul_inv_cancel₀ hq.ne', Real.rpow_one,
    Real.rpow_one, ← Real.exp_mul] at h
  simpa only [div_eq_mul_inv] using h

/-- A single power chosen before force and time makes the rooted structural
growth rate smaller than any prescribed positive decay budget. -/
theorem sbxS4_exists_power_small_growth (d : ℕ) (Λ₀ b : ℝ) (hb : 0 < b) :
    ∃ q : ℝ, 2 ≤ q ∧ ∀ (lam : ℝ) (t : ℝ≥0),
      complexForceShift d Λ₀ (lam : ℂ) * (t : ℝ) / q ≤
        b / 4 * lam ^ 2 * (t : ℝ) := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  let a := |K| * ((d : ℝ) * K) ^ 2
  have ha : 0 ≤ a := mul_nonneg (abs_nonneg K) (sq_nonneg _)
  let q := 2 + 4 * a / b
  have hq : 2 ≤ q := le_add_of_nonneg_right (div_nonneg (by positivity) hb.le)
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  refine ⟨q, hq, ?_⟩
  intro lam t
  have hqeq : b * q = 2 * b + 4 * a := by
    dsimp only [q]
    field_simp [hb.ne']
  have hcoef : a / q ≤ b / 4 := by
    apply (div_le_iff₀ hqpos).mpr
    nlinarith only [hqeq, hb]
  have hshift : complexForceShift d Λ₀ (lam : ℂ) ≤ a * lam ^ 2 := by
    calc
      _ = (K * ((d : ℝ) * K) ^ 2) * lam ^ 2 := by
        simp only [complexForceShift, Complex.norm_real, Real.norm_eq_abs,
          mul_pow, sq_abs]
        dsimp only [K]
        ring
      _ ≤ (|K| * ((d : ℝ) * K) ^ 2) * lam ^ 2 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self K) (sq_nonneg _)) (sq_nonneg _)
  calc
    _ ≤ a * lam ^ 2 * (t : ℝ) / q :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hshift t.coe_nonneg) hqpos.le
    _ = a / q * lam ^ 2 * (t : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (sq_nonneg lam)) t.coe_nonneg

/-- One finite exponent controls all stationary power pairings with the chosen
quadratic-force growth budget, uniformly in the law, force and time. -/
theorem sbxS4_exists_semigroup_power_pairing_small_growth
    (d : ℕ) (Λ₀ r₀ b : ℝ) (hb : 0 < b) :
    ∃ (q : ℝ) (hq : 0 < q), 2 ≤ q ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (t : ℝ≥0)
        (F G : FieldPair d → ℝ)
        (hF : MemLp F (2 * ENNReal.ofReal q) (reducedLaw Q))
        (hG : MemLp G (2 * ENNReal.ofReal q) (reducedLaw Q)),
      ‖∫ ω, sbxS4PowerLift hq hF ω *
        forcedComplexEvolution Q i (lam : ℂ) t (sbxS4PowerLift hq hG) ω
          ∂reducedLaw Q‖ ^ q⁻¹ ≤
        Real.exp (b / 4 * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal *
          (eLpNorm G (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal := by
  obtain ⟨q, hq, hbudget⟩ := sbxS4_exists_power_small_growth d Λ₀ b hb
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  refine ⟨q, hqpos, hq, ?_⟩
  intro Q i lam t F G hF hG
  exact (sbxS4_semigroup_power_pairing_bound Q i lam t hqpos hF hG).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hbudget lam t))
        ENNReal.toReal_nonneg) ENNReal.toReal_nonneg)

/-- Restricting a finite moment to an event gives integrability and the exact
Hölder event factor needed for the remainder estimate. -/
theorem sbxS4_restricted_integral_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {f : α → ℝ} {q : ℝ}
    (hq : 1 ≤ q) (hf : MemLp f (ENNReal.ofReal q) μ) (A : Set α) :
    IntegrableOn f A μ ∧
      |∫ x in A, f x ∂μ| ≤
        (eLpNorm f (ENNReal.ofReal q) μ).toReal * (μ A).toReal ^ (1 - 1 / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hq' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hfm := hf.restrict A
  refine ⟨hfm.integrable hq', ?_⟩
  have hexp : 0 ≤ 1 - 1 / q := sub_nonneg.mpr ((div_le_one hqpos).mpr hq)
  have he := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq' hfm.aestronglyMeasurable
  simp only [ENNReal.toReal_one, div_one, ENNReal.toReal_ofReal hqpos.le,
    Measure.restrict_apply_univ] at he
  have he' := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hfm.eLpNorm_ne_top
      (ENNReal.rpow_lt_top_of_nonneg hexp (measure_ne_top μ A)).ne) he
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at he'
  calc
    _ = ‖∫ x in A, f x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in A, ‖f x‖ ∂μ := norm_integral_le_integral_norm _
    _ = (eLpNorm f 1 (μ.restrict A)).toReal := by
      rw [eLpNorm_one_eq_lintegral_enorm hfm.aestronglyMeasurable]
      exact integral_norm_eq_lintegral_enorm hfm.aestronglyMeasurable
    _ ≤ (eLpNorm f (ENNReal.ofReal q) (μ.restrict A)).toReal *
        (μ A).toReal ^ (1 - 1 / q) := he'
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (ENNReal.toReal_mono hf.eLpNorm_ne_top
        (eLpNorm_mono_measure f Measure.restrict_le_self))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _)

/-- The event factor absorbs the selected semigroup growth rate, retaining
uniform decay for every exponent at least two. -/
theorem sbxS4_event_decay {B b J s q m : ℝ}
    (hB : 0 < B) (hb : 0 ≤ b) (hJ : 0 ≤ J) (hs : 0 ≤ s)
    (hq : 2 ≤ q) (hm : 0 ≤ m)
    (hmB : m ≤ B * Real.exp (B * J - b * s)) :
    Real.exp (b / 4 * s) * m ^ (1 - 1 / q) ≤
      max 1 B * Real.exp (B * J - b / 4 * s) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hrec : 0 ≤ 1 / q := div_nonneg zero_le_one hqpos.le
  have hhalf : 1 / q ≤ 1 / 2 :=
    (div_le_div_iff₀ hqpos (by norm_num)).mpr (by linarith only [hq])
  let r := 1 - 1 / q
  have hrhalf : 1 / 2 ≤ r := by dsimp only [r]; linarith only [hhalf]
  have hrpos : 0 ≤ r := le_trans (by norm_num) hrhalf
  have hrone : r ≤ 1 := by dsimp only [r]; linarith only [hrec]
  have hBpow : B ^ r ≤ max 1 B := by
    by_cases hB1 : B ≤ 1
    · exact (Real.rpow_le_one hB.le hB1 hrpos).trans (le_max_left _ _)
    · exact (Real.rpow_le_self_of_one_le (le_of_not_ge hB1) hrone).trans
        (le_max_right _ _)
  have hJmul := mul_le_mul_of_nonneg_left hrone (mul_nonneg hB.le hJ)
  have hsmul := mul_le_mul_of_nonneg_left hrhalf (mul_nonneg hb hs)
  have hexp : b / 4 * s + (B * J - b * s) * r ≤ B * J - b / 4 * s := by
    nlinarith only [hJmul, hsmul]
  calc
    _ ≤ Real.exp (b / 4 * s) * (B * Real.exp (B * J - b * s)) ^ r :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hm hmB hrpos)
        (Real.exp_pos _).le
    _ = B ^ r * Real.exp (b / 4 * s + (B * J - b * s) * r) := by
      rw [Real.mul_rpow hB.le (Real.exp_pos _).le, ← Real.exp_mul,
        Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul hBpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
      (zero_le_one.trans (le_max_left _ _))

/-- A continuous strictly positive weight controls unweighted moments on each
compact set. This supplies the local Sobolev input for Lipschitz flux tests. -/
theorem sbxS4_memLp_restrict_compact_of_density {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] {f : Vec d → E} {p : ℝ≥0∞}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (hf : MemLp f p (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (K : Set (Vec d)) (hK : IsCompact K) : MemLp f p (volume.restrict K) := by
  by_cases hK0 : K = ∅
  · simp [hK0]
  have hKnon : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK0
  obtain ⟨z, _, hzmin⟩ := hK.exists_isMinOn hKnon hρ.continuousOn
  have hzmin' : ∀ x ∈ K, ρ z ≤ ρ x := by
    simpa [IsMinOn, IsMinFilter] using hzmin
  have hz0 : ENNReal.ofReal (ρ z) ≠ 0 := (ENNReal.ofReal_pos.mpr (hρpos z)).ne'
  have hcmp : ENNReal.ofReal (ρ z) • volume.restrict K ≤
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K := by
    rw [← withDensity_const, restrict_withDensity hK.isClosed.measurableSet]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet] with x hx
    exact ENNReal.ofReal_le_ofReal (hzmin' x hx)
  have hback : volume.restrict K ≤ (ENNReal.ofReal (ρ z))⁻¹ •
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K := by
    calc
      _ = (ENNReal.ofReal (ρ z))⁻¹ •
          (ENNReal.ofReal (ρ z) • volume.restrict K) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hz0 ENNReal.ofReal_ne_top, one_smul]
      _ ≤ _ := by gcongr
  exact (hf.restrict K).of_measure_le_smul (ENNReal.inv_ne_top.mpr hz0) hback

/-- A weighted Sobolev representative belongs locally to the unweighted `H¹`
graph, with its value and gradient representatives preserved literally. -/
def sbxS4WeightedGraphLocalH1 {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    {U K : Set (Vec d)} (hK : IsCompact K) (hUK : U ⊆ K) : PDE.H1Function U where
  toFun := u.value
  grad := fun x => WithLp.ofLp (u.weakGradient x)
  memL2 := (sbxS4_memLp_restrict_compact_of_density ρ hρ hρpos
    u.value_memLp K hK).mono_measure (Measure.restrict_mono hUK le_rfl)
  gradMemL2 := fun j => by
    have hj := u.gradient_memLp.continuousLinearMap_comp
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    exact (sbxS4_memLp_restrict_compact_of_density ρ hρ hρpos
      hj K hK).mono_measure (Measure.restrict_mono hUK le_rfl)
  hasWeakGradient := by
    have h := Correctors.hasWeakGradient_mono (Set.subset_univ U) u.distributionalGradient
    intro j ψ hψ hc hs
    exact (h j).2.2 ψ ⟨hψ, hc, hs⟩

/-- Weighted weak gradients can be tested against compactly supported Lipschitz
functions. No differentiability of the weight is required. -/
theorem sbxS4_weightedGraph_integral_mul_partial_lip {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : PDE.Ch4Infra.EucLip L ψ) (hL : 0 ≤ L)
    (hc : HasCompactSupport ψ) (j : Fin d) :
    (∫ x, u.value x * coordinateDerivative j ψ x ∂volume) =
      -(∫ x, WithLp.ofLp (u.weakGradient x) j * ψ x ∂volume) := by
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_ball (0 : Vec d)
  let v := sbxS4WeightedGraphLocalH1 ρ hρ hρpos u (isCompact_closedBall (0 : Vec d) R)
    (Metric.ball_subset_closedBall : Metric.ball (0 : Vec d) R ⊆ Metric.closedBall 0 R)
  have h := PDE.Ch4Infra.H1Function.integral_mul_partial_lip_eq
    Metric.isOpen_ball v hψ hL hc hR j
  change (∫ x in Metric.ball (0 : Vec d) R, u.value x * coordinateDerivative j ψ x) =
    -(∫ x in Metric.ball (0 : Vec d) R, WithLp.ofLp (u.weakGradient x) j * ψ x) at h
  have hzero : ∀ x, x ∉ Metric.ball (0 : Vec d) R → ψ x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun ht => hx (hR ht))
  have hd : ∀ x, x ∉ Metric.ball (0 : Vec d) R → coordinateDerivative j ψ x = 0 := by
    intro x hx
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ (fun ht => hx (hR ht)),
      zero_apply]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hd x hx, mul_zero]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by rw [hzero x hx, mul_zero])] at h
  exact h

/-- The classical coordinate derivative of a compact Lipschitz test is locally
square integrable on its compact support, including its literal values on the
exceptional set of nondifferentiability. -/
theorem sbxS4_lip_partial_memLp {d : ℕ} {L : ℝ} {ψ : Vec d → ℝ}
    (hψ : PDE.Ch4Infra.EucLip L ψ) (hL : 0 ≤ L) (hc : HasCompactSupport ψ)
    (j : Fin d) :
    MemLp (coordinateDerivative j ψ) 2 (volume.restrict (tsupport ψ)) := by
  have : IsFiniteMeasure (volume.restrict (tsupport ψ)) :=
    ⟨by simpa using hc.isCompact.measure_lt_top⟩
  have hm : AEStronglyMeasurable (coordinateDerivative j ψ) volume :=
    (measurable_fderiv_apply_const ℝ ψ (unitVector j)).aestronglyMeasurable
  apply MemLp.of_bound (hm.mono_measure Measure.restrict_le_self) L
  filter_upwards [ae_restrict_of_ae (hψ.ae_differentiableAt hL)] with x hx
  exact Real.norm_eq_abs _ ▸ hψ.abs_partialDeriv_le hL hx j

/-- Both weak-gradient pairings with a compact Lipschitz test are genuine
integrals. The weighted Sobolev graph supplies local `L²` for both factors. -/
theorem sbxS4_weightedGraph_lip_test_integrable {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    {L : ℝ} {ψ : Vec d → ℝ} (hψ : PDE.Ch4Infra.EucLip L ψ) (hL : 0 ≤ L)
    (hc : HasCompactSupport ψ) (j : Fin d) :
    Integrable (fun x => u.value x * coordinateDerivative j ψ x) volume ∧
      Integrable (fun x => WithLp.ofLp (u.weakGradient x) j * ψ x) volume := by
  have hv := sbxS4_memLp_restrict_compact_of_density ρ hρ hρpos
    u.value_memLp (tsupport ψ) hc.isCompact
  have hg := sbxS4_memLp_restrict_compact_of_density ρ hρ hρpos
    (u.gradient_memLp.continuousLinearMap_comp
      (EuclideanSpace.proj j : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ))
    (tsupport ψ) hc.isCompact
  constructor
  · have hi : IntegrableOn (fun x => u.value x * coordinateDerivative j ψ x)
        (tsupport ψ) volume := hv.integrable_mul (sbxS4_lip_partial_memLp hψ hL hc j)
    apply hi.integrable_of_forall_notMem_eq_zero
    intro x hx
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx,
      zero_apply, mul_zero]
  · have hψlp : MemLp ψ 2 volume := (hψ.continuous hL).memLp_of_hasCompactSupport hc
    have hi : IntegrableOn (fun x => WithLp.ofLp (u.weakGradient x) j * ψ x)
        (tsupport ψ) volume := hg.integrable_mul (hψlp.restrict (tsupport ψ))
    apply hi.integrable_of_forall_notMem_eq_zero
    intro x hx
    simp only [image_eq_zero_of_notMem_tsupport hx, mul_zero]

/-- Divergence integration by parts for compact Lipschitz fluxes against the
full weighted weak-gradient graph. This needs only a continuous positive weight. -/
theorem sbxS4_weightedGraph_integral_divergence_lip {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (F : Vec d → Vec d) (L : Fin d → ℝ)
    (hF : ∀ j, PDE.Ch4Infra.EucLip (L j) (fun x => F x j))
    (hL : ∀ j, 0 ≤ L j) (hc : ∀ j, HasCompactSupport (fun x => F x j)) :
    (∫ x, u.value x * divergence F x ∂volume) =
      -(∫ x, dot (WithLp.ofLp (u.weakGradient x)) (F x) ∂volume) := by
  have hi := fun j => sbxS4_weightedGraph_lip_test_integrable ρ hρ hρpos u
    (hF j) (hL j) (hc j) j
  simp only [divergence, dot, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => (hi j).1),
    integral_finsetSum _ (fun j _ => (hi j).2), ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ =>
    sbxS4_weightedGraph_integral_mul_partial_lip ρ hρ hρpos u (hF j) (hL j) (hc j) j

open External.GantertSection7Support

/-- The actual exponentially weighted compact-test flux is Lipschitz even when
the coefficient field has only the regularity in the source assumptions. -/
theorem sbxS4_physicalFlux_eucLip {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (j : Fin d) :
    ∃ L : ℝ, 0 ≤ L ∧ PDE.Ch4Infra.EucLip L
      (fun x => External.GantertSection7Support.physicalForceWeight hd lam x *
        (reducedCoefficient ω x).mulVec (gradient f x) j) := by
  classical
  let w := External.GantertSection7Support.physicalForceWeight hd lam
  let g : Fin d → Vec d → ℝ := fun k x => w x * coordinateDerivative k f x
  have hg k : ContDiff ℝ (⊤ : ℕ∞) (g k) :=
    ((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp).mul
      (Work.W5.gantert_contDiff_coordinateDerivative hf k)
  have hgc k : HasCompactSupport (g k) := (hc.fderiv_apply (𝕜 := ℝ) (unitVector k)).mul_left
  have hgl k : ∃ L : ℝ, 0 ≤ L ∧ PDE.Ch4Infra.EucLip L (g k) :=
    PDE.Ch4Infra.EucLip.of_contDiff_hasCompactSupport ((hg k).of_le (by simp)) (hgc k)
  choose L hL hl using hgl
  have hgb k : ∃ N : ℝ, ∀ x, |g k x| ≤ N := by
    simpa only [Real.norm_eq_abs] using
      (hg k).continuous.bounded_above_of_compact_support (hgc k)
  choose N hN using hgb
  have hN0 k : 0 ≤ N k := (abs_nonneg (g k 0)).trans (hN k 0)
  let M : ℝ := Real.exp (2 * Λ) * Λ
  let A : ℝ≥0 := Real.toNNReal (Real.exp (2 * Λ) * (2 * Λ ^ 2 + Λ) * Real.sqrt d)
  have ha k : PDE.Ch4Infra.EucLip (A : ℝ) (fun x => reducedCoefficient ω x j k) :=
    PDE.Ch4Infra.EucLip.of_norm A.coe_nonneg fun x y => by
      have h := (reducedCoefficient_lipschitz hΛ hω j k).dist_le_mul x y
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, A] using h
  have hp k : PDE.Ch4Infra.EucLip (M * L k + N k * A)
      (fun x => reducedCoefficient ω x j k * g k x) :=
    (ha k).mul (hl k) (fun x => abs_reducedCoefficient_le hΛ hω x j k) (hN k)
  refine ⟨∑ k, (M * L k + N k * A), Finset.sum_nonneg (fun k _ => ?_), ?_⟩
  · exact add_nonneg (mul_nonneg (mul_pos (Real.exp_pos _) hΛ).le (hL k))
      (mul_nonneg (hN0 k) A.coe_nonneg)
  · have he : (fun x => w x * (reducedCoefficient ω x).mulVec (gradient f x) j) =
        (fun x => ∑ k, reducedCoefficient ω x j k * g k x) := by
      funext x
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, g, gradient]
      exact Finset.sum_congr rfl fun k _ => by ring
    change PDE.Ch4Infra.EucLip _ (fun x => w x * (reducedCoefficient ω x).mulVec (gradient f x) j)
    rw [he]
    intro x y
    calc
      _ = |∑ k, (reducedCoefficient ω x j k * g k x -
          reducedCoefficient ω y j k * g k y)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ k, |reducedCoefficient ω x j k * g k x -
          reducedCoefficient ω y j k * g k y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, (M * L k + N k * A) * PDE.vecEuclideanNorm (x - y) :=
        Finset.sum_le_sum fun k _ => hp k x y
      _ = _ := (Finset.sum_mul _ _ _).symm

/-- The reversible-density divergence identity holds almost everywhere for the
actual Lipschitz coefficient field. No smooth-field hypothesis is introduced. -/
theorem sbxS4_density_mul_physicalGenerator_ae {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (fun x => physicalReversibleDensity ω hd lam x *
      physicalGenerator (firstCoordinateIndex hd) ω lam f x) =ᵐ[volume]
    (fun x => (1 / 2 : ℝ) * divergence
      (fun y => physicalForceWeight hd lam y •
        (reducedCoefficient ω y).mulVec (gradient f y)) x) := by
  have hflux : ∀ j : Fin d, ∀ᵐ x ∂volume, DifferentiableAt ℝ
      (fun y => (reducedCoefficient ω y).mulVec (gradient f y) j) x := by
    intro j
    obtain ⟨L, hL, hl⟩ := sbxS4_physicalFlux_eucLip hd hΛ hω 0 hf hc j
    simpa only [physicalForceWeight, mul_zero, zero_mul, Real.exp_zero, one_mul]
      using hl.ae_differentiableAt hL
  have hw : Differentiable ℝ (physicalForceWeight hd lam : Vec d → ℝ) :=
    ((contDiff_const.mul (contDiff_apply ℝ ℝ (firstCoordinateIndex hd))).exp :
      ContDiff ℝ (⊤ : ℕ∞) _).differentiable (by simp)
  filter_upwards [ae_all_iff.mpr hflux] with x hx
  have hdiv : divergence
      (fun y => physicalForceWeight hd lam y •
        (reducedCoefficient ω y).mulVec (gradient f y)) x =
      physicalForceWeight hd lam x * divergence
        (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x +
      dot (gradient (physicalForceWeight hd lam) x)
        ((reducedCoefficient ω x).mulVec (gradient f x)) := by
    change (∑ j, fderiv ℝ (fun y => physicalForceWeight hd lam y *
        (reducedCoefficient ω y).mulVec (gradient f y) j) x (unitVector j)) =
      physicalForceWeight hd lam x *
        (∑ j, fderiv ℝ (fun y => (reducedCoefficient ω y).mulVec (gradient f y) j)
          x (unitVector j)) +
      ∑ j, fderiv ℝ (physicalForceWeight hd lam) x (unitVector j) *
        (reducedCoefficient ω x).mulVec (gradient f x) j
    simp only [fderiv_fun_mul (hw x) (hx _), add_apply,
      smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    simp only [mul_comm]
  have hsym := reducedCoefficient_symm hω x
  have hforce : dot ((reducedCoefficient ω x).mulVec (unitVector (firstCoordinateIndex hd)))
      (gradient f x) = (reducedCoefficient ω x).mulVec (gradient f x) (firstCoordinateIndex hd) := by
    simp only [dot, Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    apply Finset.sum_congr rfl
    intro j _
    have he := congrFun (congrFun hsym j) (firstCoordinateIndex hd)
    exact congrArg (fun a => a * gradient f x j) he.symm
  rw [hdiv]
  have hdot : dot (gradient (physicalForceWeight hd lam) x)
      ((reducedCoefficient ω x).mulVec (gradient f x)) =
      physicalForceWeight hd lam x * (2 * lam) *
        (reducedCoefficient ω x).mulVec (gradient f x) (firstCoordinateIndex hd) := by
    simp only [dot, gradient, Work.W5.gantert_coordinateDerivative_forceWeight, unitVector,
      Pi.single_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hdot]
  change (physicalForceWeight hd lam x * clockDensity ω x) * _ = _
  rw [mul_assoc, clockDensity_mul_physicalGenerator]
  unfold reducedGenerator
  rw [hforce]
  ring

/-- Compact smooth tests satisfy the actual physical form identity against the
full Sobolev graph for every regular field pair, without a smooth-field premise. -/
theorem sbxS4_fullForm_compactTest {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (External.GantertSection7Support.physicalForceMeasure hd lam)) :
    (∫ x, u.value x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
      ∂physicalReversibleMeasure ω hd lam) =
    -(∫ x, (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (gradient f x)) ∂physicalReversibleMeasure ω hd lam) := by
  let F : Vec d → Vec d := fun y => physicalForceWeight hd lam y •
    (reducedCoefficient ω y).mulVec (gradient f y)
  choose L hL hF using fun j => sbxS4_physicalFlux_eucLip hd hΛ hω lam hf hc j
  have hFc j : HasCompactSupport (fun x => F x j) := by
    apply hc.mono'
    intro x hx
    by_contra hxnot
    have hg : gradient f x = 0 := by
      ext k
      simp only [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxnot,
        zero_apply, Pi.zero_apply]
    exact hx (by simp [F, hg])
  have h := sbxS4_weightedGraph_integral_divergence_lip
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) u F L hF hL hFc
  rw [Work.W5.gantert_integral_physicalMeasure, Work.W5.gantert_integral_physicalMeasure]
  calc
    _ = (1 / 2 : ℝ) * ∫ x, u.value x * divergence F x ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [sbxS4_density_mul_physicalGenerator_ae hd hΛ hω lam hf hc] with x he
      change physicalReversibleDensity ω hd lam x * _ =
        (1 / 2 : ℝ) * (u.value x * divergence F x)
      rw [mul_left_comm, he]
      ring
    _ = -(∫ x, physicalReversibleDensity ω hd lam x * ((1 / 2 : ℝ) *
        dot (WithLp.ofLp (u.weakGradient x)) ((ω.1 x).mulVec (gradient f x))) ∂volume) := by
      rw [h, mul_neg, ← integral_const_mul]
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change (1 / 2 : ℝ) * dot _ (physicalForceWeight hd lam x •
          (reducedCoefficient ω x).mulVec (gradient f x)) = _
        rw [reducedCoefficient, Matrix.smul_mulVec]
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
          physicalReversibleDensity]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Total coordinate derivatives of a globally Lipschitz flux have a uniform
bound, including the derivative's totalized values at exceptional points. -/
theorem sbxS4_divergence_bounded {d : ℕ} (F : Vec d → Vec d)
    (hF : ∀ j, ∃ L : ℝ, 0 ≤ L ∧ PDE.Ch4Infra.EucLip L (fun x => F x j)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |divergence F x| ≤ B := by
  choose L hL hl using hF
  let C : Fin d → ℝ≥0 := fun j => ⟨L j * Real.sqrt d, mul_nonneg (hL j) (Real.sqrt_nonneg _)⟩
  refine ⟨∑ j, (C j : ℝ) * ‖unitVector j‖,
    Finset.sum_nonneg (fun j _ => mul_nonneg (C j).coe_nonneg (norm_nonneg _)), ?_⟩
  intro x
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [← Real.norm_eq_abs]
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_fderiv_le_of_lipschitz ℝ ((hl j).lipschitzWith (hL j))) (norm_nonneg _))

/-- The literal physical generator of a compact smooth test is globally bounded
for the regular Lipschitz coefficients occurring in the source theorem. -/
theorem sbxS4_physicalGenerator_bounded {d : ℕ} (hd : 2 ≤ d) (i : Fin d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |physicalGenerator i ω lam f x| ≤ B := by
  have hflux j : ∃ L : ℝ, 0 ≤ L ∧ PDE.Ch4Infra.EucLip L
      (fun x => (reducedCoefficient ω x).mulVec (gradient f x) j) := by
    simpa only [physicalForceWeight, mul_zero, zero_mul, Real.exp_zero, one_mul] using
      sbxS4_physicalFlux_eucLip hd hΛ hω 0 hf hc j
  obtain ⟨B, hB, hbound⟩ := sbxS4_divergence_bounded _ hflux
  let g : Vec d → ℝ := fun x => lam * dot ((ω.1 x).mulVec (unitVector i)) (gradient f x)
  have hg : Continuous g := by
    apply continuous_const.mul
    unfold dot
    apply continuous_finsetSum
    intro j _
    exact ((continuous_apply j).comp (ω.1.continuous.matrix_mulVec continuous_const)).mul
      (Work.W5.gantert_contDiff_coordinateDerivative hf j).continuous
  have hgc : HasCompactSupport g := by
    apply hc.mono'
    intro x hx
    by_contra hn
    have hz : gradient f x = 0 := by
      ext j
      simp only [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn,
        zero_apply, Pi.zero_apply]
    exact hx (by simp [g, hz, dot])
  obtain ⟨D, hD⟩ := hg.bounded_above_of_compact_support hgc
  have hD0 : 0 ≤ D := (norm_nonneg (g 0)).trans (hD 0)
  refine ⟨Real.exp (2 * Λ) / 2 * B + D, by positivity, fun x => ?_⟩
  refine (abs_add_le _ _).trans (add_le_add ?_ (by simpa only [Real.norm_eq_abs] using hD x))
  rw [abs_mul, abs_of_pos (div_pos (Real.exp_pos _) (by norm_num))]
  apply mul_le_mul _ (hbound x) (abs_nonneg _) (by positivity)
  exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr
    (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hω.2.1 x)) (by norm_num)))
    (by norm_num)

/-- The literal bounded compact generator belongs to the physical L² space;
no continuity of its measurable derivative representative is required. -/
theorem sbxS4_memLp_physicalGenerator {d : ℕ} (hd : 2 ≤ d) (i : Fin d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    MemLp (physicalGenerator i ω lam f) 2 (physicalReversibleMeasure ω hd lam) := by
  let μ := physicalReversibleMeasure ω hd lam
  have : IsLocallyFiniteMeasure μ := Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  have : IsFiniteMeasure (μ.restrict (tsupport f)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hc.isCompact.measure_lt_top (μ := μ)⟩
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd i hΛ hω lam hf hc
  have hm : MemLp (physicalGenerator i ω lam f) 2 (μ.restrict (tsupport f)) :=
    MemLp.of_bound (measurable_physicalGenerator i ω lam f).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hi := (memLp_indicator_iff_restrict (isClosed_tsupport f).measurableSet).mpr hm
  convert hi using 1
  symm
  exact Set.indicator_eq_self.mpr (Work.W5.gantert_physicalGenerator_support_subset i ω lam f)

open C8GMP EinsteinRelation.SpatialDirichlet Filter
open scoped Topology

/-- The mixed full-domain physical form has the actual physical generator as
 its compact-test representer. The first argument ranges over the entire domain. -/
theorem sbxS4_compactTest_fullDomain_pairing {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (hΛ : 0 < Λ)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u
      (compactTestDomain hd lam f hf hc) =
    -(∫ x, (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x *
      physicalGenerator (firstCoordinateIndex hd) ω lam f x
      ∂physicalReversibleMeasure ω hd lam) := by
  let gu := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  have hibp := sbxS4_fullForm_compactTest hd hΛ hω lam hf hc gu
  rw [hibp, neg_neg]
  apply integral_congr_ae
  filter_upwards [compactTestDomain_gradient hd Λ ω hω lam f hf hc] with x hx
  change (1 / 2 : ℝ) * dot (WithLp.ofLp (gu.weakGradient x))
    ((ω.1 x).mulVec (WithLp.ofLp
      ((densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (compactTestDomain hd lam f hf hc)).weakGradient x))) = _
  rw [hx]
  rfl

/-- The compact-test physical generator as an element of the actual L² space. -/
def sbxS4CompactTestGeneratorL2 {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd) hΛ hω lam hf hc).toLp _

/-- The full physical form represents the compact-test generator in the actual
 L² inner product, with no restriction of the first argument to smooth tests. -/
theorem sbxS4_compactTest_fullDomain_generatorInner {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (hΛ : 0 < Λ)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u
      (compactTestDomain hd lam f hf hc) =
    -inner ℝ (sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u)
      (sbxS4CompactTestGeneratorL2 hd hΛ hω lam f hf hc) := by
  rw [sbxS4_compactTest_fullDomain_pairing hd Λ ω hω lam hΛ u f hf hc]
  erw [L2.inner_def]
  congr 1
  let gu := sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
  apply integral_congr_ae
  filter_upwards [gu.value_memLp.coeFn_toLp,
    (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd) hΛ hω lam hf hc).coeFn_toLp]
    with x hx hy
  change gu.value x * physicalGenerator (firstCoordinateIndex hd) ω lam f x =
    inner ℝ (gu.value_memLp.toLp gu.value x)
      (sbxS4CompactTestGeneratorL2 hd hΛ hω lam f hf hc x)
  rw [hx]
  change _ = inner ℝ (gu.value x)
    ((sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd) hΛ hω lam hf hc).toLp _ x)
  rw [hy]
  simp [RCLike.inner_apply, mul_comm]


/-- The actual compact-test energy equals minus the physical generator pairing. -/
theorem sbxS4_compactTest_energy {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    physicalH1FormEnergy ω hd lam (compactTestGraph hd lam f hf hc) =
      -(∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
        ∂physicalReversibleMeasure ω hd lam) := by
  have h := sbxS4_fullForm_compactTest hd hΛ hω lam hf hc
    (compactTestGraph hd lam f hf hc)
  change (∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
    ∂physicalReversibleMeasure ω hd lam) =
    -physicalH1FormEnergy ω hd lam (compactTestGraph hd lam f hf hc) at h
  simpa only [neg_neg] using (congrArg Neg.neg h).symm

/-- The supplied GMP closed form has the correct compact-test physical generator
pairing as its short-time quadratic limit. This is a form limit, not yet a
strong generator derivative or a pointwise transition evolution identity. -/
theorem sbxS4_compactTest_formLimit {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    Tendsto (fun t : ℝ≥0 => semigroupFormDifferenceQuotient ω hd lam
      R.transitionKernel t f) (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (-(∫ x, f x * physicalGenerator (firstCoordinateIndex hd) ω lam f x
        ∂physicalReversibleMeasure ω hd lam))) := by
  let u := compactTestGraph hd lam f hf hc
  obtain ⟨q, hq⟩ := compactTest_mem_physicalH1 hd Λ ω hω lam f hf hc
  have h := R.closedForm_value f q hq u (EventuallyEq.rfl)
  rw [sbxS4_compactTest_energy hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc] at h
  exact h

/-- Bounded Borel generator representatives are time integrable along every
continuous path, including paths visiting the spatial exceptional set. -/
theorem sbxS4_intervalIntegrable_physicalGenerator {d : ℕ} (hd : 2 ≤ d) (i : Fin d)
    {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω) (lam : ℝ)
    {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (γ : Path d) (a b : ℝ) :
    IntervalIntegrable (fun u => physicalGenerator i ω lam f (γ u.toNNReal)) volume a b := by
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd i hΛ hω lam hf hc
  apply intervalIntegrable_iff.mpr
  apply Measure.integrableOn_of_bounded (by simp)
    (((measurable_physicalGenerator i ω lam f).comp
      (γ.continuous.comp continuous_real_toNNReal).measurable).aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun u => by simpa only [Real.norm_eq_abs, Function.comp_apply] using hB (γ u.toNNReal)

/-! The following polarization and contraction argument adapts the private
machinery of `C9GMPStrongCompactGenerator` to the actual Lipschitz coefficients.
The compact-test generator representer is supplied by the preceding form proof. -/

namespace SbxS4Dynkin

open scoped BoundedContinuousFunction

open Set ProbabilityTheory EinsteinFull.Work.W5
open scoped InnerProductSpace Matrix

private theorem sourceDot_comm {d : ℕ} (u v : Vec d) : dot u v = dot v u := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private theorem sourceDot_add_left {d : ℕ} (u v w : Vec d) :
    dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem sourceDot_add_right {d : ℕ} (u v w : Vec d) :
    dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sourceDot_sub_left {d : ℕ} (u v w : Vec d) :
    dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem sourceDot_sub_right {d : ℕ} (u v w : Vec d) :
    dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem sourceDot_matrix_symmetric {d : ℕ} (A : Mat d)
    (hA : A.transpose = A) (u v : Vec d) :
    dot u (A.mulVec v) = dot v (A.mulVec u) := by
  have hu : Matrix.vecMul u A = A.mulVec u := by
    calc
      Matrix.vecMul u A = Matrix.vecMul u A.transpose.transpose := by
        rw [Matrix.transpose_transpose]
      _ = A.transpose.mulVec u := Matrix.vecMul_transpose A.transpose u
      _ = A.mulVec u := by rw [hA]
  calc
    dot u (A.mulVec v) = dotProduct (Matrix.vecMul u A) v := by
      change dotProduct u (A.mulVec v) = _
      exact Matrix.dotProduct_mulVec u A v
    _ = dot (A.mulVec u) v := by
      rw [hu]
      rfl
    _ = dot v (A.mulVec u) := sourceDot_comm _ _

private theorem sourceDot_mulVec_quadratic_polarization {d : ℕ} (A : Mat d)
    (hA : A.transpose = A) (u v : Vec d) :
    dot (u + v) (A.mulVec (u + v)) - dot (u - v) (A.mulVec (u - v)) =
      4 * dot u (A.mulVec v) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, sourceDot_add_left,
    sourceDot_add_right, sourceDot_sub_left, sourceDot_sub_right]
  rw [sourceDot_matrix_symmetric A hA u v]
  ring

private theorem representativeGradient_eq_spaceGradient {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).gradient_memLp.toLp
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient =
      densityWeightedH1SpaceGradient u := by
  have h := congrArg Prod.snd (densityWeightedH1SpaceRepresentative_pair u)
  change _ = _ at h
  exact h

private theorem sourcePhysicalGraph_gradient_add_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gs := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u + v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gs.gradient_memLp.toLp gs.weakGradient =
      gu.gradient_memLp.toLp gu.weakGradient + gv.gradient_memLp.toLp gv.weakGradient := by
    rw [representativeGradient_eq_spaceGradient ρ hρ hρpos (u + v),
      representativeGradient_eq_spaceGradient ρ hρ hρpos u,
      representativeGradient_eq_spaceGradient ρ hρ hρpos v]
    change (E (u + v).1).2 = (E u.1).2 + (E v.1).2
    exact congrArg Prod.snd (E.map_add u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gs.weakGradient =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.weakGradient x + gv.weakGradient x := by
    filter_upwards [hae, Lp.coeFn_add
      (gu.gradient_memLp.toLp gu.weakGradient)
      (gv.gradient_memLp.toLp gv.weakGradient), gs.gradient_memLp.coeFn_toLp,
      gu.gradient_memLp.coeFn_toLp, gv.gradient_memLp.coeFn_toLp] with x heq hadd hs hu hv
    calc
      gs.weakGradient x = (gs.gradient_memLp.toLp gs.weakGradient) x := hs.symm
      _ = ((gu.gradient_memLp.toLp gu.weakGradient) +
        (gv.gradient_memLp.toLp gv.weakGradient)) x := heq
      _ = (gu.gradient_memLp.toLp gu.weakGradient) x +
        (gv.gradient_memLp.toLp gv.weakGradient) x := hadd
      _ = gu.weakGradient x + gv.weakGradient x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).weakGradient =ᵐ[
        densityWeightedMeasure σ] gs.weakGradient := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.weakGradient x + gv.weakGradient x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_gradient_sub_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gd := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u - v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gd.gradient_memLp.toLp gd.weakGradient =
      gu.gradient_memLp.toLp gu.weakGradient - gv.gradient_memLp.toLp gv.weakGradient := by
    rw [representativeGradient_eq_spaceGradient ρ hρ hρpos (u - v),
      representativeGradient_eq_spaceGradient ρ hρ hρpos u,
      representativeGradient_eq_spaceGradient ρ hρ hρpos v]
    change (E (u - v).1).2 = (E u.1).2 - (E v.1).2
    exact congrArg Prod.snd (E.map_sub u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gd.weakGradient =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.weakGradient x - gv.weakGradient x := by
    filter_upwards [hae, Lp.coeFn_sub
      (gu.gradient_memLp.toLp gu.weakGradient)
      (gv.gradient_memLp.toLp gv.weakGradient), gd.gradient_memLp.coeFn_toLp,
      gu.gradient_memLp.coeFn_toLp, gv.gradient_memLp.coeFn_toLp] with x heq hsub hd hu hv
    calc
      gd.weakGradient x = (gd.gradient_memLp.toLp gd.weakGradient) x := hd.symm
      _ = ((gu.gradient_memLp.toLp gu.weakGradient) -
        (gv.gradient_memLp.toLp gv.weakGradient)) x := heq
      _ = (gu.gradient_memLp.toLp gu.weakGradient) x -
        (gv.gradient_memLp.toLp gv.weakGradient) x := hsub
      _ = gu.weakGradient x - gv.weakGradient x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).weakGradient =ᵐ[
        densityWeightedMeasure σ] gd.weakGradient := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.weakGradient x - gv.weakGradient x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem representativeValue_eq_spaceValue {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value_memLp.toLp
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value =
      densityWeightedH1SpaceValue u := by
  have h := congrArg Prod.fst (densityWeightedH1SpaceRepresentative_pair u)
  change _ = _ at h
  exact h

private theorem sourcePhysicalGraph_value_add_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gs := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u + v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gs.value_memLp.toLp gs.value =
      gu.value_memLp.toLp gu.value + gv.value_memLp.toLp gv.value := by
    rw [representativeValue_eq_spaceValue ρ hρ hρpos (u + v),
      representativeValue_eq_spaceValue ρ hρ hρpos u,
      representativeValue_eq_spaceValue ρ hρ hρpos v]
    change (E (u + v).1).1 = (E u.1).1 + (E v.1).1
    exact congrArg Prod.fst (E.map_add u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gs.value =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.value x + gv.value x := by
    filter_upwards [hae, Lp.coeFn_add
      (gu.value_memLp.toLp gu.value) (gv.value_memLp.toLp gv.value),
      gs.value_memLp.coeFn_toLp, gu.value_memLp.coeFn_toLp,
      gv.value_memLp.coeFn_toLp] with x heq hadd hs hu hv
    calc
      gs.value x = (gs.value_memLp.toLp gs.value) x := hs.symm
      _ = ((gu.value_memLp.toLp gu.value) + (gv.value_memLp.toLp gv.value)) x := heq
      _ = (gu.value_memLp.toLp gu.value) x + (gv.value_memLp.toLp gv.value) x := hadd
      _ = gu.value x + gv.value x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
        densityWeightedMeasure σ] gs.value := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.value x + gv.value x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_value_sub_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gd := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u - v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gd.value_memLp.toLp gd.value =
      gu.value_memLp.toLp gu.value - gv.value_memLp.toLp gv.value := by
    rw [representativeValue_eq_spaceValue ρ hρ hρpos (u - v),
      representativeValue_eq_spaceValue ρ hρ hρpos u,
      representativeValue_eq_spaceValue ρ hρ hρpos v]
    change (E (u - v).1).1 = (E u.1).1 - (E v.1).1
    exact congrArg Prod.fst (E.map_sub u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gd.value =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.value x - gv.value x := by
    filter_upwards [hae, Lp.coeFn_sub
      (gu.value_memLp.toLp gu.value) (gv.value_memLp.toLp gv.value),
      gd.value_memLp.coeFn_toLp, gu.value_memLp.coeFn_toLp,
      gv.value_memLp.coeFn_toLp] with x heq hsub hd hu hv
    calc
      gd.value x = (gd.value_memLp.toLp gd.value) x := hd.symm
      _ = ((gu.value_memLp.toLp gu.value) - (gv.value_memLp.toLp gv.value)) x := heq
      _ = (gu.value_memLp.toLp gu.value) x - (gv.value_memLp.toLp gv.value) x := hsub
      _ = gu.value x - gv.value x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
        densityWeightedMeasure σ] gd.value := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.value x - gv.value x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_quotientValue_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hω : IsRegular L ω)
    (z : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm z) =ᵐ[
      densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      (sourcePhysicalGraph (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) z).value := by
  let ρ := sourceReducedDensity hd lam
  let E := densityWeightedH1GraphEquiv ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
  let q := E.symm z
  let g := densityWeightedH1SpaceRepresentative ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z
  have hEq : E q = z := E.apply_symm_apply z
  have hp := physicalH1Representative_pair_eq_quotient_pair
    hd lam q
  have hLp : g.value_memLp.toLp g.value = densityWeightedH1Value ρ q := by
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value_memLp.toLp
        (densityWeightedH1SpaceRepresentative ρ
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value =
      densityWeightedH1Value ρ q
    rw [← hEq]
    exact congrArg Prod.fst hp
  have hAE : densityWeightedH1Value ρ q =ᵐ[densityWeightedMeasure ρ] g.value := by
    filter_upwards [Lp.ext_iff.mp hLp.symm, g.value_memLp.coeFn_toLp] with x heq hg
    exact heq.trans hg
  have hMeasure : densityWeightedMeasure (sourcePhysicalDensity ω hd lam) ≤
      ENNReal.ofReal (Real.exp (2 * L)) • densityWeightedMeasure ρ :=
    sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  change densityWeightedH1Value ρ q =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
    (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value at hσ
  change densityWeightedH1Value (sourceReducedDensity hd lam)
      ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm z) =ᵐ[
      densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
    (sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) z).value
  exact hσ

/-- The physical Dirichlet form on two arbitrary full force-weighted H¹ elements is the
real polarization of its diagonal values. -/
private theorem sourcePhysicalDirichletForm_polarization {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v =
      (1 / 4 : ℝ) * (
        sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 (u + v) (u + v) -
        sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 (u - v) (u - v)) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  let gu := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  let gv := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v
  let gp := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)
  let gm := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)
  have hpoint : weightedFormIntegrand ω.1 gp gp - weightedFormIntegrand ω.1 gm gm =ᵐ[
      densityWeightedMeasure σ] fun x => 4 * weightedFormIntegrand ω.1 gu gv x := by
    filter_upwards [sourcePhysicalGraph_gradient_add_ae ρ hρ hρpos σ K hMeasure u v,
      sourcePhysicalGraph_gradient_sub_ae ρ hρ hρpos σ K hMeasure u v] with x hp hm
    change gp.weakGradient x = gu.weakGradient x + gv.weakGradient x at hp
    change gm.weakGradient x = gu.weakGradient x - gv.weakGradient x at hm
    change (1 / 2 : ℝ) * dot (WithLp.ofLp (gp.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gp.weakGradient x))) -
      (1 / 2 : ℝ) * dot (WithLp.ofLp (gm.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gm.weakGradient x))) =
      4 * ((1 / 2 : ℝ) * dot (WithLp.ofLp (gu.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gv.weakGradient x))))
    have hsym := hω.1 x |>.1
    rw [hp, hm, WithLp.ofLp_add, WithLp.ofLp_sub]
    have hquad := sourceDot_mulVec_quadratic_polarization (ω.1 x) hsym
      (WithLp.ofLp (gu.weakGradient x)) (WithLp.ofLp (gv.weakGradient x))
    linear_combination (1 / 2 : ℝ) * hquad
  have hiU := physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω gp gp
  have hiV := physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω gm gm
  have hInt := integral_congr_ae hpoint
  have hPolar :
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v * 4 =
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (u + v) (u + v) -
          sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (u - v) (u - v) := by
    change (∫ x, weightedFormIntegrand ω.1 gu gv x ∂densityWeightedMeasure σ) * 4 =
      (∫ x, weightedFormIntegrand ω.1 gp gp x ∂densityWeightedMeasure σ) -
        ∫ x, weightedFormIntegrand ω.1 gm gm x ∂densityWeightedMeasure σ
    calc
      _ = 4 * ∫ x, weightedFormIntegrand ω.1 gu gv x ∂densityWeightedMeasure σ := by ring
      _ = ∫ x, (4 * weightedFormIntegrand ω.1 gu gv x) ∂densityWeightedMeasure σ :=
        (integral_const_mul 4 _).symm
      _ = ∫ x, (weightedFormIntegrand ω.1 gp gp - weightedFormIntegrand ω.1 gm gm) x
          ∂densityWeightedMeasure σ := hInt.symm
      _ = _ := integral_sub hiU hiV
  nlinarith [hPolar]

/-- The mixed physical form is the polarization of the canonical full-H¹ energy on the
quotient representatives of `u + v` and `u - v`. -/
private theorem sourcePhysicalDirichletForm_eq_physicalH1FormEnergy_polarization {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v =
      (1 / 4 : ℝ) * (
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (u + v)) -
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (u - v))) := by
  rw [sourcePhysicalDirichletForm_polarization ω hd lam L hL hω u v,
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (u + v),
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (u - v)]

/-- The quotient H¹ value of `u + v` is represented by the sum of the corresponding actual
physical L² values. -/
private theorem sourcePhysicalGraph_quotientValue_add_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u + v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      fun x =>
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x +
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hq := sourcePhysicalGraph_quotientValue_ae ω hd lam L hω (u + v)
  have hsum := sourcePhysicalGraph_value_add_ae ρ hρ hρpos σ K hMeasure u v
  change densityWeightedH1Value ρ
      ((densityWeightedH1GraphEquiv ρ hρ hρpos).symm (u + v)) =ᵐ[
        densityWeightedMeasure σ]
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value at hq
  change (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
    densityWeightedMeasure σ] _ at hsum
  exact hq.trans hsum

/-- The quotient H¹ value of `u - v` is represented by the difference of the corresponding
actual physical L² values. -/
private theorem sourcePhysicalGraph_quotientValue_sub_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u - v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      fun x =>
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x -
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hq := sourcePhysicalGraph_quotientValue_ae ω hd lam L hω (u - v)
  have hsub := sourcePhysicalGraph_value_sub_ae ρ hρ hρpos σ K hMeasure u v
  change densityWeightedH1Value ρ
      ((densityWeightedH1GraphEquiv ρ hρ hρpos).symm (u - v)) =ᵐ[
        densityWeightedMeasure σ]
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value at hq
  change (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
    densityWeightedMeasure σ] _ at hsub
  exact hq.trans hsub

/-- The two actual physical L² test functions induced by a pair of full force-weighted H¹
elements. -/
private def physicalH1PolarizationValuePair {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (Vec d → ℝ) × (Vec d → ℝ) :=
  let gu := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  let gv := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
  (fun x => gu.value x + gv.value x, fun x => gu.value x - gv.value x)

/-- The polarization of the closed-form difference quotient on the two actual physical L²
representatives carried by the full weighted H¹ graph. -/
private def physicalSemigroupFormPolarizationDifferenceQuotient {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (K : ℝ≥0 → Kernel (Vec d) (Vec d))
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (t : ℝ≥0) : ℝ :=
  let F := physicalH1PolarizationValuePair hd lam u v
  (1 / 4 : ℝ) * (
    External.GantertSection7Support.semigroupFormDifferenceQuotient ω hd lam K t
      F.1 -
    External.GantertSection7Support.semigroupFormDifferenceQuotient ω hd lam K t
      F.2)

private theorem givenRealization_semigroupForm_tendsto_closedForm {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (f : Vec d → ℝ)
    (q : DensityWeightedH1 (External.GantertSection7Support.physicalForceWeight hd lam))
    (hq : densityWeightedH1Value (External.GantertSection7Support.physicalForceWeight hd lam) q =ᵐ[
      External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f)
    (g : WeightedSobolevGraph (External.GantertSection7Support.physicalForceMeasure hd lam))
    (hg : g.value =ᵐ[
      External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam g)) :=
  R.closedForm_value f q hq g hg

private theorem physicalH1Polarization_closedFormInputs {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u + v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).1 ∧
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
          densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).1) ∧
    (densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u - v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).2 ∧
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
          densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).2) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * Λ₀)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam Λ₀ hω
  have hqplus := sourcePhysicalGraph_quotientValue_add_ae ω hd lam Λ₀ hω u v
  have hqminus := sourcePhysicalGraph_quotientValue_sub_ae ω hd lam Λ₀ hω u v
  have hgplus : (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).1 := by
    have hsum := sourcePhysicalGraph_value_add_ae ρ hρ hρpos σ K hMeasure u v
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).1
    exact hsum
  have hgminus : (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).2 := by
    have hsub := sourcePhysicalGraph_value_sub_ae ρ hρ hρpos σ K hMeasure u v
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).2
    exact hsub
  exact ⟨⟨hqplus, hgplus⟩, ⟨hqminus, hgminus⟩⟩

private theorem givenRealization_semigroupForm_tendsto_add {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t (physicalH1PolarizationValuePair hd lam u v).1)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  let q := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) |>.symm (u + v)
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)
  have hinput := physicalH1Polarization_closedFormInputs hd ω hω lam u v
  exact givenRealization_semigroupForm_tendsto_closedForm
    hd hΛ₀ ω hω lam hlam hlam_le_one R F.1 q hinput.1.1 g hinput.1.2

private theorem givenRealization_semigroupForm_tendsto_sub {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t (physicalH1PolarizationValuePair hd lam u v).2)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  let q := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) |>.symm (u - v)
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)
  have hinput := physicalH1Polarization_closedFormInputs hd ω hω lam u v
  exact givenRealization_semigroupForm_tendsto_closedForm
    hd hΛ₀ ω hω lam hlam hlam_le_one R F.2 q hinput.2.1 g hinput.2.2

private theorem givenRealization_physicalSemigroupFormPolarization_tendsto_energy {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 ((1 / 4 : ℝ) * (
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)) -
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v))))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  have hplus := givenRealization_semigroupForm_tendsto_add
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  have hminus := givenRealization_semigroupForm_tendsto_sub
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  have hscaled := (hplus.sub hminus).const_mul (1 / 4 : ℝ)
  have hfun :
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t) =
      (fun t : ℝ≥0 => (1 / 4 : ℝ) * (
        External.GantertSection7Support.semigroupFormDifferenceQuotient
          ω hd lam R.transitionKernel t F.1 -
        External.GantertSection7Support.semigroupFormDifferenceQuotient
          ω hd lam R.transitionKernel t F.2)) := by
    funext t
    rfl
  rw [hfun]
  exact hscaled

/-- The closed-form difference quotient polarized on two arbitrary elements of the full
force-weighted H¹ graph converges to the mixed physical Dirichlet form. -/
private theorem givenRealization_physicalSemigroupFormPolarization_tendsto {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ₀))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ₀ hω) ω.1 u v)) := by
  have hpolar := givenRealization_physicalSemigroupFormPolarization_tendsto_energy
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  rw [sourcePhysicalDirichletForm_eq_physicalH1FormEnergy_polarization
    ω hd lam Λ₀ hΛ₀ hω u v]
  exact hpolar


private theorem formQuotient_congr {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) {f g : Vec d → ℝ}
    (hfg : f =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f =
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t g := by
  let : ProbabilityTheory.IsMarkovKernel (R.transitionKernel t) :=
    R.transitionKernel_isMarkovKernel t
  have hk := WeightedKernelL2.kernelIntegral_ae_congr
    (R.transitionKernel_invariant hd hΛ t) hfg
  unfold semigroupFormDifferenceQuotient
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg, hk] with x hx hy
  change (f x - WeightedKernelL2.kernelIntegral (R.transitionKernel t) f x) * f x = _
  rw [hx, hy]
  rfl

private theorem actual_mixed_quotient_limit {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
    let V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v
    Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) V)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u v)) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * Λ)
  let hρ := continuousSourceReducedDensity hd lam
  let hpos := positiveSourceReducedDensity hd lam
  let hm := sourcePhysicalMeasure_le_reduced ω hd lam Λ hω
  let gu := sourcePhysicalGraph ρ hρ hpos σ K hm u
  let gv := sourcePhysicalGraph ρ hρ hpos σ K hm v
  let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue ρ hρ hpos σ K hm u
  let V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue ρ hρ hpos σ K hm v
  have hU : (U : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] gu.value :=
    gu.value_memLp.coeFn_toLp
  have hV : (V : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] gv.value :=
    gv.value_memLp.coeFn_toLp
  have hplus : (physicalH1PolarizationValuePair hd lam u v).1 =ᵐ[
      physicalReversibleMeasure ω hd lam] (U + V : Lp ℝ 2 _) := by
    filter_upwards [hU, hV, Lp.coeFn_add U V] with x hu hv ha
    change gu.value x + gv.value x = _
    rw [ha]
    change _ = U x + V x
    rw [hu, hv]
  have hminus : (physicalH1PolarizationValuePair hd lam u v).2 =ᵐ[
      physicalReversibleMeasure ω hd lam] (U - V : Lp ℝ 2 _) := by
    filter_upwards [hU, hV, Lp.coeFn_sub U V] with x hu hv ha
    change gu.value x - gv.value x = _
    rw [ha]
    change _ = U x - V x
    rw [hu, hv]
  have hlim := givenRealization_physicalSemigroupFormPolarization_tendsto
    hd hΛ ω hω lam h0 h1 R u v
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro t
  change physicalSemigroupFormPolarizationDifferenceQuotient
    ω hd lam R.transitionKernel u v t = (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) V
  unfold physicalSemigroupFormPolarizationDifferenceQuotient
  dsimp only
  rw [formQuotient_congr hd hΛ R t hplus,
    formQuotient_congr hd hΛ R t hminus,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
  have hadd : R.kernelL2Action hd hΛ t (U + V) =
      R.kernelL2Action hd hΛ t U + R.kernelL2Action hd hΛ t V := by
    have h := R.kernelL2Action_sub hd hΛ t (U + V) V
    rw [add_sub_cancel_right] at h
    exact eq_add_of_sub_eq h.symm
  rw [hadd, R.kernelL2Action_sub hd hΛ t]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
  have hcross : inner ℝ (R.kernelL2Action hd hΛ t V) U =
      inner ℝ (R.kernelL2Action hd hΛ t U) V := by
    rw [← kernelL2Action_symmetric hd hΛ R t V U, real_inner_comm]
  rw [real_inner_comm V U, hcross]
  ring

private theorem compact_mixed_quotient_limit {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
    Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) f0)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (-inner ℝ (sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u)
        (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc))) := by
  let v := compactTestDomain hd lam f hf hc
  have hv : sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v = f0 := by
    apply Lp.ext
    exact ((sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v).value_memLp.coeFn_toLp.trans
        (compactTestDomain_value hd Λ ω hω lam f hf hc)).trans hrep.symm
  have hlim := actual_mixed_quotient_limit hd hΛ R u v
  rw [hv] at hlim
  rw [sbxS4_compactTest_fullDomain_generatorInner hd Λ ω hω lam (lt_of_lt_of_le zero_lt_one hΛ) u f hf hc] at hlim
  exact hlim

private theorem compact_action_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Tendsto (fun t : ℝ≥0 => R.kernelL2Action hd hΛ t f0)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 f0) := by
  let fm : MemLp f 2 (physicalReversibleMeasure ω hd lam) := (memLp_congr_ae hrep).mp (Lp.memLp f0)
  obtain ⟨q, hq⟩ := compactTest_mem_physicalH1 hd Λ ω hω lam f hf hc
  have hlim := R.kernelL2Action_tendsto_fullPhysicalH1 hd hΛ ω hω lam h0 h1
    f fm q hq (compactTestGraph hd lam f hf hc) (EventuallyEq.rfl)
  have he : fm.toLp f = f0 := by
    apply Lp.ext
    exact fm.coeFn_toLp.trans hrep.symm
  rw [he] at hlim
  exact hlim

/- Local finite-on-compacts helper from PhysicalH1DensitySupport; the latter
module has an unrelated integration-by-parts API failure under Lean 4.35. -/
private theorem finiteOnCompacts_of_locallyFinite {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {m : Measure X} [IsLocallyFiniteMeasure m] :
    IsFiniteMeasureOnCompacts m := by
  refine ⟨?_⟩
  intro K hK
  let U : K → Set X := fun x => Classical.choose (m.exists_isOpen_measure_lt_top x.1)
  have hU : ∀ x : K, (x : X) ∈ U x ∧ IsOpen (U x) ∧ m (U x) < ∞ := by
    intro x
    exact Classical.choose_spec (m.exists_isOpen_measure_lt_top x.1)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun x => (hU x).2.1) hcover
  calc
    m K ≤ m (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, m (U x) := measure_biUnion_finset_le t U
    _ < ∞ := ENNReal.sum_lt_top.mpr (fun x hx => (hU x).2.2)

private def actualActionCLM {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  LinearMap.mkContinuous
    { toFun := R.kernelL2Action hd hΛ t
      map_add' := fun f g => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_add_left,
          inner_add_left, ← kernelL2Action_symmetric hd hΛ R,
          ← kernelL2Action_symmetric hd hΛ R]
      map_smul' := fun c f => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_smul_left,
          inner_smul_left, ← kernelL2Action_symmetric hd hΛ R]
        simp }
    1 (fun f => by
      change ‖R.kernelL2Action hd hΛ t f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact R.kernelL2Action_norm_le hd hΛ t f)

private theorem actualAction_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    actualActionCLM hd hΛ R 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let : IsMarkovKernel (R.transitionKernel 0) := R.transitionKernel_isMarkovKernel 0
  have hk := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ 0) f
  change R.kernelL2Action hd hΛ 0 f =ᵐ[_] _ at hk
  filter_upwards [hk] with x hx
  change R.kernelL2Action hd hΛ 0 f x = f x
  rw [hx]
  simp only [WeightedKernelL2.kernelIntegral, R.transitionKernel_zero,
    Kernel.id_apply, integral_dirac]

private theorem actual_action_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun t : ℝ≥0 => R.kernelL2Action hd hΛ t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) := by
    change IsLocallyFiniteMeasure (densityWeightedMeasure (sourcePhysicalDensity ω hd lam))
    exact densityWeightedMeasure_locallyFinite _ (continuousSourcePhysicalDensity ω hd lam)
  let : IsFiniteMeasureOnCompacts (physicalReversibleMeasure ω hd lam) :=
    finiteOnCompacts_of_locallyFinite
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense : Dense {z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      ∃ g : Vec d → ℝ, (z : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g ∧
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  obtain ⟨U, ⟨g, hUg, hgc, hgd⟩, hu⟩ := hdense.exists_dist_lt f (by positivity : 0 < ε / 3)
  have hu' : dist U f < ε / 3 := by rwa [dist_comm] at hu
  obtain ⟨δ, hδ, ht⟩ := (Metric.tendsto_nhdsWithin_nhds.mp
    (compact_action_tendsto_zero hd hΛ R g hgd hgc U hUg)) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  have hclose : dist (R.kernelL2Action hd hΛ t U) U < ε / 3 := ht ht0 htδ
  have hcontract : dist (R.kernelL2Action hd hΛ t f)
      (R.kernelL2Action hd hΛ t U) ≤ dist f U := by
    rw [dist_eq_norm, dist_eq_norm, ← R.kernelL2Action_sub hd hΛ t f U]
    exact R.kernelL2Action_norm_le hd hΛ t (f - U)
  have htriangle := dist_triangle4 (R.kernelL2Action hd hΛ t f)
    (R.kernelL2Action hd hΛ t U) U f
  rw [dist_comm f U] at hcontract
  linarith

private theorem contractiveSemigroup_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖)
    (hPc : ∀ f, Tendsto (fun t => P t f) (𝓝[>] (0 : ℝ≥0)) (𝓝 f))
    (f : E) : Continuous (fun t => P t f) := by
  have hc0 : Tendsto (fun t => P t f) (𝓝 (0 : ℝ≥0)) (𝓝 f) := by
    have hs : Tendsto (fun t => P t f) (𝓝[{0}] (0 : ℝ≥0)) (𝓝 f) := by
      simpa only [hP0, ContinuousLinearMap.id_apply] using
        (continuousWithinAt_singleton (f := fun t => P t f) (x := 0)).tendsto
    have h := (hPc f).sup hs
    have he : Ici (0 : ℝ≥0) = univ := Set.eq_univ_of_forall (fun t => t.property)
    simpa only [nhdsGT_sup_nhdsWithin_singleton, he, nhdsWithin_univ] using h
  apply continuous_iff_continuousAt.mpr
  intro t
  have hleft : Tendsto (fun s : ℝ≥0 => ‖P (s - t) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => s - t) from
          continuous_id.sub continuous_const).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  have hright : Tendsto (fun s : ℝ≥0 => ‖P (t - s) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => t - s) from
          continuous_const.sub continuous_id).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun s => dist_nonneg) _ (by simpa using hleft.add hright)
  intro s
  rcases le_total t s with h | h
  · have he : P s f - P t f = P t (P (s - t) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_eq_norm, he]
    exact (hPn t _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · have he : P t f - P s f = P s (P (t - s) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_comm, dist_eq_norm, he]
    exact (hPn s _).trans (le_add_of_nonneg_left (norm_nonneg _))

private def C0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem c0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    C0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
  let u : ℝ → E := fun s => P s.toNNReal f
  let F : ℝ → E := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hPc f).comp continuous_real_toNNReal
  have hF (s : ℝ) : HasDerivAt F (u s) s :=
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hd : HasDerivAt (fun s : ℝ => F ((t : ℝ) + s) - F s) (P t f - f) 0 := by
    have h := ((hF ((t : ℝ) + 0)).scomp 0
      ((hasDerivAt_id 0).const_add (t : ℝ))).sub (hF 0)
    simp only [u, add_zero, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply, one_smul] at h
    exact h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have hh := hslope.comp hcoe
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hshift : P h (F (t : ℝ)) = F ((t : ℝ) + h) - F (h : ℝ) := by
    change P h (∫ s in (0 : ℝ)..(t : ℝ), u s) = _
    rw [← (P h).intervalIntegral_comp_comm (hu.intervalIntegrable 0 t)]
    have he : (fun s : ℝ => P h (u s)) =ᶠ[ae (volume.restrict (uIoc (0 : ℝ) t))]
        (fun s : ℝ => u (s + h)) := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs0 : 0 ≤ s := (min_eq_left t.property ▸ hs.1).le
      dsimp only [u]
      rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm]
      have ha : s.toNNReal + h = (s + (h : ℝ)).toNNReal := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left hs0]
        exact (max_eq_left (add_nonneg hs0 h.property)).symm
      rw [ha]
    rw [intervalIntegral.integral_congr_ae_restrict he,
      intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable 0 h) (hu.intervalIntegrable h (t + h)))
  simp only [Function.comp_apply, slope_def_module, sub_zero, add_zero, F, intervalIntegral.integral_same]
  rw [← hshift]

private theorem generator_quotient_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖) {f g : E} (hg : C0Graph P f g) :
    ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → ‖(t : ℝ)⁻¹ • (P t f - f)‖ ≤ C := by
  obtain ⟨δ, hδ, ht⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hg) 1 zero_lt_one
  refine ⟨max (‖g‖ + 1) (δ⁻¹ * (2 * ‖f‖)), fun t ht0 => ?_⟩
  by_cases hsmall : (t : ℝ) < δ
  · have hh := ht ht0 (by
      change |(t : ℝ) - 0| < δ
      simpa only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ t from t.property)] using hsmall)
    have hn := norm_le_norm_add_norm_sub g ((t : ℝ)⁻¹ • (P t f - f))
    rw [norm_sub_rev g] at hn
    rw [dist_eq_norm] at hh
    exact (by linarith : ‖(t : ℝ)⁻¹ • (P t f - f)‖ ≤ ‖g‖ + 1).trans (le_max_left _ _)
  · have htpos : 0 < (t : ℝ) := ht0
    have hinv : (t : ℝ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (le_of_not_gt hsmall)
    have hn : ‖P t f - f‖ ≤ 2 * ‖f‖ := by
      exact (norm_sub_le _ _).trans (by linarith [hPn t f])
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact (mul_le_mul hinv hn (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ))).trans
      (le_max_right _ _)

private theorem generator_compact_pairing {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    {v g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hg : C0Graph (actualActionCLM hd hΛ R) v g)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    inner ℝ g f0 = inner ℝ v (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc) := by
  obtain ⟨C, hC⟩ := generator_quotient_bounded
    (P := actualActionCLM hd hΛ R) (fun t z => R.kernelL2Action_norm_le hd hΛ t z) hg
  have hbound : ∃ B : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t v ≤ B := by
    refine ⟨C * ‖v‖, fun t ht => ?_⟩
    rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
    have he : (1 / (t : ℝ)) * inner ℝ (v - R.kernelL2Action hd hΛ t v) v =
        -inner ℝ ((t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t v - v)) v := by
      rw [real_inner_smul_left, inner_sub_left, inner_sub_left]
      ring
    rw [he]
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg v)))
  obtain ⟨q, hq⟩ := (R.closedForm_domain v (Lp.memLp v)).mp hbound
  let u := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q
  let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
  have hU : U = v := by
    apply Lp.ext
    have hu := fullDomain_quotient_value_ae hd Λ ω hω lam u
    have hqu : (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm u = q :=
      Equiv.symm_apply_apply _ q
    rw [hqu] at hu
    exact ((sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u).value_memLp.coeFn_toLp).trans
      (hu.symm.trans hq)
  have hm := compact_mixed_quotient_limit hd hΛ R u f hf hc f0 hrep
  change Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) *
    inner ℝ (U - R.kernelL2Action hd hΛ t U) f0) _
    (𝓝 (-inner ℝ U (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc))) at hm
  rw [hU] at hm
  have hs : Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) *
      inner ℝ (v - R.kernelL2Action hd hΛ t v) f0)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (-inner ℝ g f0)) := by
    have h : Tendsto (fun t : ℝ≥0 =>
        -inner ℝ ((t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t v - v)) f0)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (-inner ℝ g f0)) :=
      (hg.inner (tendsto_const_nhds (x := f0))).neg
    apply h.congr'
    exact Eventually.of_forall (fun t => by
      simp only [real_inner_smul_left, inner_sub_left, one_div]
      ring)
  have he := tendsto_nhds_unique hs hm
  exact neg_injective he

/-- Strong continuity of the supplied GMP action on its full physical L2 space. -/
theorem kernelL2Action_continuous {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Continuous (fun t : ℝ≥0 => R.kernelL2Action hd hΛ t f) := by
  let P := actualActionCLM hd hΛ R
  have hP0 : P 0 = ContinuousLinearMap.id ℝ _ := actualAction_zero hd hΛ R
  have hPm : ∀ s t, P (s + t) = (P s).comp (P t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro u
    exact kernelL2Action_add hd hΛ R s t u
  exact contractiveSemigroup_continuous hP0 hPm
    (fun t u => R.kernelL2Action_norm_le hd hΛ t u)
    (actual_action_tendsto_zero hd hΛ R) f

/-- The actual GMP action satisfies the integrated generator identity for compact tests
under the regular Lipschitz coefficient hypotheses. -/
theorem compact_test_integrated_evolution :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1)
  (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
  (f0 : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam)),
  (f0 : Vec d → ℝ) =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f →
  ∀ T : ℝ≥0, R.kernelL2Action hd hΛ T f0 - f0 =
    ∫ s in (0 : ℝ)..(T : ℝ), R.kernelL2Action hd hΛ s.toNNReal
      (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc) := by
  intro d hd Λ hΛ ω hω lam h0 h1 R f hf hc f0 hrep T
  let P := actualActionCLM hd hΛ R
  let L := sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc
  have hP0 : P 0 = ContinuousLinearMap.id ℝ _ := actualAction_zero hd hΛ R
  have hPm : ∀ s t, P (s + t) = (P s).comp (P t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro u
    exact kernelL2Action_add hd hΛ R s t u
  have hPn : ∀ t u, ‖P t u‖ ≤ ‖u‖ := fun t u => R.kernelL2Action_norm_le hd hΛ t u
  have hPc : ∀ u, Continuous (fun t => P t u) :=
    contractiveSemigroup_continuous hP0 hPm hPn (actual_action_tendsto_zero hd hΛ R)
  have hidentity (t : ℝ≥0) : P t f0 - f0 = ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L := by
    apply ext_inner_right ℝ
    intro u
    have hpair := generator_compact_pairing hd hΛ R
      (c0Graph_integral hP0 hPm hPc u t) f hf hc f0 hrep
    have hu := ((hPc u).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    have hL := ((hPc L).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    calc
      inner ℝ (P t f0 - f0) u = inner ℝ (P t u - u) f0 := by
        change inner ℝ (R.kernelL2Action hd hΛ t f0 - f0) u =
          inner ℝ (R.kernelL2Action hd hΛ t u - u) f0
        rw [inner_sub_left, inner_sub_left,
          ← kernelL2Action_symmetric hd hΛ R t f0 u,
          real_inner_comm f0 (R.kernelL2Action hd hΛ t u), real_inner_comm f0 u]
      _ = inner ℝ (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) L := hpair
      _ = inner ℝ L (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) := real_inner_comm _ _
      _ = ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ L (P s.toNNReal u) :=
        ((innerSL ℝ L).intervalIntegral_comp_comm hu).symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ u (P s.toNNReal L) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change inner ℝ L (R.kernelL2Action hd hΛ s.toNNReal u) =
          inner ℝ u (R.kernelL2Action hd hΛ s.toNNReal L)
        rw [kernelL2Action_symmetric hd hΛ R, real_inner_comm]
      _ = inner ℝ u (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L) :=
        (innerSL ℝ u).intervalIntegral_comp_comm hL
      _ = inner ℝ (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L) u := real_inner_comm _ _
  exact hidentity T

theorem compact_test_strong_generator :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1)
  (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
  (f0 : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam)),
  (f0 : Vec d → ℝ) =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f →
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t f0 - f0))
    (𝓝[Set.Ioi 0] (0 : ℝ≥0))
    (𝓝 (sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc)) := by
  intro d hd Λ hΛ ω hω lam h0 h1 R f hf hc f0 hrep
  let P := actualActionCLM hd hΛ R
  let L := sbxS4CompactTestGeneratorL2 hd (lt_of_lt_of_le zero_lt_one hΛ) hω lam f hf hc
  have hP0 : P 0 = ContinuousLinearMap.id ℝ _ := actualAction_zero hd hΛ R
  have hPc : ∀ u, Continuous (fun t => P t u) := kernelL2Action_continuous hd hΛ R
  have hidentity (t : ℝ≥0) : P t f0 - f0 = ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L :=
    compact_test_integrated_evolution hd hΛ R f hf hc f0 hrep t
  let F : ℝ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    fun s => ∫ r in (0 : ℝ)..s, P r.toNNReal L
  have hu : Continuous (fun r : ℝ => P r.toNNReal L) :=
    (hPc L).comp continuous_real_toNNReal
  have hdF : HasDerivAt F L 0 := by
    have h := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt
    simpa only [Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hdF.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have havg := hslope.comp hcoe
  change Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f0 - f0)) _ (𝓝 L)
  convert havg using 1
  funext t
  simp only [Function.comp_apply, slope_def_module, sub_zero, F,
    intervalIntegral.integral_same, sub_zero]
  rw [hidentity]


private theorem dynkin_integrable_bounded {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] {f : α → ℝ} (hf : Measurable f)
    (B : ℝ) (hB : ∀ x, ‖f x‖ ≤ B) : Integrable f μ :=
  ⟨hf.aestronglyMeasurable, HasFiniteIntegral.of_bounded (Eventually.of_forall hB)⟩

/-- Identify a time integral in L² by testing against finite-measure indicators.
The joint representative is measurable and bounded, so scalar Fubini applies locally. -/
private theorem dynkin_integral_representative
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ]
    (u : ℝ → Lp ℝ 2 μ) (hu : Continuous u)
    (U : ℝ → α → ℝ) (hU : Measurable (Function.uncurry U))
    (B : ℝ) (hB : ∀ t x, ‖U t x‖ ≤ B)
    (hrep : ∀ t, (u t : α → ℝ) =ᵐ[μ] U t) (T : ℝ≥0) :
    ((∫ t in (0 : ℝ)..(T : ℝ), u t : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      fun x => ∫ t in (0 : ℝ)..(T : ℝ), U t x := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have hprod (s : Set α) (hs : μ s < ∞) :
      Integrable (fun p : α × ℝ => U p.2 p.1) ((μ.restrict s).prod ν) := by
    let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa only [Measure.restrict_apply_univ] using hs⟩
    exact dynkin_integrable_bounded _ (hU.comp measurable_swap) B (fun p => hB _ _)
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · intro s hs hμs
    change Integrable (fun x => ∫ t in (0 : ℝ)..(T : ℝ), U t x) (μ.restrict s)
    simpa only [intervalIntegral.integral_of_le T.coe_nonneg, ν] using
      (hprod s hμs).integral_prod_left
  · intro s hs hμs
    let v : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs.ne (1 : ℝ)
    calc
      _ = inner ℝ v (∫ t in (0 : ℝ)..(T : ℝ), u t) :=
        (L2.inner_indicatorConstLp_one hs hμs.ne _).symm
      _ = ∫ t in (0 : ℝ)..(T : ℝ), inner ℝ v (u t) :=
        ((innerSL ℝ v).intervalIntegral_comp_comm (hu.intervalIntegrable 0 T)).symm
      _ = ∫ t in (0 : ℝ)..(T : ℝ), ∫ x in s, U t x ∂μ := by
        apply intervalIntegral.integral_congr
        intro t ht
        change inner ℝ (indicatorConstLp 2 hs hμs.ne (1 : ℝ)) (u t) = ∫ x in s, U t x ∂μ
        rw [L2.inner_indicatorConstLp_one hs hμs.ne]
        exact integral_congr_ae (ae_restrict_of_ae (hrep t))
      _ = _ := by
        simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
        exact (integral_integral_swap (hprod s hμs)).symm

section Actual
variable {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
    {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)

/-- Joint time/start measurability follows from continuous path evaluation and the
actual one-time marginals, also for bounded Borel generator representatives. -/
theorem transition_integral_measurable {g : Vec d → ℝ} (hg : Measurable g) :
    Measurable (fun p : ℝ × Vec d => ∫ y, g y ∂R.transitionKernel p.1.toNNReal p.2) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let K : Kernel (ℝ × Vec d) (Path d) := R.pathLaw.comap Prod.snd measurable_snd
  have hm : Measurable (fun p : (ℝ × Vec d) × Path d => g (p.2 p.1.1.toNNReal)) := by
    apply hg.comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0)
      (Y := Vec d)).measurable.comp
        (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst.fst))
  have hi := hm.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
  convert hi.measurable using 1
  funext p
  change (∫ y, g y ∂R.transitionKernel p.1.toNNReal p.2) =
    ∫ γ, g (γ p.1.toNNReal) ∂R.pathLaw p.2
  rw [← R.pathLaw_endpoint p.1.toNNReal p.2]
  exact integral_map (measurable_pathPosition p.1.toNNReal).aemeasurable hg.aestronglyMeasurable

private theorem transition_integral_bound {g : Vec d → ℝ} (B : ℝ)
    (hB : ∀ y, ‖g y‖ ≤ B) (t : ℝ≥0) (x : Vec d) :
    ‖∫ y, g y ∂R.transitionKernel t x‖ ≤ B := by
  let : IsMarkovKernel (R.transitionKernel t) := R.transitionKernel_isMarkovKernel t
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := R.transitionKernel t x)
      (Eventually.of_forall hB))

private theorem dynkin_action_representative (f : Vec d → ℝ)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) (t : ℝ≥0) :
    (R.kernelL2Action hd hΛ t f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ y, f y ∂R.transitionKernel t x := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  let := R.transitionKernel_isMarkovKernel t
  exact (WeightedKernelL2.kernelIntegralL2_coe (R.transitionKernel_invariant hd hΛ t) f0).trans
    (WeightedKernelL2.kernelIntegral_ae_congr (R.transitionKernel_invariant hd hΛ t) hrep)

/-- The actual transition evolution at almost every physical start, without a
smooth-coefficient premise. -/
theorem compact_test_evolution_ae
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (T : ℝ≥0) :
    (fun x => (∫ y, f y ∂R.transitionKernel T x) - f x) =ᵐ[physicalReversibleMeasure ω hd lam]
      fun x => ∫ t in (0 : ℝ)..(T : ℝ),
        ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y
          ∂R.transitionKernel t.toNNReal x := by
  let := gantert_physicalMeasure_locallyFinite hd ω lam
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hfm : MemLp f 2 (physicalReversibleMeasure ω hd lam) :=
    hf.continuous.memLp_of_hasCompactSupport hc
  let f0 := hfm.toLp f
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let g0 := sbxS4CompactTestGeneratorL2 hd hΛ0 hω lam f hf hc
  have hg0 : (g0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g :=
    (sbxS4_memLp_physicalGenerator hd (firstCoordinateIndex hd) hΛ0 hω lam hf hc).coeFn_toLp
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    hΛ0 hω lam hf hc
  have hg : Measurable g := measurable_physicalGenerator _ ω lam f
  have he := compact_test_integrated_evolution hd hΛ R f hf hc f0 hfm.coeFn_toLp T
  have hcont := (kernelL2Action_continuous hd hΛ R g0).comp
    continuous_real_toNNReal
  have hi := dynkin_integral_representative (physicalReversibleMeasure ω hd lam)
    (fun t : ℝ => R.kernelL2Action hd hΛ t.toNNReal g0) hcont
    (fun t x => ∫ y, g y ∂R.transitionKernel t.toNNReal x)
    (transition_integral_measurable hd hΛ R hg) B
    (fun t x => transition_integral_bound hd hΛ R B
      (fun y => by simpa only [Real.norm_eq_abs] using hB y) t.toNNReal x)
    (fun t => dynkin_action_representative hd hΛ R g g0 hg0 t.toNNReal) T
  rw [← he] at hi
  filter_upwards [hi, Lp.coeFn_sub (R.kernelL2Action hd hΛ T f0) f0,
    dynkin_action_representative hd hΛ R f f0 hfm.coeFn_toLp T, hfm.coeFn_toLp]
    with x hix hs hx hf0
  rw [hs, Pi.sub_apply, hx, hf0] at hix
  exact hix

private theorem dynkin_transition_add (f : Vec d → ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀ y, ‖f y‖ ≤ B)
    (s t : ℝ≥0) (x : Vec d) :
    (∫ y, f y ∂R.transitionKernel (s + t) x) =
      ∫ z, (∫ y, f y ∂R.transitionKernel t z) ∂R.transitionKernel s x := by
  let := R.transitionKernel_isMarkovKernel s
  let := R.transitionKernel_isMarkovKernel t
  rw [R.transitionKernel_add s t]
  exact Kernel.integral_comp
    (dynkin_integrable_bounded _ hf B hB)

/-- Smoothing an exceptional set by a positive transition and taking the time-zero
limit upgrades the evolution identity to every start, with only Borel regularity
of the bounded generator. Endpoint continuity of its occupation primitive suffices. -/
private theorem dynkin_evolution_every_start
    (f : Vec d →ᵇ ℝ) (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) (T : ℝ≥0)
    (hae : (fun x => (∫ y, f y ∂R.transitionKernel T x) - f x)
      =ᵐ[physicalReversibleMeasure ω hd lam]
        fun x => ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x)
    (x : Vec d) :
    (∫ y, f y ∂R.transitionKernel T x) - f x =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x := by
  let ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) T)
  have he (ε : ℝ≥0) (hε : 0 < ε) :
      (∫ y, f y ∂R.transitionKernel (ε + T) x) -
        (∫ y, f y ∂R.transitionKernel ε x) =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel (ε + t.toNNReal) x := by
    let := R.transitionKernel_isMarkovKernel ε
    let := R.transitionKernel_isMarkovKernel T
    have hfi : Integrable (fun z => ∫ y, f y ∂R.transitionKernel T z)
        (R.transitionKernel ε x) :=
      dynkin_integrable_bounded _ f.continuous.stronglyMeasurable.integral_kernel.measurable
        ‖f‖ (fun z => transition_integral_bound hd hΛ R ‖f‖ (fun y => f.norm_coe_le_norm y) T z)
    have hf0 : Integrable f (R.transitionKernel ε x) :=
      dynkin_integrable_bounded _ f.continuous.measurable ‖f‖ (fun y => f.norm_coe_le_norm y)
    have h := integral_congr_ae
      ((gantert_transition_absolutelyContinuous hd Λ hΛ ω hω lam h0 h1 R ε hε x).ae_le hae)
    rw [integral_sub hfi hf0, ← dynkin_transition_add hd hΛ R f f.continuous.measurable ‖f‖ (fun y => f.norm_coe_le_norm y) ε T x] at h
    rw [h]
    have hi : Integrable
        (fun p : Vec d × ℝ => ∫ y, g y ∂R.transitionKernel p.2.toNNReal p.1)
        ((R.transitionKernel ε x).prod ν) :=
      dynkin_integrable_bounded _ ((transition_integral_measurable hd hΛ R hg).comp measurable_swap)
        B (fun p => transition_integral_bound hd hΛ R B hB p.2.toNNReal p.1)
    calc
      _ = ∫ t in (0 : ℝ)..(T : ℝ),
          ∫ z, (∫ y, g y ∂R.transitionKernel t.toNNReal z) ∂R.transitionKernel ε x := by
        change (∫ z, (∫ t in (0 : ℝ)..(T : ℝ),
          ∫ y, g y ∂R.transitionKernel t.toNNReal z) ∂R.transitionKernel ε x) = _
        simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
        exact integral_integral_swap hi
      _ = _ := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact (dynkin_transition_add hd hΛ R g hg B hB ε t.toNNReal x).symm
  have hfcont := gantert_continuous_transition_time hd Λ hΛ ω hω lam h0 h1 R f x
  have heps : Tendsto (fun ε : ℝ≥0 => ε) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ≥0)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hfT : Tendsto (fun ε : ℝ≥0 => ∫ y, f y ∂R.transitionKernel (ε + T) x)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (∫ y, f y ∂R.transitionKernel T x)) := by
    simpa only [Function.comp_def, zero_add] using (hfcont.tendsto (0 + T)).comp (heps.add_const T)
  have hfzero : Tendsto (fun ε : ℝ≥0 => ∫ y, f y ∂R.transitionKernel ε x)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (f x)) :=
    (gantert_transition_tendsto_zero hd Λ hΛ ω hω lam h0 h1 R f x).mono_left
      nhdsWithin_le_nhds
  have hint : Tendsto (fun ε : ℝ≥0 =>
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel (ε + t.toNNReal) x)
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel t.toNNReal x)) := by
    let H : ℝ → ℝ := fun t => ∫ y, g y ∂R.transitionKernel t.toNNReal x
    have hHi (a b : ℝ) : IntervalIntegrable H volume a b := by
      apply intervalIntegrable_iff.mpr
      apply Measure.integrableOn_of_bounded (by simp)
        (((transition_integral_measurable hd hΛ R hg).comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      exact Eventually.of_forall fun t => transition_integral_bound hd hΛ R B hB t.toNNReal x
    have hcont : Continuous (fun b : ℝ => ∫ t in (0 : ℝ)..b, H t) :=
      intervalIntegral.continuous_primitive hHi 0
    have hshift (ε : ℝ≥0) :
        (∫ t in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel (ε + t.toNNReal) x) =
          (∫ t in (0 : ℝ)..((T : ℝ) + ε), H t) - ∫ t in (0 : ℝ)..(ε : ℝ), H t := by
      rw [intervalIntegral.integral_interval_sub_left (hHi _ _) (hHi _ _)]
      calc
        _ = ∫ t in (0 : ℝ)..(T : ℝ), H (t + ε) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht0 : 0 ≤ t := (Set.uIcc_of_le T.coe_nonneg ▸ ht).1
          dsimp [H]
          congr 3
          apply NNReal.eq
          simp only [NNReal.coe_add, Real.coe_toNNReal _ ht0,
            Real.coe_toNNReal _ (add_nonneg ht0 ε.coe_nonneg)]
          exact add_comm _ _
        _ = _ := by simpa only [zero_add] using intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (T : ℝ)) H (ε : ℝ)
    simp_rw [hshift]
    have hepsR : Tendsto (fun ε : ℝ≥0 => (ε : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝 (0 : ℝ)) :=
      NNReal.continuous_coe.continuousAt.tendsto.comp heps
    have hsum : Tendsto (fun ε : ℝ≥0 => (T : ℝ) + ε)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (T : ℝ)) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (T : ℝ))).add hepsR
    have htop := (hcont.tendsto (T : ℝ)).comp hsum
    have hbot := (hcont.tendsto 0).comp hepsR
    simpa only [Function.comp_apply, add_zero, intervalIntegral.integral_same, sub_zero, H] using htop.sub hbot
  apply tendsto_nhds_unique (hfT.sub hfzero)
  apply hint.congr'
  filter_upwards [eventually_mem_nhdsWithin] with ε hε
  exact (he ε hε).symm

/-- The literal compact-test transition evolution holds at every specified start. -/
theorem compact_test_evolution_every_start
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (T : ℝ≥0) (x : Vec d) :
    (∫ y, f y ∂R.transitionKernel T x) - f x =
      ∫ t in (0 : ℝ)..(T : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam f y
          ∂R.transitionKernel t.toNNReal x := by
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  exact dynkin_evolution_every_start hd hΛ R (gantertCompactObservable f hf.continuous hc)
    (physicalGenerator (firstCoordinateIndex hd) ω lam f)
    (measurable_physicalGenerator _ ω lam f) B
    (fun y => by simpa only [Real.norm_eq_abs] using hB y) T
    (compact_test_evolution_ae hd hΛ R f hf hc T) x

theorem integral_occupation (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B)
    (x : Vec d) (T : ℝ≥0) :
    (∫ γ, (∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) ∂R.pathLaw x) =
      ∫ u in (0 : ℝ)..(T : ℝ), ∫ y, g y ∂R.transitionKernel u.toNNReal x := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun p => g (p.1 p.2.toNNReal)
  have hH : Measurable H := by
    apply hg.comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hint : Integrable H ((R.pathLaw x).prod ν) :=
    dynkin_integrable_bounded _ hH B (fun p => hB _)
  simp_rw [intervalIntegral.integral_of_le T.coe_nonneg]
  calc
    _ = ∫ u, ∫ γ, H (γ, u) ∂R.pathLaw x ∂ν := integral_integral_swap hint
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun u => by
        change (∫ γ, g (γ u.toNNReal) ∂R.pathLaw x) =
          ∫ y, g y ∂R.transitionKernel u.toNNReal x
        rw [← R.pathLaw_endpoint u.toNNReal x]
        exact (integral_map (measurable_pathPosition u.toNNReal).aemeasurable
          hg.aestronglyMeasurable).symm

/-- Occupation is integrable before any martingale identity is known. -/
theorem integrable_occupation (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B)
    (x : Vec d) (T : ℝ≥0) :
    Integrable (fun γ => ∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) (R.pathLaw x) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun p => g (p.1 p.2.toNNReal)
  have hH : Measurable H := by
    apply hg.comp
    exact (ContinuousEval.continuous_eval (F := Path d) (X := ℝ≥0) (Y := Vec d)).measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hint : Integrable H ((R.pathLaw x).prod ν) :=
    dynkin_integrable_bounded _ hH B (fun p => hB _)
  simpa only [intervalIntegral.integral_of_le T.coe_nonneg] using hint.integral_prod_left

/-- Integrability of the literal compensated test under the supplied law. -/
theorem integrable_compensated_test
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) (T : ℝ≥0) :
    Integrable (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T)
      (R.pathLaw x) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let fB := gantertCompactObservable f hf.continuous hc
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have ha := stronglyAdapted_compensatedTest_of_measurable
    (physicalGenerator (firstCoordinateIndex hd) ω lam) f hf.continuous
    (measurable_physicalGenerator _ ω lam f)
  apply dynkin_integrable_bounded _ ((ha T).mono ((pathFiltration d).le T)).measurable
    (2 * ‖fB‖ + B * T)
  intro γ
  exact abs_compensatedTest_le (L := physicalGenerator (firstCoordinateIndex hd) ω lam)
    (fun y => fB.norm_coe_le_norm y) hB T γ

/-- The actual law has zero compact-test compensated mean at every start. -/
theorem compensated_test_mean_zero
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : Vec d) (T : ℝ≥0) :
    (∫ γ, compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω lam) f T γ
      ∂R.pathLaw x) = 0 := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  let fB := gantertCompactObservable f hf.continuous hc
  let g := physicalGenerator (firstCoordinateIndex hd) ω lam f
  have hg : Measurable g := measurable_physicalGenerator _ ω lam f
  obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have hBn : ∀ y, ‖g y‖ ≤ B := hB
  have hi (t : ℝ≥0) : Integrable (fun γ : Path d => f (γ t)) (R.pathLaw x) :=
    dynkin_integrable_bounded _
      (hf.continuous.comp (continuous_eval_const t)).measurable ‖fB‖
        (fun γ => fB.norm_coe_le_norm (γ t))
  have he (t : ℝ≥0) : (∫ γ, f (γ t) ∂R.pathLaw x) =
      ∫ y, f y ∂R.transitionKernel t x := by
    rw [← R.pathLaw_endpoint t x]
    exact (integral_map (measurable_pathPosition t).aemeasurable
      hf.continuous.aestronglyMeasurable).symm
  change (∫ γ, (f (γ T) - f (γ 0)) -
    (∫ u in (0 : ℝ)..(T : ℝ), g (γ u.toNNReal)) ∂R.pathLaw x) = _
  have hisub : Integrable (fun γ : Path d => f (γ T) - f (γ 0)) (R.pathLaw x) :=
    (hi T).sub (hi 0)
  rw [integral_sub hisub
    (integrable_occupation hd hΛ R g hg B hBn x T),
    integral_sub (hi T) (hi 0), he T, he 0,
    integral_occupation hd hΛ R g hg B hBn x T,
    R.transitionKernel_zero, ProbabilityTheory.Kernel.id_apply, integral_dirac]
  exact sub_eq_zero.mpr (compact_test_evolution_every_start hd hΛ R f hf hc T x)

end Actual

private theorem pastSigma_eq_pathFiltration {d : ℕ} (s : ℝ≥0) :
    gmpPastSigma (d := d) s = pathFiltration d s := by
  change (⨆ t : Set.Iic s, MeasurableSpace.comap (pathPosition t.val) inferInstance) =
    ⨆ t ≤ s, MeasurableSpace.comap (pathPosition t) inferInstance
  exact iSup_subtype

/-- Compensated-test increments are literal future compensated tests. -/
private theorem compensatedTest_shift {d : ℕ}
    (L : (Vec d → ℝ) → Vec d → ℝ) (f : Vec d → ℝ)
    (hL : ∀ γ : Path d, ∀ a b : ℝ,
      IntervalIntegrable (fun u => L f (γ u.toNNReal)) volume a b) (s t : ℝ≥0) (γ : Path d) :
    compensatedTest L f t (gmpShiftPath s γ) =
      compensatedTest L f (s + t) γ - compensatedTest L f s γ := by
  let g : ℝ → ℝ := fun u => L f (γ u.toNNReal)
  have hg (a b : ℝ) : IntervalIntegrable g volume a b := hL γ a b
  have hshift : (∫ u in (0 : ℝ)..(t : ℝ), L f (gmpShiftPath s γ u.toNNReal)) =
      ∫ u in (s : ℝ)..((s : ℝ) + t), g u := by
    calc
      _ = ∫ u in (0 : ℝ)..(t : ℝ), g (u + s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu0 : 0 ≤ u := (Set.uIcc_of_le t.coe_nonneg ▸ hu).1
        change L f (γ (s + u.toNNReal)) = L f (γ (u + s).toNNReal)
        congr 2
        apply NNReal.eq
        simp only [NNReal.coe_add, Real.coe_toNNReal _ hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        exact add_comm _ _
      _ = _ := by
        simpa only [zero_add, add_comm (t : ℝ) (s : ℝ)] using
          intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (t : ℝ)) g (s : ℝ)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hg 0 s)
    (hg s (s + t))
  simp only [compensatedTest, gmpShiftPath, ContinuousMap.coe_mk, add_zero,
    NNReal.coe_add] at hshift ⊢
  rw [hshift]
  dsimp [g] at hadd
  linarith

private theorem integral_shift_on_past {d : ℕ} {hd : 2 ≤ d} {Λ : ℝ} {hΛ : 1 ≤ Λ}
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h₀ h₁)
    (x : Vec d) (s : ℝ≥0) (E : Set (Path d))
    (hE : MeasurableSet[pathFiltration d s] E)
    (F : Path d → ℝ) (hF : Measurable F) (B : ℝ) (hB : ∀ γ, ‖F γ‖ ≤ B) :
    (∫ γ in E, F (gmpShiftPath s γ) ∂R.pathLaw x) =
      ∫ y, ∫ γ, F γ ∂R.pathLaw y
        ∂(((R.pathLaw x).restrict E).map (pathPosition s)) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have hpast : MeasurableSet[gmpPastSigma s] E :=
    (pastSigma_eq_pathFiltration s).symm ▸ hE
  let K := R.pathLaw.restrict (gmpPastSigma_le s E hpast)
  have hrestart := congrArg (fun K : Kernel (Vec d) (Path d) => K x)
    (gmpPathLaw_restrict_past_map_shift R s E hpast)
  have hi : Integrable F ((R.pathLaw ∘ₖ K.map (pathPosition s)) x) :=
    (integrable_const B).mono' hF.aestronglyMeasurable (ae_of_all _ hB)
  have he : (∫ γ, F γ ∂(K.map (gmpShiftPath s)) x) =
      ∫ γ in E, F (gmpShiftPath s γ) ∂R.pathLaw x := by
    rw [Kernel.map_apply _ (measurable_gmpShiftPath s)]
    exact integral_map (measurable_gmpShiftPath s).aemeasurable hF.aestronglyMeasurable
  rw [← he, hrestart, Kernel.integral_comp hi,
    Kernel.map_apply _ (measurable_pathPosition s)]
  rfl


/-- The supplied GMP law solves the full compact-test martingale problem at every start. -/
theorem actual_solves_martingale_problem :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1)
  (x : Vec d),
  SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x (R.pathLaw x) := by
  intro d hd Λ hΛ ω hω lam h0 h1 R x
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  refine ⟨inferInstance, R.pathLaw_starts_at x, ?_⟩
  intro f hf hc
  let L := physicalGenerator (firstCoordinateIndex hd) ω lam
  have hL : Measurable (L f) := measurable_physicalGenerator _ ω lam f
  have hLi (γ : Path d) (a b : ℝ) :
      IntervalIntegrable (fun u => L f (γ u.toNNReal)) volume a b :=
    sbxS4_intervalIntegrable_physicalGenerator hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc γ a b
  have hi := integrable_compensated_test hd hΛ R f hf hc x
  have ha := stronglyAdapted_compensatedTest_of_measurable L f hf.continuous hL
  refine ⟨fun t => ae_of_all _ fun γ => hLi γ 0 t, hi, ha, ?_⟩
  intro s u hsu
  apply Filter.EventuallyEq.symm
  apply ae_eq_condExp_of_forall_setIntegral_eq (pathFiltration d |>.le s) (hi u)
  · intro E hE hfinite
    exact (hi s).integrableOn
  · intro E hE hfinite
    have hF : Measurable (compensatedTest L f (u - s)) :=
      ((ha (u - s)).mono ((pathFiltration d).le (u - s))).measurable
    let fB := gantertCompactObservable f hf.continuous hc
    obtain ⟨B, -, hB⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
      (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
    have hbound (γ : Path d) :
        ‖compensatedTest L f (u - s) γ‖ ≤ 2 * ‖fB‖ + B * ((u - s : ℝ≥0) : ℝ) :=
      abs_compensatedTest_le (L := L) (φ := f) (fun y => fB.norm_coe_le_norm y)
        hB (u - s) γ
    have he := integral_shift_on_past R x s E hE
      (compensatedTest L f (u - s)) hF _ hbound
    simp_rw [compensatedTest_shift L f hLi s (u - s), add_tsub_cancel_of_le hsu] at he
    have hz (y : Vec d) : (∫ γ, compensatedTest L f (u - s) γ ∂R.pathLaw y) = 0 :=
      compensated_test_mean_zero hd hΛ R f hf hc y (u - s)
    simp_rw [hz] at he
    rw [integral_zero, integral_sub (hi u).integrableOn (hi s).integrableOn] at he
    exact (sub_eq_zero.mp he).symm
  · exact (ha s).aestronglyMeasurable

/-- The zero-potential GMP realization has exactly the reduced generator. -/
theorem physicalGenerator_zeroPotentialReducedPair {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) :
    physicalGenerator i (zeroPotentialReducedPair ω) lam = reducedGenerator i ω lam := by
  funext f x
  unfold physicalGenerator reducedGenerator
  simp_rw [reducedCoefficient_zeroPotentialReducedPair]
  change Real.exp (2 * (0 : ℝ)) / 2 * _ + _ = _
  rw [mul_zero, Real.exp_zero]
  rfl

/-- The literal supplied GMP reduced kernel solves the reduced martingale problem
at all starts, with no smooth-coefficient hypothesis. -/
theorem reduced_kernel_solves_martingale_problem {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) x (P (x, ω)) := by
  filter_upwards [hP] with ω hω x
  obtain ⟨hω, R, hR⟩ := hω
  rw [hR x, ← physicalGenerator_zeroPotentialReducedPair]
  exact actual_solves_martingale_problem hd
    (one_le_sourceReducedBound Q.ellipticity_parameter) R x

/-- The real-semigroup dependency identifies the supplied reduced GMP endpoint
with the actual stationary evolution, without an assumed Girsanov step. -/
theorem supplied_endpoint_eq_semigroup
    (hreal : Blueprint.node_e_u3A_generators_u23_real_u2D_semigroupStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  have hmp : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (firstCoordinateIndex hd) ω lam) 0 (P (0, ω)) := by
    filter_upwards [reduced_kernel_solves_martingale_problem hd Q lam h0 h1 P hP] with ω hω
    exact hω 0
  exact (hreal d hd Λ₀ r₀ Q lam).2.2.2.2 P hmp t f

/-- The GMP reduced kernel acts on complex L² as the forced environment evolution at the law
`Q`: the semigroup/path identification at one law. -/
def GMPReducedKernelActionAt {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    Prop :=
  ∀ (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d),
    IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P →
    ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)),
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)

/-- The GMP reduced kernel acts on complex L² as the forced environment evolution, for every
regular law: the semigroup/path identification. The real-semigroup contract V1 gives it
(`gmpReducedKernelAction_of_real`). -/
def GMPReducedKernelAction : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀), GMPReducedKernelActionAt hd Q

theorem gmpReducedKernelAction_of_real
    (hreal : Blueprint.node_e_u3A_generators_u23_real_u2D_semigroupStmt) :
    GMPReducedKernelAction :=
  fun _ hd _ _ Q lam h0 h1 P hP t f => supplied_endpoint_eq_semigroup hreal hd Q lam h0 h1 P hP t f

/-- Reduced-law representative equalities hold at the literal supplied GMP endpoint.
Positive-time endpoint absolute continuity and stationarity justify evaluation on
random translations; time zero uses the actual starting-point condition. -/
theorem ae_eq_at_supplied_endpoint {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (t : ℝ≥0) {f g : FieldPair d → ℂ} (hf : Measurable f) (hg : Measurable g)
    (heq : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂P (0, ω),
      f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) := by
  have horigin : ∀ᵐ ω ∂Q.measure, f (reduce ω) = g (reduce ω) :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable heq
  by_cases ht : t = 0
  · subst t
    filter_upwards [hP, horigin] with ω hω he
    obtain ⟨hω, R, hR⟩ := hω
    rw [hR 0]
    filter_upwards [R.pathLaw_starts_at 0] with γ hγ
    have hstart : γ 0 = 0 := hγ
    simpa only [hstart, translate_zero] using he
  · have htpos : 0 < t := lt_of_le_of_ne (show 0 ≤ t from bot_le) (Ne.symm ht)
    have hm : Measurable (fun p : Vec d × FieldPair d => translate p.1 (reduce p.2)) :=
      Probability.continuous_translate.measurable.comp
        (measurable_fst.prodMk (Probability.measurable_reduce.comp measurable_snd))
    have hspace : ∀ᵐ ω ∂Q.measure, ∀ᵐ x : Vec d ∂volume,
        f (translate x (reduce ω)) = g (translate x (reduce ω)) := by
      apply (Measure.ae_ae_comm (μ := volume) (ν := Q.measure)
        (p := fun x ω => f (translate x (reduce ω)) = g (translate x (reduce ω)))
        (measurableSet_eq_fun (hf.comp hm) (hg.comp hm))).mp
      apply Filter.Eventually.of_forall
      intro x
      have hshift : ∀ᵐ η ∂reducedLaw Q, f (translate x η) = g (translate x η) := by
        apply ae_of_ae_map (μ := reducedLaw Q) (p := fun η => f η = g η)
          (Probability.measurable_translate x).aemeasurable
        rwa [reducedLaw_stationary Q x]
      exact ae_of_ae_map Probability.measurable_reduce.aemeasurable hshift
    filter_upwards [hspace,
      map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel hd
        Q.ellipticity_parameter Q lam h0 h1 P hP t htpos] with ω hspace hac
    exact ae_of_ae_map (measurable_pathPosition t).aemeasurable ((hac 0).ae_le hspace)

/-- The supplied endpoint has the literal positive power moment represented by
its stationary L² power lift, including quenched integrability. -/
theorem supplied_power_endpoint
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hact : GMPReducedKernelActionAt hd Q)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (t : ℝ≥0) {G : FieldPair d → ℝ} (hGm : Measurable G) {q : ℝ} (hq : 0 < q)
    (hG : MemLp G (2 * ENNReal.ofReal q) (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => ‖G (translate (γ t) (reduce ω))‖ ^ q) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
          (sbxS4PowerLift hq hG) (reduce ω) =
        Complex.ofReal (∫ γ : Path d, ‖G (translate (γ t) (reduce ω))‖ ^ q ∂P (0, ω)) ∧
      ‖forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
          (sbxS4PowerLift hq hG) (reduce ω)‖ =
        ∫ γ : Path d, ‖G (translate (γ t) (reduce ω))‖ ^ q ∂P (0, ω) := by
  have heq := ae_eq_at_supplied_endpoint hd Q lam h0 h1 P hP t
    (Lp.stronglyMeasurable (sbxS4PowerLift hq hG)).measurable
    (Complex.continuous_ofReal.measurable.comp (hGm.norm.pow_const q))
    (sbxS4PowerLift_coeFn hq hG)
  filter_upwards [heq,
    hact lam h0 h1 P hP t
      (sbxS4PowerLift hq hG)] with ω heq hsem
  have hi := hsem.1.congr heq
  have hir : Integrable (fun γ : Path d => ‖G (translate (γ t) (reduce ω))‖ ^ q)
      (P (0, ω)) := by
    simpa only [Function.comp_apply, RCLike.re_to_complex, Complex.ofReal_re] using hi.re
  have he : forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
        (sbxS4PowerLift hq hG) (reduce ω) =
      Complex.ofReal (∫ γ : Path d, ‖G (translate (γ t) (reduce ω))‖ ^ q ∂P (0, ω)) := by
    rw [hsem.2, integral_congr_ae heq]
    simpa only [Function.comp_apply] using
      (integral_complex_ofReal (μ := P (0, ω))
        (f := fun γ : Path d => ‖G (translate (γ t) (reduce ω))‖ ^ q))
  refine ⟨hir, he, ?_⟩
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
  exact integral_nonneg fun γ => Real.rpow_nonneg (norm_nonneg _) _

end SbxS4Dynkin

/-- A positive power weight times the norm of an actual stationary L² field is
integrable. This keeps the literal observable when choosing L² representatives. -/
theorem sbxS4_power_weight_integrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {F : FieldPair d → ℝ} {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) (reducedLaw Q))
    (H : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ‖F ω‖ ^ q * ‖H ω‖) (reducedLaw Q) := by
  have hi := (Lp.memLp (sbxS4PowerLift hq hF)).norm.integrable_mul (Lp.memLp H).norm
  apply hi.congr
  filter_upwards [sbxS4PowerLift_coeFn hq hF] with ω hω
  dsimp only [Pi.mul_apply]
  rw [hω, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]

/-- The literal positive-power product under the supplied split law is integrable
and its moment is exactly the actual stationary semigroup pairing. -/
theorem sbxS4_supplied_power_pairing
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hact : SbxS4Dynkin.GMPReducedKernelActionAt hd Q)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F G : FieldPair d → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) (reducedLaw Q))
    (hG : MemLp G (2 * ENNReal.ofReal q) (reducedLaw Q)) :
    Integrable (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      ‖F (reduce ωz.1)‖ ^ q * ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ q)
        (Regeneration.annealedCoupledLaw Q.measure K) ∧
      Complex.ofReal (∫ ωz : FieldPair d × Regeneration.CoupledSample d,
        ‖F (reduce ωz.1)‖ ^ q * ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ q
          ∂Regeneration.annealedCoupledLaw Q.measure K) =
        ∫ ω, sbxS4PowerLift hq hF ω *
          forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
            (sbxS4PowerLift hq hG) ω ∂reducedLaw Q := by
  let H := forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
    (sbxS4PowerLift hq hG)
  let κ := Probability.probabilityPart (Regeneration.originCoupledLaw K)
  let W : FieldPair d × Regeneration.CoupledSample d → ℝ := fun ωz =>
    ‖F (reduce ωz.1)‖ ^ q * ‖G (translate (ωz.2.1 t) (reduce ωz.1))‖ ^ q
  let J : FieldPair d → ℝ := fun ω => ‖F (reduce ω)‖ ^ q * ‖H (reduce ω)‖
  have hW : Measurable W := by
    have hr : Measurable (fun w : FieldPair d × Regeneration.CoupledSample d =>
        reduce w.1) := Probability.measurable_reduce.comp measurable_fst
    have ht : Measurable (fun w : FieldPair d × Regeneration.CoupledSample d =>
        w.2.1 t) := (continuous_eval_const t).measurable.comp measurable_snd.fst
    exact ((hFm.comp hr).norm.pow_const q).mul
      ((hGm.comp (Probability.continuous_translate.measurable.comp
        (ht.prodMk hr))).norm.pow_const q)
  have hJ : Integrable J Q.measure :=
    (sbxS4_power_weight_integrable Q hq hF H).comp_measurable Probability.measurable_reduce
  have hnorm (w : FieldPair d × Regeneration.CoupledSample d) : ‖W w‖ = W w :=
    Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _)
      (Real.rpow_nonneg (norm_nonneg _) _))
  have hdata : ∀ᵐ ω ∂Q.measure,
      Integrable (fun z => W (ω, z)) (κ ω) ∧
      (∫ z, W (ω, z) ∂κ ω) = J ω ∧
      Complex.ofReal (∫ z, W (ω, z) ∂κ ω) =
        Complex.ofReal (‖F (reduce ω)‖ ^ q) * H (reduce ω) := by
    filter_upwards [Probability.probabilityPart_ae_eq Q.measure
        (Regeneration.originCoupledLaw K) hK.1.1, hK.2.1.1,
      SbxS4Dynkin.supplied_power_endpoint hd Q hact lam h0 h1 P hK.2.2.1 t hGm hq hG]
      with ω hκ hpath hGω
    change κ ω = K (0, ω) at hκ
    have hGmap : Integrable (fun γ : Path d => ‖G (translate (γ t) (reduce ω))‖ ^ q)
        ((K (0, ω)).map Prod.fst) := by
      rw [hpath]
      exact hGω.1
    have hiz := hGmap.comp_measurable measurable_fst
    have hmean : (∫ z, W (ω, z) ∂K (0, ω)) =
        ‖F (reduce ω)‖ ^ q *
          ∫ γ : Path d, ‖G (translate (γ t) (reduce ω))‖ ^ q ∂P (0, ω) := by
      rw [show (fun z => W (ω, z)) =
        (fun z : Regeneration.CoupledSample d => ‖F (reduce ω)‖ ^ q *
          ‖G (translate (z.1 t) (reduce ω))‖ ^ q) from rfl, integral_const_mul]
      congr 1
      rw [← hpath, integral_map measurable_fst.aemeasurable hGmap.aestronglyMeasurable]
    refine ⟨?_, ?_, ?_⟩
    · rw [hκ]
      exact hiz.const_mul (‖F (reduce ω)‖ ^ q)
    · rw [hκ, hmean, ← hGω.2.2]
    · rw [hκ, hmean, Complex.ofReal_mul, ← hGω.2.1]
  have hi : Integrable W (Regeneration.annealedCoupledLaw Q.measure K) := by
    apply (Measure.integrable_compProd_iff hW.aestronglyMeasurable).mpr
    refine ⟨hdata.mono fun _ h => h.1, hJ.congr ?_⟩
    filter_upwards [hdata] with ω hω
    simp_rw [hnorm]
    exact hω.2.1.symm
  refine ⟨hi, ?_⟩
  calc
    Complex.ofReal (∫ w, W w ∂Regeneration.annealedCoupledLaw Q.measure K) =
        ∫ ω, Complex.ofReal (∫ z, W (ω, z) ∂κ ω) ∂Q.measure := by
      change Complex.ofReal (∫ w, W w ∂Q.measure.compProd κ) = _
      rw [Measure.integral_compProd hi, integral_complex_ofReal]
    _ = ∫ ω, sbxS4PowerLift hq hF (reduce ω) * H (reduce ω) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [hdata, ae_of_ae_map Probability.measurable_reduce.aemeasurable
        (sbxS4PowerLift_coeFn hq hF)] with ω hω hFω
      rw [hω.2.2, hFω]
    _ = ∫ ω, sbxS4PowerLift hq hF ω * H ω ∂reducedLaw Q := by
      exact (integral_map Probability.measurable_reduce.aemeasurable
        (((Lp.stronglyMeasurable (sbxS4PowerLift hq hF)).mul
          (Lp.stronglyMeasurable H)).aestronglyMeasurable)).symm

/-- The literal coupled observation has the finite moment controlled by the
stationary pairing, with equality of its rooted moment and its Lᑫ norm. -/
theorem sbxS4_supplied_product_memLp_and_norm
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hact : SbxS4Dynkin.GMPReducedKernelActionAt hd Q)
    (lam l δ : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0 h1 P K)
    (t : ℝ≥0) {F G : FieldPair d → ℝ} (hFm : Measurable F) (hGm : Measurable G)
    {q : ℝ} (hq : 0 < q)
    (hF : MemLp F (2 * ENNReal.ofReal q) (reducedLaw Q))
    (hG : MemLp G (2 * ENNReal.ofReal q) (reducedLaw Q)) :
    MemLp (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)))
        (ENNReal.ofReal q) (Regeneration.annealedCoupledLaw Q.measure K) ∧
      (eLpNorm (fun ωz : FieldPair d × Regeneration.CoupledSample d =>
        F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)))
          (ENNReal.ofReal q) (Regeneration.annealedCoupledLaw Q.measure K)).toReal =
        ‖∫ ω, sbxS4PowerLift hq hF ω *
          forcedComplexEvolution Q (firstCoordinateIndex hd) (lam : ℂ) t
            (sbxS4PowerLift hq hG) ω ∂reducedLaw Q‖ ^ q⁻¹ := by
  let f : FieldPair d × Regeneration.CoupledSample d → ℝ := fun w =>
    F (reduce w.1) * G (translate (w.2.1 t) (reduce w.1))
  have hm : Measurable f := by
    have hr : Measurable (fun w : FieldPair d × Regeneration.CoupledSample d =>
        reduce w.1) := Probability.measurable_reduce.comp measurable_fst
    have ht : Measurable (fun w : FieldPair d × Regeneration.CoupledSample d =>
        w.2.1 t) := (continuous_eval_const t).measurable.comp measurable_snd.fst
    exact (hFm.comp hr).mul (hGm.comp
      (Probability.continuous_translate.measurable.comp (ht.prodMk hr)))
  have hp := sbxS4_supplied_power_pairing hd Q hact lam l δ h0 h1 P K hK t hFm hGm hq hF hG
  have hpow (w : FieldPair d × Regeneration.CoupledSample d) :
      ‖f w‖ ^ q = ‖F (reduce w.1)‖ ^ q * ‖G (translate (w.2.1 t) (reduce w.1))‖ ^ q := by
    rw [show f w = F (reduce w.1) * G (translate (w.2.1 t) (reduce w.1)) from rfl,
      norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hi : Integrable (fun w => ‖f w‖ ^ q) (Regeneration.annealedCoupledLaw Q.measure K) := by
    simpa only [hpow] using hp.1
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hf : MemLp f (ENNReal.ofReal q) (Regeneration.annealedCoupledLaw Q.measure K) :=
    (integrable_norm_rpow_iff hm.aestronglyMeasurable hq0 ENNReal.ofReal_ne_top).mp
      (by simpa only [ENNReal.toReal_ofReal hq.le] using hi)
  refine ⟨hf, ?_⟩
  change (eLpNorm f (ENNReal.ofReal q) _).toReal = _
  rw [hf.eLpNorm_eq_integral_rpow_norm hq0 ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le, ENNReal.toReal_ofReal (Real.rpow_nonneg
      (integral_nonneg (fun w => Real.rpow_nonneg (norm_nonneg (f w)) q)) _),
    ← hp.2, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun w =>
      mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)))]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall hpow)

/-- A measure bounded by twice the annealed measure incurs only the same fixed
factor in the restricted Hölder estimate. -/
theorem sbxS4_restricted_integral_bound_of_le_two
    {α : Type*} [MeasurableSpace α] {μ ν : Measure α} [IsFiniteMeasure μ]
    (hν : ν ≤ (2 : ℝ≥0∞) • μ) {f : α → ℝ} {q : ℝ} (hq : 1 ≤ q)
    (hf : MemLp f (ENNReal.ofReal q) μ) (A : Set α) :
    IntegrableOn f A ν ∧
      |∫ x in A, f x ∂ν| ≤
        2 * (eLpNorm f (ENNReal.ofReal q) μ).toReal * (μ A).toReal ^ (1 - 1 / q) := by
  have hA := (sbxS4_restricted_integral_bound hq hf A).1
  have hi2 : Integrable f ((2 : ℝ≥0∞) • μ.restrict A) :=
    hA.smul_measure (by norm_num)
  have hνA : ν.restrict A ≤ (2 : ℝ≥0∞) • μ.restrict A := by
    simpa only [Measure.restrict_smul] using Measure.restrict_mono_measure hν A
  have hn := sbxS4_restricted_integral_bound hq hf.norm A
  refine ⟨hi2.mono_measure hνA, ?_⟩
  calc
    |∫ x in A, f x ∂ν| = ‖∫ x in A, f x ∂ν‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x in A, ‖f x‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖f x‖ ∂((2 : ℝ≥0∞) • μ.restrict A) :=
      integral_mono_measure hνA (ae_of_all _ fun x => norm_nonneg (f x)) hi2.norm
    _ = 2 * ∫ x in A, ‖f x‖ ∂μ := by
      rw [integral_smul_measure]
      norm_num
    _ ≤ 2 * ((eLpNorm f (ENNReal.ofReal q) μ).toReal * (μ A).toReal ^ (1 - 1 / q)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      have hnpos : 0 ≤ ∫ x in A, ‖f x‖ ∂μ :=
        integral_nonneg (fun x => norm_nonneg (f x))
      simpa only [eLpNorm_norm f hf.aestronglyMeasurable, abs_of_nonneg hnpos] using hn.2
    _ = _ := by ring

namespace Blueprint

/-- The deterministic-time remainder estimate on the actual supplied split law, from the
regeneration tails and the GMP reduced-kernel action at each law. The constants do not depend
on the law. -/
theorem remainder_moment_of_actionAt (htail : node_app_u3A_regen_u2D_tailsStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (B b : ℝ), 0 < B → 0 < b →
    ∃ l₀ p c C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀), SbxS4Dynkin.GMPReducedKernelActionAt hd Q →
    ∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (A : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → MeasurableSet A →
    Regeneration.annealedCoupledLaw Q.measure K A ≤
      ENNReal.ofReal (B * Real.exp (B * J - b * lam ^ 2 * (t : ℝ))) →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) A μ ∧
      |∫ ωz in A, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd Λ₀ r₀ B b hB hb
  obtain ⟨l₀, hl₀, hsep, hhalf⟩ := c3Remainder_exists_noReturn_half htail d hd Λ₀ r₀
  obtain ⟨q, hq, hq2, hgrowth⟩ :=
    sbxS4_exists_semigroup_power_pairing_small_growth d Λ₀ r₀ b hb
  let C := 2 * max 1 B
  have hmax : 0 < max 1 B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hC : 0 < C := mul_pos (by norm_num) hmax
  have hBC : B ≤ C := by
    dsimp only [C]
    nlinarith only [le_max_right (1 : ℝ) B, hmax]
  refine ⟨l₀, 2 * q, b / 4, C, hl₀, hsep, by linarith only [hq2],
    div_pos hb (by norm_num), hC, ?_⟩
  intro Q hact lam h0 h1 l δ hl hδ0 hδ1 P K hK hD F G hFm hGm hF hG J t A hJ hA hprob μ hμ
  let ρ := Regeneration.annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure ρ := Regeneration.annealedCoupledLaw_isProbabilityMeasure
    Q.measure K hK.1
  have hν : μ ≤ (2 : ℝ≥0∞) • ρ := by
    apply Measure.le_iff.mpr
    intro E hE
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hμ
    rcases hμ with rfl | rfl
    · change ρ E ≤ 2 * ρ E
      calc
        ρ E = 1 * ρ E := (one_mul _).symm
        _ ≤ 2 * ρ E := mul_le_mul' (by norm_num : (1 : ℝ≥0∞) ≤ 2) le_rfl
    · change regenerationConditionedLaw hd Q lam l K hK.1 hD E ≤ 2 * ρ E
      exact c3Remainder_conditioned_event_le_two hd Q lam l K hK.1 hD
        (hhalf l δ hl hδ0 hδ1 Q lam h0 h1 P K hK) hE
  have hp : ENNReal.ofReal (2 * q) = 2 * ENNReal.ofReal q := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hp] at hF hG
  have hmoment := sbxS4_supplied_product_memLp_and_norm hd Q hact lam l δ h0.le h1
    P K hK t hFm hGm hq hF hG
  have hholder := sbxS4_restricted_integral_bound_of_le_two hν
    (by linarith only [hq2] : 1 ≤ q) hmoment.1 A
  refine ⟨hholder.1, hholder.2.trans ?_⟩
  let s : ℝ := lam ^ 2 * (t : ℝ)
  let m : ℝ := (ρ A).toReal
  let NF : ℝ := (eLpNorm F (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal
  let NG : ℝ := (eLpNorm G (2 * ENNReal.ofReal q) (reducedLaw Q)).toReal
  have hroot : (eLpNorm (fun w : FieldPair d × Regeneration.CoupledSample d =>
      F (reduce w.1) * G (translate (w.2.1 t) (reduce w.1))) (ENNReal.ofReal q) ρ).toReal ≤
      Real.exp (b / 4 * s) * NF * NG := by
    rw [hmoment.2]
    simpa only [s, NF, NG, mul_assoc] using
      hgrowth Q (firstCoordinateIndex hd) lam t F G hF hG
  have hmB : m ≤ B * Real.exp (B * J - b * s) := by
    have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hprob
    simpa only [m, ρ, s, mul_assoc,
      ENNReal.toReal_ofReal (mul_nonneg hB.le (Real.exp_pos _).le)] using hr
  have hdecay := sbxS4_event_decay hB hb.le hJ
    (mul_nonneg (sq_nonneg lam) t.coe_nonneg) hq2
    (show 0 ≤ m from ENNReal.toReal_nonneg) hmB
  have hexp : Real.exp (B * J - b / 4 * s) ≤ Real.exp (C * J - b / 4 * s) :=
    Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_right hBC hJ) _)
  change 2 * (eLpNorm _ (ENNReal.ofReal q) ρ).toReal * m ^ (1 - 1 / q) ≤ _
  calc
    _ ≤ 2 * (Real.exp (b / 4 * s) * NF * NG) * m ^ (1 - 1 / q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num))
        (Real.rpow_nonneg ENNReal.toReal_nonneg _)
    _ = 2 * (Real.exp (b / 4 * s) * m ^ (1 - 1 / q)) * NF * NG := by ring
    _ ≤ 2 * (max 1 B * Real.exp (B * J - b / 4 * s)) * NF * NG :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdecay (by norm_num))
          ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    _ ≤ C * Real.exp (C * J - b / 4 * s) * NF * NG := by
      dsimp only [C]
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
      calc
        _ = (2 * max 1 B) * Real.exp (B * J - b / 4 * s) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hexp hC.le
    _ = _ := by simp only [hp, s, NF, NG, mul_assoc]

/-- The deterministic-time remainder estimate on the actual supplied split law, from the
regeneration tails and the GMP reduced-kernel action. -/
theorem node_rt_u3A_remainder_u2D_moment_of_action
    (htail : node_app_u3A_regen_u2D_tailsStmt)
    (hact : SbxS4Dynkin.GMPReducedKernelAction) :
    node_rt_u3A_remainder_u2D_momentStmt := by
  intro d hd Λ₀ r₀ B b hB hb
  obtain ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, h⟩ :=
    remainder_moment_of_actionAt htail d hd Λ₀ r₀ B b hB hb
  exact ⟨l₀, p, c, C, hl₀, hsep, hp, hc, hC, fun Q => h Q (hact d hd Λ₀ r₀ Q)⟩

/-- The deterministic-time remainder estimate on the actual supplied split law,
using the regeneration tails and the real semigroup identification. -/
theorem node_rt_u3A_remainder_u2D_moment_of_deps
    (htail : node_app_u3A_regen_u2D_tailsStmt)
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmt) :
    node_rt_u3A_remainder_u2D_momentStmt :=
  node_rt_u3A_remainder_u2D_moment_of_action htail
    (SbxS4Dynkin.gmpReducedKernelAction_of_real hreal)

end Blueprint

end EinsteinFull
