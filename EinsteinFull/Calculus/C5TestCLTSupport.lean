import EinsteinFull.Calculus.AKMNegativeSobolevTransfer
import EinsteinRelation.Environment.AKMMeasurableRepresentative
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_l2
import EinsteinFull.Work.W7.ClockComplexSchwartzCovarianceProof
import EinsteinFull.Calculus.S1CovarianceL2Support
import EinsteinRelation.Correctors.ScalarRmsHomogeneity
import EinsteinRelation.Correctors.AKMSourceDirichletUpperBound
import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinRelation.Correctors.BoundedTestRms
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
import EinsteinRelation.Correctors.WeakDivergenceH1Testing
import EinsteinRelation.Correctors.PairedPDECoercivity
import EinsteinRelation.Correctors.WeakCorrectorDifference
import EinsteinRelation.Correctors.WeakGradientCentering
import EinsteinRelation.Correctors.PairedSpatialCutoff
import EinsteinRelation.Correctors.SublinearCorrectorDifference
import EinsteinRelation.Correctors.NormBallVolumeBound
import EinsteinRelation.Mobility.DriftBoundPointwise
import EinsteinRelation.Mobility.VelocityRateFromSteps
import EinsteinFull.Calculus.C3SublinearPairSupport
import EinsteinRelation.External.AKMSourceCorrectorIdentification
import EinsteinFull.Calculus.C6CoarseIdentificationSupport

/-! Compact real tests of the full anisotropic source commutator.
The matrix is kept explicit until its canonical identification; a uniform
bound follows directly from its variational characterization. Independent clock estimates use the exact frozen Schwartz
norm; source-to-horizontal commutator identification remains separate. -/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Calculus.C5TestCLT
open EinsteinRelation EinsteinRelation.External.AKM
open External.Source.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Rescaled source gradient and centered-flux test averages are measurable
in every dimension. Raw coefficient evaluation is handled by its proved
jointly measurable representative, which agrees spatially almost everywhere. -/
theorem measurable_rescaled_test_averages {d : ℕ} {K : ℝ}
    (e : Vec d) (G : Coefficient d K → Vec d → Vec d)
    (hG : Measurable (fun z : Coefficient d K × Vec d => G z.1 z.2))
    {ε : ℝ} (hε : 0 < ε) {ψ : Vec d → ℝ} (hψm : Measurable ψ)
    (j : Fin d) (b : Vec d) :
    Measurable (fun a : Coefficient d K =>
      ⨍ x in originBall d 1, G a (ε⁻¹ • x) j * ψ x) ∧
    Measurable (fun a : Coefficient d K => ⨍ x in originBall d 1,
      ((a (ε⁻¹ • x)).mulVec (e + G a (ε⁻¹ • x)) - b) j * ψ x) := by
  have hsc : Measurable (fun z : Coefficient d K × Vec d => ε⁻¹ • z.2) := by fun_prop
  have hGs := hG.comp (measurable_fst.prodMk hsc)
  have hsetavg : ∀ H : Coefficient d K → Vec d → ℝ,
      Measurable (fun z : Coefficient d K × Vec d => H z.1 z.2) →
      Measurable (fun a : Coefficient d K => ⨍ x in originBall d 1, H a x) := by
    intro H hH
    have hI : Measurable (fun a : Coefficient d K => ∫ x in originBall d 1, H a x) :=
      (hH.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (originBall d 1))).measurable
    simp only [setAverage_eq, smul_eq_mul]
    exact hI.const_mul _
  have hψs := hψm.comp (measurable_snd : Measurable
    (Prod.snd : Coefficient d K × Vec d → Vec d))
  refine ⟨hsetavg _ (((measurable_pi_apply j).comp hGs).mul hψs), ?_⟩
  let H : Coefficient d K → Vec d → ℝ := fun a x =>
    ((coefficientRepresentative a (ε⁻¹ • x)).mulVec (e + G a (ε⁻¹ • x)) - b) j * ψ x
  have hrep := measurable_coefficientRepresentative.comp (measurable_fst.prodMk hsc)
  have hmv : Measurable (fun z : Coefficient d K × Vec d =>
      (coefficientRepresentative z.1 (ε⁻¹ • z.2)).mulVec (e + G z.1 (ε⁻¹ • z.2))) :=
    (show Continuous (fun p : Mat d × Vec d => p.1.mulVec p.2) from
      continuous_fst.matrix_mulVec continuous_snd).measurable.comp
        (hrep.prodMk (measurable_const.add hGs))
  have hH : Measurable (fun z : Coefficient d K × Vec d => H z.1 z.2) :=
    ((measurable_pi_apply j).comp (hmv.sub measurable_const)).mul hψs
  have heq : (fun a : Coefficient d K => ⨍ x in originBall d 1,
      ((a (ε⁻¹ • x)).mulVec (e + G a (ε⁻¹ • x)) - b) j * ψ x) =
      fun a => ⨍ x in originBall d 1, H a x := by
    funext a
    refine average_congr (ae_restrict_of_ae ?_)
    have hcoef := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (inv_ne_zero hε.ne')).ae (coefficientRepresentative_ae_eq a)
    filter_upwards [hcoef] with x hx
    change coefficientRepresentative a (ε⁻¹ • x) = a.field (ε⁻¹ • x) at hx
    dsimp only [H]
    rw [hx]
  rw [heq]
  exact hsetavg H hH

/-- Compact source commutator tested coordinatewise. This is a difference
of actual normalized averages, before proving spatial integrability and
identifying it with the frozen horizontal commutator. -/
noncomputable def compactSourceCommutatorPairing {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (S : SourceObjects P)
    (e : Vec d) (ε : ℝ) (j : Fin d) (ψ : Vec d → ℝ) (a : Coefficient d K) : ℝ :=
  (⨍ x in originBall d 1,
    ((a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
      S.homogenized.mulVec e) j * ψ x ∂volume) -
    ∑ k, S.homogenized j k * (⨍ x in originBall d 1,
      (S.corrector e).grad a (ε⁻¹ • x) k * ψ x ∂volume)

/-- Measurability of the source compact pairing follows from the actual
source corrector, without a hypothesis about an extended dual supremum. -/
theorem measurable_compactSourceCommutatorPairing {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (S : SourceObjects P) (e : Vec d)
    {ε : ℝ} (hε : 0 < ε) (j : Fin d) {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
    Measurable (compactSourceCommutatorPairing S e ε j ψ) := by
  have htests := fun k => measurable_rescaled_test_averages e
    (S.corrector e).grad (S.corrector e).measurable_grad hε hψ k (S.homogenized.mulVec e)
  exact (htests j).2.sub (Finset.measurable_sum _ fun k _ =>
    (htests k).1.const_mul (S.homogenized j k))

/-- The source centered flux minus the matrix times the corrector gradient
is the literal anisotropic commutator. -/
theorem centered_flux_sub_gradient {d : ℕ} (a A : Mat d) (e g : Vec d) :
    a.mulVec (e + g) - A.mulVec e - A.mulVec g = (a - A).mulVec (e + g) := by
  rw [Matrix.sub_mulVec, Matrix.mulVec_add A]
  exact sub_sub _ _ _

/-- Moving the finite matrix contraction outside a normalized spatial
average, with the required Bochner integrability stated explicitly. -/
theorem average_commutator_pairing {d : ℕ} (U : Set (Vec d))
    (F G : Vec d → Vec d) (A : Mat d) (j : Fin d) (ψ : Vec d → ℝ)
    (hF : ∀ k, Integrable (fun x => F x k * ψ x) (volume.restrict U))
    (hG : Integrable (fun x => G x j * ψ x) (volume.restrict U)) :
    (⨍ x in U, (G x j - ∑ k, A j k * F x k) * ψ x ∂volume) =
      (⨍ x in U, G x j * ψ x ∂volume) -
        ∑ k, A j k * (⨍ x in U, F x k * ψ x ∂volume) := by
  have hs : Integrable (fun x => ∑ k, A j k * (F x k * ψ x)) (volume.restrict U) :=
    integrable_finsetSum _ fun k _ => (hF k).const_mul (A j k)
  simp_rw [sub_mul, Finset.sum_mul, mul_assoc]
  rw [average_fun_sub hG hs, average_fun_finsetSum (fun k _ => (hF k).const_mul (A j k))]
  simp only [average_const_mul]

/-- Subtracting a matrix times the gradient costs its absolute row sum.
This scalar estimate keeps all off-diagonal entries. -/
theorem abs_sub_matrix_row_le {d : ℕ} (A : Mat d) (j : Fin d)
    (f g : Fin d → ℝ) :
    |g j - ∑ k, A j k * f k| ≤
      (1 + ∑ k, |A j k|) * ((∑ k, |f k|) + ∑ k, |g k|) := by
  have hf : ∀ k, |f k| ≤ ∑ l, |f l| := fun k =>
    Finset.single_le_sum (fun l _ => abs_nonneg (f l)) (Finset.mem_univ k)
  have hg : |g j| ≤ ∑ k, |g k| :=
    Finset.single_le_sum (fun k _ => abs_nonneg (g k)) (Finset.mem_univ j)
  have hA : 0 ≤ ∑ k, |A j k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hfg : 0 ≤ ∑ k, |f k| := Finset.sum_nonneg fun k _ => abs_nonneg _
  calc
    |g j - ∑ k, A j k * f k| ≤ |g j| + |∑ k, A j k * f k| := abs_sub _ _
    _ ≤ (∑ k, |g k|) + ∑ k, |A j k * f k| :=
      add_le_add hg (Finset.abs_sum_le_sum_abs _ _)
    _ = (∑ k, |g k|) + ∑ k, |A j k| * |f k| := by simp only [abs_mul]
    _ ≤ (∑ k, |g k|) + ∑ k, |A j k| * (∑ l, |f l|) :=
      add_le_add le_rfl (Finset.sum_le_sum fun k _ =>
        mul_le_mul_of_nonneg_left (hf k) (abs_nonneg (A j k)))
    _ = (∑ k, |g k|) + (∑ k, |A j k|) * (∑ l, |f l|) := by
      rw [Finset.sum_mul]
    _ ≤ (1 + ∑ k, |A j k|) * ((∑ k, |f k|) + ∑ k, |g k|) := by
      have hgg : 0 ≤ ∑ k, |g k| := Finset.sum_nonneg fun k _ => abs_nonneg _
      nlinarith [mul_nonneg hA hgg]

/-- The same stochastic majorant controls a source commutator coordinate
against a normalized compact test, with an explicit anisotropic row factor.
The conclusion is a lower integral; no unproved measurability is needed. -/
theorem compact_commutator_second_moment_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d m : ℕ} {U : Set (Vec d)}
    (F G : Ω → Vec d → Vec d) {Z : Ω → ℝ} {θ : ℝ}
    (hZ : OsBound P Z 1 θ)
    (hz : ∀ᵐ ω ∂P, vectorNegativeIntegerSobolevNorm m U (F ω) +
      vectorNegativeIntegerSobolevNorm m U (G ω) ≤ ENNReal.ofReal (Z ω))
    (A : Mat d) (j : Fin d) (ψ : Vec d → ℝ)
    (hψ : IsSpatialTest U ψ) (hnψ : integerSobolevTestNorm m U ψ ≤ 1) :
    (∫⁻ ω, ENNReal.ofReal
      (((⨍ x in U, G ω x j * ψ x ∂volume) -
        ∑ k, A j k * (⨍ x in U, F ω x k * ψ x ∂volume)) ^ 2) ∂P) ≤
      ENNReal.ofReal (8 * (1 + ∑ k, |A j k|) ^ 2 * θ ^ 2) := by
  let B : ℝ := 1 + ∑ k, |A j k|
  have hB : 0 ≤ B := add_nonneg zero_le_one (Finset.sum_nonneg fun k _ => abs_nonneg _)
  have hm := hZ.moment_pos_le (show (0 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at hm
  have hbound : (∫⁻ ω, ENNReal.ofReal
      (((⨍ x in U, G ω x j * ψ x ∂volume) -
        ∑ k, A j k * (⨍ x in U, F ω x k * ψ x ∂volume)) ^ 2) ∂P) ≤
      ENNReal.ofReal (B ^ 2) * ∫⁻ ω, ENNReal.ofReal ((max (Z ω) 0) ^ 2) ∂P := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply lintegral_mono_ae
    filter_upwards [hz] with ω hω
    have hdual := normalized_two_field_pairing_le (F ω) (G ω) hω
      (fun _ => ψ) (fun _ => ψ) (fun _ => hψ) (fun _ => hnψ)
      (fun _ => hψ) (fun _ => hnψ)
    have hrow := (abs_sub_matrix_row_le A j
      (fun k => ⨍ x in U, F ω x k * ψ x ∂volume)
      (fun k => ⨍ x in U, G ω x k * ψ x ∂volume)).trans
      (mul_le_mul_of_nonneg_left hdual hB)
    rw [← ENNReal.ofReal_mul (sq_nonneg B), ← mul_pow]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = |(⨍ x in U, G ω x j * ψ x ∂volume) -
        ∑ k, A j k * (⨍ x in U, F ω x k * ψ x ∂volume)| ^ 2 := (sq_abs _).symm
      _ ≤ (B * max (Z ω) 0) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hrow 2
  calc
    _ ≤ ENNReal.ofReal (B ^ 2) *
        (∫⁻ ω, ENNReal.ofReal ((max (Z ω) 0) ^ 2) ∂P) := hbound
    _ ≤ ENNReal.ofReal (B ^ 2) * ENNReal.ofReal (8 * θ ^ 2) :=
      mul_le_mul le_rfl (by simpa only [show 2 * θ ^ 2 * (2 : ℝ) ^ 2 = 8 * θ ^ 2 by ring] using hm) bot_le bot_le
    _ = ENNReal.ofReal (8 * (1 + ∑ k, |A j k|) ^ 2 * θ ^ 2) := by
      rw [← ENNReal.ofReal_mul (sq_nonneg B)]
      congr 1
      dsimp only [B]
      ring


/-- AKM's admitted estimate on the actual physical coefficient law controls
compact commutator pairings. The structural constant precedes the law and
tests; the explicit row factor is absorbed into a uniform structural
constant by `compact_commutator_actual_coefficient_law_uniform`. The expression is a difference of
integrals, so no interchange with an unproved integrable sum is used. -/
theorem compact_commutator_actual_coefficient_law
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ),
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ 1 →
        (∫⁻ a, ENNReal.ofReal
          (((⨍ x in originBall d 1,
              ((a (ε⁻¹ • x)).mulVec (e + (S.corrector e).grad a (ε⁻¹ • x)) -
                S.homogenized.mulVec e) j * ψ x ∂volume) -
            ∑ k, S.homogenized j k * (⨍ x in originBall d 1,
              (S.corrector e).grad a (ε⁻¹ • x) k * ψ x ∂volume)) ^ 2)
            ∂actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C * (1 + ∑ k, |S.homogenized j k|) ^ 2 * ε ^ (d : ℝ)) := by
  obtain ⟨C, hC, hsource⟩ := External.akm_negative_sobolev d hd
    (AKMUpperEllipticity L) (Correctors.one_lt_AKMUpperEllipticity hL)
    m hm 1 zero_lt_one one_lt_two
  refine ⟨8 * C ^ 2, mul_pos (by norm_num) (sq_pos_of_pos hC), ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := hsource (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q)
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ hψ hnψ
  obtain ⟨Z, _, hZ, hdual⟩ := hS e he ε hε hε₂
  have hb := compact_commutator_second_moment_le
    (fun a x => (S.corrector e).grad a (ε⁻¹ • x))
    (fun a x => (a (ε⁻¹ • x)).mulVec
      (e + (S.corrector e).grad a (ε⁻¹ • x)) - S.homogenized.mulVec e)
    hZ hdual S.homogenized j ψ hψ hnψ
  have hpower : (ε ^ ((d : ℝ) / 2)) ^ 2 = ε ^ (d : ℝ) := by
    rw [← Real.rpow_mul_natCast hε.le]
    simp only [Nat.cast_ofNat, div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  convert hb using 1
  congr 1
  rw [mul_pow, hpower]
  ring


/-- The admitted compact source estimate produces genuine L² random
variables. Measurability is proved from the source fields, rather than
assumed for the test pairing. This is still a source-law result. -/
theorem exists_compactSourceCommutatorPairing_memLp
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    (r₀ : ℝ) (Q : EnvironmentLaw d L r₀) :
    ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ),
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ 1 →
        MemLp (compactSourceCommutatorPairing S e ε j ψ) 2 (actualCoefficientLaw Q) := by
  obtain ⟨C, _, h⟩ := compact_commutator_actual_coefficient_law d hd L hL m hm
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ hψ hnψ
  have hmeas := measurable_compactSourceCommutatorPairing S e hε j hψ.1.continuous.measurable
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2
  exact (hS e he ε hε hε₂ j ψ hψ hnψ).trans_lt ENNReal.ofReal_lt_top

/-- The zero-order part of the frozen Schwartz norm controls the full spatial
second moment without consuming additional derivatives. -/
theorem schwartz_integral_norm_sq_le {d N : ℕ} (hN : d < N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (∫ x, ‖F x‖ ^ 2) ≤ clockSchwartzWeightMass d N * schwartzTestNorm N F ^ 2 := by
  have hv (x : Vec d) : ‖F x‖ ≤ schwartzTestNorm N F := by
    have hw : 1 ≤ (1 + euclideanNorm x) ^ N :=
      one_le_pow₀ (le_add_of_nonneg_right (Real.sqrt_nonneg _))
    exact (le_mul_of_one_le_left (norm_nonneg _) hw).trans
      (clockSchwartz_weighted_value_le N F x)
  calc
    _ ≤ ∫ x, ‖F x‖ * schwartzTestNorm N F := by
      apply integral_mono (by simpa only [norm_norm] using
        (F.memLp 2 volume).norm.integrable_sq) (F.integrable.norm.mul_const _)
      intro x
      exact (by simpa only [pow_two] using
        mul_le_mul_of_nonneg_left (hv x) (norm_nonneg (F x)))
    _ = (∫ x, ‖F x‖) * schwartzTestNorm N F := integral_mul_const _ _
    _ ≤ (clockSchwartzWeightMass d N * schwartzTestNorm N F) *
        schwartzTestNorm N F :=
      mul_le_mul_of_nonneg_right (clockSchwartz_integral_norm_le hN F)
        (clockSchwartz_norm_nonneg N F)
    _ = _ := by ring

/-- Every continuous real test dominated by the Euclidean joint Schwartz
value is genuinely spatially square integrable, including its rescalings. -/
theorem memLp_rescaled_schwartz_dominated {d : ℕ}
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {f : Vec d → ℝ} (hfc : Continuous f) (hf : ∀ x, |f x| ≤ ‖F x‖)
    {R : ℝ} (hR : 0 < R) :
    MemLp (fun x => f (R⁻¹ • x)) 2 (volume : Measure (Vec d)) := by
  have hm : MemLp f 2 (volume : Measure (Vec d)) :=
    (F.memLp 2).mono hfc.aestronglyMeasurable (ae_of_all _ hf)
  apply (memLp_two_iff_integrable_sq
    (hfc.comp (continuous_id.const_smul R⁻¹)).aestronglyMeasurable).2
  exact hm.integrable_sq.comp_smul (inv_ne_zero hR.ne')

/-- Exact spatial L2 scaling for the real clock tests. The expression is the
actual Lp class, with its membership proved internally. -/
theorem rescaled_schwartz_dominated_norm_sq {d : ℕ}
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {f : Vec d → ℝ} (hfc : Continuous f) (hf : ∀ x, |f x| ≤ ‖F x‖)
    {R : ℝ} (hR : 0 < R) :
    ‖(memLp_rescaled_schwartz_dominated F hfc hf hR).toLp
      (fun x => f (R⁻¹ • x))‖ ^ 2 = (R ^ d) * ∫ x, f x ^ 2 := by
  rw [← S1.l2Size_eq_norm_toLp, S1.l2Size,
    Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
  simp only [Real.norm_eq_abs, sq_abs]
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin,
    mul_one, smul_eq_mul] using!
    Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Vec d))
      (fun x => f x ^ 2) hR.le

/-- The sole graph dependency supplies a law-uniform clock estimate in the
literal joint Schwartz norm, for real and imaginary coordinate tests alike.
The scale normalization cancels exactly, for every positive scale. -/
theorem clock_l2_schwartz_dominated_sq_le
    (hclock : Blueprint.node_e_u3A_clock_u2D_l2Stmt)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀)
    (N : ℕ) (hN : d < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (f : Vec d → ℝ) (hfc : Continuous f) (hf : ∀ x, |f x| ≤ ‖F x‖)
      (R : ℝ) (hR : 0 < R),
      ‖(R ^ (-(d : ℝ) / 2)) • clockTestL2 Q
        ((memLp_rescaled_schwartz_dominated F hfc hf hR).toLp
          (fun x => f (R⁻¹ • x)))‖ ^ 2 ≤ C * schwartzTestNorm N F ^ 2 := by
  obtain ⟨C, hC, h⟩ := hclock d hd L r₀ hL hr₀
  have hw : 0 ≤ clockSchwartzWeightMass d N := integral_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)
  refine ⟨C * (1 + clockSchwartzWeightMass d N), mul_pos hC (by linarith), ?_⟩
  intro Q F f hfc hf R hR
  have hfm : MemLp f 2 (volume : Measure (Vec d)) :=
    (F.memLp 2).mono hfc.aestronglyMeasurable (ae_of_all _ hf)
  have hb : (∫ x, f x ^ 2) ≤ clockSchwartzWeightMass d N * schwartzTestNorm N F ^ 2 := by
    refine (integral_mono hfm.integrable_sq (F.memLp 2).norm.integrable_sq ?_).trans
      (schwartz_integral_norm_sq_le hN F)
    intro x
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).2 (hf x)
  have hs : (R ^ (-(d : ℝ) / 2)) ^ 2 * R ^ d = 1 := by
    rw [← Real.rpow_mul_natCast hR.le, ← Real.rpow_natCast,
      ← Real.rpow_add hR]
    convert Real.rpow_zero R using 1 <;> ring
  have ht := (h Q ((memLp_rescaled_schwartz_dominated F hfc hf hR).toLp
    (fun x => f (R⁻¹ • x)))).2.2
  rw [rescaled_schwartz_dominated_norm_sq F hfc hf hR] at ht
  calc
    _ = (R ^ (-(d : ℝ) / 2)) ^ 2 * ‖clockTestL2 Q
        ((memLp_rescaled_schwartz_dominated F hfc hf hR).toLp
          (fun x => f (R⁻¹ • x)))‖ ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    _ ≤ (R ^ (-(d : ℝ) / 2)) ^ 2 * (C * (R ^ d * ∫ x, f x ^ 2)) :=
      mul_le_mul_of_nonneg_left ht (sq_nonneg _)
    _ = C * ∫ x, f x ^ 2 := by
      calc
        _ = C * ((R ^ (-(d : ℝ) / 2)) ^ 2 * R ^ d) * ∫ x, f x ^ 2 := by ring
        _ = _ := by rw [hs]; ring
    _ ≤ C * (clockSchwartzWeightMass d N * schwartzTestNorm N F ^ 2) :=
      mul_le_mul_of_nonneg_left hb hC.le
    _ ≤ (C * (1 + clockSchwartzWeightMass d N)) * schwartzTestNorm N F ^ 2 := by
      nlinarith [sq_nonneg (schwartzTestNorm N F)]

/-- Every coordinate of the literal joint Bochner pairing separates as an
actual spatial integral. Integrability follows from Schwartz decay and the
stationary translation isometry, without assumptions on the realization. -/
theorem scaledJointPairing_eq_sum_coordinates {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    scaledJointPairing Q R hR Z F =
      ∑ a : JointObservationIndex d,
        scaledComplexClockPairing Q R (Z a) (fun x => F x a) := by
  classical
  letI := reducedLaw_probability Q
  have hi (a : JointObservationIndex d) : Integrable (fun x : Vec d =>
      F (R⁻¹ • x) a • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x (Z a)) := by
    have hc := (PiLp.continuous_apply 2 _ a).comp F.continuous
    have hf : Integrable (fun x => F x a) := F.integrable.mono
      hc.aestronglyMeasurable (ae_of_all _ fun x => PiLp.norm_apply_le (F x) a)
    exact integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
      _ (hf.comp_smul (inv_ne_zero hR.ne'))
      (hc.comp (continuous_id.const_smul R⁻¹)) (Z a)
  unfold scaledJointPairing scaledComplexClockPairing complexClockSpatialPairing
  rw [integral_finsetSum _ (fun a _ => hi a), Finset.smul_sum]

/-- The actual clock and every anisotropic commutator coordinate contribute
to the norm through a finite triangle inequality, before any field estimate. -/
theorem norm_scaledJointPairing_le_coordinate_sum {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    ‖scaledJointPairing Q R hR Z F‖ ≤
      (∑ p : Fin d × Fin d,
        ‖scaledComplexClockPairing Q R (Z (.inl p)) (fun x => F x (.inl p))‖) +
      ‖scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ()))‖ := by
  rw [scaledJointPairing_eq_sum_coordinates Q hR Z F]
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique] using
    norm_sum_le (Finset.univ : Finset (JointObservationIndex d))
      (fun a => scaledComplexClockPairing Q R (Z a) (fun x => F x a))

/-- The real Hilbert covariance of literal translated complex clock observations
is the actual clock covariance under the same joint law. -/
theorem real_inner_translated_clock {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ)) (x y : Vec d) :
    inner ℝ (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y u) =
      clockCovariance Q x y := by
  rw [L2.inner_def]
  have ht (z : Vec d) :
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z u : FieldPair d → ℂ)
        =ᵐ[reducedLaw Q] fun ω => (centeredClockField Q z ω : ℂ) := by
    have hp := (measurePreserving_translate (reducedLaw Q)
      (reducedLaw_stationary Q) z).quasiMeasurePreserving.ae hu
    filter_upwards [coeFn_complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) z u, hp] with ω hω hω'
    rw [hω, hω']
    simp only [centeredClockField, translate_scalar, add_zero]
  unfold clockCovariance
  apply integral_congr_ae
  filter_upwards [ht x, ht y] with ω hx hy
  rw [hx, hy]
  simp [mul_comm]

/-- A real test against the literal complex clock has the same squared norm
as the real clock operator. This identifies the norm without choosing a
pointwise representative for the Bochner spatial integral. -/
theorem norm_complexClockSpatialPairing_real_sq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    {f : Vec d → ℝ} (hc : Continuous f) (hf : Integrable f)
    (hf2 : MemLp f 2 volume) :
    ‖complexClockSpatialPairing Q u (fun x => (f x : ℂ))‖ ^ 2 =
      ‖clockTestL2 Q (hf2.toLp f)‖ ^ 2 := by
  letI := reducedLaw_probability Q
  let T (x : Vec d) := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u
  have hk : (fun x => (f x : ℂ) • T x) = (fun x => f x • T x) := by
    funext x
    exact IsScalarTower.algebraMap_smul ℂ (f x) (T x)
  have hi : Integrable (fun x => f x • T x) := by
    rw [← hk]
    exact
      integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
        (fun x => (f x : ℂ)) hf.ofReal (Complex.continuous_ofReal.comp hc) u
  have hcov : Integrable (fun z : Vec d × Vec d =>
      f z.1 * f z.2 * clockCovariance Q z.1 z.2) := by
    apply ((hf.norm.mul_prod hf.norm).mul_const ((2 * sourceReducedBound L) ^ 2)).mono'
      ((hc.measurable.comp measurable_fst).mul (hc.measurable.comp measurable_snd) |>.mul
        (measurable_clockCovariance Q)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (abs_clockCovariance_le Q z.1 z.2)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  rw [clockTestL2_toLp Q hc.measurable hf hf2]
  have hn := S1.l2Size_eq_norm_toLp (memLp_clockTest Q hc.measurable hf)
  have hs : ‖(memLp_clockTest Q hc.measurable hf).toLp (clockTest Q f)‖ ^ 2 =
      ∫ ω, clockTest Q f ω * clockTest Q f ω ∂reducedLaw Q := by
    rw [← hn, S1.l2Size, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]
    congr 1
    funext ω
    simp [pow_two]
  rw [hs, integral_clockTest_mul Q hc.measurable hc.measurable hf hf,
    show (∫ z : Vec d × Vec d, f z.1 * f z.2 * clockCovariance Q z.1 z.2) =
      ∫ x, ∫ y, f x * f y * clockCovariance Q x y from integral_prod _ hcov]
  change ‖∫ x, (f x : ℂ) • T x‖ ^ 2 = _
  rw [hk]
  rw [← real_inner_self_eq_norm_sq]
  rw [real_inner_comm, ← integral_inner hi]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [real_inner_comm, ← integral_inner hi]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      dsimp only
      rw [real_inner_smul_left, real_inner_smul_right,
        real_inner_translated_clock Q hu]
      ring

/-- Exact transfer of the normalized real-test clock norm to its literal
complex realization, at every positive spatial scale. -/
theorem norm_scaledComplexClockPairing_real_sq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {u : Lp ℂ 2 (reducedLaw Q)}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    {f : Vec d → ℝ} (hc : Continuous f) (hf : ∀ x, |f x| ≤ ‖F x‖)
    {R : ℝ} (hR : 0 < R) :
    ‖scaledComplexClockPairing Q R u (fun x => (f x : ℂ))‖ ^ 2 =
      ‖(R ^ (-(d : ℝ) / 2)) • clockTestL2 Q
        ((memLp_rescaled_schwartz_dominated F hc hf hR).toLp
          (fun x => f (R⁻¹ • x)))‖ ^ 2 := by
  have hfi : Integrable f := F.integrable.mono hc.aestronglyMeasurable
    (ae_of_all _ fun x => by simpa only [Real.norm_eq_abs] using hf x)
  unfold scaledComplexClockPairing
  rw [norm_smul, norm_smul, Complex.norm_real]
  rw [mul_pow, mul_pow]
  congr 1
  exact norm_complexClockSpatialPairing_real_sq Q hu
    (hc.comp (continuous_id.const_smul R⁻¹))
    (hfi.comp_smul (inv_ne_zero hR.ne'))
    (memLp_rescaled_schwartz_dominated F hc hf hR)

/-- The exact real clock premise controls the literal complex clock on every
Schwartz-dominated test, with one constant chosen before the law or realization. -/
theorem complex_clock_l2_schwartz_dominated_le
    (hclock : Blueprint.node_e_u3A_clock_u2D_l2Stmt)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀)
    (N : ℕ) (hN : d < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀)
      (u : Lp ℂ 2 (reducedLaw Q))
      (_hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => (centeredClockField Q 0 ω : ℂ))
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (f : Vec d → ℂ) (_hc : Continuous f) (_hf : ∀ x, ‖f x‖ ≤ ‖F x‖)
      (R : ℝ) (_hR : 0 < R),
      ‖scaledComplexClockPairing Q R u f‖ ≤ C * schwartzTestNorm N F := by
  obtain ⟨C, hC, hb⟩ := clock_l2_schwartz_dominated_sq_le
    hclock d hd L r₀ hL hr₀ N hN
  refine ⟨2 * Real.sqrt C, mul_pos (by norm_num) (Real.sqrt_pos.2 hC), ?_⟩
  intro Q u hu F f hc hf R hR
  have hn := clockSchwartz_norm_nonneg N F
  have hr (g : Vec d → ℝ) (hgc : Continuous g) (hgf : ∀ x, |g x| ≤ ‖F x‖) :
      ‖scaledComplexClockPairing Q R u (fun x => (g x : ℂ))‖ ≤
        Real.sqrt C * schwartzTestNorm N F := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hn)).mp
    rw [mul_pow, Real.sq_sqrt hC.le,
      norm_scaledComplexClockPairing_real_sq Q hu F hgc hgf hR]
    exact hb Q F g hgc hgf R hR
  have hfr : ∀ x, |(f x).re| ≤ ‖F x‖ := fun x =>
    (Complex.abs_re_le_norm (f x)).trans (hf x)
  have hfi : ∀ x, |(f x).im| ≤ ‖F x‖ := fun x =>
    (Complex.abs_im_le_norm (f x)).trans (hf x)
  have hrf := hr (fun x => (f x).re) (Complex.continuous_re.comp hc) hfr
  have hif := hr (fun x => (f x).im) (Complex.continuous_im.comp hc) hfi
  have hfe : Integrable f := F.integrable.mono hc.aestronglyMeasurable (ae_of_all _ hf)
  have he : scaledComplexClockPairing Q R u f =
      scaledComplexClockPairing Q R u (fun x => ((f x).re : ℂ)) +
        Complex.I • scaledComplexClockPairing Q R u (fun x => ((f x).im : ℂ)) := by
    unfold scaledComplexClockPairing
    rw [complexClockSpatialPairing_re_im Q u
      (hfe.comp_smul (inv_ne_zero hR.ne')) (hc.comp (continuous_id.const_smul R⁻¹)),
      smul_add]
    congr 1
    exact smul_comm _ _ _
  calc
    _ ≤ ‖scaledComplexClockPairing Q R u (fun x => ((f x).re : ℂ))‖ +
        ‖Complex.I • scaledComplexClockPairing Q R u (fun x => ((f x).im : ℂ))‖ := by
      rw [he]
      exact norm_add_le _ _
    _ = ‖scaledComplexClockPairing Q R u (fun x => ((f x).re : ℂ))‖ +
        ‖scaledComplexClockPairing Q R u (fun x => ((f x).im : ℂ))‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    _ ≤ Real.sqrt C * schwartzTestNorm N F + Real.sqrt C * schwartzTestNorm N F :=
      add_le_add hrf hif
    _ = _ := by ring

/-- Scalar multiplication commutes with the literal iterated coordinate
partial derivative, including at points where the total derivative is zero. -/
theorem multiIndexDerivative_const_mul {d m : ℕ} (β : Fin d → Fin (m + 1))
    (c : ℝ) (ψ : Vec d → ℝ) :
    multiIndexDerivative β (fun x => c * ψ x) =
      fun x => c * multiIndexDerivative β ψ x := by
  have hlist (l : List (Fin d)) (f : Vec d → ℝ) :
      l.foldr coordinateDerivative (fun x => c * f x) =
        fun x => c * l.foldr coordinateDerivative f x := by
    induction l with
    | nil => rfl
    | cons j l ih =>
      simp only [List.foldr_cons, ih]
      funext x
      change (fderiv ℝ (c • l.foldr coordinateDerivative f) x) (unitVector j) = _
      rw [fderiv_const_smul_field]
      rfl
  exact hlist _ ψ

/-- Homogeneity of the exact source test norm retains every multi-index
and its normalized-volume factor. -/
theorem integerSobolevTestNorm_const_mul {d : ℕ} (m : ℕ) (U : Set (Vec d))
    (c : ℝ) (ψ : Vec d → ℝ) :
    integerSobolevTestNorm m U (fun x => c * ψ x) =
      |c| * integerSobolevTestNorm m U ψ := by
  classical
  unfold integerSobolevTestNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  split_ifs
  · rw [multiIndexDerivative_const_mul, Correctors.scalarRms_const_mul_abs]
    ring
  · exact (mul_zero _).symm

/-- Constant multiples remain actual smooth compact tests on the same domain. -/
theorem isSpatialTest_const_mul {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (c : ℝ) :
    IsSpatialTest U (fun x => c * ψ x) := by
  exact ⟨contDiff_const.mul hψ.1, hψ.2.1.mul_left,
    tsupport_mul_subset_right.trans hψ.2.2⟩

/-- Exact scalar linearity of the source compact pairing does not require
an interchange of a spatial integral and an infinite sum. -/
theorem compactSourceCommutatorPairing_const_mul {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (S : SourceObjects P)
    (e : Vec d) (ε : ℝ) (j : Fin d) (ψ : Vec d → ℝ) (c : ℝ) :
    compactSourceCommutatorPairing S e ε j (fun x => c * ψ x) =
      fun a => c * compactSourceCommutatorPairing S e ε j ψ a := by
  funext a
  unfold compactSourceCommutatorPairing
  simp_rw [show ∀ u v : ℝ, u * (c * v) = c * (u * v) by intros; ring,
    average_const_mul]
  rw [mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Removing the unit-test normalization costs exactly the square of a
positive Sobolev upper bound. The structural constant still precedes the law,
scale and test, and the anisotropic source matrix remains explicit. -/
theorem compact_commutator_actual_coefficient_law_test_bound
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ) (B : ℝ), 0 < B →
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ B →
        (∫⁻ a, ENNReal.ofReal ((compactSourceCommutatorPairing S e ε j ψ a) ^ 2)
          ∂actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C * (1 + ∑ k, |S.homogenized j k|) ^ 2 *
            ε ^ (d : ℝ) * B ^ 2) := by
  obtain ⟨C, hC, h⟩ := compact_commutator_actual_coefficient_law d hd L hL m hm
  refine ⟨C, hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ B hB hψ hnψ
  let χ : Vec d → ℝ := fun x => B⁻¹ * ψ x
  have hχ : IsSpatialTest (originBall d 1) χ := isSpatialTest_const_mul hψ B⁻¹
  have hnχ : integerSobolevTestNorm m (originBall d 1) χ ≤ 1 := by
    rw [integerSobolevTestNorm_const_mul, abs_of_pos (inv_pos.mpr hB)]
    calc
      _ ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left hnψ (inv_nonneg.mpr hB.le)
      _ = 1 := inv_mul_cancel₀ hB.ne'
  have hb := hS e he ε hε hε₂ j χ hχ hnχ
  change (∫⁻ a, ENNReal.ofReal ((compactSourceCommutatorPairing S e ε j χ a) ^ 2)
    ∂actualCoefficientLaw Q) ≤ _ at hb
  have hscale : compactSourceCommutatorPairing S e ε j ψ =
      fun a => B * compactSourceCommutatorPairing S e ε j χ a := by
    rw [show χ = (fun x => B⁻¹ * ψ x) from rfl,
      compactSourceCommutatorPairing_const_mul]
    funext a
    simp only [← mul_assoc, mul_inv_cancel₀ hB.ne', one_mul]
  calc
    _ = ENNReal.ofReal (B ^ 2) *
        (∫⁻ a, ENNReal.ofReal ((compactSourceCommutatorPairing S e ε j χ a) ^ 2)
          ∂actualCoefficientLaw Q) := by
      simp_rw [hscale, mul_pow, ENNReal.ofReal_mul (sq_nonneg B)]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (B ^ 2) *
        ENNReal.ofReal (C * (1 + ∑ k, |S.homogenized j k|) ^ 2 * ε ^ (d : ℝ)) :=
      mul_le_mul le_rfl hb bot_le bot_le
    _ = _ := by
      rw [← ENNReal.ofReal_mul (sq_nonneg B)]
      congr 1
      ring

/-- Every compact smooth source test produces an actual L² random
variable. Its Sobolev norm is finite as a real finite sum; unit normalization
is discharged internally using a strictly positive upper bound. -/
theorem exists_compactSourceCommutatorPairing_memLp_all_tests
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    (r₀ : ℝ) (Q : EnvironmentLaw d L r₀) :
    ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ),
        IsSpatialTest (originBall d 1) ψ →
        MemLp (compactSourceCommutatorPairing S e ε j ψ) 2 (actualCoefficientLaw Q) := by
  obtain ⟨C, _, h⟩ := compact_commutator_actual_coefficient_law_test_bound d hd L hL m hm
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ hψ
  let B := max 1 (integerSobolevTestNorm m (originBall d 1) ψ)
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb := hS e he ε hε hε₂ j ψ B hB hψ (le_max_right _ _)
  have hmeas := measurable_compactSourceCommutatorPairing S e hε j hψ.1.continuous.measurable
  apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
  refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2
  exact hb.trans_lt ENNReal.ofReal_lt_top

/-- The variational characterization bounds the source quadratic form uniformly,
without identifying the source corrector with a canonical realization. -/
theorem source_homogenized_quadratic_bounds {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P] (S : SourceObjects P)
    (e : Vec d) :
    0 ≤ dot e (S.homogenized.mulVec e) ∧
      dot e (S.homogenized.mulVec e) ≤ K * euclideanSq e := by
  have hlo : 0 ≤ (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) :=
    ge_of_tendsto (S.variational_limit e) (Filter.Eventually.of_forall fun n =>
      expected_sourceDirichletEnergy_nonneg P n e)
  have hhi : (1 / 2 : ℝ) * dot e (S.homogenized.mulVec e) ≤
      (K / 2) * euclideanSq e := by
    apply le_of_tendsto (S.variational_limit e)
    apply Filter.Eventually.of_forall
    intro n
    calc
      _ ≤ ∫ _a : Coefficient d K, (K / 2) * euclideanSq e ∂P :=
        integral_mono_of_nonneg
          (ae_of_all _ fun a => sourceDirichletEnergy_nonneg a _ e)
          (integrable_const _) (ae_of_all _ fun a =>
            sourceDirichletEnergy_triadic_upper hK a n e)
      _ = _ := by simp
  constructor <;> linarith

/-- Each entry of the source matrix is controlled by ellipticity alone.
A coarse factor two is enough for finite coordinate assembly. -/
theorem source_homogenized_entry_abs_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P] (S : SourceObjects P)
    (i j : Fin d) : |S.homogenized i j| ≤ 2 * K := by
  have hdiag (k : Fin d) : 0 ≤ S.homogenized k k ∧ S.homogenized k k ≤ K := by
    simpa [dot, euclideanSq, unitVector, Matrix.mulVec, dotProduct,
      Pi.single_apply] using source_homogenized_quadratic_bounds hK S (unitVector k)
  by_cases hij : i = j
  · subst j
    rw [abs_of_nonneg (hdiag i).1]
    linarith [(hdiag i).2]
  have hsym : S.homogenized j i = S.homogenized i j :=
    congrFun (congrFun S.symmetric i) j
  have hp := (source_homogenized_quadratic_bounds hK S (unitVector i + unitVector j)).2
  have hm := (source_homogenized_quadratic_bounds hK S (unitVector i - unitVector j)).2
  simp [dot, euclideanSq, unitVector, Matrix.mulVec, dotProduct, Pi.single_apply,
    Pi.add_apply, Pi.sub_apply, add_mul, mul_add, sub_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, hij, Ne.symm hij] at hp hm
  rw [hsym] at hp hm
  apply abs_le.mpr
  constructor <;> nlinarith [(hdiag i).1, (hdiag j).1]

/-- Uniform control of the source matrix row, before choosing a law. -/
theorem source_homogenized_row_abs_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P] (S : SourceObjects P)
    (j : Fin d) : ∑ k, |S.homogenized j k| ≤ (d : ℝ) * (2 * K) := by
  calc
    _ ≤ ∑ _k : Fin d, 2 * K :=
      Finset.sum_le_sum fun k _ => source_homogenized_entry_abs_le hK S j k
    _ = _ := by simp

/-- The compact-test estimate with a constant uniform in both the law and
its variational source matrix. The full anisotropic matrix is retained in
the pairing itself. -/
theorem compact_commutator_actual_coefficient_law_uniform
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ) (B : ℝ), 0 < B →
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ B →
        (∫⁻ a, ENNReal.ofReal ((compactSourceCommutatorPairing S e ε j ψ a) ^ 2)
          ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal (C * ε ^ (d : ℝ) * B ^ 2) := by
  obtain ⟨C, hC, h⟩ := compact_commutator_actual_coefficient_law_test_bound d hd L hL m hm
  let K := AKMUpperEllipticity L
  have hK : 0 ≤ K := (zero_lt_one.trans (Correctors.one_lt_AKMUpperEllipticity hL)).le
  have hrow : 0 < 1 + (d : ℝ) * (2 * K) := by positivity
  refine ⟨C * (1 + (d : ℝ) * (2 * K)) ^ 2, mul_pos hC (sq_pos_of_pos hrow), ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ B hB hψ hnψ
  apply (hS e he ε hε hε₂ j ψ B hB hψ hnψ).trans
  apply ENNReal.ofReal_le_ofReal
  let : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  have hr := source_homogenized_row_abs_le hK S j
  have hsq : (1 + ∑ k, |S.homogenized j k|) ^ 2 ≤
      (1 + (d : ℝ) * (2 * K)) ^ 2 := by
    apply pow_le_pow_left₀
    · positivity
    · linarith
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hC.le)
      (Real.rpow_nonneg hε.le _)) (sq_nonneg B)

/-- Every coordinate derivative word through order N has the frozen
Schwartz weight, with no enlargement of N. -/
theorem schwartz_weighted_iterated_basis_le {d N k : ℕ} (hk : k ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (dirs : Fin k → Fin d) (x : Vec d) :
    (1 + euclideanNorm x) ^ N *
      ‖iteratedFDeriv ℝ k (fun y => F y) x (fun j => unitVector (dirs j))‖ ≤
      schwartzTestNorm N F := by
  apply le_csSup (schwartzTestNorm_set_bddAbove N F)
  exact ⟨⟨k, by omega⟩, dirs, x, rfl⟩

/-- The source multi-index convention is exactly evaluation of the iterated
Fréchet derivative on its ordered list of coordinate directions. -/
theorem multiIndexDerivative_eq_iteratedFDeriv {d m : ℕ}
    (β : Fin d → Fin (m + 1)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Vec d) :
    let l := (List.finRange d).flatMap fun i => List.replicate (β i).val i
    multiIndexDerivative β ψ x =
      iteratedFDeriv ℝ l.length ψ x (fun j => unitVector (l.get j)) := by
  let l := (List.finRange d).flatMap fun i => List.replicate (β i).val i
  have heq : multiIndexDerivative β ψ =
      EinsteinRelation.Sharpness.iteratedCoordinateDerivative l ψ := by
    unfold multiIndexDerivative
    change l.foldr coordinateDerivative ψ = _
    induction l with
    | nil => rfl
    | cons i l ih => exact congrArg (coordinateDerivative i) ih
  change multiIndexDerivative β ψ x = _
  rw [heq]
  have hb := S1.iteratedFDeriv_basis hψ l.length l.get x
  rw [List.ofFn_get] at hb
  exact hb.symm

/-- Real linear contractions of a Schwartz test inherit its exact weighted
source-coordinate derivative bounds. This includes real and imaginary
coordinate projections. -/
theorem schwartz_weighted_multiIndexDerivative_le {d N m : ℕ}
    (β : Fin d → Fin (m + 1)) (hβ : (∑ j, (β j).val) ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (x : Vec d) :
    (1 + euclideanNorm x) ^ N * |multiIndexDerivative β (fun y => ℓ (F y)) x| ≤
      schwartzTestNorm N F := by
  rw [multiIndexDerivative_eq_iteratedFDeriv (ψ := fun y => ℓ (F y)) β
    (ℓ.contDiff.comp (F.smooth ⊤))]
  let l := (List.finRange d).flatMap fun i => List.replicate (β i).val i
  have hl : l.length ≤ N := by simpa [l, ← List.ofFn_eq_map, Fin.sum_ofFn] using hβ
  change (1 + euclideanNorm x) ^ N *
    |iteratedFDeriv ℝ l.length (ℓ ∘ F) x (fun j => unitVector (l.get j))| ≤ _
  rw [ℓ.iteratedFDeriv_comp_left (F.smooth ⊤).contDiffAt (by simp)]
  change (1 + euclideanNorm x) ^ N *
    |ℓ (iteratedFDeriv ℝ l.length (fun y => F y) x
      (fun j => unitVector (l.get j)))| ≤ _
  apply (mul_le_mul_of_nonneg_left (show |ℓ _| ≤ ‖_‖ from ?_)
    (pow_nonneg (add_nonneg zero_le_one (Real.sqrt_nonneg _)) N)).trans
      (schwartz_weighted_iterated_basis_le hl F l.get x)
  rw [← Real.norm_eq_abs]
  exact (ℓ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hℓ)

/-- Spatial dilations carry exactly one scalar factor per source derivative. -/
theorem multiIndexDerivative_comp_const_smul {d m : ℕ}
    (β : Fin d → Fin (m + 1)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (c : ℝ) :
    multiIndexDerivative β (fun x => ψ (c • x)) =
      fun x => c ^ (∑ j, (β j).val) * multiIndexDerivative β ψ (c • x) := by
  funext x
  rw [multiIndexDerivative_eq_iteratedFDeriv (ψ := fun y => ψ (c • y)) β
    (hψ.comp (contDiff_id.const_smul c)), multiIndexDerivative_eq_iteratedFDeriv β hψ]
  rw [iteratedFDeriv_comp_const_smul c (S1.contDiff_nat_of_top hψ _)]
  simp only [smul_apply, smul_eq_mul]
  congr 2
  simp [← List.ofFn_eq_map, Fin.sum_ofFn]

/-- The exact weighted derivative bound after spatial dilation. The scaling
power is the total multi-index order, rather than the larger test-norm order. -/
theorem schwartz_weighted_rescaled_multiIndexDerivative_le {d N m : ℕ}
    (β : Fin d → Fin (m + 1)) (hβ : (∑ j, (β j).val) ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (c : ℝ) (x : Vec d) :
    (1 + euclideanNorm (c • x)) ^ N *
      |multiIndexDerivative β (fun y => ℓ (F (c • y))) x| ≤
      |c| ^ (∑ j, (β j).val) * schwartzTestNorm N F := by
  rw [multiIndexDerivative_comp_const_smul (ψ := fun y => ℓ (F y)) β
    (ℓ.contDiff.comp (F.smooth ⊤)) c,
    abs_mul, abs_pow]
  calc
    _ = |c| ^ (∑ j, (β j).val) *
        ((1 + euclideanNorm (c • x)) ^ N *
          |multiIndexDerivative β (fun y => ℓ (F y)) (c • x)|) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (schwartz_weighted_multiIndexDerivative_le β hβ F ℓ hℓ (c • x))
      (pow_nonneg (abs_nonneg c) _)

/-- Away from the origin, every rescaled source derivative has a uniform
annular decay bound. The numerator uses m derivatives and the denominator
retains all N frozen Schwartz weights. -/
theorem schwartz_rescaled_multiIndexDerivative_annulus_le {d N m : ℕ}
    (hmN : m ≤ N) (β : Fin d → Fin (m + 1)) (hβ : (∑ j, (β j).val) ≤ m)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    {c a : ℝ} (hc : 1 ≤ c) (ha : 0 ≤ a) (x : Vec d) (hx : a ≤ euclideanNorm x) :
    |multiIndexDerivative β (fun y => ℓ (F (c • y))) x| ≤
      c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N := by
  have hc₀ : 0 ≤ c := zero_le_one.trans hc
  have hd : 0 < (1 + c * a) ^ N := by positivity
  apply (le_div_iff₀ hd).2
  have hw : (1 + c * a) ^ N ≤ (1 + euclideanNorm (c • x)) ^ N := by
    rw [euclideanNorm_smul c hc₀]
    exact pow_le_pow_left₀ (show 0 ≤ 1 + c * a from by positivity)
      (show 1 + c * a ≤ 1 + c * euclideanNorm x from by
        simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hx hc₀) 1) N
  have hb := schwartz_weighted_rescaled_multiIndexDerivative_le β (hβ.trans hmN) F ℓ hℓ c x
  rw [abs_of_nonneg hc₀] at hb
  calc
    _ ≤ |multiIndexDerivative β (fun y => ℓ (F (c • y))) x| *
        (1 + euclideanNorm (c • x)) ^ N :=
      mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ ≤ c ^ (∑ j, (β j).val) * schwartzTestNorm N F := by
      simpa only [mul_comm] using hb
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc hβ)
      (clockSchwartz_norm_nonneg N F)

/-- The source derivative convention preserves smoothness. -/
theorem contDiff_multiIndexDerivative {d m : ℕ} (β : Fin d → Fin (m + 1))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (multiIndexDerivative β ψ) := by
  have hlist (l : List (Fin d)) :
      ContDiff ℝ (⊤ : ℕ∞) (l.foldr coordinateDerivative ψ) := by
    induction l with
    | nil => exact hψ
    | cons i l ih =>
      exact (ih.fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const
  exact hlist _

/-- A uniform bound on the derivatives retained by the source norm yields
an explicit finite-dimensional Sobolev bound, with its exact volume factors. -/
theorem integerSobolevTestNorm_le_of_derivative_bound {d : ℕ} (m : ℕ)
    (U : Set (Vec d)) (hU : volume U ≠ ⊤) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ β : Fin d → Fin (m + 1), (∑ j, (β j).val) ≤ m →
      ∀ x, |multiIndexDerivative β ψ x| ≤ B) :
    integerSobolevTestNorm m U ψ ≤
      (∑ β : Fin d → Fin (m + 1),
        if (∑ j, (β j).val) ≤ m then
          (volume U).toReal ^ ((((∑ j, (β j).val : ℕ) : ℝ) - m) / d)
        else 0) * B := by
  unfold integerSobolevTestNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro β _
  split_ifs with hβ
  · exact mul_le_mul_of_nonneg_left
      (Correctors.scalarRms_le_of_ae_abs_le volume U hU hB
        (contDiff_multiIndexDerivative β hψ).continuous.measurable.aestronglyMeasurable
        (ae_of_all _ (hb β hβ))) (Real.rpow_nonneg ENNReal.toReal_nonneg _)
  · simp


/-- Bounds on coordinate evaluations control the operator norm on the existing
sup-norm carrier, with its explicit dimension factor. -/
theorem multilinear_norm_le_of_basis_bound {d k : ℕ}
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ dirs : Fin k → Fin d, |T (fun j => unitVector (dirs j))| ≤ B) :
    ‖T‖ ≤ (d : ℝ) ^ k * B := by
  classical
  apply T.opNorm_le_bound (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hB)
  intro v
  rw [Real.norm_eq_abs, S1.multilinear_expand]
  calc
    _ ≤ ∑ dirs : Fin k → Fin d,
        |(∏ j, v j (dirs j)) * T (fun j => unitVector (dirs j))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _dirs : Fin k → Fin d, (∏ j, ‖v j‖) * B := by
      apply Finset.sum_le_sum
      intro dirs _
      rw [abs_mul, Finset.abs_prod]
      apply mul_le_mul _ (hb dirs) (abs_nonneg _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun j _ => by
        rw [← Real.norm_eq_abs]
        exact norm_le_pi_norm (v j) (dirs j)
    _ = _ := by simp [mul_assoc, mul_comm, mul_left_comm]

/-- The exact weighted Schwartz bound also controls the scalar operator norm.
The dimension factor comes only from changing coordinate evaluations to an
operator norm on the inherited carrier. -/
theorem schwartz_iteratedFDeriv_le {d N k : ℕ} (hk : k ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    (x : Vec d) :
    ‖iteratedFDeriv ℝ k (fun y => ℓ (F y)) x‖ ≤
      (d : ℝ) ^ k * schwartzTestNorm N F / (1 + euclideanNorm x) ^ N := by
  have hd : 0 < (1 + euclideanNorm x) ^ N := by
    exact pow_pos (add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)) _
  have hb := multilinear_norm_le_of_basis_bound
    (iteratedFDeriv ℝ k (fun y => ℓ (F y)) x)
    (div_nonneg (clockSchwartz_norm_nonneg N F) hd.le) (fun dirs => ?_)
  · simpa only [mul_div_assoc] using hb
  change |iteratedFDeriv ℝ k (ℓ ∘ F) x (fun j => unitVector (dirs j))| ≤ _
  rw [ℓ.iteratedFDeriv_comp_left (F.smooth ⊤).contDiffAt (by simp)]
  apply (le_div_iff₀ hd).2
  have hc : |ℓ (iteratedFDeriv ℝ k (fun y => F y) x
      (fun j => unitVector (dirs j)))| ≤
      ‖iteratedFDeriv ℝ k (fun y => F y) x (fun j => unitVector (dirs j))‖ := by
    rw [← Real.norm_eq_abs]
    exact (ℓ.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) hℓ)
  exact (mul_le_mul_of_nonneg_right hc hd.le).trans
    (by simpa only [mul_comm] using schwartz_weighted_iterated_basis_le hk F dirs x)

/-- On an annulus, derivatives of every order up to m of a dilated real test
have a common bound with all N Schwartz weights. -/
theorem schwartz_rescaled_iteratedFDeriv_annulus_le {d N m : ℕ} (hmN : m ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    {c a : ℝ} (hc : 1 ≤ c) (ha : 0 ≤ a) {k : ℕ} (hk : k ≤ m)
    (x : Vec d) (hx : a ≤ euclideanNorm x) :
    ‖iteratedFDeriv ℝ k (fun y => ℓ (F (c • y))) x‖ ≤
      ((d : ℝ) + 1) ^ m * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N := by
  have hc₀ : 0 ≤ c := zero_le_one.trans hc
  have hS := clockSchwartz_norm_nonneg N F
  have hw₀ : 0 ≤ 1 + euclideanNorm (c • x) :=
    add_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hd : 0 < (1 + c * a) ^ N := by positivity
  have hw : (1 + c * a) ^ N ≤ (1 + euclideanNorm (c • x)) ^ N := by
    rw [euclideanNorm_smul c hc₀]
    exact pow_le_pow_left₀ (show 0 ≤ 1 + c * a from by positivity)
      (show 1 + c * a ≤ 1 + c * euclideanNorm x from by
        simpa only [add_comm] using add_le_add_left (mul_le_mul_of_nonneg_left hx hc₀) 1) N
  rw [iteratedFDeriv_comp_const_smul (f := fun y => ℓ (F y)) c
    (S1.contDiff_nat_of_top (ℓ.contDiff.comp (F.smooth ⊤)) k)]
  rw [norm_smul, Real.norm_eq_abs, abs_pow, abs_of_nonneg hc₀]
  calc
    _ ≤ c ^ k * ((d : ℝ) ^ k * schwartzTestNorm N F /
        (1 + euclideanNorm (c • x)) ^ N) :=
      mul_le_mul_of_nonneg_left (schwartz_iteratedFDeriv_le (hk.trans hmN) F ℓ hℓ _) (by positivity)
    _ ≤ c ^ m * (((d : ℝ) + 1) ^ m * schwartzTestNorm N F /
        (1 + c * a) ^ N) := by
      apply mul_le_mul (pow_le_pow_right₀ hc hk) _ (by positivity) (by positivity)
      apply div_le_div₀ (by positivity) _ hd hw
      apply mul_le_mul_of_nonneg_right _ (clockSchwartz_norm_nonneg N F)
      exact (pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) k).trans
        (pow_le_pow_right₀ (show 1 ≤ (d : ℝ) + 1 from by
          have := Nat.cast_nonneg (α := ℝ) d
          linarith) hk)
    _ = _ := by ring

/-- Cutoff products need bounds on the other factor only on the cutoff's
closed support. All derivatives vanish outside that support. -/
theorem norm_iteratedFDeriv_cutoff_mul_le {d m n : ℕ} {χ g : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hχA : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ A)
    (hgB : ∀ k ≤ m, ∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ k g x‖ ≤ B)
    (hn : n ≤ m) (x : Vec d) :
    ‖iteratedFDeriv ℝ n (fun y => χ y * g y) x‖ ≤
      (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) * A * B := by
  by_cases hx : x ∈ tsupport χ
  · apply (norm_iteratedFDeriv_mul_le hχ hg x (by simp)).trans
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A * B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (hχA i (hi'.trans hn) x) (Nat.cast_nonneg _))
          (hgB (n - i) ((Nat.sub_le _ _).trans hn) x hx)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hA)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
  · have hz : iteratedFDeriv ℝ n (fun y => χ y * g y) x = 0 := by
      by_contra hne
      exact hx (tsupport_mul_subset_left (support_iteratedFDeriv_subset n hne))
    rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hA) hB


/-- Source coordinate derivatives are bounded by the corresponding operator
norm, on the original coordinate carrier. -/
theorem multiIndexDerivative_abs_le_iteratedFDeriv_norm {d m : ℕ}
    (β : Fin d → Fin (m + 1)) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Vec d) :
    |multiIndexDerivative β ψ x| ≤
      ‖iteratedFDeriv ℝ (∑ j, (β j).val) ψ x‖ := by
  rw [multiIndexDerivative_eq_iteratedFDeriv β hψ]
  let l := (List.finRange d).flatMap fun i => List.replicate (β i).val i
  have hl : l.length = ∑ j, (β j).val := by
    simp [l, ← List.ofFn_eq_map, Fin.sum_ofFn]
  change |iteratedFDeriv ℝ l.length ψ x (fun j => unitVector (l.get j))| ≤ _
  have hb := (iteratedFDeriv ℝ l.length ψ x).le_opNorm (fun j => unitVector (l.get j))
  calc
    _ ≤ ‖iteratedFDeriv ℝ l.length ψ x‖ := by
      simpa only [Real.norm_eq_abs, unitVector, Pi.norm_single, norm_one,
        Finset.prod_const_one, mul_one] using hb
    _ = _ := congrArg (fun k => ‖iteratedFDeriv ℝ k ψ x‖) hl

/-- A smooth cutoff supported away from the origin preserves the full
Schwartz decay under dilation, for every source derivative retained at m. -/
theorem schwartz_cutoff_multiIndexDerivative_annulus_le {d N m : ℕ}
    (hmN : m ≤ N) {χ : Vec d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    {A a : ℝ} (hA : 0 ≤ A) (ha : 0 ≤ a)
    (hχA : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ A)
    (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1)
    {c : ℝ} (hc : 1 ≤ c) (β : Fin d → Fin (m + 1))
    (hβ : (∑ j, (β j).val) ≤ m) (x : Vec d) :
    |multiIndexDerivative β (fun y => χ y * ℓ (F (c • y))) x| ≤
      2 ^ m * A * (((d : ℝ) + 1) ^ m * c ^ m * schwartzTestNorm N F /
        (1 + c * a) ^ N) := by
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => ℓ (F (c • y))) :=
    (ℓ.contDiff.comp (F.smooth ⊤)).comp (contDiff_id.const_smul c)
  have hS := clockSchwartz_norm_nonneg N F
  have hB : 0 ≤ ((d : ℝ) + 1) ^ m * c ^ m * schwartzTestNorm N F /
      (1 + c * a) ^ N := by positivity
  apply (multiIndexDerivative_abs_le_iteratedFDeriv_norm β (hχ.mul hg) x).trans
  have hb := norm_iteratedFDeriv_cutoff_mul_le hχ hg hA hB hχA
    (fun k hk y hy => schwartz_rescaled_iteratedFDeriv_annulus_le
      hmN F ℓ hℓ hc ha hk y (hχa y hy)) hβ x
  have hs : (∑ i ∈ Finset.range ((∑ j, (β j).val) + 1),
      (((∑ j, (β j).val).choose i) : ℝ)) = 2 ^ (∑ j, (β j).val) := by
    exact_mod_cast Nat.sum_range_choose (∑ j, (β j).val)
  rw [hs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hβ) hA) hB)


/-- A fixed smooth compact cutoff gives one source Sobolev constant before
all Schwartz tests, dilation factors, and decay orders N at least m. The
annulus may start at zero, which also covers the innermost cutoff. -/
theorem exists_schwartz_cutoff_integerSobolevTestNorm_bound {d : ℕ} (m : ℕ)
    (U : Set (Vec d)) (hU : volume U ≠ ⊤) {χ : Vec d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hcχ : HasCompactSupport χ)
    {a : ℝ} (ha : 0 ≤ a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C > 0, ∀ N : ℕ, m ≤ N →
      ∀ (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
      ∀ c : ℝ, 1 ≤ c →
        integerSobolevTestNorm m U (fun y => χ y * ℓ (F (c • y))) ≤
          C * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N := by
  classical
  obtain ⟨A, hA, hχA⟩ := hcχ.exists_bound_iteratedFDeriv hχ m
  let V : ℝ := ∑ β : Fin d → Fin (m + 1),
    if (∑ j, (β j).val) ≤ m then
      (volume U).toReal ^ ((((∑ j, (β j).val : ℕ) : ℝ) - m) / d)
    else 0
  have hV : 0 ≤ V := by
    apply Finset.sum_nonneg
    intro β _
    split_ifs
    · exact Real.rpow_nonneg ENNReal.toReal_nonneg _
    · exact le_rfl
  let C : ℝ := V * (2 ^ m * A * ((d : ℝ) + 1) ^ m) + 1
  have hC₀ : 0 ≤ V * (2 ^ m * A * ((d : ℝ) + 1) ^ m) := by positivity
  refine ⟨C, by dsimp [C]; linarith, fun N hmN F ℓ hℓ c hc => ?_⟩
  have hS := clockSchwartz_norm_nonneg N F
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y => ℓ (F (c • y))) :=
    (ℓ.contDiff.comp (F.smooth ⊤)).comp (contDiff_id.const_smul c)
  have hB : 0 ≤ 2 ^ m * A * (((d : ℝ) + 1) ^ m * c ^ m * schwartzTestNorm N F /
      (1 + c * a) ^ N) := by positivity
  have hb := integerSobolevTestNorm_le_of_derivative_bound m U hU (hχ.mul hg) hB
    (fun β hβ x => schwartz_cutoff_multiIndexDerivative_annulus_le
      hmN hχ hA ha hχA hχa F ℓ hℓ hc β hβ x)
  change _ ≤ V * (2 ^ m * A * (((d : ℝ) + 1) ^ m * c ^ m * schwartzTestNorm N F /
    (1 + c * a) ^ N)) at hb
  apply hb.trans
  calc
    _ = (V * (2 ^ m * A * ((d : ℝ) + 1) ^ m)) *
        (c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N) := by ring
    _ ≤ C * (c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N) :=
      mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (by positivity)
    _ = _ := by ring


/-- Cutting off a scalar component of a dilated complex Schwartz test gives
an actual compact source test on the cutoff's original domain. -/
theorem isSpatialTest_cutoff_schwartz {d : ℕ} {U : Set (Vec d)}
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ) (c : ℝ) :
    IsSpatialTest U (fun y => χ y * ℓ (F (c • y))) := by
  exact ⟨hχ.1.mul ((ℓ.contDiff.comp (F.smooth ⊤)).comp (contDiff_id.const_smul c)),
    hχ.2.1.mul_right, tsupport_mul_subset_left.trans hχ.2.2⟩

/-- A central cutoff has a buffer inside the literal Euclidean unit ball,
even though its smooth bump is built on the inherited coordinate norm. -/
theorem exists_unitBall_cutoff (d : ℕ) :
    ∃ (η : Vec d → ℝ) (a : ℝ), 0 < a ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      (∀ x ∈ tsupport η, euclideanNorm x ≤ 1 / 2) ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ 2 * a → η x = 1) := by
  let D : ℝ := (d : ℝ) + 1
  have hD : 0 < D := by dsimp [D]; positivity
  let r : ℝ := (4 * D)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  let b : ContDiffBump (0 : Vec d) := ⟨r, 2 * r, hr, by linarith⟩
  refine ⟨b, r / 2, by positivity, b.contDiff, b.hasCompactSupport, ?_,
    fun _ => ⟨b.nonneg, b.le_one⟩, ?_⟩
  · intro x hx
    rw [b.tsupport_eq] at hx
    have hx' : ‖x‖ ≤ 2 * r := mem_closedBall_zero_iff.mp hx
    have h := (euclideanNorm_le_dimension_mul_norm x).trans
      (mul_le_mul_of_nonneg_left hx' hD.le)
    have hh : D * (2 * r) = 1 / 2 := by dsimp [r]; field_simp; ring
    change euclideanNorm x ≤ D * (2 * r) at h
    rwa [hh] at h
  · intro x hx
    apply b.one_of_mem_closedBall
    apply mem_closedBall_zero_iff.mpr
    exact (S1.norm_le_euclideanNorm x).trans (by linarith)

/-- A central cutoff and its fixed dyadic annulus are literal smooth compact
source tests on the Euclidean unit ball of the inherited coordinate carrier. -/
theorem exists_dyadic_cutoff_pair (d : ℕ) :
    ∃ (η χ : Vec d → ℝ) (a : ℝ), 0 < a ∧
      IsSpatialTest (originBall d 1) η ∧ IsSpatialTest (originBall d 1) χ ∧
      (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x, euclideanNorm x ≤ 2 * a → η x = 1) ∧
      (∀ x, χ x = η x - η ((2 : ℝ) • x)) ∧
      (∀ x ∈ tsupport χ, a ≤ euclideanNorm x) := by
  obtain ⟨η, a, ha, hη, hcη, hηb, hη01, hone⟩ := exists_unitBall_cutoff d
  let χ : Vec d → ℝ := fun x => η x - η ((2 : ℝ) • x)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hη.sub (hη.comp (contDiff_id.const_smul (2 : ℝ)))
  have hcχ : HasCompactSupport χ := hcη.sub (hcη.comp_smul (by norm_num : (2 : ℝ) ≠ 0))
  have hec : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  have hχb : tsupport χ ⊆ {x : Vec d | euclideanNorm x ≤ 1 / 2} := by
    apply closure_minimal _ (isClosed_le hec continuous_const)
    intro x hx
    change euclideanNorm x ≤ 1 / 2
    by_cases hy : η x = 0
    · have hy' : η ((2 : ℝ) • x) ≠ 0 := by simpa [χ, hy] using hx
      have hb := hηb _ (subset_closure (show (2 : ℝ) • x ∈ Function.support η from hy'))
      rw [euclideanNorm_smul 2 (by norm_num)] at hb
      have hn := Real.sqrt_nonneg (euclideanSq x)
      change 0 ≤ euclideanNorm x at hn
      linarith
    · exact hηb x (subset_closure hy)
  have hχa : tsupport χ ⊆ {x : Vec d | a ≤ euclideanNorm x} := by
    apply closure_minimal _ (isClosed_le continuous_const hec)
    intro x hx
    by_contra hn
    have hn' : euclideanNorm x < a := lt_of_not_ge hn
    have hz : η x = 1 := hone x (by linarith)
    have hz₂ : η ((2 : ℝ) • x) = 1 := hone _ (by
      rw [euclideanNorm_smul 2 (by norm_num)]
      linarith)
    exact hx (by dsimp [χ]; rw [hz, hz₂, sub_self])
  refine ⟨η, χ, a, ha, ⟨hη, hcη, ?_⟩, ⟨hχ, hcχ, ?_⟩,
    hη01, hone, fun _ => rfl, fun x hx => hχa hx⟩
  · intro x hx
    exact lt_of_le_of_lt (hηb x hx) (by norm_num)
  · intro x hx
    exact lt_of_le_of_lt (show euclideanNorm x ≤ 1 / 2 from hχb hx) (by norm_num)

/-- The annular pieces telescope exactly before any passage to an infinite
sum or any interchange with a spatial or probability integral. -/
theorem dyadic_cutoff_partial_sum {d : ℕ} (η χ : Vec d → ℝ)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x)) (n : ℕ) (x : Vec d) :
    η x + ∑ k ∈ Finset.range n, χ (((2 : ℝ) ^ (k + 1))⁻¹ • x) =
      η (((2 : ℝ) ^ n)⁻¹ • x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih, hχ]
    have hs : (2 : ℝ) * ((2 : ℝ) ^ (n + 1))⁻¹ = ((2 : ℝ) ^ n)⁻¹ := by
      rw [pow_succ, mul_inv_rev]
      ring
    rw [smul_smul, hs]
    ring


/-- The exact finite telescopes converge pointwise to the constant partition
of unity. No spatial or stochastic integral is interchanged here. -/
theorem tendsto_dyadic_cutoff_partial_sum {d : ℕ} (η χ : Vec d → ℝ)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x))
    (hη : Continuous η) (hη₀ : η 0 = 1) (x : Vec d) :
    Filter.Tendsto
      (fun n : ℕ => η x + ∑ k ∈ Finset.range n, χ (((2 : ℝ) ^ (k + 1))⁻¹ • x))
      Filter.atTop (nhds 1) := by
  have hp : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) Filter.atTop (nhds 0) := by
    simpa only [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1))
  have hx : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ • x)
      Filter.atTop (nhds 0) := by
    simpa only [zero_smul] using hp.smul (tendsto_const_nhds (x := x))
  have hlim : Filter.Tendsto (fun n : ℕ => η (((2 : ℝ) ^ n)⁻¹ • x))
      Filter.atTop (nhds (η 0)) := (hη.tendsto 0).comp hx
  simpa only [dyadic_cutoff_partial_sum η χ hχ, hη₀] using hlim

/-- One spare Schwartz weight dominates any retained polynomial scale by
an inverse scale, with the annulus radius kept explicit. -/
theorem scale_polynomial_decay_le_inv {p N : ℕ} (hpN : p + 1 ≤ N)
    {a c : ℝ} (ha : 0 < a) (hc : 1 ≤ c) :
    c ^ p / (1 + c * a) ^ N ≤ (a ^ N)⁻¹ / c := by
  have hc₀ : 0 < c := zero_lt_one.trans_le hc
  have hd : 0 < (1 + c * a) ^ N := by positivity
  have he : (a ^ N)⁻¹ / c = 1 / (a ^ N * c) := by ring
  rw [he]
  apply (div_le_div_iff₀ hd (mul_pos (pow_pos ha _) hc₀)).2
  rw [one_mul]
  calc
    c ^ p * (a ^ N * c) = c ^ (p + 1) * a ^ N := by rw [pow_succ]; ring
    _ ≤ c ^ N * a ^ N := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hc hpN) (pow_nonneg ha.le _)
    _ = (c * a) ^ N := (mul_pow c a N).symm
    _ ≤ (1 + c * a) ^ N := pow_le_pow_left₀ (mul_nonneg hc₀.le ha.le) (by linarith) N

/-- The annular Schwartz bounds are summable on every dyadic sequence
starting at a scale at least one. No increase of N is needed. -/
theorem summable_dyadic_schwartz_decay {p N : ℕ} (hpN : p + 1 ≤ N)
    {a L : ℝ} (ha : 0 < a) (hL : 1 ≤ L) :
    Summable (fun n : ℕ => (L * (2 : ℝ) ^ n) ^ p /
      (1 + (L * (2 : ℝ) ^ n) * a) ^ N) := by
  have hsum := summable_geometric_two.mul_left ((a ^ N)⁻¹)
  apply hsum.of_nonneg_of_le
  · intro n
    have hL₀ : 0 ≤ L := zero_le_one.trans hL
    positivity
  · intro n
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hscale : (2 : ℝ) ^ n ≤ L * (2 : ℝ) ^ n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (pow_nonneg (by norm_num) n)
    calc
      _ ≤ (a ^ N)⁻¹ / (L * (2 : ℝ) ^ n) :=
        scale_polynomial_decay_le_inv hpN ha (hp.trans hscale)
      _ ≤ (a ^ N)⁻¹ / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hscale
      _ = (a ^ N)⁻¹ * ((1 : ℝ) / 2) ^ n := by rw [one_div, inv_pow, div_eq_mul_inv]


/-- Expanding cutoffs converge in an actual Bochner spatial integral. The
integrable dominating function is the norm of the uncut integrand. -/
theorem tendsto_integral_expanding_cutoff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η : Vec d → ℝ} (hη : Continuous η) (hη₀ : η 0 = 1)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1) {g : Vec d → E}
    (hg : Integrable g) (L : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => ∫ x, η (((2 : ℝ) ^ n)⁻¹ • (L⁻¹ • x)) • g x)
      Filter.atTop (nhds (∫ x, g x)) := by
  have hp : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹)
      Filter.atTop (nhds 0) := by
    simpa only [one_div, inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 : ℝ) / 2 < 1))
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
  · intro n
    exact ((hη.comp ((continuous_id.const_smul L⁻¹).const_smul
      (((2 : ℝ) ^ n)⁻¹))).aestronglyMeasurable).smul hg.aestronglyMeasurable
  · exact hg.norm
  · intro n
    exact ae_of_all _ fun x => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη01 _).1]
      exact mul_le_of_le_one_left (norm_nonneg _) (hη01 _).2
  · exact ae_of_all _ fun x => by
      have hx : Filter.Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹ • (L⁻¹ • x))
          Filter.atTop (nhds 0) := by
        simpa only [zero_smul] using hp.smul (tendsto_const_nhds (x := L⁻¹ • x))
      have hv : Filter.Tendsto (fun n : ℕ => η (((2 : ℝ) ^ n)⁻¹ • (L⁻¹ • x)))
          Filter.atTop (nhds (η 0)) := (hη.tendsto 0).comp hx
      simpa only [hη₀, one_smul] using hv.smul (tendsto_const_nhds (x := g x))

/-- Every finite dyadic decomposition commutes with the Bochner integral;
all component integrability is derived from the uncut integrand. -/
theorem integral_dyadic_cutoff_partial_sum {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η χ : Vec d → ℝ} (hη : Continuous η)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x))
    {g : Vec d → E} (hg : Integrable g) (L : ℝ) (n : ℕ) :
    (∫ x, η (L⁻¹ • x) • g x) +
      ∑ k ∈ Finset.range n, ∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x =
      ∫ x, η (((2 : ℝ) ^ n)⁻¹ • (L⁻¹ • x)) • g x := by
  have hi (c : ℝ) : Integrable (fun x => η (c • (L⁻¹ • x)) • g x) := by
    apply hg.bdd_smul 1
    · exact (hη.comp ((continuous_id.const_smul L⁻¹).const_smul c)).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hη01 _).1]
        exact (hη01 _).2
  have hj (c : ℝ) : Integrable (fun x => χ (c • (L⁻¹ • x)) • g x) := by
    have heq : (fun x => χ (c • (L⁻¹ • x)) • g x) =
        (fun x => η (c • (L⁻¹ • x)) • g x - η ((2 * c) • (L⁻¹ • x)) • g x) := by
      funext x
      simp only [hχ, sub_smul, smul_smul, mul_assoc]
    rw [heq]
    exact (hi c).sub (hi (2 * c))
  have hi₀ : Integrable (fun x => η (L⁻¹ • x) • g x) := by
    simpa only [one_smul] using hi 1
  rw [← integral_finsetSum _ (fun k _ => hj (((2 : ℝ) ^ (k + 1))⁻¹)),
    ← integral_add hi₀ (integrable_finsetSum _ (fun k _ => hj (((2 : ℝ) ^ (k + 1))⁻¹)))]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    change η (L⁻¹ • x) • g x +
      (∑ k ∈ Finset.range n, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x) = _
    rw [← Finset.sum_smul, ← add_smul, dyadic_cutoff_partial_sum η χ hχ]

/-- The annular Bochner integrals sum to the uncut integral minus its
central piece. Norm summability gives the unconditional series required
by `HasSum`; expanding cutoffs identify its exact value. -/
theorem hasSum_integral_dyadic_cutoff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η χ : Vec d → ℝ} (hη : Continuous η) (hη₀ : η 0 = 1)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x))
    {g : Vec d → E} (hg : Integrable g) (L : ℝ)
    (hs : Summable (fun k : ℕ =>
      ‖∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x‖)) :
    HasSum (fun k : ℕ =>
      ∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x)
      ((∫ x, g x) - ∫ x, η (L⁻¹ • x) • g x) := by
  apply (hasSum_iff_tendsto_nat_of_summable_norm hs).2
  have ht := (tendsto_integral_expanding_cutoff hη hη₀ hη01 hg L).sub_const
    (∫ x, η (L⁻¹ • x) • g x)
  convert ht using 1
  funext n
  rw [← integral_dyadic_cutoff_partial_sum hη hη01 hχ hg L n]
  exact (add_sub_cancel_left _ _).symm


/-- Summable norm bounds for the compact pieces control the uncut Bochner
integral, using an actual integral limit rather than a formal partition. -/
theorem norm_integral_le_of_dyadic_cutoff {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {η χ : Vec d → ℝ} (hη : Continuous η) (hη₀ : η 0 = 1)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x))
    {g : Vec d → E} (hg : Integrable g) (L : ℝ)
    {B : ℝ} {b : ℕ → ℝ} (hb : Summable b)
    (hB : ‖∫ x, η (L⁻¹ • x) • g x‖ ≤ B)
    (hpieces : ∀ k, ‖∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x‖ ≤ b k) :
    ‖∫ x, g x‖ ≤ B + ∑' k, b k := by
  apply le_of_tendsto (tendsto_integral_expanding_cutoff hη hη₀ hη01 hg L).norm
  exact Filter.Eventually.of_forall fun n => by
    rw [← integral_dyadic_cutoff_partial_sum hη hη01 hχ hg L n]
    calc
      _ ≤ ‖∫ x, η (L⁻¹ • x) • g x‖ +
          ∑ k ∈ Finset.range n, ‖∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • (L⁻¹ • x)) • g x‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
      _ ≤ B + ∑ k ∈ Finset.range n, b k :=
        add_le_add hB (Finset.sum_le_sum fun k _ => hpieces k)
      _ ≤ B + ∑' k, b k := add_le_add le_rfl
        (hb.sum_le_tsum _ (fun k _ => (norm_nonneg _).trans (hpieces k)))


/-- Real cutoffs of the literal normalized coordinate pairing are actual
Bochner integrals of the same normalized L² translation kernel. -/
theorem scaledComplexClockPairing_cutoff_eq_integral {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (u : Lp ℂ 2 (reducedLaw Q))
    (w : Vec d → ℝ) (f : Vec d → ℂ) :
    scaledComplexClockPairing Q R u (fun y => (w y : ℂ) * f y) =
      ∫ x, w (R⁻¹ • x) •
        (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          (f (R⁻¹ • x) • complexTranslation (reducedLaw Q)
            (reducedLaw_stationary Q) x u)) := by
  unfold scaledComplexClockPairing complexClockSpatialPairing
  rw [← integral_smul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    dsimp only
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := Lp ℂ 2 (reducedLaw Q))]
    simp only [smul_smul, mul_comm, mul_left_comm]
    rfl

/-- Compact central and annular bounds transfer to the literal scaled
complex coordinate pairing. Spatial integrability follows internally from
Schwartz decay and the stationary translation isometry. -/
theorem norm_scaledComplexClockPairing_le_of_dyadic_cutoff {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (u : Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (a : JointObservationIndex d)
    {η χ : Vec d → ℝ} (hη : Continuous η) (hη₀ : η 0 = 1)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x)) (c : ℝ)
    {B : ℝ} {b : ℕ → ℝ} (hb : Summable b)
    (hB : ‖scaledComplexClockPairing Q R u
      (fun y => (η (c⁻¹ • y) : ℂ) * F y a)‖ ≤ B)
    (hpieces : ∀ k, ‖scaledComplexClockPairing Q R u
      (fun y => (χ (((2 : ℝ) ^ (k + 1))⁻¹ • (c⁻¹ • y)) : ℂ) * F y a)‖ ≤ b k) :
    ‖scaledComplexClockPairing Q R u (fun y => F y a)‖ ≤ B + ∑' k, b k := by
  let := reducedLaw_probability Q
  let g : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x =>
    (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
      (F (R⁻¹ • x) a • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x u))
  have hc := (PiLp.continuous_apply 2 _ a).comp F.continuous
  have hf : Integrable (fun x => F x a) := F.integrable.mono
    hc.aestronglyMeasurable (ae_of_all _ fun x => PiLp.norm_apply_le (F x) a)
  have hg : Integrable g := Integrable.smul
    (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ)) (integrable_kernel_complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) _
      (hf.comp_smul (inv_ne_zero hR.ne')) (hc.comp (continuous_id.const_smul R⁻¹)) u)
  have heq : (∫ x, g x) = scaledComplexClockPairing Q R u (fun y => F y a) := by
    dsimp only [g]
    rw [integral_smul]
    rfl
  have hs (x : Vec d) : (c * R)⁻¹ • x = c⁻¹ • (R⁻¹ • x) := by
    simp only [mul_inv_rev, smul_smul, mul_comm]
  rw [← heq]
  apply norm_integral_le_of_dyadic_cutoff hη hη₀ hη01 hχ hg (c * R) hb
  · rw [scaledComplexClockPairing_cutoff_eq_integral] at hB
    simpa only [hs] using hB
  · intro k
    have hk := hpieces k
    rw [scaledComplexClockPairing_cutoff_eq_integral] at hk
    simpa only [hs] using hk


/-- The literal scaled coordinate pairing is the central piece plus the
actual L² sum of its annular pieces. The spatial Bochner integrability is
proved from Schwartz decay and translation isometry, with no spatial
integrability hypothesis on the caller. -/
theorem hasSum_scaledComplexClockPairing_dyadic_cutoff {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (u : Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (a : JointObservationIndex d)
    {η χ : Vec d → ℝ} (hη : Continuous η) (hη₀ : η 0 = 1)
    (hη01 : ∀ x, 0 ≤ η x ∧ η x ≤ 1)
    (hχ : ∀ x, χ x = η x - η ((2 : ℝ) • x)) (c : ℝ)
    (hs : Summable (fun k : ℕ => ‖scaledComplexClockPairing Q R u
      (fun y => (χ (((2 : ℝ) ^ (k + 1))⁻¹ • (c⁻¹ • y)) : ℂ) * F y a)‖)) :
    HasSum (fun k : ℕ => scaledComplexClockPairing Q R u
      (fun y => (χ (((2 : ℝ) ^ (k + 1))⁻¹ • (c⁻¹ • y)) : ℂ) * F y a))
      (scaledComplexClockPairing Q R u (fun y => F y a) -
        scaledComplexClockPairing Q R u (fun y => (η (c⁻¹ • y) : ℂ) * F y a)) := by
  let := reducedLaw_probability Q
  let g : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x =>
    (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
      (F (R⁻¹ • x) a • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x u))
  have hc := (PiLp.continuous_apply 2 _ a).comp F.continuous
  have hf : Integrable (fun x => F x a) := F.integrable.mono
    hc.aestronglyMeasurable (ae_of_all _ fun x => PiLp.norm_apply_le (F x) a)
  have hg : Integrable g := Integrable.smul
    (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ)) (integrable_kernel_complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) _
      (hf.comp_smul (inv_ne_zero hR.ne')) (hc.comp (continuous_id.const_smul R⁻¹)) u)
  have heq : (∫ x, g x) = scaledComplexClockPairing Q R u (fun y => F y a) := by
    dsimp only [g]
    rw [integral_smul]
    rfl
  have hscale (x : Vec d) : (c * R)⁻¹ • x = c⁻¹ • (R⁻¹ • x) := by
    simp only [mul_inv_rev, smul_smul, mul_comm]
  have hcentral : (∫ x, η ((c * R)⁻¹ • x) • g x) =
      scaledComplexClockPairing Q R u (fun y => (η (c⁻¹ • y) : ℂ) * F y a) := by
    rw [scaledComplexClockPairing_cutoff_eq_integral]
    simp only [hscale, g]
  have hpiece (k : ℕ) :
      (∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • ((c * R)⁻¹ • x)) • g x) =
      scaledComplexClockPairing Q R u
        (fun y => (χ (((2 : ℝ) ^ (k + 1))⁻¹ • (c⁻¹ • y)) : ℂ) * F y a) := by
    rw [scaledComplexClockPairing_cutoff_eq_integral]
    simp only [hscale, g]
  have hs' : Summable (fun k : ℕ =>
      ‖∫ x, χ (((2 : ℝ) ^ (k + 1))⁻¹ • ((c * R)⁻¹ • x)) • g x‖) := by
    simpa only [hpiece] using hs
  have ht := hasSum_integral_dyadic_cutoff hη hη₀ hη01 hχ hg (c * R) hs'
  simpa only [hpiece, heq, hcentral] using ht


/-- The full dyadic Schwartz sum has an explicit bound independent of the
starting scale, so the eventual constant can precede the test and scale. -/
theorem tsum_dyadic_schwartz_decay_le {p N : ℕ} (hpN : p + 1 ≤ N)
    {a L : ℝ} (ha : 0 < a) (hL : 1 ≤ L) :
    (∑' n : ℕ, (L * (2 : ℝ) ^ n) ^ p /
      (1 + (L * (2 : ℝ) ^ n) * a) ^ N) ≤ 2 * (a ^ N)⁻¹ := by
  have hmajorant (n : ℕ) : (L * (2 : ℝ) ^ n) ^ p /
      (1 + (L * (2 : ℝ) ^ n) * a) ^ N ≤ (a ^ N)⁻¹ * ((1 : ℝ) / 2) ^ n := by
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hscale : (2 : ℝ) ^ n ≤ L * (2 : ℝ) ^ n := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hL (pow_nonneg (by norm_num) n)
    calc
      _ ≤ (a ^ N)⁻¹ / (L * (2 : ℝ) ^ n) :=
        scale_polynomial_decay_le_inv hpN ha (hp.trans hscale)
      _ ≤ (a ^ N)⁻¹ / (2 : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hscale
      _ = _ := by rw [one_div, inv_pow, div_eq_mul_inv]
  calc
    _ ≤ ∑' n : ℕ, (a ^ N)⁻¹ * ((1 : ℝ) / 2) ^ n :=
      (summable_dyadic_schwartz_decay hpN ha hL).tsum_le_tsum hmajorant
        (summable_geometric_two.mul_left ((a ^ N)⁻¹))
    _ = 2 * (a ^ N)⁻¹ := by rw [tsum_mul_left, tsum_geometric_two]; ring


/-- A finite scalar second-moment bound controls the norm of the actual
L² representative, independently of the membership proof used to construct it. -/
theorem norm_toLp_sq_le_of_lintegral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 μ) {T : ℝ} (hT : 0 ≤ T)
    (hb : (∫⁻ ω, ENNReal.ofReal (f ω ^ 2) ∂μ) ≤ ENNReal.ofReal T) :
    ‖hf.toLp f‖ ^ 2 ≤ T := by
  have hi : (∫ ω, f ω ^ 2 ∂μ) ≤ T := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun _ => sq_nonneg _) hf.integrable_sq.aestronglyMeasurable]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb).trans_eq
      (ENNReal.toReal_ofReal hT)
  rw [← S1.l2Size_eq_norm_toLp hf, S1.l2Size]
  simpa only [Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)] using hi

/-- The same AKM-selected source satisfies both genuine L² membership and
its quantitative norm bound. No second independent source selection is made. -/
theorem compact_commutator_actual_coefficient_law_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ) (B : ℝ), 0 < B →
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ B →
        ∃ hf : MemLp (compactSourceCommutatorPairing S e ε j ψ) 2
            (actualCoefficientLaw Q),
          ‖hf.toLp (compactSourceCommutatorPairing S e ε j ψ)‖ ^ 2 ≤
            C * ε ^ (d : ℝ) * B ^ 2 := by
  obtain ⟨C, hC, h⟩ := compact_commutator_actual_coefficient_law_uniform d hd L hL m hm
  refine ⟨C, hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ B hB hψ hnψ
  have hb := hS e he ε hε hε₂ j ψ B hB hψ hnψ
  have hmeas := measurable_compactSourceCommutatorPairing S e hε j hψ.1.continuous.measurable
  have hf : MemLp (compactSourceCommutatorPairing S e ε j ψ) 2
      (actualCoefficientLaw Q) := by
    apply (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2
    refine ⟨(hmeas.pow_const 2).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _)).2
    exact hb.trans_lt ENNReal.ofReal_lt_top
  exact ⟨hf, norm_toLp_sq_le_of_lintegral_sq_le hf (by positivity) hb⟩

/-- Central-limit normalization cancels the microscopic scale in the source
second moment. The constant is still chosen before the coefficient law. -/
theorem compact_commutator_actual_coefficient_law_normalized_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d) (ψ : Vec d → ℝ) (B : ℝ), 0 ≤ B →
        IsSpatialTest (originBall d 1) ψ →
        integerSobolevTestNorm m (originBall d 1) ψ ≤ B →
        ∃ hf : MemLp (compactSourceCommutatorPairing S e ε j ψ) 2
            (actualCoefficientLaw Q),
          ‖(ε ^ (-(d : ℝ) / 2)) •
            hf.toLp (compactSourceCommutatorPairing S e ε j ψ)‖ ≤ C * B := by
  obtain ⟨C, hC, h⟩ := compact_commutator_actual_coefficient_law_L2 d hd L hL m hm
  refine ⟨Real.sqrt C, Real.sqrt_pos.2 hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro e he ε hε hε₂ j ψ B hB hψ hnψ
  have hpos (b : ℝ) (hb : 0 < b)
      (hnb : integerSobolevTestNorm m (originBall d 1) ψ ≤ b)
      (hf : MemLp (compactSourceCommutatorPairing S e ε j ψ) 2
        (actualCoefficientLaw Q)) :
      ‖(ε ^ (-(d : ℝ) / 2)) •
        hf.toLp (compactSourceCommutatorPairing S e ε j ψ)‖ ≤ Real.sqrt C * b := by
    obtain ⟨hf₀, hb₀⟩ := hS e he ε hε hε₂ j ψ b hb hψ hnb
    have hb' : ‖hf.toLp (compactSourceCommutatorPairing S e ε j ψ)‖ ^ 2 ≤
        C * ε ^ (d : ℝ) * b ^ 2 := hb₀
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
    have hs : (ε ^ (-(d : ℝ) / 2)) ^ 2 * ε ^ (d : ℝ) = 1 := by
      rw [← Real.rpow_mul_natCast hε.le, ← Real.rpow_add hε]
      convert Real.rpow_zero ε using 1 <;> norm_num <;> ring
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hε _), mul_pow]
    calc
      _ ≤ (ε ^ (-(d : ℝ) / 2)) ^ 2 * (C * ε ^ (d : ℝ) * b ^ 2) :=
        mul_le_mul_of_nonneg_left hb' (sq_nonneg _)
      _ = C * b ^ 2 * ((ε ^ (-(d : ℝ) / 2)) ^ 2 * ε ^ (d : ℝ)) := by ring
      _ = C * b ^ 2 := by rw [hs, mul_one]
      _ = (Real.sqrt C * b) ^ 2 := by rw [mul_pow, Real.sq_sqrt hC.le]
  obtain ⟨hf, _⟩ := hS e he ε hε hε₂ j ψ (B + 1) (by linarith) hψ (by linarith)
  refine ⟨hf, le_of_forall_pos_le_add fun δ hδ => ?_⟩
  calc
    _ ≤ Real.sqrt C * (B + δ / Real.sqrt C) :=
      hpos _ (by have := Real.sqrt_pos.2 hC; positivity)
        (hnψ.trans (le_add_of_nonneg_right (by positivity))) hf
    _ = Real.sqrt C * B + δ := by
      field_simp


/-- A compact Schwartz piece obeys the source L² bound with its original
Schwartz order. The constant precedes the law and every localization scale;
all source-test measurability and L² membership are proved internally. -/
theorem compact_source_schwartz_cutoff_normalized_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 ≤ a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ N : ℕ, m ≤ N →
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 / 2 →
      ∀ (j : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
      ∀ c : ℝ, 1 ≤ c →
        ∃ hf : MemLp
            (compactSourceCommutatorPairing S e ε j (fun y => χ y * ℓ (F (c • y))))
            2 (actualCoefficientLaw Q),
          ‖(ε ^ (-(d : ℝ) / 2)) • hf.toLp
            (compactSourceCommutatorPairing S e ε j (fun y => χ y * ℓ (F (c • y))))‖ ≤
            C * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N := by
  have hvol : volume (originBall d 1) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      ((isCompact_closedBall (0 : Vec d) 1).measure_ne_top (μ := volume))
    apply measure_mono
    intro x hx
    apply mem_closedBall_zero_iff.mpr
    exact (S1.norm_le_euclideanNorm x).trans (le_of_lt hx)
  obtain ⟨A, hA, hcut⟩ := exists_schwartz_cutoff_integerSobolevTestNorm_bound
    m (originBall d 1) hvol hχ.1 hχ.2.1 ha hχa
  obtain ⟨C, hC, h⟩ :=
    compact_commutator_actual_coefficient_law_normalized_L2 d hd L hL m hm
  refine ⟨C * A, mul_pos hC hA, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro N hmN e he ε hε hε₂ j F ℓ hℓ c hc
  have htest := isSpatialTest_cutoff_schwartz hχ F ℓ c
  have hSob := hcut N hmN F ℓ hℓ c hc
  have hnorm := clockSchwartz_norm_nonneg N F
  obtain ⟨hf, hb⟩ := hS e he ε hε hε₂ j _
    (A * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N)
    (by positivity) htest hSob
  refine ⟨hf, hb.trans_eq ?_⟩
  ring


/-- The literal Euclidean unit ball has finite volume, by inclusion in the
closed ball for the inherited coordinate norm. -/
theorem volume_originBall_one_ne_top (d : ℕ) : volume (originBall d 1) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    ((isCompact_closedBall (0 : Vec d) 1).measure_ne_top (μ := volume))
  apply measure_mono
  intro x hx
  apply mem_closedBall_zero_iff.mpr
  exact (S1.norm_le_euclideanNorm x).trans (le_of_lt hx)

/-- Physical localization at radius R*c changes to the source unit ball.
The formula holds for totalized integrals; it does not assume integrability
of individual source fluxes in probability. -/
theorem integral_physical_cutoff_eq_average {d : ℕ} {χ : Vec d → ℝ}
    (hχ : tsupport χ ⊆ originBall d 1) (g f : Vec d → ℝ)
    {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    (∫ x, g x * (χ ((R * c)⁻¹ • x) * f (R⁻¹ • x))) =
      (R * c) ^ d * (volume (originBall d 1)).toReal *
        (⨍ y in originBall d 1, g ((R * c) • y) * (χ y * f (c • y))) := by
  let H : Vec d → ℝ := fun y => g ((R * c) • y) * (χ y * f (c • y))
  have hs : 0 < R * c := mul_pos hR hc
  have hscalar : c * (R * c)⁻¹ = R⁻¹ := by field_simp
  have hcomp : (fun x => g x * (χ ((R * c)⁻¹ • x) * f (R⁻¹ • x))) =
      fun x => H ((R * c)⁻¹ • x) := by
    funext x
    simp only [H, smul_smul, mul_inv_cancel₀ hs.ne', one_smul, hscalar]
  have hzero (y : Vec d) (hy : y ∉ originBall d 1) : H y = 0 := by
    have hχy : χ y = 0 := by
      by_contra hh
      exact hy (hχ (subset_closure (show y ∈ Function.support χ from hh)))
    simp only [H, hχy, zero_mul, mul_zero]
  have hI : (∫ y, H y) = ∫ y in originBall d 1, H y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [hcomp]
  have hdilate := Measure.integral_comp_inv_smul_of_nonneg volume H hs.le
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hdilate
  rw [hdilate, hI, ← measure_smul_setAverage H (volume_originBall_one_ne_top d)]
  simp only [smul_eq_mul, Measure.real, H]
  ring

/-- Physical source pairing for one compact scalar test. It retains the
centered flux and the full anisotropic matrix contraction as separate
spatial integrals until spatial integrability permits their combination. -/
noncomputable def physicalSourceCommutatorPairing {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (S : SourceObjects P)
    (e : Vec d) (R c : ℝ) (j : Fin d) (χ f : Vec d → ℝ)
    (a : Coefficient d K) : ℝ :=
  R ^ (-(d : ℝ) / 2) *
    ((∫ x, ((a x).mulVec (e + (S.corrector e).grad a x) -
      S.homogenized.mulVec e) j * (χ ((R * c)⁻¹ • x) * f (R⁻¹ • x))) -
    ∑ k, S.homogenized j k * (∫ x, (S.corrector e).grad a x k *
      (χ ((R * c)⁻¹ • x) * f (R⁻¹ • x))))

/-- Exact physical-to-source rescaling, with both the unit-ball volume
and the unnormalized Jacobian retained. -/
theorem physicalSourceCommutatorPairing_eq {d : ℕ} {K : ℝ}
    {P : Measure (Coefficient d K)} (S : SourceObjects P)
    (e : Vec d) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (j : Fin d)
    {χ : Vec d → ℝ} (hχ : tsupport χ ⊆ originBall d 1)
    (f : Vec d → ℝ) (a : Coefficient d K) :
    physicalSourceCommutatorPairing S e R c j χ f a =
      ((volume (originBall d 1)).toReal * (R ^ (-(d : ℝ) / 2) * (R * c) ^ d)) *
        compactSourceCommutatorPairing S e (R * c)⁻¹ j (fun y => χ y * f (c • y)) a := by
  unfold physicalSourceCommutatorPairing compactSourceCommutatorPairing
  simp_rw [integral_physical_cutoff_eq_average hχ _ _ hR hc]
  simp only [inv_inv]
  simp_rw [mul_sub, Finset.mul_sum]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro k _
    ring

/-- Splitting the physical Jacobian leaves precisely the localization
factor c^(d/2) beside the source central-limit normalization. -/
theorem physical_cutoff_clt_scale (d : ℕ) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    R ^ (-(d : ℝ) / 2) * (R * c) ^ d =
      c ^ ((d : ℝ) / 2) * ((R * c)⁻¹) ^ (-(d : ℝ) / 2) := by
  have hinv : ((R * c)⁻¹) ^ (-(d : ℝ) / 2) = (R * c) ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hRpow : R ^ (-(d : ℝ) / 2) * R ^ (d : ℝ) = R ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_add hR]
    congr 1
    ring
  have hcpow : c ^ ((d : ℝ) / 2) * c ^ ((d : ℝ) / 2) = c ^ (d : ℝ) := by
    rw [← Real.rpow_add hc]
    congr 1
    ring
  rw [hinv, mul_pow, ← Real.rpow_natCast R d, ← Real.rpow_natCast c d]
  rw [Real.mul_rpow hR.le hc.le]
  calc
    _ = (R ^ (-(d : ℝ) / 2) * R ^ (d : ℝ)) * c ^ (d : ℝ) := by ring
    _ = R ^ ((d : ℝ) / 2) * c ^ (d : ℝ) := by rw [hRpow]
    _ = c ^ ((d : ℝ) / 2) * (R ^ ((d : ℝ) / 2) * c ^ ((d : ℝ) / 2)) := by
      rw [← hcpow]
      ring


/-- Physical localization preserves source L² membership, and its norm has
exactly the central-limit rescaling factor. -/
theorem physicalSourceCommutatorPairing_memLp_norm
    {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} (S : SourceObjects P)
    (e : Vec d) {R c : ℝ} (hR : 0 < R) (hc : 0 < c) (j : Fin d)
    {χ : Vec d → ℝ} (hχ : tsupport χ ⊆ originBall d 1) (f : Vec d → ℝ)
    (hf : MemLp (compactSourceCommutatorPairing S e (R * c)⁻¹ j
      (fun y => χ y * f (c • y))) 2 P) :
    ∃ hp : MemLp (physicalSourceCommutatorPairing S e R c j χ f) 2 P,
      ‖hp.toLp (physicalSourceCommutatorPairing S e R c j χ f)‖ =
        (volume (originBall d 1)).toReal * c ^ ((d : ℝ) / 2) *
          ‖(((R * c)⁻¹) ^ (-(d : ℝ) / 2)) • hf.toLp
            (compactSourceCommutatorPairing S e (R * c)⁻¹ j
              (fun y => χ y * f (c • y)))‖ := by
  have heq : physicalSourceCommutatorPairing S e R c j χ f =
      ((volume (originBall d 1)).toReal * c ^ ((d : ℝ) / 2)) •
        ((((R * c)⁻¹) ^ (-(d : ℝ) / 2)) •
          compactSourceCommutatorPairing S e (R * c)⁻¹ j
            (fun y => χ y * f (c • y))) := by
    funext a
    rw [physicalSourceCommutatorPairing_eq S e hR hc j hχ f a,
      physical_cutoff_clt_scale d hR hc]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hs := (hf.const_smul (((R * c)⁻¹) ^ (-(d : ℝ) / 2))).const_smul
    ((volume (originBall d 1)).toReal * c ^ ((d : ℝ) / 2))
  have hp := (memLp_congr_ae (ae_of_all P fun a => congrFun heq.symm a)).1 hs
  refine ⟨hp, ?_⟩
  rw [hp.toLp_congr hs (ae_of_all P fun a => congrFun heq a),
    MemLp.toLp_const_smul _ (hf.const_smul _), MemLp.toLp_const_smul _ hf,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- A physical compact Schwartz piece satisfies a scale-uniform L² bound.
The original Schwartz order is retained, and the same source object serves
all radii, localization scales and tests. -/
theorem physical_source_schwartz_cutoff_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 ≤ a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ N : ℕ, m ≤ N →
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (R : ℝ), 1 ≤ R → ∀ (j : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
      ∀ c : ℝ, 4 ≤ c →
        ∃ hp : MemLp (physicalSourceCommutatorPairing S e R c j χ
            (fun x => ℓ (F x))) 2 (actualCoefficientLaw Q),
          ‖hp.toLp (physicalSourceCommutatorPairing S e R c j χ
            (fun x => ℓ (F x)))‖ ≤
            C * c ^ (m + d) * schwartzTestNorm N F / (1 + c * a) ^ N := by
  obtain ⟨C, hC, h⟩ := compact_source_schwartz_cutoff_normalized_L2
    d hd L hL m hm hχ ha hχa
  let V : ℝ := (volume (originBall d 1)).toReal
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  refine ⟨(V + 1) * C, mul_pos (by positivity) hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro N hmN e he R hR j F ℓ hℓ c hc
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc1 : 1 ≤ c := by linarith
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hRc : 2 < R * c := by nlinarith
  obtain ⟨hf, hb⟩ := hS N hmN e he (R * c)⁻¹ (by positivity)
    ((inv_lt_comm₀ (mul_pos hRpos hcpos) (by norm_num)).2 (by simpa using hRc))
    j F ℓ hℓ c hc1
  obtain ⟨hp, hnorm⟩ := physicalSourceCommutatorPairing_memLp_norm
    S e hRpos hcpos j hχ.2.2 (fun x => ℓ (F x)) hf
  refine ⟨hp, ?_⟩
  have hpow : c ^ ((d : ℝ) / 2) ≤ c ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hc1 (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hnF := clockSchwartz_norm_nonneg N F
  calc
    _ = V * c ^ ((d : ℝ) / 2) *
        ‖(((R * c)⁻¹) ^ (-(d : ℝ) / 2)) • hf.toLp
          (compactSourceCommutatorPairing S e (R * c)⁻¹ j
            (fun y => χ y * ℓ (F (c • y))))‖ := hnorm
    _ ≤ V * c ^ ((d : ℝ) / 2) *
        (C * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (V + 1) * c ^ d *
        (C * c ^ m * schwartzTestNorm N F / (1 + c * a) ^ N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul (le_add_of_nonneg_right zero_le_one) hpow (by positivity) (by positivity)
    _ = (V + 1) * C * c ^ (m + d) * schwartzTestNorm N F /
        (1 + c * a) ^ N := by rw [pow_add]; ring


/-- Dyadic Schwartz decay controls the sum in any normed group,
with the annular radius retained in the quantitative bound. -/
theorem norm_tsum_le_of_dyadic_schwartz_decay {E : Type*}
    [NormedAddCommGroup E] {p N : ℕ} (hpN : p + 1 ≤ N)
    {a b : ℝ} (ha : 0 < a) (hb : 1 ≤ b) {B : ℝ} (hB : 0 ≤ B)
    {u : ℕ → E}
    (hu : ∀ n, ‖u n‖ ≤ B * ((b * (2 : ℝ) ^ n) ^ p /
      (1 + (b * (2 : ℝ) ^ n) * a) ^ N)) :
    Summable (fun n => ‖u n‖) ∧ ‖∑' n, u n‖ ≤ 2 * B * (a ^ N)⁻¹ := by
  have hd := summable_dyadic_schwartz_decay hpN ha hb
  have hmajor := hd.mul_left B
  have hs : Summable (fun n => ‖u n‖) :=
    hmajor.of_nonneg_of_le (fun n => norm_nonneg (u n)) hu
  refine ⟨hs, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' n : ℕ, B * ((b * (2 : ℝ) ^ n) ^ p /
        (1 + (b * (2 : ℝ) ^ n) * a) ^ N) := hs.tsum_le_tsum hu hmajor
    _ = B * ∑' n : ℕ, (b * (2 : ℝ) ^ n) ^ p /
        (1 + (b * (2 : ℝ) ^ n) * a) ^ N := tsum_mul_left
    _ ≤ B * (2 * (a ^ N)⁻¹) :=
      mul_le_mul_of_nonneg_left (tsum_dyadic_schwartz_decay_le hpN ha hb) hB
    _ = _ := by ring

/-- Summable L² norms produce an actual measurable pointwise sum, and its
L² element is the sum of the original representatives. All measurability
of the infinite sum is obtained internally from the series estimate. -/
theorem memLp_tsum_of_summable_toLp_norm {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [CompleteSpace E] {μ : Measure Ω}
    {f : ℕ → Ω → E} (hf : ∀ n, MemLp (f n) 2 μ)
    (hs : Summable (fun n => ‖(hf n).toLp (f n)‖)) :
    ∃ ht : MemLp (fun ω => ∑' n, f n ω) 2 μ,
      ht.toLp (fun ω => ∑' n, f n ω) = ∑' n, (hf n).toLp (f n) ∧
      ∀ᵐ ω ∂μ, HasSum (fun n => f n ω) ((∑' n, (hf n).toLp (f n)) ω) := by
  have he : (∑' n, ‖(hf n).toLp (f n)‖ₑ) ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.2 hs
  have hreps : ∀ᵐ ω ∂μ, ∀ n, (hf n).toLp (f n) ω = f n ω :=
    ae_all_iff.2 fun n => (hf n).coeFn_toLp
  have hsum : ∀ᵐ ω ∂μ,
      HasSum (fun n => f n ω) ((∑' n, (hf n).toLp (f n)) ω) := by
    filter_upwards [Lp.hasSum_coeFn_tsum he, hreps] with ω hω hrep
    simpa only [hrep] using hω
  have heq : (fun ω => ∑' n, f n ω) =ᵐ[μ]
      (fun ω => (∑' n, (hf n).toLp (f n)) ω) :=
    hsum.mono fun _ hω => hω.tsum_eq
  have ht := (Lp.memLp (∑' n, (hf n).toLp (f n))).ae_eq heq.symm
  refine ⟨ht, ?_, hsum⟩
  exact (ht.toLp_congr (Lp.memLp _) heq).trans (Lp.toLp_coeFn _ _)

/-- The physical annular pieces form a summable L² series at the original
Schwartz order. The source is chosen once before every test and scale. -/
theorem physical_source_schwartz_dyadic_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 < a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ N : ℕ, m + d + 1 ≤ N →
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (R : ℝ), 1 ≤ R → ∀ (j : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
        ∃ hf : ∀ n : ℕ, MemLp
            (physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
              (fun x => ℓ (F x))) 2 (actualCoefficientLaw Q),
          Summable (fun n => ‖(hf n).toLp
            (physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
              (fun x => ℓ (F x)))‖) ∧
          ‖∑' n, (hf n).toLp
            (physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
              (fun x => ℓ (F x)))‖ ≤
            C * (a ^ N)⁻¹ * schwartzTestNorm N F := by
  obtain ⟨C, hC, h⟩ := physical_source_schwartz_cutoff_L2 d hd L hL m hm hχ ha.le hχa
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro N hN e he R hR j F ℓ hℓ
  have hmN : m ≤ N := by omega
  have hscale (n : ℕ) : 4 ≤ 4 * (2 : ℝ) ^ n := by
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hpieces (n : ℕ) := hS N hmN e he R hR j F ℓ hℓ
    (4 * (2 : ℝ) ^ n) (hscale n)
  choose hf hnorm using hpieces
  have hnF := clockSchwartz_norm_nonneg N F
  obtain ⟨hs, hb⟩ := norm_tsum_le_of_dyadic_schwartz_decay
    (p := m + d) hN ha (by norm_num : (1 : ℝ) ≤ 4)
    (B := C * schwartzTestNorm N F) (by positivity)
    (u := fun n => (hf n).toLp
      (physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
        (fun x => ℓ (F x)))) (fun n => (hnorm n).trans_eq (by ring))
  refine ⟨hf, hs, hb.trans_eq ?_⟩
  ring


/-- The annular series is itself an actual L² random variable on the
coefficient law, with the same quantitative Schwartz bound. -/
theorem physical_source_schwartz_dyadic_tsum_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 < a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ S : SourceObjects (actualCoefficientLaw Q),
      ∀ N : ℕ, m + d + 1 ≤ N →
      ∀ (e : Vec d), euclideanNorm e < 1 →
      ∀ (R : ℝ), 1 ≤ R → ∀ (j : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
        ∃ ht : MemLp (fun ω => ∑' n : ℕ,
            physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
              (fun x => ℓ (F x)) ω) 2 (actualCoefficientLaw Q),
          ‖ht.toLp (fun ω => ∑' n : ℕ,
            physicalSourceCommutatorPairing S e R (4 * (2 : ℝ) ^ n) j χ
              (fun x => ℓ (F x)) ω)‖ ≤
            C * (a ^ N)⁻¹ * schwartzTestNorm N F := by
  obtain ⟨C, hC, h⟩ := physical_source_schwartz_dyadic_L2 d hd L hL m hm hχ ha hχa
  refine ⟨C, hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  refine ⟨S, ?_⟩
  intro N hN e he R hR j F ℓ hℓ
  obtain ⟨hf, hs, hb⟩ := hS N hN e he R hR j F ℓ hℓ
  obtain ⟨ht, hrep, _⟩ := memLp_tsum_of_summable_toLp_norm hf hs
  refine ⟨ht, ?_⟩
  rw [hrep]
  exact hb

/-- The literal scaled coordinate pairing is represented by an actual
samplewise spatial integral. Joint integrability and measurability follow
from the L² translation kernel and its measurable orbit representative. -/
theorem scaledComplexClockPairing_joint_integral {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (u : Lp ℂ 2 (reducedLaw Q)) {f : Vec d → ℂ}
    (hc : Continuous f) (hf : Integrable f) :
    Integrable (fun p : Vec d × FieldPair d =>
      ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        (f (R⁻¹ • p.1) * u (translate p.1 p.2)))
      (volume.prod (reducedLaw Q)) ∧
    (scaledComplexClockPairing Q R u f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∫ x, ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        (f (R⁻¹ • x) * u (translate x ω)) := by
  let := reducedLaw_probability Q
  let c : ℂ := ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ)
  let v : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x =>
    c • (f (R⁻¹ • x) • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x u)
  let V : Vec d × FieldPair d → ℂ := fun p =>
    c * (f (R⁻¹ • p.1) * u (translate p.1 p.2))
  have hv : Integrable v := Integrable.smul c
    (integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
      _ (hf.comp_smul (inv_ne_zero hR.ne'))
      (hc.comp (continuous_id.const_smul R⁻¹)) u)
  have hV : Measurable V := by
    have ht : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
      Probability.continuous_translate.measurable
    exact ((hc.measurable.comp (measurable_fst.const_smul R⁻¹)).mul
      ((Lp.stronglyMeasurable u).measurable.comp ht)).const_mul c
  have heq (x : Vec d) : (fun ω => V (x, ω)) =ᵐ[reducedLaw Q] v x := by
    filter_upwards [Lp.coeFn_smul c (f (R⁻¹ • x) • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) x u),
      Lp.coeFn_smul (f (R⁻¹ • x)) (complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x u),
      coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x u]
      with ω hcω hfω htω
    dsimp only [v, V]
    rw [hcω, Pi.smul_apply, hfω, Pi.smul_apply, htω]
    rfl
  have hp : scaledComplexClockPairing Q R u f = ∫ x, v x := by
    unfold scaledComplexClockPairing complexClockSpatialPairing
    rw [← integral_smul]
  refine ⟨integrable_joint_l2_representative hv hV heq, ?_⟩
  rw [hp]
  exact coeFn_integral_joint_l2_representative hv hV heq

/-- Every coordinate of the literal joint pairing has one common,
jointly integrable samplewise spatial representative. No hypotheses on a
chosen pointwise field or on spatial integrability are required. -/
theorem scaledJointPairing_joint_integral {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {R : ℝ} (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Integrable (fun p : Vec d × FieldPair d =>
      ∑ a : JointObservationIndex d,
        ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          (F (R⁻¹ • p.1) a * Z a (translate p.1 p.2)))
      (volume.prod (reducedLaw Q)) ∧
    (scaledJointPairing Q R hR Z F : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∫ x, ∑ a : JointObservationIndex d,
        ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          (F (R⁻¹ • x) a * Z a (translate x ω)) := by
  classical
  have hcoord (a : JointObservationIndex d) :=
    scaledComplexClockPairing_joint_integral Q hR (Z a)
      ((PiLp.continuous_apply 2 _ a).comp F.continuous)
      (F.integrable.mono
        ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
        (ae_of_all _ fun x => PiLp.norm_apply_le (F x) a))
  refine ⟨integrable_finsetSum _ (fun a _ => (hcoord a).1), ?_⟩
  rw [scaledJointPairing_eq_sum_coordinates Q hR Z F]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun a => scaledComplexClockPairing Q R (Z a) (fun x => F x a)),
    ae_all_iff.2 (fun a => (hcoord a).2),
    ae_all_iff.2 (fun a => (hcoord a).1.prod_left_ae)] with ω hsum heq hi
  rw [hsum]
  change (∑ a, scaledComplexClockPairing Q R (Z a) (fun x => F x a) ω) = _
  exact (Finset.sum_congr rfl (fun a _ => heq a)).trans
    (integral_finsetSum _ (fun a _ => hi a)).symm


/-- A homogeneous weak equation admits its actual cutoff energy estimate.
This is a spatial estimate for local H¹ representatives; no regularity or
large-scale estimate is used. -/
theorem weakHarmonic_cutoff_energy {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hG : ∀ j, MemLp (fun x => G x j) 2 (volume.restrict U))
    (hw : HasWeakGradient U u G)
    (hdiv : HasWeakDivergence U (fun x => (A x).mulVec (G x)) (fun _ => 0))
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ) (hχ0 : ∀ x, 0 ≤ χ x) :
    Integrable (fun x => χ x ^ 2 * euclideanSq (G x)) (volume.restrict U) ∧
      Integrable (fun x => u x ^ 2 * euclideanSq (gradient χ x))
        (volume.restrict U) ∧
      (∫ x in U, χ x ^ 2 * euclideanSq (G x)) ≤
        4 * K ^ 2 * ∫ x in U, u x ^ 2 * euclideanSq (gradient χ x) := by
  let μ := volume.restrict U
  let F := fun x => (A x).mulVec (G x)
  have hF (i : Fin d) : MemLp (fun x => F x i) 2 μ := by
    have hAj (j : Fin d) : MemLp (fun x => A x i j) ⊤ μ := by
      apply memLp_top_of_bound
        ((A.locally_integrable i j).aestronglyMeasurable.mono_measure
          Measure.restrict_le_self) K
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact EinsteinRelation.abs_entry_le_of_quadratic_bounds hK.le (A x) (A.symmetric x)
        (fun ξ => (EinsteinRelation.euclideanSq_nonneg_coords ξ).trans (A.elliptic x ξ).1)
        (fun ξ => (A.elliptic x ξ).2) i j
    simpa only [F, Matrix.mulVec, dotProduct, mul_comm] using
      memLp_finset_sum Finset.univ (fun j _ => (hG j).mul' (r := 2) (hAj j))
  have hE : Integrable (fun x => χ x ^ 2 * euclideanSq (G x)) μ :=
    (Correctors.localized_H1_energy_products_integrable hχ hu hG hG).2.2.2
  have hErr : Integrable (fun x => u x ^ 2 * euclideanSq (gradient χ x)) μ := by
    have hi (j : Fin d) : Integrable (fun x => (u x * coordinateDerivative j χ x)^2) μ := by
      have hD : MemLp (coordinateDerivative j χ) ⊤ μ :=
        (Correctors.isSpatialTest_coordinateDerivative hχ j).1.continuous
          |>.memLp_top_of_hasCompactSupport
            (Correctors.isSpatialTest_coordinateDerivative hχ j).2.1 μ
      exact (hu.mul' hD).integrable_sq
    convert integrable_finset_sum Finset.univ (fun j _ => hi j) using 1
    funext x
    simp only [euclideanSq, dot, gradient, Finset.mul_sum, mul_pow]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let P := fun x => dot (F x)
    (fun j => χ x ^ 2 * G x j + 2 * χ x * u x * coordinateDerivative j χ x)
  have hp (x : Vec d) : P x = χ x ^ 2 * dot (F x) (G x) +
      2 * (χ x * u x * dot (F x) (gradient χ x)) := by
    simp only [P, dot, gradient, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  have hP : Integrable P μ := by
    have he : P = (fun x => χ x ^ 2 * dot (F x) (G x) +
        2 * (χ x * u x * dot (F x) (gradient χ x))) := funext hp
    rw [he]
    exact (Correctors.localized_H1_energy_products_integrable hχ hu hF hG).2.2.2.add
      ((Correctors.localized_H1_energy_products_integrable hχ hu hF hG).2.2.1.const_mul 2)
  have hP0 : (∫ x, P x ∂μ) = 0 := by
    have ht := Correctors.weakDivergence_test_cutoff_H1 hU hu hG hF MemLp.zero' hw hdiv hχ
    simpa only [zero_mul, integral_zero, neg_zero] using ht
  have hpoint (x : Vec d) : χ x ^ 2 * euclideanSq (G x) ≤
      2 * P x + (4 * K ^ 2) * (u x ^ 2 * euclideanSq (gradient χ x)) := by
    have h := Correctors.paired_cutoff_coercivity hK A x (G x) (gradient χ x)
      (u x) (χ x) (hχ0 x) 1 (by omega)
    norm_num only [Nat.cast_one, one_pow, one_mul, Nat.mul_one, Nat.reduceSub,
      Nat.cast_ofNat, pow_zero, mul_one] at h
    rw [hp]
    have hc : dot (F x) (G x) = dot (G x) ((A x).mulVec (G x)) :=
      dotProduct_comm _ _
    rw [hc]
    convert h using 1 <;> ring
  refine ⟨hE, hErr, ?_⟩
  have hi := integral_mono hE ((hP.const_mul 2).add (hErr.const_mul (4 * K^2))) hpoint
  change (∫ x, χ x ^ 2 * euclideanSq (G x) ∂μ) ≤
    (∫ x, 2 * P x + (4 * K^2) * (u x^2 * euclideanSq (gradient χ x)) ∂μ) at hi
  rw [integral_add (hP.const_mul 2) (hErr.const_mul (4 * K^2)),
    integral_const_mul, integral_const_mul, hP0] at hi
  simpa only [mul_zero, zero_add] using hi


/-- Every pair of source correctors with the same slope satisfies the spatial
energy estimate, with arbitrary centering of its actual local potential. -/
theorem sourceCorrector_difference_cutoff_energy {d : ℕ} {K : ℝ} (hK : 0 < K)
    {P : Measure (Coefficient d K)} {e : Vec d}
    (φ ψ : SourceCorrector P e) :
    ∀ᵐ a ∂P, ∀ (R : ℝ), 0 < R → ∀ (c : ℝ) (χ : Vec d → ℝ),
      IsSpatialTest (ball 0 R) χ → (∀ x, 0 ≤ χ x) →
      Integrable (fun x => χ x ^ 2 * euclideanSq (φ.grad a x - ψ.grad a x))
        (volume.restrict (ball 0 R)) ∧
      Integrable (fun x => (φ.potential a x - ψ.potential a x - c) ^ 2 *
        euclideanSq (gradient χ x)) (volume.restrict (ball 0 R)) ∧
      (∫ x in ball 0 R, χ x ^ 2 * euclideanSq (φ.grad a x - ψ.grad a x)) ≤
        4 * K ^ 2 * ∫ x in ball 0 R,
          (φ.potential a x - ψ.potential a x - c) ^ 2 * euclideanSq (gradient χ x) := by
  filter_upwards [φ.weak_gradient, ψ.weak_gradient, φ.locally_square_integrable,
    ψ.locally_square_integrable, φ.harmonic, ψ.harmonic] with a hwφ hwψ hlφ hlψ hdφ hdψ
  intro R hR c χ hχ hχ0
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
    simpa using (ENNReal.toReal_pos_iff.mp (Correctors.ball_volume_pos_finite d R hR)).2⟩
  have hs := (Correctors.affine_corrector_difference_weakSolution a e
    (φ.potential a) (ψ.potential a) (φ.grad a) (ψ.grad a) hwφ hwψ
    (fun r hr => (hlφ r hr).1) (fun r hr => (hlψ r hr).1)
    (fun r hr => (hlφ r hr).2) (fun r hr => (hlψ r hr).2) hdφ hdψ).2 R hR
  have hU : IsOpen (ball (0 : Vec d) R) := by
    unfold ball euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const
  exact weakHarmonic_cutoff_energy hK a hU
    (hs.1.sub (memLp_const c)) (memLp_pi_iff.mp hs.2.1)
    (Correctors.hasWeakGradient_sub_const _ hs.2.2.1 c) hs.2.2.2 hχ hχ0


/-- A uniform spatial Caccioppoli bound for the difference of arbitrary source
correctors. Both balls retain the Euclidean norm of the source characterization. The constant precedes the source law. -/
theorem sourceCorrector_difference_ball_energy (d : ℕ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (K : ℝ), 0 < K →
      ∀ (P : Measure (Coefficient d K)) (e : Vec d) (φ ψ : SourceCorrector P e),
      ∀ᵐ a ∂P, ∀ (R : ℝ), 0 < R → ∀ c : ℝ,
        (∫ x in originBall d (2*R), euclideanSq (φ.grad a x - ψ.grad a x)) ≤
          4 * K^2 * (D/R)^2 * ∫ x in ball 0 (4*R),
            (φ.potential a x - ψ.potential a x - c)^2 := by
  obtain ⟨D, hD, hcut⟩ := Correctors.exists_paired_euclidean_spatial_cutoff d
  refine ⟨D, hD, ?_⟩
  intro K hK P e φ ψ
  filter_upwards [sourceCorrector_difference_cutoff_energy hK φ ψ,
    φ.locally_square_integrable, ψ.locally_square_integrable] with a henergy hlφ hlψ
  intro R hR c
  have h4R : 0 < 4*R := by positivity
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (4*R))) := ⟨by
    simpa using (ENNReal.toReal_pos_iff.mp
      (Correctors.ball_volume_pos_finite d (4*R) h4R)).2⟩
  obtain ⟨χ, hχ, hχb, hχ1, hχD⟩ := hcut R hR
  have hχ' : IsSpatialTest (ball 0 (4*R)) χ := by
    simpa only [originBall, ball, sub_zero] using hχ
  obtain ⟨hE, hErr, hbound⟩ := henergy (4*R) h4R c χ hχ' (fun x => (hχb x).1)
  have hUV : originBall d (2*R) ⊆ ball (0 : Vec d) (4*R) := by
    intro x hx
    have hx' : euclideanNorm x < 2*R := hx
    have hh : euclideanNorm x < 4*R := by linarith
    simpa only [ball, sub_zero, Set.mem_setOf_eq] using hh
  have hV : MeasurableSet (originBall d (2*R)) := by
    apply measurableSet_lt _ measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hsmall : (∫ x in originBall d (2*R), euclideanSq (φ.grad a x - ψ.grad a x)) ≤
      ∫ x in ball 0 (4*R), χ x^2 * euclideanSq (φ.grad a x - ψ.grad a x) := by
    calc
      _ = ∫ x in originBall d (2*R), χ x^2 * euclideanSq (φ.grad a x - ψ.grad a x) := by
        apply setIntegral_congr_fun hV
        intro x hx
        dsimp only
        rw [hχ1 x hx, one_pow, one_mul]
      _ ≤ _ := setIntegral_mono_set hE
        (Filter.Eventually.of_forall fun x =>
          mul_nonneg (sq_nonneg _) (EinsteinRelation.euclideanSq_nonneg_coords _))
        (Filter.Eventually.of_forall hUV)
  have hu := (((hlφ (4*R) h4R).1.sub (hlψ (4*R) h4R).1).sub
    (memLp_const c)).integrable_sq
  have herrle : (∫ x in ball 0 (4*R),
      (φ.potential a x - ψ.potential a x - c)^2 * euclideanSq (gradient χ x)) ≤
      (D/R)^2 * ∫ x in ball 0 (4*R), (φ.potential a x - ψ.potential a x - c)^2 := by
    rw [← integral_const_mul]
    apply integral_mono hErr (hu.const_mul _)
    intro x
    change (φ.potential a x - ψ.potential a x - c)^2 * euclideanSq (gradient χ x) ≤
      (D/R)^2 * (φ.potential a x - ψ.potential a x - c)^2
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hχD x)
      (sq_nonneg (φ.potential a x - ψ.potential a x - c))
  calc
    _ ≤ _ := hsmall.trans hbound
    _ ≤ 4*K^2 * ((D/R)^2 * ∫ x in ball 0 (4*R),
        (φ.potential a x - ψ.potential a x - c)^2) :=
      mul_le_mul_of_nonneg_left herrle (by positivity)
    _ = _ := by ring


open Filter Topology

/-- The difference of any two characterized source gradients has vanishing
large-ball mean energy. Only their local equations and centered sublinearity
are used; no large-scale oscillation estimate is an input. -/
theorem sourceCorrector_difference_mean_energy_tendsto_zero {d : ℕ} {K : ℝ}
    (hK : 0 < K) {P : Measure (Coefficient d K)} {e : Vec d}
    (φ ψ : SourceCorrector P e) :
    ∀ᵐ a ∂P, Tendsto (fun R : ℝ =>
      ⨍ x in ball 0 R, euclideanSq (φ.grad a x - ψ.grad a x)) atTop (𝓝 0) := by
  obtain ⟨D, hD, henergy⟩ := sourceCorrector_difference_ball_energy d
  filter_upwards [henergy K hK P e φ ψ, φ.locally_square_integrable,
    ψ.locally_square_integrable, φ.sublinear, ψ.sublinear] with a hE hlφ hlψ hsφ hsψ
  let u := fun x => φ.potential a x - ψ.potential a x
  let S := fun r : ℝ => ⨍ x in ball 0 r, (u x - ⨍ y in ball 0 r, u y)^2
  have hsub := Correctors.sublinear_centered_oscillation_sub
    (φ.potential a) (ψ.potential a) (fun r hr => (hlφ r hr).1)
    (fun r hr => (hlψ r hr).1) hsφ hsψ
  have hlim : Tendsto (fun R : ℝ =>
      64*K^2*D^2*(2:ℝ)^d * ((4*R)⁻¹ * Real.sqrt (S (4*R)))^2)
      atTop (𝓝 0) := by
    have ht := (hsub.comp ((tendsto_const_mul_atTop_of_pos
      (by norm_num : (0:ℝ)<4)).mpr tendsto_id)).pow 2
    simpa only [Function.comp_def, id_eq, S, u, zero_pow (by omega : 2 ≠ 0), mul_zero] using
      ht.const_mul (64*K^2*D^2*(2:ℝ)^d)
  have hlim2 : Tendsto (fun R : ℝ =>
      ⨍ x in ball 0 (2*R), euclideanSq (φ.grad a x - ψ.grad a x)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hlim
    · exact Filter.Eventually.of_forall fun R => integral_nonneg fun x =>
        EinsteinRelation.euclideanSq_nonneg_coords _
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
      have h2 : 0 < 2*R := by positivity
      have h4 : 0 < 4*R := by positivity
      let V := fun r : ℝ => volume.real (ball (0 : Vec d) r)
      have hV2 : 0 < V (2*R) := Correctors.ball_volume_pos_finite d _ h2
      have hV4 : 0 < V (4*R) := Correctors.ball_volume_pos_finite d _ h4
      have hVr : V (4*R) = (2:ℝ)^d * V (2*R) := by
        dsimp only [V]
        rw [Correctors.paired_ball_volume_scale h4, Correctors.paired_ball_volume_scale h2]
        rw [← mul_assoc, ← mul_pow]
        congr 2
        ring
      have hS : 0 ≤ S (4*R) := integral_nonneg fun x => sq_nonneg _
      have hAvg : S (4*R) = (V (4*R))⁻¹ *
          ∫ x in ball 0 (4*R), (u x - ⨍ y in ball 0 (4*R), u y)^2 := by
        change (⨍ x in ball 0 (4*R), (u x - ⨍ y in ball 0 (4*R), u y)^2) = _
        rw [average_eq]
        simp only [V, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      have hInt : (∫ x in ball 0 (4*R), (u x - ⨍ y in ball 0 (4*R), u y)^2) =
          V (4*R) * S (4*R) := by
        rw [hAvg, ← mul_assoc, mul_inv_cancel₀ hV4.ne', one_mul]
      have hb := hE R hR (⨍ y in ball 0 (4*R), u y)
      have hb' : (∫ x in ball 0 (2*R), euclideanSq (φ.grad a x - ψ.grad a x)) ≤
          4*K^2*(D/R)^2 * ∫ x in ball 0 (4*R), (u x - ⨍ y in ball 0 (4*R), u y)^2 := by
        simpa only [originBall, ball, sub_zero, u] using hb
      rw [average_eq]
      simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      change (V (2*R))⁻¹ * _ ≤ _
      calc
        _ ≤ (V (2*R))⁻¹ * (4*K^2*(D/R)^2 *
            ∫ x in ball 0 (4*R), (u x - ⨍ y in ball 0 (4*R), u y)^2) :=
          mul_le_mul_of_nonneg_left hb' (inv_nonneg.mpr hV2.le)
        _ = _ := by
          rw [hInt, hVr, mul_pow, Real.sq_sqrt hS]
          field_simp [hR.ne', hV2.ne']
          <;> ring
  have ht := hlim2.comp ((tendsto_const_mul_atTop_of_pos
    (by norm_num : (0:ℝ)<1/2)).mpr tendsto_id)
  simpa only [Function.comp_def, id_eq, ← mul_assoc, show (2:ℝ)*(1/2)=1 by norm_num,
    one_mul] using ht

/-- Clipping a nonnegative integrable function at one bounds its average
without introducing a moment assumption. -/
theorem average_min_one_bounds {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    0 ≤ (⨍ x, min 1 (f x) ∂μ) ∧
      (⨍ x, min 1 (f x) ∂μ) ≤ 1 ∧
      (⨍ x, min 1 (f x) ∂μ) ≤ ⨍ x, f x ∂μ := by
  have hm : Integrable (fun x => min 1 (f x)) μ := (integrable_const (1:ℝ)).inf hf
  refine ⟨average_nonneg (fun x => le_min (by norm_num) (hf0 x)), ?_, ?_⟩
  · by_cases hμ : μ = 0
    · simp [hμ]
    letI : NeZero μ := ⟨hμ⟩
    calc
      _ ≤ ⨍ _x, (1 : ℝ) ∂μ := integral_mono
        (integrable_average.mpr hm) (integrable_average.mpr (integrable_const 1))
        (fun x => min_le_left _ _)
      _ = 1 := average_const μ 1
  · exact integral_mono (integrable_average.mpr hm) (integrable_average.mpr hf)
      (fun x => min_le_right _ _)

/-- The bounded truncation of source-gradient difference energy has vanishing
large-ball mean, almost surely, even without an environment energy moment. -/
theorem sourceCorrector_difference_truncated_mean_tendsto_zero {d : ℕ} {K : ℝ}
    (hK : 0 < K) {P : Measure (Coefficient d K)} {e : Vec d}
    (φ ψ : SourceCorrector P e) :
    ∀ᵐ a ∂P, Tendsto (fun R : ℝ =>
      ⨍ x in ball 0 R, min 1 (euclideanSq (φ.grad a x - ψ.grad a x)))
      atTop (𝓝 0) := by
  filter_upwards [sourceCorrector_difference_mean_energy_tendsto_zero hK φ ψ,
    φ.locally_square_integrable, ψ.locally_square_integrable] with a ha hφ hψ
  apply squeeze_zero' _ _ ha
  · exact Filter.Eventually.of_forall fun R => average_nonneg fun x =>
      le_min (by norm_num) (EinsteinRelation.euclideanSq_nonneg_coords _)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
      simpa using (ENNReal.toReal_pos_iff.mp
        (Correctors.ball_volume_pos_finite d R hR)).2⟩
    have hG := memLp_pi_iff.mp ((hφ R hR).2.sub (hψ R hR).2)
    have hE : Integrable (fun x => euclideanSq (φ.grad a x - ψ.grad a x))
        (volume.restrict (ball 0 R)) := by
      unfold euclideanSq dot
      exact integrable_finset_sum Finset.univ fun j _ => by
        simpa only [sq, Pi.sub_apply] using (hG j).integrable_sq
    exact (average_min_one_bounds hE
      (fun x => EinsteinRelation.euclideanSq_nonneg_coords _)).2.2

/-- Bounded source-gradient energy averages also vanish in expectation.
Bounded convergence supplies the stochastic integrability internally. -/
theorem sourceCorrector_difference_expected_truncated_mean_tendsto_zero
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P] {e : Vec d}
    (φ ψ : SourceCorrector P e) :
    Tendsto (fun R : ℝ => ∫ a,
      (⨍ x in ball 0 R, min 1 (euclideanSq (φ.grad a x - ψ.grad a x))) ∂P)
      atTop (𝓝 0) := by
  let H := fun a x => min 1 (euclideanSq (φ.grad a x - ψ.grad a x))
  have hH : Measurable (fun p : Coefficient d K × Vec d => H p.1 p.2) := by
    have hm := φ.measurable_grad.sub ψ.measurable_grad
    dsimp only [H]
    unfold euclideanSq dot
    exact measurable_const.min (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j |>.comp hm).mul (measurable_pi_apply j |>.comp hm))
  have hbound : ∀ (R : ℝ), 0 < R → ∀ a,
      0 ≤ (⨍ x in ball 0 R, H a x) ∧ (⨍ x in ball 0 R, H a x) ≤ 1 := by
    intro R hR a
    letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
      simpa using (ENNReal.toReal_pos_iff.mp
        (Correctors.ball_volume_pos_finite d R hR)).2⟩
    have hm : AEStronglyMeasurable (H a)
        (volume.restrict (ball 0 R)) :=
      (hH.comp ((measurable_const (a := a)).prodMk measurable_id)).aestronglyMeasurable
    have hInt : Integrable (H a) (volume.restrict (ball 0 R)) :=
      (integrable_const (1:ℝ)).mono' hm (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (by norm_num) (EinsteinRelation.euclideanSq_nonneg_coords _))
    refine ⟨average_nonneg (fun x => le_min (by norm_num)
      (EinsteinRelation.euclideanSq_nonneg_coords _)), ?_⟩
    have hp := Correctors.ball_volume_pos_finite d R hR
    calc
      _ ≤ ⨍ _x in ball (0 : Vec d) R, (1:ℝ) :=
        integral_mono (integrable_average.mpr hInt)
          (integrable_average.mpr (integrable_const 1)) (fun x => min_le_left _ _)
      _ = 1 := setAverage_const (ENNReal.toReal_pos_iff.mp hp).1.ne'
        (ENNReal.toReal_pos_iff.mp hp).2.ne 1
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := P)
    (F := fun R a => ⨍ x in ball 0 R, H a x) (f := fun _ => (0:ℝ)) (fun _ => (1:ℝ))
    (Filter.Eventually.of_forall fun R => by
      simp_rw [average_eq]
      have hm : StronglyMeasurable (fun a => ∫ x in ball 0 R, H a x) :=
        hH.stronglyMeasurable.integral_prod_right'
      exact (hm.const_smul (((volume.restrict (ball (0 : Vec d) R)).real Set.univ)⁻¹)).aestronglyMeasurable)
    (by
      filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
      exact Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hbound R hR a).1]
        exact (hbound R hR a).2)
    (integrable_const 1) (sourceCorrector_difference_truncated_mean_tendsto_zero hK φ ψ)
  simpa only [integral_zero] using ht

/-- Lattice stationarity of source gradients makes the expected bounded
energy truncation lattice periodic, without assuming an energy moment. -/
theorem sourceCorrector_difference_expected_truncation_lattice_periodic
    {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} [SFinite P]
    (hP : ∀ z : LatticeIndex d,
      MeasurePreserving (translateCoefficient (latticeShift z)) P P)
    {e : Vec d} (φ ψ : SourceCorrector P e) (z : LatticeIndex d) :
    (fun x => ∫ a, min 1 (euclideanSq
      (φ.grad a (x + latticeShift z) - ψ.grad a (x + latticeShift z))) ∂P) =ᵐ[volume]
    (fun x => ∫ a, min 1 (euclideanSq (φ.grad a x - ψ.grad a x)) ∂P) := by
  let H := fun a x => min 1 (euclideanSq (φ.grad a x - ψ.grad a x))
  have hm : Measurable (fun p : Coefficient d K × Vec d => H p.1 p.2) := by
    have hg := φ.measurable_grad.sub ψ.measurable_grad
    dsimp only [H]
    unfold euclideanSq dot
    exact measurable_const.min (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j |>.comp hg).mul (measurable_pi_apply j |>.comp hg))
  have hs : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)),
      H a (x + latticeShift z) = H (translateCoefficient (latticeShift z) a) x := by
    filter_upwards [φ.stationary z, ψ.stationary z] with a hφ hψ
    filter_upwards [hφ, hψ] with x hφx hψx
    simp only [H, hφx, hψx]
  have hm₁ := hm.comp (measurable_fst.prodMk
    (measurable_snd.add (measurable_const (a := latticeShift z))))
  have hm₂ := hm.comp (((hP z).measurable.comp measurable_fst).prodMk measurable_snd)
  have heq := measurableSet_eq_fun hm₁ hm₂
  filter_upwards [(Measure.ae_ae_comm heq).mp hs] with x hx
  change (∫ a, H a (x + latticeShift z) ∂P) = ∫ a, H a x ∂P
  calc
    _ = ∫ a, H (translateCoefficient (latticeShift z) a) x ∂P := integral_congr_ae hx
    _ = _ := by
      have hfx := hm.comp (measurable_id.prodMk (measurable_const (a := x)))
      have hi := integral_map (μ := P) (hP z).measurable.aemeasurable
        hfx.aestronglyMeasurable
      rw [(hP z).map_eq] at hi
      exact hi.symm

/-- Spatial averaging and expectation commute for the bounded source-gradient
energy truncation. The finite-ball product integral is derived internally. -/
theorem sourceCorrector_difference_truncation_average_fubini
    {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} [IsProbabilityMeasure P]
    {e : Vec d} (φ ψ : SourceCorrector P e) {R : ℝ} (hR : 0 < R) :
    (∫ a, (⨍ x in ball 0 R,
      min 1 (euclideanSq (φ.grad a x - ψ.grad a x))) ∂P) =
    ⨍ x in ball 0 R, ∫ a, min 1 (euclideanSq (φ.grad a x - ψ.grad a x)) ∂P := by
  let H := fun a x => min 1 (euclideanSq (φ.grad a x - ψ.grad a x))
  have hm : Measurable (fun p : Coefficient d K × Vec d => H p.1 p.2) := by
    have hg := φ.measurable_grad.sub ψ.measurable_grad
    dsimp only [H]
    unfold euclideanSq dot
    exact measurable_const.min (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j |>.comp hg).mul (measurable_pi_apply j |>.comp hg))
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
    simpa using (ENNReal.toReal_pos_iff.mp
      (Correctors.ball_volume_pos_finite d R hR)).2⟩
  have hInt : Integrable (fun p : Coefficient d K × Vec d => H p.1 p.2)
      (P.prod (volume.restrict (ball 0 R))) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact min_le_left _ _
        · exact le_min (by norm_num) (EinsteinRelation.euclideanSq_nonneg_coords _))
  change (∫ a, (⨍ x in ball 0 R, H a x) ∂P) =
    ⨍ x in ball 0 R, ∫ a, H a x ∂P
  simp_rw [average_eq, smul_eq_mul]
  rw [integral_const_mul]
  exact congrArg (fun t => ((volume.restrict (ball (0 : Vec d) R)).real Set.univ)⁻¹ * t)
    (integral_integral_swap hInt)

/-- Half-open unit cells indexed by the integer lattice. -/
def integerUnitCell {d : ℕ} (z : LatticeIndex d) : Set (Vec d) :=
  Set.pi Set.univ (fun i => Set.Ico (z i : ℝ) ((z i : ℝ) + 1))

theorem integerUnitCell_measurableSet {d : ℕ} (z : LatticeIndex d) :
    MeasurableSet (integerUnitCell z) :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ico)

/-- Every integer cell is the translate of the cell based at zero. -/
theorem integerUnitCell_eq_image {d : ℕ} (z : LatticeIndex d) :
    integerUnitCell z = (fun x : Vec d => x + latticeShift z) '' integerUnitCell 0 := by
  ext x
  constructor
  · intro hx
    refine ⟨x - latticeShift z, ?_, sub_add_cancel _ _⟩
    intro i _
    have hi := hx i (Set.mem_univ i)
    simp only [Set.mem_Ico] at hi
    simp only [Set.mem_Ico, Pi.sub_apply, latticeShift, Pi.zero_apply, Int.cast_zero]
    constructor <;> linarith
  · rintro ⟨y, hy, rfl⟩ i _
    have hi := hy i (Set.mem_univ i)
    change (z i : ℝ) ≤ y i + (z i : ℝ) ∧
      y i + (z i : ℝ) < (z i : ℝ) + 1
    simp only [Set.mem_Ico, Pi.zero_apply, Int.cast_zero] at hi
    constructor <;> linarith

/-- Distinct integer cells are disjoint, including their half-open boundaries. -/
theorem integerUnitCell_pairwiseDisjoint (d : ℕ) :
    Pairwise (fun z w : LatticeIndex d => Disjoint (integerUnitCell z) (integerUnitCell w)) := by
  intro z w hzw
  apply Set.disjoint_left.mpr
  intro x hz hw
  apply hzw
  funext i
  have hz' := hz i (Set.mem_univ i)
  have hw' := hw i (Set.mem_univ i)
  exact (Int.floor_eq_iff.mpr hz').symm.trans (Int.floor_eq_iff.mpr hw')

/-- The positive n-by-...-by-n collection of cells lies in a Euclidean ball. -/
theorem integerUnitCell_finite_packing_subset_ball {d n : ℕ} (hn : 0 < n)
    (z : Fin d → Fin n) :
    integerUnitCell (fun i => (z i).val) ⊆ ball 0 (((d:ℝ)+1)*n) := by
  intro x hx
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg _
  have hc : ∀ i, |x i| ≤ (n:ℝ) := by
    intro i
    have hi := hx i (Set.mem_univ i)
    have hz : (0:ℝ) ≤ (z i).val := Nat.cast_nonneg _
    have hz' : ((z i).val:ℝ) + 1 ≤ n := by exact_mod_cast (z i).isLt
    rw [abs_of_nonneg (hz.trans hi.1)]
    exact hi.2.le.trans hz'
  change euclideanNorm (x - 0) < _
  rw [sub_zero]
  calc
    _ ≤ ∑ i, |x i| := EinsteinRelation.euclideanNorm_le_sum_abs x
    _ ≤ ∑ _i : Fin d, (n:ℝ) := Finset.sum_le_sum (fun i _ => hc i)
    _ = (d:ℝ)*n := by simp
    _ < ((d:ℝ)+1)*n := by nlinarith

/-- Finite cell packing transfers the common periodic cell integral into a
large Euclidean ball, without a stochastic moment assumption. -/
theorem lattice_periodic_cell_integral_le_ball_integral {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hp : ∀ z : LatticeIndex d, (fun x => f (x + latticeShift z)) =ᵐ[volume] f)
    {n : ℕ} (hn : 0 < n) :
    (n:ℝ)^d * (∫ x in integerUnitCell (0 : LatticeIndex d), f x) ≤
      ∫ x in ball 0 (((d:ℝ)+1)*n), f x := by
  classical
  let C := fun z : Fin d → Fin n => integerUnitCell (fun i => (z i).val)
  let R : ℝ := ((d:ℝ)+1)*n
  have hR : 0 < R := mul_pos (by positivity) (by exact_mod_cast hn)
  letI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) := ⟨by
    simpa using (ENNReal.toReal_pos_iff.mp
      (Correctors.ball_volume_pos_finite d R hR)).2⟩
  have hInt : IntegrableOn f (ball 0 R) :=
    (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
        exact h1 x)
  have hsub : ∀ z, C z ⊆ ball 0 R := integerUnitCell_finite_packing_subset_ball hn
  have hC : ∀ z, ∫ x in C z, f x =
      ∫ x in integerUnitCell (0 : LatticeIndex d), f x := by
    intro z
    rw [show C z = integerUnitCell (fun i => (z i).val) from rfl,
      integerUnitCell_eq_image]
    rw [(measurePreserving_add_right (volume : Measure (Vec d))
      (latticeShift (fun i => (z i).val))).setIntegral_image_emb
      (Homeomorph.addRight _).measurableEmbedding]
    exact integral_congr_ae (ae_restrict_of_ae (hp _))
  have hdis : Pairwise (fun z w => Disjoint (C z) (C w)) := by
    intro z w hzw
    apply integerUnitCell_pairwiseDisjoint d
    intro heq
    apply hzw
    funext i
    apply Fin.ext
    have hi := congrFun heq i
    exact_mod_cast hi
  calc
    _ = ∑ z : Fin d → Fin n, ∫ x in C z, f x := by simp only [hC,
      Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_pow]
    _ = ∫ x in ⋃ z : Fin d → Fin n, C z, f x :=
      (integral_iUnion_fintype (fun z => integerUnitCell_measurableSet _)
        hdis (fun z => hInt.mono_set (hsub z))).symm
    _ ≤ _ := setIntegral_mono_set hInt
      (Filter.Eventually.of_forall h0) (Filter.Eventually.of_forall (by
        intro x hx
        obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hx
        exact hsub z hz))


/-- Normalize the packing inequality by the number of cells. -/
theorem lattice_periodic_cell_integral_le_ball_average {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hp : ∀ z : LatticeIndex d, (fun x => f (x + latticeShift z)) =ᵐ[volume] f)
    {n : ℕ} (hn : 0 < n) :
    (∫ x in integerUnitCell (0 : LatticeIndex d), f x) ≤
      ((d:ℝ)+1)^d * volume.real (ball (0 : Vec d) 1) *
        (⨍ x in ball 0 (((d:ℝ)+1)*n), f x) := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hR : 0 < ((d:ℝ)+1)*n := mul_pos (by positivity) hn'
  have hv := Correctors.ball_volume_pos_finite d (((d:ℝ)+1)*n) hR
  apply (mul_le_mul_iff_right₀ (pow_pos hn' d)).mp
  calc
    _ ≤ ∫ x in ball 0 (((d:ℝ)+1)*n), f x :=
      lattice_periodic_cell_integral_le_ball_integral hf h0 h1 hp hn
    _ = volume.real (ball (0 : Vec d) (((d:ℝ)+1)*n)) *
        (⨍ x in ball 0 (((d:ℝ)+1)*n), f x) := by
      rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul,
        ← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    _ = _ := by rw [Correctors.paired_ball_volume_scale hR, mul_pow]; ring

/-- A bounded nonnegative lattice-periodic field with vanishing large-ball
averages has zero integral on its fundamental cell. -/
theorem lattice_periodic_cell_integral_eq_zero {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hp : ∀ z : LatticeIndex d, (fun x => f (x + latticeShift z)) =ᵐ[volume] f)
    (ht : Tendsto (fun R : ℝ => ⨍ x in ball 0 R, f x) atTop (𝓝 0)) :
    (∫ x in integerUnitCell (0 : LatticeIndex d), f x) = 0 := by
  have hr : Tendsto (fun n : ℕ => ((d:ℝ)+1)*(n:ℝ)) atTop atTop :=
    tendsto_const_mul_atTop_of_pos (by positivity) |>.mpr tendsto_natCast_atTop_atTop
  have hlim := (ht.comp hr).const_mul (((d:ℝ)+1)^d *
    volume.real (ball (0 : Vec d) 1))
  have hle : (∫ x in integerUnitCell (0 : LatticeIndex d), f x) ≤ 0 := by
    apply ge_of_tendsto (by simpa using hlim)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
    exact lattice_periodic_cell_integral_le_ball_average hf h0 h1 hp hn
  exact le_antisymm hle (integral_nonneg h0)

/-- The half-open integer cells cover all of coordinate space. -/
theorem integerUnitCell_iUnion (d : ℕ) :
    (⋃ z : LatticeIndex d, integerUnitCell z) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply Set.mem_iUnion.mpr
  refine ⟨fun i => ⌊x i⌋, ?_⟩
  intro i _
  exact Int.floor_eq_iff.mp rfl


/-- A vanishing mean of a bounded periodic nonnegative field forces the field
itself to vanish almost everywhere. -/
theorem lattice_periodic_eq_zero_ae {d : ℕ} {f : Vec d → ℝ}
    (hf : Measurable f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1)
    (hp : ∀ z : LatticeIndex d, (fun x => f (x + latticeShift z)) =ᵐ[volume] f)
    (ht : Tendsto (fun R : ℝ => ⨍ x in ball 0 R, f x) atTop (𝓝 0)) :
    f =ᵐ[volume] 0 := by
  have hI := lattice_periodic_cell_integral_eq_zero hf h0 h1 hp ht
  have hcell : ∀ z : LatticeIndex d, ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ integerUnitCell z → f x = 0 := by
    intro z
    have hvol : volume (integerUnitCell z) = 1 := by
      simp [integerUnitCell, Real.volume_pi_Ico]
    letI : IsFiniteMeasure (volume.restrict (integerUnitCell z)) := ⟨by simp [hvol]⟩
    have hInt : IntegrableOn f (integerUnitCell z) :=
      (integrable_const (1:ℝ)).mono' hf.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x)
    have hz : (∫ x in integerUnitCell z, f x) = 0 := by
      rw [integerUnitCell_eq_image,
        (measurePreserving_add_right (volume : Measure (Vec d))
          (latticeShift z)).setIntegral_image_emb
          (Homeomorph.addRight _).measurableEmbedding]
      exact (integral_congr_ae (ae_restrict_of_ae (hp z))).trans hI
    exact (ae_restrict_iff' (integerUnitCell_measurableSet z)).mp
      ((integral_eq_zero_iff_of_nonneg h0 hInt).mp hz)
  filter_upwards [ae_all_iff.mpr hcell] with x hx
  have hxuniv : x ∈ (⋃ z : LatticeIndex d, integerUnitCell z) := by
    rw [integerUnitCell_iUnion]; exact Set.mem_univ x
  obtain ⟨z, hz⟩ := Set.mem_iUnion.mp hxuniv
  exact hx z hz

/-- Stationary sublinear source correctors of the same slope have identical
actual gradients. All stochastic integrability comes from bounded truncation. -/
theorem sourceCorrector_grad_ae_unique
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    {P : Measure (Coefficient d K)} [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d,
      MeasurePreserving (translateCoefficient (latticeShift z)) P P)
    {e : Vec d} (φ ψ : SourceCorrector P e) :
    ∀ᵐ a ∂P, φ.grad a =ᵐ[volume] ψ.grad a := by
  let H := fun a x => min 1 (euclideanSq (φ.grad a x - ψ.grad a x))
  have hm : Measurable (fun p : Coefficient d K × Vec d => H p.1 p.2) := by
    have hg := φ.measurable_grad.sub ψ.measurable_grad
    dsimp only [H]
    unfold euclideanSq dot
    exact measurable_const.min (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j |>.comp hg).mul (measurable_pi_apply j |>.comp hg))
  have h0 : ∀ a x, 0 ≤ H a x := fun a x =>
    le_min (by norm_num) (EinsteinRelation.euclideanSq_nonneg_coords _)
  have h1 : ∀ a x, H a x ≤ 1 := fun _ _ => min_le_left _ _
  have hInt : ∀ x, Integrable (fun a => H a x) P := fun x =>
    (integrable_const (1:ℝ)).mono'
      (hm.comp (measurable_id.prodMk (measurable_const (a := x)))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 a x)]; exact h1 a x)
  have hf : Measurable (fun x => ∫ a, H a x ∂P) :=
    hm.stronglyMeasurable.integral_prod_left'.measurable
  have ht : Tendsto (fun R : ℝ => ⨍ x in ball 0 R, ∫ a, H a x ∂P)
      atTop (𝓝 0) := by
    apply (sourceCorrector_difference_expected_truncated_mean_tendsto_zero hK φ ψ).congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    exact sourceCorrector_difference_truncation_average_fubini φ ψ hR
  have hf0 := lattice_periodic_eq_zero_ae hf (fun x => integral_nonneg (fun a => h0 a x))
    (fun x => by
      calc
        _ ≤ ∫ _a, (1:ℝ) ∂P := integral_mono (hInt x) (integrable_const 1) (fun a => h1 a x)
        _ = 1 := by simp)
    (sourceCorrector_difference_expected_truncation_lattice_periodic hP φ ψ) ht
  have hz : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ᵐ a ∂P, H a x = 0 := by
    filter_upwards [hf0] with x hx
    exact (integral_eq_zero_iff_of_nonneg (fun a => h0 a x) (hInt x)).mp hx
  have hmeq : MeasurableSet {p : Coefficient d K × Vec d | H p.1 p.2 = 0} :=
    measurableSet_eq_fun hm measurable_const
  have hza : ∀ᵐ a ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), H a x = 0 :=
    (Measure.ae_ae_comm hmeq).mpr hz
  filter_upwards [hza] with a ha
  filter_upwards [ha] with x hx
  have hs : euclideanSq (φ.grad a x - ψ.grad a x) = 0 := by
    by_contra hs
    have hpos : 0 < min 1 (euclideanSq (φ.grad a x - ψ.grad a x)) :=
      lt_min (by norm_num) (lt_of_le_of_ne
        (EinsteinRelation.euclideanSq_nonneg_coords _) (Ne.symm hs))
    change min 1 (euclideanSq (φ.grad a x - ψ.grad a x)) = 0 at hx
    linarith
  funext j
  have hj : (φ.grad a x j - ψ.grad a x j)^2 ≤
      euclideanSq (φ.grad a x - ψ.grad a x) := by
    unfold euclideanSq dot
    simpa only [sq, Pi.sub_apply] using
      (Finset.single_le_sum (fun i _ => mul_self_nonneg ((φ.grad a x - ψ.grad a x) i))
        (Finset.mem_univ j))
  nlinarith [sq_nonneg (φ.grad a x j - ψ.grad a x j)]


open EinsteinRelation.Correctors EinsteinRelation.ReductionImageV3

/-- Every characterized source corrector at the actual coefficient law has
the canonical gradient, including sources selected by the negative norm input. -/
theorem sourceCorrector_canonical_grad_identification
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ψ : SourceCorrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (correctorUnitVector i).ofLp +
        ψ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp := by
  obtain ⟨φ, hid⟩ := C3SublinearPair.exists_unitCorrector_global_identification Q i
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) :=
    (lawHypotheses_actualCoefficientLaw Q).1
  have hP : ∀ z : LatticeIndex d,
      MeasurePreserving (translateCoefficient (latticeShift z))
        (actualCoefficientLaw Q) (actualCoefficientLaw Q) := fun z =>
    ⟨measurable_translateCoefficient _, (lawHypotheses_actualCoefficientLaw Q).2.1 z⟩
  have hu := sourceCorrector_grad_ae_unique
    (zero_lt_one.trans (Correctors.one_lt_AKMUpperEllipticity Q.ellipticity_parameter))
    hP ψ φ.toSourceCorrector
  have hp := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hu
  filter_upwards [hid, hp] with ω hω hψ
  filter_upwards [hω, hψ] with y hy hgrad
  exact (congrArg (fun v : Vec d => (correctorUnitVector i).ofLp + v) hgrad).trans hy

/-- The strict half-coordinate direction used by the source estimate has
exactly half the canonical affine gradient, for every characterized source. -/
theorem sourceCorrector_half_canonical_grad_identification
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ψ : SourceCorrector (actualCoefficientLaw Q) (halfDirection i)) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i +
        ψ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp := by
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification_from_pde Q i
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) :=
    (lawHypotheses_actualCoefficientLaw Q).1
  have hP : ∀ z : LatticeIndex d,
      MeasurePreserving (translateCoefficient (latticeShift z))
        (actualCoefficientLaw Q) (actualCoefficientLaw Q) := fun z =>
    ⟨measurable_translateCoefficient _, (lawHypotheses_actualCoefficientLaw Q).2.1 z⟩
  have hu := sourceCorrector_grad_ae_unique
    (zero_lt_one.trans (Correctors.one_lt_AKMUpperEllipticity Q.ellipticity_parameter))
    hP ψ φ.toSourceCorrector
  have hp := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hu
  filter_upwards [hid, hp] with ω hω hψ
  filter_upwards [hω, hψ] with y hy hgrad
  exact (congrArg (fun v : Vec d => (2 : ℝ) • (halfDirection i + v)) hgrad).trans hy

/-- Literal source commutator identification on the actual physical law.
The factor two comes from the strict half-direction, and the ellipticity
scale is retained. The matrix contraction keeps every anisotropic entry. -/
theorem sourceCommutator_canonical_identification
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (S : SourceObjects (actualCoefficientLaw Q)) (j i : Fin d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      2 * (((project (r₀ := r₀) Q.ellipticity_parameter ω) y).mulVec
          (halfDirection i + (S.corrector (halfDirection i)).grad
            (project (r₀ := r₀) Q.ellipticity_parameter ω) y) -
        S.homogenized.mulVec
          (halfDirection i + (S.corrector (halfDirection i)).grad
            (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) j =
      ellipticityScale L * commutatorObservation Q j i
        (translate (r₀ • y) (reduce ω.1)) := by
  filter_upwards [sourceCorrector_half_canonical_grad_identification Q i
    (S.corrector (halfDirection i))] with ω hω
  filter_upwards [hω] with y hy
  have hv (k : Fin d) := congrFun hy k
  have ha : (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
      ellipticityScale L • (translate (r₀ • y) (reduce ω.1)).1 0 := by
    change ellipticityScale L • reducedCoefficient ω.1 (r₀ • y) = _
    simp only [translate_matrix, add_zero, reduce]
    rfl
  rw [coarseSource_homogenized_eq Q S, ha]
  simp only [commutatorObservation, Matrix.mulVec, dotProduct, Pi.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Pi.add_apply, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk := hv k
  change 2 * (halfDirection i k + (S.corrector (halfDirection i)).grad
    (project (r₀ := r₀) Q.ellipticity_parameter ω) y k) =
    unitVector i k + correctorGradient Q i
      (translate (r₀ • y) (reduce ω.1)) k at hk
  linear_combination (ellipticityScale L *
    ((translate (r₀ • y) (reduce ω.1)).1 0 j k - homogenizedCoefficient Q j k)) * hk

/-- The weak equations supply compact-test integrability and allow the
separate centered-flux and gradient pairings to be combined. -/
theorem sourceCorrector_compact_commutator_integral
    {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (ψ : SourceCorrector P e) (H : Mat d) (j : Fin d)
    {w : Vec d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w) :
    ∀ᵐ a ∂P,
      (∫ x, ((a x).mulVec (e + ψ.grad a x) - H.mulVec e) j * w x) -
        ∑ k, H j k * (∫ x, ψ.grad a x k * w x) =
      ∫ x, ((a x).mulVec (e + ψ.grad a x) -
        H.mulVec (e + ψ.grad a x)) j * w x := by
  filter_upwards [ψ.weak_gradient, ψ.harmonic] with a hg hh
  have hgrad (k : Fin d) : Integrable (fun x => ψ.grad a x k * w x) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrableOn_univ.mp (hg k).2.1).integrable_smul_right_of_hasCompactSupport
        hw hwc
  have hflux : Integrable (fun x => (a x).mulVec (e + ψ.grad a x) j * w x) := by
    simpa only [smul_eq_mul] using
      (locallyIntegrableOn_univ.mp (hh.1 j)).integrable_smul_right_of_hasCompactSupport
        hw hwc
  have hwInt : Integrable w (volume : Measure (Vec d)) :=
    hw.integrable_of_hasCompactSupport hwc
  have hc : Integrable (fun x => ((a x).mulVec (e + ψ.grad a x) - H.mulVec e) j * w x) := by
    simpa only [Pi.sub_apply, Pi.sub_def, sub_mul] using hflux.sub (hwInt.const_mul (H.mulVec e j))
  have hs : ∀ k ∈ (Finset.univ : Finset (Fin d)),
      Integrable (fun x => H j k * (ψ.grad a x k * w x)) :=
    fun k _ => (hgrad k).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hs, ← integral_sub hc (integrable_finsetSum _ hs)]
  apply integral_congr_ae
  filter_upwards [] with x
  have hsx : (∑ k, H j k * (ψ.grad a x k * w x)) =
      H.mulVec (ψ.grad a x) j * w x := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  rw [hsx, Matrix.mulVec_add H]
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- The literal compact physical source pairing equals the canonical
commutator integral. Both factors from normalization remain explicit. -/
theorem physicalSourceCommutatorPairing_canonical
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (S : SourceObjects (actualCoefficientLaw Q)) (j i : Fin d) (R c : ℝ)
    (χ f : Vec d → ℝ)
    (hw : Continuous (fun y => χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)))
    (hwc : HasCompactSupport (fun y => χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      2 * physicalSourceCommutatorPairing S (halfDirection i) R c j χ f
        (project (r₀ := r₀) Q.ellipticity_parameter ω) =
      ellipticityScale L * R ^ (-(d : ℝ) / 2) *
        ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
          (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)) := by
  have hi := sourceCorrector_compact_commutator_integral
    (S.corrector (halfDirection i)) S.homogenized j hw hwc
  have hp := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae hi
  filter_upwards [hp, sourceCommutator_canonical_identification Q S j i] with ω hω hxi
  unfold physicalSourceCommutatorPairing
  rw [hω]
  have hInt : 2 * (∫ y, (((project (r₀ := r₀) Q.ellipticity_parameter ω) y).mulVec
        (halfDirection i + (S.corrector (halfDirection i)).grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) -
      S.homogenized.mulVec
        (halfDirection i + (S.corrector (halfDirection i)).grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) j *
      (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) =
      ellipticityScale L * (∫ y,
        commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
          (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hxi] with y hy
    rw [← mul_assoc, hy, mul_assoc]
  linear_combination R ^ (-(d : ℝ) / 2) * hInt

/-- L² membership and its exact norm transfer from the source coefficient
law to the canonical compact commutator on the physical reference law. -/
theorem canonical_commutator_compact_L2_transfer
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (S : SourceObjects (actualCoefficientLaw Q)) (j i : Fin d) (R c : ℝ)
    (χ f : Vec d → ℝ)
    (hw : Continuous (fun y => χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)))
    (hwc : HasCompactSupport (fun y => χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)))
    (hp : MemLp (physicalSourceCommutatorPairing S (halfDirection i) R c j χ f)
      2 (actualCoefficientLaw Q)) :
    ∃ hq : MemLp (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
        ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
          (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) 2 (physicalReferenceLaw Q),
      ‖hq.toLp (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
        ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
          (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)))‖ =
      (2 / ellipticityScale L) *
        ‖hp.toLp (physicalSourceCommutatorPairing S (halfDirection i) R c j χ f)‖ := by
  let f₀ := physicalSourceCommutatorPairing S (halfDirection i) R c j χ f
  let g := fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
    ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
      (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))
  let π := project (d := d) (r₀ := r₀) Q.ellipticity_parameter
  have hπ : MeasurePreserving π (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
    measurePreserving_akmProject Q
  have hB := (ellipticityScale_pos Q.ellipticity_parameter).ne'
  have heq : (2 / ellipticityScale L) • (f₀ ∘ π) =ᵐ[physicalReferenceLaw Q] g := by
    filter_upwards [physicalSourceCommutatorPairing_canonical Q S j i R c χ f hw hwc]
      with ω hω
    change (2 / ellipticityScale L) * f₀ (π ω) = g ω
    have hω' : 2 * f₀ (π ω) = ellipticityScale L * g ω := by
      simpa only [f₀, π, g, mul_assoc] using hω
    calc
      (2 / ellipticityScale L) * f₀ (π ω) = (2 * f₀ (π ω)) / ellipticityScale L := by ring
      _ = g ω := (div_eq_iff hB).2 (hω'.trans (mul_comm _ _))
  have hs := (hp.comp_measurePreserving hπ).const_smul (2 / ellipticityScale L)
  have hq : MemLp g 2 (physicalReferenceLaw Q) := hs.ae_eq heq
  refine ⟨hq, ?_⟩
  change ‖hq.toLp g‖ = (2 / ellipticityScale L) * ‖hp.toLp f₀‖
  rw [hq.toLp_congr hs heq.symm,
    MemLp.toLp_const_smul _ (hp.comp_measurePreserving hπ)]
  rw [← Lp.toLp_compMeasurePreserving hp hπ, norm_smul, Lp.norm_compMeasurePreserving,
    Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) (ellipticityScale_pos Q.ellipticity_parameter))]

/-- The compact Schwartz estimate for the actual canonical commutator.
The constant is chosen before the law; the same Schwartz order is retained. -/
theorem canonical_commutator_schwartz_cutoff_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 ≤ a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∀ N : ℕ, m ≤ N → ∀ (R : ℝ), 1 ≤ R → ∀ (j i : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
      ∀ c : ℝ, 4 ≤ c →
        ∃ hq : MemLp (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
            ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
              (χ ((R * c)⁻¹ • y) * ℓ (F (R⁻¹ • y)))) 2 (physicalReferenceLaw Q),
          ‖hq.toLp (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
            ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
              (χ ((R * c)⁻¹ • y) * ℓ (F (R⁻¹ • y))))‖ ≤
            C * c ^ (m + d) * schwartzTestNorm N F / (1 + c * a) ^ N := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, hC, h⟩ := physical_source_schwartz_cutoff_L2 d hd L hL m hm hχ ha hχa
  have hα : 0 < 2 / ellipticityScale L := div_pos (by norm_num) (ellipticityScale_pos hL)
  refine ⟨(2 / ellipticityScale L) * C, mul_pos hα hC, ?_⟩
  intro r₀ Q
  obtain ⟨S, hS⟩ := h r₀ Q
  intro N hN R hR j i F ℓ hℓ c hc
  obtain ⟨hp, hb⟩ := hS N hN (halfDirection i) (halfDirection_mem_ball i)
    R hR j F ℓ hℓ c hc
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hc0 : 0 < c := by linarith
  have hw : Continuous (fun y => χ ((R * c)⁻¹ • y) * ℓ (F (R⁻¹ • y))) :=
    by
      have hχc : Continuous χ := hχ.1.continuous
      have hFc : Continuous (fun x => ℓ (F x)) := ℓ.continuous.comp F.continuous
      fun_prop
  have hwc : HasCompactSupport (fun y => χ ((R * c)⁻¹ • y) * ℓ (F (R⁻¹ • y))) :=
    (hχ.2.1.comp_homeomorph
      (Homeomorph.smulOfNeZero (R * c)⁻¹ (inv_ne_zero (mul_pos hR0 hc0).ne'))).mul_right
  obtain ⟨hq, hnorm⟩ := canonical_commutator_compact_L2_transfer
    Q S j i R c χ (fun x => ℓ (F x)) hw hwc hp
  refine ⟨hq, hnorm.trans_le ?_⟩
  calc
    _ ≤ (2 / ellipticityScale L) *
        (C * c ^ (m + d) * schwartzTestNorm N F / (1 + c * a) ^ N) :=
      mul_le_mul_of_nonneg_left hb hα.le
    _ = _ := by ring

/-- The canonical annular pieces are summable in L² with no loss of
Schwartz order and a constant selected before the environment law. -/
theorem canonical_commutator_schwartz_dyadic_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 < a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∀ N : ℕ, m + d + 1 ≤ N → ∀ (R : ℝ), 1 ≤ R → ∀ (j i : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
        ∃ hf : ∀ n : ℕ, MemLp
            (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
              ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
                (χ ((R * (4 * (2 : ℝ) ^ n))⁻¹ • y) * ℓ (F (R⁻¹ • y))))
            2 (physicalReferenceLaw Q),
          Summable (fun n => ‖(hf n).toLp
            (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
              ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
                (χ ((R * (4 * (2 : ℝ) ^ n))⁻¹ • y) * ℓ (F (R⁻¹ • y))))‖) ∧
          ‖∑' n, (hf n).toLp
            (fun ω : {ω : FieldPair d // IsRegular L ω} => R ^ (-(d : ℝ) / 2) *
              ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
                (χ ((R * (4 * (2 : ℝ) ^ n))⁻¹ • y) * ℓ (F (R⁻¹ • y))))‖ ≤
            C * (a ^ N)⁻¹ * schwartzTestNorm N F := by
  obtain ⟨C, hC, h⟩ := canonical_commutator_schwartz_cutoff_L2 d hd L hL m hm hχ ha.le hχa
  refine ⟨2 * C, mul_pos (by norm_num) hC, ?_⟩
  intro r₀ Q N hN R hR j i F ℓ hℓ
  have hmN : m ≤ N := by omega
  have hscale (n : ℕ) : 4 ≤ 4 * (2 : ℝ) ^ n := by
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hpieces (n : ℕ) := h r₀ Q N hmN R hR j i F ℓ hℓ
    (4 * (2 : ℝ) ^ n) (hscale n)
  choose hf hnorm using hpieces
  have hnF := clockSchwartz_norm_nonneg N F
  obtain ⟨hs, hb⟩ := norm_tsum_le_of_dyadic_schwartz_decay
    (p := m + d) hN ha (by norm_num : (1 : ℝ) ≤ 4)
    (B := C * schwartzTestNorm N F) (by positivity)
    (u := fun n => (hf n).toLp _) (fun n => (hnorm n).trans_eq (by ring))
  refine ⟨hf, hs, hb.trans_eq ?_⟩
  ring

/-- The pointwise canonical annular sum defines an L² random variable. -/
theorem canonical_commutator_schwartz_dyadic_tsum_L2
    (d : ℕ) (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (m : ℕ) (hm : (d : ℝ) / 2 < m)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest (originBall d 1) χ)
    {a : ℝ} (ha : 0 < a) (hχa : ∀ x ∈ tsupport χ, a ≤ euclideanNorm x) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∀ N : ℕ, m + d + 1 ≤ N → ∀ (R : ℝ), 1 ≤ R → ∀ (j i : Fin d)
        (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
        (ℓ : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ), ‖ℓ‖ ≤ 1 →
        ∃ ht : MemLp (fun ω : {ω : FieldPair d // IsRegular L ω} => ∑' n : ℕ,
            R ^ (-(d : ℝ) / 2) *
              ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
                (χ ((R * (4 * (2 : ℝ) ^ n))⁻¹ • y) * ℓ (F (R⁻¹ • y))))
            2 (physicalReferenceLaw Q),
          ‖ht.toLp (fun ω : {ω : FieldPair d // IsRegular L ω} => ∑' n : ℕ,
            R ^ (-(d : ℝ) / 2) *
              ∫ y, commutatorObservation Q j i (translate (r₀ • y) (reduce ω.1)) *
                (χ ((R * (4 * (2 : ℝ) ^ n))⁻¹ • y) * ℓ (F (R⁻¹ • y))))‖ ≤
            C * (a ^ N)⁻¹ * schwartzTestNorm N F := by
  obtain ⟨C, hC, h⟩ := canonical_commutator_schwartz_dyadic_L2 d hd L hL m hm hχ ha hχa
  refine ⟨C, hC, ?_⟩
  intro r₀ Q N hN R hR j i F ℓ hℓ
  obtain ⟨hf, hs, hb⟩ := h r₀ Q N hN R hR j i F ℓ hℓ
  obtain ⟨ht, hrep, _⟩ := memLp_tsum_of_summable_toLp_norm hf hs
  refine ⟨ht, ?_⟩
  rw [hrep]
  exact hb

/-- The exact normalization under the physical correlation-length change
of variables. No regularity or integrability assumption is needed for this
Bochner change of variables. -/
theorem normalized_compact_integral_physical_rescaling
    {d : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 < R)
    (G χ f : Vec d → ℝ) (c : ℝ) :
    (r * R) ^ (-(d : ℝ) / 2) *
        (∫ x, G x * (χ (((r * R) * c)⁻¹ • x) * f ((r * R)⁻¹ • x))) =
      r ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) *
        (∫ y, G (r • y) * (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) := by
  let H : Vec d → ℝ := fun x =>
    G x * (χ (((r * R) * c)⁻¹ • x) * f ((r * R)⁻¹ • x))
  have heq (y : Vec d) : H (r • y) =
      G (r • y) * (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y)) := by
    simp [H, mul_inv_rev, smul_smul, hr.ne', mul_left_comm, mul_comm]
  have hi := Measure.integral_comp_smul_of_nonneg
    (volume : Measure (Vec d)) H r (hR := hr.le)
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul, heq] at hi
  have hi' : (∫ x, H x) = r ^ d *
      (∫ y, G (r • y) * (χ ((R * c)⁻¹ • y) * f (R⁻¹ • y))) := by
    rw [hi]
    field_simp [hr.ne']
  have hscale : (r * R) ^ (-(d : ℝ) / 2) * r ^ d =
      r ^ ((d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) := by
    rw [Real.mul_rpow hr.le hR.le, ← Real.rpow_natCast r d]
    calc
      _ = (r ^ (-(d : ℝ) / 2) * r ^ (d : ℝ)) * R ^ (-(d : ℝ) / 2) := by ring
      _ = _ := by
        rw [← Real.rpow_add hr]
        congr 2
        ring
  change (r * R) ^ (-(d : ℝ) / 2) * (∫ x, H x) = _
  rw [hi', ← mul_assoc, hscale]

/-- A real representative on a measure-preserving realization has exactly
the norm of the original complex L² class. -/
theorem norm_complexLp_eq_real_toLp_of_pullback
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {π : β → α}
    (hπ : MeasurePreserving π ν μ) (u : Lp ℂ 2 μ)
    {g : β → ℝ} (hg : MemLp g 2 ν)
    (heq : ∀ᵐ b ∂ν, u (π b) = (g b : ℂ)) :
    ‖u‖ = ‖hg.toLp g‖ := by
  rw [← Lp.norm_compMeasurePreserving u hπ, Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [Lp.coeFn_compMeasurePreserving u hπ, hg.coeFn_toLp, heq]
    with b hb hgb heqb
  rw [hb, Function.comp_apply, heqb, hgb, Complex.norm_real]

/-- Forgetting physical regularity and applying the literal reduction
realizes exactly the frozen reduced law. -/
theorem measurePreserving_physical_reduce {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) :
    MeasurePreserving (fun ω : {ω : FieldPair d // IsRegular L ω} => reduce ω.1)
      (physicalReferenceLaw Q) (reducedLaw Q) := by
  refine ⟨Probability.measurable_reduce.comp measurable_subtype_coe, ?_⟩
  change (physicalReferenceLaw Q).map
    (reduce ∘ (Subtype.val : {ω : FieldPair d // IsRegular L ω} → FieldPair d)) = _
  rw [← Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    ReductionImageV3.physicalReferenceLaw_forget]
  rfl

/-- A literal real observation gives the corresponding real spatial
integral inside its complex L² realization, with null sets transported on
the full spatial/environment product. -/
theorem scaledComplexClockPairing_real_observation
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    {R : ℝ} (hR : 0 < R) (u : Lp ℂ 2 (reducedLaw Q))
    {V : FieldPair d → ℝ}
    (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω => (V ω : ℂ))
    {f : Vec d → ℝ} (hc : Continuous f) (hf : Integrable f) :
    (scaledComplexClockPairing Q R u (fun x => (f x : ℂ)) : FieldPair d → ℂ)
      =ᵐ[reducedLaw Q] fun ω =>
        ((R ^ (-(d : ℝ) / 2) * ∫ x, f (R⁻¹ • x) * V (translate x ω) : ℝ) : ℂ) := by
  let := reducedLaw_probability Q
  have hT : Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
    Probability.continuous_translate.measurable
  have hq : Measure.QuasiMeasurePreserving
      (fun p : Vec d × FieldPair d => translate p.1 p.2)
      (volume.prod (reducedLaw Q)) (reducedLaw Q) :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_right hT (Filter.Eventually.of_forall fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving)
  have hp := hq.ae_eq_comp hu
  have hs := Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp)
  have hi := (scaledComplexClockPairing_joint_integral Q hR u
    (Complex.continuous_ofReal.comp hc) hf.ofReal).2
  filter_upwards [hi, hs] with ω hω heq
  calc
    _ = ∫ x, ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        ((f (R⁻¹ • x) : ℂ) * u (translate x ω)) := hω
    _ = ∫ x, ((R ^ (-(d : ℝ) / 2) *
        (f (R⁻¹ • x) * V (translate x ω)) : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      change u (translate x ω) = (V (translate x ω) : ℂ) at hx
      rw [hx]
      simp only [Complex.ofReal_mul]
    _ = ((∫ x, R ^ (-(d : ℝ) / 2) *
        (f (R⁻¹ • x) * V (translate x ω)) : ℝ) : ℂ) := integral_ofReal
    _ = _ := by rw [integral_const_mul]

end EinsteinFull.Calculus.C5TestCLT
