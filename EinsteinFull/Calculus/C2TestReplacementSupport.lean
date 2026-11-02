import EinsteinFull.Blueprint.G3.LocalizedCovarianceObjects
import EinsteinFull.Calculus.S1ClosureArithmeticSupport
import EinsteinFull.Calculus.S1VectorL2Support
import EinsteinRelation.Correctors.NormedIntegralMoment
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Correctors.HeatKernelScaling
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_coarse_u2D_identification
import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Calculus.SchwartzNormSupport
import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinFull.Blueprint.G3.node_e_u3A_test_u2D_clt
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinFull.Work.W2.CorrectorReuseSupport
import EinsteinFull.Work.W7.ClockCovarianceLimitProof

/-! Structural scale choices and Euclidean L² spatial testing for the
smooth-test replacement step. The selected field is used with precisely its
product almost-everywhere measurability. -/

namespace EinsteinFull.Calculus.C2TestReplacement

open EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal

/-- The two strict gaps in the covariance window admit one common theta,
chosen before the law, the scale and the test. -/
theorem exists_theta (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      (d : ℝ) / 2 < θ * η * γ ∧ 1 / 2 < θ * η := by
  rcases h with ⟨_, _, _, hδ, hγ, _, hηγ, _, hη, _, _⟩
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hγpos : 0 < γ :=
    (mul_pos (div_pos hdpos (by norm_num)) (by linarith : 0 < 1 + δ)).trans hγ
  have hηpos : 0 < η := by linarith
  have hprod : (d : ℝ) / 2 < η * γ := by
    have hh := (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hγpos)).mp hηγ
    nlinarith only [hh]
  have hratio : (d : ℝ) / 2 / (η * γ) < 1 :=
    (div_lt_one (mul_pos hηpos hγpos)).mpr hprod
  have hhalf : (1 / 2 : ℝ) / η < 1 := (div_lt_one hηpos).mpr hη
  obtain ⟨θ, hθ, hθone⟩ := exists_between
    (show max 0 (max ((d : ℝ) / 2 / (η * γ)) ((1 / 2 : ℝ) / η)) < 1 from
      max_lt zero_lt_one (max_lt hratio hhalf))
  refine ⟨θ, (le_max_left _ _).trans_lt hθ, hθone, ?_, ?_⟩
  · have hh := (div_lt_iff₀ (mul_pos hηpos hγpos)).mp
      (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hθ)
    simpa only [mul_assoc] using hh
  · exact (div_lt_iff₀ hηpos).mp
      (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hθ)

/-- The dyadic mesoscopic radius eventually exceeds the physical range.
The threshold depends only on the range and the two positive exponents. -/
theorem exists_physical_threshold (ρ θ η : ℝ) (hθ : 0 < θ) (hη : 0 < η) :
    ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      2 * ρ ≤ ((2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)) ^ η := by
  have hlarge : ∀ᶠ R : ℝ in Filter.atTop,
      (2 : ℝ) ^ η * (2 * ρ) ≤ R ^ (θ * η) :=
    (tendsto_rpow_atTop (mul_pos hθ hη)).eventually_ge_atTop _
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max 2 A, le_max_left _ _, ?_⟩
  intro R hR
  have hRtwo : 2 ≤ R := (le_max_left _ _).trans hR
  have hRpos : 0 < R := by linarith
  let L := (2 : ℝ) ^ Int.floor (Real.log (R ^ θ) / Real.log 2)
  obtain ⟨hL, _, hLtwo⟩ := S1.dyadic_scale_bounds (by linarith) hθ (L := L) rfl
  have hh : (2 : ℝ) ^ η * (2 * ρ) ≤ 2 ^ η * L ^ η := by
    calc (2 : ℝ) ^ η * (2 * ρ) ≤ R ^ (θ * η) :=
          hA R ((le_max_right _ _).trans hR)
      _ = (R ^ θ) ^ η := Real.rpow_mul hRpos.le θ η
      _ ≤ (2 * L) ^ η := Real.rpow_le_rpow (by positivity) hLtwo hη.le
      _ = 2 ^ η * L ^ η := Real.mul_rpow (by norm_num) hL.le
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < 2 ^ η)).mp hh

/-- Minkowski for a product-a.e. measurable field. This consumes precisely
the measurability available for the selected localized field; it does not
require a globally jointly measurable selection. -/
theorem integral_two_bound_ae {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (H : X → ℝ) (hHm : Measurable H) (hH : ∀ x, 0 ≤ H x) (hHi : Integrable H ν)
    (f : X × Ω → E) (hf : AEStronglyMeasurable f (ν.prod μ))
    (hmem : ∀ x, MemLp (fun ω => f (x, ω)) 2 μ ∧
      eLpNorm (fun ω => f (x, ω)) 2 μ ≤ ENNReal.ofReal (H x)) :
    (∀ᵐ ω ∂μ, Integrable (fun x => f (x, ω)) ν) ∧
      MemLp (fun ω => ∫ x, f (x, ω) ∂ν) 2 μ ∧
      eLpNorm (fun ω => ∫ x, f (x, ω) ∂ν) 2 μ ≤ ENNReal.ofReal (∫ x, H x ∂ν) := by
  classical
  let g := hf.mk f
  have hg : Measurable g := hf.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[ν.prod μ] g := hf.ae_eq_mk
  have hsec : ∀ᵐ x ∂ν, (fun ω => f (x, ω)) =ᵐ[μ] (fun ω => g (x, ω)) :=
    ae_ae_of_ae_prod hfg
  obtain ⟨bad, hbad, hbadm, hbadzero⟩ := exists_measurable_superset_of_null
    (show ν {x | ¬ (fun ω => f (x, ω)) =ᵐ[μ] (fun ω => g (x, ω))} = 0 from hsec)
  let k : X × Ω → E := fun p => if p.1 ∈ bad then 0 else g p
  have hk : Measurable k := measurable_const.ite (hbadm.preimage measurable_fst) hg
  have hkmem : ∀ x, MemLp (fun ω => k (x, ω)) 2 μ ∧
      eLpNorm (fun ω => k (x, ω)) 2 μ ≤ ENNReal.ofReal (H x) := by
    intro x
    by_cases hx : x ∈ bad
    · simp only [k, ite_eq_left hx]
      change MemLp (0 : Ω → E) 2 μ ∧ eLpNorm (0 : Ω → E) 2 μ ≤ _
      rw [eLpNorm_zero]
      exact ⟨MemLp.zero, bot_le⟩
    · have heq : (fun ω => f (x, ω)) =ᵐ[μ] (fun ω => g (x, ω)) := by
        by_contra hn
        exact hx (hbad hn)
      simpa only [k, ite_eq_right hx] using
        And.intro ((memLp_congr_ae heq).mp (hmem x).1)
          ((eLpNorm_congr_ae heq).symm.trans_le (hmem x).2)
  have hnotbad : ∀ᵐ x ∂ν, x ∉ bad := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hbadzero
  have hkg : k =ᵐ[ν.prod μ] g := by
    filter_upwards [quasiMeasurePreserving_fst.ae hnotbad] with p hp
    exact ite_eq_right hp
  have hfk : f =ᵐ[ν.prod μ] k := hfg.trans hkg.symm
  have hswap : (fun p : Ω × X => f (p.2, p.1)) =ᵐ[μ.prod ν]
      (fun p => k (p.2, p.1)) := measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hfk
  have hs : ∀ᵐ ω ∂μ, (fun x => f (x, ω)) =ᵐ[ν] (fun x => k (x, ω)) :=
    ae_ae_of_ae_prod hswap
  have hi : (fun ω => ∫ x, f (x, ω) ∂ν) =ᵐ[μ] (fun ω => ∫ x, k (x, ω) ∂ν) :=
    hs.mono fun _ h => integral_congr_ae h
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  obtain ⟨hki, hklp, hkb⟩ := EinsteinRelation.Correctors.normed_integral_moment_le
    μ ν (by norm_num : (1 : ℝ) ≤ 2) H hHm hH hHi k hk (by simpa only [htwo] using hkmem)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hki, hs] with ω hω hωeq
    exact hω.congr hωeq.symm
  · apply (memLp_congr_ae hi).mpr
    simpa only [htwo] using hklp
  · exact (eLpNorm_congr_ae hi).trans_le (by simpa only [htwo] using hkb)

/-- Bilinear complex testing against a real joint vector retains its exact
Euclidean size, with no coordinate-count loss. -/
theorem bilinear_norm_le {ι : Type*} [Fintype ι]
    (F : EuclideanSpace ℂ ι) (v : ι → ℝ) :
    ‖∑ a, F a * (v a : ℂ)‖ ≤ ‖F‖ * S1.vsize v := by
  calc ‖∑ a, F a * (v a : ℂ)‖ ≤ ∑ a, ‖F a * (v a : ℂ)‖ := norm_sum_le _ _
    _ = ∑ a, ‖F a‖ * |v a| := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ Real.sqrt (∑ a, ‖F a‖ ^ 2) * Real.sqrt (∑ a, |v a| ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = ‖F‖ * S1.vsize v := by
      rw [EuclideanSpace.norm_eq]
      simp only [S1.vsize, sq_abs]

/-- Mean-square bilinear testing, retaining the Euclidean test and vector
norms on both sides. -/
theorem bilinear_l2_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} (F : EuclideanSpace ℂ ι) (v : Ω → ι → ℝ)
    (hv : S1.L2Vec μ v) :
    MemLp (fun ω => ∑ a, F a * (v ω a : ℂ)) 2 μ ∧
      S1.l2Size μ (fun ω => ∑ a, F a * (v ω a : ℂ)) ≤ ‖F‖ * S1.vl2 μ v := by
  have hp : MemLp (fun ω => ∑ a, F a * (v ω a : ℂ)) 2 μ :=
    memLp_finsetSum _ fun a _ => (hv.coord_memLp a).ofReal.const_mul (F a)
  refine ⟨hp, ?_⟩
  have hi := hv.size_memLp.integrable_sq.const_mul (‖F‖ ^ 2)
  have hbound : ∫ ω, ‖∑ a, F a * (v ω a : ℂ)‖ ^ 2 ∂μ ≤
      ∫ ω, ‖F‖ ^ 2 * S1.vsize (v ω) ^ 2 ∂μ := by
    apply integral_mono hp.norm.integrable_sq hi
    intro ω
    calc ‖∑ a, F a * (v ω a : ℂ)‖ ^ 2 ≤ (‖F‖ * S1.vsize (v ω)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (bilinear_norm_le F (v ω)) 2
      _ = ‖F‖ ^ 2 * S1.vsize (v ω) ^ 2 := mul_pow _ _ _
  calc S1.l2Size μ (fun ω => ∑ a, F a * (v ω a : ℂ)) ≤
      Real.sqrt (∫ ω, ‖F‖ ^ 2 * S1.vsize (v ω) ^ 2 ∂μ) := Real.sqrt_le_sqrt hbound
    _ = ‖F‖ * S1.vl2 μ v := by
      rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
      rfl

/-- Conversion from the explicit mean-square size to the extended L² norm.
Membership is essential under the v4.35 definition. -/
theorem eLpNorm_two_eq_ofReal_l2Size {Ω E : Type*} [MeasurableSpace Ω]
    [RCLike E] {μ : Measure Ω} {f : Ω → E} (hf : MemLp f 2 μ) :
    eLpNorm f 2 μ = ENNReal.ofReal (S1.l2Size μ f) := by
  rw [hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
  rfl

/-- Weighted spatial testing of a uniformly L²-bounded real vector field.
The field needs only product-a.e. strong measurability, and the pairing is
bilinear in its complex test coordinates. -/
theorem weighted_bilinear_integral_bound {Ω X ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (F : X → EuclideanSpace ℂ ι) (hFm : Measurable F) (hFi : Integrable F ν)
    (v : X × Ω → ι → ℝ) (hvm : AEStronglyMeasurable v (ν.prod μ))
    (hv : ∀ x, S1.L2Vec μ (fun ω => v (x, ω)))
    (M : ℝ) (hM : 0 ≤ M) (hsize : ∀ x, S1.vl2 μ (fun ω => v (x, ω)) ≤ M) :
    (∀ᵐ ω ∂μ, Integrable (fun x => ∑ a, F x a * (v (x, ω) a : ℂ)) ν) ∧
      MemLp (fun ω => ∫ x, ∑ a, F x a * (v (x, ω) a : ℂ) ∂ν) 2 μ ∧
      S1.l2Size μ (fun ω => ∫ x, ∑ a, F x a * (v (x, ω) a : ℂ) ∂ν) ≤
        (∫ x, ‖F x‖ ∂ν) * M := by
  have hmeas : AEStronglyMeasurable
      (fun p : X × Ω => ∑ a, F p.1 a * (v p a : ℂ)) (ν.prod μ) := by
    apply Finset.aestronglyMeasurable_fun_sum
    intro a _
    have hf : Measurable (fun p : X × Ω => F p.1 a) :=
      ((PiLp.continuous_apply 2 _ a).measurable.comp hFm).comp measurable_fst
    have hv' := (continuous_apply a).comp_aestronglyMeasurable hvm
    exact hf.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp_aestronglyMeasurable hv')
  obtain ⟨hsec, hlp, hb⟩ := integral_two_bound_ae μ ν (fun x => ‖F x‖ * M)
    (hFm.norm.mul_const M) (fun x => mul_nonneg (norm_nonneg _) hM)
    (hFi.norm.mul_const M) (fun p => ∑ a, F p.1 a * (v p a : ℂ)) hmeas (fun x => by
      obtain ⟨hp, hpb⟩ := bilinear_l2_bound (F x) (fun ω => v (x, ω)) (hv x)
      exact ⟨hp, (eLpNorm_two_eq_ofReal_l2Size hp).trans_le (ENNReal.ofReal_le_ofReal
        (hpb.trans (mul_le_mul_of_nonneg_left (hsize x) (norm_nonneg _))))⟩)
  refine ⟨hsec, hlp, ?_⟩
  rw [eLpNorm_two_eq_ofReal_l2Size hlp] at hb
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (S1.l2Size_nonneg _),
    ENNReal.toReal_ofReal (integral_nonneg fun x => mul_nonneg (norm_nonneg _) hM),
    integral_mul_const] at hreal
  exact hreal

/-- Scalar multiplication pulls out of the explicit mean-square size. -/
theorem l2Size_const_mul {Ω E : Type*} [MeasurableSpace Ω] [RCLike E]
    (μ : Measure Ω) (c : E) (f : Ω → E) :
    S1.l2Size μ (fun ω => c * f ω) = ‖c‖ * S1.l2Size μ f := by
  unfold S1.l2Size
  simp_rw [norm_mul, mul_pow]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]

/-- The normalization and spatial dilation in the literal pairings turn a
uniform vector error into the source's R^(d/2) weighted estimate. -/
theorem scaled_weighted_bilinear_integral_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d N : ℕ) (hN : d < N)
    (R : ℝ) (hR : 0 < R)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (v : Vec d × Ω → JointObservationIndex d → ℝ)
    (hvm : AEStronglyMeasurable v (volume.prod μ))
    (hv : ∀ x, S1.L2Vec μ (fun ω => v (x, ω)))
    (M : ℝ) (hM : 0 ≤ M) (hsize : ∀ x, S1.vl2 μ (fun ω => v (x, ω)) ≤ M) :
    MemLp (fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
      ∫ x, ∑ a, F (R⁻¹ • x) a * (v (x, ω) a : ℂ)) 2 μ ∧
    S1.l2Size μ (fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
      ∫ x, ∑ a, F (R⁻¹ • x) a * (v (x, ω) a : ℂ)) ≤
      clockSchwartzWeightMass d N * schwartzTestNorm N F * R ^ ((d : ℝ) / 2) * M := by
  obtain ⟨_, hp, hb⟩ := weighted_bilinear_integral_bound μ volume
    (fun x => F (R⁻¹ • x))
    (F.continuous.measurable.comp (measurable_id.const_smul R⁻¹))
    (F.integrable.comp_smul (inv_ne_zero hR.ne')) v hvm hv M hM hsize
  refine ⟨hp.const_mul _, ?_⟩
  have hi : (∫ x, ‖F (R⁻¹ • x)‖) ≤
      R ^ d * (clockSchwartzWeightMass d N * schwartzTestNorm N F) := by
    have he := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure (Vec d))
      (fun x => ‖F x‖) hR.le
    simp only [Module.finrank_pi, Fintype.card_fin,
      smul_eq_mul] at he
    rw [he]
    exact mul_le_mul_of_nonneg_left (clockSchwartz_integral_norm_le hN F)
      (pow_nonneg hR.le _)
  have he : R ^ (-(d : ℝ) / 2) * R ^ d = R ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]
    congr 1
    ring
  rw [l2Size_const_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hR.le _)]
  calc
    _ ≤ R ^ (-(d : ℝ) / 2) *
        (R ^ d * (clockSchwartzWeightMass d N * schwartzTestNorm N F) * M) :=
      mul_le_mul_of_nonneg_left
        (hb.trans (mul_le_mul_of_nonneg_right hi hM)) (Real.rpow_nonneg hR.le _)
    _ = (R ^ (-(d : ℝ) / 2) * R ^ d) *
        (clockSchwartzWeightMass d N * schwartzTestNorm N F) * M := by ring
    _ = _ := by rw [he]; ring

/-- Coordinate L² membership gives the explicit Euclidean vector membership. -/
theorem l2Vec_of_coord {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {v : Ω → ι → ℝ} (hv : ∀ a, MemLp (fun ω => v ω a) 2 μ) :
    S1.L2Vec μ v := by
  refine ⟨fun a => (hv a).aestronglyMeasurable, ?_⟩
  have hp : MemLp (fun ω => (WithLp.toLp 2 (v ω) : EuclideanSpace ℝ ι)) 2 μ :=
    memLp_piLp_iff.mpr hv
  simpa only [S1.vsize_eq_norm] using hp.norm

/-- Stationarity preserves the explicit Euclidean mean-square size. -/
theorem vl2_eq_of_ae_comp {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {u v : Ω → ι → ℝ} {T : Ω → Ω}
    (hu : S1.L2Vec μ u) (hv : S1.L2Vec μ v) (hT : MeasurePreserving T μ μ)
    (heq : u =ᵐ[μ] fun ω => v (T ω)) : S1.vl2 μ u = S1.vl2 μ v := by
  have heq' : (fun ω => S1.vsize (u ω)) =ᵐ[μ]
      (fun ω => S1.vsize (v (T ω))) := heq.fun_comp S1.vsize
  have hb := (eLpNorm_congr_ae heq').trans
    (eLpNorm_comp_measurePreserving (g := fun ω => S1.vsize (v ω))
      (f := T) (p := 2) hv.size_memLp.aestronglyMeasurable hT)
  rw [eLpNorm_two_eq_ofReal_l2Size hu.size_memLp,
    eLpNorm_two_eq_ofReal_l2Size hv.size_memLp] at hb
  have hc := congrArg ENNReal.toReal hb
  rw [ENNReal.toReal_ofReal (S1.l2Size_nonneg _),
    ENNReal.toReal_ofReal (S1.l2Size_nonneg _)] at hc
  simpa only [← S1.vl2_eq_l2Size] using hc

/-- The exact joint-localization conclusion already implies L² membership of
the literal localized pairing, using stationarity for a spatially uniform bound. -/
theorem localizedPairing_memLp
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (r : ℝ) (hr : 2 * D.dependenceRange ≤ r)
    (R : ℝ) (hR : R ≠ 0)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    MemLp (covarianceLocalizedPairing d hd D s δ γ η β h Q R r F) 2
      (reducedLaw Q) := by
  obtain ⟨_, _, _, hfield⟩ := hloc d hd D s δ γ η β h
  obtain ⟨hm, hx⟩ := hfield Q hQ r hr
  let v := covarianceLocalizedField d hd D s δ γ η β h Q r
  have hv (x : Vec d) : S1.L2Vec (reducedLaw Q) (v x) :=
    l2Vec_of_coord fun a => ((hx x).1 a).1
  have hsize (x : Vec d) : S1.vl2 (reducedLaw Q) (v x) =
      S1.vl2 (reducedLaw Q) (v 0) :=
    vl2_eq_of_ae_comp (hv x) (hv 0)
      (EinsteinRelation.measurePreserving_translate (reducedLaw Q)
        (reducedLaw_stationary Q) x) (hx x).2.2.1
  obtain ⟨_, hp, _⟩ := weighted_bilinear_integral_bound (reducedLaw Q) volume
    (fun x => F (R⁻¹ • x))
    (F.continuous.measurable.comp (measurable_id.const_smul R⁻¹))
    (F.integrable.comp_smul (inv_ne_zero hR))
    (fun p => v p.1 p.2) hm hv (S1.vl2 (reducedLaw Q) (v 0))
    (S1.vl2_nonneg _ _) (fun x => (hsize x).le)
  exact hp.const_mul _

/-- A bounded scalar clock error is square integrable with the same bound. -/
theorem l2Size_le_of_ae_norm_bound {Ω E : Type*} [MeasurableSpace Ω] [RCLike E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → E}
    (hf : AEStronglyMeasurable f μ) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ K) :
    MemLp f 2 μ ∧ S1.l2Size μ f ≤ K := by
  have hp : MemLp f 2 μ := MemLp.of_bound hf K hb
  refine ⟨hp, ?_⟩
  have hi : (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ K ^ 2 := by
    calc (∫ ω, ‖f ω‖ ^ 2 ∂μ) ≤ ∫ _, K ^ 2 ∂μ :=
          integral_mono_ae hp.norm.integrable_sq (integrable_const _) <|
            hb.mono fun ω hω => pow_le_pow_left₀ (norm_nonneg _) hω 2
      _ = K ^ 2 := by simp
  exact (Real.sqrt_le_sqrt hi).trans_eq (Real.sqrt_sq hK)

/-- The clock coordinate is a Euclidean isometric embedding. -/
theorem vsize_clock {ι : Type*} [Fintype ι] (c : ℝ) :
    S1.vsize (fun a : ι ⊕ Unit => match a with | .inl _ => 0 | .inr _ => c) = |c| := by
  simp [S1.vsize, Fintype.sum_sum_type, Real.sqrt_sq_eq_abs]

/-- Matrix error extended by zero in the clock coordinate. -/
def matrixError {Ω ι : Type*} (u c : Ω → ι ⊕ Unit → ℝ) (ω : Ω) : ι ⊕ Unit → ℝ
  | .inl i => u ω (.inl i) - c ω (.inl i)
  | .inr _ => 0

/-- A scalar placed in the clock coordinate, with zero matrix coordinates. -/
def clockVector {Ω ι : Type*} (f : Ω → ℝ) (ω : Ω) : ι ⊕ Unit → ℝ
  | .inl _ => 0
  | .inr _ => f ω

/-- Pointwise cancellation of the common coarse matrix. -/
theorem joint_error_decomposition {Ω ι : Type*} (u v c : Ω → ι ⊕ Unit → ℝ) :
    (fun ω => u ω - v ω) = fun ω => matrixError u c ω +
      (-1 : ℝ) • matrixError v c ω + clockVector (fun ω => u ω (.inr ()) - v ω (.inr ())) ω := by
  funext ω a
  cases a with
  | inl i => simp [matrixError, clockVector]
  | inr i => simp [matrixError, clockVector]

/-- L² control of the clock embedding retains the scalar error constant. -/
theorem clockVector_l2_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hm : AEStronglyMeasurable f μ) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ᵐ ω ∂μ, |f ω| ≤ K) :
    S1.L2Vec μ (clockVector (ι := ι) f) ∧ S1.vl2 μ (clockVector (ι := ι) f) ≤ K := by
  obtain ⟨hp, hsize⟩ := l2Size_le_of_ae_norm_bound μ hm hK
    (by simpa only [Real.norm_eq_abs] using hb)
  refine ⟨l2Vec_of_coord (fun a => ?_), ?_⟩
  · cases a with
    | inl i => exact MemLp.zero
    | inr i => exact hp
  · have he (ω : Ω) : S1.vsize (clockVector (ι := ι) f ω) = |f ω| := vsize_clock _
    simpa only [S1.vl2, he, S1.l2Size, Real.norm_eq_abs, sq_abs] using hsize

/-- Three-term vector Minkowski estimate with scalar negation simplified
before substituting the matrix-clock fields. -/
theorem three_term_l2_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) (f g k : Ω → ι → ℝ)
    (hf : S1.L2Vec μ f) (hg : S1.L2Vec μ g) (hk : S1.L2Vec μ k)
    (A B K : ℝ) (hA : S1.vl2 μ f ≤ A) (hB : S1.vl2 μ g ≤ B)
    (hK : S1.vl2 μ k ≤ K) :
    S1.L2Vec μ (fun ω => f ω + (-1 : ℝ) • g ω + k ω) ∧
      S1.vl2 μ (fun ω => f ω + (-1 : ℝ) • g ω + k ω) ≤ A + B + K := by
  have hneg : S1.vl2 μ (fun ω => (-1 : ℝ) • g ω) = S1.vl2 μ g := by
    simpa only [abs_neg, abs_one, one_mul] using S1.vl2_smul μ g (-1)
  have hfg := S1.vl2_add_le hf (hg.smul (-1))
  have hfgk := S1.vl2_add_le (hf.add (hg.smul (-1))) hk
  have hsum := add_le_add hfg (le_refl (S1.vl2 μ k))
  have hall := hfgk.trans hsum
  have heq := congrArg (fun t => S1.vl2 μ f + t + S1.vl2 μ k) hneg
  have hfinal := (hall.trans_eq heq).trans (add_le_add (add_le_add hA hB) hK)
  exact ⟨(hf.add (hg.smul (-1))).add hk, hfinal⟩

/-- Assemble the two matrix errors and the scalar clock error, retaining
Euclidean vector norms and a separate bound for each term. -/
theorem joint_error_l2_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u v c : Ω → ι ⊕ Unit → ℝ)
    (huc : S1.L2Vec μ (matrixError u c)) (hvc : S1.L2Vec μ (matrixError v c))
    (hcm : AEStronglyMeasurable (fun ω => u ω (.inr ()) - v ω (.inr ())) μ)
    (A B K : ℝ) (hK : 0 ≤ K)
    (hA : S1.vl2 μ (matrixError u c) ≤ A)
    (hB : S1.vl2 μ (matrixError v c) ≤ B)
    (hclock : ∀ᵐ ω ∂μ, |u ω (.inr ()) - v ω (.inr ())| ≤ K) :
    S1.L2Vec μ (fun ω => u ω - v ω) ∧
      S1.vl2 μ (fun ω => u ω - v ω) ≤ A + B + K := by
  obtain ⟨hmem, hsize⟩ := clockVector_l2_bound (ι := ι) μ
    (fun ω => u ω (.inr ()) - v ω (.inr ())) hcm K hK hclock
  have hp := three_term_l2_bound μ (matrixError u c) (matrixError v c)
    (clockVector (ι := ι) (fun ω => u ω (.inr ()) - v ω (.inr ())))
    huc hvc hmem A B K hA hB hsize
  exact (congrArg (fun w => S1.L2Vec μ w ∧ S1.vl2 μ w ≤ A + B + K)
    (joint_error_decomposition u v c)).mpr hp

/-- Literal real Gaussian averages of the commutator and centered clock.
This is the real representative whose complexification is smoothed against Z. -/
noncomputable def realSmoothedField {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r : ℝ) (x : Vec d) (ω : FieldPair d) :
    JointObservationIndex d → ℝ
  | .inl (j, k) => ∫ z : Vec d,
      heatKernel 0 r z * commutatorObservation Q j k (translate (x - z) ω)
  | .inr _ => ∫ z : Vec d, heatKernel 0 r z * centeredClockField Q (x - z) ω

/-- The literal commutator has a Borel representative, since the canonical
corrector gradient is evaluated using its strongly measurable L² representative. -/
theorem commutatorObservation_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (j i : Fin d) : Measurable (commutatorObservation Q j i) := by
  apply Finset.measurable_fun_sum
  intro k _
  have ha : Continuous (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_fst
  have hg : Measurable (fun ω : FieldPair d => correctorGradient Q i ω k) :=
    (PiLp.continuous_apply 2 _ k).measurable.comp
      (Lp.stronglyMeasurable (correctorGradient Q i)).measurable
  exact ((ha.matrix_elem j k).measurable.sub measurable_const).mul
    (measurable_const.add hg)

/-- Joint Borel measurability of the actual isotropic Gaussian averages.
No measurability of a selected localized basis is used. -/
theorem realSmoothedField_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (r : ℝ) :
    Measurable (fun p : Vec d × FieldPair d => realSmoothedField Q r p.1 p.2) := by
  have hk : Measurable (heatKernel (0 : Vec d) r) := by
    change Measurable (fun z : Vec d => Correctors.euclideanHeatKernel (r ^ 2) (z - 0))
    simpa only [sub_zero] using
      (Correctors.continuous_euclideanHeatKernel (d := d) (r ^ 2)).measurable
  have hT : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      translate (p.1.1 - p.2) p.1.2) :=
    Probability.continuous_translate.measurable.comp
      ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd)
  apply Measurable.of_eval
  intro a
  rcases a with ⟨j, k⟩ | u
  · exact (((hk.comp measurable_snd).mul
      ((commutatorObservation_measurable Q j k).comp hT)).stronglyMeasurable.integral_prod_right).measurable
  · exact (((hk.comp measurable_snd).mul
      ((continuous_centeredClockField Q).measurable.comp
        ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd))).stronglyMeasurable.integral_prod_right).measurable

/-- The exact coarse and joint-localization dependencies give the full
matrix-clock error at each spatial point, with the structural constant
chosen before the law, scale and spatial point. -/
theorem realSmoothed_localized_l2_bound
    (hcoarse : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt)
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ r : ℝ, 2 * D.dependenceRange ≤ r → ∀ x : Vec d,
        S1.L2Vec (reducedLaw Q) (fun ω => realSmoothedField Q r x ω -
          covarianceLocalizedField d hd D s δ γ η β h Q r x ω) ∧
        S1.vl2 (reducedLaw Q) (fun ω => realSmoothedField Q r x ω -
          covarianceLocalizedField d hd D s δ γ η β h Q r x ω) ≤
            C * (r ^ (-(d : ℝ)) + r ^ (-γ)) := by
  obtain ⟨C₁, hC₁, hc⟩ := hcoarse d hd D
  obtain ⟨C₂, hC₂, hclock, hl⟩ := hloc d hd D s δ γ η β h
  obtain ⟨C₃, hC₃, hcl⟩ := hclock (d : ℝ)
  refine ⟨C₁ + C₂ + C₃, by positivity, ?_⟩
  intro Q hQ r hr x
  have hm (a : JointObservationIndex d) : AEStronglyMeasurable
      (fun ω => realSmoothedField Q r x ω a) (reducedLaw Q) :=
    ((measurable_pi_apply a).comp ((realSmoothedField_measurable Q r).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  have hrange : D.dependenceRange ≤ r := by
    linarith [D.one_le_dependenceRange]
  have hrpos : 0 < r := by linarith [D.one_le_dependenceRange]
  obtain ⟨hcmeas, hcmem, hcb⟩ := hc Q hQ r hrange x
  obtain ⟨_, hlx⟩ := hl Q hQ r hr
  let v := covarianceLocalizedField d hd D s δ γ η β h Q r x
  let c : FieldPair d → JointObservationIndex d → ℝ := fun ω a => match a with
    | .inl (j, k) => covarianceCenteredCoarseEntry D Q r x j k ω
    | .inr _ => 0
  have hcm (a : JointObservationIndex d) :
      AEStronglyMeasurable (fun ω => c ω a) (reducedLaw Q) := by
    rcases a with ⟨j, k⟩ | u
    · exact ((hcmeas j k).2.aestronglyMeasurable).sub aestronglyMeasurable_const
    · exact aestronglyMeasurable_const
  have hvm (a : JointObservationIndex d) :
      AEStronglyMeasurable (fun ω => v ω a) (reducedLaw Q) :=
    ((hlx x).1 a).1.aestronglyMeasurable
  have hK : 0 ≤ C₃ * r ^ (-(d : ℝ)) :=
    mul_nonneg hC₃.le (Real.rpow_nonneg hrpos.le _)
  have huc : S1.L2Vec (reducedLaw Q) (matrixError (realSmoothedField Q r x) c) := by
    refine ⟨fun a => ?_, ?_⟩
    · cases a with
      | inl i => exact (hm (.inl i)).sub (hcm (.inl i))
      | inr i => exact aestronglyMeasurable_const
    · convert hcmem using 1
      funext ω
      congr 1
      funext a
      rcases a with ⟨j, k⟩ | u <;> rfl
  have hvc : S1.L2Vec (reducedLaw Q) (matrixError v c) := by
    refine ⟨fun a => ?_, ?_⟩
    · cases a with
      | inl i => exact (hvm (.inl i)).sub (hcm (.inl i))
      | inr i => exact aestronglyMeasurable_const
    · convert (hlx x).2.2.2.1 using 1
      funext ω
      congr 1
      funext a
      rcases a with ⟨j, k⟩ | u <;> rfl
  have hA : S1.vl2 (reducedLaw Q) (matrixError (realSmoothedField Q r x) c) ≤
      C₁ * r ^ (-(d : ℝ)) := by
    convert hcb using 1
    congr 1
    funext ω
    funext a
    rcases a with ⟨j, k⟩ | u <;> rfl
  have hB : S1.vl2 (reducedLaw Q) (matrixError v c) ≤ C₂ * r ^ (-γ) := by
    convert (hlx x).2.2.2.2 using 1
    congr 1
    funext ω
    funext a
    rcases a with ⟨j, k⟩ | u <;> rfl
  have he := joint_error_l2_bound (reducedLaw Q) (realSmoothedField Q r x) v c huc hvc
    ((hm _).sub (hvm _)) (C₁ * r ^ (-(d : ℝ))) (C₂ * r ^ (-γ))
    (C₃ * r ^ (-(d : ℝ))) hK hA hB (hcl Q hQ r hr x)
  refine ⟨he.1, he.2.trans ?_⟩
  have hdnonneg := Real.rpow_nonneg hrpos.le (-(d : ℝ))
  have hγnonneg := Real.rpow_nonneg hrpos.le (-γ)
  nlinarith [mul_nonneg hC₁.le hγnonneg, mul_nonneg hC₂.le hdnonneg,
    mul_nonneg hC₃.le hγnonneg]

/-- Spatial integration of the exact real matrix-clock replacement error,
with every witness chosen before the law, scale and Schwartz test. -/
theorem realSmoothed_localized_test_error_bound
    (hcoarse : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt)
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : d < N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q → ∀ r : ℝ, 2 * D.dependenceRange ≤ r →
        ∀ R : ℝ, 0 < R →
        ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        let error := fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          ∫ x, ∑ a, F (R⁻¹ • x) a * ((realSmoothedField Q r x ω a -
            covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℝ) : ℂ)
        MemLp error 2 (reducedLaw Q) ∧ S1.l2Size (reducedLaw Q) error ≤
          C * schwartzTestNorm N F * R ^ ((d : ℝ) / 2) *
            (r ^ (-(d : ℝ)) + r ^ (-γ)) := by
  obtain ⟨C₀, hC₀, hb⟩ := realSmoothed_localized_l2_bound hcoarse hloc d hd D s δ γ η β h
  have hmass : 0 ≤ clockSchwartzWeightMass d N :=
    integral_nonneg fun x => Real.rpow_nonneg (by positivity) _
  refine ⟨(clockSchwartzWeightMass d N + 1) * C₀, by positivity, ?_⟩
  intro Q hQ r hr R hR F
  obtain ⟨_, _, _, hfield⟩ := hloc d hd D s δ γ η β h
  have hm := (hfield Q hQ r hr).1
  have hrpos : 0 < r := by linarith [D.one_le_dependenceRange]
  let v := fun p : Vec d × FieldPair d => realSmoothedField Q r p.1 p.2 -
    covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2
  have hvm : AEStronglyMeasurable v (volume.prod (reducedLaw Q)) :=
    (realSmoothedField_measurable Q r).aestronglyMeasurable.sub hm
  have hsum : 0 ≤ r ^ (-(d : ℝ)) + r ^ (-γ) :=
    add_nonneg (Real.rpow_nonneg hrpos.le _) (Real.rpow_nonneg hrpos.le _)
  obtain ⟨hp, hpb⟩ := scaled_weighted_bilinear_integral_bound (reducedLaw Q) d N hN R hR F
    v hvm (fun x => (hb Q hQ r hr x).1) (C₀ * (r ^ (-(d : ℝ)) + r ^ (-γ)))
    (mul_nonneg hC₀.le hsum) (fun x => (hb Q hQ r hr x).2)
  refine ⟨hp, hpb.trans ?_⟩
  have hnorm := clockSchwartz_norm_nonneg N F
  have hRpow := Real.rpow_nonneg hR.le ((d : ℝ) / 2)
  have hnonneg := mul_nonneg (mul_nonneg (mul_nonneg hC₀.le hnorm) hRpow) hsum
  nlinarith

/-- Changing an observation on an environment null set does not change its
literal spatial Gaussian averages, at almost every environment. Stationarity
is used on the whole product before exchanging the two almost-everywhere binders. -/
theorem integral_translate_congr_ae {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (μ : Measure (FieldPair d)) [SFinite μ] (hμ : IsStationary μ)
    (f g : FieldPair d → E) (heq : f =ᵐ[μ] g)
    (k : Vec d → ℂ) (x : Vec d) :
    (fun ω => ∫ z : Vec d, k z • f (translate (x - z) ω)) =ᵐ[μ]
      (fun ω => ∫ z : Vec d, k z • g (translate (x - z) ω)) := by
  have hT : Measurable (fun p : Vec d × FieldPair d => translate (x - p.1) p.2) :=
    Probability.continuous_translate.measurable.comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  have ht : QuasiMeasurePreserving
      (fun p : Vec d × FieldPair d => translate (x - p.1) p.2) (volume.prod μ) μ :=
    QuasiMeasurePreserving.prod_of_right hT (Filter.Eventually.of_forall fun z =>
      (EinsteinRelation.measurePreserving_translate μ hμ (x - z)).quasiMeasurePreserving)
  have hp := ht.ae_eq_comp heq
  have hs := ae_ae_of_ae_prod
    (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp)
  filter_upwards [hs] with ω hω
  exact integral_congr_ae (hω.mono fun z hz => congrArg (fun e => k z • e) hz)

/-- The smoothed L² observations agree with the literal real Gaussian
averages. This preserves the actual representatives and bilinear complex convention. -/
theorem smoothedField_eq_real {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (hZ : IsJointObservation Q Z)
    (r : ℝ) (x : Vec d) :
    covarianceSmoothedField Q Z r x =ᵐ[reducedLaw Q]
      fun ω a => (realSmoothedField Q r x ω a : ℂ) := by
  have ha (a : JointObservationIndex d) :
      (fun ω => covarianceSmoothedField Q Z r x ω a) =ᵐ[reducedLaw Q]
        (fun ω => (realSmoothedField Q r x ω a : ℂ)) := by
    rcases a with ⟨j, k⟩ | u
    · have he := integral_translate_congr_ae (reducedLaw Q) (reducedLaw_stationary Q)
        (Z (.inl (j, k))) (fun ω => (commutatorObservation Q j k ω : ℂ))
        (hZ.1 j k) (fun z => (heatKernel 0 r z : ℂ)) x
      filter_upwards [he] with ω hω
      simpa only [covarianceSmoothedField, realSmoothedField, smul_eq_mul,
        ← Complex.ofReal_mul, integral_complex_ofReal] using hω
    · have he := integral_translate_congr_ae (reducedLaw Q) (reducedLaw_stationary Q)
        (Z (.inr ())) (fun ω => (Clock.centredClock Q ω : ℂ))
        hZ.2 (fun z => (heatKernel 0 r z : ℂ)) x
      cases u
      filter_upwards [he] with ω hω
      simpa only [covarianceSmoothedField, realSmoothedField, smul_eq_mul,
        ← centeredClockField_eq_translate, ← Complex.ofReal_mul, integral_complex_ofReal] using hω
  exact (ae_all_iff.mpr ha).mono fun ω hω => funext hω

/-- The literal complex smoothed field is jointly Borel measurable. -/
theorem smoothedField_measurable {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (r : ℝ) :
    Measurable (fun p : Vec d × FieldPair d => covarianceSmoothedField Q Z r p.1 p.2) := by
  have hk : Measurable (heatKernel (0 : Vec d) r) := by
    change Measurable (fun z : Vec d => Correctors.euclideanHeatKernel (r ^ 2) (z - 0))
    simpa only [sub_zero] using
      (Correctors.continuous_euclideanHeatKernel (d := d) (r ^ 2)).measurable
  have hT : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      translate (p.1.1 - p.2) p.1.2) :=
    Probability.continuous_translate.measurable.comp
      ((measurable_fst.fst.sub measurable_snd).prodMk measurable_fst.snd)
  apply Measurable.of_eval
  intro a
  exact (((Complex.continuous_ofReal.measurable.comp (hk.comp measurable_snd)).mul
    ((Lp.stronglyMeasurable (Z a)).measurable.comp hT)).stronglyMeasurable.integral_prod_right).measurable

/-- Equality of the literal pairings after replacing only the null-set
representative of the joint observations. -/
theorem smoothedPairing_eq_real {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (hZ : IsJointObservation Q Z)
    (R r : ℝ) (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    covarianceSmoothedPairing Q Z R r F =ᵐ[reducedLaw Q]
      fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
        ∫ x, ∑ a, F (R⁻¹ • x) a * (realSmoothedField Q r x ω a : ℂ) := by
  have hm : Measurable (fun p : Vec d × FieldPair d =>
      fun a => (realSmoothedField Q r p.1 p.2 a : ℂ)) := by
    apply Measurable.of_eval
    intro a
    exact Complex.continuous_ofReal.measurable.comp
      ((measurable_pi_apply a).comp (realSmoothedField_measurable Q r))
  have hp : (fun p : Vec d × FieldPair d => covarianceSmoothedField Q Z r p.1 p.2) =ᵐ[
      volume.prod (reducedLaw Q)] (fun p a => (realSmoothedField Q r p.1 p.2 a : ℂ)) :=
    (ae_prod_iff_ae_ae (measurableSet_eq_fun (smoothedField_measurable Q Z r) hm)).mpr
      (Filter.Eventually.of_forall fun x => smoothedField_eq_real Q Z hZ r x)
  have hs := ae_ae_of_ae_prod
    (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp)
  filter_upwards [hs] with ω hω
  apply congrArg (fun z => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * z)
  apply integral_congr_ae
  filter_upwards [hω] with x hx
  change covarianceSmoothedField Q Z r x ω = (fun a => (realSmoothedField Q r x ω a : ℂ)) at hx
  rw [hx]

/-- The real smoothed pairing minus the localized pairing is the integral
of their difference. Spatial integrability is obtained from localization and
the actual vector replacement estimate before using linearity of the integral. -/
theorem smoothedPairing_sub_localized_eq_error
    (hcoarse : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt)
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (hZ : IsJointObservation Q Z)
    (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (R : ℝ) (hR : R ≠ 0)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (fun ω => covarianceSmoothedPairing Q Z R r F ω -
      covarianceLocalizedPairing d hd D s δ γ η β h Q R r F ω) =ᵐ[reducedLaw Q]
      fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ x,
        ∑ a, F (R⁻¹ • x) a * ((realSmoothedField Q r x ω a -
          covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℝ) : ℂ) := by
  obtain ⟨C, hC, hb⟩ := realSmoothed_localized_l2_bound hcoarse hloc d hd D s δ γ η β h
  obtain ⟨_, _, _, hfield⟩ := hloc d hd D s δ γ η β h
  obtain ⟨hm, hx⟩ := hfield Q hQ r hr
  let v := covarianceLocalizedField d hd D s δ γ η β h Q r
  have hv (x : Vec d) : S1.L2Vec (reducedLaw Q) (v x) :=
    l2Vec_of_coord fun a => ((hx x).1 a).1
  have hsize (x : Vec d) : S1.vl2 (reducedLaw Q) (v x) =
      S1.vl2 (reducedLaw Q) (v 0) :=
    vl2_eq_of_ae_comp (hv x) (hv 0)
      (EinsteinRelation.measurePreserving_translate (reducedLaw Q)
        (reducedLaw_stationary Q) x) (hx x).2.2.1
  obtain ⟨hlsec, _, _⟩ := weighted_bilinear_integral_bound (reducedLaw Q) volume
    (fun x => F (R⁻¹ • x))
    (F.continuous.measurable.comp (measurable_id.const_smul R⁻¹))
    (F.integrable.comp_smul (inv_ne_zero hR))
    (fun p => v p.1 p.2) hm hv (S1.vl2 (reducedLaw Q) (v 0))
    (S1.vl2_nonneg _ _) (fun x => (hsize x).le)
  have hrpos : 0 < r := by linarith [D.one_le_dependenceRange]
  have hsum : 0 ≤ r ^ (-(d : ℝ)) + r ^ (-γ) :=
    add_nonneg (Real.rpow_nonneg hrpos.le _) (Real.rpow_nonneg hrpos.le _)
  obtain ⟨hesec, _, _⟩ := weighted_bilinear_integral_bound (reducedLaw Q) volume
    (fun x => F (R⁻¹ • x))
    (F.continuous.measurable.comp (measurable_id.const_smul R⁻¹))
    (F.integrable.comp_smul (inv_ne_zero hR))
    (fun p => realSmoothedField Q r p.1 p.2 - v p.1 p.2)
    ((realSmoothedField_measurable Q r).aestronglyMeasurable.sub hm)
    (fun x => (hb Q hQ r hr x).1)
    (C * (r ^ (-(d : ℝ)) + r ^ (-γ))) (mul_nonneg hC.le hsum)
    (fun x => (hb Q hQ r hr x).2)
  filter_upwards [smoothedPairing_eq_real Q Z hZ R r F, hlsec, hesec] with ω he hl heint
  have halg (x : Vec d) :
      (∑ a, F (R⁻¹ • x) a * (realSmoothedField Q r x ω a : ℂ)) =
      (∑ a, F (R⁻¹ • x) a * ((realSmoothedField Q r x ω a - v x ω a : ℝ) : ℂ)) +
      (∑ a, F (R⁻¹ • x) a * (v x ω a : ℂ)) := by
    simp only [Complex.ofReal_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  have hi := integral_add heint hl
  change (∫ x, (∑ a, F (R⁻¹ • x) a *
    ((realSmoothedField Q r x ω a - v x ω a : ℝ) : ℂ)) +
    (∑ a, F (R⁻¹ • x) a * (v x ω a : ℂ))) = _ at hi
  rw [he]
  change _ - ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
    (∫ x, ∑ a, F (R⁻¹ • x) a * (v x ω a : ℂ)) = _
  simp_rw [halg]
  rw [hi, mul_add, add_sub_cancel_right]
  rfl

/-- The complete localized replacement estimate for the literal complex
pairings, including square integrability of both pairings. -/
theorem smoothedPairing_localized_bound
    (hcoarse : node_p_u3A_covariance_u23_coarse_u2D_identificationStmt)
    (hloc : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β)
    (N : ℕ) (hN : d < N) :
    ∃ C : ℝ, 0 < C ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
        HasSmoothBounds D Q →
        ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
        ∀ r : ℝ, 2 * D.dependenceRange ≤ r → ∀ R : ℝ, 0 < R →
        ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        MemLp (covarianceSmoothedPairing Q Z R r F) 2 (reducedLaw Q) ∧
        MemLp (covarianceLocalizedPairing d hd D s δ γ η β h Q R r F) 2 (reducedLaw Q) ∧
        covarianceComplexL2Size (reducedLaw Q)
          (fun ω => covarianceSmoothedPairing Q Z R r F ω -
            covarianceLocalizedPairing d hd D s δ γ η β h Q R r F ω) ≤
          C * schwartzTestNorm N F * R ^ ((d : ℝ) / 2) *
            (r ^ (-(d : ℝ)) + r ^ (-γ)) := by
  obtain ⟨C, hC, hb⟩ := realSmoothed_localized_test_error_bound hcoarse hloc
    d hd D s δ γ η β h N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ r hr R hR F
  obtain ⟨he, heb⟩ := hb Q hQ r hr R hR F
  have heq := smoothedPairing_sub_localized_eq_error hcoarse hloc d hd D s δ γ η β h
    Q hQ Z hZ r hr R hR.ne' F
  have hdiff := (memLp_congr_ae heq).mpr he
  have hlocal := localizedPairing_memLp hloc d hd D s δ γ η β h Q hQ r hr R hR.ne' F
  have hsmooth : MemLp (covarianceSmoothedPairing Q Z R r F) 2 (reducedLaw Q) := by
    convert hdiff.add hlocal using 1
    funext ω
    exact (sub_add_cancel _ _).symm
  refine ⟨hsmooth, hlocal, ?_⟩
  have hn := integral_congr_ae (heq.mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)
  change Real.sqrt _ ≤ _
  rw [hn]
  exact heb

/-- The normalized isotropic heat semigroup preserves a uniform bound. No
regularity of the tested function is needed for this integral estimate. -/
theorem heatConvolution_norm_le {d : ℕ} {K : Vec d → ℝ} {M t : ℝ}
    (ht : 0 ≤ t) (hK : ∀ x, ‖K x‖ ≤ M) (y : Vec d) :
    ‖Correctors.heatKernelConvolution t K y‖ ≤ M := by
  rw [Correctors.heatKernelConvolution_eq_scaled_nonneg ht]
  have hb := norm_integral_le_of_norm_le
    ((Correctors.integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const M)
    (ae_of_all _ fun z => show
      ‖Correctors.euclideanHeatKernel 1 z * K (Real.sqrt t • z + y)‖ ≤
        Correctors.euclideanHeatKernel 1 z * M by
      rw [norm_mul, Real.norm_of_nonneg
        (Correctors.euclideanHeatKernel_nonneg zero_le_one z)]
      exact mul_le_mul_of_nonneg_left (hK _) (Correctors.euclideanHeatKernel_nonneg
        zero_le_one z))
  simpa only [integral_mul_const, Correctors.integral_euclideanHeatKernel zero_lt_one,
    one_mul] using hb

/-- The heat remainder costs two spatial derivatives. The constant is the
uniform Laplacian bound and the time is the square of the physical radius. -/
theorem heatConvolution_sub_norm_le {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K) {M t : ℝ}
    (ht : 0 ≤ t) (hΔ : ∀ x, ‖Correctors.coordLaplacian K x‖ ≤ M) (y : Vec d) :
    ‖Correctors.heatKernelConvolution t K y - K y‖ ≤ M * t := by
  rw [Correctors.heatKernelConvolution_sub_initial hK hKc y ht]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (C := M) (fun u hu =>
      heatConvolution_norm_le (t := u) (by
        rw [Set.uIoc_of_le ht] at hu
        exact hu.1.le) hΔ y)
  simpa only [sub_zero, abs_of_nonneg ht] using hb

/-- The first compensated heat orbit has an extra time factor in its
remainder. This identity is the first multiscale cancellation step; it uses
four spatial derivatives rather than derivatives of a high Schwartz norm. -/
theorem heatConvolution_compensated_identity {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ 2 K) (hΔ : ContDiff ℝ 2 (Correctors.coordLaplacian K))
    (hKc : HasCompactSupport K) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    K y = Correctors.heatKernelConvolution T K y -
      T * Correctors.heatKernelConvolution T (Correctors.coordLaplacian K) y +
      ∫ t in (0 : ℝ)..T, t * Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian (Correctors.coordLaplacian K)) y := by
  have hΔc := Correctors.hasCompactSupport_coordLaplacian hKc
  have hΔΔc := Correctors.hasCompactSupport_coordLaplacian hΔc
  have hc := Correctors.continuousOn_heatKernelConvolution hK.continuous hKc y
  have hΔcont := Correctors.continuousOn_heatKernelConvolution hΔ.continuous hΔc y
  have hΔΔcont := Correctors.continuousOn_heatKernelConvolution
    (Correctors.continuous_coordLaplacian hΔ) hΔΔc y
  have hsub : Set.Icc 0 T ⊆ Set.Ici 0 := fun _ hx => hx.1
  have hsubu : Set.uIcc 0 T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]
    exact hsub
  have hd (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      HasDerivAt (fun u => Correctors.heatKernelConvolution u K y -
        u * Correctors.heatKernelConvolution u (Correctors.coordLaplacian K) y)
        (- (t * Correctors.heatKernelConvolution t
          (Correctors.coordLaplacian (Correctors.coordLaplacian K)) y)) t := by
    convert (Correctors.hasDerivAt_heatKernelConvolution hK hKc y ht.1).sub
      ((hasDerivAt_id t).mul
        (Correctors.hasDerivAt_heatKernelConvolution hΔ hΔc y ht.1)) using 1
    · rfl
    · simp only [id_eq]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    ((hc.mono hsub).sub (continuousOn_id.mul (hΔcont.mono hsub))) hd
    (((continuousOn_id.mul hΔΔcont).neg.mono hsubu).intervalIntegrable)
  rw [intervalIntegral.integral_neg] at hi
  have hzero : Correctors.heatKernelConvolution 0 K y = K y := by
    simp [Correctors.heatKernelConvolution]
  simp only [Pi.sub_apply, Pi.mul_apply, id_eq, hzero, zero_mul, sub_zero] at hi
  linarith

/-- Integration by parts in heat time transfers a weighted heat moment to
one extra Laplacian. Iteration gives the finite compensated heat expansion. -/
theorem heatConvolution_weighted_identity {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K) (n : ℕ)
    (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    ((n + 1 : ℕ) : ℝ) *
        (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t K y) +
      (∫ t in (0 : ℝ)..T, t ^ (n + 1) * Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian K) y) =
      T ^ (n + 1) * Correctors.heatKernelConvolution T K y := by
  have hc := Correctors.continuousOn_heatKernelConvolution hK.continuous hKc y
  have hΔc := Correctors.hasCompactSupport_coordLaplacian hKc
  have hΔcont := Correctors.continuousOn_heatKernelConvolution
    (Correctors.continuous_coordLaplacian hK) hΔc y
  have hsub : Set.Icc 0 T ⊆ Set.Ici 0 := fun _ hx => hx.1
  have hsubu : Set.uIcc 0 T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]
    exact hsub
  have hi₁ : IntervalIntegrable
      (fun t : ℝ => t ^ n * Correctors.heatKernelConvolution t K y) volume 0 T :=
    (((continuousOn_id.pow n).mul hc).mono hsubu).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t : ℝ => t ^ (n + 1) *
      Correctors.heatKernelConvolution t (Correctors.coordLaplacian K) y) volume 0 T :=
    (((continuousOn_id.pow (n + 1)).mul hΔcont).mono hsubu).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      HasDerivAt (fun u => u ^ (n + 1) * Correctors.heatKernelConvolution u K y)
        (((n + 1 : ℕ) : ℝ) * (t ^ n * Correctors.heatKernelConvolution t K y) +
          t ^ (n + 1) * Correctors.heatKernelConvolution t
            (Correctors.coordLaplacian K) y) t := by
    convert (hasDerivAt_pow (n + 1) t).mul
      (Correctors.hasDerivAt_heatKernelConvolution hK hKc y ht.1) using 1
    simp only [Nat.add_sub_cancel]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (((continuousOn_id.pow (n + 1)).mul hc).mono hsub) hd
    ((hi₁.const_mul _).add hi₂)
  rw [intervalIntegral.integral_add (hi₁.const_mul _) hi₂,
    intervalIntegral.integral_const_mul] at hi
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq,
    zero_pow (Nat.succ_ne_zero n), zero_mul, sub_zero] using hi

/-- A bounded heat orbit has integrable polynomial time weights, with the
explicit moment bound used for the small physical scales in a heat expansion. -/
theorem heatConvolution_weighted_norm_le {d : ℕ} {K : Vec d → ℝ} {M T : ℝ}
    (hK : ∀ x, ‖K x‖ ≤ M) (hT : 0 ≤ T) (n : ℕ) (y : Vec d) :
    ‖∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t K y‖ ≤
      T ^ (n + 1) / ((n + 1 : ℕ) : ℝ) * M := by
  have hi : IntervalIntegrable (fun t : ℝ => t ^ n * M) volume 0 T :=
    ((continuous_pow n).mul continuous_const).intervalIntegrable 0 T
  have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hT
    (ae_of_all _ fun t ht => show
      ‖t ^ n * Correctors.heatKernelConvolution t K y‖ ≤ t ^ n * M by
      rw [norm_mul, Real.norm_of_nonneg (pow_nonneg ht.1.le n)]
      exact mul_le_mul_of_nonneg_left (heatConvolution_norm_le ht.1.le hK y)
        (pow_nonneg ht.1.le n))
    hi
  simpa only [intervalIntegral.integral_mul_const, integral_pow,
    zero_pow (Nat.succ_ne_zero n), sub_zero, Nat.cast_add, Nat.cast_one] using hb

/-- The heat orbit is continuous at the initial time for any bounded
continuous test, including noncompact Schwartz tests. -/
theorem heatConvolution_continuousOn_of_bound {d : ℕ} {K : Vec d → ℝ}
    (hK : Continuous K) {M : ℝ} (hM : ∀ x, ‖K x‖ ≤ M) (y : Vec d) :
    ContinuousOn (fun t => Correctors.heatKernelConvolution t K y) (Set.Ici 0) := by
  have hc : Continuous (fun t : ℝ => ∫ z : Vec d,
      Correctors.euclideanHeatKernel 1 z * K (Real.sqrt t • z + y)) := by
    apply continuous_of_dominated
      (bound := fun z => Correctors.euclideanHeatKernel 1 z * M)
    · exact fun t => ((Correctors.continuous_euclideanHeatKernel 1).mul
        (hK.comp (by fun_prop : Continuous fun z : Vec d =>
          Real.sqrt t • z + y))).aestronglyMeasurable
    · exact fun t => ae_of_all _ fun z => by
        rw [norm_mul, Real.norm_of_nonneg
          (Correctors.euclideanHeatKernel_nonneg zero_le_one z)]
        exact mul_le_mul_of_nonneg_left (hM _)
          (Correctors.euclideanHeatKernel_nonneg zero_le_one z)
    · exact (Correctors.integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const M
    · exact ae_of_all _ fun z => continuous_const.mul
        (hK.comp (by fun_prop : Continuous fun t : ℝ => Real.sqrt t • z + y))
  exact hc.continuousOn.congr fun t ht =>
    Correctors.heatKernelConvolution_eq_scaled_nonneg ht K y

/-- Every finite Laplacian iterate of a smooth compact test remains a smooth
compact test. This supplies the heat-time identities at each expansion order. -/
theorem laplacian_iterate_regular {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Correctors.coordLaplacian^[n] K) ∧
      HasCompactSupport (Correctors.coordLaplacian^[n] K) := by
  induction n with
  | zero => exact ⟨hK, hKc⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    refine ⟨?_, Correctors.hasCompactSupport_coordLaplacian ih.2⟩
    apply ContDiff.sum
    intro i _
    have hd := ((contDiff_infty_iff_fderiv.mp ih.1).2).clm_apply
      (contDiff_const (c := unitVector i))
    exact ((contDiff_infty_iff_fderiv.mp hd).2).clm_apply contDiff_const

/-- Finite heat expansion with an explicit weighted remainder. Each additional
term uses one Laplacian; the identity does not require differentiating a
Schwartz seminorm. -/
theorem heatConvolution_finite_expansion {d : ℕ} {K : Vec d → ℝ}
    (hK : ContDiff ℝ (⊤ : ℕ∞) K) (hKc : HasCompactSupport K)
    (n : ℕ) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    K y = (∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * T ^ j / (Nat.factorial j : ℝ) *
        Correctors.heatKernelConvolution T (Correctors.coordLaplacian^[j] K) y) +
      (-1 : ℝ) ^ (n + 1) / (Nat.factorial n : ℝ) *
        ∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t
          (Correctors.coordLaplacian^[n + 1] K) y := by
  induction n with
  | zero =>
    have hi := Correctors.heatKernelConvolution_sub_initial
      (hK.of_le (by simp)) hKc y hT
    simpa [sub_eq_add_neg] using (show K y = Correctors.heatKernelConvolution T K y -
      ∫ t in (0 : ℝ)..T, Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian K) y by linarith)
  | succ n ih =>
    have hr := laplacian_iterate_regular hK hKc (n + 1)
    have hi := heatConvolution_weighted_identity (hr.1.of_le (by simp))
      hr.2 n y hT
    rw [← Function.iterate_succ_apply' Correctors.coordLaplacian (n + 1) K] at hi
    rw [Finset.sum_range_succ]
    rw [ih]
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm : (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian^[n + 1] K) y) =
        (T ^ (n + 1) * Correctors.heatKernelConvolution T
          (Correctors.coordLaplacian^[n + 1] K) y -
          ∫ t in (0 : ℝ)..T, t ^ (n + 1) * Correctors.heatKernelConvolution t
            (Correctors.coordLaplacian^[n + 2] K) y) / ((n + 1 : ℕ) : ℝ) := by
      apply (eq_div_iff hn).mpr
      linarith [hi]
    rw [hm]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
    ring

/-- A coordinate derivative within Schwartz space, on the inherited coordinate carrier. -/
noncomputable def schwartzCoordDerivative {d : ℕ} (i : Fin d)
    (K : SchwartzMap (Vec d) ℝ) : SchwartzMap (Vec d) ℝ :=
  SchwartzMap.evalCLM ℝ (Vec d) ℝ (unitVector i)
    (SchwartzMap.fderivCLM ℝ (Vec d) ℝ K)

@[simp] theorem schwartzCoordDerivative_apply {d : ℕ} (i : Fin d)
    (K : SchwartzMap (Vec d) ℝ) (x : Vec d) :
    schwartzCoordDerivative i K x = fderiv ℝ K x (unitVector i) := rfl

/-- The literal coordinate Laplacian as a Schwartz function. This does not
introduce an inner product norm on the coordinate carrier. -/
noncomputable def schwartzCoordLaplacian {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) : SchwartzMap (Vec d) ℝ :=
  ∑ i : Fin d, schwartzCoordDerivative i (schwartzCoordDerivative i K)

@[simp] theorem schwartzCoordLaplacian_apply {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (x : Vec d) :
    schwartzCoordLaplacian K x = Correctors.coordLaplacian K x := by
  simp only [schwartzCoordLaplacian, _root_.sum_apply,
    schwartzCoordDerivative_apply, Correctors.coordLaplacian]
  apply Finset.sum_congr rfl
  intro i _
  rfl

/-- Taking a finite Laplacian iterate inside Schwartz space preserves the
underlying function exactly. -/
theorem schwartzCoordLaplacian_iterate_coe {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (n : ℕ) :
    ⇑(schwartzCoordLaplacian^[n] K) = Correctors.coordLaplacian^[n] ⇑K := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (funext (schwartzCoordLaplacian_apply _)).trans (congrArg _ ih)

/-- Noncompact Schwartz tests have integrable, uniformly bounded Laplacian
iterates at every order. -/
theorem laplacian_iterate_schwartz_regular {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Correctors.coordLaplacian^[n] ⇑K) ∧
      Integrable (Correctors.coordLaplacian^[n] ⇑K) ∧
      ∃ M : ℝ, ∀ x, ‖(Correctors.coordLaplacian^[n] ⇑K) x‖ ≤ M := by
  rw [← schwartzCoordLaplacian_iterate_coe]
  let L := schwartzCoordLaplacian^[n] K
  refine ⟨L.smooth ⊤, L.integrable, SchwartzMap.seminorm ℝ 0 0 L, ?_⟩
  intro x
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
    SchwartzMap.le_seminorm ℝ 0 0 L x

/-- Two integrations by parts for Schwartz tests, without compact support. -/
theorem integral_schwartz_mul_coordLaplacian_eq {d : ℕ}
    (K L : SchwartzMap (Vec d) ℝ) :
    (∫ x, K x * Correctors.coordLaplacian L x) =
      ∫ x, Correctors.coordLaplacian K x * L x := by
  have hi (A B : SchwartzMap (Vec d) ℝ) : Integrable (fun x => A x * B x) := by
    exact B.integrable.bdd_mul A.continuous.aestronglyMeasurable
      (ae_of_all _ fun x => by
        simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero] using
          SchwartzMap.le_seminorm ℝ 0 0 A x)
  have hd (A B : SchwartzMap (Vec d) ℝ) (i : Fin d) :
      (∫ x, A x * schwartzCoordDerivative i B x) =
        -(∫ x, schwartzCoordDerivative i A x * B x) :=
    SchwartzMap.integral_mul_lineDerivOp_right_eq_neg_left A B (unitVector i)
  simp_rw [← schwartzCoordLaplacian_apply, schwartzCoordLaplacian,
    _root_.sum_apply, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi K
    (schwartzCoordDerivative i (schwartzCoordDerivative i L))),
    integral_finsetSum _ (fun i _ => hi
      (schwartzCoordDerivative i (schwartzCoordDerivative i K)) L)]
  apply Finset.sum_congr rfl
  intro i _
  rw [hd K (schwartzCoordDerivative i L) i, hd (schwartzCoordDerivative i K) L i,
    neg_neg]

/-- The heat orbit of every Schwartz Laplacian iterate is continuous down
to time zero. The test need not have compact support. -/
theorem heatConvolution_schwartz_iterate_continuousOn {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (n : ℕ) (y : Vec d) :
    ContinuousOn (fun t => Correctors.heatKernelConvolution t
      (Correctors.coordLaplacian^[n] ⇑K) y) (Set.Ici 0) := by
  obtain ⟨hK, _, M, hM⟩ := laplacian_iterate_schwartz_regular K n
  exact heatConvolution_continuousOn_of_bound hK.continuous hM y

/-- Every weighted time remainder in the finite expansion is integrable for
Schwartz tests, including at the initial time. -/
theorem heatConvolution_schwartz_weighted_intervalIntegrable {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (n m : ℕ) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun t => t ^ m * Correctors.heatKernelConvolution t
      (Correctors.coordLaplacian^[n] ⇑K) y) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  apply (continuous_pow m).continuousOn.mul
  exact (heatConvolution_schwartz_iterate_continuousOn K n y).mono
    (by simpa only [Set.uIcc_of_le hT] using Set.Icc_subset_Ici_self)

/-- Quadratic Euclidean weights are integrable against any Schwartz test,
including after a fixed spatial translation of the weight. -/
theorem integrable_schwartz_mul_shifted_sq {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) :
    Integrable (fun x => ‖K x‖ * (1 + euclideanSq (x - y))) := by
  have hsq (x : Vec d) : euclideanSq x ≤ (d : ℝ) * ‖x‖ ^ 2 := by
    calc
      euclideanSq x ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
        unfold euclideanSq dot
        apply Finset.sum_le_sum
        intro i _
        have h := norm_le_pi_norm x i
        simpa only [Real.norm_eq_abs, sq_abs, ← pow_two] using
          (sq_le_sq₀ (abs_nonneg (x i)) (norm_nonneg x)).mpr h
      _ = (d : ℝ) * ‖x‖ ^ 2 := by simp
  have hshift (x : Vec d) : euclideanSq (x - y) ≤
      2 * (d : ℝ) * ‖x‖ ^ 2 + 2 * (d : ℝ) * ‖y‖ ^ 2 := by
    have hnorm := norm_sub_le x y
    have hquad : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
      nlinarith only [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x - y‖),
        norm_nonneg (x - y), norm_nonneg x, norm_nonneg y, hnorm]
    calc
      _ ≤ (d : ℝ) * ‖x - y‖ ^ 2 := hsq _
      _ ≤ (d : ℝ) * (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hquad (Nat.cast_nonneg d)
      _ = _ := by ring
  have hi := (K.integrable.norm.const_mul (1 + 2 * (d : ℝ) * ‖y‖ ^ 2)).add
    ((K.integrable_pow_mul volume 2).const_mul (2 * (d : ℝ)))
  apply hi.mono (by dsimp [euclideanSq, dot]; fun_prop)
  filter_upwards [] with x
  have hq : 0 ≤ euclideanSq (x - y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((x - y) i)
  have hn : 0 ≤ ‖K x‖ * (1 + euclideanSq (x - y)) :=
    mul_nonneg (norm_nonneg _) (by linarith)
  have h := mul_le_mul_of_nonneg_left (hshift x) (norm_nonneg (K x))
  calc
    ‖‖K x‖ * (1 + euclideanSq (x - y))‖ =
        ‖K x‖ * (1 + euclideanSq (x - y)) := Real.norm_of_nonneg hn
    _ ≤ (1 + 2 * (d : ℝ) * ‖y‖ ^ 2) * ‖K x‖ +
        2 * (d : ℝ) * (‖x‖ ^ 2 * ‖K x‖) := by nlinarith only [h]
    _ ≤ ‖(1 + 2 * (d : ℝ) * ‖y‖ ^ 2) * ‖K x‖ +
        2 * (d : ℝ) * (‖x‖ ^ 2 * ‖K x‖)‖ := le_abs_self _

/-- A positive-time heat kernel is uniformly bounded by its prefactor. -/
theorem euclideanHeatKernel_norm_le_prefactor {d : ℕ} {t : ℝ} (ht : 0 < t)
    (x : Vec d) :
    ‖Correctors.euclideanHeatKernel t x‖ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
  have hsq : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rw [Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg ht.le x)]
  unfold Correctors.euclideanHeatKernel
  exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _)
    ((Real.exp_le_one_iff).mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hsq)
      (by positivity)))

/-- The time derivative of the isotropic Gaussian has a uniform quadratic
spatial majorant on every compact positive time interval. -/
theorem heatKernel_laplacian_local_bound {d : ℕ} {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, ∀ s ∈ Metric.ball t (t / 2), ∀ x : Vec d,
      ‖Correctors.coordLaplacian (Correctors.euclideanHeatKernel s) x‖ ≤
        B * (1 + euclideanSq x) := by
  let c : ℝ → ℝ := fun s => ‖(4 * Real.pi * s) ^ (-(d : ℝ) / 2)‖ *
    (‖1 / (4 * s ^ 2)‖ + ‖(d : ℝ) / (2 * s)‖)
  have hc : ContinuousOn c (Set.Icc (t / 2) (t + t / 2)) := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs.1
    have h4 : (4 : ℝ) * Real.pi * s ≠ 0 := by positivity
    have ha : ContinuousAt (fun u : ℝ => (4 * Real.pi * u) ^ (-(d : ℝ) / 2)) s :=
      (continuous_const.mul continuous_id).continuousAt.rpow_const (Or.inl h4)
    have hb : ContinuousAt (fun u : ℝ => 1 / (4 * u ^ 2)) s :=
      continuousAt_const.div (by fun_prop) (by positivity)
    have hd : ContinuousAt (fun u : ℝ => (d : ℝ) / (2 * u)) s :=
      continuousAt_const.div (by fun_prop) (by positivity)
    exact (ha.norm.mul (hb.norm.add hd.norm)).continuousWithinAt
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨B, ?_⟩
  intro s hs x
  have hs' : s ∈ Set.Icc (t / 2) (t + t / 2) := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs'.1
  have hq : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  have hnorm : ‖Correctors.euclideanHeatKernel s x‖ ≤
      ‖(4 * Real.pi * s) ^ (-(d : ℝ) / 2)‖ := by
    exact (euclideanHeatKernel_norm_le_prefactor hspos x).trans (le_abs_self _)
  have hbracket : ‖euclideanSq x / (4 * s ^ 2) - (d : ℝ) / (2 * s)‖ ≤
      (‖1 / (4 * s ^ 2)‖ + ‖(d : ℝ) / (2 * s)‖) * (1 + euclideanSq x) := by
    calc
      _ ≤ ‖euclideanSq x / (4 * s ^ 2)‖ + ‖(d : ℝ) / (2 * s)‖ := norm_sub_le _ _
      _ = euclideanSq x * ‖1 / (4 * s ^ 2)‖ + ‖(d : ℝ) / (2 * s)‖ := by
        rw [div_eq_mul_one_div, norm_mul, Real.norm_of_nonneg hq]
      _ ≤ _ := by nlinarith only [norm_nonneg (1 / (4 * s ^ 2)),
        norm_nonneg ((d : ℝ) / (2 * s)), hq]
  rw [Correctors.coordLaplacian_euclideanHeatKernel, norm_mul]
  calc
    _ ≤ ‖(4 * Real.pi * s) ^ (-(d : ℝ) / 2)‖ *
        ((‖1 / (4 * s ^ 2)‖ + ‖(d : ℝ) / (2 * s)‖) * (1 + euclideanSq x)) :=
      mul_le_mul hnorm hbracket (norm_nonneg _) (norm_nonneg _)
    _ = c s * (1 + euclideanSq x) := by dsimp [c]; ring
    _ ≤ B * (1 + euclideanSq x) := mul_le_mul_of_nonneg_right
      ((le_abs_self (c s)).trans (by simpa only [Real.norm_eq_abs] using hB s hs'))
      (by linarith)

/-- Schwartz decay permits differentiation of Gaussian convolution under the
spatial integral at every positive time. -/
theorem hasDerivAt_heatConvolution_schwartz_kernel {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Correctors.heatKernelConvolution s K y)
      (∫ x, K x * Correctors.coordLaplacian
        (Correctors.euclideanHeatKernel t) (x - y)) t := by
  have he : 0 < t / 2 := by positivity
  have hsub : Continuous (fun x : Vec d => x - y) := by fun_prop
  obtain ⟨B, hB⟩ := heatKernel_laplacian_local_bound (d := d) ht
  have hi : Integrable (fun x => K x * Correctors.euclideanHeatKernel t (x - y)) :=
    K.integrable.mul_bdd
      (((Correctors.continuous_euclideanHeatKernel t).comp hsub).aestronglyMeasurable)
      (ae_of_all _ fun x => euclideanHeatKernel_norm_le_prefactor ht (x - y))
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure (Vec d))) (x₀ := t) (s := Metric.ball t (t / 2))
    (F := fun s x => K x * Correctors.euclideanHeatKernel s (x - y))
    (F' := fun s x => K x * Correctors.coordLaplacian
      (Correctors.euclideanHeatKernel s) (x - y))
    (bound := fun x => (‖K x‖ * (1 + euclideanSq (x - y))) * B)
    (Metric.ball_mem_nhds t he)
    (Filter.Eventually.of_forall fun s => (K.continuous.mul
      ((Correctors.continuous_euclideanHeatKernel s).comp hsub)).aestronglyMeasurable)
    hi
    (K.continuous.mul ((Correctors.continuous_coordLaplacian
      (Correctors.contDiff_two_euclideanHeatKernel t)).comp hsub)).aestronglyMeasurable
    (ae_of_all _ fun x s hs => by
      rw [norm_mul]
      calc
        _ ≤ ‖K x‖ * (B * (1 + euclideanSq (x - y))) :=
          mul_le_mul_of_nonneg_left (hB s hs (x - y)) (norm_nonneg _)
        _ = _ := by ring)
    ((integrable_schwartz_mul_shifted_sq K y).mul_const B)
    (ae_of_all _ fun x s hs => by
      have hspos : 0 < s := by
        rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
        linarith [hs.1]
      exact (Correctors.hasDerivAt_euclideanHeatKernel_heat (x - y) hspos).const_mul (K x))
  apply hdiff.2.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds ht.ne'] with s hs
  simp only [Correctors.heatKernelConvolution, ite_eq_right hs]

/-- A quadratic growth bound suffices for spatial testing against a Schwartz
function on the inherited coordinate carrier. -/
theorem integrable_schwartz_mul_of_quadratic_bound {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {g : Vec d → ℝ}
    (hg : AEStronglyMeasurable g) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B * (1 + euclideanSq (x - y))) :
    Integrable (fun x => K x * g x) := by
  apply ((integrable_schwartz_mul_shifted_sq K y).mul_const B).mono
    (K.continuous.aestronglyMeasurable.mul hg)
  filter_upwards [] with x
  change ‖K x * g x‖ ≤ ‖(‖K x‖ * (1 + euclideanSq (x - y))) * B‖
  calc
    _ = ‖K x‖ * ‖g x‖ := norm_mul _ _
    _ ≤ ‖K x‖ * (B * (1 + euclideanSq (x - y))) :=
      mul_le_mul_of_nonneg_left (hB x) (norm_nonneg _)
    _ = (‖K x‖ * (1 + euclideanSq (x - y))) * B := by ring
    _ ≤ ‖(‖K x‖ * (1 + euclideanSq (x - y))) * B‖ := le_abs_self _

/-- The directional derivative of the translated isotropic Gaussian. -/
theorem hasLineDerivAt_shifted_heatKernel {d : ℕ} (t : ℝ) (y x : Vec d)
    (i : Fin d) :
    HasLineDerivAt ℝ (fun z : Vec d => Correctors.euclideanHeatKernel t (z - y))
      (Correctors.euclideanHeatKernel t (x - y) * (-(1 / (2 * t)) * (x - y) i))
      x (unitVector i) := by
  have hd := ((Correctors.contDiff_two_euclideanHeatKernel t).differentiable
    (by norm_num) (x - y)).hasFDerivAt
  have h := (hd.comp x ((hasFDerivAt_id x).sub_const y)).hasLineDerivAt (unitVector i)
  convert h using 1
  · rfl
  · simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      Correctors.fderiv_euclideanHeatKernel]
    simp [unitVector, Pi.single_apply]

/-- The second directional derivative of the translated isotropic Gaussian,
with its quadratic coefficient retained explicitly. -/
theorem hasLineDerivAt_shifted_heatKernel_first {d : ℕ} (t : ℝ) (y x : Vec d)
    (i : Fin d) :
    HasLineDerivAt ℝ
      (fun z : Vec d => Correctors.euclideanHeatKernel t (z - y) *
        (-(1 / (2 * t)) * (z - y) i))
      (Correctors.euclideanHeatKernel t (x - y) * (-(1 / (2 * t))) +
        Correctors.euclideanHeatKernel t (x - y) * (-(1 / (2 * t))) ^ 2 *
          ((x - y) i) ^ 2) x (unitVector i) := by
  have hc : HasLineDerivAt ℝ (fun z : Vec d => (z - y) i) 1 x (unitVector i) := by
    simpa [unitVector] using
      (((hasFDerivAt_apply (𝕜 := ℝ) i x).sub_const (y i)).hasLineDerivAt (unitVector i))
  have h := (hasLineDerivAt_shifted_heatKernel t y x i).mul
    (hc.const_mul (-(1 / (2 * t))))
  unfold HasLineDerivAt
  convert h using 1
  simp only [zero_smul, add_zero]
  ring

/-- Multiplication by the first two coordinate Gaussian derivatives preserves
integrability of a Schwartz test, without a compact-support hypothesis. -/
theorem integrable_schwartz_mul_shifted_heat_polynomial {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {t : ℝ} (ht : 0 < t)
    (i : Fin d) (a b c : ℝ) :
    Integrable (fun x => K x * (Correctors.euclideanHeatKernel t (x - y) *
      (a + b * (x - y) i + c * ((x - y) i) ^ 2))) := by
  let A := (4 * Real.pi * t) ^ (-(d : ℝ) / 2)
  have hA : 0 ≤ A := Real.rpow_nonneg (by positivity) _
  have hp := (Correctors.continuous_euclideanHeatKernel t).comp
    (by fun_prop : Continuous fun x : Vec d => x - y)
  apply integrable_schwartz_mul_of_quadratic_bound K y
    ((hp.mul (by fun_prop)).aestronglyMeasurable)
    (B := A * (‖a‖ + ‖b‖ + ‖c‖))
  intro x
  have hq : 0 ≤ euclideanSq (x - y) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg ((x - y) j)
  have hs : ((x - y) i) ^ 2 ≤ euclideanSq (x - y) := by
    unfold euclideanSq dot
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
        mul_self_nonneg ((x - y) j)) (Finset.mem_univ i))
  have hz : ‖(x - y) i‖ ≤ 1 + euclideanSq (x - y) := by
    rw [Real.norm_eq_abs]
    nlinarith [sq_nonneg (|(x - y) i| - 1), sq_abs ((x - y) i)]
  have hpoly : ‖a + b * (x - y) i + c * ((x - y) i) ^ 2‖ ≤
      (‖a‖ + ‖b‖ + ‖c‖) * (1 + euclideanSq (x - y)) := by
    calc
      _ ≤ ‖a‖ + ‖b * (x - y) i‖ + ‖c * ((x - y) i) ^ 2‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ = ‖a‖ + ‖b‖ * ‖(x - y) i‖ + ‖c‖ * ((x - y) i) ^ 2 := by
        rw [norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hz (norm_nonneg b),
        mul_le_mul_of_nonneg_left hs (norm_nonneg c), norm_nonneg a,
        mul_nonneg (norm_nonneg a) hq, mul_nonneg (norm_nonneg c) hq,
        norm_nonneg c]
  change ‖Correctors.euclideanHeatKernel t (x - y) *
    (a + b * (x - y) i + c * ((x - y) i) ^ 2)‖ ≤ _
  rw [norm_mul]
  exact (mul_le_mul (euclideanHeatKernel_norm_le_prefactor ht (x - y)) hpoly
    (norm_nonneg _) hA).trans_eq (by ring)

/-- Two noncompact integrations by parts transfer the literal Gaussian
Laplacian onto a Schwartz test. -/
theorem integral_schwartz_mul_shifted_heatKernel_laplacian {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {t : ℝ} (ht : 0 < t) :
    (∫ x, K x * Correctors.coordLaplacian (Correctors.euclideanHeatKernel t) (x - y)) =
      ∫ x, Correctors.coordLaplacian K x * Correctors.euclideanHeatKernel t (x - y) := by
  let c := -(1 / (2 * t))
  let g₀ : Vec d → ℝ := fun x => Correctors.euclideanHeatKernel t (x - y)
  let g₁ : Fin d → Vec d → ℝ := fun i x => g₀ x * (c * (x - y) i)
  let g₂ : Fin d → Vec d → ℝ := fun i x =>
    g₀ x * c + g₀ x * c ^ 2 * ((x - y) i) ^ 2
  have hi₀ (L : SchwartzMap (Vec d) ℝ) : Integrable (fun x => L x * g₀ x) := by
    exact L.integrable.mul_bdd
      (((Correctors.continuous_euclideanHeatKernel t).comp
        (by fun_prop : Continuous fun x : Vec d => x - y)).aestronglyMeasurable)
      (ae_of_all _ fun x => euclideanHeatKernel_norm_le_prefactor ht (x - y))
  have hi₁ (L : SchwartzMap (Vec d) ℝ) (i : Fin d) :
      Integrable (fun x => L x * g₁ i x) := by
    simpa [g₁, g₀] using
      integrable_schwartz_mul_shifted_heat_polynomial L y ht i 0 c 0
  have hi₂ (L : SchwartzMap (Vec d) ℝ) (i : Fin d) :
      Integrable (fun x => L x * g₂ i x) := by
    convert integrable_schwartz_mul_shifted_heat_polynomial L y ht i c 0 (c ^ 2) using 1
    ext x
    dsimp [g₂, g₀]
    ring
  have hder (L : SchwartzMap (Vec d) ℝ) (i : Fin d) (x : Vec d) :
      HasLineDerivAt ℝ L (schwartzCoordDerivative i L x) x (unitVector i) := by
    simpa only [HasLineDerivAt, schwartzCoordDerivative_apply] using
      (SchwartzMap.hasFDerivAt L x).hasLineDerivAt (unitVector i)
  have hibp (i : Fin d) : (∫ x, K x * g₂ i x) =
      ∫ x, schwartzCoordDerivative i (schwartzCoordDerivative i K) x * g₀ x := by
    have hleft := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (v := unitVector i)
      (hi₁ (schwartzCoordDerivative i K) i) (hi₂ K i) (hi₁ K i)
      (fun x _ => hder K i x)
      (fun x _ => hasLineDerivAt_shifted_heatKernel_first t y x i)
    have hright := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
      (B := ContinuousLinearMap.mul ℝ ℝ) (v := unitVector i)
      (hi₀ (schwartzCoordDerivative i (schwartzCoordDerivative i K)))
      (hi₁ (schwartzCoordDerivative i K) i) (hi₀ (schwartzCoordDerivative i K))
      (fun x _ => hder (schwartzCoordDerivative i K) i x)
      (fun x _ => hasLineDerivAt_shifted_heatKernel t y x i)
    change (∫ x, K x * g₂ i x) = -(∫ x, schwartzCoordDerivative i K x * g₁ i x) at hleft
    change (∫ x, schwartzCoordDerivative i K x * g₁ i x) =
      -(∫ x, schwartzCoordDerivative i (schwartzCoordDerivative i K) x * g₀ x) at hright
    rw [hleft, hright, neg_neg]
  have hsum (x : Vec d) :
      Correctors.coordLaplacian (Correctors.euclideanHeatKernel t) (x - y) =
        ∑ i : Fin d, g₂ i x := by
    rw [Correctors.coordLaplacian_euclideanHeatKernel]
    dsimp [g₂, g₀]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    dsimp [c, euclideanSq, dot]
    simp only [← pow_two]
    field_simp
    ring
  simp_rw [hsum, Finset.mul_sum, ← schwartzCoordLaplacian_apply,
    schwartzCoordLaplacian, _root_.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi₂ K i),
    integral_finsetSum _ (fun i _ => hi₀
      (schwartzCoordDerivative i (schwartzCoordDerivative i K)))]
  exact Finset.sum_congr rfl fun i _ => hibp i

/-- The positive-time heat equation for a Schwartz test, with the Laplacian
on the test rather than on the Gaussian. -/
theorem hasDerivAt_heatConvolution_schwartz {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Correctors.heatKernelConvolution s K y)
      (Correctors.heatKernelConvolution t (Correctors.coordLaplacian K) y) t := by
  have h := hasDerivAt_heatConvolution_schwartz_kernel K y ht
  rw [integral_schwartz_mul_shifted_heatKernel_laplacian K y ht] at h
  convert h using 1
  simp only [Correctors.heatKernelConvolution, ite_eq_right ht.ne']

/-- The integrated heat equation for Schwartz tests includes the initial time. -/
theorem heatConvolution_schwartz_sub_initial {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    Correctors.heatKernelConvolution T K y - K y =
      ∫ t in (0 : ℝ)..T, Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian K) y := by
  have hc := heatConvolution_schwartz_iterate_continuousOn K 0 y
  have hi := heatConvolution_schwartz_weighted_intervalIntegrable K 1 0 y hT
  simp only [Function.iterate_zero, Function.id_def] at hc
  simp only [Function.iterate_one, pow_zero, one_mul] at hi
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (hc.mono (fun _ hx => hx.1))
    (fun _ ht => hasDerivAt_heatConvolution_schwartz K y ht.1) hi
  have hzero : Correctors.heatKernelConvolution 0 K y = K y := by
    simp [Correctors.heatKernelConvolution]
  rw [hzero] at h
  exact h.symm

/-- Integration by parts in heat time transfers a weighted heat moment to
one extra Laplacian. Iteration gives the finite compensated heat expansion. -/
theorem heatConvolution_schwartz_weighted_identity {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (n : ℕ)
    (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    ((n + 1 : ℕ) : ℝ) *
        (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t K y) +
      (∫ t in (0 : ℝ)..T, t ^ (n + 1) * Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian K) y) =
      T ^ (n + 1) * Correctors.heatKernelConvolution T K y := by
  have hc := heatConvolution_schwartz_iterate_continuousOn K 0 y
  have hΔcont := heatConvolution_schwartz_iterate_continuousOn K 1 y
  simp only [Function.iterate_zero, Function.id_def] at hc
  simp only [Function.iterate_one] at hΔcont
  have hsub : Set.Icc 0 T ⊆ Set.Ici 0 := fun _ hx => hx.1
  have hsubu : Set.uIcc 0 T ⊆ Set.Ici 0 := by
    rw [Set.uIcc_of_le hT]
    exact hsub
  have hi₁ : IntervalIntegrable
      (fun t : ℝ => t ^ n * Correctors.heatKernelConvolution t K y) volume 0 T :=
    (((continuousOn_id.pow n).mul hc).mono hsubu).intervalIntegrable
  have hi₂ : IntervalIntegrable (fun t : ℝ => t ^ (n + 1) *
      Correctors.heatKernelConvolution t (Correctors.coordLaplacian K) y) volume 0 T :=
    (((continuousOn_id.pow (n + 1)).mul hΔcont).mono hsubu).intervalIntegrable
  have hd (t : ℝ) (ht : t ∈ Set.Ioo 0 T) :
      HasDerivAt (fun u => u ^ (n + 1) * Correctors.heatKernelConvolution u K y)
        (((n + 1 : ℕ) : ℝ) * (t ^ n * Correctors.heatKernelConvolution t K y) +
          t ^ (n + 1) * Correctors.heatKernelConvolution t
            (Correctors.coordLaplacian K) y) t := by
    convert (hasDerivAt_pow (n + 1) t).mul
      (hasDerivAt_heatConvolution_schwartz K y ht.1) using 1
    simp only [Nat.add_sub_cancel]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT
    (((continuousOn_id.pow (n + 1)).mul hc).mono hsub) hd
    ((hi₁.const_mul _).add hi₂)
  rw [intervalIntegral.integral_add (hi₁.const_mul _) hi₂,
    intervalIntegral.integral_const_mul] at hi
  simpa only [Pi.mul_apply, Pi.pow_apply, id_eq,
    zero_pow (Nat.succ_ne_zero n), zero_mul, sub_zero] using hi

/-- Finite heat expansion with an explicit weighted remainder. Each additional
term uses one Laplacian; the identity does not require differentiating a
Schwartz seminorm. -/
theorem heatConvolution_schwartz_finite_expansion {d : ℕ}
    (K : SchwartzMap (Vec d) ℝ)
    (n : ℕ) (y : Vec d) {T : ℝ} (hT : 0 ≤ T) :
    K y = (∑ j ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ j * T ^ j / (Nat.factorial j : ℝ) *
        Correctors.heatKernelConvolution T (Correctors.coordLaplacian^[j] ⇑K) y) +
      (-1 : ℝ) ^ (n + 1) / (Nat.factorial n : ℝ) *
        ∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t
          (Correctors.coordLaplacian^[n + 1] ⇑K) y := by
  induction n with
  | zero =>
    have hi := heatConvolution_schwartz_sub_initial K y hT
    simpa [sub_eq_add_neg] using (show K y = Correctors.heatKernelConvolution T K y -
      ∫ t in (0 : ℝ)..T, Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian K) y by linarith)
  | succ n ih =>
    have hi := heatConvolution_schwartz_weighted_identity
      (schwartzCoordLaplacian^[n + 1] K) n y hT
    rw [schwartzCoordLaplacian_iterate_coe] at hi
    rw [← Function.iterate_succ_apply' Correctors.coordLaplacian (n + 1) ⇑K] at hi
    rw [Finset.sum_range_succ]
    rw [ih]
    have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
    have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hm : (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t
        (Correctors.coordLaplacian^[n + 1] ⇑K) y) =
        (T ^ (n + 1) * Correctors.heatKernelConvolution T
          (Correctors.coordLaplacian^[n + 1] ⇑K) y -
          ∫ t in (0 : ℝ)..T, t ^ (n + 1) * Correctors.heatKernelConvolution t
            (Correctors.coordLaplacian^[n + 2] ⇑K) y) / ((n + 1 : ℕ) : ℝ) := by
      apply (eq_div_iff hn).mpr
      linarith [hi]
    rw [hm]
    simp only [Nat.factorial_succ, Nat.cast_mul, pow_succ]
    field_simp
    ring


private lemma norm_iteratedFDeriv_affine {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : E →L[ℝ] F) (b : F) (x : E) {B : ℝ} (hB : 1 ≤ B)
    (h0 : ‖b + T x‖ ≤ B) (h1 : ‖T‖ ≤ B) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun y => b + T y) x‖ ≤ B ^ (n + 1) := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero, Nat.zero_add, pow_one] using h0
  | succ n =>
    have heq : fderiv ℝ (fun y => b + T y) = fun _ => T := by
      ext y
      rw [fderiv_const_add, T.fderiv]
    rw [← norm_iteratedFDeriv_fderiv, heq]
    cases n with
    | zero =>
      rw [norm_iteratedFDeriv_zero]
      exact h1.trans (le_self_pow₀ hB (by omega))
    | succ n =>
      rw [iteratedFDeriv_succ_const]
      simp only [Pi.zero_apply, norm_zero]
      exact pow_nonneg (le_trans (by norm_num) hB) _

private lemma norm_iteratedFDeriv_affine_log {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (T : E →L[ℝ] (E →L[ℝ] ℝ)) (b : E →L[ℝ] ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hdf : fderiv ℝ f = fun y => f y • (b + T y))
    (x : E) {B : ℝ} (hB : 1 ≤ B) (h0 : ‖b + T x‖ ≤ B) (h1 : ‖T‖ ≤ B)
    (n : ℕ) :
    ‖iteratedFDeriv ℝ n f x‖ ≤ (2 : ℝ) ^ (n ^ 2) * B ^ n * ‖f x‖ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp [norm_iteratedFDeriv_zero]
    | succ n =>
      rw [← norm_iteratedFDeriv_fderiv, hdf]
      have hsum := norm_iteratedFDeriv_smul_le hf
        ((contDiff_const (c := b)).add T.contDiff) x (n := n) (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      apply hsum.trans
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            ((2 : ℝ) ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) := by
          apply Finset.sum_le_sum
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          have hpow : (2 : ℝ) ^ (i ^ 2) ≤ 2 ^ (n ^ 2) :=
            pow_le_pow_right₀ (by norm_num) (Nat.pow_le_pow_left hin 2)
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left
              ((ih i (by omega)).trans (by gcongr)) (Nat.cast_nonneg _)
          · exact norm_iteratedFDeriv_affine T b x hB h0 h1 _
          · exact norm_nonneg _
          · positivity
        _ = (2 : ℝ) ^ n * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) := by
          have hi (i : ℕ) (hi : i ∈ Finset.range (n + 1)) :
              (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) =
                (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) := by
            have hie : i + (n - i + 1) = n + 1 := by
              have := Finset.mem_range.mp hi
              omega
            rw [show (n.choose i : ℝ) * (2 ^ (n ^ 2) * B ^ i * ‖f x‖) * B ^ (n - i + 1) =
              (n.choose i : ℝ) * (2 ^ (n ^ 2) * (B ^ i * B ^ (n - i + 1)) * ‖f x‖) by ring,
              ← pow_add, hie]
          rw [Finset.sum_congr rfl hi, ← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose n
        _ ≤ _ := by
          rw [show (2 : ℝ) ^ n * (2 ^ (n ^ 2) * B ^ (n + 1) * ‖f x‖) =
            2 ^ (n + n ^ 2) * B ^ (n + 1) * ‖f x‖ by rw [pow_add]; ring]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by linarith : 0 ≤ B) _)
          apply pow_le_pow_right₀ (by norm_num)
          nlinarith



/-- The linear logarithmic gradient of the isotropic heat kernel at time one. -/
noncomputable def isotropicGaussianGradient (d : ℕ) :
    Vec d →L[ℝ] (Vec d →L[ℝ] ℝ) :=
  ∑ i : Fin d, (-1 / 2 : ℝ) •
    (ContinuousLinearMap.proj i).smulRight (ContinuousLinearMap.proj i)

@[simp] theorem isotropicGaussianGradient_apply {d : ℕ} (x v : Vec d) :
    isotropicGaussianGradient d x v = (-1 / 2 : ℝ) * ∑ i, x i * v i := by
  simp [isotropicGaussianGradient, Finset.mul_sum]

/-- The literal isotropic Gaussian is smooth at every order. -/
theorem contDiff_isotropicGaussian (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (Correctors.euclideanHeatKernel (d := d) 1) := by
  unfold Correctors.euclideanHeatKernel euclideanSq dot
  fun_prop

/-- Derivative growth for the fixed isotropic Gaussian, with its Gaussian
factor retained for the subsequent Schwartz decay estimate. -/
theorem norm_iteratedFDeriv_isotropicGaussian {d : ℕ} (x : Vec d) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (Correctors.euclideanHeatKernel (d := d) 1) x‖ ≤
      (2 : ℝ) ^ (n ^ 2) *
        ((1 + ‖isotropicGaussianGradient d‖) * (1 + ‖x‖)) ^ n *
        ‖Correctors.euclideanHeatKernel 1 x‖ := by
  let T := isotropicGaussianGradient d
  have hdf : fderiv ℝ (Correctors.euclideanHeatKernel (d := d) 1) =
      fun y => Correctors.euclideanHeatKernel 1 y • (0 + T y) := by
    ext y v
    simp [Correctors.fderiv_euclideanHeatKernel, T]
    ring
  have hT := norm_nonneg T
  have hx := norm_nonneg x
  apply norm_iteratedFDeriv_affine_log _ T 0 (contDiff_isotropicGaussian d) hdf x
  · nlinarith
  · simp only [zero_add]
    exact (T.le_opNorm x).trans (by nlinarith)
  · nlinarith


/-- The native coordinate norm is controlled by the actual Euclidean quadratic
form, including in dimension zero. -/
theorem norm_sq_le_euclideanSq {d : ℕ} (x : Vec d) : ‖x‖ ^ 2 ≤ euclideanSq x := by
  have hsq : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (x k))
  have hn : ‖x‖ ≤ Real.sqrt (euclideanSq x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
    rw [sq_abs, Real.sq_sqrt hsq]
    simpa only [euclideanSq, dot, pow_two] using
      Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)
  calc
    ‖x‖ ^ 2 ≤ Real.sqrt (euclideanSq x) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ = _ := Real.sq_sqrt hsq

private lemma isotropicGaussian_polynomial_absorption {r q : ℝ}
    (hr : 0 ≤ r) (hq : r ^ 2 ≤ q) (p : ℕ) :
    (1 + r) ^ p * Real.exp (-q / 4) ≤ Real.exp ((p : ℝ) ^ 2) := by
  have hp : (1 + r) ^ p ≤ Real.exp ((p : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) p
  calc
    _ ≤ Real.exp ((p : ℝ) * r) * Real.exp (-q / 4) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((p : ℝ) * r - q / 4) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (r - 2 * (p : ℝ))])

/-- Every weighted derivative of the literal time-one heat kernel has a bound
chosen independently of the environment law. -/
theorem isotropicGaussian_weighted_iteratedFDeriv_bound (d m n : ℕ) (x : Vec d) :
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (Correctors.euclideanHeatKernel (d := d) 1) x‖ ≤
      (2 : ℝ) ^ (n ^ 2) * (1 + ‖isotropicGaussianGradient d‖) ^ n *
        (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (((m + n : ℕ) : ℝ) ^ 2) := by
  have hker : ‖Correctors.euclideanHeatKernel (d := d) 1 x‖ =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-euclideanSq x / 4) := by
    rw [Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg zero_le_one x)]
    simp [Correctors.euclideanHeatKernel]
  have hp := isotropicGaussian_polynomial_absorption (norm_nonneg x)
    (norm_sq_le_euclideanSq x) (m + n)
  have hm : ‖x‖ ^ m ≤ (1 + ‖x‖) ^ m :=
    pow_le_pow_left₀ (norm_nonneg x) (by linarith) m
  calc
    _ ≤ (1 + ‖x‖) ^ m * ((2 : ℝ) ^ (n ^ 2) *
        ((1 + ‖isotropicGaussianGradient d‖) * (1 + ‖x‖)) ^ n *
        ‖Correctors.euclideanHeatKernel 1 x‖) :=
      mul_le_mul hm (norm_iteratedFDeriv_isotropicGaussian x n) (norm_nonneg _) (by positivity)
    _ = ((2 : ℝ) ^ (n ^ 2) * (1 + ‖isotropicGaussianGradient d‖) ^ n *
        (4 * Real.pi) ^ (-(d : ℝ) / 2)) *
        ((1 + ‖x‖) ^ (m + n) * Real.exp (-euclideanSq x / 4)) := by
      rw [hker, mul_pow, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- The isotropic time-one heat kernel, packaged as the actual Schwartz test
used to obtain the smoothed-field CLT estimate. -/
noncomputable def isotropicGaussianSchwartz (d : ℕ) : SchwartzMap (Vec d) ℝ where
  toFun := Correctors.euclideanHeatKernel 1
  smooth' := contDiff_isotropicGaussian d
  decay' m n := ⟨_, fun x => isotropicGaussian_weighted_iteratedFDeriv_bound d m n x⟩

@[simp] theorem isotropicGaussianSchwartz_apply {d : ℕ} (x : Vec d) :
    isotropicGaussianSchwartz d x = Correctors.euclideanHeatKernel 1 x := rfl


/-- A single joint-observation coordinate tested against the literal isotropic
Gaussian. The other coordinates vanish. -/
noncomputable def isotropicGaussianJointSchwartz {d : ℕ} (a : JointObservationIndex d) :
    SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)) :=
  (isotropicGaussianSchwartz d).postcompCLM
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (PiLp.single 2 a (1 : ℂ)))

@[simp] theorem isotropicGaussianJointSchwartz_apply {d : ℕ}
    (a b : JointObservationIndex d) (x : Vec d) :
    isotropicGaussianJointSchwartz a x b =
      if a = b then (Correctors.euclideanHeatKernel 1 x : ℂ) else 0 := by
  classical
  by_cases h : a = b
  · subst b
    simp [isotropicGaussianJointSchwartz, SchwartzMap.postcompCLM_apply]
  · simp [isotropicGaussianJointSchwartz, SchwartzMap.postcompCLM_apply, h, Ne.symm h]

/-- Test-CLT supplies a structural bound for every coordinate of the actual
isotropic Gaussian test, using the original derivative index `N`. -/
theorem isotropicGaussianJoint_clt_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, ∀ hR : 1 ≤ R, ∀ a : JointObservationIndex d,
        ‖scaledJointPairing Q R (by linarith) Z (isotropicGaussianJointSchwartz a)‖ ≤ C := by
  classical
  obtain ⟨C, hC, hbound⟩ := hclt d hd D N hN
  let S : ℝ := ∑ a : JointObservationIndex d,
    |schwartzTestNorm N (isotropicGaussianJointSchwartz a)|
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨C * (1 + S), mul_pos hC (by linarith), ?_⟩
  intro Q hQ Z hZ R hR a
  apply (hbound Q hQ Z hZ R hR (isotropicGaussianJointSchwartz a)).trans
  apply mul_le_mul_of_nonneg_left _ hC.le
  have ha : |schwartzTestNorm N (isotropicGaussianJointSchwartz a)| ≤ S :=
    Finset.single_le_sum (f := fun b => |schwartzTestNorm N
      (isotropicGaussianJointSchwartz b)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ a)
  exact (le_abs_self _).trans (ha.trans (by linarith))


/-- The joint Schwartz test selects exactly one translated observation. -/
theorem scaledJointPairing_isotropicGaussian {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (a : JointObservationIndex d) :
    scaledJointPairing Q R hR Z (isotropicGaussianJointSchwartz a) =
      ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
        ∫ x : Vec d, (Correctors.euclideanHeatKernel 1 (R⁻¹ • x) : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a) := by
  classical
  unfold scaledJointPairing
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  simp [isotropicGaussianJointSchwartz_apply, ite_smul]

/-- Parabolic scaling identifies the fixed Gaussian CLT test with the literal
heat average at the physical scale. -/
theorem isotropicGaussian_average_eq_scaledJointPairing {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (a : JointObservationIndex d) :
    (∫ x : Vec d, (Correctors.euclideanHeatKernel (R ^ 2) x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a)) =
      ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
        scaledJointPairing Q R hR Z (isotropicGaussianJointSchwartz a) := by
  have hpow : R ^ (-(d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) = (R ^ d)⁻¹ := by
    rw [← Real.rpow_add hR]
    rw [show -(d : ℝ) / 2 + -(d : ℝ) / 2 = -(d : ℝ) by ring,
      Real.rpow_neg hR.le, Real.rpow_natCast]
  have hk (x : Vec d) : (R ^ d)⁻¹ *
      Correctors.euclideanHeatKernel 1 (R⁻¹ • x) =
        Correctors.euclideanHeatKernel (R ^ 2) x := by
    simpa [smul_smul, hR.ne'] using
      (Correctors.euclideanHeatKernel_scale hR zero_lt_one (R⁻¹ • x)).symm
  rw [scaledJointPairing_isotropicGaussian, smul_smul, ← Complex.ofReal_mul, hpow,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_smul, ← Complex.ofReal_mul, hk]

/-- The literal heat average decays with the CLT scaling `R^(-d/2)`.
The constant is selected before the law, observation and physical scale. -/
theorem isotropicGaussian_average_clt_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 1 ≤ R → ∀ a : JointObservationIndex d,
        ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (R ^ 2) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a)‖ ≤
            C * R ^ (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hb⟩ := isotropicGaussianJoint_clt_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR a
  have hRpos : 0 < R := by linarith
  rw [isotropicGaussian_average_eq_scaledJointPairing Q R hRpos Z a, norm_smul,
    Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hRpos.le _), mul_comm C]
  exact mul_le_mul_of_nonneg_left (hb Q hQ Z hZ R hR a) (Real.rpow_nonneg hRpos.le _)


/-- The actual isotropic heat average is a genuine Bochner integral in L². -/
theorem integrable_isotropicGaussian_average {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {t : ℝ} (ht : 0 < t)
    (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => (Correctors.euclideanHeatKernel t x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U) := by
  let := reducedLaw_probability Q
  apply integrable_kernel_complexTranslation _ _ _
    (Correctors.integrable_euclideanHeatKernel ht).ofReal
  exact Complex.continuous_ofReal.comp (Correctors.contDiff_euclideanHeatKernel t).continuous

/-- Heat averaging contracts the raw observation L² norm at every positive
time, supplying control at scales below the CLT threshold. -/
theorem isotropicGaussian_average_norm_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {t : ℝ} (ht : 0 < t)
    (U : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ x : Vec d, (Correctors.euclideanHeatKernel t x : ℂ) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U‖ ≤ ‖U‖ := by
  have hb := norm_integral_le_of_norm_le
    ((Correctors.integrable_euclideanHeatKernel (d := d) ht).mul_const ‖U‖)
    (ae_of_all _ fun x => show
      ‖(Correctors.euclideanHeatKernel t x : ℂ) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U‖ ≤
          Correctors.euclideanHeatKernel t x * ‖U‖ by
      rw [norm_smul, norm_complexTranslation, Complex.norm_real,
        Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg ht.le x)])
  simpa only [integral_mul_const, Correctors.integral_euclideanHeatKernel ht, one_mul] using hb


private lemma coord_le_euclideanNorm {d : ℕ} (x : Vec d) (j : Fin d) :
    |x j| ≤ euclideanNorm x := by
  rw [TimeChange.euclideanNorm_eq_norm_toLp]
  exact PiLp.norm_apply_le (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) j

/-- The literal reduced coefficient has structurally bounded entries. -/
theorem ae_abs_reducedCoefficient_entry_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j k : Fin d,
      |ω.1 0 j k| ≤ sourceReducedBound Λ₀ := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hω
  obtain ⟨η, hη, hηω⟩ := hω
  have ha : IsElliptic (sourceReducedBound Λ₀) ω.1 := by
    rw [← hηω]
    exact (sourceReducedBound_support Q.ellipticity_parameter hη).2.1
  have hK : 0 < sourceReducedBound Λ₀ := zero_lt_one.trans_le
    (sourceReducedBound_support Q.ellipticity_parameter hη).1
  intro j k
  have h := (coord_le_euclideanNorm ((ω.1 0).mulVec (unitVector k)) j).trans
    (Correctors.isElliptic_mulVec_euclideanNorm_le hK ha 0 (unitVector k))
  simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply,
    euclideanNorm, euclideanSq, dot] using h

/-- The commutator is controlled by the actual affine gradient on one event. -/
theorem ae_abs_commutatorObservation_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, |commutatorObservation Q j i ω| ≤
      (d : ℝ) * (2 * sourceReducedBound Λ₀) *
        ‖Correctors.correctorUnitVector i + correctorGradient Q i ω‖ := by
  filter_upwards [ae_abs_reducedCoefficient_entry_le Q] with ω hω
  have hK : 0 ≤ sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_nonneg (Real.exp_pos _).le (by nlinarith [sq_nonneg Λ₀,
      Q.ellipticity_parameter])
  calc
    _ ≤ ∑ k : Fin d, |(ω.1 0 j k - homogenizedCoefficient Q j k) *
        ((unitVector i) k + correctorGradient Q i ω k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin d, (2 * sourceReducedBound Λ₀) *
        ‖Correctors.correctorUnitVector i + correctorGradient Q i ω‖ := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      apply mul_le_mul
      · exact (abs_sub _ _).trans (by
          have hh := (coord_le_euclideanNorm
            ((homogenizedCoefficient Q).mulVec (unitVector k)) j).trans
            (homogenizedCoefficient_column_bound Q k)
          have hh' : |homogenizedCoefficient Q j k| ≤ sourceReducedBound Λ₀ := by
            simpa [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply] using hh
          linarith [hω j k])
      · exact PiLp.norm_apply_le
          (Correctors.correctorUnitVector i + correctorGradient Q i ω) k
      · exact abs_nonneg _
      · positivity
    _ = _ := by simp [mul_assoc]

/-- Each commutator coordinate has a deterministic raw L² bound. -/
theorem norm_jointObservation_commutator_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z) (j i : Fin d) :
    ‖Z (.inl (j, i))‖ ≤ (d : ℝ) * (2 * sourceReducedBound Λ₀) *
      (1 + (Real.exp (2 * Λ₀) * Λ₀) ^ 2) := by
  let := reducedLaw_probability Q
  let A : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) :=
    Lp.const 2 (reducedLaw Q) (Correctors.correctorUnitVector i)
  have hAnorm : ‖A‖ = 1 := by
    simp [A, Lp.norm_const, Correctors.correctorUnitVector]
  have hpoint : ∀ᵐ ω ∂reducedLaw Q, ‖Z (.inl (j, i)) ω‖ ≤
      ((d : ℝ) * (2 * sourceReducedBound Λ₀)) * ‖(A + correctorGradient Q i) ω‖ := by
    filter_upwards [hZ.1 j i, ae_abs_commutatorObservation_le Q j i,
      Lp.coeFn_add A (correctorGradient Q i), Lp.coeFn_const
        (p := (2 : ℝ≥0∞)) (reducedLaw Q) (Correctors.correctorUnitVector i)]
      with ω hZω hω hadd hconst
    rw [hZω, Complex.norm_real, Real.norm_eq_abs, hadd]
    change |commutatorObservation Q j i ω| ≤ _ * ‖A ω + correctorGradient Q i ω‖
    change (Lp.const 2 (reducedLaw Q) (Correctors.correctorUnitVector i)) ω = _ at hconst
    change A ω = _ at hconst
    rw [hconst]
    exact hω
  have hK : 0 ≤ (d : ℝ) * (2 * sourceReducedBound Λ₀) := by
    unfold sourceReducedBound
    exact mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (by norm_num)
      (mul_nonneg (Real.exp_pos _).le (by nlinarith [sq_nonneg Λ₀,
        Q.ellipticity_parameter])))
  exact (Lp.norm_le_mul_norm_of_ae_le_mul hpoint).trans
    (mul_le_mul_of_nonneg_left ((norm_add_le A (correctorGradient Q i)).trans
      (by rw [hAnorm]; exact add_le_add_right (norm_correctorGradient_le Q i) 1)) hK)

/-- The clock coordinate has a uniform raw L² bound under the reduced law. -/
theorem norm_jointObservation_clock_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z) :
    ‖Z (.inr ())‖ ≤ 2 * sourceReducedBound Λ₀ := by
  let := reducedLaw_probability Q
  have hK : 0 ≤ 2 * sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_nonneg (by norm_num) (mul_nonneg (Real.exp_pos _).le
      (by nlinarith [sq_nonneg Λ₀, Q.ellipticity_parameter]))
  have hb : ∀ᵐ ω ∂reducedLaw Q, ‖Z (.inr ()) ω‖ ≤ 2 * sourceReducedBound Λ₀ := by
    filter_upwards [hZ.2, ae_abs_centeredClockField_le Q 0] with ω hω hb
    rw [hω, Complex.norm_real, Real.norm_eq_abs]
    exact hb
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound hK hb

/-- A common raw bound for the actual joint observation; its constant precedes
both the law and the chosen L² representatives. -/
theorem exists_jointObservation_norm_bound (d : ℕ) (Λ₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsJointObservation Q Z → ∀ a, ‖Z a‖ ≤ C := by
  let B := (d : ℝ) * (2 * sourceReducedBound Λ₀) *
    (1 + (Real.exp (2 * Λ₀) * Λ₀) ^ 2)
  let H := 2 * sourceReducedBound Λ₀
  refine ⟨1 + |B| + |H|, by positivity, ?_⟩
  intro r₀ Q Z hZ a
  rcases a with ⟨j, i⟩ | ⟨⟩
  · exact (norm_jointObservation_commutator_le Q Z hZ j i).trans
      (by change B ≤ 1 + |B| + |H|; linarith [le_abs_self B, abs_nonneg H])
  · exact (norm_jointObservation_clock_le Q Z hZ).trans
      (by change H ≤ 1 + |B| + |H|; linarith [le_abs_self H, abs_nonneg B])

/-- The isotropic heat average has one structural estimate at every physical
scale, retaining boundedness below the CLT scale and decay above it. -/
theorem isotropicGaussian_average_all_scales_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R → ∀ a : JointObservationIndex d,
        ‖∫ x : Vec d, (Correctors.euclideanHeatKernel (R ^ 2) x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a)‖ ≤
            C * min 1 (R ^ (-(d : ℝ) / 2)) := by
  obtain ⟨A, hA, hraw⟩ := exists_jointObservation_norm_bound d D.ellipticity
  obtain ⟨B, hB, hdecay⟩ := isotropicGaussian_average_clt_bound hclt d hd D N hN
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro Q hQ Z hZ R hR a
  rw [mul_min_of_nonneg _ _ (add_pos hA hB).le, mul_one]
  apply le_min
  · exact ((isotropicGaussian_average_norm_le Q (sq_pos_of_pos hR) (Z a)).trans
      (hraw Q Z hZ a)).trans (by linarith)
  · by_cases hlarge : 1 ≤ R
    · exact (hdecay Q hQ Z hZ R hlarge a).trans
        (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hR.le _))
    · have hp : 1 ≤ R ^ (-(d : ℝ) / 2) :=
        Real.one_le_rpow_of_pos_of_le_one_of_nonpos hR (le_of_not_ge hlarge)
          (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
      exact ((isotropicGaussian_average_norm_le Q (sq_pos_of_pos hR) (Z a)).trans
        (hraw Q Z hZ a)).trans (by nlinarith)

/-- The all-scale estimate in heat time, for use in the finite heat expansion.
The singular majorant has exponent `-d/4` in L². -/
theorem isotropicGaussian_average_time_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ t : ℝ, 0 < t → ∀ a : JointObservationIndex d,
        ‖∫ x : Vec d, (Correctors.euclideanHeatKernel t x : ℂ) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (Z a)‖ ≤
            C * min 1 (t ^ (-(d : ℝ) / 4)) := by
  obtain ⟨C, hC, hb⟩ := isotropicGaussian_average_all_scales_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ t ht a
  have hp : (Real.sqrt t) ^ (-(d : ℝ) / 2) = t ^ (-(d : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le]
    congr 1
    ring
  simpa only [Real.sq_sqrt ht.le, hp] using
    hb Q hQ Z hZ (Real.sqrt t) (Real.sqrt_pos.mpr ht) a

/-- The kernel/translation product is integrable on the full spatial product,
so heat transfer uses Bochner Fubini with an explicit integrable majorant. -/
theorem integrable_heatTransfer_integrand {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × Vec d =>
      (K p.2 * Correctors.euclideanHeatKernel t (p.1 - p.2)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • p.1) U)
      (volume.prod volume) := by
  let := reducedLaw_probability Q
  have hp := Correctors.integrable_euclideanHeatKernel (d := d) ht
  have hs : Integrable (fun p : Vec d × Vec d =>
      K p.2 * Correctors.euclideanHeatKernel t (p.1 - p.2)) (volume.prod volume) :=
    hK.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hp
  have hc : Continuous (fun p : Vec d × Vec d =>
      (K p.2 * Correctors.euclideanHeatKernel t (p.1 - p.2)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • p.1) U) :=
    ((hKc.comp continuous_snd).mul
      ((Correctors.contDiff_euclideanHeatKernel t).continuous.comp
        (continuous_fst.sub continuous_snd))).smul
      ((continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        ((continuous_fst.const_smul R).prodMk continuous_const))
  apply (hs.norm.mul_const ‖U‖).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun p => by rw [norm_smul, norm_complexTranslation]

/-- Spatial heat convolution transfers from a real test to the actual complex
L² observation, with the even heat kernel fixing the reflection convention. -/
theorem integral_heatConvolution_smul_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, Correctors.heatKernelConvolution t K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) =
    ∫ y : Vec d, K y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • y)
      (∫ z : Vec d, Correctors.euclideanHeatKernel t z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) U) := by
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x)
  have hτadd (x y : Vec d) : τ (x + y) U = τ x (τ y U) := by
    dsimp [τ]
    rw [smul_add, complexTranslation_add]
  have hf := integrable_heatTransfer_integrand Q K hK hKc ht R U
  change (∫ x, Correctors.heatKernelConvolution t K x • τ x U) =
    ∫ y, K y • τ y (∫ z, Correctors.euclideanHeatKernel t z • τ z U)
  calc
    _ = ∫ x : Vec d, ∫ y : Vec d,
        (K y * Correctors.euclideanHeatKernel t (x - y)) • τ x U := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Correctors.heatKernelConvolution, ite_eq_right ht.ne', ← integral_smul_const]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [show Correctors.euclideanHeatKernel t (y - x) =
          Correctors.euclideanHeatKernel t (x - y) by
        rw [← neg_sub x y, Correctors.euclideanHeatKernel_neg]]
    _ = ∫ y : Vec d, ∫ x : Vec d,
        (K y * Correctors.euclideanHeatKernel t (x - y)) • τ x U :=
      integral_integral_swap hf
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      calc
        _ = ∫ z : Vec d, (K y * Correctors.euclideanHeatKernel t z) • τ (z + y) U := by
          have hh := integral_add_right_eq_self (μ := (volume : Measure (Vec d)))
            (fun x : Vec d => (K y * Correctors.euclideanHeatKernel t (x - y)) • τ x U) y
          simpa only [add_sub_cancel_right] using hh.symm
        _ = K y • ∫ z : Vec d,
            (τ y).restrictScalars ℝ (Correctors.euclideanHeatKernel t z • τ z U) := by
          rw [← integral_smul]
          apply integral_congr_ae
          filter_upwards [] with z
          rw [map_smul]
          change (K y * Correctors.euclideanHeatKernel t z) • τ (z + y) U =
            K y • (Correctors.euclideanHeatKernel t z • τ y (τ z U))
          rw [← hτadd, add_comm z y, smul_smul]
        _ = _ := congrArg (fun V => K y • V)
          ((τ y).integral_comp_comm
            (fun z => Correctors.euclideanHeatKernel t z • τ z U))

/-- Heat transfer bounds testing against a smoothed kernel by its L¹ norm
and the L² norm of the smoothed observation. -/
theorem norm_integral_heatConvolution_smul_translation_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ x : Vec d, Correctors.heatKernelConvolution t K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U‖ ≤
    (∫ x : Vec d, ‖K x‖) *
      ‖∫ z : Vec d, Correctors.euclideanHeatKernel t z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) U‖ := by
  rw [integral_heatConvolution_smul_translation Q K hK hKc ht R U]
  let H := ∫ z : Vec d, Correctors.euclideanHeatKernel t z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) U
  have hb := norm_integral_le_of_norm_le (hK.norm.mul_const ‖H‖)
    (ae_of_all _ fun y => show ‖K y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • y) H‖ ≤ ‖K y‖ * ‖H‖ by
        rw [norm_smul, norm_complexTranslation])
  simpa only [integral_mul_const] using hb

/-- Rescaling the translation in a heat average changes its physical heat time. -/
theorem integral_heatKernel_smul_scaled_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ z : Vec d, Correctors.euclideanHeatKernel t z •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) U) =
    ∫ x : Vec d, Correctors.euclideanHeatKernel (R ^ 2 * t) x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => Correctors.euclideanHeatKernel (R ^ 2 * t) x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U) R
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hR.le _))] at h
  simp only [Correctors.euclideanHeatKernel_scale hR ht, mul_smul] at h
  rw [integral_smul] at h
  exact smul_right_injective _ (inv_ne_zero (pow_ne_zero d hR.ne')) h

/-- The CLT normalization cancels the physical rescaling of a Gaussian average.
This estimate keeps the original derivative order of the test CLT. -/
theorem normalized_isotropicGaussian_average_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t → ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ z : Vec d, Correctors.euclideanHeatKernel t z •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)‖ ≤
        C * t ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := isotropicGaussian_average_time_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR t ht a
  rw [integral_heatKernel_smul_scaled_translation Q ht hR]
  have htime : 0 < R ^ 2 * t := mul_pos (sq_pos_of_pos hR) ht
  have hbound := (hb Q hQ Z hZ (R ^ 2 * t) htime a).trans
    (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le)
  have hscale : R ^ ((d : ℝ) / 2) * (R ^ 2 * t) ^ (-(d : ℝ) / 4) =
      t ^ (-(d : ℝ) / 4) := by
    rw [Real.mul_rpow (sq_nonneg R) ht.le, ← Real.rpow_natCast R 2,
      ← Real.rpow_mul hR.le]
    rw [← mul_assoc, ← Real.rpow_add hR]
    norm_num [show (d : ℝ) / 2 + (2 : ℝ) * (-(d : ℝ) / 4) = 0 by ring]
  calc
    _ ≤ R ^ ((d : ℝ) / 2) * (C * (R ^ 2 * t) ^ (-(d : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hR.le _)
    _ = C * (R ^ ((d : ℝ) / 2) * (R ^ 2 * t) ^ (-(d : ℝ) / 4)) := by ring
    _ = _ := by rw [hscale]

/-- Testing a heat-smoothed integrable kernel obeys a uniform normalized bound.
Only the fixed Gaussian test is consumed from the test CLT. -/
theorem normalized_heatConvolution_test_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R → ∀ t : ℝ, 0 < t →
      ∀ K : Vec d → ℝ, Integrable K → Continuous K →
      ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ x : Vec d, Correctors.heatKernelConvolution t K x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖ ≤
        C * (∫ x : Vec d, ‖K x‖) * t ^ (-(d : ℝ) / 4) := by
  obtain ⟨C, hC, hb⟩ := normalized_isotropicGaussian_average_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR t ht K hK hKc a
  have htransfer := norm_integral_heatConvolution_smul_translation_le Q K hK hKc ht R (Z a)
  calc
    _ ≤ R ^ ((d : ℝ) / 2) * ((∫ x : Vec d, ‖K x‖) *
        ‖∫ z : Vec d, Correctors.euclideanHeatKernel t z •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)‖) :=
      mul_le_mul_of_nonneg_left htransfer (Real.rpow_nonneg hR.le _)
    _ = (∫ x : Vec d, ‖K x‖) * (R ^ ((d : ℝ) / 2) *
        ‖∫ z : Vec d, Correctors.euclideanHeatKernel t z •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)‖) := by ring
    _ ≤ (∫ x : Vec d, ‖K x‖) * (C * t ^ (-(d : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (hb Q hQ Z hZ R hR t ht a)
        (integral_nonneg fun _ => norm_nonneg _)
    _ = _ := by ring

/-- Heat convolution preserves spatial integrability, including at time zero. -/
theorem integrable_heatConvolution {d : ℕ} {K : Vec d → ℝ}
    (hK : Integrable K) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (Correctors.heatKernelConvolution t K) := by
  rcases ht.eq_or_lt with rfl | ht
  · change Integrable (fun x : Vec d => Correctors.heatKernelConvolution 0 K x)
    simpa [Correctors.heatKernelConvolution] using hK
  have hi := (hK.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ)
    (Correctors.integrable_euclideanHeatKernel (d := d) ht)).integral_prod_left
  change Integrable (fun x : Vec d => ∫ y : Vec d,
    K y * Correctors.euclideanHeatKernel t (x - y)) at hi
  convert hi using 1
  funext x
  rw [Correctors.heatKernelConvolution, ite_eq_right ht.ne']
  apply integral_congr_ae
  filter_upwards [] with y
  rw [show Correctors.euclideanHeatKernel t (y - x) =
      Correctors.euclideanHeatKernel t (x - y) by
    rw [← neg_sub x y, Correctors.euclideanHeatKernel_neg]]

/-- The spatial L¹ contraction supplies the majorant for heat-time Fubini. -/
theorem integral_norm_heatConvolution_le {d : ℕ} {K : Vec d → ℝ}
    (hK : Integrable K) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : Vec d, ‖Correctors.heatKernelConvolution t K x‖) ≤
      ∫ x : Vec d, ‖K x‖ := by
  rcases ht.eq_or_lt with rfl | ht
  · simp [Correctors.heatKernelConvolution]
  have hp := Correctors.integrable_euclideanHeatKernel (d := d) ht
  have hm := hK.norm.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hp
  have hmajor := hm.integral_prod_left
  change Integrable (fun x : Vec d => ∫ y : Vec d,
    ‖K y‖ * Correctors.euclideanHeatKernel t (x - y)) at hmajor
  calc
    _ ≤ ∫ x : Vec d, ∫ y : Vec d,
        ‖K y‖ * Correctors.euclideanHeatKernel t (x - y) := by
      apply integral_mono (integrable_heatConvolution hK ht.le).norm hmajor
      intro x
      change ‖Correctors.heatKernelConvolution t K x‖ ≤ ∫ y : Vec d,
        ‖K y‖ * Correctors.euclideanHeatKernel t (x - y)
      rw [Correctors.heatKernelConvolution, ite_eq_right ht.ne']
      convert norm_integral_le_integral_norm
        (fun y : Vec d => K y * Correctors.euclideanHeatKernel t (y - x)) using 1
      apply integral_congr_ae
      filter_upwards [] with y
      rw [norm_mul, Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg ht.le _)]
      rw [show Correctors.euclideanHeatKernel t (y - x) =
          Correctors.euclideanHeatKernel t (x - y) by
        rw [← neg_sub x y, Correctors.euclideanHeatKernel_neg]]
    _ = _ := by
      rw [integral_integral_swap hm]
      simp_rw [integral_const_mul, integral_sub_right_eq_self,
        Correctors.integral_euclideanHeatKernel ht, mul_one]

/-- Clamping negative times to zero gives a jointly continuous heat orbit for
bounded continuous tests. This is used only to justify time-space measurability. -/
theorem continuous_heatConvolution_max {d : ℕ} {K : Vec d → ℝ}
    (hK : Continuous K) {M : ℝ} (hM : ∀ x, ‖K x‖ ≤ M) :
    Continuous (fun p : ℝ × Vec d => Correctors.heatKernelConvolution (max p.1 0) K p.2) := by
  have hc : Continuous (fun p : ℝ × Vec d => ∫ z : Vec d,
      Correctors.euclideanHeatKernel 1 z * K (Real.sqrt (max p.1 0) • z + p.2)) := by
    apply continuous_of_dominated
      (bound := fun z => Correctors.euclideanHeatKernel 1 z * M)
    · exact fun p => ((Correctors.continuous_euclideanHeatKernel 1).mul
        (hK.comp (by fun_prop : Continuous fun z : Vec d =>
          Real.sqrt (max p.1 0) • z + p.2))).aestronglyMeasurable
    · exact fun p => ae_of_all _ fun z => by
        rw [norm_mul, Real.norm_of_nonneg
          (Correctors.euclideanHeatKernel_nonneg zero_le_one z)]
        exact mul_le_mul_of_nonneg_left (hM _)
          (Correctors.euclideanHeatKernel_nonneg zero_le_one z)
    · exact (Correctors.integrable_euclideanHeatKernel (d := d) zero_lt_one).mul_const M
    · exact ae_of_all _ fun z => continuous_const.mul
        (hK.comp (by fun_prop : Continuous fun p : ℝ × Vec d =>
          Real.sqrt (max p.1 0) • z + p.2))
  exact hc.congr fun p =>
    (Correctors.heatKernelConvolution_eq_scaled_nonneg (le_max_right _ _) K p.2).symm

/-- The weighted heat-time remainder can be integrated jointly with the
translated observation. Its majorant uses spatial L¹ contraction. -/
theorem integrable_heatTime_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {M : ℝ} (hM : ∀ x, ‖K x‖ ≤ M)
    (n : ℕ) (T R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : ℝ × Vec d =>
      (p.1 ^ n * Correctors.heatKernelConvolution p.1 K p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • p.2) U)
      ((volume.restrict (Set.Ioc 0 T)).prod volume) := by
  let f := fun p : ℝ × Vec d =>
    (p.1 ^ n * Correctors.heatKernelConvolution p.1 K p.2) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • p.2) U
  have hc : Continuous (fun p : ℝ × Vec d =>
      (p.1 ^ n * Correctors.heatKernelConvolution (max p.1 0) K p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • p.2) U) :=
    ((continuous_fst.pow n).mul (continuous_heatConvolution_max hKc hM)).smul
      ((continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        ((continuous_snd.const_smul R).prodMk continuous_const))
  have hf : AEStronglyMeasurable f
      ((volume.restrict (Set.Ioc 0 T)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    apply hc.aestronglyMeasurable.restrict.congr
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod MeasurableSet.univ)] with p hp
    simp only [f, max_eq_left hp.1.1.le]
  apply (integrable_prod_iff hf).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hP := integrable_heatConvolution hK ht.1.le
    have hτ : Continuous (fun x : Vec d =>
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) :=
      (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        ((continuous_id.const_smul R).prodMk continuous_const)
    apply (hP.norm.const_mul (|t ^ n| * ‖U‖)).mono'
      ((hP.aestronglyMeasurable.const_mul (t ^ n)).smul hτ.aestronglyMeasurable)
    exact ae_of_all _ fun x => by
      change ‖(t ^ n * Correctors.heatKernelConvolution t K x) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U‖ ≤ _
      rw [norm_smul, norm_mul, Real.norm_eq_abs, norm_complexTranslation]
      exact le_of_eq (by ring)
  · have hmajor : Integrable (fun t : ℝ =>
        t ^ n * (∫ x : Vec d, ‖K x‖) * ‖U‖) (volume.restrict (Set.Ioc 0 T)) :=
      (((continuous_pow n).mul continuous_const).mul continuous_const).integrableOn_Ioc
    apply hmajor.mono' hf.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have heq : (∫ x : Vec d, ‖f (t, x)‖) =
        t ^ n * (∫ x : Vec d, ‖Correctors.heatKernelConvolution t K x‖) * ‖U‖ := by
      simp only [f, norm_smul, norm_mul, Real.norm_eq_abs, norm_complexTranslation,
        abs_of_nonneg (pow_nonneg ht.1.le n), integral_const_mul, integral_mul_const]
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), heq]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (integral_norm_heatConvolution_le hK ht.1.le)
        (pow_nonneg ht.1.le n)) (norm_nonneg U)

/-- The time-integrated remainder is an integrable spatial test against the
translated L² observation. -/
theorem integrable_heatTime_test {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {M : ℝ} (hM : ∀ x, ‖K x‖ ≤ M)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d =>
      (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t K x) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) := by
  have hi := (integrable_heatTime_translation Q K hK hKc hM n T R U).integral_prod_right
  apply hi.congr
  filter_upwards [] with x
  rw [intervalIntegral.integral_of_le hT, integral_smul_const]

/-- Bochner Fubini moves the time remainder outside the spatial testing
integral, with every integrability obligation discharged. -/
theorem integral_heatTime_test {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {M : ℝ} (hM : ∀ x, ‖K x‖ ≤ M)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d,
      (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t K x) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) =
    ∫ t in (0 : ℝ)..T, t ^ n • ∫ x : Vec d,
      Correctors.heatKernelConvolution t K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U := by
  simp_rw [intervalIntegral.integral_of_le hT]
  simp_rw [← integral_smul_const]
  rw [integral_integral_swap (f := fun (x : Vec d) (t : ℝ) =>
    (t ^ n * Correctors.heatKernelConvolution t K x) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U)
    (integrable_heatTime_translation Q K hK hKc hM n T R U).swap]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← integral_smul]
  simp only [smul_smul]

/-- Every integrable real kernel can be tested against the rescaled continuous
translation orbit of an L² observation. -/
theorem integrable_realKernel_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {K : Vec d → ℝ} (hK : Integrable K)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) := by
  have hτ : Continuous (fun x : Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      ((continuous_id.const_smul R).prodMk continuous_const)
  apply (hK.norm.mul_const ‖U‖).mono' (hK.aestronglyMeasurable.smul hτ.aestronglyMeasurable)
  exact ae_of_all _ fun x => by
    change ‖K x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U‖ ≤ _
    rw [norm_smul, norm_complexTranslation]

/-- The finite heat expansion holds after actual L² testing. In particular its
remainder is a Bochner time integral of the heat-smoothed testing integrals. -/
theorem integral_schwartz_heat_finite_expansion {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : SchwartzMap (Vec d) ℝ)
    (n : ℕ) {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) =
    (∑ j ∈ Finset.range (n + 1),
      ((-1 : ℝ) ^ j * T ^ j / (Nat.factorial j : ℝ)) •
        ∫ x : Vec d, Correctors.heatKernelConvolution T
          (Correctors.coordLaplacian^[j] ⇑K) x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) +
    ((-1 : ℝ) ^ (n + 1) / (Nat.factorial n : ℝ)) •
      ∫ t in (0 : ℝ)..T, t ^ n • ∫ x : Vec d,
        Correctors.heatKernelConvolution t (Correctors.coordLaplacian^[n + 1] ⇑K) x •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U := by
  let τ := fun x : Vec d =>
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U
  let c := fun j : ℕ => (-1 : ℝ) ^ j * T ^ j / (Nat.factorial j : ℝ)
  let b := (-1 : ℝ) ^ (n + 1) / (Nat.factorial n : ℝ)
  let A := fun j x => Correctors.heatKernelConvolution T
    (Correctors.coordLaplacian^[j] ⇑K) x • τ x
  let B := fun x : Vec d =>
    (∫ t in (0 : ℝ)..T, t ^ n * Correctors.heatKernelConvolution t
      (Correctors.coordLaplacian^[n + 1] ⇑K) x) • τ x
  have hA (j : ℕ) : Integrable (A j) :=
    integrable_realKernel_translation Q
      (integrable_heatConvolution (laplacian_iterate_schwartz_regular K j).2.1 hT) R U
  obtain ⟨hreg, hint, M, hM⟩ := laplacian_iterate_schwartz_regular K (n + 1)
  have hB : Integrable B := integrable_heatTime_test Q _ hint hreg.continuous hM n hT R U
  have heq (x : Vec d) : K x • τ x =
      (∑ j ∈ Finset.range (n + 1), c j • A j x) + b • B x := by
    conv_lhs => rw [heatConvolution_schwartz_finite_expansion K n x hT]
    simp only [add_smul, Finset.sum_smul, mul_smul, c, A, b, B]
  calc
    _ = ∫ x : Vec d, (∑ j ∈ Finset.range (n + 1), c j • A j x) + b • B x :=
      integral_congr_ae (ae_of_all _ heq)
    _ = (∑ j ∈ Finset.range (n + 1), c j • ∫ x : Vec d, A j x) +
        b • ∫ x : Vec d, B x := by
      rw [integral_add (f := fun x => ∑ j ∈ Finset.range (n + 1), c j • A j x)
        (g := fun x => b • B x)
        (integrable_finsetSum _ (fun j _ => (hA j).smul (c j))) (hB.smul b),
        integral_finsetSum (Finset.range (n + 1))
          (f := fun j x => c j • A j x) (fun j _ => (hA j).smul (c j))]
      simp only [integral_smul]
    _ = _ := by
      rw [show (∫ x : Vec d, B x) = _ from
        integral_heatTime_test Q _ hint hreg.continuous hM n hT R U]

/-- A sufficiently high time weight cancels the small-time Gaussian singularity.
On the unit time interval its normalized remainder is bounded by the test L¹ norm. -/
theorem normalized_heatTime_test_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R → ∀ n : ℕ, (d : ℝ) / 4 ≤ n →
      ∀ K : Vec d → ℝ, Integrable K → Continuous K →
      ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ t in (0 : ℝ)..1, t ^ n • ∫ x : Vec d,
            Correctors.heatKernelConvolution t K x •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖ ≤
        C * ∫ x : Vec d, ‖K x‖ := by
  obtain ⟨C, hC, hb⟩ := normalized_heatConvolution_test_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR n hn K hK hKc a
  have hRpow := Real.rpow_nonneg hR.le ((d : ℝ) / 2)
  have htest : 0 ≤ C * ∫ x : Vec d, ‖K x‖ :=
    mul_nonneg hC.le (integral_nonneg fun _ => norm_nonneg _)
  have hpoint (t : ℝ) (ht : t ∈ Set.uIoc (0 : ℝ) 1) :
      ‖R ^ ((d : ℝ) / 2) • (t ^ n • ∫ x : Vec d,
        Correctors.heatKernelConvolution t K x •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a))‖ ≤
      C * ∫ x : Vec d, ‖K x‖ := by
    have ht' : t ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa only [Set.uIoc_of_le zero_le_one] using ht
    have hw : t ^ n * t ^ (-(d : ℝ) / 4) ≤ 1 := by
      rw [← Real.rpow_natCast t n, ← Real.rpow_add ht'.1]
      exact Real.rpow_le_one ht'.1.le ht'.2 (by linarith)
    rw [norm_smul, Real.norm_of_nonneg hRpow, norm_smul,
      Real.norm_of_nonneg (pow_nonneg ht'.1.le n)]
    calc
      _ = t ^ n * (R ^ ((d : ℝ) / 2) *
          ‖∫ x : Vec d, Correctors.heatKernelConvolution t K x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖) := by ring
      _ ≤ t ^ n * (C * (∫ x : Vec d, ‖K x‖) * t ^ (-(d : ℝ) / 4)) :=
        mul_le_mul_of_nonneg_left (hb Q hQ Z hZ R hR t ht'.1 K hK hKc a)
          (pow_nonneg ht'.1.le n)
      _ = (C * ∫ x : Vec d, ‖K x‖) * (t ^ n * t ^ (-(d : ℝ) / 4)) := by ring
      _ ≤ _ := mul_le_of_le_one_right htest hw
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  rw [intervalIntegral.integral_smul, norm_smul, Real.norm_of_nonneg hRpow] at hi
  simpa only [sub_zero, abs_one, mul_one] using hi

/-- A finite heat expansion converts the Gaussian CLT into a distribution bound
using only Laplacian iterates through order `d + 2`. -/
theorem normalized_schwartz_test_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R → ∀ K : SchwartzMap (Vec d) ℝ,
      ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ x : Vec d, K x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖ ≤
        C * ∑ j ∈ Finset.range (d + 3),
          ∫ x : Vec d, ‖(Correctors.coordLaplacian^[j] ⇑K) x‖ := by
  obtain ⟨A, hA, ha⟩ := normalized_heatConvolution_test_bound hclt d hd D N hN
  obtain ⟨B, hB, hb⟩ := normalized_heatTime_test_bound hclt d hd D N hN
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro Q hQ Z hZ R hR K a
  let P := R ^ ((d : ℝ) / 2)
  let V := fun j : ℕ => ∫ x : Vec d,
    Correctors.heatKernelConvolution 1 (Correctors.coordLaplacian^[j] ⇑K) x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)
  let W := ∫ t in (0 : ℝ)..1, t ^ (d + 1) • ∫ x : Vec d,
    Correctors.heatKernelConvolution t (Correctors.coordLaplacian^[d + 2] ⇑K) x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)
  let l := fun j : ℕ => ∫ x : Vec d, ‖(Correctors.coordLaplacian^[j] ⇑K) x‖
  let c := fun j : ℕ => (-1 : ℝ) ^ j / (Nat.factorial j : ℝ)
  let b := (-1 : ℝ) ^ (d + 2) / (Nat.factorial (d + 1) : ℝ)
  have hP : 0 ≤ P := Real.rpow_nonneg hR.le _
  have hl (j : ℕ) : 0 ≤ l j := integral_nonneg fun _ => norm_nonneg _
  have hcoeff (i j : ℕ) : ‖(-1 : ℝ) ^ i / (Nat.factorial j : ℝ)‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    norm_num only [norm_neg, norm_one, one_pow]
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j))
  have hv (j : ℕ) : P * ‖c j • V j‖ ≤ A * l j := by
    obtain ⟨hreg, hint, M, hM⟩ := laplacian_iterate_schwartz_regular K j
    have hbound := ha Q hQ Z hZ R hR 1 zero_lt_one _ hint hreg.continuous a
    simp only [Real.one_rpow, mul_one] at hbound
    calc
      _ ≤ P * ‖V j‖ := mul_le_mul_of_nonneg_left
        (by rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hcoeff j j)) hP
      _ ≤ _ := hbound
  have hw : P * ‖b • W‖ ≤ B * l (d + 2) := by
    obtain ⟨hreg, hint, M, hM⟩ := laplacian_iterate_schwartz_regular K (d + 2)
    have hn : (d : ℝ) / 4 ≤ (d + 1 : ℕ) := by
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
      push_cast
      linarith
    have hbound := hb Q hQ Z hZ R hR (d + 1) hn _ hint hreg.continuous a
    calc
      _ ≤ P * ‖W‖ := mul_le_mul_of_nonneg_left
        (by rw [norm_smul]; exact mul_le_of_le_one_left (norm_nonneg _) (hcoeff _ _)) hP
      _ ≤ _ := hbound
  have heq := integral_schwartz_heat_finite_expansion Q K (d + 1) (T := 1)
    zero_le_one R (Z a)
  simp only [one_pow, mul_one] at heq
  change P * _ ≤ _
  rw [heq]
  change P * ‖(∑ j ∈ Finset.range (d + 2), c j • V j) + b • W‖ ≤ _
  calc
    _ ≤ P * ((∑ j ∈ Finset.range (d + 2), ‖c j • V j‖) + ‖b • W‖) :=
      mul_le_mul_of_nonneg_left
        ((norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) le_rfl)) hP
    _ = (∑ j ∈ Finset.range (d + 2), P * ‖c j • V j‖) + P * ‖b • W‖ := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ (∑ j ∈ Finset.range (d + 2), A * l j) + B * l (d + 2) :=
      add_le_add (Finset.sum_le_sum fun j _ => hv j) hw
    _ ≤ (A + B) * ∑ j ∈ Finset.range (d + 3), l j := by
      have hsum : (∑ j ∈ Finset.range (d + 3), l j) =
          (∑ j ∈ Finset.range (d + 2), l j) + l (d + 2) := by
        rw [show d + 3 = (d + 2) + 1 by omega, Finset.sum_range_succ]
      rw [hsum, ← Finset.mul_sum]
      have hs : 0 ≤ ∑ j ∈ Finset.range (d + 2), l j := Finset.sum_nonneg fun j _ => hl j
      nlinarith [mul_nonneg hA.le (hl (d + 2)), mul_nonneg hB.le hs]

/-- The literal frozen seminorm controls each coordinate derivative word. -/
theorem schwartz_weighted_coordWord_le {d N k : ℕ} (hk : k ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (dirs : Fin k → Fin d) (x : Vec d) :
    (1 + euclideanNorm x) ^ N *
      ‖LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j)) F x‖ ≤
        schwartzTestNorm N F := by
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  apply le_csSup (schwartzTestNorm_set_bddAbove N F)
  exact ⟨⟨k, by omega⟩, dirs, x, rfl⟩

/-- Every permitted coordinate derivative word has the same integrable decay
weight, without spending additional derivatives of the frozen test. -/
theorem schwartz_coordWord_norm_le {d N k : ℕ} (hk : k ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (dirs : Fin k → Fin d) (x : Vec d) :
    ‖LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j)) F x‖ ≤
      (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F := by
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + ‖x‖), Real.rpow_natCast,
    ← div_eq_inv_mul, le_div_iff₀' (by positivity)]
  calc
    _ ≤ (1 + euclideanNorm x) ^ N *
        ‖LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j)) F x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact pow_le_pow_left₀ (by positivity)
        (by linarith [S1.norm_le_euclideanNorm x]) N
    _ ≤ _ := schwartz_weighted_coordWord_le hk F dirs x

/-- Coordinate derivative words through order N have a uniform structural L¹
bound in the exact finite weighted seminorm. -/
theorem integral_norm_schwartz_coordWord_le {d N k : ℕ} (hN : d < N) (hk : k ≤ N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (dirs : Fin k → Fin d) :
    (∫ x : Vec d, ‖LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j)) F x‖) ≤
      clockSchwartzWeightMass d N * schwartzTestNorm N F := by
  calc
    _ ≤ ∫ x : Vec d, (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F :=
      integral_mono (LineDeriv.iteratedLineDerivOp
        (fun j => unitVector (dirs j)) F).integrable.norm
        ((integrable_clockSchwartzWeight hN).mul_const _)
        (schwartz_coordWord_norm_le hk F dirs)
    _ = _ := integral_mul_const _ _

/-- Composition of coordinate derivatives as a linear operator on Schwartz space. -/
noncomputable def schwartzCoordWordCLM {d : ℕ} (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] :
    List (Fin d) → SchwartzMap (Vec d) E →L[ℝ] SchwartzMap (Vec d) E
  | [] => ContinuousLinearMap.id ℝ _
  | i :: l => (LineDeriv.lineDerivOpCLM ℝ (SchwartzMap (Vec d) E) (unitVector i)).comp
      (schwartzCoordWordCLM E l)

/-- The list and finite-function descriptions of a coordinate word agree. -/
theorem schwartzCoordWordCLM_ofFn {d k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dirs : Fin k → Fin d) (K : SchwartzMap (Vec d) E) :
    schwartzCoordWordCLM E (List.ofFn dirs) K =
      LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j)) K := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.ofFn_succ, schwartzCoordWordCLM, ContinuousLinearMap.comp_apply,
      LineDeriv.iteratedLineDerivOp_succ_left]
    rw [ih]
    rfl

/-- Concatenating coordinate words composes their Schwartz operators. -/
theorem schwartzCoordWordCLM_append {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (l m : List (Fin d)) (K : SchwartzMap (Vec d) E) :
    schwartzCoordWordCLM E (l ++ m) K =
      schwartzCoordWordCLM E l (schwartzCoordWordCLM E m K) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.cons_append, schwartzCoordWordCLM, ContinuousLinearMap.comp_apply, ih]

/-- Coordinate words distribute over the literal coordinate Laplacian. -/
theorem schwartzCoordWordCLM_laplacian {d : ℕ}
    (l : List (Fin d)) (K : SchwartzMap (Vec d) ℝ) :
    schwartzCoordWordCLM ℝ l (schwartzCoordLaplacian K) =
      ∑ i : Fin d, schwartzCoordWordCLM ℝ (l ++ [i, i]) K := by
  rw [schwartzCoordLaplacian, _root_.map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [schwartzCoordWordCLM_append]
  rfl

/-- A Laplacian iterate costs two coordinate derivatives per iteration.
This estimate uses coordinate words and preserves their pointwise decay weight. -/
theorem norm_schwartzCoordWordCLM_laplacian_iterate_le {d N : ℕ}
    (K : SchwartzMap (Vec d) ℝ) (x : Vec d) (M : ℝ)
    (hword : ∀ l : List (Fin d), l.length ≤ N →
      ‖schwartzCoordWordCLM ℝ l K x‖ ≤ M)
    (n : ℕ) (l : List (Fin d)) (hl : l.length + 2 * n ≤ N) :
    ‖schwartzCoordWordCLM ℝ l (schwartzCoordLaplacian^[n] K) x‖ ≤
      (d : ℝ) ^ n * M := by
  induction n generalizing l with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul, mul_zero,
      add_zero] using hword l (by simpa using hl)
  | succ n ih =>
    rw [Function.iterate_succ_apply', schwartzCoordWordCLM_laplacian]
    simp only [_root_.sum_apply]
    calc
      _ ≤ ∑ i : Fin d, ‖schwartzCoordWordCLM ℝ (l ++ [i, i])
          (schwartzCoordLaplacian^[n] K) x‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin d, (d : ℝ) ^ n * M :=
        Finset.sum_le_sum fun i _ => ih (l ++ [i, i]) (by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul, pow_succ]; ring

/-- Constant linear projections commute with all Schwartz coordinate words. -/
theorem schwartzCoordWordCLM_postcomp {d : ℕ} {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (l : List (Fin d)) (K : SchwartzMap (Vec d) E) :
    schwartzCoordWordCLM G l (K.postcompCLM L) =
      (schwartzCoordWordCLM E l K).postcompCLM L := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [schwartzCoordWordCLM, ContinuousLinearMap.comp_apply] at *
    rw [ih]
    ext x
    change fderiv ℝ (fun y => L (schwartzCoordWordCLM E l K y)) x (unitVector i) =
      L (fderiv ℝ (schwartzCoordWordCLM E l K) x (unitVector i))
    have hder := (L.hasFDerivAt.comp x
      (schwartzCoordWordCLM E l K).differentiableAt.hasFDerivAt).fderiv
    exact congrArg (fun A : Vec d →L[ℝ] G => A (unitVector i)) hder

/-- List coordinate words obey the frozen joint-test decay estimate. -/
theorem norm_schwartzCoordWordCLM_joint_le {d N : ℕ}
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (l : List (Fin d)) (hl : l.length ≤ N) (x : Vec d) :
    ‖schwartzCoordWordCLM (EuclideanSpace ℂ (JointObservationIndex d)) l F x‖ ≤
      (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F := by
  have he := schwartzCoordWordCLM_ofFn l.get F
  rw [List.ofFn_get] at he
  rw [he]
  exact schwartz_coordWord_norm_le hl F l.get x

/-- Low-order Laplacian iterates of any contractive real projection of the
joint test retain the same weighted decay and spend exactly two derivatives. -/
theorem norm_coordLaplacian_iterate_projected_le {d N : ℕ}
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (L : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ)
    (hL : ∀ v, ‖L v‖ ≤ ‖v‖) (n : ℕ) (hn : 2 * n ≤ N) (x : Vec d) :
    ‖(Correctors.coordLaplacian^[n] ⇑(F.postcompCLM L)) x‖ ≤
      (d : ℝ) ^ n * ((1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F) := by
  rw [← schwartzCoordLaplacian_iterate_coe]
  have hword (l : List (Fin d)) (hl : l.length ≤ N) :
      ‖schwartzCoordWordCLM ℝ l (F.postcompCLM L) x‖ ≤
        (1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F := by
    rw [schwartzCoordWordCLM_postcomp, SchwartzMap.postcompCLM_apply]
    exact (hL _).trans (norm_schwartzCoordWordCLM_joint_le F l hl x)
  simpa only [schwartzCoordWordCLM, ContinuousLinearMap.id_apply] using
    norm_schwartzCoordWordCLM_laplacian_iterate_le (F.postcompCLM L) x _ hword n []
      (by simpa using hn)

/-- The low-order Laplacian L¹ norms in the distribution bound are controlled
by the literal frozen seminorm, without replacing its derivative order. -/
theorem integral_norm_coordLaplacian_iterate_projected_le {d N : ℕ} (hN : d < N)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (L : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ)
    (hL : ∀ v, ‖L v‖ ≤ ‖v‖) (n : ℕ) (hn : 2 * n ≤ N) :
    (∫ x : Vec d, ‖(Correctors.coordLaplacian^[n] ⇑(F.postcompCLM L)) x‖) ≤
      (d : ℝ) ^ n * (clockSchwartzWeightMass d N * schwartzTestNorm N F) := by
  have hi := (laplacian_iterate_schwartz_regular (F.postcompCLM L) n).2.1.norm
  calc
    _ ≤ ∫ x : Vec d, (d : ℝ) ^ n *
        ((1 + ‖x‖) ^ (-(N : ℝ)) * schwartzTestNorm N F) :=
      integral_mono hi (((integrable_clockSchwartzWeight hN).mul_const _).const_mul _)
        (norm_coordLaplacian_iterate_projected_le F L hL n hn)
    _ = _ := by rw [integral_const_mul, integral_mul_const]; rfl

/-- Testing a real contractive projection of the joint test has a uniform
normalized L² bound in the original frozen seminorm. -/
theorem normalized_projected_joint_test_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R →
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ L : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ,
      (∀ v, ‖L v‖ ≤ ‖v‖) → ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ x : Vec d, L (F x) •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖ ≤
        C * schwartzTestNorm N F := by
  obtain ⟨A, hA, ha⟩ := normalized_schwartz_test_bound hclt d hd D N hN
  let M := clockSchwartzWeightMass d N
  let S := ∑ j ∈ Finset.range (d + 3), (d : ℝ) ^ j
  have hM : 0 ≤ M := integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg _) _
  refine ⟨A * (M + 1) * (S + 1), by positivity, ?_⟩
  intro Q hQ Z hZ R hR F L hL a
  have hf : 0 ≤ schwartzTestNorm N F := clockSchwartz_norm_nonneg N F
  have hb := ha Q hQ Z hZ R hR (F.postcompCLM L) a
  have hs : (∑ j ∈ Finset.range (d + 3),
      ∫ x : Vec d, ‖(Correctors.coordLaplacian^[j] ⇑(F.postcompCLM L)) x‖) ≤
      S * (M * schwartzTestNorm N F) := by
    change _ ≤ (∑ j ∈ Finset.range (d + 3), (d : ℝ) ^ j) *
      (M * schwartzTestNorm N F)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    exact integral_norm_coordLaplacian_iterate_projected_le (by omega) F L hL j
      (by have := Finset.mem_range.mp hj; omega)
  calc
    _ ≤ A * (S * (M * schwartzTestNorm N F)) :=
      hb.trans (mul_le_mul_of_nonneg_left hs hA.le)
    _ = (A * M * S) * schwartzTestNorm N F := by ring
    _ ≤ (A * (M + 1) * (S + 1)) * schwartzTestNorm N F := by gcongr <;> linarith

/-- The same frozen seminorm controls testing the Laplacian of a projected
joint test. This is the distribution estimate needed for heat-smoothing error. -/
theorem normalized_projected_joint_laplacian_test_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R →
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ L : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ,
      (∀ v, ‖L v‖ ≤ ‖v‖) → ∀ a : JointObservationIndex d,
        R ^ ((d : ℝ) / 2) *
          ‖∫ x : Vec d, Correctors.coordLaplacian (F.postcompCLM L) x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖ ≤
        C * schwartzTestNorm N F := by
  obtain ⟨A, hA, ha⟩ := normalized_schwartz_test_bound hclt d hd D N hN
  let M := clockSchwartzWeightMass d N
  let S := ∑ j ∈ Finset.range (d + 3), (d : ℝ) ^ (j + 1)
  have hM : 0 ≤ M := integral_nonneg fun _ => Real.rpow_nonneg (by positivity) _
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => pow_nonneg (Nat.cast_nonneg _) _
  refine ⟨A * (M + 1) * (S + 1), by positivity, ?_⟩
  intro Q hQ Z hZ R hR F L hL a
  have hf : 0 ≤ schwartzTestNorm N F := clockSchwartz_norm_nonneg N F
  have hco : ⇑(schwartzCoordLaplacian (F.postcompCLM L)) =
      Correctors.coordLaplacian (F.postcompCLM L) :=
    funext (schwartzCoordLaplacian_apply _)
  have hb := ha Q hQ Z hZ R hR (schwartzCoordLaplacian (F.postcompCLM L)) a
  have hs : (∑ j ∈ Finset.range (d + 3),
      ∫ x : Vec d, ‖(Correctors.coordLaplacian^[j]
        ⇑(schwartzCoordLaplacian (F.postcompCLM L))) x‖) ≤
      S * (M * schwartzTestNorm N F) := by
    change _ ≤ (∑ j ∈ Finset.range (d + 3), (d : ℝ) ^ (j + 1)) *
      (M * schwartzTestNorm N F)
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro j hj
    rw [hco]
    simpa only [Function.iterate_succ_apply] using
      integral_norm_coordLaplacian_iterate_projected_le (by omega) F L hL (j + 1)
        (by have := Finset.mem_range.mp hj; omega)
  rw [hco] at hb hs
  calc
    _ ≤ A * (S * (M * schwartzTestNorm N F)) :=
      hb.trans (mul_le_mul_of_nonneg_left hs hA.le)
    _ = (A * M * S) * schwartzTestNorm N F := by ring
    _ ≤ (A * (M + 1) * (S + 1)) * schwartzTestNorm N F := by gcongr <;> linarith

/-- Independent spatial kernels and the translated observation admit Bochner
Fubini on the full spatial product. -/
theorem integrable_heatTest_product {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × Vec d =>
      (K p.1 * Correctors.euclideanHeatKernel t p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
          (R • (p.1 + p.2)) U) (volume.prod volume) := by
  have hs := hK.mul_prod (Correctors.integrable_euclideanHeatKernel (d := d) ht)
  have hc : Continuous (fun p : Vec d × Vec d =>
      (K p.1 * Correctors.euclideanHeatKernel t p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
          (R • (p.1 + p.2)) U) :=
    ((hKc.comp continuous_fst).mul
      ((Correctors.contDiff_euclideanHeatKernel t).continuous.comp continuous_snd)).smul
      ((continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        (((continuous_fst.add continuous_snd).const_smul R).prodMk continuous_const))
  apply (hs.norm.mul_const ‖U‖).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun p => by rw [norm_smul, norm_complexTranslation]

/-- The heat average also transfers outside the entire tested observation.
The two translation orders agree by the additive action law. -/
theorem integral_heatConvolution_eq_heat_test {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 < t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, Correctors.heatKernelConvolution t K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) =
    ∫ z : Vec d, Correctors.euclideanHeatKernel t z •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z)
        (∫ y : Vec d, K y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) (R • y) U) := by
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x)
  have hadd (x y : Vec d) : τ (x + y) U = τ x (τ y U) := by
    dsimp [τ]
    rw [smul_add, complexTranslation_add]
  have hsmul (x : Vec d) (c : ℝ) (V : Lp ℂ 2 (reducedLaw Q)) :
      τ x (c • V) = c • τ x V := ((τ x).restrictScalars ℝ).map_smul c V
  rw [integral_heatConvolution_smul_translation Q K hK hKc ht R U]
  change (∫ y : Vec d, K y • τ y
      (∫ z : Vec d, Correctors.euclideanHeatKernel t z • τ z U)) =
    ∫ z : Vec d, Correctors.euclideanHeatKernel t z • τ z (∫ y : Vec d, K y • τ y U)
  calc
    _ = ∫ y : Vec d, ∫ z : Vec d,
        (K y * Correctors.euclideanHeatKernel t z) • τ (y + z) U := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← (τ y).integral_comp_comm, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hsmul, ← hadd, smul_smul]
    _ = ∫ z : Vec d, ∫ y : Vec d,
        (K y * Correctors.euclideanHeatKernel t z) • τ (y + z) U :=
      integral_integral_swap (integrable_heatTest_product Q K hK hKc ht R U)
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [← (τ z).integral_comp_comm, ← integral_smul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hsmul, ← hadd, smul_smul, mul_comm, add_comm]

/-- Smoothing the real test contracts its actual L² testing norm. -/
theorem norm_heatConvolution_test_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℝ)
    (hK : Integrable K) (hKc : Continuous K) {t : ℝ} (ht : 0 ≤ t)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    ‖∫ x : Vec d, Correctors.heatKernelConvolution t K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U‖ ≤
    ‖∫ x : Vec d, K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U‖ := by
  rcases ht.eq_or_lt with hzero | ht
  · subst t
    simp [Correctors.heatKernelConvolution]
  rw [integral_heatConvolution_eq_heat_test Q K hK hKc ht R U]
  let V := ∫ x : Vec d, K x • complexTranslation (reducedLaw Q)
    (reducedLaw_stationary Q) (R • x) U
  have hb := norm_integral_le_of_norm_le
    ((Correctors.integrable_euclideanHeatKernel (d := d) ht).mul_const ‖V‖)
    (ae_of_all _ fun x => show
      ‖Correctors.euclideanHeatKernel t x • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) (R • x) V‖ ≤ Correctors.euclideanHeatKernel t x * ‖V‖ by
      rw [norm_smul, norm_complexTranslation,
        Real.norm_of_nonneg (Correctors.euclideanHeatKernel_nonneg ht.le x)])
  simpa only [integral_mul_const, Correctors.integral_euclideanHeatKernel ht, one_mul] using hb

/-- The integrated heat equation holds in the actual complex observation L²
space, after testing by any real Schwartz function. -/
theorem integral_schwartz_heat_sub_initial {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : SchwartzMap (Vec d) ℝ)
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, Correctors.heatKernelConvolution T K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U) -
    (∫ x : Vec d, K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) =
    ∫ t in (0 : ℝ)..T, ∫ x : Vec d,
      Correctors.heatKernelConvolution t (Correctors.coordLaplacian K) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U := by
  have h := integral_schwartz_heat_finite_expansion Q K 0 hT R U
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero,
    pow_one, Nat.factorial_zero, Nat.cast_one, div_one, one_mul,
    Function.iterate_zero_apply, Function.iterate_one, one_smul, neg_one_smul] at h
  rw [h]
  abel

/-- Heat smoothing has a second-order spatial testing error: its time is the
square of the smoothing length, and no derivatives above the Laplacian occur. -/
theorem norm_schwartz_heat_test_sub_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : SchwartzMap (Vec d) ℝ)
    {T : ℝ} (hT : 0 ≤ T) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    ‖(∫ x : Vec d, K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) -
      (∫ x : Vec d, Correctors.heatKernelConvolution T K x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U)‖ ≤
    T * ‖∫ x : Vec d, Correctors.coordLaplacian K x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) U‖ := by
  rw [norm_sub_rev, integral_schwartz_heat_sub_initial Q K hT R U]
  obtain ⟨hc, hi, M, hM⟩ := laplacian_iterate_schwartz_regular K 1
  simp only [Function.iterate_one] at hc hi
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (fun t ht =>
      norm_heatConvolution_test_le Q (Correctors.coordLaplacian K) hi hc.continuous
        (show 0 ≤ t from (by rw [Set.uIoc_of_le hT] at ht; exact ht.1.le)) R U)
  simpa only [sub_zero, abs_of_nonneg hT, mul_comm] using hb

/-- The exact frozen joint seminorm controls the quadratic smoothing error of
any contractive real projection, at the original test-CLT derivative index. -/
theorem normalized_projected_joint_heat_error_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R →
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ L : EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ,
      (∀ v, ‖L v‖ ≤ ‖v‖) → ∀ a : JointObservationIndex d,
      ∀ T : ℝ, 0 ≤ T →
        R ^ ((d : ℝ) / 2) *
          ‖(∫ x : Vec d, L (F x) • complexTranslation (reducedLaw Q)
            (reducedLaw_stationary Q) (R • x) (Z a)) -
          (∫ x : Vec d, Correctors.heatKernelConvolution T (F.postcompCLM L) x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a))‖ ≤
        C * schwartzTestNorm N F * T := by
  obtain ⟨C, hC, hb⟩ := normalized_projected_joint_laplacian_test_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR F L hL a T hT
  have he := norm_schwartz_heat_test_sub_le Q (F.postcompCLM L) hT R (Z a)
  have hc := hb Q hQ Z hZ R hR F L hL a
  calc
    _ ≤ R ^ ((d : ℝ) / 2) * (T *
        ‖∫ x : Vec d, Correctors.coordLaplacian (F.postcompCLM L) x •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖) :=
      mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hR.le _)
    _ = (R ^ ((d : ℝ) / 2) *
        ‖∫ x : Vec d, Correctors.coordLaplacian (F.postcompCLM L) x •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a)‖) * T := by ring
    _ ≤ C * schwartzTestNorm N F * T := mul_le_mul_of_nonneg_right hc hT

/-- Real coordinate projection on the literal Euclidean joint carrier. -/
noncomputable def jointCoordinateReCLM {d : ℕ} (a : JointObservationIndex d) :
    EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((PiLp.proj (𝕜 := ℂ) 2
    (fun _ : JointObservationIndex d => ℂ) a).restrictScalars ℝ)

/-- Imaginary coordinate projection on the literal Euclidean joint carrier. -/
noncomputable def jointCoordinateImCLM {d : ℕ} (a : JointObservationIndex d) :
    EuclideanSpace ℂ (JointObservationIndex d) →L[ℝ] ℝ :=
  Complex.imCLM.comp ((PiLp.proj (𝕜 := ℂ) 2
    (fun _ : JointObservationIndex d => ℂ) a).restrictScalars ℝ)

/-- Real coordinate extraction is contractive for the joint Euclidean norm. -/
theorem norm_jointCoordinateReCLM_le {d : ℕ} (a : JointObservationIndex d)
    (v : EuclideanSpace ℂ (JointObservationIndex d)) :
    ‖jointCoordinateReCLM a v‖ ≤ ‖v‖ := by
  exact (Complex.abs_re_le_norm (v a)).trans (PiLp.norm_apply_le v a)

/-- Imaginary coordinate extraction is contractive for the joint Euclidean norm. -/
theorem norm_jointCoordinateImCLM_le {d : ℕ} (a : JointObservationIndex d)
    (v : EuclideanSpace ℂ (JointObservationIndex d)) :
    ‖jointCoordinateImCLM a v‖ ≤ ‖v‖ := by
  exact (Complex.abs_im_le_norm (v a)).trans (PiLp.norm_apply_le v a)

/-- Integrable complex kernels can be tested on any rescaled translation orbit. -/
theorem integrable_complexKernel_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {K : Vec d → ℂ} (hK : Integrable K)
    (hKc : Continuous K) (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) := by
  have hc : Continuous (fun x : Vec d => K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) :=
    hKc.smul ((continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      ((continuous_id.const_smul R).prodMk continuous_const))
  apply (hK.norm.mul_const ‖U‖).mono' hc.aestronglyMeasurable
  exact ae_of_all _ fun x => by rw [norm_smul, norm_complexTranslation]

/-- Complex bilinear testing is the real test plus i times the imaginary test. -/
theorem integral_complexKernel_translation_eq {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {K : Vec d → ℂ} (hK : Integrable K)
    (R : ℝ) (U : Lp ℂ 2 (reducedLaw Q)) :
    (∫ x : Vec d, K x • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) =
    (∫ x : Vec d, (K x).re • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) +
    Complex.I • (∫ x : Vec d, (K x).im • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) U) := by
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q)
    (reducedLaw_stationary Q) (R • x) U
  have hr := integrable_realKernel_translation Q hK.re R U
  have hi := integrable_realKernel_translation Q hK.im R U
  have hreal (r : ℝ) (V : Lp ℂ 2 (reducedLaw Q)) : (r : ℂ) • V = r • V :=
    algebraMap_smul ℂ r V
  calc
    _ = ∫ x : Vec d, (K x).re • τ x + Complex.I • ((K x).im • τ x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      conv_lhs => rw [← Complex.re_add_im (K x)]
      rw [add_smul, mul_comm ((K x).im : ℂ) Complex.I, mul_smul, hreal, hreal]
    _ = _ := by
      rw [integral_add (f := fun x : Vec d => (K x).re • τ x)
        (g := fun x : Vec d => Complex.I • ((K x).im • τ x)) hr (hi.smul Complex.I),
        integral_smul]

/-- A complex coordinate inherits the projected quadratic heat error, retaining
bilinear testing and the literal Euclidean joint seminorm. -/
theorem normalized_complex_coordinate_heat_error_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R →
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ a : JointObservationIndex d, ∀ T : ℝ, 0 < T →
      let V := ∫ z : Vec d, Correctors.euclideanHeatKernel T z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)
      R ^ ((d : ℝ) / 2) *
        ‖(∫ x : Vec d, F x a • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) (R • x) (Z a)) -
        (∫ x : Vec d, F x a • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) (R • x) V)‖ ≤
      C * schwartzTestNorm N F * T := by
  obtain ⟨C, hC, hb⟩ := normalized_projected_joint_heat_error_bound hclt d hd D N hN
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q hQ Z hZ R hR F a T hT
  let V := ∫ z : Vec d, Correctors.euclideanHeatKernel T z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)
  let re := F.postcompCLM (jointCoordinateReCLM a)
  let im := F.postcompCLM (jointCoordinateImCLM a)
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q)
    (reducedLaw_stationary Q) (R • x)
  have hre := hb Q hQ Z hZ R hR F (jointCoordinateReCLM a)
    (norm_jointCoordinateReCLM_le a) a T hT.le
  have him := hb Q hQ Z hZ R hR F (jointCoordinateImCLM a)
    (norm_jointCoordinateImCLM_le a) a T hT.le
  rw [integral_heatConvolution_smul_translation Q re re.integrable re.continuous hT R (Z a)] at hre
  rw [integral_heatConvolution_smul_translation Q im im.integrable im.continuous hT R (Z a)] at him
  have hk : Integrable (fun x : Vec d => F x a) := by
    apply F.integrable.mono ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
    exact ae_of_all _ fun x => PiLp.norm_apply_le (F x) a
  have heq (U : Lp ℂ 2 (reducedLaw Q)) :
      (∫ x : Vec d, F x a • τ x U) =
      (∫ x : Vec d, re x • τ x U) + Complex.I • (∫ x : Vec d, im x • τ x U) :=
    integral_complexKernel_translation_eq Q hk R U
  change R ^ ((d : ℝ) / 2) *
    ‖(∫ x : Vec d, F x a • τ x (Z a)) - (∫ x : Vec d, F x a • τ x V)‖ ≤ _
  rw [heq, heq]
  have hn : ‖((∫ x : Vec d, re x • τ x (Z a)) +
        Complex.I • (∫ x : Vec d, im x • τ x (Z a))) -
      ((∫ x : Vec d, re x • τ x V) + Complex.I • (∫ x : Vec d, im x • τ x V))‖ ≤
      ‖(∫ x : Vec d, re x • τ x (Z a)) - (∫ x : Vec d, re x • τ x V)‖ +
      ‖(∫ x : Vec d, im x • τ x (Z a)) - (∫ x : Vec d, im x • τ x V)‖ := by
    calc
      _ = ‖((∫ x : Vec d, re x • τ x (Z a)) - (∫ x : Vec d, re x • τ x V)) +
          Complex.I • ((∫ x : Vec d, im x • τ x (Z a)) - (∫ x : Vec d, im x • τ x V))‖ := by
        rw [smul_sub]
        congr 1
        abel
      _ ≤ _ := by
        simpa only [norm_smul, Complex.norm_I, one_mul] using
          (norm_add_le
            ((∫ x : Vec d, re x • τ x (Z a)) - (∫ x : Vec d, re x • τ x V))
            (Complex.I • ((∫ x : Vec d, im x • τ x (Z a)) - (∫ x : Vec d, im x • τ x V))))
  calc
    _ ≤ R ^ ((d : ℝ) / 2) *
        (‖(∫ x : Vec d, re x • τ x (Z a)) - (∫ x : Vec d, re x • τ x V)‖ +
        ‖(∫ x : Vec d, im x • τ x (Z a)) - (∫ x : Vec d, im x • τ x V)‖) :=
      mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hR.le _)
    _ ≤ C * schwartzTestNorm N F * T + C * schwartzTestNorm N F * T := by
      rw [mul_add]
      exact add_le_add hre him
    _ = (2 * C) * schwartzTestNorm N F * T := by ring

/-- Finite joint summation preserves the quadratic testing error, with a
structural constant independent of the law, observations and test. -/
theorem normalized_joint_heat_error_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, 0 < R →
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ T : ℝ, 0 < T →
      let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel T z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)
      R ^ ((d : ℝ) / 2) *
        ‖(∫ x : Vec d, ∑ a, F x a • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) (R • x) (Z a)) -
        (∫ x : Vec d, ∑ a, F x a • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) (R • x) (V a))‖ ≤
      C * schwartzTestNorm N F * T := by
  classical
  obtain ⟨C, hC, hb⟩ := normalized_complex_coordinate_heat_error_bound hclt d hd D N hN
  have hcard : 0 < (Fintype.card (JointObservationIndex d) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  refine ⟨C * Fintype.card (JointObservationIndex d), by positivity, ?_⟩
  intro Q hQ Z hZ R hR F T hT
  let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel T z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q)
    (reducedLaw_stationary Q) (R • x)
  have hi (U : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (a : JointObservationIndex d) :
      Integrable (fun x : Vec d => F x a • τ x (U a)) := by
    apply integrable_complexKernel_translation Q (K := fun x : Vec d => F x a)
      (F.integrable.mono ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
        (ae_of_all _ fun x => PiLp.norm_apply_le (F x) a))
      ((PiLp.continuous_apply 2 _ a).comp F.continuous)
  change R ^ ((d : ℝ) / 2) *
    ‖(∫ x : Vec d, ∑ a, F x a • τ x (Z a)) -
      (∫ x : Vec d, ∑ a, F x a • τ x (V a))‖ ≤ _
  rw [integral_finsetSum _ (fun a _ => hi Z a), integral_finsetSum _ (fun a _ => hi V a),
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ R ^ ((d : ℝ) / 2) * ∑ a,
        ‖(∫ x : Vec d, F x a • τ x (Z a)) - (∫ x : Vec d, F x a • τ x (V a))‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (Real.rpow_nonneg hR.le _)
    _ = ∑ a, R ^ ((d : ℝ) / 2) *
        ‖(∫ x : Vec d, F x a • τ x (Z a)) - (∫ x : Vec d, F x a • τ x (V a))‖ :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ _a : JointObservationIndex d, C * schwartzTestNorm N F * T :=
      Finset.sum_le_sum fun a _ => hb Q hQ Z hZ R hR F a T hT
    _ = (C * Fintype.card (JointObservationIndex d)) * schwartzTestNorm N F * T := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- Changing from physical to unit test coordinates leaves exactly the CLT
normalization R^(d/2) on the Bochner joint pairing. -/
theorem scaledJointPairing_rescaled {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    scaledJointPairing Q R hR Z F =
      (R ^ ((d : ℝ) / 2) : ℝ) • ∫ x : Vec d, ∑ a, F x a •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • x) (Z a) := by
  have he := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x : Vec d => ∑ a, F x a • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) (R • x) (Z a)) R⁻¹
  simp only [Module.finrank_pi, Fintype.card_fin, inv_pow, inv_inv,
    abs_of_nonneg (pow_nonneg hR.le _), smul_smul,
    mul_inv_cancel₀ hR.ne', one_smul] at he
  rw [scaledJointPairing, he]
  have hs (c : ℝ) (W : Lp ℂ 2 (reducedLaw Q)) :
      (c : ℂ) • W = c • W := algebraMap_smul ℂ c W
  rw [hs]
  rw [smul_smul, ← Real.rpow_natCast, ← Real.rpow_add hR]
  congr 2
  ring

/-- The original CLT controls the literal scaled pairing error against the
physical isotropic heat average, with the quadratic ratio (r/R)^2. -/
theorem scaledJointPairing_heat_error_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ r : ℝ, 0 < r →
      let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)
      ‖scaledJointPairing Q R hR Z F - scaledJointPairing Q R hR V F‖ ≤
        C * schwartzTestNorm N F * (r / R) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := normalized_joint_heat_error_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR F r hr
  let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)
  have hT : 0 < (r / R) ^ 2 := by positivity
  have hv (a : JointObservationIndex d) :
      (∫ z : Vec d, Correctors.euclideanHeatKernel ((r / R) ^ 2) z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (R • z) (Z a)) = V a := by
    rw [integral_heatKernel_smul_scaled_translation Q hT hR]
    have he : R ^ 2 * (r / R) ^ 2 = r ^ 2 := by field_simp
    rw [he]
  have he := hb Q hQ Z hZ R hR F ((r / R) ^ 2) hT
  dsimp only at he
  simp_rw [hv] at he
  change ‖scaledJointPairing Q R hR Z F - scaledJointPairing Q R hR V F‖ ≤ _
  rw [scaledJointPairing_rescaled, scaledJointPairing_rescaled, ← smul_sub,
    norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hR.le _)]
  exact he

/-- An integrable family of L² classes has the expected literal integral
representative whenever its chosen representatives are jointly integrable. -/
theorem coeFn_integral_lp_ae {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
    (ν : Measure α) [SFinite ν] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : α → Lp ℂ 2 μ) (g : α × Ω → ℂ)
    (hf : Integrable f ν) (hg : Integrable g (ν.prod μ))
    (heq : ∀ a, (f a : Ω → ℂ) =ᵐ[μ] fun ω => g (a, ω)) :
    (∫ a, f a ∂ν : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∫ a, g (a, ω) ∂ν := by
  let U : Lp ℂ 2 μ := ∫ a, f a ∂ν
  apply Integrable.ae_eq_of_forall_setIntegral_eq (U : Ω → ℂ)
    (fun ω => ∫ a, g (a, ω) ∂ν)
    ((Lp.memLp U).integrable (by norm_num)) hg.integral_prod_right
  intro s hs _hμs
  let W : Lp ℂ 2 μ := indicatorConstLp 2 hs (measure_ne_top μ s) (1 : ℂ)
  have hgs : Integrable g (ν.prod (μ.restrict s)) :=
    hg.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ ω in s, U ω ∂μ) = inner ℂ W U :=
      (L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) U).symm
    _ = ∫ a, inner ℂ W (f a) ∂ν := ((innerSL ℂ W).integral_comp_comm hf).symm
    _ = ∫ a, ∫ ω in s, g (a, ω) ∂μ ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ fun a =>
        (L2.inner_indicatorConstLp_one hs (measure_ne_top μ s) (f a)).trans
          (integral_congr_ae (ae_restrict_of_ae (heq a)))
    _ = ∫ ω in s, ∫ a, g (a, ω) ∂ν ∂μ := integral_integral_swap hgs

/-- Integrable spatial kernels and stationary L² observations give a jointly
integrable literal translated product. -/
theorem integrable_complexKernel_literal_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℂ) (hK : Integrable K)
    (hKc : Continuous K) (U : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) :
    Integrable (fun p : Vec d × FieldPair d => K p.1 * U (translate (x + p.1) p.2))
      (volume.prod (reducedLaw Q)) := by
  let := reducedLaw_probability Q
  have hT : Measurable (fun p : Vec d × FieldPair d => translate (x + p.1) p.2) :=
    Probability.continuous_translate.measurable.comp
      ((measurable_const.add measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : Vec d × FieldPair d =>
      K p.1 * U (translate (x + p.1) p.2)) :=
    (hKc.measurable.comp measurable_fst).mul ((Lp.stronglyMeasurable U).measurable.comp hT)
  have hU : Integrable (U : FieldPair d → ℂ) (reducedLaw Q) :=
    (Lp.memLp U).integrable (by norm_num)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun z =>
    ((measurePreserving_translate _ (reducedLaw_stationary Q)
      (x + z)).integrable_comp (Lp.stronglyMeasurable U).aestronglyMeasurable |>.mpr hU).const_mul (K z), ?_⟩
  have hn (z : Vec d) : (∫ ω, ‖K z * U (translate (x + z) ω)‖ ∂reducedLaw Q) =
      ‖K z‖ * ∫ ω, ‖U ω‖ ∂reducedLaw Q := by
    simp_rw [norm_mul]
    rw [integral_const_mul]
    congr 1
    exact Probability.integral_translate _ (reducedLaw_stationary Q) (x + z)
      (fun ω => ‖U ω‖) (Lp.stronglyMeasurable U).measurable.norm
  exact (hK.norm.mul_const (∫ ω, ‖U ω‖ ∂reducedLaw Q)).congr
    (ae_of_all _ fun z => (hn z).symm)

/-- The translated Bochner kernel average has the literal translated integral
as its representative, with equality asserted almost everywhere. -/
theorem coeFn_complexKernel_average_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (K : Vec d → ℂ) (hK : Integrable K)
    (hKc : Continuous K) (U : Lp ℂ 2 (reducedLaw Q)) (x : Vec d) :
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (∫ z : Vec d, K z • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) z U) : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∫ z : Vec d, K z * U (translate (x + z) ω) := by
  let := reducedLaw_probability Q
  let τ := fun z : Vec d => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z
  have hi : Integrable (fun z : Vec d => K z • τ (x + z) U) := by
    have he (z : Vec d) : K z • τ (x + z) U = K z • τ z (τ x U) := by
      rw [add_comm x z, complexTranslation_add]
    simp_rw [he]
    exact integrable_kernel_complexTranslation _ _ K hK hKc (τ x U)
  have he : τ x (∫ z : Vec d, K z • τ z U) = ∫ z : Vec d, K z • τ (x + z) U := by
    rw [← (τ x).integral_comp_comm]
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      change τ x (K z • τ z U) = K z • τ (x + z) U
      rw [(τ x).map_smul, complexTranslation_add]
  rw [he]
  apply coeFn_integral_lp_ae volume (reducedLaw Q) _ _ hi
    (integrable_complexKernel_literal_translation Q K hK hKc U x)
  intro z
  filter_upwards [Lp.coeFn_smul (K z) (τ (x + z) U),
    coeFn_complexTranslation _ (reducedLaw_stationary Q) (x + z) U] with ω hs ht
  change (K z • τ (x + z) U : Lp ℂ 2 (reducedLaw Q)) ω = _ at hs
  rw [hs]
  change K z * (τ (x + z) U : Lp ℂ 2 (reducedLaw Q)) ω = _
  rw [ht]

/-- The physical heat average represents the literal source smoothing at every
fixed spatial point, with the required almost-everywhere qualifier. -/
theorem coeFn_heat_average_translation {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (r : ℝ) (hr : 0 < r) (x : Vec d) (a : JointObservationIndex d) :
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)) :
      FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => covarianceSmoothedField Q Z r x ω a := by
  let K : Vec d → ℂ := fun z => (Correctors.euclideanHeatKernel (r ^ 2) z : ℂ)
  have hK : Integrable K :=
    (Correctors.integrable_euclideanHeatKernel (d := d) (sq_pos_of_pos hr)).ofReal
  have hKc : Continuous K := Complex.continuous_ofReal.comp
    (Correctors.continuous_euclideanHeatKernel (r ^ 2))
  have h := coeFn_complexKernel_average_translation Q K hK hKc (Z a) x
  have he : (∫ z : Vec d, K z • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) z (Z a)) =
      ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a) := by
    apply integral_congr_ae
    exact ae_of_all _ fun z => algebraMap_smul ℂ
      (Correctors.euclideanHeatKernel (r ^ 2) z)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a))
  rw [he] at h
  filter_upwards [h] with ω hω
  rw [hω]
  change (∫ z : Vec d, (Correctors.euclideanHeatKernel (r ^ 2) z : ℂ) *
      Z a (translate (x + z) ω)) =
    ∫ z : Vec d, (Correctors.euclideanHeatKernel (r ^ 2) (z - 0) : ℂ) *
      Z a (translate (x - z) ω)
  conv_lhs => rw [← integral_neg_eq_self]
  simp only [Correctors.euclideanHeatKernel_neg, sub_eq_add_neg, neg_zero, add_zero]

/-- The L² spatial pairing agrees with its literal scalar integral almost
everywhere; the normalization remains outside the integral. -/
theorem coeFn_scaledJointPairing {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    (scaledJointPairing Q R hR Z F : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * ∫ x : Vec d,
        ∑ a, F (R⁻¹ • x) a * Z a (translate x ω) := by
  let := reducedLaw_probability Q
  let τ := fun x : Vec d => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
  let f := fun x : Vec d => ∑ a, F (R⁻¹ • x) a • τ x (Z a)
  let g := fun p : Vec d × FieldPair d => ∑ a,
    F (R⁻¹ • p.1) a * Z a (translate p.1 p.2)
  have hg : Integrable g (volume.prod (reducedLaw Q)) := by
    apply integrable_finsetSum
    intro a _
    have hFa : Integrable (fun x : Vec d => F x a) := by
      apply F.integrable.mono
        ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun x => PiLp.norm_apply_le (F x) a)
    simpa only [zero_add] using integrable_complexKernel_literal_translation Q
      (fun x => F (R⁻¹ • x) a) (hFa.comp_smul (inv_ne_zero hR.ne'))
      (((PiLp.continuous_apply 2 _ a).comp F.continuous).comp
        (continuous_id.const_smul R⁻¹)) (Z a) 0
  have he (x : Vec d) : (f x : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => g (x, ω) := by
    apply (Lp.coeFn_finsetSum Finset.univ _).trans
    have ha (a : JointObservationIndex d) :
        (fun ω => (F (R⁻¹ • x) a • τ x (Z a) : Lp ℂ 2 (reducedLaw Q)) ω) =ᵐ[
          reducedLaw Q] fun ω => F (R⁻¹ • x) a * Z a (translate x ω) := by
      apply (Lp.coeFn_smul (F (R⁻¹ • x) a) (τ x (Z a))).trans
      filter_upwards [coeFn_complexTranslation _ (reducedLaw_stationary Q) x (Z a)]
        with ω hω
      simpa only [Pi.smul_apply, smul_eq_mul] using congrArg
        (fun z : ℂ => F (R⁻¹ • x) a * z) hω
    have hsum := eventuallyEq_sum (s := Finset.univ) (fun a _ => ha a)
    filter_upwards [hsum] with ω hω
    simpa only [g, Finset.sum_apply] using hω
  have hi := coeFn_integral_lp_ae volume (reducedLaw Q) f g
    (integrable_scaledJointPairing_integrand Q R hR Z F) hg he
  apply (Lp.coeFn_smul (((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ)) (∫ x, f x)).trans
  filter_upwards [hi] with ω hω
  simpa only [Pi.smul_apply, smul_eq_mul] using congrArg
    (fun z : ℂ => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * z) hω

/-- Spatial testing of the physical heat average represents exactly the literal
smoothed pairing, including its normalization and complex bilinear pairing. -/
theorem coeFn_scaledJointPairing_heat_average {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
    (r : ℝ) (hr : 0 < r) :
    let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)
    (scaledJointPairing Q R hR V F : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      covarianceSmoothedPairing Q Z R r F := by
  let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)
  have hm : Measurable (fun p : Vec d × FieldPair d =>
      fun a => V a (translate p.1 p.2)) := by
    apply Measurable.of_eval
    intro a
    exact (Lp.stronglyMeasurable (V a)).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_fst.prodMk measurable_snd))
  have he (x : Vec d) : (fun ω a => V a (translate x ω)) =ᵐ[reducedLaw Q]
      covarianceSmoothedField Q Z r x := by
    have ha : ∀ a : JointObservationIndex d,
        (fun ω => V a (translate x ω)) =ᵐ[reducedLaw Q]
        (fun ω => covarianceSmoothedField Q Z r x ω a) := fun a =>
      (coeFn_complexTranslation _ (reducedLaw_stationary Q) x (V a)).symm.trans
        (coeFn_heat_average_translation Q Z r hr x a)
    exact (ae_all_iff.mpr ha).mono fun ω hω => funext hω
  have hp : (fun p : Vec d × FieldPair d => fun a => V a (translate p.1 p.2)) =ᵐ[
      volume.prod (reducedLaw Q)] (fun p => covarianceSmoothedField Q Z r p.1 p.2) :=
    (ae_prod_iff_ae_ae (measurableSet_eq_fun hm (smoothedField_measurable Q Z r))).mpr
      (Filter.Eventually.of_forall he)
  have hs := ae_ae_of_ae_prod
    (measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hp)
  filter_upwards [coeFn_scaledJointPairing Q R hR V F, hs] with ω hω hω'
  rw [hω]
  apply congrArg (fun z : ℂ => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * z)
  apply integral_congr_ae
  filter_upwards [hω'] with x hx
  exact Finset.sum_congr rfl fun a _ => congrArg (fun z : ℂ => F (R⁻¹ • x) a * z)
    (congrFun hx a)

/-- The first replacement estimate for the literal source smoothing, at the
original Schwartz order and with its uniform constant chosen before the law. -/
theorem scaledJointPairing_smoothed_error_bound
    (hclt : node_e_u3A_test_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (N : ℕ) (hN : 2 * d + 10 < N) :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q), IsJointObservation Q Z →
      ∀ R : ℝ, ∀ hR : 0 < R,
      ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
      ∀ r : ℝ, 0 < r →
      covarianceComplexL2Size (reducedLaw Q)
        (fun ω => scaledJointPairing Q R hR Z F ω - covarianceSmoothedPairing Q Z R r F ω) ≤
        C * schwartzTestNorm N F * (r / R) ^ 2 := by
  obtain ⟨C, hC, hb⟩ := scaledJointPairing_heat_error_bound hclt d hd D N hN
  refine ⟨C, hC, ?_⟩
  intro Q hQ Z hZ R hR F r hr
  let V := fun a => ∫ z : Vec d, Correctors.euclideanHeatKernel (r ^ 2) z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) z (Z a)
  have he : (scaledJointPairing Q R hR Z F - scaledJointPairing Q R hR V F :
      Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => scaledJointPairing Q R hR Z F ω - covarianceSmoothedPairing Q Z R r F ω :=
    (Lp.coeFn_sub _ _).trans ((Filter.EventuallyEq.rfl).sub
      (coeFn_scaledJointPairing_heat_average Q R hR Z F r hr))
  have hn := integral_congr_ae (he.mono fun ω hω => congrArg (fun z : ℂ => ‖z‖ ^ 2) hω)
  change Real.sqrt _ ≤ _
  rw [← hn]
  change S1.l2Size (reducedLaw Q)
    (⇑(scaledJointPairing Q R hR Z F - scaledJointPairing Q R hR V F)) ≤ _
  rw [S1.l2Size_lp]
  exact hb Q hQ Z hZ R hR F r hr

end EinsteinFull.Calculus.C2TestReplacement
