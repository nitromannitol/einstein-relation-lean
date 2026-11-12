import EinsteinRelation.Correctors.P53SourceSkewDiagonalTruncation
import EinsteinRelation.Correctors.HeatGradientTranslation
import EinsteinRelation.Correctors.KernelConvolutionBands
import EinsteinRelation.Correctors.P53SourceSkewVitali
import EinsteinRelation.Correctors.P53SourceSkewErgodic
import EinsteinRelation.Correctors.L2TestPairingContinuity
import EinsteinRelation.Calculus.HorizontalTranslationLpGen
import EinsteinRelation.Entropy.LocalTestApproximation
import EinsteinRelation.Entropy.DivergenceSecondAssertion

/-!
# The row-divergence identity of the heat-selected flux corrector

Source: `paper/main.tex:688-702,732-748`; AKM Lemma 6.1, Step 4. For a stationary,
square-integrable, mean-zero and samplewise divergence-free source `g`, the
stationary gradient `F` selected by the heat formula (6.7) satisfies
`Σ_k F_{jkk} = g_j` almost surely. Tested against a smooth function, the diagonal
truncations equal a small-time heat average of `g_j` minus a large-time one. The
large-time averages converge along a subsequence to the tested defect
`H = g_j - Σ_k F_{jkk}`; they have mean zero and are bounded in `L²`, so `H` has
mean zero, and their translates merge, so `H` is translation invariant.
Ergodicity of the law then forces `H = 0`.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

variable {d : ℕ}

/-- A literal truncation of AKM (6.7) observed at the origin of the orbit. -/
def truncationAtOrigin (g : FieldPair d → Vec d) (m n : ℕ) (j k l : Fin d)
    (ω : FieldPair d) : ℝ :=
  iteratedAKMHeatGradientTruncation (fun y => g (translate y ω)) m n j k l 0

theorem truncationAtOrigin_translate (g : FieldPair d → Vec d) (m n : ℕ) (j k l : Fin d)
    (ρ : FieldPair d) (x : Vec d) :
    truncationAtOrigin g m n j k l (translate x ρ) =
      iteratedAKMHeatGradientTruncation (fun y => g (translate y ρ)) m n j k l x := by
  have h := iteratedAKMHeatGradientTruncation_translation (fun y => g (translate y ρ)) x m n
    j k l 0
  rw [zero_add] at h
  rw [← h]
  unfold truncationAtOrigin
  simp only [translate_add]

/-- Local `L²` convergence on a ball containing the support of a continuous test
gives convergence of the tested integrals. -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm_ball {ι : Type*} {l : Filter ι} {R : ℝ}
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ)
    (hsupp : tsupport ψ ⊆ ball 0 R) {f : ι → Vec d → ℝ} {h : Vec d → ℝ}
    (hf : ∀ i, MemLp (f i) 2 (volume.restrict (ball 0 R)))
    (hh : MemLp h 2 (volume.restrict (ball 0 R)))
    (hlim : Tendsto (fun i => eLpNorm (fun x => f i x - h x) 2 (volume.restrict (ball 0 R)))
      l (𝓝 0)) :
    Tendsto (fun i => ∫ x, ψ x * f i x) l (𝓝 (∫ x, ψ x * h x)) := by
  set U : Set (Vec d) := ball 0 R with hUdef
  have hU : MeasurableSet U := by
    rw [hUdef]
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  haveI : IsFiniteMeasure (volume.restrict U) := by
    have : volume U < ⊤ := by
      have hb : Bornology.IsBounded U := by
        rw [Metric.isBounded_iff_subset_closedBall (0 : Vec d)]
        refine ⟨R, fun x hx => ?_⟩
        rw [Metric.mem_closedBall, dist_zero_right]
        have hx' : euclideanNorm (x - 0) < R := hx
        rw [sub_zero] at hx'
        refine le_trans ?_ hx'.le
        refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
        rw [Real.norm_eq_abs]
        have hsq : x i ^ 2 ≤ euclideanSq x := by
          unfold euclideanSq dot
          rw [sq]
          exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
        exact Real.abs_le_sqrt hsq
      exact hb.measure_lt_top
    exact isFiniteMeasure_restrict.mpr this.ne
  have hcont := continuous_integral_mul_L2 U ψ hψ hψc
  have hLp : Tendsto (fun i => (hf i).toLp (f i)) l (𝓝 (hh.toLp h)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine hlim.congr fun i => eLpNorm_congr_ae ?_
    filter_upwards [(hf i).coeFn_toLp, hh.coeFn_toLp] with x h1 h2
    simp only [Pi.sub_apply, h1, h2]
  have hT := (hcont.tendsto _).comp hLp
  have hrw (u : Vec d → ℝ) (hu : MemLp u 2 (volume.restrict U)) :
      (∫ x in U, hu.toLp u x * ψ x) = ∫ x, ψ x * u x := by
    rw [integral_congr_ae (hu.coeFn_toLp.mono fun x hx => by rw [hx])]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · exact integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    · intro x hx
      have : ψ x = 0 := image_eq_zero_of_notMem_tsupport fun hxs => hx (hsupp hxs)
      rw [this, mul_zero]
  simp only [Function.comp_def, hrw _ (hf _), hrw _ hh] at hT
  exact hT

/-- A selected heat gradient is the limit of the tested truncations. -/
theorem tendsto_integral_mul_truncation_of_heatSelected {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (hsel : IsHeatSelectedFluxGradient g G)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (j k l : Fin d) :
    Tendsto (fun mn : ℕ × ℕ =>
        ∫ x, ψ x * iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x)
      atTop (𝓝 (∫ x, ψ x * G j k x l)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    hψc.isCompact.isBounded
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt d * R)
  have hsupp : tsupport ψ ⊆ ball 0 ((N : ℝ) + 1) := by
    intro x hx
    have hxR := hR hx
    rw [Metric.mem_closedBall, dist_zero_right] at hxR
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    rw [sub_zero]
    have hsq : euclideanSq x ≤ d * ‖x‖ ^ 2 := by
      unfold euclideanSq dot
      calc (∑ i, x i * x i) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
            refine Finset.sum_le_sum fun i _ => ?_
            have h := norm_le_pi_norm x i
            rw [Real.norm_eq_abs] at h
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = d * ‖x‖ ^ 2 := by simp
    have hnorm : euclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
      unfold euclideanNorm
      rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg d)]
      exact Real.sqrt_le_sqrt hsq
    calc euclideanNorm x ≤ Real.sqrt d * ‖x‖ := hnorm
      _ ≤ Real.sqrt d * R := mul_le_mul_of_nonneg_left hxR (Real.sqrt_nonneg _)
      _ < (N : ℝ) + 1 := by linarith
  obtain ⟨-, hT, hG, hlim⟩ := hsel j k l N
  exact tendsto_integral_mul_of_tendsto_eLpNorm_ball hψ hψc hsupp
    (fun mn => hT mn.1 mn.2) hG hlim

/-- Convolution of a finite sum of observables is almost surely the sum. -/
theorem horizontalMollify_finset_sum_ae {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ι : Type*} (s : Finset ι) {K : Vec d → ℝ} (hK : Measurable K)
    (hKi : Integrable K volume) {f : ι → FieldPair d → ℝ} (hf : ∀ i, Measurable (f i))
    (hfi : ∀ i, Integrable (f i) Q) :
    horizontalMollify K (fun ω => ∑ i ∈ s, f i ω) =ᵐ[Q]
      fun ω => ∑ i ∈ s, horizontalMollify K (f i) ω := by
  have hae : ∀ᵐ ω ∂Q, ∀ i ∈ s, Integrable (fun z => K z * f i (translate z ω)) volume :=
    (Filter.eventually_all_finset s).mpr fun i _ =>
      ae_integrable_kernel_translate hQ hK hKi (hf i) (hfi i)
  filter_upwards [hae] with ω hω
  simp only [horizontalMollify, Finset.mul_sum]
  exact integral_finset_sum s hω

/-- Along almost every orbit, the tested diagonal truncations converge to the tested
diagonal of the selected stationary gradient. -/
theorem ae_tendsto_sum_horizontalMollify_truncation {Q : Measure (FieldPair d)}
    {g : FieldPair d → Vec d} {F : FieldPair d → Fin d → Fin d → Fin d → ℝ}
    (hsel : ∀ᵐ ρ ∂Q, IsHeatSelectedFluxGradient (fun y => g (translate y ρ))
      (fun j k x l => F (translate x ρ) j k l))
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∀ᵐ ρ ∂Q, Tendsto (fun mn : ℕ × ℕ =>
        ∑ k : Fin d, horizontalMollify ψ (truncationAtOrigin g mn.1 mn.2 j k k) ρ)
      atTop (𝓝 (∑ k : Fin d, horizontalMollify ψ (fun ω => F ω j k k) ρ)) := by
  filter_upwards [hsel] with ρ hρ
  refine tendsto_finset_sum _ fun k _ => ?_
  unfold horizontalMollify
  simp only [truncationAtOrigin_translate]
  exact tendsto_integral_mul_truncation_of_heatSelected hρ hψ hψc j k k

/-- Standing hypotheses on the source and the selected stationary gradient. -/
structure HeatSelectedDivergenceData (Q : Measure (FieldPair d)) where
  g : FieldPair d → Vec d
  F : FieldPair d → Fin d → Fin d → Fin d → ℝ
  measurable_g : Measurable g
  memLp_g : ∀ k, MemLp (fun ω => g ω k) 2 Q
  mean_g : ∀ k, ∫ ω, g ω k ∂Q = 0
  divergence_free : ∀ᵐ ρ ∂Q,
    HasWeakDivergence Set.univ (fun x => g (translate x ρ)) (fun _ => 0)
  measurable_F : ∀ j k l, Measurable (fun ω => F ω j k l)
  memLp_F : ∀ j k l, MemLp (fun ω => F ω j k l) 2 Q
  selected : ∀ᵐ ρ ∂Q, IsHeatSelectedFluxGradient (fun y => g (translate y ρ))
    (fun j k x l => F (translate x ρ) j k l)

namespace HeatSelectedDivergenceData

variable {Q : Measure (FieldPair d)} (D : HeatSelectedDivergenceData Q)

theorem measurable_coord (i : Fin d) : Measurable (fun ω => D.g ω i) :=
  (measurable_pi_apply i).comp D.measurable_g

theorem integrable_coord [IsProbabilityMeasure Q] (i : Fin d) : Integrable (fun ω => D.g ω i) Q :=
  (D.memLp_g i).integrable one_le_two

theorem integrable_F [IsProbabilityMeasure Q] (j k l : Fin d) :
    Integrable (fun ω => D.F ω j k l) Q :=
  (D.memLp_F j k l).integrable one_le_two

theorem measurable_heatSmoothed_coord (t : ℝ) (i : Fin d) :
    Measurable (heatSmoothed t (fun ω => D.g ω i)) :=
  (measurable_heatSmoothed_joint (D.measurable_coord i)).comp
    (measurable_const.prodMk measurable_id)

/-- The diagonal defect `g_j - Σ_k F_{jkk}`. -/
def defect (j : Fin d) (ω : FieldPair d) : ℝ := D.g ω j - ∑ k : Fin d, D.F ω j k k

theorem measurable_defect (j : Fin d) : Measurable (D.defect j) :=
  (D.measurable_coord j).sub (Finset.measurable_sum _ fun k _ => D.measurable_F j k k)

theorem integrable_defect [IsProbabilityMeasure Q] (j : Fin d) : Integrable (D.defect j) Q :=
  (D.integrable_coord j).sub (integrable_finset_sum _ fun k _ => D.integrable_F j k k)

/-- Tested defect as a difference of tested convolutions. -/
theorem horizontalMollify_defect_ae [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ψ : Vec d → ℝ}
    (hψ : Measurable ψ) (hψi : Integrable ψ volume) (j : Fin d) :
    horizontalMollify ψ (D.defect j) =ᵐ[Q] fun ρ =>
      horizontalMollify ψ (fun ω => D.g ω j) ρ -
        ∑ k : Fin d, horizontalMollify ψ (fun ω => D.F ω j k k) ρ := by
  filter_upwards [horizontalMollify_sub_ae hQ hψ hψi (D.measurable_coord j)
      (D.integrable_coord j) (Finset.measurable_sum _ fun k _ => D.measurable_F j k k)
      (integrable_finset_sum _ fun k _ => D.integrable_F j k k),
    horizontalMollify_finset_sum_ae hQ Finset.univ hψ hψi (fun k => D.measurable_F j k k)
      (fun k => D.integrable_F j k k)] with ρ h1 h2
  show horizontalMollify ψ (fun ω => D.g ω j - ∑ k : Fin d, D.F ω j k k) ρ = _
  rw [h1, h2]

/-- Large-time heat averages converge, along a subsequence, to the tested defect. -/
theorem exists_subseq_ae_tendsto_largeTime [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ρ ∂Q, Tendsto (fun k =>
      horizontalMollify ψ (heatSmoothed ((φ k + 1 : ℕ) : ℝ) (fun ω => D.g ω j)) ρ)
      atTop (𝓝 (horizontalMollify ψ (D.defect j) ρ)) := by
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  obtain ⟨φ, hφ, hlim⟩ := exists_subseq_ae_tendsto_of_sub (μ := Q)
    (X := fun mn ρ => ∑ k : Fin d, horizontalMollify ψ (truncationAtOrigin D.g mn.1 mn.2 j k k) ρ)
    (A := fun m ρ => horizontalMollify ψ
      (heatSmoothed (((m + 1 : ℕ) : ℝ)⁻¹) (fun ω => D.g ω j)) ρ)
    (B := fun n ρ => horizontalMollify ψ
      (heatSmoothed ((n + 1 : ℕ) : ℝ) (fun ω => D.g ω j)) ρ)
    (Y := fun ρ => ∑ k : Fin d, horizontalMollify ψ (fun ω => D.F ω j k k) ρ)
    (A' := horizontalMollify ψ (fun ω => D.g ω j))
    (fun m => (measurable_horizontalMollify ψ hψm
      (D.measurable_heatSmoothed_coord _ j)).aestronglyMeasurable)
    (measurable_horizontalMollify ψ hψm (D.measurable_coord j)).aestronglyMeasurable
    (fun m n => ae_sum_horizontalMollify_truncation_diag Q hQ D.measurable_g D.memLp_g
      D.divergence_free hψ hψc m n j)
    (ae_tendsto_sum_horizontalMollify_truncation D.selected hψ.continuous hψc j)
    (tendsto_eLpNorm_horizontalMollify_heatSmoothed_inv_sub Q hQ (hψ.of_le (by norm_cast))
      hψc (D.measurable_coord j) (D.integrable_coord j))
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hlim, D.horizontalMollify_defect_ae hQ hψm hψi j] with ρ h1 h2
  rw [h2]
  exact h1

/-- The large-time heat averages of the source are bounded in `L²` and have mean
zero. -/
theorem horizontalMollify_heatSmoothed_bound_mean [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ψ : Vec d → ℝ} (hψ : Measurable ψ) (hψi : Integrable ψ volume)
    (j : Fin d) (t : ℝ) (ht : 0 ≤ t) :
    eLpNorm (horizontalMollify ψ (heatSmoothed t (fun ω => D.g ω j))) 2 Q ≤
        ENNReal.ofReal ((∫ x, |ψ x|) * (eLpNorm (fun ω => D.g ω j) 2 Q).toReal) ∧
      ∫ ρ, horizontalMollify ψ (heatSmoothed t (fun ω => D.g ω j)) ρ ∂Q = 0 := by
  have hHm := D.measurable_heatSmoothed_coord t j
  have h2 := eLpNorm_heatSmoothed_le Q hQ (by norm_num : (1 : ℝ) ≤ 2) (D.measurable_coord j) ht
  have h1 := eLpNorm_heatSmoothed_le Q hQ le_rfl (D.measurable_coord j) ht
  rw [ENNReal.ofReal_one] at h1
  have hHi : Integrable (heatSmoothed t (fun ω => D.g ω j)) Q :=
    memLp_one_iff_integrable.mp ⟨hHm.aestronglyMeasurable,
      h1.trans_lt (memLp_one_iff_integrable.mpr (D.integrable_coord j)).eLpNorm_lt_top⟩
  have hfn : eLpNorm (heatSmoothed t (fun ω => D.g ω j)) (ENNReal.ofReal 2) Q ≤
      ENNReal.ofReal (eLpNorm (fun ω => D.g ω j) 2 Q).toReal := by
    rw [ENNReal.ofReal_toReal (D.memLp_g j).eLpNorm_ne_top]
    simpa only [ENNReal.ofReal_ofNat] using h2
  have hm := (horizontalMollify_moment_le Q hQ (by norm_num : (1 : ℝ) ≤ 2)
    ENNReal.toReal_nonneg hψ hψi hHm hfn).2.2
  refine ⟨by simpa only [ENNReal.ofReal_ofNat] using hm, ?_⟩
  rw [integral_horizontalMollify_of_integrable Q hQ hψ hψi hHm hHi,
    integral_heatSmoothed Q hQ (D.measurable_coord j) (D.integrable_coord j) t ht, D.mean_g j,
    mul_zero]

/-- The tested defect has mean zero. -/
theorem integral_horizontalMollify_defect [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    ∫ ρ, horizontalMollify ψ (D.defect j) ρ ∂Q = 0 := by
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  obtain ⟨φ, -, hlim⟩ := D.exists_subseq_ae_tendsto_largeTime hQ hψ hψc j
  exact (integral_eq_zero_of_tendsto_ae_of_eLpNorm_two_le
    (fun n => (measurable_horizontalMollify ψ hψm
      (D.measurable_heatSmoothed_coord _ j)).aestronglyMeasurable)
    (fun n => (D.horizontalMollify_heatSmoothed_bound_mean hQ hψm hψi j _
      (Nat.cast_nonneg _)).1)
    (fun n => (D.horizontalMollify_heatSmoothed_bound_mean hQ hψm hψi j _
      (Nat.cast_nonneg _)).2) hlim).2

/-- Large-time heat averages tested with a translation difference vanish in `L¹`. -/
theorem tendsto_eLpNorm_translate_difference [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d)
    (z : Vec d) :
    Tendsto (fun n => eLpNorm (fun ρ => horizontalMollify (fun x => ψ (x - z) - ψ x)
      (heatSmoothed ((n + 1 : ℕ) : ℝ) (fun ω => D.g ω j)) ρ - 0) 1 Q) atTop (𝓝 0) := by
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hψz : Continuous (fun x => ψ (x - z)) :=
    hψ.continuous.comp (continuous_id.sub continuous_const)
  have hψzi : Integrable (fun x => ψ (x - z)) volume :=
    hψz.integrable_of_hasCompactSupport (hψc.comp_homeomorph (Homeomorph.subRight z))
  refine (tendsto_eLpNorm_horizontalMollify_heatSmoothed_translate_sub Q hQ hψ.continuous
    hψc (D.measurable_coord j) (D.integrable_coord j) z).congr fun n => ?_
  refine eLpNorm_congr_ae ?_
  have h1 := eLpNorm_heatSmoothed_le Q hQ le_rfl (D.measurable_coord j)
    (Nat.cast_nonneg (n + 1))
  rw [ENNReal.ofReal_one] at h1
  have hHi : Integrable (heatSmoothed ((n + 1 : ℕ) : ℝ) (fun ω => D.g ω j)) Q :=
    memLp_one_iff_integrable.mp ⟨(D.measurable_heatSmoothed_coord _ j).aestronglyMeasurable,
      h1.trans_lt (memLp_one_iff_integrable.mpr (D.integrable_coord j)).eLpNorm_lt_top⟩
  filter_upwards [horizontalMollify_sub_kernel_ae hQ hψz.measurable hψzi hψm hψi
    (D.measurable_heatSmoothed_coord _ j) hHi] with ρ hρ
  rw [hρ, sub_zero]

/-- Tested against any smooth compact function, the defect is translation invariant. -/
theorem horizontalMollify_defect_translate [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d)
    (z : Vec d) :
    horizontalMollify ψ (fun ρ => D.defect j (translate z ρ)) =ᵐ[Q]
      horizontalMollify ψ (D.defect j) := by
  have hψz : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ (x - z)) :=
    hψ.comp (contDiff_id.sub contDiff_const)
  have hψzc : HasCompactSupport (fun x => ψ (x - z)) :=
    hψc.comp_homeomorph (Homeomorph.subRight z)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun x => ψ (x - z) - ψ x) := hψz.sub hψ
  have hχc : HasCompactSupport (fun x => ψ (x - z) - ψ x) := hψzc.sub hψc
  have hψm : Measurable ψ := hψ.continuous.measurable
  have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hψc
  have hψzm : Measurable (fun x => ψ (x - z)) := hψz.continuous.measurable
  have hψzi : Integrable (fun x => ψ (x - z)) volume :=
    hψz.continuous.integrable_of_hasCompactSupport hψzc
  obtain ⟨φ, hφ, hlim⟩ := D.exists_subseq_ae_tendsto_largeTime hQ hχ hχc j
  have hL1 := D.tendsto_eLpNorm_translate_difference hQ hψ hψc j z
  have hzero := ae_eq_of_subseq_tendsto_ae_of_tendsto_eLpNorm_one (μ := Q)
    (B := fun n ρ => horizontalMollify (fun x => ψ (x - z) - ψ x)
      (heatSmoothed ((n + 1 : ℕ) : ℝ) (fun ω => D.g ω j)) ρ)
    (Y := horizontalMollify (fun x => ψ (x - z) - ψ x) (D.defect j)) (Z := fun _ => 0)
    (fun n => (measurable_horizontalMollify _ hχ.continuous.measurable
      (D.measurable_heatSmoothed_coord _ j)).aestronglyMeasurable)
    aestronglyMeasurable_const hφ hlim hL1
  filter_upwards [hzero, horizontalMollify_sub_kernel_ae hQ hψzm hψzi hψm hψi
    (D.measurable_defect j) (D.integrable_defect j)] with ρ h0 hsub
  rw [horizontalMollify_comp_translate]
  have h0' : horizontalMollify (fun x => ψ (x - z) - ψ x) (D.defect j) ρ = 0 := h0
  rw [hsub] at h0'
  exact sub_eq_zero.mp h0'

/-- The defect is almost surely invariant under every translation. -/
theorem defect_translate_ae [IsProbabilityMeasure Q] (hQ : IsStationary Q) (j : Fin d)
    (z : Vec d) : (fun ρ => D.defect j (translate z ρ)) =ᵐ[Q] D.defect j := by
  have hHm : Measurable (D.defect j) := D.measurable_defect j
  have hHi : Integrable (D.defect j) Q := D.integrable_defect j
  have hHzm : Measurable (fun ρ => D.defect j (translate z ρ)) :=
    hHm.comp (Probability.measurable_translate z)
  have hHzi : Integrable (fun ρ => D.defect j (translate z ρ)) Q :=
    (measurePreserving_translate Q hQ z).integrable_comp_of_integrable hHi
  let ε : ℕ → ℝ := fun n => ((n + 1 : ℕ) : ℝ)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hε : Tendsto ε atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n => Set.mem_Ioi.mpr (hεpos n)⟩
    simpa only [ε, Nat.cast_add, Nat.cast_one] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  haveI : Fact ((1 : ENNReal) ≤ 1) := ⟨le_rfl⟩
  have hT := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ 1
    ENNReal.one_ne_top hHm (memLp_one_iff_integrable.mpr hHi)).comp hε
  have hTz := (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ 1
    ENNReal.one_ne_top hHzm (memLp_one_iff_integrable.mpr hHzi)).comp hε
  have hTz' : Tendsto (fun n => eLpNorm (fun ω =>
      horizontalMollify (Calculus.unitMassScaledMollifier d (ε n)) (D.defect j) ω -
        D.defect j (translate z ω)) 1 Q) atTop (𝓝 0) := by
    refine hTz.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [D.horizontalMollify_defect_translate hQ
      (Entropy.contDiff_unitMassScaledMollifier (d := d) (ε n))
      (Entropy.hasCompactSupport_unitMassScaledMollifier (d := d) (hεpos n)) j z] with ω hω
    show horizontalMollify _ (fun ρ => D.defect j (translate z ρ)) ω - _ = _
    rw [hω]
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (horizontalMollify (Calculus.unitMassScaledMollifier d (ε n)) (D.defect j)) Q :=
    (measurable_horizontalMollify _
      (Entropy.contDiff_unitMassScaledMollifier (ε n)).continuous.measurable
      hHm).aestronglyMeasurable
  exact tendstoInMeasure_ae_unique
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hmeas hHzm.aestronglyMeasurable hTz')
    (tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero hmeas hHm.aestronglyMeasurable hT)

/-- The row-divergence identity `Σ_k F_{jkk} = g_j` of AKM Lemma 6.1, Step 4. -/
theorem sum_diag_ae_eq [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hErg : IsErgodicUnder translate Q) (j : Fin d) :
    (fun ω => ∑ k : Fin d, D.F ω j k k) =ᵐ[Q] fun ω => D.g ω j := by
  obtain ⟨c, hc⟩ := ae_eq_const_of_translate_invariant hErg (D.measurable_defect j)
    (D.defect_translate_ae hQ j)
  set ψ : Vec d → ℝ := Calculus.unitMassScaledMollifier d 1 with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := Entropy.contDiff_unitMassScaledMollifier 1
  have hψc : HasCompactSupport ψ := Entropy.hasCompactSupport_unitMassScaledMollifier one_pos
  have hmean := D.integral_horizontalMollify_defect hQ hψ hψc j
  have hconst : horizontalMollify ψ (D.defect j) =ᵐ[Q] fun _ => c := by
    filter_upwards [horizontalMollify_congr_ae hQ (D.measurable_defect j) measurable_const hc]
      with ρ hρ
    rw [hρ]
    simp only [horizontalMollify, integral_mul_const, hψdef,
      Entropy.integral_unitMassScaledMollifier' one_pos, one_mul]
  rw [integral_congr_ae hconst, integral_const, smul_eq_mul, probReal_univ,
    one_mul] at hmean
  filter_upwards [hc] with ω hω
  have h : D.defect j ω = 0 := by rw [hω, hmean]
  unfold defect at h
  linarith

end HeatSelectedDivergenceData

end EinsteinRelation.Correctors
