import EinsteinFull.Homogenization.SourceCorrectorLiouville
import EinsteinFull.Homogenization.HighContrastSlope
import HCPoly.Provider.Regularity.LiouvilleGradientUniqueness
import HCPoly.Analytic.ClosureH1a

/-!
# Source correctors are the high-contrast correctors of the dilated coefficient

Let `φ` be a source corrector of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Definitions 3.14–3.15, with slope `e`. For almost
every coefficient `a`, the dilated corrected affine function `x ↦ e·x + φ(2x)/2` lies in the
Liouville class of the dilated coefficient; by the Liouville classification of Armstrong, Kuusi
and Loher, *Homogenization at a polynomial scale in high contrast*, it is a corrected affine
function of slope `e'` up to a constant, and the slope identification forces `e' = e`. Hence the
dilated gradient of `φ` is the high-contrast corrector gradient of slope `e`.
-/

open MeasureTheory Filter Topology
open scoped Pointwise

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
  EinsteinRelation.External.AKM
open _root_.Homogenization hiding euclideanBall Vec Mat
open _root_.Homogenization.HighContrast

variable {d : ℕ}

theorem locallyIntegrable_dilatedGradient [NeZero d] {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g) (i : Fin d) :
    LocallyIntegrable (fun x => dilatedGradient g x i) volume := by
  have hg : LocallyIntegrable (fun x => g x i) volume := by
    have := (hw i).2.1
    rwa [locallyIntegrableOn_univ] at this
  rw [locallyIntegrable_iff]
  intro k hk
  have hk2 : IsCompact ((2 : ℝ) • k) := hk.smul (2 : ℝ)
  have hmem : MemLp (fun x => g x i) 1 (volume.restrict ((2 : ℝ) • k)) :=
    memLp_one_iff_integrable.mpr ((locallyIntegrable_iff.mp hg) _ hk2)
  exact memLp_one_iff_integrable.mp (MemLp.comp_smul_restrict two_ne_zero hk.measurableSet hmem)

theorem memLp_dilatedPotential_euclideanBall {u : Vec d → ℝ}
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R))) {r : ℝ} (hr : 0 < r) :
    MemLp (dilatedPotential u) 2 (volume.restrict (euclideanBall d r)) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * r) (by norm_num : (1 : ℝ) < 3)
  have hsub : euclideanBall d r ⊆ openCubeSet (originCube d (n : ℤ)) :=
    euclideanBall_subset_openCubeSet_originCube hr.le (by linarith)
  exact (memL2On_dilatedPotential hu n).mono_measure (Measure.restrict_mono hsub le_rfl)

theorem abs_vecDot_le_of_mem_openCubeSet (e : Vec d) {n : ℕ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d (n : ℤ))) :
    |vecDot e x| ≤ (∑ i, |e i|) * ((3 : ℝ) ^ n / 2) := by
  have hx' := mem_openCubeSet_originCube_iff.mp hx
  calc |vecDot e x| = |∑ i, e i * x i| := rfl
    _ ≤ ∑ i, |e i * x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |e i| * ((3 : ℝ) ^ n / 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hx' i).le (abs_nonneg _)
    _ = (∑ i, |e i|) * ((3 : ℝ) ^ n / 2) := by rw [Finset.sum_mul]

/-- The dilated corrected affine function of a source corrector is in the Liouville class of
the dilated coefficient. -/
theorem memLiouvilleClass_dilatedCorrectedAffine [NeZero d] {K : ℝ} (hK : 1 ≤ K)
    (a : Coefficient d K) (e : Vec d) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hw : HasWeakGradient Set.univ u g)
    (hloc : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
      MemLp g 2 (volume.restrict (ball 0 R)))
    (hharm : HasWeakDivergence Set.univ (fun x => (a x).mulVec (e + g x)) (fun _ => 0))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume) ^ 2 ∂volume)) atTop (𝓝 0))
    {ϑ : ℝ} (hϑ : 0 < ϑ) :
    MemLiouvilleClass (fun x => (toHighContrast hK a).1 x) ϑ (dilatedCorrectedAffine e u)
      (fun x => e + dilatedGradient g x) := by
  have hu2 : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) := fun R hR => (hloc R hR).1
  have hg2 : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)) := fun R hR => (hloc R hR).2
  have huae : AEStronglyMeasurable u volume := (locallyIntegrable_of_hasWeakGradient hw).aestronglyMeasurable
  have hmeas : IsMeasurableGradientPair volume (dilatedCorrectedAffine e u)
      (fun x => e + dilatedGradient g x) := by
    refine ⟨?_, fun i => ?_⟩
    · exact (contDiff_vecDot_left e).continuous.aestronglyMeasurable.add
        (locallyIntegrable_dilatedPotential hw).aestronglyMeasurable
    · simp only [Pi.add_apply]
      exact aestronglyMeasurable_const.add (locallyIntegrable_dilatedGradient hw i).aestronglyMeasurable
  have hL2 : ∀ n : ℕ, MemL2On (openCubeSet (originCube d (n : ℤ))) (dilatedCorrectedAffine e u) ∧
      GradMemL2On (openCubeSet (originCube d (n : ℤ))) (fun x => e + dilatedGradient g x) := by
    intro n
    have hU := isOpenBoundedConvexDomain_openCubeSet (originCube d (n : ℤ))
    have : IsFiniteMeasure (volume.restrict (openCubeSet (originCube d (n : ℤ)))) :=
      hU.isFiniteMeasure_restrict_volume
    constructor
    · have haff : MemLp (fun x : Vec d => vecDot e x) 2
          (volume.restrict (openCubeSet (originCube d (n : ℤ)))) := by
        refine MemLp.of_bound (contDiff_vecDot_left e).continuous.aestronglyMeasurable.restrict
          ((∑ i, |e i|) * ((3 : ℝ) ^ n / 2)) ?_
        refine (ae_restrict_iff' hU.isOpen.measurableSet).mpr (Filter.Eventually.of_forall
          fun x hx => ?_)
        rw [Real.norm_eq_abs]
        exact abs_vecDot_le_of_mem_openCubeSet e hx
      exact haff.add (memL2On_dilatedPotential hu2 n)
    · intro i
      have h := gradMemL2On_dilatedGradient hg2 n i
      exact (memLp_const (e i)).add h
  refine ⟨?_, ?_, ?_⟩
  · exact memH1sLoc_of_hasWeakGradientOn one_pos (ae_isEllipticMatrix_toHighContrast hK a) hmeas
      (hasWeakGradientOn_dilatedCorrectedAffine e hw) hL2
  · exact isWeakSolutionOn_dilated hK a e hharm
  · exact tendsto_growth_dilatedCorrectedAffine e hu2 huae
      (EinsteinRelation.Correctors.sublinear_uncentered_of_centered u hu2 hsub) hϑ

/-- The dilated potential of a sublinear function is sublinear for the normalized norms. -/
theorem tendsto_normalizedL2Norm_dilatedPotential {u : Vec d → ℝ}
    (hu2 : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hsub : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => r⁻¹ * (normalizedL2Norm (euclideanBall d r) (dilatedPotential u)).toReal)
      atTop (𝓝 0) := by
  obtain ⟨q, A, hq, hA, hdil⟩ := exists_normalizedL2Norm_dilate_le (d := d)
  let ε : ℝ → ℝ := fun R => R⁻¹ * Real.sqrt (⨍ x in ball 0 R, u x ^ 2)
  have hεq : Tendsto (fun r : ℝ => ε (q * r)) atTop (𝓝 0) :=
    hsub.comp (tendsto_id.const_mul_atTop hq)
  have hlim : Tendsto (fun r : ℝ => 2⁻¹ * A * q * ε (q * r)) atTop (𝓝 0) := by
    simpa using hεq.const_mul (2⁻¹ * A * q)
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    exact mul_nonneg (inv_nonneg.mpr hr.le) ENNReal.toReal_nonneg
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    have hqr : 0 < q * r := mul_pos hq hr
    have hε0 : 0 ≤ ε (q * r) := mul_nonneg (inv_nonneg.mpr hqr.le) (Real.sqrt_nonneg _)
    have hpot : normalizedL2Norm (euclideanBall d r) (dilatedPotential u) =
        ENNReal.ofReal |(2 : ℝ)⁻¹| *
          normalizedL2Norm (euclideanBall d r) (fun x => u ((2 : ℝ) • x)) :=
      normalizedL2Norm_const_mul _ _ _
    have hball := normalizedL2Norm_euclideanBall_eq_ofReal hqr (hu2 _ hqr)
    have hsqrt : Real.sqrt (⨍ x in ball 0 (q * r), u x ^ 2) = q * r * ε (q * r) := by
      simp only [ε]
      field_simp
    have hN : normalizedL2Norm (euclideanBall d r) (dilatedPotential u) ≤
        ENNReal.ofReal (2⁻¹ * A * (q * r * ε (q * r))) := by
      rw [hpot]
      calc ENNReal.ofReal |(2 : ℝ)⁻¹| *
            normalizedL2Norm (euclideanBall d r) (fun x => u ((2 : ℝ) • x))
          ≤ ENNReal.ofReal |(2 : ℝ)⁻¹| * (ENNReal.ofReal A *
              normalizedL2Norm (euclideanBall d (q * r)) u) := by
            gcongr
            exact hdil r hr u
        _ = ENNReal.ofReal (2⁻¹ * A * (q * r * ε (q * r))) := by
            rw [hball, hsqrt, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), ← mul_assoc,
              ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
    have hNreal : (normalizedL2Norm (euclideanBall d r) (dilatedPotential u)).toReal ≤
        2⁻¹ * A * (q * r * ε (q * r)) :=
      ENNReal.toReal_le_of_le_ofReal (by positivity) hN
    calc r⁻¹ * (normalizedL2Norm (euclideanBall d r) (dilatedPotential u)).toReal
        ≤ r⁻¹ * (2⁻¹ * A * (q * r * ε (q * r))) :=
          mul_le_mul_of_nonneg_left hNreal (inv_nonneg.mpr hr.le)
      _ = 2⁻¹ * A * q * ε (q * r) := by field_simp

theorem ae_mem_Ωend {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)} (hP : LawHypotheses P)
    {κ C : ℝ} (pk : HighContrastCorrectorPackage hK P κ C) :
    ∀ᵐ a ∂P, toHighContrast hK a ∈ pk.Ωend := by
  have hprob := isProbabilityMeasure_map_toHighContrast hK hP
  have hfull : (P.map (toHighContrast hK)) pk.Ωend = 1 := by
    have h := pk.full
    rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h
    exact h
  have hae : ∀ᵐ b ∂(P.map (toHighContrast hK)), b ∈ pk.Ωend := by
    rw [ae_iff]
    have hset : {b | ¬ b ∈ pk.Ωend} = pk.Ωendᶜ := rfl
    rw [hset, measure_compl pk.measurableSet_Ωend (measure_ne_top _ _), hfull, measure_univ,
      tsub_self]
  exact (ae_map_iff (measurable_toHighContrast hK).aemeasurable pk.measurableSet_Ωend).mp hae

/-- **Identification of source correctors.** For almost every coefficient, the dilated
corrected affine function of a source corrector of slope `e` is the high-contrast corrected
affine function of slope `e` of the dilated coefficient up to an additive constant, and the
dilated gradient of the corrector is the high-contrast corrector gradient. -/
theorem ae_dilated_eq_highContrast {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) {κ C : ℝ} (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C)
    (pk : HighContrastCorrectorPackage hK P κ C) {e : Vec d} (φ : SourceCorrector P e) :
    ∀ᵐ a ∂P, toHighContrast hK a ∈ pk.Ωend ∧
      (∃ c : ℝ, dilatedCorrectedAffine e (φ.potential a) =ᵐ[volume]
        fun x => vecDot e x + pk.Phi e (toHighContrast hK a) x + c) ∧
      dilatedGradient (φ.grad a) =ᵐ[volume] pk.gradPhi e (toHighContrast hK a) := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [ae_mem_Ωend hP pk, φ.weak_gradient, φ.locally_square_integrable, φ.harmonic,
    φ.sublinear] with a hb hw hloc hharm hsub
  set b := toHighContrast hK a
  have hϑ : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hv := memLiouvilleClass_dilatedCorrectedAffine hK a e hw hloc hharm hsub
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨e', c, hvw⟩ := pk.liouville b hb (1 / 2) hϑ _ _ hv
  have hw' := pk.liouville_mem b hb (1 / 2) hϑ e' c
  have hbE : IsAELocallyUniformlyElliptic (fun x => b.1 x) := b.2
  have hgrad := gradient_ae_eq_of_memH1sLoc_of_value_ae hbE hv.1 hw'.1 hvw
  have hloc' : ∀ i, LocallyIntegrable (fun x => pk.gradPhi e' b x i) volume := by
    intro i
    rw [locallyIntegrable_iff]
    intro k hk
    have h1 := integrableOn_grad_isCompact_of_memH1sLoc_class hbE hw'.1 hk i
    have h2 : IntegrableOn (fun _ : Vec d => e' i) k volume :=
      integrableOn_const hk.measure_lt_top.ne
    refine (h1.sub h2).congr_fun (fun x _ => ?_) hk.measurableSet
    simp
  have hu2 : ∀ R : ℝ, 0 < R → MemLp (φ.potential a) 2 (volume.restrict (ball 0 R)) :=
    fun R hR => (hloc R hR).1
  have hee : e = e' :=
    eq_slope_of_ae_eq_corrected (by omega) hκ hC pk hb (hasWeakGradientOn_dilated hw)
      (fun r hr => memLp_dilatedPotential_euclideanBall hu2 hr)
      (locallyIntegrable_dilatedGradient hw) hloc'
      (tendsto_normalizedL2Norm_dilatedPotential hu2
        (EinsteinRelation.Correctors.sublinear_uncentered_of_centered _ hu2 hsub)) hgrad
  rw [← hee] at hgrad hvw
  refine ⟨hb, ⟨c, hvw⟩, ?_⟩
  filter_upwards [hgrad] with x hx
  exact add_left_cancel hx

/-- **Identification of source correctors.** For almost every coefficient, the dilated
gradient of a source corrector of slope `e` is the high-contrast corrector gradient of slope
`e` of the dilated coefficient. -/
theorem ae_dilatedGradient_eq_gradPhi {K : ℝ} {hK : 1 ≤ K} {P : Measure (Coefficient d K)}
    (hP : LawHypotheses P) {κ C : ℝ} (hd : 2 ≤ d) (hκ : 0 < κ) (hC : 0 ≤ C)
    (pk : HighContrastCorrectorPackage hK P κ C) {e : Vec d} (φ : SourceCorrector P e) :
    ∀ᵐ a ∂P, toHighContrast hK a ∈ pk.Ωend ∧
      dilatedGradient (φ.grad a) =ᵐ[volume] pk.gradPhi e (toHighContrast hK a) :=
  (ae_dilated_eq_highContrast hP hd hκ hC pk φ).mono fun _ h => ⟨h.1, h.2.2⟩

end EinsteinFull.Homogenization
