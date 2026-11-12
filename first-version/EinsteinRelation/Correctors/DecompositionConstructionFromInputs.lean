import EinsteinRelation.Correctors.ScalarDecompositionAssembly
import EinsteinRelation.Correctors.HomogenizedCoordinates
import EinsteinRelation.Correctors.ScalarAveragingInputBounds
import EinsteinRelation.Correctors.LocalCorrectorUniformMoments
import EinsteinRelation.Correctors.AnisotropicCorrectedBandEquations
import EinsteinRelation.Correctors.AnisotropicCorrectedBandLocality
import EinsteinRelation.Correctors.AnisotropicBandMomentTriple
import EinsteinRelation.Correctors.UniformAnisotropicAverageMoments
import EinsteinRelation.Correctors.AnisotropicBandSources
import EinsteinRelation.Correctors.ScalarCorrectedBandMoments
import EinsteinRelation.Calculus.CoordinatePathAverageDivergence
import EinsteinRelation.Calculus.CoordinatePathAverageLocality
import EinsteinRelation.Correctors.CoordinatePathAverageEuclidean

/-! # Proposition 6.1 construction from the local corrector inputs

Source: `paper/main.tex:978–1090`. Every field is built from the actual
homogenized matrix, compact kernels, and the localized correctors.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- The complete construction in Proposition 6.1 from Lemma 5.1 and
Proposition 5.3 (`paper/main.tex:978–1090`). -/
theorem decompositionConstruction_of_inputs (H51 : CorrectorGradientMoments)
    (H53 : CorrectorLocalConstruction) : DecompositionConstruction := by
  intro d hd Λ₀ r₀ hΛ hr₀
  let L := Real.sqrt (sourceReducedBound Λ₀)
  have hLp : 0 < L := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound hΛ))
  obtain ⟨Ka, hKa, hKab⟩ := DriftH5.exists_ae_abs_entry_le d Λ₀ r₀
  let La := Ka + sourceReducedBound Λ₀
  have hLa : 0 ≤ La := add_nonneg hKa (lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound hΛ)).le
  obtain ⟨phi, Sig, F, Dphi, hstr, hgeom⟩ := H53 d hd Λ₀ r₀
  have hDphim Q r hr j : Measurable (Dphi Q r j) :=
    (hstr Q r hr j).1.2.2.2.mono
      ((reducedCoefficientObservationSigma_le_localSigma _).trans (Probability.localSigma_le_borel _)) le_rfl
  obtain ⟨CK, hCK, hKB⟩ := anisotropicBand_moment_triple hd hLp.le
  obtain ⟨Ce, hCe, hebound⟩ := eLpNorm_anisotropicAverage_uniform_le (d := d) hLp.le
  refine ⟨33 + 2 * L, by positivity, r₀, by linarith, fun l hl => ⟨2, by norm_num, fun p hp => ?_⟩⟩
  obtain ⟨A, hA, hAb⟩ := localCorrector_uniform_coordinate_bounds H51 hd Λ₀ r₀
    (show 2 ≤ 4 * p by linarith) phi Sig F Dphi hDphim (hgeom (4*p) (by linarith))
  intro M4p
  let M₀ := 1 + |M4p|
  have hM₀ : 0 < M₀ := by dsimp [M₀]; positivity
  let B₀ := CK * M₀
  have hB₀ : 0 ≤ B₀ := mul_nonneg hCK.le hM₀.le
  obtain ⟨A₁, B₁, hA₁, hB₁, hbandb⟩ := scalarCorrected_band_moments d La A B₀ hLa hA hB₀
  let D₀ := Real.sqrt d * (L * (2 * M₀))
  let F₀ := Ce * M₀
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hF₀ : 0 ≤ F₀ := mul_nonneg hCe.le hM₀.le
  refine ⟨8 * A₁ + 24 * B₁ + D₀ + F₀, by positivity, ?_⟩
  intro Q hQ M hM R hR hdyadic f hf
  obtain ⟨K, hRK⟩ := hdyadic
  obtain ⟨T, hBA, hT, hTi, hTe⟩ := exists_homogenized_coordinates Q
  obtain ⟨hfm, hf₂, hheat, hfb₄, hfb₂⟩ := scalarAveraging_input_bounds Q (by linarith) hR M hM f hf
  have hfL : Measurable[localSigma {x : Vec d | euclideanNorm x < 33 * R}] f := by
    simpa only [sub_zero] using hf.1
  let r : ℕ → ℝ := fun k => (2 : ℝ) ^ k
  have hr (k : ℕ) : 1 ≤ r k := one_le_pow₀ (by norm_num)
  have hrp (k : ℕ) : 0 < r k := lt_of_lt_of_le zero_lt_one (hr k)
  have hrR (k : ℕ) (hk : k ∈ Finset.range K) : r k ≤ R := by
    rw [hRK]
    exact pow_le_pow_right₀ (by norm_num) (Finset.mem_range.mp hk).le
  let u k := horizontalMollify (anisotropicBandKernel T (r k)) f
  let Du k := kernelGradient (anisotropicBandKernel T (r k)) f
  let H k j := fun ω => kernelHessian (anisotropicBandKernel T (r k)) f ω j
  let X k := fun ω => u k ω + ∑ j, phi Q (r k) j ω * Du k ω j
  let V k := fun ω => Du k ω + ∑ j, (Du k ω j • Dphi Q (r k) j ω + phi Q (r k) j ω • H k j ω)
  let W k := fun ω => (1/2 : ℝ) • ∑ j, (phi Q (r k) j ω • ((ω.1 0).mulVec (H k j ω)) -
    (Sig Q (r k) j ω).mulVec (H k j ω) + Du k ω j • F Q (r k) j ω)
  let i₀ : Fin d := ⟨0, by omega⟩
  let P k := fun ω => u k ω • (homogenizedMatrix Q).mulVec (unitVector i₀) +
    ∑ j, Du k ω j • (fun m => Sig Q (r k) j ω i₀ m)
  let h k := fun ω => ∑ j, (phi Q (r k) j ω *
    dot ((ω.1 0).mulVec (unitVector i₀)) (H k j ω) -
    (Sig Q (r k) j ω).mulVec (H k j ω) i₀ + Du k ω j * F Q (r k) j ω i₀)
  let b k := fun ω => horizontalMollify (anisotropicAverage T (r k)) f ω -
    horizontalMollify (anisotropicAverage T (2 * r k)) f ω
  let e := horizontalMollify (anisotropicAverage T R) f
  let E₀ := coordinatePathAverage (anisotropicAverage T 1) f
  let U := {x : Vec d | euclideanNorm x < (33 + 2 * L) * R}
  have hBorel := Probability.localSigma_le_borel U
  have hlocal (k : ℕ) (hk : k ∈ Finset.range K) :
      Measurable[localSigma U] (X k) ∧ Measurable[localSigma U] (V k) ∧
      Measurable[localSigma U] (W k) ∧ Measurable[localSigma U] (P k) ∧
      Measurable[localSigma U] (h k) := by
    letI : MeasurableSpace (FieldPair d) := localSigma U
    have hc j := (hstr Q (r k) (hr k) j).1
    have hl := anisotropicBand_corrected_locality hd T hLp (hrp k) (hrR k hk) hTi hfL
      (homogenizedMatrix Q) (⟨0, by omega⟩ : Fin d) (phi Q (r k)) (Dphi Q (r k))
      (F Q (r k)) (Sig Q (r k))
      (fun j => by simpa only [sub_zero] using (hc j).1.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl)
      (fun j => by simpa only [sub_zero] using (hc j).2.2.2.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl)
      (fun j => by simpa only [sub_zero] using (hc j).2.2.1.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl)
      (fun j => by simpa only [sub_zero] using (hc j).2.1.mono (reducedCoefficientObservationSigma_le_localSigma _) le_rfl)
    exact ⟨hl.1, hl.2.1, measurable_const.smul hl.2.2.1, hl.2.2.2.1, hl.2.2.2.2⟩
  have hmφ k j : Measurable (phi Q (r k) j) :=
    (hstr Q (r k) (hr k) j).1.1.mono
      ((reducedCoefficientObservationSigma_le_localSigma _).trans (Probability.localSigma_le_borel _)) le_rfl
  have hmSig k j : Measurable (Sig Q (r k) j) :=
    (hstr Q (r k) (hr k) j).1.2.1.mono
      ((reducedCoefficientObservationSigma_le_localSigma _).trans (Probability.localSigma_le_borel _)) le_rfl
  have hmF k j : Measurable (F Q (r k) j) :=
    (hstr Q (r k) (hr k) j).1.2.2.1.mono
      ((reducedCoefficientObservationSigma_le_localSigma _).trans (Probability.localSigma_le_borel _)) le_rfl
  have hum k : Measurable (u k) := measurable_horizontalMollify _
    (anisotropicBandKernel_contDiff hd T (hrp k)).continuous.measurable hfm
  have hDum k : Measurable (Du k) := measurable_pi_lambda _ fun j =>
    (measurable_horizontalMollify _ (KernelCalculus.contDiff_coordinateIterate
      (anisotropicBandKernel_contDiff hd T (hrp k)) [j]).continuous.measurable hfm).neg
  have hHm k j : Measurable (H k j) := measurable_pi_lambda _ fun i =>
    measurable_horizontalMollify _ (KernelCalculus.contDiff_coordinateIterate
      (anisotropicBandKernel_contDiff hd T (hrp k)) [i,j]).continuous.measurable hfm
  have hprim k := hAb Q (r k) (hr k)
  have hb₄ k hk := hKB T hTe (reducedEnvironmentLaw Q) hQ (ENNReal.ofReal (4*p))
    (ENNReal.one_le_ofReal.mpr (by linarith)) ENNReal.ofReal_ne_top M₀ (r k) R hM₀ (hrp k)
    (by linarith) (hrR k hk) f hfm hheat
  have hmb k hk := hbandb (reducedEnvironmentLaw Q) (by linarith : 1 ≤ p) (hr k)
    (fun ω => ω.1 0) (homogenizedMatrix Q) (⟨0, by omega⟩ : Fin d)
    (u k) (Du k) (phi Q (r k)) (Dphi Q (r k)) (H k) (F Q (r k)) (Sig Q (r k))
    ((continuous_eval_const (0 : Vec d)).comp continuous_fst).measurable (hum k) (hDum k)
    (hmφ k) (hDphim Q (r k) (hr k)) (hHm k) (hmF k) (hmSig k)
    ((hKab Q).mono fun ω hω i j => (hω i j).trans (by dsimp [La]; linarith [one_le_sourceReducedBound hΛ]))
    (fun i j => (abs_homogenizedMatrix_entry_le Q i j).trans (by dsimp [La]; linarith))
    (hb₄ k hk).1 (hb₄ k hk).2.1 (hb₄ k hk).2.2
    (fun j => (hprim k j).1.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (correctorAmplitude_log_weight (d := d) (hr k)).2.2 hA)))
    (fun j i => (hprim k j).2.2.2 i) (fun j i => (hprim k j).2.2.1 i)
    (fun j i m => ((hprim k j).2.1 i m).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (correctorAmplitude_log_weight (d := d) (hr k)).2.2 hA)))
    ((hlocal k hk).2.1.mono hBorel le_rfl) ((hlocal k hk).2.2.1.mono hBorel le_rfl)
    ((hlocal k hk).2.2.2.1.mono hBorel le_rfl)
  have hm2 {g : FieldPair d → ℝ} {C : ℝ} (hg : Measurable g)
      (hb : eLpNorm g (ENNReal.ofReal (4*p)) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C) :
      MemLp g 2 (reducedEnvironmentLaw Q) :=
    (show MemLp g (ENNReal.ofReal (4*p)) _ from
      ⟨hg.aestronglyMeasurable, hb.trans_lt ENNReal.ofReal_lt_top⟩).mono_exponent
        (by exact_mod_cast ENNReal.ofReal_le_ofReal (show (2:ℝ) ≤ 4*p by linarith))
  have heq (k : ℕ) (_hk : k ∈ Finset.range K) := anisotropicBand_corrected_equations hQ hd (homogenizedMatrix Q) T hBA (hrp k) hfm hf₂
    (phi Q (r k)) (Dphi Q (r k)) (F Q (r k)) (Sig Q (r k))
    (fun j => (hstr Q (r k) (hr k) j).2.2.1) (hmφ k) (hDphim Q (r k) (hr k))
    (fun j => (hstr Q (r k) (hr k) j).2.1)
    (fun j i => (hstr Q (r k) (hr k) j).2.2.2 i)
    (fun j => hm2 (hmφ k j) (hprim k j).1)
    (fun j i => hm2 ((measurable_pi_apply i).comp (hDphim Q (r k) (hr k) j)) ((hprim k j).2.2.2 i))
    (fun j i m => hm2 (((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem i m).measurable.comp (hmSig k j)) ((hprim k j).2.1 i m))
    (fun j i => hm2 ((measurable_pi_apply i).comp (hmF k j)) ((hprim k j).2.2.1 i))
    ⟨Ka, hKab Q⟩
    ((ae_reducedEnvironmentLaw_origin_elliptic Q).mono fun ω hω => (hω 0).1)
    (homogenizedMatrix_transpose Q) (⟨0, by omega⟩ : Fin d)
  have heL := measurable_localSigma_anisotropicAverage_common T hLp (by linarith : 0<R) hTi hfL
  have hE₀L := measurable_localSigma_anisotropicPathAverage T hLp (by linarith : 1≤R) hTi hfL
  have hfU : Measurable[localSigma U] f := hfL.mono
    (Probability.localSigma_mono (fun x hx => by change euclideanNorm x < (33+2*L)*R; change euclideanNorm x < 33*R at hx; nlinarith [mul_pos hLp (by linarith : 0<R)])) le_rfl
  have hsmall := hasWeakHorizontalDivergence_coordinatePathAverage (K := anisotropicAverage T 1) hQ hLp.le
    (anisotropicAverage_contDiff T (by norm_num)).continuous.measurable
    ((anisotropicAverage_contDiff T (by norm_num)).continuous.integrable_of_hasCompactSupport
      (anisotropicAverage_hasCompactSupport T (by norm_num)))
    (anisotropicAverage_nonneg T (by norm_num)) (integral_anisotropicAverage T (by norm_num))
    (fun z hz => anisotropicAverage_tail T hLp (by norm_num) hTi (by simpa using hz)) hfm hf₂
  have hsmall' : HasWeakHorizontalDivergence (reducedEnvironmentLaw Q) hQ E₀
      (fun ω => f ω - e ω - ∑ k ∈ Finset.range K, b k ω) := by
    apply Entropy.HasWeakHorizontalDivergence.congr_div hsmall
    filter_upwards with ω
    dsimp only [b,e,r]
    rw [sum_anisotropicBand_sources, ← hRK]
    ring
  have hE₀b := eLpNorm_coordinatePathAverage_euclidean_le (K := anisotropicAverage T 1) hQ (by linarith : 2 ≤ 2*p)
    hLp.le (show 0 ≤ 2 * M₀ by positivity) (anisotropicAverage_contDiff T (by norm_num)).continuous.measurable
    ((anisotropicAverage_contDiff T (by norm_num)).continuous.integrable_of_hasCompactSupport
      (anisotropicAverage_hasCompactSupport T (by norm_num)))
    (anisotropicAverage_nonneg T (by norm_num)) (integral_anisotropicAverage T (by norm_num))
    (fun z hz => anisotropicAverage_tail T hLp (by norm_num) hTi (by simpa using hz)) hfm hfb₂
  have heb₄ := hebound T hTe (reducedEnvironmentLaw Q) hQ (ENNReal.ofReal (4*p))
    (ENNReal.one_le_ofReal.mpr (by linarith)) ENNReal.ofReal_ne_top M₀ R hM₀ (by linarith) f hfm hheat
  have heb₂ := (eLpNorm_le_eLpNorm_of_exponent_le
    (ENNReal.ofReal_le_ofReal (show 2*p ≤ 4*p by linarith))
    (heL.mono hBorel le_rfl).aestronglyMeasurable).trans heb₄
  apply scalarDecompositionData_of_bands hd hQ (by linarith) hA₁ hB₁ hD₀ hF₀ K hRK
    ⟨Ka, hKab Q⟩ X h b V W P f e E₀
    (fun k hk => by simpa only [sub_zero] using (hlocal k hk).1)
    (fun k hk => by simpa only [sub_zero] using (hlocal k hk).2.2.2.2)
    (fun k hk => by simpa only [sub_zero] using (hlocal k hk).2.1)
    (fun k hk => by simpa only [sub_zero] using (hlocal k hk).2.2.1)
    (fun k hk => by simpa only [sub_zero] using (hlocal k hk).2.2.2.1)
    (by simpa only [sub_zero] using hfU) (by simpa only [sub_zero] using heL)
    (by simpa only [sub_zero] using hE₀L)
    (fun k hk => (heq k hk).1) (fun k hk => (heq k hk).2) hsmall'
    (fun k hk => (hmb k hk).1) (fun k hk => (hmb k hk).2.1) (fun k hk => (hmb k hk).2.2.1)
    (fun k hk => (hmb k hk).2.2.2.1) (fun k hk => (hmb k hk).2.2.2.2) hE₀b
  simpa only [div_eq_mul_inv] using heb₂

/-- Proposition 6.1, including the response estimate, from the local corrector
inputs and the three entropy/occupation statements (`paper/main.tex:978–1100`). -/
theorem scalarDecompositionTwin_of_inputs (H51 : CorrectorGradientMoments)
    (H53 : CorrectorLocalConstruction) (H41 : FisherBoundStatement)
    (H43 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.ResolventStatement d hd Λ₀ r₀)
    (H32 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      EinsteinRelation.Entropy.OccupationStatement d hd Λ₀ r₀) : ScalarDecompositionTwin :=
  scalarDecompositionTwin_of_construction H41 H43 H32
    (decompositionConstruction_of_inputs H51 H53)

end EinsteinRelation.Correctors
