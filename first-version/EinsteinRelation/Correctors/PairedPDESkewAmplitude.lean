import EinsteinRelation.Correctors.PairedPDEPlanarEstimate
import EinsteinRelation.Correctors.PairedPDEBallNormalization
import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import EinsteinRelation.Correctors.PairedPDEAmplitudeMoments

/-! # Centered planar skew amplitudes from the ordinary paired energy

Source: `paper/main.tex:877–883`. The actual rotated flux is the weak
gradient of the independent skew entry. The dual harmonic equation and
ellipticity allow the same centered-amplitude estimate as for the scalar
corrector, with energy measured using the ordinary paired gradient.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- The skew gradient's normalized energy is dominated by the ordinary
paired gradient's normalized energy. Source: `paper/main.tex:880–883`. -/
theorem planar_rotated_flux_vectorRms_le {U : Set (Vec 2)} (hU : IsOpen U)
    {L : ℝ} (hL : 0 < L) {a : Vec 2 → Mat 2} (ha : IsElliptic L a)
    {σ : Vec 2 → ℝ} {H G : Vec 2 → Vec 2}
    (hσ : HasWeakGradient U σ H)
    (hH : Set.EqOn H (fun x => planarRotation.mulVec ((a x).mulVec (G x))) U)
    (hG : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U)) :
    vectorRms volume U H ≤ L * vectorRms volume U G := by
  have he := planar_rotated_flux_energy_le hU hL ha hσ hH hG
  have hmean : (⨍ x in U, euclideanSq (H x)) ≤ L^2 * ⨍ x in U, euclideanSq (G x) := by
    simp only [average_eq, smul_eq_mul]
    have h := mul_le_mul_of_nonneg_left he
      (inv_nonneg.mpr (show 0 ≤ ((volume.restrict U) Set.univ).toReal from ENNReal.toReal_nonneg))
    simpa only [mul_left_comm] using h
  change Real.sqrt _ ≤ L * Real.sqrt _
  calc
    _ ≤ Real.sqrt (L^2 * ⨍ x in U, euclideanSq (G x)) := Real.sqrt_le_sqrt hmean
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL.le]

/-- The GT centered-value estimate applies to the planar skew entry with
the ordinary paired energy on its right. All representatives and equations
are concrete; dual coefficient measurability is explicit.
Source: `paper/main.tex:877–883`. -/
theorem planar_skew_centered_amplitude_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ (a : Vec 2 → Mat 2) (σ : Vec 2 → ℝ) (H G : Vec 2 → Vec 2),
        IsElliptic L a →
        (∀ i j, Measurable (fun x =>
          (planarRotation * (a x)⁻¹ * planarRotation.transpose) i j)) →
        HasWeakGradient (ball 0 (2*R)) σ H →
        Set.EqOn H (fun x => planarRotation.mulVec ((a x).mulVec (G x))) (ball 0 (2*R)) →
        HasWeakDivergence (ball 0 (2*R))
          (fun x => (planarRotation * (a x)⁻¹ * planarRotation.transpose).mulVec (H x))
          (fun _ => 0) →
        MemLp σ 2 (volume.restrict (ball 0 (2*R))) →
        MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict (ball 0 (2*R))) →
        ContinuousOn σ (ball 0 R) →
        ∀ (w : Vec 2 → ℝ), Integrable w volume →
          Integrable (fun x => w x * σ x) volume →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 → Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R,
            |σ x₀ - ∫ x, w x * σ x| ≤ C*R * vectorRms volume (ball 0 (2*R)) G := by
  obtain ⟨C, hC, hbound⟩ := paired_harmonic_centered_amplitude_planar_of_gt h817 hP
    (inv_pos.mpr hL) (by positivity : 0 < ((2 : ℝ)+1)*L)
  refine ⟨C*L, mul_pos hC hL, ?_⟩
  intro R hR a σ H G ha ham hσ hH hdiv hσ2 hG hcont w hw hwσ hw0 hw1 hws x₀ hx₀
  have hU := paired_isOpen_ball (0 : Vec 2) (2*R)
  have hHn := planar_rotated_flux_memLp hU hL ha hσ hH hG
  have hHm : AEStronglyMeasurable H (volume.restrict (ball 0 (2*R))) :=
    (aemeasurable_pi_lambda _ fun j => (hσ j).2.1.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
  have hHv : MemLp H 2 (volume.restrict (ball 0 (2*R))) := by
    apply hHn.of_le hHm
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm (H x) from Real.sqrt_nonneg _)]
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun j => ?_
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    change (H x j)^2 ≤ ∑ k : Fin 2, H x k * H x k
    rw [sq]
    exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
  have hdual := isElliptic_planar_dual hL ha
  have hell := ellipticBound_of_isElliptic hL hdual ham (ball 0 (2*R))
  have hb := hbound R hR _ σ H hell ⟨hσ2, hHv, hσ, hdiv⟩ hcont
    w hw hwσ hw0 hw1 hws x₀ hx₀
  calc
    _ ≤ C*R * vectorRms volume (ball 0 (2*R)) H := hb
    _ ≤ C*R * (L * vectorRms volume (ball 0 (2*R)) G) :=
      mul_le_mul_of_nonneg_left (planar_rotated_flux_vectorRms_le hU hL ha hσ hH hG)
        (mul_nonneg hC.le hR.le)
    _ = _ := by ring

/-- The centered skew entry has every probability moment controlled by
`C R` times the ordinary paired-gradient energy moment. The coefficients,
weak equations and continuous representative are the actual samplewise
ones. Source: `paper/main.tex:877–883`. -/
theorem planar_skew_centered_amplitude_moments_of_gt
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        (a : Ω → Vec 2 → Mat 2) (σ : Ω → Vec 2 → ℝ)
        (H G : Ω → Vec 2 → Vec 2),
        Measurable (fun z : Ω × Vec 2 => σ z.1 z.2) →
        (∀ᵐ ω ∂P, IsElliptic L (a ω) ∧
          (∀ i j, Measurable (fun x =>
            (planarRotation * (a ω x)⁻¹ * planarRotation.transpose) i j)) ∧
          HasWeakGradient (ball 0 (2*R)) (σ ω) (H ω) ∧
          Set.EqOn (H ω) (fun x =>
            planarRotation.mulVec ((a ω x).mulVec (G ω x))) (ball 0 (2*R)) ∧
          HasWeakDivergence (ball 0 (2*R))
            (fun x => (planarRotation * (a ω x)⁻¹ * planarRotation.transpose).mulVec (H ω x))
            (fun _ => 0) ∧
          MemLp (σ ω) 2 (volume.restrict (ball 0 (2*R))) ∧
          MemLp (fun x => euclideanNorm (G ω x)) 2 (volume.restrict (ball 0 (2*R))) ∧
          ContinuousOn (σ ω) (ball 0 R)) →
        ∀ (w : Vec 2 → ℝ), Measurable w → Integrable w volume →
          (∀ᵐ ω ∂P, Integrable (fun x => w x * σ ω x) volume) →
          (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 → Function.support w ⊆ ball 0 R →
          ∀ x₀ ∈ ball 0 R, ∀ p : ℝ≥0∞,
            MemLp (fun ω => vectorRms volume (ball 0 (2*R)) (G ω)) p P →
            MemLp (fun ω => σ ω x₀ - ∫ x, w x * σ ω x) p P ∧
              eLpNorm (fun ω => σ ω x₀ - ∫ x, w x * σ ω x) p P ≤
                ENNReal.ofReal (C*R) *
                  eLpNorm (fun ω => vectorRms volume (ball 0 (2*R)) (G ω)) p P := by
  obtain ⟨C, hC, hbound⟩ := planar_skew_centered_amplitude_of_gt h817 hP hL
  refine ⟨C, hC, ?_⟩
  intro R hR Ω _ P a σ H G hσm hdata w hwm hwi hwσi hw0 hw1 hws x₀ hx₀ p hGp
  have hdom : ∀ᵐ ω ∂P, ‖σ ω x₀ - ∫ x, w x * σ ω x‖ ≤
      (C*R) * ‖vectorRms volume (ball 0 (2*R)) (G ω)‖ := by
    filter_upwards [hdata, hwσi] with ω hω hwiσ
    rcases hω with ⟨ha, ham, hσ, hH, hdiv, hσ2, hG, hcont⟩
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ vectorRms volume (ball 0 (2*R)) (G ω)
        from Real.sqrt_nonneg _)] using
      hbound R hR (a ω) (σ ω) (H ω) (G ω) ha ham hσ hH hdiv hσ2 hG hcont
        w hwi hwiσ hw0 hw1 hws x₀ hx₀
  exact ⟨hGp.of_le_mul (measurable_centered_spatial_value σ hσm hwm x₀).aestronglyMeasurable
      hdom, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hdom p⟩

end EinsteinRelation.Correctors
