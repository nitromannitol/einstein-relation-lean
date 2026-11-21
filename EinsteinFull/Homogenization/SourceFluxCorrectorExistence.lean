import EinsteinFull.Homogenization.HeatFormulaMeasurability
import EinsteinFull.Homogenization.HighContrastFluxPairing
import EinsteinFull.External.Source.AKMSourceFluxCorrector

/-!
# Existence of the flux corrector of a source corrector

Let `φ` be a source corrector of a unit slope `e` for a law of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*. Its centered flux
`a(e + ∇φ) - E[∫_□ a(e + ∇φ)]` has, almost surely, components that are locally square
integrable with square integrals on balls `B_R`, `R ≥ X`, of order `R^d`, hence Gaussian moments,
and whose heat Hessians decay at large times, by the pairing bounds for the fluxes. The heat
formula (6.7) therefore selects a flux gradient and a potential, which depend measurably on the
coefficient field: this is the flux corrector `SourceFluxCorrector φ` of Lemma 6.1.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM

variable {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)} {e : Vec d}

/-- The measurable representative of the centered source flux of (6.7). -/
noncomputable def representativeFlux (φ : SourceCorrector P e) (a : Coefficient d K)
    (y : Vec d) : Vec d :=
  (coefficientRepresentative a y).mulVec (e + φ.grad a y) - sourceMeanFlux φ

theorem representativeFlux_ae_eq (φ : SourceCorrector P e) (a : Coefficient d K) :
    representativeFlux φ a =ᵐ[volume] sourceCenteredFlux φ a := by
  filter_upwards [coefficientRepresentative_ae_eq a] with y hy
  simp only [representativeFlux, sourceCenteredFlux, hy]

theorem measurable_representativeFlux (φ : SourceCorrector P e) (k : Fin d) :
    Measurable (fun p : Coefficient d K × Vec d => representativeFlux φ p.1 p.2 k) := by
  have hg (j : Fin d) : Measurable (fun p : Coefficient d K × Vec d => φ.grad p.1 p.2 j) :=
    (measurable_pi_apply j).comp φ.measurable_grad
  have hfun : (fun p : Coefficient d K × Vec d => representativeFlux φ p.1 p.2 k) =
      fun p => (∑ j, coefficientRepresentative p.1 p.2 k j * (e j + φ.grad p.1 p.2 j)) -
        sourceMeanFlux φ k := rfl
  rw [hfun]
  exact (Finset.measurable_sum _ fun j _ =>
    (measurable_coefficientRepresentative_apply k j).mul (measurable_const.add (hg j))).sub_const _

/-- The square integrals of the components of the source flux on large balls grow like the
volume. -/
theorem lintegral_sourceFlux_sq_le (hK : 1 ≤ K) (a : Coefficient d K) {g : Vec d → Vec d}
    (hgm : Measurable g) (hmem : ∀ R : ℝ, 0 < R → MemLp g 2 (volume.restrict (ball 0 R)))
    {R₀ C : ℝ} (hR₀ : 0 < R₀)
    (hg : ∀ r : ℝ, R₀ ≤ r → Real.sqrt (⨍ x in ball 0 r, euclideanSq (g x)) ≤ C)
    (e c : Vec d) (k : Fin d) (R : ℝ) (hR : R₀ ≤ R) :
    ∫⁻ y in ball 0 R, ‖((coefficientRepresentative a y).mulVec (e + g y)) k - c k‖ₑ ^ 2 ≤
      ENNReal.ofReal (3 * (K ^ 2 * euclideanSq e + K ^ 2 * C ^ 2 + c k ^ 2) *
        (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal * R ^ d) := by
  have hR0 : 0 < R := lt_of_lt_of_le hR₀ hR
  set f : Vec d → ℝ := fun y => ((coefficientRepresentative a y).mulVec (e + g y)) k - c k
    with hf
  have hfm := memLp_sourceFlux hK a hgm hmem e c k R
  have hfin := isFiniteMeasure_restrict_ball (d := d) R
  have hint : Integrable (fun y => f y ^ 2) (volume.restrict (ball 0 R)) := hfm.integrable_sq
  have hlin : ∫⁻ y in ball 0 R, ‖f y‖ₑ ^ 2 = ENNReal.ofReal (∫ y in ball 0 R, f y ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun y => sq_nonneg _)]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [hlin]
  refine ENNReal.ofReal_le_ofReal ?_
  have hgj : ∀ j, MemLp (fun x => g x j) 2 (volume.restrict (ball 0 R)) :=
    memLp_pi_iff.mp (hmem R hR0)
  have hsqint : Integrable (fun x => euclideanSq (g x)) (volume.restrict (ball 0 R)) := by
    unfold euclideanSq dot
    exact integrable_finsetSum _ fun j _ => by
      simpa [sq] using (hgj j).integrable_sq
  have hK0 : 0 ≤ K := by linarith
  have hbound : ∀ᵐ y ∂(volume.restrict (ball (0 : Vec d) R)), f y ^ 2 ≤
      3 * (K ^ 2 * euclideanSq e + c k ^ 2) + 3 * K ^ 2 * euclideanSq (g y) := by
    filter_upwards [ae_restrict_of_ae (coefficientRepresentative_ae_eq a)] with y hy
    have hy' : coefficientRepresentative a y = a.field y := hy
    have h1 : |f y| ≤ K * euclideanNorm e + K * euclideanNorm (g y) + |c k| := by
      simp only [hf, hy']
      have h2 := abs_mulVec_apply_le hK a y (e + g y) k
      have h3 := TimeChange.euclideanNorm_add_le e (g y)
      have h4 := abs_sub ((a.field y).mulVec (e + g y) k) (c k)
      nlinarith
    have he2 := euclideanSq_eq_euclideanNorm_sq e
    have hg2 := euclideanSq_eq_euclideanNorm_sq (g y)
    have hfa : f y ^ 2 ≤ (K * euclideanNorm e + K * euclideanNorm (g y) + |c k|) ^ 2 := by
      rw [← sq_abs (f y)]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    have hck : |c k| ^ 2 = c k ^ 2 := sq_abs _
    rw [he2, hg2]
    nlinarith [sq_nonneg (K * euclideanNorm e - K * euclideanNorm (g y)),
      sq_nonneg (K * euclideanNorm e - |c k|), sq_nonneg (K * euclideanNorm (g y) - |c k|)]
  have hmono : ∫ y in ball 0 R, f y ^ 2 ≤ ∫ y in ball 0 R,
      (3 * (K ^ 2 * euclideanSq e + c k ^ 2) + 3 * K ^ 2 * euclideanSq (g y)) :=
    integral_mono_ae hint ((integrable_const (3 * (K ^ 2 * euclideanSq e + c k ^ 2))).add
      (hsqint.const_mul (3 * K ^ 2))) hbound
  have havg := hg R hR
  have hvol := volume_real_ball (d := d) hR0
  have hvol0 : 0 < volume.real (ball (0 : Vec d) R) := by
    rw [hvol]
    exact mul_pos (pow_pos hR0 d) (ENNReal.toReal_pos (volume_euclideanBall_pos' one_pos).ne'
      (volume_euclideanBall_ne_top' 1))
  have hI0 : 0 ≤ ∫ x in ball 0 R, euclideanSq (g x) :=
    integral_nonneg fun x => _root_.Homogenization.vecNormSq_nonneg (g x)
  have hsq : ∫ x in ball 0 R, euclideanSq (g x) ≤ C ^ 2 * volume.real (ball (0 : Vec d) R) := by
    have hC0 : 0 ≤ C := (Real.sqrt_nonneg _).trans havg
    have h1 : ⨍ x in ball 0 R, euclideanSq (g x) ≤ C ^ 2 := by
      have h2 := (Real.sqrt_le_left hC0).mp havg
      exact h2
    rw [setAverage_eq, smul_eq_mul, inv_mul_le_iff₀ hvol0] at h1
    linarith
  have hmr : (volume.restrict (ball (0 : Vec d) R)).real univ = volume.real (ball (0 : Vec d) R) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ]
  have hcomp : ∫ y in ball 0 R,
      (3 * (K ^ 2 * euclideanSq e + c k ^ 2) + 3 * K ^ 2 * euclideanSq (g y)) =
      volume.real (ball (0 : Vec d) R) * (3 * (K ^ 2 * euclideanSq e + c k ^ 2)) +
        3 * K ^ 2 * ∫ x in ball 0 R, euclideanSq (g x) := by
    rw [integral_add (integrable_const _) (hsqint.const_mul _), integral_const, smul_eq_mul, hmr,
      integral_const_mul]
  rw [hcomp] at hmono
  calc ∫ y in ball 0 R, f y ^ 2
      ≤ volume.real (ball (0 : Vec d) R) * (3 * (K ^ 2 * euclideanSq e + c k ^ 2)) +
          3 * K ^ 2 * ∫ x in ball 0 R, euclideanSq (g x) := hmono
    _ ≤ volume.real (ball (0 : Vec d) R) * (3 * (K ^ 2 * euclideanSq e + c k ^ 2)) +
          3 * K ^ 2 * (C ^ 2 * volume.real (ball (0 : Vec d) R)) := by gcongr
    _ = _ := by
        rw [hvol]
        ring

/-- **The heat formula applies to the source flux almost surely.** -/
theorem ae_heatFormulaHypotheses_representativeFlux (hd : 2 ≤ d) (hK : 1 < K)
    (hP : LawHypotheses P) (he : euclideanNorm e = 1) (φ : SourceCorrector P e) :
    ∀ᵐ a ∂P, HeatFormulaHypotheses (representativeFlux φ a) := by
  have hK1 : 1 ≤ K := hK.le
  obtain ⟨β, C, hβ, hC, hbounds⟩ := exists_sourceCorrector_bounds d hd K hK
  obtain ⟨Cs, hCs, hX⟩ := hbounds 1 one_pos (by exact_mod_cast (show 1 < d by omega))
  obtain ⟨X, hXm, -, hX1, hXbd⟩ := hX P hP
  obtain ⟨κ, hκ, hpair⟩ := exists_hasScalePairingBound_sourceFlux d hd K hK
  filter_upwards [hXbd e he φ, hpair P hP e φ, φ.locally_square_integrable] with a hga hpa hloc
  have hgm : Measurable (φ.grad a) :=
    Measurable.of_uncurry_left (f := fun a y => φ.grad a y) φ.measurable_grad
  have hmem : ∀ R : ℝ, 0 < R → MemLp (φ.grad a) 2 (volume.restrict (ball 0 R)) :=
    fun R hR => (hloc R hR).2
  have hX0 : 0 < X a := lt_of_lt_of_le one_pos (hX1 a)
  have hgrow : ∀ r : ℝ, X a ≤ r → Real.sqrt (⨍ x in ball 0 r, euclideanSq (φ.grad a x)) ≤ C :=
    fun r hr => (hga r hr).2
  have hmom : ∀ (c : Vec d) (k : Fin d), HasGaussianMoments
      (fun y => ((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k - c k) := by
    intro c k
    refine hasGaussianMoments_of_growth (measurable_sourceFlux a hgm e c k)
      (M := 3 * (K ^ 2 * euclideanSq e + K ^ 2 * C ^ 2 + c k ^ 2) *
        (volume (_root_.Homogenization.HighContrast.euclideanBall d 1)).toReal) ?_ hX0
      (fun R hR => lintegral_sourceFlux_sq_le hK1 a hgm hmem hX0 hgrow e c k R hR)
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg (add_nonneg
      (mul_nonneg (sq_nonneg K) (_root_.Homogenization.vecNormSq_nonneg e))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))) (sq_nonneg _))) ENNReal.toReal_nonneg
  obtain ⟨R₀, c, hR₀, hA⟩ := hpa
  refine ⟨fun k => Measurable.of_uncurry_left (f := fun a y => representativeFlux φ a y k)
      (measurable_representativeFlux φ k),
    fun k R => memLp_sourceFlux hK1 a hgm hmem e (sourceMeanFlux φ) k R,
    fun k => hmom (sourceMeanFlux φ) k, fun k i j => ?_⟩
  obtain ⟨A, hA0, hAk⟩ := hA k
  have hdec := hAk.hasHeatHessianDecay hR₀ hA0 hκ (measurable_sourceFlux a hgm e c k)
    (hmom c k) i j
  have h2 := hdec.add_const (hmom c k) (measurable_sourceFlux a hgm e c k)
    (c k - sourceMeanFlux φ k)
  have hfun : (fun y => representativeFlux φ a y k) = fun y =>
      (((coefficientRepresentative a y).mulVec (e + φ.grad a y)) k - c k) +
        (c k - sourceMeanFlux φ k) := by
    funext y
    simp only [representativeFlux, Pi.sub_apply]
    ring
  rw [hfun]
  exact h2

/-- **Existence of the flux corrector** (Armstrong, Kuusi and Mourrat, Lemma 6.1): for every unit
slope and every source corrector, the heat formula (6.7) selects a flux corrector. -/
theorem nonempty_sourceFluxCorrector (hd : 2 ≤ d) (hK : 1 < K) (hP : LawHypotheses P)
    (he : euclideanNorm e = 1) (φ : SourceCorrector P e) :
    Nonempty (SourceFluxCorrector φ) := by
  have hgood := ae_heatFormulaHypotheses_representativeFlux hd hK hP he φ
  refine ⟨{
    potential := fun a x => heatSelectedPotential (representativeFlux φ a) x
    grad := fun a j k x => heatSelectedGradient (representativeFlux φ a) j k x
    measurable_potential := ?_
    measurable_grad := ?_
    weak_gradient := ?_
    locally_square_integrable := ?_
    heat_selected := ?_ }⟩
  · exact measurable_heatSelectedPotential_param (G := representativeFlux φ)
      (measurable_representativeFlux φ)
  · exact fun j k => measurable_heatSelectedGradient_param (G := representativeFlux φ)
      (measurable_representativeFlux φ) j k
  · filter_upwards [hgood] with a hg
    exact fun j k => hg.hasWeakGradient_heatSelectedPotential hd j k
  · filter_upwards [hgood] with a hg
    exact fun R _ j k => ⟨hg.memLp_heatSelectedPotential hd j k R,
      memLp_pi_iff.mpr fun l => hg.memLp_heatSelectedGradient j k l R⟩
  · filter_upwards [hgood] with a hg
    exact isHeatSelectedFluxGradient_congr_ae (representativeFlux_ae_eq φ a)
      hg.isHeatSelectedFluxGradient

end EinsteinFull.Homogenization
