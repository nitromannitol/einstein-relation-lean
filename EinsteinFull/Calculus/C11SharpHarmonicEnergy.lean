import EinsteinFull.Work.W8.SharpnessConstructionSupport
import EinsteinFull.Calculus.S4GammaSupport
import EinsteinFull.Calculus.S4SharpDetSupport
import EinsteinFull.Calculus.C11SharpHarmonicReduction
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Diffusion.Velocity
import Mathlib.MeasureTheory.Function.L2Space
import EinsteinRelation.Probability.SlutskyMetric
import EinsteinRelation.Probability.SlutskyMetrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

/-! The exact spatial energy of the constructed sharp harmonic coordinate. -/

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Sharpness

/-- The carré du champ of the actual sharp harmonic coordinate, at every signed force. -/
theorem sharp_harmonic_carre_du_champ_eq {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (lam : ℝ) (x : Vec d) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let ω := EinsteinFull.Work.W8.physicalPair i W
    let H := fun y : Vec d => y i + ψ y
    reducedGenerator i ω lam (fun y => (H y)^2) x -
      2 * H x * reducedGenerator i ω lam H x = 1 + gradient ψ x i := by
  dsimp only
  let ψ := EinsteinFull.Work.W8.corrector W
  let ω := EinsteinFull.Work.W8.physicalPair i W
  let H := fun y : Vec d => y i + ψ y
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := EinsteinFull.Work.W8.corrector_contDiff W
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := (contDiff_apply ℝ ℝ i).add hψ
  have hs := EinsteinFull.Work.W8.physicalPair_isSmooth i W
  change reducedGenerator i ω lam (fun y => (H y)^2) x -
    2 * H x * reducedGenerator i ω lam H x = 1 + gradient ψ x i
  rw [reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top (hH.pow 2)),
    reducedGenerator_eq_svGenerator hs i lam (contDiff_two_of_top hH),
    svGenerator_sq_sub _ _ (contDiff_two_of_top hH) x]
  have hgrad : gradient H x = unitVector i + gradient ψ x := by
    funext k
    have hc : DifferentiableAt ℝ (fun z : Vec d => z i) x := differentiableAt_apply i x
    have hp := hψ.differentiable (by simp) x
    change (fderiv ℝ (fun z : Vec d => z i + ψ z) x) (unitVector k) =
      unitVector i k + (fderiv ℝ ψ x) (unitVector k)
    rw [fderiv_fun_add hc hp, add_apply, (hasFDerivAt_apply i x).fderiv]
    simp only [ContinuousLinearMap.proj_apply]
    congr 1
    simp only [unitVector, Pi.single_apply, eq_comm]
  have hflux : (reducedCoefficient ω x).mulVec (gradient H x) = unitVector i := by
    rw [hgrad]
    exact EinsteinFull.Work.W8.physicalPair_harmonic i W x
  calc
    (∑ j, ∑ k, reducedCoefficient ω x j k *
        (fderiv ℝ H x (unitVector j) * fderiv ℝ H x (unitVector k))) =
        ∑ j, gradient H x j * ((reducedCoefficient ω x).mulVec (gradient H x)) j := by
      simp only [gradient, coordinateDerivative, Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ j, gradient H x j * unitVector i j := by rw [hflux]
    _ = gradient H x i := by simp [unitVector, Pi.single_apply]
    _ = 1 + gradient ψ x i := by rw [hgrad]; simp [unitVector]

/-- The actual sharp harmonic coordinate has annealed energy one at every signed force. -/
theorem sharp_harmonic_carre_du_champ_mean {d : ℕ} (hd : 2 ≤ d)
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) :
    ∫ W, (let i : Fin d := ⟨0, by omega⟩
      let ψ := EinsteinFull.Work.W8.corrector W
      let ω := EinsteinFull.Work.W8.physicalPair i W
      let H := fun y : Vec d => y i + ψ y
      reducedGenerator i ω lam (fun y => (H y)^2) 0 -
        2 * H 0 * reducedGenerator i ω lam H 0) ∂P = 1 := by
  let : IsProbabilityMeasure P := hP.1
  let i : Fin d := ⟨0, by omega⟩
  have hmeas : Measurable (fun W : NoiseSample d =>
      gradient (EinsteinFull.Work.W8.corrector W) 0 i) := by
    have hm := ((measurable_pi_apply i).comp (measurable_sharpLocalGradient hd)).comp
      (EinsteinFull.Work.W8.measurable_physicalPair i)
    simpa only [Function.comp_def, i, sharpLocalGradient_physicalPair hd] using hm
  have hint : Integrable (fun W : NoiseSample d =>
      gradient (EinsteinFull.Work.W8.corrector W) 0 i) P := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (1 / 4) ?_
    exact Eventually.of_forall fun W => by
      rw [Real.norm_eq_abs]
      exact abs_coord_le_of_euclideanNorm_le i
        (EinsteinFull.Work.W8.corrector_gradient_bound W 0)
  have hmean : (∫ W, gradient (EinsteinFull.Work.W8.corrector W) 0 i ∂P) = 0 :=
    (sharpPositive_environment hd hP Q hQ).1
  calc
    _ = ∫ W, 1 + gradient (EinsteinFull.Work.W8.corrector W) 0 i ∂P := by
      apply integral_congr_ae
      exact Eventually.of_forall fun W => sharp_harmonic_carre_du_champ_eq i W lam 0
    _ = 1 := by rw [integral_add (integrable_const (1 : ℝ)) hint, hmean]; simp

/-- Uniform spatial energy bounds for the actual sharp harmonic coordinate at every signed force. -/
theorem sharp_harmonic_carre_du_champ_bounds {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (lam : ℝ) (x : Vec d) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let ω := EinsteinFull.Work.W8.physicalPair i W
    let H := fun y : Vec d => y i + ψ y
    let Γ := reducedGenerator i ω lam (fun y => (H y)^2) x -
      2 * H x * reducedGenerator i ω lam H x
    (3 : ℝ) / 4 ≤ Γ ∧ Γ ≤ (5 : ℝ) / 4 := by
  dsimp only
  rw [sharp_harmonic_carre_du_champ_eq i W lam x]
  obtain ⟨hlower, hupper⟩ := abs_le.mp (abs_coord_le_of_euclideanNorm_le i
    (EinsteinFull.Work.W8.corrector_gradient_bound W x))
  constructor
  · linarith only [hlower]
  · linarith only [hupper]

/-- A bounded sharp corrector changes the normalized coordinate second moment by an
explicit vanishing error on any supplied probability law with the stated moment bound. -/
theorem sharp_harmonic_coordinate_second_moment_error {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (t : ℝ≥0) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (hcoord : MemLp (fun γ : Path d => γ t i - γ 0 i) 2 P)
    (hsecond : (∫ γ, (γ t i - γ 0 i)^2 ∂P) ≤ B*(t : ℝ)) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let H := fun x : Vec d => x i + ψ x
    |(∫ γ, (H (γ t)-H (γ 0))^2 ∂P)/(t : ℝ) -
      (∫ γ, (γ t i-γ 0 i)^2 ∂P)/(t : ℝ)| ≤
      4*EinsteinFull.Work.W8.seedScale d*Real.sqrt (B/(t : ℝ)) +
      4*(EinsteinFull.Work.W8.seedScale d)^2/(t : ℝ) := by
  dsimp only
  let s := EinsteinFull.Work.W8.seedScale d
  let a := fun γ : Path d => γ t i - γ 0 i
  let e := fun γ : Path d => EinsteinFull.Work.W8.corrector W (γ t) -
    EinsteinFull.Work.W8.corrector W (γ 0)
  have hs : 0 ≤ s := (EinsteinFull.Work.W8.seedScale_pos d).le
  have htR : 0 < (t : ℝ) := ht
  have he_bound (γ : Path d) : |e γ| ≤ 2*s := by
    exact (abs_sub _ _).trans (by
      have h₁ := EinsteinFull.Work.W8.corrector_abs_le W (γ t)
      have h₀ := EinsteinFull.Work.W8.corrector_abs_le W (γ 0)
      dsimp only [s]
      linarith only [h₁, h₀])
  have he_meas : Measurable e := by
    exact ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
      (measurable_pathPosition t)).sub
      ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
        (measurable_pathPosition 0))
  have he : MemLp e 2 P := MemLp.of_bound he_meas.aestronglyMeasurable (2*s)
    (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using he_bound γ)
  have ha : MemLp a 2 P := hcoord
  have ha_abs : Integrable (fun γ => |a γ|) P := (ha.integrable (by norm_num)).abs
  let m := ∫ γ, |a γ| ∂P
  have hm : 0 ≤ m := integral_nonneg fun γ => abs_nonneg (a γ)
  have hm_sq : m^2 ≤ ∫ γ, (a γ)^2 ∂P := by
    have hid : (∫ γ, (|a γ| - m)^2 ∂P) = (∫ γ, (a γ)^2 ∂P) - m^2 := by
      calc
        _ = ∫ γ, (a γ)^2 - 2*m*|a γ| + m^2 ∂P := by
          apply integral_congr_ae
          exact Eventually.of_forall fun γ => by nlinarith only [sq_abs (a γ)]
        _ = _ := by
          have hsub : Integrable (fun γ => (a γ)^2 - 2*m*|a γ|) P :=
            ha.integrable_sq.sub (ha_abs.const_mul (2*m))
          rw [integral_add hsub (integrable_const (m^2)),
            integral_sub ha.integrable_sq (ha_abs.const_mul (2*m)), integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          change (∫ γ, (a γ)^2 ∂P) - 2*m*m + m^2 = _
          ring
    have hnonneg : 0 ≤ ∫ γ, (|a γ| - m)^2 ∂P :=
      integral_nonneg (fun γ => sq_nonneg (|a γ| - m))
    rw [hid] at hnonneg
    linarith only [hnonneg]
  have hm_bound : m ≤ (t : ℝ) * Real.sqrt (B/(t : ℝ)) := by
    have hroot : ((t : ℝ) * Real.sqrt (B/(t : ℝ)))^2 = B*(t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hB htR.le)]
      field_simp [ne_of_gt htR]
    exact (sq_le_sq₀ hm (mul_nonneg htR.le (Real.sqrt_nonneg _))).mp
      (hm_sq.trans (hsecond.trans_eq hroot.symm))
  have hdiff_int : Integrable (fun γ => (a γ + e γ)^2 - (a γ)^2) P :=
    (ha.add he).integrable_sq.sub ha.integrable_sq
  have hpoint (γ : Path d) : |(a γ + e γ)^2 - (a γ)^2| ≤
      4*s*|a γ| + 4*s^2 := by
    calc
      _ = |2*a γ*e γ + (e γ)^2| := by congr 1; ring
      _ ≤ |2*a γ*e γ| + |(e γ)^2| := abs_add_le _ _
      _ = 2*|a γ| * |e γ| + |e γ|^2 := by rw [abs_mul, abs_mul, abs_pow]; norm_num
      _ ≤ 2*|a γ| *(2*s) + (2*s)^2 := by
        gcongr
        · exact he_bound γ
        · exact he_bound γ
      _ = _ := by ring
  have hdiff : |(∫ γ, (a γ + e γ)^2 ∂P) - (∫ γ, (a γ)^2 ∂P)| ≤
      4*s*m + 4*s^2 := by
    have hsum_sq : Integrable (fun γ => (a γ + e γ)^2) P :=
      (ha.add he).integrable_sq
    rw [← integral_sub hsum_sq ha.integrable_sq]
    calc
      _ ≤ ∫ γ, |(a γ + e γ)^2 - (a γ)^2| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ γ, 4*s*|a γ| + 4*s^2 ∂P :=
        integral_mono hdiff_int.abs ((ha_abs.const_mul (4*s)).add (integrable_const _)) hpoint
      _ = _ := by
        rw [integral_add (ha_abs.const_mul (4*s)) (integrable_const _), integral_const_mul]
        simp only [integral_const, probReal_univ, one_smul, m]
  have hH (γ : Path d) :
      (γ t i + EinsteinFull.Work.W8.corrector W (γ t)) -
        (γ 0 i + EinsteinFull.Work.W8.corrector W (γ 0)) = a γ + e γ := by
    dsimp only [a, e]
    ring
  simp_rw [hH]
  change |(∫ γ, (a γ + e γ)^2 ∂P)/(t : ℝ) -
    (∫ γ, (a γ)^2 ∂P)/(t : ℝ)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos htR]
  calc
    _ ≤ (4*s*m + 4*s^2)/(t : ℝ) := div_le_div_of_nonneg_right hdiff htR.le
    _ ≤ (4*s*((t : ℝ)*Real.sqrt (B/(t : ℝ))) + 4*s^2)/(t : ℝ) := by
      apply div_le_div_of_nonneg_right _ htR.le
      have hmul : 4*s*m ≤ 4*s*((t : ℝ)*Real.sqrt (B/(t : ℝ))) :=
        mul_le_mul_of_nonneg_left hm_bound (mul_nonneg (by norm_num) hs)
      exact add_le_add hmul le_rfl
    _ = _ := by
      change _ = 4*s*Real.sqrt (B/(t : ℝ)) + 4*s^2/(t : ℝ)
      field_simp [ne_of_gt htR]

/-- A bounded sharp corrector changes a normalized cross moment by an explicit
vanishing error, retaining both actual coordinate increments. -/
theorem sharp_harmonic_coordinate_cross_moment_error {d : ℕ} (i j : Fin d)
    (W : NoiseSample d) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (t : ℝ≥0) (ht : 0 < t) (B : ℝ) (hB : 0 ≤ B)
    (hi : MemLp (fun γ : Path d => γ t i-γ 0 i) 2 P)
    (hj : MemLp (fun γ : Path d => γ t j-γ 0 j) 2 P)
    (hsecond : (∫ γ, (γ t j-γ 0 j)^2 ∂P) ≤ B*(t : ℝ)) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let H := fun x : Vec d => x i+ψ x
    |(∫ γ, (H (γ t)-H (γ 0))*(γ t j-γ 0 j) ∂P)/(t : ℝ)-
      (∫ γ, (γ t i-γ 0 i)*(γ t j-γ 0 j) ∂P)/(t : ℝ)| ≤
      2*EinsteinFull.Work.W8.seedScale d*Real.sqrt (B/(t : ℝ)) := by
  dsimp only
  let s := EinsteinFull.Work.W8.seedScale d
  let a := fun γ : Path d => γ t i - γ 0 i
  let b := fun γ : Path d => γ t j - γ 0 j
  let e := fun γ : Path d => EinsteinFull.Work.W8.corrector W (γ t) -
    EinsteinFull.Work.W8.corrector W (γ 0)
  have hs : 0 ≤ s := (EinsteinFull.Work.W8.seedScale_pos d).le
  have htR : 0 < (t : ℝ) := ht
  have he_bound (γ : Path d) : |e γ| ≤ 2*s := by
    exact (abs_sub _ _).trans (by
      have h₁ := EinsteinFull.Work.W8.corrector_abs_le W (γ t)
      have h₀ := EinsteinFull.Work.W8.corrector_abs_le W (γ 0)
      dsimp only [s]
      linarith only [h₁, h₀])
  have he_meas : Measurable e := by
    exact ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
      (measurable_pathPosition t)).sub
      ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
        (measurable_pathPosition 0))
  have he : MemLp e 2 P := MemLp.of_bound he_meas.aestronglyMeasurable (2*s)
    (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using he_bound γ)
  have ha : MemLp a 2 P := hi
  have hb : MemLp b 2 P := hj
  have hb_abs : Integrable (fun γ => |b γ|) P := (hb.integrable (by norm_num)).abs
  let m := ∫ γ, |b γ| ∂P
  have hm : 0 ≤ m := integral_nonneg fun γ => abs_nonneg (b γ)
  have hm_sq : m^2 ≤ ∫ γ, (b γ)^2 ∂P := by
    have hid : (∫ γ, (|b γ| - m)^2 ∂P) = (∫ γ, (b γ)^2 ∂P) - m^2 := by
      calc
        _ = ∫ γ, (b γ)^2 - 2*m*|b γ| + m^2 ∂P := by
          apply integral_congr_ae
          exact Eventually.of_forall fun γ => by nlinarith only [sq_abs (b γ)]
        _ = _ := by
          have hsub : Integrable (fun γ => (b γ)^2 - 2*m*|b γ|) P :=
            hb.integrable_sq.sub (hb_abs.const_mul (2*m))
          rw [integral_add hsub (integrable_const (m^2)),
            integral_sub hb.integrable_sq (hb_abs.const_mul (2*m)), integral_const_mul]
          simp only [integral_const, probReal_univ, one_smul]
          change (∫ γ, (b γ)^2 ∂P) - 2*m*m + m^2 = _
          ring
    have hnonneg : 0 ≤ ∫ γ, (|b γ| - m)^2 ∂P :=
      integral_nonneg (fun γ => sq_nonneg (|b γ| - m))
    rw [hid] at hnonneg
    linarith only [hnonneg]
  have hm_bound : m ≤ (t : ℝ) * Real.sqrt (B/(t : ℝ)) := by
    have hroot : ((t : ℝ) * Real.sqrt (B/(t : ℝ)))^2 = B*(t : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (div_nonneg hB htR.le)]
      field_simp [ne_of_gt htR]
    exact (sq_le_sq₀ hm (mul_nonneg htR.le (Real.sqrt_nonneg _))).mp
      (hm_sq.trans (hsecond.trans_eq hroot.symm))
  have hdiff : |(∫ γ, (a γ + e γ)*b γ ∂P) - (∫ γ, a γ*b γ ∂P)| ≤
      2*s*m := by
    have hsum : Integrable (fun γ => (a γ + e γ)*b γ) P :=
      (ha.add he).integrable_mul hb
    have hab : Integrable (fun γ => a γ*b γ) P := ha.integrable_mul hb
    rw [← integral_sub hsum hab]
    calc
      _ = |∫ γ, e γ*b γ ∂P| := by
        congr 1
        apply integral_congr_ae
        exact Eventually.of_forall fun γ => by ring
      _ ≤ ∫ γ, |e γ*b γ| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ γ, 2*s*|b γ| ∂P := by
        apply integral_mono (he.integrable_mul hb).abs (hb_abs.const_mul (2*s))
        intro γ
        change |e γ * b γ| ≤ 2*s*|b γ|
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (he_bound γ) (abs_nonneg _)
      _ = 2*s*m := integral_const_mul _ _
  have hH (γ : Path d) :
      (γ t i + EinsteinFull.Work.W8.corrector W (γ t)) -
        (γ 0 i + EinsteinFull.Work.W8.corrector W (γ 0)) = a γ + e γ := by
    dsimp only [a, e]
    ring
  simp_rw [hH]
  change |(∫ γ, (a γ + e γ)*b γ ∂P)/(t : ℝ) -
    (∫ γ, a γ*b γ ∂P)/(t : ℝ)| ≤ _
  rw [← sub_div, abs_div, abs_of_pos htR]
  calc
    _ ≤ (2*s*m)/(t : ℝ) := div_le_div_of_nonneg_right hdiff htR.le
    _ ≤ (2*s*((t : ℝ)*Real.sqrt (B/(t : ℝ))))/(t : ℝ) := by
      apply div_le_div_of_nonneg_right _ htR.le
      exact mul_le_mul_of_nonneg_left hm_bound (mul_nonneg (by norm_num) hs)
    _ = _ := by
      change _ = 2*s*Real.sqrt (B/(t : ℝ))
      field_simp [ne_of_gt htR]


/-- The bounded corrector preserves a supplied asymptotic coordinate second moment. -/
theorem sharp_harmonic_second_moment_limit_transfer {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (B a : ℝ) (hB : 0 ≤ B)
    (hcoord : ∀ t : ℝ≥0, MemLp (fun γ : Path d => γ t i-γ 0 i) 2 P)
    (hsecond : ∀ t : ℝ≥0, 0 < t →
      (∫ γ, (γ t i-γ 0 i)^2 ∂P) ≤ B*(t : ℝ))
    (hlimit : Tendsto (fun t : ℝ≥0 =>
      (∫ γ, (γ t i-γ 0 i)^2 ∂P)/(t : ℝ)) atTop (𝓝 a)) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let H := fun x : Vec d => x i+ψ x
    Tendsto (fun t : ℝ≥0 =>
      (∫ γ, (H (γ t)-H (γ 0))^2 ∂P)/(t : ℝ)) atTop (𝓝 a) := by
  dsimp only
  have htime : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hinv : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htime
  have hroot : Tendsto (fun t : ℝ≥0 => Real.sqrt (B / (t : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ≥0 => B * (t : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hinv :
        Tendsto (fun t : ℝ≥0 => B * (t : ℝ)⁻¹) atTop (𝓝 (B * 0)))
    simpa only [div_eq_mul_inv, Real.sqrt_zero] using h.sqrt
  have herr : Tendsto (fun t : ℝ≥0 =>
      4*EinsteinFull.Work.W8.seedScale d*Real.sqrt (B/(t : ℝ)) +
      4*(EinsteinFull.Work.W8.seedScale d)^2/(t : ℝ)) atTop (𝓝 0) := by
    have h₁ := hroot.const_mul (4 * EinsteinFull.Work.W8.seedScale d)
    have h₂ := hinv.const_mul (4 * (EinsteinFull.Work.W8.seedScale d)^2)
    simpa only [div_eq_mul_inv, mul_zero, add_zero] using h₁.add h₂
  apply hlimit.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ herr
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ≥0)] with t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact sharp_harmonic_coordinate_second_moment_error i W P t ht B hB
    (hcoord t) (hsecond t ht)

/-- The bounded corrector preserves a supplied asymptotic coordinate cross moment. -/
theorem sharp_harmonic_cross_moment_limit_transfer {d : ℕ} (i j : Fin d)
    (W : NoiseSample d) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (B a : ℝ) (hB : 0 ≤ B)
    (hi : ∀ t : ℝ≥0, MemLp (fun γ : Path d => γ t i-γ 0 i) 2 P)
    (hj : ∀ t : ℝ≥0, MemLp (fun γ : Path d => γ t j-γ 0 j) 2 P)
    (hsecond : ∀ t : ℝ≥0, 0 < t →
      (∫ γ, (γ t j-γ 0 j)^2 ∂P) ≤ B*(t : ℝ))
    (hlimit : Tendsto (fun t : ℝ≥0 =>
      (∫ γ, (γ t i-γ 0 i)*(γ t j-γ 0 j) ∂P)/(t : ℝ)) atTop (𝓝 a)) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let H := fun x : Vec d => x i+ψ x
    Tendsto (fun t : ℝ≥0 =>
      (∫ γ, (H (γ t)-H (γ 0))*(γ t j-γ 0 j) ∂P)/(t : ℝ)) atTop (𝓝 a) := by
  dsimp only
  have htime : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hinv : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp htime
  have hroot : Tendsto (fun t : ℝ≥0 => Real.sqrt (B / (t : ℝ))) atTop (𝓝 0) := by
    have h : Tendsto (fun t : ℝ≥0 => B * (t : ℝ)⁻¹) atTop (𝓝 0) := by
      simpa only [mul_zero] using (tendsto_const_nhds.mul hinv :
        Tendsto (fun t : ℝ≥0 => B * (t : ℝ)⁻¹) atTop (𝓝 (B * 0)))
    simpa only [div_eq_mul_inv, Real.sqrt_zero] using h.sqrt
  have herr : Tendsto (fun t : ℝ≥0 =>
      2*EinsteinFull.Work.W8.seedScale d*Real.sqrt (B/(t : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hroot.const_mul (2 * EinsteinFull.Work.W8.seedScale d)
  apply hlimit.congr_dist
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _ herr
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ≥0)] with t ht
  rw [Real.dist_eq, abs_sub_comm]
  exact sharp_harmonic_coordinate_cross_moment_error i j W P t ht B hB
    (hi t) (hj t) (hsecond t ht)

/-- Correcting both coordinates changes their normalized cross moment by a
bound that vanishes with time. -/
theorem sharp_corrected_coordinate_cross_moment_error {d : ℕ} (i j : Fin d)
    (W : NoiseSample d) (P : Measure (Path d)) [IsProbabilityMeasure P]
    (t : ℝ≥0) (ht : 0 < t) (Bi Bj : ℝ) (hBi : 0 ≤ Bi) (hBj : 0 ≤ Bj)
    (hi : MemLp (fun γ : Path d => γ t i-γ 0 i) 2 P)
    (hj : MemLp (fun γ : Path d => γ t j-γ 0 j) 2 P)
    (hsi : (∫ γ, (γ t i-γ 0 i)^2 ∂P) ≤ Bi*(t : ℝ))
    (hsj : (∫ γ, (γ t j-γ 0 j)^2 ∂P) ≤ Bj*(t : ℝ)) :
    let ψ := EinsteinFull.Work.W8.corrector W
    let H := fun x : Vec d => x i+ψ x
    let J := fun x : Vec d => x j+ψ x
    |(∫ γ, (H (γ t)-H (γ 0))*(J (γ t)-J (γ 0)) ∂P)/(t : ℝ)-
      (∫ γ, (γ t i-γ 0 i)*(γ t j-γ 0 j) ∂P)/(t : ℝ)| ≤
      2*EinsteinFull.Work.W8.seedScale d*(Real.sqrt (Bi/(t : ℝ))+Real.sqrt (Bj/(t : ℝ)))+
      4*(EinsteinFull.Work.W8.seedScale d)^2/(t : ℝ) := by
  dsimp only
  let s := EinsteinFull.Work.W8.seedScale d
  let a := fun γ : Path d => γ t i - γ 0 i
  let b := fun γ : Path d => γ t j - γ 0 j
  let e := fun γ : Path d => EinsteinFull.Work.W8.corrector W (γ t) -
    EinsteinFull.Work.W8.corrector W (γ 0)
  have htR : 0 < (t : ℝ) := ht
  have he_bound (γ : Path d) : |e γ| ≤ 2*s := by
    exact (abs_sub _ _).trans (by
      have h₁ := EinsteinFull.Work.W8.corrector_abs_le W (γ t)
      have h₀ := EinsteinFull.Work.W8.corrector_abs_le W (γ 0)
      dsimp only [s]
      linarith only [h₁, h₀])
  have he_meas : Measurable e := by
    exact ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
      (measurable_pathPosition t)).sub
      ((EinsteinFull.Work.W8.corrector_contDiff W).continuous.measurable.comp
        (measurable_pathPosition 0))
  have he : MemLp e 2 P := MemLp.of_bound he_meas.aestronglyMeasurable (2*s)
    (Eventually.of_forall fun γ => by simpa only [Real.norm_eq_abs] using he_bound γ)
  have ha : MemLp a 2 P := hi
  have hb : MemLp b 2 P := hj
  have he2 : (∫ γ, (e γ)^2 ∂P) ≤ 4*s^2 := by
    calc
      _ ≤ ∫ _ : Path d, 4*s^2 ∂P := by
        apply integral_mono he.integrable_sq (integrable_const _)
        intro γ
        have h := he_bound γ
        have hs : 0 ≤ 2*s := mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le
        have hsq := (sq_le_sq₀ (abs_nonneg (e γ)) hs).2 h
        nlinarith only [hsq, sq_abs (e γ)]
      _ = _ := by simp
  have h₁ := sharp_harmonic_coordinate_cross_moment_error i j W P t ht Bj hBj hi hj hsj
  have h₂ := sharp_harmonic_coordinate_cross_moment_error j i W P t ht Bi hBi hj hi hsi
  dsimp only at h₁ h₂
  have hid₁ : (∫ γ, ((γ t i + EinsteinFull.Work.W8.corrector W (γ t)) -
      (γ 0 i + EinsteinFull.Work.W8.corrector W (γ 0))) * (γ t j - γ 0 j) ∂P) =
      (∫ γ, a γ*b γ ∂P) + ∫ γ, e γ*b γ ∂P := by
    rw [← integral_add (f := fun γ => a γ*b γ) (g := fun γ => e γ*b γ) (ha.integrable_mul hb) (he.integrable_mul hb)]
    apply integral_congr_ae
    exact Eventually.of_forall fun γ => by dsimp [a, b, e]; ring
  have hid₂ : (∫ γ, ((γ t j + EinsteinFull.Work.W8.corrector W (γ t)) -
      (γ 0 j + EinsteinFull.Work.W8.corrector W (γ 0))) * (γ t i - γ 0 i) ∂P) =
      (∫ γ, a γ*b γ ∂P) + ∫ γ, a γ*e γ ∂P := by
    rw [← integral_add (f := fun γ => a γ*b γ) (g := fun γ => a γ*e γ) (ha.integrable_mul hb) (ha.integrable_mul he)]
    apply integral_congr_ae
    exact Eventually.of_forall fun γ => by dsimp [a, b, e]; ring
  have hab_comm : (∫ γ, (γ t j - γ 0 j)*(γ t i - γ 0 i) ∂P) =
      ∫ γ, a γ*b γ ∂P := by
    apply integral_congr_ae
    exact Eventually.of_forall fun γ => by dsimp [a, b]; ring
  rw [hid₁] at h₁
  change |((∫ γ, a γ*b γ ∂P) + ∫ γ, e γ*b γ ∂P)/(t : ℝ) -
    (∫ γ, a γ*b γ ∂P)/(t : ℝ)| ≤ _ at h₁
  rw [hid₂, hab_comm] at h₂
  have hlin₁ : |(∫ γ, e γ*b γ ∂P)/(t : ℝ)| ≤ 2*s*Real.sqrt (Bj/(t : ℝ)) := by
    convert h₁ using 1 <;> simp only [add_div] <;> ring
  have hlin₂ : |(∫ γ, a γ*e γ ∂P)/(t : ℝ)| ≤ 2*s*Real.sqrt (Bi/(t : ℝ)) := by
    convert h₂ using 1 <;> simp only [add_div] <;> ring
  have htotal : (∫ γ, ((γ t i + EinsteinFull.Work.W8.corrector W (γ t)) -
      (γ 0 i + EinsteinFull.Work.W8.corrector W (γ 0))) *
      ((γ t j + EinsteinFull.Work.W8.corrector W (γ t)) -
      (γ 0 j + EinsteinFull.Work.W8.corrector W (γ 0))) ∂P) =
      ((∫ γ, a γ*b γ ∂P) + ∫ γ, e γ*b γ ∂P) +
      (∫ γ, a γ*e γ ∂P) + ∫ γ, (e γ)^2 ∂P := by
    rw [← integral_add (f := fun γ => a γ*b γ) (g := fun γ => e γ*b γ) (ha.integrable_mul hb) (he.integrable_mul hb),
      ← integral_add (f := fun γ => a γ*b γ + e γ*b γ) (g := fun γ => a γ*e γ) ((ha.integrable_mul hb).add (he.integrable_mul hb)) (ha.integrable_mul he),
      ← integral_add (f := fun γ => (a γ*b γ + e γ*b γ) + a γ*e γ) (g := fun γ => (e γ)^2) (((ha.integrable_mul hb).add (he.integrable_mul hb)).add
      (ha.integrable_mul he)) he.integrable_sq]
    apply integral_congr_ae
    exact Eventually.of_forall fun γ => by dsimp [a, b, e]; ring
  rw [htotal]
  have he2nonneg : 0 ≤ ∫ γ, (e γ)^2 ∂P := integral_nonneg fun γ => sq_nonneg _
  have he2div : |(∫ γ, (e γ)^2 ∂P)/(t : ℝ)| ≤ 4*s^2/(t : ℝ) := by
    rw [abs_of_nonneg (div_nonneg he2nonneg htR.le)]
    exact div_le_div_of_nonneg_right he2 htR.le
  calc
    _ = |(∫ γ, e γ*b γ ∂P)/(t : ℝ) + (∫ γ, a γ*e γ ∂P)/(t : ℝ) +
        (∫ γ, (e γ)^2 ∂P)/(t : ℝ)| := by congr 1; simp only [add_div]; ring
    _ ≤ |(∫ γ, e γ*b γ ∂P)/(t : ℝ)| + |(∫ γ, a γ*e γ ∂P)/(t : ℝ)| +
        |(∫ γ, (e γ)^2 ∂P)/(t : ℝ)| := (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by dsimp only [s] at *; nlinarith only [hlin₁, hlin₂, he2div]

/-- A bounded actual corrector does not change a distributional scaling limit. -/
theorem sharp_bounded_corrector_preserves_distribution_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X U V : ℕ → Ω → Vec d) (hU : ∀ n, Measurable (U n))
    (hV : ∀ n, Measurable (V n)) (Z : Ω → Vec d)
    (hXZ : TendstoInDistribution X atTop Z (fun _ => μ) μ) :
    TendstoInDistribution
      (fun n ω => X n ω + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)) • unitVector i))
      atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  have hbound (n : ℕ) (ω : Ω) :
      dist (X n ω + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)) • unitVector i)) (X n ω) ≤
          C / ρ n := by
    have hc : |EinsteinFull.Work.W8.corrector W (V n ω) -
        EinsteinFull.Work.W8.corrector W (U n ω)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h : |EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)| ≤
          |EinsteinFull.Work.W8.corrector W (V n ω)| +
          |EinsteinFull.Work.W8.corrector W (U n ω)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          (abs_add_le (EinsteinFull.Work.W8.corrector W (V n ω))
            (-EinsteinFull.Work.W8.corrector W (U n ω)))
      linarith [EinsteinFull.Work.W8.corrector_abs_le W (V n ω),
        EinsteinFull.Work.W8.corrector_abs_le W (U n ω)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  refine EinsteinRelation.tendstoInDistribution_of_dist_tendsto_zero _ Z hXZ ?_ ?_
  · intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | ε ≤ dist (X n ω + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)) • unitVector i)) (X n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_le_of_lt (hbound n ω) hn)
    rw [this]
    exact measureReal_empty
  · intro n
    have hc : Continuous (EinsteinFull.Work.W8.corrector W) :=
      (EinsteinFull.Work.W8.corrector_contDiff W).continuous
    have hm : Measurable (fun ω => EinsteinFull.Work.W8.corrector W (V n ω) -
        EinsteinFull.Work.W8.corrector W (U n ω)) :=
      (hc.measurable.comp (hV n)).sub (hc.measurable.comp (hU n))
    have hmvec' : Measurable (fun ω : Ω => (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)) • unitVector i)) := by
      apply measurable_pi_lambda
      intro j
      change Measurable (fun ω : Ω => (ρ n)⁻¹ *
        ((EinsteinFull.Work.W8.corrector W (V n ω) -
          EinsteinFull.Work.W8.corrector W (U n ω)) * unitVector i j))
      exact measurable_const.mul (hm.mul measurable_const)
    exact (hXZ.forall_aemeasurable n).add hmvec'.aemeasurable


/-- A bounded corrector preserves joint finite-dimensional distributional limits. -/
theorem sharp_bounded_corrector_preserves_finite_dimensional_limits
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : NoiseSample d)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (m : ℕ) (X U V : ℕ → Ω → Fin m → Vec d)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n))
    (Z : Ω → Fin m → Vec d)
    (hXZ : TendstoInDistribution X atTop Z (fun _ => μ) μ) :
    TendstoInDistribution
      (fun n ω j => X n ω j + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) • unitVector i))
      atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le)
      (norm_nonneg _)
  have hbound (n : ℕ) (ω : Ω) :
      dist (fun j => X n ω j + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) • unitVector i)) (X n ω) ≤
          C / ρ n := by
    apply (dist_pi_le_iff (div_nonneg hC (hρpos n).le)).2
    intro j
    have hc : |EinsteinFull.Work.W8.corrector W (V n ω j) -
        EinsteinFull.Work.W8.corrector W (U n ω j)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector W (V n ω j))
        (EinsteinFull.Work.W8.corrector W (U n ω j))
      linarith [EinsteinFull.Work.W8.corrector_abs_le W (V n ω j),
        EinsteinFull.Work.W8.corrector_abs_le W (U n ω j)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  refine EinsteinRelation.tendstoInDistribution_of_dist_tendsto_zero _ Z hXZ ?_ ?_
  · intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | ε ≤ dist (fun j => X n ω j + (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) • unitVector i)) (X n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_le_of_lt (hbound n ω) hn)
    rw [this]
    exact measureReal_empty
  · intro n
    have hc : Continuous (EinsteinFull.Work.W8.corrector W) :=
      (EinsteinFull.Work.W8.corrector_contDiff W).continuous
    have hmvec : Measurable (fun ω : Ω => fun j => (ρ n)⁻¹ •
        ((EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) • unitVector i)) := by
      apply measurable_pi_lambda
      intro j
      have hm : Measurable (fun ω => EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) :=
        (hc.measurable.comp ((measurable_pi_apply j).comp (hV n))).sub
          (hc.measurable.comp ((measurable_pi_apply j).comp (hU n)))
      apply measurable_pi_lambda
      intro k
      change Measurable (fun ω : Ω => (ρ n)⁻¹ *
        ((EinsteinFull.Work.W8.corrector W (V n ω j) -
          EinsteinFull.Work.W8.corrector W (U n ω j)) * unitVector i k))
      exact measurable_const.mul (hm.mul measurable_const)
    exact (hXZ.forall_aemeasurable n).add hmvec.aemeasurable

/-- A bounded corrector preserves distributional limits on compact time intervals. -/
theorem sharp_bounded_corrector_preserves_compact_time_distribution_limits
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (T : ℝ≥0)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (X U V Y : ℕ → Ω → C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector W (V n ω t) -
        EinsteinFull.Work.W8.corrector W (U n ω t)) • unitVector i))
    (Z : Ω → C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hXZ : TendstoInDistribution X atTop Z (fun _ => μ) μ) :
    TendstoInDistribution Y atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le)
      (norm_nonneg _)
  have hbound (n : ℕ) (ω : Ω) : dist (Y n ω) (X n ω) ≤ C / ρ n := by
    apply (ContinuousMap.dist_le (div_nonneg hC (hρpos n).le)).2
    intro t
    rw [hpert]
    have hc : |EinsteinFull.Work.W8.corrector W (V n ω t) -
        EinsteinFull.Work.W8.corrector W (U n ω t)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector W (V n ω t))
        (EinsteinFull.Work.W8.corrector W (U n ω t))
      linarith [EinsteinFull.Work.W8.corrector_abs_le W (V n ω t),
        EinsteinFull.Work.W8.corrector_abs_le W (U n ω t)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  refine EinsteinRelation.tendstoInDistribution_of_dist_tendsto_zero Y Z hXZ ?_ ?_
  · intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | ε ≤ dist (Y n ω) (X n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt (lt_of_le_of_lt (hbound n ω) hn)
    rw [this]
    exact measureReal_empty
  · intro n
    exact (hY n).aemeasurable


/-- A bounded corrector preserves joint compact-time limits with any side observation. -/
theorem sharp_bounded_corrector_preserves_joint_compact_time_limits
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : NoiseSample d) (T : ℝ≥0)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E) (hA : ∀ n, Measurable (A n))
    (X U V Y : ℕ → Ω → C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector W (V n ω t) -
        EinsteinFull.Work.W8.corrector W (U n ω t)) • unitVector i))
    (Z : Ω → E × C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hXZ : TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ) :
    TendstoInDistribution (fun n ω => (A n ω, Y n ω)) atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le)
      (norm_nonneg _)
  have hbound (n : ℕ) (ω : Ω) : dist (Y n ω) (X n ω) ≤ C / ρ n := by
    apply (ContinuousMap.dist_le (div_nonneg hC (hρpos n).le)).2
    intro t
    rw [hpert]
    have hc : |EinsteinFull.Work.W8.corrector W (V n ω t) -
        EinsteinFull.Work.W8.corrector W (U n ω t)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector W (V n ω t))
        (EinsteinFull.Work.W8.corrector W (U n ω t))
      linarith [EinsteinFull.Work.W8.corrector_abs_le W (V n ω t),
        EinsteinFull.Work.W8.corrector_abs_le W (U n ω t)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  refine EinsteinRelation.tendstoInDistribution_of_dist_tendsto_zero _ Z hXZ ?_ ?_
  · intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | ε ≤ dist (A n ω, Y n ω) (A n ω, X n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, dist_prod_same_left]
      exact not_le_of_gt (lt_of_le_of_lt (hbound n ω) hn)
    rw [this]
    exact measureReal_empty
  · intro n
    exact ((hA n).prodMk (hY n)).aemeasurable


/-- A random bounded corrector preserves joint compact-time limits with any side observation. -/
theorem sharp_random_corrector_preserves_joint_compact_time_limits
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : Ω → NoiseSample d) (T : ℝ≥0)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E) (hA : ∀ n, Measurable (A n))
    (X U V Y : ℕ → Ω → C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)) • unitVector i))
    (Z : Ω → E × C(Set.Icc (0 : ℝ≥0) T, Vec d))
    (hXZ : TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ) :
    TendstoInDistribution (fun n ω => (A n ω, Y n ω)) atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le)
      (norm_nonneg _)
  have hbound (n : ℕ) (ω : Ω) : dist (Y n ω) (X n ω) ≤ C / ρ n := by
    apply (ContinuousMap.dist_le (div_nonneg hC (hρpos n).le)).2
    intro t
    rw [hpert]
    have hc : |EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector (W ω) (V n ω t))
        (EinsteinFull.Work.W8.corrector (W ω) (U n ω t))
      linarith [EinsteinFull.Work.W8.corrector_abs_le (W ω) (V n ω t),
        EinsteinFull.Work.W8.corrector_abs_le (W ω) (U n ω t)]
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  refine EinsteinRelation.tendstoInDistribution_of_dist_tendsto_zero _ Z hXZ ?_ ?_
  · intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | ε ≤ dist (A n ω, Y n ω) (A n ω, X n ω)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, dist_prod_same_left]
      exact not_le_of_gt (lt_of_le_of_lt (hbound n ω) hn)
    rw [this]
    exact measureReal_empty
  · intro n
    exact ((hA n).prodMk (hY n)).aemeasurable

/-- A bounded random corrector preserves joint limits in the full path topology. -/
theorem sharp_random_corrector_preserves_joint_full_path_limits
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : Ω → NoiseSample d)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E)
    (X U V Y : ℕ → Ω → Path d) (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)) • unitVector i))
    (Z : Ω → E × Path d)
    (hXZ : TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ) :
    TendstoInDistribution (fun n ω => (A n ω, Y n ω)) atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  let D : ℕ → Ω → Path d := fun n ω => Y n ω - X n ω
  have hbound (n : ℕ) (ω : Ω) (t : ℝ≥0) : ‖D n ω t‖ ≤ C / ρ n := by
    have hc : |EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector (W ω) (V n ω t))
        (EinsteinFull.Work.W8.corrector (W ω) (U n ω t))
      linarith [EinsteinFull.Work.W8.corrector_abs_le (W ω) (V n ω t),
        EinsteinFull.Work.W8.corrector_abs_le (W ω) (U n ω t)]
    change ‖Y n ω t - X n ω t‖ ≤ C / ρ n
    rw [hpert, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  have hD : Tendsto (fun p : ℕ × Ω => D p.1 p.2) (atTop ×ˢ ⊤) (𝓝 (0 : Path d)) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    rw [Filter.eventually_iff, Filter.mem_prod_top]
    filter_upwards [he] with n hn ω t ht
    simpa only [ContinuousMap.zero_apply, dist_zero_left] using lt_of_le_of_lt (hbound n ω t) hn
  have hprob : ∀ N ∈ 𝓝 (0 : Path d),
      Tendsto (fun n => μ {ω | D n ω ∉ N}) atTop (𝓝 0) := by
    intro N hN
    have he : ∀ᶠ n in atTop, ∀ ω, D n ω ∈ N := by
      have h := hD.eventually hN
      rw [Filter.eventually_iff, Filter.mem_prod_top] at h
      exact h
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | D n ω ∉ N} = ∅ := by ext ω; simp [hn ω]
    simp only [this, measure_empty]
  have hDm : ∀ n, AEMeasurable (D n) μ := by
    intro n
    exact (hY n).aemeasurable.sub (measurable_snd.comp_aemeasurable (hXZ.forall_aemeasurable n))
  have hp := EinsteinRelation.tendstoInDistribution_prodMk_of_tendsto_const hXZ hprob hDm
  have hc := hp.continuous_comp (g := fun p : (E × Path d) × Path d =>
    (p.1.1, p.1.2 + p.2)) (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd))
  simpa [Function.comp_def, D, add_comm] using hc


private theorem sharp_corrector_eval_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (W : Ω → NoiseSample d) (hW : Measurable W)
    (F : Ω → Vec d) (hF : Measurable F) :
    Measurable (fun ω => EinsteinFull.Work.W8.corrector (W ω) (F ω)) := by
  change Measurable (fun ω => EinsteinFull.Work.W8.seedScale d * seedField d (W ω) (F ω))
  have hpair : Measurable (fun ω : Ω => (W ω, F ω)) := hW.prodMk hF
  have hseed : Measurable (fun ω : Ω => seedField d (W ω) (F ω)) :=
    Measurable.comp (g := fun p : NoiseSample d × Vec d => seedField d p.1 p.2)
      (f := fun ω : Ω => (W ω, F ω)) (measurable_seedField_uncurry d) hpair
  exact hseed.const_mul (EinsteinFull.Work.W8.seedScale d)

private theorem sharp_corrector_difference_path_measurable {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (i : Fin d) (W : Ω → NoiseSample d) (hW : Measurable W)
    (r : ℝ) (U V X Y : Ω → Path d) (hU : Measurable U) (hV : Measurable V)
    (hpert : ∀ ω t, Y ω t = X ω t + r •
      ((EinsteinFull.Work.W8.corrector (W ω) (V ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U ω t)) • unitVector i)) :
    Measurable (fun ω => Y ω - X ω) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hUeval : Measurable (fun ω => U ω t) := (ContinuousMap.measurable_eval t).comp hU
  have hVeval : Measurable (fun ω => V ω t) := (ContinuousMap.measurable_eval t).comp hV
  have hc : Measurable (fun ω => EinsteinFull.Work.W8.corrector (W ω) (V ω t) -
      EinsteinFull.Work.W8.corrector (W ω) (U ω t)) :=
    (sharp_corrector_eval_measurable W hW _ hVeval).sub
      (sharp_corrector_eval_measurable W hW _ hUeval)
  have hm : Measurable (fun ω => r •
      ((EinsteinFull.Work.W8.corrector (W ω) (V ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U ω t)) • unitVector i)) :=
    (measurable_const : Measurable (fun _ : Ω => r)).smul (hc.smul_const (unitVector i))
  convert hm using 1
  funext ω
  change Y ω t - X ω t = _
  rw [hpert, add_sub_cancel_left]

/-- Measurable input paths give the full-path random corrector transfer. -/
theorem sharp_random_corrector_joint_full_path_limits_of_measurable_inputs
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : Ω → NoiseSample d) (hW : Measurable W)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E)
    (X U V Y : ℕ → Ω → Path d)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)) • unitVector i))
    (Z : Ω → E × Path d)
    (hXZ : TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ) :
    TendstoInDistribution (fun n ω => (A n ω, Y n ω)) atTop Z (fun _ => μ) μ := by
  let C : ℝ := 2 * EinsteinFull.Work.W8.seedScale d * ‖unitVector i‖
  let D : ℕ → Ω → Path d := fun n ω => Y n ω - X n ω
  have hbound (n : ℕ) (ω : Ω) (t : ℝ≥0) : ‖D n ω t‖ ≤ C / ρ n := by
    have hc : |EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector (W ω) (V n ω t))
        (EinsteinFull.Work.W8.corrector (W ω) (U n ω t))
      linarith [EinsteinFull.Work.W8.corrector_abs_le (W ω) (V n ω t),
        EinsteinFull.Work.W8.corrector_abs_le (W ω) (U n ω t)]
    change ‖Y n ω t - X n ω t‖ ≤ C / ρ n
    rw [hpert, add_sub_cancel_left, norm_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos n))]
    dsimp [C]
    rw [div_eq_mul_inv]
    nlinarith [norm_nonneg (unitVector i), inv_pos.mpr (hρpos n),
      mul_nonneg (sub_nonneg.mpr hc) (norm_nonneg (unitVector i))]
  have hD : Tendsto (fun p : ℕ × Ω => D p.1 p.2) (atTop ×ˢ ⊤) (𝓝 (0 : Path d)) := by
    rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Tendsto (fun n => C / ρ n) atTop (𝓝 0) := hρ.const_div_atTop C
    have he : ∀ᶠ n in atTop, C / ρ n < ε := ht.eventually (eventually_lt_nhds hε)
    rw [Filter.eventually_iff, Filter.mem_prod_top]
    filter_upwards [he] with n hn ω t ht
    simpa only [ContinuousMap.zero_apply, dist_zero_left] using lt_of_le_of_lt (hbound n ω t) hn
  have hprob : ∀ N ∈ 𝓝 (0 : Path d),
      Tendsto (fun n => μ {ω | D n ω ∉ N}) atTop (𝓝 0) := by
    intro N hN
    have he : ∀ᶠ n in atTop, ∀ ω, D n ω ∈ N := by
      have h := hD.eventually hN
      rw [Filter.eventually_iff, Filter.mem_prod_top] at h
      exact h
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [he] with n hn
    have : {ω | D n ω ∉ N} = ∅ := by ext ω; simp [hn ω]
    simp only [this, measure_empty]
  have hDm : ∀ n, AEMeasurable (D n) μ := by
    intro n
    exact (sharp_corrector_difference_path_measurable i W hW (ρ n)⁻¹
      (U n) (V n) (X n) (Y n) (hU n) (hV n) (hpert n)).aemeasurable
  have hp := EinsteinRelation.tendstoInDistribution_prodMk_of_tendsto_const hXZ hprob hDm
  have hc := hp.continuous_comp (g := fun p : (E × Path d) × Path d =>
    (p.1.1, p.1.2 + p.2)) (continuous_fst.fst.prodMk (continuous_fst.snd.add continuous_snd))
  simpa [Function.comp_def, D, add_comm] using hc


/-- A bounded random corrector preserves and reflects joint full-path limits. -/
theorem sharp_random_corrector_joint_full_path_limits_iff
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} (i : Fin d) (W : Ω → NoiseSample d) (hW : Measurable W)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E)
    (X U V Y : ℕ → Ω → Path d)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)) • unitVector i))
    (Z : Ω → E × Path d) :
    TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ ↔
    TendstoInDistribution (fun n ω => (A n ω, Y n ω)) atTop Z (fun _ => μ) μ := by
  constructor
  · exact sharp_random_corrector_joint_full_path_limits_of_measurable_inputs
      μ i W hW ρ hρpos hρ A X U V Y hU hV hpert Z
  · intro hYZ
    apply sharp_random_corrector_joint_full_path_limits_of_measurable_inputs
      μ i W hW ρ hρpos hρ A Y V U X hV hU _ Z hYZ
    intro n ω t
    rw [← neg_sub, neg_smul, smul_neg, ← sub_eq_add_neg, hpert, add_sub_cancel_right]


/-- A bounded corrector perturbation controls expectations of joint Lipschitz observables. -/
theorem sharp_joint_endpoint_lipschitz_expectation_error
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (i : Fin d)
    (W : Ω → NoiseSample d) (ρ : ℝ) (hρ : 0 < ρ)
    (A : Ω → E) (hA : Measurable A) (X Y U V : Ω → Vec d)
    (hX : Measurable X) (hY : Measurable Y)
    (hpert : ∀ ω, Y ω = X ω + ρ⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V ω) -
        EinsteinFull.Work.W8.corrector (W ω) (U ω)) • unitVector i))
    (φ : E × Vec d → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφX : Integrable (fun ω => φ (A ω, X ω)) μ) :
    Integrable (fun ω => φ (A ω, Y ω)) μ ∧
      |(∫ ω, φ (A ω, Y ω) ∂μ) - (∫ ω, φ (A ω, X ω) ∂μ)| ≤
        (K : ℝ) * (2 * EinsteinFull.Work.W8.seedScale d) / ρ := by
  let C : ℝ := (K : ℝ) * (2 * EinsteinFull.Work.W8.seedScale d) / ρ
  have hpoint (ω : Ω) : ‖φ (A ω, Y ω) - φ (A ω, X ω)‖ ≤ C := by
    have hc : |EinsteinFull.Work.W8.corrector (W ω) (V ω) -
        EinsteinFull.Work.W8.corrector (W ω) (U ω)| ≤
        2 * EinsteinFull.Work.W8.seedScale d := by
      have h := abs_sub (EinsteinFull.Work.W8.corrector (W ω) (V ω))
        (EinsteinFull.Work.W8.corrector (W ω) (U ω))
      linarith [EinsteinFull.Work.W8.corrector_abs_le (W ω) (V ω),
        EinsteinFull.Work.W8.corrector_abs_le (W ω) (U ω)]
    have hv : dist (Y ω) (X ω) ≤ 2 * EinsteinFull.Work.W8.seedScale d / ρ := by
      rw [dist_eq_norm, hpert, add_sub_cancel_left, norm_smul, norm_smul,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      simp only [unitVector, Pi.norm_single, norm_one, mul_one]
      rw [div_eq_mul_inv]
      nlinarith [inv_pos.mpr hρ]
    have hl := hφ.dist_le_mul (A ω, Y ω) (A ω, X ω)
    rw [dist_prod_same_left, Real.dist_eq] at hl
    rw [Real.norm_eq_abs]
    dsimp [C]
    exact hl.trans (by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hv (NNReal.coe_nonneg K))
  have hmX : Measurable (fun ω => φ (A ω, X ω)) :=
    hφ.continuous.measurable.comp (hA.prodMk hX)
  have hmY : Measurable (fun ω => φ (A ω, Y ω)) :=
    hφ.continuous.measurable.comp (hA.prodMk hY)
  have hd : Integrable (fun ω => φ (A ω, Y ω) - φ (A ω, X ω)) μ :=
    Integrable.of_bound (hmY.sub hmX).aestronglyMeasurable C (Eventually.of_forall hpoint)
  have hφY : Integrable (fun ω => φ (A ω, Y ω)) μ := by
    convert hd.add hφX using 1 <;> ext ω <;> simp
  refine ⟨hφY, ?_⟩
  rw [← integral_sub hφY hφX, ← Real.norm_eq_abs]
  have hi := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hpoint)
  simpa [C] using hi

/-- Finite evaluations preserve the joint limit under the random corrector perturbation. -/
theorem sharp_random_corrector_preserves_joint_finite_dimensional_limits
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (i : Fin d)
    (W : Ω → NoiseSample d) (hW : Measurable W)
    (ρ : ℕ → ℝ) (hρpos : ∀ n, 0 < ρ n) (hρ : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E)
    (X U V Y : ℕ → Ω → Path d)
    (hU : ∀ n, Measurable (U n)) (hV : ∀ n, Measurable (V n))
    (hpert : ∀ n ω t, Y n ω t = X n ω t + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W ω) (V n ω t) -
        EinsteinFull.Work.W8.corrector (W ω) (U n ω t)) • unitVector i))
    (Z : Ω → E × Path d) (m : ℕ) (τ : Fin m → ℝ≥0)
    (hlim : TendstoInDistribution (fun n ω => (A n ω, X n ω)) atTop Z (fun _ => μ) μ) :
    TendstoInDistribution (fun n ω => (A n ω, fun j : Fin m => Y n ω (τ j)))
      atTop (fun ω => ((Z ω).1, fun j : Fin m => (Z ω).2 (τ j)))
      (fun _ => μ) μ := by
  have hy := (sharp_random_corrector_joint_full_path_limits_iff
    μ i W hW ρ hρpos hρ A X U V Y hU hV hpert Z).mp hlim
  have hc : Continuous (fun p : E × Path d => (p.1, fun j : Fin m => p.2 (τ j))) := by
    apply Continuous.prodMk continuous_fst
    apply continuous_pi_iff.mpr
    intro j
    exact (continuous_eval_const (τ j)).comp continuous_snd
  simpa only [Function.comp_def] using hy.continuous_comp hc


/-- The expectation error from a bounded corrector perturbation vanishes at large scale. -/
theorem sharp_joint_endpoint_expectation_error_tendsto_zero
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (i : Fin d)
    (W : ℕ → Ω → NoiseSample d) (ρ : ℕ → ℝ)
    (hρ : ∀ n, 0 < ρ n) (hρtop : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E) (hA : ∀ n, Measurable (A n))
    (X Y U V : ℕ → Ω → Vec d)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω, Y n ω = X n ω + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W n ω) (V n ω) -
        EinsteinFull.Work.W8.corrector (W n ω) (U n ω)) • unitVector i))
    (φ : E × Vec d → ℝ) (K : ℝ≥0) (hφ : LipschitzWith K φ)
    (hφX : ∀ n, Integrable (fun ω => φ (A n ω, X n ω)) μ) :
    Tendsto (fun n => (∫ ω, φ (A n ω, Y n ω) ∂μ) -
      (∫ ω, φ (A n ω, X n ω) ∂μ)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n => (ρ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hρtop
  have herr : Tendsto (fun n => (K : ℝ) *
      (2 * EinsteinFull.Work.W8.seedScale d) / ρ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul ((K : ℝ) * (2 * EinsteinFull.Work.W8.seedScale d))
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) _ herr
  exact Eventually.of_forall fun n =>
    (sharp_joint_endpoint_lipschitz_expectation_error μ i (W n) (ρ n) (hρ n)
      (A n) (hA n) (X n) (Y n) (U n) (V n) (hX n) (hY n) (hpert n)
      φ K hφ (hφX n)).2

/-- The expectation error vanishes uniformly over Lipschitz observables with a fixed constant. -/
theorem sharp_joint_endpoint_expectation_errors_uniformly_vanish
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [PseudoMetricSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (i : Fin d)
    (W : ℕ → Ω → NoiseSample d) (ρ : ℕ → ℝ)
    (hρ : ∀ n, 0 < ρ n) (hρtop : Tendsto ρ atTop atTop)
    (A : ℕ → Ω → E) (hA : ∀ n, Measurable (A n))
    (X Y U V : ℕ → Ω → Vec d)
    (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    (hpert : ∀ n ω, Y n ω = X n ω + (ρ n)⁻¹ •
      ((EinsteinFull.Work.W8.corrector (W n ω) (V n ω) -
        EinsteinFull.Work.W8.corrector (W n ω) (U n ω)) • unitVector i))
    (K : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∀ φ : E × Vec d → ℝ, LipschitzWith K φ →
        Integrable (fun ω => φ (A n ω, X n ω)) μ →
        |(∫ ω, φ (A n ω, Y n ω) ∂μ) -
          (∫ ω, φ (A n ω, X n ω) ∂μ)| < ε := by
  have hinv : Tendsto (fun n => (ρ n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hρtop
  have herr : Tendsto (fun n => (K : ℝ) *
      (2 * EinsteinFull.Work.W8.seedScale d) / ρ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      hinv.const_mul ((K : ℝ) * (2 * EinsteinFull.Work.W8.seedScale d))
  intro ε hε
  have hevent : ∀ᶠ n in atTop,
      (K : ℝ) * (2 * EinsteinFull.Work.W8.seedScale d) / ρ n < ε :=
    herr.eventually (eventually_lt_nhds hε)
  filter_upwards [hevent] with n hn
  intro φ hφ hφX
  exact lt_of_le_of_lt
    (sharp_joint_endpoint_lipschitz_expectation_error μ i (W n) (ρ n) (hρ n)
      (A n) (hA n) (X n) (Y n) (U n) (V n) (hX n) (hY n) (hpert n)
      φ K hφ hφX).2 hn

/-- The proved reduced-law foundation supplies the sharp harmonic reduction. -/
theorem sharp_harmonic_reduction_from_proved_foundation
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_harmonicStmt :=
  sharp_harmonic_of_announced_reduced_foundation EinsteinFull.c16_reduced_mp_exists h0 h1

/-- The constructed environment has the stated velocity for every supplied reduced law. -/
theorem sharp_actual_reduced_velocity_first_from_graph
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω))) :
    ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) ell ∧
      ell (⟨0, by omega⟩ : Fin d) = lam :=
  (sharp_harmonic_reduction_from_proved_foundation h0 h1 d hd P hP D Q hQ).2.2.2
    lam hlam Y hY

/-- The velocity of the supplied reduced law has Euclidean norm at least the force. -/
theorem sharp_actual_reduced_velocity_norm_lower_bound_from_graph
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω))) :
    ∃ ell : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) ell ∧
      ell (⟨0, by omega⟩ : Fin d) = lam ∧ |lam| ≤ euclideanNorm ell := by
  obtain ⟨ell, hv, he⟩ :=
    sharp_actual_reduced_velocity_first_from_graph h0 h1 d hd P hP D Q hQ lam hlam Y hY
  refine ⟨ell, hv, he, ?_⟩
  rw [← he]
  exact EinsteinRelation.Entropy.abs_apply_le_euclideanNorm ell ⟨0, by omega⟩

/-- Every quenched velocity of the supplied reduced law has the sharp first coordinate. -/
theorem sharp_any_actual_reduced_velocity_first_from_graph
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (ell : Vec d) (hell : HasQuenchedVelocity Q.measure (originLaw Y) ell) :
    ell (⟨0, by omega⟩ : Fin d) = lam := by
  obtain ⟨v, hv, hvfirst⟩ :=
    sharp_actual_reduced_velocity_first_from_graph h0 h1 d hd P hP D Q hQ lam hlam Y hY
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) := by
    filter_upwards [hY] with ω hω
    exact hω.1
  have heq : ell = v := hell.unique hprob hv
  rw [heq]
  exact hvfirst

/-- Every quenched velocity of the supplied reduced law has the sharp norm bound. -/
theorem sharp_any_actual_reduced_velocity_norm_lower_bound_from_graph
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (ell : Vec d) (hell : HasQuenchedVelocity Q.measure (originLaw Y) ell) :
    |lam| ≤ euclideanNorm ell := by
  have he := sharp_any_actual_reduced_velocity_first_from_graph
    h0 h1 d hd P hP D Q hQ lam hlam Y hY ell hell
  rw [← he]
  exact EinsteinRelation.Entropy.abs_apply_le_euclideanNorm ell ⟨0, by omega⟩

/-- Velocities of supplied reduced laws separate their signed forces. -/
theorem sharp_actual_reduced_velocities_separate_forces_from_graph
    (h0 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h1 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam mu : ℝ) (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (Y Z : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hZ : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω mu) 0 (Z (0, ω)))
    (ell v : Vec d)
    (hell : HasQuenchedVelocity Q.measure (originLaw Y) ell)
    (hv : HasQuenchedVelocity Q.measure (originLaw Z) v) :
    |lam - mu| ≤ euclideanNorm (ell - v) := by
  have hellfirst := sharp_any_actual_reduced_velocity_first_from_graph
    h0 h1 d hd P hP D Q hQ lam hlam Y hY ell hell
  have hvfirst := sharp_any_actual_reduced_velocity_first_from_graph
    h0 h1 d hd P hP D Q hQ mu hmu Z hZ v hv
  have hbound := EinsteinRelation.Entropy.abs_apply_le_euclideanNorm (ell - v)
    (⟨0, by omega⟩ : Fin d)
  simpa [Pi.sub_apply, hellfirst, hvfirst] using hbound

/-- A scalar fourth-moment estimate used in compact-path moment transfer. -/
private theorem fourth_power_le_eight_of_le_add {a b c : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (h : a ≤ b + c) :
    a ^ 4 ≤ 8 * b ^ 4 + 8 * c ^ 4 := by
  have hbc : 0 ≤ 7 * b ^ 2 + 10 * b * c + 7 * c ^ 2 := by positivity
  have hfactor : 0 ≤ (b - c) ^ 2 * (7 * b ^ 2 + 10 * b * c + 7 * c ^ 2) :=
    mul_nonneg (sq_nonneg _) hbc
  have hsum : (b + c) ^ 4 ≤ 8 * b ^ 4 + 8 * c ^ 4 := by
    nlinarith [hfactor]
  exact (pow_le_pow_left₀ ha h 4).trans hsum

/-- The scaled raw path maximum is continuous as a function of the path. -/
private theorem continuous_raw_compact_path_max {d : ℕ} (r : ℝ) (T : ℝ≥0) :
    Continuous (fun γ : Path d => ⨆ s : Set.Icc (0 : ℝ≥0) T,
      euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0))) := by
  have hnorm : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i))
  let f : Path d → Set.Icc (0 : ℝ≥0) T → ℝ := fun γ s =>
    euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0))
  have hf : Continuous (Function.uncurry f) := by
    dsimp only [f, Function.uncurry]
    apply hnorm.comp
    have ht : Continuous (fun p : Path d × Set.Icc (0 : ℝ≥0) T =>
        Real.toNNReal (r^2) * p.2.1) :=
      continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    exact (continuous_const : Continuous (fun _ : Path d × Set.Icc (0 : ℝ≥0) T => r⁻¹)).smul
      ((continuous_eval.comp (continuous_fst.prodMk ht)).sub
        ((continuous_eval_const 0).comp continuous_fst))
  simpa only [iSup, Set.image_univ] using
    (isCompact_univ.continuous_sSup hf)

/-- A bounded sharp corrector changes a scaled increment by at most twice its scale. -/
private theorem sharp_scaled_increment_le_corrected {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (r : ℝ) (hr : 1 ≤ r) (x y : Vec d) :
    euclideanNorm (r⁻¹ • (x - y)) ≤
      euclideanNorm (r⁻¹ • (x - y +
        (EinsteinFull.Work.W8.corrector W x - EinsteinFull.Work.W8.corrector W y) •
          unitVector i)) + 2 * EinsteinFull.Work.W8.seedScale d := by
  let a := EinsteinFull.Work.W8.corrector W x - EinsteinFull.Work.W8.corrector W y
  have ha : |a| ≤ 2 * EinsteinFull.Work.W8.seedScale d := by
    dsimp only [a]
    have hx := EinsteinFull.Work.W8.corrector_abs_le W x
    have hy := EinsteinFull.Work.W8.corrector_abs_le W y
    have ht := abs_sub (EinsteinFull.Work.W8.corrector W x)
      (EinsteinFull.Work.W8.corrector W y)
    linarith
  have hinv : 0 ≤ r⁻¹ := inv_nonneg.mpr (by linarith)
  have hinv_le : r⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ hr
  have he : r⁻¹ • (x - y) = r⁻¹ • (x - y + a • unitVector i) +
      r⁻¹ • ((-a) • unitVector i) := by
    rw [← smul_add]
    congr 1
    simp only [neg_smul]
    abel
  rw [he]
  calc
    _ ≤ euclideanNorm (r⁻¹ • (x - y + a • unitVector i)) +
        euclideanNorm (r⁻¹ • ((-a) • unitVector i)) :=
      TimeChange.euclideanNorm_add_le _ _
    _ ≤ euclideanNorm (r⁻¹ • (x - y + a • unitVector i)) +
        2 * EinsteinFull.Work.W8.seedScale d := by
      have hu : euclideanNorm (unitVector i) = 1 := by
        change Real.sqrt (dotProduct (Pi.single i (1 : ℝ)) (Pi.single i 1)) = 1
        rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
      have hn : euclideanNorm (r⁻¹ • ((-a) • unitVector i)) = r⁻¹ * |a| := by
        rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
          hu, mul_one, abs_neg, abs_of_nonneg hinv]
      rw [hn]
      have hm : r⁻¹ * |a| ≤ |a| := by nlinarith [abs_nonneg a]
      linarith

/-- Fourth moments transfer across a deterministic additive bound. -/
private theorem fourth_moment_of_add_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R S : Ω → ℝ) (c M : ℝ)
    (hRmeas : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω) (hS0 : ∀ ω, 0 ≤ S ω)
    (hc : 0 ≤ c) (hbound : ∀ ω, R ω ≤ S ω + c)
    (hS : MemLp S 4 μ) (hM : (∫ ω, (S ω)^4 ∂μ) ≤ M) :
    MemLp R 4 μ ∧ (∫ ω, (R ω)^4 ∂μ) ≤ 8 * M + 8 * c^4 := by
  have hR : MemLp R 4 μ := by
    refine (hS.add (memLp_const c)).mono' hRmeas.aestronglyMeasurable ?_
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hR0 ω)]
    exact hbound ω
  have hRi : Integrable (fun ω => (R ω)^4) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hR0 _)] using
      hR.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hSi : Integrable (fun ω => (S ω)^4) μ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hS0 _)] using
      hS.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  refine ⟨hR, ?_⟩
  calc
    (∫ ω, (R ω)^4 ∂μ) ≤ ∫ ω, (8 * (S ω)^4 + 8 * c^4) ∂μ := by
      apply integral_mono hRi ((hSi.const_mul 8).add (integrable_const _))
      intro ω
      exact fourth_power_le_eight_of_le_add (hR0 ω) (hS0 ω) hc (hbound ω)
    _ = 8 * (∫ ω, (S ω)^4 ∂μ) + 8 * c^4 := by
      rw [integral_add (hSi.const_mul 8) (integrable_const _), integral_const_mul]
      simp
    _ ≤ 8 * M + 8 * c^4 := by linarith

/-- The corrected compact maximum controls the raw maximum pointwise. -/
private theorem sharp_compact_path_max_bound {d : ℕ} (i : Fin d)
    (W : NoiseSample d) (γ : Path d) (r : ℝ) (hr : 1 ≤ r) (T : ℝ≥0) :
    let R := ⨆ s : Set.Icc (0 : ℝ≥0) T,
      euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0))
    let S := ⨆ s : Set.Icc (0 : ℝ≥0) T,
      euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0 +
        (EinsteinFull.Work.W8.corrector W (γ (Real.toNNReal (r^2) * s.1)) -
          EinsteinFull.Work.W8.corrector W (γ 0)) • unitVector i))
    0 ≤ R ∧ 0 ≤ S ∧ R ≤ S + 2 * EinsteinFull.Work.W8.seedScale d := by
  let f : Set.Icc (0 : ℝ≥0) T → ℝ := fun s =>
    euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0))
  let g : Set.Icc (0 : ℝ≥0) T → ℝ := fun s =>
    euclideanNorm (r⁻¹ • (γ (Real.toNNReal (r^2) * s.1) - γ 0 +
      (EinsteinFull.Work.W8.corrector W (γ (Real.toNNReal (r^2) * s.1)) -
        EinsteinFull.Work.W8.corrector W (γ 0)) • unitVector i))
  have hnorm : Continuous (euclideanNorm : Vec d → ℝ) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp
      (continuous_finsetSum _ fun j _ => (continuous_apply j).mul (continuous_apply j))
  have ht : Continuous (fun s : Set.Icc (0 : ℝ≥0) T =>
      γ (Real.toNNReal (r^2) * s.1)) :=
    γ.continuous.comp (continuous_const.mul continuous_subtype_val)
  have hf : Continuous f := hnorm.comp
    ((continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ≥0) T => r⁻¹)).smul
      (ht.sub (continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ≥0) T => γ 0))))
  have hcorr : Continuous (fun s : Set.Icc (0 : ℝ≥0) T =>
      (EinsteinFull.Work.W8.corrector W (γ (Real.toNNReal (r^2) * s.1)) -
        EinsteinFull.Work.W8.corrector W (γ 0)) • unitVector i) :=
    (((EinsteinFull.Work.W8.corrector_contDiff W).continuous.comp ht).sub
      continuous_const).smul (continuous_const : Continuous
        (fun _ : Set.Icc (0 : ℝ≥0) T => unitVector i))
  have hg : Continuous g := hnorm.comp
    ((continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ≥0) T => r⁻¹)).smul
      ((ht.sub continuous_const).add hcorr))
  have hfbd : BddAbove (Set.range f) := by
    simpa only [Set.image_univ] using isCompact_univ.bddAbove_image hf.continuousOn
  have hgbd : BddAbove (Set.range g) := by
    simpa only [Set.image_univ] using isCompact_univ.bddAbove_image hg.continuousOn
  let s0 : Set.Icc (0 : ℝ≥0) T := ⟨0, ⟨le_rfl, bot_le⟩⟩
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨s0⟩
  have hn (v : Vec d) : 0 ≤ euclideanNorm v := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    exact norm_nonneg _
  change 0 ≤ (⨆ s, f s) ∧ 0 ≤ (⨆ s, g s) ∧
    (⨆ s, f s) ≤ (⨆ s, g s) + 2 * EinsteinFull.Work.W8.seedScale d
  refine ⟨(hn _).trans (le_ciSup hfbd s0), (hn _).trans (le_ciSup hgbd s0), ?_⟩
  apply ciSup_le
  intro s
  calc
    f s ≤ g s + 2 * EinsteinFull.Work.W8.seedScale d :=
      sharp_scaled_increment_le_corrected i W r hr _ _
    _ ≤ (⨆ s, g s) + 2 * EinsteinFull.Work.W8.seedScale d :=
      by simpa only [add_comm] using
        add_le_add_right (le_ciSup hgbd s) (2 * EinsteinFull.Work.W8.seedScale d)

/-- A fourth-moment bound for the corrected path transfers to the raw path. -/
theorem sharp_compact_path_fourth_moment_bound_of_corrected_bound
    {d : ℕ} (i : Fin d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → NoiseSample d)
    (γ : ℕ → Ω → Path d) (hγ : ∀ n, Measurable (γ n))
    (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) (T : ℝ≥0)
    (M : ℝ)
    (hcorrected : ∀ n,
      let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
            (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
              EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
      MemLp S 4 μ ∧ (∫ ω, (S ω)^4 ∂μ) ≤ M) :
    ∀ n,
      let R : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
      MemLp R 4 μ ∧ (∫ ω, (R ω)^4 ∂μ) ≤
        8*M + 8*(2*EinsteinFull.Work.W8.seedScale d)^4 := by
  intro n
  let R : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
    euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
  let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
    euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
      (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
        EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
  have hb (ω : Ω) : 0 ≤ R ω ∧ 0 ≤ S ω ∧
      R ω ≤ S ω + 2 * EinsteinFull.Work.W8.seedScale d :=
    sharp_compact_path_max_bound i (W ω) (γ n ω) (ρ n) (hρ n) T
  have hr : Measurable R := (continuous_raw_compact_path_max (ρ n) T).measurable.comp (hγ n)
  exact fourth_moment_of_add_bound μ R S (2 * EinsteinFull.Work.W8.seedScale d) M
    hr (fun ω => (hb ω).1) (fun ω => (hb ω).2.1)
    (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.seedScale_pos d).le)
    (fun ω => (hb ω).2.2) (hcorrected n).1 (hcorrected n).2


/-- A uniform corrected fourth moment controls the raw compact-path square tail. -/
theorem sharp_compact_path_square_tail_of_corrected_fourth_moment_bound
    {d : ℕ} (i : Fin d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → NoiseSample d)
    (γ : ℕ → Ω → Path d) (hγ : ∀ n, Measurable (γ n))
    (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) (T : ℝ≥0)
    (M : ℝ)
    (hcorrected : ∀ n,
      let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
            (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
              EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
      MemLp S 4 μ ∧ (∫ ω, (S ω)^4 ∂μ) ≤ M) :
    ∀ n,
      let R : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
      ∀ B : ℝ, 0 < B →
        (∫ ω in {ω | B < R ω}, (R ω)^2 ∂μ) ≤
          (8*M + 8*(2*EinsteinFull.Work.W8.seedScale d)^4) / B^2 := by
  intro n
  dsimp only
  intro B hB
  let R : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
    euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
  have hR := sharp_compact_path_fourth_moment_bound_of_corrected_bound
    i μ W γ hγ ρ hρ T M hcorrected n
  change MemLp R 4 μ ∧ _ at hR
  have hr : Measurable R := (continuous_raw_compact_path_max (ρ n) T).measurable.comp (hγ n)
  have h2 : Integrable (fun ω => (R ω)^2) μ :=
    (hR.1.mono_exponent (by norm_num)).integrable_sq
  have h4 : Integrable (fun ω => (R ω)^4) μ := by
    simpa only [Real.norm_eq_abs, (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_abs] using
      hR.1.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hset : MeasurableSet {ω | B < R ω} := measurableSet_lt measurable_const hr
  have hpoint : ∀ᵐ ω ∂(μ.restrict {x | B < R x}), B^2 * (R ω)^2 ≤ (R ω)^4 := by
    filter_upwards [ae_restrict_mem hset] with ω hω
    have hs : B^2 ≤ (R ω)^2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sq_nonneg (R ω))]
  have hbound : B^2 * (∫ ω in {ω | B < R ω}, (R ω)^2 ∂μ) ≤
      8*M + 8*(2*EinsteinFull.Work.W8.seedScale d)^4 := by
    calc
      _ = ∫ ω in {ω | B < R ω}, B^2 * (R ω)^2 ∂μ := by rw [integral_const_mul]
      _ ≤ ∫ ω in {ω | B < R ω}, (R ω)^4 ∂μ :=
        integral_mono_ae (h2.restrict.const_mul _) h4.restrict hpoint
      _ ≤ ∫ ω, (R ω)^4 ∂μ :=
        integral_mono_measure Measure.restrict_le_self
          (ae_of_all _ fun ω => (show Even (4 : ℕ) from ⟨2, rfl⟩).pow_nonneg (R ω)) h4
      _ ≤ _ := hR.2
  exact (le_div_iff₀ (sq_pos_of_pos hB)).2 (by nlinarith [hbound])

/-- The raw compact-path squared tails vanish uniformly in the scale. -/
theorem sharp_compact_path_uniform_square_tails_of_corrected_fourth_moment_bound
    {d : ℕ} (i : Fin d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → NoiseSample d)
    (γ : ℕ → Ω → Path d) (hγ : ∀ n, Measurable (γ n))
    (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) (T : ℝ≥0)
    (M : ℝ)
    (hcorrected : ∀ n,
      let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
            (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
              EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
      MemLp S 4 μ ∧ (∫ ω, (S ω)^4 ∂μ) ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 < B ∧ ∀ n,
      let R : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
      (∫ ω in {ω | B < R ω}, (R ω)^2 ∂μ) < ε := by
  intro ε hε
  let C := 8*M + 8*(2*EinsteinFull.Work.W8.seedScale d)^4
  let B := max 1 (C / ε + 1)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB : 0 < B := by linarith
  have hC : C < ε * B := by
    have h := le_max_right (1 : ℝ) (C / ε + 1)
    have hdiv : C / ε < B := by linarith
    simpa only [mul_comm] using (div_lt_iff₀ hε).1 hdiv
  have hBB : B ≤ B^2 := by nlinarith
  have hsmall : C / B^2 < ε := by
    apply (div_lt_iff₀ (sq_pos_of_pos hB)).2
    nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hBB)]
  refine ⟨B, hB, fun n => ?_⟩
  exact lt_of_le_of_lt
    (sharp_compact_path_square_tail_of_corrected_fourth_moment_bound
      i μ W γ hγ ρ hρ T M hcorrected n B hB) hsmall


/-- Corrected fourth moments give uniform integrability of raw compact-path squares. -/
theorem sharp_compact_path_squares_uniformIntegrable_of_corrected_fourth_moment_bound
    {d : ℕ} (i : Fin d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → NoiseSample d)
    (γ : ℕ → Ω → Path d) (hγ : ∀ n, Measurable (γ n))
    (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) (T : ℝ≥0)
    (M : ℝ)
    (hcorrected : ∀ n,
      let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
            (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
              EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
      MemLp S 4 μ ∧ (∫ ω, (S ω)^4 ∂μ) ≤ M) :
    UniformIntegrable (fun n ω =>
      (⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0)))^2) 1 μ := by
  let R : ℕ → Ω → ℝ := fun n ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
    euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0))
  have hmeas (n : ℕ) : Measurable (R n) :=
    (continuous_raw_compact_path_max (ρ n) T).measurable.comp (hγ n)
  have hint (n : ℕ) : Integrable (fun ω => (R n ω)^2) μ :=
    ((sharp_compact_path_fourth_moment_bound_of_corrected_bound
      i μ W γ hγ ρ hρ T M hcorrected n).1.mono_exponent (by norm_num)).integrable_sq
  change UniformIntegrable (fun n ω => (R n ω)^2) 1 μ
  apply uniformIntegrable_of (by norm_num) (by norm_num)
  · exact fun n => ((hmeas n).pow_const 2).aestronglyMeasurable
  · intro ε hε
    let δ : ENNReal := min ε 1
    have hδ : 0 < δ := lt_min hε (by simp)
    have hδtop : δ ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (min_le_right _ _) (by simp))
    obtain ⟨B, hB, htail⟩ :=
      sharp_compact_path_uniform_square_tails_of_corrected_fourth_moment_bound
        i μ W γ hγ ρ hρ T M hcorrected δ.toReal (ENNReal.toReal_pos hδ.ne' hδtop)
    let C : ℝ≥0 := ⟨(B + 1)^2, sq_nonneg _⟩
    refine ⟨C, fun n => ?_⟩
    let A : Set Ω := {ω | C ≤ ‖(R n ω)^2‖₊}
    let E : Set Ω := {ω | B < R n ω}
    have hA : MeasurableSet A := measurableSet_le measurable_const ((hmeas n).pow_const 2).nnnorm
    have hsub : A ⊆ E := by
      intro ω hω
      change C ≤ ‖(R n ω)^2‖₊ at hω
      have hc : (C : ℝ) ≤ ‖(R n ω)^2‖ := by
        exact_mod_cast hω
      change (B + 1)^2 ≤ ‖(R n ω)^2‖ at hc
      have h : (B + 1)^2 ≤ (R n ω)^2 := by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R n ω))] using hc
      change B < R n ω
      have hR0 : 0 ≤ R n ω :=
        (sharp_compact_path_max_bound i (W ω) (γ n ω) (ρ n) (hρ n) T).1
      nlinarith [sq_nonneg (R n ω + (B + 1))]
    calc
      eLpNorm (A.indicator (fun ω => (R n ω)^2)) 1 μ =
          eLpNorm (fun ω => (R n ω)^2) 1 (μ.restrict A) :=
        eLpNorm_indicator_eq_eLpNorm_restrict hA
      _ ≤ eLpNorm (fun ω => (R n ω)^2) 1 (μ.restrict E) :=
        eLpNorm_mono_measure _ (Measure.restrict_mono_set μ hsub)
      _ = ENNReal.ofReal (∫ ω in E, (R n ω)^2 ∂μ) := by
        rw [eLpNorm_one_eq_lintegral_enorm ((hmeas n).pow_const 2).aestronglyMeasurable.restrict,
          ofReal_integral_eq_lintegral_ofReal (hint n).restrict (ae_of_all _ fun ω => sq_nonneg _)]
        congr 1
        funext ω
        simp only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R n ω))]
      _ ≤ δ := by
        rw [← ENNReal.ofReal_toReal hδtop]
        exact ENNReal.ofReal_le_ofReal (le_of_lt (htail n))
      _ ≤ ε := min_le_left _ _


/-- Compact-time coordinate products inherit uniform integrability from the path maximum. -/
theorem sharp_compact_coordinate_products_uniformIntegrable_of_corrected_fourth_moment_bound
    {d : ℕ} (i : Fin d) {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → NoiseSample d)
    (γ : ℕ → Ω → Path d) (hγ : ∀ n, Measurable (γ n))
    (ρ : ℕ → ℝ) (hρ : ∀ n, 1 ≤ ρ n) (T : ℝ≥0)
    (M : ℝ)
    (hcorrected : ∀ n,
      let S : Ω → ℝ := fun ω => ⨆ s : Set.Icc (0 : ℝ≥0) T,
        euclideanNorm ((ρ n)⁻¹ •
          (γ n ω (Real.toNNReal (ρ n^2)*s.1) - γ n ω 0 +
            (EinsteinFull.Work.W8.corrector (W ω) (γ n ω (Real.toNNReal (ρ n^2)*s.1)) -
              EinsteinFull.Work.W8.corrector (W ω) (γ n ω 0)) • unitVector i))
      MemLp S 4 μ ∧ (∫ ω, (S ω)^4 ∂μ) ≤ M)
    (s t : ℕ → Set.Icc (0 : ℝ≥0) T) (j k : Fin d) :
    UniformIntegrable (fun n ω =>
      ((ρ n)⁻¹ * (γ n ω (Real.toNNReal (ρ n^2)*(s n).1) j - γ n ω 0 j)) *
      ((ρ n)⁻¹ * (γ n ω (Real.toNNReal (ρ n^2)*(t n).1) k - γ n ω 0 k))) 1 μ := by
  let R : ℕ → Ω → ℝ := fun n ω => ⨆ u : Set.Icc (0 : ℝ≥0) T,
    euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*u.1) - γ n ω 0))
  let F : ℕ → Ω → ℝ := fun n ω =>
    ((ρ n)⁻¹ * (γ n ω (Real.toNNReal (ρ n^2)*(s n).1) j - γ n ω 0 j)) *
    ((ρ n)⁻¹ * (γ n ω (Real.toNNReal (ρ n^2)*(t n).1) k - γ n ω 0 k))
  have hm (n : ℕ) : Measurable (F n) := by
    dsimp only [F]
    exact (measurable_const.mul (((measurable_pi_apply j).comp
      ((ContinuousMap.measurable_eval _).comp (hγ n))).sub
      ((measurable_pi_apply j).comp ((ContinuousMap.measurable_eval 0).comp (hγ n))))).mul
      (measurable_const.mul (((measurable_pi_apply k).comp
      ((ContinuousMap.measurable_eval _).comp (hγ n))).sub
      ((measurable_pi_apply k).comp ((ContinuousMap.measurable_eval 0).comp (hγ n)))))
  have hbound (n : ℕ) (ω : Ω) : ‖F n ω‖ ≤ ‖(R n ω)^2‖ := by
    let f : Set.Icc (0 : ℝ≥0) T → ℝ := fun u =>
      euclideanNorm ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*u.1) - γ n ω 0))
    have hnorm : Continuous (euclideanNorm : Vec d → ℝ) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp
        (continuous_finsetSum _ fun l _ => (continuous_apply l).mul (continuous_apply l))
    have hf : Continuous f := hnorm.comp
      ((continuous_const : Continuous (fun _ : Set.Icc (0 : ℝ≥0) T => (ρ n)⁻¹)).smul
        (((γ n ω).continuous.comp (continuous_const.mul continuous_subtype_val)).sub continuous_const))
    have hfbd : BddAbove (Set.range f) := by
      simpa only [Set.image_univ] using isCompact_univ.bddAbove_image hf.continuousOn
    have hc (u : Set.Icc (0 : ℝ≥0) T) (l : Fin d) :
        |(ρ n)⁻¹ * (γ n ω (Real.toNNReal (ρ n^2)*u.1) l - γ n ω 0 l)| ≤ R n ω := by
      have h := EinsteinRelation.Entropy.abs_apply_le_euclideanNorm
        ((ρ n)⁻¹ • (γ n ω (Real.toNNReal (ρ n^2)*u.1) - γ n ω 0)) l
      exact h.trans (le_ciSup hfbd u)
    have hR : 0 ≤ R n ω :=
      (sharp_compact_path_max_bound i (W ω) (γ n ω) (ρ n) (hρ n) T).1
    simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (R n ω))]
    dsimp only [F]
    rw [abs_mul]
    exact (mul_le_mul (hc (s n) j) (hc (t n) k) (abs_nonneg _) hR).trans_eq (sq (R n ω)).symm
  have hu := sharp_compact_path_squares_uniformIntegrable_of_corrected_fourth_moment_bound
    i μ W γ hγ ρ hρ T M hcorrected
  change UniformIntegrable F 1 μ
  refine ⟨hu.1.ae_mono (fun n => (hm n).aestronglyMeasurable) ?_, ?_⟩
  · intro n
    filter_upwards [] with ω
    exact enorm_le_iff_norm_le.mpr (hbound n ω)
  · obtain ⟨C, hC⟩ := hu.2
    refine ⟨C, fun n => (eLpNorm_mono (hm n).aestronglyMeasurable (hbound n)).trans (hC n)⟩

end EinsteinFull.Blueprint
