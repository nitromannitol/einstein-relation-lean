import EinsteinRelation.Entropy.DynkinFromFukushima
import EinsteinRelation.Entropy.LocalTestApproximation
import EinsteinRelation.Entropy.ResolventFromWeak

/-! # The weak resolvent identity from the Dynkin identity

Source: `paper/main.tex` 660-666 (Lemma 4.3, the identity `entropy.weak.resolvent`). For a
horizontal test `F`, the Laplace form of the Dynkin identity (`laplace_dynkin`) gives
`s E[ρ_s F] - s E[F] = E[ρ_s L^λ F]`, and `L^λ F = ½ D·(a DF) + λ (a e₁)·DF`. The weak divergence
of the flux `a DF` (`hasWeakHorizontalDivergence_testFlux`) and the second assertion of Lemma 4.2
turn `E[ρ_s D·(a DF)]` into `-E[Dρ_s · a DF]` (`weak_resolvent_test`).
-/

open MeasureTheory Filter
open scoped ENNReal Topology

open EinsteinRelation.External.GantertSection7Support

noncomputable section

namespace EinsteinRelation

variable {d : ℕ}

theorem HasWeakHorizontalDivergence.congr_field {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V V' : FieldPair d → Vec d} {h : FieldPair d → ℝ} (hV : HasWeakHorizontalDivergence Q hQ V h)
    (hVV : ∀ᵐ w ∂Q, V w = V' w) : HasWeakHorizontalDivergence Q hQ V' h := by
  obtain ⟨hVi, hhi, hid⟩ := hV
  refine ⟨fun i => (hVi i).congr (hVV.mono fun w hw => by simp only [hw]), hhi,
    fun F hF DF hDF => ?_⟩
  rw [← hid F hF DF hDF]
  refine integral_congr_ae (hVV.mono fun w hw => ?_)
  simp only [hw]

/-- Almost every reduced coefficient at the origin is symmetric. -/
theorem ae_symm_reducedCoefficient {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {P : QuenchedPathLaws d}
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P)) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ i j : Fin d, w.1 0 i j = w.1 0 j i := by
  have hentry : ∀ i j : Fin d, Measurable fun w : FieldPair d => w.1 0 i j := fun i j =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem i j).measurable
  have hS : MeasurableSet {w : FieldPair d | ∀ i j : Fin d, w.1 0 i j = w.1 0 j i} := by
    simp only [Set.setOf_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_eq_fun (hentry i j) (hentry j i)
  unfold Carriers.reducedReferenceLaw
  rw [ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hS]
  filter_upwards [hP] with ω hω
  obtain ⟨hω', -, -⟩ := hω
  intro i j
  have hsym := (hω'.1 0).1
  have h2 := congrFun (congrFun hsym j) i
  rw [Matrix.transpose_apply] at h2
  exact h2

/-- On the reduced reference law, the environment generator of a horizontal test is bounded by
the level `B` of `exists_abs_envGenerator_le`. -/
theorem ae_abs_envGenerator_le {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) {P : QuenchedPathLaws d}
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {B : ℝ}
    (hB : ∀ (v w : FieldPair d), IsRegular (sourceReducedBound Λ₀) v → v.1 = w.1 → ∀ x,
      |envGenerator hd lam F (translate x w)| ≤ B) :
    ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, |envGenerator hd lam F w| ≤ B := by
  have hS : MeasurableSet {w : FieldPair d | |envGenerator hd lam F w| ≤ B} :=
    measurableSet_le (continuous_abs.measurable.comp (measurable_envGenerator hd lam hF))
      measurable_const
  unfold Carriers.reducedReferenceLaw
  rw [ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hS]
  filter_upwards [hP] with ω hω
  obtain ⟨hω', -, -⟩ := hω
  have h := hB _ (reduce ω) hω' rfl 0
  rwa [translate_zero] at h

/-- **The weak resolvent identity for a horizontal test** (`paper/main.tex` 662-666), given the
second assertion of Lemma 4.2 for the flux `a G`, where `G` is a version of `DF`. -/
theorem weak_resolvent_test (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (s : {r : ℝ // 0 < r}) {rho : FieldPair d → ℝ}
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P op s rho) {Drho : FieldPair d → Vec d}
    {F : FieldPair d → ℝ} (hF : IsHorizontalTest F) {G : FieldPair d → Vec d} (hGm : Measurable G)
    (hG : ∀ᵐ w ∂Carriers.reducedReferenceLaw Q, ∀ i, horizontalDerivative i F w = G w i)
    (hdiv : HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ
        (fun w k => ∑ j, w.1 0 j k * G w j) (testFluxDiv F) →
      Integrable (fun w => rho w * testFluxDiv F w) (Carriers.reducedReferenceLaw Q) ∧
        ∫ w, rho w * testFluxDiv F w ∂(Carriers.reducedReferenceLaw Q) =
          -∫ w, dot (Drho w) (fun k => ∑ j, w.1 0 j k * G w j)
            ∂(Carriers.reducedReferenceLaw Q)) :
    s.1 * (∫ w, rho w * F w ∂(Carriers.reducedReferenceLaw Q)) -
        s.1 * (∫ w, F w ∂(Carriers.reducedReferenceLaw Q)) =
      -(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G w j)
          ∂(Carriers.reducedReferenceLaw Q)) +
        lam * (∫ w, rho w * (∑ j : Fin d, (w.1 0) j (firstCoordinateIndex hd) * G w j)
          ∂(Carriers.reducedReferenceLaw Q)) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  have hK : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le one_pos (one_le_sourceReducedBound Q.ellipticity_parameter)
  obtain ⟨B, hB0, hB⟩ := exists_abs_envGenerator_le hd lam hF hK
  have hL := laplace_dynkin hFOT hd Q h0 h1 P op hP hF hB0 hB s hrho
  rw [hL]
  obtain ⟨L, Ba, hL0, hBa0, hae⟩ := DriftH5.ae_entry_regular Q hQ
  obtain ⟨M0, M1, M2, hM1, hM2, -, hb1, -⟩ := hF.exists_bounds
  have hentry : ∀ i j : Fin d, Measurable fun w : FieldPair d => w.1 0 i j := fun i j =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem i j).measurable
  set X : FieldPair d → ℝ := fun w => ∑ j : Fin d, (w.1 0) j (firstCoordinateIndex hd) * G w j
    with hXdef
  -- The clamped generator is the generator, written with the version `G`.
  have hgen : ∀ᵐ w ∂μ, clampedEnvGenerator hd lam B F w = (1 / 2) * testFluxDiv F w + lam * X w := by
    filter_upwards [ae_abs_envGenerator_le hd Q h0 h1 hP hF hB, hG] with w hw hGw
    rw [clampedEnvGenerator_eq hw, envGenerator_eq_testFluxDiv]
    simp only [hXdef, hGw]
  -- Integrability.
  have hone := Density.integral_density_eq_one Q.measure P op s rho hrho
  have hρint : Integrable rho μ := Integrable.of_integral_ne_zero (by
    rw [hμdef]; unfold Carriers.reducedReferenceLaw; rw [hone]; exact one_ne_zero)
  have hXm : Measurable X := Finset.measurable_sum _ fun j _ =>
    (hentry j _).mul ((measurable_pi_apply j).comp hGm)
  have hXb : ∀ᵐ w ∂μ, ‖X w‖ ≤ ∑ _j : Fin d, Ba * M1 := by
    filter_upwards [hae, hG] with w hw hGw
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, ← hGw j]
    exact mul_le_mul (hw j _).2.1 (hb1 w 0 j) (abs_nonneg _) hBa0
  have hρX : Integrable (fun w => rho w * X w) μ := hρint.mul_bdd hXm.aestronglyMeasurable hXb
  -- The weak divergence of the flux written with `G`.
  have hflux : HasWeakHorizontalDivergence μ hQ (fun w k => ∑ j, w.1 0 j k * G w j)
      (testFluxDiv F) := by
    refine (hasWeakHorizontalDivergence_testFlux Q hQ hF).congr_field ?_
    filter_upwards [hG] with w hGw
    funext k
    simp only [testFlux, hGw]
  obtain ⟨hρh, hρheq⟩ := hdiv hflux
  have hsym := ae_symm_reducedCoefficient hd Q h0 h1 hP
  have hdot : ∫ w, dot (Drho w) (fun k => ∑ j, w.1 0 j k * G w j) ∂μ =
      ∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G w j) ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hsym] with w hw
    unfold dot
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hw j i]
    ring
  calc ∫ w, rho w * clampedEnvGenerator hd lam B F w ∂μ
      = ∫ w, ((1 / 2) * (rho w * testFluxDiv F w) + lam * (rho w * X w)) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hgen] with w hw
        rw [hw]
        ring
    _ = (1 / 2) * ∫ w, rho w * testFluxDiv F w ∂μ + lam * ∫ w, rho w * X w ∂μ := by
        rw [integral_add (hρh.const_mul _) (hρX.const_mul _), integral_const_mul,
          integral_const_mul]
    _ = _ := by
        rw [hρheq, hdot]
        ring

/-! ## Passage to the limit -/

theorem measurable_entry_localSigma' {U : Set (Vec d)} {x : Vec d} (hx : x ∈ U) (j k : Fin d) :
    Measurable[localSigma U] (fun w : FieldPair d => w.1 x j k) := by
  have h : Measurable[localSigma U] (fun ω : FieldPair d => (ω.1 x, ω.2 x)) :=
    Measurable.of_comap_le (le_iSup (fun x : U =>
      MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 x, ω.2 x)) inferInstance) ⟨x, hx⟩)
  exact (continuous_id.matrix_elem j k).measurable.comp (measurable_fst.comp h)

/-- An `L^q` bound by a finite combination of coordinates. -/
theorem eLpNorm_le_ofReal_mul_sum {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {q : ℝ≥0∞}
    (hq : 1 ≤ q) {g : Ω → ℝ} {v : Fin d → Ω → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ j, AEStronglyMeasurable (v j) μ) (hgm : AEStronglyMeasurable g μ)
    (hg : ∀ᵐ x ∂μ, |g x| ≤ c * ∑ j, |v j x|) :
    eLpNorm g q μ ≤ ENNReal.ofReal c * ∑ j, eLpNorm (v j) q μ := by
  have h1 : eLpNorm g q μ ≤ eLpNorm (fun x => c * ∑ j, ‖v j x‖) q μ :=
    eLpNorm_mono_ae_real hgm (hg.mono fun x hx => by
      simpa only [Real.norm_eq_abs] using hx)
  have h2 : eLpNorm (fun x => c * ∑ j, ‖v j x‖) q μ =
      ENNReal.ofReal c * eLpNorm (fun x => ∑ j, ‖v j x‖) q μ := by
    have e0 : (fun x => c * ∑ j, ‖v j x‖) = c • fun x => ∑ j, ‖v j x‖ := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]
    rw [e0, eLpNorm_const_smul, Real.enorm_eq_ofReal hc]
  have e : (fun x => ∑ j, ‖v j x‖) = ∑ j, (fun x => ‖v j x‖) := by
    funext x
    simp only [Finset.sum_apply]
  have h3 : eLpNorm (fun x => ∑ j, ‖v j x‖) q μ ≤ ∑ j, eLpNorm (v j) q μ := by
    rw [e]
    refine (eLpNorm_sum_le hq).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => eLpNorm_norm _ (hv j)
  rw [h2] at h1
  exact h1.trans (by gcongr)

theorem tendsto_zero_of_ofReal_abs_le {x : ℕ → ℝ} {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hx : ∀ n, ENNReal.ofReal |x n| ≤ e n) :
    Tendsto x atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ENNReal.ofReal |x n|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun n => zero_le) hx
  have h2 : Tendsto (fun n => (ENNReal.ofReal |x n|).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h
    exact h
  have h3 : Tendsto (fun n => |x n|) atTop (𝓝 0) :=
    h2.congr fun n => ENNReal.toReal_ofReal (abs_nonneg _)
  exact (tendsto_zero_iff_abs_tendsto_zero x).mpr h3

theorem tendsto_const_mul_sum {e : Fin d → ℕ → ℝ≥0∞} (he : ∀ j, Tendsto (e j) atTop (𝓝 0))
    (c : ℝ) : Tendsto (fun n => ENNReal.ofReal c * ∑ j, e j n) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => ∑ j, e j n) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun j _ => he j
    simpa using h
  have h := ENNReal.Tendsto.const_mul hs (Or.inr (ENNReal.ofReal_ne_top (r := c)))
  rwa [mul_zero] at h

theorem euclideanNorm_le_sum_abs' (x : Vec d) : euclideanNorm x ≤ ∑ i, |x i| := by
  have h1 : ∑ i, x i * x i ≤ (∑ i, |x i|) ^ 2 := by
    calc ∑ i, x i * x i = ∑ i, |x i| * |x i| :=
          Finset.sum_congr rfl fun i _ => (abs_mul_abs_self (x i)).symm
      _ ≤ ∑ i, ∑ j, |x i| * |x j| :=
          Finset.sum_le_sum fun i hi => Finset.single_le_sum
            (f := fun j => |x i| * |x j|) (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hi
      _ = (∑ i, |x i|) ^ 2 := by rw [sq, Finset.sum_mul_sum]
  unfold euclideanNorm euclideanSq dot
  calc Real.sqrt (∑ i, x i * x i) ≤ Real.sqrt ((∑ i, |x i|) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ∑ i, |x i| := Real.sqrt_sq (Finset.sum_nonneg fun i _ => abs_nonneg _)

theorem integrable_of_lintegral_ofReal_abs_lt {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) (hfin : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ < ⊤) :
    Integrable f μ := by
  refine ⟨hf, ?_⟩
  unfold HasFiniteIntegral
  simpa only [Real.enorm_eq_ofReal_abs] using hfin

theorem ofReal_abs_integral_le_of_lintegral_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) {M : ℝ≥0∞} (h : ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ ≤ M) :
    ENNReal.ofReal |∫ ω, f ω ∂μ| ≤ M := by
  calc ENNReal.ofReal |∫ ω, f ω ∂μ| = ‖∫ ω, f ω ∂μ‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
    _ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
    _ = ∫⁻ ω, ENNReal.ofReal |f ω| ∂μ := lintegral_congr fun ω => Real.enorm_eq_ofReal_abs _
    _ ≤ M := h

theorem abs_coord_le_euclideanNorm' (x : Vec d) (i : Fin d) : |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

/-- The flux `a Y` of a vector field. -/
def coeffFlux (Y : FieldPair d → Vec d) (w : FieldPair d) : Vec d :=
  fun i => ∑ j, w.1 0 i j * Y w j

/-- The drift `(a e₁) · Y` of a vector field. -/
def coeffDrift (hd : 2 ≤ d) (Y : FieldPair d → Vec d) (w : FieldPair d) : ℝ :=
  ∑ j, w.1 0 j (firstCoordinateIndex hd) * Y w j

theorem abs_euclideanNorm_coeffFlux_le {Y : FieldPair d → Vec d} {w : FieldPair d} {Ba : ℝ}
    (hw : ∀ i j : Fin d, |w.1 0 i j| ≤ Ba) :
    |euclideanNorm (coeffFlux Y w)| ≤ (d * Ba) * ∑ j, |Y w j| := by
  have hnn : 0 ≤ euclideanNorm (coeffFlux Y w) := by unfold euclideanNorm; exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hnn]
  refine (euclideanNorm_le_sum_abs' _).trans ?_
  calc ∑ i, |coeffFlux Y w i| ≤ ∑ _i : Fin d, Ba * ∑ j, |Y w j| := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hw i j) (abs_nonneg _)
    _ = (d * Ba) * ∑ j, |Y w j| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem abs_coeffDrift_le (hd : 2 ≤ d) {Y : FieldPair d → Vec d} {w : FieldPair d} {Ba : ℝ}
    (hw : ∀ i j : Fin d, |w.1 0 i j| ≤ Ba) :
    |coeffDrift hd Y w| ≤ Ba * ∑ j, |Y w j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hw j _) (abs_nonneg _)

theorem measurable_coeffFlux_local {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U)
    {Y : FieldPair d → Vec d} (hY : Measurable[localSigma U] Y) :
    Measurable[localSigma U] (coeffFlux Y) := by
  letI : MeasurableSpace (FieldPair d) := localSigma U
  exact Measurable.of_eval fun i => Finset.measurable_sum _ fun j _ =>
    (measurable_entry_localSigma' h0 i j).mul ((measurable_pi_apply j).comp hY)

theorem measurable_coeffDrift_local (hd : 2 ≤ d) {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U)
    {Y : FieldPair d → Vec d} (hY : Measurable[localSigma U] Y) :
    Measurable[localSigma U] (coeffDrift hd Y) := by
  letI : MeasurableSpace (FieldPair d) := localSigma U
  exact Finset.measurable_sum _ fun j _ =>
    (measurable_entry_localSigma' h0 j _).mul ((measurable_pi_apply j).comp hY)

theorem dot_coeffFlux (x : Vec d) (Y : FieldPair d → Vec d) (w : FieldPair d) :
    dot x (coeffFlux Y w) = ∑ i : Fin d, ∑ j : Fin d, x i * (w.1 0) i j * Y w j := by
  unfold dot coeffFlux
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The transposed flux `aᵀ Y`, the flux of the generator. -/
def coeffFluxT (Y : FieldPair d → Vec d) (w : FieldPair d) : Vec d :=
  fun k => ∑ j, w.1 0 j k * Y w j

theorem abs_euclideanNorm_coeffFluxT_le {Y : FieldPair d → Vec d} {w : FieldPair d} {Ba : ℝ}
    (hw : ∀ i j : Fin d, |w.1 0 i j| ≤ Ba) :
    |euclideanNorm (coeffFluxT Y w)| ≤ (d * Ba) * ∑ j, |Y w j| := by
  have hnn : 0 ≤ euclideanNorm (coeffFluxT Y w) := by
    unfold euclideanNorm; exact Real.sqrt_nonneg _
  rw [abs_of_nonneg hnn]
  refine (euclideanNorm_le_sum_abs' _).trans ?_
  calc ∑ i, |coeffFluxT Y w i| ≤ ∑ _i : Fin d, Ba * ∑ j, |Y w j| := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hw j i) (abs_nonneg _)
    _ = (d * Ba) * ∑ j, |Y w j| := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem measurable_coeffFluxT_local {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U)
    {Y : FieldPair d → Vec d} (hY : Measurable[localSigma U] Y) :
    Measurable[localSigma U] (coeffFluxT Y) := by
  letI : MeasurableSpace (FieldPair d) := localSigma U
  exact Measurable.of_eval fun i => Finset.measurable_sum _ fun j _ =>
    (measurable_entry_localSigma' h0 j i).mul ((measurable_pi_apply j).comp hY)

/-- The divergence of the flux of a horizontal test is in every `L^q` of the reduced law. -/
theorem memLp_testFluxDiv {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {F : FieldPair d → ℝ}
    (hF : IsHorizontalTest F) (q : ℝ≥0∞) :
    MemLp (testFluxDiv F) q (Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  obtain ⟨L, Ba, hL0, hBa0, hae⟩ := DriftH5.ae_entry_regular Q hQ
  obtain ⟨M0, M1, M2, hM1, hM2, -, hb1, hb2⟩ := hF.exists_bounds
  have hentry : ∀ j k : Fin d, Measurable fun w : FieldPair d => w.1 0 j k := fun j k =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable
  have hm : Measurable (testFluxDiv F) := by
    unfold testFluxDiv
    exact Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ =>
      ((measurable_fderiv_entry_zero j k _).mul (hF.measurable_derivative j)).add
        ((hentry j k).mul ((hF.horizontalDerivative j).measurable_derivative k))
  refine MemLp.of_bound hm.aestronglyMeasurable (∑ _k : Fin d, ∑ _j : Fin d, (L * M1 + Ba * M2)) ?_
  filter_upwards [hae] with w hw
  rw [Real.norm_eq_abs]
  unfold testFluxDiv
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]; exact mul_le_mul ((hw j k).2.2.2 k) (hb1 w 0 j) (abs_nonneg _) hL0
  · rw [abs_mul]
    have h2 : |horizontalDerivative k (horizontalDerivative j F) w| ≤ M2 := by
      show |fderiv ℝ (orbit (EinsteinRelation.horizontalDerivative j F) w) 0 (unitVector k)| ≤ M2
      rw [orbit_horizontalDerivative]
      exact hb2 w 0 j k
    exact mul_le_mul (hw j k).2.1 h2 (abs_nonneg _) hBa0

/-- **The weak resolvent identity for a local `f`** (`paper/main.tex` 662-666): from the identities
for the approximating local tests (`weak_resolvent_test`), the occupation bound `hocc` and both
assertions `hdiv1`, `hdiv2` of Lemma 4.2, all on the doubled ball `B_{2r}`. -/
theorem weak_resolvent_of_local (hFOT : FukushimaDecompositionInput) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {lam : ℝ}
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (s : {r : ℝ // 0 < r}) {rho : FieldPair d → ℝ}
    (hrho : Carriers.IsReducedLaplaceDensity Q.measure P op s rho) {Drho : FieldPair d → Vec d}
    {r : ℝ} (hr : 0 < r) {p : ℝ} (hp : 1 ≤ p) {K K' : ℝ}
    (hocc : ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] G →
      MemLp G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q) →
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(Carriers.reducedReferenceLaw Q) ≤
        ENNReal.ofReal K * eLpNorm G (ENNReal.ofReal p) (Carriers.reducedReferenceLaw Q))
    (hdiv1 : ∀ V : FieldPair d → Vec d,
      Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] V →
      MemLp (fun w => euclideanNorm (V w)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) →
      Integrable (fun w => dot (Drho w) (V w)) (Carriers.reducedReferenceLaw Q) ∧
        ENNReal.ofReal |∫ w, dot (Drho w) (V w) ∂(Carriers.reducedReferenceLaw Q)| ≤
          ENNReal.ofReal K' * eLpNorm (fun w => euclideanNorm (V w)) (ENNReal.ofReal (2 * p))
            (Carriers.reducedReferenceLaw Q))
    (hdiv2 : ∀ V : FieldPair d → Vec d,
      Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] V →
      MemLp (fun w => euclideanNorm (V w)) (ENNReal.ofReal (2 * p))
        (Carriers.reducedReferenceLaw Q) →
      ∀ h : FieldPair d → ℝ, MemLp h (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q) →
      HasWeakHorizontalDivergence (Carriers.reducedReferenceLaw Q) hQ V h →
      Integrable (fun w => rho w * h w) (Carriers.reducedReferenceLaw Q) ∧
        ∫ w, rho w * h w ∂(Carriers.reducedReferenceLaw Q) =
          -∫ w, dot (Drho w) (V w) ∂(Carriers.reducedReferenceLaw Q))
    {f : FieldPair d → ℝ} {Df : FieldPair d → Vec d}
    (hf : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ f Df)
    (hfM : MemLp f (ENNReal.ofReal (2 * p)) (Carriers.reducedReferenceLaw Q))
    (hDfM : MemLp (fun w => euclideanNorm (Df w)) (ENNReal.ofReal (2 * p))
      (Carriers.reducedReferenceLaw Q))
    (hfL : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] f)
    (hDfL : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] Df) :
    s.1 * (∫ w, rho w * f w ∂(Carriers.reducedReferenceLaw Q)) -
        s.1 * (∫ w, f w ∂(Carriers.reducedReferenceLaw Q)) =
      -(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j)
          ∂(Carriers.reducedReferenceLaw Q)) +
        lam * (∫ w, rho w * (∑ j : Fin d, (w.1 0) j (firstCoordinateIndex hd) * Df w j)
          ∂(Carriers.reducedReferenceLaw Q)) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) := by
    unfold Carriers.reducedReferenceLaw
    exact inferInstance
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  set U2 : Set (Vec d) := {y : Vec d | euclideanNorm y < 2 * r} with hU2def
  set U1 : Set (Vec d) := {y : Vec d | euclideanNorm y < r} with hU1def
  have hU12 : U1 ⊆ U2 := fun y hy => by
    simp only [hU1def, hU2def, Set.mem_setOf_eq] at hy ⊢
    linarith
  have h0U2 : (0 : Vec d) ∈ U2 := by
    have e : euclideanNorm (0 : Vec d) = 0 := by simp [euclideanNorm, euclideanSq, dot]
    simp only [hU2def, Set.mem_setOf_eq, e]
    linarith
  set q : ℝ≥0∞ := ENNReal.ofReal (2 * p) with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  haveI : Fact (1 ≤ q) := ⟨hq1⟩
  have hqtop : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpq : ENNReal.ofReal p ≤ q := ENNReal.ofReal_le_ofReal (by linarith)
  have hentry : ∀ i j : Fin d, Measurable fun w : FieldPair d => w.1 0 i j := fun i j =>
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem i j).measurable
  have hfm : Measurable f := hfL.mono (Probability.localSigma_le_borel U1) le_rfl
  have hDfm : Measurable Df := hDfL.mono (Probability.localSigma_le_borel U1) le_rfl
  have hDim : ∀ i, Measurable fun w => Df w i := fun i => (measurable_pi_apply i).comp hDfm
  have hDfq : ∀ i, MemLp (fun w => Df w i) q μ := fun i =>
    hDfM.of_le (hDim i).aestronglyMeasurable (ae_of_all _ fun w => by
      have hn : 0 ≤ euclideanNorm (Df w) := by unfold euclideanNorm; exact Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hn, Real.norm_eq_abs]
      exact abs_coord_le_euclideanNorm' _ i)
  have hfL2 : Measurable[localSigma U2] f := hfL.mono (Probability.localSigma_mono hU12) le_rfl
  have hDfL2 : Measurable[localSigma U2] Df := hDfL.mono (Probability.localSigma_mono hU12) le_rfl
  obtain ⟨F, G, hFt, hFl, hGl, hDG, hFq, hFc, hGq, hGc⟩ :=
    Entropy.exists_local_test_approximation hQ hr hqtop hf hfM hDfq hfL hDfL
  obtain ⟨L, Ba, hL0, hBa0, hae⟩ := DriftH5.ae_entry_regular Q hQ
  have hBa : ∀ᵐ w ∂μ, ∀ i j : Fin d, |w.1 0 i j| ≤ Ba := hae.mono fun w hw i j => (hw i j).2.1
  have hrho0 : ∀ w, 0 ≤ rho w := hrho.2.1
  have hrhom : Measurable rho := hrho.1
  have hGm : ∀ n, Measurable (G n) := fun n =>
    (hGl n).mono (Probability.localSigma_le_borel U2) le_rfl
  have hGjq : ∀ n j, MemLp (fun w => G n w j) q μ := fun n j => by
    have e : (fun w => G n w j) = fun w => (G n w j - Df w j) + Df w j :=
      funext fun w => by ring
    rw [e]
    exact (hGq n j).add (hDfq j)
  have hFnq : ∀ n, MemLp (F n) q μ := fun n => by
    have e : F n = fun w => (F n w - f w) + f w := funext fun w => by ring
    rw [e]
    exact (hFq n).add hfM
  -- Pairing with `ρ` for local `L^p` functions (the occupation bound).
  have hpair : ∀ g : FieldPair d → ℝ, Measurable[localSigma U2] g → MemLp g (ENNReal.ofReal p) μ →
      Integrable (fun w => rho w * g w) μ ∧
        ENNReal.ofReal |∫ w, rho w * g w ∂μ| ≤ ENNReal.ofReal K * eLpNorm g (ENNReal.ofReal p) μ := by
    intro g hgl hgp
    have hgm : Measurable g := hgl.mono (Probability.localSigma_le_borel U2) le_rfl
    have hlin : ∫⁻ w, ENNReal.ofReal |rho w * g w| ∂μ =
        ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |g w| ∂μ :=
      lintegral_congr fun w => by
        rw [abs_mul, abs_of_nonneg (hrho0 w), ENNReal.ofReal_mul (hrho0 w)]
    have hle := hocc g hgl hgp
    rw [← hlin] at hle
    exact ⟨integrable_of_lintegral_ofReal_abs_lt (hrhom.mul hgm).aestronglyMeasurable
      (lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgp)),
      ofReal_abs_integral_le_of_lintegral_le μ _ hle⟩
  -- Fluxes and drifts of `L^q` vector fields.
  have hfluxM : ∀ Y : FieldPair d → Vec d, Measurable Y → (∀ j, MemLp (fun w => Y w j) q μ) →
      MemLp (fun w => euclideanNorm (coeffFlux Y w)) q μ := by
    intro Y hYm hYq
    have hdom : MemLp (fun w => (d * Ba) * ∑ j, |Y w j|) q μ :=
      (memLp_finset_sum _ fun j _ => (hYq j).abs).const_mul _
    have hm : Measurable (coeffFlux Y) := Measurable.of_eval fun i =>
      Finset.measurable_sum _ fun j _ => (hentry i j).mul ((measurable_pi_apply j).comp hYm)
    refine hdom.of_le (Entropy.continuous_euclideanNorm'.measurable.comp hm).aestronglyMeasurable ?_
    filter_upwards [hBa] with w hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
      (Nat.cast_nonneg d) hBa0) (Finset.sum_nonneg fun j _ => abs_nonneg _))]
    exact abs_euclideanNorm_coeffFlux_le hw
  have hfluxTM : ∀ Y : FieldPair d → Vec d, Measurable Y → (∀ j, MemLp (fun w => Y w j) q μ) →
      MemLp (fun w => euclideanNorm (coeffFluxT Y w)) q μ := by
    intro Y hYm hYq
    have hdom : MemLp (fun w => (d * Ba) * ∑ j, |Y w j|) q μ :=
      (memLp_finset_sum _ fun j _ => (hYq j).abs).const_mul _
    have hm : Measurable (coeffFluxT Y) := Measurable.of_eval fun i =>
      Finset.measurable_sum _ fun j _ => (hentry j i).mul ((measurable_pi_apply j).comp hYm)
    refine hdom.of_le (Entropy.continuous_euclideanNorm'.measurable.comp hm).aestronglyMeasurable ?_
    filter_upwards [hBa] with w hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg
      (Nat.cast_nonneg d) hBa0) (Finset.sum_nonneg fun j _ => abs_nonneg _))]
    exact abs_euclideanNorm_coeffFluxT_le hw
  have hdriftM : ∀ Y : FieldPair d → Vec d, Measurable Y → (∀ j, MemLp (fun w => Y w j) q μ) →
      MemLp (coeffDrift hd Y) q μ := by
    intro Y hYm hYq
    have hdom : MemLp (fun w => Ba * ∑ j, |Y w j|) q μ :=
      (memLp_finset_sum _ fun j _ => (hYq j).abs).const_mul _
    have hm : Measurable (coeffDrift hd Y) :=
      Finset.measurable_sum _ fun j _ => (hentry j _).mul ((measurable_pi_apply j).comp hYm)
    refine hdom.of_le hm.aestronglyMeasurable ?_
    filter_upwards [hBa] with w hw
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hBa0
      (Finset.sum_nonneg fun j _ => abs_nonneg _))]
    exact abs_coeffDrift_le hd hw
  -- The identities for the approximating tests.
  have hid : ∀ n, s.1 * (∫ w, rho w * F n w ∂μ) - s.1 * (∫ w, F n w ∂μ) =
      -(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G n w j) ∂μ) +
        lam * (∫ w, rho w * coeffDrift hd (G n) w ∂μ) := by
    intro n
    refine weak_resolvent_test hFOT hd Q hQ h0 h1 P op hP s hrho (hFt n) (hGm n) (hDG n) ?_
    intro hdivn
    exact hdiv2 (coeffFluxT (G n)) (measurable_coeffFluxT_local h0U2 (hGl n))
      (hfluxTM (G n) (hGm n) (hGjq n)) (testFluxDiv (F n)) (memLp_testFluxDiv Q hQ (hFt n) q)
      hdivn
  -- The left side converges.
  have hEl : ∀ n, Measurable[localSigma U2] (fun w => F n w - f w) := fun n => by
    letI : MeasurableSpace (FieldPair d) := localSigma U2
    exact (hFl n).sub hfL2
  have hEp : ∀ n, MemLp (fun w => F n w - f w) (ENNReal.ofReal p) μ := fun n =>
    (hFq n).mono_exponent hpq
  have hρf := hpair f hfL2 (hfM.mono_exponent hpq)
  have hρF : ∀ n, Integrable (fun w => rho w * F n w) μ := fun n =>
    (hpair (F n) (hFl n) ((hFnq n).mono_exponent hpq)).1
  have hT1 : Tendsto (fun n => ∫ w, rho w * (F n w - f w) ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_ofReal_abs_le
      (e := fun n => ENNReal.ofReal K * eLpNorm (fun w => F n w - f w) q μ) ?_ fun n => ?_
    · have h := ENNReal.Tendsto.const_mul hFc (Or.inr (ENNReal.ofReal_ne_top (r := K)))
      rwa [mul_zero] at h
    · refine (hpair _ (hEl n) (hEp n)).2.trans (mul_le_mul_right ?_ _)
      exact eLpNorm_le_eLpNorm_of_exponent_le hpq
  have hT2 : Tendsto (fun n => ∫ w, (F n w - f w) ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_ofReal_abs_le
      (e := fun n => eLpNorm (fun w => F n w - f w) q μ) hFc fun n => ?_
    calc ENNReal.ofReal |∫ w, (F n w - f w) ∂μ| = ‖∫ w, (F n w - f w) ∂μ‖ₑ :=
          (Real.enorm_eq_ofReal_abs _).symm
      _ ≤ ∫⁻ w, ‖F n w - f w‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm (fun w => F n w - f w) 1 μ :=
          (eLpNorm_one_eq_lintegral_enorm (hFq n).aestronglyMeasurable).symm
      _ ≤ eLpNorm (fun w => F n w - f w) q μ :=
          eLpNorm_le_eLpNorm_of_exponent_le hq1
  have hLHS : Tendsto (fun n => s.1 * (∫ w, rho w * F n w ∂μ) - s.1 * (∫ w, F n w ∂μ)) atTop
      (𝓝 (s.1 * (∫ w, rho w * f w ∂μ) - s.1 * (∫ w, f w ∂μ))) := by
    have hdiff : ∀ n, s.1 * (∫ w, rho w * F n w ∂μ) - s.1 * (∫ w, F n w ∂μ) =
        (s.1 * (∫ w, rho w * f w ∂μ) - s.1 * (∫ w, f w ∂μ)) +
          (s.1 * (∫ w, rho w * (F n w - f w) ∂μ) - s.1 * (∫ w, (F n w - f w) ∂μ)) := by
      intro n
      have e1 : ∫ w, rho w * (F n w - f w) ∂μ =
          ∫ w, rho w * F n w ∂μ - ∫ w, rho w * f w ∂μ := by
        rw [← integral_sub (hρF n) hρf.1]
        congr 1
        funext w
        ring
      have e2 : ∫ w, (F n w - f w) ∂μ = ∫ w, F n w ∂μ - ∫ w, f w ∂μ :=
        integral_sub ((hFnq n).integrable hq1) (hfM.integrable hq1)
      rw [e1, e2]
      ring
    have hlim := (tendsto_const_nhds (x := s.1 * (∫ w, rho w * f w ∂μ) -
      s.1 * (∫ w, f w ∂μ))).add ((hT1.const_mul s.1).sub (hT2.const_mul s.1))
    rw [mul_zero, sub_zero, add_zero] at hlim
    exact hlim.congr fun n => (hdiff n).symm
  -- The right side converges.
  set H : ℕ → FieldPair d → Vec d := fun n w j => G n w j - Df w j with hHdef
  have hHm : ∀ n, Measurable (H n) := fun n => (hGm n).sub hDfm
  have hHl : ∀ n, Measurable[localSigma U2] (H n) := fun n => by
    letI : MeasurableSpace (FieldPair d) := localSigma U2
    exact (hGl n).sub hDfL2
  have hHq : ∀ n j, MemLp (fun w => H n w j) q μ := fun n j => hGq n j
  have hfluxG := fun n => hdiv1 (coeffFlux (G n)) (measurable_coeffFlux_local h0U2 (hGl n))
    (hfluxM (G n) (hGm n) (hGjq n))
  have hfluxDf := hdiv1 (coeffFlux Df) (measurable_coeffFlux_local h0U2 hDfL2)
    (hfluxM Df hDfm hDfq)
  have hT3 : Tendsto (fun n => ∫ w, dot (Drho w) (coeffFlux (H n) w) ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_ofReal_abs_le (e := fun n => ENNReal.ofReal K' *
      (ENNReal.ofReal (d * Ba) * ∑ j, eLpNorm (fun w => H n w j) q μ)) ?_ fun n => ?_
    · have h := ENNReal.Tendsto.const_mul (tendsto_const_mul_sum hGc (d * Ba))
        (Or.inr (ENNReal.ofReal_ne_top (r := K')))
      rwa [mul_zero] at h
    · refine (hdiv1 (coeffFlux (H n)) (measurable_coeffFlux_local h0U2 (hHl n))
        (hfluxM (H n) (hHm n) (hHq n))).2.trans (mul_le_mul_right ?_ _)
      refine eLpNorm_le_ofReal_mul_sum hq1 (mul_nonneg (Nat.cast_nonneg d) hBa0)
        (fun j => (hHq n j).aestronglyMeasurable)
        (hfluxM (H n) (hHm n) (hHq n)).aestronglyMeasurable ?_
      filter_upwards [hBa] with w hw
      exact abs_euclideanNorm_coeffFlux_le hw
  have hdriftp : ∀ Y : FieldPair d → Vec d, Measurable Y → Measurable[localSigma U2] Y →
      (∀ j, MemLp (fun w => Y w j) q μ) →
      Integrable (fun w => rho w * coeffDrift hd Y w) μ ∧
        ENNReal.ofReal |∫ w, rho w * coeffDrift hd Y w ∂μ| ≤
          ENNReal.ofReal K * eLpNorm (coeffDrift hd Y) (ENNReal.ofReal p) μ :=
    fun Y hYm hYl hYq => hpair _ (measurable_coeffDrift_local hd h0U2 hYl)
      ((hdriftM Y hYm hYq).mono_exponent hpq)
  have hT4 : Tendsto (fun n => ∫ w, rho w * coeffDrift hd (H n) w ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_ofReal_abs_le (e := fun n => ENNReal.ofReal K *
      (ENNReal.ofReal Ba * ∑ j, eLpNorm (fun w => H n w j) q μ)) ?_ fun n => ?_
    · have h := ENNReal.Tendsto.const_mul (tendsto_const_mul_sum hGc Ba)
        (Or.inr (ENNReal.ofReal_ne_top (r := K)))
      rwa [mul_zero] at h
    · refine (hdriftp (H n) (hHm n) (hHl n) (hHq n)).2.trans (mul_le_mul_right ?_ _)
      refine (eLpNorm_le_eLpNorm_of_exponent_le hpq).trans ?_
      refine eLpNorm_le_ofReal_mul_sum hq1 hBa0 (fun j => (hHq n j).aestronglyMeasurable)
        (hdriftM (H n) (hHm n) (hHq n)).aestronglyMeasurable ?_
      filter_upwards [hBa] with w hw
      exact abs_coeffDrift_le hd hw
  have hRHS : Tendsto (fun n => -(1 / 2 : ℝ) *
      (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G n w j) ∂μ) +
        lam * (∫ w, rho w * coeffDrift hd (G n) w ∂μ)) atTop
      (𝓝 (-(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ) +
        lam * (∫ w, rho w * coeffDrift hd Df w ∂μ))) := by
    have hiD : Integrable (fun w => ∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) μ :=
      hfluxDf.1.congr (ae_of_all _ fun w => dot_coeffFlux (Drho w) Df w)
    have hdD := (hdriftp Df hDfm hDfL2 hDfq).1
    have hdiff : ∀ n, -(1 / 2 : ℝ) *
        (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G n w j) ∂μ) +
          lam * (∫ w, rho w * coeffDrift hd (G n) w ∂μ) =
        (-(1 / 2 : ℝ) * (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ) +
          lam * (∫ w, rho w * coeffDrift hd Df w ∂μ)) +
        (-(1 / 2 : ℝ) * (∫ w, dot (Drho w) (coeffFlux (H n) w) ∂μ) +
          lam * (∫ w, rho w * coeffDrift hd (H n) w ∂μ)) := by
      intro n
      have hiG : Integrable
          (fun w => ∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G n w j) μ :=
        (hfluxG n).1.congr (ae_of_all _ fun w => dot_coeffFlux (Drho w) (G n) w)
      have e1 : ∫ w, dot (Drho w) (coeffFlux (H n) w) ∂μ =
          (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * G n w j) ∂μ) -
            ∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ := by
        rw [← integral_sub hiG hiD]
        congr 1
        funext w
        rw [dot_coeffFlux]
        simp only [hHdef, mul_sub, Finset.sum_sub_distrib]
      have e2 : ∫ w, rho w * coeffDrift hd (H n) w ∂μ =
          (∫ w, rho w * coeffDrift hd (G n) w ∂μ) - ∫ w, rho w * coeffDrift hd Df w ∂μ := by
        rw [← integral_sub (hdriftp (G n) (hGm n) (hGl n) (hGjq n)).1 hdD]
        congr 1
        funext w
        simp only [coeffDrift, hHdef, mul_sub, Finset.sum_sub_distrib]
      rw [e1, e2]
      ring
    have hlim := (tendsto_const_nhds (x := -(1 / 2 : ℝ) *
      (∫ w, (∑ i : Fin d, ∑ j : Fin d, Drho w i * (w.1 0) i j * Df w j) ∂μ) +
        lam * (∫ w, rho w * coeffDrift hd Df w ∂μ))).add
      ((hT3.const_mul (-(1 / 2 : ℝ))).add (hT4.const_mul lam))
    rw [mul_zero, mul_zero, add_zero, add_zero] at hlim
    exact hlim.congr fun n => (hdiff n).symm
  exact tendsto_nhds_unique hLHS (hRHS.congr fun n => (hid n).symm)

/-- **`WeakResolventStep`** (`paper/main.tex` 660-666, the identity `entropy.weak.resolvent` of
Lemma 4.3) from the FOT input, Lemma 4.2 (`DivergenceStatement`, both assertions, used on the
ball `B_{l/λ}`) and Proposition 3.2 (`OccupationStatement`, on the same ball). -/
theorem weakResolventStep_of_fukushima (hFOT : FukushimaDecompositionInput) (d : ℕ) (hd : 2 ≤ d)
    (Λ₀ r₀ : ℝ) (hDiv : Entropy.DivergenceStatement d hd Λ₀ r₀)
    (hOcc : Entropy.OccupationStatement d hd Λ₀ r₀) : Entropy.WeakResolventStep d hd Λ₀ r₀ := by
  unfold Entropy.WeakResolventStep
  by_cases hΛ : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  swap
  · obtain ⟨lD, hrD, -⟩ := hDiv
    refine ⟨lD, hrD, fun l _ => ⟨2, by norm_num, fun p _ => ⟨0, le_rfl, fun Q => ?_⟩⟩⟩
    exact absurd ⟨Q.ellipticity_parameter, Q.range_parameter⟩ hΛ
  obtain ⟨hΛ₀, hr₀⟩ := hΛ
  obtain ⟨lD, hrD, hD⟩ := hDiv
  obtain ⟨lO, hrO, hO⟩ := hOcc hΛ₀ hr₀
  refine ⟨max lD lO, by linarith [le_max_left lD lO], fun l hl => ?_⟩
  have hlD : lD ≤ l := le_trans (le_max_left _ _) hl
  have hlO : lO ≤ l := le_trans (le_max_right _ _) hl
  have hlpos : 0 < l := by linarith
  obtain ⟨pD, hpD, hD'⟩ := hD (2 * l) (by linarith)
  obtain ⟨pO, hpO, hO'⟩ := hO l hlO
  refine ⟨max pD pO, lt_of_lt_of_le hpD (le_max_left _ _), fun p hp => ?_⟩
  have hpD' : pD ≤ p := le_trans (le_max_left _ _) hp
  have hpO' : pO ≤ p := le_trans (le_max_right _ _) hp
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨CD, hCD, hDb⟩ := hD' p hpD'
  obtain ⟨CO, hCO, hOb⟩ := hO' p hpO'
  refine ⟨0, le_rfl, ?_⟩
  intro Q hQ lam hl0 hl1 IQ P op hyp s hs rho hrho Drho hDrho f Df hf hfM hDfM hfL hDfL
  obtain ⟨rfl, hGMP⟩ := hyp
  have hr : 0 < l / (2 * lam) := by positivity
  have hrad1 : (2 * l) / (2 * lam) = 2 * (l / (2 * lam)) := by ring
  have hrad2 : l / lam = 2 * (l / (2 * lam)) := by field_simp
  exact weak_resolvent_of_local hFOT hd Q hQ hl0.le hl1 P op hGMP s hrho hr hp1
    (K := CO * (1 + s.1 * (lam ^ 2)⁻¹)) (K' := CD * lam)
    (fun G hGl hGp =>
      (hOb Q lam hl0 hl1 Q.measure P op ⟨rfl, hGMP⟩ G (by rw [hrad2]; exact hGl) hGp 1 one_pos
        s).2 rho hrho)
    (fun V hVl hVp => (hDb Q hQ lam hl0 hl1 Q.measure P op ⟨rfl, hGMP⟩ s hs rho hrho Drho hDrho V
      (by rw [hrad1]; exact hVl) hVp).1)
    (fun V hVl hVp h hh hdiv => (hDb Q hQ lam hl0 hl1 Q.measure P op ⟨rfl, hGMP⟩ s hs rho hrho
      Drho hDrho V (by rw [hrad1]; exact hVl) hVp).2 h hh hdiv)
    hf hfM hDfM hfL hDfL

end EinsteinRelation
