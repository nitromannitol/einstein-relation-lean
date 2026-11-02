import EinsteinRelation.External.AKMEnergyDensity
import EinsteinRelation.Mobility.CorrectorGradientMoments
import EinsteinRelation.Correctors.HomogenizedMatrixBounds

/-!
# Transferring the AKM energy estimate to canonical unit-ball energy

Source: `paper/main.tex:727-729`. The stochastic estimate is used only in its
literal normalized-coefficient form. `CanonicalAKMRealization` records the
remaining internal identification and spatial change-of-variable obligations.
It is not an external input and is not proved here. In particular, the theorem
below does not by itself close the gradient part of Lemma 5.1.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- A direction strictly inside AKM's open unit ball. -/
def halfDirection {d : ℕ} (i : Fin d) : Vec d := (1 / 2 : ℝ) • unitVector i

theorem halfDirection_mem_ball {d : ℕ} (i : Fin d) : euclideanNorm (halfDirection i) < 1 := by
  rw [halfDirection, euclideanNorm_smul _ (by norm_num)]
  have hu : euclideanNorm (unitVector i) = 1 := by
    simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  rw [hu]
  norm_num

/-- The positive lower bound for `Φ_{0,1}` on the unit ball. -/
def unitHeatLowerBound (d : ℕ) : ℝ :=
  (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / 4 : ℝ))

theorem unitHeatLowerBound_pos (d : ℕ) : 0 < unitHeatLowerBound d := by
  unfold unitHeatLowerBound
  exact mul_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.exp_pos _)

private theorem euclideanSq_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ euclideanSq x :=
  by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- The kernel comparison requires only Euclidean geometry; no probability
or corrector estimate enters it. -/
theorem unitHeatLowerBound_le {d : ℕ} {x : Vec d} (hx : euclideanNorm x ≤ 1) :
    unitHeatLowerBound d ≤ heatKernel 0 1 x := by
  have hs : euclideanSq x ≤ 1 := by
    have hsq : euclideanNorm x ^ 2 = euclideanSq x :=
      Real.sq_sqrt (euclideanSq_nonneg' x)
    have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    nlinarith
  simp only [heatKernel, euclideanHeatKernel, one_pow, mul_one, sub_zero]
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith))
    (Real.rpow_nonneg (by positivity) _)

/-- Comparison of a local energy with the actual heat-averaged energy.
The heat integrability premise is explicit, so totalized Bochner integrals
cannot silently remove a nonintegrable energy. -/
theorem local_energy_le_heat {d : ℕ} {K : ℝ} {P : Measure (Coefficient d K)}
    {e : Vec d} (φ : Corrector P e) (a : Coefficient d K) {ρ : ℝ} (hρ : ρ ≤ 1)
    (hint : Integrable (fun y => heatKernel 0 1 y *
      ((1 / 2 : ℝ) * dot (e + φ.grad a y) ((a y).mulVec (e + φ.grad a y)))) volume) :
    (unitHeatLowerBound d / 2) *
      (∫ y in ball 0 ρ, euclideanSq (e + φ.grad a y) ∂volume) ≤ energyAverage φ 0 1 a := by
  let f : Vec d → ℝ := fun y => heatKernel 0 1 y *
    ((1 / 2 : ℝ) * dot (e + φ.grad a y) ((a y).mulVec (e + φ.grad a y)))
  have hnonneg : ∀ y, 0 ≤ f y := by
    intro y
    have he := (a.elliptic y (e + φ.grad a y)).1
    have hsq := euclideanSq_nonneg' (e + φ.grad a y)
    exact mul_nonneg (by unfold heatKernel euclideanHeatKernel; positivity)
      (mul_nonneg (by norm_num) (hsq.trans he))
  have hball : MeasurableSet (ball (0 : Vec d) ρ) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have hlocal : ∀ᵐ y ∂volume.restrict (ball 0 ρ),
      unitHeatLowerBound d / 2 * euclideanSq (e + φ.grad a y) ≤ f y := by
    filter_upwards [ae_restrict_mem hball] with y hy
    have hk : unitHeatLowerBound d ≤ heatKernel 0 1 y :=
      unitHeatLowerBound_le ((show euclideanNorm y < ρ by simpa [ball] using hy).le.trans hρ)
    have he := (a.elliptic y (e + φ.grad a y)).1
    have hs := euclideanSq_nonneg' (e + φ.grad a y)
    have hk0 := (unitHeatLowerBound_pos d).le.trans hk
    dsimp [f]
    nlinarith [mul_le_mul_of_nonneg_right hk hs,
      mul_le_mul_of_nonneg_left he hk0]
  calc (unitHeatLowerBound d / 2) *
        (∫ y in ball 0 ρ, euclideanSq (e + φ.grad a y) ∂volume)
      = ∫ y in ball 0 ρ, unitHeatLowerBound d / 2 * euclideanSq (e + φ.grad a y) ∂volume :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ y in ball 0 ρ, f y ∂volume := integral_mono_of_nonneg
        (ae_of_all _ fun y => mul_nonneg (by positivity [unitHeatLowerBound_pos d])
          (euclideanSq_nonneg' _)) hint.integrableOn hlocal
    _ ≤ ∫ y, f y ∂volume := integral_mono_measure Measure.restrict_le_self
        (ae_of_all _ hnonneg) hint
    _ = energyAverage φ 0 1 a := rfl

/-- The factor in the change of variables `x = r₀ y`, including the square
of the factor two in `halfDirection`. The denominator is the physical unit
ball volume in the same Euclidean carrier as `canonicalCorrectorUnitEnergy`. -/
def unitEnergyRescaling (d : ℕ) (r₀ : ℝ) : ℝ :=
  4 * r₀ ^ d / (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1)).toReal

/-- Internal identification obligations for applying AKM to the canonical
gradient. The normalized coefficient is exactly `project`, i.e.
`κ a_red(r₀ ·)`. The intended spatial corrector is
`φ_A(y) = φ_red(r₀ y)/(2r₀)` in the half-unit direction.

`local_energy_identity` is a spatial change-of-variables identity, not a
moment or stochastic estimate. `mean_flux_identity` identifies the source
homogenized flux with the already constructed canonical homogenized matrix.
Proving these fields requires constructing the spatial potential and using
the canonical variational uniqueness theorem; uniqueness is not assumed.
Heat integrability also remains explicit. None of these obligations is
registered as a literature assumption. -/
structure CanonicalAKMRealization {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) where
  corrector : Corrector (actualCoefficientLaw Q) (halfDirection i)
  local_energy_identity : ∀ᵐ ω ∂physicalReferenceLaw Q,
    canonicalCorrectorUnitEnergy Q i (reduce ω.1) ^ 2 = unitEnergyRescaling d r₀ *
      (∫ y in ball 0 r₀⁻¹,
        euclideanSq (halfDirection i + corrector.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y)
          ∂volume)
  mean_flux_identity : dot (halfDirection i) (meanFlux corrector) =
    ellipticityScale L / 4 * dot (unitVector i) ((homogenizedMatrix Q).mulVec (unitVector i))
  heat_integrable : ∀ᵐ a ∂actualCoefficientLaw Q,
    Integrable (fun y => heatKernel 0 1 y * ((1 / 2 : ℝ) *
      dot (halfDirection i + corrector.grad a y)
        ((a y).mulVec (halfDirection i + corrector.grad a y)))) volume

/-- The elementary probability step after comparing the local and heat
energies. Constants are explicit and the probability measure is arbitrary. -/
theorem moment_le_of_os_affine {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {A X : Ω → ℝ} {θ D B m : ℝ}
    (hX : OsBound μ X 1 θ) (hD : 0 ≤ D) (hB : 0 ≤ B) (hm : 0 < m)
    (hA : ∀ ω, 0 ≤ A ω) (hbound : ∀ᵐ ω ∂μ, A ω ≤ D * max (X ω) 0 + B) :
    (∫⁻ ω, ENNReal.ofReal (A ω ^ m) ∂μ) ≤
      ENNReal.ofReal ((2 : ℝ) ^ m *
        (D ^ m * (2 * θ ^ m * m ^ m) + B ^ m)) := by
  have hpt : ∀ᵐ ω ∂μ, ENNReal.ofReal (A ω ^ m) ≤
      ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (D ^ m) * ENNReal.ofReal ((max (X ω) 0) ^ m) +
          ENNReal.ofReal (B ^ m)) := by
    filter_upwards [hbound] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg (hA ω) hm.le]
    calc ENNReal.ofReal (A ω) ^ m
        ≤ ENNReal.ofReal (D * max (X ω) 0 + B) ^ m :=
          ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hω) hm.le
      _ = (ENNReal.ofReal D * ENNReal.ofReal (max (X ω) 0) + ENNReal.ofReal B) ^ m := by
          rw [ENNReal.ofReal_add (by positivity) hB, ENNReal.ofReal_mul hD]
      _ ≤ (2 : ℝ≥0∞) ^ m *
          ((ENNReal.ofReal D * ENNReal.ofReal (max (X ω) 0)) ^ m +
            ENNReal.ofReal B ^ m) :=
          ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow _ _ hm.le
      _ = _ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hm.le,
            ← ENNReal.ofReal_rpow_of_nonneg hD hm.le,
            ← ENNReal.ofReal_rpow_of_nonneg (le_max_right _ _) hm.le,
            ← ENNReal.ofReal_rpow_of_nonneg hB hm.le,
            ← ENNReal.ofReal_ofNat 2,
            ← ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0 : ℝ) ≤ 2) hm.le]
  calc (∫⁻ ω, ENNReal.ofReal (A ω ^ m) ∂μ)
      ≤ ∫⁻ ω, ENNReal.ofReal ((2 : ℝ) ^ m) *
          (ENNReal.ofReal (D ^ m) * ENNReal.ofReal ((max (X ω) 0) ^ m) +
            ENNReal.ofReal (B ^ m)) ∂μ := lintegral_mono_ae hpt
    _ = ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (D ^ m) * (∫⁻ ω, ENNReal.ofReal ((max (X ω) 0) ^ m) ∂μ) +
          ENNReal.ofReal (B ^ m)) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_right _ measurable_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal ((2 : ℝ) ^ m) *
        (ENNReal.ofReal (D ^ m) * ENNReal.ofReal (2 * θ ^ m * m ^ m) +
          ENNReal.ofReal (B ^ m)) := by
      gcongr
      exact hX.moment_pos_le hm
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ m),
        ENNReal.ofReal_add (by positivity [hX.2.2.1]) (Real.rpow_nonneg hB _),
        ENNReal.ofReal_mul (Real.rpow_nonneg hD _)]

/-- Pullback of the Appendix A notation along a measurable map. -/
theorem osBound_comp {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {μ : Measure Ω} {f : Ω → Ω'} (hf : Measurable f) {X : Ω' → ℝ} {s θ : ℝ}
    (h : OsBound (Measure.map f μ) X s θ) : OsBound μ (X ∘ f) s θ := by
  refine ⟨h.1.comp hf, h.2.1, h.2.2.1, ?_⟩
  have hmeas : Measurable X := h.1
  have hmap := lintegral_map (μ := μ) (f := fun ω =>
    ENNReal.ofReal (Real.exp ((θ⁻¹ * max (X ω) 0) ^ s)))
    (by fun_prop) hf
  exact hmap.symm.le.trans h.2.2.2

/-- The actual physical-to-reduced transport of unit-energy moments. -/
theorem canonicalUnitEnergy_moment_transport {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (m : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i ω ^ m) ∂reducedEnvironmentLaw Q) =
    ∫⁻ ω, ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i (reduce ω.1) ^ m)
      ∂physicalReferenceLaw Q := by
  have hm : Measurable (fun ω => ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i ω ^ m)) :=
    ((measurable_canonicalCorrectorUnitEnergy Q i).pow_const m).ennreal_ofReal
  change (∫⁻ ω, ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i ω ^ m)
    ∂Measure.map reduce Q.measure) = _
  rw [← physicalReferenceLaw_forget Q,
    Measure.map_map Probability.measurable_reduce measurable_subtype_coe,
    lintegral_map hm (Probability.measurable_reduce.comp measurable_subtype_coe)]
  rfl

private theorem normalized_ellipticity_gt_one {L : ℝ} (hL : 1 ≤ L) :
    1 < AKMUpperEllipticity L := by
  have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
  have hκ : 1 < ellipticityScale L := by
    unfold ellipticityScale
    nlinarith
  unfold AKMUpperEllipticity
  nlinarith

/-- The deterministic center of (4.4) is bounded using the already proved
canonical homogenized-matrix bound and the realization's flux identity. -/
theorem canonicalAKM_center_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (R : CanonicalAKMRealization Q i) :
    |(1 / 2 : ℝ) * dot (halfDirection i) (meanFlux R.corrector)| ≤
      ellipticityScale L * sourceReducedBound L / 8 := by
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hΛ : 0 < sourceReducedBound L := by unfold sourceReducedBound; positivity
  have hu : euclideanSq (unitVector i) = 1 := by
    simp [euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
  have hlo := homogenizedMatrix_quadratic_lower Q (unitVector i)
  have hhi := homogenizedMatrix_quadratic_upper Q (unitVector i)
  rw [hu] at hlo hhi
  rw [R.mean_flux_identity, abs_of_nonneg (by
    have hq : 0 ≤ dot (unitVector i) ((homogenizedMatrix Q).mulVec (unitVector i)) :=
      (by positivity : 0 ≤ (sourceReducedBound L)⁻¹ * 1).trans hlo
    positivity [ellipticityScale_pos Q.ellipticity_parameter])]
  have hκ := (ellipticityScale_pos Q.ellipticity_parameter).le
  nlinarith [mul_le_mul_of_nonneg_left hhi hκ]

/-- AKM (4.4) implies the former `henergy` obligation, conditional only on
the explicitly separated internal spatial-realization facts. Rescaling of
the law, the heat-kernel comparison, the deterministic homogenized-energy
bound, probability transport and all real-moment conversion are proved here.
The half direction avoids extending the source's open unit ball by fiat. -/
theorem canonicalUnitEnergy_moments_of_akm
    (hAKM : EnergyDensityEstimate)
    (hreal : ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ : ℝ)
      (Q : EnvironmentLaw d L r₀) (i : Fin d), Nonempty (CanonicalAKMRealization Q i)) :
    ∀ (d : ℕ), 2 ≤ d → ∀ (L r₀ m : ℝ), 2 ≤ m → ∃ C : ℝ,
      ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
        (∫⁻ ω, ENNReal.ofReal (canonicalCorrectorUnitEnergy Q i ω ^ m)
          ∂reducedEnvironmentLaw Q) ≤ ENNReal.ofReal C := by
  intro d hd L r₀ m hm
  by_cases hL : 1 ≤ L
  swap
  · exact ⟨0, fun Q _ => False.elim (hL Q.ellipticity_parameter)⟩
  by_cases hr : 1 ≤ r₀
  swap
  · exact ⟨0, fun Q _ => False.elim (hr Q.range_parameter)⟩
  obtain ⟨θ, hθ, hestimate⟩ := hAKM d hd (AKMUpperEllipticity L) 1
    (normalized_ellipticity_gt_one hL) (by norm_num) (by norm_num)
  let k := unitHeatLowerBound d / 2
  let S := unitEnergyRescaling d r₀
  let D := S / k
  let B := ellipticityScale L * sourceReducedBound L / 8
  have hk : 0 < k := by dsimp [k]; exact div_pos (unitHeatLowerBound_pos d) (by norm_num)
  have hS : 0 ≤ S := by dsimp [S, unitEnergyRescaling]; positivity
  have hD : 0 ≤ D := div_nonneg hS hk.le
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hB : 0 ≤ B := by dsimp [B, ellipticityScale, sourceReducedBound]; positivity
  refine ⟨(2 : ℝ) ^ m * (D ^ m * (2 * θ ^ m * m ^ m) + (D * B + 1) ^ m), ?_⟩
  intro Q i
  letI := physicalReferenceLaw_probability Q
  obtain ⟨R⟩ := hreal d hd L r₀ Q i
  let X : Coefficient d (AKMUpperEllipticity L) → ℝ := fun a =>
    |energyAverage R.corrector 0 1 a - (1 / 2 : ℝ) * dot (halfDirection i) (meanFlux R.corrector)|
  have hraw : OsBound (actualCoefficientLaw Q) X 1 θ := by
    simpa only [Real.one_rpow, mul_one] using
      hestimate (actualCoefficientLaw Q) (lawHypotheses_actualCoefficientLaw Q)
        (halfDirection i) (halfDirection_mem_ball i) R.corrector 0 1 le_rfl
  have hpull : OsBound (physicalReferenceLaw Q)
      (X ∘ project (r₀ := r₀) Q.ellipticity_parameter) 1 θ :=
    osBound_comp (measurable_project Q.ellipticity_parameter) hraw
  have hheat := ae_of_ae_map (measurable_project (r₀ := r₀) Q.ellipticity_parameter).aemeasurable
    R.heat_integrable
  have hbound : ∀ᵐ ω ∂physicalReferenceLaw Q,
      canonicalCorrectorUnitEnergy Q i (reduce ω.1) ≤
        D * max ((X ∘ project (r₀ := r₀) Q.ellipticity_parameter) ω) 0 + (D * B + 1) := by
    filter_upwards [R.local_energy_identity, hheat] with ω hid hint
    let a := project (r₀ := r₀) Q.ellipticity_parameter ω
    let E := energyAverage R.corrector 0 1 a
    have hlocal := local_energy_le_heat R.corrector a (inv_le_one_of_one_le₀ hr) hint
    have hscaled := mul_le_mul_of_nonneg_left hlocal hS
    have hAE : canonicalCorrectorUnitEnergy Q i (reduce ω.1) ^ 2 ≤ D * E := by
      dsimp [D]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hk).mpr
      dsimp [k, S, E] at *
      rw [hid]
      nlinarith only [hscaled]
    have hcenter := canonicalAKM_center_le Q i R
    have hE : E ≤ X a + B := by
      have hdev := le_abs_self (E - (1 / 2 : ℝ) * dot (halfDirection i) (meanFlux R.corrector))
      have hc := le_abs_self ((1 / 2 : ℝ) * dot (halfDirection i) (meanFlux R.corrector))
      dsimp [X, B] at *
      linarith
    have hA := canonicalCorrectorUnitEnergy_nonneg Q i (reduce ω.1)
    have hsq := sq_nonneg (canonicalCorrectorUnitEnergy Q i (reduce ω.1) - 1 / 2)
    have hDX := mul_le_mul_of_nonneg_left hE hD
    have hXnonneg : 0 ≤ X a := abs_nonneg _
    change canonicalCorrectorUnitEnergy Q i (reduce ω.1) ≤ D * max (X a) 0 + _
    rw [max_eq_left hXnonneg]
    nlinarith
  rw [canonicalUnitEnergy_moment_transport]
  exact moment_le_of_os_affine (physicalReferenceLaw Q) hpull hD (by positivity)
    (by linarith) (fun ω => canonicalCorrectorUnitEnergy_nonneg Q i (reduce ω.1)) hbound

end EinsteinRelation.Correctors

