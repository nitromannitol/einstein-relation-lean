import EinsteinFull.Calculus.C16FiniteTubeChaining
import EinsteinFull.Calculus.LocalEnergyDomainSupport
import EinsteinFull.Calculus.C17TubeCoefficientMesh
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_tube_u2D_probability

open MeasureTheory Filter
open scoped NNReal ENNReal Pointwise
namespace EinsteinFull
open EinsteinRelation
noncomputable section

/-- Translation preserves the coordinate volume of the actual Euclidean window. -/
theorem s3_tube_window_volume_eq {d : ℕ} (x : Vec d) (r : ℝ) :
    volume {y : Vec d | euclideanNorm (y - x) < r} =
      volume {y : Vec d | euclideanNorm y < r} := by
  let e : Vec d ≃ᵐ Vec d := MeasurableEquiv.addRight (-x)
  have hv : (volume : Measure (Vec d)).map e = volume :=
    (measurePreserving_add_right volume (-x)).map_eq
  symm
  calc
    _ = (volume.map e) {y : Vec d | euclideanNorm y < r} := by rw [hv]
    _ = _ := by
      rw [e.measurableEmbedding.map_apply]
      congr 1

/-- A setwise lower bound on a Euclidean endpoint window gives a uniform
strictly positive one-step probability, with the constant independent of the centre. -/
theorem s3_tube_endpoint_mass {d : ℕ} (r cstar : ℝ) (hr : 0 < r)
    (hc : 0 < cstar) : ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧
      ∀ (x : Vec d) (μ : Measure (Path d)) (E : Set (Path d)) (f : Path d → Vec d),
      (∀ A : Set (Vec d), MeasurableSet A →
        A ⊆ {y | euclideanNorm (y - x) < r} →
        ENNReal.ofReal cstar * volume A ≤ μ (E ∩ f ⁻¹' A)) →
      ENNReal.ofReal eta ≤ μ (E ∩ f ⁻¹' {y | euclideanNorm (y - x) < r}) := by
  let V : ℝ := volume.real {y : Vec d | euclideanNorm y < r}
  have hV : 0 < V := by
    simpa [V] using (localSpatialEnergy_window_volume (0 : Vec d) r hr)
  refine ⟨min 1 (cstar * V), lt_min zero_lt_one (mul_pos hc hV), min_le_left _ _, ?_⟩
  intro x μ E f hdom
  have hm : MeasurableSet {y : Vec d | euclideanNorm (y - x) < r} := by
    exact (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have h := hdom _ hm (Set.Subset.rfl)
  rw [s3_tube_window_volume_eq] at h
  have hv : ENNReal.ofReal V ≤ volume {y : Vec d | euclideanNorm y < r} :=
    ENNReal.ofReal_toReal_le
  calc
    ENNReal.ofReal (min 1 (cstar * V)) ≤ ENNReal.ofReal (cstar * V) :=
      ENNReal.ofReal_le_ofReal (min_le_right _ _)
    _ = ENNReal.ofReal cstar * ENNReal.ofReal V := by
      rw [ENNReal.ofReal_mul hc.le]
    _ ≤ ENNReal.ofReal cstar * volume {y : Vec d | euclideanNorm y < r} :=
      mul_le_mul_right hv _
    _ ≤ μ (E ∩ f ⁻¹' {y | euclideanNorm (y - x) < r}) := h


/-- Scaling an arbitrary endpoint set by the inverse force changes its volume
by the inverse dimensional power. -/
theorem s3_tube_physical_set_volume {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (A : Set (Vec d)) :
    volume (lam⁻¹ • A) = ENNReal.ofReal ((lam⁻¹) ^ d) * volume A := by
  simpa only [Module.finrank_pi, Fintype.card_fin] using
    (Measure.addHaar_smul_of_nonneg (volume : Measure (Vec d))
      (inv_nonneg.mpr hlam.le) A)

/-- The physical tube and endpoint event is exactly the rescaled event. -/
theorem s3_tube_physical_event {d : ℕ} (lam h eps : ℝ)
    (hlam : 0 < lam) (hh : 0 < h) (c : Vec d) (A : Set (Vec d)) :
    {Y : Path d | (∀ s : ℝ≥0, s ≤ (h / lam ^ 2).toNNReal →
      euclideanNorm (Y s - lam⁻¹ • c) < eps / (2 * lam)) ∧
      Y (h / lam ^ 2).toNNReal ∈ lam⁻¹ • A} =
    {Y : Path d | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
      euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c) < eps / 2) ∧
      lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  have hl : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have hscale (z : Vec d) :
      euclideanNorm (z - lam⁻¹ • c) < eps / (2 * lam) ↔
        euclideanNorm (lam • z - c) < eps / 2 := by
    have heq : lam • (z - lam⁻¹ • c) = lam • z - c := by
      simp [smul_sub, smul_smul, hlam.ne']
    rw [← heq, TimeChange.euclideanNorm_smul, abs_of_pos hlam]
    rw [mul_comm lam (euclideanNorm (z - lam⁻¹ • c)), ← lt_div_iff₀ hlam]
    congr 1
    ring
  ext Y
  simp only [Set.mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem₀
    (inv_ne_zero hlam.ne'), inv_inv, hscale]
  constructor
  · rintro ⟨htube, hend⟩
    refine ⟨?_, hend⟩
    intro u hu
    apply htube
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hl.le),
      Real.coe_toNNReal _ (div_nonneg hh.le hl.le)]
    exact div_le_div_of_nonneg_right hu hl.le
  · rintro ⟨htube, hend⟩
    refine ⟨?_, hend⟩
    intro s hs
    let u : ℝ≥0 := (lam ^ 2 * (s : ℝ)).toNNReal
    have hu : (u : ℝ) ≤ h := by
      have hs' : (s : ℝ) ≤ h / lam ^ 2 :=
        le_trans (NNReal.coe_le_coe.mpr hs)
          (le_of_eq (Real.coe_toNNReal _ (div_nonneg hh.le hl.le)))
      change ((lam ^ 2 * (s : ℝ)).toNNReal : ℝ) ≤ h
      rw [Real.coe_toNNReal _ (mul_nonneg hl.le s.coe_nonneg)]
      have hs'' := (le_div_iff₀ hl).mp hs'
      simpa only [mul_comm] using hs''
    have htime : ((u : ℝ) / lam ^ 2).toNNReal = s := by
      apply NNReal.eq
      change (((((lam ^ 2 * (s : ℝ)).toNNReal : ℝ) / lam ^ 2).toNNReal : ℝ)) = (s : ℝ)
      rw [Real.coe_toNNReal _ (mul_nonneg hl.le s.coe_nonneg)]
      rw [Real.coe_toNNReal _ (div_nonneg (mul_nonneg hl.le s.coe_nonneg) hl.le)]
      field_simp
    simpa only [htime] using htube u hu

/-- Setwise killed-endpoint lower bound for the literal Section 3 tubes.  The
constant is chosen before the law, force, and supplied quenched kernel. -/
def s3TubeKilledEndpointInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∀ (B C : ℝ) (N : ℕ), 0 < B → 1 ≤ C → 0 < N →
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) →
      ∃ cstar : ℝ, 0 < cstar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
        ∀ k : ℕ, k < N → ∀ x : Vec d,
          euclideanNorm (x - c k) < ε / 16 →
          ∀ A : Set (Vec d), MeasurableSet A →
            A ⊆ {y | euclideanNorm (y - c (k + 1)) < ε / 16} →
            ENNReal.ofReal cstar * volume A ≤ P (lam⁻¹ • x, ω)
              {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
                euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c k) < ε / 2) ∧
                lam • Y (h / lam ^ 2).toNNReal ∈ A}

/-- Physical setwise killed-endpoint lower bound for the same supplied law. -/
def s3TubePhysicalKilledEndpointInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∀ (B C : ℝ) (N : ℕ), 0 < B → 1 ≤ C → 0 < N →
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) →
      ∃ cstar : ℝ, 0 < cstar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
        ∀ k : ℕ, k < N → ∀ x : Vec d,
          euclideanNorm (x - c k) < ε / 16 →
          ∀ A : Set (Vec d), MeasurableSet A →
            A ⊆ {y | euclideanNorm (y - c (k + 1)) < ε / 16} →
            ENNReal.ofReal (cstar * lam ^ d) * volume (lam⁻¹ • A) ≤ P (lam⁻¹ • x, ω)
              {Y | (∀ s : ℝ≥0, s ≤ (h / lam ^ 2).toNNReal →
                euclideanNorm (Y s - lam⁻¹ • c k) < ε / (2 * lam)) ∧
                Y (h / lam ^ 2).toNNReal ∈ lam⁻¹ • A}

/-- A uniform jointly measurable density of the actual physical killed endpoint law. -/
def s3TubePhysicalKilledDensityInput : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∀ (B C : ℝ) (N : ℕ), 0 < B → 1 ≤ C → 0 < N →
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) →
      ∃ cstar : ℝ, 0 < cstar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
        ∀ k : ℕ, k < N → ∃ p : Vec d × Vec d → ℝ≥0∞,
          Measurable p ∧ ∀ x : Vec d,
          euclideanNorm (x - c k) < ε / 16 →
          ((P (lam⁻¹ • x, ω)).restrict
            {Y | ∀ s : ℝ≥0, s ≤ (h / lam ^ 2).toNNReal →
              euclideanNorm (Y s - lam⁻¹ • c k) < ε / (2 * lam)}).map
                (fun Y => Y (h / lam ^ 2).toNNReal) =
              volume.withDensity (fun y => p (x, y)) ∧
          ∀ᵐ y ∂(volume : Measure (Vec d)).restrict
              (lam⁻¹ • {y | euclideanNorm (y - c (k + 1)) < ε / 16}),
            ENNReal.ofReal (cstar * lam ^ d) ≤ p (x, y)

/-- A lower density for the actual killed endpoint law gives its setwise bound. -/
theorem s3_tube_physical_killed_endpoint_of_density
    (hdensity : s3TubePhysicalKilledDensityInput) : s3TubePhysicalKilledEndpointInput := by
  dsimp only [s3TubePhysicalKilledEndpointInput]
  intro d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  obtain ⟨cstar, hc, hbound⟩ := hdensity d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  refine ⟨cstar, hc, ?_⟩
  intro Q lam h₀ h₁ P hP
  filter_upwards [hbound Q lam h₀ h₁ P hP] with ω hω
  intro j hj k hk x hx A hA hsub
  obtain ⟨p, hp, heq⟩ := hω j hj k hk
  obtain ⟨hmeasure, hlower⟩ := heq x hx
  have hscaled : MeasurableSet (lam⁻¹ • A) := hA.const_smul_of_ne_zero (inv_ne_zero h₀.ne')
  have hle := lintegral_mono_ae
    (ae_restrict_of_ae_restrict_of_subset (Set.smul_set_mono hsub) hlower)
  rw [lintegral_const, Measure.restrict_apply_univ, ← withDensity_apply _ hscaled,
    ← hmeasure, Measure.map_apply (continuous_eval_const _).measurable hscaled,
    Measure.restrict_apply (hscaled.preimage (continuous_eval_const _).measurable)] at hle
  convert hle using 1
  congr 1
  ext Y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, and_comm]

/-- Setwise bounds along one actual tube yield both the one-step bounds and
its full finite-chain estimate for the same supplied quenched law. -/
theorem s3_tube_chain_of_setwise {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (eps cstar : ℝ) (heps : 0 < eps) (hc : 0 < cstar) :
    ∃ eta : ℝ, 0 < eta ∧ eta ≤ 1 ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (hlam : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam hlam.le h₁ P →
      ∀ (N : ℕ), 0 < N → ∀ (h : ℝ), 0 < h → ∀ (gamma : ℝ → Vec d),
      gamma 0 = 0 →
      (∀ k : ℕ, k < N → ∀ u : ℝ, (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
        euclideanNorm (gamma u - gamma ((k : ℝ) * h)) ≤ eps / 16) →
      (∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < N → ∀ x : Vec d,
        euclideanNorm (x - gamma ((k : ℝ) * h)) < eps / 16 →
        ∀ A : Set (Vec d), MeasurableSet A →
          A ⊆ {y | euclideanNorm (y - gamma (((k + 1 : ℕ) : ℝ) * h)) < eps / 16} →
          ENNReal.ofReal cstar * volume A ≤ P (lam⁻¹ • x, ω)
            {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
              euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
                gamma ((k : ℝ) * h)) < eps / 2) ∧
              lam • Y (h / lam ^ 2).toNNReal ∈ A}) →
      (∀ᵐ ω ∂Q.measure, (∀ k : ℕ, k < N → ∀ x : Vec d,
        euclideanNorm (x - gamma ((k : ℝ) * h)) < eps / 16 →
        ENNReal.ofReal eta ≤ P (lam⁻¹ • x, ω)
          {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
            euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
              gamma ((k : ℝ) * h)) < eps / 2) ∧
            euclideanNorm (lam • Y (h / lam ^ 2).toNNReal -
              gamma (((k + 1 : ℕ) : ℝ) * h)) < eps / 16}) ∧
        ENNReal.ofReal (eta ^ N) ≤ P (0, ω) {Y | ∀ u : ℝ≥0,
          (u : ℝ) ≤ (N : ℝ) * h →
          euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma (u : ℝ)) < eps}) := by
  obtain ⟨eta, heta, heta1, hmass⟩ := s3_tube_endpoint_mass (eps / 16) cstar (by positivity) hc
  refine ⟨eta, heta, heta1, ?_⟩
  intro Q lam hlam h₁ P hP N hN h hh gamma hzero hosc hinput
  have hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < N → ∀ x : Vec d,
      euclideanNorm (x - gamma ((k : ℝ) * h)) < eps / 16 →
      ENNReal.ofReal eta ≤ P (lam⁻¹ • x, ω)
        {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
          euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - gamma ((k : ℝ) * h)) < eps / 2) ∧
          euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - gamma (((k + 1 : ℕ) : ℝ) * h)) < eps / 16} := by
    filter_upwards [hinput] with ω hinputω
    intro k hk x hx
    exact hmass _ _ _ _ (hinputω k hk x hx)
  have hchain := c16_quenched_actual_tube_of_steps hd Q lam hlam h₁ P hP N hN h eps eta
    hh heps heta.le gamma hzero hosc hstep
  filter_upwards [hstep, hchain] with ω hs ht
  exact ⟨hs, ht⟩


/-- The literal two Section 3 tubes share one positive probability constant and
one environment event, conditional on the stated killed-endpoint input. -/
theorem s3_two_tube_probability_of_killed_endpoint
    (hkilled : s3TubeKilledEndpointInput) (d : ℕ) (hd : 2 ≤ d)
    (Λ₀ r₀ l : ℝ) (hl : 0 < l) :
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∀ (B C : ℝ) (N : ℕ), 0 < B → 1 ≤ C → 0 < N →
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) →
      ∃ cstar η : ℝ, 0 < cstar ∧ 0 < η ∧ η ≤ 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
        (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
        let piece : ℕ → Set (Path d) := fun k =>
          {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
            euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c k) < ε / 2) ∧
            euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - c (k + 1)) < ε / 16}
        (∀ k : ℕ, k < N → ∀ x : Vec d,
          euclideanNorm (x - c k) < ε / 16 →
          (∀ A : Set (Vec d), MeasurableSet A →
            A ⊆ {y | euclideanNorm (y - c (k + 1)) < ε / 16} →
            ENNReal.ofReal cstar * volume A ≤ P (lam⁻¹ • x, ω)
              {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
                euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c k) < ε / 2) ∧
                lam • Y (h / lam ^ 2).toNNReal ∈ A}) ∧
          ENNReal.ofReal η ≤ P (lam⁻¹ • x, ω) (piece k)) ∧
        ENNReal.ofReal (η ^ N) ≤ P (0, ω) {Y | ∀ u : ℝ≥0,
          (u : ℝ) ≤ (j : ℝ) - 1 →
          euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - γ j (u : ℝ)) < ε} := by
  dsimp only
  intro B C N hB hC hN hgeom
  obtain ⟨cstar, hc, hinput⟩ := hkilled d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  obtain ⟨eta, heta, heta1, hchain⟩ :=
    s3_tube_chain_of_setwise hd (l / 32) cstar (by positivity) hc
  refine ⟨cstar, eta, hc, heta, heta1, ?_⟩
  intro Q lam h₀ h₁ P hP
  let γ₂ : ℝ → Vec d := fun u =>
    min ((25 * l / 4) * u) (25 * l / 8) • unitVector (Regeneration.Renewal.forceCoord hd)
  let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
  let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
  have hzero : ∀ j : ℕ, j = 2 ∨ j = 3 → γ j 0 = 0 := by
    intro j hj
    rcases hj with rfl | rfl <;> simp [γ, γ₂, γ₃, min_eq_left (by positivity : (0 : ℝ) ≤ 25 * l / 8)]
  have hfor : ∀ j : ℕ, j = 2 ∨ j = 3 →
      ∀ᵐ ω ∂Q.measure,
        (∀ k : ℕ, k < N → ∀ x : Vec d,
          euclideanNorm (x - γ j ((k : ℝ) * (((j : ℝ) - 1) / N))) < (l / 32) / 16 →
          ENNReal.ofReal eta ≤ P (lam⁻¹ • x, ω)
            {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ ((j : ℝ) - 1) / N →
              euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
                γ j ((k : ℝ) * (((j : ℝ) - 1) / N))) < (l / 32) / 2) ∧
              euclideanNorm (lam • Y ((((j : ℝ) - 1) / N) / lam ^ 2).toNNReal -
                γ j (((k + 1 : ℕ) : ℝ) * (((j : ℝ) - 1) / N))) < (l / 32) / 16}) ∧
        ENNReal.ofReal (eta ^ N) ≤ P (0, ω) {Y | ∀ u : ℝ≥0,
          (u : ℝ) ≤ (N : ℝ) * (((j : ℝ) - 1) / N) →
          euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - γ j (u : ℝ)) < l / 32} := by
    intro j hj
    have hg := hgeom j hj
    apply hchain Q lam h₀ h₁ P hP N hN _ hg.1 (γ j) (hzero j hj) hg.2.2.2
    filter_upwards [hinput Q lam h₀ h₁ P hP] with ω hω
    exact hω j hj
  filter_upwards [hinput Q lam h₀ h₁ P hP, hfor 2 (Or.inl rfl), hfor 3 (Or.inr rfl)] with ω hi h2 h3
  intro j hj
  rcases hj with rfl | rfl
  · refine ⟨?_, ?_⟩
    · intro k hk x hx
      exact ⟨hi 2 (Or.inl rfl) k hk x hx, h2.1 k hk x hx⟩
    · have ht : (N : ℝ) * ((2 - 1) / N) = (2 : ℝ) - 1 := (hgeom 2 (Or.inl rfl)).2.1
      norm_num only [Nat.cast_ofNat] at ht h2
      rw [ht] at h2
      norm_num only [Nat.cast_ofNat]
      simpa [γ, γ₂, γ₃] using h2.2
  · refine ⟨?_, ?_⟩
    · intro k hk x hx
      exact ⟨hi 3 (Or.inr rfl) k hk x hx, h3.1 k hk x hx⟩
    · have ht : (N : ℝ) * ((3 - 1) / N) = (3 : ℝ) - 1 := (hgeom 3 (Or.inr rfl)).2.1
      norm_num only [Nat.cast_ofNat] at ht h3
      rw [ht] at h3
      norm_num only [Nat.cast_ofNat]
      simpa [γ, γ₂, γ₃] using h3.2


/-- The source tube-probability statement follows from the uniform
killed-endpoint lower-kernel input. -/
theorem s3_tube_probability_of_killed_endpoint (hkilled : s3TubeKilledEndpointInput) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt := by
  unfold Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt
  dsimp only
  intro d hd Λ₀ r₀ l hl
  obtain ⟨B, C, N, hB, hC, hN, hgeom, hcoeff⟩ :=
    c17_annealed_coefficient_mesh_prefix Λ₀ r₀ l hl (Regeneration.Renewal.forceCoord hd)
  obtain ⟨cstar, eta, hc, heta, heta1, hprob⟩ :=
    s3_two_tube_probability_of_killed_endpoint hkilled d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  refine ⟨B, C, cstar, eta, N, hB, hC, hc, heta, heta1, hN, hgeom, ?_⟩
  intro Q lam h₀ h₁ P hP
  filter_upwards [hcoeff Q, hprob Q lam h₀ h₁ P hP] with ω hcoeffω hprobω
  exact ⟨hcoeffω lam, hprobω⟩

/-- Physical killed-density bounds yield the rescaled setwise bounds for the same law. -/
theorem s3_tube_killed_endpoint_of_physical
    (hphysical : s3TubePhysicalKilledEndpointInput) : s3TubeKilledEndpointInput := by
  dsimp only [s3TubeKilledEndpointInput]
  intro d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  obtain ⟨cstar, hc, hbound⟩ := hphysical d hd Λ₀ r₀ l hl B C N hB hC hN hgeom
  refine ⟨cstar, hc, ?_⟩
  intro Q lam h₀ h₁ P hP
  filter_upwards [hbound Q lam h₀ h₁ P hP] with ω hω
  intro j hj k hk x hx A hA hsub
  have hh := (hgeom j hj).1
  have hp := hω j hj k hk x hx A hA hsub
  rw [s3_tube_physical_event lam _ _ h₀ hh, s3_tube_physical_set_volume h₀] at hp
  have hcancel : ENNReal.ofReal (cstar * lam ^ d) * ENNReal.ofReal (lam⁻¹ ^ d) =
      ENNReal.ofReal cstar := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hc.le (pow_nonneg h₀.le _))]
    congr 1
    rw [inv_pow]
    field_simp
  simpa only [← mul_assoc, hcancel] using hp

/-- The physical lower bound implies the source tube-probability statement. -/
theorem s3_tube_probability_of_physical_killed_endpoint
    (hphysical : s3TubePhysicalKilledEndpointInput) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  s3_tube_probability_of_killed_endpoint (s3_tube_killed_endpoint_of_physical hphysical)

/-- The source tube conclusion follows from the physical killed-density input. -/
theorem s3_tube_probability_of_physical_killed_density
    (hdensity : s3TubePhysicalKilledDensityInput) :
    Blueprint.node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt :=
  s3_tube_probability_of_physical_killed_endpoint
    (s3_tube_physical_killed_endpoint_of_density hdensity)

end
end EinsteinFull
