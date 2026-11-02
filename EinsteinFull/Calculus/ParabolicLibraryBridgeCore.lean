import EinsteinFull.Calculus.ParabolicLibraryBridgeCoreTransfer
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedPower
import EinsteinFull.Calculus.ParabolicLibraryBridgeAffineH1
import EllipticRegularity.Parabolic.NashLower.Restrict

/-!
# Local boundedness and Hölder decay for library energy-class weak solutions

For a weak solution `u` on `B(c,ρ) × (T₀ - ρ², T₀]` and every constant `κ`, the oscillation of
`u` on `B(c,θρ) × (T₀ - (θρ)², T₀]` is at most `C θ^α` times the scaled `L²` norm of `u - κ`
on the full cylinder, for `θ ≤ 3/8`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE PDE.Parabolic.Rescale

theorem lintegral_sq_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (h : MemLp g 2 μ) : ∫⁻ z, ENNReal.ofReal |g z| ^ (2 : ℝ) ∂μ ≠ ⊤ := by
  have hi : Integrable (fun x => g x ^ 2) μ := h.integrable_sq
  have h1 := hi.lintegral_lt_top
  have e : (fun z => ENNReal.ofReal |g z| ^ (2 : ℝ)) = fun z => ENNReal.ofReal (g z ^ 2) := by
    funext z
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [e]
  exact h1.ne

theorem parabolic_core (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧ ∀ (a : ParCoeffField d) (c : Vec d) (T₀ ρ : ℝ), 0 < ρ →
      IsParabolicCoeff 1 Lam a (euclideanBall c ρ) (Ioc (T₀ - ρ ^ 2) T₀) →
      ∀ u : ParH1Function (euclideanBall c ρ) (Ioc (T₀ - ρ ^ 2) T₀),
      IsParabolicWeakSolution a (euclideanBall c ρ) (Ioc (T₀ - ρ ^ 2) T₀) u →
      ∀ κ θ : ℝ, 0 < θ → θ ≤ 3 / 8 →
      ∃ m' M' : ℝ,
        (∀ᵐ z ∂(volume.restrict (euclideanBall c (θ * ρ) ×ˢ Ioc (T₀ - (θ * ρ) ^ 2) T₀)),
          m' ≤ u.toFun z ∧ u.toFun z ≤ M') ∧
        M' - m' ≤ C * θ ^ α * ((ENNReal.ofReal ((ρ ^ (d + 2))⁻¹) *
          ∫⁻ z in euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀,
            ENNReal.ofReal |u.toFun z - κ| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹).toReal := by
  obtain ⟨C₀, hC₀, hstep⟩ := SignedLocalMax.power_step_S d hd
  obtain ⟨C₁, hC₁, hmax⟩ := SignedLocalMax.signed_local_max_L2 d hd hC₀ hstep Lam hLam
  obtain ⟨α, C₂, hα0, hα1, hC₂, hhol⟩ := osc_holder d hd Lam hLam
  refine ⟨α, max 1 (C₂ * (16 / 3) * C₁), hα0, hα1, le_max_left _ _, ?_⟩
  intro a c T₀ ρ hρ ha u hu κ θ hθ hθ3
  have hI : MeasurableSet (Ioc (T₀ - ρ ^ 2) T₀) := measurableSet_Ioc
  have hfin : volume (euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀) ≠ ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ hρ.le) (by simp)
  have hu' := isParabolicWeakSolution_affine hI hfin (-κ) 1 u hu
  obtain ⟨ã, ũ, hã, hũ, hval, -⟩ :=
    exists_unit_rescaling a c hρ T₀ hI subset_rfl ha (affineParH1 hI hfin (-κ) 1 u) hu'
  have hu'fun : ∀ z, (affineParH1 hI hfin (-κ) 1 u).toFun z = -κ + 1 * u.toFun z :=
    fun z => rfl
  have habs : ∀ z, |(affineParH1 hI hfin (-κ) 1 u).toFun z| = |u.toFun z - κ| := by
    intro z
    rw [hu'fun]
    congr 1
    ring
  have heq : ∀ z, ũ.toFun z = (affineParH1 hI hfin (-κ) 1 u).toFun (cylMap c ρ T₀ z) := by
    intro z
    obtain ⟨y, s⟩ := z
    exact hval y s
  -- the scaled L² integral
  set k := ENNReal.ofReal ((ρ ^ (d + 2))⁻¹) with hk
  set Wint := ∫⁻ z in euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀,
    ENNReal.ofReal |u.toFun z - κ| ^ (2 : ℝ) with hW
  have hWfin : Wint ≠ ⊤ := by
    have hm := (affineParH1 hI hfin (-κ) 1 u).memL2
    have h1 := lintegral_sq_ne_top hm
    have e : Wint = ∫⁻ z in euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀,
        ENNReal.ofReal |(affineParH1 hI hfin (-κ) 1 u).toFun z| ^ (2 : ℝ) := by
      rw [hW]
      exact lintegral_congr fun z => by rw [habs]
    rw [e]
    exact h1
  have hkfin : k ≠ ⊤ := ENNReal.ofReal_ne_top
  have hkWfin : k * Wint ≠ ⊤ := ENNReal.mul_ne_top hkfin hWfin
  have hunit : ∫⁻ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
      ENNReal.ofReal |ũ.toFun z| ^ (2 : ℝ) = k * Wint := by
    have h := lintegral_comp_cylMap_unit c hρ T₀ (affineParH1 hI hfin (-κ) 1 u).toFun
    simp only [← heq] at h
    rw [h, hW]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [habs]
  set R := ∫⁻ z in SignedLocalMax.moserCylZ d (1 / 2) (-3 / 4),
    ENNReal.ofReal |ũ.toFun z| ^ (2 : ℝ) with hR
  have hRle : R ≤ k * Wint := by
    rw [← hunit, hR]
    refine lintegral_mono_set ?_
    intro z hz
    exact ⟨euclideanBall_mono (by norm_num) (by norm_num) hz.1,
      ⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩⟩
  have hmaxres := hmax ã hã ũ hũ
  set Kbd : ℝ≥0∞ := ENNReal.ofReal C₁ * (k * Wint) ^ (2 : ℝ)⁻¹ with hKbd
  have hKfin : Kbd ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hkWfin)
  have hess : essSup (fun z => ENNReal.ofReal |ũ.toFun z|)
      (volume.restrict (SignedLocalMax.moserCylZ d (3 / 8) (-11 / 16))) ≤ Kbd := by
    refine hmaxres.trans (mul_le_mul' le_rfl ?_)
    exact ENNReal.rpow_le_rpow hRle (by norm_num)
  have hae1 : ∀ᵐ z ∂(volume.restrict (SignedLocalMax.moserCylZ d (3 / 8) (-11 / 16))),
      |ũ.toFun z| ≤ Kbd.toReal := by
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict
      (SignedLocalMax.moserCylZ d (3 / 8) (-11 / 16)))
      (fun z => ENNReal.ofReal |ũ.toFun z|)] with z hz
    exact (ENNReal.ofReal_le_iff_le_toReal hKfin).mp (hz.trans hess)
  -- transfer to `u'`
  have hF := cylMap_measurableEmbedding c hρ T₀
  have hk0 : k ≠ 0 := ofReal_inv_pow_ne_zero hρ (d + 2)
  have hmapS := map_restrict_cylMap c hρ T₀ (SignedLocalMax.moserCylZ d (3 / 8) (-11 / 16))
  rw [cylMap_image_moserRegion c hρ T₀] at hmapS
  have hae2 : ∀ᵐ y ∂(volume.restrict (euclideanBall c (ρ * (3 / 8)) ×ˢ
      Ioo (T₀ + ρ ^ 2 * (-11 / 16)) T₀)),
      |(affineParH1 hI hfin (-κ) 1 u).toFun y| ≤ Kbd.toReal := by
    refine ae_of_comp_of_map_eq_smul' hF hk0 hmapS ?_
    filter_upwards [hae1] with z hz
    rw [← heq]
    exact hz
  -- restriction to the smaller cylinder and Hölder decay
  set ρ₁ : ℝ := ρ * (3 / 8) with hρ₁
  have hρ₁0 : 0 < ρ₁ := by positivity
  have hsub : euclideanBall c ρ₁ ⊆ euclideanBall c ρ :=
    euclideanBall_mono hρ₁0.le (by rw [hρ₁]; nlinarith)
  have hIsub : Ioc (T₀ - ρ₁ ^ 2) T₀ ⊆ Ioc (T₀ - ρ ^ 2) T₀ := by
    refine Ioc_subset_Ioc_left ?_
    have : ρ₁ ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hρ₁0.le (by rw [hρ₁]; nlinarith) 2
    linarith
  let u₁ := PDE.Parabolic.NashLower.restrictParH1 (J := Ioc (T₀ - ρ ^ 2) T₀) hsub subset_rfl
    (affineParH1 hI hfin (-κ) 1 u)
  have hu₁fun : u₁.toFun = (affineParH1 hI hfin (-κ) 1 u).toFun := rfl
  have hcoeff : IsParabolicCoeff 1 Lam a (euclideanBall c ρ₁) (Ioc (T₀ - ρ ^ 2) T₀) :=
    PDE.Parabolic.NashLower.isParabolicCoeff_mono ha hsub subset_rfl
  have hsol : IsParabolicWeakSolution a (euclideanBall c ρ₁) (Ioc (T₀ - ρ ^ 2) T₀) u₁ :=
    PDE.Parabolic.NashLower.isParabolicWeakSolution_restrict hsub subset_rfl hu'
  have hae2' : ∀ᵐ z ∂(volume.restrict (euclideanBall c ρ₁ ×ˢ Ioc (T₀ - ρ₁ ^ 2) T₀)),
      |(affineParH1 hI hfin (-κ) 1 u).toFun z| ≤ Kbd.toReal := by
    rw [← PDE.Parabolic.LocalMax.restrict_prod_Ioo_eq]
    refine ae_restrict_of_ae_restrict_of_subset ?_ hae2
    refine prod_mono subset_rfl (Ioo_subset_Ioo_left ?_)
    have : ρ₁ ^ 2 ≤ ρ ^ 2 * (11 / 16) := by rw [hρ₁]; nlinarith [sq_nonneg ρ]
    linarith
  have hbd₁ : ∀ᵐ z ∂(volume.restrict (euclideanBall c ρ₁ ×ˢ Ioc (T₀ - ρ₁ ^ 2) T₀)),
      -Kbd.toReal ≤ u₁.toFun z ∧ u₁.toFun z ≤ Kbd.toReal := by
    filter_upwards [hae2'] with z hz
    have h := abs_le.mp hz
    rw [hu₁fun]
    exact h
  have hKnn : 0 ≤ Kbd.toReal := ENNReal.toReal_nonneg
  obtain ⟨m'', M'', hae3, hosc⟩ := hhol a c T₀ ρ₁ hρ₁0 hI hIsub hcoeff u₁ hsol
    (-Kbd.toReal) Kbd.toReal (by linarith) hbd₁ (8 / 3 * θ) (by positivity)
    (by linarith)
  have e : 8 / 3 * θ * ρ₁ = θ * ρ := by rw [hρ₁]; ring
  rw [e] at hae3
  refine ⟨m'' + κ, M'' + κ, ?_, ?_⟩
  · filter_upwards [hae3] with z hz
    have h1 : m'' ≤ -κ + 1 * u.toFun z := hz.1
    have h2 : -κ + 1 * u.toFun z ≤ M'' := hz.2
    constructor <;> linarith
  · -- numerics
    have hW0 : 0 ≤ ((k * Wint) ^ (2 : ℝ)⁻¹).toReal := ENNReal.toReal_nonneg
    have hS : Kbd.toReal = C₁ * ((k * Wint) ^ (2 : ℝ)⁻¹).toReal := by
      rw [hKbd, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC₁.le]
    have hθα : 0 ≤ θ ^ α := Real.rpow_nonneg hθ.le _
    have hmulα : (8 / 3 * θ) ^ α ≤ 8 / 3 * θ ^ α := by
      rw [Real.mul_rpow (by norm_num) hθ.le]
      refine mul_le_mul_of_nonneg_right ?_ hθα
      calc (8 / 3 : ℝ) ^ α ≤ (8 / 3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
        _ = 8 / 3 := Real.rpow_one _
    have hc1 : 0 ≤ C₂ := by linarith
    calc M'' + κ - (m'' + κ) = M'' - m'' := by ring
      _ ≤ C₂ * (8 / 3 * θ) ^ α * (Kbd.toReal - -Kbd.toReal) := hosc
      _ ≤ C₂ * (8 / 3 * θ ^ α) * (Kbd.toReal - -Kbd.toReal) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmulα hc1) ?_
          linarith
      _ = (C₂ * (16 / 3) * C₁) * θ ^ α * ((k * Wint) ^ (2 : ℝ)⁻¹).toReal := by
          rw [hS]; ring
      _ ≤ max 1 (C₂ * (16 / 3) * C₁) * θ ^ α * ((k * Wint) ^ (2 : ℝ)⁻¹).toReal := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hθα) hW0

end EinsteinFull.ParabolicBridge
