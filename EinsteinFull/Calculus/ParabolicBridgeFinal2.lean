import EinsteinFull.Calculus.ParabolicBridgeFinal

/-!
# The interior Hölder decay for almost-everywhere defined data
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

theorem avg_osc_congr {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (h : f =ᵐ[μ] g) :
    ⨍ z, |f z - ⨍ w, f w ∂μ| ^ 2 ∂μ = ⨍ z, |g z - ⨍ w, g w ∂μ| ^ 2 ∂μ := by
  have hi : ⨍ w, f w ∂μ = ⨍ w, g w ∂μ := average_congr h
  rw [hi]
  exact average_congr (h.mono fun z hz => by simp only [hz])

theorem holder_interior_ae (d : ℕ) (hd : 0 < d) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ α₀ C : ℝ, 0 < α₀ ∧ α₀ < 1 ∧ 1 ≤ C ∧
    ∀ (ω1 : Vec d → Mat d), (∀ j k, Measurable fun y => ω1 y j k) →
      (∀ y, (ω1 y).transpose = ω1 y ∧
        (∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul (ω1 y) ξ)) ∧
        (∀ ξ : Vec d, vecDot ξ (matVecMul (ω1 y) ξ) ≤ Λ * vecNormSq ξ)) →
    ∀ (τ : ℝ) (x : Vec d) (r : ℝ), 0 < r →
    ∀ (v : ℝ × Vec d → ℝ) (g : Fin d → ℝ × Vec d → ℝ),
      MemLp v 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)) →
      (∀ j, MemLp (g j) 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r))) →
      (∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r → ∀ j : Fin d,
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (0, Pi.single j 1) =
          -∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g j z * φ z) →
      (∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r →
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (1, 0) =
          (1 / 2) * ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
            (∑ k : Fin d, ω1 z.2 j k * g k z) * fderiv ℝ φ z (0, Pi.single j 1)) →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      Real.sqrt (⨍ z in Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r),
          |v z - ⨍ w in Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r), v w| ^ 2) ≤
        C * θ ^ α₀ * Real.sqrt (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r,
          |v z - ⨍ w in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v w| ^ 2) := by
  obtain ⟨α₀, C, hα0, hα1, hC1, hcore⟩ := holder_interior_core d hd Λ hΛ
  refine ⟨α₀, C, hα0, hα1, hC1, ?_⟩
  intro ω1 hmeas hell τ x r hr v g hv hg H1 H2 θ hθ hθ2
  have hvm := hv.aestronglyMeasurable
  have hgm : ∀ j, AEStronglyMeasurable (g j)
      (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)) := fun j =>
    (hg j).aestronglyMeasurable
  set v' : ℝ × Vec d → ℝ := hvm.mk v with hv'
  set g' : Fin d → ℝ × Vec d → ℝ := fun j => (hgm j).mk (g j) with hg'
  have hv'm : Measurable v' := hvm.stronglyMeasurable_mk.measurable
  have hg'm : ∀ j, Measurable (g' j) := fun j => (hgm j).stronglyMeasurable_mk.measurable
  have hvv' : v =ᵐ[volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)] v' :=
    hvm.ae_eq_mk
  have hgg' : ∀ j, g j =ᵐ[volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)] g' j :=
    fun j => (hgm j).ae_eq_mk
  have hgg'all : ∀ᵐ z ∂(volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)),
      ∀ k, g k z = g' k z := ae_all_iff.mpr hgg'
  have hv'2 : MemLp v' 2 (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)) :=
    hv.ae_eq hvv'
  have hg'2 : ∀ j, MemLp (g' j) 2
      (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r)) := fun j => (hg j).ae_eq (hgg' j)
  have H1' : ∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r → ∀ j : Fin d,
      ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v' z * fderiv ℝ φ z (0, Pi.single j 1) =
        -∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g' j z * φ z := by
    intro φ hφ hc hs j
    have e1 : ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r,
        v' z * fderiv ℝ φ z (0, Pi.single j 1) =
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r,
        v z * fderiv ℝ φ z (0, Pi.single j 1) :=
      integral_congr_ae (hvv'.mono fun z hz => by simp only [hz])
    have e2 : ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g' j z * φ z =
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, g j z * φ z :=
      integral_congr_ae ((hgg' j).mono fun z hz => by simp only [hz])
    rw [e1, e2]
    exact H1 φ hφ hc hs j
  have H2' : ∀ φ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r →
      ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v' z * fderiv ℝ φ z (1, 0) =
        (1 / 2) * ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
          (∑ k : Fin d, ω1 z.2 j k * g' k z) * fderiv ℝ φ z (0, Pi.single j 1) := by
    intro φ hφ hc hs
    have e1 : ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v' z * fderiv ℝ φ z (1, 0) =
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, v z * fderiv ℝ φ z (1, 0) :=
      integral_congr_ae (hvv'.mono fun z hz => by simp only [hz])
    have e2 : ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
        (∑ k : Fin d, ω1 z.2 j k * g' k z) * fderiv ℝ φ z (0, Pi.single j 1) =
        ∫ z in Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r, ∑ j : Fin d,
        (∑ k : Fin d, ω1 z.2 j k * g k z) * fderiv ℝ φ z (0, Pi.single j 1) :=
      integral_congr_ae (hgg'all.mono fun z hz => by simp only [hz])
    rw [e1, e2]
    exact H2 φ hφ hc hs
  have hmain := hcore ω1 hmeas hell τ x r hr v' g' hv'm hg'm hv'2 hg'2 H1' H2' θ hθ hθ2
  -- transfer back to `v`
  have hθ1 : θ ≤ 1 := by linarith
  have hθr0 : 0 < θ * r := mul_pos hθ hr
  have hθr : θ * r ≤ r := by nlinarith
  have hEsub : Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r) ⊆
      Ioo (τ - r ^ 2) τ ×ˢ euclideanBall x r := by
    refine Set.prod_mono (Set.Ioo_subset_Ioo_left ?_) (euclideanBall_mono hθr0.le hθr)
    have : (θ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hθr0.le hθr 2
    linarith
  have hvvE : v =ᵐ[volume.restrict (Ioo (τ - (θ * r) ^ 2) τ ×ˢ euclideanBall x (θ * r))] v' :=
    ae_restrict_of_ae_restrict_of_subset hEsub hvv'
  have eE := avg_osc_congr hvvE
  have eS := avg_osc_congr hvv'
  rw [eE, eS]
  exact hmain

end EinsteinFull.ParabolicBridge
