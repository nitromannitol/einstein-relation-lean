import EinsteinFull.Calculus.C3FluxNormalizedSiteCutoffs
import EinsteinFull.Calculus.C3FluxGaussianSiteBounds

open scoped BigOperators
namespace EinsteinFull.Blueprint
open EinsteinRelation

theorem c6_actual_schwartz_recovery_admissible_partitions
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (ctest : ℝ) (hctest : 0 < ctest) (Btest : ℕ → ℝ)
    (hBtest : ∀ q, 0 < Btest q) :
    ∃ Crec Csite : ℝ, 1 ≤ Crec ∧ 0 < Csite ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i j : Fin d)
        (s r : ℝ) (hs : 0 < s) (hr : 0 < r) (k : ℕ)
        (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ →
      ∀ z : Vec d,
      let R := 2 * Real.sqrt (d : ℝ) + 2
      let W := s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
          {y : Vec d | euclideanNorm (y - z) ≤ R * r})
      let A := Csite
      let B := Csite * (R + r * (Real.sqrt s)⁻¹)
      let f := fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))
      let g := fun x : Vec d => f x / (W : ℂ)
      let s := r ^ 2
      let v := r • unitVector j
      let slope := fun w : Vec d => ((((homogenizedCoefficient Q)⁻¹).mulVec w j / s : ℝ) : ℂ)
      let h := fun w : Vec d => g (w + v) /
        (slope v * homogenizedGaussianKernel Q i s (sq_pos_of_pos hr) 0 (-(w + v)))
      let δ : Bool → Vec d → ℂ := fun b w => if b then
        slope w * h w - slope (w - v) * h (w - v) else h w - h (w - v)
      let M : Bool → ℝ := fun b => 2 * Crec * (1 + A + B) * (if b then r ^ d else r ^ (d + 1))
      let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
        (fluxPartitionCutoff r w + fluxPartitionCutoff r (w - v)) / 2 +
          (if q then (δ b w).im else (δ b w).re) / M b
      ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
        Function.support (θ b q) ⊆ {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
        (∀ w, |θ b q w| ≤ 1) ∧
        (∀ w, Real.sqrt (∑ k : Fin d, (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤
          (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
        ∀ y, HasSum (fun z : Fin d → ℤ => θ b q (y - fun k => r * (z k : ℝ))) 1 := by
  obtain ⟨Crec, hCrec, hpart⟩ := c3_weighted_recovery_admissible_partitions_split d hd D
  obtain ⟨Csite, hCsite, hsite⟩ := c3_gaussian_site_recovery_bounds d ctest hctest Btest hBtest
  refine ⟨Crec, Csite, hCrec, hCsite, ?_⟩
  intro Q i j s r hs hr k ψ hψ z
  have hbounds := hsite s r hs hr k ψ hψ z
  dsimp only at hbounds
  have hR : 0 ≤ (2 * Real.sqrt (d : ℝ) + 2) * r := by positivity
  have hsup := c1_gaussian_ball_sup s ctest ((2 * Real.sqrt (d : ℝ) + 2) * r) hs hctest hR z
  have hz : z ∈ {y : Vec d | euclideanNorm (y - z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
    simpa [euclideanNorm, euclideanSq, dot] using hR
  have hW := lt_of_lt_of_le (show 0 < s ^ (-(d : ℝ) / 2) * Real.exp (-ctest * euclideanNorm z ^ 2 / s) by positivity) (hsup.2 z hz)
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))) := by
    exact (Complex.ofRealCLM.contDiff.comp (flux_partition_cutoff_contDiff r)).mul
      ((ψ.smooth (⊤ : ℕ∞)).comp ((contDiff_id.add contDiff_const).neg))
  have hc : HasCompactSupport (fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))) := by
    exact ((flux_partition_cutoff_hasCompactSupport hr).comp_left (g := Complex.ofReal) rfl).mul_right
  have hsupport : Function.support (fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))) ⊆ {x : Vec d | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ)) * r} := by
    intro w hw
    apply flux_partition_cutoff_support_sharp hr
    intro hw0
    apply hw
    simp [hw0]
  have hpow : s ^ (-((k + 1 : ℕ) : ℝ) / 2) =
      s ^ (-(k : ℝ) / 2) * (Real.sqrt s)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le, ← Real.rpow_add hs]
    congr 1
    push_cast
    ring
  have hval (w : Vec d) : ‖(fluxPartitionCutoff r w : ℂ) * ψ (-(w + z))‖ ≤
      Csite * (s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})) := by
    convert hbounds.2.2.1 w using 1 <;> ring
  have hgrad (w : Vec d) :
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun x : Vec d =>
        (fluxPartitionCutoff r x : ℂ) * ψ (-(x + z))) w (unitVector j)‖ ^ 2) ≤
      (Csite * ((2 * Real.sqrt (d : ℝ) + 2) + r * (Real.sqrt s)⁻¹) / r) *
        (s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
          Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
          {y : Vec d | euclideanNorm (y - z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})) := by
    have h := hbounds.2.2.2 w
    rw [hpow] at h
    convert h using 1 <;> ring
  exact hpart Q i j r
    (s ^ (-(k : ℝ) / 2) * sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
      {y : Vec d | euclideanNorm (y - z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r}))
    Csite (Csite * ((2 * Real.sqrt (d : ℝ) + 2) + r * (Real.sqrt s)⁻¹))
    hr (mul_pos (Real.rpow_pos_of_pos hs _) hW) hCsite.le (by positivity)
    (fun w : Vec d => (fluxPartitionCutoff r w : ℂ) * ψ (-(w + z)))
    hf hc hsupport hval hgrad

end EinsteinFull.Blueprint
