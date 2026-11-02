import EinsteinFull.Calculus.C13TubeNativeC2Energy

open EinsteinRelation PDE MeasureTheory Filter Set EinsteinFull.External.Source.GMP
open PDE.Parabolic.LocalMax
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The symmetric signed truncated power has the actual continuous cutoff energy identity. -/
theorem c5_signed_truncated_C2_continuous_energy_of_eq {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (F : ℝ → ℝ)
    (hF_eq : F = fun s => PDE.Parabolic.LocalMax.powF p ε (n:ℝ) s + PDE.Parabolic.LocalMax.powF p ε (n:ℝ) (-s) - 2*PDE.Parabolic.LocalMax.powF p ε (n:ℝ) 0)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * deriv (deriv F) (u (r,x)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j))) := by
  subst F
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hF : ContDiff ℝ 2 (fun s => f s + f (-s) - 2 * f 0) := by
    change ContDiff ℝ 2 (fun s => f s + f (-s) - 2 * f 0)
    exact (hf.add (hf.comp contDiff_neg)).sub contDiff_const
  have hF0 : (fun s => f s + f (-s) - 2 * f 0) 0 = 0 := by simp only [neg_zero]; ring
  obtain ⟨C, hC⟩ := exists_powF2_bound (p := p) (by linarith : 1 < p) hε (Nat.cast_nonneg n)
  have hd : ∀ s, deriv (deriv (fun s => f s + f (-s) - 2 * f 0)) s = deriv (deriv f) s + deriv (deriv f) (-s) := by
    intro s
    have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hdf : Differentiable ℝ (deriv f) :=
      (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
    have hfirst : deriv (fun x => f x + f (-x) - 2 * f 0) =
        (fun x => deriv f x - deriv f (-x)) := by
      funext x
      change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) x = _
      rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
        (differentiableAt_const _), deriv_add hf'.differentiableAt
        (hf'.comp differentiable_neg).differentiableAt]
      change deriv f x + deriv (fun y => f (-y)) x - deriv (fun _ => 2 * f 0) x = _
      rw [deriv_comp_neg, deriv_const]
      ring
    rw [hfirst]
    change deriv (deriv f - (deriv f ∘ Neg.neg)) s = _
    rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
    change deriv (deriv f) s - deriv (fun x => deriv f (-x)) s = _
    rw [deriv_comp_neg, sub_neg_eq_add]
  apply c13_actual_weighted_C2_continuous_energy hκ hR hab ρ α hell u G hcal _ hF hF0
    (2 * (C : ℝ)) (by positivity) ?_ χ hχ hχc hχU
  intro s
  rw [hd]
  calc
    |deriv (deriv f) s + deriv (deriv f) (-s)| ≤
        |deriv (deriv f) s| + |deriv (deriv f) (-s)| := abs_add_le _ _
    _ ≤ 2 * (C : ℝ) := by have h₁ := hC s; have h₂ := hC (-s); dsimp [f]; linarith

/-- The continuous energy identity for the canonical symmetric truncated power. -/
theorem c5_signed_truncated_C2_continuous_energy {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (χ : EinsteinRelation.Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R) :
    let F := fun s => powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s) -
      2 * powF p ε (n : ℝ) 0
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * F (u (t,x))) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -(∫ r in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * deriv (deriv F) (u (r,x)) *
            dot ((α x).mulVec (G (r,x))) (G (r,x)) +
          2 * χ x * deriv F (u (r,x)) * dot ((α x).mulVec (G (r,x)))
            (fun j => fderiv ℝ χ x (unitVector j))) := by
  exact c5_signed_truncated_C2_continuous_energy_of_eq hκ hR hab ρ α hell u G hcal
    p ε hp hε n _ rfl χ hχ hχc hχU

end EinsteinFull.Calculus
