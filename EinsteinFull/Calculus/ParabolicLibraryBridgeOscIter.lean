import EinsteinFull.Calculus.ParabolicLibraryBridgeOscScaled
import EllipticRegularity.Parabolic.NashLower.Restrict

/-!
# Geometric decay of the oscillation on shrinking parabolic cylinders
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter PDE

/-- Iteration of the oscillation reduction: after `k` halvings the oscillation is at most
`(1 - η)^k (M - m)`. -/
theorem osc_decay_iter (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 2 ∧ ∀ (a : ParCoeffField d) (c : Vec d) (T₀ ρ : ℝ), 0 < ρ →
      ∀ {I' : Set ℝ}, MeasurableSet I' → Ioc (T₀ - ρ ^ 2) T₀ ⊆ I' →
      IsParabolicCoeff 1 Lam a (euclideanBall c ρ) I' →
      ∀ u : ParH1Function (euclideanBall c ρ) I',
      IsParabolicWeakSolution a (euclideanBall c ρ) I' u →
      ∀ m M : ℝ, m ≤ M →
      (∀ᵐ z ∂(volume.restrict (euclideanBall c ρ ×ˢ Ioc (T₀ - ρ ^ 2) T₀)),
        m ≤ u.toFun z ∧ u.toFun z ≤ M) →
      ∀ k : ℕ, ∃ m' M' : ℝ,
        (∀ᵐ z ∂(volume.restrict
          (euclideanBall c (ρ / 2 ^ k) ×ˢ Ioc (T₀ - (ρ / 2 ^ k) ^ 2) T₀)),
          m' ≤ u.toFun z ∧ u.toFun z ≤ M') ∧ m ≤ m' ∧ M' ≤ M ∧ m' ≤ M' ∧
          M' - m' ≤ (1 - η) ^ k * (M - m) := by
  obtain ⟨η, hη, hη2, hred⟩ := osc_reduction_scaled d hd Lam hLam
  refine ⟨η, hη, hη2, ?_⟩
  intro a c T₀ ρ hρ I' hI'meas hI' ha u hu m M hmM hbd k
  induction k with
  | zero =>
    refine ⟨m, M, ?_, le_rfl, le_rfl, hmM, by simp⟩
    simpa using hbd
  | succ k ih =>
    obtain ⟨mk, Mk, hk, h1, h2, h3, h4⟩ := ih
    have hrk : 0 < ρ / 2 ^ k := by positivity
    have hsub : euclideanBall c (ρ / 2 ^ k) ⊆ euclideanBall c ρ :=
      euclideanBall_mono hrk.le (div_le_self hρ.le (one_le_pow₀ (by norm_num)))
    have hIk : Ioc (T₀ - (ρ / 2 ^ k) ^ 2) T₀ ⊆ I' := by
      refine Subset.trans (Ioc_subset_Ioc_left ?_) hI'
      have : (ρ / 2 ^ k) ^ 2 ≤ ρ ^ 2 :=
        pow_le_pow_left₀ hrk.le (div_le_self hρ.le (one_le_pow₀ (by norm_num))) 2
      linarith
    let uk := PDE.Parabolic.NashLower.restrictParH1 (J := I') hsub subset_rfl u
    have hukfun : uk.toFun = u.toFun := rfl
    have hak : IsParabolicCoeff 1 Lam a (euclideanBall c (ρ / 2 ^ k)) I' :=
      PDE.Parabolic.NashLower.isParabolicCoeff_mono ha hsub subset_rfl
    have huk : IsParabolicWeakSolution a (euclideanBall c (ρ / 2 ^ k)) I' uk :=
      PDE.Parabolic.NashLower.isParabolicWeakSolution_restrict hsub subset_rfl hu
    have hbdk : ∀ᵐ z ∂(volume.restrict
        (euclideanBall c (ρ / 2 ^ k) ×ˢ Ioc (T₀ - (ρ / 2 ^ k) ^ 2) T₀)),
        mk ≤ uk.toFun z ∧ uk.toFun z ≤ Mk := by
      rw [hukfun]
      exact hk
    obtain ⟨m', M', hae, g1, g2, g3, g4⟩ := hred a c T₀ (ρ / 2 ^ k) hrk hI'meas hIk hak uk huk
      mk Mk h3 hbdk
    have e : ρ / 2 ^ (k + 1) = ρ / 2 ^ k / 2 := by
      rw [pow_succ]
      field_simp
    refine ⟨m', M', ?_, h1.trans g1, g2.trans h2, g3, ?_⟩
    · rw [e]
      rw [hukfun] at hae
      exact hae
    · calc M' - m' ≤ (1 - η) * (Mk - mk) := g4
        _ ≤ (1 - η) * ((1 - η) ^ k * (M - m)) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
        _ = (1 - η) ^ (k + 1) * (M - m) := by ring

end EinsteinFull.ParabolicBridge
