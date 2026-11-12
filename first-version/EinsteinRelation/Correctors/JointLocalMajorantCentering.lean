import EinsteinRelation.Correctors.ScalarLocalMajorantCentering
import EinsteinRelation.Correctors.TensorLocalMajorantCentering
import EinsteinRelation.Correctors.JointMajorantMoments
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Source: `paper/main.tex:727-745`. Joint local PDE bounds and measurable
L² majorants give both large-ball centered moments in their original gauges. -/
theorem joint_centered_moments_of_local_L2_majorants
    (d : ℕ) (hd : 0 < d) (p C : ℝ) (hp : 2 ≤ p) (hC : 0 < C) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (f u : Ω → Vec d → ℝ) (S : Ω → Vec d → Mat d)
      (c a : Ω → ℝ) (b : Ω → Mat d)
      (hfm : Measurable (Function.uncurry f))
      (hSm : Measurable (Function.uncurry S)) (hbm : Measurable b)
      (z : Vec d) (R B : ℝ) (hR : 0 < R),
      (∀ᵐ ω ∂P, Integrable (f ω) (volume.restrict (ball z R)) ∧
        ∀ j k, Integrable (fun x => S ω x j k) (volume.restrict (ball z R))) →
      (∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure (Vec d)), f ω x = u ω x + a ω) →
      (∀ᵐ ω ∂P, ∀ x : Vec d,
        ∀ᵐ y ∂volume.restrict (ball x (1 / 4)),
          |u ω y - c ω| ≤ C * (1 +
            Real.sqrt (∫ t in ball x 4, |u ω t - c ω| ^ 2 ∂volume) +
            Real.sqrt (∫ t in ball x 4, frobeniusNorm (S ω t - b ω) ^ 2 ∂volume)) ∧
          frobeniusNorm (S ω y - b ω) ≤ C * (1 +
            Real.sqrt (∫ t in ball x 4, |u ω t - c ω| ^ 2 ∂volume) +
            Real.sqrt (∫ t in ball x 4, frobeniusNorm (S ω t - b ω) ^ 2 ∂volume))) →
      (∀ x ∈ ball z R, ∃ U V : Ω → ℝ,
        AEMeasurable U P ∧ AEMeasurable V P ∧ (∀ ω, 0 ≤ U ω) ∧ (∀ ω, 0 ≤ V ω) ∧
        (∀ᵐ ω ∂P,
          Real.sqrt (∫ t in ball x 4, |u ω t - c ω| ^ 2 ∂volume) ≤ U ω ∧
          Real.sqrt (∫ t in ball x 4, frobeniusNorm (S ω t - b ω) ^ 2 ∂volume) ≤ V ω) ∧
        (∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂P) ≤ ENNReal.ofReal B ∧
        (∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂P) ≤ ENNReal.ofReal B) →
      ((∫⁻ ω, ⨍⁻ x in ball z R, ENNReal.ofReal
        (|f ω x - ⨍ y in ball z R, f ω y ∂volume| ^ p) ∂volume ∂P) ≤
          ENNReal.ofReal (A * (max B 0 + 1))) ∧
      ((∫⁻ ω, ⨍⁻ x in ball z R, ENNReal.ofReal (frobeniusNorm
        (S ω x - Matrix.of (fun j k => ⨍ y in ball z R, S ω y j k ∂volume)) ^ p) ∂volume ∂P) ≤
          ENNReal.ofReal (A * (max B 0 + 1))) := by
  obtain ⟨A₁, hA₁, hscalar⟩ := centered_scalar_moment_of_local_measurable_majorants d p (by linarith)
  obtain ⟨A₂, hA₂, htensor⟩ := centered_tensor_moment_of_local_measurable_majorants d hd p hp
  let K := 2 ^ p * C ^ p * (2 ^ p * 2 + 1)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨(A₁ + A₂ + 1) * K, by positivity, ?_⟩
  intro Ω _ P _ f u S c a b hfm hSm hbm z R B hR hint hgauge hvalue hlocal
  let D := 2 ^ p * C ^ p * (2 ^ p * (max B 0 + max B 0) + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hDK : D ≤ K * (max B 0 + 1) := by
    have hin : 2 ^ p * (max B 0 + max B 0) + 1 ≤
        (2 ^ p * 2 + 1) * (max B 0 + 1) := by
      nlinarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) p, le_max_right B 0]
    calc
      D ≤ (2 ^ p * C ^ p) * ((2 ^ p * 2 + 1) * (max B 0 + 1)) :=
        mul_le_mul_of_nonneg_left hin (by positivity)
      _ = K * (max B 0 + 1) := by dsimp [K]; ring
  have hpoint : ∀ x ∈ ball z R, ∃ M : Ω → ℝ,
      AEMeasurable M P ∧ (∀ ω, 0 ≤ M ω) ∧
      (∫⁻ ω, ENNReal.ofReal (M ω ^ p) ∂P) ≤ ENNReal.ofReal D ∧
      ∀ᵐ ω ∂P, ∀ᵐ y ∂volume.restrict (ball x (1 / 4)),
        |u ω y - c ω| ≤ M ω ∧ frobeniusNorm (S ω y - b ω) ≤ M ω := by
    intro x hx
    obtain ⟨U, V, hU, hV, hU0, hV0, hUV, hUB, hVB⟩ := hlocal x hx
    let M := fun ω => C * (1 + U ω + V ω)
    refine ⟨M, aemeasurable_const.mul ((aemeasurable_const.add hU).add hV),
      (fun ω => mul_nonneg hC.le (by linarith [hU0 ω, hV0 ω])), ?_, ?_⟩
    · exact lintegral_one_add_two_majorants_rpow_le P U V C p B B hC.le
        (by linarith) hU0 hV0 hU hV hUB hVB
    · filter_upwards [hUV, hvalue] with ω hω hv
      have hbnd : C * (1 + Real.sqrt (∫ t in ball x 4, |u ω t - c ω| ^ 2 ∂volume) +
          Real.sqrt (∫ t in ball x 4, frobeniusNorm (S ω t - b ω) ^ 2 ∂volume)) ≤ M ω :=
        mul_le_mul_of_nonneg_left (by linarith [hω.1, hω.2]) hC.le
      exact (hv x).mono fun y hy => ⟨hy.1.trans hbnd, hy.2.trans hbnd⟩
  have hs := hscalar P f u c a hfm z R hR D (hint.mono fun _ h => h.1) hgauge
    (fun x hx => by
      obtain ⟨M, hm, hm0, hmB, hmb⟩ := hpoint x hx
      exact ⟨M, hm, hm0, hmB, hmb.mono fun _ h => h.mono fun _ h => h.1⟩)
  have ht := htensor P S b hSm hbm z R hR D (hint.mono fun _ h => h.2)
    (fun x hx => by
      obtain ⟨M, hm, hm0, hmB, hmb⟩ := hpoint x hx
      exact ⟨M, hm, hm0, hmB, hmb.mono fun _ h => h.mono fun _ h => h.2⟩)
  rw [max_eq_left hD] at hs ht
  constructor
  · apply hs.trans
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hDK hA₁.le).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A₁ ≤ A₁ + A₂ + 1) hK.le) (by positivity))
  · apply ht.trans
    apply ENNReal.ofReal_le_ofReal
    exact (mul_le_mul_of_nonneg_left hDK hA₂.le).trans (by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A₂ ≤ A₁ + A₂ + 1) hK.le) (by positivity))
end EinsteinRelation.Correctors
