import EinsteinRelation.Correctors.HeatGradientConvolution
import EinsteinRelation.Correctors.HeatSelectedSkewGaugeUniqueness
import EinsteinRelation.Correctors.AKMHeatSelectionTranslation
import EinsteinRelation.Correctors.P53SourceSkewHeatTruncationSwap
import EinsteinRelation.Correctors.P53SourceSkewHeatSelectionCyclic

/-!
# Algebra of the heat-selected flux-corrector gradient

Source: `paper/main.tex:740-756`, AKM (6.7). The literal truncations of the heat
formula determine their local `L²` limit uniquely. They are antisymmetric in
row and column, and their cyclic sums vanish, so the selected gradient is the
gradient of a closed skew-symmetric two-form.
-/

open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

private theorem iUnion_ball_nat_eq_univ {d : ℕ} :
    (⋃ R : ℕ, ball (0 : Vec d) ((R : ℝ) + 1)) = Set.univ := by
  apply Set.iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
  refine ⟨N, ?_⟩
  change euclideanNorm (x - 0) < (N : ℝ) + 1
  rw [sub_zero]
  linarith

/-- An almost-everywhere statement on every integer origin ball holds almost
everywhere. -/
theorem ae_of_ae_restrict_ball_nat {d : ℕ} {P : Vec d → Prop}
    (h : ∀ R : ℕ, ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ((R : ℝ) + 1))), P x) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), P x := by
  have hu := (ae_restrict_iUnion_iff _ _).mpr h
  rwa [iUnion_ball_nat_eq_univ, Measure.restrict_univ] at hu

/-- Two gradients selected by the same literal heat formula agree almost everywhere. -/
theorem isHeatSelectedFluxGradient_ae_eq {d : ℕ} {g : Vec d → Vec d}
    {G G' : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (h' : IsHeatSelectedFluxGradient g G')
    (j k l : Fin d) :
    (fun x => G j k x l) =ᵐ[volume] (fun x => G' j k x l) := by
  apply ae_of_ae_restrict_ball_nat
  intro R
  obtain ⟨-, hT, hG, hlim⟩ := h j k l R
  obtain ⟨-, -, hG', hlim'⟩ := h' j k l R
  exact ae_eq_of_common_L2_limit _
    (fun n x => iteratedAKMHeatGradientTruncation g n.1 n.2 j k l x) _ _
    (fun n => hT n.1 n.2) hG hG' hlim hlim'

/-- Heat selection is covariant: the gradient selected for a translated source is
the translate of the selected gradient. -/
theorem isHeatSelectedFluxGradient_ae_translate_eq {d : ℕ} {g : Vec d → Vec d}
    {G G' : Fin d → Fin d → Vec d → Vec d}
    (h : IsHeatSelectedFluxGradient g G) (z : Vec d)
    (h' : IsHeatSelectedFluxGradient (fun x => g (x + z)) G') (j k l : Fin d) :
    (fun x => G' j k x l) =ᵐ[volume] (fun x => G j k (x + z) l) :=
  isHeatSelectedFluxGradient_ae_eq h' (isHeatSelectedFluxGradient_translate h z) j k l

/-- Changing the selected gradient on a null set preserves every clause of the
heat selection. -/
theorem isHeatSelectedFluxGradient_congr_ae {d : ℕ} {g : Vec d → Vec d}
    {G G' : Fin d → Fin d → Vec d → Vec d}
    (hG : IsHeatSelectedFluxGradient g G)
    (heq : ∀ j k l : Fin d, (fun x => G j k x l) =ᵐ[volume] (fun x => G' j k x l)) :
    IsHeatSelectedFluxGradient g G' := by
  intro j k ℓ R
  let μ : Measure (Vec d) := volume.restrict (ball 0 (R + 1))
  have hG_jkℓ := hG j k ℓ R
  rcases hG_jkℓ with ⟨h_int, h_memlp_iter, h_memlp_G, h_tendsto⟩
  have h_restrict_ae : (fun x => G j k x ℓ) =ᵐ[μ] (fun x => G' j k x ℓ) :=
    ae_mono (Measure.restrict_le_self (μ := volume)) (heq j k ℓ)
  refine ⟨h_int, h_memlp_iter, MemLp.ae_eq h_restrict_ae h_memlp_G, ?_⟩
  have h_ae_eq (mn : ℕ × ℕ) :
      (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k ℓ x - G j k x ℓ) =ᵐ[μ]
      (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k ℓ x - G' j k x ℓ) := by
    filter_upwards [h_restrict_ae] with x hx
    simp [hx]
  refine h_tendsto.congr (fun mn => ?_)
  exact eLpNorm_congr_ae (h_ae_eq mn)

/-- The Euclidean norm is at most `√d` times the sup norm of `Vec d`. -/
theorem euclideanNorm_le_sqrt_mul_norm {d : ℕ} (x : Vec d) :
    euclideanNorm x ≤ Real.sqrt d * ‖x‖ := by
  have hsq : euclideanSq x ≤ d * ‖x‖ ^ 2 := by
    unfold euclideanSq dot
    calc (∑ i, x i * x i) ≤ ∑ _i : Fin d, ‖x‖ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := norm_le_pi_norm x i
          rw [Real.norm_eq_abs] at h
          nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
      _ = d * ‖x‖ ^ 2 := by simp
  unfold euclideanNorm
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (Nat.cast_nonneg d)]
  exact Real.sqrt_le_sqrt hsq

/-- Every coordinate cube lies in an integer Euclidean origin ball. -/
theorem exists_nat_cube_subset_ball {d : ℕ} (r : ℝ) :
    ∃ N : ℕ, Metric.ball (0 : Vec d) r ⊆ ball 0 ((N : ℝ) + 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.sqrt d * r)
  refine ⟨N, fun x hx => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hx
  change euclideanNorm (x - 0) < (N : ℝ) + 1
  rw [sub_zero]
  calc euclideanNorm x ≤ Real.sqrt d * ‖x‖ := euclideanNorm_le_sqrt_mul_norm x
    _ ≤ Real.sqrt d * r := mul_le_mul_of_nonneg_left hx.le (Real.sqrt_nonneg _)
    _ < (N : ℝ) + 1 := by linarith

/-- Heat selection on all Euclidean origin balls implies the iterated source
selection on all coordinate cubes. -/
theorem isIteratedAKMHeatGradientAt_of_isHeatSelectedFluxGradient {d : ℕ}
    (g : Vec d → Vec d) (ω : FieldPair d)
    (F : FieldPair d → Fin d → Fin d → Fin d → ℝ)
    (h : IsHeatSelectedFluxGradient g (fun j k x l => F (translate x ω) j k l)) :
    IsIteratedAKMHeatGradientAt g ω F := by
  intro j k l R
  obtain ⟨N, hsub⟩ := exists_nat_cube_subset_ball (d := d) ((R + 1 : ℕ) : ℝ)
  have hm := Measure.restrict_mono_set (volume : Measure (Vec d)) hsub
  obtain ⟨hi, hT, hG, hlim⟩ := h j k l N
  refine ⟨fun m n => ae_mono hm (hi m n), fun m n => (hT m n).mono_measure hm,
    hG.mono_measure hm, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun _ => eLpNorm_mono_measure _ hm)

/-- The selected gradient is almost everywhere antisymmetric in row and column. -/
theorem isHeatSelectedFluxGradient_ae_swap {d : ℕ} {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G)
    (j k l : Fin d) :
    (fun x => G k j x l) =ᵐ[volume] (fun x => -G j k x l) :=
  isHeatSelectedFluxGradient_ae_eq h (isHeatSelectedFluxGradient_swap h) k j l

end EinsteinRelation.Correctors
