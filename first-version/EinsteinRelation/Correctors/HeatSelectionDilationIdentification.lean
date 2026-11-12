import EinsteinRelation.Correctors.SpatialLocalL2LimitDilation
import EinsteinRelation.Correctors.StationaryHeatSelectionRescaling
import EinsteinRelation.Correctors.AKMHeatTimeDilation
import EinsteinRelation.Correctors.HeatSelectedSkewGaugeUniqueness

/-! Source: `paper/main.tex:722,756`. Actual independent heat limits
identify the selected gradient after physical space dilation. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The heat formula identifies a dilated selected gradient from its
rescaled local L² limits. Uniqueness is proved from the common integrals. -/
theorem ae_eq_of_heat_selection_dilation {d : ℕ}
    (g : Vec d → Vec d) (G H : Fin d → Fin d → Vec d → Vec d)
    (hG : IsHeatSelectedFluxGradient g G) (r b : ℝ) (hr : 0 < r)
    (hrescale : ∀ (j k l : Fin d) (R : ℕ),
      (∀ m n, MemLp (rescaledAKMHeatGradientTruncation g (r ^ 2)⁻¹ m n j k l)
        2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
      Tendsto (fun mn : ℕ × ℕ => eLpNorm
        (fun x => rescaledAKMHeatGradientTruncation g (r ^ 2)⁻¹ mn.1 mn.2 j k l x -
          G j k x l) 2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0))
    (hH : IsHeatSelectedFluxGradient (fun x => b • g (r⁻¹ • x)) H) :
    ∀ j k, H j k =ᵐ[volume] (fun x => b • G j k (r⁻¹ • x)) := by
  have hcover : (⋃ R : ℕ, ball (0 : Vec d) ((R : ℝ) + 1)) = Set.univ := by
    apply Set.iUnion_eq_univ_iff.mpr
    intro x
    obtain ⟨N, hN⟩ := exists_nat_gt (euclideanNorm x)
    refine ⟨N, ?_⟩
    change euclideanNorm (x - 0) < (N : ℝ) + 1
    simpa only [sub_zero] using (lt_trans hN (lt_add_one (N : ℝ)))
  intro j k
  have heq (l : Fin d) : (fun x => H j k x l) =ᵐ[volume]
      (fun x => (b • G j k (r⁻¹ • x)) l) := by
    let f : ℕ × ℕ → Vec d → ℝ := fun mn x =>
      rescaledAKMHeatGradientTruncation g (r ^ 2)⁻¹ mn.1 mn.2 j k l x - G j k x l
    have herr := local_L2_zero_dilation f
      (fun R mn => ((hrescale j k l R).1 mn.1 mn.2).sub (hG j k l R).2.2.1)
      (fun R => (hrescale j k l R).2) r⁻¹ b (inv_pos.mpr hr)
    have htrunc (m n : ℕ) (x : Vec d) :
        iteratedAKMHeatGradientTruncation (fun y => b • g (r⁻¹ • y)) m n j k l x =
          b * rescaledAKMHeatGradientTruncation g (r ^ 2)⁻¹ m n j k l (r⁻¹ • x) := by
      have h := iteratedAKMHeatGradientTruncation_dilation g r b hr m n j k l (r⁻¹ • x)
      simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul,
        rescaledAKMHeatGradientTruncation, div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h
    have hfun (mn : ℕ × ℕ) :
        (fun x => iteratedAKMHeatGradientTruncation (fun y => b • g (r⁻¹ • y))
          mn.1 mn.2 j k l x - (b • G j k (r⁻¹ • x)) l) =
        (fun x => b * f mn (r⁻¹ • x)) := by
      funext x
      simp only [htrunc, Pi.smul_apply, smul_eq_mul, f, mul_sub]
    have hlocal (R : ℕ) : (fun x => H j k x l) =ᵐ[volume.restrict (ball 0 ((R : ℝ) + 1))]
        (fun x => (b • G j k (r⁻¹ • x)) l) := by
      have hsrc := hH j k l R
      have herror (mn : ℕ × ℕ) : MemLp
          (fun x => iteratedAKMHeatGradientTruncation (fun y => b • g (r⁻¹ • y))
            mn.1 mn.2 j k l x - (b • G j k (r⁻¹ • x)) l)
          2 (volume.restrict (ball 0 ((R : ℝ) + 1))) := by
        rw [hfun]
        exact (herr R).1 mn
      have htarget : MemLp (fun x => (b • G j k (r⁻¹ • x)) l)
          2 (volume.restrict (ball 0 ((R : ℝ) + 1))) := by
        apply ((hsrc.2.1 0 0).sub (herror (0, 0))).ae_eq
        exact ae_of_all _ (fun x => by simp only [Pi.sub_apply]; ring)
      apply ae_eq_of_common_L2_limit _
        (fun mn x => iteratedAKMHeatGradientTruncation
          (fun y => b • g (r⁻¹ • y)) mn.1 mn.2 j k l x) _ _
        (fun mn => hsrc.2.1 mn.1 mn.2) hsrc.2.2.1 htarget hsrc.2.2.2
      change Tendsto (fun mn : ℕ × ℕ => eLpNorm
        (fun x => iteratedAKMHeatGradientTruncation (fun y => b • g (r⁻¹ • y))
          mn.1 mn.2 j k l x - (b • G j k (r⁻¹ • x)) l)
          2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0)
      simpa only [hfun] using (herr R).2
    have h := (ae_restrict_iUnion_iff _ _).mpr hlocal
    simpa only [hcover, Measure.restrict_univ] using h
  filter_upwards [ae_all_iff.mpr heq] with x hx
  exact funext hx

end EinsteinRelation.Correctors
