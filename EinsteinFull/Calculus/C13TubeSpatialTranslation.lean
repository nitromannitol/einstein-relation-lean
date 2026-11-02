import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinFull.Calculus.C3JointLocalizationSupport

open EinsteinRelation MeasureTheory

namespace EinsteinFull

/-- Translating a centered source ball gives the source ball at the translated center. -/
theorem c13_sourceBall_translate {d : ℕ} (y x : Vec d) (R : ℝ) :
    x + y ∈ External.Source.GMP.sourceBall y R ↔
      x ∈ External.Source.GMP.sourceBall (0 : Vec d) R := by
  simp only [External.Source.GMP.sourceBall, Set.mem_setOf_eq, add_sub_cancel_right,
    sub_zero]

/-- Space translation preserves Lebesgue measure on the corresponding cylinders. -/
theorem c13_cylinder_translation_measurePreserving {d : ℕ} (y : Vec d)
    (R : ℝ) (I : Set ℝ) :
    MeasurePreserving (fun z : ℝ × Vec d => (z.1, z.2 + y))
      (volume.restrict (I ×ˢ External.Source.GMP.sourceBall (0 : Vec d) R))
      (volume.restrict (I ×ˢ External.Source.GMP.sourceBall y R)) := by
  let a : ℝ × Vec d := (0, y)
  have hp : MeasurePreserving (fun z : ℝ × Vec d => z + a)
      (volume : Measure (ℝ × Vec d)) volume := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    have he : (fun z : ℝ × Vec d => z + a) = Prod.map id (fun x : Vec d => x + y) := by
      funext z
      rcases z with ⟨t, x⟩
      simp [a]
    rw [he]
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (measurePreserving_add_right (volume : Measure (Vec d)) y)
  have h := hp.restrict_preimage_emb
    (Homeomorph.addRight a).measurableEmbedding (I ×ˢ External.Source.GMP.sourceBall y R)
  have heq : (fun z : ℝ × Vec d => z + a) ⁻¹' (I ×ˢ External.Source.GMP.sourceBall y R) =
      I ×ˢ External.Source.GMP.sourceBall (0 : Vec d) R := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Prod.fst_add, Prod.snd_add, a, add_zero,
      c13_sourceBall_translate]
  rw [heq] at h
  have he : (fun z : ℝ × Vec d => z + a) = (fun z => (z.1, z.2 + y)) := by
    funext z
    rcases z with ⟨t, x⟩
    simp [a]
  rwa [he] at h

/-- Spatial translation preserves the source weighted weak caloric equation. -/
theorem c13_weighted_caloric_spatial_translation {d : ℕ} (y : Vec d) (R : ℝ) (I : Set ℝ)
    (rho : Vec d → ℝ) (alpha : Vec d → Mat d) (u : ℝ × Vec d → ℝ)
    (grad : ℝ × Vec d → Vec d)
    (hu : External.Source.GMP.IsWeightedCaloric rho alpha I
      (External.Source.GMP.sourceBall y R) u grad) :
    External.Source.GMP.IsWeightedCaloric (fun x => rho (x + y)) (fun x => alpha (x + y)) I
      (External.Source.GMP.sourceBall (0 : Vec d) R)
      (fun z => u (z.1, z.2 + y)) (fun z => grad (z.1, z.2 + y)) := by
  rcases hu with ⟨hu, hg, hn, hw, he⟩
  have hm := c13_cylinder_translation_measurePreserving y R I
  refine ⟨hu.comp_measurePreserving hm, hg.comp_measurePreserving hm,
    hn.comp_measurePreserving hm, ?_, ?_⟩
  · filter_upwards [hw] with t ht
    intro i
    have h := EinsteinFull.Blueprint.covariance_hasWeakPartialDerivative_translate
      (z := y) (T := R) (ht i) (-y)
    simpa only [add_neg_cancel, sub_neg_eq_add,
      External.Source.GMP.sourceBall, EinsteinRelation.External.AKM.ball] using h
  · intro psi hpsi hc hs
    let a : ℝ × Vec d := (0, -y)
    let phi : ℝ × Vec d → ℝ := fun z => psi (z + a)
    have hphi : ContDiff ℝ (⊤ : ℕ∞) phi :=
      hpsi.comp (contDiff_id.add contDiff_const)
    have hphic : HasCompactSupport phi := hc.comp_homeomorph (Homeomorph.addRight a)
    have hphis : tsupport phi ⊆ interior I ×ˢ External.Source.GMP.sourceBall y R := by
      intro z hz
      have h := hs (tsupport_comp_subset_preimage psi
        (continuous_id.add continuous_const) hz)
      have ht : z.1 ∈ interior I := by simpa [a] using h.1
      have hx : z.2 ∈ External.Source.GMP.sourceBall y R := by
        have hx' : z.2 + -y ∈ External.Source.GMP.sourceBall (0 : Vec d) R := by
          simpa [a] using h.2
        have := (c13_sourceBall_translate y (z.2 + -y) R).2 hx'
        simpa using this
      exact ⟨ht, hx⟩
    have heq := he phi hphi hphic hphis
    let F : ℝ × Vec d → ℝ := fun z =>
      -(rho z.2 * u z) * fderiv ℝ phi z (1, 0) +
        dot ((alpha z.2).mulVec (grad z))
          (fun j => fderiv ℝ phi z (0, unitVector j))
    have hme : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1, z.2 + y)) := by
      convert (Homeomorph.addRight ((0 : ℝ), y)).measurableEmbedding using 1
      funext z
      rcases z with ⟨t, x⟩
      simp
    have hi := hm.integral_comp hme F
    have hd (z : ℝ × Vec d) : fderiv ℝ phi (z.1, z.2 + y) = fderiv ℝ psi z := by
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := psi) a (x := (z.1, z.2 + y))
      simpa [phi, a, Prod.ext_iff] using h
    change (∫ z in I ×ˢ External.Source.GMP.sourceBall (0 : Vec d) R,
      -(rho (z.2 + y) * u (z.1, z.2 + y)) * fderiv ℝ psi z (1, 0) +
        dot ((alpha (z.2 + y)).mulVec (grad (z.1, z.2 + y)))
          (fun j => fderiv ℝ psi z (0, unitVector j))) = 0
    simpa only [F, hd] using hi.trans heq

end EinsteinFull
