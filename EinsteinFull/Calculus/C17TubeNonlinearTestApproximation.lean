import EinsteinFull.Calculus.C17TubeSpacetimeSobolevDensity
import EinsteinFull.Calculus.C13TubeWeakGradientChain
import EinsteinFull.Calculus.C13TubeSpatialTranslation

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The bounded C¹ chain rule and smooth cutoff hold on almost every spatial slice. -/
theorem c17_nonlinear_cutoff_weak_gradient_slices
    {d : ℕ} {a b R : ℝ} (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => u (t,x)) (fun x => G (t,x)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => θ (t,x) * F (u (t,x)))
        (fun x => θ (t,x) • (deriv F (u (t,x)) • G (t,x)) +
          F (u (t,x)) • (fun j => fderiv ℝ θ (t,x) (0,unitVector j))) := by
  have hball : IsOpen (sourceBall (0 : Vec d) R) := by
    unfold sourceBall
    exact isOpen_lt ((Feller.continuous_euclideanNorm d).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hu' : MemLp u 2 ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : Vec d) R))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu
    exact hu
  have hG' : MemLp (fun z => euclideanNorm (G z)) 2
      ((volume.restrict (Set.Ioo a b)).prod (volume.restrict (sourceBall (0 : Vec d) R))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hG
    exact hG
  filter_upwards [c9_memLp_prod_right_ae _ _ u hu',
    c9_memLp_prod_right_ae _ _ (fun z => euclideanNorm (G z)) hG', hgrad] with t ht hGt hw
  have hchain := (c13_native_weak_gradient_bounded_C1_chain hball _ _ ht hGt hw F hF hF0 M hM hFM).2.2
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x => θ (t,x)) := hθ.comp (contDiff_prodMk_right t)
  have hd (i : Fin d) (x : Vec d) : coordinateDerivative i (fun y => θ (t,y)) x =
      fderiv ℝ θ (t,x) (0,unitVector i) := by
    have hp : HasFDerivAt (fun y : Vec d => (t,y))
        (ContinuousLinearMap.inr ℝ ℝ (Vec d)) x := hasFDerivAt_prodMk_right t x
    unfold coordinateDerivative
    change fderiv ℝ (θ ∘ (fun y : Vec d => (t,y))) x (unitVector i) = _
    rw [fderiv_comp x (hθ.differentiable (by simp) (t,x)) hp.differentiableAt, hp.fderiv]
    rfl
  intro i
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hd] using
    (Correctors.hasWeakGradient_mul_smooth hball hchain hs i)

/-- Smooth compact tests approximate the nonlinear spatial Sobolev cutoff. -/
theorem c17_nonlinear_spacetime_test_approximation
    {d : ℕ} {a b R : ℝ}
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => u (t,x)) (fun x => G (t,x)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    let ψ := fun z => θ z * F (u z)
    let H := fun z => θ z • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ θ z (0,unitVector j))
    ∃ v : ℕ → (ℝ × Vec d → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
        tsupport (v n) ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - H z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) := by
  let μ := volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)
  let D : ℝ × Vec d → Vec d := fun z j => fderiv ℝ θ z (0, unitVector j)
  have hf : MemLp (fun z => F (u z)) 2 μ := by
    change MemLp (F ∘ u) 2 μ
    exact (PDE.lipschitzWith_of_abs_deriv_le hM (hF.differentiable (by simp)) hFM).comp_memLp hF0 hu
  have hθtop : MemLp θ ⊤ μ := hθ.continuous.memLp_top_of_hasCompactSupport hθc μ
  have hψ : MemLp (fun z => θ z * F (u z)) 2 μ := by
    simpa only [mul_comm] using hf.fun_mul hθtop
  have hderm : AEStronglyMeasurable (fun z => deriv F (u z)) μ :=
    hF.continuous_deriv_one.comp_aestronglyMeasurable hu.aestronglyMeasurable
  have hdertop : MemLp (fun z => deriv F (u z)) ⊤ μ := by
    apply memLp_top_of_bound hderm M
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFM (u z)
  have hDcont (j : Fin d) : Continuous (fun z => D z j) := by
    dsimp [D]
    exact ((contDiff_infty_iff_fderiv.mp hθ).2.clm_apply contDiff_const).continuous
  have hDtop (j : Fin d) : MemLp (fun z => D z j) ⊤ μ :=
    (hDcont j).memLp_top_of_hasCompactSupport (hθc.fderiv_apply ℝ (0,unitVector j)) μ
  have hcoord (j : Fin d) : MemLp (fun z => G z j) 2 μ := by
    apply hG.mono' ((continuous_apply j).comp_aestronglyMeasurable hGm)
    exact ae_of_all _ fun z => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (G z)) j)
  let H : ℝ × Vec d → Vec d := fun z => θ z • (deriv F (u z) • G z) + F (u z) • D z
  have hHi (j : Fin d) : MemLp (fun z => H z j) 2 μ := by
    have h1 : MemLp (fun z => deriv F (u z) * G z j) 2 μ := by
      simpa only [mul_comm] using (hcoord j).fun_mul hdertop
    have h2 : MemLp (fun z => θ z * (deriv F (u z) * G z j)) 2 μ := by
      simpa only [mul_comm] using h1.fun_mul hθtop
    convert h2.add (hf.fun_mul (hDtop j)) using 1
  have hvec : MemLp (fun z => (WithLp.toLp 2 (H z) : EuclideanSpace ℝ (Fin d))) 2 μ := by
    exact memLp_piLp_iff.mpr hHi
  have hH : MemLp (fun z => euclideanNorm (H z)) 2 μ := by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hvec.norm
  have hHm : AEStronglyMeasurable H μ := by
    exact (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ)).comp_aestronglyMeasurable hvec.aestronglyMeasurable
  exact c17_spacetime_spatial_sobolev_test_density _ _ hψ hHm hH
    (c17_nonlinear_cutoff_weak_gradient_slices u G hu hG hgrad F hF hF0 M hM hFM θ hθ)
    hθc.mul_right (tsupport_mul_subset_left.trans hθs)


/-- The nonlinear approximation also applies when the nonlinearity has nonzero value at zero. -/
theorem c17_nonlinear_spacetime_test_approximation_without_zero
    {d : ℕ} {a b R : ℝ}
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => u (t,x)) (fun x => G (t,x)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) :
    let ψ := fun z => θ z * F (u z)
    let H := fun z => θ z • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ θ z (0,unitVector j))
    ∃ v : ℕ → (ℝ × Vec d → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
        tsupport (v n) ⊆ Set.Ioo a b ×ˢ sourceBall 0 R) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - H z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R))) atTop (𝓝 0) := by
  let Q : ℝ → ℝ := fun s => F s - F 0
  have hQ : ContDiff ℝ 1 Q := hF.sub contDiff_const
  have hQder (s : ℝ) : deriv Q s = deriv F s := by
    simp [Q]
  obtain ⟨v, hv, hv0, hv1⟩ := c17_nonlinear_spacetime_test_approximation
    u G hu hGm hG hgrad Q hQ (by simp [Q]) M hM
    (fun s => by simpa only [hQder] using hFM s) θ hθ hθc hθs
  let c : ℝ × Vec d → ℝ := fun z => θ z * F 0
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := hθ.mul contDiff_const
  have hcc : HasCompactSupport c := hθc.mul_right
  have hcs : tsupport c ⊆ Set.Ioo a b ×ˢ sourceBall 0 R :=
    tsupport_mul_subset_left.trans hθs
  refine ⟨fun n z => v n z + c z, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(hv n).1.add hc, (hv n).2.1.add hcc,
      (tsupport_add _ _).trans (Set.union_subset (hv n).2.2 hcs)⟩
  · have heq (n : ℕ) : (fun z => v n z + c z - θ z * F (u z)) =
        (fun z => v n z - θ z * Q (u z)) := by
      funext z
      dsimp [c, Q]
      ring
    simpa only [heq] using hv0
  · have heq (n : ℕ) : (fun z => euclideanNorm
        ((fun j => fderiv ℝ (fun z => v n z + c z) z (0,unitVector j)) -
          (θ z • (deriv F (u z) • G z) +
            F (u z) • (fun j => fderiv ℝ θ z (0,unitVector j))))) =
        (fun z => euclideanNorm
          ((fun j => fderiv ℝ (v n) z (0,unitVector j)) -
            (θ z • (deriv Q (u z) • G z) +
              Q (u z) • (fun j => fderiv ℝ θ z (0,unitVector j))))) := by
      funext z
      congr 1
      ext j
      have hd : fderiv ℝ c z (0, unitVector j) =
          F 0 * fderiv ℝ θ z (0, unitVector j) := by
        change fderiv ℝ (θ * fun _ => F 0) z (0, unitVector j) = _
        rw [fderiv_mul (hθ.differentiable (by simp) z) (differentiableAt_const _)]
        simp
      change (fderiv ℝ (v n + c) z) (0,unitVector j) - _ = _
      rw [fderiv_add ((hv n).1.differentiable (by simp) z) (hc.differentiable (by simp) z)]
      simp only [add_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul, hQder, hd, Q]
      ring
    simpa only [heq] using hv1

/-- Translation extends the nonlinear test approximation to any spatial center. -/
theorem c17_nonlinear_spacetime_test_approximation_at_center
    {d : ℕ} {y : Vec d} {a b R : ℝ}
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)))
    (hgrad : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall y R) (fun x => u (t,x)) (fun x => G (t,x)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F)
    (M : ℝ) (hM : 0 ≤ M) (hFM : ∀ s, |deriv F s| ≤ M)
    (θ : ℝ × Vec d → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆ Set.Ioo a b ×ˢ sourceBall y R) :
    let ψ := fun z => θ z * F (u z)
    let H := fun z => θ z • (deriv F (u z) • G z) +
      F (u z) • (fun j => fderiv ℝ θ z (0,unitVector j))
    ∃ v : ℕ → (ℝ × Vec d → ℝ),
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (v n) ∧ HasCompactSupport (v n) ∧
        tsupport (v n) ⊆ Set.Ioo a b ×ˢ sourceBall y R) ∧
      Tendsto (fun n => eLpNorm (fun z => v n z - ψ z) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n) z (0,unitVector j)) - H z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))) atTop (𝓝 0) := by
  let A : ℝ × Vec d := (0, y)
  let B : ℝ × Vec d := (0, -y)
  let T : ℝ × Vec d → ℝ × Vec d := fun z => z + A
  let S : ℝ × Vec d → ℝ × Vec d := fun z => z + B
  have hTS (z : ℝ × Vec d) : T (S z) = z := by
    rcases z with ⟨t, x⟩
    simp [T, S, A, B, add_assoc]
  have hm : MeasurePreserving T
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)) := by
    convert c13_cylinder_translation_measurePreserving y R (Set.Ioo a b) using 1
    funext z
    rcases z with ⟨t, x⟩
    simp [T, A]
  have hm' : MeasurePreserving S
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
    have h := MeasurePreserving.symm (Homeomorph.addRight A).toMeasurableEquiv hm
    convert h using 1
    funext z
    apply (Homeomorph.addRight A).injective
    simp [S, A, B, add_assoc]
  have ht : ContDiff ℝ (⊤ : ℕ∞) (θ ∘ T) :=
    hθ.comp (contDiff_id.add contDiff_const)
  have htc : HasCompactSupport (θ ∘ T) := hθc.comp_homeomorph (Homeomorph.addRight A)
  have hts : tsupport (θ ∘ T) ⊆ Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R := by
    intro z hz
    have hh := hθs (tsupport_comp_subset_preimage θ (continuous_id.add continuous_const) hz)
    exact ⟨by simpa [T, A] using hh.1, (c13_sourceBall_translate y z.2 R).1 (by simpa [T, A] using hh.2)⟩
  have hw : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient (sourceBall 0 R) (fun x => u (T (t,x))) (fun x => G (T (t,x))) := by
    filter_upwards [hgrad] with t hh
    intro i
    have h := EinsteinFull.Blueprint.covariance_hasWeakPartialDerivative_translate (hh i) (-y)
    simpa [T, A, sourceBall, EinsteinRelation.External.AKM.ball] using h
  obtain ⟨v, hv, hv0, hv1⟩ := c17_nonlinear_spacetime_test_approximation_without_zero
    (u ∘ T) (G ∘ T) (hu.comp_measurePreserving hm)
    (hGm.comp_measurePreserving hm) (hG.comp_measurePreserving hm) hw F hF M hM hFM
    (θ ∘ T) ht htc hts
  have hd (f : ℝ × Vec d → ℝ) (z : ℝ × Vec d) :
      fderiv ℝ (f ∘ S) z = fderiv ℝ f (S z) := by
    simpa [S, Function.comp_def] using fderiv_comp_add_right (𝕜 := ℝ) (f := f) B (x := z)
  have hdT (z : ℝ × Vec d) : fderiv ℝ (θ ∘ T) (S z) = fderiv ℝ θ z := by
    simpa [T, Function.comp_def, hTS] using
      fderiv_comp_add_right (𝕜 := ℝ) (f := θ) A (x := S z)
  refine ⟨fun n => v n ∘ S, ?_, ?_, ?_⟩
  · intro n
    refine ⟨(hv n).1.comp (contDiff_id.add contDiff_const),
      (hv n).2.1.comp_homeomorph (Homeomorph.addRight B), ?_⟩
    intro z hz
    have hh := (hv n).2.2 (tsupport_comp_subset_preimage (v n) (continuous_id.add continuous_const) hz)
    refine ⟨by simpa [S, B] using hh.1, ?_⟩
    have hx := (c13_sourceBall_translate y (z.2 + -y) R).2 (by simpa [S, B] using hh.2)
    simpa using hx
  · have he (n : ℕ) : (fun z => v n (S z) - θ z * F (u z)) =
        (fun z => v n z - (θ ∘ T) z * F ((u ∘ T) z)) ∘ S := by
      funext z
      simp [hTS]
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun z => v n z - (θ ∘ T) z * F ((u ∘ T) z))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) :=
      (hv n).1.continuous.aestronglyMeasurable.sub
        (ht.continuous.aestronglyMeasurable.mul
          (hF.continuous.comp_aestronglyMeasurable (hu.comp_measurePreserving hm).aestronglyMeasurable))
    have hn (n : ℕ) : eLpNorm (fun z => (v n ∘ S) z - θ z * F (u z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall y R)) =
        eLpNorm (fun z => v n z - (θ ∘ T) z * F ((u ∘ T) z)) 2
          (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
      change eLpNorm (fun z => v n (S z) - θ z * F (u z)) 2 _ = _
      rw [he n, eLpNorm_comp_measurePreserving (hmeas n) hm']
    simpa only [hn] using hv0
  · have he (n : ℕ) : (fun z => euclideanNorm
        ((fun j => fderiv ℝ (v n ∘ S) z (0,unitVector j)) -
          (θ z • (deriv F (u z) • G z) + F (u z) •
            (fun j => fderiv ℝ θ z (0,unitVector j))))) =
        (fun z => euclideanNorm
          ((fun j => fderiv ℝ (v n) z (0,unitVector j)) -
            ((θ ∘ T) z • (deriv F ((u ∘ T) z) • (G ∘ T) z) +
              F ((u ∘ T) z) • (fun j => fderiv ℝ (θ ∘ T) z (0,unitVector j))))) ∘ S := by
      funext z
      simp only [Function.comp_apply, hd, hdT, hTS]
    have hmeas (n : ℕ) : AEStronglyMeasurable
        (fun z => euclideanNorm
          ((fun j => fderiv ℝ (v n) z (0,unitVector j)) -
            ((θ ∘ T) z • (deriv F ((u ∘ T) z) • (G ∘ T) z) +
              F ((u ∘ T) z) • (fun j => fderiv ℝ (θ ∘ T) z (0,unitVector j)))))
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : Vec d) R)) := by
      apply (Feller.continuous_euclideanNorm d).comp_aestronglyMeasurable
      apply AEStronglyMeasurable.sub
      · exact (continuous_pi fun j =>
          ((contDiff_infty_iff_fderiv.mp (hv n).1).2.clm_apply contDiff_const).continuous).aestronglyMeasurable
      · apply AEStronglyMeasurable.add
        · exact ht.continuous.aestronglyMeasurable.smul
            ((hF.continuous_deriv_one.comp_aestronglyMeasurable
              (hu.comp_measurePreserving hm).aestronglyMeasurable).smul
              (hGm.comp_measurePreserving hm))
        · exact (hF.continuous.comp_aestronglyMeasurable
            (hu.comp_measurePreserving hm).aestronglyMeasurable).smul
              ((continuous_pi fun j =>
                ((contDiff_infty_iff_fderiv.mp ht).2.clm_apply contDiff_const).continuous).aestronglyMeasurable)
    have hn (n : ℕ) := eLpNorm_comp_measurePreserving (p := 2) (hmeas n) hm'
    have hn' (n : ℕ) := (he n).symm ▸ hn n
    simpa only [hn'] using hv1

end EinsteinFull.Calculus
