import EinsteinRelation.Correctors.PairedPDECutoffGlobalGradient

/-! # Space-time weak derivative of the actual compact cutoff

Source: `paper/main.tex:832–840`. Spatial integration by parts on almost
every time slice passes through Fubini to the full space-time cutoff.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial differentiation of a smooth space-time field restricted to a
fixed time. Source: `paper/main.tex:832–840`. -/
theorem paired_coordinateDerivative_slice {d : ℕ} {φ : ℝ × Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (t : ℝ) (x : Vec d) (j : Fin d) :
    coordinateDerivative j (fun y => φ (t, y)) x =
      fderiv ℝ φ (t, x) (0, unitVector j) := by
  have hp := hasFDerivAt_prodMk_right (𝕜 := ℝ) t x
  change fderiv ℝ (φ ∘ fun y : Vec d => (t, y)) x (unitVector j) = _
  rw [fderiv_comp x (hφ.differentiable (by simp) (t, x)) hp.differentiableAt,
    hp.fderiv]
  rfl

/-- Fubini and the spatial product rule give the global weak derivative
of the actual compact cutoff field. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_spacetime_integration_by_parts {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (_hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ φ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) (j : Fin d) :
    (∫ z : ℝ × Vec d, (ζ z * u z) * fderiv ℝ φ z (0, unitVector j)) =
      -(∫ z : ℝ × Vec d,
        (ζ z * G z j + u z * fderiv ℝ ζ z (0, unitVector j)) * φ z) := by
  let μ := volume.restrict (I ×ˢ U)
  let D := fun (f : ℝ × Vec d → ℝ) z => fderiv ℝ f z (0, unitVector j)
  have hD (f : ℝ × Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
      (hfc : HasCompactSupport f) : MemLp (D f) 2 μ := by
    have hc : Continuous (D f) :=
      ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).continuous
    exact (hc.memLp_of_hasCompactSupport
      (hfc.fderiv_apply ℝ (0, unitVector j))).mono_measure Measure.restrict_le_self
  have hζφ : MemLp (fun z => ζ z * φ z) 2 μ :=
    ((hζ.mul hφ).continuous.memLp_of_hasCompactSupport hζc.mul_right).mono_measure
      Measure.restrict_le_self
  have hDζφ : MemLp (fun z => D ζ z * φ z) 2 μ := by
    have hc : Continuous (fun z => D ζ z * φ z) :=
      (((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).mul hφ).continuous
    exact (hc.memLp_of_hasCompactSupport
      (hζc.fderiv_apply ℝ (0, unitVector j)).mul_right).mono_measure
        Measure.restrict_le_self
  have hL : Integrable (fun z => ζ z * u z * D φ z) μ :=
    ((parabolicSolution_cutoff_energy_class hU hsol hζ hζc).1).integrable_mul (hD φ hφ hφc)
  have hM : Integrable (fun z => u z * (D ζ z * φ z)) μ :=
    hsol.1.integrable_mul hDζφ
  have hR : Integrable (fun z => G z j * (ζ z * φ z)) μ :=
    (parabolicSolution_gradient_coordinate_memLp hsol j).integrable_mul hζφ
  have hLp : Integrable (fun z => ζ z * u z * D φ z)
      ((volume.restrict I).prod (volume.restrict U)) := by
    rwa [Measure.prod_restrict]
  have hMp : Integrable (fun z => u z * (D ζ z * φ z))
      ((volume.restrict I).prod (volume.restrict U)) := by
    rwa [Measure.prod_restrict]
  have hRp : Integrable (fun z => G z j * (ζ z * φ z))
      ((volume.restrict I).prod (volume.restrict U)) := by
    rwa [Measure.prod_restrict]
  have hslice : ∀ᵐ t ∂volume.restrict I,
      (∫ x in U, ζ (t, x) * u (t, x) * D φ (t, x)) =
        -(∫ x in U, (ζ (t, x) * G (t, x) j + u (t, x) * D ζ (t, x)) * φ (t, x)) := by
    filter_upwards [hsol.2.2.2.1, hLp.prod_right_ae, hMp.prod_right_ae,
      hRp.prod_right_ae] with t ht hLt hMt hRt
    let ψ := fun x : Vec d => ζ (t, x) * φ (t, x)
    have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
      (hζ.mul hφ).comp (contDiff_const.prodMk contDiff_id)
    have hψc : HasCompactSupport ψ := by
      apply HasCompactSupport.of_support_subset_isCompact (hζc.image continuous_snd)
      intro x hx
      exact ⟨(t, x), subset_tsupport ζ (mul_ne_zero_iff.mp hx).1, rfl⟩
    have hψU : tsupport ψ ⊆ U := by
      have hs : tsupport ψ ⊆ (fun x : Vec d => (t, x)) ⁻¹' tsupport ζ := by
        apply closure_minimal ?_ (isClosed_closure.preimage (continuous_const.prodMk continuous_id))
        intro x hx
        exact subset_tsupport ζ (mul_ne_zero_iff.mp hx).1
      exact fun x hx => (hζsupp (hs hx)).2
    have hw := (ht j).2.2 ψ ⟨hψ, hψc, hψU⟩
    have hd (x : Vec d) : coordinateDerivative j ψ x =
        D ζ (t, x) * φ (t, x) + ζ (t, x) * D φ (t, x) := by
      rw [show ψ = fun x : Vec d => (fun y => ζ (t, y)) x * (fun y => φ (t, y)) x from rfl]
      rw [coordinateDerivative_mul j (fun y => ζ (t, y)) (fun y => φ (t, y)) x
        ((hζ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x)
        ((hφ.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) x),
        paired_coordinateDerivative_slice hζ, paired_coordinateDerivative_slice hφ]
      dsimp only [D]
      ring
    have hi : (∫ x in U, u (t, x) * coordinateDerivative j ψ x) =
        (∫ x in U, u (t, x) * (D ζ (t, x) * φ (t, x))) +
          ∫ x in U, ζ (t, x) * u (t, x) * D φ (t, x) := by
      rw [← integral_add hMt hLt]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp only; rw [hd]; ring)
    rw [hi] at hw
    have hrhs : (∫ x in U, (ζ (t, x) * G (t, x) j + u (t, x) * D ζ (t, x)) * φ (t, x)) =
        (∫ x in U, G (t, x) j * (ζ (t, x) * φ (t, x))) +
          ∫ x in U, u (t, x) * (D ζ (t, x) * φ (t, x)) := by
      rw [← integral_add hRt hMt]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    rw [hrhs]
    change _ = -(∫ x in U, G (t, x) j * (ζ (t, x) * φ (t, x))) at hw
    linarith only [hw]
  have hglobal : (∫ z in I ×ˢ U, ζ z * u z * D φ z) =
      -(∫ z in I ×ˢ U, (ζ z * G z j + u z * D ζ z) * φ z) := by
    have hsum : Integrable (fun z => (ζ z * G z j + u z * D ζ z) * φ z)
        ((volume.restrict I).prod (volume.restrict U)) := by
      convert hRp.add hMp using 1
      funext z
      simp only [Pi.add_apply]
      ring
    change (∫ z, ζ z * u z * D φ z ∂(volume.prod volume).restrict (I ×ˢ U)) =
      -(∫ z, (ζ z * G z j + u z * D ζ z) * φ z ∂(volume.prod volume).restrict (I ×ˢ U))
    rw [← Measure.prod_restrict, integral_prod _ hLp, integral_prod _ hsum, ← integral_neg]
    exact integral_congr_ae hslice
  have hzero (z : ℝ × Vec d) (hz : z ∉ I ×ˢ U) :
      ζ z = 0 ∧ D ζ z = 0 := by
    have hn : z ∉ tsupport ζ := fun hx => hz (hζsupp hx)
    exact ⟨image_eq_zero_of_notMem_tsupport hn, by
      simp only [D, fderiv_of_notMem_tsupport ℝ hn, ContinuousLinearMap.zero_apply]⟩
  change (∫ z, ζ z * u z * D φ z) = -(∫ z, (ζ z * G z j + u z * D ζ z) * φ z)
  calc
    _ = ∫ z in I ×ˢ U, ζ z * u z * D φ z :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun z hz => by rw [(hzero z hz).1, zero_mul, zero_mul])).symm
    _ = _ := hglobal
    _ = _ := congrArg Neg.neg (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by rw [(hzero z hz).1, (hzero z hz).2]; ring))

end EinsteinRelation.Correctors
