import EinsteinRelation.Correctors.ParabolicCutoffGlobalWeakGradient

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Localizing a spatial energy class uses no parabolic equation.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem parabolicEnergy_cutoff_data {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hG : ∀ j, MemLp (fun z => G z j) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x)))
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ I ×ˢ U) :
    MemLp (fun z => ζ z * u z) 2 volume ∧
      (∀ j, MemLp (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0,unitVector j))
        2 volume) ∧
      ∀ᵐ t ∂(volume : Measure ℝ), HasWeakGradient Set.univ
        (fun x => ζ (t,x) * u (t,x))
        (fun x j => ζ (t,x) * G (t,x) j + u (t,x) * fderiv ℝ ζ (t,x) (0,unitVector j)) := by
  let μ := volume.restrict (I ×ˢ U)
  have hζm : MemLp ζ ∞ μ := hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hlocal : MemLp (fun z => ζ z * u z) 2 μ ∧
      ∀ j, MemLp (fun z => ζ z * G z j + u z * fderiv ℝ ζ z (0,unitVector j)) 2 μ := by
    refine ⟨hu.mul' hζm, fun j => ?_⟩
    have hd : MemLp (fun z => fderiv ℝ ζ z (0,unitVector j)) ∞ μ :=
      ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
        |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (0,unitVector j)) _
    exact ((hG j).mul' hζm).add (hd.mul' hu)
  have hext {f : ℝ × Vec d → ℝ} (hf : MemLp f 2 μ)
      (hs : ∀ z ∉ I ×ˢ U, f z = 0) : MemLp f 2 volume := by
    have hi : (I ×ˢ U).indicator f = f := by
      funext z
      by_cases hz : z ∈ I ×ˢ U
      · exact Set.indicator_of_mem hz _
      · rw [Set.indicator_of_notMem hz, hs z hz]
    rw [← hi]
    exact (memLp_indicator_iff_restrict (hI.prod hU.measurableSet)).mpr hf
  refine ⟨hext hlocal.1 (fun z hz => ?_), fun j => hext (hlocal.2 j) (fun z hz => ?_), ?_⟩
  · have hn : z ∉ tsupport ζ := fun hx => hz (hζs hx)
    rw [image_eq_zero_of_notMem_tsupport hn, zero_mul]
  · have hn : z ∉ tsupport ζ := fun hx => hz (hζs hx)
    simp only [image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn,
      ContinuousLinearMap.zero_apply, zero_mul, mul_zero, add_zero]
  have hae := (ae_restrict_iff' hI).mp hw
  filter_upwards [hae] with t ht
  by_cases htI : t ∈ I
  · have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => ζ (t,x)) :=
      hζ.comp (contDiff_const.prodMk contDiff_id)
    have hemb : Topology.IsClosedEmbedding (fun x : Vec d => (t,x)) := by
      rw [Topology.IsClosedEmbedding.isClosedEmbedding_iff_continuous_injective_isClosedMap]
      exact ⟨continuous_const.prodMk continuous_id,
        fun _ _ h => congrArg Prod.snd h, isClosedMap_prodMk_left t⟩
    have hsub : tsupport (fun x : Vec d => ζ (t,x)) ⊆
        (fun x : Vec d => (t,x)) ⁻¹' tsupport ζ := by
      apply closure_minimal
      · intro x hx
        exact subset_tsupport ζ hx
      · exact (isClosed_tsupport ζ).preimage (continuous_const.prodMk continuous_id)
    have htest : IsSpatialTest U (fun x => ζ (t,x)) :=
      ⟨hs, hζc.comp_isClosedEmbedding hemb, fun x hx => (hζs (hsub hx)).2⟩
    have hg := hasWeakGradient_mul_spatialTest (ht htI) htest
    have hder (j : Fin d) (x : Vec d) :
        coordinateDerivative j (fun y => ζ (t,y)) x =
          fderiv ℝ ζ (t,x) (0,unitVector j) := by
      have hd := ((hζ.differentiable (by simp) (t,x)).hasFDerivAt).comp x
        ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
      change fderiv ℝ (ζ ∘ Prod.mk t) x (unitVector j) = _
      rw [hd.fderiv]
      rfl
    simpa only [hder] using hg
  · have hn (x : Vec d) : (t,x) ∉ tsupport ζ :=
      fun hx => htI (hζs hx).1
    have hz (x : Vec d) : ζ (t,x) = 0 := image_eq_zero_of_notMem_tsupport (hn x)
    have hd (x : Vec d) : fderiv ℝ ζ (t,x) = 0 :=
      fderiv_of_notMem_tsupport ℝ (hn x)
    have hzero : HasWeakGradient Set.univ (fun _ : Vec d => (0 : ℝ))
        (fun _ => (0 : Vec d)) := by
      intro j
      refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
      intro ψ _
      simp
    simpa only [hz, hd, ContinuousLinearMap.zero_apply, zero_mul, mul_zero,
      add_zero, Pi.zero_apply] using hzero

end EinsteinRelation.Correctors
