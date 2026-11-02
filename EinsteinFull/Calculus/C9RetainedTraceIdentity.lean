import EinsteinFull.Calculus.C9ShortTimeLocality

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open C9ShortTimeLocality

/-! Initial and terminal traces for the jointly realized retained cutoff equation. -/

theorem retained_cutoff_initial_terminal_trace
{d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    :     ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q,
        let u : Vec d → ℂ := fun x =>
          ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω)
        let X : Vec d → Fin d → ℂ := fun x j =>
          ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V j (s, translate x ω)
        let b : Lp ℂ 2 (reducedLaw Q) := η (t : ℝ) • P t f - η 0 • f
        let g : Vec d → ℂ := fun x => b (translate x ω) -
          ∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) * U (s, translate x ω)
        ∀ χ : C(Vec d, ℝ), ∀ ψ : Vec d → ℝ,
          IsSpatialTest Set.univ ψ → ∀ L : ℂ →L[ℝ] ℝ,
          let H : Vec d → Fin d → ℂ := fun x => C9ShortTimeLocality.cutoffGradient (ψ x)
            (fun k => coordinateDerivative k ψ x) (u x) (X x)
          let R : Vec d → Fin d → ℂ := fun x j =>
            ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) *
              C9ShortTimeLocality.retainedCutoffFluxSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (U (s, translate x ω)) (fun k => V k (s, translate x ω)) j
          let S : Vec d → ℂ := fun x =>
            ∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) *
              C9ShortTimeLocality.retainedCutoffScalarSource χ ω x (ψ x) (fun k => coordinateDerivative k ψ x)
                (U (s, translate x ω)) (fun k => V k (s, translate x ω)) i ζ
          HasWeakDivergence Set.univ
            (fun x j => L ((∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * H x k) + R x j))
            (fun x => L (2 * (ψ x : ℂ) * g x -
              2 * ζ * (∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * H x j) - S x)) := by
  have htimegraph (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s)
      (hη' : Continuous η') (t : ℝ≥0) :
    IsComplexGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), η s • P s.toNNReal f)
      (η (t : ℝ) • P t f - η 0 • f -
        ∫ s in (0 : ℝ)..(t : ℝ), η' s • P s.toNNReal f) := by
    let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P s.toNNReal f
    let U : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => ∫ r in (0 : ℝ)..s, u r
    have hu : Continuous u := (hP.2.2.1 f).comp continuous_real_toNNReal
    have hU : ∀ s, HasDerivAt U (u s) s := fun s =>
      (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
    have hUc : Continuous U := continuous_iff_continuousAt.mpr fun s => (hU s).continuousAt
    have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
    have hgraph (s : ℝ) (hs : s ∈ uIcc (0 : ℝ) (t : ℝ)) :
        IsComplexGeneratorPair Q i ζ (η' s • U s) (η' s • (u s - f)) := by
      rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
      have hg := (hP.generator_timeIntegral f s.toNNReal).smul (η' s : ℂ)
      simpa only [Real.coe_toNNReal', max_eq_left hs.1, Complex.coe_smul] using! hg
    have hg := complexGeneratorPair_intervalIntegral_on (hη'.fun_smul hUc)
      (hη'.fun_smul (hu.fun_sub continuous_const)) 0 t hgraph
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := (t : ℝ))
      (fun s _ => (hη s).smul (hU s))
      (((hηc.fun_smul hu).add (hη'.fun_smul hUc)).intervalIntegrable 0 t)
    change (∫ s in (0 : ℝ)..(t : ℝ), η s • u s + η' s • U s) =
      η (t : ℝ) • U (t : ℝ) - η 0 • U 0 at he
    have hUz : U 0 = 0 := intervalIntegral.integral_same
    rw [hUz, smul_zero, sub_zero,
      intervalIntegral.integral_add ((hηc.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
        ((hη'.fun_smul hUc).intervalIntegrable (μ := volume) 0 t)] at he
    have hηi : (∫ s in (0 : ℝ)..(t : ℝ), η' s) = η t - η 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (t : ℝ)) (fun s _ => hη s) (hη'.intervalIntegrable 0 t)
    have hv : (∫ s in (0 : ℝ)..(t : ℝ), η' s • (u s - f)) =
        (∫ s in (0 : ℝ)..(t : ℝ), η' s • u s) - (η t - η 0) • f := by
      simp_rw [smul_sub]
      rw [intervalIntegral.integral_sub ((hη'.fun_smul hu).intervalIntegrable (μ := volume) 0 t)
        ((hη'.fun_smul continuous_const).intervalIntegrable (μ := volume) 0 t),
        intervalIntegral.integral_smul_const, hηi]
    have hb := (hP.generator_timeIntegral f t).smul (η t : ℂ)
    have hc := hb.add (hg.smul (-1))
    have he' : η (t : ℝ) • U (t : ℝ) -
        (∫ s in (0 : ℝ)..(t : ℝ), η' s • U s) =
        ∫ s in (0 : ℝ)..(t : ℝ), η s • u s := by
      rw [← he]
      abel
    simp only [neg_one_smul, Complex.coe_smul, ← sub_eq_add_neg] at hc
    change IsComplexGeneratorPair Q i ζ
      (η (t : ℝ) • U (t : ℝ) - ∫ s in (0 : ℝ)..(t : ℝ), η' s • U s)
      (η (t : ℝ) • (P t f - f) - ∫ s in (0 : ℝ)..(t : ℝ), η' s • (u s - f)) at hc
    rw [he', hv, smul_sub, sub_smul] at hc
    convert hc using 1; abel
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  obtain ⟨V, hV, heV⟩ := hP.exists_joint_gradient_representative f
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro η η' hη hη' t
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hg := htimegraph η η' hη hη' t
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at hg
  let b : Lp ℂ 2 (reducedLaw Q) := η (t : ℝ) • P t f - η 0 • f
  let I : Lp ℂ 2 (reducedLaw Q) := ∫ s in Icc (0 : ℝ) (t : ℝ), η' s • P s.toNNReal f
  have hgb := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (b - I)).measurable
    ((Lp.stronglyMeasurable b).measurable.sub (Lp.stronglyMeasurable I).measurable)
    (Lp.coeFn_sub b I)
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η hηc
  have hci := ae_spatial_weighted_integral_joint_l2_representative t
    (integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 f) (t : ℝ)) hU heU η' hη'
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      (hP.integrableOn_gradientOrbit f t)) (hV j) (heV j) η hηc
  filter_upwards [generatorPair_ae_retained_cutoff_equation Q hg
      (hP.weighted_integral_orbit_gradient f η hηc t), hgb, hcu, hci,
      ae_all_iff.mpr hcv, ae_joint_retained_sources_timeIntegral Q hP f hU hV heU heV t]
    with ω hw hgb hcu hci hcv hc
  dsimp only
  intro χ ψ hψ L
  apply Correctors.hasWeakDivergence_congr_ae isOpen_univ (hw χ ψ hψ L)
  · rw [Measure.restrict_univ]
    filter_upwards [hcu, ae_all_iff.mpr hcv, hc] with x hu hv hx
    funext j
    rw [hu]
    have hv' : (fun k => (∫ s in Icc (0 : ℝ) (t : ℝ),
        η s • (hP.gradientOrbit f s) k) (translate x ω)) =
        (fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
          (η s : ℂ) * V k (s, translate x ω)) := funext hv
    rw [hv']
    erw [(hx η hηc χ (ψ x) (fun k => coordinateDerivative k ψ x)).2.2.1 j]
  · rw [Measure.restrict_univ]
    filter_upwards [hgb, hcu, hci, ae_all_iff.mpr hcv, hc] with x hb hu hi hv hx
    change (b - I) (translate x ω) = b (translate x ω) - I (translate x ω) at hb
    rw [hb, hi, hu]
    have hv' : (fun k => (∫ s in Icc (0 : ℝ) (t : ℝ),
        η s • (hP.gradientOrbit f s) k) (translate x ω)) =
        (fun k => ∫ s in Icc (0 : ℝ) (t : ℝ),
          (η s : ℂ) * V k (s, translate x ω)) := funext hv
    rw [hv']
    erw [(hx η hηc χ (ψ x) (fun k => coordinateDerivative k ψ x)).2.2.2]

end EinsteinFull.Blueprint
