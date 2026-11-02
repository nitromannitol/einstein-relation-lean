import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private def conjugateLp {d : ℕ} (μ : Measure (FieldPair d)) :
    Lp ℂ 2 μ →L[ℝ] Lp ℂ 2 μ := Complex.conjCLE.toContinuousLinearMap.compLpL 2 μ

private theorem conjugateLp_apply {d : ℕ} (μ : Measure (FieldPair d)) (f : Lp ℂ 2 μ) :
    conjugateLp μ f = star f := by
  apply Lp.ext
  filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL f,
    Lp.coeFn_star f] with ω ha hb
  change (star f) ω = star (f ω) at hb
  simpa only [conjugateLp, Complex.conjCLE_apply, Complex.star_def, hb] using! ha

private theorem star_sub_lp {d : ℕ} (μ : Measure (FieldPair d)) (f g : Lp ℂ 2 μ) :
    star (f - g) = star f - star g := by
  simp only [← conjugateLp_apply μ, map_sub]

private theorem star_add_lp {d : ℕ} (μ : Measure (FieldPair d)) (f g : Lp ℂ 2 μ) :
    star (f + g) = star f + star g := by
  simpa only [conjugateLp_apply] using! (conjugateLp μ).map_add f g

private theorem star_real_smul_lp {d : ℕ} (μ : Measure (FieldPair d))
    (c : ℝ) (f : Lp ℂ 2 μ) : star (c • f) = c • star f := by
  simp only [← conjugateLp_apply μ, map_smul]

private theorem star_complex_real_smul_lp {d : ℕ} (μ : Measure (FieldPair d))
    (c : ℝ) (f : Lp ℂ 2 μ) : star ((c : ℂ) • f) = (c : ℂ) • star f := by
  simpa only [Complex.coe_smul] using! star_real_smul_lp μ c f

private theorem real_generator_star {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {lam : ℝ}
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i (lam : ℂ) f g) :
    IsComplexGeneratorPair Q i (lam : ℂ) (star f) (star g) := by
  obtain ⟨G, hG, hw⟩ := hfg
  refine ⟨fun j => star (G j), fun j => (hG j).star, ?_⟩
  intro v V hV
  have h := congrArg (starRingEnd ℂ)
    (hw (star v) (fun j => star (V j)) (fun j => (hV j).star))
  have hm : (∫ ω, (star g) ω * v ω ∂reducedLaw Q) =
      (starRingEnd ℂ) (∫ ω, g ω * (star v) ω ∂reducedLaw Q) := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star g, Lp.coeFn_star v] with ω hg hv
    change (star g) ω = star (g ω) at hg
    change (star v) ω = star (v ω) at hv
    simp only [hg, hv, map_mul, starRingEnd_apply, star_star]
  have he : (starRingEnd ℂ) (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
      (star (V j)) ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * (star (G k)) ω * V j ω ∂reducedLaw Q := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j)),
      ae_all_iff.mpr (fun j => Lp.coeFn_star (V j))] with ω hGω hVω
    change (∀ j, (star (G j)) ω = star (G j ω)) at hGω
    change (∀ j, (star (V j)) ω = star (V j ω)) at hVω
    have hc (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
    simp only [map_sum, map_mul, hGω, hVω, starRingEnd_apply, hc, star_star]
  have hd : (starRingEnd ℂ) (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) *
      (star v) ω ∂reducedLaw Q) =
      ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * (star (G j)) ω) * v ω ∂reducedLaw Q := by
    rw [← integral_conj]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j)),
      Lp.coeFn_star v] with ω hGω hvω
    change (∀ j, (star (G j)) ω = star (G j ω)) at hGω
    change (star v) ω = star (v ω) at hvω
    have hc (x : ℝ) : star (x : ℂ) = (x : ℂ) := Complex.conj_ofReal x
    simp only [map_sum, map_mul, hGω, hvω, starRingEnd_apply, hc, star_star]
  rw [hm, h]
  simp only [map_add, map_mul, map_neg, map_div₀, map_one, map_ofNat,
    Complex.conj_ofReal, he, hd]

private theorem real_resolvent_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam s : ℝ)
    (hs : complexForceShift d Λ (lam : ℂ) < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    forcedComplexResolvent Q i (lam : ℂ) s hs (star f) =
      star (forcedComplexResolvent Q i (lam : ℂ) s hs f) := by
  apply IsComplexGeneratorPair.forced_resolvent_unique hs
    (forcedComplexResolvent_spec Q i (lam : ℂ) s hs (star f))
  convert! real_generator_star (forcedComplexResolvent_spec Q i (lam : ℂ) s hs f) using 1
  simp only [star_sub_lp, star_complex_real_smul_lp, star_real_smul_lp]

private theorem exp_apply_star {d : ℕ} (μ : Measure (FieldPair d))
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f, A (star f) = star (A f)) (f : Lp ℂ 2 μ) :
    NormedSpace.exp A (star f) = star (NormedSpace.exp A f) := by
  have hp (m : ℕ) (u : Lp ℂ 2 μ) : (A ^ m) (star u) = star ((A ^ m) u) := by
    induction m with
    | zero => rfl
    | succ m hm =>
      simp only [pow_succ', ContinuousLinearMap.mul_apply, hm, hA]
  let E (u : Lp ℂ 2 μ) := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 μ) u).restrictScalars ℝ
  have hs (u : Lp ℂ 2 μ) := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (E u) (E u).continuous
  have hc := (hs f).map (conjugateLp μ) (conjugateLp μ).continuous
  have he : HasSum (fun m : ℕ => (m.factorial⁻¹ : ℝ) • (A ^ m) (star f))
      (star (NormedSpace.exp A f)) := by
    have hc' : HasSum (fun m : ℕ => conjugateLp μ ((m.factorial⁻¹ : ℝ) • (A ^ m) f))
        (conjugateLp μ (NormedSpace.exp A f)) := hc
    simpa only [map_smul, conjugateLp_apply, ← hp] using! hc'
  exact (hs (star f)).unique he

private theorem real_yosida_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (n : ℕ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    forcedComplexYosida Q i (lam : ℂ) n (star f) =
      star (forcedComplexYosida Q i (lam : ℂ) n f) := by
  simp only [forcedComplexYosida, forcedComplexResolventApproximation,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply, real_resolvent_star,
    star_sub_lp, star_complex_real_smul_lp, star_real_smul_lp]

private theorem real_yosidaEvolution_star {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (lam : ℝ) (n : ℕ) (t : ℝ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    forcedComplexYosidaEvolution Q i (lam : ℂ) n t (star f) =
      star (forcedComplexYosidaEvolution Q i (lam : ℂ) n t f) := by
  apply exp_apply_star
  intro u
  simp only [ContinuousLinearMap.smul_apply, real_yosida_star, star_real_smul_lp]

/-- Every full real-force evolution commutes with conjugation of L² data. -/
theorem realForceSemigroup_star {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {lam : ℝ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i (lam : ℂ) P) (t : ℝ≥0)
    (f : Lp ℂ 2 (reducedLaw Q)) : P t (star f) = star (P t f) := by
  have he : shiftedForcedComplexEvolution Q i (lam : ℂ) t (star f) =
      star (shiftedForcedComplexEvolution Q i (lam : ℂ) t f) :=
    tendsto_nhds_unique (tendsto_forcedComplexYosidaEvolution Q i (lam : ℂ) t (star f))
      (by
        have h := ((conjugateLp (reducedLaw Q)).continuous.tendsto _).comp
          (tendsto_forcedComplexYosidaEvolution Q i (lam : ℂ) t f)
        simpa only [Function.comp_def, conjugateLp_apply,
          ← real_yosidaEvolution_star] using! h)
  rw [hP.eq_forcedComplexEvolution]
  simp only [forcedComplexEvolution, ContinuousLinearMap.smul_apply,
    star_complex_real_smul_lp, star_real_smul_lp, he]

private theorem star_eq_of_real_ae {d : ℕ} {μ : Measure (FieldPair d)}
    {f : Lp ℂ 2 μ} {v : FieldPair d → ℝ}
    (hf : (f : FieldPair d → ℂ) =ᵐ[μ] fun ω => (v ω : ℂ)) : star f = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star f, hf] with ω hs hv
  change (star f) ω = star (f ω) at hs
  rw [hs, hv]
  exact Complex.conj_ofReal _

private theorem pairing_real {d : ℕ} {μ : Measure (FieldPair d)}
    (f g : Lp ℂ 2 μ) (hf : star f = f) (hg : star g = g) :
    (∫ ω, f ω * g ω ∂μ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f, Lp.coeFn_star g] with ω hfw hgw
  change (star f) ω = star (f ω) at hfw
  change (star g) ω = star (g ω) at hgw
  rw [hf] at hfw
  rw [hg] at hgw
  simp only [map_mul, starRingEnd_apply, ← hfw, ← hgw]

/-- The actual correlations are time measurable and real at every real force. -/
theorem node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_reality_of_deps
    (hstationary : node_stationary_u2D_analytic_u2D_semigroupStmt) :
    node_p_u3A_integration_u23_kernel_u2D_measurability_u2D_realityStmt := by
  intro d hd D Q hQ β a μ hβ ha hμ P hP
  let i₀ : Fin d := ⟨0, by omega⟩
  have hc (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
      Continuous (fun t : ℝ => ∫ ω, β i₀ ω * (P ζ t.toNNReal f) ω ∂reducedLaw Q) := by
    let L := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 (β i₀)
    have h := L.continuous.comp (((hP ζ).2.2.1 f).comp continuous_real_toNNReal)
    change Continuous (fun t : ℝ => L (P ζ t.toNNReal f)) at h
    simpa only [L, ContinuousLinearMap.lpPairing_eq_integral,
      ContinuousLinearMap.mul_apply'] using! h
  have hcanonical := (hstationary d hd D).1 Q hQ
  have hstar (lam : ℝ) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
      P (lam : ℂ) t (star f) = star (P (lam : ℂ) t f) := by
    have hF := (hcanonical.1 (lam : ℂ)).1
    rw [(hP (lam : ℂ)).unique hF]
    exact realForceSemigroup_star hF t f
  have hβreal (j : Fin d) : star (β j) = β j := star_eq_of_real_ae (hβ j)
  have hareal (j k : Fin d) : star (a j k) = a j k := star_eq_of_real_ae (ha j k)
  have hμreal : star μ = μ := star_eq_of_real_ae hμ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ζ j
    exact (hc ζ (β j + ζ • a i₀ j)).measurable
  · intro ζ
    exact (hc ζ (ζ • μ)).measurable
  · intro lam t j
    apply pairing_real
    · exact hβreal i₀
    · rw [← hstar lam]
      congr 1
      simp only [star_add_lp, star_complex_real_smul_lp, star_real_smul_lp, hβreal, hareal]
  · intro lam t
    apply pairing_real
    · exact hβreal i₀
    · rw [← hstar lam]
      congr 1
      simp only [star_complex_real_smul_lp, star_real_smul_lp, hμreal]

end EinsteinFull.Blueprint
