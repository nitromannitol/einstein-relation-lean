import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Calculus.ComplexTransposeContinuitySupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Weighted temporal energy for the actual transpose orbit, on a common physical
event before every compact region and absolutely continuous cutoff. -/
theorem local_time_transpose_ae_physical_weighted_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ U V : ℝ × FieldPair d → ℂ,
      Measurable U ∧ Measurable V ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal g) ∧
      ∀ b c : ℝ, 0 ≤ b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K, ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c →
            (∫ s in b..c, η s *
              (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
              η c * ‖(T c.toNNReal f) (translate x ω)‖ ^ 2 -
              η b * ‖(T b.toNNReal f) (translate x ω)‖ ^ 2 -
              ∫ s in b..c, deriv η s * ‖U (s, translate x ω)‖ ^ 2 := by
  let := reducedLaw_probability Q
  let w : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => T s.toNNReal f
  have hcont : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hwcont : Continuous w :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  obtain ⟨U, hU, heU⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative hwcont.stronglyMeasurable
  obtain ⟨V, hV, heV⟩ := EinsteinFull.StronglyMeasurable.exists_joint_l2_representative hcont.stronglyMeasurable
  have hIntegral (b c : ℝ) (hb : 0 ≤ b) (hbc : b ≤ c) :
      (∫ s in Icc b c, T s.toNNReal g) = w c - w b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc,
      ← intervalIntegral.integral_interval_sub_left
        (hcont.intervalIntegrable 0 c) (hcont.intervalIntegrable 0 b)]
    have hc := hT.integral_orbit_eq_sub hP hfg c.toNNReal
    have hb' := hT.integral_orbit_eq_sub hP hfg b.toNNReal
    rw [Real.coe_toNNReal c (hb.trans hbc)] at hc
    rw [Real.coe_toNNReal b hb] at hb'
    rw [hc, hb']
    dsimp only [w]
    abel
  have hprimitive (b c : ℝ) (hb : 0 ≤ b) (_hbc : b ≤ c) :
      ∀ᵐ ω ∂reducedLaw Q,
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod (volume.restrict (Icc b c)),
          U (p.2, translate p.1 ω) = (w b) (translate p.1 ω) +
            ∫ v in Icc b p.2, V (v, translate p.1 ω) := by
    let F : ℝ × FieldPair d → ℂ := fun p =>
      (w b) p.2 + ∫ v in Icc b p.1, V (v, p.2)
    have hF : Measurable F :=
      ((Lp.stronglyMeasurable (w b)).measurable.comp measurable_snd).add
        (measurable_complexPrimitive hV b)
    have he (s : ℝ) (hs : s ∈ Icc b c) :
        (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => F (s, ω) := by
      have hint : IntegrableOn (fun r : ℝ => T r.toNNReal g) (Icc b s) :=
        hcont.continuousOn.integrableOn_compact isCompact_Icc
      have hi := coeFn_integral_joint_l2_representative hint hV heV
      have hFTC := hIntegral b s hb hs.1
      rw [hFTC] at hi
      filter_upwards [heU s, hi, Lp.coeFn_sub (w s) (w b)] with ω hω hi hsub
      change U (s, ω) = (w b) ω + ∫ v in Icc b s, V (v, ω)
      rw [hω, ← hi, hsub]
      exact (add_sub_cancel _ _).symm
    have hmU := measurable_joint_spatial_translate hU
    have hmF := measurable_joint_spatial_translate hF
    have hephys : ∀ᵐ s ∂volume.restrict (Icc b c),
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod (reducedLaw Q),
          U (s, translate p.1 p.2) = F (s, translate p.1 p.2) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
        (hmU.comp (measurable_const.prodMk measurable_id))
        (hmF.comp (measurable_const.prodMk measurable_id)))).mpr
      exact ae_of_all _ fun x =>
        (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae
          (he s hs)
    have heprod := (Measure.ae_prod_iff_ae_ae
      (measurableSet_eq_fun hmU hmF)).mpr hephys
    have hswap := (measurePreserving_prodAssoc
      (volume.restrict (Icc b c)) (volume : Measure (Vec d)) (reducedLaw Q))
    have heassoc := hswap.quasiMeasurePreserving.ae heprod
    have henv := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heassoc)
    filter_upwards [henv] with ω hω
    exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae hω
  refine ⟨U, V, hU, hV, heU, heV, ?_⟩
  intro b c hb hbc
  have hi : IntegrableOn (fun s : ℝ => T s.toNNReal g) (Icc b c) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC := hIntegral b c hb hbc
  have hc := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) hi hV heV
  rw [hFTC] at hc
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (w c - w b)).measurable
    ((Lp.stronglyMeasurable (w c)).measurable.sub (Lp.stronglyMeasurable (w b)).measurable)
    (Lp.coeFn_sub (w c) (w b))
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hV heV)
  filter_upwards [hprimitive b c hb hbc, hc, hs, hl] with ω hprim hc hs hl
  intro K hK
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hprim),
    ae_restrict_of_ae hc, ae_restrict_of_ae hs, (hl K hK).prod_right_ae]
    with x hx hc hs hv
  have hu : IntervalIntegrable (fun s => V (s, translate x ω)) volume b c := by
    have hv' : IntegrableOn (fun s => V (s, translate x ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using! hv
    exact hv'.intervalIntegrable
  have hend : (w b) (translate x ω) + (∫ s in b..c, V (s, translate x ω)) =
      (w c) (translate x ω) := by
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc, ← hc, hs]
    exact add_sub_cancel _ _
  intro η hη
  have heq : ∀ᵐ s ∂volume.restrict (Icc b c),
      U (s, translate x ω) = (w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω) := by
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  have hleft :
      (∫ s in b..c, η s * (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
      ∫ s in b..c, η s * (2 * (star ((w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω)) * V (s, translate x ω)).re) := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  have hright : (∫ s in b..c, deriv η s * ‖U (s, translate x ω)‖ ^ 2) =
      ∫ s in b..c, deriv η s * ‖(w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  rw [hleft, hright]
  simpa only [hend] using complexPrimitive_weighted_energy hu ((w b) (translate x ω)) hη

end EinsteinFull.Blueprint
