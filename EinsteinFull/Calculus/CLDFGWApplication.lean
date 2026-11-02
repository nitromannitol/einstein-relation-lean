import EinsteinFull.Calculus.CLDFGWCarrier
import EinsteinFull.Calculus.CLTwoSidedMartingale
import EinsteinRelation.Diffusion.TimeChangeCovariance

/-!
# The two-sided environment process in the setting of DFGW

The two-sided environment process satisfies the reversible ergodic Markov setting of
De Masi–Ferrari–Goldstein–Wick, Section 2, and its displacement is an antisymmetric family; the
rescaled forward path under the two-sided law has the annealed law of the quenched path laws.
-/

namespace EinsteinFull.External.Draft

open MeasureTheory ProbabilityTheory Filter EinsteinRelation EinsteinFull EinsteinFull.Blueprint
open scoped NNReal Topology

variable {d : ℕ}

section Application

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hap hK in
/-- The two-sided environment process satisfies the setting of DFGW Section 2. -/
theorem dfgw_process :
    IsDFGWReversibleErgodicProcess (tsLaw Q K) Q.measure tsState tsShift tsRefl (envKernel K) where
  probability := tsLaw_isProbability Q hap K
  invariant_probability := Q.probability
  measurable := measurable_tsState_joint
  marginal t := tsLaw_map_tsState hd D Q hQ hunforced hpath hap hK t
  translate_measurable := measurable_tsShift
  translate τ t ω := tsState_shift τ t ω
  stationary := tsLaw_map_tsShift hd D Q hQ hunforced hpath hap hK
  reflect_measurable := measurable_tsRefl
  reflect τ t ω := tsState_refl τ t ω
  reversible := tsLaw_map_tsRefl hd D Q hQ hunforced hpath hap hK
  markov_kernel _ := inferInstance
  markov t _ hf hC := tsLaw_condExp_state_bdd hd D Q hap hK t hf hC
  ergodic _ hA hinv := envKernel_ergodic hd D Q hQ hunforced hpath hK hA hinv

include hQ hunforced hpath hap hK in
/-- The displacement is an antisymmetric family in the sense of DFGW (2.3)–(2.5), A.1–A.4. -/
theorem dfgw_family :
    IsDFGWAntisymmetricFamily (tsLaw Q K) tsState tsShift tsRefl (tsDisp (d := d)) where
  adapted a b hab := by
    have ha : Measurable[dfgwSigma tsState (Set.Icc a b)] (tsState (d := d) a) :=
      Measurable.of_comap_le (le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc a b) =>
        MeasurableSpace.comap (tsState (d := d) t) inferInstance) a ⟨le_rfl, hab⟩ le_rfl)
    have hb : Measurable[dfgwSigma tsState (Set.Icc a b)] (tsState (d := d) b) :=
      Measurable.of_comap_le (le_iSup₂_of_le (f := fun t (_ : t ∈ Set.Icc a b) =>
        MeasurableSpace.comap (tsState (d := d) t) inferInstance) b ⟨hab, le_rfl⟩ le_rfl)
    have h : tsDisp (d := d) a b = fun ω => displacementInv (tsState a ω, tsState b ω) :=
      funext fun ω => tsDisp_eq_displacementInv a b ω
    rw [h]
    exact measurable_displacementInv.comp (ha.prodMk hb)
  antisymmetric a b _ := ae_of_all _ fun ω => tsDisp_refl_mid a b ω
  integrable _ _ hab := integrable_tsDisp hd D Q hQ hunforced hpath hap hK hab
  covariant a b τ _ := ae_of_all _ fun ω => tsDisp_shift τ a b ω
  additive a b c _ _ := ae_of_all _ fun ω => tsDisp_add a b c ω
  continuous ω := (ω.2.continuous.comp NNReal.continuous_coe).sub continuous_const

theorem memLp_envDrift : MemLp (envDrift hd) 2 Q.measure := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  refine MemLp.of_bound (measurable_envDrift hd).aestronglyMeasurable
    (driftBound d D.ellipticity) ?_
  filter_upwards [Q.regular] with x hx
  exact (pi_norm_le_iff_of_nonneg (driftBound_nonneg _)).2 fun j => by
    rw [Real.norm_eq_abs]
    exact abs_reducedDrift_le hΛ hx _ 0 j

include hQ hap hK in
/-- The rescaled forward path under the two-sided law has the annealed law of the quenched path
laws. -/
theorem integral_rescale_dfgwPath (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω)))
    (hX : IsDFGWAntisymmetricFamily (tsLaw Q K) tsState tsShift tsRefl (tsDisp (d := d)))
    (F : BoundedContinuousFunction (Path d) ℝ) (ε : ℝ) :
    ∫ ω, F (rescalePath ε (dfgwPath hX ω)) ∂tsLaw Q K =
      ∫ ω, ∫ γ, F (rescalePath ε γ) ∂originLaw Y ω ∂Q.measure := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hpath : ∀ ω, dfgwPath hX ω = tsFwdPath ω := fun ω => by
    ext t j
    rfl
  simp_rw [hpath]
  let G : FieldPair d × Path d → ℝ := fun z => F (rescalePath ε z.2)
  have hGc : Continuous fun γ : Path d => F (rescalePath ε γ) :=
    F.continuous.comp (TimeChangeCovariance.continuous_rescalePath ε)
  have hGm : Measurable G := hGc.measurable.comp measurable_snd
  have hGi : Integrable G (Q.measure ⊗ₘ originKernel K) :=
    Integrable.of_bound hGm.aestronglyMeasurable ‖F‖ (ae_of_all _ fun z => F.norm_coe_le_norm _)
  have h := integral_tsLaw_split_fwd hd D Q hap hK (F₀ := fun _ => 1) measurable_const
    (fun _ => by simp) (Lb := []) (fun _ h => (List.not_mem_nil h).elim) hGm hGi
  simp only [tsBwdProd, one_mul, chainMean] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [hY, Q.regular, hQ] with x hYx hx hsm
  have hsv := (reducedGenerator_solves_iff hsm.1 _ 0 0 _).1 hYx
  have heq := reducedKernel_eq_of_solves hΛ (⟨0, by omega⟩ : Fin d) 0 hK (by omega) hx 0 hsv
  simp only [originLaw, Kernel.comap_apply, G]
  rw [heq]

end Application

end EinsteinFull.External.Draft
