import EinsteinFull.Work.W3.ForwardFullHorizonEnergySupport
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
import EinsteinFull.Calculus.ComplexCenteringSourceSupport
import EinsteinRelation.Regeneration.HalfSpaces

/-!
# Local space-time energy of the actual forward gradient

The energy density is the sum of squared complex coordinate norms. Joint
representatives are chosen before taking spatial translates. Stationarity and
Fubini then give the literal Lebesgue volume factor, including windows starting
at zero. The endpoint value is the zero extension, not an initial H1 trace.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- Euclidean squared gradient density of a joint coordinate representative. -/
def jointForwardGradientEnergy {d : ℕ}
    (V : Fin d → ℝ × FieldPair d → ℂ) (p : ℝ × FieldPair d) : ℝ :=
  ∑ j, ‖V j p‖ ^ 2

/-- The joint coordinate energy is measurable. -/
theorem measurable_jointForwardGradientEnergy {d : ℕ}
    {V : Fin d → ℝ × FieldPair d → ℂ} (hV : ∀ j, Measurable (V j)) :
    Measurable (jointForwardGradientEnergy V) :=
  Finset.measurable_sum _ fun j _ => (hV j).norm.pow_const 2

/-- Joint representatives preserve the exact Euclidean L2 energy at each time. -/
theorem integral_jointForwardGradientEnergy {d : ℕ}
    {μ : Measure (FieldPair d)}
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)}
    {V : Fin d → ℝ × FieldPair d → ℂ}
    (heq : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[μ] (G s) j) (s : ℝ) :
    Integrable (fun ω => jointForwardGradientEnergy V (s, ω)) μ ∧
      (∫ ω, jointForwardGradientEnergy V (s, ω) ∂μ) = ‖G s‖ ^ 2 := by
  have hi (j : Fin d) : Integrable (fun ω => ‖V j (s, ω)‖ ^ 2) μ :=
    (Lp.memLp ((G s) j)).norm.integrable_sq.congr
      ((heq j s).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)
  refine ⟨integrable_finset_sum _ (fun j _ => hi j), ?_⟩
  change (∫ ω, ∑ j, ‖V j (s, ω)‖ ^ 2 ∂μ) = _
  rw [integral_finset_sum _ (fun j _ => hi j), PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_congr_ae ((heq j s).mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)]
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Genuine time energy supplies integrability on the time/environment product. -/
theorem integrable_jointForwardGradientEnergy {d : ℕ}
    {μ : Measure (FieldPair d)} [IsFiniteMeasure μ]
    {ν : Measure ℝ} {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 μ)}
    {V : Fin d → ℝ × FieldPair d → ℂ} (hV : ∀ j, Measurable (V j))
    (heq : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[μ] (G s) j)
    (hi : Integrable (fun s => ‖G s‖ ^ 2) ν) :
    Integrable (jointForwardGradientEnergy V) (ν.prod μ) := by
  apply (integrable_prod_iff (measurable_jointForwardGradientEnergy hV).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ fun s => (integral_jointForwardGradientEnergy heq s).1, ?_⟩
  have he (s : ℝ) : (∫ ω, ‖jointForwardGradientEnergy V (s, ω)‖ ∂μ) = ‖G s‖ ^ 2 := by
    simp only [jointForwardGradientEnergy,
      Real.norm_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _))]
    exact (integral_jointForwardGradientEnergy heq s).2
  simpa only [he] using hi

/-- Stationarity transfers real joint energy to every finite spatial region. -/
theorem integrable_joint_spatial_energy {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν] (m : Measure (Vec d)) [IsFiniteMeasure m]
    {E : ℝ × FieldPair d → ℝ} (hi : Integrable E (ν.prod Q)) :
    Integrable (fun p : (Vec d × ℝ) × FieldPair d =>
      E (p.1.2, translate p.1.1 p.2)) ((m.prod ν).prod Q) := by
  have ha := measurePreserving_prodAssoc m ν Q
  have hb : Integrable (fun p : (Vec d × ℝ) × FieldPair d => E (p.1.2, p.2))
      ((m.prod ν).prod Q) :=
    (ha.integrable_comp (hi.comp_snd m).aestronglyMeasurable).mpr (hi.comp_snd m)
  have hm := (MeasurePreserving.id (m.prod ν)).skew_product
    (g := fun p ω => translate p.1 ω)
    (Probability.continuous_translate.measurable.comp
      ((measurable_fst.fst).prodMk measurable_snd))
    (ae_of_all _ fun p => (measurePreserving_translate Q hQ p.1).map_eq)
  exact (hm.integrable_comp hb.aestronglyMeasurable).mpr hb

/-- Exact expectation of the samplewise local energy, with unnormalized volume. -/
theorem integral_joint_spatial_energy {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν] (m : Measure (Vec d)) [IsFiniteMeasure m]
    {E : ℝ × FieldPair d → ℝ} (hE : Measurable E) (hi : Integrable E (ν.prod Q)) :
    (∫ ω, ∫ p : Vec d × ℝ, E (p.2, translate p.1 ω) ∂(m.prod ν) ∂Q) =
      m.real univ * ∫ s, ∫ ω, E (s, ω) ∂Q ∂ν := by
  have ht := integrable_joint_spatial_energy Q hQ m hi
  have he : (fun p : Vec d × ℝ => ∫ ω, E (p.2, translate p.1 ω) ∂Q) =
      fun p => ∫ ω, E (p.2, ω) ∂Q := by
    funext p
    have hm : AEStronglyMeasurable (fun ω => E (p.2, ω))
        (Measure.map (translate p.1) Q) :=
      (hE.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [← integral_map (measurePreserving_translate Q hQ p.1).measurable.aemeasurable hm, hQ p.1]
  rw [← integral_integral_swap ht, he,
    integral_prod _ (hi.integral_prod_left.comp_snd m)]
  simp only [integral_const, smul_eq_mul]

/-- One event obtained by countable spatial exhaustion precedes every compact
spatial region. This real-valued form applies directly to squared energy. -/
theorem ae_locally_integrable_joint_spatial_energy {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν] {E : ℝ × FieldPair d → ℝ}
    (hi : Integrable E (ν.prod Q)) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      Integrable (fun p : Vec d × ℝ => E (p.2, translate p.1 ω))
        ((volume.restrict K).prod ν) := by
  have hb (n : ℕ) : ∀ᵐ ω ∂Q,
      Integrable (fun p : Vec d × ℝ => E (p.2, translate p.1 ω))
        ((volume.restrict (Metric.closedBall 0 (n : ℝ))).prod ν) := by
    letI : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
    exact (integrable_joint_spatial_energy Q hQ _ hi).prod_left_ae
  filter_upwards [ae_all_iff.mpr hb] with ω hω
  intro K hK
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨n, hn⟩ := exists_nat_gt r
  have hsub : K ⊆ Metric.closedBall 0 (n : ℝ) :=
    hr.trans (Metric.closedBall_subset_closedBall hn.le)
  have h := hω n
  rw [← Measure.restrict_univ (μ := ν), Measure.prod_restrict] at h ⊢
  exact h.mono_measure (Measure.restrict_mono_set _ (Set.prod_mono hsub Subset.rfl))

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

private instance reducedProbability : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Every joint representative of the actual gradient has the exact local
energy expectation. No choice of representative changes this identity. -/
theorem IsComplexEnvironmentSemigroup.local_gradient_energy_expectation
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {V : Fin d → ℝ × FieldPair d → ℂ} (hV : ∀ j, Measurable (V j))
    (heq : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j)
    {T : ℝ} (hT : 0 ≤ T) (K : Set (Vec d))
    [IsFiniteMeasure (volume.restrict K)] :
    Integrable (fun p : (Vec d × ℝ) × FieldPair d =>
      jointForwardGradientEnergy V (p.1.2, translate p.1.1 p.2))
      (((volume.restrict K).prod (volume.restrict (Icc 0 T))).prod (reducedLaw Q)) ∧
    (∫ ω, ∫ p : Vec d × ℝ, jointForwardGradientEnergy V (p.2, translate p.1 ω)
      ∂((volume.restrict K).prod (volume.restrict (Icc 0 T))) ∂reducedLaw Q) =
      volume.real K * ∫ s in Icc 0 T, ‖hP.gradientOrbit f s‖ ^ 2 := by
  have hi := integrable_jointForwardGradientEnergy hV heq
    (hP.integrableOn_Icc_sq_gradientOrbit_fullHorizon f hT).1
  refine ⟨integrable_joint_spatial_energy (reducedLaw Q) (reducedLaw_stationary Q) _ hi, ?_⟩
  rw [integral_joint_spatial_energy (reducedLaw Q) (reducedLaw_stationary Q) _
    (measurable_jointForwardGradientEnergy hV) hi]
  simp only [Measure.real, Measure.restrict_apply_univ,
    (integral_jointForwardGradientEnergy heq _).2]

/-- The actual semigroup and its centered field share joint gradient
representatives and one local-energy event, before every finite time window
and every compact spatial region. Centering preserves the actual gradient at
positive times; the zero endpoint is only the specified extension. -/
theorem IsComplexEnvironmentSemigroup.exists_joint_local_spacetime_energy
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ (U W : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ Measurable W ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] centeredComplexLp Q (P s.toNNReal f)) ∧
      (∀ p, W p = U p - ∫ ω, P p.1.toNNReal f ω ∂reducedLaw Q) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      (∀ s, 0 < s → HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (centeredComplexLp Q (P s.toNNReal f)) (hP.gradientOrbit f s)) ∧
      (∀ j, (fun ω => V j (0, ω)) =ᵐ[reducedLaw Q] 0) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ T : ℝ, 0 ≤ T → ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ => jointForwardGradientEnergy V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc 0 T))) := by
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  obtain ⟨V, hV, heV⟩ := hP.exists_joint_gradient_representative f
  let m : ℝ → ℂ := fun s => ∫ ω, P s.toNNReal f ω ∂reducedLaw Q
  have hmc : Continuous m := (continuous_complexL2_integral (reducedLaw Q)).comp
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
  let W : ℝ × FieldPair d → ℂ := fun p => U p - m p.1
  have hW : Measurable W := hU.sub (hmc.measurable.comp measurable_fst)
  have heW (s : ℝ) : (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      centeredComplexLp Q (P s.toNNReal f) := by
    filter_upwards [heU s, coeFn_centeredComplexLp Q (P s.toNNReal f)] with ω hu hc
    dsimp only [W, m]
    rw [hu, hc]
  have hl (n : ℕ) := ae_locally_integrable_joint_spatial_energy
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_jointForwardGradientEnergy hV heV
      (hP.integrableOn_Icc_sq_gradientOrbit_fullHorizon f (Nat.cast_nonneg n)).1)
  refine ⟨U, W, V, hU, hW, hV, heU, heW, fun _ => rfl, heV,
    fun s hs => hP.centered_gradientOrbit_spec f hs, ?_, ?_⟩
  · intro j
    have he := heV j 0
    rw [hP.gradientOrbit_zero_fullHorizon f] at he
    exact he.trans (Lp.coeFn_zero _ _ _)
  · filter_upwards [ae_all_iff.mpr hl] with ω hω
    intro T _ K hK
    obtain ⟨n, hn⟩ := exists_nat_gt T
    have h := hω n K hK
    rw [Measure.prod_restrict] at h ⊢
    exact h.mono_measure (Measure.restrict_mono_set _
      (Set.prod_mono Subset.rfl (Icc_subset_Icc_right hn.le)))

/-- Euclidean physical balls fit inside compact comparison sets in the
coordinate topology; the balls themselves keep the Euclidean norm. -/
theorem forward_euclidean_ball_subset_closedBall (a : Vec d) {R : ℝ} (hR : 0 < R) :
    {x : Vec d | euclideanNorm (x - a) < R} ⊆ Metric.closedBall a R := by
  intro x hx
  rw [Metric.mem_closedBall, dist_pi_le_iff hR.le]
  intro j
  rw [Real.dist_eq]
  exact (Regeneration.coordinate_abs_le_euclideanNorm (x - a) j).trans hx.le

/-- A single event covers all finite horizons and all Euclidean spatial balls.
The only premises identify joint representatives of the actual gradient. -/
theorem IsComplexEnvironmentSemigroup.ae_local_spacetime_energy_euclidean_balls
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {V : Fin d → ℝ × FieldPair d → ℂ} (hV : ∀ j, Measurable (V j))
    (heq : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ T : ℝ, 0 ≤ T → ∀ (a : Vec d) (R : ℝ), 0 < R →
      Integrable (fun p : Vec d × ℝ => jointForwardGradientEnergy V (p.2, translate p.1 ω))
        ((volume.restrict {x : Vec d | euclideanNorm (x - a) < R}).prod
          (volume.restrict (Icc 0 T))) := by
  have hl (n : ℕ) := ae_locally_integrable_joint_spatial_energy
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_jointForwardGradientEnergy hV heq
      (hP.integrableOn_Icc_sq_gradientOrbit_fullHorizon f (Nat.cast_nonneg n)).1)
  filter_upwards [ae_all_iff.mpr hl] with ω hω
  intro T _ a R hR
  obtain ⟨n, hn⟩ := exists_nat_gt T
  have h := hω n (Metric.closedBall a R) (isCompact_closedBall a R)
  rw [Measure.prod_restrict] at h ⊢
  exact h.mono_measure (Measure.restrict_mono_set _
    (Set.prod_mono (forward_euclidean_ball_subset_closedBall a hR)
      (Icc_subset_Icc_right hn.le)))

/-- The local expectation has a structural bound with the constant chosen
before the law, signed complex force, initial datum, window and spatial region. -/
theorem forward_local_spacetime_gradient_energy_bound (d : ℕ) (Λ₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
      (V : Fin d → ℝ × FieldPair d → ℂ), (∀ j, Measurable (V j)) →
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) →
      ∀ (T : ℝ), 0 ≤ T → ∀ K : Set (Vec d),
      ∀ (_ : IsFiniteMeasure (volume.restrict K)),
      (∫ ω, ∫ p : Vec d × ℝ, jointForwardGradientEnergy V (p.2, translate p.1 ω)
        ∂((volume.restrict K).prod (volume.restrict (Icc 0 T))) ∂reducedLaw Q) ≤
        volume.real K * (C * Real.exp (C * ‖ζ‖ ^ 2 * T) * ‖f‖ ^ 2) := by
  obtain ⟨C, hC, he⟩ := forward_fullHorizon_gradient_energy d Λ₀
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ P hP f V hV heV T hT K hK
  rw [(hP.local_gradient_energy_expectation f hV heV hT K).2]
  exact mul_le_mul_of_nonneg_left (he Q i ζ P hP f T hT).2 ENNReal.toReal_nonneg

end EinsteinFull
