import EinsteinFull.Calculus.C5ResponseDriftSpatialRepresentative
import EinsteinFull.Calculus.C6ResponseVelocityCesaro

open MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- Spatial almost everywhere equality transports to almost every positive time
under the literal null-occupation contract of the supplied path law. -/
theorem response_spatial_ae_path_time_transport {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (hOccupation : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N)
    (f g : FieldPair d × Vec d → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfg : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (ω, x) = g (ω, x)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᵐ ω ∂Q.measure,
      ∀ᵐ γ ∂Y (0, ω), f (ω, γ t.toNNReal) = g (ω, γ t.toNNReal) := by
  obtain ⟨κ, hfinite, hκ⟩ := response_finite_originLaw Q Y hprob
  have : ProbabilityTheory.IsFiniteKernel κ := hfinite
  let ν := volume.restrict (Set.Ioi (0 : ℝ))
  let J := Q.measure.compProd κ
  let e : (FieldPair d × Path d) × ℝ → FieldPair d × Vec d :=
    fun p => (p.1.1, p.1.2 p.2.toNNReal)
  have he : Measurable e :=
    (measurable_fst.comp measurable_fst).prodMk
      ((continuous_pathEval d).measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hE : MeasurableSet {p : (FieldPair d × Path d) × ℝ |
      f (e p) = g (e p)} := measurableSet_eq_fun (hf.comp he) (hg.comp he)
  have hgood : MeasurableSet {z : FieldPair d × Path d |
      ∀ᵐ t ∂ν, f (e (z, t)) = g (e (z, t))} := by
    simp only [ae_iff]
    exact measurableSet_eq_fun (measurable_measure_prodMk_left hE.compl) measurable_const
  have hpath : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂κ ω,
      ∀ᵐ t ∂ν, f (e ((ω, γ), t)) = g (e ((ω, γ), t)) := by
    filter_upwards [hOccupation, hfg, hκ] with ω hocc hω hκω
    rw [hκω]
    let N : Set (Vec d) := {x | f (ω, x) ≠ g (ω, x)}
    have hN : MeasurableSet N :=
      (measurableSet_eq_fun (hf.comp (measurable_const.prodMk measurable_id))
        (hg.comp (measurable_const.prodMk measurable_id))).compl
    have hzero : (volume : Measure (Vec d)) N = 0 :=
      measure_eq_zero_iff_ae_notMem.mpr (by
        simpa only [N, Set.mem_ofPred_eq, not_not] using hω)
    exact (hocc N hN hzero).mono fun γ hγ => hγ.mono fun t ht => by
      simpa only [N, Set.mem_ofPred_eq, not_not] using ht
  have hjoint : ∀ᵐ z ∂J, ∀ᵐ t ∂ν,
      f (e (z, t)) = g (e (z, t)) :=
    Measure.ae_compProd_of_ae_ae hgood hpath
  have ht := (Measure.ae_ae_comm hE).mp hjoint
  filter_upwards [ht] with t ht
  have hω := Measure.ae_ae_of_ae_compProd ht
  filter_upwards [hω, hκ] with ω hω hκω
  simpa only [hκω] using hω

/-- Conditional consumer of the exact null-occupation contract. The supplied
martingale law and signed force are retained throughout the drift identification. -/
theorem response_velocity_cesaro_of_rate_of_occupation
    (hreal : node_e_u3A_generators_u23_real_u2D_semigroupStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (lam : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) (lam : ℂ) P)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (hOccupation : ∀ᵐ ω ∂Q.measure, ∀ N : Set (Vec d), MeasurableSet N →
      (volume : Measure (Vec d)) N = 0 →
      ∀ᵐ γ ∂Y (0, ω), ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        γ t.toNNReal ∉ N)
    (velocity : Vec d)
    (hv : HasQuenchedVelocity Q.measure (originLaw Y) velocity) :
    ∀ j : Fin d,
      Tendsto (fun T : ℝ => (T : ℂ)⁻¹ *
        ∫ t in (0 : ℝ)..T, ∫ ω,
          (P t.toNNReal (β j + (lam : ℂ) • a (⟨0, by omega⟩ : Fin d) j)) ω
            ∂reducedLaw Q) atTop (𝓝 (velocity j : ℂ)) := by
  intro j
  let i : Fin d := ⟨0, by omega⟩
  let b : Lp ℂ 2 (reducedLaw Q) := β j + (lam : ℂ) • a i j
  let f : FieldPair d × Vec d → ℂ := fun p => b (translate p.2 (reduce p.1))
  let g : FieldPair d × Vec d → ℂ :=
    fun p => (famB D.ellipticity i lam p.1 p.2 j : ℂ)
  have hf : Measurable f := (Lp.stronglyMeasurable b).measurable.comp
    (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (Probability.measurable_reduce.comp measurable_fst)))
  have hg : Measurable g := Complex.measurable_ofReal.comp
    (measurable_famB D.ellipticity i lam j)
  have hfg : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f (ω, x) = g (ω, x) := by
    filter_upwards [response_forced_drift_observation_spatial_ae d hd D Q hQ β a hβ ha lam,
      Q.regular] with ω hω hreg
    filter_upwards [hω j] with x hx
    simpa only [f, g, b, i, famB, ite_eq_left hreg] using hx
  have ht := response_spatial_ae_path_time_transport Q Y (hY.mono fun _ h => h.1)
    hOccupation f g hf hg hfg
  have hmean : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (∫ ω, P t.toNNReal b ω ∂reducedLaw Q) =
        ∫ ω, ∫ γ, (reducedGenerator i ω lam (fun z => z j) (γ t.toNNReal) : ℂ)
          ∂Y (0, ω) ∂Q.measure := by
    filter_upwards [ht] with t ht
    rw [response_semigroup_mean_path_expectation d hd D.ellipticity
      D.dependenceRange Q (realSemigroupAt_of_stmtV2 hreal hd D Q hQ) lam P hP Y hY
      t.toNNReal b]
    apply integral_congr_ae
    filter_upwards [ht, Q.regular, hQ] with ω hω hreg hsm
    apply integral_congr_ae
    filter_upwards [hω] with γ hγ
    rw [response_reducedGenerator_coordinate hsm.1]
    simpa only [f, g, famB, ite_eq_left hreg] using hγ
  apply (response_complex_drift_primitive_cesaro D Q hQ i lam Y hY hv j).congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
  apply congrArg ((T : ℂ)⁻¹ * ·)
  rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
  exact (integral_congr_ae
    (ae_restrict_of_ae_restrict_of_subset (fun _ ht => ht.1) hmean)).symm

end EinsteinFull.Blueprint
