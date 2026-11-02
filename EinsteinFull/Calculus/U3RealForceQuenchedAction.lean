import EinsteinFull.Calculus.U3ForcedHorizonLaw
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.S2ReducedLawUniquenessSupport
import EinsteinFull.Calculus.C27RealForceRealization
import EinsteinFull.Calculus.C17UnforcedIdentification
import EinsteinFull.Calculus.C2UnforcedProcessSupport
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport

/-! Signed-force support for the actual supplied reduced path laws. -/

open MeasureTheory
open Filter
open ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The pathwise graph dependency identifies the supplied actual reduced law
with a textbook solution on almost every environment. -/
theorem u3_supplied_reduced_law_solves_textbook_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) :
    ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) 0 (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, _, hY₀⟩ := foundation_reduced_textbook_kernel hΛ i lam
  have hactual : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i lam
      (hY₀ ω hω)
      (foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i lam
        (hY₀ ω hω))
  have heq := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q i lam Y Y₀ hY hactual
  filter_upwards [Q.regular, heq] with ω hω heqω
  rw [heqω]
  exact hY₀ ω hω

/-- The signed finite-horizon tilt relates the same two supplied actual laws. -/
theorem u3_supplied_reduced_force_finite_horizon_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, ∀ A : Set (Path d), MeasurableSet[(pathFiltration d) T] A →
      Y (0, ω) A = ∫⁻ γ in A, ENNReal.ofReal (Real.exp
        (lam * ((γ T) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
          (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ∂Y₀ (0, ω) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q i 0 Y₀ hY₀, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q i lam Y hY] with ω hω h₀ h
  exact u3_reduced_force_finite_horizon_law (by omega) hΛ hω i h₀ lam T h

/-- The actual signed finite-horizon density is square-integrable under the
unforced textbook solution. -/
theorem u3_reduced_force_density_memLp_two {d : ℕ} (hd : 1 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i 0)) x P)
    (lam : ℝ) (T : ℝ≥0) :
    MemLp (fun γ : Path d => Real.exp
      (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) 2 P := by
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ T) i - x i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  have hZm : StronglyMeasurable Z :=
    (((u3_reduced_force_density_adapted_integrable hd hΛ hω i hP lam).1 T).mono
      ((pathFiltration d).le T))
  obtain ⟨_, K, hK⟩ := c2_reduced_force_potential_measurable_bounded hΛ hω i lam
  obtain ⟨B, hB, hbound⟩ := c2_path_weight_horizon_bound hK T
  have hmax := c16_reduced_textbook_exp_coordinate_max_integrable hd hΛ hω i hP
    (2 * |lam|) T
  have hZbound : ∀ γ : Path d, Z γ ≤ B * Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) := by
    intro γ
    have hc := c27_exp_coord_le_max i lam x γ T T (le_refl T)
    have hw := hbound T (le_refl T) γ
    rw [abs_of_pos (Real.exp_pos _)] at hw
    have h := mul_le_mul hc hw (Real.exp_pos _).le (Real.exp_pos _).le
    simpa only [Z, sub_eq_add_neg, Real.exp_add, mul_comm] using h
  apply (memLp_two_iff_integrable_sq hZm.aestronglyMeasurable).2
  apply (hmax.const_mul (B ^ 2)).mono' (hZm.pow 2).aestronglyMeasurable
  filter_upwards [] with γ
  have h := hZbound γ
  have hpos : 0 ≤ Z γ := (Real.exp_pos _).le
  have hs : Z γ ^ 2 ≤ (B * Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))) ^ 2 := by
    nlinarith [sq_nonneg (B * Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) - Z γ)]
  rw [Real.norm_eq_abs]
  change |Z γ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg (Z γ))]
  refine hs.trans_eq ?_
  have hexp : (Real.exp (|lam| *
      sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T))) ^ 2 =
      Real.exp (2 * |lam| * sSup ((fun t : ℝ≥0 => |(γ t) i - x i|) '' Set.Icc 0 T)) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, hexp]

/-- The square-integrable signed density belongs to the same supplied
unforced reduced path law, for almost every environment. -/
theorem u3_supplied_reduced_force_density_memLp_two_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, MemLp (fun γ : Path d => Real.exp
      (lam * ((γ T) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) 2 (Y₀ (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q i 0 Y₀ hY₀] with ω hω h₀
  exact u3_reduced_force_density_memLp_two (by omega) hΛ hω i h₀ lam T

/-- The signed tilt is strictly positive: the two supplied path laws have
exactly the same null events up to the chosen horizon. -/
theorem u3_supplied_reduced_force_past_null_iff_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, ∀ A : Set (Path d), MeasurableSet[(pathFiltration d) T] A →
      (Y (0, ω) A = 0 ↔ Y₀ (0, ω) A = 0) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, u3_supplied_reduced_law_solves_textbook_of_pathwise
    (hpath := hpath) hd Q i 0 Y₀ hY₀, u3_supplied_reduced_force_finite_horizon_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY T] with ω hω h₀ htilt
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ T) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  have hZm : Measurable Z := by
    exact (((u3_reduced_force_density_adapted_integrable (by omega) hΛ hω i h₀ lam).1 T).mono
      ((pathFiltration d).le T)).measurable
  have hrev : Y₀ (0, ω) ≪ (Y₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ)) :=
    withDensity_absolutelyContinuous' hZm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun γ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
  have hfwd := withDensity_absolutelyContinuous (Y₀ (0, ω)) (fun γ => ENNReal.ofReal (Z γ))
  intro A hA
  have hA' : MeasurableSet A := (pathFiltration d).le T A hA
  have heq : Y (0, ω) A = (Y₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ)) A := by
    rw [withDensity_apply _ hA']
    exact htilt A hA
  rw [heq]
  exact ⟨fun h => hrev h, fun h => hfwd h⟩

/-- The actual supplied endpoint distributions are mutually absolutely continuous
for every signed force and every fixed time. -/
theorem u3_supplied_reduced_force_endpoint_equivalent_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      Measure.map (fun γ : Path d => γ t) (Y (0, ω)) ≪
          Measure.map (fun γ : Path d => γ t) (Y₀ (0, ω)) ∧
      Measure.map (fun γ : Path d => γ t) (Y₀ (0, ω)) ≪
          Measure.map (fun γ : Path d => γ t) (Y (0, ω)) := by
  filter_upwards [u3_supplied_reduced_force_past_null_iff_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY t] with ω hnull
  have h : ∀ S : Set (Vec d), MeasurableSet S →
      ((Y (0, ω)).map (fun γ : Path d => γ t) S = 0 ↔
        (Y₀ (0, ω)).map (fun γ : Path d => γ t) S = 0) := by
    intro S hS
    change ((Y (0, ω)).map (pathPosition t)) S = 0 ↔
      ((Y₀ (0, ω)).map (pathPosition t)) S = 0
    rw [Measure.map_apply (measurable_pathPosition t) hS,
      Measure.map_apply (measurable_pathPosition t) hS]
    exact hnull _ ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable hS)
  exact ⟨Measure.AbsolutelyContinuous.mk (fun S hS hs => (h S hS).2 hs),
    Measure.AbsolutelyContinuous.mk (fun S hS hs => (h S hS).1 hs)⟩

/-- Equivalence also holds for the actual environment seen from the particle. -/
theorem u3_supplied_environment_endpoint_equivalent_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      Measure.map (fun γ : Path d => translate (γ t) (reduce ω)) (Y (0, ω)) ≪
          Measure.map (fun γ : Path d => translate (γ t) (reduce ω)) (Y₀ (0, ω)) ∧
      Measure.map (fun γ : Path d => translate (γ t) (reduce ω)) (Y₀ (0, ω)) ≪
          Measure.map (fun γ : Path d => translate (γ t) (reduce ω)) (Y (0, ω)) := by
  filter_upwards [u3_supplied_reduced_force_endpoint_equivalent_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY t] with ω h
  let φ : Vec d → FieldPair d := fun x => translate x (reduce ω)
  have hφ : Measurable φ := Probability.continuous_translate.measurable.comp
    (measurable_id.prodMk measurable_const)
  have heq : ∀ P : Measure (Path d),
      P.map (fun γ => translate (γ t) (reduce ω)) =
        (P.map (fun γ : Path d => γ t)).map φ := by
    intro P
    exact (Measure.map_map hφ (measurable_pathPosition t)).symm
  rw [heq, heq]
  constructor <;> apply Measure.AbsolutelyContinuous.mk <;> intro S hS hzero <;>
    rw [Measure.map_apply hφ hS] at hzero ⊢
  · exact h.1 hzero
  · exact h.2 hzero

/-- The supplied signed-force path avoids every reduced-law null set at almost
every positive time. The exceptional path and time sets may depend on the null set. -/
theorem u3_supplied_force_environment_null_occupation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (N : Set (FieldPair d)) (hNm : MeasurableSet N) (hN : reducedLaw Q N = 0) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        translate (γ t.toNNReal) (reduce ω) ∉ N := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hn : ∀ᵐ ρ ∂reducedLaw Q, ρ ∉ N := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hN
  have horbit : ∀ᵐ ρ ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x ρ ∉ N := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure (Vec d)))
      (ν := reducedLaw Q) (hNm.preimage Probability.continuous_translate.measurable).compl).mp
    exact ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hn
  have hpull : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x (reduce ω) ∉ N :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable horbit
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, hpull,
    u3_supplied_reduced_law_solves_textbook_of_pathwise (hpath := hpath) hd Q i lam Y hY]
    with ω hω horbitω htextbook
  have hocc := foundation_reduced_textbook_averaged_occupation_ac_of_two_le
    hd hΛ hω i lam htextbook
  exact c16_ae_path_of_averaged_occupation (Y (0, ω)) hocc horbitω

/-- Reduced-law almost-everywhere equality transfers to the actual signed
environment path for almost every positive time. -/
theorem u3_supplied_force_environment_ae_eq_occupation_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (f g : FieldPair d → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        f (translate (γ t.toNNReal) (reduce ω)) =
          g (translate (γ t.toNNReal) (reduce ω)) := by
  let N : Set (FieldPair d) := {ρ | f ρ ≠ g ρ}
  have hNm : MeasurableSet N := (measurableSet_eq_fun hf hg).compl
  have hN : reducedLaw Q N = 0 := by
    change ∀ᵐ ρ ∂reducedLaw Q, f ρ = g ρ at hfg
    simpa only [N] using (ae_iff.mp hfg)
  filter_upwards [u3_supplied_force_environment_null_occupation_of_pathwise
    (hpath := hpath) hd Q i lam Y hY N hNm hN] with ω hω
  filter_upwards [hω] with γ hγ
  filter_upwards [hγ] with t ht
  exact not_not.mp ht

/-- Bounded continuous observations of an actual unforced solution have
stationary annealed means at almost every positive time. -/
theorem u3_unforced_annealed_mean_ae_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      (∫ ω, ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure) =
        ∫ ρ, g ρ ∂reducedLaw Q := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
  let S : Set (FieldPair d) := {ρ | F ρ = g ρ}
  have hS : MeasurableSet S := measurableSet_eq_fun (Lp.stronglyMeasurable F).measurable g.continuous.measurable
  have hN : reducedLaw Q Sᶜ = 0 := by
    have h := BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g
    change ∀ᵐ ρ ∂reducedLaw Q, F ρ = g ρ at h
    change reducedLaw Q {ρ | ¬ F ρ = g ρ} = 0
    exact ae_iff.mp h
  have hjoint := c17_unforced_occupation_ae_mem (hpath := hpath) hd Q K hK S hS hN
  have htime : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ z ∂(Q.measure ⊗ₘ K),
        F (translate (z.2 t.toNNReal) (reduce z.1)) =
          g (translate (z.2 t.toNNReal) (reduce z.1)) := by
    have hpair := Measure.ae_ae_of_ae_prod hjoint
    simpa only [S, Set.mem_setOf_eq] using hpair
  let Y : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)) := hK
  filter_upwards [htime] with t ht
  have ht' := Measure.ae_ae_of_ae_compProd ht
  have ha := c27_zero_force_quenched_action_of_unforced (hunforced := hunforced) hd Q Y hY t.toNNReal F
  have hint : (∫ ω, ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure) =
      ∫ ω, forcedComplexEvolution Q ⟨0, by omega⟩ 0 t.toNNReal F (reduce ω) ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [ht', ha] with ω hω hact
    change Integrable _ (K ω) ∧ _ = ∫ γ : Path d, F (translate (γ t.toNNReal) (reduce ω)) ∂K ω at hact
    rw [hact.2]
    exact integral_congr_ae (hω.mono fun γ hγ => hγ.symm)
  rw [hint, ← integral_map Probability.measurable_reduce.aemeasurable
    (Lp.stronglyMeasurable _).aestronglyMeasurable]
  change (∫ ρ, forcedComplexEvolution Q ⟨0, by omega⟩ 0 t.toNNReal F ρ ∂reducedLaw Q) = _
  rw [integral_forcedComplexEvolution_zero]
  exact integral_congr_ae (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g)

/-- Continuity extends stationary bounded-test means to every time. -/
theorem u3_unforced_annealed_mean_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (g : BoundedContinuousFunction (FieldPair d) ℂ) (t : ℝ≥0) :
    (∫ ω, ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure) =
      ∫ ρ, g ρ ∂reducedLaw Q := by
  let m : ℝ → ℂ := fun s => ∫ ω, ∫ γ : Path d,
    g (translate (γ s.toNNReal) (reduce ω)) ∂K ω ∂Q.measure
  have hm : Continuous m := c17_continuous_annealed_environment_mean Q K g
  have hae : m =ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun _ => ∫ ρ, g ρ ∂reducedLaw Q :=
    u3_unforced_annealed_mean_ae_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK g
  have hpos : Set.EqOn m (fun _ => ∫ ρ, g ρ ∂reducedLaw Q) (Set.Ioi (0 : ℝ)) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioi hm.continuousOn continuous_const.continuousOn
  have hclosed : IsClosed {s : ℝ | m s = ∫ ρ, g ρ ∂reducedLaw Q} :=
    isClosed_eq hm continuous_const
  have hall := closure_minimal hpos hclosed
  have ht : (t : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    rw [closure_Ioi]
    exact t.coe_nonneg
  have hh : m (t : ℝ) = ∫ ρ, g ρ ∂reducedLaw Q := hall ht
  simpa only [m, Real.toNNReal_coe] using hh

/-- The actual unforced environment endpoint has exactly the reduced law
under the annealed joint law, at every nonnegative time. -/
theorem u3_unforced_annealed_marginal_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) :
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q := by
  apply c17_unforced_annealed_marginal_of_bounded_means Q K
  intro g s
  exact u3_unforced_annealed_mean_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK g s

/-- Every reduced-law L² observation is square-integrable at a fixed time
under almost every supplied unforced path law. -/
theorem u3_unforced_endpoint_memLp_two_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (K ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let E : FieldPair d × Path d → FieldPair d :=
    fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hmap := u3_unforced_annealed_marginal_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK t
  have hjoint : MemLp (fun z => f (E z)) 2 (Q.measure ⊗ₘ K) := by
    have hf : MemLp (fun ρ => f ρ) 2 (Measure.map E (Q.measure ⊗ₘ K)) := by
      rw [hmap]
      exact Lp.memLp f
    exact hf.comp_of_map hE.aemeasurable
  have hsq := (memLp_two_iff_integrable_sq_norm hjoint.aestronglyMeasurable).mp hjoint
  have hsections := ((Measure.integrable_compProd_iff hsq.aestronglyMeasurable).mp hsq).1
  filter_upwards [hsections] with ω hω
  have hmeas : StronglyMeasurable (fun γ : Path d => f (translate (γ t) (reduce ω))) :=
    (Lp.stronglyMeasurable f).comp_measurable
      ((Probability.continuous_translate.comp
        ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk
          continuous_const)).measurable)
  apply (memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable).mpr
  exact hω

/-- Every reduced-law L² observation is integrable at a fixed time under the
actual supplied signed-force path law. -/
theorem u3_supplied_force_endpoint_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, hmarkov, hactual⟩ :=
    foundation_reduced_actual_kernel hd hΛ ⟨0, by omega⟩ 0
  letI : IsMarkovKernel Y₀ := hmarkov
  let K : Kernel (FieldPair d) (Path d) :=
    Y₀.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  letI : IsMarkovKernel K := inferInstance
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := hY₀
  filter_upwards [u3_unforced_endpoint_memLp_two_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK t f,
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y₀ hY₀ t,
    u3_supplied_reduced_force_finite_horizon_of_pathwise (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y₀ Y hY₀ hY t] with ω hU hZ htilt
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) ⟨0, by omega⟩ - (0 : Vec d) ⟨0, by omega⟩) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ 0 (γ u.toNNReal) ⟨0, by omega⟩ +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) ⟨0, by omega⟩ ⟨0, by omega⟩))
  let U : Path d → ℂ := fun γ => f (translate (γ t) (reduce ω))
  let R := (Y₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ))
  change MemLp U 2 (Y₀ (0, ω)) at hU
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  have hmul : Integrable (fun γ => (Z γ : ℂ) * U γ) (Y₀ (0, ω)) :=
    hZ.ofReal.integrable_mul hU
  have hR : Integrable U R := by
    apply (integrable_withDensity_iff_integrable_smul₀' hZ.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun γ => ENNReal.ofReal_lt_top)).2
    convert hmul using 1
    funext γ
    simp only [ENNReal.toReal_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le), Complex.real_smul]
  have heq : Measure.map (fun γ : Path d => γ t) (Y (0, ω)) =
      Measure.map (fun γ : Path d => γ t) R := by
    ext S hS
    change (Measure.map (pathPosition t) (Y (0, ω))) S =
      (Measure.map (pathPosition t) R) S
    rw [Measure.map_apply (measurable_pathPosition t) hS,
      Measure.map_apply (measurable_pathPosition t) hS,
      withDensity_apply _ (hS.preimage (measurable_pathPosition t))]
    exact htilt _ ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable hS)
  let V : Vec d → ℂ := fun x => f (translate x (reduce ω))
  have hV : StronglyMeasurable V := (Lp.stronglyMeasurable f).comp_measurable
    (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hmap : Integrable V (Measure.map (fun γ : Path d => γ t) R) :=
    (integrable_map_measure hV.aestronglyMeasurable (measurable_pathPosition t).aemeasurable).2 hR
  rw [← heq] at hmap
  exact hmap.comp_measurable (measurable_pathPosition t)

/-- A reduced-law almost-everywhere equality is respected at each fixed time
by the supplied signed-force environment process. -/
theorem u3_supplied_force_endpoint_ae_eq_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f g : FieldPair d → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfg : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      f (translate (γ t) (reduce ω)) = g (translate (γ t) (reduce ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, hmarkov, hactual⟩ :=
    foundation_reduced_actual_kernel hd hΛ ⟨0, by omega⟩ 0
  letI : IsMarkovKernel Y₀ := hmarkov
  let K : Kernel (FieldPair d) (Path d) :=
    Y₀.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  letI : IsMarkovKernel K := inferInstance
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := hY₀
  let E : FieldPair d × Path d → FieldPair d :=
    fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hmap : ∀ᵐ ρ ∂Measure.map E (Q.measure ⊗ₘ K), f ρ = g ρ := by
    rw [u3_unforced_annealed_marginal_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK t]
    exact hfg
  have hjoint : ∀ᵐ z ∂(Q.measure ⊗ₘ K), f (E z) = g (E z) :=
    ae_of_ae_map hE.aemeasurable hmap
  have hsections := Measure.ae_ae_of_ae_compProd hjoint
  filter_upwards [hsections, u3_supplied_environment_endpoint_equivalent_of_pathwise
    (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y₀ Y hY₀ hY t] with ω hω hac
  let φ : Path d → FieldPair d := fun γ => translate (γ t) (reduce ω)
  have hφ : Measurable φ := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk
      continuous_const)).measurable
  have hm : MeasurableSet {ρ | f ρ = g ρ} := measurableSet_eq_fun hf hg
  have hmap : ∀ᵐ ρ ∂Measure.map φ (Y₀ (0, ω)), f ρ = g ρ :=
    (ae_map_iff hφ.aemeasurable hm).2 hω
  exact (ae_map_iff hφ.aemeasurable hm).1 (hac.1.ae_le hmap)

/-- The supplied signed endpoint expectation equals the actual exponential
weight under any supplied unforced solution. -/
theorem u3_supplied_force_endpoint_integral_eq_tilt_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : FieldPair d → ℂ) (hf : StronglyMeasurable f) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) =
        ∫ γ : Path d, (Real.exp
          (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
            (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
              (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i)) : ℂ) *
          f (translate (γ t) (reduce ω)) ∂Y₀ (0, ω) := by
  filter_upwards [u3_supplied_reduced_force_density_memLp_two_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ hY₀ t, u3_supplied_reduced_force_finite_horizon_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY t] with ω hZ htilt
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let R := (Y₀ (0, ω)).withDensity (fun γ => ENNReal.ofReal (Z γ))
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  have heq : Measure.map (fun γ : Path d => γ t) (Y (0, ω)) =
      Measure.map (fun γ : Path d => γ t) R := by
    ext S hS
    change (Measure.map (pathPosition t) (Y (0, ω))) S =
      (Measure.map (pathPosition t) R) S
    rw [Measure.map_apply (measurable_pathPosition t) hS,
      Measure.map_apply (measurable_pathPosition t) hS,
      withDensity_apply _ (hS.preimage (measurable_pathPosition t))]
    exact htilt _ ((Filtration.stronglyAdapted_natural
      (fun s => (measurable_pathPosition (d := d) s).stronglyMeasurable) t).measurable hS)
  let V : Vec d → ℂ := fun x => f (translate x (reduce ω))
  have hV : StronglyMeasurable V := hf.comp_measurable
    (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  calc
    (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)) =
        ∫ x, V x ∂Measure.map (fun γ : Path d => γ t) (Y (0, ω)) :=
      (integral_map (measurable_pathPosition t).aemeasurable hV.aestronglyMeasurable).symm
    _ = ∫ x, V x ∂Measure.map (fun γ : Path d => γ t) R := by rw [heq]
    _ = ∫ γ : Path d, V (γ t) ∂R :=
      integral_map (measurable_pathPosition t).aemeasurable hV.aestronglyMeasurable
    _ = ∫ γ : Path d, (Z γ : ℂ) * V (γ t) ∂Y₀ (0, ω) := by
      rw [integral_withDensity_eq_integral_toReal_smul₀ hZ.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun γ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [] with γ
      simp only [ENNReal.toReal_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le), Complex.real_smul]
    _ = _ := rfl

/-- Fixed-time L² integrability also holds for any supplied unforced solution,
without requiring its kernel to be Markov on exceptional environments. -/
theorem u3_supplied_unforced_endpoint_memLp_two_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      MemLp (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (Y (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, hmarkov, hactual⟩ :=
    foundation_reduced_actual_kernel hd hΛ ⟨0, by omega⟩ 0
  letI : IsMarkovKernel Y₀ := hmarkov
  let K : Kernel (FieldPair d) (Path d) :=
    Y₀.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  letI : IsMarkovKernel K := inferInstance
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := hY₀
  have heq := reducedOriginLaw_ae_unique_of_pathwise (hpath := hpath) Q ⟨0, by omega⟩ 0
    Y Y₀ hY hY₀
  filter_upwards [heq, u3_unforced_endpoint_memLp_two_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK t f]
    with ω he hmem
  change MemLp (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (Y₀ (0, ω)) at hmem
  rw [he]
  exact hmem

/-- The weighted L² endpoint observable is integrable under any supplied
unforced solution, for every signed force. -/
theorem u3_supplied_force_weighted_endpoint_integrable_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure, Integrable (fun γ : Path d => (Real.exp
      (lam * ((γ t) ⟨0, by omega⟩ - (0 : Vec d) ⟨0, by omega⟩) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ 0 (γ u.toNNReal) ⟨0, by omega⟩ +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) ⟨0, by omega⟩ ⟨0, by omega⟩)) : ℂ) *
      f (translate (γ t) (reduce ω))) (Y₀ (0, ω)) := by
  filter_upwards [u3_supplied_unforced_endpoint_memLp_two_of_deps (hunforced := hunforced) (hpath := hpath) hd Q Y₀ hY₀ t f,
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q ⟨0, by omega⟩ lam Y₀ hY₀ t]
    with ω hU hZ
  exact hZ.ofReal.integrable_mul hU

/-- Every signed finite-horizon density has total mass one under any
supplied unforced solution. -/
theorem u3_supplied_force_density_lintegral_eq_one_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, (∫⁻ γ : Path d, ENNReal.ofReal (Real.exp
      (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ∂Y₀ (0, ω)) = 1 := by
  filter_upwards [hY, u3_supplied_reduced_force_finite_horizon_of_pathwise
    (hpath := hpath) hd Q i lam Y₀ Y hY₀ hY t] with ω hω htilt
  letI : IsProbabilityMeasure (Y (0, ω)) := hω.1
  have h := htilt Set.univ MeasurableSet.univ
  simpa only [Measure.restrict_univ, measure_univ] using h.symm

/-- The square of the signed density is bounded uniformly by the density at
twice the force, times the ellipticity-dependent exponential factor. -/
theorem u3_reduced_force_density_sq_le_double_force {d : ℕ} {Λ₀ : ℝ}
    (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) (t : ℝ≥0) (γ : Path d) :
    let Z : ℝ → ℝ := fun a => Real.exp
      (a * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (a * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (a ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
    Z lam ^ 2 ≤ Z (2 * lam) * Real.exp
      (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)) := by
  intro Z
  let q : ℝ → ℝ → ℝ := fun a u =>
    a * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
      (a ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i
  obtain ⟨_, _, hq₁⟩ := c25_reduced_force_path_potential_integrable hΛ hω i lam
  obtain ⟨_, _, hq₂⟩ := c25_reduced_force_path_potential_integrable hΛ hω i (2 * lam)
  have h₁ : IntegrableOn (q lam) (Set.Ioc (0 : ℝ) (t : ℝ)) := (hq₁ γ t).1
  have h₂ : IntegrableOn (q (2 * lam)) (Set.Ioc (0 : ℝ) (t : ℝ)) := (hq₂ γ t).1
  have hfinite : volume (Set.Ioc (0 : ℝ) (t : ℝ)) < ⊤ := by simp
  have hbound := norm_setIntegral_le_of_norm_le_const
    (f := fun u : ℝ => q (2 * lam) u - 2 * q lam u)
    (C := lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀)) hfinite (fun u _ => by
      have he : q (2 * lam) u - 2 * q lam u =
          lam ^ 2 * reducedCoefficient ω (γ u.toNNReal) i i := by
        dsimp [q]
        ring
      rw [he, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg lam)]
      exact mul_le_mul_of_nonneg_left (abs_reducedCoefficient_le hΛ hω _ i i) (sq_nonneg lam))
  have hdifference : |(∫ u in Set.Ioc (0 : ℝ) (t : ℝ), q (2 * lam) u) -
      2 * (∫ u in Set.Ioc (0 : ℝ) (t : ℝ), q lam u)| ≤
      lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ) := by
    simpa only [Real.norm_eq_abs, integral_sub h₂ (h₁.const_mul 2), integral_const_mul,
      Real.volume_real_Ioc_of_le t.coe_nonneg, sub_zero] using hbound
  have hupper := (abs_le.mp hdifference).2
  dsimp [Z]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  change (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), q lam u) +
      (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), q lam u) ≤
    ((2 * lam) * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ), q (2 * lam) u) +
      lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ)
  linarith

/-- The signed density has a deterministic, environment-uniform second-moment
bound under any supplied unforced reduced law. -/
theorem u3_supplied_force_density_second_moment_bound_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫⁻ γ : Path d, ENNReal.ofReal ((Real.exp
        (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
          (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
            (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) ^ 2) ∂Y₀ (0, ω)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₂, _, hactual⟩ := foundation_reduced_actual_kernel hd hΛ i (2 * lam)
  have hY₂ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω (2 * lam)) 0 (Y₂ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  filter_upwards [Q.regular, u3_supplied_force_density_lintegral_eq_one_of_pathwise
    (hpath := hpath) hd Q i (2 * lam) Y₀ Y₂ hY₀ hY₂ t] with ω hω hnorm
  let Z : ℝ → Path d → ℝ := fun a γ => Real.exp
    (a * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (a * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (a ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  let B : ℝ := Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))
  change (∫⁻ γ, ENNReal.ofReal (Z (2 * lam) γ) ∂Y₀ (0, ω)) = 1 at hnorm
  change (∫⁻ γ, ENNReal.ofReal (Z lam γ ^ 2) ∂Y₀ (0, ω)) ≤ ENNReal.ofReal B
  calc
    (∫⁻ γ, ENNReal.ofReal (Z lam γ ^ 2) ∂Y₀ (0, ω)) ≤
        ∫⁻ γ, ENNReal.ofReal (Z (2 * lam) γ * B) ∂Y₀ (0, ω) := by
      apply lintegral_mono
      intro γ
      exact ENNReal.ofReal_le_ofReal (u3_reduced_force_density_sq_le_double_force hΛ hω i lam t γ)
    _ = (∫⁻ γ, ENNReal.ofReal (Z (2 * lam) γ) ∂Y₀ (0, ω)) * ENNReal.ofReal B := by
      simp_rw [ENNReal.ofReal_mul (show 0 ≤ Z (2 * lam) _ from (Real.exp_pos _).le)]
      exact lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal B := by rw [hnorm, one_mul]

/-- A uniform extended L²-norm bound for the signed density. -/
theorem u3_supplied_force_density_eLpNorm_two_bound_of_pathwise
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (i : Fin d) (lam : ℝ) (Y₀ : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω 0) 0 (Y₀ (0, ω)))
    (t : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure, eLpNorm (fun γ : Path d => Real.exp
      (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
        (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
          (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))) 2 (Y₀ (0, ω)) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) := by
  filter_upwards [u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t,
    u3_supplied_force_density_second_moment_bound_of_pathwise (hpath := hpath) hd Q i lam Y₀ hY₀ t]
    with ω hZ hbound
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) i - (0 : Vec d) i) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) i 0 (γ u.toNNReal) i +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) i i))
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  change (∫⁻ γ, ENNReal.ofReal (Z γ ^ 2) ∂Y₀ (0, ω)) ≤ _ at hbound
  change eLpNorm Z 2 (Y₀ (0, ω)) ≤ _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZ.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hz : ∀ γ, ‖Z γ‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (Z γ ^ 2) := by
    intro γ
    rw [ENNReal.rpow_two, Real.enorm_eq_ofReal (show 0 ≤ Z γ from (Real.exp_pos _).le),
      ← ENNReal.ofReal_pow (show 0 ≤ Z γ from (Real.exp_pos _).le)]
  simpa only [ENNReal.toReal_ofNat, hz] using hbound

/-- Quenched signed endpoint expectations are controlled by the unforced
endpoint L² norm, with an environment-independent exponential factor. -/
theorem u3_supplied_force_endpoint_enorm_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y₀ Y : QuenchedPathLaws d)
    (hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ ≤
        ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
          eLpNorm (fun γ : Path d => f (translate (γ t) (reduce ω))) 2 (Y₀ (0, ω)) := by
  filter_upwards [u3_supplied_force_endpoint_integral_eq_tilt_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ Y hY₀ hY t f (Lp.stronglyMeasurable f),
    u3_supplied_reduced_force_density_memLp_two_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ hY₀ t,
    u3_supplied_unforced_endpoint_memLp_two_of_deps (hunforced := hunforced) (hpath := hpath) hd Q Y₀ hY₀ t f,
    u3_supplied_force_density_eLpNorm_two_bound_of_pathwise (hpath := hpath) hd Q
      ⟨0, by omega⟩ lam Y₀ hY₀ t] with ω heq hZ hU hbound
  let Z : Path d → ℝ := fun γ => Real.exp
    (lam * ((γ t) ⟨0, by omega⟩ - (0 : Vec d) ⟨0, by omega⟩) - ∫ u in Set.Ioc (0 : ℝ) (t : ℝ),
      (lam * forcedDrift (reducedCoefficient ω) ⟨0, by omega⟩ 0 (γ u.toNNReal) ⟨0, by omega⟩ +
        (lam ^ 2 / 2) * reducedCoefficient ω (γ u.toNNReal) ⟨0, by omega⟩ ⟨0, by omega⟩))
  let U : Path d → ℂ := fun γ => f (translate (γ t) (reduce ω))
  change MemLp Z 2 (Y₀ (0, ω)) at hZ
  change MemLp U 2 (Y₀ (0, ω)) at hU
  change eLpNorm Z 2 (Y₀ (0, ω)) ≤ _ at hbound
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Y₀ (0, ω))
    Real.HolderConjugate.two_two hZ.aemeasurable.enorm hU.aemeasurable.enorm
  have hholder : (∫⁻ γ, ‖Z γ‖ₑ * ‖U γ‖ₑ ∂Y₀ (0, ω)) ≤
      eLpNorm Z 2 (Y₀ (0, ω)) * eLpNorm U 2 (Y₀ (0, ω)) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hZ.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU.aestronglyMeasurable]
    simpa only [Pi.mul_apply, ENNReal.toReal_ofNat] using hh
  rw [heq]
  change ‖∫ γ, (Z γ : ℂ) * U γ ∂Y₀ (0, ω)‖ₑ ≤ _
  calc
    _ ≤ ∫⁻ γ, ‖(Z γ : ℂ) * U γ‖ₑ ∂Y₀ (0, ω) := enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ γ, ‖Z γ‖ₑ * ‖U γ‖ₑ ∂Y₀ (0, ω) := by
      apply lintegral_congr
      intro γ
      rw [enorm_mul]
      congr 1
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [Real.norm_eq_abs] using Complex.norm_real (Z γ)
    _ ≤ eLpNorm Z 2 (Y₀ (0, ω)) * eLpNorm U 2 (Y₀ (0, ω)) := hholder
    _ ≤ _ := mul_le_mul' hbound le_rfl

/-- The annealed absolute signed endpoint expectation is controlled by the
initial reduced-law L² norm, uniformly over the supplied signed path law. -/
theorem u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨Y₀, hmarkov, hactual⟩ := foundation_reduced_actual_kernel hd hΛ ⟨0, by omega⟩ 0
  letI : IsMarkovKernel Y₀ := hmarkov
  let K : Kernel (FieldPair d) (Path d) :=
    Y₀.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  letI : IsMarkovKernel K := inferInstance
  have hY₀ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (Y₀ (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hactual ω hω
  have hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω) := hY₀
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  let F : FieldPair d × Path d → ℝ≥0∞ := fun z => ‖f (E z)‖ₑ ^ (2 : ℝ)
  have hF : Measurable F := ((Lp.stronglyMeasurable f).measurable.comp hE).enorm.pow_const _
  let G : FieldPair d → ℝ≥0∞ := fun ω => ∫⁻ γ, F (ω, γ) ∂K ω
  have hG : Measurable G := hF.lintegral_kernel_prod_right
  have hGint : (∫⁻ ω, G ω ∂Q.measure) =
      ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂reducedLaw Q := by
    change (∫⁻ ω, ∫⁻ γ, F (ω, γ) ∂K ω ∂Q.measure) = _
    rw [← Measure.lintegral_compProd hF]
    have hmap := u3_unforced_annealed_marginal_of_deps (hunforced := hunforced) (hpath := hpath) hd Q K hK t
    calc
      _ = ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂Measure.map E (Q.measure ⊗ₘ K) :=
        (lintegral_map ((Lp.stronglyMeasurable f).measurable.enorm.pow_const _) hE).symm
      _ = _ := congrArg (fun μ : Measure (FieldPair d) => ∫⁻ ρ, ‖f ρ‖ₑ ^ (2 : ℝ) ∂μ) hmap
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq Q.measure
    Real.HolderConjugate.two_two (f := fun _ : FieldPair d => (1 : ℝ≥0∞)) measurable_const.aemeasurable (hG.pow_const (1 / 2 : ℝ)).aemeasurable
  have hroot : (∫⁻ ω, G ω ^ (1 / 2 : ℝ) ∂Q.measure) ≤
      (∫⁻ ω, G ω ∂Q.measure) ^ (1 / 2 : ℝ) := by
    have hpow : ∀ ω, (G ω ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = G ω := by
      intro ω
      rw [← ENNReal.rpow_mul]
      norm_num
    simpa only [Pi.mul_apply, one_mul, ENNReal.one_rpow, lintegral_one,
      measure_univ, hpow] using hholder
  let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
  have hbound := u3_supplied_force_endpoint_enorm_bound_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y₀ Y hY₀ hY t f
  have hpoint : ∀ᵐ ω ∂Q.measure,
      ‖∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ ≤ B * G ω ^ (1 / 2 : ℝ) := by
    filter_upwards [hbound] with ω hω
    apply hω.trans
    apply mul_le_mul' le_rfl
    have hU : AEStronglyMeasurable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y₀ (0, ω)) :=
      ((Lp.stronglyMeasurable f).comp_measurable
        ((Probability.continuous_translate.comp
          ((continuous_eval.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const)).measurable)).aestronglyMeasurable
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hU]
    simp only [ENNReal.toReal_ofNat]
    rfl
  calc
    _ ≤ ∫⁻ ω, B * G ω ^ (1 / 2 : ℝ) ∂Q.measure := lintegral_mono_ae hpoint
    _ = B * (∫⁻ ω, G ω ^ (1 / 2 : ℝ) ∂Q.measure) := lintegral_const_mul _ (hG.pow_const _)
    _ ≤ B * (∫⁻ ω, G ω ∂Q.measure) ^ (1 / 2 : ℝ) := mul_le_mul' le_rfl hroot
    _ = _ := by
      rw [hGint, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (Lp.stronglyMeasurable f).aestronglyMeasurable]
      simp only [ENNReal.toReal_ofNat]
      rfl

/-- The annealed absolute endpoint observable, before taking the path
expectation, is bounded by its reduced-law L² norm. -/
theorem u3_supplied_force_endpoint_annealed_absolute_bound_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫⁻ ω, ∫⁻ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ₑ ∂Y (0, ω) ∂Q.measure) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ) *
        eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
  let g : FieldPair d → ℂ := fun ρ => (‖f ρ‖ : ℂ)
  have hg : MemLp g 2 (reducedLaw Q) := (Lp.memLp f).norm.ofReal
  let G : Lp ℂ 2 (reducedLaw Q) := hg.toLp g
  have heq := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
    (fun ρ => G ρ) g (Lp.stronglyMeasurable G).measurable
    (Complex.continuous_ofReal.measurable.comp (Lp.stronglyMeasurable f).measurable.norm) hg.coeFn_toLp
  have hint := u3_supplied_force_endpoint_integrable_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t f
  have hrep : ∀ᵐ ω ∂Q.measure,
      (∫⁻ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ₑ ∂Y (0, ω)) =
        ‖∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ := by
    filter_upwards [heq, hint] with ω he hi
    have h : (∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂Y (0, ω)) =
        ((∫ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ ∂Y (0, ω)) : ℂ) := by
      rw [integral_congr_ae he]
    rw [h]
    have henorm : ‖((∫ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ ∂Y (0, ω)) : ℂ)‖ₑ =
        ‖∫ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ ∂Y (0, ω)‖ₑ := by
      rw [integral_complex_ofReal]
      apply enorm_eq_iff_norm_eq.mpr
      simpa only [Real.norm_eq_abs] using Complex.norm_real
        (∫ γ : Path d, ‖f (translate (γ t) (reduce ω))‖ ∂Y (0, ω))
    rw [henorm, Real.enorm_eq_ofReal (integral_nonneg fun _ => norm_nonneg _),
      ofReal_integral_norm_eq_lintegral_enorm hi]
  have hnorm : eLpNorm (fun ρ => G ρ) 2 (reducedLaw Q) =
      eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q) := by
    rw [eLpNorm_congr_ae hg.coeFn_toLp]
    apply eLpNorm_congr_enorm_ae hg.aestronglyMeasurable (Lp.memLp f).aestronglyMeasurable
    filter_upwards [] with ρ
    apply enorm_eq_iff_norm_eq.mpr
    simp [g]
  calc
    _ = ∫⁻ ω, ‖∫ γ : Path d, G (translate (γ t) (reduce ω)) ∂Y (0, ω)‖ₑ ∂Q.measure :=
      lintegral_congr_ae hrep
    _ ≤ _ := by
      have hb := u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t G
      rwa [hnorm] at hb

/-- Identification on bounded continuous tests extends to every L² class for the
same supplied signed-force path law. The bounded-test identity remains a separate
analytic obligation. -/
theorem u3_real_force_quenched_action_of_bounded_tests
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0)
    (hid : ∀ (g : BoundedContinuousFunction (FieldPair d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)),
      F =ᵐ[reducedLaw Q] (fun ρ => g ρ) →
      (fun ω => forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t F (reduce ω)) =ᵐ[Q.measure]
        fun ω => ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂Y (0, ω))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
      forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω) :=
    hY.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  letI : IsMarkovKernel K := hmarkov
  have : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  have : PolishSpace (FieldPair d) := inferInstance
  let T := forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t
  have hb : ‖T‖ ≤ (‖T‖₊ : ℝ≥0) := le_rfl
  have hidK : ∀ (g : BoundedContinuousFunction (FieldPair d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)),
      F =ᵐ[reducedLaw Q] (fun ρ => g ρ) →
      (fun ω => T F (reduce ω)) =ᵐ[Q.measure]
        fun ω => ∫ ρ, g ρ ∂c2EnvironmentKernel K t ω := by
    intro g F hF
    filter_upwards [hid g F hF, hK] with ω ha hk
    rw [c2EnvironmentKernel_apply]
    have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
      (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
    rw [integral_map hm.aemeasurable g.continuous.aestronglyMeasurable]
    change Y (0, ω) = K ω at hk
    rw [← hk]
    exact ha
  have h := quenched_apply_eq_integral Q.measure reduce Probability.measurable_reduce
    (c2EnvironmentKernel K t) T ‖T‖₊ hb hidK f
  filter_upwards [h, hK] with ω hω hk
  rw [c2EnvironmentKernel_apply] at hω
  have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
    (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
  change Y (0, ω) = K ω at hk
  rw [← hk] at hω
  refine ⟨hω.1.comp_aemeasurable hm.aemeasurable, ?_⟩
  exact hω.2.trans (integral_map hm.aemeasurable
    (Lp.stronglyMeasurable f).aestronglyMeasurable)

/-- The signed-force action holds for every actual constant L² class, at all
times and for the same supplied path law. -/
theorem u3_real_force_quenched_action_const_of_deps
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
    (lam : ℝ) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω lam) 0 (Y (0, ω)))
    (t : ℝ≥0) (c : ℂ) :
    letI := reducedLaw_probability Q
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => (Lp.const 2 (reducedLaw Q) c)
        (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
      forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t
        (Lp.const 2 (reducedLaw Q) c) (reduce ω) =
        ∫ γ : Path d, (Lp.const 2 (reducedLaw Q) c)
          (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Lp ℂ 2 (reducedLaw Q) := Lp.const 2 (reducedLaw Q) c
  have hconst : (fun ρ => F ρ) =ᵐ[reducedLaw Q] fun _ => c :=
    Lp.coeFn_const 2 (reducedLaw Q) c
  have hreduced : ∀ᵐ ω ∂Q.measure, F (reduce ω) = c := by
    have h := ae_of_ae_map Probability.measurable_reduce.aemeasurable hconst
    exact h
  have hend := u3_supplied_force_endpoint_ae_eq_of_deps (hunforced := hunforced) (hpath := hpath) hd Q lam Y hY t
    (fun ρ => F ρ) (fun _ => c) (Lp.stronglyMeasurable F).measurable measurable_const hconst
  have hfix : forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t F = F :=
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ)).map_const t c
  filter_upwards [hY, hreduced, hend] with ω hω hr he
  let : IsProbabilityMeasure (Y (0, ω)) := hω.1
  have hi : Integrable (fun γ : Path d => F (translate (γ t) (reduce ω))) (Y (0, ω)) :=
    (integrable_const c).congr (he.mono fun _ h => h.symm)
  refine ⟨hi, ?_⟩
  change forcedComplexEvolution Q ⟨0, by omega⟩ (lam : ℂ) t F (reduce ω) = _
  rw [hfix, hr, integral_congr_ae he]
  simp

#print axioms u3_real_force_quenched_action_const_of_deps
#print axioms u3_real_force_quenched_action_of_bounded_tests
#print axioms u3_supplied_force_endpoint_annealed_absolute_bound_of_deps
#print axioms u3_supplied_force_endpoint_annealed_lintegral_bound_of_deps
#print axioms u3_supplied_force_endpoint_enorm_bound_of_deps
#print axioms u3_supplied_force_density_eLpNorm_two_bound_of_pathwise
#print axioms u3_supplied_force_density_second_moment_bound_of_pathwise
#print axioms u3_reduced_force_density_sq_le_double_force
#print axioms u3_supplied_force_density_lintegral_eq_one_of_pathwise
#print axioms u3_supplied_force_weighted_endpoint_integrable_of_deps
#print axioms u3_supplied_unforced_endpoint_memLp_two_of_deps
#print axioms u3_supplied_force_endpoint_integral_eq_tilt_of_pathwise
#print axioms u3_supplied_force_endpoint_ae_eq_of_deps
#print axioms u3_supplied_force_endpoint_integrable_of_deps
#print axioms u3_unforced_endpoint_memLp_two_of_deps
#print axioms u3_unforced_annealed_marginal_of_deps
#print axioms u3_unforced_annealed_mean_of_deps
#print axioms u3_unforced_annealed_mean_ae_of_deps
#print axioms u3_supplied_force_environment_ae_eq_occupation_of_pathwise
#print axioms u3_supplied_force_environment_null_occupation_of_pathwise
#print axioms u3_supplied_reduced_force_density_memLp_two_of_pathwise
#print axioms u3_reduced_force_density_memLp_two
#print axioms u3_supplied_environment_endpoint_equivalent_of_pathwise
#print axioms u3_supplied_reduced_force_past_null_iff_of_pathwise
#print axioms u3_supplied_reduced_force_endpoint_equivalent_of_pathwise

#print axioms u3_supplied_reduced_law_solves_textbook_of_pathwise
#print axioms u3_supplied_reduced_force_finite_horizon_of_pathwise

end EinsteinFull
