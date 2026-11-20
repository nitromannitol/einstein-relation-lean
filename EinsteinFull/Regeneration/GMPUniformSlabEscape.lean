import EinsteinFull.Regeneration.GMPUniformExitMinorization
import EinsteinFull.Regeneration.KilledSurvivalIteration
import EinsteinFull.Regeneration.CoordinateSlabExit
import EinsteinFull.Regeneration.SuccessiveSlabExits
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7FiniteTrialSupport

/-!
# One-step slab escape for regular GMP paths

The source endpoint window lies strictly beyond the positive face of any
slab of the same radius containing the starting point. Its minorization
therefore supplies a uniform one-step escape probability.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A source endpoint minorization bounds one-step slab survival. -/
theorem gmp_slab_survival_le_of_source_minorization
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
    (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)
    (τ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hR : 0 < R)
    (hminor : HasSourceMinorization (fun x => G.pathLaw x) τ δ R i) (c : Vec d) :
    ∀ x, G.pathLaw x {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} ≤
      ENNReal.ofReal (1 - δ) := by
  intro x
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  by_cases hx : x ∈ coordinateSlab i c R
  · let B := endpointBall i R x
    let E : Set (Path d) := {γ | γ τ ∈ B}
    have hB : MeasurableSet B :=
      (isOpen_lt ((Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_id.sub continuous_const)) continuous_const).measurableSet
    have hE : MeasurableSet E := hB.preimage (continuous_eval_const τ).measurable
    have hcond : ProbabilityTheory.cond (volume : Measure (Vec d)) B B = 1 :=
      ProbabilityTheory.cond_apply_self (endpointBall_volume_pos i R hR x).ne'
        (endpointBall_volume_ne_top i R hR x)
    have hminor' := hminor x B hB
    rw [hcond, mul_one] at hminor'
    have hsuccess : ENNReal.ofReal δ ≤ G.pathLaw x E := by
      calc
        ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * δ) := ENNReal.ofReal_le_ofReal (by linarith)
        _ ≤ G.pathLaw x {γ | (∀ t : ℝ≥0, t ≤ τ → γ t ∈ couplingRegion i R x) ∧
          γ τ ∈ B} := hminor'
        _ ≤ G.pathLaw x E := measure_mono (fun _ h => h.2)
    have hreal := ENNReal.toReal_mono (measure_ne_top (G.pathLaw x) E) hsuccess
    rw [ENNReal.toReal_ofReal hδ.le] at hreal
    have hwin : δ * (G.pathLaw x).real Set.univ ≤ (G.pathLaw x).real (Set.univ ∩ E) := by
      simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Set.univ_inter]
        using hreal
    have hbound := EinsteinFull.Blueprint.ConditionalTrialExhaustion.measure_sdiff_le_of_success_measure
      (G.pathLaw x) Set.univ E hE δ hδ1 hwin
    have hsub : {γ : Path d | ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} ⊆
        Set.univ \ E := by
      intro γ hγ
      refine ⟨Set.mem_univ _, ?_⟩
      intro he
      have hb := (endpointBall_coordinate_bounds i R x (γ τ) he).1
      have hs := hγ τ le_rfl
      change |γ τ i - c i| < R at hs
      change |x i - c i| < R at hx
      have hs' := (abs_lt.mp hs).2
      have hx' := (abs_lt.mp hx).1
      linarith
    simpa only [measure_univ, mul_one] using (measure_mono hsub).trans hbound
  · have hnull : G.pathLaw x {γ : Path d | γ 0 ≠ x} = 0 := by
      exact ae_iff.mp (G.pathLaw_starts_at x)
    have hzero : G.pathLaw x {γ : Path d |
        ∀ t : ℝ≥0, t ≤ τ → γ t ∈ coordinateSlab i c R} = 0 := by
      apply measure_mono_null _ hnull
      intro γ hγ hstart
      apply hx
      simpa only [hstart] using hγ 0 (zero_le : 0 ≤ τ)
    rw [hzero]
    exact zero_le

/-- The scaled slab-exit estimate used in GMP (4.9), for every regular realization. -/
theorem uniform_regular_gmp_slab_exit_tail
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ n : ℕ, ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ) (zeroPotentialReducedPair ω))
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
        hω μ hμ.le hμ1) (x : Vec d),
      G.pathLaw x {γ : Path d |
        (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ≤
        ENNReal.ofReal (1 / 15 : ℝ) := by
  obtain ⟨δ, hδ, hδ1, hminor⟩ := uniform_regular_gmp_source_minorization d hd Λ r l hl
  obtain ⟨n, hn⟩ := exists_gmp_survival_le δ (1 / 15) hδ hδ1.le (by norm_num)
  refine ⟨n, ?_⟩
  intro Q μ hμ hμ1 ω hω G x
  let i := Renewal.forceCoord hd
  let R := l / μ
  let Δ := Renewal.regenDelta μ
  let U := coordinateSlab i x R
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hstep : ∀ y, G.pathLaw y {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U} ≤ ENNReal.ofReal (1 - δ) :=
    gmp_slab_survival_le_of_source_minorization G Δ δ R i hδ hδ1.le hR
      (hminor Q μ hμ hμ1 ω hω G) x
  have hsurv := hn G U (isOpen_coordinateSlab i x R) Δ hstep x
  have hsub : ∀ᵐ γ ∂G.pathLaw x,
      γ ∈ {γ : Path d | (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) < coordinateSlabExit γ i R} →
      γ ∈ {γ : Path d | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → γ t ∈ U} := by
    filter_upwards [G.pathLaw_starts_at x] with γ hstart hγ t ht
    have ht' : (t : ℝ≥0∞) < coordinateSlabExit γ i R :=
      (ENNReal.coe_le_coe.mpr ht).trans_lt hγ
    have hm := MarkovProcess.ContinuousPath.mem_of_lt_exitTime
      (coordinateSlab i (γ 0) R) γ t ht'
    change γ 0 = x at hstart
    rw [hstart] at hm
    exact hm
  exact (measure_mono_ae hsub).trans hsurv

/-- The uniform scaled slab-exit estimate holds for every supplied reduced law. -/
theorem uniform_supplied_gmp_slab_exit_tail
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ n : ℕ, ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (P : QuenchedPathLaws d),
      IsGMPReducedKernel hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
      ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        P (x, ω) {γ : Path d |
          (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
            coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ≤
          ENNReal.ofReal (1 / 15 : ℝ) := by
  obtain ⟨n, hn⟩ := uniform_regular_gmp_slab_exit_tail d hd Λ r l hl
  refine ⟨n, ?_⟩
  intro Q μ hμ hμ1 P hP
  filter_upwards [hP] with ω hω
  obtain ⟨hω, G, hrow⟩ := hω
  intro x
  rw [hrow x]
  exact hn Q μ hμ hμ1 ω hω G x

end EinsteinFull.Regeneration
