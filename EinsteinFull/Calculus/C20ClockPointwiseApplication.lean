import EinsteinFull.Calculus.C12ClockMaximalErgodic
import EinsteinFull.Calculus.C12ClockCorrelationMean
import EinsteinFull.Calculus.C12ClockCocycleIdentity
import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.JointClockPathMapSupport

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Stationary centered clock blocks with vanishing L¹ averages give the
physical clock speed under almost every quenched origin law. -/
theorem c20_clock_rate_of_stationary_blocks {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    (T : FieldPair d × Path d → FieldPair d × Path d)
    (hT : MeasurePreserving T (Carriers.annealedCoordinateJoint Q Y hprob)
      (Carriers.annealedCoordinateJoint Q Y hprob))
    (f : FieldPair d × Path d → ℝ) (hf : Measurable f)
    (hi : Integrable f (Carriers.annealedCoordinateJoint Q Y hprob)) (η : ℝ)
    (hblock : ∀ n : ℕ, ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob,
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) - ((n : ℝ) + 1) * η =
        birkhoffSum T f (n + 1) z)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      |birkhoffSum T f (n + 1) z / ((n : ℝ) + 1)|
        ∂Carriers.annealedCoordinateJoint Q Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q (originLaw Y) hprob
  have hpoint := clock_pointwise_of_l1_mean_zero
    (Carriers.annealedCoordinateJoint Q Y hprob) T hT f hf hi hmean
  have hblocks : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob, ∀ n : ℕ,
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) - ((n : ℝ) + 1) * η =
        birkhoffSum T f (n + 1) z := by
    exact ae_all_iff.2 hblock
  apply (c20_annealed_event_iff_fibers Q Y hprob
    (c20_measurableSet_clock_speed η)).1
  filter_upwards [hpoint, hblocks] with z hz hb
  apply (c20_clock_speed_iff_integer_event z.1 z.2 η).2
  have hratio (n : ℕ) :
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) / ((n : ℝ) + 1) =
        birkhoffSum T f (n + 1) z / ((n : ℝ) + 1) + η := by
    have hn : (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    rw [← hb n, sub_div]
    field_simp
    ring
  have hsucc : Tendsto (fun n : ℕ =>
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 η) := by
    simpa only [zero_add, ← hratio] using hz.add_const η
  apply (tendsto_add_atTop_iff_nat 1).1
  simpa only [Clock.clockRateNatSet, Set.mem_ofPred_eq, Nat.cast_add,
    Nat.cast_one, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one] using hsucc

/-- Vanishing averaged absolute block correlations imply the actual quenched
physical clock speed for a bounded centered block observable. -/
theorem c20_clock_rate_of_block_correlations {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    (T : FieldPair d × Path d → FieldPair d × Path d)
    (hT : MeasurePreserving T (Carriers.annealedCoordinateJoint Q Y hprob)
      (Carriers.annealedCoordinateJoint Q Y hprob))
    (f : FieldPair d × Path d → ℝ) (hf : Measurable f)
    (hi : Integrable f (Carriers.annealedCoordinateJoint Q Y hprob)) (η : ℝ)
    (hblock : ∀ n : ℕ, ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob,
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) - ((n : ℝ) + 1) * η =
        birkhoffSum T f (n + 1) z)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob, |f z| ≤ B)
    (hcorr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), |∫ z, f z * f ((T^[k]) z)
        ∂Carriers.annealedCoordinateJoint Q Y hprob|) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q (originLaw Y) hprob
  exact c20_clock_rate_of_stationary_blocks Q Y hprob T hT f hf hi η hblock
    (clock_l1_mean_zero_of_abs_correlations
      (Carriers.annealedCoordinateJoint Q Y hprob) T hT f hf B hB hbound hcorr)

/-- Vanishing averaged signed block correlations imply the actual quenched
physical clock speed for a bounded centered block observable. -/
theorem c20_clock_rate_of_signed_block_correlations {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    (T : FieldPair d × Path d → FieldPair d × Path d)
    (hT : MeasurePreserving T (Carriers.annealedCoordinateJoint Q Y hprob)
      (Carriers.annealedCoordinateJoint Q Y hprob))
    (f : FieldPair d × Path d → ℝ) (hf : Measurable f)
    (hi : Integrable f (Carriers.annealedCoordinateJoint Q Y hprob)) (η : ℝ)
    (hblock : ∀ n : ℕ, ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob,
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) - ((n : ℝ) + 1) * η =
        birkhoffSum T f (n + 1) z)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob, |f z| ≤ B)
    (hcorr : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ *
      ∑ k ∈ Finset.range (n + 1), (∫ z, f z * f ((T^[k]) z)
        ∂Carriers.annealedCoordinateJoint Q Y hprob)) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q (originLaw Y) hprob
  exact c20_clock_rate_of_stationary_blocks Q Y hprob T hT f hf hi η hblock
    (clock_l1_mean_zero_of_signed_correlations
      (Carriers.annealedCoordinateJoint Q Y hprob) T hT f hf B hB hbound hcorr)

/-- An L² transfer identity for the stationary block correlations gives the
physical clock speed under almost every quenched origin law. -/
theorem c20_clock_rate_of_l2_block_transfer {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    (T : FieldPair d × Path d → FieldPair d × Path d)
    (hT : MeasurePreserving T (Carriers.annealedCoordinateJoint Q Y hprob)
      (Carriers.annealedCoordinateJoint Q Y hprob))
    (f : FieldPair d × Path d → ℝ) (hf : Measurable f)
    (hi : Integrable f (Carriers.annealedCoordinateJoint Q Y hprob)) (η : ℝ)
    (hblock : ∀ n : ℕ, ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob,
      (Clock.physicalPathClock z.1 z.2 (n + 1) : ℝ) - ((n : ℝ) + 1) * η =
        birkhoffSum T f (n + 1) z)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob, |f z| ≤ B)
    (g : ℕ → FieldPair d × Path d → ℝ)
    (hg : ∀ k, MemLp (g k) 2 (Carriers.annealedCoordinateJoint Q Y hprob))
    (hpair : ∀ k, (∫ z, f z * f ((T^[k]) z)
      ∂Carriers.annealedCoordinateJoint Q Y hprob) =
        ∫ z, f z * g k z ∂Carriers.annealedCoordinateJoint Q Y hprob)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), g k z) ^ 2
        ∂Carriers.annealedCoordinateJoint Q Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q (originLaw Y) hprob
  have hf2 : MemLp f 2 (Carriers.annealedCoordinateJoint Q Y hprob) :=
    MemLp.of_bound hf.aestronglyMeasurable B (by
      simpa only [Real.norm_eq_abs] using hbound)
  exact c20_clock_rate_of_signed_block_correlations Q Y hprob T hT f hf hi η hblock
    B hB hbound (clock_signed_correlations_of_l2_transfer
      (Carriers.annealedCoordinateJoint Q Y hprob) T f hf2 g hg hpair hmean)

/-- The canonical centered unit-clock blocks give the actual quenched clock speed
from their stationary L² transfer estimates on the supplied annealed law. -/
theorem c20_clock_rate_of_canonical_clock_blocks {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ)
    (hT : MeasurePreserving (c12ClockShift 1) (Carriers.annealedCoordinateJoint Q Y hprob)
      (Carriers.annealedCoordinateJoint Q Y hprob))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q Y hprob,
      |(c12CenteredClockBlock η) z| ≤ B)
    (g : ℕ → FieldPair d × Path d → ℝ)
    (hg : ∀ k, MemLp (g k) 2 (Carriers.annealedCoordinateJoint Q Y hprob))
    (hpair : ∀ k, (∫ z, (c12CenteredClockBlock η) z *
      (c12CenteredClockBlock η) (((c12ClockShift 1)^[k]) z)
        ∂Carriers.annealedCoordinateJoint Q Y hprob) =
      ∫ z, (c12CenteredClockBlock η) z * g k z
        ∂Carriers.annealedCoordinateJoint Q Y hprob)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), g k z)^2
        ∂Carriers.annealedCoordinateJoint Q Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q (originLaw Y) hprob
  have hf : Measurable (c12CenteredClockBlock (d := d) η) :=
    (Clock.continuous_physicalPathClock_at (d := d) 1).measurable.sub_const η
  have hf1 : MemLp (c12CenteredClockBlock η) 1
      (Carriers.annealedCoordinateJoint Q Y hprob) :=
    MemLp.of_bound hf.aestronglyMeasurable B (by
      simpa only [Real.norm_eq_abs] using hbound)
  apply c20_clock_rate_of_l2_block_transfer Q Y hprob (c12ClockShift 1) hT
    (c12CenteredClockBlock η) hf (memLp_one_iff_integrable.mp hf1) η
    _ B hB hbound g hg hpair hmean
  intro n
  exact Filter.Eventually.of_forall fun z => by
    simpa only [Nat.cast_add, Nat.cast_one] using
      c12_centered_clock_birkhoff_identity η (n + 1) z

/-- Bounded potential controls the actual centered unit-clock block on every path. -/
theorem c20_centered_clock_block_bound {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L η : ℝ) (hV : ∀ x, |ω.2 x| ≤ L) :
    |c12CenteredClockBlock η (ω, γ)| ≤ Real.exp (2*L) + |η| := by
  have hclock : (Clock.physicalPathClock ω γ 1 : ℝ) ≤ Real.exp (2 * L) := by
    simpa only [NNReal.coe_one, mul_one] using
      (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ L hV 1).2
  calc
    |c12CenteredClockBlock η (ω, γ)| ≤
        |(Clock.physicalPathClock ω γ 1 : ℝ)| + |η| := by
      change |(Clock.physicalPathClock ω γ 1 : ℝ) - η| ≤ _
      simpa only [Real.norm_eq_abs] using
        norm_sub_le (Clock.physicalPathClock ω γ 1 : ℝ) η
    _ = (Clock.physicalPathClock ω γ 1 : ℝ) + |η| := by
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
    _ ≤ Real.exp (2 * L) + |η| := add_le_add hclock le_rfl

/-- The canonical block bound holds on the same supplied annealed coordinate law. -/
theorem c20_ae_centered_clock_block_bound {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ) :
    ∀ᵐ z ∂Carriers.annealedCoordinateJoint Q.measure Y hprob,
      |c12CenteredClockBlock η z| ≤ Real.exp (2*L) + |η| := by
  have hf : Measurable (c12CenteredClockBlock (d := d) η) :=
    (Clock.continuous_physicalPathClock_at (d := d) 1).measurable.sub_const η
  have hS : MeasurableSet {z : FieldPair d × Path d |
      |c12CenteredClockBlock η z| ≤ Real.exp (2 * L) + |η|} := by
    simpa only [Real.norm_eq_abs] using
      measurableSet_le hf.norm (measurable_const (a := Real.exp (2 * L) + |η|))
  apply Clock.ae_annealedCoordinateJoint_mem Q.measure Y hprob hS
  filter_upwards [Q.regular] with ω hω
  exact Filter.Eventually.of_forall fun γ =>
    c20_centered_clock_block_bound ω γ L η hω.2.1

/-- Regular environments supply the canonical block bound for the clock-speed
application on the supplied stationary annealed law. -/
theorem c20_clock_rate_of_regular_canonical_clock_blocks {d : ℕ}
    {L r : ℝ} (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ)
    (hT : MeasurePreserving (c12ClockShift 1)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob))
    (g : ℕ → FieldPair d × Path d → ℝ)
    (hg : ∀ k, MemLp (g k) 2 (Carriers.annealedCoordinateJoint Q.measure Y hprob))
    (hpair : ∀ k, (∫ z, (c12CenteredClockBlock η) z *
      (c12CenteredClockBlock η) (((c12ClockShift 1)^[k]) z)
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) =
      ∫ z, (c12CenteredClockBlock η) z * g k z
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1), g k z)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  exact c20_clock_rate_of_canonical_clock_blocks Q.measure Y hprob η hT
    (Real.exp (2 * L) + |η|)
    (add_nonneg (Real.exp_pos _).le (abs_nonneg η))
    (c20_ae_centered_clock_block_bound Q Y hprob η) g hg hpair hmean

/-- The actual squared canonical block mean and shift preservation imply clock
speed for the supplied regular-environment path laws. -/
theorem c20_clock_rate_of_regular_canonical_block_mean {d : ℕ}
    {L r : ℝ} (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ)
    (hT : MeasurePreserving (c12ClockShift 1) (Carriers.annealedCoordinateJoint Q.measure Y hprob)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob))
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1),
        c12CenteredClockBlock η (((c12ClockShift 1)^[k]) z))^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) hprob
  have hf2 : MemLp (c12CenteredClockBlock η) 2
      (Carriers.annealedCoordinateJoint Q.measure Y hprob) :=
    MemLp.of_bound (continuous_c12CenteredClockBlock η).measurable.aestronglyMeasurable
      (Real.exp (2 * L) + |η|) (by
        simpa only [Real.norm_eq_abs] using c20_ae_centered_clock_block_bound Q Y hprob η)
  exact c20_clock_rate_of_regular_canonical_clock_blocks Q Y hprob η hT
    (fun k z => c12CenteredClockBlock η (((c12ClockShift 1)^[k]) z))
    (fun k => hf2.comp_measurePreserving (hT.iterate k)) (fun _ => rfl) hmean

/-- Vanishing physical-clock L² error implies clock speed under the supplied
regular-environment path laws when their annealed law preserves the unit shift. -/
theorem c20_clock_rate_of_regular_clock_l2_error {d : ℕ}
    {L r : ℝ} (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ)
    (hT : MeasurePreserving (c12ClockShift 1)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob)
      (Carriers.annealedCoordinateJoint Q.measure Y hprob))
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1) - η)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0)) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  apply c20_clock_rate_of_regular_canonical_block_mean Q Y hprob η hT
  simpa only [c12_actual_centered_clock_average] using hmean

/-- The normalized physical-clock error is square integrable under the actual
annealed law, uniformly in the observation time. -/
theorem c20_clock_error_memLp {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ) (t : ℝ≥0) :
    MemLp (fun z : FieldPair d × Path d =>
      (Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η) 2
      (Carriers.annealedCoordinateJoint Q.measure Y hprob) := by
  let : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure Y hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) hprob
  have hf : Measurable (fun z : FieldPair d × Path d =>
      (Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η) :=
    ((Clock.continuous_physicalPathClock_at (d := d) t).measurable.div_const _).sub_const η
  apply MemLp.of_bound hf.aestronglyMeasurable (Real.exp (2 * L) + |η|)
  have hS : MeasurableSet {z : FieldPair d × Path d |
      |(Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η| ≤
        Real.exp (2 * L) + |η|} := by
    simpa only [Real.norm_eq_abs] using
      measurableSet_le hf.norm (measurable_const (a := Real.exp (2 * L) + |η|))
  have hb := Clock.ae_annealedCoordinateJoint_mem Q.measure Y hprob hS
  simp only [Real.norm_eq_abs]
  apply hb
  filter_upwards [Q.regular] with ω hω
  exact Filter.Eventually.of_forall fun γ => by
    have hc := (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ L hω.2.1 t).2
    have hratio := div_le_of_le_mul₀ t.coe_nonneg (Real.exp_pos (2 * L)).le hc
    calc
      |(Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) - η| ≤
          |(Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ)| + |η| :=
        abs_sub _ _
      _ ≤ Real.exp (2 * L) + |η| := by
        rw [abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg)]
        exact add_le_add hratio le_rfl

/-- The mean-square error at a real time is controlled by its preceding integer
sample and the deterministic clock interpolation error. -/
theorem c20_clock_l2_integer_comparison {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ) (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0)
    (hlo : (n : ℝ≥0) ≤ t) (hhi : t ≤ ((n + 1 : ℕ) : ℝ≥0)) :
    (∫ z, ((Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) ≤
    2 * (∫ z, ((Clock.physicalPathClock z.1 z.2 (n : ℝ≥0) : ℝ) / (n : ℝ) - η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) +
      2 * (2 * Real.exp (2 * L) / (n : ℝ))^2 := by
  let μ := Carriers.annealedCoordinateJoint Q.measure Y hprob
  let : IsProbabilityMeasure μ :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw Y) hprob
  let f := fun s : ℝ≥0 => fun z : FieldPair d × Path d =>
    (Clock.physicalPathClock z.1 z.2 s : ℝ) / (s : ℝ) - η
  have hi (s : ℝ≥0) : Integrable (fun z => (f s z)^2) μ :=
    (c20_clock_error_memLp Q Y hprob η s).integrable_sq
  have hf (s : ℝ≥0) : Measurable (f s) :=
    ((Clock.continuous_physicalPathClock_at (d := d) s).measurable.div_const _).sub_const η
  have hS : MeasurableSet {z | (f t z)^2 ≤
      2 * (f (n : ℝ≥0) z)^2 + 2 * (2 * Real.exp (2 * L) / (n : ℝ))^2} :=
    measurableSet_le ((hf t).pow_const 2)
      (((hf (n : ℝ≥0)).pow_const 2).const_mul 2 |>.add_const _)
  have hb : ∀ᵐ z ∂μ, (f t z)^2 ≤
      2 * (f (n : ℝ≥0) z)^2 + 2 * (2 * Real.exp (2 * L) / (n : ℝ))^2 := by
    apply Clock.ae_annealedCoordinateJoint_mem Q.measure Y hprob hS
    filter_upwards [Q.regular] with ω hω
    exact Filter.Eventually.of_forall fun γ => by
      have hc := c12_clock_ratio_integer_comparison ω γ L hω.2.1 n hn t hlo hhi
      have hnonneg : 0 ≤ 2 * Real.exp (2 * L) / (n : ℝ) := by positivity
      have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hc
      rw [sq_abs] at hs
      dsimp only [f]
      simp only [NNReal.coe_natCast]
      nlinarith only [hs, sq_nonneg
        (((Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) -
          (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) / (n : ℝ)) -
          ((Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) / (n : ℝ) - η))]
  have h := integral_mono_ae (hi t) (((hi n).const_mul 2).add (integrable_const _)) hb
  simp only [Pi.add_apply] at h
  rw [integral_add ((hi n).const_mul 2) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  simpa only [f, NNReal.coe_natCast] using h

/-- Integer-sample L² convergence of the actual physical clock extends to all
nonnegative real times under the same supplied annealed law. -/
theorem c20_clock_l2_real_time_of_integer_samples {d : ℕ}
    {L r : ℝ} (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1) - η)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ) - η)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0) := by
  let I := fun t : ℝ≥0 => ∫ z,
    ((Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob
  have hseq : Tendsto (fun n : ℕ => I (n : ℝ≥0)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [I, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
      NNReal.coe_add, NNReal.coe_one] using hmean
  have hfloor : Tendsto (fun t : ℝ≥0 => ⌊t⌋₊) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop (b : ℝ≥0)).mono fun t ht =>
      (Nat.le_floor_iff (show 0 ≤ t from bot_le)).2 ht
  have herror : Tendsto (fun t : ℝ≥0 =>
      2 * Real.exp (2 * L) / (⌊t⌋₊ : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.exp (2 * L))).comp hfloor
  have hupper : Tendsto (fun t : ℝ≥0 =>
      2 * I (⌊t⌋₊ : ℝ≥0) + 2 * (2 * Real.exp (2 * L) / (⌊t⌋₊ : ℝ))^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      ((hseq.comp hfloor).const_mul 2).add ((herror.pow 2).const_mul 2)
  apply squeeze_zero' (Filter.Eventually.of_forall fun t =>
    integral_nonneg fun z => sq_nonneg _) _ hupper
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with t ht
  simpa only [I, NNReal.coe_natCast] using
    c20_clock_l2_integer_comparison Q Y hprob η ⌊t⌋₊ ht t
      (Nat.floor_le (show 0 ≤ t from bot_le)) (Nat.lt_succ_floor t).le

/-- Markov's inequality bounds the actual physical-clock ratio tail by its
annealed mean-square error. -/
theorem c20_clock_ratio_tail_of_l2_error {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ) (t : ℝ≥0) (ht : 0 < t) (ε : ℝ) (hε : 0 < ε) :
    Carriers.annealedCoordinateJoint Q.measure Y hprob
      {z | ε < |(Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η|} ≤
    ENNReal.ofReal ((∫ z, ((Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob)/(ε^2)) := by
  have _ht := ht
  have hi := (c20_clock_error_memLp Q Y hprob η t).integrable_sq
  calc
    _ ≤ ENNReal.ofReal (∫ z,
        ((Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η)^2 / ε^2
          ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) := by
      apply (hi.div_const (ε^2)).measure_le_integral
        (Filter.Eventually.of_forall fun z => div_nonneg (sq_nonneg _) (sq_nonneg ε))
      intro z hz
      apply (le_div_iff₀ (sq_pos_of_pos hε)).2
      simpa only [one_mul, sq_abs] using
        (sq_le_sq₀ hε.le (abs_nonneg _)).2 hz.le
    _ = _ := by rw [integral_div]

/-- An integer-sample mean-square bound controls the clock tail between
that sample and the next integer. -/
theorem c20_clock_tail_of_integer_l2_bound {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η C : ℝ) (b : ℕ → ℝ)
    (hL2 : ∀ n : ℕ, 1 ≤ n →
      (∫ z, ((Clock.physicalPathClock z.1 z.2 (n : ℝ≥0) : ℝ)/(n : ℝ)-η)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) ≤ C*b n)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0)
    (hlo : (n : ℝ≥0) ≤ t) (hhi : t ≤ ((n+1 : ℕ) : ℝ≥0))
    (ε : ℝ) (hε : 0 < ε) :
    Carriers.annealedCoordinateJoint Q.measure Y hprob
      {z | ε < |(Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η|} ≤
    ENNReal.ofReal ((2*C*b n+2*(2*Real.exp (2*L)/(n : ℝ))^2)/(ε^2)) := by
  have ht : 0 < t := lt_of_lt_of_le (by exact_mod_cast hn) hlo
  have hcomp := c20_clock_l2_integer_comparison Q Y hprob η n hn t hlo hhi
  have hbound := hL2 n hn
  have hnum : (∫ z, ((Clock.physicalPathClock z.1 z.2 t : ℝ) / (t : ℝ) - η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) ≤
      2*C*b n + 2*(2*Real.exp (2*L)/(n : ℝ))^2 := by
    linarith only [hcomp, hbound]
  exact (c20_clock_ratio_tail_of_l2_error Q Y hprob η t ht ε hε).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hnum (sq_nonneg ε)))

/-- Mean-square convergence implies convergence in probability for the actual
physical-clock ratio under the supplied annealed law. -/
theorem c20_clock_ratio_in_probability_of_l2 {d : ℕ} {L r : ℝ}
    (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω))
    (η : ℝ)
    (hL2 : Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η)^2
      ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun t : ℝ≥0 => Carriers.annealedCoordinateJoint Q.measure Y hprob
        {z | ε < |(Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η|})
      atTop (𝓝 0) := by
  intro ε hε
  have hupper := ENNReal.tendsto_ofReal (hL2.div_const (ε^2))
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun t => bot_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
  exact c20_clock_ratio_tail_of_l2_error Q Y hprob η t ht ε hε

/-- Integer-sample mean-square convergence implies vanishing actual
physical-clock ratio tail probabilities at all nonnegative real times. -/
theorem c20_clock_ratio_tail_tendsto_zero_of_integer_samples {d : ℕ}
    {L r : ℝ} (Q : EnvironmentLaw d L r) (Y : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) (η : ℝ)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1) - η)^2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun t : ℝ≥0 => Carriers.annealedCoordinateJoint Q.measure Y hprob
      {z | ε < |(Clock.physicalPathClock z.1 z.2 t : ℝ)/(t : ℝ)-η|})
      atTop (𝓝 0) := by
  exact c20_clock_ratio_in_probability_of_l2 Q Y hprob η
    (c20_clock_l2_real_time_of_integer_samples Q Y hprob η hmean) ε hε

/-- Compare the actual inverse time with a deterministic clock time. -/
theorem c20_inverse_time_le_iff {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (s t : ℝ≥0) :
    Clock.PathMapV4.inversePhysicalTime z s ≤ t ↔
      s ≤ Clock.physicalPathClock z.1.1 z.2 t := by
  let e := Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2
  change e.symm s ≤ t ↔ s ≤ e t
  constructor
  · intro h
    simpa using e.monotone h
  · intro h
    simpa using e.symm.monotone h

/-- Compare a deterministic clock time with the actual inverse time. -/
theorem c20_le_inverse_time_iff {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (s t : ℝ≥0) :
    t ≤ Clock.PathMapV4.inversePhysicalTime z s ↔
      Clock.physicalPathClock z.1.1 z.2 t ≤ s := by
  let e := Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2
  change t ≤ e.symm s ↔ e t ≤ s
  constructor
  · intro h
    simpa using e.monotone h
  · intro h
    simpa using e.symm.monotone h

/-- Two deterministic clock comparisons sandwich the inverse-clock ratio. -/
theorem c20_inverse_ratio_sandwich {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (s a b : ℝ≥0)
    (hs : 0 < s)
    (ha : Clock.physicalPathClock z.1.1 z.2 (a * s) ≤ s)
    (hb : s ≤ Clock.physicalPathClock z.1.1 z.2 (b * s)) :
    (a : ℝ) ≤ (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) ∧
      (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) ≤ (b : ℝ) := by
  have ha' := (c20_le_inverse_time_iff z s (a * s)).2 ha
  have hb' := (c20_inverse_time_le_iff z s (b * s)).2 hb
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · apply (le_div_iff₀ hs').2
    exact_mod_cast ha'
  · apply (div_le_iff₀ hs').2
    simpa only [NNReal.coe_mul] using (show
      (Clock.PathMapV4.inversePhysicalTime z s : ℝ) ≤ ((b * s : ℝ≥0) : ℝ) by
        exact_mod_cast hb')

/-- Clock-ratio comparisons at positive scaled times control the inverse ratio. -/
theorem c20_inverse_ratio_sandwich_of_clock_ratios {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (s a b : ℝ≥0)
    (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (hlo : (Clock.physicalPathClock z.1.1 z.2 (a * s) : ℝ) /
        ((a : ℝ) * (s : ℝ)) ≤ (a : ℝ)⁻¹)
    (hhi : (b : ℝ)⁻¹ ≤ (Clock.physicalPathClock z.1.1 z.2 (b * s) : ℝ) /
        ((b : ℝ) * (s : ℝ))) :
    (a : ℝ) ≤ (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) ∧
      (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) ≤ (b : ℝ) := by
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  apply c20_inverse_ratio_sandwich z s a b hs
  · have h := (div_le_iff₀ (mul_pos ha' hs')).1 hlo
    have heq : (a : ℝ)⁻¹ * ((a : ℝ) * (s : ℝ)) = (s : ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt ha'), one_mul]
    have h' : (Clock.physicalPathClock z.1.1 z.2 (a * s) : ℝ) ≤ (s : ℝ) := by
      simpa only [heq] using h
    exact_mod_cast h'
  · have h := (le_div_iff₀ (mul_pos hb' hs')).1 hhi
    have heq : (b : ℝ)⁻¹ * ((b : ℝ) * (s : ℝ)) = (s : ℝ) := by
      rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hb'), one_mul]
    have h' : (s : ℝ) ≤ (Clock.physicalPathClock z.1.1 z.2 (b * s) : ℝ) := by
      simpa only [heq] using h
    exact_mod_cast h'

/-- A bad inverse ratio forces a bad direct ratio at one of two scaled times. -/
theorem c20_inverse_ratio_bad_event_subset {d : ℕ} {L : ℝ}
    (s a b : ℝ≥0) (hs : 0 < s) (ha : 0 < a) (hb : 0 < b)
    (η ε δa δb : ℝ)
    (hlo : η⁻¹ - ε ≤ (a : ℝ)) (hhi : (b : ℝ) ≤ η⁻¹ + ε)
    (hδa : η + δa ≤ (a : ℝ)⁻¹) (hδb : (b : ℝ)⁻¹ ≤ η - δb) :
    {z : ReductionImageV3.PhysicalField d L × Path d |
      ε < |(Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹|} ⊆
    {z | δa < |(Clock.physicalPathClock z.1.1 z.2 (a*s) : ℝ)/
      ((a*s : ℝ≥0) : ℝ)-η|} ∪
    {z | δb < |(Clock.physicalPathClock z.1.1 z.2 (b*s) : ℝ)/
      ((b*s : ℝ≥0) : ℝ)-η|} := by
  intro z hz
  by_contra hn
  have hna : ¬ δa < |(Clock.physicalPathClock z.1.1 z.2 (a*s) : ℝ)/
      ((a*s : ℝ≥0) : ℝ)-η| := fun h => hn (Or.inl h)
  have hnb : ¬ δb < |(Clock.physicalPathClock z.1.1 z.2 (b*s) : ℝ)/
      ((b*s : ℝ≥0) : ℝ)-η| := fun h => hn (Or.inr h)
  have hca := abs_le.mp (le_of_not_gt hna)
  have hcb := abs_le.mp (le_of_not_gt hnb)
  have hclocka : (Clock.physicalPathClock z.1.1 z.2 (a*s) : ℝ)/
      ((a : ℝ)*(s : ℝ)) ≤ (a : ℝ)⁻¹ := by
    simp only [NNReal.coe_mul] at hca
    linarith [hca.2]
  have hclockb : (b : ℝ)⁻¹ ≤ (Clock.physicalPathClock z.1.1 z.2 (b*s) : ℝ)/
      ((b : ℝ)*(s : ℝ)) := by
    simp only [NNReal.coe_mul] at hcb
    linarith [hcb.1]
  have hbounds := c20_inverse_ratio_sandwich_of_clock_ratios z s a b hs ha hb hclocka hclockb
  have hgood : |(Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹| ≤ ε := by
    apply abs_le.mpr
    constructor <;> linarith [hbounds.1, hbounds.2]
  exact (not_lt_of_ge hgood) hz

/-- Convergence in probability transfers from the physical clock to its actual inverse. -/
theorem c20_inverse_clock_ratio_in_probability {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d))
    (η : ℝ) (hη : 0 < η)
    (hclock : ∀ ε : ℝ, 0 < ε → Tendsto
      (fun t : ℝ≥0 => μ {z | ε <
        |(Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η|})
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun s : ℝ≥0 => μ {z | ε <
        |(Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹|}) atTop (𝓝 0) := by
  intro ε hε
  let x : ℝ := η⁻¹
  have hx : 0 < x := inv_pos.mpr hη
  let a : ℝ≥0 := ⟨max (x - ε / 2) (x / 2),
    le_trans (le_of_lt (show 0 < x / 2 by positivity)) (le_max_right _ _)⟩
  let b : ℝ≥0 := ⟨x + ε / 2, by positivity⟩
  have ha_real : 0 < (a : ℝ) := by
    dsimp [a]
    exact lt_of_lt_of_le (by positivity : 0 < x / 2) (le_max_right _ _)
  have hb_real : 0 < (b : ℝ) := by
    change 0 < x + ε / 2
    linarith
  have ha : 0 < a := by exact_mod_cast ha_real
  have hb : 0 < b := by exact_mod_cast hb_real
  have hal : (a : ℝ) < x := by
    dsimp [a]
    exact max_lt (by linarith) (by linarith)
  have hbl : x < (b : ℝ) := by
    change x < x + ε / 2
    linarith
  have hIa : η < (a : ℝ)⁻¹ := by
    have h := (inv_lt_inv₀ hx ha_real).2 hal
    simpa [x] using h
  have hIb : (b : ℝ)⁻¹ < η := by
    have h := (inv_lt_inv₀ hb_real hx).2 hbl
    simpa [x] using h
  let δa := ((a : ℝ)⁻¹ - η) / 2
  let δb := (η - (b : ℝ)⁻¹) / 2
  have hδa : 0 < δa := by dsimp [δa]; linarith
  have hδb : 0 < δb := by dsimp [δb]; linarith
  have ha_bound : η⁻¹ - ε ≤ (a : ℝ) := by
    change x - ε ≤ max (x - ε / 2) (x / 2)
    have h := le_max_left (x - ε / 2) (x / 2)
    linarith
  have hb_bound : (b : ℝ) ≤ η⁻¹ + ε := by
    change x + ε / 2 ≤ x + ε
    linarith
  have hδa_bound : η + δa ≤ (a : ℝ)⁻¹ := by dsimp [δa]; linarith
  have hδb_bound : (b : ℝ)⁻¹ ≤ η - δb := by dsimp [δb]; linarith
  have hscalea : Tendsto (fun s : ℝ≥0 => a * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  have hscaleb : Tendsto (fun s : ℝ≥0 => b * s) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hb).2 tendsto_id
  have htails := ((hclock δa hδa).comp hscalea).add ((hclock δb hδb).comp hscaleb)
  simp only [zero_add] at htails
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htails
    (Filter.Eventually.of_forall fun _ => bot_le)
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
  exact (measure_mono (c20_inverse_ratio_bad_event_subset s a b hs ha hb η ε δa δb
    ha_bound hb_bound hδa_bound hδb_bound)).trans (measure_union_le _ _)


/-- Mean-square convergence of the actual joint clock implies convergence in
probability of its actual inverse clock under the same joint law. -/
theorem c20_inverse_clock_ratio_in_probability_of_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 < η)
    (hL2 : Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ)
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto
      (fun s : ℝ≥0 => μ {z | ε <
        |(Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹|}) atTop (𝓝 0) := by
  apply c20_inverse_clock_ratio_in_probability μ η hη
  intro ε hε
  have hbound : ∀ t : ℝ≥0, μ {z | ε <
      |(Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η|} ≤
      ENNReal.ofReal ((∫ z,
        ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ) / ε^2) := by
    intro t
    have hf : Measurable (fun z : ReductionImageV3.PhysicalField d L × Path d =>
        (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η) := by
      exact (((Clock.continuous_physicalPathClock_at (d := d) t).measurable.comp
        (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd)).div_const _).sub_const η
    have hlp : MemLp (fun z : ReductionImageV3.PhysicalField d L × Path d =>
        (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η) 2 μ := by
      apply MemLp.of_bound hf.aestronglyMeasurable (Real.exp (2 * L) + |η|)
      filter_upwards with z
      simp only [Real.norm_eq_abs]
      have hc := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 t).2
      have hr := div_le_of_le_mul₀ t.coe_nonneg (Real.exp_pos (2 * L)).le hc
      calc
        |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η| ≤
            |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ)| + |η| := abs_sub _ _
        _ ≤ Real.exp (2 * L) + |η| := by
          rw [abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg)]
          exact add_le_add hr le_rfl
    calc
      _ ≤ ENNReal.ofReal (∫ z,
          ((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^2 / ε^2 ∂μ) := by
        apply (hlp.integrable_sq.div_const (ε^2)).measure_le_integral
          (Filter.Eventually.of_forall fun z => div_nonneg (sq_nonneg _) (sq_nonneg ε))
        intro z hz
        apply (le_div_iff₀ (sq_pos_of_pos hε)).2
        simpa only [one_mul, sq_abs] using
          (sq_le_sq₀ hε.le (abs_nonneg _)).2 hz.le
      _ = _ := by rw [integral_div]
  have hupper : Tendsto (fun t : ℝ≥0 => ENNReal.ofReal ((∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ) / ε^2))
      atTop (𝓝 0) := by
    have hdiv : Tendsto (fun t : ℝ≥0 => (∫ z,
        ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ) / ε^2)
        atTop (𝓝 0) := by
      simpa only [zero_div] using hL2.div_const (ε^2)
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hdiv
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)

/-- A uniformly bounded inverse clock converges in mean square whenever the
physical clock does, under the same joint probability law. -/
theorem c20_inverse_clock_ratio_l2_of_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 < η)
    (hL2 : Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ)
      atTop (𝓝 0)) :
    Tendsto (fun s : ℝ≥0 => ∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹)^2 ∂μ)
      atTop (𝓝 0) := by
  let f : ℝ≥0 → ReductionImageV3.PhysicalField d L × Path d → ℝ := fun s z =>
    (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) - η⁻¹
  let K : ℝ := Real.exp (2 * L) + |η⁻¹|
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hfmeas (s : ℝ≥0) : Measurable (f s) := by
    dsimp [f]
    exact (((measurable_coe_nnreal_real.comp
      (Clock.PathMapV4.measurable_inversePhysicalTime.comp
        (measurable_id.prodMk measurable_const))).div_const _).sub_const _)
  have hbound (s : ℝ≥0) (z : ReductionImageV3.PhysicalField d L × Path d) :
      |f s z| ≤ K := by
    have hc := (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds
      z.1.1 z.2 L z.1.2 s).2
    have hr : (Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ) ≤
        Real.exp (2 * L) := by
      apply div_le_of_le_mul₀ s.coe_nonneg (Real.exp_pos _).le
      exact hc
    calc
      |f s z| ≤ |(Clock.PathMapV4.inversePhysicalTime z s : ℝ) / (s : ℝ)| + |η⁻¹| :=
        abs_sub _ _
      _ ≤ K := by
        rw [abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) s.coe_nonneg)]
        exact add_le_add hr le_rfl
  have hint (s : ℝ≥0) : Integrable (fun z => (f s z)^2) μ := by
    have hlp : MemLp (f s) 2 μ :=
      MemLp.of_bound (hfmeas s).aestronglyMeasurable K
        (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbound s z)
    exact hlp.integrable_sq
  have hprob := c20_inverse_clock_ratio_in_probability_of_l2 μ η hη hL2
  apply tendsto_order.2
  constructor
  · intro a ha
    filter_upwards with s
    exact lt_of_lt_of_le ha (integral_nonneg fun z => sq_nonneg (f s z))
  · intro b hb
    let ε : ℝ := Real.sqrt (b / 2)
    have hε : 0 < ε := Real.sqrt_pos.2 (by positivity)
    have hεsq : ε^2 = b / 2 := Real.sq_sqrt (by positivity)
    have htail : Tendsto (fun s : ℝ≥0 => (μ {z | ε < |f s z|}).toReal)
        atTop (𝓝 0) := by
      simpa only [ENNReal.toReal_zero, Function.comp_def, f] using
        (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hprob ε hε)
    have hlim : Tendsto (fun s : ℝ≥0 => ε^2 + K^2 *
        (μ {z | ε < |f s z|}).toReal) atTop (𝓝 (ε^2)) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul htail)
    have hevent := hlim.eventually (Iio_mem_nhds (show ε^2 < b by linarith))
    filter_upwards [hevent] with s hs
    let A := {z | ε < |f s z|}
    have hA : MeasurableSet A := by
      apply measurableSet_lt measurable_const
      simpa only [Real.norm_eq_abs] using (hfmeas s).norm
    have hbad : ∫ z in A, (f s z)^2 ∂μ ≤ K^2 * μ.real A := by
      apply le_trans (le_abs_self _)
      simpa only [Real.norm_eq_abs] using
        (norm_setIntegral_le_of_norm_le_const (measure_lt_top μ A) (f := fun z => (f s z)^2)
          (C := K^2) (fun z _ => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).2 (hbound s z)))
    have hgood : ∫ z in Aᶜ, (f s z)^2 ∂μ ≤ ε^2 := by
      have h := norm_setIntegral_le_of_norm_le_const (measure_lt_top μ Aᶜ)
        (f := fun z => (f s z)^2) (C := ε^2) (fun z hz => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hz' : |f s z| ≤ ε := le_of_not_gt hz
          simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε.le).2 hz')
      have hm : μ.real Aᶜ ≤ 1 := measureReal_le_one
      calc
        _ ≤ |∫ z in Aᶜ, (f s z)^2 ∂μ| := le_abs_self _
        _ ≤ ε^2 * μ.real Aᶜ := by simpa only [Real.norm_eq_abs] using h
        _ ≤ ε^2 := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hm (sq_nonneg ε)
    have hsplit := integral_add_compl hA (hint s)
    change (∫ z, (f s z)^2 ∂μ) < b
    have : (∫ z, (f s z)^2 ∂μ) ≤ ε^2 + K^2 * μ.real A := by linarith
    exact lt_of_le_of_lt this hs

/-- Mean-square convergence forces the physical clock speed into its
pointwise bounds and gives mean-square convergence of the inverse clock. -/
theorem c20_clock_speed_bounds_and_inverse_l2_of_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ)
      atTop (𝓝 0)) :
    (Real.exp (-2*L) ≤ η ∧ η ≤ Real.exp (2*L)) ∧
    Tendsto (fun s : ℝ≥0 => ∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹)^2 ∂μ)
      atTop (𝓝 0) := by
  let f : ℝ≥0 → ReductionImageV3.PhysicalField d L × Path d → ℝ := fun t z =>
    (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η
  have hint (t : ℝ≥0) : Integrable (fun z => (f t z)^2) μ := by
    have hf : Measurable (f t) := by
      dsimp [f]
      exact (((Clock.continuous_physicalPathClock_at (d := d) t).measurable.comp
        (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd)).div_const _).sub_const η
    have hlp : MemLp (f t) 2 μ := by
      apply MemLp.of_bound hf.aestronglyMeasurable (Real.exp (2 * L) + |η|)
      filter_upwards with z
      simp only [Real.norm_eq_abs]
      have hc := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 t).2
      have hr := div_le_of_le_mul₀ t.coe_nonneg (Real.exp_pos (2 * L)).le hc
      calc
        |f t z| ≤ |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ)| + |η| := abs_sub _ _
        _ ≤ Real.exp (2 * L) + |η| := by
          rw [abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg)]
          exact add_le_add hr le_rfl
    exact hlp.integrable_sq
  have hrange (t : ℝ≥0) (ht : 0 < t) (z : ReductionImageV3.PhysicalField d L × Path d) :
      Real.exp (-2 * L) ≤ (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ≤ Real.exp (2 * L) := by
    have ht' : 0 < (t : ℝ) := by exact_mod_cast ht
    have hc := Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 t
    exact ⟨(le_div_iff₀ ht').2 hc.1, (div_le_iff₀ ht').2 hc.2⟩
  have hbounds : Real.exp (-2 * L) ≤ η ∧ η ≤ Real.exp (2 * L) := by
    constructor
    · by_contra hn
      have hp : 0 < Real.exp (-2 * L) - η := sub_pos.mpr (lt_of_not_ge hn)
      have he := hL2.eventually (Iio_mem_nhds (sq_pos_of_pos hp))
      obtain ⟨t, ht, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ≥0)).and he).exists
      have hlower : (Real.exp (-2 * L) - η)^2 ≤ ∫ z, (f t z)^2 ∂μ := by
        have h := integral_mono (integrable_const ((Real.exp (-2 * L) - η)^2)) (hint t)
          (fun z => by
            have hz := (hrange t ht z).1
            change (Real.exp (-2 * L) - η)^2 ≤
              ((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^2
            apply (sq_le_sq₀ hp.le (by linarith)).2
            linarith)
        simpa using h
      change (∫ z, (f t z)^2 ∂μ) < (Real.exp (-2 * L) - η)^2 at hsmall
      exact (not_lt_of_ge hlower) hsmall
    · by_contra hn
      have hp : 0 < η - Real.exp (2 * L) := sub_pos.mpr (lt_of_not_ge hn)
      have he := hL2.eventually (Iio_mem_nhds (sq_pos_of_pos hp))
      obtain ⟨t, ht, hsmall⟩ := ((eventually_gt_atTop (0 : ℝ≥0)).and he).exists
      have hlower : (η - Real.exp (2 * L))^2 ≤ ∫ z, (f t z)^2 ∂μ := by
        have h := integral_mono (integrable_const ((η - Real.exp (2 * L))^2)) (hint t)
          (fun z => by
            have hz := (hrange t ht z).2
            change (η - Real.exp (2 * L))^2 ≤
              ((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^2
            calc
              _ ≤ (η - (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ))^2 :=
                (sq_le_sq₀ hp.le (by linarith)).2 (by linarith)
              _ = _ := by ring)
        simpa using h
      change (∫ z, (f t z)^2 ∂μ) < (η - Real.exp (2 * L))^2 at hsmall
      exact (not_lt_of_ge hlower) hsmall
  exact ⟨hbounds, c20_inverse_clock_ratio_l2_of_clock_l2 μ η
    (lt_of_lt_of_le (Real.exp_pos _) hbounds.1) hL2⟩


/-- Integer clock estimates interpolate under any probability law on regular fields and paths. -/
theorem c20_physical_clock_l2_real_time_of_integer_samples {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hmean : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ) /
        ((n:ℝ)+1) - η)^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ) - η)^2 ∂μ)
      atTop (𝓝 0) := by
  let f : ℝ≥0 → ReductionImageV3.PhysicalField d L × Path d → ℝ := fun t z =>
    (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η
  have hint (t : ℝ≥0) : Integrable (fun z => (f t z)^2) μ := by
    have hf : Measurable (f t) := by
      dsimp [f]
      exact (((Clock.continuous_physicalPathClock_at (d := d) t).measurable.comp
        (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd)).div_const _).sub_const η
    have hlp : MemLp (f t) 2 μ := by
      apply MemLp.of_bound hf.aestronglyMeasurable (Real.exp (2 * L) + |η|)
      filter_upwards with z
      simp only [Real.norm_eq_abs]
      have hc := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 t).2
      have hr := div_le_of_le_mul₀ t.coe_nonneg (Real.exp_pos (2 * L)).le hc
      calc
        |f t z| ≤ |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ)| + |η| := abs_sub _ _
        _ ≤ Real.exp (2 * L) + |η| := by
          rw [abs_of_nonneg (div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg)]
          exact add_le_add hr le_rfl
    exact hlp.integrable_sq
  have hcomp (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0)
      (hlo : (n : ℝ≥0) ≤ t) (hhi : t ≤ ((n+1 : ℕ) : ℝ≥0)) :
      (∫ z, (f t z)^2 ∂μ) ≤ 2 * (∫ z, (f (n : ℝ≥0) z)^2 ∂μ) +
        2 * (2 * Real.exp (2 * L) / (n : ℝ))^2 := by
    have hb : ∀ᵐ z ∂μ, (f t z)^2 ≤
        2 * (f (n : ℝ≥0) z)^2 + 2 * (2 * Real.exp (2 * L) / (n : ℝ))^2 := by
      filter_upwards with z
      have hc := c12_clock_ratio_integer_comparison z.1.1 z.2 L z.1.2.2.1 n hn t hlo hhi
      have hnonneg : 0 ≤ 2 * Real.exp (2 * L) / (n : ℝ) := by positivity
      have hs := (sq_le_sq₀ (abs_nonneg _) hnonneg).2 hc
      rw [sq_abs] at hs
      dsimp only [f]
      simp only [NNReal.coe_natCast]
      nlinarith only [hs, sq_nonneg
        (((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) -
          (Clock.physicalPathClock z.1.1 z.2 (n : ℝ≥0) : ℝ) / (n : ℝ)) -
          ((Clock.physicalPathClock z.1.1 z.2 (n : ℝ≥0) : ℝ) / (n : ℝ) - η))]
    have h := integral_mono_ae (hint t) (((hint n).const_mul 2).add (integrable_const _)) hb
    simp only [Pi.add_apply] at h
    rw [integral_add ((hint n).const_mul 2) (integrable_const _), integral_const_mul,
      integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    exact h
  let I := fun t : ℝ≥0 => ∫ z, (f t z)^2 ∂μ
  have hseq : Tendsto (fun n : ℕ => I (n : ℝ≥0)) atTop (𝓝 0) := by
    apply (tendsto_add_atTop_iff_nat 1).1
    simpa only [I, f, NNReal.coe_natCast, Nat.cast_add, Nat.cast_one,
      NNReal.coe_add, NNReal.coe_one] using hmean
  have hfloor : Tendsto (fun t : ℝ≥0 => ⌊t⌋₊) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact (eventually_ge_atTop (b : ℝ≥0)).mono fun t ht =>
      (Nat.le_floor_iff (show 0 ≤ t from bot_le)).2 ht
  have herror : Tendsto (fun t : ℝ≥0 =>
      2 * Real.exp (2 * L) / (⌊t⌋₊ : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 * Real.exp (2 * L))).comp hfloor
  have hupper : Tendsto (fun t : ℝ≥0 =>
      2 * I (⌊t⌋₊ : ℝ≥0) + 2 * (2 * Real.exp (2 * L) / (⌊t⌋₊ : ℝ))^2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero,
      zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using
      ((hseq.comp hfloor).const_mul 2).add ((herror.pow 2).const_mul 2)
  apply squeeze_zero' (Filter.Eventually.of_forall fun t =>
    integral_nonneg fun z => sq_nonneg _) _ hupper
  filter_upwards [hfloor.eventually (eventually_ge_atTop 1)] with t ht
  simpa only [I, f, NNReal.coe_natCast] using
    hcomp ⌊t⌋₊ ht t (Nat.floor_le (show 0 ≤ t from bot_le)) (Nat.lt_succ_floor t).le

/-- Integer-sample clock convergence determines the speed bounds and inverse-clock limit. -/
theorem c20_clock_speed_bounds_and_inverse_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) :
    (Real.exp (-2*L) ≤ η ∧ η ≤ Real.exp (2*L)) ∧
    Tendsto (fun s : ℝ≥0 => ∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z s : ℝ)/(s : ℝ)-η⁻¹)^2 ∂μ)
      atTop (𝓝 0) :=
  c20_clock_speed_bounds_and_inverse_l2_of_clock_l2 μ η
    (c20_physical_clock_l2_real_time_of_integer_samples μ η hL2)

/-- The physical inverse clock is increasing in its time parameter. -/
theorem c20_inverse_physical_time_monotone {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) :
    Monotone (Clock.PathMapV4.inversePhysicalTime z) :=
  (Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2).symm.monotone

/-- The physical inverse clock is continuous in its time parameter. -/
theorem c20_inverse_physical_time_continuous {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) :
    Continuous (Clock.PathMapV4.inversePhysicalTime z) :=
  (Clock.InverseMeaningV3.physicalPathClockOrderIso z.1.1 z.2 L z.1.2).symm.continuous

/-- Pointwise mean-square convergence at a fixed rescaled time. -/
theorem c20_inverse_clock_scaled_time_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)
        -(s : ℝ)*η⁻¹)^2 ∂μ) atTop (𝓝 0) := by
  by_cases hs : s = 0
  · subst s
    simp only [mul_zero, NNReal.coe_zero, zero_mul, sub_zero]
    have hz (z : ReductionImageV3.PhysicalField d L × Path d) :
        Clock.PathMapV4.inversePhysicalTime z 0 = 0 :=
      Clock.InverseMeaningV3.inversePhysicalPathClock_zero z.1.1 z.2 L z.1.2
    simp only [hz, NNReal.coe_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
    exact tendsto_const_nhds
  · have hspos : 0 < s := bot_lt_iff_ne_bot.mpr hs
    have hmul : Tendsto (fun t : ℝ≥0 => t * s) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b / s)] with t ht
      exact (div_le_iff₀ hspos).1 ht
    have hlim := ((c20_clock_speed_bounds_and_inverse_l2_of_integer_clock_l2 μ η hL2).2.comp hmul).const_mul ((s : ℝ)^2)
    have heq : ∀ᶠ t : ℝ≥0 in atTop, (∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)
        -(s : ℝ)*η⁻¹)^2 ∂μ) = (s : ℝ)^2 * (∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/((t*s : ℝ≥0) : ℝ)-η⁻¹)^2 ∂μ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
      rw [NNReal.coe_mul]
      field_simp
      <;> ring
    exact (tendsto_congr' heq).2 (by simpa only [mul_zero, Function.comp_def] using hlim)

/-- The compact-time inverse-clock deviation is measurable in the joint input. -/
theorem c20_measurable_inverse_clock_compact_deviation {d : ℕ} {L : ℝ}
    (η : ℝ) (T t : ℝ≥0) :
    Measurable (fun z : ReductionImageV3.PhysicalField d L × Path d =>
      ⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η⁻¹|) := by
  let f : Set.Icc (0 : ℝ≥0) T →
      ReductionImageV3.PhysicalField d L × Path d → ℝ := fun s z =>
        |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η⁻¹|
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  haveI := hD.to_subtype
  have hcont (z : ReductionImageV3.PhysicalField d L × Path d) :
      Continuous (fun s => f s z) := by
    dsimp [f]
    exact (((NNReal.continuous_coe.comp ((c20_inverse_physical_time_continuous z).comp
      (continuous_const.mul continuous_subtype_val))).div_const _).sub
        ((NNReal.continuous_coe.comp continuous_subtype_val).mul continuous_const)).abs
  have hmeas (s : Set.Icc (0 : ℝ≥0) T) : Measurable (f s) := by
    dsimp [f]
    exact (((measurable_coe_nnreal_real.comp
      (Clock.PathMapV4.measurable_inversePhysicalTime.comp
        (measurable_id.prodMk measurable_const))).div_const _).sub_const _).abs
  have heq : (fun z => ⨆ s, f s z) = (fun z => ⨆ s : D, f s.1 z) := by
    funext z
    exact (hdense.ciSup' (hcont z)).symm
  change Measurable (fun z => ⨆ s, f s z)
  rw [heq]
  exact Measurable.iSup (fun s : D => hmeas s.1)

/-- A monotone finite mesh brackets each point between consecutive mesh values. -/
theorem c20_monotone_mesh_brackets {α : Type*} [LinearOrder α]
    (g : ℕ → α) (hg : Monotone g) (x : α) (m : ℕ)
    (h0 : g 0 ≤ x) (hm : x ≤ g m) :
    ∃ n ≤ m, g n ≤ x ∧ x ≤ g (n + 1) := by
  classical
  have hex : ∃ n, x ≤ g n := ⟨m, hm⟩
  have hk := Nat.find_spec hex
  have hkm := Nat.find_min' hex hm
  cases hfind : Nat.find hex with
  | zero =>
    simp only [hfind] at hk
    exact ⟨0, Nat.zero_le _, h0, le_trans hk (hg (Nat.zero_le 1))⟩
  | succ k =>
    simp only [hfind] at hk hkm
    refine ⟨k, by omega, ?_, hk⟩
    exact le_of_not_ge (Nat.find_min hex (by rw [hfind]; omega))

/-- Monotonicity controls a deviation between two mesh points by endpoint deviations. -/
theorem c20_monotone_deviation_between (f : ℝ≥0 → ℝ) (hf : Monotone f)
    (c : ℝ) (hc : 0 ≤ c) {a x b : ℝ≥0} (hax : a ≤ x) (hxb : x ≤ b) :
    |f x - c * (x : ℝ)| ≤ |f a - c * (a : ℝ)| +
      |f b - c * (b : ℝ)| + c * ((b : ℝ) - (a : ℝ)) := by
  have ha := hf hax
  have hb := hf hxb
  have hax' : (a : ℝ) ≤ (x : ℝ) := by exact_mod_cast hax
  have hxb' : (x : ℝ) ≤ (b : ℝ) := by exact_mod_cast hxb
  have ha₁ := neg_abs_le (f a - c * (a : ℝ))
  have ha₂ := le_abs_self (f a - c * (a : ℝ))
  have hb₁ := neg_abs_le (f b - c * (b : ℝ))
  have hb₂ := le_abs_self (f b - c * (b : ℝ))
  have habsa := abs_nonneg (f a - c * (a : ℝ))
  have habsb := abs_nonneg (f b - c * (b : ℝ))
  apply abs_le.mpr
  constructor <;> nlinarith [mul_nonneg hc (sub_nonneg.mpr hax'),
    mul_nonneg hc (sub_nonneg.mpr hxb')]

/-- A deterministic bound for the compact-time inverse-clock deviation. -/
theorem c20_inverse_clock_compact_deviation_bound {d : ℕ} {L : ℝ}
    (η : ℝ) (T t : ℝ≥0) (z : ReductionImageV3.PhysicalField d L × Path d) :
    (⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|) ≤ (T : ℝ) * (Real.exp (2*L) + |η⁻¹|) := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
  apply ciSup_le
  intro s
  have hs : (s.1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast s.2.2
  have hr : (Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
      ≤ Real.exp (2*L) * (s.1 : ℝ) := by
    apply div_le_of_le_mul₀ t.coe_nonneg
      (mul_nonneg (Real.exp_pos _).le s.1.coe_nonneg)
    have hb := (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds
      z.1.1 z.2 L z.1.2 (t*s.1)).2
    rw [NNReal.coe_mul] at hb
    change (Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ) ≤
      Real.exp (2*L) * ((t : ℝ) * (s.1 : ℝ)) at hb
    convert hb using 1 <;> ring
  have hpos : 0 ≤ (Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ) :=
    div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg
  calc
    _ ≤ |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)| +
        |(s.1 : ℝ)*η⁻¹| := abs_sub _ _
    _ = (Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ) +
        (s.1 : ℝ)*|η⁻¹| := by rw [abs_of_nonneg hpos, abs_mul, abs_of_nonneg s.1.coe_nonneg]
    _ ≤ (T : ℝ) * (Real.exp (2*L) + |η⁻¹|) := by
      nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_pos (2*L)).le,
        mul_le_mul_of_nonneg_left hs (abs_nonneg η⁻¹)]

/-- The sum of mean-square errors over any fixed finite time mesh vanishes. -/
theorem c20_inverse_clock_finite_mesh_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (S : Finset ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∑ s ∈ S, ∫ z,
      ((Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)
        -(s : ℝ)*η⁻¹)^2 ∂μ) atTop (𝓝 0) := by
  simpa only [Finset.sum_const_zero] using
    (tendsto_finsetSum S fun s _ =>
      c20_inverse_clock_scaled_time_l2_of_integer_clock_l2 μ η hL2 s)

/-- Every compact nonnegative time interval admits an arbitrarily fine finite mesh. -/
theorem c20_exists_finite_time_mesh (T : ℝ≥0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (a : ℕ → ℝ≥0) (m : ℕ), Monotone a ∧ a 0 = 0 ∧ T ≤ a m ∧
      ∀ n ≤ m, (a (n+1) : ℝ) - (a n : ℝ) ≤ δ := by
  let e := Set.Icc.addNSMul (show (0 : ℝ) ≤ T from T.coe_nonneg) δ
  let a : ℕ → ℝ≥0 := fun n => ⟨(e n).1, (e n).2.1⟩
  have he : Monotone e := Set.Icc.monotone_addNSMul T.coe_nonneg hδ.le
  obtain ⟨m, hm⟩ := Set.Icc.addNSMul_eq_right T.coe_nonneg hδ
  refine ⟨a, m, ?_, ?_, ?_, ?_⟩
  · intro n k hnk
    change (e n).1 ≤ (e k).1
    exact he hnk
  · apply Subtype.ext
    exact Set.Icc.addNSMul_zero T.coe_nonneg
  · change (T : ℝ) ≤ (e m).1
    rw [hm m le_rfl]
  · intro n _
    change (e (n+1)).1 - (e n).1 ≤ δ
    exact (le_abs_self _).trans (Set.Icc.abs_sub_addNSMul_le T.coe_nonneg hδ.le n
      ⟨he (Nat.le_succ n), le_rfl⟩)

/-- A finite mesh bounds the uniform deviation of an increasing function. -/
theorem c20_monotone_compact_deviation_le_mesh_sum
    (g : ℝ≥0 → ℝ) (hg : Monotone g) (c δ : ℝ) (hc : 0 ≤ c)
    (T : ℝ≥0) (a : ℕ → ℝ≥0) (ha : Monotone a) (m : ℕ)
    (ha0 : a 0 = 0) (haT : T ≤ a m)
    (hgap : ∀ n ≤ m, (a (n+1) : ℝ) - (a n : ℝ) ≤ δ) :
    (⨆ x : Set.Icc (0 : ℝ≥0) T, |g x.1 - c * (x.1 : ℝ)|) ≤
      2 * (∑ n ∈ Finset.range (m+2), |g (a n) - c * (a n : ℝ)|) + c*δ := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
  apply ciSup_le
  intro x
  obtain ⟨n, hnm, hnx, hxn⟩ := c20_monotone_mesh_brackets a ha x.1 m
    (by simpa only [ha0] using x.2.1) (x.2.2.trans haT)
  let S := ∑ k ∈ Finset.range (m+2), |g (a k) - c * (a k : ℝ)|
  have hn : |g (a n) - c * (a n : ℝ)| ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (f := fun k : ℕ => |g (a k) - c * (a k : ℝ)|)
      (fun k _ => abs_nonneg _)
    simp only [Finset.mem_range]
    omega
  have hn1 : |g (a (n+1)) - c * (a (n+1) : ℝ)| ≤ S := by
    dsimp only [S]
    apply Finset.single_le_sum (f := fun k : ℕ => |g (a k) - c * (a k : ℝ)|)
      (fun k _ => abs_nonneg _)
    simp only [Finset.mem_range]
    omega
  have hbetween := c20_monotone_deviation_between g hg c hc hnx hxn
  have hwidth := mul_le_mul_of_nonneg_left (hgap n hnm) hc
  linarith

/-- Each fixed scaled-time inverse-clock error is square integrable. -/
theorem c20_inverse_clock_scaled_time_error_memLp {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (t s : ℝ≥0) :
    MemLp (fun z => (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)
      -(s : ℝ)*η⁻¹) 2 μ := by
  let f : ReductionImageV3.PhysicalField d L × Path d → ℝ := fun z =>
    (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ) - (s : ℝ)*η⁻¹
  have hmeas : Measurable f := by
    dsimp [f]
    exact (((measurable_coe_nnreal_real.comp
      (Clock.PathMapV4.measurable_inversePhysicalTime.comp
        (measurable_id.prodMk measurable_const))).div_const _).sub_const _)
  apply MemLp.of_bound hmeas.aestronglyMeasurable
    ((s : ℝ) * (Real.exp (2*L) + |η⁻¹|))
  filter_upwards with z
  rw [Real.norm_eq_abs]
  have hr : (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)
      ≤ Real.exp (2*L) * (s : ℝ) := by
    apply div_le_of_le_mul₀ t.coe_nonneg
      (mul_nonneg (Real.exp_pos _).le s.coe_nonneg)
    have h := (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds
      z.1.1 z.2 L z.1.2 (t*s)).2
    rw [NNReal.coe_mul] at h
    change (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ) ≤
      Real.exp (2*L) * ((t : ℝ) * (s : ℝ)) at h
    convert h using 1 <;> ring
  have hr0 : 0 ≤ (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ) :=
    div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg
  calc
    |f z| ≤ |(Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)| +
        |(s : ℝ)*η⁻¹| := abs_sub _ _
    _ ≤ (s : ℝ) * (Real.exp (2*L) + |η⁻¹|) := by
      rw [abs_of_nonneg hr0, abs_mul, abs_of_nonneg s.coe_nonneg]
      nlinarith

/-- Squaring a finite-mesh bound produces a sum of squared mesh errors. -/
theorem c20_mesh_sum_square_bound (v : ℕ → ℝ) (m : ℕ) (u b : ℝ)
    (hu : 0 ≤ u)
    (hbound : u ≤ 2 * (∑ k ∈ Finset.range (m+2), |v k|) + b) :
    u^2 ≤ 8 * ((m+2 : ℕ) : ℝ) * (∑ k ∈ Finset.range (m+2), (v k)^2) + 2*b^2 := by
  let S : ℝ := ∑ k ∈ Finset.range (m+2), |v k|
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcs : S^2 ≤ ((m+2 : ℕ) : ℝ) * (∑ k ∈ Finset.range (m+2), (v k)^2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (m+2))
      (fun _ => (1 : ℝ)) (fun k => |v k|)
    simpa [S, Finset.sum_const, nsmul_eq_mul, sq_abs] using h
  have hbound' : u ≤ 2*S+b := hbound
  nlinarith [sq_nonneg (2*S-b)]

/-- Integrating the finite mesh estimate bounds the compact mean-square error. -/
theorem c20_inverse_clock_compact_mesh_l2_bound {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 ≤ η⁻¹) (T t : ℝ≥0) (δ : ℝ)
    (a : ℕ → ℝ≥0) (ha : Monotone a) (m : ℕ) (ha0 : a 0 = 0) (haT : T ≤ a m)
    (hgap : ∀ n ≤ m, (a (n+1) : ℝ) - (a n : ℝ) ≤ δ) :
    (∫ z, (⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|)^2 ∂μ) ≤
      8 * ((m+2 : ℕ) : ℝ) * (∑ k ∈ Finset.range (m+2), ∫ z,
        ((Clock.PathMapV4.inversePhysicalTime z (t*a k) : ℝ)/(t : ℝ)
          -(a k : ℝ)*η⁻¹)^2 ∂μ) + 2*(η⁻¹*δ)^2 := by
  let f : ReductionImageV3.PhysicalField d L × Path d → ℝ := fun z =>
    ⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ) - (s.1 : ℝ)*η⁻¹|
  let e : ℕ → ReductionImageV3.PhysicalField d L × Path d → ℝ := fun k z =>
    (Clock.PathMapV4.inversePhysicalTime z (t*a k) : ℝ)/(t : ℝ) - (a k : ℝ)*η⁻¹
  have hf0 (z) : 0 ≤ f z := Real.iSup_nonneg fun _ => abs_nonneg _
  have hf : MemLp f 2 μ :=
    MemLp.of_bound (c20_measurable_inverse_clock_compact_deviation η T t).aestronglyMeasurable
      ((T : ℝ) * (Real.exp (2*L) + |η⁻¹|)) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
        exact c20_inverse_clock_compact_deviation_bound η T t z)
  have he (k) : Integrable (fun z => (e k z)^2) μ :=
    (c20_inverse_clock_scaled_time_error_memLp μ η t (a k)).integrable_sq
  have hs : Integrable (fun z => ∑ k ∈ Finset.range (m+2), (e k z)^2) μ :=
    integrable_finsetSum _ fun k _ => he k
  have hb : ∀ z, (f z)^2 ≤ 8 * ((m+2 : ℕ) : ℝ) *
      (∑ k ∈ Finset.range (m+2), (e k z)^2) + 2*(η⁻¹*δ)^2 := by
    intro z
    have hg : Monotone (fun s : ℝ≥0 =>
        (Clock.PathMapV4.inversePhysicalTime z (t*s) : ℝ)/(t : ℝ)) := by
      intro x y hxy
      apply div_le_div_of_nonneg_right _ t.coe_nonneg
      exact_mod_cast (c20_inverse_physical_time_monotone z (mul_le_mul_of_nonneg_left hxy (show 0 ≤ t from bot_le)))
    apply c20_mesh_sum_square_bound (fun k => e k z) m (f z) (η⁻¹*δ)
      (hf0 z)
    simpa only [f, e, mul_comm η⁻¹] using
      (c20_monotone_compact_deviation_le_mesh_sum _ hg η⁻¹ δ hη T a ha m ha0 haT hgap)
  have h := integral_mono_ae hf.integrable_sq
    ((hs.const_mul (8 * ((m+2 : ℕ) : ℝ))).add (integrable_const _))
    (Filter.Eventually.of_forall hb)
  change (∫ z, (f z)^2 ∂μ) ≤ ∫ z, 8 * ((m+2 : ℕ) : ℝ) *
    (∑ k ∈ Finset.range (m+2), (e k z)^2) + 2*(η⁻¹*δ)^2 ∂μ at h
  rw [integral_add (hs.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ (fun k _ => he k), integral_const, probReal_univ, one_smul] at h
  exact h

/-- Integer-clock mean-square convergence is uniform on compact rescaled times. -/
theorem c20_inverse_clock_compact_time_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (T : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ z,
      (⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η⁻¹|)^2 ∂μ) atTop (𝓝 0) := by
  have hη : 0 ≤ η⁻¹ := inv_nonneg.mpr
    ((Real.exp_pos (-2*L)).le.trans (c20_clock_speed_bounds_and_inverse_l2_of_integer_clock_l2 μ η hL2).1.1)
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards with t
    exact lt_of_lt_of_le hb (integral_nonneg fun z => sq_nonneg _)
  · intro b hb
    let δ : ℝ := Real.sqrt (b/4) / (η⁻¹ + 1)
    have hsqrt : 0 < Real.sqrt (b/4) := Real.sqrt_pos.2 (by positivity)
    have hden : 0 < η⁻¹ + 1 := by linarith
    have hδ : 0 < δ := div_pos hsqrt hden
    have hr : η⁻¹ * δ ≤ Real.sqrt (b/4) := by
      dsimp only [δ]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).2
      nlinarith
    have hsq : 2*(η⁻¹*δ)^2 < b := by
      have heq : (Real.sqrt (b/4))^2 = b/4 := Real.sq_sqrt (by positivity)
      have hp : 0 ≤ η⁻¹*δ := mul_nonneg hη hδ.le
      nlinarith [sq_nonneg (Real.sqrt (b/4) - η⁻¹*δ)]
    obtain ⟨a, m, ha, ha0, haT, hgap⟩ := c20_exists_finite_time_mesh T δ hδ
    have hlim : Tendsto (fun t : ℝ≥0 => 8 * ((m+2 : ℕ) : ℝ) *
        (∑ k ∈ Finset.range (m+2), ∫ z,
          ((Clock.PathMapV4.inversePhysicalTime z (t*a k) : ℝ)/(t : ℝ)
            -(a k : ℝ)*η⁻¹)^2 ∂μ) + 2*(η⁻¹*δ)^2)
        atTop (𝓝 (2*(η⁻¹*δ)^2)) := by
      have hsum := tendsto_finsetSum (Finset.range (m+2)) fun k _ =>
        c20_inverse_clock_scaled_time_l2_of_integer_clock_l2 μ η hL2 (a k)
      simpa only [Finset.sum_const_zero, mul_zero, zero_add] using
        ((hsum.const_mul (8 * ((m+2 : ℕ) : ℝ))).add_const (2*(η⁻¹*δ)^2))
    filter_upwards [hlim.eventually (Iio_mem_nhds hsq)] with t ht
    exact lt_of_le_of_lt
      (c20_inverse_clock_compact_mesh_l2_bound μ η hη T t δ a ha m ha0 haT hgap) ht

/-- Mean-square convergence of the compact deviation implies convergence in probability. -/
theorem c20_inverse_clock_compact_time_probability_of_compact_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (T : ℝ≥0)
    (hcompact : Tendsto (fun t : ℝ≥0 => ∫ z,
      (⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η⁻¹|)^2 ∂μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun t : ℝ≥0 => μ {z |
      ε < (⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η⁻¹|)}) atTop (𝓝 0) := by
  intro ε hε
  have hupper := ENNReal.tendsto_ofReal (hcompact.div_const (ε^2))
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun t => bot_le)
  filter_upwards with t
  let f : ReductionImageV3.PhysicalField d L × Path d → ℝ := fun z =>
    ⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|
  have hf0 (z) : 0 ≤ f z := Real.iSup_nonneg fun _ => abs_nonneg _
  have hf : MemLp f 2 μ :=
    MemLp.of_bound (c20_measurable_inverse_clock_compact_deviation η T t).aestronglyMeasurable
      ((T : ℝ) * (Real.exp (2*L) + |η⁻¹|)) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
        exact c20_inverse_clock_compact_deviation_bound η T t z)
  calc
    _ ≤ ENNReal.ofReal (∫ z, (f z)^2 / ε^2 ∂μ) := by
      apply (hf.integrable_sq.div_const (ε^2)).measure_le_integral
        (Filter.Eventually.of_forall fun z => div_nonneg (sq_nonneg _) (sq_nonneg ε))
      intro z hz
      apply (le_div_iff₀ (sq_pos_of_pos hε)).2
      simpa only [one_mul] using (sq_le_sq₀ hε.le (hf0 z)).2 hz.le
    _ = _ := by rw [integral_div]


/-- Integer-clock mean-square convergence gives compact-time convergence in probability. -/
theorem c20_inverse_clock_compact_time_probability_of_integer_clock_l2
    {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
       ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun t : ℝ≥0 => μ {z |
      ε < (⨆ s : Set.Icc (0 : ℝ≥0) T,
       |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|)}) atTop (𝓝 0) :=
  c20_inverse_clock_compact_time_probability_of_compact_l2 μ η T
    (c20_inverse_clock_compact_time_l2_of_integer_clock_l2 μ η hL2 T)


/-- Compact convergence remains valid up to an almost surely finite random horizon. -/
theorem c20_inverse_clock_random_horizon_probability_of_integer_clock_l2
    {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
       ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0))
    (T : ReductionImageV3.PhysicalField d L × Path d → ℝ≥0) (hT : Measurable T) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun t : ℝ≥0 => μ {z |
      ε < (⨆ s : Set.Icc (0 : ℝ≥0) (T z),
       |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|)}) atTop (𝓝 0) := by
  intro ε hε
  let A : ℕ → Set (ReductionImageV3.PhysicalField d L × Path d) :=
    fun n => {z | (n : ℝ≥0) < T z}
  have hAmeas (n : ℕ) : MeasurableSet (A n) := measurableSet_lt measurable_const hT
  have hAanti : Antitone A := by
    intro n m hnm z hz
    change (m : ℝ≥0) < T z at hz
    change (n : ℝ≥0) < T z
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hz
  have hAempty : (⋂ n, A n) = ∅ := by
    apply subset_antisymm _ (Set.empty_subset _)
    intro z hz
    have hz' : ∀ n : ℕ, (n : ℝ≥0) < T z := by simpa [A] using hz
    obtain ⟨n, hn⟩ := exists_nat_gt (T z : ℝ)
    have hn' : (T z : ℝ) ≤ (n : ℝ) := hn.le
    have := hz' n
    have : (n : ℝ) < (T z : ℝ) := by exact_mod_cast this
    linarith
  have htail : Tendsto (fun n => μ (A n)) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (fun n => (hAmeas n).nullMeasurableSet) hAanti ⟨0, measure_ne_top μ _⟩
    simpa only [hAempty, measure_empty, Function.comp_def] using h
  apply ENNReal.tendsto_nhds_zero.2
  intro δ hδ
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htail).2 (δ / 2) (ENNReal.half_pos hδ.ne')).exists
  have hdet := c20_inverse_clock_compact_time_probability_of_integer_clock_l2 μ η hL2 (n : ℝ≥0) ε hε
  have hdet' := (tendsto_order.1 hdet).2 (δ / 2) (ENNReal.half_pos hδ.ne')
  filter_upwards [hdet'] with t ht
  calc
    μ {z | ε < (⨆ s : Set.Icc (0 : ℝ≥0) (T z),
       |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|)} ≤
        μ (A n) + μ {z | ε < (⨆ s : Set.Icc (0 : ℝ≥0) (n : ℝ≥0),
       |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η⁻¹|)} := by
      apply le_trans (measure_mono ?_) (measure_union_le _ _)
      intro z hz
      by_cases hzn : (n : ℝ≥0) < T z
      · exact Or.inl hzn
      · right
        simp only [Set.mem_setOf_eq] at hz ⊢
        have hle : T z ≤ (n : ℝ≥0) := le_of_not_gt hzn
        have hbound : BddAbove (Set.range fun s : Set.Icc (0 : ℝ≥0) (n : ℝ≥0) =>
          |(Clock.PathMapV4.inversePhysicalTime z (t*s.1) : ℝ)/(t : ℝ)
            -(s.1 : ℝ)*η⁻¹|) := by
          apply IsCompact.bddAbove
          apply isCompact_range
          exact (((NNReal.continuous_coe.comp ((c20_inverse_physical_time_continuous z).comp
            (continuous_const.mul continuous_subtype_val))).div_const _).sub
              ((NNReal.continuous_coe.comp continuous_subtype_val).mul continuous_const)).abs
        apply lt_of_lt_of_le hz
        letI : Nonempty (Set.Icc (0 : ℝ≥0) (T z)) := ⟨⟨0, le_rfl, bot_le⟩⟩
        apply ciSup_le
        intro s
        exact le_ciSup hbound ⟨s.1, s.2.1, le_trans s.2.2 hle⟩
    _ ≤ δ / 2 + δ / 2 := add_le_add hn.le ht.le
    _ = δ := ENNReal.add_halves δ

theorem c20_forward_clock_scaled_time_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)
        -(s : ℝ)*η)^2 ∂μ) atTop (𝓝 0) := by
  by_cases hs : s = 0
  · subst s
    simp only [mul_zero, NNReal.coe_zero, zero_mul, sub_zero]
    have hz (z : ReductionImageV3.PhysicalField d L × Path d) :
        Clock.physicalPathClock z.1.1 z.2 0 = 0 :=
      by
        apply NNReal.eq
        have h := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 0).2
        simp only [NNReal.coe_zero, mul_zero] at h ⊢
        exact le_antisymm h (NNReal.coe_nonneg _)
    simp only [hz, NNReal.coe_zero, zero_div, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero]
    exact tendsto_const_nhds
  · have hspos : 0 < s := bot_lt_iff_ne_bot.mpr hs
    have hmul : Tendsto (fun t : ℝ≥0 => t * s) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b / s)] with t ht
      exact (div_le_iff₀ hspos).1 ht
    have hlim := ((c20_physical_clock_l2_real_time_of_integer_samples μ η hL2).comp hmul).const_mul ((s : ℝ)^2)
    have heq : ∀ᶠ t : ℝ≥0 in atTop, (∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)
        -(s : ℝ)*η)^2 ∂μ) = (s : ℝ)^2 * (∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/((t*s : ℝ≥0) : ℝ)-η)^2 ∂μ) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
      have hs' : (s : ℝ) ≠ 0 := by exact_mod_cast hs
      rw [NNReal.coe_mul]
      field_simp
      <;> ring
    exact (tendsto_congr' heq).2 (by simpa only [mul_zero, Function.comp_def] using hlim)


theorem c20_measurable_forward_clock_compact_deviation {d : ℕ} {L : ℝ}
    (η : ℝ) (T t : ℝ≥0) :
    Measurable (fun z : ReductionImageV3.PhysicalField d L × Path d =>
      ⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η|) := by
  let f : Set.Icc (0 : ℝ≥0) T →
      ReductionImageV3.PhysicalField d L × Path d → ℝ := fun s z =>
        |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η|
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ≥0) T)
  haveI := hD.to_subtype
  have hcont (z : ReductionImageV3.PhysicalField d L × Path d) :
      Continuous (fun s => f s z) := by
    dsimp [f]
    exact (((NNReal.continuous_coe.comp ((Clock.InverseMeaningV3.physicalPathClock_continuous z.1.1 z.2).comp
      (continuous_const.mul continuous_subtype_val))).div_const _).sub
        ((NNReal.continuous_coe.comp continuous_subtype_val).mul continuous_const)).abs
  have hmeas (s : Set.Icc (0 : ℝ≥0) T) : Measurable (f s) := by
    dsimp [f]
    exact ((((Clock.continuous_physicalPathClock_at (d := d) (t*s.1)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd)).div_const _).sub_const _).abs
  have heq : (fun z => ⨆ s, f s z) = (fun z => ⨆ s : D, f s.1 z) := by
    funext z
    exact (hdense.ciSup' (hcont z)).symm
  change Measurable (fun z => ⨆ s, f s z)
  rw [heq]
  exact Measurable.iSup (fun s : D => hmeas s.1)


theorem c20_forward_clock_compact_deviation_bound {d : ℕ} {L : ℝ}
    (η : ℝ) (T t : ℝ≥0) (z : ReductionImageV3.PhysicalField d L × Path d) :
    (⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η|) ≤ (T : ℝ) * (Real.exp (2*L) + |η|) := by
  letI : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, bot_le⟩⟩
  apply ciSup_le
  intro s
  have hs : (s.1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast s.2.2
  have hr : (Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
      ≤ Real.exp (2*L) * (s.1 : ℝ) := by
    apply div_le_of_le_mul₀ t.coe_nonneg
      (mul_nonneg (Real.exp_pos _).le s.1.coe_nonneg)
    have hb := (Clock.InverseMeaningV3.physicalPathClock_bounds
      z.1.1 z.2 L z.1.2.2.1 (t*s.1)).2
    rw [NNReal.coe_mul] at hb
    change (Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ) ≤
      Real.exp (2*L) * ((t : ℝ) * (s.1 : ℝ)) at hb
    convert hb using 1 <;> ring
  have hpos : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) :=
    div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg
  calc
    _ ≤ |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)| +
        |(s.1 : ℝ)*η| := abs_sub _ _
    _ = (Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) +
        (s.1 : ℝ)*|η| := by rw [abs_of_nonneg hpos, abs_mul, abs_of_nonneg s.1.coe_nonneg]
    _ ≤ (T : ℝ) * (Real.exp (2*L) + |η|) := by
      nlinarith [mul_le_mul_of_nonneg_left hs (Real.exp_pos (2*L)).le,
        mul_le_mul_of_nonneg_left hs (abs_nonneg η)]


theorem c20_forward_clock_scaled_time_error_memLp {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (t s : ℝ≥0) :
    MemLp (fun z => (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)
      -(s : ℝ)*η) 2 μ := by
  let f : ReductionImageV3.PhysicalField d L × Path d → ℝ := fun z =>
    (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ) - (s : ℝ)*η
  have hmeas : Measurable f := by
    dsimp [f]
    exact ((((Clock.continuous_physicalPathClock_at (d := d) (t*s)).measurable.comp
      (measurable_subtype_coe.comp measurable_fst |>.prodMk measurable_snd)).div_const _).sub_const _)
  apply MemLp.of_bound hmeas.aestronglyMeasurable
    ((s : ℝ) * (Real.exp (2*L) + |η|))
  filter_upwards with z
  rw [Real.norm_eq_abs]
  have hr : (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)
      ≤ Real.exp (2*L) * (s : ℝ) := by
    apply div_le_of_le_mul₀ t.coe_nonneg
      (mul_nonneg (Real.exp_pos _).le s.coe_nonneg)
    have h := (Clock.InverseMeaningV3.physicalPathClock_bounds
      z.1.1 z.2 L z.1.2.2.1 (t*s)).2
    rw [NNReal.coe_mul] at h
    change (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ) ≤
      Real.exp (2*L) * ((t : ℝ) * (s : ℝ)) at h
    convert h using 1 <;> ring
  have hr0 : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ) :=
    div_nonneg (NNReal.coe_nonneg _) t.coe_nonneg
  calc
    |f z| ≤ |(Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)| +
        |(s : ℝ)*η| := abs_sub _ _
    _ ≤ (s : ℝ) * (Real.exp (2*L) + |η|) := by
      rw [abs_of_nonneg hr0, abs_mul, abs_of_nonneg s.coe_nonneg]
      nlinarith


theorem c20_forward_clock_compact_mesh_l2_bound {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (hη : 0 ≤ η) (T t : ℝ≥0) (δ : ℝ)
    (a : ℕ → ℝ≥0) (ha : Monotone a) (m : ℕ) (ha0 : a 0 = 0) (haT : T ≤ a m)
    (hgap : ∀ n ≤ m, (a (n+1) : ℝ) - (a n : ℝ) ≤ δ) :
    (∫ z, (⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
        -(s.1 : ℝ)*η|)^2 ∂μ) ≤
      8 * ((m+2 : ℕ) : ℝ) * (∑ k ∈ Finset.range (m+2), ∫ z,
        ((Clock.physicalPathClock z.1.1 z.2 (t*a k) : ℝ)/(t : ℝ)
          -(a k : ℝ)*η)^2 ∂μ) + 2*(η*δ)^2 := by
  let f : ReductionImageV3.PhysicalField d L × Path d → ℝ := fun z =>
    ⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) - (s.1 : ℝ)*η|
  let e : ℕ → ReductionImageV3.PhysicalField d L × Path d → ℝ := fun k z =>
    (Clock.physicalPathClock z.1.1 z.2 (t*a k) : ℝ)/(t : ℝ) - (a k : ℝ)*η
  have hf0 (z) : 0 ≤ f z := Real.iSup_nonneg fun _ => abs_nonneg _
  have hf : MemLp f 2 μ :=
    MemLp.of_bound (c20_measurable_forward_clock_compact_deviation η T t).aestronglyMeasurable
      ((T : ℝ) * (Real.exp (2*L) + |η|)) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 z)]
        exact c20_forward_clock_compact_deviation_bound η T t z)
  have he (k) : Integrable (fun z => (e k z)^2) μ :=
    (c20_forward_clock_scaled_time_error_memLp μ η t (a k)).integrable_sq
  have hs : Integrable (fun z => ∑ k ∈ Finset.range (m+2), (e k z)^2) μ :=
    integrable_finsetSum _ fun k _ => he k
  have hb : ∀ z, (f z)^2 ≤ 8 * ((m+2 : ℕ) : ℝ) *
      (∑ k ∈ Finset.range (m+2), (e k z)^2) + 2*(η*δ)^2 := by
    intro z
    have hg : Monotone (fun s : ℝ≥0 =>
        (Clock.physicalPathClock z.1.1 z.2 (t*s) : ℝ)/(t : ℝ)) := by
      intro x y hxy
      apply div_le_div_of_nonneg_right _ t.coe_nonneg
      exact_mod_cast ((Clock.InverseMeaningV3.physicalPathClock_strictMono z.1.1 z.2 L z.1.2).monotone (mul_le_mul_of_nonneg_left hxy (show 0 ≤ t from bot_le)))
    apply c20_mesh_sum_square_bound (fun k => e k z) m (f z) (η*δ)
      (hf0 z)
    simpa only [f, e, mul_comm η] using
      (c20_monotone_compact_deviation_le_mesh_sum _ hg η δ hη T a ha m ha0 haT hgap)
  have h := integral_mono_ae hf.integrable_sq
    ((hs.const_mul (8 * ((m+2 : ℕ) : ℝ))).add (integrable_const _))
    (Filter.Eventually.of_forall hb)
  change (∫ z, (f z)^2 ∂μ) ≤ ∫ z, 8 * ((m+2 : ℕ) : ℝ) *
    (∑ k ∈ Finset.range (m+2), (e k z)^2) + 2*(η*δ)^2 ∂μ at h
  rw [integral_add (hs.const_mul _) (integrable_const _), integral_const_mul,
    integral_finsetSum _ (fun k _ => he k), integral_const, probReal_univ, one_smul] at h
  exact h


theorem c20_forward_clock_compact_time_l2_of_integer_clock_l2 {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (T : ℝ≥0) :
    (∀ t : ℝ≥0, MemLp (fun z => ⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) - (s.1 : ℝ)*η|) 2 μ) ∧
    Tendsto (fun t : ℝ≥0 => ∫ z,
      (⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
          -(s.1 : ℝ)*η|)^2 ∂μ) atTop (𝓝 0) := by
  constructor
  · intro t
    apply MemLp.of_bound (c20_measurable_forward_clock_compact_deviation η T t).aestronglyMeasurable
      ((T : ℝ) * (Real.exp (2*L) + |η|))
    filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.iSup_nonneg fun _ => abs_nonneg _)]
    exact c20_forward_clock_compact_deviation_bound η T t z
  · have hη : 0 ≤ η :=
      (Real.exp_pos (-2*L)).le.trans (c20_clock_speed_bounds_and_inverse_l2_of_integer_clock_l2 μ η hL2).1.1
    apply tendsto_order.2
    constructor
    · intro b hb
      filter_upwards with t
      exact lt_of_lt_of_le hb (integral_nonneg fun z => sq_nonneg _)
    · intro b hb
      let δ : ℝ := Real.sqrt (b/4) / (η + 1)
      have hsqrt : 0 < Real.sqrt (b/4) := Real.sqrt_pos.2 (by positivity)
      have hden : 0 < η + 1 := by linarith
      have hδ : 0 < δ := div_pos hsqrt hden
      have hr : η * δ ≤ Real.sqrt (b/4) := by
        dsimp only [δ]
        rw [← mul_div_assoc]
        apply (div_le_iff₀ hden).2
        nlinarith
      have hsq : 2*(η*δ)^2 < b := by
        have heq : (Real.sqrt (b/4))^2 = b/4 := Real.sq_sqrt (by positivity)
        have hp : 0 ≤ η*δ := mul_nonneg hη hδ.le
        nlinarith [sq_nonneg (Real.sqrt (b/4) - η*δ)]
      obtain ⟨a, m, ha, ha0, haT, hgap⟩ := c20_exists_finite_time_mesh T δ hδ
      have hlim : Tendsto (fun t : ℝ≥0 => 8 * ((m+2 : ℕ) : ℝ) *
          (∑ k ∈ Finset.range (m+2), ∫ z,
            ((Clock.physicalPathClock z.1.1 z.2 (t*a k) : ℝ)/(t : ℝ)
              -(a k : ℝ)*η)^2 ∂μ) + 2*(η*δ)^2)
          atTop (𝓝 (2*(η*δ)^2)) := by
        have hsum := tendsto_finsetSum (Finset.range (m+2)) fun k _ =>
          c20_forward_clock_scaled_time_l2_of_integer_clock_l2 μ η hL2 (a k)
        simpa only [Finset.sum_const_zero, mul_zero, zero_add] using
          ((hsum.const_mul (8 * ((m+2 : ℕ) : ℝ))).add_const (2*(η*δ)^2))
      filter_upwards [hlim.eventually (Iio_mem_nhds hsq)] with t ht
      exact lt_of_le_of_lt
        (c20_forward_clock_compact_mesh_l2_bound μ η hη T t δ a ha m ha0 haT hgap) ht


/-- Integer-clock mean-square convergence gives forward-clock compact-time convergence in
probability. -/
theorem c20_forward_clock_compact_time_probability_of_integer_clock_l2
    {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ)
    (hL2 : Tendsto (fun n : ℕ => ∫ z,
      ((Clock.physicalPathClock z.1.1 z.2 ((n+1 : ℕ) : ℝ≥0) : ℝ)/
        ((n:ℝ)+1)-η)^2 ∂μ) atTop (𝓝 0)) (T : ℝ≥0) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun t : ℝ≥0 =>
      μ {z | ε < ⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) - (s.1 : ℝ)*η|})
      atTop (𝓝 0) := by
  intro ε hε
  have hcompact := (c20_forward_clock_compact_time_l2_of_integer_clock_l2 μ η hL2 T).2
  have hupper := ENNReal.tendsto_ofReal (hcompact.div_const (ε^2))
  simp only [zero_div, ENNReal.ofReal_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall fun t => bot_le)
  filter_upwards with t
  have hf := (c20_forward_clock_compact_time_l2_of_integer_clock_l2 μ η hL2 T).1 t
  have hf0 (z : ReductionImageV3.PhysicalField d L × Path d) : 0 ≤ ⨆ s : Set.Icc (0 : ℝ≥0) T,
      |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ) - (s.1 : ℝ)*η| :=
    Real.iSup_nonneg fun _ => abs_nonneg _
  calc
    _ ≤ ENNReal.ofReal (∫ z, (⨆ s : Set.Icc (0 : ℝ≥0) T,
        |(Clock.physicalPathClock z.1.1 z.2 (t*s.1) : ℝ)/(t : ℝ)
          - (s.1 : ℝ)*η|)^2 / ε^2 ∂μ) := by
      apply (hf.integrable_sq.div_const (ε^2)).measure_le_integral
        (Filter.Eventually.of_forall fun z => div_nonneg (sq_nonneg _) (sq_nonneg ε))
      intro z hz
      apply (le_div_iff₀ (sq_pos_of_pos hε)).2
      simpa only [one_mul] using (sq_le_sq₀ hε.le (hf0 z)).2 hz.le
    _ = _ := by rw [integral_div]


end EinsteinFull.Blueprint
