import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Calculus.WeightedH1QuotientSupport
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.ContinuousMap.Bounded.Normed

open MeasureTheory
open ProbabilityTheory
open scoped Topology

namespace EinsteinRelation

/-- The bounded-continuous-test formulation of the Feller property for a state kernel. -/
def IsFellerKernel {d : ℕ} (K : Kernel (Vec d) (Vec d)) : Prop :=
  ∀ f : BoundedContinuousFunction (Vec d) ℝ,
    Continuous (fun x => ∫ y, f y ∂K x)

/-- Equality of two Markov kernels at Lebesgue-almost every starting point extends to every
starting point when both kernels have the Feller property. The proof first extends each bounded
continuous test integral by the full support of Euclidean volume, then uses separation of finite
Borel measures by bounded continuous integrals. -/
theorem kernel_eq_of_ae_eq_of_isFeller {d : ℕ}
    {K L : Kernel (Vec d) (Vec d)} [IsMarkovKernel K] [IsMarkovKernel L]
    (hK : IsFellerKernel K) (hL : IsFellerKernel L)
    (hAE : ∀ᵐ x ∂(volume : Measure (Vec d)), K x = L x) : K = L := by
  apply Kernel.ext
  intro x
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let gK : Vec d → ℝ := fun z => ∫ y, f y ∂K z
  let gL : Vec d → ℝ := fun z => ∫ y, f y ∂L z
  have hgK : Continuous gK := hK f
  have hgL : Continuous gL := hL f
  have hAEint : gK =ᵐ[volume] gL := by
    filter_upwards [hAE] with z hz
    simp only [gK, gL, hz]
  have hEq : gK = gL := (hgK.ae_eq_iff_eq volume hgL).mp hAEint
  exact congrFun hEq x

/-- The same uniqueness bridge when almost-everywhere equality is initially known under a
continuous strictly positive density with respect to Euclidean volume. -/
theorem kernel_eq_of_ae_eq_withDensity_of_isFeller {d : ℕ}
    {K L : Kernel (Vec d) (Vec d)} [IsMarkovKernel K] [IsMarkovKernel L]
    (hK : IsFellerKernel K) (hL : IsFellerKernel L)
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (hAE : ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x)),
      K x = L x) : K = L := by
  apply kernel_eq_of_ae_eq_of_isFeller hK hL
  exact (SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
    ρ hρ hρpos _).mp hAE

theorem physicalReversibleDensity_continuous {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam : ℝ) :
    Continuous (External.GantertSection7Support.physicalReversibleDensity ω hd lam) := by
  change Continuous (fun x : Vec d =>
    External.GantertSection7Support.physicalForceWeight hd lam x * clockDensity ω x)
  exact (External.GantertSection7Support.physicalForceWeight_continuous hd lam).mul
    (Real.continuous_exp.comp (continuous_const.mul ω.2.continuous))

theorem physicalReversibleDensity_pos {d : ℕ} (ω : FieldPair d)
    (hd : 2 ≤ d) (lam : ℝ) (x : Vec d) :
    0 < External.GantertSection7Support.physicalReversibleDensity ω hd lam x := by
  exact mul_pos (External.GantertSection7Support.physicalForceWeight_pos hd lam x)
    (clockDensity_pos ω x)

/-- The all-start conclusion from almost-everywhere equality under the physical reversible
measure. Positivity of its actual density turns that exceptional-set statement into a
Lebesgue-a.e. statement before the Feller extension. -/
theorem kernel_eq_of_ae_eq_physicalReversibleMeasure_of_isFeller {d : ℕ}
    {K L : Kernel (Vec d) (Vec d)} [IsMarkovKernel K] [IsMarkovKernel L]
    (hK : IsFellerKernel K) (hL : IsFellerKernel L)
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (hAE : ∀ᵐ x ∂External.GantertSection7Support.physicalReversibleMeasure ω hd lam,
      K x = L x) : K = L := by
  apply kernel_eq_of_ae_eq_of_isFeller hK hL
  exact (SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
    (External.GantertSection7Support.physicalReversibleDensity ω hd lam)
    (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _).mp hAE

/-- The identity transition kernel acts on a bounded continuous observable by evaluation at its
starting point. -/
theorem identityKernel_integral_boundedContinuous {d : ℕ}
    (f : BoundedContinuousFunction (Vec d) ℝ) (x : Vec d) :
    (∫ y, f y ∂(Kernel.id : Kernel (Vec d) (Vec d)) x) = f x := by
  rw [Kernel.id_apply, integral_dirac]

theorem isFellerKernel_identity {d : ℕ} :
    IsFellerKernel (Kernel.id : Kernel (Vec d) (Vec d)) := by
  intro f
  have hfun : (fun x : Vec d => ∫ y, f y ∂(Kernel.id : Kernel (Vec d) (Vec d)) x) = f :=
    funext (identityKernel_integral_boundedContinuous f)
  rw [hfun]
  exact f.continuous

/-- A nonconstant bounded continuous coordinate observable for the manuscript's first direction. -/
noncomputable def firstCoordinateSineTest {d : ℕ} (hd : 2 ≤ d) :
    BoundedContinuousFunction (Vec d) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => Real.sin (x (External.GantertSection7Support.firstCoordinateIndex hd)))
    (Real.continuous_sin.comp
      (continuous_apply (External.GantertSection7Support.firstCoordinateIndex hd)))
    1 (fun x => by
      simpa only [Real.norm_eq_abs] using
        Real.abs_sin_le_one (x (External.GantertSection7Support.firstCoordinateIndex hd)))

theorem firstCoordinateSineTest_nonconstant {d : ℕ} (hd : 2 ≤ d) :
    ∃ x y : Vec d, firstCoordinateSineTest hd x ≠ firstCoordinateSineTest hd y := by
  let i := External.GantertSection7Support.firstCoordinateIndex hd
  let y : Vec d := fun j => if j = i then Real.pi / 2 else 0
  refine ⟨0, y, ?_⟩
  have hzero : firstCoordinateSineTest hd 0 = 0 := by
    simp [firstCoordinateSineTest]
  have hone : firstCoordinateSineTest hd y = 1 := by
    simp [firstCoordinateSineTest, y, i]
  rw [hzero, hone]
  norm_num

theorem identityKernel_action_nonconstant {d : ℕ} (hd : 2 ≤ d) :
    ∃ x y : Vec d,
      (∫ z, firstCoordinateSineTest hd z ∂(Kernel.id : Kernel (Vec d) (Vec d)) x) ≠
        (∫ z, firstCoordinateSineTest hd z ∂(Kernel.id : Kernel (Vec d) (Vec d)) y) := by
  obtain ⟨x, y, hxy⟩ := firstCoordinateSineTest_nonconstant hd
  exact ⟨x, y, by rwa [identityKernel_integral_boundedContinuous,
    identityKernel_integral_boundedContinuous]⟩

/-- This real nonconstant kernel/test consumer exercises the physical-density conversion and the
all-start uniqueness bridge without asserting Feller hypotheses for any cited diffusion witness. -/
theorem identityKernel_test_consumer {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) :
    (∫ y, firstCoordinateSineTest hd y ∂(Kernel.id : Kernel (Vec d) (Vec d)) 0) =
      (∫ y, firstCoordinateSineTest hd y ∂
        (Kernel.deterministic id measurable_id : Kernel (Vec d) (Vec d)) 0) := by
  have hAE : ∀ᵐ x ∂External.GantertSection7Support.physicalReversibleMeasure ω hd lam,
      (Kernel.id : Kernel (Vec d) (Vec d)) x =
        (Kernel.deterministic id measurable_id : Kernel (Vec d) (Vec d)) x := by
    filter_upwards [] with x
    rw [Kernel.id_apply, Kernel.deterministic_apply]
    rfl
  have hK : (Kernel.id : Kernel (Vec d) (Vec d)) =
      (Kernel.deterministic id measurable_id : Kernel (Vec d) (Vec d)) :=
    kernel_eq_of_ae_eq_physicalReversibleMeasure_of_isFeller
      isFellerKernel_identity (by
        intro f
        have hfun : (fun x : Vec d => ∫ y, f y ∂
            (Kernel.deterministic id measurable_id : Kernel (Vec d) (Vec d)) x) = f := by
          funext x
          rw [Kernel.deterministic_apply, integral_dirac]
          simp
        rw [hfun]
        exact f.continuous) ω hd lam hAE
  rw [hK]

end EinsteinRelation
