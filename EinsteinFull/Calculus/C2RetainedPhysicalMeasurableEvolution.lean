import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.S5CoefficientSupport
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import EinsteinRelation.Correctors.WeakPartialAddition
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.BigOperators.Option
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
local instance : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
/-- Joint coefficient measurability gives measurable physical form entries
on each fixed pair of L2 data, without an L∞ topology on coefficient families. -/
private theorem c2m_measurable_coefficient_pairing
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun s : Ω × Vec d => a s.1 s.2))
    (j k : Fin d) (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    Measurable (fun ω => ∫ x, (a ω x j k : ℂ) * u x * v x) := by
  have hcoord : Measurable (fun A : Mat d => A j k) :=
    (show Continuous (fun A : Mat d => A j k) from
      (continuous_apply k).comp (continuous_apply j)).measurable
  have hc : Measurable (fun s : Ω × Vec d => (a s.1 s.2 j k : ℂ)) :=
    Complex.measurable_ofReal.comp (hcoord.comp ha)
  have hu : Measurable (fun s : Ω × Vec d => u s.2) :=
    (Lp.stronglyMeasurable u).measurable.comp measurable_snd
  have hv : Measurable (fun s : Ω × Vec d => v s.2) :=
    (Lp.stronglyMeasurable v).measurable.comp measurable_snd
  exact ((hc.mul hu).mul hv).stronglyMeasurable.integral_prod_right'.measurable

/-- Uniform ellipticity bounds each actual matrix entry. -/
private theorem c2m_entry_bound {d : ℕ} {A : Mat d} {Λ : ℝ}
    (hA : S5Elliptic A Λ) (j k : Fin d) : |A j k| ≤ Λ := by
  have h := s5Bil_abs_le hA (Pi.single j 1) (Pi.single k 1)
  simpa [s5Bil, s5Nrm, Pi.single_apply, ite_mul, mul_ite] using h

/-- The jointly measurable elliptic family defines bounded physical L2
multipliers for each coefficient entry and each parameter. -/
private theorem c2m_coefficient_memLp
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (Λ : ℝ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ) :
    ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume := by
  intro ω j k
  have hcoord : Measurable (fun A : Mat d => A j k) :=
    (show Continuous (fun A : Mat d => A j k) from
      (continuous_apply k).comp (continuous_apply j)).measurable
  have hm : Measurable (fun x => (a ω x j k : ℂ)) :=
    Complex.measurable_ofReal.comp
      (hcoord.comp (ha.comp (measurable_const.prodMk measurable_id)))
  apply memLp_top_of_bound hm.aestronglyMeasurable Λ
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using c2m_entry_bound (hA ω x) j k)

/-- All fixed entries of the shifted physical diffusion-drift form are
measurable, for arbitrary complex force and jointly measurable coefficients. -/
private theorem c2m_measurable_shifted_form
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (Gu Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Measurable (fun ω =>
      (s : ℂ) * (∫ x, u x * v x) + (1 / 2 : ℂ) *
        (∑ j, ∑ k, ∫ x, (a ω x j k : ℂ) * Gu k x * Gv j x) -
      ζ * (∑ j, ∫ x, (a ω x j i : ℂ) * Gu j x * v x)) := by
  have hdiff : Measurable (fun ω =>
      ∑ j, ∑ k, ∫ x, (a ω x j k : ℂ) * Gu k x * Gv j x) :=
    Finset.measurable_fun_sum Finset.univ (fun j _ =>
      Finset.measurable_fun_sum Finset.univ (fun k _ =>
        c2m_measurable_coefficient_pairing a ha j k (Gu k) (Gv j)))
  have hdrift : Measurable (fun ω =>
      ∑ j, ∫ x, (a ω x j i : ℂ) * Gu j x * v x) :=
    Finset.measurable_fun_sum Finset.univ (fun j _ =>
      c2m_measurable_coefficient_pairing a ha j i (Gu j) v)
  exact (measurable_const.add (measurable_const.mul hdiff)).sub
    (measurable_const.mul hdrift)

/-- Weak scalar measurability implies Borel measurability in a separable
real Hilbert space. The countable encoding avoids any operator-norm topology. -/
private theorem c2m_measurable_of_inner
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (f : Ω → E) (hf : ∀ v : E, Measurable (fun ω => inner ℝ v (f ω))) :
    Measurable f := by
  let q : ℕ → E := TopologicalSpace.denseSeq E
  have hq : DenseRange q := TopologicalSpace.denseRange_denseSeq E
  let enc : E → ℕ → ℝ := fun x n => inner ℝ (q n) x
  have hc : Continuous enc := continuous_pi (fun n => continuous_const.inner continuous_id)
  have hi : Function.Injective enc := by
    intro x y hxy
    apply ext_inner_left ℝ
    have he : (fun v : E => inner ℝ v x) = (fun v : E => inner ℝ v y) :=
      hq.equalizer (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const) (funext (fun n => congrFun hxy n))
    exact congrFun he
  apply (hc.measurableEmbedding hi).measurable_comp_iff.mp
  exact measurable_pi_lambda (fun n => hf (q n))

private def c2m_physicalCoefficientMul {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (j k : Fin d) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL volume ∞ 2 2 ((ha j k).toLp _)

private theorem c2m_physicalCoefficientMul_coe {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (j k : Fin d)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalCoefficientMul a ha j k f =ᵐ[volume] fun x => (a x j k : ℂ) * f x := by
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ((ha j k).toLp _) f
  filter_upwards [(ha j k).coeFn_toLp, hm] with x hx hmx
  simpa only [c2m_physicalCoefficientMul, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', hx] using hmx


private theorem c2m_physicalCoefficientMul_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (j k : Fin d)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖c2m_physicalCoefficientMul a ha j k u‖ ≤ Λ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hA, c2m_physicalCoefficientMul_coe a ha j k u] with x hx hu
  rw [hu, norm_mul]
  exact mul_le_mul_of_nonneg_right
    (by simpa only [Complex.norm_real, Real.norm_eq_abs] using c2m_entry_bound hx j k)
    (norm_nonneg _)

/-- Physical coefficient multiplication acts measurably on each L2 datum. -/
private theorem c2m_measurable_coefficient_action
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    (j k : Fin d) (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalCoefficientMul (a ω) (hb ω) j k u) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  apply c2m_measurable_of_inner
  intro v
  have hcoord : Measurable (fun A : Mat d => A j k) :=
    (show Continuous (fun A : Mat d => A j k) from
      (continuous_apply k).comp (continuous_apply j)).measurable
  have hc : Measurable (fun p : Ω × Vec d => (a p.1 p.2 j k : ℂ)) :=
    Complex.measurable_ofReal.comp (hcoord.comp ha)
  have hu : Measurable (fun p : Ω × Vec d => u p.2) :=
    (Lp.stronglyMeasurable u).measurable.comp measurable_snd
  have hv : Measurable (fun p : Ω × Vec d => v p.2) :=
    (Lp.stronglyMeasurable v).measurable.comp measurable_snd
  have hj : Measurable (fun p : Ω × Vec d =>
      inner ℝ (v p.2) ((a p.1 p.2 j k : ℂ) * u p.2)) := hv.inner (hc.mul hu)
  have he : (fun ω => inner ℝ v (c2m_physicalCoefficientMul (a ω) (hb ω) j k u)) =
      (fun ω => ∫ x, inner ℝ (v x) ((a ω x j k : ℂ) * u x)) := by
    funext ω
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [c2m_physicalCoefficientMul_coe (a ω) (hb ω) j k u] with x hx
    rw [hx]
  rw [he]
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- Continuous, separately measurable contraction families have measurable fixed
points. This applies to convergent iterations for the physical resolvent. -/
private theorem c2m_measurable_fixedPoint
    {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] [CompleteSpace E]
    [Nonempty E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    (T : Ω → E → E) (K : ℝ≥0)
    (hT : ∀ ω, ContractingWith K (T ω))
    (hm : ∀ x, Measurable (fun ω => T ω x)) :
    Measurable (fun ω => ContractingWith.fixedPoint (T ω) (hT ω)) := by
  classical
  let x₀ : E := Classical.choice inferInstance
  have hj : Measurable (fun p : E × Ω => T p.2 p.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (hT ω).2.continuous) hm
  have hi : ∀ n : ℕ, Measurable (fun ω => (T ω)^[n] x₀) := by
    intro n
    induction n with
    | zero => exact measurable_const
    | succ n ihn =>
      convert hj.comp (ihn.prodMk measurable_id) using 1
      funext ω
      exact Function.iterate_succ_apply' (T ω) n x₀
  apply measurable_of_tendsto_metrizable hi
  exact tendsto_pi_nhds.mpr (fun ω => (hT ω).tendsto_iterate_fixedPoint x₀)

/-- A single Richardson step contracts uniformly for a bounded, uniformly
coercive family; the operators need not be symmetric. -/
private theorem c2m_uniform_richardson_step
    {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : Ω → E →L[ℝ] E) (m M : ℝ) (hm : 0 < m) (hM : 0 ≤ M)
    (hbound : ∀ ω x, ‖A ω x‖ ≤ M * ‖x‖)
    (hcoer : ∀ ω x, m * ‖x‖ ^ 2 ≤ inner ℝ x (A ω x)) :
    ∃ η : ℝ, 0 < η ∧ ∃ K : ℝ≥0, K < 1 ∧
      ∀ ω x, ‖x - η • A ω x‖ ≤ (K : ℝ) * ‖x‖ := by
  let D := 1 + m ^ 2 + M ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  let η := m / D
  have hη : 0 < η := div_pos hm hD
  have hηm : η * m < 1 := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_lt_one hD]
    dsimp [D]
    nlinarith [sq_nonneg M]
  have hηM : η * M ^ 2 ≤ m := by
    dsimp [η]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    dsimp [D]
    nlinarith [mul_nonneg hm.le (sq_nonneg m)]
  let q := Real.sqrt (1 - η * m)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = 1 - η * m := Real.sq_sqrt (sub_nonneg.mpr hηm.le)
  have hq1 : q < 1 := by nlinarith [mul_pos hη hm]
  refine ⟨η, hη, ⟨q, hq⟩, hq1, ?_⟩
  intro ω x
  have hAx2 : ‖A ω x‖ ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg (A ω x)) (mul_nonneg hM (norm_nonneg x))).mpr
        (hbound ω x)
  have he : ‖x - η • A ω x‖ ^ 2 =
      ‖x‖ ^ 2 - 2 * η * inner ℝ x (A ω x) + η ^ 2 * ‖A ω x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hη]
    ring
  have hc := hcoer ω x
  have hc' := mul_le_mul_of_nonneg_left hc hη.le
  have hb := mul_le_mul_of_nonneg_left hAx2 (sq_nonneg η)
  have hd := mul_le_mul_of_nonneg_left hηM (mul_nonneg hη.le (sq_nonneg ‖x‖))
  have hn : ‖x - η • A ω x‖ ^ 2 ≤ (q * ‖x‖) ^ 2 := by
    rw [he, mul_pow, hq2]
    nlinarith
  change ‖x - η • A ω x‖ ≤ q * ‖x‖
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hq (norm_nonneg _))).mp hn

/-- Parameter measurability of solutions obtained by contraction of a
linear equation. Only measurability of the action on fixed vectors is needed. -/
private theorem c2m_measurable_linear_solution
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (A : Ω → E →L[ℝ] E) (rhs : Ω → E) (K : ℝ≥0)
    (hA : ∀ x, Measurable (fun ω => A ω x)) (hrhs : Measurable rhs)
    (hc : ∀ ω, ContractingWith K (fun x => x + (rhs ω - A ω x))) :
    ∃ u : Ω → E, Measurable u ∧ ∀ ω, A ω (u ω) = rhs ω := by
  let T : Ω → E → E := fun ω x => x + (rhs ω - A ω x)
  let u : Ω → E := fun ω => ContractingWith.fixedPoint (T ω) (hc ω)
  refine ⟨u, c2m_measurable_fixedPoint T K hc
    (fun x => measurable_const.add (hrhs.sub (hA x))), ?_⟩
  intro ω
  have hf : u ω + (rhs ω - A ω (u ω)) = u ω + 0 := by
    simpa only [add_zero] using (hc ω).fixedPoint_isFixedPt.eq
  have hz : rhs ω - A ω (u ω) = 0 := add_left_cancel hf
  exact (sub_eq_zero.mp hz).symm

/-- Uniform boundedness and coercivity turn weak measurability of operator
actions into measurable solutions, with no operator-norm measurability premise. -/
private theorem c2m_measurable_coercive_solution
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (A : Ω → E →L[ℝ] E) (rhs : Ω → E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hA : ∀ x y, Measurable (fun ω => inner ℝ y (A ω x)))
    (hrhs : Measurable rhs)
    (hbound : ∀ ω x, ‖A ω x‖ ≤ M * ‖x‖)
    (hcoer : ∀ ω x, m * ‖x‖ ^ 2 ≤ inner ℝ x (A ω x)) :
    ∃ u : Ω → E, Measurable u ∧ ∀ ω, A ω (u ω) = rhs ω := by
  obtain ⟨η, hη, K, hK, hstep⟩ :=
    c2m_uniform_richardson_step A m M hm hM hbound hcoer
  have hAm : ∀ x, Measurable (fun ω => A ω x) :=
    fun x => c2m_measurable_of_inner _ (hA x)
  let T : Ω → E → E := fun ω x => x + η • (rhs ω - A ω x)
  have hTc : ∀ ω, ContractingWith K (T ω) := by
    intro ω
    refine ⟨hK, LipschitzWith.of_dist_le_mul (fun x y => ?_)⟩
    have he : T ω x - T ω y = (x - y) - η • A ω (x - y) := by
      dsimp [T]
      rw [map_sub, smul_sub, smul_sub, smul_sub]
      abel
    rw [dist_eq_norm, dist_eq_norm, he]
    exact hstep ω (x - y)
  let u : Ω → E := fun ω => ContractingWith.fixedPoint (T ω) (hTc ω)
  refine ⟨u, c2m_measurable_fixedPoint T K hTc
    (fun x => measurable_const.add (measurable_const.smul (hrhs.sub (hAm x)))), ?_⟩
  intro ω
  have hf : u ω + η • (rhs ω - A ω (u ω)) = u ω + 0 := by
    simpa only [add_zero] using (hTc ω).fixedPoint_isFixedPt.eq
  have hz : η • (rhs ω - A ω (u ω)) = 0 := add_left_cancel hf
  exact (sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (ne_of_gt hη))).symm

/-- Parameter-dependent Lax--Milgram solutions are measurable whenever fixed
form entries are measurable and boundedness/coercivity constants are uniform. -/
private theorem c2m_measurable_variational_solution
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    (B : Ω → E →L[ℝ] E →L[ℝ] ℝ) (rhs : Ω → E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hB : ∀ x y, Measurable (fun ω => B ω x y)) (hrhs : Measurable rhs)
    (hbound : ∀ ω, ‖B ω‖ ≤ M)
    (hcoer : ∀ ω x, m * ‖x‖ ^ 2 ≤ B ω x x) :
    ∃ u : Ω → E, Measurable u ∧ ∀ ω v, B ω (u ω) v = inner ℝ (rhs ω) v := by
  let A : Ω → E →L[ℝ] E := fun ω => InnerProductSpace.continuousLinearMapOfBilin (B ω)
  have hpair : ∀ ω x y, inner ℝ (A ω x) y = B ω x y :=
    fun ω x y => InnerProductSpace.continuousLinearMapOfBilin_apply (B ω) x y
  have hAm : ∀ x y, Measurable (fun ω => inner ℝ y (A ω x)) := by
    intro x y
    have he : (fun ω => inner ℝ y (A ω x)) = (fun ω => B ω x y) := by
      funext ω
      rw [real_inner_comm, hpair]
    rw [he]
    exact hB x y
  have hAb : ∀ ω x, ‖A ω x‖ ≤ M * ‖x‖ := by
    intro ω x
    have he : ‖A ω x‖ = ‖B ω x‖ :=
      (InnerProductSpace.toDual ℝ E).symm.norm_map (B ω x)
    rw [he]
    exact ((B ω).le_opNorm x).trans
      (mul_le_mul_of_nonneg_right (hbound ω) (norm_nonneg x))
  have hAc : ∀ ω x, m * ‖x‖ ^ 2 ≤ inner ℝ x (A ω x) := by
    intro ω x
    rw [real_inner_comm, hpair]
    exact hcoer ω x
  obtain ⟨u, hu, hsol⟩ :=
    c2m_measurable_coercive_solution A rhs m M hm hM hAm hrhs hAb hAc
  refine ⟨u, hu, fun ω v => ?_⟩
  rw [← hpair, hsol]

private theorem c2m_weakPartial_smul {d : ℕ} {U : Set (Vec d)} {j : Fin d}
    {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g) (c : ℝ) :
    HasWeakPartialDerivative U j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨fun x hx => (h.1 x hx).smul c,
    fun x hx => (h.2.1 x hx).smul c, ?_⟩
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [h.2.2 φ hφ]
  ring

/-- The physical complex H1 graph is a real linear space of value/gradient tuples.
The L2 representatives are replaced explicitly before invoking weak linearity. -/
private def c2m_physicalGraph (d : ℕ) :
    Submodule ℝ (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d)))) where
  carrier := {u | IsPhysicalH1Graph volume (Or.inl rfl) (u none) (fun j => u (some j))}
  zero_mem' := by
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun _ => 0) (fun _ _ => 0) (Lp.coeFn_zero _ _ _) (fun _ => Lp.coeFn_zero _ _ _)).mpr
    constructor <;> intro j <;>
      exact ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by intros; simp⟩
  add_mem' := by
    intro u v hu hv
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun x => u none x + v none x)
      (fun j x => u (some j) x + v (some j) x)
      (Lp.coeFn_add _ _) (fun _ => Lp.coeFn_add _ _)).mpr
    constructor
    · intro j
      simpa only [Complex.add_re] using Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j)
    · intro j
      simpa only [Complex.add_im] using Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)
  smul_mem' := by
    intro c u hu
    apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
      (fun x => c • u none x) (fun j x => c • u (some j) x)
      (Lp.coeFn_smul _ _) (fun _ => Lp.coeFn_smul _ _)).mpr
    constructor
    · intro j
      simpa only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using c2m_weakPartial_smul (hu.1 j) c
    · intro j
      simpa only [Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using c2m_weakPartial_smul (hu.2 j) c

/-- Closedness supplies completeness for the physical variational problem. -/
private theorem c2m_physicalGraph_closed (d : ℕ) :
    IsClosed (c2m_physicalGraph d : Set
      (PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))))) := by
  let T : PiLp 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))) →
      Lp ℂ 2 (volume : Measure (Vec d)) × (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :=
    fun u => (u none, fun j => u (some j))
  have hT : Continuous T := (PiLp.continuous_apply 2 _ none).prodMk
    (continuous_pi fun j => PiLp.continuous_apply 2 _ (some j))
  exact (isClosed_physicalH1Graph volume (Or.inl rfl)).preimage hT

private theorem c2m_physicalGraph_norm_sq {d : ℕ} (u : c2m_physicalGraph d) :
    ‖u‖ ^ 2 = ‖u.val none‖ ^ 2 + ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, univ_option,
    Finset.sum_insertNone]

private def c2m_physicalGraphEval {d : ℕ} (o : Option (Fin d)) :
    c2m_physicalGraph d →L[ℝ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin d) => Lp ℂ 2 (volume : Measure (Vec d))) o).comp
    (c2m_physicalGraph d).subtypeL

private instance c2m_physicalGraph_complete (d : ℕ) :
    CompleteSpace (c2m_physicalGraph d) :=
  (c2m_physicalGraph_closed d).completeSpace_coe

private theorem c2m_physical_energy_lowerBound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Λ⁻¹ * ∑ j, ‖G j‖ ^ 2 ≤
      ∑ j, ∑ k, inner ℝ (G j) (c2m_physicalCoefficientMul a ha j k (G k)) := by
  have hint (j k : Fin d) : Integrable
      (fun x => star (G j x) * (a x j k : ℂ) * G k x) volume := by
    have hp := ((Lp.memLp (G j)).star.integrable_mul (Lp.memLp (G k))).mul_of_top_right
      (ha j k)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply, Pi.star_apply]
    ring
  have hsum : (∫ x, ∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * G k x) =
      ∑ j, ∑ k, inner ℂ (G j) (c2m_physicalCoefficientMul a ha j k (G k)) := by
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum _ (fun k _ => hint j k)]
    apply Finset.sum_congr rfl
    intro k _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [c2m_physicalCoefficientMul_coe a ha j k (G k)] with x hx
    simp only [hx, RCLike.inner_apply, Complex.star_def]
    ring
  have hreal (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ u v = (inner ℂ u v).re := by
    rw [L2.inner_def, L2.inner_def]
    exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)
  have hn (u : Lp ℂ 2 (volume : Measure (Vec d))) :
      ‖u‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hN := integrable_finset_sum Finset.univ (fun j _ => (Lp.memLp (G j)).norm.integrable_sq)
  have hB := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => hint j k))
  have hle : ∀ᵐ x ∂volume, Λ⁻¹ * ∑ j, ‖G j x‖ ^ 2 ≤
      (∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * G k x).re := by
    filter_upwards [hA] with x hx
    convert s5_coercive hx (fun j => G j x) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [starRingEnd_apply]
    ring
  have hi := integral_mono_ae (hN.const_mul Λ⁻¹) hB.re hle
  rw [integral_const_mul, integral_finset_sum _ (fun j _ =>
    (Lp.memLp (G j)).norm.integrable_sq), integral_re hB, hsum] at hi
  change Λ⁻¹ * (∑ j, ∫ x, ‖G j x‖ ^ 2) ≤
    (∑ j, ∑ k, inner ℂ (G j) (c2m_physicalCoefficientMul a ha j k (G k))).re at hi
  simpa only [hn, Complex.re_sum, hreal] using hi

/-- The shifted physical form on the actual completed value-gradient graph,
including the complex first-order drift. -/
private def c2m_physicalShiftedForm {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) :
    c2m_physicalGraph d →L[ℝ] c2m_physicalGraph d →L[ℝ] ℝ :=
  let E := c2m_physicalGraphEval (d := d)
  let I : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] ℝ := innerSL ℝ
  let C := fun j k => (c2m_physicalCoefficientMul a ha j k).restrictScalars ℝ
  s • I.bilinearComp (E none) (E none) + (1 / 2 : ℝ) •
    ∑ j : Fin d, ∑ k : Fin d,
      (I.bilinearComp (E (some j)) ((C j k).comp (E (some k)))).flip -
    (I.bilinearComp (E none) (ζ • ∑ j : Fin d, (C j i).comp (E (some j)))).flip

private theorem c2m_physicalShiftedForm_apply {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c2m_physicalGraph d) :
    c2m_physicalShiftedForm a ha i ζ s u v =
      s * inner ℝ (u.val none) (v.val none) +
      (1 / 2 : ℝ) * ∑ j, ∑ k,
        inner ℝ (v.val (some j)) (c2m_physicalCoefficientMul a ha j k (u.val (some k))) -
      inner ℝ (v.val none) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j))) := by
  simp only [c2m_physicalShiftedForm, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', c2m_physicalGraphEval,
    PiLp.proj_apply, Submodule.subtypeL_apply, smul_eq_mul]
  rfl

/-- Fixed entries of the actual graph form are measurable in the coefficient
parameter. This uses action measurability, not norm measurability of the form. -/
private theorem c2m_measurable_physicalShiftedForm
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c2m_physicalGraph d) :
    Measurable (fun ω => c2m_physicalShiftedForm (a ω) (hb ω) i ζ s u v) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  simp_rw [c2m_physicalShiftedForm_apply]
  have hm (j k : Fin d) :=
    c2m_measurable_coefficient_action a ha hb j k (u.val (some k))
  have hdiff : Measurable (fun ω => ∑ j, ∑ k,
      inner ℝ (v.val (some j))
        (c2m_physicalCoefficientMul (a ω) (hb ω) j k (u.val (some k)))) :=
    Finset.measurable_fun_sum Finset.univ (fun j _ =>
      Finset.measurable_fun_sum Finset.univ (fun k _ => measurable_const.inner (hm j k)))
  have hdrift : Measurable (fun ω => ∑ j,
      c2m_physicalCoefficientMul (a ω) (hb ω) j i (u.val (some j))) :=
    Finset.measurable_fun_sum Finset.univ (fun j _ =>
      c2m_measurable_coefficient_action a ha hb j i (u.val (some j)))
  have hd : Measurable (fun ω => ζ • ∑ j,
      c2m_physicalCoefficientMul (a ω) (hb ω) j i (u.val (some j))) :=
    hdrift.const_smul ζ
  exact (measurable_const.add (measurable_const.mul hdiff)).sub
    (measurable_const.inner hd)

private instance c2m_physicalGraph_normedGroup (d : ℕ) :
    NormedAddCommGroup (c2m_physicalGraph d) := inferInstance

private instance c2m_physicalGraph_normedSpace (d : ℕ) :
    NormedSpace ℝ (c2m_physicalGraph d) := inferInstance

private theorem c2m_physicalShiftedForm_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) :
    ‖c2m_physicalShiftedForm a ha i ζ s‖ ≤
      |s| + (1 / 2 : ℝ) * (d : ℝ) ^ 2 * Λ + ‖ζ‖ * (d : ℝ) * Λ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  have he (w : c2m_physicalGraph d) (o : Option (Fin d)) : ‖w.val o‖ ≤ ‖w‖ :=
    PiLp.norm_apply_le (p := 2) w.val o
  have hc (j k l : Fin d) :
      ‖c2m_physicalCoefficientMul a ha j k (u.val (some l))‖ ≤ Λ * ‖u‖ :=
    (c2m_physicalCoefficientMul_bound a ha hA j k _).trans
      (mul_le_mul_of_nonneg_left (he u _) hΛ)
  have hp (j k : Fin d) :
      |inner ℝ (v.val (some j))
        (c2m_physicalCoefficientMul a ha j k (u.val (some k)))| ≤ Λ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖v.val (some j)‖ *
          ‖c2m_physicalCoefficientMul a ha j k (u.val (some k))‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (Λ * ‖u‖) := mul_le_mul (he v _) (hc j k k) (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  have hs : |∑ j, ∑ k, inner ℝ (v.val (some j))
      (c2m_physicalCoefficientMul a ha j k (u.val (some k)))| ≤
      (d : ℝ) ^ 2 * Λ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ∑ j : Fin d, |∑ k, inner ℝ (v.val (some j))
          (c2m_physicalCoefficientMul a ha j k (u.val (some k)))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin d, ∑ _k : Fin d, Λ * ‖u‖ * ‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hp j k)
      _ = _ := by simp; ring
  have hd : ‖ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j))‖ ≤
      ‖ζ‖ * (d : ℝ) * Λ * ‖u‖ := by
    rw [norm_smul]
    calc
      _ ≤ ‖ζ‖ * ∑ j : Fin d,
          ‖c2m_physicalCoefficientMul a ha j i (u.val (some j))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)
      _ ≤ ‖ζ‖ * ∑ _j : Fin d, Λ * ‖u‖ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hc j i j) (norm_nonneg _)
      _ = _ := by simp; ring
  have hzero : |inner ℝ (u.val none) (v.val none)| ≤ ‖u‖ * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (he u _) (he v _) (norm_nonneg _) (norm_nonneg _))
  have hdrift : |inner ℝ (v.val none)
      (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j)))| ≤
      ‖ζ‖ * (d : ℝ) * Λ * ‖u‖ * ‖v‖ := by
    calc
      _ ≤ ‖v.val none‖ * ‖ζ • ∑ j,
          c2m_physicalCoefficientMul a ha j i (u.val (some j))‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖ζ‖ * (d : ℝ) * Λ * ‖u‖) :=
        mul_le_mul (he v _) hd (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  rw [c2m_physicalShiftedForm_apply, Real.norm_eq_abs]
  calc
    _ ≤ |s * inner ℝ (u.val none) (v.val none)| +
        |(1 / 2 : ℝ) * ∑ j, ∑ k, inner ℝ (v.val (some j))
          (c2m_physicalCoefficientMul a ha j k (u.val (some k)))| +
        |inner ℝ (v.val none) (ζ • ∑ j,
          c2m_physicalCoefficientMul a ha j i (u.val (some j)))| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |s| * (‖u‖ * ‖v‖) +
        (1 / 2 : ℝ) * ((d : ℝ) ^ 2 * Λ * ‖u‖ * ‖v‖) +
        ‖ζ‖ * (d : ℝ) * Λ * ‖u‖ * ‖v‖ := by
      simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
      exact add_le_add (add_le_add
        (mul_le_mul_of_nonneg_left hzero (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hs (by norm_num))) hdrift
    _ = _ := by ring

private theorem c2m_physical_drift_absorption {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (u : c2m_physicalGraph d) :
    |inner ℝ (u.val none) (ζ • ∑ j,
      c2m_physicalCoefficientMul a ha j i (u.val (some j)))| ≤
      (Λ⁻¹ / 4) * ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 +
        (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * ‖u.val none‖ ^ 2 := by
  have hy (x y : ℝ) : x * y ≤ (Λ⁻¹ / 4) * x ^ 2 + Λ * y ^ 2 := by
    have hid : (Λ⁻¹ / 4) * x ^ 2 + Λ * y ^ 2 - x * y =
        (4 * Λ)⁻¹ * (x - 2 * Λ * y) ^ 2 := by
      field_simp [ne_of_gt hΛ]
      <;> ring
    exact sub_nonneg.mp (hid ▸ mul_nonneg (by positivity) (sq_nonneg _))
  have hc (j : Fin d) :=
    c2m_physicalCoefficientMul_bound a ha hA j i (u.val (some j))
  have hd : ‖ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j))‖ ≤
      ‖ζ‖ * ∑ j : Fin d, Λ * ‖u.val (some j)‖ := by
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hc j)) (norm_nonneg _)
  calc
    _ ≤ ‖u.val none‖ * ‖ζ • ∑ j,
        c2m_physicalCoefficientMul a ha j i (u.val (some j))‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖u.val none‖ * (‖ζ‖ * ∑ j : Fin d, Λ * ‖u.val (some j)‖) :=
      mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ∑ j : Fin d, ‖u.val (some j)‖ * (‖ζ‖ * Λ * ‖u.val none‖) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ ∑ j : Fin d, ((Λ⁻¹ / 4) * ‖u.val (some j)‖ ^ 2 +
        Λ * (‖ζ‖ * Λ * ‖u.val none‖) ^ 2) :=
      Finset.sum_le_sum fun j _ => hy _ _
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.mul_sum]; ring

private theorem c2m_physicalShiftedForm_coercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u : c2m_physicalGraph d) :
    min (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4) * ‖u‖ ^ 2 ≤
      c2m_physicalShiftedForm a ha i ζ s u u := by
  have henergy := c2m_physical_energy_lowerBound a ha hA (fun j => u.val (some j))
  have hdrift := c2m_physical_drift_absorption a ha hΛ hA i ζ u
  have hn : 0 ≤ ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hm := add_le_add
    (mul_le_mul_of_nonneg_right
      (min_le_left (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4))
      (sq_nonneg ‖u.val none‖))
    (mul_le_mul_of_nonneg_right
      (min_le_right (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4)) hn)
  rw [← mul_add, ← c2m_physicalGraph_norm_sq] at hm
  rw [c2m_physicalShiftedForm_apply, real_inner_self_eq_norm_sq]
  have hd := (le_abs_self _).trans hdrift
  nlinarith only [hm, henergy, hd]

private theorem c2m_physicalShiftedForm_isCoercive {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    IsCoercive (c2m_physicalShiftedForm a ha i ζ s) := by
  refine ⟨min (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4),
    lt_min (sub_pos.mpr hs) (by positivity), fun u => ?_⟩
  have h := c2m_physicalShiftedForm_coercive a ha hΛ hA i ζ s u
  nlinarith only [h]

private def c2m_physicalGraphResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] c2m_physicalGraph d :=
  (c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp (c2m_physicalGraphEval (d := d) none).adjoint

/-- The physical shifted variational inverse depends measurably on the
jointly measurable elliptic coefficients. No topology on coefficient L∞ is used. -/
private theorem c2m_measurable_physical_variational_solution
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (c2m_physicalGraph d) := borel (c2m_physicalGraph d)
    ∃ u : Ω → c2m_physicalGraph d, Measurable u ∧
      ∀ ω v, c2m_physicalShiftedForm (a ω) (hb ω) i ζ s (u ω) v =
        inner ℝ rhs (v.val none) := by
  letI : MeasurableSpace (c2m_physicalGraph d) := borel (c2m_physicalGraph d)
  letI : BorelSpace (c2m_physicalGraph d) := ⟨rfl⟩
  let E := c2m_physicalGraphEval (d := d) none
  let m := min (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) (Λ⁻¹ / 4)
  let M := |s| + (1 / 2 : ℝ) * (d : ℝ) ^ 2 * Λ + ‖ζ‖ * (d : ℝ) * Λ
  have hm : 0 < m := lt_min (sub_pos.mpr hs) (by positivity)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  obtain ⟨u, hmu, hu⟩ := c2m_measurable_variational_solution
    (fun ω => c2m_physicalShiftedForm (a ω) (hb ω) i ζ s)
    (fun _ : Ω => E.adjoint rhs) m M hm hM
    (fun u v => c2m_measurable_physicalShiftedForm a ha hb i ζ s u v)
    measurable_const
    (fun ω => c2m_physicalShiftedForm_bound (a ω) (hb ω) hΛ.le
      (Filter.Eventually.of_forall (hA ω)) i ζ s)
    (fun ω u => c2m_physicalShiftedForm_coercive (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ s u)
  refine ⟨u, hmu, fun ω v => ?_⟩
  exact (hu ω v).trans (E.adjoint_inner_left v rhs)

private theorem c2m_measurable_physicalGraphResolvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (c2m_physicalGraph d) := borel (c2m_physicalGraph d)
    Measurable (fun ω => c2m_physicalGraphResolvent (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ s hs rhs) := by
  letI : MeasurableSpace (c2m_physicalGraph d) := borel (c2m_physicalGraph d)
  obtain ⟨u, hmu, hu⟩ :=
    c2m_measurable_physical_variational_solution a ha hb hΛ hA i ζ s hs rhs
  have he : (fun ω => c2m_physicalGraphResolvent (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ s hs rhs) = u := by
    funext ω
    let hc := c2m_physicalShiftedForm_isCoercive (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ s hs
    let E := c2m_physicalGraphEval (d := d) none
    apply hc.continuousLinearEquivOfBilin.injective
    change hc.continuousLinearEquivOfBilin
      (hc.continuousLinearEquivOfBilin.symm (E.adjoint rhs)) =
        hc.continuousLinearEquivOfBilin (u ω)
    rw [hc.continuousLinearEquivOfBilin.apply_symm_apply]
    apply hc.unique_continuousLinearEquivOfBilin
    intro v
    exact (E.adjoint_inner_left v rhs).trans (hu ω v).symm
  rw [he]
  exact hmu

private theorem c2m_physicalGraphResolvent_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c2m_physicalGraph d) :
    c2m_physicalShiftedForm a ha i ζ s
      (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v =
      inner ℝ rhs (v.val none) := by
  let hB := c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
  have hb := hB.continuousLinearEquivOfBilin_apply
    (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v
  change inner ℝ (hB.continuousLinearEquivOfBilin
    (hB.continuousLinearEquivOfBilin.symm ((c2m_physicalGraphEval none).adjoint rhs))) v = _ at hb
  rw [hB.continuousLinearEquivOfBilin.apply_symm_apply] at hb
  exact hb.symm.trans ((c2m_physicalGraphEval none).adjoint_inner_left v rhs)

private def c2m_physicalGraphComplexSmul {d : ℕ} (c : ℂ)
    (u : c2m_physicalGraph d) : c2m_physicalGraph d := by
  refine ⟨c • u.val, ?_⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => c * u.val none x) (fun j x => c * u.val (some j) x)
    (Lp.coeFn_smul _ _) (fun _ => Lp.coeFn_smul _ _)).mpr
  constructor
  · intro j
    have h := Correctors.hasWeakPartialDerivative_add
      (c2m_weakPartial_smul (u.property.1 j) c.re)
      (c2m_weakPartial_smul (u.property.2 j) (-c.im))
    simpa only [Complex.mul_re, neg_mul, sub_eq_add_neg] using h
  · intro j
    have h := Correctors.hasWeakPartialDerivative_add
      (c2m_weakPartial_smul (u.property.2 j) c.re)
      (c2m_weakPartial_smul (u.property.1 j) c.im)
    simpa only [Complex.mul_im] using h

private def c2m_physicalGraphStar {d : ℕ} (u : c2m_physicalGraph d) :
    c2m_physicalGraph d := by
  refine ⟨WithLp.toLp 2 (fun o => star (u.val o)), ?_⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => star (u.val none x)) (fun j x => star (u.val (some j) x))
    (Lp.coeFn_star _) (fun _ => Lp.coeFn_star _)).mpr
  constructor
  · simpa only [Complex.star_def, Complex.conj_re] using u.property.1
  · intro j
    simpa only [Complex.star_def, Complex.conj_im, neg_one_mul] using
      c2m_weakPartial_smul (u.property.2 j) (-1)

private def c2m_physicalResolventExpression {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c2m_physicalGraph d) : ℂ :=
  (s : ℂ) * inner ℂ (v.val none) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    ∑ j, ∑ k, inner ℂ (v.val (some j)) (c2m_physicalCoefficientMul a ha j k (u.val (some k))) -
    inner ℂ (v.val none) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j)))

private theorem c2m_physical_realInner {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) : inner ℝ u v = (inner ℂ u v).re := by
  rw [L2.inner_def, L2.inner_def]
  exact integral_re (L2.integrable_inner (𝕜 := ℂ) u v)

private theorem c2m_physicalShiftedForm_eq_re {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c2m_physicalGraph d) :
    c2m_physicalShiftedForm a ha i ζ s u v = (c2m_physicalResolventExpression a ha i ζ s u v).re := by
  rw [c2m_physicalShiftedForm_apply]
  simp only [c2m_physical_realInner, c2m_physicalResolventExpression,
    Complex.add_re, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_sum]
  rw [show (inner ℂ (u.val none) (v.val none)).re =
    (inner ℂ (v.val none) (u.val none)).re from inner_re_symm (𝕜 := ℂ) _ _]

private theorem c2m_physicalResolventExpression_I {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (u v : c2m_physicalGraph d) :
    c2m_physicalResolventExpression a ha i ζ s u (c2m_physicalGraphComplexSmul Complex.I v) =
      -Complex.I * c2m_physicalResolventExpression a ha i ζ s u v := by
  simp only [c2m_physicalResolventExpression, c2m_physicalGraphComplexSmul,
    PiLp.smul_apply, inner_smul_left, Complex.conj_I, ← Finset.mul_sum]
  ring

/-- Imaginary tests promote the real Lax–Milgram solution to the full complex
weak resolvent identity, without a reality assumption on the initial datum. -/
private theorem c2m_physicalGraphResolvent_complex_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) (rhs : Lp ℂ 2 (volume : Measure (Vec d)))
    (v : c2m_physicalGraph d) :
    c2m_physicalResolventExpression a ha i ζ s (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) v =
      inner ℂ (v.val none) rhs := by
  apply Complex.ext
  · have h := c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v
    rw [c2m_physicalShiftedForm_eq_re, c2m_physical_realInner] at h
    exact h.trans (inner_re_symm (𝕜 := ℂ) _ _)
  · have h := c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs
      (c2m_physicalGraphComplexSmul Complex.I v)
    rw [c2m_physicalShiftedForm_eq_re, c2m_physicalResolventExpression_I,
      c2m_physical_realInner] at h
    change (-Complex.I * c2m_physicalResolventExpression a ha i ζ s _ v).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simp only [neg_mul, Complex.neg_re, Complex.I_mul_re, neg_neg] at h
    have him : (inner ℂ rhs (v.val none)).im = -(inner ℂ (v.val none) rhs).im :=
      inner_im_symm (𝕜 := ℂ) _ _
    linarith only [h, him]

private theorem c2m_physicalGraphResolvent_unique {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (u : c2m_physicalGraph d)
    (hu : ∀ v, c2m_physicalResolventExpression a ha i ζ s u v =
      inner ℂ (v.val none) rhs) :
    u = c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs := by
  let hB := c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply]
  rw [c2m_physicalShiftedForm_eq_re, hu]
  exact (c2m_physical_realInner _ _).symm.trans
    ((real_inner_comm _ _).trans (c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v).symm)

private theorem c2m_physicalResolventExpression_smul {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (c : ℂ) (u v : c2m_physicalGraph d) :
    c2m_physicalResolventExpression a ha i ζ s (c2m_physicalGraphComplexSmul c u) v =
      c * c2m_physicalResolventExpression a ha i ζ s u v := by
  simp only [c2m_physicalResolventExpression, c2m_physicalGraphComplexSmul,
    PiLp.smul_apply, map_smul, inner_smul_right, ← Finset.smul_sum,
    smul_comm ζ c, ← Finset.mul_sum]
  ring

private theorem c2m_physicalGraphResolvent_smul {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (c : ℂ) :
    c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs (c • rhs) =
      c2m_physicalGraphComplexSmul c
        (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs) := by
  symm
  apply c2m_physicalGraphResolvent_unique a ha hΛ hA i ζ s hs
  intro v
  rw [c2m_physicalResolventExpression_smul,
    c2m_physicalGraphResolvent_complex_spec, inner_smul_right]

/-- The actual L2 resolvent is complex linear; continuity is inherited from
its real variational construction. -/
private def c2m_physicalResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) where
  toFun f := (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs f).val none
  map_add' f g := by
    change c2m_physicalGraphEval none
      (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs (f + g)) = _
    rw [map_add, map_add]
    rfl
  map_smul' c f := by
    rw [c2m_physicalGraphResolvent_smul]
    rfl
  cont := (c2m_physicalGraphEval none).continuous.comp
    (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs).continuous

private theorem c2m_measurable_physicalResolvent
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalResolvent (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ s hs rhs) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  letI : MeasurableSpace (c2m_physicalGraph d) := borel (c2m_physicalGraph d)
  letI : BorelSpace (c2m_physicalGraph d) := ⟨rfl⟩
  exact (c2m_physicalGraphEval none).continuous.measurable.comp
    (c2m_measurable_physicalGraphResolvent a ha hb hΛ hA i ζ s hs rhs)

/-- The shifted energy estimate retains the explicit growth rate needed for
contractive Yosida approximants after subtracting that rate. -/
private theorem c2m_physicalResolvent_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) *
      ‖c2m_physicalResolvent a ha hΛ hA i ζ s hs f‖ ≤ ‖f‖ := by
  let u := c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs f
  have he := c2m_physical_energy_lowerBound a ha hA (fun j => u.val (some j))
  have hd := (le_abs_self _).trans (c2m_physical_drift_absorption a ha hΛ hA i ζ u)
  have hf := c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs f u
  rw [c2m_physicalShiftedForm_apply, real_inner_self_eq_norm_sq] at hf
  have hc := real_inner_le_norm f (u.val none)
  have hn : 0 ≤ (Λ⁻¹ / 4) * ∑ j : Fin d, ‖u.val (some j)‖ ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  change (s - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u.val none‖ ≤ ‖f‖
  by_cases hz : ‖u.val none‖ = 0
  · rw [hz, mul_zero]
    exact norm_nonneg _
  · have hp : 0 < ‖u.val none‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    nlinarith only [he, hd, hf, hc, hn]

private theorem c2m_physicalGraphResolvent_unique_real {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (u : c2m_physicalGraph d)
    (hu : ∀ v, c2m_physicalShiftedForm a ha i ζ s u v =
      inner ℝ rhs (v.val none)) :
    u = c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs := by
  let hB := c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
  apply hB.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro v
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply]
  exact (hu v).trans (c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v).symm

private theorem c2m_physicalShiftedForm_shift {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (u v : c2m_physicalGraph d) :
    c2m_physicalShiftedForm a ha i ζ s u v =
      c2m_physicalShiftedForm a ha i ζ t u v +
      (s - t) * inner ℝ (u.val none) (v.val none) := by
  rw [c2m_physicalShiftedForm_apply, c2m_physicalShiftedForm_apply]
  ring

private theorem c2m_physicalResolvent_identity {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ)
    (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (ht : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < t)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalResolvent a ha hΛ hA i ζ s hs f -
      c2m_physicalResolvent a ha hΛ hA i ζ t ht f =
      (t - s) • c2m_physicalResolvent a ha hΛ hA i ζ s hs
        (c2m_physicalResolvent a ha hΛ hA i ζ t ht f) := by
  have he : c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs f -
      c2m_physicalGraphResolvent a ha hΛ hA i ζ t ht f =
      c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs
        ((t - s) • c2m_physicalResolvent a ha hΛ hA i ζ t ht f) := by
    apply c2m_physicalGraphResolvent_unique_real a ha hΛ hA i ζ s hs
    intro v
    rw [map_sub, ContinuousLinearMap.sub_apply,
      c2m_physicalGraphResolvent_spec, c2m_physicalShiftedForm_shift a ha i ζ s t,
      c2m_physicalGraphResolvent_spec]
    change inner ℝ f (v.val none) -
      (inner ℝ f (v.val none) + (s - t) *
        inner ℝ (c2m_physicalResolvent a ha hΛ hA i ζ t ht f) (v.val none)) = _
    simp only [real_inner_smul_left]
    ring
  rw [map_smul] at he
  have hh := congrArg (fun u : c2m_physicalGraph d => c2m_physicalGraphEval none u) he
  change (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs f).val none -
    (c2m_physicalGraphResolvent a ha hΛ hA i ζ t ht f).val none =
    (t - s) • (c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs
      (c2m_physicalResolvent a ha hΛ hA i ζ t ht f)).val none
  simpa only [map_sub, map_smul, c2m_physicalGraphEval, ContinuousLinearMap.comp_apply,
    PiLp.proj_apply, Submodule.subtypeL_apply] using hh

/-- Positive resolvents for the generator shifted by its uniform growth rate. -/
private def c2m_physicalShiftedResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (r : ℝ) (hr : 0 < r) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  c2m_physicalResolvent a ha hΛ hA i ζ
    ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r) (by linarith)

private theorem c2m_physicalShiftedResolvent_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (r : ℝ) (hr : 0 < r)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    r * ‖c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr f‖ ≤ ‖f‖ := by
  have hb := c2m_physicalResolvent_bound a ha hΛ hA i ζ
    ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r) (by linarith) f
  have hw : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r -
      (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 = r := by ring
  calc
    r * ‖c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr f‖ =
        ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r - (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) *
          ‖c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr f‖ :=
      congrArg (fun q : ℝ => q * ‖c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr f‖) hw.symm
    _ ≤ ‖f‖ := hb

private def c2m_physicalYosida {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (r : ℝ) (hr : 0 < r) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  r • (r • c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr -
    ContinuousLinearMap.id ℂ _)

private theorem c2m_physicalYosida_dissipative {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (r : ℝ) (hr : 0 < r)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℝ f (c2m_physicalYosida a ha hΛ hA i ζ r hr f) ≤ 0 := by
  have hb := c2m_physicalShiftedResolvent_bound a ha hΛ hA i ζ r hr f
  have hc := real_inner_le_norm f (c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr f)
  have hm := mul_le_mul_of_nonneg_left hc hr.le
  have hn := mul_le_mul_of_nonneg_left hb (norm_nonneg f)
  simp only [c2m_physicalYosida, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, inner_sub_right, real_inner_self_eq_norm_sq]
  exact mul_nonpos_of_nonneg_of_nonpos hr.le (by nlinarith only [hm, hn])

private def c2m_physicalYosidaEvolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (t : ℝ) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  NormedSpace.exp (t • c2m_physicalYosida a ha hΛ hA i ζ s hs)

private theorem c2m_physicalYosidaEvolution_hasDerivAt {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ) :
    HasDerivAt (fun r => c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs r f)
      (c2m_physicalYosida a ha hΛ hA i ζ s hs (c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure (Vec d))) f).restrictScalars ℝ
  exact E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (c2m_physicalYosida a ha hΛ hA i ζ s hs) t)

/-- Every bounded physical approximating evolution is contractive, uniformly
in the positive resolvent parameter and in the retained coefficient field. -/
private theorem c2m_physicalYosidaEvolution_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (t : ℝ) (ht : 0 ≤ t) : ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t f‖ ≤ ‖f‖ := by
  have hd (r : ℝ) := (c2m_physicalYosidaEvolution_hasDerivAt a ha hΛ hA i ζ s hs f r).norm_sq
  have hm := antitone_of_hasDerivAt_nonpos hd (fun r =>
    mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (c2m_physicalYosida_dissipative a ha hΛ hA i ζ s hs _))
  have hb := hm ht
  change ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t f‖ ^ 2 ≤
    ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs 0 f‖ ^ 2 at hb
  have hz : c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs 0 = ContinuousLinearMap.id ℂ _ := by
    change NormedSpace.exp ((0 : ℝ) • c2m_physicalYosida a ha hΛ hA i ζ s hs) = _
    have hzero : (0 : ℝ) • c2m_physicalYosida a ha hΛ hA i ζ s hs = 0 :=
      zero_smul ℝ (c2m_physicalYosida a ha hΛ hA i ζ s hs)
    rw [hzero, NormedSpace.exp_zero]
    rfl
  rw [hz, ContinuousLinearMap.id_apply] at hb
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hb

private instance c2m_physical_rationalOperator_normedAlgebra {d : ℕ} :
    NormedAlgebra ℚ (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) := .restrictScalars ℚ ℂ _

private instance c2m_physicalOperator_smulComm {d : ℕ} :
    SMulCommClass ℝ (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
      (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) where
  smul_comm c A B := by
    apply ContinuousLinearMap.ext
    intro f
    exact ((A.restrictScalars ℝ).map_smul c (B f)).symm

private instance c2m_physicalOperator_scalarTower {d : ℕ} :
    IsScalarTower ℝ (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
      (Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) where
  smul_assoc c A B := by
    apply ContinuousLinearMap.ext
    intro f
    rfl

private theorem c2m_physicalResolvent_commute {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (ht : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < t) :
    Commute (c2m_physicalResolvent a ha hΛ hA i ζ s hs)
      (c2m_physicalResolvent a ha hΛ hA i ζ t ht) := by
  by_cases he : s = t
  · subst t
    exact Commute.refl _
  · apply ContinuousLinearMap.ext
    intro f
    have hst := c2m_physicalResolvent_identity a ha hΛ hA i ζ s t hs ht f
    have hts := c2m_physicalResolvent_identity a ha hΛ hA i ζ t s ht hs f
    apply smul_right_injective (Lp ℂ 2 (volume : Measure (Vec d)))
      (sub_ne_zero.mpr (Ne.symm he) : t - s ≠ 0)
    change (t - s) • c2m_physicalResolvent a ha hΛ hA i ζ s hs
      (c2m_physicalResolvent a ha hΛ hA i ζ t ht f) =
      (t - s) • c2m_physicalResolvent a ha hΛ hA i ζ t ht
        (c2m_physicalResolvent a ha hΛ hA i ζ s hs f)
    rw [← hst, show t - s = -(s - t) by ring, neg_smul, ← hts, neg_sub]

private theorem c2m_physicalShiftedResolvent_commute {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Commute (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs)
      (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht) :=
  c2m_physicalResolvent_commute a ha hΛ hA i ζ
    ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + t)
    (by linarith) (by linarith)

private theorem c2m_physicalYosida_commute {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    Commute (c2m_physicalYosida a ha hΛ hA i ζ s hs)
      (c2m_physicalYosida a ha hΛ hA i ζ t ht) := by
  have hR := c2m_physicalShiftedResolvent_commute a ha hΛ hA i ζ s t hs ht
  have hB := (hR.smul_left s).smul_right t
  have hA := (hB.sub_right (Commute.one_right _)).sub_left
    ((Commute.one_left _).sub_right (Commute.refl 1))
  exact (hA.smul_left s).smul_right t

private theorem c2m_physicalYosida_commute_evolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (r : ℝ) :
    Commute (c2m_physicalYosida a ha hΛ hA i ζ s hs)
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht r) :=
  ((c2m_physicalYosida_commute a ha hΛ hA i ζ s t hs ht).smul_right r).exp_right

private theorem c2m_physicalYosidaEvolution_add {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (r t : ℝ) :
    c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs (r + t) =
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs r).comp
        (c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t) := by
  let A := c2m_physicalYosida a ha hΛ hA i ζ s hs
  have hcomm : Commute (r • A) (t • A) := by
    apply ContinuousLinearMap.ext
    intro f
    change r • A (t • A f) = t • A (r • A f)
    rw [A.map_smul_of_tower, A.map_smul_of_tower, smul_smul, smul_smul, mul_comm r t]
  change NormedSpace.exp ((r + t) • A) =
    (NormedSpace.exp (r • A)).comp (NormedSpace.exp (t • A))
  rw [show (r + t) • A = r • A + t • A from by simpa using! add_smul r t A,
    NormedSpace.exp_add_of_commute hcomm]
  rfl

private theorem c2m_physicalYosidaEvolution_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun t => c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t f) :=
  continuous_iff_continuousAt.mpr fun t =>
    (c2m_physicalYosidaEvolution_hasDerivAt a ha hΛ hA i ζ s hs f t).continuousAt

private theorem c2m_physicalYosidaEvolution_zero {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) :
    c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs 0 = ContinuousLinearMap.id ℂ _ := by
  change NormedSpace.exp ((0 : ℝ) • c2m_physicalYosida a ha hΛ hA i ζ s hs) = _
  rw [zero_smul ℝ (c2m_physicalYosida a ha hΛ hA i ζ s hs), NormedSpace.exp_zero]
  rfl

private theorem c2m_physicalYosidaEvolution_comparison_hasDerivAt {d : ℕ}
    (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (r q : ℝ) :
    HasDerivAt (fun z => c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs (r-z)
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht z f))
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs (r-q)
        (c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht q
          (c2m_physicalYosida a ha hΛ hA i ζ t ht f -
            c2m_physicalYosida a ha hΛ hA i ζ s hs f))) q := by
  let A := c2m_physicalYosida a ha hΛ hA i ζ s hs
  let B := c2m_physicalYosida a ha hΛ hA i ζ t ht
  let T := c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs
  let S := c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht
  have hT : HasDerivAt (fun z => T (r-z)) (-(T (r-q) * A)) q := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (r-q)).scomp q
      ((hasDerivAt_const q r).sub (hasDerivAt_id q))
    simpa only [zero_sub, neg_smul, one_smul] using! h
  have hS : HasDerivAt S (S q * B) q := hasDerivAt_exp_smul_const (𝕂 := ℝ) B q
  have hc : A * S q = S q * A :=
    (c2m_physicalYosida_commute_evolution a ha hΛ hA i ζ s t hs ht q).eq
  have hD : HasDerivAt (fun z => T (r-z) * S z)
      (T (r-q) * S q * (B-A)) q := by
    apply (hT.mul hS).congr_deriv
    have halg {α : Type} [Ring α] (X Y Z W : α)
        (h : Y * Z = Z * Y) : -(X * Y) * Z + X * (Z * W) = X * Z * (W - Y) := by
      rw [neg_mul, mul_assoc X Y Z, h]
      noncomm_ring
    exact halg (α := Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
      (T (r-q)) A (S q) B hc
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure (Vec d))) f).restrictScalars ℝ
  exact E.hasFDerivAt.comp_hasDerivAt q hD

/-- Uniform comparison of bounded physical approximations reduces convergence
to the initial bounded-generator gap, without stationarity of the fields. -/
private theorem c2m_physicalYosidaEvolution_comparison {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (r : ℝ) (hr : 0 ≤ r) :
    ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs r f -
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht r f‖ ≤
      r * ‖c2m_physicalYosida a ha hΛ hA i ζ s hs f -
        c2m_physicalYosida a ha hΛ hA i ζ t ht f‖ := by
  have hd (q : ℝ) (_hq : q ∈ Set.Icc 0 r) :=
    (c2m_physicalYosidaEvolution_comparison_hasDerivAt a ha hΛ hA i ζ s t hs ht f r q).hasDerivWithinAt
      (s := Set.Icc 0 r)
  have hb (q : ℝ) (hq : q ∈ Set.Ico 0 r) :
      ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs (r-q)
        (c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht q
          (c2m_physicalYosida a ha hΛ hA i ζ t ht f -
            c2m_physicalYosida a ha hΛ hA i ζ s hs f))‖ ≤
        ‖c2m_physicalYosida a ha hΛ hA i ζ t ht f -
          c2m_physicalYosida a ha hΛ hA i ζ s hs f‖ :=
    (c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ s hs _ (r-q)
      (sub_nonneg.mpr hq.2.le)).trans
      (c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ t ht _ q hq.1)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb r ⟨hr, le_rfl⟩
  simpa only [sub_self, sub_zero, c2m_physicalYosidaEvolution_zero,
    ContinuousLinearMap.id_apply, norm_sub_rev, mul_comm] using h

/-- Schwartz values and their classical coordinate derivatives belong to the
actual physical graph; no stationary law is used in this embedding. -/
private def c2m_physicalSchwartzGraph {d : ℕ} (f : SchwartzMap (Vec d) ℂ) :
    c2m_physicalGraph d := by
  let g (j : Fin d) : SchwartzMap (Vec d) ℂ :=
    (SchwartzMap.evalCLM ℝ (Vec d) ℂ (unitVector j)).comp
      (SchwartzMap.fderivCLM ℝ (Vec d) ℂ) f
  refine ⟨WithLp.toLp 2 (fun o => Option.elim o (f.toLp 2 volume)
    (fun j => (g j).toLp 2 volume)), ?_⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    f (fun j => g j) (f.coeFn_toLp 2 volume)
    (fun j => (g j).coeFn_toLp 2 volume)).mpr
  constructor
  · intro j
    have hd : coordinateDerivative j (fun x => (f x).re) = fun x => (g j x).re := by
      funext x
      have h : HasFDerivAt (fun y => (f y).re)
          (Complex.reCLM.comp (fderiv ℝ f x)) x :=
        Complex.reCLM.hasFDerivAt.comp x (f.hasFDerivAt x)
      change fderiv ℝ (fun y => (f y).re) x (unitVector j) = _
      rw [h.fderiv]
      rfl
    rw [← hd]
    exact hasWeakPartialDerivative_of_contDiff j _ (Complex.reCLM.contDiff.comp (f.smooth 1))
  · intro j
    have hd : coordinateDerivative j (fun x => (f x).im) = fun x => (g j x).im := by
      funext x
      have h : HasFDerivAt (fun y => (f y).im)
          (Complex.imCLM.comp (fderiv ℝ f x)) x :=
        Complex.imCLM.hasFDerivAt.comp x (f.hasFDerivAt x)
      change fderiv ℝ (fun y => (f y).im) x (unitVector j) = _
      rw [h.fderiv]
      rfl
    rw [← hd]
    exact hasWeakPartialDerivative_of_contDiff j _ (Complex.imCLM.contDiff.comp (f.smooth 1))

private theorem c2m_physicalGraphEval_denseRange (d : ℕ) :
    DenseRange (c2m_physicalGraphEval (d := d) none) := by
  apply (SchwartzMap.denseRange_toLpCLM (E := Vec d) (F := ℂ)
    (μ := volume) (p := 2) (by norm_num)).mono
  rintro _ ⟨f, rfl⟩
  exact ⟨c2m_physicalSchwartzGraph f, rfl⟩

/-- Coercivity and density of physical H1 values force the physical
resolvent to have dense range, even for a nonstationary coefficient. -/
private theorem c2m_physicalResolvent_denseRange {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    DenseRange (c2m_physicalResolvent a ha hΛ hA i ζ s hs) := by
  let R := (c2m_physicalResolvent a ha hΛ hA i ζ s hs).restrictScalars ℝ
  have hk : R.adjoint.ker = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    change R.adjoint f = 0 at hf
    change f = 0
    let u := c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs f
    have he : c2m_physicalShiftedForm a ha i ζ s u u = 0 := by
      rw [c2m_physicalGraphResolvent_spec]
      change inner ℝ f (R f) = 0
      rw [← R.adjoint_inner_left f f, hf, inner_zero_left]
    obtain ⟨c, hc, hb⟩ := c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
    have hu : u = 0 := by
      have hh := hb u
      rw [he] at hh
      have hn : ‖u‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg u]
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg u])
    apply (c2m_physicalGraphEval_denseRange d).eq_zero_of_inner_left ℝ
    intro v
    have hv := c2m_physicalGraphResolvent_spec a ha hΛ hA i ζ s hs f v
    change c2m_physicalShiftedForm a ha i ζ s u v = _ at hv
    rw [hu, map_zero, ContinuousLinearMap.zero_apply] at hv
    exact hv.symm
  have hh := R.adjoint.orthogonal_ker
  rw [hk, Submodule.bot_orthogonal_eq_top, ContinuousLinearMap.adjoint_adjoint] at hh
  change Dense (R.range : Set (Lp ℂ 2 (volume : Measure (Vec d))))
  exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hh.symm

private theorem c2m_physicalShiftedResolvent_denseRange {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (r : ℝ) (hr : 0 < r) :
    DenseRange (c2m_physicalShiftedResolvent a ha hΛ hA i ζ r hr) :=
  c2m_physicalResolvent_denseRange a ha hΛ hA i ζ
    ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r) (by linarith)

private theorem c2m_physicalShiftedResolvent_identity {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f -
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f =
      (t - s) • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) := by
  have h := c2m_physicalResolvent_identity a ha hΛ hA i ζ
    ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + t)
    (by linarith) (by linarith) f
  have he : ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + t) -
      ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) = t - s := by ring
  change c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f -
    c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f =
    (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + t) - ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s)) •
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) at h
  rw [he] at h
  exact h

private theorem c2m_physicalShiftedResolvent_normalized_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f‖ ≤ ‖f‖ := by
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hs] using
    c2m_physicalShiftedResolvent_bound a ha hΛ hA i ζ s hs f

private theorem c2m_physicalShiftedResolvent_range_error {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) -
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f =
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
        (t • c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f - f) := by
  let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
  let T := c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht
  have h := c2m_physicalShiftedResolvent_identity a ha hΛ hA i ζ s t hs ht f
  change R f - T f = (t - s) • R (T f) at h
  change s • R (T f) - T f = R (t • T f - f)
  calc
    _ = (R f - T f) + s • R (T f) - R f := by abel
    _ = (t - s) • R (T f) + s • R (T f) - R f := by rw [h]
    _ = _ := by rw [map_sub, R.map_smul_of_tower, ← add_smul, sub_add_cancel]

private theorem c2m_physicalShiftedResolvent_tendsto_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ) (ht : 0 < t) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) •
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f)) atTop
      (𝓝 (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  let g := t • c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f - f
  have hb (n : ℕ) : ‖((n : ℝ) + 1) •
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) -
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f‖ ≤ ((n : ℝ) + 1)⁻¹ * ‖g‖ := by
    rw [c2m_physicalShiftedResolvent_range_error]
    calc
      _ ≤ ‖g‖ / ((n : ℝ) + 1) := (le_div_iff₀' (by positivity : 0 < (n : ℝ) + 1)).mpr
        (c2m_physicalShiftedResolvent_bound a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) g)
      _ = _ := by rw [div_eq_inv_mul]
  have hz : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹ * ‖g‖) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mul_const ‖g‖
    simpa only [one_div, zero_mul] using h
  exact squeeze_zero (fun _ => norm_nonneg _) hb hz

/-- The normalized physical resolvents converge on every physical L2 datum.
This density argument applies to the retained, nonstationary coefficient. -/
private theorem c2m_physicalShiftedResolvent_tendsto {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) •
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) f) atTop (𝓝 f) := by
  let B (n : ℕ) := ((n : ℝ) + 1) •
    c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨g, hfg⟩ := (c2m_physicalShiftedResolvent_denseRange a ha hΛ hA i ζ 1 zero_lt_one).exists_dist_lt f (by positivity : 0 < ε / 3)
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ 1 zero_lt_one g
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (c2m_physicalShiftedResolvent_tendsto_on_range a ha hΛ hA i ζ 1 zero_lt_one g)
    (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hc : dist (B n f) (B n u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact c2m_physicalShiftedResolvent_normalized_bound a ha hΛ hA i ζ ((n : ℝ) + 1)
      (by positivity) (f-u)
  change dist (B n f) f < ε
  calc
    _ ≤ dist (B n f) (B n u) + dist (B n u) f := dist_triangle _ _ _
    _ ≤ dist f u + (dist (B n u) u + dist u f) :=
      add_le_add hc (dist_triangle _ _ _)
    _ < ε := by
      have hnu := hN n hn
      change dist (B n u) u < ε / 3 at hnu
      change dist f u < ε / 3 at hfg
      rw [dist_comm u f]
      linarith only [hfg, hnu]

private theorem c2m_physicalYosida_tendsto_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ) (ht : 0 < t) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun n : ℕ => c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
      (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f)) atTop
      (𝓝 (t • c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f - f)) := by
  have he (n : ℕ) : c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
      (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) =
      ((n : ℝ) + 1) • c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
        (t • c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f - f) := by
    simp only [c2m_physicalYosida, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [c2m_physicalShiftedResolvent_range_error]
  simp_rw [he]
  exact c2m_physicalShiftedResolvent_tendsto a ha hΛ hA i ζ _

private theorem c2m_physicalYosidaEvolution_cauchy_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ) (ht : 0 < t) (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (r : ℝ) (hr : 0 ≤ r) :
    CauchySeq (fun n : ℕ =>
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f)) := by
  have hc := (c2m_physicalYosida_tendsto_on_range a ha hΛ hA i ζ t ht f).cauchySeq
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < r + 1 := by linarith only [hr]
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hc (ε / (r + 1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ r * ‖c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity)
          (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f) -
        c2m_physicalYosida a ha hΛ hA i ζ ((m : ℝ) + 1) (by positivity)
          (c2m_physicalShiftedResolvent a ha hΛ hA i ζ t ht f)‖ :=
      c2m_physicalYosidaEvolution_comparison a ha hΛ hA i ζ _ _ (by positivity)
        (by positivity) _ r hr
    _ ≤ (r + 1) * _ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- The bounded physical evolutions converge strongly on all physical L2
data. Density and contraction extend the range-data comparison estimate. -/
private theorem c2m_physicalYosidaEvolution_cauchy {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec d))) (r : ℝ) (hr : 0 ≤ r) :
    CauchySeq (fun n : ℕ =>
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f) := by
  let T (n : ℕ) := c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1)
    (by positivity) r
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨g, hfg⟩ := (c2m_physicalShiftedResolvent_denseRange a ha hΛ hA i ζ 1 zero_lt_one).exists_dist_lt
    f (by positivity : 0 < ε / 3)
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ 1 zero_lt_one g
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp
    (c2m_physicalYosidaEvolution_cauchy_on_range a ha hΛ hA i ζ 1 zero_lt_one g r hr)
    (ε / 3) (by positivity)
  have hb (n : ℕ) : dist (T n f) (T n u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ _ (by positivity) (f-u) r hr
  refine ⟨N, fun n hn m hm => ?_⟩
  change dist (T n f) (T m f) < ε
  calc
    _ ≤ dist (T n f) (T n u) + (dist (T n u) (T m u) + dist (T m u) (T m f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u + (dist (T n u) (T m u) + dist f u) :=
      add_le_add (hb n) (add_le_add le_rfl (by simpa only [dist_comm] using hb m))
    _ < ε := by
      have hnm := hN n hn m hm
      change dist (T n u) (T m u) < ε / 3 at hnm
      change dist f u < ε / 3 at hfg
      linarith only [hfg, hnm]

private def c2m_physicalEvolutionLimit {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) :=
  limUnder atTop (fun n : ℕ =>
    c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f)

private theorem c2m_physicalEvolutionLimit_tendsto {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun n : ℕ =>
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f) atTop
      (𝓝 (c2m_physicalEvolutionLimit a ha hΛ hA i ζ r f)) :=
  (c2m_physicalYosidaEvolution_cauchy a ha hΛ hA i ζ f r r.property).tendsto_limUnder

private theorem c2m_physicalEvolutionLimit_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖c2m_physicalEvolutionLimit a ha hΛ hA i ζ r f‖ ≤ ‖f‖ :=
  le_of_tendsto (c2m_physicalEvolutionLimit_tendsto a ha hΛ hA i ζ r f).norm
    (Eventually.of_forall fun n =>
      c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) f r r.property)

/-- Canonical physical L2 evolution obtained from the actual variational
resolvents, available for retained coefficients without a stationary law. -/
private def c2m_physicalEvolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) (r : ℝ≥0) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (linearMapOfTendsto (c2m_physicalEvolutionLimit a ha hΛ hA i ζ r)
    (fun n : ℕ => (c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1)
      (by positivity) r).toLinearMap)
    (tendsto_pi_nhds.mpr (fun f => c2m_physicalEvolutionLimit_tendsto a ha hΛ hA i ζ r f))).mkContinuous 1
    (fun f => by simpa only [one_mul] using! c2m_physicalEvolutionLimit_bound a ha hΛ hA i ζ r f)

private theorem c2m_physicalEvolution_tendsto {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun n : ℕ =>
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f) atTop
      (𝓝 (c2m_physicalEvolution a ha hΛ hA i ζ r f)) :=
  c2m_physicalEvolutionLimit_tendsto a ha hΛ hA i ζ r f

private theorem c2m_physicalEvolution_bound {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖c2m_physicalEvolution a ha hΛ hA i ζ r f‖ ≤ ‖f‖ :=
  c2m_physicalEvolutionLimit_bound a ha hΛ hA i ζ r f

private theorem c2m_physicalEvolution_tendsto_apply {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (r : ℝ≥0) {u : ℕ → Lp ℂ 2 (volume : Measure (Vec d))}
    {f : Lp ℂ 2 (volume : Measure (Vec d))} (hu : Tendsto u atTop (𝓝 f)) :
    Tendsto (fun n : ℕ => c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1)
      (by positivity) r (u n)) atTop (𝓝 (c2m_physicalEvolution a ha hΛ hA i ζ r f)) := by
  have hz : Tendsto (fun n : ℕ =>
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r (u n) -
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (tendsto_iff_norm_sub_tendsto_zero.mp hu)
    rw [← map_sub]
    exact c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ ((n : ℝ) + 1)
      (by positivity) (u n-f) r r.property
  simpa only [sub_add_cancel, zero_add] using
    hz.add (c2m_physicalEvolution_tendsto a ha hΛ hA i ζ r f)

private theorem c2m_physicalEvolution_zero {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) :
    c2m_physicalEvolution a ha hΛ hA i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  have h := c2m_physicalEvolution_tendsto a ha hΛ hA i ζ 0 f
  simp only [NNReal.coe_zero, c2m_physicalYosidaEvolution_zero,
    ContinuousLinearMap.id_apply] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

private theorem c2m_physicalEvolution_add {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0) :
    c2m_physicalEvolution a ha hΛ hA i ζ (s+t) =
      (c2m_physicalEvolution a ha hΛ hA i ζ s).comp (c2m_physicalEvolution a ha hΛ hA i ζ t) := by
  apply ContinuousLinearMap.ext
  intro f
  have h := c2m_physicalEvolution_tendsto_apply a ha hΛ hA i ζ s
    (c2m_physicalEvolution_tendsto a ha hΛ hA i ζ t f)
  simp only [← ContinuousLinearMap.comp_apply, ← c2m_physicalYosidaEvolution_add,
    ← NNReal.coe_add] at h
  exact tendsto_nhds_unique (c2m_physicalEvolution_tendsto a ha hΛ hA i ζ (s+t) f) h

private theorem c2m_physicalYosidaEvolution_hasDerivAt_right {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ) :
    HasDerivAt (fun r => c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs r f)
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t (c2m_physicalYosida a ha hΛ hA i ζ s hs f)) t := by
  let E := (ContinuousLinearMap.apply ℂ (Lp ℂ 2 (volume : Measure (Vec d))) f).restrictScalars ℝ
  exact E.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (c2m_physicalYosida a ha hΛ hA i ζ s hs) t)

private theorem c2m_physicalYosidaEvolution_increment {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (t : ℝ) (ht : 0 ≤ t) :
    ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ s hs t f-f‖ ≤
      t * ‖c2m_physicalYosida a ha hΛ hA i ζ s hs f‖ := by
  have hd (r : ℝ) (_hr : r ∈ Set.Icc 0 t) :=
    (c2m_physicalYosidaEvolution_hasDerivAt_right a ha hΛ hA i ζ s hs f r).hasDerivWithinAt
      (s := Set.Icc 0 t)
  have hb (r : ℝ) (hr : r ∈ Set.Ico 0 t) :=
    c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ s hs
      (c2m_physicalYosida a ha hΛ hA i ζ s hs f) r hr.1
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hd hb t ⟨ht, le_rfl⟩
  simpa only [c2m_physicalYosidaEvolution_zero, ContinuousLinearMap.id_apply,
    sub_zero, mul_comm] using h

private theorem c2m_physicalEvolution_increment_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    ‖c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) -
      c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f‖ ≤
      (t : ℝ) * ‖s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f‖ := by
  exact le_of_tendsto_of_tendsto
    ((c2m_physicalEvolution_tendsto a ha hΛ hA i ζ t _).sub_const _).norm
    ((c2m_physicalYosida_tendsto_on_range a ha hΛ hA i ζ s hs f).norm.const_mul (t : ℝ))
    (Eventually.of_forall fun n => c2m_physicalYosidaEvolution_increment a ha hΛ hA i ζ
      ((n : ℝ) + 1) (by positivity) _ t t.property)

private theorem c2m_physicalEvolution_increment_between {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (t r : ℝ≥0) (htr : t ≤ r) :
    ‖c2m_physicalEvolution a ha hΛ hA i ζ r (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) -
      c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f)‖ ≤
      ((r : ℝ)-(t : ℝ)) * ‖s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f‖ := by
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f
  have he : c2m_physicalEvolution a ha hΛ hA i ζ r u - c2m_physicalEvolution a ha hΛ hA i ζ t u =
      c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalEvolution a ha hΛ hA i ζ (r-t) u-u) := by
    rw [map_sub]
    congr 1
    have hadd := congrArg (fun T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)) => T u)
      (c2m_physicalEvolution_add a ha hΛ hA i ζ t (r-t))
    simpa only [add_tsub_cancel_of_le htr, ContinuousLinearMap.comp_apply] using hadd
  rw [he]
  have h := (c2m_physicalEvolution_bound a ha hΛ hA i ζ t _).trans
    (c2m_physicalEvolution_increment_on_range a ha hΛ hA i ζ s hs f (r-t))
  simpa only [NNReal.coe_sub htr] using h

private theorem c2m_physicalEvolution_lipschitz_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    LipschitzWith ⟨‖s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f‖, norm_nonneg _⟩
      (fun t => c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f)) := by
  apply LipschitzWith.of_dist_le_mul
  intro t r
  rw [dist_eq_norm]
  change ‖c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) -
    c2m_physicalEvolution a ha hΛ hA i ζ r (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f)‖ ≤
    ‖s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f-f‖ * |(t : ℝ)-(r : ℝ)|
  rcases le_total t r with htr | hrt
  · rw [norm_sub_rev, abs_of_nonpos (sub_nonpos.mpr (show (t : ℝ) ≤ (r : ℝ) from htr)),
      neg_sub, mul_comm]
    exact c2m_physicalEvolution_increment_between a ha hΛ hA i ζ s hs f t r htr
  · rw [abs_of_nonneg (sub_nonneg.mpr (show (r : ℝ) ≤ (t : ℝ) from hrt)), mul_comm]
    exact c2m_physicalEvolution_increment_between a ha hΛ hA i ζ s hs f r t hrt

private theorem c2m_physicalEvolution_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun t => c2m_physicalEvolution a ha hΛ hA i ζ t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨g, hfg⟩ := (c2m_physicalShiftedResolvent_denseRange a ha hΛ hA i ζ 1 zero_lt_one).exists_dist_lt f
    (by positivity : 0 < ε/3)
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ 1 zero_lt_one g
  obtain ⟨δ, hδ, huδ⟩ := Metric.continuousAt_iff.mp
    (c2m_physicalEvolution_lipschitz_on_range a ha hΛ hA i ζ 1 zero_lt_one g).continuous.continuousAt
      (ε/3) (by positivity)
  refine ⟨δ, hδ, fun r hr => ?_⟩
  have hb (q : ℝ≥0) : dist (c2m_physicalEvolution a ha hΛ hA i ζ q f)
      (c2m_physicalEvolution a ha hΛ hA i ζ q u) ≤ dist f u := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact c2m_physicalEvolution_bound a ha hΛ hA i ζ q (f-u)
  calc
    _ ≤ dist (c2m_physicalEvolution a ha hΛ hA i ζ r f) (c2m_physicalEvolution a ha hΛ hA i ζ r u) +
        (dist (c2m_physicalEvolution a ha hΛ hA i ζ r u) (c2m_physicalEvolution a ha hΛ hA i ζ t u) +
          dist (c2m_physicalEvolution a ha hΛ hA i ζ t u) (c2m_physicalEvolution a ha hΛ hA i ζ t f)) := by
      rw [← add_assoc]
      exact dist_triangle4 _ _ _ _
    _ ≤ dist f u +
        (dist (c2m_physicalEvolution a ha hΛ hA i ζ r u) (c2m_physicalEvolution a ha hΛ hA i ζ t u) +
          dist f u) := add_le_add (hb r) (add_le_add le_rfl (by
            simpa only [dist_comm] using hb t))
    _ < ε := by
      have hgu := huδ hr
      change dist (c2m_physicalEvolution a ha hΛ hA i ζ r u)
        (c2m_physicalEvolution a ha hΛ hA i ζ t u) < ε/3 at hgu
      change dist f u < ε/3 at hfg
      linarith only [hfg, hgu]

/-- Separate action measurability suffices for evaluating a measurable datum. -/
private theorem c2m_measurable_operator_apply
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (A : Ω → E →L[ℂ] E) (hA : ∀ f, Measurable (fun ω => A ω f))
    (g : Ω → E) (hg : Measurable g) : Measurable (fun ω => A ω (g ω)) := by
  exact (measurable_uncurry_of_continuous_of_measurable
    (fun ω => (A ω).continuous) hA).comp (hg.prodMk measurable_id)

/-- Exponential action is measurable without operator-norm measurability. -/
private theorem c2m_measurable_operator_exp_apply
    {Ω E : Type*} [MeasurableSpace Ω] [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (A : Ω → E →L[ℂ] E) (hA : ∀ f, Measurable (fun ω => A ω f)) (f : E) :
    Measurable (fun ω => NormedSpace.exp (A ω) f) := by
  have hp (n : ℕ) : Measurable (fun ω => (A ω ^ n) f) := by
    induction n with
    | zero => simpa only [pow_zero, ContinuousLinearMap.one_apply] using
        (measurable_const : Measurable (fun _ : Ω => f))
    | succ n hn =>
        simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
          c2m_measurable_operator_apply A hA _ hn
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => ∑ k ∈ Finset.range n, ((k.factorial : ℂ)⁻¹) • (A ω ^ k) f)
  · intro n
    exact Finset.measurable_sum _ (fun k _ => measurable_const.smul (hp k))
  · apply tendsto_pi_nhds.mpr
    intro ω
    let ev := ContinuousLinearMap.apply ℂ E f
    have ht := ev.continuous.tendsto (NormedSpace.exp (A ω)) |>.comp
      (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (A ω)).tendsto_sum_nat
    simpa only [Function.comp_def, map_sum, map_smul, ev,
      ContinuousLinearMap.apply_apply] using ht

private theorem c2m_measurable_physicalEvolution
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalEvolution (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ t f) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have hR (r : ℝ) (hr : 0 < r) (g : Lp ℂ 2 (volume : Measure (Vec d))) :
      Measurable (fun ω => c2m_physicalShiftedResolvent (a ω) (hb ω) hΛ
        (Filter.Eventually.of_forall (hA ω)) i ζ r hr g) :=
    c2m_measurable_physicalResolvent a ha hb hΛ hA i ζ
      ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + r) (by linarith) g
  have hY (r : ℝ) (hr : 0 < r) (g : Lp ℂ 2 (volume : Measure (Vec d))) :
      Measurable (fun ω => c2m_physicalYosida (a ω) (hb ω) hΛ
        (Filter.Eventually.of_forall (hA ω)) i ζ r hr g) := by
    have hsc : Measurable (fun u : Lp ℂ 2 (volume : Measure (Vec d)) => r • u) :=
      (continuous_const_smul r).measurable
    have hm := hsc.comp ((hsc.comp (hR r hr g)).sub
      (measurable_const : Measurable (fun _ : Ω => g)))
    simpa only [c2m_physicalYosida, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
      Function.comp_def, Pi.sub_apply] using hm
  apply measurable_of_tendsto_metrizable
    (f := fun n ω => c2m_physicalYosidaEvolution (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ ((n : ℝ) + 1) (by positivity) t f)
  · intro n
    exact c2m_measurable_operator_exp_apply
      (fun ω => (t : ℝ) • c2m_physicalYosida (a ω) (hb ω) hΛ
        (Filter.Eventually.of_forall (hA ω)) i ζ ((n : ℝ) + 1) (by positivity))
      (fun g => by
        change Measurable (fun ω => (t : ℝ) • c2m_physicalYosida (a ω) (hb ω) hΛ
          (Filter.Eventually.of_forall (hA ω)) i ζ ((n : ℝ) + 1) (by positivity) g)
        have hsc : Measurable (fun u : Lp ℂ 2 (volume : Measure (Vec d)) => (t : ℝ) • u) :=
          (continuous_const_smul (t : ℝ)).measurable
        exact hsc.comp (hY ((n : ℝ) + 1) (by positivity) g)) f
  · apply tendsto_pi_nhds.mpr
    intro ω
    exact c2m_physicalEvolution_tendsto (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ t f

private theorem c2m_physical_energy_inner {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, ∑ j, ∑ k, star (G j x) * (a x j k : ℂ) * H k x) =
      ∑ j, ∑ k, inner ℂ (G j) (c2m_physicalCoefficientMul a ha j k (H k)) := by
  have hint (j k : Fin d) : Integrable
      (fun x => star (G j x) * (a x j k : ℂ) * H k x) volume := by
    have hp := ((Lp.memLp (G j)).star.integrable_mul (Lp.memLp (H k))).mul_of_top_right
      (ha j k)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply, Pi.star_apply]
    ring
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hint j k))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum _ (fun k _ => hint j k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [c2m_physicalCoefficientMul_coe a ha j k (H k)] with x hx
  simp only [hx, RCLike.inner_apply, Complex.star_def]
  ring

private theorem c2m_physical_inner_star {d : ℕ}
    (v f : Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℂ (star v) f = ∫ x, v x * f x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star v] with x hx
  change (star v) x = star (v x) at hx
  simp only [hx, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

private theorem c2m_physical_drift_inner {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℂ (star v) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (G j)) =
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * v x) := by
  have hint (j : Fin d) : Integrable
      (fun x => (a x j i : ℂ) * G j x * v x) volume := by
    have hp := ((Lp.memLp (G j)).integrable_mul (Lp.memLp v)).mul_of_top_right (ha j i)
    convert hp using 1
    ext x
    simp only [Pi.mul_apply]
    ring
  rw [inner_smul_right, inner_sum]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [integral_finset_sum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [c2m_physical_inner_star]
  apply integral_congr_ae
  filter_upwards [c2m_physicalCoefficientMul_coe a ha j i (G j)] with x hx
  rw [hx]
  ring

private theorem c2m_physicalGraphResolvent_generator {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    let u := c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs
    IsPhysicalComplexGeneratorPair a i ζ (u.val none) ((s : ℂ) • u.val none - rhs) := by
  let u := c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs rhs
  refine ⟨fun j => u.val (some j), u.property, ?_⟩
  intro v Gv hv
  let w0 : c2m_physicalGraph d :=
    ⟨WithLp.toLp 2 (fun o => o.elim v Gv), hv⟩
  let w := c2m_physicalGraphStar w0
  have ht := c2m_physicalGraphResolvent_complex_spec a ha hΛ hA i ζ s hs rhs w
  change (s : ℂ) * inner ℂ (star v) (u.val none) + ((1 / 2 : ℝ) : ℂ) *
    (∑ j, ∑ k, inner ℂ (star (Gv j)) (c2m_physicalCoefficientMul a ha j k (u.val (some k)))) -
    inner ℂ (star v) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (u.val (some j))) =
    inner ℂ (star v) rhs at ht
  rw [← c2m_physical_energy_inner, c2m_physical_drift_inner] at ht
  simp only [c2m_physical_inner_star] at ht
  have hE : (∫ x, ∑ j, ∑ k, star ((star (Gv j) : Lp ℂ 2 (volume : Measure (Vec d))) x) *
      (a x j k : ℂ) * u.val (some k) x) =
      ∫ x, ∑ j, ∑ k, (a x j k : ℂ) * u.val (some k) x * Gv j x := by
    apply integral_congr_ae
    have hgrad : ∀ᵐ x ∂volume, ∀ j, (star (Gv j) : Lp ℂ 2 (volume : Measure (Vec d))) x =
        star (Gv j x) := ae_all_iff.mpr fun j => Lp.coeFn_star (Gv j)
    filter_upwards [hgrad] with x hx
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx j, star_star]
    ring
  rw [hE] at ht
  have hm : (∫ x, ((s : ℂ) • u.val none - rhs : Lp ℂ 2 (volume : Measure (Vec d))) x * v x) =
      (s : ℂ) * (∫ x, v x * u.val none x) - ∫ x, v x * rhs x := by
    calc
      _ = ∫ x, (s : ℂ) * (v x * u.val none x) - v x * rhs x := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((s : ℂ) • u.val none) rhs,
          Lp.coeFn_smul (s : ℂ) (u.val none)] with x hx hy
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy
        rw [hx, hy]
        ring
      _ = _ := by
        have h1 : Integrable (fun x => (s : ℂ) * (v x * u.val none x)) volume :=
          ((Lp.memLp v).integrable_mul (Lp.memLp (u.val none))).const_mul _
        have h2 : Integrable (fun x => v x * rhs x) volume :=
          (Lp.memLp v).integrable_mul (Lp.memLp rhs)
        rw [integral_sub h1 h2, integral_const_mul]
  rw [hm]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at ht
  linear_combination ht

private theorem c2m_physicalShiftedResolvent_commute_evolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (r : ℝ) :
    Commute (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs)
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ t ht r) := by
  have hc := ((((c2m_physicalShiftedResolvent_commute a ha hΛ hA i ζ s t hs ht).smul_right t).sub_right
    (Commute.one_right _)).smul_right t).smul_right r
  exact hc.exp_right

private theorem c2m_commute_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {R T : E →L[ℂ] E} (h : Commute R T) (f : E) : R (T f) = T (R f) :=
  congrArg (fun S : E →L[ℂ] E => S f) h.eq

private theorem c2m_physicalEvolution_resolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (r : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs (c2m_physicalEvolution a ha hΛ hA i ζ r f) =
      c2m_physicalEvolution a ha hΛ hA i ζ r (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) := by
  let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
  have h : Tendsto (fun n : ℕ => R
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f))
      atTop (𝓝 (R (c2m_physicalEvolution a ha hΛ hA i ζ r f))) :=
    (R.continuous.tendsto _).comp (c2m_physicalEvolution_tendsto a ha hΛ hA i ζ r f)
  have he (n : ℕ) : c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f) =
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) :=
    c2m_commute_apply
      (c2m_physicalShiftedResolvent_commute_evolution a ha hΛ hA i ζ s ((n : ℝ) + 1) hs (by positivity) r) f
  have heq : (fun n : ℕ => R
      (c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r f)) =
      (fun n : ℕ => c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1)
        (by positivity) r (R f)) := funext he
  rw [heq] at h
  exact tendsto_nhds_unique h (c2m_physicalEvolution_tendsto a ha hΛ hA i ζ r (R f))

private theorem c2m_physicalEvolution_integral_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    (∫ r in (0 : ℝ)..(t : ℝ), c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal
      (s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f)) =
      c2m_physicalEvolution a ha hΛ hA i ζ t (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) -
        c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f := by
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f
  let g := s • u - f
  let F (n : ℕ) (r : ℝ) := c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1)
    (by positivity) r (c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) u)
  have he (n : ℕ) : c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) u =
      ((n : ℝ) + 1) • c2m_physicalShiftedResolvent a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) g := by
    simp only [c2m_physicalYosida, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    rw [c2m_physicalShiftedResolvent_range_error]
  have hlim : Tendsto (fun n => ∫ r in (0 : ℝ)..(t : ℝ), F n r) atTop
      (𝓝 (∫ r in (0 : ℝ)..(t : ℝ), c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal g)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => ‖g‖)
    · exact Eventually.of_forall fun n =>
        (c2m_physicalYosidaEvolution_continuous a ha hΛ hA i ζ ((n : ℝ) + 1)
          (by positivity) _).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro r hr
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hr
      change ‖c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) r
        (c2m_physicalYosida a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) u)‖ ≤ ‖g‖
      exact (c2m_physicalYosidaEvolution_bound a ha hΛ hA i ζ ((n : ℝ) + 1)
        (by positivity) _ r hr.1.le).trans (he n ▸
          c2m_physicalShiftedResolvent_normalized_bound a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) g)
    · exact intervalIntegrable_const
    · apply Eventually.of_forall
      intro r hr
      rw [Set.uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hr
      have hl := c2m_physicalEvolution_tendsto_apply a ha hΛ hA i ζ r.toNNReal
        (c2m_physicalYosida_tendsto_on_range a ha hΛ hA i ζ s hs f)
      simpa only [Real.coe_toNNReal r hr.1.le] using hl
  have hint (n : ℕ) : (∫ r in (0 : ℝ)..(t : ℝ), F n r) =
      c2m_physicalYosidaEvolution a ha hΛ hA i ζ ((n : ℝ) + 1) (by positivity) t u-u := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := (t : ℝ))
      (fun r _ => c2m_physicalYosidaEvolution_hasDerivAt_right a ha hΛ hA i ζ
        ((n : ℝ) + 1) (by positivity) u r)
      ((c2m_physicalYosidaEvolution_continuous a ha hΛ hA i ζ ((n : ℝ) + 1)
        (by positivity) _).intervalIntegrable 0 t)
    simpa only [c2m_physicalYosidaEvolution_zero, ContinuousLinearMap.id_apply] using h
  simp only [hint] at hlim
  exact tendsto_nhds_unique hlim
    ((c2m_physicalEvolution_tendsto a ha hΛ hA i ζ t u).sub_const u)

/-- Physical retained evolution has the actual time derivative from the right,
including the initial time, for every resolvent-range datum. -/
private theorem c2m_physicalEvolution_hasDerivWithinAt_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    HasDerivWithinAt
      (fun r : ℝ => c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f))
      (c2m_physicalEvolution a ha hΛ hA i ζ t (s • c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f))
      (Set.Ici 0) (t : ℝ) := by
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f
  let g := s • u-f
  let F (r : ℝ) := c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal g
  have hF : Continuous F := (c2m_physicalEvolution_continuous a ha hΛ hA i ζ g).comp
    continuous_real_toNNReal
  have hi := (hF.integral_hasStrictDerivAt 0 (t : ℝ)).hasDerivAt
  have hd : HasDerivAt (fun r : ℝ => u + ∫ q in (0 : ℝ)..r, F q) (F t) (t : ℝ) := by
    simpa only [zero_add] using! (hasDerivAt_const (t : ℝ) u).add hi
  have hd' := hd.hasDerivWithinAt (s := Set.Ici 0)
  have hh : HasDerivWithinAt (fun r : ℝ => c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal u)
      (F t) (Set.Ici 0) (t : ℝ) := by
    apply hd'.congr_of_mem ?_ t.property
    intro r hr
    have he := c2m_physicalEvolution_integral_on_range a ha hΛ hA i ζ s hs f r.toNNReal
    rw [Real.coe_toNNReal r hr] at he
    change (∫ q in (0 : ℝ)..r, F q) = c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal u-u at he
    rw [he]
    abel
  simpa only [F, Real.toNNReal_coe] using hh

/-- The full physical weak generator domain is the physical resolvent range. -/
private theorem c2m_physicalGenerator_resolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    f = c2m_physicalResolvent a ha hΛ hA i ζ s hs (s • f-g) := by
  rcases hfg with ⟨G, hG, hweak⟩
  let u : c2m_physicalGraph d := ⟨WithLp.toLp 2 (fun o => o.elim f G), hG⟩
  have hu : u = c2m_physicalGraphResolvent a ha hΛ hA i ζ s hs (s • f-g) := by
    apply c2m_physicalGraphResolvent_unique a ha hΛ hA i ζ s hs (s • f-g) u
    intro v
    let w := c2m_physicalGraphStar v
    have ht := hweak (w.val none) (fun j => w.val (some j)) w.property
    change (∫ x, g x * (star (v.val none) : Lp ℂ 2 (volume : Measure (Vec d))) x) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (star (v.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x) +
      ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) *
        (star (v.val none) : Lp ℂ 2 (volume : Measure (Vec d))) x) at ht
    have hm : (∫ x, g x * (star (v.val none) : Lp ℂ 2 (volume : Measure (Vec d))) x) =
        inner ℂ (v.val none) g := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star (v.val none)] with x hx
      change (star (v.val none) : Lp ℂ 2 (volume : Measure (Vec d))) x =
        star (v.val none x) at hx
      simp only [hx, RCLike.inner_apply, Complex.star_def]
    have hE : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (star (v.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x) =
        ∑ j, ∑ k, inner ℂ (v.val (some j)) (c2m_physicalCoefficientMul a ha j k (G k)) := by
      rw [← c2m_physical_energy_inner]
      apply integral_congr_ae
      have hv : ∀ᵐ x ∂volume, ∀ j, (star (v.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x =
          star (v.val (some j) x) := ae_all_iff.mpr fun j => Lp.coeFn_star _
      filter_upwards [hv] with x hx
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [hx j]
      ring
    have hD := c2m_physical_drift_inner a ha i ζ (star (v.val none)) G
    rw [star_star] at hD
    rw [hm, hE, ← hD] at ht
    change (s : ℂ) * inner ℂ (v.val none) f + ((1 / 2 : ℝ) : ℂ) *
      (∑ j, ∑ k, inner ℂ (v.val (some j)) (c2m_physicalCoefficientMul a ha j k (G k))) -
      inner ℂ (v.val none) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (G j)) =
      inner ℂ (v.val none) (s • f-g)
    simp only [inner_sub_right, RCLike.real_smul_eq_coe_smul (K := ℂ) s f, inner_smul_right] at ht ⊢
    have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
    rw [hhalf]
    linear_combination ht
  exact congrArg (fun v : c2m_physicalGraph d => v.val none) hu


/-- Convert a right derivative in real time into the physical complex quotient. -/
private theorem c2m_tendsto_quotient_of_hasDerivWithinAt {d : ℕ}
    (F : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d))) (g : Lp ℂ 2 (volume : Measure (Vec d)))
    (h : HasDerivWithinAt (fun r : ℝ => F r.toNNReal) g (Set.Ici 0) 0) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (F t - F 0))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  have hc : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    change Filter.map _ _ ≤ _
    rw [NNReal.map_coe_nhdsGT]
    rfl
  have hm : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 \ {0} := by
    intro x hx
    have hx' : 0 < x := hx
    exact ⟨hx'.le, by simpa using ne_of_gt hx'⟩
  have hh := (hasDerivWithinAt_iff_tendsto_slope.mp h).comp
    (hc.mono_right (nhdsWithin_mono 0 hm))
  have hh' : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (F t - F 0))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
    simpa only [Function.comp_def, slope_def_module, sub_zero, Real.toNNReal_coe,
      Real.toNNReal_zero] using hh
  apply hh'.congr
  intro t
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  congr 1 <;> norm_cast


/-- Remove the coercivity growth shift from the retained physical evolution. -/
private noncomputable def c2m_physicalUnshiftedEvolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  Real.exp ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (t : ℝ)) • c2m_physicalEvolution a ha hΛ hA i ζ t

private theorem c2m_physicalUnshiftedEvolution_zero {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) :
    c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  simp only [c2m_physicalUnshiftedEvolution, NNReal.coe_zero, mul_zero, Real.exp_zero,
    one_smul, c2m_physicalEvolution_zero]

private theorem c2m_physicalUnshiftedEvolution_add {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0) :
    c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ (s+t) =
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ s).comp
        (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [c2m_physicalUnshiftedEvolution, NNReal.coe_add, mul_add, Real.exp_add,
    c2m_physicalEvolution_add, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.map_smul_of_tower, mul_smul]

private theorem c2m_physicalUnshiftedEvolution_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun t : ℝ≥0 => c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t f) := by
  exact (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul
    (c2m_physicalEvolution_continuous a ha hΛ hA i ζ f)


private theorem c2m_physicalUnshiftedEvolution_derivative_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    HasDerivWithinAt
      (fun r : ℝ => c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ r.toNNReal
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f))
      (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) •
        c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f) (Set.Ici 0) 0 := by
  let w : ℝ := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f
  have hc : HasDerivAt (fun r : ℝ => Real.exp (w * r)) w 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul w).exp
  have hd := c2m_physicalEvolution_hasDerivWithinAt_on_range a ha hΛ hA i ζ s hs f 0
  have hh := hc.hasDerivWithinAt.smul hd
  simp only [NNReal.coe_zero, Real.toNNReal_zero, mul_zero, Real.exp_zero,
    c2m_physicalEvolution_zero, ContinuousLinearMap.id_apply, one_smul] at hh
  have he : (s • u - f) + w • u = (w+s) • u - f := by
    rw [add_smul]
    abel
  change HasDerivWithinAt _ ((s • u - f) + w • u) (Set.Ici 0) 0 at hh
  rw [he] at hh
  apply hh.congr_of_mem ?_ (by simp)
  intro r hr
  change Real.exp (w * (r.toNNReal : ℝ)) • c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal u =
    Real.exp (w * r) • c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal u
  rw [Real.coe_toNNReal r hr]

private theorem c2m_physicalUnshiftedEvolution_quotient_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) -
        c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) •
        c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f - f)) := by
  let u := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f
  let g := ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) • u - f
  have hd : HasDerivWithinAt
      (fun r : ℝ => c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ r.toNNReal u)
      g (Set.Ici 0) 0 :=
    c2m_physicalUnshiftedEvolution_derivative_on_range a ha hΛ hA i ζ s hs f
  have ht := c2m_tendsto_quotient_of_hasDerivWithinAt (d := d)
    (fun t => c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t u) g hd
  have hz : c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ 0 u = u := by
    rw [c2m_physicalUnshiftedEvolution_zero]
    rfl
  change Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
    (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t u -
      c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ 0 u)) (𝓝[>] (0 : ℝ≥0)) (𝓝 g) at ht
  rw [hz] at ht
  exact ht



private theorem c2m_physicalUnshiftedEvolution_resolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (t : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t f) =
      c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs f) := by
  simp only [c2m_physicalUnshiftedEvolution, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.map_smul_of_tower, c2m_physicalEvolution_resolvent]

/-- No extra smoothness is hidden in the infinitesimal generator domain. -/
private theorem c2m_physicalUnshiftedEvolution_generator_iff {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsPhysicalComplexGeneratorPair a i ζ f g := by
  let s : ℝ := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + 1
  have hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s := by dsimp [s]; linarith
  let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ 1 (by norm_num)
  have hR : R = c2m_physicalResolvent a ha hΛ hA i ζ s hs := rfl
  have hrange (u : Lp ℂ 2 (volume : Measure (Vec d))) :
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
        (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t (R u) - R u))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (s • R u - u)) :=
    c2m_physicalUnshiftedEvolution_quotient_on_range a ha hΛ hA i ζ 1 (by norm_num) u
  constructor
  · intro h
    have hh := (R.continuous.tendsto g).comp h
    have he (t : ℝ≥0) : R (((t : ℝ) : ℂ)⁻¹ •
        (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t f - f)) =
        ((t : ℝ) : ℂ)⁻¹ • (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t (R f) - R f) := by
      rw [map_smul, map_sub]
      rw [c2m_physicalUnshiftedEvolution_resolvent]
    change Tendsto (fun t : ℝ≥0 => R (((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t f-f))) (𝓝[>] (0 : ℝ≥0)) (𝓝 (R g)) at hh
    simp only [he] at hh
    have hg : R g = s • R f-f := tendsto_nhds_unique hh (hrange f)
    have hf : f = R (s • f-g) := by
      rw [map_sub, R.map_smul_of_tower, hg]
      abel
    have hw := c2m_physicalGraphResolvent_generator a ha hΛ hA i ζ s hs (s • f-g)
    change IsPhysicalComplexGeneratorPair a i ζ
      (c2m_physicalResolvent a ha hΛ hA i ζ s hs (s • f-g))
      ((s : ℂ) • c2m_physicalResolvent a ha hΛ hA i ζ s hs (s • f-g) - (s • f-g)) at hw
    rw [← hR, ← hf] at hw
    have hsm : (s : ℂ) • f = s • f := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      congr 1 <;> norm_cast
    rw [hsm] at hw
    simpa only [sub_sub_cancel] using hw
  · intro h
    have hf : f = R (s • f-g) := by
      rw [hR]
      exact c2m_physicalGenerator_resolvent a ha hΛ hA i ζ s hs h
    have hh := hrange (s • f-g)
    rw [← hf] at hh
    simpa only [sub_sub_cancel] using hh

private theorem c2m_physicalUnshiftedEvolution_isSemigroup {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) :
    IsPhysicalComplexSemigroup a i ζ (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ) := by
  exact ⟨c2m_physicalUnshiftedEvolution_zero a ha hΛ hA i ζ,
    c2m_physicalUnshiftedEvolution_add a ha hΛ hA i ζ,
    c2m_physicalUnshiftedEvolution_continuous a ha hΛ hA i ζ,
    c2m_physicalUnshiftedEvolution_generator_iff a ha hΛ hA i ζ⟩


private theorem c2m_measurable_physicalUnshiftedEvolution
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalUnshiftedEvolution (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ t f) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  exact (continuous_const_smul (Real.exp ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (t : ℝ)))).measurable.comp
    (c2m_measurable_physicalEvolution a ha hb hΛ hA i ζ t f)


private theorem c2m_physicalLp_star_add {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) : star (f+g) = star f+star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f+g), Lp.coeFn_add f g, Lp.coeFn_star f,
    Lp.coeFn_star g, Lp.coeFn_add (star f) (star g)] with x h1 h2 h3 h4 h5
  simpa only [Pi.star_apply, Pi.add_apply, h1, h2, h3, h4, h5, star_add]

private theorem c2m_physicalLp_star_smul {d : ℕ}
    (c : ℂ) (f : Lp ℂ 2 (volume : Measure (Vec d))) : star (c • f) = star c • star f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (c • f), Lp.coeFn_smul c f, Lp.coeFn_star f,
    Lp.coeFn_smul (star c) (star f)] with x h1 h2 h3 h4
  simpa only [Pi.star_apply, Pi.smul_apply, h1, h2, h3, h4, star_smul]

private theorem c2m_physicalLp_norm_star {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) : ‖star f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  exact (eLpNorm_congr_ae (Lp.coeFn_star f)).trans eLpNorm_star

/-- Bilinear transpose on physical L2, obtained by conjugating the Hilbert adjoint. -/
private noncomputable def c2m_physicalBilinearTranspose {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  ({ toFun := fun f => star (T.adjoint (star f))
     map_add' := by intro f g; simp only [c2m_physicalLp_star_add, map_add]
     map_smul' := by intro c f; simp only [c2m_physicalLp_star_smul, map_smul, star_star, RingHom.id_apply] } :
      Lp ℂ 2 (volume : Measure (Vec d)) →ₗ[ℂ] Lp ℂ 2 (volume : Measure (Vec d))).mkContinuous
    ‖T.adjoint‖ (fun f => by
      change ‖star (T.adjoint (star f))‖ ≤ ‖T.adjoint‖ * ‖f‖
      simpa only [c2m_physicalLp_norm_star] using T.adjoint.le_opNorm (star f))

private theorem c2m_physicalBilinearTranspose_apply {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalBilinearTranspose T f = star (T.adjoint (star f)) := rfl

private theorem c2m_physicalBilinearTranspose_id (d : ℕ) :
    c2m_physicalBilinearTranspose (ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume : Measure (Vec d)))) =
      ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [c2m_physicalBilinearTranspose_apply, ContinuousLinearMap.adjoint_id,
    ContinuousLinearMap.id_apply, star_star]

private theorem c2m_physicalBilinearTranspose_comp {d : ℕ}
    (T S : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) :
    c2m_physicalBilinearTranspose (T.comp S) =
      (c2m_physicalBilinearTranspose S).comp (c2m_physicalBilinearTranspose T) := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [c2m_physicalBilinearTranspose_apply, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply, star_star]

private theorem c2m_physical_inner_star_right {d : ℕ}
    (v h : Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℂ v (star h) = inner ℂ h (star v) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star v, Lp.coeFn_star h] with x hv hh
  change (star v : Lp ℂ 2 (volume : Measure (Vec d))) x = star (v x) at hv
  change (star h : Lp ℂ 2 (volume : Measure (Vec d))) x = star (h x) at hh
  simp only [hv, hh, RCLike.inner_apply, Complex.star_def]
  ring

private theorem c2m_physicalBilinearTranspose_pairing {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, T f x * g x) = ∫ x, f x * c2m_physicalBilinearTranspose T g x := by
  have h := T.adjoint_inner_left f (star g)
  rw [c2m_physicalBilinearTranspose_apply]
  have he := c2m_physical_inner_star (star (T.adjoint (star g))) f
  rw [star_star] at he
  rw [c2m_physical_inner_star] at h
  calc
    (∫ x, T f x * g x) = ∫ x, g x * T f x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _
    _ = inner ℂ (T.adjoint (star g)) f := h.symm
    _ = ∫ x, star (T.adjoint (star g)) x * f x := he
    _ = ∫ x, f x * star (T.adjoint (star g)) x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => mul_comm _ _


private theorem c2m_measurable_physicalBilinearTranspose_action
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (T : Ω → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (hT : ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
        borel (Lp ℂ 2 (volume : Measure (Vec d)))
      Measurable (fun ω => T ω f)) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalBilinearTranspose (T ω) f) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  apply c2m_measurable_of_inner
  intro v
  have he (ω : Ω) : inner ℝ v (c2m_physicalBilinearTranspose (T ω) f) =
      (inner ℂ (star f) (T ω (star v))).re := by
    rw [c2m_physical_realInner, c2m_physicalBilinearTranspose_apply,
      c2m_physical_inner_star_right, (T ω).adjoint_inner_left]
  simp only [he]
  exact Complex.continuous_re.measurable.comp
    ((continuous_const.inner continuous_id).measurable.comp (hT (star v)))


private noncomputable def c2m_physicalTransposeEvolution {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  c2m_physicalBilinearTranspose (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t)

private theorem c2m_physicalTransposeEvolution_zero {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) :
    c2m_physicalTransposeEvolution a ha hΛ hA i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  rw [c2m_physicalTransposeEvolution, c2m_physicalUnshiftedEvolution_zero,
    c2m_physicalBilinearTranspose_id]

private theorem c2m_physicalTransposeEvolution_add {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) (s t : ℝ≥0) :
    c2m_physicalTransposeEvolution a ha hΛ hA i ζ (s+t) =
      (c2m_physicalTransposeEvolution a ha hΛ hA i ζ s).comp
        (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t) := by
  change c2m_physicalBilinearTranspose (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ (s+t)) = _
  rw [add_comm s t, c2m_physicalUnshiftedEvolution_add, c2m_physicalBilinearTranspose_comp]
  rfl

private theorem c2m_measurable_physicalTransposeEvolution
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (a : Ω → Vec d → Mat d)
    (ha : Measurable (fun p : Ω × Vec d => a p.1 p.2))
    (hb : ∀ ω j k, MemLp (fun x => (a ω x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ ω x, S5Elliptic (a ω x) Λ)
    (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    Measurable (fun ω => c2m_physicalTransposeEvolution (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ t f) := by
  exact c2m_measurable_physicalBilinearTranspose_action
    (fun ω => c2m_physicalUnshiftedEvolution (a ω) (hb ω) hΛ
      (Filter.Eventually.of_forall (hA ω)) i ζ t)
    (c2m_measurable_physicalUnshiftedEvolution a ha hb hΛ hA i ζ t) f


/-- Contractivity upgrades weak continuity of Hilbert adjoints to strong continuity at zero. -/
private theorem c2m_adjoint_continuousAt_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : ℝ≥0 → E →L[ℂ] E)
    (h0 : T 0 = ContinuousLinearMap.id ℂ E)
    (hb : ∀ t f, ‖T t f‖ ≤ ‖f‖) (hc : ∀ f, Continuous (fun t => T t f)) (f : E) :
    ContinuousAt (fun t => (T t).adjoint f) 0 := by
  have hadj (t : ℝ≥0) : ‖(T t).adjoint f‖ ≤ ‖f‖ := by
    have hn : ‖(T t).adjoint‖ = ‖T t‖ := ContinuousLinearMap.adjoint.norm_map (T t)
    have ho : ‖T t‖ ≤ 1 := (T t).opNorm_le_bound (by norm_num) (by
      intro g
      simpa only [one_mul] using hb t g)
    exact ((T t).adjoint.le_opNorm f).trans (by rw [hn]; nlinarith [norm_nonneg f])
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hi : ContinuousAt (fun t => (inner ℂ f (T t f)).re) 0 :=
    Complex.continuous_re.continuousAt.comp
      (continuous_const.inner (hc f)).continuousAt
  have hi0 : (inner ℂ f (T 0 f)).re = ‖f‖ ^ 2 := by
    rw [h0, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K]
    norm_cast
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hi (ε ^ 2 / 2) (by positivity)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hid := hd ht
  rw [Real.dist_eq, hi0] at hid
  have hnorm := norm_sub_sq (𝕜 := ℂ) ((T t).adjoint f) f
  rw [(T t).adjoint_inner_left] at hnorm
  change ‖(T t).adjoint f - f‖ ^ 2 =
    ‖(T t).adjoint f‖ ^ 2 - 2 * (inner ℂ f (T t f)).re + ‖f‖ ^ 2 at hnorm
  have hb' := hadj t
  have hs : ‖(T t).adjoint f - f‖ ^ 2 < ε ^ 2 := by
    have ha := (abs_lt.mp hid).1
    nlinarith [norm_nonneg ((T t).adjoint f), norm_nonneg f]
  rw [h0, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, dist_eq_norm]
  nlinarith [norm_nonneg ((T t).adjoint f - f)]

private theorem c2m_contractSemigroup_continuous_of_zero {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (T : ℝ≥0 → E →L[ℂ] E)
    (h0 : T 0 = ContinuousLinearMap.id ℂ E)
    (hadd : ∀ s t, T (s+t) = (T s).comp (T t))
    (hb : ∀ t f, ‖T t f‖ ≤ ‖f‖) (f : E)
    (hc : ContinuousAt (fun t => T t f) 0) : Continuous (fun t => T t f) := by
  have hbetween (s t : ℝ≥0) (hst : s ≤ t) :
      dist (T t f) (T s f) ≤ dist (T (t-s) f) f := by
    have he : t = s + (t-s) := (add_tsub_cancel_of_le hst).symm
    nth_rw 1 [he]
    rw [hadd, ContinuousLinearMap.comp_apply, dist_eq_norm, dist_eq_norm, ← map_sub]
    exact hb s (T (t-s) f - f)
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun r hr => ?_⟩
  rcases le_total t r with htr | hrt
  · have hdist : dist (r-t) 0 = dist r t := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub htr, NNReal.coe_zero, sub_zero, abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ r from htr))]
    have hh := hd (by rwa [hdist])
    rw [h0, ContinuousLinearMap.id_apply] at hh
    exact (hbetween t r htr).trans_lt hh
  · have hdist : dist (t-r) 0 = dist r t := by
      rw [NNReal.dist_eq, NNReal.dist_eq, NNReal.coe_sub hrt, NNReal.coe_zero, sub_zero,
        abs_of_nonneg (sub_nonneg.mpr (show (r : ℝ) ≤ t from hrt)), abs_of_nonpos (sub_nonpos.mpr (show (r : ℝ) ≤ t from hrt)), neg_sub]
    have hh := hd (by rwa [hdist])
    rw [h0, ContinuousLinearMap.id_apply] at hh
    have hle : dist (T r f) (T t f) ≤ dist (T (t-r) f) f := by
      simpa only [dist_comm] using hbetween r t hrt
    exact hle.trans_lt hh

private theorem c2m_physicalLp_star_sub {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) : star (f-g) = star f-star g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (f-g), Lp.coeFn_sub f g, Lp.coeFn_star f,
    Lp.coeFn_star g, Lp.coeFn_sub (star f) (star g)] with x h1 h2 h3 h4 h5
  simpa only [Pi.star_apply, Pi.sub_apply, h1, h2, h3, h4, h5, star_sub]

private theorem c2m_physicalLp_star_continuous {d : ℕ} :
    Continuous (star : Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d))) := by
  apply (LipschitzWith.of_dist_le_mul (K := 1) ?_).continuous
  intro f g
  simp only [dist_eq_norm, ← c2m_physicalLp_star_sub, c2m_physicalLp_norm_star,
    NNReal.coe_one, one_mul]
  exact le_rfl

private theorem c2m_physicalEvolution_adjoint_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun t => (c2m_physicalEvolution a ha hΛ hA i ζ t).adjoint f) := by
  let T := c2m_physicalEvolution a ha hΛ hA i ζ
  have h0 : T 0 = ContinuousLinearMap.id ℂ _ := c2m_physicalEvolution_zero a ha hΛ hA i ζ
  have hb (t : ℝ≥0) (g : Lp ℂ 2 (volume : Measure (Vec d))) : ‖(T t).adjoint g‖ ≤ ‖g‖ := by
    have hn : ‖(T t).adjoint‖ = ‖T t‖ := ContinuousLinearMap.adjoint.norm_map (T t)
    have ho : ‖T t‖ ≤ 1 := (T t).opNorm_le_bound (by norm_num) (by
      intro u
      simpa only [one_mul] using c2m_physicalEvolution_bound a ha hΛ hA i ζ t u)
    exact ((T t).adjoint.le_opNorm g).trans (by rw [hn]; nlinarith [norm_nonneg g])
  apply c2m_contractSemigroup_continuous_of_zero (fun t => (T t).adjoint)
    (by rw [h0, ContinuousLinearMap.adjoint_id]) ?_ hb f
  · exact c2m_adjoint_continuousAt_zero T h0
      (c2m_physicalEvolution_bound a ha hΛ hA i ζ)
      (c2m_physicalEvolution_continuous a ha hΛ hA i ζ) f
  · intro s t
    change (T (s+t)).adjoint = _
    dsimp only [T]
    rw [add_comm s t, c2m_physicalEvolution_add, ContinuousLinearMap.adjoint_comp]

private theorem c2m_physicalAdjoint_real_smul {d : ℕ} (r : ℝ)
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))) :
    (r • T).adjoint = r • T.adjoint := by
  change ContinuousLinearMap.adjoint ((r : ℂ) • T) = (r : ℂ) • T.adjoint
  rw [map_smulₛₗ]
  simp

private theorem c2m_physicalTransposeEvolution_continuous {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Continuous (fun t => c2m_physicalTransposeEvolution a ha hΛ hA i ζ t f) := by
  have hc : Continuous (fun t : ℝ≥0 =>
      Real.exp ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (t : ℝ)) •
        (c2m_physicalEvolution a ha hΛ hA i ζ t).adjoint (star f)) :=
    (Real.continuous_exp.comp
    (continuous_const.mul NNReal.continuous_coe)).smul
      (c2m_physicalEvolution_adjoint_continuous a ha hΛ hA i ζ (star f))
  apply c2m_physicalLp_star_continuous.comp at hc
  simpa only [Function.comp_def, c2m_physicalTransposeEvolution, c2m_physicalBilinearTranspose_apply,
    c2m_physicalUnshiftedEvolution, c2m_physicalAdjoint_real_smul,
    ContinuousLinearMap.smul_apply] using hc

/-- The adjoint variational inverse takes values in the actual physical H1 graph. -/
private noncomputable def c2m_physicalAdjointGraphResolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] c2m_physicalGraph d :=
  (c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin.symm.toContinuousLinearMap.adjoint.comp
    (c2m_physicalGraphEval (d := d) none).adjoint

private theorem c2m_physicalAdjointGraphResolvent_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c2m_physicalGraph d) :
    c2m_physicalShiftedForm a ha i ζ s v
      (c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs) =
      inner ℝ rhs (v.val none) := by
  let B := (c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin
  let S := c2m_physicalGraphEval (d := d) none
  rw [← (c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin_apply]
  rw [real_inner_comm]
  change inner ℝ (B.symm.toContinuousLinearMap.adjoint (S.adjoint rhs)) (B v) = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  change inner ℝ (S.adjoint rhs) (B.symm (B v)) = _
  rw [B.symm_apply_apply, S.adjoint_inner_left]
  rfl

private theorem c2m_physicalAdjointGraphResolvent_eval {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    (c2m_physicalResolvent a ha hΛ hA i ζ s hs).adjoint rhs =
      (c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs).val none := by
  let B := (c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs).continuousLinearEquivOfBilin
  let S := c2m_physicalGraphEval (d := d) none
  let Q := B.symm.toContinuousLinearMap
  apply ext_inner_right ℝ
  intro v
  calc
    inner ℝ ((c2m_physicalResolvent a ha hΛ hA i ζ s hs).adjoint rhs) v =
        inner ℝ rhs (c2m_physicalResolvent a ha hΛ hA i ζ s hs v) := by
      rw [c2m_physical_realInner, c2m_physical_realInner, ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℝ (S.adjoint rhs) (Q (S.adjoint v)) :=
      (S.adjoint_inner_left (Q (S.adjoint v)) rhs).symm
    _ = inner ℝ (Q.adjoint (S.adjoint rhs)) (S.adjoint v) :=
      (Q.adjoint_inner_left (S.adjoint v) (S.adjoint rhs)).symm
    _ = inner ℝ ((c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs).val none) v :=
      S.adjoint_inner_right (Q.adjoint (S.adjoint rhs)) v

private theorem c2m_physicalAdjointGraphResolvent_complex_spec {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (v : c2m_physicalGraph d) :
    c2m_physicalResolventExpression a ha i ζ s v
      (c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs) =
      inner ℂ rhs (v.val none) := by
  apply Complex.ext
  · have h := c2m_physicalAdjointGraphResolvent_spec a ha hΛ hA i ζ s hs rhs v
    rw [c2m_physicalShiftedForm_eq_re, c2m_physical_realInner] at h
    exact h
  · have h := c2m_physicalAdjointGraphResolvent_spec a ha hΛ hA i ζ s hs rhs
      (c2m_physicalGraphComplexSmul Complex.I v)
    rw [c2m_physicalShiftedForm_eq_re, c2m_physicalResolventExpression_smul,
      c2m_physical_realInner] at h
    change (Complex.I * c2m_physicalResolventExpression a ha i ζ s v _).re =
      (inner ℂ rhs (Complex.I • v.val none)).re at h
    rw [inner_smul_right] at h
    simpa only [Complex.I_mul_re, neg_neg] using congrArg Neg.neg h

/-- Conjugating the Hilbert adjoint inverse gives the physical bilinear transpose graph. -/
private theorem c2m_physicalTransposeResolvent_generator {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) :
    let R := c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs)
    IsPhysicalComplexTransposeGeneratorPair a i ζ (R rhs) ((s : ℂ) • R rhs - rhs) := by
  let u := c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs (star rhs)
  let w := c2m_physicalGraphStar u
  have he : c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs) rhs =
      w.val none := by
    rw [c2m_physicalBilinearTranspose_apply, c2m_physicalAdjointGraphResolvent_eval]
    rfl
  dsimp only
  rw [he]
  refine ⟨fun j => w.val (some j), w.property, ?_⟩
  intro v Gv hv
  let V : c2m_physicalGraph d := ⟨WithLp.toLp 2 (fun o => o.elim v Gv), hv⟩
  have ht := c2m_physicalAdjointGraphResolvent_complex_spec a ha hΛ hA i ζ s hs (star rhs) V
  change (s : ℂ) * inner ℂ (u.val none) v + ((1 / 2 : ℝ) : ℂ) *
      (∑ j, ∑ k, inner ℂ (u.val (some j)) (c2m_physicalCoefficientMul a ha j k (Gv k))) -
      inner ℂ (u.val none) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (Gv j)) =
      inner ℂ (star rhs) v at ht
  have hm (h : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℂ (u.val none) h = ∫ x, w.val none x * h x := by
    have hstar := c2m_physical_inner_star (star (u.val none)) h
    rw [star_star] at hstar
    exact hstar
  rw [hm, c2m_physical_inner_star, ← c2m_physical_energy_inner] at ht
  have hE : (∫ x, ∑ j, ∑ k, star (u.val (some j) x) * (a x j k : ℂ) * Gv k x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * w.val (some k) x * Gv j x := by
    apply integral_congr_ae
    have hgrad : ∀ᵐ x ∂volume, ∀ j, w.val (some j) x = star (u.val (some j) x) :=
      ae_all_iff.mpr fun j => Lp.coeFn_star _
    filter_upwards [hgrad] with x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx k]
    ring
  have hD : inner ℂ (u.val none) (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (Gv j)) =
      ζ * (∫ x, w.val none x * (∑ j, (a x j i : ℂ) * Gv j x)) := by
    have h := c2m_physical_drift_inner a ha i ζ (star (u.val none)) Gv
    rw [star_star] at h
    rw [h]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  rw [hE, hD] at ht
  have hL : (∫ x, ((s : ℂ) • w.val none - rhs : Lp ℂ 2 (volume : Measure (Vec d))) x * v x) =
      (s : ℂ) * (∫ x, w.val none x * v x) - ∫ x, rhs x * v x := by
    calc
      _ = ∫ x, (s : ℂ) * (w.val none x * v x) - rhs x * v x := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub ((s : ℂ) • w.val none) rhs,
          Lp.coeFn_smul (s : ℂ) (w.val none)] with x hx hy
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hx hy
        rw [hx, hy]
        ring
      _ = _ := by
        have h1 : Integrable (fun x => (s : ℂ) * (w.val none x * v x)) volume :=
          ((Lp.memLp (w.val none)).integrable_mul (Lp.memLp v)).const_mul _
        have h2 : Integrable (fun x => rhs x * v x) volume :=
          (Lp.memLp rhs).integrable_mul (Lp.memLp v)
        rw [integral_sub h1 h2, integral_const_mul]
  rw [hL]
  have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by norm_num
  rw [hhalf] at ht
  linear_combination ht

private theorem c2m_physicalAdjointGraphResolvent_unique {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    (rhs : Lp ℂ 2 (volume : Measure (Vec d))) (u : c2m_physicalGraph d)
    (hu : ∀ v, c2m_physicalResolventExpression a ha i ζ s v u =
      inner ℂ rhs (v.val none)) :
    u = c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs rhs := by
  let hB := c2m_physicalShiftedForm_isCoercive a ha hΛ hA i ζ s hs
  apply ext_inner_left ℝ
  intro v
  obtain ⟨w, rfl⟩ := hB.continuousLinearEquivOfBilin.surjective v
  rw [hB.continuousLinearEquivOfBilin_apply, hB.continuousLinearEquivOfBilin_apply,
    c2m_physicalShiftedForm_eq_re, hu, ← c2m_physical_realInner]
  exact (c2m_physicalAdjointGraphResolvent_spec a ha hΛ hA i ζ s hs rhs w).symm

private theorem c2m_physicalTransposeExpression {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (u v : c2m_physicalGraph d) :
    c2m_physicalResolventExpression a ha i ζ s v (c2m_physicalGraphStar u) =
      (s : ℂ) * (∫ x, u.val none x * v.val none x) +
      (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        (a x k j : ℂ) * u.val (some k) x * v.val (some j) x) -
      ζ * (∫ x, u.val none x * (∑ j, (a x j i : ℂ) * v.val (some j) x)) := by
  change (s : ℂ) * inner ℂ (star (u.val none)) (v.val none) + ((1 / 2 : ℝ) : ℂ) *
      (∑ j, ∑ k, inner ℂ (star (u.val (some j)))
        (c2m_physicalCoefficientMul a ha j k (v.val (some k)))) -
      inner ℂ (star (u.val none))
        (ζ • ∑ j, c2m_physicalCoefficientMul a ha j i (v.val (some j))) = _
  rw [c2m_physical_inner_star, ← c2m_physical_energy_inner, c2m_physical_drift_inner]
  have hE : (∫ x, ∑ j, ∑ k,
      star ((star (u.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x) *
        (a x j k : ℂ) * v.val (some k) x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * u.val (some k) x * v.val (some j) x := by
    apply integral_congr_ae
    have hgrad : ∀ᵐ x ∂volume, ∀ j,
        (star (u.val (some j)) : Lp ℂ 2 (volume : Measure (Vec d))) x =
          star (u.val (some j) x) := ae_all_iff.mpr fun j => Lp.coeFn_star _
    filter_upwards [hgrad] with x hx
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hx k, star_star]
    ring
  rw [hE]
  have hD : (∫ x, (∑ j, (a x j i : ℂ) * v.val (some j) x) * u.val none x) =
      ∫ x, u.val none x * (∑ j, (a x j i : ℂ) * v.val (some j) x) := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  rw [hD]
  norm_num

private theorem c2m_physicalTransposeGenerator_resolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    f = c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs) (s • f-g) := by
  rcases hfg with ⟨G, hG, hweak⟩
  let u : c2m_physicalGraph d := ⟨WithLp.toLp 2 (fun o => o.elim f G), hG⟩
  have hu : c2m_physicalGraphStar u =
      c2m_physicalAdjointGraphResolvent a ha hΛ hA i ζ s hs (star (s • f-g)) := by
    apply c2m_physicalAdjointGraphResolvent_unique a ha hΛ hA i ζ s hs
    intro v
    rw [c2m_physicalTransposeExpression]
    have ht := hweak (v.val none) (fun j => v.val (some j)) v.property
    change (∫ x, g x * v.val none x) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        (a x k j : ℂ) * G k x * v.val (some j) x) +
      ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * v.val (some j) x)) at ht
    change (s : ℂ) * (∫ x, f x * v.val none x) +
      (1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        (a x k j : ℂ) * G k x * v.val (some j) x) -
      ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * v.val (some j) x)) =
      inner ℂ (star (s • f-g)) (v.val none)
    have hsm : s • f = (s : ℂ) • f := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      congr 1 <;> norm_cast
    rw [hsm, c2m_physicalLp_star_sub, c2m_physicalLp_star_smul,
      inner_sub_left, inner_smul_left]
    simp only [starRingEnd_apply, star_star, c2m_physical_inner_star]
    linear_combination ht
  rw [c2m_physicalBilinearTranspose_apply, c2m_physicalAdjointGraphResolvent_eval, ← hu]
  change f = star (star f)
  exact (star_star f).symm

private theorem c2m_physicalAdjoint_real_inner {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    inner ℝ f (T.adjoint g) = inner ℝ (T f) g := by
  rw [c2m_physical_realInner, c2m_physical_realInner, T.adjoint_inner_right]

private theorem c2m_physicalAdjointEvolution_integral_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
    (∫ r in (0 : ℝ)..(t : ℝ), (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint
      (s • R.adjoint f - f)) =
      (c2m_physicalEvolution a ha hΛ hA i ζ t).adjoint (R.adjoint f) - R.adjoint f := by
  let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
  let T := c2m_physicalEvolution a ha hΛ hA i ζ
  let F (r : ℝ) := (T r.toNNReal).adjoint (s • R.adjoint f-f)
  have hF : Continuous F := (c2m_physicalEvolution_adjoint_continuous a ha hΛ hA i ζ _).comp
    continuous_real_toNNReal
  apply ext_inner_left ℝ
  intro v
  let G (r : ℝ) := T r.toNNReal (s • R v-v)
  have hG : Continuous G := (c2m_physicalEvolution_continuous a ha hΛ hA i ζ _).comp
    continuous_real_toNNReal
  have he (r : ℝ) : inner ℝ v (F r) = inner ℝ (G r) f := by
    change inner ℝ v ((T r.toNNReal).adjoint (s • R.adjoint f-f)) = _
    rw [c2m_physicalAdjoint_real_inner, inner_sub_right, real_inner_smul_right,
      c2m_physicalAdjoint_real_inner, ← real_inner_smul_left, ← inner_sub_left]
    congr 1
    change s • R (T r.toNNReal v) - T r.toNNReal v = T r.toNNReal (s • R v-v)
    rw [map_sub, ContinuousLinearMap.map_smul_of_tower]
    dsimp only [R, T]
    rw [c2m_physicalEvolution_resolvent]
  change inner ℝ v (∫ r in (0 : ℝ)..(t : ℝ), F r) =
    inner ℝ v ((T t).adjoint (R.adjoint f)-R.adjoint f)
  calc
    _ = ∫ r in (0 : ℝ)..(t : ℝ), inner ℝ v (F r) :=
      ((innerSL ℝ v).intervalIntegral_comp_comm (hF.intervalIntegrable 0 t)).symm
    _ = ∫ r in (0 : ℝ)..(t : ℝ), inner ℝ (G r) f := by
      apply intervalIntegral.integral_congr
      intro r hr
      exact he r
    _ = inner ℝ (∫ r in (0 : ℝ)..(t : ℝ), G r) f := by
      calc
        _ = ∫ r in (0 : ℝ)..(t : ℝ), inner ℝ f (G r) := by
          apply intervalIntegral.integral_congr
          intro r hr
          exact real_inner_comm _ _
        _ = inner ℝ f (∫ r in (0 : ℝ)..(t : ℝ), G r) :=
          (innerSL ℝ f).intervalIntegral_comp_comm (hG.intervalIntegrable 0 t)
        _ = _ := real_inner_comm _ _
    _ = inner ℝ (T t (R v)-R v) f := by
      have hgi : (∫ r in (0 : ℝ)..(t : ℝ), G r) = T t (R v)-R v :=
        c2m_physicalEvolution_integral_on_range a ha hΛ hA i ζ s hs v t
      rw [hgi]
    _ = _ := by
      rw [inner_sub_left, inner_sub_right, c2m_physicalAdjoint_real_inner,
        c2m_physicalAdjoint_real_inner, c2m_physicalAdjoint_real_inner]
      dsimp only [R, T]
      rw [c2m_physicalEvolution_resolvent]

private theorem c2m_physicalAdjointEvolution_hasDerivWithinAt_on_range {d : ℕ}
    (a : Vec d → Mat d) (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
    HasDerivWithinAt
      (fun r : ℝ => (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint (R.adjoint f))
      ((c2m_physicalEvolution a ha hΛ hA i ζ t).adjoint (s • R.adjoint f-f))
      (Set.Ici 0) (t : ℝ) := by
  let R := c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs
  let u := R.adjoint f
  let g := s • u-f
  let F (r : ℝ) := (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint g
  have hF : Continuous F := (c2m_physicalEvolution_adjoint_continuous a ha hΛ hA i ζ g).comp
    continuous_real_toNNReal
  have hi := (hF.integral_hasStrictDerivAt 0 (t : ℝ)).hasDerivAt
  have hd : HasDerivAt (fun r : ℝ => u + ∫ q in (0 : ℝ)..r, F q) (F t) (t : ℝ) := by
    simpa only [zero_add] using! (hasDerivAt_const (t : ℝ) u).add hi
  have hd' := hd.hasDerivWithinAt (s := Set.Ici 0)
  have hh : HasDerivWithinAt
      (fun r : ℝ => (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint u)
      (F t) (Set.Ici 0) (t : ℝ) := by
    apply hd'.congr_of_mem ?_ t.property
    intro r hr
    have he := c2m_physicalAdjointEvolution_integral_on_range a ha hΛ hA i ζ s hs f r.toNNReal
    rw [Real.coe_toNNReal r hr] at he
    change (∫ q in (0 : ℝ)..r, F q) =
      (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint u-u at he
    rw [he]
    abel
  simpa only [F, Real.toNNReal_coe] using hh

private theorem c2m_physicalUnshiftedAdjointEvolution_derivative_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    HasDerivWithinAt
      (fun r : ℝ => (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ r.toNNReal).adjoint
        ((c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f))
      (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) •
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f - f) (Set.Ici 0) 0 := by
  let w : ℝ := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let u := (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f
  have hc : HasDerivAt (fun r : ℝ => Real.exp (w * r)) w 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul w).exp
  have hd := c2m_physicalAdjointEvolution_hasDerivWithinAt_on_range a ha hΛ hA i ζ s hs f 0
  have hh := hc.hasDerivWithinAt.smul hd
  simp only [NNReal.coe_zero, Real.toNNReal_zero, mul_zero, Real.exp_zero,
    c2m_physicalEvolution_zero, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, one_smul] at hh
  have he : (s • u - f) + w • u = (w+s) • u - f := by
    rw [add_smul]
    abel
  change HasDerivWithinAt _ ((s • u - f) + w • u) (Set.Ici 0) 0 at hh
  rw [he] at hh
  apply hh.congr_of_mem ?_ (by simp)
  intro r hr
  change (Real.exp (w * (r.toNNReal : ℝ)) • c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint u =
    Real.exp (w * r) • (c2m_physicalEvolution a ha hΛ hA i ζ r.toNNReal).adjoint u
  rw [c2m_physicalAdjoint_real_smul, ContinuousLinearMap.smul_apply]
  rw [Real.coe_toNNReal r hr]

private theorem c2m_physicalUnshiftedAdjointEvolution_quotient_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      ((c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t).adjoint
        ((c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f) -
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) •
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f - f)) := by
  let u := (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).adjoint f
  let g := ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) • u - f
  have hd : HasDerivWithinAt
      (fun r : ℝ => (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ r.toNNReal).adjoint u)
      g (Set.Ici 0) 0 :=
    c2m_physicalUnshiftedAdjointEvolution_derivative_on_range a ha hΛ hA i ζ s hs f
  have ht := c2m_tendsto_quotient_of_hasDerivWithinAt (d := d)
    (fun t => (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t).adjoint u) g hd
  have hz : (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ 0).adjoint u = u := by
    rw [c2m_physicalUnshiftedEvolution_zero, ContinuousLinearMap.adjoint_id]
    rfl
  change Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
    ((c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t).adjoint u -
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ 0).adjoint u)) (𝓝[>] (0 : ℝ≥0)) (𝓝 g) at ht
  rw [hz] at ht
  exact ht

private theorem c2m_physicalLp_star_real_smul {d : ℕ} (r : ℝ)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) : star (r • f) = r • star f := by
  have he (g : Lp ℂ 2 (volume : Measure (Vec d))) : r • g = (r : ℂ) • g := by
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    congr 1 <;> norm_cast
  rw [he, c2m_physicalLp_star_smul]
  simpa only [Complex.star_def, Complex.conj_ofReal] using (he (star f)).symm

private theorem c2m_physicalTransposeEvolution_quotient_on_range {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    let R := c2m_physicalBilinearTranspose (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs)
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t (R f) - R f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + s) • R f - f)) := by
  have ht := c2m_physicalUnshiftedAdjointEvolution_quotient_on_range a ha hΛ hA i ζ s hs (star f)
  have h := (c2m_physicalLp_star_continuous.tendsto _).comp ht
  have hc (t : ℝ≥0) : star (((t : ℝ) : ℂ)⁻¹) = (((t : ℝ) : ℂ)⁻¹) := by
    change (starRingEnd ℂ) (((t : ℝ) : ℂ)⁻¹) = _
    rw [map_inv₀]
    exact congrArg (fun z : ℂ => z⁻¹) (Complex.conj_ofReal (t : ℝ))
  simp only [Function.comp_def, c2m_physicalLp_star_smul, hc,
    c2m_physicalLp_star_sub, c2m_physicalLp_star_real_smul, star_star] at h
  simpa only [c2m_physicalTransposeEvolution, c2m_physicalBilinearTranspose_apply,
    star_star] using h

private theorem c2m_physicalTransposeEvolution_resolvent {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (s : ℝ) (hs : 0 < s) (t : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    let R := c2m_physicalBilinearTranspose (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs)
    R (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t f) =
      c2m_physicalTransposeEvolution a ha hΛ hA i ζ t (R f) := by
  have he :
      (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs).comp
        (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t) =
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ t).comp
        (c2m_physicalShiftedResolvent a ha hΛ hA i ζ s hs) := by
    apply ContinuousLinearMap.ext
    intro g
    exact c2m_physicalUnshiftedEvolution_resolvent a ha hΛ hA i ζ s hs t g
  have hh := congrArg c2m_physicalBilinearTranspose he
  simp only [c2m_physicalBilinearTranspose_comp] at hh
  exact congrArg (fun T => T f) hh.symm

private theorem c2m_physicalTransposeEvolution_generator_iff {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsPhysicalComplexTransposeGeneratorPair a i ζ f g := by
  let s : ℝ := (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 + 1
  have hs : (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 < s := by dsimp [s]; linarith
  let R := c2m_physicalBilinearTranspose (c2m_physicalShiftedResolvent a ha hΛ hA i ζ 1 (by norm_num))
  have hR : R = c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs) := rfl
  have hrange (u : Lp ℂ 2 (volume : Measure (Vec d))) :
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ •
        (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t (R u) - R u))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (s • R u - u)) :=
    c2m_physicalTransposeEvolution_quotient_on_range a ha hΛ hA i ζ 1 (by norm_num) u
  constructor
  · intro h
    have hh := (R.continuous.tendsto g).comp h
    have he (t : ℝ≥0) : R (((t : ℝ) : ℂ)⁻¹ •
        (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t f - f)) =
        ((t : ℝ) : ℂ)⁻¹ • (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t (R f) - R f) := by
      rw [map_smul, map_sub]
      rw [c2m_physicalTransposeEvolution_resolvent]
    change Tendsto (fun t : ℝ≥0 => R (((t : ℝ) : ℂ)⁻¹ •
      (c2m_physicalTransposeEvolution a ha hΛ hA i ζ t f-f))) (𝓝[>] (0 : ℝ≥0)) (𝓝 (R g)) at hh
    simp only [he] at hh
    have hg : R g = s • R f-f := tendsto_nhds_unique hh (hrange f)
    have hf : f = R (s • f-g) := by
      rw [map_sub, R.map_smul_of_tower, hg]
      abel
    have hw := c2m_physicalTransposeResolvent_generator a ha hΛ hA i ζ s hs (s • f-g)
    change IsPhysicalComplexTransposeGeneratorPair a i ζ
      (c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs) (s • f-g))
      ((s : ℂ) • c2m_physicalBilinearTranspose (c2m_physicalResolvent a ha hΛ hA i ζ s hs) (s • f-g) - (s • f-g)) at hw
    rw [← hR, ← hf] at hw
    have hsm : (s : ℂ) • f = s • f := by
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      congr 1 <;> norm_cast
    rw [hsm] at hw
    simpa only [sub_sub_cancel] using hw
  · intro h
    have hf : f = R (s • f-g) := by
      rw [hR]
      exact c2m_physicalTransposeGenerator_resolvent a ha hΛ hA i ζ s hs h
    have hh := hrange (s • f-g)
    rw [← hf] at hh
    simpa only [sub_sub_cancel] using hh

private theorem c2m_physicalTransposeEvolution_isSemigroup {d : ℕ} (a : Vec d → Mat d)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume) {Λ : ℝ}
    (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ) (i : Fin d) (ζ : ℂ) :
    IsPhysicalComplexTransposeSemigroup a i ζ
      (c2m_physicalUnshiftedEvolution a ha hΛ hA i ζ)
      (c2m_physicalTransposeEvolution a ha hΛ hA i ζ) := by
  refine ⟨c2m_physicalTransposeEvolution_zero a ha hΛ hA i ζ,
    c2m_physicalTransposeEvolution_add a ha hΛ hA i ζ,
    c2m_physicalTransposeEvolution_continuous a ha hΛ hA i ζ,
    c2m_physicalTransposeEvolution_generator_iff a ha hΛ hA i ζ, ?_⟩
  intro t f g
  exact c2m_physicalBilinearTranspose_pairing _ f g

theorem retained_physical_complex_measurable_evolution :
∀ {Ω : Type*} [MeasurableSpace Ω] (d : ℕ) (i : Fin d) (ζ : ℂ)
    (Λ : ℝ), 1 ≤ Λ →
    ∀ (a : Ω → Vec d → Mat d),
    Measurable (fun s : Ω × Vec d => a s.1 s.2) →
    (∀ ω x, S5Elliptic (a ω x) Λ) →
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    ∃ P Pdag : Ω → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ ω, IsPhysicalComplexSemigroup (a ω) i ζ (P ω) ∧
        IsPhysicalComplexTransposeSemigroup (a ω) i ζ (P ω) (Pdag ω)) ∧
      (∀ (t : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))),
        Measurable (fun ω => P ω t f) ∧ Measurable (fun ω => Pdag ω t f)) := by
  intro Ω _ d i ζ Λ hΛ a ha hA
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  have hΛ' : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let hb := c2m_coefficient_memLp a ha Λ hA
  refine ⟨(fun ω => c2m_physicalUnshiftedEvolution (a ω) (hb ω) hΛ'
      (Filter.Eventually.of_forall (hA ω)) i ζ),
    (fun ω => c2m_physicalTransposeEvolution (a ω) (hb ω) hΛ'
      (Filter.Eventually.of_forall (hA ω)) i ζ), ?_, ?_⟩
  · intro ω
    exact ⟨c2m_physicalUnshiftedEvolution_isSemigroup _ _ _ _ _ _,
      c2m_physicalTransposeEvolution_isSemigroup _ _ _ _ _ _⟩
  · intro t f
    exact ⟨c2m_measurable_physicalUnshiftedEvolution a ha hb hΛ' hA i ζ t f,
      c2m_measurable_physicalTransposeEvolution a ha hb hΛ' hA i ζ t f⟩

-- Transitive dependency audits of every owned declaration.
#print axioms c2m_measurable_coefficient_pairing
#print axioms c2m_entry_bound
#print axioms c2m_coefficient_memLp
#print axioms c2m_measurable_shifted_form
#print axioms c2m_measurable_of_inner
#print axioms c2m_physicalCoefficientMul
#print axioms c2m_physicalCoefficientMul_coe
#print axioms c2m_physicalCoefficientMul_bound
#print axioms c2m_measurable_coefficient_action
#print axioms c2m_measurable_fixedPoint
#print axioms c2m_uniform_richardson_step
#print axioms c2m_measurable_linear_solution
#print axioms c2m_measurable_coercive_solution
#print axioms c2m_measurable_variational_solution
#print axioms c2m_weakPartial_smul
#print axioms c2m_physicalGraph
#print axioms c2m_physicalGraph_closed
#print axioms c2m_physicalGraph_norm_sq
#print axioms c2m_physicalGraphEval
#print axioms c2m_physical_energy_lowerBound
#print axioms c2m_physicalShiftedForm
#print axioms c2m_physicalShiftedForm_apply
#print axioms c2m_measurable_physicalShiftedForm
#print axioms c2m_physicalShiftedForm_bound
#print axioms c2m_physical_drift_absorption
#print axioms c2m_physicalShiftedForm_coercive
#print axioms c2m_physicalShiftedForm_isCoercive
#print axioms c2m_physicalGraphResolvent
#print axioms c2m_measurable_physical_variational_solution
#print axioms c2m_measurable_physicalGraphResolvent
#print axioms c2m_physicalGraphResolvent_spec
#print axioms c2m_physicalGraphComplexSmul
#print axioms c2m_physicalGraphStar
#print axioms c2m_physicalResolventExpression
#print axioms c2m_physical_realInner
#print axioms c2m_physicalShiftedForm_eq_re
#print axioms c2m_physicalResolventExpression_I
#print axioms c2m_physicalGraphResolvent_complex_spec
#print axioms c2m_physicalGraphResolvent_unique
#print axioms c2m_physicalResolventExpression_smul
#print axioms c2m_physicalGraphResolvent_smul
#print axioms c2m_physicalResolvent
#print axioms c2m_measurable_physicalResolvent
#print axioms c2m_physicalResolvent_bound
#print axioms c2m_physicalGraphResolvent_unique_real
#print axioms c2m_physicalShiftedForm_shift
#print axioms c2m_physicalResolvent_identity
#print axioms c2m_physicalShiftedResolvent
#print axioms c2m_physicalShiftedResolvent_bound
#print axioms c2m_physicalYosida
#print axioms c2m_physicalYosida_dissipative
#print axioms c2m_physicalYosidaEvolution
#print axioms c2m_physicalYosidaEvolution_hasDerivAt
#print axioms c2m_physicalYosidaEvolution_bound
#print axioms c2m_physicalResolvent_commute
#print axioms c2m_physicalShiftedResolvent_commute
#print axioms c2m_physicalYosida_commute
#print axioms c2m_physicalYosida_commute_evolution
#print axioms c2m_physicalYosidaEvolution_add
#print axioms c2m_physicalYosidaEvolution_continuous
#print axioms c2m_physicalYosidaEvolution_zero
#print axioms c2m_physicalYosidaEvolution_comparison_hasDerivAt
#print axioms c2m_physicalYosidaEvolution_comparison
#print axioms c2m_physicalSchwartzGraph
#print axioms c2m_physicalGraphEval_denseRange
#print axioms c2m_physicalResolvent_denseRange
#print axioms c2m_physicalShiftedResolvent_denseRange
#print axioms c2m_physicalShiftedResolvent_identity
#print axioms c2m_physicalShiftedResolvent_normalized_bound
#print axioms c2m_physicalShiftedResolvent_range_error
#print axioms c2m_physicalShiftedResolvent_tendsto_on_range
#print axioms c2m_physicalShiftedResolvent_tendsto
#print axioms c2m_physicalYosida_tendsto_on_range
#print axioms c2m_physicalYosidaEvolution_cauchy_on_range
#print axioms c2m_physicalYosidaEvolution_cauchy
#print axioms c2m_physicalEvolutionLimit
#print axioms c2m_physicalEvolutionLimit_tendsto
#print axioms c2m_physicalEvolutionLimit_bound
#print axioms c2m_physicalEvolution
#print axioms c2m_physicalEvolution_tendsto
#print axioms c2m_physicalEvolution_bound
#print axioms c2m_physicalEvolution_tendsto_apply
#print axioms c2m_physicalEvolution_zero
#print axioms c2m_physicalEvolution_add
#print axioms c2m_physicalYosidaEvolution_hasDerivAt_right
#print axioms c2m_physicalYosidaEvolution_increment
#print axioms c2m_physicalEvolution_increment_on_range
#print axioms c2m_physicalEvolution_increment_between
#print axioms c2m_physicalEvolution_lipschitz_on_range
#print axioms c2m_physicalEvolution_continuous
#print axioms c2m_measurable_operator_apply
#print axioms c2m_measurable_operator_exp_apply
#print axioms c2m_measurable_physicalEvolution
#print axioms c2m_physical_energy_inner
#print axioms c2m_physical_inner_star
#print axioms c2m_physical_drift_inner
#print axioms c2m_physicalGraphResolvent_generator
#print axioms c2m_physicalShiftedResolvent_commute_evolution
#print axioms c2m_commute_apply
#print axioms c2m_physicalEvolution_resolvent
#print axioms c2m_physicalEvolution_integral_on_range
#print axioms c2m_physicalEvolution_hasDerivWithinAt_on_range
#print axioms c2m_physicalGenerator_resolvent
#print axioms c2m_tendsto_quotient_of_hasDerivWithinAt
#print axioms c2m_physicalUnshiftedEvolution
#print axioms c2m_physicalUnshiftedEvolution_zero
#print axioms c2m_physicalUnshiftedEvolution_add
#print axioms c2m_physicalUnshiftedEvolution_continuous
#print axioms c2m_physicalUnshiftedEvolution_derivative_on_range
#print axioms c2m_physicalUnshiftedEvolution_quotient_on_range
#print axioms c2m_physicalUnshiftedEvolution_resolvent
#print axioms c2m_physicalUnshiftedEvolution_generator_iff
#print axioms c2m_physicalUnshiftedEvolution_isSemigroup
#print axioms c2m_measurable_physicalUnshiftedEvolution
#print axioms c2m_physicalLp_star_add
#print axioms c2m_physicalLp_star_smul
#print axioms c2m_physicalLp_norm_star
#print axioms c2m_physicalBilinearTranspose
#print axioms c2m_physicalBilinearTranspose_apply
#print axioms c2m_physicalBilinearTranspose_id
#print axioms c2m_physicalBilinearTranspose_comp
#print axioms c2m_physical_inner_star_right
#print axioms c2m_physicalBilinearTranspose_pairing
#print axioms c2m_measurable_physicalBilinearTranspose_action
#print axioms c2m_physicalTransposeEvolution
#print axioms c2m_physicalTransposeEvolution_zero
#print axioms c2m_physicalTransposeEvolution_add
#print axioms c2m_measurable_physicalTransposeEvolution
#print axioms c2m_adjoint_continuousAt_zero
#print axioms c2m_contractSemigroup_continuous_of_zero
#print axioms c2m_physicalLp_star_sub
#print axioms c2m_physicalLp_star_continuous
#print axioms c2m_physicalEvolution_adjoint_continuous
#print axioms c2m_physicalAdjoint_real_smul
#print axioms c2m_physicalTransposeEvolution_continuous
#print axioms c2m_physicalAdjointGraphResolvent
#print axioms c2m_physicalAdjointGraphResolvent_spec
#print axioms c2m_physicalAdjointGraphResolvent_eval
#print axioms c2m_physicalAdjointGraphResolvent_complex_spec
#print axioms c2m_physicalTransposeResolvent_generator
#print axioms c2m_physicalAdjointGraphResolvent_unique
#print axioms c2m_physicalTransposeExpression
#print axioms c2m_physicalTransposeGenerator_resolvent
#print axioms c2m_physicalAdjoint_real_inner
#print axioms c2m_physicalAdjointEvolution_integral_on_range
#print axioms c2m_physicalAdjointEvolution_hasDerivWithinAt_on_range
#print axioms c2m_physicalUnshiftedAdjointEvolution_derivative_on_range
#print axioms c2m_physicalUnshiftedAdjointEvolution_quotient_on_range
#print axioms c2m_physicalLp_star_real_smul
#print axioms c2m_physicalTransposeEvolution_quotient_on_range
#print axioms c2m_physicalTransposeEvolution_resolvent
#print axioms c2m_physicalTransposeEvolution_generator_iff
#print axioms c2m_physicalTransposeEvolution_isSemigroup
#print axioms retained_physical_complex_measurable_evolution

end EinsteinFull.Blueprint
