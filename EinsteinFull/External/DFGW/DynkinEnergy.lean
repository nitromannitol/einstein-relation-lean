import EinsteinFull.External.DFGW.DynkinOrthogonality
import EinsteinFull.External.DFGW.GeneratorEnergy

/-! # Energy of Dynkin martingale increments

The variance rate of a Dynkin martingale increment is twice the Dirichlet energy of its
observable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The mean square of a Dynkin increment is twice elapsed time times generator energy. -/
theorem integral_dynkin_increment_sq_eq_energy (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hcoord : Draft.dfgwCoordSigma (S := S) Set.univ =
      Draft.dfgwTrajectoryMeasurableSpace (S := S))
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    (∫ η, (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2 ∂P) =
      (t : ℝ) * (2 * -inner ℝ (f : Lp ℝ 2 μ) ((transitionSemigroup hP).generator f)) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let F : Lp ℝ 2 μ := f
  let g := (transitionSemigroup hP).generator f
  let K : ℝ := ∫ x, g x ^ 2 ∂μ
  let V : ℝ := ∫ η, (dynkinProcess hP f 1 η - dynkinProcess hP f 0 η) ^ 2 ∂P
  let R : ℕ → ℝ := fun n => (n : ℝ) *
    ∫ η, (∫ u in (0 : ℝ)..((n : ℝ≥0)⁻¹ : ℝ≥0), g (η u)) ^ 2 ∂P
  have hinv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hR : Tendsto R atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n => by
      dsimp only [R]
      positivity) ?_ (by simpa using hinv.mul_const K)
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hbound := (time_integral_memLp_and_sq_le hP g (Lp.memLp g)
      ((n : ℝ≥0)⁻¹).coe_nonneg).2
    change (∫ η, (∫ u in (0 : ℝ)..((n : ℝ≥0)⁻¹ : ℝ≥0), g (η u)) ^ 2 ∂P) ≤
      ((n : ℝ≥0)⁻¹ : ℝ) ^ 2 * K at hbound
    have hm := mul_le_mul_of_nonneg_left hbound hnR.le
    dsimp only [R]
    simp only [NNReal.coe_inv, NNReal.coe_natCast] at hm
    calc
      _ ≤ (n : ℝ) * ((n : ℝ)⁻¹ ^ 2 * K) := hm
      _ = (n : ℝ)⁻¹ * K := by field_simp
  have hgen := tendsto_generator_energy hP F f.property
  have hdomain : (⟨F, f.property⟩ : (transitionSemigroup hP).generatorDomain) = f :=
    Subtype.ext rfl
  rw [hdomain] at hgen
  have hsum : Tendsto (fun n : ℕ => 2 * ((n : ℝ) * (‖F‖ ^ 2 -
      inner ℝ F (transitionOperator hP ((n : ℝ≥0)⁻¹) F))) + R n) atTop
      (𝓝 (2 * -inner ℝ F g)) := by
    convert (hgen.const_mul 2).add hR using 1; simp [g]
  have hconst : ∀ᶠ n : ℕ in atTop, 2 * ((n : ℝ) * (‖F‖ ^ 2 -
      inner ℝ F (transitionOperator hP ((n : ℝ≥0)⁻¹) F))) + R n = V := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have he := integral_dynkin_increment_sq_eq_energy_add hP f ((n : ℝ≥0)⁻¹)
    have hl := integral_dynkin_increment_sq_eq_mul hP hcoord f ((n : ℝ≥0)⁻¹)
    simp only [NNReal.coe_inv, NNReal.coe_natCast] at hl
    have he' : (n : ℝ)⁻¹ * V = 2 * (‖F‖ ^ 2 -
        inner ℝ F (transitionOperator hP ((n : ℝ≥0)⁻¹) F)) +
      ∫ η, (∫ u in (0 : ℝ)..((n : ℝ≥0)⁻¹ : ℝ≥0), g (η u)) ^ 2 ∂P := hl.symm.trans he
    dsimp only [R]
    have hmul := congrArg (fun x : ℝ => (n : ℝ) * x) he'
    rw [← mul_assoc, mul_inv_cancel₀ hnR, one_mul] at hmul
    nlinarith
  have hconstlim : Tendsto (fun _ : ℕ => V) atTop (𝓝 (2 * -inner ℝ F g)) :=
    hsum.congr' hconst
  have hV : V = 2 * -inner ℝ F g := tendsto_nhds_unique tendsto_const_nhds hconstlim
  rw [integral_dynkin_increment_sq_eq_mul hP hcoord f t]
  exact congrArg ((t : ℝ) * ·) hV

end EinsteinFull.External.DFGW
