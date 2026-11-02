import EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinRelation.Correctors.HeatKernelConvolution
import Mathlib.Tactic
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
/-- Nonnegativity, a uniform quadratic bound, and exact strict upper cuts for Gaussian J₁. -/
theorem coarse_gaussianEnergyJ1_bounds_upperCuts :
    ∀ {d : ℕ} {K : ℝ} (a : Coefficient d K) (z : Vec d) (r : ℝ),
      0 < r → ∀ p q : Vec d,
      0 ≤ gaussianEnergyJ1 a z r p q ∧
      gaussianEnergyJ1 a z r p q ≤ K * euclideanSq p + euclideanSq q ∧
      ∀ t : ℝ, t < gaussianEnergyJ1 a z r p q ↔
        ∃ w : SubquadraticHarmonic a, t < ∫ x, heatKernel z r x *
          (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
            dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)) := by
  intro d K a z r hr p q
  have hgeneral (mask : Vec d → ℝ) (hm : Integrable mask)
      (hpos : ∀ x, 0 ≤ mask x) (p q : Vec d) : 0 ≤ energyJ1 a mask p q ∧
    energyJ1 a mask p q ≤ (∫ x, mask x) * (K * euclideanSq p + euclideanSq q) ∧
    ∀ t : ℝ, t < energyJ1 a mask p q ↔
    ∃ w : SubquadraticHarmonic a, t < ∫ x, mask x *
      (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
        dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)) := by
    have hsq (v : Vec d) : 0 ≤ euclideanSq v := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hbound (x : Vec d) (g : Vec d) :
        -(1 / 2 : ℝ) * dot g ((a x).mulVec g) -
          dot p ((a x).mulVec g) + dot q g ≤ K * euclideanSq p + euclideanSq q := by
      have hsym : dot g ((a x).mulVec p) = dot p ((a x).mulVec g) := by
        change dotProduct g ((a x).mulVec p) = dotProduct p ((a x).mulVec g)
        rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, a.symmetric x]
        exact dotProduct_comm _ _
      have he : dot (g + (2 : ℝ) • p) ((a x).mulVec (g + (2 : ℝ) • p)) =
          dot g ((a x).mulVec g) + 4 * dot p ((a x).mulVec g) +
            4 * dot p ((a x).mulVec p) := by
        change dotProduct _ _ = dotProduct _ _ + 4 * dotProduct _ _ +
          4 * dotProduct _ _
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct,
          dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
        change dot g ((a x).mulVec g) + 2 * dot p ((a x).mulVec g) +
          2 * (dot g ((a x).mulVec p) + 2 * dot p ((a x).mulVec p)) =
          dot g ((a x).mulVec g) + 4 * dot p ((a x).mulVec g) +
            4 * dot p ((a x).mulVec p)
        rw [hsym]
        ring
      have hp := (a.elliptic x (g + (2 : ℝ) • p)).1
      rw [he] at hp
      have hE : 0 ≤ dot g ((a x).mulVec g) + 4 * dot p ((a x).mulVec g) +
          4 * dot p ((a x).mulVec p) := (hsq _).trans hp
      have heq : euclideanSq (g - (2 : ℝ) • q) =
          euclideanSq g - 4 * dot q g + 4 * euclideanSq q := by
        change dotProduct _ _ = dotProduct _ _ - 4 * dotProduct _ _ +
          4 * dotProduct _ _
        simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct,
          dotProduct_smul, smul_eq_mul]
        rw [dotProduct_comm g q]
        ring
      have hQ := hsq (g - (2 : ℝ) • q)
      rw [heq] at hQ
      linarith [(a.elliptic x g).1, (a.elliptic x p).2]
    have hC : 0 ≤ K * euclideanSq p + euclideanSq q := by
      have := (hsq p).trans ((a.elliptic 0 p).1.trans (a.elliptic 0 p).2)
      linarith [hsq q]
    have hvalues : ∀ e ∈ {e : ℝ | ∃ w : SubquadraticHarmonic a,
        e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))},
        e ≤ ∫ x, mask x * (K * euclideanSq p + euclideanSq q) := by
      rintro e ⟨w, rfl⟩
      by_cases hi : Integrable (fun x => mask x *
          (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
            dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)))
      · exact integral_mono hi (hm.mul_const _) fun x =>
          mul_le_mul_of_nonneg_left (hbound x (w.grad x)) (hpos x)
      · rw [integral_undef hi]
        exact integral_nonneg fun x => mul_nonneg (hpos x) hC
    have hbounded : BddAbove {e : ℝ | ∃ w : SubquadraticHarmonic a,
        e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))} := ⟨_, hvalues⟩
    let hz : SubquadraticHarmonic a := {
      potential := fun _ => 0
      grad := fun _ => 0
      weak_gradient := by
        intro i
        refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
        intro φ _hφ
        simp
      local_energy := by
        intro R _hR
        simp [euclideanNorm, euclideanSq, dot]
      harmonic := by simpa only [Matrix.mulVec_zero] using hasWeakDivergence_zero (d := d) Set.univ
      growth := by simp }
    have hmem : (0 : ℝ) ∈ {e : ℝ | ∃ w : SubquadraticHarmonic a,
        e = ∫ x, mask x * (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))} := by
      refine ⟨hz, ?_⟩
      simp [hz, dot]
    refine ⟨le_csSup hbounded hmem, ?_, ?_⟩
    · exact (csSup_le ⟨_, hmem⟩ hvalues).trans_eq (integral_mul_const _ _)
    intro t
    rw [energyJ1, lt_csSup_iff hbounded ⟨_, hz, rfl⟩]
    constructor
    · rintro ⟨e, ⟨w, rfl⟩, ht⟩
      exact ⟨w, ht⟩
    · rintro ⟨w, hw⟩
      exact ⟨_, ⟨w, rfl⟩, hw⟩
  have hi : Integrable (heatKernel (d := d) z r) :=
    (Correctors.integrable_euclideanHeatKernel (sq_pos_of_pos hr)).comp_sub_right z
  have hn : ∀ x, 0 ≤ heatKernel z r x := fun x =>
    Correctors.euclideanHeatKernel_nonneg (sq_nonneg r) (x - z)
  have hmass : ∫ x, heatKernel (d := d) z r x = 1 := by
    unfold heatKernel
    rw [integral_sub_right_eq_self, Correctors.integral_euclideanHeatKernel (sq_pos_of_pos hr)]
  simpa only [gaussianEnergyJ1, hmass, one_mul] using hgeneral _ hi hn p q

-- Check the supervisor contract independently of the exported proof.
example :
    ∀ {d : ℕ} {K : ℝ} (a : Coefficient d K) (z : Vec d) (r : ℝ),
      0 < r → ∀ p q : Vec d,
      0 ≤ gaussianEnergyJ1 a z r p q ∧
      gaussianEnergyJ1 a z r p q ≤ K * euclideanSq p + euclideanSq q ∧
      ∀ t : ℝ, t < gaussianEnergyJ1 a z r p q ↔
        ∃ w : SubquadraticHarmonic a, t < ∫ x, heatKernel z r x *
          (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
            dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x)) :=
  coarse_gaussianEnergyJ1_bounds_upperCuts

#print axioms coarse_gaussianEnergyJ1_bounds_upperCuts
#lint

-- Audit every local declaration, including automatically generated proof helpers.
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  Lean.logInfo m!"Standard-axiom audit passed for all {count} local declarations."
end EinsteinFull.Blueprint
