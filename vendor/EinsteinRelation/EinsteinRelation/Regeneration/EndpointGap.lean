import EinsteinRelation.Regeneration.ForcedBitGeometry
import EinsteinRelation.Regeneration.Coupling
import EinsteinRelation.Regeneration.HalfSpaces

/-! # Endpoint gap and past barrier on the forced last-bit event

Source `paper/main.tex:353–374`, with the displayed `regen.gap` at lines 373–374.
On the explicit prestart event `forcedBitTrialEvent`, every endpoint `y` of the
coupling ball `endpointBall` at time `mΔ` lies at least `7R` above the actual
running maximum of the path plus its starting coordinate. The proof uses only the
coordinate bound `|x i| ≤ euclideanNorm x`, the geometry of the forced event, and
the finite-maximum displacement bound. No origin-zero premise is assumed.

The measurability statement uses the exact finite-history sigma-algebra: the
evaluation at the grid time `mΔ` is measurable for it, and the endpoint-ball event
is the preimage of an open set under a continuous function of that evaluation.
-/

open MeasureTheory
open scoped NNReal ENNReal BigOperators

namespace EinsteinRelation.Regeneration

/-- The Euclidean norm is continuous on the coordinate space. -/
private theorem continuous_euclideanNorm_vec {d : ℕ} :
    Continuous (fun v : Vec d => euclideanNorm v) := by
  have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) := by
    apply continuous_finset_sum
    intro j _
    exact (continuous_apply j).mul (continuous_apply j)
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp hsum

/-- The Euclidean distance from `y` to the shifted endpoint centre is continuous in the
base point `x`; this gives the open endpoint-ball condition. -/
private theorem continuous_endpointDistance {d : ℕ} (y : Vec d) (i : Fin d) (R : ℝ) :
    Continuous (fun x : Vec d => euclideanNorm (y - (x + (9 * R) • unitVector i))) := by
  have hc : Continuous (fun x : Vec d => y - (x + (9 * R) • unitVector i)) :=
    continuous_const.sub (continuous_id.add continuous_const)
  exact continuous_euclideanNorm_vec.comp hc

/-- The path coordinate at the grid time `mΔ` is measurable for the exact finite-history
sigma-algebra, since that time lies in the closed window `[0, mΔ]`. -/
private theorem measurable_eval_gridTime {d : ℕ} (Δ : ℝ≥0) (m : ℕ) :
    @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ m) inferInstance
      (fun z : CoupledSample d => z.1 ((m : ℝ≥0) * Δ)) := by
  apply Measurable.of_comap_le
  exact le_sup_of_le_left (le_iSup_of_le ⟨(m : ℝ≥0) * Δ, zero_le, le_rfl⟩ le_rfl)

/-- Source `regen.gap` (`paper/main.tex:373–374`) on the forced prestart event: the
actual running maximum up to `mΔ`, shifted by the starting coordinate, lies below
`y i - 7R` for every endpoint `y` of the ball at `z (mΔ)`. -/
theorem forcedBitTrialEvent_endpoint_gap {d : ℕ} (Δ : ℝ≥0) (_hΔ : 0 < Δ) (lam R : ℝ)
    (_hlam : 0 < lam) (_hR : 0 < R) (i : Fin d) (m : ℕ)
    (z : CoupledSample d) (_hz : z ∈ forcedBitTrialEvent Δ lam R i m)
    (y : Vec d) (_hy : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))) :
    coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) + z.1 0 i ≤ y i - 7 * R := by
  obtain ⟨hmax, _⟩ := forcedBitTrialEvent_geometry Δ _hΔ lam R _hlam _hR i m z _hz
  have hball : euclideanNorm (y - (z.1 ((m : ℝ≥0) * Δ) + (9 * R) • unitVector i)) < R := _hy
  have hcoord := coordinate_abs_le_euclideanNorm
    (y - (z.1 ((m : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i
  have habs : |(y - (z.1 ((m : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i| < R :=
    lt_of_le_of_lt hcoord hball
  have hlow := (abs_lt.mp habs).1
  have hshift : (y - (z.1 ((m : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i =
      y i - (z.1 ((m : ℝ≥0) * Δ) i + 9 * R) := by
    simp [unitVector]
  linarith

/-- Source `regen.gap` past barrier: every earlier time `t ≤ mΔ` of the path lies
below `y i - 7R`, for every endpoint `y` of the ball at `z (mΔ)`. -/
theorem forcedBitTrialEvent_endpoint_past_barrier {d : ℕ} (Δ : ℝ≥0) (_hΔ : 0 < Δ)
    (lam R : ℝ) (_hlam : 0 < lam) (_hR : 0 < R) (i : Fin d) (m : ℕ)
    (z : CoupledSample d) (_hz : z ∈ forcedBitTrialEvent Δ lam R i m)
    (y : Vec d) (_hy : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))) :
    ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R := by
  intro t ht
  have hgap := forcedBitTrialEvent_endpoint_gap Δ _hΔ lam R _hlam _hR i m z _hz y _hy
  have hdisp := displacement_le_coordinateMaximum z.1 i t ((m : ℝ≥0) * Δ) ht
  linarith

/-- The endpoint-ball event at the grid time `mΔ` is measurable for the exact
finite-history sigma-algebra. -/
theorem measurableSet_endpointBall_past {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (m : ℕ)
    (y : Vec d) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m)
      {z | y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))} := by
  have hopen : IsOpen {x : Vec d | euclideanNorm (y - (x + (9 * R) • unitVector i)) < R} :=
    isOpen_lt (continuous_endpointDistance y i R) continuous_const
  exact measurable_eval_gridTime Δ m hopen.measurableSet

end EinsteinRelation.Regeneration
