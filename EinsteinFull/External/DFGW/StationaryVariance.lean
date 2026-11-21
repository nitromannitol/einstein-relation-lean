import EinsteinFull.External.DFGW.TimeIntegrability
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-! # Stationary variance of compensated increments

The shifted-increment identity and stationarity identify second moments of compensated
increments with the second moments of the initial compensated process.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

omit [BorelSpace S] in
/-- The compensated process begins at zero almost surely. -/
theorem compensated_zero_ae (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) :
    (fun η => X 0 0 η - ∫ t in (0 : ℝ)..0, φ (η t)) =ᵐ[P] 0 := by
  filter_upwards [hX.additive 0 0 0 le_rfl le_rfl] with η hη
  have hz : X 0 0 η = 0 := by
    ext i
    have hi := congrFun hη i
    simp only [Pi.add_apply, Pi.zero_apply] at hi ⊢
    linarith
  simp [hz]

/-- The second moment of a compensated increment depends only on its duration. -/
theorem integral_compensated_increment_sq (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (i : Fin d)
    (hL2 : MemLp (fun η => X 0 (b - a) η - ∫ t in (0 : ℝ)..(b - a), φ (η t)) 2 P) :
    (∫ η, ((X 0 b η - ∫ t in (0 : ℝ)..b, φ (η t)) i -
      (X 0 a η - ∫ t in (0 : ℝ)..a, φ (η t)) i) ^ 2 ∂P) =
    ∫ η, (X 0 (b - a) η i - (∫ t in (0 : ℝ)..(b - a), φ (η t)) i) ^ 2 ∂P := by
  let Z : C(ℝ, S) → Vec d := fun η =>
    X 0 (b - a) η - ∫ t in (0 : ℝ)..(b - a), φ (η t)
  have hZ : Integrable (fun η => (Z η i) ^ 2) P := (hL2.eval i).integrable_sq
  have hm : AEStronglyMeasurable (fun η => (Z η i) ^ 2) (P.map (Draft.dfgwShift a)) := by
    rw [hP.stationary]
    exact hZ.aestronglyMeasurable
  have he := compensated_increment_eq_shift_of_integrable hP hX φ hφ ha hab
  calc
    (∫ η, ((X 0 b η - ∫ t in (0 : ℝ)..b, φ (η t)) i -
        (X 0 a η - ∫ t in (0 : ℝ)..a, φ (η t)) i) ^ 2 ∂P) =
        ∫ η, (Z (Draft.dfgwShift a η) i) ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [he] with η hη
      have hi := congrFun hη i
      simpa only [Z, Pi.sub_apply] using congrArg (fun x : ℝ => x ^ 2) hi
    _ = ∫ η, (Z η i) ^ 2 ∂P.map (Draft.dfgwShift a) :=
      (integral_map (measurable_shift a).aemeasurable hm).symm
    _ = ∫ η, (X 0 (b - a) η i - (∫ t in (0 : ℝ)..(b - a), φ (η t)) i) ^ 2 ∂P := by
      rw [hP.stationary]
      rfl

end EinsteinFull.External.DFGW
