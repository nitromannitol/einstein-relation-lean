import EinsteinRelation.Correctors.ParabolicPowerEnergyInequality
import EinsteinRelation.Correctors.PairedPowerEnergyPrimitive
import EinsteinRelation.Correctors.PowerGradientEnergyIntegrability
import EinsteinRelation.Correctors.WeightedEnergyFromLocalPrimitive
import EinsteinRelation.Correctors.SemigroupParabolicOnPrecompact

/-! # Paired weighted energy from the weak PDE and its actual zero trace

Source: `paper/main.tex:814–840`. This assembly uses the actual semigroup
fields, the weak local equation, and a continuous realization of their
literal energy. The time derivative and the global dissipation bound are
conclusions of the weak PDE and local integration argument.
-/

open MeasureTheory Set
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The actual paired weak flow has the weighted energy maximum and total
dissipation bounds once its scalar zero trace and scalar source integral
are supplied. Canonical flows obtain that trace from their kernel formula.
Source: `paper/main.tex:814–840`. -/
theorem paired_semigroupSolutions_weighted_energy_bound
    {d : ℕ} {K T : ℝ} (hK : 0 < K) (hT : 0 < T)
    {A₁ A₂ : Coefficient d K} {g₁ g₂ : Vec d → Vec d}
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsSemigroupSolution A₁ g₁ u₁ G₁)
    (h₂ : IsSemigroupSolution A₂ g₂ u₂ G₂)
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    [IsFiniteMeasure (volume.restrict U)] (hA : Set.EqOn A₁ A₂ U)
    {χ : Vec d → ℝ} (hχ : IsSpatialTest U χ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    {L : ℝ} (hD : ∀ x, euclideanSq (gradient χ x) ≤ L^2)
    (n : ℕ) (hn : 2 ≤ n)
    (F : ℝ → ℝ) (hF : ContinuousOn F (Icc 0 T)) (hF₀ : F 0 = 0)
    (hFn : ∀ t ∈ Icc 0 T, 0 ≤ F t)
    (hrep : ∀ t : ℝ, 0 < t → t ≤ T →
      F t = ∫ x in U, χ x^(2*n) * (u₁ (t,x) - u₂ (t,x))^2)
    (hsource : IntegrableOn (fun t =>
      (∫ x in U, (u₁ (t,x) - u₂ (t,x))^2)^((n : ℝ)⁻¹)) (Icc 0 T)) :
    let E := fun t => ∫ x in U, χ x^(2*n) * euclideanSq (G₁ (t,x) - G₂ (t,x))
    let B := (4 * (n : ℝ)^2 * K^2 * L^2) * ∫ t in (0 : ℝ)..T,
      (∫ x in U, (u₁ (t,x) - u₂ (t,x))^2)^((n : ℝ)⁻¹)
    IntegrableOn E (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, F t ≤ B^n) ∧ (∫ t in (0 : ℝ)..T, E t) ≤ B^n := by
  let v := fun z => u₁ z - u₂ z
  let G := fun z => G₁ z - G₂ z
  let E := fun t => ∫ x in U, χ x^(2*n) * euclideanSq (G (t,x))
  let g := fun t => -2 * ∫ x in U, dot ((A₁ x).mulVec (G (t,x))) (fun j =>
    χ x^(2*n) * G (t,x) j +
      2 * (n : ℝ) * χ x^(2*n-1) * v (t,x) * coordinateDerivative j χ x)
  have hl₁ (a b : ℝ) (ha : 0 < a) (hab : a < b) (_hb : b ≤ T) :=
    semigroupSolution_parabolic_on_precompact h₁ hU hUc ha hab
  have hl₂ (a b : ℝ) (ha : 0 < a) (hab : a < b) (_hb : b ≤ T) :=
    semigroupSolution_parabolic_on_precompact h₂ hU hUc ha hab
  have hp (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b ≤ T) :
      IsParabolicSolution A₁ (Ioo a b) U v G :=
    paired_parabolicSolution hK measurableSet_Ioo hU.measurableSet hA
      (hl₁ a b ha hab hb) (hl₂ a b ha hab hb)
  apply weighted_energy_bound_of_local_primitive n hn hT (by positivity)
    hF hF₀ hFn (fun t _ => integral_nonneg fun x => sq_nonneg _)
    (fun t _ => integral_nonneg fun x =>
      mul_nonneg (pow_nonneg (hχb x).1 _) (euclideanSq_nonneg_fisher _))
    hsource
  · intro a b ha hab hb
    exact (parabolicSolution_power_energy_time_integrable hK (hp a b ha hab hb) hχ n (by omega)).2
  · intro a b ha hab hb
    exact (parabolicSolution_power_gradient_energy_integrable (hp a b ha hab hb)
      hχ.1.continuous.measurable hχb n).2
  · intro a b ha hab hb
    rw [hrep b (ha.trans hab) hb, hrep a ha (hab.le.trans hb)]
    exact paired_semigroupSolutions_power_energy_integral_eq_sub hK ha hab h₁ h₂ hU hUc hA
      (hl₁ a b ha hab hb) (hl₂ a b ha hab hb) hχ n (by omega)
  · intro a b ha hab hb
    filter_upwards [parabolicSolution_power_energy_inequality_ae hK (hp a b ha hab hb)
      hχ hχb hD n hn, ae_restrict_mem measurableSet_Ioo] with t ht htI
    simpa only [hrep t (ha.trans htI.1) (htI.2.le.trans hb)] using ht

end EinsteinRelation.Correctors
