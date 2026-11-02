import EinsteinFull.Blueprint.Foundation.Proofs.SbxS3TubeProbability
import EllipticRegularity.Parabolic.LocalMax.Cutoff
import PDEFoundation.Sobolev.Cutoff.Ball
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinFull.Calculus.C13TubeMoserEssentialBound

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A weighted caloric solution remains caloric on a smaller time set. -/
theorem c20_weighted_caloric_time_mono {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {I J : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U) (hJI : J ⊆ I)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G) : IsWeightedCaloric ρ α J U u G := by
  have hsub : J ×ˢ U ⊆ I ×ˢ U := Set.prod_mono hJI Set.Subset.rfl
  have hmeasure := Measure.restrict_mono_set (volume : Measure (ℝ × Vec d)) hsub
  refine ⟨hu.1.mono_measure hmeasure, hu.2.1.mono_measure hmeasure,
    hu.2.2.1.mono_measure hmeasure, ?_, ?_⟩
  · exact ae_restrict_of_ae_restrict_of_subset hJI hu.2.2.2.1
  · intro ψ hψ hc hs
    have hs' : tsupport ψ ⊆ interior I ×ˢ U :=
      hs.trans (Set.prod_mono (interior_mono hJI) Set.Subset.rfl)
    have hz (z : ℝ × Vec d) (hz : z ∈ (I ×ˢ U) \ (J ×ˢ U)) :
        fderiv ℝ ψ z = 0 := by
      apply fderiv_of_notMem_tsupport ℝ
      intro hz'
      have hh := hs hz'
      exact hz.2 ⟨interior_subset hh.1, hh.2⟩
    have heq : (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j))) =
      ∫ z in J ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (hI.prod hU) hsub
      intro z hz'
      simp [hz z hz', dot]
    rw [← heq]
    exact hu.2.2.2.2 ψ hψ hc hs'


variable (hInterval : ∀ {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hab : a < b) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R),
∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b, s ≤ t →
        (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j))))
variable (hCutoffError : ∀ {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2),
(∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, Real.rpow (u z) p *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j))) ≤
    (L^2 * κ⁻¹) * (∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p))
variable (hFutureAverage : ∀ {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (E : ℝ → ℝ) (hrep : ∀ᵐ t ∂volume.restrict (Set.Ioo (-1 : ℝ) 1),
      E t = ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p),
IntegrableOn E (Set.Ioo (1/4 : ℝ) (1/2)) ∧
    (∫ t in Set.Ioo (1/4 : ℝ) (1/2), E t) ≤
      ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) p)
variable (hErrorIntegrable : ∀ {d : ℕ} {R a b ε p : ℝ}
    (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ),
        Integrable (fun z => Real.rpow (u z) p *
      euclideanSq (fun j => fderiv ℝ χ z.2 (unitVector j)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
variable (hMassIntegrable : ∀ {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z),
        Integrable (fun z => ρ z.2 * Real.rpow (u z) p)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))
variable (hLiteralMassIntegrable : ∀ {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ),
        Integrable (fun z => ρ z.2 * χ z.2 ^ 2 * Real.rpow (u z) p)
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)))

include hMassIntegrable in
/-- Restriction of a time interval preserves the positive mass bound. -/
theorem c20_positive_power_mass_subinterval_le {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (J : Set ℝ) (hJ : J ⊆ Set.Ioo a b) :
    (∫ z in J ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) ≤
      ∫ z in Set.Ioo a b ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p := by
  apply integral_mono_measure (Measure.restrict_mono (Set.prod_mono hJ (Set.Subset.rfl)) le_rfl)
  · filter_upwards [hu] with z hz
    exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
  · exact hMassIntegrable hκ hε hp hp1 ρ α hell u G hcal hu

include hLiteralMassIntegrable in
/-- On almost every time slice, the inner positive-power mass is bounded by
its cutoff mass on the outer ball. -/
theorem c20_positive_power_inner_mass_le_cutoff_slices {d : ℕ} {κ ε p : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hone : ∀ x ∈ sourceBall 0 (1/2), χ x = 1) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)),
      (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (t,x)) p) ≤
      ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p := by
  have hsub : sourceBall (0 : Vec d) (1/2) ⊆ sourceBall 0 1 := by
    intro x hx
    change euclideanNorm (x - 0) < 1/2 at hx
    change euclideanNorm (x - 0) < 1
    linarith
  have hsmall : MeasurableSet (sourceBall (0 : Vec d) (1/2)) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hi := hLiteralMassIntegrable hκ hε hp hp1 ρ α hell u G hcal hu χ hχ hχc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hi hu
  have hslices := Measure.ae_ae_of_ae_prod hu
  have htime : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hi.prod_right_ae,
    ae_restrict_of_ae_restrict_of_subset htime hslices] with t htint htpos
  calc
    (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (t,x)) p) =
        ∫ x in sourceBall 0 (1/2), ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p := by
      apply setIntegral_congr_fun hsmall
      intro x hx
      dsimp only
      rw [hone x hx]
      ring
    _ ≤ ∫ x in sourceBall 0 1, ρ x * χ x ^ 2 * Real.rpow (u (t,x)) p := by
      apply integral_mono_measure (Measure.restrict_mono hsub le_rfl) ?_ htint
      filter_upwards [htpos] with x hx
      exact mul_nonneg (mul_nonneg (hκ.le.trans (hell.2.2 x).1) (sq_nonneg _))
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _)



include hCutoffError hErrorIntegrable in
/-- The concave-power balance bounds the earlier cutoff trace by the later trace. -/
theorem c20_positive_power_interval_control {d : ℕ} {κ R a b ε p : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hε : 0 < ε) (hp : 0 < p) (hp1 : p < 1)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (hu : ∀ᵐ z ∂volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R), ε ≤ u z)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (L : ℝ) (hL : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ L ^ 2)
    (E : ℝ → ℝ) (s t : ℝ) (hs : s ∈ Set.Ioo a b) (ht : t ∈ Set.Ioo a b) (hst : s < t)
    (hE : (κ * p * (1-p) / 2) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x)))) ≤
        E t - E s + (2*p/(κ^3*(1-p))) * (∫ q in s..t, ∫ x in sourceBall 0 R,
          Real.rpow (u (q,x)) p * euclideanSq (fun j => fderiv ℝ χ x (unitVector j)))) :
    E s ≤ E t + ((2*p/(κ^3*(1-p))) * (L^2 * κ⁻¹)) *
      (∫ z in Set.Ioo s t ×ˢ sourceBall 0 R, ρ z.2 * Real.rpow (u z) p) := by
  have hU : MeasurableSet (sourceBall (0 : Vec d) R) := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hsub : Set.Ioo s t ⊆ Set.Ioo a b := by
    intro q hq
    exact ⟨lt_trans hs.1 hq.1, lt_trans hq.2 ht.2⟩
  have hcal' := c20_weighted_caloric_time_mono measurableSet_Ioo hU hsub hcal
  have hu' := ae_restrict_of_ae_restrict_of_subset
    (Set.prod_mono hsub (Set.Subset.rfl)) hu
  have hb := hCutoffError hκ hε hp hp1 ρ α hell u G hcal' hu' χ hχ hχc L hL
  have hi := hErrorIntegrable hε hp hp1 ρ α u G hcal' hu' χ hχ hχc
  have hprod : (volume.restrict (Set.Ioo s t)).prod (volume.restrict (sourceBall (0 : Vec d) R)) =
      (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo s t ×ˢ sourceBall 0 R) := by
    rw [Measure.prod_restrict]
    rfl
  rw [← hprod] at hi hb
  rw [integral_prod _ hi, hprod] at hb
  simp only [intervalIntegral.integral_of_le hst.le, integral_Ioc_eq_integral_Ioo] at hE
  have hpos := hu'
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hpos
  have hD : 0 ≤ ∫ q in Set.Ioo s t, ∫ x in sourceBall 0 R,
      χ x ^ 2 * (Real.rpow (u (q,x)) (p-2) * euclideanSq (G (q,x))) := by
    apply integral_nonneg_of_ae
    filter_upwards [Measure.ae_ae_of_ae_prod hpos] with q hq
    apply integral_nonneg_of_ae
    filter_upwards [hq] with x hx
    exact mul_nonneg (sq_nonneg _) (mul_nonneg
      (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hx)) _) (PDE.vecNormSq_nonneg _))
  have hp1' : 0 < 1-p := by linarith
  have hB : 0 ≤ κ*p*(1-p)/2 := by positivity
  have hA : 0 ≤ 2*p/(κ^3*(1-p)) := by positivity
  have hBD := mul_nonneg hB hD
  have hbound := mul_le_mul_of_nonneg_left hb hA
  nlinarith

/-- A future cutoff-mass average and a backward increment estimate imply the
native positive-power slice bound. The hypothesis is the remaining cutoff
trace producer, stated for the actual weighted-caloric fields. -/
theorem c20_native_positive_small_power_slice_mass_of_cutoff_trace
    (d : ℕ) (κ p A : ℝ) (hA : 0 ≤ A)
    (htrace : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ ε : ℝ, 0 < ε →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
      ∃ E : ℝ → ℝ,
        IntegrableOn E (Set.Ioo (1/4 : ℝ) (1/2)) ∧
        (∫ t in Set.Ioo (1/4 : ℝ) (1/2), E t) ≤
          ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, ρ z.2 * Real.rpow (u z) p ∧
        (∀ s ∈ Set.Ioo (-1/4 : ℝ) (1/4), ∀ t ∈ Set.Ioo (1/4 : ℝ) (1/2),
          E s ≤ E t + A * (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
            ρ z.2 * Real.rpow (u z) p)) ∧
        (∀ᵐ s ∂volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)),
          (∫ x in sourceBall 0 (1/2), ρ x * Real.rpow (u (s,x)) p) ≤ E s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ ε : ℝ, 0 < ε →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    essSup (fun t : ℝ => ENNReal.ofReal (∫ x in sourceBall 0 (1/2),
      ρ x * Real.rpow (u (t,x)) p))
      (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4))) ≤
    ENNReal.ofReal ((C) * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) p) := by
  refine ⟨4 + A, by linarith, ?_⟩
  intro ρ α hell ε hε u G hcal hu
  obtain ⟨E, hE, havg, hincr, hrep⟩ := htrace ρ α hell ε hε u G hcal hu
  obtain ⟨t, htI, _, htbound⟩ := c13_exists_future_energy_le_average E
    (fun _ => True) hE (ae_of_all _ (fun _ => trivial))
  simp only [← neg_div] at ⊢
  letI : (ae (volume.restrict (Set.Ioo (-1/4 : ℝ) (1/4)))).NeBot :=
    ae_restrict_neBot.mpr (by norm_num [Real.volume_Ioo])
  apply essSup_le_of_ae_le _ ?_ (Filter.isCoboundedUnder_le_of_le _ (x := 0) (fun _ => bot_le))
  filter_upwards [hrep, ae_restrict_mem measurableSet_Ioo] with s hs hsI
  apply ENNReal.ofReal_le_ofReal
  have hi := hincr s hsI t htI
  nlinarith

include hInterval hCutoffError hFutureAverage hErrorIntegrable
  hMassIntegrable hLiteralMassIntegrable in
/-- Uniform inner slice control for a positive small power of a caloric field. -/
theorem c20_native_positive_small_power_slice_mass_of_interval_inputs
    (d : ℕ) (hd : 2 ≤ d) (κ p : ℝ) (hκ : 0 < κ) (hp : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ ε : ℝ, 0 < ε →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), ε ≤ u z) →
    essSup (fun t : ℝ => ENNReal.ofReal (∫ x in sourceBall 0 (1/2),
      ρ x * Real.rpow (u (t,x)) p))
      (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4))) ≤
    ENNReal.ofReal (C * ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1,
      ρ z.2 * Real.rpow (u z) p) := by
  let χ : Vec d → ℝ := PDE.canonicalBallCutoff (0 : PDE.Vec d) (1/2) 1
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    PDE.canonicalBallCutoff_smooth _ (by norm_num) (by norm_num)
  have hχc : HasCompactSupport χ := PDE.canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)
  have hχU : tsupport χ ⊆ sourceBall 0 1 := by
    rw [← EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1)]
    exact PDE.canonicalBallCutoff_tsupport_subset_outer (by norm_num) (by norm_num)
  have hχ0 : ∀ x, 0 ≤ χ x := PDE.canonicalBallCutoff_nonneg _ _ _
  have hχ1 : ∀ x, χ x ≤ 1 := PDE.canonicalBallCutoff_le_one _ _ _
  have hone : ∀ x ∈ sourceBall 0 (1/2), χ x = 1 := by
    intro x hx
    apply PDE.canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num)
    rwa [EinsteinFull.Blueprint.TubeProbability.DimensionLift.pde_ball_eq_sourceBall
      (0 : PDE.Vec d) (by norm_num : (0 : ℝ) < 1/2)]
  have hgrad : ∀ x, euclideanSq (fun j => fderiv ℝ χ x (unitVector j)) ≤ (64 : ℝ)^2 := by
    intro x
    have h := PDE.canonicalBallCutoff_gradient_bound (x₀ := (0 : PDE.Vec d))
      (r := (1/2 : ℝ)) (R := 1) (by norm_num) (by norm_num) x
    have hs := pow_le_pow_left₀ (PDE.vecEuclideanNorm_nonneg _) h 2
    rw [PDE.vecEuclideanNorm_sq] at hs
    convert hs using 1 <;> norm_num [χ, PDE.vecNormSq_eq_sum_sq, euclideanSq, dot, pow_two,
      PDE.classicalGradient_apply, coordinateDerivative, PDE.basisVec, unitVector]
  let A : ℝ := (2*p/(κ^3*(1-p))) * ((64 : ℝ)^2 * κ⁻¹) + (d : ℝ)
  have hp1' : 0 < 1-p := by linarith
  have hdreal : (0 : ℝ) ≤ d := by exact_mod_cast (Nat.zero_le d)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  apply c20_native_positive_small_power_slice_mass_of_cutoff_trace d κ p A hA
  intro ρ α hell ε hε u G hcal hu
  let M : ℝ := ∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
    ρ z.2 * Real.rpow (u z) p
  obtain ⟨E, hEcont, hErep, hEincr⟩ := hInterval hκ
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (-1 : ℝ) < 1) hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc hχU
  obtain ⟨hEint, hEavg⟩ := hFutureAverage hκ hε hp hp1
    ρ α hell u G hcal hu χ hχ hχc hχ0 hχ1 E hErep
  refine ⟨E, hEint, hEavg, ?_, ?_⟩
  · intro s hs t ht
    have hsI : s ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have htI : t ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hst : s < t := by linarith [hs.2, ht.1]
    have hb := c20_positive_power_interval_control hCutoffError hErrorIntegrable hκ (by norm_num : (0 : ℝ) < 1) hε hp hp1
      ρ α hell u G hcal hu χ hχ hχc 64 hgrad E s t hsI htI hst (hEincr s hsI t htI hst.le)
    have hm := c20_positive_power_mass_subinterval_le hMassIntegrable hκ hε hp hp1 ρ α hell u G hcal hu
      (Set.Ioo s t) (by intro q hq; exact ⟨lt_trans hsI.1 hq.1, lt_trans hq.2 htI.2⟩)
    have hbase : 0 ≤ (2*p/(κ^3*(1-p))) * ((64 : ℝ)^2 * κ⁻¹) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hm hbase
    have hM : 0 ≤ M := by
      dsimp [M]
      apply integral_nonneg_of_ae
      filter_upwards [hu] with z hz
      exact mul_nonneg (hκ.le.trans (hell.2.2 z.2).1)
        (Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le hε hz)) _)
    have hdpositive : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hd)
    have hextra := mul_nonneg hdpositive.le hM
    dsimp [A, M] at *
    nlinarith
  · have hinner := c20_positive_power_inner_mass_le_cutoff_slices hLiteralMassIntegrable hκ hε hp hp1
      ρ α hell u G hcal hu χ hχ hχc hone
    have hsub : Set.Ioo (-1/4 : ℝ) (1/4) ⊆ Set.Ioo (-1 : ℝ) 1 := by
      intro t ht
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    filter_upwards [hinner, ae_restrict_of_ae_restrict_of_subset hsub hErep] with t hi he
    rw [he]
    exact hi

end EinsteinFull.Calculus
