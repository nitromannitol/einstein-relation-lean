import EinsteinFull.Calculus.CarverSFluxLattice
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_block

/-! Gaussian forced-flux gain from actual centered lattice blocks. The finite
estimates, smooth partition, and Bochner reconstruction retain the structural
parameters and endpoint fields of the independent-block witness. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Combining the block volume, square-sum normalization, and lattice inflation
gives exactly the exponent used in the strict forced-flux gain. -/
lemma flux_gaussian_scale_identity (d k ell : ℕ) (κ η t s : ℝ)
    (ht : 0 < t) (hs : 0 < s) :
    t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
        (1 + t / s) ^ ell *
        ((t ^ (1 / 2 + η)) ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) =
      t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ)) *
        s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
        (1 + t / s) ^ ((ell : ℝ) + (d : ℝ) / 4) := by
  have hratio : 0 < 1 + t / s := by positivity
  calc
    _ = (t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
          (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) *
          (t ^ (1 / 2 + η)) ^ (-(d : ℝ) / 2) * t ^ (η * (d : ℝ) / 2)) *
        (s ^ (-(k : ℝ) / 2) * s ^ (-(d : ℝ) / 4)) *
        ((1 + t / s) ^ ell * (1 + t / s) ^ ((d : ℝ) / 4)) := by ring
    _ = _ := by
      congr 2
      · rw [← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le,
          ← Real.rpow_add ht, ← Real.rpow_add ht, ← Real.rpow_add ht]
        congr 1
        ring
      · rw [← Real.rpow_add hs]
        congr 1
        ring
      · rw [← Real.rpow_natCast, ← Real.rpow_add hratio]

/-- Absorb the mesoscopic lattice inflation into the strict time gain and
an integer power of the Gaussian scale ratio. -/
lemma flux_gaussian_scale_le (d k ell : ℕ) (κ t s : ℝ) (hκ : 0 < κ)
    (ht : 1 ≤ t) (hs : 1 ≤ s) :
    let η := κ / (16 * ((d : ℝ) + 2))
    t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
        (1 + t / s) ^ ell *
        ((t ^ (1 / 2 + η)) ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          (1 + t ^ (1 / 2 + η) / Real.sqrt s) ^ ((d : ℝ) / 2)) ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * t ^ (-1 - κ / 8) *
        s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
        (1 + t / s) ^ (ell + ⌈(d : ℝ) / 4⌉₊) := by
  dsimp only
  let η := κ / (16 * ((d : ℝ) + 2))
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hη : 0 ≤ η := by dsimp only [η]; positivity
  have hinfl := flux_lattice_inflation_le d η t s hη ht hs
  have htime : t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ)) ≤
      t ^ (-1 - κ / 8) := by
    apply Real.rpow_le_rpow_of_exponent_le ht
    have hm := flux_lattice_exponent_margin d κ hκ
    change -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 at hm
    linarith only [hm, hκ]
  have hratio : (1 + t / s) ^ ((ell : ℝ) + (d : ℝ) / 4) ≤
      (1 + t / s) ^ (ell + ⌈(d : ℝ) / 4⌉₊) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [div_nonneg ht0.le hs0.le])
    rw [Nat.cast_add]
    simpa only [add_comm] using add_le_add_left (Nat.le_ceil ((d : ℝ) / 4)) (ell : ℝ)
  calc
    _ ≤ t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
        (1 + t / s) ^ ell *
        ((t ^ (1 / 2 + η)) ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
          ((2 : ℝ) ^ ((d : ℝ) / 2) * t ^ (η * (d : ℝ) / 2) *
            (1 + t / s) ^ ((d : ℝ) / 4))) := by gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) *
        (t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ)) *
          s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
          (1 + t / s) ^ ((ell : ℝ) + (d : ℝ) / 4)) := by
      rw [← flux_gaussian_scale_identity d k ell κ η t s ht0 hs0]
      ring
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) *
        t ^ (-1 - κ / 2 + η * ((d : ℝ) + 1 - κ)) *
          s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
          (1 + t / s) ^ ((ell : ℝ) + (d : ℝ) / 4) := by ring
    _ ≤ _ := by gcongr

/-- A finite Gaussian envelope square sum inherits the full-lattice scale
bound. The estimate is uniform in the finite set of retained blocks. -/
lemma flux_gaussian_finite_envelope_le (d k ell : ℕ) (κ t s Clat : ℝ)
    (hκ : 0 < κ) (ht : 1 ≤ t) (hs : 1 ≤ s) (hClat : 0 ≤ Clat)
    (W : (Fin d → ℤ) → ℝ) (hW : Summable (fun z => (W z) ^ 2))
    (hlat : Real.sqrt (∑' z, (W z) ^ 2) ≤
      Clat * (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ (-(d : ℝ) / 2) *
        s ^ (-(d : ℝ) / 4) *
        (1 + t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2))) / Real.sqrt s) ^
          ((d : ℝ) / 2))
    (Λ : Finset (Fin d → ℤ)) :
    t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ ((d : ℝ) + 1 - κ) *
        s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ ell *
        Real.sqrt (∑ z ∈ Λ, (W z) ^ 2) ≤
      Clat * (2 : ℝ) ^ ((d : ℝ) / 2) * t ^ (-1 - κ / 8) *
        s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
        (1 + t / s) ^ (ell + ⌈(d : ℝ) / 4⌉₊) := by
  have hfinite : Real.sqrt (∑ z ∈ Λ, (W z) ^ 2) ≤
      Real.sqrt (∑' z, (W z) ^ 2) :=
    Real.sqrt_le_sqrt (hW.sum_le_tsum Λ (fun z _ => sq_nonneg (W z)))
  calc
    _ ≤ t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ ((d : ℝ) + 1 - κ) *
        s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ ell *
        (Clat * (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ (-(d : ℝ) / 2) *
          s ^ (-(d : ℝ) / 4) *
          (1 + t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2))) / Real.sqrt s) ^
            ((d : ℝ) / 2)) := by
      gcongr
      exact hfinite.trans hlat
    _ = Clat * (t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ ((d : ℝ) + 1 - κ) *
        s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ ell *
        ((t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2)))) ^ (-(d : ℝ) / 2) *
          s ^ (-(d : ℝ) / 4) *
          (1 + t ^ (1 / 2 + κ / (16 * ((d : ℝ) + 2))) / Real.sqrt s) ^
            ((d : ℝ) / 2))) := by ring
    _ ≤ _ := by
      simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (flux_gaussian_scale_le d k ell κ t s hκ ht hs) hClat

/-- The actual centered endpoint blocks satisfy the strict Gaussian gain,
uniformly over every finite lattice truncation. The endpoint witnesses and all
structural parameters come from the independent-block dependency itself. -/
theorem carverS_flux_gaussian_finite_gain :
    node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 →
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧
      η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →

        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          let r := (t : ℝ) ^ (1 / 2 + η)
          let R := 2 * Real.sqrt (d : ℝ) + 2
          let kernel := fun y : Vec d =>
            iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
              y (fun j => unitVector (dirs j))
          ∀ χ : Vec d → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
            (∀ y, |χ y| ≤ 1) →
            (∀ y, Real.sqrt (∑ j : Fin d,
              (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
          let B := fun (x z : Vec d) (j : Fin d) =>
            ∫ y : Vec d, (χ (y - z) * kernel (x - y)) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
          (∀ y : Vec d, (∑' z : Fin d → ℤ,
            χ (y - fun j => r * (z j : ℝ))) = 1) →
          ∀ (x : Vec d) (j : Fin d),
          ∀ Λ : Finset (Fin d → ℤ),
            MemLp ((∑ z ∈ Λ, centeredComplexLp Q
              (B x (fun j => r * (z j : ℝ)) j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q) ∧
            (eLpNorm ((∑ z ∈ Λ, centeredComplexLp Q
              (B x (fun j => r * (z j : ℝ)) j)) : FieldPair d → ℂ)
              (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
              Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
                (t : ℝ) ^ (-1 - κ / 8) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
                (1 + (t : ℝ) / s) ^ Lblock k := by
  intro hblocks d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ, hκhalf, hCenv, hη, hη₀, hblocks⟩ :=
    hblocks d hd D
  obtain ⟨Clat, hClat, hlat⟩ :=
    carverS_flux_lattice_square_sum_fixed_parameters d hd κ Cenv hκ hCenv
  refine ⟨κ, η, η₀, Cenv, fun k => Lblock k + ⌈(d : ℝ) / 4⌉₊,
    hκ, hκhalf, hCenv, hη, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cloc, Cder, hgrowth₀, ht₀, hCloc, hCder, hblocks⟩ :=
    hblocks p hp
  refine ⟨growth₀, t₀, fun k => Cder k * Clat * (2 : ℝ) ^ ((d : ℝ) / 2),
    hgrowth₀, ht₀, fun k => mul_pos (mul_pos (lt_of_lt_of_le zero_lt_one (hCder k)) hClat)
      (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hfinite⟩ := hblocks Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hζ growth K hgrowth hK hmem hbound s hs hs0 k dirs
  dsimp only
  intro χ hχ hχcompact hχsupport hχone hχder hpartition x j Λ
  have hactual := (hfinite t ht hζ growth K hgrowth hK hmem hbound
    s hs hs0 k dirs χ hχ hχcompact hχsupport hχone hχder hpartition x j).2.2.2.2.2 Λ
  refine ⟨hactual.1, hactual.2.trans ?_⟩
  have ht1 : 1 ≤ (t : ℝ) := ht₀.trans ht
  obtain ⟨hsum, hlatbound, hinfl⟩ := hlat (t : ℝ) s ht1 hs x
  have hscale := flux_gaussian_finite_envelope_le d k (Lblock k) κ (t : ℝ) s Clat
    hκ ht1 hs hClat.le _ hsum hlatbound Λ
  rw [← hη] at hscale
  have hcoef : 0 ≤ Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) := by
    exact mul_nonneg (mul_nonneg (le_trans zero_le_one (hCder k))
      (le_trans zero_le_one hK)) (Real.exp_nonneg _)
  convert mul_le_mul_of_nonneg_left hscale hcoef using 1 <;> ring

/-- A nonnegative compact smooth step difference of total integral one. -/
noncomputable def fluxPartitionStep (x : ℝ) : ℝ :=
  Real.smoothTransition x - Real.smoothTransition (x - 1)

lemma flux_partition_step_contDiff : ContDiff ℝ (⊤ : ℕ∞) fluxPartitionStep :=
  Real.smoothTransition.contDiff.sub
    (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

lemma flux_partition_step_nonneg (x : ℝ) : 0 ≤ fluxPartitionStep x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

lemma flux_partition_step_le_one (x : ℝ) : fluxPartitionStep x ≤ 1 := by
  unfold fluxPartitionStep
  linarith [Real.smoothTransition.le_one x, Real.smoothTransition.nonneg (x - 1)]

lemma flux_partition_step_support : Function.support fluxPartitionStep ⊆ Set.Ioc 0 2 := by
  intro x hx
  have hn : fluxPartitionStep x ≠ 0 := hx
  constructor
  · by_contra h
    have hx0 : x ≤ 0 := le_of_not_gt h
    exact hn (by simp only [fluxPartitionStep,
      Real.smoothTransition.zero_of_nonpos hx0,
      Real.smoothTransition.zero_of_nonpos (by linarith : x - 1 ≤ 0), sub_self])
  · by_contra h
    have hx2 : 2 < x := lt_of_not_ge h
    exact hn (by simp only [fluxPartitionStep,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x),
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ x - 1), sub_self])

lemma flux_partition_step_integrable : Integrable fluxPartitionStep := by
  apply flux_partition_step_contDiff.continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 2))
  intro x hx
  apply Function.notMem_support.mp
  exact fun h => hx ⟨(flux_partition_step_support h).1.le,
    (flux_partition_step_support h).2⟩

lemma flux_partition_step_integral : (∫ x : ℝ, fluxPartitionStep x) = 1 := by
  have hc : Continuous Real.smoothTransition := (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).continuous
  rw [← intervalIntegral.integral_eq_integral_of_support_subset flux_partition_step_support]
  change (∫ x : ℝ in 0..2, Real.smoothTransition x -
    Real.smoothTransition (x - 1)) = 1
  rw [intervalIntegral.integral_sub (f := Real.smoothTransition)
    (g := fun x : ℝ => Real.smoothTransition (x - 1)) (hc.intervalIntegrable _ _)
    ((hc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _),
    intervalIntegral.integral_comp_sub_right]
  norm_num only [zero_sub, sub_self, show (2 : ℝ) - 1 = 1 by norm_num]
  have h01 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 1) (hc.intervalIntegrable 1 2)
  have hm01 := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable 0 1)
  have h12 : (∫ x : ℝ in 1..2, Real.smoothTransition x) = 1 := by
    calc
      _ = ∫ _x : ℝ in 1..2, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact Real.smoothTransition.one_of_one_le (by simpa using hx.1)
      _ = _ := by norm_num
  have hm0 : (∫ x : ℝ in (-1)..0, Real.smoothTransition x) = 0 := by
    calc
      _ = ∫ _x : ℝ in (-1)..0, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact Real.smoothTransition.zero_of_nonpos (by simpa using hx.2)
      _ = _ := by simp only [intervalIntegral.integral_zero]
  linarith only [h01, hm01, h12, hm0]

/-- The primitive of the smooth step profile, integrated from `0`. -/
noncomputable def fluxPartitionPrimitive (x : ℝ) : ℝ :=
  ∫ y : ℝ in 0..x, fluxPartitionStep y

lemma flux_partition_primitive_hasDerivAt (x : ℝ) :
    HasDerivAt fluxPartitionPrimitive (fluxPartitionStep x) x := by
  have hc := flux_partition_step_contDiff.continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

lemma flux_partition_primitive_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) fluxPartitionPrimitive := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun x => (flux_partition_primitive_hasDerivAt x).differentiableAt, ?_⟩
  have he : deriv fluxPartitionPrimitive = fluxPartitionStep :=
    funext fun x => (flux_partition_primitive_hasDerivAt x).deriv
  rw [he]
  exact flux_partition_step_contDiff

/-- Averaging a smooth partition profile over one unit interval yields a
profile whose first derivative is bounded by one, without enlarging constants. -/
noncomputable def fluxPartitionProfile (x : ℝ) : ℝ :=
  fluxPartitionPrimitive (x + 1) - fluxPartitionPrimitive x

lemma flux_partition_profile_eq_integral (x : ℝ) : fluxPartitionProfile x =
    ∫ y : ℝ in x..x + 1, fluxPartitionStep y := by
  have hc := flux_partition_step_contDiff.continuous
  have h := intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) 0 x) (hc.intervalIntegrable x (x + 1))
  unfold fluxPartitionProfile fluxPartitionPrimitive
  linarith only [h]

lemma flux_partition_profile_contDiff : ContDiff ℝ (⊤ : ℕ∞) fluxPartitionProfile :=
  (flux_partition_primitive_contDiff.comp (contDiff_id.add contDiff_const)).sub
    flux_partition_primitive_contDiff

lemma flux_partition_profile_hasDerivAt (x : ℝ) : HasDerivAt fluxPartitionProfile
    (fluxPartitionStep (x + 1) - fluxPartitionStep x) x := by
  convert
    ((flux_partition_primitive_hasDerivAt (x + 1)).comp x
      ((hasDerivAt_id x).add_const 1)).sub (flux_partition_primitive_hasDerivAt x) using 1
  · funext u
    simp only [fluxPartitionProfile, Function.comp_def, Pi.sub_apply, id_eq]
  · ring

lemma flux_partition_profile_deriv_le (x : ℝ) : |deriv fluxPartitionProfile x| ≤ 1 := by
  rw [(flux_partition_profile_hasDerivAt x).deriv, abs_le]
  constructor <;> linarith [flux_partition_step_nonneg (x + 1),
    flux_partition_step_nonneg x, flux_partition_step_le_one (x + 1),
    flux_partition_step_le_one x]

lemma flux_partition_profile_nonneg (x : ℝ) : 0 ≤ fluxPartitionProfile x := by
  rw [flux_partition_profile_eq_integral]
  exact intervalIntegral.integral_nonneg_of_forall (by linarith) flux_partition_step_nonneg

lemma flux_partition_profile_le_one (x : ℝ) : fluxPartitionProfile x ≤ 1 := by
  rw [flux_partition_profile_eq_integral]
  have h := intervalIntegral.integral_mono (by linarith : x ≤ x + 1)
    (flux_partition_step_contDiff.continuous.intervalIntegrable (μ := volume) x (x + 1))
    (continuous_const.intervalIntegrable x (x + 1)) flux_partition_step_le_one
  simpa only [intervalIntegral.integral_const, sub_self, add_sub_cancel_left,
    smul_eq_mul, mul_one] using h

lemma flux_partition_profile_support :
    Function.support fluxPartitionProfile ⊆ Set.Icc (-1) 2 := by
  intro x hx
  by_contra h
  have hn : fluxPartitionProfile x ≠ 0 := hx
  apply hn
  rw [flux_partition_profile_eq_integral]
  rw [← intervalIntegral.integral_zero (a := x) (b := x + 1)]
  apply intervalIntegral.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y hy
  apply Function.notMem_support.mp
  intro hsupp
  have hsupp := flux_partition_step_support hsupp
  have hy' : x < y ∧ y ≤ x + 1 := by simpa using hy
  change ¬ (-1 ≤ x ∧ x ≤ 2) at h
  rcases hsupp with ⟨hsupp0, hsupp2⟩
  rcases hy' with ⟨hxy, hyx⟩
  rcases not_and_or.mp h with h | h <;> linarith

lemma flux_partition_profile_hasSum (x : ℝ) :
    HasSum (fun n : ℤ => fluxPartitionProfile (x - n)) 1 := by
  have h := flux_partition_step_integrable.hasSum_intervalIntegral x
  rw [flux_partition_step_integral] at h
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr h
  simpa only [flux_partition_profile_eq_integral, Int.cast_neg, sub_eq_add_neg, Function.comp_def, Equiv.neg_apply] using hneg

/-- Tensor product of the scalar profiles at the physical lattice scale. -/
noncomputable def fluxPartitionCutoff {d : ℕ} (r : ℝ) (x : Vec d) : ℝ :=
  ∏ i : Fin d, fluxPartitionProfile (x i / r)

lemma flux_partition_tensor_hasSum (d : ℕ) (x : Vec d) :
    HasSum (fun z : Fin d → ℤ => ∏ i : Fin d,
      fluxPartitionProfile (x i - (z i : ℝ))) 1 := by
  classical
  induction d with
  | zero => simp
  | succ d ih =>
    have h0 := flux_partition_profile_hasSum (x 0)
    have ht := ih (fun i => x i.succ)
    have hs := h0.summable.mul_of_nonneg ht.summable
      (fun n => flux_partition_profile_nonneg _) (fun z =>
        Finset.prod_nonneg fun i _ => flux_partition_profile_nonneg _)
    have hp := h0.mul ht hs
    let e : (Fin (d + 1) → ℤ) ≃ ℤ × (Fin d → ℤ) :=
      { toFun := fun z => (z 0, Fin.tail z)
        invFun := fun z => Fin.cons z.1 z.2
        left_inv := fun z => Fin.cons_self_tail z
        right_inv := fun z => by simp }
    have hh := e.hasSum_iff.mpr hp
    change HasSum (fun z : Fin (d + 1) → ℤ =>
      fluxPartitionProfile (x 0 - (z 0 : ℝ)) *
        ∏ i : Fin d, fluxPartitionProfile (x i.succ - (z i.succ : ℝ))) (1 * 1) at hh
    simpa only [Fin.prod_univ_succ, one_mul] using hh

lemma flux_partition_cutoff_nonneg {d : ℕ} (r : ℝ) (x : Vec d) :
    0 ≤ fluxPartitionCutoff r x :=
  Finset.prod_nonneg fun i _ => flux_partition_profile_nonneg _

lemma flux_partition_cutoff_le_one {d : ℕ} (r : ℝ) (x : Vec d) :
    fluxPartitionCutoff r x ≤ 1 := by
  change (∏ i : Fin d, fluxPartitionProfile (x i / r)) ≤ 1
  exact Finset.prod_le_one₀
    (fun i _ => flux_partition_profile_nonneg (x i / r))
    (fun i _ => flux_partition_profile_le_one (x i / r))

lemma flux_partition_cutoff_contDiff {d : ℕ} (r : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fluxPartitionCutoff (d := d) r) := by
  apply contDiff_prod
  intro i _
  exact flux_partition_profile_contDiff.comp ((contDiff_apply ℝ ℝ i).div_const r)

lemma flux_partition_cutoff_partition {d : ℕ} {r : ℝ} (hr : 0 < r) (x : Vec d) :
    HasSum (fun z : Fin d → ℤ => fluxPartitionCutoff r
      (x - fun i => r * (z i : ℝ))) 1 := by
  have h := flux_partition_tensor_hasSum d (fun i => x i / r)
  convert h using 1
  ext z
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  dsimp only [Pi.sub_apply]
  field_simp

lemma flux_partition_cutoff_support_sharp {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Function.support (fluxPartitionCutoff (d := d) r) ⊆
      {x | euclideanNorm x ≤ 2 * Real.sqrt (d : ℝ) * r} := by
  classical
  intro x hx
  have hcoord (i : Fin d) : |x i| ≤ 2 * r := by
    have hni : fluxPartitionProfile (x i / r) ≠ 0 := by
      intro h
      exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h)
    have hi := flux_partition_profile_support hni
    have hi1 : -r ≤ x i := by simpa only [neg_one_mul] using (le_div_iff₀ hr).mp hi.1
    have hi2 : x i ≤ 2 * r := (div_le_iff₀ hr).mp hi.2
    exact abs_le.mpr ⟨by linarith, hi2⟩
  have hsum : ∑ i : Fin d, (x i) ^ 2 ≤ (d : ℝ) * (2 * r) ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, (2 * r) ^ 2 := by
        exact Finset.sum_le_sum fun i _ => sq_le_sq' (by
          have := (abs_le.mp (hcoord i)).1; linarith) (abs_le.mp (hcoord i)).2
      _ = _ := by simp
  have hn : euclideanNorm x ≤ Real.sqrt (d : ℝ) * (2 * r) := by
    change Real.sqrt (∑ i : Fin d, x i * x i) ≤ _
    simpa only [← pow_two, Real.sqrt_mul (Nat.cast_nonneg d),
      Real.sqrt_sq (by positivity : 0 ≤ 2 * r)] using Real.sqrt_le_sqrt hsum
  change euclideanNorm x ≤ 2 * Real.sqrt (d : ℝ) * r
  nlinarith only [hn]

lemma flux_partition_cutoff_support {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Function.support (fluxPartitionCutoff (d := d) r) ⊆
      {x | euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
  intro x hx
  have h : euclideanNorm x ≤ 2 * Real.sqrt (d : ℝ) * r :=
    flux_partition_cutoff_support_sharp hr hx
  change euclideanNorm x ≤ (2 * Real.sqrt (d : ℝ) + 2) * r
  nlinarith only [h, hr]

lemma flux_partition_cutoff_hasCompactSupport {d : ℕ} {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fluxPartitionCutoff (d := d) r) := by
  classical
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact
    (Set.Icc (fun _ : Fin d => -2 * r) (fun _ : Fin d => 2 * r)))
  intro x hx
  apply Function.notMem_support.mp
  intro hs
  apply hx
  have hcoord (i : Fin d) : -2 * r ≤ x i ∧ x i ≤ 2 * r := by
    have hni : fluxPartitionProfile (x i / r) ≠ 0 := by
      intro h
      exact hs (Finset.prod_eq_zero (Finset.mem_univ i) h)
    have hi := flux_partition_profile_support hni
    have hi1 : -r ≤ x i := by simpa only [neg_one_mul] using (le_div_iff₀ hr).mp hi.1
    exact ⟨by linarith, (div_le_iff₀ hr).mp hi.2⟩
  exact ⟨fun i => (hcoord i).1, fun i => (hcoord i).2⟩

lemma flux_partition_cutoff_fderiv {d : ℕ} (r : ℝ) (x : Vec d) (j : Fin d) :
    fderiv ℝ (fluxPartitionCutoff r) x (unitVector j) =
      (∏ i ∈ Finset.univ.erase j, fluxPartitionProfile (x i / r)) *
        (fluxPartitionStep (x j / r + 1) - fluxPartitionStep (x j / r)) / r := by
  classical
  let a := fun i : Fin d => fluxPartitionStep (x i / r + 1) - fluxPartitionStep (x i / r)
  have hi (i : Fin d) : HasFDerivAt (fun y : Vec d => fluxPartitionProfile (y i / r))
      (a i • (r⁻¹ • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ))) x := by
    have ht := (flux_partition_profile_hasDerivAt (r⁻¹ * x i)).comp_hasFDerivAt x
      ((hasFDerivAt_apply (𝕜 := ℝ) i x).const_mul r⁻¹)
    simpa only [a, div_eq_mul_inv, mul_comm, Function.comp_def] using ht
  have h := (HasFDerivAt.finsetProd (u := Finset.univ) (fun i _ => hi i)).fderiv
  rw [show fluxPartitionCutoff r =
    (fun y : Vec d => ∏ i : Fin d, fluxPartitionProfile (y i / r)) from rfl, h]
  simp [ContinuousLinearMap.proj_apply, unitVector, Pi.single_apply, a,
    div_eq_mul_inv, mul_comm, mul_assoc]

lemma flux_partition_cutoff_coord_deriv_le {d : ℕ} {r : ℝ} (hr : 0 < r)
    (x : Vec d) (j : Fin d) :
    |fderiv ℝ (fluxPartitionCutoff r) x (unitVector j)| ≤ 1 / r := by
  rw [flux_partition_cutoff_fderiv, abs_div, abs_mul, abs_of_pos hr]
  have hp0 : 0 ≤ ∏ i ∈ Finset.univ.erase j, fluxPartitionProfile (x i / r) :=
    Finset.prod_nonneg fun i _ => flux_partition_profile_nonneg _
  have hp1 : (∏ i ∈ Finset.univ.erase j, fluxPartitionProfile (x i / r)) ≤ 1 :=
    by
      exact Finset.prod_le_one₀
        (fun i _ => flux_partition_profile_nonneg (x i / r))
        (fun i _ => flux_partition_profile_le_one (x i / r))
  have hδ : |fluxPartitionStep (x j / r + 1) - fluxPartitionStep (x j / r)| ≤ 1 := by
    simpa only [(flux_partition_profile_hasDerivAt (x j / r)).deriv] using
      flux_partition_profile_deriv_le (x j / r)
  apply div_le_div_of_nonneg_right _ hr.le
  rw [abs_of_nonneg hp0]
  simpa only [one_mul] using mul_le_mul hp1 hδ (abs_nonneg _) zero_le_one

lemma flux_partition_cutoff_grad_le {d : ℕ} {r : ℝ} (hr : 0 < r) (x : Vec d) :
    Real.sqrt (∑ j : Fin d, (fderiv ℝ (fluxPartitionCutoff r) x (unitVector j)) ^ 2) ≤
      (2 * Real.sqrt (d : ℝ) + 2) / r := by
  have hs : ∑ j : Fin d, (fderiv ℝ (fluxPartitionCutoff r) x (unitVector j)) ^ 2 ≤
      (d : ℝ) * (1 / r) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, (1 / r) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        have hh := pow_le_pow_left₀
          (abs_nonneg (fderiv ℝ (fluxPartitionCutoff r) x (unitVector j)))
          (flux_partition_cutoff_coord_deriv_le hr x j) 2
        simpa only [sq_abs] using hh
      _ = _ := by simp
  calc
    _ ≤ Real.sqrt ((d : ℝ) * (1 / r) ^ 2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt (d : ℝ) / r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq (by positivity : 0 ≤ 1 / r)]
      ring
    _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [Real.sqrt_nonneg (d : ℝ)]) hr.le

/-- A smooth compact partition at the prescribed physical lattice scale. -/
theorem carverS_exists_flux_lattice_partition (d : ℕ)
    (r : ℝ) (hr : 0 < r) : ∃ χ : Vec d → ℝ,
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    Function.support χ ⊆ {y | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
    (∀ y, 0 ≤ χ y ∧ χ y ≤ 1) ∧
    (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤
      (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
    ∀ y, HasSum (fun z : Fin d → ℤ => χ (y - fun j => r * (z j : ℝ))) 1 := by
  exact ⟨fluxPartitionCutoff r, flux_partition_cutoff_contDiff r,
    flux_partition_cutoff_hasCompactSupport hr, flux_partition_cutoff_support hr,
    fun y => ⟨flux_partition_cutoff_nonneg r y, flux_partition_cutoff_le_one r y⟩,
    flux_partition_cutoff_grad_le hr, flux_partition_cutoff_partition hr⟩

/-- The actual partition reconstructs every Bochner-integrable spatial field. -/
lemma flux_partition_integral_hasSum {d : ℕ} {r : ℝ} (hr : 0 < r)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) (hf : Integrable f) :
    HasSum (fun z : Fin d → ℤ => ∫ y : Vec d,
      fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) • f y) (∫ y : Vec d, f y) := by
  let w := fun (z : Fin d → ℤ) (y : Vec d) =>
    fluxPartitionCutoff r (y - fun i => r * (z i : ℝ))
  have hw0 (z : Fin d → ℤ) (y : Vec d) : 0 ≤ w z y :=
    flux_partition_cutoff_nonneg _ _
  have hw (y : Vec d) : HasSum (fun z => w z y) 1 :=
    flux_partition_cutoff_partition hr y
  apply hasSum_integral_of_dominated_convergence (fun z y => w z y * ‖f y‖)
  · intro z
    exact ((flux_partition_cutoff_contDiff r).continuous.comp
      (continuous_id.sub continuous_const)).aestronglyMeasurable.smul hf.aestronglyMeasurable
  · intro z
    exact Filter.Eventually.of_forall fun y => by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hw0 z y), w, le_refl]
  · exact Filter.Eventually.of_forall fun y => (hw y).summable.mul_right ‖f y‖
  · have he (y : Vec d) : (∑' z, w z y * ‖f y‖) = ‖f y‖ := by
      rw [((hw y).mul_right ‖f y‖).tsum_eq, one_mul]
    simpa only [he] using hf.norm
  · exact Filter.Eventually.of_forall fun y => by
      simpa only [one_smul] using (hw y).smul_const (f y)

/-- A uniform actual finite-sum Lp estimate survives convergence in L2. -/
lemma flux_memLp_bound_of_tendsto {α ι : Type*} [MeasurableSpace α] [Countable ι]
    (Q : Measure α) (p C : ℝ) (hC : 0 ≤ C)
    (F : Finset ι → Lp ℂ 2 Q) (f : Lp ℂ 2 Q)
    (hF : ∀ Λ, MemLp (F Λ : α → ℂ) (ENNReal.ofReal p) Q ∧
      (eLpNorm (F Λ : α → ℂ) (ENNReal.ofReal p) Q).toReal ≤ C)
    (hlim : Filter.Tendsto F Filter.atTop (nhds f)) :
    MemLp (f : α → ℂ) (ENNReal.ofReal p) Q ∧
      (eLpNorm (f : α → ℂ) (ENNReal.ofReal p) Q).toReal ≤ C := by
  have hb : eLpNorm (f : α → ℂ) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C := by
    apply eLpNorm_le_of_tendstoInMeasure
      (Filter.Eventually.of_forall fun Λ =>
        (ENNReal.le_ofReal_iff_toReal_le (hF Λ).1.eLpNorm_ne_top hC).mpr (hF Λ).2)
      (tendstoInMeasure_of_tendsto_Lp hlim)
    exact fun Λ => (Lp.memLp (F Λ)).aestronglyMeasurable
  exact ⟨hb.trans_lt ENNReal.ofReal_lt_top, ENNReal.toReal_le_of_le_ofReal hC hb⟩

/-- Reduced-law centering commutes with the actual stationary translation. -/
lemma flux_centered_complexTranslation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) (F : Lp ℂ 2 (reducedLaw Q)) :
    centeredComplexLp Q (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (centeredComplexLp Q F) := by
  let T := complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
  have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
  have hmean : (∫ ω, T x F ω ∂reducedLaw Q) = ∫ ω, F ω ∂reducedLaw Q := by
    rw [integral_congr_ae (coeFn_complexTranslation _ _ x F)]
    have hmap : AEStronglyMeasurable F (Measure.map (translate x) (reducedLaw Q)) := by
      rw [hm.map_eq]
      exact (Lp.stronglyMeasurable F).aestronglyMeasurable
    calc
      _ = ∫ ω, F ω ∂Measure.map (translate x) (reducedLaw Q) :=
        (integral_map hm.measurable.aemeasurable hmap).symm
      _ = _ := by rw [hm.map_eq]
  apply Lp.ext
  filter_upwards [coeFn_centeredComplexLp Q (T x F),
    coeFn_complexTranslation _ (reducedLaw_stationary Q) x F,
    coeFn_complexTranslation _ (reducedLaw_stationary Q) x (centeredComplexLp Q F),
    hm.quasiMeasurePreserving.ae (coeFn_centeredComplexLp Q F)] with ω hc ht htc hct
  rw [hc, ht, htc, hct, hmean]

/-- Centered physical blocks reconstruct the literal centered Gaussian derivative. -/
lemma flux_gaussian_centered_partition_hasSum {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {r : ℝ} (hr : 0 < r) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    HasSum (fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
      (fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
          (-y) (fun j => unitVector (dirs j))) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F))
      (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q F)) := by
  letI := reducedLaw_probability Q
  let f := fun y : Vec d =>
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
      (-y) (fun j => unitVector (dirs j)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F
  have hf : Integrable f := integrable_kernel_complexTranslation _ (reducedLaw_stationary Q) _
    (integrable_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs k dirs)
    (continuous_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs k dirs) F
  have hsum := (centeredComplexLpCLM Q).hasSum (flux_partition_integral_hasSum hr f hf)
  have he : centeredComplexLpCLM Q (∫ y, f y) =
      gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q F) := by
    rw [← (centeredComplexLpCLM Q).integral_comp_comm hf]
    unfold gaussianDerivativeAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [f, map_smul, centeredComplexLpCLM_apply, flux_centered_complexTranslation]
  rw [he] at hsum
  convert hsum using 1
  funext z
  rw [centeredComplexLpCLM_apply]
  apply congrArg (centeredComplexLp Q)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [f, ← smul_assoc, Complex.real_smul]

lemma flux_euclidean_components_bound {d : ℕ} (hd : 1 ≤ d) (B : ℝ) (hB : 0 ≤ B)
    (v : Fin d → ℝ) (hv0 : ∀ j, 0 ≤ v j) (hv : ∀ j, v j ≤ B) :
    Real.sqrt (∑ j, (v j) ^ 2) ≤ (d : ℝ) * B := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ ∑ _j : Fin d, B ^ 2 := Finset.sum_le_sum fun j _ =>
      pow_le_pow_left₀ (hv0 j) (hv j) 2
    _ = (d : ℝ) * B ^ 2 := by simp
    _ ≤ (d : ℝ) ^ 2 * B ^ 2 :=
      mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg B)
    _ = _ := by ring

/-- The full Gaussian gain, with the original structural and endpoint witnesses. -/
theorem carverS_flux_gaussian_gain : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 → EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_parametersStmt → EinsteinFull.Blueprint.node_e_u3A_flux_u2D_blockStmt → ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ κ η η₀ ε Clat : ℝ, ∃ L : ℕ → ℕ, 0 < κ ∧ κ < 1 / 2 ∧ η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧ ε = κ / 8 ∧ 0 < ε ∧ 0 < η₀ ∧ 0 < Clat ∧ -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧ (∀ t s : ℝ, 1 ≤ t → 1 ≤ s → ∀ x : Vec d, let r := t ^ (1 / 2 + η); let R := 2 * Real.sqrt (d : ℝ) + 2; let W := fun z : Fin d → ℤ => sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) * Real.exp (-euclideanNorm (x - y) ^ 2 / s)) '' {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r}); Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧ Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤ Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) * (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧ (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤ Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) ∧ ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ, 0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧ ( ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q), (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧ ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ → ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K → MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) → (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) * (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) → ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s, ∀ (k : ℕ) (dirs : Fin k → Fin d), (∀ j : Fin d, MemLp (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) ∧ Real.sqrt (∑ j : Fin d, ((eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤ Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ L k) := by
  intro hblocks _hparameters _hblock d hd D
  obtain ⟨κ, η, η₀, Cenv, L, hκ, hκhalf, hCenv, hη, hη₀, hfinite⟩ :=
    carverS_flux_gaussian_finite_gain hblocks d hd D
  obtain ⟨Clat, hClat, hlat⟩ :=
    carverS_flux_lattice_square_sum_fixed_parameters d hd κ 1 hκ le_rfl
  have hηpos : 0 < η := by rw [hη]; positivity
  refine ⟨κ, η, η₀, κ / 8, Clat, L, hκ, hκhalf, hη, hη₀, rfl,
    by positivity, by rw [hη₀]; positivity, hClat, ?_, ?_, ?_⟩
  · simpa only [← hη] using flux_lattice_exponent_margin d κ hκ
  · intro t s ht hs x
    simpa only [one_mul, ← hη] using hlat t s ht hs x
  · intro p hp
    obtain ⟨growth₀, t₀, Cder, hgrowth₀, ht₀, hCder, hfinite⟩ := hfinite p hp
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    refine ⟨growth₀, t₀, fun k => (d : ℝ) * Cder k, hgrowth₀, ht₀,
      fun k => mul_pos hd0 (hCder k), ?_⟩
    intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    obtain ⟨G, J, hflux, hfinite⟩ := hfinite Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    refine ⟨G, J, hflux, ?_⟩
    intro t ht hζ growth K hgrowth hK hmem hbound s hs hs0 k dirs
    let r := (t : ℝ) ^ (1 / 2 + η)
    have hr : 0 < r := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (ht₀.trans ht)) _
    let χ : Vec d → ℝ := fluxPartitionCutoff r
    have hχabs (y : Vec d) : |χ y| ≤ 1 := by
      rw [abs_of_nonneg (flux_partition_cutoff_nonneg r y)]
      exact flux_partition_cutoff_le_one r y
    have hpartition (y : Vec d) :
        (∑' z : Fin d → ℤ, χ (y - fun i => r * (z i : ℝ))) = 1 :=
      (flux_partition_cutoff_partition hr y).tsum_eq
    have hactual := hfinite t ht hζ growth K hgrowth hK hmem hbound s hs hs0 k dirs
      χ (flux_partition_cutoff_contDiff r) (flux_partition_cutoff_hasCompactSupport hr)
      (flux_partition_cutoff_support hr) hχabs (flux_partition_cutoff_grad_le hr) hpartition
    let B := Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
      (t : ℝ) ^ (-1 - κ / 8) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
      (1 + (t : ℝ) / s) ^ L k
    have hB : 0 ≤ B := by
      have hc := (hCder k).le
      have hK0 : 0 ≤ K := zero_le_one.trans hK
      dsimp only [B]
      positivity
    have hscalar (j : Fin d) :
        MemLp (gaussianDerivativeAverage hd Q s hs0 k dirs (centeredComplexLp Q (J t j)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianDerivativeAverage hd Q s hs0 k dirs (centeredComplexLp Q (J t j)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B := by
      let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
        (χ (y - fun i => r * (z i : ℝ)) *
          iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs0 0)
            (-y) (fun i => unitVector (dirs i))) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j))
      have hsum : HasSum b (gaussianDerivativeAverage hd Q s hs0 k dirs
          (centeredComplexLp Q (J t j))) :=
        flux_gaussian_centered_partition_hasSum hd Q hr s hs0 k dirs (J t j)
      apply flux_memLp_bound_of_tendsto (reducedLaw Q) p B hB
        (fun Λ => ∑ z ∈ Λ, b z) _ _ hsum
      intro Λ
      have hh : MemLp (∑ z ∈ Λ, (b z : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q) ∧
          (eLpNorm (∑ z ∈ Λ, (b z : FieldPair d → ℂ))
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ B := by
        simpa only [b, B, zero_sub] using hactual (0 : Vec d) j Λ
      have he := Lp.coeFn_finsetSum Λ b
      refine ⟨(memLp_congr_ae he).mpr hh.1, ?_⟩
      rw [eLpNorm_congr_ae he]
      exact hh.2
    refine ⟨fun j => (hscalar j).1, ?_⟩
    have hvec := flux_euclidean_components_bound (by omega) B hB
      (fun j : Fin d => (eLpNorm (gaussianDerivativeAverage hd Q s hs0 k dirs
        (centeredComplexLp Q (J t j)) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal)
      (fun j => ENNReal.toReal_nonneg) (fun j => (hscalar j).2)
    calc
      _ ≤ (d : ℝ) * B := hvec
      _ = _ := by dsimp only [B]; ring

end EinsteinFull.Blueprint
