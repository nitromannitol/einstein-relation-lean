import EinsteinFull.Homogenization.SourceResponseFluctuationDecay

/-!
# Mean convergence from one-sided fluctuations

The deterministic probabilistic step in Proposition 1.7 of Armstrong, Kuusi
and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*: convergence of means and decay of positive deviations at each
fixed mesoscopic scale imply convergence in mean.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Convergence of means and decay of one-sided fluctuations imply mean
absolute convergence to the same limit. -/
theorem tendsto_integral_abs_sub_of_posPart
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : ℕ → Ω → ℝ) (L : ℝ) (hf : ∀ m, Integrable (f m) P)
    (hmean : Tendsto (fun m => ∫ x, f m x ∂P) atTop (𝓝 L))
    (hpos : ∀ n, Tendsto (fun j => ∫ x, max 0
      (f (n + j) x - ∫ y, f n y ∂P) ∂P) atTop (𝓝 0)) :
    Tendsto (fun m => ∫ x, |f m x - L| ∂P) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := Metric.tendsto_atTop.1 hmean (ε / 8) (by positivity)
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 (hpos n) (ε / 8) (by positivity)
  refine ⟨n + J, fun m hm => ?_⟩
  have hm_n : n ≤ m := by omega
  have hmJ : J ≤ m - n := by omega
  have hn' := hn n le_rfl
  have hm' := hn m (by omega)
  have hp' := hJ (m - n) hmJ
  simp only [Real.dist_eq, sub_zero] at hn' hm' hp' ⊢
  have hmn : n + (m - n) = m := by omega
  rw [hmn] at hp'
  let A := ∫ y, f n y ∂P
  let g := fun x => f m x - A
  have hg : Integrable g P := (hf m).sub (integrable_const _)
  have habs := integral_abs_eq_two_mul_integral_posPart_sub_integral hg
  simp only [PosPart.posPart] at habs
  have hgint : (∫ x, g x ∂P) = (∫ x, f m x ∂P) - A := by
    dsimp only [g]
    rw [integral_sub (hf m) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  have htriangle : (∫ x, |f m x - L| ∂P) ≤
      (∫ x, |g x| ∂P) + |A - L| := by
    calc
      (∫ x, |f m x - L| ∂P) ≤ ∫ x, (|g x| + |A - L|) ∂P := by
        apply integral_mono ((hf m).sub (integrable_const _)).abs
          (hg.abs.add (integrable_const _))
        intro x
        change |f m x - L| ≤ |f m x - A| + |A - L|
        have h := abs_add_le (f m x - A) (A - L)
        convert h using 1; congr 1; ring
      _ = (∫ x, |g x| ∂P) + |A - L| := by
        rw [integral_add hg.abs (integrable_const _)]
        simp only [integral_const, probReal_univ, one_smul]
  have hnonneg : 0 ≤ ∫ x, |f m x - L| ∂P := integral_nonneg fun _ => abs_nonneg _
  rw [abs_of_nonneg hnonneg]
  rw [habs, hgint] at htriangle
  have hpbound : (∫ x, max (g x) 0 ∂P) < ε / 8 := by
    simpa only [max_comm] using (le_abs_self _).trans_lt hp'
  have hnabs : |A - L| < ε / 8 := hn'
  have hmabs : |(∫ x, f m x ∂P) - L| < ε / 8 := hm'
  have hnupper := le_abs_self (A - L)
  have hmlower := neg_le_of_abs_le (le_of_lt hmabs)
  linarith

/-- Under stationary finite-range dependence, the response converges in mean
to the sum of the limiting primal and dual energies minus the pairing. -/
theorem tendsto_integral_abs_sourceResponseJ_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Tendsto (fun m : ℕ => ∫ a, |Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (m : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (m : ℤ))) k hk) p q -
      ((⨅ n : ℕ, ∫ b, sourceDirichletEnergy b (sourceTriadicCube d n) (-p) ∂P) +
       (⨅ n : ℕ, ∫ b, sourceDualEnergy b
         (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) - vecDot p q)| ∂P)
      atTop (𝓝 0) := by
  apply tendsto_integral_abs_sub_of_posPart P _ _
    (fun m => integrable_sourceResponseJ hK P m k hk p q)
    (tendsto_expected_sourceResponseJ hK P hstat k hk p q)
  intro n
  simpa only [Int.natCast_add] using
    tendsto_integral_posPart_sourceResponseJ_sub_mean hK P hP hstat n k hk p q

end EinsteinFull.Homogenization
