import EinsteinFull.Calculus.C15ClockFinitePSharedFlux
import EinsteinFull.Calculus.C9ClockHighLpAnalyticTransfer
import EinsteinFull.Calculus.RadialCutoffLimitSupport
import EinsteinFull.Calculus.C10AnalyticClockAveragedBounds

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- The same canonical gradient and its anisotropic flux have entire finite-p
representatives at every positive time. -/
theorem c15_clock_entire_gradient_flux_representatives_of_deps
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q))
    (hμ : IsReducedClockObservation Q μ)
    (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
    (r : ℝ≥0) (hr : 0 < r) :
    letI : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
    ∃ Gp Jp : ℂ → Fin d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
      (∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
          (P := P) hP μ ζ r j : FieldPair d → ℂ)) ∧
      (∀ ζ j, (Jp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        (ClockAnalyticity.flux Q (ClockAnalyticity.gradient (Q := Q)
          (i := ⟨0, by omega⟩) (P := P) hP μ ζ r) j : FieldPair d → ℂ)) ∧
      (∀ j, Differentiable ℂ (fun ζ => Gp ζ j)) ∧
      (∀ j, Differentiable ℂ (fun ζ => Jp ζ j)) := by
  classical
  letI : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  have hlift (j : Fin d) :
      ∃ Fp : ℂ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ ζ, (Fp ζ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
            (P := P) hP μ ζ r j : FieldPair d → ℂ)) ∧ Differentiable ℂ Fp := by
    apply clock_highLp_analytic_transfer_of_local_moments Q p (p + 1) hp (by linarith)
      (fun ζ => ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
        (P := P) hP μ ζ r j)
      (ClockAnalyticity.analyticGradient hP μ r hr j)
    intro ζ₀
    obtain ⟨K, hK, hb⟩ :=
      c15_clock_gradient_finite_moments_on_compact_time_force_sets_of_deps h0
        d hd D (p + 1) (‖ζ₀‖ + 1) (r : ℝ) (r : ℝ)
        (by linarith) (by positivity) hr' le_rfl
    refine ⟨1, K, zero_lt_one, hK.le, ?_⟩
    intro ζ hζ
    have hforce : ‖ζ‖ ≤ ‖ζ₀‖ + 1 := by
      have hn := norm_add_le (ζ - ζ₀) ζ₀
      rw [sub_add_cancel] at hn
      linarith
    exact hb Q hQ μ hμ P hP ζ r hforce le_rfl le_rfl j
  choose Fp hFp hFpa using hlift
  let Gp := fun ζ j => Fp j ζ
  have hGp : ∀ ζ j, (Gp ζ j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r j :=
    fun ζ j => hFp j ζ
  obtain ⟨Jp, hJp, hJpa⟩ := clock_flux_representatives_of_gradient Q (ENNReal.ofReal p)
    (fun ζ => ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
      (P := P) hP μ ζ r) Gp hGp univ (fun j => (hFpa j).differentiableOn)
  exact ⟨Gp, Jp, hGp, hJp, hFpa, fun j => differentiableOn_univ.mp (hJpa j)⟩

/-- Quantitative finite-p growth on the supplied semigroup, with the actual
quadratic force rate and no output membership assumption. -/
theorem c15_clock_semigroup_finitep_growth
    {d : ℕ} {Λ R : ℝ} {Q : EnvironmentLaw d Λ R} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (p : ℝ) (hp : 2 ≤ p) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (t : ℝ≥0) :
    MemLp (P t f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (P t f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
        eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
          ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ) * Λ) *
            (‖ζ‖ * (Real.exp (2 * Λ) * Λ)) ^ 2) * (t : ℝ))) := by
  have ha : 0 ≤ p / 2 - 1 := by linarith
  have heq : 2 * (1 + (p / 2 - 1)) = p := by ring
  have hf' : MemLp (f : FieldPair d → ℂ)
      (ENNReal.ofReal (2 * (1 + (p / 2 - 1)))) (reducedLaw Q) := by
    simpa only [heq] using hf
  have hm := (hP.power_moment_growth ha f hf' t).1
  have hn := hP.eLpNorm_growth ha f hf' t
  exact ⟨by simpa only [heq] using hm, by simpa only [heq] using hn⟩

/-- On a fixed parabolic force disc, the actual clock value and canonical
horizontal gradient have a structural, time-independent finite-p bound. -/
theorem c15_clock_finitep_on_parabolic_disc
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p B : ℝ)
    (hp : 2 ≤ p) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ))
      (ζ : ℂ) (r : ℝ≥0), 1 ≤ (r : ℝ) → ‖ζ‖ * Real.sqrt (r : ℝ) ≤ B →
      (MemLp (P ζ r μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (P ζ r μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal C) ∧
      ∀ j : Fin d,
        MemLp (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
          (P := P) hP μ ζ r j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
          (P := P) hP μ ζ r j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal C := by
  obtain ⟨L, hL, hdatum⟩ := clock_observation_uniform_moments d D
  obtain ⟨J, hJ, hgen⟩ := clock_initial_generator_uniform_moments d D B hB
  obtain ⟨H, hH, hgrad⟩ := c15_clock_gradient_finitep_of_generator_pair d hd D p hp B hB
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let E := Real.exp (((d : ℝ) * K) * K ^ 2 * B ^ 2)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hE : 0 < E := Real.exp_pos _
  have hH0 : 0 ≤ H := by linarith
  let C := L * E + H * (L * E + J * E) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ P hP ζ r hr hζ
  letI := reducedLaw_probability Q
  have hrpos : 0 < r := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)
  have hζB : ‖ζ‖ ≤ B := by
    have hs : 1 ≤ Real.sqrt (r : ℝ) := Real.one_le_sqrt.mpr hr
    exact (le_mul_of_one_le_right (norm_nonneg ζ) hs).trans hζ
  have hsq : ‖ζ‖ ^ 2 * (r : ℝ) ≤ B ^ 2 := by
    have h := pow_le_pow_left₀ (mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg _)) hζ 2
    simpa only [mul_pow, Real.sq_sqrt r.coe_nonneg] using h
  have hexp : Real.exp (((d : ℝ) * K * (‖ζ‖ * K) ^ 2) * (r : ℝ)) ≤ E := by
    apply Real.exp_le_exp.mpr
    calc
      _ = ((d : ℝ) * K) * K ^ 2 * (‖ζ‖ ^ 2 * (r : ℝ)) := by ring
      _ ≤ ((d : ℝ) * K) * K ^ 2 * B ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
  have hμp : MemLp (μ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hdatum Q μ hμ _).trans_lt (by finiteness)
  obtain ⟨g, hμg, hgtop, hgnorm⟩ := hgen Q hQ μ hμ ⟨0, by omega⟩ ζ hζB
  have hgp := hgtop.mono_exponent (show ENNReal.ofReal p ≤ ∞ from le_top)
  obtain ⟨hfm, hfn⟩ := c15_clock_semigroup_finitep_growth (hP ζ) p hp μ hμp r
  obtain ⟨hgm, hgn⟩ := c15_clock_semigroup_finitep_growth (hP ζ) p hp g hgp r
  have hb (F : Lp ℂ 2 (reducedLaw Q)) (M : ℝ) (hM : 0 ≤ M)
      (hm : eLpNorm F (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M)
      (hn : eLpNorm (P ζ r F) (ENNReal.ofReal p) (reducedLaw Q) ≤
        eLpNorm F (ENNReal.ofReal p) (reducedLaw Q) *
          ENNReal.ofReal (Real.exp (((d : ℝ) * K * (‖ζ‖ * K) ^ 2) * (r : ℝ)))) :
      eLpNorm (P ζ r F) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal (M * E) := by
    exact hn.trans ((mul_le_mul' hm (ENNReal.ofReal_le_ofReal hexp)).trans_eq
      (ENNReal.ofReal_mul hM).symm)
  have hfbound := hb μ L hL.le (hdatum Q μ hμ _) hfn
  have hgbound := hb g J hJ.le (hgnorm _) hgn
  have hfC : L * E ≤ C := by
    dsimp [C]
    linarith [mul_nonneg hH0 (add_nonneg (mul_nonneg hL.le hE.le)
      (mul_nonneg hJ.le hE.le))]
  constructor
  · exact ⟨hfm, hfbound.trans (ENNReal.ofReal_le_ofReal hfC)⟩
  · intro j
    have hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P ζ r μ) (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
          (P := P) hP μ ζ r) := by
      intro k
      simpa only [ClockAnalyticity.gradient, dif_pos hrpos] using
        ((hP ζ).forcedGradient_spec r hrpos μ k)
    obtain ⟨hm, hn⟩ := hgrad Q hQ ⟨0, by omega⟩ ζ hζB (P ζ r μ) (P ζ r g)
      (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ ζ r)
      ((hP ζ).map_generator hμg r) hG hfm hgm j
    refine ⟨hm, ?_⟩
    rw [← ENNReal.ofReal_toReal hm.eLpNorm_ne_top]
    apply ENNReal.ofReal_le_ofReal
    have hnf : (eLpNorm (P ζ r μ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ L * E :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hfbound).trans_eq
        (ENNReal.toReal_ofReal (mul_pos hL hE).le)
    have hng : (eLpNorm (P ζ r g) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ J * E :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hgbound).trans_eq
        (ENNReal.toReal_ofReal (mul_pos hJ hE).le)
    exact hn.trans ((mul_le_mul_of_nonneg_left (add_le_add hnf hng) hH0).trans
      (by dsimp [C]; linarith [mul_nonneg hL.le hE.le]))

/-- The averaged decay holds for the actual canonical clock flux.  Weak-gradient
uniqueness identifies the decay witnesses before either norm is estimated. -/
theorem c15_clock_canonical_outer_disc_decay
    (h0 : node_stationary_u2D_analytic_u2D_semigroupStmt)
    (hflux : node_l_u3A_forced_u2D_fluxStmt)
    (hscalar : node_p_u3A_scalarStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε C t₀ : ℝ, 0 < ε ∧ 0 < C ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
    ∀ (P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (P ζ)),
    ∀ r : ℝ≥0, t₀ ≤ (r : ℝ) → ∀ (s : ℝ) (hs : 0 < s),
      2 * (r : ℝ) ≤ s → ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt (r : ℝ) ≤ 2 →
      ‖gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r)‖ ≤
        C * (r : ℝ) ^ (-1 / 2 : ℝ) * s ^ (-(d : ℝ) / 4) ∧
      Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
        (centeredComplexLp Q (ζ • ClockAnalyticity.flux Q
          (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
            (P := P) hP μ ζ r) j))‖ ^ 2) ≤
        C * (r : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) := by
  intro d hd D
  obtain ⟨ε, hε, hb⟩ := analytic_clock_averaged_bounds_of_deps h0 hflux hscalar d hd D
  obtain ⟨C, t₀, N, hC, ht₀, hb⟩ := hb 2 2 (by norm_num) (by norm_num)
  refine ⟨ε, C, t₀, hε, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP r hr s hs hrs ζ hζ
  obtain ⟨G, J, hweak, havg⟩ := hb Q hQ a μ ha hμ P hP
  have hrpos : 0 < (r : ℝ) := zero_lt_one.trans_le (ht₀.trans hr)
  have hrpos' : 0 < r := by exact_mod_cast hrpos
  have hcanonical := (ClockAnalyticity.sharedWeakFlux hd a ha hP μ ζ r hrpos').1
  have hgrad := ((hweak ζ r hrpos).1).1.unique hcanonical.1
  have hfluxeq : J ζ r = ClockAnalyticity.flux Q
      (ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩)
        (P := P) hP μ ζ r) := by
    funext j
    apply Lp.ext
    exact (((hweak ζ r hrpos).1).2 j).trans
      (by simpa only [hgrad] using (hcanonical.2 j).symm)
  have hdecay := (havg r hr s hs hrs).2.2.2.2 ζ hζ
  simpa only [hfluxeq] using hdecay


private def c15LpCoefficient {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : Fin d) :
    Lp ℂ p (reducedLaw Q) →L[ℂ] Lp ℂ p (reducedLaw Q) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ p p
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ)))

private theorem c15LpCoefficient_coe {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : Fin d)
    (f : Lp ℂ p (reducedLaw Q)) :
    (c15LpCoefficient Q p j k f : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (ω.1 0 j k : ℂ) * f ω := by
  have hc := (memLp_reduced_coefficient_complex Q j k).coeFn_toLp
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := p)
    ((memLp_reduced_coefficient_complex Q j k).toLp (fun ω => (ω.1 0 j k : ℂ))) f
  filter_upwards [hc, hm] with ω ha hb
  simpa only [c15LpCoefficient, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ha] using hb

private theorem c15LpCoefficient_norm_le {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)] (j k : Fin d)
    (f : Lp ℂ p (reducedLaw Q)) :
    ‖c15LpCoefficient Q p j k f‖ ≤ sourceReducedBound Λ * ‖f‖ := by
  have hK : 0 ≤ Real.exp (2 * Λ) * Λ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  apply (show ‖c15LpCoefficient Q p j k f‖ ≤
      (Real.exp (2 * Λ) * Λ) * ‖f‖ from ?_).trans
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    unfold sourceReducedBound
    exact mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg Λ]) (Real.exp_pos _).le
  · apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [c15LpCoefficient_coe Q p j k f,
      Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hf hω
    rw [hf, norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    rw [Complex.norm_real, Real.norm_eq_abs]
    apply abs_entry_le_of_quadratic_bounds hK (ω.1 0) (hω 0).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hK) (euclideanSq_nonneg_coords ξ)).trans
        ((hω 0).2 ξ).1
    · exact fun ξ => ((hω 0).2 ξ).2

/-- Any finite-p representatives of the same canonical flux retain the actual
anisotropic coefficient bound. -/
theorem c15_clock_flux_finitep_norm_le {d : ℕ} {Λ R : ℝ}
    (Q : EnvironmentLaw d Λ R) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (Gp : Fin d → Lp ℂ p (reducedLaw Q)) (Jp : Lp ℂ p (reducedLaw Q))
    (hG : ∀ k, (Gp k : FieldPair d → ℂ) =ᵐ[reducedLaw Q] G k)
    (j : Fin d) (hJ : (Jp : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      ClockAnalyticity.flux Q G j) :
    ‖Jp‖ ≤ (2 * sourceReducedBound Λ) * ∑ k, ‖Gp k‖ := by
  classical
  let H k := c15LpCoefficient Q p j k (Gp k) -
    (homogenizedCoefficient Q j k : ℂ) • Gp k
  have he : Jp = ∑ k, H k := by
    apply Lp.ext
    apply hJ.trans
    have hs := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin d)) H
    have hsl := Lp.coeFn_fun_finsetSum (Finset.univ : Finset (Fin d))
      (fun k => complexCoefficientMul Q j k (G k) -
        (homogenizedCoefficient Q j k : ℂ) • G k)
    filter_upwards [hs, hsl, ae_all_iff.mpr hG,
      ae_all_iff.mpr (fun k => c15LpCoefficient_coe Q p j k (Gp k)),
      ae_all_iff.mpr (fun k => complexCoefficientMul_coe Q j k (G k)),
      ae_all_iff.mpr (fun k => Lp.coeFn_sub (c15LpCoefficient Q p j k (Gp k))
        ((homogenizedCoefficient Q j k : ℂ) • Gp k)),
      ae_all_iff.mpr (fun k => Lp.coeFn_sub (complexCoefficientMul Q j k (G k))
        ((homogenizedCoefficient Q j k : ℂ) • G k)),
      ae_all_iff.mpr (fun k => Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) (Gp k)),
      ae_all_iff.mpr (fun k => Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) (G k))]
      with ω hs hsl hG hc hcl hd hdl hm hml
    change (∑ k, (complexCoefficientMul Q j k (G k) -
      (homogenizedCoefficient Q j k : ℂ) • G k)) ω = _
    rw [hsl, hs]
    apply Finset.sum_congr rfl
    intro k _
    simp only [H, hd, hdl, hm, hml, hc, hcl, hG, Pi.sub_apply, Pi.smul_apply]
  have hentry k : ‖(homogenizedCoefficient Q j k : ℂ)‖ ≤ sourceReducedBound Λ := by
    have hcoord (x : Vec d) : |x j| ≤ euclideanNorm x := by
      unfold euclideanNorm euclideanSq dot
      rw [← Real.sqrt_sq_eq_abs (x j)]
      apply Real.sqrt_le_sqrt
      simpa only [pow_two] using!
        (Finset.single_le_sum (fun l _ => mul_self_nonneg (x l)) (Finset.mem_univ j))
    have h := (hcoord ((homogenizedCoefficient Q).mulVec (unitVector k))).trans
      (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
    simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
      Complex.norm_real, Real.norm_eq_abs] using! h
  rw [he]
  calc
    _ ≤ ∑ k, ‖H k‖ := norm_sum_le _ _
    _ ≤ ∑ k, (2 * sourceReducedBound Λ) * ‖Gp k‖ := by
      apply Finset.sum_le_sum
      intro k _
      apply (norm_sub_le _ _).trans
      rw [norm_smul]
      have hm := c15LpCoefficient_norm_le Q p j k (Gp k)
      have hh := mul_le_mul_of_nonneg_right (hentry k) (norm_nonneg (Gp k))
      linarith
    _ = _ := (Finset.mul_sum ..).symm

private theorem c15_sqrt_sum_sq_le {d : ℕ} (hd : 1 ≤ d)
    (f : Fin d → ℝ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ j, 0 ≤ f j ∧ f j ≤ K) :
    Real.sqrt (∑ j, f j ^ 2) ≤ (d : ℝ) * K := by
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  have hs : (∑ j, f j ^ 2) ≤ (d : ℝ) * K ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, K ^ 2 :=
        Finset.sum_le_sum (fun j _ => by nlinarith [(hf j).1, (hf j).2])
      _ = _ := by simp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  exact hs.trans ((mul_le_mul_of_nonneg_right hd2 (sq_nonneg K)).trans_eq (by ring))

/-- Assembly of the original clock contract from its three graph dependencies,
using one canonical gradient and flux throughout. -/
theorem c15_clock_of_deps :
    node_stationary_u2D_analytic_u2D_semigroupStmt → node_l_u3A_forced_u2D_fluxStmt →
      node_p_u3A_scalarStmt → node_stationary_u2D_analytic_u2D_semigroup_u23_clockStmt := by
  classical
  intro h0 hflux hscalar d hd D
  obtain ⟨ε, Cd, t₀, hε, hCd, ht₀, hdecay⟩ :=
    c15_clock_canonical_outer_disc_decay h0 hflux hscalar d hd D
  refine ⟨ε, hε, ?_⟩
  intro p B hp hB
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  obtain ⟨K, hK, hdisc⟩ := c15_clock_finitep_on_parabolic_disc d hd D p B hp (by linarith)
  let κ := sourceReducedBound D.ellipticity
  have hκ : 0 ≤ κ := by
    dsimp [κ, sourceReducedBound]
    have := D.one_le_ellipticity
    positivity
  let L := (2 * κ) * ((d : ℝ) * K)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  let C := 2 * K + (d : ℝ) * K + (d : ℝ) * L + Cd + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hCdC : Cd ≤ C := by
    have hdK : 0 ≤ (d : ℝ) * K := by positivity
    have hdL : 0 ≤ (d : ℝ) * L := by positivity
    dsimp [C]
    linarith
  refine ⟨C, t₀, 0, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP
  letI := reducedLaw_probability Q
  let G := ClockAnalyticity.gradient (Q := Q) (i := ⟨0, by omega⟩) (P := P) hP μ
  let J := fun ζ r => ClockAnalyticity.flux Q (G ζ r)
  refine ⟨G, J, ?_, ?_⟩
  · intro ζ r hr
    exact ClockAnalyticity.sharedWeakFlux hd a ha hP μ ζ r (by exact_mod_cast hr)
  · intro r hr
    have hr1 : 1 ≤ (r : ℝ) := ht₀.trans hr
    have hrpos : 0 < (r : ℝ) := by linarith
    have hrnn : 0 < r := by exact_mod_cast hrpos
    obtain ⟨Kw, _, hw⟩ := clock_value_finitep_on_compact_sets_of_deps h0 d hd D p 1 r hp
      zero_lt_one hrpos
    obtain ⟨Wp, hWp, hWa, _⟩ := hw Q hQ μ hμ P hP r le_rfl
    obtain ⟨Gp, Jp, hGp, hJp, hGa, hJa⟩ :=
      c15_clock_entire_gradient_flux_representatives_of_deps h0 d hd D p hp Q hQ μ hμ
        P hP r hrnn
    refine ⟨Wp, Gp, Jp, hWp, fun ζ j => ⟨hGp ζ j, hJp ζ j⟩,
      fun ζ _ => (hWa ζ).differentiableAt.differentiableWithinAt,
      fun j => ⟨(hGa j).differentiableOn, (hJa j).differentiableOn⟩, ?_, ?_⟩
    · intro ζ hζ
      have hb := hdisc Q hQ μ hμ P hP ζ r hr1 hζ
      have hraw : (eLpNorm (P ζ r μ : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ K :=
        (ENNReal.toReal_mono ENNReal.ofReal_ne_top hb.1.2).trans_eq
          (ENNReal.toReal_ofReal hK.le)
      let u := hb.1.1.toLp (P ζ r μ)
      have he : Wp ζ = EndpointFiniteP.center u := by
        apply Lp.ext
        exact (hWp ζ).trans
          (EndpointFiniteP.center_ae_l2 Q u (P ζ r μ) hb.1.1.coeFn_toLp).symm
      have hnW : ‖Wp ζ‖ ≤ 2 * K := by
        rw [he]
        apply (EndpointFiniteP.norm_center_le u).trans
        simpa only [u, Lp.norm_toLp] using
          mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 2)
      have hnG (j : Fin d) : ‖Gp ζ j‖ ≤ K := by
        rw [Lp.norm_def, eLpNorm_congr_ae (hGp ζ j)]
        exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb.2 j).2).trans_eq
          (ENNReal.toReal_ofReal hK.le)
      have hnJ (j : Fin d) : ‖Jp ζ j‖ ≤ L := by
        apply (c15_clock_flux_finitep_norm_le Q (ENNReal.ofReal p) (G ζ r)
          (Gp ζ) (Jp ζ j) (hGp ζ) j (hJp ζ j)).trans
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc
          _ ≤ ∑ _j : Fin d, K := Finset.sum_le_sum (fun j _ => hnG j)
          _ = _ := by simp
      have hgs := c15_sqrt_sum_sq_le (by omega : 1 ≤ d)
        (fun j => ‖Gp ζ j‖) K hK.le (fun j => ⟨norm_nonneg _, hnG j⟩)
      have hjs := c15_sqrt_sum_sq_le (by omega : 1 ≤ d)
        (fun j => ‖Jp ζ j‖) L hL (fun j => ⟨norm_nonneg _, hnJ j⟩)
      simp only [pow_zero, mul_one]
      dsimp [C]
      linarith
    · intro s hs hrs
      dsimp only
      let H := homogeneousAverageCLM Q (⟨0, by omega⟩ : Fin d) s hs 0
      have hH (f : Lp ℂ 2 (reducedLaw Q)) : H f = gaussianAverage hd Q s hs f := rfl
      have hc (c : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
          centeredComplexLp Q (c • f) = c • centeredComplexLp Q f := by
        simpa only [centeredComplexLpCLM_apply] using (centeredComplexLpCLM Q).map_smul c f
      have hU (ζ : ℂ) : gaussianAverage hd Q s hs (clockEndpoint Q ζ (P ζ) μ r) =
          ζ • gaussianAverage hd Q s hs (centeredComplexLp Q (P ζ r μ)) := H.map_smul ζ _
      have hV (ζ : ℂ) (j : Fin d) :
          gaussianAverage hd Q s hs (centeredComplexLp Q (ζ • J ζ r j)) =
          ζ • gaussianAverage hd Q s hs (centeredComplexLp Q (J ζ r j)) := by
        rw [hc]
        exact H.map_smul ζ _
      refine ⟨?_, ?_, ?_, ?_, hU, hV, ?_⟩
      · intro z _
        have ha := (H.analyticAt _).comp (analyticAt_clockEndpoint hP μ r z)
        simpa only [Function.comp_def, hH] using ha.differentiableAt.differentiableWithinAt
      · intro j z _
        have hJ := ((centeredComplexLpCLM Q).analyticAt _).comp
          ((analyticAt_id (𝕜 := ℂ) (z := z)).fun_smul
            (ClockAnalyticity.analyticFlux hP μ r hrnn j z))
        have ha := (H.analyticAt _).comp hJ
        simpa only [Function.comp_def, id_eq, hH, centeredComplexLpCLM_apply] using
          ha.differentiableAt.differentiableWithinAt
      · rw [hU, zero_smul]
      · intro j
        rw [hV, zero_smul]
      · intro ζ hζ
        have hb := hdecay Q hQ a μ ha hμ P hP r hr s hs hrs ζ hζ
        refine ⟨hb.1.trans ?_, hb.2.trans ?_⟩
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCdC (Real.rpow_nonneg r.coe_nonneg _))
            (Real.rpow_nonneg hs.le _)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hCdC (Real.rpow_nonneg r.coe_nonneg _))
            (Real.rpow_nonneg hs.le _)

end EinsteinFull.Blueprint
