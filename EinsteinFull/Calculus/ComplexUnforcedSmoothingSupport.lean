import EinsteinFull.Calculus.ComplexSemigroupEnergySupport
import EinsteinFull.Calculus.ComplexResolventApproximationSupport

/-!
# Unforced stationary energy decay and gradient smoothing

Symmetry of the actual full weak generator differentiates the principal energy
on its second domain. Resolvent approximation then passes the energy estimates
to the full domain and, using the closed horizontal gradient graph, to all L2 data.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- On the second full generator domain, principal energy dissipates at twice the output norm. -/
theorem IsComplexEnvironmentSemigroup.hasDerivWithinAt_unforced_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g h : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (hgh : IsComplexGeneratorPair Q i 0 g h)
    (s : ℝ) (hs : 0 ≤ s) :
    HasDerivWithinAt
      (fun r : ℝ => -(inner ℂ (P r.toNNReal f) (P r.toNNReal g)).re)
      (-2 * ‖P s.toNNReal g‖ ^ 2) (Ici s) s := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s
    ((hP.hasDerivWithinAt_orbit hfg s hs).inner ℂ (hP.hasDerivWithinAt_orbit hgh s hs))
  have he := (hP.map_generator hfg s.toNNReal).unforced_inner_symm
    (hP.map_generator hgh s.toNNReal)
  have hi : (inner ℂ (P s.toNNReal g) (P s.toNNReal g)).re = ‖P s.toNNReal g‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hn := hd.neg
  simp only [Function.comp_def, Complex.reCLM_apply, Complex.add_re,
    ← he, hi] at hn
  convert hn using 1
  ring

/-- Principal energy decreases along unforced orbits on the second full generator domain. -/
theorem IsComplexEnvironmentSemigroup.antitoneOn_unforced_energy_of_second_domain
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g h : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i 0 f g) (hgh : IsComplexGeneratorPair Q i 0 g h) :
    AntitoneOn (fun s : ℝ => -(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re) (Ici 0) := by
  have hu := (hP.2.2.1 f).comp continuous_real_toNNReal
  have hv := (hP.2.2.1 g).comp continuous_real_toNNReal
  intro a ha b _ hab
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (a := a) (b := b) hab (Complex.continuous_re.comp (hu.inner hv)).neg.continuousOn
    (fun s hs => (hP.hasDerivWithinAt_unforced_energy hfg hgh s (ha.trans hs.1.le)).mono
      Ioi_subset_Ici_self) ((continuous_const.mul (hv.norm.pow 2)).intervalIntegrable a b)
  change (∫ s in a..b, -2 * ‖P s.toNNReal g‖ ^ 2) =
    -(inner ℂ (P b.toNNReal f) (P b.toNNReal g)).re -
      -(inner ℂ (P a.toNNReal f) (P a.toNNReal g)).re at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hz := intervalIntegral.integral_nonneg_of_forall (μ := volume) hab
    (fun s : ℝ => sq_nonneg ‖P s.toNNReal g‖)
  dsimp only
  linarith only [hi, hz]

/-- Resolvent regularization of a full unforced graph pair stays in that full graph. -/
theorem IsComplexGeneratorPair.unforced_approximation_graph
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) (n : ℕ) :
    IsComplexGeneratorPair Q i 0 (unforcedComplexResolventApproximation Q i n f)
      (unforcedComplexResolventApproximation Q i n g) := by
  have he : unforcedComplexYosida Q i n f = unforcedComplexResolventApproximation Q i n g := by
    change (((n : ℝ) + 1 : ℝ) : ℂ) •
      ((((n : ℝ) + 1 : ℝ) : ℂ) •
        unforcedComplexResolvent Q i ((n : ℝ) + 1) (by positivity) f - f) = _
    rw [hfg.unforced_resolvent_error]
    rfl
  rw [← he]
  exact unforcedComplexYosida_graph Q i n f

/-- Resolvent approximation extends principal energy monotonicity to the full unforced domain. -/
theorem IsComplexEnvironmentSemigroup.antitoneOn_unforced_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    AntitoneOn (fun s : ℝ => -(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re) (Ici 0) := by
  have hn (n : ℕ) := hP.antitoneOn_unforced_energy_of_second_domain
    (hfg.unforced_approximation_graph n) (unforcedComplexYosida_graph Q i n g)
  have ht (s : ℝ) : Tendsto (fun n =>
      -(inner ℂ (P s.toNNReal (unforcedComplexResolventApproximation Q i n f))
        (P s.toNNReal (unforcedComplexResolventApproximation Q i n g))).re)
      atTop (𝓝 (-(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re)) :=
    (Complex.continuous_re.tendsto _ |>.comp
      ((((P s.toNNReal).continuous.tendsto f).comp
        (tendsto_unforcedComplexResolventApproximation Q i f)).inner
      (((P s.toNNReal).continuous.tendsto g).comp
        (tendsto_unforcedComplexResolventApproximation Q i g)))).neg
  intro a ha b hb hab
  exact le_of_tendsto_of_tendsto (ht b) (ht a) (Eventually.of_forall fun n => hn n ha hb hab)

/-- Decreasing principal energy is bounded at time t by the initial squared norm over 2t. -/
theorem IsComplexEnvironmentSemigroup.time_mul_unforced_energy_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ≥0) :
    (t : ℝ) * (-(inner ℂ (P t f) (P t g)).re) ≤ ‖f‖ ^ 2 / 2 := by
  let E : ℝ → ℝ := fun s => -(inner ℂ (P s.toNNReal f) (P s.toNNReal g)).re
  have hE : Continuous E := (Complex.continuous_re.comp
    (((hP.2.2.1 f).comp continuous_real_toNNReal).inner
      ((hP.2.2.1 g).comp continuous_real_toNNReal))).neg
  have hm := intervalIntegral.integral_mono_on (μ := volume)
    (a := (0 : ℝ)) (b := (t : ℝ)) t.property
    (continuous_const.intervalIntegrable 0 t) (hE.intervalIntegrable 0 t)
    (fun s hs => show E (t : ℝ) ≤ E s from
      hP.antitoneOn_unforced_energy hfg hs.1 t.property hs.2)
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul,
    E, Real.toNNReal_coe] at hm
  have hi := hP.integral_weighted_energy hfg t
  simp only [complexForceShift, norm_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, Real.exp_zero, one_mul, add_zero] at hi
  have hz := sq_nonneg ‖P t f‖
  linarith only [hm, hi, hz]

/-- The full unforced generator domain has the pointwise Euclidean gradient smoothing bound. -/
theorem IsComplexEnvironmentSemigroup.time_mul_gradient_sq_le
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ≥0) {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G) :
    (t : ℝ) * ‖G‖ ^ 2 ≤ (Real.exp (2 * Λ₀) * Λ₀) * ‖f‖ ^ 2 := by
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  obtain ⟨H, hH, hc⟩ := (hP.map_generator hfg t).unforced_coercive
  rw [hH.unique hG, ← PiLp.norm_sq_eq_of_L2] at hc
  have he := hP.time_mul_unforced_energy_le hfg t
  have hb := (mul_le_mul_of_nonneg_left hc t.property).trans he
  have hm := mul_le_mul_of_nonneg_left hb hK.le
  have ha : K * ((t : ℝ) * ((K⁻¹ / 2) * ‖G‖ ^ 2)) = (t : ℝ) * ‖G‖ ^ 2 / 2 := by
    field_simp
  change K * ((t : ℝ) * ((K⁻¹ / 2) * ‖G‖ ^ 2)) ≤ K * (‖f‖ ^ 2 / 2) at hm
  rw [ha] at hm
  change (t : ℝ) * ‖G‖ ^ 2 ≤ K * ‖f‖ ^ 2
  linarith only [hm]

/-- On the full domain, the unforced horizontal gradient is bounded by C times t^(-1/2). -/
theorem IsComplexEnvironmentSemigroup.norm_gradient_le_of_generator
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    (t : ℝ≥0) (ht : 0 < t)
    {G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G) :
    ‖G‖ ≤ Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ)) * ‖f‖ := by
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  apply (sq_le_sq₀ (norm_nonneg G) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg f))).mp
  rw [mul_pow, Real.sq_sqrt (div_nonneg hK (show (0 : ℝ) ≤ t from t.property))]
  have hb := hP.time_mul_gradient_sq_le hfg t hG
  have ht' : (0 : ℝ) < t := ht
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ ht').mpr (by simpa only [mul_comm (‖G‖ ^ 2)] using hb)

private theorem cauchySeq_of_norm_sub_control {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] {u : ℕ → E} {v : ℕ → F}
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n m, ‖v n-v m‖ ≤ C * ‖u n-u m‖)
    (hu : CauchySeq u) : CauchySeq v := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have hpos : 0 < C+1 := add_pos_of_nonneg_of_pos hC zero_lt_one
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hu (ε/(C+1)) (div_pos hε hpos)
  refine ⟨N, fun n hn m hm => ?_⟩
  have hgap := hN n hn m hm
  rw [dist_eq_norm] at hgap ⊢
  calc
    _ ≤ C * ‖u n-u m‖ := hb n m
    _ ≤ (C+1) * ‖u n-u m‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := (lt_div_iff₀' hpos).mp hgap

/-- Every complex L2 datum acquires an actual horizontal gradient at every positive unforced time. -/
theorem IsComplexEnvironmentSemigroup.exists_gradient_unforced
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 0 < t) :
    ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G ∧
      ‖G‖ ≤ Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ)) * ‖f‖ := by
  let C := Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / (t : ℝ))
  set u : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n => unforcedComplexResolventApproximation Q i n f with hu_def
  set v : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n => unforcedComplexYosida Q i n f with hv_def
  clear_value u v
  have hg (n : ℕ) : IsComplexGeneratorPair Q i 0 (u n) (v n) := by
    rw [hu_def, hv_def]
    exact unforcedComplexYosida_graph Q i n f
  have he (n : ℕ) : ∃ G : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t (u n)) G := by
    obtain ⟨G, hG, _⟩ := hP.map_generator (hg n) t
    exact ⟨WithLp.toLp 2 G, hG⟩
  choose G hG using he
  have hb (n m : ℕ) : ‖G n-G m‖ ≤ C * ‖u n-u m‖ := by
    have hd : IsComplexGeneratorPair Q i 0 (u n-u m) (v n-v m) := by
      simpa only [neg_one_smul, ← sub_eq_add_neg] using (hg n).add ((hg m).smul (-1))
    have hD : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t (u n-u m)) (G n-G m) := by
      intro j
      simpa only [map_sub, PiLp.sub_apply, Pi.sub_apply, neg_one_smul, ← sub_eq_add_neg] using
        (hG n j).add ((hG m j).smul (-1))
    exact hP.norm_gradient_le_of_generator hd t ht (G := G n-G m) hD
  have hu : Tendsto u atTop (𝓝 f) := by
    rw [hu_def]
    exact tendsto_unforcedComplexResolventApproximation Q i f
  have hC : CauchySeq G := cauchySeq_of_norm_sub_control (Real.sqrt_nonneg _) hb hu.cauchySeq
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hC
  have hPH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) H := by
    letI := reducedLaw_probability Q
    apply complexHorizontalGradient_of_tendsto
      (Q := reducedLaw Q) (hQ := reducedLaw_stationary Q) (l := atTop)
      (p := fun n : ℕ => (P t (u n), (G n).ofLp)) (q := (P t f, H.ofLp))
      (Eventually.of_forall hG)
    exact (((P t).continuous.tendsto f).comp hu).prodMk_nhds
      ((PiLp.continuous_ofLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))).tendsto H |>.comp hH)
  refine ⟨H, hPH, ?_⟩
  apply le_of_tendsto_of_tendsto hH.norm (hu.norm.const_mul C)
  exact Eventually.of_forall fun n => hP.norm_gradient_le_of_generator (hg n) t ht (G := G n) (hG n)

end EinsteinFull
