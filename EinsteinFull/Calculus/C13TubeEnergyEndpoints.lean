import EinsteinFull.Calculus.C13TubeWeightedEnergyTrace
import EinsteinFull.Calculus.C17TubeWeakEnergyPrimitive

open EinsteinRelation MeasureTheory Filter Set Function Metric Topology intervalIntegral EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus



private lemma setIntegral_Ioo_eq_interval {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_congr_set Ioo_ae_eq_Ioc

private lemma integrableOn_Ioo_intervalIntegrable {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : IntegrableOn f (Ioo a b) volume) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  rwa [IntegrableOn, ← Measure.restrict_congr_set (μ := volume) Ioo_ae_eq_Ioc]

private theorem integrableOn_Icc_of_Ioo {g : ℝ → ℝ} {a b : ℝ}
    (hg : IntegrableOn g (Ioo a b) volume) :
    IntegrableOn g (Icc a b) volume := by
  rwa [IntegrableOn, ← Measure.restrict_congr_set Ioo_ae_eq_Icc]

private theorem integrable_primitive {a b : ℝ} (_hab : a < b) {g : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) volume) :
    IntegrableOn (fun x => ∫ t in a..x, g t) (Ioo a b) volume := by
  have hcont := intervalIntegral.continuousOn_primitive (μ := volume) (integrableOn_Icc_of_Ioo hg)
  have hcont' : ContinuousOn (fun x => ∫ t in a..x, g t) (Icc a b) :=
    hcont.congr (fun x hx => by simp only [intervalIntegral.integral_of_le hx.1])
  exact (hcont'.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self

private theorem exists_antideriv_of_zero_integral {a b : ℝ} (_hab : a < b)
    {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_cs : HasCompactSupport η)
    (hη_supp : tsupport η ⊆ Ioo a b) (hη_int : ∫ x, η x = 0) :
    ∃ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      tsupport φ ⊆ Ioo a b ∧ ∀ x, deriv φ x = η x := by
  let φ : ℝ → ℝ := fun x => ∫ t in a..x, η t
  have hη_cont : Continuous η := hη.continuous
  have hderiv : ∀ x, HasDerivAt φ (η x) x := fun x =>
    intervalIntegral.integral_hasDerivAt_right (hη_cont.intervalIntegrable _ _)
      hη_cont.aestronglyMeasurable.stronglyMeasurableAtFilter hη_cont.continuousAt
  have hderiv_eq : deriv φ = η := funext fun x => (hderiv x).deriv
  have hφ_diff : Differentiable ℝ φ := fun x => (hderiv x).differentiableAt
  have hη_zero : ∀ x, x ∉ Ioo a b → η x = 0 := fun x hx => by
    by_contra h; exact hx (hη_supp (subset_tsupport η (Function.mem_support.mpr h)))
  have hint_ab : ∫ t in a..b, η t = 0 := by
    rw [intervalIntegral.integral_eq_integral_of_support_subset
      ((subset_tsupport η).trans (hη_supp.trans Ioo_subset_Ioc_self)), hη_int]
  have hφ_zero_ge_b : ∀ x, x ≥ b → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hη_cont.intervalIntegrable a b) (hη_cont.intervalIntegrable b x), hint_ab]
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc b x) from fun t ht => by
      simp only [Pi.zero_apply]; exact hη_zero t (fun h => not_le.mpr h.2 (uIcc_of_le hx ▸ ht).1))]
    simp
  obtain ⟨ε, hε_pos, hε_thick⟩ :=
    hη_cs.isCompact.exists_cthickening_subset_open isOpen_Ioo hη_supp
  have hη_supp_Icc : tsupport η ⊆ Icc (a + ε) (b - ε) := by
    intro x hx; have hx_Ioo := hη_supp hx; constructor
    · by_contra h; push_neg at h
      exact lt_irrefl a (hε_thick (Metric.mem_cthickening_of_dist_le a x ε _ hx
        (by rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx_Ioo.1.le)]; linarith))).1
    · by_contra h; push_neg at h
      exact lt_irrefl b (hε_thick (Metric.mem_cthickening_of_dist_le b x ε _ hx
        (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx_Ioo.2.le)]; linarith))).2
  have hη_zero_lt : ∀ x, x < a + ε → η x = 0 := fun x hx => by
    by_contra h; exact not_lt.mpr (hη_supp_Icc (subset_tsupport η (Function.mem_support.mpr h))).1 hx
  have hη_zero_gt : ∀ x, x > b - ε → η x = 0 := fun x hx => by
    by_contra h; exact not_lt.mpr (hη_supp_Icc (subset_tsupport η (Function.mem_support.mpr h))).2 hx
  have hφ_zero_lt : ∀ x, x < a + ε → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc a x) from fun t ht => by
      simp only [Pi.zero_apply]; apply hη_zero_lt
      rcases le_total a x with hax | hxa
      · rw [uIcc_of_le hax] at ht; linarith [ht.2]
      · rw [uIcc_of_ge hxa] at ht; linarith [ht.2])]
    exact intervalIntegral.integral_zero
  have hφ_zero_gt : ∀ x, x > b - ε → φ x = 0 := by
    intro x hx; show ∫ t in a..x, η t = 0
    rw [← intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hη_cont.intervalIntegrable a b) (hη_cont.intervalIntegrable b x), hint_ab]
    rw [intervalIntegral.integral_congr (show EqOn η 0 (Set.uIcc b x) from fun t ht => by
      simp only [Pi.zero_apply]; apply hη_zero_gt
      rcases le_total b x with hbx | hxb
      · rw [uIcc_of_le hbx] at ht; linarith [ht.1]
      · rw [uIcc_of_ge hxb] at ht; linarith [ht.1, hx])]
    simp
  have hφ_supp_Icc : Function.support φ ⊆ Icc (a + ε) (b - ε) := by
    intro x hx; constructor
    · by_contra h; push_neg at h; exact Function.mem_support.mp hx (hφ_zero_lt x h)
    · by_contra h; push_neg at h; exact Function.mem_support.mp hx (hφ_zero_gt x h)
  exact ⟨φ,
    contDiff_infty_iff_deriv.mpr ⟨hφ_diff, hderiv_eq ▸ hη⟩,
    IsCompact.of_isClosed_subset isCompact_Icc isClosed_closure
      (closure_minimal hφ_supp_Icc isClosed_Icc),
    (closure_minimal hφ_supp_Icc isClosed_Icc).trans (fun x ⟨h1, h2⟩ => ⟨by linarith, by linarith⟩),
    fun x => by rw [hderiv_eq]⟩

/-- If ∫_{(a,b)} f·η = 0 for all smooth η with support in (a,b), then f = 0 a.e.
on (a,b), hence ∫_{(a,b)} f·ψ = 0 for any ψ. Uses Mathlib's
`IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`. -/
private theorem smooth_cutoff_approximation {a b : ℝ} (_hab : a < b)
    {f : ℝ → ℝ} (hf : IntegrableOn f (Ioo a b) volume)
    {ψ : ℝ → ℝ} (_hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (_hψ_cs : HasCompactSupport ψ)
    (hmain : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → ∫ x in Ioo a b, f x * η x = 0) :
    ∫ x in Ioo a b, f x * ψ x = 0 := by
  have hf_ae : ∀ᵐ x ∂volume, x ∈ Ioo a b → f x = 0 := by
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo
    · exact hf.locallyIntegrableOn
    · intro η hη hη_cs hη_supp
      have hη_zero : ∀ x, x ∉ Ioo a b → η x = 0 :=
        fun x hx => by by_contra h; exact hx (hη_supp (subset_tsupport _ h))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by simp [hη_zero x hx])]
      simp only [smul_eq_mul]
      rw [show (∫ x in Ioo a b, η x * f x) = (∫ x in Ioo a b, f x * η x) from by
        congr 1; ext x; ring]
      exact hmain η hη hη_cs hη_supp
  exact integral_eq_zero_of_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
    (hf_ae.mono fun x hx hx_mem => by simp [hx hx_mem]))

private lemma integrable_of_smooth_cs {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hf_cs : HasCompactSupport f) : Integrable f :=
  hf.continuous.integrable_of_hasCompactSupport hf_cs

private lemma integrableOn_mul_of_smooth_cs {a b : ℝ} {g f : ℝ → ℝ}
    (hg : IntegrableOn g (Ioo a b) volume)
    (hf_cont : Continuous f) (hf_cs : HasCompactSupport f) :
    IntegrableOn (fun x => g x * f x) (Ioo a b) volume := by
  obtain ⟨M, _, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
    have hb := hf_cont.norm.bddAbove_range_of_hasCompactSupport hf_cs.norm
    obtain ⟨C, hC⟩ := hb
    exact ⟨max C 0, le_max_right _ _, fun x => (hC ⟨x, rfl⟩).trans (le_max_left _ _)⟩
  exact (hg.norm.mul_const M).mono'
    (hg.aestronglyMeasurable.mul hf_cont.measurable.aestronglyMeasurable)
    (ae_of_all _ fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _))

private lemma support_sub_tsupport {f g : ℝ → ℝ} :
    support (f - g) ⊆ tsupport f ∪ tsupport g := by
  intro x hx; simp only [mem_support, Pi.sub_apply, sub_ne_zero] at hx
  by_contra h; simp only [mem_union, not_or] at h
  exact hx (by rw [image_eq_zero_of_notMem_tsupport h.1, image_eq_zero_of_notMem_tsupport h.2])

/-- **Du Bois-Reymond lemma**: if `g ∈ L^1(a,b)` and `∫ g · φ' = 0` for all
smooth compactly supported `φ` in `(a,b)`, then `g` is constant a.e.

Proof (Evans, Appendix C): fix `ψ₀ ∈ C_c^∞(a,b)` with `∫ψ₀ = 1`, set `c = ∫g·ψ₀`.
For any test `η`, decompose `η = [η - (∫η)·ψ₀] + (∫η)·ψ₀`. The first part has zero
integral, hence is `φ'` for some test `φ` (antiderivative lemma). The hypothesis gives
`∫g·φ' = 0`, so `∫g·η = c·∫η`. Then `∫(g-c)·η = 0` for all test `η`, and the
fundamental lemma (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) gives `g = c` a.e. -/
private theorem du_bois_reymond
    {a b : ℝ} (hab : a < b)
    {g : ℝ → ℝ} (hg : IntegrableOn g (Ioo a b) volume)
    (htest : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ x in Ioo a b, g x * deriv φ x = 0) :
    ∃ C : ℝ, g =ᵐ[volume.restrict (Ioo a b)] fun _ => C := by
  have ⟨ψ₀, hψ₀_smooth, hψ₀_cs, hψ₀_supp, hψ₀_int⟩ :
      ∃ ψ₀ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ₀ ∧ HasCompactSupport ψ₀ ∧
        tsupport ψ₀ ⊆ Ioo a b ∧ ∫ x, ψ₀ x = 1 := by
    set f : ContDiffBump ((a + b) / 2) :=
      ⟨(b - a) / 8, (b - a) / 4, by linarith, by linarith⟩
    refine ⟨f.normed volume, f.contDiff_normed, f.hasCompactSupport_normed, ?_,
      f.integral_normed⟩
    rw [f.tsupport_normed_eq]; intro x hx
    simp only [mem_closedBall, Real.dist_eq] at hx; rw [mem_Ioo]
    have := abs_le.mp (show |x - (a + b) / 2| ≤ (b - a) / 4 from hx)
    constructor <;> linarith
  set c := ∫ x in Ioo a b, g x * ψ₀ x
  have hmain : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b → ∫ x in Ioo a b, (g x - c) * η x = 0 := by
    intro η hη hη_cs hη_supp
    set α := ∫ x, η x
    set η₀ : ℝ → ℝ := fun x => η x - α * ψ₀ x with hη₀_def
    have hαψ₀_cs : HasCompactSupport (fun x => α * ψ₀ x) := by
      rw [hasCompactSupport_def]
      apply hψ₀_cs.isCompact.of_isClosed_subset isClosed_closure
      exact closure_mono (fun x hx => by
        simp only [mem_support] at hx ⊢; intro h; exact hx (by simp [h]))
    have hαψ₀_tsup : tsupport (fun x => α * ψ₀ x) ⊆ tsupport ψ₀ :=
      closure_mono (fun x hx => by simp only [mem_support] at hx ⊢; intro h; exact hx (by simp [h]))
    have hunion_closed : IsClosed (tsupport η ∪ tsupport (fun x => α * ψ₀ x)) :=
      isClosed_closure.union isClosed_closure
    have hη₀_smooth : ContDiff ℝ (⊤ : ℕ∞) η₀ := hη.sub (contDiff_const.mul hψ₀_smooth)
    have hη₀_cs : HasCompactSupport η₀ := by
      rw [hasCompactSupport_def]; exact (hη_cs.isCompact.union hαψ₀_cs.isCompact).of_isClosed_subset
        isClosed_closure (closure_minimal (show support η₀ ⊆ _ from hη₀_def ▸ support_sub_tsupport) hunion_closed)
    have hη₀_supp : tsupport η₀ ⊆ Ioo a b :=
      (closure_minimal (hη₀_def ▸ support_sub_tsupport) hunion_closed).trans
        (union_subset hη_supp (hαψ₀_tsup.trans hψ₀_supp))
    have hη₀_int : ∫ x, η₀ x = 0 := by
      have : ∫ x, η₀ x = (∫ x, η x) - ∫ x, α * ψ₀ x :=
        integral_sub (integrable_of_smooth_cs hη hη_cs)
          ((integrable_of_smooth_cs hψ₀_smooth hψ₀_cs).const_mul α)
      rw [this, MeasureTheory.integral_const_mul, hψ₀_int, mul_one, sub_self]
    obtain ⟨φ, hφ_smooth, hφ_cs, hφ_supp, hφ_deriv⟩ :=
      exists_antideriv_of_zero_integral hab hη₀_smooth hη₀_cs hη₀_supp hη₀_int
    have key : ∫ x in Ioo a b, g x * η₀ x = 0 := by
      rw [show (fun x => g x * η₀ x) = (fun x => g x * deriv φ x) from by ext x; rw [hφ_deriv]]
      exact htest φ hφ_smooth hφ_cs hφ_supp
    have hgη := integrableOn_mul_of_smooth_cs hg hη.continuous hη_cs
    have hgψ₀ := integrableOn_mul_of_smooth_cs hg hψ₀_smooth.continuous hψ₀_cs
    have gη_eq : ∫ x in Ioo a b, g x * η x = α * ∫ x in Ioo a b, g x * ψ₀ x := by
      have h_pw : ∀ x, g x * η₀ x = g x * η x - α * (g x * ψ₀ x) := by
        intro x; simp [hη₀_def, mul_sub, mul_comm α, mul_assoc]
      have h_sub : ∫ x in Ioo a b, g x * η₀ x =
          (∫ x in Ioo a b, g x * η x) - ∫ x in Ioo a b, α * (g x * ψ₀ x) := by
        simp_rw [h_pw]; exact integral_sub hgη (hgψ₀.const_mul α)
      have h_smul : ∫ x in Ioo a b, α * (g x * ψ₀ x) =
          α * ∫ x in Ioo a b, g x * ψ₀ x := by
        simp_rw [show ∀ x, α * (g x * ψ₀ x) = α • (g x * ψ₀ x) from
          fun x => (smul_eq_mul _ _).symm]; exact integral_smul α _
      linarith [key, h_sub, h_smul]
    have hcη : IntegrableOn (fun x => c * η x) (Ioo a b) :=
      ((integrable_of_smooth_cs hη hη_cs).integrableOn).const_mul c
    have hη_Ioo : ∫ x in Ioo a b, η x = α :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
        image_eq_zero_of_notMem_tsupport (fun hmem => hx (hη_supp hmem)))
    have hcη_eq : ∫ x in Ioo a b, c * η x = c * α := by
      simp_rw [show ∀ x, c * η x = c • η x from fun x => (smul_eq_mul _ _).symm]
      rw [MeasureTheory.integral_smul, hη_Ioo, smul_eq_mul]
    simp_rw [fun x => show (g x - c) * η x = g x * η x - c * η x from by ring]
    rw [integral_sub hgη hcη, gη_eq, hcη_eq]; ring
  refine ⟨c, ?_⟩
  set h := (Ioo a b).indicator (fun x => g x - c)
  have hh_li : LocallyIntegrable h volume := by
    exact ((integrable_indicator_iff measurableSet_Ioo).mpr
      (hg.sub (integrableOn_const (hs := measure_Ioo_lt_top.ne)))).locallyIntegrable
  have hh_zero : ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, ψ x • h x = 0 := by
    intro ψ hψ hψ_cs
    simp only [smul_eq_mul]
    rw [show (fun x => ψ x * h x) = (Ioo a b).indicator (fun x => ψ x * (g x - c)) from by
      ext x; by_cases hx : x ∈ Ioo a b <;> simp [indicator, hx, h]]
    rw [MeasureTheory.integral_indicator measurableSet_Ioo,
        show (fun x => ψ x * (g x - c)) = (fun x => (g x - c) * ψ x) from by ext; ring]
    exact smooth_cutoff_approximation hab
      (hg.sub (integrableOn_const (hs := measure_Ioo_lt_top.ne))) hψ hψ_cs hmain
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hh_li hh_zero
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
  filter_upwards [hae] with x hx hx_mem
  simp only [h, indicator_of_mem hx_mem] at hx
  linarith

/-- For `u ∈ W^{1,1}(a,b)` with weak derivative `g`, `u` agrees a.e. with
`x ↦ C + ∫_a^x g(t) dt` for some constant `C`.

Proof: define `F(x) = ∫_a^x g`. By AC-IBP, `F` also has weak derivative `g` on `(a,b)`.
Then `u - F` has zero weak derivative. By `du_bois_reymond`, `u - F = D` a.e. -/
theorem c13_w11_ae_eq_ac_representative
    {a b : ℝ} (hab : a < b) {u g : ℝ → ℝ}
    (hu : IntegrableOn u (Ioo a b) volume)
    (hg : IntegrableOn g (Ioo a b) volume)
    (hweak : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, u x * deriv φ x = -∫ x in Ioo a b, g x * φ x) :
    ∃ C : ℝ, u =ᵐ[volume.restrict (Ioo a b)]
      fun x => C + ∫ t in a..x, g t := by
  set F := fun x => ∫ t in a..x, g t
  have h_uF_test : ∀ φ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ x in Ioo a b, (u x - F x) * deriv φ x = 0 := by
    intro φ hφ hφ_cs hφ_supp
    -- Convert set integral on Ioo to interval integral (they agree for volume)
    have conv := setIntegral_Ioo_eq_interval hab.le
    rw [conv]; simp_rw [sub_mul]
    -- Split ∫(u*φ' - F*φ') = ∫u*φ' - ∫F*φ'
    have hu_ii : IntervalIntegrable (fun x => u x * deriv φ x) volume a b :=
      integrableOn_Ioo_intervalIntegrable hab.le
        ((hu.bdd_mul (hφ.continuous_deriv (by norm_cast)).aestronglyMeasurable.restrict
          (ae_of_all _ fun x => (hφ_cs.deriv.exists_bound_of_continuous
            (hφ.continuous_deriv (by norm_cast))).choose_spec x)).congr
          (ae_of_all _ fun x => by ring))
    have hF_ii : IntervalIntegrable (fun x => (∫ t in a..x, g t) * deriv φ x) volume a b := by
      apply integrableOn_Ioo_intervalIntegrable hab.le
      have hcont := (intervalIntegral.continuousOn_primitive (μ := volume)
        (integrableOn_Icc_of_Ioo hg)).congr
        (fun x hx => by show ∫ t in a..x, g t = _; rw [intervalIntegral.integral_of_le hx.1])
      exact (hcont.mul (hφ.continuous_deriv (by norm_cast)).continuousOn).integrableOn_compact
        isCompact_Icc |>.mono_set Ioo_subset_Icc_self
    rw [intervalIntegral.integral_sub hu_ii hF_ii,
        ← conv, hweak φ hφ hφ_cs hφ_supp, ← conv,
        c17_primitive_compact_test_integration_by_parts hab g φ hg hφ hφ_supp]; ring
  obtain ⟨D, hD⟩ := du_bois_reymond hab
    (hu.sub (integrable_primitive hab hg))
    h_uF_test
  exact ⟨D, hD.mono (fun x hx => by simp at hx; linarith)⟩



/-- A distributional cutoff energy balance admits a continuous representative
with the corresponding signed flux increments at all interior times. -/
@[nolint unusedArguments]
theorem c13_weighted_cutoff_energy_continuous_balance_of_distributional {d : ℕ}
    {κ R a b : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hab : a < b)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u G)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ sourceBall 0 R)
    (hweak : ∀ (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηI : tsupport η ⊆ Set.Ioo a b),
    (∫ t in Set.Ioo a b, deriv η t *
      ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * u (t,x) ^ 2) =
    2 * ∫ t in Set.Ioo a b, η t * ∫ x in sourceBall 0 R,
      χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
      2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
        (fun j => fderiv ℝ χ x (unitVector j))) :
    ∃ E : ℝ → ℝ, ContinuousOn E (Set.Ioo a b) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        E t = ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * u (t,x) ^ 2) ∧
      ∀ s ∈ Set.Ioo a b, ∀ t ∈ Set.Ioo a b,
        E t - E s = -2 * ∫ r in s..t,
          ∫ x in sourceBall 0 R,
            χ x ^ 2 * dot ((α x).mulVec (G (r,x))) (G (r,x)) +
            2 * χ x * u (r,x) * dot ((α x).mulVec (G (r,x)))
              (fun j => fderiv ℝ χ x (unitVector j)) := by
  let f : ℝ → ℝ := fun t => ∫ x in sourceBall 0 R, ρ x * χ x ^ 2 * u (t,x) ^ 2
  let q : ℝ → ℝ := fun t => ∫ x in sourceBall 0 R,
    χ x ^ 2 * dot ((α x).mulVec (G (t,x))) (G (t,x)) +
    2 * χ x * u (t,x) * dot ((α x).mulVec (G (t,x)))
      (fun j => fderiv ℝ χ x (unitVector j))
  let g : ℝ → ℝ := fun t => -2 * q t
  have hf : IntegrableOn f (Set.Ioo a b) volume :=
    c13_weighted_cutoff_mass_time_integrable hκ ρ α hell _ _ u G hcal χ hχ hχc
  have hq : IntegrableOn q (Set.Ioo a b) volume :=
    c13_weighted_cutoff_energy_flux_time_integrable hκ ρ α hell _ _ u G hcal χ hχ hχc
  have hg : IntegrableOn g (Set.Ioo a b) volume := hq.const_mul (-2)
  have hw : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b →
      ∫ t in Set.Ioo a b, f t * deriv η t = -∫ t in Set.Ioo a b, g t * η t := by
    intro η hη hηc hηI
    have h := hweak η hη hηc hηI
    simp only [f, q, g] at *
    simp_rw [show ∀ t, (-2 * (∫ x in sourceBall 0 R, χ x ^ 2 *
      dot ((α x).mulVec (G (t,x))) (G (t,x)) + 2 * χ x * u (t,x) *
      dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j)))) * η t =
      -2 * (η t * (∫ x in sourceBall 0 R, χ x ^ 2 *
      dot ((α x).mulVec (G (t,x))) (G (t,x)) + 2 * χ x * u (t,x) *
      dot ((α x).mulVec (G (t,x))) (fun j => fderiv ℝ χ x (unitVector j)))) from fun t => by ring,
      MeasureTheory.integral_const_mul]
    simpa only [mul_comm (deriv η _), neg_mul, neg_neg] using h
  obtain ⟨C, hC⟩ := c13_w11_ae_eq_ac_representative hab hf hg hw
  have hi : IntervalIntegrable g volume a b := integrableOn_Ioo_intervalIntegrable hab.le hg
  refine ⟨fun t => C + ∫ r in a..t, g r, ?_, ?_, ?_⟩
  · have hc : ContinuousOn (fun x => ∫ r in a..x, g r) (Set.Icc a b) :=
      (intervalIntegral.continuousOn_primitive (integrableOn_Icc_of_Ioo hg)).congr
        (fun x hx => by rw [intervalIntegral.integral_of_le hx.1])
    exact (continuousOn_const.add hc).mono Set.Ioo_subset_Icc_self
  · exact hC.symm
  · intro s hs t ht
    have hs' : s ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨hs.1.le, hs.2.le⟩
    have ht' : t ∈ Set.uIcc a b := by simpa [Set.uIcc_of_le hab.le] using ⟨ht.1.le, ht.2.le⟩
    have his := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc hs')
    have hit := hi.mono_set (Set.uIcc_subset_uIcc Set.left_mem_uIcc ht')
    change (C + ∫ r in a..t, g r) - (C + ∫ r in a..s, g r) = -2 * ∫ r in s..t, q r
    have hadd := intervalIntegral.integral_interval_sub_left hit his
    calc
      _ = ∫ r in s..t, g r := by linarith [hadd]
      _ = -2 * ∫ r in s..t, q r := intervalIntegral.integral_const_mul _ _

end EinsteinFull.Calculus
