import EinsteinRelation.Environment.AKMTestIntegralSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Topology.ContinuousMap.Compact

/-! # Countable determining smooth tests

Source: `paper/main.tex:699–704`, the coefficient observations of AKM (0.11).
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The zero smooth compact test, used to make the countable family nonempty. -/
def countableTestZero (d : ℕ) : SmoothCompactTest d :=
  ⟨fun _ => 0, contDiff_const, HasCompactSupport.zero⟩

/-- Restriction of a smooth test to a closed ball, as a continuous function on that ball. -/
def countableTestRestrict {d : ℕ} (R : ℝ) (φ : SmoothCompactTest d) :
    ContinuousMap (Metric.closedBall (0 : Vec d) R) ℝ :=
  ⟨fun x => φ.toFun x.1, φ.smooth.continuous.comp continuous_subtype_val⟩

/-- For each radius `m + 1`, a countable set of smooth tests supported in that ball
approximates every smooth test supported in the same ball, uniformly. Separability of
`C(closedBall, ℝ)` supplies a countable dense subset of the restricted tests. -/
theorem countable_test_ball_net (d : ℕ) (m : ℕ) :
    ∃ P : Set (SmoothCompactTest d), P.Countable ∧
      ∀ φ : SmoothCompactTest d, Function.support φ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1) →
        ∀ ε : ℝ, 0 < ε → ∃ ψ ∈ P, Function.support ψ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1) ∧
          ∀ x, |ψ.toFun x - φ.toFun x| ≤ ε := by
  haveI : CompactSpace (Metric.closedBall (0 : Vec d) ((m : ℝ) + 1)) :=
    isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  haveI : SecondCountableTopology
      (ContinuousMap (Metric.closedBall (0 : Vec d) ((m : ℝ) + 1)) ℝ) := inferInstance
  haveI : Nonempty (SmoothCompactTest d) := ⟨countableTestZero d⟩
  obtain ⟨t, htT, htc, hTt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace
      (countableTestRestrict ((m : ℝ) + 1) '' {φ : SmoothCompactTest d |
        Function.support φ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1)})).exists_countable_dense_subset
  have hpre : ∀ h ∈ t, ∃ ψ : SmoothCompactTest d,
      Function.support ψ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1) ∧
        countableTestRestrict ((m : ℝ) + 1) ψ = h := by
    intro h hh
    obtain ⟨φ, hφ, rfl⟩ := htT hh
    exact ⟨φ, hφ, rfl⟩
  choose! ψ hψs hψr using hpre
  refine ⟨ψ '' t, htc.image ψ, fun φ hφ ε hε => ?_⟩
  have hφ' : φ ∈ {φ : SmoothCompactTest d |
      Function.support φ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1)} := hφ
  have hmem : countableTestRestrict ((m : ℝ) + 1) φ ∈ closure t :=
    hTt (Set.mem_image_of_mem _ hφ')
  obtain ⟨h, hht, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
  refine ⟨ψ h, ⟨h, hht, rfl⟩, hψs h hht, fun x => ?_⟩
  by_cases hx : x ∈ Metric.closedBall (0 : Vec d) ((m : ℝ) + 1)
  · have hd : dist (countableTestRestrict ((m : ℝ) + 1) φ ⟨x, hx⟩) (h ⟨x, hx⟩) ≤
        dist (countableTestRestrict ((m : ℝ) + 1) φ) h :=
      ContinuousMap.dist_apply_le_dist (⟨x, hx⟩ : Metric.closedBall (0 : Vec d) ((m : ℝ) + 1))
    have hhx : (ψ h).toFun x = h ⟨x, hx⟩ :=
      congrArg (fun g : ContinuousMap (Metric.closedBall (0 : Vec d) ((m : ℝ) + 1)) ℝ =>
        g ⟨x, hx⟩) (hψr h hht)
    have key : |φ.toFun x - h ⟨x, hx⟩| < ε := by
      have := lt_of_le_of_lt hd hdist
      rw [Real.dist_eq] at this
      exact this
    rw [hhx, abs_sub_comm]
    exact key.le
  · have h1 : (ψ h).toFun x = 0 := by
      by_contra hne
      exact hx (hψs h hht (Function.mem_support.mpr hne))
    have h2 : φ.toFun x = 0 := by
      by_contra hne
      exact hx (hφ (Function.mem_support.mpr hne))
    rw [h1, h2, sub_self, abs_zero]
    exact hε.le

/-- A real number bounded by `ε * C` for every `ε > 0`, with `C ≥ 0`, vanishes. -/
theorem countable_test_eq_zero_of_norm_le {a C : ℝ} (hC : 0 ≤ C)
    (h : ∀ ε : ℝ, 0 < ε → ‖a‖ ≤ ε * C) : a = 0 := by
  have hle : ‖a‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
    have h1 := h _ hδ
    have h2 : ε / (C + 1) * C ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  exact norm_eq_zero.mp (le_antisymm hle (norm_nonneg a))

/-- Uniform approximation on a common ball, with local integrability, makes the
pairing with `f` vanish: the zero-test hypothesis forces `∫ g * f = 0` for each `g`. -/
theorem countable_test_ae_eq_zero {d : ℕ}
    (u : ℕ → SmoothCompactTest d)
    (hdense : ∀ φ : SmoothCompactTest d, ∃ R : ℝ, 0 < R ∧
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        Function.support (u n).toFun ⊆ Metric.closedBall 0 R ∧
        Function.support φ.toFun ⊆ Metric.closedBall 0 R ∧
        ∀ x, |(u n).toFun x - φ.toFun x| ≤ ε)
    (f : Vec d → ℝ) (hf : LocallyIntegrable f volume)
    (hz : ∀ n, (∫ x, (u n).toFun x * f x ∂volume) = 0) :
    f =ᵐ[volume] 0 := by
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hf
  intro g hg hgc
  simp only [smul_eq_mul]
  obtain ⟨R, _hR, happ⟩ := hdense ⟨g, hg, hgc⟩
  have hKc : IsCompact (Metric.closedBall (0 : Vec d) R) := isCompact_closedBall 0 R
  have hfK : IntegrableOn f (Metric.closedBall (0 : Vec d) R) volume :=
    hf.integrableOn_isCompact hKc
  have hnorm : Integrable ((Metric.closedBall (0 : Vec d) R).indicator fun x => ‖f x‖) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr (Integrable.norm hfK)
  have hgi : Integrable (fun x => g x * f x) volume := by
    simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hg.continuous hgc
  have hbound : ∀ ε : ℝ, 0 < ε → ‖∫ x, g x * f x ∂volume‖ ≤
      ε * ∫ x, (Metric.closedBall (0 : Vec d) R).indicator (fun x => ‖f x‖) x ∂volume := by
    intro ε hε
    obtain ⟨n, hsu, hsg, hclose⟩ := happ ε hε
    have hclose' : ∀ x, |(u n).toFun x - g x| ≤ ε := hclose
    have hsg' : Function.support g ⊆ Metric.closedBall (0 : Vec d) R := hsg
    have hsu' : Function.support (u n).toFun ⊆ Metric.closedBall (0 : Vec d) R := hsu
    have hui : Integrable (fun x => (u n).toFun x * f x) volume := by
      simpa [smul_eq_mul] using
        hf.integrable_smul_left_of_hasCompactSupport (u n).smooth.continuous (u n).compact
    have hsplit : ∫ x, (g x - (u n).toFun x) * f x ∂volume = ∫ x, g x * f x ∂volume := by
      simp only [sub_mul]
      rw [integral_sub hgi hui, hz n, sub_zero]
    have hpt : ∀ x, ‖(g x - (u n).toFun x) * f x‖ ≤
        ε * (Metric.closedBall (0 : Vec d) R).indicator (fun x => ‖f x‖) x := by
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : Vec d) R
      · rw [Set.indicator_of_mem hx]
        show ‖(g x - (u n).toFun x) * f x‖ ≤ ε * ‖f x‖
        have h1 : |(u n).toFun x - g x| * ‖f x‖ ≤ ε * ‖f x‖ :=
          mul_le_mul_of_nonneg_right (hclose' x) (norm_nonneg _)
        rw [norm_mul, Real.norm_eq_abs (g x - (u n).toFun x), abs_sub_comm]
        exact h1
      · have hg0 : g x = 0 := by
          by_contra h
          have hmem : x ∈ Function.support g := Function.mem_support.mpr h
          exact hx (hsg' hmem)
        have hu0 : (u n).toFun x = 0 := by
          by_contra h
          have hmem : x ∈ Function.support (u n).toFun := Function.mem_support.mpr h
          exact hx (hsu' hmem)
        rw [Set.indicator_of_notMem hx, hg0, hu0]
        simp
    have hnb := norm_integral_le_of_norm_le (hnorm.const_mul ε) (ae_of_all _ hpt)
    rw [integral_const_mul, hsplit] at hnb
    exact hnb
  have hC0 : 0 ≤ ∫ x, (Metric.closedBall (0 : Vec d) R).indicator (fun x => ‖f x‖) x ∂volume :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => norm_nonneg _) x
  exact countable_test_eq_zero_of_norm_le hC0 hbound

/-- A countable family of smooth tests is uniformly dense in the following sense: every
smooth test is approximated, uniformly on a common ball, by members of the family.
Union over the radii `m + 1` of the countable nets from `countable_test_ball_net`, plus the zero
test, enumerated by `ℕ`. -/
theorem countable_test_uniform_approx (d : ℕ) :
    ∃ u : ℕ → SmoothCompactTest d, ∀ φ : SmoothCompactTest d,
      ∃ R : ℝ, 0 < R ∧ ∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        Function.support (u n).toFun ⊆ Metric.closedBall 0 R ∧
        Function.support φ.toFun ⊆ Metric.closedBall 0 R ∧
        ∀ x, |(u n).toFun x - φ.toFun x| ≤ ε := by
  choose P hPc hPapprox using countable_test_ball_net d
  obtain ⟨u, hu⟩ := ((Set.countable_singleton (countableTestZero d)).union
    (Set.countable_iUnion hPc)).exists_eq_range
      ⟨countableTestZero d, Set.mem_union_left _ (Set.mem_singleton _)⟩
  refine ⟨u, fun φ => ?_⟩
  obtain ⟨R0, hR0⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    (φ.compact.isCompact).isBounded
  obtain ⟨m, hm⟩ := exists_nat_ge R0
  have hRm : R0 ≤ (m : ℝ) + 1 := by linarith
  have hsupp : Function.support φ.toFun ⊆ Metric.closedBall 0 ((m : ℝ) + 1) :=
    (subset_tsupport φ.toFun).trans (hR0.trans (Metric.closedBall_subset_closedBall hRm))
  refine ⟨(m : ℝ) + 1, by positivity, fun ε hε => ?_⟩
  obtain ⟨ψ, hψP, hψs, hψε⟩ := hPapprox m φ hsupp ε hε
  have hψu : ψ ∈ Set.range u := by
    rw [← hu]
    exact Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨m, hψP⟩)
  obtain ⟨n, hn⟩ := hψu
  refine ⟨n, ?_, hsupp, fun x => ?_⟩
  · rw [hn]
    exact hψs
  · rw [hn]
    exact hψε x

theorem exists_countable_locally_integrable_zero_tests (d : ℕ) :
    ∃ u : ℕ → SmoothCompactTest d,
    ∀ (f : Vec d → ℝ), LocallyIntegrable f volume →
    (∀ n, (∫ x, (u n).toFun x * f x ∂volume) = 0) → f =ᵐ[volume] 0 := by
  obtain ⟨u, hu⟩ := countable_test_uniform_approx d
  exact ⟨u, fun f hf hz => countable_test_ae_eq_zero u hu f hf hz⟩

end EinsteinRelation.Environment.AKMTestIntegralSupport
