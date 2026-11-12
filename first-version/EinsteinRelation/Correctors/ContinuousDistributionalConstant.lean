import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Auxiliary scalar estimates; source `paper/main.tex:699–753,808–848`. -/

open MeasureTheory
open scoped Topology
namespace EinsteinRelation.Correctors

theorem eqOn_const_of_smooth_test_pairings {a b c : ℝ} (hab : a < b)
    (U : ℝ → ℝ) (hU : ContinuousOn U (Set.Icc a b))
    (htest : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Set.Ioo a b → (∫ t : ℝ, η t * (U t-c)) = 0) :
    Set.EqOn U (fun _ => c) (Set.Icc a b) := by
  -- `U - c` is continuous and locally integrable on the open interval `(a, b)`.
  have hfc : ContinuousOn (fun t => U t - c) (Set.Ioo a b) :=
    (hU.mono Set.Ioo_subset_Icc_self).sub continuousOn_const
  have hloc : LocallyIntegrableOn (fun t => U t - c) (Set.Ioo a b) volume :=
    hfc.locallyIntegrableOn measurableSet_Ioo
  have hopen : IsOpen (Set.Ioo a b) := isOpen_Ioo
  -- The full-space pairings give `U - c = 0` almost everywhere on `(a, b)`.
  have hae : ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → U x - c = 0 :=
    hopen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun g hg hgc hgU => by
      simp only [smul_eq_mul]
      exact htest g hg hgc hgU)
  -- Continuity upgrades this to every point: the set where `U - c ≠ 0` inside
  -- `(a, b)` is open and null, hence empty.
  have hIoo : ∀ x ∈ Set.Ioo a b, U x - c = 0 := by
    intro x hx
    by_contra hne
    have hVopen : IsOpen (Set.Ioo a b ∩ (fun t => U t - c) ⁻¹' {0}ᶜ) :=
      hfc.isOpen_inter_preimage hopen isOpen_compl_singleton
    have hVpos : 0 < volume (Set.Ioo a b ∩ (fun t => U t - c) ⁻¹' {0}ᶜ) :=
      IsOpen.measure_pos volume hVopen ⟨x, hx, hne⟩
    have hVnull : volume (Set.Ioo a b ∩ (fun t => U t - c) ⁻¹' {0}ᶜ) = 0 := by
      refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae)
      have hy1 : y ∈ Set.Ioo a b := hy.1
      have hy2 : U y - c ≠ 0 := hy.2
      show ¬ (y ∈ Set.Ioo a b → U y - c = 0)
      exact fun himp => hy2 (himp hy1)
    exact hVpos.ne' hVnull
  -- The zero set of `U - c` on `[a, b]` is closed and contains `(a, b)`, hence its closure `[a, b]`.
  have hclosed : IsClosed (Set.Icc a b ∩ (fun t => U t - c) ⁻¹' {0}) :=
    (hU.sub continuousOn_const).preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hsub : closure (Set.Ioo a b) ⊆ Set.Icc a b ∩ (fun t => U t - c) ⁻¹' {0} :=
    closure_minimal (fun x hx => ⟨Set.Ioo_subset_Icc_self hx, hIoo x hx⟩) hclosed
  intro x hx
  have hx' : x ∈ closure (Set.Ioo a b) := by
    rw [closure_Ioo (ne_of_lt hab)]
    exact hx
  have h0 : U x - c = 0 := (hsub hx').2
  exact sub_eq_zero.mp h0

end EinsteinRelation.Correctors
