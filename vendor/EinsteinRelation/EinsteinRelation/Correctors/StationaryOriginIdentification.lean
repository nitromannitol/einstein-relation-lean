import EinsteinRelation.Correctors.ScalarMollifierApproximation
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Identifying a continuous orbit representative at the origin

Source: `paper/main.tex:693-698,727-729`. A spatial a.e. identity alone
does not identify an arbitrary representative at a specified point. For a
stationary measurable observable, the horizontal approximate identity has
an a.e. convergent subsequence. Every continuous local orbit representative
has the same mollifier limit, so its value at the origin agrees almost surely
with the environment observable. A bounded injective transform removes any
boundedness or moment hypothesis on that observable.
-/

open MeasureTheory Filter Topology

noncomputable section

namespace EinsteinRelation.Correctors

/-- Local continuity fixes the limit of literal orbit mollifications along
every nonzero sequence of scales tending to zero. -/
theorem tendsto_scalarMollifier_of_local_representative {d : ℕ}
    {F : FieldPair d → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀ ω, |F ω| ≤ M) {ε : ℕ → ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, ε n ≠ 0)
    (ω : FieldPair d) {U : Set (Vec d)} (hU : IsOpen U) (h0 : (0 : Vec d) ∈ U)
    {g : Vec d → ℝ} (hg : ContinuousAt g 0)
    (hrep : ∀ᵐ x ∂volume.restrict U, F (translate x ω) = g x) :
    Tendsto (fun n => ∫ x : Vec d, mollifier d x * F (translate (ε n • x) ω))
      atTop (𝓝 (g 0)) := by
  have hrep' : ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ U → F (translate x ω) = g x :=
    (ae_restrict_iff' hU.measurableSet).mp hrep
  have hpull : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ n,
      ε n • x ∈ U → F (translate (ε n • x) ω) = g (ε n • x) := by
    apply ae_all_iff.mpr
    intro n
    exact (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) (hε0 n)).ae hrep'
  have hint : Integrable (fun x : Vec d => mollifier d x * M) volume :=
    ((contDiff_mollifier d).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_mollifier d)).mul_const M
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun x : Vec d => mollifier d x * F (translate (ε n • x) ω)) volume := by
    have ht : Continuous (fun x : Vec d => translate (ε n • x) ω) :=
      Probability.continuous_translate.comp
        ((continuous_id.const_smul (ε n)).prodMk continuous_const)
    exact ((contDiff_mollifier d).continuous.measurable.mul
      (hF.comp ht.measurable)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖mollifier d x * F (translate (ε n • x) ω)‖ ≤ mollifier d x * M := by
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mollifier_nonneg d x)]
    exact mul_le_mul_of_nonneg_left (hM _) (mollifier_nonneg d x)
  have hlim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      Tendsto (fun n => mollifier d x * F (translate (ε n • x) ω))
        atTop (𝓝 (mollifier d x * g 0)) := by
    filter_upwards [hpull] with x hx
    have hxlim : Tendsto (fun n => ε n • x) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hε.smul_const x
    have hevent := hxlim.eventually (hU.mem_nhds h0)
    have heq : (fun n => F (translate (ε n • x) ω)) =ᶠ[atTop]
        fun n => g (ε n • x) := hevent.mono fun n hn => hx n hn
    exact ((hg.tendsto.comp hxlim).congr' heq.symm).const_mul (mollifier d x)
  have h := tendsto_integral_of_dominated_convergence
    (fun x : Vec d => mollifier d x * M) hm hint hb hlim
  simpa only [integral_mul_const, integral_mollifier, one_mul] using h

private theorem ae_origin_eq_of_bounded {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {F : FieldPair d → ℝ}
    (hF : Measurable F) {M : ℝ} (hM : ∀ ω, |F ω| ≤ M) :
    ∀ᵐ ω ∂Q, ∀ (U : Set (Vec d)), IsOpen U → (0 : Vec d) ∈ U →
      ∀ (g : Vec d → ℝ), ContinuousAt g 0 →
        (∀ᵐ x ∂volume.restrict U, F (translate x ω) = g x) → g 0 = F ω := by
  have hmem : MemLp F 2 Q := MemLp.of_bound hF.aestronglyMeasurable M
    (ae_of_all _ fun ω => by simpa only [Real.norm_eq_abs] using hM ω)
  obtain ⟨hS, hSconv⟩ := exists_scalarMollifier_Lp_approximation Q hQ hF ⟨M, hM⟩ hmem
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hconv := hSconv.comp hε
  obtain ⟨ns, hns, hpt⟩ := (tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  have heq : ∀ᵐ ω ∂Q, ∀ n,
      (hS (ε (ns n))).toLp
        (fun ω => ∫ x : Vec d, mollifier d x * F (translate (ε (ns n) • x) ω)) ω =
      ∫ x : Vec d, mollifier d x * F (translate (ε (ns n) • x) ω) :=
    ae_all_iff.mpr fun n => (hS (ε (ns n))).coeFn_toLp
  filter_upwards [hpt, heq, hmem.coeFn_toLp] with ω hptω heqω hFω
  intro U hU h0 g hg hrep
  have hlim := tendsto_scalarMollifier_of_local_representative hF hM
    (hε.comp hns.tendsto_atTop) (fun n => by dsimp [ε]; positivity) ω hU h0 hg hrep
  have hlim' : Tendsto
      (fun n => ∫ x : Vec d, mollifier d x * F (translate (ε (ns n) • x) ω))
      atTop (𝓝 (F ω)) := by
    rw [← hFω]
    exact hptω.congr fun n => heqω n
  exact tendsto_nhds_unique hlim hlim'

/-- A stationary measurable observable agrees almost surely at the origin
with every continuous local spatial representative. The full-measure event
depends only on the observable, not on a choice of representatives. -/
theorem ae_origin_eq_of_continuous_representative {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {F : FieldPair d → ℝ} (hF : Measurable F) :
    ∀ᵐ ω ∂Q, ∀ (U : Set (Vec d)), IsOpen U → (0 : Vec d) ∈ U →
      ∀ (g : Vec d → ℝ), ContinuousAt g 0 →
        (∀ᵐ x ∂volume.restrict U, F (translate x ω) = g x) → g 0 = F ω := by
  have hm : Measurable (fun ω => Real.arctan (F ω)) :=
    Real.continuous_arctan.measurable.comp hF
  have hb (ω : FieldPair d) : |Real.arctan (F ω)| ≤ Real.pi / 2 :=
    (abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le,
      (Real.arctan_lt_pi_div_two _).le⟩)
  filter_upwards [ae_origin_eq_of_bounded Q hQ hm hb] with ω hω
  intro U hU h0 g hg hrep
  apply Real.arctan_injective
  exact hω U hU h0 (fun x => Real.arctan (g x))
    (Real.continuous_arctan.continuousAt.comp hg)
    (hrep.mono fun x hx => congrArg Real.arctan hx)

end EinsteinRelation.Correctors

