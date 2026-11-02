import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Simultaneous `L²(ν)` and `L¹(μ)` approximation by bounded continuous functions

If `μ ≪ ν` are finite Borel measures on a pseudo-metrizable space and
`∫ ‖g‖ dμ ≤ K ‖g‖_{L²(ν)}` for every bounded continuous complex `g`, then every `F ∈ L²(ν)` is the
`ν`-a.e. limit of bounded continuous `h n` with `h n → F` in `L²(ν)` and `∫ ‖F - h n‖ dμ → 0`
(Fatou, with the `μ`-a.e. convergence inherited from `μ ≪ ν`).
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

variable {Ω : Type*} [TopologicalSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- Bounded continuous approximants converging in `L²` and almost everywhere. -/
theorem exists_cb_seq_ae (ν : Measure Ω) [IsFiniteMeasure ν] (F : MeasureTheory.Lp ℂ 2 ν) :
    ∃ h : ℕ → Ω →ᵇ ℂ, (∀ᵐ x ∂ν, Tendsto (fun n => h n x) atTop (𝓝 (F x))) ∧
      Tendsto (fun n => eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 ν) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ g : Ω →ᵇ ℂ,
      eLpNorm ((F : Ω → ℂ) - (g : Ω → ℂ)) 2 ν ≤ ENNReal.ofReal (1 / ((n : ℝ) + 1)) := fun n => by
    obtain ⟨g, hg, _⟩ := (MeasureTheory.Lp.memLp F).exists_boundedContinuous_eLpNorm_sub_le
      (p := 2) (by norm_num) (ε := ENNReal.ofReal (1 / ((n : ℝ) + 1)))
      (ENNReal.ofReal_pos.2 (by positivity)).ne'
    exact ⟨g, hg⟩
  choose g hg using hex
  have hε : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n => eLpNorm ((F : Ω → ℂ) - (g n : Ω → ℂ)) 2 ν) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun n => zero_le) hg
  have hinm : TendstoInMeasure ν (fun n => (g n : Ω → ℂ)) atTop (F : Ω → ℂ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      (hlim.congr fun n => eLpNorm_sub_comm _ _ 2 ν)
  obtain ⟨ns, hns, hae⟩ := hinm.exists_seq_tendsto_ae
  exact ⟨fun i => g (ns i), hae, hlim.comp hns.tendsto_atTop⟩

/-- Simultaneous `L²(ν)`/`L¹(μ)` approximation of an `L²(ν)` class by bounded continuous functions. -/
theorem exists_cb_seq_lintegral (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (K : ℝ≥0∞) (hK : K ≠ ∞)
    (hB : ∀ g : Ω →ᵇ ℂ, ∫⁻ x, ‖g x‖ₑ ∂μ ≤ K * eLpNorm (g : Ω → ℂ) 2 ν)
    (F : MeasureTheory.Lp ℂ 2 ν) :
    ∃ h : ℕ → Ω →ᵇ ℂ, Tendsto (fun n => ∫⁻ x, ‖F x - h n x‖ₑ ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 ν) atTop (𝓝 0) := by
  obtain ⟨h, hae, hlim⟩ := exists_cb_seq_ae ν F
  have hae' : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 (F x)) := hμν.ae_le hae
  set a : ℕ → ℝ≥0∞ := fun n => eLpNorm ((F : Ω → ℂ) - (h n : Ω → ℂ)) 2 ν with ha
  have hmeas : ∀ m n : ℕ, Measurable fun x => ‖h m x - h n x‖ₑ := fun m n =>
    (continuous_enorm.comp ((h m).continuous.sub (h n).continuous)).measurable
  have hclaim : ∀ n, ∫⁻ x, ‖F x - h n x‖ₑ ∂μ ≤ K * a n := fun n => by
    have hpt : ∀ m, ∫⁻ x, ‖h m x - h n x‖ₑ ∂μ ≤ K * (a n + a m) := fun m => by
      have e : ((h m - h n : Ω →ᵇ ℂ) : Ω → ℂ) =
          ((F : Ω → ℂ) - (h n : Ω → ℂ)) - ((F : Ω → ℂ) - (h m : Ω → ℂ)) := by
        funext x
        simp only [BoundedContinuousFunction.coe_sub, Pi.sub_apply]
        ring
      have h1 : ∫⁻ x, ‖h m x - h n x‖ₑ ∂μ ≤
          K * eLpNorm ((h m - h n : Ω →ᵇ ℂ) : Ω → ℂ) 2 ν := hB (h m - h n)
      have h2 : eLpNorm ((h m - h n : Ω →ᵇ ℂ) : Ω → ℂ) 2 ν ≤ a n + a m := by
        rw [e]
        exact eLpNorm_sub_le (p := 2) (by norm_num)
      exact h1.trans (mul_le_mul' le_rfl h2)
    have hlimit : Tendsto (fun m => K * (a n + a m)) atTop (𝓝 (K * (a n + 0))) :=
      ENNReal.Tendsto.const_mul (tendsto_const_nhds.add hlim) (Or.inr hK)
    calc ∫⁻ x, ‖F x - h n x‖ₑ ∂μ
        = ∫⁻ x, liminf (fun m => ‖h m x - h n x‖ₑ) atTop ∂μ := by
          refine lintegral_congr_ae (hae'.mono fun x hx => ?_)
          have ht : Tendsto (fun m => ‖h m x - h n x‖ₑ) atTop (𝓝 ‖F x - h n x‖ₑ) :=
            (continuous_enorm.tendsto _).comp (hx.sub tendsto_const_nhds)
          exact ht.liminf_eq.symm
      _ ≤ liminf (fun m => ∫⁻ x, ‖h m x - h n x‖ₑ ∂μ) atTop :=
          lintegral_liminf_le fun m => hmeas m n
      _ ≤ liminf (fun m => K * (a n + a m)) atTop :=
          liminf_le_liminf (Eventually.of_forall hpt)
      _ = K * (a n + 0) := hlimit.liminf_eq
      _ = K * a n := by rw [add_zero]
  refine ⟨h, ?_, hlim⟩
  have hK0 : Tendsto (fun n => K * a n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim (Or.inr hK)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hK0
    (fun n => zero_le) hclaim

end EinsteinFull
