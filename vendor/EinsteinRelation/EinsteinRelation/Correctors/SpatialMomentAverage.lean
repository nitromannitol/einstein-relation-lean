import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-! Spatial `L²` averages inherit uniform probabilistic moments.

Source anchors: paper/main.tex, lines 834–838 and 845–876 (spatial averages of gradients and
copy gradients). Let `Q` be the environment or copy probability on `Ω` and `ν` a probability
measure on the spatial space `X`, for example a normalized ball volume. For a jointly measurable
`g : Ω × X → EuclideanSpace ℝ ι` with uniform pointwise finite `p`-moments and `2 ≤ p`:

* for `Q`-a.e. `ω`, the section `x ↦ g (ω, x)` lies in `L²(ν)`;
* the spatial root-mean-square `ω ↦ √(∫ ‖g (ω, x)‖² dν)` lies in `L^p(Q)` with norm at most `C`.

Proof: Tonelli gives the joint `p`-th moment bound, finiteness of the spatial `p`-moment holds
`Q`-a.e., monotonicity of `L^q` norms in the exponent on the probability space `ν` gives the
`L²(ν)` membership and the Jensen-type bound, and integration against `Q` gives the `C` bound.
No independence, continuity, spatial compactness, derivative, PDE, or normalization premise is
used. Nothing is claimed for `p < 2`, which needs a separate moment embedding.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- Raising an `ℝ≥0∞` inequality `a ≤ b ^ (1/q)` to the power `q` gives `a ^ q ≤ b`. -/
private theorem spatialAvg_rpow_le_of_le_inv {a b : ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    (h : a ≤ b ^ (1 / q)) : a ^ q ≤ b := by
  calc a ^ q ≤ (b ^ (1 / q)) ^ q := ENNReal.rpow_le_rpow h hq.le
    _ = b := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The converse direction: `a ^ (1/q) ≤ b` gives `a ≤ b ^ q`. -/
private theorem spatialAvg_le_rpow_of_inv_le {a b : ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    (h : a ^ (1 / q) ≤ b) : a ≤ b ^ q := by
  have ha : (a ^ (1 / q)) ^ q = a := by
    rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]
  calc a = (a ^ (1 / q)) ^ q := ha.symm
    _ ≤ b ^ q := ENNReal.rpow_le_rpow h hq.le

/-- Taking the `1/q` power of `a ≤ b ^ q` gives `a ^ (1/q) ≤ b`. -/
private theorem spatialAvg_inv_le_of_le_rpow {a b : ℝ≥0∞} {q : ℝ} (hq : 0 < q)
    (h : a ≤ b ^ q) : a ^ (1 / q) ≤ b := by
  calc a ^ (1 / q) ≤ (b ^ q) ^ (1 / q) := ENNReal.rpow_le_rpow h (one_div_pos.mpr hq).le
    _ = b := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one]

/-- The squared Euclidean norm, as an `ℝ≥0∞` rpow of the extended norm. -/
private theorem spatialAvg_ofReal_sq_eq_enorm_rpow {E : Type*} [NormedAddCommGroup E] (v : E) :
    ENNReal.ofReal (‖v‖ ^ 2) = ‖v‖ₑ ^ (2 : ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg v), ofReal_norm]

/-- Spatial `L²` averages of a jointly measurable Euclidean-valued field with uniform pointwise
finite `p`-moments, `2 ≤ p`: the spatial energy is `Q`-a.e. in `L²(ν)`, and the spatial
root-mean-square has `L^p(Q)` norm at most `C`. Source anchors: paper/main.tex, lines 834–838 and
845–876. -/
theorem spatialL2_average_moment_le :
    ∀ {Ω X ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [Fintype ι] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [IsProbabilityMeasure ν] {p C : ℝ}, 2 ≤ p → 0 ≤ C →
    ∀ g : Ω × X → EuclideanSpace ℝ ι, Measurable g →
    (∀ x, MemLp (fun ω => g (ω,x)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => g (ω,x)) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) →
    (∀ᵐ ω ∂Q, MemLp (fun x => g (ω,x)) 2 ν) ∧
    MemLp (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖^2 ∂ν)) (ENNReal.ofReal p) Q ≤
      ENNReal.ofReal C := by
  intro Ω X ι instΩ instX instι Q instQ ν instν p C hp hC g hg hmom
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_two hp
  have hPt : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp0.le
  have hP0 : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp0).ne'
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have h2P : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  -- Tonelli: the joint `p`-th moment has `Q`-integral at most `C ^ p`.
  have hgm : Measurable (fun z : Ω × X => ‖g z‖ₑ ^ p) := hg.enorm.pow_const p
  have hGm : Measurable (fun ω => ∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) :=
    hgm.lintegral_prod_right' (ν := ν)
  have hswap : ∫⁻ ω, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) ∂Q =
      ∫⁻ x, (∫⁻ ω, ‖g (ω,x)‖ₑ ^ p ∂Q) ∂ν :=
    lintegral_lintegral_swap (μ := Q) (ν := ν) (f := fun ω x => ‖g (ω,x)‖ₑ ^ p)
      hgm.aemeasurable
  have hcol : ∀ x : X, ∫⁻ ω, ‖g (ω,x)‖ₑ ^ p ∂Q ≤ ENNReal.ofReal (C ^ p) := by
    intro x
    have h := (hmom x).2
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop (hmom x).1.aestronglyMeasurable,
      hPt] at h
    rw [← ENNReal.ofReal_rpow_of_nonneg hC hp0.le]
    exact spatialAvg_le_rpow_of_inv_le hp0 h
  have hGint : ∫⁻ ω, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) ∂Q ≤ ENNReal.ofReal (C ^ p) := by
    rw [hswap]
    calc ∫⁻ x, (∫⁻ ω, ‖g (ω,x)‖ₑ ^ p ∂Q) ∂ν ≤ ∫⁻ _x, ENNReal.ofReal (C ^ p) ∂ν :=
          lintegral_mono fun x => hcol x
      _ = ENNReal.ofReal (C ^ p) := by rw [lintegral_const, measure_univ, mul_one]
  -- The spatial `p`-moment is finite `Q`-a.e.
  have hGtop : ∀ᵐ ω ∂Q, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) < ⊤ :=
    ae_lt_top hGm (lt_of_le_of_lt hGint ENNReal.ofReal_lt_top).ne
  -- A finite spatial `p`-moment gives `L^p(ν)` membership, hence `L²(ν)` on a probability space.
  have hspP : ∀ ω, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) < ⊤ →
      MemLp (fun x => g (ω,x)) (ENNReal.ofReal p) ν := by
    intro ω hω
    have hmω : AEStronglyMeasurable (fun x => g (ω,x)) ν :=
      (hg.comp (measurable_prodMk_left (x := ω))).stronglyMeasurable.aestronglyMeasurable
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hmω, hPt]
    exact ENNReal.rpow_lt_top_of_nonneg (one_div_nonneg.mpr hp0.le) hω.ne
  have hsp2 : ∀ ω, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) < ⊤ → MemLp (fun x => g (ω,x)) 2 ν :=
    fun ω hω => (hspP ω hω).mono_exponent h2P
  -- Statement (1): the spatial energy is `L²(ν)` for `Q`-a.e. `ω`.
  have hAE : ∀ᵐ ω ∂Q, MemLp (fun x => g (ω,x)) 2 ν := by
    filter_upwards [hGtop] with ω hω
    exact hsp2 ω hω
  -- Measurability of the spatial root-mean-square.
  have hsq : Measurable (fun z : Ω × X => ‖g z‖ ^ 2) := hg.norm.pow_const 2
  have hIm : StronglyMeasurable (fun ω => ∫ x, ‖g (ω,x)‖ ^ 2 ∂ν) :=
    hsq.stronglyMeasurable.integral_prod_right' (ν := ν)
  have hSm : Measurable (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)) :=
    hIm.measurable.sqrt
  -- Jensen-type bound, on the event where the spatial `p`-moment is finite.
  have hbd : ∀ ω, (∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν) < ⊤ →
      ‖Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)‖ₑ ^ p ≤ ∫⁻ x, ‖g (ω,x)‖ₑ ^ p ∂ν := by
    intro ω hω
    have hsp := hsp2 ω hω
    have hint : Integrable (fun x => ‖g (ω,x)‖ ^ 2) ν :=
      (memLp_two_iff_integrable_sq_norm hsp.aestronglyMeasurable).mp hsp
    have hnn : (0 : X → ℝ) ≤ᵐ[ν] (fun x => ‖g (ω,x)‖ ^ 2) :=
      ae_of_all _ fun x => sq_nonneg _
    have hI0 : 0 ≤ ∫ x, ‖g (ω,x)‖ ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg _
    have hI : ENNReal.ofReal (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν) = ∫⁻ x, ‖g (ω,x)‖ₑ ^ (2 : ℝ) ∂ν := by
      rw [ofReal_integral_eq_lintegral_ofReal hint hnn]
      exact lintegral_congr fun x => spatialAvg_ofReal_sq_eq_enorm_rpow (g (ω,x))
    have hmono : eLpNorm (fun x => g (ω,x)) 2 ν ≤
        eLpNorm (fun x => g (ω,x)) (ENNReal.ofReal p) ν :=
      eLpNorm_le_eLpNorm_of_exponent_le h2P
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
        hsp.aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop (hspP ω hω).aestronglyMeasurable]
      at hmono
    simp only [ENNReal.toReal_ofNat, hPt] at hmono
    have hnorm : ‖Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)‖ₑ =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)) := by
      rw [← ofReal_norm, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    have hS : ENNReal.ofReal (Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)) =
        ENNReal.ofReal (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.ofReal_rpow_of_nonneg hI0 (by norm_num : (0 : ℝ) ≤ 1 / 2),
        Real.sqrt_eq_rpow]
    rw [hnorm, hS, hI]
    exact spatialAvg_rpow_le_of_le_inv hp0 hmono
  -- Integration over `Q` gives the `C` bound; no division by a possibly zero integral occurs.
  have hlint : ∫⁻ ω, (‖Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)‖ₑ ^ p) ∂Q ≤
      ENNReal.ofReal (C ^ p) :=
    (lintegral_mono_ae (hGtop.mono fun ω hω => hbd ω hω)).trans hGint
  have hfin : eLpNorm (fun ω => Real.sqrt (∫ x, ‖g (ω,x)‖ ^ 2 ∂ν)) (ENNReal.ofReal p) Q ≤
      ENNReal.ofReal C := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hP0 hPtop hSm.aestronglyMeasurable, hPt]
    refine spatialAvg_inv_le_of_le_rpow hp0 ?_
    rw [ENNReal.ofReal_rpow_of_nonneg hC hp0.le]
    exact hlint
  exact ⟨hAE, lt_of_le_of_lt hfin ENNReal.ofReal_lt_top, hfin⟩

end EinsteinRelation.Correctors
