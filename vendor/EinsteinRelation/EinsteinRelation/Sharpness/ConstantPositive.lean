import EinsteinRelation.Calculus.HorizontalCore
import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Sharpness.Energy
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Positivity of the sharpness constant under translation ergodicity

Source `paper/main.tex:1262–1265`, Proposition 7.1, Step 4. The constant is
`c = δ E[|∇ψ|² / (1 + ∂₁ψ)]`, and the paper asserts its strict positivity "because `h` is
nonconstant and its stationary law is ergodic". Here `Q` is a stationary, translation ergodic
probability law on coefficient pairs, and `ψ` is measurable with smooth translation orbits
`x ↦ ψ (translate x ω)` whose Euclidean orbit gradient has norm at most `1/4`.

Two facts are proved:
* if the mean squared orbit gradient at the origin vanishes, then `ψ` is `Q`-almost surely
  constant (`ae_const_of_integral_gradSq_eq_zero`);
* if `ψ` is not `Q`-almost surely constant, the mean sharp energy
  `|∇ψ|² / (1 + ∂₁ψ)` is strictly positive (`integral_sharpEnergy_pos`), so `c > 0`
  for every `δ > 0` (`sharpConstant_pos`).
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Each squared coordinate is at most the squared Euclidean norm. -/
private theorem sqCoord_le_euclideanSq {d : ℕ} (v : Vec d) (i : Fin d) :
    v i * v i ≤ euclideanSq v := by
  unfold euclideanSq dot
  exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)

/-- Each coordinate is bounded in absolute value by the Euclidean norm. -/
private theorem abs_coord_le_euclideanNorm {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact sqCoord_le_euclideanSq v i

/-- A vector of Euclidean norm at most `1/4` has squared Euclidean norm at most `1/16`. -/
private theorem euclideanSq_le_sixteenth {d : ℕ} (v : Vec d) (hv : euclideanNorm v ≤ 1 / 4) :
    euclideanSq v ≤ 1 / 16 := by
  have h0 : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _
  have hsq : euclideanNorm v ^ 2 = euclideanSq v := Real.sq_sqrt (euclideanSq_nonneg v)
  nlinarith [mul_nonneg h0 (sub_nonneg.mpr hv)]

/-- Under the gradient bound, the denominator `1 + gᵢ` of the sharp energy is positive. -/
private theorem one_add_coord_pos {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : 0 < 1 + g i := by
  have hlo := (abs_le.mp ((abs_coord_le_euclideanNorm g i).trans hg)).1
  linarith

/-- Under the gradient bound, the sharp energy dominates `4/5` times the squared norm. -/
private theorem four_fifths_mul_le_sharpEnergy {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : 4 / 5 * euclideanSq g ≤ sharpEnergy i g := by
  have hj := one_add_coord_pos i g hg
  have hhi := (abs_le.mp ((abs_coord_le_euclideanNorm g i).trans hg)).2
  rw [sharpEnergy, le_div_iff₀ hj]
  nlinarith [mul_nonneg (euclideanSq_nonneg g) (sub_nonneg.mpr hhi)]

/-- Under the gradient bound, the sharp energy is at most `1/12`. -/
private theorem sharpEnergy_le_twelfth {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : sharpEnergy i g ≤ 1 / 12 := by
  have hj := one_add_coord_pos i g hg
  have hlo := (abs_le.mp ((abs_coord_le_euclideanNorm g i).trans hg)).1
  have hE := euclideanSq_le_sixteenth g hg
  rw [sharpEnergy, div_le_iff₀ hj]
  linarith

/-- A vector with vanishing squared Euclidean norm is zero. -/
private theorem eq_zero_of_euclideanSq_eq_zero {d : ℕ} {v : Vec d}
    (h : euclideanSq v = 0) : v = 0 := by
  by_contra hv
  have hpos : 0 < euclideanSq v := (euclideanSq_pos_iff v).mpr hv
  linarith

/-- Orbits of a smooth observable are differentiable at the origin. -/
private theorem differentiableAt_orbit_zero {d : ℕ} {ψ : FieldPair d → ℝ}
    (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω)) (ω : FieldPair d) :
    DifferentiableAt ℝ (orbit ψ ω) 0 :=
  ((hsmooth ω).differentiable (by simp)).differentiableAt

/-- The squared orbit gradient at the origin is measurable in the sample. -/
private theorem measurable_gradSq_zero {d : ℕ} {ψ : FieldPair d → ℝ} (hψ : Measurable ψ)
    (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω)) :
    Measurable (fun ω : FieldPair d => euclideanSq (gradient (orbit ψ ω) 0)) := by
  have hd : ∀ i : Fin d, Measurable (horizontalDerivative i ψ) := fun i =>
    measurable_horizontalDerivative i ψ hψ (differentiableAt_orbit_zero hsmooth)
  have hsum : Measurable (fun ω : FieldPair d =>
      ∑ i, horizontalDerivative i ψ ω * horizontalDerivative i ψ ω) :=
    Finset.measurable_sum Finset.univ fun i _ => (hd i).mul (hd i)
  exact hsum

/-- The sharp energy of the orbit gradient at the origin is measurable in the sample. -/
private theorem measurable_sharpEnergy_orbit {d : ℕ} (i : Fin d) {ψ : FieldPair d → ℝ}
    (hψ : Measurable ψ) (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω)) :
    Measurable (fun ω : FieldPair d => sharpEnergy i (gradient (orbit ψ ω) 0)) := by
  have hd : Measurable (horizontalDerivative i ψ) :=
    measurable_horizontalDerivative i ψ hψ (differentiableAt_orbit_zero hsmooth)
  have hden : Measurable (fun ω : FieldPair d => 1 + horizontalDerivative i ψ ω) :=
    measurable_const.add hd
  exact (measurable_gradSq_zero hψ hsmooth).div hden

/-- Under the gradient bound, the squared orbit gradient at the origin is integrable. -/
private theorem integrable_gradSq_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] {ψ : FieldPair d → ℝ} (hψ : Measurable ψ)
    (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω))
    (hgrad : ∀ ω x, euclideanNorm (gradient (orbit ψ ω) x) ≤ 1 / 4) :
    Integrable (fun ω : FieldPair d => euclideanSq (gradient (orbit ψ ω) 0)) Q := by
  refine Integrable.of_bound (measurable_gradSq_zero hψ hsmooth).aestronglyMeasurable (1 / 16)
    (ae_of_all _ fun ω => ?_)
  show ‖euclideanSq (gradient (orbit ψ ω) 0)‖ ≤ 1 / 16
  rw [Real.norm_eq_abs, abs_of_nonneg (euclideanSq_nonneg _)]
  exact euclideanSq_le_sixteenth _ (hgrad ω 0)

/-- Along a `C¹` function, the squared gradient is continuous in the spatial variable. -/
private theorem continuous_gradSq {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f) :
    Continuous (fun x => euclideanSq (gradient f x)) := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hcd : ∀ i : Fin d, Continuous (fun x => fderiv ℝ f x (unitVector i)) := fun i =>
    hfd.clm_apply continuous_const
  show Continuous (fun x => ∑ i, fderiv ℝ f x (unitVector i) * fderiv ℝ f x (unitVector i))
  exact continuous_finset_sum _ fun i _ => (hcd i).mul (hcd i)

/-- Translating the sample by `x` moves the orbit gradient at the origin to the orbit gradient
at `x`. -/
private theorem gradient_orbit_translate {d : ℕ} (ψ : FieldPair d → ℝ) (x : Vec d)
    (ω : FieldPair d) :
    gradient (orbit ψ (translate x ω)) 0 = gradient (orbit ψ ω) x := by
  funext i
  exact horizontalDerivative_translate i ψ ω x

/-- A `C¹` function whose squared gradient vanishes almost everywhere is constant. -/
private theorem const_of_ae_gradSq_eq_zero {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ 1 f)
    (hae : ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanSq (gradient f x) = 0) :
    ∀ x y, f x = f y := by
  have heq : (fun x => euclideanSq (gradient f x)) = fun _ => (0 : ℝ) :=
    ((continuous_gradSq hf).ae_eq_iff_eq volume continuous_const).mp hae
  have hgrad0 : ∀ x, gradient f x = 0 := fun x =>
    eq_zero_of_euclideanSq_eq_zero (congrFun heq x)
  have hfd : ∀ x, fderiv ℝ f x = 0 := by
    intro x
    refine ContinuousLinearMap.ext fun v => ?_
    have hv : v = ∑ i, v i • unitVector i := by
      ext j
      simp [unitVector, Finset.sum_apply, Pi.single_apply, mul_ite]
    rw [ContinuousLinearMap.zero_apply, hv, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hi : fderiv ℝ f x (unitVector i) = 0 := congrFun (hgrad0 x) i
    rw [map_smul, hi, smul_zero]
  exact fun x y => is_const_of_fderiv_eq_zero (hf.differentiable (by simp)) hfd x y

/-- A measurable real function all of whose sublevel sets have measure `0` or `1` is almost
surely constant. -/
private theorem ae_const_of_sublevel_zero_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ) (hf : Measurable f)
    (h01 : ∀ t : ℝ, μ {ω | f ω < t} = 0 ∨ μ {ω | f ω < t} = 1) :
    ∃ c : ℝ, ∀ᵐ ω ∂μ, f ω = c := by
  have hmono : ∀ s t : ℝ, s ≤ t → μ {ω | f ω < s} ≤ μ {ω | f ω < t} := fun s t hst =>
    measure_mono fun ω (hω : f ω < s) => lt_of_lt_of_le hω hst
  -- Some sublevel set has full measure, since the sublevel sets exhaust the space.
  have hup : ∃ T : ℝ, μ {ω | f ω < T} = 1 := by
    by_contra hcon
    push_neg at hcon
    have hnull : μ (⋃ n : ℕ, {ω | f ω < (n : ℝ)}) = 0 :=
      measure_iUnion_null fun n => (h01 (n : ℝ)).resolve_right (hcon (n : ℝ))
    have hU : (⋃ n : ℕ, {ω | f ω < (n : ℝ)}) = Set.univ := by
      refine Set.eq_univ_of_forall fun ω => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (f ω)
      exact Set.mem_iUnion.mpr ⟨n, hn⟩
    rw [hU, measure_univ] at hnull
    exact one_ne_zero hnull
  -- Some sublevel set is null, since the sublevel sets shrink to the empty set.
  have hdown : ∃ T : ℝ, μ {ω | f ω < T} = 0 := by
    by_contra hcon
    push_neg at hcon
    have hnull : ∀ n : ℕ, μ {ω | f ω < -(n : ℝ)}ᶜ = 0 := fun n => by
      have hm : MeasurableSet {ω | f ω < -(n : ℝ)} := measurableSet_lt hf measurable_const
      exact (prob_compl_eq_zero_iff hm).mpr ((h01 (-(n : ℝ))).resolve_left (hcon (-(n : ℝ))))
    have hU : (⋃ n : ℕ, {ω | f ω < -(n : ℝ)}ᶜ) = Set.univ := by
      refine Set.eq_univ_of_forall fun ω => ?_
      obtain ⟨n, hn⟩ := exists_nat_gt (-f ω)
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      show ¬ f ω < -(n : ℝ)
      exact not_lt.mpr (by linarith)
    have hnull' : μ (⋃ n : ℕ, {ω | f ω < -(n : ℝ)}ᶜ) = 0 := measure_iUnion_null hnull
    rw [hU, measure_univ] at hnull'
    exact one_ne_zero hnull'
  obtain ⟨T, hT⟩ := hup
  obtain ⟨T', hT'⟩ := hdown
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = sInf {t : ℝ | μ {ω | f ω < t} = 1} := ⟨_, rfl⟩
  have hSne : {t : ℝ | μ {ω | f ω < t} = 1}.Nonempty := ⟨T, hT⟩
  have hSbdd : BddBelow {t : ℝ | μ {ω | f ω < t} = 1} := by
    refine ⟨T', fun t ht => ?_⟩
    have ht' : μ {ω | f ω < t} = 1 := ht
    by_contra hlt
    push_neg at hlt
    have h1 := hmono t T' hlt.le
    rw [ht', hT'] at h1
    exact one_ne_zero (le_antisymm h1 zero_le)
  have hbelow : ∀ s : ℝ, s < c → μ {ω | f ω < s} = 0 := by
    intro s hs
    have hnot : ¬ μ {ω | f ω < s} = 1 := by
      intro h1
      have hle : c ≤ s := by
        rw [hc]
        exact csInf_le hSbdd (show s ∈ {t : ℝ | μ {ω | f ω < t} = 1} from h1)
      exact absurd hs (not_lt.mpr hle)
    exact (h01 s).resolve_right hnot
  have habove : ∀ s : ℝ, c < s → μ {ω | f ω < s} = 1 := by
    intro s hs
    have hb : sInf {t : ℝ | μ {ω | f ω < t} = 1} < s := by
      rw [← hc]
      exact hs
    obtain ⟨t, ht, hts⟩ := exists_lt_of_csInf_lt hSne hb
    have ht' : μ {ω | f ω < t} = 1 := ht
    have h1 := hmono t s hts.le
    rw [ht'] at h1
    exact le_antisymm prob_le_one h1
  have hc0 : μ {ω | f ω < c} = 0 := by
    have hsub : {ω | f ω < c} ⊆ ⋃ n : ℕ, {ω | f ω < c - 1 / ((n : ℝ) + 1)} := by
      intro ω hω
      have hω' : f ω < c := hω
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hω')
      exact Set.mem_iUnion.mpr ⟨n, by show f ω < c - 1 / ((n : ℝ) + 1); linarith⟩
    have hn : ∀ n : ℕ, μ {ω | f ω < c - 1 / ((n : ℝ) + 1)} = 0 := by
      intro n
      apply hbelow
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    exact measure_mono_null hsub (measure_iUnion_null hn)
  refine ⟨c, ?_⟩
  rw [ae_iff]
  have hsub : {ω | ¬ f ω = c} ⊆
      {ω | f ω < c} ∪ ⋃ n : ℕ, {ω | c + 1 / ((n : ℝ) + 1) ≤ f ω} := by
    intro ω hω
    have hω' : f ω ≠ c := hω
    by_cases hlt : f ω < c
    · exact Set.mem_union_left _ hlt
    · have hgt : c < f ω := lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hω')
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hgt)
      refine Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨n, ?_⟩)
      show c + 1 / ((n : ℝ) + 1) ≤ f ω
      linarith
  have hup_n : ∀ n : ℕ, μ {ω | c + 1 / ((n : ℝ) + 1) ≤ f ω} = 0 := by
    intro n
    have hm : MeasurableSet {ω | f ω < c + 1 / ((n : ℝ) + 1)} :=
      measurableSet_lt hf measurable_const
    have hset : {ω | c + 1 / ((n : ℝ) + 1) ≤ f ω} =
        {ω | f ω < c + 1 / ((n : ℝ) + 1)}ᶜ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [hset, prob_compl_eq_zero_iff hm]
    apply habove
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  exact measure_mono_null hsub (measure_union_null hc0 (measure_iUnion_null hup_n))

/-- The joint shift map `(x, ω) ↦ translate x ω` is measurable. -/
private theorem measurable_translate_pair {d : ℕ} :
    Measurable (fun p : Vec d × FieldPair d => translate p.1 p.2) :=
  EinsteinRelation.Probability.continuous_translate.measurable

/-- A real function whose nonnegative part has zero lower integral vanishes almost everywhere. -/
private theorem ae_eq_zero_of_lintegral_ofReal_eq_zero {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {h : α → ℝ} (hh : Measurable h) (hnn : ∀ x, 0 ≤ h x)
    (h0 : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = 0) : ∀ᵐ x ∂μ, h x = 0 := by
  filter_upwards [(lintegral_eq_zero_iff hh.ennreal_ofReal).mp h0] with x hx
  have hx' : ENNReal.ofReal (h x) = 0 := hx
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx') (hnn x)

/-- Stationarity leaves the mean of each shifted observable unchanged, so a vanishing mean
stays vanishing at every shift. -/
private theorem lintegral_translate_eq_zero {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) {G : FieldPair d → ENNReal} (hG : Measurable G)
    (hG0 : ∫⁻ ω, G ω ∂Q = 0) (x : Vec d) :
    ∫⁻ ω, G (translate x ω) ∂Q = 0 := by
  calc ∫⁻ ω, G (translate x ω) ∂Q
      = ∫⁻ ω, G ω ∂(Measure.map (translate x) Q) :=
        (lintegral_map hG (EinsteinRelation.Probability.measurable_translate x)).symm
    _ = ∫⁻ ω, G ω ∂Q := by rw [hQ x]
    _ = 0 := hG0

/-- The shift integral of a measurable observable is measurable in the sample. -/
private theorem measurable_lintegral_translate {d : ℕ} {G : FieldPair d → ENNReal}
    (hG : Measurable G) :
    Measurable (fun ω : FieldPair d => ∫⁻ x, G (translate x ω) ∂(volume : Measure (Vec d))) := by
  have hF : Measurable (fun p : Vec d × FieldPair d => G (translate p.1 p.2)) :=
    hG.comp (measurable_translate_pair (d := d))
  exact Measurable.lintegral_prod_left' (μ := (volume : Measure (Vec d))) hF

/-- Tonelli's theorem exchanges the shift and sample lower integrals of a measurable observable. -/
private theorem lintegral_translate_swap {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] {G : FieldPair d → ENNReal} (hG : Measurable G) :
    ∫⁻ x, ∫⁻ ω, G (translate x ω) ∂Q ∂(volume : Measure (Vec d)) =
      ∫⁻ ω, ∫⁻ x, G (translate x ω) ∂(volume : Measure (Vec d)) ∂Q := by
  have hF : Measurable (fun p : Vec d × FieldPair d => G (translate p.1 p.2)) :=
    hG.comp (measurable_translate_pair (d := d))
  exact lintegral_lintegral_swap (μ := (volume : Measure (Vec d))) (ν := Q)
    (f := fun x ω => G (translate x ω)) hF.aemeasurable

/-- Stationarity turns the shifted means into the mean at the origin, so the double lower
integral vanishes when the sample mean does. -/
private theorem lintegral_lintegral_translate_eq_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {G : FieldPair d → ENNReal} (hG : Measurable G)
    (hG0 : ∫⁻ ω, G ω ∂Q = 0) :
    ∫⁻ ω, ∫⁻ x, G (translate x ω) ∂(volume : Measure (Vec d)) ∂Q = 0 := by
  rw [← lintegral_translate_swap Q hG]
  exact (lintegral_congr fun x => lintegral_translate_eq_zero Q hQ hG hG0 x).trans lintegral_zero

/-- If the lower integral over shifts of the squared orbit gradient vanishes at a sample, the
orbit gradient of that sample vanishes almost everywhere in space. -/
private theorem ae_gradSq_orbit_eq_zero {d : ℕ} {ψ : FieldPair d → ℝ}
    (hHm : Measurable (fun ω : FieldPair d => euclideanSq (gradient (orbit ψ ω) 0)))
    (ω : FieldPair d)
    (hω : ∫⁻ x, ENNReal.ofReal (euclideanSq (gradient (orbit ψ (translate x ω)) 0))
      ∂(volume : Measure (Vec d)) = 0) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), euclideanSq (gradient (orbit ψ ω) x) = 0 := by
  have hpair : Measurable (fun x : Vec d => (x, ω)) := measurable_id.prodMk measurable_const
  have hm : Measurable (fun x : Vec d => euclideanSq (gradient (orbit ψ (translate x ω)) 0)) :=
    hHm.comp ((measurable_translate_pair (d := d)).comp hpair)
  filter_upwards [ae_eq_zero_of_lintegral_ofReal_eq_zero (volume : Measure (Vec d)) hm
    (fun x => euclideanSq_nonneg _) hω] with x hx
  have hx' : euclideanSq (gradient (orbit ψ (translate x ω)) 0) = 0 := hx
  rw [gradient_orbit_translate] at hx'
  exact hx'

/-- Stationarity and a vanishing mean squared orbit gradient make every orbit of `ψ` constant
for almost every sample. -/
private theorem ae_translate_invariant {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : FieldPair d → ℝ} (hψ : Measurable ψ) (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω))
    (hG0 : ∫⁻ ω, ENNReal.ofReal (euclideanSq (gradient (orbit ψ ω) 0)) ∂Q = 0) :
    ∀ᵐ ω ∂Q, ∀ x : Vec d, ψ (translate x ω) = ψ ω := by
  have hHm := measurable_gradSq_zero hψ hsmooth
  have hG : Measurable (fun ω : FieldPair d =>
      ENNReal.ofReal (euclideanSq (gradient (orbit ψ ω) 0))) := hHm.ennreal_ofReal
  have hzero := lintegral_lintegral_translate_eq_zero Q hQ hG hG0
  have hae := (lintegral_eq_zero_iff (measurable_lintegral_translate hG)).mp hzero
  filter_upwards [hae] with ω hω
  have hω' : ∫⁻ x, ENNReal.ofReal (euclideanSq (gradient (orbit ψ (translate x ω)) 0))
      ∂(volume : Measure (Vec d)) = 0 := hω
  have hconstω := const_of_ae_gradSq_eq_zero (hsmooth ω) (ae_gradSq_orbit_eq_zero hHm ω hω')
  intro x
  have h := hconstω x 0
  rw [EinsteinRelation.orbit_zero] at h
  exact h

/-- Stationarity and translation ergodicity force a mean-zero squared orbit gradient at the
origin to vanish, so every orbit is constant on a full-measure set of samples, and then `ψ` is
almost surely constant. -/
theorem ae_const_of_integral_gradSq_eq_zero {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (hErg : EinsteinRelation.External.GantertSection7Support.IsTranslationErgodic Q)
    {ψ : FieldPair d → ℝ} (hψ : Measurable ψ) (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω))
    (hgrad : ∀ ω x, euclideanNorm (gradient (orbit ψ ω) x) ≤ 1 / 4)
    (hint : ∫ ω, euclideanSq (gradient (orbit ψ ω) 0) ∂Q = 0) :
    ∃ c : ℝ, ∀ᵐ ω ∂Q, ψ ω = c := by
  have hHnn : ∀ ω, 0 ≤ euclideanSq (gradient (orbit ψ ω) 0) := fun ω => euclideanSq_nonneg _
  have hHint := integrable_gradSq_zero Q hψ hsmooth hgrad
  have hG0 : ∫⁻ ω, ENNReal.ofReal (euclideanSq (gradient (orbit ψ ω) 0)) ∂Q = 0 := by
    have h := ofReal_integral_eq_lintegral_ofReal hHint (ae_of_all _ hHnn)
    rw [hint, ENNReal.ofReal_zero] at h
    exact h.symm
  have hconst_ae := ae_translate_invariant Q hQ hψ hsmooth hG0
  -- Level sets of `ψ` are translation invariant, so the ergodicity hypothesis applies to them.
  have h01 : ∀ t : ℝ, Q {ω | ψ ω < t} = 0 ∨ Q {ω | ψ ω < t} = 1 := by
    intro t
    have hm : MeasurableSet {ω : FieldPair d | ψ ω < t} := measurableSet_lt hψ measurable_const
    refine hErg _ hm fun z => ?_
    filter_upwards [hconst_ae] with ω hω
    show ψ (translate z ω) < t ↔ ψ ω < t
    rw [hω z]
  exact ae_const_of_sublevel_zero_one Q ψ hψ h01

/-- If `ψ` is not `Q`-almost surely constant, the mean sharp energy
`E[|∇ψ|² / (1 + ∂ᵢψ)]` of its orbit gradient at the origin is strictly positive. -/
theorem integral_sharpEnergy_pos {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q)
    (hErg : EinsteinRelation.External.GantertSection7Support.IsTranslationErgodic Q)
    (i₁ : Fin d) {ψ : FieldPair d → ℝ} (hψ : Measurable ψ)
    (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω))
    (hgrad : ∀ ω x, euclideanNorm (gradient (orbit ψ ω) x) ≤ 1 / 4)
    (hnc : ¬ ∃ c : ℝ, ∀ᵐ ω ∂Q, ψ ω = c) :
    0 < ∫ ω, sharpEnergy i₁ (gradient (orbit ψ ω) 0) ∂Q := by
  have hKnn : ∀ ω, 0 ≤ sharpEnergy i₁ (gradient (orbit ψ ω) 0) := fun ω =>
    sharpEnergy_nonneg i₁ _ (one_add_coord_pos i₁ _ (hgrad ω 0))
  have hKint : Integrable (fun ω => sharpEnergy i₁ (gradient (orbit ψ ω) 0)) Q :=
    Integrable.of_bound (measurable_sharpEnergy_orbit i₁ hψ hsmooth).aestronglyMeasurable
      (1 / 12) (ae_of_all _ fun ω => by
        show ‖sharpEnergy i₁ (gradient (orbit ψ ω) 0)‖ ≤ 1 / 12
        rw [Real.norm_eq_abs, abs_of_nonneg (hKnn ω)]
        exact sharpEnergy_le_twelfth i₁ _ (hgrad ω 0))
  have hHint := integrable_gradSq_zero Q hψ hsmooth hgrad
  by_contra hnonpos
  push_neg at hnonpos
  have hK0 : ∫ ω, sharpEnergy i₁ (gradient (orbit ψ ω) 0) ∂Q = 0 :=
    le_antisymm hnonpos (integral_nonneg fun ω => hKnn ω)
  have hmono : ∫ ω, 4 / 5 * euclideanSq (gradient (orbit ψ ω) 0) ∂Q ≤
      ∫ ω, sharpEnergy i₁ (gradient (orbit ψ ω) 0) ∂Q :=
    integral_mono (hHint.const_mul (4 / 5)) hKint
      (fun ω => four_fifths_mul_le_sharpEnergy i₁ _ (hgrad ω 0))
  rw [integral_const_mul, hK0] at hmono
  have hH0 : ∫ ω, euclideanSq (gradient (orbit ψ ω) 0) ∂Q = 0 := by
    have hHnonneg : 0 ≤ ∫ ω, euclideanSq (gradient (orbit ψ ω) 0) ∂Q :=
      integral_nonneg fun ω => euclideanSq_nonneg _
    exact le_antisymm (by linarith) hHnonneg
  exact hnc (ae_const_of_integral_gradSq_eq_zero Q hQ hErg hψ hsmooth hgrad hH0)

/-- The Step 4 constant `c = δ · E[|∇ψ|² / (1 + ∂₁ψ)]` is strictly positive for every `δ > 0`,
when `ψ` is not `Q`-almost surely constant. -/
theorem sharpConstant_pos {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q)
    (hErg : EinsteinRelation.External.GantertSection7Support.IsTranslationErgodic Q)
    (i₁ : Fin d) {ψ : FieldPair d → ℝ} (hψ : Measurable ψ)
    (hsmooth : ∀ ω, ContDiff ℝ 1 (orbit ψ ω))
    (hgrad : ∀ ω x, euclideanNorm (gradient (orbit ψ ω) x) ≤ 1 / 4)
    (hnc : ¬ ∃ c : ℝ, ∀ᵐ ω ∂Q, ψ ω = c) (δ : ℝ) (hδ : 0 < δ) :
    0 < δ * ∫ ω, sharpEnergy i₁ (gradient (orbit ψ ω) 0) ∂Q :=
  mul_pos hδ (integral_sharpEnergy_pos Q hQ hErg i₁ hψ hsmooth hgrad hnc)

end EinsteinRelation.Sharpness
