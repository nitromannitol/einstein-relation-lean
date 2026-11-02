import EinsteinFull.Calculus.CubeIntegralSupport
import EinsteinFull.Frozen.ComplexLocalObservation
import EinsteinRelation.Environment.LocalIntegralMeasurability
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

open MeasureTheory
open scoped NNReal BigOperators

namespace EinsteinFull
open EinsteinRelation

private theorem c7_cube_volume {d : ℕ} {ρ : ℝ} (_hρ : 0 ≤ ρ) :
    volume (Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))) =
      ENNReal.ofReal ρ ^ d := by
  rw [Real.volume_pi_Ioo]
  simp only [show ρ / 2 - -ρ / 2 = ρ by ring, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- A measurable representative of the stationary orbit has the literal
pointwise cube integral prescribed by the actual L2 Bochner integral. -/
theorem c7_cubeIntegralObservation_coeFn {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (U : Lp ℂ 2 (reducedLaw Q)) (f : FieldPair d → ℂ) (hf : Measurable f)
    (heq : f =ᵐ[reducedLaw Q] U) :
    Integrable (fun p : Vec d × FieldPair d => f (translate p.1 p.2))
      ((volume.restrict (Set.pi Set.univ
        (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2)))).prod (reducedLaw Q)) ∧
    (cubeIntegralObservation Q ρ U : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => ∫ x in Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2)),
        f (translate x ω) := by
  let := reducedLaw_probability Q
  let C := Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))
  have hC : volume C < ⊤ := by
    rw [show C = _ from rfl, c7_cube_volume hρ]
    finiteness
  let : IsFiniteMeasure (volume.restrict C) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hC⟩
  have hfm : Measurable (fun p : Vec d × FieldPair d => f (translate p.1 p.2)) :=
    hf.comp Probability.continuous_translate.measurable
  have hfi : Integrable f (reducedLaw Q) :=
    ((Lp.memLp U).integrable (by norm_num)).congr heq.symm
  have hs (x : Vec d) : (fun ω => f (translate x ω)) =ᵐ[reducedLaw Q]
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U := by
    have ht := (measurePreserving_translate _ (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae_eq_comp heq
    filter_upwards [ht, coeFn_complexTranslation _ (reducedLaw_stationary Q) x U]
      with ω hfω hUω
    exact hfω.trans hUω.symm
  have hi : Integrable (fun p : Vec d × FieldPair d => f (translate p.1 p.2))
      ((volume.restrict C).prod (reducedLaw Q)) := by
    apply (integrable_prod_iff hfm.aestronglyMeasurable).mpr
    refine ⟨Filter.Eventually.of_forall (fun x =>
      (measurePreserving_translate _ (reducedLaw_stationary Q) x).integrable_comp_of_integrable hfi), ?_⟩
    have hn (x : Vec d) : (∫ ω, ‖f (translate x ω)‖ ∂reducedLaw Q) =
        ∫ ω, ‖f ω‖ ∂reducedLaw Q :=
      Probability.integral_translate _ (reducedLaw_stationary Q) x (fun ω => ‖f ω‖) hf.norm
    simp_rw [hn]
    exact integrable_const _
  refine ⟨hi, ?_⟩
  have hu := integrableOn_cubeIntegralObservation_integrand Q ρ U
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℂ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℂ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  change (∫ ω in A, (∫ x in C,
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x U) ω ∂reducedLaw Q) = _
  rw [← ht]
  have hir : Integrable (fun p : Vec d × FieldPair d => f (translate p.1 p.2))
      ((volume.restrict C).prod ((reducedLaw Q).restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun x ω => f (translate x ω)) hir]
  apply integral_congr_ae
  filter_upwards with x
  exact integral_congr_ae (ae_restrict_of_ae (hs x).symm)

private theorem c7_cube_add_ball {d : ℕ} {ρ : ℝ} (hρ : 0 < ρ)
    {x : Vec d} (hx : x ∈ Set.pi Set.univ
      (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2)))
    {y : Vec d} (hy : euclideanNorm y < ρ) :
    euclideanNorm (x + y) < ((d : ℝ) + 1) * ρ := by
  have hcoord (j : Fin d) : |x j| ≤ ρ := by
    have hj := Set.mem_pi.mp hx j (Set.mem_univ j)
    exact (abs_le.mpr ⟨by linarith [hj.1], by linarith [hj.2]⟩)
  have hn : euclideanNorm x ≤ ∑ j : Fin d, |x j| := by
    unfold euclideanNorm euclideanSq dot
    apply Real.sqrt_le_iff.mpr
    refine ⟨Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
    simpa only [pow_two, abs_mul_abs_self] using
      (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
        (f := fun j : Fin d => |x j|) (fun _ _ => abs_nonneg _))
  have hb : euclideanNorm x ≤ (d : ℝ) * ρ := hn.trans (by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using (Finset.sum_le_sum (s := Finset.univ) (fun j _ => hcoord j)))
  have ht := TimeChange.euclideanNorm_add_le x y
  nlinarith only [ht, hb, hy]

theorem c7_cubeIntegralObservation_local {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ρ : ℝ} (hρ : 0 < ρ)
    (V : Lp ℂ 2 (reducedLaw Q)) (hV : IsComplexLocalObservation Q ρ V) :
    IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (cubeIntegralObservation Q ρ V) := by
  let := reducedLaw_probability Q
  obtain ⟨f, hfm, hf⟩ := hV
  have hfg : Measurable f := hfm.mono (Probability.localSigma_le_borel _) le_rfl
  obtain ⟨hi, heq⟩ := c7_cubeIntegralObservation_coeFn Q hρ.le V f hfg hf
  let C := Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))
  have hCm : MeasurableSet C := MeasurableSet.univ_pi fun _ => measurableSet_Ioo
  have hSW : ∀ x ∈ C, ∀ y ∈ {y : Vec d | euclideanNorm y < ρ},
      x + y ∈ {y : Vec d | euclideanNorm y < ((d : ℝ) + 1) * ρ} :=
    fun _ hx _ hy => c7_cube_add_ball hρ hx hy
  have hre := measurable_localSigma_setIntegral_translate hCm hSW
    (fun _ => (1 : ℝ)) measurable_const (fun ω => (f ω).re)
    (Complex.measurable_re.comp hfm)
  have him := measurable_localSigma_setIntegral_translate hCm hSW
    (fun _ => (1 : ℝ)) measurable_const (fun ω => (f ω).im)
    (Complex.measurable_im.comp hfm)
  simp only [one_mul] at hre him
  let g : FieldPair d → ℂ := fun ω =>
    (∫ x in C, (f (translate x ω)).re) + (∫ x in C, (f (translate x ω)).im) * Complex.I
  refine ⟨g, (Complex.measurable_ofReal.comp hre).add
    ((Complex.measurable_ofReal.comp him).mul measurable_const), ?_⟩
  filter_upwards [hi.prod_left_ae, heq] with ω hω heω
  rw [heω]
  change (↑(∫ x in C, (f (translate x ω)).re) +
    ↑(∫ x in C, (f (translate x ω)).im) * Complex.I) = _
  exact integral_re_add_im hω

theorem c7_cubeIntegralObservation_error {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ρ ε : ℝ} (hρ : 0 < ρ) (_hε : 0 ≤ ε)
    (U V : Lp ℂ 2 (reducedLaw Q))
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖cubeIntegralObservation Q ρ U ω - cubeIntegralObservation Q ρ V ω‖ ≤ ρ ^ d * ε := by
  let := reducedLaw_probability Q
  let f := (Lp.aestronglyMeasurable U).mk U
  let g := (Lp.aestronglyMeasurable V).mk V
  have hf : Measurable f := (Lp.aestronglyMeasurable U).stronglyMeasurable_mk.measurable
  have hg : Measurable g := (Lp.aestronglyMeasurable V).stronglyMeasurable_mk.measurable
  have heU : f =ᵐ[reducedLaw Q] U := (Lp.aestronglyMeasurable U).ae_eq_mk.symm
  have heV : g =ᵐ[reducedLaw Q] V := (Lp.aestronglyMeasurable V).ae_eq_mk.symm
  obtain ⟨hiU, hU⟩ := c7_cubeIntegralObservation_coeFn Q hρ.le U f hf heU
  obtain ⟨hiV, hV⟩ := c7_cubeIntegralObservation_coeFn Q hρ.le V g hg heV
  let C := Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))
  have he : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - g ω‖ ≤ ε := by
    filter_upwards [heU, heV, herr] with ω hU hV hω
    simpa only [hU, hV] using hω
  have hp : ∀ᵐ p ∂(volume.restrict C).prod (reducedLaw Q),
      ‖f (translate p.1 p.2) - g (translate p.1 p.2)‖ ≤ ε := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      ((hf.comp Probability.continuous_translate.measurable).sub
        (hg.comp Probability.continuous_translate.measurable)).norm measurable_const)).mpr
    exact Filter.Eventually.of_forall fun x =>
      (measurePreserving_translate _ (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae he
  have hC : volume C < ⊤ := by
    rw [show C = _ from rfl, c7_cube_volume hρ.le]
    finiteness
  filter_upwards [hU, hV, hiU.prod_left_ae, hiV.prod_left_ae,
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp)]
      with ω hU hV hiU hiV hb
  rw [hU, hV, ← integral_sub hiU hiV]
  have h := norm_setIntegral_le_of_norm_le_const_ae hC hb
  rw [Measure.real, show volume C = _ from c7_cube_volume hρ.le,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le, mul_comm] at h
  exact h

theorem c7_cubeIntegralObservation_local_approximation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (U V : Lp ℂ 2 (reducedLaw Q)) (hV : IsComplexLocalObservation Q ρ V)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖U ω - V ω‖ ≤ ε) :
    IsComplexLocalObservation Q (((d : ℝ) + 1) * ρ) (cubeIntegralObservation Q ρ V) ∧
    (∀ᵐ ω ∂reducedLaw Q,
      ‖cubeIntegralObservation Q ρ U ω - cubeIntegralObservation Q ρ V ω‖ ≤ ρ ^ d * ε) :=
  ⟨c7_cubeIntegralObservation_local Q hρ V hV,
    c7_cubeIntegralObservation_error Q hρ hε U V herr⟩

private theorem c7_integral_joint_bound {d : ℕ} {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} [IsFiniteMeasure ν] {f : Y → ℂ} {g : Y → Fin d → ℂ}
    (hf : Integrable f ν) (hg : ∀ j, Integrable (fun x => g x j) ν)
    {ε : ℝ} (hε : 0 ≤ ε) (hb : ∀ᵐ x ∂ν, ‖f x‖ + Real.sqrt (∑ j, ‖g x j‖ ^ 2) ≤ ε) :
    ‖∫ x, f x ∂ν‖ + Real.sqrt (∑ j, ‖∫ x, g x j ∂ν‖ ^ 2) ≤ ν.real Set.univ * ε := by
  let G : Y → EuclideanSpace ℂ (Fin d) := fun x => WithLp.toLp 2 (g x)
  have hG : Integrable G ν := Integrable.of_eval_piLp hg
  have hGn (x : Y) : ‖G x‖ = Real.sqrt (∑ j, ‖g x j‖ ^ 2) :=
    EuclideanSpace.norm_eq _
  have he : ‖∫ x, G x ∂ν‖ = Real.sqrt (∑ j, ‖∫ x, g x j ∂ν‖ ^ 2) := by
    rw [EuclideanSpace.norm_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [eval_integral_piLp hg j]
  rw [← he]
  calc
    ‖∫ x, f x ∂ν‖ + ‖∫ x, G x ∂ν‖ ≤
        (∫ x, ‖f x‖ ∂ν) + ∫ x, ‖G x‖ ∂ν :=
      add_le_add (norm_integral_le_integral_norm _) (norm_integral_le_integral_norm _)
    _ = ∫ x, (‖f x‖ + ‖G x‖) ∂ν := (integral_add hf.norm hG.norm).symm
    _ ≤ ∫ _x, |ε| ∂ν := integral_mono_ae (hf.norm.add hG.norm) (integrable_const |ε|)
      (hb.mono fun x hx => by simpa only [hGn, abs_of_nonneg hε] using hx)
    _ = ν.real Set.univ * ε := by rw [abs_of_nonneg hε, integral_const, smul_eq_mul]

theorem c7_cubeIntegralObservation_joint_error {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 ≤ ε)
    (U V : Lp ℂ 2 (reducedLaw Q)) (G H : Fin d → Lp ℂ 2 (reducedLaw Q))
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖U ω - V ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω - H j ω‖ ^ 2) ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖cubeIntegralObservation Q ρ U ω - cubeIntegralObservation Q ρ V ω‖ +
        Real.sqrt (∑ j : Fin d,
          ‖cubeIntegralObservation Q ρ (G j) ω - cubeIntegralObservation Q ρ (H j) ω‖ ^ 2)
        ≤ ρ ^ d * ε := by
  let := reducedLaw_probability Q
  let rep (W : Lp ℂ 2 (reducedLaw Q)) := (Lp.aestronglyMeasurable W).mk W
  have hm (W : Lp ℂ 2 (reducedLaw Q)) : Measurable (rep W) :=
    (Lp.aestronglyMeasurable W).stronglyMeasurable_mk.measurable
  have ha (W : Lp ℂ 2 (reducedLaw Q)) : rep W =ᵐ[reducedLaw Q] W :=
    (Lp.aestronglyMeasurable W).ae_eq_mk.symm
  have hrep (W : Lp ℂ 2 (reducedLaw Q)) :=
    c7_cubeIntegralObservation_coeFn Q hρ.le W (rep W) (hm W) (ha W)
  let C := Set.pi Set.univ (fun _ : Fin d => Set.Ioo (-ρ / 2) (ρ / 2))
  have hC : volume C < ⊤ := by
    rw [show C = _ from rfl, c7_cube_volume hρ.le]
    finiteness
  let : IsFiniteMeasure (volume.restrict C) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hC⟩
  have hb : ∀ᵐ ω ∂reducedLaw Q, ‖rep U ω - rep V ω‖ +
      Real.sqrt (∑ j : Fin d, ‖rep (G j) ω - rep (H j) ω‖ ^ 2) ≤ ε := by
    filter_upwards [ha U, ha V, ae_all_iff.mpr (fun j => ha (G j)),
      ae_all_iff.mpr (fun j => ha (H j)), herr] with ω hU hV hG hH hω
    simpa only [hU, hV, hG, hH] using hω
  have hp : ∀ᵐ p ∂(volume.restrict C).prod (reducedLaw Q),
      ‖rep U (translate p.1 p.2) - rep V (translate p.1 p.2)‖ +
        Real.sqrt (∑ j : Fin d,
          ‖rep (G j) (translate p.1 p.2) - rep (H j) (translate p.1 p.2)‖ ^ 2) ≤ ε := by
    have hT := (Probability.continuous_translate (d := d)).measurable
    have hmeas : Measurable (fun p : Vec d × FieldPair d =>
        ‖rep U (translate p.1 p.2) - rep V (translate p.1 p.2)‖ +
          Real.sqrt (∑ j : Fin d,
            ‖rep (G j) (translate p.1 p.2) - rep (H j) (translate p.1 p.2)‖ ^ 2)) := by
      fun_prop
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hmeas measurable_const)).mpr
    exact Filter.Eventually.of_forall fun x =>
      (measurePreserving_translate _ (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hb
  have hGi := ae_all_iff.mpr (fun j => (hrep (G j)).1.prod_left_ae)
  have hHi := ae_all_iff.mpr (fun j => (hrep (H j)).1.prod_left_ae)
  have hGe := ae_all_iff.mpr (fun j => (hrep (G j)).2)
  have hHe := ae_all_iff.mpr (fun j => (hrep (H j)).2)
  filter_upwards [(hrep U).1.prod_left_ae, (hrep V).1.prod_left_ae, hGi, hHi,
    (hrep U).2, (hrep V).2, hGe, hHe,
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hp)]
    with ω hiU hiV hiG hiH heU heV heG heH hbω
  simp_rw [heU, heV, heG, heH, ← integral_sub hiU hiV,
    ← integral_sub (hiG _) (hiH _)]
  have h := c7_integral_joint_bound (hiU.sub hiV)
    (fun j => (hiG j).sub (hiH j)) hε hbω
  rw [Measure.real, Measure.restrict_apply_univ,
    show volume C = _ from c7_cube_volume hρ.le,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le] at h
  exact h

end EinsteinFull
