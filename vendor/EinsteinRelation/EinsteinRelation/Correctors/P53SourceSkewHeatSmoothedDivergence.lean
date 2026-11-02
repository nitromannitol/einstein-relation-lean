import EinsteinRelation.Correctors.HeatKernelConvolutionIntegrability
import EinsteinRelation.Calculus.Weak

/-!
# Heat smoothing of divergence-free stationary fields

Source: `paper/main.tex:732-748`; AKM Lemma 6.1, Step 4. If the orbits of a
stationary field are weakly divergence free, so are the orbits of its heat
smoothing, tested against derivatives of a smooth compactly supported kernel.
-/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

/-- A weakly divergence-free field integrates to zero against `F · ∇φ` for every smooth
compactly supported test `φ`. -/
theorem integral_dot_eq_zero_of_hasWeakDivergence_univ {d : ℕ} {F : Vec d → Vec d}
    (hF : HasWeakDivergence Set.univ F (fun _ => 0))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    ∫ x, dot (F x) (gradient φ x) = 0 := by
  have h := hF.2.2 φ ⟨hφ, hφc, Set.subset_univ _⟩
  simpa only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] using h

/-- A `Q`-a.e. property of the environment holds, for `Q`-a.e. `ρ`, along almost every
translate `translate z ρ` (Fubini on `Q × Lebesgue`, using stationarity). -/
theorem ae_ae_translate_of_ae {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {P : FieldPair d → Prop} (hP : ∀ᵐ ρ ∂Q, P ρ) :
    ∀ᵐ ρ ∂Q, ∀ᵐ z ∂(volume : Measure (Vec d)), P (translate z ρ) := by
  obtain ⟨M, hMm, hMN, hM0⟩ : ∃ M : Set (FieldPair d), MeasurableSet M ∧
      {ρ | ¬ P ρ} ⊆ M ∧ Q M = 0 :=
    ⟨toMeasurable Q {ρ | ¬ P ρ}, measurableSet_toMeasurable _ _, subset_toMeasurable _ _,
      by rw [measure_toMeasurable]; exact ae_iff.mp hP⟩
  have hT : Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
    Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)
  have hS : MeasurableSet {p : FieldPair d × Vec d | translate p.2 p.1 ∈ M} :=
    hMm.preimage hT
  have hslice : ∀ z : Vec d,
      Q ((fun ρ => (ρ, z)) ⁻¹' {p : FieldPair d × Vec d | translate p.2 p.1 ∈ M}) = 0 := by
    intro z
    have hpre : (fun ρ => (ρ, z)) ⁻¹' {p : FieldPair d × Vec d | translate p.2 p.1 ∈ M} =
        translate z ⁻¹' M := rfl
    rw [hpre, ← Measure.map_apply (Probability.measurable_translate z) hMm, hQ z, hM0]
  have hprod : (Q.prod (volume : Measure (Vec d)))
      {p : FieldPair d × Vec d | translate p.2 p.1 ∈ M} = 0 := by
    rw [Measure.prod_apply_symm hS]
    simp only [hslice, lintegral_zero]
  have hae := Measure.ae_ae_of_ae_prod (μ := Q) (ν := (volume : Measure (Vec d)))
    (p := fun q : FieldPair d × Vec d => translate q.2 q.1 ∉ M)
    (measure_eq_zero_iff_ae_notMem.mp hprod)
  filter_upwards [hae] with ρ hρ
  filter_upwards [hρ] with z hz
  by_contra hc
  exact hz (hMN hc)

/-- For a fixed starting point, the joint orbit integrand `(x, z) ↦ a x * (b z * f (T_{x+z} ω))`
is integrable for `Q`-a.e. `ω`, by Tonelli-type Fubini over `(x, z) × ω` and stationarity. -/
theorem ae_integrable_heat_joint {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {a b : Vec d → ℝ} (ham : Measurable a) (hai : Integrable a)
    (hbm : Measurable b) (hbi : Integrable b) {f : FieldPair d → ℝ} (hfm : Measurable f)
    (hfi : Integrable f Q) :
    ∀ᵐ ω ∂Q, Integrable (fun p : Vec d × Vec d => a p.1 * (b p.2 * f (translate (p.1 + p.2) ω)))
      ((volume : Measure (Vec d)).prod volume) := by
  have hT : Measurable (fun q : (Vec d × Vec d) × FieldPair d => translate (q.1.1 + q.1.2) q.2) :=
    Probability.continuous_translate.measurable.comp
      (((measurable_fst.comp measurable_fst).add
        (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  have hGm : Measurable (fun q : (Vec d × Vec d) × FieldPair d =>
      a q.1.1 * (b q.1.2 * f (translate (q.1.1 + q.1.2) q.2))) :=
    (ham.comp (measurable_fst.comp measurable_fst)).mul
      ((hbm.comp (measurable_snd.comp measurable_fst)).mul (hfm.comp hT))
  have hnorm : ∀ p : Vec d × Vec d,
      (∫ ω, ‖a p.1 * (b p.2 * f (translate (p.1 + p.2) ω))‖ ∂Q) =
        |a p.1| * |b p.2| * ∫ ω, ‖f ω‖ ∂Q := by
    intro p
    have hpt : ∀ ω, ‖a p.1 * (b p.2 * f (translate (p.1 + p.2) ω))‖ =
        |a p.1| * |b p.2| * ‖f (translate (p.1 + p.2) ω)‖ := by
      intro ω
      simp only [norm_mul, Real.norm_eq_abs, mul_assoc]
    have hT' : ∫ ω, ‖f (translate (p.1 + p.2) ω)‖ ∂Q = ∫ ω, ‖f ω‖ ∂Q :=
      Probability.integral_translate Q hQ (p.1 + p.2) (fun ω => ‖f ω‖) hfm.norm
    simp only [hpt, integral_const_mul]
    rw [hT']
  have hC : Integrable (fun p : Vec d × Vec d => |a p.1| * |b p.2| * ∫ ω, ‖f ω‖ ∂Q)
      ((volume : Measure (Vec d)).prod volume) :=
    ((Integrable.mul_prod hai.abs hbi.abs).mul_const (∫ ω, ‖f ω‖ ∂Q))
  have hG : Integrable (fun q : (Vec d × Vec d) × FieldPair d =>
      a q.1.1 * (b q.1.2 * f (translate (q.1.1 + q.1.2) q.2)))
      (((volume : Measure (Vec d)).prod volume).prod Q) := by
    rw [integrable_prod_iff hGm.aestronglyMeasurable]
    refine ⟨ae_of_all _ fun p => ?_, ?_⟩
    · have hsh : Integrable f (Measure.map (translate (p.1 + p.2)) Q) := by
        rw [hQ (p.1 + p.2)]
        exact hfi
      have h := (hsh.comp_measurable (Probability.measurable_translate (p.1 + p.2))).const_mul
        (a p.1 * b p.2)
      refine h.congr (ae_of_all _ fun ω => ?_)
      simp only [Function.comp_apply, mul_assoc]
    · refine hC.congr (ae_of_all _ fun p => ?_)
      exact (hnorm p).symm
  filter_upwards [hG.prod_left_ae] with ω hω
  exact hω

/-- The `t > 0` case, for a fixed environment `ρ` at which the joint Fubini integrability and
the a.e. translate-divergence property hold. -/
theorem sum_horizontalMollify_heatSmoothed_eq_zero_of_pos {d : ℕ} (ρ : FieldPair d)
    (g : FieldPair d → Vec d) {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) {t : ℝ} (htpos : 0 < t)
    (hI : ∀ k : Fin d, Integrable (fun p : Vec d × Vec d =>
      coordinateDerivative k φ p.1 * (euclideanHeatKernel t p.2 * g (translate (p.1 + p.2) ρ) k))
      ((volume : Measure (Vec d)).prod volume))
    (hS : ∀ᵐ z ∂(volume : Measure (Vec d)),
      HasWeakDivergence Set.univ (fun x => g (translate x (translate z ρ))) (fun _ => 0)) :
    ∑ k : Fin d, horizontalMollify (coordinateDerivative k φ) (heatSmoothed t (fun ω => g ω k)) ρ
      = 0 := by
  have hh' : ∀ (f : FieldPair d → ℝ) (ω : FieldPair d),
      heatSmoothed t f ω = ∫ z : Vec d, euclideanHeatKernel t z * f (translate z ω) := by
    intro f ω
    unfold heatSmoothed
    exact if_neg htpos.ne'
  have hA : ∀ k : Fin d,
      horizontalMollify (coordinateDerivative k φ) (heatSmoothed t (fun ω => g ω k)) ρ =
        ∫ p : Vec d × Vec d, coordinateDerivative k φ p.1 *
          (euclideanHeatKernel t p.2 * g (translate (p.1 + p.2) ρ) k)
          ∂((volume : Measure (Vec d)).prod volume) := by
    intro k
    rw [integral_prod _ (hI k)]
    simp only [horizontalMollify, hh']
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [← integral_const_mul]
    congr 1
    ext z
    rw [translate_add, add_comm z x]
  have hΦ : Integrable (fun p : Vec d × Vec d => ∑ k : Fin d,
      coordinateDerivative k φ p.1 * (euclideanHeatKernel t p.2 * g (translate (p.1 + p.2) ρ) k))
      ((volume : Measure (Vec d)).prod volume) :=
    integrable_finset_sum _ fun k _ => hI k
  have hz : ∀ᵐ z ∂(volume : Measure (Vec d)), ∫ x, ∑ k : Fin d,
      coordinateDerivative k φ x * (euclideanHeatKernel t z * g (translate (x + z) ρ) k) = 0 := by
    filter_upwards [hS] with z hzd
    have hkey : ∀ x : Vec d, ∑ k : Fin d,
        coordinateDerivative k φ x * (euclideanHeatKernel t z * g (translate (x + z) ρ) k) =
          euclideanHeatKernel t z * dot (g (translate x (translate z ρ))) (gradient φ x) := by
      intro x
      rw [translate_add]
      simp only [dot, gradient, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    simp only [hkey]
    rw [integral_const_mul, integral_dot_eq_zero_of_hasWeakDivergence_univ hzd hφ hφc, mul_zero]
  simp only [hA]
  rw [← integral_finset_sum Finset.univ fun k _ => hI k, integral_prod_symm _ hΦ]
  rw [integral_congr_ae hz, integral_zero]

/-- Source: AKM Lemma 6.1, Step 4, `paper/main.tex:732-748`. -/
theorem ae_sum_horizontalMollify_heatSmoothed_divergence_eq_zero {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {g : FieldPair d → Vec d} (hg : Measurable g)
    (hgi : ∀ k, Integrable (fun ω => g ω k) Q)
    (hdiv : ∀ᵐ ρ ∂Q, HasWeakDivergence Set.univ (fun x => g (translate x ρ)) (fun _ => 0))
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ρ ∂Q, ∑ k : Fin d,
      horizontalMollify (coordinateDerivative k φ) (heatSmoothed t (fun ω => g ω k)) ρ = 0 := by
  have hcd : ∀ k : Fin d, Continuous (coordinateDerivative k φ) := fun k =>
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcdc : ∀ k : Fin d, HasCompactSupport (coordinateDerivative k φ) := fun k =>
    hφc.fderiv_apply ℝ (unitVector k)
  have hgm : ∀ k : Fin d, Measurable (fun ω => g ω k) := fun k =>
    (measurable_pi_apply k).comp hg
  rcases ht.eq_or_lt with rfl | htpos
  · have h0 : ∀ (f : FieldPair d → ℝ) (ω : FieldPair d), heatSmoothed 0 f ω = f ω := by
      intro f ω
      unfold heatSmoothed
      exact if_pos rfl
    filter_upwards [hdiv] with ρ hρ
    have hint : ∀ k : Fin d,
        Integrable (fun x => coordinateDerivative k φ x * g (translate x ρ) k) := by
      intro k
      have hloc : LocallyIntegrable (fun x => g (translate x ρ) k) :=
        locallyIntegrableOn_univ.mp (hρ.1 k)
      simpa only [smul_eq_mul] using
        hloc.integrable_smul_left_of_hasCompactSupport (hcd k) (hcdc k)
    have hdot : ∀ x : Vec d, ∑ k : Fin d, coordinateDerivative k φ x * g (translate x ρ) k =
        dot (g (translate x ρ)) (gradient φ x) := by
      intro x
      simp only [dot, gradient]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    simp only [horizontalMollify, h0]
    rw [← integral_finset_sum Finset.univ fun k _ => hint k]
    simp only [hdot]
    exact integral_dot_eq_zero_of_hasWeakDivergence_univ hρ hφ hφc
  · have hI : ∀ᵐ ρ ∂Q, ∀ k : Fin d, Integrable (fun p : Vec d × Vec d =>
        coordinateDerivative k φ p.1 *
          (euclideanHeatKernel t p.2 * g (translate (p.1 + p.2) ρ) k))
        ((volume : Measure (Vec d)).prod volume) :=
      ae_all_iff.mpr fun k => ae_integrable_heat_joint Q hQ (hcd k).measurable
        ((hcd k).integrable_of_hasCompactSupport (hcdc k))
        (continuous_euclideanHeatKernel t).measurable
        (integrable_euclideanHeatKernel htpos) (hgm k) (hgi k)
    have hS : ∀ᵐ ρ ∂Q, ∀ᵐ z ∂(volume : Measure (Vec d)),
        HasWeakDivergence Set.univ (fun x => g (translate x (translate z ρ))) (fun _ => 0) :=
      ae_ae_translate_of_ae Q hQ hdiv
    filter_upwards [hI, hS] with ρ hIρ hSρ
    exact sum_horizontalMollify_heatSmoothed_eq_zero_of_pos ρ g hφ hφc htpos hIρ hSρ

end EinsteinRelation.Correctors
