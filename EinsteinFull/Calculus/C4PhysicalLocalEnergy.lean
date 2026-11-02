import EinsteinFull.Calculus.C4ComplexCaccioppoliEnergy
import EinsteinFull.Calculus.ComplexCommonSpatialSupport
import EinsteinFull.Work.W6.PhysicalLocalTestingSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.InnerProductSpace.Calculus
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! Spatial cutoff energy for the literal stationary generator on physical orbits.
The generator output is retained in the estimate; temporal integration by parts
and the parabolic time-slice bound are separate obligations. -/

open MeasureTheory Filter Set
open scoped Topology BigOperators NNReal ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

private theorem divergence_projection {d : ℕ} {F : Vec d → Fin d → ℂ}
    {q : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => F x j) 2 (volume.restrict K))
    (hq : ∀ K : Set (Vec d), IsCompact K → MemLp q 2 (volume.restrict K))
    (hw : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q x * (φ x : ℂ)) = -(∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakDivergence univ (fun x j => L (F x j)) (fun x => L (q x)) := by
  have hloc {v : Vec d → ℂ}
      (hv : ∀ K : Set (Vec d), IsCompact K → MemLp v 2 (volume.restrict K)) :
      LocallyIntegrable (fun x => L (v x)) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hv K hK)).integrable (by norm_num)
  refine ⟨fun j => (hloc (fun K hK => hF K hK j)).locallyIntegrableOn univ,
    (hloc hq).locallyIntegrableOn univ, ?_⟩
  intro φ hφ
  have hi := integrable_spatial_mul_test hq hφ.1.continuous hφ.2.1
  have hj (j : Fin d) : Integrable (fun x => F x j * (coordinateDerivative j φ x : ℂ)) volume := integrable_spatial_mul_test (fun K hK => hF K hK j)
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφ.2.1.fderiv_apply ℝ (unitVector j))
  have hs := integrable_finsetSum Finset.univ (fun j _ => hj j)
  have he := congrArg L (hw φ hφ.1 hφ.2.1)
  rw [map_neg, ← L.integral_comp_comm hi, ← L.integral_comp_comm hs] at he
  have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
  simp only [map_sum, hp] at he
  simpa only [Measure.restrict_univ, dot, gradient] using (neg_eq_iff_eq_neg.mp he.symm)

/-- The literal reduced coefficient is elliptic at every physical point on
one environment event. This transports the actual regularity event. -/
theorem c4_ae_reduced_physical_elliptic {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedLaw Q,
      IsElliptic (Real.exp (2 * Λ₀) * Λ₀) (fun x => ω.1 x) := by
  have hc (L : ℝ) : IsClosed {ω : FieldPair d | IsElliptic L (fun x => ω.1 x)} := by
    have he : {ω : FieldPair d | IsElliptic L (fun x => ω.1 x)} =
        ⋂ x : Vec d, ({ω : FieldPair d | (ω.1 x).transpose = ω.1 x} ∩
          ⋂ ξ : Vec d, ({ω : FieldPair d | L⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ)} ∩
            {ω : FieldPair d | dot ξ ((ω.1 x).mulVec ξ) ≤ L * euclideanSq ξ})) := by
      ext ω
      simp only [IsElliptic, mem_ofPred_eq, mem_iInter, mem_inter_iff]
    rw [he]
    apply isClosed_iInter
    intro x
    have hx : Continuous (fun ω : FieldPair d => ω.1 x) :=
      (continuous_eval_const x).comp continuous_fst
    refine (isClosed_eq hx.matrix_transpose hx).inter (isClosed_iInter fun ξ => ?_)
    have hq : Continuous (fun ω : FieldPair d => dot ξ ((ω.1 x).mulVec ξ)) := by
      exact continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp (hx.matrix_mulVec continuous_const))
    exact (isClosed_le continuous_const hq).inter (isClosed_le hq continuous_const)
  rw [reducedLaw, ae_map_iff Probability.measurable_reduce.aemeasurable (hc _).measurableSet]
  filter_upwards [Q.regular] with ω hω
  intro x
  change (reducedMatrixField ω x).transpose = reducedMatrixField ω x ∧ _
  refine ⟨reducedCoefficient_transpose ω x (hω.1 x).1, fun ξ => ?_⟩
  have hinv : (Real.exp (2 * Λ₀) * Λ₀)⁻¹ = Real.exp (-2 * Λ₀) * Λ₀⁻¹ := by
    rw [mul_inv, ← Real.exp_neg, neg_mul]
  rw [hinv]
  exact reducedCoefficient_energy_bounds ω x ξ Λ₀ Q.ellipticity_parameter hω

/-- Physical spatial Caccioppoli estimate for a genuine full forced generator
pair. The event precedes every compact smooth cutoff. The source is exactly
the generator output, with no local PDE or regularity premise. -/
theorem IsComplexGeneratorPair.ae_physical_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re +
        (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) := by
  intro L
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun j ω => (1 / 2 : ℂ) * ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let q : FieldPair d → ℂ := fun ω => g ω - ζ * b ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) := measurable_const.mul
    (Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable)
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (hm j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hqm : Measurable q := (Lp.stronglyMeasurable g).measurable.sub (measurable_const.mul hbm)
  have hq : MemLp q 2 (reducedLaw Q) := (Lp.memLp g).sub (hb.const_mul ζ)
  have hF j : MemLp (F j) 2 (reducedLaw Q) := (memLp_complex_coefficient_flux Q G j).const_mul _
  have hw := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F q hFm hqm hF hq (by
      intro v V hV
      have he := hfg.horizontal_flux hG v V hV
      have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
        (Lp.memLp g).integrable_mul (Lp.memLp v)
      have hd : Integrable (fun ω => b ω * v ω) (reducedLaw Q) :=
        hb.integrable_mul (Lp.memLp v)
      have heq : (fun ω => (2 * g ω - 2 * ζ *
          (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω) =
          (fun ω => 2 * (g ω * v ω) - (2 * ζ) * (b ω * v ω)) := by
        funext ω
        dsimp only [b]
        ring
      rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
        integral_const_mul, integral_const_mul] at he
      have hqe : (fun ω => q ω * v ω) =
          (fun ω => g ω * v ω - ζ * (b ω * v ω)) := by
        funext ω
        dsimp only [q]
        ring
      rw [hqe, integral_sub hg (hd.const_mul ζ), integral_const_mul]
      simp only [F, mul_assoc, ← Finset.mul_sum, integral_const_mul]
      linear_combination (1 / 2 : ℂ) * he)
  filter_upwards [hG.ae_reduced_spatial Q, hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) hqm hq,
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j)),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    c4_ae_reduced_physical_elliptic Q] with ω hω hw hqω hFω hgω ha
  have hreal := divergence_projection (fun K hK j => hFω j K hK) hqω hw Complex.reCLM
  have himag := divergence_projection (fun K hK j => hFω j K hK) hqω hw Complex.imCLM
  simp only [F, q, b, translate_matrix, add_zero] at hreal himag
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  intro φ hφ
  have he := physicalLocalEnergy_locallyH1 isOpen_univ (fun x => ω.1 x)
    (fun j k => memLp_complex_elliptic_entry _ _ L hL ha
      (fun j k => (ω.1.continuous.matrix_elem j k)) j k)
    L⁻¹ L (inv_pos.mpr hL)
    (Eventually.of_forall fun x ξ => ((ha x).2 ξ).1)
    (Eventually.of_forall fun x j k => Correctors.IsElliptic.entry_abs_le hL ha x j k)
    i ζ (F := fun _ => 0) (fun K hK _ => (hω.2.2 K hK).1)
    (fun K hK _ j => (hω.2.2 K hK).2 j) (fun K hK _ => hgω K hK)
    (fun K hK _ => MemLp.zero) hω.1 hω.2.1
    (by simpa only [sub_zero] using! hreal) (by simpa only [sub_zero] using! himag) hφ
  have hc : 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 2 / L⁻¹ =
      2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by rw [div_inv_eq_mul]; ring
  simpa only [Pi.zero_apply, zero_sub, hc] using he

/-- The actual corrected orbit supplies its derivative, weak gradient and
physical spatial cutoff estimate internally at every positive time. The
almost-everywhere event is for each fixed time, before all spatial cutoffs. -/
theorem complexForced_correctedOrbit_ae_physical_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t : ℝ} (ht : 0 < t) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∀ r : ℝ, 0 < r → ∃ (V : Lp ℂ 2 (reducedLaw Q))
      (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasDerivAt w V r ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (w r) G ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
          (∫ x, (φ x : ℂ) ^ 2 * star ((w r) (translate x ω)) * (-V (translate x ω))).re +
          (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
            (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
              (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖(w r) (translate x ω)‖ ^ 2) := by
  intro L w r hr
  obtain ⟨V, hd, hgen⟩ := Blueprint.centered_source_corrected_equation hP f ht r hr
  obtain ⟨G, hG, hpair⟩ := hgen
  have hgen : IsComplexGeneratorPair Q i ζ (w r) V := ⟨G, hG, hpair⟩
  exact ⟨V, G, hd, hG, hgen.ae_physical_cutoff_energy hG⟩

/-- A single measurable representative of the derivative orbit realizes the
physical FTC at each fixed time. Its spacetime integrability holds on one
environment event before all compact spatial sets and integer time windows.
No samplewise energy chain rule or pointwise time trace is assumed. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_physical_generatorFTC
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        (P t f) (translate x ω) - f (translate x ω) =
          ∫ s in Icc (0 : ℝ) (t : ℝ), U (s, translate x ω)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        ∀ᵐ x ∂volume.restrict K,
          ContinuousOn (fun s => f (translate x ω) +
            ∫ v in Icc (0 : ℝ) s, U (v, translate x ω)) (Icc (0 : ℝ) (n : ℝ)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative g
  have hi (t : ℝ) := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) t
  refine ⟨U, hU, heU, ?_, ?_⟩
  · intro t
    have hc := ae_spatial_coeFn_integral_joint_l2_representative
      (reducedLaw Q) (reducedLaw_stationary Q) (hi t) hU heU
    have hFTC : (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal g) = P t f - f := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
      exact hP.w6_integral_generator_orbit hfg t
    rw [hFTC] at hc
    have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (P t f - f)).measurable
      ((Lp.stronglyMeasurable (P t f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
      (Lp.coeFn_sub (P t f) f)
    filter_upwards [hc, hs] with ω hc hs
    filter_upwards [hc, hs] with x hc hs
    exact hs.symm.trans hc
  · have hl (n : ℕ) := ae_locally_integrable_joint_spatial_translate
      (reducedLaw Q) (reducedLaw_stationary Q)
      (integrable_joint_l2_representative (hi (n : ℝ)) hU heU)
    filter_upwards [ae_all_iff.mpr hl] with ω hω
    intro n K hK
    have hint := hω n K hK
    refine ⟨hint, ?_⟩
    filter_upwards [hint.prod_right_ae] with x hx
    exact continuousOn_const.add (intervalIntegral.continuousOn_primitive_Icc hx)

/-- Absolute continuity and the almost-everywhere derivative of the energy
of a complex integrable primitive. -/
theorem complexPrimitive_energy_regular {u : ℝ → ℂ} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b) (c : ℂ) :
    let w := fun s => c + ∫ v in a..s, u v
    AbsolutelyContinuousOnInterval (fun s => ‖w s‖ ^ 2) a b ∧
      (∀ᵐ s, s ∈ uIcc a b →
        deriv (fun r => ‖w r‖ ^ 2) s = 2 * (star (w s) * u s).re) := by
  intro w
  have hr : IntervalIntegrable (fun s => (u s).re) volume a b :=
    ⟨Complex.reCLM.integrable_comp hu.1, Complex.reCLM.integrable_comp hu.2⟩
  have hi : IntervalIntegrable (fun s => (u s).im) volume a b :=
    ⟨Complex.imCLM.integrable_comp hu.1, Complex.imCLM.integrable_comp hu.2⟩
  have hc (z : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => z) a b :=
    (LipschitzWith.const z).lipschitzOnWith.absolutelyContinuousOnInterval
  have hR := (hc c.re).fun_add
    (hr.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc)
  have hI := (hc c.im).fun_add
    (hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) left_mem_uIcc)
  have hwr : AbsolutelyContinuousOnInterval (fun s => (w s).re) a b := by
    apply hR.congr
    intro s hs
    have hus := hu.mono_set (uIcc_subset_uIcc left_mem_uIcc hs)
    change c.re + (∫ v in a..s, (u v).re) = c.re + (∫ v in a..s, u v).re
    exact congrArg (fun z => c.re + z) (Complex.reCLM.intervalIntegral_comp_comm hus)
  have hwi : AbsolutelyContinuousOnInterval (fun s => (w s).im) a b := by
    apply hI.congr
    intro s hs
    have hus := hu.mono_set (uIcc_subset_uIcc left_mem_uIcc hs)
    change c.im + (∫ v in a..s, (u v).im) = c.im + (∫ v in a..s, u v).im
    exact congrArg (fun z => c.im + z) (Complex.imCLM.intervalIntegral_comp_comm hus)
  have hE : AbsolutelyContinuousOnInterval (fun s => ‖w s‖ ^ 2) a b := by
    convert (hwr.fun_mul hwr).fun_add (hwi.fun_mul hwi) using 1
    funext s
    simp only [Complex.sq_norm, Complex.normSq_apply]
  have hd : ∀ᵐ s, s ∈ uIcc a b →
      deriv (fun r => ‖w r‖ ^ 2) s = 2 * (star (w s) * u s).re := by
    filter_upwards [hu.ae_hasDerivAt_integral] with s hs hmem
    have hw : HasDerivAt w (u s) s := (hs hmem a left_mem_uIcc).const_add c
    simpa only [Complex.inner, mul_comm (u s), starRingEnd_apply] using hw.norm_sq.deriv
  exact ⟨hE, hd⟩

/-- The temporal squared-norm identity for a complex integrable primitive.
Absolute continuity, rather than a merely a.e. derivative, justifies FTC. -/
theorem complexPrimitive_energy {u : ℝ → ℂ} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b) (c : ℂ) :
    let w := fun s => c + ∫ v in a..s, u v
    (∫ s in a..b, 2 * (star (w s) * u s).re) = ‖w b‖ ^ 2 - ‖c‖ ^ 2 := by
  intro w
  obtain ⟨hE, hd⟩ := complexPrimitive_energy_regular hu c
  calc
    (∫ s in a..b, 2 * (star (w s) * u s).re) =
        ∫ s in a..b, deriv (fun r => ‖w r‖ ^ 2) s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with s hs hmem
      exact (hs (uIoc_subset_uIcc hmem)).symm
    _ = ‖w b‖ ^ 2 - ‖c‖ ^ 2 := by
      simpa only [w, intervalIntegral.integral_same, add_zero] using hE.integral_deriv_eq_sub

/-- Physical temporal energy for actual generator-domain data. The primitive
uses one measurable derivative representative, and its final energy is the
literal semigroup orbit energy at each prescribed time. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_physical_generatorEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        ∀ᵐ x ∂volume.restrict K,
          let w := fun s => f (translate x ω) + ∫ v in (0 : ℝ)..s, U (v, translate x ω)
          (∫ s in (0 : ℝ)..(t : ℝ), 2 * (star (w s) * U (s, translate x ω)).re) =
            ‖(P t f) (translate x ω)‖ ^ 2 - ‖f (translate x ω)‖ ^ 2 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU, hFTC, _⟩ := hP.exists_ae_physical_generatorFTC hfg
  refine ⟨U, hU, heU, ?_⟩
  intro t
  have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) (t : ℝ)
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hU heU)
  filter_upwards [hl, hFTC t] with ω hω hend
  intro K hK
  filter_upwards [(hω K hK).prod_right_ae, ae_restrict_of_ae hend] with x hx he
  have hx' : IntegrableOn (fun s => U (s, translate x ω)) (uIcc (0 : ℝ) (t : ℝ)) := by
    simpa only [IntegrableOn, uIcc_of_le (NNReal.coe_nonneg t)] using! hx
  have he' : f (translate x ω) + (∫ s in (0 : ℝ)..(t : ℝ), U (s, translate x ω)) =
      (P t f) (translate x ω) := by
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
      ← integral_Icc_eq_integral_Ioc, ← he]
    exact add_sub_cancel _ _
  simpa only [he'] using complexPrimitive_energy hx'.intervalIntegrable (f (translate x ω))

/-- Squared integrability of an L2-valued path passes to its single joint
representative, with the actual L2 norm giving the section integral. -/
theorem integrable_sq_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable (fun p => ‖U p‖ ^ 2) (ν.prod μ) := by
  apply (integrable_prod_iff (hU.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).norm.integrable_sq).congr
    ((heq t).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)), ?_⟩
  apply hu.congr
  filter_upwards with t
  have hn : ‖u t‖ ^ 2 = ∫ ω, ‖(u t) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [heq t] with ω hω
  simp only [hω, Real.norm_eq_abs]
  exact (abs_of_nonneg (sq_nonneg ‖(u t) ω‖)).symm

/-- The existing stationary spacetime transport applied to the squared norm
produces local L2 on one event before every compact spatial region. -/
theorem ae_locally_memLp_joint_spatial_translate {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {U : T × FieldPair d → ℂ} (hU : Measurable U)
    (hi : Integrable (fun p => ‖U p‖ ^ 2) (ν.prod Q)) :
    ∀ᵐ ω ∂Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun p : Vec d × T => U (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod ν) := by
  have hc : Integrable (fun p => ((‖U p‖ ^ 2 : ℝ) : ℂ)) (ν.prod Q) :=
    by simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp hi
  filter_upwards [ae_locally_integrable_joint_spatial_translate Q hQ hc] with ω hω
  intro K hK
  have hm : Measurable (fun p : Vec d × T => U (p.2, translate p.1 ω)) :=
    hU.comp (measurable_snd.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_fst.prodMk measurable_const)))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  simpa only [Complex.reCLM_apply, Complex.ofReal_re] using! Complex.reCLM.integrable_comp (hω K hK)


/-- A continuous L2 path has locally square-integrable physical spacetime
sections for any of its measurable joint representatives. -/
theorem ae_spacetime_memLp_of_continuous_joint_l2
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {u : ℝ → Lp ℂ 2 Q} (hu : Continuous u)
    {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[Q] u s) :
    ∀ᵐ ω ∂Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun p : Vec d × ℝ => U (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  have hi (n : ℕ) : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc (0 : ℝ) (n : ℝ)) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  exact ae_all_iff.mpr fun n => ae_locally_memLp_joint_spatial_translate Q hQ
    hU (integrable_sq_joint_l2_representative (hi n) hU heU)

/-- Any measurable joint representative of the actual semigroup orbit is
locally L2 in spacetime, on one environment event before all compact spatial
sets and integer time windows. -/
theorem IsComplexEnvironmentSemigroup.ae_spacetime_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) {f : Lp ℂ 2 (reducedLaw Q)}
    {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun p : Vec d × ℝ => U (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  exact ae_spacetime_memLp_of_continuous_joint_l2 (reducedLaw Q) (reducedLaw_stationary Q)
    ((hP.2.2.1 f).comp continuous_real_toNNReal) hU heU

/-- Actual semigroup orbits supply their own jointly measurable, locally
square-integrable physical spacetime representative. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_spacetime_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => U (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  obtain ⟨U, hU, heU, _⟩ := hP.exists_joint_spatial_representative f
  exact ⟨U, hU, heU, hP.ae_spacetime_memLp hU heU⟩

/-- The actual source-corrected orbit supplies a single measurable physical
representative locally L2 in spacetime. The environment event precedes every
compact spatial set and integer time window. -/
theorem complexForced_correctedOrbit_ae_spacetime_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => U (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  intro w
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU⟩ := Blueprint.centered_source_joint_representative hP f t
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hc := (Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4))
  have hw : Continuous w := hu.add hc
  exact ⟨U, hU.measurable, heU,
    ae_spacetime_memLp_of_continuous_joint_l2 (reducedLaw Q) (reducedLaw_stationary Q)
      hw hU.measurable heU⟩

/-- A fixed positive-time restart realizes the corrected orbit's actual time
 derivative as one continuous semigroup orbit. The same representative is
 locally square-integrable in physical spacetime on one environment event. -/
theorem complexForced_correctedOrbit_derivative_ae_spacetime_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ U : ℝ × FieldPair d → ℂ,
      IsComplexGeneratorPair Q i ζ (P a.toNNReal f) g ∧ Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => U (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, hg⟩ := Blueprint.centered_source_positive_generator_domain hP f ha
  obtain ⟨U₀, hU₀, heU₀, _⟩ := hP.exists_joint_spatial_representative g
  let U : ℝ × FieldPair d → ℂ := fun p => U₀ (p.1 - a, p.2)
  have hU : Measurable U := hU₀.comp ((measurable_fst.sub_const a).prodMk measurable_snd)
  have heU (s : ℝ) : (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g :=
    heU₀ (s - a)
  have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  refine ⟨g, U, hg, hU, heU, ?_,
    ae_spacetime_memLp_of_continuous_joint_l2 (reducedLaw Q) (reducedLaw_stationary Q)
      hcont hU heU⟩
  intro r hr
  have hpos : 0 < r := ha.trans hr
  have hdiff : 0 < r - a := sub_pos.mpr hr
  have hd := Blueprint.centeredEquations_forward_hasDerivAt hP hg (r - a).toNNReal
    (by rwa [Real.coe_toNNReal (r - a) hdiff.le])
  rw [Real.coe_toNNReal (r - a) hdiff.le] at hd
  have hder := hd.scomp r ((hasDerivAt_id r).sub_const a)
  simp only [id_eq, one_smul] at hder
  have he (s : ℝ) (hs : a ≤ s) : P (s - a).toNNReal (P a.toNNReal f) = P s.toNNReal f := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1]
    apply congrArg (fun v : ℝ≥0 => P v f)
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal (s - a) (sub_nonneg.mpr hs),
      Real.coe_toNNReal a ha.le, Real.coe_toNNReal s (ha.le.trans hs)]
    ring
  have hdirect : HasDerivAt (fun s : ℝ => P s.toNNReal f) (P (r - a).toNNReal g) r := by
    apply hder.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact (he s hs.le).symm
  have hgen : IsComplexGeneratorPair Q i ζ (P r.toNNReal f) (P (r - a).toNNReal g) := by
    simpa only [he r hr.le] using hP.map_generator hg (r - a).toNNReal
  obtain ⟨G, hG, hm⟩ := hgen.integral_eq
  have heG := hG.unique (hP.gradientOrbit_spec f hpos)
  have hmean : (∫ ω, (P (r - a).toNNReal g) ω ∂reducedLaw Q) = hP.centeringSource f r := by
    rw [heG] at hm
    exact hm
  have hcenter := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r hdirect
  have hprimitive := ((Lp.constL 2 (reducedLaw Q) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r
    (Blueprint.hasDerivAt_centered_source_primitive hP f ht hpos)
  have hsum := hcenter.add hprimitive
  change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q (P s.toNNReal f) +
    Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v))
    (centeredComplexLpCLM Q (P (r - a).toNNReal g) +
      Lp.const 2 (reducedLaw Q) (hP.centeringSource f r)) r at hsum
  have hcancel : centeredComplexLpCLM Q (P (r - a).toNNReal g) +
      Lp.const 2 (reducedLaw Q) (hP.centeringSource f r) = P (r - a).toNNReal g := by
    rw [centeredComplexLpCLM_apply, centeredComplexLp, hmean, sub_add_cancel]
  rw [hcancel] at hsum
  have hw : HasDerivAt w (P (r - a).toNNReal g) r := by
    simpa only [w, centeredComplexLpCLM_apply, hP.centered_apply] using hsum
  obtain ⟨V, hV, hVgen⟩ := Blueprint.centered_source_corrected_equation hP f ht r hpos
  have hVe : V = P (r - a).toNNReal g := hV.unique hw
  exact ⟨hw, hVe ▸ hVgen⟩

/-- The actual corrected L2 orbit equals the time primitive of its restarted
 derivative on every closed interval strictly after the restart. -/
theorem complexForced_correctedOrbit_restart_integral
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ (P a.toNNReal f) g ∧
      ∀ b c : ℝ, a < b → a < c →
        (∫ s in b..c, P (s - a).toNNReal g) = w c - w b := by
  intro w
  obtain ⟨g, U, hg, hU, heU, hd, hlocal⟩ :=
    complexForced_correctedOrbit_derivative_ae_spacetime_memLp hP f ht ha
  refine ⟨g, hg, ?_⟩
  intro b c hb hc
  have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => (hd s ((lt_min hb hc).trans_le hs.1)).1) (hcont.intervalIntegrable b c)

/-- The same restarted derivative representative gives the physical FTC and
scalar energy balance of the literal corrected orbit between prescribed
positive times. The environment event precedes all compact spatial sets. -/
theorem complexForced_correctedOrbit_ae_physical_temporalEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ U : ℝ × FieldPair d → ℂ,
      IsComplexGeneratorPair Q i ζ (P a.toNNReal f) g ∧ Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K,
            let W := fun s => (w b) (translate x ω) + ∫ v in b..s, U (v, translate x ω)
            W c = (w c) (translate x ω) ∧
            (∫ s in b..c, 2 * (star (W s) * U (s, translate x ω)).re) =
              ‖(w c) (translate x ω)‖ ^ 2 - ‖(w b) (translate x ω)‖ ^ 2 := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, U, hg, hU, heU, hd, _⟩ :=
    complexForced_correctedOrbit_derivative_ae_spacetime_memLp hP f ht ha
  refine ⟨g, U, hg, hU, heU, ?_⟩
  intro b c hb hbc
  have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hi : IntegrableOn (fun s : ℝ => P (s - a).toNNReal g) (Icc b c) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC : (∫ s in Icc b c, P (s - a).toNNReal g) = w c - w b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => (hd s (hb.trans_le ((uIcc_of_le hbc ▸ hs).1))).1)
      (hcont.intervalIntegrable b c)
  have hc := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) hi hU heU
  rw [hFTC] at hc
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (w c - w b)).measurable
    ((Lp.stronglyMeasurable (w c)).measurable.sub (Lp.stronglyMeasurable (w b)).measurable)
    (Lp.coeFn_sub (w c) (w b))
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hU heU)
  filter_upwards [hc, hs, hl] with ω hc hs hl
  intro K hK
  filter_upwards [ae_restrict_of_ae hc, ae_restrict_of_ae hs,
    (hl K hK).prod_right_ae] with x hc hs hx
  have hu : IntervalIntegrable (fun s => U (s, translate x ω)) volume b c := by
    have hx' : IntegrableOn (fun s => U (s, translate x ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using! hx
    exact hx'.intervalIntegrable
  have he : (w b) (translate x ω) + (∫ s in b..c, U (s, translate x ω)) =
      (w c) (translate x ω) := by
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc,
      ← hc, hs]
    exact add_sub_cancel _ _
  exact ⟨he, by simpa only [he] using complexPrimitive_energy hu ((w b) (translate x ω))⟩

/-- The actual corrected field and its restarted derivative have an
integrable physical energy product on every compact spacetime window.
Both representatives and all local L2 hypotheses are supplied internally. -/
theorem complexForced_correctedOrbit_ae_spacetime_energyProduct
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ =>
          star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  intro w
  obtain ⟨W, hW, heW, hlocalW⟩ := complexForced_correctedOrbit_ae_spacetime_memLp hP f t
  obtain ⟨g, V, _, hV, heV, hd, hlocalV⟩ :=
    complexForced_correctedOrbit_derivative_ae_spacetime_memLp hP f ht ha
  refine ⟨g, W, V, hW, hV, heW, heV, fun r hr => (hd r hr).1, ?_⟩
  filter_upwards [hlocalW, hlocalV] with ω hωW hωV
  intro n K hK
  exact (hωW n K hK).star.integrable_mul (hωV n K hK)


/-- A variable upper endpoint preserves joint measurability of a scalar
primitive. This uses the measurable integral, so no pointwise integrability
hypothesis or choice of time-dependent exceptional sets is needed. -/
theorem measurable_complexPrimitive {Ω : Type*} [MeasurableSpace Ω]
    {V : ℝ × Ω → ℂ} (hV : Measurable V) (b : ℝ) :
    Measurable (fun p : ℝ × Ω => ∫ v in Icc b p.1, V (v, p.2)) := by
  have hm : Measurable (fun q : (ℝ × Ω) × ℝ =>
      (if b ≤ q.2 ∧ q.2 ≤ q.1.1 then V (q.2, q.1.2) else 0)) := by
    exact (hV.comp (measurable_snd.prodMk measurable_fst.snd)).ite
      ((measurableSet_le measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
  have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  simpa only [← integral_indicator measurableSet_Icc, Set.indicator, mem_Icc] using hi

/-- The chosen joint representative of the actual corrected orbit agrees
with the primitive of its chosen restarted derivative in physical spacetime.
Fubini gives a single environment event for the whole time interval. -/
theorem complexForced_correctedOrbit_ae_physical_primitive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ =>
          star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q,
          ∀ᵐ p ∂(volume : Measure (Vec d)).prod (volume.restrict (Icc b c)),
            W (p.2, translate p.1 ω) = (w b) (translate p.1 ω) +
              ∫ v in Icc b p.2, V (v, translate p.1 ω) := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, hW, hV, heW, heV, hd, henergy⟩ :=
    complexForced_correctedOrbit_ae_spacetime_energyProduct hP f ht ha
  refine ⟨g, W, V, hW, hV, heW, heV, hd, henergy, ?_⟩
  intro b c hb _hbc
  let F : ℝ × FieldPair d → ℂ := fun p =>
    (w b) p.2 + ∫ v in Icc b p.1, V (v, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable (w b)).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hV b)
  have he (s : ℝ) (hs : s ∈ Icc b c) :
      (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] fun ω => F (s, ω) := by
    have hcont : Continuous (fun r : ℝ => P (r - a).toNNReal g) :=
      (hP.2.2.1 g).comp (continuous_real_toNNReal.comp
        (continuous_id.sub continuous_const))
    have hint : IntegrableOn (fun r : ℝ => P (r - a).toNNReal g) (Icc b s) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    have hi := coeFn_integral_joint_l2_representative hint hV heV
    have hFTC : (∫ v in Icc b s, P (v - a).toNNReal g) = w s - w b := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr => hd r (hb.trans_le ((uIcc_of_le hs.1 ▸ hr).1)))
        (hcont.intervalIntegrable b s)
    rw [hFTC] at hi
    filter_upwards [heW s, hi, Lp.coeFn_sub (w s) (w b)] with ω hω hi hsub
    change W (s, ω) = (w b) ω + ∫ v in Icc b s, V (v, ω)
    rw [hω, ← hi, hsub]
    exact (add_sub_cancel _ _).symm
  have hmW := measurable_joint_spatial_translate hW
  have hmF := measurable_joint_spatial_translate hF
  have hephys : ∀ᵐ s ∂volume.restrict (Icc b c),
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod (reducedLaw Q),
        W (s, translate p.1 p.2) = F (s, translate p.1 p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (hmW.comp (measurable_const.prodMk measurable_id))
      (hmF.comp (measurable_const.prodMk measurable_id)))).mpr
    exact ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae
        (he s hs)
  have heprod := (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun hmW hmF)).mpr hephys
  have hswap := (measurePreserving_prodAssoc
    (volume.restrict (Icc b c)) (volume : Measure (Vec d)) (reducedLaw Q))
  have heassoc := hswap.quasiMeasurePreserving.ae heprod
  have henv := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heassoc)
  filter_upwards [henv] with ω hω
  exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae hω


/-- Integration by parts for an absolutely continuous temporal cutoff and
the energy of a complex integrable primitive. -/
theorem complexPrimitive_weighted_energy {u : ℝ → ℂ} {a b : ℝ}
    (hu : IntervalIntegrable u volume a b) (c : ℂ)
    {η : ℝ → ℝ} (hη : AbsolutelyContinuousOnInterval η a b) :
    let w := fun s => c + ∫ v in a..s, u v
    (∫ s in a..b, η s * (2 * (star (w s) * u s).re)) =
      η b * ‖w b‖ ^ 2 - η a * ‖c‖ ^ 2 -
        ∫ s in a..b, deriv η s * ‖w s‖ ^ 2 := by
  intro w
  obtain ⟨hE, hd⟩ := complexPrimitive_energy_regular hu c
  calc
    _ = ∫ s in a..b, η s * deriv (fun r => ‖w r‖ ^ 2) s := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hd] with s hs hmem
      rw [hs (uIoc_subset_uIcc hmem)]
    _ = _ := by
      simpa only [w, intervalIntegral.integral_same, add_zero] using
        hη.integral_mul_deriv_eq_deriv_mul hE

/-- Physical integration by parts for every absolutely continuous temporal
cutoff, using the actual joint orbit and restarted derivative. The full
measure event is chosen before the cutoff. -/
theorem complexForced_correctedOrbit_ae_physical_jointWeightedEnergy_regular
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ =>
          star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K, ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c →
            (∫ s in b..c, η s * (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re)) =
              η c * ‖(w c) (translate x ω)‖ ^ 2 - η b * ‖(w b) (translate x ω)‖ ^ 2 -
                ∫ s in b..c, deriv η s * ‖W (s, translate x ω)‖ ^ 2 := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, hW, hV, heW, heV, hd, henergy, hprimitive⟩ :=
    complexForced_correctedOrbit_ae_physical_primitive hP f ht ha
  have hregular (r : ℝ) (hr : a < r) :
      HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g) := by
    obtain ⟨v, hv, hgen⟩ := Blueprint.centered_source_corrected_equation hP f ht r (ha.trans hr)
    have he : v = P (r - a).toNNReal g := hv.unique (hd r hr)
    exact ⟨hd r hr, he ▸ hgen⟩
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, henergy, ?_⟩
  intro b c hb hbc
  have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hi : IntegrableOn (fun s : ℝ => P (s - a).toNNReal g) (Icc b c) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC : (∫ s in Icc b c, P (s - a).toNNReal g) = w c - w b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hd s (hb.trans_le ((uIcc_of_le hbc ▸ hs).1)))
      (hcont.intervalIntegrable b c)
  have hc := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) hi hV heV
  rw [hFTC] at hc
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (w c - w b)).measurable
    ((Lp.stronglyMeasurable (w c)).measurable.sub (Lp.stronglyMeasurable (w b)).measurable)
    (Lp.coeFn_sub (w c) (w b))
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hV heV)
  filter_upwards [hprimitive b c hb hbc, hc, hs, hl] with ω hprim hc hs hl
  intro K hK
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hprim),
    ae_restrict_of_ae hc, ae_restrict_of_ae hs, (hl K hK).prod_right_ae]
    with x hx hc hs hv
  have hu : IntervalIntegrable (fun s => V (s, translate x ω)) volume b c := by
    have hv' : IntegrableOn (fun s => V (s, translate x ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using! hv
    exact hv'.intervalIntegrable
  have hend : (w b) (translate x ω) + (∫ s in b..c, V (s, translate x ω)) =
      (w c) (translate x ω) := by
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc, ← hc, hs]
    exact add_sub_cancel _ _
  intro η hη
  have heq : ∀ᵐ s ∂volume.restrict (Icc b c),
      W (s, translate x ω) = (w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω) := by
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  have hleft :
      (∫ s in b..c, η s * (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re)) =
      ∫ s in b..c, η s * (2 * (star ((w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω)) * V (s, translate x ω)).re) := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  have hright : (∫ s in b..c, deriv η s * ‖W (s, translate x ω)‖ ^ 2) =
      ∫ s in b..c, deriv η s * ‖(w b) (translate x ω) +
        ∫ v in b..s, V (v, translate x ω)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  rw [hleft, hright]
  simpa only [hend] using complexPrimitive_weighted_energy hu ((w b) (translate x ω)) hη

/-- Temporal cutoff energy for the actual corrected orbit. -/
theorem complexForced_correctedOrbit_ae_physical_jointWeightedEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ =>
          star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K, ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c →
            (∫ s in b..c, η s * (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re)) =
              η c * ‖(w c) (translate x ω)‖ ^ 2 - η b * ‖(w b) (translate x ω)‖ ^ 2 -
                ∫ s in b..c, deriv η s * ‖W (s, translate x ω)‖ ^ 2 := by
  intro w
  obtain ⟨g, W, V, hW, hV, heW, heV, _, henergy, htime⟩ :=
    complexForced_correctedOrbit_ae_physical_jointWeightedEnergy_regular hP f ht ha
  exact ⟨g, W, V, hW, hV, heW, heV, henergy, htime⟩

/-- The temporal energy identity uses the same joint physical orbit and
restarted derivative as the spacetime energy product. It holds on one
environment event before every compact spatial region. -/
theorem complexForced_correctedOrbit_ae_physical_jointEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        Integrable (fun p : Vec d × ℝ =>
          star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K,
            (∫ s in b..c, 2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re) =
              ‖(w c) (translate x ω)‖ ^ 2 - ‖(w b) (translate x ω)‖ ^ 2 := by
  intro w
  obtain ⟨g, W, V, hW, hV, heW, heV, henergy, hweighted⟩ :=
    complexForced_correctedOrbit_ae_physical_jointWeightedEnergy hP f ht ha
  refine ⟨g, W, V, hW, hV, heW, heV, henergy, ?_⟩
  intro b c hb hbc
  filter_upwards [hweighted b c hb hbc] with ω hω
  intro K hK
  filter_upwards [hω K hK] with x hx
  have hone : AbsolutelyContinuousOnInterval (fun _ : ℝ => (1 : ℝ)) b c :=
    (LipschitzWith.const (1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  simpa only [one_mul, deriv_const, zero_mul, intervalIntegral.integral_zero, sub_zero]
    using hx (fun _ => 1) hone


/-- A continuous weight on a compact spatial/time rectangle preserves
integrability for its literal product restriction measure. -/
theorem integrable_spacetime_continuousOn_mul {d : ℕ}
    {K : Set (Vec d)} (hK : IsCompact K) {b c : ℝ}
    {F Ψ : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hΨ : ContinuousOn Ψ (K ×ˢ Icc b c)) :
    Integrable (fun p => Ψ p * F p)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
  rw [Measure.prod_restrict] at hF ⊢
  exact IntegrableOn.continuousOn_mul hΨ hF (hK.prod isCompact_Icc)

/-- Spatial integration of the actual corrected-orbit temporal cutoff
identity, with both time/space orders justified by local L2 integrability.
The environment event precedes the spatial region and both cutoffs. -/
theorem complexForced_correctedOrbit_ae_physical_spatialWeightedEnergy_regular
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ φ : Vec d → ℝ, Continuous φ → ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c → ContinuousOn (deriv η) (Icc b c) →
            (∫ s in Icc b c, η s * (∫ x in K, φ x ^ 2 *
              (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) =
              η c * (∫ x in K, φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) -
              η b * (∫ x in K, φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) -
              ∫ s in Icc b c, deriv η s *
                (∫ x in K, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2) := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, hW, hV, heW, heV, hregular, _, htemporal⟩ :=
    complexForced_correctedOrbit_ae_physical_jointWeightedEnergy_regular hP f ht ha
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hv : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  intro b c hb hbc
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖P (s - a).toNNReal g‖ ^ 2) (Icc b c) volume :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative
      hwI hW heW)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      hvI hV heV)
  filter_upwards [htemporal b c hb hbc, hlocalW, hlocalV,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) (w b),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) (w c)]
    with ω htime hlocW hlocV hwb hwc
  intro K hK φ hφ η hη hη'
  let X : Vec d × ℝ → ℂ := fun p => W (p.2, translate p.1 ω)
  let Y : Vec d × ℝ → ℂ := fun p => V (p.2, translate p.1 ω)
  let A : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * η p.2 * (2 * (star (X p) * Y p).re)
  let B : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * deriv η p.2 * ‖X p‖ ^ 2
  have hηc : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc] using hη.continuousOn
  have hweight (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc b c)) :
      ContinuousOn (fun p : Vec d × ℝ => φ p.1 ^ 2 * ψ p.2) (K ×ˢ Icc b c) :=
    ((hφ.pow 2).comp continuous_fst).continuousOn.mul
      (hψ.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hprod : Integrable (fun p => star (X p) * Y p)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    (hlocW K hK).star.integrable_mul (hlocV K hK)
  have hA : Integrable A ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((Complex.reCLM.integrable_comp hprod).const_mul 2) (hweight η hηc)
  have hB : Integrable B ((volume.restrict K).prod (volume.restrict (Icc b c))) :=
    integrable_spacetime_continuousOn_mul hK
      ((memLp_two_iff_integrable_sq_norm (hlocW K hK).aestronglyMeasurable).mp (hlocW K hK))
      (hweight (deriv η) hη')
  have hend (s : ℝ) (hs : ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => (w s) (translate x ω)) 2 (volume.restrict K)) :
      Integrable (fun x => φ x ^ 2 * ‖(w s) (translate x ω)‖ ^ 2) (volume.restrict K) :=
    IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn
      ((memLp_two_iff_integrable_sq_norm (hs K hK).aestronglyMeasurable).mp (hs K hK)) hK
  have heq : ∀ᵐ x ∂volume.restrict K,
      (∫ s in Icc b c, A (x, s)) =
        η c * (φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) -
        η b * (φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) - ∫ s in Icc b c, B (x, s) := by
    filter_upwards [htime K hK] with x hx
    have he := hx η hη
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc] at he
    simp only [A, B, X, Y]
    simp_rw [mul_assoc (φ x ^ 2)]
    rw [integral_const_mul, integral_const_mul, he]
    ring
  calc
    _ = ∫ s in Icc b c, ∫ x in K, A (x, s) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [A, X, Y]
      ring
    _ = ∫ x in K, ∫ s in Icc b c, A (x, s) := (integral_integral_swap hA).symm
    _ = η c * (∫ x in K, φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) -
        η b * (∫ x in K, φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) -
        ∫ x in K, ∫ s in Icc b c, B (x, s) := by
      have hsplit := integral_sub
        (((hend c hwc).const_mul (η c)).sub ((hend b hwb).const_mul (η b)))
        hB.integral_prod_left
      have hends := integral_sub ((hend c hwc).const_mul (η c))
        ((hend b hwb).const_mul (η b))
      simp only [Pi.sub_apply] at hsplit hends
      rw [integral_congr_ae heq, hsplit, hends, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [integral_integral_swap hB]
      congr 1
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [B, X]
      ring

/-- Spatially integrated temporal cutoff energy for the actual corrected orbit. -/
theorem complexForced_correctedOrbit_ae_physical_spatialWeightedEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      ∀ b c : ℝ, a < b → b ≤ c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ φ : Vec d → ℝ, Continuous φ → ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c → ContinuousOn (deriv η) (Icc b c) →
            (∫ s in Icc b c, η s * (∫ x in K, φ x ^ 2 *
              (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) =
              η c * (∫ x in K, φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) -
              η b * (∫ x in K, φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) -
              ∫ s in Icc b c, deriv η s *
                (∫ x in K, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2) := by
  intro w
  obtain ⟨g, W, V, hW, hV, heW, heV, _, htime⟩ :=
    complexForced_correctedOrbit_ae_physical_spatialWeightedEnergy_regular hP f ht ha
  exact ⟨g, W, V, hW, hV, heW, heV, htime⟩

/-- The centered orbit and its scalar source correction retain the actual
positive-time semigroup gradient. -/
theorem complexForced_correctedOrbit_gradient_spec
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) {s : ℝ} (hs : 0 < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
        Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v))
      (hP.gradientOrbit (centeredComplexLp Q f) s) := by
  let := reducedLaw_probability Q
  have hG := hP.centered_gradientOrbit_spec (centeredComplexLp Q f) hs
  have hc := hasComplexHorizontalGradient_const (reducedLaw Q)
    (reducedLaw_stationary Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
  intro j
  simpa only [add_zero] using (hG j).add (hc j)

/-- A single joint representative of every actual corrected-orbit gradient
is locally spacetime L2 on each prescribed interval away from zero. The
environment event precedes every compact spatial set and coordinate. -/
theorem complexForced_correctedOrbit_ae_spacetime_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      ∀ b c : ℝ, 0 < b →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K → ∀ j,
          MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
            ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
  let := reducedLaw_probability Q
  obtain ⟨D, hD, heD⟩ := hP.exists_joint_gradient_representative (centeredComplexLp Q f)
  refine ⟨D, hD, heD, ?_⟩
  intro b c hb
  have hlocal (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit (centeredComplexLp Q f) s) j‖ ^ 2)
        (Icc b c) volume :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le hb hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  exact fun K hK j => hω j K hK

/-- Joint representatives of a generator/gradient family satisfy physical
cutoff coercivity for almost every time in almost every environment. The
spatial test is fixed before exchanging the two almost-everywhere events. -/
theorem ae_joint_physical_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {W V : ℝ × FieldPair d → ℂ} {D : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V) (hD : ∀ j, Measurable (D j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))).re +
        (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2) := by
  intro L
  let := reducedLaw_probability Q
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hφm : Measurable (fun q : (ℝ × FieldPair d) × Vec d => φ q.2) :=
    hφ.1.continuous.measurable.comp measurable_snd
  have hder j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  let A := (fun p : ℝ × FieldPair d =>
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2)))
  have hA : Measurable A :=
    measurable_const.mul ((hφm.pow_const 2).mul
      (Finset.measurable_sum _ fun j _ => ((hshift (hD j)).norm.pow_const 2))).stronglyMeasurable.integral_prod_right'.measurable
  let B := (fun p : ℝ × FieldPair d =>
      (∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))).re +
        (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (p.1, translate x p.2)‖ ^ 2))
  have hB : Measurable B := by
    have hmain : Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, (φ x : ℂ) ^ 2 * star (W (p.1, translate x p.2)) * (-V (p.1, translate x p.2))) :=
      (((Complex.continuous_ofReal.measurable.comp hφm).pow_const 2).mul
      ((hshift hW).stronglyMeasurable.star.measurable) |>.mul (hshift hV).neg).stronglyMeasurable.integral_prod_right'.measurable
    have herr : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        (‖ζ‖ ^ 2 * φ q.2 ^ 2 + (∑ j, (coordinateDerivative j φ q.2) ^ 2)) *
          ‖W (q.1.1, translate q.2 q.1.2)‖ ^ 2) :=
      ((measurable_const.mul (hφm.pow_const 2)).add
      (Finset.measurable_sum _ fun j _ =>
        (((hder j).measurable.comp measurable_snd).pow_const 2))).mul
          ((hshift hW).norm.pow_const 2)
    exact (Complex.continuous_re.measurable.comp hmain).add
      (measurable_const.mul herr.stronglyMeasurable.integral_prod_right'.measurable)
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  filter_upwards [(hgen s hs).ae_physical_cutoff_energy (hgrad s hs), hew, hev,
    ae_all_iff.mpr hed] with ω henergy hw hv hd
  have hdall : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j,
      D j (s, translate x ω) = G s j (translate x ω) := ae_all_iff.mpr hd
  have hleft : (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2)) =
      ∫ x, φ x ^ 2 * (∑ j, ‖G s j (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hdall] with x hx
    simp only [hx]
  have hmain : (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))) =
      ∫ x, (φ x : ℂ) ^ 2 * star ((u s) (translate x ω)) * (-(v s) (translate x ω)) := by
    apply integral_congr_ae
    filter_upwards [hw, hv] with x hx hy
    change W (s, translate x ω) = _ at hx
    change V (s, translate x ω) = _ at hy
    rw [hx, hy]
  have herr : (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ‖W (s, translate x ω)‖ ^ 2) =
      ∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
        ‖(u s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    change W (s, translate x ω) = _ at hx
    rw [hx]
  change (L⁻¹ / 4) * _ ≤ _ + _ * _
  rw [hleft, hmain, herr]
  exact henergy φ hφ

/-- The actual corrected orbit, restarted derivative and gradient satisfy the
spatial coercivity and temporal cutoff identities on the same environment
event for each prescribed time interval and smooth spatial cutoff. -/
theorem complexForced_correctedOrbit_ae_physical_jointCutoffEnergy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ᵐ ω ∂reducedLaw Q,
          (∀ K : Set (Vec d), IsCompact K → ∀ j,
            MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
              ((volume.restrict K).prod (volume.restrict (Icc b c)))) ∧
          (∀ᵐ s ∂volume.restrict (Icc b c),
            (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
              (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) * (-V (s, translate x ω))).re +
              (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
                (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                  (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2)) ∧
          ∀ K : Set (Vec d), IsCompact K → ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η b c → ContinuousOn (deriv η) (Icc b c) →
            (∫ s in Icc b c, η s * (∫ x in K, φ x ^ 2 *
              (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) =
              η c * (∫ x in K, φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) -
              η b * (∫ x in K, φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) -
              ∫ s in Icc b c, deriv η s *
                (∫ x in K, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨g, W, V, hW, hV, heW, heV, hregular, htime⟩ :=
    complexForced_correctedOrbit_ae_physical_spatialWeightedEnergy_regular hP f ht ha
  obtain ⟨D, hD, heD, hlocal⟩ :=
    complexForced_correctedOrbit_ae_spacetime_gradient hP f
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  intro b c hb hbc φ hφ
  have hcoer := ae_joint_physical_cutoff_energy (b := b) (c := c) (u := w)
    (v := fun s => P (s - a).toNNReal g)
    (G := fun s j => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
    (fun s hs => (hregular s (hb.trans_le hs.1)).2)
    (fun s hs => complexForced_correctedOrbit_gradient_spec hP f t
      (ha.trans (hb.trans_le hs.1))) hW hV hD heW heV heD hφ
  filter_upwards [hcoer, hlocal b c (ha.trans hb), htime b c hb hbc]
    with ω hc hl htω
  exact ⟨hl, hc, fun K hK η hη hη' => htω K hK φ hφ.1.continuous η hη hη'⟩

/-- A spatial weight supported on a compact set turns local spacetime
integrability into integrability of the whole-space spatial integral in time. -/
theorem integrable_time_integral_compact_spatial_weight {d : ℕ}
    {𝕜 : Type*} [RCLike 𝕜] {K : Set (Vec d)} (hK : IsCompact K)
    {b c : ℝ} {F : Vec d × ℝ → 𝕜}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    {ψ : Vec d → 𝕜} (hψ : Continuous ψ) (hzero : ∀ x, x ∉ K → ψ x = 0) :
    Integrable (fun s => ∫ x, ψ x * F (x, s)) (volume.restrict (Icc b c)) := by
  have hi : Integrable (fun p : Vec d × ℝ => ψ p.1 * F p)
      ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    rw [Measure.prod_restrict] at hF ⊢
    exact IntegrableOn.continuousOn_mul (hψ.comp continuous_fst).continuousOn
      hF (hK.prod isCompact_Icc)
  convert hi.integral_prod_right using 1
  ext s
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by rw [hzero x hx, zero_mul])).symm

/-- Local spacetime L2 justifies time integration of all three terms of
physical cutoff coercivity, including its whole-space generator product. -/
theorem physical_cutoff_energy_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c : ℝ}
    {W V : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hW : MemLp W 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hcoer : ∀ᵐ s ∂volume.restrict (Icc b c),
      ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
          (∫ x, φ x ^ 2 * (∑ j, ‖D j (x, s)‖ ^ 2)) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re +
          (2 * (d : ℝ) * ((d : ℝ) + 1) * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
            (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
              ‖W (x, s)‖ ^ 2)) :
    ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * (∑ j, ‖D j (x, s)‖ ^ 2))) ≤
      (∫ s in Icc b c, η s *
        (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re) +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * (Real.exp (2 * Λ₀) * Λ₀) ^ 3) *
        (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + (∑ j, (coordinateDerivative j φ x) ^ 2)) *
            ‖W (x, s)‖ ^ 2)) := by
  have hK := hφ.2.1
  have hz : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hdz j x (hx : x ∉ tsupport φ) : coordinateDerivative j φ x = 0 := by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  have hgrad := integrable_time_integral_compact_spatial_weight hK
    (integrable_finsetSum Finset.univ (fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j)))
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have herr := integrable_time_integral_compact_spatial_weight hK
    (ψ := fun x => ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2)
    ((memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx])
  have hm := integrable_time_integral_compact_spatial_weight hK
    (hW.star.integrable_mul hV.neg)
    ((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2)
    (fun x hx => by simp [Function.comp_def, hz x hx])
  have hmain : Integrable (fun s => η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (x, s)) * (-V (x, s))).re)
      (volume.restrict (Icc b c)) := by
    simp_rw [mul_assoc] at ⊢
    exact IntegrableOn.continuousOn_mul hη (Complex.reCLM.integrable_comp hm) isCompact_Icc
  have hg := IntegrableOn.continuousOn_mul hη hgrad isCompact_Icc
  have he := IntegrableOn.continuousOn_mul hη herr isCompact_Icc
  have hi := integral_mono_ae (hg.const_mul ((Real.exp (2 * Λ₀) * Λ₀)⁻¹ / 4))
    (hmain.add (he.const_mul
      (2 * (d : ℝ) * ((d : ℝ) + 1) * (Real.exp (2 * Λ₀) * Λ₀) ^ 3)))
    (by
      filter_upwards [hcoer, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.pow_apply]
      nlinarith [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.pow_apply] at hi
  simpa only [integral_add hmain (he.const_mul _), integral_const_mul] using hi

/-- Time-integrated physical cutoff coercivity for the actual corrected
semigroup orbit and its actual restarted derivative and horizontal gradient. -/
theorem complexForced_correctedOrbit_ae_physical_integratedCutoffEnergy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ η : ℝ → ℝ, ContinuousOn η (Icc b c) →
          (∀ s ∈ Icc b c, 0 ≤ η s) → ∀ᵐ ω ∂reducedLaw Q,
          (L⁻¹ / 4) * (∫ s in Icc b c, η s *
            (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2))) ≤
            (∫ s in Icc b c, η s *
              (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) *
                (-V (s, translate x ω))).re) +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (∫ s in Icc b c, η s *
                (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                  (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2)) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, hcut⟩ :=
    complexForced_correctedOrbit_ae_physical_jointCutoffEnergy hP f ht ha
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hv : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  intro b c hb hbc φ hφ η hη hηpos
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖P (s - a).toNNReal g‖ ^ 2) (Icc b c) volume :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hvI hV heV)
  filter_upwards [hcut b c hb hbc φ hφ, hlocalW, hlocalV] with ω hc hlW hlV
  exact physical_cutoff_energy_time_integral hφ (hlW _ hφ.2.1)
    (hlV _ hφ.2.1) (hc.1 _ hφ.2.1) hη hηpos hc.2.1

/-- On a compactly supported spatial test, the generator pairing is
minus one half of the derivative of the squared modulus. -/
theorem physical_cutoff_generator_pairing_eq {d : ℕ} {φ : Vec d → ℝ}
    {U V : Vec d → ℂ}
    (hi : Integrable (fun x => (φ x : ℂ) ^ 2 * star (U x) * V x)
      (volume.restrict (tsupport φ))) :
    (∫ x, (φ x : ℂ) ^ 2 * star (U x) * (-V x)).re =
      -(∫ x, φ x ^ 2 * (2 * (star (U x) * V x).re)) / 2 := by
  have hz x (hx : x ∉ tsupport φ) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hC := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := tsupport φ)
    (f := fun x => (φ x : ℂ) ^ 2 * star (U x) * V x)
    (fun x hx => by simp [hz x hx])
  have hR := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (s := tsupport φ)
    (f := fun x => φ x ^ 2 * (2 * (star (U x) * V x).re))
    (fun x hx => by simp [hz x hx])
  have hr : (∫ x in tsupport φ, (φ x : ℂ) ^ 2 * star (U x) * V x).re =
      ∫ x in tsupport φ, φ x ^ 2 * (star (U x) * V x).re := by
    calc
      _ = ∫ x in tsupport φ, Complex.reCLM ((φ x : ℂ) ^ 2 * star (U x) * V x) :=
        (Complex.reCLM.integral_comp_comm hi).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [Complex.reCLM_apply, mul_assoc, ← Complex.ofReal_pow, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [mul_neg]
  rw [integral_neg, Complex.neg_re, ← hC, hr, ← hR]
  have he : (∫ x in tsupport φ, φ x ^ 2 * (2 * (star (U x) * V x).re)) =
      2 * (∫ x in tsupport φ, φ x ^ 2 * (star (U x) * V x).re) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  rw [he]
  ring

/-- Physical cutoff energy with the actual temporal endpoint values. This
is the Caccioppoli inequality before choosing cutoffs and absorbing the force. -/
theorem complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c →
          ContinuousOn (deriv η) (Icc b c) →
          (∀ s ∈ Icc b c, 0 ≤ η s) → ∀ᵐ ω ∂reducedLaw Q,
          (L⁻¹ / 4) * (∫ s in Icc b c, η s *
            (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2))) ≤
            (η b * (∫ x, φ x ^ 2 * ‖(w b) (translate x ω)‖ ^ 2) -
              η c * (∫ x, φ x ^ 2 * ‖(w c) (translate x ω)‖ ^ 2) +
              (∫ s in Icc b c, deriv η s *
                (∫ x, φ x ^ 2 * ‖W (s, translate x ω)‖ ^ 2))) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (∫ s in Icc b c, η s *
                (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                  (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖W (s, translate x ω)‖ ^ 2)) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, hcut⟩ :=
    complexForced_correctedOrbit_ae_physical_jointCutoffEnergy hP f ht ha
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hv : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  intro b c hb hbc φ hφ η hη hη' hηpos
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖P (s - a).toNNReal g‖ ^ 2) (Icc b c) volume :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hvI hV heV)
  filter_upwards [hcut b c hb hbc φ hφ, hlocalW, hlocalV] with ω hc hlW hlV
  have hηc : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc] using hη.continuousOn
  have hineq := physical_cutoff_energy_time_integral hφ (hlW _ hφ.2.1)
    (hlV _ hφ.2.1) (hc.1 _ hφ.2.1) hηc hηpos hc.2.1
  have hp := (hlW (tsupport φ) hφ.2.1).star.integrable_mul
    (hlV (tsupport φ) hφ.2.1)
  have hpφ : Integrable (fun p : Vec d × ℝ =>
      (φ p.1 : ℂ) ^ 2 * star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω))
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
    have hi : Integrable (fun p : Vec d × ℝ =>
        (φ p.1 : ℂ) ^ 2 * (star (W (p.2, translate p.1 ω)) * V (p.2, translate p.1 ω)))
        ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))) := by
      rw [Measure.prod_restrict] at hp ⊢
      exact IntegrableOn.continuousOn_mul
        (((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).comp
          continuous_fst).continuousOn hp (hφ.2.1.prod isCompact_Icc)
    simpa only [mul_assoc] using hi
  have hpair : (∫ s in Icc b c, η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (W (s, translate x ω)) *
        (-V (s, translate x ω))).re) =
      -(∫ s in Icc b c, η s * (∫ x, φ x ^ 2 *
        (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
    calc
      _ = ∫ s in Icc b c, -(η s * (∫ x, φ x ^ 2 *
          (2 * (star (W (s, translate x ω)) * V (s, translate x ω)).re))) / 2 := by
        apply integral_congr_ae
        filter_upwards [hpφ.prod_left_ae] with s hs
        rw [physical_cutoff_generator_pairing_eq hs]
        ring
      _ = _ := by rw [integral_div, integral_neg]
  have hres (F : Vec d → ℝ) :
      (∫ x in tsupport φ, φ x ^ 2 * F x) = ∫ x, φ x ^ 2 * F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have htime := hc.2.2 (tsupport φ) hφ.2.1 η hη hη'
  simp_rw [hres] at htime
  rw [hpair] at hineq
  linarith

/-- Smooth physical cutoffs use the explicit Euclidean balls on the inherited
coordinate carrier. One derivative constant works for every center and radius. -/
theorem exists_physical_euclidean_cutoff (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : Vec d, ∀ r : ℝ, 0 < r →
      ∃ φ : Vec d → ℝ, IsSpatialTest univ φ ∧
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x, euclideanNorm (x - z) ≤ r → φ x = 1) ∧
        (∀ x, 2 * r ≤ euclideanNorm (x - z) → φ x = 0) ∧
        ∀ j x, |coordinateDerivative j φ x| ≤ B / r := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨1, 3 / 2, by norm_num, by norm_num⟩
  let ψ : Vec d → ℝ := b ∘ J
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.comp J.contDiff
  have hc : HasCompactSupport ψ := b.hasCompactSupport.comp_homeomorph J.toHomeomorph
  obtain ⟨N, hN⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hs.continuous_fderiv (by simp))
  let B := max N 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hDb x : ‖fderiv ℝ ψ x‖ ≤ B :=
    (hN x).trans ((le_max_left N 0).trans (le_add_of_nonneg_right zero_le_one))
  refine ⟨B, hB, ?_⟩
  intro z r hr
  let T : Vec d → Vec d := fun x => r⁻¹ • (x - z)
  let φ : Vec d → ℝ := ψ ∘ T
  have hT : ContDiff ℝ (⊤ : ℕ∞) T := by dsimp [T]; fun_prop
  have hhome : ∃ H : Homeomorph (Vec d) (Vec d), (H : Vec d → Vec d) = T := by
    refine ⟨(Homeomorph.subRight z).trans (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne'))), ?_⟩
    rfl
  obtain ⟨H, hH⟩ := hhome
  have hφ : IsSpatialTest univ φ := by
    refine ⟨hs.comp hT, ?_, subset_univ _⟩
    change HasCompactSupport (ψ ∘ T)
    rw [← hH]
    exact hc.comp_homeomorph H
  refine ⟨φ, hφ, fun x => ⟨b.nonneg, b.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    have h : euclideanNorm (T x) ≤ 1 := by
      dsimp [T]
      rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      exact (inv_mul_le_iff₀ hr).mpr (by simpa using hx)
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply, ← TimeChange.euclideanNorm_eq_norm_toLp] using h
  · intro x hx
    apply b.zero_of_le_dist
    have h : (3 / 2 : ℝ) ≤ euclideanNorm (T x) := by
      dsimp [T]
      rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      apply (le_inv_mul_iff₀ hr).mpr
      linarith
    simpa only [dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply, ← TimeChange.euclideanNorm_eq_norm_toLp] using h
  · intro j x
    have hder : fderiv ℝ φ x =
        (fderiv ℝ ψ (T x)).comp (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) := by
      apply HasFDerivAt.fderiv
      exact (hs.differentiable (by simp) (T x)).hasFDerivAt.comp x
        (((hasFDerivAt_id x).sub_const z).const_smul r⁻¹)
    change |(fderiv ℝ φ x) (unitVector j)| ≤ _
    rw [hder, ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, abs_mul,
      abs_of_pos (inv_pos.mpr hr)]
    have hu : ‖unitVector j‖ ≤ (1 : ℝ) := by
      apply pi_norm_le_iff_of_nonneg zero_le_one |>.mpr
      intro k
      simp only [unitVector, Pi.single_apply]
      split_ifs <;> norm_num
    have hd : |(fderiv ℝ ψ (T x)) (unitVector j)| ≤ B := by
      calc
        _ ≤ ‖fderiv ℝ ψ (T x)‖ * ‖unitVector j‖ := by
          simpa only [Real.norm_eq_abs] using (fderiv ℝ ψ (T x)).le_opNorm (unitVector j)
        _ ≤ B * 1 := mul_le_mul (hDb _) hu (norm_nonneg _) hB.le
        _ = B := mul_one _
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr hr.le)

/-- A smooth temporal cutoff vanishes initially and controls the upper half
of the time interval, with the parabolic inverse-time derivative bound. -/
theorem exists_physical_temporal_cutoff {b c : ℝ} (hbc : b < c) :
    ∃ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c ∧
      ContinuousOn (deriv η) (Icc b c) ∧ η b = 0 ∧ η c = 1 ∧
      ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
        0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) ∧
        ((b + c) / 2 ≤ s → 1 / 4 ≤ η s) := by
  let η : ℝ → ℝ := fun s => ((s - b) / (c - b)) ^ 2
  have hΔ : 0 < c - b := sub_pos.mpr hbc
  have hs : ContDiff ℝ 1 η := by dsimp [η]; fun_prop
  have hd s : deriv η s = 2 * ((s - b) / (c - b)) / (c - b) := by
    have h := (((hasDerivAt_id s).sub_const b).div_const (c - b)).pow 2
    simp only [Nat.reduceSub, pow_one, Nat.cast_ofNat, id_eq] at h
    change HasDerivAt η (2 * ((s - b) / (c - b)) * (1 / (c - b))) s at h
    rw [h.deriv]
    ring
  refine ⟨η, hs.contDiffOn.absolutelyContinuousOnInterval, ?_, ?_, ?_, ?_⟩
  · have he : deriv η = fun s => 2 * ((s - b) / (c - b)) / (c - b) := funext hd
    rw [he]
    fun_prop
  · simp [η]
  · simp [η, hΔ.ne']
  · intro s hs
    have hq : 0 ≤ (s - b) / (c - b) ∧ (s - b) / (c - b) ≤ 1 := by
      constructor
      · exact div_nonneg (sub_nonneg.mpr hs.1) hΔ.le
      · apply (div_le_one hΔ).mpr
        linarith [hs.2]
    refine ⟨sq_nonneg _, ?_, ?_, ?_, ?_⟩
    · dsimp [η]
      nlinarith
    · rw [hd]
      exact div_nonneg (mul_nonneg (by norm_num) hq.1) hΔ.le
    · rw [hd]
      exact div_le_div_of_nonneg_right (by linarith [hq.2]) hΔ.le
    · intro hm
      have hhalf : (1 / 2 : ℝ) ≤ (s - b) / (c - b) := by
        apply (le_div_iff₀ hΔ).mpr
        linarith
      dsimp [η]
      nlinarith [sq_nonneg ((s - b) / (c - b) - 1 / 2)]

/-- The physical parabolic radius condition absorbs the signed complex force
into an inverse-square spatial error. -/
theorem physical_force_radius_bound {ζ : ℂ} {κ t r : ℝ}
    (hκ : 0 ≤ κ) (hr : 0 < r)
    (hrad : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t)) :
    ‖ζ‖ ^ 2 ≤ κ ^ 2 / r ^ 2 := by
  have hden : 0 < 1 + ‖ζ‖ * Real.sqrt t := by positivity
  have hm := (le_div_iff₀ hden).mp hrad
  have hp : (‖ζ‖ * r) * (1 + ‖ζ‖ * Real.sqrt t) ≤
      κ * (1 + ‖ζ‖ * Real.sqrt t) := by
    calc
      _ = ‖ζ‖ * (r * (1 + ‖ζ‖ * Real.sqrt t)) := by ring
      _ ≤ ‖ζ‖ * (κ * Real.sqrt t) :=
        mul_le_mul_of_nonneg_left hm (norm_nonneg ζ)
      _ ≤ κ * (1 + ‖ζ‖ * Real.sqrt t) := by nlinarith
  have hprod : ‖ζ‖ * r ≤ κ := (mul_le_mul_iff_left₀ hden).mp hp
  have hs := mul_self_le_mul_self (mul_nonneg (norm_nonneg ζ) hr.le) hprod
  apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
  nlinarith

/-- Vanishing outside a Euclidean ball also controls the closed support,
so physical cutoff derivatives vanish outside that same closed ball. -/
theorem physical_cutoff_tsupport_subset {d : ℕ} {φ : Vec d → ℝ}
    {z : Vec d} {R : ℝ}
    (hz : ∀ x, R ≤ euclideanNorm (x - z) → φ x = 0) :
    tsupport φ ⊆ {x | euclideanNorm (x - z) ≤ R} := by
  apply closure_minimal
  · intro x hx
    change φ x ≠ 0 at hx
    by_contra hh
    exact hx (hz x (not_le.mp hh).le)
  · have hn : Continuous (fun x : Vec d => euclideanNorm (x - z)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact isClosed_le hn continuous_const

/-- Both cutoff errors are of inverse-square-radius size under the actual
force/radius condition, with no restriction on the sign of the force. -/
theorem physical_cutoff_force_error_bound {d : ℕ} {φ : Vec d → ℝ}
    {ζ : ℂ} {B κ t r : ℝ} (hκ : 0 ≤ κ) (hr : 0 < r)
    (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r)
    (hrad : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t)) (x : Vec d) :
    ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 ≤
      (κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2 := by
  have hφsq : φ x ^ 2 ≤ 1 := by nlinarith [hφ x]
  have hforce : ‖ζ‖ ^ 2 * φ x ^ 2 ≤ κ ^ 2 / r ^ 2 := by
    calc
      _ ≤ ‖ζ‖ ^ 2 * 1 := mul_le_mul_of_nonneg_left hφsq (sq_nonneg _)
      _ = ‖ζ‖ ^ 2 := mul_one _
      _ ≤ κ ^ 2 / r ^ 2 := physical_force_radius_bound hκ hr hrad
  have hd j : (coordinateDerivative j φ x) ^ 2 ≤ B ^ 2 / r ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (coordinateDerivative j φ x)) (hD j x)
    simpa only [← sq, sq_abs, div_pow] using h
  have hsum : (∑ j, (coordinateDerivative j φ x) ^ 2) ≤
      (d : ℝ) * (B ^ 2 / r ^ 2) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd j)
  rw [add_div, mul_div_assoc]
  exact add_le_add hforce hsum

/-- Closed physical Euclidean balls are compact on the inherited coordinate
carrier, even though its ambient norm is the coordinate supremum norm. -/
theorem isCompact_physical_euclidean_closedBall {d : ℕ} (z : Vec d) (R : ℝ) :
    IsCompact {x : Vec d | euclideanNorm (x - z) ≤ R} := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have he : {x : Vec d | euclideanNorm (x - z) ≤ R} =
      J ⁻¹' Metric.closedBall (J z) R := by
    ext x
    change euclideanNorm (x - z) ≤ R ↔ ‖J x - J z‖ ≤ R
    rw [← map_sub J]
    change euclideanNorm (x - z) ≤ R ↔ ‖WithLp.toLp 2 (x - z)‖ ≤ R
    rw [← TimeChange.euclideanNorm_eq_norm_toLp]
  rw [he]
  exact J.toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)

/-- A compactly supported space-time weight bounded by A is dominated by A
 times the unweighted outer-cylinder integral. All integral existence follows
from local product integrability and continuous weights. -/
theorem physical_spacetime_weight_integral_le {d : ℕ} {K : Set (Vec d)}
    (hK : IsCompact K) {b c A : ℝ} {F : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hFpos : ∀ p, 0 ≤ F p) {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    (hzero : ∀ x, x ∉ K → ψ x = 0) {η : ℝ → ℝ}
    (hη : ContinuousOn η (Icc b c))
    (hbound : ∀ s ∈ Icc b c, ∀ x ∈ K, η s * ψ x ≤ A) :
    (∫ s in Icc b c, η s * (∫ x, ψ x * F (x, s))) ≤
      A * (∫ s in Icc b c, ∫ x in K, F (x, s)) := by
  have hi := IntegrableOn.continuousOn_mul hη
    (integrable_time_integral_compact_spatial_weight hK hF hψ hzero) isCompact_Icc
  have ho := hF.integral_prod_right
  have hm := integral_mono_ae hi (ho.const_mul A) (by
    filter_upwards [hF.prod_left_ae, ae_restrict_mem measurableSet_Icc] with s hs hsm
    have hw : Integrable (fun x => ψ x * F (x, s)) (volume.restrict K) :=
      IntegrableOn.continuousOn_mul hψ.continuousOn hs hK
    have he : (∫ x, ψ x * F (x, s)) = ∫ x in K, ψ x * F (x, s) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzero x hx, zero_mul])).symm
    rw [he, ← integral_const_mul, ← integral_const_mul]
    apply integral_mono_ae (hw.const_mul (η s)) (hs.const_mul A)
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hbound s hsm x hx) (hFpos (x, s)))
  simpa only [integral_const_mul] using hm

/-- The cutoff gradient controls the inner cylinder on the upper half of the
interval. The comparison uses the same physical integrand and product measure. -/
theorem physical_inner_cylinder_integral_le {d : ℕ} {K S : Set (Vec d)}
    (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {b c : ℝ} (hbc : b ≤ c) {F : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hFpos : ∀ p, 0 ≤ F p) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hzero : ∀ x, x ∉ K → φ x = 0) (hone : ∀ x ∈ S, φ x = 1)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hηlower : ∀ s ∈ Icc ((b + c) / 2) c, 1 / 4 ≤ η s) :
    (∫ s in Icc ((b + c) / 2) c, ∫ x in S, F (x, s)) ≤
      4 * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * F (x, s))) := by
  have hJI : Icc ((b + c) / 2) c ⊆ Icc b c := by
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  have hw := IntegrableOn.continuousOn_mul hη
    (integrable_time_integral_compact_spatial_weight hK hF (hφ.pow 2)
      (fun x hx => by simp only [Pi.pow_apply, hzero x hx, zero_pow (by decide : 2 ≠ 0)])) isCompact_Icc
  have hinner := hF.mono_measure
    (Measure.prod_mono (Measure.restrict_mono hSK le_rfl) le_rfl)
  have hiJ := hinner.integral_prod_right.mono_measure (Measure.restrict_mono hJI le_rfl)
  have hwJ := Integrable.mono_measure hw (Measure.restrict_mono hJI le_rfl)
  have hcmp : (∫ s in Icc ((b + c) / 2) c, ∫ x in S, F (x, s)) ≤
      4 * (∫ s in Icc ((b + c) / 2) c, η s * (∫ x, φ x ^ 2 * F (x, s))) := by
    have hm := integral_mono_ae hiJ (hwJ.const_mul 4) (by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hF.prod_left_ae,
        ae_restrict_mem measurableSet_Icc] with s hs hsm
      have hi : IntegrableOn (fun x => φ x ^ 2 * F (x, s)) K volume :=
        IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn hs hK
      have he : (∫ x in S, F (x, s)) = ∫ x in S, φ x ^ 2 * F (x, s) := by
        apply setIntegral_congr_fun hS
        intro x hx
        change F (x, s) = φ x ^ 2 * F (x, s)
        rw [hone x hx]
        simp
      have hsp := setIntegral_mono_set hi
        (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))
        (Eventually.of_forall (fun x hx => hSK hx))
      have hz : (∫ x in K, φ x ^ 2 * F (x, s)) = ∫ x, φ x ^ 2 * F (x, s) :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx => by rw [hzero x hx]; simp)
      rw [← he, hz] at hsp
      have hp : 0 ≤ ∫ x, φ x ^ 2 * F (x, s) :=
        integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s)))
      simp only [Pi.pow_apply]
      nlinarith [mul_le_mul_of_nonneg_right (hηlower s hsm) hp])
    simpa only [Pi.pow_apply, integral_const_mul] using hm
  apply hcmp.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hw _ (Eventually.of_forall (fun s hs => hJI hs))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact mul_nonneg (hηpos s hs)
    (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))

/-- The deterministic cylinder Caccioppoli step: cutoff boundary energy,
local spacetime L2 and the actual radius condition control the inner gradient. -/
theorem physical_cylinder_caccioppoli_of_cutoff_energy {d : ℕ}
    {b c r κ t B L C : ℝ} (hbc : b < c) (hr : 0 < r) (hκ : 0 ≤ κ)
    (hL : 0 < L) (hC : 0 ≤ C) {ζ : ℂ} {z : Vec d}
    (hrad : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t))
    {W : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ} {U : Vec d → ℂ}
    (hW : MemLp W 2 ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
      (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2
      ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
        (volume.restrict (Icc b c))))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x, euclideanNorm (x - z) ≤ r → φ x = 1)
    (hzero : ∀ x, 2 * r ≤ euclideanNorm (x - z) → φ x = 0)
    (hφD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηd : ContinuousOn (deriv η) (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b))
    (hηlower : ∀ s ∈ Icc ((b + c) / 2) c, 1 / 4 ≤ η s)
    (henergy : (L⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      -(∫ x, φ x ^ 2 * ‖U x‖ ^ 2) / 2 +
        (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (x, s)‖ ^ 2)) / 2 +
        C * (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
            ‖W (x, s)‖ ^ 2))) :
    (∫ s in Icc ((b + c) / 2) c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
      ∑ j, ‖D j (x, s)‖ ^ 2) ≤
      16 * L * ((c - b)⁻¹ + C * ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
          ‖W (x, s)‖ ^ 2) := by
  let K := {x : Vec d | euclideanNorm (x - z) ≤ 2 * r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (2 * r)
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K := physical_cutoff_tsupport_subset hzero
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have ht := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hz x hx, zero_pow (by decide : 2 ≠ 0)])
    hηd (A := 2 / (c - b)) (by
      intro s hs x hx
      have hsq : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
      simpa only [Pi.pow_apply, mul_one] using
        (mul_le_mul_of_nonneg_left hsq (hηrange s hs).2.2.1).trans
          (by simpa only [mul_one] using (hηrange s hs).2.2.2))
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have he := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx]) hη
    (A := (κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) (by
      intro s hs x hx
      have hp : 0 ≤ ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      exact (mul_le_mul_of_nonneg_right (hηrange s hs).2.1 hp).trans
        (by simpa only [one_mul] using
          physical_cutoff_force_error_bound hκ hr hφrange hφD hrad x))
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
  have hinner := physical_inner_cylinder_integral_le hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => by
      change euclideanNorm (x - z) ≤ r at hx
      change euclideanNorm (x - z) ≤ 2 * r
      linarith)
    hbc.le hiD (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg ‖D j p‖))
    hφ.1.continuous hz (fun x hx => hone x hx) hη
    (fun s hs => (hηrange s hs).1) hηlower
  have hp : 0 ≤ ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hupper : (L⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      ((c - b)⁻¹ + C * ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2) := by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at ht he
    simp only [div_eq_mul_inv] at ht
    have hce := mul_le_mul_of_nonneg_left he hC
    nlinarith only [henergy, hp, ht, hce]
  have hm := mul_le_mul_of_nonneg_left hupper (show 0 ≤ 4 * L by positivity)
  have hinv : (4 * L) * (L⁻¹ / 4) = 1 := by field_simp [hL.ne']
  rw [← mul_assoc, hinv, one_mul] at hm
  calc
    _ ≤ 4 * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) := hinner
    _ ≤ 4 * ((4 * L) * (((c - b)⁻¹ + C * ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2))) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by dsimp only [K]; ring

/-- Physical cylinder Caccioppoli for the actual corrected semigroup orbit.
The joint gradient is the actual horizontal gradient, and the SAME joint
primitive and restarted derivative retain their generator/derivative graph. -/
theorem complexForced_correctedOrbit_ae_physical_cylinderCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b < c → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc ((b + c) / 2) c,
            ∫ x in {x | euclideanNorm (x - z) ≤ r},
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          16 * L * ((c - b)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b c hb hbc z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc b c) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hηlower s (hs : s ∈ Icc ((b + c) / 2) c) : 1 / 4 ≤ η s :=
    (hηbounds s ⟨by linarith [hs.1], hs.2⟩).2.2.2.2 hs.1
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit (centeredComplexLp Q f) s) j‖ ^ 2)
        (Icc b c) volume :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy b c hb hbc.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_cylinder_caccioppoli_of_cutoff_energy (U := fun x => (w c) (translate x ω))
    hbc hr hκ hL hC hrad
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange hηlower
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Parabolic physical Caccioppoli, with the inverse-square-radius constant
and literal Euclidean cylinders. This retains the actual joint gradient and
temporal primitive rather than replacing them by independent witnesses. -/
theorem complexForced_correctedOrbit_ae_physical_parabolicCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ z : Vec d, ∀ r κ : ℝ, 0 < r → 0 ≤ κ → a < t - 2 * r ^ 2 →
        r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc (t - r ^ 2) t, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          16 * L * ((1 / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2) *
            (∫ s in Icc (t - 2 * r ^ 2) t,
              ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, hcyl⟩ :=
    complexForced_correctedOrbit_ae_physical_cylinderCaccioppoli hP f ht ha
  refine ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  intro z r κ hr hκ htime hrad
  have hbc : t - 2 * r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  filter_upwards [hcyl (t - 2 * r ^ 2) t htime hbc z r κ hr hκ hrad] with ω hω
  have hhalf : ((t - 2 * r ^ 2) + t) / 2 = t - r ^ 2 := by ring
  have hΔ : t - (t - 2 * r ^ 2) = 2 * r ^ 2 := by ring
  rw [hhalf, hΔ] at hω
  have he : (2 * r ^ 2)⁻¹ +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) =
      (1 / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2 := by
    field_simp
  rw [he] at hω
  exact hω

/-- Keeping the terminal boundary energy gives a physical L2 time-slice
bound. This controls the value of the solution at a fixed terminal time. -/
theorem physical_timeSliceL2_of_cutoff_energy {d : ℕ}
    {b c r κ t B L C : ℝ} (_hbc : b < c) (hr : 0 < r) (hκ : 0 ≤ κ)
    (hL : 0 < L) (hC : 0 ≤ C) {ζ : ℂ} {z : Vec d}
    (hrad : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t))
    {W : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ} {U : Vec d → ℂ}
    (hW : MemLp W 2 ((volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}).prod
      (volume.restrict (Icc b c))))
    (hU : MemLp U 2 (volume.restrict {x | euclideanNorm (x - z) ≤ 2 * r}))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x, euclideanNorm (x - z) ≤ r → φ x = 1)
    (hzero : ∀ x, 2 * r ≤ euclideanNorm (x - z) → φ x = 0)
    (hφD : ∀ j x, |coordinateDerivative j φ x| ≤ B / r)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηd : ContinuousOn (deriv η) (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b))
    (henergy : (L⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      -(∫ x, φ x ^ 2 * ‖U x‖ ^ 2) / 2 +
        (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (x, s)‖ ^ 2)) / 2 +
        C * (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
            ‖W (x, s)‖ ^ 2))) :
    (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) ≤
      2 * ((c - b)⁻¹ + C * ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
        (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
          ‖W (x, s)‖ ^ 2) := by
  let K := {x : Vec d | euclideanNorm (x - z) ≤ 2 * r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (2 * r)
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K := physical_cutoff_tsupport_subset hzero
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs]
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have ht := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hz x hx, zero_pow (by decide : 2 ≠ 0)])
    hηd (A := 2 / (c - b)) (by
      intro s hs x hx
      have hsq : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
      simpa only [Pi.pow_apply, mul_one] using
        (mul_le_mul_of_nonneg_left hsq (hηrange s hs).2.2.1).trans
          (by simpa only [mul_one] using (hηrange s hs).2.2.2))
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have he := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hz x hx, hdz, hx]) hη
    (A := (κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) (by
      intro s hs x hx
      have hp : 0 ≤ ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      exact (mul_le_mul_of_nonneg_right (hηrange s hs).2.1 hp).trans
        (by simpa only [one_mul] using
          physical_cutoff_force_error_bound hκ hr hφrange hφD hrad x))
  have hiU := (memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mp hU
  have hiφ : IntegrableOn (fun x => φ x ^ 2 * ‖U x‖ ^ 2) K volume :=
    IntegrableOn.continuousOn_mul (hφ.1.continuous.pow 2).continuousOn hiU hK
  have hinner : (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) ≤
      ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 := by
    have heq : (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖U x‖ ^ 2) =
        ∫ x in {x | euclideanNorm (x - z) ≤ r}, φ x ^ 2 * ‖U x‖ ^ 2 := by
      apply setIntegral_congr_fun (isCompact_physical_euclidean_closedBall z r).measurableSet
      intro x hx
      change ‖U x‖ ^ 2 = φ x ^ 2 * ‖U x‖ ^ 2
      rw [hone x hx]
      simp
    have hm := setIntegral_mono_set hiφ
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg ‖U x‖)))
      (Eventually.of_forall (fun x (hx : euclideanNorm (x - z) ≤ r) =>
        show x ∈ K from le_trans hx (by linarith)))
    have hzint : (∫ x in K, φ x ^ 2 * ‖U x‖ ^ 2) =
        ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hz x hx]; simp)
    change (∫ x in {x | euclideanNorm (x - z) ≤ r}, φ x ^ 2 * ‖U x‖ ^ 2) ≤
      (∫ x in K, φ x ^ 2 * ‖U x‖ ^ 2) at hm
    rw [← heq, hzint] at hm
    exact hm
  have hp : 0 ≤ (L⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) := by
    apply mul_nonneg (by positivity)
    apply setIntegral_nonneg measurableSet_Icc
    intro s hs
    exact mul_nonneg (hηrange s hs).1 (integral_nonneg (fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg _))))
  simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at ht he
  simp only [div_eq_mul_inv] at ht
  have hce := mul_le_mul_of_nonneg_left he hC
  dsimp only [K] at ht hce
  nlinarith only [henergy, hp, ht, hce, hinner]

/-- Fixed-time physical L2 trace of the actual corrected orbit, bounded by
its outer-cylinder L2 mass. The endpoint uses its actual Lp representative. -/
theorem complexForced_correctedOrbit_ae_physical_timeSliceL2
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b < c → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(w c) (translate x ω)‖ ^ 2) ≤
          2 * ((c - b)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b c hb hbc z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc b c) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalU := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (w c)
  filter_upwards [henergy b c hb hbc.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, hlocalU]
    with ω hω hlW hlU
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_timeSliceL2_of_cutoff_energy (D := fun j p => D j (p.2, translate p.1 ω))
    hbc hr hκ hL hC hrad
    (hlW _ hK) (hlU _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- The physical terminal-time L2 trace with parabolic scaling and the
actual corrected orbit at t. -/
theorem complexForced_correctedOrbit_ae_physical_parabolicTimeSliceL2
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ z : Vec d, ∀ r κ : ℝ, 0 < r → 0 ≤ κ → a < t - 2 * r ^ 2 →
        r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) → ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(w t) (translate x ω)‖ ^ 2) ≤
          2 * ((1 / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2) *
            (∫ s in Icc (t - 2 * r ^ 2) t,
              ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, hcyl⟩ :=
    complexForced_correctedOrbit_ae_physical_timeSliceL2 hP f ht ha
  refine ⟨B, hB, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  intro z r κ hr hκ htime hrad
  have hbc : t - 2 * r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  filter_upwards [hcyl (t - 2 * r ^ 2) t htime hbc z r κ hr hκ hrad] with ω hω
  have hΔ : t - (t - 2 * r ^ 2) = 2 * r ^ 2 := by ring
  rw [hΔ] at hω
  have he : (2 * r ^ 2)⁻¹ +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) =
      (1 / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2 := by
    field_simp
  rw [he] at hω
  exact hω

/-- After a second positive restart, a homogeneous semigroup orbit has its
actual derivative and generator output represented by one further orbit. -/
theorem IsComplexEnvironmentSemigroup.restarted_derivative_generator
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (g : Lp ℂ 2 (reducedLaw Q)) {a b : ℝ} (hab : a < b) :
    ∃ h : Lp ℂ 2 (reducedLaw Q),
      IsComplexGeneratorPair Q i ζ (P (b - a).toNNReal g) h ∧
      ∀ s : ℝ, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g)
          (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g)
          (P (s - b).toNNReal h) := by
  obtain ⟨h, hh⟩ := Blueprint.centered_source_positive_generator_domain hP g (sub_pos.mpr hab)
  refine ⟨h, hh, ?_⟩
  intro s hs
  have hsb : 0 < s - b := sub_pos.mpr hs
  have he (r : ℝ) (hr : b ≤ r) :
      P (r - b).toNNReal (P (b - a).toNNReal g) = P (r - a).toNNReal g := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1]
    apply congrArg (fun v : ℝ≥0 => P v g)
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal (r - b) (sub_nonneg.mpr hr),
      Real.coe_toNNReal (b - a) (sub_nonneg.mpr hab.le),
      Real.coe_toNNReal (r - a) (sub_nonneg.mpr (hab.le.trans hr))]
    ring
  have hd := Blueprint.centeredEquations_forward_hasDerivAt hP hh (s - b).toNNReal
    (by rwa [Real.coe_toNNReal (s - b) hsb.le])
  rw [Real.coe_toNNReal (s - b) hsb.le] at hd
  have hder := hd.scomp s ((hasDerivAt_id s).sub_const b)
  simp only [id_eq, one_smul] at hder
  refine ⟨?_, ?_⟩
  · apply hder.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with r hr
    exact (he r hr.le).symm
  · simpa only [he s hs.le] using hP.map_generator hh (s - b).toNNReal

/-- The actual time derivative of the corrected orbit solves the same
homogeneous generator equation after a second positive restart. Its joint
representative is retained from the first derivative construction. -/
theorem complexForced_correctedOrbit_derivative_generator_graph
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V : ℝ × FieldPair d → ℂ,
      Measurable V ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  intro w
  obtain ⟨g, V, _, hV, heV, hw, hlocal⟩ :=
    complexForced_correctedOrbit_derivative_ae_spacetime_memLp hP f ht ha
  obtain ⟨h, _, hder⟩ := hP.restarted_derivative_generator g hab
  refine ⟨g, h, V, hV, heV, hw, ?_, hlocal⟩
  intro s hs
  exact ⟨(hder s hs).1, (hder s hs).2,
    hP.gradientOrbit_spec g (sub_pos.mpr (hab.trans hs))⟩

/-- Physical cutoff coercivity for the actual time derivative of the
corrected orbit. At each positive time after the second restart the event
precedes all spatial tests; the source is its actual second derivative. -/
theorem complexForced_correctedOrbit_derivative_ae_physical_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V : ℝ × FieldPair d → ℂ,
      Measurable V ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ s : ℝ, b < s → ∀ᵐ ω ∂reducedLaw Q,
        ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
          (L⁻¹ / 4) * (∫ x, φ x ^ 2 *
            (∑ j, ‖(hP.gradientOrbit g (s - a)) j (translate x ω)‖ ^ 2)) ≤
            (∫ x, (φ x : ℂ) ^ 2 * star ((P (s - a).toNNReal g) (translate x ω)) *
              (-((P (s - b).toNNReal h) (translate x ω)))).re +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                (∑ j, (coordinateDerivative j φ x) ^ 2)) *
                  ‖(P (s - a).toNNReal g) (translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨g, h, V, hV, heV, hw, hder, hlocal⟩ :=
    complexForced_correctedOrbit_derivative_generator_graph hP f ht ha hab
  refine ⟨g, h, V, hV, heV, hw, hder, hlocal, ?_⟩
  intro s hs
  exact (hder s hs).2.1.ae_physical_cutoff_energy (hder s hs).2.2

/-- The actual first and second time derivatives admit compatible jointly
measurable physical representatives. Their local L2 bounds supply the
energy product, and the actual derivative orbit satisfies the physical
scalar energy identity between any two times after the second restart. -/
theorem complexForced_correctedOrbit_derivative_ae_temporalEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c ≤ e →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K,
            let v := fun s => (P (c - a).toNNReal g) (translate x ω) +
              ∫ r in c..s, Z (r, translate x ω)
            v e = (P (e - a).toNNReal g) (translate x ω) ∧
            (∫ s in c..e, 2 * (star (v s) * Z (s, translate x ω)).re) =
              ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2 -
                ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2 ∧
            AbsolutelyContinuousOnInterval (fun s => ‖v s‖ ^ 2) c e ∧
            (∀ᵐ s, s ∈ uIcc c e →
              deriv (fun r => ‖v r‖ ^ 2) s =
                2 * (star (v s) * Z (s, translate x ω)).re) ∧
            ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η c e →
              (∫ s in c..e, η s * (2 * (star (v s) * Z (s, translate x ω)).re)) =
                η e * ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2 -
                  η c * ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2 -
                  ∫ s in c..e, deriv η s * ‖v s‖ ^ 2 := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, hV, heV, hw, hd, hlocalV⟩ :=
    complexForced_correctedOrbit_derivative_generator_graph hP f ht ha hab
  obtain ⟨Z₀, hZ₀, heZ₀, _⟩ := hP.exists_joint_spatial_representative h
  let Z : ℝ × FieldPair d → ℂ := fun p => Z₀ (p.1 - b, p.2)
  have hZ : Measurable Z := hZ₀.comp ((measurable_fst.sub_const b).prodMk measurable_snd)
  have heZ (s : ℝ) : (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h :=
    heZ₀ (s - b)
  have hcont : Continuous (fun s : ℝ => P (s - b).toNNReal h) :=
    (hP.2.2.1 h).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hlocalZ := ae_spacetime_memLp_of_continuous_joint_l2 (reducedLaw Q)
    (reducedLaw_stationary Q) hcont hZ heZ
  refine ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, ?_, ?_⟩
  · filter_upwards [hlocalV, hlocalZ] with ω hωV hωZ
    intro n K hK
    exact ⟨hωV n K hK, hωZ n K hK,
      (hωV n K hK).star.integrable_mul (hωZ n K hK)⟩
  · intro c e hc hce
    have hi : IntegrableOn (fun s : ℝ => P (s - b).toNNReal h) (Icc c e) :=
      hcont.continuousOn.integrableOn_compact isCompact_Icc
    have hFTC : (∫ s in Icc c e, P (s - b).toNNReal h) =
        P (e - a).toNNReal g - P (c - a).toNNReal g := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hce]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => (hd s (hc.trans_le ((uIcc_of_le hce ▸ hs).1))).1)
        (hcont.intervalIntegrable c e)
    have hcZ := ae_spatial_coeFn_integral_joint_l2_representative
      (reducedLaw Q) (reducedLaw_stationary Q) hi hZ heZ
    rw [hFTC] at hcZ
    have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable (P (e - a).toNNReal g - P (c - a).toNNReal g)).measurable
      ((Lp.stronglyMeasurable (P (e - a).toNNReal g)).measurable.sub
        (Lp.stronglyMeasurable (P (c - a).toNNReal g)).measurable)
      (Lp.coeFn_sub (P (e - a).toNNReal g) (P (c - a).toNNReal g))
    have hl := ae_locally_integrable_joint_spatial_translate
      (reducedLaw Q) (reducedLaw_stationary Q)
      (integrable_joint_l2_representative hi hZ heZ)
    filter_upwards [hcZ, hs, hl] with ω hcZ hs hl
    intro K hK
    filter_upwards [ae_restrict_of_ae hcZ, ae_restrict_of_ae hs,
      (hl K hK).prod_right_ae] with x hcZ hs hx
    have hu : IntervalIntegrable (fun s => Z (s, translate x ω)) volume c e := by
      have hx' : IntegrableOn (fun s => Z (s, translate x ω)) (uIcc c e) := by
        simpa only [uIcc_of_le hce] using! hx
      exact hx'.intervalIntegrable
    have he : (P (c - a).toNNReal g) (translate x ω) +
        (∫ s in c..e, Z (s, translate x ω)) =
          (P (e - a).toNNReal g) (translate x ω) := by
      rw [intervalIntegral.integral_of_le hce, ← integral_Icc_eq_integral_Ioc, ← hcZ, hs]
      exact add_sub_cancel _ _
    obtain ⟨hAC, hAE⟩ :=
      complexPrimitive_energy_regular hu ((P (c - a).toNNReal g) (translate x ω))
    refine ⟨he, ?_, hAC, hAE, ?_⟩
    · simpa only [he] using
        complexPrimitive_energy hu ((P (c - a).toNNReal g) (translate x ω))
    · intro η hη
      simpa only [he] using
        complexPrimitive_weighted_energy hu ((P (c - a).toNNReal g) (translate x ω)) hη

/-- A continuously differentiable L2 path and any of its joint measurable
representatives agree physically with the primitive of the chosen joint
representative of its derivative. The event holds in full spacetime. -/
theorem ae_physical_primitive_of_joint_l2_derivative
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u v : ℝ → Lp ℂ 2 Q}
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[Q] v s)
    (hv : Continuous v) {a b c : ℝ} (hab : a < b)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s) :
    ∀ᵐ ω ∂Q,
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod (volume.restrict (Icc b c)),
        U (p.2, translate p.1 ω) = (u b) (translate p.1 ω) +
          ∫ r in Icc b p.2, V (r, translate p.1 ω) := by
  let F : ℝ × FieldPair d → ℂ := fun p => (u b) p.2 + ∫ r in Icc b p.1, V (r, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable (u b)).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hV b)
  have he (s : ℝ) (hs : s ∈ Icc b c) :
      (fun ω => U (s, ω)) =ᵐ[Q] fun ω => F (s, ω) := by
    have hint : IntegrableOn v (Icc b s) :=
      hv.continuousOn.integrableOn_compact isCompact_Icc
    have hi := coeFn_integral_joint_l2_representative hint hV heV
    have hFTC : (∫ r in Icc b s, v r) = u s - u b := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.1]
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun r hr => hd r (hab.trans_le ((uIcc_of_le hs.1 ▸ hr).1)))
        (hv.intervalIntegrable b s)
    rw [hFTC] at hi
    filter_upwards [heU s, hi, Lp.coeFn_sub (u s) (u b)] with ω hω hi hsub
    change U (s, ω) = (u b) ω + ∫ r in Icc b s, V (r, ω)
    rw [hω, ← hi, hsub]
    exact (add_sub_cancel _ _).symm
  have hmU := measurable_joint_spatial_translate hU
  have hmF := measurable_joint_spatial_translate hF
  have hephys : ∀ᵐ s ∂volume.restrict (Icc b c),
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q,
        U (s, translate p.1 p.2) = F (s, translate p.1 p.2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (hmU.comp (measurable_const.prodMk measurable_id))
      (hmF.comp (measurable_const.prodMk measurable_id)))).mpr
    exact ae_of_all _ fun x =>
      (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae (he s hs)
  have heprod := (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hmU hmF)).mpr hephys
  have heassoc := (measurePreserving_prodAssoc
    (volume.restrict (Icc b c)) (volume : Measure (Vec d)) Q).quasiMeasurePreserving.ae heprod
  have henv := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heassoc)
  filter_upwards [henv] with ω hω
  exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae hω

/-- The actual joint first derivative is the physical primitive of the
same joint second derivative, and therefore satisfies the weighted energy
identity with its own spacetime values and actual endpoint traces. -/
theorem complexForced_correctedOrbit_derivative_ae_jointWeightedEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c ≤ e →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ᵐ x ∂volume.restrict K,
            (∀ᵐ s ∂volume.restrict (Icc c e),
              V (s, translate x ω) = (P (c - a).toNNReal g) (translate x ω) +
                ∫ r in c..s, Z (r, translate x ω)) ∧
            ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η c e →
              (∫ s in c..e, η s *
                (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re)) =
                η e * ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2 -
                  η c * ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2 -
                  ∫ s in c..e, deriv η s * ‖V (s, translate x ω)‖ ^ 2 := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, hlocal, htime⟩ :=
    complexForced_correctedOrbit_derivative_ae_temporalEnergy hP f ht ha hab
  refine ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, hlocal, ?_⟩
  intro c e hc hce
  have hcont : Continuous (fun s : ℝ => P (s - b).toNNReal h) :=
    (hP.2.2.1 h).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hprim := ae_physical_primitive_of_joint_l2_derivative (reducedLaw Q)
    (reducedLaw_stationary Q) hV hZ heV heZ hcont hc (fun s hs => (hd s hs).1)
      (c := e)
  filter_upwards [hprim, htime c e hc hce] with ω hprim htime
  intro K hK
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hprim), htime K hK]
    with x hx htime
  have heq : ∀ᵐ s ∂volume.restrict (Icc c e),
      V (s, translate x ω) = (P (c - a).toNNReal g) (translate x ω) +
        ∫ r in c..s, Z (r, translate x ω) := by
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  refine ⟨heq, ?_⟩
  intro η hη
  have hleft :
      (∫ s in c..e, η s *
        (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re)) =
      ∫ s in c..e, η s * (2 * (star ((P (c - a).toNNReal g) (translate x ω) +
        ∫ r in c..s, Z (r, translate x ω)) * Z (s, translate x ω)).re) := by
    rw [intervalIntegral.integral_of_le hce, intervalIntegral.integral_of_le hce,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  have hright : (∫ s in c..e, deriv η s * ‖V (s, translate x ω)‖ ^ 2) =
      ∫ s in c..e, deriv η s * ‖(P (c - a).toNNReal g) (translate x ω) +
        ∫ r in c..s, Z (r, translate x ω)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hce, intervalIntegral.integral_of_le hce,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  rw [hleft, hright]
  exact htime.2.2.2.2 η hη

/-- Spatially integrated temporal energy for the actual derivative orbit.
The same V,Z and actual endpoint traces occur in both orders of integration;
local L2 supplies every integrability claim internally. -/
theorem complexForced_correctedOrbit_derivative_ae_spatialWeightedEnergy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c ≤ e →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
          ∀ φ : Vec d → ℝ, Continuous φ → ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η c e → ContinuousOn (deriv η) (Icc c e) →
            (∫ s in Icc c e, η s * (∫ x in K, φ x ^ 2 *
              (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re))) =
              η e * (∫ x in K, φ x ^ 2 * ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2) -
              η c * (∫ x in K, φ x ^ 2 * ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2) -
              ∫ s in Icc c e, deriv η s *
                (∫ x in K, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) := by
  intro w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, hlocal, htemporal⟩ :=
    complexForced_correctedOrbit_derivative_ae_jointWeightedEnergy hP f ht ha hab
  refine ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hcontV : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hcontZ : Continuous (fun s : ℝ => P (s - b).toNNReal h) :=
    (hP.2.2.1 h).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  intro c e hc hce
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c e) volume :=
    (hcontV.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖P (s - b).toNNReal h‖ ^ 2) (Icc c e) volume :=
    (hcontZ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      hwI hV heV)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hZ
    (integrable_sq_joint_l2_representative
      hvI hZ heZ)
  filter_upwards [htemporal c e hc hce, hlocalW, hlocalV,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) (u c),
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) (u e)]
    with ω htime hlocW hlocV hwb hwc
  intro K hK φ hφ η hη hη'
  let X : Vec d × ℝ → ℂ := fun p => V (p.2, translate p.1 ω)
  let Y : Vec d × ℝ → ℂ := fun p => Z (p.2, translate p.1 ω)
  let A : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * η p.2 * (2 * (star (X p) * Y p).re)
  let B : Vec d × ℝ → ℝ := fun p => φ p.1 ^ 2 * deriv η p.2 * ‖X p‖ ^ 2
  have hηc : ContinuousOn η (Icc c e) := by
    simpa only [uIcc_of_le hce] using hη.continuousOn
  have hweight (ψ : ℝ → ℝ) (hψ : ContinuousOn ψ (Icc c e)) :
      ContinuousOn (fun p : Vec d × ℝ => φ p.1 ^ 2 * ψ p.2) (K ×ˢ Icc c e) :=
    ((hφ.pow 2).comp continuous_fst).continuousOn.mul
      (hψ.comp continuous_snd.continuousOn (fun p hp => hp.2))
  have hprod : Integrable (fun p => star (X p) * Y p)
      ((volume.restrict K).prod (volume.restrict (Icc c e))) :=
    (hlocW K hK).star.integrable_mul (hlocV K hK)
  have hA : Integrable A ((volume.restrict K).prod (volume.restrict (Icc c e))) :=
    integrable_spacetime_continuousOn_mul hK
      ((Complex.reCLM.integrable_comp hprod).const_mul 2) (hweight η hηc)
  have hB : Integrable B ((volume.restrict K).prod (volume.restrict (Icc c e))) :=
    integrable_spacetime_continuousOn_mul hK
      ((memLp_two_iff_integrable_sq_norm (hlocW K hK).aestronglyMeasurable).mp (hlocW K hK))
      (hweight (deriv η) hη')
  have hend (s : ℝ) (hs : ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => (u s) (translate x ω)) 2 (volume.restrict K)) :
      Integrable (fun x => φ x ^ 2 * ‖(u s) (translate x ω)‖ ^ 2) (volume.restrict K) :=
    IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn
      ((memLp_two_iff_integrable_sq_norm (hs K hK).aestronglyMeasurable).mp (hs K hK)) hK
  have heq : ∀ᵐ x ∂volume.restrict K,
      (∫ s in Icc c e, A (x, s)) =
        η e * (φ x ^ 2 * ‖(u e) (translate x ω)‖ ^ 2) -
        η c * (φ x ^ 2 * ‖(u c) (translate x ω)‖ ^ 2) - ∫ s in Icc c e, B (x, s) := by
    filter_upwards [htime K hK] with x hx
    have he := hx.2 η hη
    rw [intervalIntegral.integral_of_le hce, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hce, ← integral_Icc_eq_integral_Ioc] at he
    simp only [A, B, X, Y]
    simp_rw [mul_assoc (φ x ^ 2)]
    rw [integral_const_mul, integral_const_mul, he]
    ring
  calc
    _ = ∫ s in Icc c e, ∫ x in K, A (x, s) := by
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [A, X, Y]
      ring
    _ = ∫ x in K, ∫ s in Icc c e, A (x, s) := (integral_integral_swap hA).symm
    _ = η e * (∫ x in K, φ x ^ 2 * ‖(u e) (translate x ω)‖ ^ 2) -
        η c * (∫ x in K, φ x ^ 2 * ‖(u c) (translate x ω)‖ ^ 2) -
        ∫ x in K, ∫ s in Icc c e, B (x, s) := by
      have hsplit := integral_sub
        (((hend e hwc).const_mul (η e)).sub ((hend c hwb).const_mul (η c)))
        hB.integral_prod_left
      have hends := integral_sub ((hend e hwc).const_mul (η e))
        ((hend c hwb).const_mul (η c))
      simp only [Pi.sub_apply] at hsplit hends
      rw [integral_congr_ae heq, hsplit, hends, integral_const_mul, integral_const_mul]
    _ = _ := by
      rw [integral_integral_swap hB]
      congr 1
      apply integral_congr_ae
      filter_upwards with s
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [B, X]
      ring

/-- The gradient of a restarted homogeneous semigroup orbit has a joint
representative locally L2 on every interval strictly after its restart. -/
theorem IsComplexEnvironmentSemigroup.exists_ae_spacetime_restarted_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (g : Lp ℂ 2 (reducedLaw Q)) (a : ℝ) :
    ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit g (s - a)) j) ∧
      ∀ c e : ℝ, a < c →
        ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K → ∀ j,
          MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
            ((volume.restrict K).prod (volume.restrict (Icc c e))) := by
  let := reducedLaw_probability Q
  obtain ⟨D₀, hD₀, heD₀⟩ := hP.exists_joint_gradient_representative g
  let D : Fin d → ℝ × FieldPair d → ℂ := fun j p => D₀ j (p.1 - a, p.2)
  have hD (j : Fin d) : Measurable (D j) :=
    (hD₀ j).comp ((measurable_fst.sub_const a).prodMk measurable_snd)
  have heD (j : Fin d) (s : ℝ) : (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (hP.gradientOrbit g (s - a)) j := heD₀ j (s - a)
  refine ⟨D, hD, heD, ?_⟩
  intro c e hc
  have hlocal (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc c e))) := by
    have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
      (hP.continuousOn_gradientOrbit g).comp
        (continuous_id.sub continuous_const).continuousOn (fun s hs => by
          change 0 < s - a
          exact sub_pos.mpr hs)
    have hcoord : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit g (s - a)) j‖ ^ 2)
        (Icc c e) volume :=
      ((hcoord.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le hc hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  exact fun K hK j => hω j K hK

/-- The differentiated physical equation, gradient integrability, and
spatially integrated temporal energy hold for the same joint V,Z,D. -/
theorem complexForced_correctedOrbit_derivative_ae_jointCutoffEnergy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c ≤ e → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ᵐ ω ∂reducedLaw Q,
          (∀ K : Set (Vec d), IsCompact K → ∀ j,
            MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
              ((volume.restrict K).prod (volume.restrict (Icc c e)))) ∧
          (∀ᵐ s ∂volume.restrict (Icc c e),
            (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
              (∫ x, (φ x : ℂ) ^ 2 * star (V (s, translate x ω)) * (-Z (s, translate x ω))).re +
              (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
                (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                  (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖V (s, translate x ω)‖ ^ 2)) ∧
          ∀ K : Set (Vec d), IsCompact K → ∀ η : ℝ → ℝ,
            AbsolutelyContinuousOnInterval η c e → ContinuousOn (deriv η) (Icc c e) →
            (∫ s in Icc c e, η s * (∫ x in K, φ x ^ 2 *
              (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re))) =
              η e * (∫ x in K, φ x ^ 2 * ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2) -
              η c * (∫ x in K, φ x ^ 2 * ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2) -
              ∫ s in Icc c e, deriv η s *
                (∫ x in K, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨g, h, V, Z, hV, hZ, heV, heZ, hw, hd, hlocal, htime⟩ :=
    complexForced_correctedOrbit_derivative_ae_spatialWeightedEnergy hP f ht ha hab
  obtain ⟨D, hD, heD, hlocalD⟩ := hP.exists_ae_spacetime_restarted_gradient g a
  refine ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  intro c e hc hce φ hφ
  have hcoer := ae_joint_physical_cutoff_energy (b := c) (c := e)
    (u := fun s => P (s - a).toNNReal g) (v := fun s => P (s - b).toNNReal h)
    (G := fun s j => (hP.gradientOrbit g (s - a)) j)
    (fun s hs => (hd s (hc.trans_le hs.1)).2.1)
    (fun s hs => (hd s (hc.trans_le hs.1)).2.2) hV hZ hD heV heZ heD hφ
  filter_upwards [hcoer, hlocalD c e (hab.trans hc), htime c e hc hce]
    with ω hcoer hlocalD htime
  exact ⟨hlocalD, hcoer,
    fun K hK η hη hη' => htime K hK φ hφ.1.continuous η hη hη'⟩

/-- Integrated physical cutoff coercivity for the actual time derivative,
with the actual derivative's temporal endpoint values. -/
theorem complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c ≤ e → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η c e →
          ContinuousOn (deriv η) (Icc c e) →
          (∀ s ∈ Icc c e, 0 ≤ η s) → ∀ᵐ ω ∂reducedLaw Q,
          (L⁻¹ / 4) * (∫ s in Icc c e, η s *
            (∫ x, φ x ^ 2 * (∑ j, ‖D j (s, translate x ω)‖ ^ 2))) ≤
            (η c * (∫ x, φ x ^ 2 * ‖(P (c - a).toNNReal g) (translate x ω)‖ ^ 2) -
              η e * (∫ x, φ x ^ 2 * ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2) +
              (∫ s in Icc c e, deriv η s *
                (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2))) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (∫ s in Icc c e, η s *
                (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
                  (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖V (s, translate x ω)‖ ^ 2)) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, hcut⟩ :=
    complexForced_correctedOrbit_derivative_ae_jointCutoffEnergy hP f ht ha hab
  refine ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hcontV : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hcontZ : Continuous (fun s : ℝ => P (s - b).toNNReal h) :=
    (hP.2.2.1 h).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  intro c e hc hce φ hφ η hη hη' hηpos
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c e) volume :=
    (hcontV.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvI : IntegrableOn (fun s => ‖P (s - b).toNNReal h‖ ^ 2) (Icc c e) volume :=
    (hcontZ.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hZ
    (integrable_sq_joint_l2_representative hvI hZ heZ)
  filter_upwards [hcut c e hc hce φ hφ, hlocalW, hlocalV] with ω hc hlW hlV
  have hηc : ContinuousOn η (Icc c e) := by
    simpa only [uIcc_of_le hce] using hη.continuousOn
  have hineq := physical_cutoff_energy_time_integral hφ (hlW _ hφ.2.1)
    (hlV _ hφ.2.1) (hc.1 _ hφ.2.1) hηc hηpos hc.2.1
  have hp := (hlW (tsupport φ) hφ.2.1).star.integrable_mul
    (hlV (tsupport φ) hφ.2.1)
  have hpφ : Integrable (fun p : Vec d × ℝ =>
      (φ p.1 : ℂ) ^ 2 * star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc c e))) := by
    have hi : Integrable (fun p : Vec d × ℝ =>
        (φ p.1 : ℂ) ^ 2 * (star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω)))
        ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc c e))) := by
      rw [Measure.prod_restrict] at hp ⊢
      exact IntegrableOn.continuousOn_mul
        (((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).comp
          continuous_fst).continuousOn hp (hφ.2.1.prod isCompact_Icc)
    simpa only [mul_assoc] using hi
  have hpair : (∫ s in Icc c e, η s *
      (∫ x, (φ x : ℂ) ^ 2 * star (V (s, translate x ω)) *
        (-Z (s, translate x ω))).re) =
      -(∫ s in Icc c e, η s * (∫ x, φ x ^ 2 *
        (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re))) / 2 := by
    calc
      _ = ∫ s in Icc c e, -(η s * (∫ x, φ x ^ 2 *
          (2 * (star (V (s, translate x ω)) * Z (s, translate x ω)).re))) / 2 := by
        apply integral_congr_ae
        filter_upwards [hpφ.prod_left_ae] with s hs
        rw [physical_cutoff_generator_pairing_eq hs]
        ring
      _ = _ := by rw [integral_div, integral_neg]
  have hres (F : Vec d → ℝ) :
      (∫ x in tsupport φ, φ x ^ 2 * F x) = ∫ x, φ x ^ 2 * F x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have htime := hc.2.2 (tsupport φ) hφ.2.1 η hη hη'
  simp_rw [hres] at htime
  rw [hpair] at hineq
  linarith

/-- Physical cylinder Caccioppoli for the actual time derivative of the
corrected orbit, under the same force/radius absorption condition. -/
theorem complexForced_correctedOrbit_derivative_ae_cylinderCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c < e → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc ((c + e) / 2) e,
            ∫ x in {x | euclideanNorm (x - z) ≤ r},
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          16 * L * ((e - c)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc c e, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  refine ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hcontV : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro c e hc hce z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hce
  have hηcont : ContinuousOn η (Icc c e) := by
    simpa only [uIcc_of_le hce.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc c e) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (e - c) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hηlower s (hs : s ∈ Icc ((c + e) / 2) e) : 1 / 4 ≤ η s :=
    (hηbounds s ⟨by linarith [hs.1], hs.2⟩).2.2.2.2 hs.1
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c e) volume :=
    (hcontV.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc c e))) := by
    have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
      (hP.continuousOn_gradientOrbit g).comp
        (continuous_id.sub continuous_const).continuousOn (fun s hs => by
          change 0 < s - a
          exact sub_pos.mpr hs)
    have hcoord : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit g (s - a)) j‖ ^ 2)
        (Icc c e) volume :=
      ((hcoord.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (hab.trans hc) hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy c e hc hce.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_cylinder_caccioppoli_of_cutoff_energy (U := fun x => (u e) (translate x ω))
    hce hr hκ hL hC hrad
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange hηlower
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Parabolic specialization of the physical cylinder estimate for the actual
time derivative. -/
theorem complexForced_correctedOrbit_derivative_ae_parabolicCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ z : Vec d, ∀ r κ : ℝ, 0 < r → 0 ≤ κ → b < t - 2 * r ^ 2 →
        r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc (t - r ^ 2) t, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          16 * L * ((1 / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2) *
            (∫ s in Icc (t - 2 * r ^ 2) t,
              ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, hcyl⟩ :=
    complexForced_correctedOrbit_derivative_ae_cylinderCaccioppoli hP f ht ha hab
  refine ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  intro z r κ hr hκ htime hrad
  have hbc : t - 2 * r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  filter_upwards [hcyl (t - 2 * r ^ 2) t htime hbc z r κ hr hκ hrad] with ω hω
  have hhalf : ((t - 2 * r ^ 2) + t) / 2 = t - r ^ 2 := by ring
  have hΔ : t - (t - 2 * r ^ 2) = 2 * r ^ 2 := by ring
  rw [hhalf, hΔ] at hω
  have he : (2 * r ^ 2)⁻¹ +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) =
      (1 / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2 := by
    field_simp
  rw [he] at hω
  exact hω

/-- The actual time derivative at a fixed terminal time is controlled by its
outer-cylinder physical L2 mass, with the original derivative graphs retained. -/
theorem complexForced_correctedOrbit_derivative_ae_timeSliceL2
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c < e → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
          2 * ((e - c)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc c e, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  refine ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hcontV : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro c e hc hce z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hce
  have hηcont : ContinuousOn η (Icc c e) := by
    simpa only [uIcc_of_le hce.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc c e) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (e - c) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c e) volume :=
    (hcontV.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalU := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (u e)
  filter_upwards [henergy c e hc hce.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, hlocalU]
    with ω hω hlW hlU
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_timeSliceL2_of_cutoff_energy (D := fun j p => D j (p.2, translate p.1 ω))
    hce hr hκ hL hC hrad
    (hlW _ hK) (hlU _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Parabolic fixed-time L2 bound for the actual time derivative. -/
theorem complexForced_correctedOrbit_derivative_ae_parabolicTimeSliceL2
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ z : Vec d, ∀ r κ : ℝ, 0 < r → 0 ≤ κ → b < t - 2 * r ^ 2 →
        r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) → ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
          2 * ((1 / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2) *
            (∫ s in Icc (t - 2 * r ^ 2) t,
              ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
                ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  obtain ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, hcyl⟩ :=
    complexForced_correctedOrbit_derivative_ae_timeSliceL2 hP f ht ha hab
  refine ⟨B, hB, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  intro z r κ hr hκ htime hrad
  have hbc : t - 2 * r ^ 2 < t := by nlinarith [sq_pos_of_pos hr]
  filter_upwards [hcyl (t - 2 * r ^ 2) t htime hbc z r κ hr hκ hrad] with ω hω
  have hΔ : t - (t - 2 * r ^ 2) = 2 * r ^ 2 := by ring
  rw [hΔ] at hω
  have he : (2 * r ^ 2)⁻¹ +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2) =
      (1 / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (κ ^ 2 + (d : ℝ) * B ^ 2)) / r ^ 2 := by
    field_simp
  rw [he] at hω
  exact hω

/-- Compact spatial cutoffs turn two locally square-integrable fields into
an integrable pairing on the whole physical space. -/
theorem integrable_physical_cutoff_pairing {d : ℕ} {F G : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K → MemLp F 2 (volume.restrict K))
    (hG : ∀ K : Set (Vec d), IsCompact K → MemLp G 2 (volume.restrict K))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) :
    Integrable (fun x => (φ x : ℂ) ^ 2 * F x * G x) volume := by
  have hp := (hF (tsupport φ) hφ.2.1).integrable_mul (hG (tsupport φ) hφ.2.1)
  have hi := IntegrableOn.continuousOn_mul
    ((Complex.continuous_ofReal.comp hφ.1.continuous).pow 2).continuousOn hp hφ.2.1
  have hj : IntegrableOn (fun x => (φ x : ℂ) ^ 2 * F x * G x) (tsupport φ) volume := by
    simpa only [Pi.pow_apply, Function.comp_apply, Pi.mul_apply, mul_assoc] using hi
  exact hj.integrable_of_forall_notMem_eq_zero (fun x hx => by
    simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul])

/-- Test the actual generator equation by the cutoff-squared conjugate of
its output. This is the mixed spatial identity needed to estimate the time
derivative using the original solution and the gradient of the derivative. -/
theorem IsComplexGeneratorPair.ae_physical_generator_output_test
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g H) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      (∫ x, (g (translate x ω) -
        ζ * (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) *
          ((φ x : ℂ) ^ 2 * star (g (translate x ω)))) =
      -(∫ x, ∑ j, ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
        ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
            star (g (translate x ω)))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun j ω => (1 / 2 : ℂ) * ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let q : FieldPair d → ℂ := fun ω => g ω - ζ * b ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) := measurable_const.mul
    (Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable)
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (hm j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hqm : Measurable q := (Lp.stronglyMeasurable g).measurable.sub (measurable_const.mul hbm)
  have hq : MemLp q 2 (reducedLaw Q) := (Lp.memLp g).sub (hb.const_mul ζ)
  have hF j : MemLp (F j) 2 (reducedLaw Q) := (memLp_complex_coefficient_flux Q G j).const_mul _
  have hw := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F q hFm hqm hF hq (by
      intro v V hV
      have he := hfg.horizontal_flux hG v V hV
      have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
        (Lp.memLp g).integrable_mul (Lp.memLp v)
      have hd : Integrable (fun ω => b ω * v ω) (reducedLaw Q) :=
        hb.integrable_mul (Lp.memLp v)
      have heq : (fun ω => (2 * g ω - 2 * ζ *
          (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω) =
          (fun ω => 2 * (g ω * v ω) - (2 * ζ) * (b ω * v ω)) := by
        funext ω
        dsimp only [b]
        ring
      rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
        integral_const_mul, integral_const_mul] at he
      have hqe : (fun ω => q ω * v ω) =
          (fun ω => g ω * v ω - ζ * (b ω * v ω)) := by
        funext ω
        dsimp only [q]
        ring
      rw [hqe, integral_sub hg (hd.const_mul ζ), integral_const_mul]
      simp only [F, mul_assoc, ← Finset.mul_sum, integral_const_mul]
      linear_combination (1 / 2 : ℂ) * he)
  filter_upwards [hH.ae_reduced_spatial Q, hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) hqm hq,
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j))]
    with ω hω hw hqω hFω
  have hreal := divergence_projection (fun K hK j => hFω j K hK) hqω hw Complex.reCLM
  have himag := divergence_projection (fun K hK j => hFω j K hK) hqω hw Complex.imCLM
  intro φ hφ
  have he := physicalWeakDivergence_cutoff_locallyH1 isOpen_univ
    (fun K hK _ => (hω.2.2 K hK).1)
    (fun K hK _ j => (hω.2.2 K hK).2 j)
    (fun K hK _ j => hFω j K hK) (fun K hK _ => hqω K hK)
    hω.1 hω.2.1 hreal himag hφ
  simpa only [F, q, b, translate_matrix, add_zero, neg_neg] using
    (congrArg Neg.neg he).symm

/-- The generator tested against its own output gives the literal physical
squared mass of that output, with the mixed gradient and drift terms explicit. -/
theorem IsComplexGeneratorPair.ae_physical_generator_output_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g H) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) =
        (ζ * (∫ x, (φ x : ℂ) ^ 2 * star (g (translate x ω)) *
          (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) -
        (∫ x, ∑ j, ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
          ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
            2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
              star (g (translate x ω))))).re := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    ((Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j i)).measurable).mul
        (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  filter_upwards [hfg.ae_physical_generator_output_test hG hH,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) hbm hb]
    with ω he hgω hbω
  intro φ hφ
  have hgg := integrable_physical_cutoff_pairing (fun K hK => (hgω K hK).star) hgω hφ
  have hgb := integrable_physical_cutoff_pairing (fun K hK => (hgω K hK).star) hbω hφ
  simp only [Pi.star_apply] at hgg hgb
  have hgb' : Integrable (fun x => (φ x : ℂ) ^ 2 * star (g (translate x ω)) *
      (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) volume := by
    simpa only [b, translate_matrix, add_zero] using hgb
  have hid := he φ hφ
  have halg : (fun x => (g (translate x ω) -
      ζ * (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) *
      ((φ x : ℂ) ^ 2 * star (g (translate x ω)))) =
      (fun x => (φ x : ℂ) ^ 2 * star (g (translate x ω)) * g (translate x ω) -
        ζ * ((φ x : ℂ) ^ 2 * star (g (translate x ω)) *
          (∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)))) := by
    funext x
    ring
  rw [halg, integral_sub hgg (hgb'.const_mul ζ), integral_const_mul] at hid
  have hmass : (∫ x, (φ x : ℂ) ^ 2 * star (g (translate x ω)) * g (translate x ω)) =
      ((∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [mul_assoc, RCLike.star_def, RCLike.conj_mul]
    push_cast
    rfl
  rw [hmass] at hid
  have heq := congrArg Complex.re hid
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.neg_re] at heq ⊢
  linarith


/-- A continuous compactly supported multiplier preserves local L2 pairings. -/
theorem integrable_physical_compact_pairing {d : ℕ} {F G ψ : Vec d → ℂ}
    {K : Set (Vec d)} (hK : IsCompact K)
    (hF : MemLp F 2 (volume.restrict K)) (hG : MemLp G 2 (volume.restrict K))
    (hψ : Continuous ψ) (hz : ∀ x, x ∉ K → ψ x = 0) :
    Integrable (fun x => ψ x * F x * G x) volume := by
  have hi := IntegrableOn.continuousOn_mul hψ.continuousOn (hF.integrable_mul hG) hK
  have hj : IntegrableOn (fun x => ψ x * F x * G x) K volume := by
    simpa only [Pi.mul_apply, mul_assoc] using hi
  exact hj.integrable_of_forall_notMem_eq_zero fun x hx => by rw [hz x hx]; simp only [zero_mul]

/-- Continuous compact weights integrate the squared norm of a local L2 field. -/
theorem integrable_physical_compact_sq_norm {d : ℕ} {F : Vec d → ℂ} {ψ : Vec d → ℝ}
    {K : Set (Vec d)} (hK : IsCompact K) (hF : MemLp F 2 (volume.restrict K))
    (hψ : Continuous ψ) (hz : ∀ x, x ∉ K → ψ x = 0) :
    Integrable (fun x => ψ x * ‖F x‖ ^ 2) volume := by
  have hi := IntegrableOn.continuousOn_mul hψ.continuousOn
    ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF) hK
  exact hi.integrable_of_forall_notMem_eq_zero fun x hx => by
    rw [hz x hx]; simp only [zero_mul]

/-- Quantitative physical testing of the actual generator output. The output
mass is bounded by an arbitrarily small output-gradient term and explicit
original-gradient terms; no extra physical realization premise is required. -/
theorem IsComplexGeneratorPair.ae_physical_generator_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g H) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ → ∀ ε : ℝ, 0 < ε →
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖H j (translate x ω)‖ ^ 2)) +
        (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)) *
          (∑ j, ‖G j (translate x ω)‖ ^ 2)) := by
  intro L
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  filter_upwards [hfg.ae_physical_generator_output_mass hG hH,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j)),
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (H j)),
    c4_ae_reduced_physical_elliptic Q] with ω hm hgω hGω hHω ha
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  let F : Vec d → Fin d → ℂ := fun x j => (1 / 2 : ℂ) *
    ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)
  let b : Vec d → ℂ := fun x => ∑ j, (ω.1 x j i : ℂ) * G j (translate x ω)
  have hc (K : Set (Vec d)) (j k : Fin d) := memLp_complex_elliptic_entry
    (volume.restrict K) (fun x => ω.1 x) L hL ha
      (fun j k => ω.1.continuous.matrix_elem j k) j k
  have hFω (j : Fin d) (K : Set (Vec d)) (hK : IsCompact K) :
      MemLp (fun x => F x j) 2 (volume.restrict K) := by
    exact (memLp_finsetSum _ (fun k _ => (hc K j k).fun_mul (hGω k K hK))).const_mul _
  have hbω (K : Set (Vec d)) (hK : IsCompact K) : MemLp b 2 (volume.restrict K) := by
    exact memLp_finsetSum _ (fun j _ => (hc K j i).fun_mul (hGω j K hK))
  intro φ hφ ε hε
  let K := tsupport φ
  have hK : IsCompact K := hφ.2.1
  have hz x (hx : x ∉ K) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hD j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hDz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
  have hflux : Integrable (fun x => ∑ j, F x j * ((φ x : ℂ) ^ 2 *
      star (H j (translate x ω)) + 2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
        star (g (translate x ω)))) volume := by
    apply integrable_finsetSum
    intro j _
    have h1 := integrable_physical_cutoff_pairing (hFω j)
      (fun K hK => (hHω j K hK).star) hφ
    have h2 := integrable_physical_compact_pairing hK (hFω j K hK) (hgω K hK).star
      (ψ := fun x => 2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ))
      ((continuous_const.mul (Complex.continuous_ofReal.comp hφ.1.continuous)).mul
        (Complex.continuous_ofReal.comp (hD j))) (fun x hx => by simp [hz x hx])
    convert h1.add h2 using 1
    ext x
    simp only [Pi.star_apply, Pi.add_apply]
    ring
  have hpair := integrable_physical_cutoff_pairing (fun K hK => (hgω K hK).star) hbω hφ
  simp only [Pi.star_apply] at hpair
  have hi := (hpair.const_mul ζ).sub hflux
  have hmass : (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) =
      ∫ x, (ζ * ((φ x : ℂ) ^ 2 * star (g (translate x ω)) * b x) -
        ∑ j, F x j * ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (g (translate x ω)))).re := by
    have hr := integral_re hi
    change (∫ x, (ζ * ((φ x : ℂ) ^ 2 * star (g (translate x ω)) * b x) -
      ∑ j, F x j * ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
          star (g (translate x ω)))).re) = _ at hr
    have hj := integral_sub (hpair.const_mul ζ) hflux
    simp only [integral_const_mul] at hj
    rw [hr]
    exact (hm φ hφ).trans (congrArg Complex.re hj).symm
  let R : Vec d → ℝ := fun x =>
    ((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)
  have hR : Continuous R :=
    (((hφ.1.continuous.pow 2).div_const _).add
      (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hD j).pow 2)))).mul
        continuous_const |>.add ((continuous_const.mul (hφ.1.continuous.pow 2)).mul continuous_const)
  have hRz x (hx : x ∉ K) : R x = 0 := by simp [R, hz x hx, hDz, hx]
  have hRv : Integrable (fun x => R x * (∑ j, ‖G j (translate x ω)‖ ^ 2)) volume := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ =>
      integrable_physical_compact_sq_norm hK (hGω j K hK) hR hRz)
  have hHy : Integrable (fun x => φ x ^ 2 * (∑ j, ‖H j (translate x ω)‖ ^ 2)) volume := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => integrable_physical_compact_sq_norm hK
      (hHω j K hK) (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx]))
  have hv := integrable_physical_compact_sq_norm hK (hgω K hK)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have he := integral_mono_ae (Complex.reCLM.integrable_comp hi)
    (((hv.const_mul (1 / 2 : ℝ)).add (hHy.const_mul ε)).add hRv)
    (Eventually.of_forall (fun x => by
      simpa only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, Complex.reCLM_apply,
        mul_assoc, F, b, R] using
        (complexMatrix_cutoff_output_young (fun j k => ω.1 x j k)
          (fun j => G j (translate x ω)) (fun j => H j (translate x ω))
          (fun j => coordinateDerivative j φ x) (g (translate x ω)) ζ (φ x) ε i
          (fun j k => Correctors.IsElliptic.entry_abs_le hL ha x j k) hε)))
  change (∫ x, (ζ * ((φ x : ℂ) ^ 2 * star (g (translate x ω)) * b x) -
    ∑ j, F x j * ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
      2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
        star (g (translate x ω)))).re) ≤ _ at he
  have hj₁ := integral_add ((hv.const_mul (1 / 2 : ℝ)).add (hHy.const_mul ε)) hRv
  have hj₂ := integral_add (hv.const_mul (1 / 2 : ℝ)) (hHy.const_mul ε)
  simp only [Pi.add_apply, Pi.pow_apply] at he hj₁ hj₂
  rw [← hmass, hj₁, hj₂, integral_const_mul, integral_const_mul] at he
  change _ ≤ _ + (∫ x, R x * (∑ j, ‖G j (translate x ω)‖ ^ 2))
  linarith

/-- Transfer the output-mass estimate to measurable time-dependent physical
representatives. The spatial cutoff and Young parameter are fixed before
exchanging the almost-everywhere time and environment events. -/
theorem ae_joint_physical_generator_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G H : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    (hout : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (v s) (H s))
    {V : ℝ × FieldPair d → ℂ} {D E : Fin d → ℝ × FieldPair d → ℂ}
    (hV : Measurable V) (hD : ∀ j, Measurable (D j)) (hE : ∀ j, Measurable (E j))
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    (heE : ∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] H s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) {ε : ℝ} (hε : 0 < ε) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2)) +
        (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)) *
          (∑ j, ‖D j (s, translate x ω)‖ ^ 2)) := by
  intro L
  let := reducedLaw_probability Q
  let R : Vec d → ℝ := fun x =>
    ((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)
  have hRm : Measurable R := by
    have hd j : Continuous (coordinateDerivative j φ) :=
      ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
    exact (((hφ.1.continuous.measurable.pow_const 2).div_const _).add
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => (hd j).measurable.pow_const 2))).mul
        measurable_const |>.add ((measurable_const.mul
          (hφ.1.continuous.measurable.pow_const 2)).mul measurable_const)
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d => U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hweight {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * ‖U (p.1, translate x p.2)‖ ^ 2) :=
    ((hψ.comp measurable_snd).mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hsum {J : Fin d → ℝ × FieldPair d → ℂ} (hJ : ∀ j, Measurable (J j))
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * (∑ j, ‖J j (p.1, translate x p.2)‖ ^ 2)) :=
    ((hψ.comp measurable_snd).mul (Finset.measurable_sum _ fun j _ =>
      ((hshift (hJ j)).norm.pow_const 2))).stronglyMeasurable.integral_prod_right'.measurable
  let A := fun p : ℝ × FieldPair d =>
    (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (p.1, translate x p.2)‖ ^ 2)
  let B := fun p : ℝ × FieldPair d =>
    ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (p.1, translate x p.2)‖ ^ 2)) +
      (∫ x, R x * (∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2))
  have hA : Measurable A := measurable_const.mul
    (hweight hV (hφ.1.continuous.measurable.pow_const 2))
  have hB : Measurable B := (measurable_const.mul
    (hsum hE (hφ.1.continuous.measurable.pow_const 2))).add (hsum hD hRm)
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  have hee j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hE j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (H s j)).measurable (heE j s)
  filter_upwards [(hgen s hs).ae_physical_generator_output_young (hgrad s hs) (hout s hs),
    hev, ae_all_iff.mpr hed, ae_all_iff.mpr hee] with ω hy hv hd he
  have heall := ae_all_iff.mpr he
  have hdall := ae_all_iff.mpr hd
  have hmass : (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) =
      ∫ x, φ x ^ 2 * ‖(v s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    change V (s, translate x ω) = _ at hx
    rw [hx]
  have hsum_eq {J : Fin d → ℝ × FieldPair d → ℂ} {K : Fin d → Lp ℂ 2 (reducedLaw Q)}
      (hJK : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, J j (s, translate x ω) = K j (translate x ω))
      (ψ : Vec d → ℝ) :
      (∫ x, ψ x * (∑ j, ‖J j (s, translate x ω)‖ ^ 2)) =
        ∫ x, ψ x * (∑ j, ‖K j (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hJK] with x hx
    simp only [hx]
  change (1 / 2 : ℝ) * _ ≤ ε * _ + _
  rw [hmass, hsum_eq heall, hsum_eq hdall]
  exact hy φ hφ ε hε

/-- Local spacetime L2 justifies time integration of the quantitative
output-mass estimate, with any nonnegative continuous time weight. -/
theorem physical_generator_output_young_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c ε : ℝ}
    {V : Vec d × ℝ → ℂ} {D E : Fin d → Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hE : ∀ j, MemLp (E j) 2
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hy : ∀ᵐ s ∂volume.restrict (Icc b c),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (x, s)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (x, s)‖ ^ 2)) +
        (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          ((d : ℝ) ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) ^ 2 / 4)) +
          ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) ^ 2)) *
          (∑ j, ‖D j (x, s)‖ ^ 2))) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    (1 / 2 : ℝ) * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ‖V (x, s)‖ ^ 2)) ≤
      ε * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * (∑ j, ‖E j (x, s)‖ ^ 2))) +
      (∫ s in Icc b c, η s *
        (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)) *
          (∑ j, ‖D j (x, s)‖ ^ 2))) := by
  intro L
  have hz x (hx : x ∉ tsupport φ) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hdz j x (hx : x ∉ tsupport φ) : coordinateDerivative j φ x = 0 := by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  let R : Vec d → ℝ := fun x =>
    ((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)
  have hR : Continuous R :=
    (((hφ.1.continuous.pow 2).div_const _).add
      (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))).mul
        continuous_const |>.add ((continuous_const.mul (hφ.1.continuous.pow 2)).mul continuous_const)
  have hRv := integrable_time_integral_compact_spatial_weight hφ.2.1
    (integrable_finsetSum Finset.univ (fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))) hR
    (fun x hx => by simp [R, hz x hx, hdz, hx])
  have hEv := integrable_time_integral_compact_spatial_weight hφ.2.1
    (integrable_finsetSum Finset.univ (fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hE j).aestronglyMeasurable).mp (hE j)))
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hVv := integrable_time_integral_compact_spatial_weight hφ.2.1
    ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hRη := IntegrableOn.continuousOn_mul hη hRv isCompact_Icc
  have hEη := IntegrableOn.continuousOn_mul hη hEv isCompact_Icc
  have hVη := IntegrableOn.continuousOn_mul hη hVv isCompact_Icc
  have hi := integral_mono_ae (hVη.const_mul (1 / 2 : ℝ))
    ((hEη.const_mul ε).add hRη) (by
      filter_upwards [hy, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.pow_apply]
      change _ ≤ _ + η s * (∫ x, R x * (∑ j, ‖D j (x, s)‖ ^ 2))
      nlinarith [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.pow_apply] at hi
  have hj := integral_add (hEη.const_mul ε) hRη
  simp only [Pi.pow_apply] at hj
  rw [hj, integral_const_mul, integral_const_mul] at hi
  exact hi

/-- The actual corrected orbit and its restarted derivative satisfy the
integrated output-mass estimate, with the actual original and derivative
semigroup gradients and no additional physical estimate premise. -/
theorem complexForced_correctedOrbit_ae_physical_integratedOutputYoung
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit g (s - a)) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ ε : ℝ, 0 < ε → ∀ η : ℝ → ℝ, ContinuousOn η (Icc b c) →
          (∀ s ∈ Icc b c, 0 ≤ η s) → ∀ᵐ ω ∂reducedLaw Q,
          (1 / 2 : ℝ) * (∫ s in Icc b c, η s *
            (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2)) ≤
            ε * (∫ s in Icc b c, η s *
              (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2))) +
            (∫ s in Icc b c, η s *
              (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
                ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)) *
                (∑ j, ‖D j (s, translate x ω)‖ ^ 2))) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, hcut⟩ :=
    complexForced_correctedOrbit_ae_physical_jointCutoffEnergy hP f ht ha
  obtain ⟨E, hE, heE, hElocal⟩ := hP.exists_ae_spacetime_restarted_gradient g a
  refine ⟨g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hregular, ?_⟩
  intro b c hb hbc φ hφ ε hε η hη hηpos
  have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      ((hcont.norm.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure ℝ)) (K := Icc b c) isCompact_Icc)
      hV heV)
  have hyoung := ae_joint_physical_generator_output_young (b := b) (c := c)
    (u := w) (v := fun s => P (s - a).toNNReal g)
    (G := fun s j => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
    (H := fun s j => (hP.gradientOrbit g (s - a)) j)
    (fun s hs => (hregular s (hb.trans_le hs.1)).2)
    (fun s hs => complexForced_correctedOrbit_gradient_spec hP f t
      (ha.trans (hb.trans_le hs.1)))
    (fun s hs => hP.gradientOrbit_spec g (sub_pos.mpr (hb.trans_le hs.1)))
    hV hD hE heV heD heE hφ hε
  filter_upwards [hyoung, hlocalV, hElocal b c hb, hcut b c hb hbc φ hφ]
    with ω hy hv he hd
  exact physical_generator_output_young_time_integral hφ
    (hv (tsupport φ) hφ.2.1) (hd.1 (tsupport φ) hφ.2.1)
    (he (tsupport φ) hφ.2.1) hη hηpos hy


/-- Compare any inner time set with a nonnegative temporal cutoff which is one
there. This permits nested cylinders with independently chosen time gaps. -/
theorem physical_inner_spacetime_integral_le {d : ℕ} {K S : Set (Vec d)}
    (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {b c : ℝ} {J : Set ℝ} (hJ : MeasurableSet J) (hJI : J ⊆ Icc b c)
    {F : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hFpos : ∀ p, 0 ≤ F p) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hzero : ∀ x, x ∉ K → φ x = 0) (hone : ∀ x ∈ S, φ x = 1)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s) (hηlower : ∀ s ∈ J, 1 ≤ η s) :
    (∫ s in J, ∫ x in S, F (x, s)) ≤
      ∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * F (x, s)) := by
  have hw := IntegrableOn.continuousOn_mul hη
    (integrable_time_integral_compact_spatial_weight hK hF (hφ.pow 2)
      (fun x hx => by simp only [Pi.pow_apply, hzero x hx, zero_pow (by decide : 2 ≠ 0)]))
    isCompact_Icc
  have hinner := hF.mono_measure
    (Measure.prod_mono (Measure.restrict_mono hSK le_rfl) le_rfl)
  have hiJ := hinner.integral_prod_right.mono_measure (Measure.restrict_mono hJI le_rfl)
  have hwJ := hw.mono_set hJI
  have hcmp : (∫ s in J, ∫ x in S, F (x, s)) ≤
      ∫ s in J, η s * (∫ x, φ x ^ 2 * F (x, s)) := by
    apply integral_mono_ae hiJ hwJ
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hJI hF.prod_left_ae,
      ae_restrict_mem hJ] with s hs hsm
    have hi : IntegrableOn (fun x => φ x ^ 2 * F (x, s)) K volume :=
      IntegrableOn.continuousOn_mul (hφ.pow 2).continuousOn hs hK
    have he : (∫ x in S, F (x, s)) = ∫ x in S, φ x ^ 2 * F (x, s) := by
      apply setIntegral_congr_fun hS
      intro x hx
      change F (x, s) = φ x ^ 2 * F (x, s)
      rw [hone x hx]
      simp
    have hsp := setIntegral_mono_set hi
      (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))
      (Eventually.of_forall (fun x hx => hSK hx))
    have hz : (∫ x in K, φ x ^ 2 * F (x, s)) = ∫ x, φ x ^ 2 * F (x, s) :=
      setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzero x hx]; simp)
    rw [← he, hz] at hsp
    have hp : 0 ≤ ∫ x, φ x ^ 2 * F (x, s) :=
      integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s)))
    exact hsp.trans (le_mul_of_one_le_left hp (hηlower s hsm))
  apply hcmp.trans
  apply setIntegral_mono_set hw _ (Eventually.of_forall (fun s hs => hJI hs))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact mul_nonneg (hηpos s hs)
    (integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (hFpos (x, s))))

/-- Caccioppoli with independent inner/outer spatial and temporal cutoffs.
The constants are the actual cutoff derivative bounds, so a shrinking gap
can be used without fixing a radius ratio or halving every time interval. -/
theorem physical_spacetime_caccioppoli_of_cutoff_energy {d : ℕ}
    {K S : Set (Vec d)} (hK : IsCompact K) (hS : MeasurableSet S) (hSK : S ⊆ K)
    {b c L C A T : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJI : J ⊆ Icc b c) {ζ : ℂ}
    {W : Vec d × ℝ → ℂ} {D : Fin d → Vec d × ℝ → ℂ} {U : Vec d → ℂ}
    (hW : MemLp W 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2 ((volume.restrict K).prod (volume.restrict (Icc b c))))
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hφrange : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hone : ∀ x ∈ S, φ x = 1) (hzero : ∀ x, x ∉ K → φ x = 0)
    (herror : ∀ x ∈ K,
      ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 ≤ A)
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηd : ContinuousOn (deriv η) (Icc b c))
    (hηrange : ∀ s ∈ Icc b c, 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ T)
    (hηlower : ∀ s ∈ J, 1 ≤ η s)
    (henergy : (L⁻¹ / 4) *
        (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      -(∫ x, φ x ^ 2 * ‖U x‖ ^ 2) / 2 +
        (∫ s in Icc b c, deriv η s * (∫ x, φ x ^ 2 * ‖W (x, s)‖ ^ 2)) / 2 +
        C * (∫ s in Icc b c, η s *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2) *
            ‖W (x, s)‖ ^ 2))) :
    (∫ s in J, ∫ x in S, ∑ j, ‖D j (x, s)‖ ^ 2) ≤
      4 * L * (T / 2 + C * A) * (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2) := by
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hzero x hn)) hK.isClosed
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have ht := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hzero x hx, zero_pow (by decide : 2 ≠ 0)])
    hηd (A := T) (by
      intro s hs x hx
      have hsq : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
      simpa only [Pi.pow_apply, mul_one] using
        (mul_le_mul_of_nonneg_left hsq (hηrange s hs).2.2.1).trans
          (by simpa only [mul_one] using (hηrange s hs).2.2.2))
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have he := physical_spacetime_weight_integral_le hK hiW
    (fun p => sq_nonneg ‖W p‖)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (fun x hx => by simp [hzero x hx, hdz, hx]) hη (A := A) (by
      intro s hs x hx
      have hp : 0 ≤ ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 :=
        add_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Finset.sum_nonneg (fun j _ => sq_nonneg _))
      exact (mul_le_mul_of_nonneg_right (hηrange s hs).2.1 hp).trans
        (by simpa only [one_mul] using herror x hx))
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
  have hinner := physical_inner_spacetime_integral_le hK hS hSK hJ hJI hiD
    (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg ‖D j p‖))
    hφ.1.continuous hzero hone hη (fun s hs => (hηrange s hs).1) hηlower
  have hp : 0 ≤ ∫ x, φ x ^ 2 * ‖U x‖ ^ 2 :=
    integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hu : (L⁻¹ / 4) *
      (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ∑ j, ‖D j (x, s)‖ ^ 2)) ≤
      (T / 2 + C * A) * (∫ s in Icc b c, ∫ x in K, ‖W (x, s)‖ ^ 2) := by
    simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at ht he
    have hce := mul_le_mul_of_nonneg_left he hC
    nlinarith only [henergy, hp, ht, hce]
  have hm := mul_le_mul_of_nonneg_left hu (show 0 ≤ 4 * L by positivity)
  have hinv : (4 * L) * (L⁻¹ / 4) = 1 := by field_simp [hL.ne']
  rw [← mul_assoc, hinv, one_mul] at hm
  exact hinner.trans (by nlinarith only [hm])


/-- The fixed smooth transition has a globally bounded derivative. -/
theorem exists_smoothTransition_deriv_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ, |deriv Real.smoothTransition s| ≤ B := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := ⊤)).continuous_deriv (by simp)
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hc.continuousOn : ContinuousOn (deriv Real.smoothTransition) (Icc (0 : ℝ) 1))
  refine ⟨max N 0 + 1, by positivity, ?_⟩
  intro s
  by_cases hs : s ∈ Icc (0 : ℝ) 1
  · have hNs : |deriv Real.smoothTransition s| ≤ N := by
      simpa only [Real.norm_eq_abs] using hN s hs
    exact hNs.trans ((le_max_left N 0).trans (le_add_of_nonneg_right zero_le_one))
  · have hz : deriv Real.smoothTransition s = 0 := by
      rcases (not_and_or.mp hs) with hs | hs
      all_goals have hs := lt_of_not_ge hs
      · have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (0 : ℝ)) := by
          filter_upwards [eventually_lt_nhds hs] with y hy
          exact Real.smoothTransition.zero_of_nonpos hy.le
        simpa only [deriv_const] using he.deriv_eq
      · have he : Real.smoothTransition =ᶠ[𝓝 s] (fun _ => (1 : ℝ)) := by
          filter_upwards [eventually_gt_nhds hs] with y hy
          exact Real.smoothTransition.one_of_one_le hy.le
        simpa only [deriv_const] using he.deriv_eq
    rw [hz, abs_zero]
    positivity

/-- A smooth temporal cutoff reaches one after any prescribed positive gap.
Its derivative bound depends only on the inverse gap, not the outer duration. -/
theorem exists_physical_gap_temporal_cutoff :
    ∃ B : ℝ, 0 < B ∧ ∀ b e : ℝ, b < e → ∃ η : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ η b = 0 ∧ (∀ s, e ≤ s → η s = 1) ∧
      ∀ s, 0 ≤ η s ∧ η s ≤ 1 ∧ 0 ≤ deriv η s ∧ deriv η s ≤ B / (e - b) := by
  obtain ⟨B, hB, hbound⟩ := exists_smoothTransition_deriv_bound
  refine ⟨B, hB, ?_⟩
  intro b e hbe
  have hgap : 0 < e - b := sub_pos.mpr hbe
  let η : ℝ → ℝ := fun s => Real.smoothTransition ((s - b) / (e - b))
  have hd s : deriv η s = deriv Real.smoothTransition ((s - b) / (e - b)) / (e - b) := by
    have h := ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp)
      ((s - b) / (e - b))).hasDerivAt.comp s
        (((hasDerivAt_id s).sub_const b).div_const (e - b))
    change HasDerivAt η _ s at h
    rw [h.deriv]
    ring
  refine ⟨η, Real.smoothTransition.contDiff.comp (by fun_prop), ?_, ?_, ?_⟩
  · simp only [η, sub_self, zero_div, Real.smoothTransition.zero]
  · intro s hs
    exact Real.smoothTransition.one_of_one_le ((one_le_div hgap).mpr (by linarith))
  · intro s
    refine ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, ?_, ?_⟩
    · rw [hd]
      exact div_nonneg Real.smoothTransition.monotone.deriv_nonneg hgap.le
    · rw [hd]
      exact div_le_div_of_nonneg_right
        ((le_abs_self _).trans (hbound _)) hgap.le


/-- Smooth Euclidean annular cutoffs have a uniform inverse-gap derivative
bound, including when the inner and outer radii are arbitrarily close. -/
theorem exists_physical_gap_euclidean_cutoff (d : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z : Vec d, ∀ r R : ℝ, 0 < r → r < R →
      ∃ φ : Vec d → ℝ, IsSpatialTest univ φ ∧
        (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧
        (∀ x, euclideanNorm (x - z) ≤ r → φ x = 1) ∧
        (∀ x, R ≤ euclideanNorm (x - z) → φ x = 0) ∧
        ∀ j x, |coordinateDerivative j φ x| ≤ B / (R - r) := by
  obtain ⟨B, hB, hbound⟩ := exists_smoothTransition_deriv_bound
  refine ⟨2 * B, by positivity, ?_⟩
  intro z r R hr hrR
  have hR : 0 < R := hr.trans hrR
  have hgap : 0 < R - r := sub_pos.mpr hrR
  let Δ := R ^ 2 - r ^ 2
  have hΔ : 0 < Δ := by dsimp [Δ]; nlinarith
  let q : Vec d → ℝ := fun x => Δ⁻¹ * ((∑ k, (x k - z k) ^ 2) - r ^ 2)
  let φ : Vec d → ℝ := fun x => 1 - Real.smoothTransition (q x)
  have hnorm x : euclideanNorm (x - z) ^ 2 = ∑ k, (x k - z k) ^ 2 := by
    change Real.sqrt (∑ k, (x k - z k) * (x k - z k)) ^ 2 = _
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun k _ => mul_self_nonneg (x k - z k)))]
    simp only [pow_two]
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := by dsimp [q]; fun_prop
  have hc : ContDiff ℝ (⊤ : ℕ∞) φ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp hq)
  have hz x (hx : R ≤ euclideanNorm (x - z)) : φ x = 0 := by
    have hs : R ^ 2 ≤ ∑ k, (x k - z k) ^ 2 := by
      rw [← hnorm]
      nlinarith
    have hqq : 1 ≤ q x := by
      dsimp [q]
      apply (le_inv_mul_iff₀ hΔ).mpr
      dsimp [Δ]
      linarith
    dsimp [φ]
    rw [Real.smoothTransition.one_of_one_le hqq, sub_self]
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hsupport : tsupport φ ⊆ K := closure_minimal
    (fun x hx => by
      by_contra hn
      exact hx (hz x (not_le.mp hn).le)) hK.isClosed
  have hφ : IsSpatialTest univ φ :=
    ⟨hc, hK.of_isClosed_subset isClosed_closure hsupport, subset_univ _⟩
  refine ⟨φ, hφ, fun x => ⟨by dsimp [φ]; linarith [Real.smoothTransition.le_one (q x)],
    by dsimp [φ]; linarith [Real.smoothTransition.nonneg (q x)]⟩, ?_, hz, ?_⟩
  · intro x hx
    have hs : (∑ k, (x k - z k) ^ 2) ≤ r ^ 2 := by
      rw [← hnorm]
      have hp : 0 ≤ euclideanNorm (x - z) := Real.sqrt_nonneg _
      nlinarith
    have hqq : q x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos
      (inv_nonneg.mpr hΔ.le) (sub_nonpos.mpr hs)
    dsimp [φ]
    rw [Real.smoothTransition.zero_of_nonpos hqq, sub_zero]
  · intro j x
    by_cases hx : x ∈ K
    · have hqd : HasFDerivAt q (Δ⁻¹ •
          (∑ k : Fin d, (2 * (x k - z k)) •
            (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ))) x := by
        simpa only [q, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat,
          Pi.smul_def, smul_eq_mul, ContinuousLinearMap.proj_apply] using
          ((HasFDerivAt.fun_sum (u := Finset.univ) (fun k _ =>
            ((ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ).hasFDerivAt.sub_const (z k)).pow 2)).sub_const
              (r ^ 2)).const_smul Δ⁻¹
      have hpd := ((hasDerivAt_const (q x) (1 : ℝ)).sub
        ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) (q x)).hasDerivAt).comp_hasFDerivAt x hqd
      change HasFDerivAt φ _ x at hpd
      have hd : coordinateDerivative j φ x =
          -(deriv Real.smoothTransition (q x) * Δ⁻¹ * (2 * (x j - z j))) := by
        simp [coordinateDerivative, hpd.fderiv, unitVector, Pi.single_apply,
          smul_eq_mul]
        ring
      have hcoord : (x j - z j) ^ 2 ≤ ∑ k, (x k - z k) ^ 2 :=
        Finset.single_le_sum (fun k _ => sq_nonneg (x k - z k)) (Finset.mem_univ j)
      have hsum : (∑ k, (x k - z k) ^ 2) ≤ R ^ 2 := by
        rw [← hnorm]
        change euclideanNorm (x - z) ≤ R at hx
        have hp : 0 ≤ euclideanNorm (x - z) := Real.sqrt_nonneg _
        nlinarith
      have hcoord' : |x j - z j| ≤ R := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
      calc
        |coordinateDerivative j φ x| =
            |deriv Real.smoothTransition (q x)| * (2 * |x j - z j|) / Δ := by
          rw [hd]
          simp only [abs_neg, abs_mul, abs_of_pos (inv_pos.mpr hΔ), abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
          ring
        _ ≤ B * (2 * R) / Δ := by
          apply div_le_div_of_nonneg_right _ hΔ.le
          exact mul_le_mul (hbound _) (by linarith) (by positivity) hB.le
        _ ≤ (2 * B) / (R - r) := by
          apply (div_le_div_iff₀ hΔ hgap).mpr
          dsimp [Δ]
          nlinarith [mul_nonneg (mul_nonneg hB.le hr.le) hgap.le]
    · have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
      simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply, abs_zero]
      positivity


/-- The spatial cutoff error with an arbitrary positive annular gap. -/
theorem physical_gap_cutoff_error_bound {d : ℕ} {φ : Vec d → ℝ}
    {ζ : ℂ} {B δ : ℝ} (hφ : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hD : ∀ j x, |coordinateDerivative j φ x| ≤ B / δ) (x : Vec d) :
    ‖ζ‖ ^ 2 * φ x ^ 2 + ∑ j, (coordinateDerivative j φ x) ^ 2 ≤
      ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / δ ^ 2 := by
  have hs : φ x ^ 2 ≤ 1 := by nlinarith [hφ x]
  have hd j : (coordinateDerivative j φ x) ^ 2 ≤ B ^ 2 / δ ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (coordinateDerivative j φ x)) (hD j x)
    simpa only [← sq, sq_abs, div_pow] using h
  have hsum : (∑ j, (coordinateDerivative j φ x) ^ 2) ≤
      (d : ℝ) * (B ^ 2 / δ ^ 2) := by
    simpa using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hd j)
  have hf := mul_le_mul_of_nonneg_left hs (sq_nonneg ‖ζ‖)
  simp only [mul_one] at hf
  simpa only [mul_div_assoc] using add_le_add hf hsum

/-- Actual corrected-orbit Caccioppoli with independently prescribed spatial
and temporal gaps. This is the form used on nested cylinders. -/
theorem complexForced_correctedOrbit_ae_physical_gapCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b e c : ℝ, a < b → b < e → e ≤ c → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - b) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖W (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨T, hT, htime⟩ := exists_physical_gap_temporal_cutoff
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨B, T, hB, hT, g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b e c hb hbe hec z r R hr hrR
  have hbc : b < c := hbe.trans_le hec
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime b e hbe
  have hηcont : ContinuousOn η (Icc b c) := hη.continuous.continuousOn
  have hηd : ContinuousOn (deriv η) (Icc b c) :=
    (hη.continuous_deriv (by simp)).continuousOn
  have hηac : AbsolutelyContinuousOnInterval η b c :=
    (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit (centeredComplexLp Q f) s) j‖ ^ 2)
        (Icc b c) volume :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy b c hb hbc.le φ hφ η hηac hηd
    (fun s _ => (hηbounds s).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z R
  apply physical_spacetime_caccioppoli_of_cutoff_energy hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) hL hC measurableSet_Icc
    (Icc_subset_Icc_left hbe.le) (U := fun x => (w c) (translate x ω))
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange
    (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
    hηcont hηd (fun s _ => hηbounds s) (fun s hs => (hηone s hs.1).ge)
  rw [hηb, hηone c hec, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Arbitrary-gap cylinder control for the actual restarted time derivative. -/
theorem complexForced_correctedOrbit_derivative_ae_gapCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧ ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - c) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖V (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨T, hT, htime⟩ := exists_physical_gap_temporal_cutoff
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  refine ⟨B, T, hB, hT, g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD,
    hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hu : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro c e v hc hce hev z r R hr hrR
  have hcv : c < v := hce.trans_le hev
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime c e hce
  have hηcont : ContinuousOn η (Icc c v) := hη.continuous.continuousOn
  have hηd : ContinuousOn (deriv η) (Icc c v) :=
    (hη.continuous_deriv (by simp)).continuousOn
  have hηac : AbsolutelyContinuousOnInterval η c v :=
    (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c v) volume :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc c v))) := by
    have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
      (hP.continuousOn_gradientOrbit g).comp
        (continuous_id.sub continuous_const).continuousOn (fun s hs => by
          change 0 < s - a
          exact sub_pos.mpr hs)
    have hcoord : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit g (s - a)) j‖ ^ 2)
        (Icc c v) volume :=
      ((hcoord.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (hab.trans hc) hs.1)).integrableOn_compact
        isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy c v hc hcv.le φ hφ η hηac hηd
    (fun s _ => (hηbounds s).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z R
  apply physical_spacetime_caccioppoli_of_cutoff_energy hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) hL hC measurableSet_Icc
    (Icc_subset_Icc_left hce.le) (U := fun x => (u v) (translate x ω))
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange
    (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
    hηcont hηd (fun s _ => hηbounds s) (fun s hs => (hηone s hs.1).ge)
  rw [hηb, hηone v hev, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]


/-- The initial datum of a continuous restarted derivative orbit is unique.
This identifies independent energy constructions before physical realization. -/
theorem IsComplexEnvironmentSemigroup.restart_derivative_unique
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {w : ℝ → Lp ℂ 2 (reducedLaw Q)} {a : ℝ}
    {g h : Lp ℂ 2 (reducedLaw Q)}
    (hg : ∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s)
    (hh : ∀ s, a < s → HasDerivAt w (P (s - a).toNNReal h) s) : g = h := by
  have he : EqOn (fun s : ℝ => P (s - a).toNNReal g)
      (fun s : ℝ => P (s - a).toNNReal h) (Ioi a) :=
    fun s hs => (hg s hs).unique (hh s hs)
  have hc (v : Lp ℂ 2 (reducedLaw Q)) :
      Continuous (fun s : ℝ => P (s - a).toNNReal v) :=
    (hP.2.2.1 v).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hea := he.closure (hc g) (hc h)
    (show a ∈ closure (Ioi a) by
      simpa only [closure_Ioi, mem_Ici] using (le_refl a))
  simpa only [sub_self, Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply] using hea

end EinsteinFull
