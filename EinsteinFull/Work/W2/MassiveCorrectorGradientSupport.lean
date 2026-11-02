import EinsteinFull.Work.W2.CorrectorReuseSupport
import EinsteinFull.Calculus.ComplexGeneratorOperatorSupport
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinRelation.Mobility.DriftWeakDivergence
import Mathlib.Topology.MetricSpace.Equicontinuity

/-!
# Massive corrector energy and gradient convergence on the actual reduced law

The drift identity below tests every strong complex horizontal H1 function.
Positive massive correctors are the actual full-generator resolvents, with
Euclidean gradient energy controlled uniformly in the mass. Their gradients
converge strongly in reduced Euclidean L2 to the complexification of the
literal canonical real corrector gradient.
-/

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors

private instance reducedProbability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- A real linear observation commutes with the actual L2 translations. -/
theorem translationLp_complex_realMap {d : ℕ} (μ : Measure (FieldPair d))
    (hμ : IsStationary μ) (T : ℂ →L[ℝ] ℝ) (x : Vec d) (f : Lp ℂ 2 μ) :
    translationLp μ hμ x (T.compLpL 2 μ f) =
      T.compLpL 2 μ (complexTranslation μ hμ x f) := by
  apply Lp.ext
  have hc := (measurePreserving_translate μ hμ x).quasiMeasurePreserving.ae
    (T.coeFn_compLpL f)
  filter_upwards [coeFn_translationLp μ hμ x (T.compLpL 2 μ f),
    T.coeFn_compLpL (complexTranslation μ hμ x f),
    coeFn_complexTranslation μ hμ x f, hc] with ω ha hb hd he
  change (T.compLpL 2 μ f) (translate x ω) = T (f (translate x ω)) at he
  rw [ha, he, hb, hd]

/-- Real and imaginary parts preserve the full strong horizontal derivative domain. -/
theorem HasComplexHorizontalDerivative.realMap {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {k : Fin d} {f g : Lp ℂ 2 μ}
    (h : HasComplexHorizontalDerivative μ hμ k f g) (T : ℂ →L[ℝ] ℝ) :
    HasHorizontalLpDerivative μ hμ k (T.compLpL 2 μ f) (T.compLpL 2 μ g) := by
  have ht := ((T.compLpL 2 μ).continuous.tendsto g).comp h
  change Tendsto (fun t : ℝ => T.compLpL 2 μ ((t : ℂ)⁻¹ •
    (complexTranslation μ hμ (t • unitVector k) f - f)))
    (𝓝[≠] (0 : ℝ)) (𝓝 (T.compLpL 2 μ g)) at ht
  simp only [← Complex.ofReal_inv, Complex.coe_smul] at ht
  change Tendsto (fun t : ℝ => T.compLpL 2 μ (t⁻¹ •
    (complexTranslation μ hμ (t • unitVector k) f - f))) _ _ at ht
  simp only [map_smul, map_sub, ← translationLp_complex_realMap] at ht
  exact ht

private theorem reducedColumn_real_pairing {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d)
    (v : Lp ℝ 2 (reducedLaw Q)) (V : Fin d → Lp ℝ 2 (reducedLaw Q))
    (hV : ∀ k, HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) k v (V k)) :
    (∫ ω, ∑ k, ω.1 0 k j * V k ω ∂reducedLaw Q) =
      -(∫ ω, DriftH5.cdiv j ω * v ω ∂reducedLaw Q) := by
  obtain ⟨L, B, hL, _, hreg⟩ := DriftH5.ae_entry_regular Q (reducedLaw_stationary Q)
  have hentry (k : Fin d) : Measurable (fun ω : FieldPair d => ω.1 0 k j) :=
    (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem k j).measurable
  have hdmeas (k : Fin d) : Measurable (fun ω : FieldPair d =>
      fderiv ℝ (fun y => ω.1 y k j) 0 (unitVector k)) := by
    exact (measurable_fderiv_apply_const_with_param ℝ
      (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y k j)
      (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
        |>.matrix_elem k j) (unitVector k)).comp (measurable_id.prodMk measurable_const)
  have hint (k : Fin d) : Integrable (fun ω => ω.1 0 k j * V k ω) (reducedLaw Q) := by
    apply Integrable.bdd_mul ((Lp.memLp (V k)).integrable (by norm_num))
      (hentry k).aestronglyMeasurable
    filter_upwards [hreg] with ω hω
    simpa only [Real.norm_eq_abs] using! (hω k j).2.1
  have hdint (k : Fin d) : Integrable (fun ω =>
      fderiv ℝ (fun y => ω.1 y k j) 0 (unitVector k) * v ω) (reducedLaw Q) := by
    apply Integrable.bdd_mul ((Lp.memLp v).integrable (by norm_num))
      (hdmeas k).aestronglyMeasurable
    filter_upwards [hreg] with ω hω
    simpa only [Real.norm_eq_abs] using! (hω k j).2.2.2 k
  have hp (k : Fin d) := DriftH5.integral_mul_deriv_of_orbit
    (reducedLaw_stationary Q) k (hentry k) hL
    (hreg.mono fun ω hω => by
      change ∀ t : ℝ, |ω.1 (-(t • unitVector k) + 0) k j - ω.1 0 k j| ≤ L * |t|
      simpa only [add_zero] using! (hω k j).1 k)
    (hreg.mono fun ω hω => (hω k j).2.1)
    (hreg.mono fun ω hω => by
      change DifferentiableAt ℝ (fun y => ω.1 (y + 0) k j) 0
      simpa only [add_zero] using! (hω k j).2.2.1)
    v (V k) (hV k)
  change ∀ k, (∫ ω, ω.1 0 k j * V k ω ∂reducedLaw Q) =
    -(∫ ω, fderiv ℝ (fun y => ω.1 (y + 0) k j) 0 (unitVector k) * v ω ∂reducedLaw Q) at hp
  simp only [add_zero] at hp
  rw [integral_finset_sum _ (fun k _ => hint k)]
  simp_rw [hp]
  rw [Finset.sum_neg_distrib, ← integral_finset_sum _ (fun k _ => hdint k)]
  simp only [DriftH5.cdiv, Finset.sum_mul]

private theorem integrable_column_pairing {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d) (V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∑ k, (ω.1 0 k j : ℂ) * V k ω) (reducedLaw Q) := by
  apply integrable_finset_sum
  intro k _
  obtain ⟨B, _, hB⟩ := DriftH5.exists_ae_abs_entry_le d Λ₀ r₀
  exact ((Lp.memLp (V k)).integrable (by norm_num)).bdd_mul (c := B)
    (memLp_reduced_coefficient_complex Q k j).aestronglyMeasurable
    (by
      filter_upwards [hB Q] with ω hω
      simpa only [Complex.norm_real, Real.norm_eq_abs] using! hω k j)

/-- The literal reduced drift is half the blueprint's classical column divergence. -/
theorem IsReducedDriftObservation.ae_eq_cdiv {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) :
    β j =ᵐ[reducedLaw Q] fun ω => ((1 / 2 : ℝ) * DriftH5.cdiv j ω : ℝ) := hβ j

/-- Weak divergence of the actual drift against every actual complex horizontal H1 test. -/
theorem IsReducedDriftObservation.integral_mul {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, β j ω * v ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q := by
  have hleft : Integrable (fun ω => β j ω * v ω) (reducedLaw Q) :=
    (Lp.memLp (β j)).integrable_mul (Lp.memLp v)
  have hright := integrable_column_pairing Q j V
  have hp (T : ℂ →L[ℝ] ℝ) := reducedColumn_real_pairing Q j
    (T.compLpL 2 (reducedLaw Q) v) (fun k => T.compLpL 2 (reducedLaw Q) (V k))
    (fun k => (hV k).realMap T)
  have hreal (T : ℂ →L[ℝ] ℝ) :
      (∫ ω, T (β j ω * v ω) ∂reducedLaw Q) =
        -(1 / 2 : ℝ) * ∫ ω, T (∑ k, (ω.1 0 k j : ℂ) * V k ω) ∂reducedLaw Q := by
    have hv := T.coeFn_compLpL v
    have hg := ae_all_iff.mpr fun k => T.coeFn_compLpL (V k)
    have he1 : (fun ω => T (β j ω * v ω)) =ᵐ[reducedLaw Q]
        fun ω => (1 / 2 : ℝ) * DriftH5.cdiv j ω * (T.compLpL 2 (reducedLaw Q) v) ω := by
      filter_upwards [hβ.ae_eq_cdiv j, hv] with ω hb hvω
      rw [hb, hvω]
      change T (((1 / 2 : ℝ) * DriftH5.cdiv j ω) • v ω) = _
      rw [map_smul]
      rfl
    have he2 : (fun ω => T (∑ k, (ω.1 0 k j : ℂ) * V k ω)) =ᵐ[reducedLaw Q]
        fun ω => ∑ k, ω.1 0 k j * (T.compLpL 2 (reducedLaw Q) (V k)) ω := by
      filter_upwards [hg] with ω hω
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hω k]
      exact T.map_smul (ω.1 0 k j) (V k ω)
    rw [integral_congr_ae he1, integral_congr_ae he2]
    simp_rw [mul_assoc (1 / 2 : ℝ)]
    rw [integral_const_mul, hp T]
    ring
  apply Complex.ext
  · have hr := hreal Complex.reCLM
    simp only [Complex.reCLM_apply] at hr
    have h1 := integral_re hleft
    have h2 := integral_re hright
    simp only [RCLike.re_eq_complex_re] at h1 h2
    rw [h1, h2] at hr
    simpa using! hr
  · have hi := hreal Complex.imCLM
    simp only [Complex.imCLM_apply] at hi
    have h1 := integral_im hleft
    have h2 := integral_im hright
    simp only [RCLike.im_eq_complex_im] at h1 h2
    rw [h1, h2] at hi
    simpa using! hi

/-- The actual gradient witness constructed from the full positive-resolvent graph. -/
def unforcedComplexResolventGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) : Fin d → Lp ℂ 2 (reducedLaw Q) :=
  (unforcedComplexResolvent_spec Q i s hs rhs).choose

/-- The chosen witness is the strong horizontal gradient of the actual resolvent. -/
theorem hasComplexHorizontalGradient_unforcedComplexResolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (unforcedComplexResolvent Q i s hs rhs)
      (unforcedComplexResolventGradient Q i s hs rhs) :=
  (unforcedComplexResolvent_spec Q i s hs rhs).choose_spec.1

private theorem memLp_resolventEuclideanGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    MemLp (fun ω => (WithLp.toLp 2
      (fun k => unforcedComplexResolventGradient Q i s hs rhs k ω) :
        EuclideanSpace ℂ (Fin d))) 2 (reducedLaw Q) :=
  memLp_piLp_iff.mpr fun k => Lp.memLp (unforcedComplexResolventGradient Q i s hs rhs k)

/-- The massive gradient in the actual Euclidean-valued reduced L2 space. -/
def unforcedComplexResolventEuclideanGradient {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) : Lp (EuclideanSpace ℂ (Fin d)) 2 (reducedLaw Q) :=
  (memLp_resolventEuclideanGradient Q i s hs rhs).toLp _

/-- Each Euclidean coordinate is the corresponding actual strong horizontal derivative. -/
theorem unforcedComplexResolventEuclideanGradient_ae {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ k,
      unforcedComplexResolventEuclideanGradient Q i s hs rhs ω k =
        unforcedComplexResolventGradient Q i s hs rhs k ω := by
  filter_upwards [(memLp_resolventEuclideanGradient Q i s hs rhs).coeFn_toLp] with ω hω
  exact fun k => congrArg (fun v : EuclideanSpace ℂ (Fin d) => v k) hω

private theorem norm_sq_L2 {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure α) (f : Lp E 2 μ) :
    ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- The vector gradient norm is exactly the Euclidean sum, with no supremum norm conversion. -/
theorem norm_unforcedComplexResolventEuclideanGradient_sq {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ‖unforcedComplexResolventEuclideanGradient Q i s hs rhs‖ ^ 2 =
      ∑ k, ‖unforcedComplexResolventGradient Q i s hs rhs k‖ ^ 2 := by
  rw [norm_sq_L2]
  have he : (∫ ω, ‖unforcedComplexResolventEuclideanGradient Q i s hs rhs ω‖ ^ 2
      ∂reducedLaw Q) =
      ∫ ω, ∑ k, ‖unforcedComplexResolventGradient Q i s hs rhs k ω‖ ^ 2 ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [unforcedComplexResolventEuclideanGradient_ae Q i s hs rhs] with ω hω
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun k _ => congrArg (fun z : ℂ => ‖z‖ ^ 2) (hω k)
  rw [he, integral_finset_sum _ (fun k _ =>
    (Lp.memLp (unforcedComplexResolventGradient Q i s hs rhs k)).norm.integrable_sq)]
  exact Finset.sum_congr rfl fun k _ => (norm_sq_L2 _ _).symm

/-- The massive equation holds on the full test domain, with the actual coefficient and drift. -/
theorem IsReducedDriftObservation.resolvent_weak_equation {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) (s : ℝ) (hs : 0 < s)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (s : ℂ) * (∫ ω, unforcedComplexResolvent Q i s hs (β j) ω * v ω ∂reducedLaw Q) +
      (1 / 2 : ℂ) * (∫ ω, ∑ k, ∑ l, (ω.1 0 k l : ℂ) *
        unforcedComplexResolventGradient Q i s hs (β j) l ω * V k ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q := by
  let f := unforcedComplexResolvent Q i s hs (β j)
  have hw := (unforcedComplexResolvent_spec Q i s hs (β j)).choose_spec.2 v V hV
  have hm : (∫ ω, ((s : ℂ) • f - β j : Lp ℂ 2 (reducedLaw Q)) ω * v ω ∂reducedLaw Q) =
      (s : ℂ) * (∫ ω, f ω * v ω ∂reducedLaw Q) - ∫ ω, β j ω * v ω ∂reducedLaw Q := by
    have he : (fun ω => ((s : ℂ) • f - β j : Lp ℂ 2 (reducedLaw Q)) ω * v ω) =ᵐ[reducedLaw Q]
        fun ω => (s : ℂ) * (f ω * v ω) - β j ω * v ω := by
      filter_upwards [Lp.coeFn_sub ((s : ℂ) • f) (β j), Lp.coeFn_smul (s : ℂ) f]
        with ω ha hb
      simp only [ha, hb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hfv : Integrable (fun ω => f ω * v ω) (reducedLaw Q) :=
      (Lp.memLp f).integrable_mul (Lp.memLp v)
    have hb : Integrable (fun ω => β j ω * v ω) (reducedLaw Q) :=
      (Lp.memLp (β j)).integrable_mul (Lp.memLp v)
    rw [integral_congr_ae he, integral_sub (hfv.const_mul _) hb, integral_const_mul]
  change (∫ ω, ((s : ℂ) • f - β j : Lp ℂ 2 (reducedLaw Q)) ω * v ω ∂reducedLaw Q) = _ at hw
  rw [hm, hβ.integral_mul j v V hV] at hw
  simp only [zero_mul, add_zero] at hw
  change (s : ℂ) * (∫ ω, f ω * v ω ∂reducedLaw Q) + _ = _
  dsimp only [unforcedComplexResolventGradient]
  linear_combination hw

/-- The drift pairing in Hermitian form, still for every actual H1 function. -/
theorem IsReducedDriftObservation.inner_eq {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    inner ℂ v (β j) = -(1 / 2 : ℂ) *
      ∫ ω, ∑ k, (ω.1 0 k j : ℂ) * star (V k ω) ∂reducedLaw Q := by
  have ht := hβ.integral_mul j (star v) (fun k => star (V k)) (fun k => (hV k).star)
  have hl : (∫ ω, β j ω * (star v : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) =
      inner ℂ v (β j) := by
    erw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star v] with ω hω
    change (star v : Lp ℂ 2 (reducedLaw Q)) ω = star (v ω) at hω
    simp only [hω, RCLike.inner_apply, Complex.star_def, mul_comm]
  rw [hl] at ht
  convert ht using 2
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun k => Lp.coeFn_star (V k)] with ω hω
  apply Finset.sum_congr rfl
  intro k _
  change _ = (ω.1 0 k j : ℂ) * (star (V k) : Lp ℂ 2 (reducedLaw Q)) ω
  simpa only [Pi.star_apply] using! congrArg ((ω.1 0 k j : ℂ) * ·) (hω k).symm

private theorem norm_column_pairing_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂reducedLaw Q, ∀ k, |ω.1 0 k j| ≤ B) :
    ‖∫ ω, ∑ k, (ω.1 0 k j : ℂ) * star (G k ω) ∂reducedLaw Q‖ ≤
      B * ∑ k, ‖G k‖ := by
  have hC (k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 k j : ℂ)) 2
      (reducedLaw Q) := by
    apply MemLp.of_bound (memLp_reduced_coefficient_complex Q k j).aestronglyMeasurable B
    filter_upwards [hbound] with ω hω
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! hω k
  let C (k : Fin d) := (hC k).toLp (fun ω : FieldPair d => (ω.1 0 k j : ℂ))
  have hnorm (k : Fin d) : ‖C k‖ ≤ B := by
    have hn := Lp.norm_le_of_ae_bound (f := C k) hB (by
      filter_upwards [(hC k).coeFn_toLp, hbound] with ω hc hb
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
      exact hb k)
    simpa only [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one,
      NNReal.coe_one, Real.one_rpow, one_mul] using hn
  have he (k : Fin d) :
      (∫ ω : FieldPair d, (ω.1 0 k j : ℂ) * star (G k ω) ∂reducedLaw Q) = inner ℂ (G k) (C k) := by
    erw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hC k).coeFn_toLp] with ω hω
    simp only [RCLike.inner_apply, Complex.star_def, C, hω, mul_comm]
  have hint (k : Fin d) : Integrable
      (fun ω => (ω.1 0 k j : ℂ) * star (G k ω)) (reducedLaw Q) :=
    (hC k).integrable_mul (Lp.memLp (G k)).star
  rw [integral_finset_sum _ (fun k _ => hint k)]
  calc
    _ ≤ ∑ k, ‖∫ ω, (ω.1 0 k j : ℂ) * star (G k ω) ∂reducedLaw Q‖ := norm_sum_le _ _
    _ ≤ ∑ k, B * ‖G k‖ := Finset.sum_le_sum fun k _ => by
      rw [he k]
      exact (norm_inner_le_norm _ _).trans
        ((mul_le_mul_of_nonneg_left (hnorm k) (norm_nonneg (G k))).trans_eq (mul_comm _ _))
    _ = _ := (Finset.mul_sum _ _ _).symm

private theorem massive_energy_algebra {K B S X F s n : ℝ}
    (hK : 0 < K) (hB : 0 ≤ B) (hS : 0 ≤ S) (hX : 0 ≤ X)
    (hF : 0 ≤ F) (hs : 0 < s) (hn : 0 ≤ n)
    (hc : s * F + K⁻¹ / 2 * X ≤ B / 2 * S) (hcs : S ^ 2 ≤ n * X) :
    X ≤ n * (K * B) ^ 2 ∧ s * F ≤ n * K * B ^ 2 / 2 := by
  have hx : X ≤ K * B * S := by
    have hh := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 2 * K)
    have hi : 2 * K * (K⁻¹ / 2) = 1 := by field_simp
    rw [mul_add, ← mul_assoc (2 * K) (K⁻¹ / 2), hi, one_mul] at hh
    have hh' : 2 * K * s * F + X ≤ K * B * S := by
      nlinarith only [hh]
    exact (le_add_of_nonneg_left (by positivity)).trans hh'
  have hs2 : S ^ 2 ≤ (n * K * B) * S := by
    calc
      S ^ 2 ≤ n * X := hcs
      _ ≤ n * (K * B * S) := mul_le_mul_of_nonneg_left hx hn
      _ = _ := by ring
  have hSbound : S ≤ n * K * B := by
    rcases eq_or_lt_of_le hS with hz | hp
    · rw [← hz]; positivity
    · nlinarith only [hs2, hp]
  constructor
  · calc
      X ≤ K * B * S := hx
      _ ≤ K * B * (n * K * B) := mul_le_mul_of_nonneg_left hSbound (by positivity)
      _ = _ := by ring
  · have hb := mul_le_mul_of_nonneg_left hSbound (by positivity : 0 ≤ B / 2)
    nlinarith only [hc, hb, mul_nonneg (div_nonneg (inv_nonneg.mpr hK.le) (by norm_num : (0 : ℝ) ≤ 2)) hX]

/-- Uniform mass and Euclidean gradient energy for the actual massive drift resolvents.
The one constant is chosen before the law, observation, mass and coordinate. -/
theorem exists_massiveCorrector_energy_bound (d : ℕ) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : StructuralData d) (_hD : D.ellipticity = Λ₀)
      (_hr : D.dependenceRange = r₀)
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → ∀ (i j : Fin d) (s : ℝ) (hs : 0 < s),
        ‖unforcedComplexResolventEuclideanGradient Q i s hs (β j)‖ ^ 2 ≤ C ∧
        s * ‖unforcedComplexResolvent Q i s hs (β j)‖ ^ 2 ≤ C := by
  obtain ⟨B, hB, hbound⟩ := DriftH5.exists_ae_abs_entry_le d Λ₀ r₀
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  refine ⟨1 + (d : ℝ) * (K * B) ^ 2 + (d : ℝ) * K * B ^ 2 / 2, by positivity, ?_⟩
  intro D hD hr Q hQ β hβ i j s hs
  let f := unforcedComplexResolvent Q i s hs (β j)
  let G := unforcedComplexResolventGradient Q i s hs (β j)
  have hG := hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs (β j)
  obtain ⟨H, hH, hcoer⟩ := (unforcedComplexResolvent_spec Q i s hs (β j)).unforced_coercive
  have hHG : H = G := funext fun k => (hH k).unique (hG k)
  rw [hHG] at hcoer
  have hp := hβ.inner_eq j f G hG
  have hboundQ : ∀ᵐ ω ∂reducedLaw Q, ∀ k, |ω.1 0 k j| ≤ B := by
    subst hD hr
    exact (hbound Q).mono fun ω hω k => hω k j
  have hn := norm_column_pairing_le Q j G hB hboundQ
  have hinner : (inner ℂ f (β j)).re ≤ B / 2 * ∑ k, ‖G k‖ := by
    calc
      _ ≤ ‖inner ℂ f (β j)‖ := Complex.re_le_norm _
      _ = (1 / 2 : ℝ) * ‖∫ ω, ∑ k, (ω.1 0 k j : ℂ) * star (G k ω) ∂reducedLaw Q‖ := by
        rw [hp, norm_mul]; norm_num
      _ ≤ _ := by nlinarith only [hn]
  have hc : s * ‖f‖ ^ 2 + K⁻¹ / 2 * (∑ k, ‖G k‖ ^ 2) ≤ B / 2 * ∑ k, ‖G k‖ := by
    have he : (inner ℂ f ((s : ℂ) • f - β j)).re =
        s * ‖f‖ ^ 2 - (inner ℂ f (β j)).re := by
      rw [inner_sub_right, inner_smul_right]
      simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
      have hself : (inner ℂ f f).re = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm
      rw [hself]
    change (Real.exp (2 * D.ellipticity) * D.ellipticity)⁻¹ / 2 *
      (∑ k, ‖G k‖ ^ 2) ≤ -(inner ℂ f ((s : ℂ) • f - β j)).re at hcoer
    have heK : Real.exp (2 * D.ellipticity) * D.ellipticity = K :=
      congrArg (fun t => Real.exp (2 * t) * t) hD
    rw [heK, he] at hcoer
    change K⁻¹ / 2 * (∑ k, ‖G k‖ ^ 2) ≤ _ at hcoer
    linarith only [hcoer, hinner]
  have hcs : (∑ k, ‖G k‖) ^ 2 ≤ (d : ℝ) * ∑ k, ‖G k‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1 : ℝ)) (fun k => ‖G k‖)
  have hb := massive_energy_algebra hK hB
    (Finset.sum_nonneg fun k _ => norm_nonneg (G k))
    (Finset.sum_nonneg fun k _ => sq_nonneg ‖G k‖) (sq_nonneg ‖f‖) hs
    (Nat.cast_nonneg d) hc hcs
  constructor
  · rw [norm_unforcedComplexResolventEuclideanGradient_sq]
    exact hb.1.trans (by
      have hn : 0 ≤ (d : ℝ) * K * B ^ 2 / 2 := by positivity
      linarith only [hn])
  · exact hb.2.trans (by linarith only [show 0 ≤ (d : ℝ) * (K * B) ^ 2 by positivity])

/-- The mass residual tends to zero in actual reduced L2 along every positive mass family.
This uses only the uniform massive energy estimate and asserts no scalar-corrector limit. -/
theorem IsReducedDriftObservation.tendsto_mass_residual {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => (s n : ℂ) • unforcedComplexResolvent Q i (s n) (hs n) (β j))
      l (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_massiveCorrector_energy_bound d D.ellipticity
    D.dependenceRange D.one_le_ellipticity
  have hb (n : ι) :
      ‖(s n : ℂ) • unforcedComplexResolvent Q i (s n) (hs n) (β j)‖ ^ 2 ≤ C * s n := by
    have hh := mul_le_mul_of_nonneg_left (hC D rfl rfl Q hQ β hβ i j (s n) (hs n)).2
      (hs n).le
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hs n)]
    nlinarith only [hh]
  have hsq := squeeze_zero (fun n => sq_nonneg
    ‖(s n : ℂ) • unforcedComplexResolvent Q i (s n) (hs n) (β j)‖) hb
    (by simpa only [mul_zero] using! ht.const_mul C)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hn

/-- Every fixed full H1 test has the correct limiting variational pairing.
This is a statement about the actual resolvent gradients, rather than an assumed weak equation. -/
theorem IsReducedDriftObservation.tendsto_resolvent_gradient_pairing
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0))
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    Tendsto (fun n => ∫ ω, ∑ k, ∑ q, (ω.1 0 k q : ℂ) *
      unforcedComplexResolventGradient Q i (s n) (hs n) (β j) q ω * V k ω ∂reducedLaw Q)
      l (𝓝 (-∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q)) := by
  let F := (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 v
  have hlim := (F.continuous.tendsto 0).comp (hβ.tendsto_mass_residual i j s hs ht)
  have hpair (n : ι) :
      F ((s n : ℂ) • unforcedComplexResolvent Q i (s n) (hs n) (β j)) =
        (s n : ℂ) * (∫ ω, unforcedComplexResolvent Q i (s n) (hs n) (β j) ω * v ω
          ∂reducedLaw Q) := by
    rw [map_smul]
    dsimp only [F]
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    change (s n : ℂ) * (∫ ω, v ω * unforcedComplexResolvent Q i (s n) (hs n) (β j) ω
      ∂reducedLaw Q) = _
    simp_rw [mul_comm (v _)]
  simp only [Function.comp_def, hpair, map_zero] at hlim
  have he (n : ι) : (∫ ω, ∑ k, ∑ q, (ω.1 0 k q : ℂ) *
      unforcedComplexResolventGradient Q i (s n) (hs n) (β j) q ω * V k ω ∂reducedLaw Q) =
      -(∫ ω, ∑ k, (ω.1 0 k j : ℂ) * V k ω ∂reducedLaw Q) -
        2 * ((s n : ℂ) * (∫ ω, unforcedComplexResolvent Q i (s n) (hs n) (β j) ω * v ω
          ∂reducedLaw Q)) := by
    have hw := hβ.resolvent_weak_equation i j (s n) (hs n) v V hV
    linear_combination 2 * hw
  simp_rw [he]
  simpa only [mul_zero, sub_zero] using! tendsto_const_nhds.sub (hlim.const_mul 2)

/-- A real-linear component of an actual complex H1 function, in the existing real domain. -/
def complexHorizontalRealPart {d : ℕ} {μ : Measure (FieldPair d)} {hμ : IsStationary μ}
    {f : Lp ℂ 2 μ} {G : Fin d → Lp ℂ 2 μ}
    (hG : HasComplexHorizontalGradient μ hμ f G) (T : ℂ →L[ℝ] ℝ) :
    horizontalH1 μ hμ :=
  ⟨T.compLpL 2 μ f, ⟨fun k => T.compLpL 2 μ (G k), fun k => (hG k).realMap T⟩⟩

/-- Its real Euclidean gradient has the literal componentwise real-linear observations. -/
theorem complexHorizontalRealPart_gradient_ae {d : ℕ} {μ : Measure (FieldPair d)}
    {hμ : IsStationary μ} {f : Lp ℂ 2 μ} {G : Fin d → Lp ℂ 2 μ}
    (hG : HasComplexHorizontalGradient μ hμ f G) (T : ℂ →L[ℝ] ℝ) :
    ∀ᵐ ω ∂μ, ∀ k, horizontalEuclideanGradient μ hμ
      (complexHorizontalRealPart hG T) ω k = T (G k ω) := by
  have he := horizontalH1Gradient_eq_of_hasHorizontalLpDerivative μ hμ
    (complexHorizontalRealPart hG T) (fun k => T.compLpL 2 μ (G k))
    (fun k => (hG k).realMap T)
  filter_upwards [ae_all_iff.mpr (horizontalEuclideanGradient_coordinates μ hμ
    (complexHorizontalRealPart hG T)), ae_all_iff.mpr fun k => T.coeFn_compLpL (G k)]
    with ω hg ht
  intro k
  rw [hg k, he, ht k]

private theorem real_gradient_inner_coefficient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    inner ℝ v (reducedOriginCoefficientAction Q u) =
      ∫ ω, ∑ j, ∑ k, ω.1 0 j k * u ω k * v ω j ∂reducedLaw Q := by
  erw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [reducedOriginCoefficientAction_coeFn Q u] with ω hω
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  change (∑ j, (reducedOriginCoefficientAction Q u ω) j * v ω j) = _
  simp only [hω, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rfl

private theorem complex_principal_integrable {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (G V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * V j ω)
      (reducedLaw Q) := by
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  have hi := ((Lp.memLp (G k)).integrable_mul (Lp.memLp (V j))).mul_of_top_right
    (memLp_reduced_coefficient_complex Q j k)
  convert hi using 1
  ext ω
  simp only [Pi.mul_apply]
  ring

private theorem realMap_principal_pairing {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {f : Lp ℂ 2 (reducedLaw Q)}
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (T : ℂ →L[ℝ] ℝ)
    (v : horizontalH1 (reducedLaw Q) (reducedLaw_stationary Q)) :
    T (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω *
      (Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
        (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v j)) ω
      ∂reducedLaw Q) =
    inner ℝ (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
      (reducedOriginCoefficientAction Q
        (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (complexHorizontalRealPart hG T))) := by
  rw [← T.integral_comp_comm (complex_principal_integrable Q G _),
    real_gradient_inner_coefficient]
  apply integral_congr_ae
  filter_upwards [complexHorizontalRealPart_gradient_ae hG T,
    ae_all_iff.mpr (horizontalEuclideanGradient_coordinates (reducedLaw Q)
      (reducedLaw_stationary Q) v),
    ae_all_iff.mpr fun j => Complex.ofRealCLM.coeFn_compLpL
      (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v j)] with ω hg hv hc
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [hc j, hg k, hv j]
  change T ((ω.1 0 j k : ℂ) * G k ω * (horizontalH1Gradient
    (reducedLaw Q) (reducedLaw_stationary Q) v j ω : ℝ)) = _
  have ht := T.map_smul (ω.1 0 j k * horizontalH1Gradient
    (reducedLaw Q) (reducedLaw_stationary Q) v j ω) (G k ω)
  change T (((ω.1 0 j k * horizontalH1Gradient
    (reducedLaw Q) (reducedLaw_stationary Q) v j ω : ℝ) : ℂ) * G k ω) = _ at ht
  push_cast at ht
  simp only [smul_eq_mul] at ht
  calc
    _ = T ((ω.1 0 j k : ℂ) * (horizontalH1Gradient
        (reducedLaw Q) (reducedLaw_stationary Q) v j ω : ℝ) * G k ω) :=
      congrArg T (by ring)
    _ = _ := ht.trans (by ring)

private theorem realMap_value_pairing {d : ℕ} {μ : Measure (FieldPair d)}
    (f : Lp ℂ 2 μ) (v : Lp ℝ 2 μ) (T : ℂ →L[ℝ] ℝ) :
    T (∫ ω, f ω * (Complex.ofRealCLM.compLpL 2 μ v) ω ∂μ) =
      inner ℝ (T.compLpL 2 μ f) v := by
  have hi : Integrable (fun ω => f ω * (Complex.ofRealCLM.compLpL 2 μ v) ω) μ :=
    (Lp.memLp f).integrable_mul (Lp.memLp (Complex.ofRealCLM.compLpL 2 μ v))
  rw [← T.integral_comp_comm hi, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL v, T.coeFn_compLpL f] with ω hv hf
  rw [hv, hf]
  change T (f ω * (v ω : ℝ)) = v ω * T (f ω)
  rw [mul_comm (f ω)]
  exact T.map_smul (v ω) (f ω)

private theorem realMap_column_pairing {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (T : ℂ →L[ℝ] ℝ)
    (v : horizontalH1 (reducedLaw Q) (reducedLaw_stationary Q)) :
    T (∫ ω, ∑ k, (ω.1 0 k i : ℂ) *
      (Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
        (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k)) ω
      ∂reducedLaw Q) =
    T 1 * inner ℝ (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
      (reducedOriginCoefficientAction Q (correctorAffineField Q i)) := by
  have hi : Integrable (fun ω => ∑ k, (ω.1 0 k i : ℂ) *
      (Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
        (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k)) ω)
      (reducedLaw Q) := by
    apply integrable_finset_sum
    intro k _
    have h := (Lp.memLp (Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
      (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k))).integrable
      (by norm_num)
    convert h.mul_of_top_left (memLp_reduced_coefficient_complex Q k i) using 1
    ext ω
    exact mul_comm _ _
  erw [← T.integral_comp_comm hi, real_gradient_inner_coefficient, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr (horizontalEuclideanGradient_coordinates (reducedLaw Q)
      (reducedLaw_stationary Q) v), ae_all_iff.mpr fun k => Complex.ofRealCLM.coeFn_compLpL
      (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k),
    Lp.coeFn_const 2 (reducedLaw Q) (correctorUnitVector i)] with ω hv hc he
  have he' : correctorAffineField Q i ω = correctorUnitVector i := he
  erw [he']
  have hsingle (k : Fin d) : (∑ q, ω.1 0 k q * correctorUnitVector i q *
      horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v ω k) =
      ω.1 0 k i * horizontalEuclideanGradient (reducedLaw Q)
        (reducedLaw_stationary Q) v ω k := by
    simp [correctorUnitVector]
  simp_rw [hsingle]
  rw [map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hc k, hv k]
  have h := T.map_smul (ω.1 0 k i * horizontalH1Gradient (reducedLaw Q)
    (reducedLaw_stationary Q) v k ω) (1 : ℂ)
  simpa [Complex.real_smul, mul_comm, mul_left_comm, mul_assoc] using! h

/-- The actual massive equation transported into the existing real Euclidean H1 carrier. -/
theorem IsReducedDriftObservation.resolvent_realMap_equation {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) (T : ℂ →L[ℝ] ℝ)
    (v : horizontalH1 (reducedLaw Q) (reducedLaw_stationary Q)) :
    s * inner ℝ (complexHorizontalRealPart
        (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs (β j)) T).val v.val +
      (1 / 2 : ℝ) * inner ℝ
        (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
        (reducedOriginCoefficientAction Q
          (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q)
            (complexHorizontalRealPart
              (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs (β j)) T))) =
    -(T 1 / 2) * inner ℝ
      (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
      (reducedOriginCoefficientAction Q (correctorAffineField Q j)) := by
  have ht := hβ.resolvent_weak_equation i j s hs
    (Complex.ofRealCLM.compLpL 2 (reducedLaw Q) v.val)
    (fun k => Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
      (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k))
    (fun k => hasComplexHorizontalDerivative_ofReal
      (hasHorizontalLpDerivative_horizontalH1Gradient _ _ v k))
  have h := congrArg T ht
  have hm (a : ℝ) (z : ℂ) : T ((a : ℂ) * z) = a * T z := T.map_smul a z
  rw [map_add, hm] at h
  rw [show (1 / 2 : ℂ) = (((1 / 2 : ℝ)) : ℂ) by norm_num,
    ← Complex.ofReal_neg, hm, hm] at h
  rw [realMap_value_pairing, realMap_principal_pairing Q
    (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs (β j)),
    realMap_column_pairing] at h
  change s * inner ℝ (T.compLpL 2 (reducedLaw Q) _) v.val + _ = _
  convert h using 1
  ring

/-- Coordinatewise complexification on the Euclidean carrier. -/
def euclideanComplexify (d : ℕ) : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin d) where
  toFun x := WithLp.toLp 2 (fun j => (x j : ℂ))
  map_add' x y := by ext j; simp
  map_smul' c x := by ext j; simp
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℂ)).comp
    (continuous_pi fun j => Complex.continuous_ofReal.comp (PiLp.continuous_apply 2 _ j))

/-- Real and imaginary parts on the Euclidean carrier. -/
def euclideanRealMap (d : ℕ) (T : ℂ →L[ℝ] ℝ) :
    EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) where
  toFun x := WithLp.toLp 2 (fun j => T (x j))
  map_add' x y := by ext j; simp
  map_smul' c x := by
    ext j
    change T (c • x j) = c • T (x j)
    exact T.map_smul c (x j)
  cont := (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    (continuous_pi fun j => T.continuous.comp (PiLp.continuous_apply 2 _ j))

theorem euclideanComplexify_re_im (d : ℕ) (x : EuclideanSpace ℂ (Fin d)) :
    euclideanComplexify d (euclideanRealMap d Complex.reCLM x) +
      Complex.I • euclideanComplexify d (euclideanRealMap d Complex.imCLM x) = x := by
  ext j
  change (x j).re + Complex.I * (x j).im = x j
  simpa only [mul_comm Complex.I] using! Complex.re_add_im (x j)

private theorem tendsto_of_coercive_energy_dense {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (V : Submodule ℝ E)
    (hb : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ V, c * ‖x‖ * ‖x‖ ≤ b x x)
    (hsym : ∀ x y, b x y = b y x) {S : Set E} {g : E} (hgv : g ∈ V) (hg : g ∈ closure S)
    {l : Filter ι} (u : ι → E) (huv : ∀ n, u n ∈ V) {C : ℝ} (hu : ∀ n, ‖u n‖ ≤ C)
    (ht : ∀ x ∈ S, Tendsto (fun n => b x (u n)) l (𝓝 (b x g)))
    (he : ∀ n, b (u n) (u n) ≤ b g (u n)) : Tendsto u l (𝓝 g) := by
  let F : ι → E → ℝ := fun n x => b x (u n)
  have hEq : Equicontinuous F :=
    Metric.equicontinuous_of_continuity_modulus (fun t => (‖b‖ * C) * t)
      (by
        simpa only [mul_zero] using!
          (tendsto_id.const_mul (‖b‖ * C) :
            Tendsto (fun t : ℝ => (‖b‖ * C) * t) (𝓝 0) (𝓝 ((‖b‖ * C) * 0)))) F
      (by
        intro x y n
        change ‖b x (u n) - b y (u n)‖ ≤ _
        rw [← ContinuousLinearMap.sub_apply, ← map_sub]
        calc
          ‖b (x - y) (u n)‖ ≤ ‖b‖ * ‖x - y‖ * ‖u n‖ := b.le_opNorm₂ _ _
          _ ≤ ‖b‖ * ‖x - y‖ * C := mul_le_mul_of_nonneg_left (hu n) (by positivity)
          _ = (‖b‖ * C) * dist x y := by rw [dist_eq_norm]; ring)
  have hlim : Tendsto (fun n => b g (u n)) l (𝓝 (b g g)) :=
    (hEq g).tendsto_of_mem_closure
      (((b.flip g).continuous.tendsto g).mono_left nhdsWithin_le_nhds) ht hg
  obtain ⟨c, hc, hcoer⟩ := hb
  have hh (n : ι) : ‖u n - g‖ ^ 2 ≤ (b g g - b g (u n)) / c := by
    have h := hcoer (u n - g) (V.sub_mem (huv n) hgv)
    simp only [map_sub, ContinuousLinearMap.sub_apply] at h
    rw [hsym (u n) g] at h
    apply (le_div_iff₀ hc).mpr
    nlinarith only [h, he n]
  have hsq := squeeze_zero (fun n => sq_nonneg ‖u n - g‖) hh
    (by simpa only [sub_self, zero_div] using! (hlim.const_sub (b g g)).div_const c)
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

/-- A real-linear component of the actual positive massive drift resolvent. -/
def unforcedComplexResolventRealPart {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) (T : ℂ →L[ℝ] ℝ) :
    horizontalH1 (reducedLaw Q) (reducedLaw_stationary Q) :=
  complexHorizontalRealPart
    (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs rhs) T

/-- The existing real Euclidean assembly applied to that actual H1 function. -/
def unforcedComplexResolventRealGradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) (T : ℂ →L[ℝ] ℝ) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) :=
  horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (unforcedComplexResolventRealPart Q i s hs rhs T)

/-- The real component gradient is in the literal canonical potential domain. -/
theorem unforcedComplexResolventRealGradient_mem {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) (T : ℂ →L[ℝ] ℝ) :
    unforcedComplexResolventRealGradient Q i s hs rhs T ∈ correctorPotentialDomain Q :=
  horizontalEuclideanGradient_mem_stationaryPotentialGradients _ _ _

/-- Real-linear component maps commute with the two actual Euclidean gradient assemblies. -/
theorem unforcedComplexResolventRealGradient_eq {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) (T : ℂ →L[ℝ] ℝ) :
    unforcedComplexResolventRealGradient Q i s hs rhs T =
      (euclideanRealMap d T).compLpL 2 (reducedLaw Q)
        (unforcedComplexResolventEuclideanGradient Q i s hs rhs) := by
  apply Lp.ext
  filter_upwards [complexHorizontalRealPart_gradient_ae
      (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs rhs) T,
    (euclideanRealMap d T).coeFn_compLpL
      (unforcedComplexResolventEuclideanGradient Q i s hs rhs),
    unforcedComplexResolventEuclideanGradient_ae Q i s hs rhs] with ω hg hc he
  ext k
  change horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q)
    (complexHorizontalRealPart _ T) ω k = _
  rw [hg k, hc]
  change T _ = T _
  rw [he k]

private def reducedEuclideanEnergy {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ _ _ _).flip (reducedOriginCoefficientAction Q)).comp
    (innerSL ℝ)

private theorem reducedEuclideanEnergy_apply {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    reducedEuclideanEnergy Q u v = inner ℝ u (reducedOriginCoefficientAction Q v) := rfl

private theorem reducedEuclideanEnergy_symmetric {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r)
    (u v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q)) :
    reducedEuclideanEnergy Q u v = reducedEuclideanEnergy Q v u := by
  erw [reducedEuclideanEnergy_apply, reducedEuclideanEnergy_apply,
    reducedOriginCoefficientAction_symmetric, real_inner_comm]
  rfl

private theorem reducedEuclideanEnergy_coercive {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ correctorPotentialDomain Q,
      c * ‖x‖ * ‖x‖ ≤ reducedEuclideanEnergy Q x x := by
  obtain ⟨c, hc, h⟩ := correctorEnergyForm_isCoercive Q
  exact ⟨c, hc, fun x hx => h ⟨x, hx⟩⟩

private theorem corrector_energy_pairing {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (v : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q))
    (hv : v ∈ correctorPotentialDomain Q) :
    reducedEuclideanEnergy Q v (correctorGradient Q j) =
      -inner ℝ v (reducedOriginCoefficientAction Q (correctorAffineField Q j)) := by
  let e : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorAffineField Q j
  let g : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedLaw Q) := correctorGradient Q j
  have h := correctorGradient_variational_domain Q j ⟨v, hv⟩
  change inner ℝ v (reducedOriginCoefficientAction Q (e + g)) = 0 at h
  erw [map_add, inner_add_right] at h
  change inner ℝ v (reducedOriginCoefficientAction Q (correctorGradient Q j)) = _
  linarith only [h]

/-- The actual massive drift resolvent has no imaginary Euclidean gradient. -/
theorem IsReducedDriftObservation.resolvent_imaginary_gradient_eq_zero
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) :
    unforcedComplexResolventRealGradient Q i s hs (β j) Complex.imCLM = 0 := by
  let u := unforcedComplexResolventRealPart Q i s hs (β j) Complex.imCLM
  let G := unforcedComplexResolventRealGradient Q i s hs (β j) Complex.imCLM
  have he := hβ.resolvent_realMap_equation i j s hs Complex.imCLM u
  change s * inner ℝ u.val u.val + (1 / 2 : ℝ) * reducedEuclideanEnergy Q G G = _ at he
  simp only [Complex.imCLM_apply, Complex.one_im, zero_div, neg_zero, zero_mul,
    real_inner_self_eq_norm_sq] at he
  obtain ⟨c, hc, hcoer⟩ := reducedEuclideanEnergy_coercive Q
  have hh := hcoer G (unforcedComplexResolventRealGradient_mem Q i s hs (β j) Complex.imCLM)
  have hnorm : ‖G‖ = 0 := by
    have hn := norm_nonneg G
    have hmass : 0 ≤ s * ‖u.val‖ ^ 2 := mul_nonneg hs.le (sq_nonneg _)
    have he_nonpos : reducedEuclideanEnergy Q G G ≤ 0 := by linarith only [he, hmass]
    have hnonpos := hh.trans he_nonpos
    have hsquare : ‖G‖ * ‖G‖ ≤ 0 :=
      nonpos_of_mul_nonpos_right (by simpa only [mul_assoc] using! hnonpos) hc
    nlinarith only [hsquare, hn]
  exact norm_eq_zero.mp hnorm

/-- Energy comparison against the literal canonical corrector for the real massive gradients. -/
theorem IsReducedDriftObservation.resolvent_real_gradient_energy_le
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) :
    inner ℝ (unforcedComplexResolventRealGradient Q i s hs (β j) Complex.reCLM)
      (reducedOriginCoefficientAction Q
        (unforcedComplexResolventRealGradient Q i s hs (β j) Complex.reCLM)) ≤
    inner ℝ (correctorGradient Q j) (reducedOriginCoefficientAction Q
      (unforcedComplexResolventRealGradient Q i s hs (β j) Complex.reCLM)) := by
  let u := unforcedComplexResolventRealPart Q i s hs (β j) Complex.reCLM
  let G := unforcedComplexResolventRealGradient Q i s hs (β j) Complex.reCLM
  have he := hβ.resolvent_realMap_equation i j s hs Complex.reCLM u
  change s * inner ℝ u.val u.val + (1 / 2 : ℝ) * reducedEuclideanEnergy Q G G = _ at he
  simp only [Complex.reCLM_apply, Complex.one_re, real_inner_self_eq_norm_sq] at he
  change s * ‖u.val‖ ^ 2 + (1 / 2 : ℝ) * reducedEuclideanEnergy Q G G =
    -(1 / 2 : ℝ) * inner ℝ G (reducedOriginCoefficientAction Q (correctorAffineField Q j)) at he
  have hh := corrector_energy_pairing Q j G
    (unforcedComplexResolventRealGradient_mem Q i s hs (β j) Complex.reCLM)
  rw [reducedEuclideanEnergy_symmetric Q G] at hh
  change reducedEuclideanEnergy Q G G ≤ reducedEuclideanEnergy Q (correctorGradient Q j) G
  nlinarith only [he, hh, mul_nonneg hs.le (sq_nonneg ‖u.val‖)]

/-- The real massive gradients converge against every actual real H1 gradient. -/
theorem IsReducedDriftObservation.tendsto_real_resolvent_gradient_pairing
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0))
    (v : horizontalH1 (reducedLaw Q) (reducedLaw_stationary Q)) :
    Tendsto (fun n => inner ℝ
      (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
      (reducedOriginCoefficientAction Q
        (unforcedComplexResolventRealGradient Q i (s n) (hs n) (β j) Complex.reCLM)))
      l (𝓝 (inner ℝ
        (horizontalEuclideanGradient (reducedLaw Q) (reducedLaw_stationary Q) v)
        (reducedOriginCoefficientAction Q (correctorGradient Q j)))) := by
  have hlim := hβ.tendsto_resolvent_gradient_pairing i j s hs ht
    (Complex.ofRealCLM.compLpL 2 (reducedLaw Q) v.val)
    (fun k => Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
      (horizontalH1Gradient (reducedLaw Q) (reducedLaw_stationary Q) v k))
    (fun k => hasComplexHorizontalDerivative_ofReal
      (hasHorizontalLpDerivative_horizontalH1Gradient _ _ v k))
  have h := (Complex.reCLM.continuous.tendsto _).comp hlim
  simp only [Function.comp_def, map_neg] at h
  simp_rw [realMap_principal_pairing Q
    (hasComplexHorizontalGradient_unforcedComplexResolvent Q i (s _) (hs _) (β j))
    Complex.reCLM v] at h
  rw [realMap_column_pairing Q j Complex.reCLM v] at h
  simp only [Complex.reCLM_apply, Complex.one_re, one_mul] at h
  have hc := corrector_energy_pairing Q j _
    (horizontalEuclideanGradient_mem_stationaryPotentialGradients _ _ v)
  rw [← hc] at h
  exact h

/-- Strong real Euclidean L2 convergence of the actual massive gradients to the frozen corrector. -/
theorem IsReducedDriftObservation.tendsto_real_resolvent_gradient
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => unforcedComplexResolventRealGradient Q i (s n) (hs n) (β j)
      Complex.reCLM) l (𝓝 (correctorGradient Q j)) := by
  obtain ⟨C, hC, hbound⟩ := exists_massiveCorrector_energy_bound d D.ellipticity
    D.dependenceRange D.one_le_ellipticity
  have hnorm (n : ι) : ‖unforcedComplexResolventEuclideanGradient Q i (s n) (hs n) (β j)‖ ≤
      Real.sqrt C := by
    have hh := (hbound D rfl rfl Q hQ β hβ i j (s n) (hs n)).1
    nlinarith only [hh, Real.sq_sqrt hC.le, Real.sqrt_nonneg C,
      norm_nonneg (unforcedComplexResolventEuclideanGradient Q i (s n) (hs n) (β j))]
  have hb (n : ι) : ‖unforcedComplexResolventRealGradient Q i (s n) (hs n) (β j)
      Complex.reCLM‖ ≤ ‖(euclideanRealMap d Complex.reCLM).compLpL 2 (reducedLaw Q)‖ *
        Real.sqrt C := by
    rw [unforcedComplexResolventRealGradient_eq]
    exact ((euclideanRealMap d Complex.reCLM).compLpL 2 (reducedLaw Q)).le_opNorm _ |>.trans
      (mul_le_mul_of_nonneg_left (hnorm n) (norm_nonneg _))
  apply tendsto_of_coercive_energy_dense (reducedEuclideanEnergy Q) (correctorPotentialDomain Q)
    (reducedEuclideanEnergy_coercive Q) (reducedEuclideanEnergy_symmetric Q)
    (correctorGradient_mem_potentialDomain Q j)
    (show correctorGradient Q j ∈ closure (Set.range (horizontalEuclideanGradient
      (reducedLaw Q) (reducedLaw_stationary Q))) from
      correctorGradient_mem_potentialDomain Q j)
    (fun n => unforcedComplexResolventRealGradient Q i (s n) (hs n) (β j) Complex.reCLM)
    (fun n => unforcedComplexResolventRealGradient_mem Q i (s n) (hs n) (β j) Complex.reCLM) hb
  · rintro x ⟨v, rfl⟩
    exact hβ.tendsto_real_resolvent_gradient_pairing i j s hs ht v
  · intro n
    exact hβ.resolvent_real_gradient_energy_le i j (s n) (hs n)

private theorem complexEuclideanLp_re_im {d : ℕ} {μ : Measure (FieldPair d)}
    (f : Lp (EuclideanSpace ℂ (Fin d)) 2 μ) :
    (euclideanComplexify d).compLpL 2 μ ((euclideanRealMap d Complex.reCLM).compLpL 2 μ f) +
      Complex.I • (euclideanComplexify d).compLpL 2 μ
        ((euclideanRealMap d Complex.imCLM).compLpL 2 μ f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      ((euclideanComplexify d).compLpL 2 μ ((euclideanRealMap d Complex.reCLM).compLpL 2 μ f))
      (Complex.I • (euclideanComplexify d).compLpL 2 μ
        ((euclideanRealMap d Complex.imCLM).compLpL 2 μ f)),
    Lp.coeFn_smul Complex.I ((euclideanComplexify d).compLpL 2 μ
      ((euclideanRealMap d Complex.imCLM).compLpL 2 μ f)),
    (euclideanComplexify d).coeFn_compLpL ((euclideanRealMap d Complex.reCLM).compLpL 2 μ f),
    (euclideanComplexify d).coeFn_compLpL ((euclideanRealMap d Complex.imCLM).compLpL 2 μ f),
    (euclideanRealMap d Complex.reCLM).coeFn_compLpL f,
    (euclideanRealMap d Complex.imCLM).coeFn_compLpL f] with ω ha hs hr hi hfr hfi
  simp only [Pi.add_apply, Pi.smul_apply] at ha hs
  rw [ha, hs, hr, hi, hfr, hfi]
  exact euclideanComplexify_re_im d (f ω)

/-- The actual massive gradient is the complexification of its real Euclidean gradient. -/
theorem IsReducedDriftObservation.resolvent_gradient_eq_complexify
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) :
    unforcedComplexResolventEuclideanGradient Q i s hs (β j) =
      (euclideanComplexify d).compLpL 2 (reducedLaw Q)
        (unforcedComplexResolventRealGradient Q i s hs (β j) Complex.reCLM) := by
  have h := complexEuclideanLp_re_im (unforcedComplexResolventEuclideanGradient Q i s hs (β j))
  rw [← unforcedComplexResolventRealGradient_eq,
    ← unforcedComplexResolventRealGradient_eq,
    hβ.resolvent_imaginary_gradient_eq_zero i j s hs, map_zero, smul_zero, add_zero] at h
  exact h.symm

/-- Strong Euclidean L2 convergence of the actual massive gradients to the complexified
literal canonical corrector gradient, along every positive mass family tending to zero. -/
theorem IsReducedDriftObservation.tendsto_resolvent_gradient
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (i j : Fin d) {ι : Type*} {l : Filter ι} (s : ι → ℝ) (hs : ∀ n, 0 < s n)
    (ht : Tendsto s l (𝓝 0)) :
    Tendsto (fun n => unforcedComplexResolventEuclideanGradient Q i (s n) (hs n) (β j))
      l (𝓝 ((euclideanComplexify d).compLpL 2 (reducedLaw Q) (correctorGradient Q j))) := by
  simp_rw [hβ.resolvent_gradient_eq_complexify i j]
  exact ((euclideanComplexify d).compLpL 2 (reducedLaw Q)).continuous.tendsto _ |>.comp
    (hβ.tendsto_real_resolvent_gradient i j s hs ht)

end EinsteinFull
