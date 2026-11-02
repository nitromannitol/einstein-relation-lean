import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ComplexHorizontalGradient
import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Correctors.HorizontalCoreLpApproximation

/-!
# Density of the actual complex horizontal H1 domain

Real and imaginary parts are approximated by the actual real horizontal core.
Complexification commutes with translations and their strong derivatives, so
these approximations belong to the full complex horizontal H1 domain. This is
L2 value density, with no assertion of gradient convergence or graph density.

The real approximation and core membership proofs are reused from the pinned
blueprint revision `7748a8e9000034825873768d309be8915ae53b07`.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinFull

open EinsteinRelation

/-- The strong complex horizontal derivative of zero is zero. -/
theorem HasComplexHorizontalDerivative.zero {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (i : Fin d) : HasComplexHorizontalDerivative Q hQ i 0 0 := by
  unfold HasComplexHorizontalDerivative
  simpa only [map_zero, sub_self, smul_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Lp ℂ 2 Q))
      (𝓝[≠] (0 : ℝ)) (𝓝 0))

/-- The full complex strong horizontal derivative relation is additive. -/
theorem HasComplexHorizontalDerivative.add {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f f' g g' : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f f')
    (hg : HasComplexHorizontalDerivative Q hQ i g g') :
    HasComplexHorizontalDerivative Q hQ i (f + g) (f' + g') := by
  unfold HasComplexHorizontalDerivative at *
  simpa only [map_add, add_sub_add_comm, smul_add] using hf.add hg

/-- The full complex strong horizontal derivative relation is complex linear. -/
theorem HasComplexHorizontalDerivative.smul {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℂ 2 Q}
    (hf : HasComplexHorizontalDerivative Q hQ i f g) (c : ℂ) :
    HasComplexHorizontalDerivative Q hQ i (c • f) (c • g) := by
  unfold HasComplexHorizontalDerivative at *
  have heq : (fun t : ℝ => (t : ℂ)⁻¹ •
      (complexTranslation Q hQ (t • unitVector i) (c • f) - c • f)) =
      (fun t : ℝ => c • ((t : ℂ)⁻¹ •
        (complexTranslation Q hQ (t • unitVector i) f - f))) := by
    funext t
    rw [map_smul, ← smul_sub, smul_comm]
  rw [heq]
  exact hf.const_smul c

/-- Complexification of real L2 classes commutes with the actual translations. -/
theorem complexTranslation_ofReal {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℝ 2 Q) :
    complexTranslation Q hQ x (Complex.ofRealCLM.compLpL 2 Q f) =
      Complex.ofRealCLM.compLpL 2 Q (translationLp Q hQ x f) := by
  apply Lp.ext
  have hm := measurePreserving_translate Q hQ x
  have hc := hm.quasiMeasurePreserving.ae (Complex.ofRealCLM.coeFn_compLpL f)
  filter_upwards [coeFn_complexTranslation Q hQ x (Complex.ofRealCLM.compLpL 2 Q f),
    Complex.ofRealCLM.coeFn_compLpL (translationLp Q hQ x f),
    coeFn_translationLp Q hQ x f, hc] with ω ha hb hd he
  change (Complex.ofRealCLM.compLpL 2 Q f) (translate x ω) =
    Complex.ofRealCLM (f (translate x ω)) at he
  rw [ha, he, hb, hd]

/-- A real strong horizontal derivative is also a complex strong derivative. -/
theorem hasComplexHorizontalDerivative_ofReal {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℝ 2 Q}
    (hf : HasHorizontalLpDerivative Q hQ i f g) :
    HasComplexHorizontalDerivative Q hQ i
      (Complex.ofRealCLM.compLpL 2 Q f) (Complex.ofRealCLM.compLpL 2 Q g) := by
  unfold HasComplexHorizontalDerivative
  have h := ((Complex.ofRealCLM.compLpL 2 Q).continuous.tendsto g).comp hf
  change Tendsto (fun t : ℝ => Complex.ofRealCLM.compLpL 2 Q
    (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)))
    (𝓝[≠] (0 : ℝ)) (𝓝 (Complex.ofRealCLM.compLpL 2 Q g)) at h
  simp only [← Complex.ofReal_inv, Complex.coe_smul]
  simp only [map_smul, map_sub, ← complexTranslation_ofReal] at h
  exact h

private theorem complexLp_re_im {d : ℕ} (Q : Measure (FieldPair d)) (f : Lp ℂ 2 Q) :
    Complex.ofRealCLM.compLpL 2 Q (Complex.reCLM.compLpL 2 Q f) +
      Complex.I • Complex.ofRealCLM.compLpL 2 Q (Complex.imCLM.compLpL 2 Q f) = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add
      (Complex.ofRealCLM.compLpL 2 Q (Complex.reCLM.compLpL 2 Q f))
      (Complex.I • Complex.ofRealCLM.compLpL 2 Q (Complex.imCLM.compLpL 2 Q f)),
    Lp.coeFn_smul Complex.I (Complex.ofRealCLM.compLpL 2 Q (Complex.imCLM.compLpL 2 Q f)),
    Complex.ofRealCLM.coeFn_compLpL (Complex.reCLM.compLpL 2 Q f),
    Complex.ofRealCLM.coeFn_compLpL (Complex.imCLM.compLpL 2 Q f),
    Complex.reCLM.coeFn_compLpL f, Complex.imCLM.coeFn_compLpL f]
    with ω ha hb hc hd he hh
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha hb
  rw [ha, hb, hc, hd, he, hh]
  simpa only [Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    mul_comm Complex.I] using Complex.re_add_im (f ω)

/-- Every complex L2 class is a value limit of classes in the actual full horizontal H1 domain. -/
theorem exists_complexHorizontalGradient_approximation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℂ 2 Q) :
    ∃ u : ℕ → Lp ℂ 2 Q,
      (∀ n, ∃ G : Fin d → Lp ℂ 2 Q, HasComplexHorizontalGradient Q hQ (u n) G) ∧
      Tendsto u atTop (𝓝 f) := by
  let C := Complex.ofRealCLM.compLpL 2 Q
  obtain ⟨F, hHorF, hF, htF⟩ := Correctors.exists_horizontalCore_Lp_approximation Q hQ
    (Complex.reCLM.compLpL 2 Q f)
  obtain ⟨H, hHorH, hH, htH⟩ := Correctors.exists_horizontalCore_Lp_approximation Q hQ
    (Complex.imCLM.compLpL 2 Q f)
  refine ⟨fun n => C ((hF n).toLp (F n)) + Complex.I • C ((hH n).toLp (H n)), ?_, ?_⟩
  · intro n
    obtain ⟨GF, hGF⟩ := (hHorF n).mem_horizontalH1 Q hQ
    obtain ⟨GH, hGH⟩ := (hHorH n).mem_horizontalH1 Q hQ
    exact ⟨fun i => C (GF i) + Complex.I • C (GH i),
      fun i => (hasComplexHorizontalDerivative_ofReal (hGF i)).add
        ((hasComplexHorizontalDerivative_ofReal (hGH i)).smul Complex.I)⟩
  · have hlim := ((C.continuous.tendsto _).comp htF).add
      (((C.continuous.tendsto _).comp htH).const_smul Complex.I)
    simp only [Function.comp_def, C, complexLp_re_im] at hlim
    exact hlim

/-- The values in the full complex horizontal H1 domain are dense in complex L2. -/
theorem dense_complexHorizontalH1 {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) :
    Dense {f : Lp ℂ 2 Q | ∃ G : Fin d → Lp ℂ 2 Q,
      HasComplexHorizontalGradient Q hQ f G} := by
  intro f
  obtain ⟨u, hu, ht⟩ := exists_complexHorizontalGradient_approximation Q hQ f
  exact mem_closure_of_tendsto ht (Eventually.of_forall hu)

end EinsteinFull
