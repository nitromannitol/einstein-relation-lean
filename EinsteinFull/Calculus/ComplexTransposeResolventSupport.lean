import EinsteinFull.Calculus.ComplexForceOperatorSupport
import EinsteinFull.Calculus.ComplexRadialTransposeSupport
import EinsteinFull.Calculus.ComplexTransposeContinuitySupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The full horizontal H1 domain of the bilinear transpose generator

The flipped real Hilbert variational problem constructs the transpose resolvent.
Its complete weak graph equals the full bilinear adjoint graph and the strong
infinitesimal generator graph of the actual transpose semigroup. Dense forward
domain testing proves the vector time-integral identity without assuming any
transpose differentiability or H1 regularity.
-/

open MeasureTheory Filter
open scoped Topology BigOperators NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

private def transposePair {d : ℕ} (Q : Measure (FieldPair d)) (f g : Lp ℂ 2 Q) : ℂ :=
  ∫ ω, f ω * g ω ∂Q

private theorem transposePair_inner {d : ℕ} (Q : Measure (FieldPair d))
    (f g : Lp ℂ 2 Q) :
    transposePair Q f g = inner ℂ (complexL2Conjugation Q f) g :=
  (inner_complexL2Conjugation_eq_integral_mul Q f g).symm

private theorem transposePair_comm {d : ℕ} (Q : Measure (FieldPair d))
    (f g : Lp ℂ 2 Q) : transposePair Q f g = transposePair Q g f :=
  integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)

private theorem transposePair_sub_right {d : ℕ} (Q : Measure (FieldPair d))
    (f g h : Lp ℂ 2 Q) :
    transposePair Q f (g - h) = transposePair Q f g - transposePair Q f h := by
  simp only [transposePair_inner, inner_sub_right]

private theorem transposePair_smul_right {d : ℕ} (Q : Measure (FieldPair d))
    (c : ℂ) (f g : Lp ℂ 2 Q) :
    transposePair Q f (c • g) = c * transposePair Q f g := by
  simp only [transposePair_inner, inner_smul_right]

private theorem transposePair_sub_left {d : ℕ} (Q : Measure (FieldPair d))
    (f g h : Lp ℂ 2 Q) :
    transposePair Q (f - g) h = transposePair Q f h - transposePair Q g h := by
  rw [transposePair_comm Q (f-g), transposePair_sub_right]
  rw [transposePair_comm Q h f, transposePair_comm Q h g]

private theorem transposePair_smul_left {d : ℕ} (Q : Measure (FieldPair d))
    (c : ℂ) (f g : Lp ℂ 2 Q) :
    transposePair Q (c • f) g = c * transposePair Q f g := by
  rw [transposePair_comm Q (c • f), transposePair_smul_right, transposePair_comm Q g f]

/-- The entire transposed H1 weak graph is onto at every real shift above the
structural quadratic force shift. -/
theorem exists_forced_complexTransposeGenerator_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃ f : Lp ℂ 2 (reducedLaw Q),
      IsComplexTransposeGeneratorPair Q i ζ f ((s : ℂ) • f - rhs) := by
  obtain ⟨f, Gf, hGf, hw⟩ := exists_forced_complexTranspose_variational Q i ζ s hs rhs
  refine ⟨f, Gf, hGf, ?_⟩
  intro v Gv hv
  have ht := hw v Gv hv
  change transposePair (reducedLaw Q) ((s : ℂ) • f - rhs) v = _
  rw [transposePair_sub_left, transposePair_smul_left]
  unfold transposePair
  linear_combination ht

/-- Every full weak transpose pair has the exact bilinear resolvent identity,
with the actual forward resolvent and arbitrary L2 data. -/
theorem IsComplexTransposeGeneratorPair.resolvent_duality
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (s : ℝ) (hs : complexForceShift d Λ₀ ζ < s) (u : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, f ω * u ω ∂reducedLaw Q) =
      ∫ ω, ((s : ℂ) • f - g : Lp ℂ 2 (reducedLaw Q)) ω *
        forcedComplexResolvent Q i ζ s hs u ω ∂reducedLaw Q := by
  have ht := hfg.bilinear_duality (forcedComplexResolvent_spec Q i ζ s hs u)
  change transposePair (reducedLaw Q) g (forcedComplexResolvent Q i ζ s hs u) =
    transposePair (reducedLaw Q) f ((s : ℂ) • forcedComplexResolvent Q i ζ s hs u - u) at ht
  change transposePair (reducedLaw Q) f u =
    transposePair (reducedLaw Q) ((s : ℂ) • f - g) (forcedComplexResolvent Q i ζ s hs u)
  simp only [transposePair_sub_right, transposePair_smul_right] at ht
  simp only [transposePair_sub_left, transposePair_smul_left]
  linear_combination ht

/-- The full transposed weak graph is exactly recovered from the actual
bilinear transpose of one forward resolvent. No adjoint regularity is assumed. -/
theorem isComplexTransposeGeneratorPair_iff_resolvent {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (f g : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeGeneratorPair Q i ζ f g ↔
      complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)
        ((s : ℂ) • f - g) = f := by
  have hid {f g : Lp ℂ 2 (reducedLaw Q)}
      (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
      complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)
        ((s : ℂ) • f - g) = f := by
    apply ext_inner_left ℂ
    intro u
    have ht := hfg.resolvent_duality s hs (complexL2Conjugation (reducedLaw Q) u)
    change transposePair (reducedLaw Q) f (complexL2Conjugation (reducedLaw Q) u) =
      transposePair (reducedLaw Q) ((s : ℂ) • f - g)
        (forcedComplexResolvent Q i ζ s hs (complexL2Conjugation (reducedLaw Q) u)) at ht
    rw [transposePair_comm (reducedLaw Q) f,
      transposePair_comm (reducedLaw Q) ((s : ℂ) • f - g)] at ht
    have hp := integral_complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)
      (complexL2Conjugation (reducedLaw Q) u) ((s : ℂ) • f - g)
    change transposePair (reducedLaw Q) _ _ = transposePair (reducedLaw Q) _ _ at hp
    have he := ht.trans hp
    simpa only [transposePair_inner, complexL2Conjugation_involutive] using he.symm
  constructor
  · exact hid
  · intro he
    obtain ⟨h, hh⟩ := exists_forced_complexTransposeGenerator_resolvent Q i ζ s hs
      ((s : ℂ) • f - g)
    have ht := hid hh
    simp only [sub_sub_cancel] at ht
    rw [he] at ht
    subst h
    simpa only [sub_sub_cancel] using hh

/-- The actual bounded bilinear transpose of the forward resolvent solves the
complete transpose weak H1 equation. This proves its H1 regularity. -/
theorem complexL2Transpose_forcedComplexResolvent_spec {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeGeneratorPair Q i ζ
      (complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs)
      ((s : ℂ) • complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs - rhs) := by
  obtain ⟨f, hf⟩ := exists_forced_complexTransposeGenerator_resolvent Q i ζ s hs rhs
  have he := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs f _).mp hf
  simp only [sub_sub_cancel] at he
  simpa only [he] using hf

/-- The actual transpose resolvent obeys the same shifted L2 norm bound. -/
theorem norm_complexL2Transpose_forcedComplexResolvent_apply_le
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ‖complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs) rhs‖ ≤
      (s - complexForceShift d Λ₀ ζ)⁻¹ * ‖rhs‖ := by
  apply ((complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)).le_opNorm rhs).trans
  rw [norm_complexL2Transpose]
  exact mul_le_mul_of_nonneg_right (norm_forcedComplexResolvent_le Q i ζ s hs) (norm_nonneg _)

/-- The shifted transpose weak equation has exactly one solution. -/
theorem existsUnique_forced_complexTransposeGenerator_resolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) (s : ℝ)
    (hs : complexForceShift d Λ₀ ζ < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∃! f : Lp ℂ 2 (reducedLaw Q),
      IsComplexTransposeGeneratorPair Q i ζ f ((s : ℂ) • f - rhs) := by
  refine ⟨_, complexL2Transpose_forcedComplexResolvent_spec Q i ζ s hs rhs, ?_⟩
  intro f hf
  have he := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs f _).mp hf
  simpa only [sub_sub_cancel] using he.symm

/-- The complete transpose weak H1 graph equals the full bilinear adjoint graph
of the forward weak generator. The reverse inclusion constructs the H1
regularity from the transpose resolvent, rather than assuming it. -/
theorem isComplexTransposeGeneratorPair_iff_bilinear_adjoint
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    IsComplexTransposeGeneratorPair Q i ζ f g ↔
      ∀ (u v : Lp ℂ 2 (reducedLaw Q)), IsComplexGeneratorPair Q i ζ u v →
        (∫ ω, g ω * u ω ∂reducedLaw Q) = ∫ ω, f ω * v ω ∂reducedLaw Q := by
  constructor
  · exact fun h _ _ huv => h.bilinear_duality huv
  · intro h
    let s := complexForceShift d Λ₀ ζ + 1
    have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
    apply (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs f g).mpr
    apply ext_inner_left ℂ
    intro w
    let u := complexL2Conjugation (reducedLaw Q) w
    have ht := h _ _ (forcedComplexResolvent_spec Q i ζ s hs u)
    change transposePair (reducedLaw Q) g (forcedComplexResolvent Q i ζ s hs u) =
      transposePair (reducedLaw Q) f ((s : ℂ) • forcedComplexResolvent Q i ζ s hs u - u) at ht
    simp only [transposePair_sub_right, transposePair_smul_right] at ht
    have hr : transposePair (reducedLaw Q) u f =
        transposePair (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs u)
          ((s : ℂ) • f - g) := by
      rw [transposePair_comm (reducedLaw Q) u,
        transposePair_sub_right, transposePair_smul_right,
        transposePair_comm (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs u) f,
        transposePair_comm (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs u) g]
      linear_combination ht
    have hp := integral_complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)
      u ((s : ℂ) • f - g)
    change transposePair (reducedLaw Q) _ _ = transposePair (reducedLaw Q) _ _ at hp
    have he := hr.trans hp
    simpa only [transposePair_inner, u, complexL2Conjugation_involutive] using he.symm

/-- The actual full transpose weak graph is closed in the product L2 topology. -/
theorem isClosed_complexTransposeGenerator_graph {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    IsClosed {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexTransposeGeneratorPair Q i ζ p.1 p.2} := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
  have he : {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexTransposeGeneratorPair Q i ζ p.1 p.2} =
      {p | complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)
        ((s : ℂ) • p.1 - p.2) = p.1} := by
    ext p
    exact isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs p.1 p.2
  rw [he]
  exact isClosed_eq ((complexL2Transpose (reducedLaw Q) (forcedComplexResolvent Q i ζ s hs)).continuous.comp
    ((continuous_fst.const_smul (s : ℂ)).sub continuous_snd)) continuous_fst

/-- Every strong derivative pair of the actual transpose semigroup belongs to
its full H1 weak graph, with the differentiated coefficient-column drift. -/
theorem IsComplexTransposeSemigroup.generatorPair_of_tendsto_slope
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g)) :
    IsComplexTransposeGeneratorPair Q i ζ f g := by
  apply (isComplexTransposeGeneratorPair_iff_bilinear_adjoint Q i ζ f g).mpr
  intro u v huv
  have hfwd := (hP.2.2.2 u v).mpr huv
  have hl := ((complexL2Conjugation (reducedLaw Q)).continuous.tendsto g).comp hfg
  have hl' := hl.inner (𝕜 := ℂ)
    (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => u) (𝓝[>] (0 : ℝ≥0)) (𝓝 u))
  have hr := (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => complexL2Conjugation (reducedLaw Q) f)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (complexL2Conjugation (reducedLaw Q) f))).inner (𝕜 := ℂ) hfwd
  have he (t : ℝ≥0) :
      transposePair (reducedLaw Q) (((t : ℝ) : ℂ)⁻¹ • (T t f - f)) u =
        transposePair (reducedLaw Q) f (((t : ℝ) : ℂ)⁻¹ • (P t u - u)) := by
    rw [transposePair_smul_left, transposePair_sub_left,
      transposePair_smul_right, transposePair_sub_right]
    have hp := hT t u f
    change transposePair (reducedLaw Q) (P t u) f = transposePair (reducedLaw Q) u (T t f) at hp
    rw [transposePair_comm (reducedLaw Q) (T t f) u,
      ← hp, transposePair_comm (reducedLaw Q) (P t u) f]
  have hl'' : Tendsto (fun t : ℝ≥0 => transposePair (reducedLaw Q) f
      (((t : ℝ) : ℂ)⁻¹ • (P t u - u))) (𝓝[>] (0 : ℝ≥0))
      (𝓝 (transposePair (reducedLaw Q) g u)) := by
    simpa only [Function.comp_def, ← transposePair_inner, he] using hl'
  have hr' : Tendsto (fun t : ℝ≥0 => transposePair (reducedLaw Q) f
      (((t : ℝ) : ℂ)⁻¹ • (P t u - u))) (𝓝[>] (0 : ℝ≥0))
      (𝓝 (transposePair (reducedLaw Q) f v)) := by
    simpa only [← transposePair_inner] using hr
  exact tendsto_nhds_unique hl'' hr'

/-- The transpose orbit of every full weak-domain datum satisfies the vector
fundamental theorem of calculus. Density is used only for testing equality;
no differentiability of the transpose orbit is presupposed. -/
theorem IsComplexTransposeSemigroup.integral_orbit_eq_sub
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (t : ℝ≥0) :
    (∫ r in (0 : ℝ)..(t : ℝ), T r.toNNReal g) = T t f - f := by
  have hcont : Continuous (fun r : ℝ => T r.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hpair (u v : Lp ℂ 2 (reducedLaw Q)) (huv : IsComplexGeneratorPair Q i ζ u v) :
      transposePair (reducedLaw Q) u (∫ r in (0 : ℝ)..(t : ℝ), T r.toNNReal g) =
        transposePair (reducedLaw Q) u (T t f - f) := by
    let L := innerSL ℂ (complexL2Conjugation (reducedLaw Q) f)
    let U := innerSL ℂ (complexL2Conjugation (reducedLaw Q) u)
    have hF : Continuous (fun r : ℝ => transposePair (reducedLaw Q) f (P r.toNNReal u)) := by
      simp only [transposePair_inner]
      exact L.continuous.comp ((hP.2.2.1 u).comp continuous_real_toNNReal)
    have hD : Continuous (fun r : ℝ => transposePair (reducedLaw Q) u (T r.toNNReal g)) := by
      simp only [transposePair_inner]
      exact U.continuous.comp hcont
    have hd (r : ℝ) (hr : 0 < r) :
        HasDerivWithinAt (fun s : ℝ => transposePair (reducedLaw Q) f (P s.toNNReal u))
          (transposePair (reducedLaw Q) u (T r.toNNReal g)) (Set.Ioi r) r := by
      have hh := ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt r
        (hP.hasDerivWithinAt_orbit huv r hr.le)).mono Set.Ioi_subset_Ici_self
      have he := hfg.bilinear_duality (hP.map_generator huv r.toNNReal)
      have hp := hT r.toNNReal u g
      change transposePair (reducedLaw Q) g (P r.toNNReal u) =
        transposePair (reducedLaw Q) f (P r.toNNReal v) at he
      change transposePair (reducedLaw Q) (P r.toNNReal u) g =
        transposePair (reducedLaw Q) u (T r.toNNReal g) at hp
      rw [transposePair_comm (reducedLaw Q) g] at he
      have hdEq : transposePair (reducedLaw Q) f (P r.toNNReal v) =
          transposePair (reducedLaw Q) u (T r.toNNReal g) := he.symm.trans hp
      change HasDerivWithinAt (fun s : ℝ => inner ℂ (complexL2Conjugation (reducedLaw Q) f) (P s.toNNReal u))
        (inner ℂ (complexL2Conjugation (reducedLaw Q) f) (P r.toNNReal v)) (Set.Ioi r) r at hh
      simp only [← transposePair_inner] at hh
      change HasDerivWithinAt (fun s : ℝ => transposePair (reducedLaw Q) f (P s.toNNReal u))
        (transposePair (reducedLaw Q) f (P r.toNNReal v)) (Set.Ioi r) r at hh
      rw [hdEq] at hh
      exact hh
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.property
      hF.continuousOn (fun r hr => hd r hr.1) (hD.intervalIntegrable 0 t)
    have hp := hT t u f
    change transposePair (reducedLaw Q) (P t u) f = transposePair (reducedLaw Q) u (T t f) at hp
    rw [transposePair_comm (reducedLaw Q) (P t u)] at hp
    simp only [Real.toNNReal_zero, hP.1, ContinuousLinearMap.id_apply] at hi
    have htcoe : ((t : ℝ).toNNReal) = t := Real.toNNReal_coe
    change (∫ y : ℝ in 0..(t : ℝ), transposePair (reducedLaw Q) u (T y.toNNReal g)) =
      transposePair (reducedLaw Q) f (P ((t : ℝ).toNNReal) u) - transposePair (reducedLaw Q) f u at hi
    rw [htcoe] at hi
    rw [hp, transposePair_comm (reducedLaw Q) f u] at hi
    rw [transposePair_sub_right]
    calc
      _ = ∫ r in (0 : ℝ)..(t : ℝ), transposePair (reducedLaw Q) u (T r.toNNReal g) := by
        simpa only [transposePair_inner, U, innerSL_apply_apply] using!
          (U.intervalIntegral_comp_comm (μ := volume) (hcont.intervalIntegrable (μ := volume) 0 (t : ℝ))).symm
      _ = _ := hi
  have hc₁ : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      transposePair (reducedLaw Q) u (∫ r in (0 : ℝ)..(t : ℝ), T r.toNNReal g)) := by
    simp only [transposePair_inner]
    exact (complexL2Conjugation (reducedLaw Q)).continuous.inner continuous_const
  have hc₂ : Continuous (fun u : Lp ℂ 2 (reducedLaw Q) =>
      transposePair (reducedLaw Q) u (T t f - f)) := by
    simp only [transposePair_inner]
    exact (complexL2Conjugation (reducedLaw Q)).continuous.inner continuous_const
  have he := Continuous.ext_on (dense_complexGenerator_domain Q i ζ) hc₁ hc₂
    (by rintro u ⟨v, huv⟩; exact hpair u v huv)
  apply ext_inner_left ℂ
  intro w
  have hw := congrFun he (complexL2Conjugation (reducedLaw Q) w)
  simpa only [transposePair_inner, complexL2Conjugation_involutive] using hw

private theorem tendsto_transpose_coe_right_zero :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  exact ⟨(NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin⟩

/-- Every full weak transpose pair is a strong derivative pair of the actual
transpose semigroup. Its vector time-integral identity supplies the derivative. -/
theorem IsComplexTransposeGeneratorPair.tendsto_transposeSemigroup_slope
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  have hcont : Continuous (fun r : ℝ => T r.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hzero : T 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (reducedLaw Q)) := by
    have he := congrFun hT.eq_complexL2Transpose 0
    simpa only [hP.1, complexL2Transpose_id] using he
  have hd := intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable 0 0)
    hcont.stronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt
  have hs := hd.tendsto_slope_zero_right.comp tendsto_transpose_coe_right_zero
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, Real.toNNReal_zero,
    hzero, ContinuousLinearMap.id_apply] at hs
  have he (t : ℝ≥0) : (∫ r in (0 : ℝ)..(t : ℝ), T r.toNNReal g) = T t f - f :=
    hT.integral_orbit_eq_sub hP hfg t
  simpa only [Function.comp_def, he, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv] using! hs

/-- The full strong infinitesimal generator of every actual bilinear transpose
family is precisely the full horizontal H1 transpose weak graph. -/
theorem IsComplexTransposeSemigroup.tendsto_slope_iff
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (T t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ IsComplexTransposeGeneratorPair Q i ζ f g :=
  ⟨hT.generatorPair_of_tendsto_slope hP, fun hfg => hfg.tendsto_transposeSemigroup_slope hP hT⟩

/-- Full transpose weak-domain pairs are transported by the actual transpose
semigroup, with no regularity assumption on the transported datum. -/
theorem IsComplexTransposeSemigroup.map_generator
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (t : ℝ≥0) : IsComplexTransposeGeneratorPair Q i ζ (T t f) (T t g) := by
  apply (isComplexTransposeGeneratorPair_iff_bilinear_adjoint Q i ζ _ _).mpr
  intro u v huv
  have h₁ := hT t u g
  have h₂ := hT t v f
  have h₃ := hfg.bilinear_duality (hP.map_generator huv t)
  change transposePair (reducedLaw Q) (P t u) g = transposePair (reducedLaw Q) u (T t g) at h₁
  change transposePair (reducedLaw Q) (P t v) f = transposePair (reducedLaw Q) v (T t f) at h₂
  change transposePair (reducedLaw Q) g (P t u) = transposePair (reducedLaw Q) f (P t v) at h₃
  rw [transposePair_comm (reducedLaw Q) (P t u), transposePair_comm (reducedLaw Q) u] at h₁
  rw [transposePair_comm (reducedLaw Q) (P t v), transposePair_comm (reducedLaw Q) v] at h₂
  exact h₁.symm.trans (h₃.trans h₂)

end EinsteinFull
