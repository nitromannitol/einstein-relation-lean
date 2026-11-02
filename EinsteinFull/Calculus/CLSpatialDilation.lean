import EinsteinFull.Calculus.CLTimeRescale
import EinsteinFull.Calculus.C8VelocityTransport
import EinsteinFull.Frozen.SmoothWithBounds
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Spatial dilation of physical evolutions. For `c ≠ 0` the map `f ↦ f (c • ·)`
sends the physical weak graph of `(a, ζ)` to that of `(a (c • ·), c ζ)` with the
generator multiplied by `c²`, so conjugation turns the evolution at time
`c² s` into the dilated evolution at time `s`. With `c = 4 / ‖ζ‖` this moves
large forces to force norm four. -/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ}

theorem clr_dil_mp (c : ℝ) (hc : c ≠ 0) :
    MeasurePreserving (fun x : Vec d => c • x) volume
      (ENNReal.ofReal |(c ^ d)⁻¹| • (volume : Measure (Vec d))) := by
  refine ⟨measurable_const_smul c, ?_⟩
  have h := Measure.map_addHaar_smul (volume : Measure (Vec d)) hc
  simpa only [Module.finrank_fin_fun] using h

theorem clr_dil_qmp (c : ℝ) (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : Vec d => c • x) volume volume :=
  ⟨measurable_const_smul c, by
    rw [(clr_dil_mp c hc).map_eq]; exact Measure.smul_absolutelyContinuous⟩

theorem clr_dil_memLp (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    MemLp (fun x => f (c • x)) 2 volume :=
  ((Lp.memLp f).smul_measure ENNReal.ofReal_ne_top).comp_measurePreserving (clr_dil_mp c hc)

/-- The integral under spatial dilation. -/
theorem clr_integral_dil (c : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : Vec d → E) :
    (∫ x, g (c • x)) = |(c ^ d)⁻¹| • ∫ y, g y := by
  have h := Measure.integral_comp_smul (volume : Measure (Vec d)) g c
  simpa only [Module.finrank_fin_fun] using h

theorem clr_dil_norm (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖(clr_dil_memLp c hc f).toLp _‖ = Real.sqrt |(c ^ d)⁻¹| * ‖f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  have h1 : eLpNorm (fun x => f (c • x)) 2 volume =
      eLpNorm (f : Vec d → ℂ) 2 (ENNReal.ofReal |(c ^ d)⁻¹| • volume) :=
    eLpNorm_comp_measurePreserving ((Lp.aestronglyMeasurable f).smul_measure _) (clr_dil_mp c hc)
  rw [h1, eLpNorm_smul_measure_of_ne_top (by norm_num) _ _ (Lp.aestronglyMeasurable f),
    smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal (abs_nonneg _),
    Real.sqrt_eq_rpow]
  norm_num

/-- Spatial dilation `f ↦ f (c • ·)` on `L²(dx)`. -/
noncomputable def clrDil (c : ℝ) (hc : c ≠ 0) :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  LinearMap.mkContinuous
    { toFun := fun f => (clr_dil_memLp c hc f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ ((clr_dil_qmp c hc).ae_eq_comp (Lp.coeFn_add f g))
      map_smul' := fun r f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ ((clr_dil_qmp c hc).ae_eq_comp (Lp.coeFn_smul r f)) }
    (Real.sqrt |(c ^ d)⁻¹|) (fun f => (clr_dil_norm c hc f).le)

theorem clrDil_coe (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    (clrDil c hc f : Vec d → ℂ) =ᵐ[volume] fun x => f (c • x) :=
  MemLp.coeFn_toLp (clr_dil_memLp c hc f)

theorem clrDil_norm (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖clrDil c hc f‖ = Real.sqrt |(c ^ d)⁻¹| * ‖f‖ :=
  clr_dil_norm c hc f

/-- An `L²` class is the dilation of its inverse dilation, read at `c • x`. -/
theorem clr_dil_inv_comp (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    (fun x => (clrDil c⁻¹ (inv_ne_zero hc) f) (c • x)) =ᵐ[volume] (f : Vec d → ℂ) := by
  have h := (clr_dil_qmp c hc).ae_eq_comp (clrDil_coe c⁻¹ (inv_ne_zero hc) f)
  refine h.trans (Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem clrDil_comp_inv (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    clrDil c hc (clrDil c⁻¹ (inv_ne_zero hc) f) = f := by
  apply Lp.ext
  exact (clrDil_coe c hc _).trans (clr_dil_inv_comp c hc f)

theorem clrDil_inv_comp (c : ℝ) (hc : c ≠ 0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    clrDil c⁻¹ (inv_ne_zero hc) (clrDil c hc f) = f := by
  have h := clrDil_comp_inv c⁻¹ (inv_ne_zero hc) f
  simp only [inv_inv] at h
  convert h using 2

/-- Change of variables for an integrand that is a.e. a dilation. -/
theorem clr_integral_of_ae_dil (c : ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : Vec d → E) {F : Vec d → E} (hF : F =ᵐ[volume] fun x => h (c • x)) :
    (∫ x, F x) = |(c ^ d)⁻¹| • ∫ y, h y := by
  rw [integral_congr_ae hF, clr_integral_dil]

/-- The bilinear `dx` pairing under dilation. -/
theorem clr_dil_pairing (c : ℝ) (hc : c ≠ 0) (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, clrDil c hc u x * v x) =
      ((|(c ^ d)⁻¹| : ℝ) : ℂ) * ∫ y, u y * clrDil c⁻¹ (inv_ne_zero hc) v y := by
  have hF : (fun x => clrDil c hc u x * v x) =ᵐ[volume]
      fun x => (fun y => u y * clrDil c⁻¹ (inv_ne_zero hc) v y) (c • x) := by
    filter_upwards [clrDil_coe c hc u, clr_dil_inv_comp c hc v] with x h1 h2
    rw [h1, h2]
  rw [clr_integral_of_ae_dil c (fun y => u y * clrDil c⁻¹ (inv_ne_zero hc) v y) hF,
    Complex.real_smul]

/-- Weak coordinate derivatives under dilation. -/
theorem clr_weak_dil (c : ℝ) (hc : c ≠ 0) (j : Fin d) {f g F Gc : Vec d → ℝ}
    (h : HasWeakPartialDerivative Set.univ j f g)
    (hF : F =ᵐ[volume] fun x => f (c • x)) (hG : Gc =ᵐ[volume] fun x => c * g (c • x))
    (hFl : LocallyIntegrable F volume) (hGl : LocallyIntegrable Gc volume) :
    HasWeakPartialDerivative Set.univ j F Gc := by
  refine ⟨hFl.locallyIntegrableOn _, hGl.locallyIntegrableOn _, fun φ hφ => ?_⟩
  obtain ⟨hφs, hφc, -⟩ := hφ
  set ψ : Vec d → ℝ := fun y => φ (c⁻¹ • y) with hψdef
  have hψ : IsSpatialTest Set.univ ψ :=
    ⟨smooth_comp_spatialScale hφs c⁻¹, compactSupport_comp_spatialScale hφc (inv_ne_zero hc),
      Set.subset_univ _⟩
  have key := h.2.2 ψ hψ
  simp only [Measure.restrict_univ] at key ⊢
  have hdψ (y : Vec d) : coordinateDerivative j ψ y =
      c⁻¹ * coordinateDerivative j φ (c⁻¹ • y) :=
    coordinateDerivative_comp_spatialScale c⁻¹ j φ y
  have hL : (∫ x, F x * coordinateDerivative j φ x) =
      |(c ^ d)⁻¹| * (c * ∫ y, f y * coordinateDerivative j ψ y) := by
    have hae : (fun x => F x * coordinateDerivative j φ x) =ᵐ[volume]
        fun x => (fun y => c * (f y * coordinateDerivative j ψ y)) (c • x) := by
      filter_upwards [hF] with x hx
      rw [hx, hdψ, smul_smul, inv_mul_cancel₀ hc, one_smul]
      field_simp
    rw [clr_integral_of_ae_dil c (fun y => c * (f y * coordinateDerivative j ψ y)) hae,
      smul_eq_mul, integral_const_mul]
  have hR : (∫ x, Gc x * φ x) = |(c ^ d)⁻¹| * (c * ∫ y, g y * ψ y) := by
    have hae : (fun x => Gc x * φ x) =ᵐ[volume]
        fun x => (fun y => c * (g y * ψ y)) (c • x) := by
      filter_upwards [hG] with x hx
      rw [hx, hψdef]
      simp only [smul_smul, inv_mul_cancel₀ hc, one_smul]
      ring
    rw [clr_integral_of_ae_dil c (fun y => c * (g y * ψ y)) hae, smul_eq_mul,
      integral_const_mul]
  rw [hL, hR, key]
  ring

theorem clr_locallyIntegrable_re (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    LocallyIntegrable (fun x => (u x).re) volume :=
  ((Lp.memLp u).re).locallyIntegrable (by norm_num)

theorem clr_locallyIntegrable_im (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    LocallyIntegrable (fun x => (u x).im) volume :=
  ((Lp.memLp u).im).locallyIntegrable (by norm_num)

/-- The physical H1 graph under dilation. -/
theorem clr_H1_dil (c : ℝ) (hc : c ≠ 0) {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (h : IsPhysicalH1Graph volume (Or.inl rfl) f G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (clrDil c hc f)
      (fun j => (c : ℂ) • clrDil c hc (G j)) := by
  refine ⟨fun j => ?_, fun j => ?_⟩
  · refine clr_weak_dil c hc j (h.1 j) ?_ ?_ (clr_locallyIntegrable_re _)
      (clr_locallyIntegrable_re _)
    · filter_upwards [clrDil_coe c hc f] with x hx
      rw [hx]
    · filter_upwards [Lp.coeFn_smul (c : ℂ) (clrDil c hc (G j)), clrDil_coe c hc (G j)]
        with x h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul, Complex.re_ofReal_mul]
  · refine clr_weak_dil c hc j (h.2 j) ?_ ?_ (clr_locallyIntegrable_im _)
      (clr_locallyIntegrable_im _)
    · filter_upwards [clrDil_coe c hc f] with x hx
      rw [hx]
    · filter_upwards [Lp.coeFn_smul (c : ℂ) (clrDil c hc (G j)), clrDil_coe c hc (G j)]
        with x h1 h2
      rw [h1, Pi.smul_apply, h2, smul_eq_mul, Complex.im_ofReal_mul]


/-- Pointwise relations of the dilated test pair, almost everywhere. -/
theorem clr_dil_test_ae (c : ℝ) (hc : c ≠ 0) (Gf : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (v : Lp ℂ 2 (volume : Measure (Vec d))) (Gv : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∀ k, ((c : ℂ) • clrDil c hc (Gf k)) x = (c : ℂ) * Gf k (c • x)) ∧
      (∀ j, Gv j x = clrDil c⁻¹ (inv_ne_zero hc) (Gv j) (c • x)) ∧
      (∀ j, (((c⁻¹ : ℝ) : ℂ) • clrDil c⁻¹ (inv_ne_zero hc) (Gv j)) (c • x) =
        ((c⁻¹ : ℝ) : ℂ) * clrDil c⁻¹ (inv_ne_zero hc) (Gv j) (c • x)) ∧
      v x = clrDil c⁻¹ (inv_ne_zero hc) v (c • x) := by
  have h1 : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ k, ((c : ℂ) • clrDil c hc (Gf k)) x = (c : ℂ) * Gf k (c • x) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_smul (c : ℂ) (clrDil c hc (Gf k)), clrDil_coe c hc (Gf k)]
      with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  have h2 : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ j, Gv j x = clrDil c⁻¹ (inv_ne_zero hc) (Gv j) (c • x) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [clr_dil_inv_comp c hc (Gv j)] with x hx
    exact hx.symm
  have h3 : ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ j, (((c⁻¹ : ℝ) : ℂ) • clrDil c⁻¹ (inv_ne_zero hc) (Gv j)) (c • x) =
        ((c⁻¹ : ℝ) : ℂ) * clrDil c⁻¹ (inv_ne_zero hc) (Gv j) (c • x) := by
    rw [ae_all_iff]
    intro j
    filter_upwards [(clr_dil_qmp c hc).ae_eq_comp
      (Lp.coeFn_smul ((c⁻¹ : ℝ) : ℂ) (clrDil c⁻¹ (inv_ne_zero hc) (Gv j)))] with x hx
    simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] using hx
  filter_upwards [h1, h2, h3, clr_dil_inv_comp c hc v] with x hx1 hx2 hx3 hx4
  exact ⟨hx1, hx2, hx3, hx4.symm⟩

/-- The physical forward weak graph under dilation. -/
theorem clr_generatorPair_dil (c : ℝ) (hc : c ≠ 0) (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))} (h : IsPhysicalComplexGeneratorPair a i ζ f g) :
    IsPhysicalComplexGeneratorPair (fun x => a (c • x)) i ((c : ℂ) * ζ) (clrDil c hc f)
      ((c : ℂ) ^ 2 • clrDil c hc g) := by
  obtain ⟨Gf, hGf, hw⟩ := h
  refine ⟨fun k => (c : ℂ) • clrDil c hc (Gf k), clr_H1_dil c hc hGf, fun v Gv hv => ?_⟩
  set Gv' : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun j => ((c⁻¹ : ℝ) : ℂ) • clrDil c⁻¹ (inv_ne_zero hc) (Gv j)
  have key := hw (clrDil c⁻¹ (inv_ne_zero hc) v) Gv' (clr_H1_dil c⁻¹ (inv_ne_zero hc) hv)
  set k : ℂ := ((|(c ^ d)⁻¹| : ℝ) : ℂ)
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hT := clr_dil_test_ae c hc Gf v Gv
  have hL : (∫ x, ((c : ℂ) ^ 2 • clrDil c hc g) x * v x) =
      k * ((c : ℂ) ^ 2 * ∫ y, g y * clrDil c⁻¹ (inv_ne_zero hc) v y) := by
    have hae : (fun x => ((c : ℂ) ^ 2 • clrDil c hc g) x * v x) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) ^ 2 * (g y * clrDil c⁻¹ (inv_ne_zero hc) v y)) (c • x) := by
      filter_upwards [Lp.coeFn_smul ((c : ℂ) ^ 2) (clrDil c hc g), clrDil_coe c hc g, hT]
        with x h1 h2 h3
      rw [h1, Pi.smul_apply, h2, h3.2.2.2, smul_eq_mul, mul_assoc]
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) ^ 2 * (g y * clrDil c⁻¹ (inv_ne_zero hc) v y)) hae, integral_const_mul, Complex.real_smul]
  have h1 : (∫ x, ∑ j, ∑ l, ((a (c • x) j l : ℝ) : ℂ) *
        ((fun k => (c : ℂ) • clrDil c hc (Gf k)) l) x * Gv j x) =
      k * ((c : ℂ) ^ 2 * ∫ y, ∑ j, ∑ l, ((a y j l : ℝ) : ℂ) * Gf l y * Gv' j y) := by
    have hae : (fun x => ∑ j, ∑ l, ((a (c • x) j l : ℝ) : ℂ) *
          ((fun k => (c : ℂ) • clrDil c hc (Gf k)) l) x * Gv j x) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) ^ 2 *
          ∑ j, ∑ l, ((a y j l : ℝ) : ℂ) * Gf l y * Gv' j y) (c • x) := by
      filter_upwards [hT] with x hx
      simp only [hx.1, hx.2.1, Gv', hx.2.2.1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.ofReal_inv]
      field_simp
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) ^ 2 *
      ∑ j, ∑ l, ((a y j l : ℝ) : ℂ) * Gf l y * Gv' j y) hae, integral_const_mul, Complex.real_smul]
  have h2 : (∫ x, (∑ j, ((a (c • x) j i : ℝ) : ℂ) *
        ((fun k => (c : ℂ) • clrDil c hc (Gf k)) j) x) * v x) =
      k * ((c : ℂ) * ∫ y, (∑ j, ((a y j i : ℝ) : ℂ) * Gf j y) * clrDil c⁻¹ (inv_ne_zero hc) v y) := by
    have hae : (fun x => (∑ j, ((a (c • x) j i : ℝ) : ℂ) *
          ((fun k => (c : ℂ) • clrDil c hc (Gf k)) j) x) * v x) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) *
          ((∑ j, ((a y j i : ℝ) : ℂ) * Gf j y) * clrDil c⁻¹ (inv_ne_zero hc) v y)) (c • x) := by
      filter_upwards [hT] with x hx
      simp only [hx.1, hx.2.2.2, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) *
      ((∑ j, ((a y j i : ℝ) : ℂ) * Gf j y) * clrDil c⁻¹ (inv_ne_zero hc) v y)) hae, integral_const_mul, Complex.real_smul]
  rw [hL, h1, h2, key]
  ring


/-- The physical transpose weak graph under dilation. -/
theorem clr_transposeGeneratorPair_dil (c : ℝ) (hc : c ≠ 0) (a : Vec d → Mat d) (i : Fin d)
    (ζ : ℂ) {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (h : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    IsPhysicalComplexTransposeGeneratorPair (fun x => a (c • x)) i ((c : ℂ) * ζ)
      (clrDil c hc f) ((c : ℂ) ^ 2 • clrDil c hc g) := by
  obtain ⟨Gf, hGf, hw⟩ := h
  refine ⟨fun k => (c : ℂ) • clrDil c hc (Gf k), clr_H1_dil c hc hGf, fun v Gv hv => ?_⟩
  set Gv' : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun j => ((c⁻¹ : ℝ) : ℂ) • clrDil c⁻¹ (inv_ne_zero hc) (Gv j)
  have key := hw (clrDil c⁻¹ (inv_ne_zero hc) v) Gv' (clr_H1_dil c⁻¹ (inv_ne_zero hc) hv)
  set k : ℂ := ((|(c ^ d)⁻¹| : ℝ) : ℂ)
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  have hT := clr_dil_test_ae c hc Gf v Gv
  have hL : (∫ x, ((c : ℂ) ^ 2 • clrDil c hc g) x * v x) =
      k * ((c : ℂ) ^ 2 * ∫ y, g y * clrDil c⁻¹ (inv_ne_zero hc) v y) := by
    have hae : (fun x => ((c : ℂ) ^ 2 • clrDil c hc g) x * v x) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) ^ 2 * (g y * clrDil c⁻¹ (inv_ne_zero hc) v y)) (c • x) := by
      filter_upwards [Lp.coeFn_smul ((c : ℂ) ^ 2) (clrDil c hc g), clrDil_coe c hc g, hT]
        with x h1 h2 h3
      rw [h1, Pi.smul_apply, h2, h3.2.2.2, smul_eq_mul, mul_assoc]
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) ^ 2 *
      (g y * clrDil c⁻¹ (inv_ne_zero hc) v y)) hae, integral_const_mul, Complex.real_smul]
  have h1 : (∫ x, ∑ j, ∑ l, ((a (c • x) l j : ℝ) : ℂ) *
        ((fun k => (c : ℂ) • clrDil c hc (Gf k)) l) x * Gv j x) =
      k * ((c : ℂ) ^ 2 * ∫ y, ∑ j, ∑ l, ((a y l j : ℝ) : ℂ) * Gf l y * Gv' j y) := by
    have hae : (fun x => ∑ j, ∑ l, ((a (c • x) l j : ℝ) : ℂ) *
          ((fun k => (c : ℂ) • clrDil c hc (Gf k)) l) x * Gv j x) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) ^ 2 *
          ∑ j, ∑ l, ((a y l j : ℝ) : ℂ) * Gf l y * Gv' j y) (c • x) := by
      filter_upwards [hT] with x hx
      simp only [hx.1, hx.2.1, Gv', hx.2.2.1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.ofReal_inv]
      field_simp
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) ^ 2 *
      ∑ j, ∑ l, ((a y l j : ℝ) : ℂ) * Gf l y * Gv' j y) hae, integral_const_mul,
      Complex.real_smul]
  have h2 : (∫ x, clrDil c hc f x * (∑ j, ((a (c • x) j i : ℝ) : ℂ) * Gv j x)) =
      k * ((c : ℂ) * ∫ y, f y * (∑ j, ((a y j i : ℝ) : ℂ) * Gv' j y)) := by
    have hae : (fun x => clrDil c hc f x * (∑ j, ((a (c • x) j i : ℝ) : ℂ) * Gv j x)) =ᵐ[volume]
        fun x => (fun y => (c : ℂ) *
          (f y * (∑ j, ((a y j i : ℝ) : ℂ) * Gv' j y))) (c • x) := by
      filter_upwards [hT, clrDil_coe c hc f] with x hx hf
      simp only [hf, hx.2.1, Gv', hx.2.2.1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.ofReal_inv]
      field_simp
    rw [clr_integral_of_ae_dil c (fun y => (c : ℂ) *
      (f y * (∑ j, ((a y j i : ℝ) : ℂ) * Gv' j y))) hae, integral_const_mul, Complex.real_smul]
  rw [hL, h1, h2, key]
  ring


theorem clr_dil_field_inv (c : ℝ) (hc : c ≠ 0) (a : Vec d → Mat d) :
    (fun x : Vec d => (fun y : Vec d => a (c • y)) (c⁻¹ • x)) = a := by
  funext x
  simp only [smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem clr_dil_force_inv (c : ℝ) (hc : c ≠ 0) (ζ : ℂ) :
    ((c⁻¹ : ℝ) : ℂ) * ((c : ℂ) * ζ) = ζ := by
  have hcC : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc
  rw [Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hcC, one_mul]

theorem clr_dil_data (c : ℝ) (hc : c ≠ 0) (h : Lp ℂ 2 (volume : Measure (Vec d))) :
    (c : ℂ) ^ 2 • clrDil c hc (((c : ℂ) ^ 2)⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h) = h := by
  have hcC : (c : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hc)
  rw [map_smul, clrDil_comp_inv, smul_smul, mul_inv_cancel₀ hcC, one_smul]

theorem clr_dil_data_inv (c : ℝ) (hc : c ≠ 0) (h : Lp ℂ 2 (volume : Measure (Vec d))) :
    ((c⁻¹ : ℝ) : ℂ) ^ 2 • clrDil c⁻¹ (inv_ne_zero hc) h =
      ((c : ℂ) ^ 2)⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h := by
  rw [Complex.ofReal_inv, inv_pow]

/-- The forward weak graph of the dilated field, read through the inverse dilation. -/
theorem clr_generatorPair_dil_iff (c : ℝ) (hc : c ≠ 0) (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (F h : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexGeneratorPair a i ζ (clrDil c⁻¹ (inv_ne_zero hc) F)
        (((c : ℂ) ^ 2)⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h) ↔
      IsPhysicalComplexGeneratorPair (fun x => a (c • x)) i ((c : ℂ) * ζ) F h := by
  constructor
  · intro hg
    have := clr_generatorPair_dil c hc a i ζ hg
    rwa [clrDil_comp_inv, clr_dil_data] at this
  · intro hg
    have := clr_generatorPair_dil c⁻¹ (inv_ne_zero hc) _ i _ hg
    rwa [clr_dil_field_inv c hc, clr_dil_force_inv c hc, clr_dil_data_inv] at this

/-- The transpose weak graph of the dilated field, read through the inverse dilation. -/
theorem clr_transposeGeneratorPair_dil_iff (c : ℝ) (hc : c ≠ 0) (a : Vec d → Mat d) (i : Fin d)
    (ζ : ℂ) (F h : Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ (clrDil c⁻¹ (inv_ne_zero hc) F)
        (((c : ℂ) ^ 2)⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h) ↔
      IsPhysicalComplexTransposeGeneratorPair (fun x => a (c • x)) i ((c : ℂ) * ζ) F h := by
  constructor
  · intro hg
    have := clr_transposeGeneratorPair_dil c hc a i ζ hg
    rwa [clrDil_comp_inv, clr_dil_data] at this
  · intro hg
    have := clr_transposeGeneratorPair_dil c⁻¹ (inv_ne_zero hc) _ i _ hg
    rwa [clr_dil_field_inv c hc, clr_dil_force_inv c hc, clr_dil_data_inv] at this

theorem clr_tendsto_dil_iff (c : ℝ) (hc : c ≠ 0) {l : Filter ℝ≥0}
    (φ : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d))) (h : Lp ℂ 2 (volume : Measure (Vec d))) :
    Tendsto (fun s => clrDil c hc (φ s)) l (𝓝 h) ↔
      Tendsto φ l (𝓝 (clrDil c⁻¹ (inv_ne_zero hc) h)) := by
  constructor
  · intro ht
    have := ((clrDil c⁻¹ (inv_ne_zero hc)).continuous.tendsto h).comp ht
    simpa only [Function.comp_def, clrDil_inv_comp] using this
  · intro ht
    have := ((clrDil c hc).continuous.tendsto _).comp ht
    simpa only [Function.comp_def, clrDil_comp_inv] using this

/-- The evolution conjugated by dilation. -/
noncomputable def clrConj (c : ℝ) (hc : c ≠ 0)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)) :=
  (clrDil c hc).comp ((P s).comp (clrDil c⁻¹ (inv_ne_zero hc)))

theorem clrConj_apply (c : ℝ) (hc : c ≠ 0)
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (s : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    clrConj c hc P s f = clrDil c hc (P s (clrDil c⁻¹ (inv_ne_zero hc) f)) := rfl

/-- Conjugating physical evolutions by a dilation whose weak graphs correspond. -/
theorem clr_conj_physical {b b' : Vec d → Mat d} {i : Fin d} {ζ ζ' : ℂ} (c : ℝ) (hc : c ≠ 0)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup b i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup b i ζ P Pdag)
    (hgen : ∀ F h, IsPhysicalComplexGeneratorPair b i ζ (clrDil c⁻¹ (inv_ne_zero hc) F)
        (clrDil c⁻¹ (inv_ne_zero hc) h) ↔ IsPhysicalComplexGeneratorPair b' i ζ' F h)
    (htgen : ∀ F h, IsPhysicalComplexTransposeGeneratorPair b i ζ
        (clrDil c⁻¹ (inv_ne_zero hc) F) (clrDil c⁻¹ (inv_ne_zero hc) h) ↔
        IsPhysicalComplexTransposeGeneratorPair b' i ζ' F h) :
    IsPhysicalComplexSemigroup b' i ζ' (clrConj c hc P) ∧
      IsPhysicalComplexTransposeSemigroup b' i ζ' (clrConj c hc P) (clrConj c hc Pdag) := by
  have hdiff (T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (F : Lp ℂ 2 (volume : Measure (Vec d))) (s : ℝ≥0) :
      ((s : ℝ) : ℂ)⁻¹ • (clrConj c hc T s F - F) = clrDil c hc
        (((s : ℝ) : ℂ)⁻¹ • (T s (clrDil c⁻¹ (inv_ne_zero hc) F) -
          clrDil c⁻¹ (inv_ne_zero hc) F)) := by
    rw [map_smul, map_sub, clrDil_comp_inv, clrConj_apply]
  have hid (T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
      (h0 : T 0 = ContinuousLinearMap.id ℂ _) :
      clrConj c hc T 0 = ContinuousLinearMap.id ℂ _ := by
    ext1 f
    rw [clrConj_apply, h0, ContinuousLinearMap.id_apply, clrDil_comp_inv,
      ContinuousLinearMap.id_apply]
  have hmul (T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
      (h0 : ∀ s t : ℝ≥0, T (s + t) = (T s).comp (T t)) (s t : ℝ≥0) :
      clrConj c hc T (s + t) = (clrConj c hc T s).comp (clrConj c hc T t) := by
    ext1 f
    rw [ContinuousLinearMap.comp_apply, clrConj_apply, clrConj_apply, clrConj_apply,
      clrDil_inv_comp, h0, ContinuousLinearMap.comp_apply]
  have hcont (T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
      (h0 : ∀ f, Continuous (fun t : ℝ≥0 => T t f)) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
      Continuous (fun t : ℝ≥0 => clrConj c hc T t f) :=
    (clrDil c hc).continuous.comp (h0 _)
  refine ⟨⟨hid P hP.1, hmul P hP.2.1, hcont P hP.2.2.1, fun F h => ?_⟩,
    ⟨hid Pdag hPdag.1, hmul Pdag hPdag.2.1, hcont Pdag hPdag.2.2.1, fun F h => ?_, ?_⟩⟩
  · simp only [hdiff]
    rw [clr_tendsto_dil_iff, hP.2.2.2, hgen]
  · simp only [hdiff]
    rw [clr_tendsto_dil_iff, hPdag.2.2.2.1, htgen]
  · intro t F H
    have h1 := clr_dil_pairing c hc (P t (clrDil c⁻¹ (inv_ne_zero hc) F)) H
    have h2 := clr_dil_pairing c hc (Pdag t (clrDil c⁻¹ (inv_ne_zero hc) H)) F
    have e1 : (∫ x, F x * clrDil c hc (Pdag t (clrDil c⁻¹ (inv_ne_zero hc) H)) x) =
        ∫ x, clrDil c hc (Pdag t (clrDil c⁻¹ (inv_ne_zero hc) H)) x * F x := by
      congr 1; funext x; ring
    rw [clrConj_apply, clrConj_apply, h1, hPdag.2.2.2.2 t, e1, h2]
    congr 2; funext y; ring

/-- Spatial dilation of a physical forward evolution and its transpose: the
dilated field with force `c ζ` is evolved at time `s` by the conjugate of the
original evolution at time `c² s`. -/
theorem clr_physical_dilation {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ} (c : ℝ) (hc : c ≠ 0)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hPdag : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag) :
    IsPhysicalComplexSemigroup (fun x => a (c • x)) i ((c : ℂ) * ζ)
        (clrConj c hc (fun s => P (⟨c ^ 2, sq_nonneg c⟩ * s))) ∧
      IsPhysicalComplexTransposeSemigroup (fun x => a (c • x)) i ((c : ℂ) * ζ)
        (clrConj c hc (fun s => P (⟨c ^ 2, sq_nonneg c⟩ * s)))
        (clrConj c hc (fun s => Pdag (⟨c ^ 2, sq_nonneg c⟩ * s))) := by
  have hκ : (0 : ℝ≥0) < ⟨c ^ 2, sq_nonneg c⟩ :=
    NNReal.coe_pos.mp (show (0 : ℝ) < c ^ 2 by positivity)
  obtain ⟨hP', hPdag'⟩ := clr_physical_time_rescale _ hκ hP hPdag
  have hκr : ((⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) : ℝ) ≠ 0 := show c ^ 2 ≠ 0 by positivity
  have hsc (h : Lp ℂ 2 (volume : Measure (Vec d))) :
      ((((⟨c ^ 2, sq_nonneg c⟩ : ℝ≥0) : ℝ) : ℂ))⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h =
        ((c : ℂ) ^ 2)⁻¹ • clrDil c⁻¹ (inv_ne_zero hc) h := by
    show (((c ^ 2 : ℝ) : ℂ))⁻¹ • _ = _
    rw [Complex.ofReal_pow]
  refine clr_conj_physical c hc hP' hPdag' (fun F h => ?_) (fun F h => ?_)
  · refine (clr_generatorPair_smul_iff a i ζ _ hκr _ _).trans ?_
    rw [hsc]
    exact clr_generatorPair_dil_iff c hc a i ζ F h
  · refine (clr_transposeGeneratorPair_smul_iff a i ζ _ hκr _ _).trans ?_
    rw [hsc]
    exact clr_transposeGeneratorPair_dil_iff c hc a i ζ F h


theorem clr_iteratedFDeriv_comp_smul {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (c : ℝ)
    (k : ℕ) (x : Vec d) (v : Fin k → Vec d) :
    iteratedFDeriv ℝ k (fun y => f (c • y)) x v = c ^ k * iteratedFDeriv ℝ k f (c • x) v := by
  have h := (c • ContinuousLinearMap.id ℝ (Vec d)).iteratedFDeriv_comp_right hf x (i := k)
    (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have he : (fun y => f (c • y)) = f ∘ (c • ContinuousLinearMap.id ℝ (Vec d)) := by
    funext y; simp
  rw [he, h, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const, smul_eq_mul]

theorem clr_isElliptic_scale {Λ : ℝ} (c : ℝ) {ω : FieldPair d} (h : IsElliptic Λ ω.1) :
    IsElliptic Λ (scaleEnvironment c ω).1 := fun x => h (c • x)

/-- Contraction (`|c| ≤ 1`) keeps every smooth-bound constant. -/
theorem clr_isSmoothWithBounds_scale {M : ℕ → ℝ} {c : ℝ} (hc : |c| ≤ 1) {ω : FieldPair d}
    (h : IsSmoothWithBounds M ω) : IsSmoothWithBounds M (scaleEnvironment c ω) := by
  obtain ⟨⟨hm, hp⟩, hb⟩ := h
  refine ⟨⟨fun j k => (hm j k).comp (contDiff_const_smul c),
    hp.comp (contDiff_const_smul c)⟩, fun k hk => ?_⟩
  obtain ⟨A, B, hA, hB, hAB, hA', hB'⟩ := hb k hk
  have hck : |c| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg c) hc
  refine ⟨A, B, hA, hB, hAB, fun x v ξ => ?_, fun x v => ?_⟩
  · have hmv : Matrix.mulVec
        (fun i j => iteratedFDeriv ℝ k (fun y => (scaleEnvironment c ω).1 y i j) x v) ξ =
        c ^ k • Matrix.mulVec
          (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) (c • x) v) ξ := by
      ext i
      simp only [scaleEnvironment_matrix, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [clr_iteratedFDeriv_comp_smul (hm i j) c k x v]
      ring
    rw [hmv, TimeChange.euclideanNorm_smul, abs_pow]
    have h0 := hA' (c • x) v ξ
    have hn : 0 ≤ A * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ := le_trans
      (Real.sqrt_nonneg _) h0
    calc |c| ^ k * euclideanNorm (Matrix.mulVec
          (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) (c • x) v) ξ)
        ≤ 1 * (A * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ) :=
          mul_le_mul hck h0 (Real.sqrt_nonneg _) zero_le_one
      _ = _ := one_mul _
  · have heq : iteratedFDeriv ℝ k (fun y => (scaleEnvironment c ω).2 y) x v =
        c ^ k * iteratedFDeriv ℝ k (fun y => ω.2 y) (c • x) v := by
      simp only [scaleEnvironment_potential]
      exact clr_iteratedFDeriv_comp_smul hp c k x v
    rw [heq, abs_mul, abs_pow]
    calc |c| ^ k * |iteratedFDeriv ℝ k (fun y => ω.2 y) (c • x) v|
        ≤ 1 * (B * ∏ j, euclideanNorm (v j)) :=
          mul_le_mul hck (hB' (c • x) v) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _


end EinsteinFull
