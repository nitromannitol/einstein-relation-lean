import EinsteinFull.Calculus.ParabolicBridgeSliceL2
import EinsteinFull.Calculus.ParabolicBridgeC1Ext

/-!
# The weak identity for the delayed mollification

`MolData` packages the distributional data `(V, G)` (a function and its weak spatial gradient with
a time derivative given by the divergence of `A G`) on the open cylinder `U × (b, e)`.  We prove
that the delayed mollification satisfies the weak equation for `C¹` test functions supported in
`U × (b + 3ε, e)`.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

/-- Distributional data on `U × (b, e)`. -/
structure MolData {d : ℕ} (U : Set (Vec d)) (b e Lam : ℝ) (A : Vec d → Mat d)
    (V : Vec d × ℝ → ℝ) (G : Fin d → Vec d × ℝ → ℝ) : Prop where
  isOpen : IsOpen U
  finite : volume U < ⊤
  measV : Measurable V
  measG : ∀ k, Measurable (G k)
  memV : MemLp V 2 (volume.restrict (U ×ˢ Ioo b e))
  memG : ∀ k, MemLp (G k) 2 (volume.restrict (U ×ˢ Ioo b e))
  ell : ∀ y, IsEllipticMatrix 1 Lam (A y)
  measA : ∀ j k, Measurable fun y => A y j k
  H1 : ∀ φ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ U ×ˢ Ioo b e → ∀ j : Fin d,
    ∫ z in U ×ˢ Ioo b e, V z * fderiv ℝ φ z (basisVec j, 0) =
      -∫ z in U ×ˢ Ioo b e, G j z * φ z
  H2 : ∀ φ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    tsupport φ ⊆ U ×ˢ Ioo b e →
    ∫ z in U ×ˢ Ioo b e, V z * fderiv ℝ φ z (0, 1) =
      ∫ z in U ×ˢ Ioo b e, ∑ j : Fin d,
        (∑ k : Fin d, A z.1 j k * G k z) * fderiv ℝ φ z (basisVec j, 0)

/-- The flux `(A G)_j`. -/
def Hs {d : ℕ} (A : Vec d → Mat d) (G : Fin d → Vec d × ℝ → ℝ) (j : Fin d)
    (z : Vec d × ℝ) : ℝ := ∑ k : Fin d, A z.1 j k * G k z

theorem indicator_memLp {d : ℕ} {S : Set (Vec d × ℝ)} (hS : MeasurableSet S)
    {F : Vec d × ℝ → ℝ} (hF : MemLp F 2 (volume.restrict S)) :
    MemLp (S.indicator F) 2 volume :=
  (memLp_indicator_iff_restrict hS).mpr hF

theorem indicator_integrable {d : ℕ} {S : Set (Vec d × ℝ)} (hS : MeasurableSet S)
    (hfin : volume S < ⊤) {F : Vec d × ℝ → ℝ} (hF : MemLp F 2 (volume.restrict S)) :
    Integrable (S.indicator F) volume := by
  rw [integrable_indicator_iff hS]
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  exact hF.integrable one_le_two

theorem integral_indicator_mul {d : ℕ} {S : Set (Vec d × ℝ)} (hS : MeasurableSet S)
    (a F g : Vec d × ℝ → ℝ) :
    ∫ z, (a z * S.indicator F z) * g z = ∫ z in S, (a z * F z) * g z := by
  rw [← integral_indicator hS]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ S
  · simp [Set.indicator_of_mem hz]
  · simp [Set.indicator_of_notMem hz]

theorem MolS_const_mul_fst {d : ℕ} {ε : ℝ} {hε : 0 < ε} (c : Vec d → ℝ)
    (F : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    MolS ε hε (fun w => c w.1 * F w) z = c z.1 * MolS ε hε F z := by
  rw [MolS_eq, MolS_eq, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  show ker ε hε (z.2 - s) * (c z.1 * F (z.1, s)) = c z.1 * (ker ε hε (z.2 - s) * F (z.1, s))
  ring

theorem fderiv_apply_continuous {d : ℕ} (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (v : Vec d × ℝ) : Continuous fun w => fderiv ℝ φ w v :=
  (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem fderiv_apply_hasCompactSupport {d : ℕ} (φ : Vec d × ℝ → ℝ) (hφc : HasCompactSupport φ)
    (v : Vec d × ℝ) : HasCompactSupport fun w => fderiv ℝ φ w v :=
  (hφc.fderiv ℝ).comp_left (g := fun L : Vec d × ℝ →L[ℝ] ℝ => L v) (by simp)

theorem Tcv_support_in {d : ℕ} {ε : ℝ} {hε : 0 < ε} {U : Set (Vec d)} {b e : ℝ}
    (φ : Vec d × ℝ → ℝ) (hφc : HasCompactSupport φ)
    (hφs : tsupport φ ⊆ U ×ˢ Ioo (b + 3 * ε) e) :
    HasCompactSupport (Tcv ε hε φ) ∧ tsupport (Tcv ε hε φ) ⊆ U ×ˢ Ioo b e := by
  have hK : IsCompact (tsupport φ) := hφc
  let S' : Set (Vec d × ℝ) := (Prod.fst '' tsupport φ) ×ˢ
    ((fun p : ℝ × ℝ => p.1 - p.2) '' ((Prod.snd '' tsupport φ) ×ˢ Icc ε (3 * ε)))
  have hS'c : IsCompact S' :=
    (hK.image continuous_fst).prod
      (((hK.image continuous_snd).prod isCompact_Icc).image (continuous_fst.sub continuous_snd))
  have hsupp : Function.support (Tcv ε hε φ) ⊆ S' := by
    intro z hz
    obtain ⟨u, hu, hmem⟩ := Tcv_exists_of_ne_zero φ (tsupport φ)
      (fun w hw => subset_tsupport φ hw) z hz
    refine ⟨⟨_, hmem, rfl⟩, ?_⟩
    refine ⟨((z.2 + u), u), ⟨⟨_, hmem, rfl⟩, hu⟩, ?_⟩
    simp
  have hS'sub : S' ⊆ U ×ˢ Ioo b e := by
    rintro z ⟨⟨w, hw, hwz⟩, ⟨⟨t, u⟩, ⟨⟨w', hw', hw't⟩, hu⟩, hz2⟩⟩
    have h1 := hφs hw
    have h2 := hφs hw'
    simp only at hw't hz2 hu
    constructor
    · rw [← hwz]; exact h1.1
    · rw [← hz2]
      obtain ⟨h3, h4⟩ := h2.2
      rw [hw't] at h3 h4
      constructor <;> linarith [hu.1, hu.2]
  have hcl : tsupport (Tcv ε hε φ) ⊆ S' := closure_minimal hsupp hS'c.isClosed
  exact ⟨hS'c.of_isClosed_subset (isClosed_tsupport _) hcl, hcl.trans hS'sub⟩

namespace MolData

variable {d : ℕ} {U : Set (Vec d)} {b e Lam : ℝ} {A : Vec d → Mat d} {V : Vec d × ℝ → ℝ}
  {G : Fin d → Vec d × ℝ → ℝ}

theorem measurableSet_S (h : MolData U b e Lam A V G) : MeasurableSet (U ×ˢ Ioo b e) :=
  h.isOpen.measurableSet.prod measurableSet_Ioo

theorem isOpen_S (h : MolData U b e Lam A V G) : IsOpen (U ×ˢ Ioo b e) :=
  h.isOpen.prod isOpen_Ioo

theorem vol_S (h : MolData U b e Lam A V G) : volume (U ×ˢ Ioo b e) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top h.finite measure_Ioo_lt_top

theorem isFiniteMeasure_S (h : MolData U b e Lam A V G) :
    IsFiniteMeasure (volume.restrict (U ×ˢ Ioo b e)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact h.vol_S⟩

theorem integrableOn_V (h : MolData U b e Lam A V G) : IntegrableOn V (U ×ˢ Ioo b e) volume := by
  haveI := h.isFiniteMeasure_S
  exact h.memV.integrable one_le_two

theorem integrableOn_G (h : MolData U b e Lam A V G) (k : Fin d) :
    IntegrableOn (G k) (U ×ˢ Ioo b e) volume := by
  haveI := h.isFiniteMeasure_S
  exact (h.memG k).integrable one_le_two

theorem abs_A_le (h : MolData U b e Lam A V G) (y : Vec d) (j k : Fin d) : |A y j k| ≤ Lam :=
  abs_apply_le_of_isEllipticMatrix (h.ell y) j k

theorem integrableOn_AG (h : MolData U b e Lam A V G) (j k : Fin d) :
    IntegrableOn (fun z : Vec d × ℝ => A z.1 j k * G k z) (U ×ˢ Ioo b e) volume :=
  (h.integrableOn_G k).bdd_mul (c := Lam)
    (((h.measA j k).comp measurable_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => by simpa using h.abs_A_le z.1 j k)

theorem integrableOn_Hs (h : MolData U b e Lam A V G) (j : Fin d) :
    IntegrableOn (Hs A G j) (U ×ˢ Ioo b e) volume :=
  integrable_finset_sum _ fun k _ => h.integrableOn_AG j k

theorem integrableOn_Hs_mul (h : MolData U b e Lam A V G) (j : Fin d) {g : Vec d × ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    IntegrableOn (fun z => Hs A G j z * g z) (U ×ˢ Ioo b e) volume := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  exact (h.integrableOn_Hs j).mul_bdd (c := C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_V_mul (h : MolData U b e Lam A V G) {g : Vec d × ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    IntegrableOn (fun z => V z * g z) (U ×ˢ Ioo b e) volume := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  exact h.integrableOn_V.mul_bdd (c := C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

theorem integrableOn_Aj_mul (h : MolData U b e Lam A V G) (j k : Fin d) {g : Vec d × ℝ → ℝ}
    (hg : Continuous g) (hc : HasCompactSupport g) :
    IntegrableOn (fun z => (A z.1 j k * G k z) * g z) (U ×ˢ Ioo b e) volume := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hc
  exact (h.integrableOn_AG j k).mul_bdd (c := C) hg.aestronglyMeasurable
    (Filter.Eventually.of_forall hC)

/-- The identity `H2` for `C¹` test functions. -/
theorem H2_C1 (h : MolData U b e Lam A V G) (ψ : Vec d × ℝ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Ioo b e) :
    ∫ z in U ×ˢ Ioo b e, V z * fderiv ℝ ψ z (0, 1) =
      ∑ j : Fin d, ∫ z in U ×ˢ Ioo b e, Hs A G j z * fderiv ℝ ψ z (basisVec j, 0) := by
  haveI : (volume : Measure (Vec d × ℝ)).IsAddHaarMeasure := by
    rw [Measure.volume_eq_prod]; infer_instance
  let w : Option (Fin d) → Vec d × ℝ := fun o => o.elim ((0 : Vec d), (1 : ℝ))
    (fun j => (basisVec j, (0 : ℝ)))
  let A' : Option (Fin d) → Vec d × ℝ → ℝ := fun o => o.elim V (fun j z => -Hs A G j z)
  have hA : ∀ i, IntegrableOn (A' i) (U ×ˢ Ioo b e) volume := by
    intro i
    cases i with
    | none => exact h.integrableOn_V
    | some j => exact (h.integrableOn_Hs j).neg
  have hB : IntegrableOn (fun _ : Vec d × ℝ => (0 : ℝ)) (U ×ˢ Ioo b e) volume :=
    integrable_zero _ _ _
  have hsmooth : ∀ φ : Vec d × ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U ×ˢ Ioo b e →
      ∑ i, (∫ z in U ×ˢ Ioo b e, A' i z * fderiv ℝ φ z (w i) ∂volume) +
        ∫ z in U ×ˢ Ioo b e, (fun _ : Vec d × ℝ => (0 : ℝ)) z * φ z ∂volume = 0 := by
    intro φ hφ hφc hφs
    have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
    have e1 := h.H2 φ hφ hφc hφs
    have hint : ∀ j : Fin d, Integrable
        (fun z => Hs A G j z * fderiv ℝ φ z (basisVec j, 0)) (volume.restrict (U ×ˢ Ioo b e)) :=
      fun j => h.integrableOn_Hs_mul j (fderiv_apply_continuous φ hφ1 _)
        (fderiv_apply_hasCompactSupport φ hφc _)
    have e2 : ∫ z in U ×ˢ Ioo b e, ∑ j : Fin d,
        (∑ k : Fin d, A z.1 j k * G k z) * fderiv ℝ φ z (basisVec j, 0) =
        ∑ j : Fin d, ∫ z in U ×ˢ Ioo b e, Hs A G j z * fderiv ℝ φ z (basisVec j, 0) :=
      integral_finset_sum _ (fun j _ => hint j)
    rw [Fintype.sum_option]
    simp only [A', w, Option.elim_none, Option.elim_some, zero_mul, integral_zero, add_zero]
    have e3 : ∀ j : Fin d, ∫ z in U ×ˢ Ioo b e, (-Hs A G j z) * fderiv ℝ φ z (basisVec j, 0) =
        -∫ z in U ×ˢ Ioo b e, Hs A G j z * fderiv ℝ φ z (basisVec j, 0) := fun j => by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [neg_mul])
    simp only [e3, Finset.sum_neg_distrib]
    rw [e1, e2]
    ring
  have := weak_identity_C1_of_smooth (volume : Measure (Vec d × ℝ)) h.isOpen_S w A'
    (fun _ => 0) hA hB hsmooth ψ hψ hc hs
  rw [Fintype.sum_option] at this
  simp only [A', w, Option.elim_none, Option.elim_some, zero_mul, integral_zero, add_zero] at this
  have e3 : ∀ j : Fin d, ∫ z in U ×ˢ Ioo b e, (-Hs A G j z) * fderiv ℝ ψ z (basisVec j, 0) =
      -∫ z in U ×ˢ Ioo b e, Hs A G j z * fderiv ℝ ψ z (basisVec j, 0) := fun j => by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by simp [neg_mul])
  simp only [e3, Finset.sum_neg_distrib] at this
  linarith

end MolData

end EinsteinFull.ParabolicBridge
