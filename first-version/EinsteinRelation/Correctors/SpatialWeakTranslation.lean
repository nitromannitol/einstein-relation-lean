import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.MeasureTheory.Measure.Haar.Unique
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.Correctors.SpatialBallLocalL2

open MeasureTheory
open Set

namespace EinsteinRelation.Correctors

/-! ## Helper lemmas -/

private theorem coordinateDerivative_comp_add_right {d : ℕ} (i : Fin d) (φ : Vec d → ℝ)
    (y : Vec d) (x : Vec d) :
    coordinateDerivative i (fun z => φ (z + y)) x = coordinateDerivative i φ (x + y) := by
  simp [coordinateDerivative, fderiv_comp_add_right]

/-- Source: `paper/main.tex:896–908`. Actual weak derivatives commute
with spatial translation, on the translated open domain. -/
theorem hasWeakPartialDerivative_translate {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {j : Fin d} {f g : Vec d → ℝ}
    (h : HasWeakPartialDerivative U j f g) (y : Vec d) :
    HasWeakPartialDerivative ((fun x : Vec d => x - y) ⁻¹' U) j
      (fun x => f (x - y)) (fun x => g (x - y)) := by
  -- First, prove local integrability of the translated functions
  have h_loc_f : LocallyIntegrableOn (fun x => f (x - y)) ((fun x : Vec d => x - y) ⁻¹' U) volume := by
    intro x hx
    have hz : x - y ∈ U := hx
    rcases h.1 (x - y) hz with ⟨V, hV, h_int⟩
    rcases mem_nhdsWithin.1 hV with ⟨W, hW_open, hW_sub, hW_mem⟩
    -- hW_open : IsOpen W, hW_sub : x - y ∈ W, hW_mem : W ∩ U ⊆ V
    have hW_int : IntegrableOn f (W ∩ U) volume :=
      h_int.mono_set hW_mem
    let Ty : (Vec d) ≃ₜ (Vec d) := Homeomorph.addRight y
    have hTy_open : IsOpen ((Ty : Vec d → Vec d) '' W) :=
      Ty.isOpenMap _ hW_open
    have hx_Ty : x ∈ (Ty : Vec d → Vec d) '' W := by
      refine ⟨x - y, hW_sub, ?_⟩
      simp [Ty]
    have hW_nhds : (Ty : Vec d → Vec d) '' (W ∩ U) ∈ nhdsWithin x ((fun x : Vec d => x - y) ⁻¹' U) := by
      apply (mem_nhdsWithin (t := (Ty : Vec d → Vec d) '' (W ∩ U)) (a := x) (s := ((fun x : Vec d => x - y) ⁻¹' U))).mpr
      refine ⟨(Ty : Vec d → Vec d) '' W, hTy_open, hx_Ty, ?_⟩
      intro z hz
      rcases hz with ⟨hzTy, hzV⟩
      rcases hzTy with ⟨w, hw, rfl⟩
      have hwU : w ∈ U := by
        simpa [Ty, MeasurableEquiv.coe_addRight] using hzV
      exact ⟨w, ⟨hw, hwU⟩, rfl⟩
    let e : (Vec d) ≃ᵐ (Vec d) := MeasurableEquiv.addRight y
    have h_map : Measure.map (e : Vec d → Vec d) volume = volume := by
      simpa [e] using map_add_right_eq_self (μ := volume) y
    have h_preimage : (e : Vec d → Vec d) ⁻¹' ((Ty : Vec d → Vec d) '' (W ∩ U)) = W ∩ U := by
      ext z; simp [e, Ty, MeasurableEquiv.coe_addRight]
    have h_equiv := integrableOn_map_equiv e (μ := volume) (f := fun x => f (x - y))
      (s := (Ty : Vec d → Vec d) '' (W ∩ U))
    rw [h_map, h_preimage] at h_equiv
    have h_simp : ((fun x : Vec d => f (x - y)) ∘ (e : Vec d → Vec d)) = f := by
      ext z; simp [e, MeasurableEquiv.coe_addRight]
    rw [h_simp] at h_equiv
    exact ⟨(Ty : Vec d → Vec d) '' (W ∩ U), hW_nhds, Iff.mpr h_equiv hW_int⟩
  have h_loc_g : LocallyIntegrableOn (fun x => g (x - y)) ((fun x : Vec d => x - y) ⁻¹' U) volume := by
    intro x hx
    have hz : x - y ∈ U := hx
    rcases h.2.1 (x - y) hz with ⟨V, hV, h_int⟩
    rcases mem_nhdsWithin.1 hV with ⟨W, hW_open, hW_sub, hW_mem⟩
    have hW_int : IntegrableOn g (W ∩ U) volume :=
      h_int.mono_set hW_mem
    let Ty : (Vec d) ≃ₜ (Vec d) := Homeomorph.addRight y
    have hTy_open : IsOpen ((Ty : Vec d → Vec d) '' W) :=
      Ty.isOpenMap _ hW_open
    have hx_Ty : x ∈ (Ty : Vec d → Vec d) '' W := by
      refine ⟨x - y, hW_sub, ?_⟩
      simp [Ty]
    have hW_nhds : (Ty : Vec d → Vec d) '' (W ∩ U) ∈ nhdsWithin x ((fun x : Vec d => x - y) ⁻¹' U) := by
      apply (mem_nhdsWithin (t := (Ty : Vec d → Vec d) '' (W ∩ U)) (a := x) (s := ((fun x : Vec d => x - y) ⁻¹' U))).mpr
      refine ⟨(Ty : Vec d → Vec d) '' W, hTy_open, hx_Ty, ?_⟩
      intro z hz
      rcases hz with ⟨hzTy, hzV⟩
      rcases hzTy with ⟨w, hw, rfl⟩
      have hwU : w ∈ U := by
        simpa [Ty, MeasurableEquiv.coe_addRight] using hzV
      exact ⟨w, ⟨hw, hwU⟩, rfl⟩
    let e : (Vec d) ≃ᵐ (Vec d) := MeasurableEquiv.addRight y
    have h_map : Measure.map (e : Vec d → Vec d) volume = volume := by
      simpa [e] using map_add_right_eq_self (μ := volume) y
    have h_preimage : (e : Vec d → Vec d) ⁻¹' ((Ty : Vec d → Vec d) '' (W ∩ U)) = W ∩ U := by
      ext z; simp [e, Ty, MeasurableEquiv.coe_addRight]
    have h_equiv := integrableOn_map_equiv e (μ := volume) (f := fun x => g (x - y))
      (s := (Ty : Vec d → Vec d) '' (W ∩ U))
    rw [h_map, h_preimage] at h_equiv
    have h_simp : ((fun x : Vec d => g (x - y)) ∘ (e : Vec d → Vec d)) = g := by
      ext z; simp [e, MeasurableEquiv.coe_addRight]
    rw [h_simp] at h_equiv
    exact ⟨(Ty : Vec d → Vec d) '' (W ∩ U), hW_nhds, Iff.mpr h_equiv hW_int⟩
  -- Now the integral equality
  have h_int_eq : ∀ φ : Vec d → ℝ, IsSpatialTest ((fun x : Vec d => x - y) ⁻¹' U) φ →
      (∫ x in ((fun x : Vec d => x - y) ⁻¹' U), f (x - y) * coordinateDerivative j φ x) =
      -(∫ x in ((fun x : Vec d => x - y) ⁻¹' U), g (x - y) * φ x) := by
    intro φ hφ
    have h_supp : tsupport φ ⊆ ((fun x : Vec d => x - y) ⁻¹' U) := hφ.2.2
    have h_support_deriv (x : Vec d) (hx : x ∉ ((fun x : Vec d => x - y) ⁻¹' U)) :
        f (x - y) * coordinateDerivative j φ x = 0 := by
      have hx' : x ∉ tsupport φ := fun h => hx (h_supp h)
      have h_deriv : coordinateDerivative j φ x = 0 := by
        simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx',
          ContinuousLinearMap.zero_apply]
      rw [h_deriv, mul_zero]
    have h_support_φ (x : Vec d) (hx : x ∉ ((fun x : Vec d => x - y) ⁻¹' U)) :
        g (x - y) * φ x = 0 := by
      have hx' : x ∉ tsupport φ := fun h => hx (h_supp h)
      have h_φ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx'
      rw [h_φ, mul_zero]
    -- Convert set integrals to whole-space integrals
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_support_deriv,
      setIntegral_eq_integral_of_forall_compl_eq_zero h_support_φ]
    -- Use integral_add_right_eq_self to translate the integration variable
    have h_translate : (∫ x : Vec d, f (x - y) * coordinateDerivative j φ x) =
        (∫ x : Vec d, f x * coordinateDerivative j (fun z => φ (z + y)) x) := by
      calc
        (∫ x : Vec d, f (x - y) * coordinateDerivative j φ x) =
            (∫ x : Vec d, f ((x + y) - y) * coordinateDerivative j φ (x + y)) := by
          rw [integral_add_right_eq_self (fun x => f (x - y) * coordinateDerivative j φ x) y]
        _ = (∫ x : Vec d, f x * coordinateDerivative j φ (x + y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp
        _ = (∫ x : Vec d, f x * coordinateDerivative j (fun z => φ (z + y)) x) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [coordinateDerivative_comp_add_right j φ y x]
    have h_translate_g : (∫ x : Vec d, g (x - y) * φ x) =
        (∫ x : Vec d, g x * φ (x + y)) := by
      calc
        (∫ x : Vec d, g (x - y) * φ x) =
            (∫ x : Vec d, g ((x + y) - y) * φ (x + y)) := by
          rw [integral_add_right_eq_self (fun x => g (x - y) * φ x) y]
        _ = (∫ x : Vec d, g x * φ (x + y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp
    rw [h_translate, h_translate_g]
    -- Now we need: (∫ x, f x * coordinateDerivative j (fun z => φ (z + y)) x) = -(∫ x, g x * φ (x + y))
    -- We want to apply h.2.2 with φ ∘ (· + y)
    have h_test : IsSpatialTest U (fun z => φ (z + y)) := by
      refine ⟨?_, ?_, ?_⟩
      · -- ContDiff: φ is ContDiff, and z ↦ z + y is ContDiff
        have h_add : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => z + y) :=
          contDiff_id.add contDiff_const
        exact hφ.1.comp h_add
      · -- HasCompactSupport
        have : HasCompactSupport (fun z => φ (z + y)) :=
          hφ.2.1.comp_homeomorph (Homeomorph.addRight y)
        exact this
      · -- tsupport ⊆ U
        intro z hz
        -- hz : z ∈ tsupport (fun z => φ (z + y))
        -- Using tsupport_comp_subset_preimage: tsupport (φ ∘ (· + y)) ⊆ (· + y)⁻¹' (tsupport φ)
        have h_sub := tsupport_comp_subset_preimage φ (continuous_add_right y)
        -- h_sub : tsupport (φ ∘ (· + y)) ⊆ (· + y)⁻¹' (tsupport φ)
        have hz' : z + y ∈ tsupport φ := h_sub hz
        have hz'' : (z + y) - y ∈ U := h_supp hz'
        simpa using hz''
    -- Now apply h.2.2 with φ ∘ (· + y)
    have h_eq := h.2.2 (fun z => φ (z + y)) h_test
    -- Now we need to relate the whole-space integrals to set integrals over U
    have h_supp_φ_translate (x : Vec d) (hx : x ∉ U) : f x * coordinateDerivative j (fun z => φ (z + y)) x = 0 := by
      have hx' : x ∉ tsupport (fun z => φ (z + y)) := fun h => hx (h_test.2.2 h)
      have h_deriv : coordinateDerivative j (fun z => φ (z + y)) x = 0 := by
        simp [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx',
          ContinuousLinearMap.zero_apply]
      rw [h_deriv, mul_zero]
    have h_supp_φ_translate_g (x : Vec d) (hx : x ∉ U) : g x * (fun z => φ (z + y)) x = 0 := by
      have hx' : x + y ∉ tsupport φ := by
        intro h
        apply hx
        have : (x + y) - y ∈ U := h_supp h
        simpa using this
      have h_φ : φ (x + y) = 0 := image_eq_zero_of_notMem_tsupport hx'
      simp [h_φ]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_supp_φ_translate,
      setIntegral_eq_integral_of_forall_compl_eq_zero h_supp_φ_translate_g] at h_eq
    simpa using h_eq
  exact ⟨h_loc_f, h_loc_g, h_int_eq⟩

/-- Source: `paper/main.tex:896–908`. Actual weak divergence commutes
with spatial translation, including local integrability. -/
theorem hasWeakDivergence_translate {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {F : Vec d → Vec d} {h : Vec d → ℝ}
    (hF : HasWeakDivergence U F h) (y : Vec d) :
    HasWeakDivergence ((fun x : Vec d => x - y) ⁻¹' U)
      (fun x => F (x - y)) (fun x => h (x - y)) := by
  let V := (fun x : Vec d => x - y) ⁻¹' U
  have h_loc_comp (i : Fin d) : LocallyIntegrableOn (fun x => F (x - y) i) V volume := by
    intro x hx
    have hz : x - y ∈ U := hx
    rcases hF.1 i (x - y) hz with ⟨W, hW, h_int⟩
    rcases mem_nhdsWithin.1 hW with ⟨Z, hZ_open, hZ_sub, hZ_mem⟩
    have hZ_int : IntegrableOn (fun z => F z i) (Z ∩ U) volume := h_int.mono_set hZ_mem
    let Ty : (Vec d) ≃ₜ (Vec d) := Homeomorph.addRight y
    have hTy_open : IsOpen ((Ty : Vec d → Vec d) '' Z) := Ty.isOpenMap _ hZ_open
    have hx_Ty : x ∈ (Ty : Vec d → Vec d) '' Z := by
      refine ⟨x - y, hZ_sub, ?_⟩
      simp [Ty]
    have hZ_nhds : (Ty : Vec d → Vec d) '' (Z ∩ U) ∈ nhdsWithin x V := by
      apply (mem_nhdsWithin (t := (Ty : Vec d → Vec d) '' (Z ∩ U)) (a := x) (s := V)).mpr
      refine ⟨(Ty : Vec d → Vec d) '' Z, hTy_open, hx_Ty, ?_⟩
      intro z hz
      rcases hz with ⟨hzTy, hzV⟩
      rcases hzTy with ⟨w, hw, rfl⟩
      have hwU : w ∈ U := by
        simpa [Ty, V, MeasurableEquiv.coe_addRight] using hzV
      exact ⟨w, ⟨hw, hwU⟩, rfl⟩
    let e : (Vec d) ≃ᵐ (Vec d) := MeasurableEquiv.addRight y
    have h_map : Measure.map (e : Vec d → Vec d) volume = volume := by
      simpa [e] using map_add_right_eq_self (μ := volume) y
    have h_preimage : (e : Vec d → Vec d) ⁻¹' ((Ty : Vec d → Vec d) '' (Z ∩ U)) = Z ∩ U := by
      ext z; simp [e, Ty, MeasurableEquiv.coe_addRight]
    have h_equiv := integrableOn_map_equiv e (μ := volume) (f := fun x => F (x - y) i)
      (s := (Ty : Vec d → Vec d) '' (Z ∩ U))
    rw [h_map, h_preimage] at h_equiv
    have h_simp : ((fun x : Vec d => F (x - y) i) ∘ (e : Vec d → Vec d)) =
        (fun z => F z i) := by
      ext z; simp [e, MeasurableEquiv.coe_addRight]
    rw [h_simp] at h_equiv
    exact ⟨(Ty : Vec d → Vec d) '' (Z ∩ U), hZ_nhds, Iff.mpr h_equiv hZ_int⟩
  have h_loc_h : LocallyIntegrableOn (fun x => h (x - y)) V volume := by
    intro x hx
    have hz : x - y ∈ U := hx
    rcases hF.2.1 (x - y) hz with ⟨W, hW, h_int⟩
    rcases mem_nhdsWithin.1 hW with ⟨Z, hZ_open, hZ_sub, hZ_mem⟩
    have hZ_int : IntegrableOn h (Z ∩ U) volume := h_int.mono_set hZ_mem
    let Ty : (Vec d) ≃ₜ (Vec d) := Homeomorph.addRight y
    have hTy_open : IsOpen ((Ty : Vec d → Vec d) '' Z) := Ty.isOpenMap _ hZ_open
    have hx_Ty : x ∈ (Ty : Vec d → Vec d) '' Z := by
      refine ⟨x - y, hZ_sub, ?_⟩
      simp [Ty]
    have hZ_nhds : (Ty : Vec d → Vec d) '' (Z ∩ U) ∈ nhdsWithin x V := by
      apply (mem_nhdsWithin (t := (Ty : Vec d → Vec d) '' (Z ∩ U)) (a := x) (s := V)).mpr
      refine ⟨(Ty : Vec d → Vec d) '' Z, hTy_open, hx_Ty, ?_⟩
      intro z hz
      rcases hz with ⟨hzTy, hzV⟩
      rcases hzTy with ⟨w, hw, rfl⟩
      have hwU : w ∈ U := by
        simpa [Ty, V, MeasurableEquiv.coe_addRight] using hzV
      exact ⟨w, ⟨hw, hwU⟩, rfl⟩
    let e : (Vec d) ≃ᵐ (Vec d) := MeasurableEquiv.addRight y
    have h_map : Measure.map (e : Vec d → Vec d) volume = volume := by
      simpa [e] using map_add_right_eq_self (μ := volume) y
    have h_preimage : (e : Vec d → Vec d) ⁻¹' ((Ty : Vec d → Vec d) '' (Z ∩ U)) = Z ∩ U := by
      ext z; simp [e, Ty, MeasurableEquiv.coe_addRight]
    have h_equiv := integrableOn_map_equiv e (μ := volume) (f := fun x => h (x - y))
      (s := (Ty : Vec d → Vec d) '' (Z ∩ U))
    rw [h_map, h_preimage] at h_equiv
    have h_simp : ((fun x : Vec d => h (x - y)) ∘ (e : Vec d → Vec d)) = h := by
      ext z; simp [e, MeasurableEquiv.coe_addRight]
    rw [h_simp] at h_equiv
    exact ⟨(Ty : Vec d → Vec d) '' (Z ∩ U), hZ_nhds, Iff.mpr h_equiv hZ_int⟩
  have h_int_eq : ∀ φ : Vec d → ℝ, IsSpatialTest V φ →
      (∫ x in V, dot (F (x - y)) (gradient φ x)) = -(∫ x in V, h (x - y) * φ x) := by
    intro φ hφ
    have h_supp : tsupport φ ⊆ V := hφ.2.2
    have h_support_dot (x : Vec d) (hx : x ∉ V) : dot (F (x - y)) (gradient φ x) = 0 := by
      have hx' : x ∉ tsupport φ := fun h => hx (h_supp h)
      have h_grad : gradient φ x = 0 := by
        ext i
        simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx',
          ContinuousLinearMap.zero_apply]
      rw [h_grad]
      simp [dot]
    have h_support_h (x : Vec d) (hx : x ∉ V) : h (x - y) * φ x = 0 := by
      have hx' : x ∉ tsupport φ := fun h => hx (h_supp h)
      have h_φ : φ x = 0 := image_eq_zero_of_notMem_tsupport hx'
      rw [h_φ, mul_zero]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_support_dot,
      setIntegral_eq_integral_of_forall_compl_eq_zero h_support_h]
    have h_translate_dot : (∫ x : Vec d, dot (F (x - y)) (gradient φ x)) =
        (∫ x : Vec d, dot (F x) (gradient (fun z => φ (z + y)) x)) := by
      calc
        (∫ x : Vec d, dot (F (x - y)) (gradient φ x)) =
            (∫ x : Vec d, dot (F ((x + y) - y)) (gradient φ (x + y))) := by
          rw [integral_add_right_eq_self (fun x => dot (F (x - y)) (gradient φ x)) y]
        _ = (∫ x : Vec d, dot (F x) (gradient φ (x + y))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp
        _ = (∫ x : Vec d, dot (F x) (gradient (fun z => φ (z + y)) x)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          have h_grad_eq : gradient φ (x + y) = gradient (fun z => φ (z + y)) x := by
            ext i
            simp [gradient, coordinateDerivative_comp_add_right i φ y x]
          simpa [h_grad_eq]
    have h_translate_h : (∫ x : Vec d, h (x - y) * φ x) =
        (∫ x : Vec d, h x * φ (x + y)) := by
      calc
        (∫ x : Vec d, h (x - y) * φ x) =
            (∫ x : Vec d, h ((x + y) - y) * φ (x + y)) := by
          rw [integral_add_right_eq_self (fun x => h (x - y) * φ x) y]
        _ = (∫ x : Vec d, h x * φ (x + y)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp
    rw [h_translate_dot, h_translate_h]
    have h_test : IsSpatialTest U (fun z => φ (z + y)) := by
      refine ⟨?_, ?_, ?_⟩
      · have h_add : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => z + y) :=
          contDiff_id.add contDiff_const
        exact hφ.1.comp h_add
      · have : HasCompactSupport (fun z => φ (z + y)) :=
          hφ.2.1.comp_homeomorph (Homeomorph.addRight y)
        exact this
      · intro z hz
        have h_sub := tsupport_comp_subset_preimage φ (continuous_add_right y)
        have hz' : z + y ∈ tsupport φ := h_sub hz
        have hz'' : (z + y) - y ∈ U := h_supp hz'
        simpa using hz''
    have h_eq := hF.2.2 (fun z => φ (z + y)) h_test
    have h_supp_dot_translate (x : Vec d) (hx : x ∉ U) :
        dot (F x) (gradient (fun z => φ (z + y)) x) = 0 := by
      have hx' : x ∉ tsupport (fun z => φ (z + y)) := fun h => hx (h_test.2.2 h)
      have h_grad : gradient (fun z => φ (z + y)) x = 0 := by
        ext i
        simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx',
          ContinuousLinearMap.zero_apply]
      rw [h_grad]
      simp [dot]
    have h_supp_h_translate (x : Vec d) (hx : x ∉ U) : h x * (fun z => φ (z + y)) x = 0 := by
      have hx' : x + y ∉ tsupport φ := by
        intro h
        apply hx
        have : (x + y) - y ∈ U := h_supp h
        simpa using this
      have h_φ : φ (x + y) = 0 := image_eq_zero_of_notMem_tsupport hx'
      simp [h_φ]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_supp_dot_translate,
      setIntegral_eq_integral_of_forall_compl_eq_zero h_supp_h_translate] at h_eq
    simpa using h_eq
  exact ⟨h_loc_comp, h_loc_h, h_int_eq⟩

end EinsteinRelation.Correctors


/-! Source: `paper/main.tex:724-731`. Weak gradients commute with translation. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The coordinate derivative of a translated test function. -/
private theorem coordinateDerivative_translate_test {d : ℕ} (i : Fin d) (φ : Vec d → ℝ)
    (z x : Vec d) :
    coordinateDerivative i (fun y => φ (y - z)) x = coordinateDerivative i φ (x - z) := by
  unfold coordinateDerivative
  have h := fderiv_comp_add_left (𝕜 := ℝ) (f := φ) (a := -z) (x := x)
  simpa [sub_eq_add_neg, add_comm] using congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) h

/-- Translate an actual global weak gradient using translated compact tests. -/
theorem hasWeakGradient_translation {d : ℕ} (u : Vec d → ℝ) (g : Vec d → Vec d)
    (hw : HasWeakGradient Set.univ u g) (z : Vec d) :
    HasWeakGradient Set.univ (fun x => u (x + z)) (fun x => g (x + z)) := by
  intro i
  have hi := hw i
  rcases hi with ⟨hlu, hlg, heq⟩
  have hlu' : LocallyIntegrableOn (fun x => u (x + z)) Set.univ volume := by
    apply locallyIntegrableOn_univ.mpr
    have h := locallyIntegrable_translate z (locallyIntegrableOn_univ.mp hlu)
    simpa [add_comm] using h
  have hlg' : LocallyIntegrableOn (fun x => g (x + z) i) Set.univ volume := by
    apply locallyIntegrableOn_univ.mpr
    have h := locallyIntegrable_translate z (locallyIntegrableOn_univ.mp hlg)
    simpa [add_comm] using h
  refine ⟨hlu', hlg', ?_⟩
  intro φ hφ
  let ψ : Vec d → ℝ := fun y => φ (y - z)
  have hψ_contDiff : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have : ψ = φ ∘ (fun y => y - z) := rfl
    rw [this]
    exact hφ.1.comp (contDiff_id.sub contDiff_const)
  have hψ_compact : HasCompactSupport ψ := by
    let h_homeo : Vec d ≃ₜ Vec d :=
      { toFun := fun y => y - z
        invFun := fun y => y + z
        left_inv := by intro y; simp
        right_inv := by intro y; simp
        continuous_toFun := continuous_id.sub continuous_const
        continuous_invFun := continuous_id.add continuous_const }
    have h_comp := hφ.2.1.comp_homeomorph h_homeo
    have h_eq : ψ = φ ∘ h_homeo := by
      ext y; dsimp [ψ, h_homeo]
    rw [h_eq]
    exact h_comp
  have hψ_test : IsSpatialTest Set.univ ψ :=
    ⟨hψ_contDiff, hψ_compact, by simp [ψ]⟩
  have h_eq_ψ := heq ψ hψ_test
  have h_deriv : ∀ x, coordinateDerivative i ψ x = coordinateDerivative i φ (x - z) := by
    intro x
    simp [ψ, coordinateDerivative_translate_test i φ z x]
  have h_ψ_val : ∀ x, ψ x = φ (x - z) := fun _ => rfl
  simp [h_deriv, h_ψ_val] at h_eq_ψ
  have hmp : MeasurePreserving (fun x : Vec d => x + z) volume volume := by
    simpa [add_comm] using measurePreserving_add_left volume z
  have h_int1 : (∫ x, u x * coordinateDerivative i φ (x - z) ∂volume) =
      (∫ x, u (x + z) * coordinateDerivative i φ x ∂volume) := by
    calc
      (∫ x, u x * coordinateDerivative i φ (x - z) ∂volume) =
          (∫ x, u ((fun y => y + z) x) * coordinateDerivative i φ (((fun y => y + z) x) - z) ∂volume) := by
        simpa [sub_add_cancel] using (hmp.integral_comp
          (Homeomorph.addRight z).measurableEmbedding
          (fun y => u y * coordinateDerivative i φ (y - z))).symm
      _ = (∫ x, u (x + z) * coordinateDerivative i φ x ∂volume) := by
        simp
  have h_int2 : (∫ x, g x i * φ (x - z) ∂volume) =
      (∫ x, g (x + z) i * φ x ∂volume) := by
    calc
      (∫ x, g x i * φ (x - z) ∂volume) =
          (∫ x, g ((fun y => y + z) x) i * φ (((fun y => y + z) x) - z) ∂volume) := by
        simpa [sub_add_cancel] using (hmp.integral_comp
          (Homeomorph.addRight z).measurableEmbedding
          (fun y => g y i * φ (y - z))).symm
      _ = (∫ x, g (x + z) i * φ x ∂volume) := by
        simp
  rw [h_int1, h_int2] at h_eq_ψ
  simpa using h_eq_ψ

end EinsteinRelation.Correctors
