import EinsteinRelation.External.GilbargTrudinger

open MeasureTheory
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger

/-- If `f =ᵐ[μ.restrict s] g` and `f` is locally integrable on `s`, then `g` is also
locally integrable on `s` (`paper/main.tex:727–729`). -/
theorem LocallyIntegrableOn.congr_ae {d : ℕ} {f g : Vec d → ℝ} {s : Set (Vec d)}
    (h : f =ᵐ[volume.restrict s] g) (hf : LocallyIntegrableOn f s volume) :
    LocallyIntegrableOn g s volume := by
  intro x hx
  rcases hf x hx with ⟨t, ht, ht_int⟩
  -- ht : t ∈ 𝓝[s] x
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp ht with ⟨V, hV, hVt⟩
  -- hV : V ∈ 𝓝 x, hVt : V ∩ s ⊆ t
  let t' := V ∩ s
  have ht'_sub_s : t' ⊆ s := by
    intro x hx
    exact hx.2
  have ht'_sub_t : t' ⊆ t := hVt
  have h_int_t' : IntegrableOn f t' volume := ht_int.mono_set ht'_sub_t
  have h_ae_t' : f =ᵐ[volume.restrict t'] g := by
    have h_restrict_le : volume.restrict t' ≤ volume.restrict s :=
      Measure.restrict_mono ht'_sub_s le_rfl
    have h0 : volume.restrict s {x | f x ≠ g x} = 0 := by
      apply (measure_eq_zero_iff_ae_notMem.2 ?_)
      filter_upwards [h] with a ha
      simp [ha]
    have h_meas : volume.restrict t' {x | f x ≠ g x} = 0 := by
      apply le_antisymm ?_ zero_le
      calc
        volume.restrict t' {x | f x ≠ g x} ≤ volume.restrict s {x | f x ≠ g x} :=
          h_restrict_le _
        _ = 0 := h0
    have h_not_mem : ∀ᵐ a ∂(volume.restrict t'), a ∉ {x | f x ≠ g x} :=
      (measure_eq_zero_iff_ae_notMem.1 h_meas)
    filter_upwards [h_not_mem] with a ha
    simpa [Set.mem_setOf_eq] using not_not.mp ha
  have h_int_g_t' : IntegrableOn g t' volume := h_int_t'.congr_fun_ae h_ae_t'
  have ht'_mem_nhdsWithin : t' ∈ 𝓝[s] x := by
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    exact ⟨V, hV, subset_rfl⟩
  exact ⟨t', ht'_mem_nhdsWithin, h_int_g_t'⟩

/-- Sobolev representative replacement preserves the weak equation
(`paper/main.tex:727-729`). -/
theorem weakSolution_congr_ae {d : ℕ} {U : Set (Vec d)}
    {a : Vec d → Mat d} {u v : Vec d → ℝ} {g h : Vec d → Vec d}
    (hu : v =ᵐ[volume.restrict U] u) (hg : h =ᵐ[volume.restrict U] g)
    (hw : WeakSolution U a u g) : WeakSolution U a v h := by
  rcases hw with ⟨hu_mem, hg_mem, h_grad, h_div⟩
  have hv_mem : MemLp v 2 (volume.restrict U) := hu_mem.ae_eq hu.symm
  have hh_mem : MemLp h 2 (volume.restrict U) := hg_mem.ae_eq hg.symm
  have h_grad_vh : HasWeakGradient U v h := by
    intro i
    rcases h_grad i with ⟨h_loc_u, h_loc_g, h_eq⟩
    have h_loc_v : LocallyIntegrableOn v U volume :=
      LocallyIntegrableOn.congr_ae hu.symm h_loc_u
    have h_loc_h : LocallyIntegrableOn (fun x => h x i) U volume := by
      have h_ae : (fun x => g x i) =ᵐ[volume.restrict U] (fun x => h x i) := by
        filter_upwards [hg] with x hx
        simp [hx]
      exact LocallyIntegrableOn.congr_ae h_ae h_loc_g
    refine ⟨h_loc_v, h_loc_h, ?_⟩
    intro φ hφ
    have h_eq' := h_eq φ hφ
    have h_left : (∫ x in U, v x * coordinateDerivative i φ x) = (∫ x in U, u x * coordinateDerivative i φ x) :=
      integral_congr_ae (hu.mul (Filter.EventuallyEq.refl _ (fun x => coordinateDerivative i φ x)))
    have h_right : (∫ x in U, h x i * φ x) = (∫ x in U, g x i * φ x) :=
      integral_congr_ae (by
        have h_ae' : (fun x => g x i) =ᵐ[volume.restrict U] (fun x => h x i) := by
          filter_upwards [hg] with x hx
          simp [hx]
        exact (h_ae'.symm.mul (Filter.EventuallyEq.refl _ φ)))
    rw [h_left, h_right, h_eq']
  have h_div_h : HasWeakDivergence U (fun x => (a x).mulVec (h x)) (fun _ => 0) := by
    rcases h_div with ⟨h_div_loc, h_zero_loc, h_div_eq⟩
    have h_div_loc_h : ∀ i : Fin d, LocallyIntegrableOn (fun x => ((a x).mulVec (h x)) i) U volume := by
      intro i
      have h_ae : (fun x => ((a x).mulVec (g x)) i) =ᵐ[volume.restrict U] (fun x => ((a x).mulVec (h x)) i) := by
        filter_upwards [hg] with x hx
        simp [hx]
      exact LocallyIntegrableOn.congr_ae h_ae (h_div_loc i)
    refine ⟨h_div_loc_h, h_zero_loc, ?_⟩
    intro φ hφ
    have h_eq' := h_div_eq φ hφ
    have h_left : (∫ x in U, dot ((a x).mulVec (h x)) (gradient φ x)) =
        (∫ x in U, dot ((a x).mulVec (g x)) (gradient φ x)) :=
      integral_congr_ae (by
        have h_mul : (fun x => (a x).mulVec (g x)) =ᵐ[volume.restrict U] (fun x => (a x).mulVec (h x)) := by
          filter_upwards [hg] with x hx
          simp [hx]
        have h_dot : (fun x => dot ((a x).mulVec (g x)) (gradient φ x)) =ᵐ[volume.restrict U]
            (fun x => dot ((a x).mulVec (h x)) (gradient φ x)) :=
          h_mul.comp₂ (fun w z => dot w z) (Filter.EventuallyEq.refl _ (gradient φ))
        exact h_dot.symm)
    rw [h_left, h_eq']
  exact ⟨hv_mem, hh_mem, h_grad_vh, h_div_h⟩

end EinsteinRelation.Correctors
