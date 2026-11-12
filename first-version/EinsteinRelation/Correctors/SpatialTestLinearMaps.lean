import EinsteinRelation.Calculus.Weak
import EinsteinRelation.Correctors.SpatialWeakLocalization
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Spatial test functions are closed under scalar multiplication.
Source: `paper/main.tex:798–806`. -/
private theorem isSpatialTest_const_smul {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (c : ℝ) :
    IsSpatialTest U (c • ψ) := by
  refine ⟨hψ.1.const_smul c, ?_, ?_⟩
  · exact hψ.2.1.of_isClosed_subset (isClosed_tsupport (c • ψ))
      (tsupport_smul_subset_right (fun _ => c) ψ)
  · exact (tsupport_smul_subset_right (fun _ => c) ψ).trans hψ.2.2

/-- Spatial test inclusion and its distributional derivative pairing are linear.
Source: `paper/main.tex:798–806`; prescribed-time weak derivative recovery. -/
theorem exists_spatial_test_linear_maps {d : ℕ} (U : Set (Vec d))
    [IsFiniteMeasure (volume.restrict U)] (i : Fin d)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict U)) :
    ∃ (V : Submodule ℝ (Vec d → ℝ))
      (T : V →ₗ[ℝ] Lp ℝ 2 (volume.restrict U)) (L : V →ₗ[ℝ] ℝ),
      (∀ ψ, ψ ∈ V ↔ IsSpatialTest U ψ) ∧
      (∀ ψ : V, (T ψ : Vec d → ℝ) =ᵐ[volume.restrict U] (ψ : Vec d → ℝ)) ∧
      (∀ ψ : V, L ψ = -(∫ x in U, u x * coordinateDerivative i ψ x)) := by
  -- V is the submodule of spatial test functions
  let V : Submodule ℝ (Vec d → ℝ) :=
    { carrier := {ψ | IsSpatialTest U ψ}
      add_mem' := by
        intro a b ha hb
        rcases ha with ⟨ha_c, ha_comp, ha_supp⟩
        rcases hb with ⟨hb_c, hb_comp, hb_supp⟩
        exact ⟨ha_c.add hb_c, ha_comp.add hb_comp, by
          have h_add : tsupport (a + b) ⊆ tsupport a ∪ tsupport b :=
            tsupport_add a b
          exact Set.Subset.trans h_add (Set.union_subset ha_supp hb_supp)⟩
      zero_mem' := by
        refine ⟨contDiff_const, HasCompactSupport.zero, ?_⟩
        simp
      smul_mem' := by
        intro c ψ hψ
        exact isSpatialTest_const_smul hψ c
    }
  have hV_mem (ψ : Vec d → ℝ) : ψ ∈ V ↔ IsSpatialTest U ψ := by rfl
  -- Helper: every spatial test function is in L^2
  have memLp_test (ψ : Vec d → ℝ) (hψ : IsSpatialTest U ψ) :
      MemLp ψ 2 (volume.restrict U) := by
    have hcont := hψ.1.continuous
    exact hcont.memLp_of_hasCompactSupport hψ.2.1
  -- Helper: coordinateDerivative of a test function is in L^2
  have memLp_deriv_test (ψ : Vec d → ℝ) (hψ : IsSpatialTest U ψ) :
      MemLp (coordinateDerivative i ψ) 2 (volume.restrict U) := by
    have h_contDiff : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i ψ) :=
      (contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const
    exact h_contDiff.continuous.memLp_of_hasCompactSupport (hψ.2.1.fderiv_apply ℝ (unitVector i))
  -- Product u * (coordinateDerivative i ψ) is integrable on U
  have integrable_product (ψ : Vec d → ℝ) (hψ : IsSpatialTest U ψ) :
      Integrable (fun x => u x * coordinateDerivative i ψ x) (volume.restrict U) := by
    exact hu.integrable_mul (memLp_deriv_test ψ hψ)
  let Tf (ψ : V) := (memLp_test ψ.1 ψ.2).toLp ψ.1
  have hTf (ψ : V) : (Tf ψ : Vec d → ℝ) =ᵐ[volume.restrict U] (ψ : Vec d → ℝ) :=
    (memLp_test ψ.1 ψ.2).coeFn_toLp
  let T : V →ₗ[ℝ] Lp ℝ 2 (volume.restrict U) :=
    { toFun := Tf
      map_add' := by
        intro ψ φ
        apply Lp.ext
        filter_upwards [hTf (ψ+φ), hTf ψ, hTf φ, Lp.coeFn_add (Tf ψ) (Tf φ)]
          with x hsum hψ hφ hLp
        simp only [hLp, hsum, hψ, hφ, Submodule.coe_add, Pi.add_apply]
      map_smul' := by
        intro c ψ
        apply Lp.ext
        filter_upwards [hTf (c • ψ), hTf ψ, Lp.coeFn_smul c (Tf ψ)]
          with x hsm hψ hLp
        simp only [hLp, hsm, hψ, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    }
  -- Construct L: V → ℝ, the linear functional
  let L : V →ₗ[ℝ] ℝ :=
    { toFun := fun ψ => -(∫ x in U, u x * coordinateDerivative i ψ.1 x)
      map_add' := by
        intro ψ φ
        dsimp
        have h_add : (fun x => u x * coordinateDerivative i (ψ.1 + φ.1) x) =
            (fun x => u x * coordinateDerivative i ψ.1 x) +
            (fun x => u x * coordinateDerivative i φ.1 x) := by
          ext x
          have hψ_diff : DifferentiableAt ℝ ψ.1 x :=
            ψ.2.1.differentiable (by simp) x
          have hφ_diff : DifferentiableAt ℝ φ.1 x :=
            φ.2.1.differentiable (by simp) x
          simp [coordinateDerivative, fderiv_add hψ_diff hφ_diff, mul_add]
        rw [h_add]
        change -(∫ x in U, (u x * coordinateDerivative i ψ.1 x) +
          (u x * coordinateDerivative i φ.1 x)) = _
        rw [integral_add (integrable_product ψ.1 ψ.2) (integrable_product φ.1 φ.2)]
        ring
      map_smul' := by
        intro c ψ
        dsimp
        have h_smul : (fun x => u x * coordinateDerivative i (c • ψ.1) x) =
            (fun x => (c * u x) * coordinateDerivative i ψ.1 x) := by
          ext x
          have hψ_diff : DifferentiableAt ℝ ψ.1 x :=
            ψ.2.1.differentiable (by simp) x
          simp [coordinateDerivative, fderiv_const_smul hψ_diff c, mul_left_comm, mul_assoc]
        rw [h_smul]
        have h_int : (∫ x in U, (c * u x) * coordinateDerivative i ψ.1 x) =
            c * (∫ x in U, u x * coordinateDerivative i ψ.1 x) := by
          simp_rw [mul_assoc]
          exact integral_const_mul c _
        rw [h_int]
        ring
    }
  refine ⟨V, T, L, hV_mem, ?_, ?_⟩
  · -- T ψ = ψ in L^2
    intro ψ
    exact hTf ψ
  · -- L ψ = -(∫ x in U, u x * coordinateDerivative i ψ x)
    intro ψ
    rfl

end EinsteinRelation.Correctors
