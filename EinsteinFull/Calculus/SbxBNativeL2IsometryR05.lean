import EinsteinFull.Calculus.SbxBDirichletClosureTransportR02
import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinFull.Work.W1.PhysicalInteriorL2Support

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift

noncomputable section

/-- The native weighted measure is the actual physical measure restricted to the ball. -/
theorem b_native_volume_eq_physical_restrict {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam R : ℝ) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    dirichletVolume ρ R =
      (physicalReversibleMeasure ω hd lam).restrict (sourceBall (0 : Vec d) R) := by
  have hU : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  rw [physicalReversibleMeasure, restrict_withDensity hU]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  exact congrArg ENNReal.ofReal (hρ x hx)

private theorem b_native_volume_le_physical {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam R : ℝ) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    dirichletVolume ρ R ≤ (1 : ℝ≥0∞) • physicalReversibleMeasure ω hd lam := by
  rw [b_native_volume_eq_physical_restrict hd ω lam R hρ, one_smul]
  exact Measure.restrict_le_self

/-- Restriction to the native weighted space preserves the norm of every
actual completed physical interior value. -/
def bPhysicalNativeL2Isometry {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω →ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R) where
  toLinearMap :=
    ((Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
      (b_native_volume_le_physical hd ω lam R hρ)).comp
      (physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω).subtypeL).toLinearMap
  norm_map' f := by
    change ‖Lp.LpToLpOfMeasureLeSMul (E := ℝ) (p := 2)
      (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (b_native_volume_le_physical hd ω lam R hρ) f.val‖ =
        ‖f.val‖
    have hU : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (dirichletBall (d := d) R).isOpen.measurableSet
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_LpToLpOfMeasureLeSMul
      (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (b_native_volume_le_physical hd ω lam R hρ) f.val),
      b_native_volume_eq_physical_restrict hd ω lam R hρ,
      ← eLpNorm_eq_restrict_of_ae_zero_off (physicalReversibleMeasure ω hd lam) hU
        (physicalZeroBoundaryL2_zero_off _ hd ω lam L hω f.val f.property) 2,
      ← Lp.norm_def]

/-- The isometry is the identity on function representatives in native measure. -/
theorem b_physical_native_l2_isometry_ae_native {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    bPhysicalNativeL2Isometry hd ω lam L R hω hρ f =ᵐ[dirichletVolume ρ R] f.val :=
  Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞)
    (b_native_volume_le_physical hd ω lam R hρ) f.val

/-- The representative agreement holds Lebesgue-a.e. on the ball. -/
theorem b_physical_native_l2_isometry_ae_ball {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    bPhysicalNativeL2Isometry hd ω lam L R hω hρ f
      =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] f.val := by
  have hU : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have htransport (p : Vec d → Prop) (hp : ∀ᵐ x ∂dirichletVolume ρ R, p x) :
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), p x := by
    rw [b_native_volume_eq_physical_restrict hd ω lam R hρ, ae_restrict_iff' hU] at hp
    rw [ae_restrict_iff' hU]
    exact (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mp hp
  exact htransport _ (b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ f)

/-- The isometry has the exact norm and is injective. -/
theorem b_physical_native_l2_isometry_norm {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    ‖bPhysicalNativeL2Isometry hd ω lam L R hω hρ f‖ = ‖f‖ :=
  (bPhysicalNativeL2Isometry hd ω lam L R hω hρ).norm_map f

theorem b_physical_native_l2_isometry_injective {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    Function.Injective (bPhysicalNativeL2Isometry hd ω lam L R hω hρ) :=
  (bPhysicalNativeL2Isometry hd ω lam L R hω hρ).injective

/-- Paired physical and native Sobolev vectors have the same scalar image. -/
theorem b_physical_native_l2_isometry_interior_value {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) (hR : 0 < R)
    {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x)
    (C : ℝ) (hC : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hpair : densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => v.val none x) ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => v.val (some i) x)) :
    bPhysicalNativeL2Isometry hd ω lam L R hω hρ
      (physicalZeroBoundaryInteriorValue (sourceBall (0 : Vec d) R) hd ω lam L hω u) =
        dirichletHilbertInclusion ρ R hR C hC v := by
  apply Lp.ext
  have hphys := physicalZeroBoundaryValue_ae_eq_volume (sourceBall (0 : Vec d) R)
    hd ω lam L hω u
  have hrest := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self : volume.restrict (sourceBall (0 : Vec d) R) ≤
      (volume : Measure (Vec d)))).ae_eq hphys
  have hnative := (withDensity_absolutelyContinuous (volume.restrict (sourceBall (0 : Vec d) R))
    (fun x => ENNReal.ofReal (ρ x))).ae_eq (hrest.trans hpair.1)
  exact (b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ _).trans
    (hnative.trans (dirichletHilbertInclusion_coe ρ R hR C hC v).symm)

/-- Every native weighted L² function has an interior physical zero extension. -/
theorem b_physical_native_l2_isometry_surjective {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    Function.Surjective (bPhysicalNativeL2Isometry hd ω lam L R hω hρ) := by
  let U := sourceBall (0 : Vec d) R
  let μ := physicalReversibleMeasure ω hd lam
  have hU : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have hmeas : dirichletVolume ρ R = μ.restrict U :=
    b_native_volume_eq_physical_restrict hd ω lam R hρ
  intro g
  have hg : MemLp (U.indicator (g : Vec d → ℝ)) 2 μ := by
    apply (memLp_indicator_iff_restrict hU).2
    rw [← hmeas]
    exact Lp.memLp g
  let f : Lp ℝ 2 μ := hg.toLp (U.indicator (g : Vec d → ℝ))
  have hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off U
      (dirichletBall (d := d) R).isOpen hd ω lam L hω f).2
    filter_upwards [hg.coeFn_toLp] with x hx hxU
    rw [hx, Set.indicator_of_notMem hxU]
  refine ⟨⟨f, hf⟩, ?_⟩
  apply Lp.ext
  have hrep : f =ᵐ[dirichletVolume ρ R] U.indicator (g : Vec d → ℝ) := by
    apply (Measure.absolutelyContinuous_of_le ?_).ae_eq hg.coeFn_toLp
    rw [hmeas]
    exact Measure.restrict_le_self
  have hmem : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ U := by
    rw [hmeas]
    exact ae_restrict_mem hU
  filter_upwards [b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ ⟨f, hf⟩,
    hrep, hmem] with x hx hy hxU
  rw [hx, hy, Set.indicator_of_mem hxU]

/-- The canonical identification is an isometric equivalence. -/
def bPhysicalNativeL2Equiv {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam L R : ℝ) (hω : IsRegular L ω) {ρ : Vec d → ℝ}
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x) :
    physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω ≃ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R) :=
  LinearIsometryEquiv.ofSurjective (bPhysicalNativeL2Isometry hd ω lam L R hω hρ)
    (b_physical_native_l2_isometry_surjective hd ω lam L R hω hρ)

#print axioms b_physical_native_l2_isometry_ae_ball
#print axioms b_physical_native_l2_isometry_interior_value
#print axioms b_physical_native_l2_isometry_surjective

end
end EinsteinFull
