import EinsteinFull.Calculus.SbxBDirichletClosureTransportR02
import EinsteinFull.Calculus.SbxS9WeightedResolventR03

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open SubdiffusiveProcess

noncomputable section

/-- Physical and native zero-boundary vectors have the same value and every
Euclidean weak-gradient coordinate on the ball. -/
@[nolint defsWithUnderscore]
def b_physical_native_paired {d : ℕ} (hd : 2 ≤ d) (lam R : ℝ) (hR : 0 < R)
    (u : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (v : DirichletHilbertSpace (d := d) R hR) : Prop :=
  densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
    (fun x => v.val none x) ∧
  ∀ i : Fin d,
    (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
      =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => v.val (some i) x)

/-- The shifted native Dirichlet solution, at inverse shift `μ⁻¹`. -/
def bNativeShiftedDirichletResolvent {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR :=
  Classical.choose (exists_compact_dirichletHilbert_shifted_resolvent hd hκ hell R hR
    (inv_pos.mpr μ.property))

/-- The selected native solution obeys the defining shifted variational iff. -/
theorem b_native_shifted_dirichlet_resolvent_spec {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (μ : MarkovProcess.Semigroup.PositiveShift) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
    IsCompactOperator (J.comp (bNativeShiftedDirichletResolvent hd hκ hell R hR μ)) ∧
    ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
      u = bNativeShiftedDirichletResolvent hd hκ hell R hR μ f ↔
        ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            ρ x * u.val none x * v.val none x +
              (μ : ℝ)⁻¹ * dot ((α x).mulVec (fun i => u.val (some i) x))
                (fun i => v.val (some i) x)) = inner ℝ f (J v) :=
  Classical.choose_spec (exists_compact_dirichletHilbert_shifted_resolvent hd hκ hell R hR
    (inv_pos.mpr μ.property))

/-- Conditional on the separate physical/native mass and energy form
identities, the actual killed resolvent agrees on the ball with the native
shifted Dirichlet resolvent. The input to the latter is divided by the shift. -/
theorem b_actual_resolvent_eq_native_of_form_transport
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (hmass : ∀ (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
      (a b : DirichletHilbertSpace (d := d) R hR),
      b_physical_native_paired hd lam R hR u a → b_physical_native_paired hd lam R hR v b →
      (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x)
    (henergy : ∀ (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
      (a b : DirichletHilbertSpace (d := d) R hR),
      b_physical_native_paired hd lam R hR u a → b_physical_native_paired hd lam R hR v b →
      (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x))
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω)
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hfg : (f.val : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (g : Vec d → ℝ)) :
    ((gmpKilledInteriorResolvent r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen μ f).val : Vec d → ℝ)
      =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
    (fun x => (bNativeShiftedDirichletResolvent hd hκ hell R hR μ
      ((μ : ℝ)⁻¹ • g)).val none x) := by
  let U := sourceBall (0 : Vec d) R
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  let u := physicalZeroBoundaryResolvent U hd ω lam L μ hL hω μ.property
    f.val (Lp.memLp f.val)
  have hu := physicalZeroBoundaryResolvent_spec U hd ω lam L μ hL hω μ.property
    f.val (Lp.memLp f.val)
  obtain ⟨a, ha, hag⟩ := sbxB_exists_dirichletHilbert_of_physicalZeroBoundary hd lam R hR u
  have ha' : b_physical_native_paired hd lam R hR u a := ⟨ha, hag⟩
  have hac : dirichletVolume ρ R ≪ volume.restrict U := withDensity_absolutelyContinuous _ _
  have hball : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have hvar : a = bNativeShiftedDirichletResolvent hd hκ hell R hR μ
      ((μ : ℝ)⁻¹ • g) := by
    apply ((b_native_shifted_dirichlet_resolvent_spec hd hκ hell R hR μ).2 _ _).mpr
    intro b
    obtain ⟨v, hv, hvg⟩ := sbxB_exists_physicalZeroBoundary_of_dirichletHilbert hd lam R hR b
    have hv' : b_physical_native_paired hd lam R hR v b := ⟨hv, hvg⟩
    have hM := hmass u v a b ha' hv'
    have hE := henergy u v a b ha' hv'
    have hphysical := hu.2 v
    have hm : Integrable (fun x => ρ x * a.val none x * b.val none x)
        (volume.restrict U) := by
      simpa using dirichletHilbert_scaled_form_integrable hκ hell R hR 0 a b
    have he : Integrable (fun x => dot ((α x).mulVec (fun i => a.val (some i) x))
        (fun i => b.val (some i) x)) (volume.restrict U) := by
      have hi := (dirichletHilbert_scaled_form_integrable hκ hell R hR 1 a b).sub hm
      apply hi.congr
      exact ae_of_all _ fun x => by dsimp; ring
    have hforce : (∫ x, f.val x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) = inner ℝ g (J b) := by
      rw [dirichletVolume_inner_eq_native hκ hell R g (J b) f.val
        (densityWeightedH1SpaceValue v.1)
        (hac.ae_eq hfg.symm)
        ((dirichletHilbertInclusion_coe ρ R hR κ⁻¹
          (fun x _ => (hell.2.2 x).2.1) b).trans (hac.ae_eq hv.symm))]
      rw [Work.W5.gantert_integral_physicalMeasure]
      calc
        _ = ∫ x in U, physicalReversibleDensity ω hd lam x *
            (f.val x * densityWeightedH1SpaceValue v.1 x) := by
          symm
          apply setIntegral_eq_integral_of_ae_compl_eq_zero
          filter_upwards [physicalH1ZeroBoundary_value_zero_off U hd lam v.1 v.2] with x hx hxU
          rw [hx hxU, mul_zero, mul_zero]
        _ = _ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem hball] with x hx
          have hc := (hcoeff x hx).1
          change ρ x = physicalReversibleDensity ω hd lam x at hc
          rw [hc]
          ring
    rw [integral_add hm (he.const_mul _), integral_const_mul,
      real_inner_smul_left, ← hforce, ← hM, ← hE]
    have hne : (μ : ℝ) ≠ 0 := ne_of_gt μ.property
    rw [← hphysical]
    field_simp [hne]
    <;> ring
  have hactual := s9_killed_resolvent_eq_physical_variational r U
    (dirichletBall (d := d) R).isOpen μ f
  have hvalue := physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω u
  rw [hactual] at hvalue
  have hvalue' := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self : volume.restrict U ≤ (volume : Measure (Vec d)))).ae_eq hvalue
  rw [← hvar]
  exact hvalue'.trans ha

#print axioms b_native_shifted_dirichlet_resolvent_spec
#print axioms b_actual_resolvent_eq_native_of_form_transport

end
end EinsteinFull
