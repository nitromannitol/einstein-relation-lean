import EinsteinFull.Calculus.SbxBDirichletClosureTransportR02
import EinsteinFull.Calculus.SbxS4KilledSpectralR01

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull

open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open SubdiffusiveProcess

noncomputable section

/-- The actual graph representative has zero weak gradient off the domain of the
completed smooth core, for either sign of the force. -/
theorem sbxB_physical_zeroBoundary_representative_gradient_zero_off
    {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (U : Set (Vec d))
    (u : physicalH1ZeroBoundary U hd lam) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ U →
      (physicalH1SpaceRepresentative hd lam u.1).weakGradient x = 0 := by
  let g := physicalH1SpaceRepresentative hd lam u.1
  have hg : g.weakGradient =ᵐ[volume] densityWeightedH1SpaceGradient u.1 := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp
    have he : g.gradient_memLp.toLp g.weakGradient = densityWeightedH1SpaceGradient u.1 :=
      congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact g.gradient_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2
          (External.GantertSection7Support.physicalForceMeasure hd lam) =>
        (f : Vec d → EuclideanSpace ℝ (Fin d))) he))
  filter_upwards [hg, physicalH1ZeroBoundary_gradient_zero_off U hd lam u.1 u.2] with x hx hz
  intro hxU
  rw [hx, hz hxU]

/-- The global physical mass pairing is the native ball pairing whenever the
value coordinates and mass coefficients agree almost everywhere on the ball. -/
theorem sbxB_physical_native_mass
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam R : ℝ) (hR : 0 < R)
    (ρ : Vec d → ℝ)
    (hρ : ρ =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] s4PhysicalRho hd ω lam)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (a b : DirichletHilbertSpace (d := d) R hR)
    (hu : densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => a.val none x))
    (hv : densityWeightedH1SpaceValue v.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => b.val none x)) :
    (∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
      ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x := by
  rw [Work.W5.gantert_integral_physicalMeasure]
  calc
    _ = ∫ x, s4PhysicalRho hd ω lam x *
        densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [s4PhysicalRho]
      ring
    _ = ∫ x in sourceBall (0 : Vec d) R, s4PhysicalRho hd ω lam x *
        densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [physicalH1ZeroBoundary_value_zero_off
        (sourceBall (0 : Vec d) R) hd lam u.1 u.2] with x hx hxU
      simp [hx hxU]
    _ = ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x := by
      apply integral_congr_ae
      filter_upwards [hρ, hu, hv] with x hρx hux hvx
      rw [hρx, hux, hvx]

/-- The global physical energy form is the native ball form for matching
weak-gradient coordinates. Symmetry is required only on the ball. -/
theorem sbxB_physical_native_energy
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam R : ℝ) (hR : 0 < R)
    (α : Vec d → Mat d)
    (hα : α =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] s4PhysicalAlpha hd ω lam)
    (hsymm : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), (α x).IsSymm)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (a b : DirichletHilbertSpace (d := d) R hR)
    (hu : ∀ i : Fin d,
      (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => a.val (some i) x))
    (hv : ∀ i : Fin d,
      (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)) i)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => b.val (some i) x)) :
    (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
      (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x) := by
  rw [s4_physical_form_lebesgue]
  calc
    _ = ∫ x in sourceBall (0 : Vec d) R,
        dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x))) := by
      symm
      apply setIntegral_eq_integral_of_ae_compl_eq_zero
      filter_upwards [sbxB_physical_zeroBoundary_representative_gradient_zero_off
        hd lam (sourceBall (0 : Vec d) R) u] with x hx hxU
      simp [hx hxU, dot]
    _ = ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x) := by
      apply integral_congr_ae
      filter_upwards [hα, hsymm, ae_all_iff.mpr hu, ae_all_iff.mpr hv] with x hαx hs hux hvx
      have hux' : WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x) =
          (fun i => a.val (some i) x) := funext hux
      have hvx' : WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x) =
          (fun i => b.val (some i) x) := funext hvx
      rw [← hαx, hux', hvx']
      change dotProduct (fun i => a.val (some i) x)
          ((α x).mulVec (fun i => b.val (some i) x)) =
        dotProduct ((α x).mulVec (fun i => a.val (some i) x))
          (fun i => b.val (some i) x)
      calc
        _ = dotProduct (fun i => b.val (some i) x)
              ((α x).mulVec (fun i => a.val (some i) x)) := hs.dotProduct_mulVec_comm
        _ = _ := dotProduct_comm _ _

/-- A regular physical field makes the matching native coefficient symmetric
on the ball, including for negative forces. -/
theorem sbxB_physical_native_energy_of_regular
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (L : ℝ) (hω : IsRegular L ω)
    (lam R : ℝ) (hR : 0 < R) (α : Vec d → Mat d)
    (hα : α =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] s4PhysicalAlpha hd ω lam)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (a b : DirichletHilbertSpace (d := d) R hR)
    (hu : ∀ i : Fin d,
      (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => a.val (some i) x))
    (hv : ∀ i : Fin d,
      (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)) i)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => b.val (some i) x)) :
    (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
      (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x) := by
  apply sbxB_physical_native_energy hd ω lam R hR α hα
  · filter_upwards [hα] with x hx
    rw [hx]
    exact Matrix.IsSymm.smul ((hω.1 x).1)
      ((1 / 2 : ℝ) * s4PhysicalRho hd ω lam x)
  · exact hu
  · exact hv

/-- Both physical forms match the corresponding native forms for the paired
vectors supplied by the physical-to-native closure transport. -/
theorem sbxB_physical_native_forms_of_regular
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (L : ℝ) (hω : IsRegular L ω)
    (lam R : ℝ) (hR : 0 < R) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (a b : DirichletHilbertSpace (d := d) R hR)
    (hu : densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => a.val none x) ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => a.val (some i) x))
    (hv : densityWeightedH1SpaceValue v.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => b.val none x) ∧
      ∀ i : Fin d,
        (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)) i)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => b.val (some i) x)) :
    ((∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x) ∧
    ((∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x)) := by
  have hρ : ρ =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] s4PhysicalRho hd ω lam := by
    filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
    exact (hcoeff x hx).1
  have hα : α =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] s4PhysicalAlpha hd ω lam := by
    filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
    exact (hcoeff x hx).2
  exact ⟨sbxB_physical_native_mass hd ω lam R hR ρ hρ u v a b hu.1 hv.1,
    sbxB_physical_native_energy_of_regular hd ω L hω lam R hR α hα u v a b hu.2 hv.2⟩

/-- Every pair of physical zero-boundary vectors has native representatives
with the same coordinates and the same physical mass and energy forms. -/
theorem sbxB_exists_physical_native_forms_of_regular
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (L : ℝ) (hω : IsRegular L ω)
    (lam R : ℝ) (hR : 0 < R) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam) :
    ∃ a b : DirichletHilbertSpace (d := d) R hR,
      (densityWeightedH1SpaceValue u.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
          (fun x => a.val none x) ∧
        ∀ i : Fin d,
          (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)) i)
            =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => a.val (some i) x)) ∧
      (densityWeightedH1SpaceValue v.1 =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
          (fun x => b.val none x) ∧
        ∀ i : Fin d,
          (fun x => (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)) i)
            =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] (fun x => b.val (some i) x)) ∧
      ((∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
          ∂physicalReversibleMeasure ω hd lam) =
        ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x) ∧
      ((∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
          (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
        ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x)) := by
  obtain ⟨a, ha, hag⟩ := sbxB_exists_dirichletHilbert_of_physicalZeroBoundary hd lam R hR u
  obtain ⟨b, hb, hbg⟩ := sbxB_exists_dirichletHilbert_of_physicalZeroBoundary hd lam R hR v
  refine ⟨a, b, ⟨ha, hag⟩, ⟨hb, hbg⟩, ?_⟩
  exact sbxB_physical_native_forms_of_regular hd ω L hω lam R hR ρ α hcoeff u v a b
    ⟨ha, hag⟩ ⟨hb, hbg⟩

#print axioms sbxB_physical_native_forms_of_regular
#print axioms sbxB_exists_physical_native_forms_of_regular

end
end EinsteinFull
