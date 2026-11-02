import EinsteinRelation.Correctors.AKMHeatKernelCutoffs
import EinsteinRelation.Correctors.WeakDivergenceH1Testing
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import EinsteinRelation.Correctors.WeakPartialFiniteSum
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.CoefficientColumnDivergence
import EinsteinFull.Calculus.C8GMPMartingale
import EinsteinRelation.SpatialDirichlet.PhysicalFormBoundednessSupport
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import SubdiffusiveProcess.DirichletForm.Basic
import SubdiffusiveProcess.DirichletForm.FOTResolventConstruction
import PDEFoundation.Sobolev.Ch4.Truncation
import PDEFoundation.Sobolev.H1.Smooth
import PDEFoundation.PDE.WeakDivergenceForm
import EinsteinRelation.Correctors.EllipticInverseBounds
import SubdiffusiveProcess.CoarseGrainingVocab.Section8Massive.Interior.FinitePResidualLift
import Homogenization.Geometry.CubeMetric
import PDEFoundation.PDE.CoefficientForcingScale
import PDEFoundation.PDE.EllipticChange
import PDEFoundation.Ambient.MatrixPerturbationEllipticity
import PDEFoundation.Ambient.HilbertVec
import PDEFoundation.Measure.DilationLp
import PDEFoundation.PDE.AffineChange
import PDEFoundation.Geometry.EuclideanBall.Basic
import SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.Schauder
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators Pointwise Convolution
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.GantertSection7Support
/- EXACT SUPERVISOR CONTRACT; replace with checked proof.
theorem gmp_smooth_fixed_environment_realization_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    Nonempty (EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
-/

open EinsteinRelation.SpatialDirichlet

/-- The complete full force-weighted weak-gradient space, retaining its Euclidean gradient. -/
abbrev GMPForceH1 {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :=
  densityWeightedH1Submodule (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)

/-- The value of a full weighted H¹ element in the actual physical reversible measure. -/
def gmpPhysicalH1Value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  sourcePhysicalValue (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u

/-- The graph representative has the scalar component encoded by the complete graph. -/
theorem gmpH1Representative_value_ae {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value =ᵐ[
      densityWeightedMeasure ρ] densityWeightedH1SpaceValue u := by
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  have hvalue : g.value_memLp.toLp g.value = densityWeightedH1SpaceValue u :=
    congrArg Prod.fst (densityWeightedH1SpaceRepresentative_pair u)
  exact g.value_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq
    (congrArg (fun f : Lp ℝ 2 (densityWeightedMeasure ρ) => (f : Vec d → ℝ)) hvalue))

/-- Measure domination transfers the representative without changing its value. -/
theorem gmpH1PhysicalValue_ae {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤ ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalValue ρ hρ hρpos σ K hMeasure u : Vec d → ℝ) =ᵐ[
      densityWeightedMeasure σ] densityWeightedH1SpaceValue u := by
  exact (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value_memLp.coeFn_toLp.trans
    ((Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq
      (gmpH1Representative_value_ae ρ hρ hρpos u))

/-- Changing the reference measure preserves the value of the full source graph. -/
theorem gmpPhysicalH1Value_ae_eq {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    (gmpPhysicalH1Value hd ω lam Λ hω u : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] densityWeightedH1SpaceValue u :=
  gmpH1PhysicalValue_ae (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u

/-- On the quotient-to-graph equivalence the scalar component is the original quotient value. -/
theorem gmpForceH1_graphEquiv_value {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (q : DensityWeightedH1 (physicalForceWeight hd lam)) :
    densityWeightedH1SpaceValue
      (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q) =
      densityWeightedH1Value (physicalForceWeight hd lam) q := by
  rfl

/-- The physical value map loses neither the function nor its unique distributional gradient. -/
theorem gmpPhysicalH1Value_injective {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    Function.Injective (gmpPhysicalH1Value hd ω lam Λ hω) := by
  intro u v huv
  let e := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
  obtain ⟨q, rfl⟩ := e.surjective u
  obtain ⟨r, rfl⟩ := e.surjective v
  apply congrArg e
  apply densityWeightedH1Value_injective (sourceReducedDensity hd lam)
  apply Lp.ext
  have hphys := (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (e q)).symm.trans
    ((Lp.ext_iff.mp huv).trans (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (e r)))
  have hvol := (ae_withDensity_iff_volume_of_continuous_pos
    (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
    (positiveSourcePhysicalDensity ω hd lam) _).mp hphys
  exact (ae_withDensity_iff_volume_of_continuous_pos
    (sourceReducedDensity hd lam) (continuousSourceReducedDensity hd lam)
    (positiveSourceReducedDensity hd lam) _).mpr hvol

/-- Membership in the source domain is exactly membership in the physical value map's range. -/
theorem gmpPhysicalH1Value_range_iff {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    f ∈ Set.range (gmpPhysicalH1Value hd ω lam Λ hω) ↔
      physicalH1Member ω hd lam f := by
  let e := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
  constructor
  · rintro ⟨u, rfl⟩
    obtain ⟨q, rfl⟩ := e.surjective u
    exact ⟨q, (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (e q)).symm⟩
  · rintro ⟨q, hq⟩
    refine ⟨e q, Lp.ext ?_⟩
    exact (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (e q)).trans hq

/-- Smooth compact tests have their literal values under the physical embedding. -/
theorem gmpPhysicalH1Value_compactTest {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    (gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam f hf hc) : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam] f := by
  exact (sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
    (EinsteinFull.C8GMP.compactTestDomain hd lam f hf hc)).value_memLp.coeFn_toLp.trans
      (EinsteinFull.C8GMP.compactTestDomain_value hd Λ ω hω lam f hf hc)

/-- The literal source weighted H¹ domain is dense in physical reversible L². -/
theorem gmpPhysicalH1Member_dense {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    Dense {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      physicalH1Member ω hd lam f} := by
  let : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense : Dense {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      ∃ g : Vec d → ℝ, (f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g ∧
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  apply hdense.mono
  rintro f ⟨g, hfg, hgc, hgd⟩
  apply (gmpPhysicalH1Value_range_iff hd ω lam Λ hω f).mp
  exact ⟨EinsteinFull.C8GMP.compactTestDomain hd lam g hgd hgc,
    Lp.ext ((gmpPhysicalH1Value_compactTest hd ω lam Λ hω g hgd hgc).trans hfg.symm)⟩

/-- The full weighted graph has dense physical values. -/
theorem gmpPhysicalH1Value_denseRange {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    DenseRange (gmpPhysicalH1Value hd ω lam Λ hω) := by
  have heq : Set.range (gmpPhysicalH1Value hd ω lam Λ hω) =
      {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
        physicalH1Member ω hd lam f} := by
    ext f
    exact gmpPhysicalH1Value_range_iff hd ω lam Λ hω f
  change Dense (Set.range (gmpPhysicalH1Value hd ω lam Λ hω))
  rw [heq]
  exact gmpPhysicalH1Member_dense hd ω lam Λ hω

/-- Null sets agree for the force and physical measures, including for signed force. -/
theorem gmp_force_ae_iff_physical {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (p : Vec d → Prop) :
    (∀ᵐ x ∂physicalForceMeasure hd lam, p x) ↔
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, p x := by
  exact (ae_withDensity_iff_volume_of_continuous_pos
    (sourceReducedDensity hd lam) (continuousSourceReducedDensity hd lam)
    (positiveSourceReducedDensity hd lam) p).trans
      (ae_withDensity_iff_volume_of_continuous_pos
        (sourcePhysicalDensity ω hd lam) (continuousSourcePhysicalDensity ω hd lam)
        (positiveSourcePhysicalDensity ω hd lam) p).symm

/-- The scalar component is a linear map on the complete full weak-gradient space. -/
def gmpForceH1ValueLinear {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    GMPForceH1 hd lam →ₗ[ℝ] Lp ℝ 2 (physicalForceMeasure hd lam) where
  toFun := densityWeightedH1SpaceValue
  map_add' u v := congrArg Prod.fst
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).map_add u.1 v.1)
  map_smul' c u := congrArg Prod.fst
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).map_smul c u.1)

/-- The actual physical value map is linear; its domain retains all weak gradients. -/
def gmpPhysicalH1ValueLinear {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    GMPForceH1 hd lam →ₗ[ℝ] Lp ℝ 2 (physicalReversibleMeasure ω hd lam) where
  toFun := gmpPhysicalH1Value hd ω lam Λ hω
  map_add' u v := by
    apply Lp.ext
    have hred : (densityWeightedH1SpaceValue (u + v) : Vec d → ℝ) =ᵐ[
        physicalForceMeasure hd lam] fun x =>
          densityWeightedH1SpaceValue u x + densityWeightedH1SpaceValue v x :=
      (Lp.ext_iff.mp ((gmpForceH1ValueLinear hd lam).map_add u v)).trans
        (Lp.coeFn_add _ _)
    have hphys := (gmp_force_ae_iff_physical hd ω lam _).mp hred
    filter_upwards [gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (u + v),
      gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u,
      gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v, hphys,
      Lp.coeFn_add (gmpPhysicalH1Value hd ω lam Λ hω u)
        (gmpPhysicalH1Value hd ω lam Λ hω v)] with x huv hu hv hadd hsum
    change (gmpPhysicalH1Value hd ω lam Λ hω u +
      gmpPhysicalH1Value hd ω lam Λ hω v) x =
      gmpPhysicalH1Value hd ω lam Λ hω u x +
      gmpPhysicalH1Value hd ω lam Λ hω v x at hsum
    calc
      _ = densityWeightedH1SpaceValue (u + v) x := huv
      _ = densityWeightedH1SpaceValue u x + densityWeightedH1SpaceValue v x := hadd
      _ = _ := (congrArg₂ (· + ·) hu hv).symm.trans hsum.symm
  map_smul' c u := by
    apply Lp.ext
    have hred : (densityWeightedH1SpaceValue (c • u) : Vec d → ℝ) =ᵐ[
        physicalForceMeasure hd lam] fun x => c * densityWeightedH1SpaceValue u x :=
      (Lp.ext_iff.mp ((gmpForceH1ValueLinear hd lam).map_smul c u)).trans
        (Lp.coeFn_smul c _)
    have hphys := (gmp_force_ae_iff_physical hd ω lam _).mp hred
    filter_upwards [gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (c • u),
      gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u, hphys,
      Lp.coeFn_smul c (gmpPhysicalH1Value hd ω lam Λ hω u)] with x hcu hu hsmul hout
    change _ = c * gmpPhysicalH1Value hd ω lam Λ hω u x at hout
    change _ = (c • gmpPhysicalH1Value hd ω lam Λ hω u) x
    exact hcu.trans (hsmul.trans ((congrArg (c * ·) hu).symm.trans hout.symm))

/-- The source's full domain as a linear subspace of physical reversible L². -/
def gmpPhysicalH1Domain {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    Submodule ℝ (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
  (gmpPhysicalH1ValueLinear hd ω lam Λ hω).range

/-- The submodule has exactly the source domain, with no additional regularity restriction. -/
theorem mem_gmpPhysicalH1Domain_iff {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    f ∈ gmpPhysicalH1Domain hd ω lam Λ hω ↔ physicalH1Member ω hd lam f :=
  gmpPhysicalH1Value_range_iff hd ω lam Λ hω f

/-- The source domain submodule is dense in the literal physical reversible L² space. -/
theorem gmpPhysicalH1Domain_dense {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    Dense (gmpPhysicalH1Domain hd ω lam Λ hω :
      Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) :=
  gmpPhysicalH1Value_denseRange hd ω lam Λ hω


/-- The scalar projection of the complete force-weighted graph is continuous. -/
def gmpForceH1ValueContinuousLinear {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    GMPForceH1 hd lam →L[ℝ] Lp ℝ 2 (physicalForceMeasure hd lam) :=
  (gmpForceH1ValueLinear hd lam).mkContinuous 1 (fun u => by
    change ‖WithLp.fst u.1‖ ≤ 1 * ‖u.1‖
    simpa only [one_mul] using WithLp.norm_fst_le _ u.1)

/-- The physical value is precisely the canonical continuous change-of-measure map. -/
theorem gmpPhysicalH1Value_eq_measureChange {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    gmpPhysicalH1Value hd ω lam Λ hω u =
      Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
        (densityWeightedH1SpaceValue u) := by
  apply Lp.ext
  exact (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u).trans
    (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
      (densityWeightedH1SpaceValue u)).symm

/-- The bounded physical clock gives the explicit norm bound on the full graph. -/
theorem gmpPhysicalH1Value_norm_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    ‖gmpPhysicalH1Value hd ω lam Λ hω u‖ ≤ Real.exp Λ * ‖u‖ := by
  let T : Lp ℝ 2 (physicalForceMeasure hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
  have hT : ‖T‖ ≤ Real.exp Λ := by
    have h := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2)
      ENNReal.ofReal_ne_top (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
    have hc : (ENNReal.ofReal (Real.exp (2 * Λ))).toReal ^
        (1 / (2 : ℝ≥0∞)).toReal = Real.exp Λ := by
      norm_num only [ENNReal.toReal_ofReal (Real.exp_nonneg _),
        ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
      rw [← Real.exp_mul]
      congr 1
      ring
    exact h.trans_eq hc
  rw [gmpPhysicalH1Value_eq_measureChange]
  exact (T.le_opNorm _).trans (mul_le_mul hT (WithLp.norm_fst_le _ u.1)
    (norm_nonneg _) (Real.exp_nonneg _))

/-- The full physical H¹ value map as a continuous linear map. -/
def gmpPhysicalH1ValueContinuousLinear {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    GMPForceH1 hd lam →L[ℝ] Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (gmpPhysicalH1ValueLinear hd ω lam Λ hω).mkContinuous (Real.exp Λ)
    (gmpPhysicalH1Value_norm_le hd ω lam Λ hω)


/-- Every physical source-domain element has one and only one full weak-gradient graph. -/
def gmpPhysicalH1DomainEquiv {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    GMPForceH1 hd lam ≃ₗ[ℝ] gmpPhysicalH1Domain hd ω lam Λ hω :=
  LinearEquiv.ofInjective (gmpPhysicalH1ValueLinear hd ω lam Λ hω)
    (gmpPhysicalH1Value_injective hd ω lam Λ hω)

/-- The domain equivalence retains the actual physical value. -/
theorem gmpPhysicalH1DomainEquiv_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    (gmpPhysicalH1DomainEquiv hd ω lam Λ hω u :
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =
      gmpPhysicalH1Value hd ω lam Λ hω u := rfl


/-- The full graph's Euclidean weak-gradient component is linear. -/
def gmpForceH1GradientLinear {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    GMPForceH1 hd lam →ₗ[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (physicalForceMeasure hd lam) where
  toFun := densityWeightedH1SpaceGradient
  map_add' u v := congrArg Prod.snd
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).map_add u.1 v.1)
  map_smul' c u := congrArg Prod.snd
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).map_smul c u.1)

/-- The Euclidean-gradient projection is continuous in the complete graph norm. -/
def gmpForceH1GradientContinuousLinear {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) :
    GMPForceH1 hd lam →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (physicalForceMeasure hd lam) :=
  (gmpForceH1GradientLinear hd lam).mkContinuous 1 (fun u => by
    change ‖WithLp.snd u.1‖ ≤ 1 * ‖u.1‖
    simpa only [one_mul] using WithLp.norm_snd_le _ u.1)

/-- The physical Euclidean weak gradient on the entire complete weighted-H¹ space. -/
def gmpPhysicalH1GradientContinuousLinear {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) :
    GMPForceH1 hd lam →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin d)) 2 (physicalReversibleMeasure ω hd lam) :=
  (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).comp
      (gmpForceH1GradientContinuousLinear hd lam)

/-- The reconstructed graph has its encoded Euclidean weak gradient almost everywhere. -/
theorem gmpH1Representative_gradient_ae {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient =ᵐ[
      densityWeightedMeasure ρ] densityWeightedH1SpaceGradient u := by
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  have hgradient : g.gradient_memLp.toLp g.weakGradient =
      densityWeightedH1SpaceGradient u :=
    congrArg Prod.snd (densityWeightedH1SpaceRepresentative_pair u)
  exact g.gradient_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq
    (congrArg (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ) =>
      (f : Vec d → EuclideanSpace ℝ (Fin d))) hgradient))

/-- The continuous physical gradient is the literal source graph gradient. -/
theorem gmpPhysicalH1Gradient_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u :
      Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      (sourcePhysicalGraph (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u).weakGradient := by
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
    (densityWeightedH1SpaceGradient u)).trans
      ((Measure.absolutelyContinuous_of_le_smul
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq
          (gmpH1Representative_gradient_ae (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam)
            (positiveSourceReducedDensity hd lam) u)).symm

/-- The actual anisotropic energy integral on the entire weighted-H¹ space. -/
def gmpPhysicalH1Energy {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) : ℝ :=
  ∫ x, (1 / 2 : ℝ) *
    dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x))
      ((ω.1 x).mulVec
        (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
    ∂physicalReversibleMeasure ω hd lam

/-- The continuous-gradient energy is exactly the full source physical Dirichlet form. -/
theorem gmpPhysicalH1Energy_eq_source {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    gmpPhysicalH1Energy hd ω lam Λ hω u v =
      sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u v := by
  apply integral_congr_ae
  filter_upwards [gmpPhysicalH1Gradient_ae hd ω lam Λ hω u,
    gmpPhysicalH1Gradient_ae hd ω lam Λ hω v] with x hu hv
  change (1 / 2 : ℝ) * _ = (1 / 2 : ℝ) * _
  rw [hu, hv]

/-- The physical energy plus mass controls the full graph norm, with an explicit constant. -/
theorem gmpPhysicalH1Energy_coercive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    (Real.exp (-2 * Λ) * min 1 ((1 / 2 : ℝ) * Λ⁻¹)) * ‖u‖ ^ 2 ≤
      ‖gmpPhysicalH1Value hd ω lam Λ hω u‖ ^ 2 +
        gmpPhysicalH1Energy hd ω lam Λ hω u u := by
  rw [gmpPhysicalH1Energy_eq_source]
  have h := sourcePhysicalResolvent_coercive hd ω lam Λ 1 hΛ hω zero_lt_one u
  simp only [one_mul, real_inner_self_eq_norm_sq] at h
  convert h using 1
  rfl

/-- The full physical energy norm is bounded above by the complete graph norm. -/
theorem gmpPhysicalH1Energy_mass_upper {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    ‖gmpPhysicalH1Value hd ω lam Λ hω u‖ ^ 2 +
        gmpPhysicalH1Energy hd ω lam Λ hω u u ≤
      Real.exp (2 * Λ) * (1 + Λ / 2) * ‖u‖ ^ 2 := by
  rw [gmpPhysicalH1Energy_eq_source]
  have h := (le_abs_self _).trans
    (sourcePhysicalResolventForm_bounded hd ω lam Λ 1 hΛ hω zero_lt_one u u)
  simp only [one_mul, real_inner_self_eq_norm_sq, pow_two, mul_assoc] at h
  simp only [pow_two, mul_assoc]
  convert h using 1
  rfl


private theorem gmp_dot_mulVec_symm {d : ℕ} (A : Mat d) (hA : A.transpose = A)
    (u v : Vec d) : dot u (A.mulVec v) = dot v (A.mulVec u) := by
  have hu : Matrix.vecMul u A = A.mulVec u := by
    calc
      Matrix.vecMul u A = Matrix.vecMul u A.transpose.transpose := by
        rw [Matrix.transpose_transpose]
      _ = A.transpose.mulVec u := Matrix.vecMul_transpose A.transpose u
      _ = A.mulVec u := by rw [hA]
  calc
    dot u (A.mulVec v) = dotProduct (Matrix.vecMul u A) v :=
      Matrix.dotProduct_mulVec u A v
    _ = dot (A.mulVec u) v := by rw [hu]; rfl
    _ = dot v (A.mulVec u) := by simp only [dot, mul_comm]

/-- Symmetry uses the actual coefficient's pointwise symmetry, without isotropy. -/
theorem gmpPhysicalH1Energy_symm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    gmpPhysicalH1Energy hd ω lam Λ hω u v =
      gmpPhysicalH1Energy hd ω lam Λ hω v u := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => congrArg ((1 / 2 : ℝ) * ·)
    (gmp_dot_mulVec_symm (ω.1 x) (hω.1 x).1 _ _)

/-- The physical quadratic energy is nonnegative on the entire weighted-H¹ space. -/
theorem gmpPhysicalH1Energy_nonneg {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    0 ≤ gmpPhysicalH1Energy hd ω lam Λ hω u u := by
  apply integral_nonneg
  intro x
  apply mul_nonneg (by norm_num)
  let ξ := WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x)
  have hs : 0 ≤ euclideanSq ξ := by
    change 0 ≤ ∑ i, ξ i * ξ i
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  exact (mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one hΛ)) hs).trans
    ((hω.1 x).2 ξ).1

/-- Integrability of the actual full physical energy density. -/
theorem gmpPhysicalH1Energy_integrable {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    Integrable (fun x => (1 / 2 : ℝ) *
      dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x))
        ((ω.1 x).mulVec
          (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))))
      (physicalReversibleMeasure ω hd lam) := by
  apply (physicalWeightedFormIntegrand_integrable_of_regular ω Λ hΛ hω
    (sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u)
    (sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v)).congr
  filter_upwards [gmpPhysicalH1Gradient_ae hd ω lam Λ hω u,
    gmpPhysicalH1Gradient_ae hd ω lam Λ hω v] with x hu hv
  change (1 / 2 : ℝ) * _ = (1 / 2 : ℝ) * _
  rw [hu, hv]

/-- The full physical energy is additive on the entire weighted-H¹ graph. -/
theorem gmpPhysicalH1Energy_add_left {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u v w : GMPForceH1 hd lam) :
    gmpPhysicalH1Energy hd ω lam Λ hω (u + v) w =
      gmpPhysicalH1Energy hd ω lam Λ hω u w +
        gmpPhysicalH1Energy hd ω lam Λ hω v w := by
  let G := gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
  have hfun : (fun x => (1 / 2 : ℝ) *
      dot (WithLp.ofLp (G (u + v) x)) ((ω.1 x).mulVec (WithLp.ofLp (G w x)))) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      (fun x => (1 / 2 : ℝ) *
        dot (WithLp.ofLp (G u x)) ((ω.1 x).mulVec (WithLp.ofLp (G w x))) +
        (1 / 2 : ℝ) *
        dot (WithLp.ofLp (G v x)) ((ω.1 x).mulVec (WithLp.ofLp (G w x)))) := by
    filter_upwards [Lp.coeFn_add (G u) (G v)] with x hx
    rw [map_add, hx, Pi.add_apply, WithLp.ofLp_add]
    simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]
  exact (integral_congr_ae hfun).trans (integral_add
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω u w)
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω v w))

/-- The full physical energy is homogeneous on the entire weighted-H¹ graph. -/
theorem gmpPhysicalH1Energy_smul_left {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (c : ℝ) (u v : GMPForceH1 hd lam) :
    gmpPhysicalH1Energy hd ω lam Λ hω (c • u) v =
      c * gmpPhysicalH1Energy hd ω lam Λ hω u v := by
  let G := gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
  have hfun : (fun x => (1 / 2 : ℝ) *
      dot (WithLp.ofLp (G (c • u) x)) ((ω.1 x).mulVec (WithLp.ofLp (G v x)))) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      (fun x => c * ((1 / 2 : ℝ) *
        dot (WithLp.ofLp (G u x)) ((ω.1 x).mulVec (WithLp.ofLp (G v x))))) := by
    filter_upwards [Lp.coeFn_smul c (G u)] with x hx
    rw [map_smul, hx, Pi.smul_apply, WithLp.ofLp_smul]
    simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    ring
  exact (integral_congr_ae hfun).trans (integral_const_mul _ _)

/-- Every sequence Cauchy for the physical mass plus energy converges in that energy.
The limit is a full weak-gradient graph, not an element of a smaller core completion. -/
theorem gmpPhysicalH1Energy_complete {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u : ℕ → GMPForceH1 hd lam)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ p ≥ N, ∀ q ≥ N,
      ‖gmpPhysicalH1Value hd ω lam Λ hω (u p - u q)‖ ^ 2 +
        gmpPhysicalH1Energy hd ω lam Λ hω (u p - u q) (u p - u q) < ε) :
    ∃ w : GMPForceH1 hd lam, Tendsto (fun n =>
      ‖gmpPhysicalH1Value hd ω lam Λ hω (u n - w)‖ ^ 2 +
        gmpPhysicalH1Energy hd ω lam Λ hω (u n - w) (u n - w)) atTop (𝓝 0) := by
  let c := Real.exp (-2 * Λ) * min 1 ((1 / 2 : ℝ) * Λ⁻¹)
  have hc : 0 < c :=
    sourcePhysicalResolvent_coercivity_constant_pos Λ 1 hΛ zero_lt_one
  have hcu : CauchySeq u := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := hu (c * ε ^ 2) (mul_pos hc (sq_pos_of_pos hε))
    refine ⟨N, fun p hp q hq => ?_⟩
    have hsq : ‖u p - u q‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left
      ((gmpPhysicalH1Energy_coercive hd ω lam Λ hΛ hω (u p - u q)).trans_lt
        (hN p hp q hq)) hc.le
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (u p - u q)]
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete hcu
  refine ⟨w, ?_⟩
  have hn : Tendsto (fun n => ‖u n - w‖) atTop (𝓝 0) := by
    simpa using (hw.sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => w) atTop (𝓝 w))).norm
  have hupper : Tendsto (fun n =>
      (Real.exp (2 * Λ) * (1 + Λ / 2)) * ‖u n - w‖ ^ 2) atTop (𝓝 0) := by
    simpa using (hn.pow 2).const_mul (Real.exp (2 * Λ) * (1 + Λ / 2))
  exact squeeze_zero
    (fun n => add_nonneg (sq_nonneg _)
      (gmpPhysicalH1Energy_nonneg hd ω lam Λ hΛ hω (u n - w)))
    (fun n => gmpPhysicalH1Energy_mass_upper hd ω lam Λ hΛ hω (u n - w)) hupper

/-- The physical energy transported to its exact submodule in physical L².
Values outside that submodule are irrelevant to the closed-form axioms. -/
def gmpPhysicalH1Form {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : ℝ := by
  classical
  exact if hf : f ∈ gmpPhysicalH1Domain hd ω lam Λ hω then
    if hg : g ∈ gmpPhysicalH1Domain hd ω lam Λ hω then
      gmpPhysicalH1Energy hd ω lam Λ hω
        ((gmpPhysicalH1DomainEquiv hd ω lam Λ hω).symm ⟨f, hf⟩)
        ((gmpPhysicalH1DomainEquiv hd ω lam Λ hω).symm ⟨g, hg⟩)
    else 0
  else 0

/-- Transport preserves the literal energy on every full weak-gradient graph. -/
theorem gmpPhysicalH1Form_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω v) =
      gmpPhysicalH1Energy hd ω lam Λ hω u v := by
  have hu : gmpPhysicalH1Value hd ω lam Λ hω u ∈
      gmpPhysicalH1Domain hd ω lam Λ hω := ⟨u, rfl⟩
  have hv : gmpPhysicalH1Value hd ω lam Λ hω v ∈
      gmpPhysicalH1Domain hd ω lam Λ hω := ⟨v, rfl⟩
  simp only [gmpPhysicalH1Form, dite_eq_left hu, dite_eq_left hv]
  change gmpPhysicalH1Energy hd ω lam Λ hω
    ((gmpPhysicalH1DomainEquiv hd ω lam Λ hω).symm
      (gmpPhysicalH1DomainEquiv hd ω lam Λ hω u))
    ((gmpPhysicalH1DomainEquiv hd ω lam Λ hω).symm
      (gmpPhysicalH1DomainEquiv hd ω lam Λ hω v)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The actual anisotropic physical energy is a closed symmetric form, with the
entire source weighted-H¹ domain and its explicit physical value embedding. -/
def gmpPhysicalClosedForm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    SubdiffusiveProcess.DirichletForm.ClosedForm (physicalReversibleMeasure ω hd lam) where
  domain := gmpPhysicalH1Domain hd ω lam Λ hω
  form := gmpPhysicalH1Form hd ω lam Λ hω
  denseDomain := gmpPhysicalH1Domain_dense hd ω lam Λ hω
  form_symm := by
    rintro f ⟨u, rfl⟩ g ⟨v, rfl⟩
    change gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω v) =
      gmpPhysicalH1Form hd ω lam Λ hω
        (gmpPhysicalH1Value hd ω lam Λ hω v) (gmpPhysicalH1Value hd ω lam Λ hω u)
    rw [gmpPhysicalH1Form_value, gmpPhysicalH1Form_value]
    exact gmpPhysicalH1Energy_symm hd ω lam Λ hω u v
  form_add_left := by
    rintro f ⟨u, rfl⟩ g ⟨v, rfl⟩ h ⟨w, rfl⟩
    let L := gmpPhysicalH1ValueLinear hd ω lam Λ hω
    change gmpPhysicalH1Form hd ω lam Λ hω (L u + L v) (L w) = _
    rw [← map_add L]
    change gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω (u + v))
      (gmpPhysicalH1Value hd ω lam Λ hω w) =
      gmpPhysicalH1Form hd ω lam Λ hω
        (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω w) +
      gmpPhysicalH1Form hd ω lam Λ hω
        (gmpPhysicalH1Value hd ω lam Λ hω v) (gmpPhysicalH1Value hd ω lam Λ hω w)
    rw [gmpPhysicalH1Form_value, gmpPhysicalH1Form_value, gmpPhysicalH1Form_value]
    exact gmpPhysicalH1Energy_add_left hd ω lam Λ hΛ hω u v w
  form_smul_left := by
    rintro c f ⟨u, rfl⟩ g ⟨v, rfl⟩
    let L := gmpPhysicalH1ValueLinear hd ω lam Λ hω
    change gmpPhysicalH1Form hd ω lam Λ hω (c • L u) (L v) = _
    rw [← map_smul L]
    change gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω (c • u))
      (gmpPhysicalH1Value hd ω lam Λ hω v) = c *
      gmpPhysicalH1Form hd ω lam Λ hω
        (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω v)
    rw [gmpPhysicalH1Form_value, gmpPhysicalH1Form_value]
    exact gmpPhysicalH1Energy_smul_left hd ω lam Λ hω c u v
  form_nonneg := by
    rintro f ⟨u, rfl⟩
    change 0 ≤ gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω u)
    rw [gmpPhysicalH1Form_value]
    exact gmpPhysicalH1Energy_nonneg hd ω lam Λ hΛ hω u
  complete := by
    intro u hu hcu
    choose U hU using hu
    let L := gmpPhysicalH1ValueLinear hd ω lam Λ hω
    have hdiff (p q : ℕ) : gmpPhysicalH1Value hd ω lam Λ hω (U p - U q) =
        u p - u q := by
      change L (U p - U q) = u p - u q
      rw [map_sub, hU, hU]
    have hform (p q : ℕ) : gmpPhysicalH1Form hd ω lam Λ hω
        (u p - u q) (u p - u q) =
        gmpPhysicalH1Energy hd ω lam Λ hω (U p - U q) (U p - U q) := by
      rw [← hdiff p q, gmpPhysicalH1Form_value]
    obtain ⟨W, hW⟩ := gmpPhysicalH1Energy_complete hd ω lam Λ hΛ hω U (by
      intro ε hε
      obtain ⟨N, hN⟩ := hcu ε hε
      refine ⟨N, fun p hp q hq => ?_⟩
      rw [hdiff, ← hform, add_comm]
      exact hN p hp q hq)
    refine ⟨gmpPhysicalH1Value hd ω lam Λ hω W, ⟨W, rfl⟩, ?_⟩
    have hdiffW (n : ℕ) : gmpPhysicalH1Value hd ω lam Λ hω (U n - W) =
        u n - gmpPhysicalH1Value hd ω lam Λ hω W := by
      change L (U n - W) = u n - L W
      rw [map_sub, hU]
    convert hW using 1
    funext n
    rw [← hdiffW, gmpPhysicalH1Form_value]
    exact add_comm _ _

/-- The constructed closed form has exactly the literal source physical-H¹ domain. -/
theorem mem_gmpPhysicalClosedForm_domain_iff {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    f ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain ↔
      physicalH1Member ω hd lam f :=
  mem_gmpPhysicalH1Domain_iff hd ω lam Λ hω f

/-- The constructed closed form agrees with the source energy on the full domain. -/
theorem gmpPhysicalClosedForm_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
      (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω v) =
      sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u v :=
  (gmpPhysicalH1Form_value hd ω lam Λ hω u v).trans
    (gmpPhysicalH1Energy_eq_source hd ω lam Λ hω u v)
/-- On every compact set, a positive continuous weighted `L²` function is in
ordinary `L²`, with the original representative. -/
theorem gmpWeightedMemLp_restrict_isCompact {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) {f : Vec d → E}
    (hf : MemLp f 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    {K : Set (Vec d)} (hK : IsCompact K) : MemLp f 2 (volume.restrict K) := by
  classical
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · simp [hEmpty]
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hNonempty hρ.continuousOn
  have hzmin' : ∀ y ∈ K, ρ z ≤ ρ y := by
    simpa [IsMinOn, IsMinFilter] using hzmin
  have hc : ENNReal.ofReal (ρ z) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hρpos z))
  have hcomp : ENNReal.ofReal (ρ z) • volume.restrict K ≤
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict K := by
    rw [restrict_withDensity hK.measurableSet, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact ENNReal.ofReal_le_ofReal (hzmin' y hy)
  have hsmall := (hf.restrict K).mono_measure hcomp
  have hback := hsmall.smul_measure (ENNReal.inv_ne_top.mpr hc)
  simpa only [smul_smul, ENNReal.inv_mul_cancel hc ENNReal.ofReal_ne_top, one_smul]
    using hback

/-- The two weak-gradient APIs use the identical coordinate derivatives and tests. -/
theorem gmpHasWeakGradient_toPDE {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → ℝ} {g : Vec d → Vec d} (h : HasWeakGradient U f g) :
    PDE.HasWeakGradientOn U f g := by
  intro i φ hSmooth hCompact hSupport
  exact (h i).2.2 φ ⟨hSmooth, hCompact, hSupport⟩
/-- Each coordinate of a Euclidean `L²` field is `L²` under the same measure. -/
theorem gmpEuclideanMemLp_coordinate {d : ℕ} {m : Measure (Vec d)}
    {g : Vec d → EuclideanSpace ℝ (Fin d)} (hg : MemLp g 2 m) (i : Fin d) :
    MemLp (fun x => (WithLp.ofLp (g x)) i) 2 m := by
  refine hg.mono ?_ (ae_of_all _ fun x => ?_)
  · exact ((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).comp_aestronglyMeasurable
      hg.aestronglyMeasurable
  · simpa using PiLp.norm_apply_le (g x) i

/-- The actual weighted graph restricts to ordinary H¹ on each bounded ball. -/
def gmpWeightedGraphLocalH1 {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (x : Vec d) (r : ℝ) : PDE.H1Function (Metric.ball x r) where
  toFun := u.value
  grad := fun y => WithLp.ofLp (u.weakGradient y)
  memL2 := (gmpWeightedMemLp_restrict_isCompact ρ hρ hρpos u.value_memLp
    (isCompact_closedBall x r)).mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  gradMemL2 i := (gmpWeightedMemLp_restrict_isCompact ρ hρ hρpos
    (gmpEuclideanMemLp_coordinate u.gradient_memLp i) (isCompact_closedBall x r)).mono_measure
      (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  hasWeakGradient := PDE.HasWeakGradientOn.restrict Metric.isOpen_ball (subset_univ _)
    (gmpHasWeakGradient_toPDE u.distributionalGradient)

/-- Positive-part values have weighted `L²` norm at most that of the original value. -/
theorem gmpWeightedMemLp_positivePart {d : ℕ} {m : Measure (Vec d)}
    {f : Vec d → ℝ} (hf : MemLp f 2 m) {c : ℝ} (hc : 0 ≤ c) :
    MemLp (fun x => max (f x - c) 0) 2 m := by
  refine hf.mono
    ((hf.aestronglyMeasurable.sub aestronglyMeasurable_const).sup
      aestronglyMeasurable_const) (ae_of_all _ fun x => ?_)
  simp only [Real.norm_eq_abs]
  rcases le_total (f x - c) 0 with h | h
  · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
  · rw [max_eq_left h, abs_of_nonneg h]
    linarith [le_abs_self (f x)]

/-- Subtracting a nonnegative measurable barrier before taking the positive
part preserves weighted `L²`, even if the barrier is not itself in `L²`. -/
theorem gmpWeightedMemLp_positivePart_sub_barrier {d : ℕ} {m : Measure (Vec d)}
    {f b : Vec d → ℝ} (hf : MemLp f 2 m) (hb : AEStronglyMeasurable b m)
    (hb0 : ∀ᵐ x ∂m, 0 ≤ b x) :
    MemLp (fun x => max (f x - b x) 0) 2 m := by
  refine hf.mono
    ((hf.aestronglyMeasurable.sub hb).sup aestronglyMeasurable_const) ?_
  filter_upwards [hb0] with x hx
  simp only [Real.norm_eq_abs]
  rcases le_total (f x - b x) 0 with h | h
  · rw [max_eq_right h, abs_zero]; exact abs_nonneg _
  · rw [max_eq_left h, abs_of_nonneg h]
    linarith [le_abs_self (f x)]

/-- The barrier gradient restricted to the positive excess is weighted `L²`
when its norm is bounded by a nonnegative multiple of the barrier. -/
theorem gmpWeightedMemLp_indicator_barrierGradient {d : ℕ} {m : Measure (Vec d)}
    {f b : Vec d → ℝ} {B : Vec d → EuclideanSpace ℝ (Fin d)} {k : ℝ}
    (hf : MemLp f 2 m) (hb : AEStronglyMeasurable b m)
    (hB : AEStronglyMeasurable B m) (hk : 0 ≤ k)
    (hb0 : ∀ᵐ x ∂m, 0 ≤ b x)
    (hBbound : ∀ᵐ x ∂m, ‖B x‖ ≤ k * b x) :
    MemLp ({x | b x < f x}.indicator B) 2 m := by
  classical
  have hset : NullMeasurableSet {x | b x < f x} m :=
    nullMeasurableSet_lt hb.aemeasurable hf.aemeasurable
  refine (hf.norm.const_mul k).mono' (hB.indicator₀ hset) ?_
  filter_upwards [hb0, hBbound] with x hx hBx
  by_cases h : b x < f x
  · rw [Set.indicator_of_mem (show x ∈ {x | b x < f x} from h)]
    have hfpos : 0 ≤ f x := le_trans hx (le_of_lt h)
    have hfbound : b x ≤ |f x| := by rw [abs_of_nonneg hfpos]; exact le_of_lt h
    simpa only [Real.norm_eq_abs] using le_trans hBx (mul_le_mul_of_nonneg_left hfbound hk)
  · rw [Set.indicator_of_notMem (show x ∉ {x | b x < f x} from h), norm_zero]
    exact mul_nonneg hk (norm_nonneg _)

/-- The excess above a smooth barrier has the expected weak gradient on
any unit ball, without requiring the barrier to be globally weighted `L²`. -/
theorem gmpWeightedGraphPositivePart_sub_barrier_local {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (b : Vec d → ℝ) (hb : ContDiff ℝ 1 b) (x : Vec d) :
    PDE.HasWeakGradientOn (Metric.ball x 1) (fun y => max (u.value y - b y) 0)
      ({y | b y < u.value y}.indicator
        (fun y => WithLp.ofLp (u.weakGradient y) - PDE.classicalGradient b y)) := by
  let hU := PDE.Ch4Infra.isOpenBoundedConvexDomain_ball x 1
  let w := gmpWeightedGraphLocalH1 ρ hρ hρpos u x 1
  let z := PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU hb
  have hw := ((w - z).positivePartSubConst hU 0).hasWeakGradient
  simpa [PDE.H1Function.positivePartSubConst_toFun,
    PDE.H1Function.positivePartSubConst_grad, PDE.H1Function.sub_toFun,
    PDE.H1Function.sub_grad, PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain_toFun,
    PDE.H1Function.ofContDiffOnIsOpenBoundedConvexDomain_grad, w, z,
    gmpWeightedGraphLocalH1, sub_pos] using hw

/-- A smooth nonnegative barrier with gradient bounded by a multiple of itself
produces a global weighted graph for the positive excess, without requiring the
barrier or its gradient to belong to weighted `L²`. -/
theorem gmpWeightedGraphPositivePart_sub_barrier_exists {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (b : Vec d → ℝ) (hb : ContDiff ℝ 1 b) (k : ℝ) (hk : 0 ≤ k)
    (hb0 : ∀ᵐ x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))), 0 ≤ b x)
    (hbound : ∀ᵐ x ∂(volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      ‖WithLp.toLp 2 (PDE.classicalGradient b x)‖ ≤ k * b x) :
    ∃ w : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      w.value = (fun x => max (u.value x - b x) 0) ∧
      w.weakGradient = {x | b x < u.value x}.indicator
        (fun x => u.weakGradient x - WithLp.toLp 2 (PDE.classicalGradient b x)) := by
  classical
  let m := volume.withDensity (fun x => ENNReal.ofReal (ρ x))
  let B : Vec d → EuclideanSpace ℝ (Fin d) :=
    fun x => WithLp.toLp 2 (PDE.classicalGradient b x)
  let v : Vec d → ℝ := fun x => max (u.value x - b x) 0
  let G : Vec d → EuclideanSpace ℝ (Fin d) :=
    {x | b x < u.value x}.indicator (fun x => u.weakGradient x - B x)
  have hbmeas : AEStronglyMeasurable b m := hb.continuous.aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable B m :=
    ((PiLp.continuous_toLp 2 _).comp (PDE.ContDiff.continuous_classicalGradient hb)).aestronglyMeasurable
  have hv : MemLp v 2 m := gmpWeightedMemLp_positivePart_sub_barrier u.value_memLp hbmeas hb0
  have hset : NullMeasurableSet {x | b x < u.value x} m :=
    nullMeasurableSet_lt hbmeas.aemeasurable u.value_memLp.aemeasurable
  have huG : MemLp ({x | b x < u.value x}.indicator u.weakGradient) 2 m :=
    u.gradient_memLp.mono (u.gradient_memLp.aestronglyMeasurable.indicator₀ hset)
      (ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
  have hBG : MemLp ({x | b x < u.value x}.indicator B) 2 m :=
    gmpWeightedMemLp_indicator_barrierGradient u.value_memLp hbmeas hBmeas hk hb0 hbound
  have hG : MemLp G 2 m := by
    have h := huG.sub hBG
    have heq : G = fun x => {y | b y < u.value y}.indicator u.weakGradient x -
        {y | b y < u.value y}.indicator B x := by
      funext x
      by_cases hx : b x < u.value x <;> simp [G, hx]
    rw [heq]
    exact h
  have hlf : IsLocallyFiniteMeasure m := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hvLoc := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos v hlf hv
  have hGLoc := fun i => memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos
    (fun x => (WithLp.ofLp (G x)) i) hlf (gmpEuclideanMemLp_coordinate hG i)
  have hweak : PDE.HasWeakGradientOn univ v (fun x => WithLp.ofLp (G x)) := by
    apply PDE.Ch4Infra.hasWeakGradientOn_of_local_ball isOpen_univ
      (hvLoc.locallyIntegrableOn _) (fun i => (hGLoc i).locallyIntegrableOn _)
    intro x _
    refine ⟨1, by norm_num, subset_univ _, ?_⟩
    have hgrad : (fun y => WithLp.ofLp (G y)) =
        {y | b y < u.value y}.indicator
          (fun y => WithLp.ofLp (u.weakGradient y) - PDE.classicalGradient b y) := by
      funext y i
      by_cases hy : b y < u.value y <;> simp [G, B, hy]
    rw [hgrad]
    exact gmpWeightedGraphPositivePart_sub_barrier_local ρ hρ hρpos u b hb x
  let w := weightedSobolevGraph_mk_of_density_distributionalData ρ hρ hρpos v G hv hG
    (fun i φ hφ => hweak i φ hφ.1 hφ.2.1 hφ.2.2)
  exact ⟨w, rfl, rfl⟩

/-- Positive-part truncation preserves the full weighted weak-gradient graph.
Both the value and the Euclidean gradient are literal representatives. -/
theorem gmpWeightedGraphPositivePart_weakGradient {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (c : ℝ) (hc : 0 ≤ c) :
    HasWeakGradient univ (fun x => max (u.value x - c) 0)
      (fun x => WithLp.ofLp ({y | c < u.value y}.indicator u.weakGradient x)) := by
  classical
  let v : Vec d → ℝ := fun x => max (u.value x - c) 0
  let G : Vec d → EuclideanSpace ℝ (Fin d) := {x | c < u.value x}.indicator u.weakGradient
  have hv : MemLp v 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    gmpWeightedMemLp_positivePart u.value_memLp hc
  have hset : NullMeasurableSet {x | c < u.value x}
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    nullMeasurableSet_lt aemeasurable_const u.value_memLp.aemeasurable
  have hG : MemLp G 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    u.gradient_memLp.mono (u.gradient_memLp.aestronglyMeasurable.indicator₀ hset)
      (ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
  have hlf : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hvLoc := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos v hlf hv
  have hGLoc := fun i => memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos
    (fun x => (WithLp.ofLp (G x)) i) hlf (gmpEuclideanMemLp_coordinate hG i)
  have hweak : PDE.HasWeakGradientOn univ v (fun x => WithLp.ofLp (G x)) := by
    apply PDE.Ch4Infra.hasWeakGradientOn_of_local_ball isOpen_univ
      (hvLoc.locallyIntegrableOn _) (fun i => (hGLoc i).locallyIntegrableOn _)
    intro x _
    refine ⟨1, by norm_num, subset_univ _, ?_⟩
    let w := gmpWeightedGraphLocalH1 ρ hρ hρpos u x 1
    have hw := (w.positivePartSubConst
      (PDE.Ch4Infra.isOpenBoundedConvexDomain_ball x 1) c).hasWeakGradient
    rw [PDE.H1Function.positivePartSubConst_toFun,
      PDE.H1Function.positivePartSubConst_grad] at hw
    have hgrad : (fun y => WithLp.ofLp (G y)) =
        {y | c < u.value y}.indicator (fun y => WithLp.ofLp (u.weakGradient y)) := by
      funext y i
      by_cases hy : c < u.value y <;> simp [G, hy]
    rw [hgrad]
    exact hw
  exact (weightedSobolevGraph_mk_of_density_distributionalData ρ hρ hρpos v G hv hG
    (fun i φ hφ => hweak i φ hφ.1 hφ.2.1 hφ.2.2)).distributionalGradient

/-- The full weighted positive-part graph, with explicit value and gradient fields. -/
def gmpWeightedGraphPositivePart {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x)
    (u : WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (c : ℝ) (hc : 0 ≤ c) :
    WeightedSobolevGraph (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) where
  value := fun x => max (u.value x - c) 0
  weakGradient := {x | c < u.value x}.indicator u.weakGradient
  value_memLp := gmpWeightedMemLp_positivePart u.value_memLp hc
  gradient_memLp := by
    classical
    have hset : NullMeasurableSet {x | c < u.value x}
        (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
      nullMeasurableSet_lt aemeasurable_const u.value_memLp.aemeasurable
    exact u.gradient_memLp.mono (u.gradient_memLp.aestronglyMeasurable.indicator₀ hset)
      (ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
  distributionalGradient := gmpWeightedGraphPositivePart_weakGradient ρ hρ hρpos u c hc
/-- Send a literal weighted graph to its full Hilbert graph class. -/
def gmpH1FromGraph {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    densityWeightedH1Submodule ρ hρ hρpos :=
  densityWeightedH1GraphEmbedding ρ hρ hρpos
    (Quotient.mk (densityWeightedH1Setoid ρ) u)

/-- Passing to the Hilbert graph retains the literal scalar representative. -/
theorem gmpH1FromGraph_value_ae {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    (densityWeightedH1SpaceValue (gmpH1FromGraph ρ hρ hρpos u) : Vec d → ℝ) =ᵐ[
      densityWeightedMeasure ρ] u.value :=
  u.value_memLp.coeFn_toLp

/-- Passing to the Hilbert graph retains the literal Euclidean gradient. -/
theorem gmpH1FromGraph_gradient_ae {d : ℕ} (ρ : Vec d → ℝ) (hρ : Continuous ρ)
    (hρpos : ∀ x, 0 < ρ x) (u : WeightedSobolevGraph (densityWeightedMeasure ρ)) :
    (densityWeightedH1SpaceGradient (gmpH1FromGraph ρ hρ hρpos u) :
      Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[densityWeightedMeasure ρ] u.weakGradient :=
  u.gradient_memLp.coeFn_toLp

/-- Positive-part truncation in the actual complete force-weighted H¹ space. -/
def gmpForceH1PositivePart {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : GMPForceH1 hd lam) (c : ℝ) (hc : 0 ≤ c) : GMPForceH1 hd lam :=
  gmpH1FromGraph (sourceReducedDensity hd lam) (continuousSourceReducedDensity hd lam)
    (positiveSourceReducedDensity hd lam)
    (gmpWeightedGraphPositivePart (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u) c hc)

/-- The force-weighted positive part has the expected scalar representative. -/
theorem gmpForceH1PositivePart_value_ae {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : GMPForceH1 hd lam) (c : ℝ) (hc : 0 ≤ c) :
    (densityWeightedH1SpaceValue (gmpForceH1PositivePart hd lam u c hc) : Vec d → ℝ) =ᵐ[
      physicalForceMeasure hd lam] fun x => max (densityWeightedH1SpaceValue u x - c) 0 := by
  let ρ := sourceReducedDensity hd lam
  let hρ := continuousSourceReducedDensity hd lam
  let hρpos := positiveSourceReducedDensity hd lam
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  have hp := gmpH1FromGraph_value_ae ρ hρ hρpos
    (gmpWeightedGraphPositivePart ρ hρ hρpos g c hc)
  filter_upwards [hp, gmpH1Representative_value_ae ρ hρ hρpos u] with x hpx hux
  exact hpx.trans (congrArg (fun s => max (s - c) 0) hux)

/-- The force-weighted positive part retains the original gradient above its level. -/
theorem gmpForceH1PositivePart_gradient_ae {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : GMPForceH1 hd lam) (c : ℝ) (hc : 0 ≤ c) :
    (densityWeightedH1SpaceGradient (gmpForceH1PositivePart hd lam u c hc) :
      Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalForceMeasure hd lam]
      {x | c < densityWeightedH1SpaceValue u x}.indicator
        (densityWeightedH1SpaceGradient u) := by
  let ρ := sourceReducedDensity hd lam
  let hρ := continuousSourceReducedDensity hd lam
  let hρpos := positiveSourceReducedDensity hd lam
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  have hp := gmpH1FromGraph_gradient_ae ρ hρ hρpos
    (gmpWeightedGraphPositivePart ρ hρ hρpos g c hc)
  filter_upwards [hp, gmpH1Representative_value_ae ρ hρ hρpos u,
    gmpH1Representative_gradient_ae ρ hρ hρpos u] with x hpx hux hgx
  refine hpx.trans ?_
  change {y | c < g.value y}.indicator g.weakGradient x = _
  change g.value x = _ at hux
  change g.weakGradient x = _ at hgx
  by_cases hx : c < densityWeightedH1SpaceValue u x
  · simp [hux, hgx, hx]
  · simp [hux, hx]

/-- The positive excess above a smooth barrier is an admissible test in the
actual force-weighted H¹ space, with its value and gradient represented almost
everywhere. -/
theorem gmpForceH1PositivePart_sub_barrier_exists {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : GMPForceH1 hd lam) (b : Vec d → ℝ) (hb : ContDiff ℝ 1 b)
    (k : ℝ) (hk : 0 ≤ k)
    (hb0 : ∀ᵐ x ∂physicalForceMeasure hd lam, 0 ≤ b x)
    (hbound : ∀ᵐ x ∂physicalForceMeasure hd lam,
      ‖WithLp.toLp 2 (PDE.classicalGradient b x)‖ ≤ k * b x) :
    ∃ v : GMPForceH1 hd lam,
      (densityWeightedH1SpaceValue v : Vec d → ℝ) =ᵐ[physicalForceMeasure hd lam]
        (fun x => max (densityWeightedH1SpaceValue u x - b x) 0) ∧
      (densityWeightedH1SpaceGradient v : Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[
        physicalForceMeasure hd lam]
        {x | b x < densityWeightedH1SpaceValue u x}.indicator
          (fun x => densityWeightedH1SpaceGradient u x -
            WithLp.toLp 2 (PDE.classicalGradient b x)) := by
  classical
  let ρ := sourceReducedDensity hd lam
  let hρ := continuousSourceReducedDensity hd lam
  let hρpos := positiveSourceReducedDensity hd lam
  let g := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  obtain ⟨w, hwvalue, hwgrad⟩ :=
    gmpWeightedGraphPositivePart_sub_barrier_exists ρ hρ hρpos g b hb k hk hb0 hbound
  refine ⟨gmpH1FromGraph ρ hρ hρpos w, ?_, ?_⟩
  · have hp := gmpH1FromGraph_value_ae ρ hρ hρpos w
    filter_upwards [hp, gmpH1Representative_value_ae ρ hρ hρpos u] with x hpx hux
    rw [hwvalue] at hpx
    exact hpx.trans (congrArg (fun s => max (s - b x) 0) hux)
  · have hp := gmpH1FromGraph_gradient_ae ρ hρ hρpos w
    filter_upwards [hp, gmpH1Representative_value_ae ρ hρ hρpos u,
      gmpH1Representative_gradient_ae ρ hρ hρpos u] with x hpx hux hgx
    rw [hwgrad] at hpx
    refine hpx.trans ?_
    change g.value x = _ at hux
    change g.weakGradient x = _ at hgx
    by_cases hx : b x < densityWeightedH1SpaceValue u x
    · simp [hux, hgx, hx]
    · simp [hux, hx]

/-- Changing to the actual physical measure preserves the full graph gradient. -/
theorem gmpPhysicalH1Gradient_ae_spaceGradient {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u :
      Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      densityWeightedH1SpaceGradient u :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) (densityWeightedH1SpaceGradient u)

/-- The physical positive-part value has its literal representative. -/
theorem gmpPhysicalH1PositivePart_value_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) (c : ℝ) (hc : 0 ≤ c) :
    (gmpPhysicalH1Value hd ω lam Λ hω (gmpForceH1PositivePart hd lam u c hc) :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        fun x => max (gmpPhysicalH1Value hd ω lam Λ hω u x - c) 0 := by
  have hp := (gmp_force_ae_iff_physical hd ω lam _).mp
    (gmpForceH1PositivePart_value_ae hd lam u c hc)
  filter_upwards [hp, gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u,
    gmpPhysicalH1Value_ae_eq hd ω lam Λ hω (gmpForceH1PositivePart hd lam u c hc)]
      with x hpx hux hvx
  exact hvx.trans (hpx.trans (congrArg (fun s => max (s - c) 0) hux.symm))

/-- The physical positive-part gradient has its literal representative. -/
theorem gmpPhysicalH1PositivePart_gradient_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) (c : ℝ) (hc : 0 ≤ c) :
    (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
      (gmpForceH1PositivePart hd lam u c hc) : Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      {x | c < gmpPhysicalH1Value hd ω lam Λ hω u x}.indicator
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u) := by
  have hp := (gmp_force_ae_iff_physical hd ω lam _).mp
    (gmpForceH1PositivePart_gradient_ae hd lam u c hc)
  filter_upwards [hp, gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u,
    gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam Λ hω u,
    gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam Λ hω
      (gmpForceH1PositivePart hd lam u c hc)] with x hpx hux hgx hvx
  rw [hvx, hpx]
  by_cases hx : c < densityWeightedH1SpaceValue u x <;> simp [hux, hgx, hx]


/-- Unit truncation as the difference of two positive parts. -/
def gmpForceH1UnitTruncation {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u : GMPForceH1 hd lam) : GMPForceH1 hd lam :=
  gmpForceH1PositivePart hd lam u 0 (by norm_num) -
    gmpForceH1PositivePart hd lam u 1 (by norm_num)

private theorem gmp_unitTruncation_eq (s : ℝ) :
    max (s - 0) 0 - max (s - 1) 0 =
      SubdiffusiveProcess.DirichletForm.unitTruncation s := by
  unfold SubdiffusiveProcess.DirichletForm.unitTruncation
  by_cases h0 : s ≤ 0
  · have h1 : s ≤ 1 := by linarith
    have hs1 : s - 1 ≤ 0 := by linarith
    simp only [sub_zero, max_eq_right h0, max_eq_right hs1, min_eq_left h1, sub_self]
  · have h0' : 0 ≤ s := le_of_lt (lt_of_not_ge h0)
    by_cases h1 : s ≤ 1
    · have hs1 : s - 1 ≤ 0 := by linarith
      simp only [sub_zero, max_eq_left h0', max_eq_right hs1, min_eq_left h1]
    · have h1' : 1 ≤ s := le_of_lt (lt_of_not_ge h1)
      have hs1 : 0 ≤ s - 1 := by linarith
      simp [max_eq_left h0', max_eq_left hs1, min_eq_right h1']

/-- Physical unit truncation has its literal clipped representative and gradient. -/
theorem gmpPhysicalH1UnitTruncation_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    ((gmpPhysicalH1Value hd ω lam Λ hω (gmpForceH1UnitTruncation hd lam u) :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        fun x => SubdiffusiveProcess.DirichletForm.unitTruncation
          (gmpPhysicalH1Value hd ω lam Λ hω u x)) ∧
    ((gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
      (gmpForceH1UnitTruncation hd lam u) : Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      {x | 0 < gmpPhysicalH1Value hd ω lam Λ hω u x ∧
        gmpPhysicalH1Value hd ω lam Λ hω u x ≤ 1}.indicator
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u)) := by
  let p := gmpForceH1PositivePart hd lam u 0 (by norm_num)
  let q := gmpForceH1PositivePart hd lam u 1 (by norm_num)
  let V := gmpPhysicalH1ValueLinear hd ω lam Λ hω
  let G := gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
  have hpv := gmpPhysicalH1PositivePart_value_ae hd ω lam Λ hω u 0 (by norm_num)
  have hpg := gmpPhysicalH1PositivePart_gradient_ae hd ω lam Λ hω u 0 (by norm_num)
  have hqv := gmpPhysicalH1PositivePart_value_ae hd ω lam Λ hω u 1 (by norm_num)
  have hqg := gmpPhysicalH1PositivePart_gradient_ae hd ω lam Λ hω u 1 (by norm_num)
  constructor
  · change (V (p - q) : Vec d → ℝ) =ᵐ[_] _
    filter_upwards [hpv, hqv, Lp.coeFn_sub (V p) (V q)] with x hp hq hs
    change (V p : Vec d → ℝ) x = _ at hp
    change (V q : Vec d → ℝ) x = _ at hq
    rw [map_sub, hs, Pi.sub_apply, hp, hq]
    exact gmp_unitTruncation_eq _
  · change (G (p - q) : Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[_] _
    filter_upwards [hpg, hqg, Lp.coeFn_sub (G p) (G q)] with x hp hq hs
    change (G p : Vec d → EuclideanSpace ℝ (Fin d)) x = _ at hp
    change (G q : Vec d → EuclideanSpace ℝ (Fin d)) x = _ at hq
    rw [map_sub, hs, Pi.sub_apply, hp, hq]
    by_cases h0 : 0 < gmpPhysicalH1Value hd ω lam Λ hω u x
    · by_cases h1 : gmpPhysicalH1Value hd ω lam Λ hω u x ≤ 1
      · simp [h0, h1, not_lt.mpr h1]
      · simp [h0, h1, lt_of_not_ge h1]
    · have h1 : ¬ 1 < gmpPhysicalH1Value hd ω lam Λ hω u x := by linarith
      simp [h0, h1]

/-- Unit truncation decreases the actual anisotropic physical energy. -/
theorem gmpPhysicalH1Energy_unitTruncation_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam) :
    gmpPhysicalH1Energy hd ω lam Λ hω (gmpForceH1UnitTruncation hd lam u)
      (gmpForceH1UnitTruncation hd lam u) ≤ gmpPhysicalH1Energy hd ω lam Λ hω u u := by
  apply integral_mono_ae
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω _ _)
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω _ _)
  filter_upwards [(gmpPhysicalH1UnitTruncation_ae hd ω lam Λ hω u).2] with x hx
  rw [hx]
  by_cases h : 0 < gmpPhysicalH1Value hd ω lam Λ hω u x ∧
      gmpPhysicalH1Value hd ω lam Λ hω u x ≤ 1
  · simp [h]
  · simp only [Set.indicator_apply, Set.mem_setOf_eq, if_neg h,
      WithLp.ofLp_zero, Matrix.mulVec_zero,
      dot, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
    apply mul_nonneg (by norm_num)
    let ξ := WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x)
    have hsq : 0 ≤ euclideanSq ξ := by
      change 0 ≤ ∑ i, ξ i * ξ i
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    exact (mul_nonneg (inv_nonneg.mpr (le_trans zero_le_one hΛ)) hsq).trans
      ((hω.1 x).2 ξ).1

/-- The actual full physical weighted form is a Dirichlet form. -/
def gmpPhysicalDirichletForm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    SubdiffusiveProcess.DirichletForm (physicalReversibleMeasure ω hd lam) where
  toClosedForm := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  markov := by
    rintro f ⟨u, rfl⟩ v hv
    let w := gmpForceH1UnitTruncation hd lam u
    have heq : v = gmpPhysicalH1Value hd ω lam Λ hω w := by
      apply Lp.ext
      exact hv.trans (gmpPhysicalH1UnitTruncation_ae hd ω lam Λ hω u).1.symm
    subst v
    constructor
    · exact ⟨w, rfl⟩
    · change gmpPhysicalH1Form hd ω lam Λ hω
        (gmpPhysicalH1Value hd ω lam Λ hω w) (gmpPhysicalH1Value hd ω lam Λ hω w) ≤
        gmpPhysicalH1Form hd ω lam Λ hω
          (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω u)
      rw [gmpPhysicalH1Form_value, gmpPhysicalH1Form_value]
      exact gmpPhysicalH1Energy_unitTruncation_le hd ω lam Λ hΛ hω u
/-- The Dirichlet form retains exactly the literal source weighted-H¹ domain. -/
theorem mem_gmpPhysicalDirichletForm_domain_iff {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    f ∈ (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω).domain ↔
      physicalH1Member ω hd lam f :=
  mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f

/-- The Dirichlet form retains the source energy on the entire weighted-H¹ domain. -/
theorem gmpPhysicalDirichletForm_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (u v : GMPForceH1 hd lam) :
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω).form
      (gmpPhysicalH1Value hd ω lam Λ hω u) (gmpPhysicalH1Value hd ω lam Λ hω v) =
      sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u v :=
  gmpPhysicalClosedForm_value hd ω lam Λ hΛ hω u v

/-- The variational resolvent of the actual full physical Dirichlet form. -/
def gmpPhysicalResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  Classical.choose (SubdiffusiveProcess.DirichletForm.FOTConstruction.exists_resolvent
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω) α hα)

/-- The physical resolvent satisfies the equation on the entire source domain. -/
theorem gmpPhysicalResolvent_isResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    SubdiffusiveProcess.DirichletForm.IsResolvent
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω) α
      (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα) :=
  Classical.choose_spec (SubdiffusiveProcess.DirichletForm.FOTConstruction.exists_resolvent
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω) α hα)

/-- A resolvent value has the literal full physical weighted-H¹ regularity. -/
theorem gmpPhysicalResolvent_physicalH1Member {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalH1Member ω hd lam (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f) :=
  (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mp
    ((gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα).mem_domain f)

/-- The full force-weighted weak-gradient solution of the physical resolvent equation. -/
def gmpPhysicalResolventH1 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : GMPForceH1 hd lam :=
  (gmpPhysicalH1DomainEquiv hd ω lam Λ hω).symm
    ⟨gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f,
      (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα).mem_domain f⟩

/-- The weak-gradient solution represents exactly the physical L² resolvent. -/
theorem gmpPhysicalResolventH1_value {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpPhysicalH1Value hd ω lam Λ hω
      (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) =
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  exact congrArg Subtype.val ((gmpPhysicalH1DomainEquiv hd ω lam Λ hω).apply_symm_apply _)

/-- The literal physical integral equation holds against every full weighted-H¹ test. -/
theorem gmpPhysicalResolvent_weakEquation {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (v : GMPForceH1 hd lam) :
    α * (∫ x, gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x *
      gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) +
      gmpPhysicalH1Energy hd ω lam Λ hω
        (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) v =
      ∫ x, f x * gmpPhysicalH1Value hd ω lam Λ hω v x
        ∂physicalReversibleMeasure ω hd lam := by
  have h := (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα).eq f
    (v := gmpPhysicalH1Value hd ω lam Λ hω v) ⟨v, rfl⟩
  change α * inner ℝ _ _ + gmpPhysicalH1Form hd ω lam Λ hω _ _ = _ at h
  rw [← gmpPhysicalResolventH1_value hd ω lam Λ hΛ hω α hα f,
    gmpPhysicalH1Form_value] at h
  rw [gmpPhysicalResolventH1_value] at h
  simpa only [SubdiffusiveProcess.DirichletForm.FOTConstruction.inner_eq_integral_mul] using h

/-- The physical resolvent preserves positivity in its actual reversible measure. -/
theorem gmpPhysicalResolvent_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f) :
    0 ≤ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f :=
  SubdiffusiveProcess.DirichletForm.FOTConstruction.resolvent_positive
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω) hα
    (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα) hf

/-- The scaled physical resolvent maps the unit interval into itself almost everywhere. -/
theorem gmpPhysicalResolvent_submarkov {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hf1 : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ 1) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ∧
      α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ≤ 1 :=
  SubdiffusiveProcess.DirichletForm.FOTConstruction.resolvent_submarkov
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω) hα
    (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα) hf0 hf1

/-- The physical resolvent is symmetric on the actual L² space. -/
theorem gmpPhysicalResolvent_inner_comm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ f (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα g) =
      inner ℝ g (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f) :=
  (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα).inner_comm f g

/-- The physical resolvent has the sharp L² bound at its positive parameter. -/
theorem gmpPhysicalResolvent_norm_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    ‖gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f‖ ≤ ‖f‖ / α := by
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have hG := gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα
  have heq := hG.eq f (hG.mem_domain f)
  have hnonneg := E.form_nonneg (G f) (hG.mem_domain f)
  rw [real_inner_self_eq_norm_sq] at heq
  have hcoer : α * ‖G f‖ ^ 2 ≤ ‖f‖ * ‖G f‖ := by
    linarith [real_inner_le_norm f (G f)]
  by_cases hz : ‖G f‖ = 0
  · change ‖G f‖ ≤ _
    rw [hz]
    exact div_nonneg (norm_nonneg _) hα.le
  · have hp : 0 < ‖G f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hm : (α * ‖G f‖) * ‖G f‖ ≤ ‖f‖ * ‖G f‖ := by nlinarith [hcoer]
    exact (le_div_iff₀ hα).mpr (by nlinarith [le_of_mul_le_mul_right hm hp])

/-- Coercivity identifies full-domain weak solutions at a positive resolvent parameter. -/
theorem gmpClosedForm_variational_ext {X : Type*} [MeasurableSpace X] {m : Measure X}
    (E : SubdiffusiveProcess.DirichletForm.ClosedForm m) {α : ℝ} (hα : 0 < α)
    {u v : Lp ℝ 2 m} (hu : u ∈ E.domain) (hv : v ∈ E.domain)
    (heq : ∀ w ∈ E.domain, α * inner ℝ u w + E.form u w =
      α * inner ℝ v w + E.form v w) : u = v := by
  have hz := E.domain.sub_mem hu hv
  have he := heq (u - v) hz
  have hzero : α * inner ℝ (u - v) (u - v) + E.form (u - v) (u - v) = 0 := by
    rw [inner_sub_left, E.form_sub_left hu hv hz]
    linarith [he]
  rw [real_inner_self_eq_norm_sq] at hzero
  have hp := E.form_nonneg (u - v) hz
  have hs : ‖u - v‖ ^ 2 ≤ 0 :=
    le_of_mul_le_mul_left (show α * ‖u - v‖ ^ 2 ≤ α * 0 by linarith [hzero]) hα
  have hn : ‖u - v‖ = 0 := by nlinarith [hs, norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- No other full-domain weak solution can differ from the physical resolvent. -/
theorem gmpPhysicalResolvent_unique {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hu : physicalH1Member ω hd lam u)
    (heq : ∀ v ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain,
      α * inner ℝ u v + gmpPhysicalH1Form hd ω lam Λ hω u v = inner ℝ f v) :
    u = gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  have hG := gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα
  apply gmpClosedForm_variational_ext (gmpPhysicalClosedForm hd ω lam Λ hΛ hω) hα
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω u).mpr hu)
    (hG.mem_domain f)
  intro v hv
  exact (heq v hv).trans (hG.eq f hv).symm

/-- The actual physical resolvent is injective because its form domain is dense. -/
theorem gmpPhysicalResolvent_injective {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    Function.Injective (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα) := by
  intro f g hfg
  apply (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).denseDomain.eq_of_inner_left ℝ
  intro v hv
  have hG := gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα
  have hf := hG.eq f hv
  have hg := hG.eq g hv
  rw [hfg] at hf
  exact hf.symm.trans hg

/-- The resolvent has dense range in the actual physical L² space. -/
theorem gmpPhysicalResolvent_denseRange {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    DenseRange (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα) := by
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hs : G.IsSymmetric := by
    intro f g
    calc
      inner ℝ (G f) g = inner ℝ g (G f) := real_inner_comm _ _
      _ = inner ℝ f (G g) := gmpPhysicalResolvent_inner_comm hd ω lam Λ hΛ hω α hα g f
  have h := SubdiffusiveProcess.DirichletForm.FOTConstruction.EnergyHilbert.dense_adjoint_range_of_injective
    G (gmpPhysicalResolvent_injective hd ω lam Λ hΛ hω α hα)
  rw [hs.clm_adjoint_eq] at h
  exact h

/-- The physical resolvents satisfy the two-parameter resolvent identity. -/
theorem gmpPhysicalResolvent_identity {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f -
        gmpPhysicalResolvent hd ω lam Λ hΛ hω β hβ f =
      (β - α) • gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
        (gmpPhysicalResolvent hd ω lam Λ hΛ hω β hβ f) := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let H := gmpPhysicalResolvent hd ω lam Λ hΛ hω β hβ
  have hG := gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα
  have hH := gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω β hβ
  apply gmpClosedForm_variational_ext E hα
    (E.domain.sub_mem (hG.mem_domain f) (hH.mem_domain f))
    (E.domain.smul_mem (β - α) (hG.mem_domain (H f)))
  intro v hv
  change α * inner ℝ (G f - H f) v + E.form (G f - H f) v =
    α * inner ℝ ((β - α) • G (H f)) v + E.form ((β - α) • G (H f)) v
  rw [inner_sub_left, E.form_sub_left (hG.mem_domain f) (hH.mem_domain f) hv,
    real_inner_smul_left, E.form_smul_left (β - α) _ (hG.mem_domain (H f)) _ hv]
  have hg := hG.eq f hv
  have hh := hH.eq f hv
  have hgh := hG.eq (H f) hv
  change α * inner ℝ (G f) v + E.form (G f) v = _ at hg
  change β * inner ℝ (H f) v + E.form (H f) v = _ at hh
  change α * inner ℝ (G (H f)) v + E.form (G (H f)) v = inner ℝ (H f) v at hgh
  nlinarith [hg, hh, hgh]

/-- The constructed solution satisfies the literal source variational-resolvent predicate. -/
theorem gmpPhysicalResolventH1_hasSourceResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    HasSourcePhysicalVariationalResolvent (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 α f
      (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) := by
  refine ⟨hα, ?_⟩
  intro v
  have h := (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α hα).eq f
    (v := gmpPhysicalH1Value hd ω lam Λ hω v) ⟨v, rfl⟩
  rw [← gmpPhysicalResolventH1_value hd ω lam Λ hΛ hω α hα f,
    gmpPhysicalClosedForm_value] at h
  exact h

/-- On every compact smooth test, the resolvent has the actual forced physical generator. -/
theorem gmpPhysicalResolvent_generatorPairing {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    inner ℝ (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f)
      (α • gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
        EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) =
      inner ℝ f (gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) := by
  have h := (gmpPhysicalResolventH1_hasSourceResolvent hd ω lam Λ hΛ hω α hα f).2
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  rw [EinsteinFull.C8GMP.compactTest_fullDomain_generatorInner hd Λ ω hω lam hSmooth] at h
  change α * inner ℝ
    (gmpPhysicalH1Value hd ω lam Λ hω (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f)) _ -
    inner ℝ (gmpPhysicalH1Value hd ω lam Λ hω
      (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f)) _ = _ at h
  rw [gmpPhysicalResolventH1_value] at h
  rw [inner_sub_right, real_inner_smul_right]
  exact h

/-- The physical resolvent inverts its actual generator on every compact smooth test. -/
theorem gmpPhysicalResolvent_compactTest {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (α • gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
        EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) =
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) := by
  symm
  apply gmpPhysicalResolvent_unique hd ω lam Λ hΛ hω α hα
  · exact (gmpPhysicalH1Value_range_iff hd ω lam Λ hω _).mp ⟨_, rfl⟩
  · rintro v ⟨w, rfl⟩
    change α * inner ℝ
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) + gmpPhysicalH1Form hd ω lam Λ hω
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) = inner ℝ _ (gmpPhysicalH1Value hd ω lam Λ hω w)
    rw [gmpPhysicalH1Form_value, gmpPhysicalH1Energy_symm,
      gmpPhysicalH1Energy_eq_source,
      EinsteinFull.C8GMP.compactTest_fullDomain_generatorInner hd Λ ω hω lam hSmooth]
    change α * inner ℝ
      (gmpPhysicalH1Value hd ω lam Λ hω (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc))
      (gmpPhysicalH1Value hd ω lam Λ hω w) - inner ℝ (gmpPhysicalH1Value hd ω lam Λ hω w)
      (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) =
      inner ℝ _ (gmpPhysicalH1Value hd ω lam Λ hω w)
    rw [inner_sub_left, real_inner_smul_left,
      real_inner_comm (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc)
        (gmpPhysicalH1Value hd ω lam Λ hω w)]

/-- The physical resolvent recovers the full energy in the high-parameter limit. -/
theorem gmpPhysicalResolvent_formLimit {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    {u v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hu : physicalH1Member ω hd lam u) (hv : physicalH1Member ω hd lam v) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) *
      inner ℝ (u - ((n : ℝ) + 1) •
        gmpPhysicalResolvent hd ω lam Λ hΛ hω ((n : ℝ) + 1) (by positivity) u) v)
      atTop (𝓝 (gmpPhysicalH1Form hd ω lam Λ hω u v)) :=
  SubdiffusiveProcess.DirichletForm.FOTConstruction.tendsto_resolvent_form
    (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω)
    (fun n => gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω ((n : ℝ) + 1) (by positivity))
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω u).mpr hu)
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω v).mpr hv)

/-- The physical resolvent preserves almost-everywhere order. -/
theorem gmpPhysicalResolvent_mono {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hfg : f ≤ᵐ[physicalReversibleMeasure ω hd lam] g) :
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f ≤ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα g := by
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hp : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] g - f := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx he
    simpa only [he, Pi.sub_apply, Pi.zero_apply] using sub_nonneg.mpr hx
  have hG := gmpPhysicalResolvent_positive hd ω lam Λ hΛ hω α hα hp
  rw [map_sub] at hG
  filter_upwards [hG, Lp.coeFn_sub (G g) (G f)] with x hx he
  change 0 ≤ (G g - G f) x at hx
  rw [he] at hx
  exact sub_nonneg.mp hx

/-- Submarkovianity gives the essential-supremum estimate for nonnegative data. -/
theorem gmpPhysicalResolvent_nonneg_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)} {C : ℝ} (hC : 0 < C)
    (hf0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hfC : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ C) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ∧
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ≤ C / α := by
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hs0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] C⁻¹ • f := by
    filter_upwards [hf0, Lp.coeFn_smul C⁻¹ f] with x hx he
    simpa only [he, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using
      mul_nonneg (inv_nonneg.mpr hC.le) hx
  have hs1 : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, (C⁻¹ • f) x ≤ 1 := by
    filter_upwards [hfC, Lp.coeFn_smul C⁻¹ f] with x hx he
    rw [he, Pi.smul_apply, smul_eq_mul]
    calc
      C⁻¹ * f x ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr hC.le)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hb := gmpPhysicalResolvent_submarkov hd ω lam Λ hΛ hω α hα hs0 hs1
  rw [map_smul] at hb
  filter_upwards [hb, Lp.coeFn_smul C⁻¹ (G f)] with x hx he
  change 0 ≤ α * (C⁻¹ • G f) x ∧ α * (C⁻¹ • G f) x ≤ 1 at hx
  rw [he, Pi.smul_apply, smul_eq_mul] at hx
  have h0 := (mul_nonneg_iff_of_pos_left hα).mp hx.1
  have h0 := (mul_nonneg_iff_of_pos_left (inv_pos.mpr hC)).mp h0
  refine ⟨h0, (le_div_iff₀ hα).mpr ?_⟩
  have hc := mul_le_mul_of_nonneg_left hx.2 hC.le
  have heq : C * (α * (C⁻¹ * G f x)) = G f x * α := by field_simp
  simpa only [heq, mul_one] using hc

/-- The actual physical L² resolvent obeys the sharp essential-supremum bound. -/
theorem gmpPhysicalResolvent_abs_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)} {C : ℝ} (hC : 0 < C)
    (hfC : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x| ≤ C / α := by
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let a : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    (Lp.memLp f).norm.toLp (fun x => ‖f x‖)
  have ha : a =ᵐ[physicalReversibleMeasure ω hd lam] fun x => |f x| := by
    filter_upwards [(Lp.memLp f).norm.coeFn_toLp] with x hx
    exact hx.trans (Real.norm_eq_abs _)
  have ha0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] a := by
    filter_upwards [ha] with x hx
    rw [hx]
    exact abs_nonneg _
  have haC : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, a x ≤ C := ha.le.trans hfC
  have hupper := gmpPhysicalResolvent_nonneg_le hd ω lam Λ hΛ hω α hα hC ha0 haC
  have hf : f ≤ᵐ[physicalReversibleMeasure ω hd lam] a := by
    filter_upwards [ha] with x hx
    rw [hx]
    exact le_abs_self _
  have hnf : -f ≤ᵐ[physicalReversibleMeasure ω hd lam] a := by
    filter_upwards [ha, Lp.coeFn_neg f] with x hx hn
    rw [hx, hn]
    exact neg_le_abs _
  have hpos := gmpPhysicalResolvent_mono hd ω lam Λ hΛ hω α hα hf
  have hneg := gmpPhysicalResolvent_mono hd ω lam Λ hΛ hω α hα hnf
  rw [map_neg] at hneg
  filter_upwards [hupper, hpos, hneg, Lp.coeFn_neg (G f)] with x hu hp hn he
  change (-G f) x ≤ G a x at hn
  rw [he] at hn
  change -(G f x) ≤ G a x at hn
  change 0 ≤ G a x ∧ G a x ≤ C / α at hu
  change G f x ≤ G a x at hp
  change |G f x| ≤ C / α
  exact abs_le.mpr ⟨by linarith [hu.2], hp.trans hu.2⟩


/-- A compact smooth full-domain test represents its literal physical value. -/
theorem gmpPhysicalCompactTest_value_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] φ := by
  have hr := gmpH1Representative_value_ae (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  have hp := (Measure.absolutelyContinuous_of_le_smul
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)).ae_eq hr
  exact (gmpPhysicalH1Value_ae_eq hd ω lam Λ hω _).trans
    (hp.symm.trans (EinsteinFull.C8GMP.compactTestDomain_value hd Λ ω hω lam φ hφ hc))

/-- The compact-test generator element retains the actual differential expression. -/
theorem gmpPhysicalCompactTestGenerator_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (hSmooth : IsSmoothFieldPair ω) (lam : ℝ)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] physicalGenerator (firstCoordinateIndex hd) ω lam φ :=
  (EinsteinFull.Work.W5.gantert_memLp_physicalGenerator hd (firstCoordinateIndex hd)
    ω hSmooth lam hφ hc).coeFn_toLp

/-- The scaled physical resolvent differs from a compact test by its resolved generator. -/
theorem gmpPhysicalResolvent_compactTest_sub {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    α • gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) -
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) =
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
      (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) := by
  have h := gmpPhysicalResolvent_compactTest hd ω lam Λ hΛ hω hSmooth α hα φ hφ hc
  rw [map_sub, map_smul] at h
  apply sub_eq_iff_eq_add.mpr
  simpa only [add_comm] using sub_eq_iff_eq_add.mp h

/-- Compact smooth tests are approximated uniformly almost everywhere at rate `C / α`. -/
theorem gmpPhysicalResolvent_compactTest_approximation {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α),
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        |α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) x - φ x| ≤ C / α := by
  obtain ⟨B, hB⟩ := (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator
    (firstCoordinateIndex hd) ω hSmooth lam hφ).continuous.bounded_above_of_compact_support
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator
        (firstCoordinateIndex hd) ω lam hc)
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun α hα => ?_⟩
  let u := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  let f := EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hfC : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C := by
    filter_upwards [gmpPhysicalCompactTestGenerator_ae hd ω hSmooth lam φ hφ hc] with x hx
    change |f x| ≤ C
    rw [hx]
    calc
      |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB x
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hb := gmpPhysicalResolvent_abs_le hd ω lam Λ hΛ hω α hα hC hfC
  have hid : α • G u - u = G f :=
    gmpPhysicalResolvent_compactTest_sub hd ω lam Λ hΛ hω hSmooth α hα φ hφ hc
  have hid' : (α • G u - u : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) =ᵐ[
      physicalReversibleMeasure ω hd lam] G f := Filter.EventuallyEq.of_eq
    (congrArg (fun z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => (z : Vec d → ℝ)) hid)
  filter_upwards [hb, hid', Lp.coeFn_sub (α • G u) u, Lp.coeFn_smul α (G u),
    gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc] with x hx he hs hm hu
  change |α * G u x - φ x| ≤ C / α
  change |G f x| ≤ C / α at hx
  change (α • G u - u) x = G f x at he
  rw [hs, Pi.sub_apply, hm, Pi.smul_apply, smul_eq_mul, hu] at he
  exact he.symm ▸ hx

/-- The scaled physical resolvents converge uniformly almost everywhere on compact smooth tests. -/
theorem gmpPhysicalResolvent_compactTest_eventually {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |((n : ℝ) + 1) *
        gmpPhysicalResolvent hd ω lam Λ hΛ hω ((n : ℝ) + 1) (by positivity)
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) x - φ x| < ε := by
  obtain ⟨C, _hC, hbound⟩ :=
    gmpPhysicalResolvent_compactTest_approximation hd ω lam Λ hΛ hω hSmooth φ hφ hc
  have ht : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  exact (hbound ((n : ℝ) + 1) (by positivity)).mono fun x hx => hx.trans_lt hn


/-- Null sets for the actual positive physical density are precisely Lebesgue null sets. -/
theorem gmpPhysical_ae_iff_volume {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (P : Vec d → Prop) :
    (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, P x) ↔ ∀ᵐ x ∂volume, P x := by
  change (∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal
    (sourcePhysicalDensity ω hd lam x)), P x) ↔ _
  rw [ae_withDensity_iff (continuousSourcePhysicalDensity ω hd lam).measurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (positiveSourcePhysicalDensity ω hd lam x)))
  · exact fun h => h.mono fun _ hx _ => hx

/-- Integration against the actual reversible measure keeps its literal exponential density. -/
theorem gmpPhysical_integral_eq_volume {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) :
    (∫ x, f x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, sourcePhysicalDensity ω hd lam x * f x := by
  change (∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal
    (sourcePhysicalDensity ω hd lam x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (continuousSourcePhysicalDensity ω hd lam).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_of_lt (positiveSourcePhysicalDensity ω hd lam _)),
    smul_eq_mul]

/-- The physical resolvent as an actual weighted weak-gradient graph. -/
def gmpPhysicalResolventGraph {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    WeightedSobolevGraph (physicalReversibleMeasure ω hd lam) :=
  sourcePhysicalGraph (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
    (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
    (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω)
    (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f)

/-- The weak-gradient graph represents the physical resolvent also in Lebesgue measure. -/
theorem gmpPhysicalResolventGraph_value_ae {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value =ᵐ[volume]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  apply (gmpPhysical_ae_iff_volume hd ω lam _).mp
  have h := (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value_memLp.coeFn_toLp
  change (gmpPhysicalH1Value hd ω lam Λ hω
    (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) : Vec d → ℝ) =ᵐ[_] _ at h
  rw [gmpPhysicalResolventH1_value] at h
  exact h.symm

/-- Every physical resolvent has ordinary local H¹ regularity on bounded balls. -/
def gmpPhysicalResolventLocalH1 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (x : Vec d) (r : ℝ) :
    PDE.H1Function (Metric.ball x r) :=
  gmpWeightedGraphLocalH1 (sourcePhysicalDensity ω hd lam)
    (continuousSourcePhysicalDensity ω hd lam) (positiveSourcePhysicalDensity ω hd lam)
    (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f) x r

/-- Compact tests in the full physical energy have their actual differential gradients. -/
theorem gmpPhysicalH1Energy_compactTest {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : GMPForceH1 hd lam)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalH1Energy hd ω lam Λ hω u
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) =
    ∫ x, (1 / 2 : ℝ) * dot
      (WithLp.ofLp ((sourcePhysicalGraph (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u).weakGradient x))
      ((ω.1 x).mulVec (gradient φ x)) ∂physicalReversibleMeasure ω hd lam := by
  rw [gmpPhysicalH1Energy_eq_source]
  apply integral_congr_ae
  filter_upwards [EinsteinFull.C8GMP.compactTestDomain_gradient hd Λ ω hω lam φ hφ hc]
    with x hx
  change (1 / 2 : ℝ) * dot _ ((ω.1 x).mulVec
    (WithLp.ofLp ((densityWeightedH1SpaceRepresentative _ _ _
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)).weakGradient x))) = _
  rw [hx]
  rfl

/-- The actual anisotropic physical resolvent satisfies the local divergence identity.
The right-hand side is the literal inhomogeneous residual, with Lebesgue measure. -/
theorem gmpPhysicalResolvent_divergenceEquation {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, sourcePhysicalDensity ω hd lam x * dot
      (WithLp.ofLp ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient x))
      ((ω.1 x).mulVec (gradient φ x))) =
    ∫ x, (2 * sourcePhysicalDensity ω hd lam x *
      (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x)) * φ x := by
  let u := gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f
  let v := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  have hv : (v : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] φ :=
    gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc
  have hu := (gmpPhysical_ae_iff_volume hd ω lam _).mpr
    (gmpPhysicalResolventGraph_value_ae hd ω lam Λ hΛ hω α hα f)
  change u.value =ᵐ[physicalReversibleMeasure ω hd lam]
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f at hu
  have hGφ : Integrable (fun x =>
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x * φ x)
      (physicalReversibleMeasure ω hd lam) :=
    ((Lp.memLp (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f)).integrable_mul
      (Lp.memLp v)).congr (hv.mono fun x hx => by simp only [Pi.mul_apply, hx])
  have hfφ : Integrable (fun x => f x * φ x) (physicalReversibleMeasure ω hd lam) :=
    ((Lp.memLp f).integrable_mul (Lp.memLp v)).congr
      (hv.mono fun x hx => by simp only [Pi.mul_apply, hx])
  have h := gmpPhysicalResolvent_weakEquation hd ω lam Λ hΛ hω α hα f
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  rw [gmpPhysicalH1Energy_compactTest] at h
  have hleft : (∫ x, gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x * v x
      ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, u.value x * φ x ∂physicalReversibleMeasure ω hd lam := by
    apply integral_congr_ae
    filter_upwards [hv, hu] with x hx hy
    rw [hx, hy]
  have hright : (∫ x, f x * v x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x, f x * φ x ∂physicalReversibleMeasure ω hd lam :=
    integral_congr_ae (hv.mono fun x hx => by dsimp only; rw [hx])
  change α * (∫ x, _ * v x ∂_) + _ = ∫ x, f x * v x ∂_ at h
  rw [hleft, hright] at h
  have huφ : Integrable (fun x => u.value x * φ x) (physicalReversibleMeasure ω hd lam) :=
    hGφ.congr (hu.mono fun x hx => by dsimp only; rw [hx])
  have hr : (∫ x, (2 * (f x - α * u.value x)) * φ x
      ∂physicalReversibleMeasure ω hd lam) =
      2 * ((∫ x, f x * φ x ∂physicalReversibleMeasure ω hd lam) -
        α * ∫ x, u.value x * φ x ∂physicalReversibleMeasure ω hd lam) := by
    simp_rw [show ∀ x, (2 * (f x - α * u.value x)) * φ x =
      2 * (f x * φ x - α * (u.value x * φ x)) by intro x; ring]
    rw [integral_const_mul, integral_sub hfφ (huφ.const_mul α), integral_const_mul]
  rw [gmpPhysical_integral_eq_volume] at hr
  have hr' : (∫ x, (2 * sourcePhysicalDensity ω hd lam x *
      (f x - α * u.value x)) * φ x) =
      2 * ((∫ x, f x * φ x ∂physicalReversibleMeasure ω hd lam) -
        α * ∫ x, u.value x * φ x ∂physicalReversibleMeasure ω hd lam) := by
    convert hr using 1
    congr 1
    funext x
    ring
  have he : (∫ x, sourcePhysicalDensity ω hd lam x *
      (dot (WithLp.ofLp (u.weakGradient x)) ((ω.1 x).mulVec (gradient φ x)))) =
      2 * (∫ x, (1 / 2 : ℝ) *
        dot (WithLp.ofLp (u.weakGradient x)) ((ω.1 x).mulVec (gradient φ x))
        ∂physicalReversibleMeasure ω hd lam) := by
    rw [gmpPhysical_integral_eq_volume, ← integral_const_mul]
    congr 1
    funext x
    ring
  change (∫ x, sourcePhysicalDensity ω hd lam x *
    dot (WithLp.ofLp (u.weakGradient x)) ((ω.1 x).mulVec (gradient φ x))) = _
  rw [he, hr']
  change α * (∫ x, u.value x * φ x ∂physicalReversibleMeasure ω hd lam) +
    (∫ x, (1 / 2 : ℝ) * dot (WithLp.ofLp (u.weakGradient x))
      ((ω.1 x).mulVec (gradient φ x)) ∂physicalReversibleMeasure ω hd lam) = _ at h
  linarith


/-- Lebesgue measure is absolutely continuous with respect to the actual physical measure. -/
theorem gmpVolume_absolutelyContinuous_physical {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) : volume ≪ physicalReversibleMeasure ω hd lam :=
  withDensity_absolutelyContinuous'
    (continuousSourcePhysicalDensity ω hd lam).measurable.ennreal_ofReal.aemeasurable
    (ae_of_all _ fun x => ne_of_gt
      (ENNReal.ofReal_pos.mpr (positiveSourcePhysicalDensity ω hd lam x)))

/-- Bounded physical data give a literal locally bounded divergence residual. -/
theorem gmpPhysicalResolvent_residual_bound {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C) :
    ∀ᵐ x ∂volume,
      |2 * sourcePhysicalDensity ω hd lam x *
        (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x)| ≤
      4 * C * sourcePhysicalDensity ω hd lam x := by
  have hb := (gmpPhysical_ae_iff_volume hd ω lam _).mp
    (gmpPhysicalResolvent_abs_le hd ω lam Λ hΛ hω α hα hC hf)
  have hf' := (gmpPhysical_ae_iff_volume hd ω lam _).mp hf
  filter_upwards [hb, hf', gmpPhysicalResolventGraph_value_ae hd ω lam Λ hΛ hω α hα f]
    with x hx hfx hu
  rw [hu]
  have hmul : α * |gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x| ≤ C := by
    simpa only [mul_comm] using (le_div_iff₀ hα).mp hx
  have habs : |f x - α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x| ≤ 2 * C := by
    calc
      _ ≤ |f x| + |α * gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x| := abs_sub _ _
      _ = |f x| + α * |gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x| := by
        rw [abs_mul, abs_of_pos hα]
      _ ≤ 2 * C := by linarith
  rw [abs_mul, abs_of_pos (mul_pos (by norm_num : (0 : ℝ) < 2)
    (positiveSourcePhysicalDensity ω hd lam x))]
  calc
    _ ≤ (2 * sourcePhysicalDensity ω hd lam x) * (2 * C) :=
      mul_le_mul_of_nonneg_left habs
        (mul_nonneg (by norm_num) (positiveSourcePhysicalDensity ω hd lam x).le)
    _ = _ := by ring

/-- On every compact set the actual divergence residual has a finite essential bound. -/
theorem gmpPhysicalResolvent_residual_compact_bound {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ᵐ x ∂volume.restrict K,
      |2 * sourcePhysicalDensity ω hd lam x *
        (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x)| ≤ B := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image (continuousSourcePhysicalDensity ω hd lam).continuousOn
  refine ⟨4 * C * (max B 0 + 1), by positivity, ?_⟩
  filter_upwards [ae_restrict_of_ae
    (gmpPhysicalResolvent_residual_bound hd ω lam Λ hΛ hω α hα f hC hf),
    ae_restrict_mem hK.measurableSet] with x hx hxK
  apply hx.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ 4 * C)
  exact (hB (mem_image_of_mem _ hxK)).trans (by linarith [le_max_left B 0])

/-- The literal anisotropic divergence residual belongs to every local `Lᵖ` space. -/
theorem gmpPhysicalResolvent_residual_memLp_compact {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    {K : Set (Vec d)} (hK : IsCompact K) (p : ℝ≥0∞) :
    MemLp (fun x => 2 * sourcePhysicalDensity ω hd lam x *
      (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x))
      p (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hfac := gmpVolume_absolutelyContinuous_physical hd ω lam
  have hfmeas := (Lp.memLp f).aestronglyMeasurable.mono_ac hfac
  have humeas := (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value_memLp.aestronglyMeasurable.mono_ac hfac
  have hmeas : AEStronglyMeasurable (fun x => 2 * sourcePhysicalDensity ω hd lam x *
      (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x)) volume :=
    (((continuous_const.mul (continuousSourcePhysicalDensity ω hd lam)).aestronglyMeasurable).mul
      (hfmeas.sub (humeas.const_mul α)))
  obtain ⟨B, _hB, hb⟩ :=
    gmpPhysicalResolvent_residual_compact_bound hd ω lam Λ hΛ hω α hα f hC hf hK
  exact MemLp.of_bound hmeas.restrict B (by simpa only [Real.norm_eq_abs] using hb)

/-- The physical divergence coefficient retains the actual continuous anisotropic matrix. -/
theorem gmpPhysicalCoefficient_continuous {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) : Continuous (fun x => sourcePhysicalDensity ω hd lam x • ω.1 x) :=
  (continuousSourcePhysicalDensity ω hd lam).smul ω.1.continuous

/-- Source Euclidean ellipticity includes the inverse coercivity of the PDE interface. -/
theorem gmpRegular_ellipticMatrix {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (x : Vec d) :
    PDE.IsEllipticMatrix Λ⁻¹ Λ (ω.1 x) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  refine ⟨inv_pos.mpr hΛpos, (inv_le_one_of_one_le₀ hΛ).trans hΛ, ?_, ?_⟩
  · intro ξ
    exact ((hω.1 x).2 ξ).1
  · intro ξ
    exact (((EinsteinRelation.Correctors.isElliptic_inverse hΛpos hω.1) x).2 ξ).1

/-- The actual physical coefficient is uniformly elliptic on every compact window. -/
theorem gmpPhysicalCoefficient_elliptic_compact {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    {K : Set (Vec d)} (hK : IsCompact K) :
    ∃ ell upper : ℝ, PDE.IsEllipticFieldOn ell upper K
      (fun x => sourcePhysicalDensity ω hd lam x • ω.1 x) := by
  classical
  have hmeas : Measurable (fun x i j => if x ∈ K then
      (sourcePhysicalDensity ω hd lam x • ω.1 x) i j else 0) := by
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    exact (((continuous_apply j).comp ((continuous_apply i).comp
      (gmpPhysicalCoefficient_continuous hd ω lam))).measurable.piecewise
        hK.measurableSet measurable_const)
  rcases K.eq_empty_or_nonempty with hEmpty | hNonempty
  · exact ⟨1, 1, hmeas, by simp [hEmpty]⟩
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hNonempty
    (continuousSourcePhysicalDensity ω hd lam).continuousOn
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuousSourcePhysicalDensity ω hd lam).continuousOn
  refine ⟨sourcePhysicalDensity ω hd lam z * Λ⁻¹, B * Λ, hmeas, ?_⟩
  intro x hx
  have hmin : sourcePhysicalDensity ω hd lam z ≤ sourcePhysicalDensity ω hd lam x :=
    hzmin hx
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  exact (PDE.isEllipticMatrix_smul (positiveSourcePhysicalDensity ω hd lam x)
    (gmpRegular_ellipticMatrix hΛ ω hω x)).mono
      (mul_pos (positiveSourcePhysicalDensity ω hd lam z) (inv_pos.mpr hΛpos))
      (mul_le_mul_of_nonneg_right hmin (inv_nonneg.mpr hΛpos.le))
      (mul_le_mul_of_nonneg_right (hB (mem_image_of_mem _ hx)) hΛpos.le)

/-- Even without a bounded-data assumption, the physical residual is locally `L²`. -/
theorem gmpPhysicalResolvent_residual_memL2_compact {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {K : Set (Vec d)} (hK : IsCompact K) :
    MemLp (fun x => 2 * sourcePhysicalDensity ω hd lam x *
      (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x))
      2 (volume.restrict K) := by
  let u := gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f
  have hfLocal := gmpWeightedMemLp_restrict_isCompact (sourcePhysicalDensity ω hd lam)
    (continuousSourcePhysicalDensity ω hd lam) (positiveSourcePhysicalDensity ω hd lam)
    (Lp.memLp f) hK
  have huLocal := gmpWeightedMemLp_restrict_isCompact (sourcePhysicalDensity ω hd lam)
    (continuousSourcePhysicalDensity ω hd lam) (positiveSourcePhysicalDensity ω hd lam)
    u.value_memLp hK
  have hres := hfLocal.sub (huLocal.const_mul α)
  obtain ⟨B, hB⟩ := hK.bddAbove_image
    (continuousSourcePhysicalDensity ω hd lam).continuousOn
  refine hres.of_le_mul (c := 2 * B)
    (((continuous_const.mul (continuousSourcePhysicalDensity ω hd lam)).aestronglyMeasurable.restrict).mul
      hres.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (positiveSourcePhysicalDensity ω hd lam x)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hB (mem_image_of_mem _ hx)) (by norm_num : (0 : ℝ) ≤ 2))
    (abs_nonneg _)

/-- The source and PDE test gradients agree in each actual Euclidean coordinate. -/
theorem gmpWeakTestFunction_grad {d : ℕ} {U : Set (Vec d)}
    (φ : PDE.WeakTestFunction U) : φ.grad = gradient φ.toFun := rfl

/-- The actual local resolvent is a weak divergence solution with genuine `L²` data.
Both the coefficient and inhomogeneous residual are the literal physical fields. -/
theorem gmpPhysicalResolvent_localWeakL2 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (x : Vec d) (r : ℝ) :
    PDE.IsWeakDivergenceFormL2SolutionOn
      (fun y => sourcePhysicalDensity ω hd lam y • ω.1 y) (Metric.ball x r)
      (gmpPhysicalResolventLocalH1 hd ω lam Λ hΛ hω α hα f x r)
      (fun y => 2 * sourcePhysicalDensity ω hd lam y *
        (f y - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value y))
      (fun _ => 0) := by
  let u := gmpPhysicalResolventLocalH1 hd ω lam Λ hΛ hω α hα f x r
  obtain ⟨ell, upper, hEll⟩ := gmpPhysicalCoefficient_elliptic_compact hd hΛ ω hω lam
    (isCompact_closedBall x r)
  have hdata : PDE.DivergenceFormL2DataOn
      (fun y => sourcePhysicalDensity ω hd lam y • ω.1 y) (Metric.ball x r) u
      (fun y => 2 * sourcePhysicalDensity ω hd lam y *
        (f y - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value y))
      (fun _ => 0) :=
    PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn
      (hEll.mono Metric.isOpen_ball.measurableSet Metric.ball_subset_closedBall)
      ((gmpPhysicalResolvent_residual_memL2_compact hd ω lam Λ hΛ hω α hα f
        (isCompact_closedBall x r)).mono_measure
          (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl))
      (by intro i; exact MemLp.zero)
  refine { hdata with identity := ?_ }
  intro φ
  have hgradZero : ∀ y ∈ (Metric.ball x r)ᶜ, φ.grad y = 0 := by
    intro y hy
    have hyt : y ∉ tsupport φ.toFun := fun hy' => hy (φ.tsupport_subset hy')
    funext i
    simp only [PDE.WeakTestFunction.grad_apply, PDE.WeakTestFunction.partialDeriv]
    rw [fderiv_of_notMem_tsupport ℝ hyt]
    rfl
  have hleft : (∫ y in Metric.ball x r,
      PDE.vecDot (PDE.matVecMul (sourcePhysicalDensity ω hd lam y • ω.1 y) (u.grad y))
        (φ.grad y)) =
      ∫ y, sourcePhysicalDensity ω hd lam y * dot
        (WithLp.ofLp ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient y))
        ((ω.1 y).mulVec (gradient φ.toFun y)) := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hgradZero y hy]; simp [PDE.vecDot])]
    apply integral_congr_ae
    filter_upwards [] with y
    change dot ((sourcePhysicalDensity ω hd lam y • ω.1 y).mulVec
      (WithLp.ofLp ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient y)))
      (gradient φ.toFun y) = _
    rw [Matrix.smul_mulVec]
    change dotProduct (sourcePhysicalDensity ω hd lam y • (ω.1 y).mulVec _)
      (gradient φ.toFun y) = _
    rw [smul_dotProduct, smul_eq_mul]
    congr 1
    change dotProduct _ _ = dotProduct _ _
    conv_lhs =>
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← (hω.1 y).1,
        Matrix.vecMul_transpose]
    exact dotProduct_comm _ _
  have hright : (∫ y in Metric.ball x r,
      (2 * sourcePhysicalDensity ω hd lam y *
        (f y - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value y)) * φ y) =
      ∫ y, (2 * sourcePhysicalDensity ω hd lam y *
        (f y - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value y)) * φ y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hzero : φ.toFun y = 0 := image_eq_zero_of_notMem_tsupport
      (fun hy' => hy (φ.tsupport_subset hy'))
    change _ * φ.toFun y = 0
    rw [hzero, mul_zero]
  change (∫ y in Metric.ball x r,
      PDE.vecDot (PDE.matVecMul (sourcePhysicalDensity ω hd lam y • ω.1 y) (u.grad y))
        (φ.grad y)) = _
  rw [hleft, hright]
  simpa only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    integral_zero, sub_zero] using
    gmpPhysicalResolvent_divergenceEquation hd ω lam Λ hΛ hω α hα f φ.toFun
      φ.contDiff φ.hasCompactSupport

/-- All actual `H¹₀` tests are allowed, by the proved `L²` pairing density extension. -/
theorem gmpPhysicalResolvent_localWeakH10 {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (x : Vec d) (r : ℝ) :
    PDE.IsWeakDivergenceFormH10SolutionOn
      (fun y => sourcePhysicalDensity ω hd lam y • ω.1 y) (Metric.ball x r)
      (gmpPhysicalResolventLocalH1 hd ω lam Λ hΛ hω α hα f x r)
      (fun y => 2 * sourcePhysicalDensity ω hd lam y *
        (f y - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value y))
      (fun _ => 0) :=
  (gmpPhysicalResolvent_localWeakL2 hd ω lam Λ hΛ hω α hα f x r).toH10SolutionOn


/-- Transfer the exact H¹ value and coordinate weak gradient to the cube API. -/
def gmpPDEH1ToHomogenization {d : ℕ} {U : Set (Vec d)} (u : PDE.H1Function U) :
    Homogenization.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

/-- Reuse a cube H¹₀ test with all of its actual supported smooth approximants. -/
def gmpHomogenizationH10ToPDE {d : ℕ} {U : Set (Vec d)}
    (φ : Homogenization.H10Function U) : PDE.H10Function U where
  toH1Function :=
    { toFun := φ.toH1Function.toFun
      grad := φ.toH1Function.grad
      memL2 := φ.toH1Function.memL2
      gradMemL2 := φ.toH1Function.gradMemL2
      hasWeakGradient := φ.toH1Function.hasWeakGradient }
  approx := φ.approx
  approx_smooth := φ.approx_smooth
  approx_hasCompactSupport := φ.approx_hasCompactSupport
  approx_support_subset := φ.approx_support_subset
  tendsto_approx := φ.tendsto_approx
  tendsto_approx_grad := φ.tendsto_approx_grad

/-- A scalar cube datum has a finite-exponent divergence lift, independently of
any coefficient in the equation to which the lift will be applied. -/
theorem gmpScalarCube_finiteLp_divergenceLift {d : ℕ} [NeZero d]
    (m : ℤ) (q : Homogenization.FiniteLpExponent) (hq : 2 < q.exponent.toReal)
    (F : Vec d → ℝ)
    (hF2 : MemLp F 2 (volume.restrict
      (Homogenization.openCubeSet (Homogenization.originCube d m))))
    (hFq : MemLp F q.exponent (volume.restrict
      (Homogenization.openCubeSet (Homogenization.originCube d m)))) :
    ∃ g : Vec d → Vec d,
      (∀ φ : Homogenization.H10Function (Homogenization.openCubeSet (Homogenization.originCube d m)),
        (∫ x in Homogenization.openCubeSet (Homogenization.originCube d m),
          F x * φ.toH1Function.toFun x) =
          -∫ x in Homogenization.openCubeSet (Homogenization.originCube d m),
            PDE.vecDot (g x) (φ.toH1Function.grad x)) ∧
      MemLp (fun x => Homogenization.HilbertVec.ofVec (g x)) q.exponent
        (volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))) := by
  let Q := Homogenization.originCube d m
  obtain ⟨w, hw⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.exists_isScalarDirichletSolutionOn_one
      (Q := Q) (hD := 0) hF2
  have hwMassive :
      SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.IsMassiveWeakSolutionOn
        (fun _ => 1) (fun _ => 1) 0 (Homogenization.openCubeSet Q) w F := by
    intro φ
    have heq := hw.2 φ
    simp_rw [show ∀ x : Vec d, Homogenization.matVecMul (1 : Mat d) (w.grad x) =
        w.grad x from fun x => Matrix.one_mulVec _] at heq
    simpa only [zero_mul, zero_add, one_mul, one_smul] using heq
  obtain ⟨g, hg, _hgWeak, hgLp⟩ :=
    SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.exists_finiteLp_divergence_lift_of_isMassiveWeakSolutionOn
      d q hq (c := fun _ => 1) (rho := fun _ => 1) (mu := 0)
      (u := w) (f := F) (rhoMax := 1) aestronglyMeasurable_const
      (by simp) hF2
      (by
        have hres : SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.massiveResidual
            (fun _ => 1) 0 w F = F := by
          funext x
          simp [SubdiffusiveProcess.CoarseGrainingVocab.Section8Resolvent.massiveResidual]
        rw [hres]
        exact hFq) hwMassive
  refine ⟨g, ?_, hgLp⟩
  intro φ
  simpa only [one_mul, zero_mul, sub_zero, Homogenization.vecDot, PDE.vecDot] using hg φ

/-- On every origin cube, the actual bounded-data anisotropic resolvent has a
finite-exponent divergence datum and keeps its exact physical H¹ representatives. -/
theorem gmpPhysicalResolvent_cubeFiniteLp_divergence {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    (m : ℤ) (q : Homogenization.FiniteLpExponent) (hq : 2 < q.exponent.toReal) :
    ∃ (u : Homogenization.H1Function (Homogenization.openCubeSet (Homogenization.originCube d m)))
      (g : Vec d → Vec d),
      u.toFun = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value ∧
      u.grad = (fun x => WithLp.ofLp
        ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient x)) ∧
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.IsMatrixDivFormWeakSolutionOn
        (fun x => sourcePhysicalDensity ω hd lam x • ω.1 x)
        (Homogenization.openCubeSet (Homogenization.originCube d m)) u g ∧
      MemLp (fun x => Homogenization.HilbertVec.ofVec (g x)) q.exponent
        (volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))) := by
  let : NeZero d := ⟨by omega⟩
  let Q := Homogenization.originCube d m
  let z := Homogenization.cubeCenter Q
  let R := Homogenization.cubeRadius Q + 1
  have hCubeOpen := Homogenization.isOpen_openCubeSet Q
  have hCubeClosed : Homogenization.openCubeSet Q ⊆ Metric.closedBall z R :=
    (Homogenization.openCubeSet_subset_cubeSet Q).trans
      ((Homogenization.cubeSet_subset_closedBall Q).trans
        (Metric.closedBall_subset_closedBall
          (show Homogenization.cubeRadius Q ≤ R by dsimp only [R]; linarith)))
  have hCubeBall : Homogenization.openCubeSet Q ⊆ Metric.ball z R :=
    (Homogenization.openCubeSet_subset_cubeSet Q).trans
      ((Homogenization.cubeSet_subset_closedBall Q).trans
        (Metric.closedBall_subset_ball
          (show Homogenization.cubeRadius Q < R by dsimp only [R]; linarith)))
  let u := (gmpPhysicalResolventLocalH1 hd ω lam Λ hΛ hω α hα f z R).restrict
    hCubeOpen hCubeBall
  let F := fun x => 2 * sourcePhysicalDensity ω hd lam x *
    (f x - α * (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value x)
  have hF2 : MemLp F 2 (volume.restrict (Homogenization.openCubeSet Q)) :=
    (gmpPhysicalResolvent_residual_memL2_compact hd ω lam Λ hΛ hω α hα f
      (isCompact_closedBall z R)).mono_measure (Measure.restrict_mono hCubeClosed le_rfl)
  have hFq : MemLp F q.exponent (volume.restrict (Homogenization.openCubeSet Q)) :=
    (gmpPhysicalResolvent_residual_memLp_compact hd ω lam Λ hΛ hω α hα f hC hf
      (isCompact_closedBall z R) q.exponent).mono_measure
        (Measure.restrict_mono hCubeClosed le_rfl)
  obtain ⟨ell, upper, hEll⟩ :=
    gmpPhysicalCoefficient_elliptic_compact hd hΛ ω hω lam (isCompact_closedBall z R)
  have hRestricted := (gmpPhysicalResolvent_localWeakL2 hd ω lam Λ hΛ hω α hα f z R).toIsWeakDivergenceFormSolutionOn.restrict
    Metric.isOpen_ball hCubeOpen hCubeBall
  have hu := hRestricted.toH10SolutionOn_of_isEllipticFieldOn
    (hEll.mono hCubeOpen.measurableSet hCubeClosed) hF2 (fun _ => MemLp.zero)
  obtain ⟨g, hg, hgLp⟩ := gmpScalarCube_finiteLp_divergenceLift m q hq F hF2 hFq
  refine ⟨gmpPDEH1ToHomogenization u, g, rfl, rfl, ?_, hgLp⟩
  intro φ
  have h := (hu (gmpHomogenizationH10ToPDE φ)).2
  simp only [PDE.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    integral_zero, sub_zero] at h
  exact h.trans (hg φ)

/-- Reverse the H¹ interface without changing either representative. -/
def gmpHomogenizationH1ToPDE {d : ℕ} {U : Set (Vec d)}
    (u : Homogenization.H1Function U) : PDE.H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2
  gradMemL2 := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

/-- A matrix equation tested on all H¹₀ functions supplies the safe PDE
interface when its actual flux and divergence datum are locally square integrable. -/
theorem gmpMatrixDivFormWeakSolution_toPDEL2 {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {a : Vec d → Mat d} {u : Homogenization.H1Function U}
    {F : Vec d → Vec d} {ell upper : ℝ}
    (hEll : PDE.IsEllipticFieldOn ell upper U a)
    (hF : PDE.MemVectorL2On U F)
    (hu : SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.IsMatrixDivFormWeakSolutionOn
      a U u F) :
    PDE.IsWeakDivergenceFormL2SolutionOn a U (gmpHomogenizationH1ToPDE u) 0 F := by
  refine ⟨PDE.DivergenceFormL2DataOn.of_isEllipticFieldOn hEll MemLp.zero hF, ?_⟩
  intro φ
  let ψ := Homogenization.H10Function.ofContDiff hU φ.contDiff
    φ.hasCompactSupport φ.tsupport_subset
  have heq := hu ψ
  simpa only [ψ, Homogenization.H10Function.ofContDiff,
    Homogenization.H1Function.ofContDiff, gmpHomogenizationH1ToPDE,
    Homogenization.vecDot, Homogenization.matVecMul, PDE.vecDot, PDE.matVecMul,
    PDE.WeakTestFunction.grad, PDE.WeakTestFunction.partialDeriv,
    Homogenization.basisVec, PDE.basisVec,
    Pi.zero_apply, zero_mul, integral_zero, zero_sub] using heq

/-- The divergence data of the actual physical resolvent are also in the safe
zero-scalar-source PDE interface, with all finite exponents above two available. -/
theorem gmpPhysicalResolvent_cubeFiniteLp_pde {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    (m : ℤ) (q : Homogenization.FiniteLpExponent) (hq : 2 < q.exponent.toReal) :
    ∃ (u : PDE.H1Function (Homogenization.openCubeSet (Homogenization.originCube d m)))
      (g : Vec d → Vec d),
      u.toFun = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value ∧
      u.grad = (fun x => WithLp.ofLp
        ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient x)) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn
        (fun x => sourcePhysicalDensity ω hd lam x • ω.1 x)
        (Homogenization.openCubeSet (Homogenization.originCube d m)) u 0 g ∧
      MemLp (fun x => Homogenization.HilbertVec.ofVec (g x)) q.exponent
        (volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))) := by
  let Q := Homogenization.originCube d m
  have hOpen := Homogenization.isOpen_openCubeSet Q
  obtain ⟨u, g, huValue, huGrad, hu, hg⟩ :=
    gmpPhysicalResolvent_cubeFiniteLp_divergence hd ω lam Λ hΛ hω α hα f hC hf m q hq
  let : IsFiniteMeasure (volume.restrict (Homogenization.openCubeSet Q)) :=
    ⟨by simpa using (Homogenization.volume_openCubeSet_lt_top Q)⟩
  have htwo : (2 : ℝ≥0∞) ≤ q.exponent := by
    apply (ENNReal.toReal_le_toReal (by norm_num) q.lt_top.ne).mp
    simpa only [ENNReal.toReal_ofNat] using hq.le
  have hg2 := hg.mono_exponent htwo
  have hgCoord : PDE.MemVectorL2On (Homogenization.openCubeSet Q) g := by
    intro i
    exact gmpEuclideanMemLp_coordinate hg2 i
  obtain ⟨ell, upper, hEll⟩ := gmpPhysicalCoefficient_elliptic_compact hd hΛ ω hω lam
    (Homogenization.isBounded_openCubeSet Q).isCompact_closure
  have hPDE := gmpMatrixDivFormWeakSolution_toPDEL2 hOpen
    (hEll.mono hOpen.measurableSet subset_closure) hgCoord hu
  exact ⟨gmpHomogenizationH1ToPDE u, g, huValue, huGrad, hPDE, hg⟩

/-- The pointwise physical coefficient can be rescaled to unit lower ellipticity
without replacing its anisotropic matrix. -/
theorem gmpPhysicalCoefficient_scaledPointElliptic {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (x : Vec d) :
    PDE.IsEllipticMatrix 1 (Λ * Λ)
      ((Λ / sourcePhysicalDensity ω hd lam x) •
        (sourcePhysicalDensity ω hd lam x • ω.1 x)) := by
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  rw [smul_smul, div_mul_cancel₀ _ (positiveSourcePhysicalDensity ω hd lam x).ne']
  simpa only [mul_inv_cancel₀ hΛpos.ne'] using
    PDE.isEllipticMatrix_smul hΛpos (gmpRegular_ellipticMatrix hΛ ω hω x)

/-- The actual lifted resolvent equation under the canonical elliptic change
of variables, with the original representatives and divergence datum retained. -/
theorem gmpPhysicalResolvent_cubeNormalized {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, |f y| ≤ C)
    (x : Vec d) (m : ℤ) (q : Homogenization.FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    ∃ (u : PDE.H1Function (Homogenization.openCubeSet (Homogenization.originCube d m)))
      (g : Vec d → Vec d),
      u.toFun = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value ∧
      u.grad = (fun y => WithLp.ofLp
        ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient y)) ∧
      MemLp (fun y => Homogenization.HilbertVec.ofVec (g y)) q.exponent
        (volume.restrict (Homogenization.openCubeSet (Homogenization.originCube d m))) ∧
      PDE.IsWeakDivergenceFormSolutionOn
        (fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
          ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T)
        (e '' Homogenization.openCubeSet (Homogenization.originCube d m))
        (u.compLinearEquiv e) 0 (fun y => PDE.matVecMul T (k • g (e.symm y))) ∧
      Continuous (fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
        ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T) := by
  let k := Λ / sourcePhysicalDensity ω hd lam x
  let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
  have hA0 : PDE.IsEllipticMatrix 1 (Λ * Λ) A0 :=
    gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x
  let e := PDE.ellipticNormalizerContinuousLinearEquiv hA0
  let T := PDE.ellipticNormalizer A0
  obtain ⟨u, g, huValue, huGrad, hu, hg⟩ :=
    gmpPhysicalResolvent_cubeFiniteLp_pde hd ω lam Λ hΛ hω α hα f hC hf m q hq
  have hscaled : PDE.IsWeakDivergenceFormSolutionOn
      (fun y => k • (sourcePhysicalDensity ω hd lam y • ω.1 y))
      (Homogenization.openCubeSet (Homogenization.originCube d m)) u 0
      (fun y => k • g y) := by
    simpa only [Pi.zero_apply, mul_zero, Pi.zero_def] using
      hu.toIsWeakDivergenceFormSolutionOn.smul_coefficient_source_forcing k
  have hnorm := hscaled.ellipticNormalize hA0
  have hcont : Continuous (fun y => T *
      (k • (sourcePhysicalDensity ω hd lam (e.symm y) • ω.1 (e.symm y)) -
        PDE.skewPart A0) * PDE.matTranspose T) := by
    have hc : Continuous (fun y =>
        sourcePhysicalDensity ω hd lam (e.symm y) • ω.1 (e.symm y)) :=
      (gmpPhysicalCoefficient_continuous hd ω lam).comp e.symm.continuous
    exact (((hc.const_smul k).sub continuous_const).const_mul T).mul_const
      (PDE.matTranspose T)
  exact ⟨u, g, huValue, huGrad, hg, hnorm, hcont⟩

/-- The canonical normalization sends the reference coefficient to the identity. -/
theorem gmpEllipticNormalizer_identity {d : ℕ} {A0 : Mat d} {upper : ℝ}
    (hA0 : PDE.IsEllipticMatrix 1 upper A0) :
    PDE.ellipticNormalizer A0 * (A0 - PDE.skewPart A0) *
      PDE.matTranspose (PDE.ellipticNormalizer A0) = 1 := by
  have h := PDE.ellipticNormalizer_mul_sub_skewPart_mul_transpose_sub_one
    (B := A0) hA0
  simpa only [sub_self, Matrix.mul_zero, Matrix.zero_mul, sub_eq_zero] using h

/-- A continuous matrix coefficient equal to the identity at a point has
arbitrarily small Euclidean operator-norm contrast on a neighborhood. -/
theorem gmpContinuousCoefficient_smallIdentityNeighborhood {d : ℕ}
    {a : Vec d → Mat d} (ha : Continuous a) (x : Vec d) (hx : a x = 1)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball x r,
      Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1) ≤ δ := by
  let L : Mat d →ₗ[ℝ]
      (EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d)) :=
    (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).toAlgEquiv.toLinearMap
  have hL : Continuous L := L.continuous_of_finiteDimensional
  have hc : Continuous (fun y =>
      Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1)) :=
    hL.norm.comp (ha.sub continuous_const)
  have hzero : Homogenization.Book.Ch02.matrixOperatorNorm (a x - 1) = 0 := by
    rw [hx, sub_self, Homogenization.Book.Ch02.matrixOperatorNorm_zero]
  have he : ∀ᶠ y in 𝓝 x,
      Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1) < δ :=
    hc.continuousAt.eventually (gt_mem_nhds (by simpa only [hzero] using hδ))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp he
  exact ⟨r, hr, fun y hy => (hball hy).le⟩

/-- The Euclidean finite-Lᵖ bound survives the same linear coordinate
change and matrix action used by elliptic normalization. -/
theorem gmpEuclideanMemLp_linearChange {d : ℕ} {U : Set (Vec d)}
    {p : ℝ≥0∞} {g : Vec d → Vec d}
    (hg : MemLp (fun y => Homogenization.HilbertVec.ofVec (g y)) p
      (volume.restrict U)) (e : Vec d ≃L[ℝ] Vec d) (T : Mat d) (k : ℝ) :
    MemLp (fun y => Homogenization.HilbertVec.ofVec
      (PDE.matVecMul T (k • g (e.symm y)))) p (volume.restrict (e '' U)) := by
  have hpre : MemLp (fun y => Homogenization.HilbertVec.ofVec (g (e.symm y))) p
      (volume.restrict (e '' U)) := by
    exact PDE.memLpOn_comp_linearEquiv e.symm (U := e '' U)
      (f := fun y => Homogenization.HilbertVec.ofVec (g y))
      (by simpa only [Set.image_image, e.symm_apply_apply, Set.image_id', PDE.volumeOn] using hg)
  have hscaled : MemLp (fun y => (WithLp.toLp 2 (k • g (e.symm y)) :
      Homogenization.HilbertVec d)) p
      (volume.restrict (e '' U)) := by
    simpa only [WithLp.toLp_smul, Pi.smul_apply] using! hpre.const_smul k
  have hmap := (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) T).comp_memLp' hscaled
  simpa only [Function.comp_def, Matrix.toEuclideanCLM_toLp] using! hmap

/-- A small Euclidean operator-norm perturbation of the identity is elliptic
with fixed constants on the unchanged native matrix carrier. -/
theorem gmpMatrixOperatorNorm_small_isElliptic {d : ℕ} {A : Mat d} {δ : ℝ}
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2)
    (hA : Homogenization.Book.Ch02.matrixOperatorNorm (A - 1) ≤ δ) :
    PDE.IsEllipticMatrix (1 / 2) 9 A := by
  have hpert : PDE.IsMatrixPerturbationLE δ A 1 := by
    intro ξ
    have hnorm :=
      Homogenization.Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm
        (A - 1) ξ
    have hbound := hnorm.trans (mul_le_mul_of_nonneg_right hA
      (Homogenization.Book.Ch02.vecNorm_nonneg ξ))
    simpa only [PDE.Vec.vecEuclideanNorm_eq_norm_toHilbertVec,
      PDE.Vec.toHilbertVec, Homogenization.Book.Ch02.vecNorm,
      PDE.matVecMul, Homogenization.matVecMul] using! hbound
  have hone : 0 < 1 - δ := by linarith
  have hscaled := PDE.isEllipticMatrix_inv_one_sub_smul_of_isMatrixPerturbationLE
    hδ0 hδ hpert
  have hback := PDE.isEllipticMatrix_smul hone hscaled
  rw [smul_smul, mul_inv_cancel₀ hone.ne', one_smul] at hback
  exact hback.mono (by norm_num) (by linarith) (by nlinarith)

/-- The actual physical coefficient, under its canonical normalization at a
point, has arbitrarily small contrast on a neighborhood of that point. -/
theorem gmpPhysicalCoefficient_normalized_smallNeighborhood {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω)
    (lam : ℝ) (x : Vec d) {δ : ℝ} (hδ : 0 < δ) :
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Metric.ball (e x) r,
      Homogenization.Book.Ch02.matrixOperatorNorm
        (T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) • ω.1 (e.symm y)) -
          PDE.skewPart A0) * PDE.matTranspose T - 1) ≤ δ := by
  let k := Λ / sourcePhysicalDensity ω hd lam x
  let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
  have hA0 : PDE.IsEllipticMatrix 1 (Λ * Λ) A0 :=
    gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x
  let e := PDE.ellipticNormalizerContinuousLinearEquiv hA0
  let T := PDE.ellipticNormalizer A0
  let a := fun y => T *
    (k • (sourcePhysicalDensity ω hd lam (e.symm y) • ω.1 (e.symm y)) -
      PDE.skewPart A0) * PDE.matTranspose T
  have hc : Continuous (fun y =>
      sourcePhysicalDensity ω hd lam (e.symm y) • ω.1 (e.symm y)) :=
    (gmpPhysicalCoefficient_continuous hd ω lam).comp e.symm.continuous
  have ha : Continuous a :=
    (((hc.const_smul k).sub continuous_const).const_mul T).mul_const
      (PDE.matTranspose T)
  have hax : a (e x) = 1 := by
    dsimp only [a]
    rw [e.symm_apply_apply]
    exact gmpEllipticNormalizer_identity hA0
  exact gmpContinuousCoefficient_smallIdentityNeighborhood ha (e x) hax hδ

/-- Around any point of a cube, the actual normalized resolvent equation
has small contrast, fixed ellipticity, and the transported finite-Lᵖ forcing. -/
theorem gmpPhysicalResolvent_cubeNormalizedLocalData {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, |f y| ≤ C)
    (x : Vec d) (m : ℤ)
    (hx : x ∈ Homogenization.openCubeSet (Homogenization.originCube d m))
    (q : Homogenization.FiniteLpExponent) (hq : 2 < q.exponent.toReal)
    {δ : ℝ} (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    let a := fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
      ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T
    ∃ (u : PDE.H1Function (Homogenization.openCubeSet (Homogenization.originCube d m)))
      (g : Vec d → Vec d) (r : ℝ),
      0 < r ∧ Metric.ball (e x) r ⊆
        e '' Homogenization.openCubeSet (Homogenization.originCube d m) ∧
      u.toFun = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value ∧
      u.grad = (fun y => WithLp.ofLp
        ((gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).weakGradient y)) ∧
      PDE.IsWeakDivergenceFormSolutionOn a
        (e '' Homogenization.openCubeSet (Homogenization.originCube d m))
        (u.compLinearEquiv e) 0 (fun y => PDE.matVecMul T (k • g (e.symm y))) ∧
      MemLp (fun y => Homogenization.HilbertVec.ofVec
        (PDE.matVecMul T (k • g (e.symm y)))) q.exponent
        (volume.restrict (e '' Homogenization.openCubeSet (Homogenization.originCube d m))) ∧
      ∀ y ∈ Metric.ball (e x) r,
        Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1) ≤ δ ∧
        PDE.IsEllipticMatrix (1 / 2) 9 (a y) := by
  let k := Λ / sourcePhysicalDensity ω hd lam x
  let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
  have hA0 : PDE.IsEllipticMatrix 1 (Λ * Λ) A0 :=
    gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x
  let e := PDE.ellipticNormalizerContinuousLinearEquiv hA0
  let T := PDE.ellipticNormalizer A0
  obtain ⟨u, g, huValue, huGrad, hg, hu, _⟩ :=
    gmpPhysicalResolvent_cubeNormalized hd ω lam Λ hΛ hω α hα f hC hf x m q hq
  have hgChange := gmpEuclideanMemLp_linearChange hg e T k
  obtain ⟨s, hs, hsmall⟩ :=
    gmpPhysicalCoefficient_normalized_smallNeighborhood hd hΛ ω hω lam x hδ
  have hOpen : IsOpen (e '' Homogenization.openCubeSet (Homogenization.originCube d m)) :=
    e.isOpenMap _ (Homogenization.isOpen_openCubeSet _)
  obtain ⟨t, ht, hball⟩ := Metric.isOpen_iff.mp hOpen (e x) (Set.mem_image_of_mem e hx)
  refine ⟨u, g, min t s, lt_min ht hs,
    (Metric.ball_subset_ball (min_le_left t s)).trans hball,
    huValue, huGrad, hu, hgChange, ?_⟩
  intro y hy
  have hySmall := hsmall y (Metric.ball_subset_ball (min_le_right t s) hy)
  exact ⟨hySmall, gmpMatrixOperatorNorm_small_isElliptic hδ.le hδhalf hySmall⟩

/-- Every native point lies in the interior of some origin cube. -/
theorem gmpPoint_mem_originCube {d : ℕ} (x : Vec d) :
    ∃ m : ℤ, x ∈ Homogenization.openCubeSet (Homogenization.originCube d m) := by
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * ‖x‖) (by norm_num : (1 : ℝ) < 3)
  refine ⟨(n : ℤ), ?_⟩
  rw [Homogenization.mem_openCubeSet_originCube_iff]
  intro i
  have hi : |x i| ≤ ‖x‖ := norm_le_pi_norm x i
  have hpow : (3 : ℝ) ^ (n : ℤ) = (3 : ℝ) ^ n := zpow_natCast 3 n
  rw [hpow]
  constructor <;> linarith [neg_abs_le (x i), le_abs_self (x i)]

/-- The safe PDE interface supplies all matrix Schauder tests without
changing the value, weak gradient, coefficient, or divergence forcing. -/
theorem gmpWeakDivergenceFormL2_toMatrixDivForm {d : ℕ}
    {U : Set (Vec d)} {a : Vec d → Mat d} {u : PDE.H1Function U}
    {F : Vec d → Vec d}
    (hu : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 F) :
    SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.IsMatrixDivFormWeakSolutionOn
      a U (gmpPDEH1ToHomogenization u) F := by
  intro φ
  have h := (hu.toH10SolutionOn (gmpHomogenizationH10ToPDE φ)).2
  simpa only [gmpPDEH1ToHomogenization, gmpHomogenizationH10ToPDE,
    PDE.vecDot, Homogenization.vecDot, PDE.matVecMul, Homogenization.matVecMul,
    Pi.zero_apply, zero_mul, integral_zero, zero_sub] using h

/-- The matrix Schauder estimate gives an interior continuous representative
for the unchanged safe PDE solution and its actual finite-exponent forcing. -/
theorem gmpMatrixSmallContrast_continuousRepresentative {d : ℕ} (hd : 2 ≤ d)
    {a : Vec d → Mat d}
    {u : PDE.H1Function
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d)}
    {F : Vec d → Vec d} {ell upper δ : ℝ}
    (hEll : PDE.IsEllipticFieldOn ell upper
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d) a)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
      d (1 / 2))
    (ha : SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.CoefficientIdentityDistanceLE
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d) a δ)
    (hu : PDE.IsWeakDivergenceFormL2SolutionOn a
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d) u 0 F)
    (hf : MemLp (fun x => Homogenization.HilbertVec.ofVec (F x))
      (ENNReal.ofReal (2 * (d : ℝ)))
      (volume.restrict
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d))) :
    ∃ v : Vec d → ℝ,
      ContinuousOn v
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastBall d (1 / 2)) ∧
      v =ᵐ[volume.restrict
        (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d)]
        u.toFun := by
  letI : NeZero d := ⟨by omega⟩
  have hEll' : Homogenization.IsEllipticFieldOn ell upper
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d) a := by
    exact hEll
  have hf' : SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.MemVectorLpOn
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d)
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.schauderSourceExponent
        d (1 / 2)) F := by
    simpa only [SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.MemVectorLpOn,
      SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.schauderSourceExponent,
      show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num,
      show (d : ℝ) / (1 / 2) = 2 * d by ring] using hf
  obtain ⟨v, hv, heq, _⟩ :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastSchauder
      hd (by constructor <;> norm_num) hδ0 hδ hEll' ha
      (gmpWeakDivergenceFormL2_toMatrixDivForm hu) hf').2
  exact ⟨v, hv, heq⟩

/-- Safe smooth tests on a finite Euclidean ball yield the L² interface
from the actual higher-integrability divergence datum. -/
theorem gmpWeakDivergenceForm_ballL2 {d : ℕ}
    {a : Vec d → Mat d} {z : Vec d} {r ell upper : ℝ}
    {u : PDE.H1Function (Homogenization.euclideanBall z r)}
    {F : Vec d → Vec d} {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hEll : PDE.IsEllipticFieldOn ell upper (Homogenization.euclideanBall z r) a)
    (hu : PDE.IsWeakDivergenceFormSolutionOn a (Homogenization.euclideanBall z r) u 0 F)
    (hF : MemLp (fun y => Homogenization.HilbertVec.ofVec (F y)) p
      (volume.restrict (Homogenization.euclideanBall z r))) :
    PDE.IsWeakDivergenceFormL2SolutionOn a (Homogenization.euclideanBall z r) u 0 F := by
  letI : IsFiniteMeasure (volume.restrict (Homogenization.euclideanBall z r)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (Homogenization.Book.Ch01.volume_euclideanBall_ne_top z r).lt_top⟩
  have hF2 := hF.mono_exponent hp
  exact hu.toL2SolutionOn_of_isEllipticFieldOn hEll MemLp.zero
    (fun i => gmpEuclideanMemLp_coordinate hF2 i)

/-- The actual normalized physical resolvent supplies the precise finite-L²d
matrix Schauder data on a Euclidean neighborhood of every native point. -/
theorem gmpPhysicalResolvent_localNormalizedSchauderData {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, |f y| ≤ C)
    (x : Vec d) :
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    let a := fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
      ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T
    ∃ (r : ℝ) (_ : 0 < r)
      (u : PDE.H1Function (Homogenization.euclideanBall (e x) r))
      (F : Vec d → Vec d),
      u.toFun = (fun y => (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value
        (e.symm y)) ∧
      PDE.IsEllipticFieldOn (1 / 2) 9 (Homogenization.euclideanBall (e x) r) a ∧
      PDE.IsWeakDivergenceFormL2SolutionOn a (Homogenization.euclideanBall (e x) r) u 0 F ∧
      MemLp (fun y => Homogenization.HilbertVec.ofVec (F y))
        (ENNReal.ofReal (2 * (d : ℝ)))
        (volume.restrict (Homogenization.euclideanBall (e x) r)) ∧
      ∀ y ∈ Homogenization.euclideanBall (e x) r,
        Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1) ≤
          SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
            d (1 / 2) := by
  classical
  let k := Λ / sourcePhysicalDensity ω hd lam x
  let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
  have hA0 : PDE.IsEllipticMatrix 1 (Λ * Λ) A0 :=
    gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x
  let e := PDE.ellipticNormalizerContinuousLinearEquiv hA0
  let T := PDE.ellipticNormalizer A0
  let a := fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
      ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T
  have hdReal : (2 : ℝ) ≤ d := by exact_mod_cast hd
  let q : Homogenization.FiniteLpExponent :=
    { exponent := ENNReal.ofReal (2 * (d : ℝ))
      one_lt := by
        rw [← ENNReal.ofReal_one]
        exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg zero_le_one).mpr
          (by linarith : (1 : ℝ) < 2 * d)
      lt_top := ENNReal.ofReal_lt_top }
  have hq : 2 < q.exponent.toReal := by
    change 2 < (ENNReal.ofReal (2 * (d : ℝ))).toReal
    rw [ENNReal.toReal_ofReal (by positivity)]
    linarith
  let δ := SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
    d (1 / 2)
  have hδ : 0 < δ := by
    unfold δ SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
    exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hδhalf : δ ≤ 1 / 2 :=
    (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold_lt_half
      d (by norm_num) (by norm_num)).le
  obtain ⟨m, hm⟩ := gmpPoint_mem_originCube x
  obtain ⟨u, g, r, hr, hsub, hvalue, _, hu, hg, hsmall⟩ :=
    gmpPhysicalResolvent_cubeNormalizedLocalData hd ω lam Λ hΛ hω α hα f hC hf x m hm
      q hq hδ hδhalf
  let V := Homogenization.euclideanBall (e x) r
  have hV : IsOpen V := Homogenization.isOpen_euclideanBall _ _
  have hVU : V ⊆ e '' Homogenization.openCubeSet (Homogenization.originCube d m) :=
    (Homogenization.euclideanBall_subset_metricBall hr).trans hsub
  let v := (u.compLinearEquiv e).restrict hV hVU
  let F := fun y => PDE.matVecMul T (k • g (e.symm y))
  have hweak : PDE.IsWeakDivergenceFormSolutionOn a V v 0 F :=
    hu.restrict (e.isOpenMap _ (Homogenization.isOpen_openCubeSet _)) hV hVU
  have hF : MemLp (fun y => Homogenization.HilbertVec.ofVec (F y)) q.exponent
      (volume.restrict V) := hg.mono_measure (Measure.restrict_mono hVU le_rfl)
  have hcont : Continuous a := by
    have hc := (gmpPhysicalCoefficient_continuous hd ω lam).comp e.symm.continuous
    exact (((hc.const_smul k).sub continuous_const).const_mul T).mul_const
      (PDE.matTranspose T)
  have hEll : PDE.IsEllipticFieldOn (1 / 2) 9 V a := by
    refine ⟨?_, ?_⟩
    · refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      exact (((continuous_apply j).comp ((continuous_apply i).comp hcont)).measurable).ite
        hV.measurableSet measurable_const
    · intro y hy
      exact (hsmall y (Homogenization.euclideanBall_subset_metricBall hr hy)).2
  have htwo : (2 : ℝ≥0∞) ≤ q.exponent := by
    change (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (d : ℝ))
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (2 : ℝ) ≤ 2 * d)
  refine ⟨r, hr, v, F, ?_, hEll,
    gmpWeakDivergenceForm_ballL2 htwo hEll hweak hF, hF, ?_⟩
  · funext y
    change u.toFun (e.symm y) = _
    rw [hvalue]
  · intro y hy
    exact (hsmall y (Homogenization.euclideanBall_subset_metricBall hr hy)).1


/-- Local continuous representatives for the same Lebesgue class glue uniquely
on overlaps and yield a global continuous representative. -/
theorem gmpContinuousRepresentative_of_local {d : ℕ} {f : Vec d → ℝ}
    (hloc : ∀ x : Vec d, ∃ (U : Set (Vec d)) (v : Vec d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContinuousOn v U ∧ v =ᵐ[volume.restrict U] f) :
    ∃ v : Vec d → ℝ, Continuous v ∧ v =ᵐ[volume] f := by
  classical
  choose U v hU hx hv hae using hloc
  have hcompat : ∀ x y : Vec d, EqOn (v x) (v y) (U x ∩ U y) := by
    intro x y
    have hx' : v x =ᵐ[volume.restrict (U x ∩ U y)] f :=
      ae_restrict_of_ae_restrict_of_subset
      (show U x ∩ U y ⊆ U x from inter_subset_left) (hae x)
    have hy' : v y =ᵐ[volume.restrict (U x ∩ U y)] f :=
      ae_restrict_of_ae_restrict_of_subset
      (show U x ∩ U y ⊆ U y from inter_subset_right) (hae y)
    exact Measure.eqOn_open_of_ae_eq (Filter.EventuallyEq.trans hx' (Filter.EventuallyEq.symm hy')) ((hU x).inter (hU y))
      ((hv x).mono inter_subset_left) ((hv y).mono inter_subset_right)
  let g := fun x => v x x
  have hglue : ∀ x : Vec d, EqOn g (v x) (U x) := by
    intro x y hy
    exact hcompat y x ⟨hx y, hy⟩
  have hg : Continuous g := by
    rw [continuous_iff_continuousAt]
    intro x
    have hnear : g =ᶠ[nhds x] v x :=
      Filter.eventually_of_mem ((hU x).mem_nhds (hx x)) (hglue x)
    exact ((hv x).continuousAt ((hU x).mem_nhds (hx x))).congr_of_eventuallyEq hnear
  have haeG : ∀ x : Vec d, g =ᵐ[volume.restrict (U x)] f := by
    intro x
    filter_upwards [ae_restrict_mem ((hU x).measurableSet), hae x] with y hy heq
    exact (hglue x hy).trans heq
  have hcover : (univ : Set (Vec d)) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hx x⟩
  obtain ⟨I, hI, hIcover⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  have hUnion : (⋃ x ∈ I, U x) = univ := eq_univ_iff_forall.mpr (fun x => hIcover (mem_univ x))
  refine ⟨g, hg, ?_⟩
  have h := (ae_restrict_biUnion_iff U hI (fun x => g x = f x)).mpr (fun x _ => haeG x)
  simpa only [hUnion, Measure.restrict_univ] using! h


/-- Pull back any finite-exponent datum under a positive affine change,
retaining its actual codomain norm and the exact restricted-volume Jacobian. -/
theorem gmpMemLp_affinePullback {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {U : Set (Vec d)} {p : ℝ≥0∞} {g : Vec d → E} {r : ℝ}
    (hr : 0 < r) (z : Vec d)
    (hg : MemLp g p (volume.restrict (PDE.translateSet z (r • U)))) :
    MemLp (fun y => g (r • y + z)) p (volume.restrict U) := by
  have htrans : MemLp (fun y => g (y + z)) p (volume.restrict (r • U)) := by
    exact hg.comp_measurePreserving (PDE.measurePreserving_addRight_restrict_translateSet z (r • U))
  have hmap : MemLp (fun y => g (y + z)) p
      (ENNReal.ofReal ((r⁻¹) ^ d) • volume.restrict (r • U)) :=
    htrans.smul_measure ENNReal.ofReal_ne_top
  have hpull := hmap.comp_measurePreserving
    (PDE.measurePreserving_inv_smul_restrict_smul_set (inv_pos.mpr hr) (r • U))
  simpa only [Function.comp_def, inv_inv, smul_smul, inv_mul_cancel₀ hr.ne',
    one_smul, PDE.volumeOn] using! hpull


/-- Translation and positive dilation put the actual ball solution on the unit
ball, with the representative amplitude and forcing scale kept explicit. -/
theorem gmpWeakDivergenceForm_affineNormalize {d : ℕ}
    {a : Vec d → Mat d} {z : Vec d} {r ell upper : ℝ} (hr : 0 < r)
    (ha : Continuous a)
    {u : PDE.H1Function (Homogenization.euclideanBall z r)}
    {F : Vec d → Vec d} {p : ℝ≥0∞} (hp : 2 ≤ p)
    (hEll : PDE.IsEllipticFieldOn ell upper (Homogenization.euclideanBall z r) a)
    (hu : PDE.IsWeakDivergenceFormL2SolutionOn a
      (Homogenization.euclideanBall z r) u 0 F)
    (hF : MemLp (fun y => Homogenization.HilbertVec.ofVec (F y)) p
      (volume.restrict (Homogenization.euclideanBall z r))) :
    ∃ v : PDE.H1Function (Homogenization.euclideanBall (0 : Vec d) 1),
      v.toFun = (fun y => r⁻¹ * u.toFun (r • y + z)) ∧
      PDE.IsEllipticFieldOn ell upper (Homogenization.euclideanBall (0 : Vec d) 1)
        (fun y => a (r • y + z)) ∧
      PDE.IsWeakDivergenceFormL2SolutionOn (fun y => a (r • y + z))
        (Homogenization.euclideanBall (0 : Vec d) 1) v 0 (fun y => F (r • y + z)) ∧
      MemLp (fun y => Homogenization.HilbertVec.ofVec (F (r • y + z))) p
        (volume.restrict (Homogenization.euclideanBall (0 : Vec d) 1)) := by
  let V := PDE.translateSet (-z) (Homogenization.euclideanBall z r)
  let W := r⁻¹ • V
  have hW : W = Homogenization.euclideanBall (0 : Vec d) 1 := by
    ext y
    simp only [W, V, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'), inv_inv,
      PDE.mem_translateSet_iff_sub_mem, sub_neg_eq_add]
    exact PDE.affine_mem_euclideanBall_iff_of_pos z y hr
  have hUnit := Homogenization.isOpen_euclideanBall (0 : Vec d) (1 : ℝ)
  have hWOpen : IsOpen W := hW.symm ▸ hUnit
  have hsub : Homogenization.euclideanBall (0 : Vec d) 1 ⊆ W := hW.symm ▸ Subset.rfl
  let w := (u.translate (-z)).dilate (inv_pos.mpr hr)
  let v := w.restrict hUnit hsub
  have hweak := ((hu.toIsWeakDivergenceFormSolutionOn.translate (-z)).dilate_of_pos
    (inv_pos.mpr hr)).restrict hWOpen hUnit hsub
  have hvweak : PDE.IsWeakDivergenceFormSolutionOn (fun y => a (r • y + z))
      (Homogenization.euclideanBall (0 : Vec d) 1) v 0 (fun y => F (r • y + z)) := by
    simpa only [inv_inv, sub_neg_eq_add, Pi.zero_apply, mul_zero] using! hweak
  have hEll' : PDE.IsEllipticFieldOn ell upper
      (Homogenization.euclideanBall (0 : Vec d) 1) (fun y => a (r • y + z)) := by
    refine ⟨?_, ?_⟩
    · have hc : Continuous (fun y : Vec d => a (r • y + z)) :=
        ha.comp (by fun_prop : Continuous (fun y : Vec d => r • y + z))
      refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
      exact (((continuous_apply j).comp ((continuous_apply i).comp hc)).measurable).ite
        hUnit.measurableSet measurable_const
    · intro y hy
      exact hEll.2 _ ((PDE.affine_mem_euclideanBall_iff_of_pos z y hr).mpr hy)
  have hF' : MemLp (fun y => Homogenization.HilbertVec.ofVec (F (r • y + z))) p
      (volume.restrict (Homogenization.euclideanBall (0 : Vec d) 1)) := by
    apply gmpMemLp_affinePullback (U := Homogenization.euclideanBall (0 : Vec d) 1)
      (g := fun y => Homogenization.HilbertVec.ofVec (F y)) hr z
    have hBall : Homogenization.euclideanBall z r =
        PDE.translateSet z (r • Homogenization.euclideanBall (0 : Vec d) 1) :=
      PDE.euclideanBall_eq_translateSet_smul_unit_of_pos z hr
    rw [← hBall]
    exact hF
  refine ⟨v, ?_, hEll', gmpWeakDivergenceForm_ballL2 hp hEll' hvweak hF', hF'⟩
  funext y
  change r⁻¹ * u.toFun ((r⁻¹)⁻¹ • y - -z) = _
  rw [inv_inv, sub_neg_eq_add]


/-- Almost-everywhere information on the unit ball transports back to the
original ball using the actual positive affine Jacobian. -/
theorem gmpAE_affinePushforward {d : ℕ} {r : ℝ} (hr : 0 < r) (z : Vec d)
    {P : Vec d → Prop}
    (hP : ∀ᵐ y ∂volume.restrict (Homogenization.euclideanBall (0 : Vec d) 1), P y) :
    ∀ᵐ x ∂volume.restrict (Homogenization.euclideanBall z r), P (r⁻¹ • (x - z)) := by
  have hDil := (PDE.measurePreserving_inv_smul_restrict_smul_set hr
    (Homogenization.euclideanBall (0 : Vec d) 1)).quasiMeasurePreserving.ae
      (Measure.ae_smul_measure hP (ENNReal.ofReal (r ^ d)))
  have hTrans := (PDE.measurePreserving_subRight_restrict_translateSet z
    (r • Homogenization.euclideanBall (0 : Vec d) 1)).quasiMeasurePreserving.ae hDil
  have hBall : Homogenization.euclideanBall z r =
      PDE.translateSet z (r • Homogenization.euclideanBall (0 : Vec d) 1) :=
    PDE.euclideanBall_eq_translateSet_smul_unit_of_pos z hr
  rw [← hBall] at hTrans
  exact hTrans

/-- The unit-ball matrix Schauder theorem supplies a genuine local continuous
representative for the original inhomogeneous anisotropic ball equation. -/
theorem gmpMatrixSmallContrast_ballLocalContinuousRepresentative {d : ℕ} (hd : 2 ≤ d)
    {a : Vec d → Mat d} (ha : Continuous a) {z : Vec d} {r ell upper δ : ℝ}
    (hr : 0 < r) {u : PDE.H1Function (Homogenization.euclideanBall z r)}
    {F : Vec d → Vec d}
    (hEll : PDE.IsEllipticFieldOn ell upper (Homogenization.euclideanBall z r) a)
    (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
      d (1 / 2))
    (haSmall : ∀ y ∈ Homogenization.euclideanBall z r,
      Homogenization.Book.Ch02.matrixOperatorNorm (a y - 1) ≤ δ)
    (hu : PDE.IsWeakDivergenceFormL2SolutionOn a (Homogenization.euclideanBall z r) u 0 F)
    (hF : MemLp (fun y => Homogenization.HilbertVec.ofVec (F y))
      (ENNReal.ofReal (2 * (d : ℝ)))
      (volume.restrict (Homogenization.euclideanBall z r))) :
    ∃ (U : Set (Vec d)) (v : Vec d → ℝ), IsOpen U ∧ z ∈ U ∧
      U ⊆ Homogenization.euclideanBall z r ∧ ContinuousOn v U ∧
      v =ᵐ[volume.restrict U] u.toFun := by
  have hp : (2 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * (d : ℝ)) := by
    have hdReal : (2 : ℝ) ≤ d := by exact_mod_cast hd
    simpa using ENNReal.ofReal_le_ofReal (by linarith : (2 : ℝ) ≤ 2 * d)
  obtain ⟨w, hw, hEll', hweak, hF'⟩ :=
    gmpWeakDivergenceForm_affineNormalize hr ha hp hEll hu hF
  have hSmall : SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.CoefficientIdentityDistanceLE
      (SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastUnitBall d)
      (fun y => a (r • y + z)) δ := by
    filter_upwards [ae_restrict_mem (Homogenization.isOpen_euclideanBall (0 : Vec d) 1).measurableSet]
      with y hy
    exact haSmall _ ((PDE.affine_mem_euclideanBall_iff_of_pos z y hr).mpr hy)
  obtain ⟨v, hv, heq⟩ :=
    gmpMatrixSmallContrast_continuousRepresentative hd hEll' hδ0 hδ hSmall hweak hF'
  let b := fun x : Vec d => r⁻¹ • (x - z)
  let B := SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastBall d (1 / 2)
  let U := b ⁻¹' B
  have hb : Continuous b := by fun_prop
  have hU : IsOpen U := (Homogenization.isOpen_euclideanBall (0 : Vec d) (1 / 2)).preimage hb
  have hz : z ∈ U := by
    change r⁻¹ • (z - z) ∈ Homogenization.euclideanBall (0 : Vec d) (1 / 2)
    simp only [sub_self, smul_zero]
    change PDE.euclideanSqDist (0 : Vec d) 0 < (1 / 2 : ℝ) ^ 2
    rw [PDE.euclideanSqDist_self]
    norm_num
  have hsub : U ⊆ Homogenization.euclideanBall z r := by
    intro x hx
    have hxb : b x ∈ Homogenization.euclideanBall (0 : Vec d) 1 :=
      Homogenization.euclideanBall_subset_euclideanBall (by norm_num) (by norm_num) hx
    have h := (PDE.affine_mem_euclideanBall_iff_of_pos z (b x) hr).mpr hxb
    simpa only [b, smul_inv_smul₀ hr.ne', sub_add_cancel] using! h
  have hcont : ContinuousOn (fun x => r * v (b x)) U :=
    continuousOn_const.mul (hv.comp hb.continuousOn (fun _ hx => hx))
  refine ⟨U, (fun x => r * v (b x)), hU, hz, hsub, hcont, ?_⟩
  have hback := gmpAE_affinePushforward hr z heq
  have heqU := ae_restrict_of_ae_restrict_of_subset hsub hback
  filter_upwards [heqU] with x hx
  rw [hw] at hx
  rw [show v (b x) = r⁻¹ * u.toFun (r • b x + z) from hx]
  simp only [b, smul_inv_smul₀ hr.ne', sub_add_cancel, ← mul_assoc,
    mul_inv_cancel₀ hr.ne', one_mul]


/-- Bounded data for the actual physical resolvent have a global continuous
representative, obtained from the inhomogeneous anisotropic local equation. -/
theorem gmpPhysicalResolvent_continuousRepresentative
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (_hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ M : ℝ, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ M) :
    ∃ u : Vec d → ℝ, Continuous u ∧
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  obtain ⟨M, hM⟩ := hf
  have hC : 0 < |M| + 1 := by positivity
  have hfC : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, |f y| ≤ |M| + 1 :=
    hM.mono fun _ hy => hy.trans (by linarith [le_abs_self M])
  have hloc : ∀ x : Vec d, ∃ (U : Set (Vec d)) (v : Vec d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContinuousOn v U ∧
      v =ᵐ[volume.restrict U]
        (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value := by
    intro x
    let k := Λ / sourcePhysicalDensity ω hd lam x
    let A0 := k • (sourcePhysicalDensity ω hd lam x • ω.1 x)
    let e := PDE.ellipticNormalizerContinuousLinearEquiv
      (gmpPhysicalCoefficient_scaledPointElliptic hd hΛ ω hω lam x)
    let T := PDE.ellipticNormalizer A0
    let a := fun y => T * (k • (sourcePhysicalDensity ω hd lam (e.symm y) •
      ω.1 (e.symm y)) - PDE.skewPart A0) * PDE.matTranspose T
    obtain ⟨r, hr, u, F, hvalue, hEll, hu, hF, hSmall⟩ :=
      gmpPhysicalResolvent_localNormalizedSchauderData hd ω lam Λ hΛ hω α hα f hC hfC x
    have ha : Continuous a := by
      have hc := (gmpPhysicalCoefficient_continuous hd ω lam).comp e.symm.continuous
      exact (((hc.const_smul k).sub continuous_const).const_mul T).mul_const
        (PDE.matTranspose T)
    have hδ : 0 ≤ SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold
        d (1 / 2) := by
      exact SubdiffusiveProcess.CoarseGrainingVocab.Section6SmallContrast.smallContrastThreshold_nonneg
        d (by norm_num)
    obtain ⟨U, v, hU, hx, _, hv, heq⟩ :=
      gmpMatrixSmallContrast_ballLocalContinuousRepresentative hd ha hr hEll hδ le_rfl hSmall hu hF
    let W := e ⁻¹' U
    have hW : IsOpen W := hU.preimage e.continuous
    have hq : Measure.QuasiMeasurePreserving e (volume.restrict W) (volume.restrict U) := by
      refine ⟨e.continuous.measurable, ?_⟩
      rw [PDE.map_linearEquiv_volumeOn,
        show e '' W = U from Set.image_preimage_eq U e.surjective]
      exact Measure.smul_absolutelyContinuous
    refine ⟨W, (fun y => v (e y)), hW, hx,
      hv.comp e.continuous.continuousOn (fun _ hy => hy), ?_⟩
    filter_upwards [hq.ae heq] with y hy
    change v (e y) = _ at hy
    rw [hvalue] at hy
    change v (e y) = (gmpPhysicalResolventGraph hd ω lam Λ hΛ hω α hα f).value
      (e.symm (e y)) at hy
    simpa only [e.symm_apply_apply] using hy
  obtain ⟨u, hu, heq⟩ := gmpContinuousRepresentative_of_local hloc
  refine ⟨u, hu, (gmpPhysical_ae_iff_volume hd ω lam _).mpr ?_⟩
  exact heq.trans (gmpPhysicalResolventGraph_value_ae hd ω lam Λ hΛ hω α hα f)

/-- A continuous representative of a physical-measure equivalence class is unique. -/
theorem gmpPhysical_continuousRepresentative_unique {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) {u v : Vec d → ℝ}
    (hu : Continuous u) (hv : Continuous v)
    (heq : u =ᵐ[physicalReversibleMeasure ω hd lam] v) : u = v := by
  exact MeasureTheory.Measure.eq_of_ae_eq
    ((gmpPhysical_ae_iff_volume hd ω lam _).mp heq) hu hv

/-- The continuous representative inherits the resolvent's pointwise sup bound. -/
theorem gmpPhysicalResolvent_continuousRepresentative_abs_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    {u : Vec d → ℝ} (hu : Continuous u)
    (heq : u =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f) :
    ∀ x, |u x| ≤ C / α := by
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |u x| ≤ C / α := by
    filter_upwards [heq, gmpPhysicalResolvent_abs_le hd ω lam Λ hΛ hω α hα hC hf]
      with x hx hb
    simpa only [hx] using hb
  have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hc : IsClosed {x : Vec d | |u x| ≤ C / α} := isClosed_le hu.abs continuous_const
  have hfull : {x : Vec d | |u x| ≤ C / α} = Set.univ :=
    (hc.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  intro x
  have : x ∈ {x : Vec d | |u x| ≤ C / α} := by rw [hfull]; exact Set.mem_univ x
  exact this

/-- Continuous resolvent representatives inherit the sup bound on differences. -/
theorem gmpPhysicalResolvent_continuousRepresentative_sub_abs_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {C : ℝ} (hC : 0 < C)
    (hfg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |(f - g) x| ≤ C)
    {u v : Vec d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (heu : u =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f)
    (hev : v =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα g) :
    ∀ x, |u x - v x| ≤ C / α := by
  have heq : (fun x => u x - v x) =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα (f - g) := by
    rw [map_sub]
    filter_upwards [heu, hev, Lp.coeFn_sub
      (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f)
      (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα g)] with x hux hvx hx
    simpa only [hx, Pi.sub_apply, hux, hvx]
  exact gmpPhysicalResolvent_continuousRepresentative_abs_le hd ω lam Λ hΛ hω α hα
    (f - g) hC hfg (hu.sub hv) heq

/-- A positive zeroth-order coefficient dominates quadratic and linear barrier
errors when the exponential rate is chosen sufficiently small. -/
theorem gmpPhysical_barrier_rate_exists {A B α : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ k ≤ 1 ∧ A * k ^ 2 + B * k < α := by
  let D := A + B + α + 1
  have hD : 0 < D := by dsimp [D]; linarith
  let k := α / (2 * D)
  have hk : 0 < k := div_pos hα (by positivity)
  have hkD : k * (2 * D) = α := by
    dsimp [k]
    exact div_mul_cancel₀ α (ne_of_gt (by positivity : 0 < 2 * D))
  have hk1 : k ≤ 1 := by
    have : α ≤ 2 * D := by dsimp [D]; linarith
    exact (div_le_one (by positivity : 0 < 2 * D)).2 this
  have hk2 : k ^ 2 ≤ k := by nlinarith
  have hAk : A * k ^ 2 ≤ A * k := mul_le_mul_of_nonneg_left hk2 hA
  have hstrict : (A + B) * k < α := by
    have hpos : 0 < (2 * D - (A + B)) * k := by
      apply mul_pos _ hk
      dsimp [D]
      linarith
    nlinarith only [hkD, hpos]
  refine ⟨k, hk, hk1, ?_⟩
  nlinarith only [hAk, hstrict]


/-- The smooth radial distance tends to infinity on the cocompact filter. -/
theorem gmpPhysical_radialDistance_tendsto_atTop {d : ℕ} :
    Tendsto (fun x : Vec d => Real.sqrt (1 + euclideanSq x))
      (Filter.cocompact (Vec d)) atTop := by
  have hnorm : Tendsto (fun x : Vec d => ‖x‖) (Filter.cocompact (Vec d)) atTop :=
    tendsto_norm_cocompact_atTop
  apply tendsto_atTop_mono (fun x => ?_) hnorm
  have hx : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change x i ^ 2 ≤ ∑ j : Fin d, x j * x j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  apply hx.trans
  change Real.sqrt (euclideanSq x) ≤ Real.sqrt (1 + euclideanSq x)
  exact Real.sqrt_le_sqrt (by linarith)

/-- The radial exponential used for exterior comparison vanishes at infinity. -/
theorem gmpPhysical_radialBarrier_tendsto_zero {d : ℕ} {k : ℝ} (hk : 0 < k)
    (M R : ℝ) :
    Tendsto (fun x : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))))
      (Filter.cocompact (Vec d)) (𝓝 0) := by
  have hr := gmpPhysical_radialDistance_tendsto_atTop (d := d)
  have hsub : Tendsto (fun x : Vec d =>
      Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))
      (Filter.cocompact (Vec d)) atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right _ (-Real.sqrt (1 + R ^ 2)) hr)
  have hexp := Real.tendsto_exp_atBot.comp (hsub.const_mul_atTop_of_neg (neg_lt_zero.mpr hk))
  simpa only [Function.comp_apply, mul_zero] using hexp.const_mul M

/-- An exterior radial-barrier bound implies decay of the bounded function. -/
theorem gmpPhysical_tendsto_zero_of_radialBarrier {d : ℕ}
    {u : Vec d → ℝ} {k M R : ℝ} (hk : 0 < k)
    (hbound : ∀ x : Vec d, R ≤ euclideanNorm x → |u x| ≤ M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) :
    Tendsto u (Filter.cocompact (Vec d)) (𝓝 0) := by
  have hnorm : Tendsto (fun x : Vec d => euclideanNorm x)
      (Filter.cocompact (Vec d)) atTop := by
    apply tendsto_atTop_mono (fun x => ?_) tendsto_norm_cocompact_atTop
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change x i ^ 2 ≤ ∑ j : Fin d, x j * x j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg (u x))
  · filter_upwards [hnorm.eventually_ge_atTop R] with x hx
    simpa only [Real.norm_eq_abs] using hbound x hx
  · exact gmpPhysical_radialBarrier_tendsto_zero hk M R


/-- The explicit radial exponential barrier is smooth, including at the origin. -/
theorem gmpPhysical_radialBarrier_contDiff {d : ℕ} (M k R : ℝ) :
    ContDiff ℝ 1 (fun x : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) := by
  have hsq : ContDiff ℝ 1 (fun x : Vec d => euclideanSq x) := by
    unfold euclideanSq dot
    exact ContDiff.sum fun i _ =>
      (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  have hr : ContDiff ℝ 1 (fun x : Vec d => Real.sqrt (1 + euclideanSq x)) := by
    apply (contDiff_const.add hsq).sqrt
    intro x
    have h : 0 ≤ euclideanSq x := by
      change 0 ≤ ∑ i, x i * x i
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    positivity
  exact contDiff_const.mul
    ((contDiff_const.mul (hr.sub contDiff_const)).exp)

/-- On the source ball, the radial barrier dominates its amplitude. -/
theorem gmpPhysical_radialBarrier_ge_amplitude {d : ℕ}
    {M k R : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (hR : 0 ≤ R)
    (x : Vec d) (hx : euclideanNorm x ≤ R) :
    M ≤ M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
  have hnorm : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hsq : euclideanSq x ≤ R ^ 2 := by
    have hnonneg : 0 ≤ euclideanSq x := by
      change 0 ≤ ∑ i, x i * x i
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h := Real.sq_sqrt hnonneg
    have hsqrt := Real.sqrt_nonneg (euclideanSq x)
    change Real.sqrt (euclideanSq x) ≤ R at hx
    nlinarith
  have hr : Real.sqrt (1 + euclideanSq x) ≤ Real.sqrt (1 + R ^ 2) :=
    Real.sqrt_le_sqrt (by linarith)
  have he : 0 ≤ -k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)) :=
    mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hk) (sub_nonpos.mpr hr)
  have he' : 1 ≤ Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr he
  nlinarith


/-- The smooth radial distance has the expected Euclidean coordinate gradient. -/
theorem gmpPhysical_radialDistance_classicalGradient {d : ℕ} (x : Vec d) :
    PDE.classicalGradient (fun y : Vec d => Real.sqrt (1 + euclideanSq y)) x =
      fun i => x i / Real.sqrt (1 + euclideanSq x) := by
  let L : Vec d →L[ℝ] ℝ := ∑ j : Fin d,
    (x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) +
      x j • (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ))
  have hsq : HasFDerivAt (fun y : Vec d => euclideanSq y) L x := by
    unfold euclideanSq dot L
    exact HasFDerivAt.fun_sum fun j _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) j x).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) j x)
  have hnonneg : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ i, x i * x i
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hq : 1 + euclideanSq x ≠ 0 := by linarith
  have hderiv := (hsq.const_add 1).sqrt hq
  funext i
  rw [PDE.classicalGradient_apply, hderiv.fderiv]
  have hL : L (PDE.basisVec i) = 2 * x i := by
    simp [L, PDE.basisVec_apply, Finset.sum_add_distrib, two_mul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hL]
  have hroot : Real.sqrt (1 + euclideanSq x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  field_simp
  <;> ring


/-- Coordinate gradient of the actual exponential barrier. -/
theorem gmpPhysical_radialBarrier_classicalGradient {d : ℕ} (M k R : ℝ)
    (x : Vec d) :
    PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x =
      fun i => (-k * (M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))))) *
          (x i / Real.sqrt (1 + euclideanSq x)) := by
  have hsq : ContDiff ℝ 1 (fun y : Vec d => euclideanSq y) := by
    unfold euclideanSq dot
    exact ContDiff.sum fun i _ =>
      (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  have hr : ContDiff ℝ 1 (fun y : Vec d => Real.sqrt (1 + euclideanSq y)) := by
    apply (contDiff_const.add hsq).sqrt
    intro y
    have h : 0 ≤ euclideanSq y := by
      change 0 ≤ ∑ i, y i * y i
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    positivity
  have hd := (hr.differentiable (by norm_num) x).hasFDerivAt
  have hb := (((hd.sub_const (Real.sqrt (1 + R ^ 2))).const_mul (-k)).exp).const_mul M
  funext i
  rw [PDE.classicalGradient_apply, hb.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hi := congrFun (gmpPhysical_radialDistance_classicalGradient x) i
  rw [PDE.classicalGradient_apply] at hi
  rw [hi]
  ring


/-- The barrier gradient is bounded by its exponential rate times its value. -/
theorem gmpPhysical_radialBarrier_gradient_bound {d : ℕ} {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) (x : Vec d) :
    ‖WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)‖ ≤
      k * (M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) := by
  let r := Real.sqrt (1 + euclideanSq x)
  let b := M * Real.exp (-k * (r - Real.sqrt (1 + R ^ 2)))
  have hsq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ i, x i * x i
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hb : 0 ≤ b := mul_nonneg hM (Real.exp_pos _).le
  have hn : ‖WithLp.toLp 2 x‖ ^ 2 = euclideanSq x := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs, euclideanSq, dot]
    simp only [pow_two]
  have hnr : ‖WithLp.toLp 2 x‖ ≤ r := by
    have hrr : r ^ 2 = 1 + euclideanSq x := Real.sq_sqrt (by linarith)
    nlinarith [norm_nonneg (WithLp.toLp 2 x)]
  have hg : WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x) =
      ((-k * b) / r) • WithLp.toLp 2 x := by
    ext i
    rw [gmpPhysical_radialBarrier_classicalGradient]
    simp only [PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul]
    dsimp [b, r]
    ring
  change ‖WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)‖ ≤ k * b
  rw [hg, norm_smul, Real.norm_eq_abs, abs_div, abs_mul, abs_neg,
    abs_of_nonneg hk, abs_of_nonneg hb, abs_of_pos hr]
  have hratio : ‖WithLp.toLp 2 x‖ / r ≤ 1 := (div_le_one hr).2 hnr
  calc
    k * b / r * ‖WithLp.toLp 2 x‖ = (k * b) * (‖WithLp.toLp 2 x‖ / r) := by ring
    _ ≤ (k * b) * 1 := mul_le_mul_of_nonneg_left hratio (mul_nonneg hk hb)
    _ = k * b := mul_one _


/-- A positive excess over the barrier is supported strictly outside the source ball. -/
theorem gmpPhysical_radialBarrier_positiveExcess_support {d : ℕ}
    {M k R : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (hR : 0 ≤ R)
    {u : Vec d → ℝ} (hu : ∀ x, u x ≤ M) (x : Vec d)
    (hx : M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) < u x) :
    R < euclideanNorm x := by
  by_contra h
  have hb := gmpPhysical_radialBarrier_ge_amplitude hM hk hR x (le_of_not_gt h)
  linarith [hu x]

/-- Compactly supported forcing is orthogonal to the barrier's positive excess. -/
theorem gmpPhysical_radialBarrier_forcing_mul_positiveExcess_eq_zero {d : ℕ}
    (μ : Measure (Vec d)) {M k R : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (hR : 0 ≤ R)
    {u f : Vec d → ℝ} (hu : ∀ x, u x ≤ M)
    (hf : ∀ᵐ x ∂μ, R ≤ euclideanNorm x → f x = 0) :
    ∀ᵐ x ∂μ, f x * max (u x - M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0 = 0 := by
  filter_upwards [hf] with x hx
  by_cases hb : M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) < u x
  · rw [hx (le_of_lt (gmpPhysical_radialBarrier_positiveExcess_support hM hk hR hu x hb))]
    simp
  · have h : u x - M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) ≤ 0 := by
      linarith
    rw [max_eq_right h, mul_zero]


/-- The coordinate Hessian of the smooth radial distance. -/
theorem gmpPhysical_radialDistance_classicalHessian {d : ℕ}
    (x : Vec d) (i j : Fin d) :
    PDE.classicalGradient
      (fun y : Vec d => PDE.classicalGradient
        (fun z : Vec d => Real.sqrt (1 + euclideanSq z)) y i) x j =
      (if i = j then 1 else 0) / Real.sqrt (1 + euclideanSq x) -
        x i * x j / (Real.sqrt (1 + euclideanSq x)) ^ 3 := by
  let L : Vec d →L[ℝ] ℝ := ∑ n : Fin d,
    (x n • (ContinuousLinearMap.proj n : Vec d →L[ℝ] ℝ) +
      x n • (ContinuousLinearMap.proj n : Vec d →L[ℝ] ℝ))
  have hsq : HasFDerivAt (fun y : Vec d => euclideanSq y) L x := by
    unfold euclideanSq dot L
    exact HasFDerivAt.fun_sum fun n _ =>
      (hasFDerivAt_apply (𝕜 := ℝ) n x).fun_mul (hasFDerivAt_apply (𝕜 := ℝ) n x)
  have hnonneg : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ n, x n * x n
    exact Finset.sum_nonneg fun n _ => mul_self_nonneg _
  have hq : 1 + euclideanSq x ≠ 0 := by linarith
  have hr := (hsq.const_add 1).sqrt hq
  have hr0 : Real.sqrt (1 + euclideanSq x) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by linarith))
  have hf := (hasFDerivAt_apply (𝕜 := ℝ) i x).fun_mul
    ((hasFDerivAt_inv hr0).comp x hr)
  change HasFDerivAt (fun y : Vec d => y i * (Real.sqrt (1 + euclideanSq y))⁻¹) _ x at hf
  have heq : (fun y : Vec d => PDE.classicalGradient
      (fun z : Vec d => Real.sqrt (1 + euclideanSq z)) y i) =
      (fun y : Vec d => y i * (Real.sqrt (1 + euclideanSq y))⁻¹) := by
    funext y
    rw [gmpPhysical_radialDistance_classicalGradient]
    simp only [div_eq_mul_inv]
  rw [heq, PDE.classicalGradient_apply, hf.fderiv]
  have hL : L (PDE.basisVec j) = 2 * x j := by
    simp [L, PDE.basisVec_apply, Finset.sum_add_distrib, two_mul]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Function.comp_apply, smul_eq_mul, hL, PDE.basisVec_apply]
  field_simp
  <;> ring


/-- Coordinate Hessian of the exponential radial barrier. -/
theorem gmpPhysical_radialBarrier_classicalHessian {d : ℕ} (M k R : ℝ)
    (x : Vec d) (i j : Fin d) :
    PDE.classicalGradient
      (fun y : Vec d => PDE.classicalGradient (fun z : Vec d => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq z) - Real.sqrt (1 + R ^ 2)))) y i) x j =
    (M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) *
      (k ^ 2 * (x i / Real.sqrt (1 + euclideanSq x)) *
        (x j / Real.sqrt (1 + euclideanSq x)) -
        k * ((if i = j then 1 else 0) / Real.sqrt (1 + euclideanSq x) -
          x i * x j / (Real.sqrt (1 + euclideanSq x)) ^ 3)) := by
  let b : Vec d → ℝ := fun y => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))
  let r : Vec d → ℝ := fun y => Real.sqrt (1 + euclideanSq y)
  have hb : Differentiable ℝ b := (gmpPhysical_radialBarrier_contDiff M k R).differentiable (by norm_num)
  have hsq : ContDiff ℝ 2 (fun y : Vec d => euclideanSq y) := by
    unfold euclideanSq dot
    exact ContDiff.sum fun n _ => (contDiff_apply ℝ ℝ n).mul (contDiff_apply ℝ ℝ n)
  have hr : ContDiff ℝ 2 r := by
    apply (contDiff_const.add hsq).sqrt
    intro y
    have h : 0 ≤ euclideanSq y := by
      change 0 ≤ ∑ n, y n * y n
      exact Finset.sum_nonneg fun n _ => mul_self_nonneg _
    positivity
  have hd : Differentiable ℝ (fun y => PDE.classicalGradient r y i) := by
    unfold PDE.classicalGradient
    fun_prop
  have hp := ((hb x).hasFDerivAt.const_mul (-k)).fun_mul (hd x).hasFDerivAt
  have heq : (fun y : Vec d => PDE.classicalGradient b y i) =
      (fun y => (-k * b y) * PDE.classicalGradient r y i) := by
    funext y
    rw [gmpPhysical_radialBarrier_classicalGradient, gmpPhysical_radialDistance_classicalGradient]
  change PDE.classicalGradient (fun y => PDE.classicalGradient b y i) x j = _
  rw [heq, PDE.classicalGradient_apply, hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hbi := congrFun (gmpPhysical_radialBarrier_classicalGradient M k R x) j
  have hri := congrFun (gmpPhysical_radialDistance_classicalGradient x) i
  have hrj := gmpPhysical_radialDistance_classicalHessian x i j
  change fderiv ℝ b x (PDE.basisVec j) = _ at hbi
  change fderiv ℝ (fun y => PDE.classicalGradient r y i) x (PDE.basisVec j) = _ at hrj
  rw [hbi, hri, hrj]
  dsimp [b, r]
  ring


/-- Every coordinate of the radial barrier Hessian is controlled by the barrier. -/
theorem gmpPhysical_radialBarrier_hessian_bound {d : ℕ} {M k : ℝ}
    (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) (x : Vec d) (i j : Fin d) :
    |PDE.classicalGradient
      (fun y : Vec d => PDE.classicalGradient (fun z : Vec d => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq z) - Real.sqrt (1 + R ^ 2)))) y i) x j| ≤
      (k ^ 2 + 2 * k) * (M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) := by
  let r := Real.sqrt (1 + euclideanSq x)
  let b := M * Real.exp (-k * (r - Real.sqrt (1 + R ^ 2)))
  have hsq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ n, x n * x n
    exact Finset.sum_nonneg fun n _ => mul_self_nonneg _
  have hr2 : r ^ 2 = 1 + euclideanSq x := Real.sq_sqrt (by linarith)
  have hr : 1 ≤ r := by
    have := Real.sqrt_nonneg (1 + euclideanSq x)
    dsimp [r] at *
    nlinarith
  have hr0 : 0 < r := by linarith
  have hn : ‖WithLp.toLp 2 x‖ ^ 2 = euclideanSq x := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs, euclideanSq, dot]
    simp only [pow_two]
  have hnr : ‖WithLp.toLp 2 x‖ ≤ r := by
    nlinarith [norm_nonneg (WithLp.toLp 2 x)]
  have hx (n : Fin d) : |x n| ≤ r := by
    have h := PiLp.norm_apply_le (WithLp.toLp 2 x) n
    simp only [PiLp.toLp_apply, Real.norm_eq_abs] at h
    exact h.trans hnr
  have hratio (n : Fin d) : |x n / r| ≤ 1 := by
    rw [abs_div, abs_of_pos hr0]
    exact (div_le_one hr0).2 (hx n)
  have hinv : |(if i = j then (1 : ℝ) else 0) / r| ≤ 1 := by
    split_ifs <;> simp only [zero_div, abs_zero, zero_le_one, one_div, abs_inv, abs_of_pos hr0]
    exact inv_le_one₀ hr0 |>.2 hr
  have hprod : |x i * x j / r ^ 3| ≤ 1 := by
    have hi := hx i
    have hj := hx j
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hr0]
    apply (div_le_one (pow_pos hr0 _)).2
    have hp := mul_le_mul hi hj (abs_nonneg _) (le_trans (abs_nonneg _) hi)
    nlinarith
  have hδ : |(if i = j then (1 : ℝ) else 0) / r - x i * x j / r ^ 3| ≤ 2 := by
    calc
      _ ≤ |(if i = j then (1 : ℝ) else 0) / r| + |x i * x j / r ^ 3| := abs_sub _ _
      _ ≤ 2 := by linarith
  have ht : |k ^ 2 * (x i / r) * (x j / r) -
      k * ((if i = j then (1 : ℝ) else 0) / r - x i * x j / r ^ 3)| ≤ k ^ 2 + 2 * k := by
    calc
      _ ≤ |k ^ 2 * (x i / r) * (x j / r)| +
          |k * ((if i = j then (1 : ℝ) else 0) / r - x i * x j / r ^ 3)| := abs_sub _ _
      _ ≤ k ^ 2 + 2 * k := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hk, abs_mul, abs_of_nonneg hk]
        have hp : |x i / r| * |x j / r| ≤ 1 := by
          calc
            _ ≤ 1 * 1 := mul_le_mul (hratio i) (hratio j) (abs_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        have hk2 := mul_le_mul_of_nonneg_left hp (sq_nonneg k)
        have hkδ := mul_le_mul_of_nonneg_left hδ hk
        nlinarith
  rw [gmpPhysical_radialBarrier_classicalHessian]
  change |b * (k ^ 2 * (x i / r) * (x j / r) -
      k * ((if i = j then (1 : ℝ) else 0) / r - x i * x j / r ^ 3))| ≤ (k ^ 2 + 2 * k) * b
  rw [abs_mul, abs_of_nonneg (mul_nonneg hM (Real.exp_pos _).le)]
  nlinarith [mul_nonneg (mul_nonneg hM (Real.exp_pos (-k * (r - Real.sqrt (1 + R ^ 2)))).le)
    (sub_nonneg.mpr ht)]


/-- The actual radial excess is an admissible test for the physical resolvent equation. -/
theorem gmpPhysicalResolvent_radialExcess_exists {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) :
    ∃ v : GMPForceH1 hd lam,
      (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam]
        (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
          M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0) ∧
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
        Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
        {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
          gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
          (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
            (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
            WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
              (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)) := by
  let u := gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  obtain ⟨v, hv, hgrad⟩ := gmpForceH1PositivePart_sub_barrier_exists hd lam u b
    (gmpPhysical_radialBarrier_contDiff M k R) k hk
    (Filter.Eventually.of_forall fun x => mul_nonneg hM (Real.exp_pos _).le)
    (Filter.Eventually.of_forall fun x => gmpPhysical_radialBarrier_gradient_bound hM hk R x)
  have hv' := (gmp_force_ae_iff_physical hd ω lam _).mp hv
  have hg' := (gmp_force_ae_iff_physical hd ω lam _).mp hgrad
  have hu : (gmpPhysicalH1Value hd ω lam Λ hω u : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
    exact Lp.ext_iff.mp (gmpPhysicalResolventH1_value hd ω lam Λ hΛ hω α hα f)
  refine ⟨v, ?_, ?_⟩
  · filter_upwards [hv', hu, gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u,
      gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v] with x hvx hux huval hvval
    change _ = max (_ - b x) 0
    rw [hvval, hvx, ← huval, hux]
  · filter_upwards [hg', hu, gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u,
      gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam Λ hω u,
      gmpPhysicalH1Gradient_ae_spaceGradient hd ω lam Λ hω v] with x hvx hux huval hugrad hvgrad
    change _ = {x | b x < gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator _ x
    rw [hvgrad, hvx]
    by_cases hx : b x < densityWeightedH1SpaceValue u x
    · have hx' : b x < gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x := by
        rw [← hux, huval]; exact hx
      simpa only [Set.indicator_of_mem, Set.mem_setOf_eq, hx, hx', u, b] using
        congrArg (fun z => z - WithLp.toLp 2 (PDE.classicalGradient b x)) hugrad.symm
    · have hx' : ¬ b x < gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x := by
        rw [← hux, huval]; exact hx
      simp [hx, hx']


/-- The actual coefficient and potential coordinate derivatives have uniform bounds. -/
theorem gmpPhysical_coefficient_coordinateDerivative_bound {d : ℕ} (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (x : Vec d) (i j k : Fin d) :
    |coordinateDerivative k (fun y => ω.1 y i j) x| ≤ Λ * ((d : ℝ) + 1) ∧
    |coordinateDerivative k (fun y => ω.2 y) x| ≤ Λ * ((d : ℝ) + 1) := by
  have hΛ0 : 0 ≤ Λ := by linarith
  let L : ℝ≥0 := ⟨Λ * ((d : ℝ) + 1), by positivity⟩
  have hcoord (g : Vec d → ℝ) (hg : LipschitzWith L g) :
      |coordinateDerivative k g x| ≤ Λ * ((d : ℝ) + 1) := by
    unfold coordinateDerivative
    rw [← Real.norm_eq_abs]
    calc
      ‖fderiv ℝ g x (unitVector k)‖ ≤ ‖fderiv ℝ g x‖ * ‖unitVector k‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (L : ℝ) * ‖unitVector k‖ :=
        mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hg) (norm_nonneg _)
      _ = Λ * ((d : ℝ) + 1) := by
        simp only [unitVector, Pi.norm_single, norm_one, mul_one]
        rfl
  constructor
  · exact hcoord _ (lipschitzWith_of_euclidean_bound Λ hΛ0 (hω.2.2.1.entry_bound i j))
  · exact hcoord _ (lipschitzWith_of_euclidean_bound Λ hΛ0 hω.2.2.2)

/-- Each column divergence of the actual coefficient field has a uniform bound. -/
theorem gmpPhysical_coefficient_divergence_bound {d : ℕ} (ω : FieldPair d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (x : Vec d) (j : Fin d) :
    |∑ i : Fin d, coordinateDerivative i (fun y => ω.1 y i j) x| ≤
      (d : ℝ) * (Λ * ((d : ℝ) + 1)) := by
  calc
    _ ≤ ∑ i : Fin d, |coordinateDerivative i (fun y => ω.1 y i j) x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, Λ * ((d : ℝ) + 1) :=
      Finset.sum_le_sum fun i _ =>
        (gmpPhysical_coefficient_coordinateDerivative_bound ω Λ hΛ hω x i j i).1
    _ = _ := by simp


/-- The divergence drift of the actual tilted physical form is uniformly bounded. -/
theorem gmpPhysical_weighted_drift_bound {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (x : Vec d) (j : Fin d) :
    |∑ i : Fin d, (coordinateDerivative i (fun y => ω.1 y i j) x +
      2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
        coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j)| ≤
      (d : ℝ) * (Λ * ((d : ℝ) + 1) +
        2 * (|lam| + Λ * ((d : ℝ) + 1)) * Λ) := by
  let D : ℝ := Λ * ((d : ℝ) + 1)
  have hΛ0 : 0 ≤ Λ := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hterm (i : Fin d) :
      |coordinateDerivative i (fun y => ω.1 y i j) x +
        2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j| ≤
        D + 2 * (|lam| + D) * Λ := by
    have hder := gmpPhysical_coefficient_coordinateDerivative_bound ω Λ hΛ hω x i j i
    have ha : |ω.1 x i j| ≤ Λ :=
      EinsteinRelation.Correctors.IsElliptic.entry_abs_le (by linarith) hω.1 x i j
    have hforce : |(if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0)| ≤ |lam| := by
      split_ifs <;> simp
    have hlog : |(if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
        coordinateDerivative i (fun y => ω.2 y) x| ≤ |lam| + D := by
      calc
        _ ≤ |(if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0)| +
          |coordinateDerivative i (fun y => ω.2 y) x| := abs_sub _ _
        _ ≤ |lam| + D := add_le_add hforce hder.2
    calc
      _ ≤ |coordinateDerivative i (fun y => ω.1 y i j) x| +
          |2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
            coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j| := abs_add_le _ _
      _ ≤ D + 2 * (|lam| + D) * Λ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        have hm := mul_le_mul hlog ha (abs_nonneg _) (add_nonneg (abs_nonneg _) hD)
        nlinarith [hder.1]
  calc
    _ ≤ ∑ i : Fin d, |coordinateDerivative i (fun y => ω.1 y i j) x +
        2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, (D + 2 * (|lam| + D) * Λ) := Finset.sum_le_sum fun i _ => hterm i
    _ = _ := by simp [D, mul_add]


/-- The physical density has the expected logarithmic derivative wherever the potential is differentiable. -/
theorem gmpPhysical_density_coordinateDerivative {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (x : Vec d) (i : Fin d)
    (hV : DifferentiableAt ℝ (fun y => ω.2 y) x) :
    coordinateDerivative i (sourcePhysicalDensity ω hd lam) x =
      sourcePhysicalDensity ω hd lam x *
        (2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x)) := by
  let i₀ : Fin d := ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩
  have hw := ((hasFDerivAt_apply (𝕜 := ℝ) i₀ x).const_mul (2 * lam)).exp
  have hc := (hV.hasFDerivAt.const_mul (-2)).exp
  have hp := hw.fun_mul hc
  have he : sourcePhysicalDensity ω hd lam = (fun y =>
      Real.exp ((2 * lam) * y i₀) * Real.exp (-2 * ω.2 y)) := by
    funext y
    simp only [sourcePhysicalDensity, sourceForceWeight, clockDensity, i₀, mul_assoc]
  unfold coordinateDerivative
  rw [he, hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, unitVector, Pi.single_apply]
  dsimp [sourcePhysicalDensity, sourceForceWeight, clockDensity, i₀]
  split_ifs <;> simp_all <;> ring

/-- The logarithmic derivative identity holds almost everywhere for regular fields. -/
theorem gmpPhysical_density_coordinateDerivative_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (i : Fin d) :
    ∀ᵐ x ∂volume, coordinateDerivative i (sourcePhysicalDensity ω hd lam) x =
      sourcePhysicalDensity ω hd lam x *
        (2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x)) := by
  filter_upwards [hω.ae_differentiableAt_fields (by linarith : 0 ≤ Λ)] with x hx
  exact gmpPhysical_density_coordinateDerivative hd ω lam x i hx.2

/-- The differential expression of the actual weighted form is dominated by
its zeroth-order term for one rate independent of the forcing and radius. -/
theorem gmpPhysical_radialBarrier_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ (R : ℝ) (x : Vec d),
      (∑ j : Fin d, (∑ i : Fin d,
        (coordinateDerivative i (fun y => ω.1 y i j) x +
          2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
            coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j)) *
        PDE.classicalGradient (fun y : Vec d => M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x j) +
      (∑ i : Fin d, ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
        (fun y : Vec d => PDE.classicalGradient (fun z : Vec d => M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq z) - Real.sqrt (1 + R ^ 2)))) y j) x i)
        ≤ 2 * α * (M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) := by
  let D : ℝ := (d : ℝ) * (Λ * ((d : ℝ) + 1) +
    2 * (|lam| + Λ * ((d : ℝ) + 1)) * Λ)
  let A : ℝ := (d : ℝ) * (d : ℝ) * Λ
  let B : ℝ := 2 * A + (d : ℝ) * D
  have hΛ0 : 0 ≤ Λ := by linarith
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨k, hk, hk1, hkbound⟩ := gmpPhysical_barrier_rate_exists hA hB hα
  refine ⟨k, hk, ?_⟩
  intro M hM R x
  let b : Vec d → ℝ := fun y => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))
  have hb : 0 ≤ b x := mul_nonneg hM (Real.exp_pos _).le
  have hg (j : Fin d) : |PDE.classicalGradient b x j| ≤ k * b x := by
    have h := PiLp.norm_apply_le (WithLp.toLp 2 (PDE.classicalGradient b x)) j
    simp only [PiLp.toLp_apply, Real.norm_eq_abs] at h
    exact h.trans (gmpPhysical_radialBarrier_gradient_bound hM hk.le R x)
  have hh (i j : Fin d) : |PDE.classicalGradient
      (fun y => PDE.classicalGradient b y j) x i| ≤ (k ^ 2 + 2 * k) * b x :=
    gmpPhysical_radialBarrier_hessian_bound hM hk.le R x j i
  have hterm (j : Fin d) :
      (∑ i : Fin d, (coordinateDerivative i (fun y => ω.1 y i j) x +
        2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j)) *
        PDE.classicalGradient b x j ≤ D * (k * b x) := by
    calc
      _ ≤ |(∑ i : Fin d, (coordinateDerivative i (fun y => ω.1 y i j) x +
          2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
            coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j)) *
          PDE.classicalGradient b x j| := le_abs_self _
      _ ≤ D * (k * b x) := by
        rw [abs_mul]
        exact mul_le_mul (gmpPhysical_weighted_drift_bound hd ω lam Λ hΛ hω x j)
          (hg j) (abs_nonneg _) hD
  have hterm2 (i j : Fin d) : ω.1 x i j * PDE.classicalGradient
      (fun y => PDE.classicalGradient b y j) x i ≤ Λ * ((k ^ 2 + 2 * k) * b x) := by
    calc
      _ ≤ |ω.1 x i j * PDE.classicalGradient
          (fun y => PDE.classicalGradient b y j) x i| := le_abs_self _
      _ ≤ Λ * ((k ^ 2 + 2 * k) * b x) := by
        rw [abs_mul]
        exact mul_le_mul (EinsteinRelation.Correctors.IsElliptic.entry_abs_le
          (by linarith) hω.1 x i j) (hh i j) (abs_nonneg _) hΛ0
  change (∑ j : Fin d, _ * PDE.classicalGradient b x j) +
    (∑ i : Fin d, ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
      (fun y => PDE.classicalGradient b y j) x i) ≤ 2 * α * b x
  have hfirst := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm j
  have hsecond := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm2 i j
  simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hfirst hsecond
  have hm := mul_le_mul_of_nonneg_right hkbound.le hb
  dsimp [A, B] at hm
  nlinarith [mul_nonneg hα.le hb]

/-- The literal density-weighted barrier flux has nonnegative massive residual
almost everywhere, including for merely Lipschitz regular environments. -/
theorem gmpPhysical_radialBarrier_weightedFlux_supersolution_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ R : ℝ,
      ∀ᵐ x ∂volume,
        (∑ i : Fin d, coordinateDerivative i
          (fun y => sourcePhysicalDensity ω hd lam y *
            (∑ j : Fin d, ω.1 y i j * PDE.classicalGradient
              (fun z : Vec d => M * Real.exp
                (-k * (Real.sqrt (1 + euclideanSq z) - Real.sqrt (1 + R ^ 2)))) y j)) x)
        ≤ 2 * α * sourcePhysicalDensity ω hd lam x *
          (M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) := by
  obtain ⟨k, hk, hbound⟩ := gmpPhysical_radialBarrier_generator_bound hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro M hM R
  let b : Vec d → ℝ := fun y => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))
  let ρ := sourcePhysicalDensity ω hd lam
  have hb2 : ContDiff ℝ 2 b := by
    have hsq : ContDiff ℝ 2 (fun y : Vec d => euclideanSq y) := by
      unfold euclideanSq dot
      exact ContDiff.sum fun n _ => (contDiff_apply ℝ ℝ n).mul (contDiff_apply ℝ ℝ n)
    have hr : ContDiff ℝ 2 (fun y : Vec d => Real.sqrt (1 + euclideanSq y)) := by
      apply (contDiff_const.add hsq).sqrt
      intro y
      have h : 0 ≤ euclideanSq y := by
        change 0 ≤ ∑ i, y i * y i
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      positivity
    exact contDiff_const.mul ((contDiff_const.mul (hr.sub contDiff_const)).exp)
  have hgrad (j : Fin d) : Differentiable ℝ (fun y => PDE.classicalGradient b y j) := by
    unfold PDE.classicalGradient
    fun_prop
  filter_upwards [hω.ae_differentiableAt_fields (by linarith : 0 ≤ Λ)] with x hx
  have hρ : DifferentiableAt ℝ ρ x := by
    dsimp [ρ, sourcePhysicalDensity, sourceForceWeight, clockDensity]
    exact (((hasFDerivAt_apply (𝕜 := ℝ) _ x).const_mul (2 * lam)).exp.differentiableAt).mul
      ((hx.2.const_mul (-2)).exp)
  have ha (i j : Fin d) : DifferentiableAt ℝ (fun y => ω.1 y i j) x :=
    (differentiableAt_pi.mp ((differentiableAt_pi.mp hx.1) i)) j
  have hterm (i j : Fin d) : coordinateDerivative i
      (fun y => ρ y * (ω.1 y i j * PDE.classicalGradient b y j)) x =
      ρ x * ((coordinateDerivative i (fun y => ω.1 y i j) x +
        2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j) *
          PDE.classicalGradient b x j + ω.1 x i j * PDE.classicalGradient
            (fun y => PDE.classicalGradient b y j) x i) := by
    unfold coordinateDerivative
    have hp := hρ.hasFDerivAt.fun_mul ((ha i j).hasFDerivAt.fun_mul (hgrad j x).hasFDerivAt)
    rw [hp.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hρ' := gmpPhysical_density_coordinateDerivative hd ω lam x i hx.2
    change fderiv ℝ ρ x (unitVector i) = ρ x *
      (2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
        fderiv ℝ (fun y => ω.2 y) x (unitVector i))) at hρ'
    rw [hρ']
    have he : PDE.basisVec i = unitVector i := by
      ext l
      simp [PDE.basisVec_apply, unitVector, Pi.single_apply, eq_comm]
    simp only [PDE.classicalGradient_apply, he]
    ring
  have hflux (i : Fin d) : coordinateDerivative i
      (fun y => ρ y * (∑ j : Fin d, ω.1 y i j * PDE.classicalGradient b y j)) x =
      ∑ j : Fin d, coordinateDerivative i
        (fun y => ρ y * (ω.1 y i j * PDE.classicalGradient b y j)) x := by
    have he : (fun y => ρ y * (∑ j : Fin d, ω.1 y i j * PDE.classicalGradient b y j)) =
        (fun y => ∑ j : Fin d, ρ y * (ω.1 y i j * PDE.classicalGradient b y j)) := by
      funext y
      rw [Finset.mul_sum]
    rw [he]
    unfold coordinateDerivative
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      hρ.hasFDerivAt.fun_mul ((ha i j).hasFDerivAt.fun_mul (hgrad j x).hasFDerivAt))
    rw [hs.fderiv]
    simp only [ContinuousLinearMap.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hp := hρ.hasFDerivAt.fun_mul ((ha i j).hasFDerivAt.fun_mul (hgrad j x).hasFDerivAt)
    rw [hp.fderiv]
  have hgen := hbound hM R x
  change (∑ i : Fin d, coordinateDerivative i
    (fun y => ρ y * (∑ j : Fin d, ω.1 y i j * PDE.classicalGradient b y j)) x) ≤
      2 * α * ρ x * b x
  simp_rw [hflux, hterm]
  have hsum : (∑ i : Fin d, ∑ j : Fin d, ρ x *
      ((coordinateDerivative i (fun y => ω.1 y i j) x +
        2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
          coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j) *
          PDE.classicalGradient b x j + ω.1 x i j * PDE.classicalGradient
            (fun y => PDE.classicalGradient b y j) x i)) =
      ρ x * ((∑ j : Fin d, (∑ i : Fin d,
        (coordinateDerivative i (fun y => ω.1 y i j) x +
          2 * ((if i = ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ then lam else 0) -
            coordinateDerivative i (fun y => ω.2 y) x) * ω.1 x i j)) *
          PDE.classicalGradient b x j) +
        ∑ i : Fin d, ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
          (fun y => PDE.classicalGradient b y j) x i) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    · simp only [Finset.mul_sum]
  rw [hsum]
  have hm := mul_le_mul_of_nonneg_left hgen (positiveSourcePhysicalDensity ω hd lam x).le
  nlinarith

private theorem gmp_lipschitzWith_hasWeakPartialDerivative {d : ℕ} {L : ℝ≥0}
    {f : Vec d → ℝ} (hf : LipschitzWith L f) (i : Fin d) :
    HasWeakPartialDerivative univ i f
      (fun x => fderiv ℝ f x (unitVector i)) := by
  have hL_one : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by norm_num
  -- Part 1: f is locally integrable (Lipschitz implies continuous)
  have h_loc_f : LocallyIntegrableOn f univ volume :=
    hf.continuous.locallyIntegrable.locallyIntegrableOn univ
  -- Part 2: the derivative is locally integrable
  have h_loc_fderiv : LocallyIntegrableOn (fun x => fderiv ℝ f x (unitVector i)) univ volume := by
    have h_line : LocallyIntegrable (fun x => lineDeriv ℝ f x (unitVector i)) volume :=
      hf.locallyIntegrable_lineDeriv (unitVector i)
    have h_ae_eq : (fun x => lineDeriv ℝ f x (unitVector i)) =ᵐ[volume]
        (fun x => fderiv ℝ f x (unitVector i)) := by
      filter_upwards [hf.ae_differentiableAt] with x hx
      exact hx.lineDeriv_eq_fderiv (v := unitVector i)
    have h_line_on : LocallyIntegrableOn (fun x => lineDeriv ℝ f x (unitVector i)) univ volume :=
      h_line.locallyIntegrableOn univ
    -- Transfer local integrability via a.e. equality
    intro x hx
    rcases h_line_on x hx with ⟨t, ht, ht_int⟩
    refine ⟨t, ht, ?_⟩
    rwa [integrableOn_congr_fun_ae (ae_restrict_of_ae h_ae_eq)] at ht_int
  -- Part 3: the integral identity
  refine ⟨h_loc_f, h_loc_fderiv, ?_⟩
  intro φ hφ
  have hφ_contDiff : ContDiff ℝ (⊤ : ℕ∞) φ := hφ.1
  have hφ_compact : HasCompactSupport φ := hφ.2.1
  have hφ_diff : Differentiable ℝ φ :=
    hφ_contDiff.differentiable (by simp)
  -- Get Lipschitz constant for φ
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφ_compact hφ_contDiff (by simp)
  -- Apply integration by parts for line derivatives
  have h_ibp := hf.integral_lineDeriv_mul_eq (μ := volume) hC hφ_compact (unitVector i)
  -- h_ibp : ∫ x, lineDeriv ℝ f x (unitVector i) * φ x ∂volume =
  --         ∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume
  -- Convert lineDeriv φ to coordinateDerivative on RHS
  have h_lineDeriv_φ (x : Vec d) : lineDeriv ℝ φ x (-unitVector i) = -coordinateDerivative i φ x := by
    rw [(hφ_diff x).lineDeriv_eq_fderiv (v := -unitVector i), coordinateDerivative,
      ContinuousLinearMap.map_neg]
  have h_rhs : (∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume) =
      -(∫ x, coordinateDerivative i φ x * f x ∂volume) := by
    calc
      (∫ x, lineDeriv ℝ φ x (-unitVector i) * f x ∂volume)
          = (∫ x, (-coordinateDerivative i φ x) * f x ∂volume) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        simp [h_lineDeriv_φ x]
      _ = (∫ x, -(coordinateDerivative i φ x * f x) ∂volume) := by
        refine integral_congr_ae (ae_of_all _ (fun x => ?_))
        ring
      _ = -(∫ x, coordinateDerivative i φ x * f x ∂volume) := by rw [integral_neg]
  -- Convert lineDeriv f to fderiv f on LHS (a.e.)
  have h_ae_eq_fderiv : (fun x => lineDeriv ℝ f x (unitVector i)) =ᵐ[volume]
      (fun x => fderiv ℝ f x (unitVector i)) := by
    filter_upwards [hf.ae_differentiableAt] with x hx
    exact hx.lineDeriv_eq_fderiv (v := unitVector i)
  have h_lhs : (∫ x, lineDeriv ℝ f x (unitVector i) * φ x ∂volume) =
      (∫ x, fderiv ℝ f x (unitVector i) * φ x ∂volume) := by
    exact integral_congr_ae (h_ae_eq_fderiv.mul (ae_of_all _ (fun _ => rfl)))
  -- Combine everything
  calc
    (∫ x in univ, f x * coordinateDerivative i φ x) = (∫ x, f x * coordinateDerivative i φ x) := by
      rw [setIntegral_univ]
    _ = (∫ x, coordinateDerivative i φ x * f x) := by
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      ring
    _ = -(∫ x, fderiv ℝ f x (unitVector i) * φ x) := by
      rw [← h_lhs, h_ibp, h_rhs]
      simp
    _ = -(∫ x in univ, fderiv ℝ f x (unitVector i) * φ x) := by rw [setIntegral_univ]


/-- The weighted flux of a smooth function has its literal weak divergence. -/
theorem gmpPhysical_smooth_weightedFlux_hasWeakDivergence {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) {b : Vec d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b) :
    HasWeakDivergence univ
      (fun x i => sourcePhysicalDensity ω hd lam x *
        ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
      (fun x => ∑ i : Fin d, coordinateDerivative i
        (fun y => sourcePhysicalDensity ω hd lam y *
          ∑ j : Fin d, ω.1 y i j * PDE.classicalGradient b y j) x) := by
  let a := reducedCoefficient ω
  let φ : Fin d → Vec d → ℝ := fun j x =>
    sourceForceWeight hd lam x * PDE.classicalGradient b x j
  have hφ (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (φ j) := by
    have hf : ContDiff ℝ (⊤ : ℕ∞) (sourceForceWeight hd lam) := by
      unfold sourceForceWeight
      fun_prop
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => PDE.classicalGradient b x j) := by
      unfold PDE.classicalGradient
      exact (contDiff_infty_iff_fderiv.mp hb).2.clm_apply contDiff_const
    exact hf.mul hg
  have hLip (i j : Fin d) : LipschitzWith _ (fun x => a x i j) :=
    lipschitzWith_of_euclidean_bound _ (by positivity)
      ((Correctors.reducedCoefficient_operatorLipschitz hΛ hω).entry_bound i j)
  have hweak (i j : Fin d) := Correctors.hasWeakPartialDerivative_mul_smooth
    isOpen_univ i (gmp_lipschitzWith_hasWeakPartialDerivative (hLip i j) i) (hφ j)
  apply Correctors.hasWeakDivergence_of_coordinate_derivatives isOpen_univ
  intro i
  let F : Vec d → ℝ := fun x => ∑ j : Fin d, φ j x * a x i j
  let D : Vec d → ℝ := fun x => ∑ j : Fin d,
    (φ j x * coordinateDerivative i (fun y => a y i j) x +
      a x i j * coordinateDerivative i (φ j) x)
  have hw : HasWeakPartialDerivative univ i F D := by
    simpa [F, D, coordinateDerivative] using
      (Correctors.hasWeakPartialDerivative_finset_sum Finset.univ
        (fun j _ => hweak i j))
  have hF : F = (fun x => sourcePhysicalDensity ω hd lam x *
      ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j) := by
    funext x
    dsimp [F, φ, a, reducedCoefficient, sourcePhysicalDensity]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hD : D =ᵐ[volume] coordinateDerivative i F := by
    filter_upwards [(Filter.eventually_all.mpr fun j => (hLip i j).ae_differentiableAt)] with x hx
    unfold coordinateDerivative
    have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((hφ j).differentiable (by simp) x).hasFDerivAt.fun_mul (hx j).hasFDerivAt)
    change D x = fderiv ℝ F x (unitVector i)
    rw [show fderiv ℝ F x = _ from hs.fderiv]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    dsimp [D, coordinateDerivative]
  rw [← hF]
  apply Correctors.hasWeakPartialDerivative_congr_ae isOpen_univ hw
  · exact Filter.EventuallyEq.rfl
  · simpa only [Measure.restrict_univ] using hD

/-- The radial barrier is a weak supersolution against nonnegative smooth tests. -/
theorem gmpPhysical_radialBarrier_weak_supersolution {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ R : ℝ,
      ∀ ψ : Vec d → ℝ, IsSpatialTest univ ψ → (∀ x, 0 ≤ ψ x) →
        -(∫ x, 2 * α * sourcePhysicalDensity ω hd lam x *
          (M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) -
            Real.sqrt (1 + R ^ 2)))) * ψ x) ≤
        ∫ x, dot (fun i => sourcePhysicalDensity ω hd lam x *
          ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
            (fun z : Vec d => M * Real.exp
              (-k * (Real.sqrt (1 + euclideanSq z) - Real.sqrt (1 + R ^ 2)))) x j)
          (gradient ψ x) := by
  obtain ⟨k, hk, hbound⟩ :=
    gmpPhysical_radialBarrier_weightedFlux_supersolution_ae hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro M hM R ψ hψ hψ0
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSq x) := by
      unfold euclideanSq dot
      exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
    have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => Real.sqrt (1 + euclideanSq x)) := by
      apply (contDiff_const.add hsq).sqrt
      intro x
      have h : 0 ≤ euclideanSq x := by
        change 0 ≤ ∑ i, x i * x i
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      positivity
    exact contDiff_const.mul ((contDiff_const.mul (hr.sub contDiff_const)).exp)
  let F : Vec d → Vec d := fun x i => sourcePhysicalDensity ω hd lam x *
    ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, coordinateDerivative i (fun y => F y i) x
  let H : Vec d → ℝ := fun x => 2 * α * sourcePhysicalDensity ω hd lam x * b x
  have hw : HasWeakDivergence univ F D :=
    gmpPhysical_smooth_weightedFlux_hasWeakDivergence hd ω lam Λ hΛ hω hb
  have hD : Integrable (fun x => D x * ψ x) := by
    exact integrableOn_univ.mp (Correctors.integrableOn_mul_spatialTest hw.2.1 hψ)
  have hH : Integrable (fun x => H x * ψ x) := by
    have hc : Continuous H := (continuous_const.mul (continuousSourcePhysicalDensity ω hd lam)).mul hb.continuous
    have hl : LocallyIntegrableOn H univ volume := hc.locallyIntegrable.locallyIntegrableOn univ
    exact integrableOn_univ.mp (Correctors.integrableOn_mul_spatialTest hl hψ)
  have hineq : (∫ x, D x * ψ x) ≤ ∫ x, H x * ψ x := by
    apply integral_mono_ae hD hH
    filter_upwards [hbound hM R] with x hx
    exact mul_le_mul_of_nonneg_right hx (hψ0 x)
  have heq : (∫ x, dot (F x) (gradient ψ x)) = -(∫ x, D x * ψ x) := by
    simpa only [Measure.restrict_univ] using hw.2.2 ψ hψ
  change -(∫ x, H x * ψ x) ≤ ∫ x, dot (F x) (gradient ψ x)
  rw [heq]
  exact neg_le_neg hineq


/-- The literal divergence of the actual smooth weighted flux is locally square integrable. -/
theorem gmpPhysical_smooth_weightedFlux_divergence_memLp_compact {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) {b : Vec d → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    {K : Set (Vec d)} (hK : IsCompact K) :
    MemLp (fun x => ∑ i : Fin d, coordinateDerivative i
      (fun y => sourcePhysicalDensity ω hd lam y *
        ∑ j : Fin d, ω.1 y i j * PDE.classicalGradient b y j) x)
      2 (volume.restrict K) := by
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hcompact (g : Vec d → ℝ) (hg : Continuous g) :
      MemLp g ∞ (volume.restrict K) := by
    obtain ⟨B, hB⟩ := hK.bddAbove_image (continuous_norm.comp hg).continuousOn
    apply memLp_top_of_bound hg.aestronglyMeasurable.restrict B
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    exact hB (mem_image_of_mem _ hx)
  let a := reducedCoefficient ω
  let φ : Fin d → Vec d → ℝ := fun j x =>
    sourceForceWeight hd lam x * PDE.classicalGradient b x j
  have hφ (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (φ j) := by
    have hf : ContDiff ℝ (⊤ : ℕ∞) (sourceForceWeight hd lam) := by
      unfold sourceForceWeight
      fun_prop
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun x => PDE.classicalGradient b x j) := by
      unfold PDE.classicalGradient
      exact (contDiff_infty_iff_fderiv.mp hb).2.clm_apply contDiff_const
    exact hf.mul hg
  have hLip (i j : Fin d) : LipschitzWith _ (fun x => a x i j) :=
    lipschitzWith_of_euclidean_bound _ (by positivity)
      ((Correctors.reducedCoefficient_operatorLipschitz hΛ hω).entry_bound i j)
  have hder (i j : Fin d) : MemLp (coordinateDerivative i (fun x => a x i j))
      2 (volume.restrict K) := by
    apply MemLp.of_bound (measurable_fderiv_apply_const ℝ _ _).aestronglyMeasurable.restrict
      (Real.exp (2 * Λ) * (Λ + 2 * Λ ^ 2) * ((d : ℝ) + 1))
    filter_upwards with x
    calc
      ‖fderiv ℝ (fun x => a x i j) x (unitVector i)‖ ≤
          ‖fderiv ℝ (fun x => a x i j) x‖ * ‖unitVector i‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ * ‖unitVector i‖ :=
        mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ (hLip i j)) (norm_nonneg _)
      _ = _ := by
        simp only [unitVector, Pi.norm_single, norm_one, mul_one]
        rfl
  have hsum (i : Fin d) : MemLp (fun x => ∑ j : Fin d,
      (φ j x * coordinateDerivative i (fun y => a y i j) x +
        a x i j * coordinateDerivative i (φ j) x)) 2 (volume.restrict K) := by
    apply memLp_finset_sum
    intro j hj
    have h1 : MemLp ((coordinateDerivative i (fun x => a x i j)) * φ j)
        2 (volume.restrict K) :=
      (hder i j).mul' (hcompact (φ j) (hφ j).continuous)
    have hD2 : MemLp (coordinateDerivative i (φ j)) 2 (volume.restrict K) :=
      (hcompact (coordinateDerivative i (φ j))
        ((contDiff_infty_iff_fderiv.mp (hφ j)).2.clm_apply contDiff_const).continuous).mono_exponent (by simp)
    have h2 : MemLp ((coordinateDerivative i (φ j)) * (fun x => a x i j))
        2 (volume.restrict K) :=
      hD2.mul' (hcompact (fun x => a x i j) (hLip i j).continuous)
    convert h1.add h2 using 1
    funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  refine memLp_finset_sum Finset.univ (fun i _ => ?_)
  let F : Vec d → ℝ := fun x => ∑ j : Fin d, φ j x * a x i j
  have hF : F = (fun x => sourcePhysicalDensity ω hd lam x *
      ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j) := by
    funext x
    dsimp [F, φ, a, reducedCoefficient, sourcePhysicalDensity]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [← hF]
  apply (memLp_congr_ae ?_).mp (hsum i)
  filter_upwards [ae_restrict_of_ae (Filter.eventually_all.mpr fun j =>
      (hLip i j).ae_differentiableAt)] with x hx
  unfold coordinateDerivative
  have hs := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    ((hφ j).differentiable (by simp) x).hasFDerivAt.fun_mul (hx j).hasFDerivAt)
  change _ = fderiv ℝ F x (unitVector i)
  rw [show fderiv ℝ F x = _ from hs.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]


/-- The radial barrier inequality extends to nonnegative full force-H¹ tests
localized by a smooth cutoff. -/
theorem gmpPhysical_radialBarrier_cutoffH1_supersolution {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ R : ℝ,
      ∀ v : GMPForceH1 hd lam,
      let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v;
      (∀ᵐ x ∂volume, 0 ≤ g.value x) →
      ∀ r : ℝ, ∀ χ : Vec d → ℝ, IsSpatialTest (Metric.ball 0 r) χ →
      let b : Vec d → ℝ := fun x => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)));
      -(∫ x in Metric.ball 0 r, 2 * α * sourcePhysicalDensity ω hd lam x * b x *
        (χ x ^ 2 * g.value x)) ≤
      ∫ x in Metric.ball 0 r, dot (fun i => sourcePhysicalDensity ω hd lam x *
        ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
        (fun j => χ x ^ 2 * WithLp.ofLp (g.weakGradient x) j +
          2 * χ x * g.value x * coordinateDerivative j χ x) := by
  obtain ⟨k, hk, hbound⟩ :=
    gmpPhysical_radialBarrier_weightedFlux_supersolution_ae hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro M hM R v
  dsimp only
  intro hv r χ hχ
  let U : Set (Vec d) := Metric.ball 0 r
  let K : Set (Vec d) := Metric.closedBall 0 r
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  let F : Vec d → Vec d := fun x i => sourcePhysicalDensity ω hd lam x *
    ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j
  let D : Vec d → ℝ := fun x => ∑ i : Fin d, coordinateDerivative i (fun y => F y i) x
  let H : Vec d → ℝ := fun x => 2 * α * sourcePhysicalDensity ω hd lam x * b x
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hsq : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => euclideanSq x) := by
      unfold euclideanSq dot
      exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
    have hr : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => Real.sqrt (1 + euclideanSq x)) := by
      apply (contDiff_const.add hsq).sqrt
      intro x
      have h : 0 ≤ euclideanSq x := by
        change 0 ≤ ∑ i, x i * x i
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      positivity
    exact contDiff_const.mul ((contDiff_const.mul (hr.sub contDiff_const)).exp)
  have hlocal (q : Vec d → ℝ) (hq : Continuous q) : MemLp q 2 (volume.restrict U) := by
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) r).measure_lt_top.ne
    obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) r).bddAbove_image
      (continuous_norm.comp hq).continuousOn
    have hqK : MemLp q 2 (volume.restrict K) := by
      apply MemLp.of_bound hq.aestronglyMeasurable.restrict B
      filter_upwards [ae_restrict_mem (isCompact_closedBall (0 : Vec d) r).measurableSet] with x hx
      exact hB (mem_image_of_mem _ hx)
    exact hqK.mono_measure (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hu : MemLp g.value 2 (volume.restrict U) :=
    (gmpWeightedMemLp_restrict_isCompact _ (continuousSourceReducedDensity hd lam)
      (positiveSourceReducedDensity hd lam) g.value_memLp
      (isCompact_closedBall (0 : Vec d) r)).mono_measure
        (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hG (j : Fin d) : MemLp (fun x => WithLp.ofLp (g.weakGradient x) j)
      2 (volume.restrict U) :=
    (gmpWeightedMemLp_restrict_isCompact _ (continuousSourceReducedDensity hd lam)
      (positiveSourceReducedDensity hd lam) (gmpEuclideanMemLp_coordinate g.gradient_memLp j)
      (isCompact_closedBall (0 : Vec d) r)).mono_measure
        (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hF (i : Fin d) : MemLp (fun x => F x i) 2 (volume.restrict U) := by
    apply hlocal
    dsimp [F]
    apply (continuousSourcePhysicalDensity ω hd lam).mul
    apply continuous_finset_sum
    intro j hj
    exact (((continuous_apply j).comp ((continuous_apply i).comp ω.1.continuous)).mul
      (((contDiff_infty_iff_fderiv.mp hb).2.clm_apply contDiff_const).continuous))
  have hD : MemLp D 2 (volume.restrict U) :=
    (gmpPhysical_smooth_weightedFlux_divergence_memLp_compact hd ω lam Λ hΛ hω hb
      (isCompact_closedBall (0 : Vec d) r)).mono_measure
        (Measure.restrict_mono Metric.ball_subset_closedBall le_rfl)
  have hH : MemLp H 2 (volume.restrict U) :=
    hlocal H ((continuous_const.mul (continuousSourcePhysicalDensity ω hd lam)).mul hb.continuous)
  have hw : HasWeakGradient U g.value (fun x => WithLp.ofLp (g.weakGradient x)) :=
    fun i => (g.distributionalGradient i).restrict_subset (subset_univ U) MeasurableSet.univ
  have hdiv : HasWeakDivergence U F D :=
    (gmpPhysical_smooth_weightedFlux_hasWeakDivergence hd ω lam Λ hΛ hω hb).restrict_subset
      (subset_univ U) MeasurableSet.univ
  have heq := Correctors.weakDivergence_test_cutoff_H1 Metric.isOpen_ball hu hG hF hD hw hdiv hχ
  have hχ2 : MemLp (fun x => χ x ^ 2 * g.value x) 2 (volume.restrict U) := by
    have h1 := (Correctors.memLp_mul_spatialTest_univ Metric.isOpen_ball.measurableSet hu hχ).mono_measure
      (Measure.restrict_le_self (s := U))
    have h2 : MemLp (fun x => χ x * (χ x * g.value x)) 2 (volume.restrict U) :=
      hχ.1.continuous.memLp_top_of_hasCompactSupport hχ.2.1 _ |>.fun_mul h1
    convert h2 using 1
    funext x
    ring
  have hineq : (∫ x in U, D x * (χ x ^ 2 * g.value x)) ≤
      ∫ x in U, H x * (χ x ^ 2 * g.value x) := by
    apply integral_mono_ae (hD.integrable_mul hχ2) (hH.integrable_mul hχ2)
    filter_upwards [ae_restrict_of_ae (hbound hM R), ae_restrict_of_ae hv] with x hx hxv
    exact mul_le_mul_of_nonneg_right hx (mul_nonneg (sq_nonneg _) hxv)
  change -(∫ x in U, H x * (χ x ^ 2 * g.value x)) ≤
    ∫ x in U, dot (F x) (fun j => χ x ^ 2 * WithLp.ofLp (g.weakGradient x) j +
      2 * χ x * g.value x * coordinateDerivative j χ x)
  rw [heq]
  exact neg_le_neg hineq


/-- The cutoff supersolution test applies to the actual resolvent excess. -/
theorem gmpPhysicalResolvent_radialExcess_cutoff_supersolution {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {M : ℝ},
      0 ≤ M → ∀ R : ℝ,
      ∃ v : GMPForceH1 hd lam,
        (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
          physicalReversibleMeasure ω hd lam]
          (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
            M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0) ∧
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
          Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
          {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
            gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
            (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
              (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
              WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
                (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)) ∧
        ∀ r : ℝ, ∀ χ : Vec d → ℝ, IsSpatialTest (Metric.ball 0 r) χ →
        let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v;
        let b : Vec d → ℝ := fun x => M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)));
        -(∫ x in Metric.ball 0 r, 2 * α * sourcePhysicalDensity ω hd lam x * b x *
          (χ x ^ 2 * g.value x)) ≤
        ∫ x in Metric.ball 0 r, dot (fun i => sourcePhysicalDensity ω hd lam x *
          ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
          (fun j => χ x ^ 2 * WithLp.ofLp (g.weakGradient x) j +
            2 * χ x * g.value x * coordinateDerivative j χ x) := by
  obtain ⟨k, hk, htest⟩ :=
    gmpPhysical_radialBarrier_cutoffH1_supersolution hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f M hM R
  obtain ⟨v, hv, hgrad⟩ :=
    gmpPhysicalResolvent_radialExcess_exists hd ω lam Λ hΛ hω α hα f hM hk.le R
  refine ⟨v, hv, hgrad, ?_⟩
  have hg : (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value =ᵐ[
        physicalReversibleMeasure ω hd lam] densityWeightedH1SpaceValue v :=
    (gmp_force_ae_iff_physical hd ω lam _).mp
      (gmpH1Representative_value_ae (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v)
  have hval := gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v
  have hp := (gmpVolume_absolutelyContinuous_physical hd ω lam).ae_eq
    (hg.trans (hval.symm.trans hv))
  have hnonneg : ∀ᵐ x ∂volume, 0 ≤
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
    filter_upwards [hp] with x hx
    rw [hx]
    exact le_max_right _ _
  exact htest hM R v hnonneg


/-- On the positive-excess set, both the radial barrier and its gradient are
weighted square-integrable, even when the barrier itself is not. -/
theorem gmpPhysicalResolvent_radialBarrier_indicator_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) :
    let u := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f
    let b : Vec d → ℝ := fun x => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
    MemLp ({x | b x < u x}.indicator b) 2 (physicalReversibleMeasure ω hd lam) ∧
    MemLp ({x | b x < u x}.indicator
      (fun x => WithLp.toLp 2 (PDE.classicalGradient b x))) 2
      (physicalReversibleMeasure ω hd lam) := by
  classical
  let m := physicalReversibleMeasure ω hd lam
  let u := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hu : MemLp (fun x => u x) 2 m := Lp.memLp u
  have hb : ContDiff ℝ 1 b := gmpPhysical_radialBarrier_contDiff M k R
  have hbmeas : AEStronglyMeasurable b m := hb.continuous.aestronglyMeasurable
  have hset : NullMeasurableSet {x | b x < u x} m :=
    nullMeasurableSet_lt hbmeas.aemeasurable hu.aemeasurable
  have hb0 : ∀ x, 0 ≤ b x := fun x => mul_nonneg hM (Real.exp_pos _).le
  constructor
  · refine hu.mono (hbmeas.indicator₀ hset) (ae_of_all _ fun x => ?_)
    by_cases hx : b x < u x
    · rw [Set.indicator_of_mem (show x ∈ {x | b x < u x} from hx)]
      change |b x| ≤ |u x|
      rw [abs_of_nonneg (hb0 x)]
      exact (le_of_lt hx).trans (le_abs_self (u x))
    · rw [Set.indicator_of_notMem (show x ∉ {x | b x < u x} from hx), norm_zero]
      exact norm_nonneg _
  · apply gmpWeightedMemLp_indicator_barrierGradient hu hbmeas
      ((PiLp.continuous_toLp 2 _).comp
        (PDE.ContDiff.continuous_classicalGradient hb)).aestronglyMeasurable hk
      (ae_of_all _ hb0)
    exact ae_of_all _ fun x => gmpPhysical_radialBarrier_gradient_bound hM hk R x


/-- The barrier times an actual positive-excess test is integrable, although
    the barrier need not be square-integrable on the whole space. -/
theorem gmpPhysicalResolvent_radialBarrier_mul_excess_integrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ)
    (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0)) :
    Integrable (fun x => (M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) *
      gmpPhysicalH1Value hd ω lam Λ hω v x) (physicalReversibleMeasure ω hd lam) := by
  let u := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hb : MemLp ({x | b x < u x}.indicator b) 2 (physicalReversibleMeasure ω hd lam) :=
    (gmpPhysicalResolvent_radialBarrier_indicator_memLp hd ω lam Λ hΛ hω α hα f hM hk R).1
  have hi := hb.integrable_mul (Lp.memLp (gmpPhysicalH1Value hd ω lam Λ hω v))
  apply hi.congr
  filter_upwards [hv] with x hx
  change _ = b x * gmpPhysicalH1Value hd ω lam Λ hω v x
  by_cases h : b x < u x
  · simp [Set.indicator_of_mem, h]
  · have hz : gmpPhysicalH1Value hd ω lam Λ hω v x = 0 := by
      rw [hx]
      change max (u x - b x) 0 = 0
      exact max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
    simp [Set.indicator_of_notMem, h, hz]


/-- The barrier flux paired with the actual excess gradient is integrable.
    The excess-gradient identity expresses it through two full H¹ energies. -/
theorem gmpPhysicalResolvent_radialBarrier_flux_excess_integrable {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (R : ℝ) (v : GMPForceH1 hd lam)
    (hg : (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
        Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
        (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
          (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
          WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
            (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x))) :
    Integrable (fun x => (1 / 2 : ℝ) * dot
      (PDE.classicalGradient (fun y : Vec d => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)
      ((ω.1 x).mulVec (WithLp.ofLp
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))))
      (physicalReversibleMeasure ω hd lam) := by
  let u := gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hi := (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω u v).sub
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω v v)
  apply hi.congr
  filter_upwards [hg] with x hx
  change (1 / 2 : ℝ) * dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear
      hd ω lam Λ hω u x)) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))) -
    (1 / 2 : ℝ) * dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear
      hd ω lam Λ hω v x)) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))) =
    (1 / 2 : ℝ) * dot (PDE.classicalGradient b x) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
  by_cases h : b x < gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x
  · have hx' := hx
    rw [Set.indicator_of_mem (show x ∈ {x | b x < _} from h)] at hx'
    have he : WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x) -
        WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) =
        PDE.classicalGradient b x := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z i) hx'
      simp only [PiLp.sub_apply] at hi
      change _ - _ = PDE.classicalGradient b x i
      change _ = _ - PDE.classicalGradient b x i at hi
      linarith
    rw [← he]
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {x | b x < _} from h)] at hx
    rw [hx]
    simp [dot, Matrix.mulVec]


/-- Each barrier-gradient coordinate times the excess is integrable; this
    supplies the integrable majorants for cutoff-gradient error terms. -/
theorem gmpPhysicalResolvent_radialBarrier_gradient_mul_excess_integrable {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ)
    (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0))
    (i : Fin d) :
    Integrable (fun x => PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x i *
      gmpPhysicalH1Value hd ω lam Λ hω v x) (physicalReversibleMeasure ω hd lam) := by
  let u := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  let G : Vec d → EuclideanSpace ℝ (Fin d) :=
    {x | b x < u x}.indicator (fun x => WithLp.toLp 2 (PDE.classicalGradient b x))
  have hG : MemLp G 2 (physicalReversibleMeasure ω hd lam) :=
    (gmpPhysicalResolvent_radialBarrier_indicator_memLp hd ω lam Λ hΛ hω α hα f hM hk R).2
  have hi := ((memLp_piLp_iff.mp hG) i).integrable_mul
    (Lp.memLp (gmpPhysicalH1Value hd ω lam Λ hω v))
  apply hi.congr
  filter_upwards [hv] with x hx
  change G x i * gmpPhysicalH1Value hd ω lam Λ hω v x =
    PDE.classicalGradient b x i * gmpPhysicalH1Value hd ω lam Λ hω v x
  by_cases h : b x < u x
  · simp [G, Set.indicator_of_mem, h]
  · have hz : gmpPhysicalH1Value hd ω lam Λ hω v x = 0 := by
      rw [hx]
      change max (u x - b x) 0 = 0
      exact max_eq_right (sub_nonpos.mpr (le_of_not_gt h))
    simp [hz]


/-- An integrable spatial flux has vanishing pairing with expanding cutoff
    gradients, for any measure on the physical coordinate space. -/
theorem gmp_cutoff_flux_tendsto_zero {d : ℕ} (μ : Measure (Vec d))
    (F : Vec d → Vec d) (hF : ∀ j : Fin d, Integrable (fun x => F x j) μ)
    (χ : ℕ → Vec d → ℝ) (B : ℝ)
    (hχ : ∀ n x, |χ n x| ≤ 1)
    (hD : ∀ n x, ‖gradient (χ n) x‖ ≤ B / (n + 1 : ℕ)) :
    Tendsto (fun n => ∫ x, χ n x * dot (F x) (gradient (χ n) x) ∂μ)
      atTop (𝓝 0) := by
  let S : Vec d → ℝ := fun x => ∑ j, |F x j|
  have hS : Integrable S μ := integrable_finsetSum _ (fun j _ => (hF j).abs)
  have hbnd (n : ℕ) (x : Vec d) :
      ‖χ n x * dot (F x) (gradient (χ n) x)‖ ≤
        (B / (n + 1 : ℕ)) * S x := by
    have hd : |dot (F x) (gradient (χ n) x)| ≤ S x * (B / (n + 1 : ℕ)) := by
      calc
        _ ≤ ∑ j, |F x j * gradient (χ n) x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, |F x j| * (B / (n + 1 : ℕ)) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          have hc : |gradient (χ n) x j| ≤ ‖gradient (χ n) x‖ := by
            simpa only [Real.norm_eq_abs] using norm_le_pi_norm (gradient (χ n) x) j
          exact mul_le_mul_of_nonneg_left (hc.trans (hD n x)) (abs_nonneg _)
        _ = _ := (Finset.sum_mul _ _ _).symm
    rw [Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ 1 * (S x * (B / (n + 1 : ℕ))) :=
        mul_le_mul (hχ n x) hd (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hint (n : ℕ) : ‖∫ x, χ n x * dot (F x) (gradient (χ n) x) ∂μ‖ ≤
      (B / (n + 1 : ℕ)) * ∫ x, S x ∂μ := by
    calc
      _ ≤ ∫ x, (B / (n + 1 : ℕ)) * S x ∂μ :=
        norm_integral_le_of_norm_le (hS.const_mul _) (Eventually.of_forall (hbnd n))
      _ = _ := integral_const_mul _ _
  have ht : Tendsto (fun n : ℕ => (B / (n + 1 : ℕ)) * ∫ x, S x ∂μ) atTop (𝓝 0) := by
    have hd : Tendsto (fun n : ℕ => B / (n + 1 : ℕ)) atTop (𝓝 0) := by
      simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
    simpa using hd.mul_const (∫ x, S x ∂μ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun n => norm_nonneg _) hint


/-- The actual coefficient-barrier flux times the excess has integrable
    coordinates, so its expanding-cutoff error tends to zero. -/
theorem gmpPhysicalResolvent_radialBarrier_cutoff_error_tendsto_zero {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ)
    (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0))
    (χ : ℕ → Vec d → ℝ) (B : ℝ) (hχ : ∀ n x, |χ n x| ≤ 1)
    (hD : ∀ n x, ‖gradient (χ n) x‖ ≤ B / (n + 1 : ℕ)) :
    Tendsto (fun n => ∫ x, χ n x * dot
      (fun i => (∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
        (fun y : Vec d => M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x j) *
        gmpPhysicalH1Value hd ω lam Λ hω v x)
      (gradient (χ n) x) ∂physicalReversibleMeasure ω hd lam) atTop (𝓝 0) := by
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  let V := gmpPhysicalH1Value hd ω lam Λ hω v
  let F : Vec d → Vec d := fun x i =>
    (∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j) * V x
  have hF (i : Fin d) : Integrable (fun x => F x i) (physicalReversibleMeasure ω hd lam) := by
    have hs : Integrable (fun x => ∑ j : Fin d,
        (PDE.classicalGradient b x j * V x) * ω.1 x i j)
        (physicalReversibleMeasure ω hd lam) := by
      apply integrable_finsetSum
      intro j hj
      apply (gmpPhysicalResolvent_radialBarrier_gradient_mul_excess_integrable
        hd ω lam Λ hΛ hω α hα f hM hk R v hv j).mul_bdd
        (((continuous_apply j).comp ((continuous_apply i).comp ω.1.continuous)).aestronglyMeasurable)
      filter_upwards [] with x
      change |ω.1 x i j| ≤ Λ
      exact EinsteinRelation.Correctors.IsElliptic.entry_abs_le (by linarith) hω.1 x i j
    apply hs.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp [F]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  exact gmp_cutoff_flux_tendsto_zero _ F hF χ B hχ hD


/-- Restriction commutes with integration against the literal physical density. -/
theorem gmpPhysical_setIntegral_eq_volume {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (U : Set (Vec d)) (hU : MeasurableSet U)
    (f : Vec d → ℝ) :
    (∫ x in U, f x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in U, sourcePhysicalDensity ω hd lam x * f x := by
  rw [← integral_indicator hU, gmpPhysical_integral_eq_volume, ← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx]

/-- Expanding bounded cutoffs preserve the integral of every physical L¹
    quantity, providing the bulk limit in the barrier comparison. -/
theorem gmp_integral_cutoff_sq_tendsto {d : ℕ} (μ : Measure (Vec d))
    (q : Vec d → ℝ) (hq : Integrable q μ) (χ : ℕ → Vec d → ℝ)
    (hχ : ∀ n, Continuous (χ n)) (hb : ∀ n x, |χ n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) :
    Tendsto (fun n => ∫ x, q x * χ n x ^ 2 ∂μ) atTop (𝓝 (∫ x, q x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖q x‖)
  · intro n
    exact hq.aestronglyMeasurable.mul ((hχ n).pow 2).aestronglyMeasurable
  · exact hq.norm
  · intro n
    exact Filter.Eventually.of_forall fun x => by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg (q x))
        (by nlinarith [hb n x, abs_nonneg (χ n x)])
  · exact Filter.Eventually.of_forall fun x => by
      simpa using ((hlim x).pow 2).const_mul (q x)


/-- The local weighted representative has the canonical physical value almost everywhere. -/
theorem gmpPhysicalH1Representative_value_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) (v : GMPForceH1 hd lam) :
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value
      =ᵐ[physicalReversibleMeasure ω hd lam] gmpPhysicalH1Value hd ω lam Λ hω v := by
  have h₁ : (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value
      =ᵐ[physicalReversibleMeasure ω hd lam] densityWeightedH1SpaceValue v :=
    (gmp_force_ae_iff_physical hd ω lam _).mp
      (gmpH1Representative_value_ae (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v)
  filter_upwards [h₁, gmpPhysicalH1Value_ae_eq hd ω lam Λ hω v] with x hx hy
  exact hx.trans hy.symm

/-- The local weighted representative has the canonical physical gradient almost everywhere. -/
theorem gmpPhysicalH1Representative_gradient_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) (v : GMPForceH1 hd lam) :
    (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).weakGradient
      =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :=
  (gmpPhysicalH1Gradient_ae hd ω lam Λ hω v).symm

/-- Convert a localized scalar pairing with an H¹ value to the weighted volume integral. -/
theorem gmpPhysicalH1Representative_setIntegral_value {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) (v : GMPForceH1 hd lam)
    (U : Set (Vec d)) (hU : MeasurableSet U) (q : Vec d → ℝ) :
    (∫ x in U, q x * gmpPhysicalH1Value hd ω lam Λ hω v x
      ∂physicalReversibleMeasure ω hd lam) =
    ∫ x in U, sourcePhysicalDensity ω hd lam x * q x *
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
  rw [gmpPhysical_setIntegral_eq_volume hd ω lam U hU]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ((gmpPhysical_ae_iff_volume hd ω lam _).mp
    (gmpPhysicalH1Representative_value_ae hd ω lam Λ hω v))] with x hx
  rw [hx]
  ring

/-- Convert a localized flux pairing with physical H¹ value and gradient to weighted volume. -/
theorem gmpPhysicalH1Representative_setIntegral_flux {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) (v : GMPForceH1 hd lam)
    (U : Set (Vec d)) (hU : MeasurableSet U) (F B : Vec d → Vec d) (a : Vec d → ℝ) :
    (∫ x in U, dot (F x) (fun i => a x * WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) i +
        gmpPhysicalH1Value hd ω lam Λ hω v x * B x i)
      ∂physicalReversibleMeasure ω hd lam) =
    ∫ x in U, dot (fun i => sourcePhysicalDensity ω hd lam x * F x i)
      (fun i => a x * WithLp.ofLp
        ((densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).weakGradient x) i +
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x * B x i) := by
  rw [gmpPhysical_setIntegral_eq_volume hd ω lam U hU]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae ((gmpPhysical_ae_iff_volume hd ω lam _).mp
      (gmpPhysicalH1Representative_value_ae hd ω lam Λ hω v)),
    ae_restrict_of_ae ((gmpPhysical_ae_iff_volume hd ω lam _).mp
      (gmpPhysicalH1Representative_gradient_ae hd ω lam Λ hω v))] with x hx hg
  rw [hx, hg]
  simp only [dot, ← Finset.mul_sum, mul_assoc]

/-- The cutoff barrier supersolution, expressed with the physical H¹ representatives. -/
theorem gmpPhysical_radialBarrier_cutoffH1_physical {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ R : ℝ,
      ∀ v : GMPForceH1 hd lam,
      let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v;
      (∀ᵐ x ∂volume, 0 ≤ g.value x) →
      ∀ r : ℝ, ∀ χ : Vec d → ℝ, IsSpatialTest (Metric.ball 0 r) χ →
      let b : Vec d → ℝ := fun x => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)));
      -(∫ x in Metric.ball 0 r, (2 * α * b x * χ x ^ 2) *
        gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x in Metric.ball 0 r, dot
        (fun i => ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
        (fun j => χ x ^ 2 * WithLp.ofLp
          (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) j +
          gmpPhysicalH1Value hd ω lam Λ hω v x *
            (2 * χ x * coordinateDerivative j χ x))
        ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨k, hk, htest⟩ :=
    gmpPhysical_radialBarrier_cutoffH1_supersolution hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro M hM R v
  dsimp only
  intro hv r χ hχ
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  rw [gmpPhysicalH1Representative_setIntegral_value hd ω lam Λ hω v _
        Metric.isOpen_ball.measurableSet,
      gmpPhysicalH1Representative_setIntegral_flux hd ω lam Λ hω v _
        Metric.isOpen_ball.measurableSet]
  have h := htest hM R v hv r χ hχ
  dsimp only at h
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- A compactly supported smooth spatial function is a test on some centered ball. -/
theorem gmp_compactSpatialTest_exists_ball {d : ℕ} (χ : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ) :
    ∃ r : ℝ, IsSpatialTest (Metric.ball 0 r) χ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hc.isBounded
  refine ⟨R + 1, hχ, hc, ?_⟩
  exact hR.trans (Metric.closedBall_subset_ball (by linarith))

/-- An integral may be restricted to a measurable set containing its support. -/
theorem gmp_integral_eq_setIntegral_of_zero_outside {d : ℕ} (μ : Measure (Vec d))
    (U : Set (Vec d)) (hU : MeasurableSet U) (q : Vec d → ℝ)
    (hq : ∀ x, x ∉ U → q x = 0) :
    (∫ x, q x ∂μ) = ∫ x in U, q x ∂μ := by
  rw [← integral_indicator hU]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ U
  · simp [hx]
  · simp [hx, hq x hx]

/-- The physical barrier cutoff inequality on the whole space. -/
theorem gmpPhysical_radialBarrier_compactH1_physical {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ {M : ℝ}, 0 ≤ M → ∀ R : ℝ,
      ∀ v : GMPForceH1 hd lam,
      let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v;
      (∀ᵐ x ∂volume, 0 ≤ g.value x) →
      ∀ χ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let b : Vec d → ℝ := fun x => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)));
      -(∫ x, (2 * α * b x * χ x ^ 2) *
        gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, dot
        (fun i => ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
        (fun j => χ x ^ 2 * WithLp.ofLp
          (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) j +
          gmpPhysicalH1Value hd ω lam Λ hω v x *
            (2 * χ x * coordinateDerivative j χ x))
        ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨k, hk, htest⟩ :=
    gmpPhysical_radialBarrier_cutoffH1_physical hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro M hM R v
  dsimp only
  intro hv χ hχ hc
  obtain ⟨r, hr⟩ := gmp_compactSpatialTest_exists_ball χ hχ hc
  have hzero (x : Vec d) (hx : x ∉ Metric.ball (0 : Vec d) r) : χ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hr.2.2 h))
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hl : (∫ x, (2 * α * b x * χ x ^ 2) *
      gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in Metric.ball 0 r, (2 * α * b x * χ x ^ 2) *
      gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam := by
    apply gmp_integral_eq_setIntegral_of_zero_outside _ _ Metric.isOpen_ball.measurableSet
    intro x hx
    simp [hzero x hx]
  have hr' : (∫ x, dot
      (fun i => ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
      (fun j => χ x ^ 2 * WithLp.ofLp
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) j +
        gmpPhysicalH1Value hd ω lam Λ hω v x *
          (2 * χ x * coordinateDerivative j χ x)) ∂physicalReversibleMeasure ω hd lam) =
      ∫ x in Metric.ball 0 r, dot
      (fun i => ∑ j : Fin d, ω.1 x i j * PDE.classicalGradient b x j)
      (fun j => χ x ^ 2 * WithLp.ofLp
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) j +
        gmpPhysicalH1Value hd ω lam Λ hω v x *
          (2 * χ x * coordinateDerivative j χ x)) ∂physicalReversibleMeasure ω hd lam := by
    apply gmp_integral_eq_setIntegral_of_zero_outside _ _ Metric.isOpen_ball.measurableSet
    intro x hx
    simp [hzero x hx, dot]
  rw [hl, hr']
  exact htest hM R v hv r χ hr

/-- Remove expanding cutoffs from a scalar inequality once the bulk and error limits are known. -/
theorem gmp_cutoff_inequality_limit {d : ℕ} (μ : Measure (Vec d))
    (q p : Vec d → ℝ) (hq : Integrable q μ) (hp : Integrable p μ)
    (χ : ℕ → Vec d → ℝ) (hχ : ∀ n, Continuous (χ n))
    (hb : ∀ n x, |χ n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (htest : ∀ n, -(∫ x, q x * χ n x ^ 2 ∂μ) ≤
      (∫ x, p x * χ n x ^ 2 ∂μ) + e n) :
    -(∫ x, q x ∂μ) ≤ ∫ x, p x ∂μ := by
  have hq' := (gmp_integral_cutoff_sq_tendsto μ q hq χ hχ hb hlim).neg
  have hp' := (gmp_integral_cutoff_sq_tendsto μ p hp χ hχ hb hlim).add he
  have h := le_of_tendsto_of_tendsto' hq' hp' htest
  simpa only [add_zero] using h

/-- Each coordinate of the physical barrier flux times the positive excess is integrable. -/
theorem gmpPhysicalResolvent_radialBarrier_flux_value_integrable {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ)
    (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0))
    (i : Fin d) :
    Integrable (fun x => (∑ j : Fin d, ω.1 x i j * PDE.classicalGradient
      (fun y : Vec d => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x j) *
      gmpPhysicalH1Value hd ω lam Λ hω v x) (physicalReversibleMeasure ω hd lam) := by
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  let V := gmpPhysicalH1Value hd ω lam Λ hω v
  have hs : Integrable (fun x => ∑ j : Fin d,
      (PDE.classicalGradient b x j * V x) * ω.1 x i j)
      (physicalReversibleMeasure ω hd lam) := by
    apply integrable_finsetSum
    intro j hj
    apply (gmpPhysicalResolvent_radialBarrier_gradient_mul_excess_integrable
      hd ω lam Λ hΛ hω α hα f hM hk R v hv j).mul_bdd
      (((continuous_apply j).comp ((continuous_apply i).comp ω.1.continuous)).aestronglyMeasurable)
    filter_upwards [] with x
    change |ω.1 x i j| ≤ Λ
    exact EinsteinRelation.Correctors.IsElliptic.entry_abs_le (by linarith) hω.1 x i j
  apply hs.congr (Filter.Eventually.of_forall fun x => ?_)
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- A smooth bounded cutoff and its bounded gradient preserve integrability of an L¹ flux. -/
theorem gmp_cutoff_flux_integrable {d : ℕ} (μ : Measure (Vec d))
    (F : Vec d → Vec d) (hF : ∀ j : Fin d, Integrable (fun x => F x j) μ)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℝ) (hb : ∀ x, |χ x| ≤ 1) (hD : ∀ x, ‖gradient χ x‖ ≤ B) :
    Integrable (fun x => χ x * dot (F x) (gradient χ x)) μ := by
  have hi (j : Fin d) : Integrable (fun x => F x j * gradient χ x j) μ := by
    have hcj : Continuous (fun x => gradient χ x j) := by
      exact (((contDiff_infty_iff_fderiv.mp hχ).2).clm_apply contDiff_const).continuous
    apply (hF j).mul_bdd (c := B) hcj.aestronglyMeasurable
    filter_upwards [] with x
    have hj : |gradient χ x j| ≤ ‖gradient χ x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (gradient χ x) j
    exact hj.trans (hD x)
  have hs : Integrable (fun x => dot (F x) (gradient χ x)) μ := by
    exact integrable_finsetSum _ (fun j _ => hi j)
  have ht := hs.mul_bdd hχ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  simpa only [mul_comm] using ht

/-- Separate the bulk and cutoff-gradient pieces of the physical flux pairing. -/
theorem gmp_cutoff_flux_decompose {d : ℕ} (F G D : Vec d) (v c : ℝ) :
    dot F (fun j => c ^ 2 * G j + v * (2 * c * D j)) =
      dot F G * c ^ 2 + 2 * (c * dot (fun i => F i * v) D) := by
  simp only [dot, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Integrating the cutoff flux separates its bulk from its gradient error. -/
theorem gmp_cutoff_flux_integral_decompose {d : ℕ} (μ : Measure (Vec d))
    (F G : Vec d → Vec d) (v χ : Vec d → ℝ)
    (hp : Integrable (fun x => dot (F x) (G x)) μ)
    (hF : ∀ j : Fin d, Integrable (fun x => F x j * v x) μ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (B : ℝ) (hb : ∀ x, |χ x| ≤ 1) (hD : ∀ x, ‖gradient χ x‖ ≤ B) :
    (∫ x, dot (F x) (fun j => χ x ^ 2 * G x j +
        v x * (2 * χ x * gradient χ x j)) ∂μ) =
      (∫ x, dot (F x) (G x) * χ x ^ 2 ∂μ) +
        2 * ∫ x, χ x * dot (fun j => F x j * v x) (gradient χ x) ∂μ := by
  have hp' : Integrable (fun x => dot (F x) (G x) * χ x ^ 2) μ := by
    apply hp.mul_bdd (c := 1) ((hχ.continuous.pow 2).aestronglyMeasurable)
    filter_upwards [] with x
    change |χ x ^ 2| ≤ 1
    rw [abs_pow]
    nlinarith [hb x, abs_nonneg (χ x)]
  have he := gmp_cutoff_flux_integrable μ (fun x j => F x j * v x)
    hF χ hχ B hb hD
  calc
    _ = ∫ x, (dot (F x) (G x) * χ x ^ 2 +
        2 * (χ x * dot (fun j => F x j * v x) (gradient χ x))) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => gmp_cutoff_flux_decompose
        (F x) (G x) (gradient χ x) (v x) (χ x))
    _ = _ := by rw [integral_add hp' (he.const_mul 2), integral_const_mul]

/-- Remove smooth expanding cutoffs from a flux supersolution. -/
theorem gmp_cutoff_flux_supersolution_limit {d : ℕ} (μ : Measure (Vec d))
    (q : Vec d → ℝ) (F G : Vec d → Vec d) (v : Vec d → ℝ)
    (hq : Integrable q μ) (hp : Integrable (fun x => dot (F x) (G x)) μ)
    (hF : ∀ j : Fin d, Integrable (fun x => F x j * v x) μ)
    (χ : ℕ → Vec d → ℝ) (B : ℝ)
    (hχ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n))
    (hb : ∀ n x, |χ n x| ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hD : ∀ n x, ‖gradient (χ n) x‖ ≤ B / (n + 1 : ℕ))
    (htest : ∀ n, -(∫ x, q x * χ n x ^ 2 ∂μ) ≤
      ∫ x, dot (F x) (fun j => χ n x ^ 2 * G x j +
        v x * (2 * χ n x * gradient (χ n) x j)) ∂μ) :
    -(∫ x, q x ∂μ) ≤ ∫ x, dot (F x) (G x) ∂μ := by
  let e : ℕ → ℝ := fun n => 2 * ∫ x, χ n x * dot
    (fun j => F x j * v x) (gradient (χ n) x) ∂μ
  have he : Tendsto e atTop (𝓝 0) := by
    simpa [e] using (gmp_cutoff_flux_tendsto_zero μ
      (fun x j => F x j * v x) hF χ B hb hD).const_mul 2
  apply gmp_cutoff_inequality_limit μ q (fun x => dot (F x) (G x)) hq hp
    χ (fun n => (hχ n).1.continuous) hb hlim e he
  intro n
  have h := htest n
  rw [gmp_cutoff_flux_integral_decompose μ F G v (χ n) hp hF
    (hχ n).1 (B / (n + 1 : ℕ)) (hb n) (hD n)] at h
  exact h


/-- The actual radial excess satisfies the full physical barrier supersolution. -/
theorem gmpPhysicalResolvent_radialExcess_supersolution {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) {M : ℝ},
      0 ≤ M → ∀ R : ℝ,
      ∃ v : GMPForceH1 hd lam,
        (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
          physicalReversibleMeasure ω hd lam]
          (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
            M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0) ∧
        (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
          Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
          {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
            gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
            (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
              (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
              WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
                (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)) ∧
        let b : Vec d → ℝ := fun x => M * Real.exp
          (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)));
        -(∫ x, α * b x * gmpPhysicalH1Value hd ω lam Λ hω v x
          ∂physicalReversibleMeasure ω hd lam) ≤
        ∫ x, (1 / 2 : ℝ) * dot (PDE.classicalGradient b x)
          ((ω.1 x).mulVec (WithLp.ofLp
            (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
          ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨k, hk, htest⟩ :=
    gmpPhysical_radialBarrier_compactH1_physical hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f M hM R
  obtain ⟨v, hv, hg⟩ :=
    gmpPhysicalResolvent_radialExcess_exists hd ω lam Λ hΛ hω α hα f hM hk.le R
  refine ⟨v, hv, hg, ?_⟩
  let μ := physicalReversibleMeasure ω hd lam
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  let V : Vec d → ℝ := gmpPhysicalH1Value hd ω lam Λ hω v
  let G : Vec d → Vec d := fun x => WithLp.ofLp
    (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)
  let F : Vec d → Vec d := fun x => (ω.1 x).mulVec (PDE.classicalGradient b x)
  let q : Vec d → ℝ := fun x => 2 * α * b x * V x
  have hn : ∀ᵐ x ∂volume, 0 ≤
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
    have hrep := gmpPhysicalH1Representative_value_ae hd ω lam Λ hω v
    have h := (gmpVolume_absolutelyContinuous_physical hd ω lam).ae_eq (hrep.trans hv)
    filter_upwards [h] with x hx
    rw [hx]
    exact le_max_right _ _
  have hq : Integrable q μ := by
    have h := (gmpPhysicalResolvent_radialBarrier_mul_excess_integrable
      hd ω lam Λ hΛ hω α hα f hM hk.le R v hv).const_mul (2 * α)
    apply h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp [q, b, V]
    ring
  have hp : Integrable (fun x => dot (F x) (G x)) μ := by
    have h := (gmpPhysicalResolvent_radialBarrier_flux_excess_integrable
      hd ω lam Λ hΛ hω α hα f R v hg).const_mul 2
    apply h.congr (Filter.Eventually.of_forall fun x => ?_)
    dsimp [F, G, b]
    rw [gmp_dot_mulVec_symm (ω.1 x) (hω.1 x).1]
    simp only [dot, mul_comm]
    ring
  have hF (j : Fin d) : Integrable (fun x => F x j * V x) μ := by
    exact gmpPhysicalResolvent_radialBarrier_flux_value_integrable
      hd ω lam Λ hΛ hω α hα f hM hk.le R v hv j
  obtain ⟨χ, B, hB, hχ, hb, hlim, hD⟩ := EinsteinRelation.Correctors.akm_exists_scaled_cutoffs d
  have hb' : ∀ n x, |χ n x| ≤ 1 := by
    intro n x
    rw [abs_of_nonneg (hb n x).1]
    exact (hb n x).2
  have hc : ∀ n, -(∫ x, q x * χ n x ^ 2 ∂μ) ≤
      ∫ x, dot (F x) (fun j => χ n x ^ 2 * G x j +
        V x * (2 * χ n x * gradient (χ n) x j)) ∂μ := by
    intro n
    have h := htest hM R v hn (χ n) (hχ n).1 (hχ n).2
    convert h using 1
    · congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by dsimp [q, V, b]; ring
    · rfl
  have h := gmp_cutoff_flux_supersolution_limit μ q F G V hq hp hF
    χ B hχ hb' hlim hD hc
  have hhalf := mul_le_mul_of_nonneg_left h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  dsimp only
  rw [mul_neg, ← integral_const_mul, ← integral_const_mul] at hhalf
  convert hhalf using 1
  · congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp [q, V, b]; ring
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp [F, G, b]
      rw [gmp_dot_mulVec_symm (ω.1 x) (hω.1 x).1]
      simp only [dot, mul_comm]


/-- Subtracting the barrier-value term leaves the square of the actual excess. -/
theorem gmpPhysicalResolvent_radialExcess_value_integral_identity {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0)) :
    (∫ x, gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x *
      gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) -
    (∫ x, (M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) *
      gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) =
    ∫ x, (gmpPhysicalH1Value hd ω lam Λ hω v x) ^ 2 ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let u := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f
  let V := gmpPhysicalH1Value hd ω lam Λ hω v
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hu : Integrable (fun x => u x * V x) μ := (Lp.memLp u).integrable_mul (Lp.memLp V)
  have hb : Integrable (fun x => b x * V x) μ :=
    gmpPhysicalResolvent_radialBarrier_mul_excess_integrable hd ω lam Λ hΛ hω α hα f hM hk R v hv
  rw [← integral_sub hu hb]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  change u x * V x - b x * V x = V x ^ 2
  change V x = max (u x - b x) 0 at hx
  by_cases h : 0 ≤ u x - b x
  · rw [max_eq_left h] at hx
    rw [hx]
    ring
  · rw [max_eq_right (le_of_not_ge h)] at hx
    rw [hx]
    ring


/-- The barrier flux is the difference between the resolvent and excess energies. -/
theorem gmpPhysicalResolvent_radialExcess_energy_integral_identity {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (R : ℝ) (v : GMPForceH1 hd lam)
    (hg : (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
        Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
        (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
          (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
          WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
            (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x))) :
    gmpPhysicalH1Energy hd ω lam Λ hω (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) v -
      gmpPhysicalH1Energy hd ω lam Λ hω v v =
    ∫ x, (1 / 2 : ℝ) * dot (PDE.classicalGradient (fun y : Vec d => M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)
      ((ω.1 x).mulVec (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
      ∂physicalReversibleMeasure ω hd lam := by
  let u := gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  unfold gmpPhysicalH1Energy
  rw [← integral_sub (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω u v)
    (gmpPhysicalH1Energy_integrable hd ω lam Λ hΛ hω v v)]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  change (1 / 2 : ℝ) * dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear
      hd ω lam Λ hω u x)) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))) -
    (1 / 2 : ℝ) * dot (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear
      hd ω lam Λ hω v x)) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x))) =
    (1 / 2 : ℝ) * dot (PDE.classicalGradient b x) ((ω.1 x).mulVec (WithLp.ofLp
      (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
  by_cases h : b x < gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x
  · rw [Set.indicator_of_mem (show x ∈ {x | b x < _} from h)] at hx
    have he : WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω u x) -
        WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x) =
        PDE.classicalGradient b x := by
      ext i
      have hi := congrArg (fun z : EuclideanSpace ℝ (Fin d) => z i) hx
      simp only [PiLp.sub_apply] at hi
      change _ - _ = PDE.classicalGradient b x i
      change _ = _ - PDE.classicalGradient b x i at hi
      linarith
    rw [← he]
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  · rw [Set.indicator_of_notMem (show x ∉ {x | b x < _} from h)] at hx
    rw [hx]
    simp [dot, Matrix.mulVec]


/-- A physical excess satisfying the barrier inequality and zero forcing vanishes. -/
theorem gmpPhysicalResolvent_radialExcess_eq_zero {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {M k : ℝ} (hM : 0 ≤ M) (hk : 0 ≤ k) (R : ℝ) (v : GMPForceH1 hd lam)
    (hv : (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      (fun x => max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
        M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0))
    (hg : (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v :
        Vec d → EuclideanSpace ℝ (Fin d)) =ᵐ[physicalReversibleMeasure ω hd lam]
      {x | M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) <
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x}.indicator
        (fun x => gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω
          (gmpPhysicalResolventH1 hd ω lam Λ hΛ hω α hα f) x -
          WithLp.toLp 2 (PDE.classicalGradient (fun y : Vec d => M * Real.exp
            (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)))
    (hforce : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x * gmpPhysicalH1Value hd ω lam Λ hω v x = 0)
    (hsuper : -(∫ x, α * (M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) *
        gmpPhysicalH1Value hd ω lam Λ hω v x ∂physicalReversibleMeasure ω hd lam) ≤
      ∫ x, (1 / 2 : ℝ) * dot (PDE.classicalGradient (fun y : Vec d => M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq y) - Real.sqrt (1 + R ^ 2)))) x)
        ((ω.1 x).mulVec (WithLp.ofLp (gmpPhysicalH1GradientContinuousLinear hd ω lam Λ hω v x)))
        ∂physicalReversibleMeasure ω hd lam) :
    (gmpPhysicalH1Value hd ω lam Λ hω v : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] 0 := by
  let μ := physicalReversibleMeasure ω hd lam
  let V := gmpPhysicalH1Value hd ω lam Λ hω v
  have hsq : Integrable (fun x => V x ^ 2) μ := by
    have h := (Lp.memLp V).integrable_mul (Lp.memLp V)
    apply h.congr
    exact Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply, pow_two]
  have hpos : 0 ≤ ∫ x, V x ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg _)
  have henergy := gmpPhysicalH1Energy_nonneg hd ω lam Λ hΛ hω v
  have hval := gmpPhysicalResolvent_radialExcess_value_integral_identity
    hd ω lam Λ hΛ hω α hα f hM hk R v hv
  have hflux := gmpPhysicalResolvent_radialExcess_energy_integral_identity
    hd ω lam Λ hΛ hω α hα f R v hg
  have hweak := gmpPhysicalResolvent_weakEquation hd ω lam Λ hΛ hω α hα f v
  have hforce' : (∫ x, f x * V x ∂μ) = 0 := integral_eq_zero_of_ae hforce
  rw [hforce'] at hweak
  have hsuper' := hsuper
  have heq : (∫ x, α * (M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) * V x ∂μ) =
      α * ∫ x, (M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) * V x ∂μ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  rw [heq, ← hflux] at hsuper'
  have hzero : (∫ x, V x ^ 2 ∂μ) = 0 := by nlinarith
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (V x)) hsq).mp hzero
  filter_upwards [hae] with x hx
  change V x = 0
  change V x ^ 2 = 0 at hx
  nlinarith [sq_nonneg (V x)]


/-- Compact forcing and a bounded representative give the radial barrier comparison almost everywhere. -/
theorem gmpPhysicalResolvent_radialBarrier_ae_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      {M : ℝ}, 0 ≤ M → ∀ R : ℝ, 0 ≤ R →
      ∀ u : Vec d → ℝ, (∀ x, u x ≤ M) →
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f →
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, R ≤ euclideanNorm x → f x = 0) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x ≤
          M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
  obtain ⟨k, hk, hs⟩ := gmpPhysicalResolvent_radialExcess_supersolution hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f M hM R hR u hu huval hf
  obtain ⟨v, hv, hg, hsuper⟩ := hs f hM R
  have hforce0 := gmpPhysical_radialBarrier_forcing_mul_positiveExcess_eq_zero
    (physicalReversibleMeasure ω hd lam) hM hk.le hR hu hf
  have hforce : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x * gmpPhysicalH1Value hd ω lam Λ hω v x = 0 := by
    filter_upwards [hforce0, hv, huval] with x hx hvx hux
    rw [hvx, ← hux]
    exact hx
  have hz := gmpPhysicalResolvent_radialExcess_eq_zero hd ω lam Λ hΛ hω α hα f
    hM hk.le R v hv hg hforce hsuper
  filter_upwards [hv, hz] with x hvx hzx
  have h : max (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
      M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0 = 0 := by
    rw [← hvx]
    exact hzx
  have := le_max_left (gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f x -
      M * Real.exp (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) 0
  linarith


/-- The continuous physical resolvent representative obeys the radial comparison everywhere. -/
theorem gmpPhysicalResolvent_radialBarrier_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      {M : ℝ}, 0 ≤ M → ∀ R : ℝ, 0 ≤ R →
      ∀ u : Vec d → ℝ, Continuous u → (∀ x, u x ≤ M) →
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f →
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, R ≤ euclideanNorm x → f x = 0) →
      ∀ x, u x ≤ M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
  obtain ⟨k, hk, ha⟩ := gmpPhysicalResolvent_radialBarrier_ae_le hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f M hM R hR u hcont hu heq hf
  let b : Vec d → ℝ := fun x => M * Real.exp
    (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, u x ≤ b x := by
    filter_upwards [ha f hM R hR u hu heq hf, heq] with x hx hx'
    rw [hx']
    exact hx
  have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hc : IsClosed {x : Vec d | u x ≤ b x} :=
    isClosed_le hcont (gmpPhysical_radialBarrier_contDiff M k R).continuous
  have hfull : {x : Vec d | u x ≤ b x} = Set.univ :=
    (hc.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  intro x
  have hx : x ∈ {x : Vec d | u x ≤ b x} := by rw [hfull]; exact Set.mem_univ x
  exact hx


/-- Compact forcing yields a two-sided radial bound and decay for the physical resolvent. -/
theorem gmpPhysicalResolvent_radialBarrier_abs_le_and_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧ ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
      {M : ℝ}, 0 ≤ M → ∀ R : ℝ, 0 ≤ R →
      ∀ u : Vec d → ℝ, Continuous u → (∀ x, |u x| ≤ M) →
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f →
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, R ≤ euclideanNorm x → f x = 0) →
      (∀ x, |u x| ≤ M * Real.exp
        (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2)))) ∧
      Tendsto u (Filter.cocompact (Vec d)) (𝓝 0) := by
  obtain ⟨k, hk, ha⟩ := gmpPhysicalResolvent_radialBarrier_le hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f M hM R hR u hcont hu heq hf
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have heqneg : (fun x => -u x) =ᵐ[physicalReversibleMeasure ω hd lam] G (-f) := by
    rw [map_neg]
    filter_upwards [heq, Lp.coeFn_neg (G f)] with x hx hn
    change -u x = (-G f) x
    rw [hn, Pi.neg_apply, hx]
  have hfneg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      R ≤ euclideanNorm x → (-f) x = 0 := by
    filter_upwards [hf, Lp.coeFn_neg f] with x hx hn hR'
    rw [hn, Pi.neg_apply, hx hR', neg_zero]
  have hp := ha f hM R hR u hcont (fun x => (le_abs_self _).trans (hu x)) heq hf
  have hn := ha (-f) hM R hR (fun x => -u x) hcont.neg
    (fun x => (neg_le_abs _).trans (hu x)) heqneg hfneg
  have hb : ∀ x, |u x| ≤ M * Real.exp
      (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
    intro x
    exact abs_le.mpr ⟨by linarith [hn x], hp x⟩
  exact ⟨hb, gmpPhysical_tendsto_zero_of_radialBarrier hk (fun x _ => hb x)⟩

/-- Bounded compactly supported forcing has a unique vanishing-at-infinity
continuous representative of the actual physical resolvent. -/
theorem gmpPhysicalResolvent_exists_unique_zeroAtInfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    {C : ℝ} (hC : 0 < C)
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C)
    {R : ℝ} (hR : 0 ≤ R)
    (hcompact : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      R ≤ euclideanNorm x → f x = 0) :
    ∃! u : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (u : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f := by
  obtain ⟨u, hu, heq⟩ :=
    gmpPhysicalResolvent_continuousRepresentative hd ω lam Λ hΛ hω hSmooth α hα f ⟨C, hf⟩
  have hbound : ∀ x, |u x| ≤ C / α :=
    gmpPhysicalResolvent_continuousRepresentative_abs_le hd ω lam Λ hΛ hω α hα f hC hf hu heq
  obtain ⟨k, hk, hbarrier⟩ :=
    gmpPhysicalResolvent_radialBarrier_abs_le_and_tendsto_zero hd ω lam Λ hΛ hω α hα
  have hzero : Tendsto u (Filter.cocompact (Vec d)) (𝓝 0) :=
    (hbarrier f (div_nonneg hC.le hα.le) R hR u hu hbound heq hcompact).2
  let U : ZeroAtInftyContinuousMap (Vec d) ℝ :=
    { toFun := u, continuous_toFun := hu, zero_at_infty' := hzero }
  refine ⟨U, heq, ?_⟩
  intro v hv
  apply DFunLike.coe_injective
  exact gmpPhysical_continuousRepresentative_unique hd ω lam v.continuous U.continuous
    (hv.trans heq.symm)

/-- The continuous representative of the physical resolvent preserves the
pointwise unit interval after scaling by the resolvent parameter. -/
theorem gmpPhysicalResolvent_continuousRepresentative_submarkov
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hf1 : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ 1)
    {u : Vec d → ℝ} (hu : Continuous u)
    (heq : u =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f) :
    ∀ x, 0 ≤ α * u x ∧ α * u x ≤ 1 := by
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ α * u x ∧ α * u x ≤ 1 := by
    filter_upwards [heq, gmpPhysicalResolvent_submarkov hd ω lam Λ hΛ hω α hα hf0 hf1]
      with x hx h
    simpa only [hx] using h
  have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hc : IsClosed {x : Vec d | 0 ≤ α * u x ∧ α * u x ≤ 1} :=
    (isClosed_le continuous_const (continuous_const.mul hu)).inter
      (isClosed_le (continuous_const.mul hu) continuous_const)
  have hfull : {x : Vec d | 0 ≤ α * u x ∧ α * u x ≤ 1} = Set.univ :=
    (hc.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  intro x
  have : x ∈ {x : Vec d | 0 ≤ α * u x ∧ α * u x ≤ 1} := by
    rw [hfull]
    exact Set.mem_univ x
  exact this

/-- Bounded forcing supported inside a ball admits a uniform exterior
exponential bound for its physical resolvent. -/
theorem gmpPhysicalResolvent_exterior_barrier_exists
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
        {C R : ℝ}, 0 < C → 0 < R →
        (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |f x| ≤ C) →
        (∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
          R ≤ euclideanNorm x → f x = 0) →
        ∀ {u : Vec d → ℝ}, Continuous u →
          u =ᵐ[physicalReversibleMeasure ω hd lam]
            gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα f →
          ∀ x : Vec d, R ≤ euclideanNorm x →
            |u x| ≤ (C / α) * Real.exp
              (-k * (Real.sqrt (1 + euclideanSq x) - Real.sqrt (1 + R ^ 2))) := by
  obtain ⟨k, hk, hbarrier⟩ :=
    gmpPhysicalResolvent_radialBarrier_abs_le_and_tendsto_zero hd ω lam Λ hΛ hω α hα
  refine ⟨k, hk, ?_⟩
  intro f C R hC hR hf hcompact u hu heq x hx
  have hbound := gmpPhysicalResolvent_continuousRepresentative_abs_le
    hd ω lam Λ hΛ hω α hα f hC hf hu heq
  exact (hbarrier f (div_nonneg hC.le hα.le) R hR.le u hu hbound heq hcompact).1 x

/-- Continuous representatives of scaled resolvents approximate smooth compact
support tests uniformly, with a constant independent of the resolvent parameter. -/
theorem gmpPhysicalResolvent_compactTest_pointwise_approximation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α)
      (u : Vec d → ℝ), Continuous u →
      u =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) →
      ∀ x, |α * u x - φ x| ≤ C / α := by
  obtain ⟨C, hC, hbound⟩ :=
    gmpPhysicalResolvent_compactTest_approximation hd ω lam Λ hΛ hω hSmooth φ hφ hc
  refine ⟨C, hC, ?_⟩
  intro α hα u hu heq
  have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |α * u x - φ x| ≤ C / α := by
    filter_upwards [heq, hbound α hα] with x hx hb
    simpa only [hx] using hb
  have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
  have hclosed : IsClosed {x : Vec d | |α * u x - φ x| ≤ C / α} :=
    isClosed_le (((continuous_const.mul hu).sub hφ.continuous).abs) continuous_const
  have hfull : {x : Vec d | |α * u x - φ x| ≤ C / α} = Set.univ :=
    (hclosed.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
  intro x
  have : x ∈ {x : Vec d | |α * u x - φ x| ≤ C / α} := by
    rw [hfull]
    exact Set.mem_univ x
  exact this

/-- A smooth compact test has a unique vanishing-at-infinity continuous
representative under the physical resolvent. -/
theorem gmpPhysicalResolvent_compactTest_exists_unique_zeroAtInfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃! u : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (u : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
          (gmpPhysicalH1Value hd ω lam Λ hω
            (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) := by
  obtain ⟨B, hB⟩ := hφ.continuous.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.bddAbove_image
    (EinsteinRelation.Entropy.continuous_euclideanNorm' (d := d)).continuousOn
  let C := max B 0 + 1
  let r := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hf := gmpPhysicalH1Value_compactTest hd ω lam Λ hω φ hφ hc
  have hb : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      |gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) x| ≤ C := by
    filter_upwards [hf] with x hx
    rw [hx]
    calc
      |φ x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hsupport : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      r ≤ euclideanNorm x →
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) x = 0 := by
    filter_upwards [hf] with x hx hxr
    rw [hx]
    by_contra hne
    have hxs : x ∈ Function.support φ := hne
    have ht : x ∈ tsupport φ := subset_closure hxs
    have hbound := hR (Set.mem_image_of_mem _ ht)
    dsimp [r] at hxr
    linarith [le_max_left R 0]
  exact gmpPhysicalResolvent_exists_unique_zeroAtInfty hd ω lam Λ hΛ hω hSmooth
    α hα _ hC hb hr hsupport

/-- The physical resolvent is uniformly Lipschitz on smooth compact tests,
when its outputs are represented by continuous functions. -/
theorem gmpPhysicalResolvent_compactTest_sub_abs_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : ℝ) (hα : 0 < α)
    (φ ψ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcφ : HasCompactSupport φ)
    (hcψ : HasCompactSupport ψ) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x, |φ x - ψ x| ≤ C)
    {u v : Vec d → ℝ} (hu : Continuous u) (hv : Continuous v)
    (heu : u =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
        (gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hcφ)))
    (hev : v =ᵐ[physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
        (gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam ψ hψ hcψ))) :
    ∀ x, |u x - v x| ≤ C / α := by
  let f := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hcφ)
  let g := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam ψ hψ hcψ)
  have hfg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |(f - g) x| ≤ C := by
    filter_upwards [Lp.coeFn_sub f g,
      gmpPhysicalH1Value_compactTest hd ω lam Λ hω φ hφ hcφ,
      gmpPhysicalH1Value_compactTest hd ω lam Λ hω ψ hψ hcψ] with x hsub hf hg
    change |(f - g) x| ≤ C
    rw [hsub, Pi.sub_apply, hf, hg]
    exact hbound x
  exact gmpPhysicalResolvent_continuousRepresentative_sub_abs_le hd ω lam Λ hΛ hω
    α hα f g hC hfg hu hv heu hev

/-- Compactly supported continuous forcing belongs to the actual physical L² space. -/
theorem gmpPhysical_compactContinuous_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : Vec d → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f) : MemLp f 2 (physicalReversibleMeasure ω hd lam) := by
  letI : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hc
  exact hc.memLp_of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)

/-- Compactly supported continuous forcing has a unique C₀ physical resolvent
representative, for any physical L² representative of the forcing. -/
theorem gmpPhysicalResolvent_compactContinuous_exists_unique_zeroAtInfty
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α) (f : Vec d → ℝ) (hf : Continuous f)
    (hc : HasCompactSupport f)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ∃! u : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (u : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hc
  obtain ⟨R, hR⟩ := hc.bddAbove_image
    (EinsteinRelation.Entropy.continuous_euclideanNorm' (d := d)).continuousOn
  let C := max B 0 + 1
  let r := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hb : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |F x| ≤ C := by
    filter_upwards [hF] with x hx
    rw [hx]
    calc
      |f x| ≤ B := by simpa only [Real.norm_eq_abs] using hB x
      _ ≤ C := by dsimp [C]; linarith [le_max_left B 0]
  have hsupport : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      r ≤ euclideanNorm x → F x = 0 := by
    filter_upwards [hF] with x hx hxr
    rw [hx]
    by_contra hne
    have hxs : x ∈ Function.support f := hne
    have ht : x ∈ tsupport f := subset_closure hxs
    have hbound := hR (Set.mem_image_of_mem _ ht)
    dsimp [r] at hxr
    linarith [le_max_left R 0]
  exact gmpPhysicalResolvent_exists_unique_zeroAtInfty hd ω lam Λ hΛ hω hSmooth
    α hα F hC hb hr hsupport

/-- Compactly supported functions form a linear subspace of C₀. -/
def gmpC0CompactSubmodule (d : ℕ) : Submodule ℝ (ZeroAtInftyContinuousMap (Vec d) ℝ) where
  carrier := {f | HasCompactSupport (f : Vec d → ℝ)}
  zero_mem' := by
    change HasCompactSupport (0 : Vec d → ℝ)
    exact HasCompactSupport.zero
  add_mem' := by
    intro f g hf hg
    exact hf.add hg
  smul_mem' := by
    intro a f hf
    exact hf.smul_left

/-- The actual physical L² class of a compactly supported C₀ function. -/
noncomputable def gmpPhysicalC0CompactToLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : gmpC0CompactSubmodule d) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  (gmpPhysical_compactContinuous_memLp hd ω lam f.1 f.1.continuous f.2).toLp f.1

/-- The physical L² class agrees almost everywhere with its continuous input. -/
theorem gmpPhysicalC0CompactToLp_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : gmpC0CompactSubmodule d) :
    (gmpPhysicalC0CompactToLp hd ω lam f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] (f.1 : Vec d → ℝ) :=
  (gmpPhysical_compactContinuous_memLp hd ω lam f.1 f.1.continuous f.2).coeFn_toLp

/-- The physical resolvent on compactly supported continuous inputs. -/
noncomputable def gmpPhysicalC0CompactResolvent {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) : ZeroAtInftyContinuousMap (Vec d) ℝ :=
  Classical.choose (gmpPhysicalResolvent_compactContinuous_exists_unique_zeroAtInfty
    hd ω lam Λ hΛ hω hSmooth α hα f.1 f.1.continuous f.2
    (gmpPhysicalC0CompactToLp hd ω lam f) (gmpPhysicalC0CompactToLp_ae hd ω lam f))

/-- The compact-data C₀ resolvent represents the actual physical L² resolvent. -/
theorem gmpPhysicalC0CompactResolvent_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) :
    (gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα (gmpPhysicalC0CompactToLp hd ω lam f) :=
  (Classical.choose_spec (gmpPhysicalResolvent_compactContinuous_exists_unique_zeroAtInfty
    hd ω lam Λ hΛ hω hSmooth α hα f.1 f.1.continuous f.2
    (gmpPhysicalC0CompactToLp hd ω lam f) (gmpPhysicalC0CompactToLp_ae hd ω lam f))).1


/-- The compact-data resolvent is independent of the chosen L² representative. -/
theorem gmpPhysicalC0CompactResolvent_ae_of_rep {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f.1) :
    (gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  have hclass : gmpPhysicalC0CompactToLp hd ω lam f = F :=
    Lp.ext ((gmpPhysicalC0CompactToLp_ae hd ω lam f).trans hF.symm)
  simpa only [hclass] using
    gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f


/-- The compact-data embedding into physical L² is linear. -/
noncomputable def gmpPhysicalC0CompactToLpLinear {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) :
    gmpC0CompactSubmodule d →ₗ[ℝ] Lp ℝ 2 (physicalReversibleMeasure ω hd lam) where
  toFun := gmpPhysicalC0CompactToLp hd ω lam
  map_add' f g := by
    apply Lp.ext
    filter_upwards [gmpPhysicalC0CompactToLp_ae hd ω lam (f + g),
      gmpPhysicalC0CompactToLp_ae hd ω lam f,
      gmpPhysicalC0CompactToLp_ae hd ω lam g,
      Lp.coeFn_add (gmpPhysicalC0CompactToLp hd ω lam f)
        (gmpPhysicalC0CompactToLp hd ω lam g)] with x hfg hf hg hadd
    change _ = (gmpPhysicalC0CompactToLp hd ω lam f +
      gmpPhysicalC0CompactToLp hd ω lam g) x
    change _ = gmpPhysicalC0CompactToLp hd ω lam f x +
      gmpPhysicalC0CompactToLp hd ω lam g x at hadd
    change _ = f.1 x + g.1 x at hfg
    exact hfg.trans ((congrArg₂ (· + ·) hf hg).symm.trans hadd.symm)
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [gmpPhysicalC0CompactToLp_ae hd ω lam (c • f),
      gmpPhysicalC0CompactToLp_ae hd ω lam f,
      Lp.coeFn_smul c (gmpPhysicalC0CompactToLp hd ω lam f)] with x hcf hf hsmul
    change _ = (c • gmpPhysicalC0CompactToLp hd ω lam f) x
    change _ = c * gmpPhysicalC0CompactToLp hd ω lam f x at hsmul
    change _ = c * f.1 x at hcf
    exact hcf.trans ((congrArg (c * ·) hf).symm.trans hsmul.symm)


/-- The compact-data physical C₀ resolvent is linear. -/
noncomputable def gmpPhysicalC0CompactResolventLinear {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α) :
    gmpC0CompactSubmodule d →ₗ[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ where
  toFun := gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα
  map_add' f g := by
    let U := gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα
    let R := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
    let F := gmpPhysicalC0CompactToLpLinear hd ω lam
    have hae : (U (f + g) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        (U f + U g : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      have hsum := gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα (f + g)
      change (U (f + g) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] R (F (f + g)) at hsum
      rw [map_add, map_add] at hsum
      filter_upwards [hsum,
        gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f,
        gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα g,
        Lp.coeFn_add (R (F f)) (R (F g))] with x hs hf hg hadd
      change U (f + g) x = (R (F f) + R (F g)) x at hs
      change U f x = R (F f) x at hf
      change U g x = R (F g) x at hg
      change (R (F f) + R (F g)) x = R (F f) x + R (F g) x at hadd
      change U (f + g) x = U f x + U g x
      rw [hs, hadd, hf, hg]
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U (f + g)).continuous (U f + U g).continuous hae) x
  map_smul' c f := by
    let U := gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα
    let R := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
    let F := gmpPhysicalC0CompactToLpLinear hd ω lam
    have hae : (U (c • f) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
        (c • U f : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      have hsmul := gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα (c • f)
      change (U (c • f) : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] R (F (c • f)) at hsmul
      rw [map_smul, map_smul] at hsmul
      filter_upwards [hsmul,
        gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f,
        Lp.coeFn_smul c (R (F f))] with x hs hf hcoeff
      change U (c • f) x = (c • R (F f)) x at hs
      change U f x = R (F f) x at hf
      change (c • R (F f)) x = c * R (F f) x at hcoeff
      change U (c • f) x = c * U f x
      rw [hs, hcoeff, hf]
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U (c • f)).continuous (c • U f).continuous hae) x


/-- The compact-data physical resolvent obeys the supremum norm bound. -/
theorem gmpPhysicalC0CompactResolvent_norm_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : gmpC0CompactSubmodule d) :
    ‖gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα f‖ ≤
      α⁻¹ * ‖f.1‖ := by
  let U := gmpPhysicalC0CompactResolvent hd ω lam Λ hΛ hω hSmooth α hα f
  have hbound : ∀ x, |U x| ≤ α⁻¹ * ‖f.1‖ := by
    intro x
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hC : 0 < ‖f.1‖ + ε * α := by positivity
    have hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        |gmpPhysicalC0CompactToLp hd ω lam f x| ≤ ‖f.1‖ + ε * α := by
      filter_upwards [gmpPhysicalC0CompactToLp_ae hd ω lam f] with y hy
      rw [hy]
      have hb := BoundedContinuousFunction.norm_coe_le_norm f.1.toBCF y
      change ‖f.1 y‖ ≤ ‖f.1‖ at hb
      rw [Real.norm_eq_abs] at hb
      linarith [mul_pos hε hα]
    have h := gmpPhysicalResolvent_continuousRepresentative_abs_le hd ω lam Λ hΛ hω
      α hα (gmpPhysicalC0CompactToLp hd ω lam f) hC hf U.continuous
      (gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f) x
    have hαne : α ≠ 0 := ne_of_gt hα
    convert h using 1 <;> field_simp <;> ring
  change ‖U.toBCF‖ ≤ α⁻¹ * ‖f.1‖
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (inv_nonneg.mpr (le_of_lt hα))
    (norm_nonneg _))).2
  intro x
  change ‖U x‖ ≤ α⁻¹ * ‖f.1‖
  simpa only [Real.norm_eq_abs] using hbound x



/-- The inherited seminormed group on zero-at-infinity maps. -/
local instance instSeminormedAddCommGroupC0 (d : ℕ) : SeminormedAddCommGroup (ZeroAtInftyContinuousMap (Vec d) ℝ) := inferInstance
/-- The inherited seminormed group on the compact-support submodule. -/
local instance instSeminormedAddCommGroupCompactC0 (d : ℕ) : SeminormedAddCommGroup (gmpC0CompactSubmodule d) := inferInstance
/-- The physical resolvent is bounded on the compact-support C₀ subspace. -/
noncomputable def gmpPhysicalC0CompactResolventCLM {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α) :
    gmpC0CompactSubmodule d →L[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ :=
  (gmpPhysicalC0CompactResolventLinear hd ω lam Λ hΛ hω hSmooth α hα).mkContinuous
    α⁻¹ (fun f => gmpPhysicalC0CompactResolvent_norm_le hd ω lam Λ hΛ hω hSmooth α hα f)

/-- The compact-data resolvent has operator norm at most the inverse parameter. -/
theorem gmpPhysicalC0CompactResolventCLM_norm_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α) :
    ‖gmpPhysicalC0CompactResolventCLM hd ω lam Λ hΛ hω hSmooth α hα‖ ≤ α⁻¹ := by
  exact LinearMap.mkContinuous_norm_le _ (inv_nonneg.mpr (le_of_lt hα)) _


/-- A compactly supported cutoff approximates a C₀ function uniformly. -/
theorem gmpC0_exists_compact_cutoff {d : ℕ}
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
      HasCompactSupport (g : Vec d → ℝ) ∧
      ∀ x, |(f * g) x - f x| ≤ ε := by
  obtain ⟨K, hK, hout⟩ := Filter.mem_cocompact.mp
    ((Metric.tendsto_nhds.mp f.zero_at_infty' ε hε))
  obtain ⟨cut, hcutK, _, hc, hcut⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty K)
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨cut, hc.is_zero_at_infty⟩
  refine ⟨g, hc, ?_⟩
  intro x
  by_cases hx : x ∈ K
  · have hg : g x = 1 := hcutK hx
    change |f x * g x - f x| ≤ ε
    rw [hg, mul_one, sub_self, abs_zero]
    exact le_of_lt hε
  · have hf : |f x| < ε := by
      have h := hout hx
      change dist (f x) 0 < ε at h
      simpa only [dist_zero_right, Real.norm_eq_abs] using h
    have hg0 : 0 ≤ g x := (hcut x).1
    have hg1 : g x ≤ 1 := (hcut x).2
    have hg : |g x - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    change |f x * g x - f x| ≤ ε
    calc
      |f x * g x - f x| = |f x| * |g x - 1| := by
        rw [← abs_mul]
        congr 1
        ring
      _ ≤ |f x| := by nlinarith [mul_le_mul_of_nonneg_left hg (abs_nonneg (f x))]
      _ ≤ ε := le_of_lt hf


/-- Compactly supported C₀ functions are dense in the uniform norm. -/
theorem gmpC0CompactSubmodule_dense (d : ℕ) :
    Dense (gmpC0CompactSubmodule d : Set (ZeroAtInftyContinuousMap (Vec d) ℝ)) := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨g, hgc, hg⟩ := gmpC0_exists_compact_cutoff f (half_pos hε)
  refine ⟨f * g, ?_, ?_⟩
  · have hb : ‖f * g - f‖ ≤ ε / 2 := by
      change ‖(f * g - f).toBCF‖ ≤ ε / 2
      apply (BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).2
      intro x
      change ‖(f * g) x - f x‖ ≤ ε / 2
      simpa only [Real.norm_eq_abs] using hg x
    change dist (f * g) f < ε
    rw [dist_eq_norm]
    linarith
  · change HasCompactSupport ((f * g : ZeroAtInftyContinuousMap (Vec d) ℝ) : Vec d → ℝ)
    exact HasCompactSupport.mul_left hgc


/-- The actual physical resolvent extends uniquely to a bounded C₀ operator. -/
theorem gmpPhysicalC0Resolvent_existsUnique
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (α : ℝ) (hα : 0 < α) :
    ∃! U : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ]
        ZeroAtInftyContinuousMap (Vec d) ℝ,
      ‖U‖ ≤ α⁻¹ ∧
      ∀ (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
        HasCompactSupport (f : Vec d → ℝ) →
        ∀ (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
          (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (f : Vec d → ℝ) →
          (U f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
            gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  let e := (gmpC0CompactSubmodule d).subtype
  let T := gmpPhysicalC0CompactResolventLinear hd ω lam Λ hΛ hω hSmooth α hα
  have hden : DenseRange e := by
    exact denseRange_subtype_val.mpr (gmpC0CompactSubmodule_dense d)
  have hb : ∀ f, ‖T f‖ ≤ α⁻¹ * ‖e f‖ := by
    intro f
    exact gmpPhysicalC0CompactResolvent_norm_le hd ω lam Λ hΛ hω hSmooth α hα f
  let U := T.extendOfNorm e
  have hU : ∀ f, U (e f) = T f :=
    T.extendOfNorm_eq hden ⟨α⁻¹, hb⟩
  refine ⟨U, ⟨?_, ?_⟩, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hden (inv_nonneg.mpr (le_of_lt hα)) hb
  · intro f hf F hF
    have heq := gmpPhysicalC0CompactResolvent_ae_of_rep hd ω lam Λ hΛ hω
      hSmooth α hα ⟨f, hf⟩ F hF
    change (T ⟨f, hf⟩ : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] _ at heq
    rw [← hU ⟨f, hf⟩] at heq
    exact heq
  · intro V hV
    symm
    apply LinearMap.extendOfNorm_unique hden α⁻¹ hb V
    ext f x
    have hVf := hV.2 f.1 f.2 (gmpPhysicalC0CompactToLp hd ω lam f)
      (gmpPhysicalC0CompactToLp_ae hd ω lam f)
    have hTf := gmpPhysicalC0CompactResolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f
    have heq : (V f.1 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] T f :=
      hVf.trans hTf.symm
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (V f.1).continuous (T f).continuous heq) x


/-- The unique C₀ extension of the actual physical resolvent. -/
noncomputable def gmpPhysicalC0Resolvent {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α) :
    ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ :=
  Classical.choose (gmpPhysicalC0Resolvent_existsUnique hd ω lam Λ hΛ hω hSmooth α hα)

/-- The C₀ physical resolvent has the inverse-parameter operator bound. -/
theorem gmpPhysicalC0Resolvent_norm_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α) :
    ‖gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα‖ ≤ α⁻¹ :=
  (Classical.choose_spec (gmpPhysicalC0Resolvent_existsUnique
    hd ω lam Λ hΛ hω hSmooth α hα)).1.1

/-- The C₀ physical resolvent agrees with the physical L² resolvent on compact data. -/
theorem gmpPhysicalC0Resolvent_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : HasCompactSupport (f : Vec d → ℝ))
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (f : Vec d → ℝ)) :
    (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F :=
  (Classical.choose_spec (gmpPhysicalC0Resolvent_existsUnique
    hd ω lam Λ hΛ hω hSmooth α hα)).1.2 f hf F hF

/-- Any bounded C₀ operator with the same compact-data property is the physical resolvent. -/
theorem gmpPhysicalC0Resolvent_eq_of_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (U : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hU : ‖U‖ ≤ α⁻¹ ∧ ∀ (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
      HasCompactSupport (f : Vec d → ℝ) →
      ∀ (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)),
        (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (f : Vec d → ℝ) →
        (U f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
          gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F) :
    U = gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα :=
  (Classical.choose_spec (gmpPhysicalC0Resolvent_existsUnique
    hd ω lam Λ hΛ hω hSmooth α hα)).2 U hU

/-- Scaled physical resolvents approximate smooth compactly supported C₀ inputs. -/
theorem gmpPhysicalC0Resolvent_compactTest_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ))
    (hc : HasCompactSupport (f : Vec d → ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (hα : 0 < α),
      ‖α • gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f - f‖ ≤ C / α := by
  obtain ⟨C, hC, hbound⟩ := gmpPhysicalResolvent_compactTest_pointwise_approximation
    hd ω lam Λ hΛ hω hSmooth (f : Vec d → ℝ) hf hc
  refine ⟨C, hC, ?_⟩
  intro α hα
  let u := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f
  have hu := gmpPhysicalC0Resolvent_ae hd ω lam Λ hΛ hω hSmooth α hα f hc
    (gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam (f : Vec d → ℝ) hf hc))
    (gmpPhysicalH1Value_compactTest hd ω lam Λ hω (f : Vec d → ℝ) hf hc)
  have hp := hbound α hα u u.continuous hu
  change ‖(α • u - f).toBCF‖ ≤ C / α
  apply (BoundedContinuousFunction.norm_le (div_nonneg hC.le hα.le)).2
  intro x
  change ‖α * u x - f x‖ ≤ C / α
  simpa only [Real.norm_eq_abs] using hp x

/-- Compactly supported C₀ functions admit smooth compact approximations. -/
theorem gmpC0_compact_smooth_approx {d : ℕ}
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : HasCompactSupport (f : Vec d → ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
      ContDiff ℝ (⊤ : ℕ∞) (g : Vec d → ℝ) ∧
      HasCompactSupport (g : Vec d → ℝ) ∧ dist g f < ε := by
  rcases Metric.uniformContinuous_iff.mp (ZeroAtInftyContinuousMap.uniformContinuous (F := ZeroAtInftyContinuousMap (Vec d) ℝ) f) (ε / 2) (half_pos hε) with
    ⟨δ, hδ, hδf⟩
  let φ : ContDiffBump (0 : Vec d) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  let v : Vec d → ℝ := (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (f : Vec d → ℝ))
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := by
    exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      (f.continuous.locallyIntegrable (μ := volume))
  have hvc : HasCompactSupport v := HasCompactSupport.convolution (ContinuousLinearMap.lsmul ℝ ℝ) φ.hasCompactSupport_normed hf
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ :=
    ⟨⟨v, hv.continuous⟩, hvc.is_zero_at_infty⟩
  refine ⟨g, hv, hvc, ?_⟩
  have hb : ‖g - f‖ ≤ ε / 2 := by
    change ‖(g - f).toBCF‖ ≤ ε / 2
    apply (BoundedContinuousFunction.norm_le (le_of_lt (half_pos hε))).2
    intro x
    change ‖v x - f x‖ ≤ ε / 2
    rw [← dist_eq_norm]
    apply φ.dist_normed_convolution_le f.continuous.aestronglyMeasurable
    intro y hy
    apply le_of_lt
    exact hδf (by simpa [φ, Metric.mem_ball, dist_comm] using hy)
  rw [dist_eq_norm]
  linarith

/-- Smooth compactly supported functions are dense in C₀. -/
theorem gmpC0_smoothCompact_dense (d : ℕ) :
    Dense {f : ZeroAtInftyContinuousMap (Vec d) ℝ |
      ContDiff ℝ (⊤ : ℕ∞) (f : Vec d → ℝ) ∧
      HasCompactSupport (f : Vec d → ℝ)} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨h, hh, hhc⟩ := Metric.dense_iff.mp (gmpC0CompactSubmodule_dense d)
    f (ε / 2) (half_pos hε)
  obtain ⟨g, hgs, hgc, hgf⟩ := gmpC0_compact_smooth_approx h hhc (ε / 2) (half_pos hε)
  refine ⟨g, ?_, ⟨hgs, hgc⟩⟩
  change dist h f < ε / 2 at hh
  calc
    dist g f ≤ dist g h + dist h f := dist_triangle g h f
    _ < ε := by linarith

/-- Scaled physical C₀ resolvents approximate every C₀ function uniformly. -/
theorem gmpPhysicalC0Resolvent_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ (α : ℝ) (hα : 0 < α), A < α →
      ‖α • gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f - f‖ < ε := by
  obtain ⟨g, hg, hgs, hgc⟩ := Metric.dense_iff.mp (gmpC0_smoothCompact_dense d)
    f (ε / 4) (by positivity)
  change dist g f < ε / 4 at hg
  have hdist : ‖f - g‖ < ε / 4 := by simpa [dist_eq_norm, norm_sub_rev] using hg
  obtain ⟨C, hC, hbound⟩ := gmpPhysicalC0Resolvent_compactTest_approximation
    hd ω lam Λ hΛ hω hSmooth g hgs hgc
  refine ⟨max 1 (4 * C / ε), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα hlarge
  have hCα : C / α < ε / 4 := by
    have h : 4 * C / ε < α := lt_of_le_of_lt (le_max_right _ _) hlarge
    have h' : 4 * C < α * ε := (div_lt_iff₀ hε).mp h
    apply (div_lt_iff₀ hα).2
    nlinarith
  let U := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
  have hU : ‖α • U (f - g)‖ ≤ ‖f - g‖ := by
    calc
      ‖α • U (f - g)‖ = α * ‖U (f - g)‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      _ ≤ α * (α⁻¹ * ‖f - g‖) := by
        gcongr
        exact (U.le_opNorm (f - g)).trans (mul_le_mul_of_nonneg_right
          (gmpPhysicalC0Resolvent_norm_le hd ω lam Λ hΛ hω hSmooth α hα) (norm_nonneg _))
      _ = ‖f - g‖ := by rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hα), one_mul]
  have heq : α • U f - f = α • U (f - g) + (α • U g - g) + (g - f) := by
    rw [map_sub, smul_sub]
    abel
  rw [heq]
  have ht := norm_add_le (α • U (f - g) + (α • U g - g)) (g - f)
  have ht' := norm_add_le (α • U (f - g)) (α • U g - g)
  have hb := hbound α hα
  rw [norm_sub_rev] at ht
  linarith

/-- The union of the physical C₀ resolvent ranges is dense. -/
theorem gmpPhysicalC0Resolvent_ranges_dense {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    Dense {u : ZeroAtInftyContinuousMap (Vec d) ℝ |
      ∃ (α : ℝ) (hα : 0 < α) (f : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u = gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f} := by
  apply Metric.dense_iff.mpr
  intro f ε hε
  obtain ⟨A, hA, happrox⟩ := gmpPhysicalC0Resolvent_approximation
    hd ω lam Λ hΛ hω hSmooth f ε hε
  let α := A + 1
  have hα : 0 < α := by dsimp [α]; linarith
  have hAα : A < α := by dsimp [α]; linarith
  refine ⟨α • gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f, ?_, ?_⟩
  · change dist (α • gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f) f < ε
    simpa [dist_eq_norm] using happrox α hα hAα
  · refine ⟨α, hα, α • f, ?_⟩
    exact (map_smul _ _ _).symm

/-- The physical C₀ resolvent approximates the identity along positive parameters. -/
theorem gmpPhysicalC0Resolvent_approx_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    Filter.Tendsto
      (fun α : {a : ℝ // 0 < a} => (α : ℝ) •
        gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property f)
      Filter.atTop (𝓝 f) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨A, hA, hbound⟩ := gmpPhysicalC0Resolvent_approximation
    hd ω lam Λ hΛ hω hSmooth f ε hε
  let B : {a : ℝ // 0 < a} := ⟨A + 1, by linarith⟩
  filter_upwards [eventually_ge_atTop B] with α hα
  have hlarge : A < (α : ℝ) := by
    have h : (B : ℝ) ≤ α := hα
    dsimp [B] at h
    linarith
  simpa only [dist_eq_norm] using hbound α α.property hlarge

/-- Simultaneous C₀ and L² approximation transfers physical resolvent agreement. -/
theorem gmpPhysicalC0Resolvent_ae_of_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ)
    (Fn : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hcompact : ∀ n, HasCompactSupport (fn n : Vec d → ℝ))
    (hae : ∀ n, (Fn n : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] fn n)
    (hf : Tendsto fn atTop (𝓝 f)) (hF : Tendsto Fn atTop (𝓝 F)) :
    (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  let U := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  have hG : Tendsto (fun n => G (Fn n)) atTop (𝓝 (G F)) := G.continuous.tendsto F |>.comp hF
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hG).exists_seq_tendsto_ae
  have hU : Tendsto (fun n => U (fn n)) atTop (𝓝 (U f)) := U.continuous.tendsto f |>.comp hf
  have hpoint (x : Vec d) : Tendsto (fun n => (U (fn (ns n))) x) atTop (𝓝 ((U f) x)) := by
    have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
    exact (heval.tendsto (U f)).comp (hU.comp hns.tendsto_atTop)
  have heq : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∀ n, (U (fn (ns n))) x = (G (Fn (ns n))) x := by
    apply ae_all_iff.mpr
    intro n
    exact gmpPhysicalC0Resolvent_ae hd ω lam Λ hΛ hω hSmooth α hα
      (fn (ns n)) (hcompact (ns n)) (Fn (ns n)) (hae (ns n))
  filter_upwards [hlim, heq] with x hx he
  apply tendsto_nhds_unique (hpoint x)
  simpa only [he] using hx

/-- A compact cutoff can fix a prescribed compact set and uniformly approximate C₀ data. -/
theorem gmpC0_exists_bounded_compact_cutoff {d : ℕ}
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (K : Set (Vec d)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
      HasCompactSupport (g : Vec d → ℝ) ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      (∀ x ∈ K, g x = 1) ∧ ∀ x, |(f * g) x - f x| ≤ ε := by
  obtain ⟨L, hL, hout⟩ := Filter.mem_cocompact.mp
    ((Metric.tendsto_nhds.mp f.zero_at_infty' ε hε))
  obtain ⟨cut, hcut, _, hc, hrange⟩ :=
    exists_continuous_one_zero_of_isCompact (hK.union hL) isClosed_empty (Set.disjoint_empty _)
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨cut, hc.is_zero_at_infty⟩
  refine ⟨g, hc, hrange, ?_, ?_⟩
  · intro x hx
    exact hcut (Set.mem_union_left _ hx)
  · intro x
    by_cases hx : x ∈ L
    · have hg : g x = 1 := hcut (Set.mem_union_right _ hx)
      change |f x * g x - f x| ≤ ε
      rw [hg, mul_one, sub_self, abs_zero]
      exact le_of_lt hε
    · have hf : |f x| < ε := by
        have h := hout hx
        change dist (f x) 0 < ε at h
        simpa only [dist_zero_right, Real.norm_eq_abs] using h
      have hb : 0 ≤ g x ∧ g x ≤ 1 := hrange x
      have hg : |g x - 1| ≤ 1 := abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩
      change |f x * g x - f x| ≤ ε
      calc
        |f x * g x - f x| = |f x| * |g x - 1| := by rw [← abs_mul]; congr 1; ring
        _ ≤ |f x| := by nlinarith [mul_le_mul_of_nonneg_left hg (abs_nonneg (f x))]
        _ ≤ ε := le_of_lt hf

/-- Pointwise dominated convergence in the extended L² seminorm. -/
theorem gmp_tendsto_eLpNorm_of_dominated {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : ℕ → α → ℝ) (g : α → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : MemLp g 2 μ)
    (hbound : ∀ n x, ‖f n x‖ ≤ ‖g x‖)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => eLpNorm (f n - g) 2 μ) atTop (𝓝 0) := by
  have hui : UnifIntegrable f 2 μ := by
    apply (unifIntegrable_const (ι := ℕ) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg).ae_mono hf
    intro n
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [enorm_le_iff_norm_le] using hbound n x)
  have hut : UnifTight f 2 μ := by
    intro ε hε
    obtain ⟨s, hs, hμs, hgs⟩ :=
      (unifTight_const (ι := ℕ) (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg).exists_measurableSet_indicator hε.ne'
    refine ⟨s, hμs.ne, fun n => ?_⟩
    apply (eLpNorm_mono ((hf n).indicator hs.compl) ?_).trans (hgs n)
    intro x
    by_cases hx : x ∈ sᶜ
    · simpa [Set.indicator_of_mem hx] using hbound n x
    · simp [Set.indicator_of_notMem hx]
  exact tendsto_Lp_of_tendsto_ae (by norm_num) (by norm_num) hf hg hui hut hlim

/-- Compact C₀ functions approximate an L² C₀ function in both norms. -/
theorem gmpPhysicalC0_compact_approximation {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hf : MemLp (f : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam)) :
    ∃ fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ,
      ∃ hfn : ∀ n, MemLp (fn n : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam),
        (∀ n, HasCompactSupport (fn n : Vec d → ℝ)) ∧
        Tendsto fn atTop (𝓝 f) ∧
        Tendsto (fun n => (hfn n).toLp (fn n : Vec d → ℝ)) atTop
          (𝓝 (hf.toLp (f : Vec d → ℝ))) := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hc (n : ℕ) : HasCompactSupport (fn n : Vec d → ℝ) :=
    HasCompactSupport.mul_left (hgc n)
  have hfn (n : ℕ) : MemLp (fn n : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam) :=
    gmpPhysical_compactContinuous_memLp hd ω lam (fn n) (fn n).continuous (hc n)
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro x
    change ‖(f * g n) x - f x‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n x
  have hconv : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  have hpoint (x : Vec d) : Tendsto (fun n => fn n x) atTop (𝓝 (f x)) := by
    have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
    exact (heval.tendsto f).comp hconv
  have hdom (n : ℕ) (x : Vec d) : ‖fn n x‖ ≤ ‖f x‖ := by
    change ‖f x * g n x‖ ≤ ‖f x‖
    rw [norm_mul, Real.norm_eq_abs]
    have h : |g n x| ≤ 1 := abs_le.mpr ⟨by linarith [(hgb n x).1], (hgb n x).2⟩
    simpa only [Real.norm_eq_abs, mul_one] using
      mul_le_mul_of_nonneg_left h (abs_nonneg (f x))
  refine ⟨fn, hfn, hc, hconv, ?_⟩
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => (fn n : Vec d → ℝ)) hfn
    (f : Vec d → ℝ) hf).mpr
  exact gmp_tendsto_eLpNorm_of_dominated _ _ _
    (fun n => (hfn n).aestronglyMeasurable) hf hdom (Filter.Eventually.of_forall hpoint)

/-- The actual C₀ and physical L² resolvents agree on every common input. -/
theorem gmpPhysicalC0Resolvent_ae_of_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα F := by
  have hf : MemLp (f : Vec d → ℝ) 2 (physicalReversibleMeasure ω hd lam) := (Lp.memLp F).ae_eq hae
  have hF : hf.toLp (f : Vec d → ℝ) = F := by
    rw [MemLp.toLp_congr hf (Lp.memLp F) hae.symm, Lp.toLp_coeFn]
  obtain ⟨fn, hfn, hc, hconv, hL2⟩ := gmpPhysicalC0_compact_approximation hd ω lam f hf
  apply gmpPhysicalC0Resolvent_ae_of_approximation hd ω lam Λ hΛ hω hSmooth α hα
    f F fn (fun n => (hfn n).toLp (fn n : Vec d → ℝ)) hc
    (fun n => (hfn n).coeFn_toLp) hconv
  simpa only [hF] using hL2

/-- The actual C₀ resolvents satisfy the two-parameter resolvent identity. -/
theorem gmpPhysicalC0Resolvent_identity {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f -
        gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β hβ f =
      (β - α) • gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
        (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β hβ f) := by
  let U := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
  let V := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β hβ
  let G := gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα
  let H := gmpPhysicalResolvent hd ω lam Λ hΛ hω β hβ
  have hcompact : ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      HasCompactSupport (f : Vec d → ℝ) → U f - V f = (β - α) • U (V f) := by
    intro f hf
    have hm := gmpPhysical_compactContinuous_memLp hd ω lam (f : Vec d → ℝ) f.continuous hf
    let F := hm.toLp (f : Vec d → ℝ)
    have hFa : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f := hm.coeFn_toLp
    have hu := gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth α hα f F hFa
    have hv := gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth β hβ f F hFa
    have huv := gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth α hα (V f) (H F) hv.symm
    have hres := gmpPhysicalResolvent_identity hd ω lam Λ hΛ hω α β hα hβ F
    have hae : ((U f - V f : ZeroAtInftyContinuousMap (Vec d) ℝ) : Vec d → ℝ) =ᵐ[
        physicalReversibleMeasure ω hd lam] ((β - α) • U (V f) : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
      filter_upwards [hu, hv, huv, Lp.coeFn_sub (G F) (H F),
        Lp.coeFn_smul (β - α) (G (H F))] with x hux hvx huvx hsub hsmul
      have hx := congrArg (fun v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) => v x) hres
      change (U f) x - (V f) x = (β - α) * (U (V f)) x
      change (G F - H F) x = ((β - α) • G (H F)) x at hx
      rw [hsub, hsmul] at hx
      change (G F) x - (H F) x = (β - α) * (G (H F)) x at hx
      rw [hux, hvx, huvx]
      exact hx
    ext x
    exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
      (U f - V f).continuous ((β - α) • U (V f)).continuous hae) x
  have heq : (fun f => U f - V f) = (fun f => (β - α) • U (V f)) := by
    apply Continuous.ext_on (gmpC0CompactSubmodule_dense d)
      (show Continuous (fun f => U f - V f) from U.continuous.sub V.continuous)
      (show Continuous (fun f => (β - α) • U (V f)) from
        ((U.continuous.comp V.continuous).const_smul (β - α)))
    intro f hf
    exact hcompact f hf
  exact congrFun heq f

/-- Each actual physical C₀ resolvent has dense range. -/
theorem gmpPhysicalC0Resolvent_denseRange {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (β : ℝ) (hβ : 0 < β) :
    DenseRange (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β hβ) := by
  let V := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β hβ
  apply (gmpPhysicalC0Resolvent_ranges_dense hd ω lam Λ hΛ hω hSmooth).mono
  intro u hu
  obtain ⟨α, hα, f, rfl⟩ := hu
  let U := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
  refine ⟨f + (β - α) • U f, ?_⟩
  have hi := gmpPhysicalC0Resolvent_identity hd ω lam Λ hΛ hω hSmooth β α hβ hα f
  change V f - U f = (α - β) • V (U f) at hi
  have hs : (α - β) • V (U f) = -((β - α) • V (U f)) := by
    rw [← neg_smul]
    congr 1
    ring
  rw [hs] at hi
  change V (f + (β - α) • U f) = U f
  rw [map_add, map_smul]
  calc
    V f + (β - α) • V (U f) = (V f - U f) + (β - α) • V (U f) + U f := by abel
    _ = U f := by rw [hi]; abel

end EinsteinFull.Blueprint
