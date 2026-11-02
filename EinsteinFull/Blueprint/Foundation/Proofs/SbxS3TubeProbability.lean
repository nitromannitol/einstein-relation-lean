import EinsteinFull.Work.W1.GMPKilledSemigroupSupport
import EinsteinRelation.TimeChange.EuclideanTransport
import SubdiffusiveProcess.Sobolev.NativeH1
import SubdiffusiveProcess.Compactness.CubeFractionalRellich
import Homogenization.Sobolev.CubeEmbedding.Extension
import SubdiffusiveProcess.Analysis.RadialKernel
import EinsteinFull.External.Source.GMPDirichletSpectralKernel
import SubdiffusiveProcess.Sobolev.KilledGraph
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import EinsteinRelation.Correctors.EllipticOperatorBound
import SubdiffusiveProcess.Sobolev.NativeH10
import Homogenization.Sobolev.W1p.ZeroExtensionGraph
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Homogenization.Sobolev.Foundations.PoincareZeroTrace
import Homogenization.Sobolev.H1.BasicLemmas
import SuperdiffusionCLT.Section7.Analytic.Defs
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import EinsteinRelation.Correctors.EllipticInvertibility
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.Support
import EllipticRegularity.Ch4.GreenDecay.MaxPrinciple
import EllipticRegularity.Ch4.GreenHarnack.OneBall
import EllipticRegularity.Ch4.GreenHarnack.ChainEss
import PDEFoundation.Geometry.EuclideanBall.Interior

/-!
Actual killed-process steps for the tube probability argument at paper lines 370–375.
These lemmas retain the supplied GMP path law. They do not identify its killed
semigroup with the spectral Dirichlet kernel in the admitted GMP lower bound.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint.TubeProbability

open EinsteinRelation EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support

noncomputable section

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- Evaluation of the actual killed kernel on a measurable endpoint set. -/
theorem killedEndpoint_apply_set (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (x : Vec d) (A : Set (Vec d)) (hA : MeasurableSet A) :
    gmpKilledEndpointKernel G U hU t x A =
      G.pathLaw x {Y | (t : ℝ≥0∞) < localityExitTime U Y ∧ Y t ∈ A} := by
  rw [gmpKilledEndpointKernel_apply, Measure.map_apply (measurable_pathPosition t) hA,
    Measure.restrict_apply (hA.preimage (measurable_pathPosition t))]
  congr 1
  ext Y
  exact and_comm

/-- Domain monotonicity is proved for the actual exit-killed path measure,
at every starting point and including time zero. -/
theorem killedEndpoint_mono (U V : Set (Vec d)) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ⊆ V) (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x ≤ gmpKilledEndpointKernel G V hV t x := by
  rw [gmpKilledEndpointKernel_apply, gmpKilledEndpointKernel_apply]
  apply Measure.map_mono _ (measurable_pathPosition t)
  apply Measure.restrict_mono_set
  intro Y hY
  apply (lt_localityExitTime_iff V hV Y t).mpr
  intro s hs
  exact hUV ((lt_localityExitTime_iff U hU Y t).mp hY s hs)

/-- Deterministic change of clocks in the strict survival event. The spatial
domain is pulled back literally, so its Euclidean geometry is preserved. -/
theorem rescaled_survival_iff (U : Set (Vec d)) (hU : IsOpen U)
    (hlam : 0 < lam) (h : ℝ) (hh : 0 ≤ h) (Y : Path d) :
    (((h / lam ^ 2).toNNReal : ℝ≥0∞) <
        localityExitTime ((fun x : Vec d => lam • x) ⁻¹' U) Y) ↔
      ∀ u : ℝ≥0, (u : ℝ) ≤ h →
        lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U := by
  have hq : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have hopen : IsOpen ((fun x : Vec d => lam • x) ⁻¹' U) :=
    hU.preimage (continuous_id.const_smul lam)
  rw [lt_localityExitTime_iff _ hopen]
  constructor
  · intro hY u hu
    apply hY
    apply NNReal.coe_le_coe.mp
    rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hq.le),
      Real.coe_toNNReal _ (div_nonneg hh hq.le)]
    exact div_le_div_of_nonneg_right hu hq.le
  · intro hY t ht
    let u : ℝ≥0 := ⟨(t : ℝ) * lam ^ 2, mul_nonneg t.coe_nonneg hq.le⟩
    have hu : (u : ℝ) ≤ h := by
      have ht' : (t : ℝ) ≤ h / lam ^ 2 := by
        have ht' := NNReal.coe_le_coe.mpr ht
        rwa [Real.coe_toNNReal _ (div_nonneg hh hq.le)] at ht'
      exact (le_div_iff₀ hq).mp ht'
    have htime : ((u : ℝ) / lam ^ 2).toNNReal = t := by
      change ((t : ℝ) * lam ^ 2 / lam ^ 2).toNNReal = t
      rw [mul_div_cancel_right₀ _ hq.ne', Real.toNNReal_coe]
    change lam • Y t ∈ U
    simpa only [htime] using hY u hu

/-- The rescaled actual killed endpoint measure is exactly the path event
appearing in the tube contract, for every measurable endpoint set. -/
theorem rescaled_killedEndpoint_apply_set (U : Set (Vec d)) (hU : IsOpen U)
    (hlam : 0 < lam) (h : ℝ) (hh : 0 ≤ h) (x : Vec d)
    (A : Set (Vec d)) (hA : MeasurableSet A) :
    ((gmpKilledEndpointKernel G ((fun y : Vec d => lam • y) ⁻¹' U)
        (hU.preimage (continuous_id.const_smul lam)) (h / lam ^ 2).toNNReal x).map
      (fun y => lam • y)) A =
      G.pathLaw x {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
          lam • Y ((u : ℝ) / lam ^ 2).toNNReal ∈ U) ∧
        lam • Y (h / lam ^ 2).toNNReal ∈ A} := by
  have hm : Measurable (fun y : Vec d => lam • y) :=
    (continuous_id.const_smul lam).measurable
  rw [Measure.map_apply hm hA, killedEndpoint_apply_set G _ _ _ _ _ (hA.preimage hm)]
  congr 1
  ext Y
  exact and_congr (rescaled_survival_iff U hU hlam h hh Y) Iff.rfl

/-- The endpoint-centered comparison ball used in the paper is contained in
the current piece's ball. All three radii use the explicit Euclidean norm. -/
theorem endpoint_ball_subset_piece_ball (ε : ℝ) (hε : 0 < ε)
    (c cnext y : Vec d)
    (hstep : euclideanNorm (cnext - c) ≤ ε / 16)
    (hy : euclideanNorm (y - cnext) < ε / 16) :
    {z : Vec d | euclideanNorm (z - y) < ε / 4} ⊆
      {z : Vec d | euclideanNorm (z - c) < ε / 2} := by
  intro z hz
  have htri := TimeChange.euclideanNorm_add_le (y - cnext) (cnext - c)
  have htri' := TimeChange.euclideanNorm_add_le (z - y) (y - c)
  have he : (y - cnext) + (cnext - c) = y - c := sub_add_sub_cancel _ _ _
  have he' : (z - y) + (y - c) = z - c := sub_add_sub_cancel _ _ _
  rw [he] at htri
  rw [he'] at htri'
  change euclideanNorm (z - y) < ε / 4 at hz
  change euclideanNorm (z - c) < ε / 2
  linarith only [htri, htri', hstep, hy, hz, hε]

/-- Every allowed starting point is strictly inside the endpoint-centered
comparison ball. This is the other geometric input to domain monotonicity. -/
theorem start_mem_endpoint_ball (ε : ℝ) (hε : 0 < ε) (c cnext x y : Vec d)
    (hstep : euclideanNorm (cnext - c) ≤ ε / 16)
    (hx : euclideanNorm (x - c) < ε / 16)
    (hy : euclideanNorm (y - cnext) < ε / 16) :
    euclideanNorm (x - y) < 3 * ε / 16 ∧ euclideanNorm (x - y) < ε / 4 := by
  have hneg (v : Vec d) : euclideanNorm (-v) = euclideanNorm v := by
    rw [← neg_one_smul ℝ v, TimeChange.euclideanNorm_smul]
    norm_num
  have hstep' : euclideanNorm (c - cnext) ≤ ε / 16 := by
    simpa only [← neg_sub cnext c, hneg] using hstep
  have hy' : euclideanNorm (cnext - y) < ε / 16 := by
    simpa only [← neg_sub y cnext, hneg] using hy
  have htri := TimeChange.euclideanNorm_add_le (x - c) (c - cnext)
  have htri' := TimeChange.euclideanNorm_add_le (x - cnext) (cnext - y)
  rw [sub_add_sub_cancel] at htri htri'
  constructor <;> linarith only [htri, htri', hstep', hx, hy', hε]

open Filter Set TopologicalSpace SubdiffusiveProcess
open SubdiffusiveProcess.EllipticRegularity

open EinsteinFull.External.Source.GMP

/-- The source and library distributional weak gradients use the same test
identity on the unchanged coordinate carrier. -/
theorem hasWeakGradientOn_of_source {U : Set (Vec d)} {f : Vec d → ℝ}
    {g : Vec d → Vec d} (h : EinsteinRelation.HasWeakGradient U f g) :
    Homogenization.HasWeakGradientOn U f g := by
  intro i φ hφ hφc hφU
  simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
    (h i).2.2 φ ⟨hφ, hφc, hφU⟩

/-- Global source weak-gradient data, including literal zero extensions,
give actual library Sobolev graph data on every open cube. -/
def cubeGraphOfGlobalWeakGradient (Ω : Opens (SpatialCoordinates d))
    (f : Vec d → ℝ) (g : Vec d → Vec d)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (fun x => g x i) 2 volume)
    (hw : EinsteinRelation.HasWeakGradient Set.univ f g) : weakSobolevGraph Ω := by
  let v : SobolevData Ω :=
    ⟨(hf.restrict Ω).toLp f, fun i => ((hg i).restrict Ω).toLp (fun x => g x i)⟩
  refine ⟨v, (mem_weakSobolevGraph_iff_hasWeakGradientOn v).mpr ?_⟩
  have hweak := (hasWeakGradientOn_of_source hw).restrict Ω.isOpen (Set.subset_univ _)
  intro i φ hφ hφc hφΩ
  calc
    _ = ∫ x in (Ω : Set (SpatialCoordinates d)),
        f x * fderiv ℝ φ x (Homogenization.basisVec i) := by
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp (hf.restrict Ω)] with x hx
      exact congrArg (fun a => a * fderiv ℝ φ x (Homogenization.basisVec i)) hx
    _ = -∫ x in (Ω : Set (SpatialCoordinates d)), g x i * φ x :=
      hweak i φ hφ hφc hφΩ
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [MemLp.coeFn_toLp ((hg i).restrict Ω)] with x hx
      exact congrArg (fun a => a * φ x) hx.symm

/-- The cube graph retains the source function and every gradient coordinate
almost everywhere for the actual restricted volume measure. -/
theorem cubeGraphOfGlobalWeakGradient_coe (Ω : Opens (SpatialCoordinates d))
    (f : Vec d → ℝ) (g : Vec d → Vec d)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (fun x => g x i) 2 volume)
    (hw : EinsteinRelation.HasWeakGradient Set.univ f g) :
    (cubeGraphOfGlobalWeakGradient Ω f g hf hg hw).val.1 =ᵐ[volume.restrict Ω] f ∧
      ∀ i, (cubeGraphOfGlobalWeakGradient Ω f g hf hg hw).val.2 i =ᵐ[volume.restrict Ω]
        (fun x => g x i) := by
  dsimp only [cubeGraphOfGlobalWeakGradient]
  constructor
  · exact MemLp.coeFn_toLp (f := f) (p := 2)
      (μ := volume.restrict (Ω : Set (Vec d))) (hf.restrict Ω)
  · intro i
    exact MemLp.coeFn_toLp (f := fun x : Vec d => g x i) (p := 2)
      (μ := volume.restrict (Ω : Set (Vec d))) ((hg i).restrict Ω)

/-- Restricting global weak-gradient data to a cube does not increase the
unweighted `L²` norm of its value or any gradient coordinate. -/
theorem cubeGraphOfGlobalWeakGradient_norm_le (Ω : Opens (SpatialCoordinates d))
    (f : Vec d → ℝ) (g : Vec d → Vec d)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (fun x => g x i) 2 volume)
    (hw : EinsteinRelation.HasWeakGradient Set.univ f g) :
    ‖(cubeGraphOfGlobalWeakGradient Ω f g hf hg hw).val.1‖ ≤ ‖hf.toLp f‖ ∧
      ∀ i, ‖(cubeGraphOfGlobalWeakGradient Ω f g hf hg hw).val.2 i‖ ≤
        ‖(hg i).toLp (fun x => g x i)‖ := by
  have hrestrict (v : Vec d → ℝ) (hv : MemLp v 2 volume) :
      ‖(hv.restrict Ω).toLp v‖ ≤ ‖hv.toLp v‖ := by
    rw [Lp.norm_toLp, Lp.norm_toLp]
    exact ENNReal.toReal_mono hv.eLpNorm_ne_top
      (eLpNorm_mono_measure v Measure.restrict_le_self)
  constructor
  · change ‖(hf.restrict Ω).toLp f‖ ≤ ‖hf.toLp f‖
    exact hrestrict f hf
  · intro i
    change ‖((hg i).restrict Ω).toLp (fun x => g x i)‖ ≤ ‖(hg i).toLp (fun x => g x i)‖
    exact hrestrict (fun x => g x i) (hg i)

/-- The Euclidean Dirichlet ball lies in the coordinate cube with side `2R`.
No replacement of the Euclidean norm is made. -/
theorem sourceBall_subset_cube (R : ℝ) (hR : 0 < R) :
    sourceBall (0 : Vec d) R ⊆
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
        Set (SpatialCoordinates d)) := by
  intro x hx
  have hnorm : ‖x‖ ≤ EinsteinRelation.euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change x i ^ 2 ≤ ∑ j : Fin d, x j * x j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i))
  have hball : EinsteinRelation.euclideanNorm x < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
  change dist x 0 < 2 * R / 2
  rw [dist_zero_right]
  linarith only [hnorm, hball]

/-- An upper density bound on the source ball suffices to transport cube
`L²` convergence to the exact weighted measure of the spectral problem. -/
theorem dirichletVolume_le_cube (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    dirichletVolume ρ R ≤ ENNReal.ofReal C •
      volume.restrict (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR) : Set (SpatialCoordinates d)) := by
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp (continuous_finsetSum _
      (fun i _ => (continuous_apply i).mul (continuous_apply i)))
  calc
    dirichletVolume ρ R ≤
        (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
          (fun _ => ENNReal.ofReal C) := by
      apply withDensity_mono
      filter_upwards [ae_restrict_mem (show MeasurableSet (sourceBall (0 : Vec d) R) from
        (by
          unfold sourceBall
          exact (isOpen_lt (hnorm.comp
            (continuous_id.sub continuous_const)) continuous_const).measurableSet))] with x hx
      exact ENNReal.ofReal_le_ofReal (hρ x hx)
    _ = ENNReal.ofReal C • volume.restrict (sourceBall (0 : Vec d) R) :=
      withDensity_const _
    _ ≤ _ := _root_.smul_le_smul_left (ENNReal.ofReal C)
      (Measure.restrict_mono_set _ (sourceBall_subset_cube R hR))

/-- The canonical change-of-measure map keeps the actual function
representative almost everywhere in the source weighted ball. -/
def cubeToDirichletL2 (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)) →L[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (dirichletVolume_le_cube ρ R hR C hρ)

/-- The transport to the weighted spectral carrier is literal AE identity. -/
theorem cubeToDirichletL2_coe (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))) :
    cubeToDirichletL2 ρ R hR C hρ f =ᵐ[dirichletVolume ρ R] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top _ f

/-- Fractional cube compactness transfers to the exact weighted ball `L²`
space of the source spectral resolution, through the canonical AE identity map. -/
theorem exists_subseq_cubeFractional_dirichletVolume (hd : 2 ≤ d)
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (s : Set.Ioo (0 : ℝ) 1)
    (u : ℕ → DomainL2
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)))
    (B : ℝ)
    (hfinite : ∀ n, cubeFractionalL2Seminorm hd 0 (2 * R) (mul_pos two_pos hR)
      s (fun _ : Fin 1 => u n) < ⊤)
    (hbound : ∀ n, cubeFractionalSqNorm hd 0 (2 * R) (mul_pos two_pos hR) s (u n) ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : Lp ℝ 2 (dirichletVolume ρ R)),
      StrictMono phi ∧ Tendsto
        (fun n => cubeToDirichletL2 ρ R hR C hρ (u (phi n))) atTop (𝓝 w) := by
  obtain ⟨phi, w, hphi, hconv⟩ := exists_subseq_of_cubeFractionalSqNorm_bounded d hd s
    (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) u B hfinite hbound
  exact ⟨phi, cubeToDirichletL2 ρ R hR C hρ w, hphi,
    ((cubeToDirichletL2 ρ R hR C hρ).continuous.tendsto w).comp hconv⟩

/-! The following segment, approximation and Fatou proofs reproduce the small
analytic core of `SubdiffusiveProcess.Analysis.CubeFractionalH1Finite`
(lines 28–317 and 373–437). Importing that entire module also imports the unrelated
elliptic regularity input graph. Keeping this core local avoids that graph and
allows a uniform energy bound, rather than only pointwise finiteness. -/
namespace CubeH1Bound
open Set TopologicalSpace

/-- The scalar Gagliardo integrand (Euclidean distance, exponent `d + 2s`). -/
def gagliardoIntegrand (s : ℝ) (g : SpatialCoordinates d → ℝ) (x y : SpatialCoordinates d) : ℝ≥0∞ :=
  ENNReal.ofReal ((g x - g y) ^ 2) /
    (ENNReal.ofReal (Real.sqrt (∑ j : Fin d, (x j - y j) ^ 2))) ^ ((d : ℝ) + 2 * s)

/-- Squared Euclidean gradient of a differentiable function. -/
def gradientSquare (φ : SpatialCoordinates d → ℝ) (x : SpatialCoordinates d) : ℝ :=
  ∑ i : Fin d, (fderiv ℝ φ x (Pi.single i 1)) ^ 2

/-- Squared Euclidean norm. -/
def euclideanSquare (h : SpatialCoordinates d) : ℝ := ∑ j : Fin d, h j ^ 2

/-- (1a) Along a segment: `(φ y - φ x)^2 ≤ |y-x|^2 ∫_0^1 |∇φ(x+t(y-x))|^2 dt`. -/
theorem sq_sub_le_segment (φ : SpatialCoordinates d → ℝ) (hφ : ContDiff ℝ 1 φ)
    (x y : SpatialCoordinates d) :
    (φ y - φ x) ^ 2 ≤ euclideanSquare (y - x) * ∫ t in (0 : ℝ)..1, gradientSquare φ (x + t • (y - x)) := by
  set v : SpatialCoordinates d := y - x with hv
  set F : ℝ → ℝ := fun t => fderiv ℝ φ (x + t • v) v with hF
  have hdiff : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hγ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • v) v t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => φ (x + t • v)) (F t) t := fun t =>
    (hdiff (x + t • v)).hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hFc : Continuous F := by
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (x + t • v) :=
      (hφ.continuous_fderiv (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))
    exact h1.clm_apply continuous_const
  -- fundamental theorem of calculus along the segment
  have hFTC : φ y - φ x = ∫ t in (0 : ℝ)..1, F t := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hFc.intervalIntegrable 0 1)
    rw [this]; simp [hv]
  -- pointwise Cauchy–Schwarz: F t ^ 2 ≤ euclideanSquare v * gradientSquare φ (x + t • v)
  have hCS : ∀ t : ℝ, F t ^ 2 ≤ euclideanSquare v * gradientSquare φ (x + t • v) := by
    intro t
    have hvsum : v = ∑ i : Fin d, v i • (Pi.single i (1 : ℝ) : SpatialCoordinates d) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    have hlin : F t = ∑ i : Fin d, v i * fderiv ℝ φ (x + t • v) (Pi.single i 1) := by
      simp only [hF]
      set L := fderiv ℝ φ (x + t • v) with hL
      calc L v = L (∑ i : Fin d, v i • (Pi.single i (1 : ℝ) : SpatialCoordinates d)) := by
            rw [← hvsum]
        _ = ∑ i : Fin d, v i * L (Pi.single i 1) := by simp [map_sum, map_smul, smul_eq_mul]
    rw [hlin, euclideanSquare, gradientSquare]
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  -- (∫ F)^2 ≤ ∫ F^2 on [0,1], since 0 ≤ ∫ (F - c)^2 = ∫ F^2 - c^2
  have hF2i : IntervalIntegrable (fun t => F t ^ 2) volume 0 1 := (hFc.pow 2).intervalIntegrable 0 1
  have hJ : (∫ t in (0 : ℝ)..1, F t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, F t ^ 2 := by
    set c := ∫ t in (0 : ℝ)..1, F t with hc
    have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (F t - c) ^ 2 :=
      intervalIntegral.integral_nonneg (by norm_num) fun t _ => sq_nonneg _
    have hexp : ∫ t in (0 : ℝ)..1, (F t - c) ^ 2 = (∫ t in (0 : ℝ)..1, F t ^ 2) - c ^ 2 := by
      have e : ∀ t, (F t - c) ^ 2 = F t ^ 2 - 2 * c * F t + c ^ 2 := fun t => by ring
      simp_rw [e]
      rw [intervalIntegral.integral_add (hF2i.sub ((hFc.intervalIntegrable 0 1).const_mul _))
          intervalIntegrable_const,
        intervalIntegral.integral_sub hF2i ((hFc.intervalIntegrable 0 1).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      simp [hc]; ring
    linarith
  have hG : Continuous fun t : ℝ => gradientSquare φ (x + t • v) := by
    unfold gradientSquare
    have h1 : Continuous fun t : ℝ => fderiv ℝ φ (x + t • v) :=
      (hφ.continuous_fderiv (by norm_num)).comp (continuous_const.add (continuous_id.smul continuous_const))
    exact continuous_finsetSum _ fun i _ => (h1.clm_apply continuous_const).pow 2
  calc (φ y - φ x) ^ 2 = (∫ t in (0 : ℝ)..1, F t) ^ 2 := by rw [hFTC]
    _ ≤ ∫ t in (0 : ℝ)..1, F t ^ 2 := hJ
    _ ≤ ∫ t in (0 : ℝ)..1, euclideanSquare v * gradientSquare φ (x + t • v) :=
        intervalIntegral.integral_mono_on (by norm_num) hF2i
          ((continuous_const.mul hG).intervalIntegrable 0 1) fun t _ => hCS t
    _ = euclideanSquare v * ∫ t in (0 : ℝ)..1, gradientSquare φ (x + t • v) := intervalIntegral.integral_const_mul _ _

/-- (1b) The kernel `|h|^{2-d-2s}` (Euclidean norm) is integrable on every ball. -/
theorem kernel_lintegral_lt_top (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (R : ℝ) :
    ∫⁻ h in Metric.ball (0 : SpatialCoordinates d) R,
      ENNReal.ofReal (euclideanSquare h) / (ENNReal.ofReal (Real.sqrt (euclideanSquare h))) ^ ((d : ℝ) + 2 * s) < ⊤ := by
  classical
  have hq : -(d : ℝ) < 2 - d - 2 * s := by linarith
  have hint := integrableOn_norm_rpow_ball (by omega : 0 < d) (2 - d - 2 * s) R hq
  refine lt_of_le_of_lt ?_ hint.lintegral_lt_top
  refine lintegral_mono fun h => ?_
  by_cases h0 : euclideanSquare h = 0
  · simp [h0]
  · have hpos : 0 < euclideanSquare h := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg (h j)) (Ne.symm h0)
    set e := Real.sqrt (euclideanSquare h) with he
    have hepos : 0 < e := Real.sqrt_pos.mpr hpos
    have hesq : euclideanSquare h = e ^ 2 := (Real.sq_sqrt hpos.le).symm
    -- sup norm ≤ Euclidean norm
    have hnorm : ‖h‖ ≤ e := by
      refine (pi_norm_le_iff_of_nonneg hepos.le).mpr fun j => ?_
      rw [Real.norm_eq_abs, he]
      refine Real.abs_le_sqrt ?_
      exact Finset.single_le_sum (f := fun j => h j ^ 2) (fun j _ => sq_nonneg (h j)) (Finset.mem_univ j)
    have hnpos : 0 < ‖h‖ := by
      rw [norm_pos_iff]; intro hz; apply h0; simp [euclideanSquare, hz]
    rw [ENNReal.ofReal_rpow_of_pos hepos, ← ENNReal.ofReal_div_of_pos (Real.rpow_pos_of_pos hepos _)]
    apply ENNReal.ofReal_le_ofReal
    rw [hesq, ← Real.rpow_natCast, ← Real.rpow_sub hepos]
    have hexp : (↑(2 : ℕ) : ℝ) - ((d : ℝ) + 2 * s) = 2 - d - 2 * s := by push_cast; ring
    rw [hexp]
    have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    exact Real.rpow_le_rpow_of_nonpos hnpos hnorm (by linarith)

/-- Generic Tonelli/substitution bound. -/
theorem segment_integral_le_gen (Q B : Set (SpatialCoordinates d)) (hQm : MeasurableSet Q)
    (hBm : MeasurableSet B) (hconv : Convex ℝ Q) (hQB : ∀ x ∈ Q, ∀ y ∈ Q, y - x ∈ B) (s : ℝ)
    (G : SpatialCoordinates d → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hGm : Measurable G) :
    ∫⁻ x in Q, ∫⁻ y in Q,
        ENNReal.ofReal (euclideanSquare (y - x)) / (ENNReal.ofReal (Real.sqrt (euclideanSquare (y - x)))) ^ ((d : ℝ) + 2 * s) *
          ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      (∫⁻ h in B, ENNReal.ofReal (euclideanSquare h) / (ENNReal.ofReal (Real.sqrt (euclideanSquare h))) ^ ((d : ℝ) + 2 * s)) *
        ∫⁻ x in Q, ENNReal.ofReal (G x) := by
  classical
  set K : SpatialCoordinates d → ℝ≥0∞ := fun h =>
    ENNReal.ofReal (euclideanSquare h) / (ENNReal.ofReal (Real.sqrt (euclideanSquare h))) ^ ((d : ℝ) + 2 * s) with hK
  have hKm : Measurable K := by simp only [hK, euclideanSquare]; fun_prop
  set g : SpatialCoordinates d → ℝ≥0∞ := fun w => ENNReal.ofReal (G w) with hg
  have hgm : Measurable g := ENNReal.measurable_ofReal.comp hGm
  -- (1) the t-integral is at most the lower integral over [0,1]
  have h1 : ∀ x y : SpatialCoordinates d,
      ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
        ∫⁻ t in Icc (0 : ℝ) 1, g (x + t • (y - x)) := by
    intro x y
    rw [intervalIntegral.integral_of_le zero_le_one]
    have hmeas : AEStronglyMeasurable (fun t : ℝ => G (x + t • (y - x))) (volume.restrict (Ioc 0 1)) :=
      (hGm.comp (by fun_prop)).aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun t => hG0 _) hmeas]
    exact ENNReal.ofReal_toReal_le.trans (lintegral_mono_set Ioc_subset_Icc_self)
  -- (2) substitute y = x + h and use convexity
  have h2 : ∀ x ∈ Q, ∫⁻ y in Q, K (y - x) * ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h := by
    intro x hx
    rw [← lintegral_indicator hQm, ← lintegral_add_left_eq_self _ x]
    refine lintegral_mono fun h => ?_
    by_cases hy : x + h ∈ Q
    · have hhB : h ∈ B := by simpa using hQB x hx (x + h) hy
      have hgi : Measurable fun t : ℝ => Q.indicator g (x + t • h) := (hgm.indicator hQm).comp (by fun_prop)
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hhB, add_sub_cancel_left, lintegral_const_mul _ hgi]
      gcongr
      calc ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • h))
          ≤ ∫⁻ t in Icc (0 : ℝ) 1, g (x + t • h) := by simpa using h1 x (x + h)
        _ = ∫⁻ t in Icc (0 : ℝ) 1, Q.indicator g (x + t • h) := by
            refine setLIntegral_congr_fun measurableSet_Icc fun t ht => ?_
            rw [Set.indicator_of_mem (hconv.add_smul_mem hx hy ht)]
    · rw [Set.indicator_of_notMem hy]; exact zero_le
  -- (3) Tonelli and translation invariance
  have hF : Measurable (fun p : (SpatialCoordinates d × SpatialCoordinates d) × ℝ =>
      K p.1.2 * Q.indicator g (p.1.1 + p.2 • p.1.2)) :=
    (hKm.comp (by fun_prop)).mul ((hgm.indicator hQm).comp (by fun_prop))
  have hinner : ∀ t : ℝ, ∀ h : SpatialCoordinates d,
      ∫⁻ x, Q.indicator g (x + t • h) = ∫⁻ x in Q, g x := by
    intro t h
    rw [lintegral_add_right_eq_self (fun x => Q.indicator g x) (t • h), lintegral_indicator hQm]
  calc ∫⁻ x in Q, ∫⁻ y in Q, K (y - x) * ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x)))
      ≤ ∫⁻ x in Q, ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h :=
        setLIntegral_mono' hQm h2
    _ ≤ ∫⁻ x, ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h :=
        setLIntegral_le_lintegral _ _
    _ = ∫⁻ h, ∫⁻ x, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * Q.indicator g (x + t • h)) h := by
        apply lintegral_lintegral_swap
        refine Measurable.aemeasurable ?_
        refine Measurable.indicator ?_ (hBm.preimage measurable_snd)
        exact hF.lintegral_prod_right'
    _ = ∫⁻ h, B.indicator (fun h => ∫⁻ t in Icc (0 : ℝ) 1, K h * ∫⁻ x in Q, g x) h := by
        refine lintegral_congr fun h => ?_
        by_cases hh : h ∈ B
        · simp only [Set.indicator_of_mem hh]
          have hm2 : Measurable (Function.uncurry fun (x : SpatialCoordinates d) (t : ℝ) =>
              K h * Q.indicator g (x + t • h)) :=
            measurable_const.mul ((hgm.indicator hQm).comp
              (by fun_prop : Measurable fun q : SpatialCoordinates d × ℝ => q.1 + q.2 • h))
          rw [lintegral_lintegral_swap hm2.aemeasurable]
          refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
          have hmx : Measurable fun x : SpatialCoordinates d => Q.indicator g (x + t • h) :=
            (hgm.indicator hQm).comp (by fun_prop)
          rw [lintegral_const_mul _ hmx, hinner t h]
        · simp [Set.indicator_of_notMem hh]
    _ = (∫⁻ h in B, K h) * ∫⁻ x in Q, g x := by
        rw [lintegral_indicator hBm]
        simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Icc,
          sub_zero, ENNReal.ofReal_one, mul_one]
        rw [lintegral_mul_const _ hKm]


/-- (1c) Tonelli + substitution `y = x + h` + translation invariance, for a nonnegative `G`
vanishing off the convex cube. -/
theorem segment_integral_le (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (s : ℝ)
    (G : SpatialCoordinates d → ℝ) (hG0 : ∀ x, 0 ≤ G x) (hGm : Measurable G) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal (euclideanSquare (y - x)) / (ENNReal.ofReal (Real.sqrt (euclideanSquare (y - x)))) ^ ((d : ℝ) + 2 * s) *
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) ≤
      (∫⁻ h in Metric.ball (0 : SpatialCoordinates d) (r + 1),
          ENNReal.ofReal (euclideanSquare h) / (ENNReal.ofReal (Real.sqrt (euclideanSquare h))) ^ ((d : ℝ) + 2 * s)) *
        ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (G x) := by
  refine segment_integral_le_gen _ _ (centeredCube z r hr).isOpen.measurableSet
    Metric.isOpen_ball.measurableSet (convex_ball z (r / 2)) ?_ s G hG0 hGm
  intro x hx y hy
  have hx' : dist x z < r / 2 := hx
  have hy' : dist y z < r / 2 := hy
  rw [Metric.mem_ball, dist_zero_right, ← dist_eq_norm]
  calc dist y x ≤ dist y z + dist z x := dist_triangle _ _ _
    _ < r / 2 + r / 2 := by rw [dist_comm z x]; linarith
    _ < r + 1 := by linarith

/-- (1) Smooth case. -/
theorem smooth_gagliardo_bound (hd : 2 ≤ d) (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ φ : SpatialCoordinates d → ℝ, ContDiff ℝ 1 φ →
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), gagliardoIntegrand s φ x y ≤
        C * ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (gradientSquare φ x) := by
  refine ⟨∫⁻ h in Metric.ball (0 : SpatialCoordinates d) (r + 1),
      ENNReal.ofReal (euclideanSquare h) / (ENNReal.ofReal (Real.sqrt (euclideanSquare h))) ^ ((d : ℝ) + 2 * s),
    kernel_lintegral_lt_top hd s hs0 hs1 (r + 1), fun φ hφ => ?_⟩
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  -- G = |∇φ|^2 on Q, 0 off Q (the segment between two points of Q stays in Q)
  set G : SpatialCoordinates d → ℝ := Q.indicator (gradientSquare φ) with hG
  have hGm : Measurable G := by
    refine Measurable.indicator ?_ hQm
    have hc := hφ.continuous_fderiv (by norm_num)
    unfold gradientSquare; fun_prop
  have hconv : Convex ℝ Q := convex_ball z (r / 2)
  calc ∫⁻ x in Q, ∫⁻ y in Q, gagliardoIntegrand s φ x y
      ≤ ∫⁻ x in Q, ∫⁻ y in Q,
          ENNReal.ofReal (euclideanSquare (y - x)) / (ENNReal.ofReal (Real.sqrt (euclideanSquare (y - x)))) ^ ((d : ℝ) + 2 * s) *
            ENNReal.ofReal (∫ t in (0 : ℝ)..1, G (x + t • (y - x))) := by
        refine setLIntegral_mono' hQm fun x hx => setLIntegral_mono' hQm fun y hy => ?_
        -- the segment stays in the convex cube, so G = gradientSquare φ along it
        have hseg : ∫ t in (0 : ℝ)..1, G (x + t • (y - x)) = ∫ t in (0 : ℝ)..1, gradientSquare φ (x + t • (y - x)) := by
          refine intervalIntegral.integral_congr fun t ht => ?_
          rw [Set.uIcc_of_le zero_le_one] at ht
          have hmem : x + t • (y - x) ∈ Q := by
            have := hconv.add_smul_sub_mem hx hy ⟨ht.1, ht.2⟩
            simpa using this
          simp [hG, Set.indicator_of_mem hmem]
        have hesym : euclideanSquare (y - x) = ∑ j : Fin d, (x j - y j) ^ 2 := by
          unfold euclideanSquare; refine Finset.sum_congr rfl fun j _ => ?_; simp only [Pi.sub_apply]; ring
        have hsq := sq_sub_le_segment φ hφ x y
        have hnn : 0 ≤ ∫ t in (0 : ℝ)..1, gradientSquare φ (x + t • (y - x)) :=
          intervalIntegral.integral_nonneg zero_le_one fun t _ => Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [hseg]
        unfold gagliardoIntegrand
        rw [← hesym, div_eq_mul_inv, div_eq_mul_inv, mul_right_comm,
          ← ENNReal.ofReal_mul (by unfold euclideanSquare; positivity)]
        gcongr
        calc (φ x - φ y) ^ 2 = (φ y - φ x) ^ 2 := by ring
          _ ≤ _ := hsq
    _ ≤ _ := segment_integral_le z hr s G (fun x => Set.indicator_nonneg (fun x _ => by
          unfold gradientSquare; positivity) x) hGm
    _ = _ := by
        congr 1
        rw [hG]
        refine setLIntegral_congr_fun hQm (fun x hx => ?_)
        exact congrArg ENNReal.ofReal (Set.indicator_of_mem hx _)

/-- (2) Smooth approximation of an H^1 function on the cube, in values and in gradient. -/
theorem exists_smooth_approx (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    ∃ φ : ℕ → SpatialCoordinates d → ℝ, (∀ n, ContDiff ℝ 1 (φ n)) ∧
      Tendsto (fun n => eLpNorm (fun x => φ n x - (u : SobolevData (centeredCube z r hr)).1 x) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0) ∧
      ∀ i : Fin d, Tendsto (fun n => eLpNorm
          (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0) := by
  classical
  obtain ⟨v, hv1, hv2⟩ := exists_nativeH1Function_of_weakSobolevGraph u
  have hU : Homogenization.IsOpenBoundedConvexDomain
      (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    refine ⟨(centeredCube z r hr).isOpen, ?_, convex_ball z (r / 2)⟩
    exact Homogenization.Bornology.IsBounded.isBoundedDomain Metric.isBounded_ball
  have hρ : (0 : ℝ) < r / 4 := by positivity
  have hball : Metric.closedBall z (r / 4) ⊆ (centeredCube z r hr : Set (SpatialCoordinates d)) := by
    intro x hx
    change x ∈ Metric.ball z (r / 2)
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx) (by linarith))
  refine ⟨fun n => (Homogenization.H1Function.convexApproxSmoothH1 hU v z hρ n).toFun,
    fun n => ?_, ?_, fun i => ?_⟩
  · dsimp only
    rw [Homogenization.H1Function.convexApproxSmoothH1_toFun]
    exact (Homogenization.contDiff_convexApproxSmoothRepresentative hU.isOpen.measurableSet
      Homogenization.isConvexApproxKernel_unitConvexApproxKernel (by norm_num) v.memL2 hρ
      (by dsimp [Homogenization.unitConvexApproxScale]; positivity)).of_le (by norm_num)
  · have h := Homogenization.tendsto_eLpNorm_convexApproxSmoothH1 hU v hρ hball
    rw [hv1] at h
    exact h
  · have h := Homogenization.tendsto_eLpNorm_grad_convexApproxSmoothH1 hU v hρ hball i
    simp only [Homogenization.H1Function.convexApproxSmoothH1_grad, hv2] at h
    simp only [Homogenization.H1Function.convexApproxSmoothH1_toFun]
    exact h


/-- (3) Fatou: a Gagliardo bound along approximants that converge in L2 passes to the limit. -/
theorem gagliardo_le_of_tendsto_L2 (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r) (s : ℝ)
    (g : SpatialCoordinates d → ℝ) (φ : ℕ → SpatialCoordinates d → ℝ)
    (_hgm : AEStronglyMeasurable g (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d))))
    (hφc : ∀ n, Continuous (φ n))
    (hconv : Tendsto (fun n => eLpNorm (fun x => φ n x - g x) 2
        (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0))
    (M : ℝ≥0∞) (hM : ∀ᶠ n in atTop, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), gagliardoIntegrand s (φ n) x y ≤ M) :
    ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)), gagliardoIntegrand s g x y ≤ M := by
  classical
  set Q : Set (SpatialCoordinates d) := (centeredCube z r hr : Set (SpatialCoordinates d)) with hQ
  set μ := volume.restrict Q with hμ
  have hQm : MeasurableSet Q := (centeredCube z r hr).isOpen.measurableSet
  -- a.e.-convergent subsequence
  have hTIM : TendstoInMeasure μ φ atTop g :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
      hconv
  obtain ⟨ns, hns, hae⟩ := hTIM.exists_seq_tendsto_ae
  -- pointwise convergence of the integrand for a.e. x and a.e. y
  have hptw : ∀ x y, Tendsto (fun k => φ (ns k) x) atTop (𝓝 (g x)) →
      Tendsto (fun k => φ (ns k) y) atTop (𝓝 (g y)) →
      Tendsto (fun k => gagliardoIntegrand s (φ (ns k)) x y) atTop (𝓝 (gagliardoIntegrand s g x y)) := by
    intro x y hx hy
    unfold gagliardoIntegrand
    have hnum : Tendsto (fun k => ENNReal.ofReal ((φ (ns k) x - φ (ns k) y) ^ 2)) atTop
        (𝓝 (ENNReal.ofReal ((g x - g y) ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (((hx.sub hy).pow 2))
    by_cases hxy : x = y
    · subst hxy; simp only [sub_self]; exact tendsto_const_nhds
    · refine ENNReal.Tendsto.div_const hnum (Or.inr ?_)
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
      have hpos : 0 < ∑ i : Fin d, (x i - y i) ^ 2 :=
        Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ _,
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hj)))⟩
      exact (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hpos))
        ENNReal.ofReal_ne_top).ne'
  have hgqm : ∀ k, Measurable (Function.uncurry (gagliardoIntegrand s (φ (ns k)))) := by
    intro k
    have hm := (hφc (ns k)).measurable
    unfold gagliardoIntegrand Function.uncurry; fun_prop
  -- Fatou in both variables
  have hM' : ∀ᶠ k in atTop, ∫⁻ x in Q, ∫⁻ y in Q, gagliardoIntegrand s (φ (ns k)) x y ≤ M :=
    (hns.tendsto_atTop.eventually hM)
  calc ∫⁻ x in Q, ∫⁻ y in Q, gagliardoIntegrand s g x y
      ≤ ∫⁻ x in Q, liminf (fun k => ∫⁻ y in Q, gagliardoIntegrand s (φ (ns k)) x y) atTop := by
        refine setLIntegral_mono_ae ?_ ?_
        · exact (Measurable.liminf fun k => (hgqm k).lintegral_prod_right).aemeasurable
        · filter_upwards [(ae_restrict_iff' hQm).mp hae] with x hx hxQ
          replace hx := hx hxQ
          calc ∫⁻ y in Q, gagliardoIntegrand s g x y
              = ∫⁻ y in Q, liminf (fun k => gagliardoIntegrand s (φ (ns k)) x y) atTop := by
                refine setLIntegral_congr_fun_ae hQm ?_
                filter_upwards [(ae_restrict_iff' hQm).mp hae] with y hy hyQ
                exact ((hptw x y hx (hy hyQ)).liminf_eq).symm
            _ ≤ liminf (fun k => ∫⁻ y in Q, gagliardoIntegrand s (φ (ns k)) x y) atTop := by
                apply lintegral_liminf_le
                intro k
                exact (hgqm k).of_uncurry_left
    _ ≤ liminf (fun k => ∫⁻ x in Q, ∫⁻ y in Q, gagliardoIntegrand s (φ (ns k)) x y) atTop := by
        apply lintegral_liminf_le
        intro k
        exact (hgqm k).lintegral_prod_right
    _ ≤ M := liminf_le_of_frequently_le' (hM'.frequently)

/-- The smooth approximants have a gradient-energy bound that depends only on
one common bound for the original coordinate gradients. -/
theorem gradient_integral_eventually_le (z : SpatialCoordinates d) {r : ℝ} (hr : 0 < r)
    (u : weakSobolevGraph (centeredCube z r hr)) (φ : ℕ → SpatialCoordinates d → ℝ)
    (B : ℝ) (hbound : ∀ i : Fin d, ‖(u : SobolevData (centeredCube z r hr)).2 i‖ ≤ B)
    (hgrad : ∀ i : Fin d, Tendsto (fun n => eLpNorm
          (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2
          (volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)))) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ENNReal.ofReal (gradientSquare (φ n) x) ≤
          ∑ _i : Fin d, (1 + ENNReal.ofReal B) ^ 2 := by
  classical
  set μ := volume.restrict (centeredCube z r hr : Set (SpatialCoordinates d)) with hμ
  set U2 : Fin d → ℝ≥0∞ := fun _ => ENNReal.ofReal B
  have hev : ∀ᶠ n in atTop, ∀ i : Fin d, eLpNorm
      (fun x => fderiv ℝ (φ n) x (Pi.single i 1) - (u : SobolevData (centeredCube z r hr)).2 i x) 2 μ ≤ 1 := by
    rw [Filter.eventually_all]
    intro i
    exact (hgrad i).eventually (Iic_mem_nhds (by norm_num))
  filter_upwards [hev] with n hn
  -- each coordinate: ∫⁻ ofReal(f^2) = (eLpNorm f 2)^2 ≤ (1 + U2 i)^2
  have hcoord : ∀ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
      ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) ≤ (1 + U2 i) ^ 2 := by
    intro i
    set f : SpatialCoordinates d → ℝ := fun x => fderiv ℝ (φ n) x (Pi.single i 1) with hf
    set w : SpatialCoordinates d → ℝ := ((u : SobolevData (centeredCube z r hr)).2 i : SpatialCoordinates d → ℝ)
    have hfm : AEStronglyMeasurable f μ :=
      (measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).aestronglyMeasurable
    have hwm : AEStronglyMeasurable w μ := Lp.aestronglyMeasurable _
    have hsq : ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (f x ^ 2) =
        eLpNorm f 2 μ ^ 2 := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfm]
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
      refine lintegral_congr fun x => ?_
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    have htri : eLpNorm f 2 μ ≤ 1 + U2 i := by
      calc eLpNorm f 2 μ = eLpNorm ((fun x => f x - w x) + w) 2 μ := by congr 1; funext x; simp
        _ ≤ eLpNorm (fun x => f x - w x) 2 μ + eLpNorm w 2 μ :=
            eLpNorm_add_le (by norm_num)
        _ ≤ 1 + U2 i := add_le_add (hn i) (by
            change eLpNorm ((u : SobolevData (centeredCube z r hr)).2 i) 2 μ ≤ ENNReal.ofReal B
            rw [← Lp.enorm_def, ← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hbound i))
    rw [hsq]
    exact pow_le_pow_left₀ (zero_le) htri 2
  calc ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)), ENNReal.ofReal (gradientSquare (φ n) x)
      = ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ∑ i : Fin d, ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) := by
        refine lintegral_congr fun x => ?_
        rw [gradientSquare, ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
    _ ≤ ∑ i : Fin d, ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
          ENNReal.ofReal ((fderiv ℝ (φ n) x (Pi.single i 1)) ^ 2) :=
        (lintegral_finsetSum _ fun i _ =>
          ((measurable_fderiv_apply_const ℝ (φ n) (Pi.single i 1)).pow_const 2).ennreal_ofReal).le
    _ ≤ ∑ i : Fin d, (1 + U2 i) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i

/-- H¹ gradient bounds give a uniform finite Euclidean Gagliardo bound. -/
theorem exists_uniform_gagliardo_bound (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (B : ℝ) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ u : weakSobolevGraph (centeredCube z r hr),
      (∀ i : Fin d, ‖(u : SobolevData (centeredCube z r hr)).2 i‖ ≤ B) →
      cubeGagliardoIntegral z r hr s (u : SobolevData (centeredCube z r hr)).1 ≤ M := by
  obtain ⟨C, hC, hsm⟩ := smooth_gagliardo_bound hd z hr s s.2.1 s.2.2
  let K : ℝ≥0∞ := ∑ _i : Fin d, (1 + ENNReal.ofReal B) ^ 2
  have hK : K < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ =>
    ENNReal.pow_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top, ENNReal.ofReal_lt_top⟩)
  refine ⟨C * K, ENNReal.mul_lt_top hC hK, ?_⟩
  intro u hu
  obtain ⟨φ, hφ, hval, hgrad⟩ := exists_smooth_approx z hr u
  have hev := gradient_integral_eventually_le z hr u φ B hu hgrad
  have hM : ∀ᶠ n in atTop,
      ∫⁻ x in (centeredCube z r hr : Set (SpatialCoordinates d)),
        ∫⁻ y in (centeredCube z r hr : Set (SpatialCoordinates d)),
          gagliardoIntegrand s (φ n) x y ≤ C * K := by
    filter_upwards [hev] with n hn
    exact (hsm (φ n) (hφ n)).trans (mul_le_mul_right hn C)
  simpa only [cubeGagliardoIntegral, gagliardoIntegrand, Homogenization.euclideanDist,
    Homogenization.euclideanNorm, Homogenization.vecNormSq, Homogenization.vecDot,
    Pi.sub_apply, ← pow_two] using
      gagliardo_le_of_tendsto_L2 z hr s _ φ (Lp.aestronglyMeasurable _)
        (fun n => (hφ n).continuous) hval (C * K) hM

/-- Native cube weak Sobolev data have genuinely finite fractional seminorm. -/
theorem cubeFractionalL2Seminorm_lt_top (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1)
    (u : weakSobolevGraph (centeredCube z r hr)) :
    cubeFractionalL2Seminorm hd z r hr s
      (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) < ⊤ := by
  let B := ∑ i : Fin d, ‖(u : SobolevData (centeredCube z r hr)).2 i‖
  obtain ⟨M, hM, hb⟩ := exists_uniform_gagliardo_bound hd z hr s B
  have hI := (hb u (fun i => Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i))).trans_lt hM
  unfold cubeFractionalL2Seminorm
  apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
  refine (ENNReal.mul_lt_top ?_ ?_).ne
  · exact ENNReal.div_lt_top ENNReal.ofReal_ne_top
      (by rw [centeredCube_volume]; exact (ENNReal.ofReal_pos.mpr (by positivity)).ne')
  · simpa only [cubeGagliardoIntegral, Fin.sum_univ_one, gagliardoIntegrand,
      Homogenization.euclideanDist, Homogenization.euclideanNorm,
      Homogenization.vecNormSq, Homogenization.vecDot, Pi.sub_apply, ← pow_two] using hI

/-- A common bound for the value and coordinate-gradient L² norms gives a
common bound for the actual normalized fractional square norm. -/
theorem exists_uniform_fractionalSqNorm_bound (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (s : Set.Ioo (0 : ℝ) 1) (B : ℝ) :
    ∃ D : ℝ, ∀ u : weakSobolevGraph (centeredCube z r hr),
      ‖(u : SobolevData (centeredCube z r hr)).1‖ ≤ B →
      (∀ i : Fin d, ‖(u : SobolevData (centeredCube z r hr)).2 i‖ ≤ B) →
      cubeFractionalSqNorm hd z r hr s (u : SobolevData (centeredCube z r hr)).1 ≤ D := by
  obtain ⟨M, hM, hb⟩ := exists_uniform_gagliardo_bound hd z hr s B
  let c := ENNReal.ofReal (s : ℝ) /
    volume (centeredCube z r hr : Set (SpatialCoordinates d))
  have hc : c < ⊤ := ENNReal.div_lt_top ENNReal.ofReal_ne_top
    (by rw [centeredCube_volume]; exact ENNReal.ofReal_ne_zero_iff.mpr (pow_pos hr d))
  have hcM : c * M ≠ ⊤ := (ENNReal.mul_lt_top hc hM).ne
  refine ⟨(c * M).toReal + B ^ 2 /
    volume.real (centeredCube z r hr : Set (SpatialCoordinates d)), ?_⟩
  intro u hu hg
  have hfinite := cubeFractionalL2Seminorm_lt_top hd z hr s u
  have he := ofReal_cubeFractionalSeminormSq hd z r hr s
    (u : SobolevData (centeredCube z r hr)).1 hfinite
  have hsemi : cubeFractionalVecSeminormSq hd z r hr s
      (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) ≤ (c * M).toReal := by
    have hle : ENNReal.ofReal (cubeFractionalVecSeminormSq hd z r hr s
        (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1)) ≤ c * M := by
      rw [he]
      exact mul_le_mul_right (hb u hg) c
    have hnon : 0 ≤ cubeFractionalVecSeminormSq hd z r hr s
        (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) := sq_nonneg _
    simpa only [ENNReal.toReal_ofReal hnon] using ENNReal.toReal_mono hcM hle
  have hl2 : ‖(u : SobolevData (centeredCube z r hr)).1‖ ^ 2 ≤ B ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  change cubeFractionalVecSeminormSq hd z r hr s
      (fun _ : Fin 1 => (u : SobolevData (centeredCube z r hr)).1) +
      (∑ _i : Fin 1, ‖(u : SobolevData (centeredCube z r hr)).1‖ ^ 2) /
        volume.real (centeredCube z r hr : Set (SpatialCoordinates d)) ≤ _
  rw [Fin.sum_univ_one]
  exact add_le_add hsemi (div_le_div_of_nonneg_right hl2
    (centeredCube_volume_pos z hr).le)

end CubeH1Bound

/-- Rellich compactness for the native cube weak Sobolev graph, with genuine
value and gradient bounds and no fractional-regularity premise. -/
theorem exists_subseq_cubeH1 (hd : 2 ≤ d) (z : SpatialCoordinates d)
    {r : ℝ} (hr : 0 < r) (u : ℕ → weakSobolevGraph (centeredCube z r hr))
    (B : ℝ)
    (hvalue : ∀ n, ‖(u n : SobolevData (centeredCube z r hr)).1‖ ≤ B)
    (hgrad : ∀ n (i : Fin d), ‖(u n : SobolevData (centeredCube z r hr)).2 i‖ ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : DomainL2 (centeredCube z r hr)),
      StrictMono phi ∧ Tendsto
        (fun n => (u (phi n) : SobolevData (centeredCube z r hr)).1) atTop (𝓝 w) := by
  let s : Set.Ioo (0 : ℝ) 1 := ⟨1 / 2, by norm_num, by norm_num⟩
  obtain ⟨D, hD⟩ := CubeH1Bound.exists_uniform_fractionalSqNorm_bound hd z hr s B
  exact exists_subseq_of_cubeFractionalSqNorm_bounded d hd s z r hr
    (fun n => (u n : SobolevData (centeredCube z r hr)).1) D
    (fun n => CubeH1Bound.cubeFractionalL2Seminorm_lt_top hd z hr s (u n))
    (fun n => hD (u n) (hvalue n) (hgrad n))

/-- The exact weighted-ball L² carrier is compact along sequences with bounded
native cube H¹ data; the transport still preserves the functions almost everywhere. -/
theorem exists_subseq_cubeH1_dirichletVolume (hd : 2 ≤ d)
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : ℕ → weakSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)))
    (B : ℝ)
    (hvalue : ∀ n, ‖(u n : SobolevData
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))).1‖ ≤ B)
    (hgrad : ∀ n (i : Fin d), ‖(u n : SobolevData
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))).2 i‖ ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : Lp ℝ 2 (dirichletVolume ρ R)),
      StrictMono phi ∧ Tendsto
        (fun n => cubeToDirichletL2 ρ R hR C hρ
          (u (phi n) : SobolevData
            (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))).1)
        atTop (𝓝 w) := by
  obtain ⟨phi, w, hphi, hconv⟩ := exists_subseq_cubeH1 hd
    (0 : SpatialCoordinates d) (mul_pos two_pos hR) u B hvalue hgrad
  exact ⟨phi, cubeToDirichletL2 ρ R hR C hρ w, hphi,
    ((cubeToDirichletL2 ρ R hR C hρ).continuous.tendsto w).comp hconv⟩

/-- Bounded global source weak-gradient data have a strongly convergent
subsequence in the exact weighted Dirichlet-ball L² space. The approximating
classes are the literal restrictions of the original functions. -/
theorem exists_subseq_globalH1_dirichletVolume (hd : 2 ≤ d)
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (f : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d)
    (hf : ∀ n, MemLp (f n) 2 volume)
    (hg : ∀ n (i : Fin d), MemLp (fun x => g n x i) 2 volume)
    (hw : ∀ n, EinsteinRelation.HasWeakGradient Set.univ (f n) (g n))
    (B : ℝ) (hvalue : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (hgrad : ∀ n (i : Fin d), ‖(hg n i).toLp (fun x => g n x i)‖ ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : Lp ℝ 2 (dirichletVolume ρ R)),
      StrictMono phi ∧ Tendsto
        (fun n => cubeToDirichletL2 ρ R hR C hρ
          (((hf (phi n)).restrict
            (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))).toLp
              (f (phi n)))) atTop (𝓝 w) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let u : ℕ → weakSobolevGraph Q := fun n =>
    cubeGraphOfGlobalWeakGradient Q (f n) (g n) (hf n) (hg n) (hw n)
  have hvalue' (n : ℕ) : ‖(u n : SobolevData Q).1‖ ≤ B :=
    (cubeGraphOfGlobalWeakGradient_norm_le Q (f n) (g n) (hf n) (hg n) (hw n)).1.trans
      (hvalue n)
  have hgrad' (n : ℕ) (i : Fin d) : ‖(u n : SobolevData Q).2 i‖ ≤ B :=
    ((cubeGraphOfGlobalWeakGradient_norm_le Q (f n) (g n) (hf n) (hg n) (hw n)).2 i).trans
      (hgrad n i)
  exact exists_subseq_cubeH1_dirichletVolume hd ρ R hR C hρ u B hvalue' hgrad'


/-- The genuine Euclidean ball, as an open set on the unchanged carrier. -/
def dirichletBall (R : ℝ) : Opens (SpatialCoordinates d) :=
  ⟨sourceBall (0 : Vec d) R, by
    have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      exact Real.continuous_sqrt.comp (continuous_finsetSum _
        (fun j _ => (continuous_apply j).mul (continuous_apply j)))
    unfold sourceBall
    exact isOpen_lt (hc.comp (continuous_id.sub continuous_const)) continuous_const⟩

/-- Value and gradient coordinates with their sum-of-squares Hilbert norm.
The spatial carrier and its Euclidean Dirichlet ball are unchanged. -/
abbrev HilbertSobolevData (Ω : Opens (SpatialCoordinates d)) :=
  PiLp 2 (fun _ : Option (Fin d) => DomainL2 Ω)

/-- The actual value/gradient projection from Hilbert data to the native graph. -/
def hilbertToSobolev (Ω : Opens (SpatialCoordinates d)) :
    HilbertSobolevData Ω →L[ℝ] SobolevData Ω :=
  (ContinuousLinearMap.proj none).prod
    (ContinuousLinearMap.pi (fun i : Fin d => ContinuousLinearMap.proj (some i))) |>.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => DomainL2 Ω)).toContinuousLinearMap

/-- Conversely, package native value and gradient coordinates with their Hilbert norm. -/
def sobolevToHilbert (Ω : Opens (SpatialCoordinates d)) :
    SobolevData Ω →L[ℝ] HilbertSobolevData Ω :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => DomainL2 Ω)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Option (Fin d) => match j with
      | none => ContinuousLinearMap.fst ℝ _ _
      | some i => (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℝ _ _))

/-- Packaging retains every coordinate exactly. -/
theorem hilbertToSobolev_sobolevToHilbert (Ω : Opens (SpatialCoordinates d))
    (z : SobolevData Ω) : hilbertToSobolev Ω (sobolevToHilbert Ω z) = z := by
  apply Prod.ext
  · rfl
  · rfl

/-- Each actual coordinate norm is bounded by the Hilbert graph norm. -/
theorem hilbertToSobolev_norm_le (Ω : Opens (SpatialCoordinates d))
    (z : HilbertSobolevData Ω) :
    ‖(hilbertToSobolev Ω z).1‖ ≤ ‖z‖ ∧
      ∀ i, ‖(hilbertToSobolev Ω z).2 i‖ ≤ ‖z‖ := by
  constructor
  · exact PiLp.norm_apply_le z none
  · intro i
    exact PiLp.norm_apply_le z (some i)

/-- Smooth tests supported in the Euclidean ball, viewed on the containing cube. -/
def dirichletTestInCube (R : ℝ) (hR : 0 < R) :
    TestFunction (dirichletBall (d := d) R) ℝ ⊤ →ₗ[ℝ]
      TestFunction (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) ℝ ⊤ where
  toFun φ := ⟨φ, φ.contDiff, φ.hasCompactSupport,
    φ.tsupport_subset.trans (sourceBall_subset_cube R hR)⟩
  map_add' φ ψ := by ext; rfl
  map_smul' c φ := by ext; rfl

/-- Actual smooth zero-boundary data on the source ball, with Hilbert graph norm. -/
def dirichletSmoothData (R : ℝ) (hR : 0 < R) :
    TestFunction (dirichletBall (d := d) R) ℝ ⊤ →ₗ[ℝ]
      HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)) :=
  (sobolevToHilbert _).toLinearMap.comp
    ((smoothSobolevDataLinear).comp (dirichletTestInCube R hR))

/-- The zero-boundary Dirichlet space is the closure of actual smooth tests
supported in the Euclidean ball, using the full value/gradient Hilbert norm. -/
def dirichletHilbertSubmodule (R : ℝ) (hR : 0 < R) :
    Submodule ℝ (HilbertSobolevData (centeredCube (0 : SpatialCoordinates d)
      (2 * R) (mul_pos two_pos hR))) :=
  (LinearMap.range (dirichletSmoothData R hR)).topologicalClosure

/-- The actual Dirichlet graph is closed; no closed-form assumption is supplied. -/
theorem isClosed_dirichletHilbertSubmodule (R : ℝ) (hR : 0 < R) :
    IsClosed (dirichletHilbertSubmodule (d := d) R hR :
      Set (HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
        (mul_pos two_pos hR)))) :=
  Submodule.isClosed_topologicalClosure _

/-- The concrete Dirichlet Hilbert space. -/
abbrev DirichletHilbertSpace (R : ℝ) (hR : 0 < R) :=
  dirichletHilbertSubmodule (d := d) R hR

instance dirichletHilbertSpace_complete (R : ℝ) (hR : 0 < R) :
    CompleteSpace (DirichletHilbertSpace (d := d) R hR) := by
  have := isClosed_dirichletHilbertSubmodule (d := d) R hR
  exact IsClosed.completeSpace_coe

/-- Every element of the completed Dirichlet space has its actual weak gradient
on the containing cube, obtained by closing the smooth distributional identities. -/
theorem dirichletHilbert_mem_weakSobolevGraph (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    hilbertToSobolev _ u.val ∈ weakSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hc : IsClosed
      ((weakSobolevGraph Q).comap (hilbertToSobolev Q).toLinearMap :
        Set (HilbertSobolevData Q)) :=
    isClosed_weakSobolevGraph.preimage (hilbertToSobolev Q).continuous
  have hrange : LinearMap.range (dirichletSmoothData R hR) ≤
      (weakSobolevGraph Q).comap (hilbertToSobolev Q).toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    change hilbertToSobolev Q
      (sobolevToHilbert Q (smoothSobolevData (dirichletTestInCube R hR φ))) ∈
        weakSobolevGraph Q
    rw [hilbertToSobolev_sobolevToHilbert]
    exact smoothSobolevData_mem _
  exact (Submodule.topologicalClosure_minimal _ hrange hc) u.property

/-- Canonical inclusion of the actual zero-boundary Hilbert space into the
weighted ball L² carrier of the source Dirichlet spectral problem. -/
def dirichletHilbertInclusion (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    DirichletHilbertSpace (d := d) R hR →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R) :=
  (cubeToDirichletL2 ρ R hR C hρ).comp
    ((ContinuousLinearMap.fst ℝ _ _).comp
      ((hilbertToSobolev _).comp (dirichletHilbertSubmodule R hR).subtypeL))

/-- The inclusion is the literal function coordinate almost everywhere. -/
theorem dirichletHilbertInclusion_coe (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : DirichletHilbertSpace (d := d) R hR) :
    dirichletHilbertInclusion ρ R hR C hρ u =ᵐ[dirichletVolume ρ R]
      (hilbertToSobolev _ u.val).1 :=
  cubeToDirichletL2_coe ρ R hR C hρ _

/-- Bounded sequences in the actual Dirichlet Hilbert space have subsequences
converging strongly in the exact weighted spectral carrier. -/
theorem exists_subseq_dirichletHilbertInclusion (hd : 2 ≤ d)
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (B : ℝ) (hu : ∀ n, ‖u n‖ ≤ B) :
    ∃ (phi : ℕ → ℕ) (w : Lp ℝ 2 (dirichletVolume ρ R)),
      StrictMono phi ∧ Tendsto
        (fun n => dirichletHilbertInclusion ρ R hR C hρ (u (phi n)))
        atTop (𝓝 w) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let v : ℕ → weakSobolevGraph Q := fun n =>
    ⟨hilbertToSobolev Q (u n).val, dirichletHilbert_mem_weakSobolevGraph R hR (u n)⟩
  exact exists_subseq_cubeH1_dirichletVolume hd ρ R hR C hρ v B
    (fun n => (hilbertToSobolev_norm_le Q (u n).val).1.trans (hu n))
    (fun n i => ((hilbertToSobolev_norm_le Q (u n).val).2 i).trans (hu n))


/-- The inclusion of the completed zero-boundary Hilbert graph is a compact
operator, rather than an assumed compactness property of an abstract form. -/
theorem isCompactOperator_dirichletHilbertInclusion (hd : 2 ≤ d)
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    IsCompactOperator (dirichletHilbertInclusion ρ R hR C hρ) := by
  let J := dirichletHilbertInclusion ρ R hR C hρ
  let S := J '' Metric.closedBall 0 1
  have htot : TotallyBounded S := by
    intro V hV
    by_contra h
    obtain ⟨v, hv, hvsep⟩ : ∃ v : ℕ → Lp ℝ 2 (dirichletVolume ρ R),
        (∀ n, v n ∈ S) ∧ ∀ n m, m < n → v m ∉ UniformSpace.ball (v n) V := by
      push Not at h
      simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
      simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
    choose u hu heq using hv
    have hnorm (n : ℕ) : ‖u n‖ ≤ (1 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hu n
    obtain ⟨phi, w, hphi, hconv⟩ :=
      exists_subseq_dirichletHilbertInclusion hd ρ R hR C hρ u 1 hnorm
    have hvconv : Tendsto (fun n => v (phi n)) atTop (𝓝 w) := by
      simpa only [J, heq] using hconv
    obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N →
        (v (phi p), v (phi q)) ∈ V := hvconv.cauchySeq.mem_entourage hV
    exact hvsep (phi (N + 1)) (phi N) (hphi (Nat.lt_add_one N))
      (hN (N + 1) N N.le_succ le_rfl)
  exact (isCompactOperator_iff_isCompact_closure_image_closedBall
    J.toLinearMap (by norm_num : (0 : ℝ) < 1)).mpr
      (htot.closure.isCompact_of_isClosed isClosed_closure)


/-- Restrict a cube L² class to the exterior of the actual Euclidean ball. -/
def dirichletExteriorRestriction (Ω : Opens (SpatialCoordinates d)) (R : ℝ) :
    DomainL2 Ω →L[ℝ]
      Lp ℝ 2 ((volume.restrict (Ω : Set (SpatialCoordinates d))).restrict
        (sourceBall (0 : Vec d) R)ᶜ) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa only [one_smul] using
      (Measure.restrict_le_self :
        (volume.restrict (Ω : Set (SpatialCoordinates d))).restrict
          (sourceBall (0 : Vec d) R)ᶜ ≤ volume.restrict (Ω : Set (SpatialCoordinates d))))

/-- Every coordinate of the completed Dirichlet graph vanishes on the exterior
of the Euclidean ball. This follows from the closure of actual supported tests. -/
theorem dirichletHilbert_coordinate_zero_exterior (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) (j : Option (Fin d)) :
    ∀ᵐ x ∂volume.restrict
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
        Set (SpatialCoordinates d)),
      x ∉ sourceBall (0 : Vec d) R → u.val j x = 0 := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let P : HilbertSobolevData Q →L[ℝ] DomainL2 Q :=
    (ContinuousLinearMap.proj j).comp
      (PiLp.continuousLinearEquiv 2 ℝ
        (fun _ : Option (Fin d) => DomainL2 Q)).toContinuousLinearMap
  let F := (dirichletExteriorRestriction Q R).comp P
  have hrange : LinearMap.range (dirichletSmoothData R hR) ≤
      LinearMap.ker F.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    apply Lp.ext
    have hrep := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
      (show (volume.restrict (Q : Set (SpatialCoordinates d))).restrict
          (sourceBall (0 : Vec d) R)ᶜ ≤ 1 • volume.restrict (Q : Set (SpatialCoordinates d)) by
        simpa only [one_smul] using Measure.restrict_le_self)
      (P (dirichletSmoothData R hR φ))
    have hj : P (dirichletSmoothData R hR φ) =ᵐ[volume.restrict (Q : Set (SpatialCoordinates d))]
        (match j with
          | none => (φ : Vec d → ℝ)
          | some i => fun x => fderiv ℝ (φ : Vec d → ℝ) x (Pi.single i 1)) := by
      cases j with
      | none => exact testL2_coeFn (dirichletTestInCube R hR φ)
      | some i => exact testPartialL2_coeFn (dirichletTestInCube R hR φ) i
    filter_upwards [hrep, ae_restrict_of_ae hj,
      ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet.compl,
      Lp.coeFn_zero ℝ 2 ((volume.restrict (Q : Set (SpatialCoordinates d))).restrict
        (sourceBall (0 : Vec d) R)ᶜ)] with x hx hjx hout hz
    change (F (dirichletSmoothData R hR φ)) x = (0 : Lp ℝ 2 _) x
    rw [show (F (dirichletSmoothData R hR φ)) x =
      P (dirichletSmoothData R hR φ) x from hx, hjx, hz]
    have hnot : x ∉ tsupport (φ : Vec d → ℝ) :=
      fun hx => hout (φ.tsupport_subset hx)
    cases j with
    | none => exact image_eq_zero_of_notMem_tsupport hnot
    | some i => simp only [fderiv_of_notMem_tsupport ℝ hnot, zero_apply, Pi.zero_apply]
  have hzero : F u.val = 0 :=
    (Submodule.topologicalClosure_minimal _ hrange F.isClosed_ker) u.property
  have hrep := Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (show (volume.restrict (Q : Set (SpatialCoordinates d))).restrict
        (sourceBall (0 : Vec d) R)ᶜ ≤ 1 • volume.restrict (Q : Set (SpatialCoordinates d)) by
      simpa only [one_smul] using Measure.restrict_le_self) (P u.val)
  have hae : ∀ᵐ x ∂(volume.restrict (Q : Set (SpatialCoordinates d))).restrict
      (sourceBall (0 : Vec d) R)ᶜ, u.val j x = 0 := by
    filter_upwards [hrep, Lp.coeFn_zero ℝ 2
      ((volume.restrict (Q : Set (SpatialCoordinates d))).restrict
        (sourceBall (0 : Vec d) R)ᶜ)] with x hx hz
    have heq : (0 : Lp ℝ 2 ((volume.restrict (Q : Set (SpatialCoordinates d))).restrict
        (sourceBall (0 : Vec d) R)ᶜ)) x = u.val j x := by
      change (F u.val) x = u.val j x at hx
      rw [hzero] at hx
      exact hx
    exact heq.symm.trans hz
  exact (ae_restrict_iff' (dirichletBall (d := d) R).isOpen.measurableSet.compl).mp hae


/-- The Hilbert norm is exactly the value L² norm plus the sum of squared
coordinate gradient norms; no sup-norm replacement enters the energy. -/
theorem dirichletHilbert_norm_sq (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ‖u‖ ^ 2 = ‖(hilbertToSobolev _ u.val).1‖ ^ 2 +
      ∑ i : Fin d, ‖(hilbertToSobolev _ u.val).2 i‖ ^ 2 := by
  change ‖u.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2]
  exact Fintype.sum_option _

/-- The completed ball-supported graph is also genuinely in the killed
Sobolev graph of its containing cube, preserving zero extension across that cube. -/
theorem dirichletHilbert_mem_killedSobolevGraph (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    hilbertToSobolev _ u.val ∈ killedSobolevGraph
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hc : IsClosed
      ((killedSobolevGraph Q).comap (hilbertToSobolev Q).toLinearMap :
        Set (HilbertSobolevData Q)) :=
    isClosed_killedSobolevGraph.preimage (hilbertToSobolev Q).continuous
  have hrange : LinearMap.range (dirichletSmoothData R hR) ≤
      (killedSobolevGraph Q).comap (hilbertToSobolev Q).toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    change hilbertToSobolev Q
      (sobolevToHilbert Q (smoothSobolevData (dirichletTestInCube R hR φ))) ∈
        killedSobolevGraph Q
    rw [hilbertToSobolev_sobolevToHilbert]
    exact smoothSobolevData_mem_killed _
  exact (Submodule.topologicalClosure_minimal _ hrange hc) u.property


/-- Actual multiplication by a bounded measurable scalar is continuous on L².
This is the direct L² construction, with no coefficient-operator premise. -/
theorem exists_boundedL2Multiplier {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (a : X → ℝ) (ha : AEStronglyMeasurable a μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂μ, |a x| ≤ C) :
    ∃ T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, ‖T‖ ≤ C ∧
      ∀ f, (T f : X → ℝ) =ᵐ[μ] fun x => a x * f x := by
  have hm (f : Lp ℝ 2 μ) : MemLp (fun x => a x * f x) 2 μ :=
    (Lp.memLp f).of_le_mul (ha.mul (Lp.aestronglyMeasurable f)) (by
      filter_upwards [hb] with x hx
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
  let T : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun f => (hm f).toLp (fun x => a x * f x)
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hm (f + g)),
          MemLp.coeFn_toLp (hm f), MemLp.coeFn_toLp (hm g), Lp.coeFn_add f g,
          Lp.coeFn_add ((hm f).toLp (fun x => a x * f x))
            ((hm g).toLp (fun x => a x * g x))] with x hfg hf hg hadd hout
        rw [hfg, hout]
        simp only [Pi.add_apply]
        rw [hf, hg, hadd]
        simp only [Pi.add_apply, mul_add]
      map_smul' := fun r f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (hm (r • f)), MemLp.coeFn_toLp (hm f),
          Lp.coeFn_smul r f, Lp.coeFn_smul r ((hm f).toLp (fun x => a x * f x))]
          with x hrf hf hsm hout
        change ((hm (r • f)).toLp (fun x => a x * (r • f) x)) x =
          (r • (hm f).toLp (fun x => a x * f x)) x
        rw [hrf, hout]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hf, hsm]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  have ht (f : Lp ℝ 2 μ) : ‖T f‖ ≤ C * ‖f‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [MemLp.coeFn_toLp (hm f), hb] with x hx hb
    change ‖((hm f).toLp (fun x => a x * f x)) x‖ ≤ _
    rw [hx]
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  refine ⟨T.mkContinuous C ht, LinearMap.mkContinuous_norm_le _ hC ht, ?_⟩
  intro f
  exact MemLp.coeFn_toLp (hm f)

/-- Bounded measurable entries act on a finite Hilbert tuple of scalar L²
classes by their actual double-sum integral. -/
theorem exists_coordinateL2Form {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ι → ℝ)
    (ha : ∀ i j, AEStronglyMeasurable (fun x => a x i j) μ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ M) :
    ∃ B : PiLp 2 (fun _ : ι => Lp ℝ 2 μ) →L[ℝ]
        PiLp 2 (fun _ : ι => Lp ℝ 2 μ) →L[ℝ] ℝ,
      ∀ u v, B u v = ∫ x, ∑ i, ∑ j, a x i j * u j x * v i x ∂μ := by
  classical
  let H := PiLp 2 (fun _ : ι => Lp ℝ 2 μ)
  let P (i : ι) : H →L[ℝ] Lp ℝ 2 μ :=
    (ContinuousLinearMap.proj i).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => Lp ℝ 2 μ)).toContinuousLinearMap
  choose T _ hT using fun i j => exists_boundedL2Multiplier μ
    (fun x => a x i j) (ha i j) hM (hb.mono fun x hx => hx i j)
  let b (i j : ι) : H →L[ℝ] H →L[ℝ] ℝ :=
    (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).bilinearComp
      ((T i j).comp (P j)) (P i)
  have hbij (i j : ι) (u v : H) :
      b i j u v = ∫ x, a x i j * u j x * v i x ∂μ := by
    change inner ℝ (T i j (P j u)) (P i v) = _
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hT i j (P j u)] with x hx
    simp only [RCLike.inner_apply, conj_trivial, hx]
    change v i x * (a x i j * u j x) = a x i j * u j x * v i x
    ring
  have hint (i j : ι) (u v : H) :
      Integrable (fun x => a x i j * u j x * v i x) μ := by
    apply ((Lp.memLp (T i j (P j u))).integrable_mul (Lp.memLp (P i v))).congr
    filter_upwards [hT i j (P j u)] with x hx
    simp only [Pi.mul_apply, hx]
    rfl
  refine ⟨∑ i, ∑ j, b i j, ?_⟩
  intro u v
  simp only [sum_apply]
  simp_rw [hbij]
  have hi (i : ι) : (∑ j, ∫ x, a x i j * u j x * v i x ∂μ) =
      ∫ x, ∑ j, a x i j * u j x * v i x ∂μ :=
    (integral_finsetSum Finset.univ (fun j _ => hint i j u v)).symm
  simp_rw [hi]
  exact (integral_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint i j u v))).symm

/-- The actual mass and elliptic coefficients on value/gradient coordinates. -/
def dirichletValueGradientMatrix (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (x : Vec d) : Option (Fin d) → Option (Fin d) → ℝ
  | none, none => ρ x
  | some i, some j => α x i j
  | _, _ => 0

/-- The augmented quadratic form is exactly the source mass plus its Euclidean
coefficient energy, with all cross terms retained. -/
theorem dirichletValueGradientMatrix_sum (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (x : Vec d) (u v : Option (Fin d) → ℝ) :
    (∑ i, ∑ j, dirichletValueGradientMatrix ρ α x i j * u j * v i) =
      ρ x * u none * v none +
        dot ((α x).mulVec (fun i => u (some i))) (fun i => v (some i)) := by
  simp only [Fintype.sum_option, dirichletValueGradientMatrix, zero_mul,
    Finset.sum_const_zero, add_zero, zero_add, dot, Matrix.mulVec, dotProduct,
    Finset.sum_mul]

/-- Source ellipticity bounds every actual augmented matrix entry. -/
theorem dirichletValueGradientMatrix_bound {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (i j : Option (Fin d)) :
    |dirichletValueGradientMatrix ρ α x i j| ≤ κ⁻¹ := by
  have hκi : 0 ≤ κ⁻¹ := inv_nonneg.mpr hκ.le
  have hx := h.2.2 x
  cases i with
  | none => cases j with
    | none =>
      change |ρ x| ≤ κ⁻¹
      rw [abs_of_nonneg (hκ.le.trans hx.1)]
      exact hx.2.1
    | some j => simpa only [dirichletValueGradientMatrix, abs_zero] using hκi
  | some i => cases j with
    | none => simpa only [dirichletValueGradientMatrix, abs_zero] using hκi
    | some j =>
      have hv := Correctors.mulVec_euclideanNorm_le_of_quadratic (α x)
        (inv_pos.mpr hκ) hx.2.2.1
        (fun v => (mul_nonneg hκ.le (by
          unfold euclideanSq dot
          exact Finset.sum_nonneg fun k _ => mul_self_nonneg _)).trans (hx.2.2.2 v).1)
        (fun v => (hx.2.2.2 v).2) (unitVector j)
      have hj : euclideanNorm (unitVector j : Vec d) = 1 := by
        change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
        rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
      rw [hj, mul_one] at hv
      have hc := PiLp.norm_apply_le (WithLp.toLp 2 ((α x).mulVec (unitVector j))) i
      change |((α x).mulVec (unitVector j)) i| ≤
        ‖(WithLp.toLp 2 ((α x).mulVec (unitVector j)) : EuclideanSpace ℝ (Fin d))‖ at hc
      rw [← TimeChange.euclideanNorm_eq_norm_toLp] at hc
      have he : ((α x).mulVec (unitVector j)) i = α x i j := by
        change dotProduct (fun k => α x i k) (Pi.single j 1) = _
        rw [dotProduct_single, mul_one]
      simpa only [dirichletValueGradientMatrix, he] using hc.trans hv


/-- The literal coordinate form is integrable under bounded measurable entries. -/
theorem integrable_coordinateL2Form {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ι → ℝ)
    (ha : ∀ i j, AEStronglyMeasurable (fun x => a x i j) μ)
    {M : ℝ} (hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ M)
    (u v : PiLp 2 (fun _ : ι => Lp ℝ 2 μ)) :
    Integrable (fun x => ∑ i, ∑ j, a x i j * u j x * v i x) μ := by
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have hatop : MemLp (fun x => a x i j) ⊤ μ :=
    memLp_top_of_bound (ha i j) M (by
      filter_upwards [hb] with x hx
      simpa only [Real.norm_eq_abs] using hx i j)
  apply (((Lp.memLp (u j)).fun_mul (r := 2) hatop).integrable_mul (Lp.memLp (v i))).congr
  exact ae_of_all _ fun x => by dsimp; ring

/-- Finite coordinate L² energies add to the exact Hilbert norm. -/
theorem integral_coordinateL2_norm_sq {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (u : PiLp 2 (fun _ : ι => Lp ℝ 2 μ)) :
    (∫ x, ∑ j, u j x ^ 2 ∂μ) = ‖u‖ ^ 2 := by
  rw [integral_finsetSum Finset.univ (fun j _ => (Lp.memLp (u j)).integrable_sq),
    PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro j _
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by simp only [RCLike.inner_apply, conj_trivial]; ring

/-- Source measurability gives every augmented coefficient entry. -/
theorem dirichletValueGradientMatrix_aestronglyMeasurable
    {κ : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (μ : Measure (Vec d))
    (i j : Option (Fin d)) :
    AEStronglyMeasurable (fun x => dirichletValueGradientMatrix ρ α x i j) μ := by
  cases i with
  | none => cases j with
    | none => exact h.1.aestronglyMeasurable
    | some j => exact aestronglyMeasurable_const
  | some i => cases j with
    | none => exact aestronglyMeasurable_const
    | some j =>
      let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
      exact (((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        h.2.1).aestronglyMeasurable

/-- Uniform ellipticity of the source fields controls the full value-gradient
Hilbert norm pointwise; the spatial quadratic form remains Euclidean. -/
theorem dirichletValueGradientMatrix_coercive {κ : ℝ} (_hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (u : Option (Fin d) → ℝ) :
    κ * (∑ j, u j ^ 2) ≤
      ∑ i, ∑ j, dirichletValueGradientMatrix ρ α x i j * u j * u i := by
  rw [dirichletValueGradientMatrix_sum, Fintype.sum_option]
  have hm := mul_le_mul_of_nonneg_right (h.2.2 x).1 (sq_nonneg (u none))
  have hg := ((h.2.2 x).2.2.2 (fun i => u (some i))).1
  change κ * (∑ i, u (some i) * u (some i)) ≤
    dot (fun i => u (some i)) ((α x).mulVec (fun i => u (some i))) at hg
  change κ * (∑ i, u (some i) * u (some i)) ≤
    dotProduct (fun i => u (some i)) ((α x).mulVec (fun i => u (some i))) at hg
  rw [dotProduct_comm] at hg
  simp only [← pow_two] at hg
  change κ * (u none ^ 2 + ∑ i, u (some i) ^ 2) ≤
    ρ x * u none * u none +
      dotProduct ((α x).mulVec (fun i => u (some i))) (fun i => u (some i))
  nlinarith only [hm, hg]

/-- The actual source coefficients give a bounded coercive mass-plus-Dirichlet
form on the completed ball-supported space. No closed-form premise is used. -/
theorem exists_dirichletHilbert_coerciveForm {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ B : DirichletHilbertSpace (d := d) R hR →L[ℝ]
        DirichletHilbertSpace (d := d) R hR →L[ℝ] ℝ,
      IsCoercive B ∧
      ∀ u v, B u v = ∫ x in
        (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
          Set (SpatialCoordinates d)),
        ρ x * u.val none x * v.val none x +
          dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let a := dirichletValueGradientMatrix ρ α
  have ha := dirichletValueGradientMatrix_aestronglyMeasurable h μ
  have hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ κ⁻¹ :=
    ae_of_all _ fun x i j => dirichletValueGradientMatrix_bound hκ h x i j
  obtain ⟨D, hD⟩ := exists_coordinateL2Form μ a ha (inv_nonneg.mpr hκ.le) hb
  let S := (dirichletHilbertSubmodule (d := d) R hR).subtypeL
  let B := D.bilinearComp S S
  refine ⟨B, ?_, ?_⟩
  · refine ⟨κ, hκ, ?_⟩
    intro u
    have hi := integrable_coordinateL2Form μ a ha hb u.val u.val
    have hs : Integrable (fun x => ∑ j, u.val j x ^ 2) μ :=
      integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (u.val j)).integrable_sq)
    have hbound := integral_mono (hs.const_mul κ) hi
      (fun x => dirichletValueGradientMatrix_coercive hκ h x (fun j => u.val j x))
    rw [integral_const_mul, integral_coordinateL2_norm_sq] at hbound
    change κ * ‖u‖ * ‖u‖ ≤ D u.val u.val
    rw [hD]
    change κ * ‖u.val‖ * ‖u.val‖ ≤ _
    convert hbound using 1
    ring
  · intro u v
    change D u.val v.val = _
    rw [hD]
    exact integral_congr_ae (ae_of_all _ fun x =>
      dirichletValueGradientMatrix_sum ρ α x (fun j => u.val j x) (fun j => v.val j x))

/-- The form integral on the containing cube is literally its Dirichlet-ball
integral: every coordinate of the completed test space vanishes outside the ball. -/
theorem dirichletHilbert_integral_eq_ball (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (R : ℝ) (hR : 0 < R) (u v : DirichletHilbertSpace (d := d) R hR) :
    (∫ x in
      (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
        Set (SpatialCoordinates d)),
      ρ x * u.val none x * v.val none x +
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x)) =
    ∫ x in sourceBall (0 : Vec d) R,
      ρ x * u.val none x * v.val none x +
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hz : ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      ∀ j : Option (Fin d), x ∉ sourceBall (0 : Vec d) R → u.val j x = 0 :=
    ae_all_iff.mpr (fun j => dirichletHilbert_coordinate_zero_exterior R hR u j)
  have heq := setIntegral_eq_integral_of_ae_compl_eq_zero (s := sourceBall (0 : Vec d) R)
    (f := fun x => ρ x * u.val none x * v.val none x +
      dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x))
    (show ∀ᵐ x ∂volume.restrict (Q : Set (SpatialCoordinates d)),
      x ∉ sourceBall (0 : Vec d) R →
        ρ x * u.val none x * v.val none x +
          dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) = 0 by
      filter_upwards [hz] with x hx hout
      have hg : (fun i => u.val (some i) x) = 0 := funext (fun i => hx (some i) hout)
      rw [hx none hout, hg]
      simp only [mul_zero, zero_mul, Matrix.mulVec_zero, dot, Pi.zero_apply,
        zero_mul, Finset.sum_const_zero, add_zero])
  have hmeas : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  rw [Measure.restrict_restrict hmeas,
    Set.inter_eq_left.mpr (sourceBall_subset_cube R hR)] at heq
  exact heq.symm

/-- Lax--Milgram constructs the resolvent from the literal uniformly elliptic
fields on the closure of supported smooth tests. Its weighted-ball realization
is compact, and its variational equation determines it uniquely. -/
theorem exists_compact_dirichletHilbert_resolvent (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧
      ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
        u = S f ↔ ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            ρ x * u.val none x * v.val none x +
              dot ((α x).mulVec (fun i => u.val (some i) x))
                (fun i => v.val (some i) x)) = inner ℝ f (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨B, hB, hform⟩ := exists_dirichletHilbert_coerciveForm hκ h R hR
  have hball (u v : DirichletHilbertSpace (d := d) R hR) :
      B u v = ∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * v.val none x +
          dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) :=
    (hform u v).trans (dirichletHilbert_integral_eq_ball ρ α R hR u v)
  let E := hB.continuousLinearEquivOfBilin
  let S := E.symm.toContinuousLinearMap.comp J.adjoint
  have heq (f : Lp ℝ 2 (dirichletVolume ρ R))
      (v : DirichletHilbertSpace (d := d) R hR) : B (S f) v = inner ℝ f (J v) := by
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (E (E.symm (J.adjoint f))) v = _
    rw [E.apply_symm_apply]
    exact J.adjoint_inner_left v f
  refine ⟨S, ?_, ?_⟩
  · exact (isCompactOperator_dirichletHilbertInclusion hd ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1)).comp_clm S
  · intro f u
    constructor
    · rintro rfl v
      rw [← hball]
      exact heq f v
    · intro hu
      have he : J.adjoint f = E u := hB.unique_continuousLinearEquivOfBilin
        (fun v => (J.adjoint_inner_left v f).trans ((hu v).symm.trans (hball u v).symm))
      change u = E.symm (J.adjoint f)
      rw [he, E.symm_apply_apply]

/-- The literal ball energy controls the full completed value-gradient norm
with the original ellipticity constant. -/
theorem dirichletHilbert_ballIntegral_coercive {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR) :
    κ * ‖u‖ ^ 2 ≤ ∫ x in sourceBall (0 : Vec d) R,
      ρ x * u.val none x * u.val none x +
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => u.val (some i) x) := by
  rw [← dirichletHilbert_integral_eq_ball ρ α R hR u u]
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let a := dirichletValueGradientMatrix ρ α
  have ha := dirichletValueGradientMatrix_aestronglyMeasurable h μ
  have hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ κ⁻¹ :=
    ae_of_all _ fun x i j => dirichletValueGradientMatrix_bound hκ h x i j
  have hi := integrable_coordinateL2Form μ a ha hb u.val u.val
  have hs : Integrable (fun x => ∑ j, u.val j x ^ 2) μ :=
    integrable_finsetSum Finset.univ (fun j _ => (Lp.memLp (u.val j)).integrable_sq)
  have hbound := integral_mono (hs.const_mul κ) hi
    (fun x => dirichletValueGradientMatrix_coercive hκ h x (fun j => u.val j x))
  rw [integral_const_mul, integral_coordinateL2_norm_sq] at hbound
  have heq : (∫ x, ∑ i, ∑ j, a x i j * u.val j x * u.val i x ∂μ) =
      ∫ x, ρ x * u.val none x * u.val none x +
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => u.val (some i) x) ∂μ :=
    integral_congr_ae (ae_of_all _ fun x =>
      dirichletValueGradientMatrix_sum ρ α x (fun j => u.val j x) (fun j => u.val j x))
  exact hbound.trans_eq heq

/-- Symmetry of the source matrix gives symmetry of the actual ball energy. -/
theorem dirichletHilbert_ballIntegral_symm {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (u v : DirichletHilbertSpace (d := d) R hR) :
    (∫ x in sourceBall (0 : Vec d) R,
      ρ x * u.val none x * v.val none x +
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x)) =
    ∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.val none x * u.val none x +
        dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => u.val (some i) x) := by
  apply integral_congr_ae
  exact ae_of_all _ fun x => by
    have hsym : (α x).IsSymm := (h.2.2 x).2.2.1
    have he := hsym.dotProduct_mulVec_comm
      (x := fun i => v.val (some i) x) (y := fun i => u.val (some i) x)
    rw [dotProduct_comm, dotProduct_comm (fun i => u.val (some i) x)] at he
    change ρ x * u.val none x * v.val none x + _ =
      ρ x * v.val none x * u.val none x + _
    change dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) =
      dot ((α x).mulVec (fun i => v.val (some i) x)) (fun i => u.val (some i) x) at he
    rw [he]
    ring

/-- The canonical weighted inclusion has the explicit density bound. -/
theorem dirichletHilbertInclusion_norm_le (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hC : 0 ≤ C) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    ‖dirichletHilbertInclusion ρ R hR C hρ‖ ≤ Real.sqrt C := by
  have hc : ‖cubeToDirichletL2 ρ R hR C hρ‖ ≤ Real.sqrt C := by
    have hb := Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℝ) (p := 2)
      ENNReal.ofReal_ne_top (dirichletVolume_le_cube ρ R hR C hρ)
    change ‖cubeToDirichletL2 ρ R hR C hρ‖ ≤ _ at hb
    simpa only [ENNReal.toReal_ofReal hC, ENNReal.toReal_div, ENNReal.toReal_one,
      ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow] using hb
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg C)
  intro u
  have hu := (hilbertToSobolev_norm_le _ u.val).1
  change ‖cubeToDirichletL2 ρ R hR C hρ ((hilbertToSobolev _ u.val).1)‖ ≤ _
  exact ((cubeToDirichletL2 ρ R hR C hρ).le_opNorm _).trans
    (mul_le_mul hc hu (norm_nonneg _) (Real.sqrt_nonneg C))

/-- The constructed weighted resolvent is compact, self-adjoint and positive,
with a quantitative bound in the original ellipticity constant. -/
theorem exists_compact_selfAdjoint_dirichletHilbert_resolvent (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧ IsSelfAdjoint (J.comp S) ∧
      (∀ f, ‖S f‖ ≤ κ⁻¹ * Real.sqrt κ⁻¹ * ‖f‖) ∧
      (∀ f, 0 ≤ inner ℝ f (J (S f))) ∧
      ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
        u = S f ↔ ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            ρ x * u.val none x * v.val none x +
              dot ((α x).mulVec (fun i => u.val (some i) x))
                (fun i => v.val (some i) x)) = inner ℝ f (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨S, hc, hv⟩ := exists_compact_dirichletHilbert_resolvent hd hκ h R hR
  have he (f : Lp ℝ 2 (dirichletVolume ρ R)) :
      κ * ‖S f‖ ^ 2 ≤ inner ℝ f (J (S f)) :=
    (dirichletHilbert_ballIntegral_coercive hκ h R hR (S f)).trans_eq
      ((hv f (S f)).mp rfl (S f))
  refine ⟨S, hc, ?_, ?_, ?_, hv⟩
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro f g
    change inner ℝ (J (S f)) g = inner ℝ f (J (S g))
    rw [real_inner_comm]
    exact (((hv g (S g)).mp rfl (S f)).symm.trans
      (dirichletHilbert_ballIntegral_symm h R hR (S g) (S f))).trans
        ((hv f (S f)).mp rfl (S g))
  · intro f
    by_cases hz : S f = 0
    · rw [hz, norm_zero]
      positivity
    have hp : 0 < ‖S f‖ := norm_pos_iff.mpr hz
    have hb := (he f).trans ((real_inner_le_norm f (J (S f))).trans
      (mul_le_mul_of_nonneg_left (J.le_opNorm (S f)) (norm_nonneg f)))
    have hJ : ‖J‖ ≤ Real.sqrt κ⁻¹ :=
      dirichletHilbertInclusion_norm_le ρ R hR κ⁻¹ (inv_nonneg.mpr hκ.le)
        (fun x _ => (h.2.2 x).2.1)
    have hl : κ * ‖S f‖ ≤ ‖J‖ * ‖f‖ :=
      (mul_le_mul_iff_right₀ hp).mp (by nlinarith only [hb])
    calc
      ‖S f‖ ≤ (‖J‖ * ‖f‖) / κ := (le_div_iff₀ hκ).mpr (by nlinarith only [hl])
      _ = κ⁻¹ * ‖J‖ * ‖f‖ := by ring
      _ ≤ κ⁻¹ * Real.sqrt κ⁻¹ * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hκ.le))
          (norm_nonneg f)
  · intro f
    exact (mul_nonneg hκ.le (sq_nonneg ‖S f‖)).trans (he f)

/-- The actual weighted ball has finite mass, by its proved domination by
Lebesgue measure on the containing bounded cube. -/
theorem dirichletVolume_isFinite (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    IsFiniteMeasure (dirichletVolume ρ R) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have : IsFiniteMeasure (volume.restrict (Q : Set (SpatialCoordinates d))) := by
    refine isFiniteMeasure_restrict.mpr ?_
    exact measure_ball_lt_top.ne
  refine ⟨lt_of_le_of_lt ((dirichletVolume_le_cube ρ R hR C hρ) Set.univ) ?_⟩
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/-- Each supported smooth test is an element of the completed Dirichlet space. -/
def dirichletSmoothElement (R : ℝ) (hR : 0 < R)
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
    DirichletHilbertSpace (d := d) R hR :=
  ⟨dirichletSmoothData R hR φ,
    (LinearMap.range (dirichletSmoothData R hR)).le_topologicalClosure ⟨φ, rfl⟩⟩

/-- Its inclusion is the same actual smooth function in weighted ball L². -/
theorem dirichletHilbertInclusion_smooth_coe (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
    dirichletHilbertInclusion ρ R hR C hρ (dirichletSmoothElement R hR φ)
      =ᵐ[dirichletVolume ρ R] (φ : Vec d → ℝ) := by
  exact (dirichletHilbertInclusion_coe ρ R hR C hρ _).trans
    ((testL2_coeFn (dirichletTestInCube R hR φ)).filter_mono
      (Measure.absolutelyContinuous_of_le_smul (dirichletVolume_le_cube ρ R hR C hρ)).ae_le)

/-- Orthogonality to the actual supported smooth tests forces a weighted L²
function to vanish. This is the distribution test lemma for the weighted measure. -/
theorem eq_zero_of_inner_dirichletSmoothElement (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      inner ℝ (dirichletHilbertInclusion ρ R hR C hρ
        (dirichletSmoothElement R hR φ)) f = 0) : f = 0 := by
  have := dirichletVolume_isFinite ρ R hR C hρ
  have hz := (dirichletBall (d := d) R).isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrableOn.locallyIntegrableOn
    (fun g hg hgc hgs => ?_)
  · apply Lp.ext
    have hmem : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R :=
      (withDensity_absolutelyContinuous _ _)
        (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
    filter_upwards [hz, hmem, Lp.coeFn_zero ℝ 2 (dirichletVolume ρ R)] with x hx hm h0
    exact (hx hm).trans h0.symm
  · let φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ := ⟨g, hg, hgc, hgs⟩
    rw [← hf φ, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [dirichletHilbertInclusion_smooth_coe ρ R hR C hρ φ] with x hx
    change g x * f x = f x * _
    rw [hx]
    exact mul_comm _ _

/-- The genuine Dirichlet form domain is dense in the exact weighted ball L²
space. No domain-density assumption is supplied. -/
theorem denseRange_dirichletHilbertInclusion (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C) :
    DenseRange (dirichletHilbertInclusion ρ R hR C hρ) := by
  let J := dirichletHilbertInclusion ρ R hR C hρ
  change Dense (Set.range J.toLinearMap)
  rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  apply eq_zero_of_inner_dirichletSmoothElement ρ R hR C hρ f
  intro φ
  exact hf _ ⟨dirichletSmoothElement R hR φ, rfl⟩

/-- The actual compact Dirichlet resolvent has trivial kernel, dense range,
and strictly positive quadratic response for every nonzero loading. -/
theorem exists_compact_injective_dirichletHilbert_resolvent (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧ IsSelfAdjoint (J.comp S) ∧
      Function.Injective (J.comp S) ∧ DenseRange (J.comp S) ∧
      (∀ f, f ≠ 0 → 0 < inner ℝ f (J (S f))) ∧
      (∀ f, ‖S f‖ ≤ κ⁻¹ * Real.sqrt κ⁻¹ * ‖f‖) ∧
      ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
        u = S f ↔ ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            ρ x * u.val none x * v.val none x +
              dot ((α x).mulVec (fun i => u.val (some i) x))
                (fun i => v.val (some i) x)) = inner ℝ f (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨S, hc, hsym, hnorm, _hpos, hv⟩ :=
    exists_compact_selfAdjoint_dirichletHilbert_resolvent hd hκ h R hR
  have hSzero (f : Lp ℝ 2 (dirichletVolume ρ R)) (hz : S f = 0) : f = 0 := by
    apply eq_zero_of_inner_dirichletSmoothElement ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) f
    intro φ
    rw [real_inner_comm]
    have hh := (hv f 0).mp hz.symm (dirichletSmoothElement R hR φ)
    have hAE : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        (0 : DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R)
          (mul_pos two_pos hR))) x = 0 :=
      (Measure.absolutelyContinuous_of_le
        (Measure.restrict_mono_set volume (sourceBall_subset_cube R hR))).ae_le
        (Lp.coeFn_zero ℝ 2 _)
    have hzInt : (∫ x in sourceBall (0 : Vec d) R,
        ρ x * (0 : DirichletHilbertSpace (d := d) R hR).val none x *
            (dirichletSmoothElement R hR φ).val none x +
          dot ((α x).mulVec (fun i =>
            (0 : DirichletHilbertSpace (d := d) R hR).val (some i) x))
            (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hAE] with x hx
      change ρ x * (0 : DomainL2 _) x * _ +
        dot ((α x).mulVec (fun _ => (0 : DomainL2 _) x)) _ = 0
      simp only [hx, mul_zero, zero_mul, Matrix.mulVec, dotProduct, dot,
        Finset.sum_const_zero, zero_add]
    exact hh.symm.trans hzInt
  have he (f : Lp ℝ 2 (dirichletVolume ρ R)) :
      κ * ‖S f‖ ^ 2 ≤ inner ℝ f (J (S f)) :=
    (dirichletHilbert_ballIntegral_coercive hκ h R hR (S f)).trans_eq
      ((hv f (S f)).mp rfl (S f))
  have hinj : Function.Injective (J.comp S) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    change J (S f) = 0 at hf
    have hzero : ‖S f‖ = 0 := by
      have hh := he f
      rw [hf, inner_zero_right] at hh
      exact sq_eq_zero_iff.mp (le_antisymm
        ((mul_le_mul_iff_right₀ hκ).mp (show κ * ‖S f‖ ^ 2 ≤ κ * 0 by
          simpa only [mul_zero] using hh)) (sq_nonneg _))
    exact hSzero f (norm_eq_zero.mp hzero)
  refine ⟨S, hc, hsym, hinj, ?_, ?_, hnorm, hv⟩
  · change Dense (Set.range (J.comp S).toLinearMap)
    rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply hinj
    rw [map_zero]
    apply ext_inner_left ℝ
    intro g
    rw [inner_zero_right]
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsym) g f).symm.trans
      (hf _ ⟨g, rfl⟩)
  · intro f hf
    exact (mul_pos hκ (sq_pos_of_pos (norm_pos_iff.mpr
      (fun hz => hf (hSzero f hz))))).trans_le (he f)

/-- A strictly positive source density makes the literal weighted inclusion
injective: the value determines every coordinate of its weak gradient. -/
theorem injective_dirichletHilbertInclusion {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    Function.Injective
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro u hu
  change dirichletHilbertInclusion ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) u = 0 at hu
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hv : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), u.val none x = 0 := by
    apply hac.ae_le
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) u, Lp.coeFn_zero ℝ 2 (dirichletVolume ρ R)] with x hx hz
    change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ u) x = u.val none x at hx
    rw [hu] at hx
    exact hx.symm.trans hz
  have hv' := (ae_restrict_iff' (dirichletBall (d := d) R).isOpen.measurableSet).mp hv
  have hv0 : u.val none = 0 := by
    apply Lp.ext
    filter_upwards [ae_restrict_of_ae hv',
      dirichletHilbert_coordinate_zero_exterior R hR u none,
      Lp.coeFn_zero ℝ 2 (volume.restrict (Q : Set (SpatialCoordinates d)))] with x hx he hz
    change u.val none x = (0 : DomainL2 Q) x
    rw [hz]
    by_cases hb : x ∈ sourceBall (0 : Vec d) R
    · exact hx hb
    · exact he hb
  have hgraph : (0, fun i => u.val (some i)) ∈ weakSobolevGraph Q := by
    have hh := dirichletHilbert_mem_weakSobolevGraph R hR u
    change (u.val none, fun i => u.val (some i)) ∈ weakSobolevGraph Q at hh
    rwa [hv0] at hh
  have hg := weakSobolevGraph_gradient_eq_zero hgraph
  apply Subtype.ext
  apply PiLp.ext
  intro j
  cases j with
  | none => exact hv0
  | some i => exact congrFun hg i

/-- Extending a graph coordinate by zero from the containing cube gives the
same global representative as extending it from the actual Dirichlet ball. -/
theorem dirichletHilbert_coordinate_zeroExtension (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) (j : Option (Fin d)) :
    (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR) :
      Set (SpatialCoordinates d)).indicator (fun x => u.val j x)
      =ᵐ[volume] (sourceBall (0 : Vec d) R).indicator (fun x => u.val j x) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have he := (ae_restrict_iff' Q.isOpen.measurableSet).mp
    (dirichletHilbert_coordinate_zero_exterior R hR u j)
  filter_upwards [he] with x hx
  by_cases hb : x ∈ sourceBall (0 : Vec d) R
  · simp only [Set.indicator_of_mem hb,
      Set.indicator_of_mem (sourceBall_subset_cube R hR hb)]
  · rw [Set.indicator_of_notMem hb]
    by_cases hq : x ∈ (Q : Set (SpatialCoordinates d))
    · rw [Set.indicator_of_mem hq]
      exact hx hq hb
    · exact Set.indicator_of_notMem hq _

/-- Literal zero extension of the actual value coordinate from the source ball. -/
def dirichletHilbertZeroExtension (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) : Vec d → ℝ :=
  (sourceBall (0 : Vec d) R).indicator (fun x => u.val none x)

/-- Literal zero extension of every actual weak-gradient coordinate. -/
def dirichletHilbertZeroExtensionGrad (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) : Vec d → Vec d :=
  (sourceBall (0 : Vec d) R).indicator (fun x i => u.val (some i) x)

/-- The completed ball-supported Hilbert graph has the genuine global source
weak gradient of its literal zero extension, with all coordinates in L². -/
theorem dirichletHilbert_global_zeroExtension (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    MemLp (dirichletHilbertZeroExtension R hR u) 2 volume ∧
      (∀ i, MemLp (fun x => dirichletHilbertZeroExtensionGrad R hR u x i) 2 volume) ∧
      EinsteinRelation.HasWeakGradient Set.univ (dirichletHilbertZeroExtension R hR u)
        (dirichletHilbertZeroExtensionGrad R hR u) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  obtain ⟨v, hv, hg⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨hilbertToSobolev Q u.val, dirichletHilbert_mem_killedSobolevGraph R hR u⟩)
  have hv' : v.toH1Function.toFun = fun x => u.val none x := hv
  have hg' : v.toH1Function.grad = fun x i => u.val (some i) x := hg
  have hvalue : v.zeroExtension =ᵐ[volume] dirichletHilbertZeroExtension R hR u := by
    change (Q : Set (SpatialCoordinates d)).indicator v.toH1Function.toFun =ᵐ[volume] _
    rw [hv']
    exact dirichletHilbert_coordinate_zeroExtension R hR u none
  have hgrad (i : Fin d) : (fun x => v.zeroExtensionGrad x i) =ᵐ[volume]
      (fun x => dirichletHilbertZeroExtensionGrad R hR u x i) := by
    have he := dirichletHilbert_coordinate_zeroExtension R hR u (some i)
    filter_upwards [he] with x hx
    change ((Q : Set (SpatialCoordinates d)).indicator v.toH1Function.grad) x i =
      ((sourceBall (0 : Vec d) R).indicator (fun x i => u.val (some i) x)) x i
    rw [hg']
    change (Q : Set (SpatialCoordinates d)).indicator (fun x => u.val (some i) x) x =
      (sourceBall (0 : Vec d) R).indicator (fun x => u.val (some i) x) x at hx
    by_cases hq : x ∈ (Q : Set (SpatialCoordinates d)) <;>
      by_cases hb : x ∈ sourceBall (0 : Vec d) R <;>
      simp [hq, hb] at hx ⊢ <;> exact hx
  have hf : MemLp (dirichletHilbertZeroExtension R hR u) 2 volume :=
    (memLp_congr_ae hvalue).mp
      (v.memLp_zeroExtension Q.isOpen.measurableSet v.toH1Function.memL2)
  have hG (i : Fin d) :
      MemLp (fun x => dirichletHilbertZeroExtensionGrad R hR u x i) 2 volume := by
    have hm := v.gradMemLp_zeroExtensionGrad Q.isOpen.measurableSet
      v.toH1Function.gradMemL2 i
    change MemLp (fun x => v.zeroExtensionGrad x i) 2 (volume.restrict Set.univ) at hm
    rw [Measure.restrict_univ] at hm
    exact (memLp_congr_ae (hgrad i)).mp hm
  refine ⟨hf, hG, ?_⟩
  have hw := v.hasWeakGradientOn_univ_zeroExtension Q.isOpen.measurableSet
  intro i
  refine ⟨(hf.locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ,
    ((hG i).locallyIntegrable (by norm_num)).locallyIntegrableOn Set.univ, ?_⟩
  intro φ hφ
  calc
    (∫ x in Set.univ, dirichletHilbertZeroExtension R hR u x *
        coordinateDerivative i φ x) =
        ∫ x in Set.univ, v.zeroExtension x * coordinateDerivative i φ x := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hvalue] with x hx
      rw [hx]
    _ = -(∫ x in Set.univ, v.zeroExtensionGrad x i * φ x) := by
      simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
        hw i φ hφ.1 hφ.2.1 hφ.2.2
    _ = -(∫ x in Set.univ, dirichletHilbertZeroExtensionGrad R hR u x i * φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (hgrad i)] with x hx
      rw [hx]

/-- The global zero-extension gradient retains the paper's Euclidean norm
and is square integrable in that norm. -/
theorem dirichletHilbert_zeroExtension_euclideanNorm_memLp (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    MemLp (fun x => euclideanNorm (dirichletHilbertZeroExtensionGrad R hR u x))
      2 volume := by
  have hp : MemLp (fun x => (WithLp.toLp 2
      (dirichletHilbertZeroExtensionGrad R hR u x) : EuclideanSpace ℝ (Fin d)))
      2 volume :=
    memLp_piLp_iff.mpr (dirichletHilbert_global_zeroExtension R hR u).2.1
  simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using hp.norm

/-- The actual zero-boundary Hilbert graph satisfies a scalar Poincaré
inequality in every source dimension, including dimension two. -/
theorem exists_dirichletHilbert_poincare (hd : 2 ≤ d) (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : DirichletHilbertSpace (d := d) R hR,
      ‖u.val none‖ ≤ C * ∑ i : Fin d, ‖u.val (some i)‖ := by
  haveI : NeZero d := ⟨by omega⟩
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  have hQ : Homogenization.IsOpenBoundedConvexDomain (Q : Set (Vec d)) :=
    Homogenization.isOpenBoundedConvexDomain_ball _ (by positivity)
  obtain ⟨C, hC, hP⟩ :=
    Homogenization.H10Function.exists_poincare_constant_of_isOpenBoundedConvexDomain hQ
  refine ⟨C, hC, ?_⟩
  intro u
  obtain ⟨v, hv, hg⟩ := exists_nativeH10Function_of_killedSobolevGraph
    (⟨hilbertToSobolev Q u.val, dirichletHilbert_mem_killedSobolevGraph R hR u⟩)
  have hv' : v.toH1Function.toFun = fun x => u.val none x := hv
  have hg' : v.toH1Function.grad = fun x i => u.val (some i) x := hg
  have hvalue : v.toH1Function.toScalarL2 = u.val none := by
    apply Lp.ext
    have hh := v.toH1Function.coeFn_toScalarL2
    change v.toH1Function.toScalarL2 =ᵐ[volume.restrict (Q : Set (Vec d))]
      v.toH1Function.toFun at hh
    rwa [hv'] at hh
  have hgrad (i : Fin d) : v.toH1Function.gradCoordToScalarL2 i = u.val (some i) := by
    apply Lp.ext
    have hh := v.toH1Function.coeFn_gradCoordToScalarL2 i
    change v.toH1Function.gradCoordToScalarL2 i =ᵐ[volume.restrict (Q : Set (Vec d))]
      (fun x => v.toH1Function.grad x i) at hh
    rwa [hg'] at hh
  have hb := hP v
  change ‖v.toH1Function.toScalarL2‖ ≤ C * ∑ i : Fin d,
    ‖v.toH1Function.gradCoordToScalarL2 i‖ at hb
  simpa only [hvalue, hgrad] using hb

/-- Zero gradient in the actual zero-boundary graph forces the whole datum
to vanish; this uses the proved Poincaré inequality, also when d = 2. -/
theorem dirichletHilbert_eq_zero_of_gradient_eq_zero (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (hg : ∀ i : Fin d, u.val (some i) = 0) : u = 0 := by
  obtain ⟨C, _hC, hP⟩ := exists_dirichletHilbert_poincare hd R hR
  have hb := hP u
  simp only [hg, norm_zero, Finset.sum_const_zero, mul_zero] at hb
  have hv : u.val none = 0 := norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  apply Subtype.ext
  apply PiLp.ext
  intro j
  cases j with
  | none => exact hv
  | some i => exact hg i

/-- The Euclidean sum of squared gradient-coordinate L² norms controls the
entire actual Dirichlet Hilbert norm, with a positive geometric constant. -/
theorem exists_dirichletHilbert_gradient_coercivity (hd : 2 ≤ d)
    (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : DirichletHilbertSpace (d := d) R hR,
      ‖u‖ ^ 2 ≤ C * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by
  obtain ⟨C, _hC, hP⟩ := exists_dirichletHilbert_poincare hd R hR
  refine ⟨1 + (d : ℝ) * C ^ 2, by positivity, ?_⟩
  intro u
  have hcs : (∑ i : Fin d, ‖u.val (some i)‖) ^ 2 ≤
      (d : ℝ) * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin d => ‖u.val (some i)‖))
  have hv := pow_le_pow_left₀ (norm_nonneg (u.val none)) (hP u) 2
  rw [mul_pow] at hv
  calc
    ‖u‖ ^ 2 = ‖u.val none‖ ^ 2 + ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 :=
      dirichletHilbert_norm_sq R hR u
    _ ≤ C ^ 2 * ((d : ℝ) * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2) +
        ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 :=
      add_le_add (hv.trans (mul_le_mul_of_nonneg_left hcs (sq_nonneg C))) le_rfl
    _ = (1 + (d : ℝ) * C ^ 2) * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by ring

/-- Poincaré and the literal source ellipticity make the pure Dirichlet energy
coercive on the completed zero-boundary space, without a mass shift. -/
theorem exists_dirichletHilbert_energyForm (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ c : ℝ, 0 < c ∧ ∃ B : DirichletHilbertSpace (d := d) R hR →L[ℝ]
        DirichletHilbertSpace (d := d) R hR →L[ℝ] ℝ,
      (∀ u, c * ‖u‖ ^ 2 ≤ B u u) ∧
      ∀ u v, B u v = ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => v.val (some i) x) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let a := dirichletValueGradientMatrix (fun _ : Vec d => 0) α
  have ha (i j : Option (Fin d)) : AEStronglyMeasurable (fun x => a x i j) μ := by
    cases i with
    | none => cases j <;> exact aestronglyMeasurable_const
    | some i => cases j with
      | none => exact aestronglyMeasurable_const
      | some j => exact dirichletValueGradientMatrix_aestronglyMeasurable h μ (some i) (some j)
  have hb : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ κ⁻¹ := by
    apply ae_of_all
    intro x i j
    cases i with
    | none => cases j <;> simpa only [a, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
    | some i => cases j with
      | none => simpa only [a, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
      | some j => exact dirichletValueGradientMatrix_bound hκ h x (some i) (some j)
  obtain ⟨D, hD⟩ := exists_coordinateL2Form μ a ha (inv_nonneg.mpr hκ.le) hb
  let S := (dirichletHilbertSubmodule (d := d) R hR).subtypeL
  let B := D.bilinearComp S S
  obtain ⟨C, hC, hP⟩ := exists_dirichletHilbert_gradient_coercivity hd R hR
  have hquad (x : Vec d) (u : Option (Fin d) → ℝ) :
      κ * (∑ i : Fin d, u (some i) ^ 2) ≤ ∑ i, ∑ j, a x i j * u j * u i := by
    rw [dirichletValueGradientMatrix_sum]
    simp only [zero_mul, zero_add]
    have hg := ((h.2.2 x).2.2.2 (fun i => u (some i))).1
    change κ * (∑ i, u (some i) * u (some i)) ≤
      dotProduct (fun i => u (some i)) ((α x).mulVec (fun i => u (some i))) at hg
    rw [dotProduct_comm] at hg
    simpa only [dot, dotProduct, ← pow_two] using hg
  refine ⟨κ / C, div_pos hκ hC, B, ?_, ?_⟩
  · intro u
    let g : PiLp 2 (fun _ : Fin d => Lp ℝ 2 μ) := WithLp.toLp 2 (fun i => u.val (some i))
    have hi := integrable_coordinateL2Form μ a ha hb u.val u.val
    have hs : Integrable (fun x => ∑ i : Fin d, u.val (some i) x ^ 2) μ :=
      integrable_finsetSum Finset.univ (fun i _ => (Lp.memLp (u.val (some i))).integrable_sq)
    have hbound := integral_mono (hs.const_mul κ) hi
      (fun x => hquad x (fun j => u.val j x))
    have hn : (∫ x, ∑ i : Fin d, u.val (some i) x ^ 2 ∂μ) =
        ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by
      change (∫ x, ∑ i, g i x ^ 2 ∂μ) = _
      rw [integral_coordinateL2_norm_sq, PiLp.norm_sq_eq_of_L2]
    rw [integral_const_mul, hn] at hbound
    have he : B u u = ∫ x, ∑ i, ∑ j, a x i j * u.val j x * u.val i x ∂μ := hD u.val u.val
    rw [he]
    calc
      κ / C * ‖u‖ ^ 2 ≤ κ * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by
        have hp := mul_le_mul_of_nonneg_left (hP u) (div_nonneg hκ.le hC.le)
        calc
          κ / C * ‖u‖ ^ 2 ≤ κ / C * (C * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2) := hp
          _ = κ * ∑ i : Fin d, ‖u.val (some i)‖ ^ 2 := by field_simp
      _ ≤ _ := hbound
  · intro u v
    change D u.val v.val = _
    rw [hD]
    have he := integral_congr_ae (μ := μ) (ae_of_all μ fun x =>
      dirichletValueGradientMatrix_sum (fun _ : Vec d => 0) α x
        (fun j => u.val j x) (fun j => v.val j x))
    have hball := dirichletHilbert_integral_eq_ball (fun _ : Vec d => 0) α R hR u v
    simpa only [zero_mul, zero_add] using he.trans hball

/-- The unshifted inverse of the actual source Dirichlet energy is compact,
self-adjoint, injective, and strictly positive, with dense weighted-L² range.
Its defining equation contains no zeroth-order mass term. -/
theorem exists_compact_dirichletHilbert_energyInverse (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ c : ℝ, 0 < c ∧
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧ IsSelfAdjoint (J.comp S) ∧
      Function.Injective (J.comp S) ∧ DenseRange (J.comp S) ∧
      (∀ f, f ≠ 0 → 0 < inner ℝ f (J (S f))) ∧
      (∀ f, ‖S f‖ ≤ c⁻¹ * Real.sqrt κ⁻¹ * ‖f‖) ∧
      ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
        u = S f ↔ ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => u.val (some i) x))
              (fun i => v.val (some i) x)) = inner ℝ f (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨c, hc, B, hbound, hform⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  have hB : IsCoercive B := ⟨c, hc, fun u => by
    simpa only [pow_two, mul_assoc] using hbound u⟩
  let E := hB.continuousLinearEquivOfBilin
  let S := E.symm.toContinuousLinearMap.comp J.adjoint
  have heq (f : Lp ℝ 2 (dirichletVolume ρ R))
      (v : DirichletHilbertSpace (d := d) R hR) : B (S f) v = inner ℝ f (J v) := by
    rw [← hB.continuousLinearEquivOfBilin_apply]
    change inner ℝ (E (E.symm (J.adjoint f))) v = _
    rw [E.apply_symm_apply]
    exact J.adjoint_inner_left v f
  have hsymm (u v : DirichletHilbertSpace (d := d) R hR) : B u v = B v u := by
    rw [hform, hform]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have hsym : (α x).IsSymm := (h.2.2 x).2.2.1
      have he := hsym.dotProduct_mulVec_comm
        (x := fun i => v.val (some i) x) (y := fun i => u.val (some i) x)
      rw [dotProduct_comm, dotProduct_comm (fun i => u.val (some i) x)] at he
      exact he
  have hSzero (f : Lp ℝ 2 (dirichletVolume ρ R)) (hz : S f = 0) : f = 0 := by
    apply eq_zero_of_inner_dirichletSmoothElement ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) f
    intro φ
    rw [real_inner_comm, ← heq f (dirichletSmoothElement R hR φ), hz, map_zero,
      zero_apply]
  have hSinj : Function.Injective S := by
    apply LinearMap.ker_eq_bot.mp
    exact LinearMap.ker_eq_bot'.mpr hSzero
  have hinj : Function.Injective (J.comp S) :=
    (injective_dirichletHilbertInclusion hκ h R hR).comp hSinj
  have hsa : IsSelfAdjoint (J.comp S) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro f g
    change inner ℝ (J (S f)) g = inner ℝ f (J (S g))
    rw [real_inner_comm, ← heq g (S f), hsymm, heq]
  have he (f : Lp ℝ 2 (dirichletVolume ρ R)) :
      c * ‖S f‖ ^ 2 ≤ inner ℝ f (J (S f)) := (hbound (S f)).trans_eq (heq f (S f))
  refine ⟨c, hc, S, ?_, hsa, hinj, ?_, ?_, ?_, ?_⟩
  · exact (isCompactOperator_dirichletHilbertInclusion hd ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1)).comp_clm S
  · change Dense (Set.range (J.comp S).toLinearMap)
    rw [← LinearMap.coe_range, Submodule.dense_iff_topologicalClosure_eq_top,
      Submodule.topologicalClosure_eq_top_iff]
    apply (Submodule.eq_bot_iff _).mpr
    intro f hf
    apply hinj
    rw [map_zero]
    apply ext_inner_left ℝ
    intro g
    rw [inner_zero_right]
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hsa) g f).symm.trans
      (hf _ ⟨g, rfl⟩)
  · intro f hf
    exact (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr
      (fun hz => hf (hSzero f hz))))).trans_le (he f)
  · intro f
    by_cases hz : S f = 0
    · rw [hz, norm_zero]
      positivity
    have hp : 0 < ‖S f‖ := norm_pos_iff.mpr hz
    have hb := (he f).trans ((real_inner_le_norm f (J (S f))).trans
      (mul_le_mul_of_nonneg_left (J.le_opNorm (S f)) (norm_nonneg f)))
    have hJ : ‖J‖ ≤ Real.sqrt κ⁻¹ :=
      dirichletHilbertInclusion_norm_le ρ R hR κ⁻¹ (inv_nonneg.mpr hκ.le)
        (fun x _ => (h.2.2 x).2.1)
    have hl : c * ‖S f‖ ≤ ‖J‖ * ‖f‖ :=
      (mul_le_mul_iff_right₀ hp).mp (by nlinarith only [hb])
    calc
      ‖S f‖ ≤ (‖J‖ * ‖f‖) / c := (le_div_iff₀ hc).mpr (by nlinarith only [hl])
      _ = c⁻¹ * ‖J‖ * ‖f‖ := by ring
      _ ≤ c⁻¹ * Real.sqrt κ⁻¹ * ‖f‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (inv_nonneg.mpr hc.le))
          (norm_nonneg f)
  · intro f u
    constructor
    · rintro rfl v
      rw [← hform]
      exact heq f v
    · intro hu
      have hv : J.adjoint f = E u := hB.unique_continuousLinearEquivOfBilin
        (fun v => (J.adjoint_inner_left v f).trans ((hu v).symm.trans (hform u v).symm))
      change u = E.symm (J.adjoint f)
      rw [hv, E.symm_apply_apply]

/-- Pairing with an actual supported smooth test is its literal density-weighted
Lebesgue integral; the weighted Hilbert measure is not replaced. -/
theorem dirichletHilbertInclusion_inner_smooth {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (f : Lp ℝ 2 (dirichletVolume ρ R))
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
    inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (dirichletSmoothElement R hR φ)) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * f x * φ x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, f x * φ x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [dirichletHilbertInclusion_smooth_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) φ] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx]
      exact mul_comm _ _
    _ = _ := by
      change (∫ x, f x * φ x ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
        ring

/-- The gradient coordinate of an actual smooth Dirichlet test is the original
Fréchet derivative against the source Euclidean coordinate vector. -/
theorem dirichletHilbert_energyIntegral_smooth (α : Vec d → Mat d)
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
    (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) =
    ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i)) := by
  have hg : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), ∀ i : Fin d,
      (dirichletSmoothElement R hR φ).val (some i) x =
        fderiv ℝ (φ : Vec d → ℝ) x (unitVector i) := by
    apply ae_all_iff.mpr
    intro i
    have ht := (Measure.absolutelyContinuous_of_le
      (Measure.restrict_mono_set volume (sourceBall_subset_cube R hR))).ae_le
        (testPartialL2_coeFn (dirichletTestInCube R hR φ) i)
    change (fun x => (testPartialL2 (dirichletTestInCube R hR φ) i) x)
      =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        (fun x => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))
    exact ht
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [funext hx]

/-- The original ball-supported smooth tests are dense in the completed
Dirichlet space. -/
theorem denseRange_dirichletSmoothElement (R : ℝ) (hR : 0 < R) :
    DenseRange (dirichletSmoothElement (d := d) R hR) := by
  rw [DenseRange, Subtype.dense_iff]
  change (dirichletHilbertSubmodule (d := d) R hR : Set _) ⊆
    closure ((fun z : DirichletHilbertSpace (d := d) R hR => z.val) ''
      Set.range (dirichletSmoothElement (d := d) R hR))
  have himage : (fun z : DirichletHilbertSpace (d := d) R hR => z.val) '' Set.range (dirichletSmoothElement (d := d) R hR) =
      Set.range (dirichletSmoothData (d := d) R hR) := by
    ext x
    constructor
    · rintro ⟨y, ⟨φ, rfl⟩, rfl⟩
      exact ⟨φ, rfl⟩
    · rintro ⟨φ, rfl⟩
      exact ⟨dirichletSmoothElement R hR φ, ⟨φ, rfl⟩, rfl⟩
  rw [himage]
  intro x hx
  exact hx

/-- A weak eigenfunction equation on supported smooth tests extends to the
entire completed Dirichlet space by continuity of the actual energy form. -/
theorem dirichletHilbert_weakEquation_of_smooth (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) (eig : ℝ)
    (hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u)
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) (dirichletSmoothElement R hR φ))) :
    ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u)
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) w) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨c, hc, B, hB, hform⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  have hclosed : IsClosed {w : DirichletHilbertSpace (d := d) R hR |
      B u w = eig * inner ℝ (J u) (J w)} :=
    isClosed_eq (B u).continuous ((continuous_const.inner J.continuous).const_mul eig)
  have hsub : Set.range (dirichletSmoothElement (d := d) R hR) ⊆
      {w : DirichletHilbertSpace (d := d) R hR | B u w = eig * inner ℝ (J u) (J w)} := by
    rintro w ⟨φ, rfl⟩
    change B u (dirichletSmoothElement R hR φ) =
      eig * inner ℝ (J u) (J (dirichletSmoothElement R hR φ))
    rw [hform]
    exact hweak φ
  intro w
  rw [← hform]
  exact closure_minimal hsub hclosed (denseRange_dirichletSmoothElement R hR w)

/-- Every weighted L² loading has a genuine zero-boundary weak solution for
the actual unshifted source operator, in all dimensions at least two. -/
theorem exists_dirichletHilbert_sourceSolution (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      EinsteinRelation.HasWeakGradient Set.univ (dirichletHilbertZeroExtension R hR u)
        (dirichletHilbertZeroExtensionGrad R hR u) ∧
      ∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall (0 : Vec d) R) ψ →
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => fderiv ℝ ψ x (unitVector i))) =
        ∫ x in sourceBall (0 : Vec d) R, ρ x * f x * ψ x := by
  obtain ⟨_c, _hc, S, _hcomp, _hsa, _hinj, _hdense, _hpos, _hnorm, hvar⟩ :=
    exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  refine ⟨S f, (dirichletHilbert_global_zeroExtension R hR (S f)).2.2, ?_⟩
  intro ψ hψ
  let φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ := ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
  exact (dirichletHilbert_energyIntegral_smooth α R hR (S f) φ).symm.trans
    (((hvar f (S f)).mp rfl (dirichletSmoothElement R hR φ)).trans
      (dirichletHilbertInclusion_inner_smooth hκ h R hR f φ))

/-! Generic Hilbert-space spectral construction, adapted from the checked
SubdiffusiveProcess.Paper compact-positive-inverse proof without its paper imports. -/
namespace CompactSpectrum

/-- Normalize a vector by its norm, with the zero vector mapped to zero. -/
def spectralUnit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (x : H) : H := ‖x‖⁻¹ • x

theorem spectralUnit_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖spectralUnit x‖ = 1 := by
  simp only [spectralUnit, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem spectralUnit_recover {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) : ‖x‖ • spectralUnit x = x := by
  rw [spectralUnit, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx), one_smul]

theorem spectralUnit_inner {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {x : H} (hx : x ≠ 0) :
    inner ℝ x (spectralUnit x) = ‖x‖ := by
  rw [spectralUnit, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hn]

theorem aux_spectral_norm_le_of_unit_tests
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (x : H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ y : H, ‖y‖ = 1 → inner ℝ x y ≤ C) : ‖x‖ ≤ C := by
  by_cases hx : x = 0
  · simpa only [hx, norm_zero] using! hC
  · have hh := h (spectralUnit x) (spectralUnit_norm hx)
    rwa [spectralUnit_inner hx] at hh

theorem aux_spectral_opNorm_le_of_unit_tests
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x y : H, ‖x‖ = 1 → ‖y‖ = 1 → inner ℝ (T x) y ≤ C) :
    ‖T‖ ≤ C := by
  apply T.opNorm_le_bound hC
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hunit : ‖T (spectralUnit x)‖ ≤ C :=
      aux_spectral_norm_le_of_unit_tests _ C hC
        (fun y hy => h (spectralUnit x) y (spectralUnit_norm hx) hy)
    have hTx : T x = ‖x‖ • T (spectralUnit x) := by
      rw [← map_smul, spectralUnit_recover hx]
    calc
      ‖T x‖ = ‖x‖ * ‖T (spectralUnit x)‖ := by
        rw [hTx, norm_smul, norm_norm]
      _ ≤ ‖x‖ * C := mul_le_mul_of_nonneg_left hunit (norm_nonneg _)
      _ = C * ‖x‖ := mul_comm _ _

theorem aux_spectral_quadratic_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (c : ℝ) (x : H) :
    inner ℝ (T (c • x)) (c • x) = c ^ 2 * inner ℝ (T x) x := by
  rw [map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

/-- The real polarization argument needed for the extremal Rayleigh value. -/
theorem aux_spectral_opNorm_le_of_quadratic_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ x : H, ‖x‖ = 1 → |inner ℝ (T x) x| ≤ C) : ‖T‖ ≤ C := by
  have hall (x : H) : |inner ℝ (T x) x| ≤ C * ‖x‖ ^ 2 := by
    by_cases hx : x = 0
    · simp [hx]
    · have hs := aux_spectral_quadratic_smul T ‖x‖ (spectralUnit x)
      rw [spectralUnit_recover hx] at hs
      rw [hs, abs_mul, abs_of_nonneg (sq_nonneg _)]
      calc
        ‖x‖ ^ 2 * |inner ℝ (T (spectralUnit x)) (spectralUnit x)|
            ≤ ‖x‖ ^ 2 * C :=
          mul_le_mul_of_nonneg_left (h _ (spectralUnit_norm hx)) (sq_nonneg _)
        _ = C * ‖x‖ ^ 2 := mul_comm _ _
  apply aux_spectral_opNorm_le_of_unit_tests T C hC
  intro x y hx hy
  have hs : inner ℝ (T y) x = inner ℝ (T x) y :=
    (hT.isSymmetric y x).trans (real_inner_comm (T x) y)
  have hpolar :
      inner ℝ (T (x + y)) (x + y) - inner ℝ (T (x - y)) (x - y) =
        4 * inner ℝ (T x) y := by
    simp only [map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right]
    rw [hs]
    ring
  have hp := (abs_le.mp (hall (x + y))).2
  have hm := (abs_le.mp (hall (x - y))).1
  have hpar := parallelogram_law_with_norm ℝ x y
  rw [hx, hy] at hpar
  have hparC := congrArg (fun t : ℝ => C * t) hpar
  nlinarith [hparC]

theorem aux_spectral_near_extremum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (ε : ℝ) (hε : 0 < ε) (hεT : ε < ‖T‖) :
    ∃ x : H, ‖x‖ = 1 ∧ ‖T‖ - ε < |inner ℝ (T x) x| := by
  classical
  by_contra h
  push Not at h
  have hbound := aux_spectral_opNorm_le_of_quadratic_bound T hT
    (‖T‖ - ε) (by linarith) h
  linarith

theorem aux_spectral_residual_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (μ : ℝ) (x : H) :
    ‖T x - μ • x‖ ^ 2 =
      ‖T x‖ ^ 2 - 2 * μ * inner ℝ (T x) x + μ ^ 2 * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm (T x) x]
  ring

/-- Compactness supplies attainment of the extremal absolute Rayleigh value. -/
theorem aux_exists_eigenvector_of_compact_selfAdjoint {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : H →L[ℝ] H) (hT : IsSelfAdjoint T)
    (hc : IsCompactOperator T) (hne : T ≠ 0) :
    ∃ (μ : ℝ) (e : H),
      (μ = ‖T‖ ∨ μ = -‖T‖) ∧ ‖e‖ = 1 ∧ T e = μ • e := by
  classical
  have hTpos : 0 < ‖T‖ := norm_pos_iff.mpr hne
  let ε : ℕ → ℝ := fun n => ‖T‖ / ((n : ℝ) + 2)
  have heps (n : ℕ) : 0 < ε n ∧ ε n < ‖T‖ := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    constructor
    · exact div_pos hTpos (by linarith)
    · apply (div_lt_iff₀ (by linarith : (0 : ℝ) < n + 2)).mpr
      have hmul : 0 ≤ ‖T‖ * (n : ℝ) := mul_nonneg hTpos.le hn
      nlinarith only [hTpos, hmul]
  choose x hx hnear using fun n => aux_spectral_near_extremum T hT (ε n)
    (heps n).1 (heps n).2
  let q : ℕ → ℝ := fun n => inner ℝ (T (x n)) (x n)
  have hup (n : ℕ) : |q n| ≤ ‖T‖ := by
    calc
      |q n| ≤ ‖T (x n)‖ * ‖x n‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖x n‖) * ‖x n‖ :=
        mul_le_mul_of_nonneg_right (T.le_opNorm _) (norm_nonneg _)
      _ = ‖T‖ := by rw [hx]; ring
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) hnat
  have hepslim : Tendsto ε atTop (𝓝 (0 : ℝ)) := by
    simpa only [ε, div_eq_mul_inv, mul_zero] using!
      (tendsto_inv_atTop_zero.comp hden).const_mul ‖T‖
  have hcomp : IsCompact (closure (T '' Metric.closedBall (0 : H) 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := T.toLinearMap) hc 1
  have himg (n : ℕ) : T (x n) ∈ closure (T '' Metric.closedBall (0 : H) 1) := by
    apply subset_closure
    refine ⟨x n, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, hx] using!
      (le_rfl : (1 : ℝ) ≤ 1)
  obtain ⟨z, hz, φ, hφ, hTx⟩ := hcomp.tendsto_subseq himg
  have hqmem (n : ℕ) : q (φ n) ∈ Set.Icc (-‖T‖) ‖T‖ := abs_le.mp (hup _)
  obtain ⟨μ, hμmem, ψ, hψ, hq⟩ := isCompact_Icc.tendsto_subseq hqmem
  let σ : ℕ → ℕ := φ ∘ ψ
  have hσ : StrictMono σ := hφ.comp hψ
  have hTxσ : Tendsto (fun n => T (x (σ n))) atTop (𝓝 z) := hTx.comp hψ.tendsto_atTop
  have hqσ : Tendsto (fun n => q (σ n)) atTop (𝓝 μ) := hq
  have hupper : |μ| ≤ ‖T‖ :=
    le_of_tendsto hqσ.abs (Filter.Eventually.of_forall (fun n => hup (σ n)))
  have hlowerlim : Tendsto (fun n => ‖T‖ - ε (σ n)) atTop (𝓝 ‖T‖) := by
    simpa only [sub_zero] using!
      (tendsto_const_nhds.sub (hepslim.comp hσ.tendsto_atTop))
  have hlower : ‖T‖ ≤ |μ| := le_of_tendsto_of_tendsto hlowerlim hqσ.abs
    (Filter.Eventually.of_forall (fun n => (hnear (σ n)).le))
  have habs : |μ| = ‖T‖ := le_antisymm hupper hlower
  have hμsq : μ ^ 2 = ‖T‖ ^ 2 := by
    calc
      μ ^ 2 = |μ| ^ 2 := (sq_abs μ).symm
      _ = ‖T‖ ^ 2 := congrArg (fun t : ℝ => t ^ 2) habs
  have hμne : μ ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at habs
    linarith
  have hsign : μ = ‖T‖ ∨ μ = -‖T‖ := by
    by_cases hμ : 0 ≤ μ
    · left
      simpa only [abs_of_nonneg hμ] using! habs
    · right
      rw [abs_of_neg (lt_of_not_ge hμ)] at habs
      linarith
  let r : ℕ → H := fun n => T (x (σ n)) - μ • x (σ n)
  have hres (n : ℕ) : ‖r n‖ ^ 2 ≤ 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n) := by
    have hnorm : ‖T (x (σ n))‖ ≤ ‖T‖ := by
      simpa only [hx, mul_one] using! T.le_opNorm (x (σ n))
    have hsq : ‖T (x (σ n))‖ ^ 2 ≤ ‖T‖ ^ 2 := by
      simpa only [pow_two] using!
        mul_le_mul hnorm hnorm (norm_nonneg _) (norm_nonneg T)
    change ‖T (x (σ n)) - μ • x (σ n)‖ ^ 2 ≤ _
    rw [aux_spectral_residual_sq, hx]
    dsimp [q]
    nlinarith only [hsq, hμsq]
  have hboundlim : Tendsto
      (fun n => 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n)) atTop (𝓝 (0 : ℝ)) := by
    have h : Tendsto
        (fun n => 2 * ‖T‖ ^ 2 - 2 * μ * q (σ n)) atTop
        (𝓝 (2 * ‖T‖ ^ 2 - 2 * μ * μ)) :=
      tendsto_const_nhds.sub (hqσ.const_mul (2 * μ))
    have hzero : 2 * ‖T‖ ^ 2 - 2 * μ * μ = 0 := by nlinarith [hμsq]
    simpa only [hzero] using! h
  have hrsq : Tendsto (fun n => ‖r n‖ ^ 2) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => sq_nonneg _) hres hboundlim
  have hrnorm : Tendsto (fun n => ‖r n‖) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hrsq
    rw [Real.sqrt_zero] at h
    refine h.congr fun n => ?_
    simp only [Function.comp, Real.sqrt_sq_eq_abs, abs_norm]
  have hr : Tendsto r atTop (𝓝 (0 : H)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero] using! hrnorm
  have hscaled : Tendsto (fun n => μ • x (σ n)) atTop (𝓝 z) := by
    have h := hTxσ.sub hr
    have hid (n : ℕ) : T (x (σ n)) - r n = μ • x (σ n) := by
      dsimp [r]
      abel
    simpa only [hid, sub_zero] using! h
  let e : H := μ⁻¹ • z
  have hxlim : Tendsto (fun n => x (σ n)) atTop (𝓝 e) := by
    simpa only [smul_smul, inv_mul_cancel₀ hμne, one_smul] using!
      hscaled.const_smul μ⁻¹
  have hnorme : ‖e‖ = 1 := by
    apply tendsto_nhds_unique hxlim.norm
    simp only [hx]
    exact tendsto_const_nhds
  have hTe : T e = z :=
    tendsto_nhds_unique ((T.continuous.tendsto e).comp hxlim) hTxσ
  have hμe : μ • e = z := by
    dsimp [e]
    rw [smul_smul, mul_inv_cancel₀ hμne, one_smul]
  exact ⟨μ, e, hsign, hnorme, hTe.trans hμe.symm⟩

/-- A finite-dimensional invariant subspace already selected by the recursion. -/
structure SpectralStage {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) where
  /-- The invariant subspace spanned by the previously selected eigenvectors. -/
  space : Submodule ℝ H
  finite : FiniteDimensional ℝ space
  invariant : ∀ x ∈ space, G x ∈ space

/-- The maximal eigenvector chosen on the orthogonal complement of a stage. -/
structure SpectralPick {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) (P : Submodule ℝ H) where
  /-- The positive eigenvalue maximal on the remaining orthogonal complement. -/
  value : ℝ
  /-- A normalized eigenvector in the remaining orthogonal complement. -/
  vector : H
  value_pos : 0 < value
  vector_norm : ‖vector‖ = 1
  vector_orth : vector ∈ P.orthogonal
  eigen : G vector = value • vector
  bound : ∀ x ∈ P.orthogonal, ‖G x‖ ≤ value * ‖x‖

theorem aux_spectral_pick_exists
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H) (hG : IsSelfAdjoint G) (hc : IsCompactOperator G)
    (hpos : ∀ x, 0 ≤ inner ℝ (G x) x) (hinj : Function.Injective G)
    (hinf : ¬ FiniteDimensional ℝ H) (P : SpectralStage G) :
    Nonempty (SpectralPick G P.space) := by
  classical
  let : FiniteDimensional ℝ P.space := P.finite
  let Q : Submodule ℝ H := P.space.orthogonal
  have hQne : Q ≠ ⊥ := by
    intro hQ
    have htop : P.space = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hQ
    have hsurj : Function.Surjective P.space.subtype := by
      intro x
      refine ⟨⟨x, ?_⟩, rfl⟩
      rw [htop]
      trivial
    exact hinf (FiniteDimensional.of_surjective P.space.subtype hsurj)
  have hQi : ∀ x ∈ Q, G x ∈ Q := by
    intro x hx y hy
    calc
      inner ℝ y (G x) = inner ℝ (G y) x := (hG.isSymmetric y x).symm
      _ = 0 := hx (G y) (P.invariant y hy)
  let T : Q →L[ℝ] Q :=
    (G.toLinearMap.restrict hQi).mkContinuous ‖G‖ (by
      intro x
      exact G.le_opNorm x.1)
  have hTc : IsCompactOperator T :=
    IsCompactOperator.restrict' (f := G.toLinearMap) hc hQi
  have hTsym : T.toLinearMap.IsSymmetric := by
    intro x y
    exact hG.isSymmetric x.1 y.1
  have hTsa : IsSelfAdjoint T := hTsym.isSelfAdjoint
  have hTne : T ≠ 0 := by
    intro hT
    have hQzero : Q ≤ ⊥ := by
      intro x hx
      rw [Submodule.mem_bot]
      apply hinj
      have h := congrArg (fun S : Q →L[ℝ] Q => (S ⟨x, hx⟩).1) hT
      simpa only [map_zero] using! h
    exact hQne (le_antisymm hQzero bot_le)
  obtain ⟨ν, e, hν, he, hTe⟩ :=
    aux_exists_eigenvector_of_compact_selfAdjoint T hTsa hTc hTne
  have hTnorm : 0 < ‖T‖ := by
    rcases (norm_nonneg T).lt_or_eq with h | h
    · exact h
    · exact absurd (ContinuousLinearMap.opNorm_zero_iff T |>.mp h.symm) hTne
  have hνnonneg : 0 ≤ ν := by
    have h := hpos e.1
    have hval : G e.1 = ν • e.1 := congrArg Subtype.val hTe
    rw [hval, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    have heval : ‖e.1‖ = 1 := he
    simpa only [heval, one_pow, mul_one] using! h
  have hνeq : ν = ‖T‖ := by
    rcases hν with hν | hν
    · exact hν
    · exfalso
      linarith
  refine ⟨{
    value := ν
    vector := e.1
    value_pos := by rw [hνeq]; exact hTnorm
    vector_norm := he
    vector_orth := e.2
    eigen := congrArg Subtype.val hTe
    bound := ?_ }⟩
  intro x hx
  have h := T.le_opNorm (⟨x, hx⟩ : Q)
  change ‖G x‖ ≤ ‖T‖ * ‖x‖ at h
  rwa [← hνeq] at h

/-- The initial stage has no selected eigenvectors. -/
def spectralInitial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H) : SpectralStage G where
  space := ⊥
  finite := inferInstance
  invariant := by
    intro x hx
    rw [Submodule.mem_bot] at hx ⊢
    simp only [hx, map_zero]

/-- Add the chosen eigenvector to a finite invariant stage. -/
def spectralEnlarge {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (G : H →L[ℝ] H)
    (P : SpectralStage G) (s : SpectralPick G P.space) : SpectralStage G where
  space := P.space ⊔ Submodule.span ℝ {s.vector}
  finite := by
    let : FiniteDimensional ℝ P.space := P.finite
    infer_instance
  invariant := by
    let R : Submodule ℝ H := P.space ⊔ Submodule.span ℝ {s.vector}
    have hle : R ≤ R.comap G.toLinearMap := by
      apply sup_le
      · intro x hx
        exact (le_sup_left : P.space ≤ R) (P.invariant x hx)
      · apply Submodule.span_le.mpr
        intro x hx
        have hx' : x = s.vector := Set.mem_singleton_iff.mp hx
        change G x ∈ R
        rw [hx', s.eigen]
        apply R.smul_mem
        exact (le_sup_right : Submodule.span ℝ {s.vector} ≤ R)
          (Submodule.subset_span (Set.mem_singleton s.vector))
    exact fun x hx => hle hx

theorem aux_spectral_scaled_distance_sq
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {e : ℕ → H} (he : Orthonormal ℝ e) {i j : ℕ} (hij : i ≠ j)
    (a b : ℝ) : ‖a • e i - b • e j‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq,
    he.2 hij, he.2 hij.symm, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, he.1]
  ring

/-- Compactness forces the eigenvalues of any orthonormal eigen-sequence to
vanish. This does not presume that the eigenvectors span the space. -/
theorem aux_spectral_values_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H →L[ℝ] H) (hc : IsCompactOperator G)
    (μ : ℕ → ℝ) (e : ℕ → H) (he : Orthonormal ℝ e)
    (hμ : ∀ n, 0 < μ n) (hGe : ∀ n, G (e n) = μ n • e n) :
    Tendsto μ atTop (𝓝 0) := by
  classical
  have hcompact : IsCompact (closure (G '' Metric.closedBall (0 : H) 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := G.toLinearMap) hc 1
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  have hev : ∀ᶠ n in atTop, μ n < ε := by
    by_contra hn
    have hfreq : ∃ᶠ n in atTop, ε ≤ μ n := by
      simpa only [not_lt] using! (not_eventually.mp hn)
    obtain ⟨φ, hφ, hφε⟩ := extraction_of_frequently_atTop hfreq
    have himg (n : ℕ) : G (e (φ n)) ∈ closure (G '' Metric.closedBall (0 : H) 1) := by
      apply subset_closure
      refine ⟨e (φ n), ?_, rfl⟩
      simpa only [Metric.mem_closedBall, dist_zero_right, he.1] using!
        (le_rfl : (1 : ℝ) ≤ 1)
    obtain ⟨z, hz, ψ, hψ, hlim⟩ := hcompact.tendsto_subseq himg
    have hC := hlim.cauchySeq
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hC ε hε
    have hd := hN N le_rfl (N + 1) (Nat.le_succ N)
    have hne : φ (ψ N) ≠ φ (ψ (N + 1)) :=
      ne_of_lt ((hφ.comp hψ) (Nat.lt_succ_self N))
    have hsq := aux_spectral_scaled_distance_sq he hne (μ (φ (ψ N))) (μ (φ (ψ (N + 1))))
    change dist (G (e (φ (ψ N)))) (G (e (φ (ψ (N + 1))))) < ε at hd
    rw [dist_eq_norm, hGe, hGe] at hd
    have hsmall : ‖μ (φ (ψ N)) • e (φ (ψ N)) -
        μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖ ^ 2 < ε ^ 2 := by
      have hp : 0 < (ε - ‖μ (φ (ψ N)) • e (φ (ψ N)) -
          μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖) *
          (ε + ‖μ (φ (ψ N)) • e (φ (ψ N)) -
          μ (φ (ψ (N + 1))) • e (φ (ψ (N + 1)))‖) :=
        mul_pos (sub_pos.mpr hd) (add_pos_of_pos_of_nonneg hε (norm_nonneg _))
      nlinarith
    have hfirst := hφε (ψ N)
    have hsecond := hφε (ψ (N + 1))
    have hfirstSq : ε ^ 2 ≤ μ (φ (ψ N)) ^ 2 := by
      simpa only [pow_two] using!
        mul_le_mul hfirst hfirst hε.le (hμ _).le
    have hsecondSq : ε ^ 2 ≤ μ (φ (ψ (N + 1))) ^ 2 := by
      simpa only [pow_two] using!
        mul_le_mul hsecond hsecond hε.le (hμ _).le
    rw [hsq] at hsmall
    nlinarith only [hsmall, hfirstSq, hsecondSq, sq_pos_of_pos hε]
  filter_upwards [hev] with n hn
  simpa only [Real.dist_eq, sub_zero, abs_of_pos (hμ n)] using! hn

/-- Successive maximal eigenvectors have dense closed span. -/
theorem aux_exists_orthonormal_eigenbasis_of_compact_pos {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (G : H →L[ℝ] H) (hG : IsSelfAdjoint G) (hc : IsCompactOperator G)
    (hpos : ∀ x, 0 ≤ inner ℝ (G x) x) (hinj : Function.Injective G)
    (hinf : ¬ FiniteDimensional ℝ H) :
    ∃ (μ : ℕ → ℝ) (e : ℕ → H), (∀ n, 0 < μ n) ∧
      (∀ n, G (e n) = μ n • e n) ∧ Orthonormal ℝ e ∧
      Tendsto μ atTop (𝓝 0) ∧
      (Submodule.span ℝ (Set.range e)).topologicalClosure = ⊤ := by
  classical
  let pick (P : SpectralStage G) : SpectralPick G P.space :=
    Classical.choice (aux_spectral_pick_exists G hG hc hpos hinj hinf P)
  let stage : ℕ → SpectralStage G :=
    Nat.rec (spectralInitial G) (fun _ P => spectralEnlarge G P (pick P))
  let μ : ℕ → ℝ := fun n => (pick (stage n)).value
  let e : ℕ → H := fun n => (pick (stage n)).vector
  have hstep (n : ℕ) : (stage (n + 1)).space =
      (stage n).space ⊔ Submodule.span ℝ {e n} := rfl
  have hle (n : ℕ) : (stage n).space ≤ (stage (n + 1)).space := by
    rw [hstep]
    exact le_sup_left
  have hmono : Monotone (fun n => (stage n).space) :=
    monotone_nat_of_le_succ hle
  have hemem (n : ℕ) : e n ∈ (stage (n + 1)).space := by
    rw [hstep]
    exact (le_sup_right : Submodule.span ℝ {e n} ≤ (stage n).space ⊔ Submodule.span ℝ {e n})
      (Submodule.subset_span (Set.mem_singleton (e n)))
  have heorth (n : ℕ) : e n ∈ (stage n).space.orthogonal :=
    (pick (stage n)).vector_orth
  have hnorm (n : ℕ) : ‖e n‖ = 1 := (pick (stage n)).vector_norm
  have hμ (n : ℕ) : 0 < μ n := (pick (stage n)).value_pos
  have hGe (n : ℕ) : G (e n) = μ n • e n := (pick (stage n)).eigen
  have hpair : Pairwise (fun i j => inner ℝ (e i) (e j) = 0) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact heorth j (e i) (hmono (Nat.succ_le_of_lt hlt) (hemem i))
    · rw [real_inner_comm]
      exact heorth i (e j) (hmono (Nat.succ_le_of_lt hgt) (hemem j))
  have he : Orthonormal ℝ e := ⟨hnorm, hpair⟩
  have hμlim : Tendsto μ atTop (𝓝 0) :=
    aux_spectral_values_tendsto_zero G hc μ e he hμ hGe
  refine ⟨μ, e, hμ, hGe, he, hμlim, ?_⟩
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range e)
  have hstage (n : ℕ) : (stage n).space ≤ S := by
    induction n with
    | zero => exact bot_le
    | succ n ih =>
      rw [hstep]
      apply sup_le ih
      apply Submodule.span_le.mpr
      intro x hx
      have hx' : x = e n := Set.mem_singleton_iff.mp hx
      rw [hx']
      exact Submodule.subset_span ⟨n, rfl⟩
  apply Submodule.topologicalClosure_eq_top_iff.mpr
  apply le_antisymm
  · intro x hx
    have hxstage (n : ℕ) : x ∈ (stage n).space.orthogonal := by
      intro y hy
      exact hx y (hstage n hy)
    have hbound (n : ℕ) : ‖G x‖ ≤ μ n * ‖x‖ :=
      (pick (stage n)).bound x (hxstage n)
    have hlim : Tendsto (fun n => μ n * ‖x‖) atTop (𝓝 (0 : ℝ)) := by
      simpa only [zero_mul] using! hμlim.mul_const ‖x‖
    have hzero : ‖G x‖ ≤ 0 := le_of_tendsto_of_tendsto
      tendsto_const_nhds hlim (Filter.Eventually.of_forall hbound)
    have hGx : G x = 0 := norm_eq_zero.mp (le_antisymm hzero (norm_nonneg _))
    rw [Submodule.mem_bot]
    apply hinj
    simpa only [map_zero] using! hGx
  · exact bot_le

end CompactSpectrum


/-- Coordinate polynomials are square integrable for the actual bounded weighted ball. -/
theorem polynomial_memLp_dirichletVolume (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R)
    (C : ℝ) (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (i : Fin d) (p : Polynomial ℝ) :
    MemLp (fun x : Vec d => p.eval (x i)) 2 (dirichletVolume ρ R) := by
  letI := dirichletVolume_isFinite ρ R hR C hρ
  have hc : Continuous (fun x : Vec d => p.eval (x i)) :=
    p.continuous.comp (continuous_apply i)
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Vec d) R).exists_bound_of_continuousOn
    hc.continuousOn
  apply MemLp.of_bound hc.aestronglyMeasurable B
  have hm : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _)
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  filter_upwards [hm] with x hx
  apply hB x
  have hh := sourceBall_subset_cube R hR hx
  change dist x 0 < 2 * R / 2 at hh
  exact (show dist x 0 ≤ R by linarith)

/-- Polynomials in a single coordinate embed injectively in the actual weighted
ball L² space. Positivity of the density and openness of the Euclidean ball
prevent almost-everywhere identification from collapsing any polynomial. -/
theorem not_finiteDimensional_dirichletVolume (hd : 1 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ¬ FiniteDimensional ℝ (Lp ℝ 2 (dirichletVolume ρ R)) := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let hf (p : Polynomial ℝ) := polynomial_memLp_dirichletVolume ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) i p
  let F : Polynomial ℝ →ₗ[ℝ] Lp ℝ 2 (dirichletVolume ρ R) :=
    { toFun := fun p => (hf p).toLp (fun x => p.eval (x i))
      map_add' := by
        intro p q
        apply Lp.ext
        filter_upwards [(hf (p + q)).coeFn_toLp,
          Lp.coeFn_add ((hf p).toLp (fun x => p.eval (x i)))
            ((hf q).toLp (fun x => q.eval (x i))),
          (hf p).coeFn_toLp, (hf q).coeFn_toLp] with x h1 h2 h3 h4
        rw [h1, h2]
        simp only [Pi.add_apply, h3, h4, Polynomial.eval_add]
      map_smul' := by
        intro c p
        apply Lp.ext
        filter_upwards [(hf (c • p)).coeFn_toLp,
          Lp.coeFn_smul c ((hf p).toLp (fun x => p.eval (x i))),
          (hf p).coeFn_toLp] with x h1 h2 h3
        change ((hf (c • p)).toLp (fun x => (c • p).eval (x i))) x =
          (c • (hf p).toLp (fun x => p.eval (x i))) x
        rw [h1, h2]
        simp only [Pi.smul_apply, smul_eq_mul, h3, Polynomial.eval_smul] }
  have hinj : Function.Injective F := by
    intro p q he
    have hae : (fun x : Vec d => p.eval (x i)) =ᵐ[dirichletVolume ρ R]
        (fun x : Vec d => q.eval (x i)) :=
      (MemLp.toLp_eq_toLp_iff (hf p) (hf q)).mp he
    have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
      apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
      exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
    have hpt := Measure.eqOn_open_of_ae_eq (hac.ae_le hae) (dirichletBall (d := d) R).isOpen
      (p.continuous.comp (continuous_apply i)).continuousOn
      (q.continuous.comp (continuous_apply i)).continuousOn
    apply Polynomial.eq_of_infinite_eval_eq p q
    apply (Set.Ioo_infinite (show -R < R by linarith)).mono
    intro t ht
    have hball : (Pi.single i t : Vec d) ∈ sourceBall (0 : Vec d) R := by
      change euclideanNorm ((Pi.single i t : Vec d) - 0) < R
      rw [sub_zero]
      have hn : euclideanNorm (Pi.single i t : Vec d) = |t| := by
        simp [euclideanNorm, euclideanSq, dot, Pi.single_apply, ← pow_two, Real.sqrt_sq_eq_abs]
      rw [hn]
      exact abs_lt.mpr ht
    change p.eval t = q.eval t
    simpa only [Pi.single_eq_same] using hpt hball
  intro hfin
  letI := hfin
  exact Polynomial.not_finite (FiniteDimensional.of_injective F hinj)


/-- Every native H10 function on the source ball belongs to the completed
Dirichlet energy space after zero extension to its containing cube. The same
smooth ball-supported sequence witnesses membership in the completion. -/
theorem exists_dirichletHilbert_of_nativeH10 {d : ℕ}
    (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function
      (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (fun x => u.val none x) =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
        v.toH1Function.toFun ∧
      ∀ i : Fin d, (fun x => u.val (some i) x)
        =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] (fun x => v.toH1Function.grad x i) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let w := v.extendByZeroToOpenSuperset (dirichletBall R).isOpen.measurableSet
    Q.isOpen (sourceBall_subset_cube R hR)
  let φ : ℕ → TestFunction (dirichletBall (d := d) R) ℝ ⊤ := fun n =>
    ⟨v.approx n, v.approx_smooth n, v.approx_hasCompactSupport n,
      v.approx_support_subset n⟩
  let f : SobolevData Q :=
    (w.toH1Function.memL2.toLp _, fun i => (w.toH1Function.gradMemL2 i).toLp _)
  have hval : Filter.Tendsto
      (fun n => (smoothSobolevData (dirichletTestInCube R hR (φ n))).1)
      Filter.atTop (nhds f.1) := by
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n => (dirichletTestInCube R hR (φ n) : SpatialCoordinates d → ℝ))
      (fun n => (dirichletTestInCube R hR (φ n)).contDiff.continuous.memLp_of_hasCompactSupport
        (dirichletTestInCube R hR (φ n)).hasCompactSupport)
      w.toH1Function.toFun w.toH1Function.memL2).mpr w.tendsto_approx
  have hgrad (i : Fin d) : Filter.Tendsto
      (fun n => (smoothSobolevData (dirichletTestInCube R hR (φ n))).2 i)
      Filter.atTop (nhds (f.2 i)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun n x => fderiv ℝ (dirichletTestInCube R hR (φ n) : SpatialCoordinates d → ℝ)
        x (Pi.single i 1))
      (fun n => ((dirichletTestInCube R hR (φ n)).contDiff.continuous_fderiv_apply
        (by simp)).comp (continuous_id.prodMk continuous_const)
        |>.memLp_of_hasCompactSupport
          ((dirichletTestInCube R hR (φ n)).hasCompactSupport.fderiv_apply ℝ (Pi.single i 1)))
      (fun x => w.toH1Function.grad x i) (w.toH1Function.gradMemL2 i)).mpr
    change Filter.Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (v.approx n) x (Pi.single i 1) - w.toH1Function.grad x i)
      2 (volume.restrict (Q : Set (SpatialCoordinates d)))) Filter.atTop (nhds 0)
    exact w.tendsto_approx_grad i
  have hlim : Filter.Tendsto (fun n => dirichletSmoothData R hR (φ n))
      Filter.atTop (nhds (sobolevToHilbert Q f)) :=
    (sobolevToHilbert Q).continuous.continuousAt.tendsto.comp
      (hval.prodMk_nhds (tendsto_pi_nhds.mpr hgrad))
  have hmem : sobolevToHilbert Q f ∈ dirichletHilbertSubmodule R hR := by
    change sobolevToHilbert Q f ∈
      closure (Set.range (dirichletSmoothData (d := d) R hR))
    apply mem_closure_of_tendsto hlim
    exact Filter.Eventually.of_forall fun n => ⟨φ n, rfl⟩
  let u : DirichletHilbertSpace (d := d) R hR := ⟨sobolevToHilbert Q f, hmem⟩
  refine ⟨u, ?_, ?_⟩
  · have hv : (fun x => u.val none x) =ᵐ[volume.restrict (Q : Set _)]
        w.toH1Function.toFun := MemLp.coeFn_toLp w.toH1Function.memL2
    have hvball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) hv
    filter_upwards [hvball, ae_restrict_mem (dirichletBall R).isOpen.measurableSet]
      with x hx hxb
    rw [hx]
    exact Set.indicator_of_mem hxb _
  · intro i
    have hg : (fun x => u.val (some i) x) =ᵐ[volume.restrict (Q : Set _)]
        (fun x => w.toH1Function.grad x i) :=
      MemLp.coeFn_toLp (w.toH1Function.gradMemL2 i)
    have hgball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) hg
    filter_upwards [hgball, ae_restrict_mem (dirichletBall R).isOpen.measurableSet]
      with x hx hxb
    rw [hx]
    change ((dirichletBall (d := d) R : Set _).indicator v.toH1Function.grad) x i = _
    rw [Set.indicator_of_mem hxb]

/-- A native zero-boundary function and its completed representative have
identical values in the weighted spectral space and identical gradients. -/
theorem exists_dirichletHilbert_of_nativeH10_weighted {d : ℕ}
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR C hρ u : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      ∀ i : Fin d, (fun x => u.val (some i) x)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
          (fun x => v.toH1Function.grad x i) := by
  obtain ⟨u, hv, hg⟩ := exists_dirichletHilbert_of_nativeH10 R hR v
  refine ⟨u, ?_, hg⟩
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  have hvalue := hac.ae_le hv
  have hincl := dirichletHilbertInclusion_coe ρ R hR C hρ u
  filter_upwards [hincl, hvalue] with x hx hy
  exact hx.trans hy

#print axioms exists_dirichletHilbert_of_nativeH10_weighted

/-- A native eigenfunction equation on smooth ball tests transfers to the
completed Dirichlet space, with its actual weighted inclusion. -/
theorem exists_dirichletHilbert_weakEquation_of_native_smooth {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      eig * ∫ x in sourceBall (0 : Vec d) R, ρ x * v.toH1Function.toFun x * φ x) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) =
        eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) u)
          (dirichletHilbertInclusion ρ R hR κ⁻¹
            (fun x _ => (h.2.2 x).2.1) w) := by
  obtain ⟨u, hv, hg⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) v
  refine ⟨u, hv, dirichletHilbert_weakEquation_of_smooth hd hκ h R hR u eig ?_⟩
  intro φ
  rw [dirichletHilbert_energyIntegral_smooth]
  have hgrad : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
      (fun i => u.val (some i) x) = v.toH1Function.grad x := by
    filter_upwards [ae_all_iff.mpr hg] with x hx
    exact funext hx
  have he : (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i)) := by
    apply integral_congr_ae
    filter_upwards [hgrad] with x hx
    rw [hx]
  rw [he, hweak φ]
  congr 1
  symm
  rw [L2.inner_def]
  calc
    _ = ∫ x, v.toH1Function.toFun x * φ x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hv, dirichletHilbertInclusion_smooth_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) φ] with x hx hy
      simp only [RCLike.inner_apply, conj_trivial, hx, hy]
      exact mul_comm _ _
    _ = _ := by
      change (∫ x, v.toH1Function.toFun x * φ x ∂(volume.restrict
        (sourceBall (0 : Vec d) R)).withDensity (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
        ring

#print axioms exists_dirichletHilbert_weakEquation_of_native_smooth

/-- An actual native H¹₀-tested weak eigenfunction equation holds on every
supported smooth test used by the completed Dirichlet space. -/
theorem native_weakEigenEquation_on_smooth {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} (R : ℝ)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    ∀ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x))
          (fun i => fderiv ℝ (φ : Vec d → ℝ) x (unitVector i))) =
      eig * ∫ x in sourceBall (0 : Vec d) R, ρ x * v.toH1Function.toFun x * φ x := by
  intro φ
  let ψ : Homogenization.H10Function (sourceBall (0 : Vec d) R) :=
    Homogenization.H10Function.ofContDiff (dirichletBall R).isOpen
      φ.contDiff φ.hasCompactSupport φ.tsupport_subset
  have hw := hweak ψ
  simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at hw
  simpa only [ψ, Homogenization.H10Function.ofContDiff,
    Homogenization.H1Function.ofContDiff, Homogenization.basisVec, unitVector,
    Homogenization.vecDot, Homogenization.matVecMul, Matrix.mulVec, dotProduct, dot,
    integral_const_mul, mul_assoc] using hw

#print axioms native_weakEigenEquation_on_smooth

/-- The actual unshifted source Dirichlet form has a complete orthonormal
weighted-L² eigenbasis, with genuine supported H¹ eigenvectors and positive
source eigenvalues tending to infinity. No spectral data are assumed. -/
theorem exists_dirichletHilbert_eigenbasis (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      Orthonormal ℝ (fun n => J (u n)) ∧
      (Submodule.span ℝ (Set.range (fun n => J (u n)))).topologicalClosure = ⊤ ∧
      ∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨_c, _hc, S, hcomp, hsa, hinj, _hdense, hpos, _hnorm, hvar⟩ :=
    exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  have hnonneg (f : Lp ℝ 2 (dirichletVolume ρ R)) :
      0 ≤ inner ℝ ((J.comp S) f) f := by
    rw [real_inner_comm]
    by_cases hf : f = 0
    · simp only [hf, inner_zero_left, le_refl]
    · exact (hpos f hf).le
  obtain ⟨μ, e, hμ, hGe, he, hμlim, hspan⟩ :=
    CompactSpectrum.aux_exists_orthonormal_eigenbasis_of_compact_pos
      (J.comp S) hsa hcomp hnonneg hinj
      (not_finiteDimensional_dirichletVolume (by omega) hκ h R hR)
  let eigenvalue : ℕ → ℝ := fun n => (μ n)⁻¹
  let u : ℕ → DirichletHilbertSpace (d := d) R hR := fun n => S (eigenvalue n • e n)
  have hJu (n : ℕ) : J (u n) = e n := by
    dsimp only [u]
    rw [map_smul, map_smul]
    change (μ n)⁻¹ • ((J.comp S) (e n)) = e n
    rw [hGe, smul_smul, inv_mul_cancel₀ (hμ n).ne', one_smul]
  refine ⟨eigenvalue, u, (fun n => inv_pos.mpr (hμ n)), ?_, ?_, ?_, ?_⟩
  · exact tendsto_inv_nhdsGT_zero.comp
      (tendsto_nhdsWithin_iff.mpr ⟨hμlim, Eventually.of_forall hμ⟩)
  · change Orthonormal ℝ (fun n => J (u n))
    simpa only [hJu] using he
  · change (Submodule.span ℝ (Set.range (fun n => J (u n)))).topologicalClosure = ⊤
    simpa only [hJu] using hspan
  · intro n v
    rw [hJu]
    have hv := (hvar (eigenvalue n • e n) (u n)).mp rfl v
    simpa only [real_inner_smul_left] using hv


/-- The actual weighted inclusion represents the literal source-ball zero extension. -/
theorem dirichletHilbertInclusion_zeroExtension_coe (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : DirichletHilbertSpace (d := d) R hR) :
    dirichletHilbertInclusion ρ R hR C hρ u =ᵐ[dirichletVolume ρ R]
      dirichletHilbertZeroExtension R hR u := by
  have hm : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _)
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  filter_upwards [dirichletHilbertInclusion_coe ρ R hR C hρ u, hm] with x hx hm
  change (dirichletHilbertInclusion ρ R hR C hρ u) x = u.val none x at hx
  simpa only [dirichletHilbertZeroExtension, Set.indicator_of_mem hm] using hx

/-- Smooth-test pairings use the literal zero-extended H¹ representative. -/
theorem dirichletHilbertInclusion_inner_smooth_zeroExtension {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
    inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        (dirichletSmoothElement R hR ψ)) =
      ∫ x in sourceBall (0 : Vec d) R,
        ρ x * dirichletHilbertZeroExtension R hR u x * ψ x := by
  rw [dirichletHilbertInclusion_inner_smooth hκ h R hR]
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  apply integral_congr_ae
  filter_upwards [hac.ae_le (dirichletHilbertInclusion_zeroExtension_coe ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) u)] with x hx
  rw [hx]

/-- Actual weak source eigenfunctions supply all algebraic, L², global weak
zero-extension, and completeness fields of the Dirichlet spectral carrier.
Continuity on the closed ball remains a separate regularity assertion. -/
theorem exists_weak_dirichletSpectralResolution (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eigenvalue : ℕ → ℝ) (φ : ℕ → Vec d → ℝ) (g : ℕ → Vec d → Vec d),
    ∃ hf : ∀ n, MemLp (φ n) 2 (dirichletVolume ρ R),
      (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      (∀ n, ∀ x ∈ frontier (sourceBall (0 : Vec d) R), φ n x = 0) ∧
      (∀ n, MemLp (fun x => euclideanNorm (g n x)) 2
        (volume.restrict (sourceBall (0 : Vec d) R))) ∧
      (∀ n, EinsteinRelation.HasWeakGradient Set.univ
        ((sourceBall (0 : Vec d) R).indicator (φ n))
        ((sourceBall (0 : Vec d) R).indicator (g n))) ∧
      (∀ n, ∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall (0 : Vec d) R) ψ →
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (g n x)) (fun i => fderiv ℝ ψ x (unitVector i))) =
          eigenvalue n * ∫ x in sourceBall (0 : Vec d) R, ρ x * φ n x * ψ x) ∧
      Orthonormal ℝ (fun n => (hf n).toLp (φ n)) ∧
      Dense (Submodule.span ℝ (Set.range (fun n => (hf n).toLp (φ n))) :
        Set (Lp ℝ 2 (dirichletVolume ρ R))) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eigenvalue, u, hpos, hlim, he, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let φ := fun n => dirichletHilbertZeroExtension R hR (u n)
  let g := fun n => dirichletHilbertZeroExtensionGrad R hR (u n)
  have hrep (n : ℕ) : J (u n) =ᵐ[dirichletVolume ρ R] φ n :=
    dirichletHilbertInclusion_zeroExtension_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n)
  let hf : ∀ n, MemLp (φ n) 2 (dirichletVolume ρ R) :=
    fun n => (Lp.memLp (J (u n))).ae_eq (hrep n)
  have hfamily : (fun n => (hf n).toLp (φ n)) = fun n => J (u n) := by
    funext n
    apply Lp.ext
    exact (hf n).coeFn_toLp.trans (hrep n).symm
  refine ⟨eigenvalue, φ, g, hf, hpos, hlim, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x hx
    have hnot : x ∉ sourceBall (0 : Vec d) R :=
      Set.disjoint_left.mp
        (disjoint_frontier_iff_isOpen.mpr (dirichletBall (d := d) R).isOpen) hx
    exact Set.indicator_of_notMem hnot _
  · intro n
    exact (dirichletHilbert_zeroExtension_euclideanNorm_memLp R hR (u n)).restrict _
  · intro n
    simpa only [φ, g, dirichletHilbertZeroExtension, dirichletHilbertZeroExtensionGrad,
      Set.indicator_indicator, Set.inter_self] using
        (dirichletHilbert_global_zeroExtension R hR (u n)).2.2
  · intro n ψ hψ
    let test : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
      ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
    have hv := hvar n (dirichletSmoothElement R hR test)
    rw [dirichletHilbert_energyIntegral_smooth α R hR (u n) test,
      dirichletHilbertInclusion_inner_smooth_zeroExtension hκ h R hR (u n) test] at hv
    calc
      _ = ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => fderiv ℝ ψ x (unitVector i)) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet]
          with x hx
        simp only [g, dirichletHilbertZeroExtensionGrad, Set.indicator_of_mem hx]
      _ = _ := hv
  · rw [hfamily]
    exact he
  · rw [hfamily]
    exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hspan


/-! Spectral heat operators on the actual weighted Hilbert space. These are
constructed from the proved eigenbasis, without a pointwise kernel assumption. -/
namespace SpectralHeat

/-- A bounded real diagonal multiplier on square-summable real sequences. -/
def diagonal (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) : lp (fun _ : ℕ => ℝ) 2 →L[ℝ] lp (fun _ : ℕ => ℝ) 2 := by
  let L : lp (fun _ : ℕ => ℝ) 2 →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
    { toFun := fun x => ⟨fun n => a n * x n,
        memℓp_gen (Summable.of_nonneg_of_le (fun n => by positivity)
          (fun n => Real.rpow_le_rpow (norm_nonneg _) (by
            change ‖a n * x n‖ ≤ ‖C * x n‖
            simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
            exact mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _)) (by norm_num))
          ((lp.memℓp (C • x)).summable (by norm_num)))⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext n
        exact mul_add _ _ _
      map_smul' := by
        intro t x
        apply lp.ext
        funext n
        change a n * (t * x n) = t * (a n * x n)
        ring }
  apply L.mkContinuous C
  intro x
  calc
    ‖L x‖ ≤ ‖C • x‖ := lp.norm_mono (by norm_num) (fun n => by
      change ‖a n * x n‖ ≤ ‖C * x n‖
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _))
    _ = C * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

theorem diagonal_apply (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) (x : lp (fun _ : ℕ => ℝ) 2) (n : ℕ) :
    diagonal a C hC ha x n = a n * x n := rfl

theorem diagonal_norm_le (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) (x : lp (fun _ : ℕ => ℝ) 2) :
    ‖diagonal a C hC ha x‖ ≤ C * ‖x‖ := by
  calc
    _ ≤ ‖C • x‖ := lp.norm_mono (by norm_num) (fun n => by
      change ‖a n * x n‖ ≤ ‖C * x n‖
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha n) (abs_nonneg _))
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Transport a bounded real diagonal multiplier through a Hilbert basis. -/
def multiplier (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, |a n| ≤ C) : H →L[ℝ] H :=
  b.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((diagonal a C hC ha).comp b.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem multiplier_repr (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (f : H) (n : ℕ) :
    b.repr (multiplier b a C hC ha f) n = a n * b.repr f n := by
  change b.repr (b.repr.symm (diagonal a C hC ha (b.repr f))) n = _
  rw [b.repr.apply_symm_apply]
  rfl

theorem multiplier_norm_le (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (f : H) :
    ‖multiplier b a C hC ha f‖ ≤ C * ‖f‖ := by
  change ‖b.repr.symm (diagonal a C hC ha (b.repr f))‖ ≤ _
  rw [b.repr.symm.norm_map]
  exact (diagonal_norm_le a C hC ha (b.repr f)).trans_eq
    (congrArg (C * ·) (b.repr.norm_map f))

theorem multiplier_basis (b : HilbertBasis ℕ ℝ H) (a : ℕ → ℝ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ n, |a n| ≤ C) (n : ℕ) :
    multiplier b a C hC ha (b n) = a n • b n := by
  classical
  apply b.repr.injective
  apply lp.ext
  funext m
  rw [multiplier_repr, map_smul, b.repr_self]
  change a m * (lp.single 2 n (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2) m =
    a n * (lp.single 2 n (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2) m
  simp only [lp.single_apply]
  by_cases hmn : m = n
  · subst m
    simp
  · simp [hmn]

theorem exp_weight_bound (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (n : ℕ) : |Real.exp (-eigenvalue n * t)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hpos n)) t.coe_nonneg

/-- The spectral heat operator for nonnegative source eigenvalues. -/
def heatOperator (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) : H →L[ℝ] H :=
  multiplier b (fun n => Real.exp (-eigenvalue n * t)) 1 (by norm_num)
    (exp_weight_bound eigenvalue hpos t)

theorem heatOperator_repr (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) (f : H) (n : ℕ) :
    b.repr (heatOperator b eigenvalue hpos t f) n =
      Real.exp (-eigenvalue n * t) * b.repr f n :=
  multiplier_repr _ _ _ _ _ _ _

theorem heatOperator_norm_le (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) (f : H) :
    ‖heatOperator b eigenvalue hpos t f‖ ≤ ‖f‖ := by
  simpa only [heatOperator, one_mul] using multiplier_norm_le b _ 1 (by norm_num)
    (exp_weight_bound eigenvalue hpos t) f

/-- High spectral modes decay at any prescribed exponential rate after a finite cutoff. -/
theorem heatOperator_finite_tail (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (hlim : Tendsto eigenvalue atTop atTop)
    (M : ℝ) : ∃ N : ℕ, ∀ (t : ℝ≥0) (f : H),
      ‖heatOperator b eigenvalue hpos t f -
        ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * t) • (b.repr f n • b n)‖ ≤
        Real.exp (-M * t) * ‖f‖ := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.1 hlim) M)
  refine ⟨N, fun t f => ?_⟩
  let a : ℕ → ℝ := fun n => if n < N then 0 else Real.exp (-eigenvalue n * t)
  have ha : ∀ n, |a n| ≤ Real.exp (-M * t) := by
    intro n
    by_cases hn : n < N
    · simp [a, hn, (Real.exp_pos _).le]
    · simp only [a, hn, ite_false, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg (hN n (Nat.le_of_not_gt hn))) t.coe_nonneg
  have heq : heatOperator b eigenvalue hpos t f -
      ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * t) • (b.repr f n • b n) =
      multiplier b a (Real.exp (-M * t)) (Real.exp_pos _).le ha f := by
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [map_sub]
    simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [heatOperator_repr, multiplier_repr]
    simp only [map_sum, map_smul, b.repr_self, lp.coeFn_smul, Pi.smul_apply,
      lp.coeFn_sum, Finset.sum_apply, lp.single_apply, smul_eq_mul]
    by_cases hn : n < N
    · simp only [a, hn, ite_true, zero_mul, sub_eq_zero]
      rw [Finset.sum_eq_single n]
      · simp
      · intro x _ hxn
        simp [hxn]
      · simp [Finset.mem_range, hn]
    · simp only [a, hn, ite_false, sub_eq_self]
      apply Finset.sum_eq_zero
      intro x hx
      have hxn : x ≠ n := by
        intro heq
        subst x
        exact hn (Finset.mem_range.mp hx)
      simp [hxn]
  rw [heq]
  exact multiplier_norm_le b a _ _ ha f

theorem heatOperator_zero (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) :
    heatOperator b eigenvalue hpos 0 = ContinuousLinearMap.id ℝ H := by
  ext f
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [heatOperator_repr]
  simp

theorem heatOperator_add (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (s t : ℝ≥0) :
    heatOperator b eigenvalue hpos (s + t) =
      (heatOperator b eigenvalue hpos s).comp (heatOperator b eigenvalue hpos t) := by
  ext f
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.comp_apply, heatOperator_repr, heatOperator_repr,
    heatOperator_repr, NNReal.coe_add, mul_add, Real.exp_add, mul_assoc]

theorem heatOperator_basis (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) (n : ℕ) :
    heatOperator b eigenvalue hpos t (b n) = Real.exp (-eigenvalue n * t) • b n :=
  multiplier_basis _ _ _ _ _ _

theorem heatOperator_symmetric (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) (f g : H) :
    inner ℝ (heatOperator b eigenvalue hpos t f) g =
      inner ℝ f (heatOperator b eigenvalue hpos t g) := by
  rw [← b.repr.inner_map_map, ← b.repr.inner_map_map f]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  rw [heatOperator_repr, heatOperator_repr]
  change inner ℝ (Real.exp (-eigenvalue n * t) • b.repr f n) (b.repr g n) =
    inner ℝ (b.repr f n) (Real.exp (-eigenvalue n * t) • b.repr g n)
  rw [real_inner_smul_left, real_inner_smul_right]

/-- A vector supported on a spectral eigenspace is a heat eigenvector, including
when that eigenspace has multiplicity greater than one. -/
theorem heatOperator_eigenvector_of_coordinates (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (u : H) (eig : ℝ) (hcoord : ∀ n, (eigenvalue n - eig) * b.repr u n = 0)
    (t : ℝ≥0) :
    heatOperator b eigenvalue hpos t u = Real.exp (-eig * t) • u := by
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [heatOperator_repr, map_smul]
  change Real.exp (-eigenvalue n * t) * b.repr u n =
    Real.exp (-eig * t) * b.repr u n
  rcases mul_eq_zero.mp (hcoord n) with h | h
  · have he : eigenvalue n = eig := sub_eq_zero.mp h
    rw [he]
  · rw [h, mul_zero, mul_zero]

/-- The diagonal spectral heat pairing is nonnegative. -/
theorem heatOperator_nonneg (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (f : H) : 0 ≤ inner ℝ f (heatOperator b eigenvalue hpos t f) := by
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
  apply tsum_nonneg
  intro n
  rw [heatOperator_repr]
  change 0 ≤ inner ℝ (b.repr f n) (Real.exp (-eigenvalue n * t) • b.repr f n)
  rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact mul_nonneg (Real.exp_pos _).le (sq_nonneg _)

/-- Projection onto any normalized heat eigenvector gives a diagonal lower
bound, without choosing a distinguished vector from a multiple eigenspace. -/
theorem heatOperator_diagonal_lower_of_eigenvector (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (u f : H) (eig : ℝ) (hu : inner ℝ u u = 1)
    (he : heatOperator b eigenvalue hpos t u = Real.exp (-eig * t) • u) :
    Real.exp (-eig * t) * (inner ℝ u f) ^ 2 ≤
      inner ℝ f (heatOperator b eigenvalue hpos t f) := by
  let a : ℝ := inner ℝ u f
  have hn := heatOperator_nonneg b eigenvalue hpos t (f - a • u)
  have hs := heatOperator_symmetric b eigenvalue hpos t f u
  rw [he, real_inner_smul_right] at hs
  simp only [map_sub, map_smul, he, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right, hu] at hn
  dsimp [a] at hn
  rw [real_inner_comm f u, real_inner_comm (heatOperator b eigenvalue hpos t f) u, hs] at hn
  rw [real_inner_comm f u]
  nlinarith only [hn]

/-- Each spectral mode gives a lower bound for the diagonal heat pairing. -/
theorem heatOperator_diagonal_lower (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (f : H) (j : ℕ) :
    Real.exp (-eigenvalue j * t) * (inner ℝ (b j) f) ^ 2 ≤
      inner ℝ f (heatOperator b eigenvalue hpos t f) := by
  let g := heatOperator b eigenvalue hpos t f
  have hs : Summable (fun n : ℕ => inner ℝ (b.repr f n) (b.repr g n)) :=
    lp.summable_inner (b.repr f) (b.repr g)
  have hn : ∀ n : ℕ, 0 ≤ inner ℝ (b.repr f n) (b.repr g n) := by
    intro n
    dsimp [g]
    rw [heatOperator_repr]
    simp only [starRingEnd_apply, star_trivial]
    have hp := mul_nonneg (Real.exp_pos (-eigenvalue n * t)).le (sq_nonneg (b.repr f n))
    nlinarith only [hp]
  have h := hs.le_tsum j (fun n _ => hn n)
  rw [← lp.inner_eq_tsum, b.repr.inner_map_map] at h
  dsimp [g] at h
  rw [heatOperator_repr] at h
  simp only [starRingEnd_apply, star_trivial] at h
  rw [b.repr_apply_apply] at h
  nlinarith only [h]

theorem heatOperator_injective (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (t : ℝ≥0) :
    Function.Injective (heatOperator b eigenvalue hpos t) := by
  intro f g hfg
  apply b.repr.injective
  apply lp.ext
  funext n
  have h := congrArg (fun v => b.repr v n) hfg
  rw [heatOperator_repr, heatOperator_repr] at h
  exact mul_left_cancel₀ (Real.exp_pos _).ne' h

/-- The spectral heat operators are strongly continuous, including at time zero. -/
theorem heatOperator_continuous (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (f : H) :
    Continuous (fun t : ℝ≥0 => heatOperator b eigenvalue hpos t f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let F : ℝ≥0 → ℕ → ℝ := fun t n =>
    ‖(Real.exp (-eigenvalue n * t) - Real.exp (-eigenvalue n * t₀)) * b.repr f n‖ ^ 2
  have hsq : Summable (fun n => ‖b.repr f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (b.repr f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hbound (t : ℝ≥0) (n : ℕ) : ‖F t n‖ ≤ 4 * ‖b.repr f n‖ ^ 2 := by
    have ha : ‖Real.exp (-eigenvalue n * t) - Real.exp (-eigenvalue n * t₀)‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by
        simpa only [Real.norm_eq_abs, one_add_one_eq_two] using add_le_add
          (exp_weight_bound eigenvalue hpos t n) (exp_weight_bound eigenvalue hpos t₀ n))
    have hb : ‖(Real.exp (-eigenvalue n * t) - Real.exp (-eigenvalue n * t₀)) *
        b.repr f n‖ ≤ 2 * ‖b.repr f n‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ha (norm_nonneg _)
    change ‖(‖_‖ ^ 2 : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (2 * ‖b.repr f n‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hterm (n : ℕ) : Tendsto (fun t => F t n) (𝓝 t₀) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ≥0 => F t n) := by dsimp [F]; fun_prop
    simpa only [F, sub_self, zero_mul, norm_zero, zero_pow (by omega : 2 ≠ 0)] using
      hc.continuousAt.tendsto (x := t₀)
  have hsum : Tendsto (fun t => ∑' n, F t n) (𝓝 t₀) (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
      (hsq.mul_left 4) hterm (Eventually.of_forall hbound)
  have heq (t : ℝ≥0) :
      ‖heatOperator b eigenvalue hpos t f - heatOperator b eigenvalue hpos t₀ f‖ ^ 2 =
        ∑' n, F t n := by
    calc
      _ = ‖b.repr (heatOperator b eigenvalue hpos t f -
          heatOperator b eigenvalue hpos t₀ f)‖ ^ 2 := by rw [b.repr.norm_map]
      _ = ∑' n, ‖b.repr (heatOperator b eigenvalue hpos t f -
          heatOperator b eigenvalue hpos t₀ f) n‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (b.repr (heatOperator b eigenvalue hpos t f - heatOperator b eigenvalue hpos t₀ f))
      _ = _ := by
        apply tsum_congr
        intro n
        rw [map_sub]
        change ‖b.repr (heatOperator b eigenvalue hpos t f) n -
          b.repr (heatOperator b eigenvalue hpos t₀ f) n‖ ^ 2 = _
        rw [heatOperator_repr, heatOperator_repr, ← sub_mul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (hsum.congr' (Eventually.of_forall (fun t => (heq t).symm)))
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

/-- The first spectral moment is bounded by the reciprocal of positive time. -/
theorem firstMoment_weight_bound (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    |eigenvalue n * Real.exp (-eigenvalue n * t)| ≤ (t : ℝ)⁻¹ := by
  rw [abs_of_nonneg (mul_nonneg (hpos n).le (Real.exp_pos _).le), ← one_div]
  apply (le_div_iff₀ (show 0 < (t : ℝ) from ht)).mpr
  calc
    _ = (eigenvalue n * t) * Real.exp (-(eigenvalue n * t)) := by ring_nf
    _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
    _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)

/-- The bounded positive-time operator with spectral weights λ exp(-λt). -/
def firstMoment (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) : H →L[ℝ] H :=
  multiplier b (fun n => eigenvalue n * Real.exp (-eigenvalue n * t))
    (t : ℝ)⁻¹ (inv_nonneg.mpr t.coe_nonneg)
    (firstMoment_weight_bound eigenvalue hpos t ht)

theorem firstMoment_norm_le (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (f : H) :
    ‖firstMoment b eigenvalue hpos t ht f‖ ≤ (t : ℝ)⁻¹ * ‖f‖ :=
  multiplier_norm_le _ _ _ _ _ _

theorem firstMoment_basis (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (n : ℕ) :
    firstMoment b eigenvalue hpos t ht (b n) =
      (eigenvalue n * Real.exp (-eigenvalue n * t)) • b n :=
  multiplier_basis _ _ _ _ _ _

/-- The first moment intertwines addition of time with the heat semigroup. -/
theorem firstMoment_add (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (s : ℝ≥0) :
    firstMoment b eigenvalue hpos (t + s) (add_pos_of_pos_of_nonneg ht zero_le) =
      (firstMoment b eigenvalue hpos t ht).comp
        (heatOperator b eigenvalue (fun n => (hpos n).le) s) := by
  apply ContinuousLinearMap.ext_on (s := Set.range b)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨n, rfl⟩
  rw [firstMoment_basis, ContinuousLinearMap.comp_apply, heatOperator_basis,
    map_smul, firstMoment_basis, smul_smul]
  congr 1
  rw [NNReal.coe_add, mul_add, Real.exp_add]
  ring

/-- The first moment is strongly continuous on the open positive-time axis.
A fixed earlier time absorbs its unbounded generator, leaving only the already
strongly continuous heat semigroup. -/
theorem firstMoment_continuous (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (f : H) :
    Continuous (fun t : {t : ℝ≥0 // 0 < t} =>
      firstMoment b eigenvalue hpos t.val t.property f) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  let a : ℝ≥0 := t₀.val / 2
  have ha : 0 < a := half_pos t₀.property
  have hat : a < t₀.val := half_lt_self t₀.property
  have hlocal : ∀ᶠ t : {t : ℝ≥0 // 0 < t} in 𝓝 t₀, a ≤ t.val :=
    continuous_subtype_val.continuousAt.tendsto.eventually (eventually_ge_nhds hat)
  have hc : Continuous (fun t : {t : ℝ≥0 // 0 < t} =>
      firstMoment b eigenvalue hpos a ha
        (heatOperator b eigenvalue (fun n => (hpos n).le) (t.val - a) f)) :=
    (firstMoment b eigenvalue hpos a ha).continuous.comp
      ((heatOperator_continuous b eigenvalue (fun n => (hpos n).le) f).comp
        (continuous_subtype_val.sub continuous_const))
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hlocal] with t ht
  have hadd : a + (t.val - a) = t.val := add_tsub_cancel_of_le ht
  have heq := firstMoment_add b eigenvalue hpos a ha (t.val - a)
  simpa only [hadd, ContinuousLinearMap.comp_apply] using congrArg (fun T : H →L[ℝ] H => T f) heq

/-- At positive time the spectral heat operator factors through its inverse and
its bounded first spectral moment. -/
theorem heatOperator_eq_inverse_comp_firstMoment (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 < eigenvalue n)
    (G : H →L[ℝ] H) (hGe : ∀ n, G (b n) = (eigenvalue n)⁻¹ • b n)
    (t : ℝ≥0) (ht : 0 < t) :
    heatOperator b eigenvalue (fun n => (hpos n).le) t =
      G.comp (firstMoment b eigenvalue hpos t ht) := by
  apply ContinuousLinearMap.ext_on (s := Set.range b)
    (Submodule.dense_iff_topologicalClosure_eq_top.mpr b.dense_span)
  rintro _ ⟨n, rfl⟩
  rw [heatOperator_basis, ContinuousLinearMap.comp_apply, firstMoment_basis,
    map_smul, hGe, smul_smul]
  congr 1
  field_simp [(hpos n).ne']

/-- A compact inverse makes every positive-time spectral heat operator compact. -/
theorem heatOperator_compact_of_inverse (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 < eigenvalue n)
    (G : H →L[ℝ] H) (hG : IsCompactOperator G)
    (hGe : ∀ n, G (b n) = (eigenvalue n)⁻¹ • b n)
    (t : ℝ≥0) (ht : 0 < t) :
    IsCompactOperator (heatOperator b eigenvalue (fun n => (hpos n).le) t) := by
  rw [heatOperator_eq_inverse_comp_firstMoment b eigenvalue hpos G hGe t ht]
  exact hG.comp_clm _

/-- Uniform finite-mode approximation of a two-time heat pairing. -/
theorem heatOperator_two_times_finite_tail (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (hlim : Tendsto eigenvalue atTop atTop) (M : ℝ) :
    ∃ N : ℕ, ∀ (s t : ℝ≥0) (f g : H),
      |inner ℝ (heatOperator b eigenvalue hpos s f)
          (heatOperator b eigenvalue hpos t g) -
        ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * (s + t)) *
          (b.repr f n * b.repr g n)| ≤
        Real.exp (-M * (s + t)) * (‖f‖ * ‖g‖) := by
  classical
  obtain ⟨N, hN⟩ := heatOperator_finite_tail b eigenvalue hpos hlim M
  refine ⟨N, fun s t f g => ?_⟩
  have hp : inner ℝ (heatOperator b eigenvalue hpos s f)
      (heatOperator b eigenvalue hpos t g) =
      inner ℝ f (heatOperator b eigenvalue hpos (s + t) g) := by
    rw [heatOperator_symmetric, heatOperator_add, ContinuousLinearMap.comp_apply]
  have hs : inner ℝ f (∑ n ∈ Finset.range N,
      Real.exp (-eigenvalue n * (s + t)) • (b.repr g n • b n)) =
      ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * (s + t)) *
        (b.repr f n * b.repr g n) := by
    simp only [inner_sum, real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [b.repr_apply_apply, real_inner_comm f (b n)]
    ring
  rw [hp, ← hs, ← inner_sub_right]
  calc
    _ ≤ ‖f‖ * ‖heatOperator b eigenvalue hpos (s + t) g -
        ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * (s + t)) •
          (b.repr g n • b n)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (Real.exp (-M * (s + t)) * ‖g‖) :=
      mul_le_mul_of_nonneg_left (hN (s + t) g) (norm_nonneg _)
    _ = _ := by ring

end SpectralHeat

/-- The finite spectral-tail estimate holds for the actual weighted Dirichlet basis. -/
theorem exists_dirichletHilbert_heat_finite_tail (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      (∀ n, b n = J (u n)) ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ‖SpectralHeat.heatOperator b eigenvalue hpos t f -
          ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * t) • (b.repr f n • b n)‖ ≤
          Real.exp (-M * t) * ‖f‖ := by
  dsimp only
  obtain ⟨eigenvalue, u, hpos, hlim, he, hspan, _hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let b := HilbertBasis.mk he (le_of_eq hspan.symm)
  refine ⟨eigenvalue, u, b, fun n => (hpos n).le, hpos, hlim, ?_, ?_⟩
  · intro n
    exact congrFun (HilbertBasis.coe_mk he (le_of_eq hspan.symm)) n
  · intro M
    exact SpectralHeat.heatOperator_finite_tail b eigenvalue (fun n => (hpos n).le) hlim M

/-- The two-time finite-mode approximation for the weighted Dirichlet basis. -/
theorem exists_dirichletHilbert_heat_two_times_finite_tail (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      (∀ n, b n = J (u n)) ∧
      ∀ M : ℝ, ∃ N : ℕ, ∀ (s t : ℝ≥0) (f g : Lp ℝ 2 (dirichletVolume ρ R)),
        |inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
            (SpectralHeat.heatOperator b eigenvalue hpos t g) -
          ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * (s + t)) *
            (b.repr f n * b.repr g n)| ≤
          Real.exp (-M * (s + t)) * (‖f‖ * ‖g‖) := by
  dsimp only
  obtain ⟨eigenvalue, u, b, hpos, hpositive, hlim, hb, _⟩ :=
    exists_dirichletHilbert_heat_finite_tail hd hκ h R hR
  exact ⟨eigenvalue, u, b, hpos, hpositive, hlim, hb,
    SpectralHeat.heatOperator_two_times_finite_tail b eigenvalue hpos hlim⟩

/-- A sequence escaping to infinity has a least value separated from all
strictly larger values. The least value may have arbitrary finite multiplicity. -/
theorem spectral_minimum_and_gap (eigenvalue : ℕ → ℝ)
    (hlim : Tendsto eigenvalue atTop atTop) :
    ∃ j : ℕ, (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ n, eigenvalue n = eigenvalue j ∨
        eigenvalue j + δ ≤ eigenvalue n := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.1 hlim) (eigenvalue 0 + 1))
  let S := (Finset.range (N + 1)).image eigenvalue
  have hS : S.Nonempty := ⟨eigenvalue 0, Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
  obtain ⟨j, hj, hjeq⟩ := Finset.mem_image.mp (Finset.min'_mem S hS)
  have hmin (n : ℕ) : eigenvalue j ≤ eigenvalue n := by
    by_cases hn : n < N + 1
    · rw [hjeq]
      exact Finset.min'_le S _ (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩)
    · have hzero : eigenvalue j ≤ eigenvalue 0 := by
        rw [hjeq]
        exact Finset.min'_le S _ (Finset.mem_image.mpr
          ⟨0, Finset.mem_range.mpr (by omega), rfl⟩)
      have hn' : N ≤ n := by omega
      linarith [hN n hn']
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.1 hlim) (eigenvalue j + 1))
  let T := insert (1 : ℝ) (((Finset.range K).filter
    (fun n => eigenvalue j < eigenvalue n)).image (fun n => eigenvalue n - eigenvalue j))
  have hT : T.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let δ := T.min' hT
  have hδ : 0 < δ := by
    have hm := Finset.min'_mem T hT
    simp only [T, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
      Finset.mem_range] at hm
    rcases hm with h | ⟨n, ⟨_, hn⟩, heq⟩
    · change 0 < T.min' hT
      rw [h]
      norm_num
    · change 0 < T.min' hT
      rw [← heq]
      linarith
  refine ⟨j, hmin, δ, hδ, ?_⟩
  intro n
  by_cases heq : eigenvalue n = eigenvalue j
  · exact Or.inl heq
  · right
    by_cases hn : n < K
    · have hlt : eigenvalue j < eigenvalue n := lt_of_le_of_ne (hmin n) (Ne.symm heq)
      have hmem : eigenvalue n - eigenvalue j ∈ T := by
        simp only [T, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
          Finset.mem_range]
        exact Or.inr ⟨n, ⟨hn, hlt⟩, rfl⟩
      have hd := Finset.min'_le T _ hmem
      change δ ≤ eigenvalue n - eigenvalue j at hd
      linarith
    · have hd : δ ≤ 1 := Finset.min'_le T _ (Finset.mem_insert_self _ _)
      have hk : K ≤ n := by omega
      linarith [hK n hk]

#print axioms spectral_minimum_and_gap

/-- The actual weighted Dirichlet spectrum has a lowest eigenvalue, separated
from all distinct spectral values; no simplicity or sign assertion is made. -/
theorem exists_dirichletHilbert_spectral_minimum_and_gap (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (j : ℕ) (δ : ℝ),
      0 < δ ∧ (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      Orthonormal ℝ (fun n => J (u n)) ∧
      (Submodule.span ℝ (Set.range (fun n => J (u n)))).topologicalClosure = ⊤ ∧
      (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      ∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v) := by
  dsimp only
  obtain ⟨eigenvalue, u, hp, hl, ho, hs, hv⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  obtain ⟨j, hm, δ, hδ, hg⟩ := spectral_minimum_and_gap eigenvalue hl
  exact ⟨eigenvalue, u, j, δ, hδ, hp, hl, ho, hs, hm, hg, hv⟩

#print axioms exists_dirichletHilbert_spectral_minimum_and_gap

/-- The complete lowest eigenspace gives the leading finite spectral pairing;
all other modes decay at the strictly faster rate supplied by the gap. -/
theorem heat_two_times_lowest_eigenspace_tail
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (hlim : Tendsto eigenvalue atTop atTop)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) :
    ∃ S : Finset ℕ, (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      ∀ (s t : ℝ≥0) (f g : H),
        |inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
            (SpectralHeat.heatOperator b eigenvalue hpos t g) -
          Real.exp (-eigenvalue j * (s + t)) *
            ∑ n ∈ S, b.repr f n * b.repr g n| ≤
        Real.exp (-(eigenvalue j + δ) * (s + t)) * (‖f‖ * ‖g‖) := by
  classical
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.1 hlim) (eigenvalue j + δ))
  let S := (Finset.range N).filter (fun n => eigenvalue n = eigenvalue j)
  have hS (n : ℕ) : n ∈ S ↔ eigenvalue n = eigenvalue j := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro heq
      refine ⟨?_, heq⟩
      by_contra hn
      have hn' : N ≤ n := Nat.le_of_not_gt hn
      have := hN n hn'
      linarith
  refine ⟨S, hS, ?_⟩
  intro s t f g
  let τ := s + t
  let a : ℕ → ℝ := fun n => if n ∈ S then 0 else Real.exp (-eigenvalue n * τ)
  have ha : ∀ n, |a n| ≤ Real.exp (-(eigenvalue j + δ) * τ) := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn, (Real.exp_pos _).le]
    · simp only [a, hn, ite_false, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hg : eigenvalue j + δ ≤ eigenvalue n := by
        rcases hgap n with heq | heq
        · exact False.elim (hn ((hS n).2 heq))
        · exact heq
      exact mul_le_mul_of_nonneg_right (neg_le_neg hg) τ.coe_nonneg
  have heq : SpectralHeat.heatOperator b eigenvalue hpos τ g -
      ∑ n ∈ S, Real.exp (-eigenvalue j * τ) • (b.repr g n • b n) =
      SpectralHeat.multiplier b a (Real.exp (-(eigenvalue j + δ) * τ))
        (Real.exp_pos _).le ha g := by
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [map_sub]
    simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [SpectralHeat.heatOperator_repr, SpectralHeat.multiplier_repr]
    simp only [map_sum, map_smul, b.repr_self, lp.coeFn_smul, Pi.smul_apply,
      lp.coeFn_sum, Finset.sum_apply, lp.single_apply, smul_eq_mul]
    by_cases hn : n ∈ S
    · simp only [a, hn, ite_true, zero_mul, sub_eq_zero]
      rw [Finset.sum_eq_single n]
      · rw [(hS n).1 hn]
        simp
      · intro x _ hxn
        simp [hxn]
      · exact fun h => (h hn).elim
    · simp only [a, hn, ite_false, sub_eq_self]
      apply Finset.sum_eq_zero
      intro x hx
      have hxn : x ≠ n := by
        intro h
        subst x
        exact hn hx
      simp [hxn]
  have htail : ‖SpectralHeat.heatOperator b eigenvalue hpos τ g -
      ∑ n ∈ S, Real.exp (-eigenvalue j * τ) • (b.repr g n • b n)‖ ≤
      Real.exp (-(eigenvalue j + δ) * τ) * ‖g‖ := by
    rw [heq]
    exact SpectralHeat.multiplier_norm_le b a _ _ ha g
  have hp : inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
      (SpectralHeat.heatOperator b eigenvalue hpos t g) =
      inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos τ g) := by
    rw [SpectralHeat.heatOperator_symmetric, SpectralHeat.heatOperator_add,
      ContinuousLinearMap.comp_apply]
  have hs : inner ℝ f (∑ n ∈ S, Real.exp (-eigenvalue j * τ) •
      (b.repr g n • b n)) = Real.exp (-eigenvalue j * τ) *
      ∑ n ∈ S, b.repr f n * b.repr g n := by
    simp only [inner_sum, real_inner_smul_right, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [b.repr_apply_apply, real_inner_comm f (b n)]
    ring
  dsimp only [τ, NNReal.coe_add] at hs htail
  rw [hp, ← hs, ← inner_sub_right]
  calc
    _ ≤ ‖f‖ * ‖SpectralHeat.heatOperator b eigenvalue hpos τ g -
        ∑ n ∈ S, Real.exp (-eigenvalue j * τ) • (b.repr g n • b n)‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖f‖ * (Real.exp (-(eigenvalue j + δ) * τ) * ‖g‖) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by
      dsimp only [τ, NNReal.coe_add]
      ring

#print axioms heat_two_times_lowest_eigenspace_tail

/-- Rescaled heat converges at the gap rate to the complete finite lowest
spectral projection, including every mode of a multiple lowest eigenvalue. -/
theorem rescaled_heat_lowest_projection_norm_le
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
    (S : Finset ℕ) (hS : ∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n)
    (t : ℝ≥0) (f : H) :
    ‖Real.exp (eigenvalue j * t) • SpectralHeat.heatOperator b eigenvalue hpos t f -
      ∑ n ∈ S, b.repr f n • b n‖ ≤ Real.exp (-δ * t) * ‖f‖ := by
  classical
  let a : ℕ → ℝ := fun n => if n ∈ S then 0 else
    Real.exp ((eigenvalue j - eigenvalue n) * t)
  have ha : ∀ n, |a n| ≤ Real.exp (-δ * t) := by
    intro n
    by_cases hn : n ∈ S
    · simp [a, hn, (Real.exp_pos _).le]
    · simp only [a, hn, ite_false, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hg : eigenvalue j + δ ≤ eigenvalue n := by
        rcases hgap n with heq | heq
        · exact False.elim (hn ((hS n).2 heq))
        · exact heq
      exact mul_le_mul_of_nonneg_right (by linarith) t.coe_nonneg
  have heq : Real.exp (eigenvalue j * t) •
      SpectralHeat.heatOperator b eigenvalue hpos t f -
      ∑ n ∈ S, b.repr f n • b n =
      SpectralHeat.multiplier b a (Real.exp (-δ * t)) (Real.exp_pos _).le ha f := by
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [map_sub, map_smul]
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [SpectralHeat.heatOperator_repr, SpectralHeat.multiplier_repr]
    simp only [map_sum, map_smul, b.repr_self, lp.coeFn_smul, Pi.smul_apply,
      lp.coeFn_sum, Finset.sum_apply, lp.single_apply, smul_eq_mul]
    have hexp : Real.exp (eigenvalue j * t) * Real.exp (-eigenvalue n * t) =
        Real.exp ((eigenvalue j - eigenvalue n) * t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← mul_assoc, hexp]
    by_cases hn : n ∈ S
    · simp only [a, hn, ite_true, zero_mul, sub_eq_zero]
      rw [Finset.sum_eq_single n]
      · rw [(hS n).1 hn]
        simp
      · intro x _ hxn
        simp [hxn]
      · exact fun h => (h hn).elim
    · simp only [a, hn, ite_false, sub_eq_self]
      apply Finset.sum_eq_zero
      intro x hx
      have hxn : x ≠ n := by
        intro h
        subst x
        exact hn hx
      simp [hxn]
  rw [heq]
  exact SpectralHeat.multiplier_norm_le b a _ _ ha f

#print axioms rescaled_heat_lowest_projection_norm_le

/-- Strong convergence of the rescaled heat to its full lowest projection. -/
theorem rescaled_heat_tendsto_lowest_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (S : Finset ℕ) (hS : ∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n)
    (f : H) :
    Tendsto (fun t : ℝ≥0 => Real.exp (eigenvalue j * t) •
      SpectralHeat.heatOperator b eigenvalue hpos t f) atTop
      (𝓝 (∑ n ∈ S, b.repr f n • b n)) := by
  have hco : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hmul : Tendsto (fun t : ℝ≥0 => δ * (t : ℝ)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hδ).mpr hco
  have hdecay : Tendsto (fun t : ℝ≥0 => Real.exp (-δ * t) * ‖f‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, neg_mul, zero_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul).mul_const ‖f‖
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun t => rescaled_heat_lowest_projection_norm_le b eigenvalue hpos j δ S hS hgap t f)
    hdecay

#print axioms rescaled_heat_tendsto_lowest_projection

/-- Native weighted Dirichlet heat converges to the complete lowest spectral
projection for the eigenbasis obtained from the elliptic operator. -/
theorem exists_dirichletHilbert_rescaled_heat_tendsto_lowest_projection (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (S : Finset ℕ),
      0 < δ ∧ (∀ n, 0 < eigenvalue n) ∧ (∀ n, b n = J (u n)) ∧
      (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v)) ∧
      (∀ t : ℝ≥0, ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        ‖Real.exp (eigenvalue j * t) • SpectralHeat.heatOperator b eigenvalue hpos t f -
          ∑ n ∈ S, b.repr f n • b n‖ ≤ Real.exp (-δ * t) * ‖f‖) ∧
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        Tendsto (fun t : ℝ≥0 => Real.exp (eigenvalue j * t) •
          SpectralHeat.heatOperator b eigenvalue hpos t f) atTop
          (𝓝 (∑ n ∈ S, b.repr f n • b n)) := by
  dsimp only
  obtain ⟨eigenvalue, u, j, δ, hδ, hp, hl, ho, hs, hm, hg, hv⟩ :=
    exists_dirichletHilbert_spectral_minimum_and_gap hd hκ h R hR
  let b := HilbertBasis.mk ho (le_of_eq hs.symm)
  have hb (n : ℕ) : b n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) :=
    congrFun (HilbertBasis.coe_mk ho (le_of_eq hs.symm)) n
  obtain ⟨S, hS, _⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    (fun n => (hp n).le) hl j δ hδ hg
  exact ⟨eigenvalue, u, b, fun n => (hp n).le, j, δ, S, hδ, hp, hb, hm, hS, hv,
    rescaled_heat_lowest_projection_norm_le b eigenvalue _ j δ S hS hg,
    rescaled_heat_tendsto_lowest_projection b eigenvalue _ j δ hδ S hS hg⟩

#print axioms exists_dirichletHilbert_rescaled_heat_tendsto_lowest_projection

/-- A one-dimensional finite spectral projection is independent of the sign
or enumeration of its unit spanning vector. -/
theorem lowest_eigenspace_coefficient_of_unit_span
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (S : Finset ℕ) (hS : S.card = 1)
    (u : H) (hu : u ∈ Submodule.span ℝ (b '' (S : Set ℕ)))
    (hu_norm : ‖u‖ = 1) (f g : H) :
    (∑ n ∈ S, b.repr f n * b.repr g n) =
      inner ℝ f u * inner ℝ g u := by
  classical
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hS
  subst S
  have hu' : u ∈ Submodule.span ℝ {b k} := by simpa using hu
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hu'
  have hcabs : |c| = 1 := by
    rw [← hc, norm_smul, Real.norm_eq_abs, b.orthonormal.norm_eq_one, mul_one] at hu_norm
    exact hu_norm
  have hc2 : c * c = 1 := by nlinarith [sq_abs c]
  rw [← hc]
  simp only [Finset.sum_singleton, b.repr_apply_apply, real_inner_comm (b k),
    real_inner_smul_right]
  calc
    _ = (c * c) * (inner ℝ (b k) f * inner ℝ (b k) g) := by rw [hc2]; ring
    _ = _ := by ring

#print axioms lowest_eigenspace_coefficient_of_unit_span

/-- With a simple lowest eigenspace and any unit vector spanning it, the
actual spectral tail is controlled relative to its basis-independent coefficient. -/
theorem heat_two_times_ground_vector_tail
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (hlim : Tendsto eigenvalue atTop atTop)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n)
    (hsimple : ∀ n, eigenvalue n = eigenvalue j → n = j)
    (u : H) (hu : u ∈ Submodule.span ℝ {b j}) (hu_norm : ‖u‖ = 1) :
    ∀ (s t : ℝ≥0) (f g : H),
      |inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
          (SpectralHeat.heatOperator b eigenvalue hpos t g) -
        Real.exp (-eigenvalue j * (s + t)) * (inner ℝ f u * inner ℝ g u)| ≤
      Real.exp (-(eigenvalue j + δ) * (s + t)) * (‖f‖ * ‖g‖) := by
  classical
  obtain ⟨S, hS, ht⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    hpos hlim j δ hδ hgap
  have hSj : S = {j} := by
    ext n
    simp only [Finset.mem_singleton, hS]
    constructor
    · exact hsimple n
    · intro hn
      subst n
      rfl
  have hcard : S.card = 1 := by simp [hSj]
  have hu' : u ∈ Submodule.span ℝ (b '' (S : Set ℕ)) := by simpa [hSj] using hu
  intro s t f g
  have hc := lowest_eigenspace_coefficient_of_unit_span b S hcard u hu' hu_norm f g
  simpa only [hc] using ht s t f g

#print axioms heat_two_times_ground_vector_tail

/-- The finite spectral coefficient is the pairing with the full spectral projection. -/
theorem lowest_eigenspace_coefficient_eq_projection
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (S : Finset ℕ) (f g : H) :
    (∑ n ∈ S, b.repr f n * b.repr g n) =
      inner ℝ f (∑ n ∈ S, b.repr g n • b n) := by
  simp only [inner_sum, real_inner_smul_right, b.repr_apply_apply,
    real_inner_comm f]
  apply Finset.sum_congr rfl
  intro n hn
  ring

#print axioms lowest_eigenspace_coefficient_eq_projection

/-- A positive leading coefficient dominates the faster exponential tail after
an explicit time depending on the coefficient, the norms, and the gap. -/
theorem exponential_tail_lower_bound
    (lam δ c N τ x : ℝ) (hδ : 0 < δ) (hc : 0 < c) (hN : 0 ≤ N)
    (ht : Real.log (1 + 2 * N / c) / δ ≤ τ)
    (h : |x - Real.exp (-lam * τ) * c| ≤
      Real.exp (-(lam + δ) * τ) * N) :
    Real.exp (-lam * τ) * (c / 2) ≤ x := by
  have hA : 0 < 1 + 2 * N / c := by positivity
  have htime : Real.log (1 + 2 * N / c) ≤ δ * τ := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp ht
  have hexp : Real.exp (-δ * τ) ≤ (1 + 2 * N / c)⁻¹ := by
    rw [← Real.exp_log hA, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    linarith
  have hsmall : Real.exp (-δ * τ) * N ≤ c / 2 := by
    have hm := mul_le_mul_of_nonneg_right hexp hN
    have haux : (1 + 2 * N / c)⁻¹ * N ≤ c / 2 := by
      rw [inv_mul_le_iff₀ hA]
      field_simp
      nlinarith
    exact le_trans hm haux
  have hexp' : Real.exp (-(lam + δ) * τ) =
      Real.exp (-lam * τ) * Real.exp (-δ * τ) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp'] at h
  have htail := (abs_le.mp h).1
  have hm := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos (-lam * τ)).le
  nlinarith

#print axioms exponential_tail_lower_bound

/-- Lower pairing bound for the complete lowest eigenspace, with no simplicity
assumption and no uniformity claim on the spectral gap or coefficient. -/
theorem heat_two_times_lowest_eigenspace_lower
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ eigenvalue n) (hlim : Tendsto eigenvalue atTop atTop)
    (j : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) :
    ∃ S : Finset ℕ, (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      ∀ (s t : ℝ≥0) (f g : H),
        let c := ∑ n ∈ S, b.repr f n * b.repr g n
        0 < c →
        Real.log (1 + 2 * (‖f‖ * ‖g‖) / c) / δ ≤ (s : ℝ) + t →
        Real.exp (-eigenvalue j * ((s : ℝ) + t)) * (c / 2) ≤
          inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
            (SpectralHeat.heatOperator b eigenvalue hpos t g) := by
  obtain ⟨S, hS, htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    hpos hlim j δ hδ hgap
  refine ⟨S, hS, ?_⟩
  intro s t f g
  dsimp only
  intro hc ht
  exact exponential_tail_lower_bound (eigenvalue j) δ _ _ _ _ hδ hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ht (htail s t f g)

#print axioms heat_two_times_lowest_eigenspace_lower

/-- Actual weighted Dirichlet heat pairings admit a finite lowest-eigenspace
leading term and an exponentially faster tail, including multiplicity. -/
theorem exists_dirichletHilbert_heat_lowest_eigenspace_tail (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (S : Finset ℕ),
      0 < δ ∧ (∀ n, 0 < eigenvalue n) ∧ (∀ n, b n = J (u n)) ∧
      (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v)) ∧
      ∀ (s t : ℝ≥0) (f g : Lp ℝ 2 (dirichletVolume ρ R)),
        |inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
            (SpectralHeat.heatOperator b eigenvalue hpos t g) -
          Real.exp (-eigenvalue j * (s + t)) *
            ∑ n ∈ S, b.repr f n * b.repr g n| ≤
        Real.exp (-(eigenvalue j + δ) * (s + t)) * (‖f‖ * ‖g‖) := by
  dsimp only
  obtain ⟨eigenvalue, u, j, δ, hδ, hp, hl, ho, hs, hm, hg, hv⟩ :=
    exists_dirichletHilbert_spectral_minimum_and_gap hd hκ h R hR
  let b := HilbertBasis.mk ho (le_of_eq hs.symm)
  have hb (n : ℕ) : b n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) :=
    congrFun (HilbertBasis.coe_mk ho (le_of_eq hs.symm)) n
  obtain ⟨S, hS, ht⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    (fun n => (hp n).le) hl j δ hδ hg
  exact ⟨eigenvalue, u, b, fun n => (hp n).le, j, δ, S, hδ, hp, hb, hm, hS, hv, ht⟩

#print axioms exists_dirichletHilbert_heat_lowest_eigenspace_tail

/-- The quantitative lower bound for the actual weighted Dirichlet spectrum.
The gap and coefficient are allowed to depend on the given operator and tests. -/
theorem exists_dirichletHilbert_heat_lowest_eigenspace_lower (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (S : Finset ℕ),
      0 < δ ∧ (∀ n, 0 < eigenvalue n) ∧ (∀ n, b n = J (u n)) ∧
      (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v)) ∧
      ∀ (s t : ℝ≥0) (f g : Lp ℝ 2 (dirichletVolume ρ R)),
        let c := ∑ n ∈ S, b.repr f n * b.repr g n
        0 < c →
        Real.log (1 + 2 * (‖f‖ * ‖g‖) / c) / δ ≤ (s : ℝ) + t →
        Real.exp (-eigenvalue j * ((s : ℝ) + t)) * (c / 2) ≤
          inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
            (SpectralHeat.heatOperator b eigenvalue hpos t g) := by
  dsimp only
  obtain ⟨eigenvalue, u, b, hpos, j, δ, S, hδ, hp, hb, hm, hS, hv, ht⟩ :=
    exists_dirichletHilbert_heat_lowest_eigenspace_tail hd hκ h R hR
  refine ⟨eigenvalue, u, b, hpos, j, δ, S, hδ, hp, hb, hm, hS, hv, ?_⟩
  intro s t f g hc htime
  exact exponential_tail_lower_bound (eigenvalue j) δ _ _ _ _ hδ hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) htime (ht s t f g)

#print axioms exists_dirichletHilbert_heat_lowest_eigenspace_lower

/-- The actual uniformly elliptic Dirichlet energy generates a strongly continuous,
contractive symmetric spectral heat semigroup. Its positive-time operators are
compact and injective, and its basis vectors are genuine zero-trace H¹ solutions. -/
theorem exists_dirichletHilbert_heatSemigroup (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (P : ℝ≥0 → Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R)),
      (∀ n, 0 < eigenvalue n) ∧ Tendsto eigenvalue atTop atTop ∧
      (∀ n, b n = J (u n)) ∧
      (∀ n, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => v.val (some i) x)) =
          eigenvalue n * inner ℝ (J (u n)) (J v)) ∧
      P 0 = ContinuousLinearMap.id ℝ _ ∧
      (∀ s t, P (s + t) = (P s).comp (P t)) ∧
      (∀ t f, ‖P t f‖ ≤ ‖f‖) ∧
      (∀ f, Continuous (fun t => P t f)) ∧
      (∀ t f g, inner ℝ (P t f) g = inner ℝ f (P t g)) ∧
      (∀ t, Function.Injective (P t)) ∧
      (∀ t, 0 < t → IsCompactOperator (P t)) ∧
      ∀ t n, P t (b n) = Real.exp (-eigenvalue n * t) • b n := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eigenvalue, u, hpos, hlim, he, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)) :=
    HilbertBasis.mk he (le_of_eq hspan.symm)
  have hb (n : ℕ) : b n = J (u n) := by
    change (HilbertBasis.mk he (le_of_eq hspan.symm)) n = J (u n)
    exact congrFun (HilbertBasis.coe_mk he (le_of_eq hspan.symm)) n
  obtain ⟨_c, _hc, S, hcomp, _hsa, _hinj, _hdense, _hpositive, _hnorm, hS⟩ :=
    exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  have hGe (n : ℕ) : (J.comp S) (b n) = (eigenvalue n)⁻¹ • b n := by
    have hu : u n = S (eigenvalue n • J (u n)) := by
      apply (hS _ _).mpr
      intro v
      simpa only [real_inner_smul_left] using hvar n v
    have hx : b n = eigenvalue n • ((J.comp S) (b n)) := by
      rw [hb]
      change J (u n) = eigenvalue n • J (S (J (u n)))
      conv_lhs => rw [hu]
      rw [map_smul, map_smul]
    calc
      _ = (eigenvalue n)⁻¹ • (eigenvalue n • ((J.comp S) (b n))) := by
        rw [smul_smul, inv_mul_cancel₀ (hpos n).ne', one_smul]
      _ = _ := congrArg ((eigenvalue n)⁻¹ • ·) hx.symm
  refine ⟨eigenvalue, u, b, SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le),
    hpos, hlim, hb, hvar, SpectralHeat.heatOperator_zero _ _ _,
    SpectralHeat.heatOperator_add _ _ _, SpectralHeat.heatOperator_norm_le _ _ _,
    SpectralHeat.heatOperator_continuous _ _ _, SpectralHeat.heatOperator_symmetric _ _ _,
    SpectralHeat.heatOperator_injective _ _ _, ?_, SpectralHeat.heatOperator_basis _ _ _⟩
  intro t ht
  exact SpectralHeat.heatOperator_compact_of_inverse b eigenvalue hpos (J.comp S) hcomp hGe t ht

/-- Positive-time spectral heat solutions lift to the genuine zero-trace H¹
space. Their energy equation is the actual coefficient form, with a quantitative
H¹ bound and an energy bound, and their lifts respect addition of time. -/
theorem exists_dirichletHilbert_heatLift (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 < eigenvalue n)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R))) (c : ℝ),
      0 < c ∧ Tendsto eigenvalue atTop atTop ∧
      ∃ Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t ∧
        (∀ f, ‖Q t ht f‖ ≤ c⁻¹ * Real.sqrt κ⁻¹ * (t : ℝ)⁻¹ * ‖f‖) ∧
        (∀ f v,
          (∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x)) =
            inner ℝ (SpectralHeat.firstMoment b eigenvalue hpos t ht f) (J v)) ∧
        (∀ s, Q (t + s) (add_pos_of_pos_of_nonneg ht zero_le) =
          (Q t ht).comp (SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) s)) ∧
        ∀ f, (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eigenvalue, u, b, _P, hpos, hlim, hb, hvar, _hP⟩ :=
    exists_dirichletHilbert_heatSemigroup hd hκ h R hR
  obtain ⟨c, hc, S, _hcomp, _hsa, _hinj, _hdense, _hpositive, hnorm, hS⟩ :=
    exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  have hGe (n : ℕ) : (J.comp S) (b n) = (eigenvalue n)⁻¹ • b n := by
    have hu : u n = S (eigenvalue n • J (u n)) := by
      apply (hS _ _).mpr
      intro v
      simpa only [real_inner_smul_left] using hvar n v
    have hx : b n = eigenvalue n • ((J.comp S) (b n)) := by
      rw [hb]
      change J (u n) = eigenvalue n • J (S (J (u n)))
      conv_lhs => rw [hu]
      rw [map_smul, map_smul]
    calc
      _ = (eigenvalue n)⁻¹ • (eigenvalue n • ((J.comp S) (b n))) := by
        rw [smul_smul, inv_mul_cancel₀ (hpos n).ne', one_smul]
      _ = _ := congrArg ((eigenvalue n)⁻¹ • ·) hx.symm
  let Q := fun (t : ℝ≥0) (ht : 0 < t) =>
    S.comp (SpectralHeat.firstMoment b eigenvalue hpos t ht)
  have hfactor (t : ℝ≥0) (ht : 0 < t) :
      J.comp (Q t ht) = SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t := by
    exact (SpectralHeat.heatOperator_eq_inverse_comp_firstMoment
      b eigenvalue hpos (J.comp S) hGe t ht).symm
  have hform (t : ℝ≥0) (ht : 0 < t) (f) (v) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
          (fun i => v.val (some i) x)) =
        inner ℝ (SpectralHeat.firstMoment b eigenvalue hpos t ht f) (J v) :=
    (hS _ _).mp rfl v
  refine ⟨eigenvalue, hpos, b, c, hc, hlim, Q, ?_, ?_⟩
  · intro f
    exact S.continuous.comp (SpectralHeat.firstMoment_continuous b eigenvalue hpos f)
  intro t ht
  refine ⟨hfactor t ht, ?_, hform t ht, ?_, ?_⟩
  · intro f
    calc
      _ ≤ c⁻¹ * Real.sqrt κ⁻¹ *
          ‖SpectralHeat.firstMoment b eigenvalue hpos t ht f‖ := hnorm _
      _ ≤ c⁻¹ * Real.sqrt κ⁻¹ * ((t : ℝ)⁻¹ * ‖f‖) :=
        mul_le_mul_of_nonneg_left (SpectralHeat.firstMoment_norm_le _ _ _ _ _ _)
          (mul_nonneg (inv_nonneg.mpr hc.le) (Real.sqrt_nonneg _))
      _ = _ := by ring
  · intro s
    dsimp only [Q]
    rw [SpectralHeat.firstMoment_add b eigenvalue hpos t ht s]
    rfl
  · intro f
    rw [hform t ht f (Q t ht f)]
    have hJ : J (Q t ht f) =
        SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t f :=
      congrArg (fun T : _ →L[ℝ] _ => T f) (hfactor t ht)
    rw [hJ]
    calc
      _ ≤ ‖SpectralHeat.firstMoment b eigenvalue hpos t ht f‖ *
          ‖SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t f‖ :=
        real_inner_le_norm _ _
      _ ≤ ((t : ℝ)⁻¹ * ‖f‖) * ‖f‖ := mul_le_mul
        (SpectralHeat.firstMoment_norm_le _ _ _ _ _ _)
        (SpectralHeat.heatOperator_norm_le _ _ _ _ _) (norm_nonneg _)
        (mul_nonneg (inv_nonneg.mpr t.coe_nonneg) (norm_nonneg _))
      _ = _ := by ring

namespace SpectralHeat

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem firstMoment_repr (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (f : H) (n : ℕ) :
    b.repr (firstMoment b eigenvalue hpos t ht f) n =
      (eigenvalue n * Real.exp (-eigenvalue n * t)) * b.repr f n :=
  multiplier_repr _ _ _ _ _ _ _

omit [CompleteSpace H] in
/-- A fixed positive earlier time makes the generator applied to the shifted
heat flow continuous on the full real time axis, using truncation at zero. -/
theorem shiftedMoment_continuous (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (τ : ℝ≥0) (hτ : 0 < τ) (f : H) :
    Continuous (fun s : ℝ => firstMoment b eigenvalue hpos τ hτ
      (heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)) :=
  (firstMoment b eigenvalue hpos τ hτ).continuous.comp
    ((heatOperator_continuous b eigenvalue (fun n => (hpos n).le) f).comp
      continuous_real_toNNReal)

/-- Integrating the first spectral moment gives the actual Hilbert-valued
increment of the heat flow. The proof uses the scalar fundamental theorem of
calculus in each coordinate of the complete orthonormal basis. -/
theorem integral_shiftedMoment (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (τ : ℝ≥0) (hτ : 0 < τ)
    (t : ℝ) (ht : 0 ≤ t) (f : H) :
    (∫ s in (0 : ℝ)..t, firstMoment b eigenvalue hpos τ hτ
      (heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)) =
      heatOperator b eigenvalue (fun n => (hpos n).le) τ f -
        heatOperator b eigenvalue (fun n => (hpos n).le) (τ + t.toNNReal) f := by
  have hc := shiftedMoment_continuous b eigenvalue hpos τ hτ f
  apply b.repr.injective
  apply lp.ext
  funext n
  simp only [b.repr_apply_apply]
  change (innerSL ℝ (b n)) (∫ s in (0 : ℝ)..t, firstMoment b eigenvalue hpos τ hτ
    (heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)) = _
  rw [← (innerSL ℝ (b n)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 t)]
  simp only [innerSL_apply_apply, ← b.repr_apply_apply]
  have hd (s : ℝ) : HasDerivAt
      (fun r : ℝ => -Real.exp (-eigenvalue n * ((τ : ℝ) + r)) * b.repr f n)
      (eigenvalue n * Real.exp (-eigenvalue n * ((τ : ℝ) + s)) * b.repr f n) s := by
    convert (((((hasDerivAt_id s).const_add (τ : ℝ)).const_mul (-eigenvalue n)).exp).neg.mul_const
      (b.repr f n)) using 1
    · funext r
      simp only [Pi.neg_apply, id_eq]
    · simp only [id_eq]
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s)
    (show IntervalIntegrable
      (fun s : ℝ => eigenvalue n * Real.exp (-eigenvalue n * ((τ : ℝ) + s)) * b.repr f n)
      volume 0 t from (by fun_prop : Continuous _).intervalIntegrable 0 t)
  calc
    _ = ∫ s in (0 : ℝ)..t,
        eigenvalue n * Real.exp (-eigenvalue n * ((τ : ℝ) + s)) * b.repr f n := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs' : 0 ≤ s := (Set.mem_Icc.mp (by simpa [Set.uIcc_of_le ht] using hs)).1
      change b.repr (firstMoment b eigenvalue hpos τ hτ
        (heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)) n = _
      dsimp only
      rw [firstMoment_repr, heatOperator_repr, Real.coe_toNNReal s hs', mul_add, Real.exp_add]
      ring
    _ = _ := by
      rw [hi, map_sub]
      change _ = b.repr (heatOperator b eigenvalue (fun n => (hpos n).le) τ f) n -
        b.repr (heatOperator b eigenvalue (fun n => (hpos n).le) (τ + t.toNNReal) f) n
      rw [heatOperator_repr, heatOperator_repr, NNReal.coe_add, Real.coe_toNNReal t ht]
      simp only [add_zero]
      ring

/-- After a strictly positive initial time, the heat flow is differentiable in
Hilbert space and its derivative is the negative first spectral moment. -/
theorem heatOperator_shift_hasDerivAt (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 < eigenvalue n)
    (τ : ℝ≥0) (hτ : 0 < τ) (t : ℝ) (ht : 0 < t) (f : H) :
    HasDerivAt
      (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le)
        (τ + s.toNNReal) f)
      (-firstMoment b eigenvalue hpos (τ + t.toNNReal)
        (add_pos_of_pos_of_nonneg hτ zero_le) f) t := by
  have hc := shiftedMoment_continuous b eigenvalue hpos τ hτ f
  have hi := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hd := (hi.const_sub
    (heatOperator b eigenvalue (fun n => (hpos n).le) τ f)).congr_of_eventuallyEq
    (show (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le)
      (τ + s.toNNReal) f) =ᶠ[𝓝 t]
      (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le) τ f -
        ∫ r in (0 : ℝ)..s, firstMoment b eigenvalue hpos τ hτ
          (heatOperator b eigenvalue (fun n => (hpos n).le) r.toNNReal f)) from by
      filter_upwards [eventually_gt_nhds ht] with s hs
      rw [integral_shiftedMoment b eigenvalue hpos τ hτ s hs.le f]
      abel)
  simpa only [firstMoment_add b eigenvalue hpos τ hτ t.toNNReal,
    ContinuousLinearMap.comp_apply] using hd

/-- The actual strongly continuous spectral heat semigroup has a strong time
derivative at every positive time, with no assumption on its initial vector. -/
theorem heatOperator_hasDerivAt (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ)
    (hpos : ∀ n, 0 < eigenvalue n) (t : ℝ≥0) (ht : 0 < t) (f : H) :
    HasDerivAt
      (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)
      (-firstMoment b eigenvalue hpos t ht f) (t : ℝ) := by
  let τ : ℝ≥0 := ⟨(t : ℝ) / 2, by positivity⟩
  have hτ : 0 < τ := by change 0 < (t : ℝ) / 2; exact half_pos ht
  have hτt : (τ : ℝ) < t := by change (t : ℝ) / 2 < t; exact half_lt_self ht
  have hr : 0 < (t : ℝ) - τ := sub_pos.mpr hτt
  have hsum : τ + ((t : ℝ) - τ).toNNReal = t := by
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal _ hr.le]
    ring
  have hd := (heatOperator_shift_hasDerivAt b eigenvalue hpos τ hτ
    ((t : ℝ) - τ) hr f).scomp (t : ℝ) ((hasDerivAt_id (t : ℝ)).sub_const (τ : ℝ))
  have heq :
      (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)
        =ᶠ[𝓝 (t : ℝ)]
      (fun s : ℝ => heatOperator b eigenvalue (fun n => (hpos n).le)
        (τ + (s - τ).toNNReal) f) := by
    filter_upwards [eventually_gt_nhds hτt] with s hs
    apply congrArg (fun r : ℝ≥0 =>
      heatOperator b eigenvalue (fun n => (hpos n).le) r f)
    apply NNReal.coe_injective
    rw [NNReal.coe_add, Real.coe_toNNReal s (le_trans τ.coe_nonneg hs.le),
      Real.coe_toNNReal _ (sub_nonneg.mpr hs.le)]
    ring
  simpa only [hsum, one_smul] using hd.congr_of_eventuallyEq heq

end SpectralHeat

/-- The genuine supported H¹ heat flow solves the time-dependent variational
equation against every member of its actual Dirichlet form domain. Its initial
condition is attained strongly in weighted L². -/
theorem exists_dirichletHilbert_weakHeatFlow (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 < eigenvalue n)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R))),
      Tendsto eigenvalue atTop atTop ∧
      ∃ Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      (∀ f, Continuous (fun t : ℝ≥0 =>
        SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t f)) ∧
      (∀ f, SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) 0 f = f) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t ∧
        (∀ f, ‖J (Q t ht f)‖ ≤ ‖f‖) ∧
        (∀ f, (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2) ∧
        (∀ f, HasDerivAt
          (fun s : ℝ => ‖SpectralHeat.heatOperator b eigenvalue
            (fun n => (hpos n).le) s.toNNReal f‖ ^ 2)
          (-2 * (∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => (Q t ht f).val (some i) x))) (t : ℝ)) ∧
        ∀ f v, HasDerivAt
          (fun s : ℝ => inner ℝ
            (SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f)
            (J v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eigenvalue, hpos, b, c, hc, hlim, Q, hcont, hQ⟩ :=
    exists_dirichletHilbert_heatLift hd hκ h R hR
  refine ⟨eigenvalue, hpos, b, hlim, Q, hcont, ?_, ?_, ?_⟩
  · exact fun f => SpectralHeat.heatOperator_continuous b eigenvalue
      (fun n => (hpos n).le) f
  · intro f
    rw [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply]
  intro t ht
  obtain ⟨hfactor, _hnorm, hform, _hadd, henergy⟩ := hQ t ht
  refine ⟨hfactor, ?_, henergy, ?_, ?_⟩
  · intro f
    have heq := congrArg (fun T : _ →L[ℝ] _ => T f) hfactor
    change J (Q t ht f) = _ at heq
    rw [heq]
    exact SpectralHeat.heatOperator_norm_le b eigenvalue (fun n => (hpos n).le) t f
  · intro f
    have hnorm := (SpectralHeat.heatOperator_hasDerivAt b eigenvalue hpos t ht f).norm_sq
    have hJ := congrArg (fun T : _ →L[ℝ] _ => T f) hfactor
    change J (Q t ht f) = _ at hJ
    have hi : inner ℝ
        (SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t f)
        (SpectralHeat.firstMoment b eigenvalue hpos t ht f) =
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) := by
      rw [real_inner_comm, ← hJ]
      exact (hform f (Q t ht f)).symm
    simpa only [Real.toNNReal_coe, inner_neg_right, hi, mul_neg, neg_mul] using hnorm
  intro f v
  have hderiv := (innerSL ℝ (J v)).hasFDerivAt.comp_hasDerivAt (t : ℝ)
    (SpectralHeat.heatOperator_hasDerivAt b eigenvalue hpos t ht f)
  change HasDerivAt
    (fun s : ℝ => inner ℝ (J v)
      (SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f))
    (inner ℝ (J v) (-SpectralHeat.firstMoment b eigenvalue hpos t ht f)) (t : ℝ)
    at hderiv
  have hpair : HasDerivAt
      (fun s : ℝ => inner ℝ
        (SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) s.toNNReal f) (J v))
      (-inner ℝ (SpectralHeat.firstMoment b eigenvalue hpos t ht f) (J v)) (t : ℝ) := by
    simpa only [Function.comp_apply, innerSL_apply_apply, inner_neg_right,
      real_inner_comm] using hderiv
  rw [← hform f v] at hpair
  exact hpair

namespace SpectralHeat

/-- A continuous scalar evolution on nonnegative times is determined by its
positive-time linear differential equation, without a derivative at time zero. -/
theorem eq_exp_mul_of_hasDerivAt_neg_mul (a : ℝ) (f : ℝ≥0 → ℝ)
    (hcont : Continuous f)
    (hderiv : ∀ t : ℝ≥0, 0 < t → HasDerivAt
      (fun s : ℝ => f s.toNNReal) (-a * f t) (t : ℝ)) (t : ℝ≥0) :
    f t = Real.exp (-a * t) * f 0 := by
  let q : ℝ → ℝ := fun s => Real.exp (a * s) * f s.toNNReal
  have hqcont : Continuous q :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hcont.comp continuous_real_toNNReal)
  have hqderiv (s : ℝ) (hs : 0 < s) : HasDerivAt q 0 s := by
    have hd := hderiv ⟨s, hs.le⟩ hs
    have he := ((hasDerivAt_id s).const_mul a).exp
    have harg : s.toNNReal = ⟨s, hs.le⟩ := by
      apply NNReal.coe_injective
      exact Real.coe_toNNReal s hs.le
    convert he.mul hd using 1
    · rfl
    · simp only [id_eq, mul_one, harg]
      ring
  have hconst (s : ℝ) (hs : 0 < s) : q s = q 1 := by
    exact isOpen_Ioi.is_const_of_deriv_eq_zero (convex_Ioi (0 : ℝ)).isPreconnected
      (fun s hs => (hqderiv s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hqderiv s hs).deriv) hs (by norm_num)
  have hzero : q 0 = q 1 :=
    hqcont.continuousAt.continuousWithinAt.eq_const_of_mem_closure
      (s := Set.Ioi (0 : ℝ))
      (by rw [closure_Ioi]; exact le_refl (0 : ℝ)) (fun s hs => hconst s hs)
  have hqt : q (t : ℝ) = f 0 := by
    by_cases ht : t = 0
    · subst t
      simp [q]
    · have heq := (hconst (t : ℝ) (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht))).trans
        hzero.symm
      simpa only [q, mul_zero, Real.exp_zero, Real.toNNReal_zero, one_mul] using heq
  have heq := congrArg (fun x : ℝ => Real.exp (-a * t) * x) hqt
  have hexp : Real.exp (-a * t) * Real.exp (a * t) = 1 := by
    rw [← Real.exp_add, show -a * (t : ℝ) + a * t = 0 by ring, Real.exp_zero]
  simpa only [q, Real.toNNReal_coe, ← mul_assoc, hexp, one_mul] using heq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The scalar weak equations against a complete orthonormal basis determine
an evolution, with only strong continuity at time zero required. -/
theorem heatOperator_eq_of_weakEvolution (b : HilbertBasis ℕ ℝ H)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (F : ℝ≥0 → H) (hcont : Continuous F)
    (hweak : ∀ t : ℝ≥0, 0 < t → ∀ n, HasDerivAt
      (fun s : ℝ => inner ℝ (b n) (F s.toNNReal))
      (-eigenvalue n * inner ℝ (b n) (F t)) (t : ℝ)) (t : ℝ≥0) :
    F t = heatOperator b eigenvalue hpos t (F 0) := by
  apply b.repr.injective
  apply lp.ext
  funext n
  rw [heatOperator_repr, b.repr_apply_apply, b.repr_apply_apply]
  exact eq_exp_mul_of_hasDerivAt_neg_mul (eigenvalue n)
    (fun s => inner ℝ (b n) (F s)) (continuous_const.inner hcont)
    (fun s hs => hweak s hs n) t

end SpectralHeat

/-- Two strongly continuous weighted-L² evolutions satisfying the actual
Dirichlet heat equation against every genuine supported H¹ test function agree
if their initial data agree. No time derivative at zero, pointwise kernel, or
regularity of eigenfunction representatives is needed for this uniqueness. -/
theorem dirichletHilbert_weakHeatFlow_unique (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (F K : ℝ≥0 → Lp ℝ 2 (dirichletVolume ρ R))
    (V W : (t : ℝ≥0) → 0 < t → DirichletHilbertSpace (d := d) R hR)
    (hF : Continuous F) (hK : Continuous K)
    (hV : ∀ t ht,
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (V t ht) = F t)
    (hW : ∀ t ht,
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (W t ht) = K t)
    (hweakF : ∀ t ht, ∀ v : DirichletHilbertSpace (d := d) R hR,
      HasDerivAt (fun s : ℝ => inner ℝ (F s.toNNReal)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
        (-(∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (V t ht).val (some i) x))
            (fun i => v.val (some i) x))) (t : ℝ))
    (hweakK : ∀ t ht, ∀ v : DirichletHilbertSpace (d := d) R hR,
      HasDerivAt (fun s : ℝ => inner ℝ (K s.toNNReal)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v))
        (-(∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (W t ht).val (some i) x))
            (fun i => v.val (some i) x))) (t : ℝ))
    (hinitial : F 0 = K 0) : F = K := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eigenvalue, u, hpos, _hlim, he, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)) :=
    HilbertBasis.mk he (le_of_eq hspan.symm)
  have hb (n : ℕ) : b n = J (u n) := by
    exact congrFun (HilbertBasis.coe_mk he (le_of_eq hspan.symm)) n
  have henergy (v : DirichletHilbertSpace (d := d) R hR) (n : ℕ) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => v.val (some i) x))
          (fun i => (u n).val (some i) x)) =
        eigenvalue n * inner ℝ (b n) (J v) := by
    rw [hb, ← hvar n v]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have hsym : (α x).IsSymm := (h.2.2 x).2.2.1
      have heq := hsym.dotProduct_mulVec_comm
        (x := fun i => (u n).val (some i) x) (y := fun i => v.val (some i) x)
      rw [dotProduct_comm, dotProduct_comm (fun i => v.val (some i) x)] at heq
      exact heq
  have hsolve (T : ℝ≥0 → Lp ℝ 2 (dirichletVolume ρ R))
      (U : (t : ℝ≥0) → 0 < t → DirichletHilbertSpace (d := d) R hR)
      (hT : Continuous T) (hU : ∀ t ht, J (U t ht) = T t)
      (hweak : ∀ t ht, ∀ v : DirichletHilbertSpace (d := d) R hR,
        HasDerivAt (fun s : ℝ => inner ℝ (T s.toNNReal) (J v))
          (-(∫ x in sourceBall (0 : Vec d) R,
            dot ((α x).mulVec (fun i => (U t ht).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ)) (t : ℝ≥0) :
      T t = SpectralHeat.heatOperator b eigenvalue (fun n => (hpos n).le) t (T 0) := by
    apply SpectralHeat.heatOperator_eq_of_weakEvolution b eigenvalue
      (fun n => (hpos n).le) T hT
    intro s hs n
    have hd := hweak s hs (u n)
    rw [henergy, hU] at hd
    simpa only [hb, real_inner_comm, neg_mul] using hd
  funext t
  rw [hsolve F V hF hV hweakF t, hsolve K W hK hW hweakK t, hinitial]


namespace DimensionLift

/-- A spatial section of a genuine compact product test is again a compact test. -/
theorem spatial_slice_test {U : Set (Vec d)} {ψ : Vec d × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U ×ˢ Set.univ) (t : ℝ) :
    IsSpatialTest U (fun x => ψ (x, t)) := by
  have hpre : tsupport (fun x => ψ (x, t)) ⊆
      (fun x : Vec d => (x, t)) ⁻¹' tsupport ψ :=
    tsupport_comp_subset_preimage ψ (by fun_prop)
  refine ⟨hψ.comp (contDiff_id.prodMk contDiff_const), ?_, ?_⟩
  · exact (hc.image continuous_fst).of_isClosed_subset (isClosed_tsupport _) fun x hx =>
      ⟨(x, t), hpre hx, rfl⟩
  · exact fun x hx => (hs (hpre hx)).1

/-- The derivative of a spatial section is the actual spatial direction of
its product test, with no coordinate norm change. -/
theorem spatial_slice_fderiv {ψ : Vec d × ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (x : Vec d) (t : ℝ) (v : Vec d) :
    fderiv ℝ (fun y => ψ (y, t)) x v = fderiv ℝ ψ (x, t) (v, 0) := by
  have heq := (hψ (x, t)).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜 := ℝ) x).prodMk (hasFDerivAt_const t x))
  exact congrArg (fun A : Vec d →L[ℝ] ℝ => A v) heq.fderiv

/-- The transverse derivative also agrees with the literal product direction. -/
theorem transverse_slice_deriv {ψ : Vec d × ℝ → ℝ}
    (hψ : Differentiable ℝ ψ) (x : Vec d) (t : ℝ) :
    deriv (fun s => ψ (x, s)) t = fderiv ℝ ψ (x, t) (0, 1) := by
  have heq := (hψ (x, t)).hasFDerivAt.comp t
    ((hasFDerivAt_const x t).prodMk (hasFDerivAt_id t))
  exact congrArg (fun A : ℝ →L[ℝ] ℝ => A 1) heq.fderiv

/-- Compact transverse tests permit integration by parts against the positive
exponential used in the eigenfunction dimension lift. -/
theorem integral_exp_mul_deriv (c : ℝ) {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) :
    (∫ s, Real.exp (c * s) * deriv η s) =
      -c * ∫ s, Real.exp (c * s) * η s := by
  have hexp (s : ℝ) : HasDerivAt (fun r : ℝ => Real.exp (c * r))
      (c * Real.exp (c * s)) s := by
    simpa only [id_eq, mul_one, mul_comm] using ((hasDerivAt_id s).const_mul c).exp
  have hfg : Integrable (fun s => Real.exp (c * s) * η s) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      hη.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hfg' : Integrable (fun s => Real.exp (c * s) * deriv η s) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      (hη.continuous_deriv (by norm_num))).integrable_of_hasCompactSupport
        hc.deriv.mul_left
  have hf'g : Integrable (fun s => c * Real.exp (c * s) * η s) := by
    simpa only [mul_assoc] using hfg.const_mul c
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (fun s _ => hexp s)
    (fun s _ => ((hη.differentiable (by norm_num)) s).hasDerivAt)
    hfg' hf'g hfg
  simpa only [mul_assoc, integral_const_mul, neg_mul] using hibp

/-- Product a.e. equality recovers the original function by transverse
averaging. This uses Fubini and never specializes a null-set identity to a slice. -/
theorem transverse_average_ae_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [SFinite ν]
    (c : ℝ) (η : ℝ → ℝ) {v : X × ℝ → ℝ} {u : X → ℝ}
    (hv : v =ᵐ[μ.prod ν] fun z => u z.1 * Real.exp (c * z.2))
    (hm : (∫ s, η s * Real.exp (c * s) ∂ν) ≠ 0) :
    (fun x => (∫ s, η s * v (x, s) ∂ν) /
      (∫ s, η s * Real.exp (c * s) ∂ν)) =ᵐ[μ] u := by
  filter_upwards [Measure.ae_ae_of_ae_prod hv] with x hx
  have hi : (∫ s, η s * v (x, s) ∂ν) =
      u x * ∫ s, η s * Real.exp (c * s) ∂ν := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hx] with s hs
    rw [hs]
    ring
  rw [hi, mul_div_cancel_right₀ _ hm]


/-- A locally integrable spatial function can be paired with any continuous
compact product test supported inside the spatial domain. -/
theorem integrable_spatial_mul_product_test {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : LocallyIntegrableOn f U volume) {θ : Vec d × ℝ → ℝ}
    (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ U ×ˢ Set.univ) :
    Integrable (fun z => f z.1 * θ z) ((volume.restrict U).prod volume) := by
  let K := Prod.fst '' tsupport θ
  let I := Prod.snd '' tsupport θ
  have hK : IsCompact K := hc.image continuous_fst
  have hI : IsCompact I := hc.image continuous_snd
  have hKU : K ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hs hz).1
  have hfK : IntegrableOn f K volume := hf.integrableOn_compact_subset hKU hK
  have h1I : IntegrableOn (fun _ : ℝ => (1 : ℝ)) I volume :=
    continuous_const.continuousOn.integrableOn_compact hI
  have hp : IntegrableOn (fun z : Vec d × ℝ => f z.1) (K ×ˢ I)
      (volume.prod volume) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, mul_one] using hfK.mul_prod h1I
  have hi := hp.mul_continuousOn hθ.continuousOn (hK.prod hI)
  have hg : Integrable (fun z => f z.1 * θ z) (volume.prod volume) := by
    apply hi.integrable_of_forall_notMem_eq_zero
    intro z hz
    have hnot : z ∉ tsupport θ := by
      intro hmem
      exact hz ⟨⟨z, hmem, rfl⟩, ⟨z, hmem, rfl⟩⟩
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  exact hg.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)

/-- The forced spatial weak equation cancels the transverse exponential
flux for arbitrary joint tests. The only temporary analytic side conditions
here are the three displayed product integrabilities. -/
theorem integral_lifted_flux_eq_zero_of_integrable {U : Set (Vec d)}
    (F : Vec d → Vec d) (m : Vec d → ℝ) (eigenvalue c : ℝ) (hc_eigenvalue : c * c = eigenvalue)
    (hweak : ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
      (∫ x in U, dot (F x) (fun i => fderiv ℝ φ x (unitVector i))) =
        eigenvalue * ∫ x in U, m x * φ x)
    {ψ : Vec d × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Set.univ)
    (hsp : Integrable (fun z => Real.exp (c * z.2) *
      dot (F z.1) (fun i => fderiv ℝ ψ z (unitVector i, 0)))
        ((volume.restrict U).prod volume))
    (htr : Integrable (fun z => (m z.1 * c * Real.exp (c * z.2)) *
      fderiv ℝ ψ z (0, 1)) ((volume.restrict U).prod volume))
    (hm : Integrable (fun z => m z.1 * (Real.exp (c * z.2) * ψ z))
      ((volume.restrict U).prod volume)) :
    (∫ z, Real.exp (c * z.2) *
      dot (F z.1) (fun i => fderiv ℝ ψ z (unitVector i, 0)) +
        (m z.1 * c * Real.exp (c * z.2)) * fderiv ℝ ψ z (0, 1)
      ∂((volume.restrict U).prod volume)) = 0 := by
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hspace : (∫ z, Real.exp (c * z.2) *
      dot (F z.1) (fun i => fderiv ℝ ψ z (unitVector i, 0))
        ∂((volume.restrict U).prod volume)) =
      eigenvalue * ∫ z, m z.1 * (Real.exp (c * z.2) * ψ z)
        ∂((volume.restrict U).prod volume) := by
    rw [integral_prod_symm _ hsp, integral_prod_symm _ hm, ← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro t
    dsimp only
    have hw := hweak (fun x => ψ (x, t)) (spatial_slice_test hψ hc hs t)
    simp_rw [spatial_slice_fderiv hdψ] at hw
    rw [integral_const_mul, hw]
    simp_rw [mul_left_comm (m _) (Real.exp (c * t)), integral_const_mul]
    ring
  have htrans : (∫ z, (m z.1 * c * Real.exp (c * z.2)) *
      fderiv ℝ ψ z (0, 1) ∂((volume.restrict U).prod volume)) =
      -eigenvalue * ∫ z, m z.1 * (Real.exp (c * z.2) * ψ z)
        ∂((volume.restrict U).prod volume) := by
    rw [integral_prod _ htr, integral_prod _ hm, ← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro x
    dsimp only
    have ht : HasCompactSupport (fun t => ψ (x, t)) := by
      have hp : tsupport (fun t => ψ (x, t)) ⊆
          (fun t : ℝ => (x, t)) ⁻¹' tsupport ψ :=
        tsupport_comp_subset_preimage ψ (by fun_prop)
      exact (hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
        fun t ht => ⟨(x, t), hp ht, rfl⟩
    have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun t => ψ (x, t)) :=
      hψ.comp (contDiff_const.prodMk contDiff_id)
    have hi := integral_exp_mul_deriv c hslice ht
    simp_rw [← transverse_slice_deriv hdψ, mul_assoc, integral_const_mul]
    rw [hi]
    rw [← hc_eigenvalue]
    ring
  rw [integral_add hsp htr, hspace, htrans]
  ring


/-- Exponentially weighted directional derivatives of compact joint tests
pair integrably with every locally integrable spatial coefficient. -/
theorem integrable_spatial_mul_exp_fderiv {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : LocallyIntegrableOn f U volume) (c : ℝ) (v : Vec d × ℝ)
    {ψ : Vec d × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Set.univ) :
    Integrable (fun z => f z.1 * (Real.exp (c * z.2) * fderiv ℝ ψ z v))
      ((volume.restrict U).prod volume) := by
  apply integrable_spatial_mul_product_test hf
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul
      ((hψ.continuous_fderiv_apply (by norm_num)).comp
        (continuous_id.prodMk continuous_const))
  · exact (hc.fderiv_apply ℝ v).mul_left
  · exact tsupport_mul_subset_right.trans ((tsupport_fderiv_apply_subset ℝ v).trans hs)

/-- A spatial divergence equation with locally integrable flux and mass
becomes a homogeneous joint-test equation after the exponential lift. -/
theorem integral_lifted_flux_eq_zero {U : Set (Vec d)}
    (F : Vec d → Vec d) (m : Vec d → ℝ) (eigenvalue c : ℝ)
    (hc_eigenvalue : c * c = eigenvalue)
    (hF : ∀ i, LocallyIntegrableOn (fun x => F x i) U volume)
    (hm : LocallyIntegrableOn m U volume)
    (hweak : ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
      (∫ x in U, dot (F x) (fun i => fderiv ℝ φ x (unitVector i))) =
        eigenvalue * ∫ x in U, m x * φ x)
    {ψ : Vec d × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Set.univ) :
    (∫ z, Real.exp (c * z.2) *
      dot (F z.1) (fun i => fderiv ℝ ψ z (unitVector i, 0)) +
        (m z.1 * c * Real.exp (c * z.2)) * fderiv ℝ ψ z (0, 1)
      ∂((volume.restrict U).prod volume)) = 0 := by
  have hsp : Integrable (fun z => Real.exp (c * z.2) *
      dot (F z.1) (fun i => fderiv ℝ ψ z (unitVector i, 0)))
        ((volume.restrict U).prod volume) := by
    have hi := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_spatial_mul_exp_fderiv (hF i) c (unitVector i, 0) hψ hc hs)
    convert hi using 1
    funext z
    simp only [dot, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have htr : Integrable (fun z => (m z.1 * c * Real.exp (c * z.2)) *
      fderiv ℝ ψ z (0, 1)) ((volume.restrict U).prod volume) := by
    have hi := (integrable_spatial_mul_exp_fderiv hm c (0, 1) hψ hc hs).const_mul c
    convert hi using 1
    funext z
    ring
  have hmass : Integrable (fun z => m z.1 * (Real.exp (c * z.2) * ψ z))
      ((volume.restrict U).prod volume) :=
    integrable_spatial_mul_product_test hm
      ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul hψ.continuous)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
  exact integral_lifted_flux_eq_zero_of_integrable F m eigenvalue c hc_eigenvalue
    hweak hψ hc hs hsp htr hmass

/-- Compact transverse averaging preserves continuity on the spatial domain. -/
theorem transverse_average_continuousOn {U : Set (Vec d)} {v : Vec d × ℝ → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.univ)) {η : ℝ → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η) (M : ℝ) :
    ContinuousOn (fun x => (∫ s, η s * v (x, s)) / M) U := by
  have hi : ContinuousOn (fun x => ∫ s, η s * v (x, s)) U := by
    apply continuousOn_integral_of_compact_support hc
    · exact (hη.comp continuous_snd).continuousOn.mul hv
    · intro x s _ hs
      rw [image_eq_zero_of_notMem_tsupport hs, zero_mul]
  exact hi.div_const M

/-- A nonzero, nonnegative compact transverse weight has positive
exponential moment, so the normalized average is well-defined. -/
theorem transverse_exponential_moment_pos (c : ℝ) {η : ℝ → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η)
    (hn : ∀ s, 0 ≤ η s) {s₀ : ℝ} (hs₀ : η s₀ ≠ 0) :
    0 < ∫ s, η s * Real.exp (c * s) := by
  have hcont : Continuous (fun s => η s * Real.exp (c * s)) :=
    hη.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
  apply hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · exact fun s => mul_nonneg (hn s) (Real.exp_pos _).le
  · exact mul_ne_zero hs₀ (Real.exp_ne_zero _)


/-- Averages only need continuity on a cylinder containing the transverse
support. Clamping extends that continuity to the whole transverse line. -/
theorem transverse_average_continuousOn_cylinder {U : Set (Vec d)}
    {a b : ℝ} (hab : a ≤ b) {v : Vec d × ℝ → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.Icc a b)) {η : ℝ → ℝ}
    (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Icc a b) (M : ℝ) :
    ContinuousOn (fun x => (∫ s, η s * v (x, s)) / M) U := by
  let q : ℝ → ℝ := fun s => max a (min b s)
  have hq : Continuous q := continuous_const.max (continuous_const.min continuous_id)
  have hq_mem (s : ℝ) : q s ∈ Set.Icc a b :=
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hq_eq {s : ℝ} (h : s ∈ Set.Icc a b) : q s = s := by
    exact (show max a (min b s) = s by rw [min_eq_right h.2, max_eq_right h.1])
  have hvc : ContinuousOn (fun z : Vec d × ℝ => v (z.1, q z.2))
      (U ×ˢ Set.univ) :=
    hv.comp (continuous_fst.prodMk (hq.comp continuous_snd)).continuousOn
      (fun z hz => ⟨hz.1, hq_mem z.2⟩)
  have hi := transverse_average_continuousOn hvc hη hc M
  have heq (x : Vec d) (s : ℝ) : η s * v (x, q s) = η s * v (x, s) := by
    by_cases h : s ∈ tsupport η
    · rw [hq_eq (hs h)]
    · rw [image_eq_zero_of_notMem_tsupport h, zero_mul, zero_mul]
  simpa only [heq] using hi

/-- A continuous representative of the lift yields a continuous spatial
representative through compact transverse averaging, with the a.e. conclusion
obtained from product Fubini. -/
theorem exists_continuousOn_ae_eq_of_lift {U : Set (Vec d)}
    {a b : ℝ} (hab : a ≤ b) {v : Vec d × ℝ → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.Icc a b)) (c : ℝ)
    (heq : v =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc a b))]
      fun z => u z.1 * Real.exp (c * z.2))
    {η : ℝ → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Icc a b)
    (hn : ∀ s, 0 ≤ η s) {s₀ : ℝ} (hs₀ : η s₀ ≠ 0) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u := by
  have hrestrict (f : ℝ → ℝ) :
      (∫ s in Set.Icc a b, η s * f s) = ∫ s, η s * f s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hnot
    have ht : s ∉ tsupport η := fun ht => hnot (hs ht)
    rw [image_eq_zero_of_notMem_tsupport ht, zero_mul]
  let M : ℝ := ∫ s, η s * Real.exp (c * s)
  refine ⟨fun x => (∫ s, η s * v (x, s)) / M,
    transverse_average_continuousOn_cylinder hab hv hη hc hs M, ?_⟩
  have hp : 0 < M := transverse_exponential_moment_pos c hη hc hn hs₀
  have hm : (∫ s in Set.Icc a b, η s * Real.exp (c * s)) ≠ 0 := by
    rw [hrestrict]
    exact ne_of_gt hp
  simpa only [hrestrict, M] using
    transverse_average_ae_eq (volume.restrict U) (volume.restrict (Set.Icc a b))
      c η heq hm


/-- Each spatial weak derivative transports to the product against arbitrary
joint tests; no pointwise derivative of the spatial function is assumed. -/
theorem integral_lifted_spatial_weakDerivative {U : Set (Vec d)}
    {u g : Vec d → ℝ} {i : Fin d} (hu : HasWeakPartialDerivative U i u g)
    (c : ℝ) {ψ : Vec d × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Set.univ) :
    (∫ z, u z.1 * (Real.exp (c * z.2) * fderiv ℝ ψ z (unitVector i, 0))
      ∂((volume.restrict U).prod volume)) =
      -(∫ z, g z.1 * (Real.exp (c * z.2) * ψ z)
        ∂((volume.restrict U).prod volume)) := by
  have hl := integrable_spatial_mul_exp_fderiv hu.1 c (unitVector i, 0) hψ hc hs
  have hr : Integrable (fun z => g z.1 * (Real.exp (c * z.2) * ψ z))
      ((volume.restrict U).prod volume) :=
    integrable_spatial_mul_product_test hu.2.1
      ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul hψ.continuous)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr, ← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hw := hu.2.2 (fun x => ψ (x, t)) (spatial_slice_test hψ hc hs t)
  simp_rw [coordinateDerivative, spatial_slice_fderiv hdψ] at hw
  simp_rw [mul_left_comm (u _) (Real.exp (c * t)),
    mul_left_comm (g _) (Real.exp (c * t)), integral_const_mul]
  rw [hw]
  ring

/-- The transverse weak derivative of the literal exponential lift is
`c` times the lift, also when the spatial function is merely locally integrable. -/
theorem integral_lifted_transverse_weakDerivative {U : Set (Vec d)}
    {u : Vec d → ℝ} (hu : LocallyIntegrableOn u U volume)
    (c : ℝ) {ψ : Vec d × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ U ×ˢ Set.univ) :
    (∫ z, u z.1 * (Real.exp (c * z.2) * fderiv ℝ ψ z (0, 1))
      ∂((volume.restrict U).prod volume)) =
      -(∫ z, (u z.1 * c) * (Real.exp (c * z.2) * ψ z)
        ∂((volume.restrict U).prod volume)) := by
  have hl := integrable_spatial_mul_exp_fderiv hu c (0, 1) hψ hc hs
  have hmass : Integrable (fun z => u z.1 * (Real.exp (c * z.2) * ψ z))
      ((volume.restrict U).prod volume) :=
    integrable_spatial_mul_product_test hu
      ((Real.continuous_exp.comp (continuous_const.mul continuous_snd)).mul hψ.continuous)
      hc.mul_left (tsupport_mul_subset_right.trans hs)
  have hr : Integrable (fun z => (u z.1 * c) * (Real.exp (c * z.2) * ψ z))
      ((volume.restrict U).prod volume) := by
    convert hmass.const_mul c using 1
    funext z
    ring
  rw [integral_prod _ hl, integral_prod _ hr, ← integral_neg]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  dsimp only
  have hdψ : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have ht : HasCompactSupport (fun t => ψ (x, t)) := by
    have hp : tsupport (fun t => ψ (x, t)) ⊆
        (fun t : ℝ => (x, t)) ⁻¹' tsupport ψ :=
      tsupport_comp_subset_preimage ψ (by fun_prop)
    exact (hc.image continuous_snd).of_isClosed_subset (isClosed_tsupport _)
      fun t ht => ⟨(x, t), hp ht, rfl⟩
  have hslice : ContDiff ℝ (⊤ : ℕ∞) (fun t => ψ (x, t)) :=
    hψ.comp (contDiff_const.prodMk contDiff_id)
  have hi := integral_exp_mul_deriv c hslice ht
  simp_rw [← transverse_slice_deriv hdψ, integral_const_mul]
  rw [hi]
  ring


/-- The exponential lift preserves every Lᵖ class on compact cylinders with
finite spatial measure. In particular this supplies L² for the lifted value
and for each of its actual weak-gradient coordinates. -/
theorem memLp_lift_on_compact {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] {u : X → ℝ} {p : ℝ≥0∞}
    (hu : MemLp u p μ) (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    MemLp (fun z : X × ℝ => u z.1 * Real.exp (c * z.2)) p
      (μ.prod (volume.restrict K)) := by
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  have he : Continuous (fun s : ℝ => Real.exp (c * s)) :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn he.continuousOn
  have hb : MemLp (fun s : ℝ => Real.exp (c * s)) ∞ (volume.restrict K) := by
    apply memLp_top_of_bound he.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem hK.measurableSet] with s hs
    exact hC s hs
  exact (hu.comp_fst (volume.restrict K)).mul (hb.comp_snd μ)


/-- The literal coordinate splitting into the first `d` coordinates and the
last coordinate, as a continuous linear equivalence. -/
def productCoordinates : Vec (d + 1) ≃L[ℝ] Vec d × ℝ :=
  ({ toEquiv := ((Fin.insertNthEquiv (fun _ : Fin (d + 1) => ℝ)
        (Fin.last d)).symm).trans (Equiv.prodComm ℝ (Vec d))
     map_add' := by intro x y; rfl
     map_smul' := by intro r x; rfl } :
      Vec (d + 1) ≃ₗ[ℝ] Vec d × ℝ).toContinuousLinearEquiv

@[simp]
theorem productCoordinates_apply (x : Vec (d + 1)) :
    productCoordinates x = ((Fin.last d).removeNth x, x (Fin.last d)) := rfl

/-- The coordinate splitting transports the actual Lebesgue volume to the
product of the actual spatial and transverse Lebesgue volumes. -/
theorem productCoordinates_measurePreserving :
    MeasurePreserving (productCoordinates (d := d)) volume (volume.prod volume) := by
  exact Measure.measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) (Fin.last d))

/-- Splitting off the transverse coordinate preserves the source Euclidean
scalar product, independently of the product carrier's norm instance. -/
theorem productCoordinates_dot (x y : Vec (d + 1)) :
    dot x y = dot (productCoordinates x).1 (productCoordinates y).1 +
      (productCoordinates x).2 * (productCoordinates y).2 := by
  simp only [dot, productCoordinates_apply, Fin.removeNth_last]
  exact Fin.sum_univ_castSucc (fun i => x i * y i)

/-- The lifted Euclidean energy is the spatial energy plus the square of
the transverse coordinate. -/
theorem productCoordinates_euclideanSq (x : Vec (d + 1)) :
    euclideanSq x = euclideanSq (productCoordinates x).1 +
      (productCoordinates x).2 ^ 2 := by
  simpa only [euclideanSq, pow_two] using productCoordinates_dot x x

/-- The coordinate splitting transports restricted Lebesgue volume on a
literal cylinder to the product of its two restricted volumes. -/
theorem productCoordinates_measurePreserving_cylinder
    {U : Set (Vec d)} (hU : MeasurableSet U) {K : Set ℝ} (hK : MeasurableSet K) :
    MeasurePreserving (productCoordinates (d := d))
      (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K)))
      ((volume.restrict U).prod (volume.restrict K)) := by
  rw [Measure.prod_restrict]
  exact productCoordinates_measurePreserving.restrict_preimage (hU.prod hK)

/-- The actual exponential lift is in Lᵖ on a finite spatial cylinder in
the original `d+1` coordinates; this applies to values and gradient entries. -/
theorem memLp_lift_on_coordinate_cylinder {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {p : ℝ≥0∞} (hu : MemLp u p (volume.restrict U))
    (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    MemLp (fun z : Vec (d + 1) =>
      u (productCoordinates z).1 * Real.exp (c * (productCoordinates z).2)) p
      (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) := by
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUfinite
  exact (memLp_lift_on_compact (volume.restrict U) hu c hK).comp_measurePreserving
    (productCoordinates_measurePreserving_cylinder hU hK.measurableSet)

/-- The literal block diagonal matrix for the exponential dimension lift.
The last coordinate has coefficient `ρ`, and the spatial block is `a`. -/
def liftedMatrix (ρ : ℝ) (a : Mat d) : Mat (d + 1) :=
  fun i j => Fin.lastCases (Fin.lastCases ρ (fun _ => 0) j)
    (fun i => Fin.lastCases 0 (fun j => a i j) j) i

@[simp]
theorem liftedMatrix_mulVec_castSucc (ρ : ℝ) (a : Mat d)
    (v : Vec (d + 1)) (i : Fin d) :
    (liftedMatrix ρ a).mulVec v i.castSucc =
      a.mulVec (fun j => v j.castSucc) i := by
  simp [liftedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

@[simp]
theorem liftedMatrix_mulVec_last (ρ : ℝ) (a : Mat d) (v : Vec (d + 1)) :
    (liftedMatrix ρ a).mulVec v (Fin.last d) = ρ * v (Fin.last d) := by
  simp [liftedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc]

/-- The lifted energy is exactly the spatial elliptic energy plus its
transverse mass term. -/
theorem liftedMatrix_energy (ρ : ℝ) (a : Mat d) (v : Vec (d + 1)) :
    dot v ((liftedMatrix ρ a).mulVec v) =
      dot (productCoordinates v).1 (a.mulVec (productCoordinates v).1) +
        ρ * (productCoordinates v).2 ^ 2 := by
  simp only [dot, Fin.sum_univ_castSucc, liftedMatrix_mulVec_castSucc,
    liftedMatrix_mulVec_last, productCoordinates_apply, Fin.removeNth_last]
  simp only [Fin.init_def]
  ring

/-- Symmetry of the actual spatial matrix is retained by the dimension lift. -/
theorem liftedMatrix_transpose (ρ : ℝ) {a : Mat d} (ha : a.transpose = a) :
    (liftedMatrix ρ a).transpose = liftedMatrix ρ a := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Matrix.transpose_apply, liftedMatrix]
  · simp [Matrix.transpose_apply, liftedMatrix]
  · simp [Matrix.transpose_apply, liftedMatrix]
  · simpa [Matrix.transpose_apply, liftedMatrix] using congrFun (congrFun ha i) j

/-- The literal lifted matrix has the same two Euclidean quadratic bounds
as the supplied uniformly elliptic spatial coefficients. -/
theorem liftedMatrix_quadratic {κ : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (x : Vec d) (v : Vec (d + 1)) :
    κ * euclideanSq v ≤ dot v ((liftedMatrix (ρ x) (α x)).mulVec v) ∧
      dot v ((liftedMatrix (ρ x) (α x)).mulVec v) ≤ κ⁻¹ * euclideanSq v := by
  rw [liftedMatrix_energy, productCoordinates_euclideanSq]
  have hs := (h.2.2 x).2.2.2 (productCoordinates v).1
  have hl := mul_le_mul_of_nonneg_right (h.2.2 x).1
    (sq_nonneg (productCoordinates v).2)
  have hu := mul_le_mul_of_nonneg_right (h.2.2 x).2.1
    (sq_nonneg (productCoordinates v).2)
  constructor <;> nlinarith only [hs.1, hs.2, hl, hu]

/-- A coercive symmetric matrix with upper quadratic constant `κ⁻¹` has
the inverse coercivity needed by the interior regularity interface. -/
theorem inverse_quadratic_lower {n : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (a : Mat n) (hsymm : a.transpose = a)
    (hl : ∀ v, κ * euclideanSq v ≤ dot v (a.mulVec v))
    (hu : ∀ v, dot v (a.mulVec v) ≤ κ⁻¹ * euclideanSq v) (v : Vec n) :
    κ ^ 3 * euclideanSq v ≤ dot v (a⁻¹.mulVec v) := by
  have hdet := Correctors.isUnit_det_of_euclidean_coercivity hκ a hl
  let w := a⁻¹.mulVec v
  have hw : a.mulVec w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv a hdet, Matrix.one_mulVec]
  have hnonneg (z : Vec n) : 0 ≤ euclideanSq z := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (z i))
  have hn := Correctors.mulVec_euclideanNorm_le_of_quadratic a (inv_pos.mpr hκ)
    hsymm (fun z => (mul_nonneg hκ.le (hnonneg z)).trans (hl z)) hu w
  rw [hw] at hn
  have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (euclideanSq v)) hn
  have hsq' : euclideanSq v ≤ (κ⁻¹) ^ 2 * euclideanSq w := by
    simpa only [euclideanNorm, ← pow_two, mul_pow,
      Real.sq_sqrt (hnonneg v), Real.sq_sqrt (hnonneg w)] using hsq
  have hcancel : κ ^ 3 * (κ⁻¹) ^ 2 = κ := by
    field_simp [hκ.ne']
  calc
    κ ^ 3 * euclideanSq v ≤ κ ^ 3 * ((κ⁻¹) ^ 2 * euclideanSq w) :=
      mul_le_mul_of_nonneg_left hsq' (by positivity)
    _ = κ * euclideanSq w := by rw [← mul_assoc, hcancel]
    _ ≤ dot w (a.mulVec w) := hl w
    _ = dot v (a⁻¹.mulVec v) := by rw [hw]; exact dotProduct_comm _ _

/-- Euclidean transport of the quadratic form uses the Hilbert norm, not
the coordinate carrier's default norm. -/
theorem euclideanSq_eq_norm_sq_toLp {n : ℕ} (v : Vec n) :
    euclideanSq v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ ^ 2 := by
  rw [← TimeChange.euclideanNorm_eq_norm_toLp]
  unfold euclideanSq euclideanNorm dot
  exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))).symm

/-- The real Hilbert inner product is the source Euclidean scalar product. -/
theorem inner_toLp_eq_dot {n : ℕ} (v w : Vec n) :
    inner ℝ (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 w) =
      dot v w := by
  simp [PiLp.inner_apply, RCLike.inner_apply, dot, mul_comm]

/-- Every entry of the actual lifted field is measurable in the original
coordinates. This requires only the supplied coefficient measurability. -/
theorem liftedMatrix_measurable {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (i j : Fin (d + 1)) :
    Measurable (fun z : Vec (d + 1) =>
      liftedMatrix (ρ (productCoordinates z).1) (α (productCoordinates z).1) i j) := by
  have hp : Measurable (fun z : Vec (d + 1) => (productCoordinates z).1) :=
    (continuous_fst.comp (productCoordinates (d := d)).continuous).measurable
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · simpa [liftedMatrix, Function.comp_def] using h.1.comp hp
  · simpa [liftedMatrix] using (measurable_const : Measurable (fun _ : Vec (d + 1) => (0 : ℝ)))
  · simpa [liftedMatrix] using (measurable_const : Measurable (fun _ : Vec (d + 1) => (0 : ℝ)))
  · let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    simpa [liftedMatrix, Function.comp_def] using
      (((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        h.2.1).comp hp

/-- The lifted field has genuine inverse Euclidean coercivity; this is
proved from its source bounds, without an inverse-coercivity hypothesis. -/
theorem liftedMatrix_inverse_quadratic {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (x : Vec d) (v : Vec (d + 1)) :
    κ ^ 3 * euclideanSq v ≤ dot v ((liftedMatrix (ρ x) (α x))⁻¹.mulVec v) :=
  inverse_quadratic_lower hκ _ (liftedMatrix_transpose _ (h.2.2 x).2.2.1)
    (fun w => (liftedMatrix_quadratic h x w).1)
    (fun w => (liftedMatrix_quadratic h x w).2) v

/-- Pulling a compact test to product coordinates preserves its support
inside the actual spatial cylinder. -/
theorem productCoordinates_test {U : Set (Vec d)} {φ : Vec (d + 1) → ℝ}
    (hφ : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ (productCoordinates.symm z)) ∧
      HasCompactSupport (fun z => φ (productCoordinates.symm z)) ∧
      tsupport (fun z => φ (productCoordinates.symm z)) ⊆ U ×ˢ Set.univ := by
  refine ⟨hφ.1.comp (productCoordinates (d := d)).symm.contDiff,
    hφ.2.1.comp_homeomorph (productCoordinates (d := d)).symm.toHomeomorph, ?_⟩
  intro z hz
  have ht := hφ.2.2 ((tsupport_comp_subset_preimage φ
    (productCoordinates (d := d)).symm.continuous) hz)
  simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using ht

/-- Spatial coordinate vectors are transported literally by the splitting. -/
theorem productCoordinates_unitVector_castSucc (i : Fin d) :
    productCoordinates (unitVector i.castSucc : Vec (d + 1)) = (unitVector i, 0) := by
  apply Prod.ext
  · ext j
    simp [productCoordinates_apply, Fin.removeNth_last, Fin.init, unitVector, Pi.single_apply]
  · simp [productCoordinates_apply, unitVector]

/-- The last coordinate is exactly the transverse unit vector. -/
theorem productCoordinates_unitVector_last :
    productCoordinates (unitVector (Fin.last d) : Vec (d + 1)) = (0, 1) := by
  apply Prod.ext
  · ext j
    simp [productCoordinates_apply, Fin.removeNth_last, Fin.init, unitVector]
  · simp [productCoordinates_apply, unitVector]

/-- The chain rule for a product-coordinate test, with no differentiability
assumption on the weak function being tested. -/
theorem productCoordinates_test_fderiv {φ : Vec (d + 1) → ℝ}
    (hφ : Differentiable ℝ φ) (z w : Vec d × ℝ) :
    fderiv ℝ (fun y => φ (productCoordinates.symm y)) z w =
      fderiv ℝ φ (productCoordinates.symm z) (productCoordinates.symm w) := by
  change (fderiv ℝ (φ ∘ productCoordinates.symm) z) w = _
  rw [fderiv_comp z hφ.differentiableAt
    (productCoordinates (d := d)).symm.differentiableAt,
    ContinuousLinearEquiv.fderiv]
  rfl

/-- Restricted Lebesgue change of variables for arbitrary product integrands. -/
theorem integral_productCoordinates_spatial {U : Set (Vec d)} (hU : MeasurableSet U)
    (f : Vec d × ℝ → ℝ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ), f (productCoordinates z)) =
      ∫ z, f z ∂((volume.restrict U).prod volume) := by
  have hm : MeasurePreserving (productCoordinates (d := d))
      (volume.restrict (productCoordinates ⁻¹' (U ×ˢ Set.univ)))
      ((volume.restrict U).prod volume) := by
    simpa only [Measure.restrict_univ] using
      productCoordinates_measurePreserving_cylinder hU MeasurableSet.univ
  exact hm.integral_comp (productCoordinates (d := d)).toHomeomorph.measurableEmbedding f

/-- The spatial weak derivative of the exponential lift in the original
`d+1` coordinates, tested against arbitrary joint compact tests. -/
theorem integral_coordinate_lift_spatial_weakDerivative {U : Set (Vec d)}
    (hU : MeasurableSet U) {u g : Vec d → ℝ} {i : Fin d}
    (hu : HasWeakPartialDerivative U i u g) (c : ℝ)
    {φ : Vec (d + 1) → ℝ}
    (hφ : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ),
      u (productCoordinates z).1 * (Real.exp (c * (productCoordinates z).2) *
        fderiv ℝ φ z (unitVector i.castSucc))) =
      -(∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ),
        g (productCoordinates z).1 * (Real.exp (c * (productCoordinates z).2) * φ z)) := by
  obtain ⟨hp, hc, hs⟩ := productCoordinates_test hφ
  have hw := integral_lifted_spatial_weakDerivative hu c hp hc hs
  have he : productCoordinates.symm (unitVector i, 0) =
      (unitVector i.castSucc : Vec (d + 1)) := by
    rw [← productCoordinates_unitVector_castSucc,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [← integral_productCoordinates_spatial hU,
    productCoordinates_test_fderiv (hφ.1.differentiable (by norm_num)),
    ContinuousLinearEquiv.symm_apply_apply, he] at hw
  exact hw

/-- The transverse weak derivative of the lift also transports to the
original coordinate carrier, without taking a slice of an a.e. identity. -/
theorem integral_coordinate_lift_transverse_weakDerivative {U : Set (Vec d)}
    (hU : MeasurableSet U) {u : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume) (c : ℝ)
    {φ : Vec (d + 1) → ℝ}
    (hφ : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ),
      u (productCoordinates z).1 * (Real.exp (c * (productCoordinates z).2) *
        fderiv ℝ φ z (unitVector (Fin.last d)))) =
      -(∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ),
        (u (productCoordinates z).1 * c) *
          (Real.exp (c * (productCoordinates z).2) * φ z)) := by
  obtain ⟨hp, hc, hs⟩ := productCoordinates_test hφ
  have hw := integral_lifted_transverse_weakDerivative hu c hp hc hs
  have he : productCoordinates.symm (0, 1) =
      (unitVector (Fin.last d) : Vec (d + 1)) := by
    rw [← productCoordinates_unitVector_last,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [← integral_productCoordinates_spatial hU,
    productCoordinates_test_fderiv (hφ.1.differentiable (by norm_num)),
    ContinuousLinearEquiv.symm_apply_apply, he] at hw
  exact hw


/-- Compact test support permits restriction of an integral without an
integrability premise, even for the conventionally zero Bochner integral. -/
theorem setIntegral_mul_test_eq {n : ℕ} {D C : Set (Vec n)}
    (hC : MeasurableSet C) (hDC : D ⊆ C) (f ψ : Vec n → ℝ)
    (hψ : tsupport ψ ⊆ D) :
    (∫ z in C, f z * ψ z) = ∫ z in D, f z * ψ z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hC hDC
  intro z hz
  have hzψ : z ∉ tsupport ψ := fun h => hz.2 (hψ h)
  simp [image_eq_zero_of_notMem_tsupport hzψ]

/-- L² of the spatial datum gives local L¹ of its actual coordinate lift
on every finite spatial, compact transverse cylinder. -/
theorem integrable_lift_on_coordinate_cylinder {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} (hu : MemLp u 2 (volume.restrict U))
    (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    IntegrableOn (fun z : Vec (d + 1) =>
      u (productCoordinates z).1 * Real.exp (c * (productCoordinates z).2))
      (productCoordinates ⁻¹' (U ×ˢ K)) := by
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUfinite
  letI : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_ne_top
  exact (productCoordinates_measurePreserving_cylinder hU hK.measurableSet).integrable_comp_of_integrable
      ((memLp_lift_on_compact (volume.restrict U) hu c hK).integrable (by norm_num))

/-- The literal exponential lift and its weak gradient in `d+1` coordinates. -/
def liftedValue (u : Vec d → ℝ) (c : ℝ) (z : Vec (d + 1)) : ℝ :=
  u (productCoordinates z).1 * Real.exp (c * (productCoordinates z).2)

/-- The first `d` entries lift the supplied spatial gradient; the last
entry is the actual derivative of the transverse exponential. -/
def liftedGradient (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ)
    (z : Vec (d + 1)) : Vec (d + 1) :=
  Fin.lastCases (u (productCoordinates z).1 * c *
      Real.exp (c * (productCoordinates z).2))
    (fun i => g (productCoordinates z).1 i *
      Real.exp (c * (productCoordinates z).2))

/-- The full exponential lift has all the native weak-gradient and L²
properties on a finite cylinder, including arbitrary joint test functions. -/
theorem coordinate_lift_memH1 {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    HasWeakGradient (productCoordinates ⁻¹' (U ×ˢ K))
        (liftedValue u c) (liftedGradient u g c) ∧
      MemLp (liftedValue u c) 2
        (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) ∧
      ∀ j, MemLp (fun z => liftedGradient u g c z j) 2
        (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) := by
  have hsub : productCoordinates ⁻¹' (U ×ˢ K) ⊆
      productCoordinates ⁻¹' (U ×ˢ Set.univ) := fun _ hz => ⟨hz.1, Set.mem_univ _⟩
  have hC : MeasurableSet (productCoordinates ⁻¹' (U ×ˢ Set.univ)) :=
    (hU.prod MeasurableSet.univ).preimage
      (productCoordinates (d := d)).continuous.measurable
  have hiu := integrable_lift_on_coordinate_cylinder hU hUfinite hu c hK
  have hig (i : Fin d) :=
    integrable_lift_on_coordinate_cylinder hU hUfinite (hg i) c hK
  have hit := integrable_lift_on_coordinate_cylinder hU hUfinite (hu.mul_const c) c hK
  refine ⟨?_, memLp_lift_on_coordinate_cylinder hU hUfinite hu c hK, ?_⟩
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · refine ⟨hiu.locallyIntegrableOn, ?_, ?_⟩
      · simpa [liftedGradient] using hit.locallyIntegrableOn
      intro φ hφ
      have hp : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ :=
        ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
      have huloc : LocallyIntegrableOn u U volume := by
        letI : IsFiniteMeasure (volume.restrict U) :=
          isFiniteMeasure_restrict.mpr hUfinite
        exact (show IntegrableOn u U volume from hu.integrable (by norm_num)).locallyIntegrableOn
      have he := integral_coordinate_lift_transverse_weakDerivative hU huloc c hp
      simp only [mul_assoc] at he
      have hd := setIntegral_mul_test_eq hC hsub (liftedValue u c)
        (fun z => fderiv ℝ φ z (unitVector (Fin.last d)))
        ((tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2)
      have hm := setIntegral_mul_test_eq hC hsub
        (fun z => u (productCoordinates z).1 * c *
          Real.exp (c * (productCoordinates z).2)) φ hφ.2.2
      simp only [liftedValue, mul_assoc] at hd hm
      rw [hd, hm] at he
      simpa [liftedValue, liftedGradient, coordinateDerivative, mul_assoc] using he
    · refine ⟨hiu.locallyIntegrableOn, ?_, ?_⟩
      · simpa [liftedGradient] using (hig i).locallyIntegrableOn
      intro φ hφ
      have hp : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ :=
        ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
      have he := integral_coordinate_lift_spatial_weakDerivative hU (hw i) c hp
      have hd := setIntegral_mul_test_eq hC hsub (liftedValue u c)
        (fun z => fderiv ℝ φ z (unitVector i.castSucc))
        ((tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2)
      have hm := setIntegral_mul_test_eq hC hsub
        (fun z => g (productCoordinates z).1 i *
          Real.exp (c * (productCoordinates z).2)) φ hφ.2.2
      simp only [liftedValue, mul_assoc] at hd hm
      rw [hd, hm] at he
      simpa [liftedValue, liftedGradient, coordinateDerivative, mul_assoc] using he
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [liftedGradient] using
        memLp_lift_on_coordinate_cylinder hU hUfinite (hu.mul_const c) c hK
    · simpa [liftedGradient] using
        memLp_lift_on_coordinate_cylinder hU hUfinite (hg i) c hK


/-- The lifted weak datum is an actual library H¹ function, with the same
value and gradient representatives rather than a substituted witness. -/
def coordinateLiftH1 {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    Homogenization.H1Function (productCoordinates ⁻¹' (U ×ˢ K)) where
  toFun := liftedValue u c
  grad := liftedGradient u g c
  memL2 := (coordinate_lift_memH1 hU hUfinite hu hg hw c hK).2.1
  gradMemL2 := (coordinate_lift_memH1 hU hUfinite hu hg hw c hK).2.2
  hasWeakGradient := hasWeakGradientOn_of_source
    (coordinate_lift_memH1 hU hUfinite hu hg hw c hK).1

/-- The lifted matrix acts on the lifted gradient by the actual source
spatial flux and transverse mass, with Euclidean scalar products. -/
theorem lifted_flux_pairing (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ) (z p : Vec (d + 1)) :
    dot ((liftedMatrix (ρ (productCoordinates z).1)
        (α (productCoordinates z).1)).mulVec (liftedGradient u g c z)) p =
      Real.exp (c * (productCoordinates z).2) *
        dot ((α (productCoordinates z).1).mulVec (g (productCoordinates z).1))
          (fun i => p i.castSucc) +
      (ρ (productCoordinates z).1 * u (productCoordinates z).1 * c *
        Real.exp (c * (productCoordinates z).2)) * p (Fin.last d) := by
  rw [dot, Fin.sum_univ_castSucc]
  simp only [liftedMatrix_mulVec_castSucc, liftedMatrix_mulVec_last, liftedGradient,
    Fin.lastCases_castSucc, Fin.lastCases_last]
  have hm (i : Fin d) :
      ((α (productCoordinates z).1).mulVec
        (fun j => g (productCoordinates z).1 j * Real.exp (c * (productCoordinates z).2))) i =
      ((α (productCoordinates z).1).mulVec (g (productCoordinates z).1)) i *
        Real.exp (c * (productCoordinates z).2) := by
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]
  simp only [hm, dot, Finset.mul_sum]
  have hs : (∑ i : Fin d,
      ((α (productCoordinates z).1).mulVec (g (productCoordinates z).1)) i *
        Real.exp (c * (productCoordinates z).2) * p i.castSucc) =
      ∑ i : Fin d, Real.exp (c * (productCoordinates z).2) *
        (((α (productCoordinates z).1).mulVec (g (productCoordinates z).1)) i * p i.castSucc) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  ring


/-- The actual spatial eigen-equation becomes the homogeneous lifted
matrix equation against every joint compact test on a finite cylinder.
The supplied flux and mass are the literal `α ∇u` and `ρ u`. -/
theorem integral_coordinate_lift_flux_eq_zero {U : Set (Vec d)}
    (hU : MeasurableSet U) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (eigenvalue c : ℝ)
    (hc_eigenvalue : c * c = eigenvalue)
    (hF : ∀ i, LocallyIntegrableOn (fun x => ((α x).mulVec (g x)) i) U volume)
    (hm : LocallyIntegrableOn (fun x => ρ x * u x) U volume)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} {φ : Vec (d + 1) → ℝ}
    (hφ : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ K)) φ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ K),
      dot ((liftedMatrix (ρ (productCoordinates z).1)
        (α (productCoordinates z).1)).mulVec (liftedGradient u g c z))
        (gradient φ z)) = 0 := by
  have hsub : productCoordinates ⁻¹' (U ×ˢ K) ⊆
      productCoordinates ⁻¹' (U ×ˢ Set.univ) := fun _ hz => ⟨hz.1, Set.mem_univ _⟩
  have hC : MeasurableSet (productCoordinates ⁻¹' (U ×ˢ Set.univ)) :=
    (hU.prod MeasurableSet.univ).preimage
      (productCoordinates (d := d)).continuous.measurable
  have hp : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ Set.univ)) φ :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
  obtain ⟨hψ, hc, hs⟩ := productCoordinates_test hp
  have he := integral_lifted_flux_eq_zero (fun x => (α x).mulVec (g x))
    (fun x => ρ x * u x) eigenvalue c hc_eigenvalue hF hm hweak hψ hc hs
  have hsp (i : Fin d) : productCoordinates.symm (unitVector i, 0) =
      (unitVector i.castSucc : Vec (d + 1)) := by
    rw [← productCoordinates_unitVector_castSucc,
      ContinuousLinearEquiv.symm_apply_apply]
  have ht : productCoordinates.symm (0, 1) =
      (unitVector (Fin.last d) : Vec (d + 1)) := by
    rw [← productCoordinates_unitVector_last,
      ContinuousLinearEquiv.symm_apply_apply]
  simp only [← integral_productCoordinates_spatial hU,
    productCoordinates_test_fderiv (hφ.1.differentiable (by norm_num)),
    ContinuousLinearEquiv.symm_apply_apply, hsp, ht] at he
  calc
    _ = ∫ z in productCoordinates ⁻¹' (U ×ˢ Set.univ),
        dot ((liftedMatrix (ρ (productCoordinates z).1)
          (α (productCoordinates z).1)).mulVec (liftedGradient u g c z))
          (gradient φ z) := by
      symm
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hC hsub
      intro z hz
      have hn : z ∉ tsupport φ := fun h => hz.2 (hφ.2.2 h)
      simp [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn, dot]
    _ = _ := by
      convert he using 1
      apply integral_congr_ae
      apply ae_of_all
      intro z
      simpa only [gradient, coordinateDerivative] using
        lifted_flux_pairing ρ α u g c z (gradient φ z)


/-- Uniform ellipticity gives actual essentially bounded mass and matrix
entries for any spatial measure, with no regularity of the coefficients. -/
theorem uniformlyElliptic_coefficients_memLp_top {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (μ : Measure (Vec d)) :
    MemLp ρ ∞ μ ∧ ∀ i j, MemLp (fun x => α x i j) ∞ μ := by
  have hα : IsElliptic κ⁻¹ α := by
    intro x
    simpa only [inv_inv] using (h.2.2 x).2.2
  refine ⟨memLp_top_of_bound h.1.aestronglyMeasurable κ⁻¹ ?_, ?_⟩
  · apply ae_of_all
    intro x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (h.2.2 x).1)] using
      (h.2.2 x).2.1
  · intro i j
    let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    have hm : Measurable (fun x => α x i j) :=
      ((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
        h.2.1
    apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
    apply ae_of_all
    intro x
    have he := PiLp.norm_apply_le
      (WithLp.toLp 2 ((α x).mulVec (unitVector j)) : EuclideanSpace ℝ (Fin d)) i
    have hn := Correctors.isElliptic_mulVec_euclideanNorm_le (inv_pos.mpr hκ)
      hα x (unitVector j)
    rw [TimeChange.euclideanNorm_eq_norm_toLp] at hn
    have hv : ((α x).mulVec (unitVector j)) i = α x i j := by
      change dotProduct (fun k => α x i k) (Pi.single j 1) = _
      rw [dotProduct_single, mul_one]
    have hu : euclideanNorm (unitVector j) = 1 := by
      simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
    simpa only [PiLp.toLp_apply, hv, Real.norm_eq_abs, hu, mul_one] using he.trans hn

/-- The literal spatial flux and mass of an L² eigenfunction are L²;
these are consequences of the source coefficient bounds. -/
theorem uniformlyElliptic_flux_mass_memLp {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (μ : Measure (Vec d)) {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 μ) (hg : ∀ i, MemLp (fun x => g x i) 2 μ) :
    (∀ i, MemLp (fun x => ((α x).mulVec (g x)) i) 2 μ) ∧
      MemLp (fun x => ρ x * u x) 2 μ := by
  obtain ⟨hρ, hα⟩ := uniformlyElliptic_coefficients_memLp_top hκ h μ
  refine ⟨?_, hρ.mul hu⟩
  intro i
  simpa only [Matrix.mulVec, dotProduct, Pi.mul_apply] using
    memLp_finsetSum Finset.univ (fun j _ => (hα i j).mul (hg j))

/-- Actual uniformly elliptic eigenfunction data imply the homogeneous
matrix equation for the lift with transverse rate `sqrt eigenvalue`.
Flux and mass integrability are proved here, rather than assumed. -/
theorem integral_coordinate_lift_eigenfunction_eq_zero {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} {φ : Vec (d + 1) → ℝ}
    (hφ : IsSpatialTest (productCoordinates ⁻¹' (U ×ˢ K)) φ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ K),
      dot ((liftedMatrix (ρ (productCoordinates z).1)
        (α (productCoordinates z).1)).mulVec
          (liftedGradient u g (Real.sqrt eigenvalue) z)) (gradient φ z)) = 0 := by
  letI : IsFiniteMeasure (volume.restrict U) :=
    isFiniteMeasure_restrict.mpr hUfinite
  obtain ⟨hF, hm⟩ := uniformlyElliptic_flux_mass_memLp hκ h (volume.restrict U) hu hg
  have hFloc (i : Fin d) :
      LocallyIntegrableOn (fun x => ((α x).mulVec (g x)) i) U volume :=
    (show IntegrableOn (fun x => ((α x).mulVec (g x)) i) U volume from
      (hF i).integrable (by norm_num)).locallyIntegrableOn
  have hmloc : LocallyIntegrableOn (fun x => ρ x * u x) U volume :=
    (show IntegrableOn (fun x => ρ x * u x) U volume from
      hm.integrable (by norm_num)).locallyIntegrableOn
  exact integral_coordinate_lift_flux_eq_zero hU ρ α u g eigenvalue
    (Real.sqrt eigenvalue) (by simpa only [← pow_two] using Real.sq_sqrt heigenvalue)
    hFloc hmloc hweak hφ


/-- The scalar L² pairing is the integral of the actual representatives. -/
theorem inner_toLp_eq_integral_mul {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply, conj_trivial, hfx, hgx]
  ring

/-- L² convergence of representatives gives convergence against a fixed
L² flux component, without pointwise convergence assumptions. -/
theorem tendsto_integral_mul_of_eLpNorm_sub {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f g : X → ℝ} {v : ℕ → X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hv : ∀ n, MemLp (v n) 2 μ)
    (ht : Filter.Tendsto (fun n => eLpNorm (fun x => v n x - g x) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x, f x * v n x ∂μ) Filter.atTop
      (nhds (∫ x, f x * g x ∂μ)) := by
  have hLp : Filter.Tendsto (fun n => (hv n).toLp (v n)) Filter.atTop
      (nhds (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' v hv g hg).mpr ht
  have hi := Filter.Tendsto.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hf.toLp f)) hLp
  simpa only [inner_toLp_eq_integral_mul] using hi

/-- Coordinatewise L² convergence is sufficient for convergence of the
Euclidean flux pairing in every finite dimension. -/
theorem tendsto_integral_dot_of_eLpNorm_sub {X : Type*} [MeasurableSpace X]
    {n : ℕ} (μ : Measure X) {F g : X → Vec n} {v : ℕ → X → Vec n}
    (hF : ∀ i, MemLp (fun x => F x i) 2 μ)
    (hg : ∀ i, MemLp (fun x => g x i) 2 μ)
    (hv : ∀ k i, MemLp (fun x => v k x i) 2 μ)
    (ht : ∀ i, Filter.Tendsto
      (fun k => eLpNorm (fun x => v k x i - g x i) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun k => ∫ x, dot (F x) (v k x) ∂μ) Filter.atTop
      (nhds (∫ x, dot (F x) (g x) ∂μ)) := by
  have hi := tendsto_finsetSum Finset.univ (fun i _ =>
    tendsto_integral_mul_of_eLpNorm_sub μ (hF i) (hg i) (fun k => hv k i) (ht i))
  have heq (k : ℕ) : (∫ x, dot (F x) (v k x) ∂μ) =
      ∑ i, ∫ x, F x i * v k x i ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hv k i))
  have heqg : (∫ x, dot (F x) (g x) ∂μ) = ∑ i, ∫ x, F x i * g x i ∂μ :=
    integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hg i))
  rw [heqg]
  exact hi.congr fun k => (heq k).symm

/-- A distributionally divergence-free L² flux annihilates every actual
native H¹₀ test, by its defining smooth approximation. -/
theorem integral_flux_dot_H10_eq_zero {n : ℕ} {Ω : Set (Vec n)}
    {F : Vec n → Vec n}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict Ω))
    (hweak : ∀ φ : Vec n → ℝ, IsSpatialTest Ω φ →
      (∫ x in Ω, dot (F x) (gradient φ x)) = 0)
    (v : Homogenization.H10Function Ω) :
    (∫ x in Ω, dot (F x) (v.toH1Function.grad x)) = 0 := by
  have happrox (k : ℕ) (i : Fin n) :
      MemLp (fun x => gradient (v.approx k) x i) 2 (volume.restrict Ω) := by
    have hc : Continuous (fun x => fderiv ℝ (v.approx k) x (unitVector i)) :=
      ((v.approx_smooth k).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact (hc.memLp_of_hasCompactSupport
      ((v.approx_hasCompactSupport k).fderiv_apply (𝕜 := ℝ) (unitVector i))).restrict Ω
  have ht (i : Fin n) : Filter.Tendsto
      (fun k => eLpNorm
        (fun x => gradient (v.approx k) x i - v.toH1Function.grad x i) 2
        (volume.restrict Ω)) Filter.atTop (nhds 0) := by
    simpa only [gradient, coordinateDerivative, Homogenization.basisVec, unitVector] using v.tendsto_approx_grad i
  have hi := tendsto_integral_dot_of_eLpNorm_sub (volume.restrict Ω) hF
    v.toH1Function.gradMemL2 happrox ht
  have hz (k : ℕ) : (∫ x in Ω, dot (F x) (gradient (v.approx k) x)) = 0 :=
    hweak (v.approx k) ⟨v.approx_smooth k, v.approx_hasCompactSupport k,
      v.approx_support_subset k⟩
  exact tendsto_nhds_unique hi ((tendsto_const_nhds (x := (0 : ℝ))).congr
    fun k => (hz k).symm)


/-- The literal lifted coefficient applied to the lifted gradient. -/
def liftedFlux (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ) (z : Vec (d + 1)) : Vec (d + 1) :=
  (liftedMatrix (ρ (productCoordinates z).1) (α (productCoordinates z).1)).mulVec
    (liftedGradient u g c z)

@[simp]
theorem liftedFlux_castSucc (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ) (z : Vec (d + 1)) (i : Fin d) :
    liftedFlux ρ α u g c z i.castSucc =
      ((α (productCoordinates z).1).mulVec (g (productCoordinates z).1)) i *
        Real.exp (c * (productCoordinates z).2) := by
  unfold liftedFlux
  rw [liftedMatrix_mulVec_castSucc]
  simp only [liftedGradient, Fin.lastCases_castSucc, Matrix.mulVec, dotProduct,
    Finset.sum_mul, mul_assoc]

@[simp]
theorem liftedFlux_last (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : Vec d → ℝ) (g : Vec d → Vec d) (c : ℝ) (z : Vec (d + 1)) :
    liftedFlux ρ α u g c z (Fin.last d) =
      (ρ (productCoordinates z).1 * u (productCoordinates z).1 * c) *
        Real.exp (c * (productCoordinates z).2) := by
  simp only [liftedFlux, liftedMatrix_mulVec_last, liftedGradient,
    Fin.lastCases_last, mul_assoc]

/-- The actual lifted flux is L² on finite cylinders; no smoothness of
coefficients or extra flux-integrability hypothesis is used. -/
theorem liftedFlux_memLp {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (c : ℝ) {K : Set ℝ} (hK : IsCompact K) :
    ∀ j, MemLp (fun z => liftedFlux ρ α u g c z j) 2
      (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) := by
  obtain ⟨hF, hm⟩ := uniformlyElliptic_flux_mass_memLp hκ h (volume.restrict U) hu hg
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [liftedFlux_last, Pi.mul_apply] using
      memLp_lift_on_coordinate_cylinder hU hUfinite (hm.mul_const c) c hK
  · simpa only [liftedFlux_castSucc] using
      memLp_lift_on_coordinate_cylinder hU hUfinite (hF i) c hK

/-- A flux pairing with a smooth test depends only on the test-support
region, including when the larger cylinder is not open. -/
theorem setIntegral_flux_dot_test_eq {n : ℕ} {Ω C : Set (Vec n)}
    (hC : MeasurableSet C) (hΩC : Ω ⊆ C) (F : Vec n → Vec n)
    {φ : Vec n → ℝ} (hφ : IsSpatialTest Ω φ) :
    (∫ x in C, dot (F x) (gradient φ x)) =
      ∫ x in Ω, dot (F x) (gradient φ x) := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hC hΩC
  intro x hx
  have hgrad : gradient φ x = 0 := by
    funext i
    have hn : x ∉ tsupport (fun y => fderiv ℝ φ y (unitVector i)) :=
      fun hmem => hx.2 (hφ.2.2 (tsupport_fderiv_apply_subset ℝ (unitVector i) hmem))
    change fderiv ℝ φ x (unitVector i) = 0
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ φ y (unitVector i)) hn
  rw [hgrad]
  simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-- Smooth-test identities on a cylinder extend to native H¹₀ tests on
any smaller region, with the literal restricted L² flux. -/
theorem integral_flux_dot_H10_eq_zero_of_subset {n : ℕ} {Ω C : Set (Vec n)}
    (hC : MeasurableSet C) (hΩC : Ω ⊆ C) {F : Vec n → Vec n}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict C))
    (hweak : ∀ φ : Vec n → ℝ, IsSpatialTest C φ →
      (∫ x in C, dot (F x) (gradient φ x)) = 0)
    (v : Homogenization.H10Function Ω) :
    (∫ x in Ω, dot (F x) (v.toH1Function.grad x)) = 0 := by
  apply integral_flux_dot_H10_eq_zero
    (fun i => (hF i).mono_measure (Measure.restrict_mono hΩC le_rfl))
  intro φ hφ
  rw [← setIntegral_flux_dot_test_eq hC hΩC F hφ]
  exact hweak φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hΩC⟩

/-- The genuine lifted eigenfunction equation holds against every native
H¹₀ test on every subregion of a finite cylinder. -/
theorem integral_lifted_eigenfunction_H10_eq_zero {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))}
    (hΩ : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K))
    (v : Homogenization.H10Function Ω) :
    (∫ z in Ω, dot (liftedFlux ρ α u g (Real.sqrt eigenvalue) z)
      (v.toH1Function.grad z)) = 0 := by
  apply integral_flux_dot_H10_eq_zero_of_subset
    ((hU.prod hK.measurableSet).preimage
      (productCoordinates (d := d)).continuous.measurable) hΩ
    (liftedFlux_memLp hκ h hU hUfinite hu hg (Real.sqrt eigenvalue) hK)
  intro φ hφ
  exact integral_coordinate_lift_eigenfunction_eq_zero hκ h hU hUfinite hu hg
    eigenvalue heigenvalue hweak hφ

/-- The squared L² integral of the actual exponential lift factors into
its spatial and transverse integrals under the measure-preserving coordinates. -/
theorem integral_liftedValue_sq {U : Set (Vec d)} (hU : MeasurableSet U)
    {K : Set ℝ} (hK : MeasurableSet K) (u : Vec d → ℝ) (c : ℝ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ K), (liftedValue u c z) ^ 2) =
      (∫ x in U, u x ^ 2) * ∫ s in K, Real.exp (c * s) ^ 2 := by
  calc
    _ = ∫ p : Vec d × ℝ, u p.1 ^ 2 * Real.exp (c * p.2) ^ 2
        ∂(volume.restrict U).prod (volume.restrict K) := by
      simpa only [liftedValue, mul_pow] using
        (productCoordinates_measurePreserving_cylinder hU hK).integral_comp
          productCoordinates.toHomeomorph.measurableEmbedding
          (fun p : Vec d × ℝ => u p.1 ^ 2 * Real.exp (c * p.2) ^ 2)
    _ = _ := integral_prod_mul (μ := volume.restrict U) (ν := volume.restrict K)
      (fun x => u x ^ 2) (fun s => Real.exp (c * s) ^ 2)

/-- The transverse L² factor stays controlled when the exponential changes
by at most one on the positive half of the interval. -/
theorem integral_exp_sq_Icc_le {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hcr : c * r ≤ 1) :
    (∫ s in Set.Icc (-r) r, Real.exp (c * s) ^ 2) ≤
      2 * r * Real.exp 2 := by
  have hf : Continuous (fun s : ℝ => Real.exp (c * s) ^ 2) := by fun_prop
  have hi : IntegrableOn (fun s : ℝ => Real.exp (c * s) ^ 2)
      (Set.Icc (-r) r) volume :=
    hf.continuousOn.integrableOn_compact isCompact_Icc
  have hb : ∀ s ∈ Set.Icc (-r) r, Real.exp (c * s) ^ 2 ≤ Real.exp 2 := by
    intro s hs
    rw [sq, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hcs := (mul_le_mul_of_nonneg_left hs.2 hc).trans hcr
    linarith
  calc
    _ ≤ ∫ _s in Set.Icc (-r) r, Real.exp 2 := by
      apply integral_mono_ae hi (integrableOn_const isCompact_Icc.measure_lt_top.ne)
      exact (ae_restrict_mem measurableSet_Icc).mono fun s hs => hb s hs
    _ = 2 * r * Real.exp 2 := by
      simp only [setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ r - -r)]
      ring

/-- A cylinder of radius at most the inverse exponential scale has spatial
L² control with the explicit transverse factor. -/
theorem integral_liftedValue_sq_le {U : Set (Vec d)} (hU : MeasurableSet U)
    (u : Vec d → ℝ) {c r : ℝ} (hc : 0 ≤ c) (hr : 0 ≤ r)
    (hcr : c * r ≤ 1) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r),
      (liftedValue u c z) ^ 2) ≤
      (2 * r * Real.exp 2) * ∫ x in U, u x ^ 2 := by
  rw [integral_liftedValue_sq hU measurableSet_Icc]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (integral_exp_sq_Icc_le hc hr hcr) (integral_nonneg fun x => sq_nonneg (u x))

/-- The interior scale is bounded both by the available spatial radius
and by the inverse eigenfunction growth scale. -/
def eigenfunctionLiftRadius (δ eigenvalue : ℝ) : ℝ :=
  min δ (1 + Real.sqrt eigenvalue)⁻¹

theorem eigenfunctionLiftRadius_pos {δ eigenvalue : ℝ} (hδ : 0 < δ) :
    0 < eigenfunctionLiftRadius δ eigenvalue := by
  exact lt_min hδ (inv_pos.mpr (by positivity))

theorem eigenfunctionLiftRadius_le (δ eigenvalue : ℝ) :
    eigenfunctionLiftRadius δ eigenvalue ≤ δ := min_le_left _ _

theorem sqrt_mul_eigenfunctionLiftRadius_le_one (δ eigenvalue : ℝ) :
    Real.sqrt eigenvalue * eigenfunctionLiftRadius δ eigenvalue ≤ 1 := by
  have hp : 0 < 1 + Real.sqrt eigenvalue := by positivity
  calc
    _ ≤ Real.sqrt eigenvalue * (1 + Real.sqrt eigenvalue)⁻¹ :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (Real.sqrt_nonneg _)
    _ ≤ (1 + Real.sqrt eigenvalue) * (1 + Real.sqrt eigenvalue)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (inv_nonneg.mpr hp.le)
    _ = 1 := mul_inv_cancel₀ hp.ne'

/-- The actual eigenfunction lift has a uniform transverse L² factor at
the interior radius selected from its eigenvalue and spatial clearance. -/
theorem integral_eigenfunctionLift_sq_le {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : Vec d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (eigenvalue : ℝ) :
    (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.Icc
      (-eigenfunctionLiftRadius δ eigenvalue) (eigenfunctionLiftRadius δ eigenvalue)),
      (liftedValue u (Real.sqrt eigenvalue) z) ^ 2) ≤
      (2 * eigenfunctionLiftRadius δ eigenvalue * Real.exp 2) *
        ∫ x in U, u x ^ 2 :=
  integral_liftedValue_sq_le hU u (Real.sqrt_nonneg _)
    (eigenfunctionLiftRadius_pos hδ).le
    (sqrt_mul_eigenfunctionLiftRadius_le_one δ eigenvalue)

/-- The coordinate carrier of Euclidean space, retaining the Euclidean
volume rather than identifying its norm with the native product norm. -/
def euclideanCoordinates (n : ℕ) : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Vec n :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)

@[simp]
theorem euclideanCoordinates_single {n : ℕ} (i : Fin n) :
    euclideanCoordinates n (EuclideanSpace.single i 1) = unitVector i := rfl

@[simp]
theorem euclideanCoordinates_symm_unitVector {n : ℕ} (i : Fin n) :
    (euclideanCoordinates n).symm (unitVector i) = EuclideanSpace.single i 1 := rfl

/-- Euclidean coordinates preserve actual Lebesgue volume. -/
theorem euclideanCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (euclideanCoordinates n) volume volume :=
  PiLp.volume_preserving_ofLp (Fin n)

/-- The reverse coordinate map also preserves actual Lebesgue volume. -/
theorem euclideanCoordinates_symm_measurePreserving (n : ℕ) :
    MeasurePreserving (euclideanCoordinates n).symm volume volume :=
  PiLp.volume_preserving_toLp (Fin n)

theorem euclideanCoordinates_measurePreserving_restrict {n : ℕ}
    {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω) :
    MeasurePreserving (euclideanCoordinates n)
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) (volume.restrict Ω) :=
  (euclideanCoordinates_measurePreserving n).restrict_preimage hΩ

theorem euclideanCoordinates_symm_measurePreserving_restrict {n : ℕ}
    {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω) :
    MeasurePreserving (euclideanCoordinates n).symm (volume.restrict Ω)
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) := by
  have hm := (euclideanCoordinates_symm_measurePreserving n).restrict_preimage
    (hΩ.preimage (euclideanCoordinates n).continuous.measurable)
  have he : (euclideanCoordinates n).symm ⁻¹' (euclideanCoordinates n ⁻¹' Ω) = Ω := by
    ext x
    simp only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
  rw [he] at hm
  exact hm

/-- Restricted change of variables from Euclidean to native coordinates. -/
theorem integral_euclideanCoordinates {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) (f : Vec n → ℝ) :
    (∫ z in euclideanCoordinates n ⁻¹' Ω, f (euclideanCoordinates n z)) =
      ∫ x in Ω, f x :=
  (euclideanCoordinates_measurePreserving_restrict hΩ).integral_comp
    (euclideanCoordinates n).toHomeomorph.measurableEmbedding f

/-- The reverse coordinate change preserves every scalar Lᵖ seminorm,
including the seminorms of smooth approximation errors. -/
theorem eLpNorm_euclideanCoordinates_symm {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) (f : EuclideanSpace ℝ (Fin n) → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => f ((euclideanCoordinates n).symm x)) p (volume.restrict Ω) =
      eLpNorm f p (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) := by
  have he : MeasurableEmbedding (euclideanCoordinates n).symm :=
    (euclideanCoordinates n).symm.toHomeomorph.measurableEmbedding
  have ht := he.eLpNorm_map_measure (g := f) (p := p) (μ := volume.restrict Ω)
  rw [(euclideanCoordinates_symm_measurePreserving_restrict hΩ).map_eq] at ht
  exact ht.symm

/-- The coordinate chain rule for Euclidean test functions. -/
theorem euclideanCoordinates_test_fderiv {n : ℕ} {φ : Vec n → ℝ}
    (hφ : Differentiable ℝ φ) (z w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => φ (euclideanCoordinates n y)) z w =
      fderiv ℝ φ (euclideanCoordinates n z) (euclideanCoordinates n w) := by
  change (fderiv ℝ (φ ∘ euclideanCoordinates n) z) w = _
  rw [fderiv_comp z hφ.differentiableAt (euclideanCoordinates n).differentiableAt,
    ContinuousLinearEquiv.fderiv]
  rfl

/-- The inverse coordinate chain rule for native test functions. -/
theorem euclideanCoordinates_symm_test_fderiv {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Differentiable ℝ φ) (x v : Vec n) :
    fderiv ℝ (fun y => φ ((euclideanCoordinates n).symm y)) x v =
      fderiv ℝ φ ((euclideanCoordinates n).symm x) ((euclideanCoordinates n).symm v) := by
  change (fderiv ℝ (φ ∘ (euclideanCoordinates n).symm) x) v = _
  rw [fderiv_comp x hφ.differentiableAt (euclideanCoordinates n).symm.differentiableAt,
    ContinuousLinearEquiv.fderiv]
  rfl

/-- Every Euclidean distributional coordinate identity transports to the
native Sobolev predicate, without assuming smoothness of the weak function. -/
theorem hasWeakGradientOn_of_euclidean {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hw : ∀ i : Fin n, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        u z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, G z i * φ z) :
    Homogenization.HasWeakGradientOn Ω (fun x => u ((euclideanCoordinates n).symm x))
      (fun x i => G ((euclideanCoordinates n).symm x) i) := by
  intro i φ hφ hφc hφΩ
  have ht : tsupport (fun z => φ (euclideanCoordinates n z)) ⊆
      euclideanCoordinates n ⁻¹' Ω := by
    intro z hz
    exact hφΩ ((tsupport_comp_subset_preimage φ (euclideanCoordinates n).continuous) hz)
  have hi := hw i (fun z => φ (euclideanCoordinates n z))
    (hφ.comp (euclideanCoordinates n).contDiff)
    (hφc.comp_homeomorph (euclideanCoordinates n).toHomeomorph) ht
  rw [← integral_euclideanCoordinates hΩ (fun x =>
      u ((euclideanCoordinates n).symm x) * fderiv ℝ φ x (Homogenization.basisVec i)),
    ← integral_euclideanCoordinates hΩ (fun x =>
      G ((euclideanCoordinates n).symm x) i * φ x)]
  simpa only [euclideanCoordinates_test_fderiv (hφ.differentiable (by simp)),
    euclideanCoordinates_single, ContinuousLinearEquiv.symm_apply_apply,
    Homogenization.basisVec, unitVector] using hi

/-- Native coordinate partial derivatives of pulled-back Euclidean tests
are exactly their original Euclidean partial derivatives. -/
theorem euclideanCoordinates_symm_test_partial {n : ℕ}
    {φ : EuclideanSpace ℝ (Fin n) → ℝ} (hφ : Differentiable ℝ φ)
    (x : Vec n) (i : Fin n) :
    fderiv ℝ (fun y => φ ((euclideanCoordinates n).symm y)) x
        (Homogenization.basisVec i) =
      fderiv ℝ φ ((euclideanCoordinates n).symm x) (EuclideanSpace.single i 1) := by
  rw [euclideanCoordinates_symm_test_fderiv hφ]
  rfl

/-- Literal Euclidean H¹ witness data give a native H¹ function with the
same values and gradient components under the volume-preserving coordinates. -/
def nativeH1OfEuclidean {n : ℕ} {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : MemLp u 2 (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hw : ∀ i : Fin n, ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        u z * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, G z i * φ z) :
    Homogenization.H1Function Ω where
  toFun := fun x => u ((euclideanCoordinates n).symm x)
  grad := fun x i => G ((euclideanCoordinates n).symm x) i
  memL2 := hu.comp_measurePreserving
    (euclideanCoordinates_symm_measurePreserving_restrict hΩ)
  gradMemL2 := fun i => (hG i).comp_measurePreserving
    (euclideanCoordinates_symm_measurePreserving_restrict hΩ)
  hasWeakGradient := hasWeakGradientOn_of_euclidean hΩ hw

/-- Euclidean zero-trace witness data, including its actual smooth
approximating sequence, transport to the native H¹₀ structure. -/
def nativeH10OfEuclidean {n : ℕ} {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : MemLp u 2 (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hw : ∀ i : Fin n, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        u z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, G z i * ψ z)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k))
    (hφc : ∀ k, HasCompactSupport (φ k))
    (hφΩ : ∀ k, tsupport (φ k) ⊆ euclideanCoordinates n ⁻¹' Ω)
    (hv : Tendsto (fun k => eLpNorm (fun z => φ k z - u z) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0))
    (hg : ∀ i, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0)) :
    Homogenization.H10Function Ω where
  toH1Function := nativeH1OfEuclidean hΩ hu hG hw
  approx := fun k x => φ k ((euclideanCoordinates n).symm x)
  approx_smooth := fun k => (hφ k).comp (euclideanCoordinates n).symm.contDiff
  approx_hasCompactSupport := fun k =>
    (hφc k).comp_homeomorph (euclideanCoordinates n).symm.toHomeomorph
  approx_support_subset := by
    intro k x hx
    have ht := hφΩ k ((tsupport_comp_subset_preimage (φ k)
      (euclideanCoordinates n).symm.continuous) hx)
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using ht
  tendsto_approx := by
    convert hv using 1
    funext k
    exact eLpNorm_euclideanCoordinates_symm hΩ (fun z => φ k z - u z) 2
  tendsto_approx_grad := by
    intro i
    convert hg i using 1
    funext k
    simp only [euclideanCoordinates_symm_test_partial ((hφ k).differentiable (by simp))]
    exact eLpNorm_euclideanCoordinates_symm hΩ
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - G z i) 2


/-- Native distributional coordinate identities transport back to the
Euclidean carrier with its actual coordinate vectors. -/
theorem euclidean_weak_gradient_of_native {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) {u : Vec n → ℝ} {G : Vec n → Vec n}
    (hw : Homogenization.HasWeakGradientOn Ω u G) (i : Fin n)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ euclideanCoordinates n ⁻¹' Ω) :
    (∫ z in euclideanCoordinates n ⁻¹' Ω,
      u (euclideanCoordinates n z) * fderiv ℝ φ z (EuclideanSpace.single i 1)) =
      -∫ z in euclideanCoordinates n ⁻¹' Ω,
        G (euclideanCoordinates n z) i * φ z := by
  have ht : tsupport (fun x => φ ((euclideanCoordinates n).symm x)) ⊆ Ω := by
    intro x hx
    have hz := hφΩ ((tsupport_comp_subset_preimage φ
      (euclideanCoordinates n).symm.continuous) hx)
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hz
  have hi := hw i (fun x => φ ((euclideanCoordinates n).symm x))
    (hφ.comp (euclideanCoordinates n).symm.contDiff)
    (hφc.comp_homeomorph (euclideanCoordinates n).symm.toHomeomorph) ht
  rw [← integral_euclideanCoordinates hΩ (fun x => u x *
      fderiv ℝ (fun y => φ ((euclideanCoordinates n).symm y)) x
        (Homogenization.basisVec i)),
    ← integral_euclideanCoordinates hΩ (fun x => G x i *
      φ ((euclideanCoordinates n).symm x))] at hi
  simpa only [euclideanCoordinates_symm_test_partial (hφ.differentiable (by simp)),
    ContinuousLinearEquiv.symm_apply_apply] using hi

/-- The Euclidean value and each gradient component retain their native
L² bounds under the forward coordinate change. -/
theorem memLp_euclideanCoordinates {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) {f : Vec n → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) :
    MemLp (fun z => f (euclideanCoordinates n z)) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) :=
  hf.comp_measurePreserving (euclideanCoordinates_measurePreserving_restrict hΩ)

/-- A native divergence-free L² flux annihilates every Euclidean zero-trace
test supplied with its actual weak gradient and smooth approximation data. -/
theorem integral_flux_dot_euclideanH10_eq_zero {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) {F : Vec n → Vec n}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict Ω))
    (hweak : ∀ ψ : Vec n → ℝ, IsSpatialTest Ω ψ →
      (∫ x in Ω, dot (F x) (gradient ψ x)) = 0)
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hu : MemLp u 2 (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hw : ∀ i : Fin n, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        u z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, G z i * ψ z)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k))
    (hφc : ∀ k, HasCompactSupport (φ k))
    (hφΩ : ∀ k, tsupport (φ k) ⊆ euclideanCoordinates n ⁻¹' Ω)
    (hv : Tendsto (fun k => eLpNorm (fun z => φ k z - u z) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0))
    (hg : ∀ i, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0)) :
    (∫ z in euclideanCoordinates n ⁻¹' Ω,
      dot (F (euclideanCoordinates n z)) (fun i => G z i)) = 0 := by
  have ht := integral_flux_dot_H10_eq_zero hF hweak
    (nativeH10OfEuclidean hΩ hu hG hw φ hφ hφc hφΩ hv hg)
  change (∫ x in Ω, dot (F x) (fun i => G ((euclideanCoordinates n).symm x) i)) = 0 at ht
  rw [← integral_euclideanCoordinates hΩ (fun x =>
    dot (F x) (fun i => G ((euclideanCoordinates n).symm x) i))] at ht
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using ht

/-- A continuous lifted representative can be integrated against a compact
transverse weight even when continuity is only known on the cylinder. -/
theorem integrable_transverse_weight_mul {U : Set (Vec d)} {a b : ℝ}
    {v : Vec d × ℝ → ℝ} (hv : ContinuousOn v (U ×ˢ Set.Icc a b))
    {η : ℝ → ℝ} (hη : Continuous η) (hs : tsupport η ⊆ Set.Icc a b)
    {x : Vec d} (hx : x ∈ U) :
    Integrable (fun s => η s * v (x, s)) := by
  have hcont : ContinuousOn (fun s => η s * v (x, s)) (Set.Icc a b) :=
    hη.continuousOn.mul (hv.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun s hs => ⟨hx, hs⟩))
  apply (hcont.integrableOn_compact isCompact_Icc).integrable_of_forall_notMem_eq_zero
  intro s hs'
  rw [image_eq_zero_of_notMem_tsupport (fun ht => hs' (hs ht)), zero_mul]

/-- A transverse average inherits any uniform oscillation bound on its
cylinder. Both slice integrals are genuine integrable functions. -/
theorem transverse_average_sub_le {U : Set (Vec d)} {a b : ℝ}
    {v : Vec d × ℝ → ℝ} (hv : ContinuousOn v (U ×ˢ Set.Icc a b))
    {η : ℝ → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Icc a b) (hn : ∀ s, 0 ≤ η s)
    {M : ℝ} (hM : 0 < M) {x y : Vec d} (hx : x ∈ U) (hy : y ∈ U)
    {H : ℝ} (hosc : ∀ s ∈ Set.Icc a b, |v (x, s) - v (y, s)| ≤ H) :
    |(∫ s, η s * v (x, s)) / M - (∫ s, η s * v (y, s)) / M| ≤
      ((∫ s, η s) / M) * H := by
  have hix := integrable_transverse_weight_mul hv hη hs hx
  have hiy := integrable_transverse_weight_mul hv hη hs hy
  have hbound : |∫ s, η s * (v (x, s) - v (y, s))| ≤ ∫ s, η s * H := by
    rw [← Real.norm_eq_abs]
    apply norm_integral_le_of_norm_le ((hη.integrable_of_hasCompactSupport hc).mul_const H)
    filter_upwards [] with s
    change |η s * (v (x, s) - v (y, s))| ≤ η s * H
    rw [abs_mul, abs_of_nonneg (hn s)]
    by_cases ht : s ∈ tsupport η
    · exact mul_le_mul_of_nonneg_left (hosc s (hs ht)) (hn s)
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_mul, zero_mul]
  calc
    _ = |∫ s, η s * (v (x, s) - v (y, s))| / M := by
      rw [← sub_div, abs_div, abs_of_pos hM, ← integral_sub hix hiy]
      simp only [mul_sub]
    _ ≤ (∫ s, η s * H) / M := div_le_div_of_nonneg_right hbound hM.le
    _ = _ := by rw [integral_mul_const]; ring

/-- The mass of a nonnegative transverse weight divided by its exponential
moment costs at most `exp (|c| * r)` on a symmetric cylinder. The estimate
retains signed transverse rates. -/
theorem transverse_mass_div_exponential_moment_le {r : ℝ}
    (c : ℝ) {η : ℝ → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Icc (-r) r) (hn : ∀ s, 0 ≤ η s)
    {s₀ : ℝ} (hs₀ : η s₀ ≠ 0) :
    (∫ s, η s) / (∫ s, η s * Real.exp (c * s)) ≤ Real.exp (|c| * r) := by
  have hM := transverse_exponential_moment_pos c hη hc hn hs₀
  have hi : Integrable (fun s => η s * Real.exp (c * s)) :=
    (hη.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      hc.mul_right
  apply (div_le_iff₀ hM).mpr
  rw [← integral_const_mul]
  apply integral_mono (hη.integrable_of_hasCompactSupport hc)
    (hi.const_mul _)
  intro s
  change η s ≤ Real.exp (|c| * r) * (η s * Real.exp (c * s))
  by_cases ht : s ∈ tsupport η
  · have habs : |s| ≤ r := abs_le.mpr (hs ht)
    have hcs : -(|c| * r) ≤ c * s :=
      (neg_le_neg (mul_le_mul_of_nonneg_left habs (abs_nonneg c))).trans
        (by rw [← abs_mul]; exact neg_abs_le (c * s))
    have he : 1 ≤ Real.exp (|c| * r + c * s) := Real.one_le_exp_iff.mpr (by linarith)
    calc
      η s = η s * 1 := (mul_one _).symm
      _ ≤ η s * Real.exp (|c| * r + c * s) :=
        mul_le_mul_of_nonneg_left he (hn s)
      _ = _ := by rw [Real.exp_add]; ring
  · simp only [image_eq_zero_of_notMem_tsupport ht, zero_mul, mul_zero, le_refl]

/-- Quantitative descent of a supplied lifted representative by Fubini and
compact transverse averaging. The spatial seminorm uses the actual Euclidean
distance, and the radius and signed exponential rate remain explicit. -/
theorem exists_continuousOn_ae_eq_holder_of_lift {U : Set (Vec d)}
    {r : ℝ} (hr : 0 < r) {v : Vec d × ℝ → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.Icc (-r) r)) (c : ℝ)
    (heq : v =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc (-r) r))]
      fun z => u z.1 * Real.exp (c * z.2))
    {η : ℝ → ℝ} (hη : Continuous η) (hc : HasCompactSupport η)
    (hs : tsupport η ⊆ Set.Icc (-r) r) (hn : ∀ s, 0 ≤ η s)
    {s₀ : ℝ} (hs₀ : η s₀ ≠ 0) {K β : ℝ} (hK : 0 ≤ K)
    (hosc : ∀ x ∈ U, ∀ y ∈ U, ∀ s ∈ Set.Icc (-r) r,
      |v (x, s) - v (y, s)| ≤ K * (euclideanNorm (x - y)) ^ β) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |w x - w y| ≤ Real.exp (|c| * r) * K * (euclideanNorm (x - y)) ^ β := by
  let M : ℝ := ∫ s, η s * Real.exp (c * s)
  have hM : 0 < M := transverse_exponential_moment_pos c hη hc hn hs₀
  have hcont := transverse_average_continuousOn_cylinder (by linarith : -r ≤ r)
    hv hη hc hs M
  have hae : (fun x => (∫ s, η s * v (x, s)) / M) =ᵐ[volume.restrict U] u := by
    have hrestrict (f : ℝ → ℝ) :
        (∫ s in Set.Icc (-r) r, η s * f s) = ∫ s, η s * f s := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro s hnot
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hnot (hs ht)), zero_mul]
    have hm : (∫ s in Set.Icc (-r) r, η s * Real.exp (c * s)) ≠ 0 := by
      rw [hrestrict]
      exact ne_of_gt hM
    simpa only [hrestrict, M] using
      transverse_average_ae_eq (volume.restrict U) (volume.restrict (Set.Icc (-r) r))
        c η heq hm
  refine ⟨_, hcont, hae, ?_⟩
  intro x hx y hy
  calc
    _ ≤ ((∫ s, η s) / M) * (K * (euclideanNorm (x - y)) ^ β) :=
      transverse_average_sub_le hv hη hc hs hn hM hx hy (hosc x hx y hy)
    _ ≤ Real.exp (|c| * r) * (K * (euclideanNorm (x - y)) ^ β) :=
      mul_le_mul_of_nonneg_right
        (transverse_mass_div_exponential_moment_le c hη hc hs hn hs₀)
        (mul_nonneg hK (Real.rpow_nonneg (Real.sqrt_nonneg _) _))
    _ = _ := (mul_assoc _ _ _).symm

/-- A concrete compact transverse weight. Smoothness is unnecessary for
averaging a continuous representative. -/
def transverseTent (r s : ℝ) : ℝ := max (r - |s|) 0

theorem continuous_transverseTent (r : ℝ) : Continuous (transverseTent r) :=
  (continuous_const.sub continuous_abs).max continuous_const

theorem transverseTent_nonneg (r s : ℝ) : 0 ≤ transverseTent r s := le_max_right _ _

theorem tsupport_transverseTent_subset (r : ℝ) :
    tsupport (transverseTent r) ⊆ Set.Icc (-r) r := by
  apply closure_minimal _ isClosed_Icc
  intro s hs
  have hlt : |s| < r := by
    by_contra h
    exact hs (max_eq_right (sub_nonpos.mpr (not_lt.mp h)))
  exact abs_le.mp hlt.le

theorem hasCompactSupport_transverseTent (r : ℝ) : HasCompactSupport (transverseTent r) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_transverseTent_subset r)

theorem transverseTent_zero_pos {r : ℝ} (hr : 0 < r) : 0 < transverseTent r 0 := by
  simpa only [transverseTent, abs_zero, sub_zero, max_eq_left hr.le] using hr

/-- The quantitative descent has an actual compact averaging weight, so
its only analytic inputs concern the supplied lifted representative. -/
theorem exists_continuousOn_ae_eq_holder_of_lift_cylinder {U : Set (Vec d)}
    {r : ℝ} (hr : 0 < r) {v : Vec d × ℝ → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.Icc (-r) r)) (c : ℝ)
    (heq : v =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc (-r) r))]
      fun z => u z.1 * Real.exp (c * z.2))
    {K β : ℝ} (hK : 0 ≤ K)
    (hosc : ∀ x ∈ U, ∀ y ∈ U, ∀ s ∈ Set.Icc (-r) r,
      |v (x, s) - v (y, s)| ≤ K * (euclideanNorm (x - y)) ^ β) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |w x - w y| ≤ Real.exp (|c| * r) * K * (euclideanNorm (x - y)) ^ β :=
  exists_continuousOn_ae_eq_holder_of_lift hr hv c heq
    (continuous_transverseTent r) (hasCompactSupport_transverseTent r)
    (tsupport_transverseTent_subset r) (transverseTent_nonneg r)
    (ne_of_gt (transverseTent_zero_pos hr)) hK hosc

/-- Inverse product coordinates preserve both restricted volume measures. -/
theorem productCoordinates_symm_measurePreserving_cylinder
    {U : Set (Vec d)} (hU : MeasurableSet U) {K : Set ℝ} (hK : MeasurableSet K) :
    MeasurePreserving (productCoordinates (d := d)).symm
      ((volume.restrict U).prod (volume.restrict K))
      (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) :=
  MeasurePreserving.symm (productCoordinates (d := d)).toHomeomorph.toMeasurableEquiv
    (productCoordinates_measurePreserving_cylinder hU hK)

/-- Comparing two points at the same transverse height preserves the
spatial Euclidean distance exactly. No product supremum norm is used. -/
theorem euclideanNorm_productCoordinates_symm_sub (x y : Vec d) (s : ℝ) :
    euclideanNorm (productCoordinates.symm (x, s) - productCoordinates.symm (y, s)) =
      euclideanNorm (x - y) := by
  unfold euclideanNorm
  congr 1
  rw [productCoordinates_euclideanSq]
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply,
    Prod.fst_sub, Prod.snd_sub, sub_self, zero_pow (by norm_num : 2 ≠ 0), add_zero]

/-- A representative of the actual lift in the original coordinate carrier
descends with the same Euclidean Holder exponent. The a.e. equality is
transported through a measure-preserving equivalence before applying Fubini. -/
theorem exists_continuousOn_ae_eq_holder_of_coordinate_lift {U : Set (Vec d)}
    (hU : MeasurableSet U) {r : ℝ} (hr : 0 < r)
    {v : Vec (d + 1) → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r))) (c : ℝ)
    (heq : v =ᵐ[volume.restrict (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r))]
      liftedValue u c) {K β : ℝ} (hK : 0 ≤ K)
    (hosc : ∀ z ∈ productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r),
      ∀ z' ∈ productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r),
        |v z - v z'| ≤ K * (euclideanNorm (z - z')) ^ β) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |w x - w y| ≤ Real.exp (|c| * r) * K * (euclideanNorm (x - y)) ^ β := by
  have hvc : ContinuousOn (fun p : Vec d × ℝ => v (productCoordinates.symm p))
      (U ×ˢ Set.Icc (-r) r) :=
    hv.comp (productCoordinates (d := d)).symm.continuous.continuousOn
      (fun p hp => by simpa only [Set.mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply] using hp)
  have hae : (fun p : Vec d × ℝ => v (productCoordinates.symm p))
      =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc (-r) r))]
        (fun p => u p.1 * Real.exp (c * p.2)) := by
    simpa only [Function.comp_def, liftedValue, ContinuousLinearEquiv.apply_symm_apply]
      using (productCoordinates_symm_measurePreserving_cylinder hU measurableSet_Icc).quasiMeasurePreserving.ae_eq_comp heq
  apply exists_continuousOn_ae_eq_holder_of_lift_cylinder hr hvc c hae hK
  intro x hx y hy s hs
  have hx' : productCoordinates.symm (x, s) ∈
      productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r) := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using
      (show (x, s) ∈ U ×ˢ Set.Icc (-r) r from ⟨hx, hs⟩)
  have hy' : productCoordinates.symm (y, s) ∈
      productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r) := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using
      (show (y, s) ∈ U ×ˢ Set.Icc (-r) r from ⟨hy, hs⟩)
  simpa only [euclideanNorm_productCoordinates_symm_sub] using
    hosc _ hx' _ hy'

/-- At the previously checked eigenfunction lift scale, transverse descent
costs at most `exp 1`, uniformly in the eigenvalue and spatial clearance. -/
theorem exists_eigenfunction_continuousOn_ae_eq_holder_of_lift {U : Set (Vec d)}
    {δ : ℝ} (hδ : 0 < δ) (eigenvalue : ℝ)
    {v : Vec d × ℝ → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (U ×ˢ Set.Icc
      (-eigenfunctionLiftRadius δ eigenvalue) (eigenfunctionLiftRadius δ eigenvalue)))
    (heq : v =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc
      (-eigenfunctionLiftRadius δ eigenvalue) (eigenfunctionLiftRadius δ eigenvalue)))]
      fun z => u z.1 * Real.exp (Real.sqrt eigenvalue * z.2))
    {K β : ℝ} (hK : 0 ≤ K)
    (hosc : ∀ x ∈ U, ∀ y ∈ U, ∀ s ∈ Set.Icc
      (-eigenfunctionLiftRadius δ eigenvalue) (eigenfunctionLiftRadius δ eigenvalue),
      |v (x, s) - v (y, s)| ≤ K * (euclideanNorm (x - y)) ^ β) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |w x - w y| ≤ Real.exp 1 * K * (euclideanNorm (x - y)) ^ β := by
  obtain ⟨w, hw, hae, hbound⟩ := exists_continuousOn_ae_eq_holder_of_lift_cylinder
    (eigenfunctionLiftRadius_pos hδ) hv (Real.sqrt eigenvalue) heq hK hosc
  refine ⟨w, hw, hae, ?_⟩
  intro x hx y hy
  apply (hbound x hx y hy).trans
  have he : Real.exp (|Real.sqrt eigenvalue| * eigenfunctionLiftRadius δ eigenvalue) ≤
      Real.exp 1 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.exp_le_exp.mpr (sqrt_mul_eigenfunctionLiftRadius_le_one δ eigenvalue)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hK)
    (Real.rpow_nonneg (Real.sqrt_nonneg _) _)

/-- Dividing the lifted L² integral by the `d+1` dimensional radius power
leaves the spatial `d` dimensional normalization. -/
theorem normalized_integral_liftedValue_sq_le {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : Vec d → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 < r) (hcr : c * r ≤ 1) :
    (r ^ (d + 1))⁻¹ * (∫ z in productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r),
      (liftedValue u c z) ^ 2) ≤
      (2 * Real.exp 2) * ((r ^ d)⁻¹ * ∫ x in U, u x ^ 2) := by
  calc
    _ ≤ (r ^ (d + 1))⁻¹ * ((2 * r * Real.exp 2) * ∫ x in U, u x ^ 2) :=
      mul_le_mul_of_nonneg_left (integral_liftedValue_sq_le hU u hc hr.le hcr)
        (inv_nonneg.mpr (pow_nonneg hr.le _))
    _ = _ := by
      rw [pow_succ, mul_inv_rev]
      calc
        _ = (r * r⁻¹) * ((2 * Real.exp 2) * ((r ^ d)⁻¹ * ∫ x in U, u x ^ 2)) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hr.ne', one_mul]

/-- The L² amplitude used by an interior Holder estimate retains the
spatial radius normalization after transverse descent. -/
theorem sqrt_normalized_integral_liftedValue_sq_le {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : Vec d → ℝ) {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 < r) (hcr : c * r ≤ 1) :
    Real.sqrt ((r ^ (d + 1))⁻¹ *
      ∫ z in productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r), (liftedValue u c z) ^ 2) ≤
      Real.sqrt (2 * Real.exp 2) * Real.sqrt ((r ^ d)⁻¹ * ∫ x in U, u x ^ 2) := by
  calc
    _ ≤ Real.sqrt ((2 * Real.exp 2) * ((r ^ d)⁻¹ * ∫ x in U, u x ^ 2)) :=
      Real.sqrt_le_sqrt (normalized_integral_liftedValue_sq_le hU u hc hr hcr)
    _ = _ := Real.sqrt_mul (by positivity) _

/-- At the actual eigenfunction radius, the lifted interior L² amplitude
is controlled solely by the spatial L² integral and its `d` dimensional scale. -/
theorem sqrt_normalized_integral_eigenfunctionLift_sq_le {U : Set (Vec d)}
    (hU : MeasurableSet U) (u : Vec d → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (eigenvalue : ℝ) :
    Real.sqrt (((eigenfunctionLiftRadius δ eigenvalue) ^ (d + 1))⁻¹ *
      ∫ z in productCoordinates ⁻¹' (U ×ˢ Set.Icc
        (-eigenfunctionLiftRadius δ eigenvalue) (eigenfunctionLiftRadius δ eigenvalue)),
      (liftedValue u (Real.sqrt eigenvalue) z) ^ 2) ≤
      Real.sqrt (2 * Real.exp 2) * Real.sqrt
        (((eigenfunctionLiftRadius δ eigenvalue) ^ d)⁻¹ * ∫ x in U, u x ^ 2) :=
  sqrt_normalized_integral_liftedValue_sq_le hU u (Real.sqrt_nonneg _)
    (eigenfunctionLiftRadius_pos hδ) (sqrt_mul_eigenfunctionLiftRadius_le_one δ eigenvalue)

/-- The Euclidean carrier conversion preserves the distance appearing in
the Holder estimate; the native coordinate norm is not substituted for it. -/
theorem norm_euclideanCoordinates_symm_sub {n : ℕ} (x y : Vec n) :
    ‖(euclideanCoordinates n).symm x - (euclideanCoordinates n).symm y‖ =
      euclideanNorm (x - y) := by
  rw [← map_sub, TimeChange.euclideanNorm_eq_norm_toLp]
  rfl

/-- Quantitative transverse descent accepts a genuine Euclidean lifted
representative, with precisely the Euclidean norm supplied by interior
regularity. Its existence and estimate remain explicit analytic obligations. -/
theorem exists_continuousOn_ae_eq_holder_of_euclidean_lift {U : Set (Vec d)}
    (hU : MeasurableSet U) {r : ℝ} (hr : 0 < r)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {u : Vec d → ℝ}
    (hv : ContinuousOn v (euclideanCoordinates (d + 1) ⁻¹'
      (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r)))) (c : ℝ)
    (heq : v =ᵐ[volume.restrict (euclideanCoordinates (d + 1) ⁻¹'
      (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r)))]
      fun z => liftedValue u c (euclideanCoordinates (d + 1) z))
    {K β : ℝ} (hK : 0 ≤ K)
    (hosc : ∀ z ∈ euclideanCoordinates (d + 1) ⁻¹'
        (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r)),
      ∀ z' ∈ euclideanCoordinates (d + 1) ⁻¹'
        (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r)),
        |v z - v z'| ≤ K * ‖z - z'‖ ^ β) :
    ∃ w : Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u ∧
      ∀ x ∈ U, ∀ y ∈ U,
        |w x - w y| ≤ Real.exp (|c| * r) * K * (euclideanNorm (x - y)) ^ β := by
  let Ω : Set (Vec (d + 1)) := productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r)
  have hΩ : MeasurableSet Ω :=
    (hU.prod measurableSet_Icc).preimage (productCoordinates (d := d)).continuous.measurable
  have hmem (z : Vec (d + 1)) (hz : z ∈ Ω) :
      (euclideanCoordinates (d + 1)).symm z ∈ euclideanCoordinates (d + 1) ⁻¹' Ω := by
    simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using hz
  have hvc : ContinuousOn (fun z => v ((euclideanCoordinates (d + 1)).symm z)) Ω :=
    hv.comp (euclideanCoordinates (d + 1)).symm.continuous.continuousOn hmem
  have hae : (fun z => v ((euclideanCoordinates (d + 1)).symm z))
      =ᵐ[volume.restrict Ω] liftedValue u c := by
    simpa only [Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using
      (euclideanCoordinates_symm_measurePreserving_restrict hΩ).quasiMeasurePreserving.ae_eq_comp heq
  apply exists_continuousOn_ae_eq_holder_of_coordinate_lift hU hr hvc c hae hK
  intro z hz z' hz'
  simpa only [norm_euclideanCoordinates_symm_sub] using
    hosc _ (hmem z hz) _ (hmem z' hz')

/-- Spatial representatives obtained on overlapping open cylinders agree
throughout the overlap, since both are continuous and spatially a.e. equal
to the same function. This permits gluing averages with different weights. -/
theorem continuous_representatives_eqOn_inter {U V : Set (Vec d)}
    (hU : IsOpen U) (hV : IsOpen V) {u v w : Vec d → ℝ}
    (hv : ContinuousOn v U) (hw : ContinuousOn w V)
    (hvu : v =ᵐ[volume.restrict U] u) (hwu : w =ᵐ[volume.restrict V] u) :
    Set.EqOn v w (U ∩ V) := by
  have hv' : v =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_left hvu
  have hw' : w =ᵐ[volume.restrict (U ∩ V)] u :=
    ae_restrict_of_ae_restrict_of_subset Set.inter_subset_right hwu
  exact Measure.eqOn_open_of_ae_eq (hv'.trans hw'.symm) (hU.inter hV)
    (hv.mono Set.inter_subset_left) (hw.mono Set.inter_subset_right)


/-- The Euclidean distance from a lifted spatial centre splits into the
spatial Euclidean energy and the transverse square. -/
theorem norm_euclidean_lift_sub_center_sq (z : EuclideanSpace ℝ (Fin (d + 1)))
    (x₀ : Vec d) :
    ‖z - (euclideanCoordinates (d + 1)).symm
      (productCoordinates.symm (x₀, 0))‖ ^ 2 =
      euclideanNorm ((productCoordinates (euclideanCoordinates (d + 1) z)).1 - x₀) ^ 2 +
        (productCoordinates (euclideanCoordinates (d + 1) z)).2 ^ 2 := by
  have hn {n : ℕ} (x : Vec n) : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  rw [← (euclideanCoordinates (d + 1)).symm_apply_apply z,
    norm_euclideanCoordinates_symm_sub, hn, productCoordinates_euclideanSq]
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub,
    Prod.snd_sub, sub_zero, hn]

/-- A cylinder with both radii `R/4` lies strictly inside the half-ball
where the lifted interior estimate is available. The ambient norm is Euclidean. -/
theorem euclidean_cylinder_subset_half_ball (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    euclideanCoordinates (d + 1) ⁻¹' (productCoordinates ⁻¹'
      ({x : Vec d | euclideanNorm (x - x₀) < R / 4} ×ˢ Set.Icc (-(R / 4)) (R / 4))) ⊆
      Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (R / 2) := by
  intro z hz
  change euclideanNorm ((productCoordinates (euclideanCoordinates (d + 1) z)).1 - x₀) <
      R / 4 ∧ -(R / 4) ≤ (productCoordinates (euclideanCoordinates (d + 1) z)).2 ∧
        (productCoordinates (euclideanCoordinates (d + 1) z)).2 ≤ R / 4 at hz
  rw [Metric.mem_ball, dist_eq_norm]
  have hs := norm_euclidean_lift_sub_center_sq z x₀
  have hn : 0 ≤ euclideanNorm
      ((productCoordinates (euclideanCoordinates (d + 1) z)).1 - x₀) := Real.sqrt_nonneg _
  have ht : (productCoordinates (euclideanCoordinates (d + 1) z)).2 ^ 2 ≤ (R / 4) ^ 2 := by
    nlinarith [sq_nonneg ((productCoordinates (euclideanCoordinates (d + 1) z)).2)]
  nlinarith [norm_nonneg (z - (euclideanCoordinates (d + 1)).symm
    (productCoordinates.symm (x₀, 0)))]

/-- The full lifted ball lies in the spatial Euclidean ball times the
closed transverse interval of the same radius. -/
theorem euclidean_ball_subset_cylinder (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    Metric.ball ((euclideanCoordinates (d + 1)).symm
      (productCoordinates.symm (x₀, 0))) R ⊆
      euclideanCoordinates (d + 1) ⁻¹' (productCoordinates ⁻¹'
        ({x : Vec d | euclideanNorm (x - x₀) < R} ×ˢ Set.Icc (-R) R)) := by
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hs := norm_euclidean_lift_sub_center_sq z x₀
  have hn : 0 ≤ euclideanNorm
      ((productCoordinates (euclideanCoordinates (d + 1) z)).1 - x₀) := Real.sqrt_nonneg _
  have hnz := norm_nonneg (z - (euclideanCoordinates (d + 1)).symm
    (productCoordinates.symm (x₀, 0)))
  change euclideanNorm ((productCoordinates (euclideanCoordinates (d + 1) z)).1 - x₀) < R ∧
    -R ≤ (productCoordinates (euclideanCoordinates (d + 1) z)).2 ∧
      (productCoordinates (euclideanCoordinates (d + 1) z)).2 ≤ R
  constructor
  · nlinarith [sq_nonneg ((productCoordinates (euclideanCoordinates (d + 1) z)).2)]
  · constructor <;> nlinarith [sq_nonneg ((productCoordinates
      (euclideanCoordinates (d + 1) z)).2)]

/-- A positive-exponent scaled oscillation estimate supplies the continuity
needed for averaging; no separate continuity input from regularity is required. -/
theorem continuousOn_of_scaled_holder_oscillation
    {E : Type*} [NormedAddCommGroup E] {S : Set E} {v : E → ℝ}
    {K a β : ℝ} (hβ : 0 < β)
    (hosc : ∀ x ∈ S, ∀ y ∈ S, |v x - v y| ≤ K * (a * ‖x - y‖) ^ β) :
    ContinuousOn v S := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : Continuous (fun y : E => K * (a * ‖y - x‖) ^ β) :=
    continuous_const.mul ((Real.continuous_rpow_const hβ.le).comp
      (continuous_const.mul (continuous_id.sub continuous_const).norm))
  have ht : Filter.Tendsto (fun y : E => K * (a * ‖y - x‖) ^ β) (𝓝[S] x) (𝓝 0) := by
    have ht' : Filter.Tendsto (fun y : E => K * (a * ‖y - x‖) ^ β) (𝓝[S] x)
        (𝓝 (K * (a * ‖x - x‖) ^ β)) :=
      hb.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [sub_self, norm_zero, mul_zero, Real.zero_rpow hβ.ne'] using ht'
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) ?_ ht
  filter_upwards [self_mem_nhdsWithin] with y hy
  simpa only [Real.dist_eq] using hosc y hy x hx

/-- This consumes precisely the shape of a lifted ball regularity output:
a.e. equality on the full ball and positive-exponent oscillation on its half.
Continuity and the genuine compact transverse averaging are then proved. -/
theorem exists_continuousOn_ae_eq_holder_of_euclidean_ball_lift
    (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ} {u : Vec d → ℝ} (c : ℝ)
    (heq : v =ᵐ[volume.restrict (Metric.ball
      ((euclideanCoordinates (d + 1)).symm (productCoordinates.symm (x₀, 0))) R)]
      fun z => liftedValue u c (euclideanCoordinates (d + 1) z))
    {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β)
    (hosc : ∀ z ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (R / 2),
      ∀ z' ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (R / 2),
        |v z - v z'| ≤ K * (R⁻¹ * ‖z - z'‖) ^ β) :
    ∃ w : Vec d → ℝ,
      ContinuousOn w {x | euclideanNorm (x - x₀) < R / 4} ∧
      w =ᵐ[volume.restrict {x | euclideanNorm (x - x₀) < R / 4}] u ∧
      ∀ x ∈ {x | euclideanNorm (x - x₀) < R / 4},
        ∀ y ∈ {x | euclideanNorm (x - x₀) < R / 4},
          |w x - w y| ≤ Real.exp (|c| * (R / 4)) * K *
            (R⁻¹ * euclideanNorm (x - y)) ^ β := by
  have hU : MeasurableSet {x : Vec d | euclideanNorm (x - x₀) < R / 4} := by
    have hc : Continuous (fun x : Vec d => euclideanNorm (x - x₀)) := by
      simp only [TimeChange.euclideanNorm_eq_norm_toLp]
      fun_prop
    exact (isOpen_lt hc continuous_const).measurableSet
  have hsub := euclidean_cylinder_subset_half_ball x₀ hR
  have hsub' := hsub.trans (Metric.ball_subset_ball (by linarith : R / 2 ≤ R))
  have hvc := (continuousOn_of_scaled_holder_oscillation hβ hosc).mono hsub
  obtain ⟨w, hw, hae, hb⟩ := exists_continuousOn_ae_eq_holder_of_euclidean_lift hU
    (by linarith : 0 < R / 4) hvc c
    (ae_restrict_of_ae_restrict_of_subset hsub' heq)
    (mul_nonneg hK (Real.rpow_nonneg (inv_nonneg.mpr hR.le) β))
    (fun z hz z' hz' => by
      simpa only [Real.mul_rpow (inv_nonneg.mpr hR.le) (norm_nonneg _), mul_assoc]
        using hosc z (hsub hz) z' (hsub hz'))
  refine ⟨w, hw, hae, fun x hx y hy => ?_⟩
  simpa only [Real.mul_rpow (inv_nonneg.mpr hR.le)
    (show 0 ≤ euclideanNorm (x - y) from Real.sqrt_nonneg _), mul_assoc]
    using hb x hx y hy


/-- Spatial balls retain the explicit Euclidean norm on the native carrier. -/
theorem isOpen_spatial_euclidean_ball (x₀ : Vec d) (R : ℝ) :
    IsOpen {x : Vec d | euclideanNorm (x - x₀) < R} := by
  have hc : Continuous (fun x : Vec d => euclideanNorm (x - x₀)) := by
    simp only [TimeChange.euclideanNorm_eq_norm_toLp]
    fun_prop
  exact isOpen_lt hc continuous_const

/-- Native spatial Euclidean balls have finite actual Lebesgue volume,
by the measure-preserving Euclidean coordinate equivalence. -/
theorem volume_spatial_euclidean_ball_ne_top (x₀ : Vec d) (R : ℝ) :
    volume {x : Vec d | euclideanNorm (x - x₀) < R} ≠ ∞ := by
  have hpre : euclideanCoordinates d ⁻¹' {x : Vec d | euclideanNorm (x - x₀) < R} =
      Metric.ball ((euclideanCoordinates d).symm x₀) R := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
    rw [← (euclideanCoordinates d).symm_apply_apply z, norm_euclideanCoordinates_symm_sub]
    simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [← (euclideanCoordinates_measurePreserving d).measure_preimage
    (isOpen_spatial_euclidean_ball x₀ R).measurableSet.nullMeasurableSet, hpre]
  exact measure_ball_lt_top.ne

/-- The full-ball L² amplitude in interior regularity is controlled by the
spatial L² amplitude. Integrability is obtained from the actual lift, using
only the spatial finite-volume L² datum. -/
theorem sqrt_normalized_integral_euclidean_ball_lift_sq_le
    (x₀ : Vec d) {R c : ℝ} (hR : 0 < R) (hc : 0 ≤ c) (hcR : c * R ≤ 1)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R})) :
    Real.sqrt ((R ^ (d + 1))⁻¹ * ∫ z in Metric.ball
      ((euclideanCoordinates (d + 1)).symm (productCoordinates.symm (x₀, 0))) R,
      (liftedValue u c (euclideanCoordinates (d + 1) z)) ^ 2) ≤
      Real.sqrt (2 * Real.exp 2) *
        Real.sqrt ((R ^ d)⁻¹ * ∫ x in {x : Vec d | euclideanNorm (x - x₀) < R}, u x ^ 2) := by
  have hU := (isOpen_spatial_euclidean_ball x₀ R).measurableSet
  have hUfinite := volume_spatial_euclidean_ball_ne_top x₀ R
  let Ω : Set (Vec (d + 1)) := productCoordinates ⁻¹'
    ({x : Vec d | euclideanNorm (x - x₀) < R} ×ˢ Set.Icc (-R) R)
  have hΩ : MeasurableSet Ω :=
    (hU.prod measurableSet_Icc).preimage (productCoordinates (d := d)).continuous.measurable
  have hm : MemLp (liftedValue u c) 2 (volume.restrict Ω) :=
    memLp_lift_on_coordinate_cylinder hU hUfinite hu c isCompact_Icc
  have hi : IntegrableOn (fun z => (liftedValue u c (euclideanCoordinates (d + 1) z)) ^ 2)
      (euclideanCoordinates (d + 1) ⁻¹' Ω) volume :=
    (hm.comp_measurePreserving (euclideanCoordinates_measurePreserving_restrict hΩ)).integrable_sq
  have hle : (∫ z in Metric.ball ((euclideanCoordinates (d + 1)).symm
      (productCoordinates.symm (x₀, 0))) R,
      (liftedValue u c (euclideanCoordinates (d + 1) z)) ^ 2) ≤
      ∫ z in Ω, (liftedValue u c z) ^ 2 := by
    rw [← integral_euclideanCoordinates hΩ]
    exact setIntegral_mono_set hi (Filter.Eventually.of_forall fun z => sq_nonneg _)
      (Filter.Eventually.of_forall (euclidean_ball_subset_cylinder x₀ hR))
  exact (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle
    (inv_nonneg.mpr (pow_nonneg hR.le _)))).trans
    (sqrt_normalized_integral_liftedValue_sq_le hU u hc hR hcR)


/-- At the eigenfunction scale, a supplied lifted interior regularity output
descends to a spatial estimate with a uniform exponential cost and the spatial
L² normalization. The existence of that regularity output is not asserted. -/
theorem exists_eigenfunction_continuousOn_ae_eq_holder_of_euclidean_ball_lift
    (x₀ : Vec d) {δ : ℝ} (hδ : 0 < δ) (eigenvalue : ℝ)
    {u : Vec d → ℝ} {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hu : MemLp u 2 (volume.restrict
      {x : Vec d | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue}))
    (heq : v =ᵐ[volume.restrict (Metric.ball ((euclideanCoordinates (d + 1)).symm
      (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue))]
      fun z => liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) z))
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 < β)
    (hosc : ∀ z ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue / 2),
      ∀ z' ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue / 2),
      |v z - v z'| ≤ C * Real.sqrt (((eigenfunctionLiftRadius δ eigenvalue) ^ (d + 1))⁻¹ *
        ∫ q in Metric.ball ((euclideanCoordinates (d + 1)).symm
          (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue),
          (liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) q)) ^ 2) *
        ((eigenfunctionLiftRadius δ eigenvalue)⁻¹ * ‖z - z'‖) ^ β) :
    ∃ w : Vec d → ℝ,
      ContinuousOn w {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4} ∧
      w =ᵐ[volume.restrict
        {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4}] u ∧
      ∀ x ∈ {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4},
        ∀ y ∈ {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4},
        |w x - w y| ≤ Real.exp 1 * C * Real.sqrt (2 * Real.exp 2) *
          Real.sqrt (((eigenfunctionLiftRadius δ eigenvalue) ^ d)⁻¹ *
            ∫ q in {q : Vec d | euclideanNorm (q - x₀) < eigenfunctionLiftRadius δ eigenvalue},
              u q ^ 2) *
          ((eigenfunctionLiftRadius δ eigenvalue)⁻¹ * euclideanNorm (x - y)) ^ β := by
  have hR := eigenfunctionLiftRadius_pos (eigenvalue := eigenvalue) hδ
  obtain ⟨w, hw, hae, hb⟩ := exists_continuousOn_ae_eq_holder_of_euclidean_ball_lift
    x₀ hR (Real.sqrt eigenvalue) heq (mul_nonneg hC (Real.sqrt_nonneg _)) hβ hosc
  refine ⟨w, hw, hae, fun x hx y hy => ?_⟩
  have he : Real.exp (|Real.sqrt eigenvalue| * (eigenfunctionLiftRadius δ eigenvalue / 4)) ≤
      Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hr := sqrt_mul_eigenfunctionLiftRadius_le_one δ eigenvalue
    nlinarith [mul_nonneg (Real.sqrt_nonneg eigenvalue) hR.le]
  have hL := sqrt_normalized_integral_euclidean_ball_lift_sq_le x₀ hR
    (Real.sqrt_nonneg eigenvalue) (sqrt_mul_eigenfunctionLiftRadius_le_one δ eigenvalue) hu
  apply (hb x hx y hy).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg
    (mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)) β)
  calc
    _ ≤ Real.exp 1 * (C * _) :=
      mul_le_mul_of_nonneg_right he (mul_nonneg hC (Real.sqrt_nonneg _))
    _ ≤ Real.exp 1 * (C * (Real.sqrt (2 * Real.exp 2) * _)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL hC) (Real.exp_pos _).le
    _ = _ := by ring


/-- Continuous representatives on a countable open cover glue to one
representative, preserving each local representative pointwise. Countability
is used only to combine the genuine spatial a.e. equalities. -/
theorem exists_continuousOn_ae_eq_of_countable_open_cover
    {ι : Type*} [Countable ι] (U : ι → Set (Vec d)) (hU : ∀ i, IsOpen (U i))
    {u : Vec d → ℝ} (v : ι → Vec d → ℝ)
    (hv : ∀ i, ContinuousOn (v i) (U i))
    (hae : ∀ i, v i =ᵐ[volume.restrict (U i)] u) :
    ∃ w : Vec d → ℝ, ContinuousOn w (⋃ i, U i) ∧
      w =ᵐ[volume.restrict (⋃ i, U i)] u ∧ ∀ i, Set.EqOn w (v i) (U i) := by
  classical
  let w : Vec d → ℝ := fun x =>
    if hx : ∃ i, x ∈ U i then v hx.choose x else u x
  have heq (i : ι) : Set.EqOn w (v i) (U i) := by
    intro x hx
    have hex : ∃ j, x ∈ U j := ⟨i, hx⟩
    dsimp only [w]
    rw [dif_pos hex]
    exact continuous_representatives_eqOn_inter (hU hex.choose) (hU i)
      (hv hex.choose) (hv i) (hae hex.choose) (hae i) ⟨hex.choose_spec, hx⟩
  refine ⟨w, ContinuousOn.iUnion_of_isOpen (fun i => (hv i).congr (heq i)) hU, ?_, heq⟩
  apply (ae_eq_restrict_iUnion_iff U w u).mpr
  intro i
  exact ((heq i).aeEq_restrict (hU i).measurableSet).trans (hae i)

/-- The distributional gradient of an L² Sobolev datum is independent of
its chosen witness on an open domain. -/
theorem weakGradient_ae_eq_of_memLp {n : ℕ} {Ω : Set (Vec n)} (hΩ : IsOpen Ω)
    {u : Vec n → ℝ} {g h : Vec n → Vec n}
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict Ω))
    (hh : ∀ i, MemLp (fun x => h x i) 2 (volume.restrict Ω))
    (hwg : Homogenization.HasWeakGradientOn Ω u g)
    (hwh : Homogenization.HasWeakGradientOn Ω u h) :
    g =ᵐ[volume.restrict Ω] h := by
  have hi (i : Fin n) : (fun x => g x i) =ᵐ[volume.restrict Ω] fun x => h x i :=
    Homogenization.HasWeakPartialDerivOn.ae_eq hΩ
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hg i).locallyIntegrable (by norm_num)))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((hh i).locallyIntegrable (by norm_num)))
      (hwg i) (hwh i)
  filter_upwards [ae_all_iff.mpr hi] with x hx
  exact funext hx

/-- Equal concrete H¹ values have almost-everywhere equal gradients,
including when the two bundles were constructed by different approximations. -/
theorem h1Function_grad_ae_eq_of_toFun_eq {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (u v : Homogenization.H1Function Ω)
    (heq : u.toFun = v.toFun) : u.grad =ᵐ[volume.restrict Ω] v.grad := by
  apply weakGradient_ae_eq_of_memLp hΩ u.gradMemL2 v.gradMemL2
  · exact u.hasWeakGradient
  · rw [heq]
    exact v.hasWeakGradient

/-- A divergence-free L² flux annihilates every H¹ gradient whose value
has zero trace, regardless of the witness chosen by the zero-trace proof. -/
theorem integral_flux_dot_H1_eq_zero_of_memH10 {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) {F : Vec n → Vec n}
    (hF : ∀ i, MemLp (fun x => F x i) 2 (volume.restrict Ω))
    (hweak : ∀ ψ : Vec n → ℝ, IsSpatialTest Ω ψ →
      (∫ x in Ω, dot (F x) (gradient ψ x)) = 0)
    (v : Homogenization.H1Function Ω) (hv : Homogenization.MemH10 Ω v.toFun) :
    (∫ x in Ω, dot (F x) (v.grad x)) = 0 := by
  obtain ⟨v₀, hv₀⟩ := hv
  have heq := h1Function_grad_ae_eq_of_toFun_eq hΩ v v₀.toH1Function hv₀.symm
  calc
    _ = ∫ x in Ω, dot (F x) (v₀.toH1Function.grad x) := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ = 0 := integral_flux_dot_H10_eq_zero hF hweak v₀

/-- The homogeneous variational identity of a selected H¹ solution holds
for every solution-gradient witness and every zero-trace test-gradient witness. -/
theorem integral_matrix_mul_H1_dot_H1_eq_zero {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) (A : Vec n → Mat n) (u₀ : Homogenization.H1Function Ω)
    (hF : ∀ i, MemLp (fun x => ((A x).mulVec (u₀.grad x)) i) 2 (volume.restrict Ω))
    (hweak : ∀ ψ : Vec n → ℝ, IsSpatialTest Ω ψ →
      (∫ x in Ω, dot ((A x).mulVec (u₀.grad x)) (gradient ψ x)) = 0)
    (u v : Homogenization.H1Function Ω) (hu : u.toFun = u₀.toFun)
    (hv : Homogenization.MemH10 Ω v.toFun) :
    (∫ x in Ω, dot ((A x).mulVec (u.grad x)) (v.grad x)) = 0 := by
  have heq := h1Function_grad_ae_eq_of_toFun_eq hΩ u u₀ hu
  calc
    _ = ∫ x in Ω, dot ((A x).mulVec (u₀.grad x)) (v.grad x) := by
      apply integral_congr_ae
      filter_upwards [heq] with x hx
      rw [hx]
    _ = 0 := integral_flux_dot_H1_eq_zero_of_memH10 hΩ hF hweak v hv

/-- The actual lifted eigenfunction equation is independent of both
Sobolev-gradient choices on every open subregion of its finite cylinder. -/
theorem integral_lifted_matrix_H1_dot_H1_eq_zero {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K))
    (w v : Homogenization.H1Function Ω)
    (hwvalue : w.toFun = liftedValue u (Real.sqrt eigenvalue))
    (hv : Homogenization.MemH10 Ω v.toFun) :
    (∫ z in Ω, dot ((liftedMatrix (ρ (productCoordinates z).1)
      (α (productCoordinates z).1)).mulVec (w.grad z)) (v.grad z)) = 0 := by
  let u₀ := (coordinateLiftH1 hU hUfinite hu hg hw (Real.sqrt eigenvalue) hK).restrict hΩ hsub
  have hC : MeasurableSet (productCoordinates ⁻¹' (U ×ˢ K)) :=
    (hU.prod hK.measurableSet).preimage
      (productCoordinates (d := d)).continuous.measurable
  apply integral_matrix_mul_H1_dot_H1_eq_zero hΩ
    (fun z => liftedMatrix (ρ (productCoordinates z).1) (α (productCoordinates z).1)) u₀
  · intro i
    exact (liftedFlux_memLp hκ h hU hUfinite hu hg (Real.sqrt eigenvalue) hK i).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  · intro ψ hψ
    change (∫ z in Ω, dot (liftedFlux ρ α u g (Real.sqrt eigenvalue) z) (gradient ψ z)) = 0
    rw [← setIntegral_flux_dot_test_eq hC hsub _ hψ]
    exact integral_coordinate_lift_eigenfunction_eq_zero hκ h hU hUfinite hu hg
      eigenvalue heigenvalue hweak ⟨hψ.1, hψ.2.1, hψ.2.2.trans hsub⟩
  · exact hwvalue
  · exact hv

/-- The coordinate map preserves the actual Euclidean inner product as the
explicit coordinate dot product, without changing the native product norm. -/
theorem inner_euclideanCoordinates_symm_eq_dot {n : ℕ} (x y : Vec n) :
    inner ℝ ((euclideanCoordinates n).symm x) ((euclideanCoordinates n).symm y) =
      dot x y := by
  simp [PiLp.inner_apply, euclideanCoordinates, dot, mul_comm]

/-- A Euclidean vector may remain on the second side of the coordinate
inner-product identity. -/
theorem inner_euclideanCoordinates_symm_left {n : ℕ} (x : Vec n)
    (y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ ((euclideanCoordinates n).symm x) y =
      dot x (euclideanCoordinates n y) := by
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    inner_euclideanCoordinates_symm_eq_dot x (euclideanCoordinates n y)

/-- A genuine Euclidean zero-trace approximation supplies native zero-trace
membership for its value, independently of any later gradient witness. -/
theorem memH10_of_euclidean_approximation {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hv : MemLp v 2 (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hH : ∀ i, MemLp (fun z => H z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hw : ∀ i : Fin n, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, H z i * ψ z)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k))
    (hφc : ∀ k, HasCompactSupport (φ k))
    (hφΩ : ∀ k, tsupport (φ k) ⊆ euclideanCoordinates n ⁻¹' Ω)
    (hvlim : Tendsto (fun k => eLpNorm (fun z => φ k z - v z) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0))
    (hHlim : ∀ i, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - H z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0)) :
    Homogenization.MemH10 Ω (fun x => v ((euclideanCoordinates n).symm x)) :=
  ⟨nativeH10OfEuclidean hΩ hv hH hw φ hφ hφc hφΩ hvlim hHlim, rfl⟩

/-- The actual exponential lift has Euclidean L² value and gradient
components and satisfies every Euclidean distributional coordinate identity. -/
theorem euclidean_liftedValue_memH1 {U : Set (Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (c : ℝ)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K)) :
    MemLp (fun z => liftedValue u c (euclideanCoordinates (d + 1) z)) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)) ∧
    (∀ i, MemLp (fun z => liftedGradient u g c (euclideanCoordinates (d + 1) z) i) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω))) ∧
    (∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
      (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
        liftedValue u c (euclideanCoordinates (d + 1) z) *
          fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
          liftedGradient u g c (euclideanCoordinates (d + 1) z) i * ψ z) := by
  let w := (coordinateLiftH1 hU hUfinite hu hg hw c hK).restrict hΩ hsub
  exact ⟨memLp_euclideanCoordinates hΩ.measurableSet w.memL2,
    fun i => memLp_euclideanCoordinates hΩ.measurableSet (w.gradMemL2 i),
    euclidean_weak_gradient_of_native hΩ.measurableSet w.hasWeakGradient⟩

/-- The lifted eigenfunction annihilates every Euclidean zero-trace test,
with arbitrary solution and test weak-gradient witnesses.  The zero-trace
membership can come from a different approximation witness via
`memH10_of_euclidean_approximation`. -/
theorem integral_lifted_matrix_euclideanH1_inner_euclideanH1_eq_zero
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K))
    {G H : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hwG : ∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
      (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
        liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) z) *
          fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω, G z i * ψ z)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : MemLp v 2 (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hH : ∀ i, MemLp (fun z => H z i) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hwH : ∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
      (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
        v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω, H z i * ψ z)
    (htrace : Homogenization.MemH10 Ω
      (fun x => v ((euclideanCoordinates (d + 1)).symm x))) :
    (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
      inner ℝ ((euclideanCoordinates (d + 1)).symm
        ((liftedMatrix (ρ (productCoordinates (euclideanCoordinates (d + 1) z)).1)
          (α (productCoordinates (euclideanCoordinates (d + 1) z)).1)).mulVec
            (euclideanCoordinates (d + 1) (G z)))) (H z)) = 0 := by
  have huE := (euclidean_liftedValue_memH1 hU hUfinite hu hg hw
    (Real.sqrt eigenvalue) hK hΩ hsub).1
  let w := nativeH1OfEuclidean hΩ.measurableSet huE hG hwG
  let v₀ := nativeH1OfEuclidean hΩ.measurableSet hv hH hwH
  have hwvalue : w.toFun = liftedValue u (Real.sqrt eigenvalue) := by
    funext x
    exact congrArg (liftedValue u (Real.sqrt eigenvalue))
      ((euclideanCoordinates (d + 1)).apply_symm_apply x)
  have ht := integral_lifted_matrix_H1_dot_H1_eq_zero hκ h hU hUfinite hu hg hw
    eigenvalue heigenvalue hweak hK hΩ hsub w v₀ hwvalue htrace
  change (∫ x in Ω, dot ((liftedMatrix (ρ (productCoordinates x).1)
    (α (productCoordinates x).1)).mulVec
      (fun i => G ((euclideanCoordinates (d + 1)).symm x) i))
        (fun i => H ((euclideanCoordinates (d + 1)).symm x) i)) = 0 at ht
  rw [← integral_euclideanCoordinates hΩ.measurableSet (fun x =>
    dot ((liftedMatrix (ρ (productCoordinates x).1) (α (productCoordinates x).1)).mulVec
      (fun i => G ((euclideanCoordinates (d + 1)).symm x) i))
        (fun i => H ((euclideanCoordinates (d + 1)).symm x) i))] at ht
  simp only [ContinuousLinearEquiv.symm_apply_apply] at ht
  simp only [inner_euclideanCoordinates_symm_left]
  simpa only [euclideanCoordinates, PiLp.coe_continuousLinearEquiv] using ht


/-- The actual block coefficient field in Euclidean coordinates. -/
def euclideanLiftedMatrix (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (z : EuclideanSpace ℝ (Fin (d + 1))) : Mat (d + 1) :=
  liftedMatrix (ρ (productCoordinates (euclideanCoordinates (d + 1) z)).1)
    (α (productCoordinates (euclideanCoordinates (d + 1) z)).1)

/-- Every Euclidean entry of the actual lifted coefficient is measurable. -/
theorem euclideanLiftedMatrix_measurable {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (i j : Fin (d + 1)) :
    Measurable (fun z => euclideanLiftedMatrix ρ α z i j) :=
  (liftedMatrix_measurable h i j).comp
    (euclideanCoordinates (d + 1)).continuous.measurable

/-- Euclidean transport preserves symmetry of the literal coefficient matrix. -/
theorem euclideanLiftedMatrix_transpose {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (z : EuclideanSpace ℝ (Fin (d + 1))) :
    (euclideanLiftedMatrix ρ α z).transpose = euclideanLiftedMatrix ρ α z :=
  liftedMatrix_transpose _ (h.2.2 _).2.2.1

/-- The explicit coordinate energy is exactly the square of the Euclidean
Hilbert norm; no identity with the native product norm is used. -/
theorem euclideanSq_euclideanCoordinates {n : ℕ}
    (ξ : EuclideanSpace ℝ (Fin n)) :
    euclideanSq (euclideanCoordinates n ξ) = ‖ξ‖ ^ 2 := by
  simpa only [euclideanCoordinates, PiLp.coe_continuousLinearEquiv,
    WithLp.toLp_ofLp] using
    euclideanSq_eq_norm_sq_toLp (euclideanCoordinates n ξ)

/-- Both source quadratic bounds hold for the actual coefficient acting on
Euclidean Hilbert vectors. -/
theorem euclideanLiftedMatrix_quadratic {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (z ξ : EuclideanSpace ℝ (Fin (d + 1))) :
    κ * ‖ξ‖ ^ 2 ≤ inner ℝ ξ ((euclideanCoordinates (d + 1)).symm
      ((euclideanLiftedMatrix ρ α z).mulVec (euclideanCoordinates (d + 1) ξ))) ∧
    inner ℝ ξ ((euclideanCoordinates (d + 1)).symm
      ((euclideanLiftedMatrix ρ α z).mulVec (euclideanCoordinates (d + 1) ξ))) ≤
        κ⁻¹ * ‖ξ‖ ^ 2 := by
  have ht := liftedMatrix_quadratic h
    (productCoordinates (euclideanCoordinates (d + 1) z)).1
    (euclideanCoordinates (d + 1) ξ)
  rw [euclideanSq_euclideanCoordinates] at ht
  simpa only [euclideanLiftedMatrix,
    ← inner_euclideanCoordinates_symm_eq_dot,
    ContinuousLinearEquiv.symm_apply_apply] using ht

/-- Inverse coercivity also holds in the actual Euclidean Hilbert norm. -/
theorem euclideanLiftedMatrix_inverse_coercive {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (z ξ : EuclideanSpace ℝ (Fin (d + 1))) :
    κ ^ 3 * ‖ξ‖ ^ 2 ≤ inner ℝ ξ ((euclideanCoordinates (d + 1)).symm
      ((euclideanLiftedMatrix ρ α z)⁻¹.mulVec (euclideanCoordinates (d + 1) ξ))) := by
  have ht := liftedMatrix_inverse_quadratic hκ h
    (productCoordinates (euclideanCoordinates (d + 1) z)).1
    (euclideanCoordinates (d + 1) ξ)
  rw [euclideanSq_euclideanCoordinates] at ht
  simpa only [euclideanLiftedMatrix,
    ← inner_euclideanCoordinates_symm_eq_dot,
    ContinuousLinearEquiv.symm_apply_apply] using ht

/-- The source coefficient bounds force the ellipticity parameter below one,
and hence give the comparison required for lower scale `κ` and upper
scale `(κ ^ 3)⁻¹`. -/
theorem lifted_ellipticity_scale_comparison {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α) :
    κ ≤ 1 ∧ κ ≤ (κ ^ 3)⁻¹ := by
  have hb : κ ≤ κ⁻¹ := (h.2.2 0).1.trans (h.2.2 0).2.1
  have hb' := mul_le_mul_of_nonneg_right hb hκ.le
  rw [inv_mul_cancel₀ hκ.ne'] at hb'
  have hk1 : κ ≤ 1 := by nlinarith
  have hk3 : κ ^ 3 ≤ 1 := pow_le_one₀ hκ.le hk1
  exact ⟨hk1, hk1.trans ((one_le_inv₀ (pow_pos hκ 3)).2 hk3)⟩

/-- The ellipticity ratio for the preceding Hilbert-space coercivity
constants is exactly the fourth inverse power of the source scale. -/
theorem lifted_ellipticity_ratio {κ : ℝ} (hκ : 0 < κ) :
    (κ ^ 3)⁻¹ / κ = (κ ^ 4)⁻¹ := by
  field_simp [hκ.ne']


/-- Spatial L² membership gives L² membership of the actual exponential
lift on its Euclidean ball, for every signed transverse exponent. -/
theorem memLp_euclidean_ball_lift (x₀ : Vec d) {R : ℝ} (hR : 0 < R)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R}))
    (c : ℝ) :
    MemLp (fun z => liftedValue u c (euclideanCoordinates (d + 1) z)) 2
      (volume.restrict (Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) R)) := by
  have hU := (isOpen_spatial_euclidean_ball x₀ R).measurableSet
  let Ω : Set (Vec (d + 1)) := productCoordinates ⁻¹'
    ({x : Vec d | euclideanNorm (x - x₀) < R} ×ˢ Set.Icc (-R) R)
  have hΩ : MeasurableSet Ω :=
    (hU.prod measurableSet_Icc).preimage (productCoordinates (d := d)).continuous.measurable
  have hm : MemLp (liftedValue u c) 2 (volume.restrict Ω) :=
    memLp_lift_on_coordinate_cylinder hU (volume_spatial_euclidean_ball_ne_top x₀ R)
      hu c isCompact_Icc
  exact (hm.comp_measurePreserving (euclideanCoordinates_measurePreserving_restrict hΩ)).mono_measure
    (Measure.restrict_mono (euclidean_ball_subset_cylinder x₀ hR) le_rfl)

/-- This is the `p₀ = 2` integrability input in the genuine Moser theorem,
obtained from the actual spatial L² datum. -/
theorem integrableOn_euclidean_ball_lift_abs_rpow_two (x₀ : Vec d)
    {R : ℝ} (hR : 0 < R) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R}))
    (c : ℝ) :
    IntegrableOn (fun z => |liftedValue u c (euclideanCoordinates (d + 1) z)| ^ (2 : ℝ))
      (Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) R) volume := by
  simpa only [IntegrableOn, Real.rpow_two, sq_abs] using
    (memLp_euclidean_ball_lift x₀ hR hu c).integrable_sq

/-- At `p₀ = 2`, the Moser volume normalization is exactly the square-root
L² amplitude with the true Euclidean dimension. -/
theorem normalized_euclidean_ball_abs_rpow_two {n : ℕ}
    (z₀ : EuclideanSpace ℝ (Fin n)) (R : ℝ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ((R ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))⁻¹ *
      ∫ z in Metric.ball z₀ R, |f z| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) =
      Real.sqrt ((R ^ n)⁻¹ * ∫ z in Metric.ball z₀ R, (f z) ^ 2) := by
  simp only [finrank_euclideanSpace_fin, Real.rpow_two, sq_abs, Real.sqrt_eq_rpow]

/-- A supplied Moser output at `p₀ = 2` descends by genuine transverse
averaging. The parameters `M`, `σ`, and `θ` stand for the theorem's dimension
constant, Sobolev dimension, and ellipticity ratio. Its exponent lower bound
is retained. This lemma does not assert existence of the Moser output. -/
theorem exists_eigenfunction_continuousOn_ae_eq_holder_of_moser_p_two
    (x₀ : Vec d) {δ : ℝ} (hδ : 0 < δ) (eigenvalue M σ θ : ℝ) (hM : 0 ≤ M) (hθ : 0 ≤ θ)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict
      {x : Vec d | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue}))
    (hregularity : ∃ v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      (v =ᵐ[volume.restrict (Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue))]
        fun z => liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) z)) ∧
      ∃ β > 0, Real.exp (-(M * θ ^ ((1 : ℝ) / 2))) ≤ β ∧
        ∀ z ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
            (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue / 2),
          ∀ z' ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
            (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue / 2),
          |v z - v z'| ≤ M * θ ^ (σ / (2 * (2 : ℝ))) *
            ((2 : ℝ) / (2 - 1)) ^ (σ / 2) *
            (((eigenfunctionLiftRadius δ eigenvalue) ^
                Module.finrank ℝ (EuclideanSpace ℝ (Fin (d + 1))))⁻¹ *
              ∫ q in Metric.ball ((euclideanCoordinates (d + 1)).symm
                (productCoordinates.symm (x₀, 0))) (eigenfunctionLiftRadius δ eigenvalue),
                |liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) q)| ^
                  (2 : ℝ)) ^ ((1 : ℝ) / 2) *
            ((eigenfunctionLiftRadius δ eigenvalue)⁻¹ * ‖z - z'‖) ^ β) :
    ∃ β > 0, Real.exp (-(M * θ ^ ((1 : ℝ) / 2))) ≤ β ∧
      ∃ w : Vec d → ℝ,
        ContinuousOn w {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4} ∧
        w =ᵐ[volume.restrict
          {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4}] u ∧
        ∀ x ∈ {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4},
          ∀ y ∈ {x | euclideanNorm (x - x₀) < eigenfunctionLiftRadius δ eigenvalue / 4},
          |w x - w y| ≤ Real.exp 1 * (M * θ ^ (σ / 4) * (2 : ℝ) ^ (σ / 2)) *
            Real.sqrt (2 * Real.exp 2) *
            Real.sqrt (((eigenfunctionLiftRadius δ eigenvalue) ^ d)⁻¹ *
              ∫ q in {q : Vec d | euclideanNorm (q - x₀) < eigenfunctionLiftRadius δ eigenvalue},
                u q ^ 2) *
            ((eigenfunctionLiftRadius δ eigenvalue)⁻¹ * euclideanNorm (x - y)) ^ β := by
  obtain ⟨v, heq, β, hβ, hlower, hosc⟩ := hregularity
  obtain ⟨w, hw, hae, hb⟩ :=
    exists_eigenfunction_continuousOn_ae_eq_holder_of_euclidean_ball_lift x₀ hδ eigenvalue
      hu heq (C := M * θ ^ (σ / 4) * (2 : ℝ) ^ (σ / 2)) (by positivity) hβ
      (fun z hz z' hz' => by
        simpa only [normalized_euclidean_ball_abs_rpow_two,
          show (2 : ℝ) * 2 = 4 by norm_num,
          show (2 : ℝ) / (2 - 1) = 2 by norm_num] using hosc z hz z' hz')
  exact ⟨β, hβ, hlower, w, hw, hae, hb⟩


/-- Local continuous representatives glue on every open cover. The spatial
carrier is second countable, so a countable subcover suffices for the a.e.
equality; continuity then gives agreement with all the original patches. -/
theorem exists_continuousOn_ae_eq_of_open_cover
    {ι : Type*} (U : ι → Set (Vec d)) (hU : ∀ i, IsOpen (U i))
    {u : Vec d → ℝ} (v : ι → Vec d → ℝ)
    (hv : ∀ i, ContinuousOn (v i) (U i))
    (hae : ∀ i, v i =ᵐ[volume.restrict (U i)] u) :
    ∃ w : Vec d → ℝ, ContinuousOn w (⋃ i, U i) ∧
      w =ᵐ[volume.restrict (⋃ i, U i)] u ∧ ∀ i, Set.EqOn w (v i) (U i) := by
  classical
  obtain ⟨s, hs, hcover⟩ := eq_open_union_countable U hU
  letI : Countable s := hs.to_subtype
  obtain ⟨w, hw, hwu, hagree⟩ := exists_continuousOn_ae_eq_of_countable_open_cover
    (fun i : s => U i) (fun i => hU i) (fun i => v i)
    (fun i => hv i) (fun i => hae i)
  have he : (⋃ i : s, U i) = ⋃ i, U i := by
    simpa only [Set.iUnion_subtype] using hcover
  rw [he] at hw hwu
  refine ⟨w, hw, hwu, fun i x hx => ?_⟩
  exact continuous_representatives_eqOn_inter (isOpen_iUnion hU) (hU i)
    hw (hv i) hwu (hae i) ⟨Set.mem_iUnion.mpr ⟨i, hx⟩, hx⟩

/-- A family of supplied lifted-ball regularity outputs gives one spatial
continuous representative on the union of the descended balls, preserving
every local exponent and oscillation constant. The cover may be uncountable;
all a.e. equalities are obtained by transverse averaging and a countable
subcover, never by evaluating a product-a.e. identity at a fixed height. -/
theorem exists_continuousOn_ae_eq_holder_of_euclidean_ball_lift_cover
    {ι : Type*} (x₀ : ι → Vec d) (R c K β : ι → ℝ)
    (hR : ∀ i, 0 < R i) (hK : ∀ i, 0 ≤ K i) (hβ : ∀ i, 0 < β i)
    {u : Vec d → ℝ} (v : ι → EuclideanSpace ℝ (Fin (d + 1)) → ℝ)
    (heq : ∀ i, v i =ᵐ[volume.restrict (Metric.ball
      ((euclideanCoordinates (d + 1)).symm (productCoordinates.symm (x₀ i, 0))) (R i))]
      fun z => liftedValue u (c i) (euclideanCoordinates (d + 1) z))
    (hosc : ∀ i, ∀ z ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀ i, 0))) (R i / 2),
      ∀ z' ∈ Metric.ball ((euclideanCoordinates (d + 1)).symm
        (productCoordinates.symm (x₀ i, 0))) (R i / 2),
        |v i z - v i z'| ≤ K i * ((R i)⁻¹ * ‖z - z'‖) ^ (β i)) :
    ∃ w : Vec d → ℝ,
      ContinuousOn w (⋃ i, {x | euclideanNorm (x - x₀ i) < R i / 4}) ∧
      w =ᵐ[volume.restrict (⋃ i, {x | euclideanNorm (x - x₀ i) < R i / 4})] u ∧
      ∀ i, ∀ x ∈ {x | euclideanNorm (x - x₀ i) < R i / 4},
        ∀ y ∈ {x | euclideanNorm (x - x₀ i) < R i / 4},
          |w x - w y| ≤ Real.exp (|c i| * (R i / 4)) * K i *
            ((R i)⁻¹ * euclideanNorm (x - y)) ^ (β i) := by
  classical
  have hlocal := fun i => exists_continuousOn_ae_eq_holder_of_euclidean_ball_lift
    (x₀ i) (hR i) (c i) (heq i) (hK i) (hβ i) (hosc i)
  choose w hw hwu hbound using hlocal
  obtain ⟨W, hW, hWu, hagree⟩ := exists_continuousOn_ae_eq_of_open_cover
    (fun i => {x | euclideanNorm (x - x₀ i) < R i / 4})
    (fun i => isOpen_spatial_euclidean_ball (x₀ i) (R i / 4)) w hw hwu
  refine ⟨W, hW, hWu, fun i x hx y hy => ?_⟩
  rw [hagree i hx, hagree i hy]
  exact hbound i x hx y hy

/-- Euclidean distributional gradients are unique on an open domain,
with componentwise L² hypotheses and the actual restricted volume. -/
theorem euclidean_weak_gradient_ae_eq_of_memLp {n : ℕ} {Ω : Set (Vec n)}
    (hΩ : IsOpen Ω) {v : EuclideanSpace ℝ (Fin n) → ℝ}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hH : ∀ i, MemLp (fun z => H z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω)))
    (hwG : ∀ i : Fin n, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, G z i * ψ z)
    (hwH : ∀ i : Fin n, ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates n ⁻¹' Ω →
      (∫ z in euclideanCoordinates n ⁻¹' Ω,
        v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates n ⁻¹' Ω, H z i * ψ z) :
    G =ᵐ[volume.restrict (euclideanCoordinates n ⁻¹' Ω)] H := by
  have hnative := weakGradient_ae_eq_of_memLp hΩ
    (fun i => (hG i).comp_measurePreserving
      (euclideanCoordinates_symm_measurePreserving_restrict hΩ.measurableSet))
    (fun i => (hH i).comp_measurePreserving
      (euclideanCoordinates_symm_measurePreserving_restrict hΩ.measurableSet))
    (hasWeakGradientOn_of_euclidean hΩ.measurableSet hwG)
    (hasWeakGradientOn_of_euclidean hΩ.measurableSet hwH)
  have heq := (euclideanCoordinates_measurePreserving_restrict hΩ.measurableSet).quasiMeasurePreserving.ae_eq_comp hnative
  filter_upwards [heq] with z hz
  have hz' : (fun i => G z i) = (fun i => H z i) := by
    simpa only [Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hz
  have hcoords : euclideanCoordinates n (G z) = euclideanCoordinates n (H z) := by
    simpa only [euclideanCoordinates, PiLp.coe_continuousLinearEquiv] using hz'
  exact (euclideanCoordinates n).injective hcoords

/-- Convergence of smooth gradients to one distributional witness gives
convergence to every such witness.  The approximating sequence is unchanged. -/
theorem tendsto_euclidean_approximation_gradient_of_ae_eq {n : ℕ}
    {Ω : Set (Vec n)}
    {G H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (heq : G =ᵐ[volume.restrict (euclideanCoordinates n ⁻¹' Ω)] H)
    (φ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hlim : ∀ i, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - G z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0)) :
    ∀ i, Tendsto (fun k => eLpNorm
      (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - H z i) 2
      (volume.restrict (euclideanCoordinates n ⁻¹' Ω))) atTop (nhds 0) := by
  intro i
  have hnorm (k : ℕ) :
      eLpNorm (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - H z i) 2
        (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) =
      eLpNorm (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - G z i) 2
        (volume.restrict (euclideanCoordinates n ⁻¹' Ω)) := by
    apply eLpNorm_congr_ae
    filter_upwards [heq] with z hz
    rw [hz]
  simpa only [hnorm] using hlim i

/-- The actual lifted eigenfunction annihilates every Euclidean zero-trace
test specified by smooth approximation.  The solution and test gradients are
arbitrary weak witnesses; the approximation may use a third, independently
chosen test gradient.  All three witnesses use the same restricted volume. -/
theorem integral_lifted_matrix_euclidean_eq_zero_of_zero_trace_approximation
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K))
    {G H : EuclideanSpace ℝ (Fin (d + 1)) → EuclideanSpace ℝ (Fin (d + 1))}
    (hG : ∀ i, MemLp (fun z => G z i) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hwG : ∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
      (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
        liftedValue u (Real.sqrt eigenvalue) (euclideanCoordinates (d + 1) z) *
          fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω, G z i * ψ z)
    {v : EuclideanSpace ℝ (Fin (d + 1)) → ℝ}
    (hv : MemLp v 2 (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hH : ∀ i, MemLp (fun z => H z i) 2
      (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω)))
    (hwH : ∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
      (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
        v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
        -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω, H z i * ψ z)
    (htrace : ∃ H₀ : EuclideanSpace ℝ (Fin (d + 1)) →
        EuclideanSpace ℝ (Fin (d + 1)),
      (∀ i, MemLp (fun z => H₀ z i) 2
        (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω))) ∧
      (∀ i : Fin (d + 1), ∀ ψ : EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω →
        (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
          v z * fderiv ℝ ψ z (EuclideanSpace.single i 1)) =
          -∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω, H₀ z i * ψ z) ∧
      ∃ φ : ℕ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ,
        (∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) ∧
        (∀ k, HasCompactSupport (φ k)) ∧
        (∀ k, tsupport (φ k) ⊆ euclideanCoordinates (d + 1) ⁻¹' Ω) ∧
        Tendsto (fun k => eLpNorm (fun z => φ k z - v z) 2
          (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω))) atTop (nhds 0) ∧
        ∀ i, Tendsto (fun k => eLpNorm
          (fun z => fderiv ℝ (φ k) z (EuclideanSpace.single i 1) - H₀ z i) 2
          (volume.restrict (euclideanCoordinates (d + 1) ⁻¹' Ω))) atTop (nhds 0)) :
    (∫ z in euclideanCoordinates (d + 1) ⁻¹' Ω,
      inner ℝ ((euclideanCoordinates (d + 1)).symm
        ((euclideanLiftedMatrix ρ α z).mulVec (euclideanCoordinates (d + 1) (G z))))
          (H z)) = 0 := by
  obtain ⟨H₀, hH₀, hwH₀, φ, hφ, hφc, hφΩ, hvlim, hH₀lim⟩ := htrace
  have heq := euclidean_weak_gradient_ae_eq_of_memLp hΩ hH₀ hH hwH₀ hwH
  have hHlim := tendsto_euclidean_approximation_gradient_of_ae_eq heq φ hH₀lim
  have hnative := memH10_of_euclidean_approximation hΩ.measurableSet
    hv hH hwH φ hφ hφc hφΩ hvlim hHlim
  exact integral_lifted_matrix_euclideanH1_inner_euclideanH1_eq_zero hκ h hU hUfinite
    hu hg hw eigenvalue heigenvalue hweak hK hΩ hsub hG hwG hv hH hwH hnative

/-- The native Sobolev representative embeds in the Harnack library without
changing either its value or its coordinate gradient. -/
def pdeH1OfNative {n : ℕ} {Ω : Set (Vec n)} (w : Homogenization.H1Function Ω) :
    PDE.H1Function Ω where
  toFun := w.toFun
  grad := w.grad
  memL2 := w.memL2
  gradMemL2 := w.gradMemL2
  hasWeakGradient := w.hasWeakGradient

/-- Scalar normalization multiplies the actual Euclidean flux pairing by
exactly the same scalar. -/
theorem pde_flux_pairing_smul {n : ℕ} (c : ℝ) (A : Mat n) (ξ η : Vec n) :
    PDE.vecDot (PDE.matVecMul (c • A) ξ) η =
      c * PDE.vecDot (PDE.matVecMul A ξ) η := by
  change dot ((c • A).mulVec ξ) η = c * dot (A.mulVec ξ) η
  rw [Matrix.smul_mulVec]
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Constant coefficient scaling preserves the homogeneous weak equation,
including all three test-integrability obligations. -/
theorem pde_homogeneous_solution_smul {n : ℕ} {Ω : Set (Vec n)}
    {A : PDE.CoeffField n} {w : PDE.H1Function Ω}
    (hsol : PDE.IsWeakDivergenceFormSolutionOn A Ω w (0 : Vec n → ℝ) 0)
    (c : ℝ) :
    PDE.IsWeakDivergenceFormSolutionOn (fun z => c • A z) Ω w
      (0 : Vec n → ℝ) 0 := by
  intro φ
  obtain ⟨ht, heq⟩ := hsol φ
  have hpair : (fun z => PDE.vecDot (PDE.matVecMul (c • A z) (w.grad z))
      (φ.grad z)) = fun z => c * PDE.vecDot (PDE.matVecMul (A z) (w.grad z))
        (φ.grad z) := funext fun z => pde_flux_pairing_smul c (A z) _ _
  refine ⟨⟨?_, ht.source_integrable, ht.forcing_integrable⟩, ?_⟩
  · rw [hpair]
    exact ht.flux_integrable.const_mul c
  · rw [hpair, integral_const_mul, heq]
    simp only [Pi.zero_apply, zero_mul, PDE.vecDot,
      Finset.sum_const_zero, integral_zero, sub_self, mul_zero]

/-- The literal lifted coefficient normalized by its positive source lower
ellipticity constant. -/
def normalizedCoordinateLiftedMatrix (κ : ℝ) (ρ : Vec d → ℝ)
    (α : Vec d → Mat d) (z : Vec (d + 1)) : Mat (d + 1) :=
  κ⁻¹ • liftedMatrix (ρ (productCoordinates z).1) (α (productCoordinates z).1)

/-- The Harnack library's inverse-coercivity convention holds with lower
constant one and upper constant exactly the fourth inverse power. -/
theorem normalizedCoordinateLiftedMatrix_elliptic {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (z : Vec (d + 1)) :
    PDE.IsEllipticMatrix 1 (κ ^ 4)⁻¹ (normalizedCoordinateLiftedMatrix κ ρ α z) := by
  have hA : PDE.IsEllipticMatrix κ (κ ^ 3)⁻¹
      (liftedMatrix (ρ (productCoordinates z).1) (α (productCoordinates z).1)) := by
    refine ⟨hκ, (lifted_ellipticity_scale_comparison hκ h).2, ?_, ?_⟩
    · intro ξ
      simpa only [PDE.vecNormSq, PDE.vecDot, PDE.matVecMul,
        Matrix.mulVec, dotProduct, dot, euclideanSq, pow_two] using
        (liftedMatrix_quadratic h (productCoordinates z).1 ξ).1
    · intro ξ
      simpa only [inv_inv, PDE.vecNormSq, PDE.vecDot, PDE.matVecMul,
        Matrix.mulVec, dotProduct, dot, euclideanSq, pow_two] using
        liftedMatrix_inverse_quadratic hκ h (productCoordinates z).1 ξ
  have hscale : κ⁻¹ * (κ ^ 3)⁻¹ = (κ ^ 4)⁻¹ := by
    field_simp [hκ.ne']
  simpa only [normalizedCoordinateLiftedMatrix, inv_mul_cancel₀ hκ.ne', hscale] using
    PDE.isEllipticMatrix_smul (inv_pos.mpr hκ) hA

/-- Coefficient normalization preserves entrywise measurability. -/
theorem normalizedCoordinateLiftedMatrix_measurable {κ : ℝ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (i j : Fin (d + 1)) :
    Measurable (fun z => normalizedCoordinateLiftedMatrix κ ρ α z i j) :=
  measurable_const.mul (liftedMatrix_measurable h i j)

/-- The actual exponential lift supplies the library's safe homogeneous weak
solution on every open part of its finite cylinder. -/
theorem pde_coordinate_lift_solution {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    {U : Set (Vec d)} (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K)) :
    PDE.IsWeakDivergenceFormSolutionOn (normalizedCoordinateLiftedMatrix κ ρ α) Ω
      (pdeH1OfNative ((coordinateLiftH1 hU hUfinite hu hg hw
        (Real.sqrt eigenvalue) hK).restrict hΩ hsub)) (0 : Vec (d + 1) → ℝ) 0 := by
  apply pde_homogeneous_solution_smul (c := κ⁻¹)
  intro φ
  have hφ : IsSpatialTest Ω φ.toFun :=
    ⟨φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset⟩
  have hflux := fun i => (liftedFlux_memLp hκ h hU hUfinite hu hg
    (Real.sqrt eigenvalue) hK i).mono_measure (Measure.restrict_mono hsub le_rfl)
  refine ⟨⟨PDE.integrableOn_vecDot_weakTestFunction_grad hflux φ, ?_, ?_⟩, ?_⟩
  · simp only [Pi.zero_apply, zero_mul]
    exact integrable_zero _ _ _
  · simp only [Pi.zero_apply, PDE.vecDot, zero_mul, Finset.sum_const_zero]
    exact integrable_zero _ _ _
  · have hC : MeasurableSet (productCoordinates ⁻¹' (U ×ˢ K)) :=
      (hU.prod hK.measurableSet).preimage
        (productCoordinates (d := d)).continuous.measurable
    have heq := integral_coordinate_lift_eigenfunction_eq_zero hκ h hU hUfinite
      hu hg eigenvalue heigenvalue hweak ⟨hφ.1, hφ.2.1, hφ.2.2.trans hsub⟩
    rw [setIntegral_flux_dot_test_eq hC hsub _ hφ] at heq
    change (∫ z in Ω, dot ((liftedMatrix (ρ (productCoordinates z).1)
      (α (productCoordinates z).1)).mulVec
        (liftedGradient u g (Real.sqrt eigenvalue) z)) (gradient φ.toFun z)) = _
    simpa only [Pi.zero_apply, zero_mul, PDE.vecDot, Finset.sum_const_zero,
      integral_zero, sub_self] using heq

/-- Spatial almost-everywhere nonnegativity propagates to the actual
exponential lift by restricted product volume, for every signed exponent. -/
theorem coordinate_lift_nonneg_ae {U : Set (Vec d)} (hU : MeasurableSet U)
    {u : Vec d → ℝ} (hu0 : ∀ᵐ x ∂volume.restrict U, 0 ≤ u x) (c : ℝ)
    {K : Set ℝ} (hK : MeasurableSet K) {Ω : Set (Vec (d + 1))}
    (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K)) :
    ∀ᵐ z ∂volume.restrict Ω, 0 ≤ liftedValue u c z := by
  have hp : ∀ᵐ p ∂(volume.restrict U).prod (volume.restrict K), 0 ≤ u p.1 :=
    Measure.quasiMeasurePreserving_fst.ae hu0
  have hc := (productCoordinates_measurePreserving_cylinder hU hK).quasiMeasurePreserving.ae hp
  filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hc] with z hz
  exact mul_nonneg hz (Real.exp_pos _).le

/-- The genuine one-ball Harnack theorem applies to the actual exponential
lift of a nonnegative weak eigenfunction. Its constant is chosen using only
the lifted dimension; no continuity representative is assumed. -/
theorem exists_coordinate_lift_harnack_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (κ : ℝ) (_hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (U : Set (Vec d)) (_hU : MeasurableSet U) (_hUfinite : volume U ≠ ∞)
      (u : Vec d → ℝ) (g : Vec d → Vec d)
      (_hu : MemLp u 2 (volume.restrict U))
      (_hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
      (_hw : HasWeakGradient U u g) (eigenvalue : ℝ), 0 ≤ eigenvalue →
    (∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x) →
    ∀ (K : Set ℝ) (_hK : IsCompact K) (Ω : Set (Vec (d + 1))) (_hΩ : IsOpen Ω),
    Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K) →
    (∀ᵐ x ∂volume.restrict U, 0 ≤ u x) →
    ∀ (y : Vec (d + 1)) (s : ℝ), 0 < s → PDE.euclideanBall y (2 * s) ⊆ Ω →
      essSup (fun z => ENNReal.ofReal (liftedValue u (Real.sqrt eigenvalue) z))
          (volume.restrict (PDE.euclideanBall y s)) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))) *
          essInf (fun z => ENNReal.ofReal (liftedValue u (Real.sqrt eigenvalue) z))
            (volume.restrict (PDE.euclideanBall y s)) := by
  obtain ⟨C, hC, hH⟩ := PDE.Ch4GreenHarnack.harnack_one_ball (d + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro κ hκ ρ α h U hU hUfinite u g hu hg hw eigenvalue heigenvalue hweak
    K hK Ω hΩ hsub hu0 y s hs hball
  exact hH ((κ ^ 4)⁻¹) (normalizedCoordinateLiftedMatrix κ ρ α) Ω hΩ
    (fun i j => (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable)
    (fun z _ => normalizedCoordinateLiftedMatrix_elliptic hκ h z)
    (pdeH1OfNative ((coordinateLiftH1 hU hUfinite hu hg hw
      (Real.sqrt eigenvalue) hK).restrict hΩ hsub))
    (coordinate_lift_nonneg_ae hU hu0 (Real.sqrt eigenvalue) hK.measurableSet hsub)
    (pde_coordinate_lift_solution hκ h hU hUfinite hu hg hw eigenvalue heigenvalue
      hweak hK hΩ hsub) y s hs hball

/-- Averaging a product-almost-everywhere bound for an actual exponential
lift yields spatial bounds. The moment and measure mass are retained
explicitly, and no distinguished transverse slice is selected. -/
theorem transverse_average_ae_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (c : ℝ) (hE : Integrable (fun t => Real.exp (c * t)) ν)
    {u : X → ℝ} {A B : ℝ}
    (hb : ∀ᵐ p ∂μ.prod ν,
      A ≤ u p.1 * Real.exp (c * p.2) ∧ u p.1 * Real.exp (c * p.2) ≤ B) :
    0 < ν.real Set.univ / (∫ t, Real.exp (c * t) ∂ν) ∧
      ∀ᵐ x ∂μ,
        A * (ν.real Set.univ / (∫ t, Real.exp (c * t) ∂ν)) ≤ u x ∧
        u x ≤ B * (ν.real Set.univ / (∫ t, Real.exp (c * t) ∂ν)) := by
  have hM := integral_exp_pos hE
  refine ⟨div_pos measureReal_univ_pos hM, ?_⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hb] with x hx
  have hi : Integrable (fun t => u x * Real.exp (c * t)) ν := hE.const_mul _
  have hl := integral_mono_ae (integrable_const A) hi (hx.mono fun _ ht => ht.1)
  have hr := integral_mono_ae hi (integrable_const B) (hx.mono fun _ ht => ht.2)
  rw [integral_const, integral_const_mul] at hl hr
  simp only [smul_eq_mul] at hl hr
  constructor
  · rw [← mul_div_assoc]
    apply (div_le_iff₀ hM).2
    simpa only [mul_comm] using hl
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hM).2
    simpa only [mul_comm] using hr

/-- A finite-valued nonnegative function satisfying an essential Harnack
comparison has finite real bounds with the same comparison factor. -/
theorem exists_real_bounds_of_ennreal_harnack {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [NeZero μ] {f : X → ℝ} {H : ℝ} (hH0 : 0 ≤ H)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hH : essSup (fun x => ENNReal.ofReal (f x)) μ ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (f x)) μ) :
    ∃ A B : ℝ, 0 ≤ A ∧ B ≤ H * A ∧ ∀ᵐ x ∂μ, A ≤ f x ∧ f x ≤ B := by
  let F := fun x => ENNReal.ofReal (f x)
  have hl : ∀ᵐ x ∂μ, essInf F μ ≤ F x := ae_essInf_le
  obtain ⟨x, hx⟩ := hl.exists
  have hi : essInf F μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hx
  have hp : ENNReal.ofReal H * essInf F μ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hi
  have hs : essSup F μ ≠ ∞ := ne_top_of_le_ne_top hp hH
  refine ⟨(essInf F μ).toReal, (essSup F μ).toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH0] using
      ENNReal.toReal_mono hp hH
  · filter_upwards [hl, ENNReal.ae_le_essSup F, hf0] with x hxl hxu hx0
    constructor
    · simpa only [F, ENNReal.toReal_ofReal hx0] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hxl
    · simpa only [F, ENNReal.toReal_ofReal hx0] using ENNReal.toReal_mono hs hxu

/-- A common positive normalization of real lower and upper bounds cancels
from the essential Harnack comparison. -/
theorem ennreal_harnack_of_scaled_ae_bounds {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {u : X → ℝ} {A B H F : ℝ} (hH0 : 0 ≤ H) (hF : 0 ≤ F)
    (hcomp : B ≤ H * A) (hb : ∀ᵐ x ∂μ, A * F ≤ u x ∧ u x ≤ B * F) :
    essSup (fun x => ENNReal.ofReal (u x)) μ ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (u x)) μ := by
  have hu := essSup_le_of_ae_le (ENNReal.ofReal (B * F))
    (hb.mono fun _ hx => ENNReal.ofReal_le_ofReal hx.2)
  have hl := le_essInf_of_ae_le (ENNReal.ofReal (A * F))
    (hb.mono fun _ hx => ENNReal.ofReal_le_ofReal hx.1)
  refine hu.trans ((?_ : ENNReal.ofReal (B * F) ≤
    ENNReal.ofReal H * ENNReal.ofReal (A * F)).trans (mul_le_mul_right hl _))
  rw [← ENNReal.ofReal_mul hH0]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [mul_le_mul_of_nonneg_right hcomp hF])

/-- Product-almost-everywhere real bounds for an exponential lift descend
to a spatial essential Harnack comparison by actual transverse integration. -/
theorem transverse_average_ennreal_harnack {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (ν : Measure ℝ) [IsFiniteMeasure ν] [NeZero ν]
    (c : ℝ) (hE : Integrable (fun t => Real.exp (c * t)) ν)
    {u : X → ℝ} {A B H : ℝ} (hH0 : 0 ≤ H) (hcomp : B ≤ H * A)
    (hb : ∀ᵐ p ∂μ.prod ν,
      A ≤ u p.1 * Real.exp (c * p.2) ∧ u p.1 * Real.exp (c * p.2) ≤ B) :
    essSup (fun x => ENNReal.ofReal (u x)) μ ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (u x)) μ := by
  obtain ⟨hF, hbounds⟩ := transverse_average_ae_bounds μ ν c hE hb
  exact ennreal_harnack_of_scaled_ae_bounds μ hH0 hF.le hcomp hbounds

/-- The explicit cylinder with spatial and transverse radii `R/4` lies
in the native-coordinate Euclidean ball of radius `R/2`. -/
theorem coordinate_cylinder_subset_half_ball (x₀ : Vec d) {R : ℝ} (hR : 0 < R) :
    productCoordinates ⁻¹'
      ({x : Vec d | euclideanNorm (x - x₀) < R / 4} ×ˢ Set.Icc (-(R / 4)) (R / 4)) ⊆
      PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2) := by
  have hn {n : ℕ} (x : Vec n) : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  intro z hz
  change euclideanNorm ((productCoordinates z).1 - x₀) < R / 4 ∧
    -(R / 4) ≤ (productCoordinates z).2 ∧ (productCoordinates z).2 ≤ R / 4 at hz
  change euclideanSq (z - productCoordinates.symm (x₀, 0)) < (R / 2) ^ 2
  rw [productCoordinates_euclideanSq]
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub,
    Prod.snd_sub, sub_zero, ← hn]
  have hx0 : 0 ≤ euclideanNorm ((productCoordinates z).1 - x₀) := Real.sqrt_nonneg _
  have ht : (productCoordinates z).2 ^ 2 ≤ (R / 4) ^ 2 := by
    nlinarith [sq_nonneg ((productCoordinates z).2)]
  nlinarith

/-- A Harnack comparison for the actual exponential lift on the half-ball
descends to the spatial Euclidean ball of radius `R/4`. It uses Fubini on a
positive transverse interval rather than evaluating an exceptional slice. -/
theorem spatial_harnack_of_coordinate_lift {u : Vec d → ℝ} {c H R : ℝ}
    (x₀ : Vec d) (hR : 0 < R) (hH0 : 0 ≤ H)
    (hu0 : ∀ᵐ z ∂volume.restrict
      (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2)),
      0 ≤ liftedValue u c z)
    (hH : essSup (fun z => ENNReal.ofReal (liftedValue u c z))
        (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2))) ≤
      ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (liftedValue u c z))
        (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2)))) :
    essSup (fun x => ENNReal.ofReal (u x))
        (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R / 4}) ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (u x))
        (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R / 4}) := by
  let S := {x : Vec d | euclideanNorm (x - x₀) < R / 4}
  let K := Set.Icc (-(R / 4)) (R / 4)
  have hS : MeasurableSet S := by
    have hn : Continuous (fun x : Vec d => euclideanNorm x) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (isOpen_lt (hn.comp (continuous_id.sub continuous_const)) continuous_const).measurableSet
  have hr : 0 < R / 2 := by positivity
  have hposB : 0 < volume (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2)) :=
    (PDE.isOpen_euclideanBall _ _).measure_pos volume
      ⟨_, PDE.center_mem_euclideanBall _ hr⟩
  have : NeZero (volume.restrict
      (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2))) := ⟨by
    intro h
    have he := Measure.restrict_apply_self volume
      (PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2))
    rw [h] at he
    exact hposB.ne' (by simpa using he.symm)⟩
  obtain ⟨A, B, _hA, hcomp, hb⟩ :=
    exists_real_bounds_of_ennreal_harnack _ hH0 hu0 hH
  have hbc := ae_restrict_of_ae_restrict_of_subset
    (coordinate_cylinder_subset_half_ball x₀ hR) hb
  have hp := (productCoordinates_symm_measurePreserving_cylinder hS
    measurableSet_Icc).quasiMeasurePreserving.ae hbc
  have hp' : ∀ᵐ p ∂(volume.restrict S).prod (volume.restrict K),
      A ≤ u p.1 * Real.exp (c * p.2) ∧ u p.1 * Real.exp (c * p.2) ≤ B := by
    simpa only [liftedValue, ContinuousLinearEquiv.apply_symm_apply] using hp
  have hKpos : 0 < volume K := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have : NeZero (volume.restrict K) := ⟨by
    intro h
    have he := Measure.restrict_apply_self volume K
    rw [h] at he
    exact hKpos.ne' (by simpa using he.symm)⟩
  have hcont : Continuous (fun t : ℝ => Real.exp (c * t)) := by fun_prop
  have hE : Integrable (fun t => Real.exp (c * t)) (volume.restrict K) :=
    hcont.continuousOn.integrableOn_compact isCompact_Icc
  exact transverse_average_ennreal_harnack (volume.restrict S) (volume.restrict K)
    c hE hH0 hcomp hp'

/-- Interior spatial Harnack comparison for the genuine nonnegative weak
eigenfunction. The constant depends only on the dimension, the coefficient
ratio is `κ⁻⁴`, and the comparison holds on the explicit ball of radius `R/4`.
No nonzero normalization or absolute positive amplitude is inferred. -/
theorem exists_spatial_eigenfunction_harnack_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (κ : ℝ) (_hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (U : Set (Vec d)) (_hU : MeasurableSet U) (_hUfinite : volume U ≠ ∞)
      (u : Vec d → ℝ) (g : Vec d → Vec d)
      (_hu : MemLp u 2 (volume.restrict U))
      (_hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
      (_hw : HasWeakGradient U u g) (eigenvalue : ℝ), 0 ≤ eigenvalue →
    (∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x) →
    ∀ (K : Set ℝ) (_hK : IsCompact K) (Ω : Set (Vec (d + 1))) (_hΩ : IsOpen Ω),
    Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K) →
    (∀ᵐ x ∂volume.restrict U, 0 ≤ u x) →
    ∀ (x₀ : Vec d) (R : ℝ), 0 < R →
      PDE.euclideanBall (productCoordinates.symm (x₀, 0)) R ⊆ Ω →
      essSup (fun x => ENNReal.ofReal (u x))
          (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R / 4}) ≤
        ENNReal.ofReal (Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))) *
          essInf (fun x => ENNReal.ofReal (u x))
            (volume.restrict {x : Vec d | euclideanNorm (x - x₀) < R / 4}) := by
  obtain ⟨C, hC, hH⟩ := exists_coordinate_lift_harnack_constant d hd
  refine ⟨C, hC, ?_⟩
  intro κ hκ ρ α h U hU hUfinite u g hu hg hw eigenvalue heigenvalue hweak
    K hK Ω hΩ hsub hu0 x₀ R hR hball
  have hr : 0 < R / 2 := by positivity
  have hsmall : PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2) ⊆ Ω :=
    (PDE.euclideanBall_mono hr.le (by linarith : R / 2 ≤ R)).trans hball
  have hnonneg := ae_restrict_of_ae_restrict_of_subset hsmall
    (coordinate_lift_nonneg_ae hU hu0 (Real.sqrt eigenvalue) hK.measurableSet hsub)
  exact spatial_harnack_of_coordinate_lift x₀ hR (Real.exp_pos _).le hnonneg
    (hH κ hκ ρ α h U hU hUfinite u g hu hg hw eigenvalue heigenvalue hweak
      K hK Ω hΩ hsub hu0 (productCoordinates.symm (x₀, 0)) (R / 2) hr
      (by simpa only [show 2 * (R / 2) = R by ring] using hball))

/-- The source and PDE-library balls use the same explicit Euclidean norm. -/
theorem pde_ball_eq_sourceBall {n : ℕ} (x : Vec n) {r : ℝ} (hr : 0 < r) :
    PDE.euclideanBall x r = sourceBall x r := by
  ext y
  exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr

/-- A finite-mode certificate for positivity between two actual ball indicators.
The cutoff is uniform in the two times and centers; the certificate itself must
still be established for the particular balls and times. -/
theorem exists_dirichletHilbert_heat_ball_pairing_pos_of_finite_modes (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eigenvalue : ℕ → ℝ)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      ∀ M : ℝ, ∃ N : ℕ, ∀ (s t : ℝ≥0) (c₁ c₂ : Vec d) (r₁ r₂ : ℝ)
        (hr₁ : 0 < r₁) (hr₂ : 0 < r₂),
        let hs₁ : MeasurableSet (sourceBall c₁ r₁) := by
          rw [← pde_ball_eq_sourceBall c₁ hr₁]
          exact (PDE.isOpen_euclideanBall c₁ r₁).measurableSet
        let hs₂ : MeasurableSet (sourceBall c₂ r₂) := by
          rw [← pde_ball_eq_sourceBall c₂ hr₂]
          exact (PDE.isOpen_euclideanBall c₂ r₂).measurableSet
        letI : IsFiniteMeasure (dirichletVolume ρ R) :=
          dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        let f := indicatorConstLp 2 hs₁ (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
        let g := indicatorConstLp 2 hs₂ (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
        Real.exp (-M * (s + t)) * (‖f‖ * ‖g‖) <
          ∑ n ∈ Finset.range N, Real.exp (-eigenvalue n * (s + t)) *
            (b.repr f n * b.repr g n) →
        0 < inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
          (SpectralHeat.heatOperator b eigenvalue hpos t g) := by
  obtain ⟨eigenvalue, _u, b, hpos, _hp, _hl, _hb, htail⟩ :=
    exists_dirichletHilbert_heat_two_times_finite_tail hd hκ h R hR
  refine ⟨eigenvalue, b, hpos, ?_⟩
  intro M
  obtain ⟨N, hN⟩ := htail M
  refine ⟨N, ?_⟩
  intro s t c₁ c₂ r₁ r₂ hr₁ hr₂
  dsimp only
  intro hcertificate
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let hs₁ : MeasurableSet (sourceBall c₁ r₁) := by
    rw [← pde_ball_eq_sourceBall c₁ hr₁]
    exact (PDE.isOpen_euclideanBall c₁ r₁).measurableSet
  let hs₂ : MeasurableSet (sourceBall c₂ r₂) := by
    rw [← pde_ball_eq_sourceBall c₂ hr₂]
    exact (PDE.isOpen_euclideanBall c₂ r₂).measurableSet
  let f := indicatorConstLp 2 hs₁ (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
  let g := indicatorConstLp 2 hs₂ (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
  have hbound := hN s t f g
  have hleft := (abs_le.mp hbound).1
  change Real.exp (-M * (s + t)) * (‖f‖ * ‖g‖) < _ at hcertificate
  change 0 < inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s f)
    (SpectralHeat.heatOperator b eigenvalue hpos t g)
  linarith

#print axioms exists_dirichletHilbert_heat_ball_pairing_pos_of_finite_modes

/-- A straight segment in a concentric interior ball admits a chain with
an explicit number of steps. The step condition uses Euclidean length. -/
theorem interior_ball_segment_chain (c : Vec d) {r s : ℝ} (hr : 0 < r)
    {n : ℕ} (hn : 0 < n) (hstep : 2 * r < n * s)
    {x y : Vec d} (hx : x ∈ sourceBall c r) (hy : y ∈ sourceBall c r) :
    PDE.Ch4GreenHarnack.IsChain (sourceBall c r) s n x y := by
  let γ : ℝ → Vec d := fun t => (1 - t) • x + t • y
  have hconv : Convex ℝ (sourceBall c r) := by
    rw [← pde_ball_eq_sourceBall c hr]
    exact PDE.convex_euclideanBall c r
  have hK : ∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ sourceBall c r := by
    intro t ht
    exact hconv hx hy (by linarith only [ht.2]) ht.1 (by ring)
  have hxy : PDE.vecEuclideanNorm (y - x) ≤ 2 * r := by
    have htri := PDE.vecEuclideanNorm_add_le (y - c) (c - x)
    rw [PDE.vecEuclideanNorm_sub_comm c x] at htri
    have hid : y - c + (c - x) = y - x := by abel
    rw [hid] at htri
    change PDE.vecEuclideanNorm (x - c) < r at hx
    change PDE.vecEuclideanNorm (y - c) < r at hy
    linarith only [htri, hx, hy]
  have hL : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ t' ∈ Set.Icc (0 : ℝ) 1,
      PDE.vecEuclideanNorm (γ t - γ t') ≤ 2 * r * |t - t'| := by
    intro t _ t' _
    have hid : γ t - γ t' = (t - t') • (y - x) := by
      ext i
      simp only [γ, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hid, PDE.vecEuclideanNorm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hxy (abs_nonneg (t - t'))
  simpa only [γ, sub_zero, one_smul, zero_smul, add_zero, sub_self, zero_add] using
    PDE.Ch4GreenHarnack.IsChain.of_lipschitz hK hL hn hstep

/-- Local essential comparisons propagate along an actual finite chain.
The overlap step is the proved positive-measure ball-intersection argument. -/
theorem spatial_harnack_along_chain {u : Vec d → ℝ} {K : Set (Vec d)}
    {s : ℝ} (hs : 0 < s) {H : ℝ≥0∞}
    (hlocal : ∀ z ∈ K,
      essSup (fun x => ENNReal.ofReal (u x)) (volume.restrict (sourceBall z s)) ≤
        H * essInf (fun x => ENNReal.ofReal (u x)) (volume.restrict (sourceBall z s)))
    {n : ℕ} {x y : Vec d} (hchain : PDE.Ch4GreenHarnack.IsChain K s n x y) :
    essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
      H ^ (n + 1) * essInf (fun z => ENNReal.ofReal (u z))
        (volume.restrict (sourceBall y s)) := by
  apply PDE.Ch4GreenHarnack.chain_propagate hlocal ?_ hchain
  intro z _ z' _ hclose
  simpa only [PDE.volumeOn, pde_ball_eq_sourceBall _ hs] using
    PDE.Ch4GreenHarnack.essInf_le_essSup_of_close (fun w => ENNReal.ofReal (u w)) hs hclose

/-- The checked spatial estimate for the genuine weak eigenfunction chains
with a constant chosen before the coefficients, scale, function and chain. -/
theorem exists_spatial_eigenfunction_harnack_chain_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (κ : ℝ) (_hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (U : Set (Vec d)) (_hU : MeasurableSet U) (_hUfinite : volume U ≠ ∞)
      (u : Vec d → ℝ) (g : Vec d → Vec d)
      (_hu : MemLp u 2 (volume.restrict U))
      (_hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
      (_hw : HasWeakGradient U u g) (eigenvalue : ℝ), 0 ≤ eigenvalue →
    (∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x) →
    ∀ (K : Set ℝ) (_hK : IsCompact K) (Ω : Set (Vec (d + 1))) (_hΩ : IsOpen Ω),
    Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K) →
    (∀ᵐ x ∂volume.restrict U, 0 ≤ u x) →
    ∀ (centers : Set (Vec d)) (s : ℝ), 0 < s →
    (∀ z ∈ centers, PDE.euclideanBall (productCoordinates.symm (z, 0)) (4 * s) ⊆ Ω) →
    ∀ (n : ℕ) (x y : Vec d), PDE.Ch4GreenHarnack.IsChain centers s n x y →
      essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
        (ENNReal.ofReal (Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹)))) ^ (n + 1) *
          essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall y s)) := by
  obtain ⟨C, hC, hH⟩ := exists_spatial_eigenfunction_harnack_constant d hd
  refine ⟨C, hC, ?_⟩
  intro κ hκ ρ α h U hU hUfinite u g hu hg hw eigenvalue heigenvalue hweak
    K hK Ω hΩ hsub hu0 centers s hs hballs n x y hchain
  apply spatial_harnack_along_chain hs ?_ hchain
  intro z hz
  simpa only [show 4 * s / 4 = s by ring, sourceBall] using
    hH κ hκ ρ α h U hU hUfinite u g hu hg hw eigenvalue heigenvalue hweak
      K hK Ω hΩ hsub hu0 z (4 * s) (by positivity) (hballs z hz)

/-- Bounds holding almost everywhere on every ball in an arbitrary open
cover hold almost everywhere on the covered set. A countable subcover is
chosen before combining the exceptional sets. -/
theorem ae_restrict_of_open_cover {ι : Type*} {S : Set (Vec d)}
    (U : ι → Set (Vec d)) (hU : ∀ i, IsOpen (U i))
    (hcover : S ⊆ ⋃ i, U i) {p : Vec d → Prop}
    (hp : ∀ i, ∀ᵐ x ∂volume.restrict (U i), p x) :
    ∀ᵐ x ∂volume.restrict S, p x := by
  obtain ⟨t, ht, heq⟩ := eq_open_union_countable U hU
  have ha : ∀ᵐ x ∂volume.restrict (⋃ i ∈ t, U i), p x :=
    (ae_restrict_biUnion_iff U ht p).2 (fun i _ => hp i)
  exact ae_restrict_of_ae_restrict_of_subset (hcover.trans heq.symm.subset) ha

/-- The full lifted Euclidean ball lies in the spatial source ball times
a compact transverse interval, with exactly the same radius. -/
theorem coordinate_ball_subset_spatial_cylinder (c : Vec d) {R : ℝ} (hR : 0 < R) :
    PDE.euclideanBall (productCoordinates.symm (c, 0)) R ⊆
      productCoordinates ⁻¹' (sourceBall c R ×ˢ Set.Icc (-R) R) := by
  intro z hz
  change euclideanSq (z - productCoordinates.symm (c, 0)) < R ^ 2 at hz
  rw [productCoordinates_euclideanSq] at hz
  simp only [map_sub, ContinuousLinearEquiv.apply_symm_apply, Prod.fst_sub,
    Prod.snd_sub, sub_zero] at hz
  have hsp : 0 ≤ euclideanSq ((productCoordinates z).1 - c) :=
    PDE.vecNormSq_nonneg _
  have ht : |(productCoordinates z).2| < R :=
    abs_lt_of_sq_lt_sq (by linarith only [hz, hsp]) hR.le
  refine ⟨?_, (abs_lt.mp ht).1.le, (abs_lt.mp ht).2.le⟩
  change Real.sqrt (euclideanSq ((productCoordinates z).1 - c)) < R
  exact (Real.sqrt_lt' hR).2 (by nlinarith only [hz, sq_nonneg (productCoordinates z).2])

/-- Every center in a compact concentric subball has the claimed lifted
interior radius. This proves the enlarged-ball inclusion used by Harnack. -/
theorem coordinate_interior_ball_subset (c : Vec d) {R r s : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hmargin : r + 4 * s ≤ R)
    {x : Vec d} (hx : x ∈ sourceBall c r) :
    PDE.euclideanBall (productCoordinates.symm (x, 0)) (4 * s) ⊆
      PDE.euclideanBall (productCoordinates.symm (c, 0)) R := by
  apply PDE.euclideanBall_subset_of_center_norm_add_le (by positivity) hR
  change euclideanNorm (productCoordinates.symm (x, 0) -
    productCoordinates.symm (c, 0)) + 4 * s ≤ R
  rw [euclideanNorm_productCoordinates_symm_sub]
  have hxc : euclideanNorm (x - c) < r := hx
  linarith only [hxc, hmargin]

/-- An actual source-ball weak eigenfunction has a uniform chain comparison
between any two interior balls. The step count and interior margin are
explicit; no boundary lower bound or representative is assumed. -/
theorem exists_sourceBall_eigenfunction_interior_chain_constant (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (κ : ℝ) (_hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (c : Vec d) (R : ℝ), 0 < R →
    ∀ (u : Vec d → ℝ) (g : Vec d → Vec d)
      (_hu : MemLp u 2 (volume.restrict (sourceBall c R)))
      (_hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (sourceBall c R)))
      (_hw : HasWeakGradient (sourceBall c R) u g) (eigenvalue : ℝ), 0 ≤ eigenvalue →
    (∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall c R) ψ →
      (∫ x in sourceBall c R, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in sourceBall c R, (ρ x * u x) * ψ x) →
    (∀ᵐ x ∂volume.restrict (sourceBall c R), 0 ≤ u x) →
    ∀ (r s : ℝ), 0 < r → 0 < s → r + 4 * s ≤ R →
    ∀ (n : ℕ), 0 < n → 2 * r < n * s →
    ∀ (x y : Vec d), x ∈ sourceBall c r → y ∈ sourceBall c r →
      essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
        (ENNReal.ofReal (Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹)))) ^ (n + 1) *
          essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall y s)) := by
  obtain ⟨C, hC, hH⟩ := exists_spatial_eigenfunction_harnack_chain_constant d hd
  refine ⟨C, hC, ?_⟩
  intro κ hκ ρ α h c R hR u g hu hg hw eigenvalue heigenvalue hweak hu0
    r s hr hs hmargin n hn hstep x y hx hy
  have hU : MeasurableSet (sourceBall c R) := by
    rw [← pde_ball_eq_sourceBall c hR]
    exact PDE.measurableSet_euclideanBall c R
  have hfinite : volume (sourceBall c R) ≠ ∞ := by
    rw [← pde_ball_eq_sourceBall c hR]
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (PDE.euclideanBall_subset_supBall hR))
  exact hH κ hκ ρ α h (sourceBall c R) hU hfinite u g hu hg hw eigenvalue
    heigenvalue hweak (Set.Icc (-R) R) isCompact_Icc
    (PDE.euclideanBall (productCoordinates.symm (c, 0)) R)
    (PDE.isOpen_euclideanBall _ _) (coordinate_ball_subset_spatial_cylinder c hR) hu0
    (sourceBall c r) s hs (fun _ hz => coordinate_interior_ball_subset c hR hs hmargin hz)
    n x y (interior_ball_segment_chain c hr hn hstep hx hy)

/-- A genuine seed amplitude propagates to the whole interior ball.
The countable-cover step preserves the almost-everywhere qualifier, and the
loss is the exact finite Harnack-chain factor. The seed is not manufactured
from nonnegativity. -/
theorem interior_ae_lower_of_harnack_chains {u : Vec d → ℝ}
    (c : Vec d) {r s : ℝ} (hs : 0 < s) {H : ℝ} (hH : 0 < H)
    {n : ℕ} {x : Vec d} {a : ℝ}
    (hseed : ENNReal.ofReal a ≤ essSup (fun z => ENNReal.ofReal (u z))
      (volume.restrict (sourceBall x s)))
    (hchain : ∀ y ∈ sourceBall c r,
      essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
        (ENNReal.ofReal H) ^ (n + 1) * essInf (fun z => ENNReal.ofReal (u z))
          (volume.restrict (sourceBall y s)))
    (hu0 : ∀ᵐ z ∂volume.restrict (sourceBall c r), 0 ≤ u z) :
    ∀ᵐ z ∂volume.restrict (sourceBall c r), a / H ^ (n + 1) ≤ u z := by
  have hpow : 0 < H ^ (n + 1) := pow_pos hH _
  have hlocal (y : sourceBall c r) :
      ∀ᵐ z ∂volume.restrict (sourceBall y.1 s),
        ENNReal.ofReal (a / H ^ (n + 1)) ≤ ENNReal.ofReal (u z) := by
    have hbound : ENNReal.ofReal a / ENNReal.ofReal (H ^ (n + 1)) ≤
        essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall y.1 s)) := by
      apply (ENNReal.div_le_iff' (ENNReal.ofReal_pos.mpr hpow).ne' ENNReal.ofReal_ne_top).2
      simpa only [ENNReal.ofReal_pow hH.le] using hseed.trans (hchain y.1 y.2)
    filter_upwards [ae_essInf_le (f := fun z => ENNReal.ofReal (u z))
      (μ := volume.restrict (sourceBall y.1 s))] with z hz
    rw [ENNReal.ofReal_div_of_pos hpow]
    exact hbound.trans hz
  have hcover : sourceBall c r ⊆ ⋃ y : sourceBall c r, sourceBall y.1 s := by
    intro y hy
    refine Set.mem_iUnion.2 ⟨⟨y, hy⟩, ?_⟩
    rw [← pde_ball_eq_sourceBall y hs]
    exact PDE.center_mem_euclideanBall y hs
  have ha := ae_restrict_of_open_cover (fun y : sourceBall c r => sourceBall y.1 s)
    (fun y => by rw [← pde_ball_eq_sourceBall y.1 hs]; exact PDE.isOpen_euclideanBall _ _)
    hcover hlocal
  filter_upwards [ha, hu0] with z hz hz0
  exact (ENNReal.ofReal_le_ofReal_iff hz0).1 hz

/-- A positive weighted square mass and an essential Harnack comparison
supply a quantitative positive real lower amplitude. The finite measure
mass, coefficient upper bound and seed mass all remain explicit. -/
theorem positive_ae_lower_of_weighted_sq_mass {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ]
    {f ρ : X → ℝ} {κ H m : ℝ} (hκ : 0 < κ) (hH : 0 < H) (hm : 0 < m)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hρ : ∀ᵐ x ∂μ, ρ x ≤ κ⁻¹)
    (hi : Integrable (fun x => ρ x * (f x) ^ 2) μ)
    (hmass : m ≤ ∫ x, ρ x * (f x) ^ 2 ∂μ)
    (hcomp : essSup (fun x => ENNReal.ofReal (f x)) μ ≤
      ENNReal.ofReal H * essInf (fun x => ENNReal.ofReal (f x)) μ) :
    0 < Real.sqrt (m / (κ⁻¹ * μ.real Set.univ)) / H ∧
      ∀ᵐ x ∂μ, Real.sqrt (m / (κ⁻¹ * μ.real Set.univ)) / H ≤ f x := by
  obtain ⟨A, B, _hA, hBA, hb⟩ := exists_real_bounds_of_ennreal_harnack μ hH.le hf0 hcomp
  have hB0 : 0 ≤ B := by
    obtain ⟨x, hx, hx0⟩ := (hb.and hf0).exists
    exact hx0.trans hx.2
  have hbnd : ∀ᵐ x ∂μ, ρ x * (f x) ^ 2 ≤ κ⁻¹ * B ^ 2 := by
    filter_upwards [hb, hf0, hρ] with x hx hx0 hxρ
    calc
      ρ x * (f x) ^ 2 ≤ κ⁻¹ * (f x) ^ 2 :=
        mul_le_mul_of_nonneg_right hxρ (sq_nonneg _)
      _ ≤ κ⁻¹ * B ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hx.2, hx0, hB0]) (inv_nonneg.mpr hκ.le)
  have hint := integral_mono_ae hi (integrable_const (κ⁻¹ * B ^ 2)) hbnd
  rw [integral_const] at hint
  simp only [smul_eq_mul] at hint
  have hden : 0 < κ⁻¹ * μ.real Set.univ := mul_pos (inv_pos.mpr hκ) measureReal_univ_pos
  have hsqrt : Real.sqrt (m / (κ⁻¹ * μ.real Set.univ)) ≤ B := by
    apply (Real.sqrt_le_left hB0).2
    apply (div_le_iff₀ hden).2
    nlinarith only [hmass.trans hint]
  refine ⟨div_pos (Real.sqrt_pos.mpr (div_pos hm hden)) hH, ?_⟩
  filter_upwards [hb] with x hx
  exact ((div_le_iff₀ hH).2 (by simpa only [mul_comm] using hsqrt.trans hBA)).trans hx.1

/-- Positive mass in a genuine seed ball propagates through the local
comparisons to a positive essential lower bound throughout the interior
ball. This is an internal consumer of explicit analytic estimates, not an
extra hypothesis of the tube-probability graph node. -/
theorem interior_ae_lower_of_seed_mass {u ρ : Vec d → ℝ}
    (c : Vec d) {r s κ H m : ℝ} (hs : 0 < s)
    (hκ : 0 < κ) (hH : 0 < H) (hm : 0 < m)
    (hρ : ∀ z, ρ z ≤ κ⁻¹) {n : ℕ} {x : Vec d}
    (hi : Integrable (fun z => ρ z * (u z) ^ 2) (volume.restrict (sourceBall x s)))
    (hmass : m ≤ ∫ z in sourceBall x s, ρ z * (u z) ^ 2)
    (hseed0 : ∀ᵐ z ∂volume.restrict (sourceBall x s), 0 ≤ u z)
    (hseedH : essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
      ENNReal.ofReal H * essInf (fun z => ENNReal.ofReal (u z))
        (volume.restrict (sourceBall x s)))
    (hchain : ∀ y ∈ sourceBall c r,
      essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
        (ENNReal.ofReal H) ^ (n + 1) * essInf (fun z => ENNReal.ofReal (u z))
          (volume.restrict (sourceBall y s)))
    (hu0 : ∀ᵐ z ∂volume.restrict (sourceBall c r), 0 ≤ u z) :
    let a := Real.sqrt (m / (κ⁻¹ * (volume.real (sourceBall x s)))) / H
    0 < a / H ^ (n + 1) ∧
      ∀ᵐ z ∂volume.restrict (sourceBall c r), a / H ^ (n + 1) ≤ u z := by
  have hball := pde_ball_eq_sourceBall x hs
  have hfinite : volume (sourceBall x s) ≠ ∞ := by
    rw [← hball]
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (PDE.euclideanBall_subset_supBall hs))
  letI : IsFiniteMeasure (volume.restrict (sourceBall x s)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfinite.lt_top⟩
  letI : NeZero (volume.restrict (sourceBall x s)) := by
    rw [← hball]
    exact PDE.Ch4GreenHarnack.neZero_volumeOn_of_isOpen
      (PDE.isOpen_euclideanBall x s) ⟨x, PDE.center_mem_euclideanBall x hs⟩
  obtain ⟨ha, hlow⟩ := positive_ae_lower_of_weighted_sq_mass
    (volume.restrict (sourceBall x s)) hκ hH hm hseed0
    (Filter.Eventually.of_forall hρ) hi hmass hseedH
  have hreal : (volume.restrict (sourceBall x s)).real Set.univ =
      volume.real (sourceBall x s) := by
    simp only [Measure.real, Measure.restrict_apply_univ]
  rw [hreal] at ha hlow
  refine ⟨div_pos ha (pow_pos hH _), ?_⟩
  apply interior_ae_lower_of_harnack_chains c hs hH ?_ hchain hu0
  obtain ⟨z, hzl, hzu⟩ :=
    (hlow.and (ENNReal.ae_le_essSup (fun z => ENNReal.ofReal (u z)))).exists
  exact (ENNReal.ofReal_le_ofReal hzl).trans hzu

/-- Actual nonnegative weak source-ball eigenfunctions propagate a positive
weighted seed mass throughout a concentric interior ball. All constants are
chosen in structural order and every scale, chain length and seed volume
is retained. This supplies analytic support; it does not identify a killed
process or infer a uniform seed mass from normalization. -/
theorem exists_sourceBall_eigenfunction_interior_lower_of_seed_mass
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (κ : ℝ) (_hκ : 0 < κ) (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (c : Vec d) (R : ℝ), 0 < R →
    ∀ (u : Vec d → ℝ) (g : Vec d → Vec d)
      (_hu : MemLp u 2 (volume.restrict (sourceBall c R)))
      (_hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (sourceBall c R)))
      (_hw : HasWeakGradient (sourceBall c R) u g) (eigenvalue : ℝ), 0 ≤ eigenvalue →
    (∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall c R) ψ →
      (∫ x in sourceBall c R, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in sourceBall c R, (ρ x * u x) * ψ x) →
    (∀ᵐ x ∂volume.restrict (sourceBall c R), 0 ≤ u x) →
    ∀ (r s : ℝ), 0 < r → 0 < s → r + 4 * s ≤ R →
    ∀ (n : ℕ), 0 < n → 2 * r < n * s →
    ∀ (x : Vec d), x ∈ sourceBall c r →
    ∀ (m : ℝ), 0 < m → (m ≤ ∫ z in sourceBall x s, ρ z * (u z) ^ 2) →
      let H := Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))
      let a := Real.sqrt (m / (κ⁻¹ * volume.real (sourceBall x s))) / H ^ (n + 1)
      0 < a / (H ^ (n + 1)) ∧
        ∀ᵐ z ∂volume.restrict (sourceBall c r), a / (H ^ (n + 1)) ≤ u z := by
  obtain ⟨C, hC, hchain⟩ := exists_sourceBall_eigenfunction_interior_chain_constant d hd
  refine ⟨C, hC, ?_⟩
  intro κ hκ ρ α h c R hR u g hu hg hw eigenvalue heigenvalue hweak hu0
    r s hr hs hmargin n hn hstep x hx m hm hmass
  let H := Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))
  have hH : 0 < H := Real.exp_pos _
  have hpow : 0 < H ^ (n + 1) := pow_pos hH _
  have hcomp := hchain κ hκ ρ α h c R hR u g hu hg hw eigenvalue heigenvalue
    hweak hu0 r s hr hs hmargin n hn hstep x
  have hseed : sourceBall x s ⊆ sourceBall c R := by
    rw [← pde_ball_eq_sourceBall x hs, ← pde_ball_eq_sourceBall c hR]
    apply PDE.euclideanBall_subset_of_center_norm_add_le hs hR
    change euclideanNorm (x - c) + s ≤ R
    change euclideanNorm (x - c) < r at hx
    linarith only [hx, hmargin, hs]
  have hinner : sourceBall c r ⊆ sourceBall c R := by
    intro z hz
    change euclideanNorm (z - c) < R
    change euclideanNorm (z - c) < r at hz
    linarith only [hz, hmargin, hs]
  have hint : IntegrableOn (fun z => ρ z * (u z) ^ 2) (sourceBall c R) := by
    exact hu.integrable_sq.mul_of_top_right
      (uniformlyElliptic_coefficients_memLp_top hκ h (volume.restrict (sourceBall c R))).1
  have hseedH : essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
      ENNReal.ofReal (H ^ (n + 1)) * essInf (fun z => ENNReal.ofReal (u z))
        (volume.restrict (sourceBall x s)) := by
    simpa only [H, ENNReal.ofReal_pow hH.le] using hcomp x hx hx
  have hchains : ∀ y ∈ sourceBall c r,
      essSup (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall x s)) ≤
        (ENNReal.ofReal (H ^ (n + 1))) ^ (0 + 1) *
          essInf (fun z => ENNReal.ofReal (u z)) (volume.restrict (sourceBall y s)) := by
    intro y hy
    simpa only [H, zero_add, pow_one, ENNReal.ofReal_pow hH.le] using hcomp y hx hy
  simpa only [zero_add, pow_one] using
    interior_ae_lower_of_seed_mass c hs hκ hpow hm (fun z => (h.2.2 z).2.1)
      (hint.mono_set hseed) hmass (ae_restrict_of_ae_restrict_of_subset hseed hu0)
      hseedH hchains (ae_restrict_of_ae_restrict_of_subset hinner hu0)

/-- The balls used in the tube step have a structural chain length: any
two centers in the three-quarter source subball are joined in 25 steps of
length less than `R/16`, and all radius-`R/4` lifted enlargements remain in
the full lifted source ball. The estimate is independent of `R` and `c`. -/
theorem tube_subball_harnack_chain_geometry (c : Vec d) {R : ℝ} (hR : 0 < R) :
    (∀ z ∈ sourceBall c (3 * R / 4),
      PDE.euclideanBall (productCoordinates.symm (z, 0)) (4 * (R / 16)) ⊆
        PDE.euclideanBall (productCoordinates.symm (c, 0)) R) ∧
    (∀ x ∈ sourceBall c (3 * R / 4), ∀ y ∈ sourceBall c (3 * R / 4),
      PDE.Ch4GreenHarnack.IsChain (sourceBall c (3 * R / 4)) (R / 16) 25 x y) := by
  constructor
  · intro z hz
    exact coordinate_interior_ball_subset c hR (by positivity) (by linarith only []) hz
  · intro x hx y hy
    exact interior_ball_segment_chain c (by positivity) (by norm_num)
      (by push_cast; linarith only [hR]) hx hy

/-- The actual weighted indicator of a source ball has a diagonal spectral
lower bound given by its pairing with any eigenbasis vector. -/
theorem sourceBall_indicator_heat_diagonal_lower (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (j : ℕ) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eigenvalue j * t) * (∫ x in sourceBall c r, b j x ∂dirichletVolume ρ R) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  have hs : MeasurableSet (sourceBall c r) := by
    rw [← pde_ball_eq_sourceBall c hr]
    exact (PDE.isOpen_euclideanBall c r).measurableSet
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
  have hfinite : dirichletVolume ρ R (sourceBall c r) ≠ ∞ := measure_ne_top _ _
  have h := SpectralHeat.heatOperator_diagonal_lower b eigenvalue hpos t
    (indicatorConstLp 2 hs hfinite (1 : ℝ)) j
  rw [real_inner_comm (indicatorConstLp 2 hs hfinite (1 : ℝ)) (b j),
    L2.inner_indicatorConstLp_one] at h
  exact h

/-- The completed Dirichlet weak equation identifies every spectral
coordinate of the actual eigenfunction, including degenerate eigenvalues. -/
theorem dirichletHilbert_eigenfunction_coordinates
    {κ : ℝ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (v : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (v n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (v n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (u : DirichletHilbertSpace (d := d) R hR) (eig : ℝ)
    (hweak : ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    ∀ n, (eigenvalue n - eig) * b.repr
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u) n = 0 := by
  intro n
  have hs : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => (v n).val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (v n).val (some i) x))
        (fun i => u.val (some i) x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have hsym : (α x).IsSymm := (h.2.2 x).2.2.1
      have heq := hsym.dotProduct_mulVec_comm
        (x := fun i => (v n).val (some i) x) (y := fun i => u.val (some i) x)
      rw [dotProduct_comm, dotProduct_comm (fun i => u.val (some i) x)] at heq
      exact heq
  rw [hweak, hvar, ← hb, real_inner_comm] at hs
  rw [b.repr_apply_apply]
  nlinarith only [hs]

/-- A native weak eigenfunction is the corresponding heat mode, including
when its eigenvalue has multiplicity greater than one. -/
theorem exists_native_weakEigenfunction_heat_mode {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u :
        Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      ∀ t : ℝ≥0, SpectralHeat.heatOperator b eigenvalue hpos t
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u) =
        Real.exp (-eig * t) •
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u) := by
  obtain ⟨u, hu, hvaru⟩ := exists_dirichletHilbert_weakEquation_of_native_smooth
    hd hκ h R hR v eig (native_weakEigenEquation_on_smooth R v eig hweak)
  refine ⟨u, hu, ?_⟩
  intro t
  exact SpectralHeat.heatOperator_eigenvector_of_coordinates b eigenvalue hpos _ eig
    (dirichletHilbert_eigenfunction_coordinates h R hR eigenvalue vs b hb hvar u eig hvaru) t

#print axioms exists_native_weakEigenfunction_heat_mode

/-- The genuine Dirichlet spectral basis can be chosen so that a given native
weak eigenfunction is a heat mode, without assuming spectral data. -/
theorem exists_dirichletSpectralHeat_native_weakEigenfunction_mode {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    ∃ (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      (∀ n, 0 < eigenvalue n) ∧
      (∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) ∧
      ∃ u : DirichletHilbertSpace (d := d) R hR,
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u :
          Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
        ∀ t : ℝ≥0, SpectralHeat.heatOperator b eigenvalue hpos t
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u) =
          Real.exp (-eig * t) •
            (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u) := by
  obtain ⟨eigenvalue, vs, heig, _hlim, he, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)) :=
    HilbertBasis.mk he (le_of_eq hspan.symm)
  have hb (n : ℕ) : b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n) := by
    exact congrFun (HilbertBasis.coe_mk he (le_of_eq hspan.symm)) n
  have hvarb (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w) := by
    rw [hb]
    exact hvar n w
  let hpos : ∀ n, 0 ≤ eigenvalue n := fun n => (heig n).le
  obtain ⟨u, hu, hmode⟩ := exists_native_weakEigenfunction_heat_mode
    hd hκ h R hR eigenvalue hpos vs b hb hvarb v eig hweak
  exact ⟨eigenvalue, vs, b, hpos, heig, hb, u, hu, hmode⟩

#print axioms exists_dirichletSpectralHeat_native_weakEigenfunction_mode

/-- The weighted spectral norm is the native weighted square integral when
the two representatives agree almost everywhere. -/
theorem dirichletVolume_inner_self_eq_native {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (f : Lp ℝ 2 (dirichletVolume ρ R)) (u : Vec d → ℝ)
    (hu : (f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u) :
    inner ℝ f f = ∫ x in sourceBall (0 : Vec d) R, ρ x * u x * u x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x * u x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hu] with x hx
      simp only [RCLike.inner_apply, conj_trivial, hx]
    _ = _ := by
      change (∫ x, u x * u x ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
        ring

#print axioms dirichletVolume_inner_self_eq_native

/-- A Lebesgue almost-everywhere interior lower bound transfers to an
almost-everywhere equal weighted spectral representative on that ball. -/
theorem dirichletVolume_restrict_ae_lower_of_native (ρ : Vec d → ℝ) (R : ℝ)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (u : Vec d → ℝ)
    (hu : (f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u)
    (s : Set (Vec d)) (a : ℝ) (hlower : ∀ᵐ x ∂volume.restrict s, a ≤ u x) :
    ∀ᵐ x ∂(dirichletVolume ρ R).restrict s, a ≤ f x := by
  have hac : dirichletVolume ρ R ≪ (volume : Measure (Vec d)) :=
    (withDensity_absolutelyContinuous _ _).trans Measure.absolutelyContinuous_restrict
  have hlow := (hac.restrict s).ae_le hlower
  filter_upwards [hlow, ae_restrict_of_ae hu] with x hx heq
  simpa only [heq] using hx

#print axioms dirichletVolume_restrict_ae_lower_of_native

/-- A normalized vector in a spectral eigenspace gives the same-ball
indicator bound, without selecting a basis vector. -/
theorem sourceBall_indicator_heat_diagonal_lower_of_eigenvector (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (u : Lp ℝ 2 (dirichletVolume ρ R)) (eig : ℝ)
    (hu : inner ℝ u u = 1)
    (hcoord : ∀ n, (eigenvalue n - eig) * b.repr u n = 0) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eig * t) * (∫ x in sourceBall c r, u x ∂dirichletVolume ρ R) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  have hs : MeasurableSet (sourceBall c r) := by
    rw [← pde_ball_eq_sourceBall c hr]
    exact (PDE.isOpen_euclideanBall c r).measurableSet
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
  have hfinite : dirichletVolume ρ R (sourceBall c r) ≠ ∞ := measure_ne_top _ _
  have h := SpectralHeat.heatOperator_diagonal_lower_of_eigenvector b eigenvalue hpos t u
    (indicatorConstLp 2 hs hfinite (1 : ℝ)) eig hu
    (SpectralHeat.heatOperator_eigenvector_of_coordinates b eigenvalue hpos u eig hcoord t)
  rw [real_inner_comm (indicatorConstLp 2 hs hfinite (1 : ℝ)) u,
    L2.inner_indicatorConstLp_one] at h
  exact h

/-- A lower amplitude for an arbitrary normalized spectral eigenvector gives
an explicit same-ball diagonal estimate uniformly on a compact time interval. -/
theorem sourceBall_indicator_heat_diagonal_lower_eigenvector_on_interval (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (T : ℝ≥0) (u : Lp ℝ 2 (dirichletVolume ρ R)) (eig : ℝ)
    (heig : 0 ≤ eig) (hu : inner ℝ u u = 1)
    (hcoord : ∀ n, (eigenvalue n - eig) * b.repr u n = 0)
    (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ u x)
    (t : ℝ≥0) (ht : t ≤ T) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eig * T) * (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
  have hf : dirichletVolume ρ R (sourceBall c r) ≠ ∞ := measure_ne_top _ _
  have hm : a * (dirichletVolume ρ R).real (sourceBall c r) ≤
      ∫ x in sourceBall c r, u x ∂dirichletVolume ρ R := by
    have hconst : IntegrableOn (fun _ : Vec d => a) (sourceBall c r)
        (dirichletVolume ρ R) := integrableOn_const hf
    have h := integral_mono_ae hconst
      (integrableOn_Lp_of_measure_ne_top u fact_one_le_two_ennreal.elim hf) hamp
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using h
  have hn : 0 ≤ a * (dirichletVolume ρ R).real (sourceBall c r) :=
    mul_nonneg ha measureReal_nonneg
  have hsq := (sq_le_sq₀ hn (hn.trans hm)).2 hm
  have htime : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hexp : Real.exp (-eig * T) ≤ Real.exp (-eig * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [heig, htime]
  exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le).trans
      (sourceBall_indicator_heat_diagonal_lower_of_eigenvector ρ R hR C hρ c r hr b
        eigenvalue hpos t u eig hu hcoord))

/-- A normalized heat mode with a lower amplitude yields the same-ball
heat pairing bound uniformly on a compact time interval. -/
theorem sourceBall_indicator_heat_diagonal_lower_mode_on_interval (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (T : ℝ≥0) (u : Lp ℝ 2 (dirichletVolume ρ R)) (eig : ℝ)
    (heig : 0 ≤ eig) (hu : inner ℝ u u = 1)
    (hmode : ∀ t : ℝ≥0, SpectralHeat.heatOperator b eigenvalue hpos t u =
      Real.exp (-eig * t) • u)
    (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ u x)
    (t : ℝ≥0) (ht : t ≤ T) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eig * T) * (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
  have hs : MeasurableSet (sourceBall c r) := by
    rw [← pde_ball_eq_sourceBall c hr]
    exact (PDE.isOpen_euclideanBall c r).measurableSet
  have hf : dirichletVolume ρ R (sourceBall c r) ≠ ∞ := measure_ne_top _ _
  let v := indicatorConstLp 2 hs hf (1 : ℝ)
  have hm : a * (dirichletVolume ρ R).real (sourceBall c r) ≤
      ∫ x in sourceBall c r, u x ∂dirichletVolume ρ R := by
    have hconst : IntegrableOn (fun _ : Vec d => a) (sourceBall c r)
        (dirichletVolume ρ R) := integrableOn_const hf
    have h := integral_mono_ae hconst
      (integrableOn_Lp_of_measure_ne_top u fact_one_le_two_ennreal.elim hf) hamp
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using h
  have hn : 0 ≤ a * (dirichletVolume ρ R).real (sourceBall c r) :=
    mul_nonneg ha measureReal_nonneg
  have hsq := (sq_le_sq₀ hn (hn.trans hm)).2 hm
  have htime : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hexp : Real.exp (-eig * T) ≤ Real.exp (-eig * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [heig, htime]
  have hdiag := SpectralHeat.heatOperator_diagonal_lower_of_eigenvector b eigenvalue hpos t u
    v eig hu (hmode t)
  rw [real_inner_comm v u, L2.inner_indicatorConstLp_one] at hdiag
  exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)).trans
    ((mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le).trans hdiag)

#print axioms sourceBall_indicator_heat_diagonal_lower_mode_on_interval

/-- A normalized native weak eigenfunction with an interior lower bound
produces a genuine spectral heat pairing on that ball. -/
theorem exists_native_weakEigenfunction_heat_pairing {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (heig : 0 ≤ eig)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1)
    (c : Vec d) (r : ℝ) (hr : 0 < r) (a : ℝ) (ha : 0 ≤ a)
    (hlower : ∀ᵐ x ∂volume.restrict (sourceBall c r), a ≤ v.toH1Function.toFun x)
    (T : ℝ≥0) :
    ∃ (eigenvalue : ℕ → ℝ)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      ∀ t : ℝ≥0, t ≤ T →
        let hs : MeasurableSet (sourceBall c r) := by
          rw [← pde_ball_eq_sourceBall c hr]
          exact (PDE.isOpen_euclideanBall c r).measurableSet
        letI : IsFiniteMeasure (dirichletVolume ρ R) :=
          dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        let w := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
        Real.exp (-eig * T) * (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 ≤
          inner ℝ w (SpectralHeat.heatOperator b eigenvalue hpos t w) := by
  obtain ⟨eigenvalue, vs, b, hpos, _heig, _hb, u, hu, hmode⟩ :=
    exists_dirichletSpectralHeat_native_weakEigenfunction_mode hd hκ h R hR v eig hweak
  let f := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u
  have hf : inner ℝ f f = 1 := by
    rw [dirichletVolume_inner_self_eq_native hκ h R f v.toH1Function.toFun hu, hnorm]
  have hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ f x :=
    dirichletVolume_restrict_ae_lower_of_native ρ R f v.toH1Function.toFun hu
      (sourceBall c r) a hlower
  refine ⟨eigenvalue, b, hpos, ?_⟩
  intro t ht
  exact sourceBall_indicator_heat_diagonal_lower_mode_on_interval ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) c r hr b eigenvalue hpos T f eig heig hf hmode
    a ha hamp t ht

#print axioms exists_native_weakEigenfunction_heat_pairing

/-- An almost-everywhere lower amplitude on the same weighted ball gives
an explicit lower bound for its diagonal spectral heat pairing. -/
theorem sourceBall_indicator_heat_diagonal_lower_of_ae (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (j : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ b j x) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eigenvalue j * t) *
        (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
  have hf : dirichletVolume ρ R (sourceBall c r) ≠ ∞ := measure_ne_top _ _
  have hm : a * (dirichletVolume ρ R).real (sourceBall c r) ≤
      ∫ x in sourceBall c r, b j x ∂dirichletVolume ρ R := by
    have hconst : IntegrableOn (fun _ : Vec d => a) (sourceBall c r)
        (dirichletVolume ρ R) := integrableOn_const hf
    have h := integral_mono_ae hconst
      (integrableOn_Lp_of_measure_ne_top (b j) fact_one_le_two_ennreal.elim hf) hamp
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using h
  have hnonneg : 0 ≤ a * (dirichletVolume ρ R).real (sourceBall c r) :=
    mul_nonneg ha measureReal_nonneg
  have hsq := (sq_le_sq₀ hnonneg (hnonneg.trans hm)).2 hm
  exact (mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le).trans
    (sourceBall_indicator_heat_diagonal_lower ρ R hR C hρ c r hr b eigenvalue hpos t j)

/-- A single same-ball lower amplitude gives a diagonal heat bound uniformly
for all nonnegative times up to `T`. The eigenvalue and weighted ball mass
remain explicit; this does not supply the lower amplitude. -/
theorem sourceBall_indicator_heat_diagonal_lower_on_interval (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (T : ℝ≥0) (j : ℕ) (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ b j x)
    (t : ℝ≥0) (ht : t ≤ T) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hρ
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-eigenvalue j * T) *
        (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  have htime : (t : ℝ) ≤ T := by exact_mod_cast ht
  have hexp : Real.exp (-eigenvalue j * T) ≤ Real.exp (-eigenvalue j * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hpos j, htime]
  exact (mul_le_mul_of_nonneg_right hexp (sq_nonneg _)).trans
    (sourceBall_indicator_heat_diagonal_lower_of_ae ρ R hR C hρ c r hr b
      eigenvalue hpos t j a ha hamp)

/-- A uniform lower density on the containing ball bounds the actual
weighted mass of an interior ball below by its Euclidean volume. -/
theorem sourceBall_dirichletVolume_real_lower (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C κ : ℝ) (hκ : 0 ≤ κ)
    (hupper : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (hlower : ∀ x ∈ sourceBall (0 : Vec d) R, κ ≤ ρ x)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (hsub : sourceBall c r ⊆ sourceBall (0 : Vec d) R) :
    κ * volume.real (sourceBall c r) ≤
      (dirichletVolume ρ R).real (sourceBall c r) := by
  have hs : MeasurableSet (sourceBall (0 : Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hball : MeasurableSet (sourceBall c r) := by
    rw [← pde_ball_eq_sourceBall c hr]
    exact (PDE.isOpen_euclideanBall c r).measurableSet
  have hmeasure : ENNReal.ofReal κ • volume.restrict (sourceBall (0 : Vec d) R) ≤
      dirichletVolume ρ R := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hlower x hx)
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR C hupper
  have h := ENNReal.toReal_mono (measure_ne_top (dirichletVolume ρ R) _)
    (hmeasure (sourceBall c r))
  simpa only [Measure.real, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hball, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] using h

/-- Uniform same-ball heat pairing with the density and eigenvalue bounds
displayed explicitly. The amplitude and eigenvalue bounds are inputs to this
analytic estimate, not consequences of normalization. -/
theorem sourceBall_indicator_heat_diagonal_lower_of_bounds (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C κ : ℝ) (hκ : 0 ≤ κ)
    (hupper : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (hlower : ∀ x ∈ sourceBall (0 : Vec d) R, κ ≤ ρ x)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (hsub : sourceBall c r ⊆ sourceBall (0 : Vec d) R)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (T : ℝ≥0) (j : ℕ) (L : ℝ) (hL : eigenvalue j ≤ L)
    (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ b j x)
    (t : ℝ≥0) (ht : t ≤ T) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hupper
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-L * T) * (a * (κ * volume.real (sourceBall c r))) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  have hm := sourceBall_dirichletVolume_real_lower ρ R hR C κ hκ
    hupper hlower c r hr hsub
  have hmass := mul_le_mul_of_nonneg_left hm ha
  have hn : 0 ≤ a * (κ * volume.real (sourceBall c r)) :=
    mul_nonneg ha (mul_nonneg hκ measureReal_nonneg)
  have hsq := (sq_le_sq₀ hn (hn.trans hmass)).2 hmass
  have hexp : Real.exp (-L * T) ≤ Real.exp (-eigenvalue j * T) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hL, T.coe_nonneg]
  calc
    _ ≤ Real.exp (-eigenvalue j * T) *
        (a * (dirichletVolume ρ R).real (sourceBall c r)) ^ 2 :=
      mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le
    _ ≤ _ := sourceBall_indicator_heat_diagonal_lower_on_interval ρ R hR C hupper
      c r hr b eigenvalue hpos T j a ha hamp t ht

/-- Euclidean source-ball volume has the exact radius-to-dimension scaling. -/
theorem sourceBall_volume_real_eq_unit_mul (c : Vec d) (r : ℝ) (hr : 0 < r) :
    volume.real (sourceBall c r) =
      r ^ d * volume.real (sourceBall (0 : Vec d) 1) := by
  rw [← pde_ball_eq_sourceBall c hr,
    ← pde_ball_eq_sourceBall (0 : Vec d) (by norm_num)]
  exact PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos c hr

/-- A normalized native weak eigenfunction with a structural eigenvalue
bound and an interior amplitude yields a radius-scaled heat pairing. -/
theorem exists_native_weakEigenfunction_heat_pairing_scaled {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig E : ℝ)
    (heig : 0 ≤ eig) (hE : eig ≤ E)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (hsub : sourceBall c r ⊆ sourceBall (0 : Vec d) R)
    (a : ℝ) (ha : 0 ≤ a)
    (hlower : ∀ᵐ x ∂volume.restrict (sourceBall c r), a ≤ v.toH1Function.toFun x)
    (T : ℝ≥0) :
    ∃ (eigenvalue : ℕ → ℝ)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      ∀ t : ℝ≥0, t ≤ T →
        let hs : MeasurableSet (sourceBall c r) := by
          rw [← pde_ball_eq_sourceBall c hr]
          exact (PDE.isOpen_euclideanBall c r).measurableSet
        letI : IsFiniteMeasure (dirichletVolume ρ R) :=
          dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        let w := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
        Real.exp (-E * T) *
            (a * (κ * (r ^ d * volume.real (sourceBall (0 : Vec d) 1)))) ^ 2 ≤
          inner ℝ w (SpectralHeat.heatOperator b eigenvalue hpos t w) := by
  obtain ⟨eigenvalue, b, hpos, hpair⟩ :=
    exists_native_weakEigenfunction_heat_pairing hd hκ h R hR v eig heig hweak
      hnorm c r hr a ha hlower T
  have hm := sourceBall_dirichletVolume_real_lower ρ R hR κ⁻¹ κ hκ.le
    (fun x _ => (h.2.2 x).2.1) (fun x _ => (h.2.2 x).1) c r hr hsub
  rw [sourceBall_volume_real_eq_unit_mul c r hr] at hm
  have hmass := mul_le_mul_of_nonneg_left hm ha
  have hn : 0 ≤ a * (κ * (r ^ d * volume.real (sourceBall (0 : Vec d) 1))) :=
    mul_nonneg ha (mul_nonneg hκ.le (mul_nonneg (pow_nonneg hr.le _) measureReal_nonneg))
  have hsq := (sq_le_sq₀ hn (hn.trans hmass)).2 hmass
  have hexp : Real.exp (-E * T) ≤ Real.exp (-eig * T) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hE, T.coe_nonneg]
  refine ⟨eigenvalue, b, hpos, ?_⟩
  intro t ht
  exact (mul_le_mul hexp hsq (sq_nonneg _) (Real.exp_pos _).le).trans (hpair t ht)

#print axioms exists_native_weakEigenfunction_heat_pairing_scaled

/-- The scaled same-ball estimate also controls the inner product of two
heat evolutions, with the two times constrained by their sum. -/
theorem exists_native_weakEigenfunction_heat_pairing_two_times_scaled {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig E : ℝ)
    (heig : 0 ≤ eig) (hE : eig ≤ E)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (hsub : sourceBall c r ⊆ sourceBall (0 : Vec d) R)
    (a : ℝ) (ha : 0 ≤ a)
    (hlower : ∀ᵐ x ∂volume.restrict (sourceBall c r), a ≤ v.toH1Function.toFun x)
    (T : ℝ≥0) :
    ∃ (eigenvalue : ℕ → ℝ)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      ∀ s t : ℝ≥0, s + t ≤ T →
        let hs : MeasurableSet (sourceBall c r) := by
          rw [← pde_ball_eq_sourceBall c hr]
          exact (PDE.isOpen_euclideanBall c r).measurableSet
        letI : IsFiniteMeasure (dirichletVolume ρ R) :=
          dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        let w := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
        Real.exp (-E * T) *
            (a * (κ * (r ^ d * volume.real (sourceBall (0 : Vec d) 1)))) ^ 2 ≤
          inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos s w)
            (SpectralHeat.heatOperator b eigenvalue hpos t w) := by
  obtain ⟨eigenvalue, b, hpos, hpair⟩ :=
    exists_native_weakEigenfunction_heat_pairing_scaled hd hκ h R hR v eig E
      heig hE hweak hnorm c r hr hsub a ha hlower T
  refine ⟨eigenvalue, b, hpos, ?_⟩
  intro s t hst
  have hp := hpair (s + t) hst
  simpa only [SpectralHeat.heatOperator_add, ContinuousLinearMap.comp_apply,
    ← SpectralHeat.heatOperator_symmetric] using hp

#print axioms exists_native_weakEigenfunction_heat_pairing_two_times_scaled

/-- The same-ball diagonal heat estimate with the radius scaling of the
Euclidean volume made explicit. The eigenvalue and amplitude bounds remain
inputs to this estimate. -/
theorem sourceBall_indicator_heat_diagonal_lower_of_bounds_scaled (ρ : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C κ : ℝ) (hκ : 0 ≤ κ)
    (hupper : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (hlower : ∀ x ∈ sourceBall (0 : Vec d) R, κ ≤ ρ x)
    (c : Vec d) (r : ℝ) (hr : 0 < r)
    (hsub : sourceBall c r ⊆ sourceBall (0 : Vec d) R)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (T : ℝ≥0) (j : ℕ) (L : ℝ) (hL : eigenvalue j ≤ L)
    (a : ℝ) (ha : 0 ≤ a)
    (hamp : ∀ᵐ x ∂(dirichletVolume ρ R).restrict (sourceBall c r), a ≤ b j x)
    (t : ℝ≥0) (ht : t ≤ T) :
    let hs : MeasurableSet (sourceBall c r) := by
      rw [← pde_ball_eq_sourceBall c hr]
      exact (PDE.isOpen_euclideanBall c r).measurableSet
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR C hupper
    let v := indicatorConstLp 2 hs (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
    Real.exp (-L * T) *
        (a * (κ * (r ^ d * volume.real (sourceBall (0 : Vec d) 1)))) ^ 2 ≤
      inner ℝ v (SpectralHeat.heatOperator b eigenvalue hpos t v) := by
  simpa only [sourceBall_volume_real_eq_unit_mul c r hr] using
    sourceBall_indicator_heat_diagonal_lower_of_bounds ρ R hR C κ hκ hupper hlower
      c r hr hsub b eigenvalue hpos T j L hL a ha hamp t ht


/-- Continuous restriction of the cube coordinate classes to the actual source ball. -/
noncomputable def sourceBallL2Restriction {d : ℕ} (R : ℝ) (hR : 0 < R) :
    DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR))
      →L[ℝ] DomainL2 (dirichletBall (d := d) R) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by
    rw [one_smul]
    apply Measure.restrict_mono_set
    exact sourceBall_subset_cube R hR)

/-- Restriction keeps the original cube representative almost everywhere. -/
theorem sourceBallL2Restriction_coe {d : ℕ} (R : ℝ) (hR : 0 < R)
    (f : DomainL2 (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR))) :
    (sourceBallL2Restriction R hR f : SpatialCoordinates d → ℝ)
      =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] f := by
  exact Lp.coeFn_LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (show volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d)) ≤
        1 • volume.restrict (centeredCube (0 : SpatialCoordinates d) (2 * R)
          (mul_pos two_pos hR) : Set (SpatialCoordinates d)) by
      rw [one_smul]
      apply Measure.restrict_mono_set
      exact sourceBall_subset_cube R hR) f

/-- The value and all coordinate gradients, restricted to the source ball. -/
noncomputable def dirichletHilbertBallData {d : ℕ} (R : ℝ) (hR : 0 < R) :
    HilbertSobolevData (centeredCube (0 : SpatialCoordinates d) (2 * R)
      (mul_pos two_pos hR)) →L[ℝ] SobolevData (dirichletBall (d := d) R) :=
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let L := sourceBallL2Restriction (d := d) R hR
  ((L.comp (ContinuousLinearMap.fst ℝ (DomainL2 Q) (Fin d → DomainL2 Q))).prod
    (ContinuousLinearMap.pi fun i : Fin d =>
      L.comp ((ContinuousLinearMap.proj i).comp
        (ContinuousLinearMap.snd ℝ (DomainL2 Q) (Fin d → DomainL2 Q))))).comp
      (hilbertToSobolev Q)

/-- Restriction preserves the closure of smooth ball-supported data, including
its zero trace on the ball itself. -/
theorem dirichletHilbertBallData_mem_killedSobolevGraph {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR) :
    dirichletHilbertBallData R hR u.val ∈ killedSobolevGraph (dirichletBall R) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let L := sourceBallL2Restriction (d := d) R hR
  let F := dirichletHilbertBallData (d := d) R hR
  have hrep (f : DomainL2 Q) :
      (L f : SpatialCoordinates d → ℝ) =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] f :=
    sourceBallL2Restriction_coe R hR f
  have hmap (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤) :
      F (dirichletSmoothData R hR φ) = smoothSobolevData φ := by
    apply Prod.ext
    · change L (testL2 (dirichletTestInCube R hR φ)) = testL2 φ
      apply Lp.ext
      have ht : (testL2 (dirichletTestInCube R hR φ) : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] φ :=
        ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR)
          (testL2_coeFn (dirichletTestInCube R hR φ))
      filter_upwards [hrep (testL2 (dirichletTestInCube R hR φ)), ht,
        testL2_coeFn φ] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
    · funext i
      change L (testPartialL2 (dirichletTestInCube R hR φ) i) = testPartialL2 φ i
      apply Lp.ext
      have ht : (testPartialL2 (dirichletTestInCube R hR φ) i : SpatialCoordinates d → ℝ)
          =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
            (fun x => fderiv ℝ φ x (Pi.single i 1)) :=
        ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR)
          (testPartialL2_coeFn (dirichletTestInCube R hR φ) i)
      filter_upwards [hrep (testPartialL2 (dirichletTestInCube R hR φ) i), ht,
        testPartialL2_coeFn φ i] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
  have hc : IsClosed ((killedSobolevGraph (dirichletBall (d := d) R)).comap
      F.toLinearMap : Set (HilbertSobolevData Q)) :=
    isClosed_killedSobolevGraph.preimage F.continuous
  have hrange : LinearMap.range (dirichletSmoothData R hR) ≤
      (killedSobolevGraph (dirichletBall R)).comap F.toLinearMap := by
    rintro _ ⟨φ, rfl⟩
    apply Submodule.mem_comap.mpr
    rw [show F.toLinearMap (dirichletSmoothData R hR φ) = smoothSobolevData φ from hmap φ]
    exact smoothSobolevData_mem_killed φ
  exact (Submodule.topologicalClosure_minimal _ hrange hc) u.property

/-- Every vector in the completed source-ball energy space has an actual native
H10 representative on that same ball, preserving values and gradients a.e. -/
theorem exists_nativeH10_of_dirichletHilbert {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ v : Homogenization.H10Function
        (EinsteinFull.External.Source.GMP.sourceBall (0 : EinsteinRelation.Vec d) R),
      v.toH1Function.toFun =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))]
        (fun x => u.val none x) ∧
      ∀ i : Fin d, (fun x => v.toH1Function.grad x i)
        =ᵐ[volume.restrict (dirichletBall (d := d) R : Set (SpatialCoordinates d))] (fun x => u.val (some i) x) := by
  obtain ⟨v, hv, hg⟩ := exists_nativeH10Function_of_killedSobolevGraph
    ⟨dirichletHilbertBallData R hR u.val,
      dirichletHilbertBallData_mem_killedSobolevGraph R hR u⟩
  refine ⟨v, ?_, ?_⟩
  · rw [show v.toH1Function.toFun = _ from hv]
    exact sourceBallL2Restriction_coe R hR (u.val none)
  · intro i
    rw [hg]
    exact sourceBallL2Restriction_coe R hR (u.val (some i))


/-- A normalized native weak eigenfunction has a nonzero coordinate in the
actual Dirichlet eigenbasis, and every nonzero coordinate has its eigenvalue. -/
theorem native_weakEigenfunction_spectral_coordinate {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u :
        Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      (∃ n, b.repr (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u) n ≠ 0) ∧
      ∀ n, eigenvalue n ≠ eig → b.repr (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u) n = 0 := by
  obtain ⟨u, hu, hvaru⟩ := exists_dirichletHilbert_weakEquation_of_native_smooth
    hd hκ h R hR v eig (native_weakEigenEquation_on_smooth R v eig hweak)
  let f := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u
  have hf : inner ℝ f f = 1 := by
    rw [dirichletVolume_inner_self_eq_native hκ h R f v.toH1Function.toFun hu, hnorm]
  have hne : f ≠ 0 := by
    intro hf0
    rw [hf0, inner_zero_left] at hf
    norm_num at hf
  have hc := dirichletHilbert_eigenfunction_coordinates h R hR eigenvalue vs b hb hvar u eig hvaru
  refine ⟨u, hu, ?_, ?_⟩
  · by_contra hn
    push Not at hn
    apply hne
    apply b.repr.injective
    ext n
    simp only [map_zero]
    exact hn n
  · intro n hn
    exact (mul_eq_zero.mp (hc n)).resolve_left (sub_ne_zero.mpr hn)

#print axioms native_weakEigenfunction_spectral_coordinate

/-- A native all-vector Rayleigh bound also bounds each actual spectral value. -/
theorem native_rayleigh_lower_le_spectral_value {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (eig : ℝ)
    (hmin : ∀ v : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      eig * (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) :
    ∀ n, eig ≤ eigenvalue n := by
  intro n
  obtain ⟨v, hv, hg⟩ := exists_nativeH10_of_dirichletHilbert R hR (vs n)
  have hvw : (b n : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun := by
    rw [hb]
    have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n), hac.ae_le hv] with x hx hy
    exact hx.trans hy.symm
  have hself : inner ℝ (b n) (b n) = 1 := by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one n]
    norm_num
  have hmass : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1 := by
    rw [← dirichletVolume_inner_self_eq_native hκ h R (b n) v.toH1Function.toFun hvw, hself]
  have henergy : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) = eigenvalue n := by
    calc
      _ = ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (vs n).val (some i) x))
            (fun i => (vs n).val (some i) x) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hg] with x hx
        rw [show v.toH1Function.grad x = (fun i => (vs n).val (some i) x) from funext hx]
      _ = _ := by rw [hvar n, ← hb, hself, mul_one]
  have hh := hmin v
  rw [hmass, henergy, mul_one] at hh
  exact hh

#print axioms native_rayleigh_lower_le_spectral_value


/-- The actual heat rescaling uses the native Rayleigh minimum, and the native
minimizer is supported on the complete lowest eigenspace. -/
theorem native_rayleigh_minimum_rescaled_heat_projection {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hnorm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1)
    (hmin : ∀ w : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      eig * (∫ x in sourceBall (0 : Vec d) R,
        ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (S : Finset ℕ)
      (u : DirichletHilbertSpace (d := d) R hR),
      0 < δ ∧ eigenvalue j = eig ∧ (∀ n, eig ≤ eigenvalue n) ∧
      (∀ n, 0 < eigenvalue n) ∧ (∀ n, b n = J (vs n)) ∧
      (∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (vs n).val (some i) x))
            (fun i => w.val (some i) x)) = eigenvalue n * inner ℝ (J (vs n)) (J w)) ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eig) ∧
      (J u : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      (∃ n, b.repr (J u) n ≠ 0) ∧
      (∀ n, n ∉ S → b.repr (J u) n = 0) ∧
      (∀ t : ℝ≥0, ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        ‖Real.exp (eig * t) • SpectralHeat.heatOperator b eigenvalue hpos t f -
          ∑ n ∈ S, b.repr f n • b n‖ ≤ Real.exp (-δ * t) * ‖f‖) ∧
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        Tendsto (fun t : ℝ≥0 => Real.exp (eig * t) •
          SpectralHeat.heatOperator b eigenvalue hpos t f) atTop
          (𝓝 (∑ n ∈ S, b.repr f n • b n)) := by
  dsimp only
  obtain ⟨eigenvalue, vs, b, hpos, j, δ, S, hδ, hp, hb, hj, hS, hvar, htail, hlimit⟩ :=
    exists_dirichletHilbert_rescaled_heat_tendsto_lowest_projection hd hκ h R hR
  have hvarb (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w) := by
    rw [hb]
    exact hvar n w
  obtain ⟨u, hu, ⟨n, hn⟩, hsupport⟩ :=
    native_weakEigenfunction_spectral_coordinate hd hκ h R hR eigenvalue vs b hb hvarb
      v eig hweak hnorm
  have heq : eigenvalue n = eig := by
    by_contra hne
    exact hn (hsupport n hne)
  have hlower := native_rayleigh_lower_le_spectral_value hκ h R hR eigenvalue vs b hb hvarb eig hmin
  have hjeq : eigenvalue j = eig := le_antisymm ((hj n).trans_eq heq) (hlower j)
  refine ⟨eigenvalue, vs, b, hpos, j, δ, S, u, hδ, hjeq, hlower, hp, hb, hvar, ?_, hu,
    ⟨n, hn⟩, ?_, ?_, ?_⟩
  · intro k
    simpa only [hjeq] using hS k
  · intro k hk
    apply hsupport k
    intro he
    exact hk ((hS k).2 (he.trans hjeq.symm))
  · simpa only [hjeq] using htail
  · simpa only [hjeq] using hlimit

#print axioms native_rayleigh_minimum_rescaled_heat_projection

/-- A finite spectral projection has a completed energy representative, with
its actual weighted inclusion and variational equation. Multiplicity and the
zero projection are both allowed. -/
theorem finite_spectral_projection_dirichletHilbert {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (hS : ∀ n ∈ S, eigenvalue n = eig)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      J u = ∑ n ∈ S, b.repr f n • b n ∧
      ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) = eig * inner ℝ (J u) (J w) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let u : DirichletHilbertSpace (d := d) R hR := ∑ n ∈ S, b.repr f n • vs n
  have hJu : J u = ∑ n ∈ S, b.repr f n • b n := by
    simp only [u, map_sum, map_smul]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hb n]
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨u, hJu, ?_⟩
  intro w
  rw [← hB, hJu]
  change B (∑ n ∈ S, b.repr f n • vs n) w = _
  simp only [map_sum, map_smul, sum_apply,
    smul_apply, sum_inner, real_inner_smul_left]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hB, hvar, hS n hn]
  simp only [smul_eq_mul]
  ring

#print axioms finite_spectral_projection_dirichletHilbert

/-- Weighted inner products agree with the source-ball product integral for
any two almost-everywhere native representatives. -/
theorem dirichletVolume_inner_eq_native {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (f g : Lp ℝ 2 (dirichletVolume ρ R)) (u v : Vec d → ℝ)
    (hu : (f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u)
    (hv : (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v) :
    inner ℝ f g = ∫ x in sourceBall (0 : Vec d) R, ρ x * u x * v x := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, u x * v x ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [hu, hv] with x hx hy
      simp only [RCLike.inner_apply, conj_trivial, hx, hy, mul_comm]
    _ = _ := by
      change (∫ x, u x * v x ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
        (fun x => ENNReal.ofReal (ρ x))) = _
      rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by
        dsimp only
        rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
        ring

#print axioms dirichletVolume_inner_eq_native

/-- The complete finite spectral projection is represented by an actual native
H10 weak eigenmode, including the zero mode. -/
theorem finite_spectral_projection_native {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (hS : ∀ n ∈ S, eigenvalue n = eig)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ∃ v : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      ((∑ n ∈ S, b.repr f n • b n : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨u, hu, hweak⟩ := finite_spectral_projection_dirichletHilbert
    hd hκ h R hR eigenvalue vs b hb hvar S eig hS f
  obtain ⟨v, hv, hg⟩ := exists_nativeH10_of_dirichletHilbert R hR u
  have hvw : (J u : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun := by
    have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) u, hac.ae_le hv] with x hx hy
    exact hx.trans hy.symm
  refine ⟨v, ?_, ?_⟩
  · rw [← hu]
    exact hvw
  · intro φ
    obtain ⟨w, hw, hwg⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) φ
    have he := hweak w
    rw [dirichletVolume_inner_eq_native hκ h R (J u) (J w)
      v.toH1Function.toFun φ.toH1Function.toFun hvw hw] at he
    have hegrad : (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x)) =
        ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (v.toH1Function.grad x)) (φ.toH1Function.grad x) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hg, ae_all_iff.mpr hwg] with x hx hy
      rw [show (fun i => u.val (some i) x) = v.toH1Function.grad x from (funext hx).symm,
        show (fun i => w.val (some i) x) = φ.toH1Function.grad x from funext hy]
    rw [hegrad] at he
    simpa only [SuperdiffusionCLT.Section7.IsWeakSolutionOn, Homogenization.vecDot,
      Homogenization.matVecMul, Matrix.mulVec, dotProduct, dot,
      Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero, integral_const_mul,
      mul_assoc] using he

#print axioms finite_spectral_projection_native

/-- Testing a native weak eigenmode against itself gives its exact Rayleigh
energy identity, also when the mode is zero. -/
theorem native_weakEigenfunction_energy_eq {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} (R eig : ℝ)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) =
      eig * ∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x := by
  have he := hweak v
  simpa only [Homogenization.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    integral_zero, add_zero, Homogenization.matVecMul, Matrix.mulVec, dotProduct, dot,
    integral_const_mul, mul_assoc] using he

#print axioms native_weakEigenfunction_energy_eq


/-- A represented native weak eigenmode has the exact weighted mass and energy
of its spectral representative, including the zero representative. -/
theorem native_weakEigenfunction_mass_energy {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R eig : ℝ) (p : Lp ℝ 2 (dirichletVolume ρ R))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hv : (p : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = ‖p‖ ^ 2 ∧
    (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) =
      eig * ‖p‖ ^ 2 := by
  have hm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = ‖p‖ ^ 2 := by
    rw [← dirichletVolume_inner_self_eq_native hκ h R p v.toH1Function.toFun hv,
      real_inner_self_eq_norm_sq]
  exact ⟨hm, (native_weakEigenfunction_energy_eq R eig v hweak).trans (congrArg (eig * ·) hm)⟩

#print axioms native_weakEigenfunction_mass_energy


/-- Scalar multiples of native weak eigenfunctions remain weak eigenfunctions. -/
theorem native_weakEigenfunction_smul {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} (R eig c : ℝ)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      (c • v).toH1Function
      (fun x => eig * ρ x * (c • v).toH1Function.toFun x) (fun _ => 0) := by
  intro φ
  have he := hweak φ
  have hl : ∀ x, Homogenization.vecDot
      (Homogenization.matVecMul (α x) ((c • v).toH1Function.grad x))
      (φ.toH1Function.grad x) =
      c * Homogenization.vecDot (Homogenization.matVecMul (α x) (v.toH1Function.grad x))
        (φ.toH1Function.grad x) := by
    intro x
    change (∑ i, (∑ j, α x i j * (c * v.toH1Function.grad x j)) *
      φ.toH1Function.grad x i) = c * ∑ i,
        (∑ j, α x i j * v.toH1Function.grad x j) * φ.toH1Function.grad x i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hh : (∑ j, α x i j * (c * v.toH1Function.grad x j)) =
        c * ∑ j, α x i j * v.toH1Function.grad x j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hh]
    ring
  have hr : (∫ x in sourceBall (0 : Vec d) R,
      (eig * ρ x * (c • v).toH1Function.toFun x) * φ.toH1Function.toFun x) =
      c * ∫ x in sourceBall (0 : Vec d) R,
        (eig * ρ x * v.toH1Function.toFun x) * φ.toH1Function.toFun x := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change eig * ρ x * (c * v.toH1Function.toFun x) * φ.toH1Function.toFun x = _
    ring
  simp only [hl, integral_const_mul, hr]
  simp only [Homogenization.vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero,
    integral_zero, add_zero] at he ⊢
  rw [he]

#print axioms native_weakEigenfunction_smul


/-- A nonzero weighted representative yields a normalized native eigenmode. -/
theorem native_weakEigenfunction_normalize {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R eig : ℝ) (p : Lp ℝ 2 (dirichletVolume ρ R))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hv : (p : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hp : p ≠ 0) :
    ∃ v₀ : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      (((‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v₀.toH1Function.toFun) ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v₀.toH1Function (fun x => eig * ρ x * v₀.toH1Function.toFun x) (fun _ => 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v₀.toH1Function.toFun x * v₀.toH1Function.toFun x) = 1 ∧
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v₀.toH1Function.grad x)) (v₀.toH1Function.grad x)) = eig := by
  let v₀ := ‖p‖⁻¹ • v
  have hrep : (((‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ)
      =ᵐ[dirichletVolume ρ R] v₀.toH1Function.toFun) := by
    filter_upwards [Lp.coeFn_smul ‖p‖⁻¹ p, hv] with x hx hy
    change (‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R)) x =
      ‖p‖⁻¹ * v.toH1Function.toFun x
    simpa only [Pi.smul_apply, smul_eq_mul, hy] using hx
  have hweak₀ := native_weakEigenfunction_smul R eig ‖p‖⁻¹ v hweak
  have hn : ‖(‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R))‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg p)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hp)]
  have hm := native_weakEigenfunction_mass_energy hκ h R eig (‖p‖⁻¹ • p) v₀ hrep hweak₀
  refine ⟨v₀, hrep, hweak₀, ?_, ?_⟩
  · simpa only [hn, one_pow] using hm.1
  · simpa only [hn, one_pow, mul_one] using hm.2

#print axioms native_weakEigenfunction_normalize


/-- Every finite equal-eigenvalue projection has its native mass and energy;
if nonzero it also determines a normalized native weak eigenmode. -/
theorem finite_spectral_projection_zero_or_normalized_native {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (hS : ∀ n ∈ S, eigenvalue n = eig)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    let p : Lp ℝ 2 (dirichletVolume ρ R) := ∑ n ∈ S, b.repr f n • b n
    ∃ v : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      (p : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = ‖p‖ ^ 2 ∧
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) =
        eig * ‖p‖ ^ 2 ∧
      (p = 0 ∨ ∃ v₀ : Homogenization.H10Function (sourceBall (0 : Vec d) R),
        ((‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ)
          =ᵐ[dirichletVolume ρ R] v₀.toH1Function.toFun ∧
        SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
          v₀.toH1Function (fun x => eig * ρ x * v₀.toH1Function.toFun x) (fun _ => 0) ∧
        (∫ x in sourceBall (0 : Vec d) R,
          ρ x * v₀.toH1Function.toFun x * v₀.toH1Function.toFun x) = 1 ∧
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (v₀.toH1Function.grad x)) (v₀.toH1Function.grad x)) = eig) := by
  dsimp only
  obtain ⟨v, hv, hw⟩ := finite_spectral_projection_native hd hκ h R hR
    eigenvalue vs b hb hvar S eig hS f
  have hm := native_weakEigenfunction_mass_energy hκ h R eig _ v hv hw
  refine ⟨v, hv, hw, hm.1, hm.2, ?_⟩
  by_cases hp : (∑ n ∈ S, b.repr f n • b n : Lp ℝ 2 (dirichletVolume ρ R)) = 0
  · exact Or.inl hp
  · exact Or.inr (native_weakEigenfunction_normalize hκ h R eig _ v hv hw hp)

#print axioms finite_spectral_projection_zero_or_normalized_native


/-- Normalization preserves the already established native Rayleigh minimum. -/
theorem native_weakEigenfunction_normalize_at_minimum {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R eig : ℝ) (p : Lp ℝ 2 (dirichletVolume ρ R))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hv : (p : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
      v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0))
    (hp : p ≠ 0)
    (hmin : ∀ w : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      eig * (∫ x in sourceBall (0 : Vec d) R,
        ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x)) :
    ∃ v₀ : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      (((‖p‖⁻¹ • p : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ)
        =ᵐ[dirichletVolume ρ R] v₀.toH1Function.toFun) ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v₀.toH1Function (fun x => eig * ρ x * v₀.toH1Function.toFun x) (fun _ => 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v₀.toH1Function.toFun x * v₀.toH1Function.toFun x) = 1 ∧
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v₀.toH1Function.grad x)) (v₀.toH1Function.grad x)) = eig ∧
      ∀ w : Homogenization.H10Function (sourceBall (0 : Vec d) R),
        eig * (∫ x in sourceBall (0 : Vec d) R,
          ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
        ∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x) := by
  obtain ⟨v₀, hrep, hw, hm, he⟩ :=
    native_weakEigenfunction_normalize hκ h R eig p v hv hweak hp
  exact ⟨v₀, hrep, hw, hm, he, hmin⟩

#print axioms native_weakEigenfunction_normalize_at_minimum

/-- Every native weak mode has a weighted representative supported on its
actual eigenspace, including the zero mode. -/
theorem native_weakEigenfunction_spectral_support {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)) (eig : ℝ)
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    ∃ u : DirichletHilbertSpace (d := d) R hR,
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u :
        Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      ∀ n, eigenvalue n ≠ eig → b.repr (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u) n = 0 := by
  obtain ⟨u, hu, hvaru⟩ := exists_dirichletHilbert_weakEquation_of_native_smooth
    hd hκ h R hR v eig (native_weakEigenEquation_on_smooth R v eig hweak)
  have hc := dirichletHilbert_eigenfunction_coordinates h R hR eigenvalue vs b hb hvar u eig hvaru
  exact ⟨u, hu, fun n hn => (mul_eq_zero.mp (hc n)).resolve_left (sub_ne_zero.mpr hn)⟩

#print axioms native_weakEigenfunction_spectral_support

/-- A vector supported on a finite set of basis coordinates is its complete
finite spectral projection. -/
theorem finite_spectral_projection_eq_of_support {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (b : HilbertBasis ℕ ℝ E)
    (S : Finset ℕ) (f : E) (hs : ∀ n, n ∉ S → b.repr f n = 0) :
    f = ∑ n ∈ S, b.repr f n • b n := by
  apply b.repr.injective
  apply lp.ext
  funext n
  simp only [map_sum, map_smul, b.repr_self, lp.coeFn_smul, Pi.smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.single_apply, smul_eq_mul]
  by_cases hn : n ∈ S
  · rw [Finset.sum_eq_single n]
    · simp
    · intro x _ hxn
      simp [hxn]
    · exact fun h => (h hn).elim
  · rw [hs n hn]
    symm
    apply Finset.sum_eq_zero
    intro x hx
    have hxn : x ≠ n := fun h => hn (h ▸ hx)
    simp [hxn]

#print axioms finite_spectral_projection_eq_of_support

/-- An arbitrary native weak mode is exactly the complete finite projection
of its weighted representative onto the actual eigenspace. -/
theorem native_weakEigenfunction_eq_finite_spectral_projection {d : ℕ}
    (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (S : Finset ℕ) (eig : ℝ) (hS : ∀ n, n ∈ S ↔ eigenvalue n = eig)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hweak : SuperdiffusionCLT.Section7.IsWeakSolutionOn α
      (sourceBall (0 : Vec d) R) v.toH1Function
      (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0)) :
    ∃ g : Lp ℝ 2 (dirichletVolume ρ R),
      (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun ∧
      g = ∑ n ∈ S, b.repr g n • b n ∧
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (w : Vec d → ℝ),
        (f : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] w →
        inner ℝ g f = ∫ x in sourceBall (0 : Vec d) R,
          ρ x * v.toH1Function.toFun x * w x := by
  obtain ⟨u, hu, hs⟩ := native_weakEigenfunction_spectral_support
    hd hκ h R hR eigenvalue vs b hb hvar v eig hweak
  let g := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u
  refine ⟨g, hu, finite_spectral_projection_eq_of_support b S g ?_, ?_⟩
  · intro n hn
    exact hs n (fun he => hn ((hS n).2 he))
  · intro f w hw
    exact dirichletVolume_inner_eq_native hκ h R g f v.toH1Function.toFun w hu hw

#print axioms native_weakEigenfunction_eq_finite_spectral_projection


/-- Transport a zero-boundary representative to the PDE truncation API. -/
def nativeH10ToPDE {d : ℕ} {U : Set (Vec d)} (v : Homogenization.H10Function U) :
    PDE.H10Function U where
  toH1Function := ⟨v.toH1Function.toFun, v.toH1Function.grad, v.toH1Function.memL2,
    v.toH1Function.gradMemL2, v.toH1Function.hasWeakGradient⟩
  approx := v.approx
  approx_smooth := v.approx_smooth
  approx_hasCompactSupport := v.approx_hasCompactSupport
  approx_support_subset := v.approx_support_subset
  tendsto_approx := v.tendsto_approx
  tendsto_approx_grad := v.tendsto_approx_grad

/-- Return a PDE zero-boundary representative to the native Sobolev API. -/
def pdeH10ToNative {d : ℕ} {U : Set (Vec d)} (v : PDE.H10Function U) :
    Homogenization.H10Function U where
  toH1Function := ⟨v.toH1Function.toFun, v.toH1Function.grad, v.toH1Function.memL2,
    v.toH1Function.gradMemL2, v.toH1Function.hasWeakGradient⟩
  approx := v.approx
  approx_smooth := v.approx_smooth
  approx_hasCompactSupport := v.approx_hasCompactSupport
  approx_support_subset := v.approx_support_subset
  tendsto_approx := v.tendsto_approx
  tendsto_approx_grad := v.tendsto_approx_grad

/-- The negative part and the positive excess above one of a completed
Dirichlet vector are admissible completed test vectors on the same ball. -/
theorem dirichletHilbert_truncation_tests {d : ℕ}
    (ρ : Vec d → ℝ) (R : ℝ) (hR : 0 < R) (C : ℝ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ v n p : Homogenization.H10Function (sourceBall (0 : Vec d) R),
      (v.toH1Function.toFun =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
        fun x => u.val none x) ∧
      (∀ i : Fin d, (fun x => v.toH1Function.grad x i)
        =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] fun x => u.val (some i) x) ∧
      (∀ x, n.toH1Function.toFun x = max (-v.toH1Function.toFun x) 0) ∧
      (∀ x, n.toH1Function.grad x =
        {y | v.toH1Function.toFun y < 0}.indicator (fun x => -v.toH1Function.grad x) x) ∧
      (∀ x, p.toH1Function.toFun x = max (v.toH1Function.toFun x - 1) 0) ∧
      (∀ x, p.toH1Function.grad x =
        {y | 1 < v.toH1Function.toFun y}.indicator v.toH1Function.grad x) ∧
      ∃ un up : DirichletHilbertSpace (d := d) R hR,
        (dirichletHilbertInclusion ρ R hR C hρ un : Vec d → ℝ)
          =ᵐ[dirichletVolume ρ R] n.toH1Function.toFun ∧
        (∀ i : Fin d, (fun x => un.val (some i) x)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] fun x => n.toH1Function.grad x i) ∧
        (dirichletHilbertInclusion ρ R hR C hρ up : Vec d → ℝ)
          =ᵐ[dirichletVolume ρ R] p.toH1Function.toFun ∧
        (∀ i : Fin d, (fun x => up.val (some i) x)
          =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)] fun x => p.toH1Function.grad x i) := by
  have hU : IsOpen (sourceBall (0 : Vec d) R) := by
    rw [← pde_ball_eq_sourceBall 0 hR]
    exact PDE.isOpen_euclideanBall _ _
  have hfin : volume (sourceBall (0 : Vec d) R) ≠ ∞ := by
    rw [← pde_ball_eq_sourceBall 0 hR]
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono (PDE.euclideanBall_subset_supBall hR))
  obtain ⟨v, hv, hvg⟩ := exists_nativeH10_of_dirichletHilbert R hR u
  obtain ⟨nP, hn, hng⟩ := PDE.Ch4GreenDecay.exists_negativePart_h10 hU hfin (nativeH10ToPDE v)
  let n := pdeH10ToNative nP
  let p := pdeH10ToNative (PDE.Ch4Infra.positivePartH10 hU hfin (nativeH10ToPDE v)
    (show (0 : ℝ) ≤ 1 by norm_num))
  obtain ⟨un, hun, hung⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR C hρ n
  obtain ⟨up, hup, hupg⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR C hρ p
  refine ⟨v, n, p, hv, hvg, hn, hng, ?_, ?_, un, up, hun, hung, hup, hupg⟩
  · intro x
    rfl
  · intro x
    rfl

#print axioms dirichletHilbert_truncation_tests


/-- The truncation tests retain their pointwise value and gradient formulas
on the source ball, as representatives of the completed space. -/
theorem dirichletHilbert_truncation_test_coordinates {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ un up : DirichletHilbertSpace (d := d) R hR,
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        un.val none x = max (-u.val none x) 0 ∧
        up.val none x = max (u.val none x - 1) 0 ∧
        (fun i => un.val (some i) x) =
          {y | u.val none y < 0}.indicator (fun y i => -u.val (some i) y) x ∧
        (fun i => up.val (some i) x) =
          {y | 1 < u.val none y}.indicator (fun y i => u.val (some i) y) x) := by
  let C := κ⁻¹
  let hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x ≤ C := fun x _ => (h.2.2 x).2.1
  have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  obtain ⟨v, n, p, hv, hvg, hn, hng, hp, hpg, un, up, hun, hung, hup, hupg⟩ :=
    dirichletHilbert_truncation_tests ρ R hR C hρ u
  have hunv : (fun x => un.val none x) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      n.toH1Function.toFun := hac.ae_le ((dirichletHilbertInclusion_coe ρ R hR C hρ un).symm.trans hun)
  have hupv : (fun x => up.val none x) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      p.toH1Function.toFun := hac.ae_le ((dirichletHilbertInclusion_coe ρ R hR C hρ up).symm.trans hup)
  refine ⟨un, up, ?_⟩
  filter_upwards [hv, ae_all_iff.mpr hvg, hunv, ae_all_iff.mpr hung,
    hupv, ae_all_iff.mpr hupg] with x hx hxg hnx hnxg hpx hpxg
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hnx, hn, hx]
  · rw [hpx, hp, hx]
  · by_cases ht : v.toH1Function.toFun x < 0
    · have ht' : u.val none x < 0 := hx ▸ ht
      rw [Set.indicator_of_mem (show x ∈ {y | u.val none y < 0} from ht')]
      funext i
      rw [hnxg i, hng, Set.indicator_of_mem (show x ∈ {y | v.toH1Function.toFun y < 0} from ht)]
      simp only [Pi.neg_apply, hxg i]
    · have ht' : ¬ u.val none x < 0 := by simpa only [← hx] using ht
      rw [Set.indicator_of_notMem (show x ∉ {y | u.val none y < 0} from ht')]
      funext i
      rw [hnxg i, hng, Set.indicator_of_notMem (show x ∉ {y | v.toH1Function.toFun y < 0} from ht)]
  · by_cases ht : 1 < v.toH1Function.toFun x
    · have ht' : 1 < u.val none x := hx ▸ ht
      rw [Set.indicator_of_mem (show x ∈ {y | 1 < u.val none y} from ht')]
      funext i
      rw [hpxg i, hpg, Set.indicator_of_mem (show x ∈ {y | 1 < v.toH1Function.toFun y} from ht)]
      exact hxg i
    · have ht' : ¬ 1 < u.val none x := by simpa only [← hx] using ht
      rw [Set.indicator_of_notMem (show x ∉ {y | 1 < u.val none y} from ht')]
      funext i
      rw [hpxg i, hpg, Set.indicator_of_notMem (show x ∉ {y | 1 < v.toH1Function.toFun y} from ht)]

#print axioms dirichletHilbert_truncation_test_coordinates


/-- Testing the shifted form with the negative part gives exactly the
negative of the self-energy of that completed test. -/
theorem dirichletHilbert_negative_test_energy {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) (τ : ℝ)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ un : DirichletHilbertSpace (d := d) R hR,
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        un.val none x = max (-u.val none x) 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * un.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => un.val (some i) x)) =
      -(∫ x in sourceBall (0 : Vec d) R,
        ρ x * un.val none x * un.val none x +
          τ * dot ((α x).mulVec (fun i => un.val (some i) x))
            (fun i => un.val (some i) x)) := by
  obtain ⟨un, up, ht⟩ := dirichletHilbert_truncation_test_coordinates hκ h R hR u
  refine ⟨un, ht.mono (fun _ hx => hx.1), ?_⟩
  rw [← integral_neg]
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  obtain ⟨hn, _, hng, _⟩ := hx
  by_cases hs : u.val none x < 0
  · rw [Set.indicator_of_mem (show x ∈ {y | u.val none y < 0} from hs)] at hng
    rw [hn, max_eq_left (neg_nonneg.mpr hs.le), hng]
    rw [show (fun i => -u.val (some i) x) = -(fun i => u.val (some i) x) from rfl,
      Matrix.mulVec_neg]
    simp only [dot, Pi.neg_apply, neg_mul, mul_neg, Finset.sum_neg_distrib, neg_neg]
    ring
  · have hu : 0 ≤ u.val none x := le_of_not_gt hs
    rw [Set.indicator_of_notMem (show x ∉ {y | u.val none y < 0} from hs)] at hng
    rw [hn, max_eq_right (neg_nonpos.mpr hu), hng]
    simp only [mul_zero, Matrix.mulVec_zero, dot, Pi.zero_apply,
      Finset.sum_const_zero, add_zero, neg_zero]

#print axioms dirichletHilbert_negative_test_energy

/-- The positive excess above one tests the shifted form as its own energy. -/
theorem dirichletHilbert_excess_test_energy {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) (τ : ℝ)
    (u : DirichletHilbertSpace (d := d) R hR) :
    ∃ up : DirichletHilbertSpace (d := d) R hR,
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        up.val none x = max (u.val none x - 1) 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * (u.val none x - 1) * up.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => up.val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
        ρ x * up.val none x * up.val none x +
          τ * dot ((α x).mulVec (fun i => up.val (some i) x))
            (fun i => up.val (some i) x) := by
  obtain ⟨un, up, ht⟩ := dirichletHilbert_truncation_test_coordinates hκ h R hR u
  refine ⟨up, ht.mono (fun _ hx => hx.2.1), ?_⟩
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  obtain ⟨_, hp, _, hpg⟩ := hx
  by_cases hs : 1 < u.val none x
  · rw [Set.indicator_of_mem (show x ∈ {y | 1 < u.val none y} from hs)] at hpg
    rw [hp, max_eq_left (sub_nonneg.mpr hs.le), hpg]
  · have hu : u.val none x ≤ 1 := le_of_not_gt hs
    rw [Set.indicator_of_notMem (show x ∉ {y | 1 < u.val none y} from hs)] at hpg
    rw [hp, max_eq_right (sub_nonpos.mpr hu), hpg]
    simp only [mul_zero, Matrix.mulVec_zero, dot, Pi.zero_apply,
      Finset.sum_const_zero, add_zero]

#print axioms dirichletHilbert_excess_test_energy

/-- The scaled source energy dominates the weighted square of its value. -/
theorem dirichlet_scaled_energy_value_bound {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Vec d) (z : ℝ) (v : Vec d) :
    κ * z ^ 2 ≤ ρ x * z * z + τ * dot ((α x).mulVec v) v := by
  have hs : 0 ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hg : 0 ≤ dot ((α x).mulVec v) v := by
    rw [show dot ((α x).mulVec v) v = dot v ((α x).mulVec v) from dotProduct_comm _ _]
    exact (mul_nonneg hκ.le hs).trans ((h.2.2 x).2.2.2 v).1
  have hm := mul_nonneg (sub_nonneg.mpr (h.2.2 x).1) (sq_nonneg z)
  have ht := mul_nonneg hτ hg
  nlinarith

#print axioms dirichlet_scaled_energy_value_bound

/-- The scaled value-gradient form is integrable on the actual source ball. -/
theorem dirichletHilbert_scaled_form_integrable {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) (τ : ℝ)
    (u v : DirichletHilbertSpace (d := d) R hR) :
    Integrable (fun x => ρ x * u.val none x * v.val none x +
      τ * dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => v.val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
  let Q := centeredCube (0 : SpatialCoordinates d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (SpatialCoordinates d))
  let a := dirichletValueGradientMatrix ρ α
  let b := dirichletValueGradientMatrix (fun _ : Vec d => 0) α
  have ha := dirichletValueGradientMatrix_aestronglyMeasurable h μ
  have hb (i j : Option (Fin d)) : AEStronglyMeasurable (fun x => b x i j) μ := by
    cases i with
    | none => cases j <;> exact aestronglyMeasurable_const
    | some i => cases j with
      | none => exact aestronglyMeasurable_const
      | some j => exact ha (some i) (some j)
  have hab : ∀ᵐ x ∂μ, ∀ i j, |a x i j| ≤ κ⁻¹ :=
    ae_of_all _ fun x i j => dirichletValueGradientMatrix_bound hκ h x i j
  have hbb : ∀ᵐ x ∂μ, ∀ i j, |b x i j| ≤ κ⁻¹ := by
    apply ae_of_all
    intro x i j
    cases i with
    | none => cases j <;> simpa only [b, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
    | some i => cases j with
      | none => simpa only [b, dirichletValueGradientMatrix, abs_zero] using inv_nonneg.mpr hκ.le
      | some j => exact dirichletValueGradientMatrix_bound hκ h x (some i) (some j)
  have hi := integrable_coordinateL2Form μ a ha hab u.val v.val
  have hj := integrable_coordinateL2Form μ b hb hbb u.val v.val
  have hform := hi.add (hj.const_mul (τ - 1))
  have hball : volume.restrict (sourceBall (0 : Vec d) R) ≤ μ :=
    Measure.restrict_mono (sourceBall_subset_cube R hR) le_rfl
  apply (hform.mono_measure hball).congr
  exact ae_of_all _ fun x => by
    dsimp only [Pi.add_apply, a, b]
    rw [dirichletValueGradientMatrix_sum, dirichletValueGradientMatrix_sum]
    simp only [zero_mul, zero_add]
    ring

#print axioms dirichletHilbert_scaled_form_integrable

/-- A nonpositive scaled self-energy forces the test value to vanish almost everywhere. -/
theorem dirichletHilbert_value_eq_zero_of_scaled_energy_nonpos {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {τ : ℝ} (hτ : 0 ≤ τ) (u : DirichletHilbertSpace (d := d) R hR)
    (he : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * u.val none x * u.val none x +
        τ * dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => u.val (some i) x)) ≤ 0) :
    ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), u.val none x = 0 := by
  have hi := dirichletHilbert_scaled_form_integrable hκ h R hR τ u u
  have hn : ∀ x, 0 ≤ ρ x * u.val none x * u.val none x +
      τ * dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => u.val (some i) x) :=
    fun x => (mul_nonneg hκ.le (sq_nonneg _)).trans
      (dirichlet_scaled_energy_value_bound hκ h hτ x _ _)
  have hz := (integral_eq_zero_iff_of_nonneg hn hi).mp
    (le_antisymm he (integral_nonneg hn))
  filter_upwards [hz] with x hx
  have hb := dirichlet_scaled_energy_value_bound hκ h hτ x (u.val none x)
    (fun i => u.val (some i) x)
  rw [hx] at hb
  have : (u.val none x) ^ 2 ≤ 0 := nonpos_of_mul_nonpos_left (by simpa [mul_comm] using hb) hκ
  exact sq_eq_zero_iff.mp (le_antisymm this (sq_nonneg _))

#print axioms dirichletHilbert_value_eq_zero_of_scaled_energy_nonpos

/-- The actual shifted variational solution is nonnegative for nonnegative data. -/
theorem dirichletHilbert_shifted_variational_nonneg {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x)
    (u : DirichletHilbertSpace (d := d) R hR)
    (hvar : ∀ v : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * v.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => v.val (some i) x)) =
        inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) v)) :
    ∀ᵐ x ∂dirichletVolume ρ R,
      0 ≤ dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u x := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hJ (v : DirichletHilbertSpace (d := d) R hR) :
      (J v : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (fun x => v.val none x) :=
    dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  obtain ⟨un, hn, he⟩ := dirichletHilbert_negative_test_energy hκ h R hR τ u
  have htest : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (J un) x := by
    filter_upwards [hJ un, hac.ae_le hn] with x hj hx
    rw [hj, hx]
    exact le_max_right _ _
  have hinner : 0 ≤ inner ℝ f (J un) := by
    rw [L2.inner_def]
    apply integral_nonneg_of_ae
    filter_upwards [hf, htest] with x hx hy
    simpa only [Pi.zero_apply, RCLike.inner_apply, conj_trivial] using mul_nonneg hy hx
  have henergy : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * un.val none x * un.val none x +
        τ * dot ((α x).mulVec (fun i => un.val (some i) x))
          (fun i => un.val (some i) x)) ≤ 0 := by
    have hv := hvar un
    change _ = inner ℝ f (J un) at hv
    rw [he] at hv
    linarith
  have hz := dirichletHilbert_value_eq_zero_of_scaled_energy_nonpos hκ h R hR hτ un henergy
  have hu : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), 0 ≤ u.val none x := by
    filter_upwards [hn, hz] with x hx hy
    have hm := le_max_left (-u.val none x) 0
    rw [← hx, hy] at hm
    linarith
  filter_upwards [hJ u, hac.ae_le hu] with x hx hy
  rw [hx]
  exact hy

#print axioms dirichletHilbert_shifted_variational_nonneg


/-- The shifted variational solution is at most one for data bounded by one. -/
theorem dirichletHilbert_shifted_variational_le_one {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {τ : ℝ} (hτ : 0 ≤ τ)
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, f x ≤ 1)
    (u : DirichletHilbertSpace (d := d) R hR)
    (hvar : ∀ v : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * v.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => v.val (some i) x)) =
        inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) v)) :
    ∀ᵐ x ∂dirichletVolume ρ R,
      dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u x ≤ 1 := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hJ (v : DirichletHilbertSpace (d := d) R hR) :
      (J v : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (fun x => v.val none x) :=
    dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  obtain ⟨up, hp, he⟩ := dirichletHilbert_excess_test_energy hκ h R hR τ u
  have htest : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (J up) x := by
    filter_upwards [hJ up, hac.ae_le hp] with x hj hx
    rw [hj, hx]
    exact le_max_right _ _
  have hmass : Integrable (fun x => ρ x * up.val none x)
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    have hi : Integrable (fun x => up.val none x) (dirichletVolume ρ R) :=
      ((Lp.memLp (J up)).integrable (by norm_num)).congr (hJ up)
    have ht := (integrable_withDensity_iff h.1.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)).mp hi
    apply ht.congr
    exact ae_of_all _ fun x => by
      dsimp only
      rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1)]
      ring
  have hinner : inner ℝ f (J up) ≤ ∫ x, (J up) x ∂dirichletVolume ρ R := by
    rw [L2.inner_def]
    apply integral_mono_ae
    · apply ((Lp.memLp f).integrable_mul (Lp.memLp (J up))).congr
      exact ae_of_all _ fun x => by
        simp only [Pi.mul_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    · exact (Lp.memLp (J up)).integrable (by norm_num)
    · filter_upwards [hf, htest] with x hx hy
      simpa only [RCLike.inner_apply, conj_trivial, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_right hx hy
  have hmass_eq : (∫ x, (J up) x ∂dirichletVolume ρ R) =
      ∫ x in sourceBall (0 : Vec d) R, ρ x * up.val none x := by
    calc
      _ = ∫ x, up.val none x ∂dirichletVolume ρ R := integral_congr_ae (hJ up)
      _ = _ := by
        change (∫ x, up.val none x ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
          (fun x => ENNReal.ofReal (ρ x))) = _
        rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        exact ae_of_all _ fun x => by
          dsimp only
          rw [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
  have henergy : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * up.val none x * up.val none x +
        τ * dot ((α x).mulVec (fun i => up.val (some i) x))
          (fun i => up.val (some i) x)) ≤ 0 := by
    have hv := hvar up
    change _ = inner ℝ f (J up) at hv
    have hs : (∫ x in sourceBall (0 : Vec d) R,
        ρ x * (u.val none x - 1) * up.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => up.val (some i) x)) =
        (∫ x in sourceBall (0 : Vec d) R,
          ρ x * u.val none x * up.val none x +
            τ * dot ((α x).mulVec (fun i => u.val (some i) x))
              (fun i => up.val (some i) x)) -
          ∫ x in sourceBall (0 : Vec d) R, ρ x * up.val none x := by
      rw [← integral_sub (dirichletHilbert_scaled_form_integrable hκ h R hR τ u up) hmass]
      apply integral_congr_ae
      exact ae_of_all _ fun x => by dsimp; ring
    rw [hs, hv] at he
    rw [hmass_eq] at hinner
    linarith
  have hz := dirichletHilbert_value_eq_zero_of_scaled_energy_nonpos hκ h R hR hτ up henergy
  have hu : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), u.val none x ≤ 1 := by
    filter_upwards [hp, hz] with x hx hy
    have hm := le_max_left (u.val none x - 1) 0
    rw [← hx, hy] at hm
    linarith
  filter_upwards [hJ u, hac.ae_le hu] with x hx hy
  rw [hx]
  exact hy

#print axioms dirichletHilbert_shifted_variational_le_one


/-- Positive time scaling preserves uniform ellipticity of the original fields. -/
theorem uniformlyElliptic_time_scale {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) {τ : ℝ} (hτ : 0 < τ) :
    ∃ κ' : ℝ, 0 < κ' ∧ IsUniformlyElliptic κ' ρ (fun x => τ • α x) := by
  let κ' := min κ (min (τ * κ) (κ / τ))
  have hk' : 0 < κ' := lt_min hκ (lt_min (mul_pos hτ hκ) (div_pos hκ hτ))
  have hk1 : κ' ≤ κ := min_le_left _ _
  have hk2 : κ' ≤ τ * κ := (min_le_right _ _).trans (min_le_left _ _)
  have hk3 : κ' ≤ κ / τ := (min_le_right _ _).trans (min_le_right _ _)
  have hkinv : κ⁻¹ ≤ κ'⁻¹ := inv_anti₀ hk' hk1
  have hkinvτ : τ * κ⁻¹ ≤ κ'⁻¹ := by
    have ht := inv_anti₀ hk' hk3
    simpa [div_eq_mul_inv, mul_comm] using ht
  refine ⟨κ', hk', h.1, ?_, ?_⟩
  · let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
    let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
    exact (show Continuous (fun a : Mat d => τ • a) from continuous_const_smul τ).measurable.comp h.2.1
  · intro x
    refine ⟨hk1.trans (h.2.2 x).1, (h.2.2 x).2.1.trans hkinv, ?_, ?_⟩
    · rw [Matrix.transpose_smul, (h.2.2 x).2.2.1]
    · intro v
      have hs : 0 ≤ euclideanSq v := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
      have hd : dot v ((τ • α x).mulVec v) = τ * dot v ((α x).mulVec v) := by
        rw [Matrix.smul_mulVec]
        simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      rw [hd]
      constructor
      · calc
          κ' * euclideanSq v ≤ (τ * κ) * euclideanSq v :=
            mul_le_mul_of_nonneg_right hk2 hs
          _ ≤ τ * dot v ((α x).mulVec v) := by
            nlinarith [mul_le_mul_of_nonneg_left ((h.2.2 x).2.2.2 v).1 hτ.le]
      · calc
          τ * dot v ((α x).mulVec v) ≤ (τ * κ⁻¹) * euclideanSq v := by
            nlinarith [mul_le_mul_of_nonneg_left ((h.2.2 x).2.2.2 v).2 hτ.le]
          _ ≤ κ'⁻¹ * euclideanSq v := mul_le_mul_of_nonneg_right hkinvτ hs

#print axioms uniformlyElliptic_time_scale


/-- The positive-time shifted resolvent acts on the original weighted carrier
and is characterized by its literal scaled variational equation. -/
theorem exists_compact_dirichletHilbert_shifted_resolvent {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {τ : ℝ} (hτ : 0 < τ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧
      ∀ f, ∀ u : DirichletHilbertSpace (d := d) R hR,
        u = S f ↔ ∀ v : DirichletHilbertSpace (d := d) R hR,
          (∫ x in sourceBall (0 : Vec d) R,
            ρ x * u.val none x * v.val none x +
              τ * dot ((α x).mulVec (fun i => u.val (some i) x))
                (fun i => v.val (some i) x)) = inner ℝ f (J v) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨κ', hk', hs⟩ := uniformlyElliptic_time_scale hκ h hτ
  let J' := dirichletHilbertInclusion ρ R hR κ'⁻¹ (fun x _ => (hs.2.2 x).2.1)
  have hJ : J' = J := by
    apply ContinuousLinearMap.ext
    intro v
    apply Lp.ext
    exact (dirichletHilbertInclusion_coe ρ R hR κ'⁻¹
      (fun x _ => (hs.2.2 x).2.1) v).trans
      (dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) v).symm
  obtain ⟨S, hcompact, hvar⟩ := exists_compact_dirichletHilbert_resolvent hd hk' hs R hR
  change IsCompactOperator (J'.comp S) at hcompact
  rw [hJ] at hcompact
  refine ⟨S, hcompact, ?_⟩
  intro f u
  have heq (v : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * v.val none x +
          dot (((τ • α x) : Mat d).mulVec (fun i => u.val (some i) x))
            (fun i => v.val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * v.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => v.val (some i) x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [Matrix.smul_mulVec]
      simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  constructor
  · intro hu v
    have hv := (hvar f u).mp hu v
    change _ = inner ℝ f (J' v) at hv
    rw [hJ, heq v] at hv
    exact hv
  · intro hu
    apply (hvar f u).mpr
    intro v
    change _ = inner ℝ f (J' v)
    rw [hJ, heq v]
    exact hu v

#print axioms exists_compact_dirichletHilbert_shifted_resolvent


/-- The actual compact shifted resolvent preserves nonnegativity and [0,1]. -/
theorem exists_compact_dirichletHilbert_shifted_resolvent_order {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {τ : ℝ} (hτ : 0 < τ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧
      (∀ f, ∀ v : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          ρ x * (S f).val none x * v.val none x +
            τ * dot ((α x).mulVec (fun i => (S f).val (some i) x))
              (fun i => v.val (some i) x)) = inner ℝ f (J v)) ∧
      (∀ f, (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
        ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (J (S f)) x) ∧
      (∀ f, (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (J (S f)) x ∧ (J (S f)) x ≤ 1) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨S, hc, hv⟩ := exists_compact_dirichletHilbert_shifted_resolvent hd hκ h R hR hτ
  have hs (f : Lp ℝ 2 (dirichletVolume ρ R)) := (hv f (S f)).mp rfl
  refine ⟨S, hc, hs, ?_, ?_⟩
  · intro f hf
    exact dirichletHilbert_shifted_variational_nonneg hκ h R hR hτ.le f hf (S f) (hs f)
  · intro f hf
    have hn := dirichletHilbert_shifted_variational_nonneg hκ h R hR hτ.le f
      (hf.mono (fun _ hx => hx.1)) (S f) (hs f)
    have hu := dirichletHilbert_shifted_variational_le_one hκ h R hR hτ.le f
      (hf.mono (fun _ hx => hx.2)) (S f) (hs f)
    filter_upwards [hn, hu] with x hx hy
    exact ⟨hx, hy⟩

#print axioms exists_compact_dirichletHilbert_shifted_resolvent_order


/-- Every coordinate of the actual shifted variational solution is the
corresponding resolvent multiplier of the original Dirichlet eigenbasis. -/
theorem dirichletHilbert_shifted_variational_coordinate {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    {τ : ℝ} (hτ : 0 ≤ τ) (f : Lp ℝ 2 (dirichletVolume ρ R))
    (u : DirichletHilbertSpace (d := d) R hR)
    (hvar : ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * u.val none x * w.val none x +
          τ * dot ((α x).mulVec (fun i => u.val (some i) x))
            (fun i => w.val (some i) x)) =
      inner ℝ f (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w)) :
    ∀ n, b.repr (dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) u) n =
      (1 + τ * eigenvalue n)⁻¹ * b.repr f n := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  intro n
  have hm : Integrable (fun x => ρ x * u.val none x * (vs n).val none x)
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    simpa using dirichletHilbert_scaled_form_integrable hκ h R hR 0 u (vs n)
  have hg : Integrable (fun x => dot ((α x).mulVec (fun i => u.val (some i) x))
      (fun i => (vs n).val (some i) x))
      (volume.restrict (sourceBall (0 : Vec d) R)) := by
    have hi := (dirichletHilbert_scaled_form_integrable hκ h R hR 1 u (vs n)).sub hm
    apply hi.congr
    exact ae_of_all _ fun x => by dsimp; ring
  have hmass : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * u.val none x * (vs n).val none x) = inner ℝ (J u) (b n) := by
    rw [hb n]
    exact (dirichletVolume_inner_eq_native hκ h R (J u) (J (vs n))
      (fun x => u.val none x) (fun x => (vs n).val none x)
      (dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u)
      (dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (vs n))).symm
  have hsym : (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => u.val (some i) x)) (fun i => (vs n).val (some i) x)) =
      ∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (vs n).val (some i) x)) (fun i => u.val (some i) x) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      have hs : (α x).IsSymm := (h.2.2 x).2.2.1
      have he := hs.dotProduct_mulVec_comm
        (x := fun i => (vs n).val (some i) x) (y := fun i => u.val (some i) x)
      rw [dotProduct_comm, dotProduct_comm (fun i => u.val (some i) x)] at he
      exact he
  have hv := hvar (vs n)
  change _ = inner ℝ f (J (vs n)) at hv
  rw [integral_add hm (hg.const_mul τ), integral_const_mul, hmass, hsym,
    hvarb n u, ← hb n] at hv
  have hd : 0 < 1 + τ * eigenvalue n := by
    have := mul_nonneg hτ (hpos n)
    linarith
  rw [b.repr_apply_apply, b.repr_apply_apply]
  rw [real_inner_comm (b n) (J u), real_inner_comm (b n) f] at hv
  rw [eq_inv_mul_iff_mul_eq₀ (ne_of_gt hd)]
  nlinarith only [hv]

#print axioms dirichletHilbert_shifted_variational_coordinate


/-- The same compact shifted resolvent has the spectral multiplier and its
finite iterates preserve the unit interval. -/
theorem exists_dirichletHilbert_shifted_resolvent_iterates {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    {τ : ℝ} (hτ : 0 < τ) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ S : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      IsCompactOperator (J.comp S) ∧
      (∀ f m n, b.repr ((fun g => J (S g))^[m] f) n =
        ((1 + τ * eigenvalue n)⁻¹) ^ m * b.repr f n) ∧
      (∀ f m, (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
        ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ ((fun g => J (S g))^[m] f) x) ∧
      (∀ f m, (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ ((fun g => J (S g))^[m] f) x ∧
          ((fun g => J (S g))^[m] f) x ≤ 1) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨S, hc, hv, hn, hu⟩ :=
    exists_compact_dirichletHilbert_shifted_resolvent_order hd hκ h R hR hτ
  have hcoord (f : Lp ℝ 2 (dirichletVolume ρ R)) (n : ℕ) :
      b.repr (J (S f)) n = (1 + τ * eigenvalue n)⁻¹ * b.repr f n :=
    dirichletHilbert_shifted_variational_coordinate hκ h R hR eigenvalue hpos vs b hb hvarb
      hτ.le f (S f) (hv f) n
  refine ⟨S, hc, ?_, ?_, ?_⟩
  · intro f m
    induction m with
    | zero => intro n; simp only [Function.iterate_zero_apply, pow_zero, one_mul]
    | succ m ih =>
      intro n
      rw [Function.iterate_succ_apply', hcoord, ih, pow_succ]
      ring
  · intro f m hf
    induction m with
    | zero => simpa only [Function.iterate_zero_apply] using hf
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hn _ ih
  · intro f m hf
    induction m with
    | zero => simpa only [Function.iterate_zero_apply] using hf
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact hu _ ih

#print axioms exists_dirichletHilbert_shifted_resolvent_iterates


/-- The scalar shifted-resolvent iterates converge to the heat multiplier. -/
theorem shifted_resolvent_scalar_euler_limit (a : ℝ) :
    Tendsto (fun n : ℕ => (1 + a / (n + 1 : ℝ))⁻¹ ^ (n + 1))
      atTop (𝓝 (Real.exp (-a))) := by
  have ht := ((Real.tendsto_one_add_div_pow_exp a).comp
    (tendsto_add_atTop_nat 1)).inv₀ (Real.exp_ne_zero a)
  simpa only [Function.comp_apply, inv_pow, Real.exp_neg, Nat.cast_add, Nat.cast_one] using ht

#print axioms shifted_resolvent_scalar_euler_limit


/-- Uniformly bounded spectral multipliers converge strongly when their
coordinates converge to the heat weights. -/
theorem spectralHeat_tendsto_of_bounded_coordinates {d : ℕ}
    {ρ : Vec d → ℝ} {R : ℝ}
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R))
    (g : ℕ → Lp ℝ 2 (dirichletVolume ρ R)) (a : ℕ → ℕ → ℝ)
    (ha : ∀ m n, |a m n| ≤ 1)
    (hg : ∀ m n, b.repr (g m) n = a m n * b.repr f n)
    (hlim : ∀ n, Tendsto (fun m => a m n) atTop
      (𝓝 (Real.exp (-eigenvalue n * t)))) :
    Tendsto g atTop (𝓝 (SpectralHeat.heatOperator b eigenvalue hpos t f)) := by
  let F : ℕ → ℕ → ℝ := fun m n =>
    ‖(a m n - Real.exp (-eigenvalue n * t)) * b.repr f n‖ ^ 2
  have hsq : Summable (fun n => ‖b.repr f n‖ ^ 2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.memℓp (b.repr f)).summable (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  have hbound (m n : ℕ) : ‖F m n‖ ≤ 4 * ‖b.repr f n‖ ^ 2 := by
    have hcoeff : ‖a m n - Real.exp (-eigenvalue n * t)‖ ≤ 2 := by
      exact (norm_sub_le _ _).trans (by
        simpa only [Real.norm_eq_abs, one_add_one_eq_two] using
          add_le_add (ha m n) (SpectralHeat.exp_weight_bound eigenvalue hpos t n))
    have hp : ‖(a m n - Real.exp (-eigenvalue n * t)) * b.repr f n‖ ≤
        2 * ‖b.repr f n‖ := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)
    change ‖(‖_‖ ^ 2 : ℝ)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ (2 * ‖b.repr f n‖) ^ 2 := by gcongr
      _ = _ := by ring
  have hterm (n : ℕ) : Tendsto (fun m => F m n) atTop (𝓝 0) := by
    have ht := (((hlim n).sub (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => Real.exp (-eigenvalue n * t)) atTop
        (𝓝 (Real.exp (-eigenvalue n * t))))).mul_const (b.repr f n)).norm.pow 2
    simpa only [F, sub_self, zero_mul, norm_zero, zero_pow (by omega : 2 ≠ 0)] using ht
  have hsum : Tendsto (fun m => ∑' n, F m n) atTop (𝓝 0) := by
    simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence
      (hsq.mul_left 4) hterm (Eventually.of_forall hbound)
  have heq (m : ℕ) :
      ‖g m - SpectralHeat.heatOperator b eigenvalue hpos t f‖ ^ 2 = ∑' n, F m n := by
    calc
      _ = ‖b.repr (g m - SpectralHeat.heatOperator b eigenvalue hpos t f)‖ ^ 2 := by
        rw [b.repr.norm_map]
      _ = ∑' n, ‖b.repr (g m - SpectralHeat.heatOperator b eigenvalue hpos t f) n‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (b.repr (g m - SpectralHeat.heatOperator b eigenvalue hpos t f))
      _ = _ := by
        apply tsum_congr
        intro n
        rw [map_sub]
        change ‖b.repr (g m) n -
          b.repr (SpectralHeat.heatOperator b eigenvalue hpos t f) n‖ ^ 2 = _
        rw [hg, SpectralHeat.heatOperator_repr, ← sub_mul]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (hsum.congr' (Eventually.of_forall (fun m => (heq m).symm)))
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs

#print axioms spectralHeat_tendsto_of_bounded_coordinates

/-- The actual shifted resolvent Euler iterates converge strongly to spectral heat
and retain the order bounds at every finite step. -/
theorem exists_dirichletHilbert_resolvent_euler_approximation {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ∃ g : ℕ → Lp ℝ 2 (dirichletVolume ρ R),
      Tendsto g atTop (𝓝 (SpectralHeat.heatOperator b eigenvalue hpos t f)) ∧
      ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
        ∀ m, ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ g m x) ∧
      ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ m, ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ g m x ∧ g m x ≤ 1) := by
  classical
  let τ : ℕ → ℝ := fun m => (t : ℝ) / (m + 1 : ℝ)
  have hτ (m : ℕ) : 0 < τ m := div_pos ht (by positivity)
  choose S hS using fun m =>
    exists_dirichletHilbert_shifted_resolvent_iterates hd hκ h R hR eigenvalue hpos vs b hb hvarb (hτ m)
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let g : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun m => (fun v => J (S m v))^[m + 1] f
  let a : ℕ → ℕ → ℝ := fun m n => (1 + τ m * eigenvalue n)⁻¹ ^ (m + 1)
  have ha (m n : ℕ) : |a m n| ≤ 1 := by
    have hd : 1 ≤ 1 + τ m * eigenvalue n := by
      nlinarith [mul_nonneg (hτ m).le (hpos n)]
    have hi : 0 ≤ (1 + τ m * eigenvalue n)⁻¹ := inv_nonneg.mpr (by linarith)
    have hi1 : (1 + τ m * eigenvalue n)⁻¹ ≤ 1 := by
      exact (inv_le_one₀ (by linarith)).2 hd
    simpa only [a, abs_of_nonneg (pow_nonneg hi _)] using pow_le_one₀ hi hi1
  have hg (m n : ℕ) : b.repr (g m) n = a m n * b.repr f n :=
    (hS m).2.1 f (m + 1) n
  have hlim (n : ℕ) : Tendsto (fun m => a m n) atTop
      (𝓝 (Real.exp (-eigenvalue n * t))) := by
    have he : -eigenvalue n * (t : ℝ) = -(eigenvalue n * (t : ℝ)) := by ring
    rw [he]
    convert shifted_resolvent_scalar_euler_limit (eigenvalue n * t) using 1
    funext m
    dsimp only [a, τ]
    congr 2
    ring
  refine ⟨g, spectralHeat_tendsto_of_bounded_coordinates b eigenvalue hpos t f g a ha hg hlim, ?_, ?_⟩
  · intro hf m
    exact (hS m).2.2.1 f (m + 1) hf
  · intro hf m
    exact (hS m).2.2.2 f (m + 1) hf

#print axioms exists_dirichletHilbert_resolvent_euler_approximation

/-- Almost-everywhere order intervals are closed under strong convergence in L². -/
theorem lp_tendsto_ae_order {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] (g : ℕ → Lp ℝ 2 μ) (z : Lp ℝ 2 μ)
    (hg : Tendsto g atTop (𝓝 z)) :
    ((∀ m, ∀ᵐ x ∂μ, 0 ≤ g m x) → ∀ᵐ x ∂μ, 0 ≤ z x) ∧
    ((∀ m, ∀ᵐ x ∂μ, 0 ≤ g m x ∧ g m x ≤ 1) →
      ∀ᵐ x ∂μ, 0 ≤ z x ∧ z x ≤ 1) := by
  have lower (h : ∀ m, ∀ᵐ x ∂μ, 0 ≤ g m x) : ∀ᵐ x ∂μ, 0 ≤ z x := by
    apply (Lp.coeFn_nonneg z).2
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hg
      (Eventually.of_forall fun m => (Lp.coeFn_nonneg (g m)).1 (h m))
  refine ⟨lower, ?_⟩
  intro h
  have hz : ∀ᵐ x ∂μ, 0 ≤ z x := lower (fun m => (h m).mono fun _ hx => hx.1)
  let one : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  have hu (m : ℕ) : g m ≤ one := by
    apply (Lp.coeFn_le (g m) one).1
    filter_upwards [h m, Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx hc
    simpa only [one, Function.const_apply] using hc ▸ hx.2
  have hzu : z ≤ one := le_of_tendsto_of_tendsto hg tendsto_const_nhds
    (Eventually.of_forall hu)
  have hzae := (Lp.coeFn_le z one).2 hzu
  filter_upwards [hz, hzae, Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx hle hc
  have hc' : one x = 1 := hc
  rw [hc'] at hle
  exact ⟨hx, hle⟩

#print axioms lp_tendsto_ae_order

/-- The weighted spectral Dirichlet heat operator preserves nonnegativity and
    the unit interval. -/
theorem dirichletHilbert_spectralHeat_order {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
      ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ SpectralHeat.heatOperator b eigenvalue hpos t f x) ∧
    ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
      ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ SpectralHeat.heatOperator b eigenvalue hpos t f x ∧
        SpectralHeat.heatOperator b eigenvalue hpos t f x ≤ 1) := by
  by_cases ht : t = 0
  · subst t
    simp only [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply]
    exact ⟨id, id⟩
  · have htpos : 0 < (t : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr ht : 0 < t)
    obtain ⟨g, hg, hn, hu⟩ :=
      exists_dirichletHilbert_resolvent_euler_approximation hd hκ h R hR eigenvalue hpos vs b hb hvarb t htpos f
    haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
      dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    have hord := lp_tendsto_ae_order (dirichletVolume ρ R) g _ hg
    exact ⟨fun hf => hord.1 (hn hf), fun hf => hord.2 (hu hf)⟩

#print axioms dirichletHilbert_spectralHeat_order

/-- The actual Dirichlet spectral heat operator preserves almost-everywhere order. -/
theorem dirichletHilbert_spectralHeat_mono {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (f g : Lp ℝ 2 (dirichletVolume ρ R))
    (hfg : ∀ᵐ x ∂dirichletVolume ρ R, f x ≤ g x) :
    ∀ᵐ x ∂dirichletVolume ρ R,
      SpectralHeat.heatOperator b eigenvalue hpos t f x ≤
        SpectralHeat.heatOperator b eigenvalue hpos t g x := by
  have hsub : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (g - f) x := by
    filter_upwards [hfg, Lp.coeFn_sub g f] with x hx hs
    simp only [Pi.sub_apply] at hs
    rw [hs]
    exact sub_nonneg.mpr hx
  have hout := (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos
    vs b hb hvarb t (g - f)).1 hsub
  rw [map_sub] at hout
  filter_upwards [hout, Lp.coeFn_sub (SpectralHeat.heatOperator b eigenvalue hpos t g)
    (SpectralHeat.heatOperator b eigenvalue hpos t f)] with x hx hs
  simp only [Pi.sub_apply] at hs
  rw [hs] at hx
  exact sub_nonneg.mp hx

#print axioms dirichletHilbert_spectralHeat_mono

/-- Bounded nonnegative inputs remain bounded by the same constant. -/
theorem dirichletHilbert_spectralHeat_bounded {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ C) :
    ∀ᵐ x ∂dirichletVolume ρ R,
      0 ≤ SpectralHeat.heatOperator b eigenvalue hpos t f x ∧
        SpectralHeat.heatOperator b eigenvalue hpos t f x ≤ C := by
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
  have hone : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ one x ∧ one x ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
    simp only [Function.const_apply] at hx
    rw [hx]
    exact ⟨zero_le_one, le_rfl⟩
  have hheat := (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos
    vs b hb hvarb t one).2 hone
  have hcompare : ∀ᵐ x ∂dirichletVolume ρ R, f x ≤ (C • one) x := by
    filter_upwards [hf, Lp.coeFn_smul C one,
      Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx hs ho
    simp only [Pi.smul_apply, smul_eq_mul, one, Function.const_apply] at hs ho
    rw [hs, ho, mul_one]
    exact hx.2
  have hmono := dirichletHilbert_spectralHeat_mono hd hκ h R hR eigenvalue hpos
    vs b hb hvarb t f (C • one) hcompare
  rw [map_smul] at hmono
  have hnonneg := (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos
    vs b hb hvarb t f).1 (hf.mono fun _ hx => hx.1)
  filter_upwards [hnonneg, hmono, hheat,
    Lp.coeFn_smul C (SpectralHeat.heatOperator b eigenvalue hpos t one)] with x hn hm hh hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs] at hm
  exact ⟨hn, hm.trans (by nlinarith [mul_le_mul_of_nonneg_left hh.2 hC])⟩

#print axioms dirichletHilbert_spectralHeat_bounded

/-- The actual weighted Dirichlet spectral basis has an order-preserving heat
operator; no order property is assumed of the basis. -/
theorem exists_dirichletSpectralHeat_order {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n),
      (∀ n, 0 < eigenvalue n) ∧
      (∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) ∧
      (∀ t : ℝ≥0, ∀ f g : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂dirichletVolume ρ R, f x ≤ g x) →
        ∀ᵐ x ∂dirichletVolume ρ R,
          SpectralHeat.heatOperator b eigenvalue hpos t f x ≤
            SpectralHeat.heatOperator b eigenvalue hpos t g x) ∧
      (∀ t : ℝ≥0, ∀ f : Lp ℝ 2 (dirichletVolume ρ R), ∀ C : ℝ, 0 ≤ C →
        (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ C) →
        ∀ᵐ x ∂dirichletVolume ρ R,
          0 ≤ SpectralHeat.heatOperator b eigenvalue hpos t f x ∧
            SpectralHeat.heatOperator b eigenvalue hpos t f x ≤ C) := by
  obtain ⟨eigenvalue, vs, heig, _hlim, he, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  let b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)) :=
    HilbertBasis.mk he (le_of_eq hspan.symm)
  have hb (n : ℕ) : b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n) :=
    congrFun (HilbertBasis.coe_mk he (le_of_eq hspan.symm)) n
  have hvarb (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w) := by
    rw [hb]
    exact hvar n w
  let hpos : ∀ n, 0 ≤ eigenvalue n := fun n => (heig n).le
  exact ⟨eigenvalue, vs, b, hpos, heig, hb,
    fun t f g hfg => dirichletHilbert_spectralHeat_mono hd hκ h R hR
      eigenvalue hpos vs b hb hvarb t f g hfg,
    fun t f C hC hf => dirichletHilbert_spectralHeat_bounded hd hκ h R hR
      eigenvalue hpos vs b hb hvarb t f C hC hf⟩

#print axioms exists_dirichletSpectralHeat_order


/-- The lowest finite spectral projection of the actual Dirichlet heat is positive. -/
theorem dirichletHilbert_lowest_projection_nonneg {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (j : ℕ) (S : Finset ℕ)
    (hlimit : ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
      Tendsto (fun t : ℝ≥0 => Real.exp (eigenvalue j * t) •
        SpectralHeat.heatOperator b eigenvalue hpos t f) atTop
        (𝓝 (∑ n ∈ S, b.repr f n • b n)))
    (f : Lp ℝ 2 (dirichletVolume ρ R))
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) :
    ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (∑ n ∈ S, b.repr f n • b n) x := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let g : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun m =>
    Real.exp (eigenvalue j * (m : ℝ≥0)) •
      SpectralHeat.heatOperator b eigenvalue hpos (m : ℝ≥0) f
  have hg : Tendsto g atTop (𝓝 (∑ n ∈ S, b.repr f n • b n)) :=
    (hlimit f).comp tendsto_natCast_atTop_atTop
  apply (lp_tendsto_ae_order (dirichletVolume ρ R) g _ hg).1
  intro m
  have hn := (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos
    vs b hb hvar (m : ℝ≥0) f).1 hf
  filter_upwards [hn, Lp.coeFn_smul (Real.exp (eigenvalue j * (m : ℝ≥0)))
    (SpectralHeat.heatOperator b eigenvalue hpos (m : ℝ≥0) f)] with x hx hs
  simp only [g, Pi.smul_apply, smul_eq_mul] at hs ⊢
  rw [hs]
  exact mul_nonneg (Real.exp_pos _).le hx

#print axioms dirichletHilbert_lowest_projection_nonneg


/-- A finite projection containing a basis vector is nonzero on a nonnegative input. -/
theorem finite_spectral_projection_exists_nonnegative_input
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 μ)) (S : Finset ℕ) (j : ℕ) (hj : j ∈ S) :
    ∃ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) ∧
      (∑ n ∈ S, b.repr f n • b n) ≠ 0 := by
  classical
  let P : Lp ℝ 2 μ → Lp ℝ 2 μ := fun f => ∑ n ∈ S, b.repr f n • b n
  have hfixed : P (b j) = b j := by
    dsimp only [P]
    rw [Finset.sum_eq_single j]
    · simp [b.repr_self, lp.single_apply]
    · intro n _ hnj
      simp [b.repr_self, lp.single_apply, hnj]
    · exact fun h => (h hj).elim
  have hdecomp : Lp.posPart (b j) - Lp.negPart (b j) = b j := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (Lp.posPart (b j)) (Lp.negPart (b j)),
      Lp.coeFn_posPart (b j), Lp.coeFn_negPart (b j)] with x hs hp hn
    simp only [Pi.sub_apply] at hs
    rw [hs, hp, hn]
    simpa only [sub_neg_eq_add, add_zero] using max_add_min (b j x) 0
  have hlinear : P (Lp.posPart (b j) - Lp.negPart (b j)) =
      P (Lp.posPart (b j)) - P (Lp.negPart (b j)) := by
    simp only [P, map_sub, lp.coeFn_sub, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have hnonzero : P (Lp.posPart (b j)) ≠ 0 ∨ P (Lp.negPart (b j)) ≠ 0 := by
    by_contra hc
    push Not at hc
    have hz : b j = 0 := by
      rw [← hfixed, ← hdecomp, hlinear, hc.1, hc.2, sub_zero]
    have hn := b.orthonormal.norm_eq_one j
    rw [hz, norm_zero] at hn
    norm_num at hn
  rcases hnonzero with hp | hn
  · refine ⟨Lp.posPart (b j), ?_, hp⟩
    filter_upwards [Lp.coeFn_posPart (b j)] with x hx
    rw [hx]
    exact le_max_right _ _
  · refine ⟨Lp.negPart (b j), ?_, hn⟩
    filter_upwards [Lp.coeFn_negPart_eq_max (b j)] with x hx
    rw [hx]
    exact le_max_right _ _

#print axioms finite_spectral_projection_exists_nonnegative_input


/-- An actual lowest Dirichlet spectral mode is nonnegative and nonzero. -/
theorem exists_dirichletHilbert_nonnegative_lowest_projection {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (eigenvalue : ℕ → ℝ) (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
      (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
      (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ) (S : Finset ℕ)
      (f : Lp ℝ 2 (dirichletVolume ρ R)),
      0 < δ ∧ (∀ n, 0 < eigenvalue n) ∧ (∀ n, b n = J (vs n)) ∧
      (∀ n, eigenvalue j ≤ eigenvalue n) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : Vec d) R,
          dot ((α x).mulVec (fun i => (vs n).val (some i) x))
            (fun i => w.val (some i) x)) = eigenvalue n * inner ℝ (b n) (J w)) ∧
      (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) ∧
      (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ (∑ n ∈ S, b.repr f n • b n) x) ∧
      (∑ n ∈ S, b.repr f n • b n) ≠ 0 ∧
      ∀ g : Lp ℝ 2 (dirichletVolume ρ R),
        Tendsto (fun t : ℝ≥0 => Real.exp (eigenvalue j * t) •
          SpectralHeat.heatOperator b eigenvalue hpos t g) atTop
          (𝓝 (∑ n ∈ S, b.repr g n • b n)) := by
  dsimp only
  obtain ⟨eigenvalue, vs, j, δ, hδ, hp, hl, ho, hs, hm, hg, hv⟩ :=
    exists_dirichletHilbert_spectral_minimum_and_gap hd hκ h R hR
  let b := HilbertBasis.mk ho (le_of_eq hs.symm)
  have hb (n : ℕ) : b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n) :=
    congrFun (HilbertBasis.coe_mk ho (le_of_eq hs.symm)) n
  let hpos : ∀ n, 0 ≤ eigenvalue n := fun n => (hp n).le
  obtain ⟨S, hS, _⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue hpos hl j δ hδ hg
  have hvar (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w) := by
    rw [hb]
    exact hv n w
  have hlimit := rescaled_heat_tendsto_lowest_projection b eigenvalue hpos j δ hδ S hS hg
  obtain ⟨f, hf, hfne⟩ := finite_spectral_projection_exists_nonnegative_input
    (dirichletVolume ρ R) b S j ((hS j).2 rfl)
  have hprojection := dirichletHilbert_lowest_projection_nonneg hd hκ h R hR
    eigenvalue hpos vs b hb hvar j S hlimit f hf
  exact ⟨eigenvalue, vs, b, hpos, j, δ, S, f, hδ, hp, hb, hm, hg, hS,
    hvar, hf, hprojection, hfne, hlimit⟩

#print axioms exists_dirichletHilbert_nonnegative_lowest_projection



/-- The actual lowest spectral projection yields a nonnegative normalized
native Dirichlet weak eigenfunction. -/
theorem exists_dirichlet_native_nonnegative_groundstate {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eig : ℝ) (v : Homogenization.H10Function (sourceBall (0 : Vec d) R)),
      0 < eig ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R),
        0 ≤ v.toH1Function.toFun x) ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1 ∧
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) = eig := by
  obtain ⟨eigenvalue, vs, b, hpos, j, δ, S, f, hδ, hp, hb, hm, hg, hS,
    hvar, hf, hproj, hne, hlimit⟩ :=
    exists_dirichletHilbert_nonnegative_lowest_projection hd hκ h R hR
  obtain ⟨v, hv, hw, hmass, henergy, hz⟩ :=
    finite_spectral_projection_zero_or_normalized_native hd hκ h R hR
      eigenvalue vs b hb hvar S (eigenvalue j) (fun n hn => (hS n).1 hn) f
  rcases hz with hz | ⟨v₀, hrep, hweak, hmass₀, henergy₀⟩
  · exact (hne hz).elim
  · refine ⟨eigenvalue j, v₀, hp j, ?_, hweak, hmass₀, henergy₀⟩
    have hweighted : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ v₀.toH1Function.toFun x := by
      filter_upwards [hproj, hrep, Lp.coeFn_smul
        ‖(∑ n ∈ S, b.repr f n • b n : Lp ℝ 2 (dirichletVolume ρ R))‖⁻¹
        (∑ n ∈ S, b.repr f n • b n)] with x hx hr hs
      have hh : 0 ≤ ‖(∑ n ∈ S, b.repr f n • b n : Lp ℝ 2 (dirichletVolume ρ R))‖⁻¹ *
          (∑ n ∈ S, b.repr f n • b n) x := mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) hx
      rw [← hr, hs]
      simpa only [Pi.smul_apply, smul_eq_mul] using hh
    have hac : volume.restrict (sourceBall (0 : Vec d) R) ≪ dirichletVolume ρ R := by
      apply withDensity_absolutelyContinuous' (ENNReal.measurable_ofReal.comp h.1).aemeasurable
      exact Filter.Eventually.of_forall (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (h.2.2 x).1)))
    exact hac.ae_le hweighted

#print axioms exists_dirichlet_native_nonnegative_groundstate


/-- Positive integrable mass in a source ball has an interior support point;
every smaller source ball about that point has positive mass. -/
theorem exists_sourceBall_positive_mass_point {d : ℕ} (R : ℝ) (hR : 0 < R)
    (f : Vec d → ℝ) (hf : IntegrableOn f (sourceBall (0 : Vec d) R))
    (hn : ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), 0 ≤ f x)
    (hm : 0 < ∫ x in sourceBall (0 : Vec d) R, f x) :
    ∃ x ∈ sourceBall (0 : Vec d) R, ∀ s : ℝ, 0 < s →
      sourceBall x s ⊆ sourceBall (0 : Vec d) R →
      0 < ∫ y in sourceBall x s, f y := by
  let μ := (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
    (fun x => ENNReal.ofReal (f x))
  have hRmeas : MeasurableSet (sourceBall (0 : Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hμ : 0 < μ (sourceBall (0 : Vec d) R) := by
    rw [show μ (sourceBall (0 : Vec d) R) =
      ∫⁻ x, ENNReal.ofReal (f x) ∂volume.restrict (sourceBall (0 : Vec d) R) by
        dsimp only [μ]
        rw [withDensity_apply _ hRmeas, Measure.restrict_restrict_of_subset (Subset.rfl)]]
    rw [← ofReal_integral_eq_lintegral_ofReal hf hn]
    exact ENNReal.ofReal_pos.mpr hm
  obtain ⟨x, hx, hxs⟩ := Measure.nonempty_inter_support_of_pos hμ
  refine ⟨x, hx, ?_⟩
  intro s hs hsub
  have hopen : IsOpen (sourceBall x s) := by
    rw [← pde_ball_eq_sourceBall x hs]
    exact PDE.isOpen_euclideanBall _ _
  have hmem : x ∈ sourceBall x s := by
    rw [← pde_ball_eq_sourceBall x hs]
    exact PDE.center_mem_euclideanBall x hs
  have hμs := (Measure.mem_support_iff_forall x).1 hxs _ (hopen.mem_nhds hmem)
  have hint : IntegrableOn f (sourceBall x s) := hf.mono_set hsub
  have hns : ∀ᵐ x ∂volume.restrict (sourceBall x s), 0 ≤ f x :=
    ae_restrict_of_ae_restrict_of_subset hsub hn
  rw [show μ (sourceBall x s) = ∫⁻ y, ENNReal.ofReal (f y)
      ∂volume.restrict (sourceBall x s) by
        dsimp only [μ]
        rw [withDensity_apply _ hopen.measurableSet, Measure.restrict_restrict_of_subset hsub]] at hμs
  rw [← ofReal_integral_eq_lintegral_ofReal hint hns] at hμs
  exact ENNReal.ofReal_pos.mp hμs

#print axioms exists_sourceBall_positive_mass_point


/-- Unit weighted mass supplies a coefficient-dependent interior seed ball. -/
theorem native_normalized_exists_interior_seed {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R)
    (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
    (hm : (∫ x in sourceBall (0 : Vec d) R,
      ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1) :
    ∃ (r s : ℝ) (x : Vec d), 0 < r ∧ 0 < s ∧ r + 4 * s ≤ R ∧
      x ∈ sourceBall (0 : Vec d) r ∧
      0 < ∫ z in sourceBall x s, ρ z * (v.toH1Function.toFun z) ^ 2 := by
  let f : Vec d → ℝ := fun z => ρ z * (v.toH1Function.toFun z) ^ 2
  have hf : IntegrableOn f (sourceBall (0 : Vec d) R) := by
    exact v.toH1Function.memL2.integrable_sq.mul_of_top_right
      (uniformlyElliptic_coefficients_memLp_top hκ h (volume.restrict (sourceBall (0 : Vec d) R))).1
  have hn : ∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) R), 0 ≤ f z := by
    exact Filter.Eventually.of_forall (fun z => mul_nonneg
      (le_trans hκ.le (h.2.2 z).1) (sq_nonneg _))
  have hmass : 0 < ∫ z in sourceBall (0 : Vec d) R, f z := by
    have heq : (∫ z in sourceBall (0 : Vec d) R, f z) = 1 := by
      rw [← hm]
      apply integral_congr_ae
      filter_upwards with z
      dsimp only [f]
      ring
    rw [heq]
    norm_num
  obtain ⟨x, hx, hmasspoint⟩ := exists_sourceBall_positive_mass_point R hR f hf hn hmass
  have hxR : euclideanNorm x < R := by simpa only [sourceBall, Set.mem_setOf_eq, sub_zero] using hx
  have hx0 : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  let r := (R + euclideanNorm x) / 2
  let s := (R - r) / 8
  have hr : 0 < r := by dsimp [r]; linarith
  have hs : 0 < s := by dsimp [s, r]; linarith
  have hmargin : r + 4 * s ≤ R := by dsimp [s, r]; linarith
  have hxr : x ∈ sourceBall (0 : Vec d) r := by
    change euclideanNorm (x - 0) < r
    simp only [sub_zero]
    dsimp [r]
    linarith
  have hsub : sourceBall x s ⊆ sourceBall (0 : Vec d) R := by
    rw [← pde_ball_eq_sourceBall x hs, ← pde_ball_eq_sourceBall _ hR]
    apply PDE.euclideanBall_subset_of_center_norm_add_le hs hR
    change euclideanNorm (x - 0) + s ≤ R
    simp only [sub_zero]
    dsimp [s, r]
    linarith
  exact ⟨r, s, x, hr, hs, hmargin, hxr, hmasspoint s hs hsub⟩

#print axioms native_normalized_exists_interior_seed


/-- The actual normalized nonnegative native mode is strictly positive almost
    everywhere on a coefficient-dependent concentric interior ball. -/
theorem exists_dirichlet_native_interior_positive {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eig : ℝ) (v : Homogenization.H10Function (sourceBall (0 : Vec d) R))
      (r a : ℝ), 0 < eig ∧ 0 < r ∧ r < R ∧ 0 < a ∧
      SuperdiffusionCLT.Section7.IsWeakSolutionOn α (sourceBall (0 : Vec d) R)
        v.toH1Function (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0) ∧
      (∫ x in sourceBall (0 : Vec d) R,
        ρ x * v.toH1Function.toFun x * v.toH1Function.toFun x) = 1 ∧
      (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x)) (v.toH1Function.grad x)) = eig ∧
      ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) r), a ≤ v.toH1Function.toFun x := by
  obtain ⟨eig, v, heig, hv0, hweak, hmass, henergy⟩ :=
    exists_dirichlet_native_nonnegative_groundstate hd hκ h R hR
  obtain ⟨r, s, x, hr, hs, hmargin, hx, hseed⟩ :=
    native_normalized_exists_interior_seed hκ h R hR v hmass
  have hsmooth : ∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall (0 : Vec d) R) ψ →
      (∫ z in sourceBall (0 : Vec d) R,
        dot ((α z).mulVec (v.toH1Function.grad z))
          (fun i => fderiv ℝ ψ z (unitVector i))) =
        eig * ∫ z in sourceBall (0 : Vec d) R, (ρ z * v.toH1Function.toFun z) * ψ z := by
    intro ψ hψ
    let φ : Homogenization.H10Function (sourceBall (0 : Vec d) R) :=
      Homogenization.H10Function.ofContDiff (dirichletBall R).isOpen hψ.1 hψ.2.1 hψ.2.2
    have hw := hweak φ
    simp only [Homogenization.vecDot_zero_left, integral_zero, add_zero] at hw
    simpa only [φ, Homogenization.H10Function.ofContDiff, Homogenization.H1Function.ofContDiff,
      Homogenization.basisVec, unitVector, Homogenization.vecDot, Homogenization.matVecMul,
      Matrix.mulVec, dotProduct, dot, integral_const_mul, mul_assoc] using hw
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * r / s)
  have hstep : 2 * r < (n : ℝ) * s := (div_lt_iff₀ hs).mp hn
  have hnpos : 0 < n := by
    have hnreal : (0 : ℝ) < n := lt_of_le_of_lt (by positivity : 0 ≤ 2 * r / s) hn
    exact_mod_cast hnreal
  obtain ⟨C, hC, hchain⟩ := exists_sourceBall_eigenfunction_interior_lower_of_seed_mass d hd
  have hgrad : HasWeakGradient (sourceBall (0 : Vec d) R)
      v.toH1Function.toFun v.toH1Function.grad := by
    intro i
    refine ⟨locallyIntegrableOn_of_locallyIntegrable_restrict
      (v.toH1Function.memL2.locallyIntegrable (by norm_num)),
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((v.toH1Function.gradMemL2 i).locallyIntegrable (by norm_num)), ?_⟩
    intro φ hφ
    simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
      v.toH1Function.hasWeakGradient i φ hφ.1 hφ.2.1 hφ.2.2
  have hlower := hchain κ hκ ρ α h 0 R hR v.toH1Function.toFun v.toH1Function.grad
    v.toH1Function.memL2 v.toH1Function.gradMemL2 hgrad
    eig heig.le hsmooth hv0 r s hr hs hmargin n hnpos hstep x hx _ hseed le_rfl
  let H := Real.exp (C * Real.sqrt ((κ ^ 4)⁻¹))
  let a := Real.sqrt ((∫ z in sourceBall x s, ρ z * (v.toH1Function.toFun z) ^ 2) /
    (κ⁻¹ * volume.real (sourceBall x s))) / H ^ (n + 1) / H ^ (n + 1)
  refine ⟨eig, v, r, a, heig, hr, ?_, hlower.1, hweak, hmass, henergy, hlower.2⟩
  linarith

#print axioms exists_dirichlet_native_interior_positive


end DimensionLift

end

end EinsteinFull.Blueprint.TubeProbability



#lint
