import EinsteinFull.Calculus.SbxBNativeResolventIdentificationR04
import EinsteinFull.Calculus.SbxBNativeL2IsometryR05
import EinsteinFull.Calculus.SbxBPhysicalNativeFormR03
import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace
import MarkovProcess.Semigroup.ResolventGeneration

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace CompactlySupported

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open SubdiffusiveProcess
open MarkovProcess.Semigroup

noncomputable section

/-- The actual killed resolvent satisfies the native variational equation with
its literal physical mass and half-energy coefficients. -/
theorem b_actual_resolvent_eq_native
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
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
  apply b_actual_resolvent_eq_native_of_form_transport r hκ hR hell hcoeff
  · intro u v a b hu hv
    exact (sbxB_physical_native_forms_of_regular hd ω L hω lam R hR ρ α hcoeff
      u v a b hu hv).1
  · intro u v a b hu hv
    exact (sbxB_physical_native_forms_of_regular hd ω L hω lam R hR ρ α hcoeff
      u v a b hu hv).2
  · exact hfg

/-- The canonical physical/native isometry intertwines the actual killed
resolvent with the native shifted variational resolvent on all interior L² data. -/
theorem b_actual_native_resolvent_intertwines
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    let hρ := fun x hx => (hcoeff x hx).1
    let e := bPhysicalNativeL2Equiv hd ω lam L R hω hρ
    e (gmpKilledInteriorResolvent r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen μ f) =
    dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      (bNativeShiftedDirichletResolvent hd hκ hell R hR μ ((μ : ℝ)⁻¹ • e f)) := by
  dsimp only
  let hρ : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x := fun x hx => (hcoeff x hx).1
  let e := bPhysicalNativeL2Equiv hd ω lam L R hω hρ
  have hf : (f.val : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (e f : Vec d → ℝ) :=
    (b_physical_native_l2_isometry_ae_ball hd ω lam L R hω hρ f).symm
  have hr := b_actual_resolvent_eq_native r hκ hR hell hcoeff μ f (e f) hf
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  apply Lp.ext
  exact (b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ _).trans
    ((hac.ae_eq hr).trans (dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) _).symm)

/-- The native spectral heat operators form a strongly continuous contraction semigroup. -/
@[nolint unusedArguments]
def bSpectralHeatSemigroup {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n) :
    StronglyContinuousContractionSemigroup H where
  operator := SpectralHeat.heatOperator b eigenvalue hpos
  operator_zero := SpectralHeat.heatOperator_zero b eigenvalue hpos
  operator_add := SpectralHeat.heatOperator_add b eigenvalue hpos
  opNorm_le_one := fun t =>
    (SpectralHeat.heatOperator b eigenvalue hpos t).opNorm_le_bound zero_le_one
      (fun f => by simpa only [one_mul] using
        SpectralHeat.heatOperator_norm_le b eigenvalue hpos t f)
  continuous_orbit := SpectralHeat.heatOperator_continuous b eigenvalue hpos

/-- Conjugating a contraction semigroup by an onto isometry preserves its evolution. -/
def bConjugateSemigroup {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (S : StronglyContinuousContractionSemigroup E) :
    StronglyContinuousContractionSemigroup F where
  operator t := e.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((S t).comp e.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  operator_zero := by ext x; simp
  operator_add := by intro s t; ext x; simp
  opNorm_le_one := fun t => by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖e (S t (e.symm x))‖ ≤ 1 * ‖x‖
    simpa only [e.norm_map, e.symm.norm_map, one_mul] using S.norm_apply_le t (e.symm x)
  continuous_orbit := fun x => e.continuous.comp (S.continuous (e.symm x))

/-- The resolvent of a conjugated semigroup is the conjugated resolvent. -/
theorem b_conjugate_resolvent {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (e : E ≃ₗᵢ[ℝ] F) (S : StronglyContinuousContractionSemigroup E)
    (μ : PositiveShift) (x : F) :
    (bConjugateSemigroup e S).resolvent μ x = e (S.resolvent μ (e.symm x)) := by
  rw [StronglyContinuousContractionSemigroup.resolvent_apply,
    StronglyContinuousContractionSemigroup.resolvent_apply]
  change _ = e.toLinearIsometry (∫ t in Set.Ioi (0 : ℝ),
    S.laplaceIntegrand μ (e.symm x) t)
  rw [← e.toLinearIsometry.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with t
  simp only [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
    bConjugateSemigroup, ContinuousLinearMap.comp_apply, map_smul]
  rfl

/-- Equality of all resolvents determines a strongly continuous contraction semigroup. -/
theorem b_semigroup_eq_of_resolvents {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (S T : StronglyContinuousContractionSemigroup E)
    (h : ∀ μ, S.resolvent μ = T.resolvent μ) : S = T := by
  have hr : S.toContractiveResolvent = T.toContractiveResolvent := by
    suffices ∀ {R Q : ContractiveResolvent E}, R.operator = Q.operator → R = Q by
      apply this
      funext μ
      exact h μ
    intro R Q hop
    cases R
    cases Q
    simp_all only
  calc
    S = S.toContractiveResolvent.generatedSemigroup :=
      S.generatedSemigroup_toContractiveResolvent.symm
    _ = T.toContractiveResolvent.generatedSemigroup := by rw [hr]
    _ = T := T.generatedSemigroup_toContractiveResolvent

/-- The Laplace resolvent of spectral heat has the expected coordinate multiplier. -/
theorem b_spectral_heat_resolvent_coordinate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (μ : PositiveShift) (f : H) (n : ℕ) :
    b.repr ((bSpectralHeatSemigroup b eigenvalue hpos).resolvent μ f) n =
      ((μ : ℝ) + eigenvalue n)⁻¹ * b.repr f n := by
  let S := bSpectralHeatSemigroup b eigenvalue hpos
  let c : H →L[ℝ] ℝ := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) 2 n).comp
    b.repr.toContinuousLinearEquiv.toContinuousLinearMap
  have hc (x : H) : c x = b.repr x n := rfl
  change c (S.resolvent μ f) = _
  rw [StronglyContinuousContractionSemigroup.resolvent_apply,
    ← c.integral_comp_comm (S.integrableOn_laplaceIntegrand μ.property f)]
  have hi : (∫ t in Set.Ioi (0 : ℝ), c (S.laplaceIntegrand μ f t)) =
      ∫ t in Set.Ioi (0 : ℝ),
        Real.exp (-((μ : ℝ) + eigenvalue n) * t) * b.repr f n := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, map_smul, hc]
    change Real.exp (-(μ : ℝ) * t) *
      b.repr (SpectralHeat.heatOperator b eigenvalue hpos (Real.toNNReal t) f) n = _
    rw [SpectralHeat.heatOperator_repr, Real.coe_toNNReal _ ht.le, ← mul_assoc,
      ← Real.exp_add]
    congr 2; ring
  rw [hi, integral_mul_const,
    StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero
      (add_pos_of_pos_of_nonneg μ.property (hpos n))]

/-- The actual native variational resolvent has the same spectral coordinates. -/
theorem b_native_resolvent_coordinate {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = eigenvalue n * inner ℝ (b n)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (μ : PositiveShift) (g : Lp ℝ 2 (dirichletVolume ρ R)) (n : ℕ) :
    b.repr (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      (bNativeShiftedDirichletResolvent hd hκ hell R hR μ ((μ : ℝ)⁻¹ • g))) n =
        ((μ : ℝ) + eigenvalue n)⁻¹ * b.repr g n := by
  let v := bNativeShiftedDirichletResolvent hd hκ hell R hR μ ((μ : ℝ)⁻¹ • g)
  have hvar := ((b_native_shifted_dirichlet_resolvent_spec hd hκ hell R hR μ).2
    ((μ : ℝ)⁻¹ • g) v).mp rfl
  have hc := dirichletHilbert_shifted_variational_coordinate hκ hell R hR
    eigenvalue hpos u b hb hv (inv_nonneg.mpr μ.property.le) ((μ : ℝ)⁻¹ • g) v hvar n
  rw [map_smul] at hc
  change _ = (1 + (μ : ℝ)⁻¹ * eigenvalue n)⁻¹ *
    ((μ : ℝ)⁻¹ * b.repr g n) at hc
  rw [hc]
  have hμ : (μ : ℝ) ≠ 0 := μ.property.ne'
  have hsum : (μ : ℝ) + eigenvalue n ≠ 0 :=
    (add_pos_of_pos_of_nonneg μ.property (hpos n)).ne'
  field_simp

/-- The actual interior killed evolution is the native spectral heat evolution
under the canonical onto physical/native isometry. -/
theorem b_actual_native_semigroup_intertwines
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = eigenvalue n * inner ℝ (b n)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (t : ℝ≥0)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    let hρ := fun x hx => (hcoeff x hx).1
    let e := bPhysicalNativeL2Equiv hd ω lam L R hω hρ
    e (gmpKilledInteriorSemigroup r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t f) =
        SpectralHeat.heatOperator b eigenvalue hpos t (e f) := by
  dsimp only
  let hρ : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x := fun x hx => (hcoeff x hx).1
  let e := bPhysicalNativeL2Equiv hd ω lam L R hω hρ
  let S := gmpKilledInteriorSemigroup r (sourceBall (0 : Vec d) R)
    (dirichletBall (d := d) R).isOpen
  let T := bSpectralHeatSemigroup b eigenvalue hpos
  change e (S t f) = T t (e f)
  have hr : ∀ μ, (bConjugateSemigroup e S).resolvent μ = T.resolvent μ := by
    intro μ
    apply ContinuousLinearMap.ext
    intro g
    apply b.repr.injective
    apply lp.ext
    funext n
    rw [b_conjugate_resolvent, b_spectral_heat_resolvent_coordinate]
    have hi := b_actual_native_resolvent_intertwines r hκ hR hell hcoeff μ (e.symm g)
    change e (S.resolvent μ (e.symm g)) =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
        (bNativeShiftedDirichletResolvent hd hκ hell R hR μ
          ((μ : ℝ)⁻¹ • e (e.symm g))) at hi
    rw [e.apply_symm_apply] at hi
    rw [hi, b_native_resolvent_coordinate hd hκ hR hell b eigenvalue hpos u hb hv]
  have hs := b_semigroup_eq_of_resolvents (bConjugateSemigroup e S) T hr
  have ht := congrArg (fun V : StronglyContinuousContractionSemigroup _ => V t (e f)) hs
  change e (S t (e.symm (e f))) = T t (e f) at ht
  simpa only [e.symm_apply_apply] using ht

/-- Matching physical and native L² data have matching killed and spectral
evolutions on the ball, for every nonnegative time. -/
theorem b_actual_killed_l2_eq_spectral_of_ae
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = eigenvalue n * inner ℝ (b n)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (t : ℝ≥0) (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hFg : (F : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (g : Vec d → ℝ)) :
    (fun x => gmpKilledL2Operator r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
    (fun x => SpectralHeat.heatOperator b eigenvalue hpos t g x) := by
  let U := sourceBall (0 : Vec d) R
  let hU := (dirichletBall (d := d) R).isOpen
  let hρ : ∀ x ∈ U, ρ x = s4PhysicalRho hd ω lam x := fun x hx => (hcoeff x hx).1
  let e := bPhysicalNativeL2Equiv hd ω lam L R hω hρ
  let F₀ : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω F,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω F⟩
  have hle : dirichletVolume ρ R ≤ physicalReversibleMeasure ω hd lam := by
    rw [b_native_volume_eq_physical_restrict hd ω lam R hρ]
    exact Measure.restrict_le_self
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ U := by
    rw [b_native_volume_eq_physical_restrict hd ω lam R hρ]
    exact ae_restrict_mem hU.measurableSet
  have hp := (physicalZeroBoundaryProjection_ae_eq_indicator U hU hd ω lam L hω F)
    |>.filter_mono (ae_mono hle)
  have hinput : e F₀ = g := by
    apply Lp.ext
    filter_upwards [b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ F₀,
      hp, hball, hFg] with x hx hpx hxU hFx
    exact hx.trans ((hpx.trans (Set.indicator_of_mem hxU F)).trans hFx)
  have hsem := b_actual_native_semigroup_intertwines r hκ hR hell hcoeff
    b eigenvalue hpos u hb hv t F₀
  change e (gmpKilledInteriorSemigroup r U hU t F₀) =
    SpectralHeat.heatOperator b eigenvalue hpos t (e F₀) at hsem
  rw [hinput] at hsem
  have hout := b_physical_native_l2_isometry_ae_native hd ω lam L R hω hρ
    (gmpKilledInteriorSemigroup r U hU t F₀)
  change (e (gmpKilledInteriorSemigroup r U hU t F₀) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
    (fun x => gmpKilledL2 r U hU t (physicalZeroBoundaryProjection U hd ω lam L hω F) x)
      at hout
  have hproj : (fun x => gmpKilledL2 r U hU t
      (physicalZeroBoundaryProjection U hd ω lam L hω F) x) =
      (fun x => gmpKilledL2 r U hU t F x) :=
    congrArg (fun v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) =>
      (v : Vec d → ℝ)) (gmpKilledL2_projection r U hU t F)
  rw [hproj] at hout
  rw [hsem] at hout
  exact hout.symm

/-- A supplied genuine Dirichlet spectrum gives the actual killed evolution,
for every pair of matching physical and native L² representatives. -/
theorem b_actual_killed_l2_eq_supplied_spectral
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (s : DirichletSpectralResolution ρ α R)
    (t : ℝ≥0) (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hFg : (F : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (g : Vec d → ℝ)) :
    (fun x => gmpKilledL2Operator r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t g x) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu hv using fun n =>
    Calculus.c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  have hb (n : ℕ) : spectralHeatBasis s n = J (u n) := by
    have hs : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
      exact congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    rw [hs]
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  apply b_actual_killed_l2_eq_spectral_of_ae r hκ hR hell hcoeff
    (spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) u hb
  · intro n w
    rw [hb n]
    exact hv n w
  · exact hFg

/-- The actual/native killed operator identification for compact continuous tests. -/
theorem b_actual_killed_l2_eq_spectral_on_compact_tests
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    (s : DirichletSpectralResolution ρ α R) (t : ℝ≥0)
    (f : Vec d →C_c ℝ) (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hg : (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f) :
    (fun x => gmpKilledL2Operator r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t g x) := by
  apply b_actual_killed_l2_eq_supplied_spectral r hκ hR hell hcoeff s t F g
  have hρ : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x := fun x hx => (hcoeff x hx).1
  have hle : dirichletVolume ρ R ≤ physicalReversibleMeasure ω hd lam := by
    rw [b_native_volume_eq_physical_restrict hd ω lam R hρ]
    exact Measure.restrict_le_self
  exact (hF.filter_mono (ae_mono hle)).trans hg.symm

#print axioms b_actual_resolvent_eq_native
#print axioms b_actual_native_resolvent_intertwines
#print axioms b_native_resolvent_coordinate
#print axioms b_actual_native_semigroup_intertwines
#print axioms b_actual_killed_l2_eq_spectral_on_compact_tests

end
end EinsteinFull
