import EinsteinFull.Calculus.SbxBPhysicalNativeFormR03
import EinsteinFull.Calculus.SbxBNativeResolventIdentificationR04
import EinsteinFull.Calculus.SbxBEveryStartNativeRowsR07

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

/-- The physical mass and energy forms are the same positive multiple of the
normalized native forms on paired zero-boundary functions. -/
theorem b_normalized_physical_native_forms
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (L : ℝ) (hω : IsRegular L ω)
    (lam R : ℝ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (u v : physicalH1ZeroBoundary (sourceBall (0 : Vec d) R) hd lam)
    (a b : DirichletHilbertSpace (d := d) R hR)
    (hu : b_physical_native_paired hd lam R hR u a)
    (hv : b_physical_native_paired hd lam R hR v b) :
    ((∫ x, densityWeightedH1SpaceValue u.1 x * densityWeightedH1SpaceValue v.1 x
        ∂physicalReversibleMeasure ω hd lam) =
      c * ∫ x in sourceBall (0 : Vec d) R, ρ x * a.val none x * b.val none x) ∧
    ((∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u.1)
        (physicalH1SpaceRepresentative hd lam v.1) x ∂physicalReversibleMeasure ω hd lam) =
      c * ∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => a.val (some i) x)) (fun i => b.val (some i) x)) := by
  have hmatch : ∀ x ∈ sourceBall (0 : Vec d) R,
      c * ρ x = s4PhysicalRho hd ω lam x ∧
      c • α x = s4PhysicalAlpha hd ω lam x := by
    intro x hx
    rcases hcoeff x hx with ⟨hρ, hα⟩
    constructor
    · rw [hρ]; field_simp
    · rw [hα, smul_smul, mul_inv_cancel₀ (ne_of_gt hc), one_smul]
  have h := sbxB_physical_native_forms_of_regular hd ω L hω lam R hR
    (fun x => c * ρ x) (fun x => c • α x) hmatch u v a b hu hv
  constructor
  · rw [h.1, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    ring
  · rw [h.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change dotProduct ((c • α x).mulVec (fun i => a.val (some i) x))
      (fun i => b.val (some i) x) = _
    rw [Matrix.smul_mulVec, smul_dotProduct]
    rfl


/-- Common positive coefficient normalization preserves the actual killed
resolvent as a function on the ball. -/
theorem b_normalized_actual_resolvent_eq_native
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
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
    have hforms := b_normalized_physical_native_forms hd ω L hω lam R hR c hc ρ α
      hcoeff u v a b ha' hv'
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
        ∂physicalReversibleMeasure ω hd lam) = c * inner ℝ g (J b) := by
      rw [dirichletVolume_inner_eq_native hκ hell R g (J b) f.val
        (densityWeightedH1SpaceValue v.1)
        (hac.ae_eq hfg.symm)
        ((dirichletHilbertInclusion_coe ρ R hR κ⁻¹
          (fun x _ => (hell.2.2 x).2.1) b).trans (hac.ae_eq hv.symm))]
      rw [Work.W5.gantert_integral_physicalMeasure, ← integral_const_mul]
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
          have hρ := (hcoeff x hx).1
          change ρ x = physicalReversibleDensity ω hd lam x / c at hρ
          rw [hρ]
          field_simp
    rw [integral_add hm (he.const_mul _), integral_const_mul, real_inner_smul_left]
    rw [hforms.1, hforms.2, hforce] at hphysical
    have hne : (μ : ℝ) ≠ 0 := ne_of_gt μ.property
    apply (mul_left_cancel₀ (ne_of_gt hc))
    field_simp [hne] at hphysical ⊢
    dsimp only [J, U] at hphysical ⊢
    simp only [one_div] at hphysical ⊢
    linarith
  have hactual := s9_killed_resolvent_eq_physical_variational r U
    (dirichletBall (d := d) R).isOpen μ f
  have hvalue := physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω u
  rw [hactual] at hvalue
  have hvalue' := (Measure.absolutelyContinuous_of_le
    (Measure.restrict_le_self : volume.restrict U ≤ (volume : Measure (Vec d)))).ae_eq hvalue
  rw [← hvar]
  exact hvalue'.trans ha


/-- A positive elliptic density has the same null sets as Lebesgue measure on
 the ball. -/
theorem b_normalized_native_ae_ball {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (p : Vec d → Prop) (hp : ∀ᵐ x ∂dirichletVolume ρ R, p x) :
    ∀ᵐ x ∂volume.restrict (sourceBall (0 : Vec d) R), p x := by
  have h := (ae_withDensity_iff hell.1.ennreal_ofReal).mp hp
  filter_upwards [h] with x hx
  exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le hκ (hell.2.2 x).1)))

/-- A scaling isometry transports the normalized physical resolvent to the
native shifted resolvent. The hypothesis states only its action on L² values. -/
theorem b_normalized_resolvent_intertwines_of_isometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (e : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω ≃ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R))
    (he : ∀ f, (e f : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => Real.sqrt c * f.val x))
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω) :
    e (gmpKilledInteriorResolvent r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen μ f) =
    dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      (bNativeShiftedDirichletResolvent hd hκ hell R hR μ ((μ : ℝ)⁻¹ • e f)) := by
  let k := Real.sqrt c
  have hk : k ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  let g : Lp ℝ 2 (dirichletVolume ρ R) := k⁻¹ • e f
  have hfg : (f.val : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (g : Vec d → ℝ) := by
    have hsm := b_normalized_native_ae_ball hκ hell _ (Lp.coeFn_smul k⁻¹ (e f))
    filter_upwards [he f, hsm] with x hx hs
    rw [hs]
    change f.val x = k⁻¹ * (e f) x
    rw [hx]
    change f.val x = k⁻¹ * (k * f.val x)
    rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  have hr := b_normalized_actual_resolvent_eq_native r hκ hR c hc hell hcoeff μ f g hfg
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  let A := bNativeShiftedDirichletResolvent hd hκ hell R hR μ
  have hright : J (A ((μ : ℝ)⁻¹ • e f)) = k • J (A ((μ : ℝ)⁻¹ • g)) := by
    dsimp only [g]
    simp only [map_smul, smul_smul]
    congr 1
    field_simp
  rw [hright]
  apply Lp.ext
  have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : Vec d) R) :=
    withDensity_absolutelyContinuous _ _
  have hj := dirichletHilbertInclusion_coe ρ R hR κ⁻¹
    (fun x _ => (hell.2.2 x).2.1) (A ((μ : ℝ)⁻¹ • g))
  filter_upwards [hac.ae_eq (he _), hac.ae_eq hr, hj,
    Lp.coeFn_smul k (J (A ((μ : ℝ)⁻¹ • g)))] with x he' hr' hj' hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [he', hs, hr']
  change k * (A ((μ : ℝ)⁻¹ • g)).val none x = k * (J (A ((μ : ℝ)⁻¹ • g))) x
  exact congrArg (fun z : ℝ => k * z) hj'.symm


/-- The scaling isometry intertwines the killed and spectral semigroups. -/
theorem b_normalized_semigroup_intertwines_of_isometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (e : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω ≃ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R))
    (he : ∀ f, (e f : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => Real.sqrt c * f.val x))
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
    e (gmpKilledInteriorSemigroup r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t f) =
      SpectralHeat.heatOperator b eigenvalue hpos t (e f) := by
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
    have hi := b_normalized_resolvent_intertwines_of_isometry r hκ hR c hc hell hcoeff
      e he μ (e.symm g)
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


/-- Compact tests have the normalized native spectral evolution whenever the
scaling isometry exists. -/
theorem b_normalized_compact_test_evolution_of_isometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (e : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω ≃ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R))
    (he : ∀ f, (e f : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => Real.sqrt c * f.val x))
    (s : DirichletSpectralResolution ρ α R) (t : ℝ≥0)
    (f : Vec d →C_c ℝ) (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hF : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hg : (g : Vec d → ℝ) =ᵐ[dirichletVolume ρ R] f) :
    (fun x => gmpKilledL2Operator r (sourceBall (0 : Vec d) R)
      (dirichletBall (d := d) R).isOpen t F x) =ᵐ[dirichletVolume ρ R]
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t g x) := by
  classical
  let U := sourceBall (0 : Vec d) R
  let hU := (dirichletBall (d := d) R).isOpen
  let k := Real.sqrt c
  have hk : k ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hac : dirichletVolume ρ R ≪ volume.restrict U := withDensity_absolutelyContinuous _ _
  have hPN (p : Vec d → Prop) (hp : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, p x) :
      ∀ᵐ x ∂dirichletVolume ρ R, p x := by
    have hv := (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) p).mp hp
    exact hac.ae_le ((ae_mono (Measure.restrict_le_self : volume.restrict U ≤ volume)) hv)
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ U :=
    hac.ae_le (ae_restrict_mem hU.measurableSet)
  let F₀ : physicalZeroBoundaryL2 U hd ω lam L hω :=
    ⟨physicalZeroBoundaryProjection U hd ω lam L hω F,
      physicalZeroBoundaryProjection_mem U hd ω lam L hω F⟩
  have hp := hPN _ (physicalZeroBoundaryProjection_ae_eq_indicator U hU hd ω lam L hω F)
  have hinput : e F₀ = k • g := by
    apply Lp.ext
    filter_upwards [hac.ae_eq (he F₀), hp, hball, hPN _ hF, hg, Lp.coeFn_smul k g]
      with x he' hp' hx hF' hg' hs'
    simp only [Pi.smul_apply, smul_eq_mul] at hs'
    rw [he', hs', hp', Set.indicator_of_mem hx, hF', hg']
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu hv using fun n =>
    Calculus.c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  have hb (n : ℕ) : spectralHeatBasis s n = J (u n) := by
    have hs' : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
      exact congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    rw [hs']
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  have hv' : ∀ n w, (∫ x in U,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (spectralHeatBasis s n) (J w) := by
    intro n w
    rw [hb n]
    exact hv n w
  have hsem := b_normalized_semigroup_intertwines_of_isometry r hκ hR c hc hell hcoeff
    e he (spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) u hb hv' t F₀
  rw [hinput, map_smul] at hsem
  have hout := hac.ae_eq (he (gmpKilledInteriorSemigroup r U hU t F₀))
  change (e (gmpKilledInteriorSemigroup r U hU t F₀) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
    (fun x => k * gmpKilledL2 r U hU t (physicalZeroBoundaryProjection U hd ω lam L hω F) x)
      at hout
  have hproj : (fun x => gmpKilledL2 r U hU t
      (physicalZeroBoundaryProjection U hd ω lam L hω F) x) =
      (fun x => gmpKilledL2 r U hU t F x) :=
    congrArg (fun v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) =>
      (v : Vec d → ℝ)) (gmpKilledL2_projection r U hU t F)
  have hproj' := congrFun hproj
  simp_rw [hproj'] at hout
  rw [hsem] at hout
  filter_upwards [hout, Lp.coeFn_smul k
    (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t g)] with x hx hs'
  simp only [Pi.smul_apply, smul_eq_mul] at hs'
  exact mul_left_cancel₀ hk (hx.symm.trans hs')


/-- The literal L² measure-scaling ingredient for a common coefficient
normalization. It makes no assertion about killed processes or spectral rows. -/
def BNormalizedPhysicalScalingIsometry {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam L R : ℝ) (hω : IsRegular L ω) (ρ : Vec d → ℝ) (c : ℝ) : Prop :=
  ∃ e : physicalZeroBoundaryL2 (sourceBall (0 : Vec d) R) hd ω lam L hω ≃ₗᵢ[ℝ]
      Lp ℝ 2 (dirichletVolume ρ R),
    ∀ f, (e f : Vec d → ℝ) =ᵐ[volume.restrict (sourceBall (0 : Vec d) R)]
      (fun x => Real.sqrt c * f.val x)

/-- A scaling isometry gives the actual killed row with the supplied
source-normalized kernel at every interior start and positive time. -/
theorem b_normalized_every_start_row_of_scaling_isometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (hisom : BNormalizedPhysicalScalingIsometry hd ω lam L R hω ρ c)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (hs : Tendsto (Classical.choose hK.2).eigenvalue atTop atTop)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (y : Vec d) (hy : y ∈ sourceBall 0 R) :
    gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
      volume.withDensity ((sourceBall (0 : Vec d) R).indicator (fun x => ENNReal.ofReal
        ((ρ x / ρ y) * K (t : ℝ) x y))) := by
  classical
  obtain ⟨e, he⟩ := hisom
  let s := Classical.choose hK.2
  have hspec := Classical.choose_spec hK.2
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  choose u hu hv using fun n =>
    Calculus.c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  have hb (n : ℕ) : spectralHeatBasis s n = J (u n) := by
    have hs' : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) := by
      exact congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
    rw [hs']
    apply Lp.ext
    exact (s.square_integrable n).coeFn_toLp.trans (hu n).symm
  have hrow := s10_actual_killed_row_eq_spectral_of_ae_operator_identification
    hd L hL ω hω lam h0 h1 r hκ hR hell s hs u hb hv t ht
    (fun f F g hF hg => b_normalized_compact_test_evolution_of_isometry
      r hκ hR c hc hell hcoeff e he s t f F g hF hg) y hy
  have hB : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  rw [withDensity_indicator hB, hrow,
    s10_spectral_row_source_normalization hd hκ hR hell s hs t ht y hy]
  apply withDensity_congr_ae
  filter_upwards [ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet] with x hx
  have hswap : (∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
      s.eigenfunction n y * s.eigenfunction n x) =
      ∑' n, Real.exp (-s.eigenvalue n * (t : ℝ)) *
        s.eigenfunction n x * s.eigenfunction n y :=
    tsum_congr (fun _ => by ring)
  rw [hswap, (hspec (t : ℝ) ht x hx y hy).2]


/-- Spectral escape follows from ellipticity, leaving only the explicit
measure-scaling isometry as the separate ingredient. -/
theorem b_normalized_every_start_supplied_row_of_scaling_isometry
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) (c : ℝ) (hc : 0 < c)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x / c ∧
      α x = c⁻¹ • s4PhysicalAlpha hd ω lam x)
    (hisom : BNormalizedPhysicalScalingIsometry hd ω lam L R hω ρ c)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ y ∈ sourceBall 0 R,
      gmpKilledEndpointKernel r (sourceBall 0 R) (dirichletBall (d := d) R).isOpen t y =
        volume.withDensity ((sourceBall (0 : Vec d) R).indicator (fun x => ENNReal.ofReal
          ((ρ x / ρ y) * K (t : ℝ) x y))) := by
  intro t ht y hy
  exact b_normalized_every_start_row_of_scaling_isometry r hκ hR c hc hell hcoeff hisom hK
    (Calculus.br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell (Classical.choose hK.2))
    t ht y hy

/-- The physical reversible measure restricted to the ball is the positive
constant multiple of the normalized native measure. -/
theorem b_normalized_physical_restrict_eq_smul_native {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam R c : ℝ) (hc : 0 < c) {ρ : Vec d → ℝ} (hρm : Measurable ρ)
    (hρ : ∀ x ∈ sourceBall (0 : Vec d) R, ρ x = s4PhysicalRho hd ω lam x / c) :
    (physicalReversibleMeasure ω hd lam).restrict (sourceBall (0 : Vec d) R) =
      ENNReal.ofReal c • dirichletVolume ρ R := by
  have hρ' : ∀ x ∈ sourceBall (0 : Vec d) R, c * ρ x = s4PhysicalRho hd ω lam x := by
    intro x hx
    rw [hρ x hx]
    field_simp
  rw [← b_native_volume_eq_physical_restrict hd ω lam R hρ']
  change (volume.restrict (sourceBall (0 : Vec d) R)).withDensity
    (fun x => ENNReal.ofReal (c * ρ x)) = _
  simp_rw [ENNReal.ofReal_mul hc.le]
  exact withDensity_smul _ hρm.ennreal_ofReal

#print axioms b_normalized_every_start_supplied_row_of_scaling_isometry
#print axioms b_normalized_physical_restrict_eq_smul_native
#print axioms b_normalized_every_start_row_of_scaling_isometry
#print axioms b_normalized_compact_test_evolution_of_isometry
#print axioms b_normalized_semigroup_intertwines_of_isometry
#print axioms b_normalized_resolvent_intertwines_of_isometry
#print axioms b_normalized_physical_native_forms
#print axioms b_normalized_actual_resolvent_eq_native
end EinsteinFull
