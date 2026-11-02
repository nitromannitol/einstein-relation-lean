import EinsteinFull.Calculus.C8VelocityTransport
import EinsteinFull.Regeneration.GMPVelocityTransfer
import EinsteinFull.Calculus.C9SignedVelocityTimeChange
import EinsteinFull.Calculus.S2ClockLeftInverseSupport
import EinsteinFull.Calculus.C9ReducedEnvironmentLaw
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_lln

/-! # Signed velocities from the source origin-law association

The source association below is an explicit foundation coverage request. It is
not an extra graph premise and is not claimed to follow from an admitted input.
All force normalization, joint-law transport and velocity transfer are proved
here using the actual physical martingale problems. The reduced-law consumer
pulls a physical law back through the flat coefficient map and uses the graph
clock identity to identify it with the supplied reduced law. No smoothness is assumed.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- Recover the original velocity from a nondegenerate simultaneous transport
of the joint environment law and path kernel. -/
theorem quenchedVelocity_of_reindex {d : ℕ} {Q : Measure (FieldPair d)}
    {P : Kernel (FieldPair d) (Path d)} (e : FieldPair d ≃ᵐ FieldPair d)
    {a : ℝ} (ha : a ≠ 0) {b : ℝ≥0} (hb : 0 < b) {v : Vec d}
    (hv : HasQuenchedVelocity (Q.map e) (reindexVelocityKernel P e a b) v) :
    HasQuenchedVelocity Q P ((a⁻¹ * ((b : ℝ)⁻¹)) • v) := by
  have h := ae_of_ae_map e.measurable.aemeasurable hv
  filter_upwards [h] with ω hω
  rw [reindexVelocityKernel_apply] at hω
  have hγ := (velocityPathHomeomorph ha hb).measurableEmbedding.ae_map_iff.mp hω
  filter_upwards [hγ] with γ hγ
  have hi := hasPathVelocity_velocityPathTransform hγ a⁻¹ (inv_pos.mpr hb)
  change HasPathVelocity
    ((velocityPathHomeomorph ha hb).symm ((velocityPathHomeomorph ha hb) γ)) _ at hi
  simpa only [Homeomorph.symm_apply_apply, NNReal.coe_inv] using hi

section SourceAssociation

variable
  (hFoundationPhysicalOriginLaw :
    ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (mu : ℝ) (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
      (P : Kernel (FieldPair d) (Path d)),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu)
          0 (P ω)) →
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0.le hmu1 P)

include hFoundationPhysicalOriginLaw

/-- Positive forces of arbitrary size are normalized by scaling both coefficient
fields and the path law, with the finite range enlarged explicitly. -/
theorem physical_positive_velocity_of_source_association {d : ℕ} (hd : 2 ≤ d)
    {L R : ℝ} (Q : EnvironmentLaw d L R) {lam : ℝ} (hlam : 0 < lam)
    (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  let c : ℝ := min 1 lam⁻¹
  have hc : 0 < c := lt_min zero_lt_one (inv_pos.mpr hlam)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hmu0 : 0 < c * lam := mul_pos hc hlam
  have hmu1 : c * lam ≤ 1 := by
    calc
      c * lam ≤ lam⁻¹ * lam := mul_le_mul_of_nonneg_right (min_le_right _ _) hlam.le
      _ = 1 := inv_mul_cancel₀ hlam.ne'
  let Qs := scaledEnvironmentLaw Q hc hc1
  let Ps := scaledEnvironmentKernel P c hc
  have hPs : ∀ᵐ ω ∂Qs.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω (c * lam))
        0 (Ps ω) := solvesMartingaleProblem_scaledJointLaw _ lam c hc hP
  have hsource := hFoundationPhysicalOriginLaw d hd L (R / c) Qs
    (c * lam) hmu0 hmu1 Ps hPs
  obtain ⟨v, hv, hpos, _⟩ := Regeneration.gmp_physical_origin_velocity hd Qs hmu0 hmu1 Ps hsource
  have hback := quenchedVelocity_of_reindex
    (scaleEnvironmentHomeomorph d c hc.ne').toMeasurableEquiv
    (inv_ne_zero hc.ne')
    (sq_pos_of_pos (show (0 : ℝ≥0) < NNReal.mk c hc.le from hc)) hv
  have hscalar : (c⁻¹)⁻¹ * (((NNReal.mk c hc.le) ^ (2 : ℕ) : ℝ≥0) : ℝ)⁻¹ = c⁻¹ := by
    simp only [inv_inv, pow_two, NNReal.coe_mul, NNReal.coe_mk, mul_inv_rev]
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [hscalar] at hback
  refine ⟨c⁻¹ • v, hback, ?_⟩
  exact mul_pos hlam (mul_pos (inv_pos.mpr hc) hpos)

/-- The supplied physical law has a strictly signed velocity for every nonzero
real force. Reflection transports the full joint law, without an isotropy premise. -/
theorem physical_signed_velocity_of_source_association {d : ℕ} (hd : 2 ≤ d)
    {L R : ℝ} (Q : EnvironmentLaw d L R) {lam : ℝ} (hlam : lam ≠ 0)
    (P : Kernel (FieldPair d) (Path d))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (P ω)) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure P v ∧
      0 < lam * v (firstCoordinateIndex hd) := by
  rcases lt_or_gt_of_ne hlam with hneg | hpos
  · let e := (reflectEnvironmentHomeomorph d).toMeasurableEquiv
    let Qr := reflectedEnvironmentLaw Q
    let Pr := reindexVelocityKernel P e (-1) 1
    have hPr : ∀ᵐ ω ∂Qr.measure,
        SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω (-lam))
          0 (Pr ω) := by
      apply e.measurableEmbedding.ae_map_iff.mpr
      filter_upwards [hP] with ω hω
      rw [reindexVelocityKernel_apply]
      change SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) (reflectEnvironment ω) (-lam)) 0
        ((P ω).map (velocityPathTransform (-1) 1))
      simpa only [neg_zero] using
        solvesMartingaleProblem_reflectedPath (firstCoordinateIndex hd) ω lam 0 hω
    obtain ⟨v, hv, hsign⟩ := physical_positive_velocity_of_source_association
      hFoundationPhysicalOriginLaw hd Qr (neg_pos.mpr hneg) Pr hPr
    have hback := quenchedVelocity_of_reindex e (a := -1) (by norm_num)
      (b := 1) (by norm_num) hv
    have hv' : HasQuenchedVelocity Q.measure P (-v) := by
      simpa only [inv_neg, inv_one, NNReal.coe_one, mul_one, neg_one_smul] using hback
    refine ⟨-v, hv', ?_⟩
    simpa only [Pi.neg_apply, neg_mul, mul_neg] using hsign
  · exact physical_positive_velocity_of_source_association
      hFoundationPhysicalOriginLaw hd Q hpos P hP

/-- The physical half of the literal forced-LLN contract for the supplied law.
The foundation source association remains explicit until its proved name lands. -/
theorem forced_supplied_physical_velocity_of_source_association
    (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
    (lam : ℝ) (hlam : lam ≠ 0) (X : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω))) :
    ∃ vX : Vec d, HasQuenchedVelocity Q.measure (originLaw X) vX ∧
      0 < lam * vX ⟨0, by omega⟩ :=
  physical_signed_velocity_of_source_association hFoundationPhysicalOriginLaw hd Q hlam
    (originLaw X) hX

end SourceAssociation

section FoundationIdentification

-- Exact planned interface in FOUNDATION.md. This parameter is removed when
-- CARVER-F publishes its proved name; it is not a graph premise.
variable
  (physical_mp_ae_unique :
    ∀ (d : ℕ) (_hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) →
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) →
      ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω))

include physical_mp_ae_unique

/-- A source kernel that solves the actual physical martingale problem identifies
every supplied solution. The source martingale-problem hypothesis is explicit:
source association and uniqueness alone do not discharge it. Indexing the two
given kernels by a redundant spatial variable only adapts the uniqueness API. -/
theorem physical_origin_law_of_source_mp
    {d : ℕ} (hd : 2 ≤ d) {L R : ℝ} (Q : EnvironmentLaw d L R)
    {mu : ℝ} (hmu0 : 0 ≤ mu) (hmu1 : mu ≤ 1)
    (K P : Kernel (FieldPair d) (Path d))
    (hsource : IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0 hmu1 K)
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu) 0 (K ω))
    (hP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu) 0 (P ω)) :
    IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0 hmu1 P := by
  let PX : QuenchedPathLaws d := P.comap Prod.snd measurable_snd
  let KX : QuenchedPathLaws d := K.comap Prod.snd measurable_snd
  have hPX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu)
        0 (PX (0, ω)) := hP
  have hKX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu)
        0 (KX (0, ω)) := hK
  have heq : ∀ᵐ ω ∂Q.measure, P ω = K ω :=
    physical_mp_ae_unique d hd L R Q (firstCoordinateIndex hd) mu PX KX hPX hKX
  filter_upwards [hsource, heq] with ω hω hωeq
  obtain ⟨hreg, realization, hr⟩ := hω
  exact ⟨hreg, realization, hωeq.trans hr⟩

end FoundationIdentification

namespace Blueprint

/-- The zero-potential physical operator is exactly the original reduced
operator, including the divergence and the signed force term. -/
theorem physicalGenerator_zeroPotentialReducedPair {d : ℕ} (i : Fin d)
    (ω : FieldPair d) (lam : ℝ) :
    physicalGenerator i (zeroPotentialReducedPair ω) lam = reducedGenerator i ω lam := by
  funext f x
  unfold physicalGenerator reducedGenerator
  simp_rw [reducedCoefficient_zeroPotentialReducedPair]
  change Real.exp (2 * (0 : ℝ)) / 2 * _ + _ = _
  rw [mul_zero, Real.exp_zero]
  rfl

/-- Transfer an actual physical velocity on the zero-potential environment law
to the supplied reduced law. Both path laws are supplied; the graph's clock
identity identifies their pullbacks without a kernel descent assumption. -/
theorem reduced_velocity_of_flat_physical_law
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
    (Qflat : EnvironmentLaw d (sourceReducedBound L) R)
    (hQflat : Qflat.measure = Q.measure.map zeroPotentialReducedPair)
    (i : Fin d) (lam : ℝ) (K Y : QuenchedPathLaws d)
    (hK : ∀ᵐ ω ∂Qflat.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (K (0, ω)))
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (v : Vec d) (hv : HasQuenchedVelocity Qflat.measure (originLaw K) v) :
    HasQuenchedVelocity Q.measure (originLaw Y) v := by
  have hflat : Measurable (zeroPotentialReducedPair (d := d)) :=
    (Probability.continuous_reduce.fst.prodMk continuous_const).measurable
  let Z : QuenchedPathLaws d := K.comap
    (fun z => (z.1, zeroPotentialReducedPair z.2))
    (measurable_fst.prodMk (hflat.comp measurable_snd))
  have hKpull : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i (zeroPotentialReducedPair ω) lam)
        0 (K (0, zeroPotentialReducedPair ω)) := by
    rw [hQflat] at hK
    exact ae_of_ae_map hflat.aemeasurable hK
  have hZ : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Z (0, ω)) := by
    filter_upwards [hKpull] with ω hω
    rw [physicalGenerator_zeroPotentialReducedPair] at hω
    exact hω
  have hvZ : HasQuenchedVelocity Q.measure (originLaw Z) v := by
    rw [hQflat] at hv
    exact ae_of_ae_map hflat.aemeasurable hv
  obtain ⟨X, _, hX, _⟩ := (h0 d hd L R Q i lam).1
  have hTCY := (h0 d hd L R Q i lam).2 X Y hX hY
  have hTCZ := (h0 d hd L R Q i lam).2 X Z hX hZ
  filter_upwards [Q.regular, hTCY, hTCZ, hvZ] with ω hω hωY hωZ hωv
  have hmaps := (hωY hω).1.symm.trans (hωZ hω).1
  have heq := pathLaw_eq_of_inverseClock_map_eq ω L hω _ _ hmaps
  change ∀ᵐ γ ∂Y (0, ω), HasPathVelocity γ v
  rw [heq]
  exact hωv

section FlatSourceAssociation

-- The same source coverage request used above; no new graph premise.
variable
  (hFoundationPhysicalOriginLaw :
    ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (mu : ℝ) (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
      (P : Kernel (FieldPair d) (Path d)),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω mu)
          0 (P ω)) →
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0.le hmu1 P)

include hFoundationPhysicalOriginLaw

/-- The source physical LLN on the flat environment gives the strictly signed
reduced LLN. The graph dependency supplies the auxiliary actual physical law;
no deterministic reduced clock rate or descended kernel is assumed. -/
theorem forced_reduced_signed_velocity_of_flat_source_association
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
    (Qflat : EnvironmentLaw d (sourceReducedBound L) R)
    (hQflat : Qflat.measure = Q.measure.map zeroPotentialReducedPair)
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) v ∧
      0 < lam * v ⟨0, by omega⟩ := by
  obtain ⟨K, _, hK, _⟩ :=
    (h0 d hd (sourceReducedBound L) R Qflat (⟨0, by omega⟩ : Fin d) lam).1
  obtain ⟨v, hv, hsign⟩ := forced_supplied_physical_velocity_of_source_association
    hFoundationPhysicalOriginLaw d hd _ R Qflat lam hlam K hK
  exact ⟨v, reduced_velocity_of_flat_physical_law
    h0 d hd L R Q Qflat hQflat _ lam K Y hK hY v hv, hsign⟩

/-- Instantiate the actual flat environment law. The only remaining source
hypothesis is the same explicit physical association request used above. -/
theorem forced_reduced_signed_velocity_of_source_association
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω))) :
    ∃ v : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) v ∧
      0 < lam * v ⟨0, by omega⟩ := by
  apply forced_reduced_signed_velocity_of_flat_source_association
    hFoundationPhysicalOriginLaw h0 d hd L R Q (flatReducedEnvironmentLaw Q)
    _ lam hlam Y hY
  exact flatReducedEnvironmentLaw_measure Q

/-- Assemble the literal forced-LLN statement once the actual physical source
association is supplied. This conditional helper does not close the graph node. -/
theorem forced_lln_of_source_association
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmt := by
  intro d hd L R Q lam hlam X Y hX hY
  obtain ⟨vX, hvX, hsignX⟩ := forced_supplied_physical_velocity_of_source_association
    hFoundationPhysicalOriginLaw d hd L R Q lam hlam X hX
  obtain ⟨vY, hvY, hsignY⟩ := forced_reduced_signed_velocity_of_source_association
    hFoundationPhysicalOriginLaw h0 d hd L R Q lam hlam Y hY
  exact ⟨vX, vY, hvX, hvY, hsignX, hsignY⟩

end FlatSourceAssociation

section FoundationConsumer

-- Exact planned FOUNDATION interfaces, pending their proved names.
variable
  (physical_mp_ae_unique :
    ∀ (d : ℕ) (_hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) →
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) →
      ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω))
  (foundation_gmp_physical_origin_law_and_mp :
    ∀ {d : ℕ} (hd : 2 ≤ d) {L R : ℝ} (hL : 1 ≤ L)
      (Q : EnvironmentLaw d L R) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1),
      ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
        IsGMPPhysicalOriginLaw hd hL Q lam h0 h1 K ∧
        (∀ᵐ ω ∂Q.measure,
          SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam)
            0 (K ω)))

include physical_mp_ae_unique foundation_gmp_physical_origin_law_and_mp

/-- The literal forced LLN follows from the two exact planned foundation
interfaces. Both the source association and the martingale problem belong to
the same canonical kernel before uniqueness identifies the supplied law.
This conditional consumer does not close the graph node. -/
theorem forced_lln_of_foundation
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmt := by
  refine forced_lln_of_source_association ?_ h0
  intro d hd L R Q mu hmu0 hmu1 P hP
  obtain ⟨K, _, hsource, hK⟩ := foundation_gmp_physical_origin_law_and_mp
    hd Q.ellipticity_parameter Q mu hmu0.le hmu1
  exact physical_origin_law_of_source_mp physical_mp_ae_unique hd Q hmu0.le hmu1
    K P hsource hK hP

/-- Retain the two ordered graph premises in the foundation consumer. The flat
environment route already proves the needed bounds from the environment law,
so the separate reduced-bounds premise is redundant in this proof.
The two planned foundation interfaces remain explicit conditional inputs. -/
theorem forced_lln_two_deps_of_foundation
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (_h1 : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmt := by
  exact forced_lln_of_foundation physical_mp_ae_unique
    foundation_gmp_physical_origin_law_and_mp h0

end FoundationConsumer

/-- A scalar reduced displacement limit determines the clock rate, once the
physical velocity has a nonzero coordinate. No reduced vector limit is used. -/
private theorem clockRate_of_longitudinal_limit {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L : ℝ) (hω : IsRegular L ω) (i : Fin d) (vX : Vec d)
    (hX : HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) vX)
    (hne : vX i ≠ 0) (ell : ℝ)
    (hell : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 ell)) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ (ell / vX i) := by
  let A := Clock.physicalPathClock ω γ
  let X := Clock.InverseMeaningV3.inverseClockPath ω γ L hω
  have hAtop : Tendsto A atTop atTop :=
    Clock.physicalPathClock_tendsto_atTop ω γ L hω.2.1
  have hXA : ∀ t, X (A t) = γ t :=
    Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ L hω
  have hXc : Tendsto (fun t : ℝ≥0 => (A t : ℝ)⁻¹ * X (A t) i)
      atTop (𝓝 (vX i)) := by
    exact (tendsto_pi_nhds.1 hX i).comp hAtop
  have hratio := hell.div hXc hne
  have hnonzero := hXc.eventually_ne hne
  have hApos : ∀ᶠ t in atTop, (A t : ℝ) ≠ 0 := by
    exact (NNReal.tendsto_coe_atTop.mpr hAtop).eventually_ne_atTop 0
  apply Tendsto.congr' _ hratio
  filter_upwards [hnonzero, hApos] with t ht hAt
  have hcoord : (A t : ℝ) / t * ((A t : ℝ)⁻¹ * X (A t) i) =
      (t : ℝ)⁻¹ * γ t i := by
    have hcancel : (A t : ℝ) / t * (A t : ℝ)⁻¹ = (t : ℝ)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ hAt, one_mul]
    rw [← hXA t, ← mul_assoc, hcancel]
  exact (div_eq_iff ht).mpr hcoord.symm

/-- The remaining reduced LLN obligation can be scalar: a deterministic first
coordinate limit supplies the actual clock rate and hence the full strictly
signed reduced velocity. This helper does not assert existence of that limit. -/
theorem forced_reduced_signed_velocity_of_longitudinal_limit
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (lam : ℝ) (X Y : QuenchedPathLaws d)
    (hXMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω)))
    (hYMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (vX : Vec d) (hvX : HasQuenchedVelocity Q.measure (originLaw X) vX)
    (hsigned : 0 < lam * vX ⟨0, by omega⟩)
    (ell : ℝ)
    (hell : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω,
      Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t ⟨0, by omega⟩)
        atTop (𝓝 ell)) :
    ∃ vY : Vec d, HasQuenchedVelocity Q.measure (originLaw Y) vY ∧
      0 < lam * vY ⟨0, by omega⟩ := by
  let i : Fin d := ⟨0, by omega⟩
  let η := ell / vX i
  have hne : vX i ≠ 0 := by
    intro hz
    have hz' : lam * vX i = 0 := by rw [hz, mul_zero]
    exact (ne_of_gt hsigned) hz'
  have hTC := (h0 d hd Λ r Q i lam).2 X Y hXMP hYMP
  have hrate : HasReducedClockRate Q Y η := by
    filter_upwards [Q.regular, hTC, hvX, hell] with ω hω hωTC hωX hωell
    have hmeas : AEMeasurable
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω) :=
      ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := Λ)).comp
        (measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d Λ)).prodMk
          measurable_id)).aemeasurable
    have hωX' : ∀ᵐ γ ∂(Measure.map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω)),
        HasPathVelocity γ vX := by
      rw [originLaw_apply, ← (hωTC hω).1]
      exact hωX
    have hpull := ae_of_ae_map hmeas hωX'
    filter_upwards [hpull, hωell] with γ hγX hγell
    exact clockRate_of_longitudinal_limit ω γ Λ hω i vX hγX hne ell hγell
  obtain ⟨ω, hω, hωMP, hωrate⟩ := (Q.regular.and (hYMP.and hrate)).exists
  let : IsProbabilityMeasure (originLaw Y ω) := hωMP.1
  obtain ⟨γ, hγrate⟩ := hωrate.exists
  have hlo : ∀ᶠ t : ℝ≥0 in atTop,
      Real.exp (-2 * Λ) ≤ (Clock.physicalPathClock ω γ t : ℝ) / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact (le_div_iff₀ (NNReal.coe_pos.mpr ht)).2
      (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ Λ hω.2.1 t).1
  have hηpos : 0 < η := lt_of_lt_of_le (Real.exp_pos _) (ge_of_tendsto hγrate hlo)
  refine ⟨η • vX, c9_reduced_velocity_of_physical_velocity_and_clock_rate
    h0 d hd Λ r Q lam X Y hXMP hYMP vX hvX η hηpos hrate, ?_⟩
  change 0 < lam * (η * vX i)
  calc
    0 < η * (lam * vX i) := mul_pos hηpos hsigned
    _ = lam * (η * vX i) := by ring

end Blueprint
end EinsteinFull
