import EinsteinFull.Calculus.C11ForcedSignedVelocity
import EinsteinFull.Regeneration.GMPVelocityTransfer

/-! # Signed velocities from the source association and the GMP velocity law

Under the source association of physical origin laws, the GMP velocity law
(`EinsteinFull.Regeneration.gmp_physical_origin_velocity`) gives the strictly signed physical
velocity for every nonzero force, the strictly signed reduced velocity through the flat
environment law, and the literal forced law of large numbers.
-/

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

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

namespace Blueprint

section FlatSourceAssociation

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

end Blueprint
end EinsteinFull
