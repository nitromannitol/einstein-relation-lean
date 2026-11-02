import EinsteinFull.Calculus.C1SublinearScalarScaling
import EinsteinFull.Calculus.C6SublinearSkewGaugeRepresentative

open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

namespace C6SublinearPair

/-- Returning to the original coefficient amplitude contracts the tensor norm. -/
theorem inverse_ellipticityScale_le_one {L : ℝ} (hL : 1 ≤ L) :
    (ellipticityScale L)⁻¹ ≤ 1 := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hexp : 1 ≤ Real.exp (2 * L) := Real.one_le_exp (by positivity)
  have hscale : 1 ≤ ellipticityScale L := by
    exact le_trans hL (le_mul_of_one_le_left hLpos.le hexp)
  exact inv_le_one_of_one_le₀ hscale

/-- Spatial dilation and coefficient normalization of the corrected source
representative produce the literal physical column divergence. -/
theorem physical_skew_representative
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (correctorUnitVector i).ofLp)
    (S : FluxCorrector φ) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ (w : Vec d → Mat d) (A : Mat d),
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => w x j k)) ∧
      (∀ x, (w x).transpose = -(w x)) ∧
      w =ᵐ[(volume : Measure (Vec d))]
        (fun x => -(ellipticityScale D.ellipticity)⁻¹ •
          (C1SublinearScalarScaling.physicalSkew D.dependenceRange
            (S.potential (project (r₀ := D.dependenceRange)
              Q.ellipticity_parameter ω)) x) + A) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        (∑ k : Fin d, fderiv ℝ (fun y => w y k j) x (unitVector k)) =
          (((reduce ω.1).1 x).mulVec (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x (reduce ω.1))))) j -
            homogenizedCoefficient Q j i := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  have hr : 0 < D.dependenceRange := zero_lt_one.trans_le Q.range_parameter
  have hid := EinsteinFull.Calculus.C5TestCLT.sourceCorrector_canonical_grad_identification
    Q i φ.toSourceCorrector
  have htarget := c6_unitCenteredFlux_physical_target Q i φ hid
  filter_upwards [sublinear_source_skew_smooth_representative_mod_const
    d hd D Q hQ i φ S, htarget] with ω hω htω
  obtain ⟨v, A, hvc, hvskew, hvae, hvdiv⟩ := hω
  let t : ℝ := (ellipticityScale D.ellipticity)⁻¹
  let r : ℝ := D.dependenceRange
  let w : Vec d → Mat d := fun x => t • (r • v (r⁻¹ • x))
  have hwc (j k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (fun x => w x j k) := by
    exact contDiff_const.mul
      (C1SublinearScalarScaling.physicalPotential_contDiff (hvc j k))
  refine ⟨w, t • (r • A), hwc, ?_, ?_, ?_⟩
  · intro x
    change (t • (r • v (r⁻¹ • x))).transpose = -(t • (r • v (r⁻¹ • x)))
    rw [Matrix.transpose_smul, Matrix.transpose_smul, hvskew, smul_neg, smul_neg]
  · have hdil := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (inv_ne_zero hr.ne')).ae hvae
    filter_upwards [hdil] with x hx
    change t • (r • v (r⁻¹ • x)) = _
    rw [hx, smul_add, smul_add, smul_neg, smul_neg, neg_smul]
    rfl
  · have hdil := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
      (inv_ne_zero hr.ne')).ae hvdiv
    filter_upwards [hdil, htω] with x hx htx
    intro j
    calc
      (∑ k : Fin d, fderiv ℝ (fun y => w y k j) x (unitVector k)) =
          t * ∑ k : Fin d, fderiv ℝ (fun y => v y k j) (r⁻¹ • x) (unitVector k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        change fderiv ℝ (fun y => t *
          C1SublinearScalarScaling.physicalPotential r (fun z => v z k j) y)
            x (unitVector k) = _
        rw [fderiv_const_mul
          ((C1SublinearScalarScaling.physicalPotential_contDiff (hvc k j)).differentiable
            (by norm_num)).differentiableAt,
          smul_apply, smul_eq_mul,
          C1SublinearScalarScaling.physicalPotential_fderiv hr
            ((hvc k j).differentiable (by norm_num))]
      _ = _ := by rw [hx j]; exact htx j

/-- A constant matrix gauge and sign preserve oscillations, while the inverse
coefficient amplitude can only decrease their Frobenius mean square root. -/
theorem rms_gauge_le {d : ℕ} {w v : Vec d → Mat d} {A : Mat d} {t : ℝ}
    (ht : 0 ≤ t) (htone : t ≤ 1)
    (hw : w =ᵐ[(volume : Measure (Vec d))] (fun x => -t • v x + A))
    (B : Set (Vec d)) (b : Mat d) :
    Real.sqrt ((volume B).toReal⁻¹ *
      ∫ x in B, frobeniusNorm (w x - (A - t • b)) ^ 2) ≤
    Real.sqrt ((volume B).toReal⁻¹ *
      ∫ x in B, frobeniusNorm (v x - b) ^ 2) := by
  have heq : (∫ x in B, frobeniusNorm (w x - (A - t • b)) ^ 2) =
      ∫ x in B, t ^ 2 * frobeniusNorm (v x - b) ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hw] with x hx
    rw [hx]
    have hmat : -t • v x + A - (A - t • b) = (-t) • (v x - b) := by
      simp only [smul_sub, neg_smul]
      abel
    rw [hmat, frobeniusNorm_smul, mul_pow, sq_abs, neg_sq]
  rw [heq, integral_const_mul]
  rw [show (volume B).toReal⁻¹ *
      (t ^ 2 * ∫ x in B, frobeniusNorm (v x - b) ^ 2) =
      t ^ 2 * ((volume B).toReal⁻¹ *
        ∫ x in B, frobeniusNorm (v x - b) ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) htone

end C6SublinearPair

/-- The same selected source pair supplies the smooth scalar and skew
potentials, with joint oscillations on common measurable good events. -/
theorem c6_sublinear_pair_of_source_representatives :
    node_e_u3A_sublinear_u2D_pairStmt := by
  classical
  intro d hd D
  obtain ⟨κ, C, c, hκ, hκhalf, hC, hc, hpairs⟩ :=
    exists_sourcePairs_normalized_joint_class d hd D
  refine ⟨κ, C, c, hκ, hκhalf, hC, hc, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, u, v, _huclass, hvclass, hu, hosc⟩ := hpairs Q hQ
  have hrep := ae_all_iff.mpr fun i =>
    C6SublinearPair.physical_skew_representative d hd D Q hQ i (φ i) (S i)
  obtain ⟨B, hB, hBnull, hBp⟩ :=
    C1SublinearScalarScaling.measurable_common_event _ _ (hvclass.and hrep)
  let w : PhysicalField d D.ellipticity → Fin d → Vec d → Mat d := fun ω i =>
    if h : ω ∈ B then Classical.choose ((hBp ω h).2 i) else fun _ => 0
  have hw (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :=
    Classical.choose_spec ((hBp ω hω).2 i)
  have hw_eq (ω : PhysicalField d D.ellipticity) (hω : ω ∈ B) (i : Fin d) :
      w ω i = Classical.choose ((hBp ω hω).2 i) := dite_eq_left hω
  let W : Fin d → FieldPair d → Vec d → Mat d := fun i =>
    C1SublinearScalarScaling.reducedSkew (fun ω => w ω i)
  have hW_eq (ω : PhysicalField d D.ellipticity) (i : Fin d) :
      W i (reduce ω.1) = w ω i :=
    C1SublinearScalarScaling.reducedSkew_reduce _ _
  have hBae : ∀ᵐ ω ∂physicalReferenceLaw Q, ω ∈ B := ae_iff.mpr hBnull
  have hW : ∀ᵐ ρ ∂reducedLaw Q, ∀ i : Fin d,
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => W i ρ x j k)) ∧
      (∀ x, (W i ρ x).transpose = -(W i ρ x)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        (∑ k : Fin d, fderiv ℝ (fun y => W i ρ y k j) x (unitVector k)) =
          ((ρ.1 x).mulVec (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ρ)))) j -
            homogenizedCoefficient Q j i := by
    let p : FieldPair d → Prop := fun ρ => ∀ i : Fin d,
      (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => W i ρ x j k)) ∧
      (∀ x, (W i ρ x).transpose = -(W i ρ x)) ∧
      ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j : Fin d,
        (∑ k : Fin d, fderiv ℝ (fun y => W i ρ y k j) x (unitVector k)) =
          ((ρ.1 x).mulVec (unitVector i +
            WithLp.ofLp (correctorGradient Q i (translate x ρ)))) j -
            homogenizedCoefficient Q j i
    change ∀ᵐ ρ ∂reducedLaw Q, p ρ
    rw [← C1SublinearScalarScaling.map_physicalReduce Q,
      (C1SublinearScalarScaling.measurableEmbedding_physicalReduce
        D.ellipticity).ae_map_iff]
    filter_upwards [hBae] with ω hω
    intro i
    rw [hW_eq, hw_eq ω hω i]
    obtain ⟨A, hAc, hAskew, _hAclass, hAdiv⟩ := hw ω hω i
    exact ⟨hAc, hAskew, hAdiv⟩
  refine ⟨u, W, ?_, ?_⟩
  · filter_upwards [hu, hW] with ρ huρ hWρ
    intro i
    refine ⟨(huρ i).1, (hWρ i).1, (hWρ i).2.1, ?_⟩
    filter_upwards [(huρ i).2, (hWρ i).2.2] with x hux hWx
    exact ⟨hux, hWx⟩
  · intro r hr z
    obtain ⟨E, hE, hEtail, hEp⟩ := hosc r hr z
    let G : Set (FieldPair d) := (fun ω : PhysicalField d D.ellipticity => reduce ω.1) '' B
    obtain ⟨hG, hGmeasure⟩ := C1SublinearScalarScaling.reduced_good_event Q B hB
    have hGnull : reducedLaw Q Gᶜ = 0 := hGmeasure.trans hBnull
    refine ⟨E ∩ G, hE.inter hG, ?_, ?_⟩
    · calc
        reducedLaw Q (E ∩ G)ᶜ = reducedLaw Q (Eᶜ ∪ Gᶜ) := by rw [compl_inter]
        _ ≤ reducedLaw Q Eᶜ + reducedLaw Q Gᶜ := measure_union_le _ _
        _ = reducedLaw Q Eᶜ := by rw [hGnull, add_zero]
        _ ≤ _ := hEtail
    · rintro ρ ⟨hρE, ω, hωB, rfl⟩
      obtain ⟨a, b, hab⟩ := hEp _ hρE
      have hspec (i : Fin d) := hw ω hωB i
      choose A hAc hAskew hAclass hAdiv using hspec
      let t : ℝ := (ellipticityScale D.ellipticity)⁻¹
      have ht : 0 ≤ t := (inv_pos.mpr
        (ellipticityScale_pos D.one_le_ellipticity)).le
      have htone : t ≤ 1 :=
        C6SublinearPair.inverse_ellipticityScale_le_one D.one_le_ellipticity
      refine ⟨a, fun i => A i - t • b i, ?_⟩
      apply le_trans (Finset.sum_le_sum fun i _ => ?_) hab
      refine add_le_add le_rfl ?_
      apply C6SublinearPair.rms_gauge_le ht htone
      rw [hW_eq, hw_eq ω hωB i]
      filter_upwards [hAclass i, (hBp ω hωB).1 i] with x hx hvx
      rw [hx, hvx]
      rfl

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.c6_sublinear_pair_of_source_representatives
