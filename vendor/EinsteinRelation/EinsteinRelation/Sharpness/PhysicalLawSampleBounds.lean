import EinsteinRelation.Sharpness.Ellipticity
import EinsteinRelation.Sharpness.SeedPhysicalMeasurability
import EinsteinRelation.Sharpness.SmoothEnvironment
import EinsteinRelation.Sharpness.PotentialBounds
import EinsteinRelation.Sharpness.ScalarSmoothBorel

/-! # Almost-sure bounds for the sampled physical environment

Source: `paper/main.tex`, Proposition 7.1 (`sharp.example`, lines 1202–1231) and the physical
fields of lines 1218–1231. For the scaled canonical seed `ψ_W = ε * seedField d W`, with the
gradient bound `1/4` and clock density in `[3/4, 5/4]` for every sample and point, every sample
of the physical pair is elliptic, smooth, and has potential bounded by `1/6`. The almost-sure
statement transports this pointwise fact through the law `P.map F`.

The transport `ae_map_iff` needs the good set of field pairs to be Borel. The closed parts
(ellipticity and the potential bound) are proved here. Scalar smoothness is Borel by realization as
the root projection of the closed compatible-jet set, and matrix smoothness is a finite intersection
of those scalar predicates.
-/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-- Evaluation at a fixed direction `ξ` is continuous on matrices. -/
private theorem goodPair_continuous_dot_mulVec {d : ℕ} (ξ : Vec d) :
    Continuous fun M : Mat d => dot ξ (M.mulVec ξ) := by
  have hmv : Continuous fun M : Mat d => M.mulVec ξ :=
    continuous_id.matrix_mulVec continuous_const
  unfold dot
  exact continuous_finset_sum _ fun i _ => continuous_const.mul ((continuous_apply i).comp hmv)

/-- The pointwise ellipticity condition on a matrix is a closed condition. -/
private theorem goodPair_isClosed_ellipticMatrix {d : ℕ} (Λ : ℝ) :
    IsClosed {M : Mat d | M.transpose = M ∧ ∀ ξ : Vec d,
      Λ⁻¹ * euclideanSq ξ ≤ dot ξ (M.mulVec ξ) ∧ dot ξ (M.mulVec ξ) ≤ Λ * euclideanSq ξ} := by
  have hT : Continuous fun M : Mat d => M.transpose := continuous_id.matrix_transpose
  rw [Set.setOf_and, Set.setOf_forall]
  refine (isClosed_eq hT continuous_id).inter (isClosed_iInter fun ξ => ?_)
  rw [Set.setOf_and]
  exact (isClosed_le continuous_const (goodPair_continuous_dot_mulVec ξ)).inter
    (isClosed_le (goodPair_continuous_dot_mulVec ξ) continuous_const)

/-- The set of field pairs whose coefficient is elliptic with constant `Λ` is Borel. It is an
intersection over points of closed conditions, hence closed. -/
private theorem goodPair_measurableSet_elliptic {d : ℕ} (Λ : ℝ) :
    MeasurableSet {ω : FieldPair d | IsElliptic Λ (ω.1 : Vec d → Mat d)} := by
  have hset : {ω : FieldPair d | IsElliptic Λ (ω.1 : Vec d → Mat d)} =
      ⋂ x : Vec d, (fun ω : FieldPair d => ω.1 x) ⁻¹'
        {M : Mat d | M.transpose = M ∧ ∀ ξ : Vec d,
          Λ⁻¹ * euclideanSq ξ ≤ dot ξ (M.mulVec ξ) ∧ dot ξ (M.mulVec ξ) ≤ Λ * euclideanSq ξ} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, IsElliptic]
  have hclosed : IsClosed {ω : FieldPair d | IsElliptic Λ (ω.1 : Vec d → Mat d)} := by
    rw [hset]
    exact isClosed_iInter fun x =>
      (goodPair_isClosed_ellipticMatrix Λ).preimage
        ((continuous_eval_const (F := ContinuousMap (Vec d) (Mat d)) x).comp continuous_fst)
  exact hclosed.measurableSet

/-- The set of field pairs whose potential is bounded by `1/6` everywhere is Borel. It is an
intersection over points of closed conditions, hence closed. -/
private theorem goodPair_measurableSet_bound {d : ℕ} :
    MeasurableSet {ω : FieldPair d | ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ)} := by
  have hset : {ω : FieldPair d | ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ)} =
      ⋂ x : Vec d, (fun ω : FieldPair d => ω.2 x) ⁻¹' {r : ℝ | |r| ≤ (1/6 : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  have hclosed : IsClosed {ω : FieldPair d | ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ)} := by
    rw [hset]
    exact isClosed_iInter fun x =>
      (isClosed_le _root_.continuous_abs continuous_const).preimage
        ((continuous_eval_const (F := ContinuousMap (Vec d) ℝ) x).comp continuous_snd)
  exact hclosed.measurableSet

/-- Extract one scalar continuous map from a matrix-valued continuous field. -/
private def matrixEntryContinuousMap {d : ℕ} (A : C(Vec d, Mat d)) (j k : Fin d) :
    C(Vec d, ℝ) :=
  ⟨fun x => A x j k,
    by
      exact ((continuous_apply k).comp (continuous_apply j)).comp A.continuous⟩

/-- Each scalar matrix entry of a field pair, considered as a continuous-map-valued function,
is measurable by its point evaluations. -/
private theorem measurable_matrixEntryContinuousMap {d : ℕ} (j k : Fin d) :
    Measurable (fun ω : FieldPair d => matrixEntryContinuousMap ω.1 j k) := by
  apply measurable_continuousMap_of_evaluations
  intro x
  have hmat : Continuous fun ω : FieldPair d => ω.1 x :=
    (continuous_eval_const x).comp continuous_fst
  exact ((continuous_apply k).comp (continuous_apply j)).comp hmat |>.measurable

/-- The smoothness predicate on scalar matrix entries is Borel, by the scalar realization result. -/
private theorem measurableSet_smoothMatrixEntry {d : ℕ} (j k : Fin d) :
    MeasurableSet {ω : FieldPair d | ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)} := by
  have hpre := (measurableSet_contDiff_continuousMap (d := d)).preimage
    (measurable_matrixEntryContinuousMap j k)
  simpa [matrixEntryContinuousMap] using hpre

/-- Smoothness of the scalar component is Borel on the field-pair carrier. -/
private theorem measurableSet_smoothPotential {d : ℕ} :
    MeasurableSet {ω : FieldPair d | ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.2 x)} := by
  have hmeas : Measurable (fun ω : FieldPair d => ω.2) := by
    apply measurable_continuousMap_of_evaluations
    intro x
    exact (continuous_eval_const x).comp continuous_snd |>.measurable
  exact (measurableSet_contDiff_continuousMap (d := d)).preimage hmeas

/-- The smoothness predicate on field pairs is Borel. Its matrix part is the finite intersection
of scalar Borel predicates on the matrix entries, and the potential part is scalar. -/
theorem measurableSet_isSmoothFieldPair_fieldPair {d : ℕ} :
    MeasurableSet {ω : FieldPair d | IsSmoothFieldPair ω} := by
  have hentries : MeasurableSet
      (⋂ j : Fin d, ⋂ k : Fin d,
        {ω : FieldPair d | ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)}) :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
      measurableSet_smoothMatrixEntry j k
  have hset : {ω : FieldPair d | IsSmoothFieldPair ω} =
      (⋂ j : Fin d, ⋂ k : Fin d,
        {ω : FieldPair d | ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)}) ∩
        {ω : FieldPair d | ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.2 x)} := by
    ext ω
    simp [IsSmoothFieldPair, Set.mem_iInter]
  rw [hset]
  exact hentries.inter measurableSet_smoothPotential

/-- Pointwise bounds on one sample. A field pair equal to the physical coefficient and potential of
a seed `ψ`, under the gradient bound `1/4` and clock density in `[3/4, 5/4]`, is elliptic with
constant `4`, smooth, and has potential bounded by `1/6`. Source: `paper/main.tex`, lines
1218–1231. -/
private theorem physicalPair_sample_good {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hg : ∀ x, euclideanNorm (gradient ψ x) ≤ (1/4 : ℝ))
    (hμ : ∀ x, (3/4 : ℝ) ≤ densityField i δ ψ x ∧ densityField i δ ψ x ≤ (5/4 : ℝ))
    (ω : FieldPair d) (hω₁ : ∀ x, ω.1 x = physicalCoefficientField i δ ψ x)
    (hω₂ : ∀ x, ω.2 x = potentialField i δ ψ x) :
    IsElliptic 4 (ω.1 : Vec d → Mat d) ∧ IsSmoothFieldPair ω ∧
      ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ) := by
  have hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0 := fun x =>
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3 / 4)
      (jacobianFactor_bounds i (gradient ψ x) (hg x)).1).ne'
  have hμpos : ∀ x, 0 < densityField i δ ψ x := fun x => by linarith [(hμ x).1]
  have hca : Continuous (physicalCoefficientField i δ ψ) :=
    continuous_physicalCoefficientField i δ ψ hψ hj hμpos
  have hcv : Continuous (potentialField i δ ψ) :=
    continuous_potentialField i δ ψ hψ hj hμpos
  have hEnv : ω = physicalEnvironment i δ ψ hca hcv :=
    Prod.ext (ContinuousMap.ext hω₁) (ContinuousMap.ext hω₂)
  subst hEnv
  exact ⟨physicalCoefficientField_isElliptic i δ ψ hg hμ,
    isSmoothFieldPair_physicalEnvironment i δ ψ hca hcv hψ hj hμpos,
    fun x => potentialField_abs_le i δ ψ hμ x⟩

/-- Source: `paper/main.tex`, Proposition 7.1 (`sharp.example`, lines 1202–1231) and the physical
fields of lines 1218–1231. For the scaled canonical seed `ψ_W = ε * seedField d W`, with the
gradient bound `1/4` and clock density in `[3/4, 5/4]` for every sample and point, and for any
measurable sample map `F` whose coordinates are the physical coefficient and potential of `ψ_W`,
almost every sample of the law `P.map F` is elliptic (constant `4`), smooth, and has potential
bounded by `1/6`. -/
theorem ae_seedField_physical_sample_bounds {d : ℕ} (i : Fin d) (ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1/4 : ℝ))
    (δ : ℝ)
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3/4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5/4 : ℝ))
    {P : Measure (NoiseSample d)} (_hP : External.IsWhiteNoiseLaw P)
    (F : NoiseSample d → FieldPair d) (hF : Measurable F)
    (hFW : ∀ (W : NoiseSample d) (x : Vec d),
      (F W).1 x = physicalCoefficientField i δ (fun y => ε * seedField d W y) x ∧
      (F W).2 x = potentialField i δ (fun y => ε * seedField d W y) x) :
    ∀ᵐ ω ∂(P.map F), IsElliptic 4 (ω.1 : Vec d → Mat d) ∧ IsSmoothFieldPair ω ∧
      ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ) := by
  have hpt : ∀ W : NoiseSample d, IsElliptic 4 ((F W).1 : Vec d → Mat d) ∧
      IsSmoothFieldPair (F W) ∧ ∀ x : Vec d, |(F W).2 x| ≤ (1/6 : ℝ) := fun W =>
    physicalPair_sample_good i δ (fun y => ε * seedField d W y)
      (contDiff_const.mul (contDiff_seedField d W)) (hgrad W) (hμ W) (F W)
      (fun x => (hFW W x).1) (fun x => (hFW W x).2)
  have hmeas : MeasurableSet {ω : FieldPair d | IsElliptic 4 (ω.1 : Vec d → Mat d) ∧
      IsSmoothFieldPair ω ∧ ∀ x : Vec d, |ω.2 x| ≤ (1/6 : ℝ)} := by
    rw [Set.setOf_and, Set.setOf_and]
    exact (goodPair_measurableSet_elliptic 4).inter
      (measurableSet_isSmoothFieldPair_fieldPair.inter goodPair_measurableSet_bound)
  exact (ae_map_iff hF.aemeasurable hmeas).mpr (ae_of_all _ hpt)

end EinsteinRelation.Sharpness
