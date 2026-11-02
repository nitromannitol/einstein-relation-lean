import EinsteinRelation.Clock.SpatialAverageBound
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Matrix

/-!
# Spatial averages of centred observables at the origin

The clock argument `exists_clock_averaging` uses only that the centred clock density is a bounded
function of the coefficient and clock values at the origin. This file states the same spatial
average bound for any measurable bounded function `φ` of the origin pair `(A(0), μ(0))` of the
reduced environment. The diagonal coefficient entries `a_{ii}(0)` are the first instance
(`paper/main.tex:1176-1178` and `1255-1256`).

The observable is truncated to a fixed band, which does not change it almost surely. The truncated
centred function is bounded, has mean zero, and is measurable for the σ-algebra of a neighbourhood
of the origin. The local heat-smoothing estimate then gives the scalar averaging bound, with a
constant depending only on `d`, `r₀` and the bound `K`.
-/

open MeasureTheory

namespace EinsteinRelation.Clock

/-! ### Truncation of a real number -/

/-- The real number `s` truncated to the interval `[-B, B]`. -/
noncomputable def clampTo (B s : ℝ) : ℝ :=
  max (-B) (min B s)

/-- Truncation keeps values within the band of half-width `|B|`. -/
theorem abs_clampTo_le (B s : ℝ) : |clampTo B s| ≤ |B| := by
  unfold clampTo
  rw [abs_le]
  exact ⟨(neg_le_neg (le_abs_self B)).trans (le_max_left _ _),
    max_le (neg_le_abs B) ((min_le_left B s).trans (le_abs_self B))⟩

/-- Truncation leaves a value unchanged when the value already lies in the band. -/
theorem clampTo_eq_self {B s : ℝ} (h : |s| ≤ B) : clampTo B s = s := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  unfold clampTo
  rw [min_eq_right h2, max_eq_right h1]

/-- Truncation is a measurable map of the real line. -/
theorem measurable_clampTo (B : ℝ) : Measurable (clampTo B) := by
  show Measurable (fun s : ℝ => max (-B) (min B s))
  exact measurable_const.max (measurable_const.min measurable_id)

/-! ### Continuity and measurability of the origin pair -/

private theorem continuous_coeffAtOrigin {d : ℕ} :
    Continuous (fun w : FieldPair d => w.1 (0 : Vec d)) :=
  (continuous_eval_const (0 : Vec d)).comp continuous_fst

/-- The diagonal entry of a matrix is continuous in the matrix. -/
private theorem continuous_diag {d : ℕ} (i : Fin d) : Continuous (fun A : Mat d => A i i) :=
  continuous_id.matrix_elem i i

private theorem continuous_diag_origin {d : ℕ} (i : Fin d) :
    Continuous (fun w : FieldPair d => w.1 (0 : Vec d) i i) :=
  (continuous_diag i).comp (continuous_coeffAtOrigin (d := d))

/-- The origin pair `(A(0), μ(0))` is measurable on field pairs. -/
theorem measurable_originPair {d : ℕ} :
    Measurable (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) :=
  (continuous_coeffAtOrigin (d := d)).measurable.prodMk
    (continuous_clockAtOrigin (d := d)).measurable

/-- The origin pair is measurable for the σ-algebra of any neighbourhood of the origin. -/
theorem measurable_originPair_localSigma {d : ℕ} {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U) :
    Measurable[EinsteinRelation.localSigma U]
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) := by
  have hpair : Measurable[MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) inferInstance]
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) :=
    comap_measurable _
  have hle : MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (0 : Vec d), w.2 (0 : Vec d))) inferInstance ≤
      EinsteinRelation.localSigma U := by
    unfold EinsteinRelation.localSigma
    exact le_iSup (fun x : U => MeasurableSpace.comap
      (fun w : FieldPair d => (w.1 (x : Vec d), w.2 (x : Vec d))) inferInstance) ⟨0, h0⟩
  exact hpair.mono hle le_rfl

/-- An observable `φ(A(0), μ(0))` of a measurable `φ` is measurable for the σ-algebra of any
neighbourhood of the origin. -/
theorem measurable_observable_localSigma {d : ℕ} {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U)
    {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    Measurable[EinsteinRelation.localSigma U]
      (fun w : FieldPair d => φ (w.1 (0 : Vec d), w.2 (0 : Vec d))) :=
  hφ.comp (measurable_originPair_localSigma h0)

/-- A ball of positive radius about the origin contains the origin. -/
theorem origin_mem_ball {d : ℕ} {r : ℝ} (hr : 0 < r) :
    (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < r} := by
  have h00 : euclideanNorm ((0 : Vec d) - (0 : Vec d)) = 0 := by
    simp [euclideanNorm, euclideanSq, dot]
  show euclideanNorm ((0 : Vec d) - (0 : Vec d)) < r
  rw [h00]
  exact hr

/-! ### Centring under a probability law -/

private theorem integrable_of_abs_le {d : ℕ} {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] {G : FieldPair d → ℝ} (hG : Measurable G) {B : ℝ}
    (hB : ∀ w, |G w| ≤ B) : Integrable G P :=
  Integrable.of_bound hG.aestronglyMeasurable B
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hB w)

/-- A function bounded by `B` has integral bounded by `B` under a probability law. -/
private theorem abs_integral_le_of_abs_le {d : ℕ} {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] {G : FieldPair d → ℝ} {B : ℝ} (hB : ∀ w, |G w| ≤ B) :
    |∫ w, G w ∂P| ≤ B := by
  have h : ‖∫ w, G w ∂P‖ ≤ B * P.real Set.univ :=
    norm_integral_le_of_norm_le_const (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact hB w)
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at h
  exact h

/-- A centred integrable function has mean zero. -/
private theorem integral_centre_eq_zero {d : ℕ} {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] {G : FieldPair d → ℝ} (hG : Integrable G P) :
    ∫ w, (G w - ∫ w', G w' ∂P) ∂P = 0 := by
  rw [integral_sub hG (integrable_const (∫ w', G w' ∂P)), integral_const, probReal_univ,
    one_smul, sub_self]

/-- Centring a function bounded by `B` gives a function bounded by `2 B`. -/
private theorem abs_centre_le {d : ℕ} {P : Measure (FieldPair d)} [IsProbabilityMeasure P]
    {G : FieldPair d → ℝ} {B : ℝ} (hB : ∀ w, |G w| ≤ B) (w : FieldPair d) :
    |G w - ∫ w', G w' ∂P| ≤ 2 * B := by
  obtain ⟨h1, h2⟩ := abs_le.mp (abs_integral_le_of_abs_le (P := P) hB)
  obtain ⟨h3, h4⟩ := abs_le.mp (hB w)
  rw [abs_le]
  constructor <;> linarith

/-- Centring commutes with almost-everywhere equality. -/
private theorem centre_congr_ae {d : ℕ} {P : Measure (FieldPair d)} {F G : FieldPair d → ℝ}
    (h : F =ᵐ[P] G) :
    (fun w => F w - ∫ w', F w' ∂P) =ᵐ[P] (fun w => G w - ∫ w', G w' ∂P) := by
  have hint : ∫ w', F w' ∂P = ∫ w', G w' ∂P := integral_congr_ae h
  filter_upwards [h] with w hw
  show F w - ∫ w', F w' ∂P = G w - ∫ w', G w' ∂P
  rw [hw, hint]

/-! ### The observables -/

/-- The centred observable `φ(A(0), μ(0)) - E φ(A(0), μ(0))` under the reduced reference law
(`paper/main.tex:1176-1178`). -/
noncomputable def centredObservable {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (φ : Mat d × ℝ → ℝ) (w : FieldPair d) : ℝ :=
  φ (w.1 (0 : Vec d), w.2 (0 : Vec d)) -
    ∫ w', φ (w'.1 (0 : Vec d), w'.2 (0 : Vec d)) ∂(Carriers.reducedReferenceLaw Q)

/-- The observable `φ(A(0), μ(0))` truncated to the band `[-B, B]`. -/
noncomputable def truncatedOrigin {d : ℕ} (B : ℝ) (φ : Mat d × ℝ → ℝ) (w : FieldPair d) : ℝ :=
  clampTo B (φ (w.1 (0 : Vec d), w.2 (0 : Vec d)))

/-- The truncated observable, centred under the reduced reference law. -/
noncomputable def truncatedCentred {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (B : ℝ)
    (φ : Mat d × ℝ → ℝ) (w : FieldPair d) : ℝ :=
  truncatedOrigin B φ w - ∫ w', truncatedOrigin B φ w' ∂(Carriers.reducedReferenceLaw Q)

theorem measurable_truncatedOrigin {d : ℕ} (B : ℝ) {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (truncatedOrigin B φ) :=
  (measurable_clampTo B).comp (hφ.comp (measurable_originPair (d := d)))

theorem measurable_truncatedOrigin_localSigma {d : ℕ} (B : ℝ) {U : Set (Vec d)}
    (h0 : (0 : Vec d) ∈ U) {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    Measurable[EinsteinRelation.localSigma U] (truncatedOrigin B φ) :=
  (measurable_clampTo B).comp (measurable_observable_localSigma h0 hφ)

theorem measurable_truncatedCentred {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (B : ℝ)
    {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    Measurable (truncatedCentred Q B φ) :=
  (measurable_truncatedOrigin B hφ).sub_const
    (∫ w', truncatedOrigin B φ w' ∂(Carriers.reducedReferenceLaw Q))

theorem measurable_truncatedCentred_localSigma {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (B : ℝ) {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U)
    {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    Measurable[EinsteinRelation.localSigma U] (truncatedCentred Q B φ) :=
  (measurable_truncatedOrigin_localSigma B h0 hφ).sub_const
    (∫ w', truncatedOrigin B φ w' ∂(Carriers.reducedReferenceLaw Q))

theorem abs_truncatedOrigin_le {d : ℕ} (B : ℝ) (φ : Mat d × ℝ → ℝ) (w : FieldPair d) :
    |truncatedOrigin B φ w| ≤ |B| :=
  abs_clampTo_le B _

/-- The truncated centred observable is bounded by `2 |B|` everywhere. -/
theorem abs_truncatedCentred_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (B : ℝ)
    (φ : Mat d × ℝ → ℝ) (w : FieldPair d) : |truncatedCentred Q B φ w| ≤ 2 * |B| := by
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  exact abs_centre_le (P := Carriers.reducedReferenceLaw Q) (abs_truncatedOrigin_le B φ) w

/-- The truncated centred observable has mean zero under the reduced reference law. -/
theorem integral_truncatedCentred_eq_zero {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (B : ℝ) {φ : Mat d × ℝ → ℝ} (hφ : Measurable φ) :
    ∫ w, truncatedCentred Q B φ w ∂(Carriers.reducedReferenceLaw Q) = 0 := by
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  exact integral_centre_eq_zero
    (integrable_of_abs_le (P := Carriers.reducedReferenceLaw Q)
      (measurable_truncatedOrigin B hφ) (abs_truncatedOrigin_le B φ))

/-- The centred observable agrees almost surely with its truncation at `|K|`, when `φ` is almost
surely bounded by `K`. -/
theorem centredObservable_ae_eq_truncated {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (φ : Mat d × ℝ → ℝ) {K : ℝ}
    (hK : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |φ (w.1 (0 : Vec d), w.2 (0 : Vec d))| ≤ K) :
    centredObservable Q φ =ᵐ[Carriers.reducedReferenceLaw Q] truncatedCentred Q (|K|) φ := by
  have hG : (fun w : FieldPair d => φ (w.1 (0 : Vec d), w.2 (0 : Vec d))) =ᵐ[
      Carriers.reducedReferenceLaw Q] truncatedOrigin (|K|) φ := by
    filter_upwards [hK] with w hw
    exact (clampTo_eq_self (hw.trans (le_abs_self K))).symm
  exact centre_congr_ae hG

/-! ### The diagonal coefficient entries -/

private theorem mulVec_unitVector_eq {d : ℕ} (A : Mat d) (i : Fin d) :
    A.mulVec (unitVector i) = fun j => A j i :=
  (Matrix.mulVec_single_one A i).trans rfl

private theorem dot_unitVector_mulVec_unitVector {d : ℕ} (A : Mat d) (i : Fin d) :
    dot (unitVector i) (A.mulVec (unitVector i)) = A i i := by
  rw [mulVec_unitVector_eq]
  unfold dot unitVector
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

private theorem euclideanSq_unitVector {d : ℕ} (i : Fin d) : euclideanSq (unitVector i) = 1 := by
  have h := dot_unitVector_mulVec_unitVector (1 : Mat d) i
  rw [Matrix.one_mulVec, Matrix.one_apply_eq] at h
  exact h

/-- The diagonal entry `a_{ii}(0)` of the reduced coefficient is bounded by the source constant
almost surely under the reduced reference law. The bound comes from ellipticity tested at the
unit vector `e_i`. -/
theorem ae_reduced_diag_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) :
    ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |w.1 (0 : Vec d) i i| ≤ sourceReducedBound Λ₀ := by
  have hset : MeasurableSet {w : FieldPair d | |w.1 (0 : Vec d) i i| ≤ sourceReducedBound Λ₀} :=
    (isClosed_le (continuous_diag_origin i).abs continuous_const).measurableSet
  unfold Carriers.reducedReferenceLaw
  refine (ae_map_iff (Probability.measurable_reduce (d := d)).aemeasurable hset).mpr ?_
  filter_upwards [Q.regular] with ω hω
  have hE := (sourceReducedBound_support Q.ellipticity_parameter hω).2.1 0
  have hbnd := hE.2 (unitVector i)
  rw [euclideanSq_unitVector, dot_unitVector_mulVec_unitVector] at hbnd
  obtain ⟨hlo, hhi⟩ := hbnd
  have hΛ : 0 < sourceReducedBound Λ₀ := sourceReducedBound_pos Q.ellipticity_parameter
  have hinv : 0 < (sourceReducedBound Λ₀)⁻¹ := inv_pos.mpr hΛ
  show |reducedCoefficient ω 0 i i| ≤ sourceReducedBound Λ₀
  rw [abs_le]
  constructor <;> linarith

/-! ### The averaging bound for centred observables -/

/-- **Spatial averages of centred observables at the origin.** For every dimension `d ≥ 2`, bounds
`Λ₀`, `r₀` and every level `K`, there is a family `M` of constants, independent of the environment
law `Q`, of the observable `φ`, and of the scale `R`, such that the centred observable
`φ(A(0), μ(0)) - E φ(A(0), μ(0))` is a scalar averaging field at every scale `R > 0`, whenever
`φ` is measurable and almost surely bounded by `K` under the reduced reference law
(`paper/main.tex:1176-1178`, `1255-1256`). -/
theorem exists_observable_averaging :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ K : ℝ), ∃ M : ℝ → ℝ, (∀ m, 0 ≤ M m) ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (φ : Mat d × ℝ → ℝ), Measurable φ →
        (∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), |φ (w.1 (0 : Vec d), w.2 (0 : Vec d))| ≤ K) →
        ∀ R : ℝ, 0 < R → Carriers.IsScalarAveragingField Q M R (centredObservable Q φ) := by
  intro d hd Λ₀ r₀ K
  -- The truncated observable is bounded by `2 |K|`, and the origin lies in the unit ball.
  have key := fun (m : ℝ) (hm : 1 ≤ m) =>
    eLpNorm_heatSmoothed_local_le (d := d) r₀ 1 (2 * |K|) m zero_le_one hm
  choose! Cm _ hCm using key
  refine ⟨fun m => |Cm m|, fun m => abs_nonneg _, fun Q φ hφ hK R hR => ?_⟩
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  have h1 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 1} :=
    origin_mem_ball zero_lt_one
  have h33 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R} :=
    origin_mem_ball (by linarith)
  have hmeas33 : Measurable[EinsteinRelation.localSigma
      {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}] (centredObservable Q φ) :=
    (measurable_observable_localSigma h33 hφ).sub_const
      (∫ w', φ (w'.1 (0 : Vec d), w'.2 (0 : Vec d)) ∂(Carriers.reducedReferenceLaw Q))
  have hae := centredObservable_ae_eq_truncated Q φ hK
  have hbd : ∀ w : FieldPair d, |truncatedCentred Q (|K|) φ w| ≤ 2 * |K| := fun w => by
    have h := abs_truncatedCentred_le Q (|K|) φ w
    rwa [abs_of_nonneg (abs_nonneg K)] at h
  refine isScalarAveragingField_of_heat_bound Q (fun m => |Cm m|) hR hmeas33
    (fun m _ => abs_nonneg _) ?_
  intro m hm t ht
  have hbound := hCm m (by linarith) (Carriers.reducedReferenceLaw Q)
    (isStationary_reducedReferenceLaw Q) (hasFiniteRange_reducedReferenceLaw Q)
    (truncatedCentred Q (|K|) φ) (measurable_truncatedCentred Q (|K|) hφ)
    (measurable_truncatedCentred_localSigma Q (|K|) h1 hφ) hbd
    (integral_truncatedCentred_eq_zero Q (|K|) hφ) t ht
  refine (eLpNorm_congr_ae
    (heatSmoothed_congr_ae t (isStationary_reducedReferenceLaw Q) hae)).trans_le
    (hbound.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ (1 + t) ^ (-(d : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc Cm m * (1 + t) ^ (-(d : ℝ) / 4) ≤ |Cm m| * (1 + t) ^ (-(d : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hp
    _ ≤ |Cm m| * (1 + t) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow_decay_le hd ht) (abs_nonneg _)

/-- **Spatial averages of a diagonal coefficient entry.** For every index `i₁` (the first
coordinate is `⟨0, _⟩`), the centred entry `a_{i₁ i₁}(0) - E a_{i₁ i₁}(0)` is a scalar averaging
field at every scale. The bound `K` is the source constant `sourceReducedBound Λ₀`, which bounds the
reduced coefficient almost surely (`ae_reduced_diag_le`). -/
theorem exists_diagonal_observable_averaging :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (i₁ : Fin d), ∃ M : ℝ → ℝ, (∀ m, 0 ≤ M m) ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 0 < R →
        Carriers.IsScalarAveragingField Q M R (centredObservable Q (fun p => p.1 i₁ i₁)) := by
  intro d hd Λ₀ r₀ i₁
  obtain ⟨M, hM, hobs⟩ := exists_observable_averaging d hd Λ₀ r₀ (sourceReducedBound Λ₀)
  have hφ : Measurable (fun p : Mat d × ℝ => p.1 i₁ i₁) :=
    ((continuous_diag i₁).comp continuous_fst).measurable
  exact ⟨M, hM, fun Q R hR => hobs Q (fun p => p.1 i₁ i₁) hφ (ae_reduced_diag_le Q i₁) R hR⟩

/-- **Clock spatial averages from the observable bound.** The centred clock density `μ - E μ` is
the centred observable `φ(A, m) = m`, and its almost-sure bound is `sourceReducedBound Λ₀`. This
re-derives `exists_clock_averaging` from `exists_observable_averaging`. -/
theorem exists_clock_averaging_of_observable :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ M : ℝ → ℝ, (∀ m, 0 ≤ M m) ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 0 < R →
        Carriers.IsScalarAveragingField Q M R (centredClock Q) := by
  intro d hd Λ₀ r₀
  obtain ⟨M, hM, hobs⟩ := exists_observable_averaging d hd Λ₀ r₀ (sourceReducedBound Λ₀)
  exact ⟨M, hM, fun Q R hR =>
    hobs Q (fun p => p.2) measurable_snd (ae_abs_clockAtOrigin_le Q) R hR⟩

end EinsteinRelation.Clock
