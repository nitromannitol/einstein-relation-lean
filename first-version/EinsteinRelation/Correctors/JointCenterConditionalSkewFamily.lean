import EinsteinRelation.Correctors.JointCenterConditionalVectorFamily

/-! # Joint conditioning of center-dependent skew corrector fields

Source: `paper/main.tex:913–938`.

Each column of a skew-valued observable is conditioned through the vector
family. The entrywise antisymmetrization `(T - Tᵀ)/2` keeps the conditional
identity because the original field is pointwise skew, so each entry of the
output is an a.e. version of the corresponding entry of `F`.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Joint versions for center-dependent skew-valued observables: columns are
conditioned via the vector family, then antisymmetrized pointwise. The result
is exactly skew at every point and has the literal matrix-valued conditional
expectation at every center. Source: `paper/main.tex:913–938`. -/
theorem exists_joint_center_conditioned_skew_family {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (R : ℝ) (F : Vec d × FieldPair d → Mat d)
    (hF : Measurable F)
    (hi : ∀ (y : Vec d) (k : Fin d),
      Integrable (fun w j => F (y, w) j k) (reducedEnvironmentLaw Q))
    (hskew : ∀ y : Vec d,
      ∀ᵐ w ∂(reducedEnvironmentLaw Q), (F (y, w)).transpose = -(F (y, w))) :
    ∃ S : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Mat d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance S) ∧
      (∀ z, (S z).transpose = -(S z)) ∧
      ∀ (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}),
        (fun w j => S (y, w) j k) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun w j => F (y.1, w) j k | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}] := by
  have hFentry : ∀ j k : Fin d, Measurable (fun p : Vec d × FieldPair d => F p j k) :=
    fun j k => (continuous_id.matrix_elem j k).measurable.comp hF
  choose u hum huv using fun k : Fin d =>
    exists_joint_center_conditioned_vector_family (R := R) Q
      (fun (p : Vec d × FieldPair d) (j : Fin d) => F p j k)
      (measurable_pi_lambda _ fun j => hFentry j k)
      (fun y => hi y k)
  -- Coordinates of a vector conditional expectation are scalar conditional expectations.
  have hcoordCol (y : {y : Vec d // euclideanNorm y ≤ R}) (j' i : Fin d) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q),
        (reducedEnvironmentLaw Q)[fun a => (fun i' => F (y.1, a) i' j')
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w i =
        (reducedEnvironmentLaw Q)[fun a => F (y.1, a) i j'
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w := by
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ).comp_condExp_comm
        (m := reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R})
        (hi y.1 j')
  have hcol (y : {y : Vec d // euclideanNorm y ≤ R}) (j' : Fin d) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q), ∀ i : Fin d,
        u j' (y, w) i = (reducedEnvironmentLaw Q)[fun a => F (y.1, a) i j'
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w := by
    filter_upwards [huv j' y, ae_all_iff.mpr (fun i => hcoordCol y j' i)] with w hw hc
    exact fun i => (congrFun hw i).trans (hc i)
  -- Skew symmetry of `F` transfers to the scalar conditional expectations.
  have hneg (y : {y : Vec d // euclideanNorm y ≤ R}) (j k : Fin d) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q),
        (reducedEnvironmentLaw Q)[fun a => F (y.1, a) k j
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w =
        -(reducedEnvironmentLaw Q)[fun a => F (y.1, a) j k
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w := by
    have hent : (fun a => F (y.1, a) k j) =ᵐ[reducedEnvironmentLaw Q]
        -(fun a => F (y.1, a) j k) := by
      filter_upwards [hskew y.1] with a ha
      simpa [Matrix.transpose_apply, Matrix.neg_apply, Pi.neg_apply] using
        congrArg (fun M : Mat d => M j k) ha
    have hcn : (reducedEnvironmentLaw Q)[fun a => F (y.1, a) k j
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}]
        =ᵐ[reducedEnvironmentLaw Q]
        -(reducedEnvironmentLaw Q)[fun a => F (y.1, a) j k
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] :=
      (condExp_congr_ae hent).trans (condExp_neg _ _)
    filter_upwards [hcn] with w hw
    simpa only [Pi.neg_apply] using hw
  have hvec (y : {y : Vec d // euclideanNorm y ≤ R}) (k : Fin d) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q), ∀ i : Fin d,
        (reducedEnvironmentLaw Q)[fun a => (fun i' => F (y.1, a) i' k)
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w i =
        (reducedEnvironmentLaw Q)[fun a => F (y.1, a) i k
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w :=
    ae_all_iff.mpr (fun i => hcoordCol y k i)
  have hu (y : {y : Vec d // euclideanNorm y ≤ R}) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q), ∀ j' i : Fin d,
        u j' (y, w) i = (reducedEnvironmentLaw Q)[fun a => F (y.1, a) i j'
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w :=
    ae_all_iff.mpr (fun j' => hcol y j')
  have hn (y : {y : Vec d // euclideanNorm y ≤ R}) :
      ∀ᵐ w ∂(reducedEnvironmentLaw Q), ∀ j i : Fin d,
        (reducedEnvironmentLaw Q)[fun a => F (y.1, a) i j
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w =
        -(reducedEnvironmentLaw Q)[fun a => F (y.1, a) j i
          | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w :=
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun i => hneg y j i))
  obtain ⟨T, hT⟩ : ∃ T : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d,
      ∀ (p : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (j k : Fin d),
        T p j k = u k p j :=
    ⟨fun p => Matrix.of fun j k => u k p j, fun p j k => rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d,
      ∀ (p : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (j k : Fin d),
        S p j k = (2⁻¹ : ℝ) * (T p j k - T p k j) :=
    ⟨fun p => Matrix.of fun j k => (2⁻¹ : ℝ) * (T p j k - T p k j), fun p j k => rfl⟩
  refine ⟨S, ?_, ?_, ?_⟩
  · letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}
    have hpi : @Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
        (Fin d → Fin d → ℝ) inferInstance MeasurableSpace.pi S := by
      refine measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun k => ?_))
      simp only [hS]
      refine Measurable.const_mul ?_ _
      refine Measurable.sub ?_ ?_
      · simp only [hT]
        exact (measurable_pi_apply j).comp (hum k)
      · simp only [hT]
        exact (measurable_pi_apply k).comp (hum j)
    exact hpi.mono le_rfl (OpensMeasurableSpace.borel_le (α := Fin d → Fin d → ℝ))
  · intro z
    ext j k
    simp only [Matrix.transpose_apply, Matrix.neg_apply, hS]
    ring
  · intro k y
    filter_upwards [hvec y k, hu y, hn y] with w hvw huw hnw
    funext j
    have hentry : S (y, w) j k = (reducedEnvironmentLaw Q)[fun a => F (y.1, a) j k
        | reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}] w := by
      rw [hS, hT, hT, huw k j, huw j k, hnw j k]
      ring
    exact hentry.trans (hvw j).symm

end EinsteinRelation.Correctors
