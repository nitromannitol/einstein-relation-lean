import EinsteinRelation.Environment.SquareRootLipschitzSupport
import EinsteinRelation.Environment.MatrixNorm
import EinsteinRelation.Environment.EuclideanLipschitz
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.UniformConvergence

open Filter MeasureTheory Matrix Topology
open scoped MatrixOrder

namespace EinsteinRelation

local instance (d : ℕ) : SeminormedAddCommGroup (Mat d) :=
  Matrix.seminormedAddCommGroup

private theorem frobeniusNorm_nonneg' {d : ℕ} (M : Mat d) :
    0 ≤ frobeniusNorm M := Real.sqrt_nonneg _

/-- The entrywise Frobenius norm is bounded by `d` times the matrix supremum norm. -/
theorem frobeniusNorm_le_dim_mul_matrix_norm {d : ℕ} (M : Mat d) :
    frobeniusNorm M ≤ (d : ℝ) * ‖M‖ := by
  have hentry (i j : Fin d) : (M i j) ^ 2 ≤ ‖M‖ ^ 2 := by
    have hcoord : ‖M i j‖ ≤ ‖M‖ :=
      (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
    have habs : |M i j| ≤ ‖M‖ := by
      simpa only [Real.norm_eq_abs] using hcoord
    have hsq := (sq_le_sq₀ (abs_nonneg (M i j)) (norm_nonneg M)).mpr habs
    simpa only [sq_abs] using hsq
  have hsum : frobeniusSq M ≤ ((d : ℝ) * ‖M‖) ^ 2 := by
    unfold frobeniusSq
    calc
      (∑ i, ∑ j, M i j * M i j) ≤ ∑ i, ∑ j, ‖M‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          simpa only [pow_two] using hentry i j
      _ = ((d : ℝ) * ‖M‖) ^ 2 := by simp [pow_two, mul_left_comm, mul_comm]
  unfold frobeniusNorm
  apply Real.sqrt_le_iff.mpr
  exact ⟨mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _), hsum⟩

/-- Every matrix entry is bounded by the entrywise Frobenius norm. -/
theorem matrix_norm_le_frobeniusNorm {d : ℕ} (M : Mat d) :
    ‖M‖ ≤ frobeniusNorm M := by
  rw [Matrix.norm_le_iff (frobeniusNorm_nonneg' M)]
  intro i j
  have hinner : (M i j) ^ 2 ≤ ∑ k, M i k * M i k := by
    simpa only [pow_two] using
      (Finset.single_le_sum (fun k _ => mul_self_nonneg (M i k)) (Finset.mem_univ j))
  have hrow_nonneg (k : Fin d) : 0 ≤ ∑ j, M k j * M k j :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg (M k j)
  have houter : (∑ k, M i k * M i k) ≤ frobeniusSq M := by
    unfold frobeniusSq
    exact Finset.single_le_sum (fun k _ => hrow_nonneg k) (Finset.mem_univ i)
  have hsq : (M i j) ^ 2 ≤ frobeniusSq M := by
    exact hinner.trans houter
  have habs : |M i j| ≤ frobeniusNorm M := by
    unfold frobeniusNorm
    exact Real.abs_le_sqrt hsq
  simpa only [Real.norm_eq_abs] using habs

/-- The matrix norm version of the common-ellipticity CFC square-root bound. -/
theorem cfcSqrt_matrix_norm_lipschitz_of_ellipticity {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (A B : Mat d)
    (hA : IsElliptic Λ (fun _ : Vec d => A))
    (hB : IsElliptic Λ (fun _ : Vec d => B)) :
    ‖CFC.sqrt A - CFC.sqrt B‖ ≤
      (Real.sqrt (Λ / 4) * (d : ℝ)) * ‖A - B‖ := by
  have hsq := cfcSqrt_frobenius_lipschitz_of_ellipticity hΛ A B hA hB
  have hFrobSq : frobeniusSq (CFC.sqrt A - CFC.sqrt B) ≤
      Λ / 4 * frobeniusSq (A - B) := by
    simpa [frobeniusSq, pow_two] using hsq
  have hFrob : frobeniusNorm (CFC.sqrt A - CFC.sqrt B) ≤
      Real.sqrt (Λ / 4) * frobeniusNorm (A - B) := by
    calc
      frobeniusNorm (CFC.sqrt A - CFC.sqrt B) ≤
          Real.sqrt (Λ / 4 * frobeniusSq (A - B)) := by
        unfold frobeniusNorm
        exact Real.sqrt_le_sqrt hFrobSq
      _ = Real.sqrt (Λ / 4) * frobeniusNorm (A - B) := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ Λ / 4)]
        rfl
  calc
    ‖CFC.sqrt A - CFC.sqrt B‖ ≤ frobeniusNorm (CFC.sqrt A - CFC.sqrt B) :=
      matrix_norm_le_frobeniusNorm _
    _ ≤ Real.sqrt (Λ / 4) * frobeniusNorm (A - B) := hFrob
    _ ≤ Real.sqrt (Λ / 4) * ((d : ℝ) * ‖A - B‖) :=
      mul_le_mul_of_nonneg_left (frobeniusNorm_le_dim_mul_matrix_norm _) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (Λ / 4) * (d : ℝ)) * ‖A - B‖ := by ring

private noncomputable def regularSquareRootLipschitzConstant (d : ℕ) (Λ : ℝ) : ℝ :=
  Real.sqrt (Λ / 4) * (d : ℝ) * Λ

private theorem regularSquareRootLipschitzConstant_nonneg {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) : 0 ≤ regularSquareRootLipschitzConstant d Λ := by
  unfold regularSquareRootLipschitzConstant
  exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    (le_trans zero_le_one hΛ)

/-- The coefficient square-root estimate in the carrier's matrix norm, with the
Euclidean distance from the source regularity hypothesis. -/
theorem regularCoefficient_cfcSqrt_matrix_norm_lipschitz {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (x y : Vec d) :
    ‖CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)‖ ≤
      regularSquareRootLipschitzConstant d Λ * euclideanNorm (x - y) := by
  have hA : IsElliptic Λ (fun _ : Vec d => ω.1 x) := fun _ => hω.1 x
  have hB : IsElliptic Λ (fun _ : Vec d => ω.1 y) := fun _ => hω.1 y
  have hroot := cfcSqrt_matrix_norm_lipschitz_of_ellipticity hΛ
    (ω.1 x) (ω.1 y) hA hB
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hdist0 : 0 ≤ euclideanNorm (x - y) := Real.sqrt_nonneg _
  have hcoeff : ‖ω.1 x - ω.1 y‖ ≤ Λ * euclideanNorm (x - y) := by
    rw [Matrix.norm_le_iff (mul_nonneg hΛ0 hdist0)]
    intro i j
    simpa only [Real.norm_eq_abs] using hω.2.2.1.entry_bound i j x y
  dsimp [regularSquareRootLipschitzConstant]
  calc
    ‖CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)‖ ≤
        (Real.sqrt (Λ / 4) * (d : ℝ)) * ‖ω.1 x - ω.1 y‖ := hroot
    _ ≤ (Real.sqrt (Λ / 4) * (d : ℝ)) * (Λ * euclideanNorm (x - y)) :=
      mul_le_mul_of_nonneg_left hcoeff
        (mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _))
    _ = Real.sqrt (Λ / 4) * (d : ℝ) * Λ * euclideanNorm (x - y) := by ring

/-- Each entry of the square-root field obeys the same Euclidean Lipschitz bound. -/
theorem regularCoefficient_cfcSqrt_entry_bound {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (i j : Fin d)
    (x y : Vec d) :
    |CFC.sqrt (ω.1 x) i j - CFC.sqrt (ω.1 y) i j| ≤
      regularSquareRootLipschitzConstant d Λ * euclideanNorm (x - y) := by
  have hentry : ‖CFC.sqrt (ω.1 x) i j - CFC.sqrt (ω.1 y) i j‖ ≤
      ‖CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)‖ := by
    have hrow : ‖(CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)) i j‖ ≤
        ‖(CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)) i‖ := norm_le_pi_norm _ j
    have hmat : ‖(CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)) i‖ ≤
        ‖CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)‖ := norm_le_pi_norm _ i
    exact hrow.trans hmat
  have hroot := regularCoefficient_cfcSqrt_matrix_norm_lipschitz hΛ ω hω x y
  calc
    |CFC.sqrt (ω.1 x) i j - CFC.sqrt (ω.1 y) i j| ≤
        ‖CFC.sqrt (ω.1 x) - CFC.sqrt (ω.1 y)‖ := by
      simpa only [Real.norm_eq_abs, Matrix.sub_apply] using hentry
    _ ≤ regularSquareRootLipschitzConstant d Λ * euclideanNorm (x - y) := hroot

/-- A regular elliptic coefficient field has a continuous pointwise CFC square root. -/
theorem continuous_regularCoefficient_cfcSqrt {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) :
    Continuous (fun x : Vec d => CFC.sqrt (ω.1 x)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  apply (lipschitzWith_of_euclidean_bound
    (regularSquareRootLipschitzConstant d Λ)
    (regularSquareRootLipschitzConstant_nonneg hΛ)
    (regularCoefficient_cfcSqrt_entry_bound hΛ ω hω i j)).continuous

/-- The field-valued square root on the actual subtype of regular physical fields. -/
noncomputable def regularCoefficient_cfcSqrtField {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : {ω : FieldPair d // IsRegular Λ ω}) : C(Vec d, Mat d) :=
  ⟨fun x => CFC.sqrt (ω.1.1 x), continuous_regularCoefficient_cfcSqrt hΛ ω.1 ω.2⟩

@[simp] theorem regularCoefficient_cfcSqrtField_apply {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : {ω : FieldPair d // IsRegular Λ ω}) (x : Vec d) :
    regularCoefficient_cfcSqrtField hΛ ω x = CFC.sqrt (ω.1.1 x) := rfl

/-- A common ellipticity bound gives a uniform matrix-norm estimate between two
regular environments at each spatial point. -/
theorem regularFields_cfcSqrt_matrix_norm_lipschitz {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω η : {ω : FieldPair d // IsRegular Λ ω}) (x : Vec d) :
    ‖CFC.sqrt (ω.1.1 x) - CFC.sqrt (η.1.1 x)‖ ≤
      (Real.sqrt (Λ / 4) * (d : ℝ)) * ‖ω.1.1 x - η.1.1 x‖ := by
  have hA : IsElliptic Λ (fun _ : Vec d => ω.1.1 x) := fun _ => ω.2.1 x
  have hB : IsElliptic Λ (fun _ : Vec d => η.1.1 x) := fun _ => η.2.1 x
  exact cfcSqrt_matrix_norm_lipschitz_of_ellipticity hΛ _ _ hA hB

/-- The square-root field varies continuously in the compact-open topology on
the actual regular-field subtype. -/
private theorem tendsto_regularCoefficient_cfcSqrtField {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) {α : Type*} [TopologicalSpace α] {l : Filter α}
    (F : α → {ω : FieldPair d // IsRegular Λ ω})
    (ω : {ω : FieldPair d // IsRegular Λ ω})
    (hF : Tendsto F l (𝓝 ω)) :
    Tendsto (fun z => regularCoefficient_cfcSqrtField hΛ (F z)) l
      (𝓝 (regularCoefficient_cfcSqrtField hΛ ω)) := by
  have hCoefficient : Tendsto (fun z => (F z).1.1) l (𝓝 (ω.1.1)) := by
    have hproj : Continuous (fun ξ : {ω : FieldPair d // IsRegular Λ ω} => ξ.1.1) :=
      continuous_fst.comp continuous_subtype_val
    simpa using (hproj.tendsto ω).comp hF
  have hCoefficientUniform :=
    (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn).mp hCoefficient
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  apply (Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity
    Metric.uniformity_basis_dist).2
  intro ε hε
  let C : ℝ := Real.sqrt (Λ / 4) * (d : ℝ)
  let δ : ℝ := ε / (C + 1)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Real.sqrt_nonneg _) (Nat.cast_nonneg _)
  have hδ : 0 < δ := div_pos hε (by dsimp [C]; positivity)
  have hCδ : C * δ < ε := by
    dsimp [δ]
    have hden : 0 < C + 1 := by linarith
    have hratio : C / (C + 1) < 1 := (div_lt_one hden).2 (by linarith)
    have heq : C * (ε / (C + 1)) = ε * (C / (C + 1)) := by ring
    rw [heq]
    nlinarith
  have hNear : ∀ᶠ z in l, ∀ x ∈ K,
      dist ((ω.1.1) x) (((F z).1.1) x) < δ := by
    have h := (Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity
      Metric.uniformity_basis_dist).mp
      (hCoefficientUniform K hK)
    simpa only [Set.mem_setOf_eq] using h δ hδ
  exact hNear.mono fun z hz x hx => by
    change dist (regularCoefficient_cfcSqrtField hΛ ω x)
      (regularCoefficient_cfcSqrtField hΛ (F z) x) < ε
    have hinput : ‖ω.1.1 x - (F z).1.1 x‖ < δ := by
      simpa only [dist_eq_norm] using hz x hx
    have hroot := regularFields_cfcSqrt_matrix_norm_lipschitz hΛ ω (F z) x
    have hroot' : ‖regularCoefficient_cfcSqrtField hΛ ω x -
        regularCoefficient_cfcSqrtField hΛ (F z) x‖ ≤ C *
          ‖ω.1.1 x - (F z).1.1 x‖ := by
      simpa [C, regularCoefficient_cfcSqrtField_apply] using hroot
    rw [dist_eq_norm]
    calc
      ‖regularCoefficient_cfcSqrtField hΛ ω x -
          regularCoefficient_cfcSqrtField hΛ (F z) x‖ ≤
          C * ‖ω.1.1 x - (F z).1.1 x‖ := hroot'
      _ ≤ C * δ := mul_le_mul_of_nonneg_left hinput.le hC
      _ < ε := hCδ

theorem continuous_regularCoefficient_cfcSqrtField {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    Continuous (regularCoefficient_cfcSqrtField (d := d) hΛ) := by
  apply continuous_iff_continuousAt.mpr
  intro ω
  change Tendsto (fun η : {ω : FieldPair d // IsRegular Λ ω} =>
    regularCoefficient_cfcSqrtField hΛ η) (𝓝 ω)
      (𝓝 (regularCoefficient_cfcSqrtField hΛ ω))
  exact tendsto_regularCoefficient_cfcSqrtField hΛ (fun η => η) ω tendsto_id

/-- The square-root coefficient field paired with the unchanged physical potential. -/
noncomputable def regularSquareRootFieldMap {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : {ω : FieldPair d // IsRegular Λ ω}) : FieldPair d :=
  (regularCoefficient_cfcSqrtField hΛ ω, ω.1.2)

@[simp] theorem regularSquareRootFieldMap_coefficient_apply {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : {ω : FieldPair d // IsRegular Λ ω}) (x : Vec d) :
    (regularSquareRootFieldMap hΛ ω).1 x = CFC.sqrt (ω.1.1 x) := rfl

@[simp] theorem regularSquareRootFieldMap_potential_apply {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : {ω : FieldPair d // IsRegular Λ ω}) (x : Vec d) :
    (regularSquareRootFieldMap hΛ ω).2 x = ω.1.2 x := rfl

/-- The regular-subtype operation is continuous for the compact-open field topology. -/
theorem continuous_regularSquareRootFieldMap {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    Continuous (regularSquareRootFieldMap (d := d) hΛ) := by
  have hroot : Continuous (fun ω : {ω : FieldPair d // IsRegular Λ ω} =>
      regularCoefficient_cfcSqrtField hΛ ω) := continuous_regularCoefficient_cfcSqrtField hΛ
  have hpotential : Continuous (fun ω : {ω : FieldPair d // IsRegular Λ ω} => ω.1.2) :=
    continuous_snd.comp continuous_subtype_val
  exact hroot.prodMk hpotential

/-- The subtype operation is Borel measurable on the canonical Borel carriers. -/
theorem measurable_regularSquareRootFieldMap {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) :
    Measurable (regularSquareRootFieldMap (d := d) hΛ) := by
  exact (continuous_regularSquareRootFieldMap hΛ).measurable

/-- Actual-law use of the square-root operation, retaining only the law's given
almost-everywhere regularity and assigning no values off that locus. -/
theorem EnvironmentLaw.ae_regularSquareRootFieldMap_spec {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) :
    ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ ω,
      (∀ x : Vec d,
        (regularSquareRootFieldMap Q.ellipticity_parameter ⟨ω, hω⟩).1 x =
          CFC.sqrt (ω.1 x)) ∧
      (regularSquareRootFieldMap Q.ellipticity_parameter ⟨ω, hω⟩).2 = ω.2 := by
  filter_upwards [Q.regular] with ω hω
  refine ⟨hω, ?_, ?_⟩
  · intro x
    rfl
  · rfl

end EinsteinRelation
