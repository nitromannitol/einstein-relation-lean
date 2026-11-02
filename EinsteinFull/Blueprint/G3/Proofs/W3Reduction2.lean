import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail
import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_potential_u2D_identification
import EinsteinFull.Calculus.ComplexForceDriftSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Work.W2.CorrectorReuseSupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Multiplication by the literal commutator coefficient entry. -/
private def entryMul {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (j k : Fin d) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  complexCoefficientMul Q j k - (homogenizedCoefficient Q j k : ℂ) •
    ContinuousLinearMap.id ℂ _

private theorem entryMul_coe {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    entryMul Q j k f =ᵐ[reducedLaw Q] fun ω =>
      ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * f ω := by
  change (complexCoefficientMul Q j k f - (homogenizedCoefficient Q j k : ℂ) • f)
    =ᵐ[reducedLaw Q] _
  filter_upwards [Lp.coeFn_sub (complexCoefficientMul Q j k f)
      ((homogenizedCoefficient Q j k : ℂ) • f),
    complexCoefficientMul_coe Q j k f,
    Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) f] with ω hs hc hm
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hs hm
  rw [hs, hc, hm, Complex.ofReal_sub, sub_mul]

private theorem sum_coe {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (f : Fin d → Lp ℂ 2 (reducedLaw Q)) (s : Finset (Fin d)) :
    (∑ k ∈ s, f k : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∑ k ∈ s, f k ω := by
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 (reducedLaw Q)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (f k) (∑ l ∈ s, f l), ih] with ω ha hb
    simpa only [Pi.add_apply, hb] using! ha

private theorem row_coe {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (j : Fin d) (f : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∑ k, entryMul Q j k (f k) : Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q]
      fun ω => ∑ k, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * f k ω := by
  filter_upwards [sum_coe Q (fun k => entryMul Q j k (f k)) Finset.univ,
    ae_all_iff.mpr (fun k => entryMul_coe Q j k (f k))] with ω hs hm
  simpa only [hm] using! hs

private theorem primitive_sub_total {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E)
    (hf : IntegrableOn f (Ici 0)) (τ : ℝ≥0) :
    (∫ r in Icc (0 : ℝ) (τ : ℝ), f r) - (∫ r in Ici (0 : ℝ), f r) =
      -(∫ r in Ici (τ : ℝ), f r) := by
  have ha := hf.mono_set (show Ico (0 : ℝ) (τ : ℝ) ⊆ Ici 0 from fun _ h => h.1)
  have hb := hf.mono_set (Ici_subset_Ici.mpr τ.property)
  have hd : Disjoint (Ico (0 : ℝ) (τ : ℝ)) (Ici (τ : ℝ)) := by
    exact disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge h₂) h₁.2
  have he := setIntegral_union (μ := volume) (f := f) hd measurableSet_Ici ha hb
  rw [Ico_union_Ici_eq_Ici (a := (0 : ℝ)) (b := (τ : ℝ)) τ.property, ← integral_Icc_eq_integral_Ico] at he
  rw [he]
  abel

private theorem affine_row_coe {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (i j : Fin d) (V : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∑ k, entryMul Q j k (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) + V k) :
      Lp ℂ 2 (reducedLaw Q)) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) *
          ((unitVector i k : ℂ) + V k ω) := by
  filter_upwards [row_coe Q j (fun k =>
      Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) + V k),
    ae_all_iff.mpr (fun k => Lp.coeFn_add
      (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ)) (V k)),
    ae_all_iff.mpr (fun k => Lp.coeFn_const 2 (reducedLaw Q) (unitVector i k : ℂ))]
    with ω hx ha hc
  simpa only [ha, Pi.add_apply, hc] using! hx

private theorem joint_row_eq {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)} (hZ : IsJointObservation Q Z)
    (i j : Fin d) (L : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hLcoe : ∀ k, (L k : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (correctorGradient Q i ω k : ℂ)) :
    Z (.inl (j, i)) =
      ∑ k, entryMul Q j k (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) + L k) := by
  apply Lp.ext
  filter_upwards [hZ.1 j i, row_coe Q j (fun k =>
      Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) + L k),
    ae_all_iff.mpr (hLcoe),
    ae_all_iff.mpr (fun k => Lp.coeFn_add
      (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ)) (L k)),
    ae_all_iff.mpr (fun k => Lp.coeFn_const 2 (reducedLaw Q) (unitVector i k : ℂ))]
    with ω hz hr hl ha hc
  rw [hz, hr]
  simp only [ha, Pi.add_apply, hc, hl, commutatorObservation,
    Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_add,
    Function.const_apply]

private theorem row_tail {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (i j : Fin d) (G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hg : ∀ k, IntegrableOn (fun r => G r k) (Ici 0)) (τ : ℝ≥0) :
    (∑ k, entryMul Q j k (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) +
      ∫ r in Icc (0 : ℝ) (τ : ℝ), G r k)) -
    (∑ k, entryMul Q j k (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) +
      ∫ r in Ici (0 : ℝ), G r k)) =
      -(∫ r in Ici (τ : ℝ), ∑ k, entryMul Q j k (G r k)) := by
  have ht (k : Fin d) : IntegrableOn (fun r => G r k) (Ici (τ : ℝ)) :=
    (hg k).mono_set (Ici_subset_Ici.mpr τ.property)
  rw [← Finset.sum_sub_distrib]
  simp_rw [← map_sub, add_sub_add_left_eq_sub,
    primitive_sub_total _ (hg _) τ, map_neg]
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [integral_finset_sum _ (fun k _ => (entryMul Q j k).integrable_comp (ht k))]
  exact Finset.sum_congr rfl (fun k _ =>
    ((entryMul Q j k).integral_comp_comm (ht k)).symm)

private theorem centered_sub_integral {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (x z : Lp ℂ 2 (reducedLaw Q)) (f : ℝ → Lp ℂ 2 (reducedLaw Q)) (s : Set ℝ)
    (hf : IntegrableOn f s) (hz : centeredComplexLpCLM Q z = z)
    (he : x - z = -(∫ r in s, f r)) :
    centeredComplexLp Q x - z = -(∫ r in s, centeredComplexLp Q (f r)) := by
  calc
    _ = centeredComplexLpCLM Q (x - z) := by
      rw [map_sub, hz, centeredComplexLpCLM_apply]
    _ = -(centeredComplexLpCLM Q (∫ r in s, f r)) := by rw [he, map_neg]
    _ = _ := by
      rw [← (centeredComplexLpCLM Q).integral_comp_comm hf]
      simp only [centeredComplexLpCLM_apply]

/-- The centered commutator tail follows from the actual full-gradient integral identification. -/
theorem node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail_of_deps
    (hpotential : node_l_u3A_finite_u2D_xi_u23_potential_u2D_identificationStmt) :
    node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt := by
  intro d hd D Q hQ β hβ P hP Z hZ
  obtain ⟨G, hG, hL⟩ := hpotential d hd D Q hQ β hβ P hP
  choose L hLcoe hH htime using hL
  let H := fun (τ : ℝ≥0) (i k : Fin d) =>
    ∫ r in Icc (0 : ℝ) (τ : ℝ), G r.toNNReal i k
  let J := fun (r : ℝ≥0) (i j : Fin d) => ∑ k, entryMul Q j k (G r i k)
  let X := fun (τ : ℝ≥0) (i j : Fin d) => ∑ k, entryMul Q j k
    (Lp.const 2 (reducedLaw Q) (unitVector i k : ℂ) + H τ i k)
  refine ⟨G, J, H, X, hG, fun r i j => row_coe Q j (G r i),
    fun τ i => ⟨hH i τ, fun j => affine_row_coe Q i j (H τ i)⟩, ?_⟩
  intro τ i j
  have hg (k : Fin d) : IntegrableOn (fun r : ℝ => G r.toNNReal i k) (Ici (τ : ℝ)) :=
    (htime i k).1.mono_set (Ici_subset_Ici.mpr τ.property)
  have hj : IntegrableOn (fun r : ℝ => J r.toNNReal i j) (Ici (τ : ℝ)) :=
    integrable_finset_sum _ (fun k _ => (entryMul Q j k).integrable_comp (hg k))
  have hcZ : centeredComplexLpCLM Q (Z (.inl (j, i))) = Z (.inl (j, i)) := by
    rw [centeredComplexLpCLM_apply]
    apply Lp.ext
    filter_upwards [coeFn_centeredComplexLp Q (Z (.inl (j, i)))] with ω hω
    simpa only [hZ.integral_eq_zero, sub_zero] using! hω
  have herr : X τ i j - Z (.inl (j, i)) = -(∫ r in Ici (τ : ℝ), J r.toNNReal i j) := by
    rw [joint_row_eq Q hZ i j (L i) (hLcoe i)]
    simp_rw [← (htime i _).2.1]
    exact row_tail Q i j (fun r => G r.toNNReal i) (fun k => (htime i k).1) τ
  constructor
  · simpa only [centeredComplexLpCLM_apply] using!
      (centeredComplexLpCLM Q).integrable_comp hj
  · exact centered_sub_integral Q (X τ i j) (Z (.inl (j, i)))
      (fun r => J r.toNNReal i j) (Ici (τ : ℝ)) hj hcZ herr

end EinsteinFull.Blueprint
