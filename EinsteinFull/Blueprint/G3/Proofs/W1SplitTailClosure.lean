import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_split_u2D_tail
import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tail
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Work.W4.ActualHomogeneousGaussianSemigroupProof
import EinsteinFull.Blueprint.G3.Proofs.W2GradientLimitClosure
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_2
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Work.W4.HomogeneousAllDataHorizontalSmoothingSupport
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint.SplitTail
open EinsteinRelation

/-- Splitting a Bochner tail includes the common endpoint only once up to
Lebesgue null sets. The result is valid for the stationary complex L² carrier. -/
theorem integral_tail_split {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a b : ℝ}
    (hab : a ≤ b) (hf : IntegrableOn f (Ici a)) :
    (∫ r in Ici a, f r) = (∫ r in Icc a b, f r) + (∫ r in Ici b, f r) := by
  have hleft := hf.mono_set (show Ico a b ⊆ Ici a from fun _ h => h.1)
  have hright := hf.mono_set (Ici_subset_Ici.mpr hab)
  have hd : Disjoint (Ico a b) (Ici b) :=
    disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge h₂) h₁.2
  have h := setIntegral_union (μ := volume) (f := f) hd measurableSet_Ici hleft hright
  rw [Ico_union_Ici_eq_Ici hab, ← integral_Icc_eq_integral_Ico] at h
  exact h

/-- The split identity after the literal anisotropic Gaussian average.
No estimate or convergence assertion is inserted as a hypothesis. -/
theorem gaussian_tail_split {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (s : ℝ) (hs : 0 < s)
    {f : ℝ → Lp ℂ 2 (reducedLaw Q)} {a b : ℝ}
    (hab : a ≤ b) (hf : IntegrableOn f (Ici a)) :
    gaussianAverage hd Q s hs (-(∫ r in Ici a, f r)) =
      -(gaussianAverage hd Q s hs (∫ r in Icc a b, f r) +
        gaussianAverage hd Q s hs (∫ r in Ici b, f r)) := by
  change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 _ =
    -((homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0) _ +
      (homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0) _)
  rw [integral_tail_split hab hf, map_neg, map_add]

/-- Minkowski's inequality for the explicit Euclidean sum of component L²
norms. No supremum norm on the coordinate carrier is used. -/
theorem sqrt_sum_norm_add_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
    (f g : ι → E) :
    Real.sqrt (∑ j, ‖f j + g j‖ ^ 2) ≤
      Real.sqrt (∑ j, ‖f j‖ ^ 2) + Real.sqrt (∑ j, ‖g j‖ ^ 2) := by
  simpa only [PiLp.norm_eq_of_L2, PiLp.add_apply, PiLp.toLp_apply] using!
    norm_add_le (WithLp.toLp 2 f) (WithLp.toLp 2 g)

/-- The literal power-tail normalization used for the long-time part. -/
theorem integral_power_tail {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    (∫ r in Ici a, r ^ (-1 - δ)) = a ^ (-δ) / δ := by
  rw [integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) ha]
  rw [show -1 - δ + 1 = -δ by ring]
  exact neg_div_neg_eq _ _

/-- The exponent in the far-tail bound is exactly the source's νd/4. -/
theorem power_tail_cutoff {s ν δ : ℝ} (hs : 0 < s) (hδ : 0 < δ) :
    s ^ δ * (∫ r in Ici (s ^ (1 + ν)), r ^ (-1 - δ)) =
      s ^ (-ν * δ) / δ := by
  rw [integral_power_tail (Real.rpow_pos_of_pos hs _) hδ,
    ← mul_div_assoc, ← Real.rpow_mul hs.le, ← Real.rpow_add hs]
  congr 2
  ring

/-- A single gain controls the three decay terms when 1 ≤ τ ≤ s. -/
theorem common_gain {τ s ε ν δ gain : ℝ}
    (hτ : 1 ≤ τ) (hτs : τ ≤ s) (hg : 0 ≤ gain)
    (hgε : gain ≤ ε) (hghalf : gain ≤ ε / 2) (hgν : gain ≤ ν * δ) :
    τ ^ (-ε) + s ^ (-ε / 2) + s ^ (-ν * δ) ≤ 3 * τ ^ (-gain) := by
  have hs : 1 ≤ s := hτ.trans hτs
  have hτpos : 0 < τ := zero_lt_one.trans_le hτ
  have h₁ : τ ^ (-ε) ≤ τ ^ (-gain) :=
    Real.rpow_le_rpow_of_exponent_le hτ (neg_le_neg hgε)
  have h₂ : s ^ (-ε / 2) ≤ τ ^ (-gain) := calc
    _ ≤ s ^ (-gain) := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
    _ ≤ τ ^ (-gain) :=
      Real.rpow_le_rpow_of_nonpos hτpos hτs (neg_nonpos.mpr hg)
  have h₃ : s ^ (-ν * δ) ≤ τ ^ (-gain) := calc
    _ ≤ s ^ (-gain) := Real.rpow_le_rpow_of_exponent_le hs (by nlinarith)
    _ ≤ τ ^ (-gain) :=
      Real.rpow_le_rpow_of_nonpos hτpos hτs (neg_nonpos.mpr hg)
  linarith only [h₁, h₂, h₃]

/-- Integrating a nonnegative power over a finite interval can only decrease
the corresponding improper tail. -/
theorem integral_power_interval_le {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    (∫ r in Icc a b, r ^ (-1 - δ)) ≤ a ^ (-δ) / δ := by
  have hi : IntegrableOn (fun r : ℝ => r ^ (-1 - δ)) (Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) ha
  rw [← integral_power_tail ha hδ]
  apply setIntegral_mono_set hi
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    exact Real.rpow_nonneg (ha.trans_le hr).le _
  · exact Filter.Eventually.of_forall fun r h => h.1

/-- Before time s, the polynomial loss is bounded by 2^L. -/
theorem integral_short_piece_le {τ s ε : ℝ} (L : ℕ)
    (hτ : 0 < τ) (hτs : τ ≤ s) (hε : 0 < ε) :
    (∫ r in Icc τ s, r ^ (-1 - ε) * (1 + r / s) ^ L) ≤
      (2 : ℝ) ^ L / ε * τ ^ (-ε) := by
  have hs : 0 < s := hτ.trans_le hτs
  have hrpow : IntegrableOn (fun r : ℝ => r ^ (-1 - ε)) (Icc τ s) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_id.rpow_const (fun r hr => Or.inl (hτ.trans_le hr.1).ne')
  have hf : IntegrableOn
      (fun r : ℝ => r ^ (-1 - ε) * (1 + r / s) ^ L) (Icc τ s) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_id.rpow_const (fun r hr => Or.inl (hτ.trans_le hr.1).ne')).mul
      ((continuousOn_const.add (continuousOn_id.div_const s)).pow L)
  calc
    _ ≤ ∫ r in Icc τ s, (2 : ℝ) ^ L * r ^ (-1 - ε) := by
      apply setIntegral_mono_on hf (hrpow.const_mul _) measurableSet_Icc
      intro r hr
      have hr0 : 0 ≤ r := (hτ.trans_le hr.1).le
      have hratio : r / s ≤ 1 := (div_le_one hs).mpr hr.2
      have hpoly : (1 + r / s) ^ L ≤ (2 : ℝ) ^ L :=
        pow_le_pow_left₀ (by positivity) (by linarith) L
      exact (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg hr0 (-1 - ε))).trans_eq
        (mul_comm _ _)
    _ = (2 : ℝ) ^ L * (∫ r in Icc τ s, r ^ (-1 - ε)) := integral_const_mul _ _
    _ ≤ (2 : ℝ) ^ L * (τ ^ (-ε) / ε) :=
      mul_le_mul_of_nonneg_left (integral_power_interval_le hτ hε) (by positivity)
    _ = _ := by ring

/-- Between s and s^(1+ν), the polynomial loss costs at most s^(νL).
The strict source restriction ν < ε/(4L₀) is stronger than the restriction
needed here. -/
theorem integral_middle_piece_le {s ε ν : ℝ} (L : ℕ)
    (hs : 1 ≤ s) (hε : 0 < ε) (hν : 0 ≤ ν) (hνL : ν * L ≤ ε / 2) :
    (∫ r in Icc s (s ^ (1 + ν)), r ^ (-1 - ε) * (1 + r / s) ^ L) ≤
      (2 : ℝ) ^ L / ε * s ^ (-ε / 2) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hsp : 1 ≤ s ^ ν := Real.one_le_rpow hs hν
  have hrpow : IntegrableOn (fun r : ℝ => r ^ (-1 - ε))
      (Icc s (s ^ (1 + ν))) := by
    apply ContinuousOn.integrableOn_Icc
    exact continuousOn_id.rpow_const (fun r hr => Or.inl (hspos.trans_le hr.1).ne')
  have hf : IntegrableOn
      (fun r : ℝ => r ^ (-1 - ε) * (1 + r / s) ^ L)
      (Icc s (s ^ (1 + ν))) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_id.rpow_const (fun r hr => Or.inl (hspos.trans_le hr.1).ne')).mul
      ((continuousOn_const.add (continuousOn_id.div_const s)).pow L)
  have hpoly (r : ℝ) (hr : r ∈ Icc s (s ^ (1 + ν))) :
      (1 + r / s) ^ L ≤ (2 : ℝ) ^ L * s ^ (ν * L) := by
    have hratio : r / s ≤ s ^ ν := by
      apply (div_le_iff₀ hspos).mpr
      calc
        r ≤ s ^ (1 + ν) := hr.2
        _ = s ^ ν * s := by rw [Real.rpow_add hspos, Real.rpow_one, mul_comm]
    have hbase : 1 + r / s ≤ 2 * s ^ ν := by linarith only [hratio, hsp]
    calc
      _ ≤ (2 * s ^ ν) ^ L :=
        pow_le_pow_left₀ (by
          have := div_nonneg (hspos.trans_le hr.1).le hspos.le
          linarith) hbase L
      _ = _ := by rw [mul_pow, Real.rpow_mul_natCast hspos.le]
  calc
    _ ≤ ∫ r in Icc s (s ^ (1 + ν)),
        ((2 : ℝ) ^ L * s ^ (ν * L)) * r ^ (-1 - ε) := by
      apply setIntegral_mono_on hf (hrpow.const_mul _) measurableSet_Icc
      intro r hr
      exact (mul_le_mul_of_nonneg_left (hpoly r hr)
        (Real.rpow_nonneg (hspos.trans_le hr.1).le (-1 - ε))).trans_eq (mul_comm _ _)
    _ = ((2 : ℝ) ^ L * s ^ (ν * L)) *
        (∫ r in Icc s (s ^ (1 + ν)), r ^ (-1 - ε)) := integral_const_mul _ _
    _ ≤ ((2 : ℝ) ^ L * s ^ (ν * L)) * (s ^ (-ε) / ε) :=
      mul_le_mul_of_nonneg_left (integral_power_interval_le hspos hε) (by positivity)
    _ = (2 : ℝ) ^ L / ε * s ^ (ν * L - ε) := by
      rw [sub_eq_add_neg, Real.rpow_add hspos]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hs (by linarith only [hνL])) (by positivity)

/-- The scalar integral estimate in the first displayed inequality of the
split-tail argument, with an explicit constant independent of τ and s. -/
theorem integral_weak_flux_weight_le {τ s ε ν : ℝ} (L : ℕ)
    (hτ : 1 ≤ τ) (hτs : τ ≤ s) (hε : 0 < ε) (hν : 0 ≤ ν)
    (hνL : ν * L ≤ ε / 2) :
    (∫ r in Icc τ (s ^ (1 + ν)), r ^ (-1 - ε) * (1 + r / s) ^ L) ≤
      (2 : ℝ) ^ L / ε * (τ ^ (-ε) + s ^ (-ε / 2)) := by
  have hτpos : 0 < τ := zero_lt_one.trans_le hτ
  have hs : 1 ≤ s := hτ.trans hτs
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hsb : s ≤ s ^ (1 + ν) := by
    calc
      s = s ^ (1 : ℝ) := (Real.rpow_one s).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hs (by linarith)
  let f := fun r : ℝ => r ^ (-1 - ε) * (1 + r / s) ^ L
  have hi : IntegrableOn f (Icc τ (s ^ (1 + ν))) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_id.rpow_const (fun r hr => Or.inl (hτpos.trans_le hr.1).ne')).mul
      ((continuousOn_const.add (continuousOn_id.div_const s)).pow L)
  have hleft : IntegrableOn f (Icc τ s) :=
    hi.mono_set (Icc_subset_Icc le_rfl hsb)
  have hright : IntegrableOn f (Ioc s (s ^ (1 + ν))) :=
    hi.mono_set (fun _ hr => ⟨hτs.trans hr.1.le, hr.2⟩)
  have hd : Disjoint (Icc τ s) (Ioc s (s ^ (1 + ν))) :=
    disjoint_left.mpr fun _ h₁ h₂ => (not_lt_of_ge h₁.2) h₂.1
  have he := setIntegral_union (μ := volume) (f := f) hd measurableSet_Ioc hleft hright
  rw [Icc_union_Ioc_eq_Icc hτs hsb, ← integral_Icc_eq_integral_Ioc] at he
  calc
    _ = (∫ r in Icc τ s, f r) + (∫ r in Icc s (s ^ (1 + ν)), f r) := he
    _ ≤ (2 : ℝ) ^ L / ε * τ ^ (-ε) + (2 : ℝ) ^ L / ε * s ^ (-ε / 2) :=
      add_le_add (integral_short_piece_le L hτpos hτs hε)
        (integral_middle_piece_le L hs hε hν hνL)
    _ = _ := by ring

/-- Structural exponents are selected before any environment law, time or
derivative order, as required by the split-tail contract. -/
theorem exists_split_parameters {ε L₀ : ℝ} (hε : 0 < ε) (hL : 0 < L₀)
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ ν gain : ℝ, 0 < ν ∧ ν < ε / (4 * L₀) ∧
      0 < gain ∧ gain ≤ ε ∧ gain ≤ ε / 2 ∧ gain ≤ ν * (d : ℝ) / 4 ∧
      ν * L₀ ≤ ε / 2 := by
  let ν := ε / (8 * L₀)
  have hν : 0 < ν := div_pos hε (by positivity)
  have hνL : ν * L₀ = ε / 8 := by
    dsimp only [ν]
    field_simp
  have hνsmall : ν < ε / (4 * L₀) := by
    apply (lt_div_iff₀ (by positivity : 0 < 4 * L₀)).mpr
    nlinarith only [hνL, hε]
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  let gain := min (ε / 2) (ν * (d : ℝ) / 4)
  have hg : 0 < gain := lt_min (by positivity) (by positivity)
  have hghalf : gain ≤ ε / 2 := min_le_left _ _
  refine ⟨ν, gain, hν, hνsmall, hg, ?_, hghalf, min_le_right _ _, ?_⟩
  · exact hghalf.trans (by linarith)
  · rw [hνL]
    linarith only [hε]

/-- Applying the prescribed tail dependency to the actual stationary objects
gives the exact split identity used by the quantitative estimates. This does
not assume any of those estimates. -/
theorem commutator_split_identity_of_deps
    (htail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (hZ : IsJointObservation Q Z) :
    ∃ G J H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ r i, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r (β i)) (G r i)) ∧
      (∀ r i j, (J r i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G r i k ω) ∧
      (∀ τ i, IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      (∀ (τ : ℝ≥0) (i j : Fin d), IntegrableOn (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j))
        (Ici (τ : ℝ))) ∧
      ∀ (τ : ℝ≥0) (s ν : ℝ), 1 ≤ s → (τ : ℝ) ≤ s → 0 ≤ ν →
      ∀ (hs : 0 < s) (i j : Fin d),
        gaussianAverage hd Q s hs (centeredComplexLp Q (X τ i j) - Z (.inl (j,i))) =
          -(gaussianAverage hd Q s hs
            (∫ r in Icc (τ : ℝ) (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j)) +
            gaussianAverage hd Q s hs
            (∫ r in Ici (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j))) := by
  obtain ⟨G, J, H, X, hG, hJ, hX, htailid⟩ := htail d hd D Q hQ β hβ P hP Z hZ
  refine ⟨G, J, H, X, hG, hJ, hX, fun τ i j => (htailid τ i j).1, ?_⟩
  intro τ s ν hs1 hτs hν hs i j
  have hcut : (τ : ℝ) ≤ s ^ (1 + ν) := calc
    _ ≤ s := hτs
    _ = s ^ (1 : ℝ) := (Real.rpow_one s).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hs1 (by linarith only [hν])
  rw [(htailid τ i j).2]
  exact gaussian_tail_split hd Q s hs hcut (htailid τ i j).1


variable {d : ℕ} {Λ r₀ : ℝ} {Q : EnvironmentLaw d Λ r₀}

/-- Each entry of the actual anisotropic homogenized matrix has the same
structural bound as its Euclidean column. -/
theorem norm_homogenized_entry_le (Q : EnvironmentLaw d Λ r₀) (j k : Fin d) :
    ‖(homogenizedCoefficient Q j k : ℂ)‖ ≤ sourceReducedBound Λ := by
  have hcoord (x : Vec d) : |x j| ≤ euclideanNorm x := by
    unfold euclideanNorm euclideanSq dot
    rw [← Real.sqrt_sq_eq_abs (x j)]
    apply Real.sqrt_le_sqrt
    simpa only [pow_two] using!
      (Finset.single_le_sum (fun l _ => mul_self_nonneg (x l)) (Finset.mem_univ j))
  have h := (hcoord ((homogenizedCoefficient Q).mulVec
    (unitVector k))).trans (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q k)
  simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite,
    Complex.norm_real, Real.norm_eq_abs] using! h

/-- Bounded multiplication by the literal coefficient difference a-A. -/
def commutatorEntryMul (Q : EnvironmentLaw d Λ r₀) (j k : Fin d) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  complexCoefficientMul Q j k -
    (homogenizedCoefficient Q j k : ℂ) • ContinuousLinearMap.id ℂ _

/-- Almost-everywhere representative of the actual coefficient multiplier. -/
theorem commutatorEntryMul_coe (Q : EnvironmentLaw d Λ r₀) (j k : Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    commutatorEntryMul Q j k f =ᵐ[reducedLaw Q] fun ω =>
      ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * f ω := by
  have he : commutatorEntryMul Q j k f = complexCoefficientMul Q j k f -
      (homogenizedCoefficient Q j k : ℂ) • f := rfl
  rw [he]
  filter_upwards [Lp.coeFn_sub (complexCoefficientMul Q j k f)
    ((homogenizedCoefficient Q j k : ℂ) • f), complexCoefficientMul_coe Q j k f,
    Lp.coeFn_smul (homogenizedCoefficient Q j k : ℂ) f] with ω h₁ h₂ h₃
  simp only [h₁, Pi.sub_apply, h₂, h₃, Pi.smul_apply, smul_eq_mul,
    Complex.ofReal_sub, sub_mul]

/-- The multiplier constant depends only on ellipticity, not on the law. -/
theorem norm_commutatorEntryMul_apply_le (Q : EnvironmentLaw d Λ r₀) (j k : Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖commutatorEntryMul Q j k f‖ ≤ (2 * sourceReducedBound Λ) * ‖f‖ := by
  change ‖complexCoefficientMul Q j k f -
    (homogenizedCoefficient Q j k : ℂ) • f‖ ≤ _
  calc
    _ ≤ ‖complexCoefficientMul Q j k f‖ +
        ‖(homogenizedCoefficient Q j k : ℂ) • f‖ := norm_sub_le _ _
    _ ≤ sourceReducedBound Λ * ‖f‖ + sourceReducedBound Λ * ‖f‖ := by
      rw [norm_smul]
      exact add_le_add (((complexCoefficientMul Q j k).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right ((norm_complexCoefficientMul_le Q j k).trans
          (mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg Λ])
            (Real.exp_pos (2 * Λ)).le)) (norm_nonneg _)))
        (mul_le_mul_of_nonneg_right (norm_homogenized_entry_le Q j k) (norm_nonneg _))
    _ = _ := by ring

private theorem commutator_sum_coe {ι : Type*}
    (f : ι → Lp ℂ 2 (reducedLaw Q)) (s : Finset ι) :
    (⇑(∑ k ∈ s, f k)) =ᵐ[reducedLaw Q] fun ω => ∑ k ∈ s, f k ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using! Lp.coeFn_zero ℂ 2 (reducedLaw Q)
  | @insert k s hk ih =>
    simp only [Finset.sum_insert hk]
    filter_upwards [Lp.coeFn_add (f k) (∑ l ∈ s, f l), ih] with ω h₁ h₂
    simp only [h₁, Pi.add_apply, h₂]

/-- A literal a.e. flux identity identifies its stationary L2 class with the
finite sum of actual coefficient multipliers. -/
theorem commutator_eq_sum (Q : EnvironmentLaw d Λ r₀)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (J : Lp ℂ 2 (reducedLaw Q)) (j : Fin d)
    (hJ : (J : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G k ω) :
    J = ∑ k, commutatorEntryMul Q j k (G k) := by
  apply Lp.ext
  filter_upwards [hJ, commutator_sum_coe (fun k : Fin d => commutatorEntryMul Q j k (G k))
    Finset.univ, ae_all_iff.mpr (fun k => commutatorEntryMul_coe Q j k (G k))]
    with ω h₁ h₂ h₃
  rw [h₁, h₂]
  exact Finset.sum_congr rfl fun k _ => (h₃ k).symm

/-- The stationary L2 norm of each actual centered commutator component is
controlled by the explicit Euclidean gradient norm. -/
theorem norm_centered_commutator_le (Q : EnvironmentLaw d Λ r₀)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (J : Lp ℂ 2 (reducedLaw Q)) (j : Fin d)
    (hJ : (J : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G k ω) :
    ‖centeredComplexLp Q J‖ ≤
      ((d : ℝ) * (2 * sourceReducedBound Λ)) * ‖WithLp.toLp 2 G‖ := by
  apply (norm_fluxCentered_le J).trans
  rw [commutator_eq_sum Q G J j hJ]
  calc
    _ ≤ ∑ k, ‖commutatorEntryMul Q j k (G k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin d, (2 * sourceReducedBound Λ) * ‖WithLp.toLp 2 G‖ := by
      apply Finset.sum_le_sum
      intro k _
      exact (norm_commutatorEntryMul_apply_le Q j k (G k)).trans
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (WithLp.toLp 2 G) k) (by
          unfold sourceReducedBound
          have := Q.ellipticity_parameter
          positivity))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- Uniqueness transfers any tail-dependency gradient witness to the actual
positive-time semigroup gradient before applying the structural decay bound. -/
theorem commutator_gradient_witness_eq (hd : 2 ≤ d)
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (r : ℝ) (hr : 0 < r)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P r.toNNReal f) G) :
    G = ⇑(hP.gradientOrbit f r) :=
  hG.unique (hP.gradientOrbit_spec f hr)

/-- The new gradient producer supplies a structural power majorant for every
actual centered commutator component, including arbitrary a.e. tail witnesses. -/
theorem centered_commutator_decay (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (_hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
      (r : ℝ), 1 ≤ r → ∀ (i j : Fin d)
      (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (J : Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r.toNNReal (β i)) G →
      ((J : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G k ω) →
      ‖centeredComplexLp Q J‖ ≤ C * r ^ (-1 - (d : ℝ) / 4) := by
  obtain ⟨C, hC, hdec⟩ := finiteXi_gradient_decay hscalar d hd D
  let B := (d : ℝ) * (2 * sourceReducedBound D.ellipticity)
  have hB : 0 < B := by
    dsimp [B, sourceReducedBound]
    have := D.one_le_ellipticity
    have hdpos : 0 < d := by omega
    positivity
  refine ⟨B * C, mul_pos hB hC, ?_⟩
  intro Q hQ β hβ P hP r hr i j G J hG hJ
  have he := commutator_gradient_witness_eq hd hP (β i) r
    (zero_lt_one.trans_le hr) G hG
  have hn : ‖WithLp.toLp 2 G‖ = ‖hP.gradientOrbit (β i) r‖ := by rw [he]
  calc
    _ ≤ B * ‖WithLp.toLp 2 G‖ := norm_centered_commutator_le Q G J j hJ
    _ = B * ‖hP.gradientOrbit (β i) r‖ := by rw [hn]
    _ ≤ B * (C * r ^ (-1 - (d : ℝ) / 4)) :=
      mul_le_mul_of_nonneg_left (hdec Q hQ β hβ P hP r hr i) hB.le
    _ = _ := by ring

/-- The actual anisotropic Gaussian average commutes with every integrable
stationary L2 Bochner integral, including an improper tail. -/
theorem gaussianAverage_integral (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r₀)
    (s : ℝ) (hs : 0 < s) {μ : Measure ℝ}
    {f : ℝ → Lp ℂ 2 (reducedLaw Q)} (hf : Integrable f μ) :
    gaussianAverage hd Q s hs (∫ r, f r ∂μ) =
      ∫ r, gaussianAverage hd Q s hs (f r) ∂μ :=
  ((homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0).integral_comp_comm hf).symm

/-- The zero-force anisotropic Gaussian is a contraction on actual stationary L2. -/
theorem norm_gaussianAverage_le (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r₀)
    (s : ℝ) (hs : 0 < s) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianAverage hd Q s hs f‖ ≤ ‖f‖ := by
  simpa only [gaussianAverage, Complex.zero_im, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_mul, zero_div, Real.exp_zero, one_mul] using!
    norm_homogeneousAverage_le Q ⟨0, by omega⟩ s hs 0 f

/-- A stationary L2 power majorant gives its literal improper Bochner-tail
bound. Integrability is retained from the commutator-tail dependency. -/
theorem norm_integral_power_tail_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : ℝ → E} {a δ C : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hf : IntegrableOn f (Ici a))
    (hb : ∀ r ∈ Ici a, ‖f r‖ ≤ C * r ^ (-1 - δ)) :
    ‖∫ r in Ici a, f r‖ ≤ C * a ^ (-δ) / δ := by
  have hi : IntegrableOn (fun r : ℝ => r ^ (-1 - δ)) (Ici a) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_Ioi_rpow_of_lt (by linarith) ha
  calc
    _ ≤ ∫ r in Ici a, ‖f r‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ r in Ici a, C * r ^ (-1 - δ) := by
      apply integral_mono_ae hf.norm (hi.const_mul C)
      filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
      exact hb r hr
    _ = C * (a ^ (-δ) / δ) := by rw [integral_const_mul, integral_power_tail ha hδ]
    _ = _ := by ring

private theorem sqrt_sum_norm_sq_le_sum {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] (f : ι → E) :
    Real.sqrt (∑ j, ‖f j‖ ^ 2) ≤ ∑ j, ‖f j‖ := by
  have h := Real.sqrt_le_sqrt
    (Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (fun j _ => norm_nonneg (f j)))
  rwa [Real.sqrt_sq (Finset.sum_nonneg fun j _ => norm_nonneg (f j))] at h

/-- The source far-tail estimate for actual anisotropic Gaussian averages,
with the Euclidean component sum and the exact split exponent. -/
theorem gaussian_far_tail_bound (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r₀)
    {f : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)} {s ν δ C : ℝ}
    (hs : 1 ≤ s) (hν : 0 ≤ ν) (hδ : 0 < δ)
    (hi : ∀ j, IntegrableOn (fun r => f r j) (Ici (s ^ (1 + ν))))
    (hb : ∀ r, 1 ≤ r → ∀ j, ‖f r j‖ ≤ C * r ^ (-1 - δ)) :
    Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s (zero_lt_one.trans_le hs)
      (∫ r in Ici (s ^ (1 + ν)), f r j)‖ ^ 2) ≤
      ((d : ℝ) * C / δ) * s ^ (-δ) * s ^ (-ν * δ) := by
  have hspos : 0 < s := zero_lt_one.trans_le hs
  have hcutpos : 0 < s ^ (1 + ν) := Real.rpow_pos_of_pos hspos _
  have hcutone : 1 ≤ s ^ (1 + ν) := Real.one_le_rpow hs (by linarith)
  have hcomp (j : Fin d) :
      ‖gaussianAverage hd Q s hspos (∫ r in Ici (s ^ (1 + ν)), f r j)‖ ≤
        (C / δ) * s ^ (-δ) * s ^ (-ν * δ) := by
    apply (norm_gaussianAverage_le hd Q s hspos _).trans
    apply (norm_integral_power_tail_le hcutpos hδ (hi j)
      (fun r hr => hb r (hcutone.trans hr) j)).trans_eq
    rw [← Real.rpow_mul hspos.le]
    have he : (1 + ν) * -δ = -δ + -ν * δ := by ring
    rw [he, Real.rpow_add hspos]
    ring
  calc
    _ ≤ ∑ j : Fin d, ‖gaussianAverage hd Q s hspos
        (∫ r in Ici (s ^ (1 + ν)), f r j)‖ := sqrt_sum_norm_sq_le_sum _
    _ ≤ ∑ _j : Fin d, (C / δ) * s ^ (-δ) * s ^ (-ν * δ) :=
      Finset.sum_le_sum fun j _ => hcomp j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- Structural far-tail control is derived for the very same G,J,H,X witnesses
as the exact commutator-tail dependency. No norm estimate is a new premise. -/
theorem commutator_far_tail_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (htail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P),
    ∃ G J H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ r i, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r (β i)) (G r i)) ∧
      (∀ r i j, (J r i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G r i k ω) ∧
      (∀ τ i, IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      (∀ (τ : ℝ≥0) i j, IntegrableOn (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j))
        (Ici (τ : ℝ)) ∧
        centeredComplexLp Q (X τ i j) - Z (.inl (j,i)) =
          -(∫ r in Ici (τ : ℝ), centeredComplexLp Q (J r.toNNReal i j))) ∧
      ∀ s : ℝ, 1 ≤ s → ∀ ν : ℝ, 0 ≤ ν → ∀ hs : 0 < s, ∀ i : Fin d,
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Ici (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
          C * s ^ (-(d : ℝ) / 4) * s ^ (-ν * (d : ℝ) / 4) := by
  obtain ⟨C, hC, hdec⟩ := centered_commutator_decay hscalar d hd D
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  refine ⟨(d : ℝ) * C / ((d : ℝ) / 4), div_pos (mul_pos hdpos hC) (by positivity), ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨G, J, H, X, hG, hJ, hX, hid⟩ := htail d hd D Q hQ β hβ P hP Z hZ
  refine ⟨G, J, H, X, hG, hJ, hX, hid, ?_⟩
  intro s hs ν hν hspos i
  have hcut : 0 ≤ s ^ (1 + ν) := (Real.rpow_pos_of_pos hspos _).le
  have hi (j : Fin d) : IntegrableOn
      (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j)) (Ici (s ^ (1 + ν))) := by
    simpa only [Real.coe_toNNReal _ hcut] using! (hid (s ^ (1 + ν)).toNNReal i j).1
  have hb (r : ℝ) (hr : 1 ≤ r) (j : Fin d) :=
    hdec Q hQ β hβ P hP r hr i j (G r.toNNReal i) (J r.toNNReal i j)
      (hG r.toNNReal i) (hJ r.toNNReal i j)
  simpa only [neg_div, mul_div_assoc] using!
    gaussian_far_tail_bound hd Q hs hν (by positivity : 0 < (d : ℝ) / 4) hi hb

private theorem coefficient_clock_observations
    (Q : EnvironmentLaw d Λ r₀) :
    ∃ (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a ∧ IsReducedClockObservation Q μ := by
  letI := reducedLaw_probability Q
  have ha (j k : Fin d) : MemLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
      2 (reducedLaw Q) := (memLp_reduced_coefficient_complex Q j k).mono_exponent le_top
  have hm : MemLp (fun ω : FieldPair d => (ω.2 0 : ℂ)) 2 (reducedLaw Q) := by
    apply (memLp_top_of_bound
      (Complex.continuous_ofReal.comp Clock.continuous_clockAtOrigin).aestronglyMeasurable
      (sourceReducedBound Λ) ?_).mono_exponent le_top
    filter_upwards [Clock.ae_abs_clockAtOrigin_le Q] with ω hω
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using! hω
  exact ⟨fun j k => (ha j k).toLp _, hm.toLp _,
    fun j k => (ha j k).coeFn_toLp, hm.coeFn_toLp⟩

/-- The weak-flux dependency and the tail dependency describe the same
actual zero-force commutator, even though they choose witnesses separately. -/
theorem weak_flux_witness_eq (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (i : Fin d)
    (G G' J' : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t (β i)) G)
    (hf : IsEndpointWeakFlux hd Q (.inl i) 0 a
      (indexedEndpoint hd Q (.inl i) 0 P Pdag β a μ t) G' J') :
    ∀ j, J' j = ∑ k, commutatorEntryMul Q j k (G k) := by
  have he : indexedEndpoint hd Q (.inl i) 0 P Pdag β a μ t =
      centeredComplexLp Q (P t (β i)) := by
    simp only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero]
  have hh := hf.1
  rw [he] at hh
  have hg : G' = G := hh.unique hG.centered
  intro j
  apply commutator_eq_sum Q G (J' j) j
  filter_upwards [hf.2 j, ae_all_iff.mpr (ha j)] with ω hfω haω
  rw [hfω]
  apply Finset.sum_congr rfl
  intro k _
  simp only [haω k, hg, sub_zero, Complex.ofReal_sub]

/-- Specialization of weak flux at p=2 and zero force produces a structural
bound for every actual commutator gradient witness. -/
theorem commutator_weak_flux_decay
    (hflux : node_l_u3A_forced_u2D_fluxStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε : ℝ, ∃ L : ℕ, ∃ t₀ C : ℝ,
      0 < ε ∧ 1 ≤ t₀ ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (_hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
      (r : ℝ), t₀ ≤ r → ∀ (i : Fin d)
      (G J : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r.toNNReal (β i)) G →
      (∀ j, (J j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G k ω) →
      ∀ s : ℝ, 1 ≤ s → ∀ hs : 0 < s,
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (centeredComplexLp Q (J j))‖ ^ 2) ≤
          C * r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (1 + r / s) ^ L := by
  obtain ⟨ε, η, L, hε, hη, hflux⟩ := hflux d hd D
  obtain ⟨growth₀, t₀, Cf, hgrowth, ht₀, hCf, hflux⟩ := hflux 2 le_rfl
  obtain ⟨K, hK, hdec⟩ := finiteXi_centered_drift_decay hscalar d hd D
  let K' := max 1 K
  have hK' : 1 ≤ K' := le_max_left _ _
  refine ⟨ε, L 0, max 8 t₀, Cf 0 * K', hε,
    (by exact (by norm_num : (1 : ℝ) ≤ 8).trans (le_max_left _ _)),
    mul_pos (hCf 0) (zero_lt_one.trans_le hK'), ?_⟩
  intro Q hQ β hβ P hP r hr i G J hG hJ s hs hspos
  have hr8 : 8 ≤ r := (le_max_left _ _).trans hr
  have hrpos : 0 < r := by linarith only [hr8]
  have hrcoe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal _ hrpos.le
  obtain ⟨a, μ, ha, hμ⟩ := coefficient_clock_observations Q
  let Pdag := fun t => complexL2Transpose (reducedLaw Q) (P t)
  obtain ⟨G', J', hweak, hest⟩ := hflux.1 Q hQ β a μ hβ ha hμ 0 P Pdag hP
    (isComplexTransposeSemigroup_complexL2Transpose Q P) (.inl i)
  have he (j : Fin d) : J' r.toNNReal j = J j := by
    rw [weak_flux_witness_eq hd Q β a μ ha P Pdag r.toNNReal i G
      (G' r.toNNReal) (J' r.toNNReal) hG (hweak r.toNNReal (by rwa [hrcoe])),
      ← commutator_eq_sum Q G (J j) j (hJ j)]
  have hmem : MemLp
      (indexedEndpoint hd Q (.inl i) 0 P Pdag β a μ (r.toNNReal / 8) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q) := by
    simpa only [ENNReal.ofReal_ofNat] using! Lp.memLp _
  have hstart : (eLpNorm
      (indexedEndpoint hd Q (.inl i) 0 P Pdag β a μ (r.toNNReal / 8) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
        K' * Real.exp (growth₀ * ‖(0 : ℂ)‖ ^ 2 * (r.toNNReal : ℝ) / 8) *
          (((r.toNNReal : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖(0 : ℂ)‖ * ((r.toNNReal : ℝ) / 8) ^ (-(d : ℝ) / 4)) := by
    simp only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero,
      ENNReal.ofReal_ofNat, ← Lp.norm_def, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      mul_zero, zero_div, Real.exp_zero, mul_one, zero_mul, add_zero]
    have hh := hdec Q hQ β hβ P hP (r.toNNReal / 8) (by
      simp only [NNReal.coe_div, NNReal.coe_ofNat, hrcoe]
      exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr (by simpa using! hr8)) i
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (le_max_right 1 K) (Real.rpow_nonneg (by positivity) _)
  have hb := (hest r.toNNReal (by rw [hrcoe]; exact (le_max_right _ _).trans hr)
    (by simp only [norm_zero, zero_mul]; positivity)
    growth₀ K' le_rfl hK' hmem hstart s hs hspos 0 (fun z => Fin.elim0 z)).2
  have heq : ∀ f : Lp ℂ 2 (reducedLaw Q),
      gaussianDerivativeAverage hd Q s hspos 0 (fun z => Fin.elim0 z) f =
        gaussianAverage hd Q s hspos f := by
    intro f
    simp only [gaussianDerivativeAverage, iteratedFDeriv_zero_apply,
      gaussianAverage, ← homogenizedGaussianKernel_neg_force, neg_zero]
  simp only [ENNReal.ofReal_ofNat, ← Lp.norm_def, he, heq, norm_zero,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_mul, zero_div,
    Real.exp_zero, mul_one, Nat.cast_zero, zero_div, sub_zero, hrcoe] at hb
  exact hb

/-- Integrating the actual componentwise weak-flux bound gives the first
split estimate. All constants in this analytic step remain explicit. -/
theorem gaussian_near_tail_bound (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ r₀)
    {f : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)} {τ s ε ν C : ℝ} (L : ℕ) (hC : 0 ≤ C)
    (hτ : 1 ≤ τ) (hτs : τ ≤ s) (hε : 0 < ε) (hν : 0 ≤ ν)
    (hνL : ν * L ≤ ε / 2)
    (hi : ∀ j, IntegrableOn (fun r => f r j) (Icc τ (s ^ (1 + ν))))
    (hb : ∀ r ∈ Icc τ (s ^ (1 + ν)), ∀ j,
      ‖gaussianAverage hd Q s (zero_lt_one.trans_le (hτ.trans hτs)) (f r j)‖ ≤
        C * r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (1 + r / s) ^ L) :
    Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s (zero_lt_one.trans_le (hτ.trans hτs))
      (∫ r in Icc τ (s ^ (1 + ν)), f r j)‖ ^ 2) ≤
      ((d : ℝ) * (C * s ^ (-(d : ℝ) / 4))) *
        ((2 : ℝ) ^ L / ε * (τ ^ (-ε) + s ^ (-ε / 2))) := by
  have hτpos : 0 < τ := zero_lt_one.trans_le hτ
  have hspos : 0 < s := hτpos.trans_le hτs
  let w := fun r : ℝ => r ^ (-1 - ε) * (1 + r / s) ^ L
  have hw : IntegrableOn w (Icc τ (s ^ (1 + ν))) := by
    apply ContinuousOn.integrableOn_Icc
    exact (continuousOn_id.rpow_const (fun r hr => Or.inl (hτpos.trans_le hr.1).ne')).mul
      ((continuousOn_const.add (continuousOn_id.div_const s)).pow L)
  have hcomp (j : Fin d) :
      ‖gaussianAverage hd Q s hspos (∫ r in Icc τ (s ^ (1 + ν)), f r j)‖ ≤
        (C * s ^ (-(d : ℝ) / 4)) *
          ((2 : ℝ) ^ L / ε * (τ ^ (-ε) + s ^ (-ε / 2))) := by
    rw [gaussianAverage_integral hd Q s hspos (hi j)]
    calc
      _ ≤ ∫ r in Icc τ (s ^ (1 + ν)),
          (C * s ^ (-(d : ℝ) / 4)) * w r := by
        apply norm_integral_le_of_norm_le (hw.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        exact (hb r hr j).trans_eq (by dsimp [w]; ring)
      _ = (C * s ^ (-(d : ℝ) / 4)) * (∫ r in Icc τ (s ^ (1 + ν)), w r) :=
        integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (integral_weak_flux_weight_le L hτ hτs hε hν hνL) (by positivity)
  calc
    _ ≤ ∑ j : Fin d, ‖gaussianAverage hd Q s hspos
        (∫ r in Icc τ (s ^ (1 + ν)), f r j)‖ := sqrt_sum_norm_sq_le_sum _
    _ ≤ ∑ _j : Fin d, (C * s ^ (-(d : ℝ) / 4)) *
        ((2 : ℝ) ^ L / ε * (τ ^ (-ε) + s ^ (-ε / 2))) :=
      Finset.sum_le_sum fun j _ => hcomp j
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]; ring

/-- The complete zero-order split-tail estimate, with one structural choice
of all constants and the same actual commutator witnesses in every estimate. -/
theorem commutator_zero_order_of_deps
    (hflux : node_l_u3A_forced_u2D_fluxStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (htail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt) :
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ ε L₀ ν gain t₀ : ℝ, ∃ C : ℝ,
      0 < ε ∧ 0 < L₀ ∧ 0 < ν ∧ ν < ε / (4 * L₀) ∧
      0 < gain ∧ gain ≤ ε ∧ gain ≤ ε / 2 ∧ gain ≤ ν * (d : ℝ) / 4 ∧
      1 ≤ t₀ ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
    ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ G J H X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ r i, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P r (β i)) (G r i)) ∧
      (∀ r i j, (J r i j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, ((ω.1 0 j k - homogenizedCoefficient Q j k : ℝ) : ℂ) * G r i k ω) ∧
      (∀ τ i, IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (H τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) →
      (∀ (s : ℝ), (τ : ℝ) ≤ s → ∀ hs : 0 < s, ∀ i : Fin d,
        (∀ j, IntegrableOn (fun r : ℝ => centeredComplexLp Q (J r.toNNReal i j))
          (Set.Ici (τ : ℝ))) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Set.Icc (τ : ℝ) (s ^ (1 + ν)),
            centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
          C * s ^ (-(d : ℝ) / 4) *
            ((τ : ℝ) ^ (-ε) + s ^ (-ε / 2)) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Set.Ici (s ^ (1 + ν)),
            centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
          C * s ^ (-(d : ℝ) / 4) * s ^ (-ν * (d : ℝ) / 4) ∧
        Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ^ 2) ≤
          C * (τ : ℝ) ^ (-gain) * s ^ (-(d : ℝ) / 4)) := by
  intro d hd D
  obtain ⟨ε, L, t₀, Cw, hε, ht₀, hCw, hw⟩ := commutator_weak_flux_decay hflux hscalar d hd D
  obtain ⟨Cf, hCf, hf⟩ := commutator_far_tail_of_deps hscalar htail d hd D
  let L₀ : ℝ := (L : ℝ) + 1
  have hL₀ : 0 < L₀ := by dsimp only [L₀]; positivity
  obtain ⟨ν, gain, hν, hνsmall, hg, hgε, hghalf, hgν, hνL₀⟩ :=
    exists_split_parameters hε hL₀ d hd
  have hνL : ν * (L : ℝ) ≤ ε / 2 := by
    apply le_trans _ hνL₀
    exact mul_le_mul_of_nonneg_left (by dsimp only [L₀]; linarith) hν.le
  let A : ℝ := (d : ℝ) * Cw * ((2 : ℝ) ^ L / ε)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let B : ℝ := A + Cf
  have hB : 0 < B := by dsimp only [B]; positivity
  have hAB : A ≤ B := by dsimp only [B]; linarith only [hCf]
  have hCfB : Cf ≤ B := by dsimp only [B]; linarith only [hA]
  have hBC : B ≤ 3 * B := by linarith only [hB]
  refine ⟨ε, L₀, ν, gain, t₀, 3 * B, hε, hL₀, hν, hνsmall,
    hg, hgε, hghalf, hgν, ht₀, mul_pos (by norm_num) hB, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨G, J, H, X, hG, hJ, hX, hid, hfar⟩ := hf Q hQ β Z hβ hZ P hP
  refine ⟨G, J, H, X, hG, hJ, hX, ?_⟩
  intro τ hτ s hτs hs i
  have hτone : 1 ≤ (τ : ℝ) := ht₀.trans hτ
  have hsone : 1 ≤ s := hτone.trans hτs
  have hcut : (τ : ℝ) ≤ s ^ (1 + ν) := by
    apply hτs.trans
    calc
      s = s ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hsone (by linarith only [hν])
  have hnear := gaussian_near_tail_bound hd Q L hCw.le hτone hτs hε hν.le hνL
    (fun j => (hid τ i j).1.mono_set (fun _ hr => hr.1))
  have hcomponent (r : ℝ) (hr : r ∈ Icc (τ : ℝ) (s ^ (1 + ν))) (j : Fin d) :
      ‖gaussianAverage hd Q s hs (centeredComplexLp Q (J r.toNNReal i j))‖ ≤
        Cw * r ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (1 + r / s) ^ L := by
    have he := hw Q hQ β hβ P hP r (hτ.trans hr.1) i
      (G r.toNNReal i) (J r.toNNReal i) (hG r.toNNReal i) (hJ r.toNNReal i) s hsone hs
    apply le_trans _ he
    simpa only [PiLp.norm_eq_of_L2, PiLp.toLp_apply] using!
      (PiLp.norm_apply_le (WithLp.toLp 2 (fun j =>
        gaussianAverage hd Q s hs (centeredComplexLp Q (J r.toNNReal i j)))) j)
  have hn := hnear hcomponent
  have hfar' := hfar s hsone ν hν.le hs i
  have hn' : Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
      (∫ r in Icc (τ : ℝ) (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
      B * s ^ (-(d : ℝ) / 4) * ((τ : ℝ) ^ (-ε) + s ^ (-ε / 2)) := by
    calc
      _ ≤ A * s ^ (-(d : ℝ) / 4) * ((τ : ℝ) ^ (-ε) + s ^ (-ε / 2)) :=
        hn.trans_eq (by dsimp only [A]; ring)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hAB (by positivity)) (by positivity)
  have hf' : Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
      (∫ r in Ici (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) ≤
      B * s ^ (-(d : ℝ) / 4) * s ^ (-ν * (d : ℝ) / 4) :=
    hfar'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCfB (by positivity)) (by positivity))
  refine ⟨fun j => (hid τ i j).1, hn'.trans ?_, hf'.trans ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (by positivity)) (by positivity)
  · exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hBC (by positivity)) (by positivity)
  · have he (j : Fin d) := gaussian_tail_split hd Q s hs hcut (hid τ i j).1
    simp_rw [← (hid τ i _).2] at he
    calc
      _ = Real.sqrt (∑ j : Fin d, ‖gaussianAverage hd Q s hs
          (∫ r in Icc (τ : ℝ) (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j)) +
          gaussianAverage hd Q s hs
          (∫ r in Ici (s ^ (1 + ν)), centeredComplexLp Q (J r.toNNReal i j))‖ ^ 2) := by
        simp_rw [he, norm_neg]
      _ ≤ _ := (sqrt_sum_norm_add_le _ _).trans (add_le_add hn' hf')
      _ = B * s ^ (-(d : ℝ) / 4) *
          ((τ : ℝ) ^ (-ε) + s ^ (-ε / 2) + s ^ (-ν * ((d : ℝ) / 4))) := by
        rw [show -ν * ((d : ℝ) / 4) = -ν * (d : ℝ) / 4 by ring]
        ring
      _ ≤ B * s ^ (-(d : ℝ) / 4) * (3 * (τ : ℝ) ^ (-gain)) := by
        apply mul_le_mul_of_nonneg_left
          (common_gain hτone hτs hg.le hgε hghalf (by nlinarith only [hgν]))
        positivity
      _ = _ := by ring

private theorem stationarySchwartzAverage_translation (Q : EnvironmentLaw d Λ r₀)
    (ψ : SchwartzMap (Vec d) ℂ) (a : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q ψ (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a (stationarySchwartzAverage Q ψ f) := by
  unfold stationarySchwartzAverage
  change _ = (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap
    (∫ x : Vec d, ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  rw [← (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a).toContinuousLinearMap.integral_comp_comm
    (integrable_stationarySchwartzAverage_integrand Q ψ f)]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [map_smul]
    change ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a f) =
      ψ (-x) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) a
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
    rw [← complexTranslation_add, ← complexTranslation_add, add_comm x a]

/-- A Schwartz average preserves any existing strong horizontal derivative. -/
private theorem horizontalDerivative_stationarySchwartzAverage
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f) (stationarySchwartzAverage Q ψ g) := by
  let A := stationarySchwartzAverageCLM Q ψ
  have h := (A.continuous.tendsto g).comp hf
  change Tendsto (fun t : ℝ => A ((t : ℂ)⁻¹ •
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (A g)) at h
  unfold HasComplexHorizontalDerivative
  simpa only [map_smul, map_sub, A, stationarySchwartzAverageCLM_apply,
    stationarySchwartzAverage_translation] using! h

/-- Spatial integration by parts identifies the derivative kernel on an existing horizontal jet. -/
private theorem stationarySchwartzAverage_horizontalDerivative
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    stationarySchwartzAverage Q ψ g =
      stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  have hg (x : Vec d) : HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
    have hd := (((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hf.hasDerivAt_orbit 0)
    simp only [zero_smul, complexTranslation_zero] at hd
    change HasDerivAt (fun t : ℝ => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f))
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) 0 at hd
    simpa only [HasLineDerivAt, ← complexTranslation_add] using! hd
  have hk (x : Vec d) : HasLineDerivAt ℝ (fun y => ψ (-y)) (-D (-x)) x (unitVector j) := by
    convert ((ψ.hasFDerivAt (-x)).comp x ((hasFDerivAt_id x).neg)).hasLineDerivAt (unitVector j) using 1 <;>
      (try simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg]) <;> rfl
  have hi := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (by simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, Pi.neg_apply] using! (integrable_stationarySchwartzAverage_integrand Q D f).neg)
    (integrable_stationarySchwartzAverage_integrand Q ψ g)
    (integrable_stationarySchwartzAverage_integrand Q ψ f) (fun x _ => hk x) (fun x _ => hg x)
  simpa only [ContinuousLinearMap.lsmul_apply, neg_smul, integral_neg, neg_neg, stationarySchwartzAverage, D] using! hi

/-- Every stationary Schwartz average has the literal differentiated-kernel horizontal derivative. -/
private theorem stationarySchwartzAverage_hasHorizontalDerivative
    (Q : EnvironmentLaw d Λ r₀) (j : Fin d) (ψ : SchwartzMap (Vec d) ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ f)
      (stationarySchwartzAverage Q ((SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp
        (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ) f) := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) ψ
  let S := {u : Lp ℂ 2 (reducedLaw Q) |
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
      (stationarySchwartzAverage Q ψ u) (stationarySchwartzAverage Q D u)}
  have hclosed : IsClosed S :=
    (isClosed_complexHorizontalDerivative_graph (reducedLaw Q) (reducedLaw_stationary Q) j).preimage
      ((stationarySchwartzAverageCLM Q ψ).continuous.prodMk (stationarySchwartzAverageCLM Q D).continuous)
  have hsub : {u | IsComplexHorizontallySmooth Q u} ⊆ S := by
    intro u hu
    obtain ⟨J, hJ0, hJ⟩ := hu
    have hjet : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j u (J [j]) := by
      simpa only [hJ0] using! hJ [] j
    have he := stationarySchwartzAverage_horizontalDerivative Q j ψ hjet
    change HasComplexHorizontalDerivative _ _ _ _ _
    rw [← he]
    exact horizontalDerivative_stationarySchwartzAverage Q j ψ hjet
  exact hclosed.closure_subset (closure_mono hsub (dense_complexHorizontallySmooth Q f))


/-- The stationary Schwartz realization is exactly the frozen derivative average. -/
theorem gaussianDerivativeAverage_eq_schwartz (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs k dirs f =
      stationarySchwartzAverage Q
        (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs) f := by
  simp only [gaussianDerivativeAverage, stationarySchwartzAverage,
    unforcedGaussianDerivativeSchwartz_apply]

/-- An arbitrary differentiated Gaussian average has the next actual horizontal
coordinate derivative, with no smoothness assumption on the random field. -/
theorem gaussianDerivativeAverage_hasHorizontalDerivative (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin (k + 1) → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) (dirs 0)
      (gaussianDerivativeAverage hd Q s hs k (Fin.tail dirs) f)
      (gaussianDerivativeAverage hd Q s hs (k + 1) dirs f) := by
  simp only [gaussianDerivativeAverage_eq_schwartz]
  exact stationarySchwartzAverage_hasHorizontalDerivative
    Q (dirs 0) (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k (Fin.tail dirs)) f

/-- Arbitrary-order derivative smoothing reserves half the Gaussian time.
Uniqueness of actual horizontal derivatives extends the semigroup identity
at order zero to every order. -/
theorem gaussianDerivativeAverage_half_split (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs k dirs f =
      gaussianDerivativeAverage hd Q (s / 2) (half_pos hs) k dirs
        (gaussianAverage hd Q (s / 2) (half_pos hs) f) := by
  induction k with
  | zero =>
    have he (t : ℝ) (ht : 0 < t) (g : Lp ℂ 2 (reducedLaw Q)) :
        gaussianDerivativeAverage hd Q t ht 0 dirs g = gaussianAverage hd Q t ht g := by
      simp only [gaussianDerivativeAverage, iteratedFDeriv_zero_apply, gaussianAverage,
        ← homogenizedGaussianKernel_neg_force, neg_zero]
    simp only [he]
    have hh := homogeneousAverage_add Q ⟨0, by omega⟩ (s / 2) (s / 2)
      (half_pos hs) (half_pos hs) 0 f
    simpa only [add_halves] using! hh.symm
  | succ k ih =>
    have hleft := gaussianDerivativeAverage_hasHorizontalDerivative hd Q s hs k dirs f
    have hright := gaussianDerivativeAverage_hasHorizontalDerivative hd Q (s / 2)
      (half_pos hs) k dirs (gaussianAverage hd Q (s / 2) (half_pos hs) f)
    rw [ih] at hleft
    exact hleft.unique hright

/-- At time one every coordinate derivative has a structural integral norm
bound. The witness precedes the law and the derivative directions. -/
theorem exists_unit_derivative_integral_bound (d : ℕ) (Λ : ℝ) (hΛ : 1 ≤ Λ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ r₀) (i : Fin d)
      (dirs : Fin k → Fin d),
      (∫ x : Vec d, ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖) ≤ C := by
  let n := (volume : Measure (Vec d)).integrablePower
  let W := (2 : ℝ) ^ n * (∫ x : Vec d, (1 + ‖x‖) ^ (-(n : ℝ)))
  let C₀ := gaussianSchwartzOrderBound d Λ 0 k
  let C₁ := gaussianSchwartzOrderBound d Λ n k
  let E := Real.exp (C₀ + C₁)
  have h₀ : 0 < C₀ := gaussianSchwartzOrderBound_pos d Λ hΛ 0 k
  have h₁ : 0 < C₁ := gaussianSchwartzOrderBound_pos d Λ hΛ n k
  have hW : 0 ≤ W := mul_nonneg (by positivity)
    (integral_nonneg fun x => Real.rpow_nonneg (by positivity) _)
  refine ⟨W * (C₀ + C₁) * E + 1, by dsimp only [E]; positivity, ?_⟩
  intro r₀ Q i dirs
  have hb (m : ℕ) (hC : gaussianSchwartzOrderBound d Λ m k ≤ C₀ + C₁) (x : Vec d) :
      (1 + euclideanNorm x) ^ m * ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖ ≤ gaussianSchwartzOrderBound d Λ m k * E := by
    have hh := homogenizedGaussianKernel_weighted_iteratedFDeriv_apply_bound
      Q i 1 zero_lt_one (by norm_num) le_rfl 0 x m k (fun j => unitVector (dirs j))
    simp only [euclideanNorm_unitVector_eq_one, Finset.prod_const_one, mul_one,
      norm_zero, add_zero, one_pow] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hC)
      (gaussianSchwartzOrderBound_pos d Λ hΛ m k).le)
  have hb₀ (x : Vec d) : ‖iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
        (fun j => unitVector (dirs j))‖ ≤ C₀ * E := by
    simpa only [pow_zero, one_mul] using! hb 0 (by dsimp only [C₀]; linarith) x
  have hb₁ (x : Vec d) : ‖x‖ ^ n * ‖iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
        (fun j => unitVector (dirs j))‖ ≤ C₁ * E := by
    apply (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (norm_nonneg x)
        ((norm_vec_le_euclideanNorm x).trans (le_add_of_nonneg_left zero_le_one)) n)
      (norm_nonneg _)).trans
    exact hb n (by dsimp only [C₁]; linarith) x
  have hi := integral_pow_mul_le_of_le_of_pow_mul_le (μ := (volume : Measure (Vec d)))
    (k := 0) hb₀ (by simpa only [zero_add] using! hb₁)
  simp only [pow_zero, one_mul] at hi
  apply hi.trans
  change W * (C₀ * E + C₁ * E) ≤ W * (C₀ + C₁) * E + 1
  nlinarith only

/-- Exact parabolic scaling of every literal coordinate derivative. -/
theorem gaussianDerivativeKernel_scale (Q : EnvironmentLaw d Λ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j)) =
      (s ^ (-(d : ℝ) / 2) * ((Real.sqrt s)⁻¹) ^ k) •
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0)
          ((Real.sqrt s)⁻¹ • x) (fun j => unitVector (dirs j)) := by
  let g : Vec d →L[ℝ] Vec d := (Real.sqrt s)⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  let K := homogenizedGaussianKernel Q i 1 zero_lt_one 0
  have hK : ContDiff ℝ k K :=
    (homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl 0).smooth k
  have he : homogenizedGaussianKernel Q i s hs 0 =
      fun x => s ^ (-(d : ℝ) / 2) • (K ∘ g) x :=
    funext (homogenizedGaussianKernel_zero_scale Q i s hs)
  rw [he, iteratedFDeriv_const_smul_apply' (hK.comp g.contDiff).contDiffAt,
    g.iteratedFDeriv_comp_right hK x le_rfl]
  change s ^ (-(d : ℝ) / 2) •
    (iteratedFDeriv ℝ k K (g x) (fun j => (Real.sqrt s)⁻¹ • unitVector (dirs j))) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul]
  rfl

private theorem sqrt_inv_pow {s : ℝ} (hs : 0 < s) (n : ℕ) :
    ((Real.sqrt s)⁻¹) ^ n = s ^ (-(n : ℝ) / 2) := by
  rw [inv_pow, ← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_mul hs.le,
    ← Real.rpow_neg hs.le]
  congr 1
  ring

/-- The derivative-kernel integral norm has its exact parabolic scaling. -/
theorem gaussianDerivativeKernel_integral_scale (Q : EnvironmentLaw d Λ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    (∫ x : Vec d, ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j))‖) =
      s ^ (-(k : ℝ) / 2) * (∫ x : Vec d, ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖) := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hpoint (x : Vec d) :
      ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (c • x)
        (fun j => unitVector (dirs j))‖ =
      ((c ^ d)⁻¹ * (c⁻¹) ^ k) * ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
          (fun j => unitVector (dirs j))‖ := by
    rw [gaussianDerivativeKernel_scale]
    have hcoef : s ^ (-(d : ℝ) / 2) = (c ^ d)⁻¹ := by
      rw [← sqrt_inv_pow hs d, inv_pow]
    rw [hcoef, inv_smul_smul₀ hc.ne', norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _))
        (pow_nonneg (inv_nonneg.mpr hc.le) _))]
  have he := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
      (fun j => unitVector (dirs j))‖) c
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _)), smul_eq_mul] at he
  simp_rw [hpoint] at he
  rw [integral_const_mul, mul_assoc] at he
  have he' := (mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d hc.ne')) he).symm
  simpa only [c, sqrt_inv_pow hs k] using! he'

/-- The structural operator bound for every fixed coordinate order, with its
constant chosen before the law, time, directions and random datum. -/
theorem exists_gaussianDerivativeAverage_bound (d : ℕ) (hd : 2 ≤ d)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r₀ : ℝ) (Q : EnvironmentLaw d Λ r₀)
      (s : ℝ) (hs : 0 < s) (dirs : Fin k → Fin d) (f : Lp ℂ 2 (reducedLaw Q)),
      ‖gaussianDerivativeAverage hd Q s hs k dirs f‖ ≤ C * s ^ (-(k : ℝ) / 2) * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := exists_unit_derivative_integral_bound d Λ hΛ k
  refine ⟨C, hC, ?_⟩
  intro r₀ Q s hs dirs f
  apply (norm_gaussianDerivativeAverage_le hd Q s hs k dirs f).trans
  rw [gaussianDerivativeKernel_integral_scale]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (mul_le_mul_of_nonneg_left (hb r₀ Q ⟨0, by omega⟩ dirs)
    (Real.rpow_nonneg hs.le _)).trans_eq (mul_comm _ _)

/-- A scalar operator bound controls the explicit Euclidean component sum.
The harmless dimension factor avoids changing the frozen coordinate carrier. -/
theorem sqrt_sum_operator_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] {T : E → E} {C : ℝ} (hC : 0 ≤ C)
    (hT : ∀ f, ‖T f‖ ≤ C * ‖f‖) (f : ι → E) :
    Real.sqrt (∑ j, ‖T (f j)‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * C) * Real.sqrt (∑ j, ‖f j‖ ^ 2) := by
  calc
    _ ≤ ∑ j, ‖T (f j)‖ := sqrt_sum_norm_sq_le_sum _
    _ ≤ ∑ _j : ι, C * Real.sqrt (∑ j, ‖f j‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      apply (hT (f j)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      simpa only [PiLp.norm_eq_of_L2, PiLp.toLp_apply] using!
        (PiLp.norm_apply_le (WithLp.toLp 2 f) j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end EinsteinFull.Blueprint.SplitTail

namespace EinsteinFull.Blueprint
open EinsteinRelation SplitTail

/-- The exact split-tail graph reduction, with the four prescribed dependencies
and structural choices before every actual environment and observation.
The local graph binder is retained in prescribed order; the adopted actual
gradient decay producer already derives the needed bound from scalar alone. -/
@[nolint unusedArguments]
theorem node_l_u3A_finite_u2D_xi_u23_split_u2D_tail_of_deps
    (hflux : node_l_u3A_forced_u2D_fluxStmt)
    (hscalar : node_p_u3A_scalarStmt)
    (_hlocal : node_l_u3A_forced_u2D_localStmt)
    (htail : node_l_u3A_finite_u2D_xi_u23_commutator_u2D_tailStmt) :
    node_l_u3A_finite_u2D_xi_u23_split_u2D_tailStmt := by
  intro d hd D
  obtain ⟨ε, L₀, ν, gain, t₀, C₀, hε, hL₀, hν, hνsmall, hg, hgε, hghalf, hgν,
    ht₀, hC₀, hz⟩ := commutator_zero_order_of_deps hflux hscalar htail d hd D
  have hbound (k : ℕ) := exists_gaussianDerivativeAverage_bound d hd D.ellipticity
    D.one_le_ellipticity k
  choose B hB hb using hbound
  let A := fun k : ℕ => (d : ℝ) * B k * C₀ * (2 : ℝ) ^ ((d : ℝ) / 4 + (k : ℝ) / 2)
  have hA (k : ℕ) : 0 ≤ A k := by
    have := (hB k).le
    dsimp only [A]
    positivity
  let Cder := fun k : ℕ => C₀ + A k
  have hCder (k : ℕ) : 0 < Cder k := add_pos_of_pos_of_nonneg hC₀ (hA k)
  have hC₀der (k : ℕ) : C₀ ≤ Cder k := le_add_of_nonneg_right (hA k)
  refine ⟨ε, L₀, ν, gain, t₀, Cder, hε, hL₀, hν, hνsmall, hg, hgε, hghalf, hgν,
    ht₀, hCder, ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨G, J, H, X, hG, hJ, hX, hz⟩ := hz Q hQ β Z hβ hZ P hP
  refine ⟨G, J, H, X, hG, hJ, hX, ?_⟩
  intro τ hτ
  refine ⟨?_, ?_⟩
  · intro s hτs hs i
    obtain ⟨hi, hn, hf, hc⟩ := hz τ hτ s hτs hs i
    refine ⟨hi, hn.trans ?_, hf.trans ?_, hc.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC₀der 0) (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC₀der 0) (by positivity)) (by positivity)
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC₀der 0) (by positivity)) (by positivity)
  · intro s hτs hs i k dirs
    have hhalf : (τ : ℝ) ≤ s / 2 := by linarith only [hτs]
    have hh := (hz τ hτ (s / 2) hhalf (half_pos hs) i).2.2.2
    simp_rw [gaussianDerivativeAverage_half_split hd Q s hs k dirs]
    have hop := sqrt_sum_operator_le
      (mul_nonneg (hB k).le (Real.rpow_nonneg (half_pos hs).le _))
      (hb k D.dependenceRange Q (s / 2) (half_pos hs) dirs)
      (fun j => gaussianAverage hd Q (s / 2) (half_pos hs)
        (centeredComplexLp Q (X τ i j) - Z (.inl (j,i))))
    simp only [Fintype.card_fin] at hop
    have hBk : 0 ≤ B k := (hB k).le
    apply (hop.trans (mul_le_mul_of_nonneg_left hh (by positivity))).trans
    have hscale : (s / 2) ^ (-(k : ℝ) / 2) * (s / 2) ^ (-(d : ℝ) / 4) =
        (2 : ℝ) ^ ((d : ℝ) / 4 + (k : ℝ) / 2) *
          s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) := by
      rw [← Real.rpow_add (half_pos hs), Real.div_rpow hs.le (by norm_num)]
      have he : -(k : ℝ) / 2 + -(d : ℝ) / 4 =
          -((d : ℝ) / 4 + (k : ℝ) / 2) := by ring
      rw [he, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
      congr 1
      congr 1
      ring
    calc
      _ = A k * (τ : ℝ) ^ (-gain) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) := by
        dsimp only [A]
        have := hscale
        linear_combination (d : ℝ) * B k * C₀ * (τ : ℝ) ^ (-gain) * this
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [Cder]; linarith only [hC₀])
          (by positivity)) (by positivity)

end EinsteinFull.Blueprint
