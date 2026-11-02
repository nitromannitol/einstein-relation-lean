import EinsteinFull.Blueprint.G4.node_e_u3A_numerator_u2D_clock
import EinsteinFull.Blueprint.G4.node_p_u3A_integration_u23_actual_u2D_kernel_u2D_application
import EinsteinFull.Blueprint.G4.node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removal
import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import EinsteinFull.Blueprint.G4.node_clock_u2D_zero_u2D_coefficient
import EinsteinRelation.Mobility.DriftWeakDivergence
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinFull.Frozen.ReducedLawProbability

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma euclidean_bound {d : ℕ} {v : Vec d} {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) : euclideanNorm v ≤ ((d : ℝ) + 1) * B := by
  apply (euclideanNorm_le_dimension_mul_norm v).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (pi_norm_le_iff_of_nonneg hB).mpr fun i => by
    simpa only [Real.norm_eq_abs] using hv i

private lemma numerator_polynomial (d : ℕ) (b lam : ℝ) (k : Fin (d + 1) → ℝ) :
    (∑ n : Fin (d + 1), lam ^ (n.val + 1) *
      (if n.val = 0 then b - 2 * k ⟨0, by omega⟩ else -2 * k n)) =
      lam * b - 2 * lam * ∑ n : Fin (d + 1), k n * lam ^ n.val := by
  have hz : (0 : Fin (d + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fin.val_succ, zero_add, pow_one, pow_zero, mul_one,
    ↓reduceIte, Nat.add_one_ne_zero, hz]
  have hs : (∑ n : Fin d, lam ^ (n.val + 1 + 1) * (-2 * k n.succ)) =
      -2 * lam * ∑ n : Fin d, k n.succ * lam ^ (n.val + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [pow_succ]
    ring
  rw [hs]
  ring

private lemma clock_polynomial (d : ℕ) (lam : ℝ) (k : Fin (d + 1) → ℝ)
    (hk : k ⟨0, by omega⟩ = 0) :
    (∑ j : Fin d, (-2 * k ⟨j.val + 1, by omega⟩) * lam ^ (j.val + 1)) =
      -2 * ∑ n : Fin (d + 1), k n * lam ^ n.val := by
  have hz : (0 : Fin (d + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  rw [Fin.sum_univ_succ, hz, hk, zero_mul, zero_add, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  exact mul_assoc _ _ _

/-- Assemble the prescribed ordinary coefficients and the signed-force response
remainders from the actual integrated correlations. -/
theorem node_e_u3A_numerator_u2D_clock_of_deps
    (hkernel : node_p_u3A_integration_u23_actual_u2D_kernel_u2D_applicationStmt)
    (habel : node_finite_u2D_time_u2D_analyticity_u23_abel_u2D_removalStmt)
    (hresponse : node_p_u3A_responseStmt)
    (hclock : node_clock_u2D_zero_u2D_coefficientStmt) :
    node_e_u3A_numerator_u2D_clockStmt := by
  classical
  intro d hd D
  obtain ⟨B, ls, hB, hls, hlse, hkernels⟩ := hkernel d hd D
  obtain ⟨la, hla, hab⟩ := habel d hd D
  obtain ⟨Λ, _hΛ, hcl⟩ := hclock d hd D
  obtain ⟨M, hM, hentries⟩ := DriftH5.exists_ae_abs_entry_le d D.ellipticity D.dependenceRange
  let C := ((d : ℝ) + 2) * (M + 4 * B + 1)
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hC : 0 < C := by dsimp [C]; positivity
  have hcoef : ((d : ℝ) + 1) * (M + 2 * B) ≤ C := by
    dsimp [C]
    nlinarith only [hM, hB, hd0, mul_nonneg hd0 hM, mul_nonneg hd0 hB.le]
  have hcrit : ((d : ℝ) + 1) * B + B ≤ C := by
    dsimp [C]
    nlinarith only [hM, hB, hd0, mul_nonneg hd0 hM, mul_nonneg hd0 hB.le]
  have herrC : ((d : ℝ) + 1) * (2 * B) ≤ C := by
    dsimp [C]
    nlinarith only [hM, hB, hd0, mul_nonneg hd0 hM, mul_nonneg hd0 hB.le]
  have h2B : 2 * B ≤ C := by nlinarith only [herrC, mul_nonneg hd0 hB.le]
  refine ⟨C, min ls la, hC, lt_min hls hla, (min_le_left _ _).trans hlse, ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  letI := reducedLaw_probability Q
  obtain ⟨hγ, hK, hR, hI, hk, hχ, he⟩ :=
    hkernels Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  obtain ⟨_hjzero, _hprofzero, _hintzero, hkzero, _hrate⟩ :=
    hcl Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  dsimp only
  let first : Fin d := ⟨0, by omega⟩
  let A := homogenizedCoefficient Q
  let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
  let γ : ℝ := A first first / 2
  let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => 0
    | some i => p₀ / 4 * ∑ j, ∑ l,
        (A⁻¹) j l * covariance (.inl (j, first)) (.inl (l, i))
  let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
    | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
    | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
  let K : Option (Fin d) → ℝ → ℂ → ℂ := fun κ t z => match κ with
    | none => clockCorrelation Q first z (P z) β μ t.toNNReal
    | some i => velocityCorrelation Q first i z (P z) β a t.toNNReal
  refine ⟨hγ, hK, hR, hI, ?_⟩
  let k : Option (Fin d) → Fin (d + 1) → ℝ := fun κ =>
    integratedKernelCoefficient d (u₀ κ) (u₂ κ) γ hγ (K κ) (hK κ) (hR κ) (hI κ)
  let χ : Option (Fin d) → ℝ := fun κ =>
    integratedKernelCriticalCoefficient d (u₀ κ) (u₂ κ) γ hγ
  let b : Fin d → ℝ := fun i => ∫ ω, ω.1 0 first i ∂reducedLaw Q
  let m : ℝ := ∫ ω, ω.2 0 ∂reducedLaw Q
  let ac : Fin (d + 1) → Vec d := fun n i =>
    if n.val = 0 then b i - 2 * k (some i) ⟨0, by omega⟩ else -2 * k (some i) n
  let ec : Fin d → ℝ := fun j => -2 * k none ⟨j.val + 1, by omega⟩
  change k none ⟨0, by omega⟩ = 0 ∧
    (∀ n, euclideanNorm (ac n) ≤ C) ∧ (∀ j, |ec j| ≤ C) ∧
    euclideanNorm (fun i => χ (some i)) + |χ none| ≤ C ∧ _
  have hk0 : k none ⟨0, by omega⟩ = 0 := by
    simpa only [k, integratedKernelCoefficient, integratedRemainderCoefficient,
      Fin.val_zero, iteratedDeriv_zero, Nat.factorial_zero, Nat.cast_one, div_one,
      if_pos (show 0 < d by omega), Nat.sub_zero] using! hkzero
  have hb (i : Fin d) : |b i| ≤ M := by
    change ‖∫ ω, ω.1 0 first i ∂reducedLaw Q‖ ≤ M
    apply (norm_integral_le_of_norm_le_const ?_).trans_eq
      (show (M * (reducedLaw Q).real Set.univ) = M by simp)
    filter_upwards [hentries Q] with ω hω
    simpa only [Real.norm_eq_abs] using hω first i
  refine ⟨hk0, ?_, ?_, ?_, ?_⟩
  · intro n
    apply (euclidean_bound (by positivity : 0 ≤ M + 2 * B) ?_).trans hcoef
    intro i
    dsimp only [ac]
    split_ifs
    · exact (abs_sub _ _).trans (by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact add_le_add (hb i) (mul_le_mul_of_nonneg_left (hk (some i) _) (by norm_num)))
    · rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (mul_le_mul_of_nonneg_left (hk (some i) n) (by norm_num)).trans
        (le_add_of_nonneg_left hM)
  · intro j
    exact (show |ec j| ≤ 2 * B by
      dsimp only [ec]
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact mul_le_mul_of_nonneg_left (hk none _) (by norm_num)).trans h2B
  · exact (add_le_add (euclidean_bound hB.le (fun i => hχ (some i))) (hχ none)).trans hcrit
  · intro lam h₀ h₁ hsmall Y hY ell η hell hη
    have hlam : lam ≠ 0 := abs_pos.mp h₀
    obtain ⟨kv, jc, hkv, hjc, hv, hj, _hb⟩ :=
      (hresponse d hd D Q hQ β a μ hβ ha hμ lam (P (lam : ℂ)) (hP _)).2
        hlam Y hY ell hell η hη
    obtain ⟨hav, haj, halj⟩ := hab Q hQ β a μ hβ ha hμ P hP lam hlam
      (h₁.trans (min_le_right _ _))
    have hvint (i : Fin d) : kv i = ∫ t in Set.Ici (0 : ℝ), (K (some i) t (lam : ℂ)).re := by
      have hlim := tendsto_nhds_unique (hkv i) (hav i).2
      have hr := congrArg Complex.re hlim
      calc
        kv i = (∫ t in Set.Ioi (0 : ℝ), K (some i) t (lam : ℂ)).re := hr
        _ = ∫ t in Set.Ioi (0 : ℝ), (K (some i) t (lam : ℂ)).re := (integral_re (hav i).1).symm
        _ = _ := integral_Ici_eq_integral_Ioi.symm
    have hjint : jc = ∫ t in Set.Ici (0 : ℝ), (K none t (lam : ℂ)).re := by
      have hlim := tendsto_nhds_unique hjc halj
      have hr := congrArg Complex.re hlim
      calc
        jc = (∫ t in Set.Ioi (0 : ℝ), K none t (lam : ℂ)).re := hr
        _ = ∫ t in Set.Ioi (0 : ℝ), (K none t (lam : ℂ)).re := (integral_re haj).symm
        _ = _ := integral_Ici_eq_integral_Ioi.symm
    have hva (i : Fin d) : ell i = lam * b i -
        2 * lam * (∫ t in Set.Ici (0 : ℝ), (K (some i) t (lam : ℂ)).re) := by
      rw [hv i, hvint i]
      congr 2
      apply integral_congr_ae
      filter_upwards [ha first i] with ω hω
      rw [hω, Complex.ofReal_re]
    have hηeq : η = m - 2 * (∫ t in Set.Ici (0 : ℝ), (K none t (lam : ℂ)).re) := by
      rw [hj, hjint]
      congr 1
      apply integral_congr_ae
      filter_upwards [hμ] with ω hω
      rw [hω, Complex.ofReal_re]
    let T := criticalKernelTerm d lam (abs_pos.mp h₀)
    let E := |lam| ^ d * expansionModulus |lam| h₀ hsmall
    have hE : 0 ≤ E := mul_nonneg (pow_nonneg (abs_nonneg lam) _) (Real.exp_nonneg _)
    have he' (κ : Option (Fin d)) :
        |(∫ t in Set.Ici (0 : ℝ), (K κ t (lam : ℂ)).re) -
          (∑ n : Fin (d + 1), k κ n * lam ^ n.val) - χ κ * T| ≤ B * E := by
      simpa only [E, mul_assoc] using! (he κ lam h₀ (h₁.trans (min_le_left _ _)) hsmall).2
    constructor
    · have hc (i : Fin d) :
          |(ell - (∑ n : Fin (d + 1), lam ^ (n.val + 1) • ac n) +
              (2 * lam * T) • (fun i => χ (some i))) i| ≤ 2 * |lam| * (B * E) := by
        have hp := numerator_polynomial d (b i) lam (k (some i))
        have hp' : (∑ n : Fin (d + 1), lam ^ (n.val + 1) • ac n) i =
            lam * b i - 2 * lam * ∑ n : Fin (d + 1), k (some i) n * lam ^ n.val := by
          simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ac] using hp
        change |ell i - _ + (2 * lam * T) * χ (some i)| ≤ _
        rw [hp', hva i]
        have halg (v p c : ℝ) :
            lam * b i - 2 * lam * v - (lam * b i - 2 * lam * p) +
              (2 * lam * T) * c = (-2 * lam) * (v - p - c * T) := by ring
        rw [halg, abs_mul, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        exact mul_le_mul_of_nonneg_left (he' (some i)) (by positivity)
      apply (euclidean_bound (by positivity) hc).trans
      calc
        ((d : ℝ) + 1) * (2 * |lam| * (B * E)) =
            (((d : ℝ) + 1) * (2 * B)) * (|lam| * E) := by ring
        _ ≤ C * (|lam| * E) := mul_le_mul_of_nonneg_right herrC (mul_nonneg (abs_nonneg _) hE)
        _ = C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall := by
          dsimp only [E]
          rw [pow_succ]
          ring
    · change |η - m - (∑ j : Fin d, ec j * lam ^ (j.val + 1)) + 2 * χ none * T| ≤ _
      rw [clock_polynomial d lam (k none) hk0, hηeq]
      have halg (v p c : ℝ) : m - 2 * v - m - (-2 * p) + 2 * c * T =
          -2 * (v - p - c * T) := by ring
      rw [halg, abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      exact (mul_le_mul_of_nonneg_left (he' none) (by norm_num)).trans
        (by simpa only [E, mul_assoc] using mul_le_mul_of_nonneg_right h2B hE)

end EinsteinFull.Blueprint
