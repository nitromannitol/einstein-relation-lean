import EinsteinRelation.Entropy.EntropyStep
import EinsteinRelation.Correctors.ScalarDecompositionGlue

/-! # Lemma 4.1 from the entropy steps

Source: `paper/main.tex` 518-624, in the discrete form of
the resolvent route to Lemma 4.1: the weighted entropy steps telescope, and the
Fisher information of `ρ_s = ∑ w_m ρ_m` is at most the weighted sum of those of the `ρ_m`, by the
convexity of `(v, r) ↦ v·av/r`.
-/

open MeasureTheory Filter Set
open scoped ENNReal Topology NNReal

noncomputable section

open EinsteinRelation.External.GantertSection7Support

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## Telescoping -/

/-- **Weighted telescoping**: if `I₀ ≤ -μ H₀ + C` and `I_{m+1} ≤ μ (H_m - H_{m+1}) + C`, with
`H ≥ 0` and nonincreasing weights `w ≥ 0`, then `∑_{m≤N} w_m I_m ≤ C ∑_{m≤N} w_m - μ w_N H_N`. -/
theorem weighted_telescope {w H I : ℕ → ℝ} {μ C : ℝ} (hμ : 0 ≤ μ) (hwmono : ∀ m, w (m + 1) ≤ w m)
    (hw0 : ∀ m, 0 ≤ w m) (hH : ∀ m, 0 ≤ H m) (h0 : I 0 ≤ μ * (0 - H 0) + C)
    (hstep : ∀ m, I (m + 1) ≤ μ * (H m - H (m + 1)) + C) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), w m * I m ≤
      C * ∑ m ∈ Finset.range (N + 1), w m - μ * w N * H N := by
  induction N with
  | zero =>
    rw [zero_add, Finset.sum_range_one, Finset.sum_range_one]
    have h := mul_le_mul_of_nonneg_left h0 (hw0 0)
    have e : w 0 * (μ * (0 - H 0) + C) = C * w 0 - μ * w 0 * H 0 := by ring
    linarith
  | succ N ih =>
    rw [Finset.sum_range_succ (fun m => w m * I m) (N + 1), Finset.sum_range_succ w (N + 1)]
    have h1 := mul_le_mul_of_nonneg_left (hstep N) (hw0 (N + 1))
    have h2 : 0 ≤ μ * H N * (w N - w (N + 1)) :=
      mul_nonneg (mul_nonneg hμ (hH N)) (sub_nonneg.mpr (hwmono N))
    have e1 : w (N + 1) * (μ * (H N - H (N + 1)) + C) =
        μ * w (N + 1) * H N - μ * w (N + 1) * H (N + 1) + C * w (N + 1) := by ring
    have e2 : μ * H N * (w N - w (N + 1)) = μ * w N * H N - μ * w (N + 1) * H N := by ring
    have e3 : C * (∑ m ∈ Finset.range (N + 1), w m + w (N + 1)) =
        C * ∑ m ∈ Finset.range (N + 1), w m + C * w (N + 1) := by ring
    rw [e3]
    linarith

/-! ## The perspective inequality -/

/-- The bilinear form `B(y, z) = ∑_k y_k ∑_j a_{jk} z_j` of `qform`. -/
def bform2 (w : FieldPair d) (y z : Vec d) : ℝ := ∑ k, y k * ∑ j, w.1 0 j k * z j

theorem qform_add (w : FieldPair d) (y z : Vec d) :
    qform w (y + z) = qform w y + qform w z + bform2 w y z + bform2 w z y := by
  simp only [qform, bform2, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem qform_sub_smul (w : FieldPair d) (a b : ℝ) (y z : Vec d) :
    qform w (b • y - a • z) =
      b ^ 2 * qform w y + a ^ 2 * qform w z - a * b * (bform2 w y z + bform2 w z y) := by
  simp only [qform, bform2, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact Finset.sum_congr rfl fun j _ => by ring

theorem qform_smul (w : FieldPair d) (c : ℝ) (y : Vec d) :
    qform w (c • y) = c ^ 2 * qform w y := by
  simp only [qform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

/-- The two-term perspective inequality: `q(y+z)/(a+b) ≤ q(y)/a + q(z)/b`. -/
theorem qform_add_div_le {w : FieldPair d} (hq : ∀ v, 0 ≤ qform w v) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (y z : Vec d) :
    qform w (y + z) / (a + b) ≤ qform w y / a + qform w z / b := by
  have h := hq (b • y - a • z)
  rw [qform_sub_smul] at h
  rw [qform_add, div_add_div _ _ ha.ne' hb.ne', div_le_div_iff₀ (by linarith) (by positivity)]
  nlinarith [hq y, hq z, mul_pos ha hb]

/-- **The finite perspective inequality**: `q(∑ y_m)/(∑ a_m) ≤ ∑ q(y_m)/a_m`. -/
theorem qform_sum_div_le {w : FieldPair d} (hq : ∀ v, 0 ≤ qform w v) {a : ℕ → ℝ}
    (ha : ∀ m, 0 < a m) (y : ℕ → Vec d) (N : ℕ) :
    qform w (∑ m ∈ Finset.range (N + 1), y m) / (∑ m ∈ Finset.range (N + 1), a m) ≤
      ∑ m ∈ Finset.range (N + 1), qform w (y m) / a m := by
  induction N with
  | zero =>
    rw [zero_add, Finset.sum_range_one, Finset.sum_range_one, Finset.sum_range_one]
  | succ N ih =>
    rw [Finset.sum_range_succ y (N + 1), Finset.sum_range_succ a (N + 1),
      Finset.sum_range_succ (fun m => qform w (y m) / a m) (N + 1)]
    have hpos : 0 < ∑ m ∈ Finset.range (N + 1), a m :=
      Finset.sum_pos (fun m _ => ha m) Finset.nonempty_range_add_one
    have h1 := qform_add_div_le hq hpos (ha (N + 1)) (∑ m ∈ Finset.range (N + 1), y m) (y (N + 1))
    exact h1.trans (add_le_add ih le_rfl)

/-! ## The Gamma family in `H¹` -/

theorem measurable_gammaPrev {ρ : ℕ → FieldPair d → ℝ} (hρ : ∀ m, Measurable (ρ m)) (m : ℕ) :
    Measurable (gammaPrev ρ m) := by
  cases m with
  | zero => exact measurable_const
  | succ m => exact hρ m

theorem memLp_gammaPrev {Q : Measure (FieldPair d)} [IsFiniteMeasure Q] {ρ : ℕ → FieldPair d → ℝ}
    (hρ : ∀ m, MemLp (ρ m) 2 Q) (m : ℕ) : MemLp (gammaPrev ρ m) 2 Q := by
  cases m with
  | zero => exact memLp_const 1
  | succ m => exact hρ m

theorem integral_gammaDensity (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) {μ : ℝ}
    (hμ : 0 < μ) (m : ℕ) {rho : FieldPair d → ℝ} (hrho : IsGammaDensity Q P op μ m rho) :
    ∫ w, rho w ∂(Measure.map reduce Q) = 1 := by
  have h := integral_mul_gammaDensity Q P op hμ m hrho (fun _ => 1) measurable_const
    (B := 1) (fun _ => by simp)
  simp only [mul_one] at h
  rw [h]
  haveI := Density.isProbabilityMeasure_annealedCoordinateJoint Q P op
  have e : ∀ t, Density.observationMean Q P op (fun _ => (1 : ℝ)) t = 1 := fun t => by
    simp [Density.observationMean]
  simp only [e, mul_one]
  exact integral_gk hμ m

/-- **The Gamma family in `H¹`**: the densities `ρ_m` with their weak gradients `V_m` and the
`H¹` weak form of the recursion. -/
theorem exists_gamma_H1 (hFOT : FukushimaDecompositionInput) (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (hQ : IsStationary (Carriers.reducedReferenceLaw Q))
    {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (P' : DiffusionFamily d) (hP' : IsGMPReducedFamily hd Q.ellipticity_parameter Q P')
    (hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω))
    {μ : ℝ} (hμ : (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 < μ) :
    ∃ (ρ : ℕ → FieldPair d → ℝ) (V : ℕ → FieldPair d → Vec d),
      (∀ m, IsGammaDensity Q.measure P op μ m (ρ m)) ∧
      (∀ m, MemLp (ρ m) 2 (Carriers.reducedReferenceLaw Q)) ∧
      (∀ m, Measurable (V m)) ∧
      (∀ m j, MemLp (fun w => V m w j) 2 (Carriers.reducedReferenceLaw Q)) ∧
      (∀ m, HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ (ρ m) (V m)) ∧
      ∀ m (u : FieldPair d → ℝ) (G : FieldPair d → Vec d), Measurable u →
        MemLp u 2 (Carriers.reducedReferenceLaw Q) → Measurable G →
        (∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q)) →
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G →
        μ * (∫ w, ρ m w * u w ∂(Carriers.reducedReferenceLaw Q)) +
            (1 / 2 : ℝ) * ∑ k, (∫ w, V m w k * ∑ j, w.1 0 j k * G w j
              ∂(Carriers.reducedReferenceLaw Q)) -
            lam * (∫ w, ρ m w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
              ∂(Carriers.reducedReferenceLaw Q)) =
          ∫ w, (μ * gammaPrev ρ m w) * u w ∂(Carriers.reducedReferenceLaw Q) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  have hc0 : 0 ≤ (1 / 2) * sourceReducedBound Λ₀ * lam ^ 2 := by
    have := (sourceReducedBound_pos' Λ₀).le
    positivity
  have hμ0 : 0 < μ := hc0.trans_lt hμ
  choose ρ hρ using fun m => exists_gammaDensity hd Q h0 h1 P op hP hμ0 m
  have hρ2 : ∀ m, MemLp (ρ m) 2 (Carriers.reducedReferenceLaw Q) := fun m =>
    (memLp_gammaDensity hGir hInv hd Q h0 h1 P hP op P' hP' hP'0 hμ m (hρ m)).1
  obtain ⟨K, L, hgood⟩ := ae_good Q
  have hH := fun m => resolvent_density_H1 hd lam Q hQ (μ0 := μ) (ρ := ρ m)
    (f := fun w => μ * gammaPrev ρ m w) (hρ m).1 (hρ2 m)
    (measurable_const.mul (measurable_gammaPrev (fun k => (hρ k).1) m))
    ((memLp_gammaPrev hρ2 m).const_mul μ)
    (fun G hG => gamma_resolvent_equation hFOT hd Q h0 h1 P op hP hμ0 hρ m hG) hgood
  choose V hVm hV2 hρV hweak using hH
  exact ⟨ρ, V, hρ, hρ2, hVm, hV2, hρV, hweak⟩

/-! ## The summed entropy bound -/

theorem sum_range_gweight_le_one {s μ : ℝ} (hs : 0 < s) (hsμ : s ≤ μ) (N : ℕ) :
    ∑ m ∈ Finset.range N, gweight s μ m ≤ 1 := by
  have hμ : 0 < μ := hs.trans_le hsμ
  have hr0 : 0 ≤ 1 - s / μ := by
    have : s / μ ≤ 1 := (div_le_one hμ).mpr hsμ
    linarith
  have hr1 : 1 - s / μ < 1 := by
    have : 0 < s / μ := div_pos hs hμ
    linarith
  have hsum : HasSum (fun m => gweight s μ m) 1 := by
    have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (s / μ)
    have e : s / μ * (1 - (1 - s / μ))⁻¹ = 1 := by
      rw [sub_sub_cancel, mul_inv_cancel₀ (div_pos hs hμ).ne']
    rw [e] at h
    exact h
  rw [← hsum.tsum_eq]
  exact Summable.sum_le_tsum (Finset.range N) (fun m _ => gweight_nonneg hs.le hsμ hμ m)
    hsum.summable

theorem gweight_antitone {s μ : ℝ} (hs : 0 < s) (hsμ : s ≤ μ) (m : ℕ) :
    gweight s μ (m + 1) ≤ gweight s μ m := by
  have hμ : 0 < μ := hs.trans_le hsμ
  have hr0 : 0 ≤ 1 - s / μ := by
    have : s / μ ≤ 1 := (div_le_one hμ).mpr hsμ
    linarith
  have hr1 : 1 - s / μ ≤ 1 := by
    have : 0 < s / μ := div_pos hs hμ
    linarith
  unfold gweight
  rw [pow_succ, ← mul_assoc]
  exact mul_le_of_le_one_right (mul_nonneg (div_nonneg hs.le hμ.le) (pow_nonneg hr0 m)) hr1

/-- **The summed entropy bound**: `∑_{m≤N} w_m E[k_ε(ρ_m) V_m·aV_m] ≤ 4 Λ λ²`. -/
theorem gamma_entropy_sum (hd : 2 ≤ d) (lam : ℝ) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)) {s μ : ℝ} (hs : 0 < s)
    (hsμ : s ≤ μ) {ρ : ℕ → FieldPair d → ℝ} {V : ℕ → FieldPair d → Vec d}
    (hρ : ∀ m, IsGammaDensity Q.measure P op μ m (ρ m))
    (hρ2 : ∀ m, MemLp (ρ m) 2 (Carriers.reducedReferenceLaw Q)) (hVm : ∀ m, Measurable (V m))
    (hV2 : ∀ m j, MemLp (fun w => V m w j) 2 (Carriers.reducedReferenceLaw Q))
    (hρV : ∀ m, HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ (ρ m) (V m))
    (hweak : ∀ m (u : FieldPair d → ℝ) (G : FieldPair d → Vec d), Measurable u →
        MemLp u 2 (Carriers.reducedReferenceLaw Q) → Measurable G →
        (∀ j, MemLp (fun w => G w j) 2 (Carriers.reducedReferenceLaw Q)) →
        HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ u G →
        μ * (∫ w, ρ m w * u w ∂(Carriers.reducedReferenceLaw Q)) +
            (1 / 2 : ℝ) * ∑ k, (∫ w, V m w k * ∑ j, w.1 0 j k * G w j
              ∂(Carriers.reducedReferenceLaw Q)) -
            lam * (∫ w, ρ m w * ∑ j, w.1 0 j (firstCoordinateIndex hd) * G w j
              ∂(Carriers.reducedReferenceLaw Q)) =
          ∫ w, (μ * gammaPrev ρ m w) * u w ∂(Carriers.reducedReferenceLaw Q))
    {K : ℝ} (hK : ∀ᵐ w ∂(Carriers.reducedReferenceLaw Q), ∀ x j k, |w.1 x j k| ≤ K)
    {ε : ℝ} (hε : 0 < ε) (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1), gweight s μ m *
        ∫ w, rlogDeriv ε (ρ m w) * qform w (V m w) ∂(Carriers.reducedReferenceLaw Q) ≤
      4 * sourceReducedBound Λ₀ * lam ^ 2 := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  have hμ : 0 < μ := hs.trans_le hsμ
  have href : Carriers.reducedReferenceLaw Q = Measure.map reduce Q.measure := rfl
  have hint1 : ∀ m, ∫ w, ρ m w ∂(Carriers.reducedReferenceLaw Q) = 1 := fun m => by
    rw [href]
    exact integral_gammaDensity Q.measure P op hμ m (hρ m)
  set C := sourceReducedBound Λ₀ * lam ^ 2 with hCdef
  have hC : 0 ≤ C := by
    have := (sourceReducedBound_pos' Λ₀).le
    positivity
  set H : ℕ → ℝ := fun m => ∫ w, rent ε (ρ m w) ∂(Carriers.reducedReferenceLaw Q) with hHdef
  set I : ℕ → ℝ := fun m => (1 / 4 : ℝ) *
    ∫ w, rlogDeriv ε (ρ m w) * qform w (V m w) ∂(Carriers.reducedReferenceLaw Q) with hIdef
  have hstep' : ∀ m, I m ≤ μ * ((∫ w, rent ε (gammaPrev ρ m w) ∂(Carriers.reducedReferenceLaw Q))
      - H m) + C := fun m => by
    have h := entropy_step hd lam Q hQ hμ.le (hρ m).1 (hρ2 m) (hρ m).2.1
      (measurable_gammaPrev (fun k => (hρ k).1) m) (memLp_gammaPrev hρ2 m) hK (hVm m)
      (hV2 m) (hρV m) (hweak m) hε
    rw [hint1 m, mul_one] at h
    exact h
  have h0 : I 0 ≤ μ * (0 - H 0) + C := by
    have h := hstep' 0
    simp only [gammaPrev, rent_one, integral_zero] at h
    exact h
  have hstep : ∀ m, I (m + 1) ≤ μ * (H m - H (m + 1)) + C := fun m => hstep' (m + 1)
  have hH : ∀ m, 0 ≤ H m := fun m => integral_nonneg fun w => rent_nonneg hε _
  have ht := weighted_telescope hμ.le (gweight_antitone hs hsμ)
    (gweight_nonneg hs.le hsμ hμ) hH h0 hstep N
  have hw1 := sum_range_gweight_le_one hs hsμ (N + 1)
  have hwN : 0 ≤ μ * gweight s μ N * H N :=
    mul_nonneg (mul_nonneg hμ.le (gweight_nonneg hs.le hsμ hμ N)) (hH N)
  have e : ∑ m ∈ Finset.range (N + 1), gweight s μ m *
      ∫ w, rlogDeriv ε (ρ m w) * qform w (V m w) ∂(Carriers.reducedReferenceLaw Q) =
      4 * ∑ m ∈ Finset.range (N + 1), gweight s μ m * I m := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [hIdef]
    ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hw1 hC]

/-! ## The series for `ρ_s` and its gradient -/

theorem abs_coord_le_of_qform {Λ q r : ℝ} (hΛ : 0 < Λ) {v : Vec d} (j : Fin d)
    (hq : Λ⁻¹ * euclideanSq v ≤ q) (hr : 0 ≤ r) :
    |v j| ≤ (1 / 2) * (Λ * (rlogDeriv 1 r * q) + (r + 1)) := by
  have hvj : v j ^ 2 ≤ euclideanSq v := by
    unfold euclideanSq dot
    rw [sq]
    exact Finset.single_le_sum (f := fun i => v i * v i) (fun i _ => mul_self_nonneg _)
      (Finset.mem_univ j)
  have hq' : euclideanSq v ≤ Λ * q := by
    have := mul_le_mul_of_nonneg_left hq hΛ.le
    rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at this
  rw [rlogDeriv_of_nonneg 1 hr]
  have hr1 : 0 < 1 + r := by linarith
  set A := Λ * ((1 + r)⁻¹ * q) with hAdef
  have hAB : A * (r + 1) = Λ * q := by
    rw [hAdef]
    field_simp
    ring
  have hq0 : 0 ≤ q := le_trans (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher v)) hq
  have hA : 0 ≤ A := by positivity
  have h2 : |v j| ^ 2 ≤ A * (r + 1) := by rw [sq_abs, hAB]; linarith
  nlinarith [sq_nonneg (A - (r + 1)), abs_nonneg (v j)]

/-- If `ofReal ρ = ∑ ofReal (w_m ρ_m)` with `ρ` real, then `∑ w_m ρ_m` has sum `ρ`. -/
theorem hasSum_of_ofReal_eq_tsum {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m) {r : ℝ} (hr : 0 ≤ r)
    (h : ENNReal.ofReal r = ∑' m, ENNReal.ofReal (a m)) : HasSum a r := by
  have hfin : ∑' m, ((a m).toNNReal : ℝ≥0∞) ≠ ⊤ := by
    have : ∑' m, ((a m).toNNReal : ℝ≥0∞) = ENNReal.ofReal r := h.symm
    rw [this]
    exact ENNReal.ofReal_ne_top
  have hs : Summable a := by
    have := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp hfin)
    exact this.congr fun m => Real.coe_toNNReal _ (ha m)
  have he := ENNReal.ofReal_tsum_of_nonneg ha hs
  rw [← he, ENNReal.ofReal_eq_ofReal_iff hr (tsum_nonneg ha)] at h
  rw [h]
  exact hs.hasSum

/-- A nonnegative series of measurable functions with finite integral sums a.e., and its finite
`ℝ≥0∞`-sum is measurable. -/
theorem summable_of_lintegral_tsum_ne_top {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    {a : ℕ → Ω → ℝ} (ham : ∀ m, Measurable (a m))
    (hfin : ∫⁻ x, ∑' m, ENNReal.ofReal (a m x) ∂ν ≠ ⊤) :
    ∀ᵐ x ∂ν, ∑' m, ENNReal.ofReal (a m x) < ⊤ :=
  ae_lt_top (Measurable.ennreal_tsum fun m => (ham m).ennreal_ofReal) hfin

theorem summable_of_tsum_ofReal_lt_top {a : ℕ → ℝ} (ha : ∀ m, 0 ≤ a m)
    (h : ∑' m, ENNReal.ofReal (a m) < ⊤) : Summable a := by
  have := NNReal.summable_coe.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mp h.ne)
  exact this.congr fun m => Real.coe_toNNReal _ (ha m)

/-- The weighted `L¹` bound on the gradients: `∑_{m<N} w_m E|V_{m,j}| ≤ ½ Λ C + 1`. -/
theorem sum_weighted_abs_le {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀) {w : ℕ → ℝ}
    (hw0 : ∀ m, 0 ≤ w m) (hw1 : ∀ N, ∑ m ∈ Finset.range N, w m ≤ 1) {ρ : ℕ → FieldPair d → ℝ}
    (hρ0 : ∀ m x, 0 ≤ ρ m x) (hρi : ∀ m, Integrable (ρ m) (Carriers.reducedReferenceLaw Q))
    (hρ1 : ∀ m, ∫ x, ρ m x ∂(Carriers.reducedReferenceLaw Q) = 1) {V : ℕ → FieldPair d → Vec d}
    (hVm : ∀ m, Measurable (V m)) (hρm : ∀ m, Measurable (ρ m))
    (hqi : ∀ m, Integrable (fun x => qform x (V m x)) (Carriers.reducedReferenceLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hJ : ∀ N, ∑ m ∈ Finset.range (N + 1), w m *
      ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x) ∂(Carriers.reducedReferenceLaw Q) ≤ C)
    (j : Fin d) (N : ℕ) :
    ∑ m ∈ Finset.range N, w m * ∫ x, |V m x j| ∂(Carriers.reducedReferenceLaw Q) ≤
      (1 / 2) * sourceReducedBound Λ₀ * C + 1 := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  set Λ := sourceReducedBound Λ₀ with hΛdef
  have hΛ : 0 < Λ := sourceReducedBound_pos' Λ₀
  have hk : ∀ m, Integrable (fun x => rlogDeriv 1 (ρ m x) * qform x (V m x))
      (Carriers.reducedReferenceLaw Q) := fun m =>
    (hqi m).bdd_mul ((continuous_rlogDeriv one_pos).measurable.comp (hρm m)).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (rlogDeriv_pos one_pos _)]
        simpa using rlogDeriv_le one_pos (ρ m x))
  have hm : ∀ m, ∫ x, |V m x j| ∂(Carriers.reducedReferenceLaw Q) ≤
      (1 / 2) * (Λ * ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x) ∂(Carriers.reducedReferenceLaw Q))
        + 1 := fun m => by
    have hint : Integrable (fun x => (1 / 2 : ℝ) * (Λ * (rlogDeriv 1 (ρ m x) * qform x (V m x)) +
        (ρ m x + 1))) (Carriers.reducedReferenceLaw Q) :=
      (((hk m).const_mul Λ).add ((hρi m).add (integrable_const 1))).const_mul _
    have hle := integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) hint
      ((ae_qform_bounds hd Q).mono fun x hx => abs_coord_le_of_qform hΛ j (hx (V m x)).1 (hρ0 m x))
    refine hle.trans (le_of_eq ?_)
    have i1 : Integrable (fun x => Λ * (rlogDeriv 1 (ρ m x) * qform x (V m x)))
        (Carriers.reducedReferenceLaw Q) := (hk m).const_mul Λ
    have i2 : Integrable (fun x => ρ m x + 1) (Carriers.reducedReferenceLaw Q) :=
      (hρi m).add (integrable_const 1)
    rw [integral_const_mul, integral_add i1 i2, integral_const_mul,
      integral_add (f := fun x => ρ m x) (g := fun _ => (1 : ℝ)) (hρi m) (integrable_const 1),
      hρ1 m, integral_const, probReal_univ, one_smul]
    ring
  have hJ' : ∀ N, ∑ m ∈ Finset.range N, w m *
      ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x) ∂(Carriers.reducedReferenceLaw Q) ≤ C := by
    intro N
    cases N with
    | zero => simpa using hC
    | succ N => exact hJ N
  calc ∑ m ∈ Finset.range N, w m * ∫ x, |V m x j| ∂(Carriers.reducedReferenceLaw Q)
      ≤ ∑ m ∈ Finset.range N, w m * ((1 / 2) * (Λ * ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x)
          ∂(Carriers.reducedReferenceLaw Q)) + 1) :=
        Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left (hm m) (hw0 m)
    _ = (1 / 2) * Λ * (∑ m ∈ Finset.range N, w m * ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x)
          ∂(Carriers.reducedReferenceLaw Q)) + ∑ m ∈ Finset.range N, w m := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ (1 / 2) * Λ * C + 1 := by
        have h1 := mul_le_mul_of_nonneg_left (hJ' N) (by positivity : (0 : ℝ) ≤ 1 / 2 * Λ)
        linarith [hw1 N]

/-- **The series gradient** `Dρ_s = ∑ w_m V_m`: a measurable field to which the series converges
almost everywhere, with integrable Euclidean norm. -/
theorem exists_series_gradient {Λ₀ r₀ : ℝ} (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw1 : ∀ N, ∑ m ∈ Finset.range N, w m ≤ 1)
    {ρ : ℕ → FieldPair d → ℝ} (hρ0 : ∀ m x, 0 ≤ ρ m x)
    (hρi : ∀ m, Integrable (ρ m) (Carriers.reducedReferenceLaw Q))
    (hρ1 : ∀ m, ∫ x, ρ m x ∂(Carriers.reducedReferenceLaw Q) = 1) {V : ℕ → FieldPair d → Vec d}
    (hVm : ∀ m, Measurable (V m)) (hρm : ∀ m, Measurable (ρ m))
    (hV1 : ∀ m j, Integrable (fun x => V m x j) (Carriers.reducedReferenceLaw Q))
    (hqi : ∀ m, Integrable (fun x => qform x (V m x)) (Carriers.reducedReferenceLaw Q)) {C : ℝ}
    (hC : 0 ≤ C) (hJ : ∀ N, ∑ m ∈ Finset.range (N + 1), w m *
      ∫ x, rlogDeriv 1 (ρ m x) * qform x (V m x) ∂(Carriers.reducedReferenceLaw Q) ≤ C) :
    ∃ Drho : FieldPair d → Vec d, Measurable Drho ∧
      (∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), ∀ j,
        HasSum (fun m => w m * V m x j) (Drho x j)) ∧
      Integrable (fun x => euclideanNorm (Drho x)) (Carriers.reducedReferenceLaw Q) ∧
      ∀ j, ∑' m, ENNReal.ofReal (w m * ∫ x, |V m x j| ∂(Carriers.reducedReferenceLaw Q)) ≤
        ENNReal.ofReal ((1 / 2) * sourceReducedBound Λ₀ * C + 1) := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  set ν := Carriers.reducedReferenceLaw Q with hνdef
  set B := (1 / 2) * sourceReducedBound Λ₀ * C + 1 with hBdef
  have hcm : ∀ m j, Measurable fun x => w m * |V m x j| := fun m j =>
    measurable_const.mul (continuous_abs.measurable.comp ((measurable_pi_apply j).comp (hVm m)))
  have hcn : ∀ m j x, 0 ≤ w m * |V m x j| := fun m j x => mul_nonneg (hw0 m) (abs_nonneg _)
  have htsum : ∀ j, ∑' m, ENNReal.ofReal (w m * ∫ x, |V m x j| ∂ν) ≤ ENNReal.ofReal B := by
    intro j
    refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg fun m _ =>
      mul_nonneg (hw0 m) (integral_nonneg fun x => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (sum_weighted_abs_le hd Q hw0 hw1 hρ0 hρi hρ1 hVm hρm hqi hC hJ j N)
  set A : Fin d → FieldPair d → ℝ≥0∞ := fun j x => ∑' m, ENNReal.ofReal (w m * |V m x j|)
    with hAdef
  have hAm : ∀ j, Measurable (A j) := fun j =>
    Measurable.ennreal_tsum fun m => (hcm m j).ennreal_ofReal
  have hAint : ∀ j, ∫⁻ x, A j x ∂ν ≤ ENNReal.ofReal B := by
    intro j
    rw [hAdef, lintegral_tsum fun m => (hcm m j).ennreal_ofReal.aemeasurable]
    refine le_trans (le_of_eq ?_) (htsum j)
    refine tsum_congr fun m => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal ((hV1 m j).abs.const_mul (w m))
      (ae_of_all _ (hcn m j)), integral_const_mul]
  have hAfin : ∀ j, ∫⁻ x, A j x ∂ν ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAint j)
  set S : Set (FieldPair d) := {x | ∀ j, A j x < ⊤} with hSdef
  have hS : MeasurableSet S := by
    rw [hSdef, Set.setOf_forall]
    exact MeasurableSet.iInter fun j => measurableSet_lt (hAm j) measurable_const
  have hSae : ∀ᵐ x ∂ν, x ∈ S := by
    rw [hSdef]
    exact ae_all_iff.mpr fun j => ae_lt_top (hAm j) (hAfin j)
  have hsumm : ∀ x ∈ S, ∀ j, Summable fun m => w m * V m x j := fun x hx j => by
    refine Summable.of_norm ?_
    refine (summable_of_tsum_ofReal_lt_top (fun m => hcn m j x) (hx j)).congr fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m)]
  set Drho : FieldPair d → Vec d := fun x j => S.indicator (fun x => ∑' m, w m * V m x j) x
    with hDdef
  have hDm : Measurable Drho := by
    refine measurable_pi_lambda _ fun j => ?_
    refine measurable_of_tendsto_metrizable (f := fun N x =>
      S.indicator (fun x => ∑ m ∈ Finset.range N, w m * V m x j) x) (fun N => ?_) ?_
    · exact (Finset.measurable_sum _ fun m _ =>
        measurable_const.mul ((measurable_pi_apply j).comp (hVm m))).indicator hS
    · refine tendsto_pi_nhds.mpr fun x => ?_
      by_cases hx : x ∈ S
      · simp only [hDdef, Set.indicator_of_mem hx]
        exact (hsumm x hx j).hasSum.tendsto_sum_nat
      · simp only [hDdef, Set.indicator_of_notMem hx]
        exact tendsto_const_nhds
  have hhas : ∀ᵐ x ∂ν, ∀ j, HasSum (fun m => w m * V m x j) (Drho x j) := by
    filter_upwards [hSae] with x hx j
    simp only [hDdef, Set.indicator_of_mem hx]
    exact (hsumm x hx j).hasSum
  refine ⟨Drho, hDm, hhas, ?_, htsum⟩
  have hTi : Integrable (fun x => ∑ j, (A j x).toReal) ν :=
    integrable_finset_sum _ fun j _ =>
      integrable_toReal_of_lintegral_ne_top (hAm j).aemeasurable (hAfin j)
  refine Integrable.mono' hTi (continuous_euclideanNorm'.measurable.comp hDm).aestronglyMeasurable
    ?_
  filter_upwards [hSae] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ euclideanNorm (Drho x) from Real.sqrt_nonneg _)]
  refine (euclideanNorm_le_sum_abs' _).trans (Finset.sum_le_sum fun j _ => ?_)
  simp only [hDdef, Set.indicator_of_mem hx]
  have hn : Summable fun m => ‖w m * V m x j‖ := by
    refine (summable_of_tsum_ofReal_lt_top (fun m => hcn m j x) (hx j)).congr fun m => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m)]
  calc |∑' m, w m * V m x j| = ‖∑' m, w m * V m x j‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' m, ‖w m * V m x j‖ := norm_tsum_le_tsum_norm hn
    _ = (A j x).toReal := by
        rw [hAdef, ENNReal.tsum_toReal_eq fun m => ENNReal.ofReal_ne_top]
        refine tsum_congr fun m => ?_
        rw [ENNReal.toReal_ofReal (hcn m j x), Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 m)]

/-! ## The weak gradient of `ρ_s` -/

/-- `hasWeakHorizontalGradient_of_tests` for integrable functions. -/
theorem hasWeakHorizontalGradient_of_tests_L1 {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} {V : FieldPair d → Vec d} (hum : Measurable u)
    (hu : Integrable u Q) (hVm : Measurable V) (hV : ∀ i, Integrable (fun w => V w i) Q)
    (hcore : ∀ i, ∀ K : FieldPair d → ℝ, IsHorizontalTest K →
      (∫ ω, u ω * horizontalDerivative i K ω ∂Q) = -(∫ ω, V ω i * K ω ∂Q)) :
    HasWeakHorizontalGradient Q hQ u V := by
  refine ⟨hu, hV, fun i F G hFs hG => ?_⟩
  have h := Calculus.integral_chain_smooth hQ (g := id) contDiff_id (L := 1)
    (fun x => by simp) hum hu ((measurable_pi_apply i).comp hVm) (hV i) i (hcore i) hFs hG
  simpa using h

/-- `∑' ofReal (w_m c_m) < ⊤` when `w` is summable and `0 ≤ c_m ≤ M`. -/
theorem tsum_ofReal_mul_ne_top {w c : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m) (hw : Summable w) {M : ℝ}
    (hc0 : ∀ m, 0 ≤ c m) (hcM : ∀ m, c m ≤ M) : ∑' m, ENNReal.ofReal (w m * c m) ≠ ⊤ := by
  have hM : 0 ≤ M := (hc0 0).trans (hcM 0)
  refine ne_top_of_le_ne_top (b := ∑' m, ENNReal.ofReal (w m * M)) ?_ (ENNReal.tsum_le_tsum
    fun m => ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hcM m) (hw0 m)))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hw0 m) hM) (hw.mul_right M)]
  exact ENNReal.ofReal_ne_top

/-- **The weak gradient of `ρ_s`**: `Dρ_s = ∑ w_m Dρ_m`. -/
theorem hasWeakHorizontalGradient_series {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {w : ℕ → ℝ} (hw0 : ∀ m, 0 ≤ w m)
    (hwsum : Summable w) {ρ : ℕ → FieldPair d → ℝ} (hρm : ∀ m, Measurable (ρ m))
    (hρ0 : ∀ m x, 0 ≤ ρ m x) (hρi : ∀ m, Integrable (ρ m) (Carriers.reducedReferenceLaw Q))
    (hρ1 : ∀ m, ∫ x, ρ m x ∂(Carriers.reducedReferenceLaw Q) = 1) {V : ℕ → FieldPair d → Vec d}
    (hVm : ∀ m, Measurable (V m))
    (hV1 : ∀ m j, Integrable (fun x => V m x j) (Carriers.reducedReferenceLaw Q))
    (hρV : ∀ m, HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ (ρ m) (V m))
    {rho : FieldPair d → ℝ} (hrhom : Measurable rho)
    (hrhoi : Integrable rho (Carriers.reducedReferenceLaw Q))
    (hrho : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), HasSum (fun m => w m * ρ m x) (rho x))
    {Drho : FieldPair d → Vec d} (hDm : Measurable Drho)
    (hD : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), ∀ j,
      HasSum (fun m => w m * V m x j) (Drho x j))
    (hDi : Integrable (fun x => euclideanNorm (Drho x)) (Carriers.reducedReferenceLaw Q)) {B : ℝ}
    (hB : ∀ j, ∑' m, ENNReal.ofReal (w m * ∫ x, |V m x j| ∂(Carriers.reducedReferenceLaw Q)) ≤
      ENNReal.ofReal B) :
    HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho := by
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  set ν := Carriers.reducedReferenceLaw Q with hνdef
  have hDi' : ∀ i, Integrable (fun x => Drho x i) ν := fun i =>
    hDi.mono' ((measurable_pi_apply i).comp hDm).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs]
        exact abs_apply_le_euclideanNorm _ i)
  refine hasWeakHorizontalGradient_of_tests_L1 hQ hrhom hrhoi hDm hDi' fun i K hK => ?_
  obtain ⟨M0, M1, -, -, -, hb0, hb1, -⟩ := hK.exists_bounds
  have hKB : ∀ x, |K x| ≤ M0 := fun x => by simpa using hb0 x 0
  have hDKB : ∀ x, |horizontalDerivative i K x| ≤ M1 := fun x => by simpa using hb1 x 0 i
  have hKm : Measurable K := hK.1
  have hDKm : Measurable (horizontalDerivative i K) := hK.measurable_derivative i
  -- The density side.
  have hL : ∫ x, rho x * horizontalDerivative i K x ∂ν =
      ∑' m, w m * ∫ x, ρ m x * horizontalDerivative i K x ∂ν := by
    have hae : (fun x => rho x * horizontalDerivative i K x) =ᵐ[ν]
        fun x => ∑' m, w m * ρ m x * horizontalDerivative i K x := by
      filter_upwards [hrho] with x hx
      exact ((hx.mul_right (horizontalDerivative i K x)).tsum_eq).symm
    rw [integral_congr_ae hae, integral_tsum (f := fun m x => w m * ρ m x * horizontalDerivative i K x)
      (fun m => ((measurable_const.mul (hρm m)).mul hDKm).aestronglyMeasurable)]
    · refine tsum_congr fun m => ?_
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    · have hle : ∀ m, ∫⁻ x, ‖w m * ρ m x * horizontalDerivative i K x‖ₑ ∂ν ≤
          ENNReal.ofReal (w m * M1) := fun m => by
        calc ∫⁻ x, ‖w m * ρ m x * horizontalDerivative i K x‖ₑ ∂ν
            ≤ ∫⁻ x, ENNReal.ofReal (w m * M1 * ρ m x) ∂ν := lintegral_mono fun x => by
              rw [Real.enorm_eq_ofReal_abs]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (hw0 m), abs_of_nonneg (hρ0 m x)]
              have := mul_le_mul_of_nonneg_left (hDKB x) (mul_nonneg (hw0 m) (hρ0 m x))
              linarith
          _ = ENNReal.ofReal (w m * M1) := by
              rw [← ofReal_integral_eq_lintegral_ofReal ((hρi m).const_mul _)
                (ae_of_all _ fun x => mul_nonneg (mul_nonneg (hw0 m) ((abs_nonneg _).trans
                  (hDKB 0))) (hρ0 m x)), integral_const_mul, hρ1 m, mul_one]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => mul_nonneg (hw0 m)
        ((abs_nonneg _).trans (hDKB 0))) (hwsum.mul_right M1)]
      exact ENNReal.ofReal_ne_top
  -- The gradient side.
  have hR : ∫ x, Drho x i * K x ∂ν = ∑' m, w m * ∫ x, V m x i * K x ∂ν := by
    have hae : (fun x => Drho x i * K x) =ᵐ[ν] fun x => ∑' m, w m * V m x i * K x := by
      filter_upwards [hD] with x hx
      exact (((hx i).mul_right (K x)).tsum_eq).symm
    rw [integral_congr_ae hae, integral_tsum (f := fun m x => w m * V m x i * K x) (fun m =>
      ((measurable_const.mul ((measurable_pi_apply i).comp (hVm m))).mul hKm).aestronglyMeasurable)]
    · refine tsum_congr fun m => ?_
      rw [← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun x => by ring)
    · have hM0 : 0 ≤ M0 := (abs_nonneg _).trans (hKB 0)
      have hle : ∀ m, ∫⁻ x, ‖w m * V m x i * K x‖ₑ ∂ν ≤
          ENNReal.ofReal M0 * ENNReal.ofReal (w m * ∫ x, |V m x i| ∂ν) := fun m => by
        calc ∫⁻ x, ‖w m * V m x i * K x‖ₑ ∂ν
            ≤ ∫⁻ x, ENNReal.ofReal (M0 * (w m * |V m x i|)) ∂ν := lintegral_mono fun x => by
              rw [Real.enorm_eq_ofReal_abs]
              refine ENNReal.ofReal_le_ofReal ?_
              rw [abs_mul, abs_mul, abs_of_nonneg (hw0 m)]
              have := mul_le_mul_of_nonneg_left (hKB x) (mul_nonneg (hw0 m) (abs_nonneg (V m x i)))
              linarith
          _ = ENNReal.ofReal M0 * ENNReal.ofReal (w m * ∫ x, |V m x i| ∂ν) := by
              rw [← ofReal_integral_eq_lintegral_ofReal (((hV1 m i).abs.const_mul _).const_mul _)
                (ae_of_all _ fun x => mul_nonneg hM0 (mul_nonneg (hw0 m) (abs_nonneg _))),
                integral_const_mul, integral_const_mul, ENNReal.ofReal_mul hM0]
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB i))
  rw [hL, hR, ← tsum_neg]
  refine tsum_congr fun m => ?_
  rw [HasWeakHorizontalGradient.integral_test' (hρV m) i hK]
  ring

/-! ## The Fisher bound for `ρ_s` -/

theorem continuous_qform (x : FieldPair d) : Continuous (qform x) := by
  unfold qform
  exact continuous_finset_sum _ fun k _ => (continuous_apply k).mul
    (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j))

theorem measurable_qform_comp {V : FieldPair d → Vec d} (hVm : Measurable V) :
    Measurable fun x => qform x (V x) := by
  unfold qform
  refine Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp hVm).mul
    (Finset.measurable_sum _ fun j _ => ?_)
  exact (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k).measurable.mul
    ((measurable_pi_apply j).comp hVm)

/-- **The regularized Fisher bound for `ρ_s`**: `E[Dρ_s·aDρ_s / (ρ_s + ε)] ≤ C`, from the
perspective inequality applied to the partial sums. -/
theorem lintegral_qform_div_le {ν : Measure (FieldPair d)}
    {w : ℕ → ℝ} (hw : ∀ m, 0 < w m) (hwsum : HasSum w 1) {ρ : ℕ → FieldPair d → ℝ}
    (hρm : ∀ m, Measurable (ρ m)) (hρ0 : ∀ m x, 0 ≤ ρ m x) {V : ℕ → FieldPair d → Vec d}
    (hVm : ∀ m, Measurable (V m)) (hqnn : ∀ᵐ x ∂ν, ∀ v, 0 ≤ qform x v) {ε : ℝ} (hε : 0 < ε)
    (hJi : ∀ m, Integrable (fun x => rlogDeriv ε (ρ m x) * qform x (V m x)) ν)
    {rho : FieldPair d → ℝ} (hrho0 : ∀ x, 0 ≤ rho x)
    (hrho : ∀ᵐ x ∂ν, HasSum (fun m => w m * ρ m x) (rho x)) {Drho : FieldPair d → Vec d}
    (hD : ∀ᵐ x ∂ν, ∀ j, HasSum (fun m => w m * V m x j) (Drho x j)) {C : ℝ}
    (hJ : ∀ N, ∑ m ∈ Finset.range (N + 1), w m *
      ∫ x, rlogDeriv ε (ρ m x) * qform x (V m x) ∂ν ≤ C) :
    ∫⁻ x, ENNReal.ofReal (qform x (Drho x) / (rho x + ε)) ∂ν ≤ ENNReal.ofReal C := by
  set F : ℕ → FieldPair d → ℝ≥0∞ := fun m x =>
    ENNReal.ofReal (w m * (rlogDeriv ε (ρ m x) * qform x (V m x))) with hFdef
  have hFm : ∀ m, Measurable (F m) := fun m =>
    (measurable_const.mul (((continuous_rlogDeriv hε).measurable.comp (hρm m)).mul
      (measurable_qform_comp (hVm m)))).ennreal_ofReal
  -- The pointwise bound.
  have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal (qform x (Drho x) / (rho x + ε)) ≤ ∑' m, F m x := by
    filter_upwards [hqnn, hrho, hD] with x hq hx hDx
    set y : ℕ → Vec d := fun m => w m • V m x with hydef
    set a : ℕ → ℝ := fun m => w m * (ρ m x + ε) with hadef
    have ha : ∀ m, 0 < a m := fun m => mul_pos (hw m) (by linarith [hρ0 m x])
    have hya : ∀ m, qform x (y m) / a m = w m * (rlogDeriv ε (ρ m x) * qform x (V m x)) :=
      fun m => by
        rw [hydef, hadef, qform_smul, rlogDeriv_of_nonneg ε (hρ0 m x), add_comm ε]
        have hw' := (hw m).ne'
        have hr : ρ m x + ε ≠ 0 := by linarith [hρ0 m x]
        field_simp
    have hN : ∀ N, ENNReal.ofReal (qform x (∑ m ∈ Finset.range (N + 1), y m) /
        ∑ m ∈ Finset.range (N + 1), a m) ≤ ∑' m, F m x := fun N => by
      refine (ENNReal.ofReal_le_ofReal (qform_sum_div_le hq ha y N)).trans ?_
      simp only [hya]
      rw [ENNReal.ofReal_sum_of_nonneg fun m _ => mul_nonneg (hw m).le
        (mul_nonneg (rlogDeriv_pos hε _).le (hq _))]
      exact ENNReal.sum_le_tsum _
    have hshift : Tendsto (fun N : ℕ => N + 1) atTop atTop := tendsto_add_atTop_nat 1
    have hP : Tendsto (fun N => ∑ m ∈ Finset.range (N + 1), y m) atTop (𝓝 (Drho x)) := by
      refine tendsto_pi_nhds.mpr fun j => ?_
      have h := ((hDx j).tendsto_sum_nat).comp hshift
      refine h.congr fun N => ?_
      simp only [Function.comp, hydef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have hA : Tendsto (fun N => ∑ m ∈ Finset.range (N + 1), a m) atTop (𝓝 (rho x + ε)) := by
      have h1 := (hx.tendsto_sum_nat).comp hshift
      have h2 := ((hwsum.tendsto_sum_nat).comp hshift).const_mul ε
      rw [mul_one] at h2
      refine (h1.add h2).congr fun N => ?_
      simp only [Function.comp, hadef, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    have hpos : rho x + ε ≠ 0 := by linarith [hrho0 x]
    have hlim := ENNReal.tendsto_ofReal (((continuous_qform x).tendsto _).comp hP |>.div hA hpos)
    exact le_of_tendsto' hlim hN
  -- Integrate.
  have hJ0 : ∀ m, 0 ≤ ∫ x, rlogDeriv ε (ρ m x) * qform x (V m x) ∂ν := fun m =>
    integral_nonneg_of_ae (hqnn.mono fun x hx => mul_nonneg (rlogDeriv_pos hε _).le (hx _))
  calc ∫⁻ x, ENNReal.ofReal (qform x (Drho x) / (rho x + ε)) ∂ν
      ≤ ∫⁻ x, ∑' m, F m x ∂ν := lintegral_mono_ae hpt
    _ = ∑' m, ∫⁻ x, F m x ∂ν := lintegral_tsum fun m => (hFm m).aemeasurable
    _ = ∑' m, ENNReal.ofReal (w m * ∫ x, rlogDeriv ε (ρ m x) * qform x (V m x) ∂ν) := by
        refine tsum_congr fun m => ?_
        rw [hFdef, ← ofReal_integral_eq_lintegral_ofReal ((hJi m).const_mul (w m))
          (hqnn.mono fun x hx => mul_nonneg (hw m).le (mul_nonneg (rlogDeriv_pos hε _).le (hx _))),
          integral_const_mul]
    _ ≤ ENNReal.ofReal C := by
        refine ENNReal.tsum_le_of_sum_range_le fun N => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun m _ => mul_nonneg (hw m).le (hJ0 m)]
        refine ENNReal.ofReal_le_ofReal ?_
        cases N with
        | zero =>
          simp only [Finset.range_zero, Finset.sum_empty]
          have h := hJ 0
          rw [zero_add, Finset.sum_range_one] at h
          exact (mul_nonneg (hw 0).le (hJ0 0)).trans h
        | succ N => exact hJ N

/-- **The Fisher bound for `ρ_s`**, letting `ε ↓ 0` by monotone convergence. -/
theorem fisher_lintegral_le {ν : Measure (FieldPair d)} {rho : FieldPair d → ℝ}
    (hrhom : Measurable rho) (hrho0 : ∀ x, 0 ≤ rho x) {Drho : FieldPair d → Vec d}
    (hDm : Measurable Drho) (hqnn : ∀ᵐ x ∂ν, ∀ v, 0 ≤ qform x v)
    (hsym : ∀ᵐ x ∂ν, (x.1 0).transpose = x.1 0) {C : ℝ}
    (hε : ∀ ε : ℝ, 0 < ε → ∫⁻ x, ENNReal.ofReal (qform x (Drho x) / (rho x + ε)) ∂ν ≤
      ENNReal.ofReal C) :
    ∫⁻ x, ENNReal.ofReal (if rho x = 0 then 0 else
      dot (Drho x) ((x.1 (0 : Vec d)).mulVec (Drho x)) / rho x) ∂ν ≤ ENNReal.ofReal C := by
  set f : ℕ → FieldPair d → ℝ≥0∞ := fun n x =>
    ENNReal.ofReal (qform x (Drho x) / (rho x + 1 / ((n : ℝ) + 1))) with hfdef
  have hfm : ∀ n, Measurable (f n) := fun n =>
    ((measurable_qform_comp hDm).div (hrhom.add measurable_const)).ennreal_ofReal
  have hmono : ∀ᵐ x ∂ν, Monotone fun n => f n x := by
    filter_upwards [hqnn] with x hx n k hnk
    refine ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (hx _) ?_ ?_)
    · have := hrho0 x
      positivity
    · have h1 : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnk
      have h2 : 1 / ((k : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) h1
      linarith
  have hsup : ∫⁻ x, ⨆ n, f n x ∂ν ≤ ENNReal.ofReal C := by
    rw [lintegral_iSup' (fun n => (hfm n).aemeasurable) hmono]
    exact iSup_le fun n => hε _ (by positivity)
  refine le_trans (lintegral_mono_ae ?_) hsup
  filter_upwards [hsym] with x hx
  by_cases h0 : rho x = 0
  · simp [h0]
  · rw [if_neg h0, dot_mulVec_eq_qform hx]
    have hT : Tendsto (fun n : ℕ => rho x + 1 / ((n : ℝ) + 1)) atTop (𝓝 (rho x)) := by
      have := tendsto_const_nhds (x := rho x) |>.add tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using this
    have hlim := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := qform x (Drho x))).div hT h0)
    exact le_of_tendsto' hlim fun n => le_iSup (fun n => f n x) n

/-! ## Lemma 4.1 -/

theorem hasSum_gweight {s μ : ℝ} (hs : 0 < s) (hsμ : s ≤ μ) : HasSum (gweight s μ) 1 := by
  have hμ : 0 < μ := hs.trans_le hsμ
  have hr0 : 0 ≤ 1 - s / μ := by
    have : s / μ ≤ 1 := (div_le_one hμ).mpr hsμ
    linarith
  have hr1 : 1 - s / μ < 1 := by
    have : 0 < s / μ := div_pos hs hμ
    linarith
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (s / μ)
  have e : s / μ * (1 - (1 - s / μ))⁻¹ = 1 := by
    rw [sub_sub_cancel, mul_inv_cancel₀ (div_pos hs hμ).ne']
  rw [e] at h
  exact h

theorem gweight_pos {s μ : ℝ} (hs : 0 < s) (hsμ : s < μ) (m : ℕ) : 0 < gweight s μ m := by
  have hμ : 0 < μ := hs.trans hsμ
  have : s / μ < 1 := (div_lt_one hμ).mpr hsμ
  unfold gweight
  exact mul_pos (div_pos hs hμ) (pow_pos (by linarith) m)

/-- **Lemma 4.1** (`paper/main.tex` 518-624): every reduced Laplace density has a weak horizontal
gradient, integrable in norm, with Fisher information at most `4 Λ λ²`. From the Fukushima
decomposition, the Girsanov endpoint bound, the unforced invariance and the existence of the reduced
family, through the discrete resolvent route. -/
theorem fisherBoundStatement_of_inputs (hFOT : FukushimaDecompositionInput)
    (hGir : GirsanovEndpointStep) (hInv : UnforcedEnvironmentInvarianceStep)
    (hRF : External.GMPReducedFamilyExistence) : Correctors.FisherBoundStatement := by
  intro d hd Λ₀ r₀ Q hQ lam hl0 hl1 P op hP s rho hrho
  haveI : IsProbabilityMeasure (Carriers.reducedReferenceLaw Q) :=
    reducedReferenceLaw_isProbabilityMeasure Q
  set Λ := sourceReducedBound Λ₀ with hΛdef
  have hΛ : 0 < Λ := sourceReducedBound_pos' Λ₀
  set c := (1 / 2) * Λ * lam ^ 2 with hcdef
  have hc0 : 0 ≤ c := by positivity
  set μ := s.1 + c + 1 with hμdef
  have hsμ : s.1 < μ := by linarith
  have hcμ : c < μ := by linarith [s.2]
  obtain ⟨P', hP'⟩ := hRF d hd Λ₀ r₀ Q
  have hP'0 : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P' 0) ω) := by
    filter_upwards [hP' 0 le_rfl zero_le_one] with ω hω
    obtain ⟨_, r0, hr0⟩ := hω
    haveI := r0.pathLaw_isMarkovKernel
    rw [originLaw_apply, hr0]
    infer_instance
  obtain ⟨ρ, V, hρ, hρ2, hVm, hV2, hρV, hweak⟩ :=
    exists_gamma_H1 hFOT hGir hInv hd Q hQ hl0.le hl1 P op hP P' hP' hP'0 hcμ
  set w := gweight s.1 μ with hwdef
  have hw : ∀ m, 0 < w m := gweight_pos s.2 hsμ
  have hw0 : ∀ m, 0 ≤ w m := fun m => (hw m).le
  have hwsum : HasSum w 1 := hasSum_gweight s.2 hsμ.le
  obtain ⟨K, L, hgood⟩ := ae_good Q
  have hK : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), ∀ y j k, |x.1 y j k| ≤ K :=
    hgood.mono fun x hx => hx.1
  set C := 4 * Λ * lam ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  have hJsum : ∀ ε : ℝ, 0 < ε → ∀ N, ∑ m ∈ Finset.range (N + 1), w m *
      ∫ x, rlogDeriv ε (ρ m x) * qform x (V m x) ∂(Carriers.reducedReferenceLaw Q) ≤ C :=
    fun ε hε N => gamma_entropy_sum hd lam Q hQ P op s.2 hsμ.le hρ hρ2 hVm hV2 hρV hweak hK hε N
  have href : Carriers.reducedReferenceLaw Q = Measure.map reduce Q.measure := rfl
  have hρm : ∀ m, Measurable (ρ m) := fun m => (hρ m).1
  have hρ0 : ∀ m x, 0 ≤ ρ m x := fun m => (hρ m).2.1
  have hρi : ∀ m, Integrable (ρ m) (Carriers.reducedReferenceLaw Q) := fun m =>
    (hρ2 m).integrable one_le_two
  have hρ1 : ∀ m, ∫ x, ρ m x ∂(Carriers.reducedReferenceLaw Q) = 1 := fun m => by
    rw [href]
    exact integral_gammaDensity Q.measure P op (hc0.trans_lt hcμ) m (hρ m)
  have hV1 : ∀ m j, Integrable (fun x => V m x j) (Carriers.reducedReferenceLaw Q) := fun m j =>
    (hV2 m j).integrable one_le_two
  have hqi : ∀ m, Integrable (fun x => qform x (V m x)) (Carriers.reducedReferenceLaw Q) :=
    fun m => by
      unfold qform
      exact integrable_finset_sum _ fun k _ =>
        (hV2 m k).integrable_mul (memLp_entry_sum hK (hV2 m) k)
  have hJi : ∀ ε : ℝ, 0 < ε → ∀ m,
      Integrable (fun x => rlogDeriv ε (ρ m x) * qform x (V m x))
        (Carriers.reducedReferenceLaw Q) := fun ε hε m =>
    (hqi m).bdd_mul ((continuous_rlogDeriv hε).measurable.comp (hρm m)).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_pos (rlogDeriv_pos hε _)]
        exact rlogDeriv_le hε _)
  obtain ⟨Drho, hDm, hD, hDi, hB⟩ := exists_series_gradient hd Q hw0
    (fun N => sum_range_gweight_le_one s.2 hsμ.le N) hρ0 hρi hρ1 hVm hρm hV1 hqi hC
    (hJsum 1 one_pos)
  have hrhom : Measurable rho := hrho.1
  have hrho0 : ∀ x, 0 ≤ rho x := hrho.2.1
  have hrho_sum : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q),
      HasSum (fun m => w m * ρ m x) (rho x) := by
    have h := ae_laplaceDensity_eq_tsum Q.measure P op s.2 hsμ.le hrho hρ
    rw [← href] at h
    filter_upwards [h] with x hx
    refine hasSum_of_ofReal_eq_tsum (fun m => mul_nonneg (hw0 m) (hρ0 m x)) (hrho0 x) ?_
    rw [hx]
    exact tsum_congr fun m => (ENNReal.ofReal_mul (hw0 m)).symm
  have hrhoi : Integrable rho (Carriers.reducedReferenceLaw Q) := by
    have h1 := Density.integral_density_eq_one Q.measure P op s rho hrho
    rw [← href] at h1
    exact Integrable.of_integral_ne_zero (by rw [h1]; exact one_ne_zero)
  have hqnn : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), ∀ v, 0 ≤ qform x v :=
    (ae_qform_bounds hd Q).mono fun x hx v =>
      (mul_nonneg (inv_nonneg.mpr hΛ.le) (euclideanSq_nonneg_fisher v)).trans (hx v).1
  have hsym : ∀ᵐ x ∂(Carriers.reducedReferenceLaw Q), (x.1 0).transpose = x.1 0 :=
    (ae_reduced_elliptic_zero Q).mono fun x hx => hx.1
  refine ⟨Drho, hasWeakHorizontalGradient_series Q hQ hw0 hwsum.summable hρm hρ0 hρi hρ1 hVm
    hV1 hρV hrhom hrhoi hrho_sum hDm hD hDi hB, hDi, ?_⟩
  exact fisher_lintegral_le hrhom hrho0 hDm hqnn hsym fun ε hε =>
    lintegral_qform_div_le hw hwsum hρm hρ0 hVm hqnn hε (hJi ε hε) hrho0 hrho_sum hD (hJsum ε hε)

end EinsteinRelation.Entropy
