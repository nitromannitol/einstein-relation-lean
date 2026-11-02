import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_bootstrap_u2D_point
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_bootstrap_u2D_average
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_unit_u2D_initialization
import EinsteinFull.Blueprint.G2.node_p_u3A_scalar_u23_smoothing_u2D_selection
import EinsteinFull.Blueprint.G3.Proofs.W3ScalarIntegral
import EinsteinFull.Calculus.ComplexHighExponentSupport
import EinsteinFull.Calculus.ScalarWeightSupport
import Mathlib.Analysis.SpecificLimits.Normed

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Widen the fixed exponential growth weight. The preceding point amplitude
is rescaled at t/8; the averaged amplitude is rescaled at t. -/
theorem bootstrap_point_rescaled_amplitude {g₀ g x B K L : ℝ}
    (hg : g₀ ≤ g) (hx : 0 ≤ x) (hK : 0 ≤ K) :
    (B * (L * Real.exp ((g - g₀) * x)) +
        (K * Real.exp ((g - g₀) * x / 8)) / 2) * Real.exp (g₀ * x) ≤
      (B * L + K / 2) * Real.exp (g * x) := by
  have he : Real.exp ((g - g₀) * x) * Real.exp (g₀ * x) =
      Real.exp (g * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have he8 : Real.exp ((g - g₀) * x / 8) * Real.exp (g₀ * x) ≤
      Real.exp (g * x) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sub_nonneg.mpr hg) hx]
  calc
    _ = B * L * (Real.exp ((g - g₀) * x) * Real.exp (g₀ * x)) +
        (K / 2) * (Real.exp ((g - g₀) * x / 8) * Real.exp (g₀ * x)) := by ring
    _ ≤ B * L * Real.exp (g * x) + (K / 2) * Real.exp (g * x) := by
      rw [he]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he8
        (show 0 ≤ K / 2 from div_nonneg hK (by norm_num)))
    _ = _ := by ring

/-- The point half of the scalar bootstrap on the last, possibly truncated,
doubling interval. The smoothing fraction is selected after the moment order. -/
theorem bootstrap_point_point_step_of_smoothing_selection
    (hSelection : node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ a₀ : ℝ, 0 < a₀ ∧ a₀ ≤ 1 / 16 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ b growth₀ T₀ : ℝ,
      0 < b ∧ b ≤ a₀ ∧ 0 < growth₀ ∧ 16 ≤ T₀ ∧ b⁻¹ ≤ T₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth →
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      let w := fun s : ℝ => s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)
      let N := fun f : Lp ℂ 2 (reducedLaw Q) =>
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Point := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        MemLp (U r : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        N (U r) ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w (r : ℝ)
      let Avg := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        ∀ s : ℝ, b * (r : ℝ) ≤ s → ∀ hs : 0 < s,
          MemLp (gaussianAverage hd Q s hs (U r) : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q) ∧
          N (gaussianAverage hd Q s hs (U r)) ≤
            K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w s
      ∀ T F Kavg Kprime : ℝ, T₀ ≤ T → 1 ≤ Kavg → 1 ≤ Kprime →
        Point T Kprime → Avg (min (2 * T) F) Kavg →
        Point (min (2 * T) F) (max Kprime (b ^ (-h) * Kavg + Kprime / 2)) := by
  intro d hd D
  obtain ⟨a₀, ha₀, ha₀16, hSelection⟩ := hSelection d hd D
  refine ⟨a₀, ha₀, ha₀16, ?_⟩
  intro p hp
  obtain ⟨b, growth, T₀, hb, hba, hgrowth, hT₀, hbT₀, hSelection⟩ := hSelection p hp
  refine ⟨b, growth, T₀, hb, hba, hgrowth, hT₀, hbT₀, ?_⟩
  intro growthNew hgrowthNew Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  dsimp only
  intro T F Kavg Kprime hT hKavg hKprime hPoint hAvg t ht1 ht
  have hw : 0 ≤ (t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) +
      ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4) := by positivity
  by_cases htT : (t : ℝ) ≤ T
  · obtain ⟨hm, hn⟩ := hPoint t ht1 htT
    refine ⟨hm, hn.trans ?_⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le) hw
  have hTt : T < (t : ℝ) := lt_of_not_ge htT
  have ht₀ : T₀ ≤ (t : ℝ) := hT.trans hTt.le
  have htpos : 0 < (t : ℝ) := zero_lt_one.trans_le ht1
  have ht8one : 1 ≤ ((t / 8 : ℝ≥0) : ℝ) := by
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith only [hT₀, hT, hTt]
  have ht8T : ((t / 8 : ℝ≥0) : ℝ) ≤ T := by
    have ht2 := ht.trans (min_le_left _ _)
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    linarith only [hT₀, hT, ht2]
  obtain ⟨hm8, hn8⟩ := hPoint (t / 8) ht8one ht8T
  let x := ‖ζ‖ ^ 2 * (t : ℝ)
  let δ := growthNew - growth
  have hx : 0 ≤ x := mul_nonneg (sq_nonneg _) t.property
  have hδ : 0 ≤ δ := sub_nonneg.mpr hgrowthNew
  have he8 : 1 ≤ Real.exp (δ * x / 8) := Real.one_le_exp (by positivity)
  have he : 1 ≤ Real.exp (δ * x) := Real.one_le_exp (by positivity)
  have hKprime' : 1 ≤ Kprime * Real.exp (δ * x / 8) := by
    nlinarith only [hKprime, he8, mul_le_mul hKprime he8 zero_le_one
      (zero_le_one.trans hKprime)]
  have hKavg' : 1 ≤ Kavg * Real.exp (δ * x) := by
    nlinarith only [hKavg, he, mul_le_mul hKavg he zero_le_one
      (zero_le_one.trans hKavg)]
  have hn8' : (eLpNorm
      (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (Kprime * Real.exp (δ * x / 8)) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
        (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) := by
    have heq : Real.exp (δ * x / 8) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) =
        Real.exp (growthNew * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [δ, x]
      ring
    rw [mul_assoc Kprime, heq]
    simpa only [NNReal.coe_div, NNReal.coe_ofNat, mul_div_assoc] using! hn8
  have hbt : 0 < b * (t : ℝ) := mul_pos hb htpos
  obtain ⟨_, _, hPointStep⟩ := hSelection Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    t ht₀ _ hKprime' hm8 hn8' hbt
  obtain ⟨hmavg, hnavg⟩ := hAvg t ht1 ht (b * (t : ℝ)) le_rfl hbt
  have hnavg' : (eLpNorm (gaussianAverage hd Q (b * (t : ℝ)) hbt
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (Kavg * Real.exp (δ * x)) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) *
        ((b * (t : ℝ)) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * (b * (t : ℝ)) ^ (-(d : ℝ) / 4)) := by
    have heq : Real.exp (δ * x) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) =
        Real.exp (growthNew * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      dsimp only [δ, x]
      ring
    rwa [mul_assoc Kavg, heq]
  obtain ⟨hm, hnBase⟩ := hPointStep _ hKavg' hmavg hnavg'
  have hn : (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (b ^ (-(1 / 2 + (d : ℝ) / 4)) * Kavg + Kprime / 2) *
        Real.exp (growthNew * ‖ζ‖ ^ 2 * (t : ℝ)) *
          ((t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) +
            ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4)) := by
    apply hnBase.trans
    have hr := bootstrap_point_rescaled_amplitude
      (B := b ^ (-(1 / 2 + (d : ℝ) / 4))) (K := Kprime) (L := Kavg)
      hgrowthNew hx (zero_le_one.trans hKprime)
    dsimp only [δ, x] at *
    simp only [mul_assoc] at hr ⊢
    simpa only [mul_assoc] using! mul_le_mul_of_nonneg_right hr hw
  refine ⟨hm, hn.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le) hw

/-- The half-error step preserves the ratio used in the averaged recurrence. -/
theorem bootstrap_point_bootstrap_ratio_step {B K Kprime Knext : ℝ}
    (hB : 0 ≤ B) (hKKnext : K ≤ Knext) (hRatio : Kprime ≤ 2 * B * K) :
    max Kprime (B * Knext + Kprime / 2) ≤ 2 * B * Knext := by
  have hOld : Kprime ≤ 2 * B * Knext :=
    hRatio.trans (mul_le_mul_of_nonneg_left hKKnext (by positivity))
  exact max_le hOld (by linarith only [hOld])

/-- Substitution of the ratio invariant leaves a coefficient-one averaged step. -/
theorem bootstrap_point_bootstrap_average_step {B C e K Kprime Knext : ℝ}
    (hC : 0 ≤ C) (he : 0 ≤ e) (hRatio : Kprime ≤ 2 * B * K)
    (hNext : Knext ≤ K + C * e * Kprime) :
    Knext ≤ (1 + 2 * B * C * e) * K := by
  calc
    Knext ≤ K + C * e * Kprime := hNext
    _ ≤ K + C * e * (2 * B * K) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hRatio (mul_nonneg hC he))
    _ = (1 + 2 * B * C * e) * K := by ring

/-- Dyadic gains have a finite sum, with an explicit scale-dependent value. -/
theorem bootstrap_point_dyadic_gain_hasSum {ε T : ℝ} (hε : 0 < ε) (hT : 0 < T) :
    HasSum (fun n : ℕ => ((2 : ℝ) ^ n * T) ^ (-ε))
      (T ^ (-ε) / (1 - (2 : ℝ) ^ (-ε))) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-ε) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (2 : ℝ) ^ (-ε) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε)
  have h := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (T ^ (-ε))
  convert h using 1
  · funext n
    rw [Real.mul_rpow (by positivity) hT.le]
    rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (n : ℝ) (-ε),
      Real.rpow_mul_natCast (by norm_num)]
    ring
  · exact div_eq_mul_inv _ _

/-- The dyadic product is uniformly bounded; no fixed loss is paid per scale. -/
theorem bootstrap_point_dyadic_product_le {ε T A : ℝ} (hε : 0 < ε) (hT : 0 < T)
    (hA : 0 ≤ A) (n : ℕ) :
    (∏ j ∈ Finset.range n, (1 + A * ((2 : ℝ) ^ j * T) ^ (-ε))) ≤
      Real.exp (A * T ^ (-ε) / (1 - (2 : ℝ) ^ (-ε))) := by
  have hsum := bootstrap_point_dyadic_gain_hasSum hε hT
  calc
    _ ≤ ∏ j ∈ Finset.range n, Real.exp (A * ((2 : ℝ) ^ j * T) ^ (-ε)) := by
      apply Finset.prod_le_prod₀
      · intro j _
        positivity
      · intro j _
        simpa only [add_comm] using! Real.add_one_le_exp (A * ((2 : ℝ) ^ j * T) ^ (-ε))
    _ = Real.exp (A * ∑ j ∈ Finset.range n, ((2 : ℝ) ^ j * T) ^ (-ε)) := by
      rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hpartial := hsum.summable.sum_le_tsum (Finset.range n)
        (fun j _ => Real.rpow_nonneg (by positivity) (-ε))
      rw [hsum.tsum_eq] at hpartial
      simpa only [mul_div_assoc] using! mul_le_mul_of_nonneg_left hpartial hA

/-- Close a finite-horizon averaged/point bootstrap by the summable dyadic
product. This is a numerical iteration lemma; the actual endpoint predicates
and their two steps are supplied by the source-facing dependencies. -/
theorem bootstrap_point_truncated_bootstrap_close
    (Avg Point : ℝ → ℝ → Prop) {B C ε T F K₀ : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hε : 0 < ε) (hT : 0 < T)
    (hTF : T ≤ F) (hK₀ : 1 ≤ K₀)
    (hAvgMono : ∀ S K L, K ≤ L → Avg S K → Avg S L)
    (hPointMono : ∀ S K L, K ≤ L → Point S K → Point S L)
    (hAvgInit : Avg T K₀) (hPointInit : Point T (2 * B * K₀))
    (hAvgStep : ∀ S K Kprime, T ≤ S → S ≤ F → 1 ≤ K → 1 ≤ Kprime →
      Avg S K → Point S Kprime →
      Avg (min (2 * S) F) (K + C * S ^ (-ε) * Kprime))
    (hPointStep : ∀ S K Kprime, T ≤ S → S ≤ F → 1 ≤ K → 1 ≤ Kprime →
      Point S Kprime → Avg (min (2 * S) F) K →
      Point (min (2 * S) F) (max Kprime (B * K + Kprime / 2))) :
    let M := K₀ * Real.exp (2 * B * C * T ^ (-ε) / (1 - (2 : ℝ) ^ (-ε)))
    Avg F M ∧ Point F (2 * B * M) := by
  let K := fun n : ℕ => K₀ *
    ∏ j ∈ Finset.range n, (1 + (2 * B * C) * ((2 : ℝ) ^ j * T) ^ (-ε))
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hK₀0 : 0 ≤ K₀ := zero_le_one.trans hK₀
  have hKn (n : ℕ) : 1 ≤ K n := by
    apply hK₀.trans
    dsimp only [K]
    calc
      K₀ = K₀ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by
          have hprod := Finset.prod_le_prod₀
            (s := Finset.range n) (f := fun _ => (1 : ℝ))
            (g := fun j => 1 + (2 * B * C) * ((2 : ℝ) ^ j * T) ^ (-ε))
            (fun _ _ => zero_le_one)
            (fun j _ => le_add_of_nonneg_right (by positivity))
          simpa only [Finset.prod_const_one] using! hprod) hK₀0
  have hKrec (n : ℕ) : K (n + 1) =
      K n + C * ((2 : ℝ) ^ n * T) ^ (-ε) * (2 * B * K n) := by
    dsimp only [K]
    rw [Finset.prod_range_succ]
    ring
  have hKmono (n : ℕ) : K n ≤ K (n + 1) := by
    rw [hKrec]
    have hnonneg : 0 ≤ C * ((2 : ℝ) ^ n * T) ^ (-ε) * (2 * B * K n) := by
      have := hKn n
      positivity
    exact le_add_of_nonneg_right hnonneg
  have hKprime (n : ℕ) : 1 ≤ 2 * B * K n := by
    have hmul := mul_le_mul hB (hKn n) (by norm_num) hB0
    nlinarith only [hmul]
  have hIter (n : ℕ) : Avg (min ((2 : ℝ) ^ n * T) F) (K n) ∧
      Point (min ((2 : ℝ) ^ n * T) F) (2 * B * K n) := by
    induction n with
    | zero => simpa only [pow_zero, one_mul, min_eq_left hTF, K,
        Finset.range_zero, Finset.prod_empty, mul_one] using And.intro hAvgInit hPointInit
    | succ n ih =>
      by_cases hdone : F ≤ (2 : ℝ) ^ n * T
      · have hdone' : F ≤ (2 : ℝ) ^ (n + 1) * T := by
          rw [pow_succ]
          have hn : 0 ≤ (2 : ℝ) ^ n * T := by positivity
          nlinarith only [hdone, hn]
        rw [min_eq_right hdone] at ih
        rw [min_eq_right hdone']
        exact ⟨hAvgMono F _ _ (hKmono n) ih.1,
          hPointMono F _ _ (mul_le_mul_of_nonneg_left (hKmono n) (by positivity)) ih.2⟩
      have hnF : (2 : ℝ) ^ n * T ≤ F := (lt_of_not_ge hdone).le
      have hTn : T ≤ (2 : ℝ) ^ n * T := by
        simpa only [one_mul] using!
          mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)) hT.le
      rw [min_eq_left hnF] at ih
      have ha := hAvgStep _ _ _ hTn hnF (hKn n) (hKprime n) ih.1 ih.2
      rw [← hKrec n] at ha
      have hp := hPointStep _ _ _ hTn hnF (hKn (n + 1)) (hKprime n) ih.2 ha
      have hr := bootstrap_point_bootstrap_ratio_step hB0 (hKmono n)
        (le_refl (2 * B * K n))
      have hp' := hPointMono _ _ _ hr hp
      have hscale : 2 * ((2 : ℝ) ^ n * T) = (2 : ℝ) ^ (n + 1) * T := by
        rw [pow_succ]; ring
      rw [hscale] at ha hp'
      exact ⟨ha, hp'⟩
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (F / T) (by norm_num : (1 : ℝ) < 2)
  have hcover : F ≤ (2 : ℝ) ^ n * T := ((div_lt_iff₀ hT).mp hn).le
  have hFinal := hIter n
  rw [min_eq_right hcover] at hFinal
  have hbound : K n ≤ K₀ *
      Real.exp (2 * B * C * T ^ (-ε) / (1 - (2 : ℝ) ^ (-ε))) :=
    mul_le_mul_of_nonneg_left
      (bootstrap_point_dyadic_product_le hε hT (by positivity : 0 ≤ 2 * B * C) n) hK₀0
  exact ⟨hAvgMono F _ _ hbound hFinal.1,
    hPointMono F _ _ (mul_le_mul_of_nonneg_left hbound (by positivity)) hFinal.2⟩

/-- The point weight is uniformly bounded below on the starting interval. -/
theorem bootstrap_point_initial_weight {h T t g q : ℝ}
    (hh : 0 ≤ h) (hT : 1 ≤ T) (ht : 1 ≤ t) (htT : t ≤ T)
    (hg : 0 ≤ g) (hq : 0 ≤ q) :
    1 ≤ T ^ h * Real.exp (g * q * t) * t ^ (-h) := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hp := Real.rpow_le_rpow_of_nonpos htpos htT (neg_nonpos.mpr hh)
  have hexp : 1 ≤ Real.exp (g * q * t) := Real.one_le_exp (by positivity)
  calc
    1 = T ^ h * T ^ (-h) := by rw [← Real.rpow_add hTpos]; simp only [add_neg_cancel, Real.rpow_zero]
    _ ≤ T ^ h * t ^ (-h) := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hTpos.le _)
    _ ≤ T ^ h * Real.exp (g * q * t) * t ^ (-h) := by
      have hmul := mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg hTpos.le h)
      simpa only [mul_one] using! mul_le_mul_of_nonneg_right hmul
        (Real.rpow_nonneg htpos.le (-h))

/-- A single structural amplitude initializes both actual indexed-endpoint
predicates. The amplitude precedes the environment, force, operators and index. -/
theorem bootstrap_point_common_initialization
    (hInit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (b : ℝ) (hb : 0 < b) (hb1 : b < 1)
    (p : ℝ) (hp : 2 ≤ p) (T : ℝ) (hT : 1 ≤ T) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ growth : ℝ, 0 ≤ growth →
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      (MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) *
            ((t : ℝ) ^ (-h) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4))) ∧
      (∀ s : ℝ, b * (t : ℝ) ≤ s → ∀ hs : 0 < s,
        MemLp (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (gaussianAverage hd Q s hs U : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4))) := by
  obtain ⟨C, hC, hInit⟩ := hInit d hd D b hb hb1 p hp T hT
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hpow : 1 ≤ T ^ h := Real.one_le_rpow hT hh
  have hK : 1 ≤ C * T ^ h := by
    simpa only [one_mul] using! (mul_le_mul hC hpow zero_le_one (zero_le_one.trans hC))
  refine ⟨C * T ^ h, hK, ?_⟩
  intro growth hg Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t ht htT
  dsimp only
  obtain ⟨hpt, havg⟩ := hInit Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ t htT
  have he : 1 ≤ Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) := Real.one_le_exp (by positivity)
  have hscale : C ≤ (C * T ^ h) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) *
      ((t : ℝ) ^ (-h) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4)) := by
    have hw := bootstrap_point_initial_weight hh hT ht htT hg (sq_nonneg ‖ζ‖)
    have hw' := mul_le_mul_of_nonneg_left hw (zero_le_one.trans hC)
    calc
      C ≤ (C * T ^ h) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) * (t : ℝ) ^ (-h) := by
        simpa only [mul_one, mul_assoc] using! hw'
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_right (by positivity)) (by positivity)
  refine ⟨⟨hpt.1, hpt.2.trans hscale⟩, ?_⟩
  intro s hbs hs
  obtain ⟨hm, hn⟩ := havg s hbs hs
  refine ⟨hm, hn.trans ?_⟩
  have hcoef : C ≤ (C * T ^ h) * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    calc
      C ≤ C * T ^ h := by simpa only [mul_one] using! mul_le_mul_of_nonneg_left hpow (by linarith)
      _ ≤ _ := by simpa only [mul_one] using! mul_le_mul_of_nonneg_left he (by positivity)
  exact mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- The actual coupled bootstrap closes uniformly at every admissible terminal
horizon. Inner fractions and amplitudes are selected before the environment;
the force window is used only at the terminal horizon. -/
theorem bootstrap_point_indexed_terminal_bounds
    (hAverage : node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt)
    (hInit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt)
    (hSelection : node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ η : ℝ, 0 < η ∧ ∀ p : ℝ, 2 ≤ p →
    ∃ b growth T M : ℝ, 0 < b ∧ b ≤ 1 / 16 ∧ 0 < growth ∧ 16 ≤ T ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let h : ℝ := 1 / 2 + (d : ℝ) / 4
      let w := fun s : ℝ => s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)
      let N := fun f : Lp ℂ 2 (reducedLaw Q) =>
        (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Point := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        MemLp (U r : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        N (U r) ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w (r : ℝ)
      let Avg := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
        ∀ s : ℝ, b * (r : ℝ) ≤ s → ∀ hs : 0 < s,
          MemLp (gaussianAverage hd Q s hs (U r) : FieldPair d → ℂ)
            (ENNReal.ofReal p) (reducedLaw Q) ∧
          N (gaussianAverage hd Q s hs (U r)) ≤
            K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w s
      ‖ζ‖ ≤ 1 → ∀ F : ℝ, T ≤ F → ‖ζ‖ * Real.sqrt F ≤ F ^ η →
        Point F M ∧ Avg F M := by
  obtain ⟨ε, η, hε, hη, _, hAverage⟩ := hAverage d hd D
  obtain ⟨a₀, ha₀, ha₀16, hSelection⟩ :=
    bootstrap_point_point_step_of_smoothing_selection hSelection d hd D
  refine ⟨η, hη, ?_⟩
  intro p hp
  obtain ⟨b, gS, TS, hb, hba, hgS, hTS, _, hSelection⟩ := hSelection p hp
  have hb16 : b ≤ 1 / 16 := hba.trans ha₀16
  have hb1 : b < 1 := lt_of_le_of_lt hb16 (by norm_num)
  obtain ⟨C, gA, TA, hC, _, hTA, _, hAverage⟩ := hAverage b hb hb16 p hp
  let growth := max gS gA
  let T := max TS TA
  have hT16 : 16 ≤ T := hTS.trans (le_max_left _ _)
  have hT1 : 1 ≤ T := le_trans (by norm_num) hT16
  have hTpos : 0 < T := zero_lt_one.trans_le hT1
  have hg : 0 < growth := hgS.trans_le (le_max_left _ _)
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  let B := b ^ (-h)
  have hh : 0 ≤ h := by dsimp only [h]; positivity
  have hB : 1 ≤ B := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hb hb1.le (neg_nonpos.mpr hh)
  obtain ⟨K₀, hK₀, hInit⟩ := bootstrap_point_common_initialization hInit d hd D b hb hb1 p hp T hT1
  let A := K₀ * Real.exp (2 * B * C * T ^ (-ε) / (1 - (2 : ℝ) ^ (-ε)))
  let M := 2 * B * A
  have hApos : 0 < A := mul_pos (zero_lt_one.trans_le hK₀) (Real.exp_pos _)
  have hMpos : 0 < M := mul_pos (mul_pos (by norm_num) (zero_lt_one.trans_le hB)) hApos
  refine ⟨b, growth, T, M, hb, hb16, hg, hT16, hMpos, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  dsimp only
  intro hζ F hTF hwindow
  let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
  let w := fun s : ℝ => s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)
  let N := fun f : Lp ℂ 2 (reducedLaw Q) =>
    (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let Point := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
    MemLp (U r : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    N (U r) ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w (r : ℝ)
  let Avg := fun (S K : ℝ) => ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → (r : ℝ) ≤ S →
    ∀ s : ℝ, b * (r : ℝ) ≤ s → ∀ hs : 0 < s,
      MemLp (gaussianAverage hd Q s hs (U r) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      N (gaussianAverage hd Q s hs (U r)) ≤
        K * Real.exp (growth * ‖ζ‖ ^ 2 * (r : ℝ)) * w s
  change Point F M ∧ Avg F M
  have hw (s : ℝ) (hs : 0 ≤ s) : 0 ≤ w s := by dsimp only [w]; positivity
  have hPointMono : ∀ S K L, K ≤ L → Point S K → Point S L := by
    intro S K L hKL hpoint r hr hrS
    obtain ⟨hm, hn⟩ := hpoint r hr hrS
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKL (Real.exp_pos _).le) (hw _ r.property))⟩
  have hAvgMono : ∀ S K L, K ≤ L → Avg S K → Avg S L := by
    intro S K L hKL havg r hr hrS s hbs hs
    obtain ⟨hm, hn⟩ := havg r hr hrS s hbs hs
    exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKL (Real.exp_pos _).le) (hw _ hs.le))⟩
  have hi := hInit growth hg.le Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν (hζ.trans (by norm_num))
  have hiP : Point T K₀ := fun r hr hrT => (hi r hr hrT).1
  have hiA : Avg T K₀ := fun r hr hrT => (hi r hr hrT).2
  have hKratio : K₀ ≤ 2 * B * K₀ := by
    have hB0 : 0 ≤ B := zero_le_one.trans hB
    have htwo : 1 ≤ 2 * B := by linarith only [hB]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right htwo (zero_le_one.trans hK₀)
  have hstepA : ∀ S K Kprime, T ≤ S → S ≤ F → 1 ≤ K → 1 ≤ Kprime →
      Avg S K → Point S Kprime → Avg (min (2 * S) F) (K + C * S ^ (-ε) * Kprime) := by
    intro S K Kprime hTS hSF hK hKprime hAvg hPoint
    exact hAverage growth (le_max_right _ _) Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
      hζ F S ((le_max_right TS TA).trans hTS) hSF hwindow K Kprime hK hKprime hAvg hPoint
  have hstepP : ∀ S K Kprime, T ≤ S → S ≤ F → 1 ≤ K → 1 ≤ Kprime →
      Point S Kprime → Avg (min (2 * S) F) K →
      Point (min (2 * S) F) (max Kprime (B * K + Kprime / 2)) := by
    intro S K Kprime hTS _ hK hKprime hPoint hAvg
    exact hSelection growth (le_max_left _ _) Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
      S F K Kprime ((le_max_left TS TA).trans hTS) hK hKprime hPoint hAvg
  obtain ⟨havg, hpoint⟩ := bootstrap_point_truncated_bootstrap_close Avg Point hB hC.le hε hTpos hTF hK₀
    hAvgMono hPointMono hiA (hPointMono _ _ _ hKratio hiP) hstepA hstepP
  have hAM : A ≤ M := by
    have htwo : 1 ≤ 2 * B := by linarith only [hB]
    simpa only [one_mul] using! mul_le_mul_of_nonneg_right htwo hApos.le
  exact ⟨hpoint, hAvgMono _ _ _ hAM havg⟩

/-- Stationary convolution by an integrable continuous kernel preserves every
finite p >= 2. The integral is the actual L2 Bochner integral. -/
theorem bootstrap_point_kernel_Lp {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    (k : Vec d → ℂ) (hk : Continuous k) (hki : Integrable k)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
    let u := ∫ x : Vec d, k x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
    MemLp (u : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (u : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (∫ x : Vec d, ‖k x‖) * (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  letI := reducedLaw_probability Q
  let q := ENNReal.ofReal p
  have hq : 2 ≤ q := by exact_mod_cast ENNReal.ofReal_le_ofReal hp
  letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let fp : Lp ℂ q (reducedLaw Q) := hf.toLp f
  let τ : Vec d → Lp ℂ q (reducedLaw Q) →ₗᵢ[ℂ] Lp ℂ q (reducedLaw Q) :=
    fun x : Vec d => Lp.compMeasurePreservingₗᵢ ℂ (translate x)
    (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
  have hc : Continuous (fun x : Vec d => τ x fp) := by
    let g : Vec d → C(FieldPair d, FieldPair d) := fun x =>
      ⟨translate x, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
    have hg : Continuous g := by
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact Probability.continuous_translate
    exact continuous_const.compMeasurePreservingLp hg
      (fun x => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
      ENNReal.ofReal_ne_top
  have hi : Integrable (fun x : Vec d => k x • τ x fp) := by
    apply Integrable.mono' (hki.norm.mul_const ‖fp‖) (hk.fun_smul hc).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by rw [norm_smul, (τ x).norm_map]
  let v := ∫ x : Vec d, k x • τ x fp
  have hinc : complexLpToL2 (reducedLaw Q) hq fp = f := by
    apply Lp.ext
    exact hf.coeFn_toLp
  have hτ (x : Vec d) : complexLpToL2 (reducedLaw Q) hq (τ x fp) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f := by
    rw [← hinc]
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving fp
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)).trans
      (coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (complexLpToL2 (reducedLaw Q) hq fp)).symm
  have heq : complexLpToL2 (reducedLaw Q) hq v =
      ∫ x : Vec d, k x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f := by
    change (complexLpToL2CLM (reducedLaw Q) hq) (∫ x : Vec d, k x • τ x fp) = _
    rw [← ContinuousLinearMap.integral_comp_comm _ hi]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [map_smul]
      exact congrArg (fun v => k x • v) (hτ x)
  dsimp only
  rw [← heq]
  refine ⟨Lp.memLp v, ?_⟩
  change ‖v‖ ≤ _
  have hv : ‖v‖ ≤ (∫ x : Vec d, ‖k x‖) * ‖fp‖ := by
    calc
      ‖v‖ ≤ ∫ x : Vec d, ‖k x • τ x fp‖ := norm_integral_le_integral_norm _
      _ = _ := by simp only [norm_smul, LinearIsometry.norm_map, integral_mul_const]
  have hnorm : ‖fp‖ = (eLpNorm f q (reducedLaw Q)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hf.coeFn_toLp]
  exact hv.trans_eq (congrArg _ hnorm)

/-- The all-order Gaussian derivative estimate on the actual stationary Lp
carrier follows from the kernel L1 norm, with no field-derivative premise. -/
theorem bootstrap_point_derivative_Lp {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (p : ℝ) (hp : 2 ≤ p)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
    MemLp (gaussianDerivativeAverage hd Q s hs k dirs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (gaussianDerivativeAverage hd Q s hs k dirs f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (∫ x : Vec d, ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) x
          (fun j => unitVector (dirs j))‖) *
        (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  have h := bootstrap_point_kernel_Lp Q p hp _
    (continuous_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs k dirs)
    (integrable_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs k dirs) f hf
  simpa only [gaussianDerivativeAverage, integral_neg_eq_self
    (fun x : Vec d => ‖iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) x
        (fun j => unitVector (dirs j))‖) volume] using h

private theorem bootstrap_point_half_power (s v : ℝ) (hs : 0 < s) :
    (s / 2) ^ v = (2 : ℝ) ^ (-v) * s ^ v := by
  rw [Real.div_rpow hs.le (by norm_num), div_eq_mul_inv,
    ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_comm _ _

private theorem bootstrap_point_half_weight (d : ℕ) (s m : ℝ) (hs : 0 < s) (hm : 0 ≤ m) :
    (s / 2) ^ (-(1 / 2 + (d : ℝ) / 4)) + m * (s / 2) ^ (-(d : ℝ) / 4) ≤
      (2 : ℝ) ^ (1 / 2 + (d : ℝ) / 4) *
        (s ^ (-(1 / 2 + (d : ℝ) / 4)) + m * s ^ (-(d : ℝ) / 4)) := by
  rw [bootstrap_point_half_power s _ hs, bootstrap_point_half_power s _ hs]
  simp only [neg_neg, neg_div, neg_neg]
  have hpow : (2 : ℝ) ^ ((d : ℝ) / 4) ≤ (2 : ℝ) ^ (1 / 2 + (d : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hmul := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hs.le (-(d : ℝ) / 4))) hm
  simp only [neg_div] at hmul
  nlinarith only [hmul]

/-- The coupled scalar bootstrap, structural outer restriction, compact-force
bound and every fixed Gaussian derivative on the literal endpoint collection. -/
@[nolint unusedArguments]
theorem node_p_u3A_scalar_u23_bootstrap_u2D_point_of_deps
    (hAverage : node_p_u3A_scalar_u23_bootstrap_u2D_averageStmt)
    (_hHolder : node_e_u3A_holder_u2D_averageStmt)
    (hInit : node_p_u3A_scalar_u23_unit_u2D_initializationStmt)
    (hSelection : node_p_u3A_scalar_u23_smoothing_u2D_selectionStmt) :
    node_p_u3A_scalar_u23_bootstrap_u2D_pointStmt := by
  intro d hd D
  obtain ⟨η, hη, hwide⟩ := bootstrap_point_indexed_terminal_bounds hAverage hInit hSelection d hd D
  refine ⟨1 / 16, η, by norm_num, by norm_num, hη, ?_⟩
  intro p hp
  obtain ⟨b, g, T, M, hb, hb16, hg, hT, hM, hwide⟩ := hwide p hp
  let t₀ := max T ((2 : ℝ) ^ (1 / η))
  have ht₀ : 1 ≤ t₀ := le_trans (by linarith only [hT]) (le_max_left _ _)
  obtain ⟨K₀, hK₀, hinit⟩ := bootstrap_point_common_initialization hInit d hd D
    (1 / 16) (by norm_num) (by norm_num) p hp t₀ ht₀
  obtain ⟨B, hB, hkernel⟩ := ScalarIntegral.exists_derivativeKernel_integral_bound d
    D.ellipticity D.one_le_ellipticity
  let L := 3 * max (M * Real.exp (4 * g)) K₀ + M + 1
  let C := ((d : ℝ) + 2) * L
  let h : ℝ := 1 / 2 + (d : ℝ) / 4
  let Cder := fun k : ℕ => B k * (2 : ℝ) ^ ((k : ℝ) / 2) * M * (2 : ℝ) ^ h + 1
  have hLpos : 0 < L := by
    have hmax : 0 < max (M * Real.exp (4 * g)) K₀ :=
      lt_of_lt_of_le (zero_lt_one.trans_le hK₀) (le_max_right _ _)
    dsimp only [L]
    positivity
  have hLM : M ≤ L := by
    have hmax : 0 ≤ max (M * Real.exp (4 * g)) K₀ :=
      zero_le_one.trans (hK₀.trans (le_max_right _ _))
    dsimp only [L]
    linarith only [hmax]
  have hLC : L ≤ C := by
    have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
    dsimp only [C]
    nlinarith only [mul_nonneg hd0 hLpos.le, hLpos.le]
  have hMC : M ≤ C := hLM.trans hLC
  have hC : 0 < C := hLpos.trans_le hLC
  have hCder : ∀ k, 0 < Cder k := by
    intro k
    have hBk := hB k
    dsimp only [Cder]
    positivity
  refine ⟨C, g, t₀, Cder, hC, hg, ht₀, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
  dsimp only
  have hcollect (t : ℝ≥0) (U : Lp ℂ 2 (reducedLaw Q))
      (hU : U ∈ endpointCollection Q ⟨0, by omega⟩ ζ P Pdag β a μ t) :
      ∃ ν : EndpointIndex d, U = indexedEndpoint hd Q ν ζ P Pdag β a μ t := by
    rcases hU with (htr | ⟨j, hj⟩) | hcl
    · exact ⟨.inr true, htr⟩
    · exact ⟨.inl j, hj.symm⟩
    · exact ⟨.inr false, hcl⟩
  have hwideAt (ν : EndpointIndex d) (t : ℝ≥0) (ht : t₀ ≤ (t : ℝ))
      (hζ : ‖ζ‖ ≤ 1) (hw : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η) :=
    hwide Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ (t : ℝ)
      ((le_max_left _ _).trans ht) hw
  have hdisc (t : ℝ≥0) (ht : 1 ≤ (t : ℝ))
      (hζt : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2) (ν : EndpointIndex d) :
      MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ L * (t : ℝ) ^ (-h) := by
    have htpos : 0 < (t : ℝ) := zero_lt_one.trans_le ht
    have hwgt := scalar_decay_weight_le_of_force_bound d ‖ζ‖ (t : ℝ) 2 htpos hζt
    norm_num only [show (1 + 2 : ℝ) = 3 by norm_num] at hwgt
    by_cases hlarge : t₀ ≤ (t : ℝ)
    · have ht4 : 4 ≤ (t : ℝ) := le_trans (by linarith only [hT]) ((le_max_left _ _).trans hlarge)
      obtain ⟨hz1, hwindow⟩ := scalar_compact_window_subset_wide ‖ζ‖ (t : ℝ) η
        (norm_nonneg _) ht4 hη ((le_max_right _ _).trans hlarge) hζt
      obtain ⟨hm, hn⟩ := (hwideAt ν t hlarge hz1 hwindow).1 t ht le_rfl
      have hx : ‖ζ‖ ^ 2 * (t : ℝ) ≤ 4 := by
        have hs : ‖ζ‖ * Real.sqrt (t : ℝ) ≥ 0 := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
        have hh := mul_self_le_mul_self hs hζt
        calc
          _ = ‖ζ‖ ^ 2 * (Real.sqrt (t : ℝ) * Real.sqrt (t : ℝ)) :=
            congrArg (fun v : ℝ => ‖ζ‖ ^ 2 * v) (Real.mul_self_sqrt t.property).symm
          _ = (‖ζ‖ * Real.sqrt (t : ℝ)) ^ 2 := by ring
          _ ≤ 4 := by nlinarith only [hh]
      have he : Real.exp (g * ‖ζ‖ ^ 2 * (t : ℝ)) ≤ Real.exp (4 * g) := by
        apply Real.exp_le_exp.mpr
        nlinarith only [mul_le_mul_of_nonneg_left hx hg.le]
      have hcoef : 3 * (M * Real.exp (4 * g)) ≤ L := by
        have hm := le_max_left (M * Real.exp (4 * g)) K₀
        dsimp only [L]
        linarith only [hm, hM.le]
      refine ⟨hm, hn.trans ?_⟩
      calc
        _ ≤ M * Real.exp (4 * g) * (3 * (t : ℝ) ^ (-h)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left he hM.le) hwgt (by positivity) (by positivity)
        _ = (3 * (M * Real.exp (4 * g))) * (t : ℝ) ^ (-h) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg t.property _)
    · have htT : (t : ℝ) ≤ t₀ := (lt_of_not_ge hlarge).le
      have hsqrt : 1 ≤ Real.sqrt (t : ℝ) := by
        simpa only [Real.sqrt_one] using! Real.sqrt_le_sqrt ht
      have hz2 : ‖ζ‖ ≤ 2 := by nlinarith only [hζt, mul_nonneg (norm_nonneg ζ) (sub_nonneg.mpr hsqrt)]
      obtain ⟨hm, hn⟩ := (hinit 0 le_rfl Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hz2 t ht htT).1
      simp only [zero_mul, Real.exp_zero, mul_one] at hn
      have hcoef : 3 * K₀ ≤ L := by
        have hm := le_max_right (M * Real.exp (4 * g)) K₀
        dsimp only [L]
        linarith only [hm, hM.le]
      refine ⟨hm, hn.trans ?_⟩
      exact (mul_le_mul_of_nonneg_left hwgt (zero_le_one.trans hK₀)).trans
        (by simpa only [h, mul_assoc, mul_comm, mul_left_comm] using!
          mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg t.property (-h)))
  constructor
  · intro t ht hz
    have hpnt := hdisc t ht hz
    have hnorm (ν : EndpointIndex d) := (hpnt ν).2
    have hsum : (∑ j : Fin d, (eLpNorm
        (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal) ≤
        (d : ℝ) * (L * (t : ℝ) ^ (-h)) := by
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using!
        Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hnorm (.inl j))
    refine ⟨?_, ?_⟩
    · intro U hU
      obtain ⟨ν, rfl⟩ := hcollect t U hU
      exact (hpnt ν).1
    · have htpt := hnorm (.inr true)
      have hclk := hnorm (.inr false)
      change _ + _ + _ ≤ C * (t : ℝ) ^ (-h)
      dsimp only [indexedEndpoint] at htpt hclk
      calc
        _ ≤ L * (t : ℝ) ^ (-h) + (d : ℝ) * (L * (t : ℝ) ^ (-h)) + L * (t : ℝ) ^ (-h) :=
          add_le_add (add_le_add htpt hsum) hclk
        _ = C * (t : ℝ) ^ (-h) := by dsimp only [C]; ring
  · intro t ht hζ hw U hU
    obtain ⟨ν, rfl⟩ := hcollect t U hU
    have ht1 : 1 ≤ (t : ℝ) := ht₀.trans ht
    have hbound := hwideAt ν t ht hζ hw
    have hpoint := hbound.1 t ht1 le_rfl
    have havg := hbound.2 t ht1 le_rfl
    have hnorm (s : ℝ) (hs : 0 < s) : 0 ≤ s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4) := by positivity
    refine ⟨⟨hpoint.1, hpoint.2.trans ?_⟩, ?_, ?_⟩
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMC (Real.exp_pos _).le) (hnorm _ (zero_lt_one.trans_le ht1))
    · intro s hst hs
      obtain ⟨hm, hn⟩ := havg s ((mul_le_mul_of_nonneg_right hb16 t.property).trans hst) hs
      exact ⟨hm, hn.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMC (Real.exp_pos _).le) (hnorm s hs))⟩
    · intro k dirs s hst hs
      have hs2 : b * (t : ℝ) ≤ s / 2 := by
        have hbnd := mul_le_mul_of_nonneg_right hb16 t.property
        norm_num at hbnd hst ⊢
        linarith only [hbnd, hst]
      obtain ⟨hm, hn⟩ := havg (s / 2) hs2 (half_pos hs)
      rw [ScalarIntegral.derivativeAverage_half_split]
      obtain ⟨hmd, hnd⟩ := bootstrap_point_derivative_Lp hd Q p hp (s / 2) (half_pos hs)
        k dirs _ hm
      refine ⟨hmd, hnd.trans ?_⟩
      have hBk := hB k
      have hkb := hkernel D.dependenceRange Q ⟨0, by omega⟩ (s / 2) (half_pos hs) k dirs
      have hhalf := bootstrap_point_half_weight d s ‖ζ‖ hs (norm_nonneg _)
      have hpp : (s / 2) ^ (-(k : ℝ) / 2) = (2 : ℝ) ^ ((k : ℝ) / 2) * s ^ (-(k : ℝ) / 2) := by
        rw [bootstrap_point_half_power s _ hs]
        congr 2
        ring
      have hcder : B k * (2 : ℝ) ^ ((k : ℝ) / 2) * M * (2 : ℝ) ^ h ≤ Cder k := by
        exact le_add_of_nonneg_right zero_le_one
      calc
        _ ≤ (B k * (s / 2) ^ (-(k : ℝ) / 2)) *
            (M * Real.exp (g * ‖ζ‖ ^ 2 * (t : ℝ)) *
              ((s / 2) ^ (-h) + ‖ζ‖ * (s / 2) ^ (-(d : ℝ) / 4))) :=
          mul_le_mul hkb hn ENNReal.toReal_nonneg (by positivity)
        _ ≤ (B k * ((2 : ℝ) ^ ((k : ℝ) / 2) * s ^ (-(k : ℝ) / 2))) *
            (M * Real.exp (g * ‖ζ‖ ^ 2 * (t : ℝ)) *
              ((2 : ℝ) ^ h * (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)))) := by
          rw [hpp]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hhalf (by positivity)) (by positivity)
        _ = (B k * (2 : ℝ) ^ ((k : ℝ) / 2) * M * (2 : ℝ) ^ h) *
            Real.exp (g * ‖ζ‖ ^ 2 * (t : ℝ)) * s ^ (-(k : ℝ) / 2) *
              (s ^ (-h) + ‖ζ‖ * s ^ (-(d : ℝ) / 4)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcder (Real.exp_pos _).le)
            (Real.rpow_nonneg hs.le _)) (hnorm s hs)

end EinsteinFull.Blueprint
