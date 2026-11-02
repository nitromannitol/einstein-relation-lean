import EinsteinFull.Calculus.C3ConditionalFluxBlocks
import EinsteinFull.Calculus.C3FluxAnnularLocalization
import EinsteinFull.Calculus.K3BlockCondExpSquareSums
import EinsteinFull.Calculus.K5FixedAnnularReconstruction
import EinsteinFull.Calculus.K7AnnularConstants
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks

/-! Fixed-data assembly for the actual conditional flux blocks. Structural witnesses
are supplied together by the block/localization producer, rather than selected from
unrelated existential estimates. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Centering an actual block costs at most a factor of two in its finite-p norm. -/
theorem c6_centered_block_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) :
    (eLpNorm (centeredComplexLp Q f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      2 * (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let := reducedLaw_probability Q
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  let m : ℂ := ∫ ω, f ω ∂reducedLaw Q
  have hm : eLpNorm (fun _ : FieldPair d => m) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_const _ (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hq))
      (NeZero.ne (reducedLaw Q)), measure_univ, ENNReal.one_rpow, mul_one]
    exact (enorm_integral_le_lintegral_enorm _).trans
      ((eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm.le.trans
        (eLpNorm_le_eLpNorm_of_exponent_le hq))
  have hsub := EinsteinFull.Calculus.K5.toReal_eLpNorm_sub_le hq hf
    (memLp_const m)
  rw [eLpNorm_congr_ae (coeFn_centeredComplexLp Q f)]
  exact hsub.trans (by
    have hm' := ENNReal.toReal_mono hf.eLpNorm_ne_top hm
    change _ ≤ _ at hm'
    linarith)

/-- Assemble contraction, buffered joint-field coloring and annular reconstruction
for a single supplied family of actual blocks. The localization estimate is a
fixed-data input; the annular series remains explicit for structural absorption. -/
theorem c6_actual_conditional_blocks_reconstruction {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {p r R F L τ : ℝ}
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hR : 0 ≤ R)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hτ : 0 < τ)
    (B : (Fin d → ℤ) → Lp ℂ 2 (reducedLaw Q))
    (w : (Fin d → ℤ) → ℝ) (hw : ∀ z, 0 ≤ w z)
    (hB : ∀ z, MemLp (B z : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q))
    (hBnorm : ∀ z, (eLpNorm (B z : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ F * w z) :
    let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j : ℝ)
    let X := fun z => (centeredComplexLp Q (B z) : FieldPair d → ℂ)
    let CE := fun (n : ℕ) z => (reducedLaw Q)[X z | localSigma
      {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r}]
    let A := fun (n : ℕ) z => CE (n + 1) z - CE n z
    let N := fun f : FieldPair d → ℂ =>
      (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
    (∀ n z, N (X z - CE n z) ≤ L * Real.exp (-4 ^ n * τ) * w z) →
    (∀ z, MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q) ∧
      MemLp (CE 0 z) (ENNReal.ofReal p) (reducedLaw Q) ∧ N (CE 0 z) ≤ N (X z)) ∧
    Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * τ)) ∧
    (∀ n z, MemLp (X z - CE n z) (ENNReal.ofReal p) (reducedLaw Q) ∧
      N (X z - CE n z) ≤ L * Real.exp (-4 ^ n * τ) * w z) ∧
    (∀ S : Finset (Fin d → ℤ), N (∑ z ∈ S, CE 0 z) ≤
      EinsteinFull.Calculus.K3.blockColorConst d p r₀ R *
        Real.sqrt (∑ z ∈ S, (N (CE 0 z)) ^ 2)) ∧
    (∀ (n : ℕ) (S : Finset (Fin d → ℤ)), N (∑ z ∈ S, A n z) ≤
      EinsteinFull.Calculus.K3.blockColorConst d p r₀ R *
        2 ^ ((n : ℝ) * (d : ℝ) / 2) * Real.sqrt (∑ z ∈ S, (N (A n z)) ^ 2)) ∧
    ∀ S : Finset (Fin d → ℤ),
      MemLp ((∑ z ∈ S, centeredComplexLp Q (B z) : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      N ((∑ z ∈ S, centeredComplexLp Q (B z) : Lp ℂ 2 (reducedLaw Q)) : FieldPair d → ℂ) ≤
        EinsteinFull.Calculus.K3.blockColorConst d p r₀ R *
        (2 * F + 2 * L * ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
          Real.exp (-4 ^ n * τ)) * Real.sqrt (∑ z ∈ S, w z ^ 2) := by
  intro center X CE A N hloc
  let := reducedLaw_probability Q
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp1
  have hX : ∀ z, MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q) :=
    fun z => carverS_memLp_centered Q (B z) (hB z)
  have hCE : ∀ n z, MemLp (CE n z) (ENNReal.ofReal p) (reducedLaw Q) :=
    fun n z => (hX z).condExp hq
  have hcon : ∀ z, N (CE 0 z) ≤ N (X z) := fun z =>
    ENNReal.toReal_mono (hX z).eLpNorm_ne_top (eLpNorm_condExp_le_eLpNorm _ hq)
  have hXnorm : ∀ z, N (X z) ≤ (2 * F) * w z := by
    intro z
    exact (c6_centered_block_norm_le Q (B z) hp1 (hB z)).trans
      (by have h := hBnorm z; linarith)
  obtain ⟨hbase, hann⟩ := EinsteinFull.Calculus.K3.block_condExp_square_sums
    Q hp hr hR X hX (fun z => integral_centeredComplexLp Q (B z))
  have hcolor : 0 ≤ EinsteinFull.Calculus.K3.blockColorConst d p r₀ R := by
    unfold EinsteinFull.Calculus.K3.blockColorConst EinsteinFull.Calculus.K1.lpSqConst
      Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have hp0 : 0 ≤ p := le_trans (by norm_num) hp
    have hr₀ : 0 ≤ r₀ := by linarith [Q.range_parameter]
    positivity
  refine ⟨fun z => ⟨hX z, hCE 0 z, hcon z⟩,
    EinsteinFull.Calculus.K4.summable_two_rpow_mul_exp_neg_four_pow d hτ,
    fun n z => ⟨(hX z).sub (hCE n z), hloc n z⟩, hbase, hann, ?_⟩
  intro S
  obtain ⟨hmem, hnorm⟩ := EinsteinFull.Calculus.K5.fixed_data_annular_reconstruction hp1 d X CE w
    (2 * F) L τ (EinsteinFull.Calculus.K3.blockColorConst d p r₀ R)
    (mul_nonneg (by norm_num) hF) hL hτ hcolor hw hX hCE hcon hXnorm hloc hbase hann S
  have hae := Lp.coeFn_finsetSum S (fun z => centeredComplexLp Q (B z))
  refine ⟨hmem.ae_eq hae.symm, ?_⟩
  change (eLpNorm _ _ _).toReal ≤ _
  rw [eLpNorm_congr_ae hae]
  exact hnorm

/-- K7's scalar domination absorbs the annular series into the precise final
block rate, with an explicit structural enlargement of the derivative constant. -/
theorem c6_annular_reconstruction_constant (d : ℕ) {η κ Cloc : ℝ}
    (hη : 0 < η) (hκ : κ < 1) (hCloc : 1 ≤ Cloc) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t → ∀ z : ℝ, 0 ≤ z →
      z * Real.sqrt t ≤ t ^ (η / 4) → ∀ s : ℝ, 0 < s →
      ∀ (k Lb : ℕ) (K growth Cder Ccolor : ℝ),
      1 ≤ K → 0 ≤ growth → 0 ≤ Cder → 0 ≤ Ccolor →
      let F := K * Real.exp (growth * z ^ 2 * t / 2) *
        t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (t ^ (1 / 2 + η)) ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
        (1 + t / s) ^ Lb
      let L := (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) *
        (t ^ (1 / 2 + η)) ^ d * s ^ (-(k : ℝ) / 2)
      let A := ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * ((1 / Cloc) / 2))
      Ccolor * (2 * (Cder * F) + 2 * (Cder * L) *
        ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
          Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) ≤
        (2 * Ccolor * Cder * (1 + A)) * F := by
  obtain ⟨T, hT1, hT⟩ := EinsteinFull.Calculus.K7.annular_constant_domination d hη hκ hCloc
  refine ⟨T, hT1, fun t ht z hz hzt s hs k Lb K growth Cder Ccolor hK hg hCder hCcolor => ?_⟩
  intro F L A
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hC0 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
  have hτ : 1 / Cloc ≤ t ^ (2 * η) / Cloc :=
    div_le_div_of_nonneg_right (Real.one_le_rpow ht1 (by positivity)) hC0.le
  have htail := EinsteinFull.Calculus.K7.annular_series_shift d (one_div_pos.mpr hC0) hτ
  have hdom : L * Real.exp (-(t ^ (2 * η) / Cloc) / 2) ≤ F :=
    hT t ht z hz hzt s hs k Lb K growth hK hg
  have hA : 0 ≤ A := tsum_nonneg fun _ =>
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.exp_nonneg _)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hLsum : L * (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) ≤ A * F := by
    calc _ ≤ L * (Real.exp (-(t ^ (2 * η) / Cloc) / 2) * A) :=
        mul_le_mul_of_nonneg_left htail hL
      _ = (L * Real.exp (-(t ^ (2 * η) / Cloc) / 2)) * A := by ring
      _ ≤ F * A := mul_le_mul_of_nonneg_right hdom hA
      _ = A * F := by ring
  calc _ = (2 * Ccolor * Cder) * (F + L *
      ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc))) := by ring
    _ ≤ (2 * Ccolor * Cder) * (F + A * F) :=
      mul_le_mul_of_nonneg_left (by linarith only [hLsum]) (by positivity)
    _ = _ := by ring


/-- Uniform final-rate assembly on one actual block family. The enlarged
constant and time threshold depend only on the displayed structural data. -/
theorem c6_actual_conditional_blocks_final_rate (d : ℕ) {η κ Cloc : ℝ}
    (hη : 0 < η) (hκ : κ < 1) (hCloc : 1 ≤ Cloc) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
      {p R : ℝ}, 2 ≤ p → 0 ≤ R → ∀ t : ℝ, T ≤ t →
      ∀ z : ℝ, 0 ≤ z → z * Real.sqrt t ≤ t ^ (η / 4) →
      ∀ s : ℝ, 0 < s → ∀ (k Lb : ℕ) (K growth Cder : ℝ),
      1 ≤ K → 0 ≤ growth → 0 ≤ Cder →
      ∀ (B : (Fin d → ℤ) → Lp ℂ 2 (reducedLaw Q))
        (w : (Fin d → ℤ) → ℝ), (∀ u, 0 ≤ w u) →
      (∀ u, MemLp (B u : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) →
      let r := t ^ (1 / 2 + η)
      let F := K * Real.exp (growth * z ^ 2 * t / 2) *
        t ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) *
        s ^ (-(k : ℝ) / 2) * (1 + t / s) ^ Lb
      let center := fun (u : Fin d → ℤ) (j : Fin d) => r * (u j : ℝ)
      let X := fun u => (centeredComplexLp Q (B u) : FieldPair d → ℂ)
      let CE := fun (n : ℕ) u => (reducedLaw Q)[X u | localSigma
        {y : Vec d | euclideanNorm (y - center u) < R * 2 ^ (n + 1) * r}]
      let A := fun (n : ℕ) u => CE (n + 1) u - CE n u
      let N := fun f : FieldPair d → ℂ =>
        (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Ccolor := EinsteinFull.Calculus.K3.blockColorConst d p r₀ R
      let series := ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * ((1 / Cloc) / 2))
      let C := max 1 (max Cder (max Ccolor (2 * Ccolor * Cder * (1 + series))))
      (∀ u, N (B u) ≤ (Cder * F) * w u) →
      (∀ n u, N (X u - CE n u) ≤
        Cder * (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t -
          4 ^ n * t ^ (2 * η) / Cloc) * r ^ d * s ^ (-(k : ℝ) / 2) * w u) →
      (∀ u, MemLp (X u) (ENNReal.ofReal p) (reducedLaw Q) ∧
        MemLp (CE 0 u) (ENNReal.ofReal p) (reducedLaw Q) ∧ N (CE 0 u) ≤ N (X u)) ∧
      Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
        Real.exp (-4 ^ n * t ^ (2 * η) / Cloc)) ∧
      (∀ n u, MemLp (X u - CE n u) (ENNReal.ofReal p) (reducedLaw Q) ∧
        N (X u - CE n u) ≤
          C * (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t -
            4 ^ n * t ^ (2 * η) / Cloc) * r ^ d * s ^ (-(k : ℝ) / 2) * w u) ∧
      (∀ S : Finset (Fin d → ℤ), N (∑ u ∈ S, CE 0 u) ≤
        C * Real.sqrt (∑ u ∈ S, (N (CE 0 u)) ^ 2)) ∧
      (∀ (n : ℕ) (S : Finset (Fin d → ℤ)), N (∑ u ∈ S, A n u) ≤
        C * 2 ^ ((n : ℝ) * (d : ℝ) / 2) * Real.sqrt (∑ u ∈ S, (N (A n u)) ^ 2)) ∧
      ∀ S : Finset (Fin d → ℤ),
        MemLp ((∑ u ∈ S, centeredComplexLp Q (B u) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        N ((∑ u ∈ S, centeredComplexLp Q (B u) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) ≤ C * F * Real.sqrt (∑ u ∈ S, w u ^ 2) := by
  obtain ⟨T, hT1, hT⟩ := c6_annular_reconstruction_constant d hη hκ hCloc
  refine ⟨T, hT1, ?_⟩
  intro Λ r₀ Q p R hp hR t ht z hz hzt s hs k Lb K growth Cder hK hg hCder B w hw hB
    r F center X CE A N Ccolor series C hBnorm hloc
  let L := (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t) *
    r ^ d * s ^ (-(k : ℝ) / 2)
  have ht1 : 1 ≤ t := hT1.trans ht
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hr : 1 ≤ r := Real.one_le_rpow ht1 (by positivity)
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hC0 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hτ : 0 < t ^ (2 * η) / Cloc := div_pos (Real.rpow_pos_of_pos ht0 _) hC0
  have hcolor : 0 ≤ Ccolor := by
    dsimp only [Ccolor]
    unfold EinsteinFull.Calculus.K3.blockColorConst EinsteinFull.Calculus.K1.lpSqConst
      Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have hp0 : 0 ≤ p := le_trans (by norm_num) hp
    have hr₀ : 0 ≤ r₀ := by linarith [Q.range_parameter]
    positivity
  have hCderC : Cder ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hcolorC : Ccolor ≤ C :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hsumC : 2 * Ccolor * Cder * (1 + series) ≤ C :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hloc' : ∀ n u, N (X u - CE n u) ≤
      (Cder * L) * Real.exp (-4 ^ n * (t ^ (2 * η) / Cloc)) * w u := by
    intro n u
    calc _ ≤ _ := hloc n u
      _ = _ := by
        dsimp only [L]
        rw [show Cloc * z ^ 2 * t - 4 ^ n * t ^ (2 * η) / Cloc =
          Cloc * z ^ 2 * t + (-4 ^ n * (t ^ (2 * η) / Cloc)) by ring,
          Real.exp_add]
        ring
  obtain ⟨hcon, htail, herr, hbase, hann, hsum⟩ :=
    c6_actual_conditional_blocks_reconstruction Q hp hr hR
      (mul_nonneg hCder hF) (mul_nonneg hCder hL) hτ B w hw hB hBnorm hloc'
  refine ⟨hcon, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_div_assoc] using htail
  · intro n u
    refine ⟨(herr n u).1, (hloc n u).trans ?_⟩
    have hwu := hw u
    let M := (2 + t) ^ Cloc * Real.exp (Cloc * z ^ 2 * t -
      4 ^ n * t ^ (2 * η) / Cloc) * r ^ d * s ^ (-(k : ℝ) / 2) * w u
    have hM : 0 ≤ M := by dsimp only [M]; positivity
    simpa only [M, mul_assoc] using mul_le_mul_of_nonneg_right hCderC hM
  · intro S
    exact (hbase S).trans (mul_le_mul_of_nonneg_right hcolorC (Real.sqrt_nonneg _))
  · intro n S
    exact (hann n S).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcolorC (Real.rpow_nonneg (by norm_num) _))
      (Real.sqrt_nonneg _))
  · intro S
    refine ⟨(hsum S).1, (hsum S).2.trans ?_⟩
    have habs := hT t ht z hz hzt s hs k Lb K growth Cder Ccolor hK hg hCder hcolor
    calc _ ≤ (2 * Ccolor * Cder * (1 + series)) * F *
          Real.sqrt (∑ u ∈ S, w u ^ 2) :=
        mul_le_mul_of_nonneg_right habs (Real.sqrt_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsumC hF) (Real.sqrt_nonneg _)


/-- The actual flux blocks satisfy the independent-block estimates, with the
structural constants and flux witnesses shared by the block and localization bounds. -/
theorem c6_node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocks_of_deps :
    node_e_u3A_flux_u2D_blockStmt → node_e_u3A_forced_u2D_localityStmt →
    node_l_u3A_forced_u2D_flux_u23_parametersStmt →
    node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 := by
  intro hblock hlocal hparameters d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ0, hκ, hCenv, hηeq, hη₀, hpdata⟩ :=
    carverS_actual_block_annular_localization_with_block_bound hblock hlocal hparameters d hd D
  refine ⟨κ, η, η₀, Cenv, Lblock, hκ0, hκ, hCenv, hηeq, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cloc, Cder, hgrowth₀, ht₀, hCloc, hCder, hdata⟩ := hpdata p hp
  have hη : 0 < η := by rw [hηeq]; positivity
  obtain ⟨T, hT1, hT⟩ := c6_actual_conditional_blocks_final_rate d hη
    (lt_trans hκ (by norm_num)) hCloc
  let color := EinsteinFull.Calculus.K3.blockColorConst d p D.dependenceRange
    (2 * Real.sqrt (d : ℝ) + 2)
  let series := ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
    Real.exp (-4 ^ n * ((1 / Cloc) / 2))
  let Cnew := fun k => max 1
    (max (Cder k) (max color (2 * color * Cder k * (1 + series))))
  refine ⟨growth₀, max t₀ T, Cloc, Cnew, hgrowth₀,
    ht₀.trans (le_max_left _ _), hCloc, (fun _ => le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hrest⟩ := hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hforce growth K hg hK hendpoint hendpointNorm s hs1 hs k dirs
    r R kernel W χ hχ hχcompact hχsupport hχbound hχgrad B hpart x j center X CE A N
  have hblockloc := hrest t ((max_le_iff.mp ht).1) hforce growth K hg hK
    hendpoint hendpointNorm s hs1 hs k dirs χ hχ hχcompact hχsupport hχbound hχgrad
  have hw : ∀ u : Fin d → ℤ, 0 ≤ W x (center u) := by
    intro u
    apply Real.sSup_nonneg
    rintro _ ⟨y, hy, rfl⟩
    positivity
  have hB := fun u : Fin d → ℤ => (hblockloc.1 x (center u) j).1
  have hBnorm := fun u : Fin d → ℤ => (hblockloc.1 x (center u) j).2
  have hloc := fun n u => ((hblockloc.2 hpart x j).2 n u).2
  have hfinal := hT Q hp (show 0 ≤ R by dsimp only [R]; positivity)
    (t : ℝ) ((max_le_iff.mp ht).2) ‖ζ‖ (norm_nonneg _)
    (by simpa only [← hη₀] using hforce) s hs k (Lblock k) K growth (Cder k) hK
    (le_trans (le_of_lt hgrowth₀) hg) (le_trans zero_le_one (hCder k))
    (fun u => B x (center u) j) (fun u => W x (center u)) hw hB
    (by simpa only [mul_assoc] using hBnorm) hloc
  obtain ⟨hcon, htail, herr, hbase, hann, hsum⟩ := hfinal
  refine ⟨hcon, htail, ?_, ?_, ?_, ?_⟩
  · simpa only [r, R, center, X, CE, A, N, Cnew, color, series, mul_assoc] using herr
  · simpa only [r, R, center, X, CE, A, N, Cnew, color, series, mul_assoc] using hbase
  · simpa only [r, R, center, X, CE, A, N, Cnew, color, series, mul_assoc] using hann
  · intro S
    have hae := Lp.coeFn_finsetSum S (fun u => centeredComplexLp Q (B x (center u) j))
    refine ⟨(hsum S).1.ae_eq hae, ?_⟩
    rw [← eLpNorm_congr_ae hae]
    simpa only [Cnew, color, series, mul_assoc] using (hsum S).2

end EinsteinFull.Blueprint
