import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Sharpness.SeedField
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Probability.Independence.Basic

/-!
# Translation ergodicity of a finite-range stationary law on `C(ℝᵈ, ℝ)`

Source: `sharp.example#seed-ergodicity` (`paper/main.tex:1572`). The proof is the finite-range
zero-one argument of `Localization.environmentLaw_translation_ergodic`, transported to the
compact-open Borel carrier `C(Vec d, ℝ)`:

* `zero_one_of_decoupling`: an abstract zero-one law for a probability measure that has a
  measure-dense family `𝒜` such that every `B ∈ 𝒜` is independent of one of its measure-preserving
  images `T i ⁻¹' B`, and `A` is almost surely invariant under every `T i`;
* the family of window events `windowEvents d` (events observable in a Euclidean-ball window) is a
  set algebra generating the Borel σ-algebra, and window events decouple under the shift of
  `(2 (n + 1) + 5) e₀`, by stationarity and independence of evaluation processes at separation `> 4`;
* `exists_ae_eq_const_of_zero_one`: a measurable function all of whose sublevel sets are
  `μ`-trivial is almost surely constant.
-/

open MeasureTheory
open scoped symmDiff

noncomputable section
namespace EinsteinFull

open EinsteinRelation

/-! ### Abstract zero-one law -/

theorem zero_one_of_decoupling {X ι : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (𝒜 : Set (Set X)) (h𝒜 : μ.MeasureDense 𝒜)
    (T : ι → X → X) (hTm : ∀ i, Measurable (T i)) (hTp : ∀ i, μ.map (T i) = μ)
    (hdec : ∀ B ∈ 𝒜, ∃ i, μ (B ∩ T i ⁻¹' B) = μ B * μ B)
    {A : Set X} (hA : MeasurableSet A)
    (hInv : ∀ i, ∀ᵐ ω ∂μ, (T i ω ∈ A ↔ ω ∈ A)) :
    μ A = 0 ∨ μ A = 1 := by
  let p : ℝ := (μ A).toReal
  have hsmall : ∀ ε : ℝ, 0 < ε → |p - p * p| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨B, hB, happrox⟩ := h𝒜.approx A hA (measure_ne_top μ A) ε hε
    obtain ⟨i, hind⟩ := hdec B hB
    let S : X → X := T i
    let E : Set X := A ∆ B
    let D : Set X := A ∩ (S ⁻¹' A)
    let C : Set X := B ∩ S ⁻¹' B
    let e : ℝ := (μ E).toReal
    let b : ℝ := (μ B).toReal
    let q : ℝ := (μ C).toReal
    have hBambient : MeasurableSet B := h𝒜.measurable B hB
    have hE : MeasurableSet E := hA.symmDiff hBambient
    have hT : Measurable S := hTm i
    have hTB : MeasurableSet (S ⁻¹' B) := hT hBambient
    have hC : MeasurableSet C := hBambient.inter hTB
    have hpreE : μ (S ⁻¹' E) = μ E := by
      rw [← Measure.map_apply hT hE, hTp i]
    have hApreAE : A =ᵐ[μ] S ⁻¹' A := by
      filter_upwards [hInv i] with ω hω
      exact propext hω.symm
    have hApreNull : μ (A ∆ (S ⁻¹' A)) = 0 :=
      measure_symmDiff_eq_zero_iff.mpr hApreAE
    have hADsubset : A ∆ D ⊆ A ∆ (S ⁻¹' A) := by
      intro ω hω
      change ω ∈ A ∆ (A ∩ (S ⁻¹' A)) at hω
      simp only [Set.mem_symmDiff, Set.mem_inter_iff] at *
      tauto
    have hADnull : μ (A ∆ D) = 0 := by
      apply le_antisymm
      · exact (measure_mono hADsubset).trans_eq hApreNull
      · exact bot_le
    have hDCsubset : D ∆ C ⊆ E ∪ S ⁻¹' E := by
      intro ω hω
      change ω ∈ (A ∩ (S ⁻¹' A)) ∆ (B ∩ (S ⁻¹' B)) at hω
      change ω ∈ (A ∆ B) ∪ S ⁻¹' (A ∆ B)
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage] at *
      tauto
    have hsetMeasure : μ (A ∆ C) ≤ μ E + μ (S ⁻¹' E) := by
      calc
        μ (A ∆ C) ≤ μ (A ∆ D) + μ (D ∆ C) := measure_symmDiff_le A D C
        _ = μ (D ∆ C) := by rw [hADnull, zero_add]
        _ ≤ μ E + μ (S ⁻¹' E) :=
          (measure_mono hDCsubset).trans (measure_union_le E (S ⁻¹' E))
    have hpreEreal : (μ (S ⁻¹' E)).toReal = e := by
      simp [e, hpreE]
    have hEreal : e < ε := by
      dsimp [e, E]
      exact ENNReal.toReal_lt_of_lt_ofReal happrox
    have hsetReal : (μ (A ∆ C)).toReal ≤ 2 * e := by
      calc
        (μ (A ∆ C)).toReal ≤ (μ E + μ (S ⁻¹' E)).toReal :=
          ENNReal.toReal_mono (by finiteness) hsetMeasure
        _ = e + e := by
          rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hpreEreal]
        _ = 2 * e := by ring
    have hAp : μ A ≤ 1 := prob_le_one
    have hBp : μ B ≤ 1 := prob_le_one
    have hp_nonneg : 0 ≤ p := ENNReal.toReal_nonneg
    have hp_le : p ≤ 1 := by
      dsimp [p]
      exact (ENNReal.toReal_mono (by simp) hAp).trans_eq (by norm_num)
    have hb_nonneg : 0 ≤ b := ENNReal.toReal_nonneg
    have hb_le : b ≤ 1 := by
      dsimp [b]
      exact (ENNReal.toReal_mono (by simp) hBp).trans_eq (by norm_num)
    have hpb : |p - b| ≤ e := by
      have h := (abs_measureReal_sub_le_measureReal_symmDiff
        (μ := μ) hA.nullMeasurableSet hBambient.nullMeasurableSet)
      exact h
    have hqfac : q = b * b := by
      show (μ (B ∩ S ⁻¹' B)).toReal = (μ B).toReal * (μ B).toReal
      rw [hind, ENNReal.toReal_mul]
    have hpc : |p - q| ≤ 2 * e := by
      have h := (abs_measureReal_sub_le_measureReal_symmDiff
        (μ := μ) hA.nullMeasurableSet hC.nullMeasurableSet)
      exact h.trans hsetReal
    have hbdiff : |b - p| ≤ ε := by
      rw [abs_sub_comm]
      exact hpb.trans (le_of_lt hEreal)
    have hsum : |b + p| ≤ 2 := by
      rw [abs_of_nonneg (add_nonneg hb_nonneg hp_nonneg)]
      linarith
    have hsquares : |b * b - p * p| ≤ 2 * ε := by
      calc
        |b * b - p * p| = |(b - p) * (b + p)| := by congr 1; ring
        _ = |b - p| * |b + p| := abs_mul _ _
        _ ≤ ε * 2 := mul_le_mul hbdiff hsum (abs_nonneg _) hε.le
        _ = 2 * ε := by ring
    have hdelta : |p - p * p| ≤ 2 * e + |b * b - p * p| := by
      calc
        |p - p * p| = |(p - q) + (q - p * p)| := by congr 1; ring
        _ ≤ |p - q| + |q - p * p| := abs_add_le _ _
        _ ≤ 2 * e + |q - p * p| := add_le_add hpc le_rfl
        _ = 2 * e + |b * b - p * p| := by rw [hqfac]
    nlinarith [hEreal, hsquares, hdelta]
  have hzero : p - p * p = 0 := by
    by_contra hne
    have hpos : 0 < |p - p * p| := abs_pos.mpr hne
    have hcontr := hsmall (|p - p * p| / 5) (by positivity)
    nlinarith
  have hp_cases : p = 0 ∨ p = 1 := by
    have hprod : p * (1 - p) = 0 := by nlinarith [hzero]
    rcases mul_eq_zero.mp hprod with hp | hp
    · exact Or.inl hp
    · exact Or.inr (by linarith)
  rcases hp_cases with hp | hp
  · left
    have hz : (μ A).toReal = 0 := by simpa [p] using hp
    rcases (ENNReal.toReal_eq_zero_iff (μ A)).mp hz with h | h
    · exact h
    · exact False.elim ((measure_ne_top μ A) h)
  · right
    exact (ENNReal.toReal_eq_one_iff (μ A)).mp (by simpa [p] using hp)

/-! ### Measurable functions with trivial sublevel sets are a.e. constant -/

theorem exists_ae_eq_const_of_zero_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (F : X → ℝ) (hF : Measurable F)
    (h01 : ∀ q : ℝ, μ {x | F x ≤ q} = 0 ∨ μ {x | F x ≤ q} = 1) :
    ∃ c : ℝ, ∀ᵐ x ∂μ, F x = c := by
  have hmeas : ∀ q : ℝ, MeasurableSet {x | F x ≤ q} := fun q => measurableSet_le hF measurable_const
  have hmono : ∀ {p q : ℝ}, p ≤ q → μ {x | F x ≤ p} ≤ μ {x | F x ≤ q} :=
    fun hpq => measure_mono (fun x hx => le_trans hx hpq)
  have hU : ∃ q : ℝ, μ {x | F x ≤ q} = 1 := by
    by_contra hne
    push_neg at hne
    have h0 : ∀ n : ℕ, μ {x | F x ≤ (n : ℝ)} = 0 := fun n => (h01 n).resolve_right (hne n)
    have hcov : (Set.univ : Set X) = ⋃ n : ℕ, {x | F x ≤ (n : ℝ)} := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_setOf_eq, true_iff]
      exact exists_nat_ge (F x)
    have : μ Set.univ = 0 := by
      rw [hcov]
      exact measure_iUnion_null h0
    simp at this
  have hL : ∃ m : ℝ, ∀ q : ℝ, μ {x | F x ≤ q} = 1 → m < q := by
    by_contra hne
    push_neg at hne
    have h1 : ∀ n : ℕ, μ {x | F x ≤ -(n : ℝ)} = 1 := by
      intro n
      obtain ⟨q, hq, hqn⟩ := hne (-(n : ℝ))
      exact le_antisymm prob_le_one (hq ▸ hmono hqn)
    have hcov : (Set.univ : Set X) = ⋃ n : ℕ, {x | F x ≤ -(n : ℝ)}ᶜ := by
      ext x
      simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_compl_iff, Set.mem_setOf_eq, true_iff,
        not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-F x)
      exact ⟨n, by linarith⟩
    have : μ Set.univ = 0 := by
      rw [hcov]
      exact measure_iUnion_null fun n => (prob_compl_eq_zero_iff (hmeas _)).2 (h1 n)
    simp at this
  obtain ⟨m, hm⟩ := hL
  obtain ⟨q₀, hq₀⟩ := hU
  let A : Set ℝ := {q | μ {x | F x ≤ q} = 1}
  have hAne : A.Nonempty := ⟨q₀, hq₀⟩
  have hAbdd : BddBelow A := ⟨m, fun q hq => (hm q hq).le⟩
  refine ⟨sInf A, ?_⟩
  have hup : ∀ k : ℕ, μ {x | F x ≤ sInf A + 1 / ((k : ℝ) + 1)} = 1 := by
    intro k
    obtain ⟨q, hq, hlt⟩ := exists_lt_of_csInf_lt hAne
      (lt_add_of_pos_right (sInf A) (by positivity : (0 : ℝ) < 1 / ((k : ℝ) + 1)))
    have hq1 : μ {x | F x ≤ q} = 1 := hq
    have hle := hmono hlt.le
    rw [hq1] at hle
    exact le_antisymm prob_le_one hle
  have hlow : ∀ k : ℕ, μ {x | F x ≤ sInf A - 1 / ((k : ℝ) + 1)} = 0 := by
    intro k
    refine (h01 _).resolve_right fun h1 => ?_
    have hmem : sInf A - 1 / ((k : ℝ) + 1) ∈ A := h1
    have := csInf_le hAbdd hmem
    have hpos : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hae_le : ∀ᵐ x ∂μ, F x ≤ sInf A := by
    have hk : ∀ᵐ x ∂μ, ∀ k : ℕ, F x ≤ sInf A + 1 / ((k : ℝ) + 1) := by
      rw [ae_all_iff]
      intro k
      have h := (prob_compl_eq_zero_iff (hmeas _)).2 (hup k)
      rw [measure_eq_zero_iff_ae_notMem] at h
      filter_upwards [h] with x hx
      simpa using hx
    filter_upwards [hk] with x hx
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    have := hx k
    linarith
  have hae_ge : ∀ᵐ x ∂μ, sInf A ≤ F x := by
    have hk : ∀ᵐ x ∂μ, ∀ k : ℕ, sInf A - 1 / ((k : ℝ) + 1) < F x := by
      rw [ae_all_iff]
      intro k
      have h := hlow k
      rw [measure_eq_zero_iff_ae_notMem] at h
      filter_upwards [h] with x hx
      simpa using hx
    filter_upwards [hk] with x hx
    by_contra hlt
    push_neg at hlt
    obtain ⟨k, hk'⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
    have := hx k
    linarith
  filter_upwards [hae_le, hae_ge] with x h1 h2 using le_antisymm h1 h2

/-! ### Window events on `C(ℝᵈ, ℝ)` -/

section Window

/-- The literal translate `y ↦ H (x + y)` of a continuous field. -/
def seedShift {d : ℕ} (x : Vec d) (H : C(Vec d, ℝ)) : C(Vec d, ℝ) :=
  ⟨fun y => H (x + y), H.continuous.comp (continuous_const.add continuous_id)⟩

/-- The restriction of a field to the open (sup-norm) ball of radius `R` about the origin. -/
def windowEval {d : ℕ} (R : ℝ) (H : C(Vec d, ℝ)) : Metric.ball (0 : Vec d) R → ℝ :=
  fun s => H s.1

/-- The σ-algebra of events observable in the window of radius `n + 1`. -/
abbrev windowSigma (d n : ℕ) : MeasurableSpace C(Vec d, ℝ) :=
  MeasurableSpace.comap (windowEval ((n : ℝ) + 1))
    (inferInstance : MeasurableSpace (Metric.ball (0 : Vec d) ((n : ℝ) + 1) → ℝ))

/-- Events observable in some bounded window. -/
def windowEvents (d : ℕ) : Set (Set C(Vec d, ℝ)) :=
  {s | ∃ n : ℕ, MeasurableSet[windowSigma d n] s}

theorem seedShift_continuous {d : ℕ} (x : Vec d) : Continuous (seedShift (d := d) x) := by
  have h := ContinuousMap.continuous_precomp
    (Z := ℝ) (⟨fun y : Vec d => x + y, continuous_const.add continuous_id⟩ : C(Vec d, Vec d))
  exact h

theorem windowSigma_mono (d : ℕ) {n m : ℕ} (h : n ≤ m) : windowSigma d n ≤ windowSigma d m := by
  have hR : ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).mpr h
    linarith
  let res : (Metric.ball (0 : Vec d) ((m : ℝ) + 1) → ℝ) →
      (Metric.ball (0 : Vec d) ((n : ℝ) + 1) → ℝ) :=
    fun g s => g ⟨s.1, Metric.ball_subset_ball hR s.2⟩
  have hres : Measurable res := measurable_pi_iff.mpr fun s => measurable_pi_apply _
  calc windowSigma d n
      = MeasurableSpace.comap (res ∘ windowEval ((m : ℝ) + 1)) inferInstance := rfl
    _ = MeasurableSpace.comap (windowEval ((m : ℝ) + 1)) (MeasurableSpace.comap res inferInstance) :=
        MeasurableSpace.comap_comp.symm
    _ ≤ windowSigma d m := MeasurableSpace.comap_mono hres.comap_le

theorem windowEvents_isSetAlgebra (d : ℕ) : IsSetAlgebra (windowEvents d) := by
  constructor
  · exact ⟨0, @MeasurableSet.empty _ (windowSigma d 0)⟩
  · rintro s ⟨n, hn⟩
    exact ⟨n, (hn : MeasurableSet[windowSigma d n] s).compl⟩
  · rintro s t ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨max n m, ?_⟩
    have h1 : MeasurableSet[windowSigma d (max n m)] s :=
      windowSigma_mono d (le_max_left n m) s hn
    have h2 : MeasurableSet[windowSigma d (max n m)] t :=
      windowSigma_mono d (le_max_right n m) t hm
    exact h1.union h2

theorem windowSigma_le_borel (d n : ℕ) : windowSigma d n ≤ borel C(Vec d, ℝ) := by
  letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
  haveI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  have h : Measurable (windowEval (d := d) ((n : ℝ) + 1)) :=
    measurable_pi_iff.mpr fun s => (continuous_eval_const s.1).measurable
  exact h.comap_le

theorem generateFrom_windowEvents_eq_borel (d : ℕ) :
    MeasurableSpace.generateFrom (windowEvents d) = borel C(Vec d, ℝ) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro s ⟨n, hn⟩
    exact windowSigma_le_borel d n s hn
  · letI : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
    haveI : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
    have h : @Measurable C(Vec d, ℝ) C(Vec d, ℝ) (MeasurableSpace.generateFrom (windowEvents d))
        (borel C(Vec d, ℝ)) id := by
      refine @measurable_continuousMap_of_evaluations C(Vec d, ℝ)
        (MeasurableSpace.generateFrom (windowEvents d)) d ℝ _ _ _ _ _ id ?_
      intro x
      obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
      have hx : x ∈ Metric.ball (0 : Vec d) ((n : ℝ) + 1) := by
        rw [mem_ball_zero_iff]
        linarith
      have hσ : windowSigma d n ≤ MeasurableSpace.generateFrom (windowEvents d) :=
        fun s hs => MeasurableSpace.measurableSet_generateFrom ⟨n, hs⟩
      have hm : @Measurable C(Vec d, ℝ) ℝ (windowSigma d n) _ (fun H => H x) :=
        (measurable_pi_apply (⟨x, hx⟩ : Metric.ball (0 : Vec d) ((n : ℝ) + 1))).comp
          (comap_measurable (windowEval ((n : ℝ) + 1)))
      exact hm.mono hσ le_rfl
    exact fun s hs => h hs

end Window

/-! ### Decoupling of window events and the zero-one law -/

section ZeroOne

variable {d : ℕ} [mC : MeasurableSpace C(Vec d, ℝ)] [BorelSpace C(Vec d, ℝ)]

private theorem abs_coord_le_euclideanNorm_seed (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

/-- Two points of the window ball and its translate by `(2 R + 5) e₀` are `> 4` apart. -/
theorem four_lt_euclideanNorm_window (hd : 0 < d) (R : ℝ) (y t : Vec d)
    (hy : y ∈ Metric.ball (0 : Vec d) R) (ht : t ∈ Metric.ball (0 : Vec d) R) :
    4 < euclideanNorm (y - ((2 * R + 5) • unitVector (⟨0, hd⟩ : Fin d) + t)) := by
  let i : Fin d := ⟨0, hd⟩
  have hyNorm : ‖y‖ < R := by simpa [dist_eq_norm] using Metric.mem_ball.mp hy
  have htNorm : ‖t‖ < R := by simpa [dist_eq_norm] using Metric.mem_ball.mp ht
  have hyC : |y i| < R := by
    have := (norm_le_pi_norm y i).trans_lt hyNorm
    simpa only [Real.norm_eq_abs] using this
  have htC : |t i| < R := by
    have := (norm_le_pi_norm t i).trans_lt htNorm
    simpa only [Real.norm_eq_abs] using this
  have hcoord : (y - ((2 * R + 5) • unitVector i + t)) i = y i - ((2 * R + 5) + t i) := by
    simp [unitVector]
  have habs := abs_coord_le_euclideanNorm_seed
    (y - ((2 * R + 5) • unitVector i + t)) i
  rw [hcoord] at habs
  have hneg := neg_le_abs (y i - ((2 * R + 5) + t i))
  have h1 := (abs_lt.mp hyC).2
  have h2 := (abs_lt.mp htC).1
  linarith

/-- Window events are independent of their translates by `(2 (n + 1) + 5) e₀`. -/
theorem seed_window_decoupling (hd : 0 < d) (μ : Measure C(Vec d, ℝ))
    (hstat : ∀ x : Vec d, μ.map (seedShift x) = μ)
    (hind : ∀ (S T : Type) (xs : S → Vec d) (ys : T → Vec d),
      (∀ s t, 4 < euclideanNorm (xs s - ys t)) →
      ProbabilityTheory.IndepFun (fun H : C(Vec d, ℝ) => fun s => H (xs s))
        (fun H : C(Vec d, ℝ) => fun t => H (ys t)) μ)
    (n : ℕ) (B : Set C(Vec d, ℝ)) (hB : MeasurableSet[windowSigma d n] B) :
    μ (B ∩ seedShift ((2 * ((n : ℝ) + 1) + 5) • unitVector (⟨0, hd⟩ : Fin d)) ⁻¹' B) =
      μ B * μ B := by
  obtain ⟨B', hB', rfl⟩ := hB
  let R : ℝ := (n : ℝ) + 1
  let x : Vec d := (2 * R + 5) • unitVector (⟨0, hd⟩ : Fin d)
  have hsep : ∀ s t : Metric.ball (0 : Vec d) R,
      4 < euclideanNorm ((fun s : Metric.ball (0 : Vec d) R => s.1) s -
        (fun t : Metric.ball (0 : Vec d) R => x + t.1) t) :=
    fun s t => four_lt_euclideanNorm_window hd R s.1 t.1 s.2 t.2
  have hxind := hind (Metric.ball (0 : Vec d) R) (Metric.ball (0 : Vec d) R)
    (fun s => s.1) (fun t => x + t.1) hsep
  have hfac := hxind.measure_inter_preimage_eq_mul B' B' hB' hB'
  have hevalm : Measurable (windowEval (d := d) R) :=
    measurable_pi_iff.mpr fun s => (continuous_eval_const s.1).measurable
  have hBm : MeasurableSet (windowEval (d := d) R ⁻¹' B') := hevalm hB'
  have hshm : Measurable (seedShift (d := d) x) := (seedShift_continuous x).measurable
  have hpre : μ (seedShift x ⁻¹' (windowEval (d := d) R ⁻¹' B')) =
      μ (windowEval (d := d) R ⁻¹' B') := by
    rw [← Measure.map_apply hshm hBm, hstat x]
  have h1 : μ ((fun (H : C(Vec d, ℝ)) (s : Metric.ball (0 : Vec d) R) => H s.1) ⁻¹' B') =
      μ (windowEval (d := d) R ⁻¹' B') := rfl
  have h2 : μ ((fun (H : C(Vec d, ℝ)) (t : Metric.ball (0 : Vec d) R) => H (x + t.1)) ⁻¹' B') =
      μ (windowEval (d := d) R ⁻¹' B') := hpre
  exact hfac.trans (congrArg₂ (· * ·) h1 h2)

/-- Zero-one law for a stationary, finite-range law on `C(ℝᵈ, ℝ)`. -/
theorem seedLaw_zero_one (hd : 0 < d) (μ : Measure C(Vec d, ℝ)) [IsProbabilityMeasure μ]
    (hstat : ∀ x : Vec d, μ.map (seedShift x) = μ)
    (hind : ∀ (S T : Type) (xs : S → Vec d) (ys : T → Vec d),
      (∀ s t, 4 < euclideanNorm (xs s - ys t)) →
      ProbabilityTheory.IndepFun (fun H : C(Vec d, ℝ) => fun s => H (xs s))
        (fun H : C(Vec d, ℝ) => fun t => H (ys t)) μ)
    {E : Set C(Vec d, ℝ)} (hE : MeasurableSet E)
    (hInv : ∀ x : Vec d, ∀ᵐ H ∂μ, (seedShift x H ∈ E ↔ H ∈ E)) :
    μ E = 0 ∨ μ E = 1 := by
  have hgen : mC = MeasurableSpace.generateFrom (windowEvents d) :=
    (BorelSpace.measurable_eq (α := C(Vec d, ℝ))).trans
      (generateFrom_windowEvents_eq_borel d).symm
  have h𝒜 : μ.MeasureDense (windowEvents d) :=
    Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite μ (windowEvents_isSetAlgebra d) hgen
  refine zero_one_of_decoupling μ (windowEvents d) h𝒜 (fun x : Vec d => seedShift x)
    (fun x => (seedShift_continuous x).measurable) hstat ?_ hE hInv
  rintro B ⟨n, hn⟩
  exact ⟨(2 * ((n : ℝ) + 1) + 5) • unitVector (⟨0, hd⟩ : Fin d),
    seed_window_decoupling hd μ hstat hind n B hn⟩

end ZeroOne

end EinsteinFull
