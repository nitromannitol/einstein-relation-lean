import EinsteinFull.Calculus.C9TubeSignedDyadicGainTransport
import EinsteinFull.Calculus.SbxBBackwardCylinderCoverR12
import EinsteinFull.Calculus.SbxBPositiveNormNormalizationR11
import EllipticRegularity.Parabolic.WeakHarnack.MeasuresCylinders

open EinsteinRelation EinsteinFull.External.Source.GMP MeasureTheory Filter
open scoped ENNReal

namespace EinsteinFull.Calculus

/-- A backward cylinder centered near the terminal time stays inside a buffered
cylinder. The top is clipped to zero, so the estimate also applies arbitrarily
close to the common terminal time. -/
@[nolint unusedArguments]
theorem sbxB_backwardCylinder_buffer {d : ℕ}
    (b b' R R' r : ℝ) (q : ℝ × Vec d)
    (hr : 0 < r) (htgap : r ^ 2 ≤ b' - b) (hsgap : 2 * r ≤ R - R')
    (hqtime : b' < q.1 ∧ q.1 ≤ 0) (hqspace : q.2 ∈ sourceBall (0 : Vec d) R') :
    Set.Ioo (min 0 (q.1 + r ^ 2 / 8) - r ^ 2)
        (min 0 (q.1 + r ^ 2 / 8)) ×ˢ sourceBall q.2 (2 * r) ⊆
      Set.Ioc b 0 ×ˢ sourceBall (0 : Vec d) R := by
  intro z hz
  have ht : min 0 (q.1 + r ^ 2 / 8) ≤ 0 := min_le_left _ _
  have ht' : q.1 ≤ min 0 (q.1 + r ^ 2 / 8) :=
    le_min hqtime.2 (by nlinarith [sq_nonneg r])
  have hs : euclideanNorm (z.2 - q.2) < 2 * r := hz.2
  have hq : euclideanNorm (q.2 - 0) < R' := hqspace
  have htri := TimeChange.euclideanNorm_add_le (z.2 - q.2) (q.2 - 0)
  have heq : z.2 - 0 = (z.2 - q.2) + (q.2 - 0) := by abel
  refine ⟨⟨by linarith [hz.1.1], le_trans (le_of_lt hz.1.2) ht⟩, ?_⟩
  change euclideanNorm (z.2 - 0) < R
  rw [heq]
  linarith

/-- Away from the null terminal time, the center belongs to the smaller
backward cylinder with the clipped terminal time. -/
theorem sbxB_backwardCylinder_center (t r : ℝ) (ht : t < 0) (hr : 0 < r) :
    t ∈ Set.Ioo (min 0 (t + r ^ 2 / 8) - r ^ 2 / 4)
      (min 0 (t + r ^ 2 / 8)) := by
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
  constructor
  · have hmin : t ≤ min 0 (t + r ^ 2 / 8) := le_min (le_of_lt ht) (by linarith)
    have hmax : min 0 (t + r ^ 2 / 8) ≤ t + r ^ 2 / 8 := min_le_right _ _
    linarith
  · exact lt_min ht (by linarith)

/-- Internal quadratic nets cover any bounded negative-time set by smaller
backward cylinders; their larger cylinders fit any prescribed buffer. -/
theorem sbxB_backwardCylinder_cover_of_scale (d : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C B : ℕ, ∀ (n : ℕ) (A : Set (ℝ × Vec d)) (b b' R R' r : ℝ),
      (∀ q ∈ A, ‖q‖ ≤ 1) →
      (∀ q ∈ A, b' < q.1 ∧ q.1 < 0 ∧ q.2 ∈ sourceBall (0 : Vec d) R') →
      0 < r → r ^ 2 ≤ b' - b → 2 * r ≤ R - R' →
      δ * (1 / 4 : ℝ) ^ n ≤ (r / 2) ^ 2 / 4 →
      ((d : ℝ) + 1) * (δ * (1 / 4 : ℝ) ^ n) ≤ (r / 2) / 2 →
      ∃ F : Finset (ℝ × Vec d), F.card ≤ C * B ^ n ∧
        (∀ q ∈ F, Set.Ioo (min 0 (q.1 + r ^ 2 / 8) - r ^ 2)
          (min 0 (q.1 + r ^ 2 / 8)) ×ˢ sourceBall q.2 (2 * r) ⊆
            Set.Ioc b 0 ×ˢ sourceBall (0 : Vec d) R) ∧
        ∀ x ∈ A, ∃ q ∈ F,
          x ∈ Set.Ioo (min 0 (q.1 + r ^ 2 / 8) - r ^ 2 / 4)
            (min 0 (q.1 + r ^ 2 / 8)) ×ˢ sourceBall q.2 (r / 2) := by
  obtain ⟨C, B, hnet⟩ := c9_uniform_quadratic_internal_nets (E := ℝ × Vec d) δ hδ
  refine ⟨C, B, ?_⟩
  intro n A b b' R R' r hbounded hA hr htgap hsgap htime hspace
  obtain ⟨F, hcard, hcenters, hcover⟩ := hnet n A hbounded
  refine ⟨F, hcard, ?_, ?_⟩
  · intro q hq
    have hq' := hA q (hcenters q hq)
    exact sbxB_backwardCylinder_buffer b b' R R' r q hr htgap hsgap
      ⟨hq'.1, le_of_lt hq'.2.1⟩ hq'.2.2
  · intro x hx
    obtain ⟨q, hq, hdist⟩ := hcover x hx
    have hsmall := c9_product_metric_ball_in_inner_parabolic_cylinder d x q
      (r / 2) (δ * (1 / 4 : ℝ) ^ n) htime hspace hdist
    have hx0 := (hA x hx).2.1
    have htop : x.1 < min 0 (q.1 + r ^ 2 / 8) := by
      apply lt_min hx0
      nlinarith [hsmall.1.2, sq_nonneg r]
    have hbottom : min 0 (q.1 + r ^ 2 / 8) - r ^ 2 / 4 < x.1 := by
      have htop' := min_le_right 0 (q.1 + r ^ 2 / 8)
      nlinarith [hsmall.1.1, sq_nonneg r]
    refine ⟨q, hq, ⟨⟨hbottom, htop⟩, ?_⟩⟩
    change euclideanNorm (x.2 - q.2) < r / 2
    have hs : euclideanNorm (x.2 - q.2) < (r / 2) / 2 := hsmall.2
    linarith

/-- The terminal time of a backward cylinder is Lebesgue-null. -/
theorem sbxB_backward_restrict_Ioo_eq_Ioc (d : ℕ) (a b : ℝ)
    (S : Set (Vec d)) :
    volume.restrict (Set.Ioo a b ×ˢ S) =
      volume.restrict (Set.Ioc a b ×ˢ S) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_restrict,
    restrict_Ioo_eq_restrict_Ioc]

/-- On the nonnegative part of a field the regularizing clip is inactive. -/
theorem sbxB_inverse_clip_eq_ae {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (u : X → ℝ) (ε : ℝ)
    (hu : ∀ᵐ x ∂μ, 0 ≤ u x) :
    (fun x => 1 / max ε (u x + ε)) =ᵐ[μ] (fun x => 1 / (u x + ε)) := by
  filter_upwards [hu] with x hx
  rw [max_eq_right (by linarith)]

/-- The normalized negative cylinder written in time-first coordinates. -/
theorem sbxB_negative_normalized_norm (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (p : ℝ≥0∞)
    (f : ℝ × Vec d → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
        (PDE.Parabolic.WeakHarnack.negCyl d σ)) =
    eLpNorm f p ((volume (PDE.Parabolic.WeakHarnack.negCyl d 1))⁻¹ •
      volume.restrict (Set.Ioc (-5 / 16 - (σ - 1 / 2) / 16) 0 ×ˢ
        sourceBall 0 (5 / 8 + (σ - 1 / 2) / 4))) := by
  have hm : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioc (-5 / 16 - (σ - 1 / 2) / 16) 0 ×ˢ
        sourceBall 0 (5 / 8 + (σ - 1 / 2) / 4))) =
      volume.restrict (PDE.Parabolic.WeakHarnack.negCyl d σ) := by
    rw [PDE.Parabolic.WeakHarnack.negCyl,
      c8_sourceBall_eq_euclideanBall 0 (by linarith)]
    simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]
  have hf : MeasurableEmbedding (Prod.swap : ℝ × Vec d → Vec d × ℝ) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [PDE.Parabolic.WeakHarnack.cylMeasure_restrict
      (PDE.Parabolic.WeakHarnack.measurableSet_negCyl _)
      (PDE.Parabolic.WeakHarnack.negCyl_mono hσ hσ1),
    ← hm, ← Measure.map_smul _ hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- The normalized inner negative cylinder written in time-first coordinates. -/
theorem sbxB_negative_inner_normalized_norm (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (p : ℝ≥0∞)
    (f : ℝ × Vec d → ℝ) :
    eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
        (PDE.Parabolic.WeakHarnack.negCylInner d σ)) =
    eLpNorm f p ((volume (PDE.Parabolic.WeakHarnack.negCylInner d 1))⁻¹ •
      volume.restrict (Set.Ioc (-1 / 4 - (σ - 1 / 2) / 8) 0 ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 4))) := by
  have hm : Measure.map (Prod.swap : ℝ × Vec d → Vec d × ℝ)
      (volume.restrict (Set.Ioc (-1 / 4 - (σ - 1 / 2) / 8) 0 ×ˢ
        sourceBall 0 (1 / 2 + (σ - 1 / 2) / 4))) =
      volume.restrict (PDE.Parabolic.WeakHarnack.negCylInner d σ) := by
    rw [PDE.Parabolic.WeakHarnack.negCylInner,
      c8_sourceBall_eq_euclideanBall 0 (by linarith)]
    simp only [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.prod_swap]
  have hf : MeasurableEmbedding (Prod.swap : ℝ × Vec d → Vec d × ℝ) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  rw [PDE.Parabolic.WeakHarnack.cylMeasure_restrict
      (PDE.Parabolic.WeakHarnack.measurableSet_negCylInner _)
      (PDE.Parabolic.WeakHarnack.negCylInner_mono hσ hσ1),
    ← hm, ← Measure.map_smul _ hf.measurable.aemeasurable,
    hf.eLpNorm_map_measure]
  rfl

/-- Both normalized negative families in the time-first presentation. -/
theorem sbxB_negative_family_normalized_norm (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (inner : Bool) (p : ℝ≥0∞)
    (f : ℝ × Vec d → ℝ) :
    let S : ℝ → Set (Vec d × ℝ) := fun s =>
      if inner then PDE.Parabolic.WeakHarnack.negCylInner d s
      else PDE.Parabolic.WeakHarnack.negCyl d s
    let A : ℝ → Set (ℝ × Vec d) := fun s => {z | (z.2, z.1) ∈ S s}
    eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) p
      ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ)) =
    eLpNorm f p ((volume (S 1))⁻¹ • volume.restrict (A σ)) := by
  cases inner
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← sbxB_backCylinder_eq_neg d σ hσ]
    exact sbxB_negative_normalized_norm d σ hσ hσ1 p f
  · simp only [↓reduceIte]
    rw [← sbxB_backCylinder_eq_negInner d σ hσ]
    exact sbxB_negative_inner_normalized_norm d σ hσ hσ1 p f

/-- A finite cover controls the sum of local positive-order norm moments. -/
theorem sbxB_eLpNorm_rpow_le_finset_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ)
    (A : Set X) (F : Finset I) (V : I → Set X)
    (hfA : AEStronglyMeasurable f (μ.restrict A))
    (hfV : ∀ i ∈ F, AEStronglyMeasurable f (μ.restrict (V i)))
    (q : ℝ) (hq : 0 < q)
    (hcover : A ⊆ ⋃ i ∈ F, V i) :
    eLpNorm f (ENNReal.ofReal q) (μ.restrict A) ^ q ≤
      ∑ i ∈ F, eLpNorm f (ENNReal.ofReal q) (μ.restrict (V i)) ^ q := by
  classical
  have hid (S : Set X) (hfS : AEStronglyMeasurable f (μ.restrict S)) :
      eLpNorm f (ENNReal.ofReal q) (μ.restrict S) ^ q =
      ∫⁻ x in S, ‖f x‖ₑ ^ q ∂μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
      (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top
      hfS, ENNReal.toReal_ofReal hq.le,
      ← ENNReal.rpow_mul]
    have hh : 1 / q * q = 1 := by field_simp
    rw [hh, ENNReal.rpow_one]
  rw [hid A hfA]
  calc
    _ ≤ ∑ i ∈ F, ∫⁻ x in V i, ‖f x‖ₑ ^ q ∂μ :=
      c9_lintegral_le_finset_cover μ (fun x => ‖f x‖ₑ ^ q) A F V hcover
    _ = _ := Finset.sum_congr rfl fun i hi => (hid (V i) (hfV i hi)).symm

/-- Uniform local bounds combine over a finite cover at positive exponent. -/
theorem sbxB_eLpNorm_le_finset_cover {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ)
    (A : Set X) (F : Finset I) (V : I → Set X)
    (hfA : AEStronglyMeasurable f (μ.restrict A))
    (hfV : ∀ i ∈ F, AEStronglyMeasurable f (μ.restrict (V i)))
    (q : ℝ) (hq : 0 < q)
    (hcover : A ⊆ ⋃ i ∈ F, V i) (K : ℝ≥0∞)
    (hlocal : ∀ i ∈ F, eLpNorm f (ENNReal.ofReal q) (μ.restrict (V i)) ≤ K) :
    eLpNorm f (ENNReal.ofReal q) (μ.restrict A) ≤
      (F.card : ℝ≥0∞) ^ (1 / q) * K := by
  classical
  have hs : eLpNorm f (ENNReal.ofReal q) (μ.restrict A) ^ q ≤
      (F.card : ℝ≥0∞) * K ^ q := by
    calc
      _ ≤ ∑ i ∈ F, eLpNorm f (ENNReal.ofReal q) (μ.restrict (V i)) ^ q :=
        sbxB_eLpNorm_rpow_le_finset_cover μ f A F V hfA hfV q hq hcover
      _ ≤ ∑ _i ∈ F, K ^ q := Finset.sum_le_sum fun i hi =>
        ENNReal.rpow_le_rpow (hlocal i hi) hq.le
      _ = _ := by simp
  have hs' := ENNReal.rpow_le_rpow hs (show 0 ≤ 1 / q by positivity)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hs'
  have hq' : q * (1 / q) = 1 := by field_simp
  simpa only [hq', ENNReal.rpow_one] using hs'

/-- The polynomial backward covers turn uniform local bounds into bounds on
either source negative cylinder. -/
theorem sbxB_negative_norm_of_backward_local_bounds (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ σ σ' : ℝ,
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ inner : Bool,
      let A : ℝ → Set (ℝ × Vec d) := fun s =>
        if inner then {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d s}
        else {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d s}
      ∀ (f : ℝ × Vec d → ℝ), AEStronglyMeasurable f (volume.restrict (A σ')) →
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          AEStronglyMeasurable f
            (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32)))) →
        ∀ (q : ℝ), 0 < q → ∀ K : ℝ≥0∞,
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          eLpNorm f (ENNReal.ofReal q)
            (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32))) ≤ K) →
        eLpNorm f (ENNReal.ofReal q) (volume.restrict (A σ')) ≤
          (ENNReal.ofReal (N * (σ - σ') ^ (-b))) ^ (1 / q) * K := by
  obtain ⟨N, b, hN, hb, hcover⟩ := sbxB_negative_polynomial_backward_covers d
  refine ⟨N, b, hN, hb, ?_⟩
  intro σ σ' hlo hlt hhi inner A f hf hfm q hq K hlocal
  obtain ⟨F, hsmall, houter, hcard⟩ := hcover σ σ' hlo hlt hhi inner
  have hsub : A σ' ⊆ ⋃ i ∈ F, sbxBBackHalfPiece i ((σ - σ') / 32) := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hsmall x hx
    simp only [Set.mem_iUnion]
    exact ⟨i, hi, hxi⟩
  have hcard' : (F.card : ℝ≥0∞) ≤ ENNReal.ofReal (N * (σ - σ') ^ (-b)) := by
    simpa using ENNReal.ofReal_le_ofReal hcard
  calc
    _ ≤ (F.card : ℝ≥0∞) ^ (1 / q) * K :=
      sbxB_eLpNorm_le_finset_cover volume f (A σ') F
        (fun i => sbxBBackHalfPiece i ((σ - σ') / 32)) hf
        (fun i hi => hfm i (houter i hi)) q hq hsub K
        (fun i hi => hlocal i (houter i hi))
    _ ≤ _ := mul_le_mul_left
      (ENNReal.rpow_le_rpow hcard' (show 0 ≤ 1 / q by positivity)) K

/-- A gain on each full and half backward piece gives a gain on either
source cylinder, with the explicit polynomial cover factor. -/
theorem sbxB_negative_norm_of_backward_local_gain (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ σ σ' : ℝ,
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ inner : Bool,
      let A : ℝ → Set (ℝ × Vec d) := fun s =>
        if inner then {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d s}
        else {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d s}
      ∀ (f : ℝ × Vec d → ℝ), AEStronglyMeasurable f (volume.restrict (A σ')) →
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          AEStronglyMeasurable f
            (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32)))) →
        ∀ (p q : ℝ), 0 < q → ∀ L : ℝ≥0∞,
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          eLpNorm f (ENNReal.ofReal q)
              (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32))) ≤
            L * eLpNorm f (ENNReal.ofReal p)
              (volume.restrict (sbxBBackPiece x ((σ - σ') / 32)))) →
        eLpNorm f (ENNReal.ofReal q) (volume.restrict (A σ')) ≤
          (ENNReal.ofReal (N * (σ - σ') ^ (-b))) ^ (1 / q) *
            (L * eLpNorm f (ENNReal.ofReal p) (volume.restrict (A σ))) := by
  obtain ⟨N, b, hN, hb, hcover⟩ := sbxB_negative_norm_of_backward_local_bounds d
  refine ⟨N, b, hN, hb, ?_⟩
  intro σ σ' hlo hlt hhi inner A f hf hfm p q hq L hlocal
  apply hcover σ σ' hlo hlt hhi inner f hf hfm q hq
  intro x hx
  exact (hlocal x hx).trans (mul_le_mul_right
    (eLpNorm_mono_measure f (Measure.restrict_mono_set volume hx)) L)

/-- The polynomial covering factor and the inverse-radius factor combine
under the input-exponent root. -/
theorem sbxB_backward_cover_coefficient (N b C g p χ : ℝ)
    (hN : 1 ≤ N) (hb : 0 < b) (hC : 0 < C)
    (hg : 0 < g) (hg1 : g ≤ 1) (hp : 0 < p) (hχ : 1 < χ) :
    ENNReal.ofReal (N * g ^ (-b)) ^ (1 / (χ * p)) *
        ENNReal.ofReal ((C * (1 + p) ^ (2 : ℝ) * 1024 * g ^ (-2 : ℝ)) ^ (1 / p)) ≤
      ENNReal.ofReal (((N * C * 1024) * (1 + p) ^ (2 : ℝ) *
        g ^ (-(b + 2))) ^ (1 / p)) := by
  have hpow : 1 ≤ g ^ (-b) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hg hg1 (by linarith)
  have hbase : 1 ≤ N * g ^ (-b) := one_le_mul_of_one_le_of_one_le hN hpow
  have hbasepos : 0 < N * g ^ (-b) := lt_of_lt_of_le zero_lt_one hbase
  have hother : 0 < C * (1 + p) ^ (2 : ℝ) * 1024 * g ^ (-2 : ℝ) := by positivity
  have hexp : 1 / (χ * p) ≤ 1 / p := by
    apply one_div_le_one_div_of_le hp
    nlinarith
  rw [ENNReal.ofReal_rpow_of_pos hbasepos,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hbasepos.le _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (N * g ^ (-b)) ^ (1 / p) *
        (C * (1 + p) ^ (2 : ℝ) * 1024 * g ^ (-2 : ℝ)) ^ (1 / p) :=
      mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hbase hexp)
        (Real.rpow_nonneg hother.le _)
    _ = _ := by
      rw [← Real.mul_rpow hbasepos.le hother.le]
      have heq : N * g ^ (-b) * (C * (1 + p) ^ (2 : ℝ) * 1024 * g ^ (-2 : ℝ)) =
          N * C * 1024 * (1 + p) ^ (2 : ℝ) * (g ^ (-b) * g ^ (-2 : ℝ)) := by ring
      rw [heq, ← Real.rpow_add hg]
      congr 2 <;> ring

/-- The translated, scaled backward inverse gain needed on each member of
the cover. This is a local estimate on one full and one half cylinder. -/
def sbxBTranslatedBackwardLocalGain (d : ℕ) (κ C : ℝ) : Prop :=
  ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ (ε p : ℝ), 0 < ε → 0 < p → ∀ (x : ℝ × Vec d) (r : ℝ), 0 < r →
    (∀ z ∈ sbxBBackPiece x r,
      (z.1 + 3 / 4, z.2) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) →
    eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
        (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        (volume.restrict (sbxBBackHalfPiece x r)) ≤
      ENNReal.ofReal ((C * (1 + p) ^ (2 : ℝ) * r ^ (-2 : ℝ)) ^ (1 / p)) *
        eLpNorm (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
          (ENNReal.ofReal p) (volume.restrict (sbxBBackPiece x r))

/-- Both negative cylinders translate inside the original caloric domain. -/
theorem sbxB_negative_cylinder_shift_subset (d : ℕ) (σ : ℝ)
    (hσ : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) (inner : Bool) :
    ∀ z : ℝ × Vec d,
      (if inner then (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d σ
       else (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d σ) →
      (z.1 + 3 / 4, z.2) ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
  intro z hz
  cases inner
  · change (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d σ at hz
    have hz' : z ∈ sbxBBackCylinder d (-5 / 16 - (σ - 1 / 2) / 16)
        (5 / 8 + (σ - 1 / 2) / 4) := by
      rw [sbxB_backCylinder_eq_neg d σ hσ]
      exact hz
    change z.1 ∈ Set.Ioc (-5 / 16 - (σ - 1 / 2) / 16) 0 ∧
      z.2 ∈ sourceBall (0 : Vec d) (5 / 8 + (σ - 1 / 2) / 4) at hz'
    refine ⟨⟨by linarith [hz'.1.1], by linarith [hz'.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hs : euclideanNorm (z.2 - 0) < 5 / 8 + (σ - 1 / 2) / 4 := hz'.2
    linarith
  · change (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d σ at hz
    have hz' : z ∈ sbxBBackCylinder d (-1 / 4 - (σ - 1 / 2) / 8)
        (1 / 2 + (σ - 1 / 2) / 4) := by
      rw [sbxB_backCylinder_eq_negInner d σ hσ]
      exact hz
    change z.1 ∈ Set.Ioc (-1 / 4 - (σ - 1 / 2) / 8) 0 ∧
      z.2 ∈ sourceBall (0 : Vec d) (1 / 2 + (σ - 1 / 2) / 4) at hz'
    refine ⟨⟨by linarith [hz'.1.1], by linarith [hz'.1.2]⟩, ?_⟩
    change euclideanNorm (z.2 - 0) < 1
    have hs : euclideanNorm (z.2 - 0) < 1 / 2 + (σ - 1 / 2) / 4 := hz'.2
    linarith

/-- The shifted clipped reciprocal is measurable on every set whose time
translation lies in the caloric domain. -/
theorem sbxB_shifted_inverse_aestronglyMeasurable {d : ℕ}
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (u : ℝ × Vec d → ℝ)
    (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (ε : ℝ) (hε : 0 < ε) (S : Set (ℝ × Vec d))
    (hS : ∀ z ∈ S, (z.1 + 3 / 4, z.2) ∈
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1) :
    AEStronglyMeasurable (fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε))
      (volume.restrict S) := by
  let v : ℝ × Vec d := (3 / 4, 0)
  let D : Set (ℝ × Vec d) := Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1
  have hmp : MeasurePreserving (fun z : ℝ × Vec d => z + v) volume volume := by
    rw [Measure.volume_eq_prod ℝ (Vec d)]
    simpa [v, Prod.add_def, Prod.map_def] using
      ((measurePreserving_add_right (volume : Measure ℝ) (3 / 4)).prod
        (MeasurePreserving.id (volume : Measure (Vec d))))
  have hm := hmp.restrict_preimage_emb (Homeomorph.addRight v).measurableEmbedding D
  have hu := hcal.1.aestronglyMeasurable.comp_measurePreserving hm
  have hsub : S ⊆ (fun z : ℝ × Vec d => z + v) ⁻¹' D := by
    intro z hz
    simpa [D, v, Prod.add_def] using hS z hz
  have hu' : AEStronglyMeasurable (fun z => u (z.1 + 3 / 4, z.2))
      (volume.restrict S) := by
    have hh := hu.mono_measure (Measure.restrict_mono_set volume hsub)
    simpa [Function.comp_def, v, Prod.add_def] using hh
  have hc : Continuous (fun x : ℝ => 1 / max ε (x + ε)) :=
    continuous_const.div (continuous_const.max (continuous_id.add continuous_const))
      (fun x => ne_of_gt (lt_of_lt_of_le hε (le_max_left ε (x + ε))))
  exact hc.comp_aestronglyMeasurable hu'

/-- A half backward piece is contained in its full backward piece. -/
theorem sbxB_half_backward_piece_subset {d : ℕ} (x : ℝ × Vec d) (r : ℝ)
    (hr : 0 < r) : sbxBBackHalfPiece x r ⊆ sbxBBackPiece x r := by
  intro z hz
  refine ⟨⟨by nlinarith [hz.1.1, sq_nonneg r], hz.1.2⟩, ?_⟩
  change euclideanNorm (z.2 - x.2) < r
  have hs : euclideanNorm (z.2 - x.2) < r / 2 := hz.2
  linarith

/-- The inverse-square radius at the cover scale. -/
theorem sbxB_backward_cover_radius (g : ℝ) (hg : 0 < g) :
    (g / 32) ^ (-2 : ℝ) = 1024 * g ^ (-2 : ℝ) := by
  rw [Real.div_rpow hg.le (by norm_num),
    Real.rpow_neg (show (0 : ℝ) ≤ 32 by norm_num)]
  norm_num [Real.rpow_two]
  ring

/-- Local backward gains imply the unnormalized gain on either negative
family, with structural constants independent of the field and exponent. -/
theorem sbxB_negative_raw_gain_of_local (d : ℕ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ σ σ' : ℝ,
      1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ inner : Bool,
      let A : ℝ → Set (ℝ × Vec d) := fun s =>
        if inner then {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d s}
        else {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d s}
      ∀ (f : ℝ × Vec d → ℝ), AEStronglyMeasurable f (volume.restrict (A σ')) →
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          AEStronglyMeasurable f
            (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32)))) →
        ∀ (C χ p : ℝ), 0 < C → 1 < χ → 0 < p →
        (∀ x, sbxBBackPiece x ((σ - σ') / 32) ⊆ A σ →
          eLpNorm f (ENNReal.ofReal (χ * p))
              (volume.restrict (sbxBBackHalfPiece x ((σ - σ') / 32))) ≤
            ENNReal.ofReal ((C * (1 + p) ^ (2 : ℝ) * 1024 *
              (σ - σ') ^ (-2 : ℝ)) ^ (1 / p)) *
              eLpNorm f (ENNReal.ofReal p)
                (volume.restrict (sbxBBackPiece x ((σ - σ') / 32)))) →
        eLpNorm f (ENNReal.ofReal (χ * p)) (volume.restrict (A σ')) ≤
          ENNReal.ofReal (((N * C * 1024) * (1 + p) ^ (2 : ℝ) *
            (σ - σ') ^ (-(b + 2))) ^ (1 / p)) *
            eLpNorm f (ENNReal.ofReal p) (volume.restrict (A σ)) := by
  obtain ⟨N, b, hN, hb, hcover⟩ := sbxB_negative_norm_of_backward_local_gain d
  refine ⟨N, b, hN, hb, ?_⟩
  intro σ σ' hlo hlt hhi inner A f hf hfm C χ p hC hχ hp hlocal
  have hg : 0 < σ - σ' := sub_pos.mpr hlt
  have hg1 : σ - σ' ≤ 1 := by linarith
  have hχp : 0 < χ * p := by positivity
  have h := hcover σ σ' hlo hlt hhi inner f hf hfm p (χ * p) hχp _ hlocal
  have hc := sbxB_backward_cover_coefficient N b C (σ - σ') p χ hN hb hC hg hg1 hp hχ
  exact h.trans (by rw [← mul_assoc]; exact mul_le_mul_left hc _)

/-- The translated backward local estimate yields both unnormalized C8
inverse gains, with constants chosen before the coefficients and field. -/
theorem sbxB_shifted_negative_raw_gains_of_local (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) :
    ∃ N b : ℝ, 1 ≤ N ∧ 0 < b ∧ ∀ C : ℝ, 0 < C →
      sbxBTranslatedBackwardLocalGain d κ C →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ σ' : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p → ∀ inner : Bool,
      let A : ℝ → Set (ℝ × Vec d) := fun s =>
        if inner then {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCylInner d s}
        else {z | (z.2, z.1) ∈ PDE.Parabolic.WeakHarnack.negCyl d s}
      let f : ℝ × Vec d → ℝ := fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε)
      eLpNorm f (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p)) (volume.restrict (A σ')) ≤
        ENNReal.ofReal (((N * C * 1024) * (1 + p) ^ (2 : ℝ) *
          (σ - σ') ^ (-(b + 2))) ^ (1 / p)) *
          eLpNorm f (ENNReal.ofReal p) (volume.restrict (A σ)) := by
  obtain ⟨N, b, hN, hb, hraw⟩ := sbxB_negative_raw_gain_of_local d
  refine ⟨N, b, hN, hb, ?_⟩
  intro C hC hlocal ρ α hell u G hcal hu ε hε σ σ' hlo hlt hhi p hp inner A f
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hχ : 1 < ((d : ℝ) + 2) / d := by
    apply (lt_div_iff₀ hdpos).2
    nlinarith
  have hg : 0 < σ - σ' := sub_pos.mpr hlt
  have hr : 0 < (σ - σ') / 32 := by positivity
  have hloσ : 1 / 2 ≤ σ := le_trans hlo hlt.le
  have hins : ∀ z ∈ A σ, (z.1 + 3 / 4, z.2) ∈
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    apply sbxB_negative_cylinder_shift_subset d σ hloσ hhi inner z
    cases inner <;> simpa [A] using hz
  have hsmall : ∀ z ∈ A σ', (z.1 + 3 / 4, z.2) ∈
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1 := by
    intro z hz
    apply sbxB_negative_cylinder_shift_subset d σ' hlo (le_trans hlt.le hhi) inner z
    cases inner <;> simpa [A] using hz
  apply hraw σ σ' hlo hlt hhi inner f
    (sbxB_shifted_inverse_aestronglyMeasurable ρ α u G hcal ε hε _ hsmall)
  · intro x hx
    apply sbxB_shifted_inverse_aestronglyMeasurable ρ α u G hcal ε hε
    intro z hz
    exact hins z (hx (sbxB_half_backward_piece_subset x _ hr hz))
  · exact hC
  · exact hχ
  · exact hp
  · intro x hx
    have h := hlocal ρ α hell u G hcal hu ε p hε hp x _ hr
      (fun z hz => hins z (hx hz))
    rw [sbxB_backward_cover_radius _ hg] at h
    simpa only [f, mul_assoc] using h

/-- Transfer a raw time-first estimate to either fixed normalized measure. -/
theorem sbxB_negative_normalize_gain (d : ℕ) (inner : Bool) (σ' σ p B χ : ℝ)
    (hσ' : 1 / 2 ≤ σ') (hσσ : σ' < σ) (hσ : σ ≤ 1)
    (hp : 0 < p) (hχ : 1 < χ) (hB : 0 ≤ B) (f : ℝ × Vec d → ℝ) :
    let S : ℝ → Set (Vec d × ℝ) := fun s =>
      if inner then PDE.Parabolic.WeakHarnack.negCylInner d s
      else PDE.Parabolic.WeakHarnack.negCyl d s
    let T : ℝ → Set (ℝ × Vec d) := fun s => {z | (z.2, z.1) ∈ S s}
    eLpNorm f (ENNReal.ofReal (χ * p)) (volume.restrict (T σ')) ≤
      ENNReal.ofReal (B ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) (volume.restrict (T σ)) →
    eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) (ENNReal.ofReal (χ * p))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ')) ≤
      ENNReal.ofReal ((B * max 1 (volume (S 1)).toReal) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ)) := by
  let S : ℝ → Set (Vec d × ℝ) := fun s =>
    if inner then PDE.Parabolic.WeakHarnack.negCylInner d s
    else PDE.Parabolic.WeakHarnack.negCyl d s
  let T : ℝ → Set (ℝ × Vec d) := fun s => {z | (z.2, z.1) ∈ S s}
  let V : ℝ≥0∞ := volume (S 1)
  have hV0 : V ≠ 0 := by
    cases inner
    · exact (PDE.Parabolic.WeakHarnack.volume_negCyl_pos (d := d) (σ := 1) (by norm_num)).ne'
    · exact (PDE.Parabolic.WeakHarnack.volume_negCylInner_pos (d := d) (σ := 1) (by norm_num)).ne'
  have hVt : V ≠ ⊤ := by
    cases inner
    · exact PDE.Parabolic.WeakHarnack.volume_negCyl_ne_top (d := d) (σ := 1) (by norm_num)
    · exact PDE.Parabolic.WeakHarnack.volume_negCylInner_ne_top (d := d) (σ := 1) (by norm_num)
  have hV : 0 < V.toReal := ENNReal.toReal_pos hV0 hVt
  have hVi : ENNReal.ofReal V.toReal⁻¹ = V⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hV, ENNReal.ofReal_toReal hVt]
  dsimp only
  intro hraw
  have hn := sbxB_normalize_nested_gain _ _ f V.toReal χ p B hV hχ hp hB hraw
  rw [hVi] at hn
  change eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) (ENNReal.ofReal (χ * p))
      ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ')) ≤
    ENNReal.ofReal ((B * max 1 V.toReal) ^ (1 / p)) *
      eLpNorm (fun z : Vec d × ℝ => f (z.2, z.1)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ))
  rw [sbxB_negative_family_normalized_norm d σ' hσ' (le_trans hσσ.le hσ) inner _ f,
    sbxB_negative_family_normalized_norm d σ (le_trans hσ' hσσ.le) hσ inner _ f]
  exact hn

/-- The local translated backward gain implies the fixed normalized gain
for either C8 negative family. -/
theorem sbxB_shifted_negative_normalized_gain_of_local
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hC : 1 ≤ C)
    (hlocal : sbxBTranslatedBackwardLocalGain d κ C) (inner : Bool) :
    ∃ A m : ℝ, 1 ≤ A ∧ 0 < m ∧
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε → ∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 →
      ∀ p : ℝ, 0 < p →
      let S : ℝ → Set (Vec d × ℝ) := fun s =>
        if inner then PDE.Parabolic.WeakHarnack.negCylInner d s
        else PDE.Parabolic.WeakHarnack.negCyl d s
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε))
          (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
          ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ')) ≤
        ENNReal.ofReal ((A * (1 + p) ^ (2 : ℝ) * (σ - σ') ^ (-m)) ^ (1 / p)) *
          eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε))
            (ENNReal.ofReal p) ((PDE.Parabolic.WeakHarnack.cylMeasure (S 1)).restrict (S σ)) := by
  obtain ⟨N, b, hN, hb, hraw⟩ := sbxB_shifted_negative_raw_gains_of_local d hd κ
  let S : ℝ → Set (Vec d × ℝ) := fun s =>
    if inner then PDE.Parabolic.WeakHarnack.negCylInner d s
    else PDE.Parabolic.WeakHarnack.negCyl d s
  let T : ℝ → Set (ℝ × Vec d) := fun s => {z | (z.2, z.1) ∈ S s}
  let V : ℝ≥0∞ := volume (S 1)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hd)
  have hχ : 1 < ((d : ℝ) + 2) / d := by
    apply (lt_div_iff₀ hdpos).2
    nlinarith
  refine ⟨N * C * 1024 * max 1 V.toReal, b + 2, ?_, by linarith, ?_⟩
  · have hNC : 1 ≤ N * C := one_le_mul_of_one_le_of_one_le hN hC
    have hfac : 1 ≤ 1024 * max 1 V.toReal := by
      have := le_max_left (1 : ℝ) V.toReal
      nlinarith
    nlinarith [one_le_mul_of_one_le_of_one_le hNC hfac]
  intro ρ α hell u G hcal hu ε hε σ' σ hσ' hσσ hσ p hp
  let f : ℝ × Vec d → ℝ := fun z => 1 / max ε (u (z.1 + 3 / 4, z.2) + ε)
  have hbase : 0 ≤ (N * C * 1024) * (1 + p) ^ (2 : ℝ) *
      (σ - σ') ^ (-(b + 2)) := by positivity
  have hh := hraw C (lt_of_lt_of_le zero_lt_one hC) hlocal ρ α hell u G hcal hu ε hε
    σ σ' hσ' hσσ hσ p hp inner
  have hh' : eLpNorm f (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
      (volume.restrict (T σ')) ≤
      ENNReal.ofReal (((N * C * 1024) * (1 + p) ^ (2 : ℝ) *
        (σ - σ') ^ (-(b + 2))) ^ (1 / p)) *
        eLpNorm f (ENNReal.ofReal p) (volume.restrict (T σ)) := by
    cases inner <;> simpa [S, T, f] using hh
  have hn := sbxB_negative_normalize_gain d inner σ' σ p
    ((N * C * 1024) * (1 + p) ^ (2 : ℝ) * (σ - σ') ^ (-(b + 2)))
    (((d : ℝ) + 2) / d) hσ' hσσ hσ hp hχ hbase f hh'
  convert hn using 1 <;> dsimp only [f, S, T, V] <;> congr 2 <;> ring

/-- Both C8 negative nested gains, with structural constants chosen before fields. -/
theorem sbxB_both_shifted_negative_normalized_gains_of_local
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hC : 1 ≤ C)
    (hlocal : sbxBTranslatedBackwardLocalGain d κ C) :
    ∃ A₂ β₂ m₂ A₃ β₃ m₃ : ℝ, 1 ≤ A₂ ∧ 0 ≤ β₂ ∧ 0 < m₂ ∧
      1 ≤ A₃ ∧ 0 ≤ β₃ ∧ 0 < m₃ ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ')) ≤
      ENNReal.ofReal ((A₂ * (1 + p) ^ β₂ * (σ - σ') ^ (-m₂)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCyl d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCyl d σ)))) ∧
      (∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
      ∀ ε : ℝ, 0 < ε →
      (∀ σ' σ : ℝ, 1 / 2 ≤ σ' → σ' < σ → σ ≤ 1 → ∀ p : ℝ, 0 < p →
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal ((((d : ℝ) + 2) / d) * p))
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ')) ≤
      ENNReal.ofReal ((A₃ * (1 + p) ^ β₃ * (σ - σ') ^ (-m₃)) ^ (1 / p)) *
      eLpNorm (fun z => 1 / max ε (u (z.2 + 3 / 4, z.1) + ε)) (ENNReal.ofReal p)
        ((PDE.Parabolic.WeakHarnack.cylMeasure (PDE.Parabolic.WeakHarnack.negCylInner d 1)).restrict
          (PDE.Parabolic.WeakHarnack.negCylInner d σ)))) := by
  obtain ⟨A₂, m₂, hA₂, hm₂, hneg⟩ :=
    sbxB_shifted_negative_normalized_gain_of_local d hd κ C hC hlocal false
  obtain ⟨A₃, m₃, hA₃, hm₃, hinner⟩ :=
    sbxB_shifted_negative_normalized_gain_of_local d hd κ C hC hlocal true
  refine ⟨A₂, 2, m₂, A₃, 2, m₃, hA₂, by norm_num, hm₂, hA₃, by norm_num, hm₃, ?_, ?_⟩
  · simpa only [Bool.false_eq_true, ↓reduceIte] using hneg
  · simpa only [↓reduceIte] using hinner

#print axioms sbxB_both_shifted_negative_normalized_gains_of_local
#print axioms sbxB_shifted_negative_normalized_gain_of_local
#print axioms sbxB_shifted_negative_raw_gains_of_local
#print axioms sbxB_negative_raw_gain_of_local
#print axioms sbxB_shifted_inverse_aestronglyMeasurable
#print axioms sbxB_negative_cylinder_shift_subset
#print axioms sbxB_backward_cover_coefficient
#print axioms sbxB_negative_norm_of_backward_local_gain
#print axioms sbxB_negative_norm_of_backward_local_bounds
#print axioms sbxB_eLpNorm_le_finset_cover
#print axioms sbxB_negative_normalized_norm
#print axioms sbxB_negative_inner_normalized_norm
#print axioms sbxB_eLpNorm_rpow_le_finset_cover

#print axioms sbxB_backward_restrict_Ioo_eq_Ioc
#print axioms sbxB_inverse_clip_eq_ae

end EinsteinFull.Calculus
