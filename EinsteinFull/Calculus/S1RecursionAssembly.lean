import EinsteinFull.Calculus.S1RecursionSupport

/-! Abstract steps of the dyadic block recursion: strip decomposition, tiling of the
cube of side `2L`, the error identity, independence/identical distribution of the
children and the second-moment bound. Everything is stated for an arbitrary finite family
of local stationary fields; the covariance construction is plugged in later. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

section Defs

variable {ι : Type*} [Fintype ι]

/-- Normalized block of a field family over a set, with a weight `f`. -/
noncomputable def blk (n : ℝ) (F : ι → Vec d → FieldPair d → ℝ) (C : Set (Vec d))
    (f : Vec d → ℝ) : FieldPair d → ι → ℝ :=
  fun ω a => n * ∫ y in C, f y * F a y ω

/-- Indicator of the boundary strip of the cube of side `L` around `x`. -/
noncomputable def stripFn (x : Vec d) (L w : ℝ) : Vec d → ℝ :=
  (clockBlockCube x (L - w))ᶜ.indicator (fun _ => (1 : ℝ))

omit [Fintype ι] in
theorem blk_one (n : ℝ) (F : ι → Vec d → FieldPair d → ℝ) (C : Set (Vec d)) :
    blk n F C (fun _ => (1 : ℝ)) = fun ω a => n * ∫ y in C, F a y ω := by
  funext ω a
  simp [blk]

theorem measurable_vsize : Measurable (vsize : (ι → ℝ) → ℝ) := by
  unfold vsize
  exact Real.continuous_sqrt.measurable.comp
    (Finset.measurable_sum _ fun a _ => (measurable_pi_apply a).pow_const 2)

end Defs

section Blocks

variable {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]
  {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}

theorem blk_strip_decomp (h : ∀ a, LocalStationaryField μ V (F a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n L w : ℝ) (hw : 0 ≤ w) (x : Vec d) :
    ∀ᵐ ω ∂μ, ∀ a, blk n F (clockBlockCube x L) (fun _ => 1) ω a -
        blk n F (clockBlockCube x (L - w)) (fun _ => 1) ω a =
      blk n F (clockBlockCube x L) (stripFn x L w) ω a := by
  have hslice : ∀ᵐ ω ∂μ, ∀ a, Integrable (fun y => F a y ω)
      (volume.restrict (clockBlockCube x L)) :=
    ae_all_iff.2 fun a => (h a).ae_integrable_slice hT (volume_clockBlockCube_lt_top x L)
  filter_upwards [hslice] with ω hω a
  have hsub := setIntegral_sub_indicator (S := clockBlockCube x L)
    (T := clockBlockCube x (L - w)) (measurableSet_clockBlockCube _ _)
    (clockBlockCube_mono' x (by linarith)) (hω a)
  unfold blk stripFn
  rw [← mul_sub, hsub]

theorem blk_tiling (h : ∀ a, LocalStationaryField μ V (F a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) {n n₂ : ℝ}
    (hn₂ : n₂ = (2 : ℝ) ^ (-(d : ℝ) / 2) * n) (L : ℝ) :
    ∀ᵐ ω ∂μ, ∀ a, blk n₂ F (clockBlockCube 0 (2 * L)) (fun _ => 1) ω a =
      (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
        blk n F (clockBlockCube (childCenter L j) L) (fun _ => 1) ω a := by
  have hslice : ∀ᵐ ω ∂μ, ∀ a, Integrable (fun y => F a y ω)
      (volume.restrict (clockBlockCube 0 (2 * L))) :=
    ae_all_iff.2 fun a => (h a).ae_integrable_slice hT (volume_clockBlockCube_lt_top 0 (2 * L))
  filter_upwards [hslice] with ω hω a
  have ht := setIntegral_clockBlockCube_two (L := L) (g := fun y => F a y ω) (hω a)
  unfold blk
  simp only [one_mul]
  rw [ht, hn₂, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blk_error_ae {V₂ : Vec d → Set (Vec d)} {F₂ : ι → Vec d → FieldPair d → ℝ}
    (h1 : ∀ a, LocalStationaryField μ V (F a)) (h2 : ∀ a, LocalStationaryField μ V₂ (F₂ a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) {n n₂ : ℝ}
    (hn₂ : n₂ = (2 : ℝ) ^ (-(d : ℝ) / 2) * n) (L w : ℝ) (hw : 0 ≤ w) :
    (fun ω a => blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => 1) ω a -
        (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
          blk n F (clockBlockCube (childCenter L j) (L - w)) (fun _ => 1) ω a) =ᵐ[μ]
      fun ω a => (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
        ((blk n F₂ (clockBlockCube (childCenter L j) L) (fun _ => 1) ω a -
          blk n F (clockBlockCube (childCenter L j) L) (fun _ => 1) ω a) +
          blk n F (clockBlockCube (childCenter L j) L) (stripFn (childCenter L j) L w) ω a) := by
  have ht := blk_tiling h2 hT hn₂ L
  have hs : ∀ᵐ ω ∂μ, ∀ j : Fin d → Fin 2, ∀ a,
      blk n F (clockBlockCube (childCenter L j) L) (fun _ => 1) ω a -
        blk n F (clockBlockCube (childCenter L j) (L - w)) (fun _ => 1) ω a =
      blk n F (clockBlockCube (childCenter L j) L) (stripFn (childCenter L j) L w) ω a :=
    ae_all_iff.2 fun j => blk_strip_decomp h1 hT n L w hw (childCenter L j)
  filter_upwards [ht, hs] with ω hω1 hω2
  funext a
  rw [hω1 a, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := hω2 j a
  linarith

theorem blk_L2Vec_of_identDistrib (h : ∀ a, LocalStationaryField μ V (F a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ) (c : Vec d) (L' : ℝ)
    {Xm : FieldPair d → ι → ℝ}
    (hid : IdentDistrib (blk n F (clockBlockCube c L') (fun _ => 1)) Xm μ μ)
    (hXm : L2Vec μ Xm) : L2Vec μ (blk n F (clockBlockCube c L') (fun _ => 1)) := by
  refine ⟨fun a => ?_, ?_⟩
  · rw [blk_one]
    exact (((h a).integrable_block hT (volume_clockBlockCube_lt_top c L')).const_mul n).aestronglyMeasurable
  · exact (((hid.comp (measurable_vsize (ι := ι))).memLp_iff (p := 2)).2 hXm.size_memLp)

end Blocks

section Vec

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] {μ : Measure Ω}

theorem l2_sum_scaled {J : Type*} [Fintype J] (c : ℝ) {Δ S : J → Ω → ι → ℝ}
    (hΔ : ∀ j, L2Vec μ (Δ j)) (hS : ∀ j, L2Vec μ (S j)) {H B : ℝ}
    (hΔb : ∀ j, vl2 μ (Δ j) ≤ H) (hSb : ∀ j, vl2 μ (S j) ≤ B) :
    L2Vec μ (fun ω a => c * ∑ j, (Δ j ω a + S j ω a)) ∧
      vl2 μ (fun ω a => c * ∑ j, (Δ j ω a + S j ω a)) ≤
        |c| * ((Fintype.card J : ℝ) * (H + B)) := by
  have hj : ∀ j, L2Vec μ (fun ω => Δ j ω + S j ω) := fun j => (hΔ j).add (hS j)
  have hsum := L2Vec.sum Finset.univ hj
  have e : (fun ω a => c * ∑ j, (Δ j ω a + S j ω a)) =
      fun ω => c • ∑ j ∈ Finset.univ, (Δ j ω + S j ω) := by
    funext ω a
    simp [Finset.sum_apply]
  rw [e]
  refine ⟨hsum.smul c, ?_⟩
  rw [vl2_smul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
  refine (vl2_sum_le Finset.univ hj).trans ?_
  calc ∑ j, vl2 μ (fun ω => Δ j ω + S j ω)
      ≤ ∑ j : J, (H + B) := Finset.sum_le_sum fun j _ =>
        (vl2_add_le (hΔ j) (hS j)).trans (add_le_add (hΔb j) (hSb j))
    _ = (Fintype.card J : ℝ) * (H + B) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The second-moment bound of the dyadic recursion. -/
theorem cov_chain {J : Type*} [Fintype J] [DecidableEq J]
    {X Xm X₂ : Ω → ι → ℝ} {ch : J → Ω → ι → ℝ} (c : ℝ)
    (hX : L2Vec μ X) (hXm : L2Vec μ Xm) (hX₂ : L2Vec μ X₂)
    (hind : iIndepFun ch μ) (hL2ch : ∀ j, L2Vec μ (ch j))
    (hmean : ∀ j a, ∫ ω, ch j ω a ∂μ = 0) (hid : ∀ j, IdentDistrib (ch j) Xm μ μ)
    (hc : c ^ 2 * (Fintype.card J : ℝ) = 1) {Cc B E : ℝ}
    (hXc : vl2 μ X ≤ Cc) (hXmc : vl2 μ Xm ≤ Cc) (hX₂c : vl2 μ X₂ ≤ Cc)
    (hdiff : vl2 μ (fun ω a => X ω a - Xm ω a) ≤ B)
    (herrL2 : L2Vec μ (fun ω a => X₂ ω a - c * ∑ j, ch j ω a))
    (herr : vl2 μ (fun ω a => X₂ ω a - c * ∑ j, ch j ω a) ≤ E) :
    frob (covMat μ X₂ - covMat μ X) ≤ E * (2 * Cc + E) + B * (2 * Cc) := by
  set Y : Ω → ι → ℝ := fun ω a => c * ∑ j, ch j ω a with hY
  set err : Ω → ι → ℝ := fun ω a => X₂ ω a - Y ω a with herrdef
  have herrL2' : L2Vec μ err := herrL2
  have hYL2 : L2Vec μ Y := by
    have h := hX₂.sub herrL2'
    have e : (fun ω => X₂ ω - err ω) = Y := by
      funext ω a
      simp [herrdef]
    rw [e] at h
    exact h
  have hcovY : covMat μ Y = covMat μ Xm :=
    (covMat_sum_indep c hind hL2ch hmean hid).trans (by rw [hc, one_smul])
  have herr' : vl2 μ err ≤ E := herr
  have hX₂nn : 0 ≤ vl2 μ X₂ := vl2_nonneg _ _
  have hYle : vl2 μ Y ≤ vl2 μ X₂ + vl2 μ err := by
    have e : Y = fun ω => X₂ ω + (-1 : ℝ) • err ω := by
      funext ω a
      simp [herrdef]
    have h := vl2_add_le hX₂ (herrL2'.smul (-1))
    rw [vl2_smul] at h
    simp only [abs_neg, abs_one, one_mul] at h
    rw [e]
    exact h
  have s1 : frob (covMat μ X₂ - covMat μ Y) ≤ E * (2 * Cc + E) := by
    refine (frob_covMat_sub_le hX₂ hYL2).trans ?_
    have e : (fun ω => X₂ ω - Y ω) = err := by
      funext ω
      rfl
    have hd : vl2 μ (fun ω => X₂ ω - Y ω) ≤ E := by
      rw [e]
      exact herr'
    have hsum : vl2 μ X₂ + vl2 μ Y ≤ 2 * Cc + E := by linarith [vl2_nonneg μ err]
    exact mul_le_mul hd hsum (add_nonneg hX₂nn (vl2_nonneg _ _))
      ((vl2_nonneg _ _).trans hd)
  have s2 : frob (covMat μ Xm - covMat μ X) ≤ B * (2 * Cc) := by
    refine (frob_covMat_sub_le hXm hX).trans ?_
    have e : (fun ω => Xm ω - X ω) = fun ω => (-1 : ℝ) • (fun ω a => X ω a - Xm ω a) ω := by
      funext ω a
      simp
    have hd : vl2 μ (fun ω => Xm ω - X ω) ≤ B := by
      rw [e, vl2_smul]
      simpa using hdiff
    exact mul_le_mul hd (by linarith) (add_nonneg (vl2_nonneg _ _) (vl2_nonneg _ _))
      ((vl2_nonneg _ _).trans hd)
  have e : covMat μ X₂ - covMat μ X =
      (covMat μ X₂ - covMat μ Y) + (covMat μ Xm - covMat μ X) := by
    rw [hcovY]
    abel
  rw [e]
  exact (frob_add_le _ _).trans (add_le_add s1 s2)

end Vec

end EinsteinFull.Calculus.S1
