import EinsteinFull.Blueprint.G3.Proofs.C10TestBlocks
import EinsteinFull.Calculus.C8ColoredBlockSeries

/-! Replacement of the actual localized pairing by its frozen-test blocks. -/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.Calculus.C10TestBlocks
open EinsteinFull.Calculus.S1

/-- Freezing the test on trimmed blocks costs the mesh size and the boundary-strip rate. -/
theorem localizedPairing_testBlocks_error
    (hclt : node_e_u3A_block_u2D_cltStmt)
    (hboundary : node_e_u3A_block_u2D_boundaryStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β) (N : ℕ) (hN : 2*d+10 < N) :
    ∃ C L₀ : ℝ, 0 < C ∧ 2 ≤ L₀ ∧
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q → ∀ L : ℝ, L₀ ≤ L → ∀ R : ℝ, L ≤ R →
    ∀ F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
    let X := fun ω => covarianceLocalizedPairing d hd D s δ γ η β h Q R (L^η) F ω -
      covarianceTestBlocks d hd D s δ γ η β h Q R L F ω
    MemLp X 2 (reducedLaw Q) ∧
    covarianceComplexL2Size (reducedLaw Q) X ≤
      C * schwartzTestNorm N F * (L/R + L^(-(1-β)/2)) := by
  classical
  obtain ⟨Cc, Lc, hCc, hLc, hcltQ⟩ := hclt d hd D s δ γ η β h
  obtain ⟨Cb, Lb, hCb, hLb, hboundaryQ⟩ := hboundary d hd D s δ γ η β h
  have horder : 1 ≤ N := by omega
  -- Dilation preserves the literal open cube, including its strict endpoints.
  have hscaled {L R : ℝ} (hR : 0 < R) {x c : Vec d}
      (hx : x ∈ clockBlockCube c L) :
      R⁻¹ • x ∈ clockBlockCube (R⁻¹ • c) (L / R) := by
    apply mem_clockBlockCube_iff.mpr
    intro i
    obtain ⟨hlo, hhi⟩ := mem_clockBlockCube_iff.mp hx i
    constructor
    · change R⁻¹ * c i - (L / R) / 2 < R⁻¹ * x i
      have hh := mul_lt_mul_of_pos_left hlo (inv_pos.mpr hR)
      convert hh using 1 <;> ring
    · change R⁻¹ * x i < R⁻¹ * c i + (L / R) / 2
      have hh := mul_lt_mul_of_pos_left hhi (inv_pos.mpr hR)
      convert hh using 1 <;> ring
  -- The error keeps order N; its small factor is exactly the mesh ratio.
  have hosc {L R : ℝ} (hL : 0 < L) (hLR : L ≤ R)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (c : Vec d) :
      ∀ x ∈ clockBlockCube c L,
      ‖F (R⁻¹ • x) - F (R⁻¹ • c)‖ ≤
        ((2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) *
          ((1 + euclideanNorm (R⁻¹ • c)) ^ N)⁻¹) * ((L / R) / 2) := by
    intro x hx
    have hR : 0 < R := hL.trans_le hLR
    exact schwartz_cube_oscillation_le horder (div_pos hL hR)
      ((div_le_one hR).mpr hLR) F (hscaled hR hx)
  have hosc_nonneg {L R : ℝ} (hL : 0 < L) (hLR : L ≤ R)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (c : Vec d) :
      0 ≤ ((2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) *
        ((1 + euclideanNorm (R⁻¹ • c)) ^ N)⁻¹) * ((L / R) / 2) := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by positivity)
        (mul_nonneg (Nat.cast_nonneg _) (schwartz_norm_nonneg N F)))
        (by unfold euclideanNorm; positivity)
    · exact div_nonneg (div_nonneg hL.le (hL.trans_le hLR).le) (by norm_num)
  -- Real projections permit direct application of the exact scalar-test CLT.
  -- The boundary error has the same spatial decay as the frozen test value.
  have hstrip
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (L : ℝ) (hL : Lb ≤ L)
      (c : Vec d) :
      let strip := (clockBlockCube c (L - L ^ β))ᶜ.indicator (fun _ => (1 : ℝ))
      let X := covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L c strip
      MemLp (fun ω => covarianceVectorSize (X ω)) 2 (reducedLaw Q) ∧
        covarianceL2Size (reducedLaw Q) X ≤ Cb * L ^ (-(1 - β) / 2) := by
    dsimp only
    have hbd : ∀ y ∈ clockBlockCube c L,
        |(clockBlockCube c (L - L ^ β))ᶜ.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
      intro y _
      by_cases hy : y ∈ (clockBlockCube c (L - L ^ β))ᶜ
      · rw [Set.indicator_of_mem hy]; norm_num
      · rw [Set.indicator_of_notMem hy]; norm_num
    have hz : ∀ y ∈ clockBlockCube c (L - L ^ β),
        (clockBlockCube c (L - L ^ β))ᶜ.indicator (fun _ => (1 : ℝ)) y = 0 := by
      intro y hy
      exact Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hy) _
    have hs := hboundaryQ Q hQ L hL c
      ((clockBlockCube c (L - L ^ β))ᶜ.indicator (fun _ => (1 : ℝ))) 1
      (measurable_const.indicator (measurableSet_clockBlockCube _ _).compl)
      zero_le_one hbd hz
    exact ⟨hs.1, by simpa only [mul_one] using hs.2⟩

  -- The parameter window supplies the source-scale condition uniformly in L.
  have hηlower : 0 < η := by
    have hh := h.2.2.2.2.2.2.2.2.1
    linarith
  have hηupper : η < 1 := by
    have hδ : 0 < δ := h.2.2.2.1
    have hh : η < (1 + δ)⁻¹ := h.2.2.2.2.2.2.2.1
    exact hh.trans (inv_lt_one_of_one_lt₀ (by linarith))
  obtain ⟨Ls, hLs⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hηlower).eventually_ge_atTop (2 * D.dependenceRange))
  have hthreshold {L : ℝ} (hL : max (max Lc Lb) Ls ≤ L) :
      2 ≤ L ∧ Lc ≤ L ∧ Lb ≤ L ∧ 2 * D.dependenceRange ≤ L ^ η ∧ L ^ η ≤ L := by
    have hc : Lc ≤ L := (le_max_left Lc Lb).trans ((le_max_left _ _).trans hL)
    have hb : Lb ≤ L := (le_max_right Lc Lb).trans ((le_max_left _ _).trans hL)
    have h2 : 2 ≤ L := hLc.trans hc
    refine ⟨h2, hc, hb, hLs L ((le_max_right _ _).trans hL), ?_⟩
    exact (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ L) hηupper.le).trans_eq
      (Real.rpow_one L)

  -- A bounded deterministic spatial weight preserves local representatives and
  -- centering. Stationarity of the weighted field is neither used nor asserted.
  have hweighted
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (a : JointObservationIndex d)
      (C U : Set (Vec d)) (hCm : MeasurableSet C) (hC : volume C < ⊤)
      (hCU : ∀ y ∈ C, ball y (covarianceLocalizationRadius D δ r) ⊆ U)
      (f : Vec d → ℝ) (hf : Measurable f) (b : ℝ) (hb : ∀ y ∈ C, |f y| ≤ b)
      (n : ℝ) :
      let X := fun ω => n * ∫ y in C,
        f y * covarianceLocalizedField d hd D s δ γ η β h Q r y ω a
      Integrable X (reducedLaw Q) ∧ (∫ ω, X ω ∂reducedLaw Q) = 0 ∧
        ∃ H : FieldPair d → ℝ, StronglyMeasurable[EinsteinRelation.localSigma U] H ∧
          X =ᵐ[reducedLaw Q] H := by
    haveI := reducedLaw_probability Q
    haveI : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC⟩
    have hfield := cov_lsf hjl d hd D s δ γ η β h Q hQ r hr a
    have hbound : ∀ᵐ p : Vec d × FieldPair d ∂((volume.restrict C).prod (reducedLaw Q)),
        ‖f p.1‖ ≤ b := by
      apply (Measure.ae_prod_iff_ae_ae
        (measurableSet_le (hf.comp measurable_fst).norm measurable_const)).2
      apply (ae_restrict_iff' hCm).2
      exact Filter.Eventually.of_forall fun y hy =>
        Filter.Eventually.of_forall fun _ => by
          simpa only [Function.comp_apply, Real.norm_eq_abs] using hb y hy
    have hint : Integrable (fun p : Vec d × FieldPair d =>
        f p.1 * covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2 a)
        ((volume.restrict C).prod (reducedLaw Q)) :=
      (hfield.integrable_prod (reducedLaw_hT Q) hC).bdd_mul
        (hf.comp measurable_fst).aestronglyMeasurable hbound
    refine ⟨hint.integral_prod_right.const_mul n, ?_, ?_⟩
    · dsimp only
      rw [integral_const_mul]
      have hswap := integral_integral_swap
        (f := fun ω y => f y * covarianceLocalizedField d hd D s δ γ η β h Q r y ω a)
        hint.swap
      rw [hswap]
      have hz (y : Vec d) :
          (∫ ω, f y * covarianceLocalizedField d hd D s δ γ η β h Q r y ω a
            ∂reducedLaw Q) = 0 := by
        rw [integral_const_mul]
        change f y * (∫ ω, covF d hd D s δ γ η β h Q r a y ω ∂reducedLaw Q) = 0
        rw [hfield.mean_zero y, mul_zero]
      simp only [hz, integral_zero, mul_zero]
    · obtain ⟨H, hHm, hHe⟩ := local_integral_aeEq_measurable
        (EinsteinRelation.Probability.localSigma_le_borel U) hint (by
          apply (ae_restrict_iff' hCm).2
          apply Filter.Eventually.of_forall
          intro y hy
          obtain ⟨g, hgm, hge⟩ := hfield.local_rep y
          refine ⟨fun ω => f y * g ω, ?_, ?_⟩
          · exact ((hgm.mono (localSigma_mono (hCU y hy)) le_rfl).stronglyMeasurable).const_mul _
          · exact hge.symm.mono fun ω hω => congrArg (fun z => f y * z) hω)
      refine ⟨fun ω => n * H ω, hHm.const_mul n, ?_⟩
      exact hHe.mono fun ω hω => congrArg (fun z => n * z) hω

  have hblock_L2
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L side : ℝ) (c : Vec d)
      (f : Vec d → ℝ) (hf : Measurable f) (b : ℝ)
      (hb : ∀ y ∈ clockBlockCube c side, |f y| ≤ b)
      (hsize : MemLp (fun ω => covarianceVectorSize
        (covarianceBlock d hd D s δ γ η β h Q r L side c f ω)) 2 (reducedLaw Q)) :
      L2Vec (reducedLaw Q) (covarianceBlock d hd D s δ γ η β h Q r L side c f) ∧
        ∀ a, (∫ ω, covarianceBlock d hd D s δ γ η β h Q r L side c f ω a
          ∂reducedLaw Q) = 0 := by
    have hc (a : JointObservationIndex d) := hweighted Q hQ r hr a
      (clockBlockCube c side) Set.univ (measurableSet_clockBlockCube _ _)
      (volume_clockBlockCube_lt_top _ _) (fun _ _ _ _ => Set.mem_univ _)
      f hf b hb (L ^ (-(d : ℝ) / 2))
    exact ⟨⟨fun a => (hc a).1.aestronglyMeasurable, hsize⟩, fun a => (hc a).2.1⟩

  -- Two residue classes in each coordinate suffice for untrimmed cubes.
  have hresidue_separated {L ρ : ℝ} (hL : 0 ≤ L)
      {j k : Fin d → ℤ} (hjk : j ≠ k)
      (hcol : ∀ i, j i % 2 = k i % 2)
      {x y : Vec d}
      (hx : x ∈ clockBlockCube (covarianceTileCenter L j) (L + 2 * ρ))
      (hy : y ∈ clockBlockCube (covarianceTileCenter L k) (L + 2 * ρ)) :
      L - 2 * ρ ≤ euclideanNorm (x - y) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hjk
    have hz : (2 : ℤ) ≤ |j i - k i| := by
      have hh := hcol i
      rcases le_total (j i) (k i) with hle | hge
      · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
        omega
      · rw [abs_of_nonneg (sub_nonneg.mpr hge)]
        omega
    have hr : (2 : ℝ) ≤ |(j i : ℝ) - (k i : ℝ)| := by exact_mod_cast hz
    have hc : 2 * L ≤ |covarianceTileCenter L j i - covarianceTileCenter L k i| := by
      simpa only [covarianceTileCenter, ← mul_sub, abs_mul, abs_of_nonneg hL, mul_comm]
        using mul_le_mul_of_nonneg_left hr hL
    have hx' := mem_clockBlockCube_iff.mp hx i
    have hy' := mem_clockBlockCube_iff.mp hy i
    apply le_trans _ (abs_coord_le_euclideanNorm (x - y) i)
    rw [Pi.sub_apply]
    rcases le_or_gt (covarianceTileCenter L j i) (covarianceTileCenter L k i) with hle | hgt
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)] at hc
      exact (by linarith : L - 2 * ρ ≤ -(x i - y i)).trans (neg_le_abs _)
    · rw [abs_of_nonneg (sub_nonneg.mpr hgt.le)] at hc
      exact (by linarith : L - 2 * ρ ≤ x i - y i).trans (le_abs_self _)

  have hweighted_independent
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L : ℝ) (hL : 0 ≤ L)
      (hs : D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ r)
      (col : Fin d → ℤ)
      (f : (Fin d → ℤ) → Vec d → ℝ) (hf : ∀ j, Measurable (f j))
      (b : (Fin d → ℤ) → ℝ)
      (hb : ∀ j, ∀ y ∈ clockBlockCube (covarianceTileCenter L j) L, |f j y| ≤ b j) :
      iIndepFun (fun j : {j : Fin d → ℤ // ∀ i, j i % 2 = col i} =>
        covarianceBlock d hd D s δ γ η β h Q r L L
          (covarianceTileCenter L j) (f j)) (reducedLaw Q) := by
    haveI := reducedLaw_probability Q
    let ρ := covarianceLocalizationRadius D δ r
    let J := {j : Fin d → ℤ // ∀ i, j i % 2 = col i}
    let U : J → Set (Vec d) := fun j =>
      clockBlockCube (covarianceTileCenter L j) (L + 2 * ρ)
    have hlocal (j : J) (a : JointObservationIndex d) :
        ∃ H : FieldPair d → ℝ, StronglyMeasurable[EinsteinRelation.localSigma (U j)] H ∧
          (fun ω => covarianceBlock d hd D s δ γ η β h Q r L L
            (covarianceTileCenter L j) (f j) ω a) =ᵐ[reducedLaw Q] H := by
      have hCU : ∀ y ∈ clockBlockCube (covarianceTileCenter L j) L,
          ball y ρ ⊆ U j := by
        intro y hy z hz
        apply mem_clockBlockCube_iff.mpr
        intro i
        have hcoord := abs_coord_le_euclideanNorm (z - y) i
        have hdiff := abs_lt.1 (lt_of_le_of_lt hcoord hz)
        have hcube := mem_clockBlockCube_iff.mp hy i
        simp only [Pi.sub_apply] at hdiff
        exact ⟨by linarith [hdiff.1, hcube.1], by linarith [hdiff.2, hcube.2]⟩
      exact (hweighted Q hQ r hr a _ (U j) (measurableSet_clockBlockCube _ _)
        (volume_clockBlockCube_lt_top _ _) hCU (f j) (hf j) (b j) (hb j)
        (L ^ (-(d : ℝ) / 2))).2.2
    choose H hHm hHe using hlocal
    have hind := iIndepFun_of_local (reducedLaw_hasFiniteRange Q) U
      (fun _ => measurableSet_clockBlockCube _ _) hs
      (fun j k hjk x hx y hy => hresidue_separated hL
        (fun he => hjk (Subtype.ext he)) (fun i => (j.2 i).trans (k.2 i).symm) hx hy)
      (g := fun j ω a => H j a ω)
      (f := fun j ω a => covarianceBlock d hd D s δ γ η β h Q r L L
        (covarianceTileCenter L j) (f j) ω a) ?_ ?_
    · exact hind
    · intro j
      letI : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma (U j)
      exact measurable_pi_iff.mpr fun a => (hHm j a).measurable
    · intro j
      filter_upwards [ae_all_iff.mpr (hHe j)] with ω hω
      exact funext fun a => hω a

  -- Encode the 2^d parity classes by a finite color type.
  let tileColor : (Fin d → ℤ) → Fin (Fintype.card (Fin d → Fin 2)) := fun j =>
    (Fintype.equivFin (Fin d → Fin 2))
      (fun i => ⟨(j i % 2).toNat, by omega⟩)
  have htileColor {j k : Fin d → ℤ} (hc : tileColor j = tileColor k) :
      ∀ i, j i % 2 = k i % 2 := by
    have he := (Fintype.equivFin (Fin d → Fin 2)).injective hc
    intro i
    have hi := congrArg (fun f : Fin d → Fin 2 => (f i).val) he
    dsimp only at hi
    omega

  have hcomplex_coordinate_independent
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L : ℝ) (hL : 0 ≤ L)
      (hs : D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ r)
      (f : (Fin d → ℤ) → Vec d → ℝ) (hf : ∀ j, Measurable (f j))
      (b : (Fin d → ℤ) → ℝ)
      (hb : ∀ j, ∀ y ∈ clockBlockCube (covarianceTileCenter L j) L, |f j y| ≤ b j)
      (a : JointObservationIndex d) (j k : Fin d → ℤ)
      (hc : tileColor j = tileColor k) (hjk : j ≠ k) :
      IndepFun
        (fun ω => (covarianceBlock d hd D s δ γ η β h Q r L L
          (covarianceTileCenter L j) (f j) ω a : ℂ))
        (fun ω => (covarianceBlock d hd D s δ γ η β h Q r L L
          (covarianceTileCenter L k) (f k) ω a : ℂ)) (reducedLaw Q) := by
    let J := {k : Fin d → ℤ // ∀ i, k i % 2 = j i % 2}
    let jj : J := ⟨j, fun _ => rfl⟩
    let kk : J := ⟨k, fun i => (htileColor hc i).symm⟩
    have hind := hweighted_independent Q hQ r hr L hL hs (fun i => j i % 2) f hf b hb
    have hp := hind.indepFun (i := jj) (j := kk) (fun he => hjk (congrArg Subtype.val he))
    exact hp.comp (Complex.measurable_ofReal.comp (measurable_pi_apply a))
      (Complex.measurable_ofReal.comp (measurable_pi_apply a))

  have hcomplex_coordinate_norm
      {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
      (μ : Measure Ω) (X : Ω → ι → ℝ) (hX : L2Vec μ X) (a : ι) :
      ‖((hX.coord_memLp a).ofReal).toLp (fun ω => (X ω a : ℂ))‖ ≤ vl2 μ X := by
    rw [← l2Size_eq_norm_toLp (f := fun ω => (X ω a : ℂ))
      ((hX.coord_memLp a).ofReal)]
    apply Real.sqrt_le_sqrt
    apply integral_mono ((hX.coord_memLp a).ofReal).norm.integrable_sq
      hX.size_memLp.integrable_sq
    intro ω
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_le_vsize (X ω) a

  have hβη : η < β := by
    have hδ : 0 < δ := h.2.2.2.1
    have hβ : η * (1 + δ) < β := h.2.2.2.2.2.2.2.2.2.1
    nlinarith [mul_pos hηlower hδ]
  obtain ⟨Lp, hLp, hparityThreshold⟩ := recursion_thresholds D.one_le_dependenceRange
    h.2.2.2.1 hηlower hβη h.2.2.2.2.2.2.2.2.2.1
  have hparity_separation {L : ℝ} (hL : max Lp 2 ≤ L) :
      D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ (L ^ η) := by
    have h1 : 1 ≤ L := by have := (le_max_right Lp 2).trans hL; linarith
    have hβ : β < 1 := h.2.2.2.2.2.2.2.2.2.2
    have hpow : L ^ β ≤ L :=
      (Real.rpow_le_rpow_of_exponent_le h1 hβ.le).trans_eq (Real.rpow_one L)
    have hs := (hparityThreshold L ((le_max_left _ _).trans hL)).2.2
    change D.dependenceRange < L - 2 * (D.dependenceRange *
      (L ^ η / D.dependenceRange) ^ (1 + δ))
    linarith

  -- The same order N gives both absolute summability and the mesh-normalized
  -- square sum. The square estimate is the cancellation needed for L² scaling.
  have hdecay_weights {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (A : ℝ) :
      Summable (fun j : Fin d → ℤ => A *
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ∧
      Summable (fun j : Fin d → ℤ => (A *
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2) ∧
      a ^ d * (∑' j : Fin d → ℤ, (A *
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2) ≤
        A ^ 2 * 3 ^ d := by
    have hN0 : 2 * d ≤ N := by omega
    have hN2 : 2 * d ≤ N * 2 := by omega
    have he (j : Fin d → ℤ) : (A *
        ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2 =
        A ^ 2 * ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (N * 2))⁻¹ := by
      rw [mul_pow, inv_pow, ← pow_mul]
    refine ⟨(summable_lattice_euclidean_decay ha hN0).mul_left A, ?_, ?_⟩
    · simp_rw [he]
      exact (summable_lattice_euclidean_decay ha hN2).mul_left (A ^ 2)
    · simp_rw [he]
      rw [tsum_mul_left]
      calc
        a ^ d * (A ^ 2 * ∑' j : Fin d → ℤ,
            ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (N * 2))⁻¹) =
            A ^ 2 * (a ^ d * ∑' j : Fin d → ℤ,
            ((1 + euclideanNorm (covarianceTileCenter a j)) ^ (N * 2))⁻¹) := by ring
        _ ≤ A ^ 2 * 3 ^ d := mul_le_mul_of_nonneg_left
          (mesh_tsum_lattice_euclidean_decay_le ha ha1 hN2) (sq_nonneg A)

  -- Absolute integrability is established on the whole spatial product before
  -- using Fubini or identifying a pointwise integral with its cube series.
  have hglobal_weighted_integrable
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (a : JointObservationIndex d)
      (k : Vec d → ℝ) (hkm : Measurable k) (hki : Integrable k volume) :
      Integrable (fun p : Vec d × FieldPair d =>
        k p.1 * covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2 a)
        (volume.prod (reducedLaw Q)) := by
    haveI := reducedLaw_probability Q
    have hf := cov_lsf hjl d hd D s δ γ η β h Q hQ r hr a
    have hm := (hkm.comp measurable_fst).aestronglyMeasurable.mul hf.meas
    apply (integrable_prod_iff hm).mpr
    refine ⟨Filter.Eventually.of_forall (fun x =>
      ((hf.memLp x).integrable one_le_two).const_mul (k x)), ?_⟩
    have he (x : Vec d) :
        (∫ ω, ‖k x * covarianceLocalizedField d hd D s δ γ η β h Q r x ω a‖
          ∂reducedLaw Q) = ‖k x‖ *
          ∫ ω, ‖covarianceLocalizedField d hd D s δ γ η β h Q r 0 ω a‖
          ∂reducedLaw Q := by
      simp_rw [norm_mul]
      rw [integral_const_mul]
      exact congrArg (fun t => ‖k x‖ * t) (hf.integral_norm_eq (reducedLaw_hT Q) x)
    exact (hki.norm.mul_const _).congr (Filter.Eventually.of_forall fun x => (he x).symm)

  have hglobal_complex_integrable
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (a : JointObservationIndex d)
      (k : Vec d → ℂ) (hkm : Measurable k) (hki : Integrable k volume) :
      Integrable (fun p : Vec d × FieldPair d =>
        k p.1 * (covarianceLocalizedField d hd D s δ γ η β h Q r p.1 p.2 a : ℂ))
        (volume.prod (reducedLaw Q)) := by
    have hre := hglobal_weighted_integrable Q hQ r hr a (fun x => (k x).re)
      (Complex.measurable_re.comp hkm) hki.re
    have him := hglobal_weighted_integrable Q hQ r hr a (fun x => (k x).im)
      (Complex.measurable_im.comp hkm) hki.im
    apply (hre.ofReal.add (him.ofReal.mul_const Complex.I)).congr
    apply Filter.Eventually.of_forall
    intro p
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

  have hpairing_tiling
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L R : ℝ)
      (hL : 0 < L) (hR : 0 < R)
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      ∀ᵐ ω ∂reducedLaw Q, HasSum
        (fun j : Fin d → ℤ => ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          ∫ x in clockBlockCube (covarianceTileCenter L j) L,
            ∑ a, F (R⁻¹ • x) a *
              (covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℂ))
        (covarianceLocalizedPairing d hd D s δ γ η β h Q R r F ω) := by
    have hk : Integrable (fun x : Vec d => ‖F (R⁻¹ • x)‖) volume :=
      (integrable_comp_smul_iff volume (fun x => ‖F x‖) (inv_ne_zero hR.ne')).2
        F.integrable.norm
    have hcoord (a : JointObservationIndex d) :
        Integrable (fun x : Vec d => F (R⁻¹ • x) a) volume :=
      hk.mono' (by fun_prop) (Filter.Eventually.of_forall fun x =>
        PiLp.norm_apply_le (F (R⁻¹ • x)) a)
    have hg (a : JointObservationIndex d) := hglobal_complex_integrable Q hQ r hr a
      (fun x => F (R⁻¹ • x) a) (by fun_prop) (hcoord a)
    have hsum := integrable_finsetSum Finset.univ (fun a _ => hg a)
    filter_upwards [hsum.prod_left_ae] with ω hω
    exact (hasSum_integral_lattice_cubes hL hω).mul_left _

  -- Package the exact scalar complex input required by the colored-series
  -- estimate, retaining genuine MemLp and the centered integral separately.
  have hblock_complex_data
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L side : ℝ) (c : Vec d)
      (f : Vec d → ℝ) (hf : Measurable f) (b : ℝ)
      (hb : ∀ y ∈ clockBlockCube c side, |f y| ≤ b)
      (hsize : MemLp (fun ω => covarianceVectorSize
        (covarianceBlock d hd D s δ γ η β h Q r L side c f ω)) 2 (reducedLaw Q))
      (B : ℝ) (hB : covarianceL2Size (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q r L side c f) ≤ B)
      (a : JointObservationIndex d) :
      let X := fun ω => (covarianceBlock d hd D s δ γ η β h Q r L side c f ω a : ℂ)
      MemLp X 2 (reducedLaw Q) ∧ (∫ ω, X ω ∂reducedLaw Q) = 0 ∧
        covarianceComplexL2Size (reducedLaw Q) X ≤ B := by
    obtain ⟨hvec, hmean⟩ := hblock_L2 Q hQ r hr L side c f hf b hb hsize
    have hm : MemLp (fun ω =>
        (covarianceBlock d hd D s δ γ η β h Q r L side c f ω a : ℂ))
        2 (reducedLaw Q) := (hvec.coord_memLp a).ofReal
    refine ⟨hm, ?_, ?_⟩
    · rw [integral_complex_ofReal, hmean a, Complex.ofReal_zero]
    · change l2Size (reducedLaw Q) _ ≤ B
      rw [l2Size_eq_norm_toLp hm]
      exact (hcomplex_coordinate_norm (reducedLaw Q) _ hvec a).trans hB

  have hnormalization {L R : ℝ} (hL : 0 < L) (hR : 0 < R) :
      ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) =
        (((L / R) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ((L ^ (-(d : ℝ) / 2) : ℝ) : ℂ) := by
    have he : (L / R) ^ ((d : ℝ) / 2) * L ^ (-(d : ℝ) / 2) =
        R ^ (-(d : ℝ) / 2) := by
      rw [Real.div_rpow hL.le hR.le, div_mul_eq_mul_div, ← Real.rpow_add hL]
      rw [show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring, Real.rpow_zero, one_div]
      rw [show -(d : ℝ) / 2 = -((d : ℝ) / 2) by ring, Real.rpow_neg hR.le]
    exact_mod_cast he.symm

  have hcube_error_identity (c : Vec d) (L w : ℝ) (hw : 0 ≤ w)
      (g : Vec d → ℝ) (k : Vec d → ℂ)
      (hg : IntegrableOn g (clockBlockCube c L) volume)
      (hkg : IntegrableOn (fun x => k x * (g x : ℂ)) (clockBlockCube c L) volume) :
      (∫ x in clockBlockCube c L, k x * (g x : ℂ)) -
          k c * ((∫ x in clockBlockCube c (L - w), g x : ℝ) : ℂ) =
        ((∫ x in clockBlockCube c L, (k x - k c).re * g x : ℝ) : ℂ) +
        ((∫ x in clockBlockCube c L, (k x - k c).im * g x : ℝ) : ℂ) * Complex.I +
        k c * ((∫ x in clockBlockCube c L,
          (clockBlockCube c (L - w))ᶜ.indicator (fun _ => (1 : ℝ)) x * g x : ℝ) : ℂ) := by
    have hconst := hg.ofReal.const_mul (k c)
    have hv : IntegrableOn (fun x => (k x - k c) * (g x : ℂ))
        (clockBlockCube c L) volume := by
      apply (hkg.sub hconst).congr
      exact Filter.Eventually.of_forall fun x => (sub_mul _ _ _).symm
    have hsplit :
        ((∫ x in clockBlockCube c L, (k x - k c).re * g x : ℝ) : ℂ) +
        ((∫ x in clockBlockCube c L, (k x - k c).im * g x : ℝ) : ℂ) * Complex.I =
        ∫ x in clockBlockCube c L, (k x - k c) * (g x : ℂ) := by
      simpa [Complex.mul_re, Complex.mul_im] using setIntegral_re_add_im hv
    have hdiff : (∫ x in clockBlockCube c L, (k x - k c) * (g x : ℂ)) =
        (∫ x in clockBlockCube c L, k x * (g x : ℂ)) -
          k c * ((∫ x in clockBlockCube c L, g x : ℝ) : ℂ) := by
      simp_rw [sub_mul]
      calc
        _ = (∫ x in clockBlockCube c L, k x * (g x : ℂ)) -
            ∫ x in clockBlockCube c L, k c * (g x : ℂ) := by
          exact integral_sub hkg hconst
        _ = _ := by rw [integral_const_mul, integral_complex_ofReal]
    have hstrip := setIntegral_sub_indicator (S := clockBlockCube c L)
      (T := clockBlockCube c (L - w)) (measurableSet_clockBlockCube _ _)
      (clockBlockCube_mono' c (by linarith)) hg
    simp only [one_mul] at hstrip
    rw [hsplit, hdiff, ← hstrip]
    push_cast
    ring

  have hmesh_sqrt_bound {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (A : ℝ) :
      a ^ ((d : ℝ) / 2) * Real.sqrt
        (∑' j : Fin d → ℤ, (A *
          ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2) ≤
        |A| * Real.sqrt ((3 : ℝ) ^ d) := by
    have he : (a ^ ((d : ℝ) / 2)) ^ 2 = a ^ d := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
      rw [show (d : ℝ) / 2 * (2 : ℕ) = (d : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    apply (sq_le_sq₀ (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.sqrt_nonneg _))
      (mul_nonneg (abs_nonneg A) (Real.sqrt_nonneg _))).mp
    rw [mul_pow, he, Real.sq_sqrt (tsum_nonneg fun _ => sq_nonneg _),
      mul_pow, sq_abs, Real.sq_sqrt (pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) d)]
    exact (hdecay_weights ha ha1 A).2.2

  have hcolored_block_series
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (r : ℝ) (hr : 2 * D.dependenceRange ≤ r) (L R : ℝ) (hL : 0 < L) (hLR : L ≤ R)
      (hsep : D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ r)
      (f : (Fin d → ℤ) → Vec d → ℝ) (hf : ∀ j, Measurable (f j))
      (b : (Fin d → ℤ) → ℝ)
      (hb : ∀ j, ∀ y ∈ clockBlockCube (covarianceTileCenter L j) L, |f j y| ≤ b j)
      (hsize : ∀ j, MemLp (fun ω => covarianceVectorSize
        (covarianceBlock d hd D s δ γ η β h Q r L L
          (covarianceTileCenter L j) (f j) ω)) 2 (reducedLaw Q))
      (B : (Fin d → ℤ) → ℝ)
      (hB : ∀ j, covarianceL2Size (reducedLaw Q)
        (covarianceBlock d hd D s δ γ η β h Q r L L
          (covarianceTileCenter L j) (f j)) ≤ B j)
      (z : (Fin d → ℤ) → ℂ) (A : ℝ)
      (hmajor : ∀ j, ‖z j‖ * B j ≤ A *
        ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹)
      (a : JointObservationIndex d) :
      let Y := fun j ω => z j * (covarianceBlock d hd D s δ γ η β h Q r L L
        (covarianceTileCenter L j) (f j) ω a : ℂ)
      (∀ᵐ ω ∂reducedLaw Q, Summable (fun j => Y j ω)) ∧
      MemLp (fun ω => ∑' j, Y j ω) 2 (reducedLaw Q) ∧
      covarianceComplexL2Size (reducedLaw Q) (fun ω => ∑' j, Y j ω) ≤
        (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt
          (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹) ^ 2) := by
    haveI := reducedLaw_probability Q
    have hR : 0 < R := hL.trans_le hLR
    have ha := div_pos hL hR
    have ha1 := (div_le_one hR).mpr hLR
    let X := fun j ω => (covarianceBlock d hd D s δ γ η β h Q r L L
      (covarianceTileCenter L j) (f j) ω a : ℂ)
    have hdata (j : Fin d → ℤ) := hblock_complex_data Q hQ r hr L L
      (covarianceTileCenter L j) (f j) (hf j) (b j) (hb j) (hsize j) (B j) (hB j) a
    have hm (j : Fin d → ℤ) : MemLp (fun ω => z j * X j ω) 2 (reducedLaw Q) :=
      (hdata j).1.const_mul (z j)
    have hmean (j : Fin d → ℤ) :
        (∫ ω, z j * X j ω ∂reducedLaw Q) = 0 := by
      rw [integral_const_mul, (hdata j).2.1, mul_zero]
    have hind (j k : Fin d → ℤ) (hc : tileColor j = tileColor k) (hjk : j ≠ k) :
        IndepFun (fun ω => z j * X j ω) (fun ω => z k * X k ω) (reducedLaw Q) :=
      (hcomplex_coordinate_independent Q hQ r hr L hL.le hsep f hf b hb a j k hc hjk).comp
        (measurable_id.const_mul (z j)) (measurable_id.const_mul (z k))
    have hnorm (j : Fin d → ℤ) :
        ‖(hm j).toLp (fun ω => z j * X j ω)‖ ≤ A *
          ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹ := by
      change ‖((hdata j).1.const_smul (z j)).toLp (z j • X j)‖ ≤ _
      rw [MemLp.toLp_const_smul, norm_smul]
      have hv : ‖(hdata j).1.toLp (X j)‖ ≤ B j := by
        rw [← l2Size_eq_norm_toLp (f := X j) (hdata j).1]
        exact (hdata j).2.2
      exact (mul_le_mul_of_nonneg_left hv (norm_nonneg _)).trans (hmajor j)
    exact colored_complex_series_L2 tileColor (fun j ω => z j * X j ω) hm hmean hind _
      hnorm (hdecay_weights ha ha1 A).1 (hdecay_weights ha ha1 A).2.1

  have hscaled_center (L R : ℝ) (j : Fin d → ℤ) :
      R⁻¹ • covarianceTileCenter L j = covarianceTileCenter (L / R) j := by
    funext i
    simp only [covarianceTileCenter, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  have htest_value_decay
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (x : Vec d) (a : JointObservationIndex d) :
      ‖F x a‖ ≤ schwartzTestNorm N F * ((1 + euclideanNorm x) ^ N)⁻¹ := by
    have hw : (1 + euclideanNorm x) ^ N * ‖F x‖ ≤ schwartzTestNorm N F := by
      apply le_csSup (schwartzTestNorm_set_bddAbove N F)
      exact ⟨⟨0, by omega⟩, Fin.elim0, x, by simp only [iteratedFDeriv_zero_apply]⟩
    have hp : 0 < (1 + euclideanNorm x) ^ N := by unfold euclideanNorm; positivity
    apply (PiLp.norm_apply_le (F x) a).trans
    rw [← div_eq_mul_inv]
    exact (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hw)

  have hstrip_series
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (L : ℝ) (hL : Lb ≤ L) (R : ℝ) (hLR : L ≤ R)
      (hr : 2 * D.dependenceRange ≤ L ^ η)
      (hsep : D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ (L ^ η))
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (a : JointObservationIndex d) :
      let f := fun j : Fin d → ℤ =>
        (clockBlockCube (covarianceTileCenter L j) (L - L ^ β))ᶜ.indicator
          (fun _ => (1 : ℝ))
      let Y := fun j ω => F (R⁻¹ • covarianceTileCenter L j) a *
        (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L
          (covarianceTileCenter L j) (f j) ω a : ℂ)
      let A := Cb * L ^ (-(1 - β) / 2) * schwartzTestNorm N F
      (∀ᵐ ω ∂reducedLaw Q, Summable (fun j => Y j ω)) ∧
      MemLp (fun ω => ∑' j, Y j ω) 2 (reducedLaw Q) ∧
      covarianceComplexL2Size (reducedLaw Q) (fun ω => ∑' j, Y j ω) ≤
        (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt
          (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹) ^ 2) := by
    have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < Lb) hL
    let f := fun j : Fin d → ℤ =>
      (clockBlockCube (covarianceTileCenter L j) (L - L ^ β))ᶜ.indicator
        (fun _ => (1 : ℝ))
    have hfm (j : Fin d → ℤ) : Measurable (f j) :=
      measurable_const.indicator (measurableSet_clockBlockCube _ _).compl
    have hfb (j : Fin d → ℤ) (y : Vec d) (_hy :
        y ∈ clockBlockCube (covarianceTileCenter L j) L) : |f j y| ≤ 1 := by
      by_cases hy : y ∈ (clockBlockCube (covarianceTileCenter L j) (L - L ^ β))ᶜ
      · simp only [f, Set.indicator_of_mem hy, abs_one, le_refl]
      · simp only [f, Set.indicator_of_notMem hy, abs_zero, zero_le_one]
    have hs (j : Fin d → ℤ) := hstrip Q hQ L hL (covarianceTileCenter L j)
    apply hcolored_block_series Q hQ (L ^ η) hr L R hLpos hLR hsep
      f hfm (fun _ => 1) hfb (fun j => (hs j).1)
      (fun _ => Cb * L ^ (-(1 - β) / 2)) (fun j => (hs j).2)
      (fun j => F (R⁻¹ • covarianceTileCenter L j) a)
      (Cb * L ^ (-(1 - β) / 2) * schwartzTestNorm N F) _ a
    intro j
    have hb := htest_value_decay F (R⁻¹ • covarianceTileCenter L j) a
    rw [hscaled_center] at hb ⊢
    calc
      _ ≤ (schwartzTestNorm N F *
          ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹) *
          (Cb * L ^ (-(1 - β) / 2)) :=
        mul_le_mul_of_nonneg_right hb (mul_nonneg hCb.le (Real.rpow_nonneg hLpos.le _))
      _ = _ := by ring

  have hosc_series
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (L : ℝ) (hL : Lc ≤ L) (R : ℝ) (hLR : L ≤ R)
      (hr : 2 * D.dependenceRange ≤ L ^ η) (hscale : L ^ η ≤ L)
      (hsep : D.dependenceRange < L - 2 * covarianceLocalizationRadius D δ (L ^ η))
      (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)))
      (φ : ℂ → ℝ) (hφm : Measurable φ) (hφb : ∀ z, |φ z| ≤ ‖z‖)
      (a : JointObservationIndex d) :
      let f := fun (j : Fin d → ℤ) x =>
        φ (F (R⁻¹ • x) a - F (R⁻¹ • covarianceTileCenter L j) a)
      let Y := fun j ω => (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L
        (covarianceTileCenter L j) (f j) ω a : ℂ)
      let A := Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2)
      (∀ᵐ ω ∂reducedLaw Q, Summable (fun j => Y j ω)) ∧
      MemLp (fun ω => ∑' j, Y j ω) 2 (reducedLaw Q) ∧
      covarianceComplexL2Size (reducedLaw Q) (fun ω => ∑' j, Y j ω) ≤
        (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt
          (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹) ^ 2) := by
    have hLpos : 0 < L := lt_of_lt_of_le (by linarith : 0 < Lc) hL
    let f := fun (j : Fin d → ℤ) x =>
      φ (F (R⁻¹ • x) a - F (R⁻¹ • covarianceTileCenter L j) a)
    let E := fun j : Fin d → ℤ =>
      ((2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) *
        ((1 + euclideanNorm (R⁻¹ • covarianceTileCenter L j)) ^ N)⁻¹) * ((L / R) / 2)
    have hfm (j : Fin d → ℤ) : Measurable (f j) := hφm.comp (by fun_prop)
    have hfb (j : Fin d → ℤ) (x : Vec d)
        (hx : x ∈ clockBlockCube (covarianceTileCenter L j) L) : |f j x| ≤ E j :=
      (hφb _).trans ((PiLp.norm_apply_le
        (F (R⁻¹ • x) - F (R⁻¹ • covarianceTileCenter L j)) a).trans
          (hosc hLpos hLR F (covarianceTileCenter L j) x hx))
    have hs (j : Fin d → ℤ) := hcltQ Q hQ L hL (covarianceTileCenter L j)
      (f j) (E j) (hfm j) (hosc_nonneg hLpos hLR F _) (hfb j) (L ^ η) le_rfl hscale
    have hmj (j : Fin d → ℤ) : ‖(1 : ℂ)‖ * (Cc * E j) ≤
        (Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2)) *
          ((1 + euclideanNorm (covarianceTileCenter (L / R) j)) ^ N)⁻¹ := by
      simp only [norm_one, one_mul]
      dsimp only [E]
      rw [hscaled_center]
      exact le_of_eq (by ring)
    simpa only [one_mul] using hcolored_block_series Q hQ (L ^ η) hr L R hLpos hLR hsep
      f hfm E hfb (fun j => (hs j).1) (fun j => Cc * E j) (fun j => (hs j).2)
      (fun _ => 1)
      (Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2)) hmj a

  have hnormalized_cube_error
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (r L w : ℝ) (hw : 0 ≤ w)
      (c : Vec d) (ω : FieldPair d) (a : JointObservationIndex d) (k : Vec d → ℂ)
      (hg : IntegrableOn
        (fun x => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a)
        (clockBlockCube c L) volume)
      (hkg : IntegrableOn
        (fun x => k x * (covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℂ))
        (clockBlockCube c L) volume) :
      ((L ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          (∫ x in clockBlockCube c L,
            k x * (covarianceLocalizedField d hd D s δ γ η β h Q r x ω a : ℂ)) -
        k c * (covarianceBlock d hd D s δ γ η β h Q r L (L - w) c (fun _ => 1) ω a : ℂ) =
      (covarianceBlock d hd D s δ γ η β h Q r L L c
        (fun x => (k x - k c).re) ω a : ℂ) +
      (covarianceBlock d hd D s δ γ η β h Q r L L c
        (fun x => (k x - k c).im) ω a : ℂ) * Complex.I +
      k c * (covarianceBlock d hd D s δ γ η β h Q r L L c
        ((clockBlockCube c (L - w))ᶜ.indicator (fun _ => 1)) ω a : ℂ) := by
    have he := hcube_error_identity c L w hw
      (fun x => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a) k hg hkg
    simp only [covarianceBlock, one_mul, Complex.ofReal_mul]
    linear_combination ((L ^ (-(d : ℝ) / 2) : ℝ) : ℂ) * he

  have hscaled_series_bound
      (μ : Measure (FieldPair d))
      {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (A : ℝ) (X : FieldPair d → ℂ)
      (hm : MemLp X 2 μ)
      (hb : covarianceComplexL2Size μ X ≤
        (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt
          (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2)) :
      MemLp (fun ω => ((a ^ ((d : ℝ) / 2) : ℝ) : ℂ) * X ω) 2 μ ∧
      covarianceComplexL2Size μ (fun ω => ((a ^ ((d : ℝ) / 2) : ℝ) : ℂ) * X ω) ≤
        (Fintype.card (Fin d → Fin 2) : ℝ) * |A| * Real.sqrt ((3 : ℝ) ^ d) := by
    let q : ℝ := a ^ ((d : ℝ) / 2)
    have hq : 0 ≤ q := Real.rpow_nonneg ha.le _
    refine ⟨hm.const_mul (q : ℂ), ?_⟩
    have he : covarianceComplexL2Size μ (fun ω => (q : ℂ) * X ω) =
        q * covarianceComplexL2Size μ X := by
      change l2Size μ (fun ω => (q : ℂ) * X ω) = q * l2Size μ X
      rw [l2Size_eq_norm_toLp (hm.const_mul (q : ℂ)), l2Size_eq_norm_toLp hm]
      change ‖(hm.const_smul (q : ℂ)).toLp ((q : ℂ) • X)‖ = _
      rw [MemLp.toLp_const_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hq]
    rw [he]
    calc
      q * covarianceComplexL2Size μ X ≤ q *
          ((Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt
          (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left hb hq
      _ = (Fintype.card (Fin d → Fin 2) : ℝ) *
          (q * Real.sqrt (∑' j : Fin d → ℤ, (A *
            ((1 + euclideanNorm (covarianceTileCenter a j)) ^ N)⁻¹) ^ 2)) := by ring
      _ ≤ (Fintype.card (Fin d → Fin 2) : ℝ) *
          (|A| * Real.sqrt ((3 : ℝ) ^ d)) :=
        mul_le_mul_of_nonneg_left (hmesh_sqrt_bound ha ha1 A) (Nat.cast_nonneg _)
      _ = _ := by ring

  obtain ⟨Lt, hLt, htrimmed⟩ := covarianceTestBlocks_summable_memLp hclt hjl
    d hd D s δ γ η β h N (by omega)
  let C0 : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) *
    (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt ((3 : ℝ) ^ d) *
      (Cc * (2 + (d : ℝ)) ^ N * (d : ℝ) + Cb)
  let L0 : ℝ := max (max (max Lc Lb) Ls) (max (max Lp 2) Lt)
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0 + 1, L0, by linarith, ?_, ?_⟩
  · exact hLt.trans ((le_max_right (max Lp 2) Lt).trans (le_max_right _ _))
  intro Q hQ L hL R hLR F
  haveI := reducedLaw_probability Q
  obtain ⟨h2, hLcL, hLbL, hr, hscale⟩ := hthreshold ((le_max_left _ _).trans hL)
  have hLpos : 0 < L := by linarith
  have hR : 0 < R := hLpos.trans_le hLR
  have hsep := hparity_separation ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hLtL : Lt ≤ L := (le_max_right (max Lp 2) Lt).trans ((le_max_right _ _).trans hL)
  have ha := div_pos hLpos hR
  have ha1 := (div_le_one hR).mpr hLR
  have hRe (a : JointObservationIndex d) := hosc_series Q hQ L hLcL R hLR hr hscale hsep
    F Complex.re Complex.measurable_re Complex.abs_re_le_norm a
  have hIm (a : JointObservationIndex d) := hosc_series Q hQ L hLcL R hLR hr hscale hsep
    F Complex.im Complex.measurable_im Complex.abs_im_le_norm a
  have hStrip (a : JointObservationIndex d) := hstrip_series Q hQ L hLbL R hLR hr hsep F a
  have hReScaled (a : JointObservationIndex d) := hscaled_series_bound (reducedLaw Q)
    ha ha1 (Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2))
    _ (hRe a).2.1 (hRe a).2.2
  have hImScaled (a : JointObservationIndex d) := hscaled_series_bound (reducedLaw Q)
    ha ha1 (Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2))
    _ (hIm a).2.1 (hIm a).2.2
  have hStripScaled (a : JointObservationIndex d) := hscaled_series_bound (reducedLaw Q)
    ha ha1 (Cb * L ^ (-(1 - β) / 2) * schwartzTestNorm N F)
    _ (hStrip a).2.1 (hStrip a).2.2
  have htiles := hpairing_tiling Q hQ (L ^ η) hr L R hLpos hR F
  have htr := htrimmed Q hQ L hLtL R hR F
  let q : ℂ := ((L / R) ^ ((d : ℝ) / 2) : ℝ)
  let U := fun (j : Fin d → ℤ) (ω : FieldPair d) (a : JointObservationIndex d) =>
    (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L (covarianceTileCenter L j)
      (fun x => (F (R⁻¹ • x) a - F (R⁻¹ • covarianceTileCenter L j) a).re) ω a : ℂ)
  let V := fun (j : Fin d → ℤ) (ω : FieldPair d) (a : JointObservationIndex d) =>
    (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L (covarianceTileCenter L j)
      (fun x => (F (R⁻¹ • x) a - F (R⁻¹ • covarianceTileCenter L j) a).im) ω a : ℂ)
  let W := fun (j : Fin d → ℤ) (ω : FieldPair d) (a : JointObservationIndex d) =>
    F (R⁻¹ • covarianceTileCenter L j) a *
      (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L L (covarianceTileCenter L j)
        ((clockBlockCube (covarianceTileCenter L j) (L - L ^ β))ᶜ.indicator
          (fun _ => 1)) ω a : ℂ)
  let Zr := fun a ω => q * ∑' j, U j ω a
  let Zi := fun a ω => q * ∑' j, V j ω a
  let Zs := fun a ω => q * ∑' j, W j ω a
  let Z := fun a ω => Zr a ω + Zi a ω * Complex.I + Zs a ω
  have hZr (a) : MemLp (Zr a) 2 (reducedLaw Q) := (hReScaled a).1
  have hZi (a) : MemLp (Zi a) 2 (reducedLaw Q) := (hImScaled a).1
  have hZs (a) : MemLp (Zs a) 2 (reducedLaw Q) := (hStripScaled a).1
  have hZ (a) : MemLp (Z a) 2 (reducedLaw Q) :=
    ((hZr a).add ((hZi a).mul_const Complex.I)).add (hZs a)
  have hsumZ : MemLp (fun ω => ∑ a, Z a ω) 2 (reducedLaw Q) :=
    memLp_finsetSum _ (fun a _ => hZ a)
  have hfield : ∀ᵐ ω ∂reducedLaw Q, ∀ (j : Fin d → ℤ) (a : JointObservationIndex d),
      IntegrableOn (fun x => covarianceLocalizedField d hd D s δ γ η β h Q
        (L ^ η) x ω a) (clockBlockCube (covarianceTileCenter L j) L) volume :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun a =>
      (cov_lsf hjl d hd D s δ γ η β h Q hQ (L ^ η) hr a).ae_integrable_slice
        (reducedLaw_hT Q) (volume_clockBlockCube_lt_top _ _)
  have hk : Integrable (fun x : Vec d => ‖F (R⁻¹ • x)‖) volume :=
    (integrable_comp_smul_iff volume (fun x => ‖F x‖) (inv_ne_zero hR.ne')).2
      F.integrable.norm
  have hweighted_ae : ∀ᵐ ω ∂reducedLaw Q, ∀ a : JointObservationIndex d,
      Integrable (fun x : Vec d => F (R⁻¹ • x) a *
        (covarianceLocalizedField d hd D s δ γ η β h Q (L ^ η) x ω a : ℂ)) volume :=
    ae_all_iff.2 fun a =>
      (hglobal_complex_integrable Q hQ (L ^ η) hr a
        (fun x => F (R⁻¹ • x) a) (by fun_prop)
        (hk.mono' (by fun_prop) (Filter.Eventually.of_forall fun x =>
          PiLp.norm_apply_le (F (R⁻¹ • x)) a))).prod_left_ae
  have hidentity : (fun ω => covarianceLocalizedPairing d hd D s δ γ η β h Q R
      (L ^ η) F ω - covarianceTestBlocks d hd D s δ γ η β h Q R L F ω) =ᵐ[reducedLaw Q]
      (fun ω => ∑ a, Z a ω) := by
    have hu : ∀ᵐ ω ∂reducedLaw Q, ∀ a, Summable (fun j => U j ω a) :=
      ae_all_iff.2 fun a => (hRe a).1
    have hv : ∀ᵐ ω ∂reducedLaw Q, ∀ a, Summable (fun j => V j ω a) :=
      ae_all_iff.2 fun a => (hIm a).1
    have hw : ∀ᵐ ω ∂reducedLaw Q, ∀ a, Summable (fun j => W j ω a) :=
      ae_all_iff.2 fun a => (hStrip a).1
    filter_upwards [htiles, htr.1, hfield, hweighted_ae, hu, hv, hw] with
      ω ht htrim hg hkg hu hv hw
    have hcoord (j : Fin d → ℤ) (a : JointObservationIndex d) :=
      hnormalized_cube_error Q (L ^ η) L (L ^ β) (Real.rpow_nonneg hLpos.le _)
        (covarianceTileCenter L j) ω a (fun x => F (R⁻¹ • x) a)
        (hg j a) ((hkg a).integrableOn)
    have heach (j : Fin d → ℤ) :
        ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) *
          (∫ x in clockBlockCube (covarianceTileCenter L j) L,
            ∑ a, F (R⁻¹ • x) a *
              (covarianceLocalizedField d hd D s δ γ η β h Q (L ^ η) x ω a : ℂ)) -
        q * (∑ a, F (R⁻¹ • covarianceTileCenter L j) a *
          (covarianceBlock d hd D s δ γ η β h Q (L ^ η) L (L - L ^ β)
            (covarianceTileCenter L j) (fun _ => 1) ω a : ℂ)) =
        ∑ a, q * (U j ω a + V j ω a * Complex.I + W j ω a) := by
      rw [integral_finsetSum _ (fun a _ => (hkg a).integrableOn)]
      rw [hnormalization hLpos hR]
      simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      rw [← hcoord j a]
      dsimp only [q]
      ring
    have herr := ht.sub (htrim.hasSum.mul_left q)
    have hright : HasSum
        (fun j => ∑ a, q * (U j ω a + V j ω a * Complex.I + W j ω a))
        (∑ a, Z a ω) := by
      apply hasSum_sum
      intro a _
      have hh := (((hu a).hasSum.add ((hv a).hasSum.mul_right Complex.I)).add
        (hw a).hasSum).mul_left q
      convert hh using 1 <;> dsimp only [Z, Zr, Zi, Zs] <;> ring
    exact (herr.congr_fun (fun j => (heach j).symm)).unique hright
  let A : ℝ := Cc * (2 + (d : ℝ)) ^ N * ((d : ℝ) * schwartzTestNorm N F) * ((L / R) / 2)
  let B : ℝ := Cb * L ^ (-(1 - β) / 2) * schwartzTestNorm N F
  let K : ℝ := (Fintype.card (Fin d → Fin 2) : ℝ) * Real.sqrt ((3 : ℝ) ^ d)
  have hn : 0 ≤ schwartzTestNorm N F := schwartz_norm_nonneg N F
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hzr (a) : l2Size (reducedLaw Q) (Zr a) ≤ K * A := by
    calc
      _ ≤ (Fintype.card (Fin d → Fin 2) : ℝ) * |A| * Real.sqrt ((3 : ℝ) ^ d) :=
        (hReScaled a).2
      _ = K * A := by rw [abs_of_nonneg hA]; dsimp [K]; ring
  have hzi (a) : l2Size (reducedLaw Q) (Zi a) ≤ K * A := by
    calc
      _ ≤ (Fintype.card (Fin d → Fin 2) : ℝ) * |A| * Real.sqrt ((3 : ℝ) ^ d) :=
        (hImScaled a).2
      _ = K * A := by rw [abs_of_nonneg hA]; dsimp [K]; ring
  have hzs (a) : l2Size (reducedLaw Q) (Zs a) ≤ K * B := by
    calc
      _ ≤ (Fintype.card (Fin d → Fin 2) : ℝ) * |B| * Real.sqrt ((3 : ℝ) ^ d) :=
        (hStripScaled a).2
      _ = K * B := by rw [abs_of_nonneg hB]; dsimp [K]; ring
  have hz (a) : l2Size (reducedLaw Q) (Z a) ≤ K * (2 * A + B) := by
    have hi : l2Size (reducedLaw Q) (fun ω => Zi a ω * Complex.I) =
        l2Size (reducedLaw Q) (Zi a) := by
      unfold l2Size
      simp only [norm_mul, Complex.norm_I, mul_one]
    have ht := (l2Size_add_le ((hZr a).add ((hZi a).mul_const Complex.I))
      (hZs a)).trans (add_le_add
        (l2Size_add_le (hZr a) ((hZi a).mul_const Complex.I)) (le_refl _))
    change l2Size (reducedLaw Q) (Z a) ≤ _ at ht
    rw [hi] at ht
    calc
      _ ≤ _ := ht
      _ ≤ K * A + K * A + K * B := add_le_add (add_le_add (hzr a) (hzi a)) (hzs a)
      _ = _ := by ring
  have hfinite (t : Finset (JointObservationIndex d)) :
      MemLp (fun ω => ∑ a ∈ t, Z a ω) 2 (reducedLaw Q) ∧
      l2Size (reducedLaw Q) (fun ω => ∑ a ∈ t, Z a ω) ≤
        (t.card : ℝ) * (K * (2 * A + B)) := by
    induction t using Finset.induction_on with
    | empty => simp [l2Size]
    | @insert a t hat ih =>
      constructor
      · simp only [Finset.sum_insert hat]
        exact (hZ a).add ih.1
      · simp only [Finset.sum_insert hat, Finset.card_insert_of_notMem hat,
          Nat.cast_add, Nat.cast_one, add_mul, one_mul]
        calc
          _ ≤ l2Size (reducedLaw Q) (Z a) +
              l2Size (reducedLaw Q) (fun ω => ∑ a ∈ t, Z a ω) :=
            l2Size_add_le (hZ a) ih.1
          _ ≤ K * (2 * A + B) + (t.card : ℝ) * (K * (2 * A + B)) :=
            add_le_add (hz a) ih.2
          _ = _ := by ring
  have hmem : MemLp (fun ω => covarianceLocalizedPairing d hd D s δ γ η β h Q R
      (L ^ η) F ω - covarianceTestBlocks d hd D s δ γ η β h Q R L F ω)
      2 (reducedLaw Q) := hsumZ.ae_eq hidentity.symm
  refine ⟨hmem, ?_⟩
  have hsize : covarianceComplexL2Size (reducedLaw Q)
      (fun ω => covarianceLocalizedPairing d hd D s δ γ η β h Q R (L ^ η) F ω -
        covarianceTestBlocks d hd D s δ γ η β h Q R L F ω) =
      l2Size (reducedLaw Q) (fun ω => ∑ a, Z a ω) := by
    unfold covarianceComplexL2Size l2Size
    rw [integral_congr_ae (hidentity.mono fun ω he => by rw [he])]
  rw [hsize]
  have hfin := (hfinite Finset.univ).2
  simp only [Finset.card_univ] at hfin
  have hfactor : (Fintype.card (JointObservationIndex d) : ℝ) * (K * (2 * A + B)) ≤
      C0 * schwartzTestNorm N F * (L / R + L ^ (-(1 - β) / 2)) := by
    let T : ℝ := Cc * (2 + (d : ℝ)) ^ N * (d : ℝ)
    let S : ℝ := (Fintype.card (JointObservationIndex d) : ℝ) * K
    have hp : 0 ≤ L ^ (-(1 - β) / 2) := Real.rpow_nonneg hLpos.le _
    have hc : 0 ≤ T := by dsimp [T]; positivity
    have hS : 0 ≤ S := mul_nonneg (Nat.cast_nonneg _) hK
    have hcross : T * (L / R) + Cb * L ^ (-(1 - β) / 2) ≤
        (T + Cb) * (L / R + L ^ (-(1 - β) / 2)) := by
      nlinarith only [mul_nonneg hc hp, mul_nonneg hCb.le ha.le]
    calc
      _ = (S * schwartzTestNorm N F) *
          (T * (L / R) + Cb * L ^ (-(1 - β) / 2)) := by dsimp [S, T, A, B]; ring
      _ ≤ (S * schwartzTestNorm N F) *
          ((T + Cb) * (L / R + L ^ (-(1 - β) / 2))) :=
        mul_le_mul_of_nonneg_left hcross (mul_nonneg hS hn)
      _ = _ := by dsimp [S, T, C0, K]; ring
  apply hfin.trans
  apply hfactor.trans
  have hp : 0 ≤ schwartzTestNorm N F * (L / R + L ^ (-(1 - β) / 2)) := by positivity
  calc
    _ = C0 * (schwartzTestNorm N F * (L / R + L ^ (-(1 - β) / 2))) := by ring
    _ ≤ (C0 + 1) * (schwartzTestNorm N F * (L / R + L ^ (-(1 - β) / 2))) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hp
    _ = _ := by ring

end EinsteinFull.Blueprint
