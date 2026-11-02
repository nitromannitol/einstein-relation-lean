import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_recursion
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_clt
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_boundary
import EinsteinFull.Blueprint.G3.node_e_u3A_block_u2D_change
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_e_u3A_parameters
import EinsteinFull.Calculus.S1RecursionCore
import EinsteinFull.Calculus.S1ThresholdSupport

/-! Reduction of graph node `e:block-recursion`, `paper/main.tex:934–948`, to the block
estimates, the joint localization and the scale window. The block estimates are first
repackaged for the abstract blocks `blk`; the recursion itself is `recursion_core`. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.S1

/-- The coordinate fields of the localized covariance construction at scale `r`. -/
noncomputable def covF (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (r : ℝ) :
    JointObservationIndex d → Vec d → FieldPair d → ℝ :=
  fun a x ω => covarianceLocalizedField d hd D s δ γ η β h Q r x ω a

theorem covarianceBlock_eq_blk (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (r L side : ℝ) (x : Vec d)
    (f : Vec d → ℝ) :
    covarianceBlock d hd D s δ γ η β h Q r L side x f =
      blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r) (clockBlockCube x side) f := rfl

theorem reducedLaw_hT {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (x : Vec d) :
    MeasurePreserving (translate x) (reducedLaw Q) (reducedLaw Q) :=
  ⟨EinsteinRelation.Probability.measurable_translate x, reducedLaw_stationary Q x⟩

private theorem cov_numeric {E E₀ t Cc B Cb : ℝ} (hE0 : 0 ≤ E) (hE : E ≤ E₀ * t)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hE₀ : 0 ≤ E₀) (hCc : 0 ≤ Cc) (hB : B ≤ Cb * t) :
    E * (2 * Cc + E) + B * (2 * Cc) ≤ (E₀ * (2 * Cc + E₀) + Cb * (2 * Cc)) * t := by
  have hE' : E ≤ E₀ := hE.trans (mul_le_of_le_one_right hE₀ ht1)
  have s1 : E * (2 * Cc + E) ≤ (E₀ * t) * (2 * Cc + E₀) :=
    mul_le_mul hE (by linarith) (by linarith) (mul_nonneg hE₀ ht0)
  have s2 : B * (2 * Cc) ≤ (Cb * t) * (2 * Cc) := mul_le_mul_of_nonneg_right hB (by linarith)
  nlinarith [s1, s2]

/-- Locality, stationarity and centering of the coordinate fields, from joint localization. -/
theorem cov_lsf (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt) (d : ℕ)
    (hd : 2 ≤ d) (D : StructuralData d) (s δ γ η β : ℝ)
    (h : covarianceWindow d D s δ γ η β) :
    ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
      ∀ r : ℝ, 2 * D.dependenceRange ≤ r → ∀ a,
        LocalStationaryField (reducedLaw Q)
          (fun x => ball x (covarianceLocalizationRadius D δ r))
          (covF d hd D s δ γ η β h Q r a) := by
  obtain ⟨Cj, hCj, -, hjlQ⟩ := hjl d hd D s δ γ η β h
  intro Q hQ r hr
  haveI := reducedLaw_probability Q
  obtain ⟨hmeas, hx⟩ := hjlQ Q hQ r hr
  exact lsf_of_vec hmeas (fun x a => ((hx x).1 a).1) (fun x a => ((hx x).1 a).2)
    (fun x => (hx x).2.1) (fun x => (hx x).2.2.1)

theorem cov_clt_data (hclt : node_e_u3A_block_u2D_cltStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ Cc Lc : ℝ, 0 < Cc ∧ 2 ≤ Lc ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
        ∀ L : ℝ, Lc ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L →
        ∀ {V : Vec d → Set (Vec d)},
          (∀ a, LocalStationaryField (reducedLaw Q) V (covF d hd D s δ γ η β h Q r a)) →
          (L2Vec (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
              (clockBlockCube 0 L) (fun _ => (1 : ℝ))) ∧
            vl2 (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
              (clockBlockCube 0 L) (fun _ => (1 : ℝ))) ≤ Cc) ∧
          (∀ w : ℝ, 0 ≤ w →
            L2Vec (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
              (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))) ∧
            vl2 (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
              (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))) ≤ Cc) := by
  obtain ⟨Cc, Lc, hCc, hLc, hcltQ⟩ := hclt d hd D s δ γ η β h
  refine ⟨Cc, Lc, hCc, hLc, ?_⟩
  intro Q hQ L hL r hr1 hr2 V hlsf
  haveI := reducedLaw_probability Q
  have hT := reducedLaw_hT Q
  refine ⟨?_, ?_⟩
  · obtain ⟨hmem, hsz⟩ := hcltQ Q hQ L hL 0 (fun _ => 1) 1 measurable_const zero_le_one
      (fun y _ => by simp) r hr1 hr2
    refine ⟨L2Vec_blk_one hlsf hT _ (volume_clockBlockCube_lt_top (0 : Vec d) L) hmem, ?_⟩
    have h1 : vl2 (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
        (clockBlockCube 0 L) (fun _ => (1 : ℝ))) ≤ Cc * 1 := hsz
    linarith
  · intro w hw
    have hfin_meas : Measurable ((clockBlockCube (0 : Vec d) (L - w)).indicator
        (fun _ => (1 : ℝ))) :=
      measurable_const.indicator (measurableSet_clockBlockCube _ _)
    obtain ⟨hmem, hsz⟩ := hcltQ Q hQ L hL 0
      ((clockBlockCube (0 : Vec d) (L - w)).indicator (fun _ => (1 : ℝ))) 1 hfin_meas
      zero_le_one (fun y _ => by
        by_cases hy : y ∈ clockBlockCube (0 : Vec d) (L - w) <;> simp [Set.indicator, hy])
      r hr1 hr2
    have heq : covarianceBlock d hd D s δ γ η β h Q r L L 0
        ((clockBlockCube (0 : Vec d) (L - w)).indicator (fun _ => (1 : ℝ))) =
        blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
          (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) := by
      funext ω a
      unfold blk covarianceBlock covF
      congr 1
      exact setIntegral_indicator_one_mul (measurableSet_clockBlockCube _ _)
        (clockBlockCube_mono' 0 (by linarith))
        (fun y => covarianceLocalizedField d hd D s δ γ η β h Q r y ω a)
    refine ⟨L2Vec_blk_one hlsf hT _ (volume_clockBlockCube_lt_top (0 : Vec d) _) ?_, ?_⟩
    · rw [← heq]
      exact hmem
    · rw [← heq]
      have h1 : vl2 (reducedLaw Q) (covarianceBlock d hd D s δ γ η β h Q r L L 0
          ((clockBlockCube (0 : Vec d) (L - w)).indicator (fun _ => (1 : ℝ)))) ≤ Cc * 1 := hsz
      linarith

theorem cov_strip_data (hbd : node_e_u3A_block_u2D_boundaryStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ Cb Lb : ℝ, 0 < Cb ∧ 2 ≤ Lb ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
        ∀ L : ℝ, Lb ≤ L → ∀ {V : Vec d → Set (Vec d)},
          (∀ a, LocalStationaryField (reducedLaw Q) V
            (covF d hd D s δ γ η β h Q (L ^ η) a)) → ∀ x : Vec d,
          L2Vec (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q (L ^ η))
              (clockBlockCube x L) (stripFn x L (L ^ β))) ∧
            vl2 (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q (L ^ η))
              (clockBlockCube x L) (stripFn x L (L ^ β))) ≤ Cb * L ^ (-(1 - β) / 2) := by
  obtain ⟨Cb, Lb, hCb, hLb, hbdQ⟩ := hbd d hd D s δ γ η β h
  refine ⟨Cb, Lb, hCb, hLb, ?_⟩
  intro Q hQ L hL V hlsf x
  haveI := reducedLaw_probability Q
  have hT := reducedLaw_hT Q
  have hL0 : 0 ≤ L := by linarith
  have hmeas : Measurable (stripFn x L (L ^ β)) :=
    measurable_const.indicator (measurableSet_clockBlockCube _ _).compl
  obtain ⟨hmem, hsz⟩ := hbdQ Q hQ L hL x (stripFn x L (L ^ β)) 1 hmeas zero_le_one
    (fun y _ => by
      unfold stripFn
      by_cases hy : y ∈ (clockBlockCube x (L - L ^ β))ᶜ <;> simp [Set.indicator, hy])
    (fun y hy => by
      unfold stripFn
      have hy' : y ∉ (clockBlockCube x (L - L ^ β))ᶜ := fun h' => h' hy
      exact Set.indicator_of_notMem hy' _)
  refine ⟨L2Vec_strip hlsf hT _ L (L ^ β) (Real.rpow_nonneg hL0 _) x hmem, ?_⟩
  have h1 : vl2 (reducedLaw Q) (blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q (L ^ η))
      (clockBlockCube x L) (stripFn x L (L ^ β))) ≤ Cb * L ^ (-(1 - β) / 2) * 1 := hsz
  linarith

theorem cov_change_data (hch : node_e_u3A_block_u2D_changeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (s δ γ η β : ℝ) (h : covarianceWindow d D s δ γ η β) :
    ∃ Ch Lh κ₀ : ℝ, 0 < Ch ∧ 2 ≤ Lh ∧ 0 < κ₀ ∧ κ₀ ≤ (1 - β) / 2 ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange, HasSmoothBounds D Q →
        ∀ L : ℝ, Lh ≤ L → ∀ r : ℝ, L ^ η ≤ r → r ≤ L ^ β →
        ∀ {V₁ V₂ : Vec d → Set (Vec d)},
          (∀ a, LocalStationaryField (reducedLaw Q) V₁
            (covF d hd D s δ γ η β h Q (L ^ η) a)) →
          (∀ a, LocalStationaryField (reducedLaw Q) V₂ (covF d hd D s δ γ η β h Q r a)) →
          ∀ x : Vec d,
          L2Vec (reducedLaw Q) (fun ω a =>
              blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
                (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a -
              blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q (L ^ η))
                (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a) ∧
            vl2 (reducedLaw Q) (fun ω a =>
              blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q r)
                (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a -
              blk (L ^ (-(d : ℝ) / 2)) (covF d hd D s δ γ η β h Q (L ^ η))
                (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a) ≤ Ch * L ^ (-κ₀) := by
  obtain ⟨Ch, Lh, κ₀, hCh, hLh, hκ₀, hκ₀β, hchQ⟩ := hch d hd D s δ γ η β h
  refine ⟨Ch, Lh, κ₀, hCh, hLh, hκ₀, hκ₀β, ?_⟩
  intro Q hQ L hL r hr1 hr2 V₁ V₂ h1 h2 x
  haveI := reducedLaw_probability Q
  have hT := reducedLaw_hT Q
  obtain ⟨hmem, hsz⟩ := hchQ Q hQ L hL x r hr1 hr2
  exact ⟨L2Vec_diff_blk h1 h2 hT _ (volume_clockBlockCube_lt_top x L) hmem, hsz⟩

theorem node_e_u3A_block_u2D_recursion_of_deps
    (hclt : node_e_u3A_block_u2D_cltStmt) (hbd : node_e_u3A_block_u2D_boundaryStmt)
    (hch : node_e_u3A_block_u2D_changeStmt)
    (hjl : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (_hpar : node_e_u3A_parametersStmt) : node_e_u3A_block_u2D_recursionStmt := by
  intro d hd D s δ γ η β h
  have hwin := h
  obtain ⟨_, _, _, hδ, _, _, _, hη3, hη2, hβ1, hβ2⟩ := hwin
  obtain ⟨Cc, Lc, hCc, hLc, hcltD⟩ := cov_clt_data hclt d hd D s δ γ η β h
  obtain ⟨Cb, Lb, hCb, hLb, hbdD⟩ := cov_strip_data hbd d hd D s δ γ η β h
  obtain ⟨Ch, Lh, κ₀, hCh, hLh, hκ₀, hκ₀β, hchD⟩ := cov_change_data hch d hd D s δ γ η β h
  have hlsfD := cov_lsf hjl d hd D s δ γ η β h
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hηpos : 0 < η := by linarith
  have hη1 : η < 1 := lt_trans hη3 (inv_lt_one_of_one_lt₀ (by linarith))
  have hβη : η < β := by nlinarith [mul_pos hηpos hδ]
  have hr₀ : 1 ≤ D.dependenceRange := D.one_le_dependenceRange
  obtain ⟨L₁, hL₁1, hthr⟩ := recursion_thresholds (r₀ := D.dependenceRange) hr₀ hδ hηpos hβη hβ1
  have hcard : (Fintype.card (Fin d → Fin 2) : ℝ) = (2 : ℝ) ^ d := by
    simp
  have hc : ((2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 * (Fintype.card (Fin d → Fin 2) : ℝ) = 1 := by
    rw [hcard]
    exact two_rpow_sq_mul_pow d
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = min κ₀ ((1 - β) / 2) := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκdef]; exact lt_min hκ₀ (by linarith)
  have hκ₁ : κ ≤ κ₀ := by rw [hκdef]; exact min_le_left _ _
  have hκ₂ : κ ≤ (1 - β) / 2 := by rw [hκdef]; exact min_le_right _ _
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : ℝ,
      E₀ = (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ) ^ d * (Ch + Cb) := ⟨_, rfl⟩
  have hE₀nn : 0 ≤ E₀ := by rw [hE₀]; positivity
  obtain ⟨C₉, hC₉⟩ : ∃ C₉ : ℝ, C₉ = E₀ * (2 * Cc + E₀) + Cb * (2 * Cc) := ⟨_, rfl⟩
  have hC₉nn : 0 ≤ C₉ := by rw [hC₉]; positivity
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cc + Cb + E₀ + C₉ := ⟨_, rfl⟩
  have hCpos : 0 < C := by rw [hCdef]; positivity
  refine ⟨C, max (max Lc Lb) (max Lh L₁), κ, hCpos,
    le_trans hLc (le_trans (le_max_left _ _) (le_max_left _ _)), hκpos, hκ₂, ?_⟩
  intro Q hQ L hL
  have hLc' : Lc ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hL
  have hLb' : Lb ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hL
  have hLh' : Lh ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL₁' : L₁ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hL1 : 1 ≤ L := le_trans hL₁1 hL₁'
  have hL0 : 0 < L := by linarith
  obtain ⟨h2r, hchg, hsep⟩ := hthr L hL₁'
  haveI := reducedLaw_probability Q
  have hT := reducedLaw_hT Q
  have hfr := reducedLaw_hasFiniteRange Q
  have hLη2 : L ^ η ≤ (2 * L) ^ η := Real.rpow_le_rpow hL0.le (by linarith) hηpos.le
  have h2L : 2 * D.dependenceRange ≤ (2 * L) ^ η := le_trans h2r hLη2
  have lsf1 := hlsfD Q hQ (L ^ η) h2r
  have lsf2 := hlsfD Q hQ ((2 * L) ^ η) h2L
  have hLη : L ^ η ≤ L :=
    (Real.rpow_le_rpow_of_exponent_le hL1 hη1.le).trans_eq (Real.rpow_one L)
  have h2Lη : (2 * L) ^ η ≤ 2 * L :=
    (Real.rpow_le_rpow_of_exponent_le (by linarith) hη1.le).trans_eq (Real.rpow_one _)
  have hLLc2 : Lc ≤ 2 * L := by linarith
  have hw0 : 0 ≤ L ^ β := Real.rpow_nonneg hL0.le _
  have hn₂ : (2 * L) ^ (-(d : ℝ) / 2) = (2 : ℝ) ^ (-(d : ℝ) / 2) * L ^ (-(d : ℝ) / 2) :=
    Real.mul_rpow (by norm_num) hL0.le
  obtain ⟨⟨hXL2, hXc⟩, hXm⟩ := hcltD Q hQ L hLc' (L ^ η) le_rfl hLη lsf1
  obtain ⟨hXmL2, hXmc⟩ := hXm (L ^ β) hw0
  obtain ⟨⟨hX₂L2, hX₂c⟩, -⟩ := hcltD Q hQ (2 * L) hLLc2 ((2 * L) ^ η) le_rfl h2Lη lsf2
  have hsbAll := fun x : Vec d => hbdD Q hQ L hLb' lsf1 x
  have hΔAll := fun x : Vec d => hchD Q hQ L hLh' ((2 * L) ^ η) hLη2 hchg lsf1 lsf2 x
  have core := recursion_core (μ := reducedLaw Q) (r₀ := D.dependenceRange)
    (ρ := covarianceLocalizationRadius D δ (L ^ η)) (L := L) (w := L ^ β)
    (n := L ^ (-(d : ℝ) / 2)) (n₂ := (2 * L) ^ (-(d : ℝ) / 2)) (Cc := Cc)
    (B := Cb * L ^ (-(1 - β) / 2)) (H := Ch * L ^ (-κ₀))
    hfr hT (fun y z hz => hz) hsep hw0 hn₂ hc lsf1 lsf2 hXL2 hXc hXmL2 hXmc hX₂L2 hX₂c
    (fun x => (hsbAll x).1) (fun x => (hsbAll x).2) (fun x => (hΔAll x).1)
    (fun x => (hΔAll x).2)
  obtain ⟨hdL2, hdc, hind, hid, hintm, herrL2, herrc, hcovc⟩ := core
  -- exponent bookkeeping
  have ht0 : 0 ≤ L ^ (-κ) := Real.rpow_nonneg hL0.le _
  have ht1 : L ^ (-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  have hLκ₀ : L ^ (-κ₀) ≤ L ^ (-κ) := rpow_neg_le_rpow_neg hL1 hκ₁
  have hLβ : L ^ (-(1 - β) / 2) ≤ L ^ (-κ) := by
    have e : L ^ (-(1 - β) / 2) = L ^ (-((1 - β) / 2)) := by
      congr 1
      ring
    rw [e]
    exact rpow_neg_le_rpow_neg hL1 hκ₂
  have hE : (2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) *
      (Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2))) ≤ E₀ * L ^ (-κ) := by
    rw [hcard, hE₀]
    have h1 : Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2) ≤ (Ch + Cb) * L ^ (-κ) :=
      calc Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2)
          ≤ Ch * L ^ (-κ) + Cb * L ^ (-κ) :=
            add_le_add (mul_le_mul_of_nonneg_left hLκ₀ hCh.le)
              (mul_le_mul_of_nonneg_left hLβ hCb.le)
        _ = (Ch + Cb) * L ^ (-κ) := by ring
    calc (2 : ℝ) ^ (-(d : ℝ) / 2) * ((2 : ℝ) ^ d * (Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2)))
        = ((2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ) ^ d) *
          (Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2)) := by ring
      _ ≤ ((2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ) ^ d) * ((Ch + Cb) * L ^ (-κ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (2 : ℝ) ^ (-(d : ℝ) / 2) * (2 : ℝ) ^ d * (Ch + Cb) * L ^ (-κ) := by ring
  have hEnn : 0 ≤ (2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) *
      (Ch * L ^ (-κ₀) + Cb * L ^ (-(1 - β) / 2))) := by positivity
  have hnum := cov_numeric hEnn hE ht0 ht1 hE₀nn hCc.le
    (mul_le_mul_of_nonneg_left hLβ hCb.le)
  have hC₉C : C₉ ≤ C := by rw [hCdef]; linarith
  have hE₀C : E₀ ≤ C := by rw [hCdef]; linarith
  have hCbC : Cb ≤ C := by rw [hCdef]; linarith
  have hCcC : Cc ≤ C := by rw [hCdef]; linarith
  dsimp only
  refine ⟨hXL2.size_memLp, hXmL2.size_memLp, ?_, ?_, hind, hid, hintm, herrL2.size_memLp,
    ?_, ?_⟩
  · exact hXc.trans hCcC
  · exact hdc.trans (mul_le_mul_of_nonneg_right hCbC (Real.rpow_nonneg hL0.le _))
  · exact herrc.trans (hE.trans (mul_le_mul_of_nonneg_right hE₀C ht0))
  · refine hcovc.trans (hnum.trans ?_)
    rw [← hC₉]
    exact mul_le_mul_of_nonneg_right hC₉C ht0

end EinsteinFull.Blueprint
