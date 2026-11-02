import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_tube_u2D_geometry
import EinsteinRelation.Regeneration.Geometry

open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

private lemma tube_coord_le {d : ℕ} (v : Vec d) (i : Fin d) :
    |v i| ≤ euclideanNorm v := by
  have hsq : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i)
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  simpa only [sq] using hsq

private lemma tube_round_mono (Δ : ℝ≥0) (hΔ : 0 < Δ) : Monotone (roundUp Δ) := by
  intro s t hst
  by_cases ht : t = ⊤
  · simp only [roundUp, if_pos ht, le_top]
  · have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht hst
    simp only [roundUp, if_neg hs, if_neg ht]
    apply ENNReal.coe_le_coe.mpr
    apply mul_le_mul_of_nonneg_right _ zero_le
    exact_mod_cast Nat.ceil_mono (div_le_div_of_nonneg_right
      (ENNReal.toReal_mono ht hst) (show (0 : ℝ) ≤ Δ from hΔ.le))

/-- Deterministic geometry of the two literal polygonal tubes (paper lines 356–368). -/
theorem node_rt_u3A_renewal_u23_tube_u2D_geometry_of_deps :
    node_rt_u3A_renewal_u23_tube_u2D_geometryStmt := by
  unfold node_rt_u3A_renewal_u23_tube_u2D_geometryStmt
  dsimp only
  intro d hd l hl lam hlam _hlam1 j hj Y hY htube
  let k : ℝ := (j : ℝ) - 2
  let f : ℝ → ℝ := fun u => min ((25 * l / 4) * max (u - k) 0) (25 * l / 8)
  have hk : 0 ≤ k := by rcases hj with rfl | rfl <;> norm_num [k]
  have hkN : ((j - 1 : ℕ) : ℝ) = k + 1 := by
    rcases hj with rfl | rfl <;> norm_num [k]
  have hmono : Monotone f := by
    intro u v huv
    apply min_le_min _ le_rfl
    exact mul_le_mul_of_nonneg_left (max_le_max (sub_le_sub_right huv k) le_rfl)
      (by positivity)
  have hf0 (u : ℝ) : 0 ≤ f u := le_min (by positivity) (by positivity)
  have hfmax (u : ℝ) : f u ≤ 25 * l / 8 := min_le_right _ _
  have hfbefore (u : ℝ) (hu : u ≤ k + 1 / 3) : f u ≤ 25 * l / 12 := by
    have hm : max (u - k) 0 ≤ (1 / 3 : ℝ) := max_le (by linarith) (by norm_num)
    have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ 25 * l / 4 by positivity)
    exact (min_le_left _ _).trans (by nlinarith only [hp])
  have hfhalf : f (k + 1 / 2) = 25 * l / 8 := by
    dsimp only [f]
    have he : k + 1 / 2 - k = (1 / 2 : ℝ) := by ring
    rw [he, max_eq_left (by norm_num)]
    have heq : 25 * l / 4 * (1 / 2) = 25 * l / 8 := by ring
    rw [heq, min_self]
  have hfcoord (u : ℝ≥0) (hu : (u : ℝ) ≤ (j : ℝ) - 1) :
      |lam * Y ((u : ℝ) / lam ^ 2).toNNReal (Renewal.forceCoord hd) - f u| < l / 32 := by
    have hb := (tube_coord_le _ (Renewal.forceCoord hd)).trans_lt (htube u hu)
    have he : (if j = 2 then
        min ((25 * l / 4) * (u : ℝ)) (25 * l / 8) • unitVector (Renewal.forceCoord hd)
        else if (u : ℝ) ≤ 1 then 0 else
          min ((25 * l / 4) * ((u : ℝ) - 1)) (25 * l / 8) •
            unitVector (Renewal.forceCoord hd)) (Renewal.forceCoord hd) = f u := by
      rcases hj with rfl | rfl
      · simp [f, k, unitVector]
      · by_cases hu1 : (u : ℝ) ≤ 1
        · have hm : max ((u : ℝ) - 1) 0 = 0 := max_eq_right (by linarith)
          norm_num [f, k, hu1, hm, min_eq_left (show 0 ≤ 25 * l / 8 by positivity)]
        · have hm : max ((u : ℝ) - 1) 0 = (u : ℝ) - 1 := max_eq_left (by linarith)
          norm_num [f, k, hu1, hm, unitVector]
    simpa only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, he] using hb
  have hq : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have hΔ : 0 < Renewal.regenDelta lam := by
    exact Real.toNNReal_pos.mpr (inv_pos.mpr hq)
  have hΔcoe : (Renewal.regenDelta lam : ℝ) = (lam ^ 2)⁻¹ :=
    Real.coe_toNNReal _ (inv_nonneg.mpr hq.le)
  have hcoord (t : ℝ≥0) (ht : (t : ℝ) * lam ^ 2 ≤ k + 1) :
      |lam * Y t (Renewal.forceCoord hd) - f ((t : ℝ) * lam ^ 2)| < l / 32 := by
    let u : ℝ≥0 := ⟨(t : ℝ) * lam ^ 2, mul_nonneg t.coe_nonneg hq.le⟩
    have hu_coe : (u : ℝ) = (t : ℝ) * lam ^ 2 := rfl
    have hu : (u : ℝ) ≤ (j : ℝ) - 1 := by
      rw [hu_coe]
      simp only [k] at ht
      linarith
    have he : ((u : ℝ) / lam ^ 2).toNNReal = t := by
      apply NNReal.coe_injective
      rw [Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hq.le), hu_coe]
      field_simp
    have h := hfcoord u hu
    rw [he, hu_coe] at h
    exact h
  let A : ℝ≥0 := ⟨(k + 1 / 3) / lam ^ 2, by positivity⟩
  let B : ℝ≥0 := ⟨(k + 1 / 2) / lam ^ 2, by positivity⟩
  let C : ℝ≥0 := ⟨(k + 2 / 3) / lam ^ 2, by positivity⟩
  let T : ℝ≥0 := (j - 1 : ℕ) * Renewal.regenDelta lam
  have hT : (T : ℝ) = (k + 1) / lam ^ 2 := by
    simp only [T, NNReal.coe_mul, NNReal.coe_natCast, hΔcoe, hkN, div_eq_mul_inv]
  have hB_coe : (B : ℝ) = (k + 1 / 2) / lam ^ 2 := rfl
  have hA_coe : (A : ℝ) = (k + 1 / 3) / lam ^ 2 := rfl
  have hB : (B : ℝ) * lam ^ 2 = k + 1 / 2 := by rw [hB_coe]; field_simp
  have hA : (A : ℝ) * lam ^ 2 = k + 1 / 3 := by rw [hA_coe]; field_simp
  have hAT : A ≤ T := by
    change (A : ℝ) ≤ (T : ℝ)
    rw [hT]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hBT : B ≤ T := by
    change (B : ℝ) ≤ (T : ℝ)
    rw [hT]
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have hBC : B < C := (div_lt_div_iff_of_pos_right hq).mpr (by linarith)
  have hwindow (t : ℝ≥0) (ht : t ≤ T) : (t : ℝ) * lam ^ 2 ≤ k + 1 := by
    have htt : (t : ℝ) ≤ (T : ℝ) := ht
    rw [hT] at htt
    exact (le_div_iff₀ hq).mp htt
  let H := firstHittingAbove Y (Renewal.forceCoord hd) (3 * (l / lam))
  have hlow : (A : ℝ≥0∞) < H := by
    apply lt_of_not_ge
    intro hbad
    obtain ⟨t, ht, hc⟩ := (firstHittingAbove_le_iff Y (Renewal.forceCoord hd)
      (3 * (l / lam)) A).mp hbad
    have he := (abs_lt.mp (hcoord t (hwindow t (ht.2.trans hAT)))).2
    have htime : (t : ℝ) * lam ^ 2 ≤ k + 1 / 3 := by
      rw [← hA]
      exact mul_le_mul_of_nonneg_right ht.2 hq.le
    have hf := hfbefore _ htime
    rw [hY, Pi.zero_apply, sub_zero] at hc
    have hp := mul_le_mul_of_nonneg_left hc hlam.le
    have hcancel : lam * (3 * (l / lam)) = 3 * l := by field_simp
    rw [hcancel] at hp
    linarith
  have hupper : H ≤ (B : ℝ≥0∞) := by
    apply firstHittingAbove_le_of_crossing
    have he := (abs_lt.mp (hcoord B (hwindow B hBT))).1
    rw [hB, hfhalf] at he
    rw [hY, Pi.zero_apply, sub_zero]
    apply (mul_le_mul_iff_right₀ hlam).mp
    have heq : lam * (3 * (l / lam)) = 3 * l := by field_simp
    -- Compare in the physical coordinate, retaining the literal radius l/lam.
    have hc : 3 * l ≤ lam * Y B (Renewal.forceCoord hd) := by linarith
    rw [heq]
    simpa only [mul_comm] using hc
  have hfin : H ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hupper
  let V := H.toNNReal
  have hHV : H = (V : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
  have hAV : A < V := ENNReal.coe_lt_coe.mp (by rwa [← hHV])
  have hVB : V ≤ B := ENNReal.coe_le_coe.mp (by rwa [← hHV])
  have hVT : V ≤ T := hVB.trans hBT
  have hcross : 3 * (l / lam) ≤ Y V (Renewal.forceCoord hd) := by
    obtain ⟨t, ht, hc⟩ := (firstHittingAbove_le_iff Y (Renewal.forceCoord hd)
      (3 * (l / lam)) V).mp hHV.le
    have hbefore := coordinate_le_at_firstHittingAbove Y (Renewal.forceCoord hd)
      (3 * (l / lam)) V hHV t ht.2
    simpa only [hY, Pi.zero_apply, sub_zero] using hc.trans
      (sub_le_sub_right hbefore _)
  have hcrossScaled : 3 * l ≤ lam * Y V (Renewal.forceCoord hd) := by
    have hc := mul_le_mul_of_nonneg_left hcross hlam.le
    have he : lam * (3 * (l / lam)) = 3 * l := by field_simp
    rwa [he] at hc
  have hscaledV : k < (V : ℝ) / (Renewal.regenDelta lam : ℝ) ∧
      (V : ℝ) / (Renewal.regenDelta lam : ℝ) ≤ k + 1 := by
    have hve : (V : ℝ) / (Renewal.regenDelta lam : ℝ) = (V : ℝ) * lam ^ 2 := by
      rw [hΔcoe, div_inv_eq_mul]
    rw [hve]
    constructor
    · have hav : (A : ℝ) < (V : ℝ) := hAV
      have hp := (mul_lt_mul_iff_left₀ hq).mpr hav
      rw [hA] at hp
      linarith
    · exact hwindow V hVT
  have hceil : Nat.ceil (H.toReal / (Renewal.regenDelta lam : ℝ)) = j - 1 := by
    have hreal : H.toReal = (V : ℝ) := by simp only [hHV, ENNReal.coe_toReal]
    rw [hreal]
    apply le_antisymm
    · exact Nat.ceil_le.mpr (by rw [hkN]; exact hscaledV.2)
    · rcases hj with rfl | rfl
      · apply Nat.succ_le_iff.mpr
        apply Nat.lt_ceil.mpr
        dsimp [k] at hscaledV
        norm_num at hscaledV ⊢
        exact hscaledV.1
      · apply Nat.succ_le_iff.mpr
        apply Nat.lt_ceil.mpr
        dsimp [k] at hscaledV
        norm_num at hscaledV ⊢
        exact hscaledV.1
  have hround : roundUp (Renewal.regenDelta lam) H = (T : ℝ≥0∞) := by
    simp only [roundUp, if_neg hfin, hceil, T]
  have hpass : passageSequence (Renewal.regenDelta lam) lam (l / lam)
      (3 * lam * (l / lam)) Y (Renewal.forceCoord hd) 0 = H := by
    dsimp only [passageSequence, H]
    congr 1
    field_simp
  have hosc : ∀ s ∈ Set.Icc V T,
      |Y s (Renewal.forceCoord hd) - Y V (Renewal.forceCoord hd)| ≤ (l / lam) / 2 := by
    intro s hs
    have heV := abs_lt.mp (hcoord V (hwindow V hVT))
    have heS := abs_lt.mp (hcoord s (hwindow s hs.2))
    have hm : f ((V : ℝ) * lam ^ 2) ≤ f ((s : ℝ) * lam ^ 2) :=
      hmono (mul_le_mul_of_nonneg_right hs.1 hq.le)
    have hmaxV := hfmax ((V : ℝ) * lam ^ 2)
    have hmaxS := hfmax ((s : ℝ) * lam ^ 2)
    have hbound : |lam * (Y s (Renewal.forceCoord hd) - Y V (Renewal.forceCoord hd))| ≤ l / 2 := by
      apply abs_le.mpr
      constructor <;> nlinarith only [heV.1, heV.2, heS.1, heS.2, hm,
        hmaxV, hmaxS, hcrossScaled, hl]
    rw [abs_mul, abs_of_pos hlam] at hbound
    apply (mul_le_mul_iff_right₀ hlam).mp
    have heq : lam * ((l / lam) / 2) = l / 2 := by field_simp
    rwa [heq]
  have hgood : IsGoodPassage (Renewal.regenDelta lam) lam (l / lam)
      (3 * lam * (l / lam)) Y (Renewal.forceCoord hd) 0 := by
    simp only [IsGoodPassage, hpass, hround, ENNReal.toNNReal_coe]
    exact ⟨hfin, ENNReal.coe_ne_top, hosc⟩
  have hcand : firstRoundedCandidate (Renewal.regenDelta lam) lam (l / lam)
      (3 * lam * (l / lam)) Y (Renewal.forceCoord hd) = (T : ℝ≥0∞) := by
    apply le_antisymm
    · rw [firstRoundedCandidate]
      exact iInf_le_of_le 0 (iInf_le_of_le hgood (by rw [hpass, hround]))
    · apply (le_firstRoundedCandidate_iff _ _ _ _ _ _ _).mpr
      intro n _hn
      rw [← hround, ← hpass]
      apply tube_round_mono _ hΔ
      exact monotone_passageSequence _ hΔ _ _ _ (div_pos hl hlam) Y _ (Nat.zero_le n)
  have hsurv : ∀ t : ℝ≥0, t ≤ T → -(l / lam) < Y t (Renewal.forceCoord hd) := by
    intro t ht
    have he := (abs_lt.mp (hcoord t (hwindow t ht))).1
    have hf := hf0 ((t : ℝ) * lam ^ 2)
    apply (mul_lt_mul_iff_right₀ hlam).mp
    have heq : lam * -(l / lam) = -l := by field_simp
    rw [heq]
    linarith
  have hAe : ENNReal.ofReal (((j : ℝ) - 2 + 1 / 3) / lam ^ 2) = (A : ℝ≥0∞) := by
    exact ENNReal.ofReal_coe_nnreal (p := A)
  have hCe : ENNReal.ofReal (((j : ℝ) - 2 + 2 / 3) / lam ^ 2) = (C : ℝ≥0∞) := by
    exact ENNReal.ofReal_coe_nnreal (p := C)
  have hTe : (T : ℝ≥0∞) = ((j - 1 : ℕ) : ℝ≥0∞) * (Renewal.regenDelta lam : ℝ≥0∞) := by
    simp only [T, ENNReal.coe_mul, ENNReal.coe_natCast]
  exact ⟨hAe ▸ hlow, hCe ▸ hupper.trans_lt (ENNReal.coe_lt_coe.mpr hBC), hgood,
    hcand.trans hTe, hsurv⟩

end EinsteinFull.Blueprint
