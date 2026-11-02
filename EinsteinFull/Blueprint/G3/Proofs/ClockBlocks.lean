import EinsteinFull.Blueprint.G3.ClockBlockEstimates
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_clock_u2D_blocks
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_l2
import EinsteinFull.Blueprint.G3.node_p_u3A_covariance_u23_joint_u2D_localization
import EinsteinFull.Blueprint.G3.node_e_u3A_parameters

/-! The complete clock-block contract at paper/main.tex:927–932.
The target follows directly from the adopted finite-range clock APIs. They apply
to every environment law, so the proof retains the prescribed three graph
premises without using the stronger joint localization assertion. -/

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation MeasureTheory ClockBlocks
open scoped ENNReal

/-- The actual clock-block estimates, with constants fixed before the law. -/
@[nolint unusedArguments] -- Preserve the exact reviewed dependency interface; direct clock APIs suffice.
theorem node_p_u3A_covariance_u23_clock_u2D_blocks_of_deps
    (_hclock : node_e_u3A_clock_u2D_l2Stmt)
    (_hlocal : node_p_u3A_covariance_u23_joint_u2D_localizationStmt)
    (_hparameters : node_e_u3A_parametersStmt) :
    node_p_u3A_covariance_u23_clock_u2D_blocksStmt := by
  intro d hd D δ η β hδ hη hηβ hβ
  have hηp : 0 < η := by linarith
  have hηβ' : η < β := by nlinarith [mul_pos hηp hδ]
  have hβp : 0 < β := hηp.trans hηβ'
  let V := clockVarianceConstant d D.ellipticity D.dependenceRange
  let F := 4 * (d : ℝ) ^ 2 * Real.sqrt (sourceReducedBound D.ellipticity)
  have hV : 0 ≤ V := by
    dsimp [V, clockVarianceConstant]
    exact mul_nonneg (sq_nonneg _) (pow_nonneg
      (mul_nonneg (by norm_num) (zero_le_one.trans D.one_le_dependenceRange)) _)
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let p := ((d : ℝ) + 1) / η
  obtain ⟨E, _hE, herror⟩ := clockCube_homogenizedGaussian_truncation_variance_inversePower_le
    d D.one_le_ellipticity hδ p
  let H := 1 + V + (d : ℝ) * V + F + 6 * E ^ 2 + 12 * V * F
  let C := Real.sqrt H + 1
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hHC : H ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt hH, Real.sqrt_nonneg H]
  have hCV : V ≤ C ^ 2 := by
    apply le_trans _ hHC
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hV,
      mul_nonneg hV hF, sq_nonneg E]
  have hCdV : (d : ℝ) * V ≤ C ^ 2 := by
    apply le_trans _ hHC
    dsimp [H]
    nlinarith [mul_nonneg hV hF, sq_nonneg E]
  have hCF : F ≤ C ^ 2 := by
    apply le_trans _ hHC
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hV,
      mul_nonneg hV hF, sq_nonneg E]
  have hCE : 6 * E ^ 2 + 12 * V * F ≤ C ^ 2 := by
    apply le_trans _ hHC
    dsimp [H]
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hV]
  refine ⟨C, (1 - β) / 2, hC, by linarith, le_rfl, ?_, ?_⟩
  · intro q
    obtain ⟨Cq, hCq, hq⟩ := clockHomogenizedGaussian_truncation_inversePower_le
      d D.one_le_ellipticity hδ q
    exact ⟨Cq, hCq, fun Q' _hsmooth r hr => hq Q' r hr⟩
  intro Q _hsmooth
  letI := reducedLaw_probability Q
  change
    (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (f : Vec d → ℝ) (b : ℝ),
      Measurable f → 0 ≤ b → (∀ y ∈ clockBlockCube x L, |f y| ≤ b) →
      (∀ (r : ℝ), L ^ η ≤ r → r ≤ L →
        MemLp (block Q r L {z | euclideanNorm z < r ^ (1 + δ)} x f) 2 (reducedLaw Q) ∧
        (∫ ω, (block Q r L {z | euclideanNorm z < r ^ (1 + δ)} x f ω) ^ 2 ∂reducedLaw Q) ≤ (C * b) ^ 2) ∧
      ((∀ y ∈ clockBlockCube x (L - L ^ β), f y = 0) →
        MemLp (block Q (L ^ η) L {z | euclideanNorm z < (L ^ η) ^ (1 + δ)} x f) 2 (reducedLaw Q) ∧
        (∫ ω, (block Q (L ^ η) L {z | euclideanNorm z < (L ^ η) ^ (1 + δ)} x f ω) ^ 2 ∂reducedLaw Q) ≤
          (C * L ^ (-(1 - β) / 2) * b) ^ 2)) ∧
    (∀ (L : ℝ), 1 ≤ L → ∀ (x : Vec d) (r : ℝ), L ^ η ≤ r → r ≤ L ^ β →
      MemLp (fun ω => block Q r L {z | euclideanNorm z < r ^ (1 + δ)} x (fun _ => 1) ω -
        block Q (L ^ η) L {z | euclideanNorm z < (L ^ η) ^ (1 + δ)} x (fun _ => 1) ω) 2 (reducedLaw Q) ∧
      (∫ ω, (block Q r L {z | euclideanNorm z < r ^ (1 + δ)} x (fun _ => 1) ω -
        block Q (L ^ η) L {z | euclideanNorm z < (L ^ η) ^ (1 + δ)} x (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
          (C * L ^ (-((1 - β) / 2))) ^ 2) ∧ _
  have hT (r : ℝ) : MeasurableSet {z : Vec d | euclideanNorm z < r ^ (1 + δ)} := by
    apply measurableSet_lt _ measurable_const
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hscale {L : ℝ} (hL : 1 ≤ L) : 1 ≤ L ^ η := Real.one_le_rpow hL hηp.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro L hL x f b hfm hb hf
    have hLp := zero_lt_one.trans_le hL
    refine ⟨?_, ?_⟩
    · intro r hr _hrL
      have hrp := zero_lt_one.trans_le ((hscale hL).trans hr)
      refine ⟨memLp_block Q hrp (hT r) x hLp.le hfm hb hf, ?_⟩
      apply (variance_block_le Q hrp (hT r) x hLp hfm hb hf).trans
      calc
        _ ≤ C ^ 2 * b ^ 2 := mul_le_mul_of_nonneg_right hCV (sq_nonneg _)
        _ = _ := by ring
    · intro hf0
      have hrp := Real.rpow_pos_of_pos hLp η
      refine ⟨memLp_block Q hrp (hT (L ^ η)) x hLp.le hfm hb hf, ?_⟩
      have hwL : L ^ β ≤ L := by
        simpa using Real.rpow_le_rpow_of_exponent_le hL hβ.le
      have hh := variance_boundary_le Q hrp (hT (L ^ η)) x
        (Real.rpow_nonneg hLp.le β) hwL hLp (by omega) hfm hb hf hf0
      apply hh.trans
      calc
        _ = ((d : ℝ) * V) * b ^ 2 * (L ^ (-1 : ℝ) * L ^ β) := by dsimp [V]; ring
        _ ≤ C ^ 2 * b ^ 2 * (L ^ (-1 : ℝ) * L ^ β) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCdV (sq_nonneg _)) (by positivity)
        _ = _ := by rw [surface_power hLp]; ring
  · intro L hL x r hr hrβ
    have hLp := zero_lt_one.trans_le hL
    have hr1 := (hscale hL).trans hr
    have hrp := zero_lt_one.trans_le hr1
    have htp := Real.rpow_pos_of_pos hLp η
    let T := fun a : ℝ => {z : Vec d | euclideanNorm z < a ^ (1 + δ)}
    have hm (a : ℝ) (ha : 0 < a) (S : Set (Vec d)) (hS : MeasurableSet S) :=
      memLp_block Q ha hS x hLp.le (f := fun _ => (1 : ℝ)) measurable_const
        (b := 1) (by norm_num) (fun _ _ => by norm_num)
    have hmr := hm r hrp (T r) (hT r)
    have hmt := hm (L ^ η) htp (T (L ^ η)) (hT (L ^ η))
    refine ⟨hmr.sub hmt, ?_⟩
    have htβ : L ^ η ≤ L ^ β := Real.rpow_le_rpow_of_exponent_le hL hηβ'.le
    have he (a : ℝ) (ha : L ^ η ≤ a) :
        (∫ ω, (block Q a L Set.univ x (fun _ => 1) ω -
          block Q a L (T a) x (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
            E ^ 2 * L ^ (β - 1) := by
      have ha1 := (hscale hL).trans ha
      have ha0 := zero_lt_one.trans_le ha1
      have hh := normalized_truncation_variance Q ha0 x hLp (herror Q a ha1 x L hLp.le)
      apply hh.trans
      have hp := truncation_power_le (d := d) hL hηp hβp.le ha
      have hp' : L ^ d * (a ^ (-p)) ^ 2 ≤ L ^ (β - 1) := by
        simpa only [p, neg_div] using hp
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp' (sq_nonneg E)
    have hs := normalized_difference_variance Q hrp htp x hLp (by omega)
    have hs' : (∫ ω, (block Q r L Set.univ x (fun _ => 1) ω -
        block Q (L ^ η) L Set.univ x (fun _ => 1) ω) ^ 2 ∂reducedLaw Q) ≤
          (4 * V * F) * L ^ (β - 1) := by
      apply hs.trans
      calc
        _ ≤ 8 * V * (d : ℝ) ^ 2 * Real.sqrt (sourceReducedBound D.ellipticity) *
            L ^ (-1 : ℝ) * (2 * L ^ β) := by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = _ := by
          rw [show β - 1 = -1 + β by ring, Real.rpow_add hLp]
          dsimp [F]
          ring
    have hh := variance_three_le (reducedLaw Q) hmr hmt
      (hm r hrp Set.univ MeasurableSet.univ)
      (hm (L ^ η) htp Set.univ MeasurableSet.univ)
    apply hh.trans
    calc
      _ ≤ 3 * (E ^ 2 * L ^ (β - 1)) + 3 * ((4 * V * F) * L ^ (β - 1)) +
          3 * (E ^ 2 * L ^ (β - 1)) := by
        linarith [he r hr, he (L ^ η) le_rfl]
      _ = (6 * E ^ 2 + 12 * V * F) * L ^ (β - 1) := by ring
      _ ≤ C ^ 2 * L ^ (β - 1) := mul_le_mul_of_nonneg_right hCE (by positivity)
      _ = _ := by
        rw [show β - 1 = -1 + β by ring, Real.rpow_add hLp, surface_power hLp]
        simp only [neg_div, mul_pow]
  · intro L hL x r hr _hrL
    have hrp := zero_lt_one.trans_le hr
    refine ⟨smoothing_error_memLp Q hrp x (zero_le_one.trans hL), ?_⟩
    exact (clockCube_homogenizedGaussian_smoothing_energy_le Q hrp x
      (zero_le_one.trans hL)).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCF (by positivity)) hrp.le)
  · intro L hL x f b hfm hb hf r hr
    exact smoothing_L2 Q (zero_lt_one.trans_le hr) x (zero_le_one.trans hL) hfm hb hf

end EinsteinFull.Blueprint
