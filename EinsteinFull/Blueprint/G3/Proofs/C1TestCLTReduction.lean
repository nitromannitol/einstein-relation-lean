import EinsteinFull.Calculus.C5CanonicalTestCLT
import EinsteinFull.Blueprint.G3.node_e_u3A_test_u2D_clt

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.External.AKM
open EinsteinFull.Calculus.C5TestCLT
open EinsteinRelation.Environment.AKMTestIntegralSupport

noncomputable section

/-- The literal joint Schwartz pairing follows from the matrix bound and the
clock L² estimate, with the same derivative order and structural constants. -/
theorem node_e_u3A_test_u2D_clt_of_deps
    (hclock : node_e_u3A_clock_u2D_l2Stmt) : node_e_u3A_test_u2D_cltStmt := by
  classical
  intro d hd D N hN
  have hmask (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
      ∃ G : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d)),
        (∀ x, G x (.inr ()) = 0) ∧
        (∀ x p, G x (.inl p) = F x (.inl p)) ∧
        schwartzTestNorm N G ≤ 2 * schwartzTestNorm N F ∧
        ∀ (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀) (R : ℝ) (hR : 0 < R)
          (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
          scaledJointPairing Q R hR Z F = scaledJointPairing Q R hR Z G +
            scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ())) := by
    classical
    let E := EuclideanSpace ℂ (JointObservationIndex d)
    let e : E := EuclideanSpace.single (.inr ()) 1
    let L : E →L[ℂ] E := ContinuousLinearMap.id ℂ E -
      (EuclideanSpace.proj (.inr ())).smulRight e
    have hL (v : E) : ‖L v‖ ≤ 2 * ‖v‖ := by
      change ‖v - v (.inr ()) • e‖ ≤ _
      have he : ‖e‖ = 1 := by simp [e, E]
      calc
        _ ≤ ‖v‖ + ‖v (.inr ()) • e‖ := norm_sub_le _ _
        _ = ‖v‖ + ‖v (.inr ())‖ := by rw [norm_smul, he, mul_one]
        _ ≤ 2 * ‖v‖ := by linarith [PiLp.norm_apply_le v (.inr ())]
    let G := F.postcompCLM L
    have hzero (x : Vec d) : G x (.inr ()) = 0 := by
      change (F x - F x (.inr ()) • e) (.inr ()) = 0
      simp [e, E, PiLp.sub_apply, PiLp.smul_apply]
    have hmatrix (x : Vec d) (p : Fin d × Fin d) : G x (.inl p) = F x (.inl p) := by
      change (F x - F x (.inr ()) • e) (.inl p) = F x (.inl p)
      simp [e, E, PiLp.sub_apply, PiLp.smul_apply]
    refine ⟨G, hzero, hmatrix, ?_, ?_⟩
    · apply csSup_le (schwartzTestNorm_set_nonempty N G)
      rintro q ⟨k, dirs, x, rfl⟩
      have hder : iteratedFDeriv ℝ k.val (fun y => G y) x =
          (L.restrictScalars ℝ).compContinuousMultilinearMap
            (iteratedFDeriv ℝ k.val (fun y => F y) x) := by
        exact (L.restrictScalars ℝ).iteratedFDeriv_comp_left
          F.smooth'.contDiffAt (mod_cast le_top)
      rw [hder]
      have hw : 0 ≤ (1 + euclideanNorm x) ^ N :=
        by unfold euclideanNorm; positivity
      calc
        _ ≤ (1 + euclideanNorm x) ^ N *
            (2 * ‖iteratedFDeriv ℝ k.val (fun y => F y) x
              (fun j => unitVector (dirs j))‖) :=
          mul_le_mul_of_nonneg_left (hL _) hw
        _ ≤ 2 * schwartzTestNorm N F := by
          nlinarith [schwartz_weighted_iterated_basis_le (by omega : k.val ≤ N) F dirs x]

    · intro L₀ r₀ Q R hR Z
      rw [scaledJointPairing_eq_sum_coordinates Q hR Z F,
        scaledJointPairing_eq_sum_coordinates Q hR Z G]
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, hmatrix, hzero,
        scaledComplexClockPairing, complexClockSpatialPairing,
        zero_smul, integral_zero, smul_zero, add_zero]
  obtain ⟨Cm, hCm, hm⟩ := matrix_test_clt d hd D N hN
  obtain ⟨Cc, hCc, hc⟩ := complex_clock_l2_schwartz_dominated_le hclock d hd
    D.ellipticity D.dependenceRange D.one_le_ellipticity D.one_le_dependenceRange
    N (by omega)
  refine ⟨2 * Cm + Cc, by positivity, ?_⟩
  intro Q hQ Z hZ R hR F
  obtain ⟨G, hzero, _hmatrix, hnorm, hsplit⟩ := hmask F
  have hpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hmat := hm Q hQ Z hZ R hR G hzero
  have hclk := hc Q (Z (.inr ())) hZ.2 F (fun x => F x (.inr ()))
    ((EuclideanSpace.proj (.inr () : JointObservationIndex d)).continuous.comp F.continuous)
    (fun x => PiLp.norm_apply_le (F x) (.inr ())) R hpos
  calc
    ‖scaledJointPairing Q R hpos Z F‖ ≤
        ‖scaledJointPairing Q R hpos Z G‖ +
          ‖scaledComplexClockPairing Q R (Z (.inr ())) (fun x => F x (.inr ()))‖ := by
      rw [hsplit _ _ Q R hpos Z]
      exact norm_add_le _ _
    _ ≤ Cm * schwartzTestNorm N G + Cc * schwartzTestNorm N F :=
      add_le_add hmat hclk
    _ ≤ (2 * Cm + Cc) * schwartzTestNorm N F := by
      nlinarith only [mul_le_mul_of_nonneg_left hnorm hCm.le]

end

end EinsteinFull.Blueprint
