import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import EinsteinRelation.Calculus.OrbitWeakGradientSupport

/-! # Orbit curl identity on the closed stationary potential-gradient domain

The spatial orbit of an actual horizontal-H¹ gradient has commuting weak mixed
derivatives. The coordinate pairings are continuous in the Euclidean-valued L²
field, so the identity extends to the closed stationary potential-gradient
domain for the actual reduced environment law.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

private def euclideanCoordinateLp {d : ℕ} (Q : Measure (FieldPair d)) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →L[ℝ] Lp ℝ 2 Q :=
  (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).compLpL 2 Q

private theorem orbitSpatialPairing_integrable {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (a : Vec d → ℝ)
    (ha : Continuous a) (hac : HasCompactSupport a)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (i : Fin d) :
    Integrable (fun x : Vec d => a x • translationLp Q hQ x
      (euclideanCoordinateLp Q i G)) volume := by
  have ht : Continuous (fun x : Vec d =>
      translationLp Q hQ x (euclideanCoordinateLp Q i G)) :=
    (continuous_translationLp Q hQ).comp
      (continuous_id.prodMk continuous_const)
  exact (ha.smul ht).integrable_of_hasCompactSupport hac.smul_right

private def orbitSpatialPairingLinearMap {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (a : Vec d → ℝ)
    (ha : Continuous a) (hac : HasCompactSupport a) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →ₗ[ℝ] Lp ℝ 2 Q where
  toFun G := ∫ x : Vec d, a x • translationLp Q hQ x
    (euclideanCoordinateLp Q i G) ∂volume
  map_add' G H := by
    have hfun : (fun x : Vec d => a x • translationLp Q hQ x
        (euclideanCoordinateLp Q i (G + H))) =
        (fun x => a x • translationLp Q hQ x (euclideanCoordinateLp Q i G)) +
          fun x => a x • translationLp Q hQ x (euclideanCoordinateLp Q i H) := by
      funext x
      change a x • translationLp Q hQ x
          (euclideanCoordinateLp Q i (G + H)) =
        a x • translationLp Q hQ x (euclideanCoordinateLp Q i G) +
          a x • translationLp Q hQ x (euclideanCoordinateLp Q i H)
      simp only [map_add, smul_add]
    calc
      (∫ x : Vec d, a x • translationLp Q hQ x
          (euclideanCoordinateLp Q i (G + H)) ∂volume) =
          ∫ x, (fun x : Vec d => a x • translationLp Q hQ x
            (euclideanCoordinateLp Q i G)) x +
              (fun x => a x • translationLp Q hQ x (euclideanCoordinateLp Q i H)) x
            ∂volume := by rw [hfun]; rfl
      _ = _ := integral_add
        (orbitSpatialPairing_integrable Q hQ a ha hac G i)
        (orbitSpatialPairing_integrable Q hQ a ha hac H i)
  map_smul' c G := by
    have hfun : (fun x : Vec d => a x • translationLp Q hQ x
        (euclideanCoordinateLp Q i (c • G))) =
        fun x => c • (a x • translationLp Q hQ x (euclideanCoordinateLp Q i G)) := by
      funext x
      change a x • translationLp Q hQ x
          (euclideanCoordinateLp Q i (c • G)) = _
      rw [map_smul, map_smul]
      exact smul_comm (a x) c _
    rw [hfun, integral_smul]
    simp only [RingHom.id_apply]

private noncomputable def orbitSpatialPairing {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (a : Vec d → ℝ)
    (ha : Continuous a) (hac : HasCompactSupport a) (i : Fin d) :
    Lp (EuclideanSpace ℝ (Fin d)) 2 Q →L[ℝ] Lp ℝ 2 Q := by
  let T := orbitSpatialPairingLinearMap Q hQ a ha hac i
  have haInt : Integrable (fun x : Vec d => |a x|) volume := by
    simpa only [Real.norm_eq_abs] using ha.integrable_of_hasCompactSupport hac |>.norm
  have hC : 0 ≤ ∫ x : Vec d, |a x| ∂volume := integral_nonneg (fun x => abs_nonneg (a x))
  refine T.mkContinuous (∫ x : Vec d, |a x| ∂volume) ?_
  intro G
  have hproj : ‖PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro v
    simpa only [PiLp.proj_apply, one_mul] using (PiLp.norm_apply_le v i)
  have hcoord : ‖euclideanCoordinateLp Q i G‖ ≤ ‖G‖ := by
    calc
      ‖euclideanCoordinateLp Q i G‖ ≤
          ‖euclideanCoordinateLp Q i‖ * ‖G‖ := (euclideanCoordinateLp Q i).le_opNorm G
      _ ≤ ‖PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i‖ * ‖G‖ := by
        gcongr
        exact ContinuousLinearMap.norm_compLpL_le _
      _ ≤ 1 * ‖G‖ := mul_le_mul_of_nonneg_right hproj (norm_nonneg _)
      _ = ‖G‖ := one_mul _
  change ‖∫ x : Vec d, a x • translationLp Q hQ x
      (euclideanCoordinateLp Q i G) ∂volume‖ ≤
        (∫ x : Vec d, |a x| ∂volume) * ‖G‖
  calc
    _ ≤ ∫ x : Vec d, ‖a x • translationLp Q hQ x
        (euclideanCoordinateLp Q i G)‖ ∂volume := norm_integral_le_integral_norm _
    _ = (∫ x : Vec d, |a x| ∂volume) * ‖euclideanCoordinateLp Q i G‖ := by
      have hfun : (fun x : Vec d => ‖a x • translationLp Q hQ x
          (euclideanCoordinateLp Q i G)‖) =
          fun x => |a x| * ‖euclideanCoordinateLp Q i G‖ := by
        funext x
        rw [norm_smul, norm_translationLp, Real.norm_eq_abs]
      rw [hfun, integral_mul_const]
    _ ≤ (∫ x : Vec d, |a x| ∂volume) * ‖G‖ :=
      mul_le_mul_of_nonneg_left hcoord hC

private theorem contDiff_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i ψ) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ ψ x (unitVector i))
  exact ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

private theorem hasCompactSupport_coordinateDerivative {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (coordinateDerivative i ψ) := by
  simpa only [coordinateDerivative] using! hψ.fderiv_apply ℝ (unitVector i)

private theorem coordinateDerivative_commute {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j k : Fin d) (x : Vec d) :
    coordinateDerivative j (coordinateDerivative k ψ) x =
      coordinateDerivative k (coordinateDerivative j ψ) x := by
  have hinner : (2 : ℕ∞) ≤ (⊤ : ℕ∞) := le_top
  have hn : minSmoothness ℝ 2 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact_mod_cast hinner
  have hs := (hψ.contDiffAt (x := x)).isSymmSndFDerivAt hn
  have hd : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y) x := by
    have hbound : (1 : WithTop ℕ∞) + 1 ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact_mod_cast hinner
    exact ((hψ.contDiffAt (x := x)).fderiv_right hbound).differentiableAt (by norm_num)
  have happly (v w : Vec d) :
      fderiv ℝ (fun y => fderiv ℝ ψ y v) x w =
        (fderiv ℝ (fderiv ℝ ψ) x w) v := by
    have h := fderiv_clm_apply hd (differentiableAt_const (x := x) v)
    have h' := congrArg (fun L : Vec d →L[ℝ] ℝ => L w) h
    simpa using h'
  have hswap := hs.iteratedFDeriv_cons (v := unitVector j) (w := unitVector k)
  change fderiv ℝ (coordinateDerivative k ψ) x (unitVector j) =
    fderiv ℝ (coordinateDerivative j ψ) x (unitVector k)
  rw [show coordinateDerivative k ψ = fun y => fderiv ℝ ψ y (unitVector k) by rfl,
      show coordinateDerivative j ψ = fun y => fderiv ℝ ψ y (unitVector j) by rfl]
  rw [happly (unitVector k) (unitVector j), happly (unitVector j) (unitVector k)]
  simpa [iteratedFDeriv_two_apply] using hswap

/-- The orbit curl identity holds on the actual closed stationary potential-gradient
submodule for any stationary probability law. Both sides are Bochner integrals in the
environment L² space, and the proof establishes integrability from compact support. -/
theorem stationaryPotentialGradient_orbit_curlFree {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (j k : Fin d) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    (∫ x : Vec d, coordinateDerivative j ψ x • translationLp Q hQ x
      (euclideanCoordinateLp Q k G) ∂volume) =
    (∫ x : Vec d, coordinateDerivative k ψ x • translationLp Q hQ x
      (euclideanCoordinateLp Q j G) ∂volume) := by
  let a := coordinateDerivative j ψ
  let b := coordinateDerivative k ψ
  let Pa := orbitSpatialPairing Q hQ a
    (contDiff_coordinateDerivative hψ j).continuous
    (hasCompactSupport_coordinateDerivative hψc j) k
  let Pb := orbitSpatialPairing Q hQ b
    (contDiff_coordinateDerivative hψ k).continuous
    (hasCompactSupport_coordinateDerivative hψc k) j
  let C := Pa - Pb
  let K := LinearMap.ker C.toLinearMap
  have hclosed : IsClosed K.carrier := ContinuousLinearMap.isClosed_ker C
  have hrange : LinearMap.range (horizontalEuclideanGradientMap Q hQ) ≤ K := by
    rintro H ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    change Pa (horizontalEuclideanGradient Q hQ f) -
      Pb (horizontalEuclideanGradient Q hQ f) = 0
    have hcoord (i : Fin d) : euclideanCoordinateLp Q i
        (horizontalEuclideanGradient Q hQ f) = horizontalH1Gradient Q hQ f i := by
      apply Lp.ext
      filter_upwards [ContinuousLinearMap.coeFn_compLpL
          (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i)
          (horizontalEuclideanGradient Q hQ f) (p := 2) (μ := Q),
        horizontalEuclideanGradient_coordinates Q hQ f i] with ω hproj hcoord
      simpa only [PiLp.proj_apply] using! hproj.trans hcoord
    have hjtest : ContDiff ℝ (⊤ : ℕ∞) a := contDiff_coordinateDerivative hψ j
    have hjtestc : HasCompactSupport a := hasCompactSupport_coordinateDerivative hψc j
    have hktest : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_coordinateDerivative hψ k
    have hktestc : HasCompactSupport b := hasCompactSupport_coordinateDerivative hψc k
    have hweak₁ := horizontalH1_orbit_hasLpWeakPartialDerivative hQ f k hjtest hjtestc
    have hweak₂ := horizontalH1_orbit_hasLpWeakPartialDerivative hQ f j hktest hktestc
    have hp₁ : Pa (horizontalEuclideanGradient Q hQ f) =
        -(∫ x : Vec d, coordinateDerivative k a x •
          translationLp Q hQ x (f : Lp ℝ 2 Q) ∂volume) := by
      change (∫ x : Vec d, a x • translationLp Q hQ x
        (euclideanCoordinateLp Q k (horizontalEuclideanGradient Q hQ f)) ∂volume) = _
      rw [hcoord k]
      have hneg := congrArg Neg.neg hweak₁
      simpa only [neg_neg] using hneg.symm
    have hp₂ : Pb (horizontalEuclideanGradient Q hQ f) =
        -(∫ x : Vec d, coordinateDerivative j b x •
          translationLp Q hQ x (f : Lp ℝ 2 Q) ∂volume) := by
      change (∫ x : Vec d, b x • translationLp Q hQ x
        (euclideanCoordinateLp Q j (horizontalEuclideanGradient Q hQ f)) ∂volume) = _
      rw [hcoord j]
      have hneg := congrArg Neg.neg hweak₂
      simpa only [neg_neg] using hneg.symm
    have hmixed : (∫ x : Vec d, coordinateDerivative k a x •
        translationLp Q hQ x (f : Lp ℝ 2 Q) ∂volume) =
        (∫ x : Vec d, coordinateDerivative j b x •
        translationLp Q hQ x (f : Lp ℝ 2 Q) ∂volume) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact congrArg (fun c : ℝ => c • translationLp Q hQ x (f : Lp ℝ 2 Q))
        (coordinateDerivative_commute hψ j k x).symm
    rw [hp₁, hp₂, hmixed]
    simp
  have hclose := (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure_minimal
    hrange hclosed hG
  have hzero : C G = 0 := LinearMap.mem_ker.mp hclose
  have hcloseEq : Pa G = Pb G := sub_eq_zero.mp hzero
  change (∫ x : Vec d, a x • translationLp Q hQ x (euclideanCoordinateLp Q k G) ∂volume) =
    (∫ x : Vec d, b x • translationLp Q hQ x (euclideanCoordinateLp Q j G) ∂volume)
  exact hcloseEq

end EinsteinRelation.Correctors

namespace EinsteinRelation.Correctors

/-- Consumer for the source actual reduced environment law and its closed corrector
potential-gradient domain. No extra regularity premise on `G` is required. -/
theorem closedPotentialGradient_orbit_curlFree {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j k : Fin d)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hG : G ∈ correctorPotentialDomain Q) :
    (∫ x : Vec d, coordinateDerivative j ψ x •
      translationLp (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) x
        ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) k).compLpL 2
          (reducedEnvironmentLaw Q) G) ∂volume) =
    (∫ x : Vec d, coordinateDerivative k ψ x •
      translationLp (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) x
        ((PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).compLpL 2
          (reducedEnvironmentLaw Q) G) ∂volume) := by
  exact stationaryPotentialGradient_orbit_curlFree (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q) hψ hψc j k G hG

end EinsteinRelation.Correctors
