import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_centered_u2D_source
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interior
import EinsteinFull.Blueprint.G2.Proofs.C1HolderAverage
import EinsteinFull.Calculus.C1HolderComparisonSupport
import EinsteinFull.Calculus.C3HolderAverageSupport
import EinsteinFull.Blueprint.G2.Proofs.C3HolderAverage
import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Calculus.CommonTemporalTestsSupport
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.ParabolicBridgeCoeff
import EinsteinFull.Calculus.C6EndpointCylinderApproximation
import EinsteinFull.Calculus.C6HolderLocalGaussianIncrement
import EinsteinRelation.Correctors.ScalarSetAverageMoments
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
open PDE.Parabolic PDE.Parabolic.Lions
/- SUPERVISOR EXACT TARGET (not a declaration or proof); replace with proved command.
theorem holder_average_transpose_of_deps
  (h0 : EinsteinFull.Blueprint.node_e_u3A_local_u2D_timeStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt)
  (h2 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h3 : EinsteinFull.Blueprint.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α : ℝ, 0 < α ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → let ν : EndpointIndex d := .inr true

    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
-/
/-- Uniform large-scale control for the actual transpose Gaussian remainder.
The constant is chosen before the environment and force. This supplies the
nonlocal part of the Gaussian integration; it asserts no small-scale decay. -/
theorem holder_transpose_gaussian_remainder_growth
    (hgrowth : node_e_u3A_lp_u2D_growthStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ Cp : ℝ, 0 < Cp ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (ζ : ℂ)
        (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P T →
      ∀ (s r : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)),
        MemLp (T s f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ (σ : ℝ) (hσ : 0 < σ),
        MemLp ((T (r + s) f - gaussianAverage hd Q σ hσ (T (r + s) f)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((T (r + s) f - gaussianAverage hd Q σ hσ (T (r + s) f)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          2 * Real.exp (Cp * ‖ζ‖ ^ 2 * (r : ℝ)) *
            (eLpNorm (T s f : FieldPair d → ℂ) (ENNReal.ofReal p)
              (reducedLaw Q)).toReal := by
  obtain ⟨Cp, hCp, hbound⟩ := hgrowth d D.ellipticity D.dependenceRange p hd hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q ζ P T hP hT s r f hf σ hσ
  obtain ⟨hU, hUgrowth⟩ :
      MemLp (T (r + s) f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (T (r + s) f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal (Real.exp (Cp * ‖ζ‖ ^ 2 * (r : ℝ))) *
          eLpNorm (T s f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
    have h := (hbound Q ⟨0, by omega⟩ ζ P T hP hT).1 r (T s f) hf
    simpa only [hT.add hP r s, ContinuousLinearMap.comp_apply] using ⟨h.2.1, h.2.2.2.2.1⟩
  have hG := bootstrap_average_homogeneous_Lp Q ⟨0, by omega⟩ σ hσ 0 p hp
    (T (r + s) f) hU
  change MemLp (gaussianAverage hd Q σ hσ (T (r + s) f) : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q) ∧ _ at hG
  have hGbound :
      (eLpNorm (gaussianAverage hd Q σ hσ (T (r + s) f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (eLpNorm (T (r + s) f : FieldPair d → ℂ) (ENNReal.ofReal p)
        (reducedLaw Q)).toReal := by
    simpa only [homogeneousAverage, gaussianAverage, Complex.zero_im,
      zero_pow (by norm_num : 2 ≠ 0), zero_mul,
      zero_div, Real.exp_zero, one_mul] using hG.2
  have hsub := eLpNorm_sub_le (f := (T (r + s) f : FieldPair d → ℂ))
    (g := (gaussianAverage hd Q σ hσ (T (r + s) f) : FieldPair d → ℂ))
    (μ := reducedLaw Q) (ENNReal.one_le_ofReal.mpr (by linarith only [hp]))
  have hsubReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hU.ne, hG.1.ne⟩) hsub
  rw [ENNReal.toReal_add hU.ne hG.1.ne] at hsubReal
  have hUgrowthReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.ne) hUgrowth
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hUgrowthReal
  refine ⟨hU.sub hG.1, ?_⟩
  linarith only [hsubReal, hGbound, hUgrowthReal]

/-- Caloric replacement for a joint source, including its gradient coordinate.
Unlike the scalar-source specialization, this estimate can retain the
conservative transpose force in that coordinate. -/
theorem holder_transpose_joint_source_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : PDE.ParCoeffField d}
    (hsT : s < T)
    (ha : PDE.IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) (w f : CauchyX d s T)
    (hforced : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      inner ℝ w (holderComparisonT ha 1 φ) =
        inner ℝ f (holderComparisonJ d (PDE.euclideanBall x₀ r) s T r φ)) :
    ∃ v : CauchyX d s T,
      w - v ∈ (LinearMap.range
        ((cauchyJ (d := d) (s := s) (T := T)).comp
          (holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T).subtype)).topologicalClosure ∧
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
        inner ℝ v (holderComparisonT ha 1 φ) = 0) ∧
      (∫ x, cauchyJointValue (w - v) x ^ 2
        ∂slabMeasure d s T) ≤ r ^ 2 * ‖f‖ ^ 2 / (lam / 10) ^ 2 := by
  obtain ⟨z, hz, hweak, hnorm⟩ := holderComparison_representation hsT ha hr i f
  let u := holderComparisonValueScale d s T r z
  refine ⟨w - u, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    exact holderComparisonTestSpace_scaledClosure hr.ne' hz
  · intro φ
    rw [inner_sub_left, hforced φ, holderComparison_decode_pairing ha z φ,
      hweak φ, sub_self]
  · rw [sub_sub_cancel]
    calc
      _ ≤ r ^ 2 * ‖z‖ ^ 2 := holderComparison_decoded_valueSq_le z
      _ ≤ r ^ 2 * (‖f‖ / (lam / 10)) ^ 2 :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hnorm 2) (sq_nonneg r)
      _ = _ := by rw [div_pow]; ring

/-- Joint representatives of the actual transpose orbit and its finite-horizon
L² gradient satisfy the conservative weak equation. The representatives are
chosen before the temporal tests, and each event covers every spatial test. -/
theorem holder_transpose_joint_weak_time_spatial_tests
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) :
    ∃ (G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q))
      (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s) ∧
      (∀ j, IntegrableOn (G j) (Icc (0 : ℝ) (t : ℝ))) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal f) (fun j => G j s)) ∧
      ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
        η 0 = 0 → η t = 0 →
        ∀ᵐ ω ∂reducedLaw Q,
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (t : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) -
              2 * ζ * (ω.1 x j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) := by
  letI := reducedLaw_probability Q
  have hu : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative hu.stronglyMeasurable
  obtain ⟨H, hH, _⟩ := hT.exists_timeL2_gradient_horizon hP f t
  let G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q) := fun j s => (H s) j
  have hGm (j : Fin d) : StronglyMeasurable (G j) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous
      |>.comp_stronglyMeasurable (Lp.stronglyMeasurable H)
  choose V hV heV using fun j => StronglyMeasurable.exists_joint_l2_representative (hGm j)
  have hiG (j : Fin d) : IntegrableOn (G j) (Icc (0 : ℝ) (t : ℝ)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).integrable_comp
      ((Lp.memLp H).integrable (by norm_num))
  have hHcc : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) (H s) :=
    hH.filter_mono (by rw [Measure.restrict_congr_set Ioc_ae_eq_Icc])
  refine ⟨G, U, V, hU, hV, heU, heV, hiG, hHcc, ?_⟩
  intro η η' hη hη' hzero ht
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hiu := hu.continuousOn.integrableOn_Icc (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ))
  have hgrad : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f)
      (fun j => ∫ s in Icc (0 : ℝ) (t : ℝ), η s • G j s) := by
    intro j
    apply HasComplexHorizontalDerivative.integral_of_ae
      (hiu.continuousOn_smul hηc.continuousOn isCompact_Icc)
      ((hiG j).continuousOn_smul hηc.continuousOn isCompact_Icc)
    filter_upwards [hHcc] with s hs
    exact (hs j).smul (η s : ℂ)
  obtain ⟨W, hW, hweak⟩ := hT.time_test_spatial_flux_all_tests hP f η η' hη hη' t hzero ht
  have hsame := hW.unique hgrad
  have hcu := ae_spatial_weighted_integral_joint_l2_representative t hiu hU heU η hηc
  have hcu' := ae_spatial_weighted_integral_joint_l2_representative t hiu hU heU η' hη'
  have hcv (j : Fin d) := ae_spatial_weighted_integral_joint_l2_representative t
    (hiG j) (hV j) (heV j) η hηc
  filter_upwards [hweak, hcu, hcu', ae_all_iff.mpr hcv] with ω he hu hu' hv
  intro φ hφ hφc
  have heq := he φ hφ hφc
  rw [hsame] at heq
  have hleft := integral_congr_ae (hu'.mono fun x hx => congrArg (· * (φ x : ℂ)) hx)
  have hright :
      (∫ x, ∑ j, ((∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), η s • G k s) (translate x ω)) -
        2 * ζ * (ω.1 x j i : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), η s • T s.toNNReal f) (translate x ω)) *
        (coordinateDerivative j φ x : ℂ)) =
      (∫ x, ∑ j, ((∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * V k (s, translate x ω))) -
        2 * ζ * (ω.1 x j i : ℂ) *
          (∫ s in Icc (0 : ℝ) (t : ℝ), (η s : ℂ) * U (s, translate x ω))) *
        (coordinateDerivative j φ x : ℂ)) := by
    apply integral_congr_ae
    filter_upwards [hu, ae_all_iff.mpr hv] with x hx hvs
    simp_rw [hx, hvs]
  rwa [hleft, hright] at heq


private abbrev HolderTransposeTimeWindow (n : ℕ) := Icc (0 : ℝ) (n : ℝ)
private abbrev HolderTransposeTimeJet (n : ℕ) :=
  C(HolderTransposeTimeWindow n, ℝ) × C(HolderTransposeTimeWindow n, ℝ)
private def holderTransposeClamp (n : ℕ) : ℝ → HolderTransposeTimeWindow n :=
  projIcc (0 : ℝ) (n : ℝ) (by positivity)
private def holderTransposeRestrict (n : ℕ) (η : ℝ → ℝ) (hc : Continuous η) :
    C(HolderTransposeTimeWindow n, ℝ) := ⟨fun s => η s, hc.comp continuous_subtype_val⟩
private def holderTransposeJets (n : ℕ) : Set (HolderTransposeTimeJet n) :=
  {q | ∃ (η η' : ℝ → ℝ) (hη : ∀ s, HasDerivAt η (η' s) s) (hη' : Continuous η'),
    η 0 = 0 ∧ η n = 0 ∧ q =
      (holderTransposeRestrict n η
        (continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt),
       holderTransposeRestrict n η' hη')}
private def holderTransposeWeight {n : ℕ} (w : C(HolderTransposeTimeWindow n, ℝ))
    (s : ℝ) : ℝ := w (holderTransposeClamp n s)
private theorem holderTransposeWeight_restrict (n : ℕ) (η : ℝ → ℝ) (hc : Continuous η)
    (F : ℝ → ℂ) :
    (∫ s in Icc (0 : ℝ) (n : ℝ),
      (holderTransposeWeight (holderTransposeRestrict n η hc) s : ℂ) * F s) =
      ∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * F s := by
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [holderTransposeWeight, holderTransposeRestrict, ContinuousMap.coe_mk,
    holderTransposeClamp, projIcc_of_mem (by positivity : (0 : ℝ) ≤ n) hs]

/-- Local integrability permits splitting the actual conservative transpose
flux into scalar temporal pairings, keeping its signed column-force term. -/
private theorem holder_transpose_split_flux
    {d : ℕ} {ν : Measure ℝ} [SFinite ν] (ω : FieldPair d) (i : Fin d) (ζ : ℂ)
    (U : Vec d × ℝ → ℂ) (V : Fin d → Vec d × ℝ → ℂ)
    (hU : ∀ K : Set (Vec d), IsCompact K → Integrable U ((volume.restrict K).prod ν))
    (hV : ∀ k K, IsCompact K → Integrable (V k) ((volume.restrict K).prod ν))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (η : ℝ → ℝ) (hη : Measurable η) (C : ℝ) (hC : ∀ s, ‖η s‖ ≤ C) :
    (∫ x, ∑ j, ((∑ k, (ω.1 x j k : ℂ) *
      (∫ s, (η s : ℂ) * V k (x, s) ∂ν)) -
        2 * ζ * (ω.1 x j i : ℂ) * (∫ s, (η s : ℂ) * U (x, s) ∂ν)) *
          (coordinateDerivative j φ x : ℂ)) =
      (∑ j, ∑ k, ∫ x, (∫ s, (η s : ℂ) * V k (x, s) ∂ν) *
        ((ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ))) -
      2 * ζ * (∑ j, ∫ x, (∫ s, (η s : ℂ) * U (x, s) ∂ν) *
        ((ω.1 x j i : ℂ) * (coordinateDerivative j φ x : ℂ))) := by
  have hm (j k : Fin d) : Continuous (fun x =>
      (ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ)) :=
    (Complex.continuous_ofReal.comp (ω.1.continuous.matrix_elem j k)).mul
      (Complex.continuous_ofReal.comp
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))
  have hc (j k : Fin d) : HasCompactSupport (fun x =>
      (ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ)) :=
    ((hφc.fderiv_apply ℝ (unitVector j)).comp_left (g := Complex.ofReal) rfl).mul_left
  have hp (j k : Fin d) := (CommonTemporalTests.spatial_temporal_pairing
    (hV k) (hm j k) (hc j k) hη hC).1
  have hf (j : Fin d) := (CommonTemporalTests.spatial_temporal_pairing
    hU (hm j i) (hc j i) hη hC).1
  have he : (fun x => ∑ j, ((∑ k, (ω.1 x j k : ℂ) *
      (∫ s, (η s : ℂ) * V k (x, s) ∂ν)) -
        2 * ζ * (ω.1 x j i : ℂ) * (∫ s, (η s : ℂ) * U (x, s) ∂ν)) *
          (coordinateDerivative j φ x : ℂ)) =
    (fun x => (∑ j, ∑ k, (∫ s, (η s : ℂ) * V k (x, s) ∂ν) *
      ((ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ))) -
      2 * ζ * (∑ j, (∫ s, (η s : ℂ) * U (x, s) ∂ν) *
        ((ω.1 x j i : ℂ) * (coordinateDerivative j φ x : ℂ)))) := by
    funext x
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [sub_mul, Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · ring
  rw [he, integral_sub
    (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hp j k)
    ((integrable_finsetSum _ fun j _ => hf j).const_mul (2 * ζ)), integral_const_mul]
  congr 1
  · rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => hp j k]
    exact Finset.sum_congr rfl fun j _ => integral_finsetSum _ fun k _ => hp j k
  · rw [integral_finsetSum _ fun j _ => hf j]

private def holderTransposeFunctional {d : ℕ} (i : Fin d) (ζ : ℂ) (n : ℕ)
    (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ)
    (ω : FieldPair d) (φ : Vec d → ℝ) (q : HolderTransposeTimeJet n) : ℂ :=
  (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (holderTransposeWeight q.2 s : ℂ) *
    U (s, translate x ω)) * (φ x : ℂ)) -
    (1 / 2 : ℂ) * (∫ x, ∑ j,
      ((∑ k, (ω.1 x j k : ℂ) *
        (∫ s in Icc (0 : ℝ) (n : ℝ),
          (holderTransposeWeight q.1 s : ℂ) * V k (s, translate x ω))) -
        2 * ζ * (ω.1 x j i : ℂ) *
          (∫ s in Icc (0 : ℝ) (n : ℝ),
            (holderTransposeWeight q.1 s : ℂ) * U (s, translate x ω))) *
        (coordinateDerivative j φ x : ℂ))

private theorem continuous_holderTransposeFunctional {d : ℕ} (i : Fin d) (ζ : ℂ)
    (n : ℕ) (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ)
    (ω : FieldPair d)
    (hU : ∀ K : Set (Vec d), IsCompact K → Integrable
      (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (hV : ∀ k K, IsCompact K → Integrable
      (fun p : Vec d × ℝ => V k (p.2, translate p.1 ω))
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Continuous (holderTransposeFunctional i ζ n U V ω φ) := by
  have hg : Measurable (holderTransposeClamp n) := continuous_projIcc.measurable
  have hm (j k : Fin d) : Continuous (fun x =>
      (ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ)) :=
    (Complex.continuous_ofReal.comp (ω.1.continuous.matrix_elem j k)).mul
      (Complex.continuous_ofReal.comp
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const))
  have hc (j k : Fin d) : HasCompactSupport (fun x =>
      (ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ)) :=
    ((hφc.fderiv_apply ℝ (unitVector j)).comp_left (g := Complex.ofReal) rfl).mul_left
  have hleft := (CommonTemporalTests.continuous_spatial_temporal_pairing hU
    (Complex.continuous_ofReal.comp hφ.continuous)
    (hφc.comp_left (g := Complex.ofReal) rfl) hg).comp
      (continuous_snd : Continuous (Prod.snd : HolderTransposeTimeJet n → _))
  have hp : Continuous (fun q : HolderTransposeTimeJet n => ∑ j, ∑ k,
      ∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ),
        (holderTransposeWeight q.1 s : ℂ) * V k (s, translate x ω)) *
          ((ω.1 x j k : ℂ) * (coordinateDerivative j φ x : ℂ))) := by
    apply continuous_finsetSum
    intro j _
    apply continuous_finsetSum
    intro k _
    exact (CommonTemporalTests.continuous_spatial_temporal_pairing (hV k)
      (hm j k) (hc j k) hg).comp continuous_fst
  have hf : Continuous (fun q : HolderTransposeTimeJet n => ∑ j,
      ∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ),
        (holderTransposeWeight q.1 s : ℂ) * U (s, translate x ω)) *
          ((ω.1 x j i : ℂ) * (coordinateDerivative j φ x : ℂ))) := by
    apply continuous_finsetSum
    intro j _
    exact (CommonTemporalTests.continuous_spatial_temporal_pairing hU
      (hm j i) (hc j i) hg).comp continuous_fst
  apply (hleft.sub ((continuous_const (y := (1 / 2 : ℂ))).mul
    (hp.sub ((continuous_const (y := 2 * ζ)).mul hf)))).congr
  intro q
  dsimp only [holderTransposeFunctional]
  rw [holder_transpose_split_flux ω i ζ _ _ hU hV φ hφ hφc
    (holderTransposeWeight q.1) (q.1.continuous.measurable.comp hg) ‖q.1‖
    (fun s => q.1.norm_coe_le_norm (holderTransposeClamp n s))]
  rfl

/-- Actual transpose representatives and gradients admit a common event for all
separated temporal and spatial tests on a fixed integer horizon. The signed
force remains inside the conservative flux. -/
theorem holder_transpose_joint_weak_time_all_tests
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (n : ℕ) :
    ∃ (G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q))
      (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s) ∧
      (∀ j, IntegrableOn (G j) (Icc (0 : ℝ) (n : ℝ))) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (n : ℝ)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal f) (fun j => G j s)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        (∀ K : Set (Vec d), IsCompact K →
          Integrable (fun p : Vec d × ℝ => U (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
          ∀ j, Integrable (fun p : Vec d × ℝ => V j (p.2, translate p.1 ω))
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
        ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
          η 0 = 0 → η n = 0 →
        ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) *
            U (s, translate x ω)) * (φ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * V k (s, translate x ω))) -
              2 * ζ * (ω.1 x j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * U (s, translate x ω))) *
              (coordinateDerivative j φ x : ℂ)) := by
  letI := reducedLaw_probability Q
  obtain ⟨G, U, V, hU, hV, heU, heV, hiG, hgrad, he⟩ :=
    holder_transpose_joint_weak_time_spatial_tests Q i ζ P T hP hT f n
  have hlU := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative
      (integrableOn_comp_toNNReal_Icc _ (hT.continuous_apply hP f) (n : ℝ)) hU heU)
  have hlV (j : Fin d) := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative (hiG j) (hV j) (heV j))
  let Test := {φ : Vec d → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ}
  have hall : ∀ᵐ ω ∂reducedLaw Q, ∀ q ∈ holderTransposeJets n, ∀ φ : Test,
      holderTransposeFunctional i ζ n U V ω φ.1 q = 0 := by
    apply CommonTemporalTests.ae_all_parameters_of_ae_fixed (reducedLaw Q)
      (holderTransposeJets n)
      (fun ω (φ : Test) q => holderTransposeFunctional i ζ n U V ω φ.1 q)
    · filter_upwards [hlU, ae_all_iff.mpr hlV] with ω hu hv
      intro φ
      exact (continuous_holderTransposeFunctional i ζ n U V ω hu hv
        φ.1 φ.2.1 φ.2.2).comp continuous_subtype_val
    · rintro q ⟨η, η', hη, hη', hzero, ht, rfl⟩
      filter_upwards [he η η' hη hη' hzero ht] with ω hω
      intro φ
      have heq := hω φ.1 φ.2.1 φ.2.2
      dsimp only [holderTransposeFunctional, Prod.fst, Prod.snd]
      simp_rw [holderTransposeWeight_restrict]
      simp only [NNReal.coe_natCast] at heq
      linear_combination heq
  refine ⟨G, U, V, hU, hV, heU, heV, hiG, hgrad, ?_⟩
  filter_upwards [hlU, ae_all_iff.mpr hlV, hall] with ω hu hv heq
  refine ⟨fun K hK => ⟨hu K hK, fun j => hv j K hK⟩, ?_⟩
  intro η η' hη hη' hzero ht φ hφ hφc
  have he := heq
    (holderTransposeRestrict n η
      (continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt),
      holderTransposeRestrict n η' hη') ⟨η, η', hη, hη', hzero, ht, rfl⟩
        (⟨φ, hφ, hφc⟩ : Test)
  dsimp only [holderTransposeFunctional, Prod.fst, Prod.snd] at he
  simp_rw [holderTransposeWeight_restrict] at he
  linear_combination he

/-- Local L² control for any joint representatives whose gradient agrees
almost everywhere with the actual transpose gradient on a finite horizon. -/
theorem holder_transpose_representatives_memLp
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s)
    (hG : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) (fun j => G j s)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun z : Vec d × ℝ => U (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (t : ℝ)))) ∧
      ∀ j, MemLp (fun z : Vec d × ℝ => V j (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (t : ℝ)))) := by
  let := reducedLaw_probability Q
  have huc : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  have hiU : IntegrableOn (fun s : ℝ => ‖T s.toNNReal f‖ ^ 2)
      (Icc (0 : ℝ) (t : ℝ)) :=
    (huc.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlU := holderComparison_ae_locally_memLp_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hU
    (holderComparison_integrable_sq_joint_l2_representative hiU hU heU)
  obtain ⟨hm, hg, _⟩ := hT.gradientOrbit_horizon_energy hP f t
  have hmcc : MemLp (complexTransposeGradientOrbit Q T f) 2
      (volume.restrict (Icc (0 : ℝ) (t : ℝ))) := by
    rwa [Measure.restrict_congr_set Ioc_ae_eq_Icc] at hm
  have hgcc : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) (complexTransposeGradientOrbit Q T f s) :=
    hg.filter_mono (by rw [Measure.restrict_congr_set Ioc_ae_eq_Icc])
  have hlV (j : Fin d) := by
    have hmj : MemLp (G j) 2 (volume.restrict (Icc (0 : ℝ) (t : ℝ))) := by
      apply (ContinuousLinearMap.comp_memLp'
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j) hmcc).ae_eq
      filter_upwards [hG, hgcc] with s hs hg
      exact congrFun (hg.unique hs) j
    exact holderComparison_ae_locally_memLp_joint_spatial_translate (reducedLaw Q)
      (reducedLaw_stationary Q) (hV j)
      (holderComparison_integrable_sq_joint_l2_representative
        (memLp_two_iff_integrable_sq_norm hmj.aestronglyMeasurable |>.mp hmj)
        (hV j) (heV j))
  filter_upwards [hlU, ae_all_iff.mpr hlV] with ω hu hv
  exact fun K hK => ⟨hu K hK, fun j => hv j K hK⟩

/-- Local integrability extends the conservative transpose equation from
separated tests to every smooth compact spacetime test inside the horizon. -/
theorem holder_transpose_joint_weak_equation_of_separated
    {d : ℕ} (ω : FieldPair d) (i : Fin d) (ζ : ℂ) (n : ℕ)
    (u : Vec d × ℝ → ℂ) (D : Fin d → Vec d × ℝ → ℂ)
    (hu : ∀ K : Set (Vec d), IsCompact K → Integrable u
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (hD : ∀ j K, IsCompact K → Integrable (D j)
      ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))))
    (he : ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
      η 0 = 0 → η n = 0 →
      ∀ (ψ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x, (∫ s in Icc (0 : ℝ) (n : ℝ), (η' s : ℂ) * u (x, s)) * (ψ x : ℂ)) =
          (1 / 2 : ℂ) * (∫ x, ∑ j,
            ((∑ k, (ω.1 x j k : ℂ) *
              (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * D k (x, s))) -
              2 * ζ * (ω.1 x j i : ℂ) *
                (∫ s in Icc (0 : ℝ) (n : ℝ), (η s : ℂ) * u (x, s))) *
              (coordinateDerivative j ψ x : ℂ))) :
    ∀ (φ : Vec d × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ univ ×ˢ Ioo (0 : ℝ) (n : ℝ) →
      let ν := (volume.restrict (Prod.fst '' tsupport φ)).prod
        (volume.restrict (Icc (0 : ℝ) (n : ℝ)))
      (∫ z, u z * (fderiv ℝ φ z (0, 1) : ℂ) ∂ν) =
        ∑ j, ∫ z, ((1 / 2 : ℂ) * (∑ k, (ω.1 z.1 j k : ℂ) * D k z) -
          ζ * (ω.1 z.1 j i : ℂ) * u z) *
          (fderiv ℝ φ z (unitVector j, 0) : ℂ) ∂ν := by
  intro φ hφ hc hs
  let K := Prod.fst '' tsupport φ
  have hK : IsCompact K := hc.image continuous_fst
  let ν := (volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))
  let a : Fin d → Fin d → Vec d → ℂ := fun j k x => (ω.1 x j k : ℂ)
  have ha (j k : Fin d) : Continuous (a j k) :=
    Complex.continuous_ofReal.comp (ω.1.continuous.matrix_elem j k)
  have huK : Integrable u ν := hu K hK
  have hDK (k : Fin d) : Integrable (D k) ν := hD k K hK
  let F : Fin d → Vec d × ℝ → ℂ := fun j z =>
    (1 / 2 : ℂ) * (∑ k, a j k z.1 * D k z) - ζ * a j i z.1 * u z
  have hrow (j k : Fin d) : Integrable (fun z => a j k z.1 * D k z) ν := by
    simpa only [Function.comp_apply, mul_comm] using
      holderComparison_local_mul_integrable hK (hDK k) ((ha j k).comp continuous_fst)
  have hcol (j : Fin d) : Integrable (fun z => a j i z.1 * u z) ν := by
    simpa only [Function.comp_apply, mul_comm] using
      holderComparison_local_mul_integrable hK huK ((ha j i).comp continuous_fst)
  have hF (j : Fin d) : Integrable (F j) ν := by
    exact ((integrable_finsetSum _ fun k _ => hrow j k).const_mul (1 / 2 : ℂ)).sub
      (by simpa only [mul_assoc] using (hcol j).const_mul ζ)
  obtain ⟨δ, hδ, hmargin⟩ := holderComparison_temporal_support_margin hc hs
  have hout := holderComparison_joint_weak_equation_of_separated huK
    (integrable_zero (Vec d × ℝ) ℂ ν) hF hδ (fun j => unitVector j) hφ hc hmargin
  suffices hw : ∀ (η η' : ℝ → ℝ), (∀ s, HasDerivAt η (η' s) s) → Continuous η' →
      η 0 = 0 → η n = 0 →
      ∀ (ψ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ ⊆ K →
        (∫ z, u z * ((η' z.2 * ψ z.1 : ℝ) : ℂ) ∂ν) =
          (∑ j, ∫ z, F j z * ((η z.2 * fderiv ℝ ψ z.1 (unitVector j) : ℝ) : ℂ) ∂ν) +
          ∫ z, (0 : ℂ) * ((η z.2 * ψ z.1 : ℝ) : ℂ) ∂ν by
    simpa only [Pi.zero_apply, zero_mul, integral_zero, add_zero, F] using hout hw
  intro η η' hη hη' hη0 hηn ψ hψ hψc hψs
  have hηc : Continuous η := continuous_iff_continuousAt.mpr fun s => (hη s).continuousAt
  have hcast (g : Vec d → ℝ) : tsupport (fun x => (g x : ℂ)) = tsupport g := by
    unfold tsupport
    congr 1
    ext x
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  have hψC : Continuous (fun x => (ψ x : ℂ)) := Complex.continuous_ofReal.comp hψ.continuous
  have hψCs : tsupport (fun x => (ψ x : ℂ)) ⊆ K := (hcast ψ).subset.trans hψs
  have hd (j : Fin d) : Continuous (fun x => (coordinateDerivative j ψ x : ℂ)) :=
    Complex.continuous_ofReal.comp ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hds (j : Fin d) : tsupport (fun x => (coordinateDerivative j ψ x : ℂ)) ⊆ K := by
    rw [hcast]
    exact (tsupport_fderiv_apply_subset ℝ (unitVector j)).trans hψs
  have hm (j k : Fin d) := (ha j k).mul (hd j)
  have hms (j k : Fin d) : tsupport (fun x => a j k x * (coordinateDerivative j ψ x : ℂ)) ⊆ K :=
    tsupport_mul_subset_right.trans (hds j)
  have hp (j k : Fin d) := holderComparison_local_separated_pairing hK (hDK k)
    (hm j k) (hms j k) hηc
  have hf (j : Fin d) := holderComparison_local_separated_pairing hK huK
    (hm j i) (hms j i) hηc
  have htime := holderComparison_local_separated_pairing hK huK hψC hψCs hη'
  have hsplit := holder_transpose_split_flux ω i ζ u D hu hD ψ hψ hψc
    (holderTransposeWeight (holderTransposeRestrict n η hηc))
    ((holderTransposeRestrict n η hηc).continuous.measurable.comp continuous_projIcc.measurable)
    ‖holderTransposeRestrict n η hηc‖
    (fun s => (holderTransposeRestrict n η hηc).norm_coe_le_norm (holderTransposeClamp n s))
  simp_rw [holderTransposeWeight_restrict] at hsplit
  have heq := he η η' hη hη' hη0 hηn ψ hψ hψc
  rw [hsplit, htime] at heq
  dsimp only [a, Pi.mul_apply] at hp hf
  simp_rw [hp, hf] at heq
  have hproduct (j k : Fin d) : Integrable (fun z => D k z *
      ((η z.2 : ℂ) * (a j k z.1 * (coordinateDerivative j ψ z.1 : ℂ)))) ν :=
    holderComparison_local_mul_integrable hK (hDK k)
      ((Complex.continuous_ofReal.comp (hηc.comp continuous_snd)).mul
        ((hm j k).comp continuous_fst))
  have hforce (j : Fin d) : Integrable (fun z => u z *
      ((η z.2 : ℂ) * (a j i z.1 * (coordinateDerivative j ψ z.1 : ℂ)))) ν :=
    holderComparison_local_mul_integrable hK huK
      ((Complex.continuous_ofReal.comp (hηc.comp continuous_snd)).mul
        ((hm j i).comp continuous_fst))
  have hFpair (j : Fin d) :
      (∫ z, F j z * ((η z.2 * fderiv ℝ ψ z.1 (unitVector j) : ℝ) : ℂ) ∂ν) =
      (1 / 2 : ℂ) * (∑ k, ∫ z, D k z *
        ((η z.2 : ℂ) * (a j k z.1 * (coordinateDerivative j ψ z.1 : ℂ))) ∂ν) -
      ζ * ∫ z, u z * ((η z.2 : ℂ) *
        (a j i z.1 * (coordinateDerivative j ψ z.1 : ℂ))) ∂ν := by
    have hext : (fun z => F j z * ((η z.2 * fderiv ℝ ψ z.1 (unitVector j) : ℝ) : ℂ)) =
        (fun z => (1 / 2 : ℂ) * (∑ k, D k z *
          ((η z.2 : ℂ) * (a j k z.1 * (coordinateDerivative j ψ z.1 : ℂ)))) -
          ζ * (u z * ((η z.2 : ℂ) * (a j i z.1 * (coordinateDerivative j ψ z.1 : ℂ))))) := by
      funext z
      simp only [F, Complex.ofReal_mul, coordinateDerivative, sub_mul,
        Finset.mul_sum, Finset.sum_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        ring
      · ring
    rw [hext, integral_sub
      ((integrable_finsetSum _ fun k _ => hproduct j k).const_mul (1 / 2 : ℂ))
      ((hforce j).const_mul ζ), integral_const_mul, integral_const_mul,
      integral_finsetSum _ fun k _ => hproduct j k]
  simp_rw [hFpair]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, zero_mul, integral_zero, add_zero]
  simp only [Complex.ofReal_mul, coordinateDerivative] at heq ⊢
  linear_combination heq

/-- The actual transpose orbit has locally L² joint representatives satisfying
its conservative equation against every compact interior spacetime test. -/
theorem holder_transpose_joint_weak_spacetime
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q)) (n : ℕ) :
    ∃ (G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q))
      (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      (∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s) ∧
      (∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (n : ℝ)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (T s.toNNReal f) (fun j => G j s)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        (∀ K : Set (Vec d), IsCompact K →
          MemLp (fun z : Vec d × ℝ => U (z.2, translate z.1 ω)) 2
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
          ∀ j, MemLp (fun z : Vec d × ℝ => V j (z.2, translate z.1 ω)) 2
            ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
        ∀ (φ : Vec d × ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ univ ×ˢ Ioo (0 : ℝ) (n : ℝ) →
          let ν := (volume.restrict (Prod.fst '' tsupport φ)).prod
            (volume.restrict (Icc (0 : ℝ) (n : ℝ)))
          (∫ z, U (z.2, translate z.1 ω) * (fderiv ℝ φ z (0, 1) : ℂ) ∂ν) =
            ∑ j, ∫ z, ((1 / 2 : ℂ) *
              (∑ k, (ω.1 z.1 j k : ℂ) * V k (z.2, translate z.1 ω)) -
              ζ * (ω.1 z.1 j i : ℂ) * U (z.2, translate z.1 ω)) *
              (fderiv ℝ φ z (unitVector j, 0) : ℂ) ∂ν := by
  obtain ⟨G, U, V, hU, hV, heU, heV, _, hg, he⟩ :=
    holder_transpose_joint_weak_time_all_tests Q i ζ P T hP hT f n
  have hl : ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun z : Vec d × ℝ => U (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
      ∀ j, MemLp (fun z : Vec d × ℝ => V j (z.2, translate z.1 ω)) 2
        ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
    exact holder_transpose_representatives_memLp hP hT f (n : ℝ≥0) hU hV heU heV hg
  refine ⟨G, U, V, hU, hV, heU, heV, hg, ?_⟩
  filter_upwards [hl, he] with ω hlocal heq
  exact ⟨hlocal, holder_transpose_joint_weak_equation_of_separated ω i ζ n
    (fun z => U (z.2, translate z.1 ω)) (fun j z => V j (z.2, translate z.1 ω))
    (fun K hK => (heq.1 K hK).1) (fun j K hK => (heq.1 K hK).2 j) heq.2⟩

/-- A common samplewise event for every spatial test of the actual transpose
horizontal gradient, with arbitrary measurable joint representatives. -/
theorem holder_transpose_representatives_spatial_common
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s)
    (hG : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) (fun j => G j s)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      ∀ j : Fin d, ∀ ψ : Vec d → ℝ, IsSpatialTest univ ψ →
        (∫ x, U (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
          -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)) := by
  let := reducedLaw_probability Q
  let ν := volume.restrict (Icc (0 : ℝ) (t : ℝ))
  let u : (FieldPair d × ℝ) × Vec d → ℂ := fun q => U (q.1.2, translate q.2 q.1.1)
  let g : Fin d → (FieldPair d × ℝ) × Vec d → ℂ :=
    fun j q => V j (q.1.2, translate q.2 q.1.1)
  have hshift : Measurable (fun q : (FieldPair d × ℝ) × Vec d =>
      (q.1.2, translate q.2 q.1.1)) :=
    (measurable_snd.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hmu : Measurable u := hU.comp hshift
  have hmg j : Measurable (g j) := (hV j).comp hshift
  have hslices : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂ν,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => U (s, translate x ω)) 2 (volume.restrict K) ∧
        ∀ j, MemLp (fun x => V j (s, translate x ω)) 2 (volume.restrict K) := by
    filter_upwards [holder_transpose_representatives_memLp hP hT f t hU hV heU heV hG]
      with ω hω
    have hm : Measurable (fun z : Vec d × ℝ => (z.2, translate z.1 ω)) :=
      measurable_snd.prodMk (Probability.continuous_translate.measurable.comp
        (measurable_fst.prodMk measurable_const))
    have hu := holderComparison_ae_slices_memLp (hU.comp hm) (fun K hK => (hω K hK).1)
    have hv j := holderComparison_ae_slices_memLp ((hV j).comp hm)
      (fun K hK => (hω K hK).2 j)
    filter_upwards [hu, ae_all_iff.mpr hv] with s hsU hsV
    exact fun K hK => ⟨hsU K hK, fun j => hsV j K hK⟩
  have hlu : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (z, x)) 2 (volume.restrict K) := by
    apply (Measure.ae_prod_iff_ae_ae
      (holderComparison_measurableSet_locally_memLp hmu)).mpr
    exact hslices.mono fun ω hω => hω.mono fun s hs => fun K hK => (hs K hK).1
  have hlg j : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => g j (z, x)) 2 (volume.restrict K) := by
    apply (Measure.ae_prod_iff_ae_ae
      (holderComparison_measurableSet_locally_memLp (hmg j))).mpr
    exact hslices.mono fun ω hω => hω.mono fun s hs => fun K hK => (hs K hK).2 j
  have hloc : ∀ᵐ z ∂(reducedLaw Q).prod ν, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => u (z, x)) 2 (volume.restrict K) ∧
      ∀ j, MemLp (fun x => g j (z, x)) 2 (volume.restrict K) := by
    filter_upwards [hlu, ae_all_iff.mpr hlg] with z hzU hzV
    exact fun K hK => ⟨hzU K hK, fun j => hzV j K hK⟩
  apply Measure.ae_ae_of_ae_prod (μ := reducedLaw Q) (ν := ν)
    (p := fun z : FieldPair d × ℝ => ∀ j : Fin d, ∀ ψ : Vec d → ℝ,
      IsSpatialTest univ ψ →
        (∫ x, u (z, x) * (coordinateDerivative j ψ x : ℂ)) =
          -(∫ x, g j (z, x) * (ψ x : ℂ)))
  apply holderComparison_ae_all_spatial_gradients ((reducedLaw Q).prod ν)
    (fun z x => u (z, x)) (fun z j x => g j (z, x)) hloc
  intro j ψ hψ
  have hd : Continuous (coordinateDerivative j ψ) :=
    ((contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const).continuous
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (holderComparison_measurable_spatial_pairing hmu hd.measurable)
    (holderComparison_measurable_spatial_pairing (hmg j)
      hψ.1.continuous.measurable).neg)).mpr
  have hshift' : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      (q.1.1, translate q.2 q.1.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
  apply (Measure.ae_ae_comm (p := fun s ω =>
    (∫ x, U (s, translate x ω) * (coordinateDerivative j ψ x : ℂ)) =
      -(∫ x, V j (s, translate x ω) * (ψ x : ℂ)))
    (measurableSet_eq_fun
      (holderComparison_measurable_spatial_pairing (hU.comp hshift') hd.measurable)
      (holderComparison_measurable_spatial_pairing ((hV j).comp hshift')
        hψ.1.continuous.measurable).neg)).mp
  filter_upwards [hG] with s hs
  have hu := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hU.comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (T s.toNNReal f)).measurable (heU s)
  have hv := ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hV j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G j s)).measurable (heV j s)
  filter_upwards [hs.ae_spatial_test, hu, hv] with ω hω hu hv
  calc
    _ = ∫ x, (T s.toNNReal f) (translate x ω) * (coordinateDerivative j ψ x : ℂ) :=
      integral_congr_ae (hu.mono fun x hx => congrArg (fun q : ℂ => q * _) hx)
    _ = -(∫ x, G j s (translate x ω) * (ψ x : ℂ)) := hω j ψ hψ
    _ = _ := congrArg Neg.neg (integral_congr_ae
      (hv.mono fun x hx => congrArg (fun q : ℂ => q * _) hx.symm))

/-- The transpose representatives satisfy every smooth compact joint
spatial weak-gradient test on one environment event. -/
theorem holder_transpose_representatives_joint_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {G : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U : ℝ × FieldPair d → ℂ} {V : Fin d → ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hV : ∀ j, Measurable (V j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f)
    (heV : ∀ j s, (fun ω => V j (s, ω)) =ᵐ[reducedLaw Q] G j s)
    (hG : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (T s.toNNReal f) (fun j => G j s)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d × ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → ∀ j : Fin d,
        (∫ z, U (z.2, translate z.1 ω) *
          (fderiv ℝ φ z (unitVector j, 0) : ℂ)
          ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
            (volume.restrict (Icc (0 : ℝ) (t : ℝ))))) =
          -(∫ z, V j (z.2, translate z.1 ω) * (φ z : ℂ)
            ∂((volume.restrict (Prod.fst '' tsupport φ)).prod
              (volume.restrict (Icc (0 : ℝ) (t : ℝ))))) := by
  filter_upwards [holder_transpose_representatives_memLp hP hT f t hU hV heU heV hG,
    holder_transpose_representatives_spatial_common hP hT f t hU hV heU heV hG]
    with ω hL hg
  intro φ hφ hc j
  apply holderComparison_joint_weak_gradient_of_spatial_slices
    (u := fun z => U (z.2, translate z.1 ω))
    (v := fun z => V j (z.2, translate z.1 ω))
    (j := j) (hφ := hφ) (hc := hc)
  · intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact (hL K hK).1.integrable (by norm_num)
  · intro K hK
    let : IsFiniteMeasure (volume.restrict K) :=
      isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
    exact ((hL K hK).2 j).integrable (by norm_num)
  · exact hg.mono fun s hs => hs j

/-- The actual transpose orbit supplies the locally L² value and gradient
and both compact C¹ identities required for conservative local comparison. -/
theorem holder_transpose_local_comparison_equations
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (n : ℕ) {b c : ℝ} (hb : 0 ≤ b) (hc : c ≤ n)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        let Ω := PDE.euclideanBall x₀ r ×ˢ Ioo b c
        let u : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
        let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
        let F : Fin d → Vec d × ℝ → ℂ := fun j z =>
          (1 / 2 : ℂ) * (∑ k, (ω.1 z.1 j k : ℂ) * D k z) -
            ζ * (ω.1 z.1 j i : ℂ) * u z
        MemLp u 2 (volume.restrict Ω) ∧
        (∀ j, MemLp (D j) 2 (volume.restrict Ω)) ∧
        (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) b c, ∀ j,
          (∫ z in Ω, u z *
            (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (unitVector j, 0) : ℂ)) =
            -(∫ z in Ω, D j z * ((φ.val : Vec d × ℝ → ℝ) z : ℂ))) ∧
        (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) b c,
          (∫ z in Ω, u z * (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (0, 1) : ℂ)) =
            ∑ j, ∫ z in Ω, F j z *
              (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z (unitVector j, 0) : ℂ)) := by
  obtain ⟨G, U, V, hU, hV, heU, heV, hg, he⟩ :=
    holder_transpose_joint_weak_spacetime Q i ζ P T hP hT f n
  refine ⟨U, V, hU, hV, heU, ?_⟩
  filter_upwards [he, holder_transpose_representatives_joint_gradient
    hP hT f (n : ℝ≥0) hU hV heU heV hg] with ω heq hgrad
  let Ω := PDE.euclideanBall x₀ r ×ˢ Ioo b c
  let K := PDE.euclideanClosedBall x₀ r
  have hK : IsCompact K := PDE.isCompact_euclideanClosedBall x₀ hr.le
  let u : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
  let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
  let F : Fin d → Vec d × ℝ → ℂ := fun j z =>
    (1 / 2 : ℂ) * (∑ k, (ω.1 z.1 j k : ℂ) * D k z) -
      ζ * (ω.1 z.1 j i : ℂ) * u z
  have hsub : Ω ⊆ K ×ˢ Icc (0 : ℝ) (n : ℝ) :=
    Set.prod_mono (PDE.euclideanBall_subset_euclideanClosedBall x₀ r)
      (fun _ hs => ⟨hb.trans hs.1.le, hs.2.le.trans hc⟩)
  have hlocal {w : Vec d × ℝ → ℂ}
      (hw : MemLp w 2 ((volume.restrict K).prod (volume.restrict (Icc 0 (n : ℝ))))) :
      MemLp w 2 (volume.restrict Ω) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hw
    exact hw.mono_measure (Measure.restrict_mono hsub le_rfl)
  let : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hrestrict {w : Vec d × ℝ → ℂ}
      (hw : Integrable w ((volume.restrict K).prod (volume.restrict (Icc 0 (n : ℝ))))) :
      IntegrableOn w Ω := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod] at hw
    exact hw.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hu : MemLp u 2 (volume.restrict Ω) := hlocal (heq.1 K hK).1
  have hD j : MemLp (D j) 2 (volume.restrict Ω) := hlocal ((heq.1 K hK).2 j)
  have huK : Integrable u ((volume.restrict K).prod (volume.restrict (Icc 0 (n : ℝ)))) :=
    (heq.1 K hK).1.integrable (by norm_num)
  have hDK j : Integrable (D j)
      ((volume.restrict K).prod (volume.restrict (Icc 0 (n : ℝ)))) :=
    ((heq.1 K hK).2 j).integrable (by norm_num)
  have ha j k : Continuous (fun z : Vec d × ℝ => (ω.1 z.1 j k : ℂ)) :=
    Complex.continuous_ofReal.comp
      (((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)).comp continuous_fst)
  have hrow j k : IntegrableOn (fun z => (ω.1 z.1 j k : ℂ) * D k z) Ω := by
    simpa only [mul_comm] using hrestrict
      (holderComparison_local_mul_integrable hK (hDK k) (ha j k))
  have hcol j : IntegrableOn (fun z => (ω.1 z.1 j i : ℂ) * u z) Ω := by
    simpa only [mul_comm] using hrestrict
      (holderComparison_local_mul_integrable hK huK (ha j i))
  have hF j : IntegrableOn (F j) Ω :=
    ((integrable_finsetSum _ (fun k _ => hrow j k)).const_mul (1 / 2 : ℂ)).sub
      (by simpa only [mul_assoc] using (hcol j).const_mul ζ)
  refine ⟨hu, hD, ?_, ?_⟩
  · intro φ j
    apply holderComparison_joint_weak_gradient_C1 (PDE.isOpen_euclideanBall x₀ r)
      (hrestrict huK) (hrestrict (hDK j)) j _
      φ.val.property.1 φ.val.property.2.1 φ.property
    intro ψ hψ hψc hsψ
    have he := hgrad ψ hψ hψc j
    simp only [NNReal.coe_natCast] at he
    simp_rw [holderComparison_joint_derivative_pairing_localize hsψ hb hc,
      holderComparison_joint_value_pairing_localize hsψ hb hc] at he
    rw [holderComparison_joint_derivative_pairing_localize hsψ le_rfl le_rfl,
      holderComparison_joint_value_pairing_localize hsψ le_rfl le_rfl]
    exact he
  · intro φ
    have hext := holderComparison_joint_weak_heat_C1 (PDE.isOpen_euclideanBall x₀ r)
      (hrestrict huK) hF (integrable_zero _ _ _) (fun ψ hψ hψc hsψ => ?_)
      φ.val.property.1 φ.val.property.2.1 φ.property
    · simpa only [Pi.zero_apply, zero_mul, integral_zero, add_zero] using hext
    · have he := heq.2 ψ hψ hψc (fun z hz =>
        ⟨Set.mem_univ _, hb.trans_lt (hsψ hz).2.1, (hsψ hz).2.2.trans_le hc⟩)
      change (∫ z, u z * (fderiv ℝ ψ z (0, 1) : ℂ)
          ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod
            (volume.restrict (Icc 0 (n : ℝ))))) =
        ∑ j, ∫ z, F j z * (fderiv ℝ ψ z (unitVector j, 0) : ℂ)
          ∂((volume.restrict (Prod.fst '' tsupport ψ)).prod
            (volume.restrict (Icc 0 (n : ℝ)))) at he
      simp_rw [holderComparison_joint_derivative_pairing_localize hsψ hb hc] at he
      simpa only [Pi.zero_apply, zero_mul, integral_zero, add_zero] using he

/-- A conservative source occupies only the gradient coordinate of the joint
carrier. Its pairing has no radius normalization factor. -/
theorem holder_transpose_flux_source_pairing
    {d : ℕ} {U : Set (Vec d)} {s T r : ℝ}
    {F : Vec d × ℝ → Vec d}
    (hF : ∀ j, MemLp (fun x => F x j) 2 (slabMeasure d s T))
    (φ : holderComparisonTestSpace d U s T) :
    inner ℝ (holderComparisonField (u := 0) (by simp) hF)
      (holderComparisonJ d U s T r φ) =
      ∫ x, PDE.vecDot (F x) (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)
        ∂slabMeasure d s T := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(holderComparisonField_memLp (u := 0) (by simp) hF).coeFn_toLp,
    holderComparisonValueScale_ae (r := r⁻¹) (cauchyJ φ.val),
    (cauchyJFun_memLp φ.val).coeFn_toLp] with x hxF hxJ hxφ
  change inner ℝ ((holderComparisonField_memLp (u := 0) (by simp) hF).toLp _ x)
    (holderComparisonValueScale d s T r⁻¹ (cauchyJ φ.val) x) = _
  rw [hxF, hxJ, cauchyJ_apply, hxφ, WithLp.prod_inner_apply]
  simp only [cauchyJFun, WithLp.ofLp_toLp, Pi.zero_apply, inner_zero_left,
    zero_add, PDE.inner_toHilbertVec_eq_vecDot]

/-- The joint conservative-source norm is its actual Euclidean energy. -/
theorem holder_transpose_flux_source_norm_sq
    {d : ℕ} {s T : ℝ} {F : Vec d × ℝ → Vec d}
    (hF : ∀ j, MemLp (fun x => F x j) 2 (slabMeasure d s T)) :
    ‖holderComparisonField (u := 0) (by simp) hF‖ ^ 2 =
      ∫ x, PDE.vecNormSq (F x) ∂slabMeasure d s T := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(holderComparisonField_memLp (u := 0) (by simp) hF).coeFn_toLp]
    with x hx
  change inner ℝ ((holderComparisonField_memLp (u := 0) (by simp) hF).toLp _ x)
    ((holderComparisonField_memLp (u := 0) (by simp) hF).toLp _ x) = _
  rw [hx, WithLp.prod_inner_apply]
  simp only [WithLp.ofLp_toLp, Pi.zero_apply, inner_zero_left, zero_add,
    PDE.inner_toHilbertVec_eq_vecDot, PDE.vecNormSq]

/-- Caloric replacement for a distributional conservative force, preserving
the spatial weak gradient and the physical radius-squared error estimate. -/
theorem holder_transpose_flux_caloric_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : PDE.ParCoeffField d}
    (hsT : s < T) (ha : PDE.IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d) (w : CauchyX d s T)
    {F : Vec d × ℝ → Vec d}
    (hF : ∀ j, MemLp (fun x => F x j) 2 (slabMeasure d s T))
    (hgradient : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      ∀ j : Fin d,
      (∫ x, cauchyJointValue w x *
        PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
        -(∫ x, cauchyJointGradient w x j *
          (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T))
    (hforced : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      (∫ x, cauchyJointValue w x *
        PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
        (1 / 2 : ℝ) * (∫ x, PDE.vecDot (cauchyJointGradient w x)
          (PDE.matVecMul (PDE.matTranspose (a x))
            (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T) -
        (∫ x, PDE.vecDot (F x) (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)
          ∂slabMeasure d s T)) :
    ∃ v : CauchyX d s T,
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
        ∀ j : Fin d,
        (∫ x, cauchyJointValue v x *
          PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
          -(∫ x, cauchyJointGradient v x j *
            (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T)) ∧
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
        (∫ x, cauchyJointValue v x *
          PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
          (1 / 2 : ℝ) * (∫ x, PDE.vecDot (cauchyJointGradient v x)
            (PDE.matVecMul (PDE.matTranspose (a x))
              (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T)) ∧
      (∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T) ≤
        r ^ 2 * (∫ x, PDE.vecNormSq (F x) ∂slabMeasure d s T) / (lam / 10) ^ 2 := by
  have hpair : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      inner ℝ w (holderComparisonT ha 1 φ) =
        inner ℝ (holderComparisonField (u := 0) (by simp) hF)
          (holderComparisonJ d (PDE.euclideanBall x₀ r) s T r φ) := by
    intro φ
    rw [holderComparison_physical_pairing, hforced φ,
      holder_transpose_flux_source_pairing]
    ring
  obtain ⟨v, hcorrection, hweak, herror⟩ :=
    holder_transpose_joint_source_replacement hsT ha hr i w
      (holderComparisonField (u := 0) (by simp) hF) hpair
  refine ⟨v, ?_, holderComparison_unforced_heat ha v hweak, ?_⟩
  · intro φ j
    exact (holderComparison_spatial_orthogonal_iff v (holderComparisonParTest φ) j).mp
      (holderComparison_unforced_replacement_spatial hcorrection
        (holderComparisonParTest φ) j
        ((holderComparison_spatial_orthogonal_iff w (holderComparisonParTest φ) j).mpr
          (hgradient φ j)))
  · simpa only [holder_transpose_flux_source_norm_sq] using herror

/-- Locally square-integrable fields with conservative forcing admit an
unforced replacement with error controlled by the local vector-source energy.
All supplied equations are interior distributional equations. -/
theorem holder_transpose_local_flux_replacement
    {d : ℕ} {x₀ : Vec d} {s T r lam Lam : ℝ} {a : PDE.ParCoeffField d}
    (hsT : s < T) (ha : PDE.IsParabolicCoeff lam Lam a univ (Icc s T))
    (hr : 0 < r) (i : Fin d)
    {u : Vec d × ℝ → ℝ} {g F : Vec d × ℝ → Vec d}
    (hu : MemLp u 2 (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo s T)))
    (hg : ∀ j, MemLp (fun x => g x j) 2
      (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo s T)))
    (hF : ∀ j, MemLp (fun x => F x j) 2
      (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo s T)))
    (hgrad : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      ∀ j : Fin d,
      (∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
        u x * PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j) =
        -(∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
          g x j * (φ.val : Vec d × ℝ → ℝ) x))
    (hheat : ∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
      (∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
        u x * PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x) =
        (1 / 2 : ℝ) * (∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
          PDE.vecDot (g x) (PDE.matVecMul (PDE.matTranspose (a x))
            (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))) -
        (∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
          PDE.vecDot (F x) (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x))) :
    ∃ v : CauchyX d s T,
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
        ∀ j : Fin d,
        (∫ x, cauchyJointValue v x *
          PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x j ∂slabMeasure d s T) =
          -(∫ x, cauchyJointGradient v x j *
            (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T)) ∧
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) s T,
        (∫ x, cauchyJointValue v x *
          PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) x ∂slabMeasure d s T) =
          (1 / 2 : ℝ) * (∫ x, PDE.vecDot (cauchyJointGradient v x)
            (PDE.matVecMul (PDE.matTranspose (a x))
              (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)) ∂slabMeasure d s T)) ∧
      (∫ z in Ioo s T ×ˢ PDE.euclideanBall x₀ r,
        |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤
        r ^ 2 * (∫ x in PDE.euclideanBall x₀ r ×ˢ Ioo s T,
          PDE.vecNormSq (F x)) / (lam / 10) ^ 2 := by
  let B := PDE.euclideanBall x₀ r
  let hB := PDE.measurableSet_euclideanBall x₀ r
  let w := holderComparisonLocalField hB hu hg
  let F₀ : Vec d × ℝ → Vec d := fun x j =>
    (B ×ˢ Ioo s T).indicator (fun x => F x j) x
  have hF₀ : ∀ j, MemLp (fun x => F₀ x j) 2 (slabMeasure d s T) :=
    fun j => holderComparison_local_indicator_memLp hB (hF j)
  have hFzero (x : Vec d × ℝ) (hx : x ∉ B ×ˢ Ioo s T) : F₀ x = 0 := by
    funext j
    exact Set.indicator_of_notMem hx _
  have hFmem (x : Vec d × ℝ) (hx : x ∈ B ×ˢ Ioo s T) : F₀ x = F x := by
    funext j
    exact Set.indicator_of_mem hx _
  have hFpair (φ : holderComparisonTestSpace d B s T) :
      (∫ x, PDE.vecDot (F₀ x) (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x)
        ∂slabMeasure d s T) =
      ∫ x in B ×ˢ Ioo s T,
        PDE.vecDot (F x) (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) x) := by
    rw [holderComparison_supported_integral _ (by
      intro x hx
      rw [hFzero x hx]
      simp [PDE.vecDot])]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hB.prod measurableSet_Ioo)] with x hx
    rw [hFmem x hx]
  have henergy : (∫ x, PDE.vecNormSq (F₀ x) ∂slabMeasure d s T) =
      ∫ x in B ×ˢ Ioo s T, PDE.vecNormSq (F x) := by
    rw [holderComparison_supported_integral _ (by
      intro x hx
      rw [hFzero x hx]
      simp [PDE.vecNormSq, PDE.vecDot])]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (hB.prod measurableSet_Ioo)] with x hx
    rw [hFmem x hx]
  obtain ⟨v, hvgrad, hvheat, herror⟩ := holder_transpose_flux_caloric_replacement
    hsT ha hr i w hF₀ (holderComparisonLocalField_weakGradient hB hu hg hgrad) (by
      intro φ
      rw [holderComparisonLocalField_value_pairing hB hu hg _ (by
        intro x hx
        simp [PDE.parTimeDeriv, holderComparisonTestSpace_fderiv_zero φ hx]),
        holderComparisonLocalField_gradient_pairing hB hu hg _ (by
          intro x hx
          ext j
          simp [PDE.matVecMul, PDE.parSpaceGrad,
            holderComparisonTestSpace_fderiv_zero φ hx]), hFpair φ]
      exact hheat φ)
  refine ⟨v, hvgrad, hvheat, ?_⟩
  have hvalues : (fun z : ℝ × Vec d => |u z.swap - cauchyJointValue v z.swap| ^ 2)
      =ᵐ[volume.restrict (Ioo s T ×ˢ B)]
        (fun z => |cauchyJointValue w z.swap - cauchyJointValue v z.swap| ^ 2) := by
    filter_upwards [holderComparisonLocalField_cylinder_ae hB hu hg] with z hz
    exact congrArg (fun q : ℝ => |q - cauchyJointValue v z.swap| ^ 2) hz.1.symm
  rw [integral_congr_ae hvalues]
  calc
    _ ≤ ∫ x, cauchyJointValue (w - v) x ^ 2 ∂slabMeasure d s T :=
      holderComparison_cylinder_error_le w v
    _ ≤ _ := by simpa only [henergy] using herror

/-- The real and imaginary conservative transpose forces are locally square
integrable. Their combined Euclidean energy is controlled by the value energy
with constants independent of the phase of the complex force. -/
theorem holder_transpose_flux_components_energy
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {d : ℕ}
    {A : X → Fin d → Fin d → ℝ} {Λ : ℝ}
    (hA : ∀ᵐ x ∂μ, S5Elliptic (A x) Λ)
    (hmA : ∀ j k, AEStronglyMeasurable (fun x => A x j k) μ)
    (i : Fin d) (ζ : ℂ) {u : X → ℂ} (hu : MemLp u 2 μ) :
    let F := fun x j => ζ * (A x j i : ℂ) * u x
    (∀ j, MemLp (fun x => (F x j).re) 2 μ) ∧
    (∀ j, MemLp (fun x => (F x j).im) 2 μ) ∧
    (∫ x, PDE.vecNormSq (fun j => (F x j).re) ∂μ) +
      (∫ x, PDE.vecNormSq (fun j => (F x j).im) ∂μ) ≤
        (d : ℝ) * (Λ * ‖ζ‖) ^ 2 * (∫ x, ‖u x‖ ^ 2 ∂μ) := by
  dsimp only
  let F := fun x j => ζ * (A x j i : ℂ) * u x
  have hb (j : Fin d) : ∀ᵐ x ∂μ, ‖F x j‖ ≤ (Λ * ‖ζ‖) * ‖u x‖ := by
    filter_upwards [hA] with x hx
    dsimp only [F]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hentry : |A x j i| ≤ Λ := by
      have h := s5_row_real_le hx i (Pi.single j (1 : ℝ))
      rw [s5Nrm_single, mul_one] at h
      simpa [Pi.single_apply] using h
    calc
      _ ≤ ‖ζ‖ * Λ * ‖u x‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hentry (norm_nonneg ζ))
        (norm_nonneg _)
      _ = _ := by ring
  have hF (j : Fin d) : MemLp (fun x => F x j) 2 μ :=
    hu.of_le_mul (((Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hmA j i)).const_mul ζ).mul hu.aestronglyMeasurable) (hb j)
  have hre : Integrable (fun x => PDE.vecNormSq (fun j => (F x j).re)) μ := by
    simp only [PDE.vecNormSq_eq_sum_sq]
    exact integrable_finsetSum _ fun j _ => (hF j).re.integrable_sq
  have him : Integrable (fun x => PDE.vecNormSq (fun j => (F x j).im)) μ := by
    simp only [PDE.vecNormSq_eq_sum_sq]
    exact integrable_finsetSum _ fun j _ => (hF j).im.integrable_sq
  refine ⟨fun j => (hF j).re, fun j => (hF j).im, ?_⟩
  rw [← integral_add hre him, ← integral_const_mul]
  apply integral_mono_ae (hre.add him)
    (((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu).const_mul _)
  filter_upwards [ae_all_iff.mpr hb] with x hbx
  have he (z : ℂ) : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  simp only [Pi.add_apply, PDE.vecNormSq_eq_sum_sq, ← Finset.sum_add_distrib, he]
  calc
    _ ≤ ∑ _j : Fin d, (Λ * ‖ζ‖ * ‖u x‖) ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hbx j) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

/-- A compact interior test derivative times a continuous coefficient pairs
integrably with any locally square-integrable complex field. -/
theorem holder_transpose_test_product_integrable
    {d : ℕ} {U : Set (Vec d)} {b c : ℝ} {u q : Vec d × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo b c))) (hq : Continuous q)
    (φ : holderComparisonTestSpace d U b c) (v : Vec d × ℝ) :
    IntegrableOn (fun z => u z * (q z *
      (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z v : ℂ))) (U ×ˢ Ioo b c) := by
  have hd : Continuous (fun z => (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z v : ℂ)) :=
    Complex.continuous_ofReal.comp
      (φ.val.property.1.continuous_fderiv (by norm_num) |>.clm_apply continuous_const)
  have hK : HasCompactSupport
      (fun z => (fderiv ℝ (φ.val : Vec d × ℝ → ℝ) z v : ℂ)) :=
    (φ.val.property.2.1.fderiv_apply ℝ v).comp_left (g := Complex.ofReal) rfl
  exact hu.integrable_mul
    (((hq.mul hd).memLp_of_hasCompactSupport (μ := volume) (p := 2)
      hK.mul_left).restrict (U ×ˢ Ioo b c))

/-- Real linear components of the complex conservative transpose equation
satisfy the corresponding real conservative equation, with the same tests. -/
theorem holder_transpose_local_component_equations
    {d : ℕ} {U : Set (Vec d)} {b c : ℝ}
    {A : PDE.ParCoeffField d}
    (hA : ∀ j k, Continuous (fun z => A z j k))
    {u : Vec d × ℝ → ℂ} {g : Fin d → Vec d × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ Ioo b c)))
    (hg : ∀ j, MemLp (g j) 2 (volume.restrict (U ×ˢ Ioo b c)))
    (i : Fin d) (ζ : ℂ)
    (hgrad : ∀ φ : holderComparisonTestSpace d U b c, ∀ j,
      (∫ z in U ×ˢ Ioo b c, u z *
        (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ)) =
        -(∫ z in U ×ˢ Ioo b c, g j z * ((φ.val : Vec d × ℝ → ℝ) z : ℂ)))
    (hheat : ∀ φ : holderComparisonTestSpace d U b c,
      (∫ z in U ×ˢ Ioo b c, u z *
        (PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z : ℂ)) =
        ∑ j, ∫ z in U ×ˢ Ioo b c,
          ((1 / 2 : ℂ) * (∑ k, (A z j k : ℂ) * g k z) -
            ζ * (A z j i : ℂ) * u z) *
              (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ))
    (L : ℂ →L[ℝ] ℝ) :
    (∀ φ : holderComparisonTestSpace d U b c, ∀ j,
      (∫ z in U ×ˢ Ioo b c, L (u z) *
        PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) =
        -(∫ z in U ×ˢ Ioo b c, L (g j z) * (φ.val : Vec d × ℝ → ℝ) z)) ∧
    (∀ φ : holderComparisonTestSpace d U b c,
      (∫ z in U ×ˢ Ioo b c,
        L (u z) * PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z) =
        (1 / 2 : ℝ) * (∫ z in U ×ˢ Ioo b c,
          PDE.vecDot (fun k => L (g k z))
            (PDE.matVecMul (PDE.matTranspose (A z))
              (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) -
        (∫ z in U ×ˢ Ioo b c,
          PDE.vecDot (fun j => L (ζ * (A z j i : ℂ) * u z))
            (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) := by
  have hLright (z : ℂ) (r : ℝ) : L (z * (r : ℂ)) = L z * r := by
    rw [mul_comm z, ← Complex.real_smul, map_smul, smul_eq_mul, mul_comm]
  have hLleft (r : ℝ) (z : ℂ) : L ((r : ℂ) * z) = r * L z := by
    simpa only [mul_comm] using hLright z r
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  constructor
  · intro φ j
    have hleft := holder_transpose_test_product_integrable (q := fun _ => 1) hu continuous_const φ
      (PDE.basisVec j, 0)
    simp only [one_mul] at hleft
    have hright : IntegrableOn
        (fun z => g j z * ((φ.val : Vec d × ℝ → ℝ) z : ℂ)) (U ×ˢ Ioo b c) :=
      (hg j).integrable_mul
        (((Complex.continuous_ofReal.comp φ.val.property.1.continuous).memLp_of_hasCompactSupport
          (μ := volume) (p := 2)
          (φ.val.property.2.1.comp_left (g := Complex.ofReal) rfl)).restrict (U ×ˢ Ioo b c))
    have he := congrArg L (hgrad φ j)
    change IntegrableOn (fun z => u z *
      (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ)) (U ×ˢ Ioo b c) at hleft
    rw [map_neg, ← L.integral_comp_comm hleft, ← L.integral_comp_comm hright] at he
    simpa only [PDE.parSpaceGrad, hLright] using he
  · intro φ
    have ht := holder_transpose_test_product_integrable (q := fun _ => 1) hu continuous_const φ (0, 1)
    simp only [one_mul] at ht
    have hrow (j k : Fin d) : IntegrableOn
        (fun z => (A z j k : ℂ) * g k z *
          (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ)) (U ×ˢ Ioo b c) := by
      simpa only [PDE.parSpaceGrad, Function.comp_apply, mul_left_comm, mul_assoc] using
        holder_transpose_test_product_integrable (hg k)
          (Complex.continuous_ofReal.comp (hA j k)) φ (PDE.basisVec j, 0)
    have hforce (j : Fin d) : IntegrableOn
        (fun z => ζ * (A z j i : ℂ) * u z *
          (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ)) (U ×ˢ Ioo b c) := by
      simpa only [PDE.parSpaceGrad, Function.comp_apply, mul_left_comm, mul_assoc] using
        holder_transpose_test_product_integrable hu
          ((Complex.continuous_ofReal.comp (hA j i)).const_mul ζ) φ (PDE.basisVec j, 0)
    have hflux (j : Fin d) : IntegrableOn
        (fun z => ((1 / 2 : ℂ) * (∑ k, (A z j k : ℂ) * g k z) -
            ζ * (A z j i : ℂ) * u z) *
              (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j : ℂ)) (U ×ˢ Ioo b c) := by
      apply (((integrable_finsetSum Finset.univ (fun k _ => hrow j k)).const_mul
        (1 / 2 : ℂ)).sub (hforce j)).congr
      filter_upwards [] with z
      dsimp only [Pi.sub_apply]
      simp only [← Finset.sum_mul]
      ring
    have he := congrArg L (hheat φ)
    change IntegrableOn (fun z => u z *
      (PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z : ℂ)) (U ×ˢ Ioo b c) at ht
    rw [← L.integral_comp_comm ht, map_sum] at he
    have hmap (j : Fin d) := L.integral_comp_comm (hflux j)
    simp_rw [← hmap] at he
    have hreal := he
    simp only [hLright, map_sub, hhalf, hLleft, map_sum] at hreal
    have hrrow (j : Fin d) : IntegrableOn
        (fun z => (∑ k, A z j k * L (g k z)) *
          PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) (U ×ˢ Ioo b c) := by
      simpa only [IntegrableOn, Function.comp_apply, map_sum, hLright, hLleft, Finset.sum_mul] using
        L.integrable_comp (integrable_finsetSum Finset.univ (fun k _ => hrow j k))
    have hrforce (j : Fin d) : IntegrableOn
        (fun z => L (ζ * (A z j i : ℂ) * u z) *
          PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) (U ×ˢ Ioo b c) := by
      simpa only [IntegrableOn, Function.comp_apply, hLright] using L.integrable_comp (hforce j)
    have hsplit (j : Fin d) :
        (∫ z in U ×ˢ Ioo b c,
          ((1 / 2 : ℝ) * (∑ k, A z j k * L (g k z)) -
            L (ζ * (A z j i : ℂ) * u z)) *
              PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) =
        (1 / 2 : ℝ) * (∫ z in U ×ˢ Ioo b c,
          (∑ k, A z j k * L (g k z)) *
            PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) -
        (∫ z in U ×ˢ Ioo b c,
          L (ζ * (A z j i : ℂ) * u z) *
            PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) := by
      simp only [sub_mul, mul_assoc (1 / 2 : ℝ)]
      rw [integral_sub ((hrrow j).const_mul (1 / 2)) (hrforce j), integral_const_mul]
    rw [hreal]
    simp_rw [hsplit]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← integral_finsetSum Finset.univ (fun j _ => hrrow j),
      ← integral_finsetSum Finset.univ (fun j _ => hrforce j)]
    simp_rw [holderComparison_flux_sum]
    rfl

/-- The actual transpose orbit has common local real component representatives
whose conservative equations match the caloric replacement interface. -/
theorem holder_transpose_local_component_representatives
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T) (f : Lp ℂ 2 (reducedLaw Q))
    (n : ℕ) {b c : ℝ} (hb : 0 ≤ b) (hc : c ≤ n)
    {x₀ : Vec d} {r : ℝ} (hr : 0 < r) :
    ∃ (U : ℝ × FieldPair d → ℂ) (V : Fin d → ℝ × FieldPair d → ℂ),
      Measurable U ∧ (∀ j, Measurable (V j)) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        let Ω := PDE.euclideanBall x₀ r ×ˢ Ioo b c
        let u : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
        let D : Fin d → Vec d × ℝ → ℂ := fun j z => V j (z.2, translate z.1 ω)
        ∀ L : ℂ →L[ℝ] ℝ,
        MemLp (fun z => L (u z)) 2 (volume.restrict Ω) ∧
        (∀ j, MemLp (fun z => L (D j z)) 2 (volume.restrict Ω)) ∧
        (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) b c, ∀ j,
          (∫ z in Ω, L (u z) *
            PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z j) =
            -(∫ z in Ω, L (D j z) * (φ.val : Vec d × ℝ → ℝ) z)) ∧
        (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) b c,
          (∫ z in Ω, L (u z) * PDE.parTimeDeriv (φ.val : Vec d × ℝ → ℝ) z) =
            (1 / 2 : ℝ) * (∫ z in Ω,
              PDE.vecDot (fun k => L (D k z))
                (PDE.matVecMul (PDE.matTranspose (ω.1 z.1))
                  (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) -
            (∫ z in Ω,
              PDE.vecDot (fun j => L (ζ * (ω.1 z.1 j i : ℂ) * u z))
                (PDE.parSpaceGrad (φ.val : Vec d × ℝ → ℝ) z))) := by
  obtain ⟨U, V, hU, hV, heU, heq⟩ :=
    holder_transpose_local_comparison_equations Q i ζ P T hP hT f n hb hc hr
  refine ⟨U, V, hU, hV, heU, ?_⟩
  filter_upwards [heq] with ω hω
  dsimp only at hω ⊢
  intro L
  have ha (j k : Fin d) : Continuous (fun z : Vec d × ℝ => ω.1 z.1 j k) :=
    (((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)).comp continuous_fst)
  refine ⟨L.comp_memLp' hω.1, fun j => L.comp_memLp' (hω.2.1 j), ?_⟩
  apply holder_transpose_local_component_equations ha hω.1 hω.2.1 i ζ
  · simpa only [PDE.parSpaceGrad, PDE.basisVec, unitVector] using hω.2.2.1
  · simpa only [PDE.parTimeDeriv, PDE.parSpaceGrad, PDE.basisVec, unitVector] using hω.2.2.2


private theorem holder_transpose_real_oscillation_transfer
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u v : X → ℝ}
    (huμ : MemLp u 2 μ) (hvμ : MemLp v 2 μ)
    (huν : MemLp u 2 ν) (hvν : MemLp v 2 ν) {K : ℝ} (hK : 0 ≤ K)
    (hv : Real.sqrt (⨍ x, |v x - (⨍ y, v y ∂μ)| ^ 2 ∂μ) ≤
      K * Real.sqrt (⨍ x, |v x - (⨍ y, v y ∂ν)| ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, |u x - (⨍ y, u y ∂μ)| ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, |u x - v x| ^ 2 ∂μ) +
        K * Real.sqrt (⨍ x, |u x - v x| ^ 2 ∂ν) +
        K * Real.sqrt (⨍ x, |u x - (⨍ y, u y ∂ν)| ^ 2 ∂ν) := by
  have hcomp {σ : Measure X} [IsFiniteMeasure σ] {f g : X → ℝ}
      (hf : MemLp f 2 σ) (hg : MemLp g 2 σ) :
      Real.sqrt (⨍ x, |f x - (⨍ y, f y ∂σ)| ^ 2 ∂σ) ≤
        Real.sqrt (⨍ x, |f x - g x| ^ 2 ∂σ) +
          Real.sqrt (⨍ x, |g x - (⨍ y, g y ∂σ)| ^ 2 ∂σ) := by
    have hmean := mul_le_mul_of_nonneg_left
      (ParabolicBridge.integral_sq_sub_average_le σ hf (⨍ y, g y ∂σ))
      (inv_nonneg.mpr (measureReal_nonneg (μ := σ) (s := univ)))
    have htriangle := ParabolicBridge.sqrt_integral_sq_add_le σ
      (hf.sub hg) (hg.sub (memLp_const (⨍ y, g y ∂σ)))
    simp only [Pi.sub_apply, sub_add_sub_cancel] at htriangle
    have hscaled := mul_le_mul_of_nonneg_left htriangle
      (Real.sqrt_nonneg ((σ.real univ)⁻¹))
    calc
      _ ≤ Real.sqrt (⨍ x, |f x - (⨍ y, g y ∂σ)| ^ 2 ∂σ) := by
        apply Real.sqrt_le_sqrt
        simpa only [average_eq, smul_eq_mul, sq_abs] using hmean
      _ ≤ _ := by
        simpa only [average_eq, smul_eq_mul, sq_abs,
          Real.sqrt_mul (inv_nonneg.mpr (measureReal_nonneg)), mul_add] using hscaled
  have hsmall := hcomp huμ hvμ
  have hlarge := hcomp hvν huν
  have hdist (x : X) : |v x - u x| = |u x - v x| := abs_sub_comm _ _
  simp only [hdist] at hlarge
  have htransfer := hv.trans (mul_le_mul_of_nonneg_left hlarge hK)
  linarith only [hsmall, htransfer]


/-- Conservative forcing has a two-radius oscillation comparison with its
actual caloric replacement error, of order radius squared times flux energy. -/
theorem holder_transpose_real_flux_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (τ : ℝ) (x₀ : EinsteinRelation.Vec d) (r lam Lam : ℝ), 0 < r →
      let a : PDE.ParCoeffField d := fun z => ω.1 z.1
      let cyl := fun ρ : ℝ =>
        Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x₀ ρ
      PDE.IsParabolicCoeff lam Lam a univ (Icc (τ - r ^ 2) τ) →
      ∀ (u : EinsteinRelation.Vec d × ℝ → ℝ) (F g : EinsteinRelation.Vec d × ℝ → EinsteinRelation.Vec d),
      MemLp u 2 (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ)) →
      (∀ j, MemLp (fun z => g z j) 2
        (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ))) →
      (∀ j, MemLp (fun z => F z j) 2
        (volume.restrict (PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ))) →
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) (τ - r ^ 2) τ,
        ∀ j : Fin d,
        (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
          u z * PDE.parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z j) =
          -(∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            g z j * (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z)) →
      (∀ φ : holderComparisonTestSpace d (PDE.euclideanBall x₀ r) (τ - r ^ 2) τ,
        (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
          u z * PDE.parTimeDeriv (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z) =
          (1 / 2 : ℝ) * (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            PDE.vecDot (g z) (PDE.matVecMul (PDE.matTranspose (a z))
              (PDE.parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z))) -
          (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
            PDE.vecDot (F z) (PDE.parSpaceGrad (φ.val : EinsteinRelation.Vec d × ℝ → ℝ) z))) →
      ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      let B := r ^ 2 * (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
        PDE.vecNormSq (F z)) / (lam / 10) ^ 2
      Real.sqrt (⨍ z in cyl (θ * r),
        |u z.swap - (⨍ w in cyl (θ * r), u w.swap)| ^ 2) ≤
        (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
          C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) * Real.sqrt B +
          C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            |u z.swap - (⨍ w in cyl r, u w.swap)| ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hinterior⟩ := hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ
  filter_upwards [hinterior Q hQ] with ω hω
  intro τ x₀ r lam Lam hr
  dsimp only
  intro ha u F g hu hg hF hgrad hheat θ hθ hθhalf
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x₀ ρ
  let B := r ^ 2 * (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ,
    PDE.vecNormSq (F z)) / (lam / 10) ^ 2
  have hsT : τ - r ^ 2 < τ := sub_lt_self _ (sq_pos_of_pos hr)
  obtain ⟨v, hvgrad, hvheat, herror⟩ := holder_transpose_local_flux_replacement
    hsT ha hr (⟨0, by omega⟩ : Fin d) hu hg hF hgrad hheat
  have hv := holderComparison_cylinder_memLp (U := PDE.euclideanBall x₀ r) (cauchyJointValue_memLp v)
  have hvG j := holderComparison_cylinder_memLp (U := PDE.euclideanBall x₀ r) (cauchyJointGradient_memLp v j)
  have hball (ρ : ℝ) (hρ : 0 < ρ) :
      {y : EinsteinRelation.Vec d | euclideanNorm (y - x₀) < ρ} = PDE.euclideanBall x₀ ρ := by
    ext y
    change Real.sqrt (euclideanSq (y - x₀)) < ρ ↔ PDE.vecNormSq (y - x₀) < ρ ^ 2
    rw [Real.sqrt_lt' hρ]
    rfl
  have hωr := hω τ x₀ r hr
  dsimp only at hωr
  rw [hball r hr] at hωr
  have hvdecay := hωr (fun z => cauchyJointValue v z.swap)
    (fun j z => cauchyJointGradient v z.swap j) hv hvG
    (fun φ hφ hc hs j => holderComparison_cylinder_weakGradient v hvgrad
      φ (hφ.of_le (by norm_num)) hc hs j)
    (fun φ hφ hc hs => holderComparison_cylinder_heat _ v hvheat
      φ (hφ.of_le (by norm_num)) hc hs) θ hθ hθhalf
  rw [hball (θ * r) (mul_pos hθ hr)] at hvdecay
  have hsub : cyl (θ * r) ⊆ cyl r := by
    have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
    have hsq : (θ * r) ^ 2 ≤ r ^ 2 := sq_le_sq₀ (by positivity) hr.le |>.mpr hθr
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], hz.1.2⟩, (PDE.euclideanBall_mono (by positivity) hθr) hz.2⟩
  have hu' : MemLp (fun z : ℝ × EinsteinRelation.Vec d => u z.swap) 2 (volume.restrict (cyl r)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu ⊢
    exact hu.comp_measurePreserving Measure.measurePreserving_swap
  have hfinit (ρ : ℝ) (hρ : 0 ≤ ρ) : IsFiniteMeasure (volume.restrict (cyl ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    have hs : cyl ρ ⊆ Icc (τ - ρ ^ 2) τ ×ˢ PDE.euclideanClosedBall x₀ ρ :=
      Set.prod_mono Ioo_subset_Icc_self (PDE.euclideanBall_subset_euclideanClosedBall x₀ ρ)
    exact ((measure_mono hs).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x₀ hρ)).measure_lt_top)).ne
  let := hfinit r hr.le
  let := hfinit (θ * r) (by positivity)
  have hμ : volume.restrict (cyl (θ * r)) ≤ volume.restrict (cyl r) :=
    Measure.restrict_mono hsub le_rfl
  have heint : Integrable (fun z : ℝ × EinsteinRelation.Vec d =>
      |u z.swap - cauchyJointValue v z.swap| ^ 2) (volume.restrict (cyl r)) := by
    simpa only [sq_abs, Pi.sub_apply] using (hu'.sub hv).integrable_sq
  have herrsmall : (∫ z in cyl (θ * r),
      |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤ B :=
    (integral_mono_measure hμ (ae_of_all _ fun _ => sq_nonneg _) heint).trans herror
  have hnormerr (ρ : ℝ) (he : (∫ z in cyl ρ,
      |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤ B) :
      Real.sqrt (⨍ z in cyl ρ, |u z.swap - cauchyJointValue v z.swap| ^ 2) ≤
        Real.sqrt ((volume.real (cyl ρ))⁻¹) * Real.sqrt B := by
    rw [average_eq, smul_eq_mul, measureReal_restrict_apply_univ,
      Real.sqrt_mul (inv_nonneg.mpr (measureReal_nonneg))]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he) (Real.sqrt_nonneg _)
  have hcomparison := holder_transpose_real_oscillation_transfer
    (hu'.mono_measure hμ) (hv.mono_measure hμ) hu' hv
    (show 0 ≤ C * θ ^ α by positivity) hvdecay
  have hsmall := hnormerr (θ * r) herrsmall
  have hlarge := mul_le_mul_of_nonneg_left (hnormerr r herror)
    (show 0 ≤ C * θ ^ α by positivity)
  change _ ≤ _ at hcomparison
  nlinarith only [hcomparison, hsmall, hlarge]


private theorem holder_transpose_complex_oscillation_transfer
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {u : X → ℂ}
    (hμ : MemLp u 2 μ) (hν : MemLp u 2 ν) {A B K : ℝ}
    (hK : 0 ≤ K)
    (hre : Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) ≤
      A * Real.sqrt B + K * Real.sqrt
        (⨍ x, |(u x).re - (⨍ y, (u y).re ∂ν)| ^ 2 ∂ν))
    (him : Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ) ≤
      A * Real.sqrt B + K * Real.sqrt
        (⨍ x, |(u x).im - (⨍ y, (u y).im ∂ν)| ^ 2 ∂ν)) :
    Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂μ)‖ ^ 2 ∂μ) ≤
      2 * A * Real.sqrt B + 2 * K *
        Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
  have hsum (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
      Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
      Real.sq_sqrt (add_nonneg ha hb), Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  have hs : Real.sqrt ((⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) +
      (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ)) ≤
      Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂μ)| ^ 2 ∂μ) +
      Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂μ)| ^ 2 ∂μ) :=
    hsum _ _ (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  rw [← holder_complex_oscillation_sq hμ] at hs
  have hr : Real.sqrt (⨍ x, |(u x).re - (⨍ y, (u y).re ∂ν)| ^ 2 ∂ν) ≤
      Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
    apply Real.sqrt_le_sqrt
    rw [holder_complex_oscillation_sq hν]
    exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)
  have hi : Real.sqrt (⨍ x, |(u x).im - (⨍ y, (u y).im ∂ν)| ^ 2 ∂ν) ≤
      Real.sqrt (⨍ x, ‖u x - (⨍ y, u y ∂ν)‖ ^ 2 ∂ν) := by
    apply Real.sqrt_le_sqrt
    rw [holder_complex_oscillation_sq hν]
    exact le_add_of_nonneg_left (integral_nonneg fun _ => sq_nonneg _)
  have hr' := mul_le_mul_of_nonneg_left hr hK
  have hi' := mul_le_mul_of_nonneg_left hi hK
  linarith


/-- Physical symmetric ellipticity supplies the exact library coefficient
convention for the unscaled transpose comparison. -/
theorem holder_transpose_parabolic_coeff {d : ℕ} {L : ℝ}
    (hL : 1 ≤ L) {ω : FieldPair d}
    (hω : IsElliptic L (fun x => ω.1 x)) (b c : ℝ) :
    PDE.IsParabolicCoeff L⁻¹ L (fun z => ω.1 z.1) univ (Icc b c) := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  refine ⟨fun j k => ?_, ae_of_all _ fun z => ?_⟩
  · exact (((continuous_apply k).comp ((continuous_apply j).comp
      ω.1.continuous)).comp continuous_fst).measurable.aemeasurable
  · have hs := ParabolicBridge.isEllipticMatrix_smul_of_symm_bounds hL
      (hω z.1).1 (fun ξ => ((hω z.1).2 ξ).1) (fun ξ => ((hω z.1).2 ξ).2)
    have hu := PDE.isEllipticMatrix_smul (inv_pos.mpr hLp) hs
    simpa only [smul_smul, inv_mul_cancel₀ hLp.ne', one_smul, mul_one,
      pow_two, ← mul_assoc, one_mul] using hu


/-- The actual complex transpose orbit has a two-radius oscillation estimate.
Its conservative source is controlled by radius times the local value energy,
with structural constants chosen before the environment and complex force. -/
theorem holder_transpose_orbit_oscillation_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (τ : ℝ) (x₀ : Vec d) (r : ℝ),
      0 < r → 0 < τ - r ^ 2 →
    ∃ (U : ℝ × FieldPair d → ℂ), Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q,
        let u := fun z : Vec d × ℝ => U (z.2, translate z.1 ω)
        let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x₀ ρ
        let L := Real.exp (2 * D.ellipticity) * D.ellipticity
        let B := r ^ 2 * ((d : ℝ) * (L * ‖ζ‖) ^ 2 *
          (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ, ‖u z‖ ^ 2)) /
            (L⁻¹ / 10) ^ 2
        MemLp (fun z : ℝ × Vec d => u z.swap) 2 (volume.restrict (cyl r)) ∧
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
          Real.sqrt (⨍ z in cyl (θ * r),
            ‖u z.swap - (⨍ w in cyl (θ * r), u w.swap)‖ ^ 2) ≤
          2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
            C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) * Real.sqrt B +
          2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            ‖u z.swap - (⨍ w in cyl r, u w.swap)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hall⟩ := holder_transpose_real_flux_comparison hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ i ζ P T hP hT f τ x₀ r hr hb
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨U, V, hU, hV, heU, hlocal⟩ := holder_transpose_local_comparison_equations
    Q i ζ P T hP hT f ⌈τ⌉₊ hb.le (Nat.le_ceil τ) hr
  refine ⟨U, hU, heU, ?_⟩
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hL : 1 ≤ L := one_le_mul_of_one_le_of_one_le
    (Real.one_le_exp (by linarith [D.one_le_ellipticity])) D.one_le_ellipticity
  filter_upwards [hlocal, hall Q hQ, c4_ae_reduced_physical_elliptic Q] with ω hloc hc hell
  dsimp only at hloc ⊢
  obtain ⟨hu, hG, hgrad, hheat⟩ := hloc
  let Ω := PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ
  let u := fun z : Vec d × ℝ => U (z.2, translate z.1 ω)
  let g := fun j (z : Vec d × ℝ) => V j (z.2, translate z.1 ω)
  let F := fun (z : Vec d × ℝ) j => ζ * (ω.1 z.1 j i : ℂ) * u z
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x₀ ρ
  have hac (j k : Fin d) : Continuous (fun z : Vec d × ℝ => ω.1 z.1 j k) :=
    ((continuous_apply k).comp ((continuous_apply j).comp ω.1.continuous)).comp continuous_fst
  have hsource := holder_transpose_flux_components_energy
    (ae_of_all (volume.restrict Ω) fun z => s5Elliptic_of_isElliptic hL hell z.1)
    (fun j k => (hac j k).aestronglyMeasurable) i ζ hu
  have hcomponent (R : ℂ →L[ℝ] ℝ) :=
    holder_transpose_local_component_equations hac hu hG i ζ
      (by simpa only [PDE.parSpaceGrad, PDE.basisVec, unitVector] using hgrad)
      (by simpa only [PDE.parTimeDeriv, PDE.parSpaceGrad, PDE.basisVec, unitVector] using hheat) R
  have hu' : MemLp (fun z : ℝ × Vec d => u z.swap) 2 (volume.restrict (cyl r)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hu ⊢
    exact hu.comp_measurePreserving Measure.measurePreserving_swap
  refine ⟨hu', ?_⟩
  intro θ hθ hθhalf
  have ha := holder_transpose_parabolic_coeff hL hell (τ - r ^ 2) τ
  have hre := hc τ x₀ r L⁻¹ L hr ha (fun z => (u z).re) (fun z j => (F z j).re)
    (fun z j => (g j z).re) hu.re (fun j => (hG j).re) hsource.1
    (hcomponent Complex.reCLM).1 (hcomponent Complex.reCLM).2 θ hθ hθhalf
  have him := hc τ x₀ r L⁻¹ L hr ha (fun z => (u z).im) (fun z j => (F z j).im)
    (fun z j => (g j z).im) hu.im (fun j => (hG j).im) hsource.2.1
    (hcomponent Complex.imCLM).1 (hcomponent Complex.imCLM).2 θ hθ hθhalf
  dsimp only at hre him hsource
  have henergy (R : ℂ → ℝ)
      (hR : (∫ z in Ω, PDE.vecNormSq (fun j => R (F z j))) ≤
        (d : ℝ) * (L * ‖ζ‖) ^ 2 * (∫ z in Ω, ‖u z‖ ^ 2)) :
      Real.sqrt (r ^ 2 * (∫ z in Ω, PDE.vecNormSq (fun j => R (F z j))) /
        (L⁻¹ / 10) ^ 2) ≤
      Real.sqrt (r ^ 2 * ((d : ℝ) * (L * ‖ζ‖) ^ 2 * (∫ z in Ω, ‖u z‖ ^ 2)) /
        (L⁻¹ / 10) ^ 2) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hR (sq_nonneg _)) (sq_nonneg _))
  have hreenergy := henergy Complex.re
    ((le_add_of_nonneg_right (integral_nonneg fun _ => PDE.vecNormSq_nonneg _)).trans hsource.2.2)
  have himenergy := henergy Complex.im
    ((le_add_of_nonneg_left (integral_nonneg fun _ => PDE.vecNormSq_nonneg _)).trans hsource.2.2)
  have hA : 0 ≤ Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
      C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹) := by positivity
  have hre' := hre.trans (add_le_add (mul_le_mul_of_nonneg_left hreenergy hA) le_rfl)
  have him' := him.trans (add_le_add (mul_le_mul_of_nonneg_left himenergy hA) le_rfl)
  have hθr : θ * r ≤ r := mul_le_of_le_one_left hr.le (by linarith)
  have hsub : cyl (θ * r) ⊆ cyl r := by
    have hs := (sq_le_sq₀ (mul_pos hθ hr).le hr.le).mpr hθr
    exact Set.prod_mono (fun s hs' => ⟨by linarith [hs'.1], hs'.2⟩)
      (PDE.euclideanBall_mono (mul_pos hθ hr).le hθr)
  have hfinit (ρ : ℝ) (hρ : 0 ≤ ρ) : IsFiniteMeasure (volume.restrict (cyl ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    exact ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall x₀ ρ))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x₀ hρ)).measure_lt_top)).ne
  let := hfinit r hr.le
  let := hfinit (θ * r) (by positivity)
  have hμ := hu'.mono_measure (Measure.restrict_mono hsub le_rfl)
  simpa only [L, Ω, u, cyl, mul_assoc] using holder_transpose_complex_oscillation_transfer hμ hu'
    (show 0 ≤ C * θ ^ α by positivity) hre' him'


/-- Joint representatives of the same environment orbit agree on almost every
physical spacetime section, on one event before choosing a local domain. -/
theorem holder_transpose_physical_representative_eq
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (U V : ℝ × FieldPair d → ℂ) (hU : Measurable U) (hV : Measurable V)
    (hUV : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (fun z : Vec d × ℝ => U (z.2, translate z.1 ω)) =ᵐ[volume]
        fun z => V (z.2, translate z.1 ω) := by
  let Φ : (Vec d × ℝ) × FieldPair d → ℝ × FieldPair d :=
    fun z => (z.1.2, translate z.1.1 z.2)
  have hΦ : Measurable Φ := measurable_fst.snd.prodMk
    (Probability.continuous_translate.measurable.comp
      (measurable_fst.fst.prodMk measurable_snd))
  have he : MeasurableSet {z : (Vec d × ℝ) × FieldPair d |
      U (z.1.2, translate z.1.1 z.2) = V (z.1.2, translate z.1.1 z.2)} :=
    measurableSet_eq_fun (hU.comp hΦ) (hV.comp hΦ)
  rw [Measure.volume_eq_prod]
  apply (Measure.ae_ae_comm he).mp
  refine ae_of_all _ fun z => ?_
  exact (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) z.1).quasiMeasurePreserving.ae (hUV z.2)

/-- The actual transpose comparison holds for any jointly measurable orbit
representative. Thus countably many radii can use the same physical field. -/
theorem holder_transpose_orbit_oscillation_of_representative
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ (τ : ℝ) (x₀ : Vec d) (r : ℝ), 0 < r → 0 < τ - r ^ 2 →
      ∀ᵐ ω ∂reducedLaw Q,
        let u := fun z : Vec d × ℝ => U (z.2, translate z.1 ω)
        let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x₀ ρ
        let L := Real.exp (2 * D.ellipticity) * D.ellipticity
        let B := r ^ 2 * ((d : ℝ) * (L * ‖ζ‖) ^ 2 *
          (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ, ‖u z‖ ^ 2)) /
            (L⁻¹ / 10) ^ 2
        MemLp (fun z : ℝ × Vec d => u z.swap) 2 (volume.restrict (cyl r)) ∧
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
          Real.sqrt (⨍ z in cyl (θ * r),
            ‖u z.swap - (⨍ w in cyl (θ * r), u w.swap)‖ ^ 2) ≤
          2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
            C * θ ^ α * Real.sqrt ((volume.real (cyl r))⁻¹)) * Real.sqrt B +
          2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            ‖u z.swap - (⨍ w in cyl r, u w.swap)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hcomparison⟩ :=
    holder_transpose_orbit_oscillation_comparison hinterior d hd D
  refine ⟨α, C, hα, hα1, hC, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ x₀ r hr hb
  obtain ⟨V, hV, heV, hbound⟩ := hcomparison Q hQ i ζ P T hP hT f τ x₀ r hr hb
  have he := holder_transpose_physical_representative_eq Q U V hU hV
    (fun s => (heU s).trans (heV s).symm)
  filter_upwards [he, hbound] with ω heq hbnd
  dsimp only at hbnd ⊢
  let u := fun z : Vec d × ℝ => U (z.2, translate z.1 ω)
  let v := fun z : Vec d × ℝ => V (z.2, translate z.1 ω)
  have he' : (fun z : ℝ × Vec d => u z.swap) =ᵐ[volume] fun z => v z.swap := by
    rw [Measure.volume_eq_prod] at heq ⊢
    exact Measure.measurePreserving_swap.quasiMeasurePreserving.ae heq
  have hosc (S : Set (ℝ × Vec d)) :
      Real.sqrt (⨍ z in S, ‖u z.swap - (⨍ w in S, u w.swap)‖ ^ 2) =
        Real.sqrt (⨍ z in S, ‖v z.swap - (⨍ w in S, v w.swap)‖ ^ 2) := by
    have hS := ae_restrict_of_ae (s := S) he'
    have hm := average_congr hS
    apply congrArg Real.sqrt
    apply average_congr
    filter_upwards [hS] with z hz
    rw [hz, hm]
  have henergy : (∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ, ‖u z‖ ^ 2) =
      ∫ z in PDE.euclideanBall x₀ r ×ˢ Ioo (τ - r ^ 2) τ, ‖v z‖ ^ 2 :=
    integral_congr_ae (Filter.EventuallyEq.fun_comp (ae_restrict_of_ae heq)
      (fun w : ℂ => ‖w‖ ^ 2))
  refine ⟨(memLp_congr_ae (ae_restrict_of_ae he')).mpr hbnd.1, ?_⟩
  intro θ hθ hθhalf
  simp only [u, v] at hosc henergy
  simpa only [← hosc, ← henergy] using hbnd.2 θ hθ hθhalf


/-- Oscillation coupled to its mean has a geometric contraction in a small
force regime. The weight and threshold precede the force size and sequences;
the force-weighted mean is retained throughout the iteration. -/
theorem holder_transpose_augmented_iteration
    (a q κ K J : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (hκ : κ < 1)
    (haκ : a < κ) (hqκ : q < κ) (hK : 0 ≤ K) (hJ : 0 ≤ J) :
    ∃ H c : ℝ, 0 < H ∧ 0 < c ∧
      ∀ (m : ℝ), 0 ≤ m → m ≤ c → ∀ (E M : ℕ → ℝ),
      (∀ n, 0 ≤ E n) → (∀ n, 0 ≤ M n) →
      (∀ n, E (n + 1) ≤ a * E n + K * m * q ^ n * (E n + M n)) →
      (∀ n, M (n + 1) ≤ M n + J * E n) →
      ∀ n, E n + H * m * q ^ n * M n ≤
        κ ^ n * (E 0 + H * m * M 0) := by
  have hden : 0 < κ - q := sub_pos.mpr hqκ
  let H := (K + 1) / (κ - q)
  have hH : 0 < H := div_pos (by linarith only [hK]) hden
  have hHcancel : H * (κ - q) = K + 1 := div_mul_cancel₀ _ hden.ne'
  have hmean : K + H * q ≤ κ * H := by nlinarith only [hHcancel]
  let A := K + H * q * J
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let c := (κ - a) / (A + 1)
  have hc : 0 < c := div_pos (sub_pos.mpr haκ) (by linarith only [hA])
  have hccancel : c * (A + 1) = κ - a :=
    div_mul_cancel₀ _ (by linarith only [hA])
  refine ⟨H, c, hH, hc, ?_⟩
  intro m hm hmc E M hE hM hstep hmeanstep
  have hq1 : q ≤ 1 := hqκ.le.trans hκ.le
  have hmA : m * A ≤ κ - a := by
    have hmul := mul_le_mul_of_nonneg_right hmc (show 0 ≤ A + 1 by linarith)
    rw [hccancel] at hmul
    nlinarith only [hmul, hm]
  have hcontraction (n : ℕ) :
      E (n + 1) + H * m * q ^ (n + 1) * M (n + 1) ≤
        κ * (E n + H * m * q ^ n * M n) := by
    have hpow : q ^ n ≤ 1 := pow_le_one₀ hq hq1
    have hforce : K * m * q ^ n ≤ K * m :=
      mul_le_of_le_one_right (mul_nonneg hK hm) hpow
    have hweighted : H * m * q ^ (n + 1) * J ≤ H * m * q * J := by
      rw [pow_succ]
      have hmul := mul_le_of_le_one_right
        (show 0 ≤ H * m * q * J by positivity) hpow
      nlinarith only [hmul]
    have hcoef : a + K * m * q ^ n + H * m * q ^ (n + 1) * J ≤ κ := by
      dsimp only [A] at hmA
      nlinarith only [hforce, hweighted, hmA]
    calc
      E (n + 1) + H * m * q ^ (n + 1) * M (n + 1) ≤
          (a * E n + K * m * q ^ n * (E n + M n)) +
            H * m * q ^ (n + 1) * (M n + J * E n) :=
        add_le_add (hstep n)
          (mul_le_mul_of_nonneg_left (hmeanstep n) (by positivity))
      _ = (a + K * m * q ^ n + H * m * q ^ (n + 1) * J) * E n +
          (K + H * q) * (m * q ^ n * M n) := by rw [pow_succ]; ring
      _ ≤ κ * E n + (κ * H) * (m * q ^ n * M n) :=
        add_le_add (mul_le_mul_of_nonneg_right hcoef (hE n))
          (mul_le_mul_of_nonneg_right hmean
            (mul_nonneg (mul_nonneg hm (pow_nonneg hq n)) (hM n)))
      _ = κ * (E n + H * m * q ^ n * M n) := by ring
  intro n
  induction n with
  | zero => simp only [pow_zero, mul_one, one_mul, le_refl]
  | succ n ih =>
    calc
      _ ≤ κ * (E n + H * m * q ^ n * M n) := hcontraction n
      _ ≤ κ * (κ ^ n * (E 0 + H * m * M 0)) :=
        mul_le_mul_of_nonneg_left ih (hq.trans hqκ.le)
      _ = _ := by rw [pow_succ]; ring


/-- The unforced exponent selects a structural scale at which both the
oscillation coefficient and the radius shrink faster than the desired decay. -/
theorem holder_transpose_augmented_scales (C α : ℝ)
    (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 / 2 ∧
      θ < θ ^ (α / 2) ∧ 2 * C * θ ^ α < θ ^ (α / 2) ∧ θ ^ (α / 2) < 1 := by
  obtain ⟨θ, c, hθ, hθhalf, hc, hbound⟩ :=
    holder_comparison_scales 0 (2 * C) α (by linarith only [hC]) hα
  have ha := hbound 0 1 (by linarith only [hc])
  simp only [zero_mul, mul_zero, add_zero] at ha
  have hhalf : 0 < α / 2 := by linarith only [hα]
  have hθ1 : θ < 1 := by linarith only [hθhalf]
  refine ⟨θ, hθ, hθhalf,
    Real.self_lt_rpow_of_lt_one hθ hθ1 (by linarith only [hα1]), ?_, ?_⟩
  · exact ha.trans_lt (Real.rpow_lt_rpow (by positivity) (by linarith only [hθ]) hhalf)
  · exact Real.rpow_lt_one hθ.le hθ1 hhalf


/-- The norm of a complex average is controlled by its mean square. -/
theorem holder_transpose_norm_average_le
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℂ} (hu : MemLp u 2 μ) (hpos : 0 < μ.real univ) :
    ‖⨍ x, u x ∂μ‖ ≤ Real.sqrt (⨍ x, ‖u x‖ ^ 2 ∂μ) := by
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    (ae_of_all μ fun x => norm_nonneg (u x)) (ae_of_all μ fun _ => zero_le_one)
    (show MemLp (fun x => ‖u x‖) (ENNReal.ofReal 2) μ by simpa only [ENNReal.ofReal_ofNat] using hu.norm)
    (show MemLp (fun _ : X => (1 : ℝ)) (ENNReal.ofReal 2) μ from memLp_const 1)
  simp only [mul_one, Real.rpow_two, Real.one_rpow, one_pow, integral_const, smul_eq_mul,
    ← Real.sqrt_eq_rpow] at hholder
  have hi : ‖∫ x, u x ∂μ‖ ≤
      Real.sqrt (∫ x, ‖u x‖ ^ 2 ∂μ) * Real.sqrt (μ.real univ) :=
    (norm_integral_le_integral_norm _).trans hholder
  rw [average_eq, average_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr hpos.le), smul_eq_mul]
  refine (mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hpos.le)).trans (le_of_eq ?_)
  rw [Real.sqrt_mul (inv_nonneg.mpr hpos.le), Real.sqrt_inv]
  have hp := (Real.sqrt_pos.mpr hpos).ne'
  field_simp
  rw [Real.sq_sqrt hpos.le]
  ring

/-- Restricting a mean square costs the square root of the volume ratio. -/
theorem holder_transpose_nested_mean_square
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X) (hνμ : ν ≤ μ)
    {u : X → ℂ} (hu : MemLp u 2 μ)
    (hμ : 0 < μ.real univ) (hν : 0 < ν.real univ) :
    Real.sqrt (⨍ x, ‖u x‖ ^ 2 ∂ν) ≤
      Real.sqrt (μ.real univ / ν.real univ) *
        Real.sqrt (⨍ x, ‖u x‖ ^ 2 ∂μ) := by
  have hi := integral_mono_measure hνμ (ae_of_all μ fun x => sq_nonneg ‖u x‖)
    ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)
  rw [← Real.sqrt_mul (div_nonneg hμ.le hν.le)]
  apply Real.sqrt_le_sqrt
  simp only [average_eq, smul_eq_mul]
  calc
    (ν.real univ)⁻¹ * ∫ x, ‖u x‖ ^ 2 ∂ν ≤
        (ν.real univ)⁻¹ * ∫ x, ‖u x‖ ^ 2 ∂μ :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hν.le)
    _ = μ.real univ / ν.real univ *
        ((μ.real univ)⁻¹ * ∫ x, ‖u x‖ ^ 2 ∂μ) := by
      field_simp

/-- The mean on a smaller domain differs by at most the outer oscillation
multiplied by the square root of the volume ratio. -/
theorem holder_transpose_nested_mean
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≤ μ)
    {u : X → ℂ} (hu : MemLp u 2 μ)
    (hμ : 0 < μ.real univ) (hν : 0 < ν.real univ) :
    ‖⨍ x, u x ∂ν‖ ≤ ‖⨍ x, u x ∂μ‖ +
      Real.sqrt (μ.real univ / ν.real univ) *
        Real.sqrt (⨍ x, ‖u x - ⨍ y, u y ∂μ‖ ^ 2 ∂μ) := by
  have hν0 : ν ≠ 0 := by
    intro hz
    simp [hz] at hν
  letI : NeZero ν := ⟨hν0⟩
  have hc : MemLp (fun x => u x - ⨍ y, u y ∂μ) 2 μ :=
    hu.sub (memLp_const _)
  have hb := (holder_transpose_norm_average_le ν (hc.mono_measure hνμ) hν).trans
    (holder_transpose_nested_mean_square μ ν hνμ hc hμ hν)
  rw [average_fun_sub ((hu.mono_measure hνμ).integrable (by norm_num))
    (integrable_const _), average_const] at hb
  calc
    ‖⨍ x, u x ∂ν‖ ≤ ‖⨍ x, u x ∂μ‖ +
        ‖(⨍ x, u x ∂ν) - ⨍ x, u x ∂μ‖ := by
      simpa only [add_sub_cancel] using
        norm_add_le (⨍ x, u x ∂μ) ((⨍ x, u x ∂ν) - ⨍ x, u x ∂μ)
    _ ≤ _ := add_le_add (le_refl _) hb

/-- A backward parabolic cylinder has homogeneous volume of degree `d + 2`. -/
theorem holder_transpose_cylinder_volume {d : ℕ} (τ : ℝ) (x : Vec d)
    {r : ℝ} (hr : 0 < r) :
    (volume (Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r)).toReal =
      (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * r ^ (d + 2) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul,
    Real.volume_Ioo, PDE.volume_euclideanBall_toReal_eq_unit_mul_of_pos x hr,
    ENNReal.toReal_ofReal (by nlinarith [sq_nonneg r])]
  rw [pow_add]
  ring

/-- The volume ratio of two concentric backward cylinders is independent
of their center and outer radius. -/
theorem holder_transpose_cylinder_volume_scale {d : ℕ} (τ : ℝ) (x : Vec d)
    {r θ : ℝ} (hr : 0 < r) (hθ : 0 < θ) :
    (volume (Ioo (τ - (θ * r) ^ 2) τ ×ˢ PDE.euclideanBall x (θ * r))).toReal =
      θ ^ (d + 2) *
        (volume (Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r)).toReal := by
  rw [holder_transpose_cylinder_volume τ x (mul_pos hθ hr),
    holder_transpose_cylinder_volume τ x hr, mul_pow]
  ring

/-- The mean square is controlled by the oscillation and the magnitude of the mean. -/
theorem holder_transpose_mean_square_le_oscillation
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {u : X → ℂ} (hu : MemLp u 2 μ) (hμ : 0 < μ.real univ) :
    Real.sqrt (⨍ x, ‖u x‖ ^ 2 ∂μ) ≤
      Real.sqrt (⨍ x, ‖u x - ⨍ y, u y ∂μ‖ ^ 2 ∂μ) + ‖⨍ x, u x ∂μ‖ := by
  let m : ℂ := ⨍ x, u x ∂μ
  have hc : MemLp (fun x => u x - m) 2 μ := hu.sub (memLp_const _)
  have hconst : MemLp (fun _ : X => ‖m‖) 2 μ := memLp_const _
  have hs : MemLp (fun x => ‖u x - m‖ + ‖m‖) 2 μ := hc.norm.add hconst
  have hi : (∫ x, ‖u x‖ ^ 2 ∂μ) ≤ ∫ x, (‖u x - m‖ + ‖m‖) ^ 2 ∂μ := by
    apply integral_mono ((memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).mp hu)
      hs.integrable_sq
    intro x
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
    simpa only [sub_add_cancel] using norm_add_le (u x - m) m
  have hb := (Real.sqrt_le_sqrt hi).trans
    (ParabolicBridge.sqrt_integral_sq_add_le μ hc.norm hconst)
  have hrewrite (f : X → ℝ) : Real.sqrt (⨍ x, f x ∂μ) =
      (Real.sqrt (μ.real univ))⁻¹ * Real.sqrt (∫ x, f x ∂μ) := by
    rw [average_eq, smul_eq_mul, Real.sqrt_mul (inv_nonneg.mpr hμ.le), Real.sqrt_inv]
  rw [hrewrite, hrewrite]
  refine (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
    (le_of_eq ?_)
  simp only [integral_const, smul_eq_mul]
  rw [Real.sqrt_mul hμ.le, Real.sqrt_sq (norm_nonneg m)]
  have hp : Real.sqrt (μ.real univ) ≠ 0 := (Real.sqrt_pos.mpr hμ).ne'
  dsimp only [m]
  field_simp
  <;> ring

private theorem holder_transpose_forcing_factorization
    {L k r z E : ℝ} (hL : 0 < L) (hk : 0 ≤ k) (hr : 0 < r)
    (hz : 0 ≤ z) (hE : 0 ≤ E) :
    Real.sqrt (r ^ 2 * (k * (L * z) ^ 2 * E) / (L⁻¹ / 10) ^ 2) =
      10 * Real.sqrt k * L ^ 2 * z * r * Real.sqrt E := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
  simp only [mul_pow, Real.sq_sqrt hk, Real.sq_sqrt hE]
  field_simp

/-- Normalization of the actual transpose flux error by its own cylinder.
No larger-cylinder gradient estimate is needed for the conservative flux. -/
theorem holder_transpose_normalized_forcing
    {d : ℕ} (x : Vec d) (τ : ℝ) {r θ L z C q : ℝ}
    (hr : 0 < r) (hθ : 0 < θ) (hL : 0 < L) (hz : 0 ≤ z)
    (u : ℝ × Vec d → ℂ) :
    let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ
    2 * (Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) +
      C * q * Real.sqrt ((volume.real (cyl r))⁻¹)) *
      Real.sqrt (r ^ 2 * ((d : ℝ) * (L * z) ^ 2 *
        (∫ w in cyl r, ‖u w‖ ^ 2)) / (L⁻¹ / 10) ^ 2) =
    (20 * Real.sqrt (d : ℝ) * L ^ 2) * z * r *
      (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * q) *
        Real.sqrt (⨍ w in cyl r, ‖u w‖ ^ 2) := by
  intro cyl
  let E := ∫ w in cyl r, ‖u w‖ ^ 2
  have hE : 0 ≤ E := integral_nonneg fun _ => sq_nonneg _
  rw [holder_transpose_forcing_factorization hL (Nat.cast_nonneg d) hr hz hE]
  have hvr : 0 < volume.real (cyl r) := by
    rw [show volume.real (cyl r) =
      (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * r ^ (d + 2) from
        holder_transpose_cylinder_volume τ x hr]
    exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos hr _)
  have hvθ : volume.real (cyl (θ * r)) = θ ^ (d + 2) * volume.real (cyl r) :=
    holder_transpose_cylinder_volume_scale τ x hr hθ
  have hinv : Real.sqrt ((volume.real (cyl (θ * r)))⁻¹) =
      Real.sqrt ((θ ^ (d + 2))⁻¹) * Real.sqrt ((volume.real (cyl r))⁻¹) := by
    rw [hvθ, mul_inv, Real.sqrt_mul (by positivity)]
  have he : E = volume.real (cyl r) * (⨍ w in cyl r, ‖u w‖ ^ 2) := by
    rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    dsimp only [E]
    field_simp
  have hscale : Real.sqrt ((volume.real (cyl r))⁻¹) * Real.sqrt E =
      Real.sqrt (⨍ w in cyl r, ‖u w‖ ^ 2) := by
    rw [he, Real.sqrt_mul hvr.le, Real.sqrt_inv]
    have hp := (Real.sqrt_pos.mpr hvr).ne'
    field_simp
  rw [hinv]
  calc
    _ = (20 * Real.sqrt (d : ℝ) * L ^ 2) * z * r *
        (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * q) *
          (Real.sqrt ((volume.real (cyl r))⁻¹) * Real.sqrt E) := by ring
    _ = _ := by rw [hscale]

/-- The actual transpose orbit satisfies a normalized two-radius estimate.
All constants precede the environment law and the force. -/
theorem holder_transpose_normalized_comparison
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C N : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ (τ : ℝ) (x : Vec d) (r : ℝ), 0 < r → 0 < τ - r ^ 2 →
      ∀ᵐ ω ∂reducedLaw Q,
        let u := fun z : ℝ × Vec d => U (z.1, translate z.2 ω)
        let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ
        MemLp u 2 (volume.restrict (cyl r)) ∧
        ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
          Real.sqrt (⨍ z in cyl (θ * r),
            ‖u z - (⨍ w in cyl (θ * r), u w)‖ ^ 2) ≤
          N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α) *
            Real.sqrt (⨍ z in cyl r, ‖u z‖ ^ 2) +
          2 * C * θ ^ α * Real.sqrt (⨍ z in cyl r,
            ‖u z - (⨍ w in cyl r, u w)‖ ^ 2) := by
  obtain ⟨α, C, hα, hα1, hC, hc⟩ :=
    holder_transpose_orbit_oscillation_of_representative hinterior d hd D
  let L := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (zero_lt_one.trans_le D.one_le_ellipticity)
  refine ⟨α, C, 20 * Real.sqrt (d : ℝ) * L ^ 2, hα, hα1, hC, ?_, ?_⟩
  · have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    positivity
  intro Q hQ i ζ P T hP hT f U hU heU τ x r hr htime
  filter_upwards [hc Q hQ i ζ P T hP hT f U hU heU τ x r hr htime] with ω hω
  dsimp only at hω ⊢
  refine ⟨hω.1, ?_⟩
  intro θ hθ hθhalf
  have he : (∫ z in PDE.euclideanBall x r ×ˢ Ioo (τ - r ^ 2) τ,
      ‖U (z.2, translate z.1 ω)‖ ^ 2) =
      ∫ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
        ‖U (z.1, translate z.2 ω)‖ ^ 2 := by
    simpa only [Measure.volume_eq_prod, Prod.swap] using
      (setIntegral_prod_swap (Ioo (τ - r ^ 2) τ) (PDE.euclideanBall x r)
        (fun z : ℝ × Vec d => ‖U (z.1, translate z.2 ω)‖ ^ 2))
  have hn := holder_transpose_normalized_forcing x τ hr hθ hL (norm_nonneg ζ)
    (C := C) (q := θ ^ α) (fun z => U (z.1, translate z.2 ω))
  have hb := hω.2 θ hθ hθhalf
  rw [he] at hb
  simpa only [L, ← hn, Prod.swap] using hb

/-- Uniform time-window moments control actual physical-cylinder RMS. -/
theorem holder_transpose_window_rms_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p M a b : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (hwindow : ∀ s ∈ Icc a b,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal M)
    (S : Set (ℝ × EinsteinRelation.Vec d)) (hS : MeasurableSet S)
    (hS0 : volume S ≠ 0) (hSfin : volume S ≠ ⊤)
    (hSt : ∀ z ∈ S, z.1 ∈ Icc a b) :
    MemLp (fun ω => Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
  letI := reducedLaw_probability Q
  let F : FieldPair d × (ℝ × EinsteinRelation.Vec d) → ℝ :=
    fun z => ‖U (z.2.1, translate z.2.2 z.1)‖
  have hF : Measurable F :=
    (hU.comp (measurable_snd.fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.snd.prodMk measurable_fst)))).norm
  apply Correctors.scalarL2_setAverage_moment_le
    (reducedLaw Q) volume hS hS0 hSfin hp hM F hF
  intro z hz
  obtain ⟨hu, hb⟩ := hwindow z.1 (hSt z hz)
  have htr := measurePreserving_translate
    (reducedLaw Q) (reducedLaw_stationary Q) z.2
  refine ⟨hu.norm.comp_measurePreserving htr, ?_⟩
  have hn := eLpNorm_comp_measurePreserving (p := ENNReal.ofReal p)
    hu.norm.aestronglyMeasurable htr
  rw [eLpNorm_norm _ hu.aestronglyMeasurable] at hn
  exact hn.trans_le hb


/-- Actual physical oscillations are measurable in the environment. -/
theorem holder_transpose_measurable_oscillation
    {d : ℕ} (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (S : Set (ℝ × EinsteinRelation.Vec d)) :
    Measurable (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2)) := by
  let F : FieldPair d × (ℝ × EinsteinRelation.Vec d) → ℂ :=
    fun z => U (z.2.1, translate z.2.2 z.1)
  have hF : Measurable F :=
    hU.comp (measurable_snd.fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.snd.prodMk measurable_fst)))
  have hm : Measurable (fun ω => ⨍ z in S, F (ω, z)) := by
    simp only [average_eq]
    exact (hF.stronglyMeasurable.integral_prod_right').measurable.const_smul _
  have hG : Measurable (fun z : FieldPair d × (ℝ × EinsteinRelation.Vec d) =>
      ‖F z - (⨍ w in S, F (z.1, w))‖ ^ 2) :=
    (hF.sub (hm.comp measurable_fst)).norm.pow_const 2
  have hi := hG.stronglyMeasurable.integral_prod_right' (ν := volume.restrict S)
  simpa only [average_eq, F, Function.comp_def, Pi.smul_apply] using
    Real.continuous_sqrt.measurable.comp (hi.measurable.const_smul
      ((volume.restrict S).real univ)⁻¹)


/-- Actual physical oscillations inherit the uniform window moment bound. -/
theorem holder_transpose_window_oscillation_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p M a b : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (hwindow : ∀ s ∈ Icc a b,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal M)
    (S : Set (ℝ × EinsteinRelation.Vec d)) (hS : MeasurableSet S)
    (hS0 : volume S ≠ 0) (hSfin : volume S ≠ ⊤)
    (hSt : ∀ z ∈ S, z.1 ∈ Icc a b)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z => U (z.1, translate z.2 ω)) 2 (volume.restrict S)) :
    MemLp (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => Real.sqrt (⨍ z in S,
      ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSfin.lt_top⟩
  obtain ⟨hrms, hnrms⟩ := holder_transpose_window_rms_bound Q hp hM U hU
    hwindow S hS hS0 hSfin hSt
  have hosc := holder_transpose_measurable_oscillation U hU S
  have hle : ∀ᵐ ω ∂reducedLaw Q,
      ‖Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω) -
        (⨍ w in S, U (w.1, translate w.2 ω))‖ ^ 2)‖ ≤
      ‖Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2)‖ := by
    filter_upwards [hlocal] with ω hω
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    apply Real.sqrt_le_sqrt
    simpa only [sub_zero] using holder_complex_mean_minimizes hω 0
  exact ⟨hrms.of_le hosc.aestronglyMeasurable hle,
    (eLpNorm_mono_ae hosc.aestronglyMeasurable hle).trans hnrms⟩


/-- Environment moments turn the actual transpose comparison into a scalar
inhomogeneous recurrence. Uniform window bounds replace the physical means. -/
theorem holder_transpose_lp_recurrence
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α C N : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ C ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (x : Vec d) (r : ℝ), 0 < r → 0 < τ - r ^ 2 → a ≤ τ - r ^ 2 →
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      let osc := fun ρ ω => Real.sqrt
        (⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ,
          ‖U (z.1, translate z.2 ω) -
            (⨍ w in Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ,
              U (w.1, translate w.2 ω))‖ ^ 2)
      MemLp (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      MemLp (osc r) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        2 * C * θ ^ α * (eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q)).toReal +
          N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α) * M := by
  obtain ⟨α, C, N, hα, hα1, hC, hN, hc⟩ :=
    holder_transpose_normalized_comparison hinterior d hd D
  refine ⟨α, C, N, hα, hα1, hC, hN, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow x r hr htime ha θ hθ hθhalf osc
  letI := reducedLaw_probability Q
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ
  let rms := fun ω => Real.sqrt (⨍ z in cyl r, ‖U (z.1, translate z.2 ω)‖ ^ 2)
  have hcomp := hc Q hQ i ζ P T hP hT f U hU heU τ x r hr htime
  have hfin (ρ : ℝ) (hρ : 0 ≤ ρ) : volume (cyl ρ) ≠ ⊤ :=
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall x ρ))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x hρ)).measure_lt_top)).ne
  have hzero (ρ : ℝ) (hρ : 0 < ρ) : volume (cyl ρ) ≠ 0 := by
    have hpos : 0 < volume.real (cyl ρ) := by
      rw [show volume.real (cyl ρ) =
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * ρ ^ (d + 2) from
          holder_transpose_cylinder_volume τ x hρ]
      exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos hρ _)
    intro hz
    simpa only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
  have hmeas (ρ : ℝ) : MeasurableSet (cyl ρ) :=
    measurableSet_Ioo.prod (PDE.isOpen_euclideanBall x ρ).measurableSet
  have hsub (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) : cyl ρ ⊆ cyl r := by
    have hs := (sq_le_sq₀ hρ.le hr.le).mpr hρr
    exact Set.prod_mono (fun s hs' => ⟨by linarith [hs'.1], hs'.2⟩)
      (PDE.euclideanBall_mono hρ.le hρr)
  have hSt : ∀ z ∈ cyl r, z.1 ∈ Icc a τ :=
    fun z hz => ⟨ha.trans hz.1.1.le, hz.1.2.le⟩
  obtain ⟨hrms, hnrms⟩ := holder_transpose_window_rms_bound Q hp hM U hU hwindow
    (cyl r) (hmeas r) (hzero r hr) (hfin r hr.le) hSt
  have hosc (ρ : ℝ) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
      MemLp (osc ρ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (osc ρ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    have hlocal : ∀ᵐ ω ∂reducedLaw Q,
        MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
          (volume.restrict (cyl ρ)) := by
      filter_upwards [hcomp] with ω hω
      exact hω.1.mono_measure (Measure.restrict_mono (hsub ρ hρ hρr) le_rfl)
    exact holder_transpose_window_oscillation_bound Q hp hM U hU hwindow
      (cyl ρ) (hmeas ρ) (hzero ρ hρ) (hfin ρ hρ.le)
      (fun z hz => hSt z (hsub ρ hρ hρr hz)) hlocal
  have hθr : θ * r ≤ r := by nlinarith
  obtain ⟨hsmall, _⟩ := hosc (θ * r) (mul_pos hθ hr) hθr
  obtain ⟨hlarge, _⟩ := hosc r hr le_rfl
  refine ⟨hsmall, hlarge, ?_⟩
  let a := 2 * C * θ ^ α
  let b := N * ‖ζ‖ * r * (Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ α)
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hpoint : ∀ᵐ ω ∂reducedLaw Q, ‖osc (θ * r) ω‖ ≤
      ‖(a • osc r + b • rms) ω‖ := by
    filter_upwards [hcomp] with ω hω
    have he := hω.2 θ hθ hθhalf
    have hnlarge : 0 ≤ osc r ω := Real.sqrt_nonneg _
    have hnrms' : 0 ≤ rms ω := Real.sqrt_nonneg _
    change ‖osc (θ * r) ω‖ ≤ ‖a * osc r ω + b * rms ω‖
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (by positivity : 0 ≤ a * osc r ω + b * rms ω)]
    change osc (θ * r) ω ≤ b * rms ω + a * osc r ω at he
    exact he.trans_eq (add_comm _ _)
  have hnorm : eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal a * eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q) +
        ENNReal.ofReal b * ENNReal.ofReal M := by
    calc
      _ ≤ eLpNorm (a • osc r + b • rms) (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_mono_ae hsmall.aestronglyMeasurable hpoint
      _ ≤ eLpNorm (a • osc r) (ENNReal.ofReal p) (reducedLaw Q) +
          eLpNorm (b • rms) (ENNReal.ofReal p) (reducedLaw Q) :=
        eLpNorm_add_le (ENNReal.one_le_ofReal.mpr (by linarith))
      _ = ENNReal.ofReal a * eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q) +
          ENNReal.ofReal b * eLpNorm rms (ENNReal.ofReal p) (reducedLaw Q) := by
        simp only [eLpNorm_const_smul, Real.enorm_eq_ofReal ha, Real.enorm_eq_ofReal hb]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hnrms (by positivity))
  have hbound : eLpNorm (osc (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (a * (eLpNorm (osc r) (ENNReal.ofReal p) (reducedLaw Q)).toReal + b * M) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul ha,
      ENNReal.ofReal_mul hb, ENNReal.ofReal_toReal hlarge.eLpNorm_ne_top]
    exact hnorm
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

private theorem holder_transpose_inhomogeneous_iteration
    (E : ℕ → ℝ) (a q κ B : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hqκ : q ≤ κ) (haκ : a < κ) (hB : 0 ≤ B) (hE : 0 ≤ E 0)
    (hstep : ∀ n, E (n + 1) ≤ a * E n + B * q ^ n) :
    ∀ n, E n ≤ κ ^ n * (E 0 + B / (κ - a)) := by
  have hden : 0 < κ - a := sub_pos.mpr haκ
  have hcancel : (κ - a) * (B / (κ - a)) = B :=
    mul_div_cancel₀ B hden.ne'
  intro n
  induction n with
  | zero =>
    simpa only [pow_zero, one_mul] using
      (le_add_of_nonneg_right (div_nonneg hB hden.le) : E 0 ≤ E 0 + B / (κ - a))
  | succ n ih =>
    have hpow : q ^ n ≤ κ ^ n := pow_le_pow_left₀ hq hqκ n
    calc
      E (n + 1) ≤ a * E n + B * q ^ n := hstep n
      _ ≤ a * (κ ^ n * (E 0 + B / (κ - a))) + B * κ ^ n :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha)
          (mul_le_mul_of_nonneg_left hpow hB)
      _ ≤ κ ^ (n + 1) * (E 0 + B / (κ - a)) := by
        rw [pow_succ]
        have hbase : a * (E 0 + B / (κ - a)) + B ≤
            κ * (E 0 + B / (κ - a)) := by
          nlinarith only [hcancel, mul_nonneg hden.le hE]
        nlinarith only [mul_le_mul_of_nonneg_left hbase
          (pow_nonneg (hq.trans hqκ) n)]


/-- Actual transpose oscillations decay geometrically in environment Lp.
The exponent, scale, and prefactor depend only on structural data; the time
window supplies the initial and forcing moments without a small-force premise. -/
theorem holder_transpose_lp_geometric_decay
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (x : Vec d) (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
    ∀ n : ℕ,
      let r := θ ^ n * R
      let osc := fun ω => Real.sqrt
        (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
          ‖U (z.1, translate z.2 ω) -
            (⨍ w in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
              U (w.1, translate w.2 ω))‖ ^ 2)
      MemLp osc (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm osc (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨β, C, N, hβ, hβ1, hC, hN, hrec⟩ :=
    holder_transpose_lp_recurrence hinterior d hd D
  obtain ⟨θ, hθ, hθhalf, hθκ, haκ, hκ1⟩ :=
    holder_transpose_augmented_scales C β hC hβ hβ1
  let κ := θ ^ (β / 2)
  let A := 2 * C * θ ^ β
  let S := Real.sqrt ((θ ^ (d + 2))⁻¹) + C * θ ^ β
  let K := 1 + N * S / (κ - A)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hden : 0 < κ - A := sub_pos.mpr haκ
  have hK : 1 ≤ K :=
    le_add_of_nonneg_right (div_nonneg (mul_nonneg hN.le hS) hden.le)
  refine ⟨β / 2, θ, K, by linarith, by linarith, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow x R hR htime ha
  let cyl := fun r : ℝ => Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r
  let osc := fun r ω => Real.sqrt (⨍ z in cyl r,
    ‖U (z.1, translate z.2 ω) - (⨍ w in cyl r, U (w.1, translate w.2 ω))‖ ^ 2)
  let E := fun n : ℕ => (eLpNorm (osc (θ ^ n * R))
    (ENNReal.ofReal p) (reducedLaw Q)).toReal
  have hrpos (n : ℕ) : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hrle (n : ℕ) : θ ^ n * R ≤ R :=
    mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le (by linarith))
  have hrad (n : ℕ) : (θ ^ n * R) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (hrpos n).le hR.le).mpr (hrle n)
  have hrecn (n : ℕ) := hrec Q hQ i ζ P T hP hT f U hU heU
    τ a p M hp hM hwindow x (θ ^ n * R) (hrpos n)
    (by linarith [hrad n]) (by linarith [hrad n]) θ hθ hθhalf
  have hmem (n : ℕ) : MemLp (osc (θ ^ n * R))
      (ENNReal.ofReal p) (reducedLaw Q) := (hrecn n).2.1
  have hbase : E 0 ≤ M := by
    have hcomp := holder_transpose_normalized_comparison hinterior d hd D
    obtain ⟨β', C', N', _, _, _, _, hc⟩ := hcomp
    have hlocal := (hc Q hQ i ζ P T hP hT f U hU heU τ x R hR htime).mono
      (fun _ hω => hω.1)
    have hfin : volume (cyl R) ≠ ⊤ :=
      ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
        (PDE.euclideanBall_subset_euclideanClosedBall x R))).trans_lt
        ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x hR.le)).measure_lt_top)).ne
    have hzero : volume (cyl R) ≠ 0 := by
      have hpos : 0 < volume.real (cyl R) := by
        rw [show volume.real (cyl R) =
          (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * R ^ (d + 2) from
            holder_transpose_cylinder_volume τ x hR]
        exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos hR _)
      intro hz
      simpa only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
    have hbound := (holder_transpose_window_oscillation_bound Q hp hM U hU hwindow
      (cyl R) (measurableSet_Ioo.prod (PDE.isOpen_euclideanBall x R).measurableSet)
      hzero hfin (fun z hz => ⟨ha.trans hz.1.1.le, hz.1.2.le⟩) hlocal).2
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simpa only [E, pow_zero, one_mul, ENNReal.toReal_ofReal hM] using ht
  let B := N * ‖ζ‖ * R * S * M
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep (n : ℕ) : E (n + 1) ≤ A * E n + B * θ ^ n := by
    have he := (hrecn n).2.2
    have hradius : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
    change (eLpNorm (osc (θ * (θ ^ n * R))) _ _).toReal ≤ _ at he
    rw [hradius] at he
    convert he using 1 <;> dsimp only [E, A, B, S] <;> ring
  have hdecay := holder_transpose_inhomogeneous_iteration E A θ κ B hA hθ.le
    hθκ.le haκ hB ENNReal.toReal_nonneg hstep
  intro n
  refine ⟨hmem n, (hdecay n).trans ?_⟩
  have hcoeff : E 0 + B / (κ - A) ≤ K * (1 + ‖ζ‖ * R) * M := by
    have heq : B / (κ - A) = (N * S / (κ - A)) * (‖ζ‖ * R) * M := by
      dsimp only [B]; ring
    rw [heq]
    dsimp only [K]
    have hnonneg : 0 ≤ (N * S / (κ - A)) * M := by positivity
    nlinarith only [hbase, hnonneg, mul_nonneg (norm_nonneg ζ) hR.le,
      mul_nonneg (mul_nonneg (norm_nonneg ζ) hR.le) hM]
  calc
    κ ^ n * (E 0 + B / (κ - A)) ≤ κ ^ n * (K * (1 + ‖ζ‖ * R) * M) :=
      mul_le_mul_of_nonneg_left hcoeff (pow_nonneg (hθ.le.trans hθκ.le) n)
    _ = K * (θ ^ (β / 2)) ^ n * (1 + ‖ζ‖ * R) * M := by ring

/-- A difference of nested means is controlled directly by the outer
oscillation, with the exact square-root volume ratio. -/
theorem holder_transpose_nested_mean_difference
    {X : Type*} [MeasurableSpace X] (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hνμ : ν ≤ μ)
    {u : X → ℂ} (hu : MemLp u 2 μ)
    (hμ : 0 < μ.real univ) (hν : 0 < ν.real univ) :
    ‖(⨍ x, u x ∂ν) - ⨍ x, u x ∂μ‖ ≤
      Real.sqrt (μ.real univ / ν.real univ) *
        Real.sqrt (⨍ x, ‖u x - ⨍ y, u y ∂μ‖ ^ 2 ∂μ) := by
  have hν0 : ν ≠ 0 := by
    intro hz
    simp [hz] at hν
  letI : NeZero ν := ⟨hν0⟩
  have hc : MemLp (fun x => u x - ⨍ y, u y ∂μ) 2 μ :=
    hu.sub (memLp_const _)
  have hb := (holder_transpose_norm_average_le ν (hc.mono_measure hνμ) hν).trans
    (holder_transpose_nested_mean_square μ ν hνμ hc hμ hν)
  rwa [average_fun_sub ((hu.mono_measure hνμ).integrable (by norm_num))
    (integrable_const _), average_const] at hb


/-- Consecutive physical cylinder means inherit the environment Lp
oscillation bound with the exact parabolic volume factor. -/
theorem holder_transpose_cylinder_mean_step
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p τ r θ : ℝ} (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (x : Vec d) (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
        (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r)))
    (hosc : MemLp (fun ω => Real.sqrt
      (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
        ‖U (z.1, translate z.2 ω) -
          (⨍ w in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
            U (w.1, translate w.2 ω))‖ ^ 2)) (ENNReal.ofReal p) (reducedLaw Q)) :
    let mean := fun ρ ω =>
      ⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ, U (z.1, translate z.2 ω)
    MemLp (mean (θ * r) - mean r) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (mean (θ * r) - mean r) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.sqrt ((θ ^ (d + 2))⁻¹) *
        (eLpNorm (fun ω => Real.sqrt
          (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
            ‖U (z.1, translate z.2 ω) - mean r ω‖ ^ 2))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro mean
  let cyl := fun ρ : ℝ => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall x ρ
  let osc := fun ω => Real.sqrt
    (⨍ z in cyl r, ‖U (z.1, translate z.2 ω) - mean r ω‖ ^ 2)
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹)
  have hfin (ρ : ℝ) (hρ : 0 ≤ ρ) : volume (cyl ρ) ≠ ⊤ :=
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall x ρ))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x hρ)).measure_lt_top)).ne
  have hpos (ρ : ℝ) (hρ : 0 < ρ) : 0 < volume.real (cyl ρ) := by
    rw [show volume.real (cyl ρ) =
      (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * ρ ^ (d + 2) from
        holder_transpose_cylinder_volume τ x hρ]
    exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos hρ _)
  haveI : IsFiniteMeasure (volume.restrict (cyl r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hfin r hr.le).lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict (cyl (θ * r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hfin (θ * r) (mul_pos hθ hr).le).lt_top⟩
  have hsub : cyl (θ * r) ⊆ cyl r := by
    have hle : θ * r ≤ r := mul_le_of_le_one_left hr.le hθ1
    have hs := (sq_le_sq₀ (mul_pos hθ hr).le hr.le).mpr hle
    exact Set.prod_mono (fun s hs' => ⟨by linarith [hs'.1], hs'.2⟩)
      (PDE.euclideanBall_mono (mul_pos hθ hr).le hle)
  have hratio : (volume.restrict (cyl r)).real univ /
      (volume.restrict (cyl (θ * r))).real univ = (θ ^ (d + 2))⁻¹ := by
    have hs : volume.real (cyl (θ * r)) = θ ^ (d + 2) * volume.real (cyl r) :=
      holder_transpose_cylinder_volume_scale τ x hr hθ
    rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ, hs]
    have hv : volume.real (cyl r) ≠ 0 := (hpos r hr).ne'
    change volume.real (cyl r) / (θ ^ (d + 2) * volume.real (cyl r)) = _
    field_simp
  have hmean (ρ : ℝ) : Measurable (mean ρ) := by
    let F : FieldPair d × (ℝ × Vec d) → ℂ :=
      fun z => U (z.2.1, translate z.2.2 z.1)
    have hF : Measurable F :=
      hU.comp (measurable_snd.fst.prodMk
        (Probability.continuous_translate.measurable.comp
          (measurable_snd.snd.prodMk measurable_fst)))
    change Measurable (fun ω => ⨍ z in cyl ρ, F (ω, z))
    simp only [average_eq]
    exact (hF.stronglyMeasurable.integral_prod_right').measurable.const_smul _
  have hpoint : ∀ᵐ ω ∂reducedLaw Q,
      ‖(mean (θ * r) - mean r) ω‖ ≤ ‖(J • osc) ω‖ := by
    filter_upwards [hlocal] with ω hω
    have hb := holder_transpose_nested_mean_difference
      (volume.restrict (cyl r)) (volume.restrict (cyl (θ * r)))
      (Measure.restrict_mono hsub le_rfl) hω
      (by simpa only [measureReal_restrict_apply_univ] using hpos r hr)
      (by simpa only [measureReal_restrict_apply_univ] using hpos (θ * r) (mul_pos hθ hr))
    rw [hratio] at hb
    change ‖mean (θ * r) ω - mean r ω‖ ≤ |J * osc ω|
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact hb
  have hmeas := (hmean (θ * r)).sub (hmean r)
  have hsmul := hosc.const_smul J
  have hmem := hsmul.of_le hmeas.aestronglyMeasurable hpoint
  refine ⟨hmem, ?_⟩
  have hn := eLpNorm_mono_ae (p := ENNReal.ofReal p) hmeas.aestronglyMeasurable hpoint
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)] at hn
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hosc.eLpNorm_ne_top) hn
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using ht

/-- Physical cylinder means are measurable functions of the environment. -/
theorem holder_transpose_measurable_mean
    {d : ℕ} (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (S : Set (ℝ × EinsteinRelation.Vec d)) :
    Measurable (fun ω => ⨍ z in S, U (z.1, translate z.2 ω)) := by
  let F : FieldPair d × (ℝ × EinsteinRelation.Vec d) → ℂ :=
    fun z => U (z.2.1, translate z.2.2 z.1)
  have hF : Measurable F :=
    hU.comp (measurable_snd.fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.snd.prodMk measurable_fst)))
  change Measurable (fun ω => ⨍ z in S, F (ω, z))
  simp only [average_eq]
  exact (hF.stronglyMeasurable.integral_prod_right').measurable.const_smul _


/-- A physical cylinder mean inherits the uniform environment moment bound. -/
theorem holder_transpose_window_mean_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p M a b : ℝ} (hp : 2 ≤ p) (hM : 0 ≤ M)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (hwindow : ∀ s ∈ Icc a b,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal M)
    (S : Set (ℝ × EinsteinRelation.Vec d)) (hS : MeasurableSet S)
    (hS0 : volume S ≠ 0) (hSfin : volume S ≠ ⊤)
    (hSt : ∀ z ∈ S, z.1 ∈ Icc a b)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z => U (z.1, translate z.2 ω)) 2 (volume.restrict S)) :
    MemLp (fun ω => ⨍ z in S, U (z.1, translate z.2 ω))
      (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (fun ω => ⨍ z in S, U (z.1, translate z.2 ω))
      (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa using hSfin.lt_top⟩
  obtain ⟨hrms, hnrms⟩ := holder_transpose_window_rms_bound Q hp hM U hU
    hwindow S hS hS0 hSfin hSt
  have hm := holder_transpose_measurable_mean U hU S
  have hpos : 0 < (volume.restrict S).real univ := by
    rw [measureReal_restrict_apply_univ]
    exact ENNReal.toReal_pos hS0 hSfin
  have hle : ∀ᵐ ω ∂reducedLaw Q,
      ‖⨍ z in S, U (z.1, translate z.2 ω)‖ ≤
        ‖Real.sqrt (⨍ z in S, ‖U (z.1, translate z.2 ω)‖ ^ 2)‖ := by
    filter_upwards [hlocal] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact holder_transpose_norm_average_le (volume.restrict S) hω hpos
  exact ⟨hrms.of_le hm.aestronglyMeasurable hle,
    (eLpNorm_mono_ae hm.aestronglyMeasurable hle).trans hnrms⟩


/-- Actual transpose cylinder means have an Lp limit with a quantitative
geometric tail. No fixed-time representative is assumed to be this limit. -/
theorem holder_transpose_lp_cylinder_limit
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (x : Vec d) (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
      let mean := fun n ω =>
        ⨍ z in Ioo (τ - (θ ^ n * R) ^ 2) τ ×ˢ PDE.euclideanBall x (θ ^ n * R),
          U (z.1, translate z.2 ω)
      ∃ (hm : ∀ n : ℕ, MemLp (mean n) (ENNReal.ofReal p) (reducedLaw Q))
        (g : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)),
        Tendsto (fun n => eLpNorm (mean n - (g : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0) ∧
        ∀ n, (eLpNorm (mean n - (g : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K₀, hα, hα1, hθ, hθhalf, hK₀, hdecay⟩ :=
    holder_transpose_lp_geometric_decay hinterior d hd D
  let κ := θ ^ α
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹)
  have hκ : κ < 1 := Real.rpow_lt_one hθ.le (by linarith only [hθhalf]) hα
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg hθ.le α
  let K := 1 + J * K₀ / (1 - κ)
  have hK : 1 ≤ K := le_add_of_nonneg_right (by positivity)
  refine ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow x R hR htime ha mean
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let cyl := fun r : ℝ => Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r
  let osc := fun r ω => Real.sqrt (⨍ z in cyl r,
    ‖U (z.1, translate z.2 ω) - (⨍ w in cyl r, U (w.1, translate w.2 ω))‖ ^ 2)
  obtain ⟨β, C, N, _, _, _, _, hc⟩ :=
    holder_transpose_normalized_comparison hinterior d hd D
  have hlocalR := (hc Q hQ i ζ P T hP hT f U hU heU τ x R hR htime).mono
    (fun _ hω => hω.1)
  have hrpos (n : ℕ) : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hrle (n : ℕ) : θ ^ n * R ≤ R :=
    mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le (by linarith))
  have hrad (n : ℕ) : (θ ^ n * R) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (hrpos n).le hR.le).mpr (hrle n)
  have hsub (n : ℕ) : cyl (θ ^ n * R) ⊆ cyl R :=
    Set.prod_mono (fun s hs => ⟨by linarith [hrad n, hs.1], hs.2⟩)
      (PDE.euclideanBall_mono (hrpos n).le (hrle n))
  have hlocal (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
        (volume.restrict (cyl (θ ^ n * R))) :=
    hlocalR.mono (fun _ hω => hω.mono_measure (Measure.restrict_mono (hsub n) le_rfl))
  have hfin (n : ℕ) : volume (cyl (θ ^ n * R)) ≠ ⊤ :=
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall x (θ ^ n * R)))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x (hrpos n).le)).measure_lt_top)).ne
  have hzero (n : ℕ) : volume (cyl (θ ^ n * R)) ≠ 0 := by
    have hpos : 0 < volume.real (cyl (θ ^ n * R)) := by
      rw [show volume.real (cyl (θ ^ n * R)) =
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * (θ ^ n * R) ^ (d + 2) from
          holder_transpose_cylinder_volume τ x (hrpos n)]
      exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos (hrpos n) _)
    intro hz
    simpa only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
  have hm (n : ℕ) : MemLp (mean n) (ENNReal.ofReal p) (reducedLaw Q) :=
    (holder_transpose_window_mean_bound Q hp hM U hU hwindow (cyl (θ ^ n * R))
      (measurableSet_Ioo.prod (PDE.isOpen_euclideanBall x _).measurableSet)
      (hzero n) (hfin n)
      (fun z hz => ⟨by linarith [hrad n, hz.1.1], hz.1.2.le⟩) (hlocal n)).1
  let F := fun n : ℕ => (hm n).toLp (mean n)
  let B := J * K₀ * (1 + ‖ζ‖ * R) * M
  have hstep (n : ℕ) : dist (F n) (F (n + 1)) ≤ B * κ ^ n := by
    obtain ⟨hosc, hnorm⟩ := hdecay Q hQ i ζ P T hP hT f U hU heU
      τ a p M hp hM hwindow x R hR htime ha n
    have hs := (holder_transpose_cylinder_mean_step Q U hU x (hrpos n) hθ
      (by linarith only [hθhalf]) (hlocal n) hosc).2
    have hradius : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
    change (eLpNorm ((fun ω => ⨍ z in cyl (θ * (θ ^ n * R)), U (z.1, translate z.2 ω)) -
      mean n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ _ at hs
    rw [hradius] at hs
    change (eLpNorm (mean (n + 1) - mean n) _ _).toReal ≤
      J * (eLpNorm (osc (θ ^ n * R)) _ _).toReal at hs
    have hdistance : dist (F n) (F (n + 1)) =
        (eLpNorm (mean (n + 1) - mean n) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      rw [dist_comm, dist_eq_norm]
      change ‖(hm (n + 1)).toLp (mean (n + 1)) - (hm n).toLp (mean n)‖ = _
      rw [← MemLp.toLp_sub, Lp.norm_toLp]
    rw [hdistance]
    calc
      _ ≤ J * (eLpNorm (osc (θ ^ n * R)) _ _).toReal := hs
      _ ≤ J * (K₀ * κ ^ n * (1 + ‖ζ‖ * R) * M) :=
        mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ = B * κ ^ n := by ring
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric κ B hκ hstep)
  have hconv : Tendsto (fun n => eLpNorm (mean n - (g : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0) := by
    have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' F g).mp hg
    apply hh.congr'
    apply Eventually.of_forall
    intro n
    exact eLpNorm_congr_ae ((hm n).coeFn_toLp.sub EventuallyEq.rfl)
  refine ⟨hm, g, hconv, ?_⟩
  intro n
  have htail := dist_le_of_le_geometric_of_tendsto κ B hκ hstep hg n
  have heq : dist (F n) g =
      (eLpNorm (mean n - (g : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    rw [dist_eq_norm, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_ae
    exact (Lp.coeFn_sub _ _).trans ((hm n).coeFn_toLp.sub EventuallyEq.rfl)
  rw [heq] at htail
  refine htail.trans ?_
  have htail_eq : B * κ ^ n / (1 - κ) =
      (J * K₀ / (1 - κ)) * κ ^ n * (1 + ‖ζ‖ * R) * M := by dsimp only [B]; ring
  rw [htail_eq]
  have hcoef : J * K₀ / (1 - κ) ≤ K := le_add_of_nonneg_left zero_le_one
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hκ0 n))
      (by positivity)) hM

/-- A displaced inner cylinder mean is controlled by the common outer
oscillation, with the exact parabolic volume factor. -/
theorem holder_transpose_displaced_cylinder_mean
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p τ r θ : ℝ} (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (x y : Vec d) (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hxy : PDE.euclideanBall y (θ * r) ⊆ PDE.euclideanBall x r)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
        (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r)))
    (hosc : MemLp (fun ω => Real.sqrt
      (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
        ‖U (z.1, translate z.2 ω) -
          (⨍ w in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
            U (w.1, translate w.2 ω))‖ ^ 2)) (ENNReal.ofReal p) (reducedLaw Q)) :
    let mean := fun c ρ ω =>
      ⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall c ρ, U (z.1, translate z.2 ω)
    MemLp (mean y (θ * r) - mean x r) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (mean y (θ * r) - mean x r) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      Real.sqrt ((θ ^ (d + 2))⁻¹) *
        (eLpNorm (fun ω => Real.sqrt
          (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
            ‖U (z.1, translate z.2 ω) - mean x r ω‖ ^ 2))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro mean
  let cyl := fun (c : Vec d) (ρ : ℝ) => Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall c ρ
  let osc := fun ω => Real.sqrt
    (⨍ z in cyl x r, ‖U (z.1, translate z.2 ω) - mean x r ω‖ ^ 2)
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹)
  have hfin (c : Vec d) (ρ : ℝ) (hρ : 0 ≤ ρ) : volume (cyl c ρ) ≠ ⊤ :=
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall c ρ))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall c hρ)).measure_lt_top)).ne
  have hpos (c : Vec d) (ρ : ℝ) (hρ : 0 < ρ) : 0 < volume.real (cyl c ρ) := by
    rw [show volume.real (cyl c ρ) =
      (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * ρ ^ (d + 2) from
        holder_transpose_cylinder_volume τ c hρ]
    exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos hρ _)
  haveI : IsFiniteMeasure (volume.restrict (cyl x r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hfin x r hr.le).lt_top⟩
  haveI : IsFiniteMeasure (volume.restrict (cyl y (θ * r))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using (hfin y (θ * r) (mul_pos hθ hr).le).lt_top⟩
  have hsub : cyl y (θ * r) ⊆ cyl x r := by
    have hle : θ * r ≤ r := mul_le_of_le_one_left hr.le hθ1
    have hs := (sq_le_sq₀ (mul_pos hθ hr).le hr.le).mpr hle
    exact Set.prod_mono (fun s hs' => ⟨by linarith [hs'.1], hs'.2⟩)
      hxy
  have hratio : (volume.restrict (cyl x r)).real univ /
      (volume.restrict (cyl y (θ * r))).real univ = (θ ^ (d + 2))⁻¹ := by
    have hs : volume.real (cyl y (θ * r)) = θ ^ (d + 2) * volume.real (cyl x r) := by
      rw [show volume.real (cyl y (θ * r)) =
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * (θ * r) ^ (d + 2) from
          holder_transpose_cylinder_volume τ y (mul_pos hθ hr),
        show volume.real (cyl x r) =
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * r ^ (d + 2) from
          holder_transpose_cylinder_volume τ x hr, mul_pow]
      ring
    rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ, hs]
    have hv : volume.real (cyl x r) ≠ 0 := (hpos x r hr).ne'
    change volume.real (cyl x r) / (θ ^ (d + 2) * volume.real (cyl x r)) = _
    field_simp
  have hmean (c : Vec d) (ρ : ℝ) : Measurable (mean c ρ) :=
    holder_transpose_measurable_mean U hU (cyl c ρ)
  have hpoint : ∀ᵐ ω ∂reducedLaw Q,
      ‖(mean y (θ * r) - mean x r) ω‖ ≤ ‖(J • osc) ω‖ := by
    filter_upwards [hlocal] with ω hω
    have hb := holder_transpose_nested_mean_difference
      (volume.restrict (cyl x r)) (volume.restrict (cyl y (θ * r)))
      (Measure.restrict_mono hsub le_rfl) hω
      (by simpa only [measureReal_restrict_apply_univ] using hpos x r hr)
      (by simpa only [measureReal_restrict_apply_univ] using hpos y (θ * r) (mul_pos hθ hr))
    rw [hratio] at hb
    change ‖mean y (θ * r) ω - mean x r ω‖ ≤ |J * osc ω|
    rw [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    exact hb
  have hmeas := (hmean y (θ * r)).sub (hmean x r)
  have hsmul := hosc.const_smul J
  have hmem := hsmul.of_le hmeas.aestronglyMeasurable hpoint
  refine ⟨hmem, ?_⟩
  have hn := eLpNorm_mono_ae (p := ENNReal.ofReal p) hmeas.aestronglyMeasurable hpoint
  rw [eLpNorm_const_smul, Real.enorm_eq_ofReal (Real.sqrt_nonneg _)] at hn
  have ht := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hosc.eLpNorm_ne_top) hn
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] using ht

/-- Two inner means with a common outer cylinder have an Lp difference
bounded by twice the outer oscillation and the parabolic volume factor. -/
theorem holder_transpose_overlapping_cylinder_means
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {p τ r θ : ℝ} (hp : 1 ≤ p)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (x y : Vec d) (hr : 0 < r) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hxy : PDE.euclideanBall y (θ * r) ⊆ PDE.euclideanBall x r)
    (hlocal : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
        (volume.restrict (Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r))) :
    let mean := fun c ρ ω =>
      ⨍ z in Ioo (τ - ρ ^ 2) τ ×ˢ PDE.euclideanBall c ρ, U (z.1, translate z.2 ω)
    let osc := fun ω => Real.sqrt
      (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
        ‖U (z.1, translate z.2 ω) - mean x r ω‖ ^ 2)
    MemLp osc (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (mean y (θ * r) - mean x (θ * r)) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (mean y (θ * r) - mean x (θ * r))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      2 * Real.sqrt ((θ ^ (d + 2))⁻¹) *
        (eLpNorm osc (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro mean osc hosc
  obtain ⟨hy, hny⟩ := holder_transpose_displaced_cylinder_mean Q U hU x y
    hr hθ hθ1 hxy hlocal hosc
  obtain ⟨hx, hnx⟩ := holder_transpose_cylinder_mean_step Q U hU x
    hr hθ hθ1 hlocal hosc
  change MemLp (mean y (θ * r) - mean x r) _ _ at hy
  change MemLp (mean x (θ * r) - mean x r) _ _ at hx
  have heq : mean y (θ * r) - mean x (θ * r) =
      (mean y (θ * r) - mean x r) - (mean x (θ * r) - mean x r) := by abel
  rw [heq]
  refine ⟨hy.sub hx, ?_⟩
  have hp' : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hb := eLpNorm_sub_le (f := mean y (θ * r) - mean x r)
    (g := mean x (θ * r) - mean x r) (μ := reducedLaw Q) hp'
  have ht := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hy.eLpNorm_ne_top, hx.eLpNorm_ne_top⟩) hb
  rw [ENNReal.toReal_add hy.eLpNorm_ne_top hx.eLpNorm_ne_top] at ht
  exact ht.trans (by linarith only [hny, hnx])

/-- Actual nearby-center cylinder means satisfy the quantitative spatial
Campanato estimate at each geometric scale. -/
theorem holder_transpose_geometric_overlapping_means
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (x y : Vec d) (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
    ∀ n : ℕ,
      PDE.euclideanBall y (θ ^ (n + 1) * R) ⊆ PDE.euclideanBall x (θ ^ n * R) →
      let mean := fun c =>
        fun ω => ⨍ z in Ioo (τ - (θ ^ (n + 1) * R) ^ 2) τ ×ˢ
          PDE.euclideanBall c (θ ^ (n + 1) * R), U (z.1, translate z.2 ω)
      MemLp (mean y - mean x) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (mean y - mean x) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K₀, hα, hα1, hθ, hθhalf, hK₀, hdecay⟩ :=
    holder_transpose_lp_geometric_decay hinterior d hd D
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹)
  let K := 1 + 2 * J * K₀
  have hK : 1 ≤ K := le_add_of_nonneg_right (by positivity)
  refine ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow x y R hR htime ha n hxy mean
  have hr : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hrle : θ ^ n * R ≤ R :=
    mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le (by linarith))
  have hsquare : (θ ^ n * R) ^ 2 ≤ R ^ 2 := (sq_le_sq₀ hr.le hR.le).mpr hrle
  obtain ⟨hosc, hnorm⟩ := hdecay Q hQ i ζ P T hP hT f U hU heU
    τ a p M hp hM hwindow x R hR htime ha n
  obtain ⟨β, C, N, _, _, _, _, hc⟩ :=
    holder_transpose_normalized_comparison hinterior d hd D
  have hlocal := (hc Q hQ i ζ P T hP hT f U hU heU τ x (θ ^ n * R)
    hr (by linarith)).mono (fun _ hω => hω.1)
  have hrad : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
  have hb := holder_transpose_overlapping_cylinder_means Q (by linarith : 1 ≤ p)
    U hU x y hr hθ (by linarith) (by simpa only [hrad] using hxy) hlocal hosc
  dsimp only at hb
  simp only [hrad] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  change 2 * J * _ ≤ _
  calc
    _ ≤ 2 * J * (K₀ * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = (2 * J * K₀) * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by ring
    _ ≤ K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
      apply mul_le_mul_of_nonneg_right _ hM
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact le_add_of_nonneg_left zero_le_one

/-- The Lp limits of actual transpose physical cylinder means have a
quantitative nearby-center increment bound at every geometric scale. -/
theorem holder_transpose_spatial_cylinder_limits
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
      let mean := fun x n ω =>
        ⨍ z in Ioo (τ - (θ ^ n * R) ^ 2) τ ×ˢ PDE.euclideanBall x (θ ^ n * R),
          U (z.1, translate z.2 ω)
      ∃ g : Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ x, Tendsto (fun n => eLpNorm (mean x n - (g x : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0)) ∧
        ∀ (x y : Vec d) (n : ℕ),
          PDE.euclideanBall y (θ ^ (n + 1) * R) ⊆ PDE.euclideanBall x (θ ^ n * R) →
          (eLpNorm ((g y : FieldPair d → ℂ) - (g x : FieldPair d → ℂ))
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            K * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K₀, hα, hα1, hθ, hθhalf, hK₀, hdecay⟩ :=
    holder_transpose_lp_geometric_decay hinterior d hd D
  let κ := θ ^ α
  let J := Real.sqrt ((θ ^ (d + 2))⁻¹)
  have hκ : κ < 1 := Real.rpow_lt_one hθ.le (by linarith only [hθhalf]) hα
  have hκ0 : 0 ≤ κ := Real.rpow_nonneg hθ.le α
  let K := 1 + 2 * J * K₀ / (1 - κ) + 2 * J * K₀
  have hK : 1 ≤ K := by
    have h₁ : 0 ≤ 2 * J * K₀ / (1 - κ) := by positivity
    have h₂ : 0 ≤ 2 * J * K₀ := by positivity
    dsimp only [K]
    linarith only [h₁, h₂]
  refine ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow R hR htime ha mean
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  let cyl := fun (x : Vec d) (r : ℝ) => Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r
  let osc := fun (x : Vec d) (r : ℝ) (ω : FieldPair d) => Real.sqrt (⨍ z in cyl x r,
    ‖U (z.1, translate z.2 ω) - (⨍ w in cyl x r, U (w.1, translate w.2 ω))‖ ^ 2)
  obtain ⟨β, C, N, _, _, _, _, hc⟩ :=
    holder_transpose_normalized_comparison hinterior d hd D
  have hrpos (n : ℕ) : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hrle (n : ℕ) : θ ^ n * R ≤ R :=
    mul_le_of_le_one_left hR.le (pow_le_one₀ hθ.le (by linarith))
  have hrad (n : ℕ) : (θ ^ n * R) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (hrpos n).le hR.le).mpr (hrle n)
  have hlocal (x : Vec d) (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun z : ℝ × Vec d => U (z.1, translate z.2 ω)) 2
        (volume.restrict (cyl x (θ ^ n * R))) :=
    (hc Q hQ i ζ P T hP hT f U hU heU τ x (θ ^ n * R) (hrpos n)
      (by linarith [hrad n])).mono (fun _ hω => hω.1)
  have hfin (x : Vec d) (n : ℕ) : volume (cyl x (θ ^ n * R)) ≠ ⊤ :=
    ((measure_mono (Set.prod_mono Ioo_subset_Icc_self
      (PDE.euclideanBall_subset_euclideanClosedBall x (θ ^ n * R)))).trans_lt
      ((isCompact_Icc.prod (PDE.isCompact_euclideanClosedBall x (hrpos n).le)).measure_lt_top)).ne
  have hzero (x : Vec d) (n : ℕ) : volume (cyl x (θ ^ n * R)) ≠ 0 := by
    have hpos : 0 < volume.real (cyl x (θ ^ n * R)) := by
      rw [show volume.real (cyl x (θ ^ n * R)) =
        (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal * (θ ^ n * R) ^ (d + 2) from
          holder_transpose_cylinder_volume τ x (hrpos n)]
      exact mul_pos (PDE.volume_euclideanBall_toReal_pos _ (by norm_num)) (pow_pos (hrpos n) _)
    intro hz
    simpa only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] using hpos
  have hm (x : Vec d) (n : ℕ) : MemLp (mean x n) (ENNReal.ofReal p) (reducedLaw Q) :=
    (holder_transpose_window_mean_bound Q hp hM U hU hwindow (cyl x (θ ^ n * R))
      (measurableSet_Ioo.prod (PDE.isOpen_euclideanBall x _).measurableSet)
      (hzero x n) (hfin x n)
      (fun z hz => ⟨by linarith [hrad n, hz.1.1], hz.1.2.le⟩) (hlocal x n)).1
  let F := fun x n => (hm x n).toLp (mean x n)
  let H := (1 + ‖ζ‖ * R) * M
  let B := J * K₀ * H
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hstep (x : Vec d) (n : ℕ) : dist (F x n) (F x (n + 1)) ≤ B * κ ^ n := by
    obtain ⟨hosc, hnorm⟩ := hdecay Q hQ i ζ P T hP hT f U hU heU
      τ a p M hp hM hwindow x R hR htime ha n
    have hs := (holder_transpose_cylinder_mean_step Q U hU x (hrpos n) hθ
      (by linarith only [hθhalf]) (hlocal x n) hosc).2
    have hradius : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
    change (eLpNorm ((fun ω => ⨍ z in cyl x (θ * (θ ^ n * R)), U (z.1, translate z.2 ω)) -
      mean x n) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ _ at hs
    rw [hradius] at hs
    change (eLpNorm (mean x (n + 1) - mean x n) _ _).toReal ≤
      J * (eLpNorm (osc x (θ ^ n * R)) _ _).toReal at hs
    rw [dist_comm, dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
    calc
      _ ≤ J * (eLpNorm (osc x (θ ^ n * R)) _ _).toReal := hs
      _ ≤ J * (K₀ * κ ^ n * (1 + ‖ζ‖ * R) * M) :=
        mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ = B * κ ^ n := by dsimp only [B, H]; ring
  choose g hg using fun x =>
    cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric κ B hκ (hstep x))
  refine ⟨g, ?_, ?_⟩
  · intro x
    have hh := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' (F x) (g x)).mp (hg x)
    apply hh.congr'
    exact Eventually.of_forall (fun n => eLpNorm_congr_ae ((hm x n).coeFn_toLp.sub EventuallyEq.rfl))
  · intro x y n hxy
    have htx := dist_le_of_le_geometric_of_tendsto κ B hκ (hstep x) (hg x) (n + 1)
    have hty := dist_le_of_le_geometric_of_tendsto κ B hκ (hstep y) (hg y) (n + 1)
    obtain ⟨hosc, hnorm⟩ := hdecay Q hQ i ζ P T hP hT f U hU heU
      τ a p M hp hM hwindow x R hR htime ha n
    have hradius : θ * (θ ^ n * R) = θ ^ (n + 1) * R := by rw [pow_succ]; ring
    have hb := (holder_transpose_overlapping_cylinder_means Q (by linarith : 1 ≤ p)
      U hU x y (hrpos n) hθ (by linarith)
      (by simpa only [hradius] using hxy) (hlocal x n) hosc).2
    simp only [hradius] at hb
    have hmid : dist (F y (n + 1)) (F x (n + 1)) ≤ 2 * B * κ ^ n := by
      rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp]
      exact hb.trans ((mul_le_mul_of_nonneg_left hnorm (by positivity)).trans
        (by dsimp only [B, H, κ, J]; ring_nf; exact le_rfl))
    have heq : (eLpNorm ((g y : FieldPair d → ℂ) - (g x : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal = dist (g y) (g x) := by
      rw [dist_eq_norm, Lp.norm_def]
      exact congrArg ENNReal.toReal (eLpNorm_congr_ae (Lp.coeFn_sub _ _)).symm
    rw [heq]
    have htri := dist_triangle4 (g y) (F y (n + 1)) (F x (n + 1)) (g x)
    rw [dist_comm (g y) (F y (n + 1))] at htri
    have hkn : κ ^ (n + 1) ≤ κ ^ n := by
      rw [pow_succ]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hκ.le (pow_nonneg hκ0 n)
    have ht : B * κ ^ (n + 1) / (1 - κ) ≤ B * κ ^ n / (1 - κ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hkn hB) (by linarith)
    have htotal := htri.trans (add_le_add (add_le_add (hty.trans ht) hmid) (htx.trans ht))
    refine htotal.trans ?_
    have hid : B * κ ^ n / (1 - κ) + 2 * B * κ ^ n + B * κ ^ n / (1 - κ) =
        (2 * J * K₀ / (1 - κ) + 2 * J * K₀) * κ ^ n * H := by dsimp only [B]; ring
    rw [hid]
    change _ ≤ K * κ ^ n * (1 + ‖ζ‖ * R) * M
    have hcoef : 2 * J * K₀ / (1 - κ) + 2 * J * K₀ ≤ K := by dsimp only [K]; linarith
    have hb' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoef (pow_nonneg hκ0 n)) hH
    simpa only [H, mul_assoc] using hb'

/-- Geometric scale selection gives a local Euclidean Holder bound for
the actual transpose cylinder limits, with a structural exponent. -/
theorem holder_transpose_holder_cylinder_limits
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α θ K : ℝ, 0 < α ∧ α < 1 ∧ 0 < θ ∧ θ ≤ 1 / 2 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (U : ℝ × FieldPair d → ℂ), Measurable U →
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] T s.toNNReal f) →
    ∀ τ a p M : ℝ, 2 ≤ p → 0 ≤ M →
      (∀ s ∈ Icc a τ,
        MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
      let mean := fun x n ω =>
        ⨍ z in Ioo (τ - (θ ^ n * R) ^ 2) τ ×ˢ PDE.euclideanBall x (θ ^ n * R),
          U (z.1, translate z.2 ω)
      ∃ g : Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q),
        (∀ x, Tendsto (fun n => eLpNorm (mean x n - (g x : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0)) ∧
        ∀ (x y : Vec d), PDE.vecEuclideanNorm (y - x) ≤ R / 2 →
          (eLpNorm ((g y : FieldPair d → ℂ) - (g x : FieldPair d → ℂ))
            (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
            K * (PDE.vecEuclideanNorm (y - x) / R) ^ α * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K₀, hα, hα1, hθ, hθhalf, hK₀, hlimits⟩ :=
    holder_transpose_spatial_cylinder_limits hinterior d hd D
  let K := 1 + K₀ * (2 / θ) ^ α
  have hK : 1 ≤ K := le_add_of_nonneg_right (by positivity)
  refine ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f U hU heU τ a p M hp hM hwindow R hR htime ha mean
  obtain ⟨g, hconv, hinc⟩ := hlimits Q hQ i ζ P T hP hT f U hU heU
    τ a p M hp hM hwindow R hR htime ha
  refine ⟨g, hconv, ?_⟩
  intro x y hxy
  by_cases heq : y = x
  · subst y
    simp only [sub_self, eLpNorm_zero, ENNReal.toReal_zero]
    apply mul_nonneg _ hM
    apply mul_nonneg _ (by positivity)
    exact mul_nonneg (by linarith) (Real.rpow_nonneg
      (div_nonneg (PDE.vecEuclideanNorm_nonneg _) hR.le) _)
  let δ := PDE.vecEuclideanNorm (y - x)
  have hδ0 : δ ≠ 0 := by
    intro hz
    exact heq (sub_eq_zero.mp (PDE.vecEuclideanNorm_eq_zero_iff.mp hz))
  have hδ : 0 < δ := lt_of_le_of_ne (PDE.vecEuclideanNorm_nonneg _) hδ0.symm
  have hzpos : 0 < 2 * δ / R := div_pos (by positivity) hR
  have hz1 : 2 * δ / R ≤ 1 := (div_le_one hR).mpr (by linarith)
  obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one hzpos hz1 hθ (by linarith)
  have hr : 0 < θ ^ n * R := mul_pos (pow_pos hθ _) hR
  have hδr : 2 * δ ≤ θ ^ n * R := (div_le_iff₀ hR).mp hnhi
  have hradius : θ ^ (n + 1) * R = θ * (θ ^ n * R) := by rw [pow_succ]; ring
  have hsub : PDE.euclideanBall y (θ ^ (n + 1) * R) ⊆
      PDE.euclideanBall x (θ ^ n * R) := by
    apply PDE.euclideanBall_subset_of_center_norm_add_le
      (mul_pos (pow_pos hθ _) hR) hr
    rw [hradius]
    have hhalf := mul_le_mul_of_nonneg_right hθhalf hr.le
    change δ + θ * (θ ^ n * R) ≤ θ ^ n * R
    linarith
  have hnsmall : θ ^ n ≤ (2 / θ) * (δ / R) := by
    have hh : θ ^ n ≤ (2 * δ / R) / θ := by
      apply (le_div_iff₀ hθ).mpr
      simpa only [pow_succ] using hnlo.le
    have hid : (2 * δ / R) / θ = (2 / θ) * (δ / R) := by ring
    simpa only [hid] using hh
  have hpow : (θ ^ α) ^ n ≤ (2 / θ) ^ α * (δ / R) ^ α := by
    rw [Real.rpow_pow_comm hθ.le]
    calc
      _ ≤ ((2 / θ) * (δ / R)) ^ α :=
        Real.rpow_le_rpow (pow_nonneg hθ.le n) hnsmall hα.le
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hb := hinc x y n hsub
  have hcoef : K₀ * (2 / θ) ^ α ≤ K := le_add_of_nonneg_left zero_le_one
  calc
    _ ≤ K₀ * (θ ^ α) ^ n * (1 + ‖ζ‖ * R) * M := hb
    _ ≤ K₀ * ((2 / θ) ^ α * (δ / R) ^ α) * (1 + ‖ζ‖ * R) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow (by linarith)) (by positivity)) hM
    _ = (K₀ * (2 / θ) ^ α) * (δ / R) ^ α * (1 + ‖ζ‖ * R) * M := by ring
    _ ≤ K * (δ / R) ^ α * (1 + ‖ζ‖ * R) * M :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) (by positivity)) hM

private theorem holderTranspose_norm_average_sub_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure α) [IsFiniteMeasure μ] [NeZero μ]
    (f : α → E) (z : E) (C : ℝ) (hi : Integrable f μ)
    (hb : ∀ᵐ x ∂μ, ‖f x - z‖ ≤ C) :
    ‖(⨍ x, f x ∂μ) - z‖ ≤ C := by
  have he : (⨍ x, f x ∂μ) - z = ⨍ x, f x - z ∂μ := by
    rw [average_fun_sub hi (integrable_const z), average_const]
  rw [he, average]
  simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
    norm_integral_le_of_norm_le_const
      (hb.filter_mono (Measure.ae_smul_measure_le (μ univ)⁻¹))

private theorem holderTranspose_physical_integrable {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (f : ℝ × Vec d → E) (hf : Continuous f)
    (t r : ℝ) (x : Vec d) :
    Integrable f (volume.restrict (Ioo (t-r^2) t ×ˢ {y | euclideanNorm (y-x) < r})) := by
  apply (hf.continuousOn.integrableOn_compact
    (isCompact_Icc.prod (isCompact_closedBall x r))).mono_set
  rintro ⟨s,y⟩ ⟨hs,hy⟩
  refine ⟨⟨hs.1.le, hs.2.le⟩, ?_⟩
  simpa only [Metric.mem_closedBall, dist_eq_norm] using
    (Calculus.S1.norm_le_euclideanNorm (y-x)).trans hy.le

private theorem holderTranspose_physical_average_tendsto {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ × Vec d → E) (hf : Continuous f) (t : ℝ) (x : Vec d) :
    Tendsto (fun r : ℝ => ⨍ z in Ioo (t-r^2) t ×ˢ {y | euclideanNorm (y-x) < r}, f z)
      (𝓝[>] (0 : ℝ)) (𝓝 (f (t,x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε/2) (by positivity)
  filter_upwards [Ioo_mem_nhdsGT (lt_min zero_lt_one hδ)] with r hr
  let A := Ioo (t-r^2) t
  let B := {y : Vec d | euclideanNorm (y-x) < r}
  have hBm : MeasurableSet B := S3LocalAv.measurableSet_euclideanBall x r
  have hBfin : volume B ≠ ∞ := S3LocalAv.measure_euclideanBall_ne_top x hr.1.le
  have hBpos : volume B ≠ 0 := by
    apply ne_of_gt
    apply (isOpen_lt (S3LocalAv.continuous_euclideanNorm'.comp
      (continuous_id.sub continuous_const)) continuous_const).measure_pos volume
    exact ⟨x, by simpa [B, euclideanNorm, euclideanSq, dot] using hr.1⟩
  have hAfin : volume A ≠ ∞ := by simp [A, Real.volume_Ioo]
  have hApos : volume A ≠ 0 := by
    rw [Real.volume_Ioo]
    exact (ENNReal.ofReal_pos.mpr (by nlinarith [sq_pos_of_pos hr.1])).ne'
  let m := volume.restrict (A ×ˢ B)
  have hmfin : m univ ≠ ∞ := by
    simp only [m, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top hAfin hBfin
  letI : IsFiniteMeasure m := ⟨hmfin.lt_top⟩
  letI : NeZero m := ⟨by
    intro he
    have : m univ = 0 := by rw [he]; rfl
    simpa only [m, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod,
      mul_eq_zero, hApos, hBpos, or_self] using this⟩
  have hbound : ‖(⨍ z, f z ∂m) - f (t,x)‖ ≤ ε/2 := by
    apply holderTranspose_norm_average_sub_le m _ _ _ (holderTranspose_physical_integrable f hf t r x)
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod hBm)] with z hz
    rw [← dist_eq_norm]
    apply (hnear ?_).le
    rw [Prod.dist_eq, Real.dist_eq, dist_eq_norm, max_lt_iff]
    refine ⟨?_, (Calculus.S1.norm_le_euclideanNorm (z.2-x)).trans_lt
      (hz.2.trans (lt_min_iff.mp hr.2).2)⟩
    rw [abs_of_nonpos (sub_nonpos.mpr hz.1.2.le)]
    have hr1 : r < 1 := (lt_min_iff.mp hr.2).1
    have hsq : r^2 ≤ r := by nlinarith [hr.1]
    have hs := hz.1.1
    linarith [(lt_min_iff.mp hr.2).2]
  exact lt_of_le_of_lt (by simpa only [dist_eq_norm] using hbound) (by linarith)

/-- A continuous finite-p lift identifies literal physical cylinder means,
without selecting pointwise values of an Lp equivalence class. -/
theorem holder_transpose_physical_mean_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (p : ℝ) (hp : 2 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    (F : ℝ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) (hF : Continuous F)
    (U : ℝ × FieldPair d → ℂ) (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] F s)
    (τ : ℝ) (x : Vec d) :
    Tendsto (fun r : ℝ => eLpNorm (fun ω =>
      (⨍ z in Ioo (τ - r ^ 2) τ ×ˢ PDE.euclideanBall x r,
        U (z.1, translate z.2 ω)) - (F τ) (translate x ω))
      (ENNReal.ofReal p) (reducedLaw Q)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hp2 : 2 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  let J : ℝ × Vec d → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun u =>
    Lp.compMeasurePreserving (translate u.2)
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2) (F u.1)
  let g : ℝ × Vec d → C(FieldPair d, FieldPair d) := fun u =>
    ⟨translate u.2, Probability.continuous_translate.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact Probability.continuous_translate.comp (continuous_fst.snd.prodMk continuous_snd)
  have hJ : Continuous J :=
    (hF.comp continuous_fst).compMeasurePreservingLp hg
      (fun u => measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2)
      ENNReal.ofReal_ne_top
  let L := (complexLpToL2CLM (reducedLaw Q) hp2).restrictScalars ℝ
  have hrep (u : ℝ × Vec d) :
      (fun ω => U (u.1, translate u.2 ω)) =ᵐ[reducedLaw Q] L (J u) := by
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) u.2
    filter_upwards [hm.quasiMeasurePreserving.ae (heU u.1),
      Lp.coeFn_compMeasurePreserving (F u.1) hm] with ω hu hj
    change U (u.1, translate u.2 ω) = (J u) ω
    exact hu.trans hj.symm
  let H : ℝ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := fun r =>
    ⨍ z in Ioo (τ-r^2) τ ×ˢ {y | euclideanNorm (y-x) < r}, J z
  have hphys (r : ℝ) :
      (fun ω => L (H r) ω) =ᵐ[reducedLaw Q] fun ω =>
        ⨍ z in Ioo (τ-r^2) τ ×ˢ {y | euclideanNorm (y-x) < r},
          U (z.1, translate z.2 ω) := by
    let m := volume.restrict (Ioo (τ-r^2) τ ×ˢ {y | euclideanNorm (y-x) < r})
    have hi : Integrable J m := holderTranspose_physical_integrable J hJ τ r x
    have hm : Measurable (fun z : (ℝ × Vec d) × FieldPair d =>
        U (z.1.1, translate z.1.2 z.2)) :=
      hU.comp (measurable_fst.fst.prodMk
        (Probability.continuous_translate.measurable.comp
          (measurable_fst.snd.prodMk measurable_snd)))
    have hh := coeFn_integral_joint_l2_representative (L.integrable_comp hi) hm hrep
    have hmap : L (H r) = (m.real univ)⁻¹ • ∫ z, L (J z) ∂m := by
      change L (⨍ z, J z ∂m) = _
      rw [average_eq, L.map_smul, L.integral_comp_comm hi]
    filter_upwards [hh, Lp.coeFn_smul ((m.real univ)⁻¹) (∫ z, L (J z) ∂m)] with ω hh hs
    change L (H r) ω = _
    calc
      _ = ((m.real univ)⁻¹ • (∫ z, L (J z) ∂m) : Lp ℂ 2 (reducedLaw Q)) ω :=
        congrArg (fun v : Lp ℂ 2 (reducedLaw Q) => v ω) hmap
      _ = (m.real univ)⁻¹ • (∫ z, L (J z) ∂m) ω := hs
      _ = _ := by rw [hh, average_eq]
  have hlim := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' H (J (τ,x))).mp
    (holderTranspose_physical_average_tendsto J hJ τ x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hball : PDE.euclideanBall x r = {y | euclideanNorm (y-x) < r} := by
    ext y
    exact PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hr
  rw [hball]
  apply eLpNorm_congr_ae
  filter_upwards [hphys r, Lp.coeFn_compMeasurePreserving (F τ)
    (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)] with ω hm hz
  exact congrArg₂ (· - ·) hm hz

/-- The cylinder limits are the actual fixed-time transpose orbit. In
particular the quantitative estimate applies to its Euclidean increments. -/
theorem holder_transpose_fixed_time_increments
    (hinterior : node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ α K : ℝ, 0 < α ∧ α < 1 ∧ 1 ≤ K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (τ a p M : ℝ), 2 ≤ p → 0 ≤ M →
      MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      (∀ s ∈ Icc a τ,
        MemLp (T s.toNNReal f) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (T s.toNNReal f) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal M) →
    ∀ (R : ℝ), 0 < R → 0 < τ - R ^ 2 → a ≤ τ - R ^ 2 →
    ∀ (x y : Vec d), PDE.vecEuclideanNorm (y - x) ≤ R / 2 →
      (eLpNorm (fun ω => (T τ.toNNReal f) (translate y ω) -
        (T τ.toNNReal f) (translate x ω)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        K * (PDE.vecEuclideanNorm (y - x) / R) ^ α * (1 + ‖ζ‖ * R) * M := by
  obtain ⟨α, θ, K, hα, hα1, hθ, hθhalf, hK, hlimits⟩ :=
    holder_transpose_holder_cylinder_limits hinterior d hd D
  refine ⟨α, K, hα, hα1, hK, ?_⟩
  intro Q hQ i ζ P T hP hT f τ a p M hp hM hf hwindow R hR htime ha x y hxy
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr (by linarith)⟩
  have hp2 : 2 ≤ ENNReal.ofReal p := by
    exact_mod_cast ENNReal.ofReal_le_ofReal hp
  have hu : Continuous (fun s : ℝ => T s.toNNReal f) :=
    (hT.continuous_apply hP f).comp continuous_real_toNNReal
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative hu.stronglyMeasurable
  have hwindowU : ∀ s ∈ Icc a τ,
      MemLp (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (fun ω => U (s, ω)) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    intro s hs
    rw [memLp_congr_ae (heU s), eLpNorm_congr_ae (heU s)]
    exact hwindow s hs
  obtain ⟨g, hconv, hinc⟩ := hlimits Q hQ i ζ P T hP hT f U hU heU
    τ a p M hp hM hwindowU R hR htime ha
  let F : ℝ → Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) :=
    fun s => hT.lpRestriction hp hP s.toNNReal (hf.toLp f)
  have hF : Continuous F := ((hT.lpRestriction_c0 hp hP).2.2 _).comp continuous_real_toNNReal
  have hlift : complexLpToL2 (reducedLaw Q) hp2 (hf.toLp f) = f := by
    apply Lp.ext
    exact hf.coeFn_toLp
  have heF (s : ℝ) : (F s : FieldPair d → ℂ) =ᵐ[reducedLaw Q] T s.toNNReal f := by
    have hh := hT.lpRestriction_apply hp hP s.toNNReal (hf.toLp f)
    rw [hlift] at hh
    exact Filter.EventuallyEq.of_eq
      (congrArg (fun v : Lp ℂ 2 (reducedLaw Q) => (v : FieldPair d → ℂ)) hh)
  have hradii : Tendsto (fun n : ℕ => θ ^ n * R) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall (fun n => mul_pos (pow_pos hθ n) hR)⟩
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hθ.le (by linarith only [hθhalf])).mul_const R
  have hge (z : Vec d) : (g z : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (T τ.toNNReal f) (translate z ω) := by
    let mean := fun n ω =>
      ⨍ w in Ioo (τ - (θ ^ n * R) ^ 2) τ ×ˢ PDE.euclideanBall z (θ ^ n * R),
        U (w.1, translate w.2 ω)
    let v := fun ω => (F τ) (translate z ω)
    have hactual : Tendsto (fun n => eLpNorm (mean n - v)
        (ENNReal.ofReal p) (reducedLaw Q)) atTop (𝓝 0) :=
      (holder_transpose_physical_mean_tendsto Q p hp F hF U hU
        (fun s => (heU s).trans (heF s).symm) τ z).comp hradii
    have hzero : eLpNorm ((g z : FieldPair d → ℂ) - v)
        (ENNReal.ofReal p) (reducedLaw Q) = 0 := by
      apply le_antisymm _ bot_le
      have hlim := (hconv z).add hactual
      simp only [add_zero] at hlim
      apply ge_of_tendsto hlim
      exact Filter.Eventually.of_forall fun n => by
        calc
          _ = eLpNorm (((g z : FieldPair d → ℂ) - mean n) + (mean n - v))
              (ENNReal.ofReal p) (reducedLaw Q) := by
            congr 1
            ext ω
            simp only [Pi.add_apply, Pi.sub_apply]
            abel
          _ ≤ _ := by
            simpa only [eLpNorm_sub_comm] using
              eLpNorm_add_le (f := (g z : FieldPair d → ℂ) - mean n)
                (g := mean n - v) (μ := reducedLaw Q) (show 1 ≤ ENNReal.ofReal p from Fact.out)
    have he : (g z : FieldPair d → ℂ) =ᵐ[reducedLaw Q] v := by
      have hh := (eLpNorm_eq_zero_iff (ne_of_gt (lt_of_lt_of_le (by norm_num) hp2))).mp hzero
      filter_upwards [hh] with ω hω
      exact sub_eq_zero.mp hω
    exact he.trans ((measurePreserving_translate (reducedLaw Q)
      (reducedLaw_stationary Q) z).quasiMeasurePreserving.ae (heF τ))
  have hnorm := eLpNorm_congr_ae ((hge y).sub (hge x)) (p := ENNReal.ofReal p)
  calc
    _ = (eLpNorm ((g y : FieldPair d → ℂ) - (g x : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal := congrArg ENNReal.toReal hnorm.symm
    _ ≤ _ := hinc x y hxy

theorem holder_transpose_gaussian_tail_power
    {c x q : ℝ} (hc : 0 < c) (hx : 0 < x) (hx1 : x ≤ 1) (hq1 : q ≤ 1) :
    Real.exp (-c / x) ≤ (1 / c) * x ^ q := by
  have hexp : c / x ≤ Real.exp (c / x) :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (Real.add_one_le_exp _)
  have hlin : Real.exp (-c / x) ≤ x / c := by
    calc
      Real.exp (-c / x) = 1 / Real.exp (c / x) := by
        rw [neg_div, Real.exp_neg, one_div]
      _ ≤ 1 / (c / x) := one_div_le_one_div_of_le (div_pos hc hx) hexp
      _ = x / c := by field_simp
  have hpow : x ≤ x ^ q := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx hx1 hq1
  calc
    Real.exp (-c / x) ≤ x / c := hlin
    _ ≤ x ^ q / c := div_le_div_of_nonneg_right hpow hc.le
    _ = (1 / c) * x ^ q := by ring

/-- The completed local Gaussian estimate gives a pure power bound; its
exponential tail is absorbed uniformly before choosing the law and endpoint. -/
theorem holder_transpose_gaussian_power_of_local_increments
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (p α : ℝ)
    (hp : 2 ≤ p) (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (f : Lp ℂ 2 (reducedLaw Q)) (A M R : ℝ),
      0 ≤ A → 0 ≤ M → 0 < R →
      MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M →
      (∀ x : EinsteinRelation.Vec d, euclideanNorm x ≤ R →
        eLpNorm (fun ω => f (translate x ω) - f ω)
          (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (A * (euclideanNorm x / R) ^ α)) →
      ∀ (s : ℝ) (hs : 0 < s), s ≤ R ^ 2 →
      MemLp ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm ((f - gaussianAverage hd Q s hs f) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (A + M) * (s / R ^ 2) ^ (α / 2) := by
  obtain ⟨C, c, hC, hc, hlocal⟩ :=
    holder_gaussian_unsmoothing_of_local_increment_bound d hd D p α hp hα hα1
  refine ⟨C * (1 + 1 / c), by positivity, ?_⟩
  intro Q f A M R hA hM hR hf hfM hinc s hs hsR
  obtain ⟨hmem, hbound⟩ := hlocal Q f A M R hA hM hR hf hfM hinc s hs hsR
  refine ⟨hmem, ?_⟩
  have hx : 0 < s / R ^ 2 := div_pos hs (sq_pos_of_pos hR)
  have hx1 : s / R ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos hR)).mpr hsR
  have htail := holder_transpose_gaussian_tail_power hc hx hx1 (by linarith : α / 2 ≤ 1)
  have he : -c * R ^ 2 / s = -c / (s / R ^ 2) := by field_simp
  rw [← he] at htail
  have hpow : 0 ≤ (s / R ^ 2) ^ (α / 2) := Real.rpow_nonneg hx.le _
  have hfactor : 1 ≤ 1 + 1 / c := le_add_of_nonneg_right (by positivity)
  have hfirst : (s / R ^ 2) ^ (α / 2) ≤
      (1 + 1 / c) * (s / R ^ 2) ^ (α / 2) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hfactor hpow
  have hsecond : Real.exp (-c * R ^ 2 / s) ≤
      (1 + 1 / c) * (s / R ^ 2) ^ (α / 2) :=
    htail.trans (mul_le_mul_of_nonneg_right (by linarith : 1 / c ≤ 1 + 1 / c) hpow)
  have htotal := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hfirst hA)
      (mul_le_mul_of_nonneg_left hsecond hM)) hC.le
  have hfinite : C * (A * (s / R ^ 2) ^ (α / 2) +
      M * Real.exp (-c * R ^ 2 / s)) ≥ 0 := by positivity
  exact (ENNReal.toReal_le_of_le_ofReal hfinite hbound).trans (htotal.trans_eq (by ring))

@[nolint unusedArguments]
theorem holder_average_transpose_of_deps
  (h0 : EinsteinFull.Blueprint.node_e_u3A_local_u2D_timeStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt)
  (h2 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h3 : EinsteinFull.Blueprint.node_e_u3A_holder_u2D_average_u23_unforced_u2D_interiorStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ α : ℝ, 0 < α ∧
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → let ν : EndpointIndex d := .inr true

    ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      ∀ b : ℝ, 0 < b → b ≤ 1 / 16 → ∀ hbt : 0 < b * (t : ℝ),
        MemLp ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm ((U - gaussianAverage hd Q (b * (t : ℝ)) hbt U) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  intro d hd D
  obtain ⟨α, K, hα, hα1, hK, hincrements⟩ :=
    holder_transpose_fixed_time_increments h3 d hd D
  refine ⟨α, hα, ?_⟩
  intro p hp
  obtain ⟨Cg, hCg, hgrowth⟩ := h1 d D.ellipticity D.dependenceRange p hd hp
  obtain ⟨H, hH, hgauss⟩ :=
    holder_transpose_gaussian_power_of_local_increments d hd D p α hp hα hα1.le
  let C := 1 + H * (K + 1) * (16 : ℝ) ^ (α / 2)
  have hC : 1 ≤ C := le_add_of_nonneg_right (by positivity)
  refine ⟨C, Cg, hC, hCg, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P T hP hT ν t ht U U8
  letI := reducedLaw_probability Q
  have hf : MemLp (U8 : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
    (holder_average_memLp_of_local_time h0 d hd D p hp Q hQ β a μ hβ ha hμ
      ζ P T hP hT ν t ht).1
  refine ⟨hf, ?_⟩
  let f := U8
  let τ : ℝ≥0 := 7 * t / 8
  let R : ℝ := Real.sqrt (t : ℝ) / 2
  let N := (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  let M := Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) * N
  have hN : 0 ≤ N := ENNReal.toReal_nonneg
  have hM : 0 ≤ M := mul_nonneg (Real.exp_nonneg _) hN
  have hτ : (τ : ℝ) = 7 * (t : ℝ) / 8 := by
    simp only [τ, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_ofNat]
  have hsum : τ + t / 8 = t := by
    apply NNReal.eq
    simp only [NNReal.coe_add, NNReal.coe_div, NNReal.coe_ofNat, hτ]
    ring
  have hrestart : T τ f = U := by
    change T τ (T (t / 8) (β ⟨0, by omega⟩)) = T t (β ⟨0, by omega⟩)
    rw [← ContinuousLinearMap.comp_apply, ← hT.add hP, hsum]
  have hwindow : ∀ s ∈ Icc (0 : ℝ) (τ : ℝ),
      MemLp (T s.toNNReal f) (ENNReal.ofReal p) (reducedLaw Q) ∧
      eLpNorm (T s.toNNReal f) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    intro s hs
    have hg := (hgrowth Q ⟨0, by omega⟩ ζ P T hP hT).1 s.toNNReal f hf
    refine ⟨hg.2.1, ?_⟩
    have hst : (s.toNNReal : ℝ) ≤ (t : ℝ) := by
      rw [Real.coe_toNNReal _ hs.1]
      linarith [hs.2, hτ]
    have hexp : Real.exp (Cg * ‖ζ‖ ^ 2 * (s.toNNReal : ℝ)) ≤
        Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst (by positivity))
    calc
      _ ≤ ENNReal.ofReal (Real.exp (Cg * ‖ζ‖ ^ 2 * (s.toNNReal : ℝ))) *
          eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := hg.2.2.2.2.1
      _ ≤ ENNReal.ofReal (Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
        mul_le_mul_left (ENNReal.ofReal_le_ofReal hexp) _
      _ = ENNReal.ofReal M := by
        rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  have hUmem : MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
    have hh := (hwindow (τ : ℝ) ⟨by positivity, le_rfl⟩).1
    simpa only [Real.toNNReal_coe, hrestart] using hh
  have hUM : eLpNorm (U : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ≤ ENNReal.ofReal M := by
    simpa only [Real.toNNReal_coe, hrestart] using
      (hwindow (τ : ℝ) ⟨by positivity, le_rfl⟩).2
  have hsqrt : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  have hR : 0 < R := div_pos hsqrt (by norm_num)
  have hR2 : R ^ 2 = (t : ℝ) / 4 := by
    dsimp only [R]
    rw [div_pow, Real.sq_sqrt t.coe_nonneg]
    norm_num
  have hrad2 : (R / 2) ^ 2 = (t : ℝ) / 16 := by rw [div_pow, hR2]; ring
  have htime : 0 < (τ : ℝ) - R ^ 2 := by rw [hτ, hR2]; linarith
  have hinc : ∀ x : Vec d, euclideanNorm x ≤ R / 2 →
      eLpNorm (fun ω => U (translate x ω) - U ω) (ENNReal.ofReal p) (reducedLaw Q) ≤
        ENNReal.ofReal ((K * (1 + ‖ζ‖ * R) * M) * (euclideanNorm x / (R / 2)) ^ α) := by
    intro x hx
    have hnorm (y : Vec d) : PDE.vecEuclideanNorm y = euclideanNorm y := rfl
    have hxnonneg : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    have hb := hincrements Q hQ ⟨0, by omega⟩ ζ P T hP hT f (τ : ℝ) 0 p M
      hp hM hf hwindow R hR htime htime.le (0 : Vec d) x (by simpa only [sub_zero, hnorm] using hx)
    simp only [Real.toNNReal_coe, hrestart, translate_zero, sub_zero, hnorm] at hb
    have hm : MemLp (fun ω => U (translate x ω) - U ω)
        (ENNReal.ofReal p) (reducedLaw Q) :=
      (hUmem.comp_measurePreserving (measurePreserving_translate (reducedLaw Q)
        (reducedLaw_stationary Q) x)).sub hUmem
    apply (ENNReal.toReal_le_toReal hm.eLpNorm_ne_top ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    have hratio : euclideanNorm x / R ≤ euclideanNorm x / (R / 2) :=
      div_le_div_of_nonneg_left hxnonneg (by positivity) (by linarith)
    have hpow := Real.rpow_le_rpow (div_nonneg hxnonneg hR.le) hratio hα.le
    exact hb.trans (by
      convert mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ K * (1 + ‖ζ‖ * R) * M) using 1 <;> ring)
  intro b hb hb16 hbt
  obtain ⟨hmem, hbound⟩ := hgauss Q U (K * (1 + ‖ζ‖ * R) * M) M (R / 2)
    (by positivity) hM (by positivity) hUmem hUM hinc (b * (t : ℝ)) hbt
    (by rw [hrad2]; nlinarith)
  refine ⟨hmem, ?_⟩
  have hscale : b * (t : ℝ) / (R / 2) ^ 2 = 16 * b := by
    rw [hrad2]
    field_simp
  rw [hscale, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 16) hb.le] at hbound
  have hforce : 1 + ‖ζ‖ * R ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) := by
    dsimp only [R]
    nlinarith [mul_nonneg (norm_nonneg ζ) hsqrt.le]
  have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) := by
    linarith [mul_nonneg (norm_nonneg ζ) hsqrt.le]
  have hpoly : 1 + ‖ζ‖ * Real.sqrt (t : ℝ) ≤
      (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hC
  have hcoeff : K * (1 + ‖ζ‖ * R) + 1 ≤
      (K + 1) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C := by
    have hh := mul_le_mul_of_nonneg_left hforce (by linarith only [hK] : 0 ≤ K)
    have hh' := mul_le_mul_of_nonneg_left hpoly (by linarith only [hK] : 0 ≤ K + 1)
    nlinarith
  have hconstant : H * (K + 1) * (16 : ℝ) ^ (α / 2) ≤ C := by dsimp only [C]; linarith
  calc
    _ ≤ H * (K * (1 + ‖ζ‖ * R) * M + M) * ((16 : ℝ) ^ (α / 2) * b ^ (α / 2)) := hbound
    _ = (H * (16 : ℝ) ^ (α / 2)) *
        (K * (1 + ‖ζ‖ * R) + 1) * b ^ (α / 2) *
        Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by dsimp only [M]; ring
    _ ≤ (H * (16 : ℝ) ^ (α / 2)) *
        ((K + 1) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C) * b ^ (α / 2) *
        Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by gcongr
    _ = (H * (K + 1) * (16 : ℝ) ^ (α / 2)) * b ^ (α / 2) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by ring
    _ ≤ C * b ^ (α / 2) * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cg * ‖ζ‖ ^ 2 * (t : ℝ)) * N := by gcongr

end EinsteinFull.Blueprint
