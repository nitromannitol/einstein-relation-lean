import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup_u23_endpoints
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
import EinsteinFull.Calculus.C2EndpointShortTimeProjection
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.ComplexTransposeGradientTimeSupport
import EinsteinFull.Work.W2.TransposeResolventGradientContinuitySupport
import EinsteinFull.Calculus.ComplexTransposeSpatialSupport
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import EinsteinFull.Calculus.C8PhysicalTransposeGradientContinuity
import EinsteinFull.Calculus.C8PhysicalTransposeTimePrimitive
import EinsteinRelation.Calculus.ClassicalSpatialDerivative
import EinsteinRelation.Sharpness.PhysicalLawSampleBounds
import EinsteinFull.Calculus.C1ShortTimeClockEndpointProjection
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/- SUPERVISOR EXACT TARGET (not a declaration or proof); replace with proved command.
theorem endpoint_short_time_transpose_projection_of_graph_deps :

∀ (hA : node_stationary_u2D_analytic_u2D_semigroupStmt) (hlocal : node_e_u3A_forced_u2D_localityStmt),
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (B : ℝ) (hB : 0 < B) (T : ℝ),
    ∃ R K c : ℝ, 1 ≤ R ∧ 0 < K ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ B →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → let ν : EndpointIndex d := .inr true

    ∀ t : ℝ≥0, (t : ℝ) ≤ T → (t : ℝ) ≤ 1 → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2)
-/
private theorem short_time_transpose_divergence_of_tests {d : ℕ} {F : Vec d → Fin d → ℂ}
    {q : Vec d → ℂ}
    (hF : ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (fun x => F x j) 2 (volume.restrict K))
    (hq : ∀ K : Set (Vec d), IsCompact K → MemLp q 2 (volume.restrict K))
    (hw : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q x * (φ x : ℂ)) = -(∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)))
    (L : ℂ →L[ℝ] ℝ) :
    HasWeakDivergence univ (fun x j => L (F x j)) (fun x => L (q x)) := by
  have hloc {v : Vec d → ℂ}
      (hv : ∀ K : Set (Vec d), IsCompact K → MemLp v 2 (volume.restrict K)) :
      LocallyIntegrable (fun x => L (v x)) volume := by
    rw [locallyIntegrable_iff]
    intro K hK
    let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (L.comp_memLp' (hv K hK)).integrable (by norm_num)
  refine ⟨fun j => (hloc (fun K hK => hF K hK j)).locallyIntegrableOn univ,
    (hloc hq).locallyIntegrableOn univ, ?_⟩
  intro φ hφ
  have hi := integrable_spatial_mul_test hq hφ.1.continuous hφ.2.1
  have hj (j : Fin d) : Integrable (fun x => F x j * (coordinateDerivative j φ x : ℂ)) volume := integrable_spatial_mul_test (fun K hK => hF K hK j)
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hφ.2.1.fderiv_apply ℝ (unitVector j))
  have hs := integrable_finsetSum Finset.univ (fun j _ => hj j)
  have he := congrArg L (hw φ hφ.1 hφ.2.1)
  rw [map_neg, ← L.integral_comp_comm hi, ← L.integral_comp_comm hs] at he
  have hp (z : ℂ) (c : ℝ) : L (z * (c : ℂ)) = L z * c := by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul, mul_comm]
  simp only [map_sum, hp] at he
  simpa only [Measure.restrict_univ, dot, gradient] using (neg_eq_iff_eq_neg.mp he.symm)

/-- The full stationary transpose graph gives a common spatial event before
all real projections of its conservative weak equation. -/
theorem short_time_transpose_generator_local_divergence
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (i : Fin d) (ζ : ℂ)
    (U q : Lp ℂ 2 (reducedLaw Q))
    (hUq : IsComplexTransposeGeneratorPair Q i ζ U q) :
    ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U H ∧
      ∀ᵐ ω ∂reducedLaw Q,
        let F := fun x j => (∑ k, (ω.1 x j k : ℂ) * H k (translate x ω)) -
          2 * ζ * (ω.1 x j i : ℂ) * U (translate x ω)
        HasWeakGradient univ (fun x => (U (translate x ω)).re)
          (fun x j => (H j (translate x ω)).re) ∧
        HasWeakGradient univ (fun x => (U (translate x ω)).im)
          (fun x j => (H j (translate x ω)).im) ∧
        (∀ K : Set (Vec d), IsCompact K →
          MemLp (fun x => U (translate x ω)) 2 (volume.restrict K) ∧
          ∀ j, MemLp (fun x => H j (translate x ω)) 2 (volume.restrict K)) ∧
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ (fun x j => L (F x j))
          (fun x => L (2 * q (translate x ω))) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨H, hH, hw⟩ := hUq.exists_spatial_flux_all_tests
  let B : Fin d → FieldPair d → ℂ := fun j ω =>
    (∑ k, (ω.1 0 j k : ℂ) * H k ω) - 2 * ζ * (ω.1 0 j i : ℂ) * U ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hBm (j : Fin d) : Measurable (B j) :=
    (Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable).sub
      ((measurable_const.mul (hm j i)).mul (Lp.stronglyMeasurable U).measurable)
  have hB (j : Fin d) : MemLp (B j) 2 (reducedLaw Q) := by
    have hb := (Lp.memLp (complexCoefficientMul Q j i U)).ae_eq
      (complexCoefficientMul_coe Q j i U)
    simpa only [B, mul_assoc] using!
      (memLp_complex_coefficient_flux Q H j).sub (hb.const_mul (2 * ζ))
  have hq : MemLp (fun ω => (2 : ℂ) * q ω) 2 (reducedLaw Q) :=
    (Lp.memLp q).const_mul 2
  refine ⟨H, hH, ?_⟩
  filter_upwards [hH.ae_reduced_spatial Q, hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (measurable_const.mul (Lp.stronglyMeasurable q).measurable) hq,
    ae_all_iff.mpr fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hBm j) (hB j)] with ω hHω hwω hqω hBω
  have hweak : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, (2 : ℂ) * q (translate x ω) * (φ x : ℂ)) =
        -(∫ x, ∑ j, B j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
    intro φ hφ hφc
    have he := hwω φ hφ hφc
    simp only [B, translate_matrix, add_zero, mul_assoc, integral_const_mul] at he ⊢
    linear_combination (2 : ℂ) * he
  refine ⟨hHω.1, hHω.2.1, hHω.2.2, ?_⟩
  intro L
  have he := short_time_transpose_divergence_of_tests
    (fun K hK j => hBω j K hK) hqω hweak L
  simpa only [B, translate_matrix, add_zero, Pi.mul_apply] using! he

private theorem short_time_transpose_compact_physical_test
    {d : ℕ} (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) :
    ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v J ∧
      (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (coordinateDerivative j φ x : ℂ)) := by
  have hv : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp hφ.continuous).memLp_of_hasCompactSupport
      (hφc.comp_left rfl)
  have hJ (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
    (Complex.continuous_ofReal.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        ((hφc.fderiv_apply ℝ (unitVector j)).comp_left rfl)
  refine ⟨hv.toLp _, fun j => (hJ j).toLp _, ?_, hv.coeFn_toLp,
    fun j => (hJ j).coeFn_toLp⟩
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _ _ _
    hv.coeFn_toLp (fun j => (hJ j).coeFn_toLp)).mpr
  constructor
  · intro j
    simpa only [Complex.ofReal_re] using
      hasWeakPartialDerivative_of_contDiff j φ (hφ.of_le (by simp))
  · intro j
    simp only [Complex.ofReal_im]
    have hz : coordinateDerivative j (fun _ : Vec d => (0 : ℝ)) = fun _ => 0 := by
      funext x
      unfold coordinateDerivative
      rw [fderiv_const_apply, zero_apply]
    have hh := hasWeakPartialDerivative_of_contDiff j
      (fun _ : Vec d => (0 : ℝ)) contDiff_const
    rw [hz] at hh
    exact hh

/-- The full physical transpose graph gives its conservative divergence with
its prescribed H1 gradient and the literal transposed principal coefficient. -/
theorem short_time_physical_transpose_generator_divergence
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (u g : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) u H)
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g) :
    let F := fun x j => (∑ k, (a x k j : ℂ) * H k x) -
      2 * ζ * (a x j i : ℂ) * u x
    ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ (fun x j => L (F x j))
      (fun x => L (2 * g x)) := by
  intro F
  obtain ⟨K, hK, hw⟩ := hug
  have hKH := physicalH1Graph_gradient_unique volume (Or.inl rfl) u K H hK hH
  subst K
  have hA (j : Fin d) : MemLp (fun x => ∑ k, (a x k j : ℂ) * H k x) 2 volume :=
    memLp_finsetSum _ (fun k _ => (ha k j).fun_mul (Lp.memLp (H k)))
  have hB (j : Fin d) : MemLp (fun x => (a x j i : ℂ) * u x) 2 volume :=
    (ha j i).fun_mul (Lp.memLp u)
  have hF (j : Fin d) : MemLp (fun x => F x j) 2 volume := by
    simpa only [F, Pi.sub_def, mul_assoc] using (hA j).sub ((hB j).const_mul (2 * ζ))
  have hweak : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, (2 : ℂ) * g x * (φ x : ℂ)) =
        -(∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)) := by
    intro φ hφ hφc
    obtain ⟨v, J, hv, hvr, hJr⟩ := short_time_transpose_compact_physical_test φ hφ hφc
    have he := hw v J hv
    have hl : (∫ x, g x * v x) = ∫ x, g x * (φ x : ℂ) :=
      integral_congr_ae (hvr.mono fun x hx => by dsimp; rw [hx])
    have hp : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * H k x * J j x) =
        ∫ x, ∑ j, (∑ k, (a x k j : ℂ) * H k x) *
          (coordinateDerivative j φ x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hJr] with x hx
      simp only [hx, Finset.sum_mul]
    have hb : (∫ x, u x * (∑ j, (a x j i : ℂ) * J j x)) =
        ∫ x, u x * (∑ j, (a x j i : ℂ) * (coordinateDerivative j φ x : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hJr] with x hx
      simp only [hx]
    rw [hl, hp, hb] at he
    have hD (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
      (Lp.memLp (J j)).ae_eq (hJr j)
    have hAi := integrable_finsetSum Finset.univ fun j _ => (hA j).integrable_mul (hD j)
    have hBi : Integrable (fun x => u x *
        (∑ j, (a x j i : ℂ) * (coordinateDerivative j φ x : ℂ))) volume := by
      have hi := integrable_finsetSum Finset.univ fun j _ => (hB j).integrable_mul (hD j)
      convert hi using 1
      funext x
      simp only [Pi.mul_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hf : (fun x => ∑ j, F x j * (coordinateDerivative j φ x : ℂ)) =
        (fun x => (∑ j, (∑ k, (a x k j : ℂ) * H k x) *
          (coordinateDerivative j φ x : ℂ)) - (2 * ζ) *
            (u x * (∑ j, (a x j i : ℂ) * (coordinateDerivative j φ x : ℂ)))) := by
      funext x
      simp only [F, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hAi' : Integrable (fun x => ∑ j, (∑ k, (a x k j : ℂ) * H k x) *
        (coordinateDerivative j φ x : ℂ)) volume := hAi
    rw [hf, integral_sub hAi' (hBi.const_mul _), integral_const_mul]
    simp only [mul_assoc, integral_const_mul]
    linear_combination (2 : ℂ) * he
  intro L
  exact short_time_transpose_divergence_of_tests (fun K _ j => (hF j).restrict K)
    (fun K _ => ((Lp.memLp g).const_mul (2 : ℂ)).restrict K) hweak L

/-- Subtracting the physical retained transpose equation preserves the force
inside the divergence and exposes the full, correctly indexed matrix defect. -/
theorem short_time_transpose_residual_divergence {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (u v q p : Vec d → ℂ) (H K : Fin d → Vec d → ℂ)
    (ha : ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
      (fun x j => L ((∑ k, (a x j k : ℂ) * H k x) -
        2 * ζ * (a x j i : ℂ) * u x)) (fun x => L (2 * q x)))
    (hb : ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
      (fun x j => L ((∑ k, (b x k j : ℂ) * K k x) -
        2 * ζ * (b x j i : ℂ) * v x)) (fun x => L (2 * p x))) :
    let F := fun x j => (1 / 2 : ℂ) *
      (∑ k, ((a x j k - b x k j : ℝ) : ℂ) * K k x) -
        ζ * ((a x j i - b x j i : ℝ) : ℂ) * v x
    ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
      (fun x j => L ((∑ k, (a x j k : ℂ) * (H k x - K k x)) -
        2 * ζ * (a x j i : ℂ) * (u x - v x) + 2 * F x j))
      (fun x => L (2 * (q x - p x))) := by
  intro F L
  have he (x : Vec d) (j : Fin d) :
      ((∑ k, (a x j k : ℂ) * H k x) - 2 * ζ * (a x j i : ℂ) * u x) -
        ((∑ k, (b x k j : ℂ) * K k x) - 2 * ζ * (b x j i : ℂ) * v x) =
      (∑ k, (a x j k : ℂ) * (H k x - K k x)) -
        2 * ζ * (a x j i : ℂ) * (u x - v x) + 2 * F x j := by
    simp only [F, Complex.ofReal_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  apply (Correctors.hasWeakDivergence_sub (ha L) (hb L)).congr_ae
  · exact ae_of_all _ fun x => funext fun j => by
      simpa only [Pi.sub_apply, ← map_sub] using congrArg L (he x j)
  · exact ae_of_all _ fun x => by simp only [← map_sub, mul_sub]

/-- The stationary-minus-retained equation holds on an event selected before
all physical retained graph data. No global spatial L2 is required of the
stationary orbit. -/
theorem short_time_transpose_generator_retained_residual
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (i : Fin d) (ζ : ℂ) (u q : Lp ℂ 2 (reducedLaw Q))
    (huq : IsComplexTransposeGeneratorPair Q i ζ u q) :
    ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ b : Vec d → Mat d,
        (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
        ∀ (v p : Lp ℂ 2 (volume : Measure (Vec d)))
          (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalH1Graph volume (Or.inl rfl) v K →
          IsPhysicalComplexTransposeGeneratorPair b i ζ v p →
        let F := fun x j => (1 / 2 : ℂ) *
          (∑ k, ((ω.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
            ζ * ((ω.1 x j i - b x j i : ℝ) : ℂ) * v x
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
          (fun x j => L ((∑ k, (ω.1 x j k : ℂ) * (H k (translate x ω) - K k x)) -
            2 * ζ * (ω.1 x j i : ℂ) * (u (translate x ω) - v x) + 2 * F x j))
          (fun x => L (2 * (q (translate x ω) - p x))) := by
  obtain ⟨H, hH, he⟩ := short_time_transpose_generator_local_divergence hd Q i ζ u q huq
  refine ⟨H, hH, ?_⟩
  filter_upwards [he] with ω hω
  intro b hb v p K hK hvp
  exact short_time_transpose_residual_divergence (fun x => ω.1 x) b i ζ
    (fun x => u (translate x ω)) v (fun x => q (translate x ω)) p
    (fun k x => H k (translate x ω)) (fun k x => K k x) hω.2.2.2
    (short_time_physical_transpose_generator_divergence b i ζ hb v p K hK hvp)

/-- On the unit-cutoff region the complete transpose defect vanishes. The
symmetry used here is obtained from the actual environment event. -/
theorem short_time_transpose_retained_defect_support
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)) (x : Vec d), χ x = 1 →
      ∀ (i j : Fin d) (ζ v : ℂ) (K : Fin d → ℂ),
        (1 / 2 : ℂ) * (∑ k,
          ((ω.1 x j k - (ForcedLocality.retainedPair χ ω).1 x k j : ℝ) : ℂ) * K k) -
          ζ * ((ω.1 x j i - (ForcedLocality.retainedPair χ ω).1 x j i : ℝ) : ℂ) * v = 0 := by
  filter_upwards [c4_ae_reduced_physical_elliptic Q] with ω hω
  intro χ x hχ i j ζ v K
  have hs (k : Fin d) : ω.1 x j k = ω.1 x k j :=
    congrArg (fun M : Mat d => M k j) (hω x).1
  simp only [ForcedLocality.retainedPair, ContinuousMap.coe_mk, hχ,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, one_mul, sub_self,
    zero_mul, add_zero, hs, Complex.ofReal_zero,
    Finset.sum_const_zero, mul_zero]

/-- The actual transpose drift endpoint and its actual temporal derivative
satisfy the retained conservative residual at every time. Smooth drift data
supply their full generator pair internally, including at the initial trace. -/
theorem short_time_transpose_endpoint_retained_residual
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      (∀ s : ℝ, 0 ≤ s → HasDerivWithinAt
        (fun r : ℝ => Pdag r.toNNReal (β ⟨0, by omega⟩))
        (Pdag s.toNNReal g) (Ici s) s) ∧
      ∀ t : ℝ≥0,
      ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (Pdag t (β ⟨0, by omega⟩)) H ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ b : Vec d → Mat d,
        (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
        ∀ (v p : Lp ℂ 2 (volume : Measure (Vec d)))
          (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalH1Graph volume (Or.inl rfl) v K →
          IsPhysicalComplexTransposeGeneratorPair b ⟨0, by omega⟩ ζ v p →
        let F := fun x j => (1 / 2 : ℂ) *
          (∑ k, ((ω.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
            ζ * ((ω.1 x j ⟨0, by omega⟩ - b x j ⟨0, by omega⟩ : ℝ) : ℂ) * v x
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
          (fun x j => L ((∑ k, (ω.1 x j k : ℂ) * (H k (translate x ω) - K k x)) -
            2 * ζ * (ω.1 x j ⟨0, by omega⟩ : ℂ) *
              ((Pdag t (β ⟨0, by omega⟩)) (translate x ω) - v x) + 2 * F x j))
          (fun x => L (2 * ((Pdag t g) (translate x ω) - p x))) := by
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator
    (i := ⟨0, by omega⟩) (ζ := ζ) hβ ⟨0, by omega⟩
  refine ⟨g, fun s hs => hPdag.hasDerivWithinAt_orbit hP hg s hs, ?_⟩
  intro t
  exact short_time_transpose_generator_retained_residual hd Q ⟨0, by omega⟩ ζ
    (Pdag t (β ⟨0, by omega⟩)) (Pdag t g) (hPdag.map_generator hP hg t)

private theorem c8_joint_l2_representative {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {u : T → Lp ℂ 2 μ} (hu : StronglyMeasurable u) :
    ∃ U : T × Ω → ℂ, Measurable U ∧ ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t := by
  obtain ⟨v, hv, herr⟩ := StronglyMeasurable.exists_joint_l2_approx hu
  let U : T × Ω → ℂ := fun p =>
    (limsup (fun n => (v n p.1 p.2).re) atTop : ℝ) +
      (limsup (fun n => (v n p.1 p.2).im) atTop : ℝ) * Complex.I
  have hUm : Measurable U :=
    (Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_re.comp (hv n))).add
      ((Complex.measurable_ofReal.comp (.limsup fun n => Complex.measurable_im.comp (hv n))).mul
        measurable_const)
  refine ⟨U, hUm, fun t => ?_⟩
  have hB : (∑' n : ℕ, ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ n)) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
      (summable_geometric_two.mul_left 4)]
    exact ENNReal.ofReal_ne_top
  have hca : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm ((fun ω => v n t ω) - (fun ω => v m t ω)) 2 μ <
        ENNReal.ofReal (4 * (1 / 2 : ℝ) ^ N) := by
    intro N n m hn hm
    rw [eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm, ← Lp.enorm_def, ← ofReal_norm]
    apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
    have hnm : ‖v n t - v m t‖ ≤ ‖v n t - u t‖ + ‖v m t - u t‖ :=
      by simpa only [norm_sub_rev (u t) (v m t)] using!
        norm_sub_le_norm_sub_add_norm_sub (v n t) (u t) (v m t)
    have hnN : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    have hmN : (1 / 2 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    have hpos : 0 < (1 / 2 : ℝ) ^ N := by positivity
    linarith [herr n t, herr m t]
  have hlim := Lp.ae_tendsto_of_cauchy_eLpNorm
    (fun n => Lp.aestronglyMeasurable (v n t)) (by norm_num : (1 : ℝ≥0∞) ≤ 2) hB hca
  have hpoint : ∀ᵐ ω ∂μ, Tendsto (fun n => v n t ω) atTop (𝓝 (U (t, ω))) := by
    filter_upwards [hlim] with ω hω
    obtain ⟨z, hz⟩ := hω
    have hre := (Complex.continuous_re.tendsto z |>.comp hz).limsup_eq
    have him := (Complex.continuous_im.tendsto z |>.comp hz).limsup_eq
    simp only [Function.comp_def] at hre him
    have he : U (t, ω) = z := by
      dsimp only [U]
      rw [hre, him, Complex.re_add_im]
    rw [he]
    exact hz
  have hvlim : Tendsto (fun n => v n t) atTop (𝓝 (u t)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (herr n t).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hvlim).exists_seq_tendsto_ae
  filter_upwards [hpoint, hae] with ω hω hω'
  exact tendsto_nhds_unique (hω.comp hns.tendsto_atTop) hω'


private def C8TransposeC0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem C8TransposeC0Graph.hasDerivWithinAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : C8TransposeC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => P (Real.toNNReal s) f)
      (P (Real.toNNReal t) g) (Ici t) t := by
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mpr
  have he : Tendsto (fun s : ℝ => Real.toNNReal (s-t))
      (𝓝[>] t) (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [Function.comp_def, id_eq, sub_self, Real.toNNReal_zero] using
        (continuous_real_toNNReal.comp (continuous_id.fun_sub (continuous_const (y := t)))).tendsto t
          |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [eventually_mem_nhdsWithin] with s hs
      exact Real.toNNReal_pos.mpr (sub_pos.mpr hs)
  have h := (((P (Real.toNNReal t)).continuous.tendsto g).comp hfg).comp he
  apply h.congr'
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  change t < s at hs
  have hs0 : 0 ≤ s := ht.trans hs.le
  have ha : Real.toNNReal t + Real.toNNReal (s-t) = Real.toNNReal s := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left ht,
      max_eq_left (sub_nonneg.mpr hs.le), max_eq_left hs0]
    ring
  simp only [Function.comp_apply]
  rw [map_smul, map_sub]
  simp only [slope_def_module, Real.coe_toNNReal', max_eq_left (sub_nonneg.mpr hs.le)]
  rw [← ContinuousLinearMap.comp_apply, ← hPm, ha]

private theorem C8TransposeC0Graph.integral_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : C8TransposeC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, P s.toNNReal g) = P t.toNNReal f - f := by
  have hf := (hPc f).comp continuous_real_toNNReal
  have hg := (hPc g).comp continuous_real_toNNReal
  simpa only [Function.comp_apply, Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hf.continuousOn
      (fun s hs => (hfg.hasDerivWithinAt_orbit hPm s hs.1.le).Ioi_of_Ici)
      (hg.intervalIntegrable 0 t)


/-- A primitive representative of the actual stationary transpose orbit. -/
theorem short_time_stationary_transpose_joint_primitive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      ∀ s ω, F (s, ω) = f ω + ∫ r in Icc (0 : ℝ) s, U (r, ω) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU⟩ := c8_joint_l2_representative
    (((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).stronglyMeasurable)
  let F : ℝ × FieldPair d → ℂ := fun p => f p.2 + ∫ r in Icc (0 : ℝ) p.1, U (r, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hU 0)
  refine ⟨F, U, hF, hU, ?_, heU, fun _ _ => rfl⟩
  intro s
  by_cases hs : 0 ≤ s
  · have hi := integrableOn_comp_toNNReal_Icc _ (hPdag.continuous_apply hP g) s
    obtain ⟨_, he⟩ := short_time_coeFn_integral_joint_l2_local hi hU heU univ (by simp)
    rw [Measure.restrict_univ] at he
    have hFTC : (∫ r in Icc (0 : ℝ) s, Pdag r.toNNReal g) = Pdag s.toNNReal f - f := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
      simpa only [Real.coe_toNNReal _ hs, Real.toNNReal_coe] using
        IsComplexTransposeSemigroup.integral_orbit_eq_sub hP hPdag hfg s.toNNReal
    rw [hFTC] at he
    filter_upwards [he, Lp.coeFn_sub (Pdag s.toNNReal f) f] with ω he hsub
    dsimp only [F]
    rw [← he, hsub]
    exact add_sub_cancel _ _
  · have hs0 : s.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_ge hs)
    have hI : Icc (0 : ℝ) s = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hs)
    exact ae_of_all _ fun ω => by simp [F, hI, hs0, hPdag.zero hP]

private theorem c8_physical_transpose_generator_primitive
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ U : ℝ × Vec d → ℂ, Measurable U ∧
      (∀ s, (fun x => U (s, x)) =ᵐ[volume] Pdag s.toNNReal g) ∧
      ∀ (t : ℝ≥0) (K : Set (Vec d)), volume K ≠ ⊤ →
        ∀ᵐ x ∂volume.restrict K,
          IntegrableOn (fun s => U (s, x)) (Icc (0 : ℝ) (t : ℝ)) ∧
          f x + (∫ s in (0 : ℝ)..(t : ℝ), U (s, x)) = (Pdag t f) x := by
  obtain ⟨U, hU, heU⟩ := c8_joint_l2_representative
    (((hP.2.2.1 g).comp continuous_real_toNNReal).stronglyMeasurable)
  refine ⟨U, hU, heU, ?_⟩
  let p := fun t : ℝ≥0 => (Pdag t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) hP.1
  have hpm : ∀ s t, p (s + t) = (p s).comp (p t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro f
    exact congrArg (fun A => A f) (hP.2.1 s t)
  have hpc : ∀ f, Continuous (fun t => p t f) := hP.2.2.1
  have hgraph : C8TransposeC0Graph p f g := by
    have h := (hP.2.2.2.1 f g).mpr hfg
    simp only [C8TransposeC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.ofReal_inv]
    exact h
  intro t K hK
  have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) (t : ℝ)
  obtain ⟨hint, he⟩ := short_time_coeFn_integral_joint_l2_local hi hU heU K hK
  have hFTC : (∫ s in Icc (0 : ℝ) (t : ℝ), Pdag s.toNNReal g) = Pdag t f - f := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    simpa only [p, ContinuousLinearMap.coe_restrictScalars', Real.toNNReal_coe] using
      hgraph.integral_orbit hp0 hpm hpc t (NNReal.coe_nonneg t)
  rw [hFTC] at he
  filter_upwards [hint.prod_left_ae, he, ae_restrict_of_ae (Lp.coeFn_sub (Pdag t f) f)]
    with x hx he hsub
  refine ⟨hx, ?_⟩
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← he, hsub]
  exact add_sub_cancel _ _

/-- A primitive representative of the actual physical transpose orbit. -/
theorem short_time_physical_transpose_joint_primitive
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ F U : ℝ × Vec d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun x => F (s, x)) =ᵐ[volume] Pdag s.toNNReal f) ∧
      (∀ s, (fun x => U (s, x)) =ᵐ[volume] Pdag s.toNNReal g) ∧
      ∀ s x, F (s, x) = f x + ∫ r in Icc (0 : ℝ) s, U (r, x) := by
  obtain ⟨U, hU, heU, hsample⟩ := c8_physical_transpose_generator_primitive hP hfg
  let F : ℝ × Vec d → ℂ := fun p => f p.2 + ∫ r in Icc (0 : ℝ) p.1, U (r, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hU 0)
  refine ⟨F, U, hF, hU, ?_, heU, fun _ _ => rfl⟩
  intro s
  by_cases hs : 0 ≤ s
  · have he : ∀ᵐ x ∂(volume : Measure (Vec d)),
        f x + (∫ r in (0 : ℝ)..s, U (r, x)) = (Pdag s.toNNReal f) x := by
      have he' : ∀ᵐ x ∂(volume : Measure (Vec d)).restrict
          (⋃ n, spanningSets (volume : Measure (Vec d)) n),
          f x + (∫ r in (0 : ℝ)..s, U (r, x)) = (Pdag s.toNNReal f) x := by
        apply (ae_restrict_iUnion_iff _ _).mpr
        intro n
        filter_upwards [hsample s.toNNReal (spanningSets volume n)
          (measure_spanningSets_lt_top volume n).ne] with x hx
        simpa only [Real.coe_toNNReal _ hs] using hx.2
      simpa only [iUnion_spanningSets, Measure.restrict_univ] using he'
    filter_upwards [he] with x hx
    simpa only [F, intervalIntegral.integral_of_le hs, ← integral_Icc_eq_integral_Ioc] using hx
  · have hs0 : s.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_ge hs)
    have hI : Icc (0 : ℝ) s = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hs)
    exact ae_of_all _ fun x => by simp [F, hI, hs0, hP.1]

private theorem c8_short_time_gaussian_time_integrable {d : ℕ} {L T : ℝ}
    (v : ℝ × Vec d → ℂ) (hv : Measurable v)
    (hv2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * v p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume)) :
    ∀ᵐ x ∂volume, IntegrableOn (fun s => v (s, x)) (Icc (0 : ℝ) T) := by
  filter_upwards [hv2.norm.integrable_sq.prod_left_ae] with x hx
  have hm : MemLp (fun s => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * v (s, x)) 2
      (volume.restrict (Icc (0 : ℝ) T)) :=
    (memLp_two_iff_integrable_sq_norm
      ((measurable_const.mul (hv.comp (measurable_id.prodMk measurable_const))).aestronglyMeasurable)).mpr hx
  have he : (Real.exp (-euclideanSq x / (4 * L)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.exp_pos _))
  have hm' := hm.const_mul (Real.exp (-euclideanSq x / (4 * L)) : ℂ)⁻¹
  have hi := hm'.integrable (by norm_num)
  simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ he, one_mul] using hi

private theorem c8_short_time_integrable_sq_joint_l2 {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SFinite μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun ω => U (t, ω)) =ᵐ[μ] u t) :
    Integrable (fun p => ‖U p‖ ^ 2) (ν.prod μ) := by
  apply (integrable_prod_iff (hU.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).norm.integrable_sq).congr
    ((heq t).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖ ^ 2) h)), ?_⟩
  apply hu.congr
  filter_upwards with t
  have hn : ‖u t‖ ^ 2 = ∫ ω, ‖(u t) ω‖ ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_congr_ae
  filter_upwards [heq t] with ω hω
  simp only [hω, Real.norm_eq_abs]
  exact (abs_of_nonneg (sq_nonneg ‖(u t) ω‖)).symm

private theorem c8_short_time_gaussian_mul_memLp {d : ℕ} {r : ℝ} (hr : 0 < r)
    {μ : Measure (ℝ × Vec d)} {u : ℝ × Vec d → ℂ}
    (hu : Measurable u) (hu2 : MemLp u 2 μ) :
    MemLp (fun p => (Real.exp (-euclideanSq p.2 / r) : ℂ) * u p) 2 μ := by
  have hq : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  apply hu2.of_le ((Complex.measurable_ofReal.comp
    (Real.continuous_exp.comp ((hq.comp continuous_snd).neg.div_const r)).measurable).mul
      hu).aestronglyMeasurable
  filter_upwards with p
  change ‖(Real.exp (-euclideanSq p.2 / r) : ℂ) * u p‖ ≤ ‖u p‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (by
      apply neg_nonpos.mpr
      change 0 ≤ ∑ j : Fin d, p.2 j * p.2 j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _) hr.le)

private theorem c8_short_time_gaussian_spatial_mul_memLp {d : ℕ} {r : ℝ} (hr : 0 < r)
    {u : Vec d → ℂ} (hu : Measurable u) (hu2 : MemLp u 2 volume) :
    MemLp (fun x => (Real.exp (-euclideanSq x / r) : ℂ) * u x) 2 volume := by
  have hq : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  apply hu2.of_le ((Complex.measurable_ofReal.comp
    (Real.continuous_exp.comp (hq.neg.div_const r)).measurable).mul hu).aestronglyMeasurable
  filter_upwards with x
  change ‖(Real.exp (-euclideanSq x / r) : ℂ) * u x‖ ≤ ‖u x‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_of_le_one_left (norm_nonneg _)
  apply Real.exp_le_one_iff.mpr
  apply div_nonpos_of_nonpos_of_nonneg _ hr.le
  apply neg_nonpos.mpr
  change 0 ≤ ∑ j : Fin d, x j * x j
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- Damped moving Gaussian energy for the actual stationary and physical
transpose orbits, with their literal initial and final traces. -/
theorem short_time_stationary_physical_transpose_damped_gaussian_energy
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ (a : Vec d → Mat d)
          (Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexTransposeSemigroup a i ζ Pr Prdag →
        ∀ (fr gr : Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexTransposeGeneratorPair a i ζ fr gr →
        ∃ V Z : ℝ × Vec d → ℂ, Measurable V ∧ Measurable Z ∧
          (∀ s, (fun x => V (s, x)) =ᵐ[volume] Prdag s.toNNReal fr) ∧
          (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Prdag s.toNNReal gr) ∧
          ∀ L : ℝ, 0 < L → ∀ γ : ℝ, 0 ≤ γ →
          let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
          let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω) - Z p
          let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
          let W : ℝ × Vec d → ℝ := fun p =>
            -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
          (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
            (η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
              γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) =
            Real.exp (-γ * (t : ℝ)) * (∫ x, η (t, x) ^ 2 * ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) -
            (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) -
            ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
              (W (s, x) * ‖X (s, x)‖ ^ 2) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_transpose_joint_primitive hP hPdag hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  intro t ht
  have hFi := c8_short_time_integrable_sq_joint_l2
    (μ := reducedLaw Q) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPdag.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hF heF
  have hUi := c8_short_time_integrable_sq_joint_l2
    (μ := reducedLaw Q) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hU heU
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hFi
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg U hU hUi
  have heT := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hF.comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (Pdag t f)).measurable
    (by
      filter_upwards [heF (t : ℝ)] with ω hω
      simpa only [Function.comp_apply, id_eq, Real.toNNReal_coe] using hω)
  filter_upwards [hFG, hUG, heT,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (Pdag t f)] with ω hFω hUω heω hfω htω
  simp only [Function.comp_apply, id_eq] at heω
  intro a Pr Prdag hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, hprimR⟩ := short_time_physical_transpose_joint_primitive hPr hfr
  refine ⟨V, Z, hV, hZ, heV, heZ, ?_⟩
  intro L hL γ hγ X Y η W
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := (hF.comp hshift).sub hV
  have hY : Measurable Y := (hU.comp hshift).sub hZ
  have hVi := c8_short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hV heV
  have hZi := c8_short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hZ heZ
  have hV2 := c8_short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hV
    ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVi)
  have hZ2 := c8_short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hZ
    ((memLp_two_iff_integrable_sq_norm hZ.aestronglyMeasurable).mpr hZi)
  have hX2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * X p) 2
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod volume) := by
    apply ((hFω (4 * L) (by positivity)).sub hV2).ae_eq
    filter_upwards with p
    change (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * F (p.1, translate p.2 ω) -
      (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * V p = _
    exact (mul_sub _ _ _).symm
  have hY2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * Y p) 2
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod volume) := by
    apply ((hUω (4 * L) (by positivity)).sub hZ2).ae_eq
    filter_upwards with p
    change (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * U (p.1, translate p.2 ω) -
      (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * Z p = _
    exact (mul_sub _ _ _).symm
  have hF0 (x : Vec d) : F (0, translate x ω) = f (translate x ω) := by
    simpa using hprim 0 (translate x ω)
  have hV0 (x : Vec d) : V (0, x) = fr x := by simpa using hprimR 0 x
  have hX0 (x : Vec d) : X (0, x) = f (translate x ω) - fr x := by
    simp only [X, hF0, hV0]
  have hends : ∀ s ∈ ({0, (t : ℝ)} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * X (s, x)) 2 volume := by
    intro s hs
    have hVs := c8_short_time_gaussian_spatial_mul_memLp (r := 4 * L) (by positivity)
      (hV.comp (measurable_const.prodMk measurable_id))
      ((Lp.memLp (Prdag s.toNNReal fr)).ae_eq (heV s).symm)
    have hFs : MemLp (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) *
        F (s, translate x ω)) 2 volume := by
      rcases hs with hs | hs
      · subst s
        simpa only [hF0] using hfω (4 * L) (by positivity)
      · have hs' : s = (t : ℝ) := hs
        subst s
        apply (htω (4 * L) (by positivity)).ae_eq
        filter_upwards [heω] with x hx
        rw [← hx]
    apply (hFs.sub hVs).ae_eq
    filter_upwards with x
    change (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * F (s, translate x ω) -
      (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * V (s, x) = _
    exact (mul_sub _ _ _).symm
  have hsample : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => Y (s, x)) volume 0 (t : ℝ) ∧
      ∀ s ∈ Icc (0 : ℝ) (t : ℝ), X (s, x) = X (0, x) + ∫ r in (0 : ℝ)..s, Y (r, x) := by
    filter_upwards [c8_short_time_gaussian_time_integrable
      (fun p => U (p.1, translate p.2 ω)) (hU.comp hshift) (hUω (4 * L) (by positivity)),
      c8_short_time_gaussian_time_integrable Z hZ hZ2] with x hx hz
    have hy : IntegrableOn (fun s => Y (s, x)) (Icc (0 : ℝ) (t : ℝ)) := hx.sub hz
    refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg).mpr hy, ?_⟩
    intro s hs
    rw [hX0, intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    change F (s, translate x ω) - V (s, x) = _
    rw [hprim, hprimR, integral_sub
      (hx.mono_set (Icc_subset_Icc le_rfl hs.2)) (hz.mono_set (Icc_subset_Icc le_rfl hs.2))]
    ring
  have he := short_time_damped_moving_gaussian_primitive_energy hL t.coe_nonneg ht γ hγ X Y hX hY
    hX2 hY2 hends hsample
  have hfinal : (∫ x, η (t, x) ^ 2 * ‖X (t, x)‖ ^ 2) =
      (∫ x, η (t, x) ^ 2 * ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [heω, heV (t : ℝ)] with x hx hv
    change η (t, x) ^ 2 * ‖F ((t : ℝ), translate x ω) - V ((t : ℝ), x)‖ ^ 2 = _
    rw [hx, hv, Real.toNNReal_coe]
  change (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
    (η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
      γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) =
    Real.exp (-γ * (t : ℝ)) * (∫ x, η (t, x) ^ 2 * ‖X (t, x)‖ ^ 2) -
    (∫ x, η (0, x) ^ 2 * ‖X (0, x)‖ ^ 2) -
    ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
      (W (s, x) * ‖X (s, x)‖ ^ 2) at he
  simpa only [hfinal, hX0] using he



private theorem c8_residual_divergence_const_mul {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → Vec d} {h : Vec d → ℝ} (hF : HasWeakDivergence U F h) (c : ℝ) :
    HasWeakDivergence U (fun x => c • F x) (fun x => c * h x) := by
  refine ⟨fun j x hx => (hF.1 j x hx).smul c,
    fun x hx => (hF.2.1 x hx).smul c, ?_⟩
  intro ψ hψ
  have hdot (x : Vec d) : dot (c • F x) (gradient ψ x) = c * dot (F x) (gradient ψ x) := by
    simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  simp only [hdot, mul_assoc, integral_const_mul]
  rw [(hF.2.2 ψ hψ), mul_neg]

private theorem c8_residual_gaussian_half {d : ℕ} {s : ℝ} (hs : 0 < s)
    (f : Vec d → ℂ)
    (hf : MemLp (fun x => (Real.exp (-euclideanSq x / (2*s)) : ℂ) * f x) 2 volume) :
    MemLp (fun x => (Real.exp (-euclideanSq x / s) : ℂ) * f x) 2 volume := by
  have hb : MemLp (fun x : Vec d => (Real.exp (-euclideanSq x / (2*s)) : ℂ))
      ∞ volume := by
    have hc : Continuous (fun x : Vec d => (Real.exp (-euclideanSq x / (2*s)) : ℂ)) := by
      unfold euclideanSq dot
      fun_prop
    apply memLp_top_of_bound hc.aestronglyMeasurable 1
    apply ae_of_all
    intro x
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg
    · apply neg_nonpos.mpr
      change 0 ≤ ∑ j : Fin d, x j * x j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)
    · positivity
  convert hb.fun_mul (r := 2) hf using 1
  funext x
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- Moving Gaussian coercivity for the conservative transpose residual.
The drift is included in the flux and bounded by ellipticity; it requires
neither a scalar drift derivative nor an unweighted spatial L2 assumption. -/
theorem short_time_transpose_residual_gaussian_energy
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (u q : Vec d → ℂ) (G F : Fin d → Vec d → ℂ)
    (hre : ∀ j, HasWeakPartialDerivative univ j (fun x => (u x).re)
      (fun x => (G j x).re))
    (him : ∀ j, HasWeakPartialDerivative univ j (fun x => (u x).im)
      (fun x => (G j x).im))
    (hdivre : HasWeakDivergence univ
      (fun x j => ((∑ k, (a x j k : ℂ) * G k x) -
        2 * ζ * (a x j i : ℂ) * u x + 2 * F j x).re) (fun x => (2 * q x).re))
    (hdivim : HasWeakDivergence univ
      (fun x j => ((∑ k, (a x j k : ℂ) * G k x) -
        2 * ζ * (a x j i : ℂ) * u x + 2 * F j x).im) (fun x => (2 * q x).im))
    {L r : ℝ} (hΛ : 0 < Λ) (hL : 64 * Λ ^ 3 ≤ L) (hr : 0 < r)
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * u x) 2 volume)
    (hq : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * q x) 2 volume)
    (hG : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * G j x) 2 volume)
    (hF : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * F j x) 2 volume) :
    let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
    let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
    Integrable (fun x => η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      2 * (∫ x, q x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) +
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ≤
          (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) *
            (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
          (2 * (4 * Λ + 16 / L)) * (∫ x, η x ^ 2 * ∑ j, ‖F j x‖ ^ 2) := by
  classical
  intro η W
  have half_flux (x : Vec d) (j : Fin d) :
      (1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) -
        ζ * (a x j i : ℂ) * u x + F j x =
      (1/2 : ℂ) * ((∑ k, (a x j k : ℂ) * G k x) -
        2 * ζ * (a x j i : ℂ) * u x + 2 * F j x) := by ring
  have hdivre : HasWeakDivergence univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) -
        ζ * (a x j i : ℂ) * u x + F j x).re) (fun x => (q x).re) := by
    convert c8_residual_divergence_const_mul hdivre (1/2) using 1
    · funext x j
      rw [half_flux]
      norm_num [Pi.smul_apply, smul_eq_mul, Complex.mul_re]
    · funext x
      norm_num [Complex.mul_re]
      ring
  have hdivim : HasWeakDivergence univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) -
        ζ * (a x j i : ℂ) * u x + F j x).im) (fun x => (q x).im) := by
    convert c8_residual_divergence_const_mul hdivim (1/2) using 1
    · funext x j
      rw [half_flux]
      norm_num [Pi.smul_apply, smul_eq_mul, Complex.mul_im]
    · funext x
      norm_num [Complex.mul_im]
      ring
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let R : Fin d → Vec d → ℂ := fun j x => ζ * (a x j i : ℂ) * u x - F j x
  have hR (j : Fin d) : MemLp
      (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * R j x) 2 volume := by
    convert (((ha j i).fun_mul (r := 2) hu).const_mul ζ).sub (hF j) using 1
    funext x
    dsimp only [R, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hflux (x : Vec d) (j : Fin d) :
      (1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x =
        (1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) -
          ζ * (a x j i : ℂ) * u x + F j x := by
    dsimp only [R]
    ring
  have hre' : HasWeakDivergence univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).re)
      (fun x => (q x - (0 : ℂ) * (∑ j, (a x j i : ℂ) * G j x)).re) := by
    simpa only [hflux, zero_mul, sub_zero] using hdivre
  have him' : HasWeakDivergence univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).im)
      (fun x => (q x - (0 : ℂ) * (∑ j, (a x j i : ℂ) * G j x)).im) := by
    simpa only [hflux, zero_mul, sub_zero] using hdivim
  obtain ⟨hGI, hWI, he⟩ := physical_locally_h1_forced_gaussian_energy
    a i 0 ha hA u q G R hre him hre' him' hΛ hL hr hu hq hG hR
  have shrink (f : Vec d → ℂ)
      (hf : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * f x) 2 volume) :
      MemLp (fun x => (η x : ℂ) * f x) 2 volume := by
    apply c8_residual_gaussian_half (mul_pos hLp hr) f
    apply c8_residual_gaussian_half (by positivity : 0 < 2*(L*r)) f
    convert hf using 1
    funext x
    congr 2
    congr 1
    ring
  have square (f : Vec d → ℂ)
      (hf : MemLp (fun x => (η x : ℂ) * f x) 2 volume) :
      Integrable (fun x => η x ^ 2 * ‖f x‖ ^ 2) := by
    convert hf.norm.integrable_sq using 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hRI : Integrable (fun x => η x ^ 2 * ∑ j, ‖R j x‖ ^ 2) := by
    simpa only [Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun j _ => square (R j) (shrink _ (hR j)))
  have hFI : Integrable (fun x => η x ^ 2 * ∑ j, ‖F j x‖ ^ 2) := by
    simpa only [Finset.mul_sum] using
      integrable_finsetSum Finset.univ (fun j _ => square (F j) (shrink _ (hF j)))
  have hbound : (∫ x, η x ^ 2 * ∑ j, ‖R j x‖ ^ 2) ≤
      (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
        2 * (∫ x, η x ^ 2 * ∑ j, ‖F j x‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add ((square u (shrink u hu)).const_mul _) (hFI.const_mul _)]
    apply integral_mono_ae hRI
      (((square u (shrink u hu)).const_mul _).add (hFI.const_mul _))
    filter_upwards [hA] with x hx
    have hj (j : Fin d) : ‖R j x‖ ^ 2 ≤
        2 * Λ ^ 2 * ‖ζ‖ ^ 2 * ‖u x‖ ^ 2 + 2 * ‖F j x‖ ^ 2 := by
      have hb : ‖ζ * (a x j i : ℂ) * u x‖ ≤ ‖ζ‖ * Λ * ‖u x‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hx.entry_abs_le j i) (norm_nonneg ζ)) (norm_nonneg _)
      have hs := norm_sub_le (ζ * (a x j i : ℂ) * u x) (F j x)
      change ‖R j x‖ ≤ _ at hs
      have ht : ‖R j x‖ ≤ ‖ζ‖ * Λ * ‖u x‖ + ‖F j x‖ :=
        hs.trans (add_le_add hb (le_refl _))
      nlinarith only [sq_nonneg (‖ζ‖ * Λ * ‖u x‖ - ‖F j x‖),
        mul_self_le_mul_self (norm_nonneg (R j x)) ht]
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hw := mul_le_mul_of_nonneg_left hsum (sq_nonneg (η x))
    dsimp only [Pi.add_apply]
    nlinarith only [hw]
  have hm := mul_le_mul_of_nonneg_left hbound
    (show 0 ≤ 4 * Λ + 16 / L by positivity)
  simp only [norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero, zero_mul, add_zero] at he
  refine ⟨hGI, hWI, ?_⟩
  change _ ≤ _ at he
  nlinarith only [he, hm]


/-- The retained conservative residual uses the horizon-independent actual
transpose gradient. Its time L2 bound and its spatial equation therefore
refer to the same gradient, rather than unrelated choices at each time. -/
theorem short_time_transpose_orbit_retained_residual
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (t : ℝ≥0) :
    MemLp (complexTransposeGradientOrbit Q Pdag f) 2
      (volume.restrict (Ioc (0 : ℝ) t)) ∧
    ∀ s : ℝ, 0 < s →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (Pdag s.toNNReal f) (complexTransposeGradientOrbit Q Pdag f s) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ b : Vec d → Mat d,
        (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
        ∀ (v p : Lp ℂ 2 (volume : Measure (Vec d)))
          (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalH1Graph volume (Or.inl rfl) v K →
          IsPhysicalComplexTransposeGeneratorPair b i ζ v p →
        let F := fun x j => (1 / 2 : ℂ) *
          (∑ k, ((ω.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
            ζ * ((ω.1 x j i - b x j i : ℝ) : ℂ) * v x
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
          (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
            ((complexTransposeGradientOrbit Q Pdag f s) k (translate x ω) - K k x)) -
            2 * ζ * (ω.1 x j i : ℂ) * ((Pdag s.toNNReal f) (translate x ω) - v x) +
              2 * F x j))
          (fun x => L (2 * ((Pdag s.toNNReal g) (translate x ω) - p x))) := by
  refine ⟨(hPdag.gradientOrbit_horizon_energy hP f t).1, ?_⟩
  intro s hs
  obtain ⟨H, hH, hevent⟩ := short_time_transpose_generator_retained_residual
    hd Q i ζ (Pdag s.toNNReal f) (Pdag s.toNNReal g)
    (hPdag.map_generator hP hfg s.toNNReal)
  have heq : complexTransposeGradientOrbit Q Pdag f s = WithLp.toLp 2 H :=
    complexTransposeGradientOrbit_eq hs hH
  constructor
  · simpa only [heq] using hH
  · simpa only [heq] using hevent

private theorem transpose_joint_spatial_local_memLp {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ) {U : ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hUs : ∀ s, MemLp (fun ω => U (s, ω)) 2 Q) :
    ∀ᵐ p ∂ν.prod Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => U (p.1, translate x p.2)) 2 (volume.restrict K) := by
  have hshift : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  let I (n : ℕ) (p : ℝ × FieldPair d) : ℝ≥0∞ :=
    ∫⁻ x in Metric.closedBall (0 : Vec d) (n : ℝ),
      ENNReal.ofReal (‖U (p.1, translate x p.2)‖ ^ 2)
  have hI (n : ℕ) : Measurable (I n) :=
    (hshift.norm.pow_const 2).ennreal_ofReal.lintegral_prod_right'
  have hfinite (n : ℕ) : ∀ᵐ p ∂ν.prod Q, I n p < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt (hI n) measurable_const)).mpr
    exact ae_of_all _ fun s => by
      filter_upwards [ae_complex_function_orbit_memLp_on_all_compacts Q hQ
        (hU.comp (measurable_const.prodMk measurable_id)) (hUs s)] with ω hω
      have hm : Measurable (fun x : Vec d => U (s, translate x ω)) :=
        hU.comp (measurable_const.prodMk
          (Probability.continuous_translate.measurable.comp
            (measurable_id.prodMk measurable_const)))
      have hmem : MemLp (fun x : Vec d => U (s, translate x ω)) 2
          (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) := by
        simpa only [Function.comp_apply, id_eq] using
          hω _ (isCompact_closedBall (0 : Vec d) (n : ℝ))
      exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
        ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hmem).hasFiniteIntegral
  filter_upwards [ae_all_iff.mpr hfinite] with p hp
  intro K hK
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp hK.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hs : K ⊆ Metric.closedBall (0 : Vec d) (n : ℝ) :=
    hR.trans (Metric.closedBall_subset_closedBall hn.le)
  have hm : Measurable (fun x => U (p.1, translate x p.2)) :=
    hshift.comp (measurable_const.prodMk measurable_id)
  have hi : Integrable (fun x => ‖U (p.1, translate x p.2)‖ ^ 2)
      (volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))) :=
    ⟨(hm.norm.pow_const 2).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr (hp n)⟩
  exact ((memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr hi).mono_measure
    (Measure.restrict_mono hs le_rfl)

/-- Joint measurable fluxes with the actual horizontal weak equation admit
one product event before every compact smooth spatial test. This is the
countable-test step needed to apply spatial coercivity to evolving data. -/
private theorem transpose_joint_spatial_divergence_all_tests {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ)
    (F : Fin d → ℝ × FieldPair d → ℂ) (q : ℝ × FieldPair d → ℂ)
    (hF : ∀ j, Measurable (F j)) (hq : Measurable q)
    (hFs : ∀ j s, MemLp (fun ω => F j (s, ω)) 2 Q)
    (hqs : ∀ s, MemLp (fun ω => q (s, ω)) 2 Q)
    (hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 Q) (V : Fin d → Lp ℂ 2 Q),
      HasComplexHorizontalGradient Q hQ v V →
      (∫ ω, ∑ j, F j (s, ω) * V j ω ∂Q) = -(∫ ω, q (s, ω) * v ω ∂Q)) :
    ∀ᵐ p ∂ν.prod Q,
      ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, q (p.1, translate x p.2) * (φ x : ℂ) +
        ∑ j, F j (p.1, translate x p.2) * (coordinateDerivative j φ x : ℂ)) = 0 := by
  have hloc : ∀ᵐ p ∂ν.prod Q, ∀ K : Set (Vec d), IsCompact K →
      MemLp (fun x => q (p.1, translate x p.2)) 2 (volume.restrict K) ∧
      ∀ j, MemLp (fun x => F j (p.1, translate x p.2)) 2 (volume.restrict K) := by
    filter_upwards [transpose_joint_spatial_local_memLp Q hQ ν hq hqs,
      ae_all_iff.mpr (fun j => transpose_joint_spatial_local_memLp Q hQ ν (hF j) (hFs j))]
      with p hp hFp
    exact fun K hK => ⟨hp K hK, fun j => hFp j K hK⟩
  apply ae_all_spatial_tests_of_ae_fixed_test (ν.prod Q)
    (fun p x => q (p.1, translate x p.2))
    (fun p j x => F j (p.1, translate x p.2)) hloc
  intro φ hφ hφc
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun z : (ℝ × FieldPair d) × Vec d => U (z.1.1, translate z.2 z.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hd (j : Fin d) : Measurable (fun x => (coordinateDerivative j φ x : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).measurable)
  have hm : Measurable (fun p : ℝ × FieldPair d =>
      ∫ x, q (p.1, translate x p.2) * (φ x : ℂ) +
        ∑ j, F j (p.1, translate x p.2) * (coordinateDerivative j φ x : ℂ)) :=
    (((hshift hq).mul (Complex.continuous_ofReal.measurable.comp
      (hφ.continuous.measurable.comp measurable_snd))).add
        (Finset.measurable_sum _ fun j _ => (hshift (hF j)).mul ((hd j).comp measurable_snd))).stronglyMeasurable.integral_prod_right'.measurable
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hm measurable_const)).mpr
  filter_upwards [hw] with s hs
  filter_upwards [ae_complex_spatial_divergence_all_tests Q hQ
    (fun j ω => F j (s, ω)) (fun ω => q (s, ω))
    (fun j => (hF j).comp (measurable_const.prodMk measurable_id))
    (hq.comp (measurable_const.prodMk measurable_id))
    (fun j => hFs j s) (hqs s) hs,
    ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      (hq.comp (measurable_const.prodMk measurable_id)) (hqs s),
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts Q hQ
      ((hF j).comp (measurable_const.prodMk measurable_id)) (hFs j s))]
    with ω he hqω hFω
  have hiq := integrable_spatial_mul_test hqω hφ.continuous hφc
  have hiF : Integrable (fun x => ∑ j, F j (s, translate x ω) *
      (coordinateDerivative j φ x : ℂ)) volume :=
    integrable_finsetSum _ fun j _ => integrable_spatial_mul_test (hFω j)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (unitVector j))
  simp only [Function.comp_apply, id_eq] at hiq hiF he
  rw [integral_add hiq hiF, he φ hφ hφc, neg_add_cancel]


/-- Joint representatives of the actual transpose orbit have their canonical spatial gradient on one product event. -/
theorem short_time_joint_transpose_spatial_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (U : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (complexTransposeGradientOrbit Q Pdag f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakGradient Set.univ (fun x => L (U (p.1, translate x p.2)))
        (fun x j => L (D j (p.1, translate x p.2))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hgrad (s : ℝ) (hs : 0 < s) :
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (Pdag s.toNNReal f) (complexTransposeGradientOrbit Q Pdag f s) := by
    obtain ⟨H, hH, _⟩ := hPdag.map_generator hP hfg s.toNNReal
    simpa only [complexTransposeGradientOrbit_eq hs hH] using hH
  have hUs (s : ℝ) : MemLp (fun ω => U (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heU s).symm
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  have hj (j : Fin d) : ∀ᵐ p ∂ν.prod (reducedLaw Q), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakPartialDerivative Set.univ j (fun x => L (U (p.1, translate x p.2)))
        (fun x => L (D j (p.1, translate x p.2))) := by
    let F : Fin d → ℝ × FieldPair d → ℂ := fun k p => if k = j then U p else 0
    have hFm (k : Fin d) : Measurable (F k) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hU
      · exact measurable_const
    have hFs (k : Fin d) (s : ℝ) : MemLp (fun ω => F k (s, ω)) 2 (reducedLaw Q) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hUs s
      · exact MemLp.zero
    have hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V →
        (∫ ω, ∑ k, F k (s, ω) * V k ω ∂reducedLaw Q) =
          -(∫ ω, D j (s, ω) * v ω ∂reducedLaw Q) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
      intro v V hV
      have he := (complexHorizontalDerivatives_integration_by_parts
        (hgrad s hs j) (hV j)).2.2
      have hl : (∫ ω, ∑ k, F k (s, ω) * V k ω ∂reducedLaw Q) =
          ∫ ω, (Pdag s.toNNReal f) ω * V j ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [heU s] with ω hω
        simp [F, hω]
      have hr : (∫ ω, D j (s, ω) * v ω ∂reducedLaw Q) =
          ∫ ω, (complexTransposeGradientOrbit Q Pdag f s) j ω * v ω ∂reducedLaw Q :=
        integral_congr_ae ((heD j s).mono fun ω hω => congrArg (· * v ω) hω)
      rw [hl, hr]
      exact neg_eq_iff_eq_neg.mp he.symm
    have ht := transpose_joint_spatial_divergence_all_tests (reducedLaw Q)
      (reducedLaw_stationary Q) ν F (D j) hFm (hD j) hFs (hDs j) hw
    filter_upwards [ht,
      transpose_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν hU hUs,
      transpose_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν (hD j) (hDs j)]
      with p hp hUp hDp
    intro L
    have hFp (K : Set (Vec d)) (hK : IsCompact K) (k : Fin d) :
        MemLp (fun x => F k (p.1, translate x p.2)) 2 (volume.restrict K) := by
      by_cases hk : k = j <;> simp only [F, hk, ite_true, ite_false]
      · exact hUp K hK
      · exact MemLp.zero
    have hd := short_time_transpose_divergence_of_tests hFp hDp
      (fun φ hφ hφc => eq_neg_of_add_eq_zero_left (by
        exact (integral_add
          (integrable_spatial_mul_test hDp hφ.continuous hφc)
          (integrable_finsetSum _ fun k _ => integrable_spatial_mul_test (fun K hK => hFp K hK k)
            ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
            (hφc.fderiv_apply ℝ (unitVector k)))).symm.trans (hp φ hφ hφc))) L
    refine ⟨?_, hd.2.1, ?_⟩
    · simpa only [F, ite_eq_left rfl] using hd.1 j
    · intro φ hφ
      simpa [F, dot, gradient, apply_ite] using hd.2.2 φ hφ
  filter_upwards [ae_all_iff.mpr hj] with p hp
  exact fun L j => hp j L

/-- Joint L2 representatives have Gaussian-admissible spatial slices on one
product event before every positive Gaussian width. -/
theorem short_time_joint_transpose_spatial_gaussian_memLp {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure ℝ) {U : ℝ × FieldPair d → ℂ}
    (hU : Measurable U) (hUs : ∀ s, MemLp (fun ω => U (s, ω)) 2 Q) :
    ∀ᵐ p ∂ν.prod Q, ∀ r : ℝ, 0 < r →
      MemLp (fun x : Vec d => (Real.exp (-euclideanSq x / r) : ℂ) *
        U (p.1, translate x p.2)) 2 volume := by
  have hweight (r : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / r) : ℂ)) := by
    have hs : Continuous (euclideanSq : Vec d → ℝ) := by
      unfold euclideanSq dot
      fun_prop
    exact (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp (hs.neg.div_const r))).measurable
  have hshift : Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
      U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  let I (n : ℕ) (p : ℝ × FieldPair d) : ℝ≥0∞ := ∫⁻ x,
    ENNReal.ofReal (‖(Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) *
      U (p.1, translate x p.2)‖ ^ 2)
  have hI (n : ℕ) : Measurable (I n) :=
    ((((hweight ((n : ℝ) + 1)).comp measurable_snd).mul hshift).norm.pow_const 2).ennreal_ofReal.lintegral_prod_right'
  have hn (n : ℕ) : ∀ᵐ p ∂ν.prod Q, I n p < ∞ := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt (hI n) measurable_const)).mpr
    exact ae_of_all _ fun s => by
      let v := (hUs s).toLp (fun ω => U (s, ω))
      have hm : Measurable (fun ω => U (s, ω)) :=
        hU.comp (measurable_const.prodMk measurable_id)
      filter_upwards [ae_stationary_spatial_orbit_gaussian_memLp d hd Q hQ v,
        ae_spatial_complex_orbit_congr Q hQ (Lp.stronglyMeasurable v).measurable hm
          (hUs s).coeFn_toLp] with ω hg he
      have hmsp : Measurable (fun x : Vec d =>
          (Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * U (s, translate x ω)) :=
        (hweight _).mul (hm.comp (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const)))
      have hmem := (hg ((n : ℝ) + 1) (by positivity)).ae_eq
        (he.mono fun x hx => congrArg ((Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * ·) hx)
      exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mp
        ((memLp_two_iff_integrable_sq_norm hmsp.aestronglyMeasurable).mp hmem).hasFiniteIntegral
  filter_upwards [ae_all_iff.mpr hn] with p hp
  have hm (r : ℝ) : Measurable (fun x : Vec d =>
      (Real.exp (-euclideanSq x / r) : ℂ) * U (p.1, translate x p.2)) :=
    (hweight r).mul (hshift.comp (measurable_const.prodMk measurable_id))
  have hmem (n : ℕ) : MemLp (fun x : Vec d =>
      (Real.exp (-euclideanSq x / ((n : ℝ) + 1)) : ℂ) * U (p.1, translate x p.2)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm (hm _).aestronglyMeasurable).mpr
      ⟨((hm _).norm.pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => sq_nonneg _)).mpr (hp n)⟩
  intro r hr
  obtain ⟨n, hn⟩ := exists_nat_gt r
  apply (hmem n).mono (hm r).aestronglyMeasurable
  refine ae_of_all _ fun x => ?_
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hh : euclideanSq x / ((n : ℝ) + 1) ≤ euclideanSq x / r :=
    div_le_div_of_nonneg_left (euclideanSq_nonneg_coords x) hr (by linarith)
  simpa only [neg_div] using neg_le_neg hh


/-- The full conservative transpose flux holds for joint orbit representatives
on one product event before all real projections. -/
theorem short_time_joint_transpose_spatial_divergence
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (U V : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hV : Measurable V) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (complexTransposeGradientOrbit Q Pdag f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
        (fun x j => L ((∑ k, (p.2.1 x j k : ℂ) * D k (p.1, translate x p.2)) -
          2 * ζ * (p.2.1 x j i : ℂ) * U (p.1, translate x p.2)))
        (fun x => L (2 * V (p.1, translate x p.2))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  let F : Fin d → ℝ × FieldPair d → ℂ := fun j p =>
    (∑ k, (p.2.1 0 j k : ℂ) * D k p) - 2 * ζ * (p.2.1 0 j i : ℂ) * U p
  let q : ℝ × FieldPair d → ℂ := fun p => 2 * V p
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) :=
    (Finset.measurable_sum _ fun k _ => ((hm j k).comp measurable_snd).mul (hD k)).sub
      ((measurable_const.mul ((hm j i).comp measurable_snd)).mul hU)
  have hqm : Measurable q := measurable_const.mul hV
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  have hUs (s : ℝ) : MemLp (fun ω => U (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heU s).symm
  have hFs (j : Fin d) (s : ℝ) : MemLp (fun ω => F j (s, ω)) 2 (reducedLaw Q) := by
    have hsum : MemLp (fun ω => ∑ k, (ω.1 0 j k : ℂ) * D k (s, ω)) 2
        (reducedLaw Q) := memLp_finsetSum _ fun k _ =>
      (memLp_reduced_coefficient_complex Q j k).fun_mul (hDs k s)
    have hprod : MemLp (fun ω => (ω.1 0 j i : ℂ) * U (s, ω)) 2 (reducedLaw Q) :=
      (memLp_reduced_coefficient_complex Q j i).fun_mul (hUs s)
    simpa only [F, mul_assoc] using! hsum.sub (hprod.const_mul (2 * ζ))
  have hqs (s : ℝ) : MemLp (fun ω => q (s, ω)) 2 (reducedLaw Q) :=
    ((Lp.memLp _).ae_eq (heV s).symm).const_mul 2
  have hw : ∀ᵐ s ∂ν, ∀ (v : Lp ℂ 2 (reducedLaw Q)) (J : Fin d → Lp ℂ 2 (reducedLaw Q)),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v J →
      (∫ ω, ∑ j, F j (s, ω) * J j ω ∂reducedLaw Q) =
        -(∫ ω, q (s, ω) * v ω ∂reducedLaw Q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    intro v J hJ
    have hpair := hPdag.map_generator hP hfg s.toNNReal
    obtain ⟨H, hH, _⟩ := hPdag.map_generator hP hfg s.toNNReal
    have hgrad : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (Pdag s.toNNReal f) (complexTransposeGradientOrbit Q Pdag f s) := by
      simpa only [complexTransposeGradientOrbit_eq hs hH] using hH
    have he := hpair.horizontal_flux hgrad v J hJ
    have hl : (∫ ω, ∑ j, F j (s, ω) * J j ω ∂reducedLaw Q) =
        ∫ ω, ∑ j, ((∑ k, (ω.1 0 j k : ℂ) *
          (complexTransposeGradientOrbit Q Pdag f s) k ω) -
          2 * ζ * (ω.1 0 j i : ℂ) * (Pdag s.toNNReal f) ω) * J j ω ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [heU s, ae_all_iff.mpr (fun k => heD k s)] with ω hu hd
      simp only [F, hu, hd]
    have hr : (∫ ω, q (s, ω) * v ω ∂reducedLaw Q) =
        ∫ ω, (2 : ℂ) * (Pdag s.toNNReal g) ω * v ω ∂reducedLaw Q :=
      integral_congr_ae ((heV s).mono fun ω hω => by simp only [q, hω])
    rw [hl, hr]
    exact he
  have ht := transpose_joint_spatial_divergence_all_tests (reducedLaw Q)
    (reducedLaw_stationary Q) ν F q hFm hqm hFs hqs hw
  filter_upwards [ht,
    transpose_joint_spatial_local_memLp (reducedLaw Q) (reducedLaw_stationary Q) ν hqm hqs,
    ae_all_iff.mpr (fun j => transpose_joint_spatial_local_memLp (reducedLaw Q)
      (reducedLaw_stationary Q) ν (hFm j) (hFs j))] with p hp hqp hFp
  intro L
  have he := short_time_transpose_divergence_of_tests (fun K hK j => hFp j K hK) hqp
    (fun φ hφ hφc => eq_neg_of_add_eq_zero_left (by
      exact (integral_add
        (integrable_spatial_mul_test hqp hφ.continuous hφc)
        (integrable_finsetSum _ fun j _ => integrable_spatial_mul_test (fun K hK => hFp j K hK)
          ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hφc.fderiv_apply ℝ (unitVector j)))).symm.trans (hp φ hφ hφc))) L
  simpa only [F, q, translate_matrix, add_zero] using he

/-- Actual-minus-physical transpose residual on a common product event,
selected before every bounded retained coefficient and every physical graph. -/
theorem short_time_joint_transpose_retained_residual
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (U V : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hV : Measurable V) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (complexTransposeGradientOrbit Q Pdag f s) j) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      ∀ (v q : Lp ℂ 2 (volume : Measure (Vec d)))
        (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalH1Graph volume (Or.inl rfl) v K →
        IsPhysicalComplexTransposeGeneratorPair b i ζ v q →
      let F := fun x j => (1 / 2 : ℂ) *
        (∑ k, ((p.2.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
          ζ * ((p.2.1 x j i - b x j i : ℝ) : ℂ) * v x
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
        (fun x j => L ((∑ k, (p.2.1 x j k : ℂ) *
          (D k (p.1, translate x p.2) - K k x)) -
          2 * ζ * (p.2.1 x j i : ℂ) * (U (p.1, translate x p.2) - v x) +
            2 * F x j))
        (fun x => L (2 * (V (p.1, translate x p.2) - q x))) := by
  filter_upwards [short_time_joint_transpose_spatial_divergence Q hP hPdag
    f g hfg U V D hU hV hD heU heV heD] with p hp
  intro b hb v q K hK hvq
  exact short_time_transpose_residual_divergence p.2.1 b i ζ
    (fun x => U (p.1, translate x p.2)) v
    (fun x => V (p.1, translate x p.2)) q
    (fun k x => D k (p.1, translate x p.2)) (fun k x => K k x) hp
    (short_time_physical_transpose_generator_divergence b i ζ hb v q K hK hvq)

/-- Full transpose graph data supply measurable joint representatives of the
canonical gradient at every real time, with no representative premise. -/
theorem short_time_transpose_exists_joint_gradient_representative
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      (∀ j, Measurable (D j)) ∧
      ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (complexTransposeGradientOrbit Q Pdag f s) j := by
  classical
  obtain ⟨G, hG, _⟩ := hPdag.existsUnique_continuous_gradient_orbit hP hfg
  let H : Fin d → ℝ → Lp ℂ 2 (reducedLaw Q) :=
    fun j s => if 0 < s then (G s.toNNReal) j else 0
  have hH (j : Fin d) : StronglyMeasurable (H j) := by
    let C : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) →L[ℂ]
        Lp ℂ 2 (reducedLaw Q) := PiLp.proj 2 _ j
    have hc : Continuous (fun s : ℝ => (G s.toNNReal) j) :=
      C.continuous.comp (hG.2.comp continuous_real_toNNReal)
    exact StronglyMeasurable.ite measurableSet_Ioi hc.stronglyMeasurable stronglyMeasurable_const
  have heq (j : Fin d) (s : ℝ) :
      H j s = (complexTransposeGradientOrbit Q Pdag f s) j := by
    by_cases hs : 0 < s
    · simpa only [H, ite_eq_left hs] using congrArg
        (fun z : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) => z j)
        (complexTransposeGradientOrbit_eq hs (hG.1 s.toNNReal)).symm
    · simp [H, complexTransposeGradientOrbit, hs]
  choose D hD heD using fun j => c8_joint_l2_representative (hH j)
  refine ⟨D, hD, ?_⟩
  intro j s
  simpa only [heq j s] using heD j s

/-- Joint transpose representatives satisfy Gaussian coercivity on a common
event before selecting any bounded physical coefficient and full graph datum. -/
theorem short_time_joint_transpose_retained_gaussian_coercivity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (U V : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hV : Measurable V) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (complexTransposeGradientOrbit Q Pdag f s) j) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ))).prod (reducedLaw Q),
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      ∀ v q : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeGeneratorPair b i ζ v q →
      ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let u : Vec d → ℂ := fun x => U (p.1, translate x p.2) - v x
      let J : Fin d → Vec d → ℂ := fun j x => D j (p.1, translate x p.2) - K j x
      let F : Fin d → Vec d → ℂ := fun j x => (1 / 2 : ℂ) *
        (∑ k, ((p.2.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
          ζ * ((p.2.1 x j i - b x j i : ℝ) : ℂ) * v x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      2 * (∫ x, (V (p.1, translate x p.2) - q x) *
        (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) +
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖J j x‖ ^ 2) ≤
          (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) *
            (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
          (2 * (4 * Λ + 16 / L)) * (∫ x, η x ^ 2 * ∑ j, ‖F j x‖ ^ 2) := by
  intro Λ
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hexp : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith)
  have hΛ1 : 1 ≤ Λ := by dsimp only [Λ]; nlinarith
  have hΛ : 0 < Λ := by linarith
  let ν : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hUs (s : ℝ) : MemLp (fun ω => U (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heU s).symm
  have hVs (s : ℝ) : MemLp (fun ω => V (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heV s).symm
  have hDs (j : Fin d) (s : ℝ) : MemLp (fun ω => D j (s, ω)) 2 (reducedLaw Q) :=
    (Lp.memLp _).ae_eq (heD j s).symm
  filter_upwards [short_time_joint_transpose_retained_residual Q hP hPdag f g hfg
    U V D hU hV hD heU heV heD,
    short_time_joint_transpose_spatial_gradient Q hP hPdag f g hfg U D hU hD heU heD,
    Measure.quasiMeasurePreserving_snd.ae (c4_ae_reduced_physical_elliptic Q),
    short_time_joint_transpose_spatial_gaussian_memLp hd (reducedLaw Q)
      (reducedLaw_stationary Q) ν hU hUs,
    short_time_joint_transpose_spatial_gaussian_memLp hd (reducedLaw Q)
      (reducedLaw_stationary Q) ν hV hVs,
    ae_all_iff.mpr (fun j => short_time_joint_transpose_spatial_gaussian_memLp hd
      (reducedLaw Q) (reducedLaw_stationary Q) ν (hD j) (hDs j))]
    with p hres hsp hA hu hv hGrad
  intro b hb v q hvq
  let K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := hvq.choose
  have hK : IsPhysicalH1Graph volume (Or.inl rfl) v K := hvq.choose_spec.1
  have hdiv := hres b hb v q K hK hvq
  have hao (j k : Fin d) : MemLp (fun x => (p.2.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hA (fun j k => p.2.1.continuous.matrix_elem j k) j k
  have had (j k l m : Fin d) : MemLp
      (fun x => ((p.2.1 x j k - b x l m : ℝ) : ℂ)) ∞ volume := by
    simpa only [Complex.ofReal_sub, Pi.sub_def] using (hao j k).sub (hb l m)
  refine ⟨K, hK, fun L r hL hr => ?_⟩
  intro u J F η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / (4 * L * r)) : ℂ)
  have hw : MemLp w ∞ volume := by
    have hc : Continuous w := by dsimp only [w, euclideanSq, dot]; fun_prop
    apply memLp_top_of_bound hc.aestronglyMeasurable 1
    refine ae_of_all _ fun x => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    exact neg_nonpos.mpr (euclideanSq_nonneg_coords x)
  have hwp (v : Lp ℂ 2 (volume : Measure (Vec d))) :
      MemLp (fun x => w x * v x) 2 volume := hw.fun_mul (Lp.memLp v)
  have hwu : MemLp (fun x => w x * u x) 2 volume := by
    simpa only [u, w, mul_sub, Pi.sub_def] using
      (hu (4 * L * r) (by positivity)).sub (hwp v)
  have hwq : MemLp (fun x => w x * (V (p.1, translate x p.2) - q x)) 2 volume := by
    simpa only [w, mul_sub, Pi.sub_def] using
      (hv (4 * L * r) (by positivity)).sub (hwp q)
  have hwJ (j : Fin d) : MemLp (fun x => w x * J j x) 2 volume := by
    simpa only [J, w, mul_sub, Pi.sub_def] using
      (hGrad j (4 * L * r) (by positivity)).sub (hwp (K j))
  have hwF (j : Fin d) : MemLp (fun x => w x * F j x) 2 volume := by
    have hs : MemLp (fun x => ∑ k, ((p.2.1 x j k - b x k j : ℝ) : ℂ) *
        (w x * K k x)) 2 volume :=
      memLp_finsetSum _ fun k _ => (had j k k j).fun_mul (hwp (K k))
    have ht : MemLp (fun x => ((p.2.1 x j i - b x j i : ℝ) : ℂ) *
        (w x * v x)) 2 volume := (had j i j i).fun_mul (hwp v)
    convert (hs.const_mul (1 / 2 : ℂ)).sub (ht.const_mul ζ) using 1
    funext x
    simp only [F, mul_sub, Finset.mul_sum, Pi.sub_apply]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · ring
  have hre j : HasWeakPartialDerivative univ j
      (fun x => (u x).re) (fun x => (J j x).re) := by
    simpa only [u, J, Complex.sub_re, Complex.reCLM_apply] using
      Correctors.hasWeakPartialDerivative_sub (hsp Complex.reCLM j) (hK.1 j)
  have him j : HasWeakPartialDerivative univ j
      (fun x => (u x).im) (fun x => (J j x).im) := by
    simpa only [u, J, Complex.sub_im, Complex.imCLM_apply] using
      Correctors.hasWeakPartialDerivative_sub (hsp Complex.imCLM j) (hK.2 j)
  have he := short_time_transpose_residual_gaussian_energy p.2.1 i ζ hao
    (ae_of_all _ fun x => s5Elliptic_of_isElliptic hΛ1 hA x)
    u (fun x => V (p.1, translate x p.2) - q x) J F hre him
    (by simpa only [J, F, Complex.reCLM_apply] using hdiv Complex.reCLM)
    (by simpa only [J, F, Complex.imCLM_apply] using hdiv Complex.imCLM)
    hΛ hL hr hwu hwq hwJ hwF
  simpa only [η, W] using he

/-- Damping with a constant uniform over the force ball absorbs the mass term
of the true transpose equation. The environment event precedes physical data. -/
theorem short_time_joint_transpose_retained_damped_gaussian_bound
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f g : Lp ℂ 2 (reducedLaw Q)) (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (U V : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hU : Measurable U) (hV : Measurable V) (hD : ∀ j, Measurable (D j))
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (complexTransposeGradientOrbit Q Pdag f s) j)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ τ ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      ∀ v q : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeGeneratorPair b i ζ v q →
      ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
      ∀ L r s : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let u : Vec d → ℂ := fun x => U (τ, translate x ω) - v x
      let F : Fin d → Vec d → ℂ := fun j x => (1 / 2 : ℂ) *
        (∑ k, ((ω.1 x j k - b x k j : ℝ) : ℂ) * K k x) -
          ζ * ((ω.1 x j i - b x j i : ℝ) : ℂ) * v x
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      Real.exp (-γ * s) * (
        2 * (∫ x, (V (τ, translate x ω) - q x) *
          (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) - γ * (∫ x, η x ^ 2 * ‖u x‖ ^ 2)) ≤
      Real.exp (-γ * s) *
        ((2 * (4 * Λ + 16 / L)) * (∫ x, η x ^ 2 * ∑ j, ‖F j x‖ ^ 2)) := by
  intro Λ γ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hj := short_time_joint_transpose_retained_gaussian_coercivity hd Q hP hPdag
    f g hfg U V D hU hV hD heU heV heD
  have hj' := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hj)
  filter_upwards [hj'] with ω hω
  filter_upwards [hω] with τ hp
  intro b hb v q hvq
  obtain ⟨K, hK, he⟩ := hp b hb v q hvq
  refine ⟨K, hK, ?_⟩
  intro L r s hL hr u F η W
  obtain ⟨_, hW, henergy⟩ := he L r hL hr
  refine ⟨hW, ?_⟩
  have hΛ₀ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hexp : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith)
  have hΛ1 : 1 ≤ Λ := by dsimp only [Λ]; nlinarith
  have hΛ : 0 < Λ := by linarith
  have hΛ3 : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ1
  have hL1 : 1 ≤ L := by linarith
  have hLp : 0 < L := by linarith
  have hdiv : 16 / L ≤ 16 := (div_le_iff₀ hLp).mpr (by linarith)
  have hsq : ‖ζ‖ ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hζ 2
  have hcoef : (4 * Λ + 16 / L) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) ≤ γ := by
    calc
      _ ≤ (4 * Λ + 16) * (2 * d * Λ ^ 2 * ‖ζ‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ ≤ (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hsq (by positivity)) (by positivity)
      _ ≤ γ := by dsimp only [γ]; linarith
  have hm : 0 ≤ ∫ x, η x ^ 2 * ‖u x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hmass := mul_le_mul_of_nonneg_right hcoef hm
  have hgrad : 0 ≤ (Λ⁻¹ / 4) *
      (∫ x, η x ^ 2 * ∑ j, ‖D j (τ, translate x ω) - K j x‖ ^ 2) := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  dsimp only [Prod.swap, u, F, η, W, Λ] at henergy hmass hgrad ⊢
  nlinarith only [henergy, hmass, hgrad]

/-- The full physical transpose generator graph is invariant under its semigroup. -/
theorem short_time_physical_transpose_map_generator
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) (s : ℝ≥0) :
    IsPhysicalComplexTransposeGeneratorPair a i ζ (Pdag s f) (Pdag s g) := by
  apply (hP.2.2.2.1 _ _).mp
  have h := ((Pdag s).continuous.tendsto g).comp ((hP.2.2.2.1 f g).mpr hfg)
  convert h using 1
  ext r
  simp only [Function.comp_apply, map_smul, map_sub]
  have hc : Pdag s (Pdag r f) = Pdag r (Pdag s f) := by
    rw [← ContinuousLinearMap.comp_apply, ← hP.2.1, add_comm,
      hP.2.1, ContinuousLinearMap.comp_apply]
  rw [hc]

/-- The actual physical transpose gradient has a joint measurable representative
whose square is integrable on each compact time interval. -/
theorem short_time_physical_transpose_joint_gradient
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ H : Fin d → ℝ × Vec d → ℂ,
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧ (∀ j, Measurable (H j)) ∧
      (∀ j s, (fun x => H j (s, x)) =ᵐ[volume] G s j) ∧
      ∀ (T : ℝ) j, Integrable (fun p => ‖H j p‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
  classical
  obtain ⟨G, hG, hc⟩ := physical_transpose_generator_orbit_continuous_gradient
    a i ζ ha hΛ hA (fun s => Pdag s.toNNReal f) (fun s => Pdag s.toNNReal g)
    ((hP.2.2.1 f).comp continuous_real_toNNReal)
    ((hP.2.2.1 g).comp continuous_real_toNNReal)
    (fun s => short_time_physical_transpose_map_generator hP hfg s.toNNReal)
  choose H hH heH using fun j => c8_joint_l2_representative (hc j).stronglyMeasurable
  refine ⟨G, H, hG, hc, hH, heH, ?_⟩
  intro T j
  exact c8_short_time_integrable_sq_joint_l2
    (((hc j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc) (hH j) (heH j)

/-- A moving short-time Gaussian is bounded by the fixed wider Gaussian. -/
private theorem c8_joint_moving_gaussian_memLp {d : ℕ} {T L : ℝ}
    (hT : T ≤ 1) (hL : 0 < L) {u : ℝ × Vec d → ℂ} (hu : Measurable u)
    (h2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume)) :
    MemLp (fun p => (Real.exp (-euclideanSq p.2 / (L * (2 - p.1))) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
  apply h2.of_le (by
    apply Measurable.aestronglyMeasurable
    exact (by dsimp only [euclideanSq, dot]; fun_prop :
      Measurable (fun p : ℝ × Vec d =>
        (Real.exp (-euclideanSq p.2 / (L * (2 - p.1))) : ℂ))).mul hu)
  have htime : ∀ᵐ p : ℝ × Vec d ∂((volume.restrict (Icc (0 : ℝ) T)).prod volume),
      p.1 ∈ Icc (0 : ℝ) T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun _ => hs
  filter_upwards [htime] with p hp
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [neg_div, neg_div]
  apply neg_le_neg
  apply (div_le_div_iff₀ (by positivity : 0 < 4 * L)
    (mul_pos hL (by linarith [hp.2] : 0 < 2 - p.1))).mpr
  have hq := euclideanSq_nonneg_coords p.2
  nlinarith [mul_nonneg hq (mul_nonneg hL.le hp.1)]

/-- Quantitative short-time comparison for the actual transpose orbits.
The physical gradient and all forcing integrability are derived from the full
generator graph; the common environment event precedes the physical data. -/
theorem short_time_transpose_integrated_gaussian_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Prdag →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeGeneratorPair b i ζ fr gr →
      ∃ V : ℝ × Vec d → ℂ, ∃ H : Fin d → ℝ × Vec d → ℂ,
        Measurable V ∧ (∀ j, Measurable (H j)) ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Prdag s.toNNReal fr) ∧
        (∀ s, ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalH1Graph volume (Or.inl rfl) (Prdag s.toNNReal fr) G ∧
          ∀ j, (fun x => H j (s, x)) =ᵐ[volume] G j) ∧
      ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
      let RF : Fin d → ℝ × Vec d → ℂ := fun j p => (1 / 2 : ℂ) *
        (∑ k, ((ω.1 p.2 j k - b p.2 k j : ℝ) : ℂ) * H k p) -
          ζ * ((ω.1 p.2 j i - b p.2 j i : ℝ) : ℂ) * V p
      Integrable (fun s => Real.exp (-γ * s) *
        ((2 * (4 * Λ + 16 / L)) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2)))
        (volume.restrict (Icc (0 : ℝ) (t : ℝ))) ∧
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, η (t, x) ^ 2 * ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) ≤
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) +
        ∫ s in Icc (0 : ℝ) (t : ℝ), Real.exp (-γ * s) *
          ((2 * (4 * Λ + 16 / L)) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2)) := by
  intro Λ γ t ht
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, htime⟩ :=
    short_time_stationary_physical_transpose_damped_gaussian_energy hd hP hPdag hfg
  obtain ⟨D, hD, heD⟩ := short_time_transpose_exists_joint_gradient_representative Q hP hPdag f g hfg
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  have hsp := short_time_joint_transpose_retained_damped_gaussian_bound hd Q hP hPdag
    f g hfg F U D hF hU hD heF heU heD B hζ
  have joint (v : Lp ℂ 2 (reducedLaw Q)) (V : ℝ × FieldPair d → ℂ)
      (hV : Measurable V) (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal v) :=
    c8_short_time_integrable_sq_joint_l2 (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
      ((((hPdag.continuous_apply hP v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF (joint f F hF heF)
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg U hU (joint g U hU heU)
  filter_upwards [htime t ht, hsp, hFG, hUG, c4_ae_reduced_physical_elliptic Q]
    with ω hω hspω hFω hUω hAω
  intro b hb hAb Pr Prdag hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, he⟩ := hω b Pr Prdag hPr fr gr hfr
  obtain ⟨G, H, hG, _, hH, heH, hHi⟩ :=
    short_time_physical_transpose_joint_gradient hb hΛ hAb hPr hfr
  refine ⟨V, H, hV, hH, heV, (fun s => ⟨G s, hG s, fun j => heH j s⟩), ?_⟩
  intro L hL η RF
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  specialize he L hLp γ hγ
  let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
  let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω) - Z p
  let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
  let m : ℝ → ℝ := fun s => Real.exp (-γ * s)
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) (t : ℝ))
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := (hF.comp hshift).sub hV
  have hY : Measurable Y := (hU.comp hshift).sub hZ
  have physical (v : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ)
      (hV : Measurable V) (heV : ∀ s, (fun x => V (s, x)) =ᵐ[volume] Prdag s.toNNReal v) :
      MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * V p) 2 (ν.prod volume) := by
    have hVi := c8_short_time_integrable_sq_joint_l2 (ν := ν)
      ((((hPr.2.2.1 v).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
    exact c8_short_time_gaussian_mul_memLp (by positivity) hV
      ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVi)
  have hX2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * X p) 2
      (ν.prod volume) := by
    simpa only [X, mul_sub, Pi.sub_def] using
      (hFω (4 * L) (by positivity)).sub (physical fr V hV heV)
  have hY2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * Y p) 2
      (ν.prod volume) := by
    simpa only [Y, mul_sub, Pi.sub_def] using
      (hUω (4 * L) (by positivity)).sub (physical gr Z hZ heZ)
  have hηX := c8_joint_moving_gaussian_memLp ht hLp hX hX2
  have hηY := c8_joint_moving_gaussian_memLp ht hLp hY hY2
  change MemLp (fun p => (η p : ℂ) * X p) 2 (ν.prod volume) at hηX
  change MemLp (fun p => (η p : ℂ) * Y p) 2 (ν.prod volume) at hηY
  have sqint (u : ℝ × Vec d → ℂ)
      (hu : MemLp (fun p => (η p : ℂ) * u p) 2 (ν.prod volume)) :
      Integrable (fun p => η p ^ 2 * ‖u p‖ ^ 2) (ν.prod volume) := by
    convert hu.norm.integrable_sq using 1
    funext p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hC := sqint X hηX
  have hJ : Integrable (fun p => Y p * (((η p ^ 2 : ℝ) : ℂ) * star (X p))) (ν.prod volume) := by
    convert hηY.integrable_mul hηX.star using 1
    funext p
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  obtain ⟨hA, hW⟩ := short_time_moving_gaussian_spacetime_integrable hLp ht X Y hX hY hX2 hY2
  have hν : ∀ᵐ s ∂ν, s ∈ Icc (0 : ℝ) (t : ℝ) := ae_restrict_mem measurableSet_Icc
  have damp (a : ℝ × Vec d → ℝ) (ha : Integrable a (ν.prod volume)) :
      Integrable (fun p => m p.1 * a p) (ν.prod volume) := by
    apply ha.norm.mono' (((by dsimp only [m]; fun_prop : Measurable
      (fun p : ℝ × Vec d => m p.1)).aestronglyMeasurable).mul ha.aestronglyMeasurable)
    have hp : ∀ᵐ p : ℝ × Vec d ∂ν.prod volume, 0 ≤ p.1 := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_Ici.preimage measurable_fst)).mpr
      filter_upwards [hν] with s hs
      exact ae_of_all _ fun _ => hs.1
    filter_upwards [hp] with p hp
    change ‖m p.1 * a p‖ ≤ ‖a p‖
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hp))
  have ha (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛ hAω
      (fun j k => ω.1.continuous.matrix_elem j k) j k
  have had (j k l n : Fin d) : MemLp
      (fun p : ℝ × Vec d => ((ω.1 p.2 j k - b p.2 l n : ℝ) : ℂ)) ∞ (ν.prod volume) := by
    simpa only [Complex.ofReal_sub, Pi.sub_apply] using ((ha j k).sub (hb l n)).comp_snd ν
  have hηH (j : Fin d) : MemLp (fun p => (η p : ℂ) * H j p) 2 (ν.prod volume) := by
    apply c8_joint_moving_gaussian_memLp ht hLp (hH j)
    exact c8_short_time_gaussian_mul_memLp (by positivity) (hH j)
      ((memLp_two_iff_integrable_sq_norm (hH j).aestronglyMeasurable).mpr (hHi t j))
  have hηV := c8_joint_moving_gaussian_memLp ht hLp hV (physical fr V hV heV)
  have hRF (j : Fin d) : MemLp (fun p => (η p : ℂ) * RF j p) 2 (ν.prod volume) := by
    have hs : MemLp (fun p => ∑ k, ((ω.1 p.2 j k - b p.2 k j : ℝ) : ℂ) *
        ((η p : ℂ) * H k p)) 2 (ν.prod volume) :=
      memLp_finsetSum _ fun k _ => (had j k k j).fun_mul (hηH k)
    have ht : MemLp (fun p => ((ω.1 p.2 j i - b p.2 j i : ℝ) : ℂ) *
        ((η p : ℂ) * V p)) 2 (ν.prod volume) := (had j i j i).fun_mul hηV
    convert (hs.const_mul (1 / 2 : ℂ)).sub (ht.const_mul ζ) using 1
    funext p
    simp only [RF, mul_sub, Finset.mul_sum, Pi.sub_apply]
    congr 1
    · apply Finset.sum_congr rfl
      intro k _
      ring
    · ring
  have hRFi : Integrable (fun p => η p ^ 2 * ∑ j, ‖RF j p‖ ^ 2) (ν.prod volume) := by
    simpa only [Finset.mul_sum] using integrable_finsetSum Finset.univ (fun j _ => sqint _ (hRF j))
  let bound : ℝ → ℝ := fun s => m s *
    ((2 * (4 * Λ + 16 / L)) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2))
  have hbi : Integrable bound ν := by
    simpa only [bound, integral_const_mul] using
      (damp _ (hRFi.const_mul (2 * (4 * Λ + 16 / L)))).integral_prod_left
  refine ⟨hbi, ?_⟩
  let A : ℝ × Vec d → ℝ := fun p => m p.1 *
    (η p ^ 2 * (2 * (star (X p) * Y p).re) - γ * (η p ^ 2 * ‖X p‖ ^ 2))
  let C : ℝ × Vec d → ℝ := fun p => m p.1 * (W p * ‖X p‖ ^ 2)
  have hAi : Integrable A (ν.prod volume) := damp _ (hA.sub (hC.const_mul γ))
  have hCi : Integrable C (ν.prod volume) := damp _ hW
  let scalar : ℝ → ℝ := fun s => (∫ x, A (s, x)) + ∫ x, C (s, x)
  have hai : Integrable scalar ν := hAi.integral_prod_left.add hCi.integral_prod_left
  have hid : (∫ s, scalar s ∂ν) = m t *
      (∫ x, η (t, x) ^ 2 * ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) -
      (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) := by
    rw [integral_add hAi.integral_prod_left hCi.integral_prod_left]
    dsimp only [ν, A, C, m, X, Y, W, η] at he ⊢
    linarith only [he]
  have hspν := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) (t : ℝ) ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hspω
  rw [restrict_Ioc_eq_restrict_Icc] at hspν
  have hle : ∀ᵐ s ∂ν, scalar s ≤ bound s := by
    filter_upwards [hspν, hν, hJ.prod_right_ae, hC.prod_right_ae, hA.prod_right_ae]
      with s hs hsI hJs hCs hAs
    obtain ⟨K, hK, hbs⟩ := hs b hb (Prdag s.toNNReal fr) (Prdag s.toNNReal gr)
      (short_time_physical_transpose_map_generator hPr hfr s.toNNReal)
    have hbs := (hbs L (2 - s) s hL (by linarith [hsI.2])).2
    rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) _ K (G s) hK (hG s)] at hbs
    have hpair : (∫ x, η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re)) =
        2 * (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re := by
      have hr : (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re =
          ∫ x, (Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re :=
        (integral_re hJs).symm
      rw [hr, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        add_zero, sub_zero, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    have hmass := integral_sub hAs (hCs.const_mul γ)
    have hrewrite : scalar s = m s * (
        2 * (∫ x, Y (s, x) * (((η (s, x) ^ 2 : ℝ) : ℂ) * star (X (s, x)))).re +
        (∫ x, W (s, x) * ‖X (s, x)‖ ^ 2) - γ * ∫ x, η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2) := by
      dsimp only [scalar, A, C]
      simp only [integral_const_mul]
      rw [hmass, hpair, integral_const_mul]
      ring
    rw [hrewrite]
    have hp := (heV s).and ((heZ s).and (ae_all_iff.mpr fun j => heH j s))
    convert hbs using 1
    · apply congrArg (fun q : ℝ => m s * q)
      apply congrArg₂ (fun b c : ℝ => b - γ * c)
      · apply congrArg₂ (fun b c : ℝ => b + c)
        · apply congrArg (fun z : ℂ => 2 * z.re)
          apply integral_congr_ae
          filter_upwards [hp] with x hx
          simp only [X, Y, hx.1, hx.2.1, η]
        · apply integral_congr_ae
          filter_upwards [hp] with x hx
          simp only [X, hx.1, W, η]
      · apply integral_congr_ae
        filter_upwards [hp] with x hx
        simp only [X, hx.1, η]
    · apply congrArg (fun q : ℝ => m s * ((2 * (4 * Λ + 16 / L)) * q))
      apply integral_congr_ae
      filter_upwards [hp] with x hx
      simp only [RF, hx.1, hx.2.2, η]
  have hi := integral_mono_ae hai hbi hle
  rw [hid] at hi
  dsimp only [bound, m, ν] at hi ⊢
  linarith only [hi]

/-- The signed physical transpose energy estimate retains generator dissipation. -/
theorem short_time_physical_transpose_signed_energy
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {u g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hug : IsPhysicalComplexTransposeGeneratorPair a i ζ u g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) u G ∧
      (inner ℂ u g).re + (1 / (4 * Λ)) * (∑ j, ‖G j‖ ^ 2) ≤
        ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u‖ ^ 2 := by
  classical
  obtain ⟨G, hG, hweak⟩ := hug
  refine ⟨G, hG, ?_⟩
  let Q : Vec d → ℂ := fun x => ∑ j, ∑ k,
    (a x k j : ℂ) * G k x * star (G j x)
  let F : Vec d → ℂ := fun x => u x * (∑ j, (a x j i : ℂ) * star (G j x))
  have hQi : Integrable Q volume := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro k _
    exact ((ha k j).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (G j)).star
  have hFi : Integrable F volume := by
    have hcol : MemLp (fun x => ∑ j, (a x j i : ℂ) * star (G j x)) 2 volume :=
      memLp_finsetSum _ fun j _ => (ha j i).mul (r := 2) (Lp.memLp (G j)).star
    exact (Lp.memLp u).integrable_mul hcol
  have hN : Integrable (fun x => ∑ j, ‖G j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq
  have hU : Integrable (fun x => ‖u x‖ ^ 2) volume := (Lp.memLp u).norm.integrable_sq
  have hpoint : ∀ᵐ x ∂volume,
      (1 / (4 * Λ)) * (∑ j, ‖G j x‖ ^ 2) ≤
        -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re +
          ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2 := by
    filter_upwards [hA] with x hx
    have hc := s5_coercive hx (fun j => star (G j x))
    have hQ : (∑ j, ∑ k, (a x j k : ℂ) * star (G k x) *
        (starRingEnd ℂ) (star (G j x))) = Q x := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp only [starRingEnd_apply, star_star]
      ring
    rw [hQ] at hc
    simp only [norm_star] at hc
    have hf := physicalForceColumn_young (a x) i Λ Λ hΛ
      (fun j => hx.entry_abs_le j i) (ζ * u x) (fun j => star (G j x))
    have he : ζ * F x = (ζ * u x) * (∑ j, (a x j i : ℂ) * star (G j x)) := by
      dsimp only [F]; ring
    rw [← he] at hf
    simp only [norm_mul, norm_star, mul_pow] at hf
    have hr := Complex.re_le_norm (ζ * F x)
    rw [norm_mul] at hr
    change Λ⁻¹ * (∑ j, ‖G j x‖ ^ 2) ≤ (Q x).re at hc
    have hreal : ((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re =
        -(1 / 2 : ℝ) * (Q x).re + (ζ * F x).re := by simp [Complex.mul_re]
    rw [hreal]
    have hinv : Λ⁻¹ = 4 * (1 / (4 * Λ)) := by field_simp
    rw [hinv] at hc
    nlinarith only [hc, hf, hr]
  have hT : Integrable (fun x => (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) volume :=
    ((hQi.const_mul _).mul_const _).add (hFi.const_mul _)
  have hi := integral_mono_ae (hN.const_mul (1 / (4 * Λ)))
    (hT.re.neg.add (hU.const_mul ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2))) hpoint
  have hNeq : (∫ x, ∑ j, ‖G j x‖ ^ 2) = ∑ j, ‖G j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (G j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (G j)).symm
  have htest := hweak (star u) (fun j => star (G j)) (physicalH1Graph_star u G hG)
  have hQa : (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * (star (G j)) x) = ∫ x, Q x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j))] with x hx
    simp only [Q, hx, Pi.star_apply]
  have hFa : (∫ x, u x * (∑ j, (a x j i : ℂ) * (star (G j)) x)) = ∫ x, F x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (G j))] with x hx
    simp only [F, hx, Pi.star_apply]
  rw [hQa, hFa] at htest
  have hTeq : (∫ x, (1 / 2 : ℂ) * Q x * (-1) + ζ * F x) = ∫ x, g x * (star u) x := by
    rw [integral_add ((hQi.const_mul _).mul_const _) (hFi.const_mul _),
      integral_mul_const, integral_const_mul, integral_const_mul, htest]
    ring
  have hpair : (∫ x, g x * (star u) x) = inner ℂ u g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star u] with x hx
    simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def, mul_comm]
  have hrealint := integral_re hT
  simp only [RCLike.re_eq_complex_re] at hrealint
  simp only [Pi.add_apply, Pi.neg_apply, RCLike.re_eq_complex_re] at hi
  rw [integral_const_mul, hNeq, integral_add (f := fun x => -((1 / 2 : ℂ) * Q x * (-1) + ζ * F x).re)
      (g := fun x => ((d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ‖u x‖ ^ 2)
      hT.re.neg (hU.const_mul _),
    integral_neg, hrealint, hTeq, hpair, integral_const_mul,
    ← physicalL2_norm_sq] at hi
  linarith only [hi]

private theorem C8TransposeC0Graph.hasDerivAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : C8TransposeC0Graph P f g) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => P s.toNNReal f) (P t.toNNReal g) t := by
  have hd := (((hPc g).comp continuous_real_toNNReal).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd' := hd.add_const f
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (eq_add_of_sub_eq (hfg.integral_orbit hP0 hPm hPc s hs.le).symm)

private theorem c8_transpose_time_energy {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (u u' : ℝ → X)
    (hu : ∀ r, 0 ≤ r → HasDerivWithinAt u (u' r) (Ici 0) r)
    (g h : ℝ → ℝ) (hg : Continuous g) (hh : Continuous h)
    (α K t : ℝ) (hα : 0 ≤ α) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hg0 : ∀ r ∈ Icc (0 : ℝ) t, 0 ≤ g r)
    (hh0 : ∀ r ∈ Icc (0 : ℝ) t, 0 ≤ h r)
    (henergy : ∀ r ∈ Icc (0 : ℝ) t,
      inner ℝ (u r) (u' r) + α * g r ≤ K * ‖u r‖ ^ 2 + h r) :
    ‖u t‖ ^ 2 + 2 * α * (∫ r in (0 : ℝ)..t, g r) ≤
      Real.exp (2*K*t) * (‖u 0‖ ^ 2 + 2 * (∫ r in (0 : ℝ)..t, h r)) := by
  let E := fun r : ℝ => ‖u r‖ ^ 2 + 2*α * (∫ v in (0 : ℝ)..r, g v)
  let w := fun r : ℝ => Real.exp (-2*K*r)
  let F := fun r : ℝ => w r * E r - 2 * (∫ v in (0 : ℝ)..r, w v * h v)
  have hw : Continuous w := by fun_prop
  have hwh : Continuous (fun r => w r * h r) := hw.mul hh
  have hE (r : ℝ) (hr : 0 ≤ r) : HasDerivWithinAt E
      (2 * inner ℝ (u r) (u' r) + 2*α*g r) (Ici 0) r := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    exact (hu r hr).norm_sq.add (hi.const_mul _).hasDerivWithinAt
  have hwd (r : ℝ) : HasDerivAt w ((-2*K) * w r) r := by
    have he := ((hasDerivAt_id r).const_mul (-2*K)).exp
    simpa only [w, mul_one, one_mul, id_eq, mul_comm] using he
  have hF (r : ℝ) (hr : 0 ≤ r) : HasDerivWithinAt F
      (((-2*K) * w r) * E r + w r *
        (2 * inner ℝ (u r) (u' r) + 2*α*g r) - 2 * (w r * h r)) (Ici 0) r := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hwh.intervalIntegrable 0 r)
      hwh.aestronglyMeasurable.stronglyMeasurableAtFilter hwh.continuousAt
    exact ((hwd r).hasDerivWithinAt.mul (hE r hr)).sub (hi.const_mul 2).hasDerivWithinAt
  have hnorm (r : ℝ) (hr : r ∈ Icc (0 : ℝ) t) : ‖u r‖ ^ 2 ≤ E r := by
    have hi : 0 ≤ ∫ v in (0 : ℝ)..r, g v :=
      intervalIntegral.integral_nonneg hr.1 (fun v hv => hg0 v ⟨hv.1, hv.2.trans hr.2⟩)
    dsimp only [E]
    exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) hα) hi)
  have hFc : ContinuousOn F (Ici 0) := fun r hr => (hF r hr).continuousWithinAt
  have hm : AntitoneOn F (Icc (0 : ℝ) t) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 t)
      (hFc.mono fun _ hr => hr.1)
      (fun r hr => (hF r (interior_subset hr).1).mono
        (fun _ hx => (interior_subset hx).1))
    intro r hr
    have hr' := interior_subset hr
    have he := mul_le_mul_of_nonneg_left (henergy r hr') (Real.exp_pos (-2*K*r)).le
    have hn := mul_le_mul_of_nonneg_left (hnorm r hr')
      (mul_nonneg hK (Real.exp_pos (-2*K*r)).le)
    change (-2*K) * w r * E r + w r *
      (2 * inner ℝ (u r) (u' r) + 2*α*g r) - 2*(w r*h r) ≤ 0
    change w r * (inner ℝ (u r) (u' r) + α*g r) ≤
      w r * (K*‖u r‖ ^ 2 + h r) at he
    change (K*w r) * ‖u r‖ ^ 2 ≤ (K*w r) * E r at hn
    nlinarith only [he, hn]
  have hFt := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hsource : (∫ r in (0 : ℝ)..t, w r * h r) ≤ ∫ r in (0 : ℝ)..t, h r := by
    apply intervalIntegral.integral_mono_on ht (hwh.intervalIntegrable 0 t)
      (hh.intervalIntegrable 0 t)
    intro r hr
    have hw1 : w r ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [hK, hr.1])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw1 (hh0 r hr)
  have hbase : w t * E t ≤ ‖u 0‖ ^ 2 + 2 * (∫ r in (0 : ℝ)..t, h r) := by
    dsimp only [F] at hFt
    simp only [w, mul_zero, Real.exp_zero, one_mul, E,
      intervalIntegral.integral_same, mul_zero, add_zero, sub_zero] at hFt
    change w t * E t - 2 * (∫ v in (0 : ℝ)..t, w v * h v) ≤ ‖u 0‖ ^ 2 at hFt
    linarith only [hFt, hsource]
  have hc : Real.exp (2*K*t) * w t = 1 := by
    dsimp only [w]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hb := mul_le_mul_of_nonneg_left hbase (Real.exp_pos (2*K*t)).le
  rw [← mul_assoc, hc, one_mul] at hb
  exact hb


/-- Physical transpose energy is uniform in the generator value of the initial
state and in the force on a fixed ball. -/
theorem short_time_physical_transpose_orbit_energy
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {B : ℝ} (hζ : ‖ζ‖ ≤ B)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Pdag s.toNNReal f) (G s)) ∧
      (∀ j, Continuous (fun s => G s j)) ∧
      ∀ t : ℝ, 0 ≤ t →
        ‖Pdag t.toNNReal f‖ ^ 2 + 2 * (1 / (4 * Λ)) *
          (∫ s in (0 : ℝ)..t, ∑ j, ‖G s j‖ ^ 2) ≤
          Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * t) * ‖f‖ ^ 2 := by
  classical
  obtain ⟨G, H, hG, hc, _, _, _⟩ :=
    short_time_physical_transpose_joint_gradient ha hΛ hA hP hfg
  refine ⟨G, hG, hc, ?_⟩
  let p := fun t : ℝ≥0 => (Pdag t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A => A v) hP.1
  have hpm : ∀ s t, p (s + t) = (p s).comp (p t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro v
    exact congrArg (fun A => A v) (hP.2.1 s t)
  have hpc : ∀ v, Continuous (fun t => p t v) := hP.2.2.1
  have hgraph : C8TransposeC0Graph p f g := by
    have h := (hP.2.2.2.1 f g).mpr hfg
    simp only [C8TransposeC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.ofReal_inv]
    exact h
  have hd : ∀ r, 0 ≤ r → HasDerivWithinAt (fun s : ℝ => Pdag s.toNNReal f)
      (Pdag r.toNNReal g) (Ici 0) r := by
    intro r hr
    rcases hr.eq_or_lt with hr | hr
    · subst r
      exact hgraph.hasDerivWithinAt_orbit hpm 0 le_rfl
    · exact (hgraph.hasDerivAt_orbit hp0 hpm hpc r hr).hasDerivWithinAt
  have hreal (v w : Lp ℂ 2 (volume : Measure (Vec d))) :
      inner ℝ v w = (inner ℂ v w).re := by
    rw [L2.inner_def, L2.inner_def]
    exact integral_re (L2.integrable_inner (𝕜 := ℂ) v w)
  have henergy (r : ℝ) :
      inner ℝ (Pdag r.toNNReal f) (Pdag r.toNNReal g) +
        (1 / (4 * Λ)) * (∑ j, ‖G r j‖ ^ 2) ≤
        ((d : ℝ) * Λ ^ 3 * B ^ 2) * ‖Pdag r.toNNReal f‖ ^ 2 := by
    obtain ⟨G', hG', he⟩ := short_time_physical_transpose_signed_energy a i ζ ha hΛ hA
      (short_time_physical_transpose_map_generator hP hfg r.toNNReal)
    have heG := physicalH1Graph_gradient_unique volume (Or.inl rfl)
      (Pdag r.toNNReal f) G' (G r) hG' (hG r)
    rw [heG, ← hreal] at he
    refine he.trans ?_
    gcongr
  intro t ht
  have hcG : Continuous (fun s => ∑ j, ‖G s j‖ ^ 2) :=
    continuous_finset_sum _ fun j _ => (hc j).norm.pow 2
  have he := c8_transpose_time_energy _ _ hd _ (fun _ => 0) hcG continuous_const
    (1 / (4 * Λ)) ((d : ℝ) * Λ ^ 3 * B ^ 2) t (by positivity) (by positivity) ht
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (fun _ _ => le_rfl)
    (fun r _ => by simpa only [add_zero] using henergy r)
  simpa only [intervalIntegral.integral_zero, mul_zero, add_zero, Real.toNNReal_zero,
    hP.1, ContinuousLinearMap.id_apply] using he

private theorem c8TransposeC0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    C8TransposeC0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
  let u : ℝ → E := fun s => P s.toNNReal f
  let F : ℝ → E := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hPc f).comp continuous_real_toNNReal
  have hF (s : ℝ) : HasDerivAt F (u s) s :=
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hd : HasDerivAt (fun s : ℝ => F ((t : ℝ) + s) - F s) (P t f - f) 0 := by
    have h := ((hF ((t : ℝ) + 0)).scomp 0
      ((hasDerivAt_id 0).const_add (t : ℝ))).sub (hF 0)
    simp only [u, add_zero, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply, one_smul] at h
    exact h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have hh := hslope.comp hcoe
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hshift : P h (F (t : ℝ)) = F ((t : ℝ) + h) - F (h : ℝ) := by
    change P h (∫ s in (0 : ℝ)..(t : ℝ), u s) = _
    rw [← (P h).intervalIntegral_comp_comm (hu.intervalIntegrable 0 t)]
    have he : (fun s : ℝ => P h (u s)) =ᶠ[ae (volume.restrict (uIoc (0 : ℝ) t))]
        (fun s : ℝ => u (s + h)) := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs0 : 0 ≤ s := (min_eq_left t.property ▸ hs.1).le
      dsimp only [u]
      rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm]
      have ha : s.toNNReal + h = (s + (h : ℝ)).toNNReal := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left hs0]
        exact (max_eq_left (add_nonneg hs0 h.property)).symm
      rw [ha]
    rw [intervalIntegral.integral_congr_ae_restrict he,
      intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable 0 h) (hu.intervalIntegrable h (t + h)))
  simp only [Function.comp_apply, slope_def_module, sub_zero, add_zero, F, intervalIntegral.integral_same]
  rw [← hshift]

private theorem C8TransposeC0Graph.smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E} {f g : E} (hfg : C8TransposeC0Graph P f g) (c : ℝ) :
    C8TransposeC0Graph P (c • f) (c • g) := by
  change Tendsto _ _ _
  have h := hfg.const_smul c
  convert h using 1
  ext t
  simp only [map_smul, ← smul_sub]
  exact smul_comm _ _ _

private theorem c8TransposeC0Graph_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) :
    Dense {f : E | ∃ g, C8TransposeC0Graph P f g} := by
  intro f
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hPc f).comp continuous_real_toNNReal
  have hd := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have ht : Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ •
      (∫ s in (0 : ℝ)..(h : ℝ), P s.toNNReal f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
    simpa only [Function.comp_def, slope_def_module, sub_zero,
      intervalIntegral.integral_same, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply] using hh.comp hcoe
  exact mem_closure_of_tendsto ht (.of_forall fun h =>
    ⟨(h : ℝ)⁻¹ • (P h f - f), (c8TransposeC0Graph_integral hP0 hPm hPc f h).smul _⟩)

/-- Time averages approximate arbitrary physical data in the full transpose graph. -/
theorem short_time_physical_transpose_generator_approximation {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ Pr P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ u g : ℕ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, IsPhysicalComplexTransposeGeneratorPair a i ζ (u n) (g n)) ∧
      Tendsto u atTop (𝓝 f) ∧
      ∀ t : ℝ≥0, Tendsto (fun n => P t (u n)) atTop (𝓝 (P t f)) := by
  let p := fun t : ℝ≥0 => (P t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ _ := by
    apply ContinuousLinearMap.ext
    intro v
    change P 0 v = v
    rw [hP.1, ContinuousLinearMap.id_apply]
  have hpm : ∀ s t, p (s+t) = (p s).comp (p t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro v
    exact DFunLike.congr_fun (hP.2.1 s t) v
  have hpc : ∀ v, Continuous (fun t => p t v) := hP.2.2.1
  obtain ⟨u, hu, hf⟩ := mem_closure_iff_seq_limit.mp
    (c8TransposeC0Graph_dense hp0 hpm hpc f)
  choose g hg using hu
  refine ⟨u, g, ?_, hf, fun t => ((P t).continuous.tendsto f).comp hf⟩
  intro n
  apply (hP.2.2.2.1 (u n) (g n)).mp
  have hn := hg n
  simp only [C8TransposeC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ),
    RCLike.ofReal_inv] at hn
  exact hn

/-- The physical transpose growth bound holds for arbitrary L2 initial data. -/
theorem short_time_physical_transpose_norm_sq_bound
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {B : ℝ} (hζ : ‖ζ‖ ≤ B)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexTransposeSemigroup a i ζ P Pdag)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    ‖Pdag t f‖ ^ 2 ≤
      Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨u, g, hug, hu, hut⟩ := short_time_physical_transpose_generator_approximation hP f
  have hn (n : ℕ) : ‖Pdag t (u n)‖ ^ 2 ≤
      Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖u n‖ ^ 2 := by
    obtain ⟨G, _, _, he⟩ :=
      short_time_physical_transpose_orbit_energy ha hΛ hA hζ hP (hug n)
    have hi : 0 ≤ ∫ s in (0 : ℝ)..(t : ℝ), ∑ j, ‖G s j‖ ^ 2 :=
      intervalIntegral.integral_nonneg t.property
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have h := he t t.property
    rw [Real.toNNReal_coe] at h
    exact (le_add_of_nonneg_right (mul_nonneg (by positivity) hi)).trans h
  exact le_of_tendsto_of_tendsto ((hut t).norm.pow 2)
    (tendsto_const_nhds.mul (hu.norm.pow 2)) (Eventually.of_forall hn)

/-- A nonnegative exterior energy loses a Gaussian factor at every short time. -/
theorem short_time_exterior_moving_gaussian_energy
    {d : ℕ} {L ρ s : ℝ} (hL : 0 < L) (hs0 : 0 ≤ s) (hs : s ≤ 1)
    {f : Vec d → ℝ} (hf : Integrable f)
    (hfn : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hzero : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → f x = 0) :
    Integrable (fun x => Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * f x) ∧
      (∫ x, Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * f x) ≤
        Real.exp (-ρ ^ 2 / L) * ∫ x, f x := by
  have hden : 0 < L * (2 - s) := mul_pos hL (by linarith)
  have hweight (x : Vec d) :
      0 ≤ Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 ∧
        Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 ≤ 1 := by
    refine ⟨sq_nonneg _, ?_⟩
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num)
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg_coords x)) hden.le)
  have hi : Integrable (fun x => Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * f x) := by
    apply hf.mono' ?_ ?_
    · have hm : Measurable (fun x : Vec d => Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2) := by
        dsimp only [euclideanSq, dot]
        fun_prop
      exact hm.aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards [hfn] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hweight x).1 hx)]
      exact mul_le_of_le_one_left hx (hweight x).2
  refine ⟨hi, ?_⟩
  have hp : ∀ᵐ x ∂volume,
      Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * f x ≤
        Real.exp (-ρ ^ 2 / L) * f x := by
    filter_upwards [hfn, hzero] with x hx hz
    by_cases hsmall : euclideanSq x < ρ ^ 2
    · simp only [hz hsmall, mul_zero, le_refl]
    apply mul_le_mul_of_nonneg_right _ hx
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hq := le_of_not_gt hsmall
    have hnon := euclideanSq_nonneg_coords x
    have he : 2 * (-euclideanSq x / (L * (2 - s))) ≤ -euclideanSq x / L := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff₀ hden hL).mpr
      nlinarith only [mul_nonneg (mul_nonneg hL.le hnon) hs0]
    exact he.trans (div_le_div_of_nonneg_right (neg_le_neg hq) hL.le)
  exact (integral_mono_ae hi (hf.const_mul _) hp).trans_eq (integral_const_mul _ _)

private theorem c8_transpose_flux_norm_sq_le
    {d : ℕ} (D : Fin d → Fin d → ℂ) (C : Fin d → ℂ)
    (G : Fin d → ℂ) (v ζ : ℂ) {M B : ℝ} (hM : 0 ≤ M)
    (hD : ∀ j k, ‖D j k‖ ≤ M) (hC : ∀ j, ‖C j‖ ≤ M)
    (hζ : ‖ζ‖ ≤ B) (j : Fin d) :
    ‖(1 / 2 : ℂ) * (∑ k, D j k * G k) - ζ * C j * v‖ ^ 2 ≤
      2 * M ^ 2 * d * (∑ k, ‖G k‖ ^ 2) + 2 * B ^ 2 * M ^ 2 * ‖v‖ ^ 2 := by
  have hB := (norm_nonneg ζ).trans hζ
  have hs : ‖∑ k, D j k * G k‖ ≤ M * ∑ k, ‖G k‖ := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hD j k) (norm_nonneg _)
  have hn : ‖(1 / 2 : ℂ) * (∑ k, D j k * G k) - ζ * C j * v‖ ≤
      M * (∑ k, ‖G k‖) + B * M * ‖v‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_mul]
    have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
    rw [hhalf]
    have hforce : ‖ζ‖ * ‖C j‖ * ‖v‖ ≤ B * M * ‖v‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hζ (hC j) (norm_nonneg _) hB) (norm_nonneg _)
    have hs0 : 0 ≤ M * ∑ k, ‖G k‖ := by positivity
    linarith only [hs, hs0, hforce]
  have hcs : (∑ k, ‖G k‖) ^ 2 ≤ (d : ℝ) * ∑ k, ‖G k‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
      (fun _ => (1 : ℝ)) (fun k => ‖G k‖)
  calc
    _ ≤ (M * (∑ k, ‖G k‖) + B * M * ‖v‖) ^ 2 := by gcongr
    _ ≤ 2 * (M * (∑ k, ‖G k‖)) ^ 2 + 2 * (B * M * ‖v‖) ^ 2 := by
      nlinarith only [sq_nonneg (M * (∑ k, ‖G k‖) - B * M * ‖v‖)]
    _ ≤ _ := by
      have hc := mul_le_mul_of_nonneg_left hcs (show 0 ≤ 2 * M ^ 2 by positivity)
      nlinarith only [hc]

/-- A transpose coefficient defect supported outside a ball has a uniform
Gaussian energy bound in the physical state and gradient. -/
theorem short_time_transpose_exterior_flux_energy
    {d : ℕ} {A b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (hA : ∀ j k, MemLp (fun x => (A x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hAe : ∀ᵐ x ∂volume, S5Elliptic (A x) Λ)
    (hbe : ∀ᵐ x ∂volume, S5Elliptic (b x) Λ)
    {B L ρ s : ℝ} (hζ : ‖ζ‖ ≤ B) (hL : 0 < L) (hs0 : 0 ≤ s) (hs : s ≤ 1)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hzero : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → ∀ j,
      (1 / 2 : ℂ) * (∑ k, ((A x j k - b x k j : ℝ) : ℂ) * G k x) -
        ζ * ((A x j i - b x j i : ℝ) : ℂ) * v x = 0) :
    let RF : Fin d → Vec d → ℂ := fun j x =>
      (1 / 2 : ℂ) * (∑ k, ((A x j k - b x k j : ℝ) : ℂ) * G k x) -
        ζ * ((A x j i - b x j i : ℝ) : ℂ) * v x
    Integrable (fun x => Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
      ∑ j, ‖RF j x‖ ^ 2) ∧
    (∫ x, Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * ∑ j, ‖RF j x‖ ^ 2) ≤
      Real.exp (-ρ ^ 2 / L) *
        (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (∑ k, ‖G k‖ ^ 2) +
          2 * d * B ^ 2 * (2 * Λ) ^ 2 * ‖v‖ ^ 2) := by
  classical
  intro RF
  have hRF (j : Fin d) : MemLp (RF j) 2 volume := by
    have hD (j k : Fin d) : MemLp (fun x => ((A x j k - b x k j : ℝ) : ℂ)) ∞ volume := by
      simpa only [Complex.ofReal_sub, Pi.sub_def] using (hA j k).sub (hb k j)
    have hC : MemLp (fun x => ((A x j i - b x j i : ℝ) : ℂ)) ∞ volume := by
      simpa only [Complex.ofReal_sub, Pi.sub_def] using (hA j i).sub (hb j i)
    exact ((memLp_finsetSum _ fun k _ => (hD j k).mul (r := 2) (Lp.memLp (G k))).const_mul _).sub
      (((hC.const_mul ζ).mul (r := 2) (Lp.memLp v)))
  have hRi : Integrable (fun x => ∑ j, ‖RF j x‖ ^ 2) :=
    integrable_finsetSum _ fun j _ => (hRF j).norm.integrable_sq
  obtain ⟨hweighted, htail⟩ := short_time_exterior_moving_gaussian_energy hL hs0 hs hRi
    (ae_of_all _ fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (by
      filter_upwards [hzero] with x hx hsmall
      simp only [RF, hx hsmall, norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero])
  refine ⟨hweighted, htail.trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _))⟩
  have hNi : Integrable (fun x => ∑ k, ‖G k x‖ ^ 2) :=
    integrable_finsetSum _ fun k _ => (Lp.memLp (G k)).norm.integrable_sq
  have hvi := (Lp.memLp v).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, (∑ j, ‖RF j x‖ ^ 2) ≤
      2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (∑ k, ‖G k x‖ ^ 2) +
        2 * d * B ^ 2 * (2 * Λ) ^ 2 * ‖v x‖ ^ 2 := by
    filter_upwards [hAe, hbe] with x hxA hxb
    have hentry (j k l m : Fin d) : ‖((A x j k - b x l m : ℝ) : ℂ)‖ ≤ 2 * Λ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact (abs_sub _ _).trans (by linarith only [hxA.entry_abs_le j k, hxb.entry_abs_le l m])
    have hj (j : Fin d) := c8_transpose_flux_norm_sq_le
      (fun j k => ((A x j k - b x k j : ℝ) : ℂ))
      (fun j => ((A x j i - b x j i : ℝ) : ℂ))
      (fun k => G k x) (v x) ζ (by positivity : 0 ≤ 2 * Λ)
      (fun j k => hentry j k k j) (fun j => hentry j i j i) hζ j
    have he := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d))) (fun j _ => hj j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he
    convert he using 1 <;> ring
  have hi := integral_mono_ae hRi
    ((hNi.const_mul _).add (hvi.const_mul _)) hp
  simp only [Pi.add_apply] at hi
  rw [integral_add (hNi.const_mul _) (hvi.const_mul _), integral_const_mul,
    integral_const_mul, integral_finsetSum _ (fun k _ => (Lp.memLp (G k)).norm.integrable_sq),
    ← physicalL2_norm_sq volume v] at hi
  simpa only [← physicalL2_norm_sq] using hi

/-- Quantitative short-time comparison: interior agreement makes the physical
transpose forcing exponentially small, uniformly in its initial generator value. -/
theorem short_time_transpose_exterior_gaussian_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Prdag →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeGeneratorPair b i ζ fr gr →
      ∀ ρ L : ℝ, 64 * Λ ^ 3 ≤ L →
        (∀ x, euclideanSq x < ρ ^ 2 → b x = ω.1 x) →
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
          ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) ≤
      (∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) +
        Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2 * (t : ℝ)) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖fr‖ ^ 2) := by
  intro Λ γ t ht
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hΛ1 : 1 ≤ Λ := by
    have he : 1 ≤ Real.exp (2 * Λ₀) := Real.one_le_exp (by linarith [Q.ellipticity_parameter])
    dsimp only [Λ]
    nlinarith [Q.ellipticity_parameter]
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  filter_upwards [short_time_transpose_integrated_gaussian_comparison hd Q hP hPdag hfg B hζ t ht,
    c4_ae_reduced_physical_elliptic Q] with ω hcomp hAω
  intro b hb hbe Pr Prdag hPr fr gr hfr ρ L hL hinterior
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  obtain ⟨V, H, _, _, heV, hHG, hcompare⟩ := hcomp b hb hbe Pr Prdag hPr fr gr hfr
  obtain ⟨hfi, hcompare⟩ := hcompare L hL
  obtain ⟨G, hG, hcG, henergy⟩ := short_time_physical_transpose_orbit_energy hb hΛ hbe hζ hPr hfr
  let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
  let RF : Fin d → ℝ × Vec d → ℂ := fun j p => (1 / 2 : ℂ) *
    (∑ k, ((ω.1 p.2 j k - b p.2 k j : ℝ) : ℂ) * H k p) -
      ζ * ((ω.1 p.2 j i - b p.2 j i : ℝ) : ℂ) * V p
  let cg : ℝ := 2 * (d : ℝ) * (2 * Λ) ^ 2 * d
  let cm : ℝ := 2 * d * B ^ 2 * (2 * Λ) ^ 2
  let J : ℝ := Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖fr‖ ^ 2
  let q : ℝ → ℝ := fun s => ∑ j, ‖G s j‖ ^ 2
  let v : ℝ → ℝ := fun s => ‖Prdag s.toNNReal fr‖ ^ 2
  let F : ℝ → ℝ := fun s => Real.exp (-γ * s) *
    ((2 * (4 * Λ + 16 / L)) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2))
  change Integrable F (volume.restrict (Icc (0 : ℝ) (t : ℝ))) at hfi
  have hqi : IntegrableOn q (Icc (0 : ℝ) (t : ℝ)) :=
    (continuous_finsetSum _ fun j _ => (hcG j).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hvi : IntegrableOn v (Icc (0 : ℝ) (t : ℝ)) :=
    ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc)
  have hqtime : (∫ s in Icc (0 : ℝ) (t : ℝ), q s) ≤ 2 * Λ * J := by
    have he := henergy t t.property
    have hdrop : 2 * (1 / (4 * Λ)) * (∫ s in (0 : ℝ)..(t : ℝ), q s) ≤ J := by
      exact (le_add_of_nonneg_left (sq_nonneg _)).trans he
    have hm := mul_le_mul_of_nonneg_left hdrop (show 0 ≤ 2 * Λ by positivity)
    have ha : 2 * Λ * (2 * (1 / (4 * Λ))) = 1 := by field_simp; ring
    rw [← mul_assoc, ha, one_mul] at hm
    rw [intervalIntegral.integral_of_le (f := q) (show (0 : ℝ) ≤ (t : ℝ) from t.property),
      ← integral_Icc_eq_integral_Ioc] at hm
    exact hm
  have hvtime : (∫ s in Icc (0 : ℝ) (t : ℝ), v s) ≤ (t : ℝ) * J := by
    have hvbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) : v s ≤ J := by
      have he := short_time_physical_transpose_norm_sq_bound hb hΛ hbe hζ hPr fr s.toNNReal
      rw [Real.coe_toNNReal _ hs.1] at he
      refine he.trans ?_
      dsimp only [J]
      gcongr
      exact hs.2
    have hi := integral_mono_ae hvi (integrable_const J) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hvbound s hs)
    simpa only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal (show (0 : ℝ) ≤ (t : ℝ) from t.property), smul_eq_mul] using hi
  have hspatial (s : ℝ) (hs : s ∈ Icc (0 : ℝ) (t : ℝ)) :
      (∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2) ≤
        Real.exp (-ρ ^ 2 / L) * (cg * q s + cm * v s) := by
    obtain ⟨K, hK, heK⟩ := hHG s
    have heG := physicalH1Graph_gradient_unique volume (Or.inl rfl) (Prdag s.toNNReal fr)
      K (G s) hK (hG s)
    rw [heG] at heK
    have ha (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
      memLp_complex_elliptic_entry _ _ Λ hΛ hAω
        (fun j k => ω.1.continuous.matrix_elem j k) j k
    have hz : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → ∀ j,
        (1 / 2 : ℂ) * (∑ k, ((ω.1 x j k - b x k j : ℝ) : ℂ) * G s k x) -
          ζ * ((ω.1 x j i - b x j i : ℝ) : ℂ) * (Prdag s.toNNReal fr) x = 0 := by
      apply ae_of_all
      intro x hx j
      have hsym (k : Fin d) : ω.1 x j k = ω.1 x k j :=
        congrArg (fun M : Mat d => M k j) (hAω x).1
      simp only [hinterior x hx, hsym, sub_self, Complex.ofReal_zero, zero_mul,
        Finset.sum_const_zero, mul_zero, sub_self]
    have hbound := (short_time_transpose_exterior_flux_energy ha hb hΛ
      (ae_of_all _ fun x => s5Elliptic_of_isElliptic hΛ1 hAω x) hbe hζ hLp hs.1
      (hs.2.trans ht) (Prdag s.toNNReal fr) (G s) hz).2
    convert hbound using 1
    apply integral_congr_ae
    filter_upwards [heV s, ae_all_iff.mpr heK] with x hx hKx
    simp only [RF, hx, hKx, η]
  have hbound : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (t : ℝ)),
      F s ≤ (Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L))) * (cg * q s + cm * v s) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hnon : 0 ≤ ∫ x, η (s, x) ^ 2 * ∑ j, ‖RF j (s, x)‖ ^ 2 :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    have hm : Real.exp (-γ * s) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hs.1)
    have he := mul_le_mul_of_nonneg_left (hspatial s hs)
      (show 0 ≤ 2 * (4 * Λ + 16 / L) by positivity)
    have hdrop := mul_le_of_le_one_left
      (mul_nonneg (by positivity : 0 ≤ 2 * (4 * Λ + 16 / L)) hnon) hm
    exact hdrop.trans (by nlinarith only [he])
  have hi := integral_mono_ae hfi
    (((hqi.const_mul cg).add (hvi.const_mul cm)).const_mul _) hbound
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (hqi.const_mul cg) (hvi.const_mul cm),
    integral_const_mul, integral_const_mul] at hi
  have hlast : (∫ s in Icc (0 : ℝ) (t : ℝ), F s) ≤
      Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
        (cg * (2 * Λ) + cm * (t : ℝ)) * J := by
    refine hi.trans ?_
    have hg := mul_le_mul_of_nonneg_left hqtime (show 0 ≤ cg by dsimp only [cg]; positivity)
    have hv := mul_le_mul_of_nonneg_left hvtime (show 0 ≤ cm by dsimp only [cm]; positivity)
    calc
      _ ≤ (Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L))) *
          (cg * (2 * Λ * J) + cm * ((t : ℝ) * J)) := by gcongr
      _ = _ := by ring
  have hresult := hcompare.trans (add_le_add le_rfl hlast)
  simpa only [η, F, RF, cg, cm, J, sub_zero, mul_comm L 2] using hresult

private theorem c8_gaussian_square_comparison_tendsto {d : ℕ}
    (a : ℝ) (ha : 0 < a) (u : Vec d → ℂ)
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x / a) : ℂ) * u x) 2 volume)
    (v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (hv : Tendsto v atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / a) ^ 2 * ‖u x - v n x‖ ^ 2)
      atTop (𝓝 (∫ x, Real.exp (-euclideanSq x / a) ^ 2 * ‖u x - f x‖ ^ 2)) := by
  have hhalf : 2 * (a / 2) = a := by ring
  have hu' : MemLp (fun x => (Real.exp (-euclideanSq x / (2 * (a / 2))) : ℂ) * u x)
      2 volume := by simpa only [hhalf] using hu
  have he (x : Vec d) : Real.exp (-euclideanSq x / a) ^ 2 =
      Real.exp (-euclideanSq x / (a / 2)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    <;> ring
  simpa only [he] using short_time_gaussian_comparison_energy_tendsto
    (a / 2) (by positivity) u hu' v f hv

/-- The exterior comparison extends to every retained L2 datum by full
transpose graph density; its environment event precedes the retained data. -/
theorem short_time_transpose_exterior_gaussian_comparison_L2
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Prdag →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ ρ L : ℝ, 64 * Λ ^ 3 ≤ L →
        (∀ x, euclideanSq x < ρ ^ 2 → b x = ω.1 x) →
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
          ‖(Pdag t f) (translate x ω) - (Prdag t fr) x‖ ^ 2) ≤
      (∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) +
        Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2 * (t : ℝ)) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖fr‖ ^ 2) := by
  intro Λ γ t ht
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  filter_upwards [short_time_transpose_exterior_gaussian_comparison hd Q hP hPdag hfg B hζ t ht,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q) (reducedLaw_stationary Q)
      (Pdag t f)] with ω hc hfω htω
  intro b hb hbe Pr Prdag hPr fr ρ L hL hinterior
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  have hat : 0 < L * (2 - (t : ℝ)) := mul_pos hLp (by linarith)
  obtain ⟨u, g, hug, hu, hut⟩ := short_time_physical_transpose_generator_approximation hPr fr
  have h0 := c8_gaussian_square_comparison_tendsto (2 * L) (by positivity)
    (fun x => f (translate x ω)) (hfω (2 * L) (by positivity)) u fr hu
  have hterm := c8_gaussian_square_comparison_tendsto (L * (2 - (t : ℝ))) hat
    (fun x => (Pdag t f) (translate x ω)) (htω _ hat)
    (fun n => Prdag t (u n)) (Prdag t fr) (hut t)
  have hnorm := hu.norm.pow 2
  exact le_of_tendsto_of_tendsto (tendsto_const_nhds.mul hterm)
    (h0.add (tendsto_const_nhds.mul (tendsto_const_nhds.mul hnorm)))
    (Eventually.of_forall fun n => hc b hb hbe Pr Prdag hPr (u n) (g n) (hug n) ρ L hL hinterior)

/-- Interior agreement bounds the initial Gaussian error by the bounded
stationary datum and the retained L2 norm, with an exterior exponential factor. -/
theorem short_time_transpose_initial_gaussian_tail {d : ℕ}
    (u : Vec d → ℂ) (hu : Measurable u) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    {M ρ L : ℝ} (hM : ∀ᵐ x ∂volume, ‖u x‖ ≤ M) (hL : 0 < L)
    (hin : ∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → u x = v x) :
    Integrable (fun x => Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖u x - v x‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖u x - v x‖ ^ 2) ≤
        Real.exp (-ρ ^ 2 / (2 * L)) *
          (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖v‖ ^ 2) := by
  let w : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (2 * L))
  let e : ℝ := Real.exp (-ρ ^ 2 / (2 * L))
  have hw : Measurable w := by dsimp only [w, euclideanSq, dot]; fun_prop
  have hwi : Integrable w := by
    have hp := Integrable.fintype_prod (fun _ : Fin d =>
      integrable_exp_neg_mul_sq (show 0 < (2 * L)⁻¹ by positivity))
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [w, euclideanSq, dot, ← Finset.mul_sum, sq, div_eq_mul_inv]
    ring
  have hvi := (Lp.memLp v).norm.integrable_sq
  have hmajor : Integrable (fun x => e * (2 * M ^ 2 * w x + 2 * ‖v x‖ ^ 2)) :=
    ((hwi.const_mul (2 * M ^ 2)).add (hvi.const_mul 2)).const_mul e
  have hn (x : Vec d) : 0 ≤ w x ∧ w x ≤ 1 := by
    refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (euclideanSq_nonneg_coords x))
      (by positivity)
  have hp : ∀ᵐ x ∂volume, w x ^ 2 * ‖u x - v x‖ ^ 2 ≤
      e * (2 * M ^ 2 * w x + 2 * ‖v x‖ ^ 2) := by
    filter_upwards [hM, hin] with x hx hi
    by_cases hs : euclideanSq x < ρ ^ 2
    · rw [hi hs, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      positivity
    have he : w x ≤ e := Real.exp_le_exp.mpr
      (div_le_div_of_nonneg_right (neg_le_neg (le_of_not_gt hs)) (by positivity))
    have hw2 : w x ^ 2 ≤ e * w x := by nlinarith only [mul_le_mul_of_nonneg_right he (hn x).1]
    have hw2' : w x ^ 2 ≤ e := hw2.trans (mul_le_of_le_one_right (Real.exp_nonneg _) (hn x).2)
    have hu2 : ‖u x‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hx 2
    have herr : ‖u x - v x‖ ^ 2 ≤ 2 * M ^ 2 + 2 * ‖v x‖ ^ 2 := by
      calc
        _ ≤ (‖u x‖ + ‖v x‖) ^ 2 := by gcongr; exact norm_sub_le _ _
        _ ≤ _ := by nlinarith only [hu2, sq_nonneg (‖u x‖ - ‖v x‖)]
    calc
      _ ≤ w x ^ 2 * (2 * M ^ 2 + 2 * ‖v x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left herr (sq_nonneg _)
      _ ≤ e * (2 * M ^ 2 * w x + 2 * ‖v x‖ ^ 2) := by
        have h1 := mul_le_mul_of_nonneg_right hw2 (show 0 ≤ 2 * M ^ 2 by positivity)
        have h2 := mul_le_mul_of_nonneg_right hw2' (show 0 ≤ 2 * ‖v x‖ ^ 2 by positivity)
        nlinarith only [h1, h2]
  have hi : Integrable (fun x => w x ^ 2 * ‖u x - v x‖ ^ 2) := by
    apply hmajor.mono' ((hw.pow_const 2).mul ((hu.sub (Lp.stronglyMeasurable v).measurable).norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [hp] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hx
  refine ⟨hi, ?_⟩
  have hb := integral_mono_ae hi hmajor hp
  rw [integral_const_mul, integral_add (hwi.const_mul _) (hvi.const_mul _),
    integral_const_mul, integral_const_mul, ← physicalL2_norm_sq volume v] at hb
  exact hb

/-- The actual drift observation has a structural spatial bound on one
sample event, derived by stationarity rather than imposed as a new premise. -/
theorem short_time_transpose_drift_spatial_bound {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖β i (translate x ω)‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hb : ∀ᵐ ω ∂reducedLaw Q,
      ‖β i ω‖ ≤ (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity := by
    filter_upwards [hβ.ae_eq_cdiv i, ae_abs_cdiv_le_reduced Q i] with ω hω hbound
    rw [hω]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    nlinarith only [hbound]
  apply (Measure.ae_ae_comm ?_).mp
    (ae_of_all _ fun x => (measurePreserving_translate (reducedLaw Q)
      (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hb)
  exact measurableSet_le
    (((Lp.stronglyMeasurable (β i)).measurable.comp
      Probability.continuous_translate.measurable).norm) measurable_const

/- The actual stationary datum and its full generator graph are supplied
by smooth drift observations; the retained datum is arbitrary physical L2. -/
theorem short_time_transpose_drift_gaussian_comparison
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (B : ℝ) (hζ : ‖ζ‖ ≤ B) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
    let γ := (4 * Λ + 16) * (2 * d * Λ ^ 2 * B ^ 2) + 1
    ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ b : Vec d → Mat d, (∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume) →
      (∀ᵐ x ∂volume, S5Elliptic (b x) Λ) →
      ∀ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexTransposeSemigroup b i ζ Pr Prdag →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ ρ L : ℝ, 64 * Λ ^ 3 ≤ L →
        (∀ x, euclideanSq x < ρ ^ 2 → b x = ω.1 x) →
        (∀ᵐ x ∂volume, euclideanSq x < ρ ^ 2 → (β i) (translate x ω) = fr x) →
      Real.exp (-γ * (t : ℝ)) *
        (∫ x, Real.exp (-euclideanSq x / (L * (2 - (t : ℝ)))) ^ 2 *
          ‖(Pdag t (β i)) (translate x ω) - (Prdag t fr) x‖ ^ 2) ≤
      Real.exp (-ρ ^ 2 / (2 * L)) *
        (2 * M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) + 2 * ‖fr‖ ^ 2) +
        Real.exp (-ρ ^ 2 / L) * (2 * (4 * Λ + 16 / L)) *
          (2 * (d : ℝ) * (2 * Λ) ^ 2 * d * (2 * Λ) +
            2 * d * B ^ 2 * (2 * Λ) ^ 2 * (t : ℝ)) *
          (Real.exp (2 * ((d : ℝ) * Λ ^ 3 * B ^ 2) * (t : ℝ)) * ‖fr‖ ^ 2) := by
  intro Λ M γ t ht
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := i) (ζ := ζ) hβ i
  filter_upwards [short_time_transpose_exterior_gaussian_comparison_L2 hd Q hP hPdag hg B hζ t ht,
    short_time_transpose_drift_spatial_bound hβ i] with ω hc hbω
  intro b hb hbe Pr Prdag hPr fr ρ L hL hinterior hinitial
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := (by positivity : 0 < 64 * Λ ^ 3).trans_le hL
  have hmeas : Measurable (fun x => (β i) (translate x ω)) :=
    (Lp.stronglyMeasurable (β i)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hi := (short_time_transpose_initial_gaussian_tail _ hmeas fr hbω hLp hinitial).2
  exact (hc b hb hbe Pr Prdag hPr fr ρ L hL hinterior).trans (add_le_add hi le_rfl)


private theorem c8_measurable_physical_toLp {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} (f : Ω → Vec d → ℂ)
    (hf : Measurable (fun s : Ω × Vec d => f s.1 s.2))
    (hL : ∀ ω, MemLp (f ω) 2 (volume : Measure (Vec d))) :
    @Measurable Ω (Lp ℂ 2 (volume : Measure (Vec d))) _ (borel _)
      (fun ω => (hL ω).toLp (f ω)) := by
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  have : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  have hcriterion (g : Ω → Lp ℂ 2 (volume : Measure (Vec d)))
      (hg : ∀ y, Measurable (fun ω => dist (g ω) y)) : Measurable g := by
    apply measurable_of_isOpen
    intro s hs
    let I := {b : Lp ℂ 2 (volume : Measure (Vec d)) × ℝ // Metric.ball b.1 b.2 ⊆ s}
    have heq : (⋃ b : I, Metric.ball b.val.1 b.val.2) = s := by
      apply Set.Subset.antisymm
      · exact Set.iUnion_subset fun b => b.property
      · intro y hy
        obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs y hy
        exact Set.mem_iUnion.mpr ⟨⟨(y, ε), hsub⟩, Metric.mem_ball_self hε⟩
    obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
      (fun b : I => Metric.ball b.val.1 b.val.2) (fun _ => Metric.isOpen_ball)
    rw [← heq, ← hcover, Set.preimage_iUnion₂]
    exact MeasurableSet.biUnion hT
      (fun b _ => measurableSet_lt (hg b.val.1) measurable_const)
  apply hcriterion
  intro u
  have hm : Measurable (fun s : Ω × Vec d => f s.1 s.2 - u s.2) :=
    hf.sub ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
  have hnorm : Measurable
      (fun ω => eLpNorm (fun x => f ω x - u x) 2 volume) := by
    have hformula (ω : Ω) : eLpNorm (fun x => f ω x - u x) 2 volume =
        (∫⁻ x, ‖f ω x - u x‖ₑ ^ (2 : ℝ≥0∞).toReal) ^
          (1 / (2 : ℝ≥0∞).toReal) :=
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        ((hL ω).aestronglyMeasurable.sub (Lp.aestronglyMeasurable u))
    simp_rw [hformula]
    exact ENNReal.continuous_rpow_const.measurable.comp
      ((ENNReal.continuous_rpow_const.measurable.comp hm.enorm).lintegral_prod_right')
  have heq : (fun ω => dist ((hL ω).toLp (f ω)) u) =
      (fun ω => (eLpNorm (fun x => f ω x - u x) 2 volume).toReal) := by
    funext ω
    rw [Lp.dist_def, eLpNorm_congr_ae ((hL ω).coeFn_toLp.sub Filter.EventuallyEq.rfl)]
    rfl
  rw [heq]
  exact hnorm.ennreal_toReal

/-- A compactly supported coefficient perturbation has square-integrable
classical drift whenever its retained field is smooth. -/
private theorem c8_retained_smooth_drift_memLp {d : ℕ}
    (χ : C(Vec d, ℝ)) (hcχ : HasCompactSupport χ) (ω : FieldPair d)
    (hω : IsSmoothFieldPair (ForcedLocality.retainedPair χ ω)) (i : Fin d) :
    MemLp (fun x => (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
      (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) 2 volume := by
  have hm (j : Fin d) : MemLp (fun x => (coordinateDerivative j
      (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℂ)) 2 volume := by
    let b : Vec d → ℝ := fun x =>
      (ForcedLocality.retainedPair χ ω).1 x j i - (1 : Mat d) j i
    have hb : ContDiff ℝ 1 b := (hω.1 j i).of_le (by simp) |>.sub contDiff_const
    have he : b = fun x => χ x * (ω.1 x j i - (1 : Mat d) j i) := by
      funext x
      simp only [b, ForcedLocality.retainedPair, ContinuousMap.coe_mk,
        Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    have hcb : HasCompactSupport b := by rw [he]; exact hcχ.mul_right
    have hcd : HasCompactSupport (coordinateDerivative j b) :=
      hcb.fderiv_apply ℝ (unitVector j)
    have hcont : Continuous (coordinateDerivative j b) :=
      (hb.continuous_fderiv_apply one_ne_zero).comp
        (continuous_id.prodMk continuous_const)
    have hmem := (Complex.continuous_ofReal.comp hcont).memLp_of_hasCompactSupport
      (p := (2 : ℝ≥0∞)) (μ := (volume : Measure (Vec d))) (hcd.comp_left (by simp))
    have he' : (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) =
        fun y => b y + (1 : Mat d) j i := by funext y; dsimp [b]; ring
    simpa only [Function.comp_def, he', coordinateDerivative, fderiv_add_const] using hmem
  simpa only [Complex.ofReal_mul, Complex.ofReal_sum] using
    (memLp_finsetSum Finset.univ (fun j _ => hm j)).const_mul ((1 / 2 : ℝ) : ℂ)

/-- The literal retained transpose drift has a locally measurable physical L2
choice on all fields, agreeing with its classical formula on smooth retained fields. -/
theorem short_time_transpose_retained_initial_measurable {d : ℕ}
    (χ : C(Vec d, ℝ)) (hcχ : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) (i : Fin d) :
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr ∧
      ∀ ω, IsSmoothFieldPair (ForcedLocality.retainedPair χ ω) →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
          ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) := by
  classical
  have hentry (j : Fin d) : @Measurable (FieldPair d) C(Vec d, ℝ)
      (borel _) (borel _) (fun ω =>
        ⟨fun x => ω.1 x j i, ω.1.continuous.matrix_elem j i⟩) := by
    apply measurable_continuousMap_of_evaluations
    intro x
    exact (show Continuous (fun ω : FieldPair d => ω.1 x j i) by fun_prop).measurable
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace C(Vec d, ℝ) := borel _
  let : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩
  have hpair : @Measurable (FieldPair d) (FieldPair d) (localSigma U) (borel _)
      (ForcedLocality.retainedPair χ) :=
    ForcedLocality.measurable_retainedPair χ U hsupport
  have hgood : MeasurableSet
      {ω : FieldPair d | IsSmoothFieldPair (ForcedLocality.retainedPair χ ω)} :=
    Sharpness.measurableSet_isSmoothFieldPair_fieldPair.preimage hpair
  let F (ω : FieldPair d) (j : Fin d) : C(Vec d, ℝ) :=
    ⟨fun x => (ForcedLocality.retainedPair χ ω).1 x j i,
      (ForcedLocality.retainedPair χ ω).1.continuous.matrix_elem j i⟩
  have hFm (j : Fin d) : Measurable (fun ω => F ω j) := by
    exact (hentry j).comp hpair
  let b : FieldPair d → Vec d → ℂ := fun ω x =>
    if IsSmoothFieldPair (ForcedLocality.retainedPair χ ω) then
      ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j (F ω j) x : ℝ) else 0
  have hbm : Measurable (fun p : FieldPair d × Vec d => b p.1 p.2) := by
    have hder (j : Fin d) : Measurable (fun p : FieldPair d × Vec d =>
        coordinateDerivative j (F p.1 j) p.2) :=
      (Sharpness.measurable_continuousMap_coordinateDerivative d j).comp
        ((hFm j |>.comp measurable_fst).prodMk measurable_snd)
    exact Measurable.ite (hgood.preimage measurable_fst)
      (Complex.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ => hder j).const_mul
        (1 / 2 : ℝ))) measurable_const
  have hbL (ω : FieldPair d) : MemLp (b ω) 2 volume := by
    by_cases hω : IsSmoothFieldPair (ForcedLocality.retainedPair χ ω)
    · simpa only [b, ite_eq_left hω, F, ContinuousMap.coe_mk] using
        c8_retained_smooth_drift_memLp χ hcχ ω hω i
    · simp only [b, ite_eq_right hω]
      exact MemLp.zero
  refine ⟨fun ω => (hbL ω).toLp (b ω), c8_measurable_physical_toLp b hbm hbL, ?_⟩
  intro ω hω
  simpa only [b, ite_eq_left hω, F, ContinuousMap.coe_mk] using (hbL ω).coeFn_toLp

/-- A single local physical L2 choice agrees with the original classical
transpose drift on every open region where the smooth cutoff is one. -/
theorem short_time_transpose_local_retained_initial_data {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcχ : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) (i : Fin d) :
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      @Measurable _ _ (EinsteinRelation.localSigma U) (borel _) fr ∧
      ∀ ω, IsSmoothFieldPair ω →
        ((fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
          ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ)) ∧
        ∀ V : Set (Vec d), IsOpen V → (∀ x ∈ V, χ x = 1) →
          ∀ᵐ x ∂volume, x ∈ V → fr ω x =
            ((1 / 2 : ℝ) * ∑ j : Fin d,
              coordinateDerivative j (fun y => ω.1 y j i) x : ℝ) := by
  obtain ⟨fr, hm, hf⟩ := short_time_transpose_retained_initial_measurable χ hcχ U hsupport i
  refine ⟨fr, hm, ?_⟩
  intro ω hω
  have hs : IsSmoothFieldPair (ForcedLocality.retainedPair χ ω) := by
    constructor
    · intro j k
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x => χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k)
      exact (hχ.mul (hω.1 j k)).add ((contDiff_const.sub hχ).mul contDiff_const)
    · exact (hχ.mul hω.2).add (contDiff_const.sub hχ)
  refine ⟨hf ω hs, ?_⟩
  intro V hV hχV
  filter_upwards [hf ω hs] with x hx
  intro hxV
  rw [hx]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (ForcedLocality.retainedPair_drift χ ω hV hχV hxV i)


/-- A locally measurable retained drift evolves under the actual physical
transpose semigroup on every elliptic retained field. The choices precede the
law, and time and environment are jointly measurable. -/
theorem short_time_transpose_cutoff_measurable_evolution {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hcχ : HasCompactSupport χ) (U : Set (Vec d))
    (hsupport : ∀ x, x ∉ U → χ x = 0) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (i : Fin d) (ζ : ℂ) :
    let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
    let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∃ fr : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ V : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)),
      Measurable fr ∧ Measurable (Function.uncurry V) ∧
      (∀ ω, IsSmoothFieldPair ω →
        (fr ω : Vec d → ℂ) =ᵐ[volume] fun x =>
          ((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
            (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ)) ∧
      ∀ ω, (∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
        ∃ Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr ∧
          IsPhysicalComplexTransposeSemigroup
            (ForcedLocality.retainedPair χ ω).1 i ζ Pr Prdag ∧
          V ω 0 = fr ω ∧ Continuous (V ω) ∧
          ∀ t, V ω t = Prdag t (fr ω) := by
  classical
  let : MeasurableSpace (FieldPair d) := EinsteinRelation.localSigma U
  let : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  let : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  obtain ⟨fr, hmfr, hfr⟩ :=
    short_time_transpose_local_retained_initial_data χ hχ hcχ U hsupport i
  have hgood : MeasurableSet
      {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ} := by
    have hc : IsClosed {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      have he : {ω : FieldPair d | ∀ x, S5Elliptic (ω.1 x) Λ} =
          ⋂ x : Vec d,
            ((⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | ω.1 x j k = ω.1 x k j}) ∩
              ⋂ ξ : Fin d → ℝ,
                ({ω : FieldPair d | Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil (ω.1 x) ξ ξ} ∩
                 {ω : FieldPair d | s5Bil (ω.1 x) ξ ξ ≤ Λ * ∑ j, ξ j ^ 2})) := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_inter_iff]
        constructor
        · intro h x
          exact ⟨(h x).symm, fun ξ => ⟨(h x).lower ξ, (h x).upper ξ⟩⟩
        · intro h x
          exact ⟨hΛ, (h x).1, fun ξ => ((h x).2 ξ).1, fun ξ => ((h x).2 ξ).2⟩
      rw [he]
      apply isClosed_iInter
      intro x
      refine IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun k => ?_)
        (isClosed_iInter fun ξ => IsClosed.inter ?_ ?_)
      · apply isClosed_eq <;> fun_prop
      · apply isClosed_le continuous_const
        unfold s5Bil
        fun_prop
      · apply isClosed_le _ continuous_const
        unfold s5Bil
        fun_prop
    have hcm : @MeasurableSet (FieldPair d) (borel _)
        {ω | ∀ x, S5Elliptic (ω.1 x) Λ} := by
      let : MeasurableSpace (FieldPair d) := borel _
      exact hc.measurableSet
    exact hcm.preimage (ForcedLocality.measurable_retainedPair χ U hsupport)
  obtain ⟨Pr, Prdag, hPr, _, _, hmPrdag⟩ :=
    short_time_clock_retained_physical_evolution χ U hsupport Λ hΛ i ζ
  let good := {ω : FieldPair d | ∀ x, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ}
  let Ω := {ω : FieldPair d // ω ∈ good}
  let V (ω : FieldPair d) (t : ℝ≥0) :=
    if h : ω ∈ good then Prdag ⟨ω, h⟩ t (fr ω) else 0
  refine ⟨fr, V, hmfr, ?_, fun ω hω => (hfr ω hω).1, ?_⟩
  · let s : Set (FieldPair d × ℝ≥0) := {q | q.1 ∈ good}
    have hs : MeasurableSet s := hgood.preimage measurable_fst
    have hv : Measurable (fun q : s => (⟨q.val.1, q.property⟩ : Ω)) :=
      (measurable_subtype_coe.fst).subtype_mk
    have ht : Measurable (fun q : s => q.val.2) := measurable_subtype_coe.snd
    have hf : Measurable (fun q : s => fr q.val.1) :=
      hmfr.comp measurable_subtype_coe.fst
    exact Measurable.dite (hmPrdag.comp (hv.prodMk (ht.prodMk hf))) measurable_const hs
  · intro ω hω
    refine ⟨Pr ⟨ω, hω⟩, Prdag ⟨ω, hω⟩, (hPr ⟨ω, hω⟩).1,
      (hPr ⟨ω, hω⟩).2, ?_, ?_, fun t => dite_eq_left hω⟩
    · change (if h : ω ∈ good then Prdag ⟨ω, h⟩ 0 (fr ω) else 0) = fr ω
      have hh : ω ∈ good := hω
      rw [dif_pos hh, (hPr ⟨ω, hω⟩).2.1]
      rfl
    · have he : V ω = fun t => Prdag ⟨ω, hω⟩ t (fr ω) := by
        funext t
        exact dite_eq_left hω
      rw [he]
      exact (hPr ⟨ω, hω⟩).2.2.2.1 (fr ω)

/-- Cauchy--Schwarz for a complex temporal primitive on a finite interval. -/
private theorem c8_endpoint_primitive_sq_bound {u : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) t))) :
    ‖∫ s in Icc (0 : ℝ) t, u s‖ ^ 2 ≤
      t * ∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2 := by
  have hc : MemLp (fun _ : ℝ => (1 : ℂ)) 2 (volume.restrict (Icc (0 : ℝ) t)) :=
    memLp_const _
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hc) (by simpa using hu)
  have hv : (volume (Icc (0 : ℝ) t)).toReal = t := by
    simp only [Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht]
  simp only [norm_one, one_mul, Real.rpow_two, integral_const, smul_eq_mul,
    mul_one, one_pow, Measure.real, Measure.restrict_apply_univ, hv,
    ← Real.sqrt_eq_rpow] at h
  have hn := norm_integral_le_integral_norm (μ := volume.restrict (Icc (0 : ℝ) t)) u
  have hI : 0 ≤ ∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hs := Real.sq_sqrt hI
  have ht' := Real.sq_sqrt ht
  have hp := mul_nonneg (Real.sqrt_nonneg t)
    (Real.sqrt_nonneg (∫ s in Icc (0 : ℝ) t, ‖u s‖ ^ 2))
  have hsq := sq_le_sq₀ (norm_nonneg _) hp |>.mpr (hn.trans h)
  simpa only [mul_pow, ht', hs] using hsq

/-- A square-integrable space-time derivative gives a quantitative strong
local trace for its literal temporal primitive. -/
private theorem c8_endpoint_local_primitive_trace {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {U : ℝ × X → ℂ} (hU : Measurable U)
    (hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ)) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2) μ ∧
      (∫ x, ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2 ∂μ) ≤
        t * ∫ x, (∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2) ∂μ) ∧
    Tendsto (fun t : ℝ≥0 => ∫ x, ‖∫ s in Icc (0 : ℝ) (t : ℝ), U (s, x)‖ ^ 2 ∂μ)
      (𝓝 0) (𝓝 0) := by
  have hb (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      ∀ᵐ x ∂μ, ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2 ≤
        t * ∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2 := by
    filter_upwards [hI.prod_left_ae] with x hx
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht1
    have hmem : MemLp (fun s => U (s, x)) 2 (volume.restrict (Icc (0 : ℝ) 1)) :=
      (memLp_two_iff_integrable_sq_norm
        (hU.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
    exact (c8_endpoint_primitive_sq_bound ht
      (hmem.mono_measure (Measure.restrict_mono_set _ hsub))).trans
      (mul_le_mul_of_nonneg_left (setIntegral_mono_set hx
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ fun _ hx => hsub hx)) ht)
  have hi (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
      Integrable (fun x => ‖∫ s in Icc (0 : ℝ) t, U (s, x)‖ ^ 2) μ := by
    have hm : Measurable (fun x => ∫ s in Icc (0 : ℝ) t, U (s, x)) :=
      (hU.stronglyMeasurable.integral_prod_left'
        (μ := volume.restrict (Icc (0 : ℝ) t))).measurable
    apply (hI.integral_prod_right.const_mul t).mono' (hm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb t ht ht1] with x hx
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hx
  have hall (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :=
    integral_mono_ae (hi t ht ht1) (hI.integral_prod_right.const_mul t) (hb t ht ht1)
  refine ⟨fun t ht ht1 => ⟨hi t ht ht1, ?_⟩, ?_⟩
  · simpa only [integral_const_mul] using hall t ht ht1
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _
    (by
      simpa only [NNReal.coe_zero, zero_mul] using
        ((NNReal.continuous_coe.tendsto 0).mul_const
          (∫ x, (∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2) ∂μ)))
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with t ht
  simpa only [integral_const_mul] using hall t t.coe_nonneg (by exact_mod_cast ht.le)

/-- One actual stationary primitive has a local strong-L2 initial trace on
one sample event, simultaneously for every compact spatial region. The trace
uses a coherent representative rather than point evaluations of L2 classes. -/
theorem short_time_stationary_transpose_primitive_local_strong_trace
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      (∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        (∀ t : ℝ≥0, (t : ℝ) ≤ 1 →
          Integrable (fun x => ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2)
            (volume.restrict K)) ∧
        Tendsto (fun t : ℝ≥0 =>
          ∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2)
          (𝓝 0) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_transpose_joint_primitive hP hPdag hfg
  refine ⟨F, U, hF, hU, heF, heU, hprim, ?_⟩
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    c8_short_time_integrable_sq_joint_l2
      ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hloc := ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hI.ofReal
  filter_upwards [hloc] with ω hω
  intro K hK
  have hi : Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) := by
    exact (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hω K hK).swap
  have hm : Measurable (fun p : ℝ × Vec d => U (p.1, translate p.2 ω)) :=
    hU.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  obtain ⟨hbound, htrace⟩ := c8_endpoint_local_primitive_trace (volume.restrict K) hm hi
  have he (t : ℝ) (x : Vec d) :
      F (t, translate x ω) - f (translate x ω) =
        ∫ v in Icc (0 : ℝ) t, U (v, translate x ω) := by
    rw [hprim, add_sub_cancel_left]
  refine ⟨fun t ht => ?_, ?_⟩
  · simpa only [he] using (hbound t t.coe_nonneg ht).1
  · simpa only [he] using htrace

/-- The actual stationary-minus-retained evolution has a local zero strong-L2
trace wherever the physical initial datum agrees with the stationary datum.
Only actual semigroup continuity is used for the retained orbit. -/
theorem short_time_stationary_transpose_retained_local_zero_trace
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
      ∀ (a : Vec d → Mat d)
        (Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup a i ζ Pr Prdag →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
        Tendsto (fun t : ℝ≥0 =>
          ∫ x in K, ‖F (t, translate x ω) - (Prdag t fr) x‖ ^ 2)
          (𝓝 0) (𝓝 0) := by
  obtain ⟨F, U, hF, _, heF, _, _, htrace⟩ :=
    short_time_stationary_transpose_primitive_local_strong_trace Q hP hPdag hfg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [htrace] with ω hω
  intro K hK a Pr Prdag hPr fr hinit
  obtain ⟨hFi, hFt⟩ := hω K hK
  have hphys (t : ℝ≥0) :
      Integrable (fun x => ‖(Prdag t fr) x - fr x‖ ^ 2) volume ∧
      (∫ x, ‖(Prdag t fr) x - fr x‖ ^ 2) = ‖Prdag t fr - fr‖ ^ 2 := by
    have he := Lp.coeFn_sub (Prdag t fr) fr
    have hi := (Lp.memLp (Prdag t fr - fr)).norm.integrable_sq
    have he' : (fun x => ‖(Prdag t fr - fr) x‖ ^ 2) =ᵐ[volume]
        (fun x => ‖(Prdag t fr) x - fr x‖ ^ 2) := by
      filter_upwards [he] with x hx
      rw [hx]
      rfl
    refine ⟨hi.congr he', ?_⟩
    rw [← integral_congr_ae he', ← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hupper (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) :
      (∫ x in K, ‖F (t, translate x ω) - (Prdag t fr) x‖ ^ 2) ≤
        2 * (∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2) +
        2 * ‖Prdag t fr - fr‖ ^ 2 := by
    have hBi : Integrable (fun x => ‖(Prdag t fr) x - fr x‖ ^ 2) (volume.restrict K) :=
      (hphys t).1.mono_measure (Measure.restrict_le_self)
    have hb : ∀ᵐ x ∂volume.restrict K,
        ‖F (t, translate x ω) - (Prdag t fr) x‖ ^ 2 ≤
          2 * ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2 +
          2 * ‖(Prdag t fr) x - fr x‖ ^ 2 := by
      filter_upwards [hinit] with x hx
      have hn := norm_sub_le_norm_sub_add_norm_sub
        (F (t, translate x ω)) (f (translate x ω)) ((Prdag t fr) x)
      rw [hx, norm_sub_rev (fr x)] at hn
      rw [hx]
      have hn2 := (sq_le_sq₀ (norm_nonneg _)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hn
      nlinarith [sq_nonneg (‖F (t, translate x ω) - fr x‖ - ‖(Prdag t fr) x - fr x‖),
        norm_nonneg (F (t, translate x ω) - (Prdag t fr) x), norm_nonneg ((Prdag t fr) x - fr x),
        norm_nonneg (F (t, translate x ω) - fr x)]
    have hmajor := ((hFi t ht).const_mul 2).add (hBi.const_mul 2)
    have hm : AEStronglyMeasurable
        (fun x => ‖F (t, translate x ω) - (Prdag t fr) x‖ ^ 2) (volume.restrict K) := by
      have hshift : Measurable (fun x : Vec d => ((t : ℝ), translate x ω)) :=
        measurable_const.prodMk (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))
      exact (((hF.comp hshift).sub
        (Lp.stronglyMeasurable (Prdag t fr)).measurable).norm.pow_const 2).aestronglyMeasurable
    have hi := hmajor.mono' hm (hb.mono fun x hx => by
      rwa [Real.norm_of_nonneg (sq_nonneg _)])
    calc
      _ ≤ ∫ x in K, 2 * ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2 +
          2 * ‖(Prdag t fr) x - fr x‖ ^ 2 := integral_mono_ae hi hmajor hb
      _ = 2 * (∫ x in K, ‖F (t, translate x ω) - f (translate x ω)‖ ^ 2) +
          2 * (∫ x in K, ‖(Prdag t fr) x - fr x‖ ^ 2) := by
        rw [integral_add ((hFi t ht).const_mul 2) (hBi.const_mul 2), integral_const_mul,
          integral_const_mul]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        ((setIntegral_le_integral (s := K) (hphys t).1 (ae_of_all _ fun _ => sq_nonneg _)).trans_eq
          (hphys t).2) (show (0 : ℝ) ≤ 2 by norm_num))
  have hpt : Tendsto (fun t : ℝ≥0 => ‖Prdag t fr - fr‖ ^ 2) (𝓝 0) (𝓝 0) := by
    have h := (((hPr.2.2.1 fr).tendsto 0).sub_const fr).norm.pow 2
    simpa only [hPr.1, ContinuousLinearMap.id_apply, sub_self, norm_zero, zero_pow
      (by norm_num : (2 : ℕ) ≠ 0)] using h
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) _
    (by simpa only [mul_zero, add_zero] using (hFt.const_mul 2).add (hpt.const_mul 2))
  filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ≥0) < 1)] with t ht
  exact hupper t (by exact_mod_cast ht.le)


/-- A reduced drift observation is the literal classical spatial drift on one
sample event, before the spatial point and every subsequent cutoff choice. -/
theorem short_time_transpose_drift_spatial_identification
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      β i (translate x ω) =
        ((1 / 2 : ℝ) * ∑ j : Fin d,
          coordinateDerivative j (fun y => ω.1 y j i) x : ℝ) := by
  have hm : Measurable (fun ω : FieldPair d =>
      (((1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => ω.1 y j i) 0 : ℝ) : ℂ)) := by
    have hd (j : Fin d) : Measurable (fun ω : FieldPair d =>
        coordinateDerivative j (fun y => ω.1 y j i) 0) :=
      (measurable_fderiv_apply_const_with_param ℝ
        (f := fun (ω : FieldPair d) (y : Vec d) => ω.1 y j i)
        (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
          |>.matrix_elem j i) (unitVector j)).comp (measurable_id.prodMk measurable_const)
    exact Complex.measurable_ofReal.comp
      ((Finset.measurable_sum _ fun j _ => hd j).const_mul (1 / 2 : ℝ))
  filter_upwards [ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (β i)).measurable hm (hβ i)] with ω hω
  filter_upwards [hω] with x hx
  rw [hx]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  have ht := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : Vec d => ω.1 y j i)
    (x := (0 : Vec d)) x
  rw [add_zero] at ht
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) ht

/-- The actual drift and any literal retained drift have zero local strong-L2
trace inside the cutoff plateau. The sample event precedes every cutoff,
compact region and physical transpose semigroup. -/
theorem short_time_transpose_actual_retained_local_zero_trace
    {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ F : ℝ × FieldPair d → ℂ, Measurable F ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)) (O K : Set (Vec d)),
        IsOpen O → (∀ x ∈ O, χ x = 1) → IsCompact K → K ⊆ O →
      ∀ (Pr Prdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Prdag →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      Tendsto (fun t : ℝ≥0 =>
        ∫ x in K, ‖F (t, translate x ω) - (Prdag t fr) x‖ ^ 2)
        (𝓝 0) (𝓝 0) := by
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := i) (ζ := ζ) hβ i
  obtain ⟨F, hF, heF, htrace⟩ :=
    short_time_stationary_transpose_retained_local_zero_trace Q hP hPdag hg
  refine ⟨F, hF, heF, ?_⟩
  filter_upwards [htrace, short_time_transpose_drift_spatial_identification hβ i]
    with ω htr hβω
  intro χ O K hO hχO hK hKO Pr Prdag hPr fr hfr
  apply htr K hK _ Pr Prdag hPr fr
  filter_upwards [ae_restrict_of_ae hβω,
    ae_restrict_of_ae hfr, ae_restrict_mem hK.measurableSet] with x hxβ hxfr hxK
  rw [hxβ, hxfr]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (ForcedLocality.retainedPair_drift χ ω hO hχO (hKO hxK) i).symm

private theorem c8_short_time_c0_integral_slope
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    Tendsto (fun h : ℝ≥0 => (h : ℝ)⁻¹ •
      (P h (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) -
        (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f)))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (P t f - f)) := by
  let u : ℝ → E := fun s => P s.toNNReal f
  let F : ℝ → E := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hPc f).comp continuous_real_toNNReal
  have hF (s : ℝ) : HasDerivAt F (u s) s :=
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hd : HasDerivAt (fun s : ℝ => F ((t : ℝ) + s) - F s) (P t f - f) 0 := by
    have h := ((hF ((t : ℝ) + 0)).scomp 0
      ((hasDerivAt_id 0).const_add (t : ℝ))).sub (hF 0)
    simp only [u, add_zero, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply, one_smul] at h
    exact h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have hh := hslope.comp hcoe
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hshift : P h (F (t : ℝ)) = F ((t : ℝ) + h) - F (h : ℝ) := by
    change P h (∫ s in (0 : ℝ)..(t : ℝ), u s) = _
    rw [← (P h).intervalIntegral_comp_comm (hu.intervalIntegrable 0 t)]
    have he : (fun s : ℝ => P h (u s)) =ᶠ[ae (volume.restrict (uIoc (0 : ℝ) t))]
        (fun s : ℝ => u (s + h)) := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs0 : 0 ≤ s := (min_eq_left t.property ▸ hs.1).le
      dsimp only [u]
      rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm]
      have ha : s.toNNReal + h = (s + (h : ℝ)).toNNReal := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left hs0]
        exact (max_eq_left (add_nonneg hs0 h.property)).symm
      rw [ha]
    rw [intervalIntegral.integral_congr_ae_restrict he,
      intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable 0 h) (hu.intervalIntegrable h (t + h)))
  simp only [Function.comp_apply, slope_def_module, sub_zero, add_zero, F, intervalIntegral.integral_same]
  rw [← hshift]

/-- The actual environmental transpose primitive belongs to the full horizontal
H1 graph, for arbitrary initial data in the stationary L2 space. -/
theorem short_time_stationary_transpose_integral_generator
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IsComplexTransposeGeneratorPair Q i ζ
      (∫ s in (0 : ℝ)..(t : ℝ), T s.toNNReal f) (T t f - f) := by
  apply hT.generatorPair_of_tendsto_slope hP
  have hs := c8_short_time_c0_integral_slope
    (P := fun s => (T s).restrictScalars ℝ)
    (congrArg (fun A => A.restrictScalars ℝ) (hT.zero hP))
    (fun s r => congrArg (fun A => A.restrictScalars ℝ) (hT.add hP s r))
    (fun v => hT.continuous_apply hP v) f t
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv] at hs
  exact hs


/-- The time-integrated stationary-minus-retained transpose orbit has a
homogeneous conservative equation on every cutoff plateau. The retained datum
is arbitrary L2 data; its time primitive supplies its H1 graph internally.
The event is selected before the cutoff, region and physical evolution. -/
theorem short_time_transpose_integral_retained_interior
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (i : Fin d) (ζ : ℂ)
    (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    let u := ∫ s in (0 : ℝ)..(t : ℝ), T s.toNNReal f
    ∃ H : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H ∧
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)) (O : Set (Vec d)),
        MeasurableSet O → (∀ x ∈ O, χ x = 1) →
        (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ))
          ∞ volume) →
      ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fun x => f (translate x ω)) =ᵐ[volume.restrict O] fr →
      let v := ∫ s in (0 : ℝ)..(t : ℝ), Tr s.toNNReal fr
      ∃ K : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) v K ∧
        ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence O
          (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
            (H k (translate x ω) - K k x)) -
            2 * ζ * (ω.1 x j i : ℂ) * (u (translate x ω) - v x)))
          (fun x => L (2 * ((T t f) (translate x ω) - (Tr t fr) x))) := by
  intro u
  have hug := short_time_stationary_transpose_integral_generator Q i ζ P T hP hT f t
  obtain ⟨H, hH, he⟩ := short_time_transpose_generator_retained_residual
    hd Q i ζ u (T t f - f) hug
  have hsub := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (T t f - f)).measurable
    ((Lp.stronglyMeasurable (T t f)).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub (T t f) f)
  refine ⟨H, hH, ?_⟩
  filter_upwards [he, hsub, short_time_transpose_retained_defect_support Q]
    with ω hω hsω hdω
  intro χ O hO hχ ha Pr Tr hTr fr hinit v
  have hvg := physical_transpose_generator_timeIntegral
    (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr hTr fr t
  have hKex := hvg
  obtain ⟨K, hK, _⟩ := hKex
  refine ⟨K, hK, ?_⟩
  intro L
  have heq := hω (ForcedLocality.retainedPair χ ω).1 ha v (Tr t fr - fr) K hK hvg L
  apply (HasWeakDivergence.restrict_subset (Set.subset_univ O)
    MeasurableSet.univ heq).congr_ae
  · filter_upwards [ae_restrict_mem hO] with x hx
    funext j
    rw [hdω χ x (hχ x hx) i j ζ (v x) (fun k => K k x)]
    simp only [mul_zero, add_zero]
  · filter_upwards [ae_restrict_of_ae hsω,
      ae_restrict_of_ae (Lp.coeFn_sub (Tr t fr) fr), hinit] with x hs hr hi
    simp only [Pi.sub_apply] at hs hr ⊢
    rw [hs, hr, hi]
    congr 1
    ring


/-- The retained transpose drift contains the cutoff derivative term. -/
theorem short_time_transpose_retained_drift_product {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : Differentiable ℝ χ)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (i : Fin d) (x : Vec d) :
    (1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
      (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x =
    χ x * ((1 / 2 : ℝ) * ∑ j : Fin d,
      coordinateDerivative j (fun y => ω.1 y j i) x) +
      (1 / 2 : ℝ) * ∑ j : Fin d,
        (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x := by
  have he (j : Fin d) : coordinateDerivative j
      (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x =
      χ x * coordinateDerivative j (fun y => ω.1 y j i) x +
        (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x := by
    have hf := (hω.1 j i).differentiable (by simp) x
    change (fderiv ℝ (fun y => χ y * ω.1 y j i +
      (1 - χ y) * (1 : Mat d) j i) x) (unitVector j) = _
    have hder := ((hχ x).hasFDerivAt.mul hf.hasFDerivAt).add
      (((hasFDerivAt_const (1 : ℝ) x).sub (hχ x).hasFDerivAt).mul_const
        ((1 : Mat d) j i))
    have hdeq : fderiv ℝ (fun y => χ y * ω.1 y j i +
        (1 - χ y) * (1 : Mat d) j i) x = _ := hder.fderiv
    rw [hdeq]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.zero_apply, smul_eq_mul,
      coordinateDerivative]
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- A radius cutoff gives a polynomial physical L2 bound for the complete
retained transpose drift, including its cutoff derivative. -/
theorem short_time_transpose_retained_drift_norm_sq {d : ℕ}
    (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (ω : FieldPair d) (hω : IsSmoothFieldPair ω) (i : Fin d)
    (A M C ρ : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hC : 0 ≤ C) (hρ : 1 ≤ ρ)
    (hχb : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hχzero : ∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0)
    (hχder : ∀ j x, |coordinateDerivative j χ x| ≤ C / ρ)
    (ha : ∀ x j k, |ω.1 x j k| ≤ A)
    (hb : ∀ᵐ x ∂(volume : Measure (Vec d)),
      |(1 / 2 : ℝ) * ∑ j : Fin d,
        coordinateDerivative j (fun y => ω.1 y j i) x| ≤ M)
    (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : (fr : Vec d → ℂ) =ᵐ[volume] fun x =>
      (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
        (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) :
    ‖fr‖ ^ 2 ≤ (M + (1 / 2 : ℝ) * d * (A + 1) * C) ^ 2 * (2 * ρ) ^ d := by
  let N := M + (1 / 2 : ℝ) * d * (A + 1) * C
  let S : Set (Vec d) := Icc (fun _ => -ρ) (fun _ => ρ)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have hρ0 : 0 < ρ := zero_lt_one.trans_le hρ
  have hvol : volume.real S = (2 * ρ) ^ d := by
    dsimp [S, Measure.real]
    rw [Real.volume_Icc_pi_toReal (by intro j; dsimp; linarith)]
    simp only [sub_neg_eq_add, ← two_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hi : Integrable (S.indicator (fun _ => N ^ 2)) volume :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (C := N ^ 2) isCompact_Icc.measure_ne_top)
  have hpoint : ∀ᵐ x ∂volume, ‖fr x‖ ^ 2 ≤ S.indicator (fun _ => N ^ 2) x := by
    filter_upwards [hfr, hb] with x hx hbx
    rw [hx, Complex.norm_real, Real.norm_eq_abs]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      have hd (j : Fin d) :
          |(ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x| ≤ (A + 1) * C := by
        have hId : |(1 : Mat d) j i| ≤ 1 := by
          simp only [Matrix.one_apply]; split_ifs <;> norm_num
        have hdiv : C / ρ ≤ C := div_le_self hC hρ
        rw [abs_mul]
        exact mul_le_mul ((abs_sub _ _).trans (add_le_add (ha x j i) hId))
          ((hχder j x).trans hdiv) (abs_nonneg _) (by positivity)
      have hbd : |(1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x| ≤ N := by
        rw [short_time_transpose_retained_drift_product χ
          (hχ.differentiable (by simp)) ω hω i x]
        apply (abs_add_le _ _).trans
        have hfirst : |χ x * ((1 / 2 : ℝ) * ∑ j : Fin d,
            coordinateDerivative j (fun y => ω.1 y j i) x)| ≤ M := by
          rw [abs_mul, abs_of_nonneg (hχb x).1]
          exact (mul_le_mul (hχb x).2 hbx (abs_nonneg _) zero_le_one).trans_eq (one_mul M)
        have hsum := (Finset.abs_sum_le_sum_abs _ Finset.univ).trans
          (Finset.sum_le_sum (fun j _ => hd j))
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        have hsecond : |(1 / 2 : ℝ) * ∑ j : Fin d,
            (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x| ≤
              (1 / 2 : ℝ) * d * (A + 1) * C := by
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          nlinarith only [hsum]
        exact add_le_add hfirst hsecond
      exact pow_le_pow_left₀ (abs_nonneg _) hbd 2
    · rw [indicator_of_notMem hxS]
      have hcoord (j : Fin d) : |x j| ≤ euclideanNorm x := by
        unfold euclideanNorm euclideanSq dot
        apply Real.abs_le_sqrt
        simpa only [sq] using Finset.single_le_sum (f := fun k => x k * x k)
          (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)
      have hnx : ρ < euclideanNorm x := by
        by_contra hn
        apply hxS
        constructor <;> intro j
        · have h := (hcoord j).trans (le_of_not_gt hn)
          exact (abs_le.mp h).1
        · have h := (hcoord j).trans (le_of_not_gt hn)
          exact (abs_le.mp h).2
      have hopen : IsOpen {y : Vec d | ρ / 2 < euclideanNorm y} :=
        isOpen_lt continuous_const (by unfold euclideanNorm euclideanSq dot; fun_prop)
      have hnear : ∀ᶠ y in 𝓝 x, χ y = 0 := by
        filter_upwards [hopen.mem_nhds (by dsimp; linarith : x ∈ {y : Vec d | ρ / 2 < euclideanNorm y})]
          with y hy
        exact hχzero y hy.le
      have hzero (j : Fin d) : coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x = 0 := by
        have he : (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) =ᶠ[𝓝 x]
            (fun _ => (1 : Mat d) j i) := by
          filter_upwards [hnear] with y hy
          simp [ForcedLocality.retainedPair, hy]
        unfold coordinateDerivative
        rw [he.fderiv_eq]
        simp
      simp only [hzero, Finset.sum_const_zero, mul_zero, abs_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]
  have hint := integral_mono_ae (Lp.memLp fr).norm.integrable_sq hi hpoint
  rw [← physicalL2_norm_sq volume fr, integral_indicator measurableSet_Icc,
    setIntegral_const, smul_eq_mul, hvol] at hint
  simpa only [N, mul_comm] using hint

/-- The literal retained transpose drift has a structural polynomial L2 bound
on one sample event, before all smooth cutoff and radius choices. -/
theorem short_time_transpose_actual_retained_drift_norm_sq
    {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) :
    let Λ := Real.exp (2 * D.ellipticity) * D.ellipticity
    let M := (1 / 2 : ℝ) * d * reducedLipschitzConstant D.ellipticity
    ∀ᵐ ω ∂reducedLaw Q,
      ∀ (χ : C(Vec d, ℝ)), ContDiff ℝ (⊤ : ℕ∞) χ →
      ∀ C ρ : ℝ, 0 ≤ C → 1 ≤ ρ →
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      (∀ x, ρ / 2 ≤ euclideanNorm x → χ x = 0) →
      (∀ j x, |coordinateDerivative j χ x| ≤ C / ρ) →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j : Fin d, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ‖fr‖ ^ 2 ≤ (M + (1 / 2 : ℝ) * d * (Λ + 1) * C) ^ 2 * (2 * ρ) ^ d := by
  dsimp only
  have hΛ : 0 ≤ Real.exp (2 * D.ellipticity) * D.ellipticity :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have hL : 0 ≤ reducedLipschitzConstant D.ellipticity := by
    unfold reducedLipschitzConstant
    exact mul_nonneg (Real.exp_pos _).le
      (by nlinarith [Q.ellipticity_parameter, sq_nonneg D.ellipticity])
  obtain ⟨Mseq, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  filter_upwards [hsmooth Q hQ, c4_ae_reduced_physical_elliptic Q,
    short_time_transpose_drift_spatial_identification hβ i,
    short_time_transpose_drift_spatial_bound hβ i] with ω hω hA hbi hbb
  intro χ hχ C ρ hC hρ hχb hχzero hχder fr hfr
  apply short_time_transpose_retained_drift_norm_sq χ hχ ω hω.1 i
    _ _ C ρ hΛ (by positivity) hC hρ hχb hχzero hχder _ _ fr hfr
  · intro x j k
    apply abs_entry_le_of_quadratic_bounds hΛ (ω.1 x) (hA x).1
    · intro ξ
      exact (mul_nonneg (inv_nonneg.mpr hΛ) (euclideanSq_nonneg_coords ξ)).trans
        ((hA x).2 ξ).1
    · exact fun ξ => ((hA x).2 ξ).2
  · filter_upwards [hbi, hbb] with x hx hb
    rw [hx, Complex.norm_real, Real.norm_eq_abs] at hb
    exact hb

/-- A transpose graph orbit and an arbitrary physical transpose graph orbit
have one measurable temporal zero extension on each compact region of initial
agreement. Real projections obey the weak time identity across zero. -/
theorem short_time_stationary_transpose_retained_temporal_zero_extension
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (a : Vec d → Mat d)
        (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup a i ζ Pr Tr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair a i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Tr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_transpose_joint_primitive hP hPdag hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    c8_short_time_integrable_sq_joint_l2
      ((((hPdag.continuous_apply hP g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hIU : Integrable U ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mpr hI).integrable (by norm_num)
  filter_upwards [ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hIU] with ω hω
  intro a Pr Tr hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, hprimR⟩ := short_time_physical_transpose_joint_primitive hPr hfr
  let Y : ℝ × Vec d → ℂ := fun p => (Ioc (0 : ℝ) 1).indicator
    (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1
  let X : ℝ × Vec d → ℂ := fun p => ∫ s in Icc (0 : ℝ) p.1, Y (s, p.2)
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hY : Measurable Y := by
    exact Measurable.ite (measurableSet_Ioc.preimage measurable_fst)
      ((hU.comp hshift).sub hZ) measurable_const
  have hX : Measurable X := measurable_complexPrimitive hY 0
  refine ⟨V, Z, X, Y, hV, hZ, hX, hY, heV, heZ, fun _ => rfl, ?_, ?_⟩
  · intro s hs x
    by_cases hs' : s = 0
    · subst s
      simp [X]
    · simp only [X, Icc_eq_empty_of_lt (lt_of_le_of_ne hs hs'),
        Measure.restrict_empty, integral_zero_measure]
  · have hZI : Integrable (fun p => ‖Z p‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure (Vec d))) :=
      c8_short_time_integrable_sq_joint_l2
        ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
          isCompact_Icc) hZ heZ
    have hZtime : ∀ᵐ x ∂(volume : Measure (Vec d)),
        IntegrableOn (fun s => Z (s, x)) (Icc (0 : ℝ) 1) := by
      filter_upwards [hZI.prod_left_ae] with x hx
      exact ((memLp_two_iff_integrable_sq_norm
        (hZ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx).integrable
          (by norm_num)
    intro K hK hinit
    have htime : ∀ᵐ x ∂volume.restrict K,
        IntegrableOn (fun s => U (s, translate x ω) - Z (s, x)) (Icc (0 : ℝ) 1) := by
      filter_upwards [(hω K hK).prod_right_ae, ae_restrict_of_ae hZtime] with x hx hz
      exact hx.sub hz
    refine ⟨?_, ?_⟩
    · intro s hs hs1
      filter_upwards [htime, hinit, (hω K hK).prod_right_ae,
        ae_restrict_of_ae hZtime] with x hx hix hu hz
      have he : (∫ t in Icc (0 : ℝ) s,
          (Ioc (0 : ℝ) 1).indicator
            (fun v => U (v, translate x ω) - Z (v, x)) t) =
          ∫ t in Icc (0 : ℝ) s, U (t, translate x ω) - Z (t, x) := by
        rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact indicator_of_mem (show t ∈ Ioc (0 : ℝ) 1 from ⟨ht.1, ht.2.trans hs1⟩) _
      change (∫ t in Icc (0 : ℝ) s,
        (Ioc (0 : ℝ) 1).indicator (fun v => U (v, translate x ω) - Z (v, x)) t) = _
      rw [he, hprim, hprimR, hix]
      have hu' : IntegrableOn (fun t => U (t, translate x ω)) (Icc (0 : ℝ) 1) := hu
      have hz' : IntegrableOn (fun t => Z (t, x)) (Icc (0 : ℝ) 1) := hz
      rw [integral_sub (hu'.mono_set (Icc_subset_Icc le_rfl hs1))
        (hz'.mono_set (Icc_subset_Icc le_rfl hs1))]
      ring
    · filter_upwards [htime] with x hx
      let y : ℝ → ℂ := (Ioc (0 : ℝ) 1).indicator
        (fun t => U (t, translate x ω) - Z (t, x))
      have hy : Integrable y := (integrable_indicator_iff measurableSet_Ioc).mpr
        (hx.mono_set Ioc_subset_Icc_self)
      have hprimitive (t : ℝ) : X (t, x) = ∫ s in (0 : ℝ)..t, y s := by
        by_cases ht : 0 ≤ t
        · rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
        · have ht' : t < 0 := lt_of_not_ge ht
          have hz : ∫ s in Ioc t (0 : ℝ), y s = 0 := by
            apply setIntegral_eq_zero_of_forall_eq_zero
            intro s hs
            exact indicator_of_notMem (fun h => (not_lt_of_ge hs.2) h.1) _
          simp only [X, Icc_eq_empty_of_lt ht', Measure.restrict_empty, integral_zero_measure,
            intervalIntegral.integral_of_ge ht'.le, hz, neg_zero]
      intro L
      have hLy : Integrable (fun t => L (y t)) := L.integrable_comp hy
      have hcomm (t : ℝ) : L (X (t, x)) = ∫ s in (0 : ℝ)..t, L (y s) := by
        rw [hprimitive, L.intervalIntegral_comp_comm hy.intervalIntegrable]
      have hac : AbsolutelyContinuousOnInterval (fun t => L (X (t, x))) (-1) 1 := by
        simp only [hcomm]
        exact hLy.intervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral
          (by norm_num [uIcc_of_le])
      refine ⟨hac, ?_⟩
      intro ψ hψ hψa hψb
      have hψac := hψ.contDiffOn.absolutelyContinuousOnInterval (a := (-1 : ℝ)) (b := 1)
      have hprod := hψac.integral_deriv_mul_eq_sub hac
      have hd : ∀ᵐ t ∂volume, deriv (fun s => L (X (s, x))) t = L (Y (t, x)) := by
        filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hLy.locallyIntegrable]
          with t ht
        simpa only [hcomm] using (ht 0).deriv
      have hi : (∫ t in (-1 : ℝ)..1, deriv ψ t * L (X (t, x)) + ψ t * L (Y (t, x))) =
          ∫ t in (-1 : ℝ)..1,
            deriv ψ t * L (X (t, x)) + ψ t * deriv (fun s => L (X (s, x))) t := by
        apply intervalIntegral.integral_congr_ae
        filter_upwards [hd] with t ht _
        rw [ht]
      rw [hi, hprod, hψa, hψb, zero_mul, zero_mul, sub_self]


/-- The same representatives satisfy the transpose spatial residual and the
weak temporal identity across zero. The physical orbit is in its actual
transpose generator graph; its continuous gradient is constructed internally.
The environment event precedes the cutoff, plateau and physical evolution. -/
theorem short_time_transpose_retained_coherent_weak_equations
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ Measurable U ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (complexTransposeGradientOrbit Q Pdag f s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ))
        ∞ volume) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr →
      ∃ V Z X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        Measurable V ∧ Measurable Z ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Tr s.toNNReal gr) ∧
        (∀ p, Y p = (Ioc (0 : ℝ) 1).indicator
          (fun s => U (s, translate p.2 ω) - Z (s, p.2)) p.1) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Tr s.toNNReal fr) (H s)) ∧
        (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
          HasWeakGradient univ (fun x => L (F (s, translate x ω)))
            (fun x j => L (D j (s, translate x ω))) ∧
          ∀ O : Set (Vec d), MeasurableSet O → (∀ x ∈ O, χ x = 1) →
          HasWeakDivergence O
            (fun x j => L ((∑ k, (ω.1 x j k : ℂ) *
              (D k (s, translate x ω) - H s k x)) -
              2 * ζ * (ω.1 x j i : ℂ) * (F (s, translate x ω) - V (s, x))))
            (fun x => L (2 * Y (s, x)))) ∧
        ∀ K : Set (Vec d), IsCompact K →
        (fun x => f (translate x ω)) =ᵐ[volume.restrict K] fr →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          ∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, htime⟩ :=
    short_time_stationary_transpose_retained_temporal_zero_extension Q hP hPdag hfg
  obtain ⟨D, hD, heD⟩ := short_time_transpose_exists_joint_gradient_representative
    Q hP hPdag f g hfg
  refine ⟨F, U, D, hF, hU, hD, heF, heU, heD, ?_⟩
  have hres := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (short_time_joint_transpose_retained_residual Q hP hPdag
        f g hfg F U D hF hU hD heF heU heD))
  have hgrad := Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae
      (short_time_joint_transpose_spatial_gradient Q hP hPdag
        f g hfg F D hF hD heF heD))
  filter_upwards [htime, hres, hgrad, short_time_transpose_retained_defect_support Q]
    with ω ht hr hg hdef
  intro χ ha Λ hΛ hA Pr Tr hPr fr gr hfr
  obtain ⟨V, Z, X, Y, hV, hZ, hX, hY, heV, heZ, heY, hX0, hlocal⟩ :=
    ht (ForcedLocality.retainedPair χ ω).1 Pr Tr hPr fr gr hfr
  obtain ⟨H, hH, hHc⟩ := physical_transpose_generator_orbit_continuous_gradient
    (ForcedLocality.retainedPair χ ω).1 i ζ ha hΛ hA
    (fun s : ℝ => Tr s.toNNReal fr) (fun s : ℝ => Tr s.toNNReal gr)
    ((hPr.2.2.1 fr).comp continuous_real_toNNReal)
    ((hPr.2.2.1 gr).comp continuous_real_toNNReal)
    (fun s => short_time_physical_transpose_map_generator hPr hfr s.toNNReal)
  refine ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, ?_, hlocal⟩
  have hr' := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hr
  have hg' := ae_restrict_of_ae_restrict_of_subset
    (show Ioc (0 : ℝ) 1 ⊆ Ioi (0 : ℝ) from Ioc_subset_Ioi_self) hg
  filter_upwards [hr', hg', ae_restrict_mem measurableSet_Ioc] with s hrs hgs hs
  intro L
  refine ⟨hgs L, ?_⟩
  intro O hO hχO
  have hdiv := hrs (ForcedLocality.retainedPair χ ω).1 ha
    (Tr s.toNNReal fr) (Tr s.toNNReal gr) (H s) (hH s)
    (short_time_physical_transpose_map_generator hPr hfr s.toNNReal) L
  dsimp only [Prod.swap] at hdiv
  apply (HasWeakDivergence.restrict_subset (Set.subset_univ O)
    MeasurableSet.univ hdiv).congr_ae
  · filter_upwards [ae_restrict_of_ae (heV s), ae_restrict_mem hO] with x hx hxO
    funext j
    rw [hdef χ x (hχO x hxO) i j ζ ((Tr s.toNNReal fr) x) (fun k => H s k x)]
    simp only [mul_zero, add_zero, hx]
  · filter_upwards [ae_restrict_of_ae (heZ s)] with x hx
    rw [heY, indicator_of_mem hs, hx]


private theorem c8_smooth_compact_flux_pairing {d : ℕ}
    (b c : Fin d → Vec d → ℝ) (ζ : ℂ)
    (hb : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (b j))
    (hc : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (c j))
    (hbc : ∀ j, HasCompactSupport (b j)) (hcc : ∀ j, HasCompactSupport (c j)) :
    ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      ∀ (v : Lp ℂ 2 (volume : Measure (Vec d)))
        (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) v H →
      (∫ x, gr x * v x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, (b j x : ℂ) * H j x) +
          ζ * (∫ x, ∑ j, (c j x : ℂ) * H j x) := by
  classical
  choose B J hB heB heJ using fun j =>
    short_time_transpose_compact_physical_test (b j) (hb j) (hbc j)
  choose C K hC heC heK using fun j =>
    short_time_transpose_compact_physical_test (c j) (hc j) (hcc j)
  have hdb (j : Fin d) : MemLp (fun x => (coordinateDerivative j (b j) x : ℂ)) 2 volume :=
    (memLp_congr_ae (heJ j j)).mp (Lp.memLp (J j j))
  have hdc (j : Fin d) : MemLp (fun x => (coordinateDerivative j (c j) x : ℂ)) 2 volume :=
    (memLp_congr_ae (heK j j)).mp (Lp.memLp (K j j))
  let q : Vec d → ℂ := fun x =>
    (1 / 2 : ℂ) * ∑ j, (coordinateDerivative j (b j) x : ℂ) -
      ζ * ∑ j, (coordinateDerivative j (c j) x : ℂ)
  have hq : MemLp q 2 volume :=
    ((memLp_finsetSum _ fun j _ => hdb j).const_mul (1 / 2 : ℂ)).sub
      ((memLp_finsetSum _ fun j _ => hdc j).const_mul ζ)
  let gr := hq.toLp q
  refine ⟨gr, ?_⟩
  intro v H hv
  have hIB (j : Fin d) :
      (∫ x, (coordinateDerivative j (b j) x : ℂ) * v x) =
        -(∫ x, (b j x : ℂ) * H j x) := by
    have hh := physicalH1Graph_integral_mul_gradient (B j) v (J j) H (hB j) hv j
    have hl : (∫ x, B j x * H j x) = ∫ x, (b j x : ℂ) * H j x :=
      integral_congr_ae ((heB j).fun_mul (Filter.EventuallyEq.rfl))
    have hr : (∫ x, J j j x * v x) = ∫ x, (coordinateDerivative j (b j) x : ℂ) * v x :=
      integral_congr_ae ((heJ j j).fun_mul (Filter.EventuallyEq.rfl))
    rw [hl, hr] at hh
    linear_combination hh
  have hIC (j : Fin d) :
      (∫ x, (coordinateDerivative j (c j) x : ℂ) * v x) =
        -(∫ x, (c j x : ℂ) * H j x) := by
    have hh := physicalH1Graph_integral_mul_gradient (C j) v (K j) H (hC j) hv j
    have hl : (∫ x, C j x * H j x) = ∫ x, (c j x : ℂ) * H j x :=
      integral_congr_ae ((heC j).fun_mul (Filter.EventuallyEq.rfl))
    have hr : (∫ x, K j j x * v x) = ∫ x, (coordinateDerivative j (c j) x : ℂ) * v x :=
      integral_congr_ae ((heK j j).fun_mul (Filter.EventuallyEq.rfl))
    rw [hl, hr] at hh
    linear_combination hh
  have hbd (j : Fin d) : Integrable (fun x => (b j x : ℂ) * H j x) :=
    ((memLp_congr_ae (heB j)).mp (Lp.memLp (B j))).integrable_mul (Lp.memLp (H j))
  have hcd (j : Fin d) : Integrable (fun x => (c j x : ℂ) * H j x) :=
    ((memLp_congr_ae (heC j)).mp (Lp.memLp (C j))).integrable_mul (Lp.memLp (H j))
  have hdbv (j : Fin d) : Integrable (fun x => (coordinateDerivative j (b j) x : ℂ) * v x) :=
    (hdb j).integrable_mul (Lp.memLp v)
  have hdcv (j : Fin d) : Integrable (fun x => (coordinateDerivative j (c j) x : ℂ) * v x) :=
    (hdc j).integrable_mul (Lp.memLp v)
  have hdbs : Integrable (fun x => ∑ j, (coordinateDerivative j (b j) x : ℂ) * v x) :=
    integrable_finsetSum Finset.univ (fun j _ => hdbv j)
  have hdcs : Integrable (fun x => ∑ j, (coordinateDerivative j (c j) x : ℂ) * v x) :=
    integrable_finsetSum Finset.univ (fun j _ => hdcv j)
  rw [integral_congr_ae (hq.coeFn_toLp.fun_mul (Filter.EventuallyEq.rfl))]
  simp only [q, sub_mul, mul_assoc, Finset.sum_mul]
  rw [integral_sub
    (hdbs.const_mul _)
    (hdcs.const_mul _),
    integral_const_mul, integral_const_mul,
    integral_finsetSum Finset.univ (fun j _ => hdbv j),
    integral_finsetSum Finset.univ (fun j _ => hdcv j),
    integral_finsetSum Finset.univ (fun j _ => hbd j),
    integral_finsetSum Finset.univ (fun j _ => hcd j)]
  simp_rw [hIB, hIC]
  simp only [Finset.sum_neg_distrib]
  ring

/-- Smooth compactly supported data belong to the full physical transpose
operator graph for every smooth real coefficient field and complex force. -/
theorem short_time_smooth_compact_transpose_generator
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) :
    ∃ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair a i ζ fr gr ∧
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x => (f x : ℂ)) := by
  classical
  obtain ⟨fr, G, hG, hefr, heG⟩ := short_time_transpose_compact_physical_test f hf hfc
  have hdf (k : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative k f) :=
    (hf.fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const
  let b (j : Fin d) (x : Vec d) : ℝ := ∑ k, a x k j * coordinateDerivative k f x
  let c (j : Fin d) (x : Vec d) : ℝ := a x j i * f x
  have hb (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (b j) :=
    ContDiff.sum fun k _ => (ha k j).mul (hdf k)
  have hc (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞) (c j) := (ha j i).mul hf
  have hbc (j : Fin d) : HasCompactSupport (b j) := by
    have hbEq : b j = ∑ k, (fun x => a x k j * coordinateDerivative k f x) := by
      funext x
      simp only [b, Finset.sum_apply]
    rw [hbEq]
    exact HasCompactSupport.finset_sum
      (fun k _ => (hfc.fderiv_apply ℝ (unitVector k)).mul_left)
  have hcc (j : Fin d) : HasCompactSupport (c j) := hfc.mul_left
  obtain ⟨gr, hgr⟩ := c8_smooth_compact_flux_pairing b c ζ hb hc hbc hcc
  refine ⟨fr, gr, ⟨G, hG, ?_⟩, hefr⟩
  intro v H hv
  rw [hgr v H hv]
  have hbID : (∫ x, ∑ j, (b j x : ℂ) * H j x) =
      ∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * H j x := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr heG] with x hx
    simp only [b, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, hx]
  have hcID : (∫ x, ∑ j, (c j x : ℂ) * H j x) =
      ∫ x, fr x * (∑ j, (a x j i : ℂ) * H j x) := by
    apply integral_congr_ae
    filter_upwards [hefr] with x hx
    simp only [c, hx, Complex.ofReal_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hbID, hcID]


/-- The literal retained drift belongs to the actual physical transpose
generator graph. Smooth compact cutoffs supply this fact internally. -/
theorem short_time_retained_transpose_drift_generator
    {d : ℕ} (χ : C(Vec d, ℝ)) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (ω : FieldPair d) (hω : IsSmoothFieldPair ω)
    (i : Fin d) (ζ : ℂ) (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    (hfr : (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
      (((1 / 2 : ℝ) * ∑ j, coordinateDerivative j
        (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ))) :
    ∃ gr : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (ForcedLocality.retainedPair χ ω).1 i ζ fr gr := by
  have ha (j k : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => (ForcedLocality.retainedPair χ ω).1 x j k) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => χ x * ω.1 x j k + (1 - χ x) * (1 : Mat d) j k)
    exact (hχ.mul (hω.1 j k)).add ((contDiff_const.sub hχ).mul contDiff_const)
  let f : Vec d → ℝ := fun x => (1 / 2 : ℝ) * ∑ j, coordinateDerivative j
    (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    contDiff_const.mul (ContDiff.sum fun j _ =>
      ((ha j i).fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const)
  have he : f = fun x =>
      χ x * ((1 / 2 : ℝ) * ∑ j, coordinateDerivative j (fun y => ω.1 y j i) x) +
        (1 / 2 : ℝ) * ∑ j,
          (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x :=
    funext (short_time_transpose_retained_drift_product χ (hχ.differentiable (by simp)) ω hω i)
  have hfc : HasCompactSupport f := by
    rw [he]
    apply HasCompactSupport.add hχc.mul_right
    have hsum : HasCompactSupport
        (∑ j : Fin d, (fun x => (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x)) :=
      HasCompactSupport.finset_sum (fun j _ => (hχc.fderiv_apply ℝ (unitVector j)).mul_left)
    have hsum' : HasCompactSupport (fun x => ∑ j : Fin d,
        (ω.1 x j i - (1 : Mat d) j i) * coordinateDerivative j χ x) := by
      convert hsum using 1
      funext x
      simp only [Finset.sum_apply]
    exact hsum'.mul_left
  obtain ⟨fr', gr, hgraph, hefr'⟩ := short_time_smooth_compact_transpose_generator
    (ForcedLocality.retainedPair χ ω).1 i ζ ha f hf hfc
  have hff : fr = fr' := Lp.ext (hfr.trans hefr'.symm)
  exact ⟨gr, hff.symm ▸ hgraph⟩

/-- A spatial weak gradient survives extension by zero in time, with slice
representatives compared only almost everywhere on the spatial domain. -/
theorem short_time_zero_extension_spatial_gradient
    {d : ℕ} (O : Set (Vec d)) (X W : ℝ × Vec d → ℝ)
    (G : ℝ → Vec d → Vec d)
    (hX0 : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (heX : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (fun x => W (s, x)) =ᵐ[volume.restrict O] (fun x => X (s, x)))
    (hgrad : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasWeakGradient O (fun x => W (s, x)) (G s)) :
    let J := fun s x k => (Ioc (0 : ℝ) 1).indicator (fun r => G r x k) s
    ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
      HasWeakGradient O (fun x => X (s, x)) (J s) := by
  intro J
  have hg := (ae_restrict_iff' measurableSet_Ioc).mp hgrad
  filter_upwards [ae_restrict_of_ae hg, ae_restrict_mem measurableSet_Ioo] with s hs hm
  by_cases hp : 0 < s
  · have ht : s ∈ Ioc (0 : ℝ) 1 := ⟨hp, hm.2.le⟩
    intro j
    apply (hs ht j).congr_ae (heX s hp hm.2.le)
    exact ae_of_all _ fun x => by simp only [J, indicator_of_mem ht]
  · have hn : s ≤ 0 := le_of_not_gt hp
    have ht : s ∉ Ioc (0 : ℝ) 1 := fun ht => (not_lt_of_ge hn) ht.1
    simp only [hX0 s hn, J, indicator_of_notMem ht]
    intro j
    refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ _
    simp

/-- Spatial divergence survives extension by zero in time. The representative
of the solution is allowed to be changed on a spatial null set on each slice. -/
theorem short_time_transpose_zero_extension_spatial_divergence
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ) (O : Set (Vec d))
    (X Y W : ℝ × Vec d → ℂ) (G : ℝ → Vec d → Fin d → ℂ)
    (hX0 : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (hY0 : ∀ s : ℝ, s ≤ 0 → ∀ x, Y (s, x) = 0)
    (heX : ∀ s : ℝ, 0 < s → s ≤ 1 →
      (fun x => W (s, x)) =ᵐ[volume.restrict O] (fun x => X (s, x)))
    (hdiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence O
        (fun x j => L ((∑ k, (a x j k : ℂ) * G s x k) -
          2 * ζ * (a x j i : ℂ) * W (s, x)))
        (fun x => L (2 * Y (s, x)))) :
    let J := fun s x k => (Ioc (0 : ℝ) 1).indicator (fun r => G r x k) s
    ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence O
        (fun x j => L ((∑ k, (a x j k : ℂ) * J s x k) -
          2 * ζ * (a x j i : ℂ) * X (s, x)))
        (fun x => L (2 * Y (s, x))) := by
  intro J
  have hd : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) 1 → ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence O
        (fun x j => L ((∑ k, (a x j k : ℂ) * G s x k) -
          2 * ζ * (a x j i : ℂ) * W (s, x)))
        (fun x => L (2 * Y (s, x))) :=
    (ae_restrict_iff' measurableSet_Ioc).mp hdiv
  filter_upwards [ae_restrict_of_ae hd, ae_restrict_mem measurableSet_Ioo] with s hs hmem
  intro L
  by_cases hpos : 0 < s
  · have ht : s ∈ Ioc (0 : ℝ) 1 := ⟨hpos, hmem.2.le⟩
    apply (hs ht L).congr_ae
    · filter_upwards [heX s hpos hmem.2.le] with x hx
      funext j
      simp only [J, indicator_of_mem ht, hx]
    · exact Filter.EventuallyEq.rfl
  · have hn : s ≤ 0 := le_of_not_gt hpos
    have ht : s ∉ Ioc (0 : ℝ) 1 := fun ht => (not_lt_of_ge hn) ht.1
    simp only [J, indicator_of_notMem ht, hX0 s hn, hY0 s hn,
      mul_zero, Finset.sum_const_zero, sub_self, map_zero]
    refine ⟨fun _ => locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ _
    simp [dot]

/-- The actual transpose drift and literal retained drift give a coherent
weak equation across zero on every compact cutoff plateau. No physical
generator membership or local initial-matching premise is required. -/
theorem short_time_transpose_actual_retained_zero_extension_equation
    {d : ℕ} (S : StructuralData d)
    (Q : EnvironmentLaw d S.ellipticity S.dependenceRange)
    (hQ : HasSmoothBounds S Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (i : Fin d) {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ F : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable F ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal (β i)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (complexTransposeGradientOrbit Q Pdag (β i) s) j) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ χ : C(Vec d, ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      (∀ j k, MemLp (fun x => ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ)) ∞ volume) →
      ∀ Λ : ℝ, 0 < Λ →
      (∀ᵐ x ∂volume, S5Elliptic ((ForcedLocality.retainedPair χ ω).1 x) Λ) →
      ∀ Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeSemigroup (ForcedLocality.retainedPair χ ω).1 i ζ Pr Tr →
      ∀ fr : Lp ℂ 2 (volume : Measure (Vec d)),
      (fr : Vec d → ℂ) =ᵐ[volume] (fun x =>
        (((1 / 2 : ℝ) * ∑ j, coordinateDerivative j
          (fun y => (ForcedLocality.retainedPair χ ω).1 y j i) x : ℝ) : ℂ)) →
      ∃ V X Y : ℝ × Vec d → ℂ,
      ∃ H : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        Measurable V ∧ Measurable X ∧ Measurable Y ∧
        (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) ∧
        (∀ j, Continuous (fun s => H s j)) ∧
        (∀ s, IsPhysicalH1Graph volume (Or.inl rfl) (Tr s.toNNReal fr) (H s)) ∧
        ∀ O K : Set (Vec d), IsOpen O → (∀ x ∈ O, χ x = 1) →
          IsCompact K → K ⊆ O →
          (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
            (fun x => X (s, x)) =ᵐ[volume.restrict K]
              (fun x => F (s, translate x ω) - V (s, x))) ∧
          (∀ᵐ x ∂volume.restrict K, ∀ L : ℂ →L[ℝ] ℝ,
            AbsolutelyContinuousOnInterval (fun s => L (X (s, x))) (-1) 1 ∧
            ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
              (∫ s in (-1 : ℝ)..1,
                deriv ψ s * L (X (s, x)) + ψ s * L (Y (s, x))) = 0) ∧
          let J := fun s x k => (Ioc (0 : ℝ) 1).indicator
            (fun r => D k (r, translate x ω) - H r k x) s
          (∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
            HasWeakGradient (interior K) (fun x => (X (s, x)).re)
              (fun x k => (J s x k).re) ∧
            HasWeakGradient (interior K) (fun x => (X (s, x)).im)
              (fun x k => (J s x k).im)) ∧
          ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1), ∀ L : ℂ →L[ℝ] ℝ,
            HasWeakDivergence (interior K)
              (fun x j => L ((∑ k, (ω.1 x j k : ℂ) * J s x k) -
                2 * ζ * (ω.1 x j i : ℂ) * X (s, x)))
              (fun x => L (2 * Y (s, x))) := by
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := i) (ζ := ζ) hβ i
  obtain ⟨F, U, D, hF, hU, hD, heF, heU, heD, hcoh⟩ :=
    short_time_transpose_retained_coherent_weak_equations Q hP hPdag hg
  obtain ⟨Mseq, _, hsmooth⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d S
  refine ⟨F, D, hF, hD, heF, heD, ?_⟩
  filter_upwards [hcoh, hsmooth Q hQ, short_time_transpose_drift_spatial_identification hβ i]
    with ω hc hω hbi
  intro χ hχ hχc ha Λ hΛ hA Pr Tr hPr fr hfr
  obtain ⟨gr, hgr⟩ := short_time_retained_transpose_drift_generator χ hχ hχc ω hω.1 i ζ fr hfr
  obtain ⟨V, Z, X, Y, H, hV, hZ, hX, hY, heV, heZ, heY, hX0, hHc, hH, hsp, hlocal⟩ :=
    hc χ ha Λ hΛ hA Pr Tr hPr fr gr hgr
  refine ⟨V, X, Y, H, hV, hX, hY, heV, hX0, hHc, hH, ?_⟩
  intro O K hO hχO hK hKO
  have hmatch : (fun x => (β i) (translate x ω)) =ᵐ[volume.restrict K] fr := by
    filter_upwards [ae_restrict_of_ae hbi, ae_restrict_of_ae hfr,
      ae_restrict_mem hK.measurableSet] with x hb hf hx
    rw [hb, hf]
    exact congrArg (fun r : ℝ => (r : ℂ))
      (ForcedLocality.retainedPair_drift χ ω hO hχO (hKO hx) i).symm
  obtain ⟨heX, htime⟩ := hlocal K hK hmatch
  refine ⟨heX, htime, ?_, ?_⟩
  · have hgrad (L : ℂ →L[ℝ] ℝ)
        (hphys : ∀ s, HasWeakGradient univ (fun x => L ((Tr s.toNNReal fr) x))
          (fun x k => L (H s k x))) :
        ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 1),
          HasWeakGradient (interior K) (fun x => L (X (s, x)))
            (fun x k => L ((Ioc (0 : ℝ) 1).indicator
              (fun r => D k (r, translate x ω) - H r k x) s)) := by
      have hz := short_time_zero_extension_spatial_gradient (interior K)
        (fun p => L (X p)) (fun p => L (F (p.1, translate p.2 ω) - V p))
        (fun s x k => L (D k (s, translate x ω) - H s k x))
        (fun s hs x => by rw [hX0 s hs x, map_zero])
        (fun s hs hs1 => (ae_restrict_of_ae_restrict_of_subset interior_subset
          (heX s hs.le hs1).symm).mono fun x hx => congrArg L hx) ?_
      · simpa only [Set.indicator, apply_ite L, map_zero] using hz
      · filter_upwards [hsp] with s hs
        intro j
        have hd := Correctors.hasWeakPartialDerivative_sub ((hs L).1 j) (hphys s j)
        apply (HasWeakPartialDerivative.restrict_subset (subset_univ (interior K))
          MeasurableSet.univ hd).congr_ae
        · filter_upwards [ae_restrict_of_ae (heV s)] with x hx
          simp only [← map_sub, hx]
        · exact ae_of_all _ fun x => by simp only [map_sub]
    have hre := hgrad Complex.reCLM (fun s => (hH s).1)
    have him := hgrad Complex.imCLM (fun s => (hH s).2)
    filter_upwards [hre, him] with s hr hi
    exact ⟨hr, hi⟩
  apply short_time_transpose_zero_extension_spatial_divergence ω.1 i ζ (interior K)
    X Y (fun p => F (p.1, translate p.2 ω) - V p)
    (fun s x k => D k (s, translate x ω) - H s k x) hX0
  · intro s hs x
    rw [heY, indicator_of_notMem (show s ∉ Ioc (0 : ℝ) 1 from fun ht => (not_lt_of_ge hs) ht.1)]
  · intro s hs hs1
    exact ae_restrict_of_ae_restrict_of_subset interior_subset (heX s hs.le hs1).symm
  · filter_upwards [hsp] with s hs
    intro L
    exact (hs L).2 (interior K) isOpen_interior.measurableSet
      (fun x hx => hχO x (hKO (interior_subset hx)))

/-- A coherent stationary-minus-physical transpose residual that vanishes before
zero is locally square integrable in space-time. The sample event precedes all
physical coefficients, semigroups, representatives and compact plateaus. -/
theorem short_time_transpose_coherent_residual_spacetime_memLp
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (f : Lp ℂ 2 (reducedLaw Q)) (F : ℝ × FieldPair d → ℂ)
    (hF : Measurable F)
    (heF : ∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] Pdag s.toNNReal f) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (a : Vec d → Mat d)
      (Pr Tr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexTransposeSemigroup a i ζ Pr Tr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V X : ℝ × Vec d → ℂ),
      Measurable V → Measurable X →
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Tr s.toNNReal fr) →
      (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) →
      ∀ K : Set (Vec d), IsCompact K →
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        (fun x => X (s, x)) =ᵐ[volume.restrict K]
          (fun x => F (s, translate x ω) - V (s, x))) →
      MemLp X 2 ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hFI : Integrable (fun p => ‖F p‖ ^ 2)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (reducedLaw Q)) :=
    c8_short_time_integrable_sq_joint_l2
      ((((hPdag.continuous_apply hP f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hF heF
  filter_upwards [ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hFI.ofReal] with ω hω
  intro a Pr Tr hPr fr V X hV hX heV hX0 K hK heX
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hFs : MemLp (fun p : ℝ × Vec d => F (p.1, translate p.2 ω)) 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) :=
    (memLp_two_iff_integrable_sq_norm (hF.comp hshift).aestronglyMeasurable).mpr
      ((Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hω K hK).swap)
  have hVI : Integrable (fun p => ‖V p‖ ^ 2)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume : Measure (Vec d))) :=
    c8_short_time_integrable_sq_joint_l2
      ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hV heV
  have hVs : MemLp V 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) :=
    ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVI).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)
  let W : ℝ × Vec d → ℂ :=
    {p : ℝ × Vec d | p.1 ∈ Ioc (0 : ℝ) 1}.indicator
      (fun p => F (p.1, translate p.2 ω) - V p)
  have hW : Measurable W :=
    ((hF.comp hshift).sub hV).indicator (measurableSet_Ioc.preimage measurable_fst)
  have hW2 : MemLp W 2
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict K)) :=
    (hFs.sub hVs).indicator (measurableSet_Ioc.preimage measurable_fst)
  apply hW2.ae_eq
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hW hX)).mpr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  by_cases hp : 0 < s
  · filter_upwards [heX s hp.le hs.2] with x hx
    rw [show W (s, x) = F (s, translate x ω) - V (s, x) from
      indicator_of_mem (show (s, x) ∈ {p : ℝ × Vec d | p.1 ∈ Ioc (0 : ℝ) 1}
        from ⟨hp, hs.2⟩) _]
    exact hx.symm
  · exact ae_of_all _ fun x => by
      rw [show W (s, x) = 0 from indicator_of_notMem
        (show (s, x) ∉ {p : ℝ × Vec d | p.1 ∈ Ioc (0 : ℝ) 1}
          from fun ht => hp ht.1) _, hX0 s (le_of_not_gt hp) x]

end EinsteinFull.Blueprint
