import EinsteinFull.Calculus.C1CrudeEnergySupport
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_local_u23_crude_u2D_energy
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_point_u2D_kernel
import EinsteinFull.Calculus.ComplexForcedGradientSupport
import EinsteinFull.Calculus.C1EndpointFiniteP

/-! Support for the crude-energy reduction, paper/main.tex:713–715.
The physical-to-stationary evolution identification and the time interval
`1 ≤ t < 2` remain open. No complete node reduction is asserted here. -/

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual uncentered velocity endpoint has a single horizontal-gradient
family at every positive time, without using the local-time graph Prop. -/
theorem crudeEnergy_velocity_gradient {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P) (k : Fin d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < t →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q (.inl k) ζ P Pdag β a μ t) (G t) := by
  let f := β k + ζ • a ⟨0, by omega⟩ k
  refine ⟨fun t j => if ht : 0 < t then hP.forcedGradient t ht f j else 0, ?_⟩
  intro t ht
  simpa only [uncenteredEndpoint, ht, ↓reduceDIte] using hP.forcedGradient_spec t ht f

/-- The actual force-weighted clock endpoint has a single horizontal-gradient
family for all positive times and every complex force, including zero. -/
theorem crudeEnergy_clock_gradient {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < t →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q (.inr false) ζ P Pdag β a μ t) (G t) := by
  refine ⟨fun t j => if ht : 0 < t then ζ • hP.forcedGradient t ht μ j else 0, ?_⟩
  intro t ht j
  simpa only [uncenteredEndpoint, ht, ↓reduceDIte] using (hP.forcedGradient_spec t ht μ j).smul ζ

/-- Each actual uncentered endpoint evolves from its earlier value with its
own forward or bilinear-transpose semigroup. No physical-space identification
or estimate is supplied by this composition identity. -/
theorem crudeEnergy_uncenteredEndpoint_add {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (s t : ℝ≥0) :
    uncenteredEndpoint hd Q ν ζ P Pdag β a μ (s + t) =
      (if ν = .inr true then Pdag s else P s)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) := by
  cases ν with
  | inl k =>
      simp only [uncenteredEndpoint, Sum.inl_ne_inr, ↓reduceIte,
        hP.2.1, ContinuousLinearMap.comp_apply]
  | inr b =>
      cases b with
      | false =>
          simp only [uncenteredEndpoint, Sum.inr.injEq, Bool.false_eq_true,
            ↓reduceIte, hP.2.1, ContinuousLinearMap.comp_apply, map_smul]
      | true =>
          simp only [uncenteredEndpoint, ↓reduceIte, transposeEndpoint,
            hPdag.add hP, ContinuousLinearMap.comp_apply]

/-- One structural constant bounds the actual initial data for every endpoint,
uniformly on the force disc. This supplies bounded data, not an evolution
estimate or a physical/stationary identification. -/
theorem crudeEnergy_initial_data_bound (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
      (∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q,
        ‖(β j + ζ • a ⟨0, by omega⟩ j) ω‖ ≤ B) ∧
      (∀ j : Fin d, ∀ᵐ ω ∂reducedLaw Q, ‖β j ω‖ ≤ B) ∧
      (∀ᵐ ω ∂reducedLaw Q, ‖(ζ • μ) ω‖ ≤ B) := by
  obtain ⟨K, hK, hb⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨5 * K, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ
  obtain ⟨hβb, hab, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  refine ⟨?_, ?_, ?_⟩
  · intro j
    filter_upwards [hβb j, hab ⟨0, by omega⟩ j,
      Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
      Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j)] with ω hβω haω hadd hsmul
    simp only [Pi.add_apply, Pi.smul_apply] at hadd hsmul
    rw [hadd, hsmul]
    calc
      _ ≤ ‖β j ω‖ + ‖ζ • a ⟨0, by omega⟩ j ω‖ := norm_add_le _ _
      _ = ‖β j ω‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ j ω‖ := by rw [norm_smul]
      _ ≤ K + 4 * K := add_le_add hβω
        (mul_le_mul hζ haω (norm_nonneg _) (by norm_num))
      _ = 5 * K := by ring
  · intro j
    filter_upwards [hβb j] with ω hω
    exact hω.trans (by linarith)
  · filter_upwards [hμb, Lp.coeFn_smul ζ μ] with ω hω hsmul
    simp only [Pi.smul_apply] at hsmul
    rw [hsmul, norm_smul]
    exact (mul_le_mul hζ hω (norm_nonneg _) (by norm_num)).trans (by linarith)

/-- Apply the literal physical point-kernel estimate to bounded stationary
data along the actual translation orbit. Constants precede the law and datum;
one environment event covers every force, direction and physical evolution.
This does not construct those evolutions or identify them with stationary P. -/
theorem crudeEnergy_stationaryData_kernel_bound
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
      ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
        IsPhysicalComplexSemigroup ω.1 i ζ P →
        IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
      ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
        IsPhysicalComplexKernel P Pdag K ∧
        ∀ H ∈ [K, fun t x y => K t y x],
        ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) →
          let u := fun x => ∫ y, H t x y * f (translate y ω)
          Differentiable ℝ u ∧ ∀ x : Vec d,
            ‖u x‖ + Real.sqrt (∑ j : Fin d,
              ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
  obtain ⟨C, c, N, hC, _hc, hk⟩ := hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ f B hB hf
  let := reducedLaw_probability Q
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [hk Q hQ, horbit] with ω hω hfω
  intro i ζ hζ P Pdag hP hPdag
  obtain ⟨K, hK, hreg⟩ := hω i ζ hζ P Pdag hP hPdag
  refine ⟨K, hK, ?_⟩
  intro H hH t ht
  have htrans : Continuous (fun y : Vec d => translate y ω) :=
    Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp htrans.measurable).aestronglyMeasurable
  have hb := (hreg H hH t ht).2.2 (fun y => f (translate y ω)) B hB hfm hfω
  exact ⟨hb.1, fun x => (hb.2 x).2.2⟩

/-- The actual uncentered endpoint at zero has one structural bound for all
indices and every force in the prescribed disc. -/
theorem crudeEnergy_initial_endpoint_bound (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ B : ℝ, 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∀ᵐ ω ∂reducedLaw Q, ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 ω‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := crudeEnergy_initial_data_bound d hd D
  refine ⟨B, hB, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  obtain ⟨hv, ht, hc⟩ := hb Q hQ β a μ hβ ha hμ ζ hζ
  cases ν with
  | inl j => simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply] using hv j
  | inr b =>
    cases b with
    | false => simpa only [uncenteredEndpoint, hP.1, ContinuousLinearMap.id_apply] using hc
    | true => simpa only [uncenteredEndpoint, transposeEndpoint, hPdag.zero hP,
        ContinuousLinearMap.id_apply] using ht ⟨0, by omega⟩

/-- The sole point-kernel dependency controls the physical evolutions of each
actual endpoint's initial data with structural constants before the law and
force. Physical-to-stationary evolution identification is still separate. -/
theorem crudeEnergy_endpointData_kernel_bound
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ, ‖ζ‖ ≤ 4 →
    ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup ω.1 ⟨0, by omega⟩ ζ S →
      IsPhysicalComplexTransposeSemigroup ω.1 ⟨0, by omega⟩ ζ S Sdag →
    ∃ K : ℝ≥0 → Vec d → Vec d → ℂ,
      IsPhysicalComplexKernel S Sdag K ∧
      ∀ H ∈ [K, fun t x y => K t y x], ∀ t : ℝ≥0, 2 ≤ (t : ℝ) →
        let u := fun x => ∫ y, H t x y *
          uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 (translate y ω)
        Differentiable ℝ u ∧ ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨A, N, hA, hk⟩ := crudeEnergy_stationaryData_kernel_bound hkernel d hd D
  obtain ⟨B, hB, hb⟩ := crudeEnergy_initial_endpoint_bound d hd D
  let C := A * (1 + B)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  have hAC : A ≤ C := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ 1 + B by linarith) hA0
  have hAB : A * B ≤ C :=
    mul_le_mul_of_nonneg_left (by linarith : B ≤ 1 + B) hA0
  refine ⟨C, N, hA.trans hAC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  have hf := hb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  filter_upwards [hk Q hQ (uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0) B hB.le hf]
    with ω hω
  intro S Sdag hS hSdag
  obtain ⟨K, hK, hreg⟩ := hω ⟨0, by omega⟩ ζ hζ S Sdag hS hSdag
  refine ⟨K, hK, ?_⟩
  intro H hH t ht
  obtain ⟨hdiff, hbound⟩ := hreg H hH t ht
  refine ⟨hdiff, fun x => (hbound x).trans ?_⟩
  calc
    _ = (A * B) * (2 + (t : ℝ)) ^ N * Real.exp (A * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
    _ ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_right hAB (pow_nonneg (by positivity) N)
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hAC (sq_nonneg _)) t.coe_nonneg
      · exact Real.exp_nonneg _
      · exact mul_nonneg (hA0.trans hAC) (pow_nonneg (by positivity) N)

end EinsteinFull.Blueprint
