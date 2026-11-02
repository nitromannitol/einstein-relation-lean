import EinsteinFull.Blueprint.G2.Proofs.C1CrudeEnergy
import EinsteinFull.Calculus.C4PhysicalForwardTimePrimitive
import EinsteinFull.Calculus.C8PhysicalTransposeTimePrimitive
import EinsteinFull.Calculus.C2RetainedPhysicalMeasurableEvolution
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.S5EnergySupport
import EinsteinFull.Calculus.C2LocallyH1ForcedGaussianEnergy
import EinsteinFull.Calculus.C1StationaryGaussianOrbitL2
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinRelation.Correctors.PairedCorrectorEquation
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/-- Actual smooth reduced environments admit physical forward and transpose
C0 evolutions on one environment event, before direction and complex force. -/
theorem crudeEnergy_ae_exists_physical_pair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (i : Fin d) (ζ : ℂ),
      ∃ S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalComplexSemigroup ω.1 i ζ S ∧
        IsPhysicalComplexTransposeSemigroup ω.1 i ζ S Sdag := by
  have hΛ : 1 ≤ Λ₀ := Q.ellipticity_parameter
  have hL : 1 ≤ Real.exp (2 * Λ₀) * Λ₀ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ :=
        mul_le_mul (Real.one_le_exp (by linarith)) hΛ zero_le_one (Real.exp_nonneg _)
  filter_upwards [c4_ae_reduced_physical_elliptic Q] with ω hω
  intro i ζ
  have ha : Measurable (fun p : Unit × Vec d => ω.1 p.2) :=
    ω.1.continuous.measurable.comp measurable_snd
  obtain ⟨S, Sdag, hS, _⟩ := retained_physical_complex_measurable_evolution
    (Ω := Unit) d i ζ (Real.exp (2 * Λ₀) * Λ₀) hL (fun _ => ω.1) ha
    (fun _ x => s5Elliptic_of_isElliptic hL hω x)
  exact ⟨S (), Sdag (), hS ()⟩

/-- The point-kernel dependency yields actual physical kernel convolutions of
every endpoint's initial data. Physical evolutions are constructed internally;
identification with the stationary endpoint at positive time remains separate. -/
theorem crudeEnergy_exists_endpoint_physical_kernel
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
      ∃ (S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)))
        (K : ℝ≥0 → Vec d → Vec d → ℂ),
        IsPhysicalComplexSemigroup ω.1 ⟨0, by omega⟩ ζ S ∧
        IsPhysicalComplexTransposeSemigroup ω.1 ⟨0, by omega⟩ ζ S Sdag ∧
        IsPhysicalComplexKernel S Sdag K ∧
        ∀ H ∈ [K, fun t x y => K t y x], ∀ t : ℝ≥0, 2 ≤ (t : ℝ) →
          let u := fun x => ∫ y, H t x y *
            uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 (translate y ω)
          Differentiable ℝ u ∧ ∀ x : Vec d,
            ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
              C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  obtain ⟨C, N, hC, hk⟩ := crudeEnergy_endpointData_kernel_bound hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  filter_upwards [hk Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν,
    crudeEnergy_ae_exists_physical_pair Q] with ω hω hex
  obtain ⟨S, Sdag, hS, hSdag⟩ := hex ⟨0, by omega⟩ ζ
  obtain ⟨K, hK, hb⟩ := hω S Sdag hS hSdag
  exact ⟨S, Sdag, K, hS, hSdag, hK, hb⟩

/-- The literal Euclidean kernel gradient estimate controls every coordinate
line with the same constant, without a dimension-dependent norm conversion. -/
theorem crudeEnergy_coordinate_lipschitz {d : ℕ} {u : Vec d → ℂ}
    (hu : Differentiable ℝ u) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ x, ‖u x‖ + Real.sqrt
      (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B)
    (x : Vec d) (j : Fin d) :
    LipschitzWith ⟨B, hB⟩ (fun s : ℝ => u (x + s • unitVector j)) := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => u (x + s • unitVector j))
      (fderiv ℝ u (x + s • unitVector j) (unitVector j)) s := by
    have hline := (((hasDerivAt_id s).smul_const (unitVector j)).const_add x)
    simpa only [Function.comp_def, id_eq, one_smul] using!
      (hu (x + s • unitVector j)).hasFDerivAt.comp_hasDerivAt s hline
  apply lipschitzWith_of_nnnorm_deriv_le (fun s => (hd s).differentiableAt)
  intro s
  rw [(hd s).deriv]
  change ‖fderiv ℝ u (x + s • unitVector j) (unitVector j)‖ ≤ B
  have hj : ‖fderiv ℝ u (x + s • unitVector j) (unitVector j)‖ ≤
      Real.sqrt (∑ k : Fin d, ‖fderiv ℝ u (x + s • unitVector j) (unitVector k)‖ ^ 2) :=
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (fun k _ => sq_nonneg
      ‖fderiv ℝ u (x + s • unitVector j) (unitVector k)‖) (Finset.mem_univ j))
  exact hj.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans (hb _))

/-- Actual endpoint kernel convolutions are uniformly Lipschitz on each
coordinate line, for both the forward and transposed kernels. -/
theorem crudeEnergy_exists_endpoint_physical_coordinate_lipschitz
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
      ∃ (S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d)))
        (K : ℝ≥0 → Vec d → Vec d → ℂ),
        IsPhysicalComplexSemigroup ω.1 ⟨0, by omega⟩ ζ S ∧
        IsPhysicalComplexTransposeSemigroup ω.1 ⟨0, by omega⟩ ζ S Sdag ∧
        IsPhysicalComplexKernel S Sdag K ∧
        ∀ H ∈ [K, fun t x y => K t y x], ∀ t : ℝ≥0, 2 ≤ (t : ℝ) →
          let u := fun x => ∫ y, H t x y *
            uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 (translate y ω)
          ∀ (x : Vec d) (j : Fin d),
            LipschitzWith (Real.toNNReal
              (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))))
              (fun s : ℝ => u (x + s • unitVector j)) := by
  obtain ⟨C, N, hC, hk⟩ := crudeEnergy_exists_endpoint_physical_kernel hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  filter_upwards [hk Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν] with ω hω
  obtain ⟨S, Sdag, K, hS, hSdag, hK, hb⟩ := hω
  refine ⟨S, Sdag, K, hS, hSdag, hK, ?_⟩
  intro H hH t ht
  dsimp only
  intro x j
  obtain ⟨hu, hub⟩ := hb H hH t ht
  have hB : 0 ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    positivity
  have he : Real.toNNReal
      (C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) =
      ⟨C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)), hB⟩ := by
    ext
    exact Real.coe_toNNReal _ hB
  rw [he]
  exact crudeEnergy_coordinate_lipschitz hu hB hub x j

/-- One actual endpoint gradient family exists for every positive time and
all complex forces. The transpose branch uses the smooth observed drift's
full generator domain, so it has no exceptional times. -/
theorem crudeEnergy_endpoint_gradient {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < t →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) := by
  cases ν with
  | inl k => exact crudeEnergy_velocity_gradient hd Q β a μ ζ P Pdag hP k
  | inr b =>
    cases b with
    | false => exact crudeEnergy_clock_gradient hd Q β a μ ζ P Pdag hP
    | true =>
      obtain ⟨G, _hGc, hG⟩ := timeFlux_transpose_continuous_gradient hβ hP hPdag
        ⟨0, by omega⟩
      refine ⟨G, fun t _ht => ?_⟩
      simpa only [uncenteredEndpoint, transposeEndpoint] using hG t

/-- The actual stationary endpoint has its initial trace in mean Gaussian
spatial energy. This supplies the zero initial defect before physical
comparison, without assuming a spatial L2 initial datum. -/
theorem crudeEnergy_endpoint_gaussian_initial_trace {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) (r : ℝ) :
    Tendsto (fun t : ℝ≥0 => ∫ x : Vec d, Real.exp (-euclideanSq x / r) ^ 2 *
      (∫ ω, ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t (translate x ω) -
        uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0 (translate x ω)‖ ^ 2
          ∂reducedLaw Q)) (𝓝 0) (𝓝 0) := by
  let u := fun t => uncenteredEndpoint hd Q ν ζ P Pdag β a μ t
  change Tendsto (fun t : ℝ≥0 => ∫ x : Vec d, Real.exp (-euclideanSq x / r) ^ 2 *
    (∫ ω, ‖u t (translate x ω) - u 0 (translate x ω)‖ ^ 2 ∂reducedLaw Q))
      (𝓝 0) (𝓝 0)
  have hc : Continuous u := by
    cases ν with
    | inl k => exact hP.2.2.1 _
    | inr b =>
      cases b with
      | false => exact (continuous_const (y := ζ)).smul (hP.2.2.1 μ)
      | true => exact hPdag.continuous_apply hP _
  have he (t : ℝ≥0) (x : Vec d) :
      (∫ ω, ‖u t (translate x ω) - u 0 (translate x ω)‖ ^ 2 ∂reducedLaw Q) =
        ‖u t - u 0‖ ^ 2 := by
    let F := fun ω => ‖u t ω - u 0 ω‖ ^ 2
    have hF : Measurable F :=
      (((Lp.stronglyMeasurable (u t)).measurable.sub
        (Lp.stronglyMeasurable (u 0)).measurable).norm.pow_const 2)
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
    have ht : (∫ ω, F (translate x ω) ∂reducedLaw Q) = ∫ ω, F ω ∂reducedLaw Q :=
      (integral_map hm.measurable.aemeasurable hF.aestronglyMeasurable).symm.trans
        (congrArg (fun m : Measure (FieldPair d) => ∫ ω, F ω ∂m) hm.map_eq)
    change (∫ ω, F (translate x ω) ∂reducedLaw Q) = _
    rw [ht]
    have hn : ‖u t - u 0‖ ^ 2 = ∫ ω, ‖(u t - u 0) ω‖ ^ 2 ∂reducedLaw Q := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    rw [hn]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u t) (u 0)] with ω hω
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2) hω.symm
  have hlim : Tendsto (fun t : ℝ≥0 => ‖u t - u 0‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
      ((hc.tendsto 0).sub (tendsto_const_nhds (x := u 0))).norm.pow 2
  have hh := hlim.const_mul (∫ x : Vec d, Real.exp (-euclideanSq x / r) ^ 2)
  simpa only [he, integral_mul_const, mul_zero] using hh

/-- Spatial Gaussian energy is integrable over environments and its mean
is the Gaussian mass times the stationary L2 norm squared. -/
private theorem crudeEnergy_integrable_gaussian_orbit_sq {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (κ : ℝ) (hκ : 0 < κ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
      ‖f (translate x ω)‖ ^ 2) (reducedLaw Q) ∧
    (∫ ω, (∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
      ‖f (translate x ω)‖ ^ 2) ∂reducedLaw Q) =
        (∫ x : Vec d, Real.exp (-κ * euclideanSq x)) * ‖f‖ ^ 2 := by
  have hf : Measurable f := (Lp.stronglyMeasurable f).measurable
  have hsq : Integrable (fun ω => ‖f ω‖ ^ 2) (reducedLaw Q) :=
    (Lp.memLp f).norm.integrable_sq
  have hn : ‖f‖ ^ 2 = ∫ ω, ‖f ω‖ ^ 2 ∂reducedLaw Q := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  have hsec (x : Vec d) : (∫ ω, ‖f (translate x ω)‖ ^ 2 ∂reducedLaw Q) =
      ‖f‖ ^ 2 := by
    rw [hn]
    have hm := measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x
    exact (integral_map hm.measurable.aemeasurable
      (hf.norm.pow_const 2).aestronglyMeasurable).symm.trans
        (congrArg (fun m : Measure (FieldPair d) => ∫ ω, ‖f ω‖ ^ 2 ∂m) hm.map_eq)
  let g : Vec d × FieldPair d → ℝ := fun p =>
    Real.exp (-κ * euclideanSq p.1) * ‖f (translate p.1 p.2)‖ ^ 2
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hgm : Measurable g :=
    (Real.continuous_exp.comp ((hs.comp continuous_fst).const_mul (-κ))).measurable.mul
      ((hf.comp Probability.continuous_translate.measurable).norm.pow_const 2)
  have hg : Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) volume := by
    have hp : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
      Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq]
  have hgi : Integrable g (volume.prod (reducedLaw Q)) := by
    apply (integrable_prod_iff hgm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => ?_), ?_⟩
    · simpa only [g, Function.comp_def] using
        ((measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).integrable_comp_of_integrable hsq).const_mul (Real.exp (-κ * euclideanSq x))
    · have heq (x : Vec d) : (∫ ω, ‖g (x, ω)‖ ∂reducedLaw Q) =
          Real.exp (-κ * euclideanSq x) * ‖f‖ ^ 2 := by
        simp only [g, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_pow, abs_norm, integral_const_mul, hsec]
      simpa only [heq] using
        hg.mul_const (‖f‖ ^ 2)
  refine ⟨hgi.integral_prod_right, ?_⟩
  rw [← integral_integral_swap hgi]
  simp only [integral_const_mul, hsec, integral_mul_const]

/-- Every time sequence tending to zero has a subsequence along which the
actual stationary endpoint defect has zero Gaussian spatial energy almost
surely. This is a physical initial trace, rather than an L2(dx) assumption. -/
theorem crudeEnergy_endpoint_gaussian_initial_trace_ae {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (κ : ℝ) (hκ : 0 < κ) (τ : ℕ → ℝ≥0) (hτ : Tendsto τ atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂reducedLaw Q,
      Tendsto (fun n => ∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖(uncenteredEndpoint hd Q ν ζ P Pdag β a μ (τ (ns n)) -
          uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0) (translate x ω)‖ ^ 2)
        atTop (𝓝 0) := by
  let u := fun t => uncenteredEndpoint hd Q ν ζ P Pdag β a μ t
  have hc : Continuous u := by
    cases ν with
    | inl k => exact hP.2.2.1 _
    | inr b =>
      cases b with
      | false => exact (continuous_const (y := ζ)).smul (hP.2.2.1 μ)
      | true => exact hPdag.continuous_apply hP _
  let F : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x : Vec d, Real.exp (-κ * euclideanSq x) * ‖(u (τ n) - u 0) (translate x ω)‖ ^ 2
  have hi (n : ℕ) := crudeEnergy_integrable_gaussian_orbit_sq Q κ hκ (u (τ n) - u 0)
  have hlim : Tendsto (fun n => ‖u (τ n) - u 0‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
      (((hc.tendsto 0).comp hτ).sub (tendsto_const_nhds (x := u 0))).norm.pow 2
  have hmean (n : ℕ) : (∫ ω, F n ω ∂reducedLaw Q) =
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x)) * ‖u (τ n) - u 0‖ ^ 2 := (hi n).2
  have hm : Tendsto (fun n => ∫ ω, F n ω ∂reducedLaw Q) atTop (𝓝 0) := by
    simpa only [hmean, mul_zero] using
      hlim.const_mul (∫ x : Vec d, Real.exp (-κ * euclideanSq x))
  have hn (n : ℕ) : eLpNorm (F n) 1 (reducedLaw Q) =
      ENNReal.ofReal (∫ ω, F n ω ∂reducedLaw Q) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).1.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n).1]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    exact Real.norm_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have he : Tendsto (fun n => eLpNorm (F n - 0) 1 (reducedLaw Q)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_zero, hn, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hm
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) he).exists_seq_tendsto_ae

/-- A joint stationary L2 path has integrable Gaussian spatial energy on
almost every physical spacetime section. -/
private theorem crudeEnergy_ae_gaussian_spacetime {T : Type*} [MeasurableSpace T]
    {ν : Measure T} [SFinite ν] {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (κ : ℝ) (hκ : 0 < κ)
    {u : T → Lp ℂ 2 (reducedLaw Q)}
    (hu : Integrable (fun t => ‖u t‖ ^ 2) ν)
    {U : T × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ t, (fun ω => U (t, ω)) =ᵐ[reducedLaw Q] u t) :
    ∀ᵐ ω ∂reducedLaw Q, Integrable (fun p : Vec d × T =>
      Real.exp (-κ * euclideanSq p.1) * ‖U (p.2, translate p.1 ω)‖ ^ 2)
        (volume.prod ν) := by
  have hi := integrable_sq_joint_l2_representative hu hU heU
  have hg : Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) volume := by
    have hp : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
        (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
      Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq]
  let F : Vec d × (T × FieldPair d) → ℝ := fun p =>
    Real.exp (-κ * euclideanSq p.1) * ‖U (p.2.1, translate p.1 p.2.2)‖ ^ 2
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hF : Measurable F :=
    (Real.continuous_exp.measurable.comp
      (measurable_const.mul (hs.measurable.comp measurable_fst))).mul
      ((hU.comp ((measurable_fst.comp measurable_snd).prodMk
        (Probability.continuous_translate.measurable.comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))).norm.pow_const 2)
  have hm (x : Vec d) : MeasurePreserving
      (fun p : T × FieldPair d => (p.1, translate x p.2))
      (ν.prod (reducedLaw Q)) (ν.prod (reducedLaw Q)) :=
    (MeasurePreserving.id ν).prod
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
  have hiF : Integrable F (volume.prod (ν.prod (reducedLaw Q))) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => ?_), ?_⟩
    · simpa only [F, Function.comp_def] using
        ((hm x).integrable_comp_of_integrable hi).const_mul
          (Real.exp (-κ * euclideanSq x))
    · have heq (x : Vec d) : (∫ p, ‖F (x, p)‖ ∂ν.prod (reducedLaw Q)) =
          Real.exp (-κ * euclideanSq x) * (∫ p, ‖U p‖ ^ 2 ∂ν.prod (reducedLaw Q)) := by
        simp only [F, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
          abs_pow, abs_norm, integral_const_mul]
        congr 1
        exact (integral_map (hm x).measurable.aemeasurable
          (hU.norm.pow_const 2).aestronglyMeasurable).symm.trans
            (congrArg (fun m => ∫ p, ‖U p‖ ^ 2 ∂m) (hm x).map_eq)
      simpa only [heq] using hg.mul_const (∫ p, ‖U p‖ ^ 2 ∂ν.prod (reducedLaw Q))
  have hassoc := (measurePreserving_prodAssoc volume ν (reducedLaw Q)).integrable_comp_of_integrable hiF
  exact hassoc.prod_left_ae

/-- Actual endpoints admit one joint representative whose Gaussian energy is
integrable on every finite integer time window, on one environment event. -/
theorem crudeEnergy_endpoint_gaussian_spacetime {d : ℕ} (hd : 2 ≤ d) {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q]
        uncenteredEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, Integrable (fun p : Vec d × ℝ =>
        Real.exp (-κ * euclideanSq p.1) * ‖U (p.2, translate p.1 ω)‖ ^ 2)
        (volume.prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) := by
  let u := fun t => uncenteredEndpoint hd Q ν ζ P Pdag β a μ t
  have hc : Continuous u := by
    cases ν with
    | inl k => exact hP.2.2.1 _
    | inr b =>
      cases b with
      | false => exact (continuous_const (y := ζ)).smul (hP.2.2.1 μ)
      | true => exact hPdag.continuous_apply hP _
  have hreal : Continuous (fun s : ℝ => u s.toNNReal) := hc.comp continuous_real_toNNReal
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative hreal.stronglyMeasurable
  refine ⟨U, hU, heU, ae_all_iff.mpr (fun n => ?_)⟩
  exact crudeEnergy_ae_gaussian_spacetime Q κ hκ
    ((hreal.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc) hU heU

/-- A differentiable stationary L2 path satisfies the physical time-energy
identity on all of space. The event is chosen before every absolutely
continuous temporal cutoff, including a spatially chosen Gaussian cutoff. -/
theorem crudeEnergy_ae_physical_time_energy {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (hv : Continuous v) {a b c : ℝ} (hab : a < b) (hbc : b ≤ c)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η b c →
        (∫ s in b..c, η s *
          (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
          η c * ‖(u c) (translate x ω)‖ ^ 2 - η b * ‖(u b) (translate x ω)‖ ^ 2 -
            ∫ s in b..c, deriv η s * ‖U (s, translate x ω)‖ ^ 2 := by
  have hi : IntegrableOn v (Icc b c) :=
    hv.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC : (∫ s in Icc b c, v s) = u c - u b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hd s (hab.trans_le ((uIcc_of_le hbc ▸ hs).1)))
      (hv.intervalIntegrable b c)
  have hc := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) hi hV heV
  rw [hFTC] at hc
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (u c - u b)).measurable
    ((Lp.stronglyMeasurable (u c)).measurable.sub (Lp.stronglyMeasurable (u b)).measurable)
    (Lp.coeFn_sub (u c) (u b))
  have hprim := ae_physical_primitive_of_joint_l2_derivative (reducedLaw Q)
    (reducedLaw_stationary Q) hU hV heU heV hv hab hd (c := c)
  have hgauss := crudeEnergy_ae_gaussian_spacetime (ν := volume.restrict (Icc b c))
    Q 1 zero_lt_one
    ((hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc (K := Icc b c)) hV heV
  filter_upwards [hprim, hc, hs, hgauss] with ω hprim hc hs hgauss
  filter_upwards [Measure.ae_ae_of_ae_prod hprim, hc, hs, hgauss.prod_right_ae]
    with x hx hc hs hsq
  have hsq' : IntegrableOn (fun s => ‖V (s, translate x ω)‖ ^ 2) (Icc b c) := by
    exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).mp hsq
  have hvmeas : Measurable (fun s => V (s, translate x ω)) :=
    hV.comp (measurable_id.prodMk measurable_const)
  have hvint : IntegrableOn (fun s => V (s, translate x ω)) (Icc b c) :=
    ((memLp_two_iff_integrable_sq_norm hvmeas.aestronglyMeasurable).mpr hsq').integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu : IntervalIntegrable (fun s => V (s, translate x ω)) volume b c := by
    have hi' : IntegrableOn (fun s => V (s, translate x ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using hvint
    exact hi'.intervalIntegrable
  have hend : (u b) (translate x ω) + (∫ s in b..c, V (s, translate x ω)) =
      (u c) (translate x ω) := by
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc, ← hc, hs]
    exact add_sub_cancel _ _
  intro η hη
  have heq : ∀ᵐ s ∂volume.restrict (Icc b c),
      U (s, translate x ω) = (u b) (translate x ω) +
        ∫ r in b..s, V (r, translate x ω) := by
    filter_upwards [hx, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  have hleft :
      (∫ s in b..c, η s * (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
      ∫ s in b..c, η s * (2 * (star ((u b) (translate x ω) +
        ∫ r in b..s, V (r, translate x ω)) * V (s, translate x ω)).re) := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  have hright : (∫ s in b..c, deriv η s * ‖U (s, translate x ω)‖ ^ 2) =
      ∫ s in b..c, deriv η s * ‖(u b) (translate x ω) +
        ∫ r in b..s, V (r, translate x ω)‖ ^ 2 := by
    rw [intervalIntegral.integral_of_le hbc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    exact integral_congr_ae (heq.mono fun s hs => by dsimp only; rw [hs])
  rw [hleft, hright]
  simpa only [hend] using complexPrimitive_weighted_energy hu ((u b) (translate x ω)) hη

private theorem crudeEnergy_ae_gaussian_endpoint {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {κ : ℝ} (hκ : 0 < κ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, Integrable (fun x : Vec d =>
      Real.exp (-κ * euclideanSq x) * ‖f (translate x ω)‖ ^ 2) volume := by
  have he := crudeEnergy_ae_gaussian_spacetime (ν := Measure.dirac (0 : ℝ))
    Q κ hκ (u := fun _ => f) (integrable_const _)
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd)
    (fun _ => Filter.EventuallyEq.rfl)
  filter_upwards [he] with ω hω
  simpa using hω.prod_left_ae

private theorem crudeEnergy_integrable_gaussian_cross {T : Type*} [MeasurableSpace T]
    (ν : Measure T) {d : ℕ} {κ M : ℝ} {X Y : Vec d × T → ℂ}
    {ψ : Vec d × T → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (hψ : Measurable ψ)
    (hψb : ∀ᵐ p ∂volume.prod ν, |ψ p| ≤ M * Real.exp (-κ * euclideanSq p.1))
    (hXsq : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖X p‖ ^ 2)
      (volume.prod ν))
    (hYsq : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖Y p‖ ^ 2)
      (volume.prod ν)) :
    Integrable (fun p => ψ p * (2 * (star (X p) * Y p).re)) (volume.prod ν) := by
  apply ((hXsq.add hYsq).const_mul M).mono'
    ((hψ.mul ((Complex.continuous_re.measurable.comp
      ((continuous_star.measurable.comp hX).mul hY)).const_mul 2)).aestronglyMeasurable)
  filter_upwards [hψb] with p hp
  have hg : 0 < Real.exp (-κ * euclideanSq p.1) := Real.exp_pos _
  have hM : 0 ≤ M := by nlinarith [abs_nonneg (ψ p), hp]
  have hre : |(star (X p) * Y p).re| ≤ ‖X p‖ * ‖Y p‖ := by
    simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (star (X p) * Y p)
  dsimp only [Pi.mul_apply, Pi.add_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hcross : 2 * |(star (X p) * Y p).re| ≤ ‖X p‖ ^ 2 + ‖Y p‖ ^ 2 := by
    nlinarith [sq_nonneg (‖X p‖ - ‖Y p‖)]
  have hm := mul_le_mul hp hcross (by positivity)
    (mul_nonneg hM hg.le)
  nlinarith only [hm]

/-- The full-space time-energy identity with a space-dependent cutoff dominated,
together with its time derivative, by an integrable Gaussian. -/
theorem crudeEnergy_ae_gaussian_time_energy {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (hu : Continuous u) (hv : Continuous v) {a b c : ℝ} (hab : a < b) (hbc : b ≤ c)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    {κ M : ℝ} (hκ : 0 < κ) {ψ ψ' : Vec d × ℝ → ℝ}
    (hψ : Measurable ψ) (hψ' : Measurable ψ')
    (hAC : ∀ x, AbsolutelyContinuousOnInterval (fun s => ψ (x, s)) b c)
    (hderiv : ∀ x s, s ∈ Icc b c → deriv (fun r => ψ (x, r)) s = ψ' (x, s))
    (hψb : ∀ x s, s ∈ Icc b c → |ψ (x, s)| ≤ M * Real.exp (-κ * euclideanSq x))
    (hψ'b : ∀ x s, s ∈ Icc b c → |ψ' (x, s)| ≤ M * Real.exp (-κ * euclideanSq x)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ s in Icc b c, ∫ x : Vec d, ψ (x, s) *
        (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
      (∫ x : Vec d, ψ (x, c) * ‖(u c) (translate x ω)‖ ^ 2) -
      (∫ x : Vec d, ψ (x, b) * ‖(u b) (translate x ω)‖ ^ 2) -
      ∫ s in Icc b c, ∫ x : Vec d, ψ' (x, s) * ‖U (s, translate x ω)‖ ^ 2 := by
  have hiU : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hiV : IntegrableOn (fun s => ‖v s‖ ^ 2) (Icc b c) :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  filter_upwards [crudeEnergy_ae_physical_time_energy Q hU hV heU heV hv hab hbc hd,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiU hU heU,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiV hV heV,
    crudeEnergy_ae_gaussian_endpoint Q hκ (u b),
    crudeEnergy_ae_gaussian_endpoint Q hκ (u c)] with ω htime hUsq hVsq hb hc
  let X : Vec d × ℝ → ℂ := fun p => U (p.2, translate p.1 ω)
  let Y : Vec d × ℝ → ℂ := fun p => V (p.2, translate p.1 ω)
  have hX : Measurable X := hU.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hY : Measurable Y := hV.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have htmem : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      p.2 ∈ Icc b c :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).mpr
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)
  have hbound : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      |ψ p| ≤ M * Real.exp (-κ * euclideanSq p.1) :=
    htmem.mono fun p hp => hψb p.1 p.2 hp
  have hA := crudeEnergy_integrable_gaussian_cross (volume.restrict (Icc b c))
    hX hY hψ hbound hUsq hVsq
  have hB : Integrable (fun p => ψ' p * ‖X p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))) := by
    apply (hUsq.const_mul M).mono' (hψ'.mul (hX.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [htmem] with p hp
    dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖X p‖)]
    nlinarith only [mul_le_mul_of_nonneg_right (hψ'b p.1 p.2 hp) (sq_nonneg ‖X p‖)]
  have hend (s : ℝ) (hmem : s ∈ Icc b c) (hs : Integrable (fun x : Vec d =>
      Real.exp (-κ * euclideanSq x) * ‖(u s) (translate x ω)‖ ^ 2) volume) :
      Integrable (fun x : Vec d => ψ (x, s) * ‖(u s) (translate x ω)‖ ^ 2) volume := by
    apply (hs.const_mul M).mono'
      ((hψ.comp (measurable_id.prodMk measurable_const)).mul
        (((Lp.stronglyMeasurable (u s)).measurable.comp
          (Probability.continuous_translate.measurable.comp
            (measurable_id.prodMk measurable_const))).norm.pow_const 2)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(u s) (translate x ω)‖)]
      nlinarith only [mul_le_mul_of_nonneg_right (hψb x s hmem)
        (sq_nonneg ‖(u s) (translate x ω)‖)]
  have heq : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ s in Icc b c, ψ (x, s) * (2 * (star (X (x, s)) * Y (x, s)).re)) =
        ψ (x, c) * ‖(u c) (translate x ω)‖ ^ 2 -
        ψ (x, b) * ‖(u b) (translate x ω)‖ ^ 2 -
        ∫ s in Icc b c, ψ' (x, s) * ‖X (x, s)‖ ^ 2 := by
    filter_upwards [htime] with x hx
    have he := hx (fun s => ψ (x, s)) (hAC x)
    rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc] at he
    have hdint : (∫ s in Icc b c, deriv (fun r => ψ (x, r)) s *
        ‖U (s, translate x ω)‖ ^ 2) =
        ∫ s in Icc b c, ψ' (x, s) * ‖U (s, translate x ω)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      rw [hderiv x s hs]
    rw [hdint] at he
    exact he
  have hsplit := integral_sub ((hend c ⟨hbc, le_rfl⟩ hc).sub (hend b ⟨le_rfl, hbc⟩ hb)) hB.integral_prod_left
  have hends := integral_sub (hend c ⟨hbc, le_rfl⟩ hc) (hend b ⟨le_rfl, hbc⟩ hb)
  simp only [Pi.sub_apply] at hsplit hends
  rw [← integral_integral_swap hA, integral_congr_ae heq, hsplit, hends,
    integral_integral_swap hB]

private theorem crudeEnergy_moving_gaussian_derivative {d : ℕ} (x : Vec d)
    {L s : ℝ} (hL : 0 < L) (hs : s < 2) :
    HasDerivAt (fun r : ℝ => Real.exp (-euclideanSq x / (L * (2 - r))) ^ 2)
      (-2 * euclideanSq x / (L * (2 - s) ^ 2) *
        Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2) s := by
  have hr : L * (2 - s) ≠ 0 := ne_of_gt (mul_pos hL (sub_pos.mpr hs))
  have hden := ((hasDerivAt_const s (2 : ℝ)).sub (hasDerivAt_id s)).const_mul L
  have hq := ((hasDerivAt_const s (-euclideanSq x)).div hden hr).exp.pow 2
  convert hq using 1
  · rfl
  · dsimp
    field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs)]
    ring

private theorem crudeEnergy_moving_gaussian_bounds {d : ℕ} (x : Vec d)
    {L b c s : ℝ} (hL : 0 < L) (hc : c < 2) (hs : s ∈ Icc b c) :
    let η := Real.exp (-euclideanSq x / (L * (2 - s)))
    let g := Real.exp (-(1 / (L * (2 - b))) * euclideanSq x)
    |η ^ 2| ≤ (1 + 2 / (2 - c)) * g ∧
      |(-2 * euclideanSq x / (L * (2 - s) ^ 2)) * η ^ 2| ≤
        (1 + 2 / (2 - c)) * g := by
  intro η g
  have hs2 : s < 2 := hs.2.trans_lt hc
  have hq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hden : 0 < L * (2 - s) := mul_pos hL (sub_pos.mpr hs2)
  have hη : 0 ≤ η ∧ η ≤ 1 := ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hden.le)⟩
  have hg : 0 ≤ g := Real.exp_nonneg _
  have hηg : η ≤ g := by
    apply Real.exp_le_exp.mpr
    have he := div_le_div_of_nonneg_left hq hden
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hs.1 2) hL.le)
    convert neg_le_neg he using 1 <;> ring
  have hqη : euclideanSq x * η ≤ L * (2 - s) := by
    have he := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * (2 - s)))).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
    have hm := mul_le_mul_of_nonneg_left he hden.le
    have heq : L * (2 - s) * (euclideanSq x / (L * (2 - s)) *
        Real.exp (-(euclideanSq x / (L * (2 - s))))) = euclideanSq x * η := by
      dsimp only [η]
      rw [neg_div]
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs2)]
    simpa only [heq, mul_one] using hm
  have hcoef : 2 / (2 - s) ≤ 2 / (2 - c) :=
    div_le_div_of_nonneg_left (by norm_num) (sub_pos.mpr hc)
      (sub_le_sub_left hs.2 2)
  have hM : 1 ≤ 1 + 2 / (2 - c) := by
    have hp : 0 ≤ 2 / (2 - c) := by positivity
    linarith only [hp]
  constructor
  · rw [abs_of_nonneg (sq_nonneg η)]
    calc
      η ^ 2 ≤ η := by nlinarith [hη.1, hη.2]
      _ ≤ g := hηg
      _ ≤ (1 + 2 / (2 - c)) * g := le_mul_of_one_le_left hg hM
  · have hneg : (-2 * euclideanSq x / (L * (2 - s) ^ 2)) * η ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (div_nonpos_of_nonpos_of_nonneg (by nlinarith only [hq]) (by positivity))
        (sq_nonneg η)
    rw [abs_of_nonpos hneg]
    calc
      _ = (2 / (L * (2 - s) ^ 2)) * (euclideanSq x * η) * η := by ring
      _ ≤ (2 / (L * (2 - s) ^ 2)) * (L * (2 - s)) * η :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqη (by positivity)) hη.1
      _ = (2 / (2 - s)) * η := by
        field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs2)]
      _ ≤ (2 / (2 - c)) * g := mul_le_mul hcoef hηg hη.1 (by positivity)
      _ ≤ (1 + 2 / (2 - c)) * g := by nlinarith only [hg]

/-- Backward moving-Gaussian temporal energy for the actual stationary L2 path.
The physical orbit need not belong to unweighted spatial L2. -/
theorem crudeEnergy_ae_moving_gaussian_time_energy {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (hu : Continuous u) (hv : Continuous v) {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2) (hL : 0 < L)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s) :
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    let W : ℝ → Vec d → ℝ := fun s x =>
      -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ s in Icc b c, ∫ x : Vec d, η s x ^ 2 *
        (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
      (∫ x : Vec d, η c x ^ 2 * ‖(u c) (translate x ω)‖ ^ 2) -
      (∫ x : Vec d, η b x ^ 2 * ‖(u b) (translate x ω)‖ ^ 2) -
      ∫ s in Icc b c, ∫ x : Vec d, W s x * ‖U (s, translate x ω)‖ ^ 2 := by
  intro η W
  have hb : b < 2 := hbc.trans_lt hc
  have hκ : 0 < 1 / (L * (2 - b)) := by positivity
  have hψ : Measurable (fun p : Vec d × ℝ => η p.2 p.1 ^ 2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hW : Measurable (fun p : Vec d × ℝ => W p.2 p.1) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  have hAC (x : Vec d) : AbsolutelyContinuousOnInterval (fun s => η s x ^ 2) b c := by
    have hsm : ContDiffOn ℝ 1 (fun s => η s x ^ 2) (uIcc b c) := by
      dsimp only [η]
      apply ContDiffOn.pow
      apply ContDiffOn.exp
      apply ContDiffOn.div contDiffOn_const
        (contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id))
      intro s hs
      rw [uIcc_of_le hbc] at hs
      exact ne_of_gt (mul_pos hL (sub_pos.mpr (hs.2.trans_lt hc)))
    exact hsm.absolutelyContinuousOnInterval
  exact crudeEnergy_ae_gaussian_time_energy Q hU hV heU heV hu hv hab hbc hd hκ hψ hW hAC
    (fun x s hs => (crudeEnergy_moving_gaussian_derivative x hL (hs.2.trans_lt hc)).deriv)
    (fun x s hs => (crudeEnergy_moving_gaussian_bounds x hL hc hs).1)
    (fun x s hs => (crudeEnergy_moving_gaussian_bounds x hL hc hs).2)

private theorem crudeEnergy_divergence_projection {d : ℕ} {F : Vec d → Fin d → ℂ}
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

/-- A stationary generator pair supplies its actual physical weak divergence
on one environment event, before the real projection is chosen. -/
theorem crudeEnergy_ae_generator_spatial_divergence
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ A : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
      (fun x j => A ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)))
      (fun x => A (g (translate x ω) -
        ζ * ∑ j, (ω.1 x j i : ℂ) * G j (translate x ω))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun j ω => (1 / 2 : ℂ) * ∑ k, (ω.1 0 j k : ℂ) * G k ω
  let b : FieldPair d → ℂ := fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω
  let q : FieldPair d → ℂ := fun ω => g ω - ζ * b ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) := measurable_const.mul
    (Finset.measurable_sum _ fun k _ => (hm j k).mul (Lp.stronglyMeasurable _).measurable)
  have hbm : Measurable b := Finset.measurable_sum _ fun j _ =>
    (hm j i).mul (Lp.stronglyMeasurable _).measurable
  have hb : MemLp b 2 (reducedLaw Q) := by
    apply memLp_finsetSum
    intro j _
    exact (Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
      (complexCoefficientMul_coe Q j i (G j))
  have hqm : Measurable q := (Lp.stronglyMeasurable g).measurable.sub (measurable_const.mul hbm)
  have hq : MemLp q 2 (reducedLaw Q) := (Lp.memLp g).sub (hb.const_mul ζ)
  have hF j : MemLp (F j) 2 (reducedLaw Q) := (memLp_complex_coefficient_flux Q G j).const_mul _
  have hw := ae_complex_spatial_divergence_all_tests (reducedLaw Q) (reducedLaw_stationary Q)
    F q hFm hqm hF hq (by
      intro v V hV
      have he := hfg.horizontal_flux hG v V hV
      have hg : Integrable (fun ω => g ω * v ω) (reducedLaw Q) :=
        (Lp.memLp g).integrable_mul (Lp.memLp v)
      have hd : Integrable (fun ω => b ω * v ω) (reducedLaw Q) :=
        hb.integrable_mul (Lp.memLp v)
      have heq : (fun ω => (2 * g ω - 2 * ζ *
          (∑ j, (ω.1 0 j i : ℂ) * G j ω)) * v ω) =
          (fun ω => 2 * (g ω * v ω) - (2 * ζ) * (b ω * v ω)) := by
        funext ω
        dsimp only [b]
        ring
      rw [heq, integral_sub (hg.const_mul 2) (hd.const_mul (2 * ζ)),
        integral_const_mul, integral_const_mul] at he
      have hqe : (fun ω => q ω * v ω) =
          (fun ω => g ω * v ω - ζ * (b ω * v ω)) := by
        funext ω
        dsimp only [q]
        ring
      rw [hqe, integral_sub hg (hd.const_mul ζ), integral_const_mul]
      simp only [F, mul_assoc, ← Finset.mul_sum, integral_const_mul]
      linear_combination (1 / 2 : ℂ) * he)
  filter_upwards [hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) hqm hq,
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j))]
    with ω hw hqω hFω
  intro A
  have he := crudeEnergy_divergence_projection (fun K hK j => hFω j K hK) hqω hw A
  simpa only [F, q, b, translate_matrix, add_zero] using he

/-- Actual stationary generator pairs obey the full-space Gaussian spatial
energy inequality on one event for every admissible width and remaining time.
The physical weak equation and weighted spatial integrability are derived from
the generator pair and stationarity. -/
theorem crudeEnergy_ae_generator_gaussian_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
      let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
      Integrable (fun x => η x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2) ∧
        Integrable (fun x => W x * ‖f (translate x ω)‖ ^ 2) ∧
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
          -2 * (∫ x, g (translate x ω) *
            (((η x ^ 2 : ℝ) : ℂ) * star (f (translate x ω)))).re +
          16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖f (translate x ω)‖ ^ 2) -
          ∫ x, W x * ‖f (translate x ω)‖ ^ 2 := by
  intro Λ
  have hΛ₀ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hΛ : 1 ≤ Λ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ := mul_le_mul
        (Real.one_le_exp (by positivity)) Q.ellipticity_parameter (by positivity) (by positivity)
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  filter_upwards [hG.ae_reduced_spatial Q,
    crudeEnergy_ae_generator_spatial_divergence hfg hG,
    c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_stationary_spatial_orbit_gaussian_memLp d Fact.out
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))]
    with ω hω hdiv ha hfL hgL hGL
  have hreal := hdiv Complex.reCLM
  have himag := hdiv Complex.imCLM
  intro L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have he := physical_locally_h1_forced_gaussian_energy (fun x => ω.1 x) i ζ
    (fun j k => memLp_complex_elliptic_entry _ _ Λ hΛp ha
      (fun j k => ω.1.continuous.matrix_elem j k) j k)
    (ae_of_all _ fun x => s5Elliptic_of_isElliptic hΛ ha x)
    (fun x => f (translate x ω)) (fun x => g (translate x ω))
    (fun j x => G j (translate x ω)) (fun _ _ => 0) hω.1 hω.2.1
    (by simpa only [sub_zero] using! hreal) (by simpa only [sub_zero] using! himag)
    hΛp hL hr (hfL (4 * L * r) (by positivity)) (hgL (4 * L * r) (by positivity))
    (fun j => hGL j (4 * L * r) (by positivity)) (fun _ => by simpa using (MemLp.zero :
      MemLp (0 : Vec d → ℂ) 2 volume))
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, integral_zero, add_zero] using he

/-- Joint representatives of an actual generator path satisfy the moving
Gaussian mass inequality for almost every environment and almost every time.
No joint gradient representative or global spatial L² assumption is needed. -/
theorem crudeEnergy_ae_joint_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c L : ℝ} (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    let W : ℝ → Vec d → ℝ := fun s x =>
      -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (∫ x, η s x ^ 2 * (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) +
        (∫ x, W s x * ‖U (s, translate x ω)‖ ^ 2) ≤
        16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η s x ^ 2 * ‖U (s, translate x ω)‖ ^ 2) := by
  intro Λ η W
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hshift {F : ℝ × FieldPair d → ℂ} (hF : Measurable F) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d =>
        F (q.1.1, translate q.2 q.1.2)) :=
    hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hη : Measurable (fun q : (ℝ × FieldPair d) × Vec d => η q.1.1 q.2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hW : Measurable (fun q : (ℝ × FieldPair d) × Vec d => W q.1.1 q.2) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  let A : ℝ × FieldPair d → ℝ := fun p =>
    (∫ x, η p.1 x ^ 2 * (2 * (star (U (p.1, translate x p.2)) * V (p.1, translate x p.2)).re)) +
      ∫ x, W p.1 x * ‖U (p.1, translate x p.2)‖ ^ 2
  let B : ℝ × FieldPair d → ℝ := fun p =>
    16 * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ x, η p.1 x ^ 2 * ‖U (p.1, translate x p.2)‖ ^ 2
  have hA : Measurable A := by
    apply Measurable.add
    · exact ((hη.pow_const 2).mul ((Complex.continuous_re.measurable.comp
        ((continuous_star.measurable.comp (hshift hU)).mul (hshift hV))).const_mul 2)).stronglyMeasurable.integral_prod_right'.measurable
    · exact (hW.mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hB : Measurable B := measurable_const.mul
    ((hη.pow_const 2).mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have heU' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hU.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heU s)
  have heV' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  filter_upwards [crudeEnergy_ae_generator_gaussian_energy (hgen s hs) (hgrad s hs),
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) (u s),
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) (v s),
    heU', heV'] with ω he hu hv heu hev
  have hr : 0 < 2 - s := sub_pos.mpr (hs.2.trans_lt hc)
  obtain ⟨_, _, henergy⟩ := he L (2 - s) hL hr
  have hZ : Integrable (fun x => (v s) (translate x ω) *
      (((η s x ^ 2 : ℝ) : ℂ) * star ((u s) (translate x ω)))) := by
    convert (hv (L * (2 - s)) (by positivity)).integrable_mul
      (hu (L * (2 - s)) (by positivity)).star using 1
    funext x
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal,
      η, Complex.ofReal_pow]
    ring
  have hcross : (∫ x, η s x ^ 2 *
      (2 * (star ((u s) (translate x ω)) * (v s) (translate x ω)).re)) =
      2 * (∫ x, (v s) (translate x ω) *
        (((η s x ^ 2 : ℝ) : ℂ) * star ((u s) (translate x ω)))).re := by
    have hre : (∫ x, ((v s) (translate x ω) *
        (((η s x ^ 2 : ℝ) : ℂ) * star ((u s) (translate x ω)))).re) =
        (∫ x, (v s) (translate x ω) *
          (((η s x ^ 2 : ℝ) : ℂ) * star ((u s) (translate x ω)))).re := by
      simpa using! integral_re hZ
    rw [← hre, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [mul_comm ((v s) (translate x ω)), mul_assoc, Complex.re_ofReal_mul]
      ring
  have hn : 0 ≤ (Λ⁻¹ / 4) * (∫ x, η s x ^ 2 * ∑ j, ‖G s j (translate x ω)‖ ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hmass : (∫ x, η s x ^ 2 *
      (2 * (star ((u s) (translate x ω)) * (v s) (translate x ω)).re)) +
      (∫ x, W s x * ‖(u s) (translate x ω)‖ ^ 2) ≤
      16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η s x ^ 2 * ‖(u s) (translate x ω)‖ ^ 2) := by
    rw [hcross]
    linarith only [henergy, hn]
  have hcross' : (∫ x, η s x ^ 2 * (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) =
      ∫ x, η s x ^ 2 * (2 * (star ((u s) (translate x ω)) * (v s) (translate x ω)).re) := by
    apply integral_congr_ae
    filter_upwards [heu, hev] with x hx hy
    change U (s, translate x ω) = _ at hx
    change V (s, translate x ω) = _ at hy
    rw [hx, hy]
  have hsq (ψ : Vec d → ℝ) : (∫ x, ψ x * ‖U (s, translate x ω)‖ ^ 2) =
      ∫ x, ψ x * ‖(u s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [heu] with x hx
    change U (s, translate x ω) = _ at hx
    rw [hx]
  dsimp only [A, B]
  rw [hcross', hsq, hsq]
  exact hmass

/-- Integrating the actual stationary generator equation against the backward
moving Gaussian yields a mass estimate with its literal endpoint energies.
The moving-weight term cancels internally against the spatial energy estimate. -/
theorem crudeEnergy_ae_integrated_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω)‖ ^ 2) ≤
        (∫ x, η b x ^ 2 * ‖(u b) (translate x ω)‖ ^ 2) +
          16 * Λ ^ 3 * ‖ζ‖ ^ 2 *
            ∫ s in Icc b c, ∫ x, η s x ^ 2 * ‖U (s, translate x ω)‖ ^ 2 := by
  intro Λ η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hb : b < 2 := hbc.trans_lt hc
  let κ : ℝ := 1 / (L * (2 - b))
  let M : ℝ := 1 + 2 / (2 - c)
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hiU : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hiV : IntegrableOn (fun s => ‖v s‖ ^ 2) (Icc b c) :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  filter_upwards [crudeEnergy_ae_moving_gaussian_time_energy Q hU hV heU heV hu hv hab hbc hc hLp hd,
    crudeEnergy_ae_joint_gaussian_mass hc hL hgen hgrad hU hV heU heV,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiU hU heU,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiV hV heV]
    with ω htime hmass hUsq hVsq
  let X : Vec d × ℝ → ℂ := fun p => U (p.2, translate p.1 ω)
  let Y : Vec d × ℝ → ℂ := fun p => V (p.2, translate p.1 ω)
  let W : Vec d × ℝ → ℝ := fun p =>
    -2 * euclideanSq p.1 / (L * (2 - p.2) ^ 2) * η p.2 p.1 ^ 2
  have hX : Measurable X := hU.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hY : Measurable Y := hV.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hη : Measurable (fun p : Vec d × ℝ => η p.2 p.1 ^ 2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hW : Measurable W := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  have htmem : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      p.2 ∈ Icc b c :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).mpr
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)
  have hηb : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      |η p.2 p.1 ^ 2| ≤ M * Real.exp (-κ * euclideanSq p.1) :=
    htmem.mono fun p hp => (crudeEnergy_moving_gaussian_bounds p.1 hLp hc hp).1
  have hWb : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      |W p| ≤ M * Real.exp (-κ * euclideanSq p.1) :=
    htmem.mono fun p hp => (crudeEnergy_moving_gaussian_bounds p.1 hLp hc hp).2
  have hweighted (ψ : Vec d × ℝ → ℝ) (hψ : Measurable ψ)
      (hbound : ∀ᵐ p ∂volume.prod (volume.restrict (Icc b c)),
        |ψ p| ≤ M * Real.exp (-κ * euclideanSq p.1)) :
      Integrable (fun p => ψ p * ‖X p‖ ^ 2) (volume.prod (volume.restrict (Icc b c))) := by
    apply (hUsq.const_mul M).mono' (hψ.mul (hX.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [hbound] with p hp
    dsimp only [Pi.mul_apply, Function.comp_apply, id_eq]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖X p‖)]
    nlinarith only [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖X p‖)]
  have hA := crudeEnergy_integrable_gaussian_cross (volume.restrict (Icc b c))
    hX hY hη hηb hUsq hVsq
  have hB := hweighted W hW hWb
  have hE := hweighted (fun p => η p.2 p.1 ^ 2) hη hηb
  have hint := integral_mono_ae (hA.integral_prod_right.add hB.integral_prod_right)
    (hE.integral_prod_right.const_mul (16 * Λ ^ 3 * ‖ζ‖ ^ 2)) hmass
  simp only [Pi.add_apply, Pi.mul_apply] at hint
  rw [integral_add hA.integral_prod_right hB.integral_prod_right, integral_const_mul] at hint
  change (∫ s in Icc b c, ∫ x, η s x ^ 2 *
      (2 * (star (U (s, translate x ω)) * V (s, translate x ω)).re)) +
      (∫ s in Icc b c, ∫ x, W (x, s) * ‖U (s, translate x ω)‖ ^ 2) ≤
      16 * Λ ^ 3 * ‖ζ‖ ^ 2 *
        ∫ s in Icc b c, ∫ x, η s x ^ 2 * ‖U (s, translate x ω)‖ ^ 2 at hint
  rw [htime] at hint
  linarith only [hint]

/-- The actual stationary path is a physical time primitive, with its two
endpoint representatives retained on the same almost-everywhere event. -/
theorem crudeEnergy_ae_physical_time_primitive {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (hv : Continuous v) {a b c : ℝ} (hab : a < b) (hbc : b ≤ c)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (u b) (translate x ω) + (∫ s in b..c, V (s, translate x ω)) =
        (u c) (translate x ω) ∧
      ∀ᵐ s ∂volume.restrict (Icc b c), U (s, translate x ω) =
        (u b) (translate x ω) + ∫ r in b..s, V (r, translate x ω) := by
  have hi : IntegrableOn v (Icc b c) :=
    hv.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC : (∫ s in Icc b c, v s) = u c - u b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hbc]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s hs => hd s (hab.trans_le ((uIcc_of_le hbc ▸ hs).1)))
      (hv.intervalIntegrable b c)
  have hc := ae_spatial_coeFn_integral_joint_l2_representative
    (reducedLaw Q) (reducedLaw_stationary Q) hi hV heV
  rw [hFTC] at hc
  have hs := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (u c - u b)).measurable
    ((Lp.stronglyMeasurable (u c)).measurable.sub (Lp.stronglyMeasurable (u b)).measurable)
    (Lp.coeFn_sub (u c) (u b))
  have hp := ae_physical_primitive_of_joint_l2_derivative (reducedLaw Q)
    (reducedLaw_stationary Q) hU hV heU heV hv hab hd (c := c)
  filter_upwards [hc, hs, hp] with ω hc hs hp
  filter_upwards [hc, hs, Measure.ae_ae_of_ae_prod hp] with x hc hs hp
  constructor
  · rw [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc, ← hc, hs]
    exact add_sub_cancel _ _
  · filter_upwards [hp, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]

/-- Gaussian time integration for a physical time primitive.  The hypotheses
are stable under subtraction of a stationary orbit and a physical L² orbit;
only Gaussian weighted space-time integrability is required. -/
theorem crudeEnergy_gaussian_primitive_time_energy {d : ℕ} {b c κ M : ℝ}
    (hbc : b ≤ c) {U V : Vec d × ℝ → ℂ} {u₀ u₁ : Vec d → ℂ}
    (hU : Measurable U) (hV : Measurable V)
    (h₀ : Measurable u₀) (h₁ : Measurable u₁)
    (hUsq : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖U p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hVsq : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖V p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hi₀ : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖u₀ x‖ ^ 2) volume)
    (hi₁ : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖u₁ x‖ ^ 2) volume)
    (hprim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      u₀ x + (∫ s in b..c, V (x, s)) = u₁ x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c),
        U (x, s) = u₀ x + ∫ r in b..s, V (x, r))
    {ψ ψ' : Vec d × ℝ → ℝ} (hψ : Measurable ψ) (hψ' : Measurable ψ')
    (hAC : ∀ x, AbsolutelyContinuousOnInterval (fun s => ψ (x, s)) b c)
    (hderiv : ∀ x s, s ∈ Icc b c → deriv (fun r => ψ (x, r)) s = ψ' (x, s))
    (hψb : ∀ x s, s ∈ Icc b c → |ψ (x, s)| ≤ M * Real.exp (-κ * euclideanSq x))
    (hψ'b : ∀ x s, s ∈ Icc b c → |ψ' (x, s)| ≤ M * Real.exp (-κ * euclideanSq x)) :
    (∫ s in Icc b c, ∫ x, ψ (x, s) * (2 * (star (U (x, s)) * V (x, s)).re)) =
      (∫ x, ψ (x, c) * ‖u₁ x‖ ^ 2) - (∫ x, ψ (x, b) * ‖u₀ x‖ ^ 2) -
        ∫ s in Icc b c, ∫ x, ψ' (x, s) * ‖U (x, s)‖ ^ 2 := by
  have htmem : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      p.2 ∈ Icc b c :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).mpr
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)
  have hA := crudeEnergy_integrable_gaussian_cross (volume.restrict (Icc b c))
    hU hV hψ (htmem.mono fun p hp => hψb p.1 p.2 hp) hUsq hVsq
  have hB : Integrable (fun p => ψ' p * ‖U p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))) := by
    apply (hUsq.const_mul M).mono' (hψ'.mul (hU.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [htmem] with p hp
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖U p‖)]
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (hψ'b p.1 p.2 hp) (sq_nonneg ‖U p‖)
  have hend (s : ℝ) (hs : s ∈ Icc b c) (u : Vec d → ℂ) (hu : Measurable u)
      (hi : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖u x‖ ^ 2) volume) :
      Integrable (fun x => ψ (x, s) * ‖u x‖ ^ 2) volume := by
    apply (hi.const_mul M).mono'
      ((hψ.comp (measurable_id.prodMk measurable_const)).mul
        (hu.norm.pow_const 2)).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      dsimp only [Pi.mul_apply]
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u x‖)]
      simpa only [mul_assoc, Function.comp_apply, id_eq] using
        mul_le_mul_of_nonneg_right (hψb x s hs) (sq_nonneg ‖u x‖)
  have heq : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ s in Icc b c, ψ (x, s) * (2 * (star (U (x, s)) * V (x, s)).re)) =
        ψ (x, c) * ‖u₁ x‖ ^ 2 - ψ (x, b) * ‖u₀ x‖ ^ 2 -
          ∫ s in Icc b c, ψ' (x, s) * ‖U (x, s)‖ ^ 2 := by
    filter_upwards [hprim, hVsq.prod_right_ae] with x hx hsq
    have hsq' : IntegrableOn (fun s => ‖V (x, s)‖ ^ 2) (Icc b c) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).mp hsq
    have hvint : IntegrableOn (fun s => V (x, s)) (Icc b c) :=
      ((memLp_two_iff_integrable_sq_norm
        (hV.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hsq').integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hint : IntervalIntegrable (fun s => V (x, s)) volume b c := by
      have hi : IntegrableOn (fun s => V (x, s)) (uIcc b c) := by
        simpa only [uIcc_of_le hbc] using hvint
      exact hi.intervalIntegrable
    have he := complexPrimitive_weighted_energy hint (u₀ x) (hAC x)
    dsimp only at he
    rw [hx.1, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hbc,
      ← integral_Icc_eq_integral_Ioc] at he
    have hleft : (∫ s in Icc b c, ψ (x, s) *
        (2 * (star (U (x, s)) * V (x, s)).re)) =
        ∫ s in Icc b c, ψ (x, s) *
          (2 * (star (u₀ x + ∫ r in b..s, V (x, r)) * V (x, s)).re) := by
      exact integral_congr_ae (hx.2.mono fun s hs => by simp only [hs])
    have hright : (∫ s in Icc b c, ψ' (x, s) * ‖U (x, s)‖ ^ 2) =
        ∫ s in Icc b c, deriv (fun r => ψ (x, r)) s *
          ‖u₀ x + ∫ r in b..s, V (x, r)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [hx.2, ae_restrict_mem measurableSet_Icc] with s hs hmem
      simp only [hs, hderiv x s hmem]
    rw [hleft, hright]
    exact he
  have hi₀' := hend b ⟨le_rfl, hbc⟩ u₀ h₀ hi₀
  have hi₁' := hend c ⟨hbc, le_rfl⟩ u₁ h₁ hi₁
  have hsplit := integral_sub (hi₁'.sub hi₀') hB.integral_prod_left
  have hends := integral_sub hi₁' hi₀'
  simp only [Pi.sub_apply] at hsplit hends
  rw [← integral_integral_swap hA, integral_congr_ae heq, hsplit, hends,
    integral_integral_swap hB]

/-- Gaussian square-integrability is preserved by taking a physical orbit
minus a second orbit; neither orbit needs to be in unweighted spatial L². -/
theorem crudeEnergy_integrable_weighted_sub_sq {T : Type*} [MeasurableSpace T]
    (ν : Measure T) {w : T → ℝ} {X Y : T → ℂ}
    (hw : Measurable w) (hw₀ : ∀ p, 0 ≤ w p)
    (hX : Measurable X) (hY : Measurable Y)
    (hiX : Integrable (fun p => w p * ‖X p‖ ^ 2) ν)
    (hiY : Integrable (fun p => w p * ‖Y p‖ ^ 2) ν) :
    Integrable (fun p => w p * ‖X p - Y p‖ ^ 2) ν := by
  apply ((hiX.add hiY).const_mul 2).mono'
    (hw.mul ((hX.sub hY).norm.pow_const 2)).aestronglyMeasurable
  exact ae_of_all _ fun p => by
    dsimp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw₀ p) (sq_nonneg _))]
    have hsq : ‖X p - Y p‖ ^ 2 ≤ 2 * (‖X p‖ ^ 2 + ‖Y p‖ ^ 2) := by
      have h := mul_self_le_mul_self (norm_nonneg (X p - Y p)) (norm_sub_le (X p) (Y p))
      nlinarith [sq_nonneg (‖X p‖ - ‖Y p‖)]
    have h := mul_le_mul_of_nonneg_left hsq (hw₀ p)
    nlinarith only [h]

/-- Time primitives of two Gaussian-integrable physical paths subtract on one
spatial event, including both exact endpoint values. -/
theorem crudeEnergy_gaussian_time_primitive_sub {d : ℕ} {b c κ : ℝ}
    (hbc : b ≤ c) {U V F H : Vec d × ℝ → ℂ} {u₀ u₁ v₀ v₁ : Vec d → ℂ}
    (hF : Measurable F) (hH : Measurable H)
    (hiF : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖F p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hiH : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖H p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hu : ∀ᵐ x ∂(volume : Measure (Vec d)),
      u₀ x + (∫ s in b..c, F (x, s)) = u₁ x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c), U (x, s) = u₀ x + ∫ r in b..s, F (x, r))
    (hv : ∀ᵐ x ∂(volume : Measure (Vec d)),
      v₀ x + (∫ s in b..c, H (x, s)) = v₁ x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c), V (x, s) = v₀ x + ∫ r in b..s, H (x, r)) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      (u₀ x - v₀ x) + (∫ s in b..c, F (x, s) - H (x, s)) = u₁ x - v₁ x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c),
        U (x, s) - V (x, s) = (u₀ x - v₀ x) + ∫ r in b..s, F (x, r) - H (x, r) := by
  have timeint (A : Vec d × ℝ → ℂ) (hA : Measurable A)
      (hiA : Integrable (fun p => Real.exp (-κ * euclideanSq p.1) * ‖A p‖ ^ 2)
        (volume.prod (volume.restrict (Icc b c)))) :
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        IntervalIntegrable (fun s => A (x, s)) volume b c := by
    filter_upwards [hiA.prod_right_ae] with x hx
    have hsq : IntegrableOn (fun s => ‖A (x, s)‖ ^ 2) (Icc b c) :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.exp_ne_zero _)) _).mp hx
    have hi : IntegrableOn (fun s => A (x, s)) (Icc b c) :=
      ((memLp_two_iff_integrable_sq_norm
        (hA.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable).mpr hsq).integrable
        (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hi' : IntegrableOn (fun s => A (x, s)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using hi
    exact hi'.intervalIntegrable
  filter_upwards [hu, hv, timeint F hF hiF, timeint H hH hiH] with x hx hy hf hh
  constructor
  · rw [intervalIntegral.integral_sub hf hh]
    linear_combination hx.1 - hy.1
  · filter_upwards [hx.2, hy.2, ae_restrict_mem measurableSet_Icc] with s hs ht hmem
    have hmem' : s ∈ uIcc b c := by simpa only [uIcc_of_le hbc] using hmem
    rw [hs, ht, intervalIntegral.integral_sub
      (hf.mono_set (uIcc_subset_uIcc_left hmem'))
      (hh.mono_set (uIcc_subset_uIcc_left hmem'))]
    ring

private theorem crudeEnergy_physical_generator_divergence {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G ∧
      ∀ L : ℂ →L[ℝ] ℝ, HasWeakDivergence Set.univ
        (fun x j => L ((1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G k x))
        (fun x => L (g x - ζ * ∑ j, (a x j i : ℂ) * G j x)) := by
  obtain ⟨G, hG, htest⟩ := hfg
  refine ⟨G, hG, fun L => ?_⟩
  let F : Vec d → Fin d → ℂ := fun x j => (1 / 2 : ℂ) * ∑ k, (a x j k : ℂ) * G k x
  let b : Vec d → ℂ := fun x => ∑ j, (a x j i : ℂ) * G j x
  have hF (j : Fin d) : MemLp (fun x => F x j) 2 volume := by
    apply MemLp.const_mul
    exact memLp_finsetSum _ fun k _ => (ha j k).fun_mul (Lp.memLp (G k))
  have hb : MemLp b 2 volume :=
    memLp_finsetSum _ fun j _ => (ha j i).fun_mul (Lp.memLp (G j))
  apply crudeEnergy_divergence_projection
    (fun K _ j => (hF j).restrict K)
    (fun K _ => ((Lp.memLp g).sub (hb.const_mul ζ)).restrict K)
  intro φ hφ hφc
  have hv : MemLp (fun x => (φ x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp' (hφ.continuous.memLp_of_hasCompactSupport hφc)
  have hV (j : Fin d) : MemLp (fun x => (coordinateDerivative j φ x : ℂ)) 2 volume :=
    Complex.ofRealCLM.comp_memLp'
      (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hφc.fderiv_apply ℝ (unitVector j)))
  let v := hv.toLp (fun x => (φ x : ℂ))
  let V (j : Fin d) := (hV j).toLp (fun x => (coordinateDerivative j φ x : ℂ))
  have hvx : (v : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ)) := hv.coeFn_toLp
  have hVx (j : Fin d) : (V j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (coordinateDerivative j φ x : ℂ)) := (hV j).coeFn_toLp
  have hvG : IsPhysicalH1Graph volume (Or.inl rfl) v V := by
    rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
      v V _ _ hvx hVx]
    constructor
    · intro j
      simpa only [Complex.ofReal_re] using
        hasWeakPartialDerivative_of_contDiff j φ (hφ.of_le (by simp))
    · intro j
      simp only [Complex.ofReal_im]
      have hd : coordinateDerivative j (fun _ : Vec d => (0 : ℝ)) = (fun _ => 0) := by
        funext x
        simp [EinsteinRelation.coordinateDerivative]
      simpa only [hd] using
        hasWeakPartialDerivative_of_contDiff j (fun _ : Vec d => (0 : ℝ)) contDiff_const
  have he := htest v V hvG
  have he' : (∫ x, g x * (φ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x *
        (coordinateDerivative j φ x : ℂ)) +
      ζ * (∫ x, b x * (φ x : ℂ)) := by
    convert he using 1
    · exact integral_congr_ae (hvx.mono fun x hx => by dsimp only; rw [hx])
    · congr 1
      · congr 1
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr hVx] with x hx
        simp only [hx]
      · congr 1
        exact integral_congr_ae (hvx.mono fun x hx => by dsimp only [b]; rw [hx])
  have hgφ : Integrable (fun x => g x * (φ x : ℂ)) := by
    simpa only [Pi.mul_def] using (Lp.memLp g).integrable_mul hv
  have hbφ : Integrable (fun x => b x * (φ x : ℂ)) := by
    simpa only [Pi.mul_def] using hb.integrable_mul hv
  change (∫ x, (g x - ζ * b x) * (φ x : ℂ)) = -∫ x, ∑ j, F x j * (coordinateDerivative j φ x : ℂ)
  rw [show (fun x => (g x - ζ * b x) * (φ x : ℂ)) =
      (fun x => g x * (φ x : ℂ) - ζ * (b x * (φ x : ℂ))) by funext x; ring]
  have hisub : (∫ x, g x * (φ x : ℂ) - ζ * (b x * (φ x : ℂ))) =
      (∫ x, g x * (φ x : ℂ)) - ∫ x, ζ * (b x * (φ x : ℂ)) := by
    exact integral_sub hgφ (hbφ.const_mul ζ)
  rw [hisub, integral_const_mul, he']
  have hflux : (fun x => ∑ j, F x j * (coordinateDerivative j φ x : ℂ)) =
      (fun x => (1 / 2 : ℂ) * ∑ j, ∑ k,
        (a x j k : ℂ) * G k x * (coordinateDerivative j φ x : ℂ)) := by
    funext x
    simp only [F, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hflux, integral_const_mul]
  ring

private theorem crudeEnergy_physical_gaussian_memLp {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) {s : ℝ} (hs : 0 < s) :
    MemLp (fun x => (Real.exp (-euclideanSq x / s) : ℂ) * f x) 2 volume := by
  have hc : Continuous (fun x : Vec d => (Real.exp (-euclideanSq x / s) : ℂ)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hb : MemLp (fun x : Vec d => (Real.exp (-euclideanSq x / s) : ℂ)) ∞ volume := by
    apply memLp_top_of_bound hc.aestronglyMeasurable 1
    exact ae_of_all _ fun x => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_one_iff.mpr
      apply div_nonpos_of_nonpos_of_nonneg _ hs.le
      apply neg_nonpos.mpr
      change 0 ≤ ∑ j : Fin d, x j * x j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  exact hb.fun_mul (Lp.memLp f)

/-- A stationary generator orbit minus an actual physical generator orbit
satisfies the Gaussian energy inequality.  The physical gradient is obtained
from its generator graph, and the stationary orbit needs no global spatial L². -/
theorem crudeEnergy_ae_mixed_generator_gaussian_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (fun x => ω.1 x) i ζ u v →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
          let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
          let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
          let w : Vec d → ℂ := fun x => f (translate x ω) - u x
          let Z : Fin d → Vec d → ℂ := fun j x => G j (translate x ω) - H j x
          Integrable (fun x => η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ∧
            Integrable (fun x => W x * ‖w x‖ ^ 2) ∧
            (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ≤
              -2 * (∫ x, (g (translate x ω) - v x) *
                (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re +
                16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖w x‖ ^ 2) -
                  ∫ x, W x * ‖w x‖ ^ 2 := by
  intro Λ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hΛ : 1 ≤ Λ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ := mul_le_mul
        (Real.one_le_exp (by positivity)) Q.ellipticity_parameter (by positivity) (by positivity)
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  filter_upwards [hG.ae_reduced_spatial Q,
    crudeEnergy_ae_generator_spatial_divergence hfg hG,
    c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_stationary_spatial_orbit_gaussian_memLp d Fact.out
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))]
    with ω hω hdiv ha hfL hgL hGL
  have ham (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛp ha (fun j k => ω.1.continuous.matrix_elem j k) j k
  intro u v huv
  obtain ⟨H, hH, hdivH⟩ := crudeEnergy_physical_generator_divergence
    (fun x => ω.1 x) i ζ ham huv
  refine ⟨H, hH, ?_⟩
  have hsub (A : ℂ →L[ℝ] ℝ) : HasWeakDivergence univ
      (fun x j => A ((1 / 2 : ℂ) * ∑ k,
        (ω.1 x j k : ℂ) * (G k (translate x ω) - H k x)))
      (fun x => A ((g (translate x ω) - v x) -
        ζ * ∑ j, (ω.1 x j i : ℂ) * (G j (translate x ω) - H j x))) := by
    have he := Correctors.hasWeakDivergence_sub (hdiv A) (hdivH A)
    convert he using 1
    · funext x j
      simp only [Pi.sub_apply, ← map_sub, mul_sub, Finset.sum_sub_distrib]
    · funext x
      simp only [Pi.sub_apply, ← map_sub, mul_sub, Finset.sum_sub_distrib]
      congr 1
      ring
  intro L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have he := physical_locally_h1_forced_gaussian_energy (fun x => ω.1 x) i ζ ham
    (ae_of_all _ fun x => s5Elliptic_of_isElliptic hΛ ha x)
    (fun x => f (translate x ω) - u x) (fun x => g (translate x ω) - v x)
    (fun j x => G j (translate x ω) - H j x) (fun _ _ => 0)
    (fun j => by simpa only [Complex.sub_re] using
      Correctors.hasWeakPartialDerivative_sub (hω.1 j) (hH.1 j))
    (fun j => by simpa only [Complex.sub_im] using
      Correctors.hasWeakPartialDerivative_sub (hω.2.1 j) (hH.2 j))
    (by simpa only [sub_zero] using! hsub Complex.reCLM)
    (by simpa only [sub_zero] using! hsub Complex.imCLM)
    hΛp hL hr
    (by
      have ht := (hfL (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp u (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (by
      have ht := (hgL (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp v (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (fun j => by
      have ht := (hGL j (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp (H j) (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (fun _ => by simpa using (MemLp.zero : MemLp (0 : Vec d → ℂ) 2 volume))
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
    mul_zero, integral_zero, add_zero] using he

/-- The mixed stationary/physical generator difference satisfies the scalar
Gaussian mass inequality. No choice of the physical gradient occurs in the
conclusion, so this estimate can be integrated along measurable time paths. -/
theorem crudeEnergy_ae_mixed_generator_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexGeneratorPair (fun x => ω.1 x) i ζ u v →
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
        let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
        let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
        let w : Vec d → ℂ := fun x => f (translate x ω) - u x
        let z : Vec d → ℂ := fun x => g (translate x ω) - v x
        (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) +
            (∫ x, W x * ‖w x‖ ^ 2) ≤
          16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖w x‖ ^ 2) := by
  intro Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  filter_upwards [crudeEnergy_ae_mixed_generator_gaussian_energy hfg hG,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q)
      (reducedLaw_stationary Q) g] with ω he hf hg
  intro u v huv L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨H, _, he⟩ := he u v huv
  have henergy := (he L r hL hr).2.2
  dsimp only at henergy ⊢
  let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
  let w : Vec d → ℂ := fun x => f (translate x ω) - u x
  let z : Vec d → ℂ := fun x => g (translate x ω) - v x
  have hw : MemLp (fun x => (η x : ℂ) * w x) 2 volume := by
    have hh := (hf (L * r) (by positivity)).sub
      (crudeEnergy_physical_gaussian_memLp u (s := L * r) (by positivity))
    convert hh using 1
    funext x
    simp only [Pi.sub_apply, η, w, mul_sub]
  have hz : MemLp (fun x => (η x : ℂ) * z x) 2 volume := by
    have hh := (hg (L * r) (by positivity)).sub
      (crudeEnergy_physical_gaussian_memLp v (s := L * r) (by positivity))
    convert hh using 1
    funext x
    simp only [Pi.sub_apply, η, z, mul_sub]
  have hZ : Integrable (fun x => z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))) := by
    convert hz.integrable_mul hw.star using 1
    funext x
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  have hcross : (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) =
      2 * (∫ x, z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re := by
    have hre : (∫ x, (z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re) =
        (∫ x, z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re := by
      simpa using! integral_re hZ
    rw [← hre, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [mul_comm (z x), mul_assoc, Complex.re_ofReal_mul]
      ring
  have hn : 0 ≤ (Λ⁻¹ / 4) * (∫ x, η x ^ 2 *
      ∑ j, ‖G j (translate x ω) - H j x‖ ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  change (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) + _ ≤ _
  rw [hcross]
  linarith only [henergy, hn]

/-- Integrating a scalar Gaussian generator inequality along a physical time
primitive cancels the moving-weight derivative. This applies to the difference
path supplied by `crudeEnergy_gaussian_time_primitive_sub`. -/
theorem crudeEnergy_gaussian_primitive_mass
    {d : ℕ} {b c L A : ℝ} (hbc : b ≤ c) (hc : c < 2) (hL : 0 < L)
    {U V : Vec d × ℝ → ℂ} {u₀ u₁ : Vec d → ℂ}
    (hU : Measurable U) (hV : Measurable V)
    (h₀ : Measurable u₀) (h₁ : Measurable u₁)
    (hUsq : Integrable (fun p =>
      Real.exp (-(1 / (L * (2 - b))) * euclideanSq p.1) * ‖U p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hVsq : Integrable (fun p =>
      Real.exp (-(1 / (L * (2 - b))) * euclideanSq p.1) * ‖V p‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))))
    (hi₀ : Integrable (fun x =>
      Real.exp (-(1 / (L * (2 - b))) * euclideanSq x) * ‖u₀ x‖ ^ 2) volume)
    (hi₁ : Integrable (fun x =>
      Real.exp (-(1 / (L * (2 - b))) * euclideanSq x) * ‖u₁ x‖ ^ 2) volume)
    (hprim : ∀ᵐ x ∂(volume : Measure (Vec d)),
      u₀ x + (∫ s in b..c, V (x, s)) = u₁ x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c),
        U (x, s) = u₀ x + ∫ r in b..s, V (x, r))
    (hmass : ∀ᵐ s ∂volume.restrict (Icc b c),
      let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * (2 - s)))
      let W : Vec d → ℝ := fun x =>
        -2 * euclideanSq x / (L * (2 - s) ^ 2) * η x ^ 2
      (∫ x, η x ^ 2 * (2 * (star (U (x, s)) * V (x, s)).re)) +
        (∫ x, W x * ‖U (x, s)‖ ^ 2) ≤ A * (∫ x, η x ^ 2 * ‖U (x, s)‖ ^ 2)) :
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    (∫ x, η c x ^ 2 * ‖u₁ x‖ ^ 2) ≤ (∫ x, η b x ^ 2 * ‖u₀ x‖ ^ 2) +
      A * ∫ s in Icc b c, ∫ x, η s x ^ 2 * ‖U (x, s)‖ ^ 2 := by
  intro η
  let κ := 1 / (L * (2 - b))
  let M := 1 + 2 / (2 - c)
  let ψ : Vec d × ℝ → ℝ := fun p => η p.2 p.1 ^ 2
  let W : Vec d × ℝ → ℝ := fun p =>
    -2 * euclideanSq p.1 / (L * (2 - p.2) ^ 2) * η p.2 p.1 ^ 2
  have hψ : Measurable ψ := by
    dsimp only [ψ, η, euclideanSq, dot]
    fun_prop
  have hW : Measurable W := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  have hb (x : Vec d) (s : ℝ) (hs : s ∈ Icc b c) :
      |ψ (x, s)| ≤ M * Real.exp (-κ * euclideanSq x) ∧
      |W (x, s)| ≤ M * Real.exp (-κ * euclideanSq x) :=
    crudeEnergy_moving_gaussian_bounds x hL hc hs
  have hAC (x : Vec d) : AbsolutelyContinuousOnInterval (fun s => ψ (x, s)) b c := by
    have hsm : ContDiffOn ℝ 1 (fun s => ψ (x, s)) (uIcc b c) := by
      dsimp only [ψ, η]
      apply ContDiffOn.pow
      apply ContDiffOn.exp
      apply ContDiffOn.div contDiffOn_const
        (contDiffOn_const.mul (contDiffOn_const.sub contDiffOn_id))
      intro s hs
      rw [uIcc_of_le hbc] at hs
      exact ne_of_gt (mul_pos hL (sub_pos.mpr (hs.2.trans_lt hc)))
    exact hsm.absolutelyContinuousOnInterval
  have htime := crudeEnergy_gaussian_primitive_time_energy hbc hU hV h₀ h₁
    hUsq hVsq hi₀ hi₁ hprim hψ hW hAC
    (fun x s hs => (crudeEnergy_moving_gaussian_derivative x hL (hs.2.trans_lt hc)).deriv)
    (fun x s hs => (hb x s hs).1) (fun x s hs => (hb x s hs).2)
  have htmem : ∀ᵐ p : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
      p.2 ∈ Icc b c :=
    (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).mpr
      (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)
  have hweighted (χ : Vec d × ℝ → ℝ) (hχ : Measurable χ)
      (hbound : ∀ᵐ p ∂volume.prod (volume.restrict (Icc b c)),
        |χ p| ≤ M * Real.exp (-κ * euclideanSq p.1)) :
      Integrable (fun p => χ p * ‖U p‖ ^ 2)
        (volume.prod (volume.restrict (Icc b c))) := by
    apply (hUsq.const_mul M).mono' (hχ.mul (hU.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [hbound] with p hp
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖U p‖)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hp (sq_nonneg ‖U p‖)
  have hψb := htmem.mono fun p hp => (hb p.1 p.2 hp).1
  have hWb := htmem.mono fun p hp => (hb p.1 p.2 hp).2
  have hcross := crudeEnergy_integrable_gaussian_cross (volume.restrict (Icc b c))
    hU hV hψ hψb hUsq hVsq
  have hweight := hweighted W hW hWb
  have henergy := hweighted ψ hψ hψb
  have hint := integral_mono_ae
    (hcross.integral_prod_right.add hweight.integral_prod_right)
    (henergy.integral_prod_right.const_mul A) hmass
  simp only [Pi.add_apply] at hint
  rw [integral_add hcross.integral_prod_right hweight.integral_prod_right,
    integral_const_mul] at hint
  change (∫ s in Icc b c, ∫ x, ψ (x, s) *
      (2 * (star (U (x, s)) * V (x, s)).re)) +
    (∫ s in Icc b c, ∫ x, W (x, s) * ‖U (x, s)‖ ^ 2) ≤
    A * (∫ s in Icc b c, ∫ x, η s x ^ 2 * ‖U (x, s)‖ ^ 2) at hint
  rw [htime] at hint
  linarith only [hint]

/-- Integral Gronwall for merely integrable mass paths. The integrating
factor is applied to the absolutely continuous time primitive, so no
pointwise time differentiability or continuity of the mass is required. -/
theorem crudeEnergy_integrable_mass_gronwall {E : ℝ → ℝ} {a b A δ : ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ s ∈ Icc a b, E s ≤ δ + A * ∫ r in a..s, E r) :
    E b ≤ δ * Real.exp (A * (b - a)) := by
  let F : ℝ → ℝ := fun s => δ + A * ∫ r in a..s, E r
  let q : ℝ → ℝ := fun s => Real.exp (-A * (s - a))
  have hF : AbsolutelyContinuousOnInterval F a b := by
    have hc := (contDiffOn_const : ContDiffOn ℝ 1
      (fun _ : ℝ => δ) (uIcc a b)).absolutelyContinuousOnInterval
    exact hc.add ((hE.absolutelyContinuousOnInterval_intervalIntegral (c := a)
      (by simp)).const_mul A)
  have hq : AbsolutelyContinuousOnInterval q a b := by
    have hsm : ContDiffOn ℝ 1 q (uIcc a b) := by
      dsimp only [q]
      fun_prop
    exact hsm.absolutelyContinuousOnInterval
  have hdq (s : ℝ) : HasDerivAt q (-A * q s) s := by
    simpa only [q, id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id s).sub_const a).const_mul (-A)).exp
  have hderiv : ∀ᵐ s ∂volume, s ∈ Icc a b →
      deriv F s * q s + F s * deriv q s ≤ 0 := by
    filter_upwards [hE.ae_hasDerivAt_integral] with s hs hmem
    have hmem' : s ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hDs : HasDerivAt F (A * E s) s :=
      ((hs hmem' a (by simp)).const_mul A).const_add δ
    rw [hDs.deriv, (hdq s).deriv]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound s hmem) hA) (Real.exp_nonneg (-A * (s - a)))
    change A * E s * q s ≤ A * F s * q s at hm
    nlinarith only [hm]
  have hint : (∫ s in Icc a b, deriv F s * q s + F s * deriv q s) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_of_ae hderiv, ae_restrict_mem measurableSet_Icc]
      with s hs hmem
    exact hs hmem
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    hF.integral_deriv_mul_eq_sub hq] at hint
  have hFa : F a = δ := by simp only [F, intervalIntegral.integral_same, mul_zero, add_zero]
  have hqa : q a = 1 := by simp only [q, sub_self, mul_zero, Real.exp_zero]
  rw [hFa, hqa, mul_one] at hint
  have hFb : F b * q b ≤ δ := sub_nonpos.mp hint
  have hcancel : q b * Real.exp (A * (b - a)) = 1 := by
    dsimp only [q]
    rw [← Real.exp_add, show -A * (b - a) + A * (b - a) = 0 by ring,
      Real.exp_zero]
  calc
    E b ≤ F b := hbound b ⟨hab, le_rfl⟩
    _ = (F b * q b) * Real.exp (A * (b - a)) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ δ * Real.exp (A * (b - a)) :=
      mul_le_mul_of_nonneg_right hFb (Real.exp_nonneg _)

/-- A Gaussian-integrable difference path with zero initial mass and the
integrated mass inequality vanishes almost everywhere at the final time. -/
theorem crudeEnergy_gaussian_mass_unique {d : ℕ} {U : ℝ → Vec d → ℂ}
    {κ : ℝ → ℝ} {a b A : ℝ} (hab : a ≤ b) (hA : 0 ≤ A)
    (hi : IntervalIntegrable
      (fun s => ∫ x, Real.exp (-κ s * euclideanSq x) * ‖U s x‖ ^ 2) volume a b)
    (hb : Integrable (fun x => Real.exp (-κ b * euclideanSq x) * ‖U b x‖ ^ 2) volume)
    (hmass : ∀ s ∈ Icc a b,
      (∫ x, Real.exp (-κ s * euclideanSq x) * ‖U s x‖ ^ 2) ≤
        A * ∫ r in a..s, ∫ x, Real.exp (-κ r * euclideanSq x) * ‖U r x‖ ^ 2) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), U b x = 0 := by
  have hg := crudeEnergy_integrable_mass_gronwall (δ := 0) hab hA hi
    (fun s hs => by simpa only [zero_add] using hmass s hs)
  have hnonneg (x : Vec d) : 0 ≤ Real.exp (-κ b * euclideanSq x) * ‖U b x‖ ^ 2 :=
    mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have hz : (∫ x, Real.exp (-κ b * euclideanSq x) * ‖U b x‖ ^ 2) = 0 :=
    le_antisymm (by simpa only [zero_mul] using hg) (integral_nonneg hnonneg)
  have hae := (integral_eq_zero_iff_of_nonneg hnonneg hb).mp hz
  filter_upwards [hae] with x hx
  have hs : ‖U b x‖ ^ 2 = 0 :=
    (mul_eq_zero.mp hx).resolve_left (Real.exp_ne_zero _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hs)


/-- A vanishing initial trace along a sequence suffices for the mass
uniqueness argument; the time path need not have a pointwise value at zero. -/
theorem crudeEnergy_mass_vanishes_of_initial_trace {E : ℝ → ℝ}
    {τ : ℕ → ℝ} {a b A : ℝ} (hA : 0 ≤ A) (hEb : 0 ≤ E b)
    (hτ : Tendsto τ atTop (𝓝 a))
    (htrace : Tendsto (fun n => E (τ n)) atTop (𝓝 0))
    (hτb : ∀ n, τ n ≤ b)
    (hi : ∀ n, IntervalIntegrable E volume (τ n) b)
    (hmass : ∀ n, ∀ s ∈ Icc (τ n) b,
      E s ≤ E (τ n) + A * ∫ r in τ n..s, E r) : E b = 0 := by
  have hlim : Tendsto (fun n => E (τ n) * Real.exp (A * (b - τ n)))
      atTop (𝓝 0) := by
    have he : Tendsto (fun n => Real.exp (A * (b - τ n)))
        atTop (𝓝 (Real.exp (A * (b - a)))) :=
      Real.continuous_exp.continuousAt.tendsto.comp
        ((tendsto_const_nhds (x := A)).mul ((tendsto_const_nhds (x := b)).sub hτ))
    simpa only [zero_mul] using htrace.mul he
  apply le_antisymm _ hEb
  exact ge_of_tendsto hlim (Eventually.of_forall fun n =>
    crudeEnergy_integrable_mass_gronwall (hτb n) hA (hi n) (hmass n))

/-- Joint stationary and physical representatives satisfy the mixed moving
Gaussian inequality on almost every environment-time section. The physical
coefficients are the literal environment field. -/
theorem crudeEnergy_ae_joint_mixed_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c L : ℝ} (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    let W : ℝ → Vec d → ℝ := fun s x =>
      -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
    let Z : (ℝ × FieldPair d) × Vec d → ℂ := fun t =>
      U (t.1.1, translate t.2 t.1.2) - F t
    let Y : (ℝ × FieldPair d) × Vec d → ℂ := fun t =>
      V (t.1.1, translate t.2 t.1.2) - H t
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (∫ x, η s x ^ 2 * (2 * (star (Z ((s, ω), x)) * Y ((s, ω), x)).re)) +
        (∫ x, W s x * ‖Z ((s, ω), x)‖ ^ 2) ≤
        16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η s x ^ 2 * ‖Z ((s, ω), x)‖ ^ 2) := by
  intro Λ η W Z Y
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hshift {T : ℝ × FieldPair d → ℂ} (hT : Measurable T) :
      Measurable (fun t : (ℝ × FieldPair d) × Vec d =>
        T (t.1.1, translate t.2 t.1.2)) :=
    hT.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hZ : Measurable Z := (hshift hU).sub hF
  have hY : Measurable Y := (hshift hV).sub hH
  have hη : Measurable (fun t : (ℝ × FieldPair d) × Vec d => η t.1.1 t.2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hW : Measurable (fun t : (ℝ × FieldPair d) × Vec d => W t.1.1 t.2) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  let A : ℝ × FieldPair d → ℝ := fun t =>
    (∫ x, η t.1 x ^ 2 * (2 * (star (Z (t, x)) * Y (t, x)).re)) +
      ∫ x, W t.1 x * ‖Z (t, x)‖ ^ 2
  let B : ℝ × FieldPair d → ℝ := fun t =>
    16 * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ x, η t.1 x ^ 2 * ‖Z (t, x)‖ ^ 2
  have hA : Measurable A := by
    apply Measurable.add
    · exact ((hη.pow_const 2).mul ((Complex.continuous_re.measurable.comp
        ((continuous_star.measurable.comp hZ).mul hY)).const_mul 2)).stronglyMeasurable.integral_prod_right'.measurable
    · exact (hW.mul (hZ.norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hB : Measurable B := measurable_const.mul
    ((hη.pow_const 2).mul (hZ.norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have heU' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hU.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heU s)
  have heV' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  filter_upwards [crudeEnergy_ae_mixed_generator_gaussian_mass (hgen s hs) (hgrad s hs),
    hphys s hs, heU', heV'] with ω hm hp heu hev
  have hr : 0 < 2 - s := sub_pos.mpr (hs.2.trans_lt hc)
  have hm := hm (p s ω) (q s ω) hp L (2 - s) hL hr
  have hZeq : (fun x => Z ((s, ω), x)) =ᵐ[volume]
      (fun x => (u s) (translate x ω) - (p s ω) x) := by
    filter_upwards [heu, heF s ω] with x hx hy
    change U (s, translate x ω) = _ at hx
    dsimp only [Z]
    rw [hx, hy]
  have hYeq : (fun x => Y ((s, ω), x)) =ᵐ[volume]
      (fun x => (v s) (translate x ω) - (q s ω) x) := by
    filter_upwards [hev, heH s ω] with x hx hy
    change V (s, translate x ω) = _ at hx
    dsimp only [Y]
    rw [hx, hy]
  have hcross : (∫ x, η s x ^ 2 * (2 * (star (Z ((s, ω), x)) * Y ((s, ω), x)).re)) =
      ∫ x, η s x ^ 2 * (2 * (star ((u s) (translate x ω) - (p s ω) x) *
        ((v s) (translate x ω) - (q s ω) x)).re) := by
    apply integral_congr_ae
    filter_upwards [hZeq, hYeq] with x hx hy
    rw [hx, hy]
  have hsq (ψ : Vec d → ℝ) : (∫ x, ψ x * ‖Z ((s, ω), x)‖ ^ 2) =
      ∫ x, ψ x * ‖(u s) (translate x ω) - (p s ω) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hZeq] with x hx
    rw [hx]
  dsimp only [A, B]
  rw [hcross, hsq, hsq]
  exact hm

/-- The actual physical evolutions can be chosen measurably in the
reduced environment. The coefficient field is modified only on the null
exceptional set when applying the all-parameter construction. -/
theorem crudeEnergy_ae_exists_measurable_physical_pair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
      borel (Lp ℂ 2 (volume : Measure (Vec d)))
    ∃ S Sdag : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω) ∧
        IsPhysicalComplexTransposeSemigroup ω.1 i ζ (S ω) (Sdag ω)) ∧
      (∀ (t : ℝ≥0) (f : Lp ℂ 2 (volume : Measure (Vec d))),
        Measurable (fun ω => S ω t f) ∧ Measurable (fun ω => Sdag ω t f)) ∧
      (Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) ∧
       Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        Sdag z.2.2 z.2.1 z.1)) := by
  classical
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) :=
    borel (Lp ℂ 2 (volume : Measure (Vec d)))
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 1 ≤ Λ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ :=
        mul_le_mul (Real.one_le_exp (by linarith [Q.ellipticity_parameter]))
          Q.ellipticity_parameter zero_le_one (Real.exp_nonneg _)
  let E : Set (FieldPair d) := {ω | IsElliptic Λ (fun x => ω.1 x)}
  have hE : IsClosed E := by
    have he : E = ⋂ x : Vec d, ({ω : FieldPair d | (ω.1 x).transpose = ω.1 x} ∩
        ⋂ ξ : Vec d, ({ω : FieldPair d | Λ⁻¹ * euclideanSq ξ ≤ dot ξ ((ω.1 x).mulVec ξ)} ∩
          {ω : FieldPair d | dot ξ ((ω.1 x).mulVec ξ) ≤ Λ * euclideanSq ξ})) := by
      ext ω
      simp only [E, IsElliptic, mem_setOf_eq, mem_iInter, mem_inter_iff]
    rw [he]
    apply isClosed_iInter
    intro x
    have hx : Continuous (fun ω : FieldPair d => ω.1 x) :=
      (continuous_eval_const x).comp continuous_fst
    refine (isClosed_eq hx.matrix_transpose hx).inter (isClosed_iInter fun ξ => ?_)
    have hq : Continuous (fun ω : FieldPair d => dot ξ ((ω.1 x).mulVec ξ)) :=
      continuous_finsetSum _ fun j _ =>
        continuous_const.mul ((continuous_apply j).comp (hx.matrix_mulVec continuous_const))
    exact (isClosed_le continuous_const hq).inter (isClosed_le hq continuous_const)
  obtain ⟨ω₀, hω₀⟩ := (c4_ae_reduced_physical_elliptic Q).exists
  let ρ : FieldPair d → FieldPair d := E.piecewise id (fun _ => ω₀)
  have hρ : Measurable ρ := measurable_id.piecewise hE.measurableSet measurable_const
  have hρE (ω : FieldPair d) : IsElliptic Λ (fun x => (ρ ω).1 x) := by
    by_cases hω : ω ∈ E
    · have hw : IsElliptic Λ (fun x => ω.1 x) := hω
      simpa only [ρ, piecewise_eq_of_mem E _ _ hω, id_eq] using hw
    · simpa only [ρ, piecewise_eq_of_notMem E _ _ hω] using hω₀
  have ha : Measurable (fun t : FieldPair d × Vec d => (ρ t.1).1 t.2) :=
    (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).measurable.comp
      ((hρ.comp measurable_fst).prodMk measurable_snd)
  obtain ⟨S, Sdag, hS, hm⟩ := retained_physical_complex_measurable_evolution
    d i ζ Λ hΛ (fun ω x => (ρ ω).1 x) ha
    (fun ω x => s5Elliptic_of_isElliptic hΛ (hρE ω) x)
  refine ⟨S, Sdag, ?_, hm, ?_, ?_⟩
  · filter_upwards [c4_ae_reduced_physical_elliptic Q] with ω hω
    have he : ρ ω = ω := by
      exact piecewise_eq_of_mem E id (fun _ => ω₀) hω
    simpa only [he] using hS ω
  · exact measurable_uncurry_of_continuous_of_measurable
      (u := fun f (z : ℝ≥0 × FieldPair d) => S z.2 z.1 f)
      (fun z => (S z.2 z.1).continuous) (fun f =>
        measurable_uncurry_of_continuous_of_measurable
          (u := fun t ω => S ω t f)
          (fun ω => (hS ω).1.2.2.1 f) (fun t => (hm t f).1))
  · exact measurable_uncurry_of_continuous_of_measurable
      (u := fun f (z : ℝ≥0 × FieldPair d) => Sdag z.2 z.1 f)
      (fun z => (Sdag z.2 z.1).continuous) (fun f =>
        measurable_uncurry_of_continuous_of_measurable
          (u := fun t ω => Sdag ω t f)
          (fun ω => (hS ω).2.2.2.1 f) (fun t => (hm t f).2))

/-- A continuous physical L² path is Gaussian square-integrable on each
compact time interval, for every measurable joint representative. -/
theorem crudeEnergy_physical_gaussian_spacetime {d : ℕ} {b c κ : ℝ}
    (hκ : 0 ≤ κ) {u : ℝ → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : Continuous u) {F : ℝ × Vec d → ℂ} (hF : Measurable F)
    (heF : ∀ s, (fun x => F (s, x)) =ᵐ[volume] u s) :
    Integrable (fun p : Vec d × ℝ =>
      Real.exp (-κ * euclideanSq p.1) * ‖F (p.2, p.1)‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))) := by
  have hinorm : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hi : Integrable (fun p : ℝ × Vec d => ‖F p‖ ^ 2)
      ((volume.restrict (Icc b c)).prod volume) := by
    apply (integrable_prod_iff (hF.norm.pow_const 2).aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun s => ((Lp.memLp (u s)).norm.integrable_sq).congr
      ((heF s).symm.mono fun x hx => congrArg (fun z : ℂ => ‖z‖ ^ 2) hx)), ?_⟩
    apply hinorm.congr
    filter_upwards with s
    have hn : ‖u s‖ ^ 2 = ∫ x, ‖(u s) x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    rw [hn]
    apply integral_congr_ae
    filter_upwards [heF s] with x hx
    simp only [hx, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖(u s) x‖)]
  have hw : Measurable (fun p : Vec d × ℝ => Real.exp (-κ * euclideanSq p.1)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  apply hi.swap.mono' (hw.mul ((hF.comp measurable_swap).norm.pow_const 2)).aestronglyMeasurable
  filter_upwards with p
  change ‖Real.exp (-κ * euclideanSq p.1) * ‖F (p.2, p.1)‖ ^ 2‖ ≤
    ‖F (p.2, p.1)‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  apply mul_le_of_le_one_left (sq_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hs : 0 ≤ euclideanSq p.1 := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) hs

private theorem crudeEnergy_integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (f : Lp ℂ 2 μ) :
    ∫ x, ‖f x‖ ∂μ ≤ (μ Set.univ ^ (1 / 2 : ℝ)).toReal * ‖f‖ := by
  have hb : eLpNorm f 1 μ ≤ eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
    convert eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (Lp.aestronglyMeasurable f) using 1
    norm_num
  have hfin : eLpNorm f 2 μ * μ Set.univ ^ (1 / 2 : ℝ) ≠ ⊤ := by
    apply ENNReal.mul_ne_top (Lp.memLp f).ne
    finiteness
  have h := ENNReal.toReal_mono hfin hb
  rw [eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ← integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
    ENNReal.toReal_mul, ← Lp.norm_def] at h
  simpa only [mul_comm] using h

private theorem crudeEnergy_integrable_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    Integrable U (ν.prod μ) := by
  apply (integrable_prod_iff hU.aestronglyMeasurable).mpr
  refine ⟨ae_of_all _ (fun t => ((Lp.memLp (u t)).integrable (by norm_num)).congr
    (heq t).symm), ?_⟩
  apply (hu.norm.const_mul (μ Set.univ ^ (1 / 2 : ℝ)).toReal).mono'
    (hU.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg (fun x => norm_nonneg _)),
    integral_congr_ae ((heq t).mono (fun x h => congrArg norm h))]
  exact crudeEnergy_integral_norm_le_l2 (u t)

private theorem crudeEnergy_coeFn_integral_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi := crudeEnergy_integrable_joint_l2_finite hu hU heq
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℂ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℂ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable U (ν.prod (μ.restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun t x => U (t, x)) hir]
  apply integral_congr_ae
  filter_upwards with t
  exact integral_congr_ae (ae_restrict_of_ae (heq t).symm)

/-- On each finite spatial set, a measurable representative of an integrable
physical L2 curve has the literal pointwise time integral prescribed by its
Bochner integral. Spatial volume need not be finite. -/
private theorem crudeEnergy_coeFn_integral_joint_l2_local {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t)
    (K : Set Ω) (hK : μ K ≠ ⊤) :
    Integrable U (ν.prod (μ.restrict K)) ∧
      (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ.restrict K] fun x => ∫ t, U (t, x) ∂ν := by
  let : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hK.lt_top⟩
  let C := LpToLpRestrictCLM Ω ℂ ℂ μ 2 K
  have hC : Integrable (fun t => C (u t)) ν := C.integrable_comp hu
  have hrep : ∀ t, (fun x => U (t, x)) =ᵐ[μ.restrict K] C (u t) := by
    intro t
    have ht : (fun x => U (t, x)) =ᵐ[μ.restrict K] (u t : Ω → ℂ) :=
      ae_restrict_of_ae (heq t)
    exact ht.trans (LpToLpRestrictCLM_coeFn ℂ K (u t)).symm
  refine ⟨crudeEnergy_integrable_joint_l2_finite hC hU hrep, ?_⟩
  have hi := crudeEnergy_coeFn_integral_joint_l2_finite hC hU hrep
  rw [C.integral_comp_comm hu] at hi
  exact (LpToLpRestrictCLM_coeFn ℂ K (∫ t, u t ∂ν)).symm.trans hi

/-- The L² Bochner integral agrees with the time integral of a joint
representative on a sigma-finite spatial measure. Finite restrictions justify
the identification before taking a countable spatial union. -/
theorem crudeEnergy_coeFn_integral_joint_l2_sigmaFinite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi (n : ℕ) := (crudeEnergy_coeFn_integral_joint_l2_local hu hU heq
    (spanningSets μ n) (measure_spanningSets_lt_top μ n).ne).2
  have h := (ae_restrict_iUnion_iff (spanningSets μ)
    (fun x => (∫ t, u t ∂ν) x = ∫ t, U (t, x) ∂ν)).mpr hi
  simpa only [iUnion_spanningSets, Measure.restrict_univ, Filter.EventuallyEq] using h

/-- A continuously differentiable physical L² path has its literal temporal
primitive on one spatial event, including the two actual L² endpoint traces. -/
theorem crudeEnergy_physical_time_primitive {d : ℕ}
    {p q : ℝ → Lp ℂ 2 (volume : Measure (Vec d))}
    {F H : ℝ × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s, (fun x => F (s, x)) =ᵐ[volume] p s)
    (heH : ∀ s, (fun x => H (s, x)) =ᵐ[volume] q s)
    (hq : Continuous q) {a b c : ℝ} (hab : a < b) (hbc : b ≤ c)
    (hd : ∀ s, a < s → HasDerivAt p (q s) s) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      (p b) x + (∫ s in b..c, H (s, x)) = (p c) x ∧
      ∀ᵐ s ∂volume.restrict (Icc b c), F (s, x) =
        (p b) x + ∫ r in b..s, H (r, x) := by
  have hint (s : ℝ) : IntegrableOn q (Icc b s) :=
    hq.continuousOn.integrableOn_compact isCompact_Icc
  have hFTC (s : ℝ) (hs : b ≤ s) : (∫ r in Icc b s, q r) = p s - p b := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun r hr => hd r (hab.trans_le ((uIcc_of_le hs ▸ hr).1)))
      (hq.intervalIntegrable b s)
  have hend (s : ℝ) (hs : b ≤ s) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (p b) x + (∫ r in Icc b s, H (r, x)) = (p s) x := by
    have hi := crudeEnergy_coeFn_integral_joint_l2_sigmaFinite (hint s) hH heH
    rw [hFTC s hs] at hi
    filter_upwards [hi, Lp.coeFn_sub (p s) (p b)] with x hx hsub
    rw [← hx, hsub]
    exact add_sub_cancel _ _
  let J : ℝ × Vec d → ℂ := fun z => (p b) z.2 + ∫ r in Icc b z.1, H (r, z.2)
  have hJ : Measurable J :=
    ((Lp.stronglyMeasurable (p b)).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hH b)
  have he : ∀ᵐ s ∂volume.restrict (Icc b c), ∀ᵐ x ∂(volume : Measure (Vec d)),
      F (s, x) = J (s, x) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    filter_upwards [heF s, hend s hs.1] with x hx hj
    exact hx.trans hj.symm
  have hp := (Measure.ae_ae_comm (p := fun s x => F (s, x) = J (s, x))
    (measurableSet_eq_fun hF hJ)).mp he
  filter_upwards [hend c hbc, hp] with x hx ht
  constructor
  · rwa [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc]
  · filter_upwards [ht, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rw [hs, intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]

private theorem crudeEnergy_physical_gaussian_endpoint {d : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ) (p : Lp ℂ 2 (volume : Measure (Vec d))) :
    Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖p x‖ ^ 2) volume := by
  have hw : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  apply ((Lp.memLp p).norm.integrable_sq).mono'
    (hw.mul ((Lp.stronglyMeasurable p).measurable.norm.pow_const 2)).aestronglyMeasurable
  filter_upwards with x
  change ‖Real.exp (-κ * euclideanSq x) * ‖p x‖ ^ 2‖ ≤ ‖p x‖ ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
  apply mul_le_of_le_one_left (sq_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hs : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) hs

/-- The mixed stationary/physical generator inequality integrates along the
actual two L² paths. Both endpoint differences are retained literally, and
all Gaussian spacetime integrability is derived from the continuous paths. -/
theorem crudeEnergy_ae_integrated_mixed_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        (∫ x, η b x ^ 2 * ‖(u b) (translate x ω) - (p b ω) x‖ ^ 2) +
          16 * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ s in Icc b c, ∫ x, η s x ^ 2 *
            ‖U (s, translate x ω) - F ((s, ω), x)‖ ^ 2 := by
  intro Λ η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hb : b < 2 := hbc.trans_lt hc
  let κ : ℝ := 1 / (L * (2 - b))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hiU : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hiV : IntegrableOn (fun s => ‖v s‖ ^ 2) (Icc b c) :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  filter_upwards [crudeEnergy_ae_physical_time_primitive Q hU hV heU heV hv hab hbc hd,
    crudeEnergy_ae_joint_mixed_gaussian_mass hc hL hgen hgrad hphys hU hV heU heV hF hH heF heH,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiU hU heU,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiV hV heV,
    crudeEnergy_ae_gaussian_endpoint Q hκ (u b),
    crudeEnergy_ae_gaussian_endpoint Q hκ (u c), hC1]
    with ω hprim hmass hUsq hVsq hi₀ hi₁ hpq
  let X : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
  let Y : Vec d × ℝ → ℂ := fun z => V (z.2, translate z.1 ω)
  let R : Vec d × ℝ → ℂ := fun z => F ((z.2, ω), z.1)
  let T : Vec d × ℝ → ℂ := fun z => H ((z.2, ω), z.1)
  have hX : Measurable X := hU.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hY : Measurable Y := hV.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hFω : Measurable (fun z : ℝ × Vec d => F ((z.1, ω), z.2)) :=
    hF.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hHω : Measurable (fun z : ℝ × Vec d => H ((z.1, ω), z.2)) :=
    hH.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hR : Measurable R := hFω.comp measurable_swap
  have hT : Measurable T := hHω.comp measurable_swap
  have hiR := crudeEnergy_physical_gaussian_spacetime (b := b) (c := c) hκ.le hpq.1 hFω (fun s => heF s ω)
  have hiT := crudeEnergy_physical_gaussian_spacetime (b := b) (c := c) hκ.le hpq.2.1 hHω (fun s => heH s ω)
  have hpr := crudeEnergy_physical_time_primitive hFω hHω
    (fun s => heF s ω) (fun s => heH s ω) hpq.2.1 hab hbc hpq.2.2
  have hw : Measurable (fun z : Vec d × ℝ => Real.exp (-κ * euclideanSq z.1)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hw' : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hsub := crudeEnergy_gaussian_time_primitive_sub
    (U := X) (V := R)
    (u₀ := fun x => (u b) (translate x ω)) (u₁ := fun x => (u c) (translate x ω))
    (v₀ := fun x => (p b ω) x) (v₁ := fun x => (p c ω) x)
    hbc hY hT hVsq hiT hprim hpr
  have hsq := crudeEnergy_integrable_weighted_sub_sq
    (volume.prod (volume.restrict (Icc b c))) hw
    (fun _ => (Real.exp_pos _).le) hX hR hUsq hiR
  have hdsq := crudeEnergy_integrable_weighted_sub_sq
    (volume.prod (volume.restrict (Icc b c))) hw
    (fun _ => (Real.exp_pos _).le) hY hT hVsq hiT
  have hm (s : ℝ) : Measurable (fun x => (u s) (translate x ω)) :=
    (Lp.stronglyMeasurable (u s)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have h₀ := crudeEnergy_integrable_weighted_sub_sq volume hw'
    (fun _ => (Real.exp_pos _).le) (hm b) (Lp.stronglyMeasurable (p b ω)).measurable
    hi₀ (crudeEnergy_physical_gaussian_endpoint hκ.le (p b ω))
  have h₁ := crudeEnergy_integrable_weighted_sub_sq volume hw'
    (fun _ => (Real.exp_pos _).le) (hm c) (Lp.stronglyMeasurable (p c ω)).measurable
    hi₁ (crudeEnergy_physical_gaussian_endpoint hκ.le (p c ω))
  exact crudeEnergy_gaussian_primitive_mass hbc hc hLp
    (hX.sub hR) (hY.sub hT)
    ((hm b).sub (Lp.stronglyMeasurable (p b ω)).measurable)
    ((hm c).sub (Lp.stronglyMeasurable (p c ω)).measurable)
    hsq hdsq h₀ h₁ hsub hmass

/-- Integral Gronwall with an almost-everywhere interior inequality and a
separate literal endpoint inequality, as supplied by environment/time Fubini. -/
theorem crudeEnergy_integrable_mass_gronwall_ae {E : ℝ → ℝ} {a b A δ : ℝ}
    (hab : a ≤ b) (hA : 0 ≤ A) (hE : IntervalIntegrable E volume a b)
    (hbound : ∀ᵐ s ∂volume.restrict (Icc a b), E s ≤ δ + A * ∫ r in a..s, E r)
    (hend : E b ≤ δ + A * ∫ r in a..b, E r) :
    E b ≤ δ * Real.exp (A * (b - a)) := by
  let F : ℝ → ℝ := fun s => δ + A * ∫ r in a..s, E r
  let q : ℝ → ℝ := fun s => Real.exp (-A * (s - a))
  have hF : AbsolutelyContinuousOnInterval F a b := by
    have hc := (contDiffOn_const : ContDiffOn ℝ 1
      (fun _ : ℝ => δ) (uIcc a b)).absolutelyContinuousOnInterval
    exact hc.add ((hE.absolutelyContinuousOnInterval_intervalIntegral (c := a)
      (by simp)).const_mul A)
  have hq : AbsolutelyContinuousOnInterval q a b := by
    have hsm : ContDiffOn ℝ 1 q (uIcc a b) := by
      dsimp only [q]
      fun_prop
    exact hsm.absolutelyContinuousOnInterval
  have hdq (s : ℝ) : HasDerivAt q (-A * q s) s := by
    simpa only [q, id_eq, mul_one, mul_comm] using
      (((hasDerivAt_id s).sub_const a).const_mul (-A)).exp
  have hderiv : ∀ᵐ s ∂volume.restrict (Icc a b),
      deriv F s * q s + F s * deriv q s ≤ 0 := by
    filter_upwards [ae_restrict_of_ae hE.ae_hasDerivAt_integral, hbound,
      ae_restrict_mem measurableSet_Icc] with s hs hbs hmem
    have hmem' : s ∈ uIcc a b := by rwa [uIcc_of_le hab]
    have hDs : HasDerivAt F (A * E s) s :=
      ((hs hmem' a (by simp)).const_mul A).const_add δ
    rw [hDs.deriv, (hdq s).deriv]
    have hm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbs hA) (Real.exp_nonneg (-A * (s - a)))
    change A * E s * q s ≤ A * F s * q s at hm
    nlinarith only [hm]
  have hint : (∫ s in Icc a b, deriv F s * q s + F s * deriv q s) ≤ 0 := by
    apply integral_nonpos_of_ae
    exact hderiv
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    hF.integral_deriv_mul_eq_sub hq] at hint
  have hFa : F a = δ := by simp only [F, intervalIntegral.integral_same, mul_zero, add_zero]
  have hqa : q a = 1 := by simp only [q, sub_self, mul_zero, Real.exp_zero]
  rw [hFa, hqa, mul_one] at hint
  have hFb : F b * q b ≤ δ := sub_nonpos.mp hint
  have hcancel : q b * Real.exp (A * (b - a)) = 1 := by
    dsimp only [q]
    rw [← Real.exp_add, show -A * (b - a) + A * (b - a) = 0 by ring,
      Real.exp_zero]
  calc
    E b ≤ F b := hend
    _ = (F b * q b) * Real.exp (A * (b - a)) := by
      rw [mul_assoc, hcancel, mul_one]
    _ ≤ δ * Real.exp (A * (b - a)) :=
      mul_le_mul_of_nonneg_right hFb (Real.exp_nonneg _)

private theorem crudeEnergy_integrable_moving_gaussian_mass {d : ℕ} {b c L : ℝ}
    (hc : c < 2) (hL : 0 < L) {Z : Vec d × ℝ → ℂ}
    (hZ : Measurable Z)
    (hiZ : Integrable (fun z => Real.exp (-(1 / (L * (2 - b))) * euclideanSq z.1) *
      ‖Z z‖ ^ 2) (volume.prod (volume.restrict (Icc b c)))) :
    IntegrableOn (fun s => ∫ x, Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
      ‖Z (x, s)‖ ^ 2) (Icc b c) := by
  let ψ : Vec d × ℝ → ℝ := fun z => Real.exp (-euclideanSq z.1 / (L * (2 - z.2))) ^ 2
  have hψ : Measurable ψ := by
    dsimp only [ψ, euclideanSq, dot]
    fun_prop
  have hi : Integrable (fun z => ψ z * ‖Z z‖ ^ 2)
      (volume.prod (volume.restrict (Icc b c))) := by
    apply (hiZ.const_mul (1 + 2 / (2 - c))).mono'
      (hψ.mul (hZ.norm.pow_const 2)).aestronglyMeasurable
    have htmem : ∀ᵐ z : Vec d × ℝ ∂volume.prod (volume.restrict (Icc b c)),
        z.2 ∈ Icc b c :=
      (Measure.ae_prod_iff_ae_ae (measurable_snd measurableSet_Icc)).mpr
        (ae_of_all _ fun _ => ae_restrict_mem measurableSet_Icc)
    filter_upwards [htmem] with z hz
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖Z z‖)]
    simpa only [ψ, mul_assoc] using mul_le_mul_of_nonneg_right
      (crudeEnergy_moving_gaussian_bounds z.1 hL hc hz).1 (sq_nonneg ‖Z z‖)
  exact hi.integral_prod_right

private theorem crudeEnergy_ae_integrable_mixed_gaussian_mass {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {b c L : ℝ} (hbc : b ≤ c) (hc : c < 2) (hL : 0 < L)
    {u : ℝ → Lp ℂ 2 (reducedLaw Q)} (hu : Continuous u)
    {p : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hp : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω))
    {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    {F : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω) :
    ∀ᵐ ω ∂reducedLaw Q, IntegrableOn (fun s => ∫ x,
      Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
        ‖U (s, translate x ω) - F ((s, ω), x)‖ ^ 2) (Icc b c) := by
  let κ : ℝ := 1 / (L * (2 - b))
  have hb : b < 2 := hbc.trans_lt hc
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hiU : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  filter_upwards [crudeEnergy_ae_gaussian_spacetime Q κ hκ hiU hU heU, hp]
    with ω hiU hpω
  let X : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
  let R : Vec d × ℝ → ℂ := fun z => F ((z.2, ω), z.1)
  have hX : Measurable X := hU.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hFω : Measurable (fun z : ℝ × Vec d => F ((z.1, ω), z.2)) :=
    hF.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hR : Measurable R := hFω.comp measurable_swap
  have hiR := crudeEnergy_physical_gaussian_spacetime (b := b) (c := c)
    hκ.le hpω hFω (fun s => heF s ω)
  have hw : Measurable (fun z : Vec d × ℝ => Real.exp (-κ * euclideanSq z.1)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hsq := crudeEnergy_integrable_weighted_sub_sq
    (volume.prod (volume.restrict (Icc b c))) hw
    (fun _ => (Real.exp_pos _).le) hX hR hiU hiR
  change IntegrableOn (fun s => ∫ x,
    Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 * ‖X (x, s) - R (x, s)‖ ^ 2) (Icc b c)
  exact crudeEnergy_integrable_moving_gaussian_mass (b := b) (c := c) (L := L)
    (Z := fun z => X z - R z) hc hL (hX.sub hR) hsq

/-- Mixed Gaussian stability for the actual stationary and physical L² paths.
The interior time inequality is obtained by Fubini from literal endpoint
estimates and then fed to the almost-everywhere form of integral Gronwall. -/
theorem crudeEnergy_ae_mixed_gaussian_mass_gronwall
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Icc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        (∫ x, η b x ^ 2 * ‖(u b) (translate x ω) - (p b ω) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - b)) := by
  intro Λ η
  let A := 16 * Λ ^ 3 * ‖ζ‖ ^ 2
  let D : ℝ × FieldPair d → ℝ := fun z =>
    ∫ x, η z.1 x ^ 2 * ‖U (z.1, translate x z.2) - F ((z.1, z.2), x)‖ ^ 2
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hDU : Measurable (fun z : (ℝ × FieldPair d) × Vec d =>
      U (z.1.1, translate z.2 z.1.2)) := hU.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hη : Measurable (fun z : (ℝ × FieldPair d) × Vec d => η z.1.1 z.2 ^ 2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hD : Measurable D :=
    (hη.mul ((hDU.sub hF).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have heD (s : ℝ) : ∀ᵐ ω ∂reducedLaw Q, D (s, ω) =
      ∫ x, η s x ^ 2 * ‖(u s) (translate x ω) - (p s ω) x‖ ^ 2 := by
    have he := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (hU.comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (u s)).measurable (heU s)
    filter_upwards [he] with ω hω
    apply integral_congr_ae
    filter_upwards [hω, heF s ω] with x hx hy
    change U (s, translate x ω) = (u s) (translate x ω) at hx
    rw [hx, hy]
  have hbound (s : ℝ) (hs : s ∈ Icc b c) : ∀ᵐ ω ∂reducedLaw Q,
      D (s, ω) ≤ D (b, ω) + A * ∫ r in Icc b s, D (r, ω) := by
    have h := crudeEnergy_ae_integrated_mixed_gaussian_mass hab hs.1
      (hs.2.trans_lt hc) hL hu hv hd
      (fun r hr => hgen r ⟨hr.1, hr.2.trans hs.2⟩)
      (fun r hr => hgrad r ⟨hr.1, hr.2.trans hs.2⟩) hC1
      (fun r hr => hphys r ⟨hr.1, hr.2.trans hs.2⟩)
      hU hV heU heV hF hH heF heH
    filter_upwards [h, heD s, heD b] with ω hω hs hb
    rw [hs, hb]
    exact hω
  let J : ℝ × FieldPair d → ℝ := fun z => ∫ r in Icc b z.1, D (r, z.2)
  have hJ : Measurable J := by
    have hm : Measurable (fun z : (ℝ × FieldPair d) × ℝ =>
        if b ≤ z.2 ∧ z.2 ≤ z.1.1 then D (z.2, z.1.2) else 0) :=
      (hD.comp (measurable_snd.prodMk measurable_fst.snd)).ite
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
    have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    simpa only [J, ← integral_indicator measurableSet_Icc, Set.indicator, mem_Icc] using hi
  have hineq : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      D (s, ω) ≤ D (b, ω) + A * J (s, ω) := by
    apply (Measure.ae_ae_comm
      (p := fun s ω => D (s, ω) ≤ D (b, ω) + A * J (s, ω))
      (measurableSet_le hD ((hD.comp (measurable_const.prodMk measurable_snd)).add
        (measurable_const.mul hJ)))).mp
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound s hs
  have hiD : ∀ᵐ ω ∂reducedLaw Q, IntegrableOn (fun s => D (s, ω)) (Icc b c) :=
    crudeEnergy_ae_integrable_mixed_gaussian_mass Q hbc hc hLp hu
      (hC1.mono fun _ h => h.1) hU heU hF heF
  filter_upwards [hineq, hiD, hbound c ⟨hbc, le_rfl⟩, heD c, heD b]
    with ω hω hiω hcω hec heb
  have hint : IntervalIntegrable (fun s => D (s, ω)) volume b c := by
    have hi : IntegrableOn (fun s => D (s, ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using hiω
    exact hi.intervalIntegrable
  have hω' : ∀ᵐ s ∂volume.restrict (Icc b c),
      D (s, ω) ≤ D (b, ω) + A * ∫ r in b..s, D (r, ω) := by
    filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rwa [intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  have hcω' : D (c, ω) ≤ D (b, ω) + A * ∫ r in b..c, D (r, ω) := by
    rwa [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc]
  have h := crudeEnergy_integrable_mass_gronwall_ae hbc hA hint hω' hcω'
  rwa [hec, heb] at h

/-- Stationary L² continuity gives an almost-sure Gaussian initial trace
along a subsequence, without requiring global physical L² data. -/
theorem crudeEnergy_stationary_gaussian_initial_trace_ae {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hc : Continuous u) (κ : ℝ) (hκ : 0 < κ)
    (τ : ℕ → ℝ) (hτ : Tendsto τ atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂reducedLaw Q,
      Tendsto (fun n => ∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖(u (τ (ns n)) - u 0) (translate x ω)‖ ^ 2) atTop (𝓝 0) := by
  let F : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x : Vec d, Real.exp (-κ * euclideanSq x) * ‖(u (τ n) - u 0) (translate x ω)‖ ^ 2
  have hi (n : ℕ) := crudeEnergy_integrable_gaussian_orbit_sq Q κ hκ (u (τ n) - u 0)
  have hlim : Tendsto (fun n => ‖u (τ n) - u 0‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
      (((hc.tendsto 0).comp hτ).sub (tendsto_const_nhds (x := u 0))).norm.pow 2
  have hmean (n : ℕ) : (∫ ω, F n ω ∂reducedLaw Q) =
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x)) * ‖u (τ n) - u 0‖ ^ 2 := (hi n).2
  have hm : Tendsto (fun n => ∫ ω, F n ω ∂reducedLaw Q) atTop (𝓝 0) := by
    simpa only [hmean, mul_zero] using
      hlim.const_mul (∫ x : Vec d, Real.exp (-κ * euclideanSq x))
  have hn (n : ℕ) : eLpNorm (F n) 1 (reducedLaw Q) =
      ENNReal.ofReal (∫ ω, F n ω ∂reducedLaw Q) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).1.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n).1]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    exact Real.norm_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have he : Tendsto (fun n => eLpNorm (F n - 0) 1 (reducedLaw Q)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_zero, hn, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hm
  exact (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) he).exists_seq_tendsto_ae

/-- A Gaussian weight bounded by one cannot increase physical L² mass. -/
theorem crudeEnergy_physical_gaussian_mass_le_norm_sq {d : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ) (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2) ≤ ‖f‖ ^ 2 := by
  have hn : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [hn]
  apply integral_mono (crudeEnergy_physical_gaussian_endpoint hκ f)
    (Lp.memLp f).norm.integrable_sq
  intro x
  apply mul_le_of_le_one_left (sq_nonneg _)
  apply Real.exp_le_one_iff.mpr
  have hs : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hκ) hs

/-- Physical C0 continuity controls the Gaussian initial defect along the
whole time filter, so no environment-dependent time subsequence is needed. -/
theorem crudeEnergy_physical_gaussian_initial_trace {d : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ) {p : ℝ → Lp ℂ 2 (volume : Measure (Vec d))}
    (hp : ContinuousAt p 0) :
    Tendsto (fun t => ∫ x, Real.exp (-κ * euclideanSq x) *
      ‖(p t - p 0) x‖ ^ 2) (𝓝 0) (𝓝 0) := by
  have hlim : Tendsto (fun t => ‖p t - p 0‖ ^ 2) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
      (hp.tendsto.sub (tendsto_const_nhds (x := p 0))).norm.pow 2
  exact squeeze_zero (fun t => integral_nonneg fun x =>
    mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
    (fun t => crudeEnergy_physical_gaussian_mass_le_norm_sq hκ (p t - p 0)) hlim

private theorem crudeEnergy_norm_sub_sq_three (z z₀ w w₀ : ℂ) :
    ‖z - w‖ ^ 2 ≤ 3 * (‖z - z₀‖ ^ 2 + ‖z₀ - w₀‖ ^ 2 + ‖w₀ - w‖ ^ 2) := by
  have he : z - w = (z - z₀) + (z₀ - w₀) + (w₀ - w) := by ring
  have hn : ‖z - w‖ ≤ ‖z - z₀‖ + ‖z₀ - w₀‖ + ‖w₀ - w‖ := by
    rw [he]
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hsq := pow_le_pow_left₀ (norm_nonneg (z - w)) hn 2
  nlinarith [sq_nonneg (‖z - z₀‖ - ‖z₀ - w₀‖),
    sq_nonneg (‖z₀ - w₀‖ - ‖w₀ - w‖), sq_nonneg (‖w₀ - w‖ - ‖z - z₀‖)]

/-- The initial comparison separates the stationary and physical continuity
defects from the actual initial-data discrepancy. A tighter Gaussian at
positive time is bounded by the one fixed at initial time. -/
theorem crudeEnergy_gaussian_initial_comparison {d : ℕ} {κ κ' : ℝ}
    (hκ : κ ≤ κ') {f f₀ g g₀ : Vec d → ℂ}
    (hiF : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖f x - f₀ x‖ ^ 2) volume)
    (hi₀ : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖f₀ x - g₀ x‖ ^ 2) volume)
    (hiG : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2) volume) :
    (∫ x, Real.exp (-κ' * euclideanSq x) * ‖f x - g x‖ ^ 2) ≤
      3 * ((∫ x, Real.exp (-κ * euclideanSq x) * ‖f x - f₀ x‖ ^ 2) +
        (∫ x, Real.exp (-κ * euclideanSq x) * ‖f₀ x - g₀ x‖ ^ 2) +
        (∫ x, Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2)) := by
  have hi := ((hiF.add hi₀).add hiG).const_mul 3
  have hle : (∫ x, Real.exp (-κ' * euclideanSq x) * ‖f x - g x‖ ^ 2) ≤
      ∫ x, 3 * ((Real.exp (-κ * euclideanSq x) * ‖f x - f₀ x‖ ^ 2 +
        Real.exp (-κ * euclideanSq x) * ‖f₀ x - g₀ x‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2) :=
    integral_mono_of_nonneg
      (ae_of_all _ fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg ‖f x - g x‖)) hi
      (ae_of_all _ fun x => ?_)
  · rw [integral_const_mul] at hle
    have hadd : (∫ x, (Real.exp (-κ * euclideanSq x) * ‖f x - f₀ x‖ ^ 2 +
        Real.exp (-κ * euclideanSq x) * ‖f₀ x - g₀ x‖ ^ 2) +
        Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2) =
        ((∫ x, Real.exp (-κ * euclideanSq x) * ‖f x - f₀ x‖ ^ 2) +
        (∫ x, Real.exp (-κ * euclideanSq x) * ‖f₀ x - g₀ x‖ ^ 2)) +
        (∫ x, Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2) :=
      (integral_add (hiF.add hi₀) hiG).trans
        (congrArg (fun r => r + ∫ x, Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2)
          (integral_add hiF hi₀))
    exact hle.trans_eq (congrArg (fun r => 3 * r) hadd)
  · change Real.exp (-κ' * euclideanSq x) * ‖f x - g x‖ ^ 2 ≤ _
    have hs : 0 ≤ euclideanSq x := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    calc
      _ ≤ Real.exp (-κ * euclideanSq x) * ‖f x - g x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hs)) (sq_nonneg _)
      _ ≤ _ := by
        have hn := mul_le_mul_of_nonneg_left
          (crudeEnergy_norm_sub_sq_three (f x) (f₀ x) (g x) (g₀ x)) (Real.exp_nonneg (-κ * euclideanSq x))
        nlinarith only [hn]

/-- Gaussian stability at positive starting times extends to initial time.
The actual initial-data discrepancy is retained; the two continuity defects
vanish along one deterministic subsequence of times for almost every environment. -/
theorem crudeEnergy_ae_gaussian_initial_mass_bound {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u : ℝ → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u)
    {p : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hp : ∀ᵐ ω ∂reducedLaw Q, ContinuousAt (fun s => p s ω) 0)
    {τ : ℕ → ℝ} (hτ : Tendsto τ atTop (𝓝 0))
    {κ κc A c : ℝ} (hκ : 0 < κ) {κn : ℕ → ℝ} (hκn : ∀ n, κ ≤ κn n)
    (hbound : ∀ n, ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-κc * euclideanSq x) *
        ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
      (∫ x, Real.exp (-κn n * euclideanSq x) *
        ‖(u (τ n)) (translate x ω) - (p (τ n) ω) x‖ ^ 2) *
        Real.exp (A * (c - τ n))) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-κc * euclideanSq x) *
        ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
      3 * (∫ x, Real.exp (-κ * euclideanSq x) *
        ‖(u 0) (translate x ω) - (p 0 ω) x‖ ^ 2) * Real.exp (A * c) := by
  obtain ⟨ns, hns, htrace⟩ :=
    crudeEnergy_stationary_gaussian_initial_trace_ae Q hu κ hκ τ hτ
  have hτns : Tendsto (fun n => τ (ns n)) atTop (𝓝 0) :=
    hτ.comp hns.tendsto_atTop
  have heU (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      (u (τ (ns n)) - u 0) (translate x ω) =
        (u (τ (ns n))) (translate x ω) - (u 0) (translate x ω) :=
    ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable _).measurable
      ((Lp.stronglyMeasurable _).measurable.sub (Lp.stronglyMeasurable _).measurable)
      (Lp.coeFn_sub _ _)
  have hiU (n : ℕ) := crudeEnergy_ae_gaussian_endpoint Q hκ (u (τ (ns n)))
  filter_upwards [hp, htrace, crudeEnergy_ae_gaussian_endpoint Q hκ (u 0),
      ae_all_iff.mpr hiU, ae_all_iff.mpr heU, ae_all_iff.mpr hbound]
      with ω hpω htω hi₀ hiω heω hbω
  let w : Vec d → ℝ := fun x => Real.exp (-κ * euclideanSq x)
  let B : ℝ := ∫ x, w x * ‖(u 0) (translate x ω) - (p 0 ω) x‖ ^ 2
  let F : ℕ → ℝ := fun n => ∫ x, w x *
    ‖(u (τ (ns n))) (translate x ω) - (u 0) (translate x ω)‖ ^ 2
  let H : ℕ → ℝ := fun n => ∫ x, w x * ‖(p 0 ω) x - (p (τ (ns n)) ω) x‖ ^ 2
  have hF : Tendsto F atTop (𝓝 0) := by
    have he (n : ℕ) : F n = ∫ x, Real.exp (-κ * euclideanSq x) *
        ‖(u (τ (ns n)) - u 0) (translate x ω)‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [heω n] with x hx
      simp only [w, hx]
    rw [show F = (fun n => ∫ x, Real.exp (-κ * euclideanSq x) *
      ‖(u (τ (ns n)) - u 0) (translate x ω)‖ ^ 2) from funext he]
    exact htω
  have hH : Tendsto H atTop (𝓝 0) := by
    have he (n : ℕ) : H n = ∫ x, Real.exp (-κ * euclideanSq x) *
        ‖(p (τ (ns n)) ω - p 0 ω) x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (p (τ (ns n)) ω) (p 0 ω)] with x hx
      simp only [w, hx, Pi.sub_apply]
      rw [norm_sub_rev]
    rw [show H = (fun n => ∫ x, Real.exp (-κ * euclideanSq x) *
      ‖(p (τ (ns n)) ω - p 0 ω) x‖ ^ 2) from funext he]
    simpa only [Function.comp_def] using
      (crudeEnergy_physical_gaussian_initial_trace hκ.le hpω).comp hτns
  have hw : Measurable w := by
    dsimp only [w, euclideanSq, dot]
    fun_prop
  have hf₀ : Measurable (fun x => (u 0) (translate x ω)) :=
    (Lp.stronglyMeasurable _).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hg (s : ℝ) : Measurable (fun x => (p s ω) x) :=
    (Lp.stronglyMeasurable _).measurable
  have hiB := crudeEnergy_integrable_weighted_sub_sq volume hw
    (fun _ => (Real.exp_pos _).le) hf₀ (hg 0) hi₀
    (crudeEnergy_physical_gaussian_endpoint hκ.le (p 0 ω))
  have hcomp (n : ℕ) :
      (∫ x, Real.exp (-κn (ns n) * euclideanSq x) *
        ‖(u (τ (ns n))) (translate x ω) - (p (τ (ns n)) ω) x‖ ^ 2) ≤
          3 * (F n + B + H n) := by
    have hf : Measurable (fun x => (u (τ (ns n))) (translate x ω)) :=
      (Lp.stronglyMeasurable _).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
    exact crudeEnergy_gaussian_initial_comparison (hκn (ns n))
      (crudeEnergy_integrable_weighted_sub_sq volume hw (fun _ => (Real.exp_pos _).le)
        hf hf₀ (hiω n) hi₀) hiB
      (crudeEnergy_integrable_weighted_sub_sq volume hw (fun _ => (Real.exp_pos _).le)
        (hg 0) (hg (τ (ns n)))
        (crudeEnergy_physical_gaussian_endpoint hκ.le (p 0 ω))
        (crudeEnergy_physical_gaussian_endpoint hκ.le (p (τ (ns n)) ω)))
  have hlim : Tendsto (fun n => 3 * (F n + B + H n) *
      Real.exp (A * (c - τ (ns n)))) atTop (𝓝 (3 * B * Real.exp (A * c))) := by
    have harg : Tendsto (fun n => A * (c - τ (ns n))) atTop (𝓝 (A * c)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds (x := A)).mul ((tendsto_const_nhds (x := c)).sub hτns)
    have he := (Real.continuous_exp.tendsto (A * c)).comp harg
    simpa only [zero_add, add_zero, sub_zero, Function.comp_def] using
      (((hF.add_const B).add hH).const_mul 3).mul he
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => (hbω (ns n)).trans
    (mul_le_mul_of_nonneg_right (hcomp n) (Real.exp_nonneg _))

private def crudeEnergyC0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem crudeEnergyC0Graph.map {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : crudeEnergyC0Graph P f g) (t : ℝ≥0) :
    crudeEnergyC0Graph P (P t f) (P t g) := by
  change Tendsto _ _ _
  have h := ((P t).continuous.tendsto g).comp hfg
  convert h using 1
  ext s
  simp only [Function.comp_apply, map_smul, map_sub]
  have hc : P t (P s f) = P s (P t f) := by
    rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm, hPm,
      ContinuousLinearMap.comp_apply]
  rw [hc]

private theorem crudeEnergyC0Graph.hasDerivWithinAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : crudeEnergyC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
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

private theorem crudeEnergyC0Graph.integral_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : crudeEnergyC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, P s.toNNReal g) = P t.toNNReal f - f := by
  have hf := (hPc f).comp continuous_real_toNNReal
  have hg := (hPc g).comp continuous_real_toNNReal
  simpa only [Function.comp_apply, Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hf.continuousOn
      (fun s hs => (hfg.hasDerivWithinAt_orbit hPm s hs.1.le).Ioi_of_Ici)
      (hg.intervalIntegrable 0 t)

private theorem crudeEnergyC0Graph.hasDerivAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : crudeEnergyC0Graph P f g) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => P s.toNNReal f) (P t.toNNReal g) t := by
  have hd := (((hPc g).comp continuous_real_toNNReal).integral_hasStrictDerivAt 0 t).hasDerivAt
  have hd' := hd.add_const f
  apply hd'.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds ht] with s hs
  exact (eq_add_of_sub_eq (hfg.integral_orbit hP0 hPm hPc s hs.le).symm)

private theorem crudeEnergyC0Graph_complex_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {f g : E} :
    crudeEnergyC0Graph (fun t => (P t).restrictScalars ℝ) f g ↔
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  simp only [crudeEnergyC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl

private theorem crudeEnergy_complex_domain_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℂ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℂ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    (R : E → E → Prop)
    (hR : ∀ f g, Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g) ↔ R f g)
    {f g : E} (hfg : R f g) :
    Continuous (fun t : ℝ => P t.toNNReal f) ∧
    Continuous (fun t : ℝ => P t.toNNReal g) ∧
    (∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => P s.toNNReal f)
      (P t.toNNReal g) t) ∧
    ∀ t : ℝ≥0, R (P t f) (P t g) := by
  let p := fun t => (P t).restrictScalars ℝ
  have hp0 : p 0 = ContinuousLinearMap.id ℝ E :=
    congrArg (fun A => A.restrictScalars ℝ) hP0
  have hpm : ∀ s t, p (s + t) = (p s).comp (p t) := fun s t =>
    congrArg (fun A => A.restrictScalars ℝ) (hPm s t)
  have hpc : ∀ f, Continuous (fun t => p t f) := hPc
  have h : crudeEnergyC0Graph p f g :=
    crudeEnergyC0Graph_complex_iff.mpr ((hR f g).mpr hfg)
  refine ⟨(hPc f).comp continuous_real_toNNReal,
    (hPc g).comp continuous_real_toNNReal, ?_, ?_⟩
  · exact fun t ht => h.hasDerivAt_orbit hp0 hpm hpc t ht
  · intro t
    apply (hR _ _).mp
    exact crudeEnergyC0Graph_complex_iff.mp (h.map hpm t)

private theorem crudeEnergy_complex_generator_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {f g : E}
    (hfg : Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 g)) (c : ℂ) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t (c • f) - c • f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (c • g)) := by
  simpa only [map_smul, ← smul_sub, smul_smul, mul_comm] using hfg.const_smul c

/-- Time averaging arbitrary physical data produces a genuine C1 generator-domain
orbit. Both the path and its derivative remain continuous at initial time. -/
theorem crudeEnergy_physical_forward_averaged_orbit
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
    Continuous (fun t : ℝ => P t.toNNReal fε) ∧
    Continuous (fun t : ℝ => P t.toNNReal gε) ∧
    (∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => P s.toNNReal fε)
      (P t.toNNReal gε) t) ∧
    ∀ t : ℝ≥0, IsPhysicalComplexGeneratorPair a i ζ (P t fε) (P t gε) := by
  intro fε gε
  apply crudeEnergy_complex_domain_orbit hP.1 hP.2.1 hP.2.2.1
    (IsPhysicalComplexGeneratorPair a i ζ) hP.2.2.2
  apply (hP.2.2.2 _ _).mp
  exact crudeEnergy_complex_generator_smul
    ((hP.2.2.2 _ _).mpr (physical_forward_generator_timeIntegral a i ζ P hP f ε)) _

/-- The same time-average construction applies to the actual transpose weak
physical graph, without changing the sign or location of its drift term. -/
theorem crudeEnergy_physical_transpose_averaged_orbit
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hT : IsPhysicalComplexTransposeSemigroup a i ζ P T)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), T s.toNNReal f
    let gε := ((ε : ℝ) : ℂ)⁻¹ • (T ε f - f)
    Continuous (fun t : ℝ => T t.toNNReal fε) ∧
    Continuous (fun t : ℝ => T t.toNNReal gε) ∧
    (∀ t : ℝ, 0 < t → HasDerivAt (fun s : ℝ => T s.toNNReal fε)
      (T t.toNNReal gε) t) ∧
    ∀ t : ℝ≥0, IsPhysicalComplexTransposeGeneratorPair a i ζ (T t fε) (T t gε) := by
  intro fε gε
  apply crudeEnergy_complex_domain_orbit hT.1 hT.2.1 hT.2.2.1
    (IsPhysicalComplexTransposeGeneratorPair a i ζ) hT.2.2.2.1
  apply (hT.2.2.2.1 _ _).mp
  exact crudeEnergy_complex_generator_smul
    ((hT.2.2.2.1 _ _).mpr (physical_transpose_generator_timeIntegral a i ζ P T hT f ε)) _

/-- Time averages of a strongly continuous complex evolution converge to its
actual initial datum; the same holds after applying any fixed evolution time. -/
theorem crudeEnergy_complex_time_average_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℂ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℂ E)
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    Tendsto (fun ε : ℝ≥0 => P t (((ε : ℝ) : ℂ)⁻¹ •
      ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (P t f)) := by
  have hu : Continuous (fun s : ℝ => P s.toNNReal f) :=
    (hPc f).comp continuous_real_toNNReal
  have hd := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt
  have hh := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ))
      (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have ht : Tendsto (fun ε : ℝ≥0 => ((ε : ℝ) : ℂ)⁻¹ •
      ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
    have htR : Tendsto (fun ε : ℝ≥0 => (ε : ℝ)⁻¹ •
        ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
      simpa only [Function.comp_def, slope_def_module, sub_zero,
        intervalIntegral.integral_same, Real.toNNReal_zero, hP0,
        ContinuousLinearMap.id_apply] using hh.comp hcoe
    convert htR using 1
    ext ε
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
    rfl
  exact ((P t).continuous.tendsto f).comp ht

/-- The actual mixed generator comparison extends to its initial time on an
arbitrary finite interval. No Gaussian identification is assumed at that time:
the conclusion retains exactly its initial stationary/physical discrepancy. -/
theorem crudeEnergy_ae_mixed_gaussian_initial_gronwall
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a c L : ℝ}
    (hac : a < c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Ioc a c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Ioc a c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Ioc a c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        3 * (∫ x, η a x ^ 2 * ‖(u a) (translate x ω) - (p a ω) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - a)) := by
  intro Λ η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let τ : ℕ → ℝ := fun n => (c - a) / ((n : ℝ) + 1)
  have hτ : Tendsto τ atTop (𝓝 0) := by
    simpa only [τ, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c - a)
  have hτpos (n : ℕ) : 0 < τ n := div_pos (sub_pos.mpr hac) (by positivity)
  have hτle (n : ℕ) : τ n ≤ c - a := by
    dsimp only [τ]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hκ : 0 < 2 / (L * (2 - a)) := div_pos (by norm_num)
    (mul_pos hLp (by linarith))
  have hκn (n : ℕ) : 2 / (L * (2 - a)) ≤ 2 / (L * (2 - (a + τ n))) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hLp (by linarith [hτle n]))
    exact mul_le_mul_of_nonneg_left (by linarith [hτpos n]) hLp.le
  have hη (s : ℝ) (x : Vec d) :
      Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 =
        Real.exp (-(2 / (L * (2 - s))) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hshift : a + (c - a) = c := by ring
  have hb (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-(2 / (L * (2 - c))) * euclideanSq x) *
        ‖(u (a + (c - a))) (translate x ω) - (p (a + (c - a)) ω) x‖ ^ 2) ≤
      (∫ x, Real.exp (-(2 / (L * (2 - (a + τ n)))) * euclideanSq x) *
        ‖(u (a + τ n)) (translate x ω) - (p (a + τ n) ω) x‖ ^ 2) *
        Real.exp ((16 * Λ ^ 3 * ‖ζ‖ ^ 2) * ((c - a) - τ n)) := by
    have hn := crudeEnergy_ae_mixed_gaussian_mass_gronwall
      (show a < a + τ n by linarith [hτpos n])
      (show a + τ n ≤ c by linarith [hτle n]) hc hL hu hv hd
      (fun s hs => hgen s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      (fun s hs => hgrad s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      hC1 (fun s hs => hphys s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      hU hV heU heV hF hH heF heH
    simpa only [hη, hshift, show (c - a) - τ n = c - (a + τ n) by ring] using hn
  have hi := crudeEnergy_ae_gaussian_initial_mass_bound Q
    (u := fun s => u (a + s))
    (p := fun s ω => p (a + s) ω)
    (hu.comp (continuous_const.add continuous_id))
    (by
      filter_upwards [hC1] with ω hω
      exact (hω.1.comp (continuous_const.add continuous_id)).continuousAt)
    hτ hκ hκn hb
  simpa only [η, hη, hshift, add_zero] using hi

/-- A physical L2 family has a jointly measurable representative even though
spatial volume is infinite. Finite restrictions are glued using the first
member of a measurable exhaustion containing the spatial point. -/
theorem crudeEnergy_exists_joint_l2_representative_sigmaFinite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [SigmaFinite μ]
    {u : T → Lp ℂ 2 μ} (hu : StronglyMeasurable u) :
    ∃ U : T × Ω → ℂ, Measurable U ∧ ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t := by
  classical
  let R (n : ℕ) := LpToLpRestrictCLM Ω ℂ ℂ μ 2 (spanningSets μ n)
  have hex (n : ℕ) : ∃ U : T × Ω → ℂ, Measurable U ∧
      ∀ t, (fun x => U (t, x)) =ᵐ[μ.restrict (spanningSets μ n)] R n (u t) := by
    letI : IsFiniteMeasure (μ.restrict (spanningSets μ n)) :=
      ⟨by simpa only [Measure.restrict_apply_univ] using measure_spanningSets_lt_top μ n⟩
    exact StronglyMeasurable.exists_joint_l2_representative ((R n).continuous.comp_stronglyMeasurable hu)
  choose V hV heV using hex
  let U : T × Ω → ℂ := fun p => V (spanningSetsIndex μ p.2) p
  have hVm : Measurable (fun z : ℕ × (T × Ω) => V z.1 z.2) :=
    measurable_from_prod_countable_right (fun n => hV n)
  have hU : Measurable U :=
    hVm.comp
      (((measurableSet_spanningSetsIndex μ).comp measurable_snd).prodMk measurable_id)
  refine ⟨U, hU, fun t => ?_⟩
  have he (n : ℕ) : ∀ᵐ x ∂μ, x ∈ spanningSets μ n → V n (t, x) = (u t) x := by
    apply (ae_restrict_iff' (measurableSet_spanningSets μ n)).mp
    exact (heV n t).trans (LpToLpRestrictCLM_coeFn ℂ (spanningSets μ n) (u t))
  filter_upwards [ae_all_iff.mpr he] with x hx
  exact hx (spanningSetsIndex μ x) (mem_spanningSetsIndex μ x)

/-- Joint representatives needed by the mixed energy argument are constructed
from the actual L2 paths. No extra representative or identification hypothesis
is needed in the resulting initial Gaussian comparison. -/
theorem crudeEnergy_ae_mixed_gaussian_initial_gronwall_of_stronglyMeasurable
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a c L : ℝ}
    (hac : a < c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Ioc a c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Ioc a c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hp : StronglyMeasurable p) (hq : StronglyMeasurable q)
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p (s, ω)) ∧
      Continuous (fun s => q (s, ω)) ∧
      ∀ s, a < s → HasDerivAt (fun r => p (r, ω)) (q (s, ω)) s)
    (hphys : ∀ s ∈ Ioc a c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p (s, ω)) (q (s, ω))) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p (c, ω)) x‖ ^ 2) ≤
        3 * (∫ x, η a x ^ 2 * ‖(u a) (translate x ω) - (p (a, ω)) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - a)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative hu.stronglyMeasurable
  obtain ⟨V, hV, heV⟩ := StronglyMeasurable.exists_joint_l2_representative hv.stronglyMeasurable
  obtain ⟨F, hF, heF⟩ := crudeEnergy_exists_joint_l2_representative_sigmaFinite hp
  obtain ⟨H, hH, heH⟩ := crudeEnergy_exists_joint_l2_representative_sigmaFinite hq
  exact crudeEnergy_ae_mixed_gaussian_initial_gronwall
    (p := fun s ω => p (s, ω)) (q := fun s ω => q (s, ω)) hac hc hL hu hv hd hgen hgrad
    hC1 hphys hU hV heU heV hF hH (fun s ω => heF (s, ω)) (fun s ω => heH (s, ω))

/-- The actual forward stationary domain orbit can be compared with a physical
time average of arbitrary measurable L2 data. The initial discrepancy is the
only term on the right; no stationary/physical identification is assumed. -/
theorem crudeEnergy_ae_forward_averaged_gaussian_comparison
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ (ε : ℝ≥0) (c L : ℝ), 0 < c →
      64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let fε : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
      ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), S ω s.toNNReal (fR ω)
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fε ω)) x‖ ^ 2) ≤
        3 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fε ω) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  intro S hS hSm fR hfR ε c L hc hL fε Λ
  let a₀ : ℝ := 1 - c
  let gε : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
    ((ε : ℝ) : ℂ)⁻¹ • (S ω ε (fR ω) - fR ω)
  have hmean : StronglyMeasurable fε := by
    have hm : Measurable (fun z : FieldPair d × ℝ => S z.1 z.2.toNNReal (fR z.1)) :=
      hSm.comp ((hfR.measurable.comp measurable_fst).prodMk
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
    have hi := hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (ε : ℝ)))
    simpa only [fε, intervalIntegral.integral_of_le ε.coe_nonneg, Pi.smul_apply] using
      hi.fun_const_smul (((ε : ℝ) : ℂ)⁻¹)
  have hdiff : StronglyMeasurable gε := by
    simpa only [gε, Pi.smul_apply, Pi.sub_apply, Function.comp_def, id_eq] using
      ((hSm.comp (hfR.measurable.prodMk (measurable_const.prodMk measurable_id))).stronglyMeasurable.sub
        hfR).fun_const_smul (((ε : ℝ) : ℂ)⁻¹)
  let p : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun z => S z.2 (z.1 - a₀).toNNReal (fε z.2)
  let q : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun z => S z.2 (z.1 - a₀).toNNReal (gε z.2)
  have hp : StronglyMeasurable p :=
    (hSm.comp ((hmean.measurable.comp measurable_snd).prodMk
      ((measurable_real_toNNReal.comp (measurable_fst.sub_const a₀)).prodMk
        measurable_snd))).stronglyMeasurable
  have hq : StronglyMeasurable q :=
    (hSm.comp ((hdiff.measurable.comp measurable_snd).prodMk
      ((measurable_real_toNNReal.comp (measurable_fst.sub_const a₀)).prodMk
        measurable_snd))).stronglyMeasurable
  have horbit := crudeEnergy_complex_domain_orbit hP.1 hP.2.1 hP.2.2.1
    (IsComplexGeneratorPair Q i ζ) hP.2.2.2 hfg
  obtain ⟨G, _, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  have hshift : Continuous (fun s : ℝ => s - a₀) := continuous_id.sub continuous_const
  have hderiv (s : ℝ) (hs : a₀ < s) :
      HasDerivAt (fun r : ℝ => P (r - a₀).toNNReal f) (P (s - a₀).toNNReal g) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (horbit.2.2.1 (s - a₀) (sub_pos.mpr hs)).scomp s ((hasDerivAt_id s).sub_const a₀)
  have hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p (s, ω)) ∧
      Continuous (fun s => q (s, ω)) ∧
      ∀ s, a₀ < s → HasDerivAt (fun r => p (r, ω)) (q (s, ω)) s := by
    filter_upwards [hS] with ω hω
    have h := crudeEnergy_physical_forward_averaged_orbit hω (fR ω) ε
    refine ⟨h.1.comp hshift, h.2.1.comp hshift, fun s hs => ?_⟩
    simpa only [p, q, fε, gε, Function.comp_def, id_eq, one_smul] using
      (h.2.2.1 (s - a₀) (sub_pos.mpr hs)).scomp s ((hasDerivAt_id s).sub_const a₀)
  have hphys (s : ℝ) (_ : s ∈ Ioc a₀ 1) : ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexGeneratorPair ω.1 i ζ (p (s, ω)) (q (s, ω)) := by
    filter_upwards [hS] with ω hω
    exact (crudeEnergy_physical_forward_averaged_orbit hω (fR ω) ε).2.2.2 (s - a₀).toNNReal
  have hb := crudeEnergy_ae_mixed_gaussian_initial_gronwall_of_stronglyMeasurable
    (G := fun s => G (s - a₀)) (show a₀ < 1 by dsimp only [a₀]; linarith)
    (by norm_num : (1 : ℝ) < 2) hL (horbit.1.comp hshift) (horbit.2.1.comp hshift) hderiv
    (fun s _ => horbit.2.2.2 (s - a₀).toNNReal) (fun s _ => hG (s - a₀)) hp hq hC1 hphys
  filter_upwards [hS, hb] with ω hω hωb
  have hend : 1 - a₀ = c := by dsimp only [a₀]; ring
  have hstart : 2 - a₀ = 1 + c := by dsimp only [a₀]; ring
  simpa only [p, Function.comp_def, hend, hstart, sub_self, Real.toNNReal_zero, hP.1, hω.1,
    ContinuousLinearMap.id_apply, show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using hωb

/-- Changing the physical datum in a Gaussian discrepancy costs only its
ordinary physical L2 distance. This also applies to removing time averages. -/
theorem crudeEnergy_gaussian_compare_physical_data {d : ℕ} {κ : ℝ}
    (hκ : 0 ≤ κ) {f : Vec d → ℂ} (hf : Measurable f)
    (hi : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2) volume)
    (g g₀ : Lp ℂ 2 (volume : Measure (Vec d))) :
    (∫ x, Real.exp (-κ * euclideanSq x) * ‖f x - g x‖ ^ 2) ≤
      3 * ((∫ x, Real.exp (-κ * euclideanSq x) * ‖f x - g₀ x‖ ^ 2) + ‖g₀ - g‖ ^ 2) := by
  have hw : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    unfold euclideanSq dot
    fun_prop
  have hi₀ := crudeEnergy_integrable_weighted_sub_sq volume hw
    (fun _ => Real.exp_nonneg _) hf (Lp.stronglyMeasurable g₀).measurable hi
    (crudeEnergy_physical_gaussian_endpoint hκ g₀)
  have he : (fun x => Real.exp (-κ * euclideanSq x) * ‖g₀ x - g x‖ ^ 2) =ᵐ[volume]
      (fun x => Real.exp (-κ * euclideanSq x) * ‖(g₀ - g) x‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub g₀ g] with x hx
    rw [hx]
    rfl
  have hiG := (crudeEnergy_physical_gaussian_endpoint hκ (g₀ - g)).congr he.symm
  have hle := crudeEnergy_gaussian_initial_comparison (le_refl κ)
    (f := f) (f₀ := f) (g := g) (g₀ := g₀)
    (by simp only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero];
        exact integrable_zero _ _ _) hi₀ hiG
  simp only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero,
    integral_zero, zero_add] at hle
  apply hle.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply add_le_add_right
  rw [integral_congr_ae he]
  exact crudeEnergy_physical_gaussian_mass_le_norm_sq hκ (g₀ - g)

/-- Removing the physical time averages gives an actual stationary/physical
forward comparison at every finite horizon, with the true initial defect. -/
theorem crudeEnergy_ae_forward_gaussian_comparison
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fR ω)) x‖ ^ 2) ≤
        27 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fR ω) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  intro S hS hSm fR hfR c L hc hL Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hε : Tendsto ε atTop (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · apply NNReal.tendsto_coe.mp
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · change 0 < 1 / ((n : ℝ) + 1)
      positivity
  let fε : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun n ω =>
    (((ε n : ℝ)) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε n : ℝ), S ω s.toNNReal (fR ω)
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb (n : ℕ) := crudeEnergy_ae_forward_averaged_gaussian_comparison
    hP hfg S hS hSm fR hfR (ε n) c L hc hL
  have hi₀ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hLp (by linarith : 0 < 1 + c))) f
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) hLp) (P c.toNNReal f)
  filter_upwards [hS, ae_all_iff.mpr hb, hi₀, hi₁] with ω hω hbω hi₀ω hi₁ω
  have ht₀ := (crudeEnergy_complex_time_average_tendsto hω.1 hω.2.2.1 (fR ω) 0).comp hε
  have ht₁ := (crudeEnergy_complex_time_average_tendsto hω.1 hω.2.2.1
    (fR ω) c.toNNReal).comp hε
  have ht₀' : Tendsto (fun n => fε n ω) atTop (𝓝 (fR ω)) := by
    simpa only [fε, Function.comp_def, hω.1, ContinuousLinearMap.id_apply] using! ht₀
  have hdist₀ : Tendsto (fun n => ‖fR ω - fε n ω‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), norm_sub_rev] using
      (ht₀'.sub_const (fR ω)).norm.pow 2
  have hdist₁ : Tendsto
      (fun n => ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [fε, Function.comp_def, sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0)] using!
      (ht₁.sub_const (S ω c.toNNReal (fR ω))).norm.pow 2
  let B : ℝ := ∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
    ‖f (translate x ω) - (fR ω) x‖ ^ 2
  let E : ℝ := Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c)
  have hlim : Tendsto (fun n => 27 * (B + ‖fR ω - fε n ω‖ ^ 2) * E +
      3 * ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2)
      atTop (𝓝 (27 * B * E)) := by
    simpa only [add_zero, mul_zero] using
      (((hdist₀.const_add B).const_mul 27).mul_const E).add (hdist₁.const_mul 3)
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hinit := crudeEnergy_gaussian_compare_physical_data
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hLp.le (by linarith : 0 ≤ 1 + c)))
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
    hi₀ω (fε n ω) (fR ω)
  have hlast := crudeEnergy_gaussian_compare_physical_data
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLp.le)
    ((Lp.stronglyMeasurable (P c.toNNReal f)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
    hi₁ω (S ω c.toNNReal (fR ω)) (S ω c.toNNReal (fε n ω))
  simp only [← hη, Function.comp_def, id_eq] at hinit hlast
  have hmiddle := (hbω n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 3)) (Real.exp_nonneg _))
  apply hlast.trans
  calc
    _ ≤ 3 * (3 * (3 * (B + ‖fR ω - fε n ω‖ ^ 2)) * E +
        ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hmiddle (le_refl _)) (by norm_num)
    _ = _ := by ring

/-- A jointly measurable family of physical L2 functions defines a strongly
measurable family of L2 classes. The proof uses measurable distances and the
separability of physical L2, so no continuity of the initial field is assumed. -/
theorem crudeEnergy_stronglyMeasurable_physical_toLp
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (f : Ω → Vec d → ℂ)
    (hf : Measurable (fun s : Ω × Vec d => f s.1 s.2))
    (hL : ∀ ω, MemLp (f ω) 2 (volume : Measure (Vec d))) :
    StronglyMeasurable (fun ω => (hL ω).toLp (f ω)) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  letI : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) :=
    Lp.SecondCountableTopology
  apply Measurable.stronglyMeasurable
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

/-- Expanding Euclidean cutoffs of an arbitrary stationary L2 field admit
strongly measurable physical L2 classes. One environment event gives their
literal spatial representatives simultaneously for every cutoff radius. -/
theorem crudeEnergy_exists_measurable_spatial_cutoffs
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ F : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, StronglyMeasurable (F n)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ n,
        (F n ω : Vec d → ℂ) =ᵐ[volume]
          {x : Vec d | euclideanNorm (x - 0) ≤ (n : ℝ)}.indicator
            (fun x => f (translate x ω)) := by
  classical
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let K : ℕ → Set (Vec d) := fun n => {x | euclideanNorm (x - 0) ≤ (n : ℝ)}
  have hK (n : ℕ) : IsCompact (K n) := isCompact_physical_euclidean_closedBall 0 n
  have hae : ∀ᵐ ω ∂reducedLaw Q, ∀ n,
      MemLp ((K n).indicator (fun x => f (translate x ω))) 2 volume := by
    filter_upwards [ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) f] with ω hω
    intro n
    exact (memLp_indicator_iff_restrict (hK n).measurableSet).mpr (hω (K n) (hK n))
  obtain ⟨N, hNsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let b : ℕ → FieldPair d → Vec d → ℂ := fun n ω x =>
    if ω ∈ N then 0 else (K n).indicator (fun y => f (translate y ω)) x
  have hbm (n : ℕ) : Measurable (fun p : FieldPair d × Vec d => b n p.1 p.2) := by
    have hm : Measurable (fun p : FieldPair d × Vec d => f (translate p.2 p.1)) :=
      (Lp.stronglyMeasurable f).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst))
    have hi : Measurable (fun p : FieldPair d × Vec d =>
        (K n).indicator (fun y => f (translate y p.1)) p.2) := by
      convert hm.indicator ((hK n).measurableSet.preimage measurable_snd) using 1
      funext p
      simp only [Set.indicator_apply, Set.mem_preimage]
    exact Measurable.ite (hNm.preimage measurable_fst) measurable_const hi
  have hbL (n : ℕ) (ω : FieldPair d) : MemLp (b n ω) 2 volume := by
    by_cases hω : ω ∈ N
    · simpa only [b, ite_eq_left hω] using (MemLp.zero' : MemLp (fun _ : Vec d => (0 : ℂ)) 2 volume)
    · have hg : ∀ n, MemLp ((K n).indicator (fun x => f (translate x ω))) 2 volume := by
        by_contra h
        exact hω (hNsub h)
      simpa only [b, ite_eq_right hω] using hg n
  refine ⟨fun n ω => (hbL n ω).toLp (b n ω),
    fun n => crudeEnergy_stronglyMeasurable_physical_toLp (b n) (hbm n) (hbL n), ?_⟩
  have hnotN : ∀ᵐ ω ∂reducedLaw Q, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNzero
  filter_upwards [hnotN] with ω hω
  intro n
  simpa only [b, ite_eq_right hω] using (hbL n ω).coeFn_toLp

/-- The Gaussian discrepancy between a spatial field and its expanding
Euclidean cutoffs vanishes. Only the true Gaussian L2 integrability is used. -/
theorem crudeEnergy_gaussian_spatial_cutoff_defect_tendsto
    {d : ℕ} {κ : ℝ} {f : Vec d → ℂ} (hf : Measurable f)
    (hi : Integrable (fun x => Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2) volume) :
    Tendsto (fun n : ℕ => ∫ x, Real.exp (-κ * euclideanSq x) *
      ‖f x - {y : Vec d | euclideanNorm (y - 0) ≤ (n : ℝ)}.indicator f x‖ ^ 2)
      atTop (𝓝 0) := by
  let K : ℕ → Set (Vec d) := fun n => {x | euclideanNorm (x - 0) ≤ (n : ℝ)}
  have hK (n : ℕ) : MeasurableSet (K n) :=
    (isCompact_physical_euclidean_closedBall 0 n).measurableSet
  have hw : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    unfold euclideanSq dot
    fun_prop
  have hh := tendsto_integral_of_dominated_convergence
    (fun x => Real.exp (-κ * euclideanSq x) * ‖f x‖ ^ 2)
    (F := fun n x => Real.exp (-κ * euclideanSq x) * ‖f x - (K n).indicator f x‖ ^ 2)
    (f := fun _ => (0 : ℝ))
    (fun n => (hw.mul ((hf.sub (hf.indicator (hK n))).norm.pow_const 2)).aestronglyMeasurable)
    hi (fun n => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
  · simpa only [integral_zero] using hh
  · by_cases hx : x ∈ K n
    · simp only [Set.indicator_of_mem hx, sub_self, norm_zero,
        zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero, norm_zero]
      positivity
    · simp only [Set.indicator_of_notMem hx, sub_zero, norm_mul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), abs_pow, abs_norm, le_refl]
  · obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - 0))
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop n] with m hm
    have hx : x ∈ K m := hn.le.trans (by exact_mod_cast hm)
    simp only [Set.indicator_of_mem hx, sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero]

/-- The actual physical semigroup applied to measurable Euclidean cutoffs
converges to the stationary forward orbit in every admissible Gaussian norm.
The cutoff data and their joint measurability are constructed internally. -/
theorem crudeEnergy_exists_forward_cutoff_gaussian_approximation
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∃ F : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, StronglyMeasurable (F n)) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n,
        (F n ω : Vec d → ℂ) =ᵐ[volume]
          {x : Vec d | euclideanNorm (x - 0) ≤ (n : ℝ)}.indicator
            (fun x => f (translate x ω))) ∧
      ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
        ∀ᵐ ω ∂reducedLaw Q,
          (∀ n, Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2) volume) ∧
          Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2)
            atTop (𝓝 0) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  intro S hS hSm
  obtain ⟨F, hFm, hF⟩ := crudeEnergy_exists_measurable_spatial_cutoffs Q f
  refine ⟨F, hFm, hF, ?_⟩
  intro c L hc hL
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hi := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hLp (by linarith : 0 < 1 + c))) f
  have hb (n : ℕ) := crudeEnergy_ae_forward_gaussian_comparison
    hP hfg S hS hSm (F n) (hFm n) c L hc hL
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) hLp) (P c.toNNReal f)
  filter_upwards [hF, hi, hi₁, ae_all_iff.mpr hb] with ω hFω hiω hi₁ω hbω
  refine ⟨?_, ?_⟩
  · intro n
    simp_rw [hη]
    exact crudeEnergy_integrable_weighted_sub_sq volume
      (by unfold euclideanSq dot; fun_prop) (fun _ => Real.exp_nonneg _)
      ((Lp.stronglyMeasurable (P c.toNNReal f)).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
      (Lp.stronglyMeasurable (S ω c.toNNReal (F n ω))).measurable hi₁ω
      (crudeEnergy_physical_gaussian_endpoint
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLp.le) _)
  · have hm : Measurable (fun x : Vec d => f (translate x ω)) :=
      (Lp.stronglyMeasurable f).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
    have ht := crudeEnergy_gaussian_spatial_cutoff_defect_tendsto hm hiω
    simp_rw [← hη] at ht
    have ht' : Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
        ‖f (translate x ω) - (F n ω) x‖ ^ 2) atTop (𝓝 0) := by
      apply ht.congr'
      exact Eventually.of_forall fun n => integral_congr_ae
        ((hFω n).mono fun x hx => by dsimp only; rw [hx])
    have hbound := (ht'.const_mul 27).mul_const (Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c))
    simp only [mul_zero, zero_mul] at hbound
    exact squeeze_zero (fun n => integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbω hbound

/-- A positive weighted square defect tending to zero identifies any almost
 everywhere pointwise limit. Fatou's lemma needs no integrability of the limit. -/
theorem crudeEnergy_ae_eq_of_weighted_sq_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    {w : Ω → ℝ} (hw : ∀ x, 0 < w x) {u v : Ω → ℂ} {V : ℕ → Ω → ℂ}
    (hi : ∀ n, Integrable (fun x => w x * ‖u x - V n x‖ ^ 2) ν)
    (ht : Tendsto (fun n => ∫ x, w x * ‖u x - V n x‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hp : ∀ᵐ x ∂ν, Tendsto (fun n => V n x) atTop (𝓝 (v x))) :
    u =ᵐ[ν] v := by
  let A : ℕ → Ω → ℝ := fun n x => w x * ‖u x - V n x‖ ^ 2
  let B : Ω → ℝ := fun x => w x * ‖u x - v x‖ ^ 2
  have hA (n : ℕ) : Integrable (A n) ν := hi n
  have hAnn (n : ℕ) : 0 ≤ᵐ[ν] A n :=
    ae_of_all _ fun x => mul_nonneg (hw x).le (sq_nonneg _)
  have hpt : ∀ᵐ x ∂ν, Tendsto (fun n => A n x) atTop (𝓝 (B x)) := by
    filter_upwards [hp] with x hx
    exact (((tendsto_const_nhds.sub hx).norm.pow 2).const_mul (w x))
  have hBm := aestronglyMeasurable_of_tendsto_ae atTop
    (fun n => (hA n).aestronglyMeasurable) hpt
  have he (n : ℕ) : (∫⁻ x, ENNReal.ofReal (A n x) ∂ν) =
      ENNReal.ofReal (∫ x, A n x ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal (hA n) (hAnn n)).symm
  have hl : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (A n x) ∂ν) atTop (𝓝 0) := by
    simp_rw [he]
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  have hFatou := lintegral_liminf_le' (u := atTop) (fun n => (hA n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
  have hlim : (fun x => liminf (fun n => ENNReal.ofReal (A n x)) atTop) =ᵐ[ν]
      (fun x => ENNReal.ofReal (B x)) :=
    hpt.mono fun x hx => (ENNReal.tendsto_ofReal hx).liminf_eq
  rw [lintegral_congr_ae hlim, hl.liminf_eq] at hFatou
  have hz := (lintegral_eq_zero_iff' hBm.aemeasurable.ennreal_ofReal).mp
    (le_antisymm hFatou bot_le)
  filter_upwards [hz] with x hx
  have hBx : B x = 0 := le_antisymm (ENNReal.ofReal_eq_zero.mp hx)
    (mul_nonneg (hw x).le (sq_nonneg _))
  have hs : ‖u x - v x‖ ^ 2 = 0 := (mul_eq_zero.mp hBx).resolve_left (hw x).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hs))

/-- Integrals of expanding Euclidean cutoffs recover any integrable physical
function, without any regularity assumption on its representative. -/
theorem crudeEnergy_euclidean_cutoff_integral_tendsto
    {d : ℕ} {f : Vec d → ℂ} (hf : Integrable f volume) :
    Tendsto (fun n : ℕ => ∫ x,
      {y : Vec d | euclideanNorm (y - 0) ≤ (n : ℝ)}.indicator f x)
      atTop (𝓝 (∫ x, f x)) := by
  let K : ℕ → Set (Vec d) := fun n => {x | euclideanNorm (x - 0) ≤ (n : ℝ)}
  have hK (n : ℕ) : MeasurableSet (K n) :=
    (isCompact_physical_euclidean_closedBall 0 n).measurableSet
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => (hf.indicator (hK n)).aestronglyMeasurable) hf.norm
  · intro n
    exact ae_of_all _ fun x => by
      by_cases hx : x ∈ K n
      · simp only [Set.indicator_of_mem hx, le_refl]
      · simp only [Set.indicator_of_notMem hx, norm_zero]
        exact norm_nonneg _
  · exact ae_of_all _ fun x => by
      obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm (x - 0))
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop n] with m hm
      have hx : x ∈ K m := hn.le.trans (by exact_mod_cast hm)
      exact (Set.indicator_of_mem hx f).symm

/-- A genuine physical kernel identifies the Gaussian limit of its cutoff
 evolutions with convolution of the full datum. The kernel may be transposed. -/
theorem crudeEnergy_physical_cutoff_kernel_identification
    {d : ℕ}
    {S Sdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    {K : ℝ≥0 → Vec d → Vec d → ℂ} (hK : IsPhysicalComplexKernel S Sdag K)
    {t : ℝ≥0} (ht : 0 < t) {f u : Vec d → ℂ}
    {F : ℕ → Lp ℂ 2 (volume : Measure (Vec d))}
    (hF : ∀ n, (F n : Vec d → ℂ) =ᵐ[volume]
      {x : Vec d | euclideanNorm (x - 0) ≤ (n : ℝ)}.indicator f)
    (hI : ∀ᵐ x ∂volume, Integrable (fun y => K t x y * f y) volume)
    (L : ℝ)
    (hi : ∀ n, Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
      ‖u x - (S t (F n)) x‖ ^ 2) volume)
    (hlim : Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
      ‖u x - (S t (F n)) x‖ ^ 2) atTop (𝓝 0)) :
    u =ᵐ[volume] fun x => ∫ y, K t x y * f y := by
  apply crudeEnergy_ae_eq_of_weighted_sq_tendsto volume
    (fun x => sq_pos_of_pos (Real.exp_pos _)) hi hlim
  have hk (n : ℕ) := (hK t ht (F n)).1.2
  filter_upwards [hI, ae_all_iff.mpr hk] with x hIx hkx
  apply (crudeEnergy_euclidean_cutoff_integral_tendsto hIx).congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [hkx n]
    apply integral_congr_ae
    filter_upwards [hF n] with y hy
    rw [hy]
    by_cases h : y ∈ {z : Vec d | euclideanNorm (z - 0) ≤ (n : ℝ)}
    · simp only [Set.indicator_of_mem h]
    · simp only [Set.indicator_of_notMem h, mul_zero]

/-- The point-kernel input gives an actual smooth representative of the
stationary forward orbit of bounded generator-domain data. Both its Euclidean
value and gradient have the original structural kernel bound. -/
theorem crudeEnergy_forward_generator_representative_of_pointKernel
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (f g : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexGeneratorPair Q i ζ f g →
    ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      ∃ u : Vec d → ℂ,
        (fun x => (P t f) (translate x ω)) =ᵐ[volume] u ∧
        Differentiable ℝ u ∧ ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, c, N, hC, _hc, hk⟩ := hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ f g B hB hf i ζ hζ P hP hfg t ht
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  obtain ⟨S, Sdag, hpair, _hm, hSm, _hSdagm⟩ :=
    crudeEnergy_ae_exists_measurable_physical_pair Q i ζ
  have hS := hpair.mono fun _ h => h.1
  obtain ⟨F, _hFm, hF, hconv⟩ :=
    crudeEnergy_exists_forward_cutoff_gaussian_approximation hP hfg S hS hSm
  let L : ℝ := 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3
  have happrox := hconv (t : ℝ) L (by linarith) (le_refl _)
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [hk Q hQ, horbit, hpair, hF, happrox] with ω hkω hfω hpairω hFω haω
  obtain ⟨K, hK, hreg⟩ := hkω i ζ hζ (S ω) (Sdag ω) hpairω.1 hpairω.2
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hb := (hreg K (by simp) t ht).2.2
    (fun y => f (translate y ω)) B hB hfm hfω
  refine ⟨fun x => ∫ y, K t x y * f (translate y ω), ?_, hb.1, ?_⟩
  · apply crudeEnergy_physical_cutoff_kernel_identification hK
      (show 0 < t by exact_mod_cast (show (0 : ℝ) < t by linarith)) hFω
      (ae_of_all _ fun x => (hb.2 x).1) L
    · simpa using haω.1
    · simpa using haω.2
  · exact fun x => (hb.2 x).2.2

/-- Stationary L2 convergence has an almost-sure Gaussian spatial subsequence.
The conclusion uses the actual representatives of the two L2 classes. -/
theorem crudeEnergy_stationary_gaussian_seq_trace_ae {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {u : ℕ → Lp ℂ 2 (reducedLaw Q)}
    {f : Lp ℂ 2 (reducedLaw Q)} (hu : Tendsto u atTop (𝓝 f))
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂reducedLaw Q,
      Tendsto (fun n => ∫ x : Vec d, Real.exp (-κ * euclideanSq x) *
        ‖(u (ns n)) (translate x ω) - f (translate x ω)‖ ^ 2) atTop (𝓝 0) := by
  let F : ℕ → FieldPair d → ℝ := fun n ω =>
    ∫ x : Vec d, Real.exp (-κ * euclideanSq x) * ‖(u n - f) (translate x ω)‖ ^ 2
  have hi (n : ℕ) := crudeEnergy_integrable_gaussian_orbit_sq Q κ hκ (u n - f)
  have hlim : Tendsto (fun n => ‖u n - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0)] using
      (hu.sub_const f).norm.pow 2
  have hmean (n : ℕ) : (∫ ω, F n ω ∂reducedLaw Q) =
      (∫ x : Vec d, Real.exp (-κ * euclideanSq x)) * ‖u n - f‖ ^ 2 := (hi n).2
  have hm : Tendsto (fun n => ∫ ω, F n ω ∂reducedLaw Q) atTop (𝓝 0) := by
    simpa only [hmean, mul_zero] using
      hlim.const_mul (∫ x : Vec d, Real.exp (-κ * euclideanSq x))
  have hn (n : ℕ) : eLpNorm (F n) 1 (reducedLaw Q) =
      ENNReal.ofReal (∫ ω, F n ω ∂reducedLaw Q) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hi n).1.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi n).1]
    congr 1
    apply integral_congr_ae
    filter_upwards with ω
    exact Real.norm_of_nonneg (integral_nonneg fun x =>
      mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))
  have he : Tendsto (fun n => eLpNorm (F n - 0) 1 (reducedLaw Q)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_zero, hn, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hm
  obtain ⟨ns, hns, ht⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) he).exists_seq_tendsto_ae
  have hrep (n : ℕ) := ae_spatial_complex_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (u (ns n) - f)).measurable
    ((Lp.stronglyMeasurable (u (ns n))).measurable.sub (Lp.stronglyMeasurable f).measurable)
    (Lp.coeFn_sub _ _)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [ht, ae_all_iff.mpr hrep] with ω htω hrω
  apply htω.congr'
  exact Eventually.of_forall fun n => integral_congr_ae
    ((hrω n).mono fun x hx => by dsimp only [F]; rw [hx]; rfl)

/-- Density of the genuine generator domain extends the forward Gaussian
comparison to every stationary L2 datum. No bounded approximation is needed. -/
theorem crudeEnergy_ae_forward_gaussian_comparison_allLp
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fR ω)) x‖ ^ 2) ≤
        243 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fR ω) x‖ ^ 2) *
          Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  intro S hS hSm fR hfR c L hc hL Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let κ₀ : ℝ := 2 / (L * (1 + c))
  let κ₁ : ℝ := 2 / L
  have hκ₀ : 0 < κ₀ := div_pos (by norm_num) (mul_pos hLp (by linarith))
  have hκ₁ : 0 < κ₁ := div_pos (by norm_num) hLp
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨fn, hfn, htfn⟩ := mem_closure_iff_seq_limit.mp
    ((dense_complexGenerator_domain Q i ζ) f)
  choose gn hgn using hfn
  obtain ⟨ns, hns, ht₀⟩ :=
    crudeEnergy_stationary_gaussian_seq_trace_ae Q htfn κ₀ hκ₀
  have htP : Tendsto (fun n => P c.toNNReal (fn (ns n))) atTop
      (𝓝 (P c.toNNReal f)) :=
    (P c.toNNReal).continuous.tendsto f |>.comp (htfn.comp hns.tendsto_atTop)
  obtain ⟨ms, hms, ht₁⟩ :=
    crudeEnergy_stationary_gaussian_seq_trace_ae Q htP κ₁ hκ₁
  let v : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n => fn (ns (ms n))
  have hb (n : ℕ) := crudeEnergy_ae_forward_gaussian_comparison
    hP (hgn (ns (ms n))) S hS hSm fR hfR c L hc hL
  simp_rw [hη] at hb
  have hi₀ := crudeEnergy_ae_gaussian_endpoint Q hκ₀ f
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q hκ₁ (P c.toNNReal f)
  have hi₀n (n : ℕ) := crudeEnergy_ae_gaussian_endpoint Q hκ₀ (v n)
  have hi₁n (n : ℕ) := crudeEnergy_ae_gaussian_endpoint Q hκ₁ (P c.toNNReal (v n))
  have hwm (κ : ℝ) : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    unfold euclideanSq dot
    fun_prop
  have hom (a : Lp ℂ 2 (reducedLaw Q)) (ω : FieldPair d) :
      Measurable (fun x : Vec d => a (translate x ω)) :=
    (Lp.stronglyMeasurable a).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  filter_upwards [ht₀, ht₁, hi₀, hi₁, ae_all_iff.mpr hi₀n, ae_all_iff.mpr hi₁n,
      ae_all_iff.mpr hb] with ω ht₀ω ht₁ω hi₀ω hi₁ω hi₀nω hi₁nω hbω
  let B : ℝ := ∫ x, Real.exp (-κ₀ * euclideanSq x) *
    ‖f (translate x ω) - (fR ω) x‖ ^ 2
  let E : ℝ := Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c)
  let E₀ : ℕ → ℝ := fun n => ∫ x, Real.exp (-κ₀ * euclideanSq x) *
    ‖(v n) (translate x ω) - f (translate x ω)‖ ^ 2
  let E₁ : ℕ → ℝ := fun n => ∫ x, Real.exp (-κ₁ * euclideanSq x) *
    ‖(P c.toNNReal f) (translate x ω) - (P c.toNNReal (v n)) (translate x ω)‖ ^ 2
  have hE₀ : Tendsto E₀ atTop (𝓝 0) := ht₀ω.comp hms.tendsto_atTop
  have hE₁ : Tendsto E₁ atTop (𝓝 0) := by
    apply ht₁ω.congr'
    exact Eventually.of_forall fun n => integral_congr_ae
      (ae_of_all _ fun x => by dsimp only [E₁, v]; rw [norm_sub_rev])
  have hlim : Tendsto (fun n => 3 * E₁ n + 243 * (E₀ n + B) * E)
      atTop (𝓝 (243 * B * E)) := by
    simpa only [mul_zero, zero_add] using
      (hE₁.const_mul 3).add (((hE₀.add_const B).const_mul 243).mul_const E)
  simp_rw [hη]
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hiD₀ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₀)
    (fun _ => Real.exp_nonneg _) (hom f ω) (Lp.stronglyMeasurable (fR ω)).measurable
    hi₀ω (crudeEnergy_physical_gaussian_endpoint hκ₀.le _)
  have hiD₁ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₁)
    (fun _ => Real.exp_nonneg _) (hom (P c.toNNReal (v n)) ω)
    (Lp.stronglyMeasurable (S ω c.toNNReal (fR ω))).measurable
    (hi₁nω n) (crudeEnergy_physical_gaussian_endpoint hκ₁.le _)
  have hiE₀ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₀)
    (fun _ => Real.exp_nonneg _) (hom (v n) ω) (hom f ω) (hi₀nω n) hi₀ω
  have hiE₁ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₁)
    (fun _ => Real.exp_nonneg _) (hom (P c.toNNReal f) ω)
    (hom (P c.toNNReal (v n)) ω) hi₁ω (hi₁nω n)
  have hinit := crudeEnergy_gaussian_initial_comparison (le_refl κ₀)
    (g := fun x => (fR ω) x) (g₀ := fun x => (fR ω) x)
    hiE₀ hiD₀ (by simp only [sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero]; exact integrable_zero _ _ _)
  have hlast := crudeEnergy_gaussian_initial_comparison (le_refl κ₁)
    (g := fun x => (S ω c.toNNReal (fR ω)) x)
    (g₀ := fun x => (S ω c.toNNReal (fR ω)) x)
    hiE₁ hiD₁ (by simp only [sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero]; exact integrable_zero _ _ _)
  simp only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero,
    integral_zero, add_zero] at hinit hlast
  have hmiddle := (hbω n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 27)) (Real.exp_nonneg _))
  apply hlast.trans
  calc
    _ ≤ 3 * (E₁ n + (27 * (3 * (E₀ n + B)) * E)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hmiddle) (by norm_num)
    _ = _ := by ring

/-- Actual physical cutoffs converge in Gaussian L2 to the stationary forward
orbit for arbitrary stationary L2 data, using the dense-domain comparison. -/
theorem crudeEnergy_exists_forward_cutoff_gaussian_approximation_allLp
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexSemigroup ω.1 i ζ (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∃ F : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, StronglyMeasurable (F n)) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n,
        (F n ω : Vec d → ℂ) =ᵐ[volume]
          {x : Vec d | euclideanNorm (x - 0) ≤ (n : ℝ)}.indicator
            (fun x => f (translate x ω))) ∧
      ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
        ∀ᵐ ω ∂reducedLaw Q,
          (∀ n, Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2) volume) ∧
          Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2)
            atTop (𝓝 0) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  intro S hS hSm
  obtain ⟨F, hFm, hF⟩ := crudeEnergy_exists_measurable_spatial_cutoffs Q f
  refine ⟨F, hFm, hF, ?_⟩
  intro c L hc hL
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hi := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hLp (by linarith : 0 < 1 + c))) f
  have hb (n : ℕ) := crudeEnergy_ae_forward_gaussian_comparison_allLp
    hP f S hS hSm (F n) (hFm n) c L hc hL
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) hLp) (P c.toNNReal f)
  filter_upwards [hF, hi, hi₁, ae_all_iff.mpr hb] with ω hFω hiω hi₁ω hbω
  refine ⟨?_, ?_⟩
  · intro n
    simp_rw [hη]
    exact crudeEnergy_integrable_weighted_sub_sq volume
      (by unfold euclideanSq dot; fun_prop) (fun _ => Real.exp_nonneg _)
      ((Lp.stronglyMeasurable (P c.toNNReal f)).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
      (Lp.stronglyMeasurable (S ω c.toNNReal (F n ω))).measurable hi₁ω
      (crudeEnergy_physical_gaussian_endpoint
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLp.le) _)
  · have hm : Measurable (fun x : Vec d => f (translate x ω)) :=
      (Lp.stronglyMeasurable f).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
    have ht := crudeEnergy_gaussian_spatial_cutoff_defect_tendsto hm hiω
    simp_rw [← hη] at ht
    have ht' : Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
        ‖f (translate x ω) - (F n ω) x‖ ^ 2) atTop (𝓝 0) := by
      apply ht.congr'
      exact Eventually.of_forall fun n => integral_congr_ae
        ((hFω n).mono fun x hx => by dsimp only; rw [hx])
    have hbound := (ht'.const_mul 243).mul_const (Real.exp (16 * Λ ^ 3 * ‖ζ‖ ^ 2 * c))
    simp only [mul_zero, zero_mul] at hbound
    exact squeeze_zero (fun n => integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbω hbound

/-- Every bounded stationary L2 datum has an actual smooth forward orbit
representative, with the original structural point-kernel value and gradient
bound. Neither generator-domain membership nor an identification is assumed. -/
theorem crudeEnergy_forward_representative_of_pointKernel
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      ∃ u : Vec d → ℂ,
        (fun x => (P t f) (translate x ω)) =ᵐ[volume] u ∧
        Differentiable ℝ u ∧ ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, c, N, hC, _hc, hk⟩ := hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ f B hB hf i ζ hζ P hP t ht
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  obtain ⟨S, Sdag, hpair, _hm, hSm, _hSdagm⟩ :=
    crudeEnergy_ae_exists_measurable_physical_pair Q i ζ
  have hS := hpair.mono fun _ h => h.1
  obtain ⟨F, _hFm, hF, hconv⟩ :=
    crudeEnergy_exists_forward_cutoff_gaussian_approximation_allLp hP f S hS hSm
  let L : ℝ := 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3
  have happrox := hconv (t : ℝ) L (by linarith) (le_refl _)
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [hk Q hQ, horbit, hpair, hF, happrox] with ω hkω hfω hpairω hFω haω
  obtain ⟨K, hK, hreg⟩ := hkω i ζ hζ (S ω) (Sdag ω) hpairω.1 hpairω.2
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hb := (hreg K (by simp) t ht).2.2
    (fun y => f (translate y ω)) B hB hfm hfω
  refine ⟨fun x => ∫ y, K t x y * f (translate y ω), ?_, hb.1, ?_⟩
  · apply crudeEnergy_physical_cutoff_kernel_identification hK
      (show 0 < t by exact_mod_cast (show (0 : ℝ) < t by linarith)) hFω
      (ae_of_all _ fun x => (hb.2 x).1) L
    · simpa using haω.1
    · simpa using haω.2
  · exact fun x => (hb.2 x).2.2

/-- A measurable stationary field bounded on almost every spatial orbit has
that same almost-sure bound at the environment origin. -/
theorem crudeEnergy_ae_le_of_ae_spatial_le {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {u : FieldPair d → ℝ} (hu : Measurable u) {B : ℝ}
    (hb : ∀ᵐ ω ∂Q, ∀ᵐ x : Vec d ∂volume, u (translate x ω) ≤ B) :
    ∀ᵐ ω ∂Q, u ω ≤ B := by
  have hc := (Measure.ae_ae_comm (μ := volume) (ν := Q)
    (p := fun x ω => u (translate x ω) ≤ B)
    (measurableSet_le (hu.comp Probability.continuous_translate.measurable)
      measurable_const)).mpr hb
  obtain ⟨x, hx⟩ := hc.exists
  have hr := (measurePreserving_translate Q hQ (-x)).quasiMeasurePreserving.ae hx
  simpa only [translate_add, add_neg_cancel, translate_zero] using hr

/-- Smooth spatial representatives transfer both their value bound and every
fixed coordinate increment bound to the actual stationary L2 representative. -/
theorem crudeEnergy_ae_value_increment_of_spatial_representatives {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) {B : ℝ} (hB : 0 ≤ B)
    (hr : ∀ᵐ ω ∂Q, ∃ u : Vec d → ℂ,
      (fun x => f (translate x ω)) =ᵐ[volume] u ∧ Differentiable ℝ u ∧
      ∀ x, ‖u x‖ + Real.sqrt
        (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B) :
    (∀ᵐ ω ∂Q, ‖f ω‖ ≤ B) ∧
      ∀ (j : Fin d) (s : ℝ),
        ∀ᵐ ω ∂Q, ‖f (translate (s • unitVector j) ω) - f ω‖ ≤ B * |s| := by
  constructor
  · apply crudeEnergy_ae_le_of_ae_spatial_le Q hQ (Lp.stronglyMeasurable f).measurable.norm
    filter_upwards [hr] with ω hω
    obtain ⟨u, he, _hu, hb⟩ := hω
    filter_upwards [he] with x hx
    rw [hx]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans (hb x)
  · intro j s
    have hm : Measurable (fun ω => ‖f (translate (s • unitVector j) ω) - f ω‖) :=
      (((Lp.stronglyMeasurable f).measurable.comp
        (Probability.measurable_translate _)).sub (Lp.stronglyMeasurable f).measurable).norm
    apply crudeEnergy_ae_le_of_ae_spatial_le Q hQ hm
    filter_upwards [hr] with ω hω
    obtain ⟨u, he, hu, hb⟩ := hω
    have hs := (measurePreserving_add_right (volume : Measure (Vec d))
      (s • unitVector j)).quasiMeasurePreserving.ae he
    filter_upwards [he, hs] with x hx hxs
    rw [translate_add, add_comm (s • unitVector j) x, hxs, hx]
    simpa only [zero_smul, add_zero, sub_zero, Real.norm_eq_abs] using!
      (crudeEnergy_coordinate_lipschitz hu hB hb x j).norm_sub_le s 0

/-- A uniform bound on actual coordinate increments bounds every existing
strong horizontal derivative, by an almost-everywhere subsequence of L2 quotients. -/
theorem crudeEnergy_ae_derivative_bound_of_increments {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (j : Fin d) (f g : Lp ℂ 2 Q) {B : ℝ}
    (hg : HasComplexHorizontalDerivative Q hQ j f g)
    (hb : ∀ s : ℝ, ∀ᵐ ω ∂Q,
      ‖f (translate (s • unitVector j) ω) - f ω‖ ≤ B * |s|) :
    ∀ᵐ ω ∂Q, ‖g ω‖ ≤ B := by
  let s : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hs0 (n : ℕ) : s n ≠ 0 := by dsimp only [s]; positivity
  have hs : Tendsto s atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall hs0⟩
  let v : ℕ → Lp ℂ 2 Q := fun n => ((s n : ℂ)⁻¹) •
    (complexTranslation Q hQ (s n • unitVector j) f - f)
  have hv : Tendsto v atTop (𝓝 g) := hg.comp hs
  obtain ⟨ns, _hns, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hv).exists_seq_tendsto_ae
  have hvb (n : ℕ) : ∀ᵐ ω ∂Q, ‖v n ω‖ ≤ B := by
    filter_upwards [Lp.coeFn_smul ((s n : ℂ)⁻¹)
        (complexTranslation Q hQ (s n • unitVector j) f - f),
      Lp.coeFn_sub (complexTranslation Q hQ (s n • unitVector j) f) f,
      coeFn_complexTranslation Q hQ (s n • unitVector j) f, hb (s n)]
      with ω hsm hsub ht hω
    change ‖(((s n : ℂ)⁻¹) •
      (complexTranslation Q hQ (s n • unitVector j) f - f)) ω‖ ≤ B
    rw [hsm, Pi.smul_apply, hsub, Pi.sub_apply, ht, norm_smul,
      norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ |s n|⁻¹ * (B * |s n|) :=
        mul_le_mul_of_nonneg_left hω (inv_nonneg.mpr (abs_nonneg _))
      _ = B := by rw [mul_left_comm, inv_mul_cancel₀ (abs_ne_zero.mpr (hs0 n)), mul_one]
  filter_upwards [ha, ae_all_iff.mpr fun n => hvb (ns n)] with ω hω hbω
  exact le_of_tendsto hω.norm (Eventually.of_forall hbω)

/-- The spatial smooth bound controls the actual Euclidean horizontal gradient.
The only loss is the displayed structural dimension factor. -/
theorem crudeEnergy_ae_gradient_bound_of_spatial_representatives {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) (G : Fin d → Lp ℂ 2 Q) {B : ℝ} (hB : 0 ≤ B)
    (hG : HasComplexHorizontalGradient Q hQ f G)
    (hr : ∀ᵐ ω ∂Q, ∃ u : Vec d → ℂ,
      (fun x => f (translate x ω)) =ᵐ[volume] u ∧ Differentiable ℝ u ∧
      ∀ x, ‖u x‖ + Real.sqrt
        (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B) :
    ∀ᵐ ω ∂Q, ‖f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤
      (1 + Real.sqrt (d : ℝ)) * B := by
  obtain ⟨hf, hi⟩ :=
    crudeEnergy_ae_value_increment_of_spatial_representatives Q hQ f hB hr
  have hg : ∀ᵐ ω ∂Q, ∀ j : Fin d, ‖G j ω‖ ≤ B :=
    (ae_all_iff.mpr fun j =>
      crudeEnergy_ae_derivative_bound_of_increments Q hQ j f (G j) (hG j) (hi j))
  filter_upwards [hf, hg] with ω hfω hgω
  have hsum : (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ (d : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, B ^ 2 := Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hgω j) 2
      _ = (d : ℝ) * B ^ 2 := by simp
  have hgrad : Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤ Real.sqrt (d : ℝ) * B := by
    calc
      _ ≤ Real.sqrt ((d : ℝ) * B ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (d : ℝ) * B := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hB]
  calc
    _ ≤ B + Real.sqrt (d : ℝ) * B := add_le_add hfω hgrad
    _ = (1 + Real.sqrt (d : ℝ)) * B := by ring

/-- The forward point-kernel input gives the actual stationary Euclidean
and local-energy estimates for every bounded L2 datum and its actual gradient. -/
theorem crudeEnergy_forward_bounds_of_pointKernel
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
    ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G →
      (∀ᵐ ω ∂reducedLaw Q, ‖P t f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) ∧
      (∀ (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
        ‖P t f ω‖ + localSpatialEnergy Q t ρ hρ x G 0 ω ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) := by
  obtain ⟨C, N, hC, hr⟩ := crudeEnergy_forward_representative_of_pointKernel hkernel d hd D
  let K : ℝ := 2 * (1 + Real.sqrt (d : ℝ))
  have hK : 1 ≤ K := by dsimp only [K]; nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hKC : 1 ≤ K * C := one_le_mul_of_one_le_of_one_le hK hC
  refine ⟨K * C, N, hKC, ?_⟩
  intro Q hQ f B hB hf i ζ hζ P hP t ht G hG
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let A : ℝ := C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp := crudeEnergy_ae_gradient_bound_of_spatial_representatives
    (reducedLaw Q) (reducedLaw_stationary Q) (P t f) G (mul_nonneg hA hB) hG
    (hr Q hQ f B hB hf i ζ hζ P hP t ht)
  have hb : 0 ≤ (1 + Real.sqrt (d : ℝ)) * (A * B) := by positivity
  have hdom : 2 * ((1 + Real.sqrt (d : ℝ)) * (A * B)) ≤
      (K * C) * (2 + (t : ℝ)) ^ N *
        Real.exp ((K * C) * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
    have he : Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
        Real.exp ((K * C) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        C = 1 * C := (one_mul C).symm
        _ ≤ K * C := mul_le_mul_of_nonneg_right hK (by linarith)
    calc
      _ = ((K * C) * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) * B := by dsimp only [A, K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by positivity)) hB
  constructor
  · filter_upwards [hp] with ω hω
    exact hω.trans ((by linarith : (1 + Real.sqrt (d : ℝ)) * (A * B) ≤
      2 * ((1 + Real.sqrt (d : ℝ)) * (A * B))).trans hdom)
  · intro ρ hρ x
    exact (norm_add_localSpatialEnergy_le_of_ae_bound Q (P t f) G hb hp t ρ hρ x).mono
      fun _ h => h.trans hdom

private theorem crudeEnergy_transpose_compact_physical_test
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

private theorem crudeEnergy_physical_transpose_generator_divergence
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
    obtain ⟨v, J, hv, hvr, hJr⟩ := crudeEnergy_transpose_compact_physical_test φ hφ hφc
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
  exact crudeEnergy_divergence_projection (fun K _ j => (hF j).restrict K)
    (fun K _ => ((Lp.memLp g).const_mul (2 : ℂ)).restrict K) hweak L

/-- The stationary transpose graph has its conservative spatial divergence.
The gradient supplied by the caller is retained in the flux. -/
theorem crudeEnergy_ae_transpose_generator_spatial_divergence
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ A : ℂ →L[ℝ] ℝ, HasWeakDivergence univ
      (fun x j => A ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω) -
        ζ * (ω.1 x j i : ℂ) * f (translate x ω)))
      (fun x => A (g (translate x ω))) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F : Fin d → FieldPair d → ℂ := fun j ω =>
    (1 / 2 : ℂ) * ∑ k, (ω.1 0 j k : ℂ) * G k ω - ζ * (ω.1 0 j i : ℂ) * f ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) :=
    (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
      (hm j k).mul (Lp.stronglyMeasurable _).measurable)).sub
      ((measurable_const.mul (hm j i)).mul (Lp.stronglyMeasurable f).measurable)
  have hF (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    have hb := (Lp.memLp (complexCoefficientMul Q j i f)).ae_eq
      (complexCoefficientMul_coe Q j i f)
    simpa only [F, mul_assoc] using!
      ((memLp_complex_coefficient_flux Q G j).const_mul (1 / 2 : ℂ)).sub (hb.const_mul ζ)
  have hw := hfg.spatial_flux_all_tests hG
  filter_upwards [hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable g).measurable (Lp.memLp g),
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j))]
    with ω hw hgω hFω
  have hweak : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, g (translate x ω) * (φ x : ℂ)) =
        -(∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
    intro φ hφ hφc
    have he := hw φ hφ hφc
    have hflux : (fun x => ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) =
        (fun x => (1 / 2 : ℂ) * ∑ j,
          ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
            2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
              (coordinateDerivative j φ x : ℂ)) := by
      funext x
      simp only [F, translate_matrix, add_zero]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hflux, integral_const_mul]
    convert he using 1 <;> ring
  intro A
  have he := crudeEnergy_divergence_projection (fun K hK j => hFω j K hK) hgω hweak A
  simpa only [F, translate_matrix, add_zero] using! he

/-- The mixed transpose Gaussian estimate keeps the conservative force as
an explicit square-integrable flux source. -/
theorem crudeEnergy_ae_mixed_transpose_generator_gaussian_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (fun x => ω.1 x) i ζ u v →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
          let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
          let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
          let w : Vec d → ℂ := fun x => f (translate x ω) - u x
          let Z : Fin d → Vec d → ℂ := fun j x => G j (translate x ω) - H j x
          Integrable (fun x => η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ∧
            Integrable (fun x => W x * ‖w x‖ ^ 2) ∧
            (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ≤
              -2 * (∫ x, (g (translate x ω) - v x) *
                (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re +
                (4 * Λ + 16 / L) *
                  (∫ x, η x ^ 2 * ∑ j, ‖ζ * (ω.1 x j i : ℂ) * w x‖ ^ 2) -
                    ∫ x, W x * ‖w x‖ ^ 2 := by
  intro Λ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hΛ : 1 ≤ Λ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ := mul_le_mul
        (Real.one_le_exp (by positivity)) Q.ellipticity_parameter (by positivity) (by positivity)
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  filter_upwards [hG.ae_reduced_spatial Q,
    crudeEnergy_ae_transpose_generator_spatial_divergence hfg hG,
    c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_stationary_spatial_orbit_gaussian_memLp d Fact.out
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))]
    with ω hω hdiv ha hfL hgL hGL
  have ham (j k : Fin d) : MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry _ _ Λ hΛp ha (fun j k => ω.1.continuous.matrix_elem j k) j k
  intro u v huv
  have hgraph := huv
  obtain ⟨H, hH, _⟩ := hgraph
  have hdivH := crudeEnergy_physical_transpose_generator_divergence
    (fun x => ω.1 x) i ζ ham u v H hH huv
  have hs (x : Vec d) (j k : Fin d) : ω.1 x k j = ω.1 x j k :=
    congrArg (fun M : Mat d => M j k) (ha x).1
  have hhalf (A : ℂ →L[ℝ] ℝ) : HasWeakDivergence univ
      (fun x j => A ((1 / 2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * H k x -
        ζ * (ω.1 x j i : ℂ) * u x)) (fun x => A (v x)) := by
    have he := hdivH ((1 / 2 : ℝ) • A)
    convert he using 1
    · funext x j
      change A _ = (1 / 2 : ℝ) • A _
      rw [← map_smul]
      congr 1
      simp only [hs, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
      norm_num <;> ring
    · funext x
      change A _ = (1 / 2 : ℝ) • A _
      rw [← map_smul]
      congr 1
      simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one]
      norm_num <;> ring
  refine ⟨H, hH, ?_⟩
  have hsub (A : ℂ →L[ℝ] ℝ) : HasWeakDivergence univ
      (fun x j => A ((1 / 2 : ℂ) * ∑ k,
        (ω.1 x j k : ℂ) * (G k (translate x ω) - H k x) -
          ζ * (ω.1 x j i : ℂ) * (f (translate x ω) - u x)))
      (fun x => A (g (translate x ω) - v x)) := by
    have he := Correctors.hasWeakDivergence_sub (hdiv A) (hhalf A)
    convert he using 1
    · funext x j
      simp only [Pi.sub_apply, ← map_sub, mul_sub, Finset.sum_sub_distrib]
      congr 1
      ring
    · funext x
      simp only [← map_sub]
  intro L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have he := physical_locally_h1_forced_gaussian_energy (fun x => ω.1 x) i 0 ham
    (ae_of_all _ fun x => s5Elliptic_of_isElliptic hΛ ha x)
    (fun x => f (translate x ω) - u x) (fun x => g (translate x ω) - v x)
    (fun j x => G j (translate x ω) - H j x)
    (fun j x => ζ * (ω.1 x j i : ℂ) * (f (translate x ω) - u x))
    (fun j => by simpa only [Complex.sub_re] using
      Correctors.hasWeakPartialDerivative_sub (hω.1 j) (hH.1 j))
    (fun j => by simpa only [Complex.sub_im] using
      Correctors.hasWeakPartialDerivative_sub (hω.2.1 j) (hH.2 j))
    (by simpa only [zero_mul, sub_zero] using! hsub Complex.reCLM)
    (by simpa only [zero_mul, sub_zero] using! hsub Complex.imCLM)
    hΛp hL hr
    (by
      have ht := (hfL (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp u (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (by
      have ht := (hgL (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp v (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (fun j => by
      have ht := (hGL j (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp (H j) (s := 4 * L * r) (by positivity))
      convert ht using 1 <;> funext x <;> simp only [Pi.sub_apply, mul_sub])
    (fun j => by
      have ht := (hfL (4 * L * r) (by positivity)).sub
        (crudeEnergy_physical_gaussian_memLp u (s := 4 * L * r) (by positivity))
      have hm : MemLp (fun x => ζ * ((ω.1 x j i : ℂ) *
          ((Real.exp (-euclideanSq x / (4 * L * r)) : ℂ) * f (translate x ω) -
            (Real.exp (-euclideanSq x / (4 * L * r)) : ℂ) * u x))) 2 volume :=
        ((ham j i).fun_mul ht).const_mul ζ
      convert hm using 1
      funext x
      simp only [mul_sub]
      ring)
  have he' := he.2.2
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul, add_zero] at he'
  exact ⟨he.1, he.2.1, by linarith⟩

/-- The conservative transpose force source is controlled by the same weighted
mass, with a coefficient depending only on dimension and ellipticity. -/
theorem crudeEnergy_transpose_weighted_source_bound {d : ℕ}
    (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ) {Λ L : ℝ}
    (hΛ : 1 ≤ Λ) (ha : ∀ x, S5Elliptic (a x) Λ) (hL : 64 * Λ ^ 3 ≤ L)
    (η : Vec d → ℝ) (w : Vec d → ℂ)
    (hw : Integrable (fun x => η x ^ 2 * ‖w x‖ ^ 2) volume) :
    (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j, ‖ζ * (a x j i : ℂ) * w x‖ ^ 2) ≤
      20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖w x‖ ^ 2) := by
  have hΛp : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hL1 : 1 ≤ L := by
    have hp : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ
    linarith
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hc : 0 ≤ 4 * Λ + 16 / L := by positivity
  have hcb : 4 * Λ + 16 / L ≤ 20 * Λ := by
    have hd : (16 : ℝ) / L ≤ 16 := div_le_self (by norm_num) hL1
    linarith
  have hpoint (x : Vec d) :
      η x ^ 2 * ∑ j, ‖ζ * (a x j i : ℂ) * w x‖ ^ 2 ≤
        ((d : ℝ) * Λ ^ 2 * ‖ζ‖ ^ 2) * (η x ^ 2 * ‖w x‖ ^ 2) := by
    have he (j : Fin d) : ‖ζ * (a x j i : ℂ) * w x‖ ^ 2 ≤
        Λ ^ 2 * ‖ζ‖ ^ 2 * ‖w x‖ ^ 2 := by
      have hb : ‖(a x j i : ℂ)‖ ≤ Λ := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using (ha x).entry_abs_le j i
      rw [norm_mul, norm_mul, mul_pow, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hb 2) (mul_nonneg (sq_nonneg ‖ζ‖) (sq_nonneg ‖w x‖))]
    have he' := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => he j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at he'
    have ht := mul_le_mul_of_nonneg_left he' (sq_nonneg (η x))
    nlinarith only [ht]
  have hb := integral_mono_of_nonneg
    (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
    (hw.const_mul ((d : ℝ) * Λ ^ 2 * ‖ζ‖ ^ 2)) (ae_of_all _ hpoint)
  rw [integral_const_mul] at hb
  have hm : 0 ≤ ∫ x, η x ^ 2 * ‖w x‖ ^ 2 :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ ≤ (4 * Λ + 16 / L) *
        (((d : ℝ) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∫ x, η x ^ 2 * ‖w x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hb hc
    _ ≤ (20 * Λ) *
        (((d : ℝ) * Λ ^ 2 * ‖ζ‖ ^ 2) * (∫ x, η x ^ 2 * ‖w x‖ ^ 2)) :=
      mul_le_mul_of_nonneg_right hcb (by positivity)
    _ = _ := by ring

/-- Absorbing the conservative force source closes the mixed transpose
Gaussian energy inequality with a structural exponential growth coefficient. -/
theorem crudeEnergy_ae_mixed_transpose_generator_gaussian_energy_absorbed
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (fun x => ω.1 x) i ζ u v →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) u H ∧
        ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
          let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
          let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
          let w : Vec d → ℂ := fun x => f (translate x ω) - u x
          let Z : Fin d → Vec d → ℂ := fun j x => G j (translate x ω) - H j x
          Integrable (fun x => η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ∧
            Integrable (fun x => W x * ‖w x‖ ^ 2) ∧
            (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖Z j x‖ ^ 2) ≤
              -2 * (∫ x, (g (translate x ω) - v x) *
                (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re +
                20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖w x‖ ^ 2) -
                    ∫ x, W x * ‖w x‖ ^ 2 := by
  intro Λ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ₀ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hΛ : 1 ≤ Λ := by
    calc
      1 = 1 * 1 := by norm_num
      _ ≤ Real.exp (2 * Λ₀) * Λ₀ := mul_le_mul
        (Real.one_le_exp (by positivity)) Q.ellipticity_parameter (by positivity) (by positivity)
  filter_upwards [crudeEnergy_ae_mixed_transpose_generator_gaussian_energy hfg hG,
    c4_ae_reduced_physical_elliptic Q,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out
      (reducedLaw Q) (reducedLaw_stationary Q) f] with ω he ha hfL
  intro u v huv
  obtain ⟨H, hH, hE⟩ := he u v huv
  refine ⟨H, hH, ?_⟩
  intro L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
  let w : Vec d → ℂ := fun x => f (translate x ω) - u x
  have hm : MemLp (fun x => (η x : ℂ) * w x) 2 volume := by
    have ht := (hfL (L * r) (by positivity)).sub
      (crudeEnergy_physical_gaussian_memLp u (s := L * r) (by positivity))
    convert ht using 1
    funext x
    simp only [Pi.sub_apply, η, w, mul_sub]
  have hi : Integrable (fun x => η x ^ 2 * ‖w x‖ ^ 2) := by
    convert hm.norm.integrable_sq using 1
    funext x
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hb := crudeEnergy_transpose_weighted_source_bound (fun x => ω.1 x) i ζ hΛ
    (fun x => s5Elliptic_of_isElliptic hΛ ha x) hL η w hi
  obtain ⟨h1, h2, h3⟩ := hE L r hL hr
  exact ⟨h1, h2, by dsimp only [η, w] at hb; linarith⟩

/-- Scalar Gaussian mass inequality for the actual stationary/physical
transpose generator difference, ready for time integration. -/
theorem crudeEnergy_ae_mixed_transpose_generator_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ u v : Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexTransposeGeneratorPair (fun x => ω.1 x) i ζ u v →
      ∀ L r : ℝ, 64 * Λ ^ 3 ≤ L → 0 < r →
        let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
        let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
        let w : Vec d → ℂ := fun x => f (translate x ω) - u x
        let z : Vec d → ℂ := fun x => g (translate x ω) - v x
        (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) +
            (∫ x, W x * ‖w x‖ ^ 2) ≤
          20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η x ^ 2 * ‖w x‖ ^ 2) := by
  intro Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  filter_upwards [crudeEnergy_ae_mixed_transpose_generator_gaussian_energy_absorbed hfg hG,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q)
      (reducedLaw_stationary Q) g] with ω he hf hg
  intro u v huv L r hL hr
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨H, _, he⟩ := he u v huv
  have henergy := (he L r hL hr).2.2
  dsimp only at henergy ⊢
  let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
  let w : Vec d → ℂ := fun x => f (translate x ω) - u x
  let z : Vec d → ℂ := fun x => g (translate x ω) - v x
  have hw : MemLp (fun x => (η x : ℂ) * w x) 2 volume := by
    have hh := (hf (L * r) (by positivity)).sub
      (crudeEnergy_physical_gaussian_memLp u (s := L * r) (by positivity))
    convert hh using 1
    funext x
    simp only [Pi.sub_apply, η, w, mul_sub]
  have hz : MemLp (fun x => (η x : ℂ) * z x) 2 volume := by
    have hh := (hg (L * r) (by positivity)).sub
      (crudeEnergy_physical_gaussian_memLp v (s := L * r) (by positivity))
    convert hh using 1
    funext x
    simp only [Pi.sub_apply, η, z, mul_sub]
  have hZ : Integrable (fun x => z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))) := by
    convert hz.integrable_mul hw.star using 1
    funext x
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def,
      Complex.conj_ofReal, Complex.ofReal_pow]
    ring
  have hcross : (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) =
      2 * (∫ x, z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re := by
    have hre : (∫ x, (z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re) =
        (∫ x, z x * (((η x ^ 2 : ℝ) : ℂ) * star (w x))).re := by
      simpa using! integral_re hZ
    rw [← hre, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      dsimp only
      rw [mul_comm (z x), mul_assoc, Complex.re_ofReal_mul]
      ring
  have hn : 0 ≤ (Λ⁻¹ / 4) * (∫ x, η x ^ 2 *
      ∑ j, ‖G j (translate x ω) - H j x‖ ^ 2) :=
    mul_nonneg (by positivity) (integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))
  change (∫ x, η x ^ 2 * (2 * (star (w x) * z x).re)) + _ ≤ _
  rw [hcross]
  linarith only [henergy, hn]

/-- Joint transpose mass estimate for measurable stationary/physical representatives. -/
theorem crudeEnergy_ae_joint_mixed_transpose_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c L : ℝ} (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    let W : ℝ → Vec d → ℝ := fun s x =>
      -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
    let Z : (ℝ × FieldPair d) × Vec d → ℂ := fun t =>
      U (t.1.1, translate t.2 t.1.2) - F t
    let Y : (ℝ × FieldPair d) × Vec d → ℂ := fun t =>
      V (t.1.1, translate t.2 t.1.2) - H t
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (∫ x, η s x ^ 2 * (2 * (star (Z ((s, ω), x)) * Y ((s, ω), x)).re)) +
        (∫ x, W s x * ‖Z ((s, ω), x)‖ ^ 2) ≤
        20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η s x ^ 2 * ‖Z ((s, ω), x)‖ ^ 2) := by
  intro Λ η W Z Y
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hshift {T : ℝ × FieldPair d → ℂ} (hT : Measurable T) :
      Measurable (fun t : (ℝ × FieldPair d) × Vec d =>
        T (t.1.1, translate t.2 t.1.2)) :=
    hT.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hZ : Measurable Z := (hshift hU).sub hF
  have hY : Measurable Y := (hshift hV).sub hH
  have hη : Measurable (fun t : (ℝ × FieldPair d) × Vec d => η t.1.1 t.2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hW : Measurable (fun t : (ℝ × FieldPair d) × Vec d => W t.1.1 t.2) := by
    dsimp only [W, η, euclideanSq, dot]
    fun_prop
  let A : ℝ × FieldPair d → ℝ := fun t =>
    (∫ x, η t.1 x ^ 2 * (2 * (star (Z (t, x)) * Y (t, x)).re)) +
      ∫ x, W t.1 x * ‖Z (t, x)‖ ^ 2
  let B : ℝ × FieldPair d → ℝ := fun t =>
    20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ x, η t.1 x ^ 2 * ‖Z (t, x)‖ ^ 2
  have hA : Measurable A := by
    apply Measurable.add
    · exact ((hη.pow_const 2).mul ((Complex.continuous_re.measurable.comp
        ((continuous_star.measurable.comp hZ).mul hY)).const_mul 2)).stronglyMeasurable.integral_prod_right'.measurable
    · exact (hW.mul (hZ.norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hB : Measurable B := measurable_const.mul
    ((hη.pow_const 2).mul (hZ.norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have heU' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hU.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heU s)
  have heV' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  filter_upwards [crudeEnergy_ae_mixed_transpose_generator_gaussian_mass (hgen s hs) (hgrad s hs),
    hphys s hs, heU', heV'] with ω hm hp heu hev
  have hr : 0 < 2 - s := sub_pos.mpr (hs.2.trans_lt hc)
  have hm := hm (p s ω) (q s ω) hp L (2 - s) hL hr
  have hZeq : (fun x => Z ((s, ω), x)) =ᵐ[volume]
      (fun x => (u s) (translate x ω) - (p s ω) x) := by
    filter_upwards [heu, heF s ω] with x hx hy
    change U (s, translate x ω) = _ at hx
    dsimp only [Z]
    rw [hx, hy]
  have hYeq : (fun x => Y ((s, ω), x)) =ᵐ[volume]
      (fun x => (v s) (translate x ω) - (q s ω) x) := by
    filter_upwards [hev, heH s ω] with x hx hy
    change V (s, translate x ω) = _ at hx
    dsimp only [Y]
    rw [hx, hy]
  have hcross : (∫ x, η s x ^ 2 * (2 * (star (Z ((s, ω), x)) * Y ((s, ω), x)).re)) =
      ∫ x, η s x ^ 2 * (2 * (star ((u s) (translate x ω) - (p s ω) x) *
        ((v s) (translate x ω) - (q s ω) x)).re) := by
    apply integral_congr_ae
    filter_upwards [hZeq, hYeq] with x hx hy
    rw [hx, hy]
  have hsq (ψ : Vec d → ℝ) : (∫ x, ψ x * ‖Z ((s, ω), x)‖ ^ 2) =
      ∫ x, ψ x * ‖(u s) (translate x ω) - (p s ω) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hZeq] with x hx
    rw [hx]
  dsimp only [A, B]
  rw [hcross, hsq, hsq]
  exact hm


/-- Integrate the mixed transpose mass inequality on the actual C1 paths. -/
theorem crudeEnergy_ae_integrated_mixed_transpose_gaussian_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        (∫ x, η b x ^ 2 * ‖(u b) (translate x ω) - (p b ω) x‖ ^ 2) +
          20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ s in Icc b c, ∫ x, η s x ^ 2 *
            ‖U (s, translate x ω) - F ((s, ω), x)‖ ^ 2 := by
  intro Λ η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hb : b < 2 := hbc.trans_lt hc
  let κ : ℝ := 1 / (L * (2 - b))
  have hκ : 0 < κ := by dsimp only [κ]; positivity
  have hiU : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc b c) :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hiV : IntegrableOn (fun s => ‖v s‖ ^ 2) (Icc b c) :=
    (hv.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  filter_upwards [crudeEnergy_ae_physical_time_primitive Q hU hV heU heV hv hab hbc hd,
    crudeEnergy_ae_joint_mixed_transpose_gaussian_mass hc hL hgen hgrad hphys hU hV heU heV hF hH heF heH,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiU hU heU,
    crudeEnergy_ae_gaussian_spacetime Q κ hκ hiV hV heV,
    crudeEnergy_ae_gaussian_endpoint Q hκ (u b),
    crudeEnergy_ae_gaussian_endpoint Q hκ (u c), hC1]
    with ω hprim hmass hUsq hVsq hi₀ hi₁ hpq
  let X : Vec d × ℝ → ℂ := fun z => U (z.2, translate z.1 ω)
  let Y : Vec d × ℝ → ℂ := fun z => V (z.2, translate z.1 ω)
  let R : Vec d × ℝ → ℂ := fun z => F ((z.2, ω), z.1)
  let T : Vec d × ℝ → ℂ := fun z => H ((z.2, ω), z.1)
  have hX : Measurable X := hU.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hY : Measurable Y := hV.comp (measurable_snd.prodMk
    (Probability.continuous_translate.measurable.comp (measurable_fst.prodMk measurable_const)))
  have hFω : Measurable (fun z : ℝ × Vec d => F ((z.1, ω), z.2)) :=
    hF.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hHω : Measurable (fun z : ℝ × Vec d => H ((z.1, ω), z.2)) :=
    hH.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
  have hR : Measurable R := hFω.comp measurable_swap
  have hT : Measurable T := hHω.comp measurable_swap
  have hiR := crudeEnergy_physical_gaussian_spacetime (b := b) (c := c) hκ.le hpq.1 hFω (fun s => heF s ω)
  have hiT := crudeEnergy_physical_gaussian_spacetime (b := b) (c := c) hκ.le hpq.2.1 hHω (fun s => heH s ω)
  have hpr := crudeEnergy_physical_time_primitive hFω hHω
    (fun s => heF s ω) (fun s => heH s ω) hpq.2.1 hab hbc hpq.2.2
  have hw : Measurable (fun z : Vec d × ℝ => Real.exp (-κ * euclideanSq z.1)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hw' : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  have hsub := crudeEnergy_gaussian_time_primitive_sub
    (U := X) (V := R)
    (u₀ := fun x => (u b) (translate x ω)) (u₁ := fun x => (u c) (translate x ω))
    (v₀ := fun x => (p b ω) x) (v₁ := fun x => (p c ω) x)
    hbc hY hT hVsq hiT hprim hpr
  have hsq := crudeEnergy_integrable_weighted_sub_sq
    (volume.prod (volume.restrict (Icc b c))) hw
    (fun _ => (Real.exp_pos _).le) hX hR hUsq hiR
  have hdsq := crudeEnergy_integrable_weighted_sub_sq
    (volume.prod (volume.restrict (Icc b c))) hw
    (fun _ => (Real.exp_pos _).le) hY hT hVsq hiT
  have hm (s : ℝ) : Measurable (fun x => (u s) (translate x ω)) :=
    (Lp.stronglyMeasurable (u s)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have h₀ := crudeEnergy_integrable_weighted_sub_sq volume hw'
    (fun _ => (Real.exp_pos _).le) (hm b) (Lp.stronglyMeasurable (p b ω)).measurable
    hi₀ (crudeEnergy_physical_gaussian_endpoint hκ.le (p b ω))
  have h₁ := crudeEnergy_integrable_weighted_sub_sq volume hw'
    (fun _ => (Real.exp_pos _).le) (hm c) (Lp.stronglyMeasurable (p c ω)).measurable
    hi₁ (crudeEnergy_physical_gaussian_endpoint hκ.le (p c ω))
  exact crudeEnergy_gaussian_primitive_mass hbc hc hLp
    (hX.sub hR) (hY.sub hT)
    ((hm b).sub (Lp.stronglyMeasurable (p b ω)).measurable)
    ((hm c).sub (Lp.stronglyMeasurable (p c ω)).measurable)
    hsq hdsq h₀ h₁ hsub hmass


/-- Gaussian Gronwall for the actual stationary and physical transpose paths. -/
theorem crudeEnergy_ae_mixed_transpose_gaussian_mass_gronwall
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a b c L : ℝ}
    (hab : a < b) (hbc : b ≤ c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Icc b c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        (∫ x, η b x ^ 2 * ‖(u b) (translate x ω) - (p b ω) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - b)) := by
  intro Λ η
  let A := 20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2
  let D : ℝ × FieldPair d → ℝ := fun z =>
    ∫ x, η z.1 x ^ 2 * ‖U (z.1, translate x z.2) - F ((z.1, z.2), x)‖ ^ 2
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hDU : Measurable (fun z : (ℝ × FieldPair d) × Vec d =>
      U (z.1.1, translate z.2 z.1.2)) := hU.comp
    ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hη : Measurable (fun z : (ℝ × FieldPair d) × Vec d => η z.1.1 z.2 ^ 2) := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hD : Measurable D :=
    (hη.mul ((hDU.sub hF).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have heD (s : ℝ) : ∀ᵐ ω ∂reducedLaw Q, D (s, ω) =
      ∫ x, η s x ^ 2 * ‖(u s) (translate x ω) - (p s ω) x‖ ^ 2 := by
    have he := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (hU.comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (u s)).measurable (heU s)
    filter_upwards [he] with ω hω
    apply integral_congr_ae
    filter_upwards [hω, heF s ω] with x hx hy
    change U (s, translate x ω) = (u s) (translate x ω) at hx
    rw [hx, hy]
  have hbound (s : ℝ) (hs : s ∈ Icc b c) : ∀ᵐ ω ∂reducedLaw Q,
      D (s, ω) ≤ D (b, ω) + A * ∫ r in Icc b s, D (r, ω) := by
    have h := crudeEnergy_ae_integrated_mixed_transpose_gaussian_mass hab hs.1
      (hs.2.trans_lt hc) hL hu hv hd
      (fun r hr => hgen r ⟨hr.1, hr.2.trans hs.2⟩)
      (fun r hr => hgrad r ⟨hr.1, hr.2.trans hs.2⟩) hC1
      (fun r hr => hphys r ⟨hr.1, hr.2.trans hs.2⟩)
      hU hV heU heV hF hH heF heH
    filter_upwards [h, heD s, heD b] with ω hω hs hb
    rw [hs, hb]
    exact hω
  let J : ℝ × FieldPair d → ℝ := fun z => ∫ r in Icc b z.1, D (r, z.2)
  have hJ : Measurable J := by
    have hm : Measurable (fun z : (ℝ × FieldPair d) × ℝ =>
        if b ≤ z.2 ∧ z.2 ≤ z.1.1 then D (z.2, z.1.2) else 0) :=
      (hD.comp (measurable_snd.prodMk measurable_fst.snd)).ite
        ((measurableSet_le measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_fst.fst)) measurable_const
    have hi := (hm.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
    simpa only [J, ← integral_indicator measurableSet_Icc, Set.indicator, mem_Icc] using hi
  have hineq : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      D (s, ω) ≤ D (b, ω) + A * J (s, ω) := by
    apply (Measure.ae_ae_comm
      (p := fun s ω => D (s, ω) ≤ D (b, ω) + A * J (s, ω))
      (measurableSet_le hD ((hD.comp (measurable_const.prodMk measurable_snd)).add
        (measurable_const.mul hJ)))).mp
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hbound s hs
  have hiD : ∀ᵐ ω ∂reducedLaw Q, IntegrableOn (fun s => D (s, ω)) (Icc b c) :=
    crudeEnergy_ae_integrable_mixed_gaussian_mass Q hbc hc hLp hu
      (hC1.mono fun _ h => h.1) hU heU hF heF
  filter_upwards [hineq, hiD, hbound c ⟨hbc, le_rfl⟩, heD c, heD b]
    with ω hω hiω hcω hec heb
  have hint : IntervalIntegrable (fun s => D (s, ω)) volume b c := by
    have hi : IntegrableOn (fun s => D (s, ω)) (uIcc b c) := by
      simpa only [uIcc_of_le hbc] using hiω
    exact hi.intervalIntegrable
  have hω' : ∀ᵐ s ∂volume.restrict (Icc b c),
      D (s, ω) ≤ D (b, ω) + A * ∫ r in b..s, D (r, ω) := by
    filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with s hs hmem
    rwa [intervalIntegral.integral_of_le hmem.1, ← integral_Icc_eq_integral_Ioc]
  have hcω' : D (c, ω) ≤ D (b, ω) + A * ∫ r in b..c, D (r, ω) := by
    rwa [intervalIntegral.integral_of_le hbc, ← integral_Icc_eq_integral_Ioc]
  have h := crudeEnergy_integrable_mass_gronwall_ae hbc hA hint hω' hcω'
  rwa [hec, heb] at h


/-- Take the initial trace in the mixed transpose Gaussian comparison. -/
theorem crudeEnergy_ae_mixed_transpose_gaussian_initial_gronwall
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a c L : ℝ}
    (hac : a < c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Ioc a c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Ioc a c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p s ω) ∧
      Continuous (fun s => q s ω) ∧
      ∀ s, a < s → HasDerivAt (fun r => p r ω) (q s ω) s)
    (hphys : ∀ s ∈ Ioc a c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p s ω) (q s ω))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {F H : (ℝ × FieldPair d) × Vec d → ℂ} (hF : Measurable F) (hH : Measurable H)
    (heF : ∀ s ω, (fun x => F ((s, ω), x)) =ᵐ[volume] p s ω)
    (heH : ∀ s ω, (fun x => H ((s, ω), x)) =ᵐ[volume] q s ω) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p c ω) x‖ ^ 2) ≤
        3 * (∫ x, η a x ^ 2 * ‖(u a) (translate x ω) - (p a ω) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - a)) := by
  intro Λ η
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let τ : ℕ → ℝ := fun n => (c - a) / ((n : ℝ) + 1)
  have hτ : Tendsto τ atTop (𝓝 0) := by
    simpa only [τ, mul_one_div, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (c - a)
  have hτpos (n : ℕ) : 0 < τ n := div_pos (sub_pos.mpr hac) (by positivity)
  have hτle (n : ℕ) : τ n ≤ c - a := by
    dsimp only [τ]
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hκ : 0 < 2 / (L * (2 - a)) := div_pos (by norm_num)
    (mul_pos hLp (by linarith))
  have hκn (n : ℕ) : 2 / (L * (2 - a)) ≤ 2 / (L * (2 - (a + τ n))) := by
    apply div_le_div_of_nonneg_left (by norm_num)
      (mul_pos hLp (by linarith [hτle n]))
    exact mul_le_mul_of_nonneg_left (by linarith [hτpos n]) hLp.le
  have hη (s : ℝ) (x : Vec d) :
      Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 =
        Real.exp (-(2 / (L * (2 - s))) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hshift : a + (c - a) = c := by ring
  have hb (n : ℕ) : ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-(2 / (L * (2 - c))) * euclideanSq x) *
        ‖(u (a + (c - a))) (translate x ω) - (p (a + (c - a)) ω) x‖ ^ 2) ≤
      (∫ x, Real.exp (-(2 / (L * (2 - (a + τ n)))) * euclideanSq x) *
        ‖(u (a + τ n)) (translate x ω) - (p (a + τ n) ω) x‖ ^ 2) *
        Real.exp ((20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2) * ((c - a) - τ n)) := by
    have hn := crudeEnergy_ae_mixed_transpose_gaussian_mass_gronwall
      (show a < a + τ n by linarith [hτpos n])
      (show a + τ n ≤ c by linarith [hτle n]) hc hL hu hv hd
      (fun s hs => hgen s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      (fun s hs => hgrad s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      hC1 (fun s hs => hphys s ⟨by linarith [hs.1, hτpos n], hs.2⟩)
      hU hV heU heV hF hH heF heH
    simpa only [hη, hshift, show (c - a) - τ n = c - (a + τ n) by ring] using hn
  have hi := crudeEnergy_ae_gaussian_initial_mass_bound Q
    (u := fun s => u (a + s))
    (p := fun s ω => p (a + s) ω)
    (hu.comp (continuous_const.add continuous_id))
    (by
      filter_upwards [hC1] with ω hω
      exact (hω.1.comp (continuous_const.add continuous_id)).continuousAt)
    hτ hκ hκn hb
  simpa only [η, hη, hshift, add_zero] using hi


/-- Joint representatives for the actual transpose initial Gaussian comparison. -/
theorem crudeEnergy_ae_mixed_transpose_gaussian_initial_gronwall_of_stronglyMeasurable
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {a c L : ℝ}
    (hac : a < c) (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hu : Continuous u) (hv : Continuous v)
    (hd : ∀ s, a < s → HasDerivAt u (v s) s)
    (hgen : ∀ s ∈ Ioc a c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Ioc a c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {p q : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hp : StronglyMeasurable p) (hq : StronglyMeasurable q)
    (hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p (s, ω)) ∧
      Continuous (fun s => q (s, ω)) ∧
      ∀ s, a < s → HasDerivAt (fun r => p (r, ω)) (q (s, ω)) s)
    (hphys : ∀ s ∈ Ioc a c, ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p (s, ω)) (q (s, ω))) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, η c x ^ 2 * ‖(u c) (translate x ω) - (p (c, ω)) x‖ ^ 2) ≤
        3 * (∫ x, η a x ^ 2 * ‖(u a) (translate x ω) - (p (a, ω)) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * (c - a)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU⟩ := StronglyMeasurable.exists_joint_l2_representative hu.stronglyMeasurable
  obtain ⟨V, hV, heV⟩ := StronglyMeasurable.exists_joint_l2_representative hv.stronglyMeasurable
  obtain ⟨F, hF, heF⟩ := crudeEnergy_exists_joint_l2_representative_sigmaFinite hp
  obtain ⟨H, hH, heH⟩ := crudeEnergy_exists_joint_l2_representative_sigmaFinite hq
  exact crudeEnergy_ae_mixed_transpose_gaussian_initial_gronwall
    (p := fun s ω => p (s, ω)) (q := fun s ω => q (s, ω)) hac hc hL hu hv hd hgen hgrad
    hC1 hphys hU hV heU heV hF hH (fun s ω => heF (s, ω)) (fun s ω => heH (s, ω))


/-- Compare the stationary transpose orbit with physical transpose time averages. -/
theorem crudeEnergy_ae_transpose_averaged_gaussian_comparison
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P0 P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP0 : IsComplexEnvironmentSemigroup Q i ζ P0)
    (hP : IsComplexTransposeSemigroup Q P0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S0 S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexTransposeSemigroup ω.1 i ζ (S0 ω) (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ (ε : ℝ≥0) (c L : ℝ), 0 < c →
      64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let fε : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
      ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), S ω s.toNNReal (fR ω)
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fε ω)) x‖ ^ 2) ≤
        3 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fε ω) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  intro S0 S hS hSm fR hfR ε c L hc hL fε Λ
  let a₀ : ℝ := 1 - c
  let gε : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun ω =>
    ((ε : ℝ) : ℂ)⁻¹ • (S ω ε (fR ω) - fR ω)
  have hmean : StronglyMeasurable fε := by
    have hm : Measurable (fun z : FieldPair d × ℝ => S z.1 z.2.toNNReal (fR z.1)) :=
      hSm.comp ((hfR.measurable.comp measurable_fst).prodMk
        ((measurable_real_toNNReal.comp measurable_snd).prodMk measurable_fst))
    have hi := hm.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (ε : ℝ)))
    simpa only [fε, intervalIntegral.integral_of_le ε.coe_nonneg, Pi.smul_apply] using
      hi.fun_const_smul (((ε : ℝ) : ℂ)⁻¹)
  have hdiff : StronglyMeasurable gε := by
    simpa only [gε, Pi.smul_apply, Pi.sub_apply, Function.comp_def, id_eq] using
      ((hSm.comp (hfR.measurable.prodMk (measurable_const.prodMk measurable_id))).stronglyMeasurable.sub
        hfR).fun_const_smul (((ε : ℝ) : ℂ)⁻¹)
  let p : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun z => S z.2 (z.1 - a₀).toNNReal (fε z.2)
  let q : ℝ × FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun z => S z.2 (z.1 - a₀).toNNReal (gε z.2)
  have hp : StronglyMeasurable p :=
    (hSm.comp ((hmean.measurable.comp measurable_snd).prodMk
      ((measurable_real_toNNReal.comp (measurable_fst.sub_const a₀)).prodMk
        measurable_snd))).stronglyMeasurable
  have hq : StronglyMeasurable q :=
    (hSm.comp ((hdiff.measurable.comp measurable_snd).prodMk
      ((measurable_real_toNNReal.comp (measurable_fst.sub_const a₀)).prodMk
        measurable_snd))).stronglyMeasurable
  have horbit := crudeEnergy_complex_domain_orbit (hP.zero hP0) (hP.add hP0)
    (hP.continuous_apply hP0) (IsComplexTransposeGeneratorPair Q i ζ)
    (hP.tendsto_slope_iff hP0) hfg
  have hg (s : ℝ) := (horbit.2.2.2 s.toNNReal).choose_spec.1
  let G := fun s : ℝ => (horbit.2.2.2 s.toNNReal).choose
  have hG (s : ℝ) : HasComplexHorizontalGradient (reducedLaw Q)
      (reducedLaw_stationary Q) (P s.toNNReal f) (G s) := hg s
  have hshift : Continuous (fun s : ℝ => s - a₀) := continuous_id.sub continuous_const
  have hderiv (s : ℝ) (hs : a₀ < s) :
      HasDerivAt (fun r : ℝ => P (r - a₀).toNNReal f) (P (s - a₀).toNNReal g) s := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      (horbit.2.2.1 (s - a₀) (sub_pos.mpr hs)).scomp s ((hasDerivAt_id s).sub_const a₀)
  have hC1 : ∀ᵐ ω ∂reducedLaw Q, Continuous (fun s => p (s, ω)) ∧
      Continuous (fun s => q (s, ω)) ∧
      ∀ s, a₀ < s → HasDerivAt (fun r => p (r, ω)) (q (s, ω)) s := by
    filter_upwards [hS] with ω hω
    have h := crudeEnergy_physical_transpose_averaged_orbit hω (fR ω) ε
    refine ⟨h.1.comp hshift, h.2.1.comp hshift, fun s hs => ?_⟩
    simpa only [p, q, fε, gε, Function.comp_def, id_eq, one_smul] using
      (h.2.2.1 (s - a₀) (sub_pos.mpr hs)).scomp s ((hasDerivAt_id s).sub_const a₀)
  have hphys (s : ℝ) (_ : s ∈ Ioc a₀ 1) : ∀ᵐ ω ∂reducedLaw Q,
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ (p (s, ω)) (q (s, ω)) := by
    filter_upwards [hS] with ω hω
    exact (crudeEnergy_physical_transpose_averaged_orbit hω (fR ω) ε).2.2.2 (s - a₀).toNNReal
  have hb := crudeEnergy_ae_mixed_transpose_gaussian_initial_gronwall_of_stronglyMeasurable
    (G := fun s => G (s - a₀)) (show a₀ < 1 by dsimp only [a₀]; linarith)
    (by norm_num : (1 : ℝ) < 2) hL (horbit.1.comp hshift) (horbit.2.1.comp hshift) hderiv
    (fun s _ => horbit.2.2.2 (s - a₀).toNNReal) (fun s _ => hG (s - a₀)) hp hq hC1 hphys
  filter_upwards [hS, hb] with ω hω hωb
  have hend : 1 - a₀ = c := by dsimp only [a₀]; ring
  have hstart : 2 - a₀ = 1 + c := by dsimp only [a₀]; ring
  simpa only [p, Function.comp_def, hend, hstart, sub_self, Real.toNNReal_zero, hP.zero hP0, hω.1,
    ContinuousLinearMap.id_apply, show (2 : ℝ) - 1 = 1 by norm_num, mul_one] using hωb


/-- Removing physical time averages gives the transpose Gaussian comparison. -/
theorem crudeEnergy_ae_transpose_gaussian_comparison
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P0 P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP0 : IsComplexEnvironmentSemigroup Q i ζ P0)
    (hP : IsComplexTransposeSemigroup Q P0 P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S0 S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexTransposeSemigroup ω.1 i ζ (S0 ω) (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fR ω)) x‖ ^ 2) ≤
        27 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fR ω) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  letI : BorelSpace (Lp ℂ 2 (volume : Measure (Vec d))) := ⟨rfl⟩
  intro S0 S hS hSm fR hfR c L hc hL Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let ε : ℕ → ℝ≥0 := fun n => ⟨1 / ((n : ℝ) + 1), by positivity⟩
  have hε : Tendsto ε atTop (𝓝[>] (0 : ℝ≥0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun n => ?_)⟩
    · apply NNReal.tendsto_coe.mp
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    · change 0 < 1 / ((n : ℝ) + 1)
      positivity
  let fε : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)) := fun n ω =>
    (((ε n : ℝ)) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε n : ℝ), S ω s.toNNReal (fR ω)
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hb (n : ℕ) := crudeEnergy_ae_transpose_averaged_gaussian_comparison
    hP0 hP hfg S0 S hS hSm fR hfR (ε n) c L hc hL
  have hi₀ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hLp (by linarith : 0 < 1 + c))) f
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) hLp) (P c.toNNReal f)
  filter_upwards [hS, ae_all_iff.mpr hb, hi₀, hi₁] with ω hω hbω hi₀ω hi₁ω
  have ht₀ := (crudeEnergy_complex_time_average_tendsto hω.1 hω.2.2.1 (fR ω) 0).comp hε
  have ht₁ := (crudeEnergy_complex_time_average_tendsto hω.1 hω.2.2.1
    (fR ω) c.toNNReal).comp hε
  have ht₀' : Tendsto (fun n => fε n ω) atTop (𝓝 (fR ω)) := by
    simpa only [fε, Function.comp_def, hω.1, ContinuousLinearMap.id_apply] using! ht₀
  have hdist₀ : Tendsto (fun n => ‖fR ω - fε n ω‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), norm_sub_rev] using
      (ht₀'.sub_const (fR ω)).norm.pow 2
  have hdist₁ : Tendsto
      (fun n => ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2)
      atTop (𝓝 0) := by
    simpa only [fε, Function.comp_def, sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0)] using!
      (ht₁.sub_const (S ω c.toNNReal (fR ω))).norm.pow 2
  let B : ℝ := ∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
    ‖f (translate x ω) - (fR ω) x‖ ^ 2
  let E : ℝ := Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c)
  have hlim : Tendsto (fun n => 27 * (B + ‖fR ω - fε n ω‖ ^ 2) * E +
      3 * ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2)
      atTop (𝓝 (27 * B * E)) := by
    simpa only [add_zero, mul_zero] using
      (((hdist₀.const_add B).const_mul 27).mul_const E).add (hdist₁.const_mul 3)
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hinit := crudeEnergy_gaussian_compare_physical_data
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (mul_nonneg hLp.le (by linarith : 0 ≤ 1 + c)))
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
    hi₀ω (fε n ω) (fR ω)
  have hlast := crudeEnergy_gaussian_compare_physical_data
    (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLp.le)
    ((Lp.stronglyMeasurable (P c.toNNReal f)).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
    hi₁ω (S ω c.toNNReal (fR ω)) (S ω c.toNNReal (fε n ω))
  simp only [← hη, Function.comp_def, id_eq] at hinit hlast
  have hmiddle := (hbω n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 3)) (Real.exp_nonneg _))
  apply hlast.trans
  calc
    _ ≤ 3 * (3 * (3 * (B + ‖fR ω - fε n ω‖ ^ 2)) * E +
        ‖S ω c.toNNReal (fε n ω) - S ω c.toNNReal (fR ω)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add hmiddle (le_refl _)) (by norm_num)
    _ = _ := by ring


/-- Density of the actual transpose graph extends Gaussian comparison to all L2 data. -/
theorem crudeEnergy_ae_transpose_gaussian_comparison_allLp
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P0 P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP0 : IsComplexEnvironmentSemigroup Q i ζ P0)
    (hP : IsComplexTransposeSemigroup Q P0 P) (f : Lp ℂ 2 (reducedLaw Q)) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S0 S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexTransposeSemigroup ω.1 i ζ (S0 ω) (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∀ fR : FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)), StronglyMeasurable fR →
    ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (fR ω)) x‖ ^ 2) ≤
        243 * (∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
          ‖f (translate x ω) - (fR ω) x‖ ^ 2) *
          Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  intro S0 S hS hSm fR hfR c L hc hL Λ
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  let κ₀ : ℝ := 2 / (L * (1 + c))
  let κ₁ : ℝ := 2 / L
  have hκ₀ : 0 < κ₀ := div_pos (by norm_num) (mul_pos hLp (by linarith))
  have hκ₁ : 0 < κ₁ := div_pos (by norm_num) hLp
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨fn, hfn, htfn⟩ := mem_closure_iff_seq_limit.mp
    ((dense_complexTransposeGenerator_domain Q i ζ) f)
  choose gn hgn using hfn
  obtain ⟨ns, hns, ht₀⟩ :=
    crudeEnergy_stationary_gaussian_seq_trace_ae Q htfn κ₀ hκ₀
  have htP : Tendsto (fun n => P c.toNNReal (fn (ns n))) atTop
      (𝓝 (P c.toNNReal f)) :=
    (P c.toNNReal).continuous.tendsto f |>.comp (htfn.comp hns.tendsto_atTop)
  obtain ⟨ms, hms, ht₁⟩ :=
    crudeEnergy_stationary_gaussian_seq_trace_ae Q htP κ₁ hκ₁
  let v : ℕ → Lp ℂ 2 (reducedLaw Q) := fun n => fn (ns (ms n))
  have hb (n : ℕ) := crudeEnergy_ae_transpose_gaussian_comparison
    hP0 hP (hgn (ns (ms n))) S0 S hS hSm fR hfR c L hc hL
  simp_rw [hη] at hb
  have hi₀ := crudeEnergy_ae_gaussian_endpoint Q hκ₀ f
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q hκ₁ (P c.toNNReal f)
  have hi₀n (n : ℕ) := crudeEnergy_ae_gaussian_endpoint Q hκ₀ (v n)
  have hi₁n (n : ℕ) := crudeEnergy_ae_gaussian_endpoint Q hκ₁ (P c.toNNReal (v n))
  have hwm (κ : ℝ) : Measurable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
    unfold euclideanSq dot
    fun_prop
  have hom (a : Lp ℂ 2 (reducedLaw Q)) (ω : FieldPair d) :
      Measurable (fun x : Vec d => a (translate x ω)) :=
    (Lp.stronglyMeasurable a).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  filter_upwards [ht₀, ht₁, hi₀, hi₁, ae_all_iff.mpr hi₀n, ae_all_iff.mpr hi₁n,
      ae_all_iff.mpr hb] with ω ht₀ω ht₁ω hi₀ω hi₁ω hi₀nω hi₁nω hbω
  let B : ℝ := ∫ x, Real.exp (-κ₀ * euclideanSq x) *
    ‖f (translate x ω) - (fR ω) x‖ ^ 2
  let E : ℝ := Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c)
  let E₀ : ℕ → ℝ := fun n => ∫ x, Real.exp (-κ₀ * euclideanSq x) *
    ‖(v n) (translate x ω) - f (translate x ω)‖ ^ 2
  let E₁ : ℕ → ℝ := fun n => ∫ x, Real.exp (-κ₁ * euclideanSq x) *
    ‖(P c.toNNReal f) (translate x ω) - (P c.toNNReal (v n)) (translate x ω)‖ ^ 2
  have hE₀ : Tendsto E₀ atTop (𝓝 0) := ht₀ω.comp hms.tendsto_atTop
  have hE₁ : Tendsto E₁ atTop (𝓝 0) := by
    apply ht₁ω.congr'
    exact Eventually.of_forall fun n => integral_congr_ae
      (ae_of_all _ fun x => by dsimp only [E₁, v]; rw [norm_sub_rev])
  have hlim : Tendsto (fun n => 3 * E₁ n + 243 * (E₀ n + B) * E)
      atTop (𝓝 (243 * B * E)) := by
    simpa only [mul_zero, zero_add] using
      (hE₁.const_mul 3).add (((hE₀.add_const B).const_mul 243).mul_const E)
  simp_rw [hη]
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro n
  have hiD₀ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₀)
    (fun _ => Real.exp_nonneg _) (hom f ω) (Lp.stronglyMeasurable (fR ω)).measurable
    hi₀ω (crudeEnergy_physical_gaussian_endpoint hκ₀.le _)
  have hiD₁ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₁)
    (fun _ => Real.exp_nonneg _) (hom (P c.toNNReal (v n)) ω)
    (Lp.stronglyMeasurable (S ω c.toNNReal (fR ω))).measurable
    (hi₁nω n) (crudeEnergy_physical_gaussian_endpoint hκ₁.le _)
  have hiE₀ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₀)
    (fun _ => Real.exp_nonneg _) (hom (v n) ω) (hom f ω) (hi₀nω n) hi₀ω
  have hiE₁ := crudeEnergy_integrable_weighted_sub_sq volume (hwm κ₁)
    (fun _ => Real.exp_nonneg _) (hom (P c.toNNReal f) ω)
    (hom (P c.toNNReal (v n)) ω) hi₁ω (hi₁nω n)
  have hinit := crudeEnergy_gaussian_initial_comparison (le_refl κ₀)
    (g := fun x => (fR ω) x) (g₀ := fun x => (fR ω) x)
    hiE₀ hiD₀ (by simp only [sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero]; exact integrable_zero _ _ _)
  have hlast := crudeEnergy_gaussian_initial_comparison (le_refl κ₁)
    (g := fun x => (S ω c.toNNReal (fR ω)) x)
    (g₀ := fun x => (S ω c.toNNReal (fR ω)) x)
    hiE₁ hiD₁ (by simp only [sub_self, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero]; exact integrable_zero _ _ _)
  simp only [sub_self, norm_zero, zero_pow (by omega : (2 : ℕ) ≠ 0), mul_zero,
    integral_zero, add_zero] at hinit hlast
  have hmiddle := (hbω n).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinit (by norm_num : (0 : ℝ) ≤ 27)) (Real.exp_nonneg _))
  apply hlast.trans
  calc
    _ ≤ 3 * (E₁ n + (27 * (3 * (E₀ n + B)) * E)) :=
      mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hmiddle) (by norm_num)
    _ = _ := by ring


/-- Physical transpose cutoffs converge in Gaussian L2 to the actual stationary transpose orbit. -/
theorem crudeEnergy_exists_transpose_cutoff_gaussian_approximation_allLp
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P0 P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP0 : IsComplexEnvironmentSemigroup Q i ζ P0)
    (hP : IsComplexTransposeSemigroup Q P0 P) (f : Lp ℂ 2 (reducedLaw Q)) :
    letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
    ∀ (S0 S : FieldPair d → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ᵐ ω ∂reducedLaw Q, IsPhysicalComplexTransposeSemigroup ω.1 i ζ (S0 ω) (S ω)) →
      Measurable (fun z : Lp ℂ 2 (volume : Measure (Vec d)) × (ℝ≥0 × FieldPair d) =>
        S z.2.2 z.2.1 z.1) →
    ∃ F : ℕ → FieldPair d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, StronglyMeasurable (F n)) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n,
        (F n ω : Vec d → ℂ) =ᵐ[volume]
          {x : Vec d | euclideanNorm (x - 0) ≤ (n : ℝ)}.indicator
            (fun x => f (translate x ω))) ∧
      ∀ c L : ℝ, 0 < c → 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L →
        ∀ᵐ ω ∂reducedLaw Q,
          (∀ n, Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2) volume) ∧
          Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
            ‖(P c.toNNReal f) (translate x ω) - (S ω c.toNNReal (F n ω)) x‖ ^ 2)
            atTop (𝓝 0) := by
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  intro S0 S hS hSm
  obtain ⟨F, hFm, hF⟩ := crudeEnergy_exists_measurable_spatial_cutoffs Q f
  refine ⟨F, hFm, hF, ?_⟩
  intro c L hc hL
  let Λ := Real.exp (2 * Λ₀) * Λ₀
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hη (r : ℝ) (x : Vec d) : Real.exp (-euclideanSq x / r) ^ 2 =
      Real.exp (-(2 / r) * euclideanSq x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hi := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) (mul_pos hLp (by linarith : 0 < 1 + c))) f
  have hb (n : ℕ) := crudeEnergy_ae_transpose_gaussian_comparison_allLp
    hP0 hP f S0 S hS hSm (F n) (hFm n) c L hc hL
  have hi₁ := crudeEnergy_ae_gaussian_endpoint Q
    (div_pos (by norm_num : (0 : ℝ) < 2) hLp) (P c.toNNReal f)
  filter_upwards [hF, hi, hi₁, ae_all_iff.mpr hb] with ω hFω hiω hi₁ω hbω
  refine ⟨?_, ?_⟩
  · intro n
    simp_rw [hη]
    exact crudeEnergy_integrable_weighted_sub_sq volume
      (by unfold euclideanSq dot; fun_prop) (fun _ => Real.exp_nonneg _)
      ((Lp.stronglyMeasurable (P c.toNNReal f)).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)))
      (Lp.stronglyMeasurable (S ω c.toNNReal (F n ω))).measurable hi₁ω
      (crudeEnergy_physical_gaussian_endpoint
        (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hLp.le) _)
  · have hm : Measurable (fun x : Vec d => f (translate x ω)) :=
      (Lp.stronglyMeasurable f).measurable.comp
        (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
    have ht := crudeEnergy_gaussian_spatial_cutoff_defect_tendsto hm hiω
    simp_rw [← hη] at ht
    have ht' : Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / (L * (1 + c))) ^ 2 *
        ‖f (translate x ω) - (F n ω) x‖ ^ 2) atTop (𝓝 0) := by
      apply ht.congr'
      exact Eventually.of_forall fun n => integral_congr_ae
        ((hFω n).mono fun x hx => by dsimp only; rw [hx])
    have hbound := (ht'.const_mul 243).mul_const (Real.exp (20 * (d : ℝ) * Λ ^ 3 * ‖ζ‖ ^ 2 * c))
    simp only [mul_zero, zero_mul] at hbound
    exact squeeze_zero (fun n => integral_nonneg fun x =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)) hbω hbound


/-- Bounded stationary L2 data admit an actual smooth transpose representative with the structural swapped-kernel bound. -/
theorem crudeEnergy_transpose_representative_of_pointKernel
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ∀ᵐ ω ∂reducedLaw Q,
      ∃ u : Vec d → ℂ,
        (fun x => (Pdag t f) (translate x ω)) =ᵐ[volume] u ∧
        Differentiable ℝ u ∧ ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, c, N, hC, _hc, hk⟩ := hkernel d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ f B hB hf i ζ hζ P Pdag hP hPdag t ht
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  letI : MeasurableSpace (Lp ℂ 2 (volume : Measure (Vec d))) := borel _
  obtain ⟨S, Sdag, hpair, _hm, _hSm, hSdagm⟩ :=
    crudeEnergy_ae_exists_measurable_physical_pair Q i ζ
  have hSdag := hpair.mono fun _ h => h.2
  obtain ⟨F, _hFm, hF, hconv⟩ :=
    crudeEnergy_exists_transpose_cutoff_gaussian_approximation_allLp hP hPdag f S Sdag hSdag hSdagm
  let L : ℝ := 64 * (Real.exp (2 * D.ellipticity) * D.ellipticity) ^ 3
  have happrox := hconv (t : ℝ) L (by linarith) (le_refl _)
  have horbit := ae_ae_stationary_orbit_le (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable f).measurable.norm hf
  filter_upwards [hk Q hQ, horbit, hpair, hF, happrox] with ω hkω hfω hpairω hFω haω
  obtain ⟨K, hK, hreg⟩ := hkω i ζ hζ (S ω) (Sdag ω) hpairω.1 hpairω.2
  have hfm : AEStronglyMeasurable (fun y : Vec d => f (translate y ω)) volume :=
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable
  have hb := (hreg (fun t x y => K t y x) (by simp) t ht).2.2
    (fun y => f (translate y ω)) B hB hfm hfω
  refine ⟨fun x => ∫ y, K t y x * f (translate y ω), ?_, hb.1, ?_⟩
  · apply crudeEnergy_physical_cutoff_kernel_identification hK.transpose
      (show 0 < t by exact_mod_cast (show (0 : ℝ) < t by linarith)) hFω
      (ae_of_all _ fun x => (hb.2 x).1) L
    · simpa using haω.1
    · simpa using haω.2
  · exact fun x => (hb.2 x).2.2


/-- The actual transpose orbit satisfies the structural Euclidean and all-radius local energy bounds for every bounded L2 datum. -/
theorem crudeEnergy_transpose_bounds_of_pointKernel
    (hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
    ∀ (f : Lp ℂ 2 (reducedLaw Q)) (B : ℝ),
      0 ≤ B → (∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q i ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
    ∀ (t : ℝ≥0), 2 ≤ (t : ℝ) →
    ∀ G : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (Pdag t f) G →
      (∀ᵐ ω ∂reducedLaw Q, ‖Pdag t f ω‖ + Real.sqrt (∑ j : Fin d, ‖G j ω‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) ∧
      (∀ (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
        ‖Pdag t f ω‖ + localSpatialEnergy Q t ρ hρ x G 0 ω ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) * B) := by
  obtain ⟨C, N, hC, hr⟩ := crudeEnergy_transpose_representative_of_pointKernel hkernel d hd D
  let K : ℝ := 2 * (1 + Real.sqrt (d : ℝ))
  have hK : 1 ≤ K := by dsimp only [K]; nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hKC : 1 ≤ K * C := one_le_mul_of_one_le_of_one_le hK hC
  refine ⟨K * C, N, hKC, ?_⟩
  intro Q hQ f B hB hf i ζ hζ P Pdag hP hPdag t ht G hG
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let A : ℝ := C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hp := crudeEnergy_ae_gradient_bound_of_spatial_representatives
    (reducedLaw Q) (reducedLaw_stationary Q) (Pdag t f) G (mul_nonneg hA hB) hG
    (hr Q hQ f B hB hf i ζ hζ P Pdag hP hPdag t ht)
  have hb : 0 ≤ (1 + Real.sqrt (d : ℝ)) * (A * B) := by positivity
  have hdom : 2 * ((1 + Real.sqrt (d : ℝ)) * (A * B)) ≤
      (K * C) * (2 + (t : ℝ)) ^ N *
        Real.exp ((K * C) * ‖ζ‖ ^ 2 * (t : ℝ)) * B := by
    have he : Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
        Real.exp ((K * C) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ t.coe_nonneg
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      calc
        C = 1 * C := (one_mul C).symm
        _ ≤ K * C := mul_le_mul_of_nonneg_right hK (by linarith)
    calc
      _ = ((K * C) * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) * B := by dsimp only [A, K]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left he (by positivity)) hB
  constructor
  · filter_upwards [hp] with ω hω
    exact hω.trans ((by linarith : (1 + Real.sqrt (d : ℝ)) * (A * B) ≤
      2 * ((1 + Real.sqrt (d : ℝ)) * (A * B))).trans hdom)
  · intro ρ hρ x
    exact (norm_add_localSpatialEnergy_le_of_ae_bound Q (Pdag t f) G hb hp t ρ hρ x).mono
      fun _ h => h.trans hdom


private lemma crudeEnergy_grow_bound (E B C : ℝ) (n N : ℕ)
    (hE : 0 ≤ E) (hEC : E ≤ C) (hEBC : E * B ≤ C)
    (hn : n ≤ N) (t : ℝ≥0) (ζ : ℂ) :
    E * (2 + (t : ℝ)) ^ n * Real.exp (E * ‖ζ‖ ^ 2 * (t : ℝ)) * B ≤
      C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
  have hp : (2 + (t : ℝ)) ^ n ≤ (2 + (t : ℝ)) ^ N :=
    pow_le_pow_right₀ (by linarith [t.coe_nonneg]) hn
  calc
    _ = (E * B) * (2 + (t : ℝ)) ^ n *
        Real.exp (E * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
    _ ≤ C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      apply mul_le_mul
      · exact mul_le_mul hEBC hp (by positivity) (hE.trans hEC)
      · apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hEC (sq_nonneg _)) t.coe_nonneg
      · exact Real.exp_nonneg _
      · exact mul_nonneg (hE.trans hEC) (by positivity)

/-- The actual endpoint and its actual Euclidean horizontal gradient obey
one structural bound at all times at least two, uniformly on the force disc. -/
theorem crudeEnergy_large_time_of_pointKernel :
node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt →
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 2 ≤ (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t)) ∧
      (∀ t : ℝ≥0, 2 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        (∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
            Real.sqrt (∑ j : Fin d, ‖G t j ω‖ ^ 2) ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))) ∧
        (∀ (ρ : ℝ) (hρ : 0 < ρ) (x : Vec d), ∀ᵐ ω ∂reducedLaw Q,
          ‖uncenteredEndpoint hd Q ν ζ P Pdag β a μ t ω‖ +
            localSpatialEnergy Q t ρ hρ x (G t) 0 ω ≤
          C * (2 + (t : ℝ)) ^ N * Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ)))) := by
  intro hkernel d hd D
  obtain ⟨Cf, Nf, hCf, hf⟩ := crudeEnergy_forward_bounds_of_pointKernel hkernel d hd D
  obtain ⟨Ct, Nt, hCt, ht⟩ := crudeEnergy_transpose_bounds_of_pointKernel hkernel d hd D
  obtain ⟨B, hB, hb⟩ := crudeEnergy_initial_endpoint_bound d hd D
  let A := max Cf Ct
  let C := A * (1 + B)
  have hA : 1 ≤ A := hCf.trans (le_max_left _ _)
  have hAC : A ≤ C := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (show 1 ≤ 1 + B by linarith) (zero_le_one.trans hA)
  have hAB : A * B ≤ C :=
    mul_le_mul_of_nonneg_left (by linarith : B ≤ 1 + B) (zero_le_one.trans hA)
  have hCfA : Cf ≤ A := le_max_left _ _
  have hCtA : Ct ≤ A := le_max_right _ _
  refine ⟨C, max Nf Nt, hA.trans hAC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, hG⟩ := crudeEnergy_endpoint_gradient hd Q hQ β a μ hβ ζ P Pdag hP hPdag ν
  refine ⟨G, fun t ht => hG t (by exact_mod_cast (show 0 < (t : ℝ) by linarith)), ?_⟩
  intro t htime hζ
  let f := uncenteredEndpoint hd Q ν ζ P Pdag β a μ 0
  have hfb : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ B :=
    hb Q hQ β a μ hβ ha hμ ζ hζ P Pdag hP hPdag ν
  let R := if ν = Sum.inr true then Pdag else P
  have he (s : ℝ≥0) : R s f = uncenteredEndpoint hd Q ν ζ P Pdag β a μ s := by
    cases ν with
    | inl j => simp only [R, f, Sum.inl_ne_inr, ite_false, uncenteredEndpoint,
        hP.1, ContinuousLinearMap.id_apply]
    | inr b => cases b <;> simp [R, f, uncenteredEndpoint, transposeEndpoint,
        hP.1, hPdag.zero hP, map_smul]
  have hGR : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (R t f) (G t) := by
    rw [he]
    exact hG t (by exact_mod_cast (show 0 < (t : ℝ) by linarith))
  have hfdom := crudeEnergy_grow_bound Cf B C Nf (max Nf Nt)
    (zero_le_one.trans hCf) (hCfA.trans hAC)
    ((mul_le_mul_of_nonneg_right hCfA hB.le).trans hAB) (le_max_left _ _) t ζ
  have htdom := crudeEnergy_grow_bound Ct B C Nt (max Nf Nt)
    (zero_le_one.trans hCt) (hCtA.trans hAC)
    ((mul_le_mul_of_nonneg_right hCtA hB.le).trans hAB) (le_max_right _ _) t ζ
  by_cases hν : ν = Sum.inr true
  · have hGR' : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (Pdag t f) (G t) := by simpa only [R, ite_eq_left hν] using hGR
    obtain ⟨hp, hl⟩ := ht Q hQ f B hB.le hfb ⟨0, by omega⟩ ζ hζ P Pdag hP hPdag t htime (G t) hGR'
    have he' : Pdag t f = uncenteredEndpoint hd Q ν ζ P Pdag β a μ t := by
      simpa only [R, ite_eq_left hν] using he t
    rw [he'] at hp hl
    exact ⟨hp.mono fun _ h => h.trans htdom,
      fun ρ hρ x => (hl ρ hρ x).mono fun _ h => h.trans htdom⟩
  · have hGR' : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (P t f) (G t) := by simpa only [R, ite_eq_right hν] using hGR
    obtain ⟨hp, hl⟩ := hf Q hQ f B hB.le hfb ⟨0, by omega⟩ ζ hζ P hP t htime (G t) hGR'
    have he' : P t f = uncenteredEndpoint hd Q ν ζ P Pdag β a μ t := by
      simpa only [R, ite_eq_right hν] using he t
    rw [he'] at hp hl
    exact ⟨hp.mono fun _ h => h.trans hfdom,
      fun ρ hρ x => (hl ρ hρ x).mono fun _ h => h.trans hfdom⟩

end EinsteinFull.Blueprint
