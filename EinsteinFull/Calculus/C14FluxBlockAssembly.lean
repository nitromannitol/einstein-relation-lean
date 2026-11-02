import EinsteinFull.Calculus.CarverSFluxBlockGain
import EinsteinFull.Calculus.C3FluxAnnularLocalization
import EinsteinFull.Calculus.CarverSFluxBlockMoments
import EinsteinFull.Calculus.C6FluxBlockGlobalGradientMoment
import EinsteinFull.Calculus.C15FluxBlockBadEventEnergy
import EinsteinFull.Calculus.C28FluxGaussianTestBounds
import EinsteinFull.Calculus.C29FluxBadEventValue
import EinsteinFull.Calculus.C10FluxBlockTerminalEnvelope
import EinsteinFull.Calculus.C34FluxBlockTerminalProduct
import EinsteinFull.Calculus.C6FluxGrowthAbsorption
import EinsteinFull.Calculus.C6FluxBlockEventAssembly
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_block
import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_identity

open MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- On the original good event, the same selected centers give the spatial
L² bounds needed by the flux identity. -/
theorem c14_flux_block_good_event_centered_l2 {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (φ : Fin d → FieldPair d → Vec d → ℝ)
    (S : Fin d → FieldPair d → Vec d → Mat d)
    (hregular : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      Continuous (φ i ω) ∧ ∀ j k : Fin d, Continuous (fun x => S i ω x j k))
    (z : Vec d) (ρ : ℝ) (hρ : 0 < ρ) (H : ℝ) (E : Set (FieldPair d))
    (hosc : ∀ ω ∈ E, ∃ (a : Fin d → ℝ) (b : Fin d → Mat d),
      (∀ i j k, b i j k = -b i k j) ∧
      (∑ i : Fin d,
        (Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
          ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ}, |φ i ω x - a i| ^ 2) +
         Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
          ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ},
            frobeniusNorm (S i ω x - b i) ^ 2))) ≤ H) :
    ∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
      ∃ (a : Fin d → ℝ) (b : Fin d → Mat d),
        (∀ i j k, b i j k = -b i k j) ∧
        ∀ i : Fin d,
          MemLp (fun x => φ i ω x - a i) 2
            (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}) ∧
          MemLp (fun x => frobeniusNorm (S i ω x - b i)) 2
            (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}) ∧
          Calculus.S1.l2Size (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ})
              (fun x => φ i ω x - a i) +
            Calculus.S1.l2Size (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ})
              (fun x => frobeniusNorm (S i ω x - b i)) ≤
            Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal) * H := by
  filter_upwards [hregular] with ω hω hE
  obtain ⟨a, b, hskew, hbound⟩ := hosc ω hE
  refine ⟨a, b, hskew, ?_⟩
  exact carverS_flux_block_centered_corrector_l2 (fun i => φ i ω)
    (fun i => S i ω) a b (fun i => (hω i).1) (fun i => (hω i).2)
    z ρ hρ H hbound

/-- The cutoff-kernel test has topological support in the closed cutoff
ball, the same ball on which the Gaussian estimates are stated. -/
theorem c14_flux_block_cutoff_closed_support {d : ℕ}
    (χ : Vec d → ℝ) (kernel : Vec d → ℂ) (x z : Vec d) (R r : ℝ)
    (hχ : Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r}) :
    tsupport (fun y : Vec d => (χ (y - z) : ℂ) * kernel (x - y)) ⊆
      {y : Vec d | euclideanNorm (y - z) ≤ R * r} := by
  have hn : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  apply closure_minimal _ (isClosed_le hn continuous_const)
  intro y hy
  by_contra h
  have hc : χ (y - z) = 0 := by
    by_contra hc
    exact h (hχ hc)
  exact hy (by simp only [hc, Complex.ofReal_zero, zero_mul])

/-- A test and its derivative vanish outside its topological support, so
estimates on the integration window imply the global bounds used by the
actual endpoint identity estimate. -/
theorem c14_flux_block_test_bounds_global {d : ℕ}
    (ψ : Vec d → ℂ) (E : Set (Vec d)) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupport : tsupport ψ ⊆ E)
    (hvalue : ∀ x ∈ E, ‖ψ x‖ ≤ A)
    (hderiv : ∀ x ∈ E, ∀ k : Fin d, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) :
    (∀ x, ‖ψ x‖ ≤ A) ∧
      ∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B := by
  constructor
  · intro x
    by_cases hx : x ∈ E
    · exact hvalue x hx
    · have hz : ψ x = 0 := by
        by_contra h
        exact hx (hsupport (subset_tsupport ψ h))
      simpa only [hz, norm_zero] using hA
  · intro x k
    by_cases hx : x ∈ E
    · exact hderiv x hx k
    · have hz : fderiv ℝ ψ x = 0 := by
        by_contra h
        exact hx (hsupport (support_fderiv_subset ℝ h))
      simpa only [hz, ContinuousLinearMap.zero_apply, norm_zero] using hB

/-- The literal endpoint identity and the oscillation estimate combine on the
same good event, with the same skew centers and the actual flux witness. -/
theorem c14_flux_block_good_event_identity_bound (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (ν : EndpointIndex d) (t : ℝ≥0) (ht : 0 < (t : ℝ))
      (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
      (G J : Fin d → Lp ℂ 2 (reducedLaw Q))
      (φ : Fin d → FieldPair d → Vec d → ℝ)
      (S : Fin d → FieldPair d → Vec d → Mat d)
      (E : Set (FieldPair d)) (H : ℝ),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) (t : ℝ)
      let c := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q
      let B := {x : Vec d | euclideanNorm (x - z) < ρ}
      (∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
        Continuous (φ i ω) ∧ ∀ j k : Fin d, Continuous (fun x => S i ω x j k)) →
      (∀ ω ∈ E, ∃ (a₀ : Fin d → ℝ) (b₀ : Fin d → Mat d),
        (∀ i j k, b₀ i j k = -b₀ i k j) ∧
        (∑ i : Fin d, (Real.sqrt ((volume B).toReal⁻¹ *
          ∫ x in B, |φ i ω x - a₀ i| ^ 2) + Real.sqrt ((volume B).toReal⁻¹ *
          ∫ x in B, frobeniusNorm (S i ω x - b₀ i) ^ 2))) ≤ H) →
      (∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d, ∀ (a₀ : ℝ) (b₀ : Mat d),
        (∀ j k, b₀ j k = -b₀ k j) →
        ∀ ψ : Vec d → ℂ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        let u := fun x : Vec d => U (translate x ω)
        let g := fun (x : Vec d) (j : Fin d) => G j (translate x ω)
        let F := fun (x : Vec d) (j : Fin d) => g x j -
          match ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
          | _ => 0
        let q := fun x : Vec d => 2 * V (translate x ω) +
          match ν with
          | .inr true => 0
          | _ => 2 * c - 2 * ζ * (∑ k : Fin d, (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
        (∫ x, J i (translate x ω) * ψ x) =
          (∫ x, ((φ i ω x - a₀ : ℝ) : ℂ) * q x * ψ x) +
          (∫ x, ((φ i ω x - a₀ : ℝ) : ℂ) *
            (∑ k : Fin d, (∑ j : Fin d, (ω.1 x k j : ℂ) * F x j) *
              fderiv ℝ ψ x (unitVector k))) -
          (∫ x, ∑ k : Fin d, ∑ j : Fin d,
            ((S i ω x k j - b₀ k j : ℝ) : ℂ) * F x j *
              fderiv ℝ ψ x (unitVector k)) +
          match ν with
          | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
              ((S i ω x k ⟨0, by omega⟩ - b₀ k ⟨0, by omega⟩ : ℝ) : ℂ) *
                g x k) * ψ x)
          | _ => 0) →
      ∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
        ∀ (ψ : Vec d → ℂ) (A B' : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B' → tsupport ψ ⊆ B →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B') →
        ∀ i : Fin d,
          ‖∫ x, J i (translate x ω) * ψ x‖ ≤
          (volume B).toReal * H *
            (A * (2 / Real.sqrt (t : ℝ) * localSpatialEnergy Q t ρ hρ z G V ω + 2 * ‖c‖ +
                2 * ‖ζ‖ * ((d : ℝ) * M * localSpatialEnergy Q t ρ hρ z G V ω)) +
              (d : ℝ) ^ 3 * (M + 1) * B' * (localSpatialEnergy Q t ρ hρ z G V ω +
                2 * ‖ζ‖ * Real.sqrt ((volume B).toReal⁻¹ * ∫ x in B, ‖U (translate x ω)‖ ^ 2)) +
              2 * ‖ζ‖ * (d : ℝ) * A * localSpatialEnergy Q t ρ hρ z G V ω) := by
  obtain ⟨M, hM, hbound⟩ := carverS_flux_block_actual_identity_oscillation_bound d hd D
  refine ⟨M, hM, ?_⟩
  intro Q hQ β a μ ζ P Pdag ν t ht ρ hρ z G J φ S E H
  dsimp only
  intro hregular hosc hidentity
  filter_upwards [hregular, hidentity, hbound Q hQ β a μ ζ P Pdag ν t ht ρ hρ z G] with ω hreg hid hest
  intro hE ψ A B' hψ hc hA hB hs hv hder i
  obtain ⟨a₀, b₀, hskew, hoscω⟩ := hosc ω hE
  have he := hest (fun i => φ i ω) (fun i => S i ω) a₀ b₀
    (fun i => (hreg i).1) (fun i => (hreg i).2) H hoscω ψ A B' hA hB hs hv hder i
  rw [hid i (a₀ i) (b₀ i) (hskew i) ψ hψ hc]
  exact he

/-- A pointwise good-event flux estimate passes to the corresponding
finite moment without changing the event or the random majorant. -/
theorem c14_flux_block_good_event_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E) (p : ℝ≥0∞)
    (f : Ω → ℂ) (g : Ω → ℝ)
    (hf : MemLp f p μ) (hg : MemLp g p μ)
    (hbound : ∀ᵐ ω ∂μ, ω ∈ E → ‖f ω‖ ≤ g ω) :
    MemLp (E.indicator f) p μ ∧
      (eLpNorm (E.indicator f) p μ).toReal ≤
        (eLpNorm (E.indicator g) p μ).toReal := by
  have hfi := hf.indicator hE
  have hgi := hg.indicator hE
  refine ⟨hfi, ?_⟩
  have hdom : ∀ᵐ ω ∂μ, ‖E.indicator f ω‖ ≤ ‖E.indicator g ω‖ := by
    filter_upwards [hbound] with ω hω
    by_cases hωE : ω ∈ E
    · have hg0 : 0 ≤ g ω := (norm_nonneg _).trans (hω hωE)
      simpa [Set.indicator_of_mem hωE, Real.norm_eq_abs, abs_of_nonneg hg0] using hω hωE
    · simp [Set.indicator_of_notMem hωE]
  exact ENNReal.toReal_mono hgi.eLpNorm_ne_top
    (eLpNorm_mono_ae hfi.aestronglyMeasurable hdom)

/-- The pointwise good-event estimate controls the actual L²-valued
spatial block, using its samplewise integral representative. -/
theorem c14_flux_block_actual_good_event_moment {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ψ : Vec d → ℂ)
    (hψ : Integrable ψ) (hψc : Continuous ψ)
    (J : Lp ℂ 2 (reducedLaw Q)) (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (p : ℝ≥0∞) (g : FieldPair d → ℝ)
    (hf : MemLp ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ) p (reducedLaw Q))
    (hg : MemLp g p (reducedLaw Q))
    (hbound : ∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
      ‖∫ y, J (translate y ω) * ψ y‖ ≤ g ω) :
    (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ)) p (reducedLaw Q)).toReal ≤
      (eLpNorm (E.indicator g) p (reducedLaw Q)).toReal := by
  have hrep := (carverS_block_integral_representative Q ψ hψ hψc J).2
  apply (c14_flux_block_good_event_moment (reducedLaw Q) E hE p _ g hf hg ?_).2
  filter_upwards [hrep, hbound] with ω hrepω hboundω hωE
  rw [hrepω]
  simpa only [smul_eq_mul, mul_comm] using hboundω hωE

/-- An affine energy/value majorant has the corresponding finite moment on
any probability space. -/
theorem c14_flux_block_affine_majorant_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℝ≥0∞} (hp : 1 ≤ p)
    (energy value : Ω → ℝ) (he : MemLp energy p μ) (hv : MemLp value p μ)
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    MemLp (fun ω => A * energy ω + B * value ω + C) p μ ∧
      (eLpNorm (fun ω => A * energy ω + B * value ω + C) p μ).toReal ≤
        A * (eLpNorm energy p μ).toReal + B * (eLpNorm value p μ).toReal + C := by
  let f : Ω → ℝ := A • energy
  let g : Ω → ℝ := B • value
  let h : Ω → ℝ := fun _ => C
  have hf : MemLp f p μ := he.const_smul A
  have hg : MemLp g p μ := hv.const_smul B
  have hh : MemLp h p μ := memLp_const C
  have hfg := hf.add hg
  have hsum := hfg.add hh
  have hn1 := eLpNorm_add_le (f := f) (g := g) (μ := μ) hp
  have hn2 := eLpNorm_add_le (f := f + g) (g := h) (μ := μ) hp
  have hreal1 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩) hn1
  have hreal2 := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfg.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩) hn2
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at hreal1
  rw [ENNReal.toReal_add hfg.eLpNorm_ne_top hh.eLpNorm_ne_top] at hreal2
  have hfn : (eLpNorm f p μ).toReal = A * (eLpNorm energy p μ).toReal := by
    dsimp [f]
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hA, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hA]
  have hgn : (eLpNorm g p μ).toReal = B * (eLpNorm value p μ).toReal := by
    dsimp [g]
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal hB, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hB]
  have hhn : (eLpNorm h p μ).toReal = C := by
    dsimp [h]
    rw [eLpNorm_const _ (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hp))
      (NeZero.ne μ), measure_univ, ENNReal.one_rpow, mul_one,
      Real.enorm_eq_ofReal hC, ENNReal.toReal_ofReal hC]
  refine ⟨?_, ?_⟩
  · change MemLp ((f + g) + h) p μ
    exact hsum
  · change (eLpNorm ((f + g) + h) p μ).toReal ≤ _
    rw [hfn, hgn] at hreal1
    rw [hhn] at hreal2
    linarith

/-- The actual good-event block inherits an affine local-energy and
local-value moment bound. -/
theorem c14_flux_block_actual_good_event_affine_moment {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (ψ : Vec d → ℂ)
    (hψ : Integrable ψ) (hψc : Continuous ψ)
    (J : Lp ℂ 2 (reducedLaw Q)) (E : Set (FieldPair d)) (hE : MeasurableSet E)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (energy value : FieldPair d → ℝ)
    (he : MemLp energy p (reducedLaw Q)) (hv : MemLp value p (reducedLaw Q))
    (A B C : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hf : MemLp ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ) p (reducedLaw Q))
    (hbound : ∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
      ‖∫ y, J (translate y ω) * ψ y‖ ≤ A * energy ω + B * value ω + C) :
    (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ)) p (reducedLaw Q)).toReal ≤
      A * (eLpNorm energy p (reducedLaw Q)).toReal +
        B * (eLpNorm value p (reducedLaw Q)).toReal + C := by
  letI := reducedLaw_probability Q
  let g : FieldPair d → ℝ := fun ω => A * energy ω + B * value ω + C
  obtain ⟨hg, hg_norm⟩ := c14_flux_block_affine_majorant_moment
    (reducedLaw Q) hp energy value he hv A B C hA hB hC
  have hi := c14_flux_block_actual_good_event_moment Q ψ hψ hψc J E hE p g hf hg hbound
  exact hi.trans ((ENNReal.toReal_mono hg.eLpNorm_ne_top
    (eLpNorm_indicator_le g hE)).trans hg_norm)

/-- The explicit good-event identity estimate yields the corresponding
moment estimate for the actual local energy and endpoint value. -/
theorem c14_flux_block_identity_good_event_moment {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V U J : Lp ℂ 2 (reducedLaw Q))
    (ζ c : ℂ) (M H A B' : ℝ) (hM : 0 ≤ M) (hH : 0 ≤ H)
    (hA : 0 ≤ A) (hB : 0 ≤ B')
    (ψ : Vec d → ℂ) (hψ : Integrable ψ) (hψc : Continuous ψ)
    (E : Set (FieldPair d)) (hE : MeasurableSet E) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (hf : MemLp ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ) p (reducedLaw Q)) :
    let ball := {x : Vec d | euclideanNorm (x - z) < ρ}
    let energy := localSpatialEnergy Q t ρ hρ z G V
    let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
      ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
    let a := (volume ball).toReal * H *
      (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
        (d : ℝ) ^ 3 * (M + 1) * B' + 2 * ‖ζ‖ * (d : ℝ) * A)
    let b := (volume ball).toReal * H *
      ((d : ℝ) ^ 3 * (M + 1) * B' * (2 * ‖ζ‖))
    let cc := (volume ball).toReal * H * (A * (2 * ‖c‖))
    MemLp energy p (reducedLaw Q) → MemLp value p (reducedLaw Q) →
    (∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
      ‖∫ x, J (translate x ω) * ψ x‖ ≤
        (volume ball).toReal * H *
          (A * (2 / Real.sqrt (t : ℝ) * energy ω + 2 * ‖c‖ +
              2 * ‖ζ‖ * ((d : ℝ) * M * energy ω)) +
            (d : ℝ) ^ 3 * (M + 1) * B' * (energy ω + 2 * ‖ζ‖ * value ω) +
            2 * ‖ζ‖ * (d : ℝ) * A * energy ω)) →
    (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y J : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ)) p (reducedLaw Q)).toReal ≤
      a * (eLpNorm energy p (reducedLaw Q)).toReal +
        b * (eLpNorm value p (reducedLaw Q)).toReal + cc := by
  dsimp only
  intro he hv hpoint
  let ball := {x : Vec d | euclideanNorm (x - z) < ρ}
  let energy := localSpatialEnergy Q t ρ hρ z G V
  let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
    ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
  let a := (volume ball).toReal * H *
    (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
      (d : ℝ) ^ 3 * (M + 1) * B' + 2 * ‖ζ‖ * (d : ℝ) * A)
  let b := (volume ball).toReal * H *
    ((d : ℝ) ^ 3 * (M + 1) * B' * (2 * ‖ζ‖))
  let cc := (volume ball).toReal * H * (A * (2 * ‖c‖))
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ cc := by dsimp [cc]; positivity
  apply c14_flux_block_actual_good_event_affine_moment Q ψ hψ hψc J E hE p hp
    energy value he hv a b cc ha hb hc hf
  filter_upwards [hpoint] with ω hω hωE
  convert hω hωE using 1 <;> dsimp [a, b, cc, energy, value, ball] <;> ring

/-- The actual endpoint has a terminal moment on the open window used by
the flux identity, with the same one-eighth-time normalization. -/
theorem c14_flux_block_open_terminal_local_value_moment
    (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ρ : ℝ) (z : Vec d),
      Real.sqrt (t : ℝ) ≤ ρ →
      let L := fun ω : FieldPair d => Real.sqrt
        ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
          ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ},
            ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t (translate x ω)‖ ^ 2)
      MemLp L (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm L (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨Cp, hCp, hgrowth⟩ := carverS_flux_block_late_endpoint_growth d hd D p hp
  refine ⟨2, Cp, by norm_num, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht ρ z hρ
  have hρ' : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have hU := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t
  have hV := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν (t / 8)
  obtain ⟨hL, hLnorm⟩ := carverS_flux_block_local_value_moment Q
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) p hp hU ρ hρ' z
  refine ⟨hL, hLnorm.trans ?_⟩
  have h8 : t / 8 ≤ t := div_le_self zero_le (by norm_num)
  have hsum : t / 8 + (t - t / 8) = t := by rw [add_comm, tsub_add_cancel_of_le h8]
  have hrestart := hP.indexedEndpoint_add hd hPdag β a μ ν (t / 8) (t - t / 8)
  rw [hsum] at hrestart
  have hg := hgrowth Q ζ P Pdag hP hPdag ν
    (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)) hV (t - t / 8)
  rw [← hrestart] at hg
  have htime : ((t - t / 8 : ℝ≥0) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast (tsub_le_self : t - t / 8 ≤ t)
  have he : Real.exp (Cp * ‖ζ‖ ^ 2 * ((t - t / 8 : ℝ≥0) : ℝ)) ≤
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htime (mul_nonneg hCp.le (sq_nonneg _))
  have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hpow : 1 ≤ (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (2 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hn : 0 ≤ (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
      FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := ENNReal.toReal_nonneg
  have hexp := (Real.exp_pos (Cp * ‖ζ‖ ^ 2 * (t : ℝ))).le
  exact hg.trans (by nlinarith [mul_nonneg hn hexp,
    mul_le_mul_of_nonneg_right he hn,
    mul_le_mul_of_nonneg_right hpow (mul_nonneg hn hexp)])


/-- The selected corrector pair supplies one measurable event and one flux
witness for the actual identity estimate at every positive time. -/
theorem c14_flux_block_selected_good_event_bound
    (hsp : node_e_u3A_sublinear_u2D_pairStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ κ C c M : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        let ρ := C * r
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < ρ}
        let energy := localSpatialEnergy Q t ρ hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        ∀ᵐ ω ∂reducedLaw Q, ω ∈ E →
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
          ‖∫ x, J t i (translate x ω) * ψ x‖ ≤
          (volume ball).toReal * (C * r ^ (1 - κ)) *
            (A * (2 / Real.sqrt (t : ℝ) * energy ω + 2 * ‖center‖ +
                2 * ‖ζ‖ * ((d : ℝ) * M * energy ω)) +
              (d : ℝ) ^ 3 * (M + 1) * B * (energy ω + 2 * ‖ζ‖ * value ω) +
              2 * ‖ζ‖ * (d : ℝ) * A * energy ω) := by
  obtain ⟨κ, C, c, hκ, hκhalf, hC, hc, hpair⟩ :=
    carverS_flux_block_selected_pair hsp d hd D
  obtain ⟨M, hM, hbound⟩ := c14_flux_block_good_event_identity_bound d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨φ, S, hregular, hevents, hidentity⟩ := hpair Q hQ
  obtain ⟨G, J, hflux, hid⟩ := hidentity hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hosc⟩ := hevents r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ
  have hreg : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      Continuous (φ i ω) ∧ ∀ j k : Fin d, Continuous (fun x => S i ω x j k) :=
    hregular.mono fun ω h i => ⟨(h i).1.continuous, fun j k => ((h i).2.1 j k).continuous⟩
  exact hbound Q hQ β a μ ζ P Pdag ν t ht (C * r) hρ z
    (G t) (J t) φ S E (C * r ^ (1 - κ)) hreg hosc (hid t ht).2


/-- The selected flux and its original good event satisfy the finite-moment
identity estimate, using local-time control for that same flux witness. -/
theorem c14_flux_block_selected_good_event_moment
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ κ C c M : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          (eLpNorm energy (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          (eLpNorm value (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * ‖center‖)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_bound hsp d hd D
  obtain ⟨C₁, C₂, hC₁, hC₂, hlocal⟩ :=
    carverS_flux_block_local_time_on_flux_witness hlt d hd D p hp
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hpoint⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i hf
  have henergy := (hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    (C * r) z hscale).1
  have hU := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t
  have hvalue := (carverS_flux_block_local_value_moment Q
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) p hp hU (C * r) hρ z).1
  have hψcont := hψ.continuous
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hH : 0 ≤ C * r ^ (1 - κ) := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  apply c14_flux_block_identity_good_event_moment Q t (C * r) hρ z (G t)
    (deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ))
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (J t i) ζ
    (ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q)
    M (C * r ^ (1 - κ)) A B (by linarith) hH hA hB ψ hψint hψcont E hE
    (ENNReal.ofReal p) hp' hf henergy hvalue
  filter_upwards [hpoint t ht hρ] with ω hω hωE
  exact hω hωE ψ A B hψ hψc hA hB hs hv hdψ i


/-- Crude energy control gives finite moments for arbitrary integrable test
averages of the supplied actual weak-flux witness. -/
theorem c14_flux_block_actual_witness_memLp
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ) (hζ : ‖ζ‖ ≤ 4)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (t : ℝ≥0) (ht : 1 ≤ (t : ℝ))
    (G J : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G J)
    (p : ℝ) (hp : 2 ≤ p) (ψ : Vec d → ℂ)
    (hψ : Integrable ψ) (hψc : Continuous ψ) (i : Fin d) :
    MemLp ((∫ y : Vec d, ψ y • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y (J i) : Lp ℂ 2 (reducedLaw Q)) :
      FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  have hJ : MemLp (J i : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
    EinsteinFull.Calculus.K8.endpoint_flux_memLp_of_crude hlt hcr hd D Q hQ β a μ hβ ha hμ ζ
      hζ P Pdag hP hPdag ν t ht G J hflux i
  exact memLp_integral_cmul_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (by linarith) ψ hψ hψc (J i) hJ


/-- Crude energy removes the block-integrability premise for the selected witness. -/
theorem c14_flux_block_selected_good_event_moment_of_crude
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ κ C c M : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          (eLpNorm energy (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          (eLpNorm value (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * ‖center‖)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_moment hsp hlt d hd D p hp
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hmoment⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i
  have hψcont := hψ.continuous
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
  have hf := c14_flux_block_actual_witness_memLp hlt hcr d hd D Q hQ β a μ hβ ha hμ ζ hζ
    P Pdag hP hPdag ν t ht1 (G t) (J t) (hflux t ht) p hp ψ hψint hψcont i
  exact ⟨hf, hmoment t ht hρ hscale ψ A B hψ hψc hA hB hs hv hdψ i hf⟩


/-- Quantitative selected-event bounds use the actual flux and one-eighth-time endpoint. -/
theorem c14_flux_block_selected_good_event_quantitative
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ κ C c M Ce Cpe Cv Cpv Cc Cpc : ℝ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
      1 ≤ Ce ∧ 0 < Cpe ∧ 1 ≤ Cv ∧ 0 < Cpv ∧ 1 ≤ Cc ∧ 0 < Cpc ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
        let energyBound := Ce * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Ce *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpe * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let valueBound := Cv * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cv *
          Real.exp (Cpv * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let centerBound := ‖ζ‖ * Cc * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cc *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpc * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          energyBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          valueBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * centerBound)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_moment_of_crude hsp hlt hcr d hd D p hp
  obtain ⟨Ce, Cpe, hCe, hCpe, hlocal⟩ :=
    carverS_flux_block_local_time_on_flux_witness hlt d hd D p hp
  obtain ⟨Cv, Cpv, hCv, hCpv, hvalue⟩ :=
    c14_flux_block_open_terminal_local_value_moment d hd D p hp
  obtain ⟨Cc, Cpc, hCc, hCpc, hcenter⟩ :=
    c6_flux_block_centering_time_moment hlt d hd D p hp
  refine ⟨κ, C, c, M, Ce, Cpe, Cv, Cpv, Cc, Cpc,
    hκ, hκhalf, hC, hc, hM, hCe, hCpe, hCv, hCpv, hCc, hCpc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hmoment⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i
  obtain ⟨hf, hb⟩ := hmoment t ht hρ hscale ht1 hζ ψ A B hψ hψc hA hB hs hv hdψ i
  refine ⟨hf, hb.trans ?_⟩
  have he := (hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    (C * r) z hscale).2
  have hu := (hvalue Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht (C * r) z hscale).2
  have hc' := hcenter Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  gcongr


/-- Split an actual block moment into its good-event moment and a
probability-weighted higher moment on the complement. -/
theorem c14_flux_block_event_split {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (f : Ω → ℂ) (p : ℝ) (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal (2 * p)) μ) :
    MemLp f (ENNReal.ofReal p) μ ∧
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (E.indicator f) (ENNReal.ofReal p) μ).toReal +
        (μ Eᶜ).toReal ^ (1 / (2 * p)) *
          (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal := by
  have hp0 : 0 < p := by linarith
  have h2p : 0 < 2 * p := by positivity
  have hpq : ENNReal.ofReal p ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hfp := hf.mono_exponent hpq
  have hgood := hfp.indicator hE
  have hbad := hfp.indicator hE.compl
  have hexp : 1 / p - 1 / (2 * p) = 1 / (2 * p) := by
    field_simp [hp0.ne'] <;> ring
  have hbound := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
    (μ := μ.restrict Eᶜ) hf.aestronglyMeasurable.restrict
  rw [ENNReal.toReal_ofReal hp0.le, ENNReal.toReal_ofReal h2p.le, hexp,
    Measure.restrict_apply_univ] at hbound
  have hle : eLpNorm (Eᶜ.indicator f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal (2 * p)) μ * (μ Eᶜ) ^ (1 / (2 * p)) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hE.compl]
    refine hbound.trans ?_
    gcongr
    exact Measure.restrict_le_self
  have hfin : eLpNorm f (ENNReal.ofReal (2 * p)) μ *
      (μ Eᶜ) ^ (1 / (2 * p)) ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by positivity) (measure_ne_top _ _))
  have hreal := ENNReal.toReal_mono hfin hle
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at hreal
  have heq : E.indicator f + Eᶜ.indicator f = f := by
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have htri := eLpNorm_add_le (f := E.indicator f) (g := Eᶜ.indicator f) (μ := μ) hp1
  rw [heq] at htri
  have htri' := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hgood.eLpNorm_ne_top, hbad.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hgood.eLpNorm_ne_top hbad.eLpNorm_ne_top] at htri'
  refine ⟨hfp, ?_⟩
  nlinarith [htri', hreal]

/-- Apply a stretched-exponential tail to the complementary block moment. -/
theorem c14_flux_block_event_split_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (f : Ω → ℂ) (p : ℝ) (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal (2 * p)) μ)
    (A b α r : ℝ) (hA : 0 ≤ A)
    (htail : (μ Eᶜ).toReal ≤ A * Real.exp (-b * r ^ α)) :
    MemLp f (ENNReal.ofReal p) μ ∧
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (E.indicator f) (ENNReal.ofReal p) μ).toReal +
        A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
          (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal := by
  have hp0 : 0 < p := by linarith
  have hpow := Real.rpow_le_rpow ENNReal.toReal_nonneg htail
    (show 0 ≤ 1 / (2 * p) by positivity)
  have hfactor : (A * Real.exp (-b * r ^ α)) ^ (1 / (2 * p)) =
      A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) := by
    rw [Real.mul_rpow hA (Real.exp_pos _).le, ← Real.exp_mul]
    congr 2
    ring
  rw [hfactor] at hpow
  obtain ⟨hm, hbound⟩ := c14_flux_block_event_split μ E hE f p hp hf
  refine ⟨hm, hbound.trans ?_⟩
  exact add_le_add_right (mul_le_mul_of_nonneg_right hpow ENNReal.toReal_nonneg) _

/-- The event split accepts the measure-valued tail supplied by the selected event. -/
theorem c14_flux_block_event_split_ennreal_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E)
    (f : Ω → ℂ) (p : ℝ) (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal (2 * p)) μ)
    (A b α r : ℝ) (hA : 0 ≤ A)
    (htail : μ Eᶜ ≤ ENNReal.ofReal (A * Real.exp (-b * r ^ α))) :
    MemLp f (ENNReal.ofReal p) μ ∧
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (E.indicator f) (ENNReal.ofReal p) μ).toReal +
        A ^ (1 / (2 * p)) * Real.exp (-b * r ^ α / (2 * p)) *
          (eLpNorm f (ENNReal.ofReal (2 * p)) μ).toReal := by
  apply c14_flux_block_event_split_tail μ E hE f p hp hf A b α r hA
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail
  rwa [ENNReal.toReal_ofReal (mul_nonneg hA (Real.exp_pos _).le)] at h


/-- The selected structural constants can be fixed before choosing the moment exponent. -/
theorem c14_flux_block_selected_good_event_moment_uniform
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ κ C c M : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (p : ℝ), 2 ≤ p →
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          (eLpNorm energy (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          (eLpNorm value (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * ‖center‖)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_bound hsp d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro p hp
  obtain ⟨C₁, C₂, hC₁, hC₂, hlocal⟩ :=
    carverS_flux_block_local_time_on_flux_witness hlt d hd D p hp
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hpoint⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i hf
  have henergy := (hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    (C * r) z hscale).1
  have hU := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t
  have hvalue := (carverS_flux_block_local_value_moment Q
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) p hp hU (C * r) hρ z).1
  have hψcont := hψ.continuous
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hH : 0 ≤ C * r ^ (1 - κ) := mul_nonneg (by linarith) (Real.rpow_nonneg (by linarith) _)
  apply c14_flux_block_identity_good_event_moment Q t (C * r) hρ z (G t)
    (deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ))
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (J t i) ζ
    (ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q)
    M (C * r ^ (1 - κ)) A B (by linarith) hH hA hB ψ hψint hψcont E hE
    (ENNReal.ofReal p) hp' hf henergy hvalue
  filter_upwards [hpoint t ht hρ] with ω hω hωE
  exact hω hωE ψ A B hψ hψc hA hB hs hv hdψ i



/-- Crude energy preserves the uniform structural choice. -/
theorem c14_flux_block_selected_good_event_moment_of_crude_uniform
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ κ C c M : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (p : ℝ), 2 ≤ p →
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          (eLpNorm energy (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          (eLpNorm value (ENNReal.ofReal p) (reducedLaw Q)).toReal +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * ‖center‖)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_moment_uniform hsp hlt d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hmoment⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i
  have hψcont := hψ.continuous
  have hψint : Integrable ψ := hψcont.integrable_of_hasCompactSupport hψc
  have hf := c14_flux_block_actual_witness_memLp hlt hcr d hd D Q hQ β a μ hβ ha hμ ζ hζ
    P Pdag hP hPdag ν t ht1 (G t) (J t) (hflux t ht) p hp ψ hψint hψcont i
  exact ⟨hf, hmoment t ht hρ hscale ψ A B hψ hψc hA hB hs hv hdψ i hf⟩


/-- Quantitative moments with structural constants chosen before the exponent. -/
theorem c14_flux_block_selected_good_event_quantitative_uniform_p
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ κ C c M : ℝ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (p : ℝ), 2 ≤ p → ∃ Ce Cpe Cv Cpv Cc Cpc : ℝ,
      1 ≤ Ce ∧ 0 < Cpe ∧ 1 ≤ Cv ∧ 0 < Cpv ∧ 1 ≤ Cc ∧ 0 < Cpc ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
        let energyBound := Ce * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Ce *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpe * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let valueBound := Cv * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cv *
          Real.exp (Cpv * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let centerBound := ‖ζ‖ * Cc * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cc *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpc * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          energyBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          valueBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * centerBound)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hselected⟩ :=
    c14_flux_block_selected_good_event_moment_of_crude_uniform hsp hlt hcr d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro p hp
  obtain ⟨Ce, Cpe, hCe, hCpe, hlocal⟩ :=
    carverS_flux_block_local_time_on_flux_witness hlt d hd D p hp
  obtain ⟨Cv, Cpv, hCv, hCpv, hvalue⟩ :=
    c14_flux_block_open_terminal_local_value_moment d hd D p hp
  obtain ⟨Cc, Cpc, hCc, hCpc, hcenter⟩ :=
    c6_flux_block_centering_time_moment hlt d hd D p hp
  refine ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc,
    hCe, hCpe, hCv, hCpv, hCc, hCpc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hgood⟩ := hselected p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro r hr z
  obtain ⟨E, hE, htail, hmoment⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ
  dsimp only
  intro ψ A B hψ hψc hA hB hs hv hdψ i
  obtain ⟨hf, hb⟩ := hmoment t ht hρ hscale ht1 hζ ψ A B hψ hψc hA hB hs hv hdψ i
  refine ⟨hf, hb.trans ?_⟩
  have he := (hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
    (C * r) z hscale).2
  have hu := (hvalue Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht (C * r) z hscale).2
  have hc' := hcenter Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  gcongr



/-- The force condition at large times gives the bounded-force hypothesis. -/
theorem c14_flux_force_le_one_of_scale (t η₀ : ℝ) (ζ : ℂ)
    (ht : 1 ≤ t) (hη : η₀ ≤ 1 / 2)
    (hforce : ‖ζ‖ * Real.sqrt t ≤ t ^ η₀) : ‖ζ‖ ≤ 1 := by
  have hpow : t ^ η₀ ≤ Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht hη
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
  nlinarith


/-- The mesoscopic radius dominates the diffusive scale at large times. -/
theorem c14_flux_mesoscopic_radius_scale (t η C : ℝ)
    (ht : 1 ≤ t) (hη : 0 ≤ η) (hC : 1 ≤ C) :
    1 ≤ t ^ (1 / 2 + η) ∧ Real.sqrt t ≤ C * t ^ (1 / 2 + η) := by
  have hr : 1 ≤ t ^ (1 / 2 + η) := Real.one_le_rpow ht (by linarith)
  have hscale : Real.sqrt t ≤ t ^ (1 / 2 + η) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht (by linarith)
  constructor
  · exact hr
  · nlinarith


/-- The paper's force exponent satisfies the hypotheses of tail absorption. -/
theorem c14_flux_block_force_exponent_bounds (d : ℕ) (hd : 2 ≤ d) (κ : ℝ)
    (hκ : 0 < κ) (hκhalf : κ < 1 / 2) :
    let η := κ / (16 * ((d : ℝ) + 2))
    let η₀ := η / 4
    0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 2 * η₀ < (d : ℝ) / 4 := by
  dsimp only
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : 1 ≤ 16 * ((d : ℝ) + 2) := by linarith
  have hη : 0 < κ / (16 * ((d : ℝ) + 2)) := by positivity
  have hηle : κ / (16 * ((d : ℝ) + 2)) ≤ κ := div_le_self hκ.le hden
  constructor
  · positivity
  constructor <;> nlinarith

/-- The force window implies the bounded-force hypothesis used by local estimates. -/
theorem c14_flux_block_force_window_bound (t η₀ : ℝ) (ζ : ℂ)
    (ht : 1 ≤ t) (hη : η₀ ≤ 1 / 2)
    (hforce : ‖ζ‖ * Real.sqrt t ≤ t ^ η₀) : ‖ζ‖ ≤ 4 := by
  have hsqrt : 1 ≤ Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    exact Real.one_le_rpow ht (by norm_num)
  have hpow : t ^ η₀ ≤ Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le ht hη
  have hz : ‖ζ‖ ≤ 1 := by
    nlinarith [norm_nonneg ζ]
  linarith

/-- Integrate a uniform test bound over its actual compact spatial support. -/
theorem c14_flux_block_integral_norm_of_support_bound {d : ℕ}
    (ψ : Vec d → ℂ) (z : Vec d) (ρ A : ℝ)
    (hint : Integrable ψ volume)
    (hsupp : Function.support ψ ⊆ {y : Vec d | euclideanNorm (y - z) ≤ ρ})
    (hbound : ∀ y, ‖ψ y‖ ≤ A) :
    (∫ y, ‖ψ y‖ ∂volume) ≤
      (volume {y : Vec d | euclideanNorm (y - z) ≤ ρ}).toReal * A := by
  let K : Set (Vec d) := {y | euclideanNorm (y - z) ≤ ρ}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z ρ
  have hfinite : volume K ≠ ⊤ := ne_of_lt hK.measure_lt_top
  have hcomp : Integrable (K.indicator (fun _ : Vec d => A)) volume :=
    (integrableOn_const hfinite).integrable_indicator hK.measurableSet
  calc
    _ ≤ ∫ y, K.indicator (fun _ : Vec d => A) y ∂volume := by
      apply integral_mono_ae hint.norm hcomp
      filter_upwards with y
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]
        exact hbound y
      · have hz : ψ y = 0 := Function.notMem_support.mp (fun h => hy (hsupp h))
        simp [Set.indicator_of_notMem hy, hz]
    _ = _ := by rw [integral_indicator_const A hK.measurableSet]; simp [K, smul_eq_mul, Measure.real_def]

/-- A Euclidean derivative bound controls each coordinate derivative. -/
theorem c14_flux_block_coordinate_derivative_bound {d : ℕ}
    (ψ : Vec d → ℂ) (B : ℝ)
    (hbound : ∀ y, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ≤ B) :
    ∀ y j, ‖fderiv ℝ ψ y (unitVector j)‖ ≤ B := by
  intro y j
  have h := Real.abs_le_sqrt (Finset.single_le_sum
    (fun k _ => sq_nonneg ‖fderiv ℝ ψ y (unitVector k)‖) (Finset.mem_univ j))
  rw [abs_of_nonneg (norm_nonneg _)] at h
  exact h.trans (hbound y)

/-- The global Gaussian estimates and the integral bound share one envelope. -/
theorem c14_flux_block_gaussian_test_bounds (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (hr : 0 < r) (s : ℝ) (hs : 0 < s) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z : Vec d),
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      let A := Cder k * s ^ (-(k : ℝ) / 2) * W
      let B := Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
        Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      (∀ y, ‖ψ y‖ ≤ A) ∧ (∀ y j, ‖fderiv ℝ ψ y (unitVector j)‖ ≤ B) ∧
      (∫ y, ‖ψ y‖ ∂volume) ≤
        (volume {y : Vec d | euclideanNorm (y - z) ≤ R * r}).toReal * A := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ :=
    c28_flux_cutoff_kernel_global_euclidean_derivative_bound d D
  refine ⟨Cenv, Cder, henv, hder, ?_⟩
  intro Q i r hr s hs χ hχ hc R hsupp habs hgrad k dirs x z ψ W A B
  have hregular := c28_flux_cutoff_kernel_tsupport Q i r s hr hs χ hχ hc hsupp k dirs x z
  have hval : ∀ y, ‖ψ y‖ ≤ A := fun y =>
    (hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y).1
  have hgrad' : ∀ y, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ≤ B :=
    fun y => (hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y).2
  have hclosed := c14_flux_block_cutoff_closed_support χ
    (fun y => iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) y
      (fun j => unitVector (dirs j))) x z R r hsupp
  have hint : Integrable ψ volume := hregular.1.continuous.integrable_of_hasCompactSupport hregular.2.1
  exact ⟨hregular.1, hregular.2.1, hval,
    c14_flux_block_coordinate_derivative_bound ψ B hgrad',
    c14_flux_block_integral_norm_of_support_bound ψ z (R * r) A hint
      (fun y hy => hclosed (subset_tsupport ψ hy)) hval⟩

/-- Combine moments of the two restrictions of the same block. -/
theorem c14_flux_block_event_split_restricted {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (E : Set Ω) (hE : MeasurableSet E)
    (f : Ω → ℂ) (p : ℝ) (hp : 1 ≤ p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ≤
      (eLpNorm (E.indicator f) (ENNReal.ofReal p) μ).toReal +
        (eLpNorm (Eᶜ.indicator f) (ENNReal.ofReal p) μ).toReal := by
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hgood := hf.indicator hE
  have hbad := hf.indicator hE.compl
  have heq : E.indicator f + Eᶜ.indicator f = f := by
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have htri := eLpNorm_add_le (f := E.indicator f) (g := Eᶜ.indicator f) (μ := μ) hp1
  rw [heq] at htri
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hgood.eLpNorm_ne_top, hbad.eLpNorm_ne_top⟩) htri
  rwa [ENNReal.toReal_add hgood.eLpNorm_ne_top hbad.eLpNorm_ne_top] at hreal

/-- One additional Gaussian derivative contributes one inverse spatial scale. -/
theorem c14_flux_block_gaussian_next_derivative_scale (s : ℝ) (hs : 0 < s)
    (k : ℕ) :
    s ^ (-((k + 1 : ℕ) : ℝ) / 2) =
      s ^ (-(k : ℝ) / 2) * (Real.sqrt s)⁻¹ := by
  have hexp : -((k + 1 : ℕ) : ℝ) / 2 =
      -(k : ℝ) / 2 + -(1 / 2 : ℝ) := by push_cast; ring
  rw [hexp, Real.rpow_add hs, Real.rpow_neg hs.le (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]

/-- Combine the cutoff and Gaussian derivative terms at one spatial scale. -/
theorem c14_flux_block_gaussian_derivative_scale_bound
    (d k : ℕ) (D Dnext R r s W : ℝ)
    (hD : 0 ≤ D) (hDnext : 0 ≤ Dnext) (hR : 0 ≤ R)
    (hr : 0 < r) (hs : 0 < s) (hW : 0 ≤ W) :
    Real.sqrt (d : ℝ) * (D * (R / r) * s ^ (-(k : ℝ) / 2) +
        Dnext * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W ≤
      Real.sqrt (d : ℝ) * (D + Dnext) * s ^ (-(k : ℝ) / 2) *
        (R / r + (Real.sqrt s)⁻¹) * W := by
  have hcoef : D * (R / r) + Dnext * (Real.sqrt s)⁻¹ ≤
      (D + Dnext) * (R / r + (Real.sqrt s)⁻¹) := by
    nlinarith [mul_nonneg hD (inv_nonneg.mpr (Real.sqrt_nonneg s)),
      mul_nonneg hDnext (div_nonneg hR hr.le)]
  calc
    _ = Real.sqrt (d : ℝ) *
        (D * (R / r) + Dnext * (Real.sqrt s)⁻¹) *
          s ^ (-(k : ℝ) / 2) * W := by
      rw [c14_flux_block_gaussian_next_derivative_scale s hs k]
      ring
    _ ≤ Real.sqrt (d : ℝ) * ((D + Dnext) * (R / r + (Real.sqrt s)⁻¹)) *
        s ^ (-(k : ℝ) / 2) * W := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcoef (Real.sqrt_nonneg _))
        (Real.rpow_nonneg hs.le _)) hW
    _ = _ := by ring

/-- Use the prescribed force-window parameters in the tail and radius bounds. -/
theorem c14_flux_block_parameters_for_assembly
    (hparams : node_l_u3A_forced_u2D_flux_u23_parametersStmt)
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2) :
    ∃ η η₀ : ℝ, η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
      0 ≤ η ∧ 0 < η₀ ∧ η₀ ≤ 1 / 2 ∧ 2 * η₀ < (d : ℝ) / 4 ∧
      ∀ t : ℝ, 1 ≤ t →
        Real.sqrt t ≤ t ^ (1 / 2 + η) ∧
        ∀ ζ : ℂ, ‖ζ‖ * Real.sqrt t ≤ t ^ η₀ →
          ‖ζ‖ ^ 2 * t ≤ t ^ (2 * η₀) := by
  obtain ⟨η, η₀, hη, hη₀, hη₀pos, hlt, _hηhalf, hscale⟩ :=
    hparams d hd κ hκ hκhalf
  have hb := c14_flux_block_force_exponent_bounds d hd κ hκ hκhalf
  dsimp only at hb
  rw [← hη, ← hη₀] at hb
  exact ⟨η, η₀, hη, hη₀, le_of_lt (lt_trans hη₀pos hlt),
    hη₀pos, hb.2.1, hb.2.2, hscale⟩

/-- The Gaussian support volume fits the selected-event radius budget. -/
theorem c14_flux_block_integral_selected_radius (d : ℕ) :
    ∃ Cv : ℝ, 1 ≤ Cv ∧ ∀ (r r' : ℝ), 1 ≤ r → r ≤ r' →
      ∀ (z : Vec d) (ψ : Vec d → ℂ) (H : ℝ), 0 ≤ H →
        Integrable ψ volume →
        Function.support ψ ⊆ {y : Vec d | euclideanNorm (y - z) ≤
          (2 * Real.sqrt (d : ℝ) + 2) * r} →
        (∀ y, ‖ψ y‖ ≤ H) →
        (∫ y, ‖ψ y‖ ∂volume) ≤ H * (Cv * (1 + r') ^ d) := by
  obtain ⟨Cv, hCv, hvolume⟩ := c28_flux_gaussian_support_ball_volume d
  refine ⟨Cv, hCv, ?_⟩
  intro r r' hr hrr z ψ H hH hint hsupp hbound
  have hpow : r ^ d ≤ (1 + r') ^ d :=
    pow_le_pow_left₀ (by linarith) (by linarith) d
  calc
    _ ≤ (volume {y : Vec d | euclideanNorm (y - z) ≤
        (2 * Real.sqrt (d : ℝ) + 2) * r}).toReal * H :=
      c14_flux_block_integral_norm_of_support_bound ψ z _ H hint hsupp hbound
    _ ≤ (Cv * r ^ d) * H := mul_le_mul_of_nonneg_right (hvolume r hr z) hH
    _ ≤ H * (Cv * (1 + r') ^ d) := by
      nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg (by linarith : 0 ≤ Cv) hH)]


/-- At each positive time the endpoint gradient and flux are uniquely determined. -/
theorem c14_flux_block_selected_flux_unique {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (U : ℝ≥0 → Lp ℂ 2 (reducedLaw Q))
    (G J H K : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (h : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (U t) (G t) (J t))
    (h' : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (U t) (H t) (K t)) :
    ∀ t : ℝ≥0, 0 < (t : ℝ) → G t = H t ∧ J t = K t := by
  intro t ht
  exact carverS_endpoint_weak_flux_unique hd Q ν ζ a (U t)
    (G t) (J t) (H t) (K t) (h t ht) (h' t ht)

/-- Put three force-polynomial and exponential envelopes under one envelope. -/
theorem c14_flux_block_three_force_envelopes
    (c₁ c₂ c₃ a₁ a₂ a₃ b₁ b₂ b₃ : ℝ)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc₃ : 0 ≤ c₃)
    (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (ha₃ : 0 ≤ a₃)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hb₃ : 0 ≤ b₃) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 ≤ Cp ∧ ∀ x q : ℝ, 1 ≤ x → 0 ≤ q →
      c₁ * (x ^ a₁ * Real.exp (b₁ * q)) +
        c₂ * (x ^ a₂ * Real.exp (b₂ * q)) +
        c₃ * (x ^ a₃ * Real.exp (b₃ * q)) ≤
      C * (x ^ C * Real.exp (Cp * q)) := by
  let C := max 1 (max (a₁ + a₂ + a₃) (c₁ + c₂ + c₃))
  let Cp := b₁ + b₂ + b₃
  have hC : 1 ≤ C := le_max_left _ _
  have ha : a₁ + a₂ + a₃ ≤ C :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hc : c₁ + c₂ + c₃ ≤ C :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hCp : 0 ≤ Cp := by dsimp [Cp]; linarith
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro x q hx hq
  have hbound (a b : ℝ) (haC : a ≤ C) (hbCp : b ≤ Cp) :
      x ^ a * Real.exp (b * q) ≤ x ^ C * Real.exp (Cp * q) := by
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx haC)
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hbCp hq))
      (Real.exp_pos _).le (Real.rpow_nonneg (by linarith : 0 ≤ x) _)
  have h₁ := mul_le_mul_of_nonneg_left (hbound a₁ b₁ (by linarith) (by dsimp [Cp]; linarith)) hc₁
  have h₂ := mul_le_mul_of_nonneg_left (hbound a₂ b₂ (by linarith) (by dsimp [Cp]; linarith)) hc₂
  have h₃ := mul_le_mul_of_nonneg_left (hbound a₃ b₃ (by linarith) (by dsimp [Cp]; linarith)) hc₃
  have hnon : 0 ≤ x ^ C * Real.exp (Cp * q) := by positivity
  have hsum := mul_le_mul_of_nonneg_right hc hnon
  nlinarith

/-- Transfer the quantitative good-event estimate to any supplied weak flux. -/
theorem c14_flux_block_quantitative_for_supplied_flux
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ κ C c M : ℝ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ (p : ℝ), 2 ≤ p → ∃ Ce Cpe Cv Cpv Cc Cpc : ℝ,
      1 ≤ Ce ∧ 0 < Cpe ∧ 1 ≤ Cv ∧ 0 < Cpv ∧ 1 ≤ Cc ∧ 0 < Cpc ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
        let energyBound := Ce * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Ce *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpe * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let valueBound := Cv * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cv *
          Real.exp (Cpv * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let centerBound := ‖ζ‖ * Cc * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cc *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpc * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          energyBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          valueBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * centerBound)) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hsel⟩ :=
    c14_flux_block_selected_good_event_quantitative_uniform_p hsp hlt hcr d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro p hp
  obtain ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc, hCe, hCpe, hCv, hCpv, hCc, hCpc, hquant⟩ := hsel p hp
  refine ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc, hCe, hCpe, hCv, hCpv, hCc, hCpc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux
  obtain ⟨G', J', hflux', hgood⟩ := hquant Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  intro r hr z
  obtain ⟨E, hE, htail, hmoment⟩ := hgood r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ
  obtain ⟨hG, hJ⟩ := carverS_endpoint_weak_flux_unique hd Q ν ζ a
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t) (G' t) (J' t)
    (hflux t ht) (hflux' t ht)
  simpa only [hG, hJ] using hmoment t ht hρ hscale ht1 hζ

/-- Pair the supplied-flux good estimate with the actual bad-event decay. -/
theorem c14_flux_block_quantitative_and_bad_event_for_supplied_flux
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (A₀ m : ℝ) (hA₀ : 0 ≤ A₀) :
    ∃ κ C c M : ℝ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧ 1 ≤ M ∧
    ∀ η₀ : ℝ, 0 < η₀ → η₀ ≤ 1 / 2 → 2 * η₀ < (d : ℝ) / 4 →
    ∀ (p : ℝ), 2 ≤ p → ∃ Ce Cpe Cv Cpv Cc Cpc t₀ : ℝ,
      1 ≤ Ce ∧ 0 < Cpe ∧ 1 ≤ Cv ∧ 0 < Cpv ∧ 1 ≤ Cc ∧ 0 < Cpc ∧ 1 ≤ t₀ ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
      ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      ∃ E : Set (FieldPair d), MeasurableSet E ∧
        reducedLaw Q Eᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
      ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (hρ : 0 < C * r),
        Real.sqrt (t : ℝ) ≤ C * r → 1 ≤ (t : ℝ) → ‖ζ‖ ≤ 4 →
        t₀ ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        Real.sqrt (t : ℝ) ≤ r →
        let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
        let V := deriv (fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal) (t : ℝ)
        let center := ζ * ∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
        let ball := {x : Vec d | euclideanNorm (x - z) < C * r}
        let energy := localSpatialEnergy Q t (C * r) hρ z (G t) V
        let value := fun ω : FieldPair d => Real.sqrt ((volume ball).toReal⁻¹ *
          ∫ x in ball, ‖U (translate x ω)‖ ^ 2)
        let N := (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal
        let energyBound := Ce * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Ce *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpe * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let valueBound := Cv * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cv *
          Real.exp (Cpv * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        let centerBound := ‖ζ‖ * Cc * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ Cc *
          (t : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Cpc * ‖ζ‖ ^ 2 * (t : ℝ)) * N
        ∀ (ψ : Vec d → ℂ) (A B H : ℝ), 0 ≤ H →
          (∫ y : Vec d, ‖ψ y‖ ∂volume) ≤ H * (A₀ * (1 + r) ^ d) → ContDiff ℝ (⊤ : ℕ∞) ψ →
          HasCompactSupport ψ → 0 ≤ A → 0 ≤ B → tsupport ψ ⊆ ball →
          (∀ x, ‖ψ x‖ ≤ A) → (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        MemLp ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (E.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          (A * (2 / Real.sqrt (t : ℝ) + 2 * ‖ζ‖ * ((d : ℝ) * M)) +
            (d : ℝ) ^ 3 * (M + 1) * B + 2 * ‖ζ‖ * (d : ℝ) * A) *
          energyBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) *
          ((d : ℝ) ^ 3 * (M + 1) * B * (2 * ‖ζ‖)) *
          valueBound +
        (volume ball).toReal * (C * r ^ (1 - κ)) * (A * (2 * centerBound)) ∧
        MemLp (Eᶜ.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (Eᶜ.indicator ((∫ y : Vec d, ψ y • complexTranslation
          (reducedLaw Q) (reducedLaw_stationary Q) y (J t i) : Lp ℂ 2 (reducedLaw Q)) :
          FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ H * (t : ℝ) ^ (-m) := by
  obtain ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, hsel⟩ :=
    c14_flux_block_quantitative_for_supplied_flux hsp hlt hcr d hd D
  refine ⟨κ, C, c, M, hκ, hκhalf, hC, hc, hM, ?_⟩
  intro η₀ hη hηhalf hsmall p hp
  obtain ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc, hCe, hCpe, hCv, hCpv, hCc, hCpc, hquant⟩ := hsel p hp
  obtain ⟨t₀, ht₀, hbad⟩ := EinsteinFull.Calculus.c29_actual_flux_block_bad_event_polynomial_decay
    hlt hcr d hd D p A₀ C c η₀ m hp hA₀ hC hc hη hηhalf hsmall
  refine ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc, t₀, hCe, hCpe, hCv, hCpv, hCc, hCpc, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux r hr z
  obtain ⟨E, hE, htail, hgood⟩ := hquant Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux r hr z
  refine ⟨E, hE, htail, ?_⟩
  intro t ht hρ hscale ht1 hζ htlarge hforce hrtime
  dsimp only
  intro ψ A B H hH hint hψ hψc hA hB hs hv hdψ i
  obtain ⟨hmem, hgoodbound⟩ := hgood t ht hρ hscale ht1 hζ ψ A B hψ hψc hA hB hs hv hdψ i
  obtain ⟨hbadmem, hbadbound⟩ := hbad Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    G J hflux t htlarge hforce r hrtime H hH ψ hψ hψc hint i E hE htail
  exact ⟨hmem, hgoodbound, hbadmem, hbadbound⟩

/-- Combine the selected-ball volume and corrector-growth powers. -/
theorem c14_flux_block_volume_growth_power (d : ℕ) (κ r : ℝ) (hr : 0 < r) :
    r ^ d * r ^ (1 - κ) = r ^ ((d : ℝ) + 1 - κ) := by
  rw [← Real.rpow_natCast r d, ← Real.rpow_add hr]
  congr 1
  ring

/-- The selected-ball volume and growth factors fit the enlarged-radius budget. -/
theorem c14_flux_block_selected_volume_growth_le (d : ℕ) (κ r : ℝ) (hr : 0 < r) :
    r ^ d * ((2 * Real.sqrt (d : ℝ) + 3) * r) ^ (1 - κ) ≤
      ((2 * Real.sqrt (d : ℝ) + 3) * r) ^ ((d : ℝ) + 1 - κ) := by
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 3
  have hR : 1 ≤ R := by dsimp [R]; have := Real.sqrt_nonneg (d : ℝ); linarith
  have hRr : 0 < R * r := by positivity
  have hrr : r ≤ R * r := by nlinarith
  have hpow : r ^ d ≤ (R * r) ^ d := by gcongr
  calc
    _ ≤ (R * r) ^ d * (R * r) ^ (1 - κ) :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hRr.le _)
    _ = _ := c14_flux_block_volume_growth_power d κ (R * r) hRr

/-- Absorb the selected-ball volume and bad-event term into the final growth estimate. -/
theorem c14_flux_block_selected_volume_final_budget
    (d : ℕ) (κ C Cp : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    ∃ A growth₀ : ℝ, 1 ≤ A ∧ 0 < growth₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth → ∀ (t : ℝ≥0) (ζ : ℂ), 1 ≤ (t : ℝ) →
    ∀ H K : ℝ, 0 ≤ H → 1 ≤ K →
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 3
    H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) +
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (r ^ d * (R * r) ^ (1 - κ)) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) ≤
      A * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) := by
  obtain ⟨A, growth₀, hA, hg₀, hbudget⟩ :=
    c6_flux_selected_radius_final_budget d κ C Cp hκ hκhalf hC hCp
  refine ⟨A, growth₀, hA, hg₀, ?_⟩
  intro growth hgrowth t ζ ht H K hH hK η r R
  have htpos : 0 < (t : ℝ) := by linarith
  have hrpos : 0 < r := Real.rpow_pos_of_pos htpos _
  have hv := c14_flux_block_selected_volume_growth_le d κ r hrpos
  have hbudget' := hbudget growth hgrowth t ζ ht H K hH hK
  dsimp only at hbudget'
  have hfactor : 0 ≤ H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) := by
    have hK0 : 0 ≤ K := by linarith
    positivity
  have hrest : 0 ≤ (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
      Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by positivity
  have hcomp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hfactor) hrest
  dsimp [R] at *
  nlinarith [hcomp, hbudget']

/-- Assemble the actual flux block with the selected-ball volume bound. -/
theorem c14_actual_flux_block_selected_volume_event_assembly
    (d : ℕ) (κ C Cp : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    ∃ A growth₀ : ℝ, 1 ≤ A ∧ 0 < growth₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth → ∀ (t : ℝ≥0) (ζ : ℂ), 1 ≤ (t : ℝ) →
    ∀ (p : ℝ), 1 ≤ p → ∀ (Λ r₀ : ℝ) (Q : EnvironmentLaw d Λ r₀)
      (ψ : Vec d → ℂ) (J : Lp ℂ 2 (reducedLaw Q))
      (E : Set (FieldPair d)), MeasurableSet E →
    ∀ H K : ℝ, 0 ≤ H → 1 ≤ K →
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 3
    let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
      ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J
    MemLp (E.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) →
    (eLpNorm (E.indicator (B : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (r ^ d * (R * r) ^ (1 - κ)) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) →
    (eLpNorm (Eᶜ.indicator (B : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) →
    MemLp (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      A * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) := by
  obtain ⟨A, growth₀, hA, hg₀, hassemble⟩ :=
    c6_actual_flux_block_event_assembly d κ C Cp hκ hκhalf hC hCp
  refine ⟨A, growth₀, hA, hg₀, ?_⟩
  intro growth hgrowth t ζ ht p hp Λ r₀ Q ψ J E hE H K hH hK η r R B
  intro hgood hbad hgoodbound hbadbound
  have htpos : 0 < (t : ℝ) := by linarith
  have hrpos : 0 < r := Real.rpow_pos_of_pos htpos _
  have hv := c14_flux_block_selected_volume_growth_le d κ r hrpos
  have hfactor : 0 ≤ H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) := by
    have hK0 : 0 ≤ K := by linarith
    positivity
  have hrest : 0 ≤ (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
      Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by positivity
  have hcomp := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv hfactor) hrest
  have hgoodbound' : (eLpNorm (E.indicator (B : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (R * r) ^ ((d : ℝ) + 1 - κ) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by
    dsimp [R] at *
    nlinarith [hcomp, hgoodbound]
  exact hassemble growth hgrowth t ζ ht p hp Λ r₀ Q ψ J E hE H K hH hK
    hgood hbad hgoodbound' hbadbound

/-- Scalar prefactors in the three local good-event estimates share one bound. -/
theorem c14_flux_block_good_prefactor_bound
    (a b q z m n u v w : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hq : 0 ≤ q) (hz : 0 ≤ z)
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    (a * (2 * q + 2 * z * m) + n * b + 2 * z * a) * q * u +
      n * b * (2 * z) * v + a * (2 * z * q) * w ≤
    (4 + 2 * m + 2 * n) * (a * (q * q + z * q) + b * (q + z)) * (u + v + w) := by
  let L := 4 + 2 * m + 2 * n
  let P := a * (q * q + z * q) + b * (q + z)
  have h1 : (a * (2 * q + 2 * z * m) + n * b + 2 * z * a) * q ≤ L * P := by
    dsimp [L, P]
    nlinarith [mul_nonneg ha (mul_nonneg hq hq), mul_nonneg ha (mul_nonneg hz hq),
      mul_nonneg hb hq, mul_nonneg hb hz,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hm,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hn,
      mul_nonneg (mul_nonneg ha (mul_nonneg hz hq)) hn,
      mul_nonneg (mul_nonneg hb hq) hm, mul_nonneg (mul_nonneg hb hq) hn,
      mul_nonneg (mul_nonneg hb hz) hm, mul_nonneg (mul_nonneg hb hz) hn]
  have h2 : n * b * (2 * z) ≤ L * P := by
    dsimp [L, P]
    nlinarith [mul_nonneg ha (mul_nonneg hq hq), mul_nonneg ha (mul_nonneg hz hq),
      mul_nonneg hb hq, mul_nonneg hb hz,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hm,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hn,
      mul_nonneg (mul_nonneg ha (mul_nonneg hz hq)) hm,
      mul_nonneg (mul_nonneg ha (mul_nonneg hz hq)) hn,
      mul_nonneg (mul_nonneg hb hq) hm, mul_nonneg (mul_nonneg hb hq) hn,
      mul_nonneg (mul_nonneg hb hz) hm]
  have h3 : a * (2 * z * q) ≤ L * P := by
    dsimp [L, P]
    nlinarith [mul_nonneg ha (mul_nonneg hq hq), mul_nonneg ha (mul_nonneg hz hq),
      mul_nonneg hb hq, mul_nonneg hb hz,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hm,
      mul_nonneg (mul_nonneg ha (mul_nonneg hq hq)) hn,
      mul_nonneg (mul_nonneg ha (mul_nonneg hz hq)) hm,
      mul_nonneg (mul_nonneg ha (mul_nonneg hz hq)) hn,
      mul_nonneg (mul_nonneg hb hq) hm, mul_nonneg (mul_nonneg hb hq) hn,
      mul_nonneg (mul_nonneg hb hz) hm, mul_nonneg (mul_nonneg hb hz) hn]
  have h1' := mul_le_mul_of_nonneg_right h1 hu
  have h2' := mul_le_mul_of_nonneg_right h2 hv
  have h3' := mul_le_mul_of_nonneg_right h3 hw
  change _ ≤ L * P * (u + v + w)
  nlinarith [h1', h2', h3']

/-- Combine the three quantitative local envelopes into one force envelope. -/
theorem c14_flux_block_local_envelopes_bound
    (Ce Cpe Cv Cpv Cc Cpc : ℝ)
    (hCe : 0 ≤ Ce) (hCpe : 0 ≤ Cpe) (hCv : 0 ≤ Cv)
    (hCpv : 0 ≤ Cpv) (hCc : 0 ≤ Cc) (hCpc : 0 ≤ Cpc) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 ≤ Cp ∧
    ∀ A B q z m n x y N : ℝ, 0 ≤ A → 0 ≤ B → 0 ≤ q → 0 ≤ z →
      0 ≤ m → 0 ≤ n → 1 ≤ x → 0 ≤ y → 0 ≤ N →
      (A * (2 * q + 2 * z * m) + n * B + 2 * z * A) *
          (Ce * x ^ Ce * q * Real.exp (Cpe * y) * N) +
        (n * B * (2 * z)) * (Cv * x ^ Cv * Real.exp (Cpv * y) * N) +
        A * (2 * (z * Cc * x ^ Cc * q * Real.exp (Cpc * y) * N)) ≤
      (4 + 2 * m + 2 * n) * (A * (q*q + z*q) + B * (q+z)) *
        (C * (x ^ C * Real.exp (Cp * y))) * N := by
  obtain ⟨C, Cp, hC, hCp, henvelope⟩ :=
    c14_flux_block_three_force_envelopes Ce Cv Cc Ce Cv Cc Cpe Cpv Cpc
      hCe hCv hCc hCe hCv hCc hCpe hCpv hCpc
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro A B q z m n x y N hA hB hq hz hm hn hx hy hN
  have hx0 : 0 ≤ x := by linarith
  let u := Ce * (x ^ Ce * Real.exp (Cpe * y))
  let v := Cv * (x ^ Cv * Real.exp (Cpv * y))
  let w := Cc * (x ^ Cc * Real.exp (Cpc * y))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hfactor := c14_flux_block_good_prefactor_bound A B q z m n u v w
    hA hB hq hz hm hn hu hv hw
  have hforce : u + v + w ≤ C * (x ^ C * Real.exp (Cp * y)) :=
    henvelope x y hx hy
  have hfac : 0 ≤ (4 + 2 * m + 2 * n) * (A * (q*q + z*q) + B * (q+z)) := by positivity
  have h := mul_le_mul_of_nonneg_right
    (hfactor.trans (mul_le_mul_of_nonneg_left hforce hfac)) hN
  dsimp [u, v, w] at h
  convert h using 1 <;> ring

/-- Insert the Gaussian test bounds into the combined local force envelope. -/
theorem c14_flux_block_gaussian_local_envelopes_bound
    (d : ℕ) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (Ce Cpe Cv Cpv Cc Cpc : ℝ)
    (hCe : 0 ≤ Ce) (hCpe : 0 ≤ Cpe) (hCv : 0 ≤ Cv)
    (hCpv : 0 ≤ Cpv) (hCc : 0 ≤ Cc) (hCpc : 0 ≤ Cpc) :
    ∃ C Cp : ℝ, ∃ Dout : ℕ → ℝ, 1 ≤ C ∧ 0 ≤ Cp ∧ (∀ k, 1 ≤ Dout k) ∧
    ∀ (k : ℕ) (t s r W : ℝ) (ζ : ℂ) (m n x y N : ℝ),
      1 ≤ t → 1 ≤ s → 0 < r → 0 ≤ W → 0 ≤ m → 0 ≤ n →
      1 ≤ x → 0 ≤ y → 0 ≤ N →
      let q := (Real.sqrt t)⁻¹
      let A := D k * s ^ (-(k : ℝ) / 2) * W
      let B := Real.sqrt (d : ℝ) *
        (D k * ((2 * Real.sqrt (d : ℝ) + 2) / r) * s ^ (-(k : ℝ) / 2) +
          D (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
      (A * (2 * q + 2 * ‖ζ‖ * m) + n * B + 2 * ‖ζ‖ * A) *
          (Ce * x ^ Ce * q * Real.exp (Cpe * y) * N) +
        (n * B * (2 * ‖ζ‖)) * (Cv * x ^ Cv * Real.exp (Cpv * y) * N) +
        A * (2 * (‖ζ‖ * Cc * x ^ Cc * q * Real.exp (Cpc * y) * N)) ≤
      (4 + 2*m + 2*n) *
        (Dout k * s ^ (-(k : ℝ) / 2) * W *
          (t⁻¹ + ‖ζ‖ * q + (q + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹))) *
        (C * (x ^ C * Real.exp (Cp * y))) * N := by
  obtain ⟨C, Cp, hC, hCp, hlocal⟩ :=
    c14_flux_block_local_envelopes_bound Ce Cpe Cv Cpv Cc Cpc
      hCe hCpe hCv hCpv hCc hCpc
  obtain ⟨Dout, hDout, hgauss⟩ :=
    EinsteinFull.Calculus.c10_flux_gaussian_prefactor_normalization d D hD
  refine ⟨C, Cp, Dout, hC, hCp, hDout, ?_⟩
  intro k t s r W ζ m n x y N ht hs hr hW hm hn hx hy hN q A B
  have ht0 : 0 ≤ t := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hq : 0 ≤ q := inv_nonneg.mpr (Real.sqrt_nonneg t)
  have hDk := hD k
  have hDnext := hD (k + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hq2 : q*q = t⁻¹ := by
    dsimp [q]
    rw [← sq, inv_pow, Real.sq_sqrt ht0]
  have htest := hgauss k t s r W ζ ht hs hr hW
  dsimp only at htest
  have htest' : A * (q*q + ‖ζ‖*q) + B * (q + ‖ζ‖) ≤
      Dout k * s ^ (-(k : ℝ) / 2) * W *
        (t⁻¹ + ‖ζ‖*q + (q + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹)) := by
    rw [hq2]
    dsimp [A, B, q] at *
    convert htest using 1 <;> ring
  have h := hlocal A B q ‖ζ‖ m n x y N hA hB hq (norm_nonneg _) hm hn hx hy hN
  have hfac : 0 ≤ 4 + 2*m + 2*n := by positivity
  have henvelope : 0 ≤ C * (x ^ C * Real.exp (Cp*y)) := by
    have hx0 : 0 ≤ x := by linarith
    positivity
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htest' hfac) henvelope) hN)

/-- The Gaussian local envelopes and eighth-time endpoint bound have parabolic scale. -/
theorem c14_flux_block_gaussian_terminal_envelopes_bound
    (d : ℕ) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (Ce Cpe Cv Cpv Cc Cpc : ℝ)
    (hCe : 0 ≤ Ce) (hCpe : 0 ≤ Cpe) (hCv : 0 ≤ Cv)
    (hCpv : 0 ≤ Cpv) (hCc : 0 ≤ Cc) (hCpc : 0 ≤ Cpc) :
    ∃ C Cp Ct : ℝ, ∃ Dout : ℕ → ℝ,
      1 ≤ C ∧ 0 ≤ Cp ∧ 1 ≤ Ct ∧ (∀ k, 1 ≤ Dout k) ∧
    ∀ (k : ℕ) (t s η W : ℝ) (ζ : ℂ) (m n K growth N : ℝ),
      8 ≤ t → 1 ≤ s → 0 ≤ η → 0 ≤ W → 0 ≤ m → 0 ≤ n → 1 ≤ K → 0 ≤ N →
      N ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 8) *
        ((t/8) ^ (-(1/2 + (d : ℝ)/4)) + ‖ζ‖ * (t/8) ^ (-(d : ℝ)/4)) →
      let r := t ^ (1/2 + η)
      let q := (Real.sqrt t)⁻¹
      let x := 1 + ‖ζ‖ * Real.sqrt t
      let y := ‖ζ‖ ^ 2 * t
      let A := D k * s ^ (-(k : ℝ) / 2) * W
      let B := Real.sqrt (d : ℝ) *
        (D k * ((2 * Real.sqrt (d : ℝ) + 2) / r) * s ^ (-(k : ℝ) / 2) +
          D (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
      (A * (2*q + 2*‖ζ‖*m) + n*B + 2*‖ζ‖*A) *
          (Ce*x^Ce*q*Real.exp (Cpe*y)*N) +
        (n*B*(2*‖ζ‖)) * (Cv*x^Cv*Real.exp (Cpv*y)*N) +
        A * (2*(‖ζ‖*Cc*x^Cc*q*Real.exp (Cpc*y)*N)) ≤
      (4 + 2*m + 2*n) * Dout k * s ^ (-(k : ℝ) / 2) * W *
        (C * Ct) * K * t ^ (-1 - (1/2 + (d : ℝ)/4)) *
        x ^ (C + 2) * Real.exp (Cp*y) *
        Real.exp (growth * ‖ζ‖ ^ 2 * t / 8) * (1+t/s) := by
  obtain ⟨C, Cp, Dout, hC, hCp, hDout, hlocal⟩ :=
    c14_flux_block_gaussian_local_envelopes_bound d D hD Ce Cpe Cv Cpv Cc Cpc
      hCe hCpe hCv hCpv hCc hCpc
  obtain ⟨Ct, hCt, hterminal⟩ := EinsteinFull.Calculus.c34_flux_block_good_event_terminal_scale d
  refine ⟨C, Cp, Ct, Dout, hC, hCp, hCt, hDout, ?_⟩
  intro k t s η W ζ m n K growth N ht hs hη hW hm hn hK hN hNbound r q x y A B
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := by linarith
  have hr : 0 < r := Real.rpow_pos_of_pos htpos _
  have hx : 1 ≤ x := by
    dsimp [x]
    nlinarith [mul_nonneg (norm_nonneg ζ) (Real.sqrt_nonneg t)]
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hlocal' := hlocal k t s r W ζ m n x y N (by linarith) hs hr hW hm hn hx hy hN
  dsimp only at hlocal'
  have hscale := hterminal t s η ζ ht hs hη
  change (t⁻¹ + ‖ζ‖ * q + (q + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹)) *
      ((t/8) ^ (-(1/2 + (d : ℝ)/4)) + ‖ζ‖ * (t/8) ^ (-(d : ℝ)/4)) ≤
    Ct * t ^ (-1 - (1/2 + (d : ℝ)/4)) * x ^ (2 : ℕ) * (1+t/s) at hscale
  let P := t⁻¹ + ‖ζ‖ * q + (q + ‖ζ‖) * (r⁻¹ + (Real.sqrt s)⁻¹)
  let T := (t/8) ^ (-(1/2 + (d : ℝ)/4)) + ‖ζ‖ * (t/8) ^ (-(d : ℝ)/4)
  let F := (4 + 2*m + 2*n) * (Dout k * s ^ (-(k : ℝ)/2) * W) *
    (C * (x ^ C * Real.exp (Cp*y)))
  have hDk : 0 ≤ Dout k := by have := hDout k; linarith
  have hC0 : 0 ≤ C := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hP : 0 ≤ P := by dsimp [P, q, r]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hEt : 0 ≤ K * Real.exp (growth * ‖ζ‖^2*t/8) := by positivity
  have h1 := mul_le_mul_of_nonneg_left hNbound (mul_nonneg hF hP)
  have h2 := mul_le_mul_of_nonneg_left hscale (mul_nonneg hF hEt)
  have hpow : x ^ C * x ^ (2 : ℕ) = x ^ (C+2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith : 0 < x)]
    norm_num
  calc
    _ ≤ F * P * N := by convert hlocal' using 1 <;> dsimp [F, P] <;> ring
    _ ≤ F * P * (K * Real.exp (growth * ‖ζ‖^2*t/8) * T) := h1
    _ = (F * (K * Real.exp (growth * ‖ζ‖^2*t/8))) * (P*T) := by ring
    _ ≤ (F * (K * Real.exp (growth * ‖ζ‖^2*t/8))) *
        (Ct * t ^ (-1 - (1/2 + (d : ℝ)/4)) * x ^ (2 : ℕ) * (1+t/s)) := h2
    _ = _ := by dsimp [F]; rw [← hpow]; ring

/-- Insert the selected-ball volume into the Gaussian terminal estimate. -/
theorem c14_flux_block_selected_ball_terminal_bound
    (d : ℕ) (D : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (C₀ κ M Ce Cpe Cv Cpv Cc Cpc : ℝ)
    (hC₀ : 1 ≤ C₀) (hM : 1 ≤ M)
    (hCe : 0 ≤ Ce) (hCpe : 0 ≤ Cpe) (hCv : 0 ≤ Cv)
    (hCpv : 0 ≤ Cpv) (hCc : 0 ≤ Cc) (hCpc : 0 ≤ Cpc) :
    ∃ C Cp Ct V : ℝ, ∃ Dout : ℕ → ℝ,
      1 ≤ C ∧ 0 ≤ Cp ∧ 1 ≤ Ct ∧ 1 ≤ V ∧ (∀ k, 1 ≤ Dout k) ∧
    ∀ (k : ℕ) (t s η W : ℝ) (ζ : ℂ) (K growth N : ℝ) (z : Vec d),
      8 ≤ t → 1 ≤ s → 0 ≤ η → 0 ≤ W → 1 ≤ K → 0 ≤ N →
      N ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * t / 8) *
        ((t/8) ^ (-(1/2 + (d : ℝ)/4)) + ‖ζ‖ * (t/8) ^ (-(d : ℝ)/4)) →
      let r := t ^ (1/2 + η)
      let r' := (2 * Real.sqrt (d : ℝ) + 3) * r
      let q := (Real.sqrt t)⁻¹
      let x := 1 + ‖ζ‖ * Real.sqrt t
      let y := ‖ζ‖ ^ 2 * t
      let A := D k * s ^ (-(k : ℝ) / 2) * W
      let B := Real.sqrt (d : ℝ) *
        (D k * ((2 * Real.sqrt (d : ℝ) + 2) / r) * s ^ (-(k : ℝ) / 2) +
          D (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
      let energy := Ce*x^Ce*q*Real.exp (Cpe*y)*N
      let value := Cv*x^Cv*Real.exp (Cpv*y)*N
      let center := ‖ζ‖*Cc*x^Cc*q*Real.exp (Cpc*y)*N
      let vol := (volume {v : Vec d | euclideanNorm (v-z) < C₀*r'}).toReal
      vol * (C₀*r'^(1-κ)) *
        ((A*(2*q + 2*‖ζ‖*((d : ℝ)*M)) + (d : ℝ)^3*(M+1)*B +
          2*‖ζ‖*(d : ℝ)*A)*energy +
        ((d : ℝ)^3*(M+1)*B*(2*‖ζ‖))*value + A*(2*center)) ≤
      V*r^d * (C₀*r'^(1-κ)) *
        (4 + 2*((d : ℝ)*M+(d : ℝ)) + 2*((d : ℝ)^3*(M+1))) *
        Dout k * s ^ (-(k : ℝ)/2) * W * (C*Ct) * K *
        t ^ (-1-(1/2+(d : ℝ)/4)) * x^(C+2) * Real.exp (Cp*y) *
        Real.exp (growth*‖ζ‖^2*t/8) * (1+t/s) := by
  obtain ⟨C, Cp, Ct, Dout, hC, hCp, hCt, hDout, hterminal⟩ :=
    c14_flux_block_gaussian_terminal_envelopes_bound d D hD Ce Cpe Cv Cpv Cc Cpc
      hCe hCpe hCv hCpv hCc hCpc
  obtain ⟨V, hV, hvolume⟩ := c28_flux_selected_good_ball_volume d C₀ hC₀
  refine ⟨C, Cp, Ct, V, Dout, hC, hCp, hCt, hV, hDout, ?_⟩
  intro k t s η W ζ K growth N z ht hs hη hW hK hN hNbound r r' q x y A B energy value center vol
  have htpos : 0 < t := by linarith
  have hspos : 0 < s := by linarith
  have hr : 1 ≤ r := Real.one_le_rpow (by linarith : 1 ≤ t) (by linarith : 0 ≤ 1/2+η)
  have hrpos : 0 < r := by linarith
  have hR : 0 ≤ 2 * Real.sqrt (d : ℝ) + 3 := by positivity
  have hr' : 0 ≤ r' := by dsimp [r']; positivity
  have hd : 0 ≤ (d : ℝ) := by positivity
  have hM0 : 0 ≤ M := by linarith
  have hm : 0 ≤ (d : ℝ)*M+(d : ℝ) := by positivity
  have hn : 0 ≤ (d : ℝ)^3*(M+1) := by positivity
  have hDk := hD k
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have henergy : 0 ≤ energy := by dsimp [energy, x, q]; positivity
  have hcoef : A*(2*q + 2*‖ζ‖*((d : ℝ)*M)) + (d : ℝ)^3*(M+1)*B +
      2*‖ζ‖*(d : ℝ)*A ≤
      A*(2*q + 2*‖ζ‖*((d : ℝ)*M+(d : ℝ))) + (d : ℝ)^3*(M+1)*B +
      2*‖ζ‖*A := by nlinarith [mul_nonneg hA (norm_nonneg ζ)]
  have hcoef' := mul_le_mul_of_nonneg_right hcoef henergy
  have hterm := hterminal k t s η W ζ ((d : ℝ)*M+(d : ℝ))
    ((d : ℝ)^3*(M+1)) K growth N ht hs hη hW hm hn hK hN hNbound
  dsimp only at hterm
  have hcore :
      ((A*(2*q + 2*‖ζ‖*((d : ℝ)*M)) + (d : ℝ)^3*(M+1)*B +
          2*‖ζ‖*(d : ℝ)*A)*energy +
        ((d : ℝ)^3*(M+1)*B*(2*‖ζ‖))*value + A*(2*center)) ≤
      (4 + 2*((d : ℝ)*M+(d : ℝ)) + 2*((d : ℝ)^3*(M+1))) *
        Dout k * s ^ (-(k : ℝ)/2) * W * (C*Ct) * K *
        t ^ (-1-(1/2+(d : ℝ)/4)) * x^(C+2) * Real.exp (Cp*y) *
        Real.exp (growth*‖ζ‖^2*t/8) * (1+t/s) := by
    apply le_trans _ hterm
    dsimp [energy, value, center] at *
    nlinarith [hcoef']
  have hvol : vol ≤ V*r^d := by
    have heq : 2 * Real.sqrt (d : ℝ) + 3 =
        (2 * Real.sqrt (d : ℝ) + 2) + 1 := by ring
    simpa [vol, r', heq] using hvolume r hr z
  have hscale : 0 ≤ C₀*r'^(1-κ) := by positivity
  have hcore0 : 0 ≤ (A*(2*q + 2*‖ζ‖*((d : ℝ)*M)) + (d : ℝ)^3*(M+1)*B +
      2*‖ζ‖*(d : ℝ)*A)*energy +
      ((d : ℝ)^3*(M+1)*B*(2*‖ζ‖))*value + A*(2*center) := by
    have hDnext := hD (k+1)
    dsimp [A, B, energy, value, center, q, x, y] at *
    positivity
  have hv0 : 0 ≤ V*r^d := by
    have hV0 : 0 ≤ V := by linarith
    positivity
  have hh := mul_le_mul hvol (mul_le_mul_of_nonneg_left hcore hscale)
    (mul_nonneg hscale hcore0) hv0
  convert hh using 1 <;> ring

/-- One derivative coefficient dominates the good and bad event prefactors. -/
theorem c14_flux_block_common_event_coefficient
    (d : ℕ) (D Dout : ℕ → ℝ) (hD : ∀ k, 0 ≤ D k)
    (hDout : ∀ k, 0 ≤ Dout k) (C₀ M V C Ct : ℝ)
    (hC₀ : 0 ≤ C₀) (hM : 1 ≤ M) (hV : 0 ≤ V) (hC : 0 ≤ C)
    (hCt : 0 ≤ Ct) :
    ∃ Cder : ℕ → ℝ, (∀ k, 1 ≤ Cder k) ∧
    ∀ (k : ℕ) (s t W : ℝ), 1 ≤ s → 0 ≤ t → 0 ≤ W →
      D k * s ^ (-(k : ℝ) / 2) * W ≤
        Cder k * s ^ (-(k : ℝ) / 2) * W * (1 + t / s) ∧
      (V*C₀*(4 + 2*((d : ℝ)*M+(d : ℝ)) + 2*((d : ℝ)^3*(M+1))) *
        Dout k * (C*Ct)) * s ^ (-(k : ℝ) / 2) * W * (1 + t/s) ≤
        Cder k * s ^ (-(k : ℝ) / 2) * W * (1 + t/s) := by
  let F : ℝ := V*C₀*(4 + 2*((d : ℝ)*M+(d : ℝ)) + 2*((d : ℝ)^3*(M+1))) * (C*Ct)
  have hM0 : 0 ≤ M := by linarith
  have hF : 0 ≤ F := by dsimp [F]; positivity
  let Cder : ℕ → ℝ := fun k => 1 + D k + F * Dout k
  have hder (k : ℕ) : 1 ≤ Cder k := by
    dsimp [Cder]
    have := hD k
    have := mul_nonneg hF (hDout k)
    linarith
  refine ⟨Cder, hder, ?_⟩
  intro k s t W hs ht hW
  have hs0 : 0 ≤ s := by linarith
  have hpow : 0 ≤ s ^ (-(k : ℝ) / 2) := Real.rpow_nonneg hs0 _
  have hscale : 1 ≤ 1 + t / s := by
    have := div_nonneg ht hs0
    linarith
  have hbase : 0 ≤ s ^ (-(k : ℝ) / 2) * W := mul_nonneg hpow hW
  have hDle : D k ≤ Cder k := by
    dsimp [Cder]
    have := mul_nonneg hF (hDout k)
    linarith
  have hFle : F * Dout k ≤ Cder k := by
    dsimp [Cder]
    have := hD k
    linarith
  have h1 := mul_le_mul_of_nonneg_right hDle hbase
  have h2 := mul_le_mul_of_nonneg_right hFle (mul_nonneg hbase (by linarith : 0 ≤ 1 + t/s))
  have h3 := mul_nonneg (mul_nonneg (hD k) hbase) (by linarith : 0 ≤ t/s)
  constructor
  · nlinarith
  · dsimp [F] at h2
    nlinarith [h2]

/-- Gaussian tests fit the selected-event ball and its bad-event integral budget. -/
theorem c14_flux_block_gaussian_test_selected_ball (d : ℕ) (D : StructuralData d) :
    ∃ Cenv Cv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ 1 ≤ Cv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (hr : 1 ≤ r) (C : ℝ) (hC : 1 ≤ C) (s : ℝ) (hs : 0 < s)
      (χ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z : Vec d),
      let r' := (R + 1) * r
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      let A := Cder k * s ^ (-(k : ℝ) / 2) * W
      let B := Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
        Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
      ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      0 ≤ A ∧ 0 ≤ B ∧ tsupport ψ ⊆ {y : Vec d | euclideanNorm (y-z) < C * r'} ∧
      (∀ y, ‖ψ y‖ ≤ A) ∧ (∀ y j, ‖fderiv ℝ ψ y (unitVector j)‖ ≤ B) ∧
      (∫ y, ‖ψ y‖ ∂volume) ≤ A * (Cv * (1 + r') ^ d) := by
  obtain ⟨Cenv, Cder, henv, hder, htest⟩ := c14_flux_block_gaussian_test_bounds d D
  obtain ⟨Cv, hCv, hvol⟩ := c14_flux_block_integral_selected_radius d
  refine ⟨Cenv, Cv, Cder, henv, hCv, hder, ?_⟩
  intro Q i r hr C hC s hs χ hχ hc R hsupp habs hgrad k dirs x z r' ψ W A B
  have hrpos : 0 < r := by linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hrr : r ≤ r' := by dsimp [r']; nlinarith [mul_nonneg hR hrpos.le]
  have hW : 0 ≤ W := (carverS_flux_block_gaussian_spatial_sup s hs Cenv x z (R*r)
    (mul_nonneg hR (le_of_lt hrpos))).2.1
  have hD (n : ℕ) : 0 ≤ Cder n := le_trans (by norm_num) (hder n)
  have hDk := hD k
  have hDnext := hD (k + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨hψ, hψc, hval, hgrad', _⟩ := htest Q i r hrpos s hs χ hχ hc hsupp habs hgrad k dirs x z
  have hclosed := c14_flux_block_cutoff_closed_support χ
    (fun y => iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) y
      (fun j => unitVector (dirs j))) x z R r hsupp
  have hball : tsupport ψ ⊆ {y : Vec d | euclideanNorm (y-z) < C * r'} := by
    intro y hy
    have hy' := hclosed hy
    have hlt : R * r < C * r' := by
      have hc : r' ≤ C * r' := by nlinarith [hrr]
      dsimp [r'] at *
      nlinarith
    exact lt_of_le_of_lt hy' hlt
  refine ⟨hψ, hψc, hA, hB, hball, hval, hgrad', ?_⟩
  apply hvol r r' hr hrr z ψ A hA
    (hψ.continuous.integrable_of_hasCompactSupport hψc)
  · exact fun y hy => hclosed (subset_tsupport ψ hy)
  · exact hval

/-- Assemble the flux-block estimate from its five graph dependencies. -/
theorem node_e_u3A_flux_u2D_block_of_deps
    (hidentity : node_e_u3A_flux_u2D_identityStmt)
    (hlt : node_e_u3A_local_u2D_timeStmt)
    (hparams : node_l_u3A_forced_u2D_flux_u23_parametersStmt)
    (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (hcr : node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt) :
    node_e_u3A_flux_u2D_blockStmt := by
  intro d hd D
  obtain ⟨Cenv, Cvtest, Dtest, hCenv, hCvtest, hDtest, htest⟩ :=
    c14_flux_block_gaussian_test_selected_ball d D
  let m : ℝ := 1 + (1 / 2 + (d : ℝ) / 4)
  obtain ⟨κ, C₀, c, M, hκ, hκhalf, hC₀, hc, hM, hquant⟩ :=
    c14_flux_block_quantitative_and_bad_event_for_supplied_flux hsp hlt hcr d hd D
      Cvtest m (by linarith)
  obtain ⟨η, η₀, hη, hη₀, hηnonneg, hη₀pos, hη₀half, hsmall, hscale⟩ :=
    c14_flux_block_parameters_for_assembly hparams d hd κ hκ hκhalf
  subst η
  let η : ℝ := κ / (16 * ((d : ℝ) + 2))
  have hη : η = κ / (16 * ((d : ℝ) + 2)) := rfl
  refine ⟨κ, η, η₀, Cenv, (fun _ => 1), hκ, hκhalf, hCenv, hη, hη₀, ?_⟩
  intro p hp
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨Ce, Cpe, Cv, Cpv, Cc, Cpc, tbad, hCe, hCpe, hCv, hCpv, hCc,
    hCpc, htbad, hevent⟩ := hquant η₀ hη₀pos hη₀half hsmall p hp
  have hDtest0 (k : ℕ) : 0 ≤ Dtest k := by have := hDtest k; linarith
  obtain ⟨C, Cp, Ct, V, Dout, hC, hCp, hCt, hV, hDout, hterminal⟩ :=
    c14_flux_block_selected_ball_terminal_bound d Dtest hDtest0 C₀ κ M
      Ce Cpe Cv Cpv Cc Cpc hC₀ hM (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith)
  have hDout0 (k : ℕ) : 0 ≤ Dout k := by have := hDout k; linarith
  obtain ⟨Ccommon, hCcommon, hcommon⟩ :=
    c14_flux_block_common_event_coefficient d Dtest Dout hDtest0 hDout0
      C₀ M V C Ct (by linarith) hM (by linarith) (by linarith) (by linarith)
  obtain ⟨A, growth₀, hA, hgrowth₀, hassemble⟩ :=
    c14_actual_flux_block_selected_volume_event_assembly d κ (C+2) Cp hκ hκhalf
      (by linarith) hCp
  refine ⟨growth₀, max 8 tbad, (fun k => A * Ccommon k), hgrowth₀, ?_, ?_, ?_⟩
  · exact le_trans (by norm_num : (1 : ℝ) ≤ 8) (le_max_left _ _)
  · intro k
    have := hCcommon k
    nlinarith
  · intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    obtain ⟨φ, S, hφ, hidentityQ⟩ := hidentity d hd D Q hQ
    obtain ⟨G, J, hflux, hweakIdentity⟩ :=
      hidentityQ hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    refine ⟨G, J, hflux, ?_⟩
    intro t htt hforce growth K hgrowth hK hterminalMem hterminalNorm
    intro s hs hspos k dirs r R kernel W χ hχ hχc hsupp habs hgrad B x z j
    have ht8 : 8 ≤ (t : ℝ) := le_trans (le_max_left _ _) htt
    have ht1 : 1 ≤ (t : ℝ) := by linarith
    have htpos : 0 < (t : ℝ) := by linarith
    have hr : 1 ≤ r := Real.one_le_rpow ht1 (by linarith : 0 ≤ 1/2+η)
    have hrpos : 0 < r := by linarith
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let r' : ℝ := (R+1)*r
    have hrr : r ≤ r' := by dsimp [r']; nlinarith [mul_nonneg hR hrpos.le]
    have hr' : 1 ≤ r' := le_trans hr hrr
    have hρ : 0 < C₀*r' := by
      have hC₀pos : 0 < C₀ := by linarith
      have hr'pos : 0 < r' := by linarith
      exact mul_pos hC₀pos hr'pos
    have hsqrt : Real.sqrt (t : ℝ) ≤ r := (hscale (t : ℝ) ht1).1
    have hsqrt' : Real.sqrt (t : ℝ) ≤ r' := hsqrt.trans hrr
    have hscale' : Real.sqrt (t : ℝ) ≤ C₀*r' := by nlinarith
    have htbad' : tbad ≤ (t : ℝ) := le_trans (le_max_right _ _) htt
    have hζ : ‖ζ‖ ≤ 4 := c14_flux_block_force_window_bound (t : ℝ) η₀ ζ ht1 hη₀half hforce
    have hW : 0 ≤ W x z := (carverS_flux_block_gaussian_spatial_sup s hspos Cenv x z
      (R*r) (mul_nonneg hR hrpos.le)).2.1
    let ψ : Vec d → ℂ := fun v => (χ (v-z) : ℂ) * kernel (x-v)
    let Dval : ℝ := Dtest k * s ^ (-(k : ℝ)/2) * W x z
    let Dgrad : ℝ := Real.sqrt (d : ℝ) *
      (Dtest k * (R/r) * s ^ (-(k : ℝ)/2) +
        Dtest (k+1) * s ^ (-((k+1 : ℕ) : ℝ)/2)) * W x z
    obtain ⟨hψ,hψc,hDval,hDgrad,hsupport,hval,hgradψ,hint⟩ :=
      htest Q ⟨0,by omega⟩ r hr C₀ hC₀ s hspos χ hχ hχc hsupp habs hgrad k dirs x z
    obtain ⟨E,hE,htail,he⟩ := hevent Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux r' hr' z
    obtain ⟨hmem,hgood,hbadmem,hbad⟩ := he t htpos hρ hscale' ht1 hζ htbad' hforce hsqrt'
      ψ Dval Dgrad Dval hDval hint hψ hψc hDval hDgrad hsupport hval hgradψ j
    have hq : (t : ℝ) ^ (-(1/2 : ℝ)) = (Real.sqrt (t : ℝ))⁻¹ := by
      rw [Real.rpow_neg (le_of_lt htpos), ← Real.sqrt_eq_rpow]
    have hterm := hterminal k (t : ℝ) s η (W x z) ζ K growth
      ((eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t/8) : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal) z ht8 hs hηnonneg hW hK
      ENNReal.toReal_nonneg hterminalNorm
    have hcoeff := hcommon k s (t : ℝ) (W x z) hs (le_of_lt htpos) hW
    let H : ℝ := Ccommon k * s ^ (-(k : ℝ)/2) * W x z * (1 + (t : ℝ)/s)
    have hH : 0 ≤ H := by
      have hCk : 0 ≤ Ccommon k := by have := hCcommon k; linarith
      have hts : 0 ≤ (t : ℝ)/s := div_nonneg (le_of_lt htpos) (le_of_lt hspos)
      dsimp [H]
      positivity
    have hgoodmem : MemLp (E.indicator (B x z j : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q) := hmem.indicator hE
    have hbadbound : (eLpNorm (Eᶜ.indicator (B x z j : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        H * (t : ℝ) ^ (-1 - (1/2 + (d : ℝ)/4)) := by
      have ht0 : 0 ≤ (t : ℝ) ^ (-1 - (1/2 + (d : ℝ)/4)) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hcoeff.1 ht0
      have hexp : -m = -1 - (1/2 + (d : ℝ)/4) := by dsimp [m]; ring
      rw [hexp] at hbad
      dsimp [Dval, H] at *
      exact le_trans hbad hmul
    have hr'eq : r' = (2 * Real.sqrt (d : ℝ) + 3) * r := by dsimp [r', R]; ring
    have hgoodbound : (eLpNorm (E.indicator (B x z j : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * K * (t : ℝ) ^ (-1 - (1/2 + (d : ℝ)/4)) *
        (r ^ d * ((2 * Real.sqrt (d : ℝ) + 3) * r) ^ (1 - κ)) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (C+2) *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) := by
      let F : ℝ := K * (t : ℝ) ^ (-1 - (1/2 + (d : ℝ)/4)) *
        (r ^ d * ((2 * Real.sqrt (d : ℝ) + 3) * r) ^ (1 - κ)) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (C+2) *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8)
      have hK0 : 0 ≤ K := by linarith
      have hF : 0 ≤ F := by dsimp [F]; positivity
      let Gcoef : ℝ := (V*C₀*(4 + 2*((d : ℝ)*M+(d : ℝ)) +
        2*((d : ℝ)^3*(M+1))) * Dout k * (C*Ct)) *
        s ^ (-(k : ℝ)/2) * W x z * (1 + (t : ℝ)/s)
      have hcombined : Gcoef * F ≤ H * F := mul_le_mul_of_nonneg_right hcoeff.2 hF
      dsimp only at hgood hterm
      rw [hr'eq, hq] at hgood
      simp only [div_eq_mul_inv, mul_assoc, ← mul_add] at hgood
      simp only [div_eq_mul_inv, mul_assoc] at hterm
      calc
        _ ≤ _ := hgood
        _ ≤ Gcoef * F := by
          convert hterm using 1 <;>
            dsimp only [Gcoef, F, Dval, Dgrad, R, r] <;>
            simp only [div_eq_mul_inv, mul_assoc] <;> first | rfl | ring
        _ ≤ H * F := hcombined
        _ = _ := by dsimp only [F]; ring
    have hresult := hassemble growth hgrowth t ζ ht1 p hp1
      D.ellipticity D.dependenceRange Q ψ (J t j) E hE H K hH hK
      hgoodmem hbadmem hgoodbound hbadbound
    refine ⟨hmem, ?_⟩
    convert hresult.2 using 1 <;> dsimp only [H] <;> ring

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.c14_flux_block_good_event_centered_l2
#print axioms EinsteinFull.Blueprint.c14_flux_block_cutoff_closed_support
#print axioms EinsteinFull.Blueprint.c14_flux_block_test_bounds_global
#print axioms EinsteinFull.Blueprint.c14_flux_block_good_event_identity_bound

#print axioms EinsteinFull.Blueprint.c14_flux_block_good_event_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_actual_good_event_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_affine_majorant_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_actual_good_event_affine_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_identity_good_event_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_open_terminal_local_value_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_bound

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_moment

#print axioms EinsteinFull.Blueprint.c14_flux_block_actual_witness_memLp

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_moment_of_crude

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_quantitative

#print axioms EinsteinFull.Blueprint.c14_flux_block_event_split
#print axioms EinsteinFull.Blueprint.c14_flux_block_event_split_tail
#print axioms EinsteinFull.Blueprint.c14_flux_block_event_split_ennreal_tail

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_moment_uniform

#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_moment_of_crude_uniform
#print axioms EinsteinFull.Blueprint.c14_flux_block_selected_good_event_quantitative_uniform_p

#print axioms EinsteinFull.Blueprint.c14_flux_force_le_one_of_scale

#print axioms EinsteinFull.Blueprint.c14_flux_mesoscopic_radius_scale
