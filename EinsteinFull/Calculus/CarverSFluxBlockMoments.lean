import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_identity
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Blueprint.G3.node_e_u3A_sublinear_u2D_pair
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_local_u23_crude_u2D_energy
import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_block
import EinsteinFull.Calculus.C2TestReplacementSupport
import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Calculus.K6KernelAverageLp
import EinsteinFull.Calculus.K8EndpointFluxMemLp
import EinsteinFull.Work.W3.ComplexGaussianProfileSupport
open MeasureTheory
open scoped NNReal ENNReal
open EinsteinRelation

namespace EinsteinFull.Blueprint

/-- The bracketed factor of the weak-flux formula is `L²`. -/
theorem memLp_endpointFluxShift {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (U : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (k : Fin d) :
    MemLp (fun ω => G k ω - match ν with
      | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω
      | _ => 0 : FieldPair d → ℂ) 2 (reducedLaw Q) := by
  refine (Lp.memLp (G k)).sub ?_
  rcases ν with i | b
  · exact MemLp.zero
  · cases b
    · exact MemLp.zero
    · simp only
      have := (Lp.memLp U).const_mul (2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ))
      simpa [mul_assoc] using this

/-- The literal weak-flux formula defines an `L²` element when the gradient and endpoint are
`L²`: the centered reduced coefficient is essentially bounded. -/
theorem exists_endpointFlux_lp {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ν : EndpointIndex d) (ζ : ℂ)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (ha : IsReducedCoefficientObservation Q a)
    (U : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    ∃ J : Fin d → Lp ℂ 2 (reducedLaw Q), ∀ j : Fin d,
      (J j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
        ∑ k : Fin d, (a j k ω - (homogenizedCoefficient Q j k : ℂ)) *
          (G k ω - match ν with
            | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω
            | _ => 0) := by
  have hmem : ∀ j : Fin d, MemLp (fun ω => ∑ k : Fin d,
      (a j k ω - (homogenizedCoefficient Q j k : ℂ)) *
        (G k ω - match ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω
          | _ => 0)) 2 (reducedLaw Q) := by
    intro j
    have hsum := memLp_finsetSum (Finset.univ : Finset (Fin d)) (p := 2) (μ := reducedLaw Q)
      (f := fun k ω => (a j k ω - (homogenizedCoefficient Q j k : ℂ)) *
        (G k ω - match ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω
          | _ => 0)) ?_
    · exact hsum
    intro k _
    refine (memLp_endpointFluxShift hd Q ν ζ U G k).of_le_mul (c := sourceReducedBound Λ₀
      + ‖(homogenizedCoefficient Q j k : ℂ)‖) ?_ ?_
    · exact (((Lp.memLp (a j k)).aestronglyMeasurable.sub
        aestronglyMeasurable_const).mul (memLp_endpointFluxShift hd Q ν ζ U G k).aestronglyMeasurable)
    · filter_upwards [EinsteinFull.Calculus.C2TestReplacement.ae_abs_reducedCoefficient_entry_le Q,
        ha j k] with ω hω hωa
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (norm_sub_le _ _).trans (add_le_add_left ?_ _)
      rw [hωa]
      simpa using hω j k
  exact ⟨fun j => (hmem j).toLp _, fun j => (hmem j).coeFn_toLp⟩

/-- The complex cutoff-kernel weight of the flux blocks is continuous and integrable. -/
theorem carverS_block_weight_continuous_integrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (k : ℕ)
    (dirs : Fin k → Fin d) (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (x z : Vec d) :
    Continuous (fun y : Vec d => ((χ (y - z) : ℝ) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) ∧
    Integrable (fun y : Vec d => ((χ (y - z) : ℝ) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) := by
  have hker : Continuous (fun y : Vec d => iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) y (fun j => unitVector (dirs j))) := by
    have h := (contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0
      ).continuous_iteratedFDeriv (m := k) (by exact_mod_cast le_top)
    exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vec d) ℂ
      (fun j => unitVector (dirs j))).continuous.comp h
  have hχt : HasCompactSupport (fun y : Vec d => ((χ (y - z) : ℝ) : ℂ)) :=
    (hχc.comp_homeomorph (Homeomorph.subRight z)).comp_left (g := Complex.ofReal) (by simp)
  have hcont : Continuous (fun y : Vec d => ((χ (y - z) : ℝ) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) := (Complex.continuous_ofReal.comp
    (hχ.continuous.comp (continuous_id.sub continuous_const))).mul
      (hker.comp (continuous_const.sub continuous_id))
  exact ⟨hcont, hcont.integrable_of_hasCompactSupport hχt.mul_right⟩

/-- Complex-valued kernel averages of the stationary translation action preserve `Lᵖ`. -/
theorem memLp_integral_cmul_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {p : ℝ} (hp : 1 ≤ p)
    (c : Vec d → ℂ) (hc : Integrable c) (hcc : Continuous c)
    (U : Lp ℂ 2 Q) (hU : MemLp (U : FieldPair d → ℂ) (ENNReal.ofReal p) Q) :
    MemLp ((∫ y : Vec d, c y • complexTranslation Q hQ y U : Lp ℂ 2 Q) : FieldPair d → ℂ)
      (ENNReal.ofReal p) Q := by
  have ht : Continuous fun y : Vec d => complexTranslation Q hQ y U :=
    (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
  have hint : ∀ r : Vec d → ℝ, Integrable r → Continuous r →
      Integrable (fun y => r y • complexTranslation Q hQ y U) := by
    intro r hr hrc
    refine (hr.norm.mul_const ‖U‖).mono' (hrc.smul ht).aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_complexTranslation]
  have hsplit : ∀ y, c y • complexTranslation Q hQ y U =
      (c y).re • complexTranslation Q hQ y U +
        Complex.I • ((c y).im • complexTranslation Q hQ y U) := by
    intro y
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, ← add_smul]
    congr 1
    apply Complex.ext <;> simp
  have hre := hint (fun y => (c y).re) hc.re (Complex.continuous_re.comp hcc)
  have him := hint (fun y => (c y).im) hc.im (Complex.continuous_im.comp hcc)
  simp_rw [hsplit]
  rw [integral_add hre (him.fun_smul Complex.I), integral_smul]
  have hA := (EinsteinFull.Calculus.K6.memLp_integral_smul_complexTranslation Q hQ hp
    (fun y => (c y).re) hc.re (Complex.continuous_re.comp hcc) U hU).1
  have hB := (EinsteinFull.Calculus.K6.memLp_integral_smul_complexTranslation Q hQ hp
    (fun y => (c y).im) hc.im (Complex.continuous_im.comp hcc) U hU).1
  refine MemLp.ae_eq (Lp.coeFn_add _ _).symm (hA.add ?_)
  exact MemLp.ae_eq (Lp.coeFn_smul _ _).symm (hB.const_smul _)

/-- F1 (CARVER-S plan e:flux-block): finite-`p` integrability of the actual cutoff blocks. -/
theorem carverS_flux_block_memLp :
    EinsteinFull.Blueprint.node_e_u3A_flux_u2D_identityStmt →
    EinsteinFull.Blueprint.node_e_u3A_local_u2D_timeStmt →
    EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_parametersStmt →
    EinsteinFull.Blueprint.node_e_u3A_sublinear_u2D_pairStmt →
    EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_crude_u2D_energyStmt →
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ,
      0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧
      η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧
    ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 1 ≤ Cder k) ∧
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
        (∀ t : ℝ≥0, 0 < (t : ℝ) →
          IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
            (G t) (J t)) ∧
        ∀ (t : ℝ≥0), t₀ ≤ (t : ℝ) →
        ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
        ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K →
        MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q) →
        (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
            (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
              ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) →

        ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s,
        ∀ (k : ℕ) (dirs : Fin k → Fin d),
          let r := (t : ℝ) ^ (1 / 2 + η)
          let R := 2 * Real.sqrt (d : ℝ) + 2
          let kernel := fun y : Vec d =>
            iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
              y (fun j => unitVector (dirs j))
          let W := fun (x z : Vec d) => sSup
            ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
              Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
                {y : Vec d | euclideanNorm (y - z) ≤ R * r})
          ∀ χ : Vec d → ℝ,
            ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
            Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
            (∀ y, |χ y| ≤ 1) →
            (∀ y, Real.sqrt (∑ j : Fin d,
              (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
          let B := fun (x z : Vec d) (j : Fin d) =>
            ∫ y : Vec d, (χ (y - z) * kernel (x - y)) •
              complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
          ∀ (x z : Vec d) (j : Fin d),
            MemLp (B x z j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
  intro _hid hlt _hpar _hsub hcr d hd D
  refine ⟨1 / 4, 1 / 4 / (16 * ((d : ℝ) + 2)), 1 / 4 / (16 * ((d : ℝ) + 2)) / 4, 1,
    fun _ => 0, by norm_num, by norm_num, le_rfl, rfl, rfl, ?_⟩
  intro p hp
  refine ⟨1, 1, fun _ => 1, one_pos, le_rfl, fun _ => le_rfl, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨C, Cp, hC, hCp, hloc⟩ := hlt d hd D 2 le_rfl
  obtain ⟨G, V, hGV, -⟩ := hloc Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hJ := fun t : ℝ≥0 => exists_endpointFlux_lp hd Q ν ζ a ha
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t)
  choose J hJ using hJ
  refine ⟨G, J, fun t ht => ⟨(hGV t ht).1, hJ t⟩, ?_⟩
  intro t ht₀ hζ growth K _ _ _ _ s hs hs' k dirs r R kernel _W χ hχ hχc hχs hχb hχg B x z j
  have ht1 : (1 : ℝ) ≤ (t : ℝ) := ht₀
  have ht0 : 0 < (t : ℝ) := by linarith
  have hη : 1 / 4 / (16 * ((d : ℝ) + 2)) / 4 ≤ (1 / 2 : ℝ) := by
    have h16 : 1 ≤ 16 * ((d : ℝ) + 2) := by
      have := (Nat.cast_nonneg d : (0 : ℝ) ≤ d); nlinarith
    calc 1 / 4 / (16 * ((d : ℝ) + 2)) / 4 ≤ 1 / 4 / 1 / 4 := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hζ1 : ‖ζ‖ ≤ 1 := by
    have hsq : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 ht0
    have h2 : (t : ℝ) ^ (1 / 4 / (16 * ((d : ℝ) + 2)) / 4) ≤ Real.sqrt (t : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le ht1 hη
    exact le_of_mul_le_mul_right (by linarith) hsq
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hmemJ : MemLp (J t j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) :=
    EinsteinFull.Calculus.K8.endpoint_flux_memLp_of_crude hlt hcr hd D Q hQ β a μ hβ ha hμ ζ
      (by linarith) P Pdag hP hPdag ν t ht1 (G t) (J t) ⟨(hGV t ht0).1, hJ t⟩ j
  have hw := carverS_block_weight_continuous_integrable Q ⟨0, by omega⟩ s hs' k dirs χ hχ hχc x z
  exact memLp_integral_cmul_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (by linarith) _ hw.2 hw.1 (J t j) hmemJ

end EinsteinFull.Blueprint
