import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_centered_u2D_source
import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.C1CrudeEnergyLargeTime
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Calculus.LocalEnergyDomainSupport
import EinsteinFull.Calculus.MigrationMeasurabilitySupport
import EinsteinFull.Calculus.C3AnalyticClockSupport
import EinsteinFull.Calculus.C3HolderAverageSupport
import EinsteinFull.Calculus.ComplexTransposeSpatialSupport
import EinsteinFull.Calculus.C6ShortTimeTransposeEndpointProjection
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/- SUPERVISOR EXACT TARGET (not a declaration or proof); replace with proved command.
theorem local_time_gradient_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (G t) (0))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal))
-/

/-- Every actual endpoint admits the common gradient and strong time derivative
required by the local-time bound. This assertion supplies regularity only. -/
theorem local_time_gradient_endpoint_witnesses
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
        HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
          (V t) (t : ℝ) := by
  classical
  obtain ⟨G, hG⟩ := crudeEnergy_endpoint_gradient hd Q hQ β a μ hβ ζ P Pdag hP hPdag ν
  have hder (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
      ∃ V, HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        V (t : ℝ) := by
    obtain ⟨_, _, V, _, hV, _⟩ := node_e_u3A_centered_u2D_equations_of_deps
      d hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht
    exact ⟨V, hV⟩
  let V := fun t : ℝ≥0 => if ht : 0 < (t : ℝ) then (hder t ht).choose else 0
  refine ⟨G, V, ?_⟩
  intro t ht
  have hg := hG t (NNReal.coe_pos.mp ht)
  refine ⟨?_, hg, ?_⟩
  · cases ν with
    | inl j => exact hg.centered
    | inr b =>
      cases b with
      | true => exact hg
      | false =>
        have he : centeredComplexLp Q (ζ • P t μ) = ζ • centeredComplexLp Q (P t μ) := by
          simpa only [centeredComplexLpCLM_apply] using (centeredComplexLpCLM Q).map_smul ζ (P t μ)
        simpa only [indexedEndpoint, clockEndpoint, uncenteredEndpoint, he] using hg.centered
  · dsimp only [V]
    rw [dite_eq_left ht]
    exact (hder t ht).choose_spec

/-- The lp-growth dependency propagates the actual bounded endpoint data to
all finite exponents under consideration, including at the earlier time t/8. -/
theorem local_time_gradient_endpoint_memLp
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (t : ℝ≥0) :
    MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
      (ENNReal.ofReal p) (reducedLaw Q) := by
  let := reducedLaw_probability Q
  obtain ⟨_, _, hgrowth⟩ := h1 d D.ellipticity D.dependenceRange p hd hp
  have hprop := (hgrowth Q ⟨0, by omega⟩ ζ P Pdag hP hPdag).1
  obtain ⟨K, _, hbounds⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨hβb, hab, hμb⟩ := hbounds Q hQ β a μ hβ ha hμ
  have hcenter (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (centeredComplexLp Q f) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hf.sub (memLp_const (∫ ω, f ω ∂reducedLaw Q))).ae_eq
      (coeFn_centeredComplexLp Q f).symm
  have hsmul (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (ζ • f : Lp ℂ 2 (reducedLaw Q)) (ENNReal.ofReal p) (reducedLaw Q) :=
    (hf.const_smul ζ).ae_eq (Lp.coeFn_smul ζ f).symm
  have hβp (j : Fin d) : MemLp (β j) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (β j)).aestronglyMeasurable K (hβb j)
  cases ν with
  | inl j =>
    have hap : MemLp (a ⟨0, by omega⟩ j) (ENNReal.ofReal p) (reducedLaw Q) :=
      MemLp.of_bound (Lp.memLp (a ⟨0, by omega⟩ j)).aestronglyMeasurable K
        (hab ⟨0, by omega⟩ j)
    have hf : MemLp (β j + ζ • a ⟨0, by omega⟩ j : Lp ℂ 2 (reducedLaw Q))
        (ENNReal.ofReal p) (reducedLaw Q) :=
      ((hβp j).add (hsmul _ hap)).ae_eq (Lp.coeFn_add _ _).symm
    exact hcenter _ (hprop t _ hf).1
  | inr b =>
    cases b with
    | true => exact (hprop t _ (hβp ⟨0, by omega⟩)).2.1
    | false =>
      have hμp : MemLp μ (ENNReal.ofReal p) (reducedLaw Q) :=
        MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable K hμb
      exact hsmul _ (hcenter _ (hprop t _ hμp).1)

/-- A fixed-time gradient cutoff estimate with the actual generator output.
The free scale permits balancing the two masses before the parabolic estimate. -/
theorem local_time_physical_cutoff_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      ∀ ε : ℝ, 0 < ε →
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
        (∫ x, φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) / (2 * ε) +
        (ε / 2) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) +
        (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) := by
  intro L
  filter_upwards [hfg.ae_physical_cutoff_energy hG,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g]
    with ω he hf hg
  intro φ hφ ε hε
  have hif := integrable_physical_compact_sq_norm hφ.2.1 (hf _ hφ.2.1)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hig := integrable_physical_compact_sq_norm hφ.2.1 (hg _ hφ.2.1)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  change Integrable (fun x => φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) volume at hif
  change Integrable (fun x => φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) volume at hig
  have hip := integrable_physical_cutoff_pairing
    (fun K hK => (hf K hK).star) (fun K hK => (hg K hK).neg) hφ
  change Integrable (fun x => (φ x : ℂ) ^ 2 * star (f (translate x ω)) *
    (-g (translate x ω))) volume at hip
  have hrint := integral_re hip
  change (∫ x, ((φ x : ℂ) ^ 2 * star (f (translate x ω)) *
    (-g (translate x ω))).re) =
    (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re at hrint
  have hb : (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω))).re ≤
      (∫ x, φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) / (2 * ε) +
        (ε / 2) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) := by
    rw [← hrint, ← integral_div, ← integral_const_mul,
      ← integral_add (hif.div_const _) (hig.const_mul _)]
    apply integral_mono hip.re ((hif.div_const _).add (hig.const_mul _))
    intro x
    dsimp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
    have hr := Complex.re_le_norm ((φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω)))
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, norm_star, norm_neg] at hr
    apply hr.trans
    have hy : ‖f (translate x ω)‖ * ‖g (translate x ω)‖ ≤
        (‖f (translate x ω)‖ ^ 2 + ε ^ 2 * ‖g (translate x ω)‖ ^ 2) / (2 * ε) := by
      apply (le_div_iff₀ (mul_pos two_pos hε)).mpr
      nlinarith [sq_nonneg (‖f (translate x ω)‖ - ε * ‖g (translate x ω)‖)]
    have hm := mul_le_mul_of_nonneg_left hy (sq_nonneg (φ x))
    convert hm using 1 <;> field_simp [ne_of_gt hε]
  exact (he φ hφ).trans (add_le_add hb le_rfl)

/-- Terminal gradient energy on a Euclidean ball is bounded by the actual
solution and generator-output masses on a larger ball. The cutoff constant
is fixed before the environment law and force are chosen. -/
theorem local_time_physical_ball_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let B := Classical.choose (exists_physical_gap_euclidean_cutoff d)
    ∀ᵐ ω ∂reducedLaw Q, ∀ z : Vec d, ∀ r R : ℝ, 0 < r → r < R →
      ∀ ε : ℝ, 0 < ε →
      (L⁻¹ / 4) * (∫ x in {x | euclideanNorm (x - z) ≤ r},
        ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
      (1 / (2 * ε) + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
          (∫ x in {x | euclideanNorm (x - z) ≤ R}, ‖f (translate x ω)‖ ^ 2) +
      (ε / 2) * (∫ x in {x | euclideanNorm (x - z) ≤ R}, ‖g (translate x ω)‖ ^ 2) := by
  intro L B
  obtain ⟨_, hcutoff⟩ := Classical.choose_spec (exists_physical_gap_euclidean_cutoff d)
  filter_upwards [local_time_physical_cutoff_gradient hfg hG,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))] with ω he hf hg hGlocal
  intro z r R hr hrR ε hε
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hS : MeasurableSet S := (isCompact_physical_euclidean_closedBall z r).measurableSet
  have hSK : S ⊆ K := fun x hx => hx.trans hrR.le
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hz x hn)) hK.isClosed
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hweight {F ψ : Vec d → ℝ} {A : ℝ}
      (hi : IntegrableOn F K volume) (hpos : ∀ x, 0 ≤ F x)
      (hψ : Continuous ψ) (hψzero : ∀ x ∉ K, ψ x = 0)
      (hbound : ∀ x ∈ K, ψ x ≤ A) :
      (∫ x, ψ x * F x) ≤ A * ∫ x in K, F x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := K) (fun x hx => by rw [hψzero x hx]; simp), ← integral_const_mul]
    apply setIntegral_mono_on (hi.continuousOn_mul hψ.continuousOn hK) (hi.const_mul A)
      hK.measurableSet
    intro x hx
    exact mul_le_mul_of_nonneg_right (hbound x hx) (hpos x)
  have hiF := (memLp_two_iff_integrable_sq_norm (hf K hK).aestronglyMeasurable).mp (hf K hK)
  have hiG := (memLp_two_iff_integrable_sq_norm (hg K hK).aestronglyMeasurable).mp (hg K hK)
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hGlocal j K hK).aestronglyMeasurable).mp
      (hGlocal j K hK))
  have hφsq x : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
  have hunitF := hweight hiF (fun x => sq_nonneg _) (hφ.1.continuous.pow 2)
    (fun x hx => by simp [hz x hx]) (fun x _ => hφsq x)
  have hunitG := hweight hiG (fun x => sq_nonneg _) (hφ.1.continuous.pow 2)
    (fun x hx => by simp [hz x hx]) (fun x _ => hφsq x)
  have herr := hweight hiF (fun x => sq_nonneg _)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (A := ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)
    (fun x hx => by simp [hz x hx, hdz, hx])
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
  have hiφ := IntegrableOn.continuousOn_mul (hφ.1.continuous.pow 2).continuousOn hiD hK
  have heq : (∫ x in S, ∑ j, ‖G j (translate x ω)‖ ^ 2) =
      ∫ x in S, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2) := by
    apply setIntegral_congr_fun hS
    intro x hx
    change (∑ j, ‖G j (translate x ω)‖ ^ 2) =
      φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)
    rw [hone x hx, one_pow, one_mul]
  have hinner := setIntegral_mono_set hiφ
    (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg
      (fun j _ => sq_nonneg _)))) (Eventually.of_forall (fun x hx => hSK hx))
  simp only [Pi.pow_apply] at hinner
  rw [← heq, setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K) (fun x hx => by simp [hz x hx])] at hinner
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hL : 0 ≤ L⁻¹ / 4 := by dsimp [L]; positivity
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by dsimp [L]; positivity
  have hc := he φ hφ ε hε
  have hleft := mul_le_mul_of_nonneg_left hinner hL
  have hfbound := div_le_div_of_nonneg_right hunitF (show 0 ≤ 2 * ε by positivity)
  have hgbound := mul_le_mul_of_nonneg_left hunitG (show 0 ≤ ε / 2 by positivity)
  have herrbound := mul_le_mul_of_nonneg_left herr hC
  simp only [Pi.pow_apply, one_mul] at hfbound hgbound
  convert hleft.trans (hc.trans
    (add_le_add (add_le_add hfbound hgbound) herrbound)) using 1
  ring

/-- The output interpolation and derivative Caccioppoli estimates hold for
one common actual derivative orbit and common gradient representatives. -/
theorem local_time_joint_derivative_estimates
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let B := Classical.choose (exists_physical_gap_euclidean_cutoff d)
    let T := Classical.choose exists_physical_gap_temporal_cutoff
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    0 < B ∧ 0 < T ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ V : ℝ × FieldPair d → ℂ, ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ c e : ℝ, b < c → c ≤ e → ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
        ∀ ε : ℝ, 0 < ε → ∀ η : ℝ → ℝ, ContinuousOn η (Icc c e) →
          (∀ s ∈ Icc c e, 0 ≤ η s) → ∀ᵐ ω ∂reducedLaw Q,
          (1 / 2 : ℝ) * (∫ s in Icc c e, η s *
            (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2)) ≤
            ε * (∫ s in Icc c e, η s *
              (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2))) +
            (∫ s in Icc c e, η s *
              (∫ x, (((φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
                ((d : ℝ) ^ 2 * L ^ 2 / 4)) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)) *
                (∑ j, ‖D j (s, translate x ω)‖ ^ 2)))) ∧
      (∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖E j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - c) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖V (s, translate x ω)‖ ^ 2)) := by
  intro L B T w
  let := reducedLaw_probability Q
  obtain ⟨hB, hcutoff⟩ := Classical.choose_spec (exists_physical_gap_euclidean_cutoff d)
  obtain ⟨hT, htime⟩ := Classical.choose_spec exists_physical_gap_temporal_cutoff
  obtain ⟨g, h, V, Z, E, hV, hZ, hE, heV, heZ, heE,
    hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  obtain ⟨D, hD, heD, hDlocal⟩ := complexForced_correctedOrbit_ae_spacetime_gradient hP f
  refine ⟨hB, hT, g, V, D, E, hV, hD, hE, heV, heD, heE, hw, ?_, ?_⟩
  · intro c e hc _hce φ hφ ε hε η hη hηpos
    have hac : a < c := hab.trans hc
    have hcont : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
      (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
    have hlocalV := ae_locally_memLp_joint_spatial_translate
      (reducedLaw Q) (reducedLaw_stationary Q) hV
      (integrable_sq_joint_l2_representative
        ((hcont.norm.pow 2).continuousOn.integrableOn_compact
          (μ := (volume : Measure ℝ)) (K := Icc c e) isCompact_Icc) hV heV)
    have hElocal (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => E j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc c e))) := by
      have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
        (hP.continuousOn_gradientOrbit g).comp
          (continuous_id.sub continuous_const).continuousOn (fun s hs => by
            change 0 < s - a
            exact sub_pos.mpr hs)
      have hj : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
      exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
        (hE j) (integrable_sq_joint_l2_representative
          (((hj.norm.pow 2).mono (fun s hs => hac.trans_le hs.1)).integrableOn_compact
            isCompact_Icc) (hE j) (heE j))
    have hyoung := ae_joint_physical_generator_output_young (b := c) (c := e)
      (u := w) (v := fun s => P (s - a).toNNReal g)
      (G := fun s j => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
      (H := fun s j => (hP.gradientOrbit g (s - a)) j)
      (fun s hs => (hw s (hac.trans_le hs.1)).2)
      (fun s hs => complexForced_correctedOrbit_gradient_spec hP f t
        (ha.trans (hac.trans_le hs.1)))
      (fun s hs => hP.gradientOrbit_spec g (sub_pos.mpr (hac.trans_le hs.1)))
      hV hD hE heV heD heE hφ hε
    filter_upwards [hyoung, hlocalV, hDlocal c e (ha.trans hac),
      ae_all_iff.mpr hElocal] with ω hy hv hdl hel
    exact physical_generator_output_young_time_integral hφ
      (hv (tsupport φ) hφ.2.1) (hdl (tsupport φ) hφ.2.1)
      (fun j => hel j (tsupport φ) hφ.2.1) hη hηpos hy

  · let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
    have hu : Continuous u :=
      (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
    have hL : 0 < L := mul_pos (Real.exp_pos _)
      (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
    have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
    intro c e v hc hce hev z r R hr hrR
    have hcv : c < v := hce.trans_le hev
    obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
    obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime c e hce
    have hηcont : ContinuousOn η (Icc c v) := hη.continuous.continuousOn
    have hηd : ContinuousOn (deriv η) (Icc c v) :=
      (hη.continuous_deriv (by simp)).continuousOn
    have hηac : AbsolutelyContinuousOnInterval η c v :=
      (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
    have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c v) volume :=
      (hu.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    have hlocalW := ae_locally_memLp_joint_spatial_translate
      (reducedLaw Q) (reducedLaw_stationary Q) hV
      (integrable_sq_joint_l2_representative hwI hV heV)
    have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
        ∀ K : Set (Vec d), IsCompact K →
          MemLp (fun p : Vec d × ℝ => E j (p.2, translate p.1 ω)) 2
            ((volume.restrict K).prod (volume.restrict (Icc c v))) := by
      have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
        (hP.continuousOn_gradientOrbit g).comp
          (continuous_id.sub continuous_const).continuousOn (fun s hs => by
            change 0 < s - a
            exact sub_pos.mpr hs)
      have hcoord : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
        (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
      have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit g (s - a)) j‖ ^ 2)
          (Icc c v) volume :=
        ((hcoord.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (hab.trans hc) hs.1)).integrableOn_compact
          isCompact_Icc
      exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
        (hE j) (integrable_sq_joint_l2_representative hi (hE j) (heE j))
    filter_upwards [henergy c v hc hcv.le φ hφ η hηac hηd
      (fun s _ => (hηbounds s).1), hlocalW, ae_all_iff.mpr hlocalD]
      with ω hω hlW hlD
    have hK := isCompact_physical_euclidean_closedBall z R
    apply physical_spacetime_caccioppoli_of_cutoff_energy hK
      (isCompact_physical_euclidean_closedBall z r).measurableSet
      (fun x hx => hx.trans hrR.le) hL hC measurableSet_Icc
      (Icc_subset_Icc_left hce.le) (U := fun x => (u v) (translate x ω))
      (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange
      (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
      (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
      hηcont hηd (fun s _ => hηbounds s) (fun s hs => (hηone s hs.1).ge)
    rw [hηb, hηone v hev, zero_mul, one_mul, zero_sub] at hω
    linarith only [hω]

/-- Bounded energies with a dyadically growing error admit uniform absorption.
This eliminates the outer output mass after nested-cylinder interpolation. -/
theorem local_time_dyadic_absorption {A : ℕ → ℝ} {K M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ n, A n ≤ M)
    (hstep : ∀ n, A n ≤ A (n + 1) / 32 + K * (16 : ℝ) ^ n) :
    A 0 ≤ 2 * K := by
  let u : ℕ → ℝ := fun n => A n / (16 : ℝ) ^ n
  have hbounded : BddAbove (Set.range u) := by
    refine ⟨M, ?_⟩
    rintro _ ⟨n, rfl⟩
    apply (div_le_iff₀ (by positivity : 0 < (16 : ℝ) ^ n)).mpr
    exact (hbound n).trans (le_mul_of_one_le_right hM (one_le_pow₀ (by norm_num)))
  let S := sSup (Set.range u)
  have hu (n : ℕ) : u n ≤ S := le_csSup hbounded (Set.mem_range_self n)
  have hrec (n : ℕ) : u n ≤ u (n + 1) / 2 + K := by
    dsimp only [u]
    rw [div_le_iff₀ (by positivity : 0 < (16 : ℝ) ^ n)]
    have he : (A (n + 1) / (16 : ℝ) ^ (n + 1) / 2 + K) * (16 : ℝ) ^ n =
        A (n + 1) / 32 + K * (16 : ℝ) ^ n := by
      rw [pow_succ]
      field_simp
      ring
    rw [he]
    exact hstep n
  have hs : S ≤ S / 2 + K := by
    apply csSup_le (Set.range_nonempty u)
    rintro _ ⟨n, rfl⟩
    exact (hrec n).trans (by linarith [hu (n + 1)])
  have hzero := hu 0
  simp only [u, pow_zero, div_one] at hzero
  linarith

private theorem local_time_divergence_projection {d : ℕ} {F : Vec d → Fin d → ℂ}
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

/-- Test the literal conservative transpose graph against any actual H1 field.
The common event precedes every compact smooth spatial cutoff. -/
theorem local_time_transpose_physical_test
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v H) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      Integrable (fun x => ∑ j, ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
          2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
        ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
            star (v (translate x ω)))) volume ∧
      (∫ x, ∑ j, ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
          2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
        ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
          2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
            star (v (translate x ω)))) =
        -(2 : ℂ) * (∫ x, g (translate x ω) *
          ((φ x : ℂ) ^ 2 * star (v (translate x ω)))) := by
  let F : Fin d → FieldPair d → ℂ := fun j ω =>
    (∑ k, (ω.1 0 j k : ℂ) * G k ω) - 2 * ζ * (ω.1 0 j i : ℂ) * f ω
  have hm (j k : Fin d) : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
    (Complex.continuous_ofReal.comp
      (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
  have hFm (j : Fin d) : Measurable (F j) :=
    (Finset.measurable_sum _ fun k _ => (hm j k).mul
      (Lp.stronglyMeasurable _).measurable).sub
        ((measurable_const.mul (hm j i)).mul
          (Lp.stronglyMeasurable f).measurable)
  have hF (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    have ha := (Lp.memLp (complexCoefficientMul Q j i f)).ae_eq
      (complexCoefficientMul_coe Q j i f)
    simpa only [F, mul_assoc] using!
      (memLp_complex_coefficient_flux Q G j).sub (ha.const_mul (2 * ζ))
  have hq : MemLp (fun ω => (2 : ℂ) * g ω) 2 (reducedLaw Q) :=
    (Lp.memLp g).const_mul 2
  have hqm : Measurable (fun ω => (2 : ℂ) * g ω) :=
    measurable_const.mul (Lp.stronglyMeasurable g).measurable
  have hw := ae_complex_spatial_divergence_all_tests (reducedLaw Q)
    (reducedLaw_stationary Q) F (fun ω => (2 : ℂ) * g ω) hFm hqm hF hq
    (fun w W hW => by simpa only [F, mul_assoc] using hfg.horizontal_flux hG w W hW)
  filter_upwards [hH.ae_reduced_spatial Q, hw,
    ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q)
      (reducedLaw_stationary Q) hqm hq,
    ae_all_iff.mpr (fun j => ae_complex_function_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (hFm j) (hF j))]
    with ω hω hw hqω hFω
  have hreal := local_time_divergence_projection
    (fun K hK j => hFω j K hK) hqω hw Complex.reCLM
  have himag := local_time_divergence_projection
    (fun K hK j => hFω j K hK) hqω hw Complex.imCLM
  intro φ hφ
  have he := physicalWeakDivergence_cutoff_locallyH1 isOpen_univ
    (fun K hK _ => (hω.2.2 K hK).1)
    (fun K hK _ j => (hω.2.2 K hK).2 j)
    (fun K hK _ j => hFω j K hK) (fun K hK _ => hqω K hK)
    hω.1 hω.2.1 hreal himag hφ
  have hi : Integrable (fun x => ∑ j, F j (translate x ω) *
      ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
        2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
          star (v (translate x ω)))) volume := by
    apply integrable_finsetSum
    intro j _
    have hfirst := integrable_physical_cutoff_pairing
      (hFω j) (fun K hK => ((hω.2.2 K hK).2 j).star) hφ
    have hsecond := integrable_physical_compact_pairing
      (ψ := fun x => (2 : ℂ) * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ)) hφ.2.1
      (hFω j (tsupport φ) hφ.2.1) ((hω.2.2 _ hφ.2.1).1.star)
      ((continuous_const.mul (Complex.continuous_ofReal.comp hφ.1.continuous)).mul
        (Complex.continuous_ofReal.comp
          ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)))
      (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
    convert hfirst.add hsecond using 1
    funext x
    simp only [Pi.star_apply, Pi.add_apply]
    ring
  constructor
  · simpa only [F, translate_matrix, add_zero] using hi
  · simpa only [F, translate_matrix, add_zero, mul_assoc, integral_const_mul,
      neg_mul] using he

/-- The conservative transpose equation tested against its actual output
recovers that output's physical squared mass. -/
theorem local_time_transpose_physical_output_mass
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g H) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) =
        (-(1 / 2 : ℂ) * (∫ x, ∑ j,
          ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
            2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)) *
          ((φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
            2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) *
              star (g (translate x ω))))).re := by
  filter_upwards [local_time_transpose_physical_test hfg hG hH] with ω he
  intro φ hφ
  have hmass : (∫ x, g (translate x ω) *
      ((φ x : ℂ) ^ 2 * star (g (translate x ω)))) =
      ((∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [mul_comm (g (translate x ω)), mul_assoc,
      RCLike.star_def, RCLike.conj_mul]
    push_cast
    rfl
  rw [(he φ hφ).2, hmass]
  norm_num [mul_assoc]
  ring

/-- Compact cutoff energy for the actual transpose generator. The force stays
inside its conservative flux throughout the conjugate testing argument. -/
theorem local_time_transpose_physical_cutoff_energy
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
        (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re +
        10 * L ^ 3 * (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
          (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) := by
  intro L
  have hL : 1 ≤ L := by
    have hΛ := Q.ellipticity_parameter
    exact le_trans (by norm_num : (1 : ℝ) ≤ 1 * 1)
      (mul_le_mul (Real.one_le_exp (by linarith)) hΛ zero_le_one (Real.exp_nonneg _))
  filter_upwards [local_time_transpose_physical_test hfg hG hG,
    hG.ae_reduced_spatial Q, c4_ae_reduced_physical_elliptic Q]
    with ω ht hω ha
  intro φ hφ
  let J : Vec d → Fin d → ℂ := fun x j =>
    (φ x : ℂ) ^ 2 * star (G j (translate x ω)) +
      2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (f (translate x ω))
  let F : Vec d → Fin d → ℂ := fun x j =>
    (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
      2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω)
  have hraw := (ht φ hφ).1
  have hid := (ht φ hφ).2
  change Integrable (fun x => ∑ j, F x j * J x j) volume at hraw
  change (∫ x, ∑ j, F x j * J x j) =
    -(2 : ℂ) * (∫ x, g (translate x ω) *
      ((φ x : ℂ) ^ 2 * star (f (translate x ω)))) at hid
  have hi := hraw.const_mul (1 / 2 : ℂ)
  have hgrad : Integrable (fun x => φ x ^ 2 *
      (∑ j, ‖G j (translate x ω)‖ ^ 2)) volume := by
    simpa only [Finset.mul_sum, Pi.pow_apply] using
      (integrable_finsetSum Finset.univ fun j _ =>
        integrable_physical_compact_sq_norm hφ.2.1 ((hω.2.2 _ hφ.2.1).2 j)
          (hφ.1.continuous.pow 2)
          (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))
  have herr : Integrable (fun x => (‖ζ‖ ^ 2 * φ x ^ 2 +
      (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) volume := by
    apply integrable_physical_compact_sq_norm hφ.2.1 ((hω.2.2 _ hφ.2.1).1)
    · exact (continuous_const.mul (hφ.1.continuous.pow 2)).add
        (continuous_finsetSum _ fun j _ =>
          (((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2))
    · intro x hx
      have hz := image_eq_zero_of_notMem_tsupport hx
      have hD (j : Fin d) : coordinateDerivative j φ x = 0 := by
        simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx,
          zero_apply]
      simp [hz, hD]
  have hpoint (x : Vec d) :
      (L⁻¹ / 4) * (φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
        ((1 / 2 : ℂ) * (∑ j, F x j * J x j)).re +
          10 * L ^ 3 * ((‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) := by
    have hc := c6_transpose_cutoff_coercive (s5Elliptic_of_isElliptic hL ha x)
      (fun j => G j (translate x ω)) (f (translate x ω))
      (fun j => coordinateDerivative j φ x) (φ x) i ζ
    have hJ (j : Fin d) : ((φ x ^ 2 : ℝ) : ℂ) * star (G j (translate x ω)) +
        star (f (translate x ω)) * ((2 * φ x * coordinateDerivative j φ x : ℝ) : ℂ) =
        J x j := by
      dsimp only [J]
      push_cast
      ring
    simp_rw [hJ] at hc
    have hs : (∑ j, F x j * J x j) =
        (∑ j, ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω) * J x j) -
          (2 * ζ * f (translate x ω)) * (∑ j, (ω.1 x j i : ℂ) * J x j) := by
      calc
        _ = ∑ j, ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω) * J x j) -
            (2 * ζ * f (translate x ω)) * ((ω.1 x j i : ℂ) * J x j)) := by
          apply Finset.sum_congr rfl
          intro j _
          dsimp only [F]
          rw [sub_mul, Finset.sum_mul]
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    have halg : -(1 / 2 : ℂ) * (∑ j, F x j * J x j) =
        -(1 / 2 : ℂ) * (∑ j, ∑ k,
          (ω.1 x j k : ℂ) * G k (translate x ω) * J x j) +
          ζ * f (translate x ω) * (∑ j, (ω.1 x j i : ℂ) * J x j) := by
      rw [hs]
      ring
    rw [← halg] at hc
    have hn : s5Nrm (fun j => coordinateDerivative j φ x) ^ 2 =
        ∑ j, (coordinateDerivative j φ x) ^ 2 := by
      exact Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)
    rw [hn] at hc
    simp only [neg_mul, Complex.neg_re] at hc
    nlinarith
  have hint := integral_mono (hgrad.const_mul (L⁻¹ / 4))
    (hi.re.add (herr.const_mul (10 * L ^ 3))) hpoint
  change (∫ x, (L⁻¹ / 4) * (φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2))) ≤
    (∫ x, ((1 / 2 : ℂ) * (∑ j, F x j * J x j)).re +
      10 * L ^ 3 * ((‖ζ‖ ^ 2 * φ x ^ 2 +
        (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2)) at hint
  have hir : Integrable (fun x => ((1 / 2 : ℂ) * (∑ j, F x j * J x j)).re) volume := hi.re
  have hier : Integrable (fun x => 10 * L ^ 3 * ((‖ζ‖ ^ 2 * φ x ^ 2 +
      (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2)) volume :=
    herr.const_mul _
  rw [integral_const_mul, integral_add hir hier, integral_const_mul] at hint
  have hire := integral_re hi
  change (∫ x, ((1 / 2 : ℂ) * (∑ j, F x j * J x j)).re) =
    (∫ x, (1 / 2 : ℂ) * (∑ j, F x j * J x j)).re at hire
  rw [hire, integral_const_mul, hid] at hint
  have hp : (1 / 2 : ℂ) * (-(2 : ℂ) * (∫ x, g (translate x ω) *
      ((φ x : ℂ) ^ 2 * star (f (translate x ω))))) =
      (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))) := by
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  rw [hp] at hint
  exact hint

/-- Balance the actual transpose generator output against its solution in
compact cutoff energy, with an arbitrary positive scale. -/
theorem local_time_transpose_physical_cutoff_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      ∀ ε : ℝ, 0 < ε →
      (L⁻¹ / 4) * (∫ x, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)) ≤
        (∫ x, φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) / (2 * ε) +
        (ε / 2) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) +
        (10 * L ^ 3) *
          (∫ x, (‖ζ‖ ^ 2 * φ x ^ 2 +
            (∑ j, (coordinateDerivative j φ x) ^ 2)) * ‖f (translate x ω)‖ ^ 2) := by
  intro L
  filter_upwards [local_time_transpose_physical_cutoff_energy hfg hG,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g]
    with ω he hf hg
  intro φ hφ ε hε
  have hif := integrable_physical_compact_sq_norm hφ.2.1 (hf _ hφ.2.1)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  have hig := integrable_physical_compact_sq_norm hφ.2.1 (hg _ hφ.2.1)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  change Integrable (fun x => φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) volume at hif
  change Integrable (fun x => φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) volume at hig
  have hip := integrable_physical_cutoff_pairing
    (fun K hK => (hf K hK).star) (fun K hK => (hg K hK).neg) hφ
  change Integrable (fun x => (φ x : ℂ) ^ 2 * star (f (translate x ω)) *
    (-g (translate x ω))) volume at hip
  have hrint := integral_re hip
  change (∫ x, ((φ x : ℂ) ^ 2 * star (f (translate x ω)) *
    (-g (translate x ω))).re) =
    (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) * (-g (translate x ω))).re at hrint
  have hb : (∫ x, (φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω))).re ≤
      (∫ x, φ x ^ 2 * ‖f (translate x ω)‖ ^ 2) / (2 * ε) +
        (ε / 2) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) := by
    rw [← hrint, ← integral_div, ← integral_const_mul,
      ← integral_add (hif.div_const _) (hig.const_mul _)]
    apply integral_mono hip.re ((hif.div_const _).add (hig.const_mul _))
    intro x
    dsimp only [Pi.add_apply, Pi.div_apply, Pi.mul_apply]
    have hr := Complex.re_le_norm ((φ x : ℂ) ^ 2 * star (f (translate x ω)) *
      (-g (translate x ω)))
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, norm_star, norm_neg] at hr
    apply hr.trans
    have hy : ‖f (translate x ω)‖ * ‖g (translate x ω)‖ ≤
        (‖f (translate x ω)‖ ^ 2 + ε ^ 2 * ‖g (translate x ω)‖ ^ 2) / (2 * ε) := by
      apply (le_div_iff₀ (mul_pos two_pos hε)).mpr
      nlinarith [sq_nonneg (‖f (translate x ω)‖ - ε * ‖g (translate x ω)‖)]
    have hm := mul_le_mul_of_nonneg_left hy (sq_nonneg (φ x))
    convert hm using 1 <;> field_simp [ne_of_gt hε]
  exact (he φ hφ).trans (add_le_add hb le_rfl)

/-- Transpose terminal gradient energy on nested Euclidean balls, using
only the actual solution and generator output and a universal cutoff. -/
theorem local_time_transpose_physical_ball_gradient
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let B := Classical.choose (exists_physical_gap_euclidean_cutoff d)
    ∀ᵐ ω ∂reducedLaw Q, ∀ z : Vec d, ∀ r R : ℝ, 0 < r → r < R →
      ∀ ε : ℝ, 0 < ε →
      (L⁻¹ / 4) * (∫ x in {x | euclideanNorm (x - z) ≤ r},
        ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤
      (1 / (2 * ε) + (10 * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
          (∫ x in {x | euclideanNorm (x - z) ≤ R}, ‖f (translate x ω)‖ ^ 2) +
      (ε / 2) * (∫ x in {x | euclideanNorm (x - z) ≤ R}, ‖g (translate x ω)‖ ^ 2) := by
  intro L B
  obtain ⟨_, hcutoff⟩ := Classical.choose_spec (exists_physical_gap_euclidean_cutoff d)
  filter_upwards [local_time_transpose_physical_cutoff_gradient hfg hG,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j))] with ω he hf hg hGlocal
  intro z r R hr hrR ε hε
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  let S := {x : Vec d | euclideanNorm (x - z) ≤ r}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hS : MeasurableSet S := (isCompact_physical_euclidean_closedBall z r).measurableSet
  have hSK : S ⊆ K := fun x hx => hx.trans hrR.le
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hz x hn)) hK.isClosed
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hweight {F ψ : Vec d → ℝ} {A : ℝ}
      (hi : IntegrableOn F K volume) (hpos : ∀ x, 0 ≤ F x)
      (hψ : Continuous ψ) (hψzero : ∀ x ∉ K, ψ x = 0)
      (hbound : ∀ x ∈ K, ψ x ≤ A) :
      (∫ x, ψ x * F x) ≤ A * ∫ x in K, F x := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := K) (fun x hx => by rw [hψzero x hx]; simp), ← integral_const_mul]
    apply setIntegral_mono_on (hi.continuousOn_mul hψ.continuousOn hK) (hi.const_mul A)
      hK.measurableSet
    intro x hx
    exact mul_le_mul_of_nonneg_right (hbound x hx) (hpos x)
  have hiF := (memLp_two_iff_integrable_sq_norm (hf K hK).aestronglyMeasurable).mp (hf K hK)
  have hiG := (memLp_two_iff_integrable_sq_norm (hg K hK).aestronglyMeasurable).mp (hg K hK)
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hGlocal j K hK).aestronglyMeasurable).mp
      (hGlocal j K hK))
  have hφsq x : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
  have hunitF := hweight hiF (fun x => sq_nonneg _) (hφ.1.continuous.pow 2)
    (fun x hx => by simp [hz x hx]) (fun x _ => hφsq x)
  have hunitG := hweight hiG (fun x => sq_nonneg _) (hφ.1.continuous.pow 2)
    (fun x hx => by simp [hz x hx]) (fun x _ => hφsq x)
  have herr := hweight hiF (fun x => sq_nonneg _)
    ((continuous_const.mul (hφ.1.continuous.pow 2)).add
      (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
    (A := ‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)
    (fun x hx => by simp [hz x hx, hdz, hx])
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
  have hiφ := IntegrableOn.continuousOn_mul (hφ.1.continuous.pow 2).continuousOn hiD hK
  have heq : (∫ x in S, ∑ j, ‖G j (translate x ω)‖ ^ 2) =
      ∫ x in S, φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2) := by
    apply setIntegral_congr_fun hS
    intro x hx
    change (∑ j, ‖G j (translate x ω)‖ ^ 2) =
      φ x ^ 2 * (∑ j, ‖G j (translate x ω)‖ ^ 2)
    rw [hone x hx, one_pow, one_mul]
  have hinner := setIntegral_mono_set hiφ
    (Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg
      (fun j _ => sq_nonneg _)))) (Eventually.of_forall (fun x hx => hSK hx))
  simp only [Pi.pow_apply] at hinner
  rw [← heq, setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := K) (fun x hx => by simp [hz x hx])] at hinner
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  have hL : 0 ≤ L⁻¹ / 4 := by dsimp [L]; positivity
  have hC : 0 ≤ 10 * L ^ 3 := by dsimp [L]; positivity
  have hc := he φ hφ ε hε
  have hleft := mul_le_mul_of_nonneg_left hinner hL
  have hfbound := div_le_div_of_nonneg_right hunitF (show 0 ≤ 2 * ε by positivity)
  have hgbound := mul_le_mul_of_nonneg_left hunitG (show 0 ≤ ε / 2 by positivity)
  have herrbound := mul_le_mul_of_nonneg_left herr hC
  simp only [Pi.pow_apply, one_mul] at hfbound hgbound
  convert hleft.trans (hc.trans
    (add_le_add (add_le_add hfbound hgbound) herrbound)) using 1
  ring

/-- The conservative transpose flux includes the force times the original field. -/
theorem local_time_transpose_half_flux_sq_le {d : ℕ}
    (A : Fin d → Fin d → ℝ) (X : Fin d → ℂ) (u ζ : ℂ)
    (i : Fin d) {L : ℝ} (hA : ∀ j k, |A j k| ≤ L) :
    (∑ j, ‖(1 / 2 : ℂ) * (∑ k, (A j k : ℂ) * X k) -
      ζ * (A j i : ℂ) * u‖ ^ 2) ≤
      ((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ k, ‖X k‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
  have hsub (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
    nlinarith only [hn, sq_nonneg (‖a‖ - ‖b‖)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    hsub ((1 / 2 : ℂ) * ∑ k, (A j k : ℂ) * X k) (ζ * (A j i : ℂ) * u))
  have ht : (∑ j, ‖ζ * (A j i : ℂ) * u‖ ^ 2) ≤
      (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖u‖ ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, ‖ζ‖ ^ 2 * L ^ 2 * ‖u‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simp only [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs]
        gcongr
        exact hA j i
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]; ring
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
  have hm := complex_matrix_halfFlux_sq_le A X hA
  nlinarith only [hs, hm, ht]

/-- Output testing for the actual transpose graph, with a freely chosen small
output-gradient coefficient and explicit original-field and gradient terms. -/
theorem local_time_transpose_physical_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    {G H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) g H) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ, IsSpatialTest univ φ →
      ∀ ε : ℝ, 0 < ε →
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖H j (translate x ω)‖ ^ 2)) +
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖G j (translate x ω)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖f (translate x ω)‖ ^ 2)) := by
  intro L
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  filter_upwards [local_time_transpose_physical_test hfg hG hH,
    local_time_transpose_physical_output_mass hfg hG hH,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j)),
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (H j)),
    c4_ae_reduced_physical_elliptic Q] with ω htest hm hfω hgω hGω hHω ha
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  intro φ hφ ε hε
  let K := tsupport φ
  have hK : IsCompact K := hφ.2.1
  have hz x (hx : x ∉ K) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hD j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hDz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx, zero_apply]
  let F : Vec d → Fin d → ℂ := fun x j => (1 / 2 : ℂ) *
    ((∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) -
      2 * ζ * (ω.1 x j i : ℂ) * f (translate x ω))
  let J : Vec d → Fin d → ℂ := fun x j =>
    (φ x : ℂ) ^ 2 * star (H j (translate x ω)) +
      2 * (φ x : ℂ) * (coordinateDerivative j φ x : ℂ) * star (g (translate x ω))
  have hi : Integrable (fun x => -(∑ j, F x j * J x j)) volume := by
    convert ((htest φ hφ).1.const_mul (-(1 / 2 : ℂ))) using 1
    ext x
    simp only [F, J, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hmass : (∫ x, φ x ^ 2 * ‖g (translate x ω)‖ ^ 2) =
      ∫ x, (-(∑ j, F x j * J x j)).re := by
    have hr := integral_re hi
    change (∫ x, (-(∑ j, F x j * J x j)).re) = _ at hr
    rw [hr]
    rw [hm φ hφ]
    apply congrArg Complex.re
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [F, J, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let R : Vec d → ℝ := fun x => φ x ^ 2 / (4 * ε) +
    4 * (∑ j, (coordinateDerivative j φ x) ^ 2)
  have hR : Continuous R := ((hφ.1.continuous.pow 2).div_const _).add
    (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hD j).pow 2)))
  have hRz x (hx : x ∉ K) : R x = 0 := by simp [R, hz x hx, hDz, hx]
  have hRv : Integrable (fun x => R x *
      (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖G j (translate x ω)‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖f (translate x ω)‖ ^ 2)) volume := by
    have h1 : Integrable (fun x => R x * (∑ j, ‖G j (translate x ω)‖ ^ 2)) volume := by
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ (fun j _ =>
        integrable_physical_compact_sq_norm hK (hGω j K hK) hR hRz)
    have h2 := integrable_physical_compact_sq_norm hK (hfω K hK) hR hRz
    convert (h1.const_mul ((d : ℝ) ^ 2 * L ^ 2 / 2)).add
      (h2.const_mul (2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2)) using 1
    ext x
    simp only [Pi.add_apply]
    ring
  have hHy : Integrable (fun x => φ x ^ 2 * (∑ j, ‖H j (translate x ω)‖ ^ 2)) volume := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun j _ => integrable_physical_compact_sq_norm hK
      (hHω j K hK) (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx]))
  have hv := integrable_physical_compact_sq_norm hK (hgω K hK)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have he := integral_mono_ae hi.re
    (((hv.const_mul (1 / 2 : ℝ)).add (hHy.const_mul ε)).add hRv)
    (Eventually.of_forall (fun x => by
      have hy := complexFlux_cutoff_output_young (F x)
        (fun j => H j (translate x ω)) (fun j => coordinateDerivative j φ x)
        (g (translate x ω)) 0 0 (φ x) ε hε
      simp only [zero_mul, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero,
        add_zero, zero_sub] at hy
      have hb := local_time_transpose_half_flux_sq_le (fun j k => ω.1 x j k)
        (fun j => G j (translate x ω)) (f (translate x ω)) ζ i
        (fun j k => Correctors.IsElliptic.entry_abs_le hL ha x j k)
      have hF : (∑ j, ‖F x j‖ ^ 2) ≤
          ((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖G j (translate x ω)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖f (translate x ω)‖ ^ 2 := by
        convert hb using 1
        apply Finset.sum_congr rfl
        intro j _
        congr 2
        dsimp [F]
        ring
      have hh := mul_le_mul_of_nonneg_left hF (show 0 ≤ R x by dsimp [R]; positivity)
      simp only [Pi.add_apply, Pi.pow_apply]
      convert hy.trans (add_le_add (le_refl _) hh) using 1
      dsimp [J, R]
      ring))
  change (∫ x, (-(∑ j, F x j * J x j)).re) ≤ _ at he
  have hj₁ := integral_add ((hv.const_mul (1 / 2 : ℝ)).add (hHy.const_mul ε)) hRv
  have hj₂ := integral_add (hv.const_mul (1 / 2 : ℝ)) (hHy.const_mul ε)
  simp only [Pi.add_apply, Pi.pow_apply] at he hj₁ hj₂
  rw [← hmass, hj₁, hj₂, integral_const_mul, integral_const_mul] at he
  change _ ≤ _ + (∫ x, R x * _)
  linarith

/-- Joint measurability lets the literal transpose output estimate hold on
one environment event for almost every time, using the actual graph fields. -/
theorem local_time_transpose_joint_output_young
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c : ℝ}
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G H : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Icc b c, IsComplexTransposeGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    (hout : ∀ s ∈ Icc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (v s) (H s))
    {W V : ℝ × FieldPair d → ℂ} {D E : Fin d → ℝ × FieldPair d → ℂ}
    (hW : Measurable W) (hV : Measurable V) (hD : ∀ j, Measurable (D j)) (hE : ∀ j, Measurable (E j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j)
    (heE : ∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q] H s j)
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ) {ε : ℝ} (hε : 0 < ε) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (s, translate x ω)‖ ^ 2)) +
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) := by
  intro L
  let := reducedLaw_probability Q
  let R : Vec d → ℝ := fun x =>
    φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)
  have hRm : Measurable R := by
    have hd j : Continuous (coordinateDerivative j φ) :=
      ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
    exact (hφ.1.continuous.measurable.pow_const 2).div_const _ |>.add
      (measurable_const.mul (Finset.measurable_sum _ fun j _ => (hd j).measurable.pow_const 2))
  have hshift {U : ℝ × FieldPair d → ℂ} (hU : Measurable U) :
      Measurable (fun q : (ℝ × FieldPair d) × Vec d => U (q.1.1, translate q.2 q.1.2)) :=
    hU.comp ((measurable_fst.comp measurable_fst).prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (measurable_snd.comp measurable_fst))))
  have hweight {U : ℝ × FieldPair d → ℂ} (hU : Measurable U)
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * ‖U (p.1, translate x p.2)‖ ^ 2) :=
    ((hψ.comp measurable_snd).mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hsum {J : Fin d → ℝ × FieldPair d → ℂ} (hJ : ∀ j, Measurable (J j))
      {ψ : Vec d → ℝ} (hψ : Measurable ψ) :
      Measurable (fun p : ℝ × FieldPair d =>
        ∫ x, ψ x * (∑ j, ‖J j (p.1, translate x p.2)‖ ^ 2)) :=
    ((hψ.comp measurable_snd).mul (Finset.measurable_sum _ fun j _ =>
      ((hshift (hJ j)).norm.pow_const 2))).stronglyMeasurable.integral_prod_right'.measurable
  let A := fun p : ℝ × FieldPair d =>
    (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (p.1, translate x p.2)‖ ^ 2)
  let B := fun p : ℝ × FieldPair d =>
    ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (p.1, translate x p.2)‖ ^ 2)) +
      (∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
        (∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (p.1, translate x p.2)‖ ^ 2))
  have hA : Measurable A := measurable_const.mul
    (hweight hV (hφ.1.continuous.measurable.pow_const 2))
  have hB : Measurable B := (measurable_const.mul
    (hsum hE (hφ.1.continuous.measurable.pow_const 2))).add
    (((hRm.comp measurable_snd).mul
      ((measurable_const.mul (Finset.measurable_sum _ fun j _ =>
        ((hshift (hD j)).norm.pow_const 2))).add
        (measurable_const.mul ((hshift hW).norm.pow_const 2)))).stronglyMeasurable.integral_prod_right'.measurable)
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  have hew := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hW.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heW s)
  have hev := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  have hed j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hD j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (G s j)).measurable (heD j s)
  have hee j := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    ((hE j).comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (H s j)).measurable (heE j s)
  filter_upwards [local_time_transpose_physical_output_young (hgen s hs) (hgrad s hs) (hout s hs),
    hew, hev, ae_all_iff.mpr hed, ae_all_iff.mpr hee] with ω hy hw hv hd he
  have heall := ae_all_iff.mpr he
  have hdall := ae_all_iff.mpr hd
  have hmass : (∫ x, φ x ^ 2 * ‖V (s, translate x ω)‖ ^ 2) =
      ∫ x, φ x ^ 2 * ‖(v s) (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [hv] with x hx
    change V (s, translate x ω) = _ at hx
    rw [hx]
  have hsum_eq {J : Fin d → ℝ × FieldPair d → ℂ} {K : Fin d → Lp ℂ 2 (reducedLaw Q)}
      (hJK : ∀ᵐ x ∂(volume : Measure (Vec d)), ∀ j, J j (s, translate x ω) = K j (translate x ω))
      (ψ : Vec d → ℝ) :
      (∫ x, ψ x * (∑ j, ‖J j (s, translate x ω)‖ ^ 2)) =
        ∫ x, ψ x * (∑ j, ‖K j (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hJK] with x hx
    simp only [hx]
  have hrest : (∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
      (∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
      2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (s, translate x ω)‖ ^ 2)) =
      ∫ x, R x * (((d : ℝ) ^ 2 * L ^ 2 / 2) *
        (∑ j, ‖G s j (translate x ω)‖ ^ 2) +
        2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖(u s) (translate x ω)‖ ^ 2) := by
    apply integral_congr_ae
    filter_upwards [hdall, hw] with x hd hw
    change W (s, translate x ω) = _ at hw
    change ∀ j, D j (s, translate x ω) = _ at hd
    simp only [hd, hw]
  change (1 / 2 : ℝ) * _ ≤ ε * _ + _
  rw [hmass, hsum_eq heall, hrest]
  exact hy φ hφ ε hε

/-- Local spacetime L2 permits weighted time integration of the conservative
transpose output estimate, including its original-field force term. -/
theorem local_time_transpose_output_young_time_integral {d : ℕ}
    {Λ₀ : ℝ} {ζ : ℂ} {b c ε : ℝ}
    {W V : Vec d × ℝ → ℂ} {D E : Fin d → Vec d × ℝ → ℂ}
    {φ : Vec d → ℝ} (hφ : IsSpatialTest univ φ)
    (hW : MemLp W 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hV : MemLp V 2 ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hD : ∀ j, MemLp (D j) 2
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    (hE : ∀ j, MemLp (E j) 2
      ((volume.restrict (tsupport φ)).prod (volume.restrict (Icc b c))))
    {η : ℝ → ℝ} (hη : ContinuousOn η (Icc b c))
    (hηpos : ∀ s ∈ Icc b c, 0 ≤ η s)
    (hy : ∀ᵐ s ∂volume.restrict (Icc b c),
      (1 / 2 : ℝ) * (∫ x, φ x ^ 2 * ‖V (x, s)‖ ^ 2) ≤
        ε * (∫ x, φ x ^ 2 * (∑ j, ‖E j (x, s)‖ ^ 2)) +
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * (Real.exp (2 * Λ₀) * Λ₀) ^ 2 / 2) *
            (∑ j, ‖D j (x, s)‖ ^ 2) +
            2 * (d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) ^ 2 * ‖ζ‖ ^ 2 * ‖W (x, s)‖ ^ 2))) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    (1 / 2 : ℝ) * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * ‖V (x, s)‖ ^ 2)) ≤
      ε * (∫ s in Icc b c, η s * (∫ x, φ x ^ 2 * (∑ j, ‖E j (x, s)‖ ^ 2))) +
      (∫ s in Icc b c, η s *
        (∫ x, (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
          (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (x, s)‖ ^ 2) +
            2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (x, s)‖ ^ 2))) := by
  intro L
  have hz x (hx : x ∉ tsupport φ) : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  have hdz j x (hx : x ∉ tsupport φ) : coordinateDerivative j φ x = 0 := by
    simp [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx]
  let R : Vec d → ℝ := fun x =>
    φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)
  have hR : Continuous R := (hφ.1.continuous.pow 2).div_const _ |>.add
    (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hD j).aestronglyMeasurable).mp (hD j))
  have hiW := (memLp_two_iff_integrable_sq_norm hW.aestronglyMeasurable).mp hW
  have hRv := integrable_time_integral_compact_spatial_weight hφ.2.1
    ((hiD.const_mul ((d : ℝ) ^ 2 * L ^ 2 / 2)).add
      (hiW.const_mul (2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2))) hR
    (fun x hx => by simp [R, hz x hx, hdz, hx])
  have hEv := integrable_time_integral_compact_spatial_weight hφ.2.1
    (integrable_finsetSum Finset.univ (fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hE j).aestronglyMeasurable).mp (hE j)))
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hVv := integrable_time_integral_compact_spatial_weight hφ.2.1
    ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mp hV)
    (hφ.1.continuous.pow 2) (fun x hx => by simp [hz x hx])
  have hRη := IntegrableOn.continuousOn_mul hη hRv isCompact_Icc
  have hEη := IntegrableOn.continuousOn_mul hη hEv isCompact_Icc
  have hVη := IntegrableOn.continuousOn_mul hη hVv isCompact_Icc
  have hi := integral_mono_ae (hVη.const_mul (1 / 2 : ℝ))
    ((hEη.const_mul ε).add hRη) (by
      filter_upwards [hy, ae_restrict_mem measurableSet_Icc] with s hs hsm
      simp only [Pi.add_apply, Pi.pow_apply]
      change _ ≤ _ + η s * (∫ x, R x *
        (((d : ℝ) ^ 2 * L ^ 2 / 2) * (∑ j, ‖D j (x, s)‖ ^ 2) +
          2 * (d : ℝ) * L ^ 2 * ‖ζ‖ ^ 2 * ‖W (x, s)‖ ^ 2))
      nlinarith [mul_le_mul_of_nonneg_left hs (hηpos s hsm)])
  simp only [Pi.add_apply, Pi.pow_apply] at hi
  have hj := integral_add (hEη.const_mul ε) hRη
  simp only [Pi.add_apply, Pi.pow_apply] at hj
  rw [hj, integral_const_mul, integral_const_mul] at hi
  exact hi

/-- The original corrected-orbit terminal trace has a dimension-only cutoff
constant, chosen before the environment and the force. -/
theorem local_time_uniform_corrected_orbit_timeSliceL2
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (_ht : 0 < t) (_ha : 0 < a),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b < c → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(w c) (translate x ω)‖ ^ 2) ≤
          2 * ((c - b)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a ht ha L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b c hb hbc z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hbc
  have hηcont : ContinuousOn η (Icc b c) := by
    simpa only [uIcc_of_le hbc.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc b c) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (c - b) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalU := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (w c)
  filter_upwards [henergy b c hb hbc.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, hlocalU]
    with ω hω hlW hlU
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_timeSliceL2_of_cutoff_energy (D := fun j p => D j (p.2, translate p.1 ω))
    hbc hr hκ hL hC hrad
    (hlW _ hK) (hlU _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]


/-- Large Euclidean windows bound the original corrected-orbit terminal mass
by its actual cylinder mass, with constants fixed before the law and force. -/
theorem local_time_uniform_corrected_orbit_mass_largeRadius
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hat : a < t / 4),
    let w := fun s : ℝ => centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v)
    ∃ W : ℝ × FieldPair d → ℂ, Measurable W ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      ∀ z : Vec d, ∀ r : ℝ, Real.sqrt t ≤ r → ∀ᵐ ω ∂reducedLaw Q,
        (∫ x in {x | euclideanNorm (x - z) ≤ r}, ‖(w t) (translate x ω)‖ ^ 2) ≤
        (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t) *
          (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
            ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hproducer⟩ := local_time_uniform_corrected_orbit_timeSliceL2 d
  let L := Real.exp (2 * Λ₀) * Λ₀
  let A := 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3
  let C := 2 * (4 / 3 + A * (1 + (d : ℝ) * B ^ 2))
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i ζ P hP f t a ht ha hat w
  obtain ⟨g, W, V, D, hW, _, _, heW, _, _, _, hslice⟩ := hproducer hP f ht ha
  refine ⟨W, hW, heW, ?_⟩
  intro z r hrad
  have hr : 0 < r := (Real.sqrt_pos.mpr ht).trans_le hrad
  have htr : t ≤ r ^ 2 := by
    calc
      t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
      _ ≤ r ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg t) hr.le).mpr hrad
  let q := 1 + ‖ζ‖ * Real.sqrt t
  have hq : 1 ≤ q ^ 2 := by
    have hp : 0 ≤ ‖ζ‖ * Real.sqrt t := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    dsimp [q]
    nlinarith [sq_nonneg (‖ζ‖ * Real.sqrt t)]
  let κ := r * q / Real.sqrt t
  have hκ : 0 ≤ κ := by dsimp [κ, q]; positivity
  have hrad' : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) := by
    apply le_of_eq
    dsimp [κ, q]
    field_simp
  have hκsq : κ ^ 2 / r ^ 2 = q ^ 2 / t := by
    dsimp [κ]
    rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
    field_simp
  have htime : (t - t / 4)⁻¹ = (4 / 3 : ℝ) / t := by field_simp; ring
  have hspace : (d : ℝ) * B ^ 2 / r ^ 2 ≤ ((d : ℝ) * B ^ 2) * (q ^ 2 / t) := by
    calc
      _ ≤ (d : ℝ) * B ^ 2 / t := by gcongr
      _ ≤ ((d : ℝ) * B ^ 2) * (q ^ 2 / t) := by
        have hn : (d : ℝ) * B ^ 2 ≤ (d : ℝ) * B ^ 2 * q ^ 2 :=
          le_mul_of_one_le_right (by positivity) hq
        exact (div_le_div_of_nonneg_right hn ht.le).trans_eq (by ring)
  have hcoeff : 2 * ((t - t / 4)⁻¹ + A * ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) ≤
      C * q ^ 2 / t := by
    rw [htime, add_div, hκsq]
    calc
      _ ≤ 2 * ((4 / 3 : ℝ) * (q ^ 2 / t) +
          A * (q ^ 2 / t + ((d : ℝ) * B ^ 2) * (q ^ 2 / t))) := by
        have htq : (4 / 3 : ℝ) / t ≤ (4 / 3 : ℝ) * (q ^ 2 / t) := by
          have hn : (4 / 3 : ℝ) ≤ (4 / 3 : ℝ) * q ^ 2 := by nlinarith
          exact (div_le_div_of_nonneg_right hn ht.le).trans_eq (by ring)
        exact mul_le_mul_of_nonneg_left
          (add_le_add htq (mul_le_mul_of_nonneg_left (add_le_add (le_refl _) hspace) hA))
          (by norm_num : (0 : ℝ) ≤ 2)
      _ = _ := by dsimp [C]; ring
  filter_upwards [hslice (t / 4) t hat (by linarith) z r κ hr hκ hrad'] with ω hω
  exact hω.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- A square bound for the actual gradient average transfers moments to the
literal local energy with zero derivative, including its `Lp` representative. -/
theorem local_time_zero_derivative_moment_of_sq_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) {p : ℝ≥0∞} {N : FieldPair d → ℝ}
    (hN : MemLp N p (reducedLaw Q)) (hNpos : ∀ᵐ ω ∂reducedLaw Q, 0 ≤ N ω)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂reducedLaw Q,
      (⨍ x in {x | euclideanNorm (x - z) < ρ},
        ∑ j, ‖G j (translate x ω)‖ ^ 2) ≤ K * N ω ^ 2) :
    MemLp (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q) ∧
      eLpNorm (localSpatialEnergy Q t ρ hρ z G 0) p (reducedLaw Q) ≤
        ENNReal.ofReal (Real.sqrt K) * eLpNorm N p (reducedLaw Q) := by
  let := reducedLaw_probability Q
  have hz : (fun ω => ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖) =ᵐ[reducedLaw Q]
      fun _ => (0 : ℝ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, norm_zero]
  have hphys := ae_ae_stationary_orbit_eq (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (0 : Lp ℂ 2 (reducedLaw Q))).measurable.norm
    measurable_const hz
  have hsq : ∀ᵐ ω ∂reducedLaw Q,
      localSpatialEnergy Q t ρ hρ z G 0 ω ^ 2 =
        ⨍ x in {x | euclideanNorm (x - z) < ρ}, ∑ j, ‖G j (translate x ω)‖ ^ 2 := by
    filter_upwards [hphys] with ω hω
    rw [localSpatialEnergy_sq]
    apply average_congr
    filter_upwards [ae_restrict_of_ae hω] with x hx
    simp only [hx, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  have hm := localSpatialEnergy_aestronglyMeasurable Q t ρ hρ z G 0
  have he : ∀ᵐ ω ∂reducedLaw Q,
      ‖localSpatialEnergy Q t ρ hρ z G 0 ω‖ ≤ Real.sqrt K * ‖N ω‖ := by
    filter_upwards [hsq, hbound, hNpos] with ω hs hb hn
    have hpos : 0 ≤ localSpatialEnergy Q t ρ hρ z G 0 ω := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Real.norm_eq_abs, abs_of_nonneg hn]
    apply (sq_le_sq₀ hpos (mul_nonneg (Real.sqrt_nonneg _) hn)).mp
    rw [mul_pow, Real.sq_sqrt hK, hs]
    exact hb
  exact ⟨hN.of_le_mul hm he, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm he p⟩

end EinsteinFull.Blueprint
