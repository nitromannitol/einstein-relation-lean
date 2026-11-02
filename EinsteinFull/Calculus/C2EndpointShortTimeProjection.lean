import PDEFoundation.Sobolev.H1.ProductLift
import PDEFoundation.Sobolev.H1.Product
import PDEFoundation.Sobolev.H1.Algebra
import PDEFoundation.Ambient.CoefficientField
import PDEFoundation.Measure.LpPower
import EllipticRegularity.Parabolic.ParabolicDef
import EllipticRegularity.Parabolic.Rescale.Affine
import EinsteinFull.Calculus.S5PointwiseSupport
import EinsteinFull.Calculus.C1ForcedLocalityClosureSupport
import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinFull.Calculus.C3EndpointLocalizationSupport
import EinsteinFull.Calculus.C2TestReplacementSupport
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_analytic_u2D_semigroup
import EinsteinFull.Calculus.C2RetainedPhysicalMeasurableEvolution
import EinsteinFull.Calculus.C2LocallyH1ForcedGaussianEnergy
import EinsteinFull.Calculus.C6GaussianLocalLocalDivergenceTesting
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.C1StationarySpacetimeGaussianL2
import EinsteinFull.Calculus.C1CrudeEnergyLargeTime
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedPower
import EinsteinFull.Calculus.ParabolicLibraryBridgeSignedMaxL2
import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

/- SUPERVISOR EXACT TARGET; replace with its proved declaration.
theorem endpoint_short_time_projection_of_graph_deps :

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
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ t : ℝ≥0, (t : ℝ) ≤ T → (t : ℝ) ≤ 1 → ∀ ρ : ℝ, R ≤ ρ →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (E : Lp ℂ p (reducedLaw Q)),
      (E : FieldPair d → ℂ) =ᵐ[reducedLaw Q] indexedEndpoint hd Q ν ζ P Pdag β a μ t →
      ‖E - EndpointProjection.project
        (m := EinsteinRelation.localSigma {x : Vec d | euclideanNorm x < ρ}) E‖ ≤
        K * Real.exp (-c * ρ ^ 2) := by
-/
/-- Subtraction exposes the actual coefficient defect, including its scalar
force term. This applies to local weak solutions without global spatial L2. -/
theorem short_time_forward_residual_divergence {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (g h : Vec d → ℂ) (Gu Gv : Fin d → Vec d → ℂ)
    (hdiv : ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1/2 : ℂ) * ∑ k, (a x j k : ℂ) * Gu k x))
        (fun x => L (g x - ζ * ∑ j, (a x j i : ℂ) * Gu j x)))
    (hdiv' : ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1/2 : ℂ) * ∑ k, (b x j k : ℂ) * Gv k x))
        (fun x => L (h x - ζ * ∑ j, (b x j i : ℂ) * Gv j x))) :
    ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1/2 : ℂ) * ∑ k, (a x j k : ℂ) * (Gu k x - Gv k x) -
          (-(1/2 : ℂ) * ∑ k, ((a x j k - b x j k : ℝ) : ℂ) * Gv k x)))
        (fun x => L ((g x - h x) -
          ζ * (∑ j, ((a x j i - b x j i : ℝ) : ℂ) * Gv j x) -
          ζ * (∑ j, (a x j i : ℂ) * (Gu j x - Gv j x)))) := by
  intro L
  have hf (x : Vec d) (j : Fin d) :
      (1/2 : ℂ) * ∑ k, (a x j k : ℂ) * (Gu k x - Gv k x) -
          (-(1/2 : ℂ) * ∑ k, ((a x j k - b x j k : ℝ) : ℂ) * Gv k x) =
        (1/2 : ℂ) * (∑ k, (a x j k : ℂ) * Gu k x) -
          (1/2 : ℂ) * (∑ k, (b x j k : ℂ) * Gv k x) := by
    simp only [Complex.ofReal_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  have hq (x : Vec d) :
      (g x - h x) - ζ * (∑ j, ((a x j i - b x j i : ℝ) : ℂ) * Gv j x) -
          ζ * (∑ j, (a x j i : ℂ) * (Gu j x - Gv j x)) =
        (g x - ζ * ∑ j, (a x j i : ℂ) * Gu j x) -
          (h x - ζ * ∑ j, (b x j i : ℂ) * Gv j x) := by
    simp only [Complex.ofReal_sub, mul_sub, sub_mul, Finset.sum_sub_distrib]
    ring
  simpa only [hf, hq, map_sub, Pi.sub_def] using
    Correctors.hasWeakDivergence_sub (hdiv L) (hdiv' L)

private theorem short_time_gaussian_half {d : ℕ} {s : ℝ} (hs : 0 < s)
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

/-- The local Gaussian estimate with a scalar residual as well as a flux
residual. The scalar source costs one copy of the solution energy and its
own square; no global spatial L2 assumption is imposed. -/
theorem short_time_scalar_flux_gaussian_energy
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (u g S : Vec d → ℂ) (G R : Fin d → Vec d → ℂ)
    (hGre : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (u x).re) (fun x => (G j x).re))
    (hGim : ∀ j, HasWeakPartialDerivative Set.univ j (fun x => (u x).im) (fun x => (G j x).im))
    (hdivre : HasWeakDivergence Set.univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).re)
      (fun x => (g x - S x - ζ * (∑ j, (a x j i : ℂ) * G j x)).re))
    (hdivim : HasWeakDivergence Set.univ
      (fun x j => ((1/2 : ℂ) * (∑ k, (a x j k : ℂ) * G k x) - R j x).im)
      (fun x => (g x - S x - ζ * (∑ j, (a x j i : ℂ) * G j x)).im))
    {L r : ℝ} (hΛ : 0 < Λ) (hL : 64 * Λ ^ 3 ≤ L) (hr : 0 < r)
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * u x) 2 volume)
    (hg : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * g x) 2 volume)
    (hS : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * S x) 2 volume)
    (hG : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * G j x) 2 volume)
    (hR : ∀ j, MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * R j x) 2 volume) :
    let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * r))
    let W : Vec d → ℝ := fun x => -2 * euclideanSq x / (L * r ^ 2) * η x ^ 2
    Integrable (fun x => η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ∧
      Integrable (fun x => W x * ‖u x‖ ^ 2) ∧
      2 * (∫ x, g x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re +
        (∫ x, W x * ‖u x‖ ^ 2) +
        (Λ⁻¹ / 4) * (∫ x, η x ^ 2 * ∑ j, ‖G j x‖ ^ 2) ≤
          (16 * Λ ^ 3 * ‖ζ‖ ^ 2 + 1) * (∫ x, η x ^ 2 * ‖u x‖ ^ 2) +
          (4 * Λ + 16 / L) * (∫ x, η x ^ 2 * ∑ j, ‖R j x‖ ^ 2) +
          (∫ x, η x ^ 2 * ‖S x‖ ^ 2) := by
  intro η W
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have shrink (f : Vec d → ℂ)
      (hf : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) * f x) 2 volume) :
      MemLp (fun x => (η x : ℂ) * f x) 2 volume := by
    apply short_time_gaussian_half (mul_pos hLp hr) f
    apply short_time_gaussian_half (by positivity : 0 < 2*(L*r)) f
    convert hf using 1
    funext x
    congr 2
    congr 1
    ring
  have hηu := shrink u hu
  have hηg := shrink g hg
  have hηS := shrink S hS
  have pair (f : Vec d → ℂ) (hf : MemLp (fun x => (η x : ℂ) * f x) 2 volume) :
      Integrable (fun x => f x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))) := by
    convert hf.integrable_mul hηu.star using 1
    funext x
    simp only [Pi.mul_apply, Pi.star_apply, star_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  have square (f : Vec d → ℂ)
      (hf : MemLp (fun x => (η x : ℂ) * f x) 2 volume) :
      Integrable (fun x => η x ^ 2 * ‖f x‖ ^ 2) := by
    convert hf.norm.integrable_sq using 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hsource :
      2 * (∫ x, S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re ≤
        (∫ x, η x ^ 2 * ‖S x‖ ^ 2) + (∫ x, η x ^ 2 * ‖u x‖ ^ 2) := by
    have hSri : (∫ x, (S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re) =
        (∫ x, S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re := integral_re (pair S hηS)
    rw [← hSri, ← integral_const_mul,
      ← integral_add (square S hηS) (square u hηu)]
    apply integral_mono ((pair S hηS).re.const_mul 2)
      ((square S hηS).add (square u hηu))
    intro x
    change 2 * (S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re ≤
      η x ^ 2 * ‖S x‖ ^ 2 + η x ^ 2 * ‖u x‖ ^ 2
    have hb := Complex.re_le_norm (S x * star (u x))
    rw [norm_mul, norm_star] at hb
    have hy : 2 * (S x * star (u x)).re ≤ ‖S x‖ ^ 2 + ‖u x‖ ^ 2 := by
      nlinarith only [hb, sq_nonneg (‖S x‖ - ‖u x‖)]
    have hm := mul_le_mul_of_nonneg_left hy (sq_nonneg (η x))
    have he : S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x)) =
        ((η x ^ 2 : ℝ) : ℂ) * (S x * star (u x)) := by ring
    rw [he, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    nlinarith only [hm]
  have hgS : MemLp (fun x => (Real.exp (-euclideanSq x/(4*L*r)) : ℂ) *
      (g x - S x)) 2 volume := by
    convert hg.sub hS using 1
    funext x
    exact mul_sub _ _ _
  obtain ⟨hGI, hWI, henergy⟩ := physical_locally_h1_forced_gaussian_energy
    a i ζ ha hA u (fun x => g x - S x) G R hGre hGim hdivre hdivim
    hΛ hL hr hu hgS hG hR
  refine ⟨hGI, hWI, ?_⟩
  have heq : (∫ x, (g x - S x) * (((η x ^ 2 : ℝ) : ℂ) * star (u x))) =
      (∫ x, g x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))) -
      (∫ x, S x * (((η x ^ 2 : ℝ) : ℂ) * star (u x))) := by
    simp_rw [sub_mul]
    exact integral_sub (pair g hηg) (pair S hηS)
  change _ ≤ -2 * (∫ x, (g x - S x) * (((η x ^ 2 : ℝ) : ℂ) * star (u x))).re + _ - _ + _ at henergy
  rw [heq, Complex.sub_re] at henergy
  linarith only [henergy, hsource]

/-- The actual stationary generator orbit has a pathwise temporal energy
identity against every absolutely continuous weight. The event precedes the
weight and every compact spatial region; no global spatial L2 is required. -/
theorem short_time_stationary_generator_weighted_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        (P t f) (translate x ω) - f (translate x ω) =
          ∫ s in Icc (0 : ℝ) (t : ℝ), U (s, translate x ω)) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        ∀ᵐ x ∂volume.restrict K,
          let w := fun s => f (translate x ω) + ∫ v in (0 : ℝ)..s, U (v, translate x ω)
          AbsolutelyContinuousOnInterval (fun s => ‖w s‖ ^ 2) 0 (t : ℝ) ∧
          ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η 0 (t : ℝ) →
            (∫ s in (0 : ℝ)..(t : ℝ),
              η s * (2 * (star (w s) * U (s, translate x ω)).re)) =
              η t * ‖(P t f) (translate x ω)‖ ^ 2 -
                η 0 * ‖f (translate x ω)‖ ^ 2 -
                  ∫ s in (0 : ℝ)..(t : ℝ), deriv η s * ‖w s‖ ^ 2 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU, hFTC, _⟩ := hP.exists_ae_physical_generatorFTC hfg
  refine ⟨U, hU, heU, hFTC, ?_⟩
  intro t
  have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) (t : ℝ)
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hU heU)
  filter_upwards [hl, hFTC t] with ω hω hend
  intro K hK
  filter_upwards [(hω K hK).prod_right_ae, ae_restrict_of_ae hend] with x hx he
  have hx' : IntegrableOn (fun s => U (s, translate x ω)) (uIcc (0 : ℝ) (t : ℝ)) := by
    simpa only [IntegrableOn, uIcc_of_le (NNReal.coe_nonneg t)] using! hx
  have he' : f (translate x ω) + (∫ s in (0 : ℝ)..(t : ℝ), U (s, translate x ω)) =
      (P t f) (translate x ω) := by
    rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
      ← integral_Icc_eq_integral_Ioc, ← he]
    exact add_sub_cancel _ _
  refine ⟨(complexPrimitive_energy_regular hx'.intervalIntegrable _).1, ?_⟩
  intro η hη
  simpa only [he'] using complexPrimitive_weighted_energy
    hx'.intervalIntegrable (f (translate x ω)) hη

private theorem short_time_joint_l2_representative {T Ω : Type*}
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

/-- The retained physical evolution has one jointly measurable time-space
representative, also on infinite spatial volume. Only its actual semigroup
continuity is used; no pointwise evaluation of L2 classes is assumed measurable. -/
theorem short_time_physical_evolution_joint_representative
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ U : ℝ × Vec d → ℂ, Measurable U ∧
      ∀ t, (fun x => U (t, x)) =ᵐ[volume] P t.toNNReal f := by
  exact short_time_joint_l2_representative
    (((hP.2.2.1 f).comp continuous_real_toNNReal).stronglyMeasurable)

private theorem short_time_integral_norm_le_l2 {Ω : Type*} [MeasurableSpace Ω]
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

private theorem short_time_integrable_joint_l2_finite {T Ω : Type*}
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
  exact short_time_integral_norm_le_l2 (u t)

private theorem short_time_coeFn_integral_joint_l2_finite {T Ω : Type*}
    [MeasurableSpace T] [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {ν : Measure T} [SFinite ν] {u : T → Lp ℂ 2 μ} (hu : Integrable u ν)
    {U : T × Ω → ℂ} (hU : Measurable U)
    (heq : ∀ t, (fun x => U (t, x)) =ᵐ[μ] u t) :
    (fun x => (∫ t, u t ∂ν) x) =ᵐ[μ] fun x => ∫ t, U (t, x) ∂ν := by
  have hi := short_time_integrable_joint_l2_finite hu hU heq
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
theorem short_time_coeFn_integral_joint_l2_local {T Ω : Type*}
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
  refine ⟨short_time_integrable_joint_l2_finite hC hU hrep, ?_⟩
  have hi := short_time_coeFn_integral_joint_l2_finite hC hU hrep
  rw [C.integral_comp_comm hu] at hi
  exact (LpToLpRestrictCLM_coeFn ℂ K (∫ t, u t ∂ν)).symm.trans hi

private def ShortTimeC0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem ShortTimeC0Graph.hasDerivWithinAt_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    {f g : E} (hfg : ShortTimeC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
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

private theorem ShortTimeC0Graph.integral_orbit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f))
    {f g : E} (hfg : ShortTimeC0Graph P f g) (t : ℝ) (ht : 0 ≤ t) :
    (∫ s in (0 : ℝ)..t, P s.toNNReal g) = P t.toNNReal f - f := by
  have hf := (hPc f).comp continuous_real_toNNReal
  have hg := (hPc g).comp continuous_real_toNNReal
  simpa only [Function.comp_apply, Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using
    intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hf.continuousOn
      (fun s hs => (hfg.hasDerivWithinAt_orbit hPm s hs.1.le).Ioi_of_Ici)
      (hg.intervalIntegrable 0 t)


/-- A generator-domain retained physical orbit has a pathwise temporal primitive
on every finite spatial set, with its actual semigroup value as final trace. -/
theorem short_time_physical_generator_primitive
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ U : ℝ × Vec d → ℂ, Measurable U ∧
      (∀ s, (fun x => U (s, x)) =ᵐ[volume] P s.toNNReal g) ∧
      ∀ (t : ℝ≥0) (K : Set (Vec d)), volume K ≠ ⊤ →
        ∀ᵐ x ∂volume.restrict K,
          IntegrableOn (fun s => U (s, x)) (Icc (0 : ℝ) (t : ℝ)) ∧
          f x + (∫ s in (0 : ℝ)..(t : ℝ), U (s, x)) = (P t f) x := by
  obtain ⟨U, hU, heU⟩ := short_time_physical_evolution_joint_representative hP g
  refine ⟨U, hU, heU, ?_⟩
  let p := fun t : ℝ≥0 => (P t).restrictScalars ℝ
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
  have hgraph : ShortTimeC0Graph p f g := by
    have h := (hP.2.2.2 f g).mpr hfg
    simp only [ShortTimeC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ),
      RCLike.ofReal_inv]
    exact h
  intro t K hK
  have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) (t : ℝ)
  obtain ⟨hint, he⟩ := short_time_coeFn_integral_joint_l2_local hi hU heU K hK
  have hFTC : (∫ s in Icc (0 : ℝ) (t : ℝ), P s.toNNReal g) = P t f - f := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (NNReal.coe_nonneg t)]
    simpa only [p, ContinuousLinearMap.coe_restrictScalars', Real.toNNReal_coe] using
      hgraph.integral_orbit hp0 hpm hpc t (NNReal.coe_nonneg t)
  rw [hFTC] at he
  filter_upwards [hint.prod_left_ae, he, ae_restrict_of_ae (Lp.coeFn_sub (P t f) f)]
    with x hx he hsub
  refine ⟨hx, ?_⟩
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
    ← integral_Icc_eq_integral_Ioc, ← he, hsub]
  exact add_sub_cancel _ _

/-- The actual stationary orbit and any actual retained physical orbit, started
in their generator domains, obey one pathwise weighted temporal energy identity
for their difference. The stationary spatial orbit need only be locally L2. -/
theorem short_time_stationary_retained_generator_weighted_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ U : ℝ × FieldPair d → ℂ, Measurable U ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, ∀ᵐ ω ∂reducedLaw Q,
        ∀ (a : Vec d → Mat d)
          (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexSemigroup a i ζ Pr →
        ∀ fr gr : Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalComplexGeneratorPair a i ζ fr gr →
        ∃ V : ℝ × Vec d → ℂ, Measurable V ∧
          (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
          ∀ K : Set (Vec d), IsCompact K → ∀ᵐ x ∂volume.restrict K,
            let w := fun s => f (translate x ω) - fr x +
              ∫ v in (0 : ℝ)..s, U (v, translate x ω) - V (v, x)
            AbsolutelyContinuousOnInterval (fun s => ‖w s‖ ^ 2) 0 (t : ℝ) ∧
            ∀ η : ℝ → ℝ, AbsolutelyContinuousOnInterval η 0 (t : ℝ) →
              (∫ s in (0 : ℝ)..(t : ℝ), η s *
                (2 * (star (w s) * (U (s, translate x ω) - V (s, x))).re)) =
                η t * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2 -
                  η 0 * ‖f (translate x ω) - fr x‖ ^ 2 -
                    ∫ s in (0 : ℝ)..(t : ℝ), deriv η s * ‖w s‖ ^ 2 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU, hFTC, _⟩ := hP.exists_ae_physical_generatorFTC hfg
  refine ⟨U, hU, heU, ?_⟩
  intro t
  have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) (t : ℝ)
  have hl := ae_locally_integrable_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q)
    (integrable_joint_l2_representative hi hU heU)
  filter_upwards [hl, hFTC t] with ω hω hend
  intro a Pr hPr fr gr hfrgr
  obtain ⟨V, hV, heV, hVFTC⟩ := short_time_physical_generator_primitive hPr hfrgr
  refine ⟨V, hV, heV, ?_⟩
  intro K hK
  filter_upwards [(hω K hK).prod_right_ae, ae_restrict_of_ae hend,
    hVFTC t K hK.measure_ne_top] with x hx he hxV
  have hx' : IntegrableOn (fun s => U (s, translate x ω)) (uIcc (0 : ℝ) (t : ℝ)) := by
    simpa only [IntegrableOn, uIcc_of_le (NNReal.coe_nonneg t)] using! hx
  have hxV' : IntervalIntegrable (fun s => V (s, x)) volume 0 (t : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (NNReal.coe_nonneg t)).mpr hxV.1
  have hdiff := hx'.intervalIntegrable.sub hxV'
  have he' : f (translate x ω) - fr x +
      (∫ s in (0 : ℝ)..(t : ℝ), U (s, translate x ω) - V (s, x)) =
        (P t f) (translate x ω) - (Pr t fr) x := by
    rw [intervalIntegral.integral_sub hx'.intervalIntegrable hxV']
    have heU' : (∫ s in (0 : ℝ)..(t : ℝ), U (s, translate x ω)) =
        (P t f) (translate x ω) - f (translate x ω) := by
      rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg t),
        ← integral_Icc_eq_integral_Ioc, ← he]
    rw [heU']
    linear_combination -hxV.2
  refine ⟨(complexPrimitive_energy_regular hdiff _).1, ?_⟩
  intro η hη
  simpa only [he'] using complexPrimitive_weighted_energy
    hdiff (f (translate x ω) - fr x) hη

private theorem short_time_moving_gaussian_bounds {d : ℕ} (x : Vec d)
    {L s : ℝ} (hL : 0 < L) (hs : s ∈ Icc (0 : ℝ) 1) :
    let η := Real.exp (-euclideanSq x / (L * (2 - s)))
    let γ := Real.exp (-euclideanSq x / (4 * L))
    η ^ 2 ≤ γ ^ 2 ∧
      ‖-2 * euclideanSq x / (L * (2 - s) ^ 2) * η ^ 2‖ ≤ 2 * γ ^ 2 := by
  intro η γ
  have hq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hd : 0 < L * (2 - s) := mul_pos hL (by linarith [hs.2])
  have hη : 0 ≤ η ∧ η ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hd.le)⟩
  have hηγ : η ≤ γ ^ 2 := by
    dsimp only [η, γ]
    rw [pow_two, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hdiv : euclideanSq x / (2 * L) ≤ euclideanSq x / (L * (2 - s)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < 2 * L) hd).mpr
      nlinarith [mul_nonneg hq (mul_nonneg hL.le hs.1)]
    convert neg_le_neg hdiv using 1 <;> ring
  have hqη : euclideanSq x * η ≤ L * (2 - s) := by
    have he := (Real.mul_exp_neg_le_exp_neg_one (euclideanSq x / (L * (2 - s)))).trans
      (Real.exp_le_one_iff.mpr (by norm_num))
    have hm := mul_le_mul_of_nonneg_left he hd.le
    have heq : L * (2 - s) * (euclideanSq x / (L * (2 - s)) *
        Real.exp (-(euclideanSq x / (L * (2 - s))))) = euclideanSq x * η := by
      dsimp only [η]
      rw [neg_div]
      field_simp [ne_of_gt hL, ne_of_gt (by linarith [hs.2] : 0 < 2 - s)]
    simpa only [heq, mul_one] using hm
  refine ⟨(by nlinarith [mul_nonneg hη.1 (sub_nonneg.mpr hη.2)]), ?_⟩
  have hneg : -2 * euclideanSq x / (L * (2 - s) ^ 2) * η ^ 2 ≤ 0 := by
    apply mul_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonpos hneg]
  have heq : -(-2 * euclideanSq x / (L * (2 - s) ^ 2) * η ^ 2) =
      (2 / (L * (2 - s) ^ 2)) * (euclideanSq x * η) * η := by ring
  rw [heq]
  calc
    _ ≤ (2 / (L * (2 - s) ^ 2)) * (L * (2 - s)) * η := by
      gcongr
    _ = (2 / (2 - s)) * η := by
      field_simp [ne_of_gt hL, ne_of_gt (by linarith [hs.2] : 0 < 2 - s)]
    _ ≤ 2 * η := by
      apply mul_le_mul_of_nonneg_right _ hη.1
      apply (div_le_iff₀ (by linarith [hs.2] : 0 < 2 - s)).mpr
      linarith [hs.2]
    _ ≤ 2 * γ ^ 2 := mul_le_mul_of_nonneg_left hηγ (by norm_num)

/-- Wider Gaussian spacetime L2 bounds justify the two spacetime integrals in
the moving Gaussian energy identity, even for spatially nonintegrable orbits. -/
theorem short_time_moving_gaussian_spacetime_integrable
    {d : ℕ} {L T : ℝ} (hL : 0 < L) (hT : T ≤ 1)
    (u v : ℝ × Vec d → ℂ) (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume))
    (hv2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * v p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume)) :
    let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
    let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
    Integrable (fun p => η p ^ 2 * (2 * (star (u p) * v p).re))
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) ∧
    Integrable (fun p => W p * ‖u p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
  intro η W
  let γ : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (4 * L))
  have hηm : Measurable η := by dsimp only [η, euclideanSq, dot]; fun_prop
  have hWm : Measurable W := by dsimp only [W, η, euclideanSq, dot]; fun_prop
  have htime : ∀ᵐ p : ℝ × Vec d ∂((volume.restrict (Icc (0 : ℝ) T)).prod volume),
      p.1 ∈ Icc (0 : ℝ) T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun _ => hs
  have hsquare : Integrable (fun p : ℝ × Vec d => γ p.2 ^ 2 * ‖u p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    convert hu2.norm.integrable_sq using 1
    funext p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hproduct : Integrable (fun p : ℝ × Vec d => γ p.2 ^ 2 * (‖u p‖ * ‖v p‖))
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    convert hu2.norm.integrable_mul hv2.norm using 1
    funext p
    dsimp only [Pi.mul_apply]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    dsimp only [γ]
    ring
  constructor
  · apply (hproduct.const_mul 2).mono'
      (((hηm.pow_const 2).mul
        ((Complex.measurable_re.comp (hu.stronglyMeasurable.star.measurable.mul hv)).const_mul 2)).aestronglyMeasurable)
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 hL ⟨hp.1, hp.2.trans hT⟩).1
    change η p ^ 2 ≤ γ p.2 ^ 2 at hb
    have hz : |(star (u p) * v p).re| ≤ ‖u p‖ * ‖v p‖ := by
      simpa only [norm_mul, norm_star] using Complex.abs_re_le_norm (star (u p) * v p)
    dsimp only [Pi.mul_apply]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _), abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ η p ^ 2 * (2 * (‖u p‖ * ‖v p‖)) := by
        gcongr
        exact hz
      _ ≤ 2 * (γ p.2 ^ 2 * (‖u p‖ * ‖v p‖)) := by nlinarith [mul_nonneg (norm_nonneg (u p)) (norm_nonneg (v p))]
  · apply (hsquare.const_mul 2).mono'
      ((hWm.mul (hu.norm.pow_const 2)).aestronglyMeasurable)
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 hL ⟨hp.1, hp.2.trans hT⟩).2
    change ‖W p‖ ≤ 2 * γ p.2 ^ 2 at hb
    dsimp only [Pi.mul_apply]
    rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg ‖u p‖]

/-- The moving Gaussian energy identity on the whole physical space. Only
Gaussian L2 integrability is required; the orbit need not be in spatial L2. -/
theorem short_time_moving_gaussian_primitive_energy
    {d : ℕ} {L T : ℝ} (hL : 0 < L) (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (u v : ℝ × Vec d → ℂ) (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume))
    (hv2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * v p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume))
    (hend : ∀ s ∈ ({0, T} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * u (s, x)) 2 volume)
    (hprimitive : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => v (s, x)) volume 0 T ∧
      ∀ s ∈ Icc (0 : ℝ) T, u (s, x) = u (0, x) + ∫ r in (0 : ℝ)..s, v (r, x)) :
    let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
    let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
    (∫ s in Icc (0 : ℝ) T, ∫ x, η (s, x) ^ 2 * (2 * (star (u (s, x)) * v (s, x)).re)) =
      (∫ x, η (T, x) ^ 2 * ‖u (T, x)‖ ^ 2) -
      (∫ x, η (0, x) ^ 2 * ‖u (0, x)‖ ^ 2) -
      ∫ s in Icc (0 : ℝ) T, ∫ x, W (s, x) * ‖u (s, x)‖ ^ 2 := by
  intro η W
  obtain ⟨hA, hB⟩ := short_time_moving_gaussian_spacetime_integrable hL hT1 u v hu hv hu2 hv2
  let A : ℝ × Vec d → ℝ := fun p => η p ^ 2 * (2 * (star (u p) * v p).re)
  let B : ℝ × Vec d → ℝ := fun p => W p * ‖u p‖ ^ 2
  change Integrable A _ at hA
  change Integrable B _ at hB
  have hηderiv (x : Vec d) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun r => η (r, x) ^ 2) (W (s, x)) s := by
    have hs2 : s < 2 := by linarith [hs.2]
    have hr : L * (2 - s) ≠ 0 := ne_of_gt (mul_pos hL (sub_pos.mpr hs2))
    have hden := ((hasDerivAt_const s (2 : ℝ)).sub (hasDerivAt_id s)).const_mul L
    have hq := ((hasDerivAt_const s (-euclideanSq x)).div hden hr).exp.pow 2
    convert hq using 1
    · rfl
    · dsimp only [W, η]
      dsimp
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs2)]
      ring
  have hηac (x : Vec d) : AbsolutelyContinuousOnInterval (fun s => η (s, x) ^ 2) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    dsimp only [η]
    have hnonzero : ∀ s ∈ uIcc (0 : ℝ) T, L * (2 - s) ≠ 0 := by
      rw [uIcc_of_le hT0]
      intro s hs
      exact ne_of_gt (mul_pos hL (by linarith [hs.2]))
    fun_prop (disch := aesop)
  have hends (s : ℝ) (hs : s ∈ ({0, T} : Set ℝ)) (hsI : s ∈ Icc (0 : ℝ) T) :
      Integrable (fun x => η (s, x) ^ 2 * ‖u (s, x)‖ ^ 2) volume := by
    have hi := (hend s hs).norm.integrable_sq
    apply hi.mono' ?_ ?_
    · exact ((by dsimp only [η, euclideanSq, dot]; fun_prop :
        Measurable (fun x => η (s, x) ^ 2)).mul
        ((hu.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2)).aestronglyMeasurable
    · filter_upwards with x
      have hb := (short_time_moving_gaussian_bounds x hL ⟨hsI.1, hsI.2.trans hT1⟩).1
      rw [norm_mul, Real.norm_of_nonneg (sq_nonneg _), Real.norm_of_nonneg (sq_nonneg _)]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have heq : ∀ᵐ x ∂volume, (∫ s in Icc (0 : ℝ) T, A (s, x)) =
      η (T, x) ^ 2 * ‖u (T, x)‖ ^ 2 - η (0, x) ^ 2 * ‖u (0, x)‖ ^ 2 -
      ∫ s in Icc (0 : ℝ) T, B (s, x) := by
    filter_upwards [hprimitive] with x hx
    have he := complexPrimitive_weighted_energy hx.1 (u (0, x)) (hηac x)
    dsimp only at he
    rw [← hx.2 T ⟨hT0, le_rfl⟩] at he
    rw [intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc] at he
    have hprim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := hx.2 s hs
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := (hηderiv x s hs).deriv
    dsimp only [A, B]
    convert he using 1
    · apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [← hprim s hs]
    · congr 1
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [← hprim s hs, hd s hs]
  calc
    _ = ∫ x, ∫ s in Icc (0 : ℝ) T, A (s, x) := integral_integral_swap hA
    _ = _ := by
      have hsplit := integral_sub ((hends T (by simp) ⟨hT0, le_rfl⟩).sub
        (hends 0 (by simp) ⟨le_rfl, hT0⟩)) hB.integral_prod_right
      have hsplitEnds := integral_sub (hends T (by simp) ⟨hT0, le_rfl⟩)
        (hends 0 (by simp) ⟨le_rfl, hT0⟩)
      simp only [Pi.sub_apply] at hsplit hsplitEnds
      rw [integral_congr_ae heq, hsplit, hsplitEnds, ← integral_integral_swap hB]

/-- A jointly measurable primitive representative of the actual stationary
semigroup orbit, constructed from its generator orbit. -/
theorem short_time_stationary_joint_primitive
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ s ω, F (s, ω) = f ω + ∫ r in Icc (0 : ℝ) s, U (r, ω) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨U, hU, heU⟩ := short_time_joint_l2_representative
    (((hP.2.2.1 g).comp continuous_real_toNNReal).stronglyMeasurable)
  let F : ℝ × FieldPair d → ℂ := fun p => f p.2 + ∫ r in Icc (0 : ℝ) p.1, U (r, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hU 0)
  refine ⟨F, U, hF, hU, ?_, heU, fun _ _ => rfl⟩
  intro s
  by_cases hs : 0 ≤ s
  · have hi := integrableOn_comp_toNNReal_Icc _ (hP.2.2.1 g) s
    have he := short_time_coeFn_integral_joint_l2_finite hi hU heU
    have hFTC : (∫ r in Icc (0 : ℝ) s, P r.toNNReal g) = P s.toNNReal f - f := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
      simpa only [Real.coe_toNNReal _ hs, Real.toNNReal_coe] using
        hP.w6_integral_generator_orbit hfg s.toNNReal
    rw [hFTC] at he
    filter_upwards [he, Lp.coeFn_sub (P s.toNNReal f) f] with ω he hsub
    dsimp only [F]
    rw [← he, hsub]
    exact add_sub_cancel _ _
  · have hs0 : s.toNNReal = 0 := Real.toNNReal_eq_zero.mpr (le_of_not_ge hs)
    have hI : Icc (0 : ℝ) s = ∅ := Icc_eq_empty_of_lt (lt_of_not_ge hs)
    exact ae_of_all _ fun ω => by simp [F, hI, hs0, hP.1]

private theorem short_time_gaussian_time_integrable {d : ℕ} {L T : ℝ}
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

/-- Whole-space moving Gaussian temporal energy for the actual stationary
semigroup, with a primitive representative and the literal final orbit trace. -/
theorem short_time_stationary_moving_gaussian_energy
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        let W : ℝ × Vec d → ℝ := fun p =>
          -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
        (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, η (s, x) ^ 2 *
          (2 * (star (F (s, translate x ω)) * U (s, translate x ω)).re)) =
          (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω)‖ ^ 2) -
          (∫ x, η (0, x) ^ 2 * ‖f (translate x ω)‖ ^ 2) -
          ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, W (s, x) * ‖F (s, translate x ω)‖ ^ 2 := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  intro t ht
  have hFi : Integrable (fun p => ‖F p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hF heF
  have hUi : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (t : ℝ))).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hFi
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg U hU hUi
  have heT := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hF.comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (P t f)).measurable
    (by
      filter_upwards [heF (t : ℝ)] with ω hω
      simpa only [Function.comp_apply, id_eq, Real.toNNReal_coe] using hω)
  filter_upwards [hFG, hUG, heT,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (P t f)] with ω hFω hUω heω hfω htω
  simp only [Function.comp_apply, id_eq] at heω
  intro L hL η W
  let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω)
  let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω)
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := hF.comp hshift
  have hY : Measurable Y := hU.comp hshift
  have hX0 (x : Vec d) : X (0, x) = f (translate x ω) := by
    simpa [X] using hprim 0 (translate x ω)
  have hends : ∀ s ∈ ({0, (t : ℝ)} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * X (s, x)) 2 volume := by
    intro s hs
    rcases hs with hs | hs
    · subst s
      simpa only [hX0] using hfω (4 * L) (by positivity)
    · have hs' : s = (t : ℝ) := hs
      subst s
      apply (htω (4 * L) (by positivity)).ae_eq
      filter_upwards [heω] with x hx
      rw [← hx]
  have hY2 := hUω (4 * L) (by positivity)
  have hsample : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => Y (s, x)) volume 0 (t : ℝ) ∧
      ∀ s ∈ Icc (0 : ℝ) (t : ℝ), X (s, x) = X (0, x) + ∫ r in (0 : ℝ)..s, Y (r, x) := by
    filter_upwards [short_time_gaussian_time_integrable Y hY hY2] with x hx
    refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg).mpr hx, ?_⟩
    intro s hs
    rw [hX0, intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    exact hprim s (translate x ω)
  have he := short_time_moving_gaussian_primitive_energy hL t.coe_nonneg ht X Y hX hY
    (hFω (4 * L) (by positivity)) hY2 hends hsample
  dsimp only at he
  rw [he]
  congr 2
  · apply integral_congr_ae
    filter_upwards [heω] with x hx
    change η (t, x) ^ 2 * ‖F ((t : ℝ), translate x ω)‖ ^ 2 = _
    rw [hx]
  · change (∫ x, η (0, x) ^ 2 * ‖X (0, x)‖ ^ 2) = _
    simp only [hX0]

/-- A physical generator orbit admits a jointly measurable primitive on all
of space, obtained from its finite-volume traces without a finite-volume premise. -/
theorem short_time_physical_joint_primitive
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ F U : ℝ × Vec d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun x => F (s, x)) =ᵐ[volume] P s.toNNReal f) ∧
      (∀ s, (fun x => U (s, x)) =ᵐ[volume] P s.toNNReal g) ∧
      ∀ s x, F (s, x) = f x + ∫ r in Icc (0 : ℝ) s, U (r, x) := by
  obtain ⟨U, hU, heU, hsample⟩ := short_time_physical_generator_primitive hP hfg
  let F : ℝ × Vec d → ℂ := fun p => f p.2 + ∫ r in Icc (0 : ℝ) p.1, U (r, p.2)
  have hF : Measurable F :=
    ((Lp.stronglyMeasurable f).measurable.comp measurable_snd).add
      (measurable_complexPrimitive hU 0)
  refine ⟨F, U, hF, hU, ?_, heU, fun _ _ => rfl⟩
  intro s
  by_cases hs : 0 ≤ s
  · have he : ∀ᵐ x ∂(volume : Measure (Vec d)),
        f x + (∫ r in (0 : ℝ)..s, U (r, x)) = (P s.toNNReal f) x := by
      have he' : ∀ᵐ x ∂(volume : Measure (Vec d)).restrict
          (⋃ n, spanningSets (volume : Measure (Vec d)) n),
          f x + (∫ r in (0 : ℝ)..s, U (r, x)) = (P s.toNNReal f) x := by
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

private theorem short_time_integrable_sq_joint_l2 {T Ω : Type*}
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

private theorem short_time_gaussian_mul_memLp {d : ℕ} {r : ℝ} (hr : 0 < r)
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

/-- Whole-space moving Gaussian energy for an actual physical generator orbit,
with no finite-volume restriction on the primitive or final trace. -/
theorem short_time_physical_moving_gaussian_energy
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g) :
    ∃ F U : ℝ × Vec d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun x => F (s, x)) =ᵐ[volume] P s.toNNReal f) ∧
      (∀ s, (fun x => U (s, x)) =ᵐ[volume] P s.toNNReal g) ∧
      ∀ (t : ℝ≥0), (t : ℝ) ≤ 1 → ∀ L : ℝ, 0 < L →
        let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
        let W : ℝ × Vec d → ℝ := fun p =>
          -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
        (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, η (s, x) ^ 2 *
          (2 * (star (F (s, x)) * U (s, x)).re)) =
          (∫ x, η (t, x) ^ 2 * ‖(P t f) x‖ ^ 2) -
          (∫ x, η (0, x) ^ 2 * ‖f x‖ ^ 2) -
          ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, W (s, x) * ‖F (s, x)‖ ^ 2 := by
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_physical_joint_primitive hP hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  intro t ht L hL η W
  have hFi := short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (K := Icc (0 : ℝ) (t : ℝ)) isCompact_Icc) hF heF
  have hUi := short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      (K := Icc (0 : ℝ) (t : ℝ)) isCompact_Icc) hU heU
  have hF2 := short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hF
    ((memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr hFi)
  have hU2 := short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hU
    ((memLp_two_iff_integrable_sq_norm hU.aestronglyMeasurable).mpr hUi)
  have hF0 (x : Vec d) : F (0, x) = f x := by simpa using hprim 0 x
  have hq : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hends : ∀ s ∈ ({0, (t : ℝ)} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * F (s, x)) 2 volume := by
    intro s _
    exact (Lp.memLp (P s.toNNReal f)).of_le
      ((Complex.measurable_ofReal.comp
        (Real.continuous_exp.comp (hq.neg.div_const (4 * L))).measurable).mul
        (hF.comp (measurable_const.prodMk measurable_id))).aestronglyMeasurable (by
          filter_upwards [heF s] with x hx
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), hx]
          apply mul_le_of_le_one_left (norm_nonneg _)
          apply Real.exp_le_one_iff.mpr
          apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
          apply neg_nonpos.mpr
          change 0 ≤ ∑ j : Fin d, x j * x j
          exact Finset.sum_nonneg fun j _ => mul_self_nonneg _)
  have hsample : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => U (s, x)) volume 0 (t : ℝ) ∧
      ∀ s ∈ Icc (0 : ℝ) (t : ℝ), F (s, x) = F (0, x) + ∫ r in (0 : ℝ)..s, U (r, x) := by
    filter_upwards [short_time_gaussian_time_integrable U hU hU2] with x hx
    refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le t.coe_nonneg).mpr hx, ?_⟩
    intro s hs
    rw [hF0, intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    exact hprim s x
  have he := short_time_moving_gaussian_primitive_energy hL t.coe_nonneg ht F U hF hU
    hF2 hU2 hends hsample
  dsimp only at he
  rw [he]
  congr 2
  · apply integral_congr_ae
    filter_upwards [heF (t : ℝ)] with x hx
    simpa only [Real.toNNReal_coe] using congrArg (fun z : ℂ => η (t, x) ^ 2 * ‖z‖ ^ 2) hx
  · change (∫ x, η (0, x) ^ 2 * ‖F (0, x)‖ ^ 2) = _
    simp only [hF0]

private theorem short_time_gaussian_spatial_mul_memLp {d : ℕ} {r : ℝ} (hr : 0 < r)
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

/-- Exponential damping of the moving-Gaussian primitive identity. The damping
constant is independent of the spatial representative and requires only weighted L2. -/
theorem short_time_damped_moving_gaussian_primitive_energy
    {d : ℕ} {L T : ℝ} (hL : 0 < L) (hT0 : 0 ≤ T) (hT1 : T ≤ 1) (γ : ℝ) (hγ : 0 ≤ γ)
    (u v : ℝ × Vec d → ℂ) (hu : Measurable u) (hv : Measurable v)
    (hu2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * u p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume))
    (hv2 : MemLp (fun p => (Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) * v p) 2
      ((volume.restrict (Icc (0 : ℝ) T)).prod volume))
    (hend : ∀ s ∈ ({0, T} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * u (s, x)) 2 volume)
    (hprimitive : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => v (s, x)) volume 0 T ∧
      ∀ s ∈ Icc (0 : ℝ) T, u (s, x) = u (0, x) + ∫ r in (0 : ℝ)..s, v (r, x)) :
    let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
    let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
    (∫ s in Icc (0 : ℝ) T, ∫ x, Real.exp (-γ * s) * (η (s, x) ^ 2 * (2 * (star (u (s, x)) * v (s, x)).re) -
      γ * (η (s, x) ^ 2 * ‖u (s, x)‖ ^ 2))) =
      Real.exp (-γ * T) * (∫ x, η (T, x) ^ 2 * ‖u (T, x)‖ ^ 2) -
      (∫ x, η (0, x) ^ 2 * ‖u (0, x)‖ ^ 2) -
      ∫ s in Icc (0 : ℝ) T, ∫ x, Real.exp (-γ * s) * (W (s, x) * ‖u (s, x)‖ ^ 2) := by
  intro η W
  obtain ⟨hA, hB⟩ := short_time_moving_gaussian_spacetime_integrable hL hT1 u v hu hv hu2 hv2
  let m : ℝ → ℝ := fun s => Real.exp (-γ * s)
  let C : ℝ × Vec d → ℝ := fun p => η p ^ 2 * ‖u p‖ ^ 2
  have hm (s : ℝ) (hs : 0 ≤ s) : 0 ≤ m s ∧ m s ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hs)⟩
  have htime : ∀ᵐ p : ℝ × Vec d ∂((volume.restrict (Icc (0 : ℝ) T)).prod volume),
      p.1 ∈ Icc (0 : ℝ) T := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun _ => hs
  have hC : Integrable C ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    apply hu2.norm.integrable_sq.mono'
      (((by dsimp only [η, euclideanSq, dot]; fun_prop : Measurable (fun p : ℝ × Vec d => η p ^ 2)).mul
        (hu.norm.pow_const 2)).aestronglyMeasurable)
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 hL ⟨hp.1, hp.2.trans hT1⟩).1
    change ‖η p ^ 2 * ‖u p‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have damp (f : ℝ × Vec d → ℝ)
      (hf : Integrable f ((volume.restrict (Icc (0 : ℝ) T)).prod volume)) :
      Integrable (fun p => m p.1 * f p) ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := by
    apply hf.norm.mono' (((by dsimp only [m]; fun_prop : Measurable (fun p : ℝ × Vec d => m p.1)).aestronglyMeasurable).mul hf.aestronglyMeasurable)
    filter_upwards [htime] with p hp
    change ‖m p.1 * f p‖ ≤ ‖f p‖
    rw [norm_mul, Real.norm_of_nonneg (hm p.1 hp.1).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (hm p.1 hp.1).2
  let A : ℝ × Vec d → ℝ := fun p => m p.1 *
    (η p ^ 2 * (2 * (star (u p) * v p).re) - γ * C p)
  let B : ℝ × Vec d → ℝ := fun p => m p.1 * (W p * ‖u p‖ ^ 2)
  have hAi : Integrable A ((volume.restrict (Icc (0 : ℝ) T)).prod volume) :=
    damp _ (hA.sub (hC.const_mul γ))
  have hBi : Integrable B ((volume.restrict (Icc (0 : ℝ) T)).prod volume) := damp _ hB
  have hηderiv (x : Vec d) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun r => m r * η (r, x) ^ 2)
        (m s * (W (s, x) - γ * η (s, x) ^ 2)) s := by
    have hs2 : s < 2 := by linarith [hs.2]
    have hr : L * (2 - s) ≠ 0 := ne_of_gt (mul_pos hL (sub_pos.mpr hs2))
    have hden := ((hasDerivAt_const s (2 : ℝ)).sub (hasDerivAt_id s)).const_mul L
    have hq := ((hasDerivAt_const s (-euclideanSq x)).div hden hr).exp.pow 2
    have he := (((hasDerivAt_id s).const_mul (-γ)).exp).mul hq
    convert he using 1
    · rfl
    · dsimp only [m, W, η]
      dsimp
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hs2)]
      ring
  have hηac (x : Vec d) : AbsolutelyContinuousOnInterval (fun s => m s * η (s, x) ^ 2) 0 T := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    dsimp only [m, η]
    have hnonzero : ∀ s ∈ uIcc (0 : ℝ) T, L * (2 - s) ≠ 0 := by
      rw [uIcc_of_le hT0]
      intro s hs
      exact ne_of_gt (mul_pos hL (by linarith [hs.2]))
    fun_prop (disch := aesop)
  have hends (s : ℝ) (hs : s ∈ ({0, T} : Set ℝ)) (hsI : s ∈ Icc (0 : ℝ) T) :
      Integrable (fun x => m s * η (s, x) ^ 2 * ‖u (s, x)‖ ^ 2) volume := by
    have hi := (hend s hs).norm.integrable_sq
    apply hi.mono' ?_ ?_
    · exact ((by dsimp only [m, η, euclideanSq, dot]; fun_prop :
        Measurable (fun x => m s * η (s, x) ^ 2)).mul
        ((hu.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2)).aestronglyMeasurable
    · filter_upwards with x
      have hb := (short_time_moving_gaussian_bounds x hL ⟨hsI.1, hsI.2.trans hT1⟩).1
      rw [Real.norm_of_nonneg (by positivity : 0 ≤ m s * η (s, x) ^ 2 * ‖u (s, x)‖ ^ 2),
        norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      exact (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (sq_nonneg _) (hm s hsI.1).2)
        (sq_nonneg _)).trans (mul_le_mul_of_nonneg_right hb (sq_nonneg _))
  have hD := damp _ (hC.const_mul γ)
  have hOriginalA := damp _ hA
  have heq : ∀ᵐ x ∂volume, (∫ s in Icc (0 : ℝ) T, A (s, x)) =
      m T * η (T, x) ^ 2 * ‖u (T, x)‖ ^ 2 - η (0, x) ^ 2 * ‖u (0, x)‖ ^ 2 -
      ∫ s in Icc (0 : ℝ) T, B (s, x) := by
    filter_upwards [hprimitive, hD.prod_left_ae, hOriginalA.prod_left_ae,
      hBi.prod_left_ae] with x hx hDx hAx hBx
    have he := complexPrimitive_weighted_energy hx.1 (u (0, x)) (hηac x)
    dsimp only at he
    rw [← hx.2 T ⟨hT0, le_rfl⟩] at he
    rw [intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hT0, ← integral_Icc_eq_integral_Ioc] at he
    have hprim (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := hx.2 s hs
    have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) := (hηderiv x s hs).deriv
    have hright : (∫ s in Icc (0 : ℝ) T, B (s, x) - m s * (γ * C (s, x))) =
        (∫ s in Icc (0 : ℝ) T, B (s, x)) -
        (∫ s in Icc (0 : ℝ) T, m s * (γ * C (s, x))) := integral_sub hBx hDx
    have heleft : (∫ s in Icc (0 : ℝ) T, m s * η (s, x) ^ 2 *
        (2 * (star (u (s, x)) * v (s, x)).re)) =
        m T * η (T, x) ^ 2 * ‖u (T, x)‖ ^ 2 - η (0, x) ^ 2 * ‖u (0, x)‖ ^ 2 -
        (∫ s in Icc (0 : ℝ) T, B (s, x) - m s * (γ * C (s, x))) := by
      convert he using 1
      · apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only
        rw [← hprim s hs]
      · simp only [m, mul_zero, Real.exp_zero, one_mul]
        congr 1
        apply setIntegral_congr_fun measurableSet_Icc
        intro s hs
        dsimp only
        rw [hd s hs, ← hprim s hs]
        dsimp only [B, C]
        ring
    have hAi' : Integrable (fun s => A (s, x)) (volume.restrict (Icc (0 : ℝ) T)) := by
      convert hAx.sub hDx using 1
      funext s
      dsimp only [A, Pi.sub_apply, η]
      ring
    have hleft' : (∫ s in Icc (0 : ℝ) T, m s * η (s, x) ^ 2 *
        (2 * (star (u (s, x)) * v (s, x)).re)) =
        (∫ s in Icc (0 : ℝ) T, A (s, x)) +
        (∫ s in Icc (0 : ℝ) T, m s * (γ * C (s, x))) := by
      rw [← integral_add hAi' hDx]
      apply integral_congr_ae
      exact Eventually.of_forall fun s => by dsimp only [A]; ring
    rw [hleft', hright] at heleft
    linarith only [heleft]
  calc
    _ = ∫ x, ∫ s in Icc (0 : ℝ) T, A (s, x) := integral_integral_swap hAi
    _ = _ := by
      have hsplit := integral_sub ((hends T (by simp) ⟨hT0, le_rfl⟩).sub
        (by simpa only [m, mul_zero, Real.exp_zero, one_mul] using hends 0 (by simp) ⟨le_rfl, hT0⟩)) hBi.integral_prod_right
      have hsplitEnds := integral_sub (hends T (by simp) ⟨hT0, le_rfl⟩)
        (by simpa only [m, mul_zero, Real.exp_zero, one_mul] using hends 0 (by simp) ⟨le_rfl, hT0⟩)
      simp only [Pi.sub_apply] at hsplit hsplitEnds
      rw [integral_congr_ae heq, hsplit, hsplitEnds, ← integral_integral_swap hBi]
      simp only [B, m, mul_assoc, integral_const_mul]

/-- The actual stationary-minus-physical orbit satisfies damped whole-space Gaussian
energy on an event chosen before the physical coefficients, orbit, width and damping. -/
theorem short_time_stationary_physical_damped_moving_gaussian_energy
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ (a : Vec d → Mat d)
          (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexSemigroup a i ζ Pr →
        ∀ (fr gr : Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexGeneratorPair a i ζ fr gr →
        ∃ V Z : ℝ × Vec d → ℂ, Measurable V ∧ Measurable Z ∧
          (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
          (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
          ∀ L : ℝ, 0 < L → ∀ γ : ℝ, 0 ≤ γ →
          let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
          let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω) - Z p
          let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
          let W : ℝ × Vec d → ℝ := fun p =>
            -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
          (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
            (η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
              γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) =
            Real.exp (-γ * (t : ℝ)) * (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) -
            (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) -
            ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, Real.exp (-γ * s) *
              (W (s, x) * ‖X (s, x)‖ ^ 2) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  intro t ht
  have hFi := short_time_integrable_sq_joint_l2
    (μ := reducedLaw Q) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hF heF
  have hUi := short_time_integrable_sq_joint_l2
    (μ := reducedLaw Q) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hU heU
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg F hF hFi
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (t : ℝ) t.coe_nonneg U hU hUi
  have heT := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hF.comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (P t f)).measurable
    (by
      filter_upwards [heF (t : ℝ)] with ω hω
      simpa only [Function.comp_apply, id_eq, Real.toNNReal_coe] using hω)
  filter_upwards [hFG, hUG, heT,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (P t f)] with ω hFω hUω heω hfω htω
  simp only [Function.comp_apply, id_eq] at heω
  intro a Pr hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, hprimR⟩ := short_time_physical_joint_primitive hPr hfr
  refine ⟨V, Z, hV, hZ, heV, heZ, ?_⟩
  intro L hL γ hγ X Y η W
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := (hF.comp hshift).sub hV
  have hY : Measurable Y := (hU.comp hshift).sub hZ
  have hVi := short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPr.2.2.1 fr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hV heV
  have hZi := short_time_integrable_sq_joint_l2
    (μ := (volume : Measure (Vec d))) (ν := volume.restrict (Icc (0 : ℝ) (t : ℝ)))
    ((((hPr.2.2.1 gr).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
      isCompact_Icc) hZ heZ
  have hV2 := short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hV
    ((memLp_two_iff_integrable_sq_norm hV.aestronglyMeasurable).mpr hVi)
  have hZ2 := short_time_gaussian_mul_memLp (r := 4 * L) (by positivity) hZ
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
    have hVs := short_time_gaussian_spatial_mul_memLp (r := 4 * L) (by positivity)
      (hV.comp (measurable_const.prodMk measurable_id))
      ((Lp.memLp (Pr s.toNNReal fr)).ae_eq (heV s).symm)
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
    filter_upwards [short_time_gaussian_time_integrable
      (fun p => U (p.1, translate p.2 ω)) (hU.comp hshift) (hUω (4 * L) (by positivity)),
      short_time_gaussian_time_integrable Z hZ hZ2] with x hx hz
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
      (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) := by
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

/-- The actual stationary-minus-physical orbit satisfies whole-space Gaussian
energy on an event chosen before the physical coefficients, orbit and width. -/
theorem short_time_stationary_physical_moving_gaussian_energy
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
        ∀ (a : Vec d → Mat d)
          (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexSemigroup a i ζ Pr →
        ∀ (fr gr : Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexGeneratorPair a i ζ fr gr →
        ∃ V Z : ℝ × Vec d → ℂ, Measurable V ∧ Measurable Z ∧
          (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) ∧
          (∀ s, (fun x => Z (s, x)) =ᵐ[volume] Pr s.toNNReal gr) ∧
          ∀ L : ℝ, 0 < L →
          let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω) - V p
          let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω) - Z p
          let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
          let W : ℝ × Vec d → ℝ := fun p =>
            -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
          (∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, η (s, x) ^ 2 *
            (2 * (star (X (s, x)) * Y (s, x)).re)) =
            (∫ x, η (t, x) ^ 2 * ‖(P t f) (translate x ω) - (Pr t fr) x‖ ^ 2) -
            (∫ x, η (0, x) ^ 2 * ‖f (translate x ω) - fr x‖ ^ 2) -
            ∫ s in Icc (0 : ℝ) (t : ℝ), ∫ x, W (s, x) * ‖X (s, x)‖ ^ 2 := by
  obtain ⟨F, U, hF, hU, heF, heU, hmain⟩ :=
    short_time_stationary_physical_damped_moving_gaussian_energy hd hP hfg
  refine ⟨F, U, hF, hU, heF, heU, ?_⟩
  intro t ht
  filter_upwards [hmain t ht] with ω hω
  intro a Pr hPr fr gr hfr
  obtain ⟨V, Z, hV, hZ, heV, heZ, hbound⟩ := hω a Pr hPr fr gr hfr
  refine ⟨V, Z, hV, hZ, heV, heZ, ?_⟩
  intro L hL
  simpa only [neg_zero, zero_mul, Real.exp_zero, one_mul, sub_zero] using
    hbound L hL 0 le_rfl

/-- Exterior forcing gains an exponential radius factor even when the source
has only Gaussian-weighted integrability on the whole space. -/
theorem short_time_gaussian_exterior_weighted_source {d : ℕ}
    (R L t : ℝ) (hR : 0 ≤ R) (hL : 0 < L) (ht : t ∈ Icc (0 : ℝ) 1)
    (f : Vec d → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hfi : Integrable (fun x => Real.exp (-euclideanSq x / (2 * L)) * f x)) :
    Integrable (fun x => Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * f x) ∧
      (∫ x in {x : Vec d | R ≤ euclideanNorm x},
        Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * f x) ≤
        Real.exp (-R ^ 2 / (2 * L)) *
          (∫ x, Real.exp (-euclideanSq x / (2 * L)) * f x) := by
  let η : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (L * (2 - t)))
  let γ : Vec d → ℝ := fun x => Real.exp (-euclideanSq x / (2 * L))
  have hden : 0 < L * (2 - t) := mul_pos hL (by linarith [ht.2])
  have hq (x : Vec d) : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hγ (x : Vec d) : 0 ≤ γ x ∧ γ x ≤ 1 :=
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hq x)) (by positivity))⟩
  have hcore (x : Vec d) : η x ^ 2 ≤ γ x * γ x := by
    have hd : euclideanSq x / L ≤ 2 * euclideanSq x / (L * (2 - t)) := by
      apply (div_le_div_iff₀ hL hden).mpr
      nlinarith [mul_nonneg (mul_nonneg (hq x) hL.le) ht.1]
    dsimp only [η, γ]
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hd using 1 <;> ring
  have hηc : Continuous η := by
    dsimp only [η, euclideanSq, dot]
    fun_prop
  have hi : Integrable (fun x => η x ^ 2 * f x) := by
    apply hfi.mono' ((hηc.pow 2).measurable.mul hf).aestronglyMeasurable
    filter_upwards with x
    change ‖η x ^ 2 * f x‖ ≤ γ x * f x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hf0 x))]
    exact mul_le_mul_of_nonneg_right ((hcore x).trans
      (mul_le_of_le_one_right (hγ x).1 (hγ x).2)) (hf0 x)
  refine ⟨hi, ?_⟩
  have htail (x : Vec d) (hx : R ≤ euclideanNorm x) :
      η x ^ 2 ≤ Real.exp (-R ^ 2 / (2 * L)) * γ x := by
    have hn : euclideanNorm x ^ 2 = euclideanSq x := Real.sq_sqrt (hq x)
    have hsq : R ^ 2 ≤ euclideanSq x := by nlinarith
    have hg : γ x ≤ Real.exp (-R ^ 2 / (2 * L)) := by
      apply Real.exp_le_exp.mpr
      exact div_le_div_of_nonneg_right (neg_le_neg hsq) (by positivity)
    exact (hcore x).trans (mul_le_mul_of_nonneg_right hg (hγ x).1)
  have hset : MeasurableSet {x : Vec d | R ≤ euclideanNorm x} := by
    apply isClosed_le continuous_const ?_ |>.measurableSet
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hm : (∫ x in {x : Vec d | R ≤ euclideanNorm x}, η x ^ 2 * f x) ≤
      ∫ x in {x : Vec d | R ≤ euclideanNorm x},
        Real.exp (-R ^ 2 / (2 * L)) * (γ x * f x) := by
    apply integral_mono_ae hi.integrableOn (hfi.const_mul _).integrableOn
    filter_upwards [ae_restrict_mem hset] with x hx
    exact (mul_le_mul_of_nonneg_right (htail x hx) (hf0 x)).trans_eq (mul_assoc _ _ _)
  rw [integral_const_mul] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (setIntegral_le_integral hfi (ae_of_all _ fun x => mul_nonneg (hγ x).1 (hf0 x)))
    (Real.exp_nonneg _))

/-- The exterior Gaussian gain survives time integration with only weighted
space-time integrability, as required for stationary spatial source orbits. -/
theorem short_time_gaussian_exterior_spacetime_source {d : ℕ}
    (R L : ℝ) (T : ℝ≥0) (hR : 0 ≤ R) (hL : 0 < L) (hT : (T : ℝ) ≤ 1)
    (f : ℝ × Vec d → ℝ) (hf : Measurable f) (hf0 : ∀ p, 0 ≤ f p)
    (hfi : Integrable (fun p => Real.exp (-euclideanSq p.2 / (2 * L)) * f p)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume)) :
    IntegrableOn (fun t => ∫ x in {x : Vec d | R ≤ euclideanNorm x},
      Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * f (t, x))
        (Icc (0 : ℝ) (T : ℝ)) ∧
      (∫ t in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : Vec d | R ≤ euclideanNorm x},
        Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * f (t, x)) ≤
        Real.exp (-R ^ 2 / (2 * L)) *
          (∫ t in Icc (0 : ℝ) (T : ℝ), ∫ x,
            Real.exp (-euclideanSq x / (2 * L)) * f (t, x)) := by
  let H : ℝ → ℝ := fun t => ∫ x in {x : Vec d | R ≤ euclideanNorm x},
    Real.exp (-euclideanSq x / (L * (2 - t))) ^ 2 * f (t, x)
  let G : ℝ → ℝ := fun t => ∫ x, Real.exp (-euclideanSq x / (2 * L)) * f (t, x)
  have hH0 (t : ℝ) : 0 ≤ H t :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hf0 (t, x))
  have hbound : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) (T : ℝ)),
      H t ≤ Real.exp (-R ^ 2 / (2 * L)) * G t := by
    filter_upwards [hfi.prod_right_ae, ae_restrict_mem measurableSet_Icc] with t hft ht
    exact (short_time_gaussian_exterior_weighted_source R L t hR hL
      ⟨ht.1, ht.2.trans hT⟩ (fun x => f (t, x))
      (hf.comp (measurable_const.prodMk measurable_id)) (fun x => hf0 (t, x)) hft).2
  have hJ : Measurable (fun p : ℝ × Vec d =>
      Real.exp (-euclideanSq p.2 / (L * (2 - p.1))) ^ 2 * f p) := by
    apply Measurable.mul _ hf
    unfold euclideanSq dot
    fun_prop
  have hHi : Integrable H (volume.restrict (Icc (0 : ℝ) (T : ℝ))) := by
    apply (hfi.integral_prod_left.const_mul (Real.exp (-R ^ 2 / (2 * L)))).mono'
      hJ.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hbound] with t ht
    change ‖H t‖ ≤ Real.exp (-R ^ 2 / (2 * L)) * G t
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hH0 t)] using ht
  refine ⟨hHi, ?_⟩
  have hm := integral_mono_ae hHi
    (hfi.integral_prod_left.const_mul (Real.exp (-R ^ 2 / (2 * L)))) hbound
  simpa only [integral_const_mul] using hm


/-- The expected whole-space Gaussian error is exactly the Gaussian volume
factor times the actual reduced-law L2 error. -/
theorem short_time_stationary_gaussian_difference_mass {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (r : ℝ) (hr : 0 < r) (f g : Lp ℂ 2 Q) :
    Measurable (fun ω => ∫ x : Vec d, Real.exp (-euclideanSq x / r) *
      ‖f (translate x ω) - g (translate x ω)‖ ^ 2) ∧
    Integrable (fun ω => ∫ x : Vec d, Real.exp (-euclideanSq x / r) *
      ‖f (translate x ω) - g (translate x ω)‖ ^ 2) Q ∧
    (∫ ω, (∫ x : Vec d, Real.exp (-euclideanSq x / r) *
      ‖f (translate x ω) - g (translate x ω)‖ ^ 2) ∂Q) =
      (∫ x : Vec d, Real.exp (-euclideanSq x / r)) * ‖f - g‖ ^ 2 := by
  have hsq : Integrable (fun ω => ‖f ω - g ω‖ ^ 2) Q :=
    ((Lp.memLp f).sub (Lp.memLp g)).norm.integrable_sq
  have hnorm : (∫ ω, ‖f ω - g ω‖ ^ 2 ∂Q) = ‖f - g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub f g] with ω hω
    rw [hω]
    rfl
  have hfm : Measurable (fun ω => f ω - g ω) :=
    (Lp.stronglyMeasurable f).measurable.sub (Lp.stronglyMeasurable g).measurable
  have hgauss : Integrable (fun x : Vec d => Real.exp (-euclideanSq x / r)) := by
    have hp := Integrable.fintype_prod (fun _ : Fin d =>
      integrable_exp_neg_mul_sq (show 0 < r⁻¹ by positivity))
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq, div_eq_mul_inv]
    ring
  let H : Vec d × FieldPair d → ℝ := fun p => Real.exp (-euclideanSq p.1 / r) *
    ‖f (translate p.1 p.2) - g (translate p.1 p.2)‖ ^ 2
  have hHm : Measurable H := by
    exact (by dsimp only [euclideanSq, dot]; fun_prop :
      Measurable (fun p : Vec d × FieldPair d => Real.exp (-euclideanSq p.1 / r))).mul
        ((hfm.comp Probability.continuous_translate.measurable).norm.pow_const 2)
  have hsection (x : Vec d) : Integrable (fun ω => H (x, ω)) Q := by
    exact ((measurePreserving_translate Q hQ x).integrable_comp_of_integrable hsq).const_mul
      (Real.exp (-euclideanSq x / r))
  have hmean (x : Vec d) : (∫ ω, H (x, ω) ∂Q) =
      Real.exp (-euclideanSq x / r) * ‖f - g‖ ^ 2 := by
    dsimp only [H]
    rw [integral_const_mul]
    congr 1
    have hm := measurePreserving_translate Q hQ x
    exact ((integral_map hm.measurable.aemeasurable
      (hfm.norm.pow_const 2).aestronglyMeasurable).symm.trans
      (congrArg (fun μ : Measure (FieldPair d) => ∫ ω, ‖f ω - g ω‖ ^ 2 ∂μ)
        hm.map_eq)).trans hnorm
  have hHi : Integrable H (volume.prod Q) := by
    apply (integrable_prod_iff hHm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hsection, ?_⟩
    apply (hgauss.mul_const (‖f - g‖ ^ 2)).congr
    filter_upwards with x
    have he := hmean x
    simpa only [H, Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))] using he.symm
  refine ⟨hHm.stronglyMeasurable.integral_prod_left'.measurable,
    hHi.integral_prod_right, ?_⟩
  calc
    _ = ∫ x : Vec d, (∫ ω, H (x, ω) ∂Q) := (integral_integral_swap hHi).symm
    _ = ∫ x : Vec d, Real.exp (-euclideanSq x / r) * ‖f - g‖ ^ 2 :=
      integral_congr_ae (ae_of_all _ hmean)
    _ = _ := integral_mul_const _ _

/-- Strong reduced-law L2 convergence admits a subsequence with vanishing
whole-space Gaussian spatial error on one environment event. -/
theorem short_time_stationary_gaussian_subsequence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (r : ℝ) (hr : 0 < r) (u : ℕ → Lp ℂ 2 Q) (f : Lp ℂ 2 Q)
    (hu : Tendsto u atTop (𝓝 f)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q,
      Tendsto (fun n => ∫ x : Vec d, Real.exp (-euclideanSq x / r) *
        ‖u (ns n) (translate x ω) - f (translate x ω)‖ ^ 2) atTop (𝓝 0) := by
  let E (n : ℕ) (ω : FieldPair d) : ℝ := ∫ x : Vec d,
    Real.exp (-euclideanSq x / r) * ‖u n (translate x ω) - f (translate x ω)‖ ^ 2
  have hE (n : ℕ) := short_time_stationary_gaussian_difference_mass Q hQ r hr (u n) f
  have hE0 (n : ℕ) (ω : FieldPair d) : 0 ≤ E n ω :=
    integral_nonneg fun x => mul_nonneg (Real.exp_nonneg _) (sq_nonneg _)
  have heLp (n : ℕ) : eLpNorm (E n) 1 Q =
      ENNReal.ofReal ((∫ x : Vec d, Real.exp (-euclideanSq x / r)) * ‖u n - f‖ ^ 2) := by
    rw [eLpNorm_one_eq_lintegral_enorm (hE n).2.1.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hE n).2.1]
    congr 1
    calc
      _ = ∫ ω, E n ω ∂Q := integral_congr_ae
        (ae_of_all _ fun ω => Real.norm_of_nonneg (hE0 n ω))
      _ = _ := (hE n).2.2
  have hn : Tendsto (fun n => ‖u n - f‖ ^ 2) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by omega : 2 ≠ 0)] using
      ((hu.sub (tendsto_const_nhds (x := f))).norm.pow 2)
  have he : Tendsto (fun n => eLpNorm (E n) 1 Q) atTop (𝓝 0) := by
    simp only [heLp]
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto _).comp
        (hn.const_mul (∫ x : Vec d, Real.exp (-euclideanSq x / r)))
  have hm : TendstoInMeasure Q E atTop (0 : FieldPair d → ℝ) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 1) (f := E) (g := 0) one_ne_zero
      (by simpa only [sub_zero] using he)
  exact hm.exists_seq_tendsto_ae

/-- Actual normalized resolvents have one subsequence for both initial and
bounded-linear evolved Gaussian errors, before any retained physical choice. -/
theorem short_time_stationary_resolvent_gaussian_subsequence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q))
    (A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (r : ℝ) (hr : 0 < r) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂reducedLaw Q,
      (Tendsto (fun n => ∫ x : Vec d, Real.exp (-euclideanSq x / r) *
        ‖(forcedComplexResolventApproximation Q i ζ (ns n) f) (translate x ω) -
          f (translate x ω)‖ ^ 2) atTop (𝓝 0)) ∧
      (Tendsto (fun n => ∫ x : Vec d, Real.exp (-euclideanSq x / r) *
        ‖(A (forcedComplexResolventApproximation Q i ζ (ns n) f)) (translate x ω) -
          (A f) (translate x ω)‖ ^ 2) atTop (𝓝 0)) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let u := fun n => forcedComplexResolventApproximation Q i ζ n f
  have hu : Tendsto u atTop (𝓝 f) := tendsto_forcedComplexResolventApproximation Q i ζ f
  obtain ⟨ns, hns, hinit⟩ := short_time_stationary_gaussian_subsequence
    (reducedLaw Q) (reducedLaw_stationary Q) r hr u f hu
  obtain ⟨ms, hms, hfinal⟩ := short_time_stationary_gaussian_subsequence
    (reducedLaw Q) (reducedLaw_stationary Q) r hr (fun n => A (u (ns n))) (A f)
    ((A.continuous.tendsto f).comp (hu.comp hns.tendsto_atTop))
  refine ⟨ns ∘ ms, hns.comp hms, ?_⟩
  filter_upwards [hinit, hfinal] with ω hω htω
  exact ⟨hω.comp hms.tendsto_atTop, htω⟩

/-- A compact multiplier is dominated by any fixed positive Gaussian.
The constant precedes the function being localized. -/
private theorem short_time_compact_gaussian_domination {d : ℕ}
    (χ : Vec d → ℝ) (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, χ x ^ 2 ≤ C * Real.exp (-euclideanSq x) := by
  have hq : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  obtain ⟨N, hN⟩ := hc.exists_bound_of_continuousOn
    ((hχ.pow 2).mul (Real.continuous_exp.comp hq)).continuousOn
  refine ⟨max N 0 + 1, by positivity, ?_⟩
  intro x
  by_cases hx : x ∈ tsupport χ
  · have hb : χ x ^ 2 * Real.exp (euclideanSq x) ≤ max N 0 + 1 :=
      (le_abs_self _).trans ((hN x hx).trans
        ((le_max_left N 0).trans (le_add_of_nonneg_right zero_le_one)))
    have hm := mul_le_mul_of_nonneg_right hb (Real.exp_nonneg (-euclideanSq x))
    simpa only [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] using hm
  · rw [image_eq_zero_of_notMem_tsupport hx]
    simp only [zero_pow (by omega : 2 ≠ 0)]
    exact mul_nonneg (by linarith [le_max_right N 0]) (Real.exp_nonneg _)

/-- Strong stationary L2 convergence admits a single environment event and
subsequence on which every continuous compact cutoff converges in physical L2.
The cutoff is chosen after the event. -/
theorem short_time_stationary_cutoff_subsequence {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (u : ℕ → Lp ℂ 2 Q) (f : Lp ℂ 2 Q) (hu : Tendsto u atTop (𝓝 f)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q,
      ∀ χ : Vec d → ℝ, Continuous χ → HasCompactSupport χ →
        ∃ (v : Lp ℂ 2 (volume : Measure (Vec d)))
          (vn : ℕ → Lp ℂ 2 (volume : Measure (Vec d))),
          (v : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) ∧
          (∀ n, (vn n : Vec d → ℂ) =ᵐ[volume]
            (fun x => (χ x : ℂ) * u (ns n) (translate x ω))) ∧
          Tendsto vn atTop (𝓝 v) := by
  obtain ⟨ns, hns, he⟩ := short_time_stationary_gaussian_subsequence Q hQ 1 zero_lt_one u f hu
  have hf := ae_stationary_spatial_orbit_gaussian_memLp d hd Q hQ f
  have hn := ae_all_iff.mpr fun n =>
    ae_stationary_spatial_orbit_gaussian_memLp d hd Q hQ (u n)
  refine ⟨ns, hns, ?_⟩
  filter_upwards [he, hf, hn] with ω he hf hn
  intro χ hχ hc
  obtain ⟨C, hC, hb⟩ := short_time_compact_gaussian_domination χ hχ hc
  have hfm : Measurable (fun x : Vec d => f (translate x ω)) :=
    (Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hum (n : ℕ) : Measurable (fun x : Vec d => u (ns n) (translate x ω)) :=
    (Lp.stronglyMeasurable (u (ns n))).measurable.comp
      (Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const))
  have hw {z : Vec d → ℂ} (hz : Measurable z)
      (hzg : MemLp (fun x => (Real.exp (-euclideanSq x / 2) : ℂ) * z x) 2 volume) :
      Integrable (fun x => Real.exp (-euclideanSq x) * ‖z x‖ ^ 2) := by
    convert hzg.norm.integrable_sq using 1
    funext x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow,
      ← Real.exp_nat_mul]
    congr 2
    ring
  have hmul {z : Vec d → ℂ} (hz : Measurable z)
      (hzg : Integrable (fun x => Real.exp (-euclideanSq x) * ‖z x‖ ^ 2)) :
      MemLp (fun x => (χ x : ℂ) * z x) 2 volume ∧
      (∫ x, ‖(χ x : ℂ) * z x‖ ^ 2) ≤
        C * ∫ x, Real.exp (-euclideanSq x) * ‖z x‖ ^ 2 := by
    have hm : AEStronglyMeasurable (fun x => (χ x : ℂ) * z x) volume :=
      ((Complex.measurable_ofReal.comp hχ.measurable).mul hz).aestronglyMeasurable
    have hbound (x : Vec d) : ‖(χ x : ℂ) * z x‖ ^ 2 ≤
        C * (Real.exp (-euclideanSq x) * ‖z x‖ ^ 2) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
      nlinarith [mul_le_mul_of_nonneg_right (hb x) (sq_nonneg ‖z x‖)]
    have hi : Integrable (fun x => ‖(χ x : ℂ) * z x‖ ^ 2) :=
      (hzg.const_mul C).mono' (((Complex.measurable_ofReal.comp hχ.measurable).mul hz).norm.pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => by
        simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hbound x)
    exact ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hi,
      (integral_mono_ae hi (hzg.const_mul C) (ae_of_all _ hbound)).trans_eq
        (integral_const_mul _ _)⟩
  have hfi := hw hfm (hf 2 (by norm_num))
  have hui (n : ℕ) := hw (hum n) (hn (ns n) 2 (by norm_num))
  have hflp := (hmul hfm hfi).1
  have hulp (n : ℕ) := (hmul (hum n) (hui n)).1
  let v := hflp.toLp (fun x => (χ x : ℂ) * f (translate x ω))
  let vn := fun n => (hulp n).toLp (fun x => (χ x : ℂ) * u (ns n) (translate x ω))
  have hev := hflp.coeFn_toLp
  have hevn (n : ℕ) := (hulp n).coeFn_toLp
  refine ⟨v, vn, hev, hevn, ?_⟩
  have hdiff (n : ℕ) : ‖vn n - v‖ ^ 2 ≤
      C * ∫ x : Vec d, Real.exp (-euclideanSq x) *
        ‖u (ns n) (translate x ω) - f (translate x ω)‖ ^ 2 := by
    have hzg : MemLp (fun x => (Real.exp (-euclideanSq x / 2) : ℂ) *
        (u (ns n) (translate x ω) - f (translate x ω))) 2 volume := by
      convert ((hn (ns n) 2 (by norm_num)).sub (hf 2 (by norm_num))) using 1
      funext x
      exact mul_sub _ _ _
    have hzi := hw ((hum n).sub hfm) hzg
    have hi := (hmul ((hum n).sub hfm) hzi).2
    have heq : ‖vn n - v‖ ^ 2 =
        ∫ x, ‖(χ x : ℂ) * (u (ns n) (translate x ω) - f (translate x ω))‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (vn n) v, hevn n, hev] with x hx hn hf
      rw [hx]
      change ‖vn n x - v x‖ ^ 2 = _
      rw [hn, hf, mul_sub]
    rw [heq]
    exact hi
  have hs : Tendsto (fun n => ‖vn n - v‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hdiff
    simpa only [div_one, mul_zero] using he.const_mul C
  have hn : Tendsto (fun n => ‖vn n - v‖) atTop (𝓝 0) := by
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hh
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn

private theorem shortTimeC0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    ShortTimeC0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
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

private theorem ShortTimeC0Graph.smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E} {f g : E} (hfg : ShortTimeC0Graph P f g) (c : ℝ) :
    ShortTimeC0Graph P (c • f) (c • g) := by
  change Tendsto _ _ _
  have h := hfg.const_smul c
  convert h using 1
  ext t
  simp only [map_smul, ← smul_sub]
  exact smul_comm _ _ _

private theorem shortTimeC0Graph_dense
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) :
    Dense {f : E | ∃ g, ShortTimeC0Graph P f g} := by
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
    ⟨(h : ℝ)⁻¹ • (P h f - f), (shortTimeC0Graph_integral hP0 hPm hPc f h).smul _⟩)

private theorem shortTimeC0Graph_complex_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {P : ℝ≥0 → E →L[ℂ] E} {f g : E} :
    ShortTimeC0Graph (fun t => (P t).restrictScalars ℝ) f g ↔
      Tendsto (fun t : ℝ≥0 => ((t : ℝ) : ℂ)⁻¹ • (P t f - f))
        (𝓝[>] (0 : ℝ≥0)) (𝓝 g) := by
  simp only [ShortTimeC0Graph, RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl

/-- Actual physical generator-domain data approximate every physical L2 datum.
The approximation also converges after each physical evolution operator.
Time averages require only the given C0 graph identity. -/
theorem short_time_physical_generator_approximation {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ u g : ℕ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, IsPhysicalComplexGeneratorPair a i ζ (u n) (g n)) ∧
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
    (shortTimeC0Graph_dense hp0 hpm hpc f)
  choose g hg using hu
  refine ⟨u, g, ?_, hf, fun t => ((P t).continuous.tendsto f).comp hf⟩
  intro n
  exact (hP.2.2.2 (u n) (g n)).mp (shortTimeC0Graph_complex_iff.mp (hg n))

/-- On one stationary event every continuous compact cutoff admits actual
physical generator-domain approximants, for every physical C0 evolution.
The event and the physical cutoff representative precede the evolution choice. -/
theorem short_time_stationary_cutoff_generator_approximation {d : ℕ} (hd : 2 ≤ d)
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℂ 2 Q) :
    ∀ᵐ ω ∂Q, ∀ χ : Vec d → ℝ, Continuous χ → HasCompactSupport χ →
      ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
        (v : Vec d → ℂ) =ᵐ[volume] (fun x => (χ x : ℂ) * f (translate x ω)) ∧
        ∀ (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
          (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
            Lp ℂ 2 (volume : Measure (Vec d))),
          IsPhysicalComplexSemigroup a i ζ P →
          ∃ u g : ℕ → Lp ℂ 2 (volume : Measure (Vec d)),
            (∀ n, IsPhysicalComplexGeneratorPair a i ζ (u n) (g n)) ∧
            Tendsto u atTop (𝓝 v) ∧
            ∀ t : ℝ≥0, Tendsto (fun n => P t (u n)) atTop (𝓝 (P t v)) := by
  obtain ⟨ns, hns, he⟩ := short_time_stationary_cutoff_subsequence hd Q hQ
    (fun _ : ℕ => f) f tendsto_const_nhds
  filter_upwards [he] with ω he
  intro χ hχ hc
  obtain ⟨v, vn, hv, hvn, hvlim⟩ := he χ hχ hc
  refine ⟨v, hv, ?_⟩
  intro a i ζ P hP
  exact short_time_physical_generator_approximation hP v

private theorem short_time_gaussian_l2_multiplier_continuous {d : ℕ}
    (r : ℝ) (hr : 0 < r) :
    let W := fun f : Lp ℂ 2 (volume : Measure (Vec d)) =>
      (short_time_gaussian_spatial_mul_memLp hr (Lp.stronglyMeasurable f).measurable
        (Lp.memLp f)).toLp (fun x => (Real.exp (-euclideanSq x / r) : ℂ) * f x)
    Continuous W := by
  dsimp only
  let W := fun f : Lp ℂ 2 (volume : Measure (Vec d)) =>
    (short_time_gaussian_spatial_mul_memLp hr (Lp.stronglyMeasurable f).measurable
      (Lp.memLp f)).toLp (fun x => (Real.exp (-euclideanSq x / r) : ℂ) * f x)
  have he (f : Lp ℂ 2 (volume : Measure (Vec d))) :
      (W f : Vec d → ℂ) =ᵐ[volume] fun x => (Real.exp (-euclideanSq x / r) : ℂ) * f x :=
    MemLp.coeFn_toLp _
  have hbound (x : Vec d) : ‖(Real.exp (-euclideanSq x / r) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    apply div_nonpos_of_nonpos_of_nonneg _ hr.le
    apply neg_nonpos.mpr
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hLip : LipschitzWith 1 W := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro f g
    simp only [NNReal.coe_one, one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [Lp.coeFn_sub (W f) (W g), Lp.coeFn_sub f g, he f, he g]
      with x hsub hsub' hf hg
    rw [hsub, hsub']
    change ‖W f x - W g x‖ ≤ ‖f x - g x‖
    rw [hf, hg, ← mul_sub, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hbound x)
  exact hLip.continuous

/-- Gaussian comparison energies are continuous in physical L2 data, with
only Gaussian-weighted L2 required of the stationary spatial reference. -/
theorem short_time_gaussian_comparison_energy_tendsto {d : ℕ}
    (r : ℝ) (hr : 0 < r) (u : Vec d → ℂ)
    (hu : MemLp (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * u x) 2 volume)
    (v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (hv : Tendsto v atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / r) * ‖u x - v n x‖ ^ 2)
      atTop (𝓝 (∫ x, Real.exp (-euclideanSq x / r) * ‖u x - f x‖ ^ 2)) := by
  let W := fun z : Lp ℂ 2 (volume : Measure (Vec d)) =>
    (short_time_gaussian_spatial_mul_memLp (by positivity : 0 < 2*r)
      (Lp.stronglyMeasurable z).measurable (Lp.memLp z)).toLp
        (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * z x)
  let U := hu.toLp (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * u x)
  have hW : Continuous W := short_time_gaussian_l2_multiplier_continuous (2*r) (by positivity)
  have he (z : Lp ℂ 2 (volume : Measure (Vec d))) :
      ‖U - W z‖ ^ 2 = ∫ x, Real.exp (-euclideanSq x / r) * ‖u x - z x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub U (W z), hu.coeFn_toLp,
      (short_time_gaussian_spatial_mul_memLp (by positivity : 0 < 2*r)
        (Lp.stronglyMeasurable z).measurable (Lp.memLp z)).coeFn_toLp]
      with x hsub hU hWz
    rw [hsub]
    change ‖U x - W z x‖ ^ 2 = _
    rw [hU, hWz, ← mul_sub, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
    congr 2
    push_cast
    field_simp
  have hU : Tendsto (fun _ : ℕ => U) atTop (𝓝 U) := tendsto_const_nhds
  have h := ((hU.sub ((hW.tendsto f).comp hv)).norm).pow 2
  simpa only [Function.comp_def, he] using h

/-- Actual physical graph approximants preserve Gaussian comparison energies
at every fixed time and width, against every Gaussian-L2 spatial reference. -/
theorem short_time_physical_generator_gaussian_approximation {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v g : ℕ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ n, IsPhysicalComplexGeneratorPair a i ζ (v n) (g n)) ∧
      Tendsto v atTop (𝓝 f) ∧
      ∀ (t : ℝ≥0) (r : ℝ), 0 < r → ∀ u : Vec d → ℂ,
        MemLp (fun x => (Real.exp (-euclideanSq x / (2*r)) : ℂ) * u x) 2 volume →
        Tendsto (fun n => ∫ x, Real.exp (-euclideanSq x / r) * ‖u x - P t (v n) x‖ ^ 2)
          atTop (𝓝 (∫ x, Real.exp (-euclideanSq x / r) * ‖u x - P t f x‖ ^ 2)) := by
  obtain ⟨v, g, hg, hv, hPv⟩ := short_time_physical_generator_approximation hP f
  exact ⟨v, g, hg, hv, fun t r hr u hu =>
    short_time_gaussian_comparison_energy_tendsto r hr u hu _ _ (hPv t)⟩


private theorem short_time_cutoff_initial_gaussian_bound {d : ℕ}
    (f : Vec d → ℂ) (hf : Measurable f) (M : ℝ)
    (hbound : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖f x‖ ≤ M)
    (χ : C(Vec d, ℝ)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (R L : ℝ) (hR : 0 ≤ R) (hL : 0 < L)
    (hin : ∀ x, euclideanNorm x ≤ R → χ x = 1) :
    Integrable (fun x => Real.exp (-euclideanSq x / (2*L)) ^ 2 *
      ‖f x - (χ x : ℂ) * f x‖ ^ 2) ∧
    (∫ x, Real.exp (-euclideanSq x / (2*L)) ^ 2 *
      ‖f x - (χ x : ℂ) * f x‖ ^ 2) ≤
      Real.exp (-R ^ 2 / (2*L)) * (M ^ 2 *
        ∫ x : Vec d, Real.exp (-euclideanSq x / (2*L))) := by
  have hg : Integrable (fun x : Vec d => Real.exp (-euclideanSq x / (2*L))) := by
    have hp := Integrable.fintype_prod (fun _ : Fin d =>
      integrable_exp_neg_mul_sq (show 0 < (2*L)⁻¹ by positivity))
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq, div_eq_mul_inv]
    ring
  have hgm : Measurable (fun x : Vec d => Real.exp (-euclideanSq x / (2*L))) := by
    unfold euclideanSq dot
    fun_prop
  have hi : Integrable (fun x => Real.exp (-euclideanSq x / (2*L)) * ‖f x‖ ^ 2) := by
    apply (hg.mul_const (M^2)).mono' ((hgm.mul (hf.norm.pow_const 2)).aestronglyMeasurable)
    filter_upwards [hbound] with x hx
    change ‖Real.exp (-euclideanSq x / (2*L)) * ‖f x‖ ^ 2‖ ≤
      Real.exp (-euclideanSq x / (2*L)) * M ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (Real.exp_nonneg _)
  have hb : (∫ x, Real.exp (-euclideanSq x / (2*L)) * ‖f x‖ ^ 2) ≤
      M^2 * ∫ x : Vec d, Real.exp (-euclideanSq x / (2*L)) := by
    rw [mul_comm (M^2), ← integral_mul_const]
    apply integral_mono_ae hi (hg.mul_const _)
    filter_upwards [hbound] with x hx
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2)
      (Real.exp_nonneg _)
  obtain ⟨hi2, htail⟩ := short_time_gaussian_exterior_weighted_source R L 0 hR hL
    ⟨le_rfl, zero_le_one⟩ (fun x => ‖f x‖ ^ 2) (hf.norm.pow_const 2)
    (fun _ => sq_nonneg _) hi
  simp only [sub_zero, mul_comm L 2] at hi2 htail
  have hn (x : Vec d) : ‖f x - (χ x : ℂ) * f x‖ ≤ ‖f x‖ := by
    have he : f x - (χ x : ℂ) * f x = ((1 - χ x : ℝ) : ℂ) * f x := by
      push_cast
      ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hχ x).2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχ x).1])
  have hei : Integrable (fun x => Real.exp (-euclideanSq x / (2*L)) ^ 2 *
      ‖f x - (χ x : ℂ) * f x‖ ^ 2) := by
    apply hi2.mono' (((hgm.pow_const 2).mul
      ((hf.sub ((Complex.measurable_ofReal.comp χ.continuous.measurable).mul hf)).norm.pow_const 2)).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hn x) 2)
      (sq_nonneg _)
  refine ⟨hei, ?_⟩
  have hs : MeasurableSet {x : Vec d | R ≤ euclideanNorm x} := by
    exact (isClosed_le continuous_const Entropy.continuous_euclideanNorm').measurableSet
  have he : (fun x => Real.exp (-euclideanSq x / (2*L)) ^ 2 *
      ‖f x - (χ x : ℂ) * f x‖ ^ 2) =
      {x : Vec d | R ≤ euclideanNorm x}.indicator (fun x =>
        Real.exp (-euclideanSq x / (2*L)) ^ 2 * ‖f x - (χ x : ℂ) * f x‖ ^ 2) := by
    funext x
    by_cases hx : R ≤ euclideanNorm x
    · simp only [Set.indicator_of_mem (show x ∈ {x : Vec d | R ≤ euclideanNorm x} from hx)]
    · rw [Set.indicator_of_notMem (show x ∉ {x : Vec d | R ≤ euclideanNorm x} from hx), hin x (le_of_not_ge hx)]
      simp
  rw [he, integral_indicator hs]
  exact (setIntegral_mono_on hei.integrableOn hi2.integrableOn hs
    (fun x _ => mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hn x) 2) (sq_nonneg _))).trans
    (htail.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _)))

/-- Uniform Gaussian initial-error bounds for the actual drift and clock
observations. One sample event works for every radius, width and cutoff. -/
theorem short_time_forward_clock_initial_gaussian_bound (d : ℕ) (D : StructuralData d) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ →
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ R L : ℝ, 0 ≤ R → 0 < L → (∀ x, euclideanNorm x ≤ R → χ x = 1) →
      (∀ i : Fin d,
        (∫ x, Real.exp (-euclideanSq x / (2*L)) ^ 2 *
          ‖β i (translate x ω) - (χ x : ℂ) * β i (translate x ω)‖ ^ 2) ≤
          Real.exp (-R ^ 2 / (2*L)) * (K ^ 2 *
            ∫ x : Vec d, Real.exp (-euclideanSq x / (2*L)))) ∧
      (∫ x, Real.exp (-euclideanSq x / (2*L)) ^ 2 *
        ‖(μ (translate x ω) - 1) - (χ x : ℂ) * (μ (translate x ω) - 1)‖ ^ 2) ≤
        Real.exp (-R ^ 2 / (2*L)) * (K ^ 2 *
          ∫ x : Vec d, Real.exp (-euclideanSq x / (2*L))) := by
  obtain ⟨M, hM, hb⟩ := EndpointFiniteP.observation_bounds d D
  refine ⟨M+1, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ
  obtain ⟨hβb, _, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  have hsection (f : FieldPair d → ℂ) (hf : Measurable f)
      (hb : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ M+1) :
      ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
        ‖f (translate x ω)‖ ≤ M+1 := by
    apply (Measure.ae_ae_comm ?_).mp (ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hb)
    exact measurableSet_le (hf.comp Probability.continuous_translate.measurable).norm
      measurable_const
  have hβs : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
      ∀ᵐ x ∂(volume : Measure (Vec d)), ‖β i (translate x ω)‖ ≤ M+1 := by
    rw [ae_all_iff]
    intro i
    exact hsection (β i) (Lp.stronglyMeasurable _).measurable
      ((hβb i).mono fun _ h => by linarith)
  have hμs := hsection (fun ω => μ ω - 1)
    ((Lp.stronglyMeasurable μ).measurable.sub measurable_const)
    (hμb.mono fun ω h => (norm_sub_le _ _).trans (by simpa using add_le_add_right h 1))
  filter_upwards [hβs, hμs] with ω hβω hμω
  intro χ hχ R L hR hL hin
  refine ⟨fun i => ?_, ?_⟩
  · exact (short_time_cutoff_initial_gaussian_bound _
      ((Lp.stronglyMeasurable (β i)).measurable.comp
        (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))) (M+1)
      (hβω i) χ hχ R L hR hL hin).2
  · exact (short_time_cutoff_initial_gaussian_bound _
      (((Lp.stronglyMeasurable μ).measurable.comp
        (Probability.continuous_translate.measurable.comp
          (measurable_id.prodMk measurable_const))).sub measurable_const)
      (M+1) hμω χ hχ R L hR hL hin).2

/-- The actual stationary gradient orbit has an exterior moving-Gaussian
source bound. Its space-time integrability follows from the generator-domain
orbit; no source-integrability or comparison hypothesis is required. -/
theorem short_time_stationary_gradient_exterior_source
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ T : ℝ≥0, (T : ℝ) ≤ 1 → ∀ᵐ ω ∂reducedLaw Q,
      ∀ R L : ℝ, 0 ≤ R → 0 < L →
      Integrable (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L)) *
        ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2)
        ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ∧
      IntegrableOn (fun s => ∫ x in {x : Vec d | R ≤ euclideanNorm x},
        Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
          ∑ j, ‖D j (s, translate x ω)‖ ^ 2) (Icc (0 : ℝ) (T : ℝ)) ∧
      (∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : Vec d | R ≤ euclideanNorm x},
        Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
          ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
        Real.exp (-R ^ 2 / (2 * L)) *
          (∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x,
            Real.exp (-euclideanSq x / (2 * L)) *
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨D, hD, heD⟩ := hP.exists_joint_gradient_representative f
  refine ⟨D, hD, heD, ?_⟩
  obtain ⟨G, hGc, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  intro T hT
  have hDi (j : Fin d) : Integrable (fun p => ‖D j p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod (reducedLaw Q)) := by
    apply short_time_integrable_sq_joint_l2 _ (hD j) (heD j)
    have hj : Continuous (fun s : ℝ => G s j) := by fun_prop
    have hi := ((hj.norm.pow 2).continuousOn.integrableOn_compact
      (μ := volume) (K := Icc (0 : ℝ) (T : ℝ)) isCompact_Icc)
    change Integrable (fun s : ℝ => ‖G s j‖ ^ 2)
      (volume.restrict (Icc (0 : ℝ) (T : ℝ))) at hi
    rw [← restrict_Ioc_eq_restrict_Icc] at hi ⊢
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    rw [(hP.gradientOrbit_spec f hs.1).unique (hG s)]
  have hDG : ∀ᵐ ω ∂reducedLaw Q, ∀ j : Fin d, ∀ r : ℝ, 0 < r →
      MemLp (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2 / r) : ℂ) *
        D j (p.1, translate p.2 ω)) 2
        ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) :=
    ae_all_iff.mpr fun j => ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (T : ℝ) T.coe_nonneg (D j) (hD j) (hDi j)
  filter_upwards [hDG] with ω hDω
  intro R L hR hL
  let H : ℝ × Vec d → ℝ := fun p => ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hH : Measurable H := Finset.measurable_sum _ fun j _ =>
    ((hD j).comp hshift).norm.pow_const 2
  have hHi : Integrable (fun p => Real.exp (-euclideanSq p.2 / (2 * L)) * H p)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) := by
    have hj (j : Fin d) := (hDω j (4 * L) (by positivity)).norm.integrable_sq
    have he (p : ℝ × Vec d) (j : Fin d) :
        ‖(Real.exp (-euclideanSq p.2 / (4 * L)) : ℂ) *
          D j (p.1, translate p.2 ω)‖ ^ 2 =
        Real.exp (-euclideanSq p.2 / (2 * L)) * ‖D j (p.1, translate p.2 ω)‖ ^ 2 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      (field_simp; ring)
    have hs := integrable_finsetSum Finset.univ (fun j _ => (hj j).congr
      (ae_of_all _ fun p => he p j))
    simpa only [H, Finset.mul_sum] using hs
  exact ⟨hHi, short_time_gaussian_exterior_spacetime_source R L T hR hL hT H hH
    (fun p => Finset.sum_nonneg fun j _ => sq_nonneg _) hHi⟩

private theorem short_time_joint_gaussian_dissipation
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ} {b c L : ℝ} (hc : c < 2)
    (hL : 64 * (Real.exp (2 * Λ₀) * Λ₀) ^ 3 ≤ L)
    {u v : ℝ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℝ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hgen : ∀ s ∈ Ioc b c, IsComplexGeneratorPair Q i ζ (u s) (v s))
    (hgrad : ∀ s ∈ Ioc b c,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (u s) (G s))
    {U V : ℝ × FieldPair d → ℂ} (hU : Measurable U) (hV : Measurable V)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] u s)
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] v s)
    {D : Fin d → ℝ × FieldPair d → ℂ} (hD : ∀ j, Measurable (D j))
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] G s j) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let η : ℝ → Vec d → ℝ := fun s x => Real.exp (-euclideanSq x / (L * (2 - s)))
    let W : ℝ → Vec d → ℝ := fun s x =>
      -2 * euclideanSq x / (L * (2 - s) ^ 2) * η s x ^ 2
    ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c),
      (Λ⁻¹ / 4) * (∫ x, η s x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) +
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
    (Λ⁻¹ / 4) * (∫ x, η p.1 x ^ 2 * ∑ j, ‖D j (p.1, translate x p.2)‖ ^ 2) +
    (∫ x, η p.1 x ^ 2 * (2 * (star (U (p.1, translate x p.2)) * V (p.1, translate x p.2)).re)) +
      ∫ x, W p.1 x * ‖U (p.1, translate x p.2)‖ ^ 2
  let B : ℝ × FieldPair d → ℝ := fun p =>
    16 * Λ ^ 3 * ‖ζ‖ ^ 2 * ∫ x, η p.1 x ^ 2 * ‖U (p.1, translate x p.2)‖ ^ 2
  have hA : Measurable A := by
    apply Measurable.add
    · apply Measurable.add
      · exact measurable_const.mul (((hη.pow_const 2).mul
          (Finset.measurable_sum _ fun j _ => ((hshift (hD j)).norm.pow_const 2))).stronglyMeasurable.integral_prod_right'.measurable)
      · exact ((hη.pow_const 2).mul ((Complex.continuous_re.measurable.comp
          ((continuous_star.measurable.comp (hshift hU)).mul (hshift hV))).const_mul 2)).stronglyMeasurable.integral_prod_right'.measurable
    · exact (hW.mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  have hB : Measurable B := measurable_const.mul
    ((hη.pow_const 2).mul ((hshift hU).norm.pow_const 2)).stronglyMeasurable.integral_prod_right'.measurable
  change ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ s ∂volume.restrict (Icc b c), A (s, ω) ≤ B (s, ω)
  apply (Measure.ae_ae_comm (p := fun s ω => A (s, ω) ≤ B (s, ω))
    (measurableSet_le hA hB)).mp
  rw [← restrict_Ioc_eq_restrict_Icc]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have heU' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hU.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (u s)).measurable (heU s)
  have heV' := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hV.comp (measurable_const.prodMk measurable_id)) (Lp.stronglyMeasurable (v s)).measurable (heV s)
  filter_upwards [crudeEnergy_ae_generator_gaussian_energy (hgen s hs) (hgrad s hs),
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) (u s),
    ae_stationary_spatial_orbit_gaussian_memLp d Fact.out (reducedLaw Q) (reducedLaw_stationary Q) (v s),
    heU', heV', ae_all_iff.mpr (fun j => ae_spatial_complex_orbit_congr
      (reducedLaw Q) (reducedLaw_stationary Q)
      ((hD j).comp (measurable_const.prodMk measurable_id))
      (Lp.stronglyMeasurable (G s j)).measurable (heD j s))] with ω he hu hv heu hev hed
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
  have hmass : (Λ⁻¹ / 4) * (∫ x, η s x ^ 2 * ∑ j, ‖G s j (translate x ω)‖ ^ 2) +
      (∫ x, η s x ^ 2 *
      (2 * (star ((u s) (translate x ω)) * (v s) (translate x ω)).re)) +
      (∫ x, W s x * ‖(u s) (translate x ω)‖ ^ 2) ≤
      16 * Λ ^ 3 * ‖ζ‖ ^ 2 * (∫ x, η s x ^ 2 * ‖(u s) (translate x ω)‖ ^ 2) := by
    rw [hcross]
    linarith only [henergy]
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
  have hgd : (∫ x, η s x ^ 2 * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) =
      ∫ x, η s x ^ 2 * ∑ j, ‖G s j (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hed] with x hx
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj := hx j
    change D j (s, translate x ω) = _ at hj
    rw [hj]
  dsimp only [A, B]
  rw [hgd, hcross', hsq, hsq]
  exact hmass



/-- Retaining spatial dissipation in the actual stationary energy identity
bounds the damped gradient energy by the literal initial Gaussian mass. -/
private theorem short_time_stationary_damped_gradient_energy
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    let Λ := Real.exp (2 * Λ₀) * Λ₀
    let γ := 16 * Λ ^ 3 * ‖ζ‖ ^ 2
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ T : ℝ≥0, (T : ℝ) ≤ 1 → ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      ∀ᵐ ω ∂reducedLaw Q,
        (∀ r : ℝ, 0 < r → Integrable (fun p : ℝ × Vec d =>
          Real.exp (-euclideanSq p.2 / (2 * r)) *
            ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume)) ∧
        (Λ⁻¹ / 4) * (∫ s in Icc (0 : ℝ) (T : ℝ),
          Real.exp (-γ * s) * (∫ x,
            Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2)) ≤
        ∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖f (translate x ω)‖ ^ 2 := by
  intro Λ γ
  let : Fact (2 ≤ d) := ⟨hd⟩
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hγ : 0 ≤ γ := by dsimp only [γ]; positivity
  obtain ⟨D, hD, heD, hsource⟩ := short_time_stationary_gradient_exterior_source hd Q hP hfg
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  refine ⟨D, hD, heD, ?_⟩
  intro T hT L hL
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have hFi : Integrable (fun p => ‖F p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 f).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hF heF
  have hUi : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hFG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (T : ℝ) T.coe_nonneg F hF hFi
  have hUG := ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) (T : ℝ) T.coe_nonneg U hU hUi
  have heT := ae_spatial_complex_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (hF.comp (measurable_const.prodMk measurable_id))
    (Lp.stronglyMeasurable (P T f)).measurable
    (by
      filter_upwards [heF (T : ℝ)] with ω hω
      simpa only [Function.comp_apply, id_eq, Real.toNNReal_coe] using hω)
  have hspace := short_time_joint_gaussian_dissipation (Q := Q) (b := 0) (c := (T : ℝ))
    (by linarith) hL
    (fun s _ => hP.map_generator hfg s.toNNReal)
    (fun s hs => hP.gradientOrbit_spec f hs.1) hF hU heF heU hD heD
  filter_upwards [hFG, hUG, heT, hsource T hT, hspace,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) (P T f)] with ω hFω hUω heω hDω hsp hfω htω
  refine ⟨fun r hr => (hDω 0 r (by norm_num) hr).1, ?_⟩
  let X : ℝ × Vec d → ℂ := fun p => F (p.1, translate p.2 ω)
  let Y : ℝ × Vec d → ℂ := fun p => U (p.1, translate p.2 ω)
  let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
  let W : ℝ × Vec d → ℝ := fun p => -2 * euclideanSq p.2 / (L * (2 - p.1) ^ 2) * η p ^ 2
  let H : ℝ × Vec d → ℝ := fun p => ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2
  let m : ℝ → ℝ := fun s => Real.exp (-γ * s)
  let τ : Measure ℝ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hX : Measurable X := hF.comp hshift
  have hY : Measurable Y := hU.comp hshift
  have hη : Measurable η := by dsimp only [η, euclideanSq, dot]; fun_prop
  have hW : Measurable W := by dsimp only [W, η, euclideanSq, dot]; fun_prop
  have hH : Measurable H := Finset.measurable_sum _ fun j _ =>
    ((hD j).comp hshift).norm.pow_const 2
  have hX0 (x : Vec d) : X (0, x) = f (translate x ω) := by
    simpa [X] using hprim 0 (translate x ω)
  have hends : ∀ s ∈ ({0, (T : ℝ)} : Set ℝ), MemLp
      (fun x => (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * X (s, x)) 2 volume := by
    intro s hs
    rcases hs with hs | hs
    · subst s
      simpa only [hX0] using hfω (4 * L) (by positivity)
    · have hs' : s = (T : ℝ) := hs
      subst s
      apply (htω (4 * L) (by positivity)).ae_eq
      filter_upwards [heω] with x hx
      change F ((T : ℝ), translate x ω) = _ at hx
      change _ = (Real.exp (-euclideanSq x / (4 * L)) : ℂ) * F ((T : ℝ), translate x ω)
      rw [hx]
  have hX2 := hFω (4 * L) (by positivity)
  have hY2 := hUω (4 * L) (by positivity)
  have hsample : ∀ᵐ x ∂volume,
      IntervalIntegrable (fun s => Y (s, x)) volume 0 (T : ℝ) ∧
      ∀ s ∈ Icc (0 : ℝ) (T : ℝ), X (s, x) = X (0, x) + ∫ r in (0 : ℝ)..s, Y (r, x) := by
    filter_upwards [short_time_gaussian_time_integrable Y hY hY2] with x hx
    refine ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le T.coe_nonneg).mpr hx, ?_⟩
    intro s hs
    rw [hX0, intervalIntegral.integral_of_le hs.1, ← integral_Icc_eq_integral_Ioc]
    exact hprim s (translate x ω)
  have hid := short_time_damped_moving_gaussian_primitive_energy hLp T.coe_nonneg hT γ hγ
    X Y hX hY hX2 hY2 hends hsample
  obtain ⟨hAi, hBi⟩ := short_time_moving_gaussian_spacetime_integrable hLp hT X Y hX hY hX2 hY2
  change Integrable (fun p => η p ^ 2 * (2 * (star (X p) * Y p).re)) _ at hAi
  change Integrable (fun p => W p * ‖X p‖ ^ 2) _ at hBi
  have htime : ∀ᵐ p : ℝ × Vec d ∂τ.prod volume, p.1 ∈ Icc (0 : ℝ) (T : ℝ) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ae_of_all _ fun _ => hs)
  have hCi : Integrable (fun p => η p ^ 2 * ‖X p‖ ^ 2) (τ.prod volume) := by
    apply hX2.norm.integrable_sq.mono' ((hη.pow_const 2).mul (hX.norm.pow_const 2)).aestronglyMeasurable
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 hLp ⟨hp.1, hp.2.trans hT⟩).1
    change ‖η p ^ 2 * ‖X p‖ ^ 2‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
      norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hHi : Integrable (fun p => η p ^ 2 * H p) (τ.prod volume) := by
    apply (hDω 0 L (by norm_num) hLp).1.mono' ((hη.pow_const 2).mul hH).aestronglyMeasurable
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 hLp ⟨hp.1, hp.2.trans hT⟩).1
    have he : Real.exp (-euclideanSq p.2 / (4 * L)) ^ 2 =
        Real.exp (-euclideanSq p.2 / (2 * L)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he] at hb
    change ‖η p ^ 2 * H p‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have damp (Z : ℝ × Vec d → ℝ) (hZ : Integrable Z (τ.prod volume)) :
      Integrable (fun p => m p.1 * Z p) (τ.prod volume) := by
    apply hZ.norm.mono' (((by dsimp only [m]; fun_prop : Measurable (fun p : ℝ × Vec d => m p.1)).aestronglyMeasurable).mul hZ.aestronglyMeasurable)
    filter_upwards [htime] with p hp
    change ‖m p.1 * Z p‖ ≤ _
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hp.1))
  have hAd := damp _ (hAi.sub (hCi.const_mul γ))
  have hBd := damp _ hBi
  have hHd := damp _ hHi
  have hi := integral_mono_ae
    ((hHd.integral_prod_left.const_mul (Λ⁻¹ / 4)).add
      (hAd.integral_prod_left.add hBd.integral_prod_left))
    (integrable_zero ℝ ℝ τ) ?_
  · simp only [Pi.zero_apply, integral_zero] at hi
    change (∫ s, (Λ⁻¹ / 4) * (∫ x, m s * (η (s, x) ^ 2 * H (s, x))) +
        ((∫ x, m s * (η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
          γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) +
         (∫ x, m s * (W (s, x) * ‖X (s, x)‖ ^ 2))) ∂τ) ≤ 0 at hi
    have hsplit := integral_add (hHd.integral_prod_left.const_mul (Λ⁻¹ / 4))
      (hAd.integral_prod_left.add hBd.integral_prod_left)
    have hsplit' := integral_add hAd.integral_prod_left hBd.integral_prod_left
    simp only [Pi.add_apply, Pi.sub_apply] at hsplit hsplit'
    rw [hsplit, integral_const_mul, hsplit'] at hi
    have hid' : (∫ s, (∫ x, m s * (η (s, x) ^ 2 *
        (2 * (star (X (s, x)) * Y (s, x)).re) - γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) ∂τ) =
        m T * (∫ x, η (T, x) ^ 2 * ‖X (T, x)‖ ^ 2) -
        (∫ x, η (0, x) ^ 2 * ‖X (0, x)‖ ^ 2) -
        (∫ s, (∫ x, m s * (W (s, x) * ‖X (s, x)‖ ^ 2)) ∂τ) := hid
    have hfinal : 0 ≤ m T * (∫ x, η (T, x) ^ 2 * ‖X (T, x)‖ ^ 2) :=
      mul_nonneg (Real.exp_nonneg _) (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hinit : (∫ x, η (0, x) ^ 2 * ‖X (0, x)‖ ^ 2) =
        ∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 * ‖f (translate x ω)‖ ^ 2 := by
      simp only [η, sub_zero, hX0, mul_comm L 2]
    rw [hid'] at hi
    simpa only [integral_const_mul, hinit] using (by linarith only [hi, hfinal] :
      (Λ⁻¹ / 4) * (∫ s, (∫ x, m s * (η (s, x) ^ 2 * H (s, x))) ∂τ) ≤
        ∫ x, η (0, x) ^ 2 * ‖X (0, x)‖ ^ 2)
  · filter_upwards [hsp, hAi.prod_right_ae, hCi.prod_right_ae] with s hs hAs hCs
    change (Λ⁻¹ / 4) * (∫ x, m s * (η (s, x) ^ 2 * H (s, x))) +
      ((∫ x, m s * (η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
        γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2))) +
       (∫ x, m s * (W (s, x) * ‖X (s, x)‖ ^ 2))) ≤ 0
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
    have hc : (∫ x, η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re) -
        γ * (η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2)) =
        (∫ x, η (s, x) ^ 2 * (2 * (star (X (s, x)) * Y (s, x)).re)) -
        γ * (∫ x, η (s, x) ^ 2 * ‖X (s, x)‖ ^ 2) := by
      rw [integral_sub, integral_const_mul]
      · exact hAs
      · exact hCs.const_mul γ
    rw [hc]
    have hm0 : 0 ≤ m s := Real.exp_nonneg _
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hm0 (sub_nonpos.mpr hs)]


/-- The actual forward and clock initial data have deterministic wider
Gaussian gradient energy, uniformly over the force disc. The constant is
chosen before the law, observations, force and semigroup. -/
theorem short_time_forward_clock_uniform_gradient_energy
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P, ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ T : ℝ≥0, (T : ℝ) ≤ 1 → ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      ∀ᵐ ω ∂reducedLaw Q,
        Integrable (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L)) *
          ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ∧
        (∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x,
          Real.exp (-euclideanSq x / (2 * L)) * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          K * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) := by
  obtain ⟨M, hM, hb⟩ := EndpointFiniteP.observation_bounds d S
  let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
  let γB := 16 * Λ ^ 3 * B ^ 2
  have hΛ : 0 < Λ := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  let N := M * (1 + B)
  refine ⟨4 * Λ * Real.exp γB * N ^ 2, by dsimp [N]; positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν f
  dsimp only
  have hgen : ∃ g, IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g := by
    cases ν with
    | inl j =>
      obtain ⟨b, hb⟩ := timeFlux_drift_generator (i := ⟨0, by omega⟩) (ζ := ζ) hβ j
      obtain ⟨c, hc⟩ := timeFlux_coefficient_generator (i := ⟨0, by omega⟩) (ζ := ζ)
        hQ ha ⟨0, by omega⟩ j
      exact ⟨b + ζ • c, hb.add (hc.smul ζ)⟩
    | inr u =>
      obtain ⟨c, hc⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      exact ⟨ζ • c, hc.smul ζ⟩
  obtain ⟨g, hfg⟩ := hgen
  obtain ⟨hβb, hab, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  have hfb : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ N := by
    cases ν with
    | inl j =>
      filter_upwards [hβb j, hab ⟨0, by omega⟩ j,
        Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
        Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j)] with ω hβω haω hadd hsmul
      change ‖(β j + ζ • a ⟨0, by omega⟩ j) ω‖ ≤ N
      rw [hadd]
      change ‖β j ω + (ζ • a ⟨0, by omega⟩ j) ω‖ ≤ N
      rw [hsmul]
      change ‖β j ω + ζ * a ⟨0, by omega⟩ j ω‖ ≤ N
      calc
        _ ≤ ‖β j ω‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ j ω‖ := by simpa only [norm_mul] using norm_add_le (β j ω) (ζ * a ⟨0, by omega⟩ j ω)
        _ ≤ M + B * M := add_le_add hβω (mul_le_mul hζ haω (norm_nonneg _) hB.le)
        _ = N := by dsimp only [N]; ring
    | inr u =>
      filter_upwards [hμb, Lp.coeFn_smul ζ μ] with ω hμω hsmul
      change ‖(ζ • μ) ω‖ ≤ N
      rw [hsmul]
      change ‖ζ * μ ω‖ ≤ N
      rw [norm_mul]
      exact (mul_le_mul hζ hμω (norm_nonneg _) hB.le).trans (by dsimp only [N]; nlinarith)
  have hfsp : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖f (translate x ω)‖ ≤ N := by
    apply (Measure.ae_ae_comm ?_).mp (ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hfb)
    exact measurableSet_le (((Lp.stronglyMeasurable f).measurable.comp
      Probability.continuous_translate.measurable).norm) measurable_const
  obtain ⟨D, hD, heD, henergy⟩ := short_time_stationary_damped_gradient_energy hd Q hP hfg
  refine ⟨D, hD, heD, ?_⟩
  intro T hT L hL
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  have h4L : 64 * Λ ^ 3 ≤ 4 * L := hL.trans (by linarith)
  filter_upwards [henergy T hT (4 * L) h4L, hfsp] with ω he hfω
  obtain ⟨hints, he⟩ := he
  refine ⟨hints L hLp, ?_⟩
  let γ := 16 * Λ ^ 3 * ‖ζ‖ ^ 2
  let H : ℝ × Vec d → ℝ := fun p => ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2
  let τ : Measure ℝ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
  have hγ : γ ≤ γB := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hζ 2) (by positivity)
  have hGi : Integrable (fun x : Vec d => Real.exp (-euclideanSq x / (4 * L))) := by
    have hp := Integrable.fintype_prod (fun _ : Fin d =>
      integrable_exp_neg_mul_sq (show 0 < (4 * L)⁻¹ by positivity))
    convert hp using 1
    funext x
    rw [← Real.exp_sum]
    congr 1
    simp only [euclideanSq, dot, ← Finset.mul_sum, sq, div_eq_mul_inv]
    ring


  have hinit : (∫ x, Real.exp (-euclideanSq x / (2 * (4 * L))) ^ 2 *
        ‖f (translate x ω)‖ ^ 2) ≤
      N ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) := by
    rw [← integral_const_mul]
    apply integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (hGi.const_mul (N ^ 2))
    filter_upwards [hfω] with x hx
    have hg : Real.exp (-euclideanSq x / (2 * (4 * L))) ^ 2 =
        Real.exp (-euclideanSq x / (4 * L)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hg, mul_comm (N ^ 2)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hx 2) (Real.exp_nonneg _)
  let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (4 * L * (2 - p.1)))
  let J : ℝ × Vec d → ℝ := fun p => Real.exp (-γ * p.1) * (η p ^ 2 * H p)
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hHm : Measurable H := Finset.measurable_sum _ fun j _ =>
    ((hD j).comp hshift).norm.pow_const 2
  have hJm : Measurable J := by dsimp only [J, η, euclideanSq, dot]; fun_prop
  have htime : ∀ᵐ p : ℝ × Vec d ∂τ.prod volume, p.1 ∈ Icc (0 : ℝ) (T : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact ae_of_all _ fun _ => hs
  have hγ0 : 0 ≤ γ := by dsimp only [γ]; positivity
  have hJi : Integrable J (τ.prod volume) := by
    apply (hints (4 * L) (by positivity)).mono' hJm.aestronglyMeasurable
    filter_upwards [htime] with p hp
    have hb := (short_time_moving_gaussian_bounds p.2 (by positivity : 0 < 4 * L)
      ⟨hp.1, hp.2.trans hT⟩).1
    have heq : Real.exp (-euclideanSq p.2 / (4 * (4 * L))) ^ 2 =
        Real.exp (-euclideanSq p.2 / (2 * (4 * L))) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [heq] at hb
    have hm : Real.exp (-γ * p.1) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ0) hp.1)
    change ‖Real.exp (-γ * p.1) * (η p ^ 2 * H p)‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun j _ => sq_nonneg _)))]
    exact (mul_le_of_le_one_left (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)) hm).trans
      (mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun j _ => sq_nonneg _))
  have hwide := hints L hLp
  have hcmp : (∫ p, Real.exp (-euclideanSq p.2 / (2 * L)) * H p ∂τ.prod volume) ≤
      Real.exp γB * (∫ p, J p ∂τ.prod volume) := by
    rw [← integral_const_mul]
    apply integral_mono_ae hwide (hJi.const_mul (Real.exp γB))
    filter_upwards [htime] with p hp
    have hs : p.1 ≤ 1 := hp.2.trans hT
    have hq : 0 ≤ euclideanSq p.2 := by
      change 0 ≤ ∑ j : Fin d, p.2 j * p.2 j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hden : 0 < 4 * L * (2 - p.1) := mul_pos (by positivity) (by linarith)
    have hw : Real.exp (-euclideanSq p.2 / (2 * L)) ≤ η p ^ 2 := by
      dsimp only [η]
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hdiv : euclideanSq p.2 / (2 * L * (2 - p.1)) ≤ euclideanSq p.2 / (2 * L) := by
        apply (div_le_div_iff₀ (mul_pos (by positivity) (by linarith) : 0 < 2 * L * (2 - p.1)) (by positivity : 0 < 2 * L)).mpr
        nlinarith [mul_nonneg (mul_nonneg hq hLp.le) (sub_nonneg.mpr hs)]
      convert neg_le_neg hdiv using 1 <;> push_cast <;> field_simp; ring
    have hm : 1 ≤ Real.exp γB * Real.exp (-γ * p.1) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      have hg : γ * p.1 ≤ γ := mul_le_of_le_one_right hγ0 hs
      linarith
    change Real.exp (-euclideanSq p.2 / (2 * L)) * H p ≤
      Real.exp γB * (Real.exp (-γ * p.1) * (η p ^ 2 * H p))
    calc
      _ ≤ η p ^ 2 * H p := mul_le_mul_of_nonneg_right hw (Finset.sum_nonneg fun j _ => sq_nonneg _)
      _ ≤ (Real.exp γB * Real.exp (-γ * p.1)) * (η p ^ 2 * H p) :=
        le_mul_of_one_le_left (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)) hm
      _ = _ := by ring
  have he' : (Λ⁻¹ / 4) * (∫ p, J p ∂τ.prod volume) ≤
      ∫ x, Real.exp (-euclideanSq x / (2 * (4 * L))) ^ 2 * ‖f (translate x ω)‖ ^ 2 := by
    rw [integral_prod _ hJi]
    simpa only [J, η, H, γ, Λ, τ, integral_const_mul, mul_assoc] using he
  have hjb : (∫ p, J p ∂τ.prod volume) ≤ 4 * Λ *
      (N ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < Λ⁻¹ / 4)).mp
    calc
      _ ≤ _ := he'.trans hinit
      _ = (Λ⁻¹ / 4) * (4 * Λ * (N ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))))) := by
        field_simp
  have hresult := hcmp.trans (mul_le_mul_of_nonneg_left hjb (Real.exp_nonneg γB))
  rw [integral_prod _ hwide] at hresult
  convert hresult using 1; ring

/-- The actual forward and clock gradient sources have deterministic exterior
Gaussian tails. The same joint representative satisfies the wider energy and
all radius bounds on one sample event at each time horizon and width. -/
theorem short_time_forward_clock_uniform_gradient_source
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P, ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    let Λ := Real.exp (2 * S.ellipticity) * S.ellipticity
    ∃ D : Fin d → ℝ × FieldPair d → ℂ, (∀ j, Measurable (D j)) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit f s) j) ∧
      ∀ T : ℝ≥0, (T : ℝ) ≤ 1 → ∀ L : ℝ, 64 * Λ ^ 3 ≤ L →
      ∀ᵐ ω ∂reducedLaw Q,
        Integrable (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / (2 * L)) *
          ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2)
          ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ∧
        (∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x,
          Real.exp (-euclideanSq x / (2 * L)) * ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          K * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L))) ∧
        ∀ R : ℝ, 0 ≤ R →
          IntegrableOn (fun s => ∫ x in {x : Vec d | R ≤ euclideanNorm x},
            Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) (Icc (0 : ℝ) (T : ℝ)) ∧
          (∫ s in Icc (0 : ℝ) (T : ℝ), ∫ x in {x : Vec d | R ≤ euclideanNorm x},
            Real.exp (-euclideanSq x / (L * (2 - s))) ^ 2 *
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
            Real.exp (-R ^ 2 / (2 * L)) *
              (K * (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) := by
  obtain ⟨K, hK, henergy⟩ := short_time_forward_clock_uniform_gradient_energy d hd S B hB
  refine ⟨K, hK, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ P hP ν
  obtain ⟨D, hD, heD, hwide⟩ := henergy Q hQ β a μ hβ ha hμ ζ hζ P hP ν
  refine ⟨D, hD, heD, ?_⟩
  intro T hT L hL
  have hΛ : 0 < Real.exp (2 * S.ellipticity) * S.ellipticity :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one S.one_le_ellipticity)
  have hLp : 0 < L := lt_of_lt_of_le (by positivity) hL
  filter_upwards [hwide T hT L hL] with ω hω
  obtain ⟨hi, hb⟩ := hω
  refine ⟨hi, hb, ?_⟩
  intro R hR
  let H : ℝ × Vec d → ℝ := fun p => ∑ j, ‖D j (p.1, translate p.2 ω)‖ ^ 2
  have hshift : Measurable (fun p : ℝ × Vec d => (p.1, translate p.2 ω)) :=
    measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const))
  have hH : Measurable H := Finset.measurable_sum _ fun j _ =>
    ((hD j).comp hshift).norm.pow_const 2
  obtain ⟨htaili, htail⟩ := short_time_gaussian_exterior_spacetime_source
    R L T hR hLp hT H hH (fun p => Finset.sum_nonneg fun j _ => sq_nonneg _) hi
  exact ⟨htaili, htail.trans (mul_le_mul_of_nonneg_left hb (Real.exp_nonneg _))⟩

/-- Initial cutoff errors for the actual combined forward and clock data,
with one event for every cutoff, radius and Gaussian width. -/
theorem short_time_forward_clock_actual_initial_gaussian_bound
    (d : ℕ) (hd : 2 ≤ d) (S : StructuralData d) (B : ℝ) (hB : 0 < B) :
    ∃ K : ℝ, 0 < K ∧
    ∀ (Q : EnvironmentLaw d S.ellipticity S.dependenceRange) (hQ : HasSmoothBounds S Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ), ‖ζ‖ ≤ B → ∀ ν : Fin d ⊕ Unit,
    let f := ν.elim (fun j => β j + ζ • a ⟨0, by omega⟩ j) (fun _ => ζ • μ)
    ∀ᵐ ω ∂reducedLaw Q, ∀ (χ : C(Vec d, ℝ)),
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
      ∀ R L : ℝ, 0 ≤ R → 0 < L → (∀ x, euclideanNorm x ≤ R → χ x = 1) →
      Integrable (fun x => Real.exp (-euclideanSq x / (2 * L)) ^ 2 *
        ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) ∧
      (∫ x, Real.exp (-euclideanSq x / (2 * L)) ^ 2 *
        ‖f (translate x ω) - (χ x : ℂ) * f (translate x ω)‖ ^ 2) ≤
        Real.exp (-R ^ 2 / (2 * L)) *
          (K ^ 2 * ∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) := by
  obtain ⟨M, hM, hb⟩ := EndpointFiniteP.observation_bounds d S
  let N := M * (1 + B)
  refine ⟨N, by dsimp only [N]; positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ hζ ν f
  obtain ⟨hβb, hab, hμb⟩ := hb Q hQ β a μ hβ ha hμ
  have hfb : ∀ᵐ ω ∂reducedLaw Q, ‖f ω‖ ≤ N := by
    cases ν with
    | inl j =>
      filter_upwards [hβb j, hab ⟨0, by omega⟩ j,
        Lp.coeFn_add (β j) (ζ • a ⟨0, by omega⟩ j),
        Lp.coeFn_smul ζ (a ⟨0, by omega⟩ j)] with ω hβω haω hadd hsmul
      change ‖(β j + ζ • a ⟨0, by omega⟩ j) ω‖ ≤ N
      rw [hadd]
      change ‖β j ω + (ζ • a ⟨0, by omega⟩ j) ω‖ ≤ N
      rw [hsmul]
      change ‖β j ω + ζ * a ⟨0, by omega⟩ j ω‖ ≤ N
      calc
        _ ≤ ‖β j ω‖ + ‖ζ‖ * ‖a ⟨0, by omega⟩ j ω‖ := by simpa only [norm_mul] using norm_add_le (β j ω) (ζ * a ⟨0, by omega⟩ j ω)
        _ ≤ M + B * M := add_le_add hβω (mul_le_mul hζ haω (norm_nonneg _) hB.le)
        _ = N := by dsimp only [N]; ring
    | inr u =>
      filter_upwards [hμb, Lp.coeFn_smul ζ μ] with ω hμω hsmul
      change ‖(ζ • μ) ω‖ ≤ N
      rw [hsmul]
      change ‖ζ * μ ω‖ ≤ N
      rw [norm_mul]
      exact (mul_le_mul hζ hμω (norm_nonneg _) hB.le).trans (by dsimp only [N]; nlinarith)
  have hfsp : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      ‖f (translate x ω)‖ ≤ N := by
    apply (Measure.ae_ae_comm ?_).mp (ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hfb)
    exact measurableSet_le (((Lp.stronglyMeasurable f).measurable.comp
      Probability.continuous_translate.measurable).norm) measurable_const
  filter_upwards [hfsp] with ω hω
  intro χ hχ R L hR hL hin
  exact short_time_cutoff_initial_gaussian_bound _
    ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))) N hω χ hχ R L hR hL hin

/-- A fixed Gaussian forcing bound controls the damped shrinking-Gaussian
forcing in the retained comparison, preserving its divergence-source factor.
The inputs are scalar nonnegative source energies, so the statement applies
to the actual retained flux and drift defects without choosing new orbits. -/
theorem short_time_damped_moving_gaussian_forcing_bound {d : ℕ}
    (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) (L Λ γ : ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hγ : 0 ≤ γ)
    (f g : ℝ × Vec d → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ p, 0 ≤ f p) (hg0 : ∀ p, 0 ≤ g p)
    (hi : Integrable (fun p => Real.exp (-euclideanSq p.2 / L) * (f p + g p))
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume)) :
    let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
    IntegrableOn (fun s => Real.exp (-γ * s) *
      ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * f (s, x)) +
        (∫ x, η (s, x) ^ 2 * g (s, x)))) (Icc (0 : ℝ) (T : ℝ)) ∧
    (∫ s in Icc (0 : ℝ) (T : ℝ), Real.exp (-γ * s) *
      ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * f (s, x)) +
        (∫ x, η (s, x) ^ 2 * g (s, x)))) ≤
      (4 * Λ + 16 / L + 1) *
        (∫ p : ℝ × Vec d, Real.exp (-euclideanSq p.2 / L) * (f p + g p)
          ∂(volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) := by
  intro η
  let τ := volume.restrict (Icc (0 : ℝ) (T : ℝ))
  let A := 4 * Λ + 16 / L
  let W : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / L)
  let J : ℝ × Vec d → ℝ := fun p => Real.exp (-γ * p.1) *
    (A * (η p ^ 2 * f p) + η p ^ 2 * g p)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hηm : Measurable η := by dsimp only [η, euclideanSq, dot]; fun_prop
  have hJm : Measurable J := by
    dsimp only [J]
    exact (Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul
      (((hηm.pow_const 2).mul hf).const_mul A |>.add ((hηm.pow_const 2).mul hg))
  have htime : ∀ᵐ p : ℝ × Vec d ∂τ.prod volume, p.1 ∈ Icc (0 : ℝ) (T : ℝ) :=
    (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_fst)).mpr (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ae_of_all _ fun _ => hs)
  have hηbound (p : ℝ × Vec d) (hp : p.1 ∈ Icc (0 : ℝ) (T : ℝ)) :
      η p ^ 2 ≤ W p := by
    have hq : 0 ≤ euclideanSq p.2 := by
      change 0 ≤ ∑ j : Fin d, p.2 j * p.2 j
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hden : 0 < L * (2 - p.1) := mul_pos hL (by linarith [hp.2.trans hT])
    have he : euclideanSq p.2 / L ≤ 2 * euclideanSq p.2 / (L * (2 - p.1)) := by
      apply (div_le_div_iff₀ hL hden).mpr
      nlinarith [mul_nonneg (mul_nonneg hq hL.le) hp.1]
    dsimp only [η, W]
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    convert neg_le_neg he using 1 <;> ring
  have hFi : Integrable (fun p => η p ^ 2 * f p) (τ.prod volume) := by
    apply hi.mono' ((hηm.pow_const 2).mul hf).aestronglyMeasurable
    filter_upwards [htime] with p hp
    change ‖η p ^ 2 * f p‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hf0 p))]
    exact (mul_le_mul_of_nonneg_right (hηbound p hp) (hf0 p)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (hg0 p)) (Real.exp_nonneg _))
  have hGi : Integrable (fun p => η p ^ 2 * g p) (τ.prod volume) := by
    apply hi.mono' ((hηm.pow_const 2).mul hg).aestronglyMeasurable
    filter_upwards [htime] with p hp
    change ‖η p ^ 2 * g p‖ ≤ _
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hg0 p))]
    exact (mul_le_mul_of_nonneg_right (hηbound p hp) (hg0 p)).trans
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hf0 p)) (Real.exp_nonneg _))
  have hJ0 (p : ℝ × Vec d) : 0 ≤ J p :=
    mul_nonneg (Real.exp_nonneg _) (add_nonneg
      (mul_nonneg hA (mul_nonneg (sq_nonneg _) (hf0 p)))
      (mul_nonneg (sq_nonneg _) (hg0 p)))
  have hbound : ∀ᵐ p ∂τ.prod volume,
      J p ≤ (A + 1) * (W p * (f p + g p)) := by
    filter_upwards [htime] with p hp
    have hdamp : Real.exp (-γ * p.1) ≤ 1 := Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ) hp.1)
    have hsrc : A * f p + g p ≤ (A + 1) * (f p + g p) := by
      nlinarith [hf0 p, hg0 p, mul_nonneg hA (hg0 p)]
    calc
      J p ≤ A * (η p ^ 2 * f p) + η p ^ 2 * g p :=
        mul_le_of_le_one_left (add_nonneg
          (mul_nonneg hA (mul_nonneg (sq_nonneg _) (hf0 p)))
          (mul_nonneg (sq_nonneg _) (hg0 p))) hdamp
      _ = η p ^ 2 * (A * f p + g p) := by ring
      _ ≤ W p * (A * f p + g p) := mul_le_mul_of_nonneg_right (hηbound p hp)
        (add_nonneg (mul_nonneg hA (hf0 p)) (hg0 p))
      _ ≤ W p * ((A + 1) * (f p + g p)) :=
        mul_le_mul_of_nonneg_left hsrc (Real.exp_nonneg _)
      _ = (A + 1) * (W p * (f p + g p)) := by ring
  have hJi : Integrable J (τ.prod volume) := by
    apply (hi.const_mul (A + 1)).mono' hJm.aestronglyMeasurable
    filter_upwards [hbound] with p hp
    simpa only [Real.norm_of_nonneg (hJ0 p)] using hp
  have he : (fun s => ∫ x, J (s, x)) =ᵐ[τ]
      (fun s => Real.exp (-γ * s) *
        (A * (∫ x, η (s, x) ^ 2 * f (s, x)) +
          (∫ x, η (s, x) ^ 2 * g (s, x)))) := by
    filter_upwards [hFi.prod_right_ae, hGi.prod_right_ae] with s hfs hgs
    dsimp only [J]
    rw [integral_const_mul, integral_add (hfs.const_mul A) hgs, integral_const_mul]
  refine ⟨hJi.integral_prod_left.congr he, ?_⟩
  change (∫ s, Real.exp (-γ * s) *
    (A * (∫ x, η (s, x) ^ 2 * f (s, x)) +
      (∫ x, η (s, x) ^ 2 * g (s, x))) ∂τ) ≤ _
  rw [← integral_congr_ae he, ← integral_prod _ hJi]
  simpa only [integral_const_mul, A, W] using
    integral_mono_ae hJi (hi.const_mul (A + 1)) hbound

/-- The complete initial-plus-forcing right side of the retained comparison
has a Gaussian radius bound. The flux and drift are arbitrary measurable
complex sources, allowing the same actual gradient representative and event
as the finite comparison to be used without a new choice. -/
theorem short_time_cutoff_comparison_gaussian_rhs_bound {d : ℕ}
    (T : ℝ≥0) (hT : (T : ℝ) ≤ 1) (L Λ γ R M C : ℝ)
    (hL : 0 < L) (hΛ : 0 ≤ Λ) (hγ : 0 ≤ γ) (hR : 0 ≤ R)
    (u : Vec d → ℂ) (hu : Measurable u)
    (hub : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖u x‖ ≤ M)
    (χ : C(Vec d, ℝ)) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1)
    (hin : ∀ x, euclideanNorm x ≤ R → χ x = 1)
    (F : Fin d → ℝ × Vec d → ℂ) (G : ℝ × Vec d → ℂ)
    (hF : ∀ j, Measurable (F j)) (hG : Measurable G)
    (hi : Integrable (fun p : ℝ × Vec d =>
      (∑ j, Real.exp (-euclideanSq p.2 / L) * ‖F j p‖ ^ 2) +
        Real.exp (-euclideanSq p.2 / L) * ‖G p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume))
    (hb : (∫ p : ℝ × Vec d,
      (∑ j, Real.exp (-euclideanSq p.2 / L) * ‖F j p‖ ^ 2) +
        Real.exp (-euclideanSq p.2 / L) * ‖G p‖ ^ 2
      ∂(volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) ≤
      C * Real.exp (-R ^ 2 / (2 * L)) *
        (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) :
    let η : ℝ × Vec d → ℝ := fun p => Real.exp (-euclideanSq p.2 / (L * (2 - p.1)))
    Integrable (fun x => η (0, x) ^ 2 * ‖u x - (χ x : ℂ) * u x‖ ^ 2) ∧
    IntegrableOn (fun s => Real.exp (-γ * s) *
      ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖F j (s, x)‖ ^ 2) +
        (∫ x, η (s, x) ^ 2 * ‖G (s, x)‖ ^ 2))) (Icc (0 : ℝ) (T : ℝ)) ∧
    (∫ x, η (0, x) ^ 2 * ‖u x - (χ x : ℂ) * u x‖ ^ 2) +
      (∫ s in Icc (0 : ℝ) (T : ℝ), Real.exp (-γ * s) *
        ((4 * Λ + 16 / L) * (∫ x, η (s, x) ^ 2 * ∑ j, ‖F j (s, x)‖ ^ 2) +
          (∫ x, η (s, x) ^ 2 * ‖G (s, x)‖ ^ 2))) ≤
      Real.exp (-R ^ 2 / (2 * L)) *
        (M ^ 2 * (∫ x : Vec d, Real.exp (-euclideanSq x / (2 * L))) +
          (4 * Λ + 16 / L + 1) * C *
            (∫ x : Vec d, Real.exp (-euclideanSq x / (4 * L)))) := by
  intro η
  have hη0 (x : Vec d) : η (0, x) = Real.exp (-euclideanSq x / (2 * L)) := by
    dsimp only [η]
    congr 1
    ring
  obtain ⟨hi0, hb0⟩ := short_time_cutoff_initial_gaussian_bound u hu M hub χ hχ R L hR hL hin
  have hfi : Integrable (fun p : ℝ × Vec d => Real.exp (-euclideanSq p.2 / L) *
      ((∑ j, ‖F j p‖ ^ 2) + ‖G p‖ ^ 2))
      ((volume.restrict (Icc (0 : ℝ) (T : ℝ))).prod volume) := by
    simpa only [mul_add, Finset.mul_sum] using hi
  obtain ⟨hif, hbf⟩ := short_time_damped_moving_gaussian_forcing_bound T hT L Λ γ
    hL hΛ hγ (fun p => ∑ j, ‖F j p‖ ^ 2) (fun p => ‖G p‖ ^ 2)
    (Finset.measurable_sum _ (fun j _ => (hF j).norm.pow_const 2))
    (hG.norm.pow_const 2) (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg _))
    (fun p => sq_nonneg _) hfi
  have hs := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ 4 * Λ + 16 / L + 1 by positivity)
  have hbf' := hbf.trans (by simpa only [mul_add, Finset.mul_sum] using hs)
  refine ⟨by simpa only [hη0] using hi0, hif, ?_⟩
  simp only [hη0]
  apply (add_le_add hb0 hbf').trans_eq
  ring


/-- Inside the retained region the stationary-minus-retained difference has
zero coefficient defect, with the same signed complex force. -/
theorem short_time_retained_interior_divergence {d : ℕ}
    (χ : C(Vec d, ℝ)) (ω : FieldPair d) (U : Set (Vec d))
    (hU : MeasurableSet U) (hχ : ∀ x ∈ U, χ x = 1)
    (i : Fin d) (ζ : ℂ) (g h : Vec d → ℂ) (Gu Gv : Fin d → Vec d → ℂ)
    (hdiv : ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1/2 : ℂ) * ∑ k, (ω.1 x j k : ℂ) * Gu k x))
        (fun x => L (g x - ζ * ∑ j, (ω.1 x j i : ℂ) * Gu j x)))
    (hdiv' : ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence Set.univ
        (fun x j => L ((1/2 : ℂ) *
          ∑ k, ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * Gv k x))
        (fun x => L (h x - ζ *
          ∑ j, ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * Gv j x))) :
    ∀ L : ℂ →L[ℝ] ℝ,
      HasWeakDivergence U
        (fun x j => L ((1/2 : ℂ) * ∑ k,
          ((ForcedLocality.retainedPair χ ω).1 x j k : ℂ) * (Gu k x - Gv k x)))
        (fun x => L ((g x - h x) - ζ * ∑ j,
          ((ForcedLocality.retainedPair χ ω).1 x j i : ℂ) * (Gu j x - Gv j x))) := by
  intro L
  have hw := short_time_forward_residual_divergence ω.1
    (ForcedLocality.retainedPair χ ω).1 i ζ g h Gu Gv hdiv hdiv' L
  apply (HasWeakDivergence.restrict_subset (Set.subset_univ U)
    MeasurableSet.univ hw).congr_ae
  · filter_upwards [ae_restrict_mem hU] with x hx
    have he := (ForcedLocality.retainedPair_eq_at χ ω (hχ x hx)).1
    funext j
    simp only [he, sub_self, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, sub_zero]
  · filter_upwards [ae_restrict_mem hU] with x hx
    have he := (ForcedLocality.retainedPair_eq_at χ ω (hχ x hx)).1
    simp only [he, sub_self, Complex.ofReal_zero, zero_mul,
      Finset.sum_const_zero, mul_zero, sub_zero]


/-- Join the time equation and spatial divergence for arbitrary joint tests.
This preserves the lower-order term and tests that cross time zero. -/
theorem short_time_spacetime_weak_equation {d : ℕ}
    (U : Set (Vec d)) (u v b : ℝ × Vec d → ℝ)
    (F : ℝ × Vec d → Vec d)
    (htime : ∀ᵐ x ∂volume.restrict U, ∀ ψ : ℝ → ℝ,
      ContDiff ℝ 1 ψ → ψ (-1) = 0 → ψ 1 = 0 →
      (∫ s in (-1 : ℝ)..1, deriv ψ s * u (s, x) + ψ s * v (s, x)) = 0)
    (hspace : ∀ᵐ s ∂volume.restrict (Icc (-1 : ℝ) 1),
      HasWeakDivergence U (fun x => F (s, x)) (fun x => v (s, x) - b (s, x)))
    (φ : ℝ × Vec d → ℝ)
    (hφt : ∀ x, ContDiff ℝ 1 (fun s => φ (s, x)))
    (hφl : ∀ x, φ (-1, x) = 0) (hφr : ∀ x, φ (1, x) = 0)
    (hφx : ∀ s, IsSpatialTest U (fun x => φ (s, x)))
    (hu : Integrable (fun p : ℝ × Vec d =>
      deriv (fun s => φ (s, p.2)) p.1 * u p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hv : Integrable (fun p : ℝ × Vec d => φ p * v p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hF : Integrable (fun p : ℝ × Vec d =>
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2))
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)))
    (hb : Integrable (fun p : ℝ × Vec d => φ p * b p)
      ((volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U))) :
    (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p -
        dot (F p) (gradient (fun x => φ (p.1, x)) p.2) + φ p * b p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
  have ht : (∫ p : ℝ × Vec d,
      deriv (fun s => φ (s, p.2)) p.1 * u p + φ p * v p
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) = 0 := by
    have hp := integral_prod_symm _ (hu.add hv)
    simp only [Pi.add_apply] at hp
    rw [hp]
    apply integral_eq_zero_of_ae
    filter_upwards [htime] with x hx
    have he := hx (fun s => φ (s, x)) (hφt x) (hφl x) (hφr x)
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc] at he
    exact he
  have hs : (∫ p : ℝ × Vec d,
      dot (F p) (gradient (fun x => φ (p.1, x)) p.2)
      ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) =
      -(∫ p : ℝ × Vec d, φ p * v p - φ p * b p
        ∂(volume.restrict (Icc (-1 : ℝ) 1)).prod (volume.restrict U)) := by
    have hp := integral_prod _ (hv.sub hb)
    simp only [Pi.sub_apply] at hp
    rw [integral_prod _ hF, hp, ← integral_neg]
    apply integral_congr_ae
    filter_upwards [hspace] with s hs
    have he := hs.2.2 (fun x => φ (s, x)) (hφx s)
    rw [he]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have hsum := integral_add (hu.sub hF) hb
  have hdiff := integral_sub hu hF
  have htv := integral_add hu hv
  have hvb := integral_sub hv hb
  simp only [Pi.sub_apply] at hsum hdiff htv hvb
  rw [hsum, hdiff]
  rw [htv] at ht
  rw [hvb] at hs
  linarith

/-- Real matrix for the lift `Re (exp (y + I*z) * u)` of the complex drift.
The equal last two diagonal entries cancel on the harmonic exponential. -/
def shortTimeComplexLiftMatrix {d : ℕ} (A : PDE.Mat d) (i : Fin d)
    (ζ : ℂ) (M : ℝ) : PDE.Mat (d + 2) :=
  Fin.addCases
    (fun j => Fin.addCases (fun k => A j k / 2) (fun _ => 0))
    (fun j : Fin 2 => Fin.addCases
      (fun k => (if j = 0 then ζ.re else ζ.im) * A k i)
      (fun k => if j = k then M else 0))

private theorem short_time_elliptic_of_entry_bound {n : ℕ} {A : PDE.Mat n}
    {lam C : ℝ} (hlam : 0 < lam) (hC : 0 < C)
    (hlower : ∀ x, lam * PDE.vecNormSq x ≤ PDE.vecDot x (PDE.matVecMul A x))
    (hentry : ∀ j k, |A j k| ≤ C) :
    PDE.IsEllipticMatrix lam (lam + ((n : ℝ) ^ 2 * C ^ 2 + 1) / lam) A := by
  let K := (n : ℝ) ^ 2 * C ^ 2 + 1
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound (x : PDE.Vec n) : PDE.vecNormSq (PDE.matVecMul A x) ≤
      K * PDE.vecNormSq x := by
    have hrow (j : Fin n) : (∑ k, A j k * x k) ^ 2 ≤
        ((n : ℝ) * C ^ 2) * (∑ k, x k ^ 2) := by
      have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A j) x
      have he : (∑ k, A j k ^ 2) ≤ (n : ℝ) * C ^ 2 := by
        calc
          (∑ k, A j k ^ 2) ≤ ∑ _k : Fin n, C ^ 2 := by
            apply Finset.sum_le_sum
            intro k _
            simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hC.le).2 (hentry j k)
          _ = (n : ℝ) * C ^ 2 := by simp
      exact hs.trans (mul_le_mul_of_nonneg_right he
        (Finset.sum_nonneg fun k _ => sq_nonneg (x k)))
    rw [PDE.vecNormSq_eq_sum_sq, PDE.vecNormSq_eq_sum_sq]
    calc
      (∑ j, (PDE.matVecMul A x j) ^ 2) ≤
          ∑ _j : Fin n, ((n : ℝ) * C ^ 2) * (∑ k, x k ^ 2) :=
        Finset.sum_le_sum fun j _ => hrow j
      _ = (n : ℝ) ^ 2 * C ^ 2 * (∑ k, x k ^ 2) := by simp; ring
      _ ≤ K * (∑ k, x k ^ 2) := by
        dsimp [K]
        nlinarith [Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (x k)]
  have hinj : Function.Injective A.mulVec := by
    intro x y he
    have hz : A.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
    have hc := hlower (x - y)
    change lam * PDE.vecNormSq (x - y) ≤ PDE.vecDot (x - y) (A.mulVec (x - y)) at hc
    rw [hz] at hc
    simp only [PDE.vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hc
    have hs : PDE.vecNormSq (x - y) = 0 := by
      nlinarith [PDE.vecNormSq_nonneg (x - y)]
    exact sub_eq_zero.mp (PDE.vecNormSq_eq_zero hs)
  have hdet : IsUnit A.det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  have hL : 0 < lam + K / lam := by positivity
  refine ⟨hlam, le_add_of_nonneg_right (div_nonneg hK.le hlam.le), hlower, ?_⟩
  intro ξ
  let x := A⁻¹.mulVec ξ
  have hx : PDE.matVecMul A x = ξ := by
    change A.mulVec (A⁻¹.mulVec ξ) = ξ
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hb := hbound x
  rw [hx] at hb
  have hc := hlower x
  rw [hx, PDE.vecDot_comm] at hc
  change (lam + K / lam)⁻¹ * PDE.vecNormSq ξ ≤ PDE.vecDot ξ x
  apply (inv_mul_le_iff₀ hL).2
  have hq : 0 ≤ PDE.vecDot ξ x :=
    (mul_nonneg hlam.le (PDE.vecNormSq_nonneg x)).trans hc
  have hscale := mul_le_mul_of_nonneg_left hc (le_of_lt (div_pos hK hlam))
  have hcancel : K / lam * (lam * PDE.vecNormSq x) = K * PDE.vecNormSq x := by
    field_simp
  rw [hcancel] at hscale
  nlinarith [mul_nonneg hlam.le hq]

/-- Uniform real ellipticity of the triangular complex-drift lift.
Constants precede the matrix, coordinate and signed complex force. -/
theorem short_time_complex_lift_uniform_ellipticity {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ L : ℝ, 0 < L ∧ ∀ (A : PDE.Mat d), EinsteinFull.S5Elliptic A Λ →
      ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      PDE.IsEllipticMatrix (Λ⁻¹ / 4) L
        (shortTimeComplexLiftMatrix A i ζ (4 * Λ ^ 3 * (B ^ 2 + 1))) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  let M := 4 * Λ ^ 3 * (B ^ 2 + 1)
  let C := M + (B + 1) * Λ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  let lam := Λ⁻¹ / 4
  have hlam : 0 < lam := by dsimp [lam]; positivity
  refine ⟨lam + (((d + 2 : ℕ) : ℝ) ^ 2 * C ^ 2 + 1) / lam,
    by positivity, ?_⟩
  intro A hA i ζ hζ
  apply short_time_elliptic_of_entry_bound hlam hC
  · intro ξ
    let x : Fin d → ℝ := fun j => ξ (Fin.castAdd 2 j)
    let y := ξ (Fin.natAdd d 0)
    let z := ξ (Fin.natAdd d 1)
    let S := ∑ j, x j ^ 2
    let H := y ^ 2 + z ^ 2
    let R := ∑ j, x j * A j i
    let r := ζ.re * y + ζ.im * z
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hH : 0 ≤ H := by dsimp [H]; positivity
    have hR : R ^ 2 ≤ Λ ^ 2 * S := by
      have hr := EinsteinFull.s5_row_real_le hA i x
      have hs := pow_le_pow_left₀ (abs_nonneg R) hr 2
      rw [sq_abs] at hs
      simpa only [mul_pow, EinsteinFull.s5Nrm_sq, S] using hs
    have hr : r ^ 2 ≤ B ^ 2 * H := by
      have hz := Complex.sq_norm ζ
      simp only [Complex.normSq_apply] at hz
      have hb := mul_self_le_mul_self (norm_nonneg ζ) hζ
      have hp := mul_nonneg hH (sub_nonneg.mpr hb)
      dsimp [r, H] at *
      nlinarith [sq_nonneg (ζ.re * z - ζ.im * y)]
    have hlow := hA.lower x
    change Λ⁻¹ * S ≤ EinsteinFull.s5Bil A x x at hlow
    have hnorm : PDE.vecNormSq ξ = S + H := by
      simp [PDE.vecNormSq_eq_sum_sq, Fin.sum_univ_add, Fin.sum_univ_two, S, H, x, y, z]
    have hquad : PDE.vecDot ξ (PDE.matVecMul
        (shortTimeComplexLiftMatrix A i ζ M) ξ) =
        EinsteinFull.s5Bil A x x / 2 + r * R + M * H := by
      have hmain : (∑ j, x j * (∑ k, A j k / 2 * x k)) =
          EinsteinFull.s5Bil A x x / 2 := by
        simp only [EinsteinFull.s5Bil, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      have hrow (c : ℝ) : (∑ k, c * A k i * x k) = c * R := by
        dsimp [R]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      simp only [PDE.vecDot, PDE.matVecMul, shortTimeComplexLiftMatrix,
        Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
        Fin.sum_univ_two]
      simp only [Fin.isValue, zero_ne_one, one_ne_zero, ↓reduceIte, zero_mul, add_zero]
      change (∑ j, x j * (∑ k, A j k / 2 * x k)) +
        (y * ((∑ k, ζ.re * A k i * x k) + M * y) +
          z * ((∑ k, ζ.im * A k i * x k) + (0 + M * z))) = _
      rw [hmain, hrow, hrow]
      dsimp only [r, H]
      ring
    rw [hnorm, hquad]
    have hΛ3 : 0 < Λ ^ 3 := pow_pos hΛ0 _
    have hyoung : -(Λ⁻¹ / 4 * S) ≤ r * R + Λ ^ 3 * r ^ 2 := by
      have hnonneg := mul_nonneg (inv_nonneg.mpr (pow_nonneg hΛ0.le 3))
        (sq_nonneg (R + 2 * Λ ^ 3 * r))
      have he : (Λ ^ 3)⁻¹ * (R + 2 * Λ ^ 3 * r) ^ 2 =
          (Λ ^ 3)⁻¹ * R ^ 2 + 4 * r * R + 4 * Λ ^ 3 * r ^ 2 := by
        field_simp; ring
      rw [he] at hnonneg
      have hscaled := mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hΛ3.le)
      have he2 : (Λ ^ 3)⁻¹ * (Λ ^ 2 * S) = Λ⁻¹ * S := by
        field_simp
      rw [he2] at hscaled
      nlinarith
    have hscaled := mul_le_mul_of_nonneg_left hr hΛ3.le
    have hΛinv : Λ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ
    have hΛ3one : 1 ≤ Λ ^ 3 := one_le_pow₀ hΛ
    have hMH : (Λ⁻¹ / 4) * H + Λ ^ 3 * (B ^ 2 * H) ≤ M * H := by
      have hc : Λ⁻¹ / 4 + Λ ^ 3 * B ^ 2 ≤ M := by
        dsimp [M]
        nlinarith [mul_nonneg hΛ3.le (sq_nonneg B)]
      nlinarith [mul_le_mul_of_nonneg_right hc hH]
    dsimp only [lam]
    nlinarith
  · intro j k
    have hentry (j k : Fin d) : |A j k| ≤ Λ := by
      have he := EinsteinFull.s5Bil_abs_le hA
        (Pi.single j (1 : ℝ)) (Pi.single k (1 : ℝ))
      simpa [EinsteinFull.s5Bil, EinsteinFull.s5Nrm_single, Pi.single_apply] using he
    have hre : |ζ.re| ≤ B := (Complex.abs_re_le_norm ζ).trans hζ
    have him : |ζ.im| ≤ B := (Complex.abs_im_le_norm ζ).trans hζ
    have hcA : Λ ≤ C := by dsimp [C]; nlinarith [mul_nonneg hB hΛ0.le]
    have hcB : B * Λ ≤ C := by dsimp [C]; nlinarith
    have hcM : M ≤ C := by dsimp [C]; nlinarith [mul_nonneg (by linarith : 0 ≤ B + 1) hΛ0.le]
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simp only [shortTimeComplexLiftMatrix, Fin.addCases_left]
      rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      linarith [hentry j k]
    · simpa [shortTimeComplexLiftMatrix] using hC.le
    · simp only [shortTimeComplexLiftMatrix, Fin.addCases_right, Fin.addCases_left,
        abs_mul]
      split_ifs
      · exact (mul_le_mul hre (hentry k i) (abs_nonneg _) hB).trans hcB
      · exact (mul_le_mul him (hentry k i) (abs_nonneg _) hB).trans hcB
    · simp only [shortTimeComplexLiftMatrix, Fin.addCases_right]
      split_ifs
      · exact (abs_of_pos hM).le.trans hcM
      · simpa using hC.le

/-- The exponential complex-drift lift preserves the actual spatial H1
representatives. Its last two weak derivatives are the real and negative
imaginary parts of the lifted value. No classical derivative of the datum
or coefficient field is required. -/
theorem short_time_complex_lift_H1 {d : ℕ} {U : Set (PDE.Vec d)}
    {V : Set (PDE.Vec 2)} (hU : IsOpen U) (hV : IsOpen V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u v : PDE.H1Function U) :
    ∃ w : PDE.H1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)),
      (∀ z, w z = (Complex.exp
        ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          ⟨u (PDE.vecAppendEquiv d 2 z).1, v (PDE.vecAppendEquiv d 2 z).1⟩).re) ∧
      (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
        ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          ⟨u.grad (PDE.vecAppendEquiv d 2 z).1 j,
            v.grad (PDE.vecAppendEquiv d 2 z).1 j⟩).re) ∧
      (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w z) ∧
      (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
        ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          ⟨u (PDE.vecAppendEquiv d 2 z).1, v (PDE.vecAppendEquiv d 2 z).1⟩).im) := by
  let E := PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)
  let a : Fin (d + 2) := Fin.natAdd d (0 : Fin 2)
  let b : Fin (d + 2) := Fin.natAdd d (1 : Fin 2)
  let f : PDE.Vec (d + 2) → ℝ := fun z => Real.exp (z a) * Real.cos (z b)
  let g : PDE.Vec (d + 2) → ℝ := fun z => Real.exp (z a) * Real.sin (z b)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by dsimp [f]; fun_prop
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by dsimp [g]; fun_prop
  have hDf (z : PDE.Vec (d + 2)) (j : Fin (d + 2)) :
      PDE.classicalGradient f z j =
        f z * PDE.basisVec j a - g z * PDE.basisVec j b := by
    have ha := (ContinuousLinearMap.proj a : PDE.Vec (d + 2) →L[ℝ] ℝ).hasFDerivAt (x := z)
    have hb := (ContinuousLinearMap.proj b : PDE.Vec (d + 2) →L[ℝ] ℝ).hasFDerivAt (x := z)
    have he := congrArg (fun L : PDE.Vec (d + 2) →L[ℝ] ℝ => L (PDE.basisVec j))
      (ha.exp.mul hb.cos).fderiv
    dsimp [PDE.classicalGradient, f, g] at *
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] at he
    change (fderiv ℝ (fun x : PDE.Vec (d + 2) =>
      Real.exp (x a) * Real.cos (x b)) z) (PDE.basisVec j) = _ at he
    rw [he]
    ring
  have hDg (z : PDE.Vec (d + 2)) (j : Fin (d + 2)) :
      PDE.classicalGradient g z j =
        g z * PDE.basisVec j a + f z * PDE.basisVec j b := by
    have ha := (ContinuousLinearMap.proj a : PDE.Vec (d + 2) →L[ℝ] ℝ).hasFDerivAt (x := z)
    have hb := (ContinuousLinearMap.proj b : PDE.Vec (d + 2) →L[ℝ] ℝ).hasFDerivAt (x := z)
    have he := congrArg (fun L : PDE.Vec (d + 2) →L[ℝ] ℝ => L (PDE.basisVec j))
      (ha.exp.mul hb.sin).fderiv
    dsimp [PDE.classicalGradient, f, g] at *
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.proj_apply, smul_eq_mul] at he
    change (fderiv ℝ (fun x : PDE.Vec (d + 2) =>
      Real.exp (x a) * Real.sin (x b)) z) (PDE.basisVec j) = _ at he
    rw [he]
    ring
  have hbound (z : PDE.Vec (d + 2)) (hz : z ∈ E) :
      |f z| ≤ Real.exp r ∧ |g z| ≤ Real.exp r := by
    have ha : z a ≤ r := hr (PDE.vecAppendEquiv d 2 z).2 hz.2
    have he := Real.exp_le_exp.mpr ha
    constructor
    · calc
        |f z| = Real.exp (z a) * |Real.cos (z b)| := by
          simp [f, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (z a) * 1 := mul_le_mul_of_nonneg_left
          (Real.abs_cos_le_one _) (Real.exp_pos _).le
        _ ≤ Real.exp r := by simpa using he
    · calc
        |g z| = Real.exp (z a) * |Real.sin (z b)| := by
          simp [g, abs_mul, abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (z a) * 1 := mul_le_mul_of_nonneg_left
          (Real.abs_sin_le_one _) (Real.exp_pos _).le
        _ ≤ Real.exp r := by simpa using he
  have hE : MeasurableSet E := (hU.prod hV).measurableSet.preimage
    (PDE.vecAppendEquiv d 2).continuous.measurable
  have hfTop : PDE.MemLpOn E ∞ f :=
    memLp_top_of_bound hf.continuous.aestronglyMeasurable (Real.exp r)
      ((ae_restrict_mem hE).mono fun z hz => by simpa using (hbound z hz).1)
  have hgTop : PDE.MemLpOn E ∞ g :=
    memLp_top_of_bound hg.continuous.aestronglyMeasurable (Real.exp r)
      ((ae_restrict_mem hE).mono fun z hz => by simpa using (hbound z hz).2)
  have hDfTop (j : Fin (d + 2)) :
      PDE.MemLpOn E ∞ (fun z => PDE.classicalGradient f z j) := by
    simp_rw [hDf]
    exact (hfTop.mul_const (PDE.basisVec j a)).sub
      (hgTop.mul_const (PDE.basisVec j b))
  have hDgTop (j : Fin (d + 2)) :
      PDE.MemLpOn E ∞ (fun z => PDE.classicalGradient g z j) := by
    simp_rw [hDg]
    exact (hgTop.mul_const (PDE.basisVec j a)).add
      (hfTop.mul_const (PDE.basisVec j b))
  let uf := (u.liftAppend hU hV hVfinite).mulContDiffMemLpTop hf hfTop hDfTop
  let vg := (v.liftAppend hU hV hVfinite).mulContDiffMemLpTop hg hgTop hDgTop
  let w := uf - vg
  have hw (z : PDE.Vec (d + 2)) :
      w z = f z * u (PDE.vecAppendEquiv d 2 z).1 -
        g z * v (PDE.vecAppendEquiv d 2 z).1 := by
    simp [w, uf, vg]
  have hDw (z : PDE.Vec (d + 2)) (j : Fin (d + 2)) :
      w.grad z j =
        f z * PDE.H1Function.appendLiftGradient u.grad z j +
          u (PDE.vecAppendEquiv d 2 z).1 * PDE.classicalGradient f z j -
        (g z * PDE.H1Function.appendLiftGradient v.grad z j +
          v (PDE.vecAppendEquiv d 2 z).1 * PDE.classicalGradient g z j) := by
    simp [w, uf, vg, PDE.H1Function.appendLiftGradient]
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro z
    rw [hw]
    simp [f, g, a, b, Complex.mul_re, Complex.exp_re, Complex.exp_im]
  · intro z j
    have h0 : Fin.natAdd d (0 : Fin 2) ≠ Fin.castAdd 2 j := by
      intro h
      have hv := congrArg Fin.val h
      change d + 0 = j.val at hv
      omega
    have h1 : Fin.natAdd d (1 : Fin 2) ≠ Fin.castAdd 2 j := by
      intro h
      have hv := congrArg Fin.val h
      change d + 1 = j.val at hv
      omega
    rw [hDw, hDf, hDg]
    simp [PDE.H1Function.appendLiftGradient, PDE.basisVec_apply, a, b,
      f, g, Complex.mul_re, Complex.exp_re, Complex.exp_im,
      h0, h1]
  · intro z
    rw [hDw, hDf, hDg, hw]
    simp [PDE.H1Function.appendLiftGradient, PDE.basisVec_apply, a, b]
    ring
  · intro z
    rw [hDw, hDf, hDg]
    simp [PDE.H1Function.appendLiftGradient, PDE.basisVec_apply, a, b,
      f, g, Complex.mul_im, Complex.exp_re, Complex.exp_im]
    ring

/-- Splitting off the two lift coordinates commutes with retaining the time
coordinate, including all restricted product measures. -/
private theorem short_time_lift_spacetime_measurePreserving {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) :
    MeasurePreserving
      (fun z : PDE.Vec (d + 2) × ℝ =>
        (((PDE.vecAppendEquiv d 2 z.1).1, z.2),
          (PDE.vecAppendEquiv d 2 z.1).2))
      (volume.restrict ((PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I))
      ((volume.restrict (U ×ˢ I)).prod (volume.restrict V)) := by
  let μ := (volume : Measure (PDE.Vec d)).restrict U
  let ν := (volume : Measure (PDE.Vec 2)).restrict V
  let τ := (volume : Measure ℝ).restrict I
  have hs := (PDE.measurePreserving_vecAppendEquiv_restrict d 2 hU hV).prod
    (MeasurePreserving.id τ)
  have ha := measurePreserving_prodAssoc μ ν τ
  have hb := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := τ))
  have hc := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ τ ν)
  have h := hc.comp (hb.comp (ha.comp hs))
  simpa [μ, ν, τ, Measure.volume_eq_prod, ← Measure.prod_restrict,
    Function.comp_def, MeasurableEquiv.prodAssoc] using h

/-- The actual exponential complex lift has joint space-time `Lᵖ`
regularity on every finite-volume auxiliary cylinder. Applying this to each
spatial derivative also supplies the joint gradient integrability needed by
`ParH1Function`; real and imaginary parts require no additional assumptions. -/
theorem short_time_complex_lift_spacetime_memLp {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hI : MeasurableSet I)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    {p : ℝ≥0∞} {u : PDE.Vec d × ℝ → ℂ}
    (hu : MemLp u p (volume.restrict (U ×ˢ I))) :
    MemLp (fun z : PDE.Vec (d + 2) × ℝ => Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)) p
      (volume.restrict ((PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I)) := by
  let E := (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I
  let φ : PDE.Vec (d + 2) × ℝ → ℂ := fun z => Complex.exp
    ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hVfinite⟩
  have huLift : MemLp
      (fun z : PDE.Vec (d + 2) × ℝ => u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)) p
      (volume.restrict E) := by
    exact (hu.comp_fst (volume.restrict V)).comp_measurePreserving
      (short_time_lift_spacetime_measurePreserving hU hV)
  have hE : MeasurableSet E :=
    (hU.prod hV).preimage (PDE.vecAppendEquiv d 2).continuous.measurable |>.prod hI
  have hφ : Continuous φ := by
    dsimp [φ]
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  have hφTop : MemLp φ ∞ (volume.restrict E) := by
    refine memLp_top_of_bound hφ.aestronglyMeasurable (Real.exp r) ?_
    filter_upwards [ae_restrict_mem hE] with z hz
    dsimp only [φ]
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hr (PDE.vecAppendEquiv d 2 z.1).2 hz.1.2)
  exact hφTop.mul huLift

private theorem short_time_complex_lift_sq_bound {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hVfinite : volume V < ⊤)
    (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r) {u : PDE.Vec d → ℂ}
    (hu : MemLp u 2 (volume.restrict U)) :
    MemLp (fun z : PDE.Vec (d + 2) => (Complex.exp
      ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        u (PDE.vecAppendEquiv d 2 z).1).re) 2
      (volume.restrict (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V))) ∧
    (∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V), (Complex.exp
      ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        u (PDE.vecAppendEquiv d 2 z).1).re ^ 2) ≤
      (Real.exp r) ^ 2 * (volume V).toReal * ∫ x in U, ‖u x‖ ^ 2 := by
  let E := PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)
  let φ : PDE.Vec (d + 2) → ℂ := fun z => Complex.exp
    ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩
  let : IsFiniteMeasure (volume.restrict V) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hVfinite⟩
  have he := PDE.measurePreserving_vecAppendEquiv_restrict d 2 hU hV
  have huLift : MemLp (fun z : PDE.Vec (d + 2) =>
      u (PDE.vecAppendEquiv d 2 z).1) 2 (volume.restrict E) :=
    (hu.comp_fst (volume.restrict V)).comp_measurePreserving he
  have hE : MeasurableSet E :=
    (hU.prod hV).preimage (PDE.vecAppendEquiv d 2).continuous.measurable
  have hφ : Continuous φ := by
    dsimp [φ]
    simp_rw [Complex.mk_eq_add_mul_I]
    fun_prop
  have hφTop : MemLp φ ∞ (volume.restrict E) := by
    refine memLp_top_of_bound hφ.aestronglyMeasurable (Real.exp r) ?_
    filter_upwards [ae_restrict_mem hE] with z hz
    dsimp only [φ]
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (hr (PDE.vecAppendEquiv d 2 z).2 hz.2)
  have hw : MemLp (fun z => (φ z * u (PDE.vecAppendEquiv d 2 z).1).re) 2
      (volume.restrict E) := (hφTop.mul huLift).re
  refine ⟨hw, ?_⟩
  have hbound : ∀ᵐ z ∂volume.restrict E,
      (φ z * u (PDE.vecAppendEquiv d 2 z).1).re ^ 2 ≤
        (Real.exp r) ^ 2 * ‖u (PDE.vecAppendEquiv d 2 z).1‖ ^ 2 := by
    filter_upwards [ae_restrict_mem hE] with z hz
    have hn : ‖(φ z * u (PDE.vecAppendEquiv d 2 z).1).re‖ ≤
        Real.exp r * ‖u (PDE.vecAppendEquiv d 2 z).1‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (by rw [show ‖φ z‖ = Real.exp (z (Fin.natAdd d (0 : Fin 2))) by
                  exact Complex.norm_exp _]
            exact Real.exp_le_exp.mpr (hr (PDE.vecAppendEquiv d 2 z).2 hz.2))
        (norm_nonneg _)
    have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
    simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using hs
  have hi := integral_mono_ae hw.integrable_sq
    (huLift.norm.integrable_sq.const_mul ((Real.exp r) ^ 2)) hbound
  have heq : (∫ z in E, ‖u (PDE.vecAppendEquiv d 2 z).1‖ ^ 2) =
      (volume V).toReal * ∫ x in U, ‖u x‖ ^ 2 := by
    rw [he.integral_comp
      (PDE.vecAppendEquiv d 2).toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (fun q => ‖u q.1‖ ^ 2)]
    simpa only [mul_one, one_mul, integral_const, Measure.real,
      Measure.restrict_apply_univ, smul_eq_mul, mul_comm] using
      (integral_prod_mul (μ := volume.restrict U) (ν := volume.restrict V)
        (fun x => ‖u x‖ ^ 2) (fun _ => (1 : ℝ)))
  simpa only [integral_const_mul, heq, mul_assoc] using hi

/-- Local strong `L²` traces pass to the real exponential lift on every compact
subset of the lifted cylinder. This uses the original compact-region squared
integral trace, including its every-time representatives. -/
theorem short_time_complex_lift_local_strong_trace {d : ℕ} {α : Type*}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} (hV : MeasurableSet V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u : α → PDE.Vec d → ℂ) (u₀ : PDE.Vec d → ℂ) (l : Filter α)
    (hu : ∀ a K, IsCompact K → K ⊆ U → MemLp (u a) 2 (volume.restrict K))
    (hu₀ : ∀ K, IsCompact K → K ⊆ U → MemLp u₀ 2 (volume.restrict K))
    (htrace : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun a => ∫ x in K, ‖u a x - u₀ x‖ ^ 2) l (𝓝 0)) :
    ∀ K : Set (PDE.Vec (d + 2)), IsCompact K →
      K ⊆ PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V) →
      (∀ a, MemLp (fun z => (Complex.exp
        ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          u a (PDE.vecAppendEquiv d 2 z).1).re) 2 (volume.restrict K)) ∧
      MemLp (fun z => (Complex.exp
        ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          u₀ (PDE.vecAppendEquiv d 2 z).1).re) 2 (volume.restrict K) ∧
      Tendsto (fun a => ∫ z in K,
        ((Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
            u a (PDE.vecAppendEquiv d 2 z).1).re -
          (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
            u₀ (PDE.vecAppendEquiv d 2 z).1).re) ^ 2) l (𝓝 0) := by
  intro K hK hKE
  let L := (fun z : PDE.Vec (d + 2) => (PDE.vecAppendEquiv d 2 z).1) '' K
  have hL : IsCompact L := hK.image ((PDE.vecAppendEquiv d 2).continuous.fst)
  have hLU : L ⊆ U := by
    rintro x ⟨z, hz, rfl⟩
    exact (hKE hz).1
  have hKL : K ⊆ PDE.vecAppendEquiv d 2 ⁻¹' (L ×ˢ V) := by
    intro z hz
    exact ⟨⟨z, hz, rfl⟩, (hKE hz).2⟩
  have hμ := Measure.restrict_mono_set volume hKL
  refine ⟨fun a => ((short_time_complex_lift_sq_bound hL.measurableSet hV
    hVfinite r hr (hu a L hL hLU)).1).mono_measure hμ,
    ((short_time_complex_lift_sq_bound hL.measurableSet hV
      hVfinite r hr (hu₀ L hL hLU)).1).mono_measure hμ, ?_⟩
  have hb (a : α) := short_time_complex_lift_sq_bound hL.measurableSet hV
    hVfinite r hr ((hu a L hL hLU).sub (hu₀ L hL hLU))
  have hlim := (htrace L hL hLU).const_mul ((Real.exp r) ^ 2 * (volume V).toReal)
  simp only [mul_zero] at hlim
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hlim
  intro a
  have hm := integral_mono_measure hμ
    (Eventually.of_forall fun z => sq_nonneg
      ((Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        (u a (PDE.vecAppendEquiv d 2 z).1 - u₀ (PDE.vecAppendEquiv d 2 z).1)).re))
    (hb a).1.integrable_sq
  simpa only [Pi.sub_apply, mul_sub, Complex.sub_re] using hm.trans (hb a).2

private theorem short_time_tendsto_L2_pairing {α β : Type*} [MeasurableSpace β]
    {μ : Measure β} {l : Filter α} {u : α → β → ℝ} {u₀ ψ : β → ℝ}
    (hu : ∀ a, MemLp (u a) 2 μ) (hu₀ : MemLp u₀ 2 μ) (hψ : MemLp ψ 2 μ)
    (htrace : Tendsto (fun a => ∫ x, (u a x - u₀ x) ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun a => ∫ x, u a x * ψ x ∂μ) l (𝓝 (∫ x, u₀ x * ψ x ∂μ)) := by
  have hd (a : α) : MemLp (fun x => u a x - u₀ x) 2 μ := (hu a).sub hu₀
  have hnorm := PDE.tendsto_eLpNorm_two_zero_of_tendsto_integral_sq hd htrace
  have hlim := ENNReal.Tendsto.mul_const hnorm (Or.inr hψ.eLpNorm_ne_top)
  simp only [zero_mul] at hlim
  refine tendsto_integral_of_L1' (fun x => u₀ x * ψ x)
    (Eventually.of_forall fun a => (hu a).integrable_mul hψ) ?_
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le) (fun a => ?_)
  have heq : (fun x => u a x * ψ x) - (fun x => u₀ x * ψ x) =
      (fun x => u a x - u₀ x) • ψ := by
    funext x
    exact (sub_mul _ _ _).symm
  rw [heq]
  exact eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
    (hd a).aestronglyMeasurable hψ.aestronglyMeasurable

/-- Every compactly supported `L²` test detects the correct trace of the real
exponential lift, along any filter for which the original local strong trace
holds. No pointwise convergence of the chosen representatives is needed. -/
theorem short_time_complex_lift_weak_trace {d : ℕ} {α : Type*}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u : α → PDE.Vec d → ℂ) (u₀ : PDE.Vec d → ℂ) (l : Filter α)
    (hu : ∀ a K, IsCompact K → K ⊆ U → MemLp (u a) 2 (volume.restrict K))
    (hu₀ : ∀ K, IsCompact K → K ⊆ U → MemLp u₀ 2 (volume.restrict K))
    (htrace : ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun a => ∫ x in K, ‖u a x - u₀ x‖ ^ 2) l (𝓝 0))
    (ψ : PDE.Vec (d + 2) → ℝ)
    (hψ : PDE.IsL2c (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ψ) :
    Tendsto (fun a => ∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V),
      (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        u a (PDE.vecAppendEquiv d 2 z).1).re * ψ z) l
      (𝓝 (∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V),
        (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          u₀ (PDE.vecAppendEquiv d 2 z).1).re * ψ z)) := by
  let E := PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)
  let w (f : PDE.Vec d → ℂ) (z : PDE.Vec (d + 2)) := (Complex.exp
    ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
      f (PDE.vecAppendEquiv d 2 z).1).re
  obtain ⟨hψ2, K, hK, hKE, hψ0⟩ := hψ
  have hw := short_time_complex_lift_local_strong_trace hV hVfinite r hr u u₀ l
    hu hu₀ htrace K hK hKE
  have hψK := hψ2.mono_measure (Measure.restrict_mono_set volume hKE)
  have hpair := short_time_tendsto_L2_pairing hw.1 hw.2.1 hψK hw.2.2
  have hE : MeasurableSet E :=
    (hU.prod hV).preimage (PDE.vecAppendEquiv d 2).continuous.measurable
  have hloc (f : PDE.Vec (d + 2) → ℝ) :
      (∫ z in E, f z * ψ z) = ∫ z in K, f z * ψ z :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hE hKE
      (fun z hz => by rw [hψ0 z hz.2, mul_zero])
  change Tendsto (fun a => ∫ z in E, w (u a) z * ψ z) l
    (𝓝 (∫ z in E, w u₀ z * ψ z))
  simpa only [← hloc] using hpair

/-- Local strong continuity of the original complex representatives supplies
the full weak-continuity field of the real lifted parabolic energy class.
The parameter space may be a time interval with its subtype topology. -/
theorem short_time_complex_lift_weak_continuous {d : ℕ} {α : Type*}
    [TopologicalSpace α] {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u : α → PDE.Vec d → ℂ)
    (hu : ∀ a K, IsCompact K → K ⊆ U → MemLp (u a) 2 (volume.restrict K))
    (hcont : ∀ a K, IsCompact K → K ⊆ U →
      Tendsto (fun b => ∫ x in K, ‖u b x - u a x‖ ^ 2) (𝓝 a) (𝓝 0))
    (ψ : PDE.Vec (d + 2) → ℝ)
    (hψ : PDE.IsL2c (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ψ) :
    Continuous (fun a => ∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V),
      (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        u a (PDE.vecAppendEquiv d 2 z).1).re * ψ z) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact short_time_complex_lift_weak_trace hU hV hVfinite r hr u (u a) (𝓝 a)
    hu (hu a) (hcont a) ψ hψ

/-- The weak continuity conclusion on the original time set, including its
one-sided endpoints. This is the literal continuity shape in `ParH1Function`. -/
theorem short_time_complex_lift_weak_continuousOn {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u : ℝ → PDE.Vec d → ℂ)
    (hu : ∀ a ∈ I, ∀ K, IsCompact K → K ⊆ U → MemLp (u a) 2 (volume.restrict K))
    (hcont : ∀ a ∈ I, ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun b => ∫ x in K, ‖u b x - u a x‖ ^ 2) (𝓝[I] a) (𝓝 0))
    (ψ : PDE.Vec (d + 2) → ℝ)
    (hψ : PDE.IsL2c (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ψ) :
    ContinuousOn (fun a => ∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V),
      (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
        u a (PDE.vecAppendEquiv d 2 z).1).re * ψ z) I := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  apply short_time_complex_lift_weak_continuous hU hV hVfinite r hr
    (fun a : I => u a) (fun a => hu a a.property) ?_ ψ hψ
  intro a K hK hKU
  have hcoe : Tendsto (fun b : I => (b : ℝ)) (𝓝 a) (𝓝[I] (a : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨continuous_subtype_val.continuousAt,
      Eventually.of_forall fun b => b.property⟩
  exact (hcont a a.property K hK hKU).comp hcoe

private theorem short_time_unit_primitive_sq_bound {u : ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (Icc (0 : ℝ) 1)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖∫ s in Icc (0 : ℝ) t, u s‖ ^ 2 ≤ ∫ s in Icc (0 : ℝ) 1, ‖u s‖ ^ 2 := by
  have hc : MemLp (fun _ : ℝ => (1 : ℂ)) 2
      (volume.restrict (Icc (0 : ℝ) 1)) := memLp_const _
  have hh := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hc) (by simpa using hu)
  simp only [norm_one, one_mul, Real.rpow_two, integral_const, smul_eq_mul,
    one_pow, Measure.real, Measure.restrict_apply_univ, Real.volume_Icc,
    sub_zero, ENNReal.toReal_ofReal zero_le_one, one_mul, ← Real.sqrt_eq_rpow,
    Real.sqrt_one] at hh
  have hn : ‖∫ s in Icc (0 : ℝ) t, u s‖ ≤
      ∫ s in Icc (0 : ℝ) 1, ‖u s‖ :=
    (norm_integral_le_integral_norm _).trans (setIntegral_mono_set (hu.integrable (by norm_num)).norm
      (ae_of_all _ fun _ => norm_nonneg _) (ae_of_all _ fun _ hx =>
        Icc_subset_Icc le_rfl ht.2 hx))
  have hI : 0 ≤ ∫ s in Icc (0 : ℝ) 1, ‖u s‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  exact ((sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr (hn.trans hh)).trans_eq
    (Real.sq_sqrt hI)

/-- The literal primitive of a jointly square-integrable derivative is strongly
continuous in spatial `L²`, including both one-sided time endpoints. -/
theorem short_time_local_primitive_continuous {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] {U : ℝ × X → ℂ} (hU : Measurable U)
    (hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ)) :
    (∀ t ∈ Icc (0 : ℝ) 1,
      MemLp (fun x => ∫ s in Icc (0 : ℝ) t, U (s, x)) 2 μ) ∧
    ∀ a ∈ Icc (0 : ℝ) 1,
      Tendsto (fun t => ∫ x, ‖(∫ s in Icc (0 : ℝ) t, U (s, x)) -
        (∫ s in Icc (0 : ℝ) a, U (s, x))‖ ^ 2 ∂μ)
        (𝓝[Icc (0 : ℝ) 1] a) (𝓝 0) := by
  let F (t : ℝ) (x : X) := ∫ s in Icc (0 : ℝ) t, U (s, x)
  let B (x : X) := ∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2
  have hF (t : ℝ) : Measurable (F t) :=
    (hU.stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Icc (0 : ℝ) t))).measurable
  have hmem : ∀ᵐ x ∂μ,
      MemLp (fun s => U (s, x)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hI.prod_left_ae] with x hx
    exact (memLp_two_iff_integrable_sq_norm
      (hU.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
  have hb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∀ᵐ x ∂μ, ‖F t x‖ ^ 2 ≤ B x := by
    filter_upwards [hmem] with x hx
    exact short_time_unit_primitive_sq_bound hx ht
  have hB : Integrable B μ := hI.integral_prod_right
  have hFm (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : MemLp (F t) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (hF t).aestronglyMeasurable).mpr
    apply hB.mono' ((hF t).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb t ht] with x hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx
  refine ⟨hFm, ?_⟩
  intro a ha
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[Icc (0 : ℝ) 1] a)
    (F := fun t x => ‖F t x - F a x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => 4 * B x)
    (Eventually.of_forall fun t => ((hF t).sub (hF a)).norm.pow_const 2
      |>.aestronglyMeasurable) ?_ (hB.const_mul 4) ?_
  · simpa only [integral_zero] using hlim
  · filter_upwards [eventually_mem_nhdsWithin] with t ht
    filter_upwards [hb t ht, hb a ha] with x ht' ha'
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_sub_le (F t x) (F a x))
    have hs : (‖F t x‖ + ‖F a x‖) ^ 2 ≤ 2 * (‖F t x‖ ^ 2 + ‖F a x‖ ^ 2) :=
      add_sq_le
    nlinarith
  · filter_upwards [hmem] with x hx
    have hc := intervalIntegral.continuousOn_primitive_Icc (hx.integrable (by norm_num)) a ha
    have hd := (hc.sub_const (F a x)).norm.pow 2
    simpa only [F, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hd

/-- A single primitive representative of the actual stationary generator orbit
is strongly continuous locally in space on the whole short-time interval.
The sample event precedes every compact set and every time, so it can be used
in the every-time fields of the real lifted parabolic energy class. -/
theorem short_time_stationary_primitive_local_strong_continuous
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ K : Set (Vec d), IsCompact K →
        (∀ t ∈ Icc (0 : ℝ) 1, MemLp (fun x => F (t, translate x ω)) 2
          (volume.restrict K)) ∧
        ∀ a ∈ Icc (0 : ℝ) 1,
          Tendsto (fun t => ∫ x in K,
            ‖F (t, translate x ω) - F (a, translate x ω)‖ ^ 2)
            (𝓝[Icc (0 : ℝ) 1] a) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨F, U, hF, hU, heF, heU, hprim⟩ := short_time_stationary_joint_primitive hP hfg
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  have hfI : Integrable (fun p : ℝ × FieldPair d => ‖f p.2‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative (integrable_const _)
      ((Lp.stronglyMeasurable f).measurable.comp measurable_snd) (fun _ => EventuallyEq.rfl)
  refine ⟨F, U, hF, hU, heF, heU, hprim, ?_⟩
  filter_upwards [ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
    (reducedLaw_stationary Q) hI.ofReal,
    ae_locally_integrable_joint_spatial_translate (reducedLaw Q)
      (reducedLaw_stationary Q) hfI.ofReal] with ω hω hfω
  intro K hK
  have hi : Integrable (fun p : ℝ × Vec d => ‖U (p.1, translate p.2 ω)‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict K)) :=
    (Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hω K hK).swap
  have hfi : Integrable (fun x => ‖f (translate x ω)‖ ^ 2) (volume.restrict K) := by
    have hf' := ((Integrable.iff_ofReal (𝕜 := ℂ)).mpr (hfω K hK)).integral_prod_left
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_mul] using hf'
  have hm : Measurable (fun p : ℝ × Vec d => U (p.1, translate p.2 ω)) :=
    hU.comp (measurable_fst.prodMk (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_const)))
  have hfm : MemLp (fun x => f (translate x ω)) 2 (volume.restrict K) :=
    (memLp_two_iff_integrable_sq_norm ((Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp
        (measurable_id.prodMk measurable_const))).aestronglyMeasurable).mpr hfi
  obtain ⟨hmem, hcont⟩ := short_time_local_primitive_continuous (volume.restrict K) hm hi
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (hfm.add (hmem t ht)).ae_eq (ae_of_all _ fun x => (hprim t (translate x ω)).symm)
  · intro a ha
    convert hcont a ha using 1
    funext t
    apply integral_congr_ae
    filter_upwards with x
    rw [hprim, hprim, add_sub_add_left_eq_sub]

private theorem short_time_physical_local_strong_continuous
    {d : ℕ} {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hPr : IsPhysicalComplexSemigroup a i ζ Pr)
    (fr : Lp ℂ 2 (volume : Measure (Vec d)))
    {V : ℝ × Vec d → ℂ}
    (heV : ∀ t, (fun x => V (t, x)) =ᵐ[volume] Pr t.toNNReal fr)
    (K : Set (Vec d)) :
    (∀ t : ℝ, MemLp (fun x => V (t, x)) 2 (volume.restrict K)) ∧
    ∀ b : ℝ, Tendsto (fun t => ∫ x in K, ‖V (t, x) - V (b, x)‖ ^ 2)
      (𝓝 b) (𝓝 0) := by
  have hm (t : ℝ) : MemLp (fun x => V (t, x)) 2 volume :=
    (Lp.memLp (Pr t.toNNReal fr)).ae_eq (heV t).symm
  refine ⟨fun t => (hm t).mono_measure Measure.restrict_le_self, ?_⟩
  intro b
  have hi (t : ℝ) : Integrable (fun x => ‖V (t, x) - V (b, x)‖ ^ 2) volume :=
    ((hm t).sub (hm b)).norm.integrable_sq
  have he (t : ℝ) : (∫ x, ‖V (t, x) - V (b, x)‖ ^ 2) =
      ‖Pr t.toNNReal fr - Pr b.toNNReal fr‖ ^ 2 := by
    have hn : ‖Pr t.toNNReal fr - Pr b.toNNReal fr‖ ^ 2 =
        ∫ x, ‖(Pr t.toNNReal fr - Pr b.toNNReal fr) x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    rw [hn]
    apply integral_congr_ae
    filter_upwards [heV t, heV b,
      Lp.coeFn_sub (Pr t.toNNReal fr) (Pr b.toNNReal fr)] with x ht hb hsub
    rw [hsub]
    rw [ht, hb]
    rfl
  have hlim : Tendsto (fun t : ℝ => ‖Pr t.toNNReal fr - Pr b.toNNReal fr‖ ^ 2)
      (𝓝 b) (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (((((hPr.2.2.1 fr).comp continuous_real_toNNReal).tendsto b).sub_const
        (Pr b.toNNReal fr)).norm.pow 2)
  apply squeeze_zero (fun _ => integral_nonneg fun _ => sq_nonneg _) ?_ hlim
  intro t
  exact (setIntegral_le_integral (s := K) (hi t)
    (ae_of_all _ fun _ => sq_nonneg _)).trans_eq (he t)

/-- The actual stationary-minus-retained orbit is weakly continuous on `[0,1]`
after real exponential lifting. Every physical representative agreeing
with its semigroup at each time is allowed, so the same representative used
by the retained weak equation can be consumed without a new choice. -/
theorem short_time_stationary_retained_lift_weak_continuous
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ F U : ℝ × FieldPair d → ℂ, Measurable F ∧ Measurable U ∧
      (∀ s, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal f) ∧
      (∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g) ∧
      (∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) ∧
      ∀ᵐ ω ∂reducedLaw Q,
      ∀ (a : Vec d → Mat d)
        (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup a i ζ Pr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ t, (fun x => V (t, x)) =ᵐ[volume] Pr t.toNNReal fr) →
      ∀ (S : Set (PDE.Vec d)) (W : Set (PDE.Vec 2)),
      MeasurableSet S → MeasurableSet W → volume W < ⊤ →
      ∀ r₁ : ℝ, (∀ y ∈ W, y 0 ≤ r₁) →
      ∀ ψ : PDE.Vec (d + 2) → ℝ,
      PDE.IsL2c (PDE.vecAppendEquiv d 2 ⁻¹' (S ×ˢ W)) ψ →
      ContinuousOn (fun t => ∫ z in PDE.vecAppendEquiv d 2 ⁻¹' (S ×ˢ W),
        (Complex.exp ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩ *
          (F (t, translate (PDE.vecAppendEquiv d 2 z).1 ω) -
            V (t, (PDE.vecAppendEquiv d 2 z).1))).re * ψ z) (Icc (0 : ℝ) 1) := by
  obtain ⟨F, U, hF, hU, heF, heU, hprim, htrace⟩ :=
    short_time_stationary_primitive_local_strong_continuous Q hP hfg
  refine ⟨F, U, hF, hU, heF, heU, hprim, ?_⟩
  filter_upwards [htrace] with ω hω
  intro a Pr hPr fr V heV S W hS hW hWfinite r₁ hr₁ ψ hψ
  let u (t : ℝ) (x : Vec d) := F (t, translate x ω) - V (t, x)
  have hu (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (K : Set (Vec d)) (hK : IsCompact K) :
      MemLp (u t) 2 (volume.restrict K) :=
    ((hω K hK).1 t ht).sub
      ((short_time_physical_local_strong_continuous hPr fr heV K).1 t)
  apply short_time_complex_lift_weak_continuousOn hS hW hWfinite r₁ hr₁ u
    (fun t ht K hK _ => hu t ht K hK) ?_ ψ hψ
  intro b hb K hK _
  obtain ⟨hVmem, hVcont⟩ := short_time_physical_local_strong_continuous hPr fr heV K
  have hupper (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x in K, ‖u t x - u b x‖ ^ 2) ≤
        2 * (∫ x in K, ‖F (t, translate x ω) - F (b, translate x ω)‖ ^ 2) +
        2 * (∫ x in K, ‖V (t, x) - V (b, x)‖ ^ 2) := by
    have hFi : Integrable (fun x => ‖F (t, translate x ω) - F (b, translate x ω)‖ ^ 2)
        (volume.restrict K) := by
      simpa only [Pi.sub_apply] using
        (((hω K hK).1 t ht).sub ((hω K hK).1 b hb)).norm.integrable_sq
    have hVi : Integrable (fun x => ‖V (t, x) - V (b, x)‖ ^ 2) (volume.restrict K) := by
      simpa only [Pi.sub_apply] using ((hVmem t).sub (hVmem b)).norm.integrable_sq
    have hi : Integrable (fun x => ‖u t x - u b x‖ ^ 2) (volume.restrict K) := by
      simpa only [Pi.sub_apply] using
        ((hu t ht K hK).sub (hu b hb K hK)).norm.integrable_sq
    calc
      _ ≤ ∫ x in K,
          2 * ‖F (t, translate x ω) - F (b, translate x ω)‖ ^ 2 +
          2 * ‖V (t, x) - V (b, x)‖ ^ 2 := by
        apply integral_mono_ae hi ((hFi.const_mul 2).add (hVi.const_mul 2))
        filter_upwards with x
        simp only [Pi.add_apply]
        have he : u t x - u b x =
            (F (t, translate x ω) - F (b, translate x ω)) - (V (t, x) - V (b, x)) := by
          dsimp only [u]
          ring
        rw [he]
        have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
          (norm_sub_le (F (t, translate x ω) - F (b, translate x ω)) (V (t, x) - V (b, x)))
        calc
          _ ≤ (‖F (t, translate x ω) - F (b, translate x ω)‖ +
              ‖V (t, x) - V (b, x)‖) ^ 2 := hn
          _ ≤ 2 * (‖F (t, translate x ω) - F (b, translate x ω)‖ ^ 2 +
              ‖V (t, x) - V (b, x)‖ ^ 2) := add_sq_le
          _ = _ := by ring
      _ = (∫ x in K, 2 * ‖F (t, translate x ω) - F (b, translate x ω)‖ ^ 2) +
          (∫ x in K, 2 * ‖V (t, x) - V (b, x)‖ ^ 2) := by
        simpa only [Pi.add_apply] using integral_add (hFi.const_mul 2) (hVi.const_mul 2)
      _ = _ := by rw [integral_const_mul, integral_const_mul]
  have hlimF := ((hω K hK).2 b hb).const_mul 2
  have hlimV := ((hVcont b).mono_left
    (show 𝓝[Icc (0 : ℝ) 1] b ≤ 𝓝 b from inf_le_left)).const_mul 2
  have hlim := hlimF.add hlimV
  apply squeeze_zero' (Eventually.of_forall fun _ => integral_nonneg fun _ => sq_nonneg _) ?_
    (by simpa only [mul_zero, add_zero] using hlim)
  filter_upwards [eventually_mem_nhdsWithin] with t ht
  exact hupper t ht


private theorem short_time_spacetime_memLp_slices {d : ℕ}
    {U : Set (PDE.Vec d)} {I : Set ℝ} {u : PDE.Vec d × ℝ → ℂ}
    (hu : MemLp u 2 (volume.restrict (U ×ˢ I))) :
    ∀ᵐ t ∂volume.restrict I, MemLp (fun x => u (x, t)) 2 (volume.restrict U) := by
  have hp : MemLp u 2 ((volume.restrict U).prod (volume.restrict I)) := by
    simpa only [Measure.prod_restrict, ← Measure.volume_eq_prod] using hu
  filter_upwards [hp.aestronglyMeasurable.prodMk_right,
    hp.norm.integrable_sq.prod_left_ae] with t hmt hit
  exact (memLp_two_iff_integrable_sq_norm hmt).mpr hit

/-- The literal real exponential lift belongs to the parabolic energy class.
Its gradient is specified in every physical and auxiliary coordinate, so the
same representative can be used in the lifted weak equation. -/
theorem short_time_complex_lift_ParH1 {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hI : MeasurableSet I)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u : PDE.Vec d × ℝ → ℂ) (D : Fin d → PDE.Vec d × ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (U ×ˢ I)))
    (hD : ∀ j, MemLp (D j) 2 (volume.restrict (U ×ˢ I)))
    (hweak : ∀ᵐ t ∂volume.restrict I,
      PDE.HasWeakGradientOn U (fun x => (u (x, t)).re)
        (fun x j => (D j (x, t)).re) ∧
      PDE.HasWeakGradientOn U (fun x => (u (x, t)).im)
        (fun x j => (D j (x, t)).im))
    (hloc : ∀ t ∈ I, ∀ K, IsCompact K → K ⊆ U →
      MemLp (fun x => u (x, t)) 2 (volume.restrict K))
    (hcont : ∀ t ∈ I, ∀ K, IsCompact K → K ⊆ U →
      Tendsto (fun s => ∫ x in K, ‖u (x, s) - u (x, t)‖ ^ 2)
        (𝓝[I] t) (𝓝 0)) :
    ∃ w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) I,
      (∀ z, w.toFun z = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re) ∧
      (∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re) ∧
      (∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z) ∧
      (∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
        ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
          u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im) := by
  let E := PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)
  let e : PDE.Vec (d + 2) → ℂ := fun z => Complex.exp
    ⟨z (Fin.natAdd d (0 : Fin 2)), z (Fin.natAdd d (1 : Fin 2))⟩
  let f : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
    (e z.1 * u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re
  let G : PDE.Vec (d + 2) × ℝ → PDE.Vec (d + 2) := fun z =>
    Fin.addCases
      (fun j => (e z.1 * D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
      ![f z, -(e z.1 * u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im]
  have hL := short_time_complex_lift_spacetime_memLp hU.measurableSet
    hV.measurableSet hI hVfinite r hr hu
  have hGL (j : Fin (d + 2)) :
      MemLp (fun z => G z j) 2 (volume.restrict (E ×ˢ I)) := by
    refine Fin.addCases ?_ ?_ j
    · intro i
      simpa [G, e] using
        (short_time_complex_lift_spacetime_memLp hU.measurableSet
          hV.measurableSet hI hVfinite r hr (hD i)).re
    · intro i
      fin_cases i
      · simpa [G, f, e] using hL.re
      · convert hL.im.neg using 1
        ext z
        simp [G, e]
  have hsD : ∀ᵐ t ∂volume.restrict I,
      ∀ j, MemLp (fun x => D j (x, t)) 2 (volume.restrict U) := by
    exact ae_all_iff.mpr fun j => short_time_spacetime_memLp_slices (hD j)
  have hsw : ∀ᵐ t ∂volume.restrict I,
      PDE.HasWeakGradientOn E (PDE.parSlice f t) (PDE.parSlice G t) := by
    filter_upwards [short_time_spacetime_memLp_slices hu, hsD, hweak] with t hut hDt hwt
    let a : PDE.H1Function U :=
      ⟨fun x => (u (x, t)).re, fun x j => (D j (x, t)).re,
        hut.re, fun j => (hDt j).re, hwt.1⟩
    let b : PDE.H1Function U :=
      ⟨fun x => (u (x, t)).im, fun x j => (D j (x, t)).im,
        hut.im, fun j => (hDt j).im, hwt.2⟩
    obtain ⟨v, hv, hvD, hva, hvb⟩ :=
      short_time_complex_lift_H1 hU hV hVfinite r hr a b
    have hvf : v.toFun = PDE.parSlice f t := by
      funext z
      simpa only [PDE.parSlice, f, e, a, b, Complex.eta] using hv z
    have hvG : v.grad = PDE.parSlice G t := by
      funext z j
      refine Fin.addCases ?_ ?_ j
      · intro i
        simpa only [PDE.parSlice, G, e, a, b, Fin.addCases_left, Complex.eta] using hvD z i
      · intro i
        fin_cases i
        · simpa [PDE.parSlice, G, f, e, hv z, a, b] using hva z
        · simpa [PDE.parSlice, G, e, a, b] using hvb z
    rw [← hvf, ← hvG]
    exact v.hasWeakGradient
  have hfloc : ∀ t ∈ I, ∀ K : Set (PDE.Vec (d + 2)), IsCompact K → K ⊆ E →
      MemLp (PDE.parSlice f t) 2 (volume.restrict K) := by
    intro t ht K hK hKE
    let L := (fun z : PDE.Vec (d + 2) => (PDE.vecAppendEquiv d 2 z).1) '' K
    have hL : IsCompact L := hK.image (PDE.vecAppendEquiv d 2).continuous.fst
    have hLU : L ⊆ U := by
      rintro x ⟨z, hz, rfl⟩
      exact (hKE hz).1
    have hKL : K ⊆ PDE.vecAppendEquiv d 2 ⁻¹' (L ×ˢ V) := by
      intro z hz
      exact ⟨⟨z, hz, rfl⟩, (hKE hz).2⟩
    exact ((short_time_complex_lift_sq_bound hL.measurableSet hV.measurableSet
      hVfinite r hr (hloc t ht L hL hLU)).1).mono_measure
        (Measure.restrict_mono_set volume hKL)
  let w : PDE.ParH1Function E I :=
    { toFun := f
      grad := G
      memL2 := hL.re
      gradMemL2 := hGL
      sliceWeakGradient := hsw
      sliceL2loc := hfloc
      weakCont := fun ψ hψ => short_time_complex_lift_weak_continuousOn
        hU.measurableSet hV.measurableSet hVfinite r hr
        (fun t x => u (x, t)) hloc hcont ψ hψ }
  refine ⟨w, fun _ => rfl, ?_, ?_, ?_⟩
  · intro z j
    simp only [w, G, e, Fin.addCases_left]
  · intro z
    simp [w, G]
  · intro z
    simp [w, G, e]


/-- The literal `Icc 0 t` primitive is zero for nonpositive times and remains
strongly continuous in spatial `L²` across time zero. No new choice of its
representative is made. -/
theorem short_time_local_primitive_zero_extended_continuous {X : Type*}
    [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    {U : ℝ × X → ℂ} (hU : Measurable U)
    (hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod μ)) :
    (∀ t ∈ Icc (-1 : ℝ) 1,
      MemLp (fun x => ∫ s in Icc (0 : ℝ) t, U (s, x)) 2 μ) ∧
    ∀ a ∈ Icc (-1 : ℝ) 1,
      Tendsto (fun t => ∫ x, ‖(∫ s in Icc (0 : ℝ) t, U (s, x)) -
        (∫ s in Icc (0 : ℝ) a, U (s, x))‖ ^ 2 ∂μ)
        (𝓝[Icc (-1 : ℝ) 1] a) (𝓝 0) := by
  let F (t : ℝ) (x : X) := ∫ s in Icc (0 : ℝ) t, U (s, x)
  let B (x : X) := ∫ s in Icc (0 : ℝ) 1, ‖U (s, x)‖ ^ 2
  have hFzero (t : ℝ) (ht : t ≤ 0) : F t = 0 := by
    funext x
    simp [F, integral_Icc_eq_integral_Ioc, Ioc_eq_empty (not_lt_of_ge ht)]
  have hF (t : ℝ) : Measurable (F t) :=
    (hU.stronglyMeasurable.integral_prod_left'
      (μ := volume.restrict (Icc (0 : ℝ) t))).measurable
  have hmem : ∀ᵐ x ∂μ,
      MemLp (fun s => U (s, x)) 2 (volume.restrict (Icc (0 : ℝ) 1)) := by
    filter_upwards [hI.prod_left_ae] with x hx
    exact (memLp_two_iff_integrable_sq_norm
      (hU.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable).mpr hx
  have hb (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ∀ᵐ x ∂μ, ‖F t x‖ ^ 2 ≤ B x := by
    by_cases ht0 : 0 ≤ t
    · filter_upwards [hmem] with x hx
      exact short_time_unit_primitive_sq_bound hx ⟨ht0, ht.2⟩
    · rw [hFzero t (le_of_not_ge ht0)]
      exact Eventually.of_forall fun x => by
        simpa only [Pi.zero_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          using integral_nonneg (μ := volume.restrict (Icc (0 : ℝ) 1))
            (fun s => sq_nonneg ‖U (s, x)‖)
  have hB : Integrable B μ := hI.integral_prod_right
  have hFm (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : MemLp (F t) 2 μ := by
    apply (memLp_two_iff_integrable_sq_norm (hF t).aestronglyMeasurable).mpr
    apply hB.mono' ((hF t).norm.pow_const 2).aestronglyMeasurable
    filter_upwards [hb t ht] with x hx
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hx
  refine ⟨hFm, ?_⟩
  intro a ha
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := 𝓝[Icc (-1 : ℝ) 1] a)
    (F := fun t x => ‖F t x - F a x‖ ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => 4 * B x)
    (Eventually.of_forall fun t => ((hF t).sub (hF a)).norm.pow_const 2
      |>.aestronglyMeasurable) ?_ (hB.const_mul 4) ?_
  · simpa only [integral_zero] using hlim
  · filter_upwards [eventually_mem_nhdsWithin] with t ht
    filter_upwards [hb t ht, hb a ha] with x ht' ha'
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hn := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr
      (norm_sub_le (F t x) (F a x))
    have hs : (‖F t x‖ + ‖F a x‖) ^ 2 ≤ 2 * (‖F t x‖ ^ 2 + ‖F a x‖ ^ 2) := add_sq_le
    nlinarith
  · filter_upwards [hmem] with x hx
    have hc0 : ContinuousOn (fun t => F t x) (Icc (0 : ℝ) 1) :=
      intervalIntegral.continuousOn_primitive_Icc (hx.integrable (by norm_num))
    have hp : ContinuousOn ((Ici (0 : ℝ)).piecewise (fun t => F t x) (fun _ => 0))
        (Icc (-1 : ℝ) 1) := by
      apply ContinuousOn.piecewise
      · intro t ht
        have ht0 : t = 0 := by simpa only [frontier_Ici, mem_singleton_iff] using ht.2
        subst t
        exact congrFun (hFzero 0 le_rfl) x
      · apply hc0.mono
        intro t ht
        exact ⟨by simpa only [closure_Ici, mem_Ici] using ht.2, ht.1.2⟩
      · exact continuousOn_const
    have hc : ContinuousOn (fun t => F t x) (Icc (-1 : ℝ) 1) := by
      apply hp.congr
      intro t _
      by_cases ht : t ∈ Ici (0 : ℝ)
      · simp only [piecewise_eq_of_mem _ _ _ ht]
      · rw [piecewise_eq_of_notMem _ _ _ ht]
        exact congrFun (hFzero t (le_of_not_ge ht)) x
    have hd := ((hc a ha).sub_const (F a x)).norm.pow 2
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hd


/-- The real lifted coefficient matrix acts on the literal lifted gradient.
The physical block is the complex diffusion flux, and the auxiliary block
retains the signed real and imaginary parts of the force. -/
theorem short_time_complex_lift_flux {d : ℕ} (A : PDE.Mat d) (i : Fin d)
    (ζ e u : ℂ) (M : ℝ) (D : Fin d → ℂ) :
    PDE.matVecMul (shortTimeComplexLiftMatrix A i ζ M)
      (Fin.addCases (fun j => (e * D j).re) ![(e * u).re, -(e * u).im]) =
    Fin.addCases
      (fun j => (e * ((1 / 2 : ℂ) * ∑ k, (A j k : ℂ) * D k)).re)
      ![ζ.re * (e * ∑ k, (A k i : ℂ) * D k).re + M * (e * u).re,
        ζ.im * (e * ∑ k, (A k i : ℂ) * D k).re - M * (e * u).im] := by
  have hsum (C : Fin d → ℝ) :
      (∑ k, C k * (e * D k).re) = (e * ∑ k, (C k : ℂ) * D k).re := by
    rw [Finset.mul_sum, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring
  ext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simp only [PDE.matVecMul, shortTimeComplexLiftMatrix, Fin.addCases_left,
      Fin.sum_univ_add, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero]
    calc
      (∑ k, A j k / 2 * (e * D k).re) =
          (1 / 2 : ℝ) * ∑ k, A j k * (e * D k).re := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (1 / 2 : ℝ) * (e * ∑ k, (A j k : ℂ) * D k).re := by rw [hsum]
      _ = _ := by
        rw [← mul_assoc, mul_comm e (1 / 2 : ℂ), mul_assoc]
        simp
  · fin_cases j <;>
      simp only [PDE.matVecMul, shortTimeComplexLiftMatrix, Fin.addCases_right,
        Fin.sum_univ_add, Fin.addCases_left, Fin.sum_univ_two, Fin.isValue,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero',
        Matrix.cons_val_succ']
    all_goals
      simp_rw [mul_assoc, ← Finset.mul_sum, hsum]
      norm_num [Fin.ext_iff]
      <;> ring

private theorem short_time_C1_integral_mul_partialDeriv
    {n : ℕ} {f φ : PDE.Vec n → ℝ} (hf : ContDiff ℝ 1 f)
    (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ) (j : Fin n) :
    (∫ x, f x * (fderiv ℝ φ x) (PDE.basisVec j)) =
      -∫ x, (fderiv ℝ f x) (PDE.basisVec j) * φ x := by
  have hdf : Continuous (fun x => (fderiv ℝ f x) (PDE.basisVec j)) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) (PDE.basisVec j)) :=
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left)
    ((hf.continuous.mul hdφ).integrable_of_hasCompactSupport
      (hφK.fderiv_apply ℝ (PDE.basisVec j)).mul_left)
    ((hf.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left)
    (fun x _ => hf.differentiable (by norm_num) x)
    (fun x _ => hφ.differentiable (by norm_num) x)

private theorem short_time_auxiliary_exp_fderiv (c : ℂ) (y : PDE.Vec 2) :
    HasFDerivAt (fun z : PDE.Vec 2 => (Complex.exp ⟨z 0, z 1⟩ * c).re)
      (((Complex.exp ⟨y 0, y 1⟩ * c).re) • (ContinuousLinearMap.proj (0 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ) -
        ((Complex.exp ⟨y 0, y 1⟩ * c).im) • (ContinuousLinearMap.proj (1 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ)) y ∧
    HasFDerivAt (fun z : PDE.Vec 2 => (Complex.exp ⟨z 0, z 1⟩ * c).im)
      (((Complex.exp ⟨y 0, y 1⟩ * c).im) • (ContinuousLinearMap.proj (0 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ) +
        ((Complex.exp ⟨y 0, y 1⟩ * c).re) • (ContinuousLinearMap.proj (1 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ)) y := by
  have h0 := (ContinuousLinearMap.proj (0 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ).hasFDerivAt
    (x := y)
  have h1 := (ContinuousLinearMap.proj (1 : Fin 2) : PDE.Vec 2 →L[ℝ] ℝ).hasFDerivAt
    (x := y)
  have hc := h0.exp.mul h1.cos
  have hs := h0.exp.mul h1.sin
  constructor
  · convert (hc.mul_const c.re).sub (hs.mul_const c.im) using 1
    · ext z
      simp [Complex.mul_re, Complex.exp_re, Complex.exp_im]
    · ext v
      simp only [sub_apply, add_apply,
        smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
      ring
  · convert (hc.mul_const c.im).add (hs.mul_const c.re) using 1
    · ext z
      simp [Complex.mul_im, Complex.exp_re, Complex.exp_im]
    · ext v
      simp only [add_apply,
        smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
        Complex.mul_re, Complex.mul_im, Complex.exp_re, Complex.exp_im]
      ring

/-- Auxiliary integration by parts for the complex exponential lift, against
C1 compact tests. The equal diagonal entries cancel, leaving precisely the
complex drift term; no sign condition is imposed on the force. -/
theorem short_time_complex_lift_auxiliary_ibp {V : Set (PDE.Vec 2)}
    (ζ u h : ℂ) (M : ℝ) (φ : PDE.Vec 2 → ℝ)
    (hφ : ContDiff ℝ 1 φ) (hφK : HasCompactSupport φ)
    (hφV : tsupport φ ⊆ V) :
    (∫ y in V,
      (ζ.re * (Complex.exp ⟨y 0, y 1⟩ * h).re +
        M * (Complex.exp ⟨y 0, y 1⟩ * u).re) *
          (fderiv ℝ φ y) (PDE.basisVec 0) +
      (ζ.im * (Complex.exp ⟨y 0, y 1⟩ * h).re -
        M * (Complex.exp ⟨y 0, y 1⟩ * u).im) *
          (fderiv ℝ φ y) (PDE.basisVec 1)) =
      -∫ y in V, (Complex.exp ⟨y 0, y 1⟩ * (ζ * h)).re * φ y := by
  let F : PDE.Vec 2 → ℝ := fun y =>
    ζ.re * (Complex.exp ⟨y 0, y 1⟩ * h).re +
      M * (Complex.exp ⟨y 0, y 1⟩ * u).re
  let G : PDE.Vec 2 → ℝ := fun y =>
    ζ.im * (Complex.exp ⟨y 0, y 1⟩ * h).re -
      M * (Complex.exp ⟨y 0, y 1⟩ * u).im
  have hf (c : ℂ) : ContDiff ℝ 1
      (fun y : PDE.Vec 2 => (Complex.exp ⟨y 0, y 1⟩ * c).re) := by
    simp only [Complex.mul_re, Complex.exp_re, Complex.exp_im]
    fun_prop
  have hg (c : ℂ) : ContDiff ℝ 1
      (fun y : PDE.Vec 2 => (Complex.exp ⟨y 0, y 1⟩ * c).im) := by
    simp only [Complex.mul_im, Complex.exp_re, Complex.exp_im]
    fun_prop
  have hF : ContDiff ℝ 1 F :=
    (contDiff_const.mul (hf h)).add (contDiff_const.mul (hf u))
  have hG : ContDiff ℝ 1 G :=
    (contDiff_const.mul (hf h)).sub (contDiff_const.mul (hg u))
  have hdiv (y : PDE.Vec 2) :
      (fderiv ℝ F y) (PDE.basisVec 0) +
        (fderiv ℝ G y) (PDE.basisVec 1) =
          (Complex.exp ⟨y 0, y 1⟩ * (ζ * h)).re := by
    have hFy := ((short_time_auxiliary_exp_fderiv h y).1.const_mul ζ.re).add
      ((short_time_auxiliary_exp_fderiv u y).1.const_mul M)
    have hGy := ((short_time_auxiliary_exp_fderiv h y).1.const_mul ζ.im).sub
      ((short_time_auxiliary_exp_fderiv u y).2.const_mul M)
    change HasFDerivAt F _ y at hFy
    change HasFDerivAt G _ y at hGy
    rw [hFy.fderiv, hGy.fderiv]
    simp [PDE.basisVec_apply, Complex.mul_re, Complex.mul_im]
    ring
  have hIntF : Integrable (fun y => F y * (fderiv ℝ φ y) (PDE.basisVec 0)) :=
    (hF.continuous.mul ((hφ.continuous_fderiv (by norm_num)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hφK.fderiv_apply ℝ (PDE.basisVec 0)).mul_left
  have hIntG : Integrable (fun y => G y * (fderiv ℝ φ y) (PDE.basisVec 1)) :=
    (hG.continuous.mul ((hφ.continuous_fderiv (by norm_num)).clm_apply
      continuous_const)).integrable_of_hasCompactSupport
        (hφK.fderiv_apply ℝ (PDE.basisVec 1)).mul_left
  have hDF : Integrable (fun y => (fderiv ℝ F y) (PDE.basisVec 0) * φ y) :=
    (((hF.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left
  have hDG : Integrable (fun y => (fderiv ℝ G y) (PDE.basisVec 1) * φ y) :=
    (((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const).mul
      hφ.continuous).integrable_of_hasCompactSupport hφK.mul_left
  have he : (∫ y, F y * (fderiv ℝ φ y) (PDE.basisVec 0) +
      G y * (fderiv ℝ φ y) (PDE.basisVec 1)) =
      -∫ y, (Complex.exp ⟨y 0, y 1⟩ * (ζ * h)).re * φ y := by
    rw [integral_add hIntF hIntG,
      short_time_C1_integral_mul_partialDeriv hF hφ hφK,
      short_time_C1_integral_mul_partialDeriv hG hφ hφK,
      ← neg_add, ← integral_add hDF hDG]
    congr 1
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      dsimp only
      rw [← add_mul, hdiv]
  change (∫ y in V, F y * (fderiv ℝ φ y) (PDE.basisVec 0) +
    G y * (fderiv ℝ φ y) (PDE.basisVec 1)) = _
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [fderiv_of_notMem_tsupport ℝ (fun hy' => hy (hφV hy'))]
      simp),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [image_eq_zero_of_notMem_tsupport (fun hy' => hy (hφV hy'))]
      simp)]
  exact he

private def shortTimePhysicalTestSlice {d : ℕ} (y : PDE.Vec 2) :
    PDE.Vec d × ℝ → PDE.Vec (d + 2) × ℝ :=
  fun z => ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2)

private theorem short_time_physical_test_slice_contDiff {d : ℕ} (y : PDE.Vec 2) :
    ContDiff ℝ 1 (shortTimePhysicalTestSlice (d := d) y) :=
  (((PDE.vecAppendEquiv d 2).symm.contDiff.comp
    (contDiff_fst.prodMk contDiff_const)).prodMk contDiff_snd)

/-- A genuine compact C1 test on the lifted cylinder restricts to a compact
C1 test on each physical spacetime slice. -/
def shortTimeComplexLiftPhysicalTest {d : ℕ} {U : Set (PDE.Vec d)}
    {V : Set (PDE.Vec 2)} {J : Set ℝ}
    (φ : PDE.ParTestFunction (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) J)
    (y : PDE.Vec 2) : PDE.ParTestFunction U J where
  toFun := φ.toFun ∘ shortTimePhysicalTestSlice y
  contDiff := φ.contDiff.comp (short_time_physical_test_slice_contDiff y)
  hasCompactSupport := φ.hasCompactSupport.comp_isClosedEmbedding (by
    exact (PDE.isClosedEmbedding_vecAppendRightSlice y).prodMap
      (Homeomorph.refl ℝ).isClosedEmbedding)
  tsupport_subset := by
    intro z hz
    have hz' := tsupport_comp_subset_preimage φ.toFun
      (short_time_physical_test_slice_contDiff y).continuous hz
    have he := φ.tsupport_subset hz'
    exact ⟨by simpa only [shortTimePhysicalTestSlice,
      ContinuousLinearEquiv.apply_symm_apply] using he.1.1, he.2⟩

/-- Physical and time derivatives of the literal lifted test slices agree
with their ambient coordinate derivatives. -/
theorem short_time_complex_lift_physical_test_derivatives {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {J : Set ℝ}
    (φ : PDE.ParTestFunction (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) J)
    (y : PDE.Vec 2) (z : PDE.Vec d × ℝ) :
    PDE.parTimeDeriv (shortTimeComplexLiftPhysicalTest φ y).toFun z =
      PDE.parTimeDeriv φ.toFun ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) ∧
    ∀ j : Fin d,
      PDE.parSpaceGrad (shortTimeComplexLiftPhysicalTest φ y).toFun z j =
        PDE.parSpaceGrad φ.toFun
          ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) (Fin.castAdd 2 j) := by
  have hS := (((PDE.vecAppendEquiv d 2).symm.hasFDerivAt.comp z
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
      (hasFDerivAt_const y z))).prodMk (hasFDerivAt_snd (𝕜 := ℝ) (p := z)))
  change HasFDerivAt (shortTimePhysicalTestSlice y) _ z at hS
  have hd := (φ.contDiff.differentiable (by norm_num)).differentiableAt
    (x := shortTimePhysicalTestSlice y z)
  have he : fderiv ℝ (shortTimeComplexLiftPhysicalTest φ y).toFun z =
      (fderiv ℝ φ.toFun (shortTimePhysicalTestSlice y z)).comp _ :=
    fderiv_comp z hd hS.differentiableAt
  rw [hS.fderiv] at he
  constructor
  · unfold PDE.parTimeDeriv
    rw [he]
    change (fderiv ℝ φ.toFun (shortTimePhysicalTestSlice y z))
      ((PDE.vecAppendEquiv d 2).symm (0 : PDE.Vec d × PDE.Vec 2), 1) = _
    rw [map_zero]
    rfl
  · intro j
    unfold PDE.parSpaceGrad
    rw [he]
    change (fderiv ℝ φ.toFun (shortTimePhysicalTestSlice y z))
      ((PDE.vecAppendEquiv d 2).symm (PDE.basisVec j, 0), 0) = _
    rw [PDE.vecAppendEquiv_symm_basis_left]
    rfl

private def shortTimeAuxiliaryTestSlice {d : ℕ} (z : PDE.Vec d × ℝ) :
    PDE.Vec 2 → PDE.Vec (d + 2) × ℝ :=
  fun y => ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2)

/-- Every auxiliary slice of a compact C1 parabolic test is compact C1 in the
auxiliary domain, with the literal ambient spatial derivatives. -/
theorem short_time_complex_lift_auxiliary_test {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {J : Set ℝ}
    (φ : PDE.ParTestFunction (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) J)
    (z : PDE.Vec d × ℝ) :
    let ψ : PDE.Vec 2 → ℝ := fun y =>
      φ.toFun ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2)
    ContDiff ℝ 1 ψ ∧ HasCompactSupport ψ ∧ tsupport ψ ⊆ V ∧
      ∀ y j, (fderiv ℝ ψ y) (PDE.basisVec j) =
        PDE.parSpaceGrad φ.toFun
          ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) (Fin.natAdd d j) := by
  dsimp only
  have hScont : ContDiff ℝ 1 (shortTimeAuxiliaryTestSlice z) :=
    (((PDE.vecAppendEquiv d 2).symm.contDiff.comp
      (contDiff_const.prodMk contDiff_id)).prodMk contDiff_const)
  have hEmb : Topology.IsClosedEmbedding (shortTimeAuxiliaryTestSlice z) := by
    have hProd : Isometry (fun x : PDE.Vec (d + 2) => (x, z.2)) := by
      intro x x'
      simp [Prod.edist_eq]
    exact hProd.isClosedEmbedding.comp (PDE.isClosedEmbedding_vecAppendLeftSlice z.1)
  refine ⟨φ.contDiff.comp hScont, φ.hasCompactSupport.comp_isClosedEmbedding hEmb,
    ?_, ?_⟩
  · intro y hy
    have hy' := tsupport_comp_subset_preimage φ.toFun hScont.continuous hy
    have he := φ.tsupport_subset hy'
    simpa only [shortTimeAuxiliaryTestSlice, ContinuousLinearEquiv.apply_symm_apply]
      using he.1.2
  · intro y j
    have hS := (((PDE.vecAppendEquiv d 2).symm.hasFDerivAt.comp y
      ((hasFDerivAt_const z.1 y).prodMk (hasFDerivAt_id y))).prodMk
        (hasFDerivAt_const z.2 y))
    change HasFDerivAt (shortTimeAuxiliaryTestSlice z) _ y at hS
    have hd := (φ.contDiff.differentiable (by norm_num)).differentiableAt
      (x := shortTimeAuxiliaryTestSlice z y)
    change (fderiv ℝ (φ.toFun ∘ shortTimeAuxiliaryTestSlice z) y)
      (PDE.basisVec j) = _
    rw [fderiv_comp y hd hS.differentiableAt, hS.fderiv]
    change (fderiv ℝ φ.toFun (shortTimeAuxiliaryTestSlice z y))
      ((PDE.vecAppendEquiv d 2).symm (0, PDE.basisVec j), 0) = _
    rw [PDE.vecAppendEquiv_symm_basis_right]
    rfl

/-- The auxiliary part of the actual lifted parabolic flux cancels against
the complex drift for every C1 parabolic test, on each physical time slice. -/
theorem short_time_complex_lift_parabolic_auxiliary_ibp {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {J : Set ℝ}
    (φ : PDE.ParTestFunction (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) J)
    (z : PDE.Vec d × ℝ) (ζ u h : ℂ) (M : ℝ) :
    (∫ y in V,
      (ζ.re * (Complex.exp ⟨y 0, y 1⟩ * h).re +
        M * (Complex.exp ⟨y 0, y 1⟩ * u).re) *
          PDE.parSpaceGrad φ.toFun
            ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) (Fin.natAdd d 0) +
      (ζ.im * (Complex.exp ⟨y 0, y 1⟩ * h).re -
        M * (Complex.exp ⟨y 0, y 1⟩ * u).im) *
          PDE.parSpaceGrad φ.toFun
            ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) (Fin.natAdd d 1)) =
      -∫ y in V, (Complex.exp ⟨y 0, y 1⟩ * (ζ * h)).re *
        φ.toFun ((PDE.vecAppendEquiv d 2).symm (z.1, y), z.2) := by
  obtain ⟨hC, hK, hV, hD⟩ := short_time_complex_lift_auxiliary_test φ z
  simpa only [hD] using short_time_complex_lift_auxiliary_ibp ζ u h M _ hC hK hV

private def shortTimeLiftSpacetimeHomeomorph (d : ℕ) :
    (PDE.Vec (d + 2) × ℝ) ≃ₜ ((PDE.Vec d × ℝ) × PDE.Vec 2) where
  toFun z := (((PDE.vecAppendEquiv d 2 z.1).1, z.2),
    (PDE.vecAppendEquiv d 2 z.1).2)
  invFun p := ((PDE.vecAppendEquiv d 2).symm (p.1.1, p.2), p.1.2)
  left_inv z := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem short_time_compact_test_mul_integrable {d : ℕ}
    {μ : Measure (PDE.Vec d × ℝ)} {f g : PDE.Vec d × ℝ → ℝ}
    (hf : Integrable f μ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun z => f z * g z) μ := by
  obtain ⟨C, hC⟩ := hg.bounded_above_of_compact_support hgc
  exact hf.mul_bdd hg.aestronglyMeasurable (c := C) (Eventually.of_forall hC)

private theorem short_time_lift_fubini_cancellation
    {d : ℕ} {μ : Measure (PDE.Vec d × ℝ)} {ν : Measure (PDE.Vec 2)}
    [SFinite μ] [SFinite ν]
    {a b c : (PDE.Vec d × ℝ) × PDE.Vec 2 → ℝ}
    (ha : Integrable a (μ.prod ν)) (hb : Integrable b (μ.prod ν))
    (hc : Integrable c (μ.prod ν))
    (hphysical : ∀ y, (∫ z, a (z, y) - c (z, y) ∂μ) = 0)
    (hauxiliary : ∀ z, (∫ y, b (z, y) ∂ν) = -∫ y, c (z, y) ∂ν) :
    (∫ p, a p + b p ∂μ.prod ν) = 0 := by
  have hp : (∫ p, a p - c p ∂μ.prod ν) = 0 := by
    rw [integral_prod_symm (fun p => a p - c p) (ha.sub hc)]
    simp only [hphysical, integral_zero]
  have hq : (∫ p, b p ∂μ.prod ν) = -(∫ p, c p ∂μ.prod ν) := by
    rw [integral_prod _ hb, integral_prod _ hc, ← integral_neg]
    exact integral_congr_ae (ae_of_all _ hauxiliary)
  rw [integral_sub ha hc] at hp
  rw [integral_add ha hb, hq]
  linarith

/-- The literal weak integrand of the two-coordinate real exponential lift.
`P` is the physical complex flux and `h` its force-direction contraction. -/
noncomputable def shortTimeComplexLiftWeakIntegrand {d : ℕ}
    (u h : PDE.Vec d × ℝ → ℂ) (P : Fin d → PDE.Vec d × ℝ → ℂ)
    (ζ : ℂ) (M : ℝ) (φ : PDE.Vec (d + 2) × ℝ → ℝ)
    (z : PDE.Vec (d + 2) × ℝ) : ℝ :=
  let x := ((PDE.vecAppendEquiv d 2 z.1).1, z.2)
  let e := Complex.exp
    ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩;
  -((e * u x).re * PDE.parTimeDeriv φ z) +
    PDE.vecDot (Fin.addCases (fun j => (e * P j x).re)
      ![ζ.re * (e * h x).re + M * (e * u x).re,
        ζ.im * (e * h x).re - M * (e * u x).im]) (PDE.parSpaceGrad φ z)

/-- The physical complex weak equation becomes the homogeneous real weak
identity after adjoining the two exponential coordinates. All pairings are
integrable; the signed force term is canceled by auxiliary integration by parts. -/
theorem short_time_complex_lift_weak_integral {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hI : MeasurableSet I)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (u h : PDE.Vec d × ℝ → ℂ) (P : Fin d → PDE.Vec d × ℝ → ℂ)
    (ζ : ℂ) (M : ℝ)
    (hu : IntegrableOn u (U ×ˢ I)) (hh : IntegrableOn h (U ×ˢ I))
    (hP : ∀ j, IntegrableOn (P j) (U ×ˢ I))
    (hweak : ∀ ψ : PDE.ParTestFunction U (interior I), ∀ e : ℂ,
      (∫ z in U ×ˢ I,
        -((e * u z).re * PDE.parTimeDeriv ψ.toFun z) +
          (∑ j, (e * P j z).re * PDE.parSpaceGrad ψ.toFun z j) -
          (e * (ζ * h z)).re * ψ.toFun z) = 0)
    (φ : PDE.ParTestFunction (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) (interior I)) :
    IntegrableOn (shortTimeComplexLiftWeakIntegrand u h P ζ M φ.toFun)
      ((PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I) ∧
    (∫ z in (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I,
      shortTimeComplexLiftWeakIntegrand u h P ζ M φ.toFun z) = 0 := by
  let E := (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I
  let μ := volume.restrict (U ×ˢ I)
  let ν := volume.restrict V
  let e (z : PDE.Vec (d + 2) × ℝ) : ℂ := Complex.exp
    ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩
  let x (z : PDE.Vec (d + 2) × ℝ) := ((PDE.vecAppendEquiv d 2 z.1).1, z.2)
  let w (z : PDE.Vec (d + 2) × ℝ) := (e z * u (x z)).re
  let H (z : PDE.Vec (d + 2) × ℝ) := (e z * h (x z)).re
  let J (j : Fin d) (z : PDE.Vec (d + 2) × ℝ) := (e z * P j (x z)).re
  let c (z : PDE.Vec (d + 2) × ℝ) := (e z * (ζ * h (x z))).re * φ.toFun z
  let a (z : PDE.Vec (d + 2) × ℝ) :=
    -(w z * PDE.parTimeDeriv φ.toFun z) +
      ∑ j, J j z * PDE.parSpaceGrad φ.toFun z (Fin.castAdd 2 j)
  let b (z : PDE.Vec (d + 2) × ℝ) :=
    (ζ.re * H z + M * w z) * PDE.parSpaceGrad φ.toFun z (Fin.natAdd d 0) +
    (ζ.im * H z - M * (e z * u (x z)).im) *
      PDE.parSpaceGrad φ.toFun z (Fin.natAdd d 1)
  have hlift {f : PDE.Vec d × ℝ → ℂ} (hf : IntegrableOn f (U ×ˢ I)) :
      Integrable (fun z => e z * f (x z)) (volume.restrict E) := by
    exact memLp_one_iff_integrable.mp
      (short_time_complex_lift_spacetime_memLp hU hV hI hVfinite r hr
        (memLp_one_iff_integrable.mpr hf))
  have hw : Integrable w (volume.restrict E) := (hlift hu).re
  have hH : Integrable H (volume.restrict E) := (hlift hh).re
  have hJ (j : Fin d) : Integrable (J j) (volume.restrict E) := (hlift (hP j)).re
  have htest (v : PDE.Vec (d + 2) × ℝ) :
      Continuous (fun z => fderiv ℝ φ.toFun z v) ∧
      HasCompactSupport (fun z => fderiv ℝ φ.toFun z v) :=
    ⟨(φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const,
      φ.hasCompactSupport.fderiv_apply ℝ v⟩
  have hmul {f : PDE.Vec (d + 2) × ℝ → ℝ}
      (hf : Integrable f (volume.restrict E)) (v : PDE.Vec (d + 2) × ℝ) :
      Integrable (fun z => f z * fderiv ℝ φ.toFun z v) (volume.restrict E) :=
    short_time_compact_test_mul_integrable hf (htest v).1 (htest v).2
  have ha : Integrable a (volume.restrict E) :=
    (hmul hw (0, 1)).neg.add (integrable_finsetSum _ fun j _ =>
      hmul (hJ j) (PDE.basisVec (Fin.castAdd 2 j), 0))
  have hb : Integrable b (volume.restrict E) :=
    (hmul ((hH.const_mul ζ.re).add (hw.const_mul M))
      (PDE.basisVec (Fin.natAdd d 0), 0)).add
    (hmul ((hH.const_mul ζ.im).sub ((hlift hu).im.const_mul M))
      (PDE.basisVec (Fin.natAdd d 1), 0))
  have hc : Integrable c (volume.restrict E) :=
    short_time_compact_test_mul_integrable (hlift (hh.const_mul ζ)).re
      φ.contDiff.continuous φ.hasCompactSupport
  have heq : shortTimeComplexLiftWeakIntegrand u h P ζ M φ.toFun = fun z => a z + b z := by
    funext z
    simp only [shortTimeComplexLiftWeakIntegrand, PDE.vecDot, Fin.sum_univ_add,
      Fin.addCases_left, Fin.addCases_right, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    dsimp only [a, b, c, w, H, J, e, x]
    ring
  refine ⟨by rw [heq]; exact ha.add hb, ?_⟩
  rw [heq]
  let S := shortTimeLiftSpacetimeHomeomorph d
  have hS : MeasurePreserving S (volume.restrict E) (μ.prod ν) :=
    short_time_lift_spacetime_measurePreserving hU hV
  have hSinv : MeasurePreserving S.symm (μ.prod ν) (volume.restrict E) :=
    MeasurePreserving.symm S.toMeasurableEquiv hS
  have ha' : Integrable (fun p => a (S.symm p)) (μ.prod ν) :=
    hSinv.integrable_comp_of_integrable ha
  have hb' : Integrable (fun p => b (S.symm p)) (μ.prod ν) :=
    hSinv.integrable_comp_of_integrable hb
  have hc' : Integrable (fun p => c (S.symm p)) (μ.prod ν) :=
    hSinv.integrable_comp_of_integrable hc
  rw [← hSinv.integral_comp S.symm.measurableEmbedding (fun z => a z + b z)]
  apply short_time_lift_fubini_cancellation ha' hb' hc'
  · intro y
    have ht := hweak (shortTimeComplexLiftPhysicalTest φ y) (Complex.exp ⟨y 0, y 1⟩)
    convert ht using 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => by
      obtain ⟨hdt, hdx⟩ := short_time_complex_lift_physical_test_derivatives φ y z
      simp only [hdt, hdx]
      dsimp [a, c, w, J, e, x, S, shortTimeLiftSpacetimeHomeomorph,
        shortTimeComplexLiftPhysicalTest, shortTimePhysicalTestSlice]
      simp
  · intro z
    simpa [b, c, H, w, e, x, S, shortTimeLiftSpacetimeHomeomorph] using
      short_time_complex_lift_parabolic_auxiliary_ibp φ z ζ (u z) (h z) M


/-- A literal exponential lift satisfying the physical complex weak equation
is a real weak solution for the lifted coefficient matrix. -/
theorem short_time_complex_lift_isParabolicWeakSolution {d : ℕ}
    {U : Set (PDE.Vec d)} {V : Set (PDE.Vec 2)} {I : Set ℝ}
    (hU : MeasurableSet U) (hV : MeasurableSet V) (hI : MeasurableSet I)
    (hVfinite : volume V < ⊤) (r : ℝ) (hr : ∀ y ∈ V, y 0 ≤ r)
    (A : PDE.Vec d → PDE.Mat d) (i : Fin d)
    (u : PDE.Vec d × ℝ → ℂ) (D : Fin d → PDE.Vec d × ℝ → ℂ)
    (ζ : ℂ) (M : ℝ)
    (hu : IntegrableOn u (U ×ˢ I))
    (hP : ∀ j, IntegrableOn
      (fun z => (1 / 2 : ℂ) * ∑ k, (A z.1 j k : ℂ) * D k z) (U ×ˢ I))
    (hh : IntegrableOn (fun z => ∑ k, (A z.1 k i : ℂ) * D k z) (U ×ˢ I))
    (hweak : ∀ ψ : PDE.ParTestFunction U (interior I), ∀ e : ℂ,
      (∫ z in U ×ˢ I,
        -((e * u z).re * PDE.parTimeDeriv ψ.toFun z) +
          (∑ j, (e * ((1 / 2 : ℂ) * ∑ k, (A z.1 j k : ℂ) * D k z)).re *
            PDE.parSpaceGrad ψ.toFun z j) -
          (e * (ζ * ∑ k, (A z.1 k i : ℂ) * D k z)).re * ψ.toFun z) = 0)
    (w : PDE.ParH1Function (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) I)
    (hw : ∀ z, w.toFun z = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
    (hD : ∀ z j, w.grad z (Fin.castAdd 2 j) = (Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
    (h0 : ∀ z, w.grad z (Fin.natAdd d (0 : Fin 2)) = w.toFun z)
    (h1 : ∀ z, w.grad z (Fin.natAdd d (1 : Fin 2)) = -(Complex.exp
      ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
        u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im) :
    PDE.IsParabolicWeakSolution
      (fun z => shortTimeComplexLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) I w := by
  intro φ
  have heq : PDE.parWeakIntegrand
      (fun z => shortTimeComplexLiftMatrix (A (PDE.vecAppendEquiv d 2 z.1).1) i ζ M)
      w φ.toFun = shortTimeComplexLiftWeakIntegrand u
        (fun z => ∑ k, (A z.1 k i : ℂ) * D k z)
        (fun j z => (1 / 2 : ℂ) * ∑ k, (A z.1 j k : ℂ) * D k z) ζ M φ.toFun := by
    funext z
    have hgrad : w.grad z = Fin.addCases
        (fun j => (Complex.exp
          ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            D j ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re)
        ![w.toFun z, -(Complex.exp
          ⟨z.1 (Fin.natAdd d (0 : Fin 2)), z.1 (Fin.natAdd d (1 : Fin 2))⟩ *
            u ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).im] := by
      ext j
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simpa only [Fin.addCases_left] using hD z j
      · fin_cases j <;> simp [h0 z, h1 z]
    simp only [PDE.parWeakIntegrand, hgrad, hw z, short_time_complex_lift_flux]
    rfl
  rw [heq]
  exact short_time_complex_lift_weak_integral hU hV hI hVfinite r hr u
    (fun z => ∑ k, (A z.1 k i : ℂ) * D k z)
    (fun j z => (1 / 2 : ℂ) * ∑ k, (A z.1 j k : ℂ) * D k z)
    ζ M hu hh hP hweak φ

/-- An affine change of time leaves every spatial coordinate unchanged. -/
def shortTimeParabolicTimeHomeomorph (d : ℕ) (T : ℝ) {r : ℝ} (hr : 0 < r) :
    (PDE.Vec d × ℝ) ≃ₜ (PDE.Vec d × ℝ) :=
  (Homeomorph.refl _).prodCongr
    ((Homeomorph.mulLeft₀ (r ^ 2) (pow_pos hr 2).ne').trans (Homeomorph.addLeft T))

private theorem short_time_time_map_measure {d : ℕ} (T : ℝ) {r : ℝ} (hr : 0 < r)
    (U : Set (PDE.Vec d)) (J : Set ℝ) :
    (volume.restrict (U ×ˢ J)).map (shortTimeParabolicTimeHomeomorph d T hr) =
      ENNReal.ofReal ((r ^ 2)⁻¹) •
        volume.restrict (U ×ˢ (PDE.Parabolic.Rescale.timeMap T r '' J)) := by
  have heq : (shortTimeParabolicTimeHomeomorph d T hr :
      (PDE.Vec d × ℝ) → (PDE.Vec d × ℝ)) =
      Prod.map id (PDE.Parabolic.Rescale.timeMap T r) := rfl
  rw [heq, Measure.volume_eq_prod, ← Measure.prod_restrict,
    ← Measure.map_prod_map _ _ measurable_id
      (PDE.Parabolic.Rescale.timeMap_measurableEmbedding T hr).measurable,
    Measure.map_id, PDE.Parabolic.Rescale.map_restrict_timeMap T hr,
    Measure.prod_smul_right, Measure.prod_restrict]

/-- Time normalization of the actual parabolic energy representative. Spatial
gradients and every-time weak traces are retained literally. -/
def shortTimeParabolicTimeRescale {d : ℕ} (T : ℝ) {r : ℝ} (hr : 0 < r)
    {U : Set (PDE.Vec d)} {I J : Set ℝ}
    (hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ I)
    (u : PDE.ParH1Function U I) : PDE.ParH1Function U J where
  toFun := fun z => u.toFun (shortTimeParabolicTimeHomeomorph d T hr z)
  grad := fun z => u.grad (shortTimeParabolicTimeHomeomorph d T hr z)
  memL2 := PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul
    (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
    ENNReal.ofReal_ne_top (short_time_time_map_measure T hr U J)
    (u.memL2.mono_measure (Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl))
  gradMemL2 i := PDE.Parabolic.Rescale.memLp_comp_of_map_eq_smul
    (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
    ENNReal.ofReal_ne_top (short_time_time_map_measure T hr U J)
    ((u.gradMemL2 i).mono_measure
      (Measure.restrict_mono (prod_mono subset_rfl hJI) le_rfl))
  sliceWeakGradient := by
    have ha := ae_mono (Measure.restrict_mono hJI le_rfl) u.sliceWeakGradient
    exact PDE.Parabolic.Rescale.ae_comp_of_map_eq_smul
      (PDE.Parabolic.Rescale.timeMap_measurableEmbedding T hr)
      (PDE.Parabolic.Rescale.map_restrict_timeMap T hr J) ha
  sliceL2loc t ht K hK hKU :=
    u.sliceL2loc _ (hJI (mem_image_of_mem _ ht)) K hK hKU
  weakCont ψ hψ :=
    (u.weakCont ψ hψ).comp
      (PDE.Parabolic.Rescale.continuous_timeMap T r).continuousOn
      (fun _ ht => hJI (mem_image_of_mem _ ht))

private theorem short_time_time_homeomorph_symm_apply {d : ℕ}
    (T : ℝ) {r : ℝ} (hr : 0 < r) (z : PDE.Vec d × ℝ) :
    (shortTimeParabolicTimeHomeomorph d T hr).symm z =
      (z.1, (z.2 - T) / r ^ 2) := by
  apply (Homeomorph.symm_apply_eq _).2
  refine Prod.ext ?_ ?_
  · rfl
  · change z.2 = T + r ^ 2 * ((z.2 - T) / r ^ 2)
    field_simp
    ring

/-- The literal compact C1 test transported to the original time variable. -/
def shortTimeParabolicTimeTest {d : ℕ} (T : ℝ) {r : ℝ} (hr : 0 < r)
    {U : Set (PDE.Vec d)} {I J : Set ℝ}
    (hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ I)
    (φ : PDE.ParTestFunction U (interior J)) : PDE.ParTestFunction U (interior I) where
  toFun := φ.toFun ∘ (shortTimeParabolicTimeHomeomorph d T hr).symm
  contDiff := by
    have heq : ((shortTimeParabolicTimeHomeomorph d T hr).symm :
        (PDE.Vec d × ℝ) → (PDE.Vec d × ℝ)) =
        fun z => (z.1, (z.2 - T) / r ^ 2) :=
      funext (short_time_time_homeomorph_symm_apply T hr)
    rw [heq]
    exact φ.contDiff.comp (contDiff_fst.prodMk
      ((contDiff_snd.sub contDiff_const).div_const _))
  hasCompactSupport := φ.hasCompactSupport.comp_homeomorph _
  tsupport_subset := by
    rw [tsupport_comp_eq_preimage]
    intro z hz
    have h := φ.tsupport_subset hz
    refine ⟨h.1, ?_⟩
    let τ := (Homeomorph.mulLeft₀ (r ^ 2) (pow_pos hr 2).ne').trans
      (Homeomorph.addLeft T)
    have him : τ '' J ⊆ I := hJI
    apply interior_mono him
    rw [← τ.image_interior]
    exact ⟨((shortTimeParabolicTimeHomeomorph d T hr).symm z).2,
      h.2, congrArg Prod.snd
        ((shortTimeParabolicTimeHomeomorph d T hr).apply_symm_apply z)⟩

private theorem short_time_time_test_derivatives {d : ℕ}
    (T : ℝ) {r : ℝ} (hr : 0 < r) {φ : PDE.Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (z : PDE.Vec d × ℝ) :
    PDE.parTimeDeriv (φ ∘ shortTimeParabolicTimeHomeomorph d T hr) z =
      r ^ 2 * PDE.parTimeDeriv φ (shortTimeParabolicTimeHomeomorph d T hr z) ∧
    PDE.parSpaceGrad (φ ∘ shortTimeParabolicTimeHomeomorph d T hr) z =
      PDE.parSpaceGrad φ (shortTimeParabolicTimeHomeomorph d T hr z) := by
  let L : (PDE.Vec d × ℝ) →L[ℝ] (PDE.Vec d × ℝ) :=
    (ContinuousLinearMap.fst ℝ (PDE.Vec d) ℝ).prod
      ((r ^ 2) • ContinuousLinearMap.snd ℝ (PDE.Vec d) ℝ)
  have hF : HasFDerivAt (shortTimeParabolicTimeHomeomorph d T hr) L z :=
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z)).prodMk
      (((hasFDerivAt_snd (𝕜 := ℝ) (p := z)).const_smul (r ^ 2)).const_add T)
  have hd := (hφ.differentiable (by norm_num)).differentiableAt
    (x := shortTimeParabolicTimeHomeomorph d T hr z)
  have he := fderiv_comp z hd hF.differentiableAt
  rw [hF.fderiv] at he
  constructor
  · unfold PDE.parTimeDeriv
    rw [he]
    have hL : L (0, 1) = (r ^ 2) • ((0 : PDE.Vec d), (1 : ℝ)) := by
      ext <;> simp [L]
    simp only [ContinuousLinearMap.comp_apply, hL, map_smul, smul_eq_mul]
  · funext j
    unfold PDE.parSpaceGrad
    rw [he]
    have hL : L (PDE.basisVec j, 0) = (PDE.basisVec j, 0) := by
      ext <;> simp [L]
    simp only [ContinuousLinearMap.comp_apply, hL]

/-- Time normalization transports the homogeneous equation with its exact
coefficient factor `r²`, without altering the spatial gradient. -/
theorem short_time_time_rescale_isParabolicWeakSolution {d : ℕ}
    (T : ℝ) {r : ℝ} (hr : 0 < r)
    {U : Set (PDE.Vec d)} {I J : Set ℝ}
    (hU : MeasurableSet U) (hI : MeasurableSet I)
    (hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ I)
    (a : PDE.ParCoeffField d) (u : PDE.ParH1Function U I)
    (hu : PDE.IsParabolicWeakSolution a U I u) :
    PDE.IsParabolicWeakSolution
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph d T hr z)) U J
      (shortTimeParabolicTimeRescale T hr hJI u) := by
  intro φ
  let ψ := shortTimeParabolicTimeTest T hr hJI φ
  obtain ⟨hint, hzero⟩ := hu ψ
  have hsub : U ×ˢ (PDE.Parabolic.Rescale.timeMap T r '' J) ⊆ U ×ˢ I :=
    prod_mono subset_rfl hJI
  have hsupp : tsupport ψ.toFun ⊆
      U ×ˢ (PDE.Parabolic.Rescale.timeMap T r '' J) := by
    intro z hz
    change z ∈ tsupport (φ.toFun ∘
      (shortTimeParabolicTimeHomeomorph d T hr).symm) at hz
    rw [tsupport_comp_eq_preimage] at hz
    have h := φ.tsupport_subset hz
    exact ⟨h.1, _, interior_subset h.2, congrArg Prod.snd
      ((shortTimeParabolicTimeHomeomorph d T hr).apply_symm_apply z)⟩
  have hzero' : (∫ z in U ×ˢ (PDE.Parabolic.Rescale.timeMap T r '' J),
      PDE.parWeakIntegrand a u ψ.toFun z) = 0 := by
    rw [← setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (hU.prod hI) hsub (fun z hz =>
        PDE.Parabolic.Rescale.parWeakIntegrand_eq_zero_of_notMem_tsupport a u
          (fun hz' => hz.2 (hsupp hz')))]
    exact hzero
  have hcomp : ψ.toFun ∘ shortTimeParabolicTimeHomeomorph d T hr = φ.toFun := by
    funext z
    exact congrArg φ.toFun
      ((shortTimeParabolicTimeHomeomorph d T hr).symm_apply_apply z)
  have heq : PDE.parWeakIntegrand
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph d T hr z))
      (shortTimeParabolicTimeRescale T hr hJI u) φ.toFun =
      fun z => r ^ 2 * PDE.parWeakIntegrand a u ψ.toFun
        (shortTimeParabolicTimeHomeomorph d T hr z) := by
    funext z
    obtain ⟨ht, hx⟩ := short_time_time_test_derivatives T hr ψ.contDiff z
    rw [hcomp] at ht hx
    simp only [PDE.parWeakIntegrand, shortTimeParabolicTimeRescale, ht, hx,
      PDE.matVecMul, PDE.vecDot, Matrix.smul_apply, smul_eq_mul,
      mul_assoc, ← Finset.mul_sum]
    ring
  rw [heq]
  refine ⟨?_, ?_⟩
  · exact (PDE.Parabolic.Rescale.integrable_comp_of_map_eq_smul
      (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
      ENNReal.ofReal_ne_top (short_time_time_map_measure T hr U J)
      (hint.mono_set hsub)).const_mul _
  · rw [integral_const_mul,
      PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul
        (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
        (short_time_time_map_measure T hr U J), hzero']
    simp

/-- The same time change multiplies both ellipticity constants by `r²`.
The coefficient measurability is transported from the original cylinder. -/
theorem short_time_time_rescale_isParabolicCoeff {d : ℕ}
    (T : ℝ) {r : ℝ} (hr : 0 < r)
    {U : Set (PDE.Vec d)} {I J : Set ℝ}
    (hJI : PDE.Parabolic.Rescale.timeMap T r '' J ⊆ I)
    {lam Lam : ℝ} {a : PDE.ParCoeffField d}
    (ha : PDE.IsParabolicCoeff lam Lam a U I) :
    PDE.IsParabolicCoeff (r ^ 2 * lam) (r ^ 2 * Lam)
      (fun z => r ^ 2 • a (shortTimeParabolicTimeHomeomorph d T hr z)) U J := by
  have hμ := Measure.restrict_mono (prod_mono (subset_rfl (a := U)) hJI)
    (le_rfl : (volume : Measure (PDE.Vec d × ℝ)) ≤ volume)
  refine ⟨fun i j => ?_, ?_⟩
  · exact (PDE.Parabolic.Rescale.aemeasurable_comp_of_map_eq_smul
      (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
      (short_time_time_map_measure T hr U J)
      ((ha.measurable i j).mono_measure hμ)).const_mul _
  · have h := PDE.Parabolic.Rescale.ae_comp_of_map_eq_smul
      (shortTimeParabolicTimeHomeomorph d T hr).measurableEmbedding
      (short_time_time_map_measure T hr U J) (ae_mono hμ ha.elliptic)
    filter_upwards [h] with z hz
    exact PDE.isEllipticMatrix_smul (pow_pos hr 2) hz

/-- Uniform normalized ellipticity for the signed complex lift. This is
exactly the coefficient factor produced by speeding time up by `4Λ`. -/
theorem short_time_complex_lift_normalized_ellipticity {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (A : PDE.Mat d), EinsteinFull.S5Elliptic A Λ →
      ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
      PDE.IsEllipticMatrix 1 L
        ((4 * Λ) • shortTimeComplexLiftMatrix A i ζ (4 * Λ ^ 3 * (B ^ 2 + 1))) := by
  have hΛ0 : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  obtain ⟨L, _, hmatrix⟩ := short_time_complex_lift_uniform_ellipticity Λ B hΛ hB
  refine ⟨max 1 (4 * Λ * L), le_max_left _ _, fun A hA i ζ hζ => ?_⟩
  have hm := PDE.isEllipticMatrix_smul (by positivity : 0 < 4 * Λ)
    (hmatrix A hA i ζ hζ)
  have hl : 4 * Λ * (Λ⁻¹ / 4) = 1 := by field_simp
  rw [hl] at hm
  exact hm.mono zero_lt_one le_rfl (le_max_right _ _)

/-- The actual continuous physical coefficient field gives continuous entries
of the normalized lift, including its two auxiliary coordinates. -/
theorem short_time_continuous_lift_entry_continuous {d : ℕ}
    (A : EinsteinRelation.CoefficientField d) (i : Fin d) (ζ : ℂ) (M κ : ℝ)
    (j k : Fin (d + 2)) :
    Continuous (fun z : PDE.Vec (d + 2) × ℝ =>
      (κ • shortTimeComplexLiftMatrix (A ((PDE.vecAppendEquiv d 2 z.1).1))
        i ζ M) j k) := by
  have hA (j k : Fin d) : Continuous (fun z : PDE.Vec (d + 2) × ℝ =>
      A ((PDE.vecAppendEquiv d 2 z.1).1) j k) :=
    (A.continuous.matrix_elem j k).comp
      ((PDE.vecAppendEquiv d 2).continuous.fst.comp continuous_fst)
  have hentry : Continuous (fun z : PDE.Vec (d + 2) × ℝ =>
      shortTimeComplexLiftMatrix (A ((PDE.vecAppendEquiv d 2 z.1).1)) i ζ M j k) := by
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa only [shortTimeComplexLiftMatrix, Fin.addCases_left] using
        (hA j k).div_const 2
    · simpa only [shortTimeComplexLiftMatrix, Fin.addCases_left, Fin.addCases_right]
        using (continuous_const : Continuous (fun _ : PDE.Vec (d + 2) × ℝ => (0 : ℝ)))
    · simpa only [shortTimeComplexLiftMatrix, Fin.addCases_right, Fin.addCases_left]
        using (hA k i).const_mul (if j = 0 then ζ.re else ζ.im)
    · simpa only [shortTimeComplexLiftMatrix, Fin.addCases_right] using
        (continuous_const : Continuous (fun _ : PDE.Vec (d + 2) × ℝ =>
          if j = k then M else 0))
  simpa only [Matrix.smul_apply, smul_eq_mul] using hentry.const_mul κ

/-- The signed local maximum estimate for the actual continuous physical
coefficient fields. The constant is chosen before the field and complex force. -/
theorem short_time_continuous_lift_local_max {d : ℕ}
    (Λ B : ℝ) (hΛ : 1 ≤ Λ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A : EinsteinRelation.CoefficientField d),
    (∀ z ∈ PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1 ×ˢ Set.Ioc (-1 : ℝ) 0,
      S5Elliptic (A ((PDE.vecAppendEquiv d 2 z.1).1)) Λ) →
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ B →
    ∀ w : PDE.ParH1Function (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Set.Ioc (-1 : ℝ) 0),
    PDE.IsParabolicWeakSolution
      (fun z => (4 * Λ) • shortTimeComplexLiftMatrix
        (A ((PDE.vecAppendEquiv d 2 z.1).1)) i ζ (4 * Λ ^ 3 * (B ^ 2 + 1)))
      (PDE.euclideanBall (0 : PDE.Vec (d + 2)) 1) (Set.Ioc (-1 : ℝ) 0) w →
    essSup (fun z => ENNReal.ofReal |w.toFun z|)
      (volume.restrict (EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (3 / 8) (-11 / 16))) ≤
      ENNReal.ofReal C * (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
        ENNReal.ofReal |w.toFun z| ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹ := by
  obtain ⟨L, hL, hmatrix⟩ := short_time_complex_lift_normalized_ellipticity Λ B hΛ hB
  obtain ⟨C₀, hC₀, hstep⟩ := EinsteinFull.SignedLocalMax.power_step_S (d + 2) (by omega)
  obtain ⟨C, hC, hmax⟩ :=
    EinsteinFull.SignedLocalMax.signed_local_max_L2 (d + 2) (by omega) hC₀ hstep L hL
  refine ⟨C, hC, fun A hA i ζ hζ w hw => hmax _ ?_ w hw⟩
  refine ⟨fun j k => ?_, ?_⟩
  · exact (short_time_continuous_lift_entry_continuous A i ζ
      (4 * Λ ^ 3 * (B ^ 2 + 1)) (4 * Λ) j k).measurable.aemeasurable
  · filter_upwards [ae_restrict_mem
      ((PDE.isOpen_euclideanBall (0 : PDE.Vec (d + 2)) 1).measurableSet.prod measurableSet_Ioc)]
        with z hz
    exact hmatrix _ (hA z hz) i ζ hζ


/-- The physical part of the normalized lift has the expected space-time
Jacobian. The time ellipticity factor improves the upper bound. -/
private theorem short_time_normalized_physical_energy {d : ℕ}
    (Λ q T : ℝ) (hΛ : 1 ≤ Λ) (hq : 0 < q)
    {X : ℝ × Vec d → ℂ}
    (hX : MemLp X 2 (volume.restrict
      (Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q))) :
    AEMeasurable (fun z : PDE.Vec d × ℝ =>
      X (T + 4 * Λ * q ^ 2 * z.2, q • z.1))
      (volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ Set.Icc (-1 : ℝ) 0)) ∧
    (∫⁻ z in PDE.euclideanBall (0 : PDE.Vec d) 1 ×ˢ Set.Icc (-1 : ℝ) 0,
      ENNReal.ofReal ‖X (T + 4 * Λ * q ^ 2 * z.2, q • z.1)‖ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((q ^ (d + 2))⁻¹) *
        ∫⁻ z in Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q,
          ENNReal.ofReal ‖X z‖ ^ (2 : ℝ) := by
  let U := PDE.euclideanBall (0 : PDE.Vec d) 1
  let I := Set.Icc (-1 : ℝ) 0
  let S := Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q
  let r := Real.sqrt (4 * Λ) * q
  have hr : 0 < r := mul_pos (Real.sqrt_pos.2 (by linarith)) hq
  have hr2 : r ^ 2 = 4 * Λ * q ^ 2 := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (by linarith)]
  let Ψ := PDE.Parabolic.Rescale.spaceMap (0 : PDE.Vec d) q
  let τ := PDE.Parabolic.Rescale.timeMap T r
  let F : PDE.Vec d × ℝ → ℝ × Vec d := fun z => (τ z.2, Ψ z.1)
  have hΨ := PDE.Parabolic.Rescale.spaceMap_measurableEmbedding (0 : PDE.Vec d) hq
  have hτ := PDE.Parabolic.Rescale.timeMap_measurableEmbedding T hr
  have hF : MeasurableEmbedding F :=
    (hτ.prodMap hΨ).comp MeasurableEquiv.prodComm.measurableEmbedding
  have hmap : (volume.restrict (U ×ˢ I)).map F =
      ENNReal.ofReal ((r ^ 2)⁻¹ * (q ^ d)⁻¹) •
        volume.restrict ((τ '' I) ×ˢ (Ψ '' U)) := by
    change (volume.restrict (U ×ˢ I)).map (Prod.map τ Ψ ∘ Prod.swap) = _
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict,
      ← Measure.map_map (hτ.prodMap hΨ).measurable measurable_swap,
      (Measure.measurePreserving_swap (μ := volume.restrict U)
        (ν := volume.restrict I)).map_eq,
      ← Measure.map_prod_map _ _ hτ.measurable hΨ.measurable,
      PDE.Parabolic.Rescale.map_restrict_timeMap T hr,
      PDE.Parabolic.Rescale.map_restrict_spaceMap (0 : PDE.Vec d) hq,
      Measure.prod_smul_left, Measure.prod_smul_right, smul_smul,
      ← ENNReal.ofReal_mul (by positivity), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  have hsub : (τ '' I) ×ˢ (Ψ '' U) ⊆ S := by
    rintro ⟨t, x⟩ ⟨⟨s, hs, rfl⟩, ⟨y, hy, rfl⟩⟩
    constructor
    · change T + r ^ 2 * s ∈ Set.Icc (T - 4 * Λ * q ^ 2) T
      rw [hr2]
      constructor <;> nlinarith [hs.1, hs.2]
    · apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt hq).2
      have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hy
      simpa [Ψ, PDE.Parabolic.Rescale.spaceMap, sub_zero,
        PDE.vecEuclideanNorm_smul, abs_of_pos hq] using mul_lt_mul_of_pos_left hx' hq
  have hXm : AEMeasurable X ((volume.restrict (U ×ˢ I)).map F) := by
    rw [hmap]
    exact (hX.aestronglyMeasurable.aemeasurable.mono_measure
      (Measure.restrict_mono hsub le_rfl)).smul_measure _
  have hcomp := hF.aemeasurable_map_iff.1 hXm
  have hcoeff : (r ^ 2)⁻¹ * (q ^ d)⁻¹ ≤ (q ^ (d + 2))⁻¹ := by
    rw [hr2]
    have hh : (4 * Λ * q ^ 2)⁻¹ ≤ (q ^ 2)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le (sq_pos_of_pos hq)
        (by nlinarith [sq_pos_of_pos hq] : q ^ 2 ≤ 4 * Λ * q ^ 2)
    calc
      _ ≤ (q ^ 2)⁻¹ * (q ^ d)⁻¹ := mul_le_mul_of_nonneg_right hh (by positivity)
      _ = _ := by rw [← mul_inv, mul_comm, ← pow_add]
  refine ⟨by simpa [Function.comp_def, F, τ, Ψ,
    PDE.Parabolic.Rescale.timeMap, PDE.Parabolic.Rescale.spaceMap, hr2] using hcomp, ?_⟩
  have hi : (∫⁻ z in U ×ˢ I, ENNReal.ofReal ‖X (F z)‖ ^ (2 : ℝ)) =
      ENNReal.ofReal ((r ^ 2)⁻¹ * (q ^ d)⁻¹) *
        ∫⁻ z in (τ '' I) ×ˢ (Ψ '' U), ENNReal.ofReal ‖X z‖ ^ (2 : ℝ) := by
    rw [← hF.lintegral_map (fun z => ENNReal.ofReal ‖X z‖ ^ (2 : ℝ)),
      hmap, lintegral_smul_measure]
    rfl
  have hi' := hi.le.trans (mul_le_mul'
    (ENNReal.ofReal_le_ofReal hcoeff) (lintegral_mono_set hsub))
  simpa [U, I, S, F, τ, Ψ, PDE.Parabolic.Rescale.timeMap,
    PDE.Parabolic.Rescale.spaceMap, hr2] using hi'

/-- Quantitative energy of the actual normalized exponential lift. The
constant precedes the ellipticity, scale, time, phase, and physical field. -/
theorem short_time_normalized_lift_energy (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ q T : ℝ), 1 ≤ Λ → 0 < q → q ≤ 1 →
    ∀ e : ℂ, ‖e‖ ≤ 1 → ∀ X : ℝ × Vec d → ℂ,
    MemLp X 2 (volume.restrict
      (Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q)) →
    let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
      (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re
    (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
      ENNReal.ofReal |v z| ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C / q ^ (d + 2)) *
        ∫⁻ z in Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q,
          ENNReal.ofReal ‖X z‖ ^ (2 : ℝ) := by
  let V := PDE.euclideanBall (0 : PDE.Vec 2) 1
  let C := (Real.exp 1) ^ 2 * ((volume V).toReal + 1)
  have hVfin : volume V ≠ ⊤ := PDE.volume_euclideanBall_ne_top _ (by norm_num)
  have hC : 0 < C := mul_pos (sq_pos_of_pos (Real.exp_pos _)) (by positivity)
  refine ⟨C, hC, fun Λ q T hΛ hq hq1 e he X hX => ?_⟩
  let U := PDE.euclideanBall (0 : PDE.Vec d) 1
  let I := Set.Icc (-1 : ℝ) 0
  let E := (PDE.vecAppendEquiv d 2 ⁻¹' (U ×ˢ V)) ×ˢ I
  let G : PDE.Vec d × ℝ → ℂ := fun z => X (T + 4 * Λ * q ^ 2 * z.2, q • z.1)
  obtain ⟨hG, henergy⟩ := short_time_normalized_physical_energy Λ q T hΛ hq hX
  have hU : MeasurableSet U := (PDE.isOpen_euclideanBall _ _).measurableSet
  have hV : MeasurableSet V := (PDE.isOpen_euclideanBall _ _).measurableSet
  have hE : MeasurableSet E :=
    ((hU.prod hV).preimage (PDE.vecAppendEquiv d 2).continuous.measurable).prod measurableSet_Icc
  have hsplit := short_time_lift_spacetime_measurePreserving hU hV (I := I)
  have hg : AEMeasurable (fun z : PDE.Vec d × ℝ => ENNReal.ofReal ‖G z‖ ^ (2 : ℝ))
      (volume.restrict (U ×ˢ I)) := hG.norm.ennreal_ofReal.pow_const _
  have hprod : (∫⁻ z in E, ENNReal.ofReal ‖G
      ((PDE.vecAppendEquiv d 2 z.1).1, z.2)‖ ^ (2 : ℝ)) =
      (∫⁻ z in U ×ˢ I, ENNReal.ofReal ‖G z‖ ^ (2 : ℝ)) * volume V := by
    calc
      _ = ∫⁻ z, ENNReal.ofReal ‖G z.1‖ ^ (2 : ℝ)
          ∂(volume.restrict (U ×ˢ I)).prod (volume.restrict V) :=
        hsplit.lintegral_comp_emb (shortTimeLiftSpacetimeHomeomorph d).measurableEmbedding _
      _ = _ := by
        simpa only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ] using
          (lintegral_prod_mul (μ := volume.restrict (U ×ˢ I)) (ν := volume.restrict V)
            hg (aemeasurable_const (b := (1 : ℝ≥0∞))))
  have hsub : EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4) ⊆ E := by
    intro z hz
    exact ⟨PDE.euclideanBall_subset_preimage_vecAppendEquiv_prod d 2 (by norm_num)
      (PDE.euclideanBall_mono (by norm_num) (by norm_num) hz.1),
      ⟨by linarith [hz.2.1], le_of_lt hz.2.2⟩⟩
  have hb : ∀ z ∈ E,
      |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          G ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re| ≤
      Real.exp 1 * ‖G ((PDE.vecAppendEquiv d 2 z.1).1, z.2)‖ := by
    intro z hz
    have hy := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hz.1.2
    have hc := PDE.abs_apply_le_vecEuclideanNorm (PDE.vecAppendEquiv d 2 z.1).2 (0 : Fin 2)
    have hcoord : z.1 (Fin.natAdd d (0 : Fin 2)) ≤ 1 := by
      exact (le_abs_self _).trans ((hc.trans_lt (by simpa [sub_zero] using hy)).le)
    have hqcoord : q * z.1 (Fin.natAdd d (0 : Fin 2)) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hcoord hq.le).trans (by simpa using hq1)
    calc
      _ ≤ ‖Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
          q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          G ((PDE.vecAppendEquiv d 2 z.1).1, z.2)‖ := Complex.abs_re_le_norm _
      _ ≤ _ := by
        rw [norm_mul, norm_mul, Complex.norm_exp]
        exact mul_le_mul_of_nonneg_right
          ((mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hqcoord) (norm_nonneg _)).trans
            (by simpa using mul_le_mul_of_nonneg_left he (Real.exp_pos 1).le)) (norm_nonneg _)
  have hi := (lintegral_mono_set (μ := volume) (f := fun z : PDE.Vec (d + 2) × ℝ =>
      ENNReal.ofReal |(Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          G ((PDE.vecAppendEquiv d 2 z.1).1, z.2)).re| ^ (2 : ℝ)) hsub).trans
    (lintegral_mono_ae (by
      filter_upwards [ae_restrict_mem hE] with z hz
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (hb z hz)) (by norm_num)))
  simp_rw [ENNReal.ofReal_mul (Real.exp_pos 1).le, ENNReal.mul_rpow_of_nonneg _ _ (show (0 : ℝ) ≤ 2 by norm_num),
    ENNReal.rpow_two (ENNReal.ofReal (Real.exp 1))] at hi
  rw [lintegral_const_mul' _ _ (by finiteness), hprod] at hi
  have hv : volume V ≤ ENNReal.ofReal ((volume V).toReal + 1) := by
    calc
      _ = ENNReal.ofReal (volume V).toReal := (ENNReal.ofReal_toReal hVfin).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
  have hlast := mul_le_mul' (le_refl (ENNReal.ofReal (Real.exp 1) ^ 2))
    (mul_le_mul' henergy hv)
  have hcoef : ENNReal.ofReal (Real.exp 1) ^ 2 *
      (ENNReal.ofReal ((q ^ (d + 2))⁻¹) * ENNReal.ofReal ((volume V).toReal + 1)) =
      ENNReal.ofReal (C / q ^ (d + 2)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos 1).le,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [C]
    ring
  have hfinal := hi.trans hlast
  convert hfinal using 1
  rw [← hcoef]
  ac_rfl

/-- The same normalized lift is controlled by the Gaussian-weighted physical
energy on the full spatial slab, without a global integrability premise. -/
theorem short_time_normalized_lift_gaussian_energy (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ q T L : ℝ), 1 ≤ Λ → 0 < q → q ≤ 1 → 0 < L →
    ∀ e : ℂ, ‖e‖ ≤ 1 → ∀ X : ℝ × Vec d → ℂ,
    MemLp X 2 (volume.restrict
      (Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q)) →
    let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
      (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re
    (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
      ENNReal.ofReal |v z| ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C * Real.exp (2 * q ^ 2 / L) / q ^ (d + 2)) *
        ∫⁻ z in Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ (Set.univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖X z‖ ^ 2) := by
  obtain ⟨C, hC, henergy⟩ := short_time_normalized_lift_energy d
  refine ⟨C, hC, fun Λ q T L hΛ hq hq1 hL e he X hX => ?_⟩
  let S := Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q
  let W : ℝ × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖X z‖ ^ 2)
  have hS : MeasurableSet S :=
    measurableSet_Icc.prod (PDE.isOpen_euclideanBall _ _).measurableSet
  have hbound : ∀ z ∈ S, ENNReal.ofReal ‖X z‖ ^ (2 : ℝ) ≤
      ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * W z := by
    intro z hz
    have hs : euclideanSq z.2 ≤ q ^ 2 := by
      have hb := hz.2
      change PDE.vecNormSq (z.2 - 0) < q ^ 2 at hb
      simpa only [sub_zero, PDE.vecNormSq, PDE.vecDot, euclideanSq, dot] using hb.le
    have hratio : euclideanSq z.2 / L ≤ 2 * q ^ 2 / L :=
      div_le_div_of_nonneg_right (by nlinarith [sq_nonneg q]) hL.le
    have hone : 1 ≤ Real.exp (2 * q ^ 2 / L) * Real.exp (-euclideanSq z.2 / L) := by
      rw [← Real.exp_add, ← Real.exp_zero]
      exact Real.exp_le_exp.2 (by
        simpa only [neg_div, sub_eq_add_neg] using sub_nonneg.2 hratio)
    have hn := mul_le_mul_of_nonneg_right hone (sq_nonneg ‖X z‖)
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
    dsimp only [W]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul, mul_assoc] using hn)
  have hlocal := lintegral_mono_ae (μ := volume.restrict S) (by
    filter_upwards [ae_restrict_mem hS] with z hz
    exact hbound z hz)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hlocal
  have hsub : S ⊆ Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ (Set.univ : Set (Vec d)) :=
    fun _ hz => ⟨hz.1, Set.mem_univ _⟩
  have hw := hlocal.trans (mul_le_mul' le_rfl (lintegral_mono_set (f := W) hsub))
  have hfinal := (henergy Λ q T hΛ hq hq1 e he X hX).trans
    (mul_le_mul' le_rfl hw)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hfinal
  convert hfinal using 1
  congr 2
  ring

/-- Local equality to the actual residual suffices for Gaussian energy
transport. The primitive may be extended by zero at negative times; no
equality outside the physical ball or global integrability is required. -/
theorem short_time_zero_extended_local_gaussian_energy {d : ℕ}
    (A T q L : ℝ) (hT : T ≤ 1) (hL : 0 < L)
    (X Y : ℝ × Vec d → ℂ) (hX : Measurable X) (hY : Measurable Y)
    (hzero : ∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0)
    (hlocal : ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (fun x => X (s, x)) =ᵐ[volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) q)]
        (fun x => Y (s, x))) :
    (∫⁻ z in Set.Icc A T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q,
      ENNReal.ofReal ‖X z‖ ^ (2 : ℝ)) ≤
      ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) *
        ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖Y z‖ ^ 2) := by
  let S := Set.Icc A T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q
  let H := Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec d))
  let W : ℝ × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖Y z‖ ^ 2)
  have hH : MeasurableSet H := measurableSet_Icc.prod MeasurableSet.univ
  have hW : Measurable W := by
    exact ((by dsimp only [euclideanSq, dot]; fun_prop :
      Measurable (fun z : ℝ × Vec d => Real.exp (-euclideanSq z.2 / L))).mul
        (hY.norm.pow_const 2)).ennreal_ofReal
  have hb : ∀ᵐ z ∂volume.restrict S, ENNReal.ofReal ‖X z‖ ^ (2 : ℝ) ≤
      ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * H.indicator W z := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le
      (hX.norm.ennreal_ofReal.pow_const _) (measurable_const.mul (hW.indicator hH)))).mpr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    by_cases hs0 : s ≤ 0
    · exact ae_of_all _ fun x => by simp only [hzero s hs0 x, norm_zero,
        ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]; exact bot_le
    · filter_upwards [hlocal s (le_of_not_ge hs0) (hs.2.trans hT),
        ae_restrict_mem (PDE.isOpen_euclideanBall (0 : PDE.Vec d) q).measurableSet] with x he hx
      have hsq : euclideanSq x ≤ q ^ 2 := by
        change PDE.vecNormSq (x - 0) < q ^ 2 at hx
        simpa only [sub_zero, PDE.vecNormSq, PDE.vecDot, euclideanSq, dot] using hx.le
      have hratio : euclideanSq x / L ≤ 2 * q ^ 2 / L :=
        div_le_div_of_nonneg_right (by nlinarith [sq_nonneg q]) hL.le
      have hone : 1 ≤ Real.exp (2 * q ^ 2 / L) * Real.exp (-euclideanSq x / L) := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_le_exp.2 (by
          simpa only [neg_div, sub_eq_add_neg] using sub_nonneg.2 hratio)
      have hn := mul_le_mul_of_nonneg_right hone (sq_nonneg ‖Y (s, x)‖)
      change ENNReal.ofReal ‖X (s, x)‖ ^ (2 : ℝ) ≤
        ENNReal.ofReal (Real.exp (2 * q ^ 2 / L)) * H.indicator W (s, x)
      rw [Set.indicator_of_mem (show (s, x) ∈ H from
        ⟨⟨le_of_not_ge hs0, hs.2.trans hT⟩, Set.mem_univ _⟩), he,
        ENNReal.rpow_two, ← ENNReal.ofReal_pow (norm_nonneg _)]
      dsimp only [W]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal (by simpa only [one_mul, mul_assoc] using hn)
  have hi := lintegral_mono_ae hb
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hi
  have hfull : (∫⁻ z in S, H.indicator W z) ≤ ∫⁻ z in H, W z := by
    calc
      _ ≤ ∫⁻ z, H.indicator W z := by
        simpa only [Measure.restrict_univ] using
          (lintegral_mono_set (μ := volume) (f := H.indicator W) (Set.subset_univ S))
      _ = _ := lintegral_indicator hH W
  exact hi.trans (mul_le_mul' le_rfl hfull)

/-- Gaussian control of the same normalized lift using only local equality
to the actual residual. The right side uses that actual residual, rather
than identifying its primitive outside the retained region. -/
theorem short_time_normalized_lift_local_residual_gaussian_energy (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ q T L : ℝ), 1 ≤ Λ → 0 < q → q ≤ 1 → T ≤ 1 → 0 < L →
    ∀ e : ℂ, ‖e‖ ≤ 1 → ∀ X Y : ℝ × Vec d → ℂ,
    Measurable X → Measurable Y →
    (∀ s : ℝ, s ≤ 0 → ∀ x, X (s, x) = 0) →
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 →
      (fun x => X (s, x)) =ᵐ[volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) q)]
        (fun x => Y (s, x))) →
    MemLp X 2 (volume.restrict
      (Set.Icc (T - 4 * Λ * q ^ 2) T ×ˢ PDE.euclideanBall (0 : PDE.Vec d) q)) →
    let v : PDE.Vec (d + 2) × ℝ → ℝ := fun z =>
      (Complex.exp ⟨q * z.1 (Fin.natAdd d (0 : Fin 2)),
        q * z.1 (Fin.natAdd d (1 : Fin 2))⟩ * e *
          X (T + 4 * Λ * q ^ 2 * z.2, q • (PDE.vecAppendEquiv d 2 z.1).1)).re
    (∫⁻ z in EinsteinFull.SignedLocalMax.moserCylZ (d + 2) (1 / 2) (-3 / 4),
      ENNReal.ofReal |v z| ^ (2 : ℝ)) ≤
      ENNReal.ofReal (C * Real.exp (2 * q ^ 2 / L) / q ^ (d + 2)) *
        ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ (Set.univ : Set (Vec d)),
          ENNReal.ofReal (Real.exp (-euclideanSq z.2 / L) * ‖Y z‖ ^ 2) := by
  obtain ⟨C, hC, henergy⟩ := short_time_normalized_lift_energy d
  refine ⟨C, hC, fun Λ q T L hΛ hq hq1 hT hL e he X Y hX hY hzero hlocal hX2 => ?_⟩
  have hw := short_time_zero_extended_local_gaussian_energy
    (T - 4 * Λ * q ^ 2) T q L hT hL X Y hX hY hzero hlocal
  have hf := (henergy Λ q T hΛ hq hq1 e he X hX2).trans (mul_le_mul' le_rfl hw)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)] at hf
  convert hf using 1
  congr 2
  ring

/-- Gaussian-weighted strong continuity of the same stationary primitive.
The event precedes every Gaussian width and every short time, allowing
rational-time comparison events to be extended without changing representatives. -/
theorem short_time_stationary_primitive_gaussian_strong_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      (∀ t ∈ Icc (0 : ℝ) 1,
        MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) *
          F (t, translate x ω)) 2 volume) ∧
      ∀ a ∈ Icc (0 : ℝ) 1,
        Tendsto (fun t => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - F (a, translate x ω)‖ ^ 2)
          (𝓝[Icc (0 : ℝ) 1] a) (𝓝 0) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hI : Integrable (fun p => ‖U p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (reducedLaw Q)) :=
    integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp continuous_real_toNNReal).norm.pow 2).continuousOn.integrableOn_compact
        isCompact_Icc) hU heU
  filter_upwards [ae_stationary_spacetime_orbit_gaussian_memLp d hd (reducedLaw Q)
    (reducedLaw_stationary Q) 1 zero_le_one U hU hI,
    ae_stationary_spatial_orbit_gaussian_memLp d hd (reducedLaw Q)
      (reducedLaw_stationary Q) f] with ω hω hfω
  intro L hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let D : ℝ × Vec d → ℂ := fun p => w p.2 * U (p.1, translate p.2 ω)
  have hw : Measurable w := by
    dsimp only [w, euclideanSq, dot]
    fun_prop
  have hD : Measurable D :=
    (hw.comp measurable_snd).mul (hU.comp (measurable_fst.prodMk
      (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk measurable_const))))
  have hi : Integrable (fun p => ‖D p‖ ^ 2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    (hω L hL).norm.integrable_sq
  obtain ⟨hm, hc⟩ := short_time_local_primitive_continuous volume hD hi
  have he (t : ℝ) (x : Vec d) :
      w x * F (t, translate x ω) = w x * f (translate x ω) +
        ∫ s in Icc (0 : ℝ) t, D (s, x) := by
    dsimp only [D]
    rw [hprim, mul_add, integral_const_mul]
  refine ⟨?_, ?_⟩
  · intro t ht
    exact ((hfω L hL).add (hm t ht)).ae_eq
      (ae_of_all _ fun x => (he t x).symm)
  · intro a ha
    convert hc a ha using 1
    funext t
    apply integral_congr_ae
    filter_upwards with x
    have heq : w x * (F (t, translate x ω) - F (a, translate x ω)) =
        (∫ s in Icc (0 : ℝ) t, D (s, x)) -
          (∫ s in Icc (0 : ℝ) a, D (s, x)) := by
      rw [mul_sub, he, he, add_sub_add_left_eq_sub]
    rw [← heq, norm_mul, mul_pow]
    simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The squared norm of the complex L2 class is the literal square integral. -/
theorem short_time_complex_L2_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [Lp.norm_toLp]
  simpa only [ENNReal.ofReal_ofNat, Real.rpow_two] using
    PDE.toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm (p := (2 : ℝ))
      (by norm_num) (by simpa only [ENNReal.ofReal_ofNat] using hf)

/-- A bounded Gaussian multiplier preserves physical L2 membership. -/
theorem short_time_gaussian_weight_memLp {d : ℕ} (L : ℝ) (hL : 0 < L)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    MemLp (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * f x) 2 volume := by
  have hw : Measurable (fun x : Vec d => (Real.exp (-euclideanSq x / L) : ℂ)) := by
    dsimp only [euclideanSq, dot]
    fun_prop
  apply (Lp.memLp f).of_le_mul (c := 1)
    (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖(Real.exp (-euclideanSq x / L) : ℂ) * f x‖ ≤ 1 * ‖f x‖
  have hsq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr
      hsq) hL.le))

/-- Multiplication by the same Gaussian contracts the physical L2 distance. -/
theorem short_time_gaussian_weight_lipschitz {d : ℕ} (L : ℝ) (hL : 0 < L) :
    LipschitzWith 1 (fun f : Lp ℂ 2 (volume : Measure (Vec d)) =>
      (short_time_gaussian_weight_memLp L hL f).toLp
        (fun x => (Real.exp (-euclideanSq x / L) : ℂ) * f x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub
    ((short_time_gaussian_weight_memLp L hL f).toLp _)
    ((short_time_gaussian_weight_memLp L hL g).toLp _),
    (short_time_gaussian_weight_memLp L hL f).coeFn_toLp,
    (short_time_gaussian_weight_memLp L hL g).coeFn_toLp,
    Lp.coeFn_sub f g] with x hs hf hg hfg
  rw [hs, hfg]
  change ‖((short_time_gaussian_weight_memLp L hL f).toLp _) x -
    ((short_time_gaussian_weight_memLp L hL g).toLp _) x‖ ≤ ‖f x - g x‖
  have hsq : 0 ≤ euclideanSq x := by
    change 0 ≤ ∑ j : Fin d, x j * x j
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rw [hf, hg, ← mul_sub, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr hsq) hL.le))

/-- The Gaussian energy of the actual stationary primitive minus any physical
semigroup representative is continuous through every short time. The sample
event is chosen before the width, retained semigroup, datum, and representative. -/
theorem short_time_stationary_physical_gaussian_energy_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      ∀ (a : Vec d → Mat d)
        (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup a i ζ Pr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) →
      ContinuousOn (fun t : ℝ => ∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2) (Icc (0 : ℝ) 1) := by
  filter_upwards [short_time_stationary_primitive_gaussian_strong_continuous
    hd Q hP f g F U hU heU hprim] with ω hω
  intro L hL a Pr hPr fr V heV
  obtain ⟨hFm, hFc⟩ := hω L hL
  let w : Vec d → ℂ := fun x => (Real.exp (-euclideanSq x / L) : ℂ)
  let H : Icc (0 : ℝ) 1 → Lp ℂ 2 (volume : Measure (Vec d)) := fun t =>
    (hFm t t.property).toLp (fun x => w x * F (t, translate x ω))
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun s : Icc (0 : ℝ) 1 => fun x => w x * F (s, translate x ω))
      (fun s => hFm s s.property) _ (hFm t t.property)).mpr
    have hc := (tendsto_nhdsWithin_iff_subtype t.property _ _).mp (hFc t t.property)
    have hc' : Tendsto (fun s : Icc (0 : ℝ) 1 => ∫ x,
        ‖w x * F (s, translate x ω) - w x * F (t, translate x ω)‖ ^ 2)
        (𝓝 t) (𝓝 0) := by
      convert hc using 1
      funext s
      apply integral_congr_ae
      filter_upwards with x
      rw [← mul_sub, norm_mul, mul_pow]
      simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he := PDE.tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun s : Icc (0 : ℝ) 1 => ((hFm s s.property).sub (hFm t t.property)).norm) hc'
    convert he using 1
    funext s
    exact (eLpNorm_norm _ ((hFm s s.property).sub (hFm t t.property)).aestronglyMeasurable).symm
  let W : Lp ℂ 2 (volume : Measure (Vec d)) → Lp ℂ 2 (volume : Measure (Vec d)) :=
    fun u => (short_time_gaussian_weight_memLp L hL u).toLp (fun x => w x * u x)
  have hW : Continuous W := (short_time_gaussian_weight_lipschitz L hL).continuous
  have hR : Continuous (fun t : Icc (0 : ℝ) 1 => H t - W (Pr t.val.toNNReal fr)) :=
    hH.sub (hW.comp (((hPr.2.2.1 fr).comp continuous_real_toNNReal).comp
      continuous_subtype_val))
  apply continuousOn_iff_continuous_domRestrict.mpr
  convert hR.norm.pow 2 using 1
  funext t
  let G : Vec d → ℂ := fun x => w x * F (t, translate x ω) - w x * (Pr t.val.toNNReal fr) x
  have hmG : MemLp G 2 volume := (hFm t t.property).sub
    (short_time_gaussian_weight_memLp L hL (Pr t.val.toNNReal fr))
  have heG : H t - W (Pr t.val.toNNReal fr) = hmG.toLp G :=
    ((hFm t t.property).toLp_sub
      (short_time_gaussian_weight_memLp L hL (Pr t.val.toNNReal fr))).symm
  change (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
    ‖F (t, translate x ω) - V (t, x)‖ ^ 2) = ‖H t - W (Pr t.val.toNNReal fr)‖ ^ 2
  rw [heG, short_time_complex_L2_sq hmG]
  apply integral_congr_ae
  filter_upwards [heV t] with x hx
  dsimp only [G]
  rw [← hx, ← mul_sub, norm_mul, mul_pow]
  simp only [w, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The same actual residual has finite Gaussian energy at every short time.
Its nonnegative integral agrees with the real energy and is continuous, on an
event chosen before all widths and retained physical semigroups. -/
theorem short_time_stationary_physical_gaussian_lintegral_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f g : Lp ℂ 2 (reducedLaw Q)) (F U : ℝ × FieldPair d → ℂ)
    (hU : Measurable U)
    (heU : ∀ s, (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] P s.toNNReal g)
    (hprim : ∀ s ω, F (s, ω) = f ω + ∫ v in Icc (0 : ℝ) s, U (v, ω)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ L : ℝ, 0 < L →
      ∀ (a : Vec d → Mat d)
        (Pr : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
          Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalComplexSemigroup a i ζ Pr →
      ∀ (fr : Lp ℂ 2 (volume : Measure (Vec d))) (V : ℝ × Vec d → ℂ),
      (∀ s, (fun x => V (s, x)) =ᵐ[volume] Pr s.toNNReal fr) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) volume ∧
        (∫⁻ x, ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) =
          ENNReal.ofReal (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
            ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) ∧
      ContinuousOn (fun t : ℝ => ∫⁻ x,
        ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) (Icc (0 : ℝ) 1) := by
  filter_upwards [short_time_stationary_primitive_gaussian_strong_continuous
    hd Q hP f g F U hU heU hprim,
    short_time_stationary_physical_gaussian_energy_continuous
      hd Q hP f g F U hU heU hprim] with ω hω hcω
  intro L hL a Pr hPr fr V heV
  have hi (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      Integrable (fun x => Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2) volume := by
    have hm := ((hω L hL).1 t ht).sub
      (short_time_gaussian_weight_memLp L hL (Pr t.toNNReal fr))
    apply hm.norm.integrable_sq.congr
    filter_upwards [heV t] with x hx
    change ‖(Real.exp (-euclideanSq x / L) : ℂ) * F (t, translate x ω) -
      (Real.exp (-euclideanSq x / L) : ℂ) * (Pr t.toNNReal fr) x‖ ^ 2 = _
    rw [← hx, ← mul_sub, norm_mul, mul_pow]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have he (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫⁻ x, ENNReal.ofReal (Real.exp (-euclideanSq x / L) ^ 2 *
        ‖F (t, translate x ω) - V (t, x)‖ ^ 2)) =
        ENNReal.ofReal (∫ x, Real.exp (-euclideanSq x / L) ^ 2 *
          ‖F (t, translate x ω) - V (t, x)‖ ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal (hi t ht)
      (ae_of_all _ fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))).symm
  refine ⟨fun t ht => ⟨hi t ht, he t ht⟩, ?_⟩
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (hcω L hL a Pr hPr fr V heV)).congr he

/-- A family of continuous short-time bounds admits one sample event for all
times, even when its parameter set is uncountable. No measurable choice of
parameters is required. -/
theorem short_time_continuous_bound_common_event {Ω α : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (E : Ω → α → ℝ → ℝ) (M : Ω → α → ℝ)
    (hc : ∀ᵐ ω ∂μ, ∀ a, ContinuousOn (E ω a) (Icc (0 : ℝ) 1))
    (hb : ∀ t ∈ Icc (0 : ℝ) 1, ∀ᵐ ω ∂μ, ∀ a, E ω a t ≤ M ω a) :
    ∀ᵐ ω ∂μ, ∀ a, ∀ t ∈ Icc (0 : ℝ) 1, E ω a t ≤ M ω a := by
  let : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, by simp⟩⟩
  let s : ℕ → Icc (0 : ℝ) 1 := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  filter_upwards [hc, ae_all_iff.mpr (fun n => hb (s n) (s n).property)]
    with ω hcω hbω
  intro a t ht
  exact hs.induction_on (p := fun z : Icc (0 : ℝ) 1 => E ω a z ≤ M ω a) ⟨t, ht⟩
    (isClosed_le (continuousOn_iff_continuous_domRestrict.mp (hcω a)) continuous_const)
    (fun n => hbω n a)

/-- A spacetime essential bound passes to every strong spatial `L²` trace,
including both time endpoints. The field is the supplied representative. -/
theorem short_time_L2_trace_bound {S : Type*} [MeasurableSpace S]
    (μ : Measure S) {a b M : ℝ} (hab : a < b) (hM : 0 ≤ M)
    (F : ℝ × S → ℂ)
    (hm : ∀ t ∈ Icc a b, MemLp (fun x => F (t, x)) 2 μ)
    (hc : ∀ s ∈ Icc a b,
      Tendsto (fun t => ∫ x, ‖F (t, x) - F (s, x)‖ ^ 2 ∂μ)
        (𝓝[Icc a b] s) (𝓝 0))
    (hb : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂μ, ‖F (t, x)‖ ≤ M) :
    ∀ t ∈ Icc a b, ∀ᵐ x ∂μ, ‖F (t, x)‖ ≤ M := by
  let H : Icc a b → Lp ℂ 2 μ := fun t => (hm t t.property).toLp (fun x => F (t, x))
  have hH : Continuous H := by
    apply continuous_iff_continuousAt.mpr
    intro s
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm''
      (fun t : Icc a b => fun x => F (t, x))
      (fun t => hm t t.property) _ (hm s s.property)).mpr
    have hlim := (tendsto_nhdsWithin_iff_subtype s.property _ _).mp (hc s s.property)
    have he := PDE.tendsto_eLpNorm_two_zero_of_tendsto_integral_sq
      (fun t : Icc a b => ((hm t t.property).sub (hm s s.property)).norm) hlim
    convert he using 1
    funext t
    exact (eLpNorm_norm _ ((hm t t.property).sub (hm s s.property)).aestronglyMeasurable).symm
  let g : ℂ → ℝ := fun z => max (‖z‖ - M) 0
  have hg : LipschitzWith 1 g := by
    have hl : LipschitzWith 1 (fun z : ℂ => ‖z‖ - M) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simpa only [dist_sub_right] using
        (lipschitzWith_one_norm : LipschitzWith 1 (norm : ℂ → ℝ)).dist_le_mul z w
    exact hl.max_const 0
  have hg0 : g 0 = 0 := by simp [g, hM]
  let G : Lp ℂ 2 μ → Lp ℝ 2 μ := hg.compLp hg0
  let E : ℝ → ℝ := fun t => if ht : t ∈ Icc a b then ‖G (H ⟨t, ht⟩)‖ else 0
  have hE : ContinuousOn E (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    convert ((hg.continuous_compLp hg0).comp hH).norm using 1
    funext t
    simp only [Set.domRestrict_apply, E, dite_eq_left t.property, G, Function.comp_apply]
  have hrep (t : Icc a b) : G (H t) =ᵐ[μ] fun x => g (F (t, x)) := by
    filter_upwards [hg.coeFn_compLp hg0 (H t), (hm t t.property).coeFn_toLp] with x hx hy
    simpa only [Function.comp_apply, H, hy] using hx
  have hz : E =ᵐ[volume.restrict (Icc a b)] fun _ => 0 := by
    filter_upwards [hb, ae_restrict_mem measurableSet_Icc] with t ht hti
    have hzero : G (H ⟨t, hti⟩) = 0 := by
      apply Lp.eq_zero_iff_ae_eq_zero.mpr
      filter_upwards [hrep ⟨t, hti⟩, ht] with x hx hbound
      simpa only [Pi.zero_apply, g, max_eq_right (sub_nonpos.mpr hbound)] using hx
    simp only [E, dite_eq_left hti, hzero, norm_zero]
  have hall := Measure.eqOn_Icc_of_ae_eq volume hab.ne hz hE continuousOn_const
  intro t ht
  have hzero : G (H ⟨t, ht⟩) = 0 := by
    apply norm_eq_zero.mp
    simpa only [E, dite_eq_left ht] using hall ht
  filter_upwards [hrep ⟨t, ht⟩, Lp.eq_zero_iff_ae_eq_zero.mp hzero] with x hx hy
  have hgx : max (‖F (t, x)‖ - M) 0 = 0 := hx.symm.trans hy
  have := le_max_left (‖F (t, x)‖ - M) 0
  linarith [hgx]

/-- Spatial averages of the actual stationary translation action are continuous
in the dilation parameter, for every finite averaging measure. -/
theorem short_time_stationary_average_continuous {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] (f : Lp ℂ 2 Q) :
    Continuous (fun r : ℝ => ⨍ x, complexTranslation Q hQ (r • x) f ∂ν) := by
  have hT : Continuous (fun x : Vec d => complexTranslation Q hQ x f) :=
    (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
  have hI : Continuous (fun r : ℝ => ∫ x, complexTranslation Q hQ (r • x) f ∂ν) := by
    apply continuous_of_dominated (μ := ν)
      (F := fun (r : ℝ) (x : Vec d) => complexTranslation Q hQ (r • x) f)
      (bound := fun _ => ‖f‖)
    · intro r
      have hs : Continuous (fun x : Vec d => r • x) := continuous_const_smul r
      exact (hT.comp hs).aestronglyMeasurable
    · intro r
      exact ae_of_all _ fun x => (norm_complexTranslation Q hQ (r • x) f).le
    · exact integrable_const _
    · apply ae_of_all
      intro x
      have hs : Continuous (fun r : ℝ => r • x) := continuous_id.smul continuous_const
      exact hT.comp hs
  simp only [average_eq]
  exact hI.const_smul (ν.real univ)⁻¹

/-- Shrinking stationary spatial averages recover the original environment L²
class. The spatial measure can in particular be volume on a fixed finite ball. -/
theorem short_time_stationary_average_tendsto {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] [NeZero ν] (f : Lp ℂ 2 Q) :
    Tendsto (fun r : ℝ => ⨍ x, complexTranslation Q hQ (r • x) f ∂ν)
      (𝓝 0) (𝓝 f) := by
  simpa only [zero_smul, complexTranslation_zero, average_const] using
    (short_time_stationary_average_continuous Q hQ ν f).tendsto 0

/-- The L² average is represented by the literal spatial average of the same
stationary field, with no pointwise representative or choice of continuous version. -/
theorem short_time_stationary_average_representative {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] (f : Lp ℂ 2 Q) (r : ℝ) :
    (⨍ x, complexTranslation Q hQ (r • x) f ∂ν : Lp ℂ 2 Q) =ᵐ[Q]
      (fun ω => ⨍ x, f (translate (r • x) ω) ∂ν) ∧
    MemLp (fun ω => ⨍ x, f (translate (r • x) ω) ∂ν) 2 Q := by
  have hs : Continuous (fun x : Vec d => r • x) := continuous_const_smul r
  have hT : Continuous (fun x : Vec d => complexTranslation Q hQ (r • x) f) :=
    (continuous_complexTranslation Q hQ).comp (hs.prodMk continuous_const)
  have hI : Integrable (fun x => complexTranslation Q hQ (r • x) f) ν := by
    apply (integrable_const ‖f‖).mono' hT.aestronglyMeasurable
    exact ae_of_all _ fun x => (norm_complexTranslation Q hQ (r • x) f).le
  have hsm : Measurable (fun p : Vec d × FieldPair d => r • p.1) :=
    hs.measurable.comp measurable_fst
  have hm : Measurable (fun p : Vec d × FieldPair d => f (translate (r • p.1) p.2)) :=
    (Lp.stronglyMeasurable f).measurable.comp
      (Probability.continuous_translate.measurable.comp (hsm.prodMk measurable_snd))
  have hf : Integrable (f : FieldPair d → ℂ) Q := (Lp.memLp f).integrable (by norm_num)
  have hg : Integrable (fun p : Vec d × FieldPair d => f (translate (r • p.1) p.2))
      (ν.prod Q) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun x => ?_), ?_⟩
    · exact ((measurePreserving_translate Q hQ (r • x)).integrable_comp
        (Lp.stronglyMeasurable f).aestronglyMeasurable).mpr hf
    · have he : (fun x : Vec d => ∫ ω, ‖f (translate (r • x) ω)‖ ∂Q) =
          fun _ => ∫ ω, ‖f ω‖ ∂Q := by
        funext x
        exact Probability.integral_translate Q hQ (r • x) (fun ω => ‖f ω‖)
          (Lp.stronglyMeasurable f).measurable.norm
      rw [he]
      exact integrable_const _
  have he := EinsteinFull.Calculus.C2TestReplacement.coeFn_integral_lp_ae ν Q
    (fun x => complexTranslation Q hQ (r • x) f)
    (fun p => f (translate (r • p.1) p.2)) hI hg
    (fun x => coeFn_complexTranslation Q hQ (r • x) f)
  have ha : (⨍ x, complexTranslation Q hQ (r • x) f ∂ν : Lp ℂ 2 Q) =ᵐ[Q]
      (fun ω => ⨍ x, f (translate (r • x) ω) ∂ν) := by
    simp only [average_eq]
    filter_upwards [Lp.coeFn_smul (ν.real univ)⁻¹
      (∫ x, complexTranslation Q hQ (r • x) f ∂ν), he] with ω hω heω
    rw [hω]
    simp only [Pi.smul_apply, heω]
  refine ⟨ha, ?_⟩
  exact (memLp_congr_ae ha).mp (Lp.memLp
    (⨍ x, complexTranslation Q hQ (r • x) f ∂ν : Lp ℂ 2 Q))

/-- Along a subsequence of any shrinking scales, the literal spatial averages
of the same stationary field converge on one environment event to that field. -/
theorem short_time_stationary_average_subsequence {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν] [NeZero ν] (f : Lp ℂ 2 Q)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂Q,
      Tendsto (fun n => ⨍ x, f (translate (r (φ n) • x) ω) ∂ν) atTop (𝓝 (f ω)) := by
  let A : ℕ → Lp ℂ 2 Q := fun n => ⨍ x, complexTranslation Q hQ (r n • x) f ∂ν
  have ht : Tendsto A atTop (𝓝 f) :=
    (short_time_stationary_average_tendsto Q hQ ν f).comp hr
  obtain ⟨φ, hφ, hconv⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  have he : ∀ᵐ ω ∂Q, ∀ n : ℕ,
      A n ω = ⨍ x, f (translate (r n • x) ω) ∂ν :=
    ae_all_iff.mpr fun n => (short_time_stationary_average_representative Q hQ ν f (r n)).1
  refine ⟨φ, hφ, ?_⟩
  filter_upwards [hconv, he] with ω hω heω
  simpa only [heω] using hω

/-- A bound on almost every point of a stationary spatial orbit transfers to
its original environment representative by an inverse translation. -/
theorem short_time_origin_error_of_stationary_orbit_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f g : Lp ℂ 2 (reducedLaw Q)) {r ε : ℝ} (hr : 0 < r)
    (hbound : ∀ᵐ ω ∂reducedLaw Q,
      ∀ᵐ x ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) r),
        ‖f (translate x ω) - g (translate x ω)‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q, ‖f ω - g ω‖ ≤ ε := by
  let := reducedLaw_probability Q
  let ν : Measure (Vec d) := volume.restrict (PDE.euclideanBall (0 : PDE.Vec d) r)
  have hpos : volume (PDE.euclideanBall (0 : PDE.Vec d) r) ≠ 0 :=
    (PDE.isOpen_euclideanBall (0 : PDE.Vec d) r).measure_ne_zero volume
      ⟨0, by simpa only [PDE.euclideanBall, mem_ofPred_eq, PDE.euclideanSqDist_self]
        using sq_pos_of_pos hr⟩
  let : NeZero ν := ⟨by
    intro hzero
    apply hpos
    have hu := congrArg (fun m : Measure (Vec d) => m univ) hzero
    simpa [ν] using hu⟩
  have hm : Measurable (fun p : Vec d × FieldPair d =>
      f (translate p.1 p.2) - g (translate p.1 p.2)) :=
    ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable).sub
      ((Lp.stronglyMeasurable g).measurable.comp Probability.continuous_translate.measurable)
  have hswap : ∀ᵐ x ∂ν, ∀ᵐ ω ∂reducedLaw Q,
      ‖f (translate x ω) - g (translate x ω)‖ ≤ ε :=
    (Measure.ae_ae_comm (μ := ν) (ν := reducedLaw Q)
      (measurableSet_le hm.norm measurable_const)).mpr hbound
  obtain ⟨x, hx⟩ := hswap.exists
  have hinv := (measurePreserving_translate (reducedLaw Q)
    (reducedLaw_stationary Q) (-x)).quasiMeasurePreserving.ae hx
  filter_upwards [hinv] with ω hω
  simpa only [translate_add, add_neg_cancel, translate_zero] using hω

private theorem short_time_real_limsup_error {a b : ℕ → ℝ} {l ε : ℝ}
    (ha : Tendsto a atTop (𝓝 l)) (hab : ∀ n, |a n - b n| ≤ ε) :
    |l - limsup b atTop| ≤ ε := by
  have hlo : (fun n => a n - ε) ≤ᶠ[atTop] b :=
    Eventually.of_forall fun n => by have h := (abs_le.mp (hab n)).2; linarith
  have hhi : b ≤ᶠ[atTop] (fun n => a n + ε) :=
    Eventually.of_forall fun n => by have h := (abs_le.mp (hab n)).1; linarith
  have htl := ha.sub_const ε
  have htu := ha.add_const ε
  have hbb := htu.isBoundedUnder_le.mono_le hhi
  have hbl := htl.isBoundedUnder_ge.mono_ge hlo
  have hl := limsup_le_limsup hlo htl.isCoboundedUnder_le hbb
  have hu := limsup_le_limsup hhi hbl.isCoboundedUnder_le htu.isBoundedUnder_le
  rw [htl.limsup_eq] at hl
  rw [htu.limsup_eq] at hu
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Local approximations to shrinking averages produce an actual local L2
observation, without assuming convergence of the approximations themselves. -/
theorem short_time_local_observation_of_shrinking_averages
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (ρ : ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) (ν : Measure (Vec d)) [IsFiniteMeasure ν] [NeZero ν]
    (f : Lp ℂ 2 (reducedLaw Q)) (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (A : ℕ → FieldPair d → ℂ)
    (hA : ∀ n, Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (A n))
    (herr : ∀ n, ∀ᵐ ω ∂reducedLaw Q,
      ‖(⨍ x, f (translate (r n • x) ω) ∂ν) - A n ω‖ ≤ ε) :
    ∃ V : Lp ℂ 2 (reducedLaw Q), IsComplexLocalObservation Q ρ V ∧
      ∀ᵐ ω ∂reducedLaw Q, ‖f ω - V ω‖ ≤ 2 * ε := by
  let := reducedLaw_probability Q
  obtain ⟨φ, _hφ, hconv⟩ := short_time_stationary_average_subsequence
    (reducedLaw Q) (reducedLaw_stationary Q) ν f r hr
  let v : FieldPair d → ℂ := fun ω =>
    (limsup (fun n => (A (φ n) ω).re) atTop : ℝ) +
      (limsup (fun n => (A (φ n) ω).im) atTop : ℝ) * Complex.I
  have hvloc : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] v :=
    (Complex.measurable_ofReal.comp
      (.limsup fun n => Complex.measurable_re.comp (hA (φ n)))).add
      ((Complex.measurable_ofReal.comp
        (.limsup fun n => Complex.measurable_im.comp (hA (φ n)))).mul measurable_const)
  have hvm : Measurable v := hvloc.mono (Probability.localSigma_le_borel _) le_rfl
  have herrall : ∀ᵐ ω ∂reducedLaw Q, ∀ n,
      ‖(⨍ x, f (translate (r n • x) ω) ∂ν) - A n ω‖ ≤ ε := ae_all_iff.mpr herr
  have he : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - v ω‖ ≤ 2 * ε := by
    filter_upwards [hconv, herrall] with ω hc hb
    have hre := short_time_real_limsup_error
      ((Complex.continuous_re.tendsto (f ω)).comp hc) (fun n =>
        (Complex.abs_re_le_norm ((⨍ x, f (translate (r (φ n) • x) ω) ∂ν) -
          A (φ n) ω)).trans (hb (φ n)))
    have him := short_time_real_limsup_error
      ((Complex.continuous_im.tendsto (f ω)).comp hc) (fun n =>
        (Complex.abs_im_le_norm ((⨍ x, f (translate (r (φ n) • x) ω) ∂ν) -
          A (φ n) ω)).trans (hb (φ n)))
    have hre' : |(f ω - v ω).re| ≤ ε := by simpa [v] using hre
    have him' : |(f ω - v ω).im| ≤ ε := by simpa [v] using him
    calc
      ‖f ω - v ω‖ ≤ |(f ω - v ω).re| + |(f ω - v ω).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ ε + |ε| := add_le_add hre' (him'.trans (le_abs_self ε))
      _ = 2 * ε := by rw [abs_of_nonneg hε]; ring
  have hdiff : MemLp (fun ω => f ω - v ω) 2 (reducedLaw Q) :=
    MemLp.of_bound ((Lp.stronglyMeasurable f).measurable.sub hvm).aestronglyMeasurable
      (2 * ε) he
  have hmem : MemLp v 2 (reducedLaw Q) := by
    convert (Lp.memLp f).sub hdiff using 1
    funext ω
    simp only [Pi.sub_apply, sub_sub_cancel]
  refine ⟨hmem.toLp v, ⟨v, hvloc, hmem.coeFn_toLp.symm⟩, ?_⟩
  filter_upwards [he, hmem.coeFn_toLp] with ω hω heω
  simpa only [heω] using hω

/-- A measurable joint representative inherits the time integral of the squared
norm of the underlying `L²` orbit. -/
theorem short_time_joint_sq_integrable {T Ω : Type*}
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

end EinsteinFull.Blueprint
