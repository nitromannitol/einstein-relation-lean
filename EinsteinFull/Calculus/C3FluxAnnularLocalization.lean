import EinsteinFull.Calculus.C3ConditionalFluxBlocks
import EinsteinFull.Calculus.K4AnnularCore
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinRelation.Environment.LocalIntegralMeasurability
import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The cutoff support plus the local observation radius fits strictly inside
the buffered ball used by the actual conditional expectation. -/
theorem carverS_buffered_block_window {d : ℕ} {R r : ℝ}
    (hRr : 0 ≤ R * r) (n : ℕ) (z y u : Vec d)
    (hy : euclideanNorm (y - z) ≤ R * r)
    (hu : euclideanNorm u < R * 2 ^ n * r) :
    euclideanNorm (y + u - z) < R * 2 ^ (n + 1) * r := by
  have hsmall : R * r ≤ R * 2 ^ n * r := by
    calc
      R * r ≤ R * r * 2 ^ n :=
        le_mul_of_one_le_right hRr (one_le_pow₀ (by norm_num))
      _ = R * 2 ^ n * r := by ring
  have heq : y + u - z = (y - z) + u := by abel
  calc
    euclideanNorm (y + u - z) ≤ euclideanNorm (y - z) + euclideanNorm u := by
      rw [heq]
      exact TimeChange.euclideanNorm_add_le _ _
    _ < R * r + R * 2 ^ n * r := add_lt_add_of_le_of_lt hy hu
    _ ≤ R * 2 ^ n * r + R * 2 ^ n * r := add_le_add hsmall le_rfl
    _ = R * 2 ^ (n + 1) * r := by rw [pow_succ]; ring

/-- Replacing an endpoint and its gradient by local representatives gives a
local representative of the literal endpoint weak-flux formula. -/
theorem carverS_measurable_local_flux {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {ρ : ℝ} (hρ : 0 < ρ)
    (ν : EndpointIndex d) (ζ : ℂ) (u : FieldPair d → ℂ)
    (g : Fin d → FieldPair d → ℂ)
    (hu : Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] u)
    (hg : ∀ k, Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (g k))
    (j : Fin d) :
    Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}]
      (fun ω => ∑ k : Fin d,
        ((ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)) *
          (g k ω - match ν with
            | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * u ω
            | _ => 0)) := by
  let U := {x : Vec d | euclideanNorm x < ρ}
  let : MeasurableSpace (FieldPair d) := localSigma U
  have hzero : (0 : Vec d) ∈ U := by
    simpa only [U, Set.mem_ofPred_eq, euclideanNorm, euclideanSq, dot,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, Real.sqrt_zero] using hρ
  have hpair : Measurable (fun ω : FieldPair d => (ω.1 0, ω.2 0)) := by
    refine Measurable.of_comap_le ?_
    exact le_iSup_of_le (⟨0, hzero⟩ : U) le_rfl
  have ha : ∀ k : Fin d, Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) := by
    intro k
    have hentry : Continuous (fun M : Mat d => M j k) := by fun_prop
    exact (Complex.continuous_ofReal.comp hentry).measurable.comp
      (measurable_fst.comp hpair)
  apply Finset.measurable_sum
  intro k _
  apply ((ha k).sub measurable_const).mul
  apply (hg k).sub
  cases ν with
  | inl i => exact measurable_const
  | inr b =>
    cases b with
    | false => exact measurable_const
    | true => exact measurable_const.mul hu

/-- A bounded matrix row transfers scalar and coordinatewise gradient errors
to the literal flux, including its zeroth-order correction. -/
theorem carverS_flux_difference_le {d : ℕ}
    (b q G g : Fin d → ℂ) (U u : ℂ) {M Z ε : ℝ}
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) (_hε : 0 ≤ ε)
    (hb : ∀ k, ‖b k‖ ≤ M) (hq : ∀ k, ‖q k‖ ≤ Z)
    (hG : ∀ k, ‖G k - g k‖ ≤ ε) (hU : ‖U - u‖ ≤ ε) :
    ‖(∑ k, b k * (G k - q k * U)) -
      ∑ k, b k * (g k - q k * u)‖ ≤ (d : ℝ) * M * (1 + Z) * ε := by
  have heq : (∑ k, b k * (G k - q k * U)) -
      ∑ k, b k * (g k - q k * u) =
      ∑ k, b k * ((G k - g k) - q k * (U - u)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ ∑ k, ‖b k * ((G k - g k) - q k * (U - u))‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin d, M * (ε + Z * ε) := by
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul]
      exact mul_le_mul (hb k)
        ((norm_sub_le _ _).trans (add_le_add (hG k)
          (by rw [norm_mul]; exact mul_le_mul (hq k) hU (norm_nonneg _) hZ)))
        (norm_nonneg _) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

/-- The literal coefficient defect has a bound depending only on the original
ellipticity parameter, under the actual reduced law. -/
theorem carverS_coefficient_defect_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j k,
      ‖(ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)‖ ≤
        Real.exp (2 * Λ) * Λ + sourceReducedBound Λ := by
  have hΛ : 0 < Λ := zero_lt_one.trans_le Q.ellipticity_parameter
  have hK : 0 < sourceReducedBound Λ := by
    unfold sourceReducedBound
    positivity
  have hentry (B : ℝ) (hB : 0 < B) (A : Mat d)
      (hA : IsElliptic B (fun _ : Vec d => A)) (j k : Fin d) : |A j k| ≤ B := by
    have hv := Correctors.mulVec_euclideanNorm_le_of_quadratic A hB (hA 0).1
      (fun ξ => (mul_nonneg (inv_nonneg.mpr hB.le)
        (by unfold euclideanSq dot; exact Finset.sum_nonneg (fun k _ => mul_self_nonneg (ξ k)))).trans ((hA 0).2 ξ).1)
      (fun ξ => ((hA 0).2 ξ).2) (unitVector k)
    have he : |(A.mulVec (unitVector k)) j| ≤ euclideanNorm (A.mulVec (unitVector k)) := by
      rw [TimeChange.euclideanNorm_eq_norm_toLp]
      simpa only [Real.norm_eq_abs] using
        PiLp.norm_apply_le (WithLp.toLp 2 (A.mulVec (unitVector k)) : EuclideanSpace ℝ (Fin d)) j
    have hj : (A.mulVec (unitVector k)) j = A j k := by
      change dotProduct (fun l => A j l) (Pi.single k 1) = _
      rw [dotProduct_single, mul_one]
    have hu : euclideanNorm (unitVector k) = 1 := by
      simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]
    rw [hj] at he
    rw [hu, mul_one] at hv
    exact he.trans hv
  have hhom : ∀ j k, |homogenizedCoefficient Q j k| ≤ sourceReducedBound Λ := by
    intro j k
    exact hentry _ hK (homogenizedMatrix Q) (homogenizedMatrix_isElliptic Q) j k
  filter_upwards [Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q] with ω hω
  intro j k
  calc
    _ ≤ ‖(ω.1 0 j k : ℂ)‖ + ‖(homogenizedCoefficient Q j k : ℂ)‖ := norm_sub_le _ _
    _ ≤ Real.exp (2 * Λ) * Λ + sourceReducedBound Λ := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        add_le_add (hentry _ (mul_pos (Real.exp_pos _) hΛ) (ω.1 0) hω j k) (hhom j k)

/-- The endpoint locality estimate gives jointly local representatives of the
same weak flux supplied by the block estimate. The scalar may be uncentered:
only the transpose endpoint enters the zeroth-order correction. -/
theorem carverS_local_flux_approximation {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {ρ M ε : ℝ} (hρ : 0 < ρ)
    (hM : 0 ≤ M) (hε : 0 ≤ ε) (ν : EndpointIndex d) (ζ : ℂ)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (U V Uloc : Lp ℂ 2 (reducedLaw Q))
    (G J Gloc : Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    (hflux : IsEndpointWeakFlux hd Q ν ζ a U G J)
    (hUV : ν = .inr true → U = V)
    (hu : IsComplexLocalObservation Q ρ Uloc)
    (hg : ∀ k, IsComplexLocalObservation Q ρ (Gloc k))
    (hcoef : ∀ᵐ ω ∂reducedLaw Q, ∀ j k,
      ‖(ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)‖ ≤ M)
    (herr : ∀ᵐ ω ∂reducedLaw Q,
      ‖V ω - Uloc ω‖ + Real.sqrt (∑ k, ‖G k ω - Gloc k ω‖ ^ 2) ≤ ε) :
    ∃ F : Fin d → FieldPair d → ℂ,
      (∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (F j)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ j,
        ‖J j ω - F j ω‖ ≤ (d : ℝ) * M * (1 + 2 * ‖ζ‖) * ε := by
  classical
  obtain ⟨u, hu, hueq⟩ := hu
  choose g hg hgeq using hg
  let q : Fin d → ℂ := fun k => match (motive := ∀ _ : EndpointIndex d, ℂ) ν with
    | .inr true => 2 * ζ * (unitVector (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ : Fin d) k : ℂ)
    | _ => 0
  let F : Fin d → FieldPair d → ℂ := fun j ω => ∑ k,
    ((ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)) *
      (g k ω - q k * u ω)
  have hq : ∀ k, ‖q k‖ ≤ 2 * ‖ζ‖ := by
    intro k
    have he : ‖(unitVector (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ : Fin d) k : ℂ)‖ ≤ 1 := by
      simp only [unitVector, Pi.single_apply]
      split_ifs <;> norm_num
    cases ν with
    | inl i => simp [q]
    | inr b =>
      cases b with
      | false => simp [q]
      | true =>
        simpa only [q, norm_mul, Complex.norm_ofNat, mul_one] using
          mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * ‖ζ‖)
  have hF : ∀ j,
      Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (F j) := by
    intro j
    convert carverS_measurable_local_flux hd Q hρ ν ζ u g hu hg j using 1
    funext ω
    apply Finset.sum_congr rfl
    intro k _
    cases ν with
    | inl i => simp only [q, zero_mul]
    | inr b => cases b <;> simp only [q, zero_mul]
  refine ⟨F, hF, ?_⟩
  have hgeq' : ∀ᵐ ω ∂reducedLaw Q, ∀ k, g k ω = Gloc k ω :=
    (ae_all_iff).2 hgeq
  have hae : ∀ᵐ ω ∂reducedLaw Q, ∀ j k, a j k ω = (ω.1 0 j k : ℂ) :=
    (ae_all_iff).2 fun j => (ae_all_iff).2 (ha j)
  have hqV (ω : FieldPair d) (k : Fin d) :
      (match (motive := ∀ _ : EndpointIndex d, ℂ) ν with
        | .inr true => 2 * ζ * (unitVector (⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ : Fin d) k : ℂ) * U ω
        | _ => 0) = q k * V ω := by
    dsimp only [q]
    cases hν : ν with
    | inl i => simp only [zero_mul]
    | inr b =>
      cases b with
      | false => simp only [zero_mul]
      | true => rw [hUV hν]
  have hflux' : ∀ᵐ ω ∂reducedLaw Q, ∀ j, J j ω = ∑ k,
      (a j k ω - (homogenizedCoefficient Q j k : ℂ)) * (G k ω - q k * V ω) := by
    apply (ae_all_iff).2
    intro j
    filter_upwards [hflux.2 j] with ω hω
    rw [hω]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun z : ℂ =>
      (a j k ω - (homogenizedCoefficient Q j k : ℂ)) * (G k ω - z)) (hqV ω k)
  filter_upwards [hcoef, herr, hueq, hgeq', hae, hflux'] with ω hc he huω hgω haω hfω
  have hscalar : ‖V ω - u ω‖ ≤ ε := by
    rw [huω]
    exact (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans he
  have hgrad : ∀ k, ‖G k ω - g k ω‖ ≤ ε := by
    intro k
    rw [hgω k]
    have hk : ‖G k ω - Gloc k ω‖ ≤ Real.sqrt (∑ l, ‖G l ω - Gloc l ω‖ ^ 2) := by
      apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)).2
      exact Finset.single_le_sum (f := fun l : Fin d => ‖G l ω - Gloc l ω‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
    exact hk.trans ((le_add_of_nonneg_left (norm_nonneg _)).trans he)
  intro j
  rw [hfω j]
  simp_rw [haω j]
  exact carverS_flux_difference_le _ q (fun k => G k ω) (fun k => g k ω)
    (V ω) (u ω) hM (by positivity) hε (hc j) hq hgrad hscalar

/-- Endpoint locality applies to any supplied actual weak-flux witnesses.
Gradient uniqueness identifies the locality witness, so the block construction
does not have to replace its original G and J. -/
theorem carverS_actual_flux_locality (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ Cdet c : ℝ, ∃ N : ℕ, 1 ≤ Cdet ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0), 1 ≤ (t : ℝ) →
    ∀ G J : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G J →
    ∀ ρ : ℝ, Cdet * Real.sqrt (t : ℝ) ≤ ρ →
    ∃ F : Fin d → FieldPair d → ℂ,
      (∀ j, Measurable[localSigma {x : Vec d | euclideanNorm x < ρ}] (F j)) ∧
      ∀ᵐ ω ∂reducedLaw Q, ∀ j,
        ‖J j ω - F j ω‖ ≤
          (d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity +
            sourceReducedBound D.ellipticity) * (1 + 2 * ‖ζ‖) *
          (Cdet * (2 + (t : ℝ)) ^ N *
            Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) := by
  obtain ⟨Cdet, c, N, hCdet, hc, hlocal⟩ := hlocal d hd D
  refine ⟨Cdet, c, N, hCdet, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht G J hflux ρ hρ
  obtain ⟨H, hH, happrox, _⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have ht0 : 0 < (t : ℝ) := zero_lt_one.trans_le ht
  have hGH : G = H t := hflux.1.unique (hH t ht0).1
  obtain ⟨Uloc, Gloc, hu, hg, herr, _⟩ := happrox t ht ρ hρ
  have hρ0 : 0 < ρ :=
    (mul_pos (zero_lt_one.trans_le hCdet) (Real.sqrt_pos.2 ht0)).trans_le hρ
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le Q.ellipticity_parameter
  have hM : 0 ≤ Real.exp (2 * D.ellipticity) * D.ellipticity +
      sourceReducedBound D.ellipticity := by
    unfold sourceReducedBound
    positivity
  have hCdet0 : 0 ≤ Cdet := zero_le_one.trans hCdet
  have hε : 0 ≤ Cdet * (2 + (t : ℝ)) ^ N *
      Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) := by
    positivity
  apply carverS_local_flux_approximation hd Q hρ0 hM hε ν ζ a
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
    (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) Uloc G J Gloc ha hflux
  · intro hν
    subst ν
    rfl
  · exact hu
  · exact hg
  · exact carverS_coefficient_defect_bound Q
  · simpa only [hGH] using herr

/-- A complex weighted spatial block sees the joint coefficient and clock
fields on the Minkowski sum of its support and its observation window. -/
theorem carverS_measurable_local_block {d : ℕ} {S U W : Set (Vec d)}
    (hS : MeasurableSet S) (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    (k : Vec d → ℝ) (hk : Measurable k)
    (f : FieldPair d → ℂ) (hf : Measurable[localSigma U] f) :
    Measurable[localSigma W] (fun ω => ∫ x in S, k x • f (translate x ω)) := by
  classical
  let : MeasurableSpace (FieldPair d) := localSigma W
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · subst S
    simpa only [setIntegral_empty] using
      (measurable_const : Measurable[localSigma W] (fun _ : FieldPair d => (0 : ℂ)))
  · let repair : Vec d → Vec d := fun x => if x ∈ S then x else x0
    have hmem : ∀ x, repair x ∈ S := by
      intro x
      dsimp only [repair]
      split_ifs with hx
      · exact hx
      · exact hx0
    let rep : Vec d → S := fun x => ⟨repair x, hmem x⟩
    have hrep : Measurable rep :=
      (Measurable.ite hS measurable_id measurable_const).subtype_mk
    have hrep_id : ∀ x ∈ S, (rep x : Vec d) = x := by
      intro x hx
      exact ite_eq_left hx
    have hpair : @Measurable (Vec d × FieldPair d) (S × FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W))
        (@Prod.instMeasurableSpace S (FieldPair d) _ (localSigma W))
        (fun q => (rep q.1, q.2)) :=
      (hrep.comp measurable_fst).prodMk measurable_snd
    have hT : @Measurable (Vec d × FieldPair d) (FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) (localSigma U)
        (fun q => translate (rep q.1 : Vec d) q.2) :=
      (measurable_translate_joint hSW).comp hpair
    have hk' : @Measurable (Vec d × FieldPair d) ℝ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1) := (hk.indicator hS).comp measurable_fst
    have hF : @Measurable (Vec d × FieldPair d) ℂ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1 • f (translate (rep q.1 : Vec d) q.2)) :=
      hk'.smul (hf.comp hT)
    have hfun : (fun ω : FieldPair d => ∫ x in S, k x • f (translate x ω)) =
        fun ω : FieldPair d =>
          ∫ x, S.indicator k x • f (translate (rep x : Vec d) ω) := by
      funext ω
      rw [← integral_indicator hS]
      congr 1
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, hrep_id x hx]
      · simp only [Set.indicator_of_notMem hx, zero_smul]
    rw [hfun]
    exact (hF.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

/-- Locality of the literal complex block integral in the buffered ball around
any center, with the Euclidean cutoff support used in the annular contract. -/
theorem carverS_measurable_buffered_block {d : ℕ} {R r : ℝ}
    (hRr : 0 ≤ R * r) (n : ℕ) (z : Vec d)
    (k : Vec d → ℝ) (hk : Measurable k)
    (hsupp : Function.support k ⊆ {y : Vec d | euclideanNorm (y - z) ≤ R * r})
    (f : FieldPair d → ℂ)
    (hf : Measurable[localSigma {u : Vec d | euclideanNorm u < R * 2 ^ n * r}] f) :
    Measurable[localSigma
      {y : Vec d | euclideanNorm (y - z) < R * 2 ^ (n + 1) * r}]
      (fun ω => ∫ y : Vec d, k y • f (translate y ω)) := by
  let S := {y : Vec d | euclideanNorm (y - z) ≤ R * r}
  have hcont : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hS : MeasurableSet S := (isClosed_le hcont continuous_const).measurableSet
  have heq : (fun ω : FieldPair d => ∫ y : Vec d, k y • f (translate y ω)) =
      fun ω : FieldPair d => ∫ y in S, k y • f (translate y ω) := by
    funext ω
    rw [← integral_indicator hS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
    · have hk0 : k y = 0 := by
        by_contra hne
        exact hy (hsupp hne)
      simp only [Set.indicator_of_notMem hy, hk0, zero_smul]
  rw [heq]
  exact carverS_measurable_local_block hS
    (fun y hy u hu => carverS_buffered_block_window hRr n z y u hy hu) k hk f hf

/-- A complex weighted spatial block sees the joint coefficient and clock
fields on the Minkowski sum of its support and its observation window. -/
theorem carverS_measurable_local_block_complex {d : ℕ} {S U W : Set (Vec d)}
    (hS : MeasurableSet S) (hSW : ∀ x ∈ S, ∀ y ∈ U, x + y ∈ W)
    (k : Vec d → ℂ) (hk : Measurable k)
    (f : FieldPair d → ℂ) (hf : Measurable[localSigma U] f) :
    Measurable[localSigma W] (fun ω => ∫ x in S, k x • f (translate x ω)) := by
  classical
  let : MeasurableSpace (FieldPair d) := localSigma W
  rcases S.eq_empty_or_nonempty with hS0 | ⟨x0, hx0⟩
  · subst S
    simpa only [setIntegral_empty] using
      (measurable_const : Measurable[localSigma W] (fun _ : FieldPair d => (0 : ℂ)))
  · let repair : Vec d → Vec d := fun x => if x ∈ S then x else x0
    have hmem : ∀ x, repair x ∈ S := by
      intro x
      dsimp only [repair]
      split_ifs with hx
      · exact hx
      · exact hx0
    let rep : Vec d → S := fun x => ⟨repair x, hmem x⟩
    have hrep : Measurable rep :=
      (Measurable.ite hS measurable_id measurable_const).subtype_mk
    have hrep_id : ∀ x ∈ S, (rep x : Vec d) = x := by
      intro x hx
      exact ite_eq_left hx
    have hpair : @Measurable (Vec d × FieldPair d) (S × FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W))
        (@Prod.instMeasurableSpace S (FieldPair d) _ (localSigma W))
        (fun q => (rep q.1, q.2)) :=
      (hrep.comp measurable_fst).prodMk measurable_snd
    have hT : @Measurable (Vec d × FieldPair d) (FieldPair d)
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) (localSigma U)
        (fun q => translate (rep q.1 : Vec d) q.2) :=
      (measurable_translate_joint hSW).comp hpair
    have hk' : @Measurable (Vec d × FieldPair d) ℂ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1) := (hk.indicator hS).comp measurable_fst
    have hF : @Measurable (Vec d × FieldPair d) ℂ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _ (localSigma W)) inferInstance
        (fun q => S.indicator k q.1 • f (translate (rep q.1 : Vec d) q.2)) :=
      hk'.smul (hf.comp hT)
    have hfun : (fun ω : FieldPair d => ∫ x in S, k x • f (translate x ω)) =
        fun ω : FieldPair d =>
          ∫ x, S.indicator k x • f (translate (rep x : Vec d) ω) := by
      funext ω
      rw [← integral_indicator hS]
      congr 1
      funext x
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx, hrep_id x hx]
      · simp only [Set.indicator_of_notMem hx, zero_smul]
    rw [hfun]
    exact (hF.stronglyMeasurable.integral_prod_left' (μ := volume)).measurable

/-- Locality of the literal complex block integral in the buffered ball around
any center, with the Euclidean cutoff support used in the annular contract. -/
theorem carverS_measurable_buffered_block_complex {d : ℕ} {R r : ℝ}
    (hRr : 0 ≤ R * r) (n : ℕ) (z : Vec d)
    (k : Vec d → ℂ) (hk : Measurable k)
    (hsupp : Function.support k ⊆ {y : Vec d | euclideanNorm (y - z) ≤ R * r})
    (f : FieldPair d → ℂ)
    (hf : Measurable[localSigma {u : Vec d | euclideanNorm u < R * 2 ^ n * r}] f) :
    Measurable[localSigma
      {y : Vec d | euclideanNorm (y - z) < R * 2 ^ (n + 1) * r}]
      (fun ω => ∫ y : Vec d, k y • f (translate y ω)) := by
  let S := {y : Vec d | euclideanNorm (y - z) ≤ R * r}
  have hcont : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hS : MeasurableSet S := (isClosed_le hcont continuous_const).measurableSet
  have heq : (fun ω : FieldPair d => ∫ y : Vec d, k y • f (translate y ω)) =
      fun ω : FieldPair d => ∫ y in S, k y • f (translate y ω) := by
    funext ω
    rw [← integral_indicator hS]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy]
    · have hk0 : k y = 0 := by
        by_contra hne
        exact hy (hsupp hne)
      simp only [Set.indicator_of_notMem hy, hk0, zero_smul]
  rw [heq]
  exact carverS_measurable_local_block_complex hS
    (fun y hy u hu => carverS_buffered_block_window hRr n z y u hy hu) k hk f hf

/-- The actual L2 spatial block equals its samplewise integral on one event.
Product integrability justifies this without intersecting uncountably many
translation events. -/
theorem carverS_block_integral_representative {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (k : Vec d → ℂ)
    (hk : Integrable k) (hc : Continuous k) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × FieldPair d => k p.1 • f (translate p.1 p.2))
      (volume.prod (reducedLaw Q)) ∧
    (fun ω => (∫ y : Vec d, k y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y f) ω) =ᵐ[reducedLaw Q]
      fun ω => ∫ y : Vec d, k y • f (translate y ω) := by
  let := reducedLaw_probability Q
  let u : Vec d → Lp ℂ 2 (reducedLaw Q) := fun y =>
    k y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f
  let F : Vec d × FieldPair d → ℂ := fun p => k p.1 • f (translate p.1 p.2)
  have ht : Continuous (fun y : Vec d => complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y f) :=
    (continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const)
  have hu : Integrable u := by
    apply (hk.norm.mul_const ‖f‖).mono' (hc.smul ht).aestronglyMeasurable
    filter_upwards with y
    change ‖k y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f‖ ≤
      ‖k y‖ * ‖f‖
    rw [norm_smul, norm_complexTranslation]
  have hF : Measurable F := (hc.measurable.comp measurable_fst).smul
    ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable)
  have heq : ∀ y, (fun ω => F (y, ω)) =ᵐ[reducedLaw Q] u y := by
    intro y
    filter_upwards [Lp.coeFn_smul (k y) (complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y f), coeFn_complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y f] with ω hsm htr
    simp only [u, F, hsm, Pi.smul_apply, htr]
  have hn (v : Lp ℂ 2 (reducedLaw Q)) : (∫ ω, ‖v ω‖ ∂reducedLaw Q) ≤ ‖v‖ := by
    rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable v),
      ← eLpNorm_one_eq_lintegral_enorm (Lp.aestronglyMeasurable v), Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top v)
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hi : Integrable F (volume.prod (reducedLaw Q)) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ (fun y => ((Lp.memLp (u y)).integrable (by norm_num)).congr
      (heq y).symm), ?_⟩
    apply hu.norm.mono' (hF.stronglyMeasurable.norm.integral_prod_right.aestronglyMeasurable)
    filter_upwards with y
    rw [Real.norm_of_nonneg (integral_nonneg fun ω => norm_nonneg _),
      integral_congr_ae ((heq y).mono fun ω h => congrArg norm h)]
    exact hn (u y)
  refine ⟨hi, ?_⟩
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hi.integral_prod_right
  intro A hA hμA
  have ht := integral_inner (𝕜 := ℂ) hu (indicatorConstLp 2 hA hμA.ne (1 : ℂ))
  rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  simp_rw [L2.inner_indicatorConstLp_one hA hμA.ne] at ht
  rw [← ht]
  have hir : Integrable F (volume.prod ((reducedLaw Q).restrict A)) := by
    have h := hi.integrableOn (s := Set.univ ×ˢ A)
    rwa [IntegrableOn, ← Measure.prod_restrict, Measure.restrict_univ] at h
  rw [← integral_integral_swap (f := fun y ω => F (y, ω)) hir]
  apply integral_congr_ae
  filter_upwards with y
  exact integral_congr_ae (ae_restrict_of_ae (heq y).symm)

/-- A uniform error in the flux gives the corresponding error in the actual
Bochner block, with the precise L1 mass of its scalar kernel. -/
theorem carverS_block_approximation_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (k : Vec d → ℂ)
    (hk : Integrable k) (hc : Continuous k) (f : Lp ℂ 2 (reducedLaw Q))
    (g : FieldPair d → ℂ) (hg : Measurable g) {ε : ℝ}
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - g ω‖ ≤ ε) :
    ∀ᵐ ω ∂reducedLaw Q,
      ‖(∫ y : Vec d, k y • complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) y f) ω -
        ∫ y : Vec d, k y • g (translate y ω)‖ ≤ ε * ∫ y : Vec d, ‖k y‖ := by
  let := reducedLaw_probability Q
  have hrep := carverS_block_integral_representative Q k hk hc f
  have hd : Measurable (fun p : Vec d × FieldPair d =>
      f (translate p.1 p.2) - g (translate p.1 p.2)) :=
    ((Lp.stronglyMeasurable f).measurable.sub hg).comp
      Probability.continuous_translate.measurable
  have hsp : ∀ᵐ ω ∂reducedLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      ‖f (translate y ω) - g (translate y ω)‖ ≤ ε := by
    have hset : MeasurableSet {p : Vec d × FieldPair d |
        ‖f (translate p.1 p.2) - g (translate p.1 p.2)‖ ≤ ε} :=
      measurableSet_le hd.norm measurable_const
    apply (Measure.ae_ae_comm (μ := (volume : Measure (Vec d))) (ν := reducedLaw Q)
      (p := fun y ω => ‖f (translate y ω) - g (translate y ω)‖ ≤ ε) hset).mp
    exact ae_of_all _ fun y =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) y).quasiMeasurePreserving.ae herr
  filter_upwards [hrep.2, hrep.1.prod_left_ae, hsp] with ω heq hfi hω
  let D : Vec d → ℂ := fun y => k y • (f (translate y ω) - g (translate y ω))
  have hdm : Measurable D := hc.measurable.smul
    (hd.comp (measurable_id.prodMk measurable_const))
  have hbound : ∀ᵐ y ∂(volume : Measure (Vec d)), ‖D y‖ ≤ ε * ‖k y‖ := by
    filter_upwards [hω] with y hy
    dsimp only [D]
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left hy (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hDi : Integrable D := (hk.norm.const_mul ε).mono' hdm.aestronglyMeasurable hbound
  have hgint : (fun y => k y • g (translate y ω)) =
      (fun y => k y • f (translate y ω) - D y) := by
    funext y
    dsimp only [D]
    rw [smul_sub]
    abel
  rw [heq, hgint, integral_sub hfi hDi, sub_sub_cancel]
  exact (norm_integral_le_of_norm_le (hk.norm.const_mul ε) hbound).trans_eq
    (integral_const_mul ε _)

/-- Comparison with a local approximant for the actual joint-field conditional
expectation. All seminorms are finite before passing to real numbers. -/
theorem carverS_condExp_error_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (U : Set (Vec d)) {f g : FieldPair d → ℂ}
    (hf : MemLp f p (reducedLaw Q)) (hg : MemLp g p (reducedLaw Q))
    (hgm : AEStronglyMeasurable[localSigma U] g (reducedLaw Q)) :
    MemLp (f - (reducedLaw Q)[f | localSigma U]) p (reducedLaw Q) ∧
      (eLpNorm (f - (reducedLaw Q)[f | localSigma U]) p (reducedLaw Q)).toReal ≤
        2 * (eLpNorm (f - g) p (reducedLaw Q)).toReal := by
  let := reducedLaw_probability Q
  have hm := Probability.localSigma_le_borel U
  have hfixed := condExp_of_aestronglyMeasurable' hm hgm (hg.integrable hp)
  have hsub := condExp_sub (hf.integrable hp) (hg.integrable hp) (localSigma U)
  have heq : f - (reducedLaw Q)[f | localSigma U] =ᵐ[reducedLaw Q]
      (f - g) - (reducedLaw Q)[f - g | localSigma U] := by
    filter_upwards [hfixed, hsub] with ω hfix hdiff
    simp only [Pi.sub_apply] at hdiff ⊢
    rw [hdiff, hfix]
    abel
  have herr := hf.sub hg
  refine ⟨hf.sub (hf.condExp hp), ?_⟩
  rw [eLpNorm_congr_ae heq]
  have hcontract :
      eLpNorm ((reducedLaw Q)[f - g | localSigma U]) p (reducedLaw Q) ≤
        eLpNorm (f - g) p (reducedLaw Q) :=
    eLpNorm_condExp_le_eLpNorm (μ := reducedLaw Q) (m := localSigma U) (f - g) hp
  have htriangle :
      eLpNorm ((f - g) - (reducedLaw Q)[f - g | localSigma U]) p (reducedLaw Q) ≤
        eLpNorm (f - g) p (reducedLaw Q) + eLpNorm (f - g) p (reducedLaw Q) :=
    (eLpNorm_sub_le (μ := reducedLaw Q) (f := f - g)
      (g := (reducedLaw Q)[f - g | localSigma U]) hp).trans
        (add_le_add le_rfl hcontract)
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨herr.eLpNorm_ne_top, herr.eLpNorm_ne_top⟩) htriangle
  rw [ENNReal.toReal_add herr.eLpNorm_ne_top herr.eLpNorm_ne_top] at hreal
  exact hreal.trans_eq (by ring)

/-- A uniformly accurate local representative suffices; its finite-p membership
is a consequence of the bound and the membership of the observation. -/
theorem carverS_condExp_error_le_of_ae_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (U : Set (Vec d)) {f g : FieldPair d → ℂ}
    (hf : MemLp f p (reducedLaw Q))
    (hgm : AEStronglyMeasurable[localSigma U] g (reducedLaw Q))
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - g ω‖ ≤ ε) :
    MemLp (f - (reducedLaw Q)[f | localSigma U]) p (reducedLaw Q) ∧
      (eLpNorm (f - (reducedLaw Q)[f | localSigma U]) p (reducedLaw Q)).toReal ≤
        2 * ε := by
  let := reducedLaw_probability Q
  have hgm' := hgm.mono (Probability.localSigma_le_borel U)
  have he : MemLp (f - g) p (reducedLaw Q) :=
    MemLp.of_bound (hf.aestronglyMeasurable.sub hgm') ε herr
  have hg : MemLp g p (reducedLaw Q) := by
    convert hf.sub he using 1
    ext ω
    simp only [Pi.sub_apply, sub_sub_cancel]
  obtain ⟨hmem, hbound⟩ := carverS_condExp_error_le Q hp U hf hg hgm
  refine ⟨hmem, hbound.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))⟩
  have hnorm : eLpNorm (f - g) p (reducedLaw Q) ≤ ENNReal.ofReal ε := by
    simpa only [measure_univ, ENNReal.one_rpow, one_mul] using
      eLpNorm_le_of_ae_bound (p := p) he.aestronglyMeasurable herr
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hnorm).trans_eq
    (ENNReal.toReal_ofReal hε)

/-- Center an actual block after constructing its local representative. The
pointwise centering cost and the conditional-expectation cost are both two. -/
theorem carverS_centered_condExp_error_le_of_approximation {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (U : Set (Vec d)) (B : Lp ℂ 2 (reducedLaw Q))
    (hB : MemLp (B : FieldPair d → ℂ) p (reducedLaw Q))
    (g : FieldPair d → ℂ) (hgm : Measurable[localSigma U] g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖B ω - g ω‖ ≤ ε) :
    let X := (centeredComplexLp Q B : FieldPair d → ℂ)
    MemLp (X - (reducedLaw Q)[X | localSigma U]) p (reducedLaw Q) ∧
      (eLpNorm (X - (reducedLaw Q)[X | localSigma U]) p (reducedLaw Q)).toReal ≤
        4 * ε := by
  let := reducedLaw_probability Q
  have hgm' : AEStronglyMeasurable g (reducedLaw Q) :=
    (hgm.mono (Probability.localSigma_le_borel U) le_rfl).stronglyMeasurable.aestronglyMeasurable
  have he : MemLp ((B : FieldPair d → ℂ) - g) p (reducedLaw Q) :=
    MemLp.of_bound (hB.aestronglyMeasurable.sub hgm') ε herr
  have hg : MemLp g p (reducedLaw Q) := by
    convert hB.sub he using 1
    ext ω
    simp only [Pi.sub_apply, sub_sub_cancel]
  have hmean : ‖(∫ ω, B ω ∂reducedLaw Q) - ∫ ω, g ω ∂reducedLaw Q‖ ≤ ε := by
    rw [← integral_sub (hB.integrable hp) (hg.integrable hp)]
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const herr
  have hcenter : ∀ᵐ ω ∂reducedLaw Q,
      ‖centeredComplexLp Q B ω - (g ω - ∫ ω', g ω' ∂reducedLaw Q)‖ ≤ 2 * ε := by
    filter_upwards [coeFn_centeredComplexLp Q B, herr] with ω hc he
    rw [hc]
    calc
      ‖(B ω - ∫ ω', B ω' ∂reducedLaw Q) -
          (g ω - ∫ ω', g ω' ∂reducedLaw Q)‖ =
          ‖(B ω - g ω) - ((∫ ω', B ω' ∂reducedLaw Q) -
            ∫ ω', g ω' ∂reducedLaw Q)‖ := by congr 1; abel
      _ ≤ ‖B ω - g ω‖ + ‖(∫ ω', B ω' ∂reducedLaw Q) -
          ∫ ω', g ω' ∂reducedLaw Q‖ := norm_sub_le _ _
      _ ≤ 2 * ε := by linarith
  have hc := carverS_condExp_error_le_of_ae_bound Q hp U
    (carverS_memLp_centered Q B hB)
    (hgm.sub_const (∫ ω, g ω ∂reducedLaw Q)).stronglyMeasurable.aestronglyMeasurable
    (mul_nonneg (by norm_num) hε) hcenter
  dsimp only
  exact ⟨hc.1, by simpa only [← mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hc.2⟩

/-- A local flux approximant controls the conditional error of the actual
centered block at the prescribed buffered radius. The finite-p input is exactly
the block membership supplied by the block estimate. -/
theorem carverS_buffered_block_condExp_bound {d : ℕ} {Λ r₀ R r : ℝ}
    (Q : EnvironmentLaw d Λ r₀) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hRr : 0 ≤ R * r) (n : ℕ) (z : Vec d)
    (k : Vec d → ℂ) (hk : Integrable k) (hc : Continuous k)
    (hsupp : Function.support k ⊆ {y : Vec d | euclideanNorm (y - z) ≤ R * r})
    (f : Lp ℂ 2 (reducedLaw Q)) (g : FieldPair d → ℂ)
    (hg : Measurable[localSigma {u : Vec d | euclideanNorm u < R * 2 ^ n * r}] g)
    {ε : ℝ} (hε : 0 ≤ ε)
    (herr : ∀ᵐ ω ∂reducedLaw Q, ‖f ω - g ω‖ ≤ ε) :
    let B := ∫ y : Vec d, k y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y f
    let X := (centeredComplexLp Q B : FieldPair d → ℂ)
    let U := {y : Vec d | euclideanNorm (y - z) < R * 2 ^ (n + 1) * r}
    MemLp (B : FieldPair d → ℂ) p (reducedLaw Q) →
      MemLp (X - (reducedLaw Q)[X | localSigma U]) p (reducedLaw Q) ∧
      (eLpNorm (X - (reducedLaw Q)[X | localSigma U]) p (reducedLaw Q)).toReal ≤
        4 * (ε * ∫ y : Vec d, ‖k y‖) := by
  dsimp only
  intro hB
  have hgm : Measurable g :=
    hg.mono (Probability.localSigma_le_borel _) le_rfl
  exact carverS_centered_condExp_error_le_of_approximation Q hp _ _ hB
    (fun ω => ∫ y : Vec d, k y • g (translate y ω))
    (carverS_measurable_buffered_block_complex hRr n z k hc.measurable hsupp g hg)
    (mul_nonneg hε (integral_nonneg fun _ => norm_nonneg _))
    (carverS_block_approximation_bound Q k hk hc f g hgm herr)

/-- The Euclidean support of a scalar block kernel gives the required
volume factor; the coordinate box is used only to bound its volume. -/
theorem carverS_supported_kernel_mass_le {d : ℕ} (k : Vec d → ℂ)
    (hk : Integrable k) (z : Vec d) {ρ M : ℝ} (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (hsupp : Function.support k ⊆ {y : Vec d | euclideanNorm (y - z) ≤ ρ})
    (hbound : ∀ y, euclideanNorm (y - z) ≤ ρ → ‖k y‖ ≤ M) :
    (∫ y : Vec d, ‖k y‖) ≤ M * (2 * ρ) ^ d := by
  let S := Set.Icc (fun i => z i - ρ) (fun i => z i + ρ)
  have hsub : {y : Vec d | euclideanNorm (y - z) ≤ ρ} ⊆ S := by
    intro y hy
    have hcoord (i : Fin d) : |y i - z i| ≤ ρ := by
      have hi : |y i - z i| ≤ euclideanNorm (y - z) := by
        rw [TimeChange.euclideanNorm_eq_norm_toLp]
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using
          PiLp.norm_apply_le (WithLp.toLp 2 (y - z) : EuclideanSpace ℝ (Fin d)) i
      exact hi.trans hy
    exact ⟨fun i => by linarith [(abs_le.mp (hcoord i)).1],
      fun i => by linarith [(abs_le.mp (hcoord i)).2]⟩
  have hvol : volume S = ENNReal.ofReal ((2 * ρ) ^ d) := by
    change volume (Set.Icc _ _) = _
    rw [Real.volume_Icc_pi]
    have hid (i : Fin d) : (z i + ρ) - (z i - ρ) = 2 * ρ := by ring
    simp only [hid, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact (ENNReal.ofReal_pow (by positivity) d).symm
  have hzero : ∀ y, y ∉ S → k y = 0 := by
    intro y hy
    by_contra hky
    exact hy (hsub (hsupp hky))
  have hpoint : ∀ y ∈ S, ‖k y‖ ≤ M := by
    intro y _
    by_cases hy : k y = 0
    · simpa only [hy, norm_zero] using hM
    · exact hbound y (hsupp hy)
  calc
    _ = ∫ y in S, ‖k y‖ :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => by rw [hzero y hy, norm_zero])).symm
    _ ≤ ∫ _y in S, M := setIntegral_mono_on hk.norm.integrableOn
      (integrableOn_const (by rw [hvol]; exact ENNReal.ofReal_ne_top))
      measurableSet_Icc hpoint
    _ = M * (2 * ρ) ^ d := by
      rw [setIntegral_const, Measure.real, hvol, ENNReal.toReal_ofReal (by positivity),
        smul_eq_mul, mul_comm]

/-- Widening the common Gaussian envelope preserves its supremum bound.
This permits one structural width for both the block and localization estimates. -/
theorem carverS_gaussian_envelope_mono {d : ℕ} (x : Vec d)
    (S : Set (Vec d)) (hS : S.Nonempty) {s C C' : ℝ}
    (hs : 0 < s) (hC : 0 < C) (hCC' : C ≤ C') :
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (C * s))) '' S) ≤
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (C' * s))) '' S) := by
  have hC' : 0 < C' := hC.trans_le hCC'
  have hs' : 0 ≤ s ^ (-(d : ℝ) / 2) := Real.rpow_nonneg hs.le _
  have hb : BddAbove ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (C' * s))) '' S) := by
    refine ⟨s ^ (-(d : ℝ) / 2), ?_⟩
    rintro _ ⟨y, _, rfl⟩
    calc
      _ ≤ s ^ (-(d : ℝ) / 2) * 1 := mul_le_mul_of_nonneg_left
        (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr (sq_nonneg _)) (mul_pos hC' hs).le)) hs'
      _ = _ := mul_one _
  apply csSup_le (hS.image _)
  rintro _ ⟨y, hy, rfl⟩
  have hd := div_le_div_of_nonneg_left (sq_nonneg (euclideanNorm (x - y)))
    (mul_pos hC hs) (mul_le_mul_of_nonneg_right hCC' hs.le)
  have he : -euclideanNorm (x - y) ^ 2 / (C * s) ≤
      -euclideanNorm (x - y) ^ 2 / (C' * s) := by
    simpa only [neg_div] using neg_le_neg hd
  exact (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hs').trans
    (le_csSup hb ⟨y, hy, rfl⟩)

/-- Polynomial derivative growth can be absorbed while retaining Gaussian
spatial decay. The constant is independent of the spatial point. -/
theorem carverS_gaussian_polynomial_absorption {K r : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (k : ℕ) :
    (1 + r) ^ k * Real.exp (-r ^ 2 / (4 * K)) ≤
      Real.exp (2 * K * (k : ℝ) ^ 2) * Real.exp (-r ^ 2 / (8 * K)) := by
  have hp : (1 + r) ^ k ≤ Real.exp ((k : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) k
  have he : (k : ℝ) * r - r ^ 2 / (8 * K) ≤ 2 * K * (k : ℝ) ^ 2 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * K)).mp
    field_simp [ne_of_gt hK]
    nlinarith only [sq_nonneg (r - 4 * K * (k : ℝ))]
  calc
    _ ≤ Real.exp ((k : ℝ) * r) * Real.exp (-r ^ 2 / (4 * K)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((k : ℝ) * r - r ^ 2 / (4 * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hid : (k : ℝ) * r - r ^ 2 / (4 * K) =
          ((k : ℝ) * r - r ^ 2 / (8 * K)) + -r ^ 2 / (8 * K) := by
        field_simp [ne_of_gt hK]
        ring
      rw [hid]
      exact add_le_add he le_rfl

/-- The additional zeroth-order flux factor is absorbed into the existing
quadratic-force exponential at every large time. -/
theorem carverS_flux_force_factor_le {t : ℝ} (ht : 1 ≤ t) (ζ : ℂ) :
    1 + 2 * ‖ζ‖ ≤ 3 * Real.exp (‖ζ‖ ^ 2 * t) := by
  calc
    _ ≤ 3 * (1 + ‖ζ‖ ^ 2) := by
      nlinarith [sq_nonneg (‖ζ‖ - 1), sq_nonneg ‖ζ‖]
    _ ≤ 3 * Real.exp (‖ζ‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (‖ζ‖ ^ 2)]) (by norm_num)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (le_mul_of_one_le_right (sq_nonneg _) ht)) (by norm_num)

/-- Every spatial derivative of the actual zero-force Gaussian has the
same exact parabolic scaling as its time-one derivative. -/
theorem carverS_homogenizedGaussianKernel_zero_derivative_scale
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (x : Vec d) :
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x =
      (s ^ (-(d : ℝ) / 2) * ((Real.sqrt s)⁻¹) ^ k) •
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0)
          ((Real.sqrt s)⁻¹ • x) := by
  have hf : ContDiff ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) :=
    (contDiff_homogenizedGaussianKernel_complexForce Q i 1 zero_lt_one 0).of_le
      (by exact_mod_cast le_top)
  have heq : homogenizedGaussianKernel Q i s hs 0 =
      fun y => (s ^ (-(d : ℝ) / 2) : ℝ) •
        homogenizedGaussianKernel Q i 1 zero_lt_one 0 ((Real.sqrt s)⁻¹ • y) :=
    funext (homogenizedGaussianKernel_zero_scale Q i s hs)
  have hg : ContDiff ℝ k (fun y : Vec d =>
      homogenizedGaussianKernel Q i 1 zero_lt_one 0 ((Real.sqrt s)⁻¹ • y)) :=
    hf.comp (contDiff_const_smul ((Real.sqrt s)⁻¹))
  rw [heq, iteratedFDeriv_const_smul_apply' (a := (s ^ (-(d : ℝ) / 2) : ℝ))
    (f := fun y : Vec d => homogenizedGaussianKernel Q i 1 zero_lt_one 0
      ((Real.sqrt s)⁻¹ • y)) hg.contDiffAt,
    iteratedFDeriv_comp_const_smul _ hf, smul_smul]

/-- Unit-time coordinate derivatives retain Gaussian decay after absorbing
the polynomial factor; the constant is independent of the law and point. -/
theorem carverS_gaussian_unit_derivative_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (k : ℕ)
    (dirs : Fin k → Fin d) (x : Vec d) :
    ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
      (fun j => unitVector (dirs j))‖ ≤
      ((2 : ℝ) ^ (k ^ 2) * (1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀) ^ k *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d) *
        Real.exp (2 * sourceReducedBound Λ₀ * (k : ℝ) ^ 2)) *
      Real.exp (-euclideanNorm x ^ 2 / (8 * sourceReducedBound Λ₀)) := by
  let K := sourceReducedBound Λ₀
  let F := 1 + 2 * (d : ℝ) ^ 2 * K
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  have hK : 0 < K := by
    dsimp only [K]
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hr : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hG : ‖homogenizedGaussianKernel Q i 1 zero_lt_one 0 x‖ ≤
      P * Real.exp (-euclideanNorm x ^ 2 / (4 * K)) := by
    simpa [P, K, neg_div] using
      norm_homogenizedGaussianKernel_le_gaussian Q i 1 zero_lt_one
        (by norm_num) le_rfl 0 x
  have hD : ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x‖ ≤
      (2 : ℝ) ^ (k ^ 2) * (F * (1 + euclideanNorm x)) ^ k *
        ‖homogenizedGaussianKernel Q i 1 zero_lt_one 0 x‖ := by
    simpa only [norm_zero, add_zero, mul_one, F, K] using
      norm_iteratedFDeriv_homogenizedGaussianKernel_le Q i 1 zero_lt_one
        (by norm_num) 0 x k
  have hdir : ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
      (fun j => unitVector (dirs j))‖ ≤
      ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x‖ := by
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    apply mul_le_of_le_one_right (norm_nonneg _)
    simpa only [Finset.prod_const_one] using
      Finset.prod_le_prod₀ (s := Finset.univ) (g := fun _ : Fin k => (1 : ℝ))
        (fun j _ => norm_nonneg (unitVector (dirs j)))
        (fun j _ => by simp only [unitVector, Pi.norm_single, norm_one]; exact le_rfl)
  calc
    _ ≤ (2 : ℝ) ^ (k ^ 2) * (F * (1 + euclideanNorm x)) ^ k *
        (P * Real.exp (-euclideanNorm x ^ 2 / (4 * K))) :=
      hdir.trans (hD.trans (mul_le_mul_of_nonneg_left hG (by positivity)))
    _ = ((2 : ℝ) ^ (k ^ 2) * F ^ k * P) *
        ((1 + euclideanNorm x) ^ k * Real.exp (-euclideanNorm x ^ 2 / (4 * K))) := by
      rw [mul_pow]
      ring
    _ ≤ ((2 : ℝ) ^ (k ^ 2) * F ^ k * P) *
        (Real.exp (2 * K * (k : ℝ) ^ 2) *
          Real.exp (-euclideanNorm x ^ 2 / (8 * K))) :=
      mul_le_mul_of_nonneg_left
        (carverS_gaussian_polynomial_absorption hK (Real.sqrt_nonneg _) k) (by positivity)
    _ = _ := by dsimp only [F, P, K]; ring

/-- The exact scaling transports the unit-time bound to every positive
Gaussian time, with the required separate derivative and volume powers. -/
theorem carverS_gaussian_derivative_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
      (fun j => unitVector (dirs j))‖ ≤
      ((2 : ℝ) ^ (k ^ 2) * (1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀) ^ k *
        Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d) *
        Real.exp (2 * sourceReducedBound Λ₀ * (k : ℝ) ^ 2)) *
      s ^ (-(k : ℝ) / 2) *
      (s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm x ^ 2 / (8 * sourceReducedBound Λ₀ * s))) := by
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hpow : ((Real.sqrt s)⁻¹) ^ k = s ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hnorm : euclideanNorm ((Real.sqrt s)⁻¹ • x) ^ 2 =
      euclideanNorm x ^ 2 / s := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hsqrt), mul_pow,
      inv_pow, Real.sq_sqrt hs.le]
    ring
  have hexp : -euclideanNorm ((Real.sqrt s)⁻¹ • x) ^ 2 /
      (8 * sourceReducedBound Λ₀) =
      -euclideanNorm x ^ 2 / (8 * sourceReducedBound Λ₀ * s) := by
    rw [neg_div, hnorm]
    ring
  rw [carverS_homogenizedGaussianKernel_zero_derivative_scale,
    smul_apply, norm_smul, Real.norm_of_nonneg (by positivity), hpow]
  have h := mul_le_mul_of_nonneg_left
    (carverS_gaussian_unit_derivative_bound Q i k dirs ((Real.sqrt s)⁻¹ • x))
    (by positivity : 0 ≤ s ^ (-(d : ℝ) / 2) * ((Real.sqrt s)⁻¹) ^ k)
  rw [hpow, hexp] at h
  exact h.trans_eq (by ring)

/-- The literal cutoff times Gaussian derivative is a continuous,
integrable complex scalar kernel, including every translated block center. -/
theorem carverS_gaussian_block_kernel_integrable {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (χ : Vec d → ℝ)
    (hχ : Continuous χ) (hχcompact : HasCompactSupport χ) (x z : Vec d) :
    Continuous (fun y : Vec d => (χ (y - z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) ∧
    Integrable (fun y : Vec d => (χ (y - z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) := by
  have hχc : Continuous (fun y : Vec d => (χ (y - z) : ℂ)) :=
    Complex.continuous_ofReal.comp (hχ.comp (continuous_id.sub continuous_const))
  have hkernel : Continuous (fun y : Vec d =>
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))) := by
    simpa only [Function.comp_def, Pi.sub_apply, id_eq, neg_sub] using
      (continuous_gaussianDerivativeKernel Q i s hs k dirs).comp
      (continuous_id.sub continuous_const : Continuous (fun y : Vec d => y - x))
  have hcs : HasCompactSupport (fun y : Vec d => (χ (y - z) : ℂ)) :=
    (hχcompact.comp_homeomorph (Homeomorph.subRight z)).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  exact ⟨hχc.mul hkernel, (hχc.mul hkernel).integrable_of_hasCompactSupport hcs.mul_right⟩

/-- The cutoff block has the required Gaussian envelope mass. Its
constant depends only on dimension, ellipticity and derivative order. -/
theorem carverS_gaussian_block_kernel_mass {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (χ : Vec d → ℝ)
    (x z : Vec d) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hχ : Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ ρ})
    (hχone : ∀ y, |χ y| ≤ 1)
    (hk : Integrable (fun y : Vec d => (χ (y - z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j)))) :
    let C := (2 : ℝ) ^ (k ^ 2) *
      (1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀) ^ k *
      Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d) *
      Real.exp (2 * sourceReducedBound Λ₀ * (k : ℝ) ^ 2)
    let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (8 * sourceReducedBound Λ₀ * s))) ''
        {y : Vec d | euclideanNorm (y - z) ≤ ρ})
    (∫ y : Vec d, ‖(χ (y - z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun j => unitVector (dirs j))‖) ≤ C * (2 * ρ) ^ d * s ^ (-(k : ℝ) / 2) * W := by
  dsimp only
  let C := (2 : ℝ) ^ (k ^ 2) *
    (1 + 2 * (d : ℝ) ^ 2 * sourceReducedBound Λ₀) ^ k *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ₀ ^ d) *
    Real.exp (2 * sourceReducedBound Λ₀ * (k : ℝ) ^ 2)
  let E : Vec d → ℝ := fun y => s ^ (-(d : ℝ) / 2) *
    Real.exp (-euclideanNorm (x - y) ^ 2 / (8 * sourceReducedBound Λ₀ * s))
  let S := {y : Vec d | euclideanNorm (y - z) ≤ ρ}
  let W := sSup (E '' S)
  let kernel : Vec d → ℂ := fun y => (χ (y - z) : ℂ) *
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
      (fun j => unitVector (dirs j))
  change (∫ y, ‖kernel y‖) ≤ C * (2 * ρ) ^ d * s ^ (-(k : ℝ) / 2) * W
  have hK : 0 < sourceReducedBound Λ₀ := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ₀])
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hb : BddAbove (E '' S) := by
    refine ⟨s ^ (-(d : ℝ) / 2), ?_⟩
    rintro _ ⟨y, _, rfl⟩
    exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)))
      (Real.rpow_nonneg hs.le _)).trans_eq (mul_one _)
  have hEW (y : Vec d) (hy : y ∈ S) : E y ≤ W := le_csSup hb ⟨y, hy, rfl⟩
  have hz : z ∈ S := by
    change euclideanNorm (z - z) ≤ ρ
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  have hW : 0 ≤ W := (by dsimp only [E]; positivity : 0 ≤ E z).trans (hEW z hz)
  have hsupp : Function.support kernel ⊆ S := by
    intro y hy
    have hχnz : χ (y - z) ≠ 0 := by
      intro he
      apply hy
      simp only [kernel, he, Complex.ofReal_zero, zero_mul]
    exact hχ hχnz
  have hbound (y : Vec d) (hy : y ∈ S) : ‖kernel y‖ ≤ C * s ^ (-(k : ℝ) / 2) * W := by
    calc
      _ ≤ ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
          (fun j => unitVector (dirs j))‖ := by
        dsimp only [kernel]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχone _)
      _ ≤ C * s ^ (-(k : ℝ) / 2) * E y := carverS_gaussian_derivative_bound Q i s hs k dirs (x - y)
      _ ≤ _ := mul_le_mul_of_nonneg_left (hEW y hy) (by positivity)
  exact (carverS_supported_kernel_mass_le kernel hk z hρ (by positivity) hsupp hbound).trans_eq (by ring)

/-- Structural cutoff mass constants preserve any prescribed Gaussian width. -/
theorem carverS_cutoff_gaussian_derivative_mass (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (Cbase : ℝ) (hCbase : 1 ≤ Cbase) :
    ∃ Cenv : ℝ, Cbase ≤ Cenv ∧ 1 ≤ Cenv ∧ ∃ Cder : ℕ → ℝ,
      (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (s : ℝ),
      1 ≤ s → ∀ hs : 0 < s, ∀ (k : ℕ) (dirs : Fin k → Fin d) (r : ℝ),
      1 ≤ r → ∀ (x z : Vec d) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      Function.support χ ⊆ {y : Vec d |
        euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} →
      (∀ y, |χ y| ≤ 1) →
      let kernel := fun y : Vec d => χ (y - z) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
          (x - y) (fun j => unitVector (dirs j))
      let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
          {y : Vec d | euclideanNorm (y - z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
      Integrable kernel ∧ (∫ y : Vec d, ‖kernel y‖) ≤
        Cder k * r ^ (d : ℝ) * s ^ (-(k : ℝ) / 2) * W := by
  let K := sourceReducedBound D.ellipticity
  let R := 2 * Real.sqrt (d : ℝ) + 2
  let Cenv := max Cbase (8 * K)
  let C : ℕ → ℝ := fun k => (2 : ℝ) ^ (k ^ 2) *
    (1 + 2 * (d : ℝ) ^ 2 * K) ^ k *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d) *
    Real.exp (2 * K * (k : ℝ) ^ 2)
  let Cder : ℕ → ℝ := fun k => max 1 (C k * (2 * R) ^ d)
  have hK : 0 < K := by
    dsimp only [K]
    unfold sourceReducedBound
    have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
    positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hCenv : 0 < Cenv :=
    zero_lt_one.trans_le (hCbase.trans (le_max_left _ _))
  refine ⟨Cenv, le_max_left _ _, hCbase.trans (le_max_left _ _), Cder,
    (fun k => le_max_left _ _), ?_⟩
  intro Q s _hs hs k dirs r hr x z χ hχ hχc hχs hχone
  dsimp only
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hρ : 0 ≤ R * r := mul_nonneg hR.le hr0
  obtain ⟨hkc, hki⟩ := carverS_gaussian_block_kernel_integrable Q
    ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ s hs k dirs χ hχ.continuous hχc x z
  refine ⟨hki, ?_⟩
  let S := {y : Vec d | euclideanNorm (y - z) ≤ R * r}
  let W := sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
    Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) '' S)
  have hz : z ∈ S := by
    change euclideanNorm (z - z) ≤ R * r
    simpa [euclideanNorm, euclideanSq, dot] using hρ
  have hm := carverS_gaussian_block_kernel_mass Q
    ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hd⟩ s hs k dirs χ x z hρ hχs hχone hki
  have hmono := carverS_gaussian_envelope_mono x S ⟨z, hz⟩ hs
    (by positivity : 0 < 8 * K) (le_max_right Cbase (8 * K))
  have hW : 0 ≤ W := by
    have hb : BddAbove ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) '' S) := by
      refine ⟨s ^ (-(d : ℝ) / 2), ?_⟩
      rintro _ ⟨y, _, rfl⟩
      exact (mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
          (mul_pos hCenv hs).le)) (Real.rpow_nonneg hs.le _)).trans_eq (mul_one _)
    exact (by positivity : 0 ≤ s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - z) ^ 2 / (Cenv * s))).trans
        (le_csSup hb ⟨z, hz, rfl⟩)
  have hC : 0 ≤ C k := by dsimp only [C]; positivity
  change _ ≤ Cder k * r ^ (d : ℝ) * s ^ (-(k : ℝ) / 2) * W
  rw [Real.rpow_natCast]
  calc
    _ ≤ C k * (2 * (R * r)) ^ d * s ^ (-(k : ℝ) / 2) *
        sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm (x - y) ^ 2 / (8 * K * s))) '' S) := hm
    _ = C k * (2 * R) ^ d * r ^ d * s ^ (-(k : ℝ) / 2) *
        sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm (x - y) ^ 2 / (8 * K * s))) '' S) := by
      rw [show 2 * (R * r) = (2 * R) * r by ring, mul_pow]
      ring
    _ ≤ C k * (2 * R) ^ d * r ^ d * s ^ (-(k : ℝ) / 2) * W :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right 1 (C k * (2 * R) ^ d))
          (pow_nonneg hr0 _)) (Real.rpow_nonneg hs.le _)) hW

/-- A structural time threshold makes every annular locality radius large
enough for the actual endpoint locality theorem. -/
theorem carverS_annular_radius_large {t η C R : ℝ}
    (ht : 1 ≤ t) (hη : 0 < η) (hC : 0 ≤ C) (hR : 1 ≤ R)
    (htC : C ^ η⁻¹ ≤ t) (n : ℕ) :
    C * Real.sqrt t ≤ R * 2 ^ n * t ^ (1 / 2 + η) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hCt : C ≤ t ^ η := (Real.rpow_inv_le_iff_of_pos hC ht0.le hη).mp htC
  calc
    _ ≤ t ^ η * Real.sqrt t := mul_le_mul_of_nonneg_right hCt (Real.sqrt_nonneg _)
    _ = t ^ (1 / 2 + η) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht0]
      congr 1
      ring
    _ ≤ _ := le_mul_of_one_le_left (Real.rpow_nonneg ht0.le _)
      (one_le_mul_of_one_le_of_one_le hR (one_le_pow₀ (by norm_num)))

/-- Squaring the buffered radius gives exactly the superexponential annular
rate appearing in the target conditional expectation estimate. -/
theorem carverS_annular_radius_sq_div {t : ℝ} (ht : 0 < t)
    (η R : ℝ) (n : ℕ) :
    (R * 2 ^ n * t ^ (1 / 2 + η)) ^ 2 / t =
      R ^ 2 * 4 ^ n * t ^ (2 * η) := by
  have htwo : ((2 : ℝ) ^ n) ^ 2 = 4 ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have htow : (t ^ (1 / 2 + η)) ^ 2 = t * t ^ (2 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num only [Nat.cast_ofNat]
    have he : (1 / 2 + η) * (2 : ℝ) = 1 + 2 * η := by ring
    rw [he, Real.rpow_add ht, Real.rpow_one]
  rw [mul_pow, mul_pow, htwo, htow]
  field_simp

/-- The locality polynomial, force factor and spatial decay can be
absorbed into one enlarged structural localization constant. -/
theorem carverS_locality_factor_absorption {t Cdet b q Cloc : ℝ}
    (ht : 1 ≤ t) (ζ : ℂ) (N : ℕ) (hN : (N : ℝ) ≤ Cloc)
    (hCdet : Cdet + 1 ≤ Cloc) (hq : 0 ≤ q) (hb : 1 / Cloc ≤ b) :
    (1 + 2 * ‖ζ‖) * (2 + t) ^ N * Real.exp (Cdet * ‖ζ‖ ^ 2 * t - b * q) ≤
      3 * (2 + t) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * t - q / Cloc) := by
  have ht0 : 0 ≤ t := zero_le_one.trans ht
  have hpow : (2 + t) ^ N ≤ (2 + t) ^ Cloc := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hN
  have he : (Cdet + 1) * ‖ζ‖ ^ 2 * t - b * q ≤
      Cloc * ‖ζ‖ ^ 2 * t - q / Cloc := by
    have hforce := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCdet (sq_nonneg ‖ζ‖)) ht0
    have hdecay := mul_le_mul_of_nonneg_right hb hq
    have hid : (1 / Cloc) * q = q / Cloc := by ring
    rw [hid] at hdecay
    linarith only [hforce, hdecay]
  calc
    _ ≤ (3 * Real.exp (‖ζ‖ ^ 2 * t)) * (2 + t) ^ N *
        Real.exp (Cdet * ‖ζ‖ ^ 2 * t - b * q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (carverS_flux_force_factor_le ht ζ) (by positivity))
        (Real.exp_pos _).le
    _ = 3 * (2 + t) ^ N *
        Real.exp ((Cdet + 1) * ‖ζ‖ ^ 2 * t - b * q) := by
      rw [show (Cdet + 1) * ‖ζ‖ ^ 2 * t - b * q =
        ‖ζ‖ ^ 2 * t + (Cdet * ‖ζ‖ ^ 2 * t - b * q) by ring, Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul
      (mul_le_mul_of_nonneg_left hpow (by norm_num)) (Real.exp_le_exp.mpr he)
      (Real.exp_pos _).le (by positivity)

/-- The superexponential annular tail has exactly the weights used by the
actual buffered conditional blocks. -/
theorem carverS_summable_annular_tail (d : ℕ) {t η Cloc : ℝ}
    (ht : 0 < t) (hCloc : 0 < Cloc) :
    Summable (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * t ^ (2 * η) / Cloc)) := by
  have hc : 0 < t ^ (2 * η) / Cloc :=
    div_pos (Real.rpow_pos_of_pos ht _) hCloc
  simpa only [mul_div_assoc] using
    EinsteinFull.Calculus.K4.summable_two_rpow_mul_exp_neg_four_pow d hc


/-- The actual cutoff blocks retain their original norm bound while their centered
conditional expectation errors have the common annular localization rate. -/
theorem carverS_actual_block_annular_localization_with_block_bound :
    EinsteinFull.Blueprint.node_e_u3A_flux_u2D_blockStmt →
    EinsteinFull.Blueprint.node_e_u3A_forced_u2D_localityStmt →
    EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_parametersStmt → ∀ (d : ℕ) (hd : 2 ≤ d) (D :
    StructuralData d), ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧ η = κ / (16 * ((d
    : ℝ) + 2)) ∧ η₀ = η / 4 ∧ ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ Cloc : ℝ, ∃ Cder : ℕ → ℝ, 0 < growth₀ ∧ 1 ≤ t₀ ∧
    1 ≤ Cloc ∧ (∀ k, 1 ≤ Cder k) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ :
    HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ
    : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw
    Q), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν :
    EndpointIndex d, ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q), (∀ t : ℝ≥0, 0 < (t : ℝ) →
    IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧ ∀ (t : ℝ≥0), t₀ ≤
    (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ → ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K → MemLp
    (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p)
    (reducedLaw Q)).toReal ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) * (((t : ℝ) / 8) ^ (-(1 / 2 + (d
    : ℝ) / 4)) + ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) → ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s, ∀ (k : ℕ) (dirs :
    Fin k → Fin d),
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let kernel := fun y :
      Vec d => iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) y (fun j => unitVector
      (dirs j))
    let W := fun (x z : Vec d) => sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) * Real.exp
      (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) '' {y : Vec d | euclideanNorm (y - z) ≤ R * r})
    ∀ χ : Vec d →
    ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R *
    r} → (∀ y, |χ y| ≤ 1) → (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
    let B := fun (x z : Vec d) (j : Fin d) => ∫ y : Vec d, (χ (y - z) * kernel (x - y)) • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
    (∀ (x z : Vec d) (j : Fin d), MemLp (B x z j :
    FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧ (eLpNorm (B x z j : FieldPair d → ℂ)
    (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t
    : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) * r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) * (1 + (t : ℝ) / s) ^
    Lblock k * W x z) ∧ ((∀ y : Vec d, (∑' z : Fin d → ℤ, χ (y - fun j => r * (z j : ℝ))) = 1) → ∀ (x : Vec
    d) (j : Fin d),
    let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j : ℝ)
    let X := fun (z : Fin d →
      ℤ) => (centeredComplexLp Q (B x (center z) j) : FieldPair d → ℂ)
    let CE := fun (n : ℕ) (z : Fin d → ℤ)
      => (reducedLaw Q)[X z | localSigma {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r}]
    let A := fun (n : ℕ) (z : Fin d → ℤ) => CE (n + 1) z - CE n z
    let N := fun f : FieldPair d → ℂ => (eLpNorm f
      (ENNReal.ofReal p) (reducedLaw Q)).toReal
    Summable (fun n : ℕ => 2 ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp
    (-4 ^ n * (t : ℝ) ^ (2 * η) / Cloc)) ∧ (∀ (n : ℕ) (z : Fin d → ℤ), MemLp (X z - CE n z) (ENNReal.ofReal
    p) (reducedLaw Q) ∧ N (X z - CE n z) ≤ Cder k * (2 + (t : ℝ)) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * (t :
    ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) * r ^ d * s ^ (-(k : ℝ) / 2) * W x (center z))) := by
  classical
  intro hblock hlocal _hparameters d hd D
  obtain ⟨κ, η, η₀, Cold, Lblock, hκ, hκlt, hCold, hη, hη₀, hblock⟩ := hblock d hd D
  obtain ⟨Cdet, c, N, hCdet, hc, hlocal⟩ := carverS_actual_flux_locality hlocal d hd D
  obtain ⟨Cenv, hColdCenv, hCenv, Cmass, hCmass, hmass⟩ :=
    carverS_cutoff_gaussian_derivative_mass d hd D Cold hCold
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let M : ℝ := Real.exp (2 * D.ellipticity) * D.ellipticity +
    sourceReducedBound D.ellipticity
  have hR : 1 ≤ R := by dsimp only [R]; linarith [Real.sqrt_nonneg (d : ℝ)]
  have hM : 0 ≤ M := by
    have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
    dsimp only [M]
    unfold sourceReducedBound
    positivity
  have hCdet0 : 0 ≤ Cdet := zero_le_one.trans hCdet
  have hηpos : 0 < η := by rw [hη]; exact div_pos hκ (by positivity)
  have hcR : 0 < c * R ^ 2 := mul_pos hc (sq_pos_of_pos (zero_lt_one.trans_le hR))
  let Cloc : ℝ := max 1 (max (N : ℝ) (max (Cdet + 1) (1 / (c * R ^ 2))))
  have hCloc : 1 ≤ Cloc := le_max_left _ _
  have hClocRest : max (N : ℝ) (max (Cdet + 1) (1 / (c * R ^ 2))) ≤ Cloc :=
    le_max_right _ _
  have hClocN : (N : ℝ) ≤ Cloc := (le_max_left _ _).trans hClocRest
  have hClocD : Cdet + 1 ≤ Cloc :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hClocRest)
  have hClocI : 1 / (c * R ^ 2) ≤ Cloc :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hClocRest)
  have hrate : 1 / Cloc ≤ c * R ^ 2 := by
    simpa only [one_div_one_div] using
      one_div_le_one_div_of_le (one_div_pos.mpr hcR) hClocI
  refine ⟨κ, η, η₀, Cenv, Lblock, hκ, hκlt, hCenv, hη, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, told, CderOld, hgrowth₀, htold, hCderOld, hblock⟩ := hblock p hp
  let t₀ : ℝ := max told (Cdet ^ η⁻¹)
  let Cder : ℕ → ℝ := fun k => max (CderOld k) (12 * (d : ℝ) * M * Cdet * Cmass k)
  have hCder (k : ℕ) : 1 ≤ Cder k := (hCderOld k).trans (le_max_left _ _)
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  refine ⟨growth₀, t₀, Cloc, Cder, hgrowth₀,
    htold.trans (le_max_left _ _), hCloc, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hblock⟩ := hblock Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hζ growth K hgrowth hK hMem hNorm s hss hs k dirs
  have htold' : told ≤ (t : ℝ) := (le_max_left _ _).trans ht
  have ht1 : 1 ≤ (t : ℝ) := htold.trans htold'
  have htpos : 0 < (t : ℝ) := zero_lt_one.trans_le ht1
  have htC : Cdet ^ η⁻¹ ≤ (t : ℝ) := (le_max_right _ _).trans ht
  let r : ℝ := (t : ℝ) ^ (1 / 2 + η)
  have hr : 1 ≤ r := Real.one_le_rpow ht1 (by linarith)
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hRr : 0 ≤ R * r := mul_nonneg (zero_le_one.trans hR) hr0
  let kernel : Vec d → ℂ := fun y =>
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
      y (fun j => unitVector (dirs j))
  let W : Vec d → Vec d → ℝ := fun x z => sSup
    ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) ''
        {y : Vec d | euclideanNorm (y - z) ≤ R * r})
  dsimp only
  intro χ hχ hχcompact hχsupport hχone hχder
  let blockKernel : Vec d → Vec d → Vec d → ℂ := fun x z y =>
    (χ (y - z) : ℂ) * kernel (x - y)
  let B : Vec d → Vec d → Fin d → Lp ℂ 2 (reducedLaw Q) := fun x z j =>
    ∫ y : Vec d, blockKernel x z y • complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) y (J t j)
  have hmass' (x z : Vec d) : Integrable (blockKernel x z) ∧
      (∫ y : Vec d, ‖blockKernel x z y‖) ≤
        Cmass k * r ^ d * s ^ (-(k : ℝ) / 2) * W x z := by
    simpa only [Real.rpow_natCast] using
      hmass Q s hss hs k dirs r hr x z χ hχ hχcompact hχsupport hχone
  have hW (x z : Vec d) : 0 ≤ W x z := by
    have hpre : 0 < Cmass k * r ^ d * s ^ (-(k : ℝ) / 2) := by
      have hCmasspos : 0 < Cmass k := zero_lt_one.trans_le (hCmass k)
      have hrpos : 0 < r := zero_lt_one.trans_le hr
      positivity
    exact nonneg_of_mul_nonneg_right
      ((integral_nonneg fun y => norm_nonneg (blockKernel x z y)).trans (hmass' x z).2) hpre
  have hWmono (x z : Vec d) :
      sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - y) ^ 2 / (Cold * s))) ''
          {y : Vec d | euclideanNorm (y - z) ≤ R * r}) ≤ W x z := by
    apply carverS_gaussian_envelope_mono x _ _ hs (zero_lt_one.trans_le hCold) hColdCenv
    refine ⟨z, ?_⟩
    simpa [euclideanNorm, euclideanSq, dot] using hRr
  have hB := hblock t htold' hζ growth K hgrowth hK hMem hNorm
    s hss hs k dirs χ hχ hχcompact hχsupport hχone hχder
  have hBnew (x z : Vec d) (j : Fin d) :
      MemLp (B x z j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (B x z j : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Cder k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
          (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
          r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
          (1 + (t : ℝ) / s) ^ Lblock k * W x z := by
    refine ⟨(hB x z j).1, (hB x z j).2.trans ?_⟩
    have hW0 : 0 ≤ W x z := hW x z
    have hCold0 : 0 ≤ CderOld k := zero_le_one.trans (hCderOld k)
    have hK0 : 0 ≤ K := zero_le_one.trans hK
    have hsBase : 0 ≤ 1 + (t : ℝ) / s := by positivity
    calc
      _ ≤ CderOld k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
          (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
          r ^ ((d : ℝ) + 1 - κ) * s ^ (-(k : ℝ) / 2) *
          (1 + (t : ℝ) / s) ^ Lblock k * W x z := by
        exact mul_le_mul_of_nonneg_left (hWmono x z) (by positivity)
      _ ≤ _ := by
        gcongr
        exact le_max_left _ _
  refine ⟨hBnew, ?_⟩
  intro _hpartition x j
  refine ⟨carverS_summable_annular_tail d htpos (zero_lt_one.trans_le hCloc), ?_⟩
  intro n z
  let z₀ : Vec d := fun i => r * (z i : ℝ)
  let ρ : ℝ := R * 2 ^ n * r
  have hρ : Cdet * Real.sqrt (t : ℝ) ≤ ρ :=
    carverS_annular_radius_large ht1 hηpos hCdet0 hR htC n
  obtain ⟨F, hF, herr⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
    ν t ht1 (G t) (J t) (hflux t htpos) ρ hρ
  let ε : ℝ := (d : ℝ) * M * (1 + 2 * ‖ζ‖) *
    (Cdet * (2 + (t : ℝ)) ^ N *
      Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)))
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have herrj : ∀ᵐ ω ∂reducedLaw Q, ‖J t j ω - F j ω‖ ≤ ε :=
    herr.mono fun ω hω => hω j
  have hcont : Continuous (blockKernel x z₀) :=
    (carverS_gaussian_block_kernel_integrable Q ⟨0, by omega⟩ s hs k dirs
      χ hχ.continuous hχcompact x z₀).1
  have hsupp : Function.support (blockKernel x z₀) ⊆
      {y : Vec d | euclideanNorm (y - z₀) ≤ R * r} := by
    intro y hy
    apply hχsupport
    intro hzero
    apply hy
    simp [blockKernel, hzero]
  obtain ⟨hCE, hCEbound⟩ := carverS_buffered_block_condExp_bound Q hp1 hRr n z₀
    (blockKernel x z₀) (hmass' x z₀).1 hcont hsupp (J t j) (F j) (hF j)
      hε herrj (hBnew x z₀ j).1
  refine ⟨hCE, hCEbound.trans ?_⟩
  have hW0 : 0 ≤ W x z₀ := hW x z₀
  have hdecay : c * ρ ^ 2 / (t : ℝ) =
      (c * R ^ 2) * (4 ^ n * (t : ℝ) ^ (2 * η)) := by
    dsimp only [ρ, r]
    rw [mul_div_assoc, carverS_annular_radius_sq_div htpos]
    ring
  have habs : (1 + 2 * ‖ζ‖) * (2 + (t : ℝ)) ^ N *
      Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ)) ≤
      3 * (2 + (t : ℝ)) ^ Cloc *
        Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) := by
    rw [hdecay]
    exact carverS_locality_factor_absorption ht1 ζ N hClocN hClocD (by positivity) hrate
  have hcoeff : 0 ≤ 4 * (d : ℝ) * M * Cdet * Cmass k := by
    have hmass0 : 0 ≤ Cmass k := zero_le_one.trans (hCmass k)
    positivity
  calc
    4 * (ε * ∫ y : Vec d, ‖blockKernel x z₀ y‖) ≤
        4 * (ε * (Cmass k * r ^ d * s ^ (-(k : ℝ) / 2) * W x z₀)) := by
      gcongr
      exact (hmass' x z₀).2
    _ = (4 * (d : ℝ) * M * Cdet * Cmass k) *
        ((1 + 2 * ‖ζ‖) * (2 + (t : ℝ)) ^ N *
          Real.exp (Cdet * ‖ζ‖ ^ 2 * (t : ℝ) - c * ρ ^ 2 / (t : ℝ))) *
        r ^ d * s ^ (-(k : ℝ) / 2) * W x z₀ := by dsimp only [ε]; ring
    _ ≤ (4 * (d : ℝ) * M * Cdet * Cmass k) *
        (3 * (2 + (t : ℝ)) ^ Cloc *
          Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc)) *
        r ^ d * s ^ (-(k : ℝ) / 2) * W x z₀ := by
      gcongr
    _ = (12 * (d : ℝ) * M * Cdet * Cmass k) * (2 + (t : ℝ)) ^ Cloc *
        Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) *
        r ^ d * s ^ (-(k : ℝ) / 2) * W x z₀ := by ring
    _ ≤ _ := by
      gcongr
      exact le_max_right _ _

set_option linter.unusedVariables false in
/-- Projection of the joint block estimate to actual annular localization. -/
theorem carverS_actual_block_annular_localization : EinsteinFull.Blueprint.node_e_u3A_flux_u2D_blockStmt →
    EinsteinFull.Blueprint.node_e_u3A_forced_u2D_localityStmt →
    EinsteinFull.Blueprint.node_l_u3A_forced_u2D_flux_u23_parametersStmt → ∀ (d : ℕ) (hd : 2 ≤ d) (D :
    StructuralData d), ∃ κ η η₀ Cenv : ℝ, ∃ Lblock : ℕ → ℕ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ Cenv ∧ η = κ / (16 * ((d
    : ℝ) + 2)) ∧ η₀ = η / 4 ∧ ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ Cloc : ℝ, ∃ Cder : ℕ → ℝ, 0 < growth₀ ∧ 1 ≤ t₀ ∧
    1 ≤ Cloc ∧ (∀ k, 1 ≤ Cder k) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ :
    HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ
    : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
    IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw
    Q), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν :
    EndpointIndex d, ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q), (∀ t : ℝ≥0, 0 < (t : ℝ) →
    IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧ ∀ (t : ℝ≥0), t₀ ≤
    (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ → ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K → MemLp
    (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
    (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p)
    (reducedLaw Q)).toReal ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) * (((t : ℝ) / 8) ^ (-(1 / 2 + (d
    : ℝ) / 4)) + ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) → ∀ (s : ℝ), 1 ≤ s → ∀ hs : 0 < s, ∀ (k : ℕ) (dirs :
    Fin k → Fin d),
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 2
    let kernel := fun y :
      Vec d => iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) y (fun j => unitVector
      (dirs j))
    let W := fun (x z : Vec d) => sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) * Real.exp
      (-euclideanNorm (x - y) ^ 2 / (Cenv * s))) '' {y : Vec d | euclideanNorm (y - z) ≤ R * r})
    ∀ χ : Vec d →
    ℝ, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ → Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R *
    r} → (∀ y, |χ y| ≤ 1) → (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
    let B := fun (x z : Vec d) (j : Fin d) => ∫ y : Vec d, (χ (y - z) * kernel (x - y)) • complexTranslation
      (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)
    (∀ y : Vec d, (∑' z : Fin d → ℤ, χ (y - fun j => r *
    (z j : ℝ))) = 1) → ∀ (x : Vec d) (j : Fin d),
    let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j
      : ℝ)
    let X := fun (z : Fin d → ℤ) => (centeredComplexLp Q (B x (center z) j) : FieldPair d → ℂ)
    let CE
      := fun (n : ℕ) (z : Fin d → ℤ) => (reducedLaw Q)[X z | localSigma {y : Vec d | euclideanNorm (y - center
      z) < R * 2 ^ (n + 1) * r}]
    let A := fun (n : ℕ) (z : Fin d → ℤ) => CE (n + 1) z - CE n z
    let N := fun f
      : FieldPair d → ℂ => (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal
    Summable (fun n : ℕ => 2 ^ ((n
    : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * (t : ℝ) ^ (2 * η) / Cloc)) ∧ (∀ (n : ℕ) (z : Fin d → ℤ), MemLp
    (X z - CE n z) (ENNReal.ofReal p) (reducedLaw Q) ∧ N (X z - CE n z) ≤ Cder k * (2 + (t : ℝ)) ^ Cloc *
    Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) * r ^ d * s ^ (-(k : ℝ) / 2) * W
    x (center z)) := by
  intro hblock hlocal hparameters d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ, hκlt, hCenv, hη, hη₀, hjoint⟩ :=
    carverS_actual_block_annular_localization_with_block_bound hblock hlocal hparameters d hd D
  refine ⟨κ, η, η₀, Cenv, Lblock, hκ, hκlt, hCenv, hη, hη₀, ?_⟩
  intro p hp
  obtain ⟨growth₀, t₀, Cloc, Cder, hgrowth₀, ht₀, hCloc, hCder, hjoint⟩ := hjoint p hp
  refine ⟨growth₀, t₀, Cloc, Cder, hgrowth₀, ht₀, hCloc, hCder, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hjoint⟩ := hjoint Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hζ growth K hgrowth hK hMem hNorm s hss hs k dirs
  dsimp only
  intro χ hχ hχcompact hχsupport hχone hχder
  exact (hjoint t ht hζ growth K hgrowth hK hMem hNorm s hss hs k dirs
    χ hχ hχcompact hχsupport hχone hχder).2

end EinsteinFull.Blueprint
