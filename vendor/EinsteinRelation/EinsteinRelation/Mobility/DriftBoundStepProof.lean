import EinsteinRelation.Mobility.DriftDecompositionFromSteps
import EinsteinRelation.Calculus.EnvironmentWeakCalculusUniqueness
import EinsteinRelation.Entropy.DivergenceFromFisher

/-! # The drift bound from a fixed weak divergence

Source: `paper/main.tex` 1144-1146. `DriftBoundStep` asks that the drift
`b_i^λ = ½ D·(a e_i) + λ e₁·a e_i` be essentially bounded under the reduced reference law, for
every weak horizontal divergence `D·(a e_i)` of the `i`-th column of the reduced coefficient.

Two weak horizontal divergences of the same field agree almost everywhere under a stationary
probability law (`HasWeakHorizontalDivergence.ae_unique`). The drift bound therefore reduces to a
pointwise bound on one fixed divergence `cdiv i`, together with a bound on the first-row entry of
the reduced coefficient. Both inputs are stated as hypotheses of `driftBoundStep_of_cdiv`.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinRelation

open Carriers

/-- Two weak horizontal divergences of the same field agree almost everywhere under a stationary
probability law. The proof mirrors `HasWeakHorizontalGradient.ae_unique`: both identities test the
same family of L²(Q) derivatives of a horizontally smooth test, so the two pairings with every
bounded orbit core coincide, and bounded orbit cores separate integrable classes. -/
theorem HasWeakHorizontalDivergence.ae_unique {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {V : FieldPair d → Vec d}
    {h h' : FieldPair d → ℝ}
    (hw : HasWeakHorizontalDivergence Q hQ V h)
    (hw' : HasWeakHorizontalDivergence Q hQ V h') : h =ᵐ[Q] h' := by
  have hint : Integrable (fun ω => h ω - h' ω) Q := hw.2.1.sub' hw'.2.1
  -- Against a bounded orbit core `H`, both weak identities test the same derivative family of
  -- `H`, so the two pairings `∫ h · H` and `∫ h' · H` coincide.
  have hfun : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, (h ω - h' ω) * H ω ∂Q) = 0 := by
    intro H hH
    obtain ⟨M, -, hM⟩ := hH.bound_orbit
    have hHm : AEStronglyMeasurable H Q := hH.1.aestronglyMeasurable
    have hHb : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ M :=
      Filter.Eventually.of_forall fun ω => by
        simpa only [Real.norm_eq_abs, orbit_zero] using hM ω 0
    have hI : Integrable (fun ω => h ω * H ω) Q := hw.2.1.mul_bdd hHm hHb
    have hI' : Integrable (fun ω => h' ω * H ω) Q := hw'.2.1.mul_bdd hHm hHb
    have hFsm := hH.isHorizontallySmoothTest Q hQ
    have hA := hw.2.2 _ hFsm _ (fun j => hH.hasHorizontalLpDerivative_toLp Q hQ j)
    have hB := hw'.2.2 _ hFsm _ (fun j => hH.hasHorizontalLpDerivative_toLp Q hQ j)
    have e := neg_inj.mp (hA.symm.trans hB)
    have hFH := (hH.memLp Q 2).coeFn_toLp
    have hA2 : (∫ ω, h ω * ((hH.memLp Q 2).toLp H) ω ∂Q) = ∫ ω, h ω * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hFH] with ω hω
      rw [hω]
    have hB2 : (∫ ω, h' ω * ((hH.memLp Q 2).toLp H) ω ∂Q) = ∫ ω, h' ω * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [hFH] with ω hω
      rw [hω]
    have hAB : (∫ ω, h ω * H ω ∂Q) = ∫ ω, h' ω * H ω ∂Q :=
      hA2.symm.trans (e.trans hB2)
    have hsplit : (∫ ω, (h ω - h' ω) * H ω ∂Q) =
        (∫ ω, h ω * H ω ∂Q) - ∫ ω, h' ω * H ω ∂Q := by
      have hpoint : (fun ω => (h ω - h' ω) * H ω) =
          fun ω => h ω * H ω - h' ω * H ω := by
        funext ω
        ring
      rw [hpoint]
      exact integral_sub hI hI'
    exact hsplit.trans (sub_eq_zero.mpr hAB)
  -- Pass from the function `h - h'` to its `L¹(Q)` class, which pairs to zero with every bounded
  -- orbit core.
  have hpairL1 : ∀ H : FieldPair d → ℝ, IsHorizontalTest H →
      (∫ ω, (Integrable.toL1 (fun ω => h ω - h' ω) hint) ω * H ω ∂Q) = 0 := by
    intro H hH
    have hcongr : (∫ ω, (Integrable.toL1 (fun ω => h ω - h' ω) hint) ω * H ω ∂Q) =
        ∫ ω, (h ω - h' ω) * H ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [Integrable.coeFn_toL1 hint] with ω hω
      rw [hω]
    exact hcongr.trans (hfun H hH)
  have hg0 : Integrable.toL1 (fun ω => h ω - h' ω) hint = 0 :=
    eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ
      (Integrable.toL1 (fun ω => h ω - h' ω) hint) hpairL1
  filter_upwards [Integrable.coeFn_toL1 hint, Lp.coeFn_zero ℝ 1 Q] with ω hω hz
  have hzω : (Integrable.toL1 (fun ω => h ω - h' ω) hint) ω = 0 :=
    (congrArg (fun z : Lp ℝ 1 Q => z ω) hg0).trans hz
  exact sub_eq_zero.mp (hω.symm.trans hzω)

/-- Scalar estimate for the drift: if `|x| ≤ L`, `|y| ≤ K` and `0 < λ ≤ 1`, then
`|½ x + λ y| ≤ ½ L + K`. -/
private theorem abs_half_add_mul_le_of_bounds {x y lam L K : ℝ} (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hx : |x| ≤ L) (hy : |y| ≤ K) :
    |(1 / 2 : ℝ) * x + lam * y| ≤ (1 / 2 : ℝ) * L + K := by
  have h1 : |(1 / 2 : ℝ) * x| ≤ (1 / 2 : ℝ) * L := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left hx (by norm_num)
  have h2 : |lam * y| ≤ K := by
    rw [abs_mul, abs_of_pos hlam]
    calc lam * |y| ≤ 1 * |y| := mul_le_mul_of_nonneg_right hlam1 (abs_nonneg y)
      _ = |y| := one_mul _
      _ ≤ K := hy
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

/-- `DriftBoundStep` from a fixed weak divergence `cdiv i` of the `i`-th column of the reduced
coefficient. The inputs are:

* `hH5`: `cdiv i` is a weak horizontal divergence of `w ↦ (w.1 0) e_i` under the reduced reference
  law;
* `hdivBound`: `cdiv i` is essentially bounded by `d L` for some constant `L` depending on the law;
* `hentryBound`: the first-row entry `(w.1 0) e₁ · e_i` of the reduced coefficient is essentially bounded
  for some constant `K` depending on the law.

Every weak divergence `D·(a e_i)` equals `cdiv i` almost everywhere, so its drift is bounded by
`½ d L + K` almost everywhere, since `0 < λ ≤ 1`. -/
theorem driftBoundStep_of_cdiv (cdiv : ∀ {d : ℕ}, Fin d → FieldPair d → ℝ)
    (hH5 : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
      (hQ : IsStationary (reducedReferenceLaw Q)) (i : Fin d),
      HasWeakHorizontalDivergence (reducedReferenceLaw Q) hQ
        (fun ω : FieldPair d => (ω.1 0).mulVec (unitVector i)) (cdiv i))
    (hdivBound : ∀ (d : ℕ) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
      ∃ L : ℝ, ∀ᵐ w ∂reducedReferenceLaw Q, |cdiv i w| ≤ (d : ℝ) * L)
    (hentryBound : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d),
      ∃ K : ℝ, ∀ᵐ w ∂reducedReferenceLaw Q, |(w.1 0) (firstIdx hd) i| ≤ K) :
    DriftBoundStep := by
  intro d hd Λ₀ r₀ Q lam hlam hlam1 hQ i divA hdiv
  haveI : IsProbabilityMeasure (reducedReferenceLaw Q) :=
    Entropy.reducedReferenceLaw_isProbabilityMeasure Q
  obtain ⟨L, hL⟩ := hdivBound d Λ₀ r₀ Q i
  obtain ⟨K, hK⟩ := hentryBound d hd Λ₀ r₀ Q i
  have hcd := hH5 d hd Λ₀ r₀ Q hQ i
  have hae : divA =ᵐ[reducedReferenceLaw Q] cdiv i :=
    HasWeakHorizontalDivergence.ae_unique hdiv hcd
  refine ⟨(1 / 2 : ℝ) * ((d : ℝ) * L) + K, ?_⟩
  filter_upwards [hae, hL, hK] with w hw hLw hKw
  simp only [velocityDrift]
  rw [hw]
  exact abs_half_add_mul_le_of_bounds hlam hlam1 hLw hKw

end EinsteinRelation
