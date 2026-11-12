import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

/-! # Identification of convergent flow gradients

Source: `paper/main.tex:808–816`. The integrated parabolic equation has
residual `u(T) = div(a(eᵢ + D∫₀ᵀu))`. If this residual tends to zero in
scalar `L²`, every strong limit of the integrated gradients is the canonical
variational gradient. The closed potential space and its uniqueness theorem
are used explicitly. Construction and estimates of the parabolic solution
are separate from this identification step.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- Strong limits of actual horizontal gradients remain in the canonical
potential domain. Source: `paper/main.tex:808–816`. -/
theorem horizontalGradient_limit_mem_potentialDomain {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    {G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)}
    (hG : Tendsto (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) atTop (𝓝 G)) :
    G ∈ correctorPotentialDomain Q := by
  exact (isClosed_stationaryPotentialGradients (reducedEnvironmentLaw Q)
    (reducedEnvironmentLaw_stationary Q)).mem_of_tendsto hG
      (Eventually.of_forall fun n =>
        horizontalEuclideanGradient_mem_stationaryPotentialGradients
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))

/-- The integrated flow equation and decay of its scalar residual identify
any strong gradient limit with the canonical corrector. No uniqueness of
parabolic solutions is a premise. Source: `paper/main.tex:808–816`. -/
theorem flowGradient_limit_eq_canonical {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    {G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)}
    (hG : Tendsto (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) atTop (𝓝 G))
    (hu : Tendsto u atTop (𝓝 0))
    (heq : ∀ n, ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i (horizontalEuclideanGradient
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))) =
        -inner ℝ (f : Lp ℝ 2 (reducedEnvironmentLaw Q)) (u n)) :
    G = (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) := by
  let g : correctorPotentialDomain Q :=
    ⟨G, horizontalGradient_limit_mem_potentialDomain Q v hG⟩
  have hvar : ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i (g :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) = 0 := by
    intro f
    have hflux := (reducedOriginCoefficientAction Q).continuous.tendsto
      (correctorAffineField Q i + G) |>.comp (tendsto_const_nhds.add hG)
    have hleft : Tendsto (fun n =>
        inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) f)
          (correctorFluxOfGradient Q i (horizontalEuclideanGradient
            (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))))
        atTop (𝓝 (inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) f) (correctorFluxOfGradient Q i G))) :=
      tendsto_const_nhds.inner hflux
    have hright : Tendsto (fun n =>
        -inner ℝ (f : Lp ℝ 2 (reducedEnvironmentLaw Q)) (u n)) atTop
        (𝓝 (-inner ℝ (f : Lp ℝ 2 (reducedEnvironmentLaw Q)) 0)) :=
      (tendsto_const_nhds.inner hu).neg
    have hequal : Tendsto (fun n =>
        inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) f)
          (correctorFluxOfGradient Q i (horizontalEuclideanGradient
            (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [heq, inner_zero_right, neg_zero] using hright
    exact tendsto_nhds_unique hleft hequal
  have hcanonical := canonicalCorrectorGradient_variational_horizontalH1 Q i
  have hg : g = canonicalCorrectorGradient Q i :=
    (existsUnique_canonicalCorrectorGradient_horizontalH1 Q i).unique hvar hcanonical
  exact congrArg Subtype.val hg

/-- A Cauchy family of integrated gradients with a decaying parabolic
residual converges to the existing canonical gradient; no limit is chosen
as a new corrector definition. Source: `paper/main.tex:808–816`. -/
theorem tendsto_flowGradient_canonical_of_cauchy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q))
    (hC : CauchySeq (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)))
    (hu : Tendsto u atTop (𝓝 0))
    (heq : ∀ n, ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i (horizontalEuclideanGradient
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))) =
        -inner ℝ (f : Lp ℝ 2 (reducedEnvironmentLaw Q)) (u n)) :
    Tendsto (fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) atTop
      (𝓝 (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))) := by
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hC
  rw [flowGradient_limit_eq_canonical Q i v u hG hu heq] at hG
  exact hG

/-- A quantitative Cauchy bound for integrated flow gradients passes to
the canonical corrector with the same constant. This transfers the time
tail estimate without defining a second gradient. Source:
`paper/main.tex:811–816`. -/
theorem flowGradient_canonical_tail_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (v : ℕ → horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q))
    (u : ℕ → Lp ℝ 2 (reducedEnvironmentLaw Q)) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 0))
    (hbound : ∀ n m, n ≤ m →
      ‖horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) (v m) -
        horizontalEuclideanGradient (reducedEnvironmentLaw Q)
          (reducedEnvironmentLaw_stationary Q) (v n)‖ ≤ b n)
    (hu : Tendsto u atTop (𝓝 0))
    (heq : ∀ n, ∀ f : horizontalH1 (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q),
      inner ℝ (horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) f)
        (correctorFluxOfGradient Q i (horizontalEuclideanGradient
          (reducedEnvironmentLaw Q) (reducedEnvironmentLaw_stationary Q) (v n))) =
        -inner ℝ (f : Lp ℝ 2 (reducedEnvironmentLaw Q)) (u n)) :
    ∀ n, ‖(canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) -
      horizontalEuclideanGradient (reducedEnvironmentLaw Q)
        (reducedEnvironmentLaw_stationary Q) (v n)‖ ≤ b n := by
  have hC := cauchySeq_of_le_tendsto_0'
    (s := fun n => horizontalEuclideanGradient (reducedEnvironmentLaw Q)
      (reducedEnvironmentLaw_stationary Q) (v n)) b (fun n m hnm => by
    rw [dist_eq_norm, norm_sub_rev]
    exact hbound n m hnm) hb
  have hlim := tendsto_flowGradient_canonical_of_cauchy Q i v u hC hu heq
  intro n
  exact le_of_tendsto (hlim.sub_const _ |>.norm)
    ((eventually_ge_atTop n).mono fun m hnm => hbound n m hnm)

end EinsteinRelation.Correctors
