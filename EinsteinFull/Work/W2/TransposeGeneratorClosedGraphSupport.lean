import EinsteinFull.Work.W2.TransposeGraphGradientEnergySupport
import EinsteinFull.Calculus.ComplexHorizontalClosedGraphSupport

/-!
# Strong limits of the full transpose generator graph

The full graph energy estimate on differences makes gradients Cauchy in the
Euclidean L2 product. Completeness and the closed horizontal derivative graph
recover the limiting gradient. The coefficient-column drift remains on every
test gradient throughout passage to the weak limit.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The actual strong horizontal gradient respects subtraction. -/
theorem HasComplexHorizontalGradient.sub
    {d : ℕ} {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f g : Lp ℂ 2 Q} {G H : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G)
    (hg : HasComplexHorizontalGradient Q hQ g H) :
    HasComplexHorizontalGradient Q hQ (f - g) (G - H) := by
  intro j
  change HasComplexHorizontalDerivative Q hQ j (f - g) (G j - H j)
  simpa only [neg_one_smul, sub_eq_add_neg] using
    (hf j).add ((hg j).smul (-1 : ℂ))

/-- Differences remain in the literal full transpose graph, at the same force. -/
theorem IsComplexTransposeGeneratorPair.sub
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g u v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (huv : IsComplexTransposeGeneratorPair Q i ζ u v) :
    IsComplexTransposeGeneratorPair Q i ζ (f - u) (g - v) := by
  let s := complexForceShift d Λ₀ ζ + 1
  have hs : complexForceShift d Λ₀ ζ < s := lt_add_one _
  apply (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mpr
  have hf := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mp hfg
  have hu := (isComplexTransposeGeneratorPair_iff_resolvent Q i ζ s hs _ _).mp huv
  rw [show (s : ℂ) • (f - u) - (g - v) =
    ((s : ℂ) • f - g) - ((s : ℂ) • u - v) by module, map_sub, hf, hu]

private theorem cauchySeq_of_sq_norm_sub_le
    {E F V : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup V] {f : ℕ → E} {g : ℕ → F} {v : ℕ → V}
    (K S : ℝ) (hf : CauchySeq f) (hg : CauchySeq g)
    (he : ∀ p : ℕ × ℕ, ‖v p.1 - v p.2‖ ^ 2 ≤
      K * (‖f p.1 - f p.2‖ * ‖g p.1 - g p.2‖ + S * ‖f p.1 - f p.2‖ ^ 2)) :
    CauchySeq v := by
  have hfn : Tendsto (fun p : ℕ × ℕ => ‖f p.1 - f p.2‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, Prod.map] using
      tendsto_uniformity_iff_dist_tendsto_zero.mp (cauchySeq_iff_tendsto.mp hf)
  have hgn : Tendsto (fun p : ℕ × ℕ => ‖g p.1 - g p.2‖) atTop (𝓝 0) := by
    simpa only [dist_eq_norm, Prod.map] using
      tendsto_uniformity_iff_dist_tendsto_zero.mp (cauchySeq_iff_tendsto.mp hg)
  have hb := ((hfn.mul hgn).add ((hfn.pow 2).const_mul (S))).const_mul
    K
  simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at hb
  have hsq := squeeze_zero (fun p => sq_nonneg
    ‖v p.1 - v p.2‖) he hb
  have hn := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at hn
  apply cauchySeq_iff_tendsto.mpr
  apply tendsto_uniformity_iff_dist_tendsto_zero.mpr
  simpa only [dist_eq_norm, Prod.map] using hn

/-- No gradient convergence or uniform bound is assumed: the full graph energy
estimate forces the unique gradients of any Cauchy graph sequence to be Cauchy. -/
theorem cauchySeq_complexTransposeGenerator_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : ℕ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℕ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hfg : ∀ n, IsComplexTransposeGeneratorPair Q i ζ (f n) (g n))
    (hG : ∀ n, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (f n) (G n)) (hf : CauchySeq f) (hg : CauchySeq g) :
    CauchySeq (fun n => WithLp.toLp 2 (G n)) := by
  apply cauchySeq_of_sq_norm_sub_le (4 * (Real.exp (2 * Λ₀) * Λ₀))
    (complexForceShift d Λ₀ ζ) hf hg
  intro p
  have hd := (hG p.1).sub (hG p.2)
  have hb := ((hfg p.1).sub (hfg p.2)).gradient_energy_le hd
  simpa only [WithLp.toLp_sub] using hb

private theorem transpose_principal_eq_sum_inner
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (G H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * H j ω ∂reducedLaw Q) =
      ∑ k, inner ℂ (complexL2Conjugation (reducedLaw Q)
        (complexForceDrift Q k (WithLp.toLp 2 H))) (G k) := by
  simp only [inner_complexL2Conjugation_eq_integral_mul]
  rw [← integral_finset_sum Finset.univ (fun k _ =>
    show Integrable (fun ω => complexForceDrift Q k (WithLp.toLp 2 H) ω * G k ω)
      (reducedLaw Q) from
      (Lp.memLp (complexForceDrift Q k (WithLp.toLp 2 H))).integrable_mul (Lp.memLp (G k)))]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr fun k => complexForceDrift_coe Q k (WithLp.toLp 2 H)]
    with ω hω
  simp only [hω, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem transpose_drift_eq_inner
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) (H : Fin d → Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, f ω * (∑ j, (ω.1 0 j i : ℂ) * H j ω) ∂reducedLaw Q) =
      inner ℂ (complexL2Conjugation (reducedLaw Q)
        (complexForceDrift Q i (WithLp.toLp 2 H))) f := by
  rw [inner_complexL2Conjugation_eq_integral_mul]
  apply integral_congr_ae
  filter_upwards [complexForceDrift_coe Q i (WithLp.toLp 2 H)] with ω hω
  rw [hω, mul_comm]

/-- Strong value, output and gradient limits preserve the genuine full H1 weak
form, including the anisotropic principal term and the test-gradient drift. -/
theorem complexTransposeGeneratorPair_of_tendsto_gradient
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : ℕ → Lp ℂ 2 (reducedLaw Q)}
    {G : ℕ → Fin d → Lp ℂ 2 (reducedLaw Q)}
    {u v : Lp ℂ 2 (reducedLaw Q)} {H : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hfg : ∀ n, IsComplexTransposeGeneratorPair Q i ζ (f n) (g n))
    (hG : ∀ n, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (f n) (G n))
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (hlim : Tendsto G atTop (𝓝 H)) :
    IsComplexTransposeGeneratorPair Q i ζ u v ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H :=
    complexHorizontalGradient_of_tendsto
      (p := fun n => (f n, G n)) (q := (u, H))
      (Eventually.of_forall hG) (hf.prodMk_nhds hlim)
  refine ⟨⟨H, hH, ?_⟩, hH⟩
  intro w J hw
  have he (n : ℕ) := (hfg n)
  have he' (n : ℕ) :
      inner ℂ (complexL2Conjugation (reducedLaw Q) w) (g n) =
        -(1 / 2 : ℂ) * (∑ k, inner ℂ (complexL2Conjugation (reducedLaw Q)
          (complexForceDrift Q k (WithLp.toLp 2 J))) (G n k)) +
        ζ * inner ℂ (complexL2Conjugation (reducedLaw Q)
          (complexForceDrift Q i (WithLp.toLp 2 J))) (f n) := by
    obtain ⟨K, hK, ht⟩ := he n
    have hKG := hK.unique (hG n)
    subst K
    have ht' := ht w J hw
    rw [transpose_principal_eq_sum_inner, transpose_drift_eq_inner] at ht'
    rw [inner_complexL2Conjugation_eq_integral_mul]
    convert ht' using 1
    exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)
  have hl := (tendsto_const_nhds (x := complexL2Conjugation (reducedLaw Q) w)).inner (𝕜 := ℂ) hg
  have hr := ((tendsto_finset_sum Finset.univ (fun k _ =>
    (tendsto_const_nhds (x := complexL2Conjugation (reducedLaw Q)
      (complexForceDrift Q k (WithLp.toLp 2 J)))).inner (𝕜 := ℂ)
        ((continuous_apply k).tendsto H |>.comp hlim))).const_mul
      (-(1 / 2 : ℂ))).add (((tendsto_const_nhds (x := complexL2Conjugation (reducedLaw Q)
        (complexForceDrift Q i (WithLp.toLp 2 J)))).inner (𝕜 := ℂ) hf).const_mul ζ)
  have ht := tendsto_nhds_unique (hl.congr' (Eventually.of_forall he')) hr
  rw [transpose_principal_eq_sum_inner, transpose_drift_eq_inner]
  rw [inner_complexL2Conjugation_eq_integral_mul] at ht
  convert ht using 1
  exact integral_congr_ae (Eventually.of_forall fun _ => mul_comm _ _)

/-- Simultaneous strong limits in the literal full transpose graph also have
strongly convergent unique Euclidean gradients; no extra regularity is assumed. -/
theorem complexTransposeGeneratorPair_of_tendsto
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : ℕ → Lp ℂ 2 (reducedLaw Q)} {u v : Lp ℂ 2 (reducedLaw Q)}
    (hfg : ∀ n, IsComplexTransposeGeneratorPair Q i ζ (f n) (g n))
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v)) :
    IsComplexTransposeGeneratorPair Q i ζ u v ∧
      ∃ (G : ℕ → Fin d → Lp ℂ 2 (reducedLaw Q))
        (H : Fin d → Lp ℂ 2 (reducedLaw Q)),
        (∀ n, HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (f n) (G n)) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u H ∧
        Tendsto (fun n => WithLp.toLp 2 (G n)) atTop (𝓝 (WithLp.toLp 2 H)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  choose G hG using fun n => (hfg n).existsUnique_gradient_energy_le.exists
  have hc := cauchySeq_complexTransposeGenerator_gradient hfg (fun n => (hG n).1)
    hf.cauchySeq hg.cauchySeq
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hc
  have hHp : Tendsto G atTop (𝓝 (WithLp.ofLp H)) :=
    ((PiLp.continuous_ofLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))).tendsto H).comp hH
  have ht := complexTransposeGeneratorPair_of_tendsto_gradient hfg
    (fun n => (hG n).1) hf hg hHp
  exact ⟨ht.1, G, WithLp.ofLp H, (fun n => (hG n).1), ht.2, hH⟩

/-- Energy and horizontal graph completeness give closedness of the entire
transpose weak generator graph in the strong product L2 topology. -/
theorem isClosed_complexTransposeGenerator_graph_of_energy
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    IsClosed {p : Lp ℂ 2 (reducedLaw Q) × Lp ℂ 2 (reducedLaw Q) |
      IsComplexTransposeGeneratorPair Q i ζ p.1 p.2} := by
  apply IsSeqClosed.isClosed
  intro p q hp hlim
  exact (complexTransposeGeneratorPair_of_tendsto hp
    (continuous_fst.tendsto q |>.comp hlim)
    (continuous_snd.tendsto q |>.comp hlim)).1

end EinsteinFull
