import EinsteinRelation.Correctors.P53SourceSkewMollifyAlgebra
import EinsteinRelation.Correctors.P53SourceSkewTruncationPairing
import EinsteinRelation.Calculus.Weak

/-!
# The source identities of a closed skew corrector

Source: `paper/main.tex:694-708,740-743`; AKM (6.5)-(6.6). Let a matrix potential
`σ` have weak gradients `f_{ab,c} = ∂_c σ_{ab}`, antisymmetric in `a, b` and with
vanishing cyclic sums, and let its row divergence be a field `g`:
`Σ_c f_{ac,c} = g_a`. Then `σ` satisfies the manuscript's distributional
row-divergence identity, and its entries solve the curl Poisson equation
`-Δσ_{jk} = ∂_j g_k - ∂_k g_j`. Both identities are tested against smooth compactly
supported functions, with all integrability made explicit.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors

variable {d : ℕ}

private theorem integrable_mul_test {h : Vec d → ℝ} (hh : LocallyIntegrable h volume)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x => h x * φ x) volume := by
  simpa only [smul_eq_mul] using
    hh.integrable_smul_right_of_hasCompactSupport hφ.continuous hφc

private theorem isSpatialTest_univ {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) : IsSpatialTest Set.univ φ :=
  ⟨hφ, hφc, Set.subset_univ _⟩

/-- The weak derivative identity on all of space, without restrictions. -/
private theorem integral_mul_coordinateDerivative_of_weak {u v : Vec d → ℝ} {c : Fin d}
    (h : HasWeakPartialDerivative Set.univ c u v) {φ : Vec d → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x, u x * coordinateDerivative c φ x) = -∫ x, v x * φ x := by
  have h' := h.2.2 φ (isSpatialTest_univ hφ hφc)
  simpa only [Measure.restrict_univ] using h'

variable {σ : Vec d → Mat d} {f : Fin d → Fin d → Fin d → Vec d → ℝ} {g : Vec d → Vec d}

/-- Exchanging the derivative index with the test derivative, through the potential. -/
theorem integral_closedGradient_swap
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (a l j : Fin d) :
    (∫ x, f a l j x * coordinateDerivative l ψ x) =
      ∫ x, f a l l x * coordinateDerivative j ψ x := by
  have h1 := integral_mul_coordinateDerivative_of_weak (hweak a l j)
    (contDiff_coordinateDerivative' hψ l) (hasCompactSupport_coordinateDerivative' hψc l)
  have h2 := integral_mul_coordinateDerivative_of_weak (hweak a l l)
    (contDiff_coordinateDerivative' hψ j) (hasCompactSupport_coordinateDerivative' hψc j)
  rw [coordinateDerivative_comm hψ j l] at h1
  linarith

theorem locallyIntegrable_closedGradient
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (a b c : Fin d) : LocallyIntegrable (f a b c) volume :=
  locallyIntegrableOn_univ.mp (hweak a b c).2.1

theorem locallyIntegrable_potential
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hd : 0 < d) (a b : Fin d) : LocallyIntegrable (fun x => σ x a b) volume :=
  locallyIntegrableOn_univ.mp (hweak a b ⟨0, hd⟩).1

theorem locallyIntegrable_rowDivergence
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hdiv : ∀ a, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ c, f a c c x = g x a) (a : Fin d) :
    LocallyIntegrable (fun x => g x a) volume := by
  have hsum : LocallyIntegrable (fun x => ∑ c, f a c c x) volume := by
    have h := locallyIntegrable_finset_sum (Finset.univ : Finset (Fin d))
      (fun c _ => locallyIntegrable_closedGradient hweak a c c)
    simpa only [Finset.sum_apply] using h
  refine hsum.mono (hsum.aestronglyMeasurable.congr (hdiv a)) ?_
  filter_upwards [hdiv a] with x hx
  rw [hx]

/-- The manuscript's row-divergence identity, from the weak divergence of the
gradient. Source: AKM (6.6), `paper/main.tex:694-708`. -/
theorem closedSkew_rowDivergence_identity (hd : 0 < d)
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hdiv : ∀ a, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ c, f a c c x = g x a)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j : Fin d) :
    Integrable (fun x => g x j * ψ x) volume ∧
      Integrable (fun x => ∑ k, σ x j k * coordinateDerivative k ψ x) volume ∧
      (∫ x, g x j * ψ x) = -(∫ x, ∑ k, σ x j k * coordinateDerivative k ψ x) := by
  have hσi (k : Fin d) : Integrable (fun x => σ x j k * coordinateDerivative k ψ x) volume :=
    integrable_mul_test (locallyIntegrable_potential hweak hd j k)
      (contDiff_coordinateDerivative' hψ k) (hasCompactSupport_coordinateDerivative' hψc k)
  have hfi (k : Fin d) : Integrable (fun x => f j k k x * ψ x) volume :=
    integrable_mul_test (locallyIntegrable_closedGradient hweak j k k) hψ hψc
  refine ⟨integrable_mul_test (locallyIntegrable_rowDivergence hweak hdiv j) hψ hψc,
    integrable_finset_sum _ fun k _ => hσi k, ?_⟩
  rw [integral_finset_sum _ fun k _ => hσi k]
  simp_rw [fun k => integral_mul_coordinateDerivative_of_weak (hweak j k k) hψ hψc]
  rw [Finset.sum_neg_distrib, neg_neg, ← integral_finset_sum _ fun k _ => hfi k]
  refine integral_congr_ae ?_
  filter_upwards [hdiv j] with x hx
  rw [← hx, Finset.sum_mul]

/-- The curl Poisson equation `-Δσ_{jk} = ∂_j g_k - ∂_k g_j` of a closed skew
corrector. Source: AKM (6.5), `paper/main.tex:740-743`. -/
theorem closedSkew_poisson_identity (hd : 0 < d)
    (hweak : ∀ a b, HasWeakGradient Set.univ (fun x => σ x a b) (fun x c => f a b c x))
    (hswap : ∀ a b c, ∀ᵐ x ∂(volume : Measure (Vec d)), f b a c x = -f a b c x)
    (hcyc : ∀ a b c, ∀ᵐ x ∂(volume : Measure (Vec d)),
      f a b c x + f b c a x + f c a b x = 0)
    (hdiv : ∀ a, ∀ᵐ x ∂(volume : Measure (Vec d)), ∑ c, f a c c x = g x a)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (j k : Fin d) :
    Integrable (fun x => σ x j k *
        (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) volume ∧
      Integrable (fun x => g x k * coordinateDerivative j ψ x) volume ∧
      Integrable (fun x => g x j * coordinateDerivative k ψ x) volume ∧
      (∫ x, σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
        -(∫ x, g x k * coordinateDerivative j ψ x) + ∫ x, g x j * coordinateDerivative k ψ x := by
  have hD (l : Fin d) := contDiff_coordinateDerivative' hψ l
  have hDc (l : Fin d) := hasCompactSupport_coordinateDerivative' hψc l
  have hDD (l : Fin d) := contDiff_coordinateDerivative' (hD l) l
  have hDDc (l : Fin d) := hasCompactSupport_coordinateDerivative' (hDc l) l
  have hσl (l : Fin d) : Integrable (fun x => σ x j k *
      coordinateDerivative l (coordinateDerivative l ψ) x) volume :=
    integrable_mul_test (locallyIntegrable_potential hweak hd j k) (hDD l) (hDDc l)
  have hfl (a b c l : Fin d) : Integrable (fun x => f a b c x * coordinateDerivative l ψ x)
      volume :=
    integrable_mul_test (locallyIntegrable_closedGradient hweak a b c) (hD l) (hDc l)
  have hgk : Integrable (fun x => g x k * coordinateDerivative j ψ x) volume :=
    integrable_mul_test (locallyIntegrable_rowDivergence hweak hdiv k) (hD j) (hDc j)
  have hgj : Integrable (fun x => g x j * coordinateDerivative k ψ x) volume :=
    integrable_mul_test (locallyIntegrable_rowDivergence hweak hdiv j) (hD k) (hDc k)
  have hlap : Integrable (fun x => σ x j k *
      (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) volume := by
    have h := (integrable_finset_sum (Finset.univ : Finset (Fin d)) fun l _ => hσl l).neg
    refine h.congr (ae_of_all _ fun x => ?_)
    simp only [Pi.neg_apply, mul_neg, Finset.mul_sum]
  refine ⟨hlap, hgk, hgj, ?_⟩
  -- the Laplacian pairing is the pairing of the gradient with the test gradient
  have hstep1 : (∫ x, σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
      ∑ l, ∫ x, f j k l x * coordinateDerivative l ψ x := by
    have h : (fun x => σ x j k * (-∑ l, coordinateDerivative l (coordinateDerivative l ψ) x)) =
        fun x => -∑ l, σ x j k * coordinateDerivative l (coordinateDerivative l ψ) x := by
      funext x
      rw [mul_neg, Finset.mul_sum]
    rw [h, integral_neg, integral_finset_sum _ fun l _ => hσl l, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_coordinateDerivative_of_weak (hweak j k l) (hD l) (hDc l), neg_neg]
  -- closedness and antisymmetry
  have hsplit (l : Fin d) : (∫ x, f j k l x * coordinateDerivative l ψ x) =
      -(∫ x, f k l l x * coordinateDerivative j ψ x) +
        ∫ x, f j l l x * coordinateDerivative k ψ x := by
    have hae : (fun x => f j k l x * coordinateDerivative l ψ x) =ᵐ[volume]
        fun x => -(f k l j x * coordinateDerivative l ψ x) +
          f j l k x * coordinateDerivative l ψ x := by
      filter_upwards [hcyc j k l, hswap j l k] with x h1 h2
      have : f j k l x = -f k l j x + f j l k x := by linarith
      rw [this]
      ring
    have hneg : Integrable (fun x => -(f k l j x * coordinateDerivative l ψ x)) volume :=
      (hfl k l j l).neg
    rw [integral_congr_ae hae, integral_add hneg (hfl j l k l), integral_neg,
      integral_closedGradient_swap hweak hψ hψc k l j,
      integral_closedGradient_swap hweak hψ hψc j l k]
  rw [hstep1, Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← integral_finset_sum _ fun l _ => hfl k l l j,
    ← integral_finset_sum _ fun l _ => hfl j l l k]
  congr 1
  · congr 1
    refine integral_congr_ae ?_
    filter_upwards [hdiv k] with x hx
    rw [← Finset.sum_mul, hx]
  · refine integral_congr_ae ?_
    filter_upwards [hdiv j] with x hx
    rw [← Finset.sum_mul, hx]

end EinsteinRelation.Correctors
