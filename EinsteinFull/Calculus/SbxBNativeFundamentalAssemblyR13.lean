import EinsteinFull.Calculus.SbxBNativeKernelNonnegativeR13
import EinsteinFull.Calculus.SbxBNativeSpectralHeatPositiveR13

open MeasureTheory Filter EinsteinRelation
open scoped Topology

namespace EinsteinFull
open External.Source.GMP Calculus Blueprint.SbxS3UniformCrossHeat

noncomputable section

/-- The native spectral series, normalized as a Lebesgue density in the start variable. -/
def bNativeSpectralKernelR13 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (x y : Vec d) : ℝ :=
  ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y

/-- The separate missing weak-caloric assertion for the spectral series and a
specified representative of its spatial gradient. -/
def BNativeSpectralCaloricR13 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (G : ℝ → Vec d → Vec d → Vec d) : Prop :=
  ∀ y ∈ sourceBall (0 : Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
    IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R)
      (fun z => bNativeSpectralKernelR13 s z.1 z.2 y) (fun z => G z.1 z.2 y)

/-- The separate missing zero-extension trace for the same gradient representative. -/
def BNativeSpectralZeroExtensionR13 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (G : ℝ → Vec d → Vec d → Vec d) : Prop :=
  ∀ y ∈ sourceBall (0 : Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      HasWeakGradient Set.univ
        (Set.indicator (sourceBall 0 R) (fun x => bNativeSpectralKernelR13 s t x y))
        (Set.indicator (sourceBall 0 R) (fun x => G t x y))

/-- The separately required pointwise initial delta of the spectral series. -/
def BNativeSpectralInitialDeltaR13 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) : Prop :=
  ∀ y ∈ sourceBall (0 : Vec d) R, ∀ ψ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) ψ →
    Tendsto (fun t : ℝ => ∫ x in sourceBall 0 R, bNativeSpectralKernelR13 s t x y * ψ x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (ψ y))

/-- The separately required pointwise nonnegativity of the spectral series. -/
def BNativeSpectralNonnegativeR13 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) : Prop :=
  ∀ y ∈ sourceBall (0 : Vec d) R, ∀ t : ℝ, 0 < t →
    ∀ x ∈ sourceBall (0 : Vec d) R, 0 ≤ bNativeSpectralKernelR13 s t x y

/-- Nonnegativity follows from positivity preservation of the native heat operator. -/
theorem b_native_spectral_nonnegative_r13 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R) :
    BNativeSpectralNonnegativeR13 s := by
  intro y hy t ht x hx
  have hp : br13NativeSpectralHeatPositive s := by
    intro u f hf
    exact (br13_native_spectral_heat_order hd hκ hR hell s u f).1 hf
  exact br13_native_kernel_nonnegative_of_heat_positive hd hκ hR hell s hp
    ⟨t, ht.le⟩ ht x y hx hy

/-- Assemble the actual spectral kernel from a supplied resolution and three
separate analytic assertions. The first and second assertions refer to the
same genuine gradient; none assumes a fundamental-solution certificate. -/
theorem b_native_fundamental_assembly_r13 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (G : ℝ → Vec d → Vec d → Vec d)
    (hcal : BNativeSpectralCaloricR13 s G)
    (hzero : BNativeSpectralZeroExtensionR13 s G)
    (hinit : BNativeSpectralInitialDeltaR13 s) :
    IsSpectralDirichletFundamentalSolution ρ α R (bNativeSpectralKernelR13 s) G := by
  have hnonneg := b_native_spectral_nonnegative_r13 hd hκ hR hell s
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  refine ⟨?_, s, ?_⟩
  · intro y hy
    refine ⟨?_, hnonneg y hy, ?_, ?_, hinit y hy⟩
    · exact continuousOn_const.mul
        (spectral_heat_row_continuousOn_closedBall hd hκ hell hR s hs y hy)
    · intro t ht x hx
      change ρ y * (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y) = 0
      have hz : (∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) = 0 := by
        simp only [s.boundary_zero _ x hx, mul_zero, zero_mul, tsum_zero]
      rw [hz, mul_zero]
    · intro a b ha hab
      exact ⟨hcal y hy a b ha hab, hzero y hy a b ha hab⟩
  · intro t ht x hx y hy
    exact ⟨spectral_heat_cross_summable_closedBall hd hκ hell hR s t ht x y
      (subset_closure hx) (subset_closure hy), rfl⟩

/-- A native resolution and one gradient satisfy both positive-time
conditions for the Lebesgue-normalized spectral kernel. -/
theorem b_native_spectral_caloric_zero_exists_r14 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → Vec d → Vec d → Vec d),
      BNativeSpectralCaloricR13 s G ∧ BNativeSpectralZeroExtensionR13 s G := by
  obtain ⟨s, G, hG⟩ :=
    exists_sourceBall_spectral_global_positive_strip_gradient hd hκ hell R hR
  refine ⟨s, fun t x y => ρ y • G t x y, ?_, ?_⟩
  · intro y hy a b ha hab
    obtain ⟨h, ht⟩ := hG y hy a b ha hab
    let u : ℝ × Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    let H : ℝ × Vec d → Vec d := fun z => G z.1 z.2 y
    change IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R) u H at h
    change IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R)
      (fun z => ρ y * u z) (fun z => ρ y • H z)
    have weak_mul : ∀ {U : Set (Vec d)} {f : Vec d → ℝ} {F : Vec d → Vec d},
        HasWeakGradient U f F → HasWeakGradient U (fun x => ρ y * f x)
          (fun x => ρ y • F x) := by
      intro U f F hf i
      refine ⟨fun x hx => ((hf i).1 x hx).smul (ρ y),
        fun x hx => ((hf i).2.1 x hx).smul (ρ y), ?_⟩
      intro ψ hψ
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
      rw [(hf i).2.2 ψ hψ, mul_neg]
    refine ⟨h.1.const_mul (ρ y), h.2.1.const_smul (ρ y), ?_, ?_, ?_⟩
    · have heq : (fun z => euclideanNorm (ρ y • H z)) =
          (fun z => |ρ y| * euclideanNorm (H z)) := by
        funext z
        exact TimeChange.euclideanNorm_smul (ρ y) (H z)
      rw [heq]
      exact h.2.2.1.const_mul |ρ y|
    · filter_upwards [h.2.2.2.1] with t ht
      exact weak_mul ht
    · intro ψ hψ hc hs
      have heq : (fun z : ℝ × Vec d =>
          -(ρ z.2 * (ρ y * u z)) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (ρ y • H z))
              (fun j => fderiv ℝ ψ z (0, unitVector j))) =
          (fun z => ρ y * (-(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (H z))
              (fun j => fderiv ℝ ψ z (0, unitVector j)))) := by
        funext z
        rw [Matrix.mulVec_smul]
        simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc]
        ring_nf
        rw [Finset.mul_sum]
        simp only [mul_assoc]
      rw [heq, integral_const_mul, h.2.2.2.2 ψ hψ hc hs, mul_zero]
  · intro y hy a b ha hab
    filter_upwards [(hG y hy a b ha hab).2] with t ht
    change HasWeakGradient Set.univ
      ((sourceBall (0 : Vec d) R).indicator (fun x => ρ y * ∑' i,
        Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
      ((sourceBall (0 : Vec d) R).indicator (fun x => ρ y • G t x y))
    have hf : (sourceBall (0 : Vec d) R).indicator (fun x => ρ y * ∑' i,
        Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y) =
        fun x => ρ y * (sourceBall (0 : Vec d) R).indicator (fun x => ∑' i,
        Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y) x := by
      funext x
      by_cases hx : x ∈ sourceBall (0 : Vec d) R <;> simp [hx]
    have hg : (sourceBall (0 : Vec d) R).indicator (fun x => ρ y • G t x y) =
        fun x => ρ y • (sourceBall (0 : Vec d) R).indicator (fun x => G t x y) x := by
      funext x
      by_cases hx : x ∈ sourceBall (0 : Vec d) R <;> simp [hx]
    rw [hf, hg]
    intro i
    refine ⟨fun x hx => ((ht i).1 x hx).smul (ρ y),
      fun x hx => ((ht i).2.1 x hx).smul (ρ y), ?_⟩
    intro ψ hψ
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    have he := (ht i).2.2 ψ hψ
    simp only [mul_assoc] at he
    rw [he, mul_neg]

/-- The remaining initial-delta assertion alone completes native existence. -/
theorem b_native_fundamental_exists_of_initial_delta_r14 {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (hinit : ∀ s : DirichletSpectralResolution ρ α R,
      BNativeSpectralInitialDeltaR13 s) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R (bNativeSpectralKernelR13 s) G := by
  obtain ⟨s, G, hc, hz⟩ := b_native_spectral_caloric_zero_exists_r14 hd hκ hR hell
  exact ⟨s, G, b_native_fundamental_assembly_r13 hd hκ hR hell s G hc hz (hinit s)⟩

#print axioms b_native_fundamental_exists_of_initial_delta_r14

#print axioms b_native_spectral_caloric_zero_exists_r14

#print axioms b_native_fundamental_assembly_r13

end
end EinsteinFull
