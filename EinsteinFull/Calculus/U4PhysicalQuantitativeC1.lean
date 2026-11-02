import EinsteinFull.Calculus.U4PhysicalComplexC1Smoothing
import EinsteinFull.Calculus.U8QuantitativeSobolev
import EinsteinFull.Calculus.C5TestCLTSupport
import EinsteinFull.Calculus.PhysicalH1WeightedIntegrationSupport
import EinsteinRelation.Correctors.WeakPartialAddition

open EinsteinRelation MeasureTheory
open scoped ENNReal NNReal Topology

namespace EinsteinFull

noncomputable section

/-- Quantitative C¹ smoothing supplies a jointly continuous physical split
kernel, with value and Euclidean coordinate-gradient bounds. -/
theorem u4_physical_quantitative_C1_split_kernel_of_Sobolev
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, ∃ N : ℕ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ t : ℝ≥0, 0 < (t : ℝ) →
    let B := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N *
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
    ∃ K : Vec d → Vec d → ℂ,
      (∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        ((∀ᵐ x ∂volume, Integrable (fun y => K x y * f y)) ∧
          (P (t + t) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * f y) ∧
        ((∀ᵐ x ∂volume, Integrable (fun y => K y x * f y)) ∧
          (Pdag (t + t) f : Vec d → ℂ) =ᵐ[volume] fun x => ∫ y, K y x * f y)) ∧
      Continuous (fun z : Vec d × Vec d => K z.1 z.2) ∧
      (∀ y, ContDiff ℝ 1 (fun x => K x y)) ∧
      (∀ x, ContDiff ℝ 1 (fun y => K x y)) ∧
      ∀ x y, ‖K x y‖ ≤ B * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K z y) x (unitVector j)‖ ^ 2) ≤ B * B ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ (fun z => K x z) y (unitVector j)‖ ^ 2) ≤ B * B := by
  obtain ⟨C, N, hC, h⟩ :=
    u4_physical_evolution_L2_C1_of_Sobolev hSobolev hoff htime hder d hd D
  refine ⟨C, N, hC, ?_⟩
  intro Q hQ
  filter_upwards [h Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag t ht
  dsimp only
  let B : ℝ := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N *
    Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  exact s3_quantitative_C1_jointly_continuous_split_kernel P Pdag t
    (hP.2.1 t t) (hPdag.2.1 t t) (hPdag.2.2.2.2 t) B B hB hB
    (fun f => hω i ζ hζ P Pdag hP hPdag P (by simp) t ht f)
    (fun f => hω i ζ hζ P Pdag hP hPdag Pdag (by simp) t ht f)

/-- Continuous forward and transpose evaluation choices identify every continuous
representative of their respective positive-time actions at every point. -/
theorem u4_physical_evaluation_choices_identify_representatives
    {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0)
    (E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ)
    (hE : ∀ f, Continuous (fun x => E x f))
    (hF : ∀ f, Continuous (fun x => F x f))
    (hEa : ∀ f, (P t f : Vec d → ℂ) =ᵐ[volume] fun x => E x f)
    (hFa : ∀ f, (Pdag t f : Vec d → ℂ) =ᵐ[volume] fun x => F x f) :
    (∀ f u, Continuous u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
      ∀ x, E x f = u x) ∧
    (∀ f u, Continuous u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
      ∀ x, F x f = u x) := by
  constructor
  · intro f u hu he x
    exact congrFun (u4_continuous_physical_representative_unique _ _
      (hE f) hu ((hEa f).symm.trans he.symm)) x
  · intro f u hu he x
    exact congrFun (u4_continuous_physical_representative_unique _ _
      (hF f) hu ((hFa f).symm.trans he.symm)) x

/-- The actual S3 forward and transpose choices identify all continuous
representatives, assuming their quantitative C¹ representatives directly. -/
theorem u4_physical_s3_evaluation_identification_of_representatives
    {d : ℕ}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hE : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (P t f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ A * ‖f‖)
    (hF : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (Pdag t f : Vec d → ℂ) ∧ ∀ x,
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ B * ‖f‖) :
    ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
      (∀ f, ContDiff ℝ 1 (fun x => F x f)) ∧
      (∀ f u, Continuous u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
        ∀ x, E x f = u x) ∧
      (∀ f u, Continuous u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
        ∀ x, F x f = u x) := by
  obtain ⟨E, _, hEa, hEc, _⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (P t) A hA hE
  obtain ⟨F, _, hFa, hFc, _⟩ :=
    s3_evaluations_of_quantitative_C1_representatives (Pdag t) B hB hF
  refine ⟨E, F, hEc, hFc, ?_⟩
  exact u4_physical_evaluation_choices_identify_representatives P Pdag t E F
    (fun f => (hEc f).continuous) (fun f => (hFc f).continuous) hEa hFa

/-- The forward and transpose evaluation families agree at every point with
every continuous representative of the corresponding positive-time action. -/
theorem u4_physical_positive_time_evaluation_identification_of_Sobolev
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (htime : Blueprint.node_e_u3A_local_u2D_timeStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ t : ℝ≥0, 0 < (t : ℝ) →
    ∃ E F : Vec d → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      (∀ f, ContDiff ℝ 1 (fun x => E x f)) ∧
      (∀ f, ContDiff ℝ 1 (fun x => F x f)) ∧
      (∀ f u, Continuous u → u =ᵐ[volume] (P t f : Vec d → ℂ) →
        ∀ x, E x f = u x) ∧
      (∀ f u, Continuous u → u =ᵐ[volume] (Pdag t f : Vec d → ℂ) →
        ∀ x, F x f = u x) := by
  obtain ⟨C, N, hC, h⟩ :=
    u4_physical_evolution_L2_C1_of_Sobolev hSobolev hoff htime hder d hd D
  intro Q hQ
  filter_upwards [h Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag t ht
  let B : ℝ := C * (1 + (t : ℝ)⁻¹)^N * (2 + (t : ℝ)) ^ N *
    Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  exact u4_physical_s3_evaluation_identification_of_representatives P Pdag t B B hB hB
    (fun f => hω i ζ hζ P Pdag hP hPdag P (by simp) t ht f)
    (fun f => hω i ζ hζ P Pdag hP hPdag Pdag (by simp) t ht f)

/-- Off-diagonal decay on a Euclidean ball centred at a point separated
from the support, for the supplied physical evolutions. -/
theorem u4_physical_local_L2_off_diagonal
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))),
    IsPhysicalComplexSemigroup ω.1 i ζ P →
    IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ (E : Set (Vec d)), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∀ (x : Vec d) (ell : ℝ), 0 ≤ ell →
    (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
    let B := {z : Vec d | euclideanNorm (x - z) < ell / 2}
    MemLp (B.indicator (fun z => S t f z)) 2 volume ∧
    (eLpNorm (B.indicator (fun z => S t f z)) 2 volume).toReal ≤
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ell ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, hc, h⟩ := hoff d hd D.ellipticity D.one_le_ellipticity
  refine ⟨C, c / 4, hC, by positivity, ?_⟩
  intro Q
  filter_upwards [h D.dependenceRange Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t ht E hE f hf x ell hell hsep
  dsimp only
  have hcont : Continuous (fun z : Vec d => euclideanNorm (x - z)) :=
    (Entropy.continuous_euclideanNorm' (d := d)).comp (continuous_const.sub continuous_id)
  have hB : MeasurableSet {z : Vec d | euclideanNorm (x - z) < ell / 2} :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hdist : ∀ y ∈ E, ∀ z ∈ {z : Vec d | euclideanNorm (x - z) < ell / 2},
      ell / 2 ≤ euclideanNorm (y - z) := by
    intro y hy z hz
    have htri := TimeChange.euclideanNorm_add_le (x - z) (z - y)
    rw [sub_add_sub_cancel, ← neg_sub y z, Entropy.euclideanNorm_neg'] at htri
    have hy' := hsep y hy
    change euclideanNorm (x - z) < ell / 2 at hz
    linarith
  obtain ⟨hm, hb⟩ := (hω i ζ P Pdag hP hPdag S hS t ht).2 E _ hE hB
    (ell / 2) (by positivity) hdist f hf
  refine ⟨hm, ?_⟩
  have heq : C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (ell / 2) ^ 2 / (t : ℝ) =
      C * ‖ζ‖ ^ 2 * (t : ℝ) - (c / 4) * ell ^ 2 / (t : ℝ) := by ring
  simpa only [heq] using hb



/-- Fixed-ball interpolation applied to the actual physical evolution and
its transpose, with a uniform positive-time derivative scale. -/
theorem u4_physical_local_C1_interpolation_of_weak_derivatives
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hlocal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
        let L : ℝ := (eLpNorm
          ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
        ‖u x‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (L ^ θ * R ^ (1 - θ) + L))
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (D : StructuralData d) :
    ∃ B K θ : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    let R := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d,
      let L : ℝ := (eLpNorm
        ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ K * (L ^ θ * R ^ (1 - θ) + L) := by
  obtain ⟨Cs, _, hs⟩ := hSobolev d
  obtain ⟨K, θ, hK, hθ, hθ1, hl⟩ := hlocal d
  obtain ⟨B, hB, hb⟩ := u4Quant_reduced_positive_time_derivatives hder d D (d + 2)
  refine ⟨B, K, θ, hB, hK, hθ, hθ1, ?_⟩
  intro Q hQ
  filter_upwards [hb Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag S hS t ht f
  dsimp only
  obtain ⟨F, hF0, hF, hFb⟩ := hω i ζ hζ P Pdag hP hPdag S hS t ht f
  let R : ℝ := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
    Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hF' : ∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])) := by
    intro p hp
    exact hF p (by omega)
  have hFb' : ∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R := by
    intro p hp
    exact hFb p (by omega)
  obtain ⟨u, hu, hue, _⟩ := hs F R hR hF' hFb'
  refine ⟨u, hu, ?_, ?_⟩
  · simpa only [hF0] using hue
  · exact hl F R hR hF' hFb' u hu hue


/-- The physical off-diagonal estimate on a fixed Euclidean unit ball. -/
theorem u4_physical_unit_ball_L2_off_diagonal
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))),
    IsPhysicalComplexSemigroup ω.1 i ζ P →
    IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ (E : Set (Vec d)), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∀ (x : Vec d) (ell : ℝ),
    (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
    let B := {z : Vec d | euclideanNorm (x - z) < 1}
    MemLp (B.indicator (fun z => S t f z)) 2 volume ∧
    (eLpNorm (B.indicator (fun z => S t f z)) 2 volume).toReal ≤
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨C, c, hC, hc, h⟩ := hoff d hd D.ellipticity D.one_le_ellipticity
  refine ⟨C, c, hC, hc, ?_⟩
  intro Q
  filter_upwards [h D.dependenceRange Q] with ω hω
  intro i ζ P Pdag hP hPdag S hS t ht E hE f hf x ell hsep
  dsimp only
  have hcont : Continuous (fun z : Vec d => euclideanNorm (x - z)) :=
    (Entropy.continuous_euclideanNorm' (d := d)).comp (continuous_const.sub continuous_id)
  have hB : MeasurableSet {z : Vec d | euclideanNorm (x - z) < 1} :=
    (isOpen_lt hcont continuous_const).measurableSet
  have hdist : ∀ y ∈ E, ∀ z ∈ {z : Vec d | euclideanNorm (x - z) < 1},
      max (ell - 1) 0 ≤ euclideanNorm (y - z) := by
    intro y hy z hz
    apply max_le
    · have htri := TimeChange.euclideanNorm_add_le (x - z) (z - y)
      rw [sub_add_sub_cancel, ← neg_sub y z, Entropy.euclideanNorm_neg'] at htri
      have hy' := hsep y hy
      change euclideanNorm (x - z) < 1 at hz
      linarith
    · exact Real.sqrt_nonneg _
  exact (hω i ζ P Pdag hP hPdag S hS t ht).2 E _ hE hB
    (max (ell - 1) 0) (le_max_right _ _) hdist f hf


/-- Passing from separation of a unit ball to separation of its centre loses
only a fixed amount in the squared Gaussian distance. -/
theorem u4_unit_ball_separation_sq (ell : ℝ) (hell : 0 ≤ ell) :
    ell ^ 2 / 2 - 1 ≤ (max (ell - 1) 0) ^ 2 := by
  by_cases h : 1 ≤ ell
  · rw [max_eq_left (by linarith : 0 ≤ ell - 1)]
    nlinarith [sq_nonneg (ell - 2)]
  · rw [max_eq_right (by linarith : ell - 1 ≤ 0)]
    nlinarith [mul_nonneg hell (show 0 ≤ 1 - ell by linarith)]


/-- Fixed-ball interpolation combined with the physical off-diagonal bound. -/
theorem u4_physical_local_C1_off_diagonal_interpolated
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hlocal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
        let L : ℝ := (eLpNorm
          ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
        ‖u x‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (L ^ θ * R ^ (1 - θ) + L))
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ B K θ C c : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧ 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ E : Set (Vec d), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    let R := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ (x : Vec d) (ell : ℝ),
      (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
      let A := Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) -
        c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ K * (A ^ θ * R ^ (1 - θ) + A) := by
  obtain ⟨B, K, θ, hB, hK, hθ, hθ1, hI⟩ :=
    u4_physical_local_C1_interpolation_of_weak_derivatives hSobolev hlocal hder d D
  obtain ⟨C, c, hC, hc, hO⟩ := u4_physical_unit_ball_L2_off_diagonal hoff d hd D
  refine ⟨B, K, θ, C, c, hB, hK, hθ, hθ1, hC, hc, ?_⟩
  intro Q hQ
  filter_upwards [hI Q hQ, hO Q] with ω hIω hOω
  intro i ζ hζ P Pdag hP hPdag S hS t ht E hE f hf
  dsimp only
  obtain ⟨u, hu, hue, hub⟩ := hIω i ζ hζ P Pdag hP hPdag S hS t ht f
  refine ⟨u, hu, hue, ?_⟩
  intro x ell hsep
  obtain ⟨_, hbound⟩ := hOω i ζ P Pdag hP hPdag S hS t ht E hE f hf x ell hsep
  have heq : ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) =ᵐ[volume]
      ({z : Vec d | euclideanNorm (x - z) < 1}.indicator (fun z => S t f z)) := by
    filter_upwards [hue] with z hz
    by_cases hzB : euclideanNorm (x - z) < 1 <;> simp [Set.indicator, hzB, hz]
  have hL : (eLpNorm ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal ≤
      Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)) * ‖f‖ := by
    rw [eLpNorm_congr_ae heq]
    exact hbound
  have hp := Real.rpow_le_rpow (ENNReal.toReal_nonneg) hL hθ.le
  have hR : 0 ≤ (B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖) ^ (1 - θ) := Real.rpow_nonneg (by positivity) _
  exact (hub x).trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_right hp hR) hL) hK.le)


/-- The interpolation powers preserve linear dependence on the input norm. -/
theorem u4_interpolation_powers_factor (a b f θ : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hf : 0 ≤ f)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    (a * f) ^ θ * (b * f) ^ (1 - θ) =
      (a ^ θ * b ^ (1 - θ)) * f := by
  by_cases hf0 : f = 0
  · subst f
    simp [Real.zero_rpow hθ.ne', Real.zero_rpow (by linarith : 1 - θ ≠ 0)]
  · have hfpos : 0 < f := lt_of_le_of_ne hf (Ne.symm hf0)
    rw [Real.mul_rpow ha hf, Real.mul_rpow hb hf]
    calc
      a ^ θ * f ^ θ * (b ^ (1 - θ) * f ^ (1 - θ)) =
          (a ^ θ * b ^ (1 - θ)) * (f ^ θ * f ^ (1 - θ)) := by ring
      _ = (a ^ θ * b ^ (1 - θ)) * f := by
        rw [← Real.rpow_add hfpos]
        simp

/-- The unit-ball loss in the exponent costs only a uniform constant for
    times at least one. -/
theorem u4_unit_ball_gaussian_exponent (B C c θ z t ell : ℝ)
    (hc : 0 ≤ c) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hz : 0 ≤ z) (ht : 1 ≤ t) (hell : 0 ≤ ell) :
    θ * (C * z * t - c * (max (ell - 1) 0) ^ 2 / t) +
      (1 - θ) * (B * z * t) ≤
      max B C * z * t - (θ * c / 2) * ell ^ 2 / t + c := by
  have htpos : 0 < t := by linarith
  have hsep := u4_unit_ball_separation_sq ell hell
  have hq : 0 ≤ θ * c / t := by positivity
  have hq_le : θ * c / t ≤ c := by
    apply (div_le_iff₀ htpos).2
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hθ1),
      mul_nonneg hc (sub_nonneg.mpr ht)]
  have hz' : 0 ≤ z * t := mul_nonneg hz (le_of_lt htpos)
  have hmaxB : B ≤ max B C := le_max_left _ _
  have hmaxC : C ≤ max B C := le_max_right _ _
  have hB := mul_nonneg (sub_nonneg.mpr hmaxB)
    (mul_nonneg (sub_nonneg.mpr hθ1) hz')
  have hC := mul_nonneg (sub_nonneg.mpr hmaxC) (mul_nonneg hθ hz')
  have hd := mul_nonneg hq (sub_nonneg.mpr hsep)
  simp only [div_eq_mul_inv] at hd hq_le ⊢
  nlinarith

/-- A real-power interpolation estimate is controlled by a common exponential
    whenever both of its exponents are controlled by that exponential. -/
theorem u4_interpolation_common_exponential
    (m p q g c θ f : ℝ) (hm : 1 ≤ m) (hf : 0 ≤ f)
    (hθ : 0 < θ) (hθ1 : θ < 1)
    (hp : p ≤ g + c) (hpq : θ * p + (1 - θ) * q ≤ g + c) :
    (Real.exp p * f) ^ θ * (m * Real.exp q * f) ^ (1 - θ) +
      Real.exp p * f ≤
      (m + 1) * Real.exp c * Real.exp g * f := by
  have hm0 : 0 ≤ m := by linarith
  have hmexp : 0 ≤ m * Real.exp q := by positivity
  rw [u4_interpolation_powers_factor (Real.exp p) (m * Real.exp q) f θ
    (Real.exp_pos p).le hmexp hf hθ hθ1]
  have hmpow : m ^ (1 - θ) ≤ m :=
    Real.rpow_le_self_of_one_le hm (by linarith)
  have hproduct : (Real.exp p) ^ θ * (m * Real.exp q) ^ (1 - θ) ≤
      m * Real.exp (g + c) := by
    rw [Real.mul_rpow hm0 (Real.exp_pos q).le, ← Real.exp_mul, ← Real.exp_mul]
    calc
      Real.exp (p * θ) * (m ^ (1 - θ) * Real.exp (q * (1 - θ))) =
          m ^ (1 - θ) * (Real.exp (p * θ) * Real.exp (q * (1 - θ))) := by ring
      _ = m ^ (1 - θ) * Real.exp (θ * p + (1 - θ) * q) := by
        rw [← Real.exp_add]
        congr 1; ring_nf
      _ ≤ m * Real.exp (g + c) :=
        mul_le_mul hmpow (Real.exp_le_exp.mpr hpq) (Real.exp_pos _).le hm0
  have hexp : Real.exp p ≤ Real.exp (g + c) := Real.exp_le_exp.mpr hp
  have hsum := add_le_add (mul_le_mul_of_nonneg_right hproduct hf)
    (mul_le_mul_of_nonneg_right hexp hf)
  rw [Real.exp_add] at hsum
  nlinarith

/-- Conditional localized Gaussian bounds for the physical evolutions. -/
theorem u4_physical_local_C1_gaussian_of_interpolation
    (hSobolev : ∀ (d : ℕ), ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∃ f : BoundedContinuousFunction (Vec d) ℂ,
          ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R)
    (hlocal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
        let L : ℝ := (eLpNorm
          ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
        ‖u x‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (L ^ θ * R ^ (1 - θ) + L))
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
    ∀ E : Set (Vec d), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ (x : Vec d) (ell : ℝ), 0 ≤ ell →
      (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ell ^ 2 / (t : ℝ)) * ‖f‖ := by
  obtain ⟨B, K, θ, C, c, hB, hK, hθ, hθ1, hC, hc, h⟩ :=
    u4_physical_local_C1_off_diagonal_interpolated hSobolev hlocal hoff hder d hd D
  let m : ℝ := B * 2 ^ (d + 3)
  let C' : ℝ := max (max B C) (max 1 (K * (m + 1) * Real.exp c))
  have hm : 1 ≤ m := by
    dsimp [m]
    have hp : 1 ≤ (2 : ℝ) ^ (d + 3) := one_le_pow₀ (by norm_num)
    nlinarith
  have hC' : 1 ≤ C' := (le_max_left 1 _).trans (le_max_right _ _)
  have hC'B : B ≤ C' := (le_max_left B C).trans (le_max_left _ _)
  have hC'C : C ≤ C' := (le_max_right B C).trans (le_max_left _ _)
  have hC'K : K * (m + 1) * Real.exp c ≤ C' :=
    (le_max_right 1 _).trans (le_max_right _ _)
  refine ⟨C', θ * c / 2, 0, hC', by positivity, ?_⟩
  intro Q hQ
  filter_upwards [h Q hQ] with ω hω
  intro i ζ hζ P Pdag hP hPdag S hS t ht E hE f hf
  have htpos : 0 < (t : ℝ) := by linarith
  obtain ⟨u, hu, hue, hub⟩ := hω i ζ hζ P Pdag hP hPdag S hS t
    (by exact_mod_cast htpos) E hE f hf
  refine ⟨u, hu, hue, ?_⟩
  intro x ell hell hsep
  have hinv : (t : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ htpos).2 ht
  have hbase : 0 ≤ 1 + (t : ℝ)⁻¹ := by positivity
  have hpow : (1 + (t : ℝ)⁻¹) ^ (d + 3) ≤ (2 : ℝ) ^ (d + 3) :=
    pow_le_pow_left₀ hbase (by linarith) _
  let p : ℝ := C * ‖ζ‖ ^ 2 * (t : ℝ) - c * (max (ell - 1) 0) ^ 2 / (t : ℝ)
  let q : ℝ := B * ‖ζ‖ ^ 2 * (t : ℝ)
  let g : ℝ := C' * ‖ζ‖ ^ 2 * (t : ℝ) - (θ * c / 2) * ell ^ 2 / (t : ℝ)
  have hR : B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖ ≤
      m * Real.exp q * ‖f‖ := by
    dsimp [m]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ B))
        (Real.exp_pos q).le) (norm_nonneg _)
  have hR0 : 0 ≤ B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖ := by positivity
  have hrpow := Real.rpow_le_rpow hR0 hR (by linarith : 0 ≤ 1 - θ)
  have hpq0 := u4_unit_ball_gaussian_exponent B C c θ (‖ζ‖ ^ 2) (t : ℝ) ell
    hc.le hθ.le hθ1.le (sq_nonneg _) ht hell
  have hmax : max B C ≤ C' := max_le hC'B hC'C
  have hzt : 0 ≤ ‖ζ‖ ^ 2 * (t : ℝ) := by positivity
  have hpq : θ * p + (1 - θ) * q ≤ g + c := by
    dsimp [p, q, g]
    have := mul_nonneg (sub_nonneg.mpr hmax) hzt
    nlinarith
  have hp0 := u4_unit_ball_gaussian_exponent C C c 1 (‖ζ‖ ^ 2) (t : ℝ) ell
    hc.le (by norm_num) (by norm_num) (sq_nonneg _) ht hell
  have hdecay : 0 ≤ (1 - θ) * c * ell ^ 2 / (t : ℝ) := by positivity
  have hp : p ≤ g + c := by
    dsimp [p, g]
    simp only [max_self] at hp0
    have := mul_nonneg (sub_nonneg.mpr hC'C) hzt
    simp only [div_eq_mul_inv] at hp0 hdecay ⊢
    nlinarith
  have hscalar := u4_interpolation_common_exponential m p q g c θ ‖f‖
    hm (norm_nonneg _) hθ hθ1 hp hpq
  have hfirst := hub x ell hsep
  dsimp only at hfirst
  have hstep : ‖u x‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
      K * ((Real.exp p * ‖f‖) ^ θ * (m * Real.exp q * ‖f‖) ^ (1 - θ) +
        Real.exp p * ‖f‖) := by
    apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ hK.le
    change (Real.exp p * ‖f‖) ^ θ *
      (B * (1 + (t : ℝ)⁻¹) ^ (d + 3) * Real.exp q * ‖f‖) ^ (1 - θ) +
      Real.exp p * ‖f‖ ≤ _
    exact add_le_add
      (mul_le_mul_of_nonneg_left hrpow
        (Real.rpow_nonneg (mul_nonneg (Real.exp_pos p).le (norm_nonneg f)) θ)) (le_refl _)
  have hlast := mul_le_mul_of_nonneg_left hscalar hK.le
  have hcoeff := mul_le_mul_of_nonneg_right hC'K
    (mul_nonneg (Real.exp_pos g).le (norm_nonneg f))
  dsimp [g] at hstep hlast hcoeff ⊢
  simp only [pow_zero, mul_one]
  nlinarith

/-- A continuous representative of a zero-norm physical L² class vanishes. -/
theorem u4_continuous_representative_eq_zero_of_norm_le_zero {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (hf : ‖f‖ ≤ 0)
    (u : Vec d → ℂ) (hu : Continuous u) (hue : u =ᵐ[volume] f) :
    u = 0 := by
  have hzero : f = 0 := norm_eq_zero.mp (le_antisymm hf (norm_nonneg f))
  have huezero : u =ᵐ[volume] (fun _ : Vec d => (0 : ℂ)) := by
    rw [hzero] at hue
    exact hue.trans (Lp.coeFn_zero ℂ 2 (volume : Measure (Vec d)))
  exact u4_continuous_physical_representative_unique u 0 hu continuous_const huezero

/-- Restricting a representative to a measurable set cannot increase its
physical L² norm. -/
theorem u4_local_L2_le_global {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hue : u =ᵐ[volume] f) (E : Set (Vec d)) (hE : MeasurableSet E) :
    (eLpNorm (E.indicator u) 2 volume).toReal ≤ ‖f‖ := by
  have heq : E.indicator u =ᵐ[volume] E.indicator (fun z => f z) := by
    filter_upwards [hue] with z hz
    by_cases hzE : z ∈ E <;> simp [Set.indicator, hzE, hz]
  rw [eLpNorm_congr_ae heq]
  simpa only [← Lp.norm_def] using
    (ENNReal.toReal_mono (Lp.memLp f).ne (eLpNorm_indicator_le (fun z => f z) hE))

theorem u4_cutoff_L2_le_local_L2 {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hue : u =ᵐ[volume] f) (E : Set (Vec d)) (hE : MeasurableSet E)
    (φ : Vec d → ℂ) (hφ : MemLp φ ∞ volume)
    (hφbound : ∀ z, ‖φ z‖ ≤ 1) (hφsupport : ∀ z ∉ E, φ z = 0) :
    ∃ w : Lp ℂ 2 (volume : Measure (Vec d)),
      (w : Vec d → ℂ) =ᵐ[volume] (fun z => φ z * f z) ∧
      ‖w‖ ≤ (eLpNorm (E.indicator u) 2 volume).toReal := by
  have hw : MemLp (fun z => φ z * f z) 2 volume := hφ.fun_mul (Lp.memLp f)
  refine ⟨hw.toLp _, hw.coeFn_toLp, ?_⟩
  have heq : E.indicator u =ᵐ[volume] E.indicator (fun z => f z) := by
    filter_upwards [hue] with z hz
    by_cases hzE : z ∈ E <;> simp [Set.indicator, hzE, hz]
  have hne : eLpNorm (E.indicator u) 2 volume ≠ ∞ := by
    rw [eLpNorm_congr_ae heq]
    exact ne_of_lt (lt_of_le_of_lt (eLpNorm_indicator_le (fun z => f z) hE)
      (Lp.memLp f))
  have hdom : ∀ᵐ z ∂volume, ‖φ z * f z‖ ≤ ‖E.indicator u z‖ := by
    filter_upwards [hue] with z hz
    by_cases hzE : z ∈ E
    · rw [Set.indicator_of_mem hzE, hz, norm_mul]
      simpa using mul_le_mul_of_nonneg_right (hφbound z) (norm_nonneg (f z))
    · simp [Set.indicator_of_notMem hzE, hφsupport z hzE]
  rw [Lp.norm_def, eLpNorm_congr_ae hw.coeFn_toLp]
  exact ENNReal.toReal_mono hne (eLpNorm_mono_ae hw.aestronglyMeasurable hdom)

theorem u4_physicalH1Graph_cutoff_local_L2 {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hf : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (u : Vec d → ℂ) (hue : u =ᵐ[volume] f)
    (E : Set (Vec d)) (hE : MeasurableSet E)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun z => (φ z : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun z => (coordinateDerivative j φ z : ℂ)) ∞ volume)
    (hφbound : ∀ z, ‖(φ z : ℂ)‖ ≤ 1) (hφsupport : ∀ z ∉ E, φ z = 0) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun z => (φ z : ℂ) * f z) ∧
      (∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun z => (φ z : ℂ) * G j z + f z * (coordinateDerivative j φ z : ℂ))) ∧
      ‖w‖ ≤ (eLpNorm (E.indicator u) 2 volume).toReal := by
  obtain ⟨w, J, hgraph, hw, hJ⟩ := physicalH1Graph_mul_smooth φ hφ hφb hDφ f G hf
  obtain ⟨v, hv, hvbound⟩ := u4_cutoff_L2_le_local_L2 f u hue E hE
    (fun z => (φ z : ℂ)) hφb hφbound (fun z hz => by simp [hφsupport z hz])
  have hwv : w = v := Lp.ext (hw.trans hv.symm)
  refine ⟨w, J, hgraph, hw, hJ, ?_⟩
  simpa only [hwv] using hvbound

theorem u4_physicalH1Graph_add {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u + v) (fun j => G j + H j) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (u + v) (fun j => G j + H j) _ _ (Lp.coeFn_add u v)
    (fun j => Lp.coeFn_add (G j) (H j))]
  exact ⟨fun j => by simpa only [Pi.add_apply, Complex.add_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j),
    fun j => by simpa only [Pi.add_apply, Complex.add_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)⟩

/-- The zero physical L² class has zero weak gradient. -/
theorem u4_physicalH1Graph_zero {d : ℕ} :
    IsPhysicalH1Graph volume (Or.inl rfl)
      (0 : Lp ℂ 2 (volume : Measure (Vec d))) (fun _ => 0) := by
  have hz (j : Fin d) : HasWeakPartialDerivative Set.univ j
      (fun _ : Vec d => (0 : ℝ)) (fun _ => 0) := by
    refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ _
    simp
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun _ => 0) (fun _ _ => 0) (Lp.coeFn_zero ℂ 2 volume)
    (fun _ => Lp.coeFn_zero ℂ 2 volume)).2
  exact ⟨fun j => hz j, fun j => hz j⟩

/-- Finite sums of physical weak graphs have the sum of their gradients. -/
theorem u4_physicalH1Graph_finset_sum {d : ℕ} {ι : Type*}
    (s : Finset ι) (u : ι → Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ι → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (h : ∀ i ∈ s, IsPhysicalH1Graph volume (Or.inl rfl) (u i) (G i)) :
    IsPhysicalH1Graph volume (Or.inl rfl) (s.sum u)
      (fun j => s.sum (fun i => G i j)) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _
    simpa using (u4_physicalH1Graph_zero (d := d))
  | @insert i s hi ih =>
    intro h
    have h' : ∀ k ∈ s, IsPhysicalH1Graph volume (Or.inl rfl) (u k) (G k) :=
      fun k hk => h k (Finset.mem_insert_of_mem hk)
    have hg := u4_physicalH1Graph_add (h i (Finset.mem_insert_self i s)) (ih h')
    simpa only [Finset.sum_insert hi] using hg

/-- Zero local L² mass forces a continuous representative to vanish throughout
the open region, not just almost everywhere. -/
theorem u4_continuous_eq_zero_on_open_of_local_L2_eq_zero {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hu : Continuous u) (hue : u =ᵐ[volume] f)
    (E : Set (Vec d)) (hE : IsOpen E)
    (hzero : (eLpNorm (E.indicator u) 2 volume).toReal = 0) :
    Set.EqOn u 0 E := by
  have heq : E.indicator u =ᵐ[volume] E.indicator (fun z => f z) := by
    filter_upwards [hue] with z hz
    by_cases hzE : z ∈ E <;> simp [Set.indicator, hzE, hz]
  have hle : eLpNorm (E.indicator u) 2 volume ≤ eLpNorm (fun z => f z) 2 volume := by
    rw [eLpNorm_congr_ae heq]
    exact eLpNorm_indicator_le (fun z => f z) hE.measurableSet
  have hne : eLpNorm (E.indicator u) 2 volume ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hle (Lp.memLp f))
  have hnorm : eLpNorm (E.indicator u) 2 volume = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hne
  have hae : E.indicator u =ᵐ[volume] (0 : Vec d → ℂ) :=
    (eLpNorm_eq_zero_iff (by norm_num)).mp hnorm
  have haer : u =ᵐ[volume.restrict E] (0 : Vec d → ℂ) := by
    apply (ae_restrict_iff' hE.measurableSet).2
    filter_upwards [hae] with z hz hzE
    simpa [Set.indicator, hzE] using hz
  exact Measure.eqOn_open_of_ae_eq haer hE hu.continuousOn continuous_const.continuousOn

theorem u4_fderiv_eq_zero_on_open_of_local_L2_eq_zero {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hu : Continuous u) (hue : u =ᵐ[volume] f)
    (E : Set (Vec d)) (hE : IsOpen E)
    (hzero : (eLpNorm (E.indicator u) 2 volume).toReal = 0)
    (x : Vec d) (hx : x ∈ E) : fderiv ℝ u x = 0 := by
  have heq := u4_continuous_eq_zero_on_open_of_local_L2_eq_zero f u hu hue E hE hzero
  have hlocal : u =ᶠ[𝓝 x] (0 : Vec d → ℂ) := by
    filter_upwards [hE.mem_nhds hx] with z hz
    exact heq hz
  simpa using hlocal.fderiv_eq

theorem u4_C1_quantity_eq_zero_on_open_of_local_L2_eq_zero {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hu : Continuous u) (hue : u =ᵐ[volume] f)
    (E : Set (Vec d)) (hE : IsOpen E)
    (hzero : (eLpNorm (E.indicator u) 2 volume).toReal = 0)
    (x : Vec d) (hx : x ∈ E) :
    ‖u x‖ + Real.sqrt (∑ j : Fin d,
      ‖fderiv ℝ u x (unitVector j)‖ ^ 2) = 0 := by
  have hu0 := u4_continuous_eq_zero_on_open_of_local_L2_eq_zero f u hu hue E hE hzero hx
  have hder := u4_fderiv_eq_zero_on_open_of_local_L2_eq_zero f u hu hue E hE hzero x hx
  simp [hu0, hder]

theorem u4_unitBall_local_L2_bounds_and_zero_case {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
    (hu : Continuous u) (hue : u =ᵐ[volume] f) (x : Vec d) :
    let L := (eLpNorm
      ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
    0 ≤ L ∧ L ≤ ‖f‖ ∧
      (L = 0 → ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) = 0) := by
  let E : Set (Vec d) := {z : Vec d | euclideanNorm (x - z) < 1}
  have hE : IsOpen E := isOpen_lt
    ((Entropy.continuous_euclideanNorm' (d := d)).comp
      (continuous_const.sub continuous_id)) continuous_const
  have hx : x ∈ E := by
    simp [E, euclideanNorm, euclideanSq, dot]
  refine ⟨ENNReal.toReal_nonneg, u4_local_L2_le_global f u hue E hE.measurableSet, ?_⟩
  intro hzero
  exact u4_C1_quantity_eq_zero_on_open_of_local_L2_eq_zero f u hu hue E hE hzero x hx

/-- When the local mass is bounded by the global scale, the interpolation
term already dominates the local mass. -/
theorem u4_local_mass_le_interpolation (L R θ : ℝ)
    (hL : 0 ≤ L) (hLR : L ≤ R) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    L ≤ L ^ θ * R ^ (1 - θ) := by
  have hpow := Real.rpow_le_rpow hL hLR (sub_nonneg.mpr hθ1)
  have hfactor : L ^ θ * L ^ (1 - θ) = L := by
    rw [← Real.rpow_add_of_nonneg hL hθ (sub_nonneg.mpr hθ1)]
    simp
  calc
    L = L ^ θ * L ^ (1 - θ) := hfactor.symm
    _ ≤ L ^ θ * R ^ (1 - θ) :=
      mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hL θ)

/-- Translate a central unit-ball cutoff to the point where it is needed. -/
theorem u4_translate_unitBall_cutoff {d : ℕ} (η : Vec d → ℝ) (a : ℝ)
    (ha : 0 < a) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hsupport : ∀ z ∈ tsupport η, euclideanNorm z ≤ 1 / 2)
    (hbound : ∀ z, 0 ≤ η z ∧ η z ≤ 1)
    (hone : ∀ z, euclideanNorm z ≤ 2 * a → η z = 1) (x : Vec d) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧
      (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) ∧ φ x = 1 ∧
      (∀ z, ¬ euclideanNorm (x - z) < 1 → φ z = 0) := by
  refine ⟨fun z => η (z - x), hη.comp (contDiff_id.sub contDiff_const),
    fun z => hbound (z - x), ?_, ?_⟩
  · apply hone
    simp [euclideanNorm, euclideanSq, dot, ha.le]
  · intro z hz
    by_contra hne
    have hmem : z - x ∈ tsupport η := subset_closure hne
    have hsmall := hsupport (z - x) hmem
    have hnorm : euclideanNorm (x - z) = euclideanNorm (z - x) := by
      rw [← neg_sub z x, Entropy.euclideanNorm_neg']
    rw [hnorm] at hz
    linarith

/-- Translation preserves compact support of a spatial cutoff. -/
theorem u4_translated_cutoff_hasCompactSupport {d : ℕ} (η : Vec d → ℝ)
    (hη : HasCompactSupport η) (x : Vec d) :
    HasCompactSupport (fun z => η (z - x)) := by
  simpa [sub_eq_add_neg, Function.comp_def] using
    hη.comp_homeomorph (Homeomorph.addRight (-x))

/-- Smooth compact cutoffs and their coordinate derivatives are bounded multipliers. -/
theorem u4_smooth_compact_cutoff_memLp {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    MemLp (fun z => (φ z : ℂ)) ∞ volume ∧
      ∀ j, MemLp (fun z => (coordinateDerivative j φ z : ℂ)) ∞ volume := by
  constructor
  · exact (Complex.continuous_ofReal.comp hφ.continuous).memLp_top_of_hasCompactSupport
      (hc.comp_left (g := Complex.ofReal) rfl) volume
  · intro j
    have hd : Continuous (coordinateDerivative j φ) := by
      exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdc : HasCompactSupport (coordinateDerivative j φ) :=
      hc.fderiv_apply ℝ (unitVector j)
    exact (Complex.continuous_ofReal.comp hd).memLp_top_of_hasCompactSupport
      (hdc.comp_left (g := Complex.ofReal) rfl) volume

/-- Every iterated coordinate derivative of a smooth compact cutoff remains
smooth, compactly supported, and an admissible bounded multiplier. -/
theorem u4_iterated_cutoff_derivative_regular {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) :
    let ψ := path.foldr coordinateDerivative φ
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      MemLp (fun z => (ψ z : ℂ)) ∞ volume ∧
      ∀ j, MemLp (fun z => (coordinateDerivative j ψ z : ℂ)) ∞ volume := by
  have hregular : ContDiff ℝ (⊤ : ℕ∞) (path.foldr coordinateDerivative φ) ∧
      HasCompactSupport (path.foldr coordinateDerivative φ) := by
    induction path with
    | nil => exact ⟨hφ, hc⟩
    | cons j path ih =>
      exact ⟨(contDiff_infty_iff_fderiv.mp ih.1).2.clm_apply contDiff_const,
        ih.2.fderiv_apply ℝ (unitVector j)⟩
  exact ⟨hregular.1, hregular.2,
    u4_smooth_compact_cutoff_memLp _ hregular.1 hregular.2⟩

/-- Multiplying a graph by any iterated cutoff derivative yields its actual
weak product graph. -/
theorem u4_iterated_cutoff_derivative_graph {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    let ψ := path.foldr coordinateDerivative φ
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun z => (ψ z : ℂ) * v z) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun z => (ψ z : ℂ) * H j z + v z * (coordinateDerivative j ψ z : ℂ)) := by
  obtain ⟨hψ, _, hψb, hDψ⟩ := u4_iterated_cutoff_derivative_regular φ hφ hc path
  exact physicalH1Graph_mul_smooth _ hψ hψb hDψ v H hv

/-- Each iterated cutoff derivative has a finite pointwise bound. -/
theorem u4_iterated_cutoff_derivative_bound {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, ‖path.foldr coordinateDerivative φ z‖ ≤ B := by
  obtain ⟨hψ, hcψ, _, _⟩ := u4_iterated_cutoff_derivative_regular φ hφ hc path
  obtain ⟨B, hB⟩ := hψ.continuous.bounded_above_of_compact_support hcψ
  exact ⟨B, (norm_nonneg _).trans (hB 0), hB⟩

/-- The derivatives of a smooth compact cutoff through a fixed order have a
common pointwise bound. -/
theorem u4_cutoff_derivatives_uniform_bound {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ path : List (Fin d), path.length ≤ N →
      ∀ z, ‖path.foldr coordinateDerivative φ z‖ ≤ B := by
  classical
  let bound : List (Fin d) → ℝ := fun path =>
    Classical.choose (u4_iterated_cutoff_derivative_bound φ hφ hc path)
  have hb (path : List (Fin d)) :
      ∀ z, ‖path.foldr coordinateDerivative φ z‖ ≤ bound path :=
    (Classical.choose_spec (u4_iterated_cutoff_derivative_bound φ hφ hc path)).2
  have hf := (List.finite_length_le (Fin d) N).image bound
  obtain ⟨B, hB⟩ := hf.bddAbove
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro path hp z
  exact (hb path z).trans ((hB ⟨path, hp, rfl⟩).trans (le_max_right _ _))

/-- An iterated cutoff multiplier inherits its pointwise bound as an L²
operator bound on the corresponding product graph. -/
theorem u4_iterated_cutoff_derivative_graph_L2_bound {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (B : ℝ) (hB : ∀ z, ‖path.foldr coordinateDerivative φ z‖ ≤ B) :
    let ψ := path.foldr coordinateDerivative φ
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun z => (ψ z : ℂ) * v z) ∧
      (∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun z => (ψ z : ℂ) * H j z + v z * (coordinateDerivative j ψ z : ℂ))) ∧
      ‖w‖ ≤ B * ‖v‖ := by
  obtain ⟨w, J, hw, hwe, hJe⟩ := u4_iterated_cutoff_derivative_graph φ hφ hc path v H hv
  refine ⟨w, J, hw, hwe, hJe, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [hwe] with z hz
  rw [hz, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)

/-- The weak derivative of a cutoff product has the expected two-term L²
bound when the cutoff and its first derivatives share a pointwise bound. -/
theorem u4_cutoff_graph_derivative_L2_bound {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (B : ℝ) (hφB : ∀ z, ‖φ z‖ ≤ B)
    (hDB : ∀ j z, ‖coordinateDerivative j φ z‖ ≤ B) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun z => (φ z : ℂ) * v z) ∧
      (∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun z => (φ z : ℂ) * H j z + v z * (coordinateDerivative j φ z : ℂ))) ∧
      ∀ j, ‖J j‖ ≤ B * (‖H j‖ + ‖v‖) := by
  obtain ⟨hφb, hDφ⟩ := u4_smooth_compact_cutoff_memLp φ hφ hc
  obtain ⟨w, J, hw, hwe, hJe⟩ := physicalH1Graph_mul_smooth φ hφ hφb hDφ v H hv
  refine ⟨w, J, hw, hwe, hJe, ?_⟩
  intro j
  have ha : MemLp (fun z => (φ z : ℂ) * H j z) 2 volume :=
    hφb.fun_mul (Lp.memLp (H j))
  have hb : MemLp (fun z => v z * (coordinateDerivative j φ z : ℂ)) 2 volume :=
    (Lp.memLp v).fun_mul (hDφ j)
  let a := ha.toLp _
  let b := hb.toLp _
  have hJa : J j = a + b := by
    apply Lp.ext
    filter_upwards [hJe j, ha.coeFn_toLp, hb.coeFn_toLp, Lp.coeFn_add a b] with z hz ha' hb' hab
    rw [hab, Pi.add_apply, ha', hb']
    exact hz
  have han : ‖a‖ ≤ B * ‖H j‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [ha.coeFn_toLp] with z hz
    rw [hz, norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hφB z) (norm_nonneg _)
  have hbn : ‖b‖ ≤ B * ‖v‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hb.coeFn_toLp] with z hz
    rw [hz, norm_mul, Complex.norm_real, mul_comm]
    exact mul_le_mul_of_nonneg_right (hDB j z) (norm_nonneg _)
  calc
    ‖J j‖ = ‖a + b‖ := by rw [hJa]
    _ ≤ ‖a‖ + ‖b‖ := norm_add_le _ _
    _ ≤ B * (‖H j‖ + ‖v‖) := by nlinarith


/-- Iterated coordinate derivatives commute with translation. -/
theorem u4_iterated_cutoff_derivative_translate {d : ℕ} (η : Vec d → ℝ)
    (path : List (Fin d)) (x z : Vec d) :
    path.foldr coordinateDerivative (fun y => η (y - x)) z =
      path.foldr coordinateDerivative η (z - x) := by
  induction path generalizing z with
  | nil => rfl
  | cons j path ih =>
    have heq : path.foldr coordinateDerivative (fun y => η (y - x)) =
        fun y => path.foldr coordinateDerivative η (y - x) := funext ih
    simp only [List.foldr_cons, heq, coordinateDerivative, fderiv_comp_sub]

/-- A fixed cutoff has translation-uniform bounds on all coordinate derivatives
through any prescribed finite order. -/
theorem u4_translated_cutoff_derivatives_uniform_bound {d : ℕ} (η : Vec d → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hc : HasCompactSupport η) (N : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Vec d, ∀ path : List (Fin d), path.length ≤ N →
      ∀ z, ‖path.foldr coordinateDerivative (fun y => η (y - x)) z‖ ≤ B := by
  obtain ⟨B, hB, hb⟩ := u4_cutoff_derivatives_uniform_bound η hη hc N
  refine ⟨B, hB, ?_⟩
  intro x path hp z
  rw [u4_iterated_cutoff_derivative_translate]
  exact hb path hp (z - x)


/-- A translated cutoff is identically one near its center. -/
theorem u4_translated_cutoff_eventually_one {d : ℕ} (η : Vec d → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hone : ∀ z, euclideanNorm z ≤ 2 * a → η z = 1) (x : Vec d) :
    (fun z => η (z - x)) =ᶠ[𝓝 x] (fun _ => 1) := by
  have hE : IsOpen {z : Vec d | euclideanNorm (z - x) < 2 * a} :=
    isOpen_lt ((Entropy.continuous_euclideanNorm' (d := d)).comp
      (continuous_id.sub continuous_const)) continuous_const
  have hx : x ∈ {z : Vec d | euclideanNorm (z - x) < 2 * a} := by
    simp [euclideanNorm, euclideanSq, dot, ha]
  filter_upwards [hE.mem_nhds hx] with z hz
  exact hone (z - x) hz.le

/-- Cutting off near the center preserves the value and derivative there. -/
theorem u4_translated_cutoff_value_fderiv {d : ℕ} (η : Vec d → ℝ)
    (a : ℝ) (ha : 0 < a)
    (hone : ∀ z, euclideanNorm z ≤ 2 * a → η z = 1)
    (u : Vec d → ℂ) (x : Vec d) :
    (η (x - x) : ℂ) * u x = u x ∧
      fderiv ℝ (fun z => (η (z - x) : ℂ) * u z) x = fderiv ℝ u x := by
  have heq : (fun z => (η (z - x) : ℂ) * u z) =ᶠ[𝓝 x] u := by
    filter_upwards [u4_translated_cutoff_eventually_one η a ha hone x] with z hz
    simp [hz]
  exact ⟨heq.self_of_nhds, heq.fderiv_eq⟩

/-- The L² class of one term in the iterated cutoff product rule. -/
noncomputable def u4CutoffDerivativeTerm {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d))) :
    Lp ℂ 2 (volume : Measure (Vec d)) :=
  ((u4_iterated_cutoff_derivative_regular φ hφ hc path).2.2.1.fun_mul
    (Lp.memLp v)).toLp _

theorem u4_cutoff_derivative_term_ae {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d))) :
    (u4CutoffDerivativeTerm φ hφ hc path v : Vec d → ℂ) =ᵐ[volume]
      fun z => (path.foldr coordinateDerivative φ z : ℂ) * v z :=
  ((u4_iterated_cutoff_derivative_regular φ hφ hc path).2.2.1.fun_mul
    (Lp.memLp v)).coeFn_toLp

/-- The actual weak gradient of each cutoff term is the two-term product rule. -/
theorem u4_cutoff_derivative_term_graph {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u4CutoffDerivativeTerm φ hφ hc path v)
      (fun j => u4CutoffDerivativeTerm φ hφ hc path (H j) +
        u4CutoffDerivativeTerm φ hφ hc (j :: path) v) := by
  obtain ⟨w, J, hgraph, hw, hJ⟩ :=
    u4_iterated_cutoff_derivative_graph φ hφ hc path v H hv
  have hw' : w = u4CutoffDerivativeTerm φ hφ hc path v :=
    Lp.ext (hw.trans (u4_cutoff_derivative_term_ae φ hφ hc path v).symm)
  have hJ' : J = fun j => u4CutoffDerivativeTerm φ hφ hc path (H j) +
      u4CutoffDerivativeTerm φ hφ hc (j :: path) v := by
    funext j
    apply Lp.ext
    filter_upwards [hJ j, u4_cutoff_derivative_term_ae φ hφ hc path (H j),
      u4_cutoff_derivative_term_ae φ hφ hc (j :: path) v,
      Lp.coeFn_add (u4CutoffDerivativeTerm φ hφ hc path (H j))
        (u4CutoffDerivativeTerm φ hφ hc (j :: path) v)] with z hz ha hb hab
    rw [hz, hab]
    change _ = (u4CutoffDerivativeTerm φ hφ hc path (H j) : Vec d → ℂ) z +
      (u4CutoffDerivativeTerm φ hφ hc (j :: path) v : Vec d → ℂ) z
    rw [ha, hb]
    simp only [List.foldr_cons]
    ring
  simpa only [hw', hJ'] using hgraph

/-- A cutoff term inherits a uniform pointwise multiplier bound in L². -/
theorem u4_cutoff_derivative_term_norm_le {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (path : List (Fin d)) (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (B : ℝ) (hB : ∀ z, ‖path.foldr coordinateDerivative φ z‖ ≤ B) :
    ‖u4CutoffDerivativeTerm φ hφ hc path v‖ ≤ B * ‖v‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [u4_cutoff_derivative_term_ae φ hφ hc path v] with z hz
  rw [hz, norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hB z) (norm_nonneg _)

/-- Finite lists of physical weak graphs have the sum of their gradients. -/
theorem u4_physicalH1Graph_list_sum {d : ℕ} {ι : Type*}
    (items : List ι) (u : ι → Lp ℂ 2 (volume : Measure (Vec d)))
    (G : ι → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (h : ∀ item ∈ items, IsPhysicalH1Graph volume (Or.inl rfl) (u item) (G item)) :
    IsPhysicalH1Graph volume (Or.inl rfl) (items.map u).sum
      (fun j => (items.map (fun item => G item j)).sum) := by
  revert h
  induction items with
  | nil =>
    intro _
    simpa using (u4_physicalH1Graph_zero (d := d))
  | cons item items ih =>
    intro h
    have hitem : IsPhysicalH1Graph volume (Or.inl rfl) (u item) (G item) :=
      h item (by simp)
    have htail : ∀ index ∈ items,
        IsPhysicalH1Graph volume (Or.inl rfl) (u index) (G index) :=
      fun index hindex => h index (by simp [hindex])
    simpa only [List.map_cons, List.sum_cons] using
      u4_physicalH1Graph_add hitem (ih htail)

/-- A finite Leibniz family has its termwise cutoff-product weak gradient. -/
theorem u4_cutoff_derivative_family_graph {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])))
    (items : List (List (Fin d) × List (Fin d)))
    (hitems : ∀ item ∈ items, item.2.length < N) :
    IsPhysicalH1Graph volume (Or.inl rfl)
      (items.map (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum
      (fun j => (items.map (fun item =>
        u4CutoffDerivativeTerm φ hφ hc item.1 (F (item.2 ++ [j])) +
        u4CutoffDerivativeTerm φ hφ hc (j :: item.1) (F item.2))).sum) := by
  apply u4_physicalH1Graph_list_sum
  intro item hitem
  exact u4_cutoff_derivative_term_graph φ hφ hc item.1 (F item.2)
    (fun j => F (item.2 ++ [j])) (hF item.2 (hitems item hitem))

/-- One coordinate derivative distributes over every term of a Leibniz family. -/
def u4CutoffLeibnizStep {d : ℕ} (j : Fin d)
    (items : List (List (Fin d) × List (Fin d))) :
    List (List (Fin d) × List (Fin d)) :=
  items.flatMap (fun item => [(item.1, item.2 ++ [j]), (j :: item.1, item.2)])

theorem u4_cutoff_leibniz_step_sum {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (items : List (List (Fin d) × List (Fin d))) (j : Fin d) :
    ((u4CutoffLeibnizStep j items).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum =
      (items.map (fun item =>
        u4CutoffDerivativeTerm φ hφ hc item.1 (F (item.2 ++ [j])) +
        u4CutoffDerivativeTerm φ hφ hc (j :: item.1) (F item.2))).sum := by
  induction items with
  | nil => simp [u4CutoffLeibnizStep]
  | cons item items ih =>
    simp only [u4CutoffLeibnizStep, List.flatMap_cons, List.map_append,
      List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
      add_zero] at ih ⊢
    rw [ih]

/-- The expanded Leibniz family is the actual weak gradient of the original family. -/
theorem u4_cutoff_leibniz_step_graph {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])))
    (items : List (List (Fin d) × List (Fin d)))
    (hitems : ∀ item ∈ items, item.2.length < N) :
    IsPhysicalH1Graph volume (Or.inl rfl)
      (items.map (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum
      (fun j => ((u4CutoffLeibnizStep j items).map
        (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum) := by
  have h := u4_cutoff_derivative_family_graph φ hφ hc F hF items hitems
  simpa only [u4_cutoff_leibniz_step_sum] using h

/-- The full iterated product rule retains the order of the derivative path. -/
def u4CutoffLeibnizFamily {d : ℕ} (path : List (Fin d)) :
    List (List (Fin d) × List (Fin d)) :=
  path.foldl (fun items j => u4CutoffLeibnizStep j items) [([], [])]

theorem u4_cutoff_leibniz_family_append {d : ℕ}
    (path : List (Fin d)) (j : Fin d) :
    u4CutoffLeibnizFamily (path ++ [j]) =
      u4CutoffLeibnizStep j (u4CutoffLeibnizFamily path) := by
  simp [u4CutoffLeibnizFamily, List.foldl_append]

theorem u4_cutoff_leibniz_step_length {d : ℕ} (j : Fin d)
    (items : List (List (Fin d) × List (Fin d))) :
    (u4CutoffLeibnizStep j items).length = 2 * items.length := by
  induction items with
  | nil => simp [u4CutoffLeibnizStep]
  | cons item items ih =>
    simp only [u4CutoffLeibnizStep, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at ih ⊢
    omega

theorem u4_cutoff_leibniz_family_length {d : ℕ} (path : List (Fin d)) :
    (u4CutoffLeibnizFamily path).length = 2 ^ path.length := by
  induction path using List.reverseRecOn with
  | nil => simp [u4CutoffLeibnizFamily]
  | append_singleton path j ih =>
    rw [u4_cutoff_leibniz_family_append, u4_cutoff_leibniz_step_length, ih]
    simp only [List.length_append, List.length_singleton, pow_succ]
    omega

theorem u4_cutoff_leibniz_family_order {d : ℕ} (path : List (Fin d))
    (item : List (Fin d) × List (Fin d))
    (hitem : item ∈ u4CutoffLeibnizFamily path) :
    item.1.length + item.2.length = path.length := by
  induction path using List.reverseRecOn generalizing item with
  | nil =>
    simp [u4CutoffLeibnizFamily] at hitem
    subst item
    rfl
  | append_singleton path j ih =>
    rw [u4_cutoff_leibniz_family_append] at hitem
    obtain ⟨previous, hprevious, hstep⟩ := List.mem_flatMap.mp hitem
    have horder := ih previous hprevious
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hstep
    rcases hstep with hstep | hstep
    · subst item
      simp only [List.length_append, List.length_singleton] at horder ⊢
      omega
    · subst item
      simp only [List.length_cons, List.length_append, List.length_nil] at horder ⊢
      omega

/-- The iterated cutoff family is itself a physical weak derivative chain. -/
theorem u4_cutoff_leibniz_chain_graph {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
      (F p) (fun j => F (p ++ [j])))
    (path : List (Fin d)) (hpath : path.length < N) :
    IsPhysicalH1Graph volume (Or.inl rfl)
      ((u4CutoffLeibnizFamily path).map
        (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum
      (fun j => ((u4CutoffLeibnizFamily (path ++ [j])).map
        (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum) := by
  have hitems : ∀ item ∈ u4CutoffLeibnizFamily path, item.2.length < N := by
    intro item hitem
    have horder := u4_cutoff_leibniz_family_order path item hitem
    omega
  have h := u4_cutoff_leibniz_step_graph φ hφ hc F hF
    (u4CutoffLeibnizFamily path) hitems
  simpa only [u4_cutoff_leibniz_family_append] using h

/-- A finite cutoff Leibniz family inherits a uniform L² bound term by term. -/
theorem u4_cutoff_derivative_family_L2_bound {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (B R : ℝ) (hB : 0 ≤ B)
    (hcut : ∀ (p : List (Fin d)), p.length ≤ N → ∀ z, ‖p.foldr coordinateDerivative φ z‖ ≤ B)
    (hF : ∀ p, p.length ≤ N → ‖F p‖ ≤ R)
    (items : List (List (Fin d) × List (Fin d)))
    (hitems : ∀ item ∈ items, item.1.length ≤ N ∧ item.2.length ≤ N) :
    ‖(items.map (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum‖ ≤
      (items.length : ℝ) * (B * R) := by
  revert hitems
  induction items with
  | nil => intro _; simp
  | cons item items ih =>
    intro hitems
    have hitem := hitems item (by simp)
    have htail : ∀ index ∈ items, index.1.length ≤ N ∧ index.2.length ≤ N :=
      fun index hindex => hitems index (by simp [hindex])
    have hterm : ‖u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2)‖ ≤ B * R :=
      (u4_cutoff_derivative_term_norm_le φ hφ hc item.1 (F item.2) B
        (hcut item.1 hitem.1)).trans (mul_le_mul_of_nonneg_left (hF item.2 hitem.2) hB)
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one]
    calc
      ‖u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2) +
          (items.map (fun index => u4CutoffDerivativeTerm φ hφ hc index.1 (F index.2))).sum‖
          ≤ ‖u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2)‖ +
            ‖(items.map (fun index => u4CutoffDerivativeTerm φ hφ hc index.1 (F index.2))).sum‖ :=
              norm_add_le _ _
      _ ≤ B * R + (items.length : ℝ) * (B * R) := add_le_add hterm (ih htail)
      _ = ((items.length : ℝ) + 1) * (B * R) := by ring

theorem u4_cutoff_leibniz_family_L2_bound {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (B R : ℝ) (hB : 0 ≤ B)
    (hcut : ∀ (p : List (Fin d)), p.length ≤ N → ∀ z, ‖p.foldr coordinateDerivative φ z‖ ≤ B)
    (hF : ∀ p, p.length ≤ N → ‖F p‖ ≤ R)
    (path : List (Fin d)) (hpath : path.length ≤ N) :
    ‖((u4CutoffLeibnizFamily path).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum‖ ≤
      ((u4CutoffLeibnizFamily path).length : ℝ) * (B * R) := by
  apply u4_cutoff_derivative_family_L2_bound φ hφ hc F B R hB hcut hF
  intro item hitem
  have horder := u4_cutoff_leibniz_family_order path item hitem
  omega

theorem u4_cutoff_leibniz_family_uniform_L2_bound {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hcut : ∀ (p : List (Fin d)), p.length ≤ N → ∀ z, ‖p.foldr coordinateDerivative φ z‖ ≤ B)
    (hF : ∀ p, p.length ≤ N → ‖F p‖ ≤ R)
    (path : List (Fin d)) (hpath : path.length ≤ N) :
    ‖((u4CutoffLeibnizFamily path).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum‖ ≤
      (2 : ℝ) ^ N * (B * R) := by
  have h := u4_cutoff_leibniz_family_L2_bound φ hφ hc F B R hB hcut hF path hpath
  rw [u4_cutoff_leibniz_family_length, Nat.cast_pow, Nat.cast_ofNat] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hpath) (mul_nonneg hB hR))

/-- The zeroth term of the weak chain is the cutoff of the original class. -/
theorem u4_cutoff_leibniz_family_zero_ae {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) :
    (((u4CutoffLeibnizFamily []).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum :
      Vec d → ℂ) =ᵐ[volume] (fun z => (φ z : ℂ) * F [] z) := by
  simpa [u4CutoffLeibnizFamily] using
    (u4_cutoff_derivative_term_ae φ hφ hc [] (F []))

/-- The zeroth chain term is controlled by the local mass of the representative. -/
theorem u4_cutoff_leibniz_family_zero_local_L2 {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (u : Vec d → ℂ) (hue : u =ᵐ[volume] (F []))
    (E : Set (Vec d)) (hE : MeasurableSet E)
    (hφbound : ∀ z, ‖(φ z : ℂ)‖ ≤ 1) (hφsupport : ∀ z ∉ E, φ z = 0) :
    ‖((u4CutoffLeibnizFamily []).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum‖ ≤
      (eLpNorm (E.indicator u) 2 volume).toReal := by
  obtain ⟨hφb, _⟩ := u4_smooth_compact_cutoff_memLp φ hφ hc
  obtain ⟨w, hw, hwbound⟩ := u4_cutoff_L2_le_local_L2 (F []) u hue E hE
    (fun z => (φ z : ℂ)) hφb hφbound (fun z hz => by simp [hφsupport z hz])
  have hzero : ((u4CutoffLeibnizFamily []).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum = w :=
    Lp.ext ((u4_cutoff_leibniz_family_zero_ae φ hφ hc F).trans hw.symm)
  simpa only [hzero] using hwbound

/-- A smooth compact cutoff turns the original chain into a bounded weak chain,
whose zeroth term retains the local L² mass. -/
theorem u4_cutoff_weak_chain_with_local_L2 {d N : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (E : Set (Vec d)) (hE : MeasurableSet E)
    (hφbound : ∀ z, ‖(φ z : ℂ)‖ ≤ 1) (hφsupport : ∀ z ∉ E, φ z = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ N → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, u =ᵐ[volume] (F []) →
        ∃ G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
          (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
            (G p) (fun j => G (p ++ [j]))) ∧
          (∀ p, p.length ≤ N → ‖G p‖ ≤ C * R) ∧
          (G [] : Vec d → ℂ) =ᵐ[volume] (fun z => (φ z : ℂ) * u z) ∧
          ‖G []‖ ≤ (eLpNorm (E.indicator u) 2 volume).toReal := by
  obtain ⟨B, hB, hcut⟩ := u4_cutoff_derivatives_uniform_bound φ hφ hc N
  refine ⟨(2 : ℝ) ^ N * (B + 1), by positivity, ?_⟩
  intro F R hR hF hnorm u hue
  let G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun p =>
    ((u4CutoffLeibnizFamily p).map
      (fun item => u4CutoffDerivativeTerm φ hφ hc item.1 (F item.2))).sum
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact u4_cutoff_leibniz_chain_graph φ hφ hc F hF p hp
  · intro p hp
    have h := u4_cutoff_leibniz_family_uniform_L2_bound φ hφ hc F B R hB hR
      hcut hnorm p hp
    dsimp only [G]
    calc
      _ ≤ (2 : ℝ) ^ N * (B * R) := h
      _ ≤ ((2 : ℝ) ^ N * (B + 1)) * R := by
        have hp : 0 ≤ (2 : ℝ) ^ N := by positivity
        nlinarith
  · filter_upwards [u4_cutoff_leibniz_family_zero_ae φ hφ hc F, hue] with z hz hu
    rw [hz, hu]
  · exact u4_cutoff_leibniz_family_zero_local_L2 φ hφ hc F u hue E hE hφbound hφsupport

/-- A uniformly bounded cutoff family gives one chain constant for all centers. -/
theorem u4_uniform_cutoff_weak_chain_with_local_L2 {d N : ℕ}
    (φ : Vec d → Vec d → ℝ)
    (hφ : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x))
    (hc : ∀ x, HasCompactSupport (φ x))
    (E : Vec d → Set (Vec d)) (hE : ∀ x, MeasurableSet (E x))
    (hφbound : ∀ x z, ‖(φ x z : ℂ)‖ ≤ 1)
    (hφsupport : ∀ x z, z ∉ E x → φ x z = 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hcut : ∀ x (p : List (Fin d)), p.length ≤ N → ∀ z,
      ‖p.foldr coordinateDerivative (φ x) z‖ ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ N → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, u =ᵐ[volume] (F []) → ∀ x,
        ∃ G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
          (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
            (G p) (fun j => G (p ++ [j]))) ∧
          (∀ p, p.length ≤ N → ‖G p‖ ≤ C * R) ∧
          (G [] : Vec d → ℂ) =ᵐ[volume] (fun z => (φ x z : ℂ) * u z) ∧
          ‖G []‖ ≤ (eLpNorm ((E x).indicator u) 2 volume).toReal := by
  refine ⟨(2 : ℝ) ^ N * (B + 1), by positivity, ?_⟩
  intro F R hR hF hnorm u hue x
  let G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) := fun p =>
    ((u4CutoffLeibnizFamily p).map
      (fun item => u4CutoffDerivativeTerm (φ x) (hφ x) (hc x) item.1 (F item.2))).sum
  refine ⟨G, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact u4_cutoff_leibniz_chain_graph (φ x) (hφ x) (hc x) F hF p hp
  · intro p hp
    have h := u4_cutoff_leibniz_family_uniform_L2_bound (φ x) (hφ x) (hc x)
      F B R hB hR (hcut x) hnorm p hp
    dsimp only [G]
    calc
      _ ≤ (2 : ℝ) ^ N * (B * R) := h
      _ ≤ ((2 : ℝ) ^ N * (B + 1)) * R := by
        have hp : 0 ≤ (2 : ℝ) ^ N := by positivity
        nlinarith
  · filter_upwards [u4_cutoff_leibniz_family_zero_ae (φ x) (hφ x) (hc x) F, hue] with z hz hu
    rw [hz, hu]
  · exact u4_cutoff_leibniz_family_zero_local_L2 (φ x) (hφ x) (hc x)
      F u hue (E x) (hE x) (hφbound x) (hφsupport x)

/-- One translated cutoff and one constant work for every center. -/
theorem u4_unitBall_cutoff_weak_chain {d N : ℕ} :
    ∃ (η : Vec d → ℝ) (a C : ℝ), 0 < a ∧ 0 < C ∧
      ContDiff ℝ (⊤ : ℕ∞) η ∧
      (∀ z, euclideanNorm z ≤ 2 * a → η z = 1) ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ N → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, u =ᵐ[volume] (F []) → ∀ x,
        ∃ G : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)),
          (∀ p, p.length < N → IsPhysicalH1Graph volume (Or.inl rfl)
            (G p) (fun j => G (p ++ [j]))) ∧
          (∀ p, p.length ≤ N → ‖G p‖ ≤ C * R) ∧
          (G [] : Vec d → ℂ) =ᵐ[volume] (fun z => (η (z - x) : ℂ) * u z) ∧
          ‖G []‖ ≤ (eLpNorm ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal := by
  obtain ⟨η, a, ha, hη, hc, hsupport, hbound, hone⟩ :=
    Calculus.C5TestCLT.exists_unitBall_cutoff d
  obtain ⟨B, hB, hcut⟩ := u4_translated_cutoff_derivatives_uniform_bound η hη hc N
  let φ : Vec d → Vec d → ℝ := fun x z => η (z - x)
  let E : Vec d → Set (Vec d) := fun x => {z | euclideanNorm (x - z) < 1}
  have hφ : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x) :=
    fun x => hη.comp (contDiff_id.sub contDiff_const)
  have hφc : ∀ x, HasCompactSupport (φ x) :=
    fun x => u4_translated_cutoff_hasCompactSupport η hc x
  have hE : ∀ x, MeasurableSet (E x) := fun x =>
    (isOpen_lt ((Entropy.continuous_euclideanNorm' (d := d)).comp
      (continuous_const.sub continuous_id)) continuous_const).measurableSet
  have hφb : ∀ x z, ‖(φ x z : ℂ)‖ ≤ 1 := by
    intro x z
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
    exact (hbound _).2
  have hφs : ∀ x z, z ∉ E x → φ x z = 0 := by
    intro x z hz
    by_contra hne
    have hmem : z - x ∈ tsupport η := subset_closure hne
    have hsmall := hsupport (z - x) hmem
    have hnorm : euclideanNorm (x - z) = euclideanNorm (z - x) := by
      rw [← neg_sub z x, Entropy.euclideanNorm_neg']
    change ¬ euclideanNorm (x - z) < 1 at hz
    rw [hnorm] at hz
    linarith
  obtain ⟨C, hC, hchain⟩ := u4_uniform_cutoff_weak_chain_with_local_L2
    φ hφ hφc E hE hφb hφs B hB hcut
  exact ⟨η, a, C, ha, hC, hη, hone, hchain⟩


/-- Global interpolation applied to a translated unit-ball weak chain gives
local interpolation for the original C¹ representative. -/
theorem u4_local_C1_interpolation_of_global_chain
    (hglobal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (‖F []‖ ^ θ * R ^ (1 - θ) + ‖F []‖)) :
    ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
        let L : ℝ := (eLpNorm
          ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
        ‖u x‖ + Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (L ^ θ * R ^ (1 - θ) + L) := by
  intro d
  obtain ⟨K, θ, hK, hθ, hθ1, hglobal⟩ := hglobal d
  obtain ⟨η, a, C, ha, hC, hη, hone, hchain⟩ :=
    u4_unitBall_cutoff_weak_chain (d := d) (N := d + 3)
  let A : ℝ := C ^ (1 - θ)
  have hA : 0 ≤ A := Real.rpow_nonneg hC.le _
  refine ⟨K * (A + 1) + 1, θ, by positivity, hθ, hθ1, ?_⟩
  intro F R hR hF hbound u hu hue x
  dsimp only
  let L : ℝ := (eLpNorm
    ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  obtain ⟨G, hG, hGb, hG0, hmass⟩ := hchain F R hR hF hbound u hue x
  let w : Vec d → ℂ := fun z => (η (z - x) : ℂ) * u z
  have hw : ContDiff ℝ 1 w := by
    dsimp [w]
    have hη' : ContDiff ℝ 1 (fun z : Vec d => η (z - x)) :=
      (hη.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
    exact (Complex.ofRealCLM.contDiff.comp hη').mul hu
  have hwG : w =ᵐ[volume] (G []) := hG0.symm
  have he := u4_translated_cutoff_value_fderiv η a ha hone u x
  have hwx : w x = u x := he.1
  have hwd : fderiv ℝ w x = fderiv ℝ u x := he.2
  have hscale := hglobal G (C * R) (mul_nonneg hC.le hR) hG hGb w hw hwG x
  rw [hwx, hwd] at hscale
  have hmass' : ‖G []‖ ≤ L := hmass
  have hp : ‖G []‖ ^ θ ≤ L ^ θ :=
    Real.rpow_le_rpow (norm_nonneg _) hmass' hθ.le
  have hr : (C * R) ^ (1 - θ) = A * R ^ (1 - θ) := by
    dsimp [A]
    exact Real.mul_rpow hC.le hR
  have hpowL : 0 ≤ L ^ θ := Real.rpow_nonneg hL _
  have hpowR : 0 ≤ R ^ (1 - θ) := Real.rpow_nonneg hR _
  rw [hr] at hscale
  have hprod : ‖G []‖ ^ θ * (A * R ^ (1 - θ)) ≤
      L ^ θ * (A * R ^ (1 - θ)) :=
    mul_le_mul_of_nonneg_right hp (mul_nonneg hA hpowR)
  have hsum : ‖G []‖ ^ θ * (A * R ^ (1 - θ)) + ‖G []‖ ≤
      (A + 1) * (L ^ θ * R ^ (1 - θ) + L) := by
    nlinarith [mul_nonneg hA hL, mul_nonneg hpowL hpowR]
  have hright : K * (‖G []‖ ^ θ * (A * R ^ (1 - θ)) + ‖G []‖) ≤
      (K * (A + 1) + 1) * (L ^ θ * R ^ (1 - θ) + L) := by
    have h := mul_le_mul_of_nonneg_left hsum hK.le
    nlinarith [mul_nonneg hpowL hpowR]
  exact hscale.trans hright


/-- Global weak-chain interpolation yields the local physical C¹ estimate. -/
theorem u4_physical_local_C1_interpolation_of_global_chain
    (hglobal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (‖F []‖ ^ θ * R ^ (1 - θ) + ‖F []‖))
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (D : StructuralData d) :
    ∃ B K θ : ℝ, 1 ≤ B ∧ 0 < K ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 0 < t →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
    let R := B * (1 + (t : ℝ)⁻¹) ^ (d + 3) *
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) * ‖f‖
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
      ∀ x : Vec d,
      let L : ℝ := (eLpNorm
        ({z : Vec d | euclideanNorm (x - z) < 1}.indicator u) 2 volume).toReal
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤ K * (L ^ θ * R ^ (1 - θ) + L) := by
  exact u4_physical_local_C1_interpolation_of_weak_derivatives
    u8_physical_high_weak_derivatives_C1_representative
    (u4_local_C1_interpolation_of_global_chain hglobal) hder d D


/-- The global interpolation estimate yields localized physical Gaussian bounds. -/
theorem u4_physical_local_C1_gaussian_of_global_chain
    (hglobal : ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (‖F []‖ ^ θ * R ^ (1 - θ) + ‖F []‖))
    (hoff : Blueprint.node_l_u3A_forced_u2D_local_u23_off_u2D_diagonalStmt)
    (hder : Blueprint.node_eq_u2E_reduced_u2D_bounds_u23_derivativesStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q → ∀ᵐ ω ∂reducedLaw Q,
    ∀ (i : Fin d) (ζ : ℂ), ‖ζ‖ ≤ 4 →
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
        Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalComplexSemigroup ω.1 i ζ P →
      IsPhysicalComplexTransposeSemigroup ω.1 i ζ P Pdag →
    ∀ S ∈ [P, Pdag], ∀ t : ℝ≥0, 1 ≤ (t : ℝ) →
    ∀ E : Set (Vec d), MeasurableSet E →
    ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ᵐ y ∂volume, y ∉ E → f y = 0) →
    ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (S t f : Vec d → ℂ) ∧
    ∀ (x : Vec d) (ell : ℝ), 0 ≤ ell →
      (∀ y ∈ E, ell ≤ euclideanNorm (x - y)) →
      ‖u x‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
        C * (2 + (t : ℝ)) ^ N *
          Real.exp (C * ‖ζ‖ ^ 2 * (t : ℝ) - c * ell ^ 2 / (t : ℝ)) * ‖f‖ := by
  exact u4_physical_local_C1_gaussian_of_interpolation
    u8_physical_high_weak_derivatives_C1_representative
    (u4_local_C1_interpolation_of_global_chain hglobal) hoff hder d hd D

end

end EinsteinFull

