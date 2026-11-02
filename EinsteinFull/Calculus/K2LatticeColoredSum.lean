import EinsteinFull.Calculus.S1FiniteRangeSupport
import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import EinsteinFull.Calculus.K1LpSquareSum

/-! Lattice colouring support: translated centres `r • z` of a lattice, observables local in
balls of radius `ρ`, coloured by residues mod `M`, so that each colour class is independent
under a law of finite range `r₀ < M r - 2 ρ`. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.K2
open EinsteinRelation

theorem abs_coord_le_euclideanNorm {d : ℕ} (g : Vec d) (j : Fin d) :
    |g j| ≤ euclideanNorm g := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun i => g i * g i) (fun i _ => mul_self_nonneg _)
    (Finset.mem_univ j)

theorem continuous_euclideanNorm {d : ℕ} : Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm euclideanSq dot
  fun_prop

/-- Colouring of the lattice by coordinatewise residues modulo `M`. -/
def col {d : ℕ} (M : ℕ) (hM : 0 < M) (z : Fin d → ℤ) : Fin d → Fin M :=
  fun j => ⟨((z j) % (M : ℤ)).toNat, by
    have h1 : 0 ≤ (z j) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
    have h2 : (z j) % (M : ℤ) < M := Int.emod_lt_of_pos _ (by exact_mod_cast hM)
    omega⟩

theorem col_eq_dvd {d : ℕ} {M : ℕ} (hM : 0 < M) {z z' : Fin d → ℤ}
    (h : col M hM z = col M hM z') (j : Fin d) : (M : ℤ) ∣ z j - z' j := by
  have hj := congrFun h j
  have h1 : 0 ≤ (z j) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
  have h2 : 0 ≤ (z' j) % (M : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hM.ne')
  have h3 : ((z j) % (M : ℤ)).toNat = ((z' j) % (M : ℤ)).toNat := by
    simpa [col] using hj
  have h4 : (z j) % (M : ℤ) = (z' j) % (M : ℤ) := by omega
  exact Int.ModEq.dvd h4.symm

/-- Same-colour distinct lattice points differ by at least `M` in some coordinate. -/
theorem exists_coord_far {d : ℕ} {M : ℕ} (hM : 0 < M) {z z' : Fin d → ℤ}
    (h : col M hM z = col M hM z') (hne : z ≠ z') :
    ∃ j, (M : ℤ) ≤ |z j - z' j| := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
  refine ⟨j, ?_⟩
  have hd := col_eq_dvd hM h j
  have hne' : z j - z' j ≠ 0 := sub_ne_zero.2 hj
  exact Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hd)

/-- Separation of the balls around two same-colour distinct lattice centres. -/
theorem ball_sep {d : ℕ} {M : ℕ} (hM : 0 < M) {r ρ : ℝ} (hr : 0 < r)
    {z z' : Fin d → ℤ} (h : col M hM z = col M hM z') (hne : z ≠ z')
    {x y : Vec d} (hx : euclideanNorm (x - fun j => r * (z j : ℝ)) < ρ)
    (hy : euclideanNorm (y - fun j => r * (z' j : ℝ)) < ρ) :
    (M : ℝ) * r - 2 * ρ ≤ euclideanNorm (x - y) := by
  obtain ⟨j, hj⟩ := exists_coord_far hM h hne
  have hj' : (M : ℝ) ≤ |(z j : ℝ) - (z' j : ℝ)| := by exact_mod_cast hj
  have h1 := abs_coord_le_euclideanNorm (x - fun j => r * (z j : ℝ)) j
  have h2 := abs_coord_le_euclideanNorm (y - fun j => r * (z' j : ℝ)) j
  have h3 := abs_coord_le_euclideanNorm (x - y) j
  simp only [Pi.sub_apply] at h1 h2 h3
  have h4 : r * |(z j : ℝ) - (z' j : ℝ)| = |r * (z j : ℝ) - r * (z' j : ℝ)| := by
    rw [← mul_sub, abs_mul, abs_of_pos hr]
  have h5 : (M : ℝ) * r ≤ |r * (z j : ℝ) - r * (z' j : ℝ)| := by
    rw [← h4]; nlinarith
  have h6 : |r * (z j : ℝ) - r * (z' j : ℝ)| ≤
      |x j - r * (z j : ℝ)| + |y j - r * (z' j : ℝ)| + |x j - y j| := by
    have : r * (z j : ℝ) - r * (z' j : ℝ) =
        -(x j - r * (z j : ℝ)) + (y j - r * (z' j : ℝ)) + (x j - y j) := by ring
    rw [this]
    calc _ ≤ |-(x j - r * (z j : ℝ)) + (y j - r * (z' j : ℝ))| + |x j - y j| := abs_add_le _ _
      _ ≤ _ := by
        gcongr
        calc _ ≤ |-(x j - r * (z j : ℝ))| + |y j - r * (z' j : ℝ)| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
  linarith

theorem measurableSet_ball {d : ℕ} (c : Vec d) (ρ : ℝ) :
    MeasurableSet {y : Vec d | euclideanNorm (y - c) < ρ} :=
  (isOpen_lt (continuous_euclideanNorm.comp (continuous_id.sub continuous_const))
    continuous_const).measurableSet

/-- Per-colour independence of lattice-local observables. -/
theorem iIndepFun_colour {d : ℕ} {r₀ : ℝ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hfr : HasFiniteRange r₀ μ)
    {r ρ : ℝ} (hr : 0 < r) (M : ℕ) (hM : 0 < M) (hs : r₀ < M * r - 2 * ρ)
    (f : (Fin d → ℤ) → FieldPair d → ℂ)
    (hloc : ∀ z, StronglyMeasurable[localSigma
      {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) < ρ}] (f z))
    (c : Fin d → Fin M) :
    iIndepFun (fun z : {z : Fin d → ℤ // col M hM z = c} => f z) μ := by
  classical
  refine S1.iIndepFun_of_local hfr
    (fun z : {z : Fin d → ℤ // col M hM z = c} =>
      {y : Vec d | euclideanNorm (y - fun j => r * ((z.1 j : ℤ) : ℝ)) < ρ})
    (fun z => measurableSet_ball _ _) hs ?_ (fun z => f z) (fun z => (hloc z.1).measurable)
    (fun z => Filter.EventuallyEq.rfl)
  intro z z' hzz' x hx y hy
  exact ball_sep hM hr (z.2.trans z'.2.symm) (fun h => hzz' (Subtype.ext h)) hx hy

theorem measurable_of_local {d : ℕ} {U : Set (Vec d)} {g : FieldPair d → ℂ}
    (hg : StronglyMeasurable[localSigma U] g) : Measurable g :=
  hg.measurable.mono (EinsteinRelation.Probability.localSigma_le_borel U) le_rfl

theorem sqrt_card_colours {d M : ℕ} :
    Real.sqrt (Fintype.card (Fin d → Fin M) : ℝ) = (M : ℝ) ^ ((d : ℝ) / 2) := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow,
    Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg M)]
  congr 1
  ring

theorem lattice_local_eLpNorm_sum_le {d : ℕ} {r₀ : ℝ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hfr : HasFiniteRange r₀ μ) (hr₀ : 0 ≤ r₀)
    {r ρ p : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) (hp : 2 ≤ p) (M : ℕ) (hM : 2 * ρ + r₀ < M * r)
    (f : (Fin d → ℤ) → FieldPair d → ℂ)
    (hloc : ∀ z, StronglyMeasurable[localSigma
      {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) < ρ}] (f z))
    (hLp : ∀ z, MemLp (f z) (ENNReal.ofReal p) μ) (hmean : ∀ z, ∫ ω, f z ω ∂μ = 0)
    (Λ : Finset (Fin d → ℤ)) :
    (eLpNorm (∑ z ∈ Λ, f z) (ENNReal.ofReal p) μ).toReal ≤
      2 * K1.lpSqConst p * (M : ℝ) ^ ((d : ℝ) / 2) *
        Real.sqrt (∑ z ∈ Λ, (eLpNorm (f z) (ENNReal.ofReal p) μ).toReal ^ 2) := by
  have hpos : 0 < (M : ℝ) * r := by linarith
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hpos
    · exact h
  have h := K1.complex_eLpNorm_sum_le_colored (μ := μ) (col M hM0) Λ hp
    (iIndepFun_colour hfr hr M hM0 (by linarith) f hloc)
    (fun z => measurable_of_local (hloc z)) hLp hmean
  rwa [sqrt_card_colours] at h
end EinsteinFull.Calculus.K2
