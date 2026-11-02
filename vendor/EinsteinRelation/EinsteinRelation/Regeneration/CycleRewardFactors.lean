import EinsteinRelation.Environment.Basic

/-!
# Locality of observables on a ball

Pointwise ingredients of the record factorization of the cycle reward (Step 2 of
Proposition 3.2, `paper/main.tex` lines 477–490). A function measurable for `localSigma U`
takes equal values at two coefficient pairs that agree on `U`. A point of the ball of radius
`R` around the origin, added to a point whose first coordinate exceeds `-R`, has first
coordinate at least `-2R`, so it lies in the future half-space `{x | -2R ≤ x i}`.
-/

open MeasureTheory

namespace EinsteinRelation

/-- The values of a coefficient pair on `U`: the matrix and scalar coefficients at each point
of `U`. -/
def localValues {d : ℕ} (U : Set (Vec d)) (ω : FieldPair d) : U → Mat d × ℝ :=
  fun x => (ω.1 x, ω.2 x)

/-- Every set of `localSigma U` is determined by the values of the coefficient pair on `U`. -/
theorem localSigma_le_comap_localValues {d : ℕ} (U : Set (Vec d)) :
    localSigma U ≤ MeasurableSpace.comap (localValues U) MeasurableSpace.pi := by
  have hV : Measurable[MeasurableSpace.comap (localValues U) MeasurableSpace.pi,
      MeasurableSpace.pi] (localValues U) :=
    measurable_iff_comap_le.2 le_rfl
  unfold localSigma
  refine iSup_le fun x => ?_
  exact measurable_iff_comap_le.1 ((measurable_pi_apply x).comp hV)

/-- A function measurable for `localSigma U` takes equal values at two coefficient pairs that
agree on `U`. -/
theorem eq_of_measurable_localSigma {d : ℕ} {U : Set (Vec d)} {G : FieldPair d → ℝ}
    (hG : Measurable[localSigma U] G) {ω₁ ω₂ : FieldPair d}
    (h : ∀ x ∈ U, ω₁.1 x = ω₂.1 x ∧ ω₁.2 x = ω₂.2 x) : G ω₁ = G ω₂ := by
  have hS : MeasurableSet[localSigma U] (G ⁻¹' {G ω₁}) :=
    hG (measurableSet_singleton (G ω₁))
  obtain ⟨T, -, hT⟩ :=
    MeasurableSpace.measurableSet_comap.1 (localSigma_le_comap_localValues U _ hS)
  have hval : localValues U ω₁ = localValues U ω₂ := by
    funext x
    show (ω₁.1 x, ω₁.2 x) = (ω₂.1 x, ω₂.2 x)
    exact Prod.ext (h x x.2).1 (h x x.2).2
  have hT₁ : localValues U ω₁ ∈ T := by
    have hmem : ω₁ ∈ localValues U ⁻¹' T := by
      rw [hT]
      exact Set.mem_singleton (G ω₁)
    exact hmem
  have hT₂ : localValues U ω₂ ∈ T := by
    rw [← hval]
    exact hT₁
  have hmem₂ : ω₂ ∈ G ⁻¹' {G ω₁} := by
    rw [← hT]
    exact hT₂
  have hmem₃ : G ω₂ ∈ ({G ω₁} : Set ℝ) := hmem₂
  exact (Set.mem_singleton_iff.1 hmem₃).symm

/-- Each coordinate of a vector is bounded in absolute value by its Euclidean norm. -/
theorem abs_coord_le_euclideanNorm {d : ℕ} (x : Vec d) (i : Fin d) :
    |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg (x j))
    (Finset.mem_univ i)

/-- A point `x` of the open ball of radius `R` around the origin, added to a point `y` with
`-R < y i`, has coordinate `i` at least `-2R`. -/
theorem neg_two_mul_le_add_coord_of_norm_lt {d : ℕ} (i : Fin d) {R : ℝ} (x y : Vec d)
    (hx : euclideanNorm x < R) (hy : -R < y i) : -2 * R ≤ (y + x) i := by
  have hxR : |x i| < R := lt_of_le_of_lt (abs_coord_le_euclideanNorm x i) hx
  have hxi : -R < x i := (abs_lt.1 hxR).1
  rw [Pi.add_apply]
  linarith

end EinsteinRelation
