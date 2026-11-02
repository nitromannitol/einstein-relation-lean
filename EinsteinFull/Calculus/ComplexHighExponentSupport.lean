import EinsteinFull.Calculus.ComplexLpContinuitySupport

/-! The actual higher-Lp restriction of stationary L2 operators. -/
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The probability-law inclusion from higher Lp to L2 preserves the AE class. -/
def complexLpToL2 (hp2 : 2 ≤ p) : Lp ℂ p μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun f := ⟨f.1, Lp.antitone hp2 f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [Fact (1 ≤ p)] in
/-- The higher-Lp inclusion uses the identical representative. -/
theorem complexLpToL2_apply (hp2 : 2 ≤ p) (f : Lp ℂ p μ) :
    (complexLpToL2 μ hp2 f : α → ℂ) = f := rfl

omit [Fact (1 ≤ p)] in
/-- Inclusion in L2 is contractive under a probability law. -/
theorem norm_complexLpToL2_le (hp2 : 2 ≤ p) (f : Lp ℂ p μ) :
    ‖complexLpToL2 μ hp2 f‖ ≤ ‖f‖ := by
  have h := ENNReal.toReal_mono (Lp.memLp f).eLpNorm_ne_top
    (eLpNorm_le_eLpNorm_of_exponent_le (f := f) hp2)
  simpa only [Lp.norm_def, complexLpToL2_apply] using h

/-- The actual higher-Lp inclusion as a continuous complex linear map. -/
def complexLpToL2CLM (hp2 : 2 ≤ p) : Lp ℂ p μ →L[ℂ] Lp ℂ 2 μ :=
  (complexLpToL2 μ hp2).mkContinuous 1 (fun f => by
    simpa only [one_mul] using norm_complexLpToL2_le μ hp2 f)

omit [Fact (1 ≤ p)] in
/-- The inclusion is injective because it preserves the AE class. -/
theorem complexLpToL2_injective (hp2 : 2 ≤ p) :
    Function.Injective (complexLpToL2 μ hp2) := by
  intro f g h
  exact Subtype.ext (congrArg (fun f : Lp ℂ 2 μ => f.1) h)

/-- Restrict an actual L2 operator which preserves the genuine higher-Lp space.
No extension or off-domain choice is involved: the output AE class is unchanged. -/
def complexL2OperatorLpRestriction (hp2 : 2 ≤ p)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f : Lp ℂ p μ, MemLp (A (complexLpToL2 μ hp2 f)) p μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f : Lp ℂ p μ,
      eLpNorm (A (complexLpToL2 μ hp2 f)) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C) :
    Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  ({ toFun f := ⟨(A (complexLpToL2 μ hp2 f)).1, hA f⟩
     map_add' f g := by
       apply Subtype.ext
       exact congrArg (fun f : Lp ℂ 2 μ => f.1)
         (map_add A (complexLpToL2 μ hp2 f) (complexLpToL2 μ hp2 g))
     map_smul' c f := by
       apply Subtype.ext
       exact congrArg (fun f : Lp ℂ 2 μ => f.1)
         (map_smul A c (complexLpToL2 μ hp2 f)) } :
      Lp ℂ p μ →ₗ[ℂ] Lp ℂ p μ).mkContinuous C (fun f => by
        have hb := ENNReal.toReal_mono
          (ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top ENNReal.ofReal_ne_top) (hbound f)
        simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, Lp.norm_def, mul_comm] using! hb)

/-- Restriction commutes exactly with the literal inclusion in actual L2. -/
theorem complexL2OperatorLpRestriction_apply (hp2 : 2 ≤ p)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f : Lp ℂ p μ, MemLp (A (complexLpToL2 μ hp2 f)) p μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f : Lp ℂ p μ,
      eLpNorm (A (complexLpToL2 μ hp2 f)) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (f : Lp ℂ p μ) :
    complexLpToL2 μ hp2 (complexL2OperatorLpRestriction μ hp2 A hA hC hbound f) =
      A (complexLpToL2 μ hp2 f) := rfl

/-- The higher-Lp restriction retains the original bound with leading constant one. -/
theorem norm_complexL2OperatorLpRestriction_le (hp2 : 2 ≤ p)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f : Lp ℂ p μ, MemLp (A (complexLpToL2 μ hp2 f)) p μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f : Lp ℂ p μ,
      eLpNorm (A (complexLpToL2 μ hp2 f)) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C) :
    ‖complexL2OperatorLpRestriction μ hp2 A hA hC hbound‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro f
  have hb := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top ENNReal.ofReal_ne_top) (hbound f)
  simpa only [complexL2OperatorLpRestriction, LinearMap.mkContinuous_apply,
    Lp.norm_def, ENNReal.toReal_mul, ENNReal.toReal_ofReal hC, mul_comm] using! hb

/-- Exact agreement on the included AE classes uniquely characterizes restriction. -/
theorem complexL2OperatorLpRestriction_unique (hp2 : 2 ≤ p)
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hA : ∀ f : Lp ℂ p μ, MemLp (A (complexLpToL2 μ hp2 f)) p μ)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ f : Lp ℂ p μ,
      eLpNorm (A (complexLpToL2 μ hp2 f)) p μ ≤ eLpNorm f p μ * ENNReal.ofReal C)
    (B : Lp ℂ p μ →L[ℂ] Lp ℂ p μ)
    (hB : ∀ f, complexLpToL2 μ hp2 (B f) = A (complexLpToL2 μ hp2 f)) :
    complexL2OperatorLpRestriction μ hp2 A hA hC hbound = B := by
  apply ContinuousLinearMap.ext
  intro f
  apply complexLpToL2_injective μ hp2
  rw [complexL2OperatorLpRestriction_apply, hB]

/-- A genuine restriction family inherits the exact identity and composition laws. -/
theorem complexLp_restriction_semigroup_laws (hp2 : 2 ≤ p)
    (A : ℝ≥0 → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (B : ℝ≥0 → Lp ℂ p μ →L[ℂ] Lp ℂ p μ)
    (hB : ∀ t f, complexLpToL2 μ hp2 (B t f) = A t (complexLpToL2 μ hp2 f))
    (hzero : A 0 = ContinuousLinearMap.id ℂ _)
    (hadd : ∀ s t, A (s+t) = (A s).comp (A t)) :
    B 0 = ContinuousLinearMap.id ℂ _ ∧ ∀ s t, B (s+t) = (B s).comp (B t) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro f
    apply complexLpToL2_injective μ hp2
    rw [hB, hzero]
    rfl
  · intro s t
    apply ContinuousLinearMap.ext
    intro f
    apply complexLpToL2_injective μ hp2
    simp only [hB, hadd, ContinuousLinearMap.comp_apply]

section Physical
variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual forward evolution preserves every higher exponent, with the
full quadratic-force rate and no output-membership premise. -/
theorem IsComplexEnvironmentSemigroup.highLp_bound
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) {p : ℝ} (hp2 : 2 ≤ p)
    (f : Lp ℂ 2 (reducedLaw Q)) (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q))
    (t : ℝ≥0) :
    MemLp (P t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ))) := by
  have ha : 0 ≤ p / 2 - 1 := by linarith
  have he : 2 * (1 + (p / 2 - 1)) = p := by ring
  have hf' : MemLp f (ENNReal.ofReal (2 * (1 + (p / 2 - 1)))) (reducedLaw Q) := by
    simpa only [he] using hf
  exact ⟨by simpa only [he] using (hP.power_moment_growth ha f hf' t).1,
    by simpa only [he] using hP.eLpNorm_growth ha f hf' t⟩

/-- The actual bilinear transpose preserves every higher exponent, with its
own proved quadratic-force rate. -/
theorem IsComplexTransposeSemigroup.highLp_bound
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    {p : ℝ} (hp2 : 2 ≤ p) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) (t : ℝ≥0) :
    MemLp (T t f) (ENNReal.ofReal p) (reducedLaw Q) ∧
    eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p - 1)) ^ 2) * (t : ℝ))) := by
  have ha : 0 ≤ p / 2 - 1 := by linarith
  have he : 2 * (1 + (p / 2 - 1)) = p := by ring
  have he' : 1 + 2 * (p / 2 - 1) = p - 1 := by ring
  have hf' : MemLp f (ENNReal.ofReal (2 * (1 + (p / 2 - 1)))) (reducedLaw Q) := by
    simpa only [he] using hf
  exact ⟨by simpa only [he] using (hT.power_moment_growth hP ha f hf' t).1,
    by simpa only [he, he'] using hT.eLpNorm_growth hP ha f hf' t⟩

variable {p : ℝ} (hp2 : 2 ≤ p)

private theorem ofReal_two_le (hp2 : 2 ≤ p) : 2 ≤ ENNReal.ofReal p := by
  exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)



/-- The actual forward evolution restricted to the entire genuine higher-Lp space. -/
def IsComplexEnvironmentSemigroup.lpRestriction
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) →L[ℂ] Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  have hA (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :=
    hP.highLp_bound hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t
  exact complexL2OperatorLpRestriction (reducedLaw Q) (ofReal_two_le hp2) (P t)
    (fun f => (hA f).1) (Real.exp_pos _).le (fun f => (hA f).2)

/-- The actual transpose restricted to the entire genuine higher-Lp space. -/
def IsComplexTransposeSemigroup.lpRestriction
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) →L[ℂ] Lp ℂ (ENNReal.ofReal p) (reducedLaw Q) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  have hA (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :=
    hT.highLp_bound hP hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t
  exact complexL2OperatorLpRestriction (reducedLaw Q) (ofReal_two_le hp2) (T t)
    (fun f => (hA f).1) (Real.exp_pos _).le (fun f => (hA f).2)

/-- Restriction of the actual forward family agrees on every higher-Lp datum. -/
theorem IsComplexEnvironmentSemigroup.lpRestriction_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0)
    (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) (hP.lpRestriction hp2 t f) =
      P t (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f) := rfl

/-- Restriction of the actual transpose agrees on every higher-Lp datum. -/
theorem IsComplexTransposeSemigroup.lpRestriction_apply
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    (t : ℝ≥0) (f : Lp ℂ (ENNReal.ofReal p) (reducedLaw Q)) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) (hT.lpRestriction hp2 hP t f) =
      T t (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f) := rfl

/-- The actual higher-Lp forward operator retains the exact quadratic growth bound. -/
theorem IsComplexEnvironmentSemigroup.norm_lpRestriction_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    ‖hP.lpRestriction hp2 t‖ ≤ Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact norm_complexL2OperatorLpRestriction_le (reducedLaw Q) (ofReal_two_le hp2) (P t)
    (fun f => (hP.highLp_bound hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t).1) (Real.exp_pos _).le
    (fun f => (hP.highLp_bound hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t).2)

/-- The actual higher-Lp transpose retains its distinct quadratic growth bound. -/
theorem IsComplexTransposeSemigroup.norm_lpRestriction_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T)
    (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    ‖hT.lpRestriction hp2 hP t‖ ≤ Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
      (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (p - 1)) ^ 2) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact norm_complexL2OperatorLpRestriction_le (reducedLaw Q) (ofReal_two_le hp2) (T t)
    (fun f => (hT.highLp_bound hP hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t).1) (Real.exp_pos _).le
    (fun f => (hT.highLp_bound hP hp2 (complexLpToL2 (reducedLaw Q) (ofReal_two_le hp2) f)
      (Lp.memLp f) t).2)

/-- The higher-Lp forward restriction has the full identity and composition laws. -/
theorem IsComplexEnvironmentSemigroup.lpRestriction_laws
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    hP.lpRestriction hp2 0 = ContinuousLinearMap.id ℂ _ ∧
    ∀ s t, hP.lpRestriction hp2 (s+t) =
      (hP.lpRestriction hp2 s).comp (hP.lpRestriction hp2 t) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact complexLp_restriction_semigroup_laws (reducedLaw Q) (ofReal_two_le hp2) P
    (hP.lpRestriction hp2) (hP.lpRestriction_apply hp2) hP.1 hP.2.1

/-- The higher-Lp transpose restriction has the full identity and composition laws. -/
theorem IsComplexTransposeSemigroup.lpRestriction_laws
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (hT : IsComplexTransposeSemigroup Q P T) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
    hT.lpRestriction hp2 hP 0 = ContinuousLinearMap.id ℂ _ ∧
    ∀ s t, hT.lpRestriction hp2 hP (s+t) =
      (hT.lpRestriction hp2 hP s).comp (hT.lpRestriction hp2 hP t) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith))⟩
  exact complexLp_restriction_semigroup_laws (reducedLaw Q) (ofReal_two_le hp2) T
    (hT.lpRestriction hp2 hP) (hT.lpRestriction_apply hp2 hP) (hT.zero hP) (hT.add hP)

end Physical
end EinsteinFull
