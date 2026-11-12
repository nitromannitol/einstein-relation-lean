import EinsteinRelation.Correctors.NormedIntegralMoment

/-! # Error of local corrector averages

Source: `paper/main.tex:953–963`. For a scalar weight of integral one, the
weighted average of `f` differs from the common conditional mean `c` only
through the centered fluctuations, which carry a uniform moment bound. The
norm is that of the supplied value space; Euclidean and Frobenius norms are
obtained by using Euclidean value spaces.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- A scalar weight of integral one averages a random field against a common
conditional mean `c`; the resulting average error has moment norm at most
`C ∫ |w|`. Source: `paper/main.tex:953–963`, applied to each component of
`∇ζ_R`. -/
theorem local_average_error_bound {Ω X E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X) [SigmaFinite ν]
    {p C : ℝ} (hp : 1 ≤ p) (hC : 0 ≤ C)
    (w : X → ℝ) (hwm : Measurable w) (hwi : Integrable w ν)
    (hw : (∫ x, w x ∂ν) = 1) (f : X × Ω → E) (hf : Measurable f)
    (c : Ω → E) (hc : Measurable c)
    (hfluct : ∀ x, MemLp (fun ω => f (x, ω) - c ω) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => f (x, ω) - c ω) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal C) :
    (∀ᵐ ω ∂Q, Integrable (fun x => w x • f (x, ω)) ν) ∧
      MemLp (fun ω => (∫ x, w x • f (x, ω) ∂ν) - c ω) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => (∫ x, w x • f (x, ω) ∂ν) - c ω) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (C * ∫ x, |w x| ∂ν) := by
  have hHi : Integrable (fun x => |w x| * C) ν := hwi.abs.mul_const C
  have hgi : Measurable (fun z : X × Ω => w z.1 • (f z - c z.2)) :=
    (hwm.comp measurable_fst).smul (hf.sub (hc.comp measurable_snd))
  have hgmem : ∀ x, MemLp (fun ω => w x • (f (x, ω) - c ω)) (ENNReal.ofReal p) Q ∧
      eLpNorm (fun ω => w x • (f (x, ω) - c ω)) (ENNReal.ofReal p) Q ≤
        ENNReal.ofReal (|w x| * C) := by
    intro x
    refine ⟨(hfluct x).1.const_smul (w x), ?_⟩
    calc
      eLpNorm (fun ω => w x • (f (x, ω) - c ω)) (ENNReal.ofReal p) Q =
          ‖w x‖ₑ * eLpNorm (fun ω => f (x, ω) - c ω) (ENNReal.ofReal p) Q :=
        eLpNorm_const_smul (w x) (fun ω => f (x, ω) - c ω) _ Q
      _ ≤ ‖w x‖ₑ * ENNReal.ofReal C := mul_le_mul_right (hfluct x).2 _
      _ = ENNReal.ofReal (|w x| * C) := by
        rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, ENNReal.ofReal_mul (abs_nonneg _)]
  obtain ⟨hsec, hmem, hbound⟩ := normed_integral_moment_le Q ν hp
    (fun x => |w x| * C) (by simpa only [Real.norm_eq_abs] using hwm.norm.mul_const C)
    (fun x => mul_nonneg (abs_nonneg _) hC) hHi
    (fun z => w z.1 • (f z - c z.2)) hgi hgmem
  have hsec' : ∀ᵐ ω ∂Q, Integrable (fun x => w x • f (x, ω)) ν := by
    filter_upwards [hsec] with ω hω
    have heq : (fun x => w x • f (x, ω)) =
        (fun x => w x • (f (x, ω) - c ω)) + (fun x => w x • c ω) := by
      ext x
      simp only [Pi.add_apply, smul_sub]
      abel
    rw [heq]
    exact hω.add (hwi.smul_const (c ω))
  have heq : (fun ω => (∫ x, w x • f (x, ω) ∂ν) - c ω) =ᵐ[Q]
      fun ω => ∫ x, w x • (f (x, ω) - c ω) ∂ν := by
    filter_upwards [hsec'] with ω hω
    simp_rw [smul_sub]
    rw [integral_sub hω (hwi.smul_const (c ω)), integral_smul_const, hw, one_smul]
  refine ⟨hsec', (memLp_congr_ae heq).mpr hmem, (eLpNorm_congr_ae heq).le.trans ?_⟩
  simpa only [integral_mul_const, mul_comm C] using hbound

end EinsteinRelation.Correctors
