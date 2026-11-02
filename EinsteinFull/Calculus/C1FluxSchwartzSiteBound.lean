import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Calculus.K5FixedAnnularReconstruction

open MeasureTheory EinsteinRelation

namespace EinsteinFull.Blueprint

/-- Recombine the eight reduced-law components while retaining their site weights. -/
theorem c1_actual_eight_blocks_site_bound
    {d : ℕ} {Λ r₀ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (q : ENNReal) (hq : 1 ≤ q) (c₀ c₁ : ℂ)
    (U : Bool → Bool → FieldPair d → ℂ)
    (B : Bool → FieldPair d → ℂ) (T : Bool → ℝ) (w : ℝ)
    (hU : ∀ b a, MemLp (U b a) q (reducedLaw Q))
    (hB : ∀ b, MemLp (B b) q (reducedLaw Q))
    (hUb : ∀ b a, (eLpNorm (U b a) q (reducedLaw Q)).toReal ≤ T b * w)
    (hBb : ∀ b, (eLpNorm (B b) q (reducedLaw Q)).toReal ≤ T b * w) :
    let f := c₀ • ((U true false - B true) + Complex.I • (U true true - B true)) -
      c₁ • ((U false false - B false) + Complex.I • (U false true - B false))
    MemLp f q (reducedLaw Q) ∧
      (eLpNorm f q (reducedLaw Q)).toReal ≤
        (4 * ‖c₀‖ * T true + 4 * ‖c₁‖ * T false) * w := by
  have branch (b : Bool) (c : ℂ) :
      MemLp (c • ((U b false - B b) + Complex.I • (U b true - B b))) q (reducedLaw Q) ∧
      (eLpNorm (c • ((U b false - B b) + Complex.I • (U b true - B b))) q (reducedLaw Q)).toReal ≤
        ‖c‖ * (4 * T b * w) := by
    have hd (a : Bool) : MemLp (U b a - B b) q (reducedLaw Q) ∧
        (eLpNorm (U b a - B b) q (reducedLaw Q)).toReal ≤ 2 * T b * w := by
      refine ⟨(hU b a).sub (hB b), ?_⟩
      calc
        _ ≤ (eLpNorm (U b a) q (reducedLaw Q)).toReal +
            (eLpNorm (B b) q (reducedLaw Q)).toReal :=
          Calculus.K5.toReal_eLpNorm_sub_le hq (hU b a) (hB b)
        _ ≤ T b * w + T b * w := add_le_add (hUb b a) (hBb b)
        _ = 2 * T b * w := by ring
    have hi := (hd true).1.const_smul Complex.I
    have hn : (eLpNorm (Complex.I • (U b true - B b)) q (reducedLaw Q)).toReal =
        (eLpNorm (U b true - B b) q (reducedLaw Q)).toReal := by
      rw [eLpNorm_const_smul, ← ofReal_norm, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (norm_nonneg Complex.I)]
      simp only [Complex.norm_I, one_mul]
    have hs := (hd false).1.add hi
    have ht := eLpNorm_add_le (μ := reducedLaw Q)
      (f := U b false - B b) (g := Complex.I • (U b true - B b)) hq
    have hr := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨(hd false).1.eLpNorm_ne_top, hi.eLpNorm_ne_top⟩) ht
    rw [ENNReal.toReal_add (hd false).1.eLpNorm_ne_top hi.eLpNorm_ne_top, hn] at hr
    have hb : (eLpNorm ((U b false - B b) + Complex.I • (U b true - B b)) q
        (reducedLaw Q)).toReal ≤ 4 * T b * w := by
      calc
        _ ≤ _ := hr
        _ ≤ 2 * T b * w + 2 * T b * w := add_le_add (hd false).2 (hd true).2
        _ = _ := by ring
    refine ⟨hs.const_smul c, ?_⟩
    rw [eLpNorm_const_smul, ← ofReal_norm, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (norm_nonneg c)]
    exact mul_le_mul_of_nonneg_left hb (norm_nonneg c)
  have h₀ := branch true c₀
  have h₁ := branch false c₁
  dsimp only
  refine ⟨h₀.1.sub h₁.1, ?_⟩
  calc
    _ ≤ _ := Calculus.K5.toReal_eLpNorm_sub_le hq h₀.1 h₁.1
    _ ≤ ‖c₀‖ * (4 * T true * w) + ‖c₁‖ * (4 * T false * w) :=
      add_le_add h₀.2 h₁.2
    _ = _ := by ring

end EinsteinFull.Blueprint
