import EinsteinRelation.Correctors.PairedParabolicEquation
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:808–816,822–840`. Compact spatial pairing
preserves continuity of an actual continuous positive-time representative. -/
theorem continuousOn_compact_test_pairing {d : ℕ}
    (u : ℝ × Vec d → ℝ)
    (hu : ContinuousOn u (Set.Ioi 0 ×ˢ Set.univ))
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ContinuousOn (fun t => ∫ x, u (t, x) * ψ x) (Set.Ioi 0) := by
  let f : ℝ → Vec d → ℝ := fun t x => u (t, x) * ψ x
  have hf_uncurry : ContinuousOn f.uncurry (Set.Ioi 0 ×ˢ Set.univ) := by
    have hψ_cont : ContinuousOn (fun (p : ℝ × Vec d) => ψ p.2) (Set.Ioi 0 ×ˢ Set.univ) :=
      (hψ.comp continuous_snd).continuousOn
    have : f.uncurry = fun (p : ℝ × Vec d) => u p * ψ p.2 := by
      ext p; rfl
    rw [this]
    exact hu.mul hψ_cont
  have hk : IsCompact (tsupport ψ) := hψc.isCompact
  have hfs : ∀ (p : ℝ) (x : Vec d), p ∈ Set.Ioi 0 → x ∉ tsupport ψ → f p x = 0 := by
    intro p x hp hx
    have hψx : ψ x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [f, hψx]
  exact continuousOn_integral_of_compact_support hk hf_uncurry hfs
end EinsteinRelation.Correctors
