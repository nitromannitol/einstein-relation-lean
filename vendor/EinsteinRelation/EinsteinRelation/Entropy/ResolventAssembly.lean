import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Assembly of the resolvent bound (Lemma 4.3)

Source: `paper/main.tex`, Lemma `entropy.resolvent` and its proof. For a nonnegative resolvent
density `ρ = ρ_s`, a function `f`, a source `h`, a vector field `G`, and the gradient `Dρ`, the
argument combines four inputs:

* the weak resolvent identity `s E[ρ f] - s E[f] = E[ρ L f]`;
* the weak equation tested against `ρ`, namely `E[ρ L f] = E[ρ h] - E[Dρ · G]`;
* the occupation bound `E[ρ |f|] ≤ C₁ ‖f‖` together with `E[|f|] ≤ ‖f‖`, where `‖f‖` is the
  `L^{2p}` norm;
* the divergence bound `|E[Dρ · G]| ≤ C₂ λ ‖G‖`.

The declarations below carry out only the algebra that combines these inputs. The occupation
and divergence bounds enter as hypotheses; their proofs belong to the estimates that precede
the lemma.
-/

open MeasureTheory

namespace EinsteinRelation

/-- Absolute value of a weighted expectation is at most the weighted expectation of the absolute
value, for a nonnegative weight. Only the sign of `ρ` is used, and no integrability is needed. -/
theorem abs_integral_weighted_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (rho f : Ω → ℝ) (hrho : ∀ᵐ ω ∂P, 0 ≤ rho ω) :
    |∫ ω, rho ω * f ω ∂P| ≤ ∫ ω, rho ω * |f ω| ∂P := by
  refine abs_integral_le_integral_abs.trans (le_of_eq ?_)
  refine integral_congr_ae ?_
  filter_upwards [hrho] with ω hω
  simp only [abs_mul, abs_of_nonneg hω]

/-- Real-number form of Lemma 4.3. The variables are `a = E[ρ f]`, `b = E[f]`, `c = E[ρ h]`,
`e = E[Dρ · G]`, `l = E[ρ L f]`, `occ = E[ρ |f|]`, `occAbs = E[|f|]`, `nf = ‖f‖_{L^{2p}}`,
and `nG = ‖G‖_{L^{2p}}`. The resolvent identity and the tested weak equation give the identity
`s a - s b = c - e`, and the occupation and divergence bounds give the estimate on `|c|`. -/
theorem resolvent_assembly_real {a b c e l occ occAbs : ℝ} (nf nG C1 C2 lam s : ℝ)
    (hs : 0 ≤ s) (hres : s * a - s * b = l) (htest : l = c - e)
    (ha : |a| ≤ occ) (hocc : occ ≤ C1 * nf)
    (hb : |b| ≤ occAbs) (hL1 : occAbs ≤ nf)
    (hdiv : |e| ≤ C2 * lam * nG) :
    s * a - s * b = c - e ∧ |c| ≤ (C1 + 1) * s * nf + C2 * lam * nG := by
  refine ⟨hres.trans htest, ?_⟩
  have hsa : |s * a| ≤ s * (C1 * nf) := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (ha.trans hocc) hs
  have hsb : |s * b| ≤ s * nf := by
    rw [abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left (hb.trans hL1) hs
  obtain ⟨hsa1, hsa2⟩ := abs_le.mp hsa
  obtain ⟨hsb1, hsb2⟩ := abs_le.mp hsb
  obtain ⟨he1, he2⟩ := abs_le.mp hdiv
  rw [abs_le]
  constructor <;> linarith

/-- Integral form of Lemma 4.3 on a probability space `(Ω, P)`. Here `rho` is the resolvent
density (nonnegative `P`-almost everywhere), `Drho` its gradient, `G` the vector field of the
divergence term, and `Lf` the function `L f`. The weak equation tested against `rho` is stated
at the integrand level, and the integrability of `ρ h` and of the pairing `Dρ · G` is what
splits its integral. The bounds on `E[ρ f]` and `E[f]` need no integrability, since they hold for
every integrand.

The conclusion is the resolvent identity `s E[ρ f] - s E[f] = E[ρ h] - E[Dρ · G]` together
with `|E[ρ h]| ≤ (C₁ + 1) s ‖f‖ + C₂ λ ‖G‖`. -/
theorem resolvent_assembly_integral {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {d : ℕ} (rho f h Lf : Ω → ℝ)
    (Drho G : Ω → EuclideanSpace ℝ (Fin d))
    (nf nG C1 C2 lam s : ℝ) (hs : 0 ≤ s) (hrho : ∀ᵐ ω ∂P, 0 ≤ rho ω)
    (hh : Integrable (fun ω => rho ω * h ω) P)
    (hDG : Integrable (fun ω => inner ℝ (Drho ω) (G ω)) P)
    (hres : s * (∫ ω, rho ω * f ω ∂P) - s * (∫ ω, f ω ∂P) = ∫ ω, rho ω * Lf ω ∂P)
    (htest : ∫ ω, rho ω * Lf ω ∂P = ∫ ω, (rho ω * h ω - inner ℝ (Drho ω) (G ω)) ∂P)
    (hocc : ∫ ω, rho ω * |f ω| ∂P ≤ C1 * nf)
    (hL1 : ∫ ω, |f ω| ∂P ≤ nf)
    (hdiv : |∫ ω, inner ℝ (Drho ω) (G ω) ∂P| ≤ C2 * lam * nG) :
    s * (∫ ω, rho ω * f ω ∂P) - s * (∫ ω, f ω ∂P) =
        (∫ ω, rho ω * h ω ∂P) - (∫ ω, inner ℝ (Drho ω) (G ω) ∂P) ∧
      |∫ ω, rho ω * h ω ∂P| ≤ (C1 + 1) * s * nf + C2 * lam * nG := by
  have hsplit : ∫ ω, (rho ω * h ω - inner ℝ (Drho ω) (G ω)) ∂P =
      (∫ ω, rho ω * h ω ∂P) - (∫ ω, inner ℝ (Drho ω) (G ω) ∂P) :=
    integral_sub hh hDG
  refine ⟨hres.trans (htest.trans hsplit), ?_⟩
  exact (resolvent_assembly_real nf nG C1 C2 lam s hs hres (htest.trans hsplit)
    (abs_integral_weighted_le P rho f hrho) hocc abs_integral_le_integral_abs hL1 hdiv).2

end EinsteinRelation
