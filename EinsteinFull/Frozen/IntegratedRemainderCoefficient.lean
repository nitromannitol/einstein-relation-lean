import EinsteinFull.Frozen.KernelProfileRemainder
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory

namespace EinsteinFull

/-- r_j is the time integral of the real force derivative of the actual
profile-subtracted correlation, divided by j!, on its genuine integrability
and holomorphic, real-on-real force domain, exactly in the source range 0,...,d. -/
noncomputable def integratedRemainderCoefficient (d : ℕ) (u₀ u₂ γ : ℝ)
    (K : ℝ → ℂ → ℂ)
    (_hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t))
    (_hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
    (j : Fin (d + 1))
    (_hI : IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
        (j.val.factorial : ℝ)) (Set.Ici 0)) : ℝ :=
  ∫ t in Set.Ici (0 : ℝ),
    iteratedDeriv j.val (fun lam : ℝ =>
      (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 / (j.val.factorial : ℝ)

end EinsteinFull
