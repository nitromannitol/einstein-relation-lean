import EinsteinFull.Frozen.IntegratedRemainderCoefficient
import EinsteinFull.Frozen.ProfileFinitePart

namespace EinsteinFull

/-- The prescribed ordinary coefficient k_j, including the parity-dependent
finite part in degree d. The index range is exactly 0,...,d. -/
noncomputable def integratedKernelCoefficient (d : ℕ) (u₀ u₂ γ : ℝ) (hγ : 0 < γ)
    (K : ℝ → ℂ → ℂ)
    (hK : ∀ t : ℝ, 0 ≤ t → Differentiable ℂ (K t))
    (hR : ∀ t : ℝ, 0 ≤ t → ∀ lam : ℝ, (K t (lam : ℂ)).im = 0)
    (hI : ∀ j : Fin (d + 1), MeasureTheory.IntegrableOn (fun t : ℝ =>
      iteratedDeriv j.val (fun lam : ℝ =>
        (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) 0 /
          (j.val.factorial : ℝ)) (Set.Ici 0))
    (j : Fin (d + 1)) : ℝ :=
  integratedRemainderCoefficient d u₀ u₂ γ K hK hR j (hI j) +
    if j.val < d then 2 * profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)
    else if Even d then 2 * profileFinitePart d u₀ u₂ γ hγ else 0

end EinsteinFull
