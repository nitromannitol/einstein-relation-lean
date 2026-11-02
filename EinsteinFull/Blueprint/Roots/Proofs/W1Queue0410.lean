import EinsteinFull.Blueprint.Roots.node_l_u3A_finite_u2D_xi
import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_split_u2D_tail
import EinsteinFull.Blueprint.G3.node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integral

namespace EinsteinFull.Blueprint

/-- Combine the commutator tail and scalar integral estimates with common structural constants. -/
theorem node_l_u3A_finite_u2D_xi_of_deps
    (htail : node_l_u3A_finite_u2D_xi_u23_split_u2D_tailStmt)
    (hscalar : node_l_u3A_finite_u2D_xi_u23_scalar_u2D_integralStmt) :
    node_l_u3A_finite_u2D_xiStmt := by
  intro d hd D
  obtain ⟨ε, L₀, ν, gain, t₁, C₁, _hε, _hL₀, _hν, _hνε, hgain,
    _hgainε, _hgainε₂, _hgainν, ht₁, hC₁, htail⟩ := htail d hd D
  obtain ⟨t₂, C₂, ht₂, hC₂, hscalar⟩ := hscalar d hd D
  refine ⟨gain, max t₁ t₂, fun k => max (C₁ k) (C₂ k), hgain,
    ht₁.trans (le_max_left _ _), fun k => (hC₁ k).trans_le (le_max_left _ _), ?_⟩
  intro Q hQ β Z hβ hZ P hP
  obtain ⟨G, J, H, X, _hG, _hJ, hcomm, htail⟩ := htail Q hQ β Z hβ hZ P hP
  refine ⟨H, X, hcomm, ?_⟩
  intro τ hτ s hs hpos
  have hτ₁ := (le_max_left t₁ t₂).trans hτ
  have hτ₂ := (le_max_right t₁ t₂).trans hτ
  constructor
  · intro i k dirs
    exact ((htail τ hτ₁).2 s hs hpos i k dirs).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left (C₁ k) (C₂ k))
          (Real.rpow_nonneg τ.coe_nonneg _)) (Real.rpow_nonneg hpos.le _))
  · intro i k hk dirs
    exact (hscalar Q hQ β hβ P hP τ hτ₂ s hs hpos i k hk dirs).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right (C₁ k) (C₂ k)) τ.coe_nonneg)
        (Real.rpow_nonneg hpos.le _))

end EinsteinFull.Blueprint
