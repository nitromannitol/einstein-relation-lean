import EinsteinRelation.External.AKMCorrectorOscillation

/-!
# Null-set invariance and linearity of the source heat formula

Source: `paper/main.tex:722,740-756`. The spatial integral is evaluated
before the independent time cutoffs. Neither operation uses a stochastic
estimate or a flux-corrector identification assumption.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning External.AKM

/-- The literal heat density depends linearly on its centered-flux input. -/
theorem akmHeatGradientDensity_const_smul {d : ℕ} (g : Vec d → Vec d)
    (c t : ℝ) (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity (fun y => c • g y) t j k l x y =
      c * akmHeatGradientDensity g t j k l x y := by
  unfold akmHeatGradientDensity
  split
  · simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · exact (mul_zero c).symm

/-- Null-set changes of the input do not change a spatial heat integral. -/
theorem akmHeatGradientSpaceIntegral_congr_ae {d : ℕ} {g h : Vec d → Vec d}
    (hgh : g =ᵐ[volume] h) (t : ℝ) (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral g t j k l x =
      akmHeatGradientSpaceIntegral h t j k l x := by
  apply integral_congr_ae
  filter_upwards [hgh] with y hy
  simp only [akmHeatGradientDensity, hy]

/-- Null-set changes of the spatial input preserve both independent cutoffs. -/
theorem iteratedAKMHeatGradientTruncation_congr_ae {d : ℕ}
    {g h : Vec d → Vec d} (hgh : g =ᵐ[volume] h)
    (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n j k l x =
      iteratedAKMHeatGradientTruncation h m n j k l x := by
  unfold iteratedAKMHeatGradientTruncation
  congr 1
  funext t
  exact akmHeatGradientSpaceIntegral_congr_ae hgh t j k l x

/-- Linearity holds even when the totalized integral vanishes. -/
theorem akmHeatGradientSpaceIntegral_const_smul {d : ℕ} (g : Vec d → Vec d)
    (c t : ℝ) (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral (fun y => c • g y) t j k l x =
      c * akmHeatGradientSpaceIntegral g t j k l x := by
  simp only [akmHeatGradientSpaceIntegral, akmHeatGradientDensity_const_smul,
    integral_const_mul]

/-- Linearity retains the literal source order of integration. -/
theorem iteratedAKMHeatGradientTruncation_const_smul {d : ℕ}
    (g : Vec d → Vec d) (c : ℝ) (m n : ℕ) (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation (fun y => c • g y) m n j k l x =
      c * iteratedAKMHeatGradientTruncation g m n j k l x := by
  simp only [iteratedAKMHeatGradientTruncation, akmHeatGradientSpaceIntegral_const_smul,
    integral_const_mul]

/-- The source's complete local L² selection, including integrability,
is unchanged by spatial null-set changes of its centered-flux input. -/
theorem isHeatSelectedFluxGradient_congr_source_ae {d : ℕ}
    {g h : Vec d → Vec d} (hgh : g =ᵐ[volume] h)
    {G : Fin d → Fin d → Vec d → Vec d}
    (hg : IsHeatSelectedFluxGradient g G) : IsHeatSelectedFluxGradient h G := by
  intro j k l R
  obtain ⟨hi, hT, hG, hlim⟩ := hg j k l R
  have hspace := akmHeatGradientSpaceIntegral_congr_ae hgh
  have htrunc := iteratedAKMHeatGradientTruncation_congr_ae hgh
  refine ⟨?_, ?_, hG, ?_⟩
  · intro m n
    filter_upwards [hi m n] with x hx
    constructor
    · filter_upwards [hx.1] with t ht
      apply ht.congr
      filter_upwards [hgh] with y hy
      simp only [akmHeatGradientDensity, hy]
    · simpa only [← hspace] using hx.2
  · intro m n
    simpa only [← htrunc] using hT m n
  · simpa only [← htrunc] using hlim

end EinsteinRelation.Correctors
