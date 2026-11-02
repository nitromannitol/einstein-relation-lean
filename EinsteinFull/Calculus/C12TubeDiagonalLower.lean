import EinsteinFull.Calculus.C17TubeParabolicScaling
import EinsteinFull.Calculus.C9TubeWeightedZeroPast
import EinsteinFull.External.Source.GMPDirichletSpectralKernel

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open scoped Topology

noncomputable section
namespace EinsteinFull.Calculus

/-- A bounded nonnegative density has bounded mass on a finite-measure set. -/
theorem c12_bounded_density_mass {d : ℕ} (s : Set (Vec d))
    (hs : volume s ≠ ⊤) {B : ℝ} (ρ : Vec d → ℝ) (hρ : Measurable ρ)
    (hρbd : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ B) :
    IntegrableOn ρ s ∧ (∫ y in s, ρ y) ≤ B * (volume s).toReal := by
  have hi : IntegrableOn ρ s :=
    Measure.integrableOn_of_bounded hs hρ.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hρbd y).1] using (hρbd y).2)
  refine ⟨hi, ?_⟩
  calc
    (∫ y in s, ρ y) ≤ ∫ _ in s, B :=
      integral_mono hi (integrableOn_const hs) (fun y => (hρbd y).2)
    _ = B * (volume s).toReal := by simp [Measure.real_def, mul_comm]

/-- Integrability of a weighted row supplies integrability for the density measure. -/
theorem c12_integrable_row_withDensity {d : ℕ} (s : Set (Vec d))
    (ρ k : Vec d → ℝ) (hρ : Measurable ρ)
    (hρ0 : ∀ y, 0 ≤ ρ y)
    (hk : IntegrableOn (fun y => k y * ρ y) s) :
    Integrable k ((volume.restrict s).withDensity (fun y => ENNReal.ofReal (ρ y))) := by
  apply (integrable_withDensity_iff_integrable_smul' (hρ.ennreal_ofReal)
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).2
  change Integrable (fun y => k y * ρ y) (volume.restrict s) at hk
  simpa only [ENNReal.toReal_ofReal (hρ0 _), smul_eq_mul, mul_comm] using hk

/-- Cauchy–Schwarz for an integrable row on a finite measure. -/
theorem c12_integral_row_sq_le {d : ℕ} (μ : Measure (Vec d)) (k : Vec d → ℝ)
    (hk : Integrable k μ) (hk2 : Integrable (fun y => k y ^ 2) μ)
    (hone : Integrable (fun _ : Vec d => (1 : ℝ)) μ) :
    (∫ y, k y ∂μ)^2 ≤ (∫ y, (1 : ℝ) ∂μ) * (∫ y, k y^2 ∂μ) := by
  have hkLp : MemLp k 2 μ := (memLp_two_iff_integrable_sq hk.aestronglyMeasurable).2 hk2
  have hoLp : MemLp (fun _ : Vec d => (1 : ℝ)) 2 μ :=
    (memLp_two_iff_integrable_sq hone.aestronglyMeasurable).2 (by simpa using hone)
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hkLp) (by simpa using hoLp)
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow, Real.norm_eq_abs, sq_abs,
    abs_one, mul_one, one_pow] at hcs
  have hi := norm_integral_le_integral_norm (μ := μ) k
  simp only [Real.norm_eq_abs] at hi
  have hq : 0 ≤ ∫ y, k y^2 ∂μ := integral_nonneg (fun y => sq_nonneg (k y))
  have hm : 0 ≤ ∫ _ : Vec d, (1 : ℝ) ∂μ := integral_nonneg (fun _ => by norm_num)
  have hs1 := Real.sq_sqrt hq
  have hs2 := Real.sq_sqrt hm
  have hp : 0 ≤ Real.sqrt (∫ y, k y^2 ∂μ) * Real.sqrt (∫ _ : Vec d, (1 : ℝ) ∂μ) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have habs : 0 ≤ |∫ y, k y ∂μ| := abs_nonneg _
  have hp2 : (Real.sqrt (∫ y, k y^2 ∂μ) * Real.sqrt (∫ _ : Vec d, (1 : ℝ) ∂μ))^2 =
      (∫ y, k y^2 ∂μ) * (∫ _ : Vec d, (1 : ℝ) ∂μ) := by
    rw [mul_pow, hs1, hs2]
  nlinarith [sq_abs (∫ y, k y ∂μ)]

/-- A survival mass on the ball controls the diagonal row-square integral. -/
@[nolint unusedArguments]
theorem c12_diagonal_lower_from_row_mass {d : ℕ} {R B m L : ℝ}
    (hR : 0 < R) (hB : 0 < B) (hm : 0 ≤ m)
    (ρ k : Vec d → ℝ) (hρ : Measurable ρ)
    (hρbd : ∀ y, 0 ≤ ρ y ∧ ρ y ≤ B)
    (hk : IntegrableOn (fun y => k y * ρ y) (sourceBall 0 R))
    (hk2 : IntegrableOn (fun y => (k y)^2 * ρ y) (sourceBall 0 R))
    (hmass : m ≤ ∫ y in sourceBall 0 R, k y * ρ y)
    (hdiag : L = ∫ y in sourceBall 0 R, (k y)^2 * ρ y) :
    m^2 ≤ (B * (volume (sourceBall (0 : Vec d) R)).toReal) * L := by
  let s := sourceBall (0 : Vec d) R
  let μ := (volume.restrict s).withDensity (fun y => ENNReal.ofReal (ρ y))
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => (hρbd y).1
  have hb := c12_bounded_density_mass s (c9_sourceBall_measure_ne_top 0 R) ρ hρ hρbd
  have hki : Integrable k μ := c12_integrable_row_withDensity s ρ k hρ hρ0 hk
  have hk2i : Integrable (fun y => k y ^ 2) μ :=
    c12_integrable_row_withDensity s ρ (fun y => k y ^ 2) hρ hρ0 hk2
  have h1i : Integrable (fun _ : Vec d => (1 : ℝ)) μ := by
    apply (integrable_withDensity_iff_integrable_smul' hρ.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).2
    have hbint : Integrable ρ (volume.restrict s) := hb.1
    simpa [hρ0] using hbint
  have hconvert (f : Vec d → ℝ) : (∫ y, f y ∂μ) = ∫ y in s, f y * ρ y := by
    rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simp [hρ0, mul_comm]
  have hc := c12_integral_row_sq_le μ k hki hk2i h1i
  rw [hconvert k, hconvert (fun _ => 1), hconvert (fun y => k y ^ 2)] at hc
  simp only [one_mul] at hc
  have hL : 0 ≤ L := by
    rw [hdiag]
    exact integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hρ0 y))
  have hmass2 : m^2 ≤ (∫ y in s, k y * ρ y)^2 := by
    exact (sq_le_sq₀ hm (le_trans hm hmass)).2 hmass
  calc
    m^2 ≤ (∫ y in s, k y * ρ y)^2 := hmass2
    _ ≤ (∫ y in s, ρ y) * L := by simpa [hdiag] using hc
    _ ≤ (B * (volume s).toReal) * L := mul_le_mul_of_nonneg_right hb.2 hL

/-- Rearrangement of a squared row-mass bound when its denominator is positive. -/
theorem c12_diagonal_lower_div {m D L : ℝ} (hD : 0 < D)
    (h : m ^ 2 ≤ D * L) : m ^ 2 / D ≤ L := by
  exact (div_le_iff₀ hD).2 (by simpa [mul_comm] using h)

/-- Conditional native diagonal lower bound in the Lebesgue-density convention. -/
theorem c12_spectral_diagonal_lower_from_survival {d : ℕ} {κ R t m : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) (hm : 0 ≤ m)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (_hK : IsSpectralDirichletFundamentalSolution ρ α R K G) (x : Vec d)
    (hk : IntegrableOn (fun y => (K t x y / ρ y) * ρ y) (sourceBall 0 R))
    (hk2 : IntegrableOn (fun y => (K t x y / ρ y)^2 * ρ y) (sourceBall 0 R))
    (hmass : m ≤ ∫ y in sourceBall 0 R, (K t x y / ρ y) * ρ y)
    (hdiag : K (2*t) x x / ρ x =
      ∫ y in sourceBall 0 R, (K t x y / ρ y)^2 * ρ y)
    (hvol : 0 < κ⁻¹ * (volume (sourceBall (0 : Vec d) R)).toReal) :
    m^2 / (κ⁻¹ * (volume (sourceBall (0 : Vec d) R)).toReal) ≤
      K (2*t) x x / ρ x := by
  apply c12_diagonal_lower_div hvol
  exact c12_diagonal_lower_from_row_mass hR (inv_pos.mpr hκ) hm ρ
    (fun y => K t x y / ρ y) hell.1
    (fun y => ⟨le_trans hκ.le (hell.2.2 y).1, (hell.2.2 y).2.1⟩)
    hk hk2 hmass hdiag

end EinsteinFull.Calculus
