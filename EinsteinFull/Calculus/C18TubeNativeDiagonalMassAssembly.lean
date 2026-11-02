import EinsteinFull.Calculus.C12TubeNativeDiagonalLower
import EinsteinFull.Calculus.C12TubeNativeLowerChaining
import EinsteinFull.Calculus.C17TubeMomentConcentration
import EinsteinFull.Calculus.C12TubeGaussianAssembly

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat

noncomputable section
namespace EinsteinFull.Calculus

/-- A nonnegative lower bound on the mass of a square-integrable row gives a
lower bound on its squared mass. -/
theorem c18_row_mass_square_lower {d : ℕ}
    (mu : Measure (Vec d)) [IsFiniteMeasure mu] (q : Vec d → ℝ)
    (hq : MemLp q 2 mu) (m : ℝ) (hm : 0 ≤ m)
    (hmass : m ≤ ∫ y, q y ∂mu) :
    m^2 ≤ (mu Set.univ).toReal * (∫ y, (q y)^2 ∂mu) := by
  have h := c12_integral_row_sq_le mu q (hq.integrable (by norm_num))
    hq.integrable_sq (integrable_const 1)
  have hm2 : m^2 ≤ (∫ y, q y ∂mu)^2 :=
    (sq_le_sq₀ hm (hm.trans hmass)).2 hmass
  refine hm2.trans ?_
  simpa only [integral_const, measureReal_def, smul_eq_mul, mul_one] using h

/-- A local weighted row mass and a squared-row Chapman–Kolmogorov lower
bound give the diagonal estimate for the actual Lebesgue-density kernel. -/
theorem c18_kernel_diagonal_from_local_row_mass {d : ℕ}
    {κ r t m : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hm : 0 ≤ m)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (x : Vec d)
    (hrow : IntegrableOn (fun y => (K t x y / ρ y) * ρ y) (sourceBall x r))
    (hsquare : IntegrableOn (fun y => (K t x y / ρ y)^2 * ρ y) (sourceBall x r))
    (hmass : m ≤ ∫ y in sourceBall x r, (K t x y / ρ y) * ρ y)
    (hck : (∫ y in sourceBall x r, (K t x y / ρ y)^2 * ρ y) ≤
      K (2*t) x x / ρ x) :
    m^2 / (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
      K (2*t) x x / ρ x := by
  let B := sourceBall x r
  let μ := (volume.restrict B).withDensity (fun y => ENNReal.ofReal (ρ y))
  let q : Vec d → ℝ := fun y => K t x y / ρ y
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hκ.le.trans (hell.2.2 y).1
  have hvol := c12_sourceBall_volume x hr
  have hb := c12_bounded_density_mass B hvol.2.1 ρ hell.1
    (fun y => ⟨hρ0 y, (hell.2.2 y).2.1⟩)
  have hq : Integrable q μ := c12_integrable_row_withDensity B ρ q hell.1 hρ0 hrow
  have hq2 : Integrable (fun y => q y ^ 2) μ :=
    c12_integrable_row_withDensity B ρ (fun y => q y ^ 2) hell.1 hρ0 hsquare
  have h1 : Integrable (fun _ : Vec d => (1 : ℝ)) μ := by
    apply (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).2
    have hbint : Integrable ρ (volume.restrict B) := hb.1
    simpa [hρ0] using hbint
  have hconvert (f : Vec d → ℝ) : (∫ y, f y ∂μ) = ∫ y in B, f y * ρ y := by
    rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simp [hρ0, mul_comm]
  have hcs := c12_integral_row_sq_le μ q hq hq2 h1
  rw [hconvert q, hconvert (fun _ => 1), hconvert (fun y => q y ^ 2)] at hcs
  simp only [one_mul] at hcs
  have hsq : 0 ≤ ∫ y in B, q y ^ 2 * ρ y :=
    integral_nonneg (fun y => mul_nonneg (sq_nonneg _) (hρ0 y))
  have hm2 : m^2 ≤ (∫ y in B, q y * ρ y)^2 :=
    (sq_le_sq₀ hm (hm.trans hmass)).2 hmass
  have hD : 0 < κ⁻¹ * (volume B).toReal := mul_pos (inv_pos.mpr hκ) hvol.2.2.1
  have hbound : m^2 ≤ (κ⁻¹ * (volume B).toReal) * (K (2*t) x x / ρ x) := by
    calc
      m^2 ≤ (∫ y in B, q y * ρ y)^2 := hm2
      _ ≤ (∫ y in B, ρ y) * (∫ y in B, q y^2 * ρ y) := hcs
      _ ≤ (κ⁻¹ * (volume B).toReal) * (∫ y in B, q y^2 * ρ y) :=
        mul_le_mul_of_nonneg_right hb.2 hsq
      _ ≤ (κ⁻¹ * (volume B).toReal) * (K (2*t) x x / ρ x) :=
        mul_le_mul_of_nonneg_left hck hD.le
  have hresult := c12_diagonal_lower_div hD hbound
  rw [hvol.2.2.2] at hresult
  exact hresult

/-- The spectral construction supplies the local row integrability and the
squared-row Chapman–Kolmogorov bound on any interior ball. -/
theorem c18_native_spectral_local_row_inputs {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (r : ℝ) (hr : 0 < r) (hinside : sourceBall x r ⊆ sourceBall 0 R) :
    IntegrableOn (fun y => (K t x y / ρ y) * ρ y) (sourceBall x r) ∧
    IntegrableOn (fun y => (K t x y / ρ y)^2 * ρ y) (sourceBall x r) ∧
    (∫ y in sourceBall x r, (K t x y / ρ y)^2 * ρ y) ≤ K (2*t) x x / ρ x := by
  obtain ⟨s, hs⟩ := hK.2
  let q : Vec d → ℝ := fun y => ∑' i, Real.exp (-s.eigenvalue i*t) *
    s.eigenfunction i x * s.eigenfunction i y
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hκ.le.trans (hell.2.2 y).1
  have hq : MemLp q 2 (dirichletVolume ρ R) :=
    spectral_heat_row_memLp hd hκ hell hR s t ht x hx
  have hweight (f : Vec d → ℝ) (hf : Integrable f (dirichletVolume ρ R)) :
      IntegrableOn (fun y => f y * ρ y) (sourceBall 0 R) := by
    unfold dirichletVolume at hf
    have hi := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
      (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).1 hf
    change Integrable (fun y => f y * ρ y) (volume.restrict (sourceBall 0 R))
    simpa [hρ0, smul_eq_mul, mul_comm] using hi
  have hrow := hweight q (hq.integrable (by norm_num))
  have hsq := hweight (fun y => q y ^ 2) hq.integrable_sq
  have heq : ∀ y ∈ sourceBall x r, K t x y / ρ y = q y := by
    intro y hy
    have hρ : ρ y ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 y).1)
    rw [(hs t ht x hx y (hinside hy)).2, mul_div_cancel_left₀ _ hρ]
  have hae : ∀ᵐ y ∂volume.restrict (sourceBall x r), K t x y / ρ y = q y := by
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume x hr).1] with y hy
    exact heq y hy
  have hconv : (∫ y in sourceBall x r, (K t x y / ρ y)^2 * ρ y) =
      ∫ y in sourceBall x r, q y^2 * ρ y := by
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    rw [hy]
  have hdiag : K (2*t) x x / ρ x = ∫ y in sourceBall 0 R, q y^2 * ρ y := by
    have hc : (∫ y, q y ^ 2 ∂dirichletVolume ρ R) =
        ∫ y in sourceBall 0 R, q y ^ 2 * ρ y := by
      unfold dirichletVolume
      rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
        (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
      simp [hρ0, mul_comm]
    rw [← hc, spectral_heat_row_integral_sq hd hκ hell hR s t ht x hx]
    have hre := (hs (2*t) (by positivity) x hx x hx).2
    have hρ : ρ x ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 x).1)
    rw [hre, mul_div_cancel_left₀ _ hρ]
    apply tsum_congr
    intro i
    have he : -(s.eigenvalue i) * (2*t) = -2*s.eigenvalue i*t := by ring
    rw [he]
    ring
  refine ⟨?_, ?_, ?_⟩
  · apply (hrow.mono_set hinside).congr_fun_ae
    filter_upwards [hae] with y hy
    rw [hy]
  · apply (hsq.mono_set hinside).congr_fun_ae
    filter_upwards [hae] with y hy
    rw [hy]
  · rw [hconv, hdiag]
    exact setIntegral_mono_set hsq (ae_of_all _ fun y => mul_nonneg (sq_nonneg _) (hρ0 y))
      (ae_of_all _ fun _ hy => hinside hy)

/-- For an interior ball, only the local survival mass remains to be supplied:
the spectral construction provides the other diagonal inputs. -/
theorem c18_native_spectral_local_diagonal_from_survival {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (r : ℝ) (hr : 0 < r) (hinside : sourceBall x r ⊆ sourceBall 0 R)
    (m : ℝ) (hm : 0 ≤ m) (hmass : m ≤ ∫ y in sourceBall x r, K t x y) :
    m^2 / (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
      K (2*t) x x / ρ x := by
  obtain ⟨hrow, hsq, hck⟩ :=
    c18_native_spectral_local_row_inputs hd hκ hR ρ α hell K G hK t ht x hx r hr hinside
  apply c18_kernel_diagonal_from_local_row_mass hκ hr hm ρ α hell K x hrow hsq _ hck
  refine hmass.trans_eq ?_
  apply integral_congr_ae
  filter_upwards [] with y
  have hρ : ρ y ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 y).1)
  exact (div_mul_cancel₀ (K t x y) hρ).symm

/-- Total killed mass and a second-moment estimate imply the local mass
needed for the spectral diagonal estimate. -/
theorem c18_native_spectral_local_diagonal_from_moment {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (r : ℝ) (hr : 0 < r) (hinside : sourceBall x r ⊆ sourceBall 0 R)
    (m M : ℝ) (hm : 0 ≤ m - M / r^2)
    (hsecond : IntegrableOn (fun y => K t x y * euclideanSq (y-x)) (sourceBall 0 R))
    (hmass : m ≤ ∫ y in sourceBall 0 R, K t x y)
    (hmoment : (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤ M) :
    (m - M / r^2)^2 /
      (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
      K (2*t) x x / ρ x := by
  obtain ⟨s, hs⟩ := hK.2
  let q : Vec d → ℝ := fun y => ∑' i, Real.exp (-s.eigenvalue i*t) *
    s.eigenfunction i x * s.eigenfunction i y
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hκ.le.trans (hell.2.2 y).1
  have hq : MemLp q 2 (dirichletVolume ρ R) :=
    spectral_heat_row_memLp hd hκ hell hR s t ht x hx
  have hqi := hq.integrable (by norm_num)
  unfold dirichletVolume at hqi
  have hqi' := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).1 hqi
  have hi : IntegrableOn (fun y => K t x y) (sourceBall 0 R) := by
    have hweight : IntegrableOn (fun y => q y * ρ y) (sourceBall 0 R) := by
      change Integrable (fun y => q y * ρ y) (volume.restrict (sourceBall 0 R))
      simpa [hρ0, smul_eq_mul, mul_comm] using hqi'
    apply hweight.congr_fun_ae
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
    rw [(hs t ht x hx y hy).2]
    ring
  have hnonneg : ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R), 0 ≤ K t x y := by
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
    exact (hK.1 y hy).2.1 t ht x hx
  have hlocal := c17_moment_to_interior_mass (volume.restrict (sourceBall (0 : Vec d) R))
    x r m M hr (fun y => K t x y) hi hnonneg hsecond hmass hmoment
  rw [Measure.restrict_restrict_of_subset hinside] at hlocal
  exact c18_native_spectral_local_diagonal_from_survival hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside (m - M / r^2) hm hlocal

/-- The bounded killed domain makes the native spectral row's second
moment integrable without a separate Gaussian or regularity hypothesis. -/
theorem c18_native_spectral_second_moment_integrable {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    IntegrableOn (fun y => K t x y * euclideanSq (y-x)) (sourceBall 0 R) := by
  obtain ⟨s, hs⟩ := hK.2
  let q : Vec d → ℝ := fun y => ∑' i, Real.exp (-s.eigenvalue i*t) *
    s.eigenfunction i x * s.eigenfunction i y
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun y _ => (hell.2.2 y).2.1)
  have hρ0 : ∀ y, 0 ≤ ρ y := fun y => hκ.le.trans (hell.2.2 y).1
  have hq : MemLp q 2 (dirichletVolume ρ R) :=
    spectral_heat_row_memLp hd hκ hell hR s t ht x hx
  have hqi := hq.integrable (by norm_num)
  unfold dirichletVolume at hqi
  have hqi' := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
    (ae_of_all _ fun y => ENNReal.ofReal_lt_top)).1 hqi
  have hi : IntegrableOn (fun y => K t x y) (sourceBall 0 R) := by
    have hweight : IntegrableOn (fun y => q y * ρ y) (sourceBall 0 R) := by
      change Integrable (fun y => q y * ρ y) (volume.restrict (sourceBall 0 R))
      simpa [hρ0, smul_eq_mul, mul_comm] using hqi'
    apply hweight.congr_fun_ae
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
    rw [(hs t ht x hx y hy).2]
    ring
  have hc : Continuous (fun y : Vec d => euclideanSq (y-x)) := by
    unfold euclideanSq dot
    exact continuous_finset_sum _ (fun i _ => ((continuous_apply i).sub continuous_const).mul
      ((continuous_apply i).sub continuous_const))
  apply hi.mul_bdd (c := (2*R)^2) hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
  have hy' : euclideanNorm y < R := by simpa [sourceBall] using hy
  have hx' : euclideanNorm x < R := by simpa [sourceBall] using hx
  have hneg : euclideanNorm (-x) = euclideanNorm x := by
    simpa using TimeChange.euclideanNorm_smul (-1 : ℝ) x
  have htri := TimeChange.euclideanNorm_add_le y (-x)
  rw [← sub_eq_add_neg, hneg] at htri
  have hn : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by
    rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]; positivity),
    TimeChange.euclideanSq_eq_sq_euclideanNorm]
  nlinarith

/-- A Gaussian upper bound for the native kernel controls its spatial second
moment, uniformly for all elliptic coefficients on the killed ball. -/
theorem c18_native_spectral_second_moment_gaussian {d : ℕ} (hd : 2 ≤ d)
    (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R,
      (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤
        (C * Real.rpow t (-(d : ℝ)/2)) *
          (Real.rpow (C*t) ((d : ℝ)/2+1) *
            ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z) := by
  obtain ⟨C, hC, hbound⟩ := c12_native_weighted_gaussian_upper d hd κ R hκ hR
  refine ⟨C, hC, ?_⟩
  intro ρ α hell K G hK t ht x hx
  let A : ℝ := C * Real.rpow t (-(d : ℝ)/2)
  have hA : 0 ≤ A := mul_nonneg hC.le (Real.rpow_nonneg ht.le _)
  have hCt : 0 < C*t := mul_pos hC ht
  have hg : Integrable (fun y : Vec d =>
      A * (Real.exp (-euclideanSq (y-x)/(C*t)) * euclideanSq (y-x))) := by
    have h := (c17_shifted_gaussian_second_moment_integrable d (C*t)⁻¹
      (inv_pos.mpr hCt) x).const_mul A
    convert h using 1 <;> ext y <;> congr 3 <;> rw [div_eq_mul_inv] <;> ring
  have hpoint : ∀ᵐ y ∂volume.restrict (sourceBall (0 : Vec d) R),
      K t x y * euclideanSq (y-x) ≤
        A * (Real.exp (-euclideanSq (y-x)/(C*t)) * euclideanSq (y-x)) := by
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
    have hs : 0 ≤ euclideanSq (y-x) := by
      rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]; positivity
    have hn : euclideanNorm (x-y) = euclideanNorm (y-x) := by
      rw [← neg_sub y x]
      simpa using TimeChange.euclideanNorm_smul (-1 : ℝ) (y-x)
    have hb := hbound ρ α hell K G hK t ht x hx y hy
    rw [hn, ← TimeChange.euclideanSq_eq_sq_euclideanNorm] at hb
    simpa only [A, mul_assoc] using mul_le_mul_of_nonneg_right hb hs
  have hi := c18_native_spectral_second_moment_integrable hd hκ hR ρ α hell K G hK t ht x hx
  have hle := integral_mono_ae hi hg.integrableOn hpoint
  have hfull := integral_mono_measure (Measure.restrict_le_self :
      volume.restrict (sourceBall (0 : Vec d) R) ≤ volume)
    (ae_of_all _ fun y => mul_nonneg hA (mul_nonneg (Real.exp_pos _).le (by
      rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]; positivity))) hg
  have h := hle.trans hfull
  rw [integral_const_mul, c17_gaussian_second_moment_formula d (C*t) hCt x] at h
  exact h

/-- The moment-based diagonal bound needs only its numerical moment estimate;
integrability follows from the bounded killed domain. -/
theorem c18_native_spectral_local_diagonal_from_moment_bound {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (r : ℝ) (hr : 0 < r) (hinside : sourceBall x r ⊆ sourceBall 0 R)
    (m M : ℝ) (hm : 0 ≤ m - M / r^2)
    (hmass : m ≤ ∫ y in sourceBall 0 R, K t x y)
    (hmoment : (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤ M) :
    (m - M / r^2)^2 /
      (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
      K (2*t) x x / ρ x :=
  c18_native_spectral_local_diagonal_from_moment hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside m M hm
    (c18_native_spectral_second_moment_integrable hd hκ hR ρ α hell K G hK t ht x hx)
    hmass hmoment

/-- Uniform diagonal control from quantitative total killed-mass and second
moment estimates for the actual kernel. -/
theorem c18_native_spectral_local_diagonal_uniform_from_moment {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (I J : Set ℝ) (X : Set (Vec d)) (m M : ℝ → Vec d → ℝ)
    (hmass : ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      m t x ≤ ∫ y in sourceBall 0 R, K t x y)
    (hmoment : ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤ M t x)
    (hnonneg : ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
        0 ≤ m t x - M t x / r^2) :
    ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
        (m t x - M t x / r^2)^2 /
          (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
          K (2*t) x x / ρ x := by
  intro t htI ht x hxX hx r hrJ hr hinside
  exact c18_native_spectral_local_diagonal_from_moment_bound hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside (m t x) (M t x)
    (hnonneg t htI ht x hxX hx r hrJ hr hinside)
    (hmass t htI ht x hxX hx) (hmoment t htI ht x hxX hx)

/-- For a fixed killed ball, the Gaussian second-moment estimate supplies the
moment input to the uniform diagonal consumer. -/
theorem c18_native_spectral_uniform_diagonal_from_total_mass {d : ℕ} (hd : 2 ≤ d)
    (κ R : ℝ) (hκ : 0 < κ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (I J : Set ℝ) (X : Set (Vec d)) (m : ℝ → Vec d → ℝ),
      let M := fun t : ℝ => (C * Real.rpow t (-(d : ℝ)/2)) *
        (Real.rpow (C*t) ((d : ℝ)/2+1) *
          ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z)
      (∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
        m t x ≤ ∫ y in sourceBall 0 R, K t x y) →
      (∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
        ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
          0 ≤ m t x - M t / r^2) →
      ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
        ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
          (m t x - M t / r^2)^2 /
            (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
            K (2*t) x x / ρ x := by
  obtain ⟨C, hC, hmoment⟩ := c18_native_spectral_second_moment_gaussian hd κ R hκ hR
  refine ⟨C, hC, ?_⟩
  intro ρ α hell K G hK I J X m M hmass hnonneg t htI ht x hxX hx r hrJ hr hinside
  exact c18_native_spectral_local_diagonal_from_moment_bound hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside (m t x) (M t)
    (hnonneg t htI ht x hxX hx r hrJ hr hinside)
    (hmass t htI ht x hxX hx) (hmoment ρ α hell K G hK t ht x hx)

/-- Uniform local survival for the actual spectral kernel yields the uniform
local diagonal bound, with no separate regularity or CK assumption. -/
theorem c18_native_spectral_local_diagonal_uniform {d : ℕ} (hd : 2 ≤ d)
    {κ R m : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hm : 0 ≤ m)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (I J : Set ℝ) (X : Set (Vec d))
    (hmass : ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
        m ≤ ∫ y in sourceBall x r, K t x y) :
    ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      ∀ r ∈ J, 0 < r → sourceBall x r ⊆ sourceBall 0 R →
        m^2 / (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
          K (2*t) x x / ρ x := by
  intro t htI ht x hxX hx r hrJ hr hinside
  exact c18_native_spectral_local_diagonal_from_survival hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside m hm (hmass t htI ht x hxX hx r hrJ hr hinside)

/-- Fully quantified local inputs for a family of times, centers and radii. -/
theorem c18_kernel_diagonal_from_uniform_local_inputs {d : ℕ}
    {κ m : ℝ} (hκ : 0 < κ) (hm : 0 ≤ m)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (I J : Set ℝ) (X : Set (Vec d))
    (hrow : ∀ t ∈ I, 0 < t → ∀ x ∈ X, ∀ r ∈ J, 0 < r →
      IntegrableOn (fun y => (K t x y / ρ y) * ρ y) (sourceBall x r))
    (hsquare : ∀ t ∈ I, 0 < t → ∀ x ∈ X, ∀ r ∈ J, 0 < r →
      IntegrableOn (fun y => (K t x y / ρ y)^2 * ρ y) (sourceBall x r))
    (hmass : ∀ t ∈ I, 0 < t → ∀ x ∈ X, ∀ r ∈ J, 0 < r →
      m ≤ ∫ y in sourceBall x r, (K t x y / ρ y) * ρ y)
    (hck : ∀ t ∈ I, 0 < t → ∀ x ∈ X, ∀ r ∈ J, 0 < r →
      (∫ y in sourceBall x r, (K t x y / ρ y)^2 * ρ y) ≤ K (2*t) x x / ρ x) :
    ∀ t ∈ I, 0 < t → ∀ x ∈ X, ∀ r ∈ J, 0 < r →
      m^2 / (κ⁻¹ * (r ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
        K (2*t) x x / ρ x := by
  intro t htI ht x hx r hrJ hr
  exact c18_kernel_diagonal_from_local_row_mass hκ hr hm ρ α hell K x
    (hrow t htI ht x hx r hrJ hr) (hsquare t htI ht x hx r hrJ hr)
    (hmass t htI ht x hx r hrJ hr) (hck t htI ht x hx r hrJ hr)

/-- The actual spectral kernel has a diagonal lower bound whenever its
weighted half-time row has the stated survival mass. The row's L² integrability
and the full squared-row identity are supplied by the spectral construction. -/
theorem c18_native_spectral_kernel_diagonal_from_row_mass {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (m : ℝ) (hm : 0 ≤ m)
    (hmass : m ≤ ∫ y in sourceBall 0 R, K t x y) :
    m^2 / (κ⁻¹ * (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
      K (2*t) x x / ρ x := by
  obtain ⟨s, hs⟩ := hK.2
  have hrow : m ≤ ∫ y in sourceBall 0 R,
      (∑' i, Real.exp (-s.eigenvalue i*t)*s.eigenfunction i x*s.eigenfunction i y)*ρ y := by
    refine hmass.trans_eq ?_
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (c12_sourceBall_volume (0 : Vec d) hR).1] with y hy
    rw [(hs t ht x hx y hy).2]
    ring
  have h := c12_native_spectral_diagonal_lower hd hκ hR ρ α hell s t ht x hx m hm hrow
  have hrepr := (hs (2*t) (by positivity) x hx x hx).2
  have hρ : ρ x ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 x).1)
  have hseries : (∑' i, Real.exp (-(s.eigenvalue i)*(2*t))*s.eigenfunction i x*s.eigenfunction i x) =
      ∑' i, Real.exp (-2*s.eigenvalue i*t)*(s.eigenfunction i x)^2 := by
    apply tsum_congr
    intro i
    have he : -(s.eigenvalue i) * (2*t) = -2*s.eigenvalue i*t := by ring
    rw [he]
    ring
  rw [hseries] at hrepr
  rw [hrepr, mul_div_cancel_left₀ _ hρ]
  rw [(c12_sourceBall_volume (0 : Vec d) hR).2.2.2] at h
  exact h

/-- A uniform survival estimate for the actual spectral kernel yields the
corresponding uniform diagonal estimate with the exact Euclidean volume. -/
theorem c18_native_spectral_kernel_diagonal_uniform {d : ℕ} (hd : 2 ≤ d)
    {κ R m : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hm : 0 ≤ m)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (I : Set ℝ) (X : Set (Vec d))
    (hmass : ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      m ≤ ∫ y in sourceBall (0 : Vec d) R, K t x y) :
    ∀ t ∈ I, 0 < t → ∀ x ∈ X, x ∈ sourceBall (0 : Vec d) R →
      m^2 / (κ⁻¹ * (R ^ d * (volume (euclideanBall (0 : Vec d) 1)).toReal)) ≤
        K (2*t) x x / ρ x := by
  intro t htI ht x hxX hx
  exact c18_native_spectral_kernel_diagonal_from_row_mass hd hκ hR ρ α hell K G hK
    t ht x hx m hm (hmass t htI ht x hxX hx)

end EinsteinFull.Calculus
