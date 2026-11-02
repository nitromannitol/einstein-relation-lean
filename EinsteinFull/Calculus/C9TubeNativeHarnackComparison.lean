import EinsteinFull.Calculus.C9TubeAeNearDiagonalAssembly
import EinsteinFull.Calculus.C9TubeNativeCutoffSurvival
import EinsteinFull.Calculus.C12TubeGaussianAssembly
import EinsteinFull.Calculus.C18TubeNativeDiagonalMassAssembly
import EinsteinFull.Calculus.C17TubeParabolicScaling
import EinsteinFull.Calculus.C13TubeGeneralChainAssembly

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology

namespace EinsteinFull.Calculus

/-- A total-mass lower bound and second-moment upper bound give local
mass for the actual spectral Dirichlet kernel. -/
theorem c9_native_kernel_local_mass_from_moment {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
    (r : ℝ) (hr : 0 < r) (hinside : sourceBall x r ⊆ sourceBall 0 R)
    (m M : ℝ)
    (hmass : m ≤ ∫ y in sourceBall 0 R, K t x y)
    (hmoment : (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤ M) :
    m - M / r^2 ≤ ∫ y in sourceBall x r, K t x y := by
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
  have hsecond := c18_native_spectral_second_moment_integrable hd hκ hR ρ α hell K G hK
    t ht x hx
  have hlocal := c17_moment_to_interior_mass (volume.restrict (sourceBall (0 : Vec d) R))
    x r m M hr (fun y => K t x y) hi hnonneg hsecond hmass hmoment
  rw [Measure.restrict_restrict_of_subset hinside] at hlocal
  exact hlocal

/-- Weighted half-time row mass and an almost-everywhere comparison imply
the near-diagonal lower bound. -/
theorem c9_native_harnack_row_near_diagonal
    (d : ℕ) (κ A H m : ℝ) (hκ : 0 < κ) (hA : 0 < A) (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ)
    (hρ : ∀ z, 0 ≤ ρ z ∧ ρ z ≤ κ⁻¹) (t : ℝ) (ht : 0 < t) (x y : Vec d),
    IntegrableOn (fun z => q (t/2) x z * ρ z) (sourceBall x (A * Real.sqrt (t/2))) →
    m ≤ (∫ z in sourceBall x (A * Real.sqrt (t/2)), q (t/2) x z * ρ z) →
    (∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
      0 ≤ q (t/2) x z ∧ q (t/2) x z ≤ H * q t x y) →
    c * Real.rpow t (-(d : ℝ)/2) ≤ q t x y :=
  c9_half_time_row_mass_near_diagonal_of_ae d κ A H m hκ hA hH hm

/-- Conditional near-diagonal estimate for the actual Dirichlet spectral row.
The hypotheses expose the missing pointwise parabolic Harnack estimate and the
positive-time caloric regularity of each spectral row. The existing weak Harnack
estimate concerns space-time averages and does not itself supply either input. -/
theorem c9_native_spectral_row_near_diagonal_of_caloric_harnack
    (d : ℕ) (hd : 2 ≤ d) (κ A H m L : ℝ) (hκ : 0 < κ) (hA : 0 < A)
    (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (s : DirichletSpectralResolution ρ α R) (hR : 0 < R)
      (hell : IsUniformlyElliptic κ ρ α) (hs : Tendsto s.eigenvalue atTop atTop)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (u n)) →
      (∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)) →
      (∀ (T : ℝ), 0 < T → ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo 0 (2*T)) (sourceBall 0 R) v G →
        ContinuousOn v (Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R) →
        (∀ p ∈ Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R, 0 ≤ v p) →
        ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
          sourceBall y ((L+2) * Real.sqrt T) ⊆ sourceBall 0 R →
          euclideanNorm (z-y) ≤ L * Real.sqrt T →
          v (T/2,z) ≤ H * v (T,y)) →
      ∀ (t : ℝ), 0 < t → ∀ x y : Vec d,
      x ∈ sourceBall 0 R →
      (∃ G : ℝ × Vec d → Vec d,
        IsWeightedCaloric ρ α (Set.Ioo 0 (2*t)) (sourceBall 0 R)
          (fun p => ∑' n, Real.exp (-s.eigenvalue n * p.1) *
            s.eigenfunction n x * s.eigenfunction n p.2) G) →
      y ∈ sourceBall 0 R →
      sourceBall y ((L+2) * Real.sqrt t) ⊆ sourceBall 0 R →
      (∀ z ∈ sourceBall x (A * Real.sqrt (t/2)),
        z ∈ sourceBall 0 R ∧ euclideanNorm (z-y) ≤ L * Real.sqrt t) →
      IntegrableOn (fun z => (∑' n, Real.exp (-s.eigenvalue n * (t/2)) *
        s.eigenfunction n x * s.eigenfunction n z) * ρ z)
        (sourceBall x (A * Real.sqrt (t/2))) →
      m ≤ (∫ z in sourceBall x (A * Real.sqrt (t/2)),
        (∑' n, Real.exp (-s.eigenvalue n * (t/2)) *
          s.eigenfunction n x * s.eigenfunction n z) * ρ z) →
      c * Real.rpow t (-(d : ℝ)/2) ≤
        ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y := by
  obtain ⟨c, hc, hnear⟩ := c9_half_time_row_mass_near_diagonal_of_ae d κ A H m hκ hA hH hm
  refine ⟨c, hc, ?_⟩
  intro ρ α R s hR hell hs u hb hv hh t ht x y hx hcal hy hinterior hgeom hint hmass
  have hcont : ContinuousOn (fun p : ℝ × Vec d => ∑' n,
      Real.exp (-s.eigenvalue n * p.1) * s.eigenfunction n x * s.eigenfunction n p.2)
      (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) := by
    apply (spectral_heat_continuousOn hd hκ hell hR s hs).comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
    intro p hp
    exact ⟨hp.1.1, hx, hp.2⟩
  have hnonneg : ∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R,
      0 ≤ ∑' n, Real.exp (-s.eigenvalue n * p.1) *
        s.eigenfunction n x * s.eigenfunction n p.2 := by
    intro p hp
    simpa only [Real.coe_toNNReal _ hp.1.1.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ hell R hR s hs u hb hv).2
        p.1.toNNReal (by simpa only [Real.coe_toNNReal _ hp.1.1.le] using hp.1.1)
        x hx p.2 hp.2
  let q : ℝ → Vec d → Vec d → ℝ := fun t x z =>
    ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n z
  apply hnear ρ q (fun z => ⟨hκ.le.trans (hell.2.2 z).1, (hell.2.2 z).2.1⟩)
    t ht x y hint hmass
  obtain ⟨G, hG⟩ := hcal
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceBall x (A * Real.sqrt (t/2))) by
    apply IsOpen.measurableSet
    unfold sourceBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const)] with z hz
  have hz' := hgeom z hz
  constructor
  · exact hnonneg (t/2,z) ⟨⟨by linarith, by linarith⟩, hz'.1⟩
  · exact hh t ht _ G hG hcont hnonneg z hz'.1 y hy hinterior hz'.2

/-- Starting the spectral semigroup from a positive-time row gives a caloric
function whose values are the native kernel at the sum of the two times. -/
theorem c9_native_positive_row_action_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (τ T : ℝ) (hτ : 0 < τ) (hT : 0 < T) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    ∃ G : ℝ × Vec d → Vec d,
      IsWeightedCaloric ρ α (Set.Ioo 0 T) (sourceBall 0 R)
        (fun p => ∫ y, (∑' n, Real.exp (-s.eigenvalue n * p.1) *
          s.eigenfunction n p.2 * s.eigenfunction n y) *
            spectralHeatRow s τ x y ∂dirichletVolume ρ R) G ∧
      ∀ p ∈ Set.Ioo 0 T ×ˢ sourceBall 0 R,
        (∫ y, (∑' n, Real.exp (-s.eigenvalue n * p.1) *
          s.eigenfunction n p.2 * s.eigenfunction n y) *
            spectralHeatRow s τ x y ∂dirichletVolume ρ R) =
        ∑' n, Real.exp (-s.eigenvalue n * (p.1 + τ)) *
          s.eigenfunction n x * s.eigenfunction n p.2 := by
  obtain ⟨G, hG⟩ := c9_native_kernel_action_weighted_caloric hd hκ hR hell s u hs hb hv
    (spectralHeatRow s τ x) T hT
  refine ⟨G, hG, ?_⟩
  intro p hp
  calc
    _ = inner ℝ (spectralHeatRow s p.1 p.2) (spectralHeatRow s τ x) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ hell hR s p.1 hp.1.1 p.2 hp.2] with y hy
      change spectralHeatRow s p.1 p.2 y = _ at hy
      simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]
    _ = _ := by
      rw [spectral_heat_row_inner hd hκ hell hR s p.1 τ hp.1.1 hτ p.2 x hp.2 hx]
      apply tsum_congr
      intro n
      ring


/-- The actual positive-time row action remains caloric after an interior
parabolic affine change of variables, and its values remain native rows. -/
theorem c9_native_positive_row_action_affine_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (τ T t₀ r : ℝ) (hτ : 0 < τ) (hT : 0 < T) (hr : 0 < r)
    (ht₀ : 0 ≤ t₀-r^2) (htT : t₀+r^2 ≤ T)
    (x y : Vec d) (hx : x ∈ sourceBall 0 R)
    (hinside : sourceBall y r ⊆ sourceBall 0 R) :
    ∃ G : ℝ × Vec d → Vec d,
      IsWeightedCaloric (fun z => ρ (y+r • z)) (fun z => α (y+r • z))
        (Set.Ioo (-1) 1) (sourceBall (0 : Vec d) 1)
        (fun p => ∫ z, (∑' n, Real.exp (-s.eigenvalue n * (t₀+r^2*p.1)) *
          s.eigenfunction n (y+r • p.2) * s.eigenfunction n z) *
            spectralHeatRow s τ x z ∂dirichletVolume ρ R)
        (fun p => r • G (t₀+r^2*p.1, y+r • p.2)) ∧
      ∀ p ∈ Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1,
        (∫ z, (∑' n, Real.exp (-s.eigenvalue n * (t₀+r^2*p.1)) *
          s.eigenfunction n (y+r • p.2) * s.eigenfunction n z) *
            spectralHeatRow s τ x z ∂dirichletVolume ρ R) =
        ∑' n, Real.exp (-s.eigenvalue n * (t₀+r^2*p.1+τ)) *
          s.eigenfunction n x * s.eigenfunction n (y+r • p.2) := by
  obtain ⟨G, hG, heq⟩ := c9_native_positive_row_action_caloric hd hκ hR hell s u hs hb hv
    τ T hτ hT x hx
  have hsub : Set.Ioo (t₀-r^2) (t₀+r^2) ⊆ Set.Ioo (0 : ℝ) T := by
    intro a ha
    exact ⟨lt_of_le_of_lt ht₀ ha.1, lt_of_lt_of_le ha.2 htT⟩
  have hlocal := c9_weighted_caloric_spatial_mono measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet hinside
    (c13_weighted_caloric_time_mono measurableSet_Ioo
      (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet hsub hG)
  refine ⟨G, c17_weighted_caloric_parabolic_rescale t₀ y hr ρ α _ _ hlocal, ?_⟩
  intro p hp
  apply (heq (t₀+r^2*p.1, y+r • p.2))
  constructor
  · apply hsub
    have hr2 : 0 < r^2 := sq_pos_of_pos hr
    constructor <;> nlinarith [hp.1.1, hp.1.2]
  · apply hinside
    exact (c17_mem_sourceBall_affine_iff y p.2 hr).2 hp.2

/-- A half-time ball around the row origin lies in the Harnack region whenever
the two points are within the stated Euclidean distance. -/
theorem c9_half_time_row_harnack_geometry {d : ℕ} {A B R t : ℝ}
    (hA : 0 ≤ A) (ht : 0 < t) (x y : Vec d)
    (hdist : euclideanNorm (x-y) ≤ B * Real.sqrt t)
    (hinside : sourceBall y ((A+B+2) * Real.sqrt t) ⊆ sourceBall 0 R) :
    ∀ z ∈ sourceBall x (A * Real.sqrt (t/2)),
      z ∈ sourceBall 0 R ∧ euclideanNorm (z-y) ≤ (A+B) * Real.sqrt t := by
  intro z hz
  have hz' : euclideanNorm (z-x) < A * Real.sqrt (t/2) := hz
  have hsqrt : Real.sqrt (t/2) ≤ Real.sqrt t := Real.sqrt_le_sqrt (by linarith)
  have hbound : euclideanNorm (z-x) ≤ A * Real.sqrt t :=
    (le_of_lt hz').trans (mul_le_mul_of_nonneg_left hsqrt hA)
  have htri := TimeChange.euclideanNorm_add_le (z-x) (x-y)
  have heq : (z-x) + (x-y) = z-y := by abel
  rw [heq] at htri
  have hzy : euclideanNorm (z-y) ≤ (A+B) * Real.sqrt t := by nlinarith
  refine ⟨hinside ?_, hzy⟩
  change euclideanNorm (z-y) < (A+B+2) * Real.sqrt t
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  nlinarith

/-- Local mass and the full almost-everywhere row comparison for the actual
Lebesgue-density kernel imply the native weighted near-diagonal estimate. -/
theorem c9_native_kernel_near_diagonal_of_row_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ A H m : ℝ)
    (hκ : 0 < κ) (hA : 0 < A) (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ),
      0 < R → IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (t : ℝ), 0 < t → ∀ x y : Vec d, x ∈ sourceBall 0 R →
      sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R →
      m ≤ (∫ z in sourceBall x (A * Real.sqrt (t/2)), K (t/2) x z) →
      (∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
        0 ≤ K (t/2) x z / ρ z ∧
        K (t/2) x z / ρ z ≤ H * (K t x y / ρ y)) →
      c * Real.rpow t (-(d : ℝ)/2) ≤ K t x y / ρ y := by
  obtain ⟨c, hc, hnear⟩ := c9_native_harnack_row_near_diagonal d κ A H m hκ hA hH hm
  refine ⟨c, hc, ?_⟩
  intro ρ α R hR hell K G hK t ht x y hx hinside hmass hrow
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  have hint := (c18_native_spectral_local_row_inputs hd hκ hR ρ α hell K G hK
    (t/2) ht2 x hx (A * Real.sqrt (t/2)) hr hinside).1
  have hmass' : m ≤ ∫ z in sourceBall x (A * Real.sqrt (t/2)),
      (K (t/2) x z / ρ z) * ρ z := by
    convert hmass using 1
    apply integral_congr_ae
    exact ae_of_all _ fun z => div_mul_cancel₀ _
      (ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 z).1))
  exact hnear ρ (fun t x z => K t x z / ρ z)
    (fun z => ⟨hκ.le.trans (hell.2.2 z).1, (hell.2.2 z).2.1⟩)
    t ht x y hint hmass' hrow

/-- Total mass and a second moment supply the local mass in the native
near-diagonal estimate; the full row comparison remains an explicit input. -/
theorem c9_native_kernel_near_diagonal_of_moment_and_row_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ A H m : ℝ)
    (hκ : 0 < κ) (hA : 0 < A) (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ),
      0 < R → IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (t : ℝ), 0 < t → ∀ x y : Vec d, x ∈ sourceBall 0 R →
      sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R →
      ∀ m₀ M : ℝ,
      m₀ ≤ (∫ z in sourceBall 0 R, K (t/2) x z) →
      (∫ z in sourceBall 0 R, K (t/2) x z * euclideanSq (z-x)) ≤ M →
      m ≤ m₀ - M / (A * Real.sqrt (t/2))^2 →
      (∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
        0 ≤ K (t/2) x z / ρ z ∧
        K (t/2) x z / ρ z ≤ H * (K t x y / ρ y)) →
      c * Real.rpow t (-(d : ℝ)/2) ≤ K t x y / ρ y := by
  obtain ⟨c, hc, hnear⟩ :=
    c9_native_kernel_near_diagonal_of_row_comparison d hd κ A H m hκ hA hH hm
  refine ⟨c, hc, ?_⟩
  intro ρ α R hR hell K G hK t ht x y hx hinside m₀ M hmass hmoment hm' hrow
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  have hlocal := c9_native_kernel_local_mass_from_moment hd hκ hR ρ α hell K G hK
    (t/2) ht2 x hx (A * Real.sqrt (t/2)) hr hinside m₀ M hmass hmoment
  exact hnear ρ α R hR hell K G hK t ht x y hx hinside (hm'.trans hlocal) hrow

/-- A positive-time semigroup action transfers a pointwise Harnack estimate to
native kernel values at half and full time. -/
theorem c9_native_spectral_row_comparison_of_harnack {d : ℕ} (hd : 2 ≤ d)
    {κ R H L t : ℝ} (hκ : 0 < κ) (hR : 0 < R) (ht : 0 < t)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (hh : ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo 0 (2*t)) (sourceBall 0 R) v G →
      ContinuousOn v (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) →
      (∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R, 0 ≤ v p) →
      ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
        sourceBall y ((L+2) * Real.sqrt t) ⊆ sourceBall 0 R →
        euclideanNorm (z-y) ≤ L * Real.sqrt t →
        v (t/4,z) ≤ H * v (3*t/4,y))
    (x z y : Vec d) (hx : x ∈ sourceBall 0 R) (hz : z ∈ sourceBall 0 R)
    (hy : y ∈ sourceBall 0 R)
    (hinterior : sourceBall y ((L+2) * Real.sqrt t) ⊆ sourceBall 0 R)
    (hgeom : euclideanNorm (z-y) ≤ L * Real.sqrt t) :
    (∑' n, Real.exp (-s.eigenvalue n * (t/2)) *
      s.eigenfunction n x * s.eigenfunction n z) ≤ H *
    (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n y) := by
  let v : ℝ × Vec d → ℝ := fun p => ∫ y,
    (∑' n, Real.exp (-s.eigenvalue n * p.1) * s.eigenfunction n p.2 *
      s.eigenfunction n y) * spectralHeatRow s (t/4) x y ∂dirichletVolume ρ R
  obtain ⟨G, hG, heq⟩ := c9_native_positive_row_action_caloric hd hκ hR hell s u hs hb hv
    (t/4) (2*t) (by positivity) (by positivity) x hx
  have hcont : ContinuousOn v (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) :=
    (c9_native_heat_action_joint_continuous hd hκ hR hell s hs
      (spectralHeatRow s (t/4) x)).mono (by intro p hp; exact ⟨hp.1.1, hp.2⟩)
  have hnonneg : ∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R, 0 ≤ v p := by
    intro p hp
    dsimp only [v]
    rw [heq p hp]
    have htime : 0 < p.1 + t/4 := by linarith [hp.1.1]
    simpa only [Real.coe_toNNReal _ htime.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ hell R hR s hs u hb hv).2
        (p.1 + t/4).toNNReal (by simpa only [Real.coe_toNNReal _ htime.le] using htime)
        x hx p.2 hp.2
  have hcomp := hh v G hG hcont hnonneg z hz y hy hinterior hgeom
  dsimp only [v] at hcomp
  rw [heq (t/4,z) ⟨⟨by linarith, by linarith⟩, hz⟩,
    heq (3*t/4,y) ⟨⟨by linarith, by linarith⟩, hy⟩] at hcomp
  have hearly : t/4 + t/4 = t/2 := by ring
  have hlate : 3*t/4 + t/4 = t := by ring
  simpa only [hearly, hlate] using hcomp

/-- The native row comparison and local mass imply the near-diagonal bound. -/
theorem c9_native_spectral_row_near_diagonal_of_positive_action_harnack
    (d : ℕ) (hd : 2 ≤ d) (κ A H m L : ℝ) (hκ : 0 < κ) (hA : 0 < A)
    (hH : 0 < H) (hm : 0 < m) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d) (R : ℝ)
      (s : DirichletSpectralResolution ρ α R) (hR : 0 < R)
      (hell : IsUniformlyElliptic κ ρ α) (hs : Tendsto s.eigenvalue atTop atTop)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (u n)) →
      (∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)) →
      (∀ (T : ℝ), 0 < T → ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo 0 (2*T)) (sourceBall 0 R) v G →
        ContinuousOn v (Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R) →
        (∀ p ∈ Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R, 0 ≤ v p) →
        ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
          sourceBall y ((L+2) * Real.sqrt T) ⊆ sourceBall 0 R →
          euclideanNorm (z-y) ≤ L * Real.sqrt T →
          v (T/4,z) ≤ H * v (3*T/4,y)) →
      ∀ (t : ℝ), 0 < t → ∀ x y : Vec d,
      x ∈ sourceBall 0 R →
      y ∈ sourceBall 0 R →
      sourceBall y ((L+2) * Real.sqrt t) ⊆ sourceBall 0 R →
      (∀ z ∈ sourceBall x (A * Real.sqrt (t/2)),
        z ∈ sourceBall 0 R ∧ euclideanNorm (z-y) ≤ L * Real.sqrt t) →
      IntegrableOn (fun z => (∑' n, Real.exp (-s.eigenvalue n * (t/2)) *
        s.eigenfunction n x * s.eigenfunction n z) * ρ z)
        (sourceBall x (A * Real.sqrt (t/2))) →
      m ≤ (∫ z in sourceBall x (A * Real.sqrt (t/2)),
        (∑' n, Real.exp (-s.eigenvalue n * (t/2)) *
          s.eigenfunction n x * s.eigenfunction n z) * ρ z) →
      c * Real.rpow t (-(d : ℝ)/2) ≤
        ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n y := by
  obtain ⟨c, hc, hnear⟩ := c9_half_time_row_mass_near_diagonal_of_ae d κ A H m hκ hA hH hm
  refine ⟨c, hc, ?_⟩
  intro ρ α R s hR hell hs u hb hv hh t ht x y hx hy hinterior hgeom hint hmass
  let q : ℝ → Vec d → Vec d → ℝ := fun t x z =>
    ∑' n, Real.exp (-s.eigenvalue n * t) * s.eigenfunction n x * s.eigenfunction n z
  apply hnear ρ q (fun z => ⟨hκ.le.trans (hell.2.2 z).1, (hell.2.2 z).2.1⟩)
    t ht x y hint hmass
  filter_upwards [ae_restrict_mem (show MeasurableSet (sourceBall x (A * Real.sqrt (t/2))) by
    apply IsOpen.measurableSet
    unfold sourceBall euclideanNorm euclideanSq dot
    exact isOpen_lt (by fun_prop) continuous_const)] with z hz
  have hz' := hgeom z hz
  constructor
  · have ht' : 0 < t/2 := by positivity
    simpa only [Real.coe_toNNReal _ ht'.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ hell R hR s hs u hb hv).2
        (t/2).toNNReal (by simpa only [Real.coe_toNNReal _ ht'.le] using ht')
        x hx z hz'.1
  · exact c9_native_spectral_row_comparison_of_harnack hd hκ hR ht hell s u hs hb hv
      (hh t ht) x z y hx hz'.1 hy hinterior hz'.2

/-- The native Gaussian constant can be selected before the killed-ball radius. -/
theorem c9_native_weighted_gaussian_upper_uniform_radius (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      K t x y ≤ C * Real.rpow t (-(d : ℝ)/2) *
        Real.exp (-(euclideanNorm (x-y))^2/(C*t)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := c12_spectral_gaussian_envelope_pointwise hd hκ
  let p : ℝ := -(d : ℝ)/2
  let P : ℝ := κ⁻¹ * (A * ((1/2 : ℝ) ^ p) / κ)
  let Q : ℝ := 2 * B
  let C : ℝ := P + Q + 1
  have hP : 0 < P := by dsimp [P]; positivity
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h K G hK t ht x hx y hy
  have hh := hbound hR h K G hK (t/2) (by positivity) x hx y hy
  have htime : t/2+t/2 = t := by ring
  rw [htime] at hh
  have hrpow : (t/2) ^ p = (1/2 : ℝ)^p * t^p := by
    have he : t/2 = (1/2 : ℝ)*t := by ring
    rw [he, Real.mul_rpow (by norm_num) ht.le]
  have hden : B * (t/2) = Q*t/4 := by dsimp [Q]; ring
  have hratio : -(euclideanNorm (x-y))^2 / (B*(t/2)) ≤
      -(euclideanNorm (x-y))^2 / (C*t) := by
    have hbt : 0 < B*(t/2) := by positivity
    have hct : 0 < C*t := by positivity
    have hle : B*(t/2) ≤ C*t := by dsimp [C, Q]; nlinarith
    have hn : 0 ≤ (euclideanNorm (x-y))^2 := sq_nonneg _
    apply (div_le_div_iff₀ hbt hct).2
    nlinarith
  have hexp := Real.exp_le_exp.mpr hratio
  have hp : 0 ≤ t^p := Real.rpow_nonneg ht.le _
  have hPC : P ≤ C := by dsimp [C]; linarith
  have hcoeff : P*t^p ≤ C*t^p := mul_le_mul_of_nonneg_right hPC hp
  have hbase : K t x y ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(B*(t/2))) := by
    rw [show (t/2) ^ (-(d : ℝ)/2) = (t/2)^p by rfl, hrpow] at hh
    dsimp [P]
    convert hh using 1 <;> ring
  calc
    K t x y ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(B*(t/2))) := hbase
    _ ≤ P*t^p * Real.exp (-(euclideanNorm (x-y))^2/(C*t)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hP.le hp)
    _ ≤ C*t^p * Real.exp (-(euclideanNorm (x-y))^2/(C*t)) :=
      mul_le_mul_of_nonneg_right hcoeff (Real.exp_pos _).le


/-- The Gaussian second-moment envelope is uniform in the killed-ball radius. -/
theorem c9_native_spectral_second_moment_uniform_radius {d : ℕ} (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R,
      (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤
        (C * Real.rpow t (-(d : ℝ)/2)) *
          (Real.rpow (C*t) ((d : ℝ)/2+1) *
            ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z) := by
  obtain ⟨C, hC, hbound⟩ := c9_native_weighted_gaussian_upper_uniform_radius d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α hell K G hK t ht x hx
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
    have hb := hbound R hR ρ α hell K G hK t ht x hx y hy
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



/-- The native second moment has a constant selected before the killed radius. -/
theorem c9_native_second_moment_uniform_radius {d : ℕ} (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R,
        (∫ y in sourceBall 0 R, K t x y * euclideanSq (y-x)) ≤ M * t := by
  obtain ⟨C, hC, hmoment⟩ := c9_native_spectral_second_moment_uniform_radius hd κ hκ
  let S : ℝ := ∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z
  have hS : 0 ≤ S := by
    apply integral_nonneg
    intro z
    apply mul_nonneg (Real.exp_pos _).le
    rw [TimeChange.euclideanSq_eq_sq_euclideanNorm]
    positivity
  refine ⟨(S+1) * Real.rpow C ((d : ℝ)/2+2),
    mul_pos (by linarith) (Real.rpow_pos_of_pos hC _), ?_⟩
  intro R hR ρ α hell K G hK t ht x hx
  have hh := hmoment R hR ρ α hell K G hK t ht x hx
  have ht' : t ^ (-(d : ℝ)/2) * t ^ ((d : ℝ)/2+1) = t := by
    rw [← Real.rpow_add ht]
    convert Real.rpow_one t using 1 <;> ring
  have hC' : C * C ^ ((d : ℝ)/2+1) = C ^ ((d : ℝ)/2+2) := by
    calc
      _ = C ^ (1 : ℝ) * C ^ ((d : ℝ)/2+1) := by rw [Real.rpow_one]
      _ = C ^ (1 + ((d : ℝ)/2+1)) := (Real.rpow_add hC _ _).symm
      _ = _ := by congr 1; ring
  have halg : (C * Real.rpow t (-(d : ℝ)/2)) *
      (Real.rpow (C*t) ((d : ℝ)/2+1) * S) =
      S * Real.rpow C ((d : ℝ)/2+2) * t := by
    change C * t ^ (-(d : ℝ)/2) * ((C*t) ^ ((d : ℝ)/2+1) * S) =
      S * C ^ ((d : ℝ)/2+2) * t
    rw [Real.mul_rpow hC.le ht.le]
    calc
      _ = S * (C * C ^ ((d : ℝ)/2+1)) *
          (t ^ (-(d : ℝ)/2) * t ^ ((d : ℝ)/2+1)) := by ring
      _ = _ := by rw [hC', ht']
  rw [show (∫ z : Vec d, Real.exp (-euclideanSq z) * euclideanSq z) = S from rfl,
    halg] at hh
  calc
    _ ≤ S * Real.rpow C ((d : ℝ)/2+2) * t := hh
    _ ≤ (S+1) * Real.rpow C ((d : ℝ)/2+2) * t := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : S ≤ S+1)
          (Real.rpow_nonneg hC.le _)) ht.le


/-- The native local-mass loss is controlled uniformly in the killed radius. -/
theorem c9_native_kernel_local_mass_uniform_radius (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R, ∀ r : ℝ, 0 < r →
      sourceBall x r ⊆ sourceBall 0 R → ∀ m : ℝ,
      m ≤ (∫ y in sourceBall 0 R, K t x y) →
      m - M * t / r^2 ≤ ∫ y in sourceBall x r, K t x y := by
  obtain ⟨M, hM, hmoment⟩ := c9_native_second_moment_uniform_radius hd κ hκ
  refine ⟨M, hM, ?_⟩
  intro R hR ρ α hell K G hK t ht x hx r hr hinside m hmass
  exact c9_native_kernel_local_mass_from_moment hd hκ hR ρ α hell K G hK
    t ht x hx r hr hinside m (M*t) hmass (hmoment R hR ρ α hell K G hK t ht x hx)


/-- At half time, a diffusive-radius ball loses at most a time-independent
amount of native total mass. -/
theorem c9_native_half_time_local_mass_uniform (d : ℕ) (hd : 2 ≤ d)
    (κ A : ℝ) (hκ : 0 < κ) (hA : 0 < A) :
    ∃ M : ℝ, 0 < M ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R,
      sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R → ∀ m : ℝ,
      m ≤ (∫ y in sourceBall 0 R, K (t/2) x y) →
      m - M / A^2 ≤ ∫ y in sourceBall x (A * Real.sqrt (t/2)), K (t/2) x y := by
  obtain ⟨M, hM, hlocal⟩ := c9_native_kernel_local_mass_uniform_radius d hd κ hκ
  refine ⟨M, hM, ?_⟩
  intro R hR ρ α hell K G hK t ht x hx hinside m hmass
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  have h := hlocal R hR ρ α hell K G hK (t/2) ht2 x hx
    (A * Real.sqrt (t/2)) hr hinside m hmass
  have heq : M * (t/2) / (A * Real.sqrt (t/2))^2 = M / A^2 := by
    rw [mul_pow, Real.sq_sqrt ht2.le]
    field_simp
  simpa only [heq] using h


/-- Half of the total mass yields a uniform quarter-mass on a sufficiently
large diffusive-radius ball. The radius factor is chosen before the domain. -/
theorem c9_native_half_time_quarter_mass (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall 0 R,
      sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R →
      (1/2 : ℝ) ≤ (∫ y in sourceBall 0 R, K (t/2) x y) →
      (1/4 : ℝ) ≤ ∫ y in sourceBall x (A * Real.sqrt (t/2)), K (t/2) x y := by
  obtain ⟨M, hM, hlocal⟩ := c9_native_kernel_local_mass_uniform_radius d hd κ hκ
  let A : ℝ := 2*M+1
  have hA : 0 < A := by dsimp [A]; linarith
  refine ⟨A, hA, ?_⟩
  intro R hR ρ α hell K G hK t ht x hx hinside hmass
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  have h := hlocal R hR ρ α hell K G hK (t/2) ht2 x hx
    (A * Real.sqrt (t/2)) hr hinside (1/2) hmass
  have heq : M * (t/2) / (A * Real.sqrt (t/2))^2 = M / A^2 := by
    rw [mul_pow, Real.sq_sqrt ht2.le]
    field_simp
  rw [heq] at h
  have hquarter : M / A^2 ≤ (1/4 : ℝ) := by
    apply (div_le_iff₀ (sq_pos_of_pos hA)).2
    dsimp [A]
    nlinarith [sq_nonneg M]
  linarith


/-- Total half-survival and the full native row comparison imply a
near-diagonal bound with constants selected before the killed-ball radius. -/
theorem c9_native_kernel_near_diagonal_of_half_survival_and_row_comparison
    (d : ℕ) (hd : 2 ≤ d) (κ H : ℝ) (hκ : 0 < κ) (hH : 0 < H) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧
    ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ t : ℝ, 0 < t → ∀ x y : Vec d, x ∈ sourceBall 0 R →
      sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R →
      (1/2 : ℝ) ≤ (∫ z in sourceBall 0 R, K (t/2) x z) →
      (∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
        0 ≤ K (t/2) x z / ρ z ∧
        K (t/2) x z / ρ z ≤ H * (K t x y / ρ y)) →
      c * Real.rpow t (-(d : ℝ)/2) ≤ K t x y / ρ y := by
  obtain ⟨A, hA, hmass⟩ := c9_native_half_time_quarter_mass d hd κ hκ
  obtain ⟨c, hc, hnear⟩ := c9_native_kernel_near_diagonal_of_row_comparison
    d hd κ A H (1/4) hκ hA hH (by norm_num)
  refine ⟨A, c, hA, hc, ?_⟩
  intro R hR ρ α hell K G hK t ht x y hx hinside hsurvival hrow
  exact hnear ρ α R hR hell K G hK t ht x y hx hinside
    (hmass R hR ρ α hell K G hK t ht x hx hinside hsurvival) hrow


/-- The full shifted pointwise Harnack input gives the almost-everywhere
comparison of the supplied native kernel rows on a diffusive ball. -/
theorem c9_native_kernel_row_comparison_of_shifted_harnack {d : ℕ} (hd : 2 ≤ d)
    {κ R H A B t : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hA : 0 < A) (ht : 0 < t)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (s : DirichletSpectralResolution ρ α R)
    (hrep : ∀ τ, 0 < τ → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      K τ x y = ρ y * (∑' n, Real.exp (-s.eigenvalue n*τ) *
        s.eigenfunction n x * s.eigenfunction n y))
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w))
    (hh : ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo 0 (2*t)) (sourceBall 0 R) v G →
      ContinuousOn v (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) →
      (∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R, 0 ≤ v p) →
      ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
        sourceBall y ((A+B+2) * Real.sqrt t) ⊆ sourceBall 0 R →
        euclideanNorm (z-y) ≤ (A+B) * Real.sqrt t →
        v (t/4,z) ≤ H * v (3*t/4,y))
    (x y : Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R)
    (hdist : euclideanNorm (x-y) ≤ B * Real.sqrt t)
    (hinside : sourceBall y ((A+B+2) * Real.sqrt t) ⊆ sourceBall 0 R) :
    ∀ᵐ z ∂volume.restrict (sourceBall x (A * Real.sqrt (t/2))),
      0 ≤ K (t/2) x z / ρ z ∧
      K (t/2) x z / ρ z ≤ H * (K t x y / ρ y) := by
  have ht2 : 0 < t/2 := by positivity
  have hr : 0 < A * Real.sqrt (t/2) := mul_pos hA (Real.sqrt_pos.2 ht2)
  have hgeom := c9_half_time_row_harnack_geometry hA.le ht x y hdist hinside
  filter_upwards [ae_restrict_mem (c12_sourceBall_volume x hr).1] with z hz
  have hzdom := (hgeom z hz).1
  have hρz : ρ z ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 z).1)
  have hρy : ρ y ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 y).1)
  constructor
  · exact div_nonneg ((hK.1 z hzdom).2.1 (t/2) ht2 x hx)
      (hκ.le.trans (hell.2.2 z).1)
  · rw [hrep (t/2) ht2 x hx z hzdom, hrep t ht x hx y hy,
      mul_div_cancel_left₀ _ hρz, mul_div_cancel_left₀ _ hρy]
    apply c9_native_spectral_row_comparison_of_harnack hd hκ hR ht hell s u hs hb hv
      hh x z y hx hzdom hy
    · simpa only [add_assoc] using hinside
    · exact (hgeom z hz).2

/-- Conditional native near-diagonal bound from half-survival and the full
shifted pointwise Harnack estimate. Constants are uniform in the domain. -/
theorem c9_native_kernel_near_diagonal_of_half_survival_and_shifted_harnack
    (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ A : ℝ, 0 < A ∧ ∀ H : ℝ, 0 < H → ∃ c : ℝ, 0 < c ∧
    ∀ (R : ℝ) (hR : 0 < R) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (hell : IsUniformlyElliptic κ ρ α),
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (s : DirichletSpectralResolution ρ α R),
      (∀ τ, 0 < τ → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
        K τ x y = ρ y * (∑' n, Real.exp (-s.eigenvalue n*τ) *
          s.eigenfunction n x * s.eigenfunction n y)) →
      ∀ (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop →
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (u n)) →
      (∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (hell.2.2 x).2.1) w)) →
      ∀ (t : ℝ), 0 < t → ∀ (B : ℝ),
      (∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
        IsWeightedCaloric ρ α (Set.Ioo 0 (2*t)) (sourceBall 0 R) v G →
        ContinuousOn v (Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R) →
        (∀ p ∈ Set.Ioo 0 (2*t) ×ˢ sourceBall 0 R, 0 ≤ v p) →
        ∀ z ∈ sourceBall (0 : Vec d) R, ∀ y ∈ sourceBall (0 : Vec d) R,
          sourceBall y ((A+B+2) * Real.sqrt t) ⊆ sourceBall 0 R →
          euclideanNorm (z-y) ≤ (A+B) * Real.sqrt t →
          v (t/4,z) ≤ H * v (3*t/4,y)) →
      ∀ x y : Vec d, x ∈ sourceBall 0 R → y ∈ sourceBall 0 R →
      euclideanNorm (x-y) ≤ B * Real.sqrt t →
      sourceBall y ((A+B+2) * Real.sqrt t) ⊆ sourceBall 0 R →
      (1/2 : ℝ) ≤ (∫ z in sourceBall 0 R, K (t/2) x z) →
      c * Real.rpow t (-(d : ℝ)/2) ≤ K t x y / ρ y := by
  obtain ⟨A, hA, hmass⟩ := c9_native_half_time_quarter_mass d hd κ hκ
  refine ⟨A, hA, ?_⟩
  intro H hH
  obtain ⟨c, hc, hnear⟩ := c9_native_kernel_near_diagonal_of_row_comparison
    d hd κ A H (1/4) hκ hA hH (by norm_num)
  refine ⟨c, hc, ?_⟩
  intro R hR ρ α hell K G hK s hrep u hs hb hv t ht B hh x y hx hy hdist hinside hsurvival
  have hsub : sourceBall x (A * Real.sqrt (t/2)) ⊆ sourceBall 0 R :=
    fun z hz => (c9_half_time_row_harnack_geometry hA.le ht x y hdist hinside z hz).1
  have hrow := c9_native_kernel_row_comparison_of_shifted_harnack hd hκ hR hA ht
    hell K G hK s hrep u hs hb hv hh x y hx hy hdist hinside
  exact hnear ρ α R hR hell K G hK t ht x y hx hsub
    (hmass R hR ρ α hell K G hK t ht x hx hsub hsurvival) hrow

end EinsteinFull.Calculus
