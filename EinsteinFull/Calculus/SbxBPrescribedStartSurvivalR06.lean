import EinsteinFull.Calculus.C9TubeNativeCutoffSurvival
import EinsteinFull.Calculus.SbxBNativeSurvivalMassR05
import EinsteinFull.Calculus.C17TubeScaledLocalMax
import EinsteinFull.Calculus.SbxBNativeSpectralCompactnessR06

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- On an open spacetime set, continuity turns an essential bound into a
pointwise bound. The value of the bound may be zero. -/
theorem b_spacetime_abs_le_of_essSup {d : ℕ}
    (U : Set (ℝ × Vec d)) (hU : IsOpen U) (u : ℝ × Vec d → ℝ)
    (hu : ContinuousOn u U) (B : ℝ) (hB : 0 ≤ B)
    (hess : essSup (fun z => ENNReal.ofReal |u z|) (volume.restrict U) ≤
      ENNReal.ofReal B) :
    ∀ z ∈ U, |u z| ≤ B := by
  have hae : ∀ᵐ z ∂volume.restrict U, |u z| ≤ B := by
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict U)
      (fun z => ENNReal.ofReal |u z|)] with z hz
    exact (ENNReal.ofReal_le_ofReal_iff hB).mp (hz.trans hess)
  have heq : (fun z => |u z|) =ᵐ[volume.restrict U]
      (fun z => min B |u z|) := by
    filter_upwards [hae] with z hz
    exact (min_eq_right hz).symm
  have hp := Measure.eqOn_open_of_ae_eq heq hU hu.abs
    ((continuousOn_const : ContinuousOn (fun _ : ℝ × Vec d => B) U).inf hu.abs)
  intro z hz
  calc
    |u z| = min B |u z| := hp hz
    _ ≤ B := min_le_left _ _

/-- An essential bound on a larger set controls a continuous representative
pointwise on any open subset. -/
theorem b_spacetime_abs_le_of_larger_essSup {d : ℕ}
    (U V : Set (ℝ × Vec d)) (hU : IsOpen U) (hUV : U ⊆ V)
    (u : ℝ × Vec d → ℝ) (hu : ContinuousOn u U) (B : ℝ) (hB : 0 ≤ B)
    (hess : essSup (fun z => ENNReal.ofReal |u z|) (volume.restrict V) ≤
      ENNReal.ofReal B) :
    ∀ z ∈ U, |u z| ≤ B := by
  have hae : ∀ᵐ z ∂volume.restrict U, ENNReal.ofReal |u z| ≤ ENNReal.ofReal B := by
    apply ae_restrict_of_ae_restrict_of_subset hUV
    filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict V)
      (fun z => ENNReal.ofReal |u z|)] with z hz
    exact hz.trans hess
  exact b_spacetime_abs_le_of_essSup U hU u hu B hB (essSup_le_of_ae_le _ hae)

/-- The supplied spectral modes have the Dirichlet carriers and variational
equations required by the native zero-past caloricity theorem. -/
theorem b_supplied_modes_have_dirichlet_carriers {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ u : ℕ → DirichletHilbertSpace (d := d) R hR,
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)) := by
  classical
  choose u hu heq using fun n =>
    c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  refine ⟨u, ?_, heq⟩
  intro n
  have hb : spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) :=
    congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n
  rw [hb]
  apply Lp.ext
  exact ((s.square_integrable n).coeFn_toLp).trans (hu n).symm

/-- The actual zero-past cutoff defect is weighted caloric and is jointly
continuous in the positive-time interior. Eigenvalue escape is the only
remaining native spectral input to this bridge. -/
theorem b_native_cutoff_defect_caloric_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (hs : Tendsto s.eigenvalue atTop atTop)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (y : Vec d) (r T : ℝ) (hr : 0 < r) (hT : 0 < T)
    (hinside : closure (sourceBall y (2 * r)) ⊆ sourceBall 0 R)
    (hplateau : ∀ x ∈ sourceBall y (2 * r), φ x = 1) :
    let v : ℝ × Vec d → ℝ := fun z => if 0 < z.1 then
      (∫ x, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
        s.eigenfunction n z.2 * s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1
      else 0
    ∃ G, IsWeightedCaloric ρ α (Set.Ioo (-T) T) (sourceBall y r) v G ∧
      ContinuousOn v (Set.Ioo (0 : ℝ) T ×ˢ sourceBall y r) := by
  obtain ⟨u, hb, hv⟩ := b_supplied_modes_have_dirichlet_carriers hκ hR hell s
  obtain ⟨G, hcal⟩ := c9_native_cutoff_zero_past_caloric hd hκ hR hell s u hs hb hv
    φ hφ hφbounds y r T hr hT hinside hplateau
  refine ⟨_, hcal, ?_⟩
  have hsub : Set.Ioo (0 : ℝ) T ×ˢ sourceBall y r ⊆
      Set.Ioi 0 ×ˢ sourceBall 0 R := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    refine ⟨ht.1, hinside (subset_closure ?_)⟩
    change euclideanNorm (x - y) < r at hx
    change euclideanNorm (x - y) < 2 * r
    linarith
  have hc := (c9_native_cutoff_action_joint_continuous hd hκ hR hell s hs
    φ hφ hφbounds).mono hsub
  have hc1 : ContinuousOn (fun _ : ℝ × Vec d => (1 : ℝ))
      (Set.Ioo (0 : ℝ) T ×ˢ sourceBall y r) := continuousOn_const
  apply (hc.sub hc1).congr
  intro z hz
  simp [hz.1.1]

/-- Integrating a linear-in-time slice estimate yields a spacetime estimate.
The slice estimate is kept visible so this measure-theoretic step can be used
with the independently proved native cutoff trace. -/
theorem b_spacetime_L2_of_slice_linear_bound {d : ℕ} {T E : ℝ}
    (hT : 0 < T) (hE : 0 ≤ E) (U : Set (Vec d))
    (v : ℝ × Vec d → ℝ)
    (hm : MemLp v 2 (volume.restrict (Set.Ioo (0 : ℝ) T ×ˢ U)))
    (hslice : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      (∫ x in U, |v (t,x)|^2) ≤ E * t) :
    (∫ z in Set.Ioo (0 : ℝ) T ×ˢ U, |v z|^2) ≤ E * T^2 := by
  have hi : Integrable (fun z => |v z|^2)
      (volume.restrict (Set.Ioo (0 : ℝ) T ×ˢ U)) := by
    simpa only [sq_abs] using hm.integrable_sq
  have hip := hi
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hip
  have ht : Integrable (fun t => ∫ x in U, |v (t,x)|^2)
      (volume.restrict (Set.Ioo (0 : ℝ) T)) := hip.integral_prod_left
  have : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) T)) := ⟨by simp⟩
  have hb : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) T),
      (∫ x in U, |v (t,x)|^2) ≤ E * T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht'
    exact (hslice t ht').trans (mul_le_mul_of_nonneg_left ht'.2.le hE)
  calc
    (∫ z in Set.Ioo (0 : ℝ) T ×ˢ U, |v z|^2) =
        ∫ t in Set.Ioo (0 : ℝ) T, ∫ x in U, |v (t,x)|^2 := by
          rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
          exact integral_prod _ hip
    _ ≤ ∫ _t in Set.Ioo (0 : ℝ) T, E * T := integral_mono_ae ht (integrable_const _) hb
    _ = E * T^2 := by
      simp [max_eq_left hT.le, pow_two, mul_comm, mul_left_comm]

/-- The spectral action for the particular resolution supplied with the
kernel is its literal Lebesgue cutoff action. -/
theorem b_supplied_spectral_cutoff_action {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) ∧
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
    (fun x => Blueprint.TubeProbability.SpectralHeat.heatOperator
      (spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t
      (hp.toLp φ) x) =ᵐ[dirichletVolume ρ R]
      fun x => ∫ y in sourceBall (0 : Vec d) R, K t x y * φ y := by
  let hp := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  have hsumm : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hspec t ht x hx y hy).1
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  filter_upwards [c16_supplied_spectral_heat_operator_ae_kernel_action
    s hsumm t ht (hp.toLp φ), hball] with x hx hxb
  rw [hx, ← b_native_weighted_cutoff_eq hκ hell K φ t x]
  apply integral_congr_ae
  filter_upwards [hp.coeFn_toLp, hball] with y hy hyb
  rw [hy, (hspec t ht x hxb y hyb).2]
  have hρ : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
  field_simp
  have hsum : (∑' n, Real.exp (-(s.eigenvalue n * (t : ℝ))) *
      s.eigenfunction n x * s.eigenfunction n y) =
      (∑' n, Real.exp (-((t : ℝ) * s.eigenvalue n)) *
        s.eigenfunction n x * s.eigenfunction n y) := by
    apply tsum_congr
    intro n
    rw [mul_comm (s.eigenvalue n) (t : ℝ)]
  rw [hsum, mul_comm]

/-- The checked global cutoff trace is integrable in time and its integral
is bounded quadratically in the time horizon. -/
theorem b_native_cutoff_integrated_trace {d : ℕ} {R r : ℝ}
    (hR : 0 < R) (hr : 0 < r) (x : Vec d)
    (hinside : sourceBall x (2 * r) ⊆ sourceBall 0 R) :
    ∃ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ ∧
      tsupport φ ⊆ sourceBall x (2 * r) ∧
      (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧
      (∀ y ∈ sourceBall x r, φ y = 1) ∧
      ∀ (κ : ℝ), 0 < κ → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G → ∀ T : ℝ, 0 < T →
      let F : ℝ → ℝ := fun t => ∫ z in sourceBall 0 R,
        ρ z * ((∫ y in sourceBall 0 R, K t z y * φ y) - φ z)^2
      IntegrableOn F (Set.Ioo 0 T) ∧
        (∫ t in Set.Ioo 0 T, F t) ≤
          (κ⁻¹ * (1024 / r^2) * (volume (sourceBall x (2 * r))).toReal) * T^2 := by
  obtain ⟨φ, hφ, hsupp, hb, hp, htrace⟩ :=
    b_native_interior_cutoff_trace hR hr x hinside
  refine ⟨φ, hφ, hsupp, hb, hp, ?_⟩
  intro κ hκ ρ α hell K G hK T hT
  obtain ⟨s, hspec⟩ := hK.2
  let hpφ := c16_spatial_test_memLp_dirichlet hR hell φ hφ
  let H := Blueprint.TubeProbability.SpectralHeat.heatOperator
    (spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le)
  let F : ℝ → ℝ := fun t => ∫ z in sourceBall 0 R,
    ρ z * ((∫ y in sourceBall 0 R, K t z y * φ y) - φ z)^2
  let J : ℝ → ℝ := fun t => ‖H t.toNNReal (hpφ.toLp φ) - hpφ.toLp φ‖^2
  have hc : Continuous J := by
    exact ((((Blueprint.TubeProbability.SpectralHeat.heatOperator_continuous
      (spectralHeatBasis s) s.eigenvalue (fun n => (s.eigenvalue_pos n).le)
      (hpφ.toLp φ)).comp continuous_real_toNNReal).sub continuous_const).norm.pow 2)
  have heq : ∀ t ∈ Set.Ioo (0 : ℝ) T, F t = J t := by
    intro t ht
    let τ : ℝ≥0 := ⟨t, ht.1.le⟩
    let f := H τ (hpφ.toLp φ)
    have ha := b_supplied_spectral_cutoff_action hκ hR hell K s hspec φ hφ τ ht.1
    have hae : ((f - hpφ.toLp φ : Lp ℝ 2 (dirichletVolume ρ R)) : Vec d → ℝ) =ᵐ[dirichletVolume ρ R]
        fun z => (∫ y in sourceBall 0 R, K t z y * φ y) - φ z := by
      filter_upwards [Lp.coeFn_sub f (hpφ.toLp φ), ha, hpφ.coeFn_toLp] with z hz hz' hz''
      rw [hz]
      change f z - (hpφ.toLp φ) z = _
      rw [hz', hz'']
      rfl
    have hn := Blueprint.TubeProbability.DimensionLift.dirichletVolume_inner_eq_native
      hκ hell R (f - hpφ.toLp φ) (f - hpφ.toLp φ) _ _ hae hae
    rw [real_inner_self_eq_norm_sq] at hn
    have hn' : F t = ‖f - hpφ.toLp φ‖^2 := by
      rw [hn]
      apply integral_congr_ae
      exact ae_of_all _ fun _ => by ring
    have hτ : τ = t.toNNReal := by
      apply Subtype.ext
      simp [τ, Real.toNNReal_of_nonneg ht.1.le]
    change F t = ‖H t.toNNReal (hpφ.toLp φ) - hpφ.toLp φ‖^2
    rw [← hτ]
    exact hn'
  have heqae : F =ᵐ[volume.restrict (Set.Ioo (0 : ℝ) T)] J := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact heq t ht
  have hJ : IntegrableOn J (Set.Ioo (0 : ℝ) T) :=
    (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set Set.Ioo_subset_Icc_self
  have hF : IntegrableOn F (Set.Ioo (0 : ℝ) T) := hJ.congr heqae.symm
  refine ⟨hF, ?_⟩
  let E : ℝ := κ⁻¹ * (1024 / r^2) * (volume (sourceBall x (2 * r))).toReal
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have : IsFiniteMeasure (volume.restrict (Set.Ioo (0 : ℝ) T)) := ⟨by simp⟩
  have hbnd : ∀ᵐ t ∂volume.restrict (Set.Ioo (0 : ℝ) T), F t ≤ E * T := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    calc
      F t ≤ t * E := by
        simpa only [F, E, mul_assoc] using htrace κ hκ ρ α hell K G hK t ht.1
      _ ≤ E * T := by nlinarith [mul_nonneg hE (sub_nonneg.mpr ht.2.le)]
  calc
    (∫ t in Set.Ioo (0 : ℝ) T, F t) ≤ ∫ _t in Set.Ioo (0 : ℝ) T, E * T :=
      integral_mono_ae hF (integrable_const _) hbnd
    _ = E * T^2 := by simp [max_eq_left hT.le, pow_two]; ring


/-- A strictly larger source ball contains the closure of a source ball. -/
theorem b_sourceBall_closure_subset_larger {d : ℕ} (x : Vec d) {a b : ℝ}
    (hab : a < b) : closure (sourceBall x a) ⊆ sourceBall x b := by
  have hsum : Continuous (fun v : Vec d => ∑ j, v j * v j) :=
    continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
  have hn : Continuous (fun v : Vec d => euclideanNorm v) := by
    unfold euclideanNorm euclideanSq dot
    exact Real.continuous_sqrt.comp hsum
  have hc : IsClosed {v : Vec d | euclideanNorm (v - x) ≤ a} :=
    isClosed_le (hn.comp (continuous_id.sub continuous_const)) continuous_const
  have hs : sourceBall x a ⊆ {v : Vec d | euclideanNorm (v - x) ≤ a} := by
    intro v hv
    change euclideanNorm (v - x) < a at hv
    exact le_of_lt hv
  intro y hy
  have hy' := closure_minimal hs hc hy
  change euclideanNorm (y - x) < b
  exact lt_of_le_of_lt hy' hab

/-- The literal supplied spectral cutoff action agrees pointwise with the
cutoff action of the same kernel, including its density factor. -/
theorem b_supplied_spectral_cutoff_action_pointwise {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) ∧
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (φ : Vec d → ℝ) (t : ℝ) (ht : 0 < t)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) :
    (∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) =
      ∫ y in sourceBall 0 R, K t x y * φ y := by
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall (0 : Vec d) R :=
    (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_mem (dirichletBall (d := d) R).isOpen.measurableSet)
  rw [← b_native_weighted_cutoff_eq hκ hell K φ t x]
  apply integral_congr_ae
  filter_upwards [hball] with y hy
  rw [(hspec t ht x hx y hy).2]
  have hρ : ρ y ≠ 0 := ne_of_gt (hκ.trans_le (hell.2.2 y).1)
  field_simp
  simp only [mul_comm t (s.eigenvalue _)]
  ring

/-- A pointwise bound for the supplied spectral cutoff defect controls the
mass of the same kernel at that prescribed starting point. -/
theorem b_native_cutoff_defect_controls_prescribed_row {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) ∧
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφupper : ∀ y, φ y ≤ 1) (t : ℝ) (ht : 0 < t)
    (x : Vec d) (hx : x ∈ sourceBall 0 R) (ε : ℝ)
    (hdef : |(∫ y, (∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1| ≤ ε) :
    1 - ε ≤ ∫ y in sourceBall 0 R, K t x y := by
  have haction := b_supplied_spectral_cutoff_action_pointwise hκ hell K s hspec φ t ht x hx
  rw [haction] at hdef
  have hrow := b_native_cutoff_le_row_mass hd hκ hR hell K G hK φ hφ hφupper t ht x hx
  linarith [(abs_le.mp hdef).1]


/-- The raw weighted local maximum estimate gives a pointwise bound at positive
interior times when the actual caloric representative is continuous there. -/
theorem b_scaled_weighted_caloric_pointwise_max
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
    (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
    (y : Vec d) (r : ℝ) (hr : 0 < r)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-r^2) (r^2)) (sourceBall y r) u G)
    (hcont : ContinuousOn u (Set.Ioo (0 : ℝ) (r^2/4) ×ˢ sourceBall y (r/2))) :
    ∀ t ∈ Set.Ioo (0 : ℝ) (r^2/4), ∀ x ∈ sourceBall y (r/2),
      |u (t,x)| ≤ C * Real.sqrt
        ((r^(d+2))⁻¹ * ∫ z in Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r, |u z|^2) := by
  let U := Set.Ioo (0 : ℝ) (r^2/4) ×ˢ sourceBall y (r/2)
  let V := Set.Ioo (-(r^2)/4) (r^2/4) ×ˢ sourceBall y (r/2)
  have hUV : U ⊆ V := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    exact ⟨⟨by nlinarith [sq_pos_of_pos hr, ht.1], ht.2⟩, hx⟩
  have hmax := c17_scaled_local_max_of_unit_bound d hd κ C hκ hC (by simpa only [neg_div] using hunit)
    y r hr ρ α hell u G hcal
  have hB : 0 ≤ C * Real.sqrt
      ((r^(d+2))⁻¹ * ∫ z in Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r, |u z|^2) :=
    mul_nonneg hC.le (Real.sqrt_nonneg _)
  have hp := b_spacetime_abs_le_of_larger_essSup U V
    (isOpen_Ioo.prod (c17_isOpen_sourceBall y (r/2))) hUV u hcont _ hB hmax
  intro t ht x hx
  exact hp (t,x) ⟨ht,hx⟩


/-- The raw local maximum estimate and a local integral bound for the actual
cutoff defect imply the prescribed-point row bound on every parabolic scale.
The local defect estimate is an explicit input. -/
theorem b_scaled_native_prescribed_row_of_local_defect
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
    (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
    {R : ℝ} (hR : 0 < R) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) ∧
        K t x y = ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y)
    (y : Vec d) (r : ℝ) (hr : 0 < r)
    (φ : Vec d → ℝ) (hφ : IsSpatialTest (sourceBall 0 R) φ)
    (hφbounds : ∀ x, 0 ≤ φ x ∧ φ x ≤ 1)
    (hinside : closure (sourceBall y (2 * r)) ⊆ sourceBall 0 R)
    (hplateau : ∀ x ∈ sourceBall y (2 * r), φ x = 1)
    (hsmall : (r^(d+2))⁻¹ *
      (∫ z in Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r,
        |if 0 < z.1 then
          (∫ x, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
            s.eigenfunction n z.2 * s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1
          else 0| ^ 2) ≤ (1 / (2 * C)) ^ 2)
    (t : ℝ) (ht : 0 < t) (htsmall : t < r^2/4) :
    (1 / 2 : ℝ) ≤ ∫ x in sourceBall 0 R, K t y x := by
  let v : ℝ × Vec d → ℝ := fun z => if 0 < z.1 then
    (∫ x, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
      s.eigenfunction n z.2 * s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1
    else 0
  have hs := br06_native_spectral_eigenvalue_tendsto_atTop hd hκ hR hell s
  obtain ⟨H, hcal, hcont⟩ := b_native_cutoff_defect_caloric_continuous
    hd hκ hR hell s hs φ hφ hφbounds y r (r^2) hr (sq_pos_of_pos hr) hinside hplateau
  change IsWeightedCaloric ρ α (Set.Ioo (-r^2) (r^2)) (sourceBall y r) v H at hcal
  change ContinuousOn v (Set.Ioo (0 : ℝ) (r^2) ×ˢ sourceBall y r) at hcont
  have hcont' : ContinuousOn v (Set.Ioo (0 : ℝ) (r^2/4) ×ˢ sourceBall y (r/2)) :=
    hcont.mono (by
      rintro ⟨a,x⟩ ⟨ha,hx⟩
      refine ⟨⟨ha.1, by nlinarith [ha.2, sq_pos_of_pos hr]⟩, ?_⟩
      change euclideanNorm (x - y) < r/2 at hx
      change euclideanNorm (x - y) < r
      linarith)
  let I : ℝ := (r^(d+2))⁻¹ *
    ∫ z in Set.Ioo (-r^2) (r^2) ×ˢ sourceBall y r, |v z|^2
  have hI : 0 ≤ I := mul_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))
    (integral_nonneg fun z => sq_nonneg _)
  have hsmall' : I ≤ (1 / (2 * C)) ^ 2 := hsmall
  have hroot : Real.sqrt I ≤ 1 / (2 * C) := by
    have hsqrt := Real.sq_sqrt hI
    have hnonneg : 0 ≤ 1 / (2 * C) := by positivity
    nlinarith [Real.sqrt_nonneg I, sq_nonneg (Real.sqrt I + 1 / (2 * C))]
  have hp := b_scaled_weighted_caloric_pointwise_max d hd κ C hκ hC hunit
    y r hr ρ α hell v H hcal hcont'
  have hy : y ∈ sourceBall 0 R := by
    apply hinside
    apply subset_closure
    change euclideanNorm (y - y) < 2 * r
    simpa [euclideanNorm, euclideanSq, dot] using (mul_pos (by norm_num : (0 : ℝ) < 2) hr)
  have hy' : y ∈ sourceBall y (r/2) := by
    change euclideanNorm (y - y) < r/2
    simpa [euclideanNorm, euclideanSq, dot] using (half_pos hr)
  have hdef : |v (t,y)| ≤ 1 / 2 := by
    have hp' := hp t ⟨ht, htsmall⟩ y hy'
    have hm := mul_le_mul_of_nonneg_left hroot hC.le
    have hcancel : C * (1 / (2 * C)) = 1 / 2 := by field_simp
    linarith
  have hdef' : |(∫ x, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n y * s.eigenfunction n x) * φ x ∂dirichletVolume ρ R) - 1| ≤ 1/2 := by
    simpa only [v, if_pos ht] using hdef
  have hrow := b_native_cutoff_defect_controls_prescribed_row hd hκ hR hell K G hK s hspec
    φ hφ (fun x => (hφbounds x).2) t ht y hy (1/2) hdef'
  linarith


/-- A uniform local cutoff-defect estimate supplies the prescribed-start
survival reduction. The two remaining hypotheses are the raw unit weighted
local maximum estimate and the displayed estimate on the actual supplied
spectral cutoff defect. The time constant is chosen before the coefficients,
domain, center, and radius. -/
theorem b_uniform_prescribed_row_of_local_defect
    (d : ℕ) (hd : 2 ≤ d) (κ C : ℝ) (hκ : 0 < κ) (hC : 0 < C)
    (hunit : ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
      IsUniformlyElliptic κ ρ α →
      ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
      IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
      essSup (fun z => ENNReal.ofReal |u z|)
        (volume.restrict (Set.Ioo (-(1/4 : ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
      ENNReal.ofReal (C * Real.sqrt
        (∫ z in Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1, |u z|^2)))
    (hlocal : ∃ a : ℝ, 0 < a ∧ a < 1/2 ∧
      ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
        IsUniformlyElliptic κ ρ α →
      ∀ (s : DirichletSpectralResolution ρ α R) (x : Vec d) (r : ℝ), 0 < r →
        sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ φ : Vec d → ℝ, IsSpatialTest (sourceBall 0 R) φ →
        tsupport φ ⊆ sourceBall x (2*r) →
        (∀ z, 0 ≤ φ z ∧ φ z ≤ 1) →
        (∀ z ∈ sourceBall x r, φ z = 1) →
        (∀ z, euclideanSq (fun i => fderiv ℝ φ z (unitVector i)) ≤ 1024 / r^2) →
      ((a*r)^(d+2))⁻¹ *
        (∫ z in Set.Ioo (-(a*r)^2) ((a*r)^2) ×ˢ sourceBall x (a*r),
          |if 0 < z.1 then
            (∫ y, (∑' n, Real.exp (-s.eigenvalue n * z.1) *
              s.eigenfunction n z.2 * s.eigenfunction n y) * φ y ∂dirichletVolume ρ R) - 1
            else 0| ^ 2) ≤ (1 / (2*C))^2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (R : ℝ), 0 < R →
      ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
        IsSpectralDirichletFundamentalSolution ρ α R K G →
      ∀ (x : Vec d) (r : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      ∀ t : ℝ, 0 < t → t ≤ δ*r^2 →
        (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K t x y := by
  obtain ⟨a, ha, ha2, hlocal⟩ := hlocal
  refine ⟨a^2/8, by positivity, ?_⟩
  intro R hR ρ α hell K G hK x r hr hinside t ht htbound
  obtain ⟨φ, hφ, hsupp, hφbounds, hplateau, hgrad⟩ :=
    b_interior_ball_cutoff x hr hinside
  obtain ⟨s, hspec⟩ := hK.2
  have har : 0 < a*r := mul_pos ha hr
  have hsmallrad : 2 * (a*r) < r := by
    have h := mul_lt_mul_of_pos_right ha2 hr
    nlinarith
  have hinner := b_sourceBall_closure_subset_larger x hsmallrad
  have hball : sourceBall x r ⊆ sourceBall (0 : Vec d) R := by
    intro z hz
    apply hinside
    change euclideanNorm (z - x) < r at hz
    change euclideanNorm (z - x) < 2*r
    linarith
  have hclose : closure (sourceBall x (2*(a*r))) ⊆ sourceBall 0 R := hinner.trans hball
  have hplateau' : ∀ z ∈ sourceBall x (2*(a*r)), φ z = 1 := by
    intro z hz
    exact hplateau z (hinner (subset_closure hz))
  have htime : t < (a*r)^2/4 := by
    have hpos := mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr)
    nlinarith
  exact b_scaled_native_prescribed_row_of_local_defect d hd κ C hκ hC hunit hR hell
    K G hK s hspec x (a*r) har φ hφ hφbounds hclose hplateau'
    (hlocal R hR ρ α hell s x r hr hinside φ hφ hsupp hφbounds hplateau hgrad)
    t ht htime

end EinsteinFull.Calculus

