import EinsteinFull.Blueprint.Foundation.Proofs.SbxS2BoundaryContraction
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.SpatialWeakLocalization
import DGNMStatements.MoserHolder
import PDEFoundation.PDE.AffineChange
import PDEFoundation.PDE.DGNM.ScalingMeasure
import PDEFoundation.PDE.DGNM.ClassAlgebra
import PDEFoundation.Sobolev.Ch4.H10Truncation
import PDEFoundation.Sobolev.Ch4.H10Algebra
import PDEFoundation.Sobolev.H1.Mean
import PDEFoundation.Sobolev.H1.RepresentativeCongruence

/-! Common bounds for the weighted indicators used in the source-ball heat estimate. -/

open MeasureTheory PDE Filter EinsteinFull.External.Source.GMP
open EinsteinRelation SuperdiffusionCLT.Section7
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS2Boundary
open scoped ENNReal NNReal

namespace EinsteinFull.Blueprint.SbxS3UniformCrossHeat


/-- A pointwise density upper bound controls the actual weighted mass of a
measurable subset of the Dirichlet ball. -/
theorem dirichletVolume_real_upper {d : ℕ} (ρ : PDE.Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C : ℝ) (hC : 0 ≤ C)
    (hρ : ∀ x ∈ sourceBall (0 : PDE.Vec d) R, ρ x ≤ C)
    (A : Set (PDE.Vec d)) (hA : MeasurableSet A)
    (hsub : A ⊆ sourceBall (0 : PDE.Vec d) R) :
    (dirichletVolume ρ R).real A ≤ C * volume.real A := by
  have hs : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hmeasure : dirichletVolume ρ R ≤
      ENNReal.ofReal C • volume.restrict (sourceBall (0 : PDE.Vec d) R) := by
    rw [← withDensity_const]
    unfold dirichletVolume
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hρ x hx)
  have hfinite : (ENNReal.ofReal C • volume.restrict (sourceBall (0 : PDE.Vec d) R)) A ≠ ⊤ := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hA,
      Set.inter_eq_self_of_subset_left hsub]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ((measure_mono hsub).trans_lt (by
        rw [← pde_ball_eq_sourceBall _ hR]
        exact PDE.volume_euclideanBall_ne_top _ hR.le |>.lt_top)).ne
  have h := ENNReal.toReal_mono hfinite (hmeasure A)
  simpa only [Measure.real, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] using h

/-- Lower comparison of weighted and Euclidean mass on a measurable subset. -/
theorem dirichletVolume_real_lower {d : ℕ} (ρ : PDE.Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (C κ : ℝ) (hκ : 0 ≤ κ)
    (hupper : ∀ x ∈ sourceBall (0 : PDE.Vec d) R, ρ x ≤ C)
    (hlower : ∀ x ∈ sourceBall (0 : PDE.Vec d) R, κ ≤ ρ x)
    (A : Set (PDE.Vec d)) (hA : MeasurableSet A)
    (hsub : A ⊆ sourceBall (0 : PDE.Vec d) R) :
    κ * volume.real A ≤ (dirichletVolume ρ R).real A := by
  have hs : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hmeasure : ENNReal.ofReal κ • volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      dirichletVolume ρ R := by
    rw [← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hs] with x hx
    exact ENNReal.ofReal_le_ofReal (hlower x hx)
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR C hupper
  have h := ENNReal.toReal_mono (measure_ne_top (dirichletVolume ρ R) A) (hmeasure A)
  simpa only [Measure.real, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Set.inter_eq_self_of_subset_left hsub,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ] using h

/-- A native ground mode pairs with every measurable interior set. -/
theorem measurable_ground_indicator_pairing_lower {d : ℕ}
    {κ R r : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
    (hell : IsUniformlyElliptic κ ρ α)
    (g : Lp ℝ 2 (dirichletVolume ρ R)) (u : PDE.Vec d → ℝ)
    (hgu : (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u)
    (a : ℝ) (ha : 0 ≤ a)
    (hinner : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ u x)
    (A : Set (PDE.Vec d)) (hA : MeasurableSet A)
    (hsub : A ⊆ sourceBall (0 : PDE.Vec d) r)
    (hsubR : A ⊆ sourceBall (0 : PDE.Vec d) R) :
    a * (κ * volume.real A) ≤ ∫ x in A, g x ∂dirichletVolume ρ R := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hf : dirichletVolume ρ R A ≠ ∞ := measure_ne_top _ _
  have hlow : ∀ᵐ x ∂(dirichletVolume ρ R).restrict A, a ≤ g x :=
    dirichletVolume_restrict_ae_lower_of_native ρ R g u hgu _ a
      (ae_restrict_of_ae_restrict_of_subset hsub hinner)
  have hi := integral_mono_ae (integrableOn_const hf :
    IntegrableOn (fun _ : PDE.Vec d => a) A (dirichletVolume ρ R))
    (integrableOn_Lp_of_measure_ne_top g fact_one_le_two_ennreal.elim hf) hlow
  have hm : a * (dirichletVolume ρ R).real A ≤ ∫ x in A, g x ∂dirichletVolume ρ R := by
    simpa only [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ,
      mul_comm] using hi
  exact (mul_le_mul_of_nonneg_left
    (dirichletVolume_real_lower ρ R hR κ⁻¹ κ hκ.le
      (fun x _ => (hell.2.2 x).2.1) (fun x _ => (hell.2.2 x).1) A hA hsubR) ha).trans hm

#print axioms dirichletVolume_real_lower
#print axioms measurable_ground_indicator_pairing_lower

/-- Structural ground-mode bounds together with the complete actual minimum projection. -/
theorem exists_interior_ground_spectral_data {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E r a : ℝ, 0 < E ∧ 0 < r ∧ r < R ∧ 0 < a ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) (S : Finset ℕ),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
        a ≤ u.toH1Function.toFun x) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      Filter.Tendsto eigenvalue Filter.atTop Filter.atTop ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧ ‖g‖ = 1 ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g) := by
  obtain ⟨E, K, r, a, hE, hK, hr, hrR, ha, hex⟩ :=
    exists_sourceBall_first_eigenfunction_uniform_interior_lower hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, heig, heE, hu0, hnorm, henergy, hmin, hweak, hub, hlower⟩ := hex hell
  obtain ⟨eigenvalue, vs, j, δ, hδ, hp, hlim, ho, hs, hj, hgap, hvar⟩ :=
    exists_dirichletHilbert_spectral_minimum_and_gap hd hκ hell R hR
  let b := HilbertBasis.mk ho (le_of_eq hs.symm)
  have hb (n : ℕ) : b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (vs n) :=
    congrFun (HilbertBasis.coe_mk ho (le_of_eq hs.symm)) n
  have hvarb (n : ℕ) (w : DirichletHilbertSpace (d := d) R hR) :
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) w) := by
    rw [hb]
    exact hvar n w
  have hnorm' : (∫ x in sourceBall (0 : PDE.Vec d) R,
      ρ x * u.toH1Function.toFun x * u.toH1Function.toFun x) = 1 := by
    simpa only [weightedL2Pairing] using hnorm
  have hmin' : ∀ w : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R),
      eig * (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x) := by
    simpa only [weightedL2Pairing, dirichletEnergyPairing, PDE.vecDot,
      PDE.matVecMul, Matrix.mulVec, dotProduct, dot] using hmin
  obtain ⟨v, hv, ⟨n, hn⟩, hsupport⟩ :=
    native_weakEigenfunction_spectral_coordinate hd hκ hell R hR eigenvalue vs b hb hvarb
      u eig hweak hnorm'
  have hneig : eigenvalue n = eig := by
    by_contra hne
    exact hn (hsupport n hne)
  have heq : eigenvalue j = eig := le_antisymm ((hj n).trans_eq hneig)
    (native_rayleigh_lower_le_spectral_value hκ hell R hR eigenvalue vs b hb hvarb eig hmin' j)
  obtain ⟨S, hS, htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue
    (fun n => (hp n).le) hlim j δ hδ hgap
  have hSeig (n : ℕ) : n ∈ S ↔ eigenvalue n = eig := by
    simpa only [heq] using hS n
  obtain ⟨g, hgu, hgnorm, hproj⟩ := sourceBall_complete_minimum_projection_rank_one
    hd hκ hR ρ α hell eigenvalue vs b hb hvarb S eig heig.le hSeig u hweak hmin hnorm
  exact ⟨eig, u, eigenvalue, b, (fun n => (hp n).le), j, δ, g, S,
    heig, heE, heq, hδ, hnorm, hu0, hweak, hlower, hgap, hlim, hgu, hgnorm, hS, hproj⟩

#print axioms exists_interior_ground_spectral_data

/-- Indicator norms for arbitrary measurable subsets of one interior ball. -/
theorem measurable_indicator_norm_product_le {d : ℕ} (ρ : PDE.Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (K : ℝ) (hK : 0 ≤ K)
    (hρ : ∀ x ∈ sourceBall (0 : PDE.Vec d) R, ρ x ≤ K)
    (r : ℝ) (hr : 0 < r)
    (hsubR : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R)
    (A B : Set (PDE.Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hsubA : A ⊆ sourceBall (0 : PDE.Vec d) r)
    (hsubB : B ⊆ sourceBall (0 : PDE.Vec d) r) :
    letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR K hρ
    ‖indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)‖ *
      ‖indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ)‖ ≤
        K * volume.real (sourceBall (0 : PDE.Vec d) r) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR K hρ
  let V := K * volume.real (sourceBall (0 : PDE.Vec d) r)
  have hV : 0 ≤ V := by positivity
  have hrmeas : MeasurableSet (sourceBall (0 : PDE.Vec d) r) := by
    rw [← pde_ball_eq_sourceBall _ hr]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hball : (dirichletVolume ρ R).real (sourceBall (0 : PDE.Vec d) r) ≤ V :=
    dirichletVolume_real_upper ρ R hR K hK hρ _ hrmeas hsubR
  have hmass (S : Set (PDE.Vec d)) (hS : S ⊆ sourceBall (0 : PDE.Vec d) r) :
      (dirichletVolume ρ R).real S ≤ V := by
    exact (ENNReal.toReal_mono (measure_ne_top (dirichletVolume ρ R) _) (measure_mono hS)).trans hball
  have hnorm (S : Set (PDE.Vec d)) (hS : MeasurableSet S) :
      ‖indicatorConstLp 2 hS (measure_ne_top (dirichletVolume ρ R) S) (1 : ℝ)‖ =
        Real.sqrt ((dirichletVolume ρ R).real S) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  change ‖indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)‖ *
    ‖indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ)‖ ≤ V
  rw [hnorm A hA, hnorm B hB]
  calc
    _ ≤ Real.sqrt V * Real.sqrt V := mul_le_mul (Real.sqrt_le_sqrt (hmass A hsubA))
      (Real.sqrt_le_sqrt (hmass B hsubB)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = V := Real.mul_self_sqrt hV

#print axioms measurable_indicator_norm_product_le

/-- A common coefficient- and mass-floor-dependent time controls all measurable endpoints. -/
theorem exists_interior_measurable_cross_heat_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E r a M : ℝ, 0 < E ∧ 0 < r ∧ r < R ∧ 0 < a ∧ 0 ≤ M ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) (S : Finset ℕ),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ u.toH1Function.toFun x) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      Filter.Tendsto eigenvalue Filter.atTop Filter.atTop ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧ ‖g‖ = 1 ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g) ∧
      ∀ m₁ m₂ : ℝ, 0 < m₁ → 0 < m₂ → ∃ T : ℝ, 0 ≤ T ∧
      ∀ (A B : Set (PDE.Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B),
        A ⊆ sourceBall (0 : PDE.Vec d) r → B ⊆ sourceBall (0 : PDE.Vec d) r →
        m₁ ≤ volume.real A → m₂ ≤ volume.real B →
      letI : IsFiniteMeasure (dirichletVolume ρ R) :=
        dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      let f := indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)
      let k := indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ)
      ∀ t : ℝ≥0, T ≤ (t : ℝ) →
        Real.exp (-E * (t : ℝ)) * ((a * κ)^2 * m₁ * m₂ / 2) ≤
          inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t k) := by
  obtain ⟨E, r, a, hE, hr, hrR, ha, hex⟩ := exists_interior_ground_spectral_data hd hκ hR
  let M := κ⁻¹ * volume.real (sourceBall (0 : PDE.Vec d) r)
  have hM : 0 ≤ M := by positivity
  refine ⟨E, r, a, M, hE, hr, hrR, ha, hM, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, eigenvalue, b, hpos, j, δ, g, S, heig, heE, heq, hδ,
    hnorm, hu0, hweak, hlower, hgap, hlim, hgu, hgnorm, hS, hproj⟩ := hex hell
  refine ⟨eig, u, eigenvalue, b, hpos, j, δ, g, S, heig, heE, heq, hδ,
    hnorm, hu0, hweak, hlower, hgap, hlim, hgu, hgnorm, hS, hproj, ?_⟩
  intro m₁ m₂ hm₁ hm₂
  let C := (a * κ)^2 * m₁ * m₂
  have hC : 0 < C := by dsimp [C]; positivity
  let T := max 0 (Real.log (1 + 2 * M / C) / δ)
  refine ⟨T, le_max_left _ _, ?_⟩
  intro A B hA hB hsubA hsubB hmA hmB
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hsubR : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R := by
    rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) hr,
      ← pde_ball_eq_sourceBall (0 : PDE.Vec d) hR]
    exact PDE.euclideanBall_mono hr.le hrR.le
  have h₁ := measurable_ground_indicator_pairing_lower hκ hR ρ α hell g u.toH1Function.toFun
    hgu a ha.le hlower A hA hsubA (hsubA.trans hsubR)
  have h₂ := measurable_ground_indicator_pairing_lower hκ hR ρ α hell g u.toH1Function.toFun
    hgu a ha.le hlower B hB hsubB (hsubB.trans hsubR)
  have h₁' : a * (κ * m₁) ≤ ∫ x in A, g x ∂dirichletVolume ρ R :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmA hκ.le) ha.le).trans h₁
  have h₂' : a * (κ * m₂) ≤ ∫ x in B, g x ∂dirichletVolume ρ R :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmB hκ.le) ha.le).trans h₂
  have hc₁ : 0 ≤ a * (κ * m₁) := by positivity
  have hc₂ : 0 ≤ a * (κ * m₂) := by positivity
  have hc : C ≤ (∫ x in A, g x ∂dirichletVolume ρ R) *
      (∫ x in B, g x ∂dirichletVolume ρ R) := by
    convert mul_le_mul h₁' h₂' hc₂ (hc₁.trans h₁') using 1 <;> dsimp [C] <;> ring
  have hn := measurable_indicator_norm_product_le ρ R hR κ⁻¹ (inv_nonneg.mpr hκ.le)
    (fun x _ => (hell.2.2 x).2.1) r hr hsubR A B hA hB hsubA hsubB
  obtain ⟨S', hS', htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue hpos hlim j δ hδ hgap
  have hSS : S' = S := by
    ext n
    exact (hS' n).trans (hS n).symm
  subst S'
  dsimp only
  intro t ht
  have htail' := htail 0 t (indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ))
    (indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ))
  rw [SpectralHeat.heatOperator_zero, ContinuousLinearMap.id_apply,
    finite_projection_indicator_pairing (dirichletVolume ρ R) b S g hproj A B hA hB _ _] at htail'
  simp only [NNReal.coe_zero, zero_add, heq] at htail'
  exact exponential_tail_uniform_lower E eig δ C M heE hδ hC hM _ _ _ _ hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hn t.coe_nonneg
    (le_trans (le_max_right _ _) ht) htail'

#print axioms exists_interior_measurable_cross_heat_lower

/-- Both radius-`s` indicator norms are bounded by the same structural
weighted Euclidean volume, independently of their centers and coefficients. -/
theorem indicator_norm_product_le {d : ℕ} (ρ : PDE.Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (K : ℝ) (hK : 0 ≤ K)
    (hρ : ∀ x ∈ sourceBall (0 : PDE.Vec d) R, ρ x ≤ K)
    (s : ℝ) (hs : 0 < s) (c₁ c₂ : PDE.Vec d)
    (hsub₁ : sourceBall c₁ s ⊆ sourceBall (0 : PDE.Vec d) R)
    (hsub₂ : sourceBall c₂ s ⊆ sourceBall (0 : PDE.Vec d) R) :
    let hA : MeasurableSet (sourceBall c₁ s) := by
      rw [← pde_ball_eq_sourceBall c₁ hs]
      exact (PDE.isOpen_euclideanBall c₁ s).measurableSet
    let hB : MeasurableSet (sourceBall c₂ s) := by
      rw [← pde_ball_eq_sourceBall c₂ hs]
      exact (PDE.isOpen_euclideanBall c₂ s).measurableSet
    let : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR K hρ
    ‖indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)‖ *
      ‖indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)‖ ≤
        K * (s ^ d * volume.real (sourceBall (0 : PDE.Vec d) 1)) := by
  let A := sourceBall c₁ s
  let B := sourceBall c₂ s
  have hA : MeasurableSet A := by
    change MeasurableSet (sourceBall c₁ s)
    rw [← pde_ball_eq_sourceBall c₁ hs]
    exact (PDE.isOpen_euclideanBall c₁ s).measurableSet
  have hB : MeasurableSet B := by
    change MeasurableSet (sourceBall c₂ s)
    rw [← pde_ball_eq_sourceBall c₂ hs]
    exact (PDE.isOpen_euclideanBall c₂ s).measurableSet
  let : IsFiniteMeasure (dirichletVolume ρ R) := dirichletVolume_isFinite ρ R hR K hρ
  let V := K * (s ^ d * volume.real (sourceBall (0 : PDE.Vec d) 1))
  have hV : 0 ≤ V := by positivity
  have h₁ : (dirichletVolume ρ R).real A ≤ V := by
    have h := dirichletVolume_real_upper ρ R hR K hK hρ A hA hsub₁
    simpa only [V, A, sourceBall_volume_real_eq_unit_mul c₁ s hs] using h
  have h₂ : (dirichletVolume ρ R).real B ≤ V := by
    have h := dirichletVolume_real_upper ρ R hR K hK hρ B hB hsub₂
    simpa only [V, B, sourceBall_volume_real_eq_unit_mul c₂ s hs] using h
  have hnorm (S : Set (PDE.Vec d)) (hS : MeasurableSet S) :
      ‖indicatorConstLp 2 hS (measure_ne_top (dirichletVolume ρ R) S) (1 : ℝ)‖ =
        Real.sqrt ((dirichletVolume ρ R).real S) := by
    rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
    simp only [norm_one, one_mul, ENNReal.toReal_ofNat, ← Real.sqrt_eq_rpow]
  change ‖indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) A) (1 : ℝ)‖ *
    ‖indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) B) (1 : ℝ)‖ ≤ V
  rw [hnorm A hA, hnorm B hB]
  calc
    _ ≤ Real.sqrt V * Real.sqrt V := mul_le_mul (Real.sqrt_le_sqrt h₁)
      (Real.sqrt_le_sqrt h₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = V := Real.mul_self_sqrt hV

/-- A coefficient-dependent spectral gap yields one time threshold that works
for every pair of balls of the same structural radius. -/
theorem exists_common_radius_cross_heat_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ (E r s : ℝ) (hs : 0 < s) (C M : ℝ), 0 < E ∧ 0 < r ∧ r < R ∧
      0 < C ∧ 0 ≤ M ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧ 0 ≤ T ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧ ‖g‖ = 1 ∧
      ∀ (c₁ c₂ : PDE.Vec d),
        sourceBall c₁ s ⊆ sourceBall (0 : PDE.Vec d) r →
        sourceBall c₂ s ⊆ sourceBall (0 : PDE.Vec d) r →
      let hA : MeasurableSet (sourceBall c₁ s) := by
        rw [← pde_ball_eq_sourceBall c₁ hs]
        exact (PDE.isOpen_euclideanBall c₁ s).measurableSet
      let hB : MeasurableSet (sourceBall c₂ s) := by
        rw [← pde_ball_eq_sourceBall c₂ hs]
        exact (PDE.isOpen_euclideanBall c₂ s).measurableSet
      let : IsFiniteMeasure (dirichletVolume ρ R) :=
        dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      let f := indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
      let k := indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
      ∀ t : ℝ≥0, T ≤ (t : ℝ) →
        Real.exp (-E * (t : ℝ)) * (C / 2) ≤
          inner ℝ f (SpectralHeat.heatOperator b eigenvalue hpos t k) := by
  obtain ⟨E, r, a, hE, hr, hrR, ha, hex⟩ :=
    SbxS2Boundary.exists_sourceBall_cross_heat_lower hd hκ hR
  let s := r / 4
  have hs : 0 < s := by dsimp [s]; positivity
  let V := s ^ d * volume.real (sourceBall (0 : PDE.Vec d) 1)
  have hv : 0 < V := by
    have hunit : 0 < volume.real (sourceBall (0 : PDE.Vec d) 1) := by
      rw [← pde_ball_eq_sourceBall (0 : PDE.Vec d) (by norm_num)]
      exact PDE.volume_euclideanBall_toReal_pos _ (by norm_num)
    dsimp [V]; positivity
  let C := (a * (κ * V)) ^ 2
  let M := κ⁻¹ * V
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨E, r, s, hs, C, M, hE, hr, hrR, hC, hM, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, eigenvalue, b, hpos, j, δ, g, heig, heE, hej, hδ,
    hnorm, hu0, hweak, hlower, hgap, hgu, hgnorm, hcross⟩ := hex hell
  let T := max 0 (Real.log (1 + 2 * M / C) / δ)
  refine ⟨eig, u, eigenvalue, b, hpos, j, δ, g, T, heig, heE, hej, hδ,
    le_max_left _ _, hnorm, hu0, hweak, hgap, hgu, hgnorm, ?_⟩
  intro c₁ c₂ hsub₁ hsub₂
  let : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hsubR : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall (0 : PDE.Vec d) R := by
    intro x hx
    exact lt_trans hx hrR
  have hn := indicator_norm_product_le ρ R hR κ⁻¹ (inv_nonneg.mpr hκ.le)
    (fun x _ => (hell.2.2 x).2.1) s hs c₁ c₂ (hsub₁.trans hsubR) (hsub₂.trans hsubR)
  have hc := hcross c₁ c₂ s s hs hs hsub₁ hsub₂
  dsimp only at hc ⊢ hn
  have hvol₁ := sourceBall_volume_real_eq_unit_mul c₁ s hs
  have hvol₂ := sourceBall_volume_real_eq_unit_mul c₂ s hs
  rw [hvol₁, hvol₂] at hc
  intro t ht
  apply SbxS2Boundary.exponential_tail_uniform_lower E eig δ C M heE hδ hC hM
    _ _ (t : ℝ) _ ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
    t.coe_nonneg (le_trans (le_max_right _ _) ht) (hc.2.2.1 t)
  · simpa only [C, V, pow_two] using hc.2.1
  · simpa only [M, V] using hn

/-- Two-time and window bounds for the same coefficient-dependent spectral basis. -/
theorem exists_common_radius_two_time_window_cross_heat_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ (E r s : ℝ) (hs : 0 < s) (C M : ℝ), 0 < E ∧ 0 < r ∧ r < R ∧
      0 < C ∧ 0 ≤ M ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) (T : ℝ),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧ 0 ≤ T ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧ ‖g‖ = 1 ∧
      ∀ (L : ℝ), 0 ≤ L → ∀ (c₁ c₂ : PDE.Vec d),
        sourceBall c₁ s ⊆ sourceBall (0 : PDE.Vec d) r →
        sourceBall c₂ s ⊆ sourceBall (0 : PDE.Vec d) r →
      let hA : MeasurableSet (sourceBall c₁ s) := by
        rw [← pde_ball_eq_sourceBall c₁ hs]
        exact (PDE.isOpen_euclideanBall c₁ s).measurableSet
      let hB : MeasurableSet (sourceBall c₂ s) := by
        rw [← pde_ball_eq_sourceBall c₂ hs]
        exact (PDE.isOpen_euclideanBall c₂ s).measurableSet
      let : IsFiniteMeasure (dirichletVolume ρ R) :=
        dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
      let f := indicatorConstLp 2 hA (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
      let k := indicatorConstLp 2 hB (measure_ne_top (dirichletVolume ρ R) _) (1 : ℝ)
      ∀ p q : ℝ≥0, T ≤ ((p + q : ℝ≥0) : ℝ) →
        Real.exp (-E * ((p + q : ℝ≥0) : ℝ)) * (C / 2) ≤
          inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos p f)
            (SpectralHeat.heatOperator b eigenvalue hpos q k) ∧
        (((p + q : ℝ≥0) : ℝ) ≤ T + L →
          Real.exp (-E * (T + L)) * (C / 2) ≤
            inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos p f)
              (SpectralHeat.heatOperator b eigenvalue hpos q k)) := by
  obtain ⟨E, r, s, hs, C, M, hE, hr, hrR, hC, hM, hex⟩ :=
    exists_common_radius_cross_heat_lower hd hκ hR
  refine ⟨E, r, s, hs, C, M, hE, hr, hrR, hC, hM, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, eigenvalue, b, hpos, j, δ, g, T, heig, heE, hej, hδ,
    hT, hnorm, hu0, hweak, hgap, hgu, hgnorm, hcross⟩ := hex hell
  refine ⟨eig, u, eigenvalue, b, hpos, j, δ, g, T, heig, heE, hej, hδ,
    hT, hnorm, hu0, hweak, hgap, hgu, hgnorm, ?_⟩
  intro L hL c₁ c₂ hsub₁ hsub₂
  have hc := hcross c₁ c₂ hsub₁ hsub₂
  dsimp only at hc ⊢
  intro p q hpq
  have h := hc (p + q) hpq
  rw [SpectralHeat.heatOperator_add, ContinuousLinearMap.comp_apply,
    ← SpectralHeat.heatOperator_symmetric] at h
  refine ⟨h, ?_⟩
  intro hwindow
  apply le_trans _ h
  apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ C / 2)
  apply Real.exp_le_exp.mpr
  nlinarith

#print axioms exists_common_radius_two_time_window_cross_heat_lower
#print axioms exists_common_radius_cross_heat_lower
#print axioms indicator_norm_product_le
#print axioms dirichletVolume_real_upper

/-- The ground lower bound controls the pairing with any supported positive L² test. -/
theorem weighted_test_ground_pairing_lower {d : ℕ} {R r : ℝ}
    (ρ : PDE.Vec d → ℝ) (g f : Lp ℝ 2 (dirichletVolume ρ R))
    [IsFiniteMeasure (dirichletVolume ρ R)] (a : ℝ)
    (hr : 0 < r) (hground : ∀ᵐ x ∂(dirichletVolume ρ R).restrict
      (sourceBall (0 : PDE.Vec d) r), a ≤ g x)
    (hf : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x)
    (hsupp : ∀ᵐ x ∂dirichletVolume ρ R,
      x ∉ sourceBall (0 : PDE.Vec d) r → f x = 0) :
    a * (∫ x, f x ∂dirichletVolume ρ R) ≤ inner ℝ f g := by
  have hs : MeasurableSet (sourceBall (0 : PDE.Vec d) r) := by
    rw [← pde_ball_eq_sourceBall _ hr]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hg := (ae_restrict_iff' hs).1 hground
  have hi := integral_mono_ae ((Lp.memLp f).integrable (by norm_num) |>.const_mul a)
    ((Lp.memLp f).integrable_mul (Lp.memLp g)) (by
      filter_upwards [hf, hsupp, hg] with x hx hxs hxg
      by_cases h : x ∈ sourceBall (0 : PDE.Vec d) r
      · simpa only [Pi.mul_apply, mul_comm] using mul_le_mul_of_nonneg_left (hxg h) hx
      · simp [hxs h])
  rw [integral_const_mul] at hi
  rw [L2.inner_def]
  simpa only [RCLike.inner_apply, conj_trivial, Pi.mul_apply, mul_comm] using hi

#print axioms weighted_test_ground_pairing_lower

/-- Positive L² tests with fixed mass floors and norm bounds share a two-time
spectral lower bound, on the actual coefficient-dependent eigenbasis. -/
theorem exists_interior_positive_test_cross_heat_lower {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E r a : ℝ, 0 < E ∧ 0 < r ∧ r < R ∧ 0 < a ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
      ∀ hell : IsUniformlyElliptic κ ρ α,
      ∃ (eig : ℝ) (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
        (eigenvalue : ℕ → ℝ) (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
        (hpos : ∀ n, 0 ≤ eigenvalue n) (j : ℕ) (δ : ℝ)
        (g : Lp ℝ 2 (dirichletVolume ρ R)) (S : Finset ℕ),
      0 < eig ∧ eig ≤ E ∧ eigenvalue j = eig ∧ 0 < δ ∧
      weightedL2Pairing ρ u.toH1Function u.toH1Function = 1 ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      IsWeakSolutionOn α (sourceBall 0 R) u.toH1Function
        (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0) ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ u.toH1Function.toFun x) ∧
      (∀ n, eigenvalue n = eigenvalue j ∨ eigenvalue j + δ ≤ eigenvalue n) ∧
      Filter.Tendsto eigenvalue Filter.atTop Filter.atTop ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧ ‖g‖ = 1 ∧
      (∀ n, n ∈ S ↔ eigenvalue n = eigenvalue j) ∧
      (∀ f, (∑ n ∈ S, b.repr f n • b n) = inner ℝ f g • g) ∧
      ∀ m₁ m₂ N₁ N₂ : ℝ, 0 < m₁ → 0 < m₂ → 0 ≤ N₁ → 0 ≤ N₂ →
      ∃ T : ℝ, 0 ≤ T ∧ ∀ f k : Lp ℝ 2 (dirichletVolume ρ R),
        (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
        (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ k x) →
        (∀ᵐ x ∂dirichletVolume ρ R, x ∉ sourceBall (0 : PDE.Vec d) r → f x = 0) →
        (∀ᵐ x ∂dirichletVolume ρ R, x ∉ sourceBall (0 : PDE.Vec d) r → k x = 0) →
        m₁ ≤ (∫ x, f x ∂dirichletVolume ρ R) →
        m₂ ≤ (∫ x, k x ∂dirichletVolume ρ R) →
        ‖f‖ ≤ N₁ → ‖k‖ ≤ N₂ → ∀ p q : ℝ≥0, T ≤ (p : ℝ) + q →
        Real.exp (-E * ((p : ℝ) + q)) * (a^2 * m₁ * m₂ / 2) ≤
          inner ℝ (SpectralHeat.heatOperator b eigenvalue hpos p f)
            (SpectralHeat.heatOperator b eigenvalue hpos q k) := by
  obtain ⟨E, r, a, hE, hr, hrR, ha, hex⟩ := exists_interior_ground_spectral_data hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell
  obtain ⟨eig, u, eigenvalue, b, hpos, j, δ, g, S, heig, heE, heq, hδ,
    hnorm, hu0, hweak, hlower, hgap, hlim, hgu, hgnorm, hS, hproj⟩ := hex hell
  refine ⟨eig, u, eigenvalue, b, hpos, j, δ, g, S, heig, heE, heq, hδ,
    hnorm, hu0, hweak, hlower, hgap, hlim, hgu, hgnorm, hS, hproj, ?_⟩
  intro m₁ m₂ N₁ N₂ hm₁ hm₂ hN₁ hN₂
  let C := a^2 * m₁ * m₂
  let M := N₁ * N₂
  have hC : 0 < C := by dsimp [C]; positivity
  have hM : 0 ≤ M := mul_nonneg hN₁ hN₂
  let T := max 0 (Real.log (1 + 2 * M / C) / δ)
  refine ⟨T, le_max_left _ _, ?_⟩
  intro f k hf hk hfs hks hmf hmk hnf hnk p q ht
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  have hg := dirichletVolume_restrict_ae_lower_of_native ρ R g u.toH1Function.toFun hgu _ a hlower
  have hfg := weighted_test_ground_pairing_lower ρ g f a hr hg hf hfs
  have hkg := weighted_test_ground_pairing_lower ρ g k a hr hg hk hks
  have hf' : a * m₁ ≤ inner ℝ f g := (mul_le_mul_of_nonneg_left hmf ha.le).trans hfg
  have hk' : a * m₂ ≤ inner ℝ k g := (mul_le_mul_of_nonneg_left hmk ha.le).trans hkg
  have hc : C ≤ inner ℝ f g * inner ℝ k g := by
    convert mul_le_mul hf' hk' (by positivity) ((by positivity : 0 ≤ a * m₁).trans hf') using 1 <;> dsimp [C] <;> ring
  have hn : ‖f‖ * ‖k‖ ≤ M := mul_le_mul hnf hnk (norm_nonneg _) hN₁
  obtain ⟨S', hS', htail⟩ := heat_two_times_lowest_eigenspace_tail b eigenvalue hpos hlim j δ hδ hgap
  have hSS : S' = S := by
    ext n
    exact (hS' n).trans (hS n).symm
  subst S'
  have ht' := htail p q f k
  rw [lowest_eigenspace_coefficient_eq_projection, hproj k] at ht'
  simp only [real_inner_smul_right, smul_eq_mul, heq] at ht'
  exact exponential_tail_uniform_lower E eig δ C M heE hδ hC hM _ _ _ _ hc
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hn (add_nonneg p.coe_nonneg q.coe_nonneg)
    (le_trans (le_max_right _ _) ht) (by simpa only [mul_comm] using ht')

#print axioms exists_interior_positive_test_cross_heat_lower

/-- The proved Moser theorem gives a continuous representative of the actual
normalized exponential lift on the half unit ball. -/
theorem coordinate_lift_continuousOn_half_unit_ball {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {U : Set (PDE.Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : PDE.Vec d → ℝ} {g : PDE.Vec d → PDE.Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : PDE.Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K)
    (hsub : PDE.euclideanBall (0 : PDE.Vec (d + 1)) 1 ⊆
      productCoordinates ⁻¹' (U ×ˢ K)) :
    ∃ v : PDE.Vec (d + 1) → ℝ,
      ContinuousOn v (PDE.euclideanBall (0 : PDE.Vec (d + 1)) (1 / 2)) ∧
      v =ᵐ[volume.restrict (PDE.euclideanBall (0 : PDE.Vec (d + 1)) (1 / 2))]
        liftedValue u (Real.sqrt eigenvalue) := by
  have hΛ : 1 ≤ (κ ^ 4)⁻¹ := by
    exact (one_le_inv₀ (pow_pos hκ 4)).2
      (pow_le_one₀ hκ.le (lifted_ellipticity_scale_comparison hκ h).1)
  obtain ⟨C, hC, hmoser⟩ := PDE.exists_moser_holder_constant (d + 1) (by omega)
  obtain ⟨β, hβ, hβ1, hmoserβ⟩ := hmoser _ hΛ
  let w := pdeH1OfNative ((coordinateLiftH1 hU hUfinite hu hg hw
    (Real.sqrt eigenvalue) hK).restrict (PDE.isOpen_euclideanBall _ _) hsub)
  have hsol := pde_coordinate_lift_solution hκ h hU hUfinite hu hg hw
    eigenvalue heigenvalue hweak hK (PDE.isOpen_euclideanBall _ _) hsub
  obtain ⟨v, M₀, M₁, hv, hM₀, hM₁, hb, hholder, hbound⟩ :=
    hmoserβ (normalizedCoordinateLiftedMatrix κ ρ α)
      (fun i j => (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable)
      (fun z _ => normalizedCoordinateLiftedMatrix_elliptic hκ h z)
      w hsol 2 (by norm_num)
  refine ⟨v, hholder.continuousOn ((Real.exp_pos _).trans_le hβ) hM₁, ?_⟩
  exact hv

#print axioms coordinate_lift_continuousOn_half_unit_ball

open scoped Pointwise

/-- Moser's unit-ball theorem transported to a ball of any positive radius. -/
theorem pde_continuousOn_half_ball_of_homogeneous {n : ℕ} (hn : 3 ≤ n)
    {Λ R : ℝ} (hΛ : 1 ≤ Λ) (hR : 0 < R) (z : PDE.Vec n)
    (a : PDE.CoeffField n) (ha : ∀ i j, Measurable (fun x => a x i j))
    (hell : ∀ x ∈ PDE.euclideanBall z R, PDE.IsEllipticMatrix 1 Λ (a x))
    (u : PDE.H1Function (PDE.euclideanBall z R))
    (hsol : PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall z R) u 0 0) :
    ∃ v : PDE.Vec n → ℝ, ContinuousOn v (PDE.euclideanBall z (R / 2)) ∧
      v =ᵐ[volume.restrict (PDE.euclideanBall z (R / 2))] u.toFun := by
  open PDE in
  let BR := euclideanBall (0 : PDE.Vec n) R
  open PDE in
  have htranslate : translateSet (-z) (euclideanBall z R) = BR := by
    ext x
    rw [mem_translateSet_iff_sub_mem]
    simp only [sub_neg_eq_add]
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
      mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simp [sub_eq_add_neg, add_assoc]
  open PDE in
  let uraw := u.translate (-z)
  open PDE in
  let uR : H1Function BR := uraw.restrict (isOpen_euclideanBall _ _)
    (htranslate ▸ Set.Subset.rfl)
  open PDE in
  let aR : CoeffField n := fun x => a (x + z)
  open PDE in
  have hsolR : IsWeakDivergenceFormSolutionOn aR BR uR 0 0 := by
    have hsolraw := hsol.translate (-z)
    have hopenraw : IsOpen (translateSet (-z) (euclideanBall z R)) := by
      rw [htranslate]
      exact isOpen_euclideanBall _ _
    simpa only [aR, uR, uraw, sub_neg_eq_add, Pi.zero_apply] using!
      hsolraw.restrict hopenraw (isOpen_euclideanBall _ _) (htranslate ▸ Set.Subset.rfl)
  open PDE in
  have hscale : R⁻¹ • BR = euclideanBall (0 : PDE.Vec n) 1 := by
    dsimp only [BR]
    rw [euclideanBall_eq_translateSet_smul_unit_of_pos (0 : PDE.Vec n) hR]
    simp only [translateSet_zero, smul_smul]
    rw [inv_mul_cancel₀ hR.ne', one_smul]
  open PDE in
  let usraw := uR.dilate (inv_pos.mpr hR)
  open PDE in
  have hunitSub : euclideanBall (0 : PDE.Vec n) 1 ⊆ R⁻¹ • BR := by rw [hscale]
  open PDE in
  let u0 : H1Function (euclideanBall (0 : PDE.Vec n) 1) :=
    usraw.restrict (isOpen_euclideanBall _ _) hunitSub
  open PDE in
  let a0 : CoeffField n := fun x => aR (R • x)
  open PDE in
  have hsol0 : IsWeakDivergenceFormSolutionOn a0 (euclideanBall (0 : PDE.Vec n) 1)
      u0 0 0 := by
    have hs := hsolR.dilate_of_pos (inv_pos.mpr hR)
    have ho : IsOpen (R⁻¹ • BR) := by rw [hscale]; exact isOpen_euclideanBall _ _
    have hs' := hs.restrict ho (isOpen_euclideanBall _ _) hunitSub
    simpa only [a0, u0, usraw, inv_inv, Pi.zero_apply, mul_zero,
      inv_mul_cancel₀ hR.ne', one_mul, smul_eq_mul] using! hs'
  open PDE in
  have hell0 : ∀ x ∈ euclideanBall (0 : PDE.Vec n) 1, IsEllipticMatrix 1 Λ (a0 x) := by
    intro x hx
    apply hell
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    simpa [a0, aR, vecEuclideanNorm_smul, abs_of_pos hR, sub_eq_add_neg,
      add_assoc] using (mul_lt_mul_of_pos_left hx' hR)
  obtain ⟨C, hC, hmoser⟩ := PDE.exists_moser_holder_constant n hn
  obtain ⟨β, hβ, hβ1, hmoserβ⟩ := hmoser Λ hΛ
  have ha0 : ∀ i j, AEMeasurable (fun x => a0 x i j)
      (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1)) := by
    intro i j
    have hc : Continuous (fun x : PDE.Vec n => R • x + z) := by fun_prop
    exact ((ha i j).comp hc.measurable).aemeasurable
  obtain ⟨v, M₀, M₁, hv, hM₀, hM₁, hb, hholder, hbound⟩ :=
    hmoserβ a0 ha0 hell0 u0 hsol0 2 (by norm_num)
  let V : PDE.Vec n → ℝ := fun x => R * v (R⁻¹ • (x - z))
  have hmap : Set.MapsTo (fun x : PDE.Vec n => R⁻¹ • (x - z))
      (PDE.euclideanBall z (R / 2)) (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)) := by
    intro x hx
    apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < R / 2)).1 hx
    have ht : PDE.vecEuclideanNorm (x - z) / R < 1 / 2 :=
      (div_lt_iff₀ hR).2 (by linarith)
    simpa [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      inv_mul_eq_div] using ht
  have hc : Continuous (fun x : PDE.Vec n => R⁻¹ • (x - z)) := by fun_prop
  refine ⟨V, ((hholder.continuousOn ((Real.exp_pos _).trans_le hβ) hM₁).comp
    hc.continuousOn hmap).const_mul R, ?_⟩
  have hunit : ∀ᵐ y ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)),
      V (R • y + z) = u.toFun (R • y + z) := by
    filter_upwards [hv] with y hy
    have hy' := congrArg (fun t : ℝ => R * t) hy
    simpa [V, u0, usraw, uR, uraw, PDE.H1Function.restrict_toFun,
      PDE.H1Function.dilate_toFun, PDE.H1Function.translate_toFun, hR.ne',
      smul_smul, mul_assoc] using hy'
  have h := (PDE.DGNM.ae_comp_affineScale_ball_iff z hR (1 / 2)
    (P := fun x => V x = u.toFun x)).mp hunit
  change ∀ᵐ x ∂PDE.volumeOn (PDE.euclideanBall z (R / 2)), V x = u.toFun x
  rw [show R / 2 = R * (1 / 2) by ring]
  exact h

#print axioms pde_continuousOn_half_ball_of_homogeneous

/-- The actual normalized exponential lift has a continuous representative on
any half ball whose full ball lies inside the lift cylinder. -/
theorem coordinate_lift_continuousOn_half_ball {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {U : Set (PDE.Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : PDE.Vec d → ℝ} {g : PDE.Vec d → PDE.Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : PDE.Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) (z : PDE.Vec (d + 1)) {R : ℝ} (hR : 0 < R)
    (hsub : PDE.euclideanBall z R ⊆ productCoordinates ⁻¹' (U ×ˢ K)) :
    ∃ v : PDE.Vec (d + 1) → ℝ,
      ContinuousOn v (PDE.euclideanBall z (R / 2)) ∧
      v =ᵐ[volume.restrict (PDE.euclideanBall z (R / 2))]
        liftedValue u (Real.sqrt eigenvalue) := by
  have hΛ : 1 ≤ (κ ^ 4)⁻¹ := by
    exact (one_le_inv₀ (pow_pos hκ 4)).2
      (pow_le_one₀ hκ.le (lifted_ellipticity_scale_comparison hκ h).1)
  let w := pdeH1OfNative ((coordinateLiftH1 hU hUfinite hu hg hw
    (Real.sqrt eigenvalue) hK).restrict (PDE.isOpen_euclideanBall _ _) hsub)
  have hsol := pde_coordinate_lift_solution hκ h hU hUfinite hu hg hw
    eigenvalue heigenvalue hweak hK (PDE.isOpen_euclideanBall _ _) hsub
  obtain ⟨v, hv, hae⟩ := pde_continuousOn_half_ball_of_homogeneous (by omega)
    hΛ hR z (normalizedCoordinateLiftedMatrix κ ρ α)
    (normalizedCoordinateLiftedMatrix_measurable h)
    (fun x _ => normalizedCoordinateLiftedMatrix_elliptic hκ h x) w hsol
  exact ⟨v, hv, hae⟩

#print axioms coordinate_lift_continuousOn_half_ball

/-- A continuous representative on a coordinate cylinder descends by
transverse averaging, preserving the spatial almost-everywhere identity. -/
theorem coordinate_lift_continuousOn_descent {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : MeasurableSet U) {r : ℝ} (hr : 0 < r)
    {v : PDE.Vec (d + 1) → ℝ} {u : PDE.Vec d → ℝ}
    (hv : ContinuousOn v (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r))) (c : ℝ)
    (heq : v =ᵐ[volume.restrict (productCoordinates ⁻¹' (U ×ˢ Set.Icc (-r) r))]
      liftedValue u c) :
    ∃ w : PDE.Vec d → ℝ, ContinuousOn w U ∧ w =ᵐ[volume.restrict U] u := by
  have hvc : ContinuousOn (fun p : PDE.Vec d × ℝ => v (productCoordinates.symm p))
      (U ×ˢ Set.Icc (-r) r) :=
    hv.comp (productCoordinates (d := d)).symm.continuous.continuousOn
      (fun p hp => by simpa only [Set.mem_preimage,
        ContinuousLinearEquiv.apply_symm_apply] using hp)
  have hae : (fun p : PDE.Vec d × ℝ => v (productCoordinates.symm p))
      =ᵐ[(volume.restrict U).prod (volume.restrict (Set.Icc (-r) r))]
        (fun p => u p.1 * Real.exp (c * p.2)) := by
    simpa only [Function.comp_def, liftedValue, ContinuousLinearEquiv.apply_symm_apply]
      using (productCoordinates_symm_measurePreserving_cylinder hU measurableSet_Icc).quasiMeasurePreserving.ae_eq_comp heq
  exact exists_continuousOn_ae_eq_of_lift (by linarith : -r ≤ r) hvc c hae
    (continuous_transverseTent r) (hasCompactSupport_transverseTent r)
    (tsupport_transverseTent_subset r) (transverseTent_nonneg r)
    (ne_of_gt (transverseTent_zero_pos hr))

#print axioms coordinate_lift_continuousOn_descent

/-- The local averaging cylinder lies in the lifted Euclidean half ball. -/
theorem coordinate_cylinder_subset_half_ball {d : ℕ} (x₀ : PDE.Vec d)
    {R : ℝ} (hR : 0 < R) :
    productCoordinates ⁻¹' (PDE.euclideanBall x₀ (R / 4) ×ˢ
      Set.Icc (-(R / 4)) (R / 4)) ⊆
      PDE.euclideanBall (productCoordinates.symm (x₀, 0)) (R / 2) := by
  intro x hx
  have hc := euclidean_cylinder_subset_half_ball x₀ hR
    (show (euclideanCoordinates (d + 1)).symm x ∈
      euclideanCoordinates (d + 1) ⁻¹' (productCoordinates ⁻¹'
        ({y : PDE.Vec d | euclideanNorm (y - x₀) < R / 4} ×ˢ
          Set.Icc (-(R / 4)) (R / 4))) by
      simp only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply]
      change (productCoordinates x).1 ∈ {y : PDE.Vec d | euclideanNorm (y - x₀) < R / 4} ∧ _
      exact ⟨(PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hx.1, hx.2⟩)
  rw [Metric.mem_ball, dist_eq_norm, norm_euclideanCoordinates_symm_sub] at hc
  exact (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2 hc

#print axioms coordinate_cylinder_subset_half_ball

/-- Local spatial continuity follows from the actual lifted weak eigenmode. -/
theorem coordinate_lift_continuousOn_spatial_ball {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {U : Set (PDE.Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    {u : PDE.Vec d → ℝ} {g : PDE.Vec d → PDE.Vec d}
    (hu : MemLp u 2 (volume.restrict U))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict U))
    (hw : HasWeakGradient U u g) (eigenvalue : ℝ) (heigenvalue : 0 ≤ eigenvalue)
    (hweak : ∀ ψ : PDE.Vec d → ℝ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eigenvalue * ∫ x in U, (ρ x * u x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) (x₀ : PDE.Vec d) {R : ℝ} (hR : 0 < R)
    (hsub : PDE.euclideanBall (productCoordinates.symm (x₀, 0)) R ⊆
      productCoordinates ⁻¹' (U ×ˢ K)) :
    ∃ w : PDE.Vec d → ℝ, ContinuousOn w (PDE.euclideanBall x₀ (R / 4)) ∧
      w =ᵐ[volume.restrict (PDE.euclideanBall x₀ (R / 4))] u := by
  obtain ⟨v, hv, heq⟩ := coordinate_lift_continuousOn_half_ball hd hκ h hU hUfinite
    hu hg hw eigenvalue heigenvalue hweak hK (productCoordinates.symm (x₀, 0)) hR hsub
  have hc := coordinate_cylinder_subset_half_ball x₀ hR
  exact coordinate_lift_continuousOn_descent (PDE.isOpen_euclideanBall _ _).measurableSet
    (by positivity : 0 < R / 4) (hv.mono hc) (Real.sqrt eigenvalue)
    (ae_restrict_of_ae_restrict_of_subset hc heq)

#print axioms coordinate_lift_continuousOn_spatial_ball

/-- Every weak eigenmode on a source ball has an interior continuous representative. -/
theorem sourceBall_weak_eigenmode_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    {u : PDE.Vec d → ℝ} {g : PDE.Vec d → PDE.Vec d}
    (hu : MemLp u 2 (volume.restrict (sourceBall (0 : PDE.Vec d) R)))
    (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict (sourceBall (0 : PDE.Vec d) R)))
    (hw : HasWeakGradient (sourceBall (0 : PDE.Vec d) R) u g)
    (eig : ℝ) (heig : 0 ≤ eig)
    (hweak : ∀ ψ : PDE.Vec d → ℝ, IsSpatialTest (sourceBall (0 : PDE.Vec d) R) ψ →
      (∫ x in sourceBall (0 : PDE.Vec d) R, dot ((α x).mulVec (g x))
        (fun i => fderiv ℝ ψ x (unitVector i))) =
        eig * ∫ x in sourceBall (0 : PDE.Vec d) R, (ρ x * u x) * ψ x) :
    ∃ v : PDE.Vec d → ℝ, ContinuousOn v (sourceBall (0 : PDE.Vec d) R) ∧
      v =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)] u := by
  classical
  let U := sourceBall (0 : PDE.Vec d) R
  let r : U → ℝ := fun x => (R - euclideanNorm (x.1 - 0)) / 2
  have hr (x : U) : 0 < r x := by
    have hx : euclideanNorm (x.1 - 0) < R := x.2
    dsimp [r]; linarith
  have hrR (x : U) : r x ≤ R := by
    have hn : 0 ≤ euclideanNorm (x.1 - 0) := Real.sqrt_nonneg _
    dsimp [r]; linarith
  have hsp (x : U) : sourceBall x.1 (r x) ⊆ U := by
    change sourceBall x.1 (r x) ⊆ sourceBall 0 R
    rw [← pde_ball_eq_sourceBall x.1 (hr x), ← pde_ball_eq_sourceBall 0 hR]
    apply PDE.euclideanBall_subset_of_center_norm_add_le (hr x) hR
    change euclideanNorm (x.1 - 0) + r x ≤ R
    have hx : euclideanNorm (x.1 - 0) < R := x.2
    dsimp [r]; linarith
  have hsub (x : U) : PDE.euclideanBall (productCoordinates.symm (x.1, 0)) (r x) ⊆
      productCoordinates ⁻¹' (U ×ˢ Set.Icc (-R) R) := by
    intro z hz
    have hz' := coordinate_ball_subset_spatial_cylinder x.1 (hr x) hz
    exact ⟨hsp x hz'.1, by linarith [hz'.2.1, hrR x], by linarith [hz'.2.2, hrR x]⟩
  have hUm : MeasurableSet U := by
    change MeasurableSet (sourceBall 0 R)
    rw [← pde_ball_eq_sourceBall 0 hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hUf : volume U ≠ ∞ := by
    change volume (sourceBall 0 R) ≠ ∞
    exact volume_spatial_euclidean_ball_ne_top 0 R
  have hlocal (x : U) := coordinate_lift_continuousOn_spatial_ball hd hκ h hUm hUf
    hu hg hw eig heig hweak isCompact_Icc x.1 (hr x) (hsub x)
  choose v hv hae using hlocal
  obtain ⟨w, hwc, hwa, _⟩ := exists_continuousOn_ae_eq_of_open_cover
    (fun x : U => PDE.euclideanBall x.1 (r x / 4))
    (fun x => PDE.isOpen_euclideanBall _ _) v hv hae
  have hcover : (⋃ x : U, PDE.euclideanBall x.1 (r x / 4)) = U := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hy
      apply hsp x
      rw [← pde_ball_eq_sourceBall x.1 (hr x)]
      exact PDE.euclideanBall_mono (le_of_lt (div_pos (hr x) (by norm_num))) (by linarith [hr x]) hx
    · intro x hx
      apply Set.mem_iUnion.mpr
      refine ⟨⟨x, hx⟩, ?_⟩
      apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt
        (div_pos (hr ⟨x, hx⟩) (by norm_num))).2
      rw [sub_self, PDE.vecEuclideanNorm_eq_zero_iff.mpr rfl]
      exact div_pos (hr ⟨x, hx⟩) (by norm_num)
  rw [hcover] at hwc hwa
  exact ⟨w, hwc, hwa⟩

#print axioms sourceBall_weak_eigenmode_continuous

/-- Every actual native weak eigenfunction has a continuous interior
representative, for every nonnegative eigenvalue and without a sign restriction. -/
theorem native_weak_eigenfunction_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (eig : ℝ) (heig : 0 ≤ eig)
    (hweak : IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R) u.toH1Function
      (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0)) :
    ∃ v : PDE.Vec d → ℝ, ContinuousOn v (sourceBall (0 : PDE.Vec d) R) ∧
      v =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)] u.toH1Function.toFun := by
  have hfin : volume (sourceBall (0 : PDE.Vec d) R) ≠ ⊤ :=
    ne_top_of_le_ne_top measure_ball_lt_top.ne (measure_mono (sourceBall_subset_cube R hR))
  haveI : IsFiniteMeasure (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
    isFiniteMeasure_restrict.mpr hfin
  have hwg : HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
      u.toH1Function.toFun u.toH1Function.grad := by
    intro i
    refine ⟨(show IntegrableOn u.toH1Function.toFun (sourceBall 0 R) volume from
      u.toH1Function.memL2.integrable (by norm_num)).locallyIntegrableOn,
      (show IntegrableOn (fun x => u.toH1Function.grad x i) (sourceBall 0 R) volume from
        (u.toH1Function.gradMemL2 i).integrable (by norm_num)).locallyIntegrableOn, ?_⟩
    intro ψ hψ
    simpa only [coordinateDerivative, unitVector, Homogenization.basisVec] using
      u.toH1Function.hasWeakGradient i ψ hψ.1 hψ.2.1 hψ.2.2
  apply sourceBall_weak_eigenmode_continuous hd hκ h R hR
    u.toH1Function.memL2 u.toH1Function.gradMemL2 hwg eig heig
  intro ψ hψ
  let φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
    ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
  exact native_weakEigenEquation_on_smooth R u eig hweak φ

#print axioms native_weak_eigenfunction_continuous

/-- A normalized native eigenmode admits a continuous zero extension. -/
theorem native_normalized_eigenfunction_continuous_zero_extension {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (eig : ℝ) (heig : 0 ≤ eig)
    (hweak : IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R) u.toH1Function
      (fun x => eig * ρ x * u.toH1Function.toFun x) (fun _ => 0))
    (hnorm : weightedL2Pairing ρ u.toH1Function u.toH1Function = 1) :
    ∃ v : PDE.Vec d → ℝ, Continuous v ∧
      v =ᵐ[volume] u.zeroExtension ∧
      ∀ x ∉ sourceBall (0 : PDE.Vec d) R, v x = 0 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_sourceBall_normalized_eigenfunction_abs_bound hd hκ hR heig
  have hb := hbound ρ α h u eig heig le_rfl hweak hnorm
  obtain ⟨v, hv, hvu⟩ := native_weak_eigenfunction_continuous hd hκ h R hR u eig heig hweak
  have hκLam : κ ≤ κ⁻¹ := (h.2.2 0).1.trans (h.2.2 0).2.1
  have hset : PDE.euclideanBall (0 : PDE.Vec d) R = sourceBall 0 R :=
    pde_ball_eq_sourceBall 0 hR
  have hA : IsEllipticFieldOn (κ ^ 3) (κ ^ 3)⁻¹ (sourceBall (0 : PDE.Vec d) R) α :=
    source_uniformlyElliptic_isEllipticFieldOn hκ h
      (dirichletBall (d := d) R).isOpen.measurableSet
  have hf : AEStronglyMeasurable (fun x => eig * ρ x * u.toH1Function.toFun x)
      (volume.restrict (sourceBall (0 : PDE.Vec d) R)) :=
    (aestronglyMeasurable_const.mul h.1.aestronglyMeasurable).mul
      u.toH1Function.memL2.aestronglyMeasurable
  have hfbound : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R),
      |eig * ρ x * u.toH1Function.toFun x| ≤ eig * κ⁻¹ * K := by
    filter_upwards [hb] with x hx
    have hρ : |ρ x| ≤ κ⁻¹ :=
      (abs_of_nonneg (hκ.le.trans (h.2.2 x).1)).trans_le (h.2.2 x).2.1
    rw [abs_mul, abs_mul, abs_of_nonneg heig]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hρ heig) hx (abs_nonneg _)
      (mul_nonneg heig (inv_nonneg.mpr hκ.le))
  have hk1 := (lifted_ellipticity_scale_comparison hκ h).1
  have hk3 : κ ^ 3 ≤ κ := by
    have hk2 := mul_le_mul_of_nonneg_left hk1 hκ.le
    nlinarith [mul_le_mul_of_nonneg_left hk2 hκ.le]
  have hk3inv : κ ^ 3 ≤ (κ ^ 3)⁻¹ :=
    hk3.trans (hκLam.trans ((inv_le_inv₀ hκ (pow_pos hκ 3)).2 hk3))
  have hc : Continuous ((sourceBall (0 : PDE.Vec d) R).indicator v) ∧
      (sourceBall (0 : PDE.Vec d) R).indicator v =ᵐ[volume] u.zeroExtension := by
    have hboundary := @continuous_zero_extension_of_bounded_weak_solution d hd
      (κ ^ 3) (pow_pos hκ 3) hk3inv 0 R hR.le α
    rw [hset] at hboundary
    exact hboundary hA u _ hf
      (mul_nonneg (mul_nonneg heig (inv_nonneg.mpr hκ.le)) hK.le)
      hfbound hweak hK hb hv hvu
  refine ⟨(sourceBall (0 : PDE.Vec d) R).indicator v, hc.1, ?_, ?_⟩
  · simpa only using hc.2
  · intro x hx
    exact Set.indicator_of_notMem hx _

#print axioms native_normalized_eigenfunction_continuous_zero_extension

/-- An eigenvector of the actual energy space gives the same native weak mode,
with its values and all gradient coordinates preserved almost everywhere. -/
theorem dirichletHilbert_native_eigenmode {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (u : DirichletHilbertSpace (d := d) R hR) (eig : ℝ)
    (hvar : ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => w.val (some i) x)) =
      eig * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) u) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w)) :
    ∃ v : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R),
      v.toH1Function.toFun =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => u.val none x) ∧
      (∀ i, (fun x => v.toH1Function.grad x i) =ᵐ[volume.restrict
        (sourceBall (0 : PDE.Vec d) R)] (fun x => u.val (some i) x)) ∧
      IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R) v.toH1Function
        (fun x => eig * ρ x * v.toH1Function.toFun x) (fun _ => 0) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨v, hv, hg⟩ := EinsteinFull.Blueprint.TubeProbability.DimensionLift.exists_nativeH10_of_dirichletHilbert R hR u
  have hvw : (J u : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] v.toH1Function.toFun := by
    have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) u, hac.ae_le hv] with x hx hy
    exact hx.trans hy.symm
  refine ⟨v, hv, hg, ?_⟩
  intro φ
  obtain ⟨w, hw, hwg⟩ := exists_dirichletHilbert_of_nativeH10_weighted ρ R hR κ⁻¹
    (fun x _ => (h.2.2 x).2.1) φ
  have he := hvar w
  rw [dirichletVolume_inner_eq_native hκ h R (J u) (J w)
    v.toH1Function.toFun φ.toH1Function.toFun hvw hw] at he
  have hegrad : (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => u.val (some i) x))
        (fun i => w.val (some i) x)) =
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (v.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hg, ae_all_iff.mpr hwg] with x hx hy
    rw [show (fun i => u.val (some i) x) = v.toH1Function.grad x from (funext hx).symm,
      show (fun i => w.val (some i) x) = φ.toH1Function.grad x from funext hy]
  rw [hegrad] at he
  simpa only [IsWeakSolutionOn, Homogenization.vecDot,
    Homogenization.matVecMul, Matrix.mulVec, dotProduct, dot,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, add_zero, integral_const_mul,
    mul_assoc] using he

#print axioms dirichletHilbert_native_eigenmode

/-- The actual energy eigenbasis has continuous zero-extended representatives,
without changing its eigenvalues or its value and gradient representatives. -/
theorem exists_continuous_dirichletHilbert_eigenbasis {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eig : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (v : ℕ → Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
      (f : ℕ → PDE.Vec d → ℝ),
      (∀ n, 0 < eig n) ∧ Tendsto eig atTop atTop ∧
      Orthonormal ℝ (fun n => dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n)) ∧
      (Submodule.span ℝ (Set.range (fun n => dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n)))).topologicalClosure = ⊤ ∧
      (∀ n, v n |>.toH1Function.toFun =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => (u n).val none x)) ∧
      (∀ n i, (fun x => (v n).toH1Function.grad x i) =ᵐ[volume.restrict
        (sourceBall (0 : PDE.Vec d) R)] (fun x => (u n).val (some i) x)) ∧
      (∀ n, IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R) (v n).toH1Function
        (fun x => eig n * ρ x * (v n).toH1Function.toFun x) (fun _ => 0)) ∧
      (∀ n, Continuous (f n)) ∧
      (∀ n, f n =ᵐ[volume] (v n).zeroExtension) ∧
      (∀ n x, x ∉ sourceBall (0 : PDE.Vec d) R → f n x = 0) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eig, u, hpos, hlim, hortho, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  have hmode (n : ℕ) := dirichletHilbert_native_eigenmode hκ h R hR (u n) (eig n) (hvar n)
  choose v hv hg hw using hmode
  have hnorm (n : ℕ) : weightedL2Pairing ρ (v n).toH1Function (v n).toH1Function = 1 := by
    have hvw : (J (u n) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (v n).toH1Function.toFun := by
      have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
        withDensity_absolutelyContinuous _ _
      filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n), hac.ae_le (hv n)] with x hx hy
      exact hx.trans hy.symm
    have hself : inner ℝ (J (u n)) (J (u n)) = 1 := by
      rw [real_inner_self_eq_norm_sq, hortho.norm_eq_one n]
      norm_num
    simpa only [weightedL2Pairing] using
      (dirichletVolume_inner_self_eq_native hκ h R (J (u n))
        (v n).toH1Function.toFun hvw).symm.trans hself
  have hc (n : ℕ) := native_normalized_eigenfunction_continuous_zero_extension
    hd hκ h R hR (v n) (eig n) (hpos n).le (hw n) (hnorm n)
  choose f hf hfe hfzero using hc
  exact ⟨eig, u, v, f, hpos, hlim, hortho, hspan, hv, hg, hw, hf, hfe, hfzero⟩


theorem exists_continuous_dirichletHilbert_eigenbasis_with_variational {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (eig : ℕ → ℝ) (u : ℕ → DirichletHilbertSpace (d := d) R hR)
      (v : ℕ → Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
      (f : ℕ → PDE.Vec d → ℝ),
      (∀ n, 0 < eig n) ∧ Tendsto eig atTop atTop ∧
      Orthonormal ℝ (fun n => dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n)) ∧
      (Submodule.span ℝ (Set.range (fun n => dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n)))).topologicalClosure = ⊤ ∧
      (∀ n, v n |>.toH1Function.toFun =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => (u n).val none x)) ∧
      (∀ n i, (fun x => (v n).toH1Function.grad x i) =ᵐ[volume.restrict
        (sourceBall (0 : PDE.Vec d) R)] (fun x => (u n).val (some i) x)) ∧
      (∀ n, IsWeakSolutionOn α (sourceBall (0 : PDE.Vec d) R) (v n).toH1Function
        (fun x => eig n * ρ x * (v n).toH1Function.toFun x) (fun _ => 0)) ∧
      (∀ n, Continuous (f n)) ∧
      (∀ n, f n =ᵐ[volume] (v n).zeroExtension) ∧
      (∀ n x, x ∉ sourceBall (0 : PDE.Vec d) R → f n x = 0) ∧
      (∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => w.val (some i) x)) =
        eig n * inner ℝ (dirichletHilbertInclusion ρ R hR κ⁻¹
          (fun x _ => (h.2.2 x).2.1) (u n))
          (dirichletHilbertInclusion ρ R hR κ⁻¹
            (fun x _ => (h.2.2 x).2.1) w)) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eig, u, hpos, hlim, hortho, hspan, hvar⟩ :=
    exists_dirichletHilbert_eigenbasis hd hκ h R hR
  have hmode (n : ℕ) := dirichletHilbert_native_eigenmode hκ h R hR (u n) (eig n) (hvar n)
  choose v hv hg hw using hmode
  have hnorm (n : ℕ) : weightedL2Pairing ρ (v n).toH1Function (v n).toH1Function = 1 := by
    have hvw : (J (u n) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (v n).toH1Function.toFun := by
      have hac : dirichletVolume ρ R ≪ volume.restrict (sourceBall (0 : PDE.Vec d) R) :=
        withDensity_absolutelyContinuous _ _
      filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (u n), hac.ae_le (hv n)] with x hx hy
      exact hx.trans hy.symm
    have hself : inner ℝ (J (u n)) (J (u n)) = 1 := by
      rw [real_inner_self_eq_norm_sq, hortho.norm_eq_one n]
      norm_num
    simpa only [weightedL2Pairing] using
      (dirichletVolume_inner_self_eq_native hκ h R (J (u n))
        (v n).toH1Function.toFun hvw).symm.trans hself
  have hc (n : ℕ) := native_normalized_eigenfunction_continuous_zero_extension
    hd hκ h R hR (v n) (eig n) (hpos n).le (hw n) (hnorm n)
  choose f hf hfe hfzero using hc
  exact ⟨eig, u, v, f, hpos, hlim, hortho, hspan, hv, hg, hw, hf, hfe, hfzero, hvar⟩


#print axioms exists_continuous_dirichletHilbert_eigenbasis_with_variational

#print axioms exists_continuous_dirichletHilbert_eigenbasis

/-- The actual Dirichlet operator admits the source spectral resolution, with
continuous boundary-zero eigenfunctions and diverging eigenvalues. -/
theorem exists_sourceBall_dirichletSpectralResolution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ spectrum : DirichletSpectralResolution ρ α R,
      Tendsto spectrum.eigenvalue atTop atTop := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eig, u, v, f, hpos, hlim, hortho, hspan, hv, hg, hw, hf, hfe, hfzero⟩ :=
    exists_continuous_dirichletHilbert_eigenbasis hd hκ h R hR
  let g := fun n => dirichletHilbertZeroExtensionGrad R hR (u n)
  have hball : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hφ (n : ℕ) : f n =ᵐ[volume] dirichletHilbertZeroExtension R hR (u n) := by
    have he := (ae_eq_restrict_iff_indicator_ae_eq hball).mp (hv n)
    change (v n).zeroExtension =ᵐ[volume] dirichletHilbertZeroExtension R hR (u n) at he
    exact (hfe n).trans he
  have hweighted : dirichletVolume ρ R ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (Measure.restrict_le_self.absolutelyContinuous)
  have hrep (n : ℕ) : J (u n) =ᵐ[dirichletVolume ρ R] f n :=
    (dirichletHilbertInclusion_zeroExtension_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n)).trans (hweighted.ae_le (hφ n).symm)
  let hmem : ∀ n, MemLp (f n) 2 (dirichletVolume ρ R) :=
    fun n => (Lp.memLp (J (u n))).ae_eq (hrep n)
  have hfamily : (fun n => (hmem n).toLp (f n)) = fun n => J (u n) := by
    funext n
    apply Lp.ext
    exact (hmem n).coeFn_toLp.trans (hrep n).symm
  have hrestrict (n : ℕ) : f n =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
      (v n).toH1Function.toFun := by
    filter_upwards [(ae_restrict_of_ae (hfe n)), ae_restrict_mem hball] with x hx hxU
    rw [hx, Homogenization.H10Function.zeroExtension_apply_of_mem _ hxU]
  let spectrum : DirichletSpectralResolution ρ α R :=
    { eigenvalue := eig
      eigenfunction := f
      gradient := g
      eigenvalue_pos := hpos
      continuous := fun n => (hf n).continuousOn
      boundary_zero := by
        intro n x hx
        apply hfzero n x
        exact Set.disjoint_left.mp
          (disjoint_frontier_iff_isOpen.mpr (dirichletBall (d := d) R).isOpen) hx
      square_integrable := hmem
      gradient_square_integrable := fun n =>
        (dirichletHilbert_zeroExtension_euclideanNorm_memLp R hR (u n)).restrict _
      zero_extension_gradient := by
        intro n
        have hg0 := (dirichletHilbert_global_zeroExtension R hR (u n)).2.2
        apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ hg0
        · simpa only [Measure.restrict_univ, Set.indicator_indicator, Set.inter_self,
            dirichletHilbertZeroExtension] using
            (ae_eq_restrict_iff_indicator_ae_eq hball).mp
              (ae_restrict_of_ae ((hφ n).symm))
        · simpa only [Measure.restrict_univ, g, dirichletHilbertZeroExtensionGrad,
            Set.indicator_indicator, Set.inter_self] using (ae_eq_refl _)
      eigenfunction_equation := by
        intro n ψ hψ
        let test : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
          ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
        have he := native_weakEigenEquation_on_smooth R (v n) (eig n) (hw n) test
        have hgrad : (fun x => g n x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
            (v n).toH1Function.grad := by
          filter_upwards [ae_all_iff.mpr (hg n), ae_restrict_mem hball] with x hx hxU
          simp only [g, dirichletHilbertZeroExtensionGrad, Set.indicator_of_mem hxU]
          exact (funext hx).symm
        calc
          _ = ∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec ((v n).toH1Function.grad x))
                (fun j => fderiv ℝ ψ x (unitVector j)) := by
              apply integral_congr_ae
              filter_upwards [hgrad] with x hx
              rw [hx]
          _ = eig n * ∫ x in sourceBall (0 : PDE.Vec d) R,
              (ρ x * (v n).toH1Function.toFun x) * ψ x := he
          _ = _ := by
              congr 1
              apply integral_congr_ae
              filter_upwards [hrestrict n] with x hx
              rw [hx]
      orthonormal := by rw [hfamily]; exact hortho
      complete := by
        rw [hfamily]
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hspan }
  exact ⟨spectrum, hlim⟩


theorem exists_sourceBall_dirichletSpectralResolution_with_variational {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ (spectrum : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto spectrum.eigenvalue atTop atTop ∧
      (∀ n, (spectrum.square_integrable n).toLp (spectrum.eigenfunction n) =
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n)) ∧
      (∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
        (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (u n).val (some i) x))
            (fun i => w.val (some i) x)) =
        spectrum.eigenvalue n * inner ℝ
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
          (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) := by
  classical
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨eig, u, v, f, hpos, hlim, hortho, hspan, hv, hg, hw, hf, hfe, hfzero, hvar⟩ :=
    exists_continuous_dirichletHilbert_eigenbasis_with_variational hd hκ h R hR
  let g := fun n => dirichletHilbertZeroExtensionGrad R hR (u n)
  have hball : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hφ (n : ℕ) : f n =ᵐ[volume] dirichletHilbertZeroExtension R hR (u n) := by
    have he := (ae_eq_restrict_iff_indicator_ae_eq hball).mp (hv n)
    change (v n).zeroExtension =ᵐ[volume] dirichletHilbertZeroExtension R hR (u n) at he
    exact (hfe n).trans he
  have hweighted : dirichletVolume ρ R ≪ volume :=
    (withDensity_absolutelyContinuous _ _).trans (Measure.restrict_le_self.absolutelyContinuous)
  have hrep (n : ℕ) : J (u n) =ᵐ[dirichletVolume ρ R] f n :=
    (dirichletHilbertInclusion_zeroExtension_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n)).trans (hweighted.ae_le (hφ n).symm)
  let hmem : ∀ n, MemLp (f n) 2 (dirichletVolume ρ R) :=
    fun n => (Lp.memLp (J (u n))).ae_eq (hrep n)
  have hfamily : (fun n => (hmem n).toLp (f n)) = fun n => J (u n) := by
    funext n
    apply Lp.ext
    exact (hmem n).coeFn_toLp.trans (hrep n).symm
  have hrestrict (n : ℕ) : f n =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
      (v n).toH1Function.toFun := by
    filter_upwards [(ae_restrict_of_ae (hfe n)), ae_restrict_mem hball] with x hx hxU
    rw [hx, Homogenization.H10Function.zeroExtension_apply_of_mem _ hxU]
  let spectrum : DirichletSpectralResolution ρ α R :=
    { eigenvalue := eig
      eigenfunction := f
      gradient := g
      eigenvalue_pos := hpos
      continuous := fun n => (hf n).continuousOn
      boundary_zero := by
        intro n x hx
        apply hfzero n x
        exact Set.disjoint_left.mp
          (disjoint_frontier_iff_isOpen.mpr (dirichletBall (d := d) R).isOpen) hx
      square_integrable := hmem
      gradient_square_integrable := fun n =>
        (dirichletHilbert_zeroExtension_euclideanNorm_memLp R hR (u n)).restrict _
      zero_extension_gradient := by
        intro n
        have hg0 := (dirichletHilbert_global_zeroExtension R hR (u n)).2.2
        apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ hg0
        · simpa only [Measure.restrict_univ, Set.indicator_indicator, Set.inter_self,
            dirichletHilbertZeroExtension] using
            (ae_eq_restrict_iff_indicator_ae_eq hball).mp
              (ae_restrict_of_ae ((hφ n).symm))
        · simpa only [Measure.restrict_univ, g, dirichletHilbertZeroExtensionGrad,
            Set.indicator_indicator, Set.inter_self] using (ae_eq_refl _)
      eigenfunction_equation := by
        intro n ψ hψ
        let test : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
          ⟨ψ, hψ.1, hψ.2.1, hψ.2.2⟩
        have he := native_weakEigenEquation_on_smooth R (v n) (eig n) (hw n) test
        have hgrad : (fun x => g n x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
            (v n).toH1Function.grad := by
          filter_upwards [ae_all_iff.mpr (hg n), ae_restrict_mem hball] with x hx hxU
          simp only [g, dirichletHilbertZeroExtensionGrad, Set.indicator_of_mem hxU]
          exact (funext hx).symm
        calc
          _ = ∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec ((v n).toH1Function.grad x))
                (fun j => fderiv ℝ ψ x (unitVector j)) := by
              apply integral_congr_ae
              filter_upwards [hgrad] with x hx
              rw [hx]
          _ = eig n * ∫ x in sourceBall (0 : PDE.Vec d) R,
              (ρ x * (v n).toH1Function.toFun x) * ψ x := he
          _ = _ := by
              congr 1
              apply integral_congr_ae
              filter_upwards [hrestrict n] with x hx
              rw [hx]
      orthonormal := by rw [hfamily]; exact hortho
      complete := by
        rw [hfamily]
        exact Submodule.dense_iff_topologicalClosure_eq_top.mpr hspan }
  exact ⟨spectrum, u, hlim, fun n => congrFun hfamily n, hvar⟩


#print axioms exists_sourceBall_dirichletSpectralResolution_with_variational

#print axioms exists_sourceBall_dirichletSpectralResolution

/-- Finite linear combinations of homogeneous weak solutions remain solutions. -/
theorem homogeneous_solution_finset_sum {n : ℕ} {U : Set (PDE.Vec n)}
    {A : PDE.CoeffField n} (I : Finset ℕ) (w : ℕ → PDE.H1Function U)
    (a : ℕ → ℝ)
    (hw : ∀ i ∈ I, PDE.IsWeakDivergenceFormSolutionOn A U (w i) 0 0) :
    PDE.IsWeakDivergenceFormSolutionOn A U (∑ i ∈ I, a i • w i) 0 0 := by
  classical
  have hadd {u v : PDE.H1Function U}
      (hu : PDE.IsWeakDivergenceFormSolutionOn A U u 0 0)
      (hv : PDE.IsWeakDivergenceFormSolutionOn A U v 0 0) :
      PDE.IsWeakDivergenceFormSolutionOn A U (u + v) 0 0 := by
    rw [PDE.DGNM.solutionOn_iff] at hu hv ⊢
    intro φ
    obtain ⟨hiu, heu⟩ := hu φ
    obtain ⟨hiv, hev⟩ := hv φ
    have hf : (fun x => PDE.vecDot (PDE.matVecMul (A x) ((u + v).grad x))
        (φ.grad x)) = fun x => PDE.vecDot (PDE.matVecMul (A x) (u.grad x)) (φ.grad x) +
          PDE.vecDot (PDE.matVecMul (A x) (v.grad x)) (φ.grad x) := by
      funext x
      rw [PDE.H1Function.add_grad]
      have hm : PDE.matVecMul (A x) (u.grad x + v.grad x) =
          PDE.matVecMul (A x) (u.grad x) + PDE.matVecMul (A x) (v.grad x) := by
        funext j
        simp only [PDE.matVecMul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [hm, PDE.DGNM.vecDot_add_left]
    rw [hf, integral_add hiu hiv, heu, hev, add_zero]
    exact ⟨hiu.add hiv, rfl⟩
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, PDE.DGNM.solutionOn_iff]
    intro φ
    simp only [PDE.H1Function.zero_grad, Pi.zero_apply, PDE.matVecMul,
      mul_zero, Finset.sum_const_zero, PDE.vecDot, zero_mul]
    exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi]
    apply hadd (PDE.DGNM.solutionOn_smul (hw i (Finset.mem_insert_self i I)) (a i))
    apply ih
    intro j hj
    exact hw j (Finset.mem_insert_of_mem hj)

#print axioms homogeneous_solution_finset_sum

/-- The finite exponential combination of weak eigenmodes has its actual
summed gradient and solves the normalized homogeneous lifted equation. -/
theorem finite_coordinate_lift_solution {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {U : Set (PDE.Vec d)}
    (hU : MeasurableSet U) (hUfinite : volume U ≠ ∞)
    (u : ℕ → PDE.Vec d → ℝ) (g : ℕ → PDE.Vec d → PDE.Vec d)
    (eig : ℕ → ℝ) (hu : ∀ i, MemLp (u i) 2 (volume.restrict U))
    (hg : ∀ i j, MemLp (fun x => g i x j) 2 (volume.restrict U))
    (hw : ∀ i, HasWeakGradient U (u i) (g i)) (heig : ∀ i, 0 ≤ eig i)
    (hweak : ∀ i ψ, IsSpatialTest U ψ →
      (∫ x in U, dot ((α x).mulVec (g i x))
        (fun j => fderiv ℝ ψ x (unitVector j))) =
        eig i * ∫ x in U, (ρ x * u i x) * ψ x)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (PDE.Vec (d + 1))}
    (hΩ : IsOpen Ω) (hsub : Ω ⊆ productCoordinates ⁻¹' (U ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    ∃ w : PDE.H1Function Ω,
      w.toFun = (fun z => ∑ i ∈ I, a i * liftedValue (u i) (Real.sqrt (eig i)) z) ∧
      w.grad = (fun z => ∑ i ∈ I, a i • liftedGradient (u i) (g i) (Real.sqrt (eig i)) z) ∧
      PDE.IsWeakDivergenceFormSolutionOn (normalizedCoordinateLiftedMatrix κ ρ α) Ω w 0 0 := by
  classical
  let W : ℕ → PDE.H1Function Ω := fun i =>
    pdeH1OfNative ((coordinateLiftH1 hU hUfinite (hu i) (hg i) (hw i)
      (Real.sqrt (eig i)) hK).restrict hΩ hsub)
  refine ⟨∑ i ∈ I, a i • W i, ?_, ?_, ?_⟩
  · funext z
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, PDE.H1Function.zero_toFun, Pi.zero_apply]
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi, PDE.H1Function.add_toFun, Pi.add_apply,
        PDE.H1Function.smul_toFun]
      rw [ih]
      rfl
  · funext z
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, PDE.H1Function.zero_grad, Pi.zero_apply]
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi, PDE.H1Function.add_grad, Pi.add_apply,
        PDE.H1Function.smul_grad]
      rw [ih]
      rfl
  · apply homogeneous_solution_finset_sum
    intro i _
    exact pde_coordinate_lift_solution hκ h hU hUfinite (hu i) (hg i) (hw i)
      (eig i) (heig i) (hweak i) hK hΩ hsub

#print axioms finite_coordinate_lift_solution

/-- Weighted spatial L² norm of a finite slice of the actual spectral lift. -/
theorem spectral_lift_slice_norm_sq {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    ‖∑ i ∈ I, (a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) •
      (s.square_integrable i).toLp (s.eigenfunction i)‖ ^ 2 =
      ∑ i ∈ I, (a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simpa only [RCLike.conj_to_real, pow_two] using
    s.orthonormal.inner_sum
      (fun i => a i * Real.exp (Real.sqrt (s.eigenvalue i) * t))
      (fun i => a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) I

#print axioms spectral_lift_slice_norm_sq

/-- The weighted slice norm obeys the energy-cutoff exponential bound. -/
theorem spectral_lift_slice_norm_sq_le {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E t : ℝ) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) :
    ‖∑ i ∈ I, (a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) •
      (s.square_integrable i).toLp (s.eigenfunction i)‖ ^ 2 ≤
      Real.exp (Real.sqrt E * |t|) ^ 2 * ∑ i ∈ I, (a i) ^ 2 := by
  rw [spectral_lift_slice_norm_sq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hs : Real.sqrt (s.eigenvalue i) ≤ Real.sqrt E := Real.sqrt_le_sqrt (hcut i hi)
  have ht : Real.sqrt (s.eigenvalue i) * t ≤ Real.sqrt E * |t| :=
    (mul_le_mul_of_nonneg_left (le_abs_self t) (Real.sqrt_nonneg _)).trans
      (mul_le_mul_of_nonneg_right hs (abs_nonneg t))
  have hexp : Real.exp (Real.sqrt (s.eigenvalue i) * t) ≤
      Real.exp (Real.sqrt E * |t|) := Real.exp_le_exp.mpr ht
  have hp : Real.exp (Real.sqrt (s.eigenvalue i) * t) ^ 2 ≤
      Real.exp (Real.sqrt E * |t|) ^ 2 :=
    pow_le_pow_left₀ (Real.exp_pos _).le hexp 2
  calc
    (a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) ^ 2 =
        (a i) ^ 2 * Real.exp (Real.sqrt (s.eigenvalue i) * t) ^ 2 := mul_pow _ _ _
    _ ≤ (a i) ^ 2 * Real.exp (Real.sqrt E * |t|) ^ 2 :=
      mul_le_mul_of_nonneg_left hp (sq_nonneg _)
    _ = Real.exp (Real.sqrt E * |t|) ^ 2 * (a i) ^ 2 := mul_comm _ _

#print axioms spectral_lift_slice_norm_sq_le

/-- The weighted slice norm is the integral of the actual finite spectral sum. -/
theorem spectral_lift_slice_weighted_integral {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    (∫ x in sourceBall (0 : PDE.Vec d) R, ρ x *
      (∑ i ∈ I, a i * Real.exp (Real.sqrt (s.eigenvalue i) * t) * s.eigenfunction i x) ^ 2) =
      ∑ i ∈ I, (a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)) ^ 2 := by
  classical
  let c : ℕ → ℝ := fun i => a i * Real.exp (Real.sqrt (s.eigenvalue i) * t)
  let f : ℕ → Lp ℝ 2 (dirichletVolume ρ R) :=
    fun i => (s.square_integrable i).toLp (s.eigenfunction i)
  have hrep : (∑ i ∈ I, c i • f i : Lp ℝ 2 (dirichletVolume ρ R)) =ᵐ[dirichletVolume ρ R]
      fun x => ∑ i ∈ I, c i * s.eigenfunction i x := by
    filter_upwards [Lp.coeFn_fun_finsetSum I (fun i => c i • f i),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul (c i) (f i)),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with x hx hy hz
    rw [hx]
    apply Finset.sum_congr rfl
    intro i _
    have hfi : (f i : PDE.Vec d → ℝ) x = s.eigenfunction i x := hz i
    simpa only [Pi.smul_apply, smul_eq_mul, hfi] using hy i
  have hinner := dirichletVolume_inner_self_eq_native hκ h R
    (∑ i ∈ I, c i • f i) (fun x => ∑ i ∈ I, c i * s.eigenfunction i x) hrep
  rw [real_inner_self_eq_norm_sq, spectral_lift_slice_norm_sq] at hinner
  simpa only [c, f, pow_two, mul_assoc] using hinner.symm

#print axioms spectral_lift_slice_weighted_integral

/-- Uniform positivity of the weight transfers spectral L² functions to
Lebesgue L² on the source ball. -/
theorem spectral_eigenfunction_memLp_sourceBall {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (i : ℕ) :
    MemLp (s.eigenfunction i) 2 (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
  have hlower : ENNReal.ofReal κ • volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      dirichletVolume ρ R := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (h.2.2 x).1
  have hk : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
  have hle : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      (ENNReal.ofReal κ)⁻¹ • dirichletVolume ρ R := by
    calc
      _ = (ENNReal.ofReal κ)⁻¹ • (ENNReal.ofReal κ •
          volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hk ENNReal.ofReal_ne_top, one_smul]
      _ ≤ _ := by gcongr
  apply (s.square_integrable i).of_measure_le_smul _ hle
  exact ENNReal.inv_ne_top.mpr hk

#print axioms spectral_eigenfunction_memLp_sourceBall

/-- The ordinary spatial slice integral is bounded by the weighted spectral
energy, uniformly over every finite energy cutoff. -/
theorem spectral_lift_slice_integral_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E t : ℝ) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) :
    κ * (∫ x in sourceBall (0 : PDE.Vec d) R,
      (∑ i ∈ I, a i * Real.exp (Real.sqrt (s.eigenvalue i) * t) * s.eigenfunction i x) ^ 2) ≤
      Real.exp (Real.sqrt E * |t|) ^ 2 * ∑ i ∈ I, (a i) ^ 2 := by
  classical
  let F : PDE.Vec d → ℝ := fun x =>
    ∑ i ∈ I, a i * Real.exp (Real.sqrt (s.eigenvalue i) * t) * s.eigenfunction i x
  have hF : MemLp F 2 (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
    apply memLp_finsetSum
    intro i _
    exact (spectral_eigenfunction_memLp_sourceBall hκ h s i).const_mul _
  have hρ : MemLp ρ ⊤ (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
    apply memLp_top_of_bound h.1.aestronglyMeasurable κ⁻¹
    exact ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hκ.le.trans (h.2.2 x).1)]
      exact (h.2.2 x).2.1
  have hsq : Integrable (fun x => F x ^ 2)
      (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := hF.integrable_sq
  have hw : Integrable (fun x => ρ x * F x ^ 2)
      (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
    apply (((hF.fun_mul (r := 2) hρ).integrable_mul hF)).congr
    exact ae_of_all _ fun x => by dsimp; ring
  have hcmp : κ * (∫ x in sourceBall (0 : PDE.Vec d) R, F x ^ 2) ≤
      ∫ x in sourceBall (0 : PDE.Vec d) R, ρ x * F x ^ 2 := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hsq.const_mul κ) hw
    exact ae_of_all _ fun x => mul_le_mul_of_nonneg_right (h.2.2 x).1 (sq_nonneg _)
  have hbound := spectral_lift_slice_norm_sq_le s I a E t hcut
  rw [spectral_lift_slice_norm_sq] at hbound
  rw [spectral_lift_slice_weighted_integral hκ h s I a t] at hcmp
  exact hcmp.trans hbound

#print axioms spectral_lift_slice_integral_le

/-- Finite spectral lifts have uniform ordinary L² control on the actual
source-ball cylinder, with no eigenvalue-counting assumption. -/
theorem spectral_lift_cylinder_integral_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E b : ℝ) (hb : 0 ≤ b) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) :
    κ * (∫ z in productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-b) b),
      (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ^ 2) ≤
      (2 * b) * (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
  classical
  let U := sourceBall (0 : PDE.Vec d) R
  let K := Set.Icc (-b) b
  let F : PDE.Vec d × ℝ → ℝ := fun p =>
    ∑ i ∈ I, a i * Real.exp (Real.sqrt (s.eigenvalue i) * p.2) * s.eigenfunction i p.1
  have hU : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have hUf : volume U ≠ ∞ := volume_spatial_euclidean_ball_ne_top 0 R
  letI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hUf
  have hF : MemLp F 2 ((volume.restrict U).prod (volume.restrict K)) := by
    apply memLp_finsetSum
    intro i _
    have hi := memLp_lift_on_compact (volume.restrict U)
      (spectral_eigenfunction_memLp_sourceBall hκ h s i)
      (Real.sqrt (s.eigenvalue i)) (K := K) isCompact_Icc
    convert hi.const_mul (a i) using 1 <;> ext p <;> ring
  have hi : Integrable (fun p => F p ^ 2)
      ((volume.restrict U).prod (volume.restrict K)) := hF.integrable_sq
  have ht : Integrable (fun t => ∫ x in U, F (x, t) ^ 2) (volume.restrict K) := by
    convert hi.integral_norm_prod_right using 1
    ext t
    apply integral_congr_ae
    exact ae_of_all _ fun x => by
      change F (x, t) ^ 2 = ‖F (x, t) ^ 2‖
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hconst : Integrable (fun _ : ℝ =>
      Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) (volume.restrict K) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  have hbound : ∀ t ∈ K, κ * (∫ x in U, F (x, t) ^ 2) ≤
      Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2 := by
    intro t htmem
    have habs : |t| ≤ b := abs_le.mpr ⟨htmem.1, htmem.2⟩
    have hexp : Real.exp (Real.sqrt E * |t|) ≤ Real.exp (Real.sqrt E * b) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs (Real.sqrt_nonneg E))
    exact (spectral_lift_slice_integral_le hκ h s I a E t hcut).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.exp_pos _).le hexp 2)
        (Finset.sum_nonneg fun i _ => sq_nonneg (a i)))
  have hcmp := integral_mono_ae (ht.const_mul κ) hconst
    ((ae_restrict_mem measurableSet_Icc).mono fun t htmem => hbound t htmem)
  rw [integral_const_mul] at hcmp
  have hcoord : (∫ z in productCoordinates ⁻¹' (U ×ˢ K), F (productCoordinates z) ^ 2) =
      ∫ t in K, ∫ x in U, F (x, t) ^ 2 := by
    calc
      _ = ∫ p, F p ^ 2 ∂((volume.restrict U).prod (volume.restrict K)) := by
        exact (productCoordinates_measurePreserving_cylinder hU (show MeasurableSet K from measurableSet_Icc)).integral_comp
          productCoordinates.toHomeomorph.measurableEmbedding (fun p => F p ^ 2)
      _ = _ := integral_prod_symm _ hi
  have hc : (∫ _t in K, Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) =
      (2 * b) * (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
    simp only [K, setIntegral_const, Measure.real, Real.volume_Icc, smul_eq_mul]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ b - -b)]
    ring
  rw [hc] at hcmp
  convert hcmp using 1
  congr 1
  rw [← hcoord]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by simp only [F, liftedValue]; congr 1; apply Finset.sum_congr rfl; intro i _; ring

#print axioms spectral_lift_cylinder_integral_le

/-- The global zero-extension gradient restricts to the actual spectral
weak gradient on the source ball. -/
theorem spectral_eigenfunction_weakGradient {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (i : ℕ) :
    HasWeakGradient (sourceBall (0 : PDE.Vec d) R) (s.eigenfunction i) (s.gradient i) := by
  let U := sourceBall (0 : PDE.Vec d) R
  have hU : IsOpen U := (dirichletBall (d := d) R).isOpen
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hU
    (EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ U)
      (s.zero_extension_gradient i))
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact Set.indicator_of_mem hx _
  · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
    exact Set.indicator_of_mem hx _

#print axioms spectral_eigenfunction_weakGradient

/-- Every coordinate of the actual spectral weak gradient is L² on the
source ball. -/
theorem spectral_gradient_coordinate_memLp {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (i : ℕ) (j : Fin d) :
    MemLp (fun x => s.gradient i x j) 2
      (volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
  have hw := spectral_eigenfunction_weakGradient s i
  apply (s.gradient_square_integrable i).of_le (hw j).2.1.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_of_nonneg (show 0 ≤ euclideanNorm (s.gradient i x) from Real.sqrt_nonneg _)]
  apply Real.abs_le_sqrt
  change (s.gradient i x j)^2 ≤ ∑ k : Fin d, s.gradient i x k * s.gradient i x k
  rw [sq]
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)

#print axioms spectral_gradient_coordinate_memLp

/-- The finite exponential combination of an actual source spectrum solves
its homogeneous lifted equation with its actual summed gradient. -/
theorem spectral_finite_coordinate_lift_solution {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) {K : Set ℝ} (hK : IsCompact K)
    {Ω : Set (PDE.Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    ∃ w : PDE.H1Function Ω,
      w.toFun = (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ∧
      w.grad = (fun z => ∑ i ∈ I, a i • liftedGradient (s.eigenfunction i)
        (s.gradient i) (Real.sqrt (s.eigenvalue i)) z) ∧
      PDE.IsWeakDivergenceFormSolutionOn (normalizedCoordinateLiftedMatrix κ ρ α) Ω w 0 0 := by
  exact finite_coordinate_lift_solution hκ h (dirichletBall (d := d) R).isOpen.measurableSet
    (volume_spatial_euclidean_ball_ne_top 0 R) s.eigenfunction s.gradient s.eigenvalue
    (spectral_eigenfunction_memLp_sourceBall hκ h s) (spectral_gradient_coordinate_memLp s)
    (spectral_eigenfunction_weakGradient s) (fun i => (s.eigenvalue_pos i).le)
    s.eigenfunction_equation hK hΩ hsub I a

#print axioms spectral_finite_coordinate_lift_solution

/-- The actual zero-extended eigenmodes lift to an H¹ function across the
lateral boundary on any bounded spatial cylinder. -/
theorem spectral_finite_zeroExtension_coordinate_lift_H1 {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R)
    {B : Set (PDE.Vec d)} (hB : MeasurableSet B) (hBfinite : volume B ≠ ∞)
    {K : Set ℝ} (hK : IsCompact K) {Ω : Set (PDE.Vec (d + 1))}
    (hΩ : IsOpen Ω) (hsub : Ω ⊆ productCoordinates ⁻¹' (B ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    ∃ w : PDE.H1Function Ω,
      w.toFun = (fun z => ∑ i ∈ I, a i * liftedValue
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        (Real.sqrt (s.eigenvalue i)) z) ∧
      w.grad = (fun z => ∑ i ∈ I, a i • liftedGradient
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
        (Real.sqrt (s.eigenvalue i)) z) := by
  classical
  let U := sourceBall (0 : PDE.Vec d) R
  have hU : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have hu (i : ℕ) : MemLp (U.indicator (s.eigenfunction i)) 2 (volume.restrict B) :=
    ((memLp_indicator_iff_restrict hU).2
      (spectral_eigenfunction_memLp_sourceBall hκ h s i)).mono_measure Measure.restrict_le_self
  have hg (i : ℕ) (j : Fin d) :
      MemLp (fun x => U.indicator (s.gradient i) x j) 2 (volume.restrict B) := by
    have hh : MemLp (U.indicator (fun x => s.gradient i x j)) 2 volume :=
      (memLp_indicator_iff_restrict hU).2 (spectral_gradient_coordinate_memLp s i j)
    have hh' := hh.mono_measure (Measure.restrict_le_self (s := B))
    convert hh' using 1
    funext x
    by_cases hx : x ∈ U <;> simp [Set.indicator_apply, hx]
  have hw (i : ℕ) : HasWeakGradient B (U.indicator (s.eigenfunction i))
      (U.indicator (s.gradient i)) :=
    EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ B)
      (s.zero_extension_gradient i)
  let W : ℕ → PDE.H1Function Ω := fun i => pdeH1OfNative
    ((coordinateLiftH1 hB hBfinite (hu i) (hg i) (hw i)
      (Real.sqrt (s.eigenvalue i)) hK).restrict hΩ hsub)
  refine ⟨∑ i ∈ I, a i • W i, ?_, ?_⟩
  · funext z
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, PDE.H1Function.zero_toFun, Pi.zero_apply]
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi, PDE.H1Function.add_toFun, Pi.add_apply,
        PDE.H1Function.smul_toFun]
      rw [ih]
      rfl
  · funext z
    induction I using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, PDE.H1Function.zero_grad, Pi.zero_apply]
    | @insert i I hi ih =>
      simp only [Finset.sum_insert hi, PDE.H1Function.add_grad, Pi.add_apply,
        PDE.H1Function.smul_grad]
      rw [ih]
      rfl

#print axioms spectral_finite_zeroExtension_coordinate_lift_H1

/-- Both signed positive parts of the actual zero-extended finite lift have
Sobolev representatives with their selected weak gradients. -/
theorem spectral_finite_zeroExtension_signedParts_H1 {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R)
    {B : Set (PDE.Vec d)} (hB : MeasurableSet B) (hBfinite : volume B ≠ ∞)
    {K : Set ℝ} (hK : IsCompact K) {Q : Set (PDE.Vec (d + 1))}
    (hQ : PDE.IsOpenBoundedConvexDomain Q)
    (hsub : Q ⊆ productCoordinates ⁻¹' (B ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    let F := fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z
    let G := fun z => ∑ i ∈ I, a i • liftedGradient
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
      (Real.sqrt (s.eigenvalue i)) z
    ∃ p n : PDE.H1Function Q,
      p.toFun = (fun z => max (F z) 0) ∧
      p.grad = (fun z => {y | 0 < F y}.indicator G z) ∧
      n.toFun = (fun z => max (-F z) 0) ∧
      n.grad = (fun z => {y | F y < 0}.indicator (-G) z) := by
  obtain ⟨w, hw, hg⟩ := spectral_finite_zeroExtension_coordinate_lift_H1
    hκ h s hB hBfinite hK hQ.isOpen hsub I a
  refine ⟨w.positivePartSubConst hQ 0, w.negativePartConstSub hQ 0, ?_, ?_, ?_, ?_⟩
  · simpa only [PDE.H1Function.positivePartSubConst_toFun, sub_zero] using
      congrArg (fun f => fun z => max (f z) 0) hw
  · simpa only [PDE.H1Function.positivePartSubConst_grad, hw, hg]
  · simpa only [PDE.H1Function.negativePartConstSub_toFun, zero_sub, hw]
  · simpa only [PDE.H1Function.negativePartConstSub_grad, hw, hg]

#print axioms spectral_finite_zeroExtension_signedParts_H1

/-- The actual finite lift has L² control on every subset of the source
cylinder, including the interior balls used for local regularity. -/
theorem spectral_lift_subset_integral_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E b : ℝ) (hb : 0 ≤ b) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E)
    {Ω : Set (PDE.Vec (d + 1))}
    (hsub : Ω ⊆ productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-b) b)) :
    κ * (∫ z in Ω, (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ^ 2) ≤
      (2 * b) * (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
  classical
  let U := sourceBall (0 : PDE.Vec d) R
  let K := Set.Icc (-b) b
  let F : PDE.Vec (d + 1) → ℝ := fun z =>
    ∑ i ∈ I, a i * liftedValue (s.eigenfunction i) (Real.sqrt (s.eigenvalue i)) z
  have hU : MeasurableSet U := (dirichletBall (d := d) R).isOpen.measurableSet
  have hUf : volume U ≠ ∞ := volume_spatial_euclidean_ball_ne_top 0 R
  have hF : MemLp F 2 (volume.restrict (productCoordinates ⁻¹' (U ×ˢ K))) := by
    apply memLp_finsetSum
    intro i _
    have hi := memLp_lift_on_coordinate_cylinder hU hUf
      (spectral_eigenfunction_memLp_sourceBall hκ h s i)
      (Real.sqrt (s.eigenvalue i)) (K := K) isCompact_Icc
    simpa only [liftedValue, mul_comm, mul_left_comm, mul_assoc] using hi.const_mul (a i)
  have hcmp : (∫ z in Ω, F z ^ 2) ≤
      ∫ z in productCoordinates ⁻¹' (U ×ˢ K), F z ^ 2 := by
    apply integral_mono_measure (Measure.restrict_mono hsub le_rfl)
    · exact ae_of_all _ fun z => sq_nonneg _
    · exact hF.integrable_sq
  exact (mul_le_mul_of_nonneg_left hcmp hκ.le).trans
    (spectral_lift_cylinder_integral_le hκ h s I a E b hb hcut)

#print axioms spectral_lift_subset_integral_le

/-- The same cylinder bound holds uniformly on all lifted balls centered in
a fixed interior source ball. -/
theorem spectral_lift_interior_ball_integral_le {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) {R r q : ℝ} (hR : 0 < R)
    (hq : 0 < q) (hmargin : r + 4 * q ≤ R)
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E : ℝ) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E)
    {x : PDE.Vec d} (hx : x ∈ sourceBall 0 r) :
    κ * (∫ z in PDE.euclideanBall (productCoordinates.symm (x, 0)) (4 * q),
      (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ^ 2) ≤
      (2 * R) * (Real.exp (Real.sqrt E * R) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
  apply spectral_lift_subset_integral_le hκ h s I a E R hR.le hcut
  exact (coordinate_interior_ball_subset 0 hR hq hmargin hx).trans
    (coordinate_ball_subset_spatial_cylinder 0 hR)

#print axioms spectral_lift_interior_ball_integral_le

/-- A continuous subsolution satisfies the unit-ball Moser estimate at every
point of the half ball. -/
theorem pde_continuous_subharmonic_unit_ball_moser {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : PDE.CoeffField n),
      (∀ i j, AEMeasurable (fun x => a x i j)
        (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec n) 1))) →
      (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec n) 1, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec n) 1),
      PDE.IsWeakDivergenceFormSubharmonicOn a (PDE.euclideanBall (0 : PDE.Vec n) 1) u →
      ContinuousOn u.toFun (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)) →
      ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec n) (1 / 2),
        (ENNReal.ofReal (u.toFun x)) ^ (2 : ℝ) ≤
          ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (n : ℝ)) *
            (eLpNorm u.toFun 2 (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec n) 1))) ^
              (2 : ℝ) := by
  obtain ⟨C, hC, hmoser⟩ := PDE.exists_moserLocalMax_constant n hn
  refine ⟨C, hC, ?_⟩
  intro Λ a ha hell u hsub hcont x hx
  have hpoint : ENNReal.ofReal (u.toFun x) ≤
      essSup (fun y => ENNReal.ofReal (u.toFun y))
        (PDE.volumeOn (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2))) :=
    PDE.DGNMAssembly.le_essSup_of_continuousOn (PDE.isOpen_euclideanBall _ _)
      (ENNReal.continuous_ofReal.comp_continuousOn hcont) hx
  have hm := hmoser Λ a ha hell u hsub 2 (by norm_num)
  have hp := ENNReal.rpow_le_rpow hpoint (by norm_num : (0 : ℝ) ≤ 2)
  exact hp.trans (by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one,
    ENNReal.ofReal_ofNat] using hm)

#print axioms pde_continuous_subharmonic_unit_ball_moser

/-- The subsolution estimate at the center of a ball, including the exact
Jacobian factor in the transported L² norm. -/
theorem pde_continuous_subharmonic_ball_center_moser {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ r : ℝ), 0 < r → ∀ (z : PDE.Vec n)
      (a : PDE.CoeffField n),
      (∀ i j, AEMeasurable (fun x => a x i j)
        (PDE.volumeOn (PDE.euclideanBall z r))) →
      (∀ x ∈ PDE.euclideanBall z r, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall z r),
      PDE.IsWeakDivergenceFormSubharmonicOn a (PDE.euclideanBall z r) u →
      Continuous u.toFun →
      (ENNReal.ofReal (u.toFun z)) ^ (2 : ℝ) ≤
        ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (n : ℝ)) *
          (ENNReal.ofReal ((r ^ n)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
            eLpNorm u.toFun 2 (PDE.volumeOn (PDE.euclideanBall z r))) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hmoser⟩ := pde_continuous_subharmonic_unit_ball_moser hn
  refine ⟨C, hC, ?_⟩
  intro Λ r hr z a ha hell u hsub hcont
  let u₀ := PDE.DGNM.blowUp u z hr (Set.Subset.rfl)
  let a₀ := PDE.DGNM.blowUpCoeff a z r
  have ha₀ := PDE.DGNM.blowUpCoeff_aemeasurable ha z hr (Set.Subset.rfl)
  have hell₀ := PDE.DGNM.blowUpCoeff_elliptic hell z hr (Set.Subset.rfl)
  have hsub₀ := PDE.DGNM.subharmonicOn_blowUp (PDE.isOpen_euclideanBall z r)
    hsub z hr (Set.Subset.rfl)
  have hc₀ : ContinuousOn u₀.toFun (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)) := by
    have hc : Continuous (fun y : PDE.Vec n => r • y + z) := by fun_prop
    exact (hcont.comp hc).continuousOn
  have hz : (0 : PDE.Vec n) ∈ PDE.euclideanBall 0 (1 / 2) :=
    PDE.center_mem_euclideanBall 0 (by norm_num)
  have hb := hmoser Λ a₀ ha₀ hell₀ u₀ hsub₀ hc₀ 0 hz
  have hnorm := PDE.DGNM.eLpNorm_comp_affineScale_ball z hr 1 u.toFun 2
  rw [mul_one] at hnorm
  have hfun : u₀.toFun = (fun y => u.toFun (r • y + z)) := by
    funext y
    rfl
  rw [hfun, hnorm] at hb
  simpa only [smul_zero, zero_add] using hb

#print axioms pde_continuous_subharmonic_ball_center_moser

/-- Quantitative unit-ball Moser estimate, retaining the pointwise bound
and the continuous representative for homogeneous solutions. -/
theorem pde_unit_ball_moser_quantitative {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ (a : PDE.CoeffField n),
      (∀ i j, AEMeasurable (fun x => a x i j)
        (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1))) →
      (∀ x ∈ PDE.euclideanBall (0 : PDE.Vec n) 1, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall (0 : PDE.Vec n) 1),
      PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall (0 : PDE.Vec n) 1) u 0 0 →
      ∃ v : PDE.Vec n → ℝ,
        ContinuousOn v (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)) ∧
        v =ᵐ[volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2))] u.toFun ∧
        ∀ x ∈ PDE.euclideanBall (0 : PDE.Vec n) (1 / 2),
          ENNReal.ofReal |v x| ≤
            ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 4) * (2 : ℝ) ^ ((n : ℝ) / 2)) *
              eLpNorm u.toFun 2 (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1)) := by
  obtain ⟨C, hC, hmoser⟩ := PDE.exists_moser_holder_constant n hn
  refine ⟨C, hC, ?_⟩
  intro Λ hΛ a ha hell u hsol
  obtain ⟨β, hβ, hβ1, hmoserβ⟩ := hmoser Λ hΛ
  obtain ⟨v, M₀, M₁, hv, hM₀, hM₁, hb, hholder, hbound⟩ :=
    hmoserβ a ha hell u hsol 2 (by norm_num)
  refine ⟨v, hholder.continuousOn ((Real.exp_pos _).trans_le hβ) hM₁, hv, ?_⟩
  intro x hx
  have hle : ENNReal.ofReal |v x| ≤ ENNReal.ofReal (M₀ + M₁) :=
    ENNReal.ofReal_le_ofReal ((hb x hx).trans (le_add_of_nonneg_right hM₁))
  exact hle.trans (by simpa only [show (2 : ℝ) - 1 = 1 by norm_num, div_one,
    show (2 : ℝ) * 2 = 4 by norm_num, ENNReal.ofReal_ofNat] using hbound)

#print axioms pde_unit_ball_moser_quantitative

/-- Quantitative Moser estimate after affine normalization to a unit ball. -/
theorem pde_ball_moser_quantitative_normalized {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 1 ≤ Λ → 0 < R → ∀ (z : PDE.Vec n)
      (a : PDE.CoeffField n), (∀ i j, Measurable (fun x => a x i j)) →
      (∀ x ∈ PDE.euclideanBall z R, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall z R),
      PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall z R) u 0 0 →
      ∃ V : PDE.Vec n → ℝ, ContinuousOn V (PDE.euclideanBall z (R / 2)) ∧
        V =ᵐ[volume.restrict (PDE.euclideanBall z (R / 2))] u.toFun ∧
        ∀ x ∈ PDE.euclideanBall z (R / 2),
          ENNReal.ofReal |V x| ≤ ENNReal.ofReal R *
            (ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 4) * (2 : ℝ) ^ ((n : ℝ) / 2)) *
              eLpNorm (fun y => R⁻¹ * u.toFun (R • y + z)) 2
                (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1))) := by
  obtain ⟨C, hC, hmoser⟩ := pde_unit_ball_moser_quantitative hn
  refine ⟨C, hC, ?_⟩
  intro Λ R hΛ hR z a ha hell u hsol
  open PDE in
  let BR := euclideanBall (0 : PDE.Vec n) R
  open PDE in
  have htranslate : translateSet (-z) (euclideanBall z R) = BR := by
    ext x
    rw [mem_translateSet_iff_sub_mem]
    simp only [sub_neg_eq_add]
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR,
      mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simp [sub_eq_add_neg, add_assoc]
  open PDE in
  let uraw := u.translate (-z)
  open PDE in
  let uR : H1Function BR := uraw.restrict (isOpen_euclideanBall _ _)
    (htranslate ▸ Set.Subset.rfl)
  open PDE in
  let aR : CoeffField n := fun x => a (x + z)
  open PDE in
  have hsolR : IsWeakDivergenceFormSolutionOn aR BR uR 0 0 := by
    have hsolraw := hsol.translate (-z)
    have hopenraw : IsOpen (translateSet (-z) (euclideanBall z R)) := by
      rw [htranslate]
      exact isOpen_euclideanBall _ _
    simpa only [aR, uR, uraw, sub_neg_eq_add, Pi.zero_apply] using!
      hsolraw.restrict hopenraw (isOpen_euclideanBall _ _) (htranslate ▸ Set.Subset.rfl)
  open PDE in
  have hscale : R⁻¹ • BR = euclideanBall (0 : PDE.Vec n) 1 := by
    dsimp only [BR]
    rw [euclideanBall_eq_translateSet_smul_unit_of_pos (0 : PDE.Vec n) hR]
    simp only [translateSet_zero, smul_smul]
    rw [inv_mul_cancel₀ hR.ne', one_smul]
  open PDE in
  let usraw := uR.dilate (inv_pos.mpr hR)
  open PDE in
  have hunitSub : euclideanBall (0 : PDE.Vec n) 1 ⊆ R⁻¹ • BR := by rw [hscale]
  open PDE in
  let u0 : H1Function (euclideanBall (0 : PDE.Vec n) 1) :=
    usraw.restrict (isOpen_euclideanBall _ _) hunitSub
  open PDE in
  let a0 : CoeffField n := fun x => aR (R • x)
  open PDE in
  have hsol0 : IsWeakDivergenceFormSolutionOn a0 (euclideanBall (0 : PDE.Vec n) 1)
      u0 0 0 := by
    have hs := hsolR.dilate_of_pos (inv_pos.mpr hR)
    have ho : IsOpen (R⁻¹ • BR) := by rw [hscale]; exact isOpen_euclideanBall _ _
    have hs' := hs.restrict ho (isOpen_euclideanBall _ _) hunitSub
    simpa only [a0, u0, usraw, inv_inv, Pi.zero_apply, mul_zero,
      inv_mul_cancel₀ hR.ne', one_mul, smul_eq_mul] using! hs'
  open PDE in
  have hell0 : ∀ x ∈ euclideanBall (0 : PDE.Vec n) 1, IsEllipticMatrix 1 Λ (a0 x) := by
    intro x hx
    apply hell
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hR).2
    simpa [a0, aR, vecEuclideanNorm_smul, abs_of_pos hR, sub_eq_add_neg,
      add_assoc] using (mul_lt_mul_of_pos_left hx' hR)
  have ha0 : ∀ i j, AEMeasurable (fun x => a0 x i j)
      (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1)) := by
    intro i j
    have hc : Continuous (fun x : PDE.Vec n => R • x + z) := by fun_prop
    exact ((ha i j).comp hc.measurable).aemeasurable
  obtain ⟨v, hvcont, hv, hbound⟩ := hmoser Λ hΛ a0 ha0 hell0 u0 hsol0
  let V : PDE.Vec n → ℝ := fun x => R * v (R⁻¹ • (x - z))
  have hmap : Set.MapsTo (fun x : PDE.Vec n => R⁻¹ • (x - z))
      (PDE.euclideanBall z (R / 2)) (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)) := by
    intro x hx
    apply (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    have hx' := (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity : 0 < R / 2)).1 hx
    have ht : PDE.vecEuclideanNorm (x - z) / R < 1 / 2 :=
      (div_lt_iff₀ hR).2 (by linarith)
    simpa [PDE.vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hR),
      inv_mul_eq_div] using ht
  have hc : Continuous (fun x : PDE.Vec n => R⁻¹ • (x - z)) := by fun_prop
  refine ⟨V, (hvcont.comp hc.continuousOn hmap).const_mul R, ?_, ?_⟩
  ·
    have hunit : ∀ᵐ y ∂volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) (1 / 2)),
        V (R • y + z) = u.toFun (R • y + z) := by
      filter_upwards [hv] with y hy
      have hy' := congrArg (fun t : ℝ => R * t) hy
      simpa [V, u0, usraw, uR, uraw, PDE.H1Function.restrict_toFun,
        PDE.H1Function.dilate_toFun, PDE.H1Function.translate_toFun, hR.ne',
        smul_smul, mul_assoc] using hy'
    have h := (PDE.DGNM.ae_comp_affineScale_ball_iff z hR (1 / 2)
      (P := fun x => V x = u.toFun x)).mp hunit
    change ∀ᵐ x ∂PDE.volumeOn (PDE.euclideanBall z (R / 2)), V x = u.toFun x
    rw [show R / 2 = R * (1 / 2) by ring]
    exact h

  · intro x hx
    have hb := hbound _ (hmap hx)
    have hfun : u0.toFun = (fun y => R⁻¹ * u.toFun (R • y + z)) := by
      funext y
      simp [u0, usraw, uR, uraw, PDE.H1Function.restrict_toFun,
        PDE.H1Function.dilate_toFun, PDE.H1Function.translate_toFun]
    rw [hfun] at hb
    have hmul := mul_le_mul_left hb (ENNReal.ofReal R)
    simpa [V, abs_mul, abs_of_pos hR, ENNReal.ofReal_mul hR.le,
      u0, usraw, uR, uraw, PDE.H1Function.restrict_toFun,
      PDE.H1Function.dilate_toFun, PDE.H1Function.translate_toFun,
      smul_smul, mul_assoc, mul_comm, mul_left_comm] using hmul

#print axioms pde_ball_moser_quantitative_normalized

/-- The L² norm of the normalized function in the unit ball, expressed
in terms of the original function on the original ball. -/
theorem pde_normalized_eLpNorm_eq {n : ℕ} {R : ℝ} (hR : 0 < R)
    (z : PDE.Vec n) (u : PDE.Vec n → ℝ) :
    eLpNorm (fun y => R⁻¹ * u (R • y + z)) 2
      (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1)) =
      ENNReal.ofReal R⁻¹ * (ENNReal.ofReal ((R ^ n)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm u 2 (volume.restrict (PDE.euclideanBall z R))) := by
  have hs := eLpNorm_const_smul R⁻¹ (fun y => u (R • y + z)) 2
    (volume.restrict (PDE.euclideanBall (0 : PDE.Vec n) 1))
  rw [Pi.smul_def] at hs
  have ha := PDE.DGNM.eLpNorm_comp_affineScale_ball z hR 1 u 2
  rw [mul_one] at ha
  simpa only [Pi.smul_apply, smul_eq_mul, Real.enorm_eq_ofReal (inv_nonneg.mpr hR.le), ha] using hs

#print axioms pde_normalized_eLpNorm_eq

/-- Quantitative Moser estimate on a ball, measured using its original L² norm. -/
theorem pde_ball_moser_quantitative {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 1 ≤ Λ → 0 < R → ∀ (z : PDE.Vec n)
      (a : PDE.CoeffField n), (∀ i j, Measurable (fun x => a x i j)) →
      (∀ x ∈ PDE.euclideanBall z R, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall z R),
      PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall z R) u 0 0 →
      ∃ V : PDE.Vec n → ℝ, ContinuousOn V (PDE.euclideanBall z (R / 2)) ∧
        V =ᵐ[volume.restrict (PDE.euclideanBall z (R / 2))] u.toFun ∧
        ∀ x ∈ PDE.euclideanBall z (R / 2),
          ENNReal.ofReal |V x| ≤ ENNReal.ofReal R *
            (ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 4) * (2 : ℝ) ^ ((n : ℝ) / 2)) *
              (ENNReal.ofReal R⁻¹ *
                (ENNReal.ofReal ((R ^ n)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
                  eLpNorm u.toFun 2 (volume.restrict (PDE.euclideanBall z R))))) := by
  obtain ⟨C, hC, h⟩ := pde_ball_moser_quantitative_normalized hn
  refine ⟨C, hC, ?_⟩
  intro Λ R hΛ hR z a ha hell u hsol
  obtain ⟨V, hv, hae, hb⟩ := h Λ R hΛ hR z a ha hell u hsol
  refine ⟨V, hv, hae, ?_⟩
  intro x hx
  simpa only [pde_normalized_eLpNorm_eq hR z u.toFun] using hb x hx

#print axioms pde_ball_moser_quantitative

/-- The squared L² norm equals the integral of the square. -/
theorem eLpNorm_two_sq_eq_ofReal_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f : α → ℝ) (hf : AEStronglyMeasurable f μ)
    (hfi : Integrable (fun x => f x ^ 2) μ) :
    eLpNorm f 2 μ ^ 2 = ENNReal.ofReal (∫ x, f x ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall fun x => sq_nonneg (f x))]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

#print axioms eLpNorm_two_sq_eq_ofReal_integral

/-- An actual finite spectral lift is continuous wherever its spatial
coordinate lies inside the source ball. -/
theorem spectral_finite_lift_continuousOn {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Ω : Set (PDE.Vec (d + 1))}
    (hΩ : Ω ⊆ {z | (productCoordinates z).1 ∈ sourceBall 0 R}) :
    ContinuousOn (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) Ω := by
  apply continuousOn_finset_sum
  intro i hi
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have ht : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).2) :=
    (productCoordinates (d := d)).continuous.snd
  have hu : ContinuousOn (fun z => s.eigenfunction i (productCoordinates z).1) Ω :=
    (s.continuous i).comp hp.continuousOn (fun z hz => subset_closure (hΩ hz))
  exact ((hu.mul (Real.continuous_exp.comp (continuous_const.mul ht)).continuousOn).const_mul (a i))

#print axioms spectral_finite_lift_continuousOn

/-- The actual finite lift remains continuous up to the lateral boundary. -/
theorem spectral_finite_lift_continuousOn_closure {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Ω : Set (PDE.Vec (d + 1))}
    (hΩ : Ω ⊆ {z | (productCoordinates z).1 ∈ closure (sourceBall 0 R)}) :
    ContinuousOn (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) Ω := by
  apply continuousOn_finset_sum
  intro i hi
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have ht : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).2) :=
    (productCoordinates (d := d)).continuous.snd
  have hu : ContinuousOn (fun z => s.eigenfunction i (productCoordinates z).1) Ω :=
    (s.continuous i).comp hp.continuousOn hΩ
  exact ((hu.mul (Real.continuous_exp.comp (continuous_const.mul ht)).continuousOn).const_mul (a i))

#print axioms spectral_finite_lift_continuousOn_closure

/-- The finite lift vanishes along the spatial boundary at every height. -/
theorem spectral_finite_lift_boundary_zero {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (z : PDE.Vec (d + 1))
    (hz : (productCoordinates z).1 ∈ frontier (sourceBall 0 R)) :
    (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [liftedValue, s.boundary_zero i _ hz]
  simp

#print axioms spectral_finite_lift_boundary_zero

/-- The finite lift with its actual spatial zero extension is continuous,
including across the lateral boundary. -/
theorem spectral_finite_zeroExtension_lift_continuous {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ) :
    Continuous (fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z) := by
  classical
  apply continuous_finset_sum
  intro i hi
  have hu : Continuous ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i)) := by
    apply continuous_piecewise
    · intro x hx
      exact s.boundary_zero i x hx
    · exact s.continuous i
    · exact continuousOn_const
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have ht : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).2) :=
    (productCoordinates (d := d)).continuous.snd
  exact ((hu.comp hp).mul (Real.continuous_exp.comp (continuous_const.mul ht))).const_mul (a i)

#print axioms spectral_finite_zeroExtension_lift_continuous

/-- On a compact lifted patch, a positive level set of the actual finite lift
is compactly contained in the spatial cylinder. -/
theorem spectral_finite_lift_positive_level_compact {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {K : Set (PDE.Vec (d + 1))} (hK : IsCompact K) {k : ℝ} (hk : 0 < k) :
    ∃ L : Set (PDE.Vec (d + 1)), IsCompact L ∧
      L ⊆ {z | (productCoordinates z).1 ∈ sourceBall 0 R} ∧
      ∀ z ∈ K, (productCoordinates z).1 ∈ sourceBall 0 R →
        k ≤ ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
          (Real.sqrt (s.eigenvalue i)) z → z ∈ L := by
  let U := sourceBall (0 : PDE.Vec d) R
  let C : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ closure U}
  let F : PDE.Vec (d + 1) → ℝ := fun z => ∑ i ∈ I, a i *
    liftedValue (s.eigenfunction i) (Real.sqrt (s.eigenvalue i)) z
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hU : IsOpen U := (dirichletBall (d := d) R).isOpen
  have hC : IsClosed C := isClosed_closure.preimage hp
  have hF : ContinuousOn F C := spectral_finite_lift_continuousOn_closure s I a (fun _ hz => hz)
  have hlevel : IsClosed (C ∩ F ⁻¹' Set.Ici k) :=
    hF.preimage_isClosed_of_isClosed hC isClosed_Ici
  refine ⟨K ∩ (C ∩ F ⁻¹' Set.Ici k), hK.inter_right hlevel, ?_, ?_⟩
  · intro z hz
    change (productCoordinates z).1 ∈ U
    by_contra hzU
    have hb : (productCoordinates z).1 ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hz.2.1, hzU⟩
    have hzero : F z = 0 := spectral_finite_lift_boundary_zero s I a z hb
    have hle : k ≤ F z := hz.2.2
    linarith
  · intro z hz hzU hzlevel
    exact ⟨hz, subset_closure hzU, hzlevel⟩

#print axioms spectral_finite_lift_positive_level_compact

/-- A positive truncation of an actual finite lift, multiplied by a smooth
cutoff supported in the patch, is an admissible zero-boundary test. -/
theorem spectral_finite_lift_positive_level_test {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q))
    (hw : w.toFun = fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z)
    {k : ℝ} (hk : 0 < k) {η : PDE.Vec (d + 1) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηQ : tsupport η ⊆ Q) :
    ∃ φ : PDE.H10Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      (∀ z, φ.toH1Function.toFun z = η z * max (w.toFun z - k) 0) ∧
      φ.toH1Function.grad = fun z => η z • PDE.Ch4Infra.posPartGrad w k z +
        max (w.toFun z - k) 0 • PDE.classicalGradient η z := by
  let V : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R}
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hV : IsOpen V := (dirichletBall (d := d) R).isOpen.preimage hp
  have hΩ : IsOpen (V ∩ Q) := hV.inter hQ
  let v := PDE.Ch4Infra.positivePartOpen hΩ w k
    (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w hk.le)
  let ψ := v.mulContDiffHasCompactSupport hη hηc
  obtain ⟨L, hLc, hLV, hL⟩ := spectral_finite_lift_positive_level_compact s I a hηc hk
  have hL'c : IsCompact (L ∩ tsupport η) := hLc.inter_right (isClosed_tsupport η)
  have hL'Ω : L ∩ tsupport η ⊆ V ∩ Q := by
    intro z hz
    exact ⟨hLV hz.1, hηQ hz.2⟩
  have hψf : ψ.toFun = fun z => η z * max (w.toFun z - k) 0 := by
    rw [PDE.H1Function.mulContDiffHasCompactSupport_toFun]
    rfl
  have hψ0 : ∀ z ∈ V ∩ Q, z ∉ L ∩ tsupport η → ψ.toFun z = 0 := by
    intro z hz hzL
    rw [hψf]
    by_cases hzη : z ∈ tsupport η
    · have hn : ¬ k ≤ w.toFun z := by
        intro hzlevel
        apply hzL
        refine ⟨hL z hzη hz.1 ?_, hzη⟩
        rw [← congrFun hw z]
        exact hzlevel
      have hmax : max (w.toFun z - k) 0 = 0 := max_eq_right (by linarith)
      simp [hmax]
    · simp [image_eq_zero_of_notMem_tsupport hzη]
  let φ := PDE.Ch4Infra.toH10OfCompact hΩ ψ hL'Ω hL'c hψ0
  refine ⟨φ, ?_, ?_⟩
  · intro z
    exact congrFun hψf z
  · exact PDE.H1Function.mulContDiffHasCompactSupport_grad v hη hηc

#print axioms spectral_finite_lift_positive_level_test

/-- Positive-level gradients converge to the zero-level truncation gradient
on every finite-volume open patch. -/
theorem posPartGrad_tendsto_zero_level {d : ℕ} {U : Set (PDE.Vec d)}
    (hU : IsOpen U) (hfin : volume U ≠ ⊤) (w : PDE.H1Function U)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (nhds 0)) (i : Fin d) :
    Tendsto (fun n => eLpNorm (fun x => PDE.Ch4Infra.posPartGrad w (ε n) x i -
      PDE.Ch4Infra.posPartGrad w 0 x i) 2 (PDE.volumeOn U)) atTop (nhds 0) := by
  letI : IsFiniteMeasure (PDE.volumeOn U) := ⟨by simpa [PDE.volumeOn] using hfin.lt_top⟩
  let F : ℕ → PDE.H1Function U := fun n => w.addConst (-ε n)
  have hgrad : ∀ j, Tendsto (fun n => eLpNorm
      (fun x => (F n).grad x j - w.grad x j) 2 (PDE.volumeOn U)) atTop (nhds 0) := by
    intro j
    simpa [F, PDE.H1Function.grad_addConst] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (nhds 0))
  have hae : ∀ᵐ x ∂(PDE.volumeOn U),
      Tendsto (fun n => (F n).toFun x) atTop (nhds (w.toFun x)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    simpa [F, PDE.H1Function.addConst_apply, sub_eq_add_neg] using
      (tendsto_const_nhds.sub hε : Tendsto (fun n => w.toFun x - ε n) atTop (nhds (w.toFun x - 0)))
  have ht := PDE.Ch4Infra.tendsto_posPartGrad_eLpNorm hU hfin w F 0 hgrad hae i
  apply ht.congr
  intro n
  congr 1
  funext x
  have heq : PDE.Ch4Infra.posPartGrad (F n) 0 x = PDE.Ch4Infra.posPartGrad w (ε n) x := by
    by_cases hx : ε n < w.toFun x
    · simp [PDE.Ch4Infra.posPartGrad, hx, F, PDE.H1Function.grad_addConst]
    · have hx' : ¬ 0 < (F n).toFun x := by
        simp only [F, PDE.H1Function.addConst_apply]
        linarith
      simp [PDE.Ch4Infra.posPartGrad, hx, hx']
  rw [heq]

#print axioms posPartGrad_tendsto_zero_level

/-- Positive-level truncations converge in L² to the zero-level truncation. -/
theorem positivePart_tendsto_zero_level {d : ℕ} {U : Set (PDE.Vec d)}
    (hfin : volume U ≠ ⊤) (w : PDE.H1Function U) (ε : ℕ → ℝ)
    (hεnonneg : ∀ n, 0 ≤ ε n) (hε : Tendsto ε atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun x => max (w.toFun x - ε n) 0 -
      max (w.toFun x - 0) 0) 2 (PDE.volumeOn U)) atTop (nhds 0) := by
  letI : IsFiniteMeasure (PDE.volumeOn U) := ⟨by simpa [PDE.volumeOn] using hfin.lt_top⟩
  have hF n := PDE.Ch4Infra.memL2On_positivePart_of_nonneg w (hεnonneg n)
  have hf := PDE.Ch4Infra.memL2On_positivePart_of_nonneg w (le_refl 0)
  have hbound : ∀ n, ∀ᵐ x ∂(PDE.volumeOn U),
      ‖max (w.toFun x - ε n) 0‖ ≤ ‖w.toFun x‖ := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    simp only [Real.norm_eq_abs]
    rcases le_total (w.toFun x - ε n) 0 with hx | hx
    · rw [max_eq_right hx, abs_zero]
      exact abs_nonneg _
    · rw [max_eq_left hx, abs_of_nonneg hx]
      linarith [hεnonneg n, le_abs_self (w.toFun x)]
  have hpoint : ∀ᵐ x ∂(PDE.volumeOn U),
      Tendsto (fun n => max (w.toFun x - ε n) 0) atTop
        (nhds (max (w.toFun x - 0) 0)) := by
    refine Filter.Eventually.of_forall fun x => ?_
    exact (tendsto_const_nhds.sub hε).max tendsto_const_nhds
  change Tendsto (fun n => eLpNorm ((fun x => max (w.toFun x - ε n) 0) -
    (fun x => max (w.toFun x - 0) 0)) 2 (PDE.volumeOn U)) atTop (nhds 0)
  exact PDE.tendsto_eLpNorm_sub_zero_of_tendsto_ae_of_dominated
    (p := 2) (by norm_num) (by norm_num)
    (fun n => (hF n).aestronglyMeasurable) hf w.memL2 hbound hpoint

#print axioms positivePart_tendsto_zero_level

/-- The zero-level cutoff of a finite spectral lift has zero boundary values. -/
theorem spectral_finite_lift_zero_level_test {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (hfin : volume ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q) ≠ ⊤)
    (w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q))
    (hw : w.toFun = fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z)
    {η : PDE.Vec (d + 1) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηQ : tsupport η ⊆ Q) :
    ∃ φ : PDE.H10Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      (∀ z, φ.toH1Function.toFun z = η z * max (w.toFun z) 0) ∧
      φ.toH1Function.grad = fun z => η z • PDE.Ch4Infra.posPartGrad w 0 z +
        max (w.toFun z) 0 • PDE.classicalGradient η z := by
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let V : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R}
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hΩ : IsOpen (V ∩ Q) := ((dirichletBall (d := d) R).isOpen.preimage hp).inter hQ
  obtain ⟨L, hL, hηL⟩ := PDE.Ch4Infra.EucLip.of_contDiff_hasCompactSupport
    (hη.of_le (by simp)) hηc
  obtain ⟨M, hM⟩ := hη.continuous.bounded_above_of_compact_support hηc
  have hM' : ∀ x, |η x| ≤ M := fun x => by simpa using hM x
  let v : ℕ → PDE.H1Function (V ∩ Q) := fun n =>
    PDE.Ch4Infra.positivePartOpen hΩ w (ε n)
      (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w (hεpos n).le)
  let v₀ : PDE.H1Function (V ∩ Q) := PDE.Ch4Infra.positivePartOpen hΩ w 0
    (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w le_rfl)
  let F : ℕ → PDE.H1Function (V ∩ Q) := fun n => PDE.Ch4Infra.mulLip hΩ (v n) hηL hL hM'
  let f : PDE.H1Function (V ∩ Q) := PDE.Ch4Infra.mulLip hΩ v₀ hηL hL hM'
  have hmem : ∀ n, PDE.MemH10 (V ∩ Q) (F n).toFun := by
    intro n
    obtain ⟨φ, hφ, _⟩ := spectral_finite_lift_positive_level_test s I a hQ w hw
      (hεpos n) hη hηc hηQ
    refine ⟨φ, ?_⟩
    funext x
    simpa [F, v, PDE.Ch4Infra.positivePartOpen] using hφ x
  have hv : Tendsto (fun n => eLpNorm (fun x => v₀.toFun x - (v n).toFun x)
      2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
    have ht := positivePart_tendsto_zero_level (U := V ∩ Q) hfin w ε
      (fun n => (hεpos n).le) hε
    simpa only [v, v₀, PDE.Ch4Infra.positivePartOpen, eLpNorm_sub_swap] using ht
  have hg (i : Fin (d + 1)) : Tendsto (fun n => eLpNorm
      (fun x => v₀.grad x i - (v n).grad x i) 2 (PDE.volumeOn (V ∩ Q)))
      atTop (nhds 0) := by
    have ht := posPartGrad_tendsto_zero_level hΩ hfin w ε hε i
    simpa [v, v₀, PDE.Ch4Infra.positivePartOpen, eLpNorm_sub_swap] using ht
  have hfun : Tendsto (fun n => eLpNorm (fun x => f.toFun x - (F n).toFun x)
      2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
    have hb : Tendsto (fun n => ENNReal.ofReal M * eLpNorm
        (fun x => v₀.toFun x - (v n).toFun x) 2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hv (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => bot_le)
      (fun n => PDE.Ch4Infra.eLpNorm_mulLip_sub_value_le hΩ v₀ (v n) hηL hL hM')
  have hgrad (i : Fin (d + 1)) : Tendsto (fun n => eLpNorm
      (fun x => f.grad x i - (F n).grad x i) 2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
    have hb1 : Tendsto (fun n => ENNReal.ofReal M * eLpNorm
        (fun x => v₀.grad x i - (v n).grad x i) 2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul (hg i) (Or.inr ENNReal.ofReal_ne_top)
    have hb2 : Tendsto (fun n => ENNReal.ofReal L * eLpNorm
        (fun x => v₀.toFun x - (v n).toFun x) 2 (PDE.volumeOn (V ∩ Q))) atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.const_mul hv (Or.inr ENNReal.ofReal_ne_top)
    have hb := hb1.add hb2
    rw [add_zero] at hb
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun n => bot_le)
      (fun n => PDE.Ch4Infra.eLpNorm_mulLip_sub_grad_le hΩ v₀ (v n) hηL hL hM' i)
  have hm := PDE.memH10_of_tendsto_H1 hΩ f F hmem hfun hgrad
  let φ := PDE.Ch4Infra.ofMemH10 hΩ f hm
  refine ⟨φ, ?_, ?_⟩
  · intro x
    simp [φ, f, v₀, PDE.Ch4Infra.positivePartOpen]
  · simp [φ, f, v₀, PDE.Ch4Infra.positivePartOpen] <;> rfl

#print axioms spectral_finite_lift_zero_level_test

/-- A smooth cutoff times the unscaled level ramp of a finite spectral lift
is a zero-boundary test, including its product-rule gradient. -/
theorem spectral_finite_lift_level_ramp_test {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (hfin : volume ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q) ≠ ⊤)
    (w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q))
    (hw : w.toFun = fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z)
    {ε : ℝ} (hε : 0 < ε) {η : PDE.Vec (d + 1) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηQ : tsupport η ⊆ Q) :
    ∃ φ : PDE.H10Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      (∀ z, φ.toH1Function.toFun z = η z *
        (max (w.toFun z) 0 - max (w.toFun z - ε) 0)) ∧
      φ.toH1Function.grad = fun z =>
        (η z • PDE.Ch4Infra.posPartGrad w 0 z +
          max (w.toFun z) 0 • PDE.classicalGradient η z) -
        (η z • PDE.Ch4Infra.posPartGrad w ε z +
          max (w.toFun z - ε) 0 • PDE.classicalGradient η z) := by
  obtain ⟨φ₀, hφ₀, hg₀⟩ := spectral_finite_lift_zero_level_test s I a
    hQ hfin w hw hη hηc hηQ
  obtain ⟨φε, hφε, hgε⟩ := spectral_finite_lift_positive_level_test s I a
    hQ w hw hε hη hηc hηQ
  refine ⟨PDE.Ch4Infra.h10Sub φ₀ φε, ?_, ?_⟩
  · intro z
    simp only [PDE.Ch4Infra.h10Sub_toH1Function, PDE.H1Function.sub_toFun, Pi.sub_apply,
      hφ₀, hφε, mul_sub]
  · simp only [PDE.Ch4Infra.h10Sub_toH1Function, PDE.H1Function.sub_grad, hg₀, hgε]

#print axioms spectral_finite_lift_level_ramp_test

/-- The elliptic energy of the difference of two selected truncation
    gradients is nonnegative on an arbitrary open set. -/
theorem posPartGrad_level_difference_energy_nonneg {n : ℕ} {U : Set (PDE.Vec n)}
    (w : PDE.H1Function U) {ε Λ : ℝ} (hε : 0 < ε) {A : PDE.Mat n}
    (hA : PDE.IsEllipticMatrix 1 Λ A) (z : PDE.Vec n) :
    0 ≤ PDE.vecDot (PDE.matVecMul A (w.grad z))
      (PDE.Ch4Infra.posPartGrad w 0 z - PDE.Ch4Infra.posPartGrad w ε z) := by
  have hE : 0 ≤ PDE.vecDot (PDE.matVecMul A (w.grad z)) (w.grad z) := by
    rw [PDE.vecDot_comm]
    exact PDE.DGNM.vecDot_matVecMul_self_nonneg hA _
  by_cases h1 : ε < w.toFun z
  · have h0 : 0 < w.toFun z := lt_trans hε h1
    simp [PDE.Ch4Infra.posPartGrad, h0, h1, PDE.DGNM.vecDot_zero_right]
  · by_cases h0 : 0 < w.toFun z
    · simpa [PDE.Ch4Infra.posPartGrad, h0, h1] using hE
    · simp [PDE.Ch4Infra.posPartGrad, h0, h1, PDE.DGNM.vecDot_zero_right]

#print axioms posPartGrad_level_difference_energy_nonneg

/-- Both terms in the ramp product rule pair integrably with an L² flux,
    and their integrals recover the pairing with the cutoff test gradient. -/
theorem level_difference_cutoff_flux_split {n : ℕ} {U : Set (PDE.Vec n)}
    (hU : IsOpen U) (w : PDE.H1Function U) {ε : ℝ} (hε : 0 < ε)
    {F : PDE.Vec n → PDE.Vec n} (hF : PDE.MemVectorL2On U F)
    {η : PDE.Vec n → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (φ : PDE.H10Function U)
    (hφ : φ.toH1Function.grad = fun z =>
      (η z • PDE.Ch4Infra.posPartGrad w 0 z +
        max (w.toFun z) 0 • PDE.classicalGradient η z) -
      (η z • PDE.Ch4Infra.posPartGrad w ε z +
        max (w.toFun z - ε) 0 • PDE.classicalGradient η z)) :
    IntegrableOn (fun z => η z * PDE.vecDot (F z)
      (PDE.Ch4Infra.posPartGrad w 0 z - PDE.Ch4Infra.posPartGrad w ε z)) U ∧
    IntegrableOn (fun z => (max (w.toFun z) 0 - max (w.toFun z - ε) 0) *
      PDE.vecDot (F z) (PDE.classicalGradient η z)) U ∧
    (∫ z in U, PDE.vecDot (F z) (φ.toH1Function.grad z)) =
      (∫ z in U, η z * PDE.vecDot (F z)
        (PDE.Ch4Infra.posPartGrad w 0 z - PDE.Ch4Infra.posPartGrad w ε z)) +
      ∫ z in U, (max (w.toFun z) 0 - max (w.toFun z - ε) 0) *
        PDE.vecDot (F z) (PDE.classicalGradient η z) := by
  let v₀ := PDE.Ch4Infra.positivePartOpen hU w 0
    (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w le_rfl)
  let vε := PDE.Ch4Infra.positivePartOpen hU w ε
    (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w hε.le)
  let v := v₀ - vε
  have hηTop : PDE.MemLpOn U ⊤ η := PDE.DGNM.memLpOn_top_of_contDiff hη hηc
  have hDηTop (i : Fin n) : PDE.MemLpOn U ⊤ (fun z => PDE.classicalGradient η z i) :=
    PDE.DGNM.memLpOn_top_classicalGradient hη hηc i
  have hA : PDE.MemVectorL2On U (fun z => η z • v.grad z) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using (v.gradMemL2 i).fun_mul hηTop
  have hB : PDE.MemVectorL2On U (fun z => v.toFun z • PDE.classicalGradient η z) := by
    intro i
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using v.memL2.fun_mul (hDηTop i)
  have hAint := PDE.integrableOn_vecDot_of_memVectorL2On hF hA
  have hBint := PDE.integrableOn_vecDot_of_memVectorL2On hF hB
  simp only [PDE.DGNM.vecDot_smul_right] at hAint hBint
  have hv : ∀ z, v.toFun z = max (w.toFun z) 0 - max (w.toFun z - ε) 0 := by
    intro z
    simp [v, v₀, vε, PDE.Ch4Infra.positivePartOpen]
  have hvg : ∀ z, v.grad z = PDE.Ch4Infra.posPartGrad w 0 z -
      PDE.Ch4Infra.posPartGrad w ε z := by
    intro z
    rfl
  simp only [hv, hvg] at hAint hBint
  refine ⟨hAint, hBint, ?_⟩
  rw [← integral_add hAint hBint]
  apply integral_congr_ae
  filter_upwards with z
  rw [hφ]
  have hsub (x y t : PDE.Vec n) : PDE.vecDot x (y - t) =
      PDE.vecDot x y - PDE.vecDot x t := by
    simp only [PDE.vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  simp only [hsub, PDE.DGNM.vecDot_add_right, PDE.DGNM.vecDot_smul_right]
  ring

#print axioms level_difference_cutoff_flux_split

/-- The actual finite spectral lift has nonpositive cutoff flux against
    every unscaled zero-level ramp. -/
theorem spectral_finite_lift_level_ramp_flux_nonpos {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (hfin : volume ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q) ≠ ⊤)
    {K : Set ℝ} (hK : IsCompact K)
    (hslab : ∀ z ∈ Q, (productCoordinates z).2 ∈ K) :
    ∃ w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      w.toFun = (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ {η : PDE.Vec (d + 1) → ℝ},
        ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Q →
        (∀ z, 0 ≤ η z) →
        (∫ z in ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
          (max (w.toFun z) 0 - max (w.toFun z - ε) 0) *
            PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
              (w.grad z)) (PDE.classicalGradient η z)) ≤ 0 := by
  let Ω : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hΩ : IsOpen Ω := ((dirichletBall (d := d) R).isOpen.preimage hp).inter hQ
  have hsub : Ω ⊆ productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ K) := by
    intro z hz
    exact ⟨hz.1, hslab z hz.2⟩
  obtain ⟨w, hw, hg, hsol⟩ :=
    spectral_finite_coordinate_lift_solution hκ h s hK hΩ hsub I a
  refine ⟨w, hw, ?_⟩
  intro ε hε η hη hηc hηQ hη0
  obtain ⟨φ, hφval, hφgrad⟩ :=
    spectral_finite_lift_level_ramp_test s I a hQ hfin w hw hε hη hηc hηQ
  have ha (i j : Fin (d + 1)) : AEMeasurable
      (fun z => normalizedCoordinateLiftedMatrix κ ρ α z i j) (PDE.volumeOn Ω) :=
    (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable
  have hell : ∀ z ∈ Ω, PDE.IsEllipticMatrix 1 ((κ ^ 4)⁻¹)
      (normalizedCoordinateLiftedMatrix κ ρ α z) :=
    fun z _ => normalizedCoordinateLiftedMatrix_elliptic hκ h z
  have hflux := PDE.DGNM.memVectorL2On_matVecMul_of_aemeasurable
    hΩ.measurableSet ha hell w.gradMemL2
  obtain ⟨b, hb, hab⟩ := PDE.exists_isEllipticFieldOn_coeffAEEqOn hΩ.measurableSet ha hell
  have hsolb := hsol.of_ae_eq_coeff hab
  have ht := hsolb.toH10SolutionOn_of_isEllipticFieldOn hb
    (MeasureTheory.MemLp.zero) (by
      intro i
      simpa only [Pi.zero_apply] using!
        (MeasureTheory.MemLp.zero : PDE.MemL2On Ω (0 : PDE.Vec (d + 1) → ℝ)))
  have hbzero : (∫ z in Ω, PDE.vecDot (PDE.matVecMul (b z) (w.grad z))
      (φ.toH1Function.grad z)) = 0 := by
    simpa [PDE.DGNM.vecDot_zero_left] using (ht φ).2
  have hazero : (∫ z in Ω, PDE.vecDot
      (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z) (w.grad z))
      (φ.toH1Function.grad z)) = 0 := by
    calc
      _ = ∫ z in Ω, PDE.vecDot (PDE.matVecMul (b z) (w.grad z))
          (φ.toH1Function.grad z) := by
            apply integral_congr_ae
            filter_upwards [hab] with z hz
            rw [hz]
      _ = 0 := hbzero
  obtain ⟨hAint, hBint, hsplit⟩ :=
    level_difference_cutoff_flux_split hΩ w hε hflux hη hηc φ hφgrad
  have henergy : 0 ≤ ∫ z in Ω, η z * PDE.vecDot
      (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z) (w.grad z))
      (PDE.Ch4Infra.posPartGrad w 0 z - PDE.Ch4Infra.posPartGrad w ε z) := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem hΩ.measurableSet] with z hz
    exact mul_nonneg (hη0 z) (posPartGrad_level_difference_energy_nonneg w hε (hell z hz) z)
  linarith

#print axioms spectral_finite_lift_level_ramp_flux_nonpos


/-- The zero-level flux inequality for an actual finite spectral lift. -/
theorem spectral_finite_lift_positive_flux_nonpos {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (hfin : volume ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q) ≠ ⊤)
    {K : Set ℝ} (hK : IsCompact K)
    (hslab : ∀ z ∈ Q, (productCoordinates z).2 ∈ K) :
    ∃ w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      w.toFun = (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) z) ∧
      ∀ {η : PDE.Vec (d + 1) → ℝ},
        ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η → tsupport η ⊆ Q →
        (∀ z, 0 ≤ η z) →
        (∫ z in ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
          {y | 0 < w.toFun y}.indicator (fun _ => (1 : ℝ)) z *
            PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
              (w.grad z)) (PDE.classicalGradient η z)) ≤ 0 := by
  let Ω : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hΩ : IsOpen Ω := ((dirichletBall (d := d) R).isOpen.preimage hp).inter hQ
  letI : IsFiniteMeasure (PDE.volumeOn Ω) := ⟨by simpa [PDE.volumeOn, Ω] using hfin.lt_top⟩
  obtain ⟨w, hw, hcut⟩ := spectral_finite_lift_level_ramp_flux_nonpos hκ h s I a hQ hfin hK hslab
  refine ⟨w, hw, ?_⟩
  intro η hη hηc hηQ hη0
  have ha (i j : Fin (d + 1)) : AEMeasurable
      (fun z => normalizedCoordinateLiftedMatrix κ ρ α z i j) (PDE.volumeOn Ω) :=
    (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable
  have hell : ∀ z ∈ Ω, PDE.IsEllipticMatrix 1 ((κ ^ 4)⁻¹)
      (normalizedCoordinateLiftedMatrix κ ρ α z) :=
    fun z _ => normalizedCoordinateLiftedMatrix_elliptic hκ h z
  have hflux := PDE.DGNM.memVectorL2On_matVecMul_of_aemeasurable
    hΩ.measurableSet ha hell w.gradMemL2
  have hDη : PDE.MemVectorL2On Ω (PDE.classicalGradient η) := by
    intro i
    exact (PDE.DGNM.memLpOn_top_classicalGradient hη hηc i).mono_exponent le_top
  have hfluxInt := PDE.integrableOn_vecDot_of_memVectorL2On hflux hDη
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  let v (n : ℕ) : PDE.H1Function Ω := (ε n)⁻¹ •
    (PDE.Ch4Infra.positivePartOpen hΩ w 0
      (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w le_rfl) -
     PDE.Ch4Infra.positivePartOpen hΩ w (ε n)
      (PDE.Ch4Infra.memL2On_positivePart_of_nonneg w (hε n).le))
  have hv (n : ℕ) (z : PDE.Vec (d + 1)) : (v n).toFun z =
      (ε n)⁻¹ * (max (w.toFun z) 0 - max (w.toFun z - ε n) 0) := by
    simp [v, PDE.Ch4Infra.positivePartOpen]
  have h0 (n : ℕ) (z : PDE.Vec (d + 1)) : 0 ≤ (v n).toFun z := by
    rw [hv]
    apply mul_nonneg (inv_nonneg.mpr (hε n).le)
    have : max (w.toFun z - ε n) 0 ≤ max (w.toFun z) 0 :=
      max_le_max (by linarith [hε n]) le_rfl
    linarith
  have h1 (n : ℕ) (z : PDE.Vec (d + 1)) : (v n).toFun z ≤ 1 := by
    rw [hv]
    have hd : max (w.toFun z) 0 - max (w.toFun z - ε n) 0 ≤ ε n := by
      rcases le_total (w.toFun z) 0 with hz | hz
      · rw [max_eq_right hz, max_eq_right (by linarith [hε n])]
        linarith [hε n]
      · rw [max_eq_left hz]
        have := le_max_left (w.toFun z - ε n) 0
        linarith
    calc (ε n)⁻¹ * (max (w.toFun z) 0 - max (w.toFun z - ε n) 0) ≤
        (ε n)⁻¹ * ε n := mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (hε n).le)
      _ = 1 := inv_mul_cancel₀ (hε n).ne'
  have ht (z : PDE.Vec (d + 1)) : Tendsto (fun n => (v n).toFun z) atTop
      (nhds ({y | 0 < w.toFun y}.indicator (fun _ => (1 : ℝ)) z)) := by
    by_cases hz : 0 < w.toFun z
    · have hm : z ∈ {y | 0 < w.toFun y} := hz
      rw [Set.indicator_of_mem hm]
      obtain ⟨N, hN⟩ := exists_nat_one_div_lt hz
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop N] with n hn
      have hεle : ε n ≤ 1 / ((N : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
      rw [hv, max_eq_left (by linarith), max_eq_left (by linarith)]
      field_simp [(hε n).ne']
      ring
    · have hm : z ∉ {y | 0 < w.toFun y} := hz
      rw [Set.indicator_of_notMem hm]
      apply tendsto_const_nhds.congr'
      filter_upwards with n
      rw [hv, max_eq_right (by linarith [not_lt.mp hz]),
        max_eq_right (by linarith [not_lt.mp hz, hε n])]
      ring
  have hstep (n : ℕ) : ∫ z in Ω, (v n).toFun z *
      PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
        (w.grad z)) (PDE.classicalGradient η z) ≤ 0 := by
    have hh := mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (hε n).le)
      (hcut (hε n) hη hηc hηQ hη0)
    rw [← integral_const_mul] at hh
    convert hh using 1
    apply integral_congr_ae
    filter_upwards with z
    rw [hv]
    ring
  have hlim : Tendsto (fun n => ∫ z in Ω, (v n).toFun z *
      PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
        (w.grad z)) (PDE.classicalGradient η z)) atTop
      (nhds (∫ z in Ω, {y | 0 < w.toFun y}.indicator (fun _ => (1 : ℝ)) z *
        PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
          (w.grad z)) (PDE.classicalGradient η z))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun z => |PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
        (w.grad z)) (PDE.classicalGradient η z)|) ?_ hfluxInt.abs ?_ ?_
    · intro n
      exact (v n).memL2.aestronglyMeasurable.mul hfluxInt.aestronglyMeasurable
    · intro n
      filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 n z)]
      exact mul_le_of_le_one_left (abs_nonneg _) (h1 n z)
    · filter_upwards with z
      exact (ht z).mul_const _
  exact le_of_tendsto' hlim hstep

#print axioms spectral_finite_lift_positive_flux_nonpos

/-- The weak gradient chosen for the interior lift agrees almost everywhere
with the literal gradient of the zero-extended lift in the source cylinder. -/
theorem spectral_finite_lift_gradient_ae_zeroExtension {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    {K : Set ℝ} (hK : IsCompact K)
    (hslab : ∀ z ∈ Q, (productCoordinates z).2 ∈ K)
    (w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q))
    (hw : w.toFun = fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) :
    w.grad =ᵐ[PDE.volumeOn ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q)]
      fun z => ∑ i ∈ I, a i • liftedGradient
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
        (Real.sqrt (s.eigenvalue i)) z := by
  let Ω : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q
  have hp : Continuous (fun z : PDE.Vec (d + 1) => (productCoordinates z).1) :=
    (productCoordinates (d := d)).continuous.fst
  have hΩ : IsOpen Ω := ((dirichletBall (d := d) R).isOpen.preimage hp).inter hQ
  have hsub : Ω ⊆ productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ K) := by
    intro z hz
    exact ⟨hz.1, hslab z hz.2⟩
  obtain ⟨v, hv, hvgrad, _⟩ := spectral_finite_coordinate_lift_solution hκ h s hK hΩ hsub I a
  have heq : w.toFun = v.toFun := hw.trans hv.symm
  have hcoord : ∀ j : Fin (d + 1), ∀ᵐ z ∂PDE.volumeOn Ω, w.grad z j = v.grad z j :=
    fun j => PDE.H1Function.grad_coord_ae_eq_of_toFun_eq hΩ w v heq j
  filter_upwards [Filter.eventually_all.2 hcoord, ae_restrict_mem hΩ.measurableSet] with z hz hzΩ
  have hgrad : w.grad z = v.grad z := funext hz
  have hzin : (productCoordinates z).1 ∈ sourceBall (0 : PDE.Vec d) R := hzΩ.1
  rw [hgrad, hvgrad]
  apply Finset.sum_congr rfl
  intro i hi
  change a i • liftedGradient (s.eigenfunction i) (s.gradient i)
      (Real.sqrt (s.eigenvalue i)) z =
    a i • liftedGradient ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
      (Real.sqrt (s.eigenvalue i)) z
  apply congrArg (fun v : PDE.Vec (d + 1) => a i • v)
  funext j
  induction j using Fin.lastCases with
  | last =>
    simp only [liftedGradient, Fin.lastCases_last]
    rw [Set.indicator_of_mem hzin]
  | cast j =>
    simp only [liftedGradient, Fin.lastCases_castSucc]
    rw [Set.indicator_of_mem hzin]

#print axioms spectral_finite_lift_gradient_ae_zeroExtension

/-- The positive part of the actual zero-extended lift is subharmonic. -/
theorem spectral_finite_zeroExtension_positive_subharmonic {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R)
    {B : Set (PDE.Vec d)} (hB : MeasurableSet B) (hBfinite : volume B ≠ ∞)
    {K : Set ℝ} (hK : IsCompact K) {Q : Set (PDE.Vec (d + 1))}
    (hQ : PDE.IsOpenBoundedConvexDomain Q)
    (hsub : Q ⊆ productCoordinates ⁻¹' (B ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    let F := fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z
    let G := fun z => ∑ i ∈ I, a i • liftedGradient
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
      (Real.sqrt (s.eigenvalue i)) z
    ∃ p : PDE.H1Function Q,
      p.toFun = (fun z => max (F z) 0) ∧
      p.grad = (fun z => {y | 0 < F y}.indicator G z) ∧
      PDE.IsWeakDivergenceFormSubharmonicOn (normalizedCoordinateLiftedMatrix κ ρ α) Q p := by
  classical
  let F := fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z
  let G := fun z => ∑ i ∈ I, a i • liftedGradient
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
      (Real.sqrt (s.eigenvalue i)) z
  let Ω : Set (PDE.Vec (d + 1)) := {z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q
  have hΩ : IsOpen Ω :=
    ((dirichletBall (d := d) R).isOpen.preimage
      (productCoordinates (d := d)).continuous.fst).inter hQ.isOpen
  have hfin : volume Ω ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
      (hQ.isBoundedDomain.isBounded.measure_lt_top (μ := volume))).ne
  have hslab : ∀ z ∈ Q, (productCoordinates z).2 ∈ K := fun z hz => (hsub hz).2
  obtain ⟨p, n, hp, hpg, hn, hng⟩ :=
    spectral_finite_zeroExtension_signedParts_H1 hκ h s hB hBfinite hK hQ hsub I a
  change p.grad = (fun z => {y | 0 < F y}.indicator G z) at hpg
  obtain ⟨w, hw, hflux⟩ := spectral_finite_lift_positive_flux_nonpos hκ h s I a
    hQ.isOpen hfin hK hslab
  have hwgrad : w.grad =ᵐ[PDE.volumeOn Ω] G :=
    spectral_finite_lift_gradient_ae_zeroExtension hκ h s I a hQ.isOpen hK hslab w hw
  have hval (z : PDE.Vec (d + 1)) (hz : z ∈ Ω) : F z = w.toFun z := by
    have hz' : (productCoordinates z).1 ∈ sourceBall (0 : PDE.Vec d) R := hz.1
    rw [hw]
    dsimp only [F]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [liftedValue]
    rw [Set.indicator_of_mem hz']
  have hzero (z : PDE.Vec (d + 1)) (hz : z ∈ Q \ Ω) : F z = 0 := by
    have hz' : (productCoordinates z).1 ∉ sourceBall (0 : PDE.Vec d) R := by
      intro hzin
      exact hz.2 ⟨hzin, hz.1⟩
    dsimp only [F]
    apply Finset.sum_eq_zero
    intro i hi
    dsimp only [liftedValue]
    rw [Set.indicator_of_notMem hz']
    ring
  refine ⟨p, hp, hpg, ?_⟩
  rw [PDE.DGNM.subharmonicOn_iff]
  intro φ hφ
  have ha (i j : Fin (d + 1)) : AEMeasurable
      (fun z => normalizedCoordinateLiftedMatrix κ ρ α z i j) (PDE.volumeOn Q) :=
    (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable
  have hell : ∀ z ∈ Q, PDE.IsEllipticMatrix 1 ((κ ^ 4)⁻¹)
      (normalizedCoordinateLiftedMatrix κ ρ α z) :=
    fun z _ => normalizedCoordinateLiftedMatrix_elliptic hκ h z
  have hi := PDE.integrableOn_vecDot_of_memVectorL2On
    (PDE.DGNM.memVectorL2On_matVecMul_of_aemeasurable hQ.measurableSet ha hell p.gradMemL2)
    φ.grad_memVectorL2On
  refine ⟨hi, ?_⟩
  have htest : φ.grad = PDE.classicalGradient φ.toFun := rfl
  have hc := hflux φ.contDiff φ.hasCompactSupport φ.tsupport_subset hφ
  calc
    (∫ z in Q, PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
        (p.grad z)) (φ.grad z)) =
      ∫ z in Ω, PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
        (p.grad z)) (φ.grad z) := by
      apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
        hQ.measurableSet Set.inter_subset_right
      intro z hz
      have hzF := hzero z hz
      rw [hpg]
      dsimp only
      have hznot : z ∉ {y | 0 < F y} := by simp only [Set.mem_setOf_eq, hzF, lt_self_iff_false, not_false_eq_true]
      rw [Set.indicator_of_notMem hznot, PDE.DGNM.matVecMul_zero', PDE.DGNM.vecDot_zero_left]
    _ = ∫ z in Ω, {y | 0 < w.toFun y}.indicator (fun _ => (1 : ℝ)) z *
        PDE.vecDot (PDE.matVecMul (normalizedCoordinateLiftedMatrix κ ρ α z)
          (w.grad z)) (PDE.classicalGradient φ.toFun z) := by
      apply integral_congr_ae
      filter_upwards [hwgrad, ae_restrict_mem hΩ.measurableSet] with z hzgrad hzΩ
      rw [hpg, htest]
      dsimp only
      have hv := hval z hzΩ
      by_cases hz : 0 < w.toFun z
      · have hpz : z ∈ {y | 0 < F y} := by simpa only [Set.mem_setOf_eq, hv] using hz
        have hwz : z ∈ {y | 0 < w.toFun y} := hz
        rw [Set.indicator_of_mem hpz, Set.indicator_of_mem hwz, one_mul, ← hzgrad]
      · have hpz : z ∉ {y | 0 < F y} := by simpa only [Set.mem_setOf_eq, hv] using hz
        have hwz : z ∉ {y | 0 < w.toFun y} := hz
        rw [Set.indicator_of_notMem hpz, Set.indicator_of_notMem hwz,
          PDE.DGNM.matVecMul_zero', PDE.DGNM.vecDot_zero_left, zero_mul]
    _ ≤ 0 := hc

#print axioms spectral_finite_zeroExtension_positive_subharmonic

/-- Both signed parts of the actual zero extension are subharmonic with their
literal selected weak gradients. -/
theorem spectral_finite_zeroExtension_signedParts_subharmonic {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R)
    {B : Set (PDE.Vec d)} (hB : MeasurableSet B) (hBfinite : volume B ≠ ∞)
    {K : Set ℝ} (hK : IsCompact K) {Q : Set (PDE.Vec (d + 1))}
    (hQ : PDE.IsOpenBoundedConvexDomain Q)
    (hsub : Q ⊆ productCoordinates ⁻¹' (B ×ˢ K))
    (I : Finset ℕ) (a : ℕ → ℝ) :
    let F := fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z
    let G := fun z => ∑ i ∈ I, a i • liftedGradient
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
      (Real.sqrt (s.eigenvalue i)) z
    ∃ p n : PDE.H1Function Q,
      p.toFun = (fun z => max (F z) 0) ∧
      p.grad = (fun z => {y | 0 < F y}.indicator G z) ∧
      n.toFun = (fun z => max (-F z) 0) ∧
      n.grad = (fun z => {y | F y < 0}.indicator (-G) z) ∧
      PDE.IsWeakDivergenceFormSubharmonicOn (normalizedCoordinateLiftedMatrix κ ρ α) Q p ∧
      PDE.IsWeakDivergenceFormSubharmonicOn (normalizedCoordinateLiftedMatrix κ ρ α) Q n := by
  obtain ⟨p, hp, hpg, hps⟩ := spectral_finite_zeroExtension_positive_subharmonic
    hκ h s hB hBfinite hK hQ hsub I a
  obtain ⟨n, hn, hng, hns⟩ := spectral_finite_zeroExtension_positive_subharmonic
    hκ h s hB hBfinite hK hQ hsub I (fun i => -a i)
  refine ⟨p, n, hp, hpg, ?_, ?_, hps, hns⟩
  · simpa only [neg_mul, Finset.sum_neg_distrib] using hn
  · have hGneg : (fun z => ∑ i ∈ I, (-a i) • liftedGradient
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
        (Real.sqrt (s.eigenvalue i)) z) =
      -(fun z => ∑ i ∈ I, a i • liftedGradient
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.gradient i))
        (Real.sqrt (s.eigenvalue i)) z) := by
      funext z
      simp only [Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hGneg] at hng
    simpa only [neg_mul, Finset.sum_neg_distrib, neg_pos] using hng

#print axioms spectral_finite_zeroExtension_signedParts_subharmonic

/-- Moser's center estimate for both signed parts of the actual finite
zero-extended lift, uniformly over all spatial centers and positive radii. -/
theorem spectral_finite_zeroExtension_signedParts_center_moser {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (r : ℝ), 0 < r → ∀ (x : PDE.Vec d)
      (I : Finset ℕ) (a : ℕ → ℝ),
      let z := productCoordinates.symm (x, 0)
      let F := fun y => ∑ i ∈ I, a i * liftedValue
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        (Real.sqrt (s.eigenvalue i)) y
      let A := ENNReal.ofReal (C * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 2) *
        (2 : ℝ) ^ ((d + 1 : ℕ) : ℝ))
      let J := ENNReal.ofReal ((r ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
      (ENNReal.ofReal (max (F z) 0)) ^ (2 : ℝ) ≤
        A * (J * eLpNorm (fun y => max (F y) 0) 2
          (PDE.volumeOn (PDE.euclideanBall z r))) ^ (2 : ℝ) ∧
      (ENNReal.ofReal (max (-F z) 0)) ^ (2 : ℝ) ≤
        A * (J * eLpNorm (fun y => max (-F y) 0) 2
          (PDE.volumeOn (PDE.euclideanBall z r))) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hmoser⟩ := pde_continuous_subharmonic_ball_center_moser (n := d + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro r hr x I a
  let z := productCoordinates.symm (x, 0)
  let Q := PDE.euclideanBall z r
  let F := fun y => ∑ i ∈ I, a i * liftedValue
    ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
    (Real.sqrt (s.eigenvalue i)) y
  have hB : MeasurableSet (sourceBall x r) := by
    rw [← pde_ball_eq_sourceBall x hr]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  obtain ⟨p, n, hp, _, hn, _, hps, hns⟩ :=
    spectral_finite_zeroExtension_signedParts_subharmonic hκ h s hB
      (volume_spatial_euclidean_ball_ne_top x r) isCompact_Icc
      (PDE.isOpenBoundedConvexDomain_euclideanBall z hr)
      (coordinate_ball_subset_spatial_cylinder x hr) I a
  have hc : Continuous F := spectral_finite_zeroExtension_lift_continuous s I a
  have ha (i j : Fin (d + 1)) : AEMeasurable
      (fun y => normalizedCoordinateLiftedMatrix κ ρ α y i j) (PDE.volumeOn Q) :=
    (normalizedCoordinateLiftedMatrix_measurable h i j).aemeasurable
  have hell : ∀ y ∈ Q, PDE.IsEllipticMatrix 1 ((κ ^ 4)⁻¹)
      (normalizedCoordinateLiftedMatrix κ ρ α y) :=
    fun y _ => normalizedCoordinateLiftedMatrix_elliptic hκ h y
  have hpcont : Continuous p.toFun := by rw [hp]; exact hc.max continuous_const
  have hncont : Continuous n.toFun := by rw [hn]; exact hc.neg.max continuous_const
  have hpbound := hmoser ((κ ^ 4)⁻¹) r hr z _ ha hell p hps hpcont
  have hnbound := hmoser ((κ ^ 4)⁻¹) r hr z _ ha hell n hns hncont
  rw [hp] at hpbound
  rw [hn] at hnbound
  exact ⟨hpbound, hnbound⟩

#print axioms spectral_finite_zeroExtension_signedParts_center_moser

/-- The negative part of the same finite spectral lift also admits a
zero-boundary cutoff test, with its exact weak gradient. -/
theorem spectral_finite_lift_negative_zero_level_test {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    {Q : Set (PDE.Vec (d + 1))} (hQ : IsOpen Q)
    (hfin : volume ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q) ≠ ⊤)
    (w : PDE.H1Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q))
    (hw : w.toFun = fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z)
    {η : PDE.Vec (d + 1) → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηQ : tsupport η ⊆ Q) :
    ∃ φ : PDE.H10Function ({z | (productCoordinates z).1 ∈ sourceBall 0 R} ∩ Q),
      (∀ z, φ.toH1Function.toFun z = η z * max (-w.toFun z) 0) ∧
      φ.toH1Function.grad = fun z => η z • PDE.Ch4Infra.posPartGrad (-w) 0 z +
        max (-w.toFun z) 0 • PDE.classicalGradient η z := by
  have hwneg : (-w).toFun = fun z => ∑ i ∈ I, (-a i) * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z := by
    funext z
    simp only [PDE.H1Function.neg_toFun, Pi.neg_apply, hw, Finset.sum_neg_distrib, neg_mul]
  obtain ⟨φ, hφ, hg⟩ := spectral_finite_lift_zero_level_test s I (fun i => -a i)
    hQ hfin (-w) hwneg hη hηc hηQ
  refine ⟨φ, ?_, ?_⟩
  · intro z
    simpa only [PDE.H1Function.neg_toFun, Pi.neg_apply] using hφ z
  · simpa only [PDE.H1Function.neg_toFun, Pi.neg_apply] using hg

#print axioms spectral_finite_lift_negative_zero_level_test

/-- A continuous weak solution itself satisfies the quantitative ball Moser bound. -/
theorem pde_continuous_ball_moser_quantitative {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 1 ≤ Λ → 0 < R → ∀ (z : PDE.Vec n)
      (a : PDE.CoeffField n), (∀ i j, Measurable (fun x => a x i j)) →
      (∀ x ∈ PDE.euclideanBall z R, PDE.IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : PDE.H1Function (PDE.euclideanBall z R),
      PDE.IsWeakDivergenceFormSolutionOn a (PDE.euclideanBall z R) u 0 0 →
      ContinuousOn u.toFun (PDE.euclideanBall z (R / 2)) →
      ∀ x ∈ PDE.euclideanBall z (R / 2),
        ENNReal.ofReal |u.toFun x| ≤ ENNReal.ofReal R *
          (ENNReal.ofReal (C * Λ ^ ((n : ℝ) / 4) * (2 : ℝ) ^ ((n : ℝ) / 2)) *
            (ENNReal.ofReal R⁻¹ *
              (ENNReal.ofReal ((R ^ n)⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
                eLpNorm u.toFun 2 (volume.restrict (PDE.euclideanBall z R))))) := by
  obtain ⟨C, hC, h⟩ := pde_ball_moser_quantitative hn
  refine ⟨C, hC, ?_⟩
  intro Λ R hΛ hR z a ha hell u hsol hu x hx
  obtain ⟨v, hv, hae, hb⟩ := h Λ R hΛ hR z a ha hell u hsol
  have heq : Set.EqOn v u.toFun (PDE.euclideanBall z (R / 2)) :=
    Measure.eqOn_open_of_ae_eq hae (PDE.isOpen_euclideanBall _ _) hv hu
  rw [← heq hx]
  exact hb x hx

#print axioms pde_continuous_ball_moser_quantitative

/-- The finite spectral sum obeys the quantitative Moser estimate at every
interior point, with a constant independent of the finite spectral cutoff. -/
theorem spectral_finite_sum_moser_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r q : ℝ} (hR : 0 < R) (hq : 0 < q) (hmargin : r + 4 * q ≤ R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (I : Finset ℕ) (a : ℕ → ℝ) (x : PDE.Vec d),
      x ∈ sourceBall 0 r →
      ENNReal.ofReal |∑ i ∈ I, a i * s.eigenfunction i x| ≤
        ENNReal.ofReal (4 * q) *
          (ENNReal.ofReal (C * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 4) *
            (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 2)) *
            (ENNReal.ofReal (4 * q)⁻¹ *
              (ENNReal.ofReal (((4 * q) ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
                eLpNorm (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
                  (Real.sqrt (s.eigenvalue i)) z) 2
                  (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0))
                    (4 * q)))))) := by
  obtain ⟨C, hC, hmoser⟩ := pde_continuous_ball_moser_quantitative (n := d + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro I a x hx
  let z : PDE.Vec (d + 1) := productCoordinates.symm (x, 0)
  have hΛ : 1 ≤ (κ ^ 4)⁻¹ :=
    (one_le_inv₀ (pow_pos hκ 4)).2
      (pow_le_one₀ hκ.le (lifted_ellipticity_scale_comparison hκ h).1)
  have hsub : PDE.euclideanBall z (4 * q) ⊆
      productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-R) R) :=
    (coordinate_interior_ball_subset 0 hR hq hmargin hx).trans
      (coordinate_ball_subset_spatial_cylinder 0 hR)
  obtain ⟨w, hw, _, hsol⟩ := spectral_finite_coordinate_lift_solution hκ h s
    isCompact_Icc (PDE.isOpen_euclideanBall z (4 * q)) hsub I a
  have hcont : ContinuousOn w.toFun (PDE.euclideanBall z ((4 * q) / 2)) := by
    rw [hw]
    apply spectral_finite_lift_continuousOn s I a
    intro y hy
    apply (hsub ?_).1
    exact PDE.euclideanBall_mono (by positivity) (by linarith) hy
  have hb := hmoser (κ ^ 4)⁻¹ (4 * q) hΛ (by positivity) z
    (normalizedCoordinateLiftedMatrix κ ρ α) (normalizedCoordinateLiftedMatrix_measurable h)
    (fun y _ => normalizedCoordinateLiftedMatrix_elliptic hκ h y) w hsol hcont z
    (PDE.center_mem_euclideanBall z (by positivity))
  rw [hw] at hb
  simpa [z, liftedValue] using hb

#print axioms spectral_finite_sum_moser_bound

/-- The lifted finite sum has a uniform (L^2) bound on every interior ball. -/
theorem spectral_finite_lift_interior_eLpNorm_le {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r q : ℝ} (hR : 0 < R) (hq : 0 < q) (hmargin : r + 4 * q ≤ R)
    (s : DirichletSpectralResolution ρ α R) (I : Finset ℕ) (a : ℕ → ℝ)
    (E : ℝ) (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E)
    {x : PDE.Vec d} (hx : x ∈ sourceBall 0 r) :
    eLpNorm (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) 2
      (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) (4 * q))) ≤
      ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
        Real.sqrt (∑ i ∈ I, (a i) ^ 2)) := by
  let z : PDE.Vec (d + 1) := productCoordinates.symm (x, 0)
  have hsub : PDE.euclideanBall z (4 * q) ⊆
      productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-R) R) :=
    (coordinate_interior_ball_subset 0 hR hq hmargin hx).trans
      (coordinate_ball_subset_spatial_cylinder 0 hR)
  obtain ⟨w, hw, _, _⟩ := spectral_finite_coordinate_lift_solution hκ h s
    isCompact_Icc (PDE.isOpen_euclideanBall z (4 * q)) hsub I a
  have hm := w.memL2
  rw [hw] at hm
  have hi := spectral_lift_interior_ball_integral_le hκ h hR hq hmargin s I a E hcut hx
  have hi' : (∫ y in PDE.euclideanBall z (4 * q),
      (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) y) ^ 2) ≤
      (2 * R / κ) * (Real.exp (Real.sqrt E * R) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
    have ht := (le_div_iff₀ hκ).2 (show
      (∫ y in PDE.euclideanBall z (4 * q),
        (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
          (Real.sqrt (s.eigenvalue i)) y) ^ 2) * κ ≤
        (2 * R) * (Real.exp (Real.sqrt E * R) ^ 2 * ∑ i ∈ I, (a i) ^ 2) by
      simpa only [mul_comm] using hi)
    convert ht using 1 <;> ring
  rw [PDE.DGNMOneStep.eLpNorm_two_eq_ofReal_sqrt hm]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt ((2 * R / κ) *
        (Real.exp (Real.sqrt E * R) ^ 2 * ∑ i ∈ I, (a i) ^ 2)) := Real.sqrt_le_sqrt hi'
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring

#print axioms spectral_finite_lift_interior_eLpNorm_le

/-- The finite spectral lift has the same uniform L² estimate on any open
subset of the cylinder, including boundary patches inside the source ball. -/
theorem spectral_finite_lift_subset_eLpNorm_le {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R b : ℝ} (hb : 0 ≤ b) (s : DirichletSpectralResolution ρ α R)
    {Ω : Set (PDE.Vec (d + 1))} (hΩ : IsOpen Ω)
    (hsub : Ω ⊆ productCoordinates ⁻¹' (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-b) b))
    (I : Finset ℕ) (a : ℕ → ℝ) (E : ℝ)
    (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) :
    eLpNorm (fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) z) 2 (volume.restrict Ω) ≤
      ENNReal.ofReal (Real.sqrt (2 * b / κ) * Real.exp (Real.sqrt E * b) *
        Real.sqrt (∑ i ∈ I, (a i) ^ 2)) := by
  obtain ⟨w, hw, _, _⟩ := spectral_finite_coordinate_lift_solution hκ h s
    isCompact_Icc hΩ hsub I a
  have hm := w.memL2
  rw [hw] at hm
  have hi := spectral_lift_subset_integral_le hκ h s I a E b hb hcut hsub
  have hi' : (∫ y in Ω, (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
      (Real.sqrt (s.eigenvalue i)) y) ^ 2) ≤
      (2 * b / κ) * (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) := by
    have ht := (le_div_iff₀ hκ).2 (show
      (∫ y in Ω, (∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
        (Real.sqrt (s.eigenvalue i)) y) ^ 2) * κ ≤
        (2 * b) * (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2) by
      simpa only [mul_comm] using hi)
    convert ht using 1 <;> ring
  rw [PDE.DGNMOneStep.eLpNorm_two_eq_ofReal_sqrt hm]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ Real.sqrt ((2 * b / κ) *
        (Real.exp (Real.sqrt E * b) ^ 2 * ∑ i ∈ I, (a i) ^ 2)) := Real.sqrt_le_sqrt hi'
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg _),
        Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]
      ring

#print axioms spectral_finite_lift_subset_eLpNorm_le

/-- The actual zero-extended finite lift has the same uniform L² bound on
every lifted ball of radius R, including balls centered on the boundary. -/
theorem spectral_finite_zeroExtension_ball_eLpNorm_le {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (I : Finset ℕ) (a : ℕ → ℝ) (E : ℝ)
    (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) (x : PDE.Vec d) :
    eLpNorm (fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z) 2
      (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)) ≤
      ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
        Real.sqrt (∑ i ∈ I, (a i) ^ 2)) := by
  let U : Set (PDE.Vec (d + 1)) :=
    {z | (productCoordinates z).1 ∈ sourceBall (0 : PDE.Vec d) R}
  let Q := PDE.euclideanBall (productCoordinates.symm (x, 0)) R
  let F := fun z => ∑ i ∈ I, a i * liftedValue (s.eigenfunction i)
    (Real.sqrt (s.eigenvalue i)) z
  have hU : IsOpen U :=
    (dirichletBall (d := d) R).isOpen.preimage (productCoordinates (d := d)).continuous.fst
  have hΩ : IsOpen (U ∩ Q) := hU.inter (PDE.isOpen_euclideanBall _ _)
  have hsub : U ∩ Q ⊆ productCoordinates ⁻¹'
      (sourceBall (0 : PDE.Vec d) R ×ˢ Set.Icc (-R) R) := by
    intro z hz
    exact ⟨hz.1, (coordinate_ball_subset_spatial_cylinder x hR hz.2).2⟩
  have heq : (fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z) = U.indicator F := by
    funext z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz]
      have hz' : (productCoordinates z).1 ∈ sourceBall (0 : PDE.Vec d) R := hz
      apply Finset.sum_congr rfl
      intro i hi
      dsimp only [liftedValue]
      rw [Set.indicator_of_mem hz']
    · rw [Set.indicator_of_notMem hz]
      have hz' : (productCoordinates z).1 ∉ sourceBall (0 : PDE.Vec d) R := hz
      apply Finset.sum_eq_zero
      intro i hi
      dsimp only [liftedValue]
      rw [Set.indicator_of_notMem hz']
      ring
  rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet,
    Measure.restrict_restrict hU.measurableSet]
  exact spectral_finite_lift_subset_eLpNorm_le hκ h hR.le s hΩ hsub I a E hcut

#print axioms spectral_finite_zeroExtension_ball_eLpNorm_le

/-- Both signed positive parts have the same uniform L² bound. -/
theorem spectral_finite_zeroExtension_signedParts_ball_eLpNorm_le {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (I : Finset ℕ) (a : ℕ → ℝ) (E : ℝ)
    (hcut : ∀ i ∈ I, s.eigenvalue i ≤ E) (x : PDE.Vec d) :
    let F := fun z => ∑ i ∈ I, a i * liftedValue
      ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
      (Real.sqrt (s.eigenvalue i)) z
    let μ := volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)
    let B := ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
      Real.sqrt (∑ i ∈ I, (a i) ^ 2))
    eLpNorm (fun z => max (F z) 0) 2 μ ≤ B ∧
    eLpNorm (fun z => max (-F z) 0) 2 μ ≤ B := by
  let F := fun z => ∑ i ∈ I, a i * liftedValue
    ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
    (Real.sqrt (s.eigenvalue i)) z
  have hc : Continuous F := spectral_finite_zeroExtension_lift_continuous s I a
  have hp : eLpNorm (fun z => max (F z) 0) 2
      (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)) ≤
      eLpNorm F 2 (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)) :=
    eLpNorm_mono (hc.max continuous_const).aestronglyMeasurable
    (fun z => show ‖max (F z) 0‖ ≤ ‖F z‖ from by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (le_abs_self _) (abs_nonneg _))
  have hn : eLpNorm (fun z => max (-F z) 0) 2
      (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)) ≤
      eLpNorm F 2 (volume.restrict (PDE.euclideanBall (productCoordinates.symm (x, 0)) R)) :=
    eLpNorm_mono (hc.neg.max continuous_const).aestronglyMeasurable
    (fun z => show ‖max (-F z) 0‖ ≤ ‖F z‖ from by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by simpa only [abs_neg] using le_abs_self (-F z)) (abs_nonneg _))
  have hb := spectral_finite_zeroExtension_ball_eLpNorm_le hκ h hR s I a E hcut x
  exact ⟨hp.trans hb, hn.trans hb⟩

#print axioms spectral_finite_zeroExtension_signedParts_ball_eLpNorm_le

/-- Uniform squared center estimate for the actual finite zero-extended lift. -/
theorem spectral_finite_zeroExtension_center_moser_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ) (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (a : ℕ → ℝ) (x : PDE.Vec d),
      let F := fun z => ∑ i ∈ I, a i * liftedValue
        ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
        (Real.sqrt (s.eigenvalue i)) z
      (ENNReal.ofReal |F (productCoordinates.symm (x, 0))|) ^ (2 : ℝ) ≤
        ENNReal.ofReal (C * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 2) *
          (2 : ℝ) ^ ((d + 1 : ℕ) : ℝ)) *
        (ENNReal.ofReal ((R ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
          ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
            Real.sqrt (∑ i ∈ I, (a i) ^ 2))) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hmoser⟩ := spectral_finite_zeroExtension_signedParts_center_moser hd hκ h s
  refine ⟨C, hC, ?_⟩
  intro E I hcut a x
  let F := fun z => ∑ i ∈ I, a i * liftedValue
    ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
    (Real.sqrt (s.eigenvalue i)) z
  let z := productCoordinates.symm (x, 0)
  let A := ENNReal.ofReal (C * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 2) *
    (2 : ℝ) ^ ((d + 1 : ℕ) : ℝ))
  let J := ENNReal.ofReal ((R ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal)
  let B := ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
    Real.sqrt (∑ i ∈ I, (a i) ^ 2))
  obtain ⟨hp, hn⟩ := hmoser R hR x I a
  obtain ⟨hpL, hnL⟩ := spectral_finite_zeroExtension_signedParts_ball_eLpNorm_le
    hκ h hR s I a E hcut x
  have hp' := hp.trans (mul_le_mul_right (ENNReal.rpow_le_rpow
    (mul_le_mul_right hpL J) (by norm_num : (0 : ℝ) ≤ 2)) A)
  have hn' := hn.trans (mul_le_mul_right (ENNReal.rpow_le_rpow
    (mul_le_mul_right hnL J) (by norm_num : (0 : ℝ) ≤ 2)) A)
  change (ENNReal.ofReal (max (F z) 0)) ^ (2 : ℝ) ≤ A * (J * B) ^ (2 : ℝ) at hp'
  change (ENNReal.ofReal (max (-F z) 0)) ^ (2 : ℝ) ≤ A * (J * B) ^ (2 : ℝ) at hn'
  change (ENNReal.ofReal |F z|) ^ (2 : ℝ) ≤ A * (J * B) ^ (2 : ℝ)
  by_cases hz : 0 ≤ F z
  · simpa only [abs_of_nonneg hz, max_eq_left hz] using hp'
  · have hz' : 0 ≤ -F z := neg_nonneg.mpr (le_of_not_ge hz)
    simpa only [abs_of_neg (lt_of_not_ge hz), max_eq_left hz'] using hn'

#print axioms spectral_finite_zeroExtension_center_moser_bound

/-- Uniform closed-ball evaluation of finite combinations of the actual modes. -/
theorem spectral_finite_sum_closedBall_uniform_evaluation {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (a : ℕ → ℝ) (x : PDE.Vec d),
      x ∈ closure (sourceBall 0 R) →
      |∑ i ∈ I, a i * s.eigenfunction i x| ≤
        C * Real.exp (C * Real.sqrt E) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) := by
  classical
  obtain ⟨M, hM, hm⟩ := spectral_finite_zeroExtension_center_moser_bound hd hκ h hR s
  let A : ℝ := M * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 2) *
    (2 : ℝ) ^ ((d + 1 : ℕ) : ℝ)
  let J : ℝ := (((R ^ (d + 1))⁻¹) : ℝ) ^ ((1 / (2 : ℝ≥0∞)).toReal)
  let D : ℝ := Real.sqrt A * J * Real.sqrt (2 * R / κ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hJ : 0 < J := by dsimp [J]; positivity
  have hD : 0 < D := by dsimp [D]; positivity
  let C : ℝ := max D R + 1
  have hC : 0 < C := by dsimp [C]; have := le_max_left D R; linarith
  have hDC : D ≤ C := by dsimp [C]; have := le_max_left D R; linarith
  have hRC : R ≤ C := by dsimp [C]; have := le_max_right D R; linarith
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut a x hx
  let F := fun z => ∑ i ∈ I, a i * liftedValue
    ((sourceBall (0 : PDE.Vec d) R).indicator (s.eigenfunction i))
    (Real.sqrt (s.eigenvalue i)) z
  let B : ℝ := Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
    Real.sqrt (∑ i ∈ I, (a i) ^ 2)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hb := hm E I hcut a x
  change (ENNReal.ofReal |F (productCoordinates.symm (x, 0))|) ^ (2 : ℝ) ≤
    ENNReal.ofReal A * (ENNReal.ofReal ((R ^ (d + 1))⁻¹) ^
      ((1 / (2 : ℝ≥0∞)).toReal) * ENNReal.ofReal B) ^ (2 : ℝ) at hb
  have hfinite : ENNReal.ofReal A * (ENNReal.ofReal ((R ^ (d + 1))⁻¹) ^
      ((1 / (2 : ℝ≥0∞)).toReal) * ENNReal.ofReal B) ^ (2 : ℝ) ≠ ⊤ := by
    repeat' apply ENNReal.mul_ne_top
    all_goals first | exact ENNReal.ofReal_ne_top | exact ENNReal.rpow_ne_top_of_nonneg (by positivity) (by repeat' apply ENNReal.mul_ne_top <;> first | exact ENNReal.ofReal_ne_top | exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)
  have hb' := ENNReal.toReal_mono hfinite hb
  have hsquared : |F (productCoordinates.symm (x, 0))| ^ 2 ≤ A * (J * B) ^ 2 := by
    simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, Real.rpow_two,
      ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (le_of_lt hA),
      ENNReal.toReal_ofReal (show 0 ≤ (R ^ (d + 1))⁻¹ by positivity),
      ENNReal.toReal_ofReal hB, J] using hb'
  have hsqrt : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt (le_of_lt hA)
  have hbound : |F (productCoordinates.symm (x, 0))| ≤ Real.sqrt A * (J * B) := by
    have hnonneg : 0 ≤ Real.sqrt A * (J * B) := by positivity
    nlinarith [sq_nonneg (|F (productCoordinates.symm (x, 0))| + Real.sqrt A * (J * B))]
  have heq : F (productCoordinates.symm (x, 0)) = ∑ i ∈ I, a i * s.eigenfunction i x := by
    have hcoords := (productCoordinates (d := d)).apply_symm_apply (x, 0)
    have hxcoord : Fin.init (productCoordinates.symm (x, 0)) = x := by
      have hfst := congrArg Prod.fst hcoords
      simpa only [productCoordinates_apply, Fin.removeNth_last] using hfst
    have htcoord : productCoordinates.symm (x, 0) (Fin.last d) = 0 := by
      have hsnd := congrArg Prod.snd hcoords
      simpa only [productCoordinates_apply] using hsnd
    dsimp [F, liftedValue]
    simp only [Fin.removeNth_last, hxcoord, htcoord]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hx' : x ∈ sourceBall (0 : PDE.Vec d) R
    · simp [Set.indicator_of_mem hx']
    · have hfront : x ∈ frontier (sourceBall (0 : PDE.Vec d) R) :=
        ⟨hx, fun hxi => hx' (interior_subset hxi)⟩
      simp [Set.indicator_of_notMem hx', s.boundary_zero i x hfront]
  rw [heq] at hbound
  have hreal : |∑ i ∈ I, a i * s.eigenfunction i x| ≤
      D * Real.exp (R * Real.sqrt E) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) := by
    simpa only [D, B, mul_assoc, mul_comm, mul_left_comm] using hbound
  refine hreal.trans ?_
  gcongr

#print axioms spectral_finite_sum_closedBall_uniform_evaluation

/-- Uniform point evaluation of finite combinations of the actual modes. -/
theorem spectral_finite_sum_uniform_evaluation {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (a : ℕ → ℝ) (x : PDE.Vec d),
      x ∈ sourceBall 0 r →
      |∑ i ∈ I, a i * s.eigenfunction i x| ≤
        C * Real.exp (C * Real.sqrt E) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) := by
  let q : ℝ := (R - r) / 8
  have hq : 0 < q := by dsimp [q]; linarith
  have hmargin : r + 4 * q ≤ R := by dsimp [q]; linarith
  obtain ⟨M, hM, hmoser⟩ := spectral_finite_sum_moser_bound hd hκ h hR hq hmargin s
  let A : ℝ := (4 * q) * (M * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 4) *
    (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 2)) * (4 * q)⁻¹ *
    (((4 * q) ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) * Real.sqrt (2 * R / κ)
  have hA : 0 < A := by dsimp [A]; positivity
  let C : ℝ := max A R + 1
  have hC : 0 < C := by dsimp [C]; have := le_max_left A R; linarith
  have hAC : A ≤ C := by dsimp [C]; have := le_max_left A R; linarith
  have hRC : R ≤ C := by dsimp [C]; have := le_max_right A R; linarith
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut a x hx
  have hn := spectral_finite_lift_interior_eLpNorm_le hκ h hR hq hmargin s I a E hcut hx
  have hb := (hmoser I a x hx).trans (mul_le_mul_right (mul_le_mul_right
    (mul_le_mul_right (mul_le_mul_right hn _) _) _) _)
  have hfinite : ENNReal.ofReal (4 * q) *
      (ENNReal.ofReal (M * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 4) *
        (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 2)) *
        (ENNReal.ofReal (4 * q)⁻¹ *
          (ENNReal.ofReal (((4 * q) ^ (d + 1))⁻¹) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
            ENNReal.ofReal (Real.sqrt (2 * R / κ) * Real.exp (Real.sqrt E * R) *
              Real.sqrt (∑ i ∈ I, (a i) ^ 2))))) ≠ ⊤ := by
    repeat' apply ENNReal.mul_ne_top
    all_goals first | exact ENNReal.ofReal_ne_top | exact ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hb' := ENNReal.toReal_mono hfinite hb
  have hreal : |∑ i ∈ I, a i * s.eigenfunction i x| ≤
      A * Real.exp (R * Real.sqrt E) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) := by
    simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (show 0 ≤ 4 * q by positivity),
      ENNReal.toReal_ofReal (show 0 ≤ (4 * q)⁻¹ by positivity),
      ENNReal.toReal_ofReal (show 0 ≤ (((4 * q) ^ (d + 1))⁻¹) by positivity),
      ENNReal.toReal_ofReal (show 0 ≤ M * ((κ ^ 4)⁻¹) ^ (((d + 1 : ℕ) : ℝ) / 4) *
        (2 : ℝ) ^ (((d + 1 : ℕ) : ℝ) / 2) by positivity),
      ENNReal.toReal_ofReal (show 0 ≤ Real.sqrt (2 * R / κ) *
        Real.exp (Real.sqrt E * R) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) by positivity)] at hb'
    simpa only [A, mul_assoc, mul_comm, mul_left_comm] using hb'
  refine hreal.trans ?_
  gcongr

#print axioms spectral_finite_sum_uniform_evaluation

/-- A single actual Dirichlet spectral resolution has diverging eigenvalues
and uniform finite-combination evaluation on every interior ball. -/
theorem exists_sourceBall_dirichletSpectralResolution_uniform_evaluation
    {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ∀ r : ℝ, 0 < r → r < R → ∃ C : ℝ, 0 < C ∧
        ∀ E : ℝ, 0 ≤ E → ∀ I : Finset ℕ,
          (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (a : ℕ → ℝ) (x : PDE.Vec d),
          x ∈ sourceBall 0 r →
          |∑ i ∈ I, a i * s.eigenfunction i x| ≤
            C * Real.exp (C * Real.sqrt E) * Real.sqrt (∑ i ∈ I, (a i) ^ 2) := by
  obtain ⟨s, hs⟩ := exists_sourceBall_dirichletSpectralResolution hd hκ h R hR
  refine ⟨s, hs, ?_⟩
  intro r _ hr
  exact spectral_finite_sum_uniform_evaluation hd hκ h hR hr s

#print axioms exists_sourceBall_dirichletSpectralResolution_uniform_evaluation

/-- Finite spectral windows have a uniform square-sum bound at interior points. -/
theorem spectral_finite_window_square_sum_le {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (x : PDE.Vec d),
      x ∈ sourceBall 0 r →
      ∑ i ∈ I, (s.eigenfunction i x) ^ 2 ≤
        (C * Real.exp (C * Real.sqrt E)) ^ 2 := by
  obtain ⟨C, hC, heval⟩ := spectral_finite_sum_uniform_evaluation hd hκ h hR hr s
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut x hx
  let S : ℝ := ∑ i ∈ I, (s.eigenfunction i x) ^ 2
  let B : ℝ := C * Real.exp (C * Real.sqrt E)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : S ≤ B * Real.sqrt S := by
    have h := heval E hE I hcut (fun i => s.eigenfunction i x) x hx
    have heq : (∑ i ∈ I, s.eigenfunction i x * s.eigenfunction i x) = S := by
      simp only [S, pow_two]
    rw [heq, abs_of_nonneg hS] at h
    exact h
  have hsqrt := Real.sq_sqrt hS
  change S ≤ B ^ 2
  by_cases hz : S = 0
  · rw [hz]; positivity
  · have hp : 0 < Real.sqrt S := Real.sqrt_pos.2 (lt_of_le_of_ne hS (Ne.symm hz))
    have hs : Real.sqrt S ≤ B := by nlinarith
    nlinarith

#print axioms spectral_finite_window_square_sum_le

/-- Absolute cross-products in a finite spectral window obey the same bound. -/
theorem spectral_finite_window_cross_sum_le {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (x y : PDE.Vec d),
      x ∈ sourceBall 0 r → y ∈ sourceBall 0 r →
      ∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y| ≤
        (C * Real.exp (C * Real.sqrt E)) ^ 2 := by
  obtain ⟨C, hC, hsq⟩ := spectral_finite_window_square_sum_le hd hκ h hR hr s
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut x y hx hy
  have hx' := hsq E hE I hcut x hx
  have hy' := hsq E hE I hcut y hy
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => |s.eigenfunction i x|) (fun i => |s.eigenfunction i y|)
  simp only [← abs_mul, sq_abs] at hc
  have hs : 0 ≤ ∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y| := by positivity
  have hprod : (∑ i ∈ I, (s.eigenfunction i x) ^ 2) *
      (∑ i ∈ I, (s.eigenfunction i y) ^ 2) ≤
      ((C * Real.exp (C * Real.sqrt E)) ^ 2) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hx' hy' (by positivity) (sq_nonneg _)
  have hb : 0 ≤ (C * Real.exp (C * Real.sqrt E)) ^ 2 := sq_nonneg _
  nlinarith

#print axioms spectral_finite_window_cross_sum_le

/-- The exponential majorant for spectral energy shells is summable. -/
theorem spectral_shell_majorant_summable (C t : ℝ) (ht : 0 < t) :
    Summable (fun m : ℕ => Real.exp (-t * (m : ℝ) +
      2 * C * Real.sqrt ((m : ℝ) + 1))) := by
  let K : ℝ := t / 2 + 2 * C ^ 2 / t
  let q : ℝ := Real.exp (-t / 2)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hgeom : Summable (fun m : ℕ => Real.exp K * q ^ m) :=
    (summable_geometric_of_lt_one hq0 hq1).mul_left _
  apply hgeom.of_norm_bounded
  intro m
  have hz : 0 ≤ (m : ℝ) + 1 := by positivity
  have hroot := Real.sq_sqrt hz
  have hdiv : t * (2 * C ^ 2 / t) = 2 * C ^ 2 := by field_simp
  have hyoung : 2 * C * Real.sqrt ((m : ℝ) + 1) ≤
      t / 2 * ((m : ℝ) + 1) + 2 * C ^ 2 / t := by
    have hsq := sq_nonneg (t * Real.sqrt ((m : ℝ) + 1) - 2 * C)
    have hm : t * (2 * C * Real.sqrt ((m : ℝ) + 1)) ≤
        t * (t / 2 * ((m : ℝ) + 1) + 2 * C ^ 2 / t) := by
      nlinarith [sq_nonneg t]
    exact (mul_le_mul_iff_right₀ ht).mp hm
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul,
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  dsimp [K, q] at *
  linarith

#print axioms spectral_shell_majorant_summable

/-- Every finite collection in one energy shell obeys the summable majorant. -/
theorem spectral_finite_shell_heat_sum_le {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ (m : ℕ) (I : Finset ℕ),
      (∀ i ∈ I, (m : ℝ) ≤ s.eigenvalue i ∧ s.eigenvalue i ≤ (m : ℝ) + 1) →
      ∀ (x y : PDE.Vec d), x ∈ sourceBall 0 r → y ∈ sourceBall 0 r →
      ∑ i ∈ I, Real.exp (-s.eigenvalue i * t) *
        |s.eigenfunction i x * s.eigenfunction i y| ≤
      C ^ 2 * Real.exp (-t * (m : ℝ) + 2 * C * Real.sqrt ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hcross⟩ := spectral_finite_window_cross_sum_le hd hκ h hR hr s
  refine ⟨C, hC, ?_⟩
  intro t ht m I hI x y hx hy
  have hwindow := hcross ((m : ℝ) + 1) (by positivity) I
    (fun i hi => (hI i hi).2) x y hx hy
  calc
    _ ≤ ∑ i ∈ I, Real.exp (-t * (m : ℝ)) *
        |s.eigenfunction i x * s.eigenfunction i y| := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [(hI i hi).1]
    _ = Real.exp (-t * (m : ℝ)) *
        (∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y|) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-t * (m : ℝ)) *
        (C * Real.exp (C * Real.sqrt ((m : ℝ) + 1))) ^ 2 :=
      mul_le_mul_of_nonneg_left hwindow (Real.exp_pos _).le
    _ = _ := by
      rw [Real.exp_add, show 2 * C * Real.sqrt ((m : ℝ) + 1) =
        C * Real.sqrt ((m : ℝ) + 1) + C * Real.sqrt ((m : ℝ) + 1) by ring,
        Real.exp_add]
      ring

#print axioms spectral_finite_shell_heat_sum_le

/-- The actual spectral heat cross-series is absolutely summable in the interior. -/
theorem spectral_heat_cross_summable {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (ht : 0 < t)
    (x y : PDE.Vec d) (hx : x ∈ sourceBall 0 r) (hy : y ∈ sourceBall 0 r) :
    Summable (fun i => Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) := by
  obtain ⟨C, hC, hshell⟩ := spectral_finite_shell_heat_sum_le hd hκ h hR hr s
  let f : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * t) *
    |s.eigenfunction i x * s.eigenfunction i y|
  let g : ℕ → ℝ := fun m => C ^ 2 * Real.exp (-t * (m : ℝ) +
    2 * C * Real.sqrt ((m : ℝ) + 1))
  let k : ℕ → ℕ := fun i => ⌊s.eigenvalue i⌋₊
  have hg : Summable g := (spectral_shell_majorant_summable C t ht).mul_left _
  have hf : Summable f := by
    apply summable_of_sum_le (c := ∑' m, g m)
    · intro i
      dsimp [f]
      positivity
    · intro I
      let J := I.image k
      have hgroup : (∑ m ∈ J, ∑ i ∈ I with k i = m, f i) = ∑ i ∈ I, f i :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem k hi) f
      rw [← hgroup]
      calc
        _ ≤ ∑ m ∈ J, g m := by
          apply Finset.sum_le_sum
          intro m hm
          apply hshell t ht.le m (I.filter (fun i => k i = m)) ?_ x y hx hy
          intro i hi
          have hki : k i = m := (Finset.mem_filter.mp hi).2
          have hlo := Nat.floor_le (s.eigenvalue_pos i).le
          have hhi := (Nat.lt_floor_add_one (s.eigenvalue i)).le
          dsimp [k] at hki
          rw [hki] at hlo hhi
          exact ⟨hlo, hhi⟩
        _ ≤ ∑' m, g m := hg.sum_le_tsum J (fun m _ => by dsimp [g]; positivity)
  apply hf.of_norm_bounded
  intro i
  dsimp [f]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
  ring_nf
  exact le_rfl

#print axioms spectral_heat_cross_summable

/-- A single actual Dirichlet spectrum has a summable positive-time cross-series. -/
theorem exists_sourceBall_dirichletSpectralResolution_heat_cross_summable
    {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ∀ t : ℝ, 0 < t → ∀ x y : PDE.Vec d,
        x ∈ sourceBall 0 R → y ∈ sourceBall 0 R →
        Summable (fun i => Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) := by
  obtain ⟨s, hs⟩ := exists_sourceBall_dirichletSpectralResolution hd hκ h R hR
  refine ⟨s, hs, ?_⟩
  intro t ht x y hx hy
  have hxR : euclideanNorm x < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
  have hyR : euclideanNorm y < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy
  let r : ℝ := (max (euclideanNorm x) (euclideanNorm y) + R) / 2
  have hr : r < R := by dsimp [r]; have := max_lt hxR hyR; linarith
  have hxr : x ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]
    have := le_max_left (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR
    linarith
  have hyr : y ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]
    have := le_max_right (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR
    linarith
  exact spectral_heat_cross_summable hd hκ h hR hr s t ht x y hxr hyr

#print axioms exists_sourceBall_dirichletSpectralResolution_heat_cross_summable

/-- Uniformly small finite spectral tails on any interior ball and positive time strip. -/
theorem spectral_heat_uniform_finite_tails {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ I : Finset ℕ,
      (∀ i ∈ I, N ≤ i) → ∀ t : ℝ, a ≤ t → ∀ x y : PDE.Vec d,
      x ∈ sourceBall 0 r → y ∈ sourceBall 0 r →
      ∑ i ∈ I, Real.exp (-s.eigenvalue i * t) *
        |s.eigenfunction i x * s.eigenfunction i y| < ε := by
  classical
  obtain ⟨C, hC, hshell⟩ := spectral_finite_shell_heat_sum_le hd hκ h hR hr s
  let g : ℕ → ℝ := fun m => C ^ 2 * Real.exp (-a * (m : ℝ) +
    2 * C * Real.sqrt ((m : ℝ) + 1))
  let k : ℕ → ℕ := fun i => ⌊s.eigenvalue i⌋₊
  have hg : Summable g := (spectral_shell_majorant_summable C a ha).mul_left _
  intro ε hε
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp hg ε hε
  let M : ℕ := S.sup id + 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hs.eventually (Filter.eventually_ge_atTop (M : ℝ)))
  refine ⟨N, ?_⟩
  intro I hI t ht x y hx hy
  let J := I.image k
  have hdis : Disjoint J S := by
    apply Finset.disjoint_left.mpr
    intro m hmJ hmS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmJ
    have hlow : M ≤ k i := Nat.le_floor (hN i (hI i hi))
    have hupp : k i ≤ S.sup id := Finset.le_sup (f := id) hmS
    dsimp [M] at hlow
    omega
  have hsmall : ∑ m ∈ J, g m < ε := by
    have hz : 0 ≤ ∑ m ∈ J, g m := by dsimp [g]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hS J hdis
  calc
    _ ≤ ∑ i ∈ I, Real.exp (-s.eigenvalue i * a) *
        |s.eigenfunction i x * s.eigenfunction i y| := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [(s.eigenvalue_pos i).le]
    _ = ∑ m ∈ J, ∑ i ∈ I with k i = m,
        Real.exp (-s.eigenvalue i * a) * |s.eigenfunction i x * s.eigenfunction i y| := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem k hi) _
    _ ≤ ∑ m ∈ J, g m := by
      apply Finset.sum_le_sum
      intro m hm
      apply hshell a ha.le m (I.filter (fun i => k i = m)) ?_ x y hx hy
      intro i hi
      have hki : k i = m := (Finset.mem_filter.mp hi).2
      have hlo := Nat.floor_le (s.eigenvalue_pos i).le
      have hhi := (Nat.lt_floor_add_one (s.eigenvalue i)).le
      dsimp [k] at hki
      rw [hki] at hlo hhi
      exact ⟨hlo, hhi⟩
    _ < ε := hsmall

#print axioms spectral_heat_uniform_finite_tails

/-- The actual spectral partial sums converge uniformly on interior positive-time strips. -/
theorem spectral_heat_tendstoUniformlyOn {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn
      (fun n (z : ℝ × PDE.Vec d × PDE.Vec d) =>
        ∑ i ∈ Finset.range n, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2) atTop
      {z | a ≤ z.1 ∧ z.2.1 ∈ sourceBall 0 r ∧ z.2.2 ∈ sourceBall 0 r} := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := spectral_heat_uniform_finite_tails hd hκ h hR hr s hs a ha
    (ε / 2) (by linarith)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn z hz
  let f : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * z.1) *
    s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2
  have hf : Summable f := spectral_heat_cross_summable hd hκ h hR hr s z.1
    (lt_of_lt_of_le ha hz.1) z.2.1 z.2.2 hz.2.1 hz.2.2
  have hshift : Summable (fun i => ‖f (i + n)‖) :=
    (summable_nat_add_iff n).mpr hf.norm
  have hbound : ∑' i, ‖f (i + n)‖ ≤ ε / 2 := by
    apply Real.tsum_le_of_sum_le (fun i => norm_nonneg _)
    intro I
    have hi := hN (I.image (fun i => i + n)) (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      omega) z.1 hz.1 z.2.1 z.2.2 hz.2.1 hz.2.2
    have heq : ∑ i ∈ I, ‖f (i + n)‖ =
        ∑ i ∈ I.image (fun i => i + n), Real.exp (-s.eigenvalue i * z.1) *
          |s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2| := by
      rw [Finset.sum_image (fun i _ j _ hij => Nat.add_right_cancel hij)]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      ring
    rw [heq]
    exact hi.le
  have hdist : dist (∑' i, f i) (∑ i ∈ Finset.range n, f i) =
      ‖∑' i, f (i + n)‖ := by
    rw [dist_eq_norm, ← hf.sum_add_tsum_nat_add n, add_sub_cancel_left]
  change dist (∑' i, f i) (∑ i ∈ Finset.range n, f i) < ε
  rw [hdist]
  exact (norm_tsum_le_tsum_norm hshift).trans_lt (lt_of_le_of_lt hbound (by linarith))

#print axioms spectral_heat_tendstoUniformlyOn

/-- The spectral heat series is continuous on each interior positive-time strip. -/
theorem spectral_heat_continuousOn_strip {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R r : ℝ} (hR : 0 < R) (hr : r < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      {z | a ≤ z.1 ∧ z.2.1 ∈ sourceBall 0 r ∧ z.2.2 ∈ sourceBall 0 r} := by
  apply (spectral_heat_tendstoUniformlyOn hd hκ h hR hr s hs a ha).continuousOn
  apply Filter.Frequently.of_forall
  intro n
  apply continuousOn_finsetSum
  intro i hi
  have hx : ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      s.eigenfunction i z.2.1)
      {z | a ≤ z.1 ∧ z.2.1 ∈ sourceBall 0 r ∧ z.2.2 ∈ sourceBall 0 r} := by
    apply (s.continuous i).comp (continuous_fst.comp continuous_snd).continuousOn
    intro z hz
    apply subset_closure
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero] at hz ⊢
    exact lt_trans hz.2.1 hr
  have hy : ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      s.eigenfunction i z.2.2)
      {z | a ≤ z.1 ∧ z.2.1 ∈ sourceBall 0 r ∧ z.2.2 ∈ sourceBall 0 r} := by
    apply (s.continuous i).comp (continuous_snd.comp continuous_snd).continuousOn
    intro z hz
    apply subset_closure
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero] at hz ⊢
    exact lt_trans hz.2.2 hr
  exact (((continuous_const.neg.mul continuous_fst).rexp.continuousOn).mul hx).mul hy

#print axioms spectral_heat_continuousOn_strip

theorem spectral_finite_window_square_sum_le_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (x : PDE.Vec d),
      x ∈ closure (sourceBall 0 R) →
      ∑ i ∈ I, (s.eigenfunction i x) ^ 2 ≤
        (C * Real.exp (C * Real.sqrt E)) ^ 2 := by
  obtain ⟨C, hC, heval⟩ := spectral_finite_sum_closedBall_uniform_evaluation hd hκ h hR s
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut x hx
  let S : ℝ := ∑ i ∈ I, (s.eigenfunction i x) ^ 2
  let B : ℝ := C * Real.exp (C * Real.sqrt E)
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : S ≤ B * Real.sqrt S := by
    have h := heval E hE I hcut (fun i => s.eigenfunction i x) x hx
    have heq : (∑ i ∈ I, s.eigenfunction i x * s.eigenfunction i x) = S := by
      simp only [S, pow_two]
    rw [heq, abs_of_nonneg hS] at h
    exact h
  have hsqrt := Real.sq_sqrt hS
  change S ≤ B ^ 2
  by_cases hz : S = 0
  · rw [hz]; positivity
  · have hp : 0 < Real.sqrt S := Real.sqrt_pos.2 (lt_of_le_of_ne hS (Ne.symm hz))
    have hs : Real.sqrt S ≤ B := by nlinarith
    nlinarith

#print axioms spectral_finite_window_square_sum_le_closedBall

theorem spectral_finite_window_cross_sum_le_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (E : ℝ), 0 ≤ E → ∀ (I : Finset ℕ),
      (∀ i ∈ I, s.eigenvalue i ≤ E) → ∀ (x y : PDE.Vec d),
      x ∈ closure (sourceBall 0 R) → y ∈ closure (sourceBall 0 R) →
      ∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y| ≤
        (C * Real.exp (C * Real.sqrt E)) ^ 2 := by
  obtain ⟨C, hC, hsq⟩ := spectral_finite_window_square_sum_le_closedBall hd hκ h hR s
  refine ⟨C, hC, ?_⟩
  intro E hE I hcut x y hx hy
  have hx' := hsq E hE I hcut x hx
  have hy' := hsq E hE I hcut y hy
  have hc := Finset.sum_mul_sq_le_sq_mul_sq I
    (fun i => |s.eigenfunction i x|) (fun i => |s.eigenfunction i y|)
  simp only [← abs_mul, sq_abs] at hc
  have hs : 0 ≤ ∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y| := by positivity
  have hprod : (∑ i ∈ I, (s.eigenfunction i x) ^ 2) *
      (∑ i ∈ I, (s.eigenfunction i y) ^ 2) ≤
      ((C * Real.exp (C * Real.sqrt E)) ^ 2) ^ 2 := by
    rw [pow_two]
    exact mul_le_mul hx' hy' (by positivity) (sq_nonneg _)
  have hb : 0 ≤ (C * Real.exp (C * Real.sqrt E)) ^ 2 := sq_nonneg _
  nlinarith

#print axioms spectral_finite_window_cross_sum_le_closedBall

theorem spectral_finite_shell_heat_sum_le_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ), 0 ≤ t → ∀ (m : ℕ) (I : Finset ℕ),
      (∀ i ∈ I, (m : ℝ) ≤ s.eigenvalue i ∧ s.eigenvalue i ≤ (m : ℝ) + 1) →
      ∀ (x y : PDE.Vec d), x ∈ closure (sourceBall 0 R) → y ∈ closure (sourceBall 0 R) →
      ∑ i ∈ I, Real.exp (-s.eigenvalue i * t) *
        |s.eigenfunction i x * s.eigenfunction i y| ≤
      C ^ 2 * Real.exp (-t * (m : ℝ) + 2 * C * Real.sqrt ((m : ℝ) + 1)) := by
  obtain ⟨C, hC, hcross⟩ := spectral_finite_window_cross_sum_le_closedBall hd hκ h hR s
  refine ⟨C, hC, ?_⟩
  intro t ht m I hI x y hx hy
  have hwindow := hcross ((m : ℝ) + 1) (by positivity) I
    (fun i hi => (hI i hi).2) x y hx hy
  calc
    _ ≤ ∑ i ∈ I, Real.exp (-t * (m : ℝ)) *
        |s.eigenfunction i x * s.eigenfunction i y| := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [(hI i hi).1]
    _ = Real.exp (-t * (m : ℝ)) *
        (∑ i ∈ I, |s.eigenfunction i x * s.eigenfunction i y|) := by
      rw [Finset.mul_sum]
    _ ≤ Real.exp (-t * (m : ℝ)) *
        (C * Real.exp (C * Real.sqrt ((m : ℝ) + 1))) ^ 2 :=
      mul_le_mul_of_nonneg_left hwindow (Real.exp_pos _).le
    _ = _ := by
      rw [Real.exp_add, show 2 * C * Real.sqrt ((m : ℝ) + 1) =
        C * Real.sqrt ((m : ℝ) + 1) + C * Real.sqrt ((m : ℝ) + 1) by ring,
        Real.exp_add]
      ring

#print axioms spectral_finite_shell_heat_sum_le_closedBall

theorem spectral_heat_cross_summable_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (ht : 0 < t)
    (x y : PDE.Vec d) (hx : x ∈ closure (sourceBall 0 R)) (hy : y ∈ closure (sourceBall 0 R)) :
    Summable (fun i => Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) := by
  obtain ⟨C, hC, hshell⟩ := spectral_finite_shell_heat_sum_le_closedBall hd hκ h hR s
  let f : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * t) *
    |s.eigenfunction i x * s.eigenfunction i y|
  let g : ℕ → ℝ := fun m => C ^ 2 * Real.exp (-t * (m : ℝ) +
    2 * C * Real.sqrt ((m : ℝ) + 1))
  let k : ℕ → ℕ := fun i => ⌊s.eigenvalue i⌋₊
  have hg : Summable g := (spectral_shell_majorant_summable C t ht).mul_left _
  have hf : Summable f := by
    apply summable_of_sum_le (c := ∑' m, g m)
    · intro i
      dsimp [f]
      positivity
    · intro I
      let J := I.image k
      have hgroup : (∑ m ∈ J, ∑ i ∈ I with k i = m, f i) = ∑ i ∈ I, f i :=
        Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem k hi) f
      rw [← hgroup]
      calc
        _ ≤ ∑ m ∈ J, g m := by
          apply Finset.sum_le_sum
          intro m hm
          apply hshell t ht.le m (I.filter (fun i => k i = m)) ?_ x y hx hy
          intro i hi
          have hki : k i = m := (Finset.mem_filter.mp hi).2
          have hlo := Nat.floor_le (s.eigenvalue_pos i).le
          have hhi := (Nat.lt_floor_add_one (s.eigenvalue i)).le
          dsimp [k] at hki
          rw [hki] at hlo hhi
          exact ⟨hlo, hhi⟩
        _ ≤ ∑' m, g m := hg.sum_le_tsum J (fun m _ => by dsimp [g]; positivity)
  apply hf.of_norm_bounded
  intro i
  dsimp [f]
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul]
  ring_nf
  exact le_rfl

#print axioms spectral_heat_cross_summable_closedBall

theorem spectral_heat_uniform_finite_tails_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ I : Finset ℕ,
      (∀ i ∈ I, N ≤ i) → ∀ t : ℝ, a ≤ t → ∀ x y : PDE.Vec d,
      x ∈ closure (sourceBall 0 R) → y ∈ closure (sourceBall 0 R) →
      ∑ i ∈ I, Real.exp (-s.eigenvalue i * t) *
        |s.eigenfunction i x * s.eigenfunction i y| < ε := by
  classical
  obtain ⟨C, hC, hshell⟩ := spectral_finite_shell_heat_sum_le_closedBall hd hκ h hR s
  let g : ℕ → ℝ := fun m => C ^ 2 * Real.exp (-a * (m : ℝ) +
    2 * C * Real.sqrt ((m : ℝ) + 1))
  let k : ℕ → ℕ := fun i => ⌊s.eigenvalue i⌋₊
  have hg : Summable g := (spectral_shell_majorant_summable C a ha).mul_left _
  intro ε hε
  obtain ⟨S, hS⟩ := summable_iff_vanishing_norm.mp hg ε hε
  let M : ℕ := S.sup id + 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (hs.eventually (Filter.eventually_ge_atTop (M : ℝ)))
  refine ⟨N, ?_⟩
  intro I hI t ht x y hx hy
  let J := I.image k
  have hdis : Disjoint J S := by
    apply Finset.disjoint_left.mpr
    intro m hmJ hmS
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hmJ
    have hlow : M ≤ k i := Nat.le_floor (hN i (hI i hi))
    have hupp : k i ≤ S.sup id := Finset.le_sup (f := id) hmS
    dsimp [M] at hlow
    omega
  have hsmall : ∑ m ∈ J, g m < ε := by
    have hz : 0 ≤ ∑ m ∈ J, g m := by dsimp [g]; positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hS J hdis
  calc
    _ ≤ ∑ i ∈ I, Real.exp (-s.eigenvalue i * a) *
        |s.eigenfunction i x * s.eigenfunction i y| := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply Real.exp_le_exp.mpr
      nlinarith [(s.eigenvalue_pos i).le]
    _ = ∑ m ∈ J, ∑ i ∈ I with k i = m,
        Real.exp (-s.eigenvalue i * a) * |s.eigenfunction i x * s.eigenfunction i y| := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem k hi) _
    _ ≤ ∑ m ∈ J, g m := by
      apply Finset.sum_le_sum
      intro m hm
      apply hshell a ha.le m (I.filter (fun i => k i = m)) ?_ x y hx hy
      intro i hi
      have hki : k i = m := (Finset.mem_filter.mp hi).2
      have hlo := Nat.floor_le (s.eigenvalue_pos i).le
      have hhi := (Nat.lt_floor_add_one (s.eigenvalue i)).le
      dsimp [k] at hki
      rw [hki] at hlo hhi
      exact ⟨hlo, hhi⟩
    _ < ε := hsmall

#print axioms spectral_heat_uniform_finite_tails_closedBall

theorem spectral_heat_tendstoUniformlyOn_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    TendstoUniformlyOn
      (fun n (z : ℝ × PDE.Vec d × PDE.Vec d) =>
        ∑ i ∈ Finset.range n, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2) atTop
      {z | a ≤ z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧ z.2.2 ∈ closure (sourceBall 0 R)} := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := spectral_heat_uniform_finite_tails_closedBall hd hκ h hR s hs a ha
    (ε / 2) (by linarith)
  filter_upwards [Filter.eventually_ge_atTop N] with n hn z hz
  let f : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * z.1) *
    s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2
  have hf : Summable f := spectral_heat_cross_summable_closedBall hd hκ h hR s z.1
    (lt_of_lt_of_le ha hz.1) z.2.1 z.2.2 hz.2.1 hz.2.2
  have hshift : Summable (fun i => ‖f (i + n)‖) :=
    (summable_nat_add_iff n).mpr hf.norm
  have hbound : ∑' i, ‖f (i + n)‖ ≤ ε / 2 := by
    apply Real.tsum_le_of_sum_le (fun i => norm_nonneg _)
    intro I
    have hi := hN (I.image (fun i => i + n)) (by
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
      omega) z.1 hz.1 z.2.1 z.2.2 hz.2.1 hz.2.2
    have heq : ∑ i ∈ I, ‖f (i + n)‖ =
        ∑ i ∈ I.image (fun i => i + n), Real.exp (-s.eigenvalue i * z.1) *
          |s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2| := by
      rw [Finset.sum_image (fun i _ j _ hij => Nat.add_right_cancel hij)]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [f]
      simp only [abs_mul, abs_of_pos (Real.exp_pos _)]
      ring
    rw [heq]
    exact hi.le
  have hdist : dist (∑' i, f i) (∑ i ∈ Finset.range n, f i) =
      ‖∑' i, f (i + n)‖ := by
    rw [dist_eq_norm, ← hf.sum_add_tsum_nat_add n, add_sub_cancel_left]
  change dist (∑' i, f i) (∑ i ∈ Finset.range n, f i) < ε
  rw [hdist]
  exact (norm_tsum_le_tsum_norm hshift).trans_lt (lt_of_le_of_lt hbound (by linarith))

#print axioms spectral_heat_tendstoUniformlyOn_closedBall

theorem spectral_heat_continuousOn_strip_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R)
    (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a : ℝ) (ha : 0 < a) :
    ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      {z | a ≤ z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧ z.2.2 ∈ closure (sourceBall 0 R)} := by
  apply (spectral_heat_tendstoUniformlyOn_closedBall hd hκ h hR s hs a ha).continuousOn
  apply Filter.Frequently.of_forall
  intro n
  apply continuousOn_finsetSum
  intro i hi
  have hx : ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      s.eigenfunction i z.2.1)
      {z | a ≤ z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧ z.2.2 ∈ closure (sourceBall 0 R)} := by
    apply (s.continuous i).comp (continuous_fst.comp continuous_snd).continuousOn
    intro z hz
    exact hz.2.1
  have hy : ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      s.eigenfunction i z.2.2)
      {z | a ≤ z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧ z.2.2 ∈ closure (sourceBall 0 R)} := by
    apply (s.continuous i).comp (continuous_snd.comp continuous_snd).continuousOn
    intro z hz
    exact hz.2.2
  exact (((continuous_const.neg.mul continuous_fst).rexp.continuousOn).mul hx).mul hy

#print axioms spectral_heat_continuousOn_strip_closedBall

/-- Joint continuity of the spectral series up to the boundary at positive times. -/
theorem spectral_heat_continuousOn_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) :
    ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      {z | 0 < z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧
        z.2.2 ∈ closure (sourceBall 0 R)} := by
  intro z hz
  have hc := spectral_heat_continuousOn_strip_closedBall hd hκ h hR s hs (z.1 / 2)
    (by linarith [hz.1]) z ⟨by linarith [hz.1], hz.2.1, hz.2.2⟩
  apply hc.mono_of_mem_nhdsWithin
  have htime : z.1 / 2 < z.1 := by linarith [hz.1]
  have ht : {w : ℝ × PDE.Vec d × PDE.Vec d | z.1 / 2 < w.1} ∈ nhds z := by
    apply (isOpen_Ioi.preimage continuous_fst).mem_nhds
    exact htime
  filter_upwards [mem_nhdsWithin_of_mem_nhds ht, self_mem_nhdsWithin] with w hw hws
  exact ⟨hw.le, hws.2.1, hws.2.2⟩

#print axioms spectral_heat_continuousOn_closedBall

/-- The spectral heat kernel has the literal boundary-continuity field. -/
theorem spectral_heat_row_continuousOn_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (y : PDE.Vec d)
    (hy : y ∈ sourceBall 0 R) :
    ContinuousOn (fun z : ℝ × PDE.Vec d =>
      ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2 * s.eigenfunction i y)
      (Set.Ioi 0 ×ˢ closure (sourceBall 0 R)) := by
  apply (spectral_heat_continuousOn_closedBall hd hκ h hR s hs).comp
    (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
  intro z hz
  exact ⟨hz.1, hz.2, subset_closure hy⟩

#print axioms spectral_heat_row_continuousOn_closedBall

/-- Continuity of the actual spectral heat series for positive time and interior points. -/
theorem spectral_heat_continuousOn {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) :
    ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
      ∑' i, Real.exp (-s.eigenvalue i * z.1) *
        s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
      {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} := by
  apply continuousOn_of_forall_continuousAt
  intro z hz
  have hxR : euclideanNorm z.2.1 < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hz.2.1
  have hyR : euclideanNorm z.2.2 < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hz.2.2
  let r : ℝ := (max (euclideanNorm z.2.1) (euclideanNorm z.2.2) + R) / 2
  have hr : r < R := by dsimp [r]; have := max_lt hxR hyR; linarith
  have hrpos : 0 < r := by
    dsimp [r]
    have : 0 ≤ euclideanNorm z.2.1 := Real.sqrt_nonneg _
    have := le_max_left (euclideanNorm z.2.1) (euclideanNorm z.2.2)
    linarith
  have hxr : z.2.1 ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]
    have := le_max_left (euclideanNorm z.2.1) (euclideanNorm z.2.2)
    have := max_lt hxR hyR
    linarith
  have hyr : z.2.2 ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]
    have := le_max_right (euclideanNorm z.2.1) (euclideanNorm z.2.2)
    have := max_lt hxR hyR
    linarith
  let U : Set (ℝ × PDE.Vec d × PDE.Vec d) :=
    {w | z.1 / 2 < w.1 ∧ w.2.1 ∈ sourceBall 0 r ∧ w.2.2 ∈ sourceBall 0 r}
  have hopenBall : IsOpen (sourceBall (0 : PDE.Vec d) r) := by
    rw [← pde_ball_eq_sourceBall _ hrpos]
    exact PDE.isOpen_euclideanBall _ _
  have hopen : IsOpen U := by
    exact (isOpen_Ioi.preimage continuous_fst).inter
      ((hopenBall.preimage (continuous_fst.comp continuous_snd)).inter
        (hopenBall.preimage (continuous_snd.comp continuous_snd)))
  have hzU : z ∈ U := ⟨by linarith [hz.1], hxr, hyr⟩
  apply (spectral_heat_continuousOn_strip hd hκ h hR hr s hs (z.1 / 2)
    (by linarith [hz.1])).continuousAt
  apply Filter.mem_of_superset (hopen.mem_nhds hzU)
  intro w hw
  exact ⟨hw.1.le, hw.2.1, hw.2.2⟩

#print axioms spectral_heat_continuousOn

/-- One actual Dirichlet spectrum supplies summability, uniform convergence and continuity. -/
theorem exists_sourceBall_dirichletSpectralResolution_heat_uniform_continuous
    {d : ℕ} (hd : 2 ≤ d) {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ t : ℝ, 0 < t → ∀ x y : PDE.Vec d,
        x ∈ sourceBall 0 R → y ∈ sourceBall 0 R →
        Summable (fun i => Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y)) ∧
      (∀ a : ℝ, 0 < a → ∀ r : ℝ, r < R →
        TendstoUniformlyOn
          (fun n (z : ℝ × PDE.Vec d × PDE.Vec d) =>
            ∑ i ∈ Finset.range n, Real.exp (-s.eigenvalue i * z.1) *
              s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2) atTop
          {z | a ≤ z.1 ∧ z.2.1 ∈ sourceBall 0 r ∧ z.2.2 ∈ sourceBall 0 r}) ∧
      ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
        ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
        {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} := by
  obtain ⟨s, hs, hsum⟩ :=
    exists_sourceBall_dirichletSpectralResolution_heat_cross_summable hd hκ h R hR
  refine ⟨s, hs, hsum, ?_, spectral_heat_continuousOn hd hκ h hR s hs⟩
  intro a ha r hr
  exact spectral_heat_tendstoUniformlyOn hd hκ h hR hr s hs a ha

#print axioms exists_sourceBall_dirichletSpectralResolution_heat_uniform_continuous

/-- The coefficients of a positive-time row are square-summable. -/
theorem spectral_heat_row_coefficients_summable {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    Summable (fun i => (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) ^ 2) := by
  have hxR : euclideanNorm x < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
  let r : ℝ := (euclideanNorm x + R) / 2
  have hr : r < R := by dsimp [r]; linarith
  have hxr : x ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]
    linarith
  have hs := spectral_heat_cross_summable hd hκ h hR hr s (2 * t)
    (by linarith) x x hxr hxr
  convert hs using 1
  funext i
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  have he : -s.eigenvalue i * t + -s.eigenvalue i * t =
      -s.eigenvalue i * (2 * t) := by ring
  rw [he]
  ring

#print axioms spectral_heat_row_coefficients_summable

/-- The same row coefficients define an element of the Hilbert sequence space. -/
theorem spectral_heat_row_coefficients_memℓp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    Memℓp (fun i => Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) 2 := by
  apply memℓp_gen
  convert spectral_heat_row_coefficients_summable hd hκ h hR s t ht x hx using 1
  funext i
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_natCast, Real.norm_eq_abs]
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  exact sq_abs (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)

#print axioms spectral_heat_row_coefficients_memℓp

/-- The weighted Hilbert-space series of the actual row converges. -/
theorem spectral_heat_row_Lp_summable {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    Summable (fun i => (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) := by
  have hs := (s.orthonormal.orthogonalFamily.summable_iff_norm_sq_summable
    (fun i => Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)).2 ?_
  · simpa only [LinearIsometry.toSpanSingleton_apply] using hs
  · simpa only [Real.norm_eq_abs, sq_abs] using
      spectral_heat_row_coefficients_summable hd hκ h hR s t ht x hx

#print axioms spectral_heat_row_Lp_summable

/-- The Hilbert-space limit is represented by the actual pointwise heat series. -/
theorem spectral_heat_row_Lp_ae_eq {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    (fun y => (∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) y) =ᵐ[dirichletVolume ρ R]
      (fun y => ∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) := by
  classical
  let f : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hf : Summable f := spectral_heat_row_Lp_summable hd hκ h hR s t ht x hx
  have hlim := hf.tendsto_sum_tsum_nat
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hsum : ∀ᵐ y ∂dirichletVolume ρ R, ∀ n,
      (∑ i ∈ Finset.range n, f i : Lp ℝ 2 (dirichletVolume ρ R)) y =
        ∑ i ∈ Finset.range n, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) f,
      ae_all_iff.mpr (fun i => Lp.coeFn_smul
        (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x)
        ((s.square_integrable i).toLp (s.eigenfunction i))),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with y hy hsmul hmode
    rw [hy]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsmul i]
    simp only [Pi.smul_apply, smul_eq_mul, hmode i]
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall 0 R := by
    have hm : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
      rw [← pde_ball_eq_sourceBall _ hR]
      exact (PDE.isOpen_euclideanBall _ _).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)
  filter_upwards [hpoint, hsum, hball] with y hy hys hyball
  have hxR : euclideanNorm x < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
  have hyR : euclideanNorm y < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hyball
  let r : ℝ := (max (euclideanNorm x) (euclideanNorm y) + R) / 2
  have hr : r < R := by dsimp [r]; have := max_lt hxR hyR; linarith
  have hxr : x ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]; have := le_max_left (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR; linarith
  have hyr : y ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]; have := le_max_right (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR; linarith
  have hs := spectral_heat_cross_summable hd hκ h hR hr s t ht x y hxr hyr
  have hp := hs.tendsto_sum_tsum_nat.comp hns.tendsto_atTop
  apply tendsto_nhds_unique hy
  change Tendsto (fun n => ∑ i ∈ Finset.range (ns n),
    Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y)
    atTop (nhds (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y)) at hp
  simpa only [hys] using hp

#print axioms spectral_heat_row_Lp_ae_eq

/-- Each positive-time heat row belongs to the actual weighted L² space. -/
theorem spectral_heat_row_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    MemLp (fun y => ∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) 2 (dirichletVolume ρ R) := by
  exact (Lp.memLp _).ae_eq (spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx)

#print axioms spectral_heat_row_memLp

/-- Parseval's identity for the actual weighted heat row. -/
theorem spectral_heat_row_integral_sq {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    (∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) ^ 2 ∂dirichletVolume ρ R) =
      ∑' i, Real.exp (-2 * s.eigenvalue i * t) * (s.eigenfunction i x) ^ 2 := by
  classical
  let c : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x
  let f : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    c i • (s.square_integrable i).toLp (s.eigenfunction i)
  have hf : Summable f := spectral_heat_row_Lp_summable hd hκ h hR s t ht x hx
  have hc : Summable (fun i => (c i) ^ 2) :=
    spectral_heat_row_coefficients_summable hd hκ h hR s t ht x hx
  have hnorm : ‖∑' i, f i‖ ^ 2 = ∑' i, (c i) ^ 2 := by
    apply tendsto_nhds_unique (hf.tendsto_sum_tsum_nat.norm.pow 2)
    have htend := hc.tendsto_sum_tsum_nat
    apply htend.congr'
    filter_upwards with n
    simpa only [f, LinearIsometry.toSpanSingleton_apply, Real.norm_eq_abs, sq_abs] using
      (s.orthonormal.orthogonalFamily.norm_sum c (Finset.range n)).symm
  have hae := spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx
  have hint : (∫ y, (∑' i, f i) y ^ 2 ∂dirichletVolume ρ R) =
      ∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) ^ 2 ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    rw [hy]
  have hi : (∫ y, (∑' i, f i) y ^ 2 ∂dirichletVolume ρ R) = ‖∑' i, f i‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards with y
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [← hint, hi, hnorm]
  apply tsum_congr
  intro i
  dsimp [c]
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  have he : -s.eigenvalue i * t + -s.eigenvalue i * t =
      -2 * s.eigenvalue i * t := by ring
  rw [he]

#print axioms spectral_heat_row_integral_sq

/-- Convolution of two actual positive-time spectral rows. -/
theorem spectral_heat_row_convolution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    (∫ z, (∑' i, Real.exp (-s.eigenvalue i * p) *
      s.eigenfunction i x * s.eigenfunction i z) *
      (∑' i, Real.exp (-s.eigenvalue i * q) *
        s.eigenfunction i y * s.eigenfunction i z) ∂dirichletVolume ρ R) =
    ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
      s.eigenfunction i x * s.eigenfunction i y := by
  classical
  let a : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * p) * s.eigenfunction i x
  let b : ℕ → ℝ := fun i => Real.exp (-s.eigenvalue i * q) * s.eigenfunction i y
  let u : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    a i • (s.square_integrable i).toLp (s.eigenfunction i)
  let v : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    b i • (s.square_integrable i).toLp (s.eigenfunction i)
  have hu : Summable u := spectral_heat_row_Lp_summable hd hκ h hR s p hp x hx
  have hv : Summable v := spectral_heat_row_Lp_summable hd hκ h hR s q hq y hy
  have hxR : euclideanNorm x < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
  have hyR : euclideanNorm y < R := by
    simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy
  let r : ℝ := (max (euclideanNorm x) (euclideanNorm y) + R) / 2
  have hr : r < R := by dsimp [r]; have := max_lt hxR hyR; linarith
  have hxr : x ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]; have := le_max_left (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR; linarith
  have hyr : y ∈ sourceBall 0 r := by
    simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
    dsimp [r]; have := le_max_right (euclideanNorm x) (euclideanNorm y)
    have := max_lt hxR hyR; linarith
  have hs := spectral_heat_cross_summable hd hκ h hR hr s (p + q)
    (by linarith) x y hxr hyr
  have hterm (i : ℕ) : a i * b i = Real.exp (-s.eigenvalue i * (p + q)) *
      s.eigenfunction i x * s.eigenfunction i y := by
    dsimp [a, b]
    calc
      _ = (Real.exp (-s.eigenvalue i * p) * Real.exp (-s.eigenvalue i * q)) *
          s.eigenfunction i x * s.eigenfunction i y := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2 <;> ring
  have hinner : inner ℝ (∑' i, u i) (∑' i, v i) =
      ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
        s.eigenfunction i x * s.eigenfunction i y := by
    apply tendsto_nhds_unique (hu.tendsto_sum_tsum_nat.inner hv.tendsto_sum_tsum_nat)
    apply hs.tendsto_sum_tsum_nat.congr'
    filter_upwards with n
    have hreal (i : ℕ) : inner ℝ (a i) (b i) = a i * b i := by
      simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    simpa only [u, v, LinearIsometry.toSpanSingleton_apply, hreal, hterm] using
      (s.orthonormal.orthogonalFamily.inner_sum a b (Finset.range n)).symm
  rw [← hinner, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s p hp x hx,
    spectral_heat_row_Lp_ae_eq hd hκ h hR s q hq y hy] with z hz hz'
  change (∑' i, u i) z = _ at hz
  change (∑' i, v i) z = _ at hz'
  simp only [RCLike.inner_apply, conj_trivial, hz, hz', mul_comm]

#print axioms spectral_heat_row_convolution

/-- The two actual rows have an integrable product under the weighted measure. -/
theorem spectral_heat_row_product_integrable {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    Integrable (fun z => (∑' i, Real.exp (-s.eigenvalue i * p) *
      s.eigenfunction i x * s.eigenfunction i z) *
      (∑' i, Real.exp (-s.eigenvalue i * q) *
        s.eigenfunction i z * s.eigenfunction i y)) (dirichletVolume ρ R) := by
  have h1 := spectral_heat_row_memLp hd hκ h hR s p hp x hx
  have h2 := spectral_heat_row_memLp hd hκ h hR s q hq y hy
  have heq : (fun z => ∑' i, Real.exp (-s.eigenvalue i * q) *
      s.eigenfunction i z * s.eigenfunction i y) =
      (fun z => ∑' i, Real.exp (-s.eigenvalue i * q) *
        s.eigenfunction i y * s.eigenfunction i z) := by
    funext z
    apply tsum_congr
    intro i
    ring
  have hpdt := h1.integrable_mul h2
  apply hpdt.congr
  filter_upwards with z
  exact congrArg (fun v => (∑' i, Real.exp (-s.eigenvalue i * p) *
    s.eigenfunction i x * s.eigenfunction i z) * v) (congrFun heq z).symm

#print axioms spectral_heat_row_product_integrable

/-- The spectral heat kernel has the usual convolution orientation. -/
theorem spectral_heat_convolution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    (∫ z, (∑' i, Real.exp (-s.eigenvalue i * p) *
      s.eigenfunction i x * s.eigenfunction i z) *
      (∑' i, Real.exp (-s.eigenvalue i * q) *
        s.eigenfunction i z * s.eigenfunction i y) ∂dirichletVolume ρ R) =
    ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
      s.eigenfunction i x * s.eigenfunction i y := by
  convert spectral_heat_row_convolution hd hκ h hR s p q hp hq x y hx hy using 1
  apply integral_congr_ae
  filter_upwards with z
  congr 1
  apply tsum_congr
  intro i
  ring

#print axioms spectral_heat_convolution

/-- The Hilbert basis induced by the actual Dirichlet spectral resolution. -/
noncomputable def spectralHeatBasis {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) :
    HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)) :=
  HilbertBasis.mk s.orthonormal
    (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)

/-- Each basis coordinate of a positive-time row is its spectral coefficient. -/
theorem spectral_heat_row_basis_coordinate {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (j : ℕ) :
    (spectralHeatBasis s).repr (∑' i,
      (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) j =
      Real.exp (-s.eigenvalue j * t) * s.eigenfunction j x := by
  classical
  let c : lp (fun _ : ℕ => ℝ) 2 := ⟨_,
    spectral_heat_row_coefficients_memℓp hd hκ h hR s t ht x hx⟩
  have hb (i : ℕ) : spectralHeatBasis s i =
      (s.square_integrable i).toLp (s.eigenfunction i) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) i
  have hs := (spectralHeatBasis s).hasSum_repr_symm c
  have heq : (∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) =
      (spectralHeatBasis s).repr.symm c := by
    simpa only [hb] using hs.tsum_eq
  rw [heq, LinearIsometryEquiv.apply_symm_apply]

#print axioms spectralHeatBasis
#print axioms spectral_heat_row_basis_coordinate

/-- Integration against a heat row is its actual spectral-coordinate pairing. -/
theorem spectral_heat_row_action_coordinates {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    (∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) =
    ∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) *
      (spectralHeatBasis s).repr f i := by
  classical
  let row : Lp ℝ 2 (dirichletVolume ρ R) := ∑' i,
    (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hae := spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx
  calc
    _ = inner ℝ row f := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hae] with y hy
      change row y = _ at hy
      simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]
    _ = ∑' i, inner ℝ row (spectralHeatBasis s i) *
        inner ℝ (spectralHeatBasis s i) f :=
      ((spectralHeatBasis s).tsum_inner_mul_inner row f).symm
    _ = _ := by
      apply tsum_congr
      intro i
      rw [show inner ℝ row (spectralHeatBasis s i) =
        inner ℝ (spectralHeatBasis s i) row from real_inner_comm _ _,
        ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply]
      rw [spectral_heat_row_basis_coordinate hd hκ h hR s t ht x hx]

#print axioms spectral_heat_row_action_coordinates

/-- The actual spectral operator is represented by integration against the heat kernel. -/
theorem spectral_heat_operator_ae_kernel_action {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t f x) =ᵐ[dirichletVolume ρ R]
    (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) := by
  classical
  let b := spectralHeatBasis s
  let F : Lp ℝ 2 (dirichletVolume ρ R) :=
    SpectralHeat.heatOperator b s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f
  let u : ℕ → Lp ℝ 2 (dirichletVolume ρ R) := fun i =>
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * b.repr f i) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hb (i : ℕ) : b i = (s.square_integrable i).toLp (s.eigenfunction i) := by
    exact congrFun (HilbertBasis.coe_mk s.orthonormal
      (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) i
  have hseries : HasSum u F := by
    have hsum := b.hasSum_repr F
    simpa only [SpectralHeat.heatOperator_repr, hb, u, F] using hsum
  have hlim := hseries.summable.tendsto_sum_tsum_nat
  have heq : ∑' i, u i = F := hseries.tsum_eq
  rw [heq] at hlim
  obtain ⟨ns, hns, hpoint⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
  have hsum : ∀ᵐ x ∂dirichletVolume ρ R, ∀ n,
      (∑ i ∈ Finset.range n, u i : Lp ℝ 2 (dirichletVolume ρ R)) x =
        ∑ i ∈ Finset.range n, (Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x) * b.repr f i := by
    rw [ae_all_iff]
    intro n
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.range n) u,
      ae_all_iff.mpr (fun i => Lp.coeFn_smul
        (Real.exp (-s.eigenvalue i * (t : ℝ)) * b.repr f i)
        ((s.square_integrable i).toLp (s.eigenfunction i))),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with x hx hsmul hmode
    rw [hx]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hsmul i]
    simp only [Pi.smul_apply, smul_eq_mul, hmode i]
    ring
  have hball : ∀ᵐ x ∂dirichletVolume ρ R, x ∈ sourceBall 0 R := by
    have hm : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
      rw [← pde_ball_eq_sourceBall _ hR]
      exact (PDE.isOpen_euclideanBall _ _).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)
  filter_upwards [hpoint, hsum, hball] with x hx hxs hxball
  let row : Lp ℝ 2 (dirichletVolume ρ R) := ∑' i,
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hs : Summable (fun i => (Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x) * b.repr f i) := by
    have hh := b.summable_inner_mul_inner row f
    convert hh using 1
    funext i
    rw [show inner ℝ row (b i) = inner ℝ (b i) row from real_inner_comm _ _,
      ← HilbertBasis.repr_apply_apply, ← HilbertBasis.repr_apply_apply]
    rw [spectral_heat_row_basis_coordinate hd hκ h hR s (t : ℝ) ht x hxball]
  have hp := hs.tendsto_sum_tsum_nat.comp hns.tendsto_atTop
  have ha := spectral_heat_row_action_coordinates hd hκ h hR s (t : ℝ) ht x hxball f
  rw [ha]
  apply tendsto_nhds_unique hx
  change Tendsto (fun n => ∑ i ∈ Finset.range (ns n),
    (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) *
      (spectralHeatBasis s).repr f i) atTop
    (nhds (∑' i, (Real.exp (-s.eigenvalue i * (t : ℝ)) * s.eigenfunction i x) *
      (spectralHeatBasis s).repr f i)) at hp
  simpa only [hxs] using hp

#print axioms spectral_heat_operator_ae_kernel_action

/-- The actual weighted Hilbert-space heat row. -/
noncomputable def spectralHeatRow {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (x : PDE.Vec d) :
    Lp ℝ 2 (dirichletVolume ρ R) :=
  ∑' i, (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
    (s.square_integrable i).toLp (s.eigenfunction i)

/-- Inner products of two actual heat rows are the heat kernel at the summed time. -/
theorem spectral_heat_row_inner {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : PDE.Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    inner ℝ (spectralHeatRow s p x) (spectralHeatRow s q y) =
      ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
        s.eigenfunction i x * s.eigenfunction i y := by
  rw [MeasureTheory.L2.inner_def, ← spectral_heat_row_convolution hd hκ h hR s p q hp hq x y hx hy]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s p hp x hx,
    spectral_heat_row_Lp_ae_eq hd hκ h hR s q hq y hy] with z hz hz'
  change spectralHeatRow s p x z = _ at hz
  change spectralHeatRow s q y z = _ at hz'
  simp only [RCLike.inner_apply, conj_trivial, hz, hz', mul_comm]

#print axioms spectralHeatRow
#print axioms spectral_heat_row_inner

/-- The squared distance between heat rows is expressed by three kernel values. -/
theorem spectral_heat_row_dist_sq {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x y : PDE.Vec d)
    (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    ‖spectralHeatRow s t x - spectralHeatRow s t y‖ ^ 2 =
      (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i x * s.eigenfunction i x) -
      2 * (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i x * s.eigenfunction i y) +
      (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i y * s.eigenfunction i y) := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    spectral_heat_row_inner hd hκ h hR s t t ht ht x x hx hx,
    spectral_heat_row_inner hd hκ h hR s t t ht ht x y hx hy,
    spectral_heat_row_inner hd hκ h hR s t t ht ht y y hy hy]

#print axioms spectral_heat_row_dist_sq

/-- A spectrum with diverging eigenvalues has heat rows continuous in weighted L². -/
theorem spectral_heat_row_continuousOn {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (t : ℝ) (ht : 0 < t) :
    ContinuousOn (spectralHeatRow s t) (sourceBall 0 R) := by
  let K : ℝ × PDE.Vec d × PDE.Vec d → ℝ := fun z =>
    ∑' i, Real.exp (-s.eigenvalue i * z.1) *
      s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2
  have hk : ContinuousOn K {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧
      z.2.2 ∈ sourceBall 0 R} := spectral_heat_continuousOn hd hκ h hR s hs
  intro y hy
  have hdiag : ContinuousOn (fun x => K (t + t, x, x)) (sourceBall 0 R) := by
    apply hk.comp (continuous_const.prodMk (continuous_id.prodMk continuous_id)).continuousOn
    intro x hx
    exact ⟨by linarith, hx, hx⟩
  have hcross : ContinuousOn (fun x => K (t + t, x, y)) (sourceBall 0 R) := by
    apply hk.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
    intro x hx
    exact ⟨by linarith, hx, hy⟩
  have hc : ContinuousOn (fun x => K (t + t, x, x) -
      2 * K (t + t, x, y) + K (t + t, y, y)) (sourceBall 0 R) :=
    (hdiag.sub (continuousOn_const.mul hcross)).add continuousOn_const
  have hlim := hc y hy
  change Tendsto (fun x => K (t + t, x, x) - 2 * K (t + t, x, y) +
    K (t + t, y, y)) (nhdsWithin y (sourceBall 0 R))
    (nhds (K (t + t, y, y) - 2 * K (t + t, y, y) + K (t + t, y, y))) at hlim
  have hzero : K (t + t, y, y) - 2 * K (t + t, y, y) + K (t + t, y, y) = 0 := by ring
  rw [hzero] at hlim
  have hsq : Tendsto (fun x => ‖spectralHeatRow s t x - spectralHeatRow s t y‖ ^ 2)
      (nhdsWithin y (sourceBall 0 R)) (nhds 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (spectral_heat_row_dist_sq hd hκ h hR s t ht x y hx hy).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun x => Real.sqrt (‖spectralHeatRow s t x -
    spectralHeatRow s t y‖ ^ 2)) (nhdsWithin y (sourceBall 0 R)) (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

#print axioms spectral_heat_row_continuousOn

/-- Integration against the spectral heat kernel is continuous in the interior. -/
theorem spectral_heat_action_continuousOn {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ContinuousOn (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R)
      (sourceBall 0 R) := by
  apply ((spectral_heat_row_continuousOn hd hκ h hR s hs t ht).inner
    continuousOn_const).congr
  intro x hx
  symm
  change inner ℝ (spectralHeatRow s t x) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hx] with y hy
  change spectralHeatRow s t x y = _ at hy
  simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]

#print axioms spectral_heat_action_continuousOn

/-- A Dirichlet heat row vanishes at every boundary point. -/
theorem spectral_heat_row_zero_frontier {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (t : ℝ) (x : PDE.Vec d)
    (hx : x ∈ frontier (sourceBall 0 R)) : spectralHeatRow s t x = 0 := by
  simp only [spectralHeatRow, s.boundary_zero _ x hx, mul_zero, zero_smul, tsum_zero]

#print axioms spectral_heat_row_zero_frontier

theorem spectral_heat_row_Lp_summable_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ closure (sourceBall 0 R)) :
    Summable (fun i => (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) := by
  by_cases hxi : x ∈ sourceBall 0 R
  · exact spectral_heat_row_Lp_summable hd hκ h hR s t ht x hxi
  · have hopen : IsOpen (sourceBall (0 : PDE.Vec d) R) := by
      rw [← pde_ball_eq_sourceBall _ hR]
      exact PDE.isOpen_euclideanBall _ _
    have hxb : x ∈ frontier (sourceBall 0 R) := by
      simp only [frontier, Set.mem_diff, hopen.interior_eq]
      exact ⟨hx, hxi⟩
    simp only [s.boundary_zero _ x hxb, mul_zero, zero_smul]
    exact summable_zero

#print axioms spectral_heat_row_Lp_summable_closedBall

theorem spectral_heat_row_Lp_ae_eq_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ closure (sourceBall 0 R)) :
    (fun y => spectralHeatRow s t x y) =ᵐ[dirichletVolume ρ R]
      (fun y => ∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) := by
  by_cases hxi : x ∈ sourceBall 0 R
  · exact spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht x hxi
  · have hopen : IsOpen (sourceBall (0 : PDE.Vec d) R) := by
      rw [← pde_ball_eq_sourceBall _ hR]
      exact PDE.isOpen_euclideanBall _ _
    have hxb : x ∈ frontier (sourceBall 0 R) := by
      simp only [frontier, Set.mem_diff, hopen.interior_eq] 
      exact ⟨hx, hxi⟩
    rw [spectral_heat_row_zero_frontier s t x hxb]
    filter_upwards [Lp.coeFn_zero ℝ 2 (dirichletVolume ρ R)] with y hy
    simpa only [s.boundary_zero _ x hxb, mul_zero, zero_mul, tsum_zero, Pi.zero_apply] using hy

#print axioms spectral_heat_row_Lp_ae_eq_closedBall

theorem spectral_heat_row_inner_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : PDE.Vec d) (hx : x ∈ closure (sourceBall 0 R))
    (hy : y ∈ closure (sourceBall 0 R)) :
    inner ℝ (spectralHeatRow s p x) (spectralHeatRow s q y) =
      ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
        s.eigenfunction i x * s.eigenfunction i y := by
  have hopen : IsOpen (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact PDE.isOpen_euclideanBall _ _
  by_cases hxi : x ∈ sourceBall 0 R
  · by_cases hyi : y ∈ sourceBall 0 R
    · exact spectral_heat_row_inner hd hκ h hR s p q hp hq x y hxi hyi
    · have hyb : y ∈ frontier (sourceBall 0 R) := by
        simp only [frontier, Set.mem_diff, hopen.interior_eq]
        exact ⟨hy, hyi⟩
      simp only [spectral_heat_row_zero_frontier s q y hyb, inner_zero_right,
        s.boundary_zero _ y hyb, mul_zero, tsum_zero]
  · have hxb : x ∈ frontier (sourceBall 0 R) := by
      simp only [frontier, Set.mem_diff, hopen.interior_eq]
      exact ⟨hx, hxi⟩
    simp only [spectral_heat_row_zero_frontier s p x hxb, inner_zero_left,
      s.boundary_zero _ x hxb, mul_zero, zero_mul, tsum_zero]

#print axioms spectral_heat_row_inner_closedBall

theorem spectral_heat_row_dist_sq_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (x y : PDE.Vec d)
    (hx : x ∈ closure (sourceBall 0 R)) (hy : y ∈ closure (sourceBall 0 R)) :
    ‖spectralHeatRow s t x - spectralHeatRow s t y‖ ^ 2 =
      (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i x * s.eigenfunction i x) -
      2 * (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i x * s.eigenfunction i y) +
      (∑' i, Real.exp (-s.eigenvalue i * (t + t)) *
        s.eigenfunction i y * s.eigenfunction i y) := by
  rw [norm_sub_sq_real, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    spectral_heat_row_inner_closedBall hd hκ h hR s t t ht ht x x hx hx,
    spectral_heat_row_inner_closedBall hd hκ h hR s t t ht ht x y hx hy,
    spectral_heat_row_inner_closedBall hd hκ h hR s t t ht ht y y hy hy]

#print axioms spectral_heat_row_dist_sq_closedBall

/-- A spectrum with diverging eigenvalues has heat rows continuous in weighted L². -/
theorem spectral_heat_row_continuousOn_closedBall_Lp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (t : ℝ) (ht : 0 < t) :
    ContinuousOn (spectralHeatRow s t) (closure (sourceBall 0 R)) := by
  let K : ℝ × PDE.Vec d × PDE.Vec d → ℝ := fun z =>
    ∑' i, Real.exp (-s.eigenvalue i * z.1) *
      s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2
  have hk : ContinuousOn K {z | 0 < z.1 ∧ z.2.1 ∈ closure (sourceBall 0 R) ∧
      z.2.2 ∈ closure (sourceBall 0 R)} := spectral_heat_continuousOn_closedBall hd hκ h hR s hs
  intro y hy
  have hdiag : ContinuousOn (fun x => K (t + t, x, x)) (closure (sourceBall 0 R)) := by
    apply hk.comp (continuous_const.prodMk (continuous_id.prodMk continuous_id)).continuousOn
    intro x hx
    exact ⟨by linarith, hx, hx⟩
  have hcross : ContinuousOn (fun x => K (t + t, x, y)) (closure (sourceBall 0 R)) := by
    apply hk.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousOn
    intro x hx
    exact ⟨by linarith, hx, hy⟩
  have hc : ContinuousOn (fun x => K (t + t, x, x) -
      2 * K (t + t, x, y) + K (t + t, y, y)) (closure (sourceBall 0 R)) :=
    (hdiag.sub (continuousOn_const.mul hcross)).add continuousOn_const
  have hlim := hc y hy
  change Tendsto (fun x => K (t + t, x, x) - 2 * K (t + t, x, y) +
    K (t + t, y, y)) (nhdsWithin y (closure (sourceBall 0 R)))
    (nhds (K (t + t, y, y) - 2 * K (t + t, y, y) + K (t + t, y, y))) at hlim
  have hzero : K (t + t, y, y) - 2 * K (t + t, y, y) + K (t + t, y, y) = 0 := by ring
  rw [hzero] at hlim
  have hsq : Tendsto (fun x => ‖spectralHeatRow s t x - spectralHeatRow s t y‖ ^ 2)
      (nhdsWithin y (closure (sourceBall 0 R))) (nhds 0) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact (spectral_heat_row_dist_sq_closedBall hd hκ h hR s t ht x y hx hy).symm
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun x => Real.sqrt (‖spectralHeatRow s t x -
    spectralHeatRow s t y‖ ^ 2)) (nhdsWithin y (closure (sourceBall 0 R))) (nhds (Real.sqrt 0)) at hsqrt
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

#print axioms spectral_heat_row_continuousOn_closedBall_Lp

/-- Integration against the spectral heat kernel is continuous in the interior. -/
theorem spectral_heat_action_continuousOn_closedBall {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (t : ℝ) (ht : 0 < t)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    ContinuousOn (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R)
      (closure (sourceBall 0 R)) := by
  apply ((spectral_heat_row_continuousOn_closedBall_Lp hd hκ h hR s hs t ht).inner
    continuousOn_const).congr
  intro x hx
  symm
  change inner ℝ (spectralHeatRow s t x) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [spectral_heat_row_Lp_ae_eq_closedBall hd hκ h hR s t ht x hx] with y hy
  change spectralHeatRow s t x y = _ at hy
  simp only [RCLike.inner_apply, conj_trivial, hy, mul_comm]

#print axioms spectral_heat_action_continuousOn_closedBall

/-- The actual kernel action vanishes at the Dirichlet boundary. -/
theorem spectral_heat_action_zero_frontier {d : ℕ} {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (t : ℝ)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) (x : PDE.Vec d)
    (hx : x ∈ frontier (sourceBall 0 R)) :
    (∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) = 0 := by
  simp only [s.boundary_zero _ x hx, mul_zero, zero_mul, tsum_zero, integral_zero]

#print axioms spectral_heat_action_zero_frontier

/-- An actual Dirichlet spectrum supplies continuous heat rows and actions. -/
theorem exists_sourceBall_spectral_heat_row_action_continuous {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R, ∀ t : ℝ, 0 < t →
      ContinuousOn (spectralHeatRow s t) (sourceBall 0 R) ∧
      ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
        ContinuousOn (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R)
          (sourceBall 0 R) := by
  obtain ⟨s, hs⟩ := exists_sourceBall_dirichletSpectralResolution hd hκ h R hR
  exact ⟨s, fun t ht => ⟨spectral_heat_row_continuousOn hd hκ h hR s hs t ht,
    fun f => spectral_heat_action_continuousOn hd hκ h hR s hs t ht f⟩⟩

#print axioms exists_sourceBall_spectral_heat_row_action_continuous


/-- A single native spectral resolution has a positivity and unit-interval
preserving heat operator. -/
theorem exists_sourceBall_spectral_heat_order {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
          ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x) ∧
        ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
          ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x ∧
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x ≤ 1) := by
  obtain ⟨s, u, hs, hu, hv⟩ :=
    exists_sourceBall_dirichletSpectralResolution_with_variational hd hκ h R hR
  have hb (n : ℕ) : spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    rw [show spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) from
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    exact hu n
  refine ⟨s, hs, ?_⟩
  intro t f
  apply dirichletHilbert_spectralHeat_order hd hκ h R hR s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) u (spectralHeatBasis s) hb _ t f
  intro n w
  rw [hb n]
  exact hv n w

#print axioms exists_sourceBall_spectral_heat_order


/-- The actual weighted measure charges every nonempty open subset of the ball. -/
theorem dirichletVolume_open_pos {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ)
    {V : Set (PDE.Vec d)} (hV : IsOpen V) (hsub : V ⊆ sourceBall 0 R)
    (hne : V.Nonempty) : 0 < dirichletVolume ρ R V := by
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hvol : 0 < (volume : Measure (PDE.Vec d)) V := hV.measure_pos volume hne
  apply pos_iff_ne_zero.mpr
  intro hz
  have hz' := hac hz
  rw [Measure.restrict_apply hV.measurableSet, Set.inter_eq_left.mpr hsub] at hz'
  exact (ne_of_gt hvol) hz'

#print axioms dirichletVolume_open_pos


/-- A continuous function on the ball inherits its almost-everywhere bounds
from the weighted measure. -/
theorem dirichletVolume_continuousOn_ae_bounds {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) {f : PDE.Vec d → ℝ}
    (hf : ContinuousOn f (sourceBall 0 R)) {a b : ℝ}
    (ha : ∀ᵐ x ∂dirichletVolume ρ R, a ≤ f x)
    (hb : ∀ᵐ x ∂dirichletVolume ρ R, f x ≤ b) :
    ∀ x ∈ sourceBall 0 R, a ≤ f x ∧ f x ≤ b := by
  intro x hx
  have hOm : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  constructor
  · by_contra hn
    have hlt : f x < a := lt_of_not_ge hn
    let V := sourceBall (0 : PDE.Vec d) R ∩ f ⁻¹' Set.Iio a
    have hV : IsOpen V := hf.isOpen_inter_preimage hOm isOpen_Iio
    have hz : dirichletVolume ρ R V = 0 := by
      apply measure_mono_null _ (ae_iff.mp ha)
      intro y hy
      exact not_le_of_gt hy.2
    exact (ne_of_gt (dirichletVolume_open_pos hκ h R hV
      Set.inter_subset_left ⟨x, hx, hlt⟩)) hz
  · by_contra hn
    have hlt : b < f x := lt_of_not_ge hn
    let V := sourceBall (0 : PDE.Vec d) R ∩ f ⁻¹' Set.Ioi b
    have hV : IsOpen V := hf.isOpen_inter_preimage hOm isOpen_Ioi
    have hz : dirichletVolume ρ R V = 0 := by
      apply measure_mono_null _ (ae_iff.mp hb)
      intro y hy
      exact not_le_of_gt hy.2
    exact (ne_of_gt (dirichletVolume_open_pos hκ h R hV
      Set.inter_subset_left ⟨x, hx, hlt⟩)) hz

#print axioms dirichletVolume_continuousOn_ae_bounds


/-- The continuous kernel action of one native spectrum preserves the unit
interval at every interior point. -/
theorem exists_sourceBall_spectral_heat_action_order {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)),
        (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ x ∈ sourceBall 0 R,
          0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
            s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
          (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
            s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1 := by
  obtain ⟨s, hs, hord⟩ := exists_sourceBall_spectral_heat_order hd hκ h R hR
  refine ⟨s, hs, ?_⟩
  intro t ht f hf
  have ha := (hord t f).2 hf
  have he := spectral_heat_operator_ae_kernel_action hd hκ h hR s t ht f
  have hb : ∀ᵐ x ∂dirichletVolume ρ R,
      0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
      (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1 := by
    filter_upwards [ha, he] with x hx heq
    rw [← heq]
    exact hx
  exact dirichletVolume_continuousOn_ae_bounds hκ h R
    (spectral_heat_action_continuousOn hd hκ h hR s hs t ht f)
    (hb.mono fun _ hx => hx.1) (hb.mono fun _ hx => hx.2)

#print axioms exists_sourceBall_spectral_heat_action_order


/-- The same native spectrum has a nonnegative sub-Markov total mass. -/
theorem exists_sourceBall_spectral_heat_mass_bounds {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        0 ≤ (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ∧
        (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ≤ 1 := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨s, hs, ha⟩ := exists_sourceBall_spectral_heat_action_order hd hκ h R hR
  let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
  have hone : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ one x ∧ one x ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
    simp only [one, Function.const_apply] at hx
    rw [hx]
    exact ⟨zero_le_one, le_rfl⟩
  refine ⟨s, hs, ?_⟩
  intro t ht x hx
  have hb := ha t ht one hone x hx
  have he : (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
      s.eigenfunction i x * s.eigenfunction i y) * one y ∂dirichletVolume ρ R) =
      ∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy
    simp only [one, Function.const_apply] at hy
    rw [hy, mul_one]
  rwa [he] at hb

#print axioms exists_sourceBall_spectral_heat_mass_bounds


/-- One native spectrum has a pointwise nonnegative heat kernel and its
continuous integral action preserves the unit interval. -/
theorem exists_sourceBall_spectral_heat_kernel_nonneg {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) →
        ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)),
          (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
          ∀ x ∈ sourceBall 0 R,
            0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
              s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
            (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
              s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1) ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y := by
  classical
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨s, hs, ha⟩ := exists_sourceBall_spectral_heat_action_order hd hκ h R hR
  refine ⟨s, hs, ha, ?_⟩
  intro t ht x hx y hy
  let row : PDE.Vec d → ℝ := fun z => ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
    s.eigenfunction i x * s.eigenfunction i z
  have hc : ContinuousOn row (sourceBall 0 R) := by
    apply (spectral_heat_continuousOn hd hκ h hR s hs).comp
      (continuousOn_const.prodMk (continuousOn_const.prodMk continuousOn_id))
    intro z hz
    exact ⟨ht, hx, hz⟩
  by_contra hn
  have hneg : row y < 0 := lt_of_not_ge hn
  let V := sourceBall (0 : PDE.Vec d) R ∩ row ⁻¹' Set.Iio 0
  have hV : IsOpen V := hc.isOpen_inter_preimage (dirichletBall (d := d) R).isOpen isOpen_Iio
  have hpos : 0 < dirichletVolume ρ R V :=
    dirichletVolume_open_pos hκ h R hV Set.inter_subset_left ⟨y, hy, hneg⟩
  let f : Lp ℝ 2 (dirichletVolume ρ R) :=
    indicatorConstLp 2 hV.measurableSet (measure_ne_top _ _) (1 : ℝ)
  have hf : ∀ᵐ z ∂dirichletVolume ρ R, 0 ≤ f z ∧ f z ≤ 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hV.measurableSet)
      (hμs := measure_ne_top (dirichletVolume ρ R) V) (c := (1 : ℝ))] with z hz
    rw [show f z = V.indicator (fun _ => (1 : ℝ)) z from hz]
    by_cases hzV : z ∈ V <;> simp [hzV]
  have haction := (ha t ht f hf x hx).1
  have hrow : Integrable row (dirichletVolume ρ R) :=
    (spectral_heat_row_memLp hd hκ h hR s t ht x hx).integrable (by norm_num)
  let g : PDE.Vec d → ℝ := V.indicator (fun z => -row z)
  have hg : Integrable g (dirichletVolume ρ R) := hrow.neg.indicator hV.measurableSet
  have hgn : 0 ≤ g := by
    intro z
    by_cases hz : z ∈ V
    · simp only [g, Set.indicator_of_mem hz]
      have hlt : row z < 0 := hz.2
      exact neg_nonneg.mpr hlt.le
    · simp [g, hz]
  have hsupport : V ⊆ Function.support g := by
    intro z hz
    simp only [Function.mem_support, g, Set.indicator_of_mem hz]
    have hlt : row z < 0 := hz.2
    exact neg_ne_zero.mpr (ne_of_lt hlt)
  have hgpos : 0 < ∫ z, g z ∂dirichletVolume ρ R :=
    (integral_pos_iff_support_of_nonneg hgn hg).2 (lt_of_lt_of_le hpos (measure_mono hsupport))
  have heq : (∫ z, row z * f z ∂dirichletVolume ρ R) =
      -(∫ z, g z ∂dirichletVolume ρ R) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hV.measurableSet)
      (hμs := measure_ne_top (dirichletVolume ρ R) V) (c := (1 : ℝ))] with z hz
    rw [show f z = V.indicator (fun _ => (1 : ℝ)) z from hz]
    by_cases hzV : z ∈ V <;> simp [g, hzV]
  change 0 ≤ ∫ z, row z * f z ∂dirichletVolume ρ R at haction
  linarith

#print axioms exists_sourceBall_spectral_heat_kernel_nonneg


/-- A single actual spectral resolution supplies the continuous, nonnegative
sub-Markov heat kernel and its weighted L² action. -/
theorem exists_sourceBall_spectral_heat_kernel_submarkov {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ s : DirichletSpectralResolution ρ α R,
      Tendsto s.eigenvalue atTop atTop ∧
      ContinuousOn (fun z : ℝ × PDE.Vec d × PDE.Vec d =>
        ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2.1 * s.eigenfunction i z.2.2)
        {z | 0 < z.1 ∧ z.2.1 ∈ sourceBall 0 R ∧ z.2.2 ∈ sourceBall 0 R} ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, Summable (fun i => Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y)) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)),
        (fun x => SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f x) =ᵐ[dirichletVolume ρ R]
        (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R)) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y) ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        0 ≤ (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ∧
        (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ≤ 1 := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨s, hs, ha, hn⟩ := exists_sourceBall_spectral_heat_kernel_nonneg hd hκ h R hR
  refine ⟨s, hs, spectral_heat_continuousOn hd hκ h hR s hs, ?_, ?_, hn, ?_⟩
  · intro t ht x hx y hy
    have hxR : euclideanNorm x < R := by
      simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hx
    have hyR : euclideanNorm y < R := by
      simpa only [sourceBall, Set.mem_ofPred_eq, sub_zero] using hy
    let r : ℝ := (max (euclideanNorm x) (euclideanNorm y) + R) / 2
    have hr : r < R := by dsimp [r]; have := max_lt hxR hyR; linarith
    have hxr : x ∈ sourceBall 0 r := by
      simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
      dsimp [r]
      have := le_max_left (euclideanNorm x) (euclideanNorm y)
      have := max_lt hxR hyR
      linarith
    have hyr : y ∈ sourceBall 0 r := by
      simp only [sourceBall, Set.mem_ofPred_eq, sub_zero]
      dsimp [r]
      have := le_max_right (euclideanNorm x) (euclideanNorm y)
      have := max_lt hxR hyR
      linarith
    exact spectral_heat_cross_summable hd hκ h hR hr s t ht x y hxr hyr
  · exact fun t ht f => spectral_heat_operator_ae_kernel_action hd hκ h hR s t ht f
  · let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
    have hone : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ one x ∧ one x ≤ 1 := by
      filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
      simp only [one, Function.const_apply] at hx
      rw [hx]
      exact ⟨zero_le_one, le_rfl⟩
    intro t ht x hx
    have hb := ha t ht one hone x hx
    have he : (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * one y ∂dirichletVolume ρ R) =
        ∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy
      simp only [one, Function.const_apply] at hy
      rw [hy, mul_one]
    rwa [he] at hb

#print axioms exists_sourceBall_spectral_heat_kernel_submarkov

/-- The same spectral heat operator advances a positive-time row. -/
theorem spectral_heat_operator_row {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (p : ℝ≥0) (q : ℝ) (hq : 0 < q) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) p (spectralHeatRow s q y) =
      spectralHeatRow s ((p : ℝ) + q) y := by
  apply (spectralHeatBasis s).repr.injective
  apply lp.ext
  funext n
  rw [SpectralHeat.heatOperator_repr]
  change _ = (spectralHeatBasis s).repr (spectralHeatRow s ((p : ℝ) + q) y) n
  rw [show (spectralHeatBasis s).repr (spectralHeatRow s q y) n =
    Real.exp (-s.eigenvalue n * q) * s.eigenfunction n y from
    spectral_heat_row_basis_coordinate hd hκ h hR s q hq y hy n]
  rw [show (spectralHeatBasis s).repr (spectralHeatRow s ((p : ℝ) + q) y) n =
    Real.exp (-s.eigenvalue n * ((p : ℝ) + q)) * s.eigenfunction n y from
    spectral_heat_row_basis_coordinate hd hκ h hR s _ (add_pos_of_nonneg_of_pos p.coe_nonneg hq) y hy n]
  rw [mul_add, Real.exp_add]
  ring

#print axioms spectral_heat_operator_row

/-- The heat multiplier lifts through the energy inverse for the same native
variational eigenbasis used to construct the spectral resolution. -/
theorem spectral_heat_native_lift {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t ∧
        (∀ f v, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => v.val (some i) x)) =
          inner ℝ (SpectralHeat.firstMoment (spectralHeatBasis s) s.eigenvalue
            s.eigenvalue_pos t ht f) (J v)) ∧
        ∀ f, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  let b := spectralHeatBasis s
  obtain ⟨c, hc, S, _hcomp, _hsa, _hinj, _hdense, _hpositive, hnorm, hS⟩ :=
    exists_compact_dirichletHilbert_energyInverse hd hκ h R hR
  have hGe (n : ℕ) : (J.comp S) (b n) = (s.eigenvalue n)⁻¹ • b n := by
    have hu : u n = S (s.eigenvalue n • J (u n)) := by
      apply (hS _ _).mpr
      intro v
      simpa only [real_inner_smul_left] using hvar n v
    have hx : b n = s.eigenvalue n • ((J.comp S) (b n)) := by
      rw [hb]
      change J (u n) = s.eigenvalue n • J (S (J (u n)))
      conv_lhs => rw [hu]
      rw [map_smul, map_smul]
    calc
      _ = (s.eigenvalue n)⁻¹ • (s.eigenvalue n • ((J.comp S) (b n))) := by
        rw [smul_smul, inv_mul_cancel₀ (s.eigenvalue_pos n).ne', one_smul]
      _ = _ := congrArg ((s.eigenvalue n)⁻¹ • ·) hx.symm
  let Q := fun (t : ℝ≥0) (ht : 0 < t) =>
    S.comp (SpectralHeat.firstMoment b s.eigenvalue s.eigenvalue_pos t ht)
  have hfactor (t : ℝ≥0) (ht : 0 < t) :
      J.comp (Q t ht) = SpectralHeat.heatOperator b s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t :=
    (SpectralHeat.heatOperator_eq_inverse_comp_firstMoment
      b s.eigenvalue s.eigenvalue_pos (J.comp S) hGe t ht).symm
  have hform (t : ℝ≥0) (ht : 0 < t) (f) (v) :
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
          (fun i => v.val (some i) x)) =
        inner ℝ (SpectralHeat.firstMoment b s.eigenvalue s.eigenvalue_pos t ht f) (J v) :=
    (hS _ _).mp rfl v
  refine ⟨Q, ?_, ?_⟩
  · intro f
    exact S.continuous.comp (SpectralHeat.firstMoment_continuous b s.eigenvalue s.eigenvalue_pos f)
  intro t ht
  refine ⟨hfactor t ht, hform t ht, ?_⟩
  intro f
  rw [hform t ht f (Q t ht f)]
  have hJ : J (Q t ht f) = SpectralHeat.heatOperator b s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) t f :=
    congrArg (fun T : _ →L[ℝ] _ => T f) (hfactor t ht)
  rw [hJ]
  calc
    _ ≤ ‖SpectralHeat.firstMoment b s.eigenvalue s.eigenvalue_pos t ht f‖ *
        ‖SpectralHeat.heatOperator b s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f‖ :=
      real_inner_le_norm _ _
    _ ≤ ((t : ℝ)⁻¹ * ‖f‖) * ‖f‖ := mul_le_mul
      (SpectralHeat.firstMoment_norm_le _ _ _ _ _ _)
      (SpectralHeat.heatOperator_norm_le _ _ _ _ _) (norm_nonneg _)
      (mul_nonneg (inv_nonneg.mpr t.coe_nonneg) (norm_nonneg _))
    _ = _ := by ring

#print axioms spectral_heat_native_lift

/-- A positive-time spectral row has a native energy lift through the
same heat multiplier, with the half-time energy estimate. -/
theorem spectral_heat_row_native_lift {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (ht : 0 < t) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ v : DirichletHilbertSpace (d := d) R hR,
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v =
        spectralHeatRow s t y ∧
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => v.val (some i) x))
          (fun i => v.val (some i) x)) ≤
        ((t : ℝ) / 2)⁻¹ * ‖spectralHeatRow s ((t : ℝ) / 2) y‖ ^ 2 := by
  obtain ⟨Q, _, hQ⟩ := spectral_heat_native_lift hd hκ h R hR s u hb hvar
  let τ : ℝ≥0 := t / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hτreal : (τ : ℝ) = (t : ℝ) / 2 := by simp [τ]
  refine ⟨Q τ hτ (spectralHeatRow s τ y), ?_, ?_⟩
  · have hf := congrArg (fun T : _ →L[ℝ] _ => T (spectralHeatRow s τ y)) (hQ τ hτ).1
    change _ = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
      (fun n => (s.eigenvalue_pos n).le) τ (spectralHeatRow s τ y) at hf
    simp only [ContinuousLinearMap.comp_apply] at hf
    rw [hf, spectral_heat_operator_row hd hκ h hR s τ τ hτ y hy]
    congr 1
    rw [hτreal]
    ring
  · simpa only [hτreal] using (hQ τ hτ).2.2 (spectralHeatRow s τ y)

#print axioms spectral_heat_row_native_lift

/-- A native lift of the row provides its actual global zero-extension weak
gradient. -/
theorem spectral_heat_row_native_weakGradient {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (v : DirichletHilbertSpace (d := d) R hR)
    (hv : dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) v =
      spectralHeatRow s t y) :
    EinsteinRelation.HasWeakGradient Set.univ
      ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
        Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
      (dirichletHilbertZeroExtensionGrad R hR v) := by
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have he : (fun x => v.val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
      (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i y * s.eigenfunction i x) := by
    apply hac.ae_le
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) v,
      spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht y hy] with x hx hy'
    change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ v) x = v.val none x at hx
    change (spectralHeatRow s t y) x = _ at hy'
    rw [hv] at hx
    exact hx.symm.trans hy'
  have hball : MeasurableSet (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen.measurableSet
  have hz := (ae_eq_restrict_iff_indicator_ae_eq hball).mp he
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ
    (dirichletHilbert_global_zeroExtension R hR v).2.2
  · simpa only [Measure.restrict_univ, dirichletHilbertZeroExtension] using hz
  · exact ae_eq_refl _

#print axioms spectral_heat_row_native_weakGradient

/-- On a compact positive-time interval, a fixed earlier row supplies one
continuous native lift. Its graph norm bounds its value and every gradient
coordinate in the genuine L² carrier. -/
theorem spectral_heat_row_continuous_native_strip {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b,
        ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
        ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C := by
  obtain ⟨Q, hQc, hQ⟩ := spectral_heat_native_lift hd hκ h R hR s u hb hvar
  let τ : ℝ≥0 := (a / 2).toNNReal
  have hτ : 0 < τ := Real.toNNReal_pos.mpr (half_pos ha)
  have hτval : (τ : ℝ) = a / 2 := Real.coe_toNNReal _ (half_pos ha).le
  let p : ℝ → ℝ≥0 := fun t => (max t a - a / 2).toNNReal
  have hp (t : ℝ) : 0 < p t := by
    apply Real.toNNReal_pos.mpr
    have := le_max_right t a
    linarith
  let V : ℝ → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q (p t) (hp t) (spectralHeatRow s τ y)
  have hpc : Continuous p := continuous_real_toNNReal.comp
    ((continuous_id.max continuous_const).sub continuous_const)
  have hVc : Continuous V := (hQc (spectralHeatRow s τ y)).comp
    (hpc.subtype_mk hp)
  refine ⟨V, hVc, ?_, ?_⟩
  · intro t ht
    have hfactor := congrArg (fun T : _ →L[ℝ] _ => T (spectralHeatRow s τ y))
      (hQ (p t) (hp t)).1
    simp only [ContinuousLinearMap.comp_apply] at hfactor
    rw [show V t = Q (p t) (hp t) (spectralHeatRow s τ y) from rfl, hfactor,
      spectral_heat_operator_row hd hκ h hR s (p t) τ hτ y hy]
    congr 1
    have hmax : max t a = t := max_eq_left ht.1
    have hnonneg : 0 ≤ t - a / 2 := by linarith [ht.1]
    simp only [p, hmax, Real.coe_toNNReal _ hnonneg, hτval]
    ring
  · obtain ⟨C, hC⟩ := (isCompact_Icc.bddAbove_image hVc.norm.continuousOn)
    refine ⟨C, ?_⟩
    intro t ht
    have hn : ‖V t‖ ≤ C := hC ⟨t, ht, rfl⟩
    have hc := hilbertToSobolev_norm_le _ (V t).val
    exact ⟨hn, hc.1.trans hn, fun i => (hc.2 i).trans hn⟩

#print axioms spectral_heat_row_continuous_native_strip

/-- Original coefficients produce one spectral resolution together with its
native variational modes and positive-time energy lift. -/
theorem exists_sourceBall_spectral_heat_native_lift {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = J (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (u n)) (J w)) ∧
      ∃ Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
        (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
        ∀ t ht, J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s)
          s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t ∧
        (∀ f v, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => v.val (some i) x)) =
          inner ℝ (SpectralHeat.firstMoment (spectralHeatBasis s) s.eigenvalue
            s.eigenvalue_pos t ht f) (J v)) ∧
        ∀ f, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2 := by
  dsimp only
  obtain ⟨s, u, hs, hu, hv⟩ :=
    exists_sourceBall_dirichletSpectralResolution_with_variational hd hκ h R hR
  have hb (n : ℕ) : spectralHeatBasis s n =
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n) := by
    rw [show spectralHeatBasis s n = (s.square_integrable n).toLp (s.eigenfunction n) from
      congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) n]
    exact hu n
  exact ⟨s, u, hs, hb, hv, spectral_heat_native_lift hd hκ h R hR s u hb hv⟩

#print axioms exists_sourceBall_spectral_heat_native_lift

/-- One actual variational spectrum supplies its native row lifts and
continuous, bounded positive-time strips with genuine weak gradients. -/
theorem exists_sourceBall_spectral_heat_native_row_strips {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = J (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (u n)) (J w)) ∧
      (∀ (t : ℝ≥0) (_ht : 0 < t) (y : PDE.Vec d), y ∈ sourceBall 0 R →
        ∃ v : DirichletHilbertSpace (d := d) R hR,
          J v = spectralHeatRow s t y ∧
          (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => v.val (some i) x))
              (fun i => v.val (some i) x)) ≤
            ((t : ℝ) / 2)⁻¹ * ‖spectralHeatRow s ((t : ℝ) / 2) y‖ ^ 2) ∧
      ∀ (a b : ℝ), 0 < a → ∀ y : PDE.Vec d, y ∈ sourceBall 0 R →
        ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (C : ℝ),
          Continuous V ∧ ∀ t ∈ Set.Icc a b,
            J (V t) = spectralHeatRow s t y ∧
            (∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec (fun i => (V t).val (some i) x))
                (fun i => (V t).val (some i) x)) ≤
              (t / 2)⁻¹ * ‖spectralHeatRow s (t / 2) y‖ ^ 2 ∧
            EinsteinRelation.HasWeakGradient Set.univ
              ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
                Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
              (dirichletHilbertZeroExtensionGrad R hR (V t)) ∧
            ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
              ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C := by
  dsimp only
  obtain ⟨s, u, hs, hb, hv, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  refine ⟨s, u, hs, hb, hv, ?_, ?_⟩
  · intro t ht y hy
    exact spectral_heat_row_native_lift hd hκ h R hR s u hb hv t ht y hy
  · intro a b ha y hy
    obtain ⟨V, hVc, hV, C, hC⟩ :=
      spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hv a b ha y hy
    refine ⟨V, C, hVc, ?_⟩
    intro t ht
    have htp : 0 < t := lt_of_lt_of_le ha ht.1
    obtain ⟨v, hvrow, hvenergy⟩ := spectral_heat_row_native_lift hd hκ h R hR
      s u hb hv t.toNNReal (Real.toNNReal_pos.mpr htp) y hy
    have hvrow' : dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) v = spectralHeatRow s t y := by
      simpa only [Real.coe_toNNReal t htp.le] using hvrow
    have heq : V t = v := (injective_dirichletHilbertInclusion hκ h R hR)
      ((hV t ht).trans hvrow'.symm)
    have henergy : (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => (V t).val (some i) x)) ≤
        (t / 2)⁻¹ * ‖spectralHeatRow s (t / 2) y‖ ^ 2 := by
      rw [heq]
      simpa only [Real.coe_toNNReal t htp.le] using hvenergy
    refine ⟨hV t ht, henergy, ?_, hC t ht⟩
    exact spectral_heat_row_native_weakGradient hd hκ h R hR s t
      (lt_of_lt_of_le ha ht.1) y hy (V t) (hV t ht)

#print axioms exists_sourceBall_spectral_heat_native_row_strips

/-- Order preservation for the heat operator of the given variational spectrum. -/
theorem spectral_heat_order_of_variational {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
      ∀ (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)),
        ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x) →
          ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x) ∧
        ((∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
          ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x ∧
            SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) t f x ≤ 1) := by
  intro t f
  apply dirichletHilbert_spectralHeat_order hd hκ h R hR s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le) u (spectralHeatBasis s) hb _ t f
  intro n w
  rw [hb n]
  exact hv n w

#print axioms spectral_heat_order_of_variational

/-- Pointwise order for the action of that same spectrum. -/
theorem spectral_heat_action_order_of_variational {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
      ∀ (t : ℝ≥0), 0 < (t : ℝ) →
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)),
        (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
        ∀ x ∈ sourceBall 0 R,
          0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
            s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
          (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
            s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1 := by
  have hord := spectral_heat_order_of_variational hd hκ h R hR s u hb hv
  intro t ht f hf
  have ha := (hord t f).2 hf
  have he := spectral_heat_operator_ae_kernel_action hd hκ h hR s t ht f
  have hb : ∀ᵐ x ∂dirichletVolume ρ R,
      0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
      (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1 := by
    filter_upwards [ha, he] with x hx heq
    rw [← heq]
    exact hx
  exact dirichletVolume_continuousOn_ae_bounds hκ h R
    (spectral_heat_action_continuousOn hd hκ h hR s hs t ht f)
    (hb.mono fun _ hx => hx.1) (hb.mono fun _ hx => hx.2)

#print axioms spectral_heat_action_order_of_variational

/-- Pointwise nonnegativity for that same variational spectrum. -/
theorem spectral_heat_kernel_nonneg_of_variational {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
      (∀ (t : ℝ≥0), 0 < (t : ℝ) →
        ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)),
          (∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ f x ∧ f x ≤ 1) →
          ∀ x ∈ sourceBall 0 R,
            0 ≤ (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
              s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ∧
            (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
              s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) ≤ 1) ∧
      ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y := by
  classical
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have ha := spectral_heat_action_order_of_variational hd hκ h R hR s hs u hb hv
  refine ⟨ha, ?_⟩
  intro t ht x hx y hy
  let row : PDE.Vec d → ℝ := fun z => ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
    s.eigenfunction i x * s.eigenfunction i z
  have hc : ContinuousOn row (sourceBall 0 R) := by
    apply (spectral_heat_continuousOn hd hκ h hR s hs).comp
      (continuousOn_const.prodMk (continuousOn_const.prodMk continuousOn_id))
    intro z hz
    exact ⟨ht, hx, hz⟩
  by_contra hn
  have hneg : row y < 0 := lt_of_not_ge hn
  let V := sourceBall (0 : PDE.Vec d) R ∩ row ⁻¹' Set.Iio 0
  have hV : IsOpen V := hc.isOpen_inter_preimage (dirichletBall (d := d) R).isOpen isOpen_Iio
  have hpos : 0 < dirichletVolume ρ R V :=
    dirichletVolume_open_pos hκ h R hV Set.inter_subset_left ⟨y, hy, hneg⟩
  let f : Lp ℝ 2 (dirichletVolume ρ R) :=
    indicatorConstLp 2 hV.measurableSet (measure_ne_top _ _) (1 : ℝ)
  have hf : ∀ᵐ z ∂dirichletVolume ρ R, 0 ≤ f z ∧ f z ≤ 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hV.measurableSet)
      (hμs := measure_ne_top (dirichletVolume ρ R) V) (c := (1 : ℝ))] with z hz
    rw [show f z = V.indicator (fun _ => (1 : ℝ)) z from hz]
    by_cases hzV : z ∈ V <;> simp [hzV]
  have haction := (ha t ht f hf x hx).1
  have hrow : Integrable row (dirichletVolume ρ R) :=
    (spectral_heat_row_memLp hd hκ h hR s t ht x hx).integrable (by norm_num)
  let g : PDE.Vec d → ℝ := V.indicator (fun z => -row z)
  have hg : Integrable g (dirichletVolume ρ R) := hrow.neg.indicator hV.measurableSet
  have hgn : 0 ≤ g := by
    intro z
    by_cases hz : z ∈ V
    · simp only [g, Set.indicator_of_mem hz]
      have hlt : row z < 0 := hz.2
      exact neg_nonneg.mpr hlt.le
    · simp [g, hz]
  have hsupport : V ⊆ Function.support g := by
    intro z hz
    simp only [Function.mem_support, g, Set.indicator_of_mem hz]
    have hlt : row z < 0 := hz.2
    exact neg_ne_zero.mpr (ne_of_lt hlt)
  have hgpos : 0 < ∫ z, g z ∂dirichletVolume ρ R :=
    (integral_pos_iff_support_of_nonneg hgn hg).2 (lt_of_lt_of_le hpos (measure_mono hsupport))
  have heq : (∫ z, row z * f z ∂dirichletVolume ρ R) =
      -(∫ z, g z ∂dirichletVolume ρ R) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hV.measurableSet)
      (hμs := measure_ne_top (dirichletVolume ρ R) V) (c := (1 : ℝ))] with z hz
    rw [show f z = V.indicator (fun _ => (1 : ℝ)) z from hz]
    by_cases hzV : z ∈ V <;> simp [g, hzV]
  change 0 ≤ ∫ z, row z * f z ∂dirichletVolume ρ R at haction
  linarith

#print axioms spectral_heat_kernel_nonneg_of_variational

/-- Native row strips and sub-Markov bounds for one actual spectrum. -/
theorem exists_sourceBall_spectral_heat_native_row_strips_submarkov {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = J (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (u n)) (J w)) ∧
      (∀ (t : ℝ≥0) (_ht : 0 < t) (y : PDE.Vec d), y ∈ sourceBall 0 R →
        ∃ v : DirichletHilbertSpace (d := d) R hR,
          J v = spectralHeatRow s t y ∧
          (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => v.val (some i) x))
              (fun i => v.val (some i) x)) ≤
            ((t : ℝ) / 2)⁻¹ * ‖spectralHeatRow s ((t : ℝ) / 2) y‖ ^ 2) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        0 ≤ (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ∧
        (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ≤ 1) ∧
      ∀ (a b : ℝ), 0 < a → ∀ y : PDE.Vec d, y ∈ sourceBall 0 R →
        ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (C : ℝ),
          Continuous V ∧ ∀ t ∈ Set.Icc a b,
            J (V t) = spectralHeatRow s t y ∧
            (∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec (fun i => (V t).val (some i) x))
                (fun i => (V t).val (some i) x)) ≤
              (t / 2)⁻¹ * ‖spectralHeatRow s (t / 2) y‖ ^ 2 ∧
            EinsteinRelation.HasWeakGradient Set.univ
              ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
                Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
              (dirichletHilbertZeroExtensionGrad R hR (V t)) ∧
            ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
              ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C := by
  dsimp only
  obtain ⟨s, u, hs, hb, hv, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  refine ⟨s, u, hs, hb, hv, ?_, ?_, ?_, ?_⟩
  · intro t ht y hy
    exact spectral_heat_row_native_lift hd hκ h R hR s u hb hv t ht y hy
  · exact (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hv).2
  · haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
      dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
    have hone : ∀ᵐ x ∂dirichletVolume ρ R, 0 ≤ one x ∧ one x ≤ 1 := by
      filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with x hx
      simp only [one, Function.const_apply] at hx
      rw [hx]
      exact ⟨zero_le_one, le_rfl⟩
    intro t ht x hx
    have hm := spectral_heat_action_order_of_variational hd hκ h R hR s hs u hb hv
      t ht one hone x hx
    have he : (∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * one y ∂dirichletVolume ρ R) =
        ∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy
      simp only [one, Function.const_apply] at hy
      rw [hy, mul_one]
    rwa [he] at hm
  · intro a b ha y hy
    obtain ⟨V, hVc, hV, C, hC⟩ :=
      spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hv a b ha y hy
    refine ⟨V, C, hVc, ?_⟩
    intro t ht
    have htp : 0 < t := lt_of_lt_of_le ha ht.1
    obtain ⟨v, hvrow, hvenergy⟩ := spectral_heat_row_native_lift hd hκ h R hR
      s u hb hv t.toNNReal (Real.toNNReal_pos.mpr htp) y hy
    have hvrow' : dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) v = spectralHeatRow s t y := by
      simpa only [Real.coe_toNNReal t htp.le] using hvrow
    have heq : V t = v := (injective_dirichletHilbertInclusion hκ h R hR)
      ((hV t ht).trans hvrow'.symm)
    have henergy : (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => (V t).val (some i) x)) ≤
        (t / 2)⁻¹ * ‖spectralHeatRow s (t / 2) y‖ ^ 2 := by
      rw [heq]
      simpa only [Real.coe_toNNReal t htp.le] using hvenergy
    refine ⟨hV t ht, henergy, ?_, hC t ht⟩
    exact spectral_heat_row_native_weakGradient hd hκ h R hR s t
      (lt_of_lt_of_le ha ht.1) y hy (V t) (hV t ht)

#print axioms exists_sourceBall_spectral_heat_native_row_strips_submarkov

/-- The heat lift of the given variational spectrum satisfies the weak evolution
identity against every native Dirichlet test vector. -/
theorem spectral_heat_native_weakFlow {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t ∧
        (∀ f, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2) ∧
        ∀ f v, HasDerivAt
          (fun r : ℝ => inner ℝ
            (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
          (-(∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨Q, hcont, hQ⟩ := spectral_heat_native_lift hd hκ h R hR s u hb hvar
  refine ⟨Q, hcont, ?_⟩
  intro t ht
  obtain ⟨hfactor, hform, henergy⟩ := hQ t ht
  refine ⟨hfactor, henergy, ?_⟩
  intro f v
  have hderiv := (innerSL ℝ (J v)).hasFDerivAt.comp_hasDerivAt (t : ℝ)
    (SpectralHeat.heatOperator_hasDerivAt (spectralHeatBasis s) s.eigenvalue
      s.eigenvalue_pos t ht f)
  change HasDerivAt
    (fun r : ℝ => inner ℝ (J v)
      (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) r.toNNReal f))
    (inner ℝ (J v) (-SpectralHeat.firstMoment (spectralHeatBasis s)
      s.eigenvalue s.eigenvalue_pos t ht f)) (t : ℝ) at hderiv
  have hpair : HasDerivAt
      (fun r : ℝ => inner ℝ
        (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
      (-inner ℝ (SpectralHeat.firstMoment (spectralHeatBasis s)
        s.eigenvalue s.eigenvalue_pos t ht f) (J v)) (t : ℝ) := by
    simpa only [Function.comp_apply, innerSL_apply_apply, inner_neg_right,
      real_inner_comm] using hderiv
  rw [← hform f v] at hpair
  exact hpair

#print axioms spectral_heat_native_weakFlow

/-- Original coefficients supply one native variational spectrum and its weak heat flow. -/
theorem exists_sourceBall_spectral_heat_native_weakFlow {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = J (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (u n)) (J w)) ∧
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      (∀ f, Continuous (fun t : {t : ℝ≥0 // 0 < t} => Q t.val t.property f)) ∧
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t ∧
        (∀ f, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
            (fun i => (Q t ht f).val (some i) x)) ≤ (t : ℝ)⁻¹ * ‖f‖ ^ 2) ∧
        ∀ f v, HasDerivAt
          (fun r : ℝ => inner ℝ
            (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) r.toNNReal f) (J v))
          (-(∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => v.val (some i) x))) (t : ℝ) := by
  dsimp only
  obtain ⟨s, u, hs, hb, hv, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  exact ⟨s, u, hs, hb, hv, spectral_heat_native_weakFlow hd hκ h R hR s u hb hv⟩

#print axioms exists_sourceBall_spectral_heat_native_weakFlow

/-- On a positive-time strip, one continuous native row lift has the actual
weak spatial gradient and satisfies the time derivative against native tests. -/
theorem spectral_heat_row_native_weakFlow_strip {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧
      (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      (∀ t, a < t → ∀ v, HasDerivAt
        (fun r : ℝ => inner ℝ (spectralHeatRow s r y) (J v))
        (-(∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => v.val (some i) x))) t) ∧
      ∃ C : ℝ, ∀ t ∈ Set.Icc a b,
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
          (dirichletHilbertZeroExtensionGrad R hR (V t)) ∧
        ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
        ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨Q, hQc, hQ⟩ := spectral_heat_native_weakFlow hd hκ h R hR s u hb hvar
  let τ : ℝ≥0 := (a / 2).toNNReal
  have hτ : 0 < τ := Real.toNNReal_pos.mpr (half_pos ha)
  have hτval : (τ : ℝ) = a / 2 := Real.coe_toNNReal _ (half_pos ha).le
  let p : ℝ → ℝ≥0 := fun t => (max t a - a / 2).toNNReal
  have hp (t : ℝ) : 0 < p t := by
    apply Real.toNNReal_pos.mpr
    have := le_max_right t a
    linarith
  let V : ℝ → DirichletHilbertSpace (d := d) R hR := fun t =>
    Q (p t) (hp t) (spectralHeatRow s τ y)
  have hpc : Continuous p := continuous_real_toNNReal.comp
    ((continuous_id.max continuous_const).sub continuous_const)
  have hVc : Continuous V := (hQc (spectralHeatRow s τ y)).comp
    (hpc.subtype_mk hp)
  have hV (t : ℝ) (ht : a ≤ t) : J (V t) = spectralHeatRow s t y := by
    have hfactor := congrArg (fun T : _ →L[ℝ] _ => T (spectralHeatRow s τ y))
      (hQ (p t) (hp t)).1
    simp only [ContinuousLinearMap.comp_apply] at hfactor
    rw [show V t = Q (p t) (hp t) (spectralHeatRow s τ y) from rfl, hfactor,
      spectral_heat_operator_row hd hκ h hR s (p t) τ hτ y hy]
    congr 1
    have hmax : max t a = t := max_eq_left ht
    have hnonneg : 0 ≤ t - a / 2 := by linarith
    simp only [p, hmax, Real.coe_toNNReal _ hnonneg, hτval]
    ring
  refine ⟨V, hVc, hV, ?_, ?_⟩
  · intro t ht v
    have hshift : 0 < t - a / 2 := by linarith
    have hpval : (p t : ℝ) = t - a / 2 := by
      simp only [p, max_eq_left ht.le, Real.coe_toNNReal _ hshift.le]
    have hderiv := (hQ (p t) (hp t)).2.2 (spectralHeatRow s τ y) v
    rw [hpval] at hderiv
    have hcomp := hderiv.comp t ((hasDerivAt_id t).sub_const (a / 2))
    have heq : (fun r : ℝ => inner ℝ (spectralHeatRow s r y) (J v)) =ᶠ[nhds t]
        (fun r : ℝ => inner ℝ
          (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) (r - a / 2).toNNReal
            (spectralHeatRow s τ y)) (J v)) := by
      filter_upwards [eventually_gt_nhds (show a / 2 < t by linarith)] with r hr
      rw [spectral_heat_operator_row hd hκ h hR s _ τ hτ y hy]
      simp only [Real.coe_toNNReal _ (sub_nonneg.mpr hr.le), hτval]
      congr 2 <;> ring
    simpa only [mul_one, Function.comp_apply, V] using hcomp.congr_of_eventuallyEq heq
  · obtain ⟨C, hC⟩ := (isCompact_Icc.bddAbove_image hVc.norm.continuousOn)
    refine ⟨C, ?_⟩
    intro t ht
    have hn : ‖V t‖ ≤ C := hC ⟨t, ht, rfl⟩
    have hc := hilbertToSobolev_norm_le _ (V t).val
    refine ⟨spectral_heat_row_native_weakGradient hd hκ h R hR s t
      (lt_of_lt_of_le ha ht.1) y hy (V t) (hV t ht.1), hn, hc.1.trans hn, ?_⟩
    exact fun i => (hc.2 i).trans hn

#print axioms spectral_heat_row_native_weakFlow_strip

/-- One actual spectrum supplies sub-Markov bounds and weakly evolving native rows. -/
theorem exists_sourceBall_spectral_heat_native_row_weakFlow_submarkov {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ (s : DirichletSpectralResolution ρ α R)
      (u : ℕ → DirichletHilbertSpace (d := d) R hR),
      Tendsto s.eigenvalue atTop atTop ∧
      (∀ n, spectralHeatBasis s n = J (u n)) ∧
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (u n)) (J w)) ∧
      (∀ (t : ℝ≥0) (_ht : 0 < t) (y : PDE.Vec d), y ∈ sourceBall 0 R →
        ∃ v : DirichletHilbertSpace (d := d) R hR,
          J v = spectralHeatRow s t y ∧
          (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => v.val (some i) x))
              (fun i => v.val (some i) x)) ≤
            ((t : ℝ) / 2)⁻¹ * ‖spectralHeatRow s ((t : ℝ) / 2) y‖ ^ 2) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        ∀ y ∈ sourceBall 0 R, 0 ≤ ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y) ∧
      (∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ x ∈ sourceBall 0 R,
        0 ≤ (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ∧
        (∫ y, ∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
          s.eigenfunction i x * s.eigenfunction i y ∂dirichletVolume ρ R) ≤ 1) ∧
      (∀ (a b : ℝ), 0 < a → ∀ y : PDE.Vec d, y ∈ sourceBall 0 R →
        ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (C : ℝ),
          Continuous V ∧ ∀ t ∈ Set.Icc a b,
            J (V t) = spectralHeatRow s t y ∧
            (∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec (fun i => (V t).val (some i) x))
                (fun i => (V t).val (some i) x)) ≤
              (t / 2)⁻¹ * ‖spectralHeatRow s (t / 2) y‖ ^ 2 ∧
            EinsteinRelation.HasWeakGradient Set.univ
              ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
                Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
              (dirichletHilbertZeroExtensionGrad R hR (V t)) ∧
            ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
              ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C ) ∧
      ∀ (a b : ℝ), 0 < a → ∀ y : PDE.Vec d, y ∈ sourceBall 0 R →
        ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
          Continuous V ∧
          (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
          (∀ t, a < t → ∀ v, HasDerivAt
            (fun r : ℝ => inner ℝ (spectralHeatRow s r y) (J v))
            (-(∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec (fun i => (V t).val (some i) x))
                (fun i => v.val (some i) x))) t) ∧
          ∃ C : ℝ, ∀ t ∈ Set.Icc a b,
            EinsteinRelation.HasWeakGradient Set.univ
              ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
                Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
              (dirichletHilbertZeroExtensionGrad R hR (V t)) ∧
            ‖V t‖ ≤ C ∧ ‖(hilbertToSobolev _ (V t).val).1‖ ≤ C ∧
            ∀ i, ‖(hilbertToSobolev _ (V t).val).2 i‖ ≤ C := by
  dsimp only
  obtain ⟨s, u, hs, hb, hv, hrow, hnonneg, hmass, hstrip⟩ :=
    exists_sourceBall_spectral_heat_native_row_strips_submarkov hd hκ h R hR
  refine ⟨s, u, hs, hb, hv, hrow, hnonneg, hmass, hstrip, ?_⟩
  intro a b ha y hy
  exact spectral_heat_row_native_weakFlow_strip hd hκ h R hR s u hb hv a b ha y hy

#print axioms exists_sourceBall_spectral_heat_native_row_weakFlow_submarkov

/-- Integration by parts in time for the actual spectral row against one
native spatial test and a differentiable scalar time test. -/
theorem spectral_heat_row_native_time_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ (v : DirichletHilbertSpace (d := d) R hR) (c e : ℝ),
        a < c → a < e → ∀ (φ φ' : ℝ → ℝ), Continuous φ → Continuous φ' →
        (∀ t, HasDerivAt φ (φ' t) t) →
        (∫ t in c..e, inner ℝ (spectralHeatRow s t y) (J v) * φ' t) =
          inner ℝ (spectralHeatRow s e y) (J v) * φ e -
          inner ℝ (spectralHeatRow s c y) (J v) * φ c +
          ∫ t in c..e, (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => v.val (some i) x)) * φ t := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨V, hVc, hV, hderiv, _⟩ :=
    spectral_heat_row_native_weakFlow_strip hd hκ h R hR s u hb hvar a a ha y hy
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨V, hVc, hV, ?_⟩
  intro v c e hc he φ φ' hφ hφ' hφd
  have henergy : Continuous (fun t => ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (V t).val (some i) x))
        (fun i => v.val (some i) x)) := by
    have hcB : Continuous (fun t => B (V t) v) :=
      (B.flip v).continuous.comp hVc
    simpa only [hB] using hcB
  have hpos : ∀ t ∈ Set.uIcc c e, a < t := by
    intro t ht
    exact lt_of_lt_of_le (lt_min hc he) ht.1
  have hd' : ∀ t ∈ Set.uIcc c e, HasDerivAt
      (fun r => inner ℝ (spectralHeatRow s r y) (J v))
      (-(∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => v.val (some i) x))) t := fun t ht => hderiv t (hpos t ht) v
  have hfcont : ContinuousOn (fun t => inner ℝ (spectralHeatRow s t y) (J v))
      (Set.uIcc c e) := HasDerivAt.continuousOn hd'
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hfcont hφ.continuousOn (fun t ht => hd' t (Set.Ioo_subset_Icc_self ht))
    (fun t _ => hφd t) (henergy.neg.intervalIntegrable c e) (hφ'.intervalIntegrable c e)
  simpa only [neg_mul, intervalIntegral.integral_neg, sub_neg_eq_add] using hibp

#print axioms spectral_heat_row_native_time_test

/-- The actual kernel row is jointly measurable on a positive-time cylinder,
and every time slice belongs to the genuine weighted spatial L² space. -/
theorem spectral_heat_row_spacetime_measurable_and_slice_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    {R : ℝ} (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop) (a b : ℝ) (ha : 0 < a)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    AEStronglyMeasurable H (volume.restrict (Set.Ioo a b ×ˢ sourceBall 0 R)) ∧
    ∀ t ∈ Set.Ioo a b, MemLp (fun x => H (t, x)) 2 (dirichletVolume ρ R) := by
  dsimp only
  have hcont : ContinuousOn (fun z : ℝ × PDE.Vec d => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y)
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) := by
    apply (spectral_heat_continuousOn hd hκ h hR s hs).comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
    intro z hz
    exact ⟨lt_trans ha hz.1.1, hz.2, hy⟩
  have hball : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  refine ⟨hcont.aestronglyMeasurable (MeasurableSet.prod measurableSet_Ioo hball), ?_⟩
  intro t ht
  have hm := spectral_heat_row_memLp hd hκ h hR s t (lt_trans ha ht.1) y hy
  convert hm using 1
  ext x
  congr 1
  ext i
  ring

#print axioms spectral_heat_row_spacetime_measurable_and_slice_memLp

/-- The same spectral row has a uniform weighted L² bound on a compact
positive-time interval. -/
theorem spectral_heat_row_uniform_weighted_L2 {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc a b, ‖spectralHeatRow s t y‖ ≤ C := by
  obtain ⟨V, hVc, hV, _⟩ :=
    spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hvar a b ha y hy
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨C, hC⟩ := isCompact_Icc.bddAbove_image (J.continuous.comp hVc).norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t ht
  rw [← hV t ht]
  exact (hC ⟨t, ht, rfl⟩).trans (le_max_left _ _)

#print axioms spectral_heat_row_uniform_weighted_L2

/-- The squared weighted mass of the actual heat row is integrable in time. -/
theorem spectral_heat_row_weighted_mass_integrable {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    IntegrableOn (fun t => ∫ x, (∑' i,
      Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y) ^ 2
        ∂dirichletVolume ρ R) (Set.Ioo a b) := by
  obtain ⟨V, hVc, hV, _⟩ :=
    spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hvar a b ha y hy
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hi : IntegrableOn (fun t => ‖J (V t)‖ ^ 2) (Set.Ioo a b) :=
    ((J.continuous.comp hVc).norm.pow 2).continuousOn.integrableOn_Icc.mono_set
      Set.Ioo_subset_Icc_self
  apply hi.congr_fun
  · intro t ht
    change ‖dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (V t)‖ ^ 2 =
      ∫ x, (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
        s.eigenfunction i y) ^ 2 ∂dirichletVolume ρ R
    rw [hV t (Set.Ioo_subset_Icc_self ht)]
    have he := spectral_heat_row_Lp_ae_eq hd hκ h hR s t (lt_trans ha ht.1) y hy
    have he' : (fun x => (spectralHeatRow s t y) x ^ 2) =ᵐ[dirichletVolume ρ R]
        (fun x => (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) ^ 2) := by
      filter_upwards [he] with x hx
      change (spectralHeatRow s t y) x = _ at hx
      rw [hx]
      congr 1
      congr 1
      funext i
      ring
    rw [← integral_congr_ae he', ← real_inner_self_eq_norm_sq,
      MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards with x
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  · exact measurableSet_Ioo

#print axioms spectral_heat_row_weighted_mass_integrable

/-- The actual spectral heat row is square-integrable on the weighted strip. -/
theorem spectral_heat_row_weighted_spacetime_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    MemLp (fun z : ℝ × PDE.Vec d => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y) 2
      ((volume.restrict (Set.Ioo a b)).prod (dirichletVolume ρ R)) := by
  let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
    Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hbase := spectral_heat_row_spacetime_measurable_and_slice_memLp
    hd hκ h hR s hs a b ha y hy
  have hac : (volume.restrict (Set.Ioo a b)).prod (dirichletVolume ρ R) ≪
      (volume : Measure (ℝ × PDE.Vec d)).restrict
        (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl
      (withDensity_absolutelyContinuous _ _)
  have hm : AEStronglyMeasurable H
      ((volume.restrict (Set.Ioo a b)).prod (dirichletVolume ρ R)) := hbase.1.mono_ac hac
  apply (memLp_two_iff_integrable_sq hm).2
  apply (integrable_prod_iff (hm.pow 2)).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hbase.2 t ht).integrable_sq
  · have hi := spectral_heat_row_weighted_mass_integrable hd hκ h R hR s u hb hvar a b ha y hy
    simpa only [IntegrableOn, H, Pi.pow_apply, Real.norm_eq_abs, abs_pow, sq_abs] using hi

#print axioms spectral_heat_row_weighted_spacetime_memLp

/-- The actual spectral heat row is square-integrable on the ordinary strip. -/
theorem spectral_heat_row_spacetime_memLp {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    MemLp (fun z : ℝ × PDE.Vec d => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y) 2
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) := by
  letI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hlower : ENNReal.ofReal κ • volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      dirichletVolume ρ R := by
    rw [← withDensity_const]
    apply withDensity_mono
    exact ae_of_all _ fun x => ENNReal.ofReal_le_ofReal (h.2.2 x).1
  have hk : ENNReal.ofReal κ ≠ 0 := (ENNReal.ofReal_pos.mpr hκ).ne'
  have hle : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≤
      (ENNReal.ofReal κ)⁻¹ • dirichletVolume ρ R := by
    calc
      _ = (ENNReal.ofReal κ)⁻¹ • (ENNReal.ofReal κ •
          volume.restrict (sourceBall (0 : PDE.Vec d) R)) := by
        rw [smul_smul, ENNReal.inv_mul_cancel hk ENNReal.ofReal_ne_top, one_smul]
      _ ≤ _ := by gcongr
  have hp : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (ENNReal.ofReal κ)⁻¹ • ((volume.restrict (Set.Ioo a b)).prod (dirichletVolume ρ R)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, ← Measure.prod_smul_right]
    exact Measure.prod_mono le_rfl hle
  exact (spectral_heat_row_weighted_spacetime_memLp hd hκ h R hR s hs u hb hvar
    a b ha y hy).of_measure_le_smul (ENNReal.inv_ne_top.mpr hk) hp

#print axioms spectral_heat_row_spacetime_memLp

/-- The native gradient coordinates vary continuously and have square-integrable time norms. -/
theorem spectral_heat_row_native_gradient_paths {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      (∀ i : Fin d, Continuous (fun t => (hilbertToSobolev _ (V t).val).2 i)) ∧
      (∀ i : Fin d, IntegrableOn (fun t => ‖(hilbertToSobolev _ (V t).val).2 i‖ ^ 2)
        (Set.Ioo a b)) ∧
      (∀ t ∈ Set.Icc a b, EinsteinRelation.HasWeakGradient Set.univ
        ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
          Real.exp (-s.eigenvalue i * t) * s.eigenfunction i y * s.eigenfunction i x))
        (dirichletHilbertZeroExtensionGrad R hR (V t))) := by
  obtain ⟨V, hVc, hV, _⟩ :=
    spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hvar a b ha y hy
  have hg (i : Fin d) : Continuous (fun t => (hilbertToSobolev _ (V t).val).2 i) := by
    exact (continuous_apply i).comp
      ((ContinuousLinearMap.snd ℝ _ _).continuous.comp
        ((hilbertToSobolev _).continuous.comp hVc.subtype_val))
  refine ⟨V, hVc, hV, hg, ?_, ?_⟩
  · intro i
    exact ((hg i).norm.pow 2).continuousOn.integrableOn_Icc.mono_set
      Set.Ioo_subset_Icc_self
  · intro t ht
    exact spectral_heat_row_native_weakGradient hd hκ h R hR s t
      (lt_of_lt_of_le ha ht.1) y hy (V t) (hV t ht)

#print axioms spectral_heat_row_native_gradient_paths

/-- Continuous time weights integrate the actual spectral row in the native space. -/
theorem spectral_heat_row_native_time_average {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      ∀ η : ℝ → ℝ, Continuous η →
        IntegrableOn (fun t => η t • V t) (Set.Ioo a b) ∧
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
          (∫ t in Set.Ioo a b, η t • V t) =
          (∫ t in Set.Ioo a b, η t • spectralHeatRow s t y) ∧
        ∀ i : Fin d,
          (hilbertToSobolev _ (∫ t in Set.Ioo a b, η t • V t).val).2 i =
            ∫ t in Set.Ioo a b, η t • (hilbertToSobolev _ (V t).val).2 i := by
  obtain ⟨V, hVc, hV, _⟩ :=
    spectral_heat_row_continuous_native_strip hd hκ h R hR s u hb hvar a b ha y hy
  refine ⟨V, hVc, hV, ?_⟩
  intro η hη
  have hi : IntegrableOn (fun t => η t • V t) (Set.Ioo a b) :=
    (hη.smul hVc).continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  refine ⟨hi, ?_, ?_⟩
  · rw [← (dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1)).integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [map_smul, hV t (Set.Ioo_subset_Icc_self ht)]
  · intro i
    let P := (ContinuousLinearMap.proj i).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        ((hilbertToSobolev _).comp (dirichletHilbertSubmodule (d := d) R hR).subtypeL))
    have hP := P.integral_comp_comm hi
    simpa [P] using hP.symm

#print axioms spectral_heat_row_native_time_average

/-- Evaluating the finitely many spatial L² representatives of a simple time path
is jointly measurable. -/
theorem simpleFunc_lp_joint_measurable {β : Type*} [MeasurableSpace β]
    (μ : Measure β) (f : SimpleFunc ℝ (Lp ℝ 2 μ)) :
    Measurable (fun z : ℝ × β => (f z.1) z.2) := by
  letI : MeasurableSpace (Lp ℝ 2 μ) := borel _
  letI : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
  letI : Countable (Set.range f) := f.finite_range.countable.to_subtype
  have heval : Measurable (fun z : (Set.range f) × β => z.1.val z.2) := by
    apply measurable_from_prod_countable_right
    intro v
    exact (Lp.stronglyMeasurable v.val).measurable
  have hf : Measurable (fun t : ℝ => (⟨f t, ⟨t, rfl⟩⟩ : Set.range f)) :=
    f.measurable.subtype_mk
  exact heval.comp (hf.comp measurable_fst |>.prodMk measurable_snd)

#print axioms simpleFunc_lp_joint_measurable

/-- Jointly measurable finite-valued time approximations of the native gradient. -/
theorem spectral_heat_row_gradient_simple_approximants {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (F : Fin d → ℕ → SimpleFunc ℝ
        (SubdiffusiveProcess.DomainL2 (SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)))),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      (∀ i n, Measurable (fun z : ℝ × PDE.Vec d => (F i n z.1) z.2)) ∧
      (∀ i t, Tendsto (fun n => F i n t) atTop
        (nhds ((hilbertToSobolev _ (V t).val).2 i))) := by
  obtain ⟨V, hVc, hV, hg, _, _⟩ :=
    spectral_heat_row_native_gradient_paths hd hκ h R hR s u hb hvar a b ha y hy
  let F := fun i : Fin d => (hg i).stronglyMeasurable.approx
  refine ⟨V, F, hVc, hV, ?_, ?_⟩
  · intro i n
    exact simpleFunc_lp_joint_measurable _ (F i n)
  · intro i t
    exact (hg i).stronglyMeasurable.tendsto_approx t

#print axioms spectral_heat_row_gradient_simple_approximants

/-- The native gradient approximants also converge in the time L² norm. -/
theorem spectral_heat_row_gradient_simple_approximants_L2 {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (F : Fin d → ℕ → SimpleFunc ℝ
        (SubdiffusiveProcess.DomainL2 (SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)))),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      (∀ i n, Measurable (fun z : ℝ × PDE.Vec d => (F i n z.1) z.2)) ∧
      (∀ i t, Tendsto (fun n => F i n t) atTop
        (nhds ((hilbertToSobolev _ (V t).val).2 i))) ∧
      (∀ i, Tendsto (fun n => eLpNorm
        (fun t => F i n t - (hilbertToSobolev _ (V t).val).2 i) 2
        (volume.restrict (Set.Ioo a b))) atTop (nhds 0)) := by
  obtain ⟨V, hVc, hV, hg, hi, _⟩ :=
    spectral_heat_row_native_gradient_paths hd hκ h R hR s u hb hvar a b ha y hy
  let g := fun i : Fin d => fun t => (hilbertToSobolev _ (V t).val).2 i
  letI : MeasurableSpace (SubdiffusiveProcess.DomainL2
      (SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR))) := borel _
  letI : BorelSpace (SubdiffusiveProcess.DomainL2
      (SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR))) := ⟨rfl⟩
  letI (i : Fin d) : TopologicalSpace.SeparableSpace (Set.range (g i) ∪ {0} : Set _) :=
    (hg i).stronglyMeasurable.separableSpace_range_union_singleton
  let F := fun i : Fin d => SimpleFunc.approxOn (g i) (hg i).measurable
    (Set.range (g i) ∪ {0}) 0 (by simp)
  refine ⟨V, F, hVc, hV, ?_, ?_, ?_⟩
  · intro i n
    exact simpleFunc_lp_joint_measurable _ (F i n)
  · intro i t
    exact SimpleFunc.tendsto_approxOn (hg i).measurable (by simp) (subset_closure (show g i t ∈ Set.range (g i) ∪ {0} from Or.inl ⟨t, rfl⟩))
  · intro i
    have hm : MemLp (g i) 2 (volume.restrict (Set.Ioo a b)) :=
      (memLp_two_iff_integrable_sq_norm (hg i).aestronglyMeasurable).2 (hi i)
    simpa only [F, g, Pi.sub_def] using
      (SimpleFunc.tendsto_approxOn_range_Lp_eLpNorm (p := 2) (μ := volume.restrict (Set.Ioo a b))
        (by simp) (hg i).measurable hm)

#print axioms spectral_heat_row_gradient_simple_approximants_L2


/-- A simple time path has the same mixed and product-space L² seminorm. -/
theorem simpleFunc_lp_eLpNorm_prod {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [SFinite ν] (F : SimpleFunc ℝ (Lp ℝ 2 ν)) :
    eLpNorm (fun z : ℝ × β => (F z.1) z.2) 2 (μ.prod ν) =
      eLpNorm (fun t => F t) 2 μ := by
  letI : MeasurableSpace (Lp ℝ 2 ν) := borel _
  letI : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩
  have hp : AEStronglyMeasurable (fun z : ℝ × β => (F z.1) z.2) (μ.prod ν) :=
    (simpleFunc_lp_joint_measurable ν F).aestronglyMeasurable
  have ht : AEStronglyMeasurable (fun t => F t) μ := F.stronglyMeasurable.aestronglyMeasurable
  apply ENNReal.rpow_left_injective (show (2 : ℝ) ≠ 0 by norm_num)
  change eLpNorm (fun z : ℝ × β => (F z.1) z.2) 2 (μ.prod ν) ^ (2 : ℝ) =
    eLpNorm (fun t => F t) 2 μ ^ (2 : ℝ)
  have hprod : eLpNorm (fun z : ℝ × β => (F z.1) z.2) 2 (μ.prod ν) ^ (2 : ℝ) =
      ∫⁻ z, ‖(F z.1) z.2‖ₑ ^ (2 : ℝ) ∂(μ.prod ν) := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) hp)
  have htime : eLpNorm (fun t => F t) 2 μ ^ (2 : ℝ) =
      ∫⁻ t, ‖F t‖ₑ ^ (2 : ℝ) ∂μ := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num) ht)
  rw [hprod, htime, lintegral_prod _ (hp.enorm.pow_const _)]
  apply lintegral_congr
  intro t
  have hs : eLpNorm (fun x => (F t) x) 2 ν ^ (2 : ℝ) =
      ∫⁻ x, ‖(F t) x‖ₑ ^ (2 : ℝ) ∂ν := by
    simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := 2) (by norm_num)
      (Lp.stronglyMeasurable (F t)).aestronglyMeasurable)
  rw [← hs, Lp.enorm_def]

#print axioms simpleFunc_lp_eLpNorm_prod


/-- Differences of simple paths have the same mixed and product L² seminorm. -/
theorem simpleFunc_lp_eLpNorm_sub_prod {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [SFinite ν] (F G : SimpleFunc ℝ (Lp ℝ 2 ν)) :
    eLpNorm (fun z : ℝ × β => (F z.1) z.2 - (G z.1) z.2) 2 (μ.prod ν) =
      eLpNorm (fun t => F t - G t) 2 μ := by
  letI : MeasurableSpace (Lp ℝ 2 ν) := borel _
  letI : BorelSpace (Lp ℝ 2 ν) := ⟨rfl⟩
  have heq : (fun z : ℝ × β => ((F - G) z.1) z.2) =ᵐ[μ.prod ν]
      (fun z : ℝ × β => (F z.1) z.2 - (G z.1) z.2) := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (simpleFunc_lp_joint_measurable ν (F - G))
      ((simpleFunc_lp_joint_measurable ν F).sub (simpleFunc_lp_joint_measurable ν G)))).2
    filter_upwards [] with t
    filter_upwards [Lp.coeFn_sub (F t) (G t)] with x hx
    simpa only [SimpleFunc.coe_sub, Pi.sub_apply] using hx
  calc
    _ = eLpNorm (fun z : ℝ × β => ((F - G) z.1) z.2) 2 (μ.prod ν) :=
      (eLpNorm_congr_ae heq).symm
    _ = eLpNorm (fun t => (F - G) t) 2 μ := simpleFunc_lp_eLpNorm_prod μ ν (F - G)
    _ = _ := by simp only [SimpleFunc.coe_sub, Pi.sub_apply]

#print axioms simpleFunc_lp_eLpNorm_sub_prod

/-- Mixed L² convergence of simple paths yields a product-space L² limit. -/
theorem simpleFunc_lp_product_limit {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [SFinite ν]
    (F : ℕ → SimpleFunc ℝ (Lp ℝ 2 ν)) (g : ℝ → Lp ℝ 2 ν)
    (hf : ∀ n, MemLp (fun t => F n t) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => F n t - g t) 2 μ)
      atTop (nhds 0)) :
    ∃ H : Lp ℝ 2 (μ.prod ν), Tendsto
      (fun n => eLpNorm (fun z : ℝ × β => (F n z.1) z.2 - H z) 2 (μ.prod ν))
      atTop (nhds 0) := by
  let fp : ℕ → (ℝ × β → ℝ) := fun n z => (F n z.1) z.2
  have hfp : ∀ n, MemLp (fp n) 2 (μ.prod ν) := by
    intro n
    change eLpNorm (fun z : ℝ × β => (F n z.1) z.2) 2 (μ.prod ν) < ∞
    rw [simpleFunc_lp_eLpNorm_prod μ ν (F n)]
    exact hf n
  let A : ℕ → Lp ℝ 2 (μ.prod ν) := fun n => (hfp n).toLp (fp n)
  let B : ℕ → Lp (Lp ℝ 2 ν) 2 μ := fun n => (hf n).toLp (fun t => F n t)
  have hB : Tendsto B atTop (nhds (hg.toLp g)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n t => F n t) hf g hg).2
    change Tendsto (fun n => eLpNorm (fun t => F n t - g t) 2 μ) atTop (nhds 0)
    exact hconv
  have hdist : ∀ n m, dist (A n) (A m) = dist (B n) (B m) := by
    intro n m
    rw [Lp.dist_def, Lp.dist_def]
    have hp : eLpNorm (⇑(A n) - ⇑(A m)) 2 (μ.prod ν) =
        eLpNorm (fun z : ℝ × β => (F n z.1) z.2 - (F m z.1) z.2) 2 (μ.prod ν) := by
      apply eLpNorm_congr_ae
      filter_upwards [(hfp n).coeFn_toLp, (hfp m).coeFn_toLp] with z hn hm
      simp only [Pi.sub_apply, A, hn, hm, fp]
    have ht : eLpNorm (⇑(B n) - ⇑(B m)) 2 μ =
        eLpNorm (fun t => F n t - F m t) 2 μ := by
      apply eLpNorm_congr_ae
      filter_upwards [(hf n).coeFn_toLp, (hf m).coeFn_toLp] with t hn hm
      simp only [Pi.sub_apply, B, hn, hm]
    rw [hp, ht, simpleFunc_lp_eLpNorm_sub_prod]
  have hc : CauchySeq A := by
    apply Metric.cauchySeq_iff.2
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hB.cauchySeq ε hε
    exact ⟨N, fun n hn m hm => by rw [hdist]; exact hN n hn m hm⟩
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨H, ?_⟩
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' A H).1 hH
  apply ht.congr'
  filter_upwards [] with n
  apply eLpNorm_congr_ae
  filter_upwards [(hfp n).coeFn_toLp] with z hz
  simp only [Pi.sub_apply, A, hz, fp]

#print axioms simpleFunc_lp_product_limit

/-- The product L² limit represents the pointwise L² limit on almost every time slice. -/
theorem simpleFunc_lp_product_limit_slices {β : Type*} [MeasurableSpace β]
    (μ : Measure ℝ) (ν : Measure β) [SFinite ν]
    (F : ℕ → SimpleFunc ℝ (Lp ℝ 2 ν)) (g : ℝ → Lp ℝ 2 ν)
    (hf : ∀ n, MemLp (fun t => F n t) 2 μ) (hg : MemLp g 2 μ)
    (hconv : Tendsto (fun n => eLpNorm (fun t => F n t - g t) 2 μ)
      atTop (nhds 0)) (hpoint : ∀ t, Tendsto (fun n => F n t) atTop (nhds (g t))) :
    ∃ H : Lp ℝ 2 (μ.prod ν),
      (∀ᵐ t ∂μ, (fun x => H (t, x)) =ᵐ[ν] (g t)) ∧
      Tendsto (fun n => eLpNorm (fun z : ℝ × β => (F n z.1) z.2 - H z)
        2 (μ.prod ν)) atTop (nhds 0) := by
  obtain ⟨H, hH⟩ := simpleFunc_lp_product_limit μ ν F g hf hg hconv
  refine ⟨H, ?_, hH⟩
  have hm : TendstoInMeasure (μ.prod ν)
      (fun n (z : ℝ × β) => (F n z.1) z.2) atTop H := by
    apply tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num)
    change Tendsto (fun n => eLpNorm (fun z : ℝ × β => (F n z.1) z.2 - H z)
      2 (μ.prod ν)) atTop (nhds 0)
    exact hH
  obtain ⟨φ, hφ, hφae⟩ := hm.exists_seq_tendsto_ae
  have hslices := Measure.ae_ae_of_ae_prod hφae
  filter_upwards [hslices] with t ht
  have hsp : Tendsto (fun n => F (φ n) t) atTop (nhds (g t)) :=
    (hpoint t).comp hφ.tendsto_atTop
  have hsm : TendstoInMeasure ν (fun n => F (φ n) t) atTop (g t) :=
    tendstoInMeasure_of_tendsto_Lp hsp
  obtain ⟨ψ, hψ, hψae⟩ := hsm.exists_seq_tendsto_ae
  filter_upwards [ht, hψae] with x hx hy
  exact tendsto_nhds_unique (hx.comp hψ.tendsto_atTop) hy

#print axioms simpleFunc_lp_product_limit_slices

/-- Native spectral gradient coordinates admit product L² representatives on a strip. -/
theorem spectral_heat_row_gradient_product_representatives {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (G : Fin d → Lp ℝ 2 ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))))),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      (∀ i, ∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
        (fun x => G i (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          ((hilbertToSobolev _ (V t).val).2 i)) := by
  obtain ⟨V, F, hVc, hV, _, hpoint, hconv⟩ :=
    spectral_heat_row_gradient_simple_approximants_L2 hd hκ h R hR s u hb hvar a b ha y hy
  have hg (i : Fin d) : Continuous (fun t => (hilbertToSobolev _ (V t).val).2 i) := by
    exact (continuous_apply i).comp
      ((ContinuousLinearMap.snd ℝ _ _).continuous.comp
        ((hilbertToSobolev _).continuous.comp hVc.subtype_val))
  have hmem (i : Fin d) : MemLp (fun t => (hilbertToSobolev _ (V t).val).2 i) 2
      (volume.restrict (Set.Ioo a b)) := by
    apply (memLp_two_iff_integrable_sq_norm (hg i).aestronglyMeasurable).2
    exact ((hg i).norm.pow 2).continuousOn.integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  have hf (i : Fin d) (n : ℕ) : MemLp (fun t => F i n t) 2
      (volume.restrict (Set.Ioo a b)) :=
    (F i n).memLp_of_isFiniteMeasure 2 _
  choose G hG using fun i => simpleFunc_lp_product_limit_slices
    (volume.restrict (Set.Ioo a b))
    (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
      (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))
    (F i) (fun t => (hilbertToSobolev _ (V t).val).2 i) (hf i) (hmem i)
    (hconv i) (hpoint i)
  exact ⟨V, G, hVc, hV, fun i => (hG i).1⟩

#print axioms spectral_heat_row_gradient_product_representatives

/-- Coordinate L² representatives form a measurable vector with L² Euclidean norm. -/
theorem lp_coordinates_euclidean_memLp {β : Type*} [MeasurableSpace β] {d : ℕ}
    (μ : Measure β) (G : Fin d → Lp ℝ 2 μ) :
    AEStronglyMeasurable (fun z i => G i z) μ ∧
      MemLp (fun z => euclideanNorm (fun i => G i z)) 2 μ := by
  have hv : MemLp (fun z i => G i z) 2 μ :=
    memLp_pi_iff.mpr (fun i => Lp.memLp (G i))
  have he : MemLp (fun z => (WithLp.toLp 2 (fun i => G i z) :
      EuclideanSpace ℝ (Fin d))) 2 μ :=
    memLp_piLp_iff.mpr (fun i => Lp.memLp (G i))
  exact ⟨hv.aestronglyMeasurable, by
    simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using he.norm⟩

#print axioms lp_coordinates_euclidean_memLp

/-- The native spectral gradient has a product-measurable vector representative. -/
theorem spectral_heat_row_gradient_vector_representative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      (∀ᵐ t ∂(volume.restrict (Set.Ioo a b)),
        (fun x => G (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          (fun x i => (hilbertToSobolev _ (V t).val).2 i x)) := by
  obtain ⟨V, G, hVc, hV, hG⟩ :=
    spectral_heat_row_gradient_product_representatives hd hκ h R hR s u hb hvar a b ha y hy
  have hGv := lp_coordinates_euclidean_memLp _ G
  refine ⟨V, (fun z i => G i z), hVc, hV, hGv.1, hGv.2, ?_⟩
  filter_upwards [ae_all_iff.mpr hG] with t ht
  filter_upwards [ae_all_iff.mpr ht] with x hx
  funext i
  exact hx i

#print axioms spectral_heat_row_gradient_vector_representative

/-- Restriction to a measurable spatial subset and zero extension preserve
product measurability and the Euclidean L² bound. -/
theorem product_spatial_zeroExtension_memLp {d : ℕ} (μ : Measure ℝ)
    [SFinite μ] (B Q : Set (PDE.Vec d)) (hB : MeasurableSet B) (hBQ : B ⊆ Q)
    (G : ℝ × PDE.Vec d → PDE.Vec d)
    (hG : AEStronglyMeasurable G (μ.prod (volume.restrict Q)))
    (hL : MemLp (fun z => euclideanNorm (G z)) 2 (μ.prod (volume.restrict Q))) :
    AEStronglyMeasurable ((Set.univ ×ˢ B).indicator G) (μ.prod volume) ∧
    MemLp (fun z => euclideanNorm (((Set.univ ×ˢ B).indicator G) z)) 2
      (μ.prod volume) := by
  have hm : μ.prod (volume.restrict B) ≤ μ.prod (volume.restrict Q) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono_set volume hBQ)
  have hr : (μ.prod volume).restrict (Set.univ ×ˢ B) = μ.prod (volume.restrict B) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hs : MeasurableSet ((Set.univ : Set ℝ) ×ˢ B) := MeasurableSet.univ.prod hB
  refine ⟨(aestronglyMeasurable_indicator_iff hs).2 ?_, ?_⟩
  · rw [hr]
    exact hG.mono_measure hm
  · have hh : MemLp ((Set.univ ×ˢ B).indicator (fun z => euclideanNorm (G z))) 2
        (μ.prod volume) := by
      apply (memLp_indicator_iff_restrict hs).2
      rw [hr]
      exact hL.mono_measure hm
    convert hh using 1
    funext z
    by_cases hz : z ∈ Set.univ ×ˢ B
    · simp only [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz, euclideanNorm, euclideanSq, dot]

#print axioms product_spatial_zeroExtension_memLp

/-- Equal spatial slices remain equal after zero extension from a smaller set. -/
theorem product_spatial_zeroExtension_slices {d : ℕ} (μ : Measure ℝ)
    (B Q : Set (PDE.Vec d)) (hB : MeasurableSet B) (hBQ : B ⊆ Q)
    (G H : ℝ × PDE.Vec d → PDE.Vec d)
    (h : ∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[volume.restrict Q]
      (fun x => H (t, x))) :
    ∀ᵐ t ∂μ, (fun x => ((Set.univ ×ˢ B).indicator G) (t, x)) =ᵐ[volume]
      (fun x => B.indicator (fun x => H (t, x)) x) := by
  filter_upwards [h] with t ht
  have hb := ae_restrict_of_ae_restrict_of_subset hBQ ht
  have hb' := (ae_restrict_iff' hB).mp hb
  filter_upwards [hb'] with x hx
  by_cases hxB : x ∈ B
  · have hp : (t, x) ∈ (Set.univ : Set ℝ) ×ˢ B := ⟨Set.mem_univ _, hxB⟩
    rw [Set.indicator_of_mem hp, Set.indicator_of_mem hxB]
    exact hx hxB
  · have hp : (t, x) ∉ (Set.univ : Set ℝ) ×ˢ B := fun hh => hxB hh.2
    rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hxB]

#print axioms product_spatial_zeroExtension_slices

/-- The zero-extended product representative is a global weak gradient for
almost every time slice of the native Dirichlet path. -/
theorem product_spatial_zeroExtension_weakGradient {d : ℕ} (μ : Measure ℝ)
    (R : ℝ) (hR : 0 < R) (V : ℝ → DirichletHilbertSpace (d := d) R hR)
    (G : ℝ × PDE.Vec d → PDE.Vec d)
    (h : ∀ᵐ t ∂μ, (fun x => G (t, x)) =ᵐ[volume.restrict
      ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
      (fun x i => (V t).val (some i) x)) :
    ∀ᵐ t ∂μ, EinsteinRelation.HasWeakGradient Set.univ
      (dirichletHilbertZeroExtension R hR (V t))
      (fun x => ((Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R).indicator G) (t, x)) := by
  have hB : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have he := product_spatial_zeroExtension_slices μ _ _ hB
    (sourceBall_subset_cube R hR) G (fun z i => (V z.1).val (some i) z.2) h
  filter_upwards [he] with t ht
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ
    (dirichletHilbert_global_zeroExtension R hR (V t)).2.2 (ae_eq_refl _)
  simpa only [Measure.restrict_univ, dirichletHilbertZeroExtensionGrad] using ht.symm

#print axioms product_spatial_zeroExtension_weakGradient

/-- The actual spectral row has one product-measurable, ball-supported
L² gradient whose slices are global weak gradients of the native zero extension. -/
theorem spectral_heat_row_global_gradient_representative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      (∀ z, z.2 ∉ sourceBall (0 : PDE.Vec d) R → G z = 0) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ (dirichletHilbertZeroExtension R hR (V t))
          (fun x => G (t, x))) := by
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs⟩ :=
    spectral_heat_row_gradient_vector_representative hd hκ h R hR s u hb hvar a b ha y hy
  have hB : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hmask := product_spatial_zeroExtension_memLp (volume.restrict (Set.Ioo a b))
    _ _ hB (sourceBall_subset_cube R hR) G hGm hGL
  have hs : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V t).val (some i) x) := by
    filter_upwards [hGs] with t ht
    filter_upwards [ht] with x hx
    funext i
    exact congrFun hx i
  refine ⟨V, (Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R).indicator G,
    hVc, hV, hmask.1, hmask.2, ?_,
    product_spatial_zeroExtension_weakGradient _ R hR V G hs⟩
  intro z hz
  apply Set.indicator_of_notMem
  exact fun hh => hz hh.2

#print axioms spectral_heat_row_global_gradient_representative

/-- The time-test identity holds for any native path representing the same
spectral row on the strip, in particular for the path chosen with the gradient. -/
theorem spectral_heat_row_time_test_of_native_path {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (V : ℝ → DirichletHilbertSpace (d := d) R hR)
    (hV : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y)
    (v : DirichletHilbertSpace (d := d) R hR) (c e : ℝ)
    (hc : c ∈ Set.Icc a b) (he : e ∈ Set.Icc a b)
    (φ φ' : ℝ → ℝ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφd : ∀ t, HasDerivAt φ (φ' t) t) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    (∫ t in c..e, inner ℝ (spectralHeatRow s t y) (J v) * φ' t) =
      inner ℝ (spectralHeatRow s e y) (J v) * φ e -
      inner ℝ (spectralHeatRow s c y) (J v) * φ c +
      ∫ t in c..e, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => v.val (some i) x)) * φ t := by
  dsimp only
  obtain ⟨W, _, hW, htest⟩ :=
    spectral_heat_row_native_time_test hd hκ h R hR s u hb hvar (a / 2)
      (by linarith) y hy
  have hVW : ∀ t ∈ Set.Icc a b, W t = V t := by
    intro t ht
    apply injective_dirichletHilbertInclusion hκ h R hR
    rw [hW t (by linarith [ht.1]), hV t ht]
  have heq : (∫ t in c..e, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (W t).val (some i) x))
          (fun i => v.val (some i) x)) * φ t) =
      ∫ t in c..e, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => v.val (some i) x)) * φ t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Set.Icc a b := Set.uIcc_subset_Icc hc he ht
    dsimp only
    rw [hVW t ht']
  rw [← heq]
  exact htest v c e (by linarith [hc.1]) (by linarith [he.1]) φ φ' hφ hφ' hφd

#print axioms spectral_heat_row_time_test_of_native_path

/-- The jointly measurable gradient represents the actual spectral series,
including its global zero extension, on almost every time slice. -/
theorem spectral_heat_row_actual_gradient_representative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      MemLp H 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      (∀ z, z.2 ∉ sourceBall (0 : PDE.Vec d) R → G z = 0) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => H (t, x)))
          (fun x => G (t, x)) ∧
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs, hGw⟩ :=
    spectral_heat_row_global_gradient_representative hd hκ h R hR s u hb hvar a b ha y hy
  refine ⟨V, G, hVc, hV,
    spectral_heat_row_spacetime_memLp hd hκ h R hR s hs u hb hvar a b ha y hy,
    hGm, hGL, hGs, ?_⟩
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  filter_upwards [hGw, ae_restrict_mem measurableSet_Ioo] with t ht htab
  have he : (fun x => (V t).val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
      (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) := by
    apply hac.ae_le
    filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t),
      spectral_heat_row_Lp_ae_eq hd hκ h hR s t (lt_trans ha htab.1) y hy] with x hx hy'
    change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ (V t)) x = (V t).val none x at hx
    change (spectralHeatRow s t y) x = _ at hy'
    rw [hV t ⟨htab.1.le, htab.2.le⟩] at hx
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hx.symm.trans hy'
  have hz := (ae_eq_restrict_iff_indicator_ae_eq hball.measurableSet).mp he
  have hw : EinsteinRelation.HasWeakGradient Set.univ
      ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
        Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
      (fun x => G (t, x)) := by
    apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ ht
    · simpa only [Measure.restrict_univ, dirichletHilbertZeroExtension] using hz
    · exact ae_eq_refl _
  refine ⟨hw, ?_⟩
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hball
    (EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ _) hw)
  · filter_upwards [ae_restrict_mem hball.measurableSet] with x hx
    exact Set.indicator_of_mem hx _
  · exact ae_eq_refl _

#print axioms spectral_heat_row_actual_gradient_representative

/-- The actual spectral row and its gradient meet the local square-integrability
and spatial-gradient requirements on the exact open cylinder. -/
theorem spectral_heat_row_cylinder_gradient {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      MemLp H 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      MemLp (fun z => euclideanNorm (G z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => H (t, x)))
          (fun x => G (t, x)) ∧
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hH, hGm, hGL, _, hGw⟩ :=
    spectral_heat_row_actual_gradient_representative hd hκ h R hR s hs u hb hvar a b ha y hy
  have hle : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (volume.restrict (Set.Ioo a b)).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  exact ⟨V, G, hVc, hV, hH, hGm.mono_measure hle, hGL.mono_measure hle, hGw⟩

#print axioms spectral_heat_row_cylinder_gradient

/-- Compactly supported scalar time tests eliminate the endpoint terms of the
native spectral weak-flow identity. -/
theorem spectral_heat_row_compact_time_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (V : ℝ → DirichletHilbertSpace (d := d) R hR)
    (hV : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y)
    (v : DirichletHilbertSpace (d := d) R hR)
    (φ φ' : ℝ → ℝ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφd : ∀ t, HasDerivAt φ (φ' t) t) (hφs : tsupport φ ⊆ Set.Ioo a b) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    (∫ t in Set.Ioo a b, inner ℝ (spectralHeatRow s t y) (J v) * φ' t) =
      ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => v.val (some i) x)) * φ t := by
  dsimp only
  have hφa : φ a = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hφs ht).1.false)
  have hφb : φ b = 0 := image_eq_zero_of_notMem_tsupport (fun ht => (hφs ht).2.false)
  have ht := spectral_heat_row_time_test_of_native_path hd hκ h R hR s u hb hvar
    a b ha y hy V hV v a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ φ φ' hφ hφ' hφd
  dsimp only at ht
  simp only [intervalIntegral.integral_of_le hab.le,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at ht
  simpa only [hφa, hφb, mul_zero, sub_self, zero_add] using ht

#print axioms spectral_heat_row_compact_time_test

/-- A separated compact time test and an actual smooth spatial test give the
literal weighted pairing with the spectral series and its native gradient. -/
theorem spectral_heat_row_separated_smooth_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (V : ℝ → DirichletHilbertSpace (d := d) R hR)
    (hV : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y)
    (ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (φ φ' : ℝ → ℝ) (hφ : Continuous φ) (hφ' : Continuous φ')
    (hφd : ∀ t, HasDerivAt φ (φ' t) t) (hφs : tsupport φ ⊆ Set.Ioo a b) :
    (∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
      ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) *
        s.eigenfunction i x * s.eigenfunction i y) * ψ x) * φ' t) =
      ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => fderiv ℝ (ψ : PDE.Vec d → ℝ) x (unitVector i))) * φ t := by
  have ht := spectral_heat_row_compact_time_test hd hκ h R hR s u hb hvar a b ha hab y hy V hV
    (dirichletSmoothElement R hR ψ) φ φ' hφ hφ' hφd hφs
  dsimp only at ht
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hl : (∫ t in Set.Ioo a b,
      inner ℝ (spectralHeatRow s t y) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (dirichletSmoothElement R hR ψ)) * φ' t) =
      ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) * ψ x) * φ' t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    rw [dirichletHilbertInclusion_inner_smooth hκ h R hR]
    congr 1
    apply integral_congr_ae
    filter_upwards [hac.ae_le (spectral_heat_row_Lp_ae_eq hd hκ h hR s t
      (lt_trans ha ht.1) y hy)] with x hx
    change (spectralHeatRow s t y) x = _ at hx
    rw [hx]
    congr 2
    apply tsum_congr
    intro i
    ring
  have hr : (∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (V t).val (some i) x))
        (fun i => (dirichletSmoothElement R hR ψ).val (some i) x)) * φ t) =
      ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => fderiv ℝ (ψ : PDE.Vec d → ℝ) x (unitVector i))) * φ t := by
    apply integral_congr_ae
    exact ae_of_all _ fun t => by
      dsimp only
      rw [dirichletHilbert_energyIntegral_smooth]
  exact hl.symm.trans (ht.trans hr)

#print axioms spectral_heat_row_separated_smooth_test

/-- A single product-measurable gradient represents the spectral row in all
separated smooth tests. -/
theorem spectral_heat_row_separated_test_gradient {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      MemLp (fun z => euclideanNorm (G z)) 2 ((volume.restrict (Set.Ioo a b)).prod volume) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (fun x => G (t, x)) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
          (fun x i => (V t).val (some i) x)) ∧
      (∀ (ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
        (φ φ' : ℝ → ℝ), Continuous φ → Continuous φ' →
        (∀ t, HasDerivAt φ (φ' t) t) → tsupport φ ⊆ Set.Ioo a b →
        (∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) * ψ x) * φ' t) =
        ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ (ψ : PDE.Vec d → ℝ) x (unitVector i))) * φ t) := by
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs⟩ :=
    spectral_heat_row_gradient_vector_representative hd hκ h R hR s u hb hvar a b ha y hy
  have hB : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact (PDE.isOpen_euclideanBall _ _).measurableSet
  have hBQ := sourceBall_subset_cube (d := d) R hR
  have hm := product_spatial_zeroExtension_memLp (volume.restrict (Set.Ioo a b))
    (sourceBall (0 : PDE.Vec d) R) _ hB hBQ G hGm hGL
  let G' := (Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R).indicator G
  have hs : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => G' (t, x)) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x i => (V t).val (some i) x) := by
    filter_upwards [hGs] with t ht
    have ht' := ae_restrict_of_ae_restrict_of_subset hBQ ht
    filter_upwards [ht', ae_restrict_mem hB] with x hx hxb
    have hp : (t, x) ∈ (Set.univ : Set ℝ) ×ˢ sourceBall (0 : PDE.Vec d) R :=
      ⟨Set.mem_univ _, hxb⟩
    change ((Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R).indicator G) (t, x) = _
    rw [Set.indicator_of_mem hp]
    funext i
    exact congrFun hx i
  refine ⟨V, G', hVc, hV, hm.1, hm.2, hs, ?_⟩
  intro ψ φ φ' hφ hφ' hφd hφs
  have ht := spectral_heat_row_separated_smooth_test hd hκ h R hR s u hb hvar
    a b ha hab y hy V hV ψ φ φ' hφ hφ' hφd hφs
  refine ht.trans ?_
  apply integral_congr_ae
  filter_upwards [hs] with t ht
  congr 1
  apply integral_congr_ae
  filter_upwards [ht] with x hx
  rw [hx]

#print axioms spectral_heat_row_separated_test_gradient

/-- The gradient used in separated tests is also a weak gradient of the
literal spectral row on the cylinder. -/
theorem spectral_heat_row_separated_test_cylinder {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      MemLp H 2 (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      AEStronglyMeasurable G (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      MemLp (fun z => euclideanNorm (G z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) ∧
      (∀ (ψ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
        (φ φ' : ℝ → ℝ), Continuous φ → Continuous φ' →
        (∀ t, HasDerivAt φ (φ' t) t) → tsupport φ ⊆ Set.Ioo a b →
        (∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * H (t, x) * ψ x) * φ' t) =
        ∫ t in Set.Ioo a b, (∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ (ψ : PDE.Vec d → ℝ) x (unitVector i))) * φ t) := by
  dsimp only
  obtain ⟨V, G, _, hV, hGm, hGL, hGs, htest⟩ :=
    spectral_heat_row_separated_test_gradient hd hκ h R hR s u hb hvar a b ha hab y hy
  have hle : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (volume.restrict (Set.Ioo a b)).prod volume := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono le_rfl Measure.restrict_le_self
  refine ⟨G, spectral_heat_row_spacetime_memLp hd hκ h R hR s hs u hb hvar a b ha y hy,
    hGm.mono_measure hle, hGL.mono_measure hle, ?_, htest⟩
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  filter_upwards [hGs, ae_restrict_mem measurableSet_Ioo] with t ht htab
  have hw := spectral_heat_row_native_weakGradient hd hκ h R hR s t
    (lt_trans ha htab.1) y hy (V t) (hV t ⟨htab.1.le, htab.2.le⟩)
  apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hball
    (EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ _) hw)
  · filter_upwards [ae_restrict_mem hball.measurableSet] with x hx
    simp only [Set.indicator_of_mem hx]
    apply tsum_congr
    intro i
    ring
  · filter_upwards [ht, ae_restrict_mem hball.measurableSet] with x hx hxb
    simp only [dirichletHilbertZeroExtensionGrad, Set.indicator_of_mem hxb]
    exact hx.symm

/-- Product rule for a weakly differentiable functional and a differentiable test. -/
theorem hasDerivAt_weak_functional_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ → E →L[ℝ] ℝ) (v : ℝ → E) (v' : E) (x : ℝ)
    (hA : ContinuousAt A x) (hv : HasDerivAt v v' x)
    (D : E →L[ℝ] ℝ)
    (hweak : ∀ w, HasDerivAt (fun t => A t w) (D w) x) :
    HasDerivAt (fun t => A t (v t)) (D (v x) + A x v') x := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  have h1 := (hweak (v x)).tendsto_slope
  have h2 : Filter.Tendsto (fun t => A t (slope v x t)) (nhdsWithin x {x}ᶜ) (nhds (A x v')) :=
    by
      simpa only [Function.comp_def] using
        (((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.tendsto
          (A x, v')).comp
          ((hA.tendsto.mono_left nhdsWithin_le_nhds).prodMk_nhds hv.tendsto_slope))
  have heq : ∀ t, slope (fun r => A r (v r)) x t =
      slope (fun r => A r (v x)) x t + A t (slope v x t) := by
    intro t
    simp only [slope_def_module, map_smul, map_sub, smul_eq_mul]
    ring
  rw [funext heq]
  exact h1.add h2

/-- The native spectral row obeys the product rule for a differentiable
Dirichlet-space test path. -/
theorem spectral_heat_row_native_path_derivative {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ t, a < t → ∀ (v : ℝ → DirichletHilbertSpace (d := d) R hR) v',
        HasDerivAt v v' t → HasDerivAt
          (fun r => inner ℝ (spectralHeatRow s r y) (J (v r)))
          (-(∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (v t).val (some i) x)) +
            inner ℝ (spectralHeatRow s t y) (J v')) t := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨V, hVc, hV, hderiv, _⟩ :=
    spectral_heat_row_native_weakFlow_strip hd hκ h R hR s u hb hvar a a ha y hy
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  let A := fun t => (innerSL ℝ (J (V t))).comp J
  have hAc : Continuous A := by
    apply Continuous.clm_comp _ continuous_const
    exact (innerSL ℝ).continuous.comp (J.continuous.comp hVc)
  refine ⟨V, hVc, hV, ?_⟩
  intro t ht v v' hv
  have hweak : ∀ w, HasDerivAt (fun r => A r w) (-(B (V t)) w) t := by
    intro w
    have heq : (fun r => A r w) =ᶠ[nhds t]
        (fun r => inner ℝ (spectralHeatRow s r y) (J w)) := by
      filter_upwards [eventually_gt_nhds ht] with r hr
      simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
      have hJ : J (V r) = spectralHeatRow s r y := hV r hr.le
      rw [hJ]
    simpa only [neg_apply, hB] using
      (hderiv t ht w).congr_of_eventuallyEq heq
  have hp := hasDerivAt_weak_functional_apply A v v' t hAc.continuousAt hv
    (-(B (V t))) hweak
  have heq : (fun r => inner ℝ (spectralHeatRow s r y) (J (v r))) =ᶠ[nhds t]
      (fun r => A r (v r)) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    simp only [A, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
    have hJ : J (V r) = spectralHeatRow s r y := hV r hr.le
    rw [hJ]
  have hJt : J (V t) = spectralHeatRow s t y := hV t ht.le
  simp only [neg_apply, hB, A, ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hp
  rw [hJt] at hp
  exact hp.congr_of_eventuallyEq heq

/-- Integration by parts for a continuously differentiable Dirichlet-space
path against the native spectral row. -/
theorem spectral_heat_row_native_path_time_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a : ℝ) (ha : 0 < a) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ (c e : ℝ), a < c → a < e →
        ∀ (v v' : ℝ → DirichletHilbertSpace (d := d) R hR),
        Continuous v → Continuous v' → (∀ t, HasDerivAt v (v' t) t) →
        (∫ t in c..e, inner ℝ (spectralHeatRow s t y) (J (v' t))) =
          inner ℝ (spectralHeatRow s e y) (J (v e)) -
          inner ℝ (spectralHeatRow s c y) (J (v c)) +
          ∫ t in c..e, ∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (v t).val (some i) x) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨V, hVc, hV, hderiv⟩ :=
    spectral_heat_row_native_path_derivative hd hκ h R hR s u hb hvar a ha y hy
  obtain ⟨_, _, B, _, hB⟩ := exists_dirichletHilbert_energyForm hd hκ h R hR
  refine ⟨V, hVc, hV, ?_⟩
  intro c e hc he v v' hvc hv'c hvd
  let E : ℝ → ℝ := fun t => B (V t) (v t)
  let F : ℝ → ℝ := fun t => inner ℝ (J (V t)) (J (v' t))
  have hEc : Continuous E := (B.continuous.comp hVc).clm_apply hvc
  have hFc : Continuous F := (J.continuous.comp hVc).inner (J.continuous.comp hv'c)
  have hpos : ∀ t ∈ Set.uIcc c e, a < t := by
    intro t ht
    exact lt_of_lt_of_le (lt_min hc he) ht.1
  have hd' : ∀ t ∈ Set.uIcc c e, HasDerivAt
      (fun r => inner ℝ (spectralHeatRow s r y) (J (v r))) (-E t + F t) t := by
    intro t ht
    have hJ : J (V t) = spectralHeatRow s t y := hV t (hpos t ht).le
    dsimp only [E, F]
    rw [hJ, hB]
    exact hderiv t (hpos t ht) v (v' t) (hvd t)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd'
    ((hEc.neg.add hFc).intervalIntegrable c e)
  have hadd : (∫ t in c..e, -E t + F t) =
      -(∫ t in c..e, E t) + ∫ t in c..e, F t := by
    have hadd0 := intervalIntegral.integral_add (μ := volume) (a := c) (b := e)
      (f := -E) (g := F) (hEc.neg.intervalIntegrable c e) (hFc.intervalIntegrable c e)
    change (∫ t in c..e, -E t + F t) = (∫ t in c..e, -E t) +
      ∫ t in c..e, F t at hadd0
    rw [intervalIntegral.integral_neg] at hadd0
    exact hadd0
  have hF : (∫ t in c..e, inner ℝ (spectralHeatRow s t y) (J (v' t))) =
      ∫ t in c..e, F t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hJ : J (V t) = spectralHeatRow s t y := hV t (hpos t ht).le
    dsimp only [F]
    rw [hJ]
  have hE : (∫ t in c..e, E t) = ∫ t in c..e,
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => (v t).val (some i) x) := by
    simp only [E, hB]
  rw [hF, ← hE]
  linarith

/-- Compactly supported native paths satisfy the open-interval weak identity. -/
theorem spectral_heat_row_native_compact_path_time_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ (v v' : ℝ → DirichletHilbertSpace (d := d) R hR),
        Continuous v → Continuous v' → (∀ t, HasDerivAt v (v' t) t) →
        tsupport v ⊆ Set.Ioo a b →
        (∫ t in Set.Ioo a b, inner ℝ (spectralHeatRow s t y) (J (v' t))) =
          ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (v t).val (some i) x) := by
  dsimp only
  have ha2 : 0 < a / 2 := by linarith
  have haa : a / 2 < a := by linarith
  obtain ⟨V, hVc, hV, ht⟩ :=
    spectral_heat_row_native_path_time_test hd hκ h R hR s u hb hvar (a / 2) ha2 y hy
  refine ⟨V, hVc, fun t ht => hV t (le_trans haa.le ht), ?_⟩
  intro v v' hvc hv'c hvd hvs
  have hva : v a = 0 := image_eq_zero_of_notMem_tsupport (fun hm => (hvs hm).1.false)
  have hvb : v b = 0 := image_eq_zero_of_notMem_tsupport (fun hm => (hvs hm).2.false)
  have htest := ht a b haa (lt_trans haa hab) v v' hvc hv'c hvd
  dsimp only at htest
  simp only [hva, hvb, map_zero, inner_zero_right, sub_self, zero_add,
    intervalIntegral.integral_of_le hab.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at htest
  exact htest

/-- Smooth compact spacetime tests have spatial slices supported in one
common compact subset of the ball. -/
theorem spacetime_test_spatial_slices {d : ℕ} (R : ℝ)
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R) :
    ∃ K : Set (PDE.Vec d), IsCompact K ∧ K ⊆ sourceBall 0 R ∧
      ∀ t, ∃ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
        (φ : PDE.Vec d → ℝ) = (fun x => ψ (t, x)) ∧ tsupport φ ⊆ K := by
  let K : Set (PDE.Vec d) := Prod.snd '' tsupport ψ
  have hK : IsCompact K := hc.image continuous_snd
  have hKU : K ⊆ sourceBall (0 : PDE.Vec d) R := by
    rintro x ⟨z, hz, rfl⟩
    exact (hs hz).2
  refine ⟨K, hK, hKU, ?_⟩
  intro t
  have hsub : Function.support (fun x => ψ (t, x)) ⊆ K := by
    intro x hx
    exact ⟨(t, x), (subset_tsupport ψ) hx, rfl⟩
  have hts : tsupport (fun x => ψ (t, x)) ⊆ K :=
    closure_minimal hsub hK.isClosed
  let φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤ :=
    ⟨fun x => ψ (t, x), hψ.comp (contDiff_const.prodMk contDiff_id),
      HasCompactSupport.of_support_subset_isCompact hK hsub, hts.trans hKU⟩
  exact ⟨φ, rfl, hts⟩

/-- The time derivative of a smooth compact spacetime test is again a smooth
compact spacetime test, with no enlargement of support. -/
theorem spacetime_test_time_derivative {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    let ψt : ℝ × PDE.Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
    ContDiff ℝ (⊤ : ℕ∞) ψt ∧ HasCompactSupport ψt ∧
      tsupport ψt ⊆ tsupport ψ ∧
      ∀ t x, HasDerivAt (fun r => ψ (r, x)) (ψt (t, x)) t := by
  dsimp only
  refine ⟨(contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const,
    hc.fderiv_apply ℝ (1, 0), tsupport_fderiv_apply_subset ℝ (1, 0), ?_⟩
  intro t x
  exact ((contDiff_infty_iff_fderiv.mp hψ).1 (t, x)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

/-- A Dirichlet-space path made from the spatial slices inherits the
compact time support of the spacetime test. -/
theorem spacetime_test_native_path_tsupport {d : ℕ} (R : ℝ) (hR : 0 < R)
    (a b : ℝ) (ψ : ℝ × PDE.Vec d → ℝ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
    (v : ℝ → DirichletHilbertSpace (d := d) R hR)
    (hv : ∀ t, ∃ φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤,
      v t = dirichletSmoothElement R hR φ ∧
        (φ : PDE.Vec d → ℝ) = fun x => ψ (t, x)) :
    tsupport v ⊆ Set.Ioo a b := by
  let K : Set ℝ := Prod.fst '' tsupport ψ
  have hK : IsCompact K := hc.image continuous_fst
  have hsub : Function.support v ⊆ K := by
    intro t ht
    by_contra htK
    obtain ⟨φ, hvφ, hφ⟩ := hv t
    have hφ0 : φ = 0 := by
      ext x
      have hz : ψ (t, x) = 0 := image_eq_zero_of_notMem_tsupport (fun hm =>
        htK ⟨(t, x), hm, rfl⟩)
      change φ x = 0
      rw [hφ]
      exact hz
    apply ht
    rw [hvφ, hφ0]
    apply Subtype.ext
    change dirichletSmoothData R hR 0 = 0
    exact map_zero _
  have hKU : K ⊆ Set.Ioo a b := by
    rintro t ⟨z, hz, rfl⟩
    exact (hs hz).1
  exact (closure_minimal hsub hK.isClosed).trans hKU

/-- A smooth spacetime test and its time derivative give native paths with
common compact spatial support and compact time support. -/
theorem spacetime_test_native_paired_paths {d : ℕ} (R : ℝ) (hR : 0 < R)
    (a b : ℝ) (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) :
    ∃ (K : Set (PDE.Vec d))
      (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤),
      IsCompact K ∧ K ⊆ sourceBall 0 R ∧
      (∀ t, tsupport (φ t) ⊆ K ∧ tsupport (φt t) ⊆ K) ∧
      (∀ t x, (φ t) x = ψ (t, x) ∧
        HasDerivAt (fun r => (φ r) x) ((φt t) x) t) ∧
      tsupport (fun t => dirichletSmoothElement R hR (φ t)) ⊆ Set.Ioo a b ∧
      tsupport (fun t => dirichletSmoothElement R hR (φt t)) ⊆ Set.Ioo a b := by
  let ψt : ℝ × PDE.Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  obtain ⟨hψt, hct, hst, hd⟩ := spacetime_test_time_derivative ψ hψ hc
  have hs' : tsupport ψ ⊆ Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R := by
    intro z hz
    exact ⟨Set.mem_univ _, (hs hz).2⟩
  obtain ⟨K, hK, hKU, hφ⟩ := spacetime_test_spatial_slices R ψ hψ hc hs'
  obtain ⟨Kt, hKt, hKtU, hφt⟩ := spacetime_test_spatial_slices R ψt hψt hct
    (hst.trans hs')
  choose φ hφeq hφsupp using hφ
  choose φt hφteq hφtsupp using hφt
  refine ⟨K ∪ Kt, φ, φt, hK.union hKt, Set.union_subset hKU hKtU, ?_, ?_, ?_, ?_⟩
  · intro t
    exact ⟨(hφsupp t).trans Set.subset_union_left, (hφtsupp t).trans Set.subset_union_right⟩
  · intro t x
    refine ⟨congrFun (hφeq t) x, ?_⟩
    have heq : (fun r => (φ r) x) = (fun r => ψ (r, x)) := by
      funext r
      exact congrFun (hφeq r) x
    rw [heq, hφteq t]
    exact hd t x
  · apply spacetime_test_native_path_tsupport R hR a b ψ hc hs
    intro t
    exact ⟨φ t, rfl, hφeq t⟩
  · apply spacetime_test_native_path_tsupport R hR a b ψt hct (hst.trans hs)
    intro t
    exact ⟨φt t, rfl, hφteq t⟩

/-- On a compact spatial set, every directional derivative of a smooth
spacetime test varies uniformly with time on a compact interval. -/
theorem spacetime_test_directional_derivative_uniform_time {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : ℝ × PDE.Vec d) (K : Set (PDE.Vec d)) (hK : IsCompact K)
    (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      dist t s < δ → ∀ x ∈ K,
        dist (fderiv ℝ ψ (t, x) v) (fderiv ℝ ψ (s, x) v) < ε := by
  have hc : Continuous (fun z => fderiv ℝ ψ z v) :=
    ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
  have hu : UniformContinuousOn (fun z => fderiv ℝ ψ z v) (Set.Icc a b ×ˢ K) :=
    (isCompact_Icc.prod hK).uniformContinuousOn_of_continuous hc.continuousOn
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts x hx
  apply hδu (t, x) ⟨ht, hx⟩ (s, x) ⟨hs, hx⟩
  simpa only [dist_prod_same_right] using hts

/-- The time derivative commutes with every spatial directional derivative
of a smooth spacetime test. -/
theorem spacetime_test_spatial_derivative_time {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : PDE.Vec d) (t : ℝ) (x : PDE.Vec d) :
    HasDerivAt (fun r => fderiv ℝ ψ (r, x) (0, v))
      (fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0)) (t, x) (0, v)) t := by
  let z : ℝ × PDE.Vec d := (t, x)
  have hf : Differentiable ℝ ψ := (contDiff_infty_iff_fderiv.mp hψ).1
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (contDiff_infty_iff_fderiv.mp (contDiff_infty_iff_fderiv.mp hψ).2).1
  have hsym := second_derivative_symmetric (fun y => (hf y).hasFDerivAt)
    (hd z).hasFDerivAt (1, 0) (0, v)
  have hspace := (hd z).hasFDerivAt.clm_apply (hasFDerivAt_const (0, v) z)
  have htime := (hd z).hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) z)
  have hspace' := hspace.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have heq : fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0)) (t, x) (0, v) =
      fderiv ℝ (fderiv ℝ ψ) z (1, 0) (0, v) := by
    rw [htime.fderiv]
    simpa using hsym.symm
  rw [heq]
  simpa [z, Function.comp_def] using hspace'

/-- Smooth spacetime slices have a uniform first-order time remainder on
compact spatial sets and compact time intervals. -/
theorem spacetime_test_uniform_time_remainder {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (K : Set (PDE.Vec d)) (hK : IsCompact K) (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      dist t s < δ → ∀ x ∈ K,
      ‖ψ (s, x) - ψ (t, x) - (s - t) * fderiv ℝ ψ (t, x) (1, 0)‖
        ≤ ε * ‖s - t‖ := by
  intro ε hε
  obtain ⟨δ, hδ, hu⟩ :=
    spacetime_test_directional_derivative_uniform_time ψ hψ (1, 0) K hK a b ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts x hx
  let c := fderiv ℝ ψ (t, x) (1, 0)
  let g : ℝ → ℝ := (fun r => ψ (r, x)) - (fun r => (r - t) * c)
  have hd (r : ℝ) : HasDerivAt g (fderiv ℝ ψ (r, x) (1, 0) - c) r := by
    have h := ((contDiff_infty_iff_fderiv.mp hψ).1 (r, x)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
    simpa only [g, Function.comp_def, id_eq, one_mul] using h.sub (((hasDerivAt_id r).sub_const t).mul_const c)
  have hb (r : ℝ) (hr : r ∈ Set.uIcc t s) :
      ‖fderiv ℝ ψ (r, x) (1, 0) - c‖ ≤ ε := by
    have hr' : r ∈ Set.Icc a b := Set.uIcc_subset_Icc ht hs hr
    have hrt : dist t r < δ := lt_of_le_of_lt (Real.dist_left_le_of_mem_uIcc hr) hts
    have hh := hu t ht r hr' hrt x hx
    simpa [c, Real.dist_eq, Real.norm_eq_abs, abs_sub_comm] using le_of_lt hh
  have hg := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r _ => (hd r).hasDerivWithinAt) hb (convex_uIcc t s)
    (Set.left_mem_uIcc) (Set.right_mem_uIcc)
  have heq : g s - g t = ψ (s, x) - ψ (t, x) - (s - t) * c := by
    dsimp [g, Pi.sub_apply]
    ring
  rw [heq] at hg
  simpa [c] using hg

/-- Spatial directional derivatives of smooth spacetime slices have a uniform
first-order time remainder, with the mixed derivative in either order. -/
theorem spacetime_test_spatial_uniform_time_remainder {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (v : PDE.Vec d) (K : Set (PDE.Vec d)) (hK : IsCompact K) (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      dist t s < δ → ∀ x ∈ K,
      ‖fderiv ℝ ψ (s, x) (0, v) - fderiv ℝ ψ (t, x) (0, v) -
        (s - t) * fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0)) (t, x) (0, v)‖
        ≤ ε * ‖s - t‖ := by
  let φ : ℝ × PDE.Vec d → ℝ := fun z => fderiv ℝ ψ z (0, v)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const
  have hder (t : ℝ) (x : PDE.Vec d) :
      fderiv ℝ φ (t, x) (1, 0) =
        fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0)) (t, x) (0, v) := by
    have h1 := ((contDiff_infty_iff_fderiv.mp hφ).1 (t, x)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
    have h2 := spacetime_test_spatial_derivative_time ψ hψ v t x
    exact (by simpa [φ, Function.comp_def] using h1 :
      HasDerivAt (fun r => fderiv ℝ ψ (r, x) (0, v))
        (fderiv ℝ φ (t, x) (1, 0)) t).unique h2
  intro ε hε
  obtain ⟨δ, hδ, hδu⟩ := spacetime_test_uniform_time_remainder φ hφ K hK a b ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts x hx
  simpa only [φ, hder] using hδu t ht s hs hts x hx

/-- A single time scale controls the value and every coordinate derivative
of a smooth spacetime test on a compact spatial set. -/
theorem spacetime_test_all_uniform_time_remainders {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (K : Set (PDE.Vec d)) (hK : IsCompact K) (a b : ℝ) :
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      dist t s < δ → ∀ x ∈ K,
      ‖ψ (s, x) - ψ (t, x) - (s - t) * fderiv ℝ ψ (t, x) (1, 0)‖
          ≤ ε * ‖s - t‖ ∧
      ∀ i : Fin d,
        ‖fderiv ℝ ψ (s, x) (0, unitVector i) -
          fderiv ℝ ψ (t, x) (0, unitVector i) -
          (s - t) * fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0))
            (t, x) (0, unitVector i)‖ ≤ ε * ‖s - t‖ := by
  intro ε hε
  have hall (I : Finset (Fin d)) : ∃ δ > 0,
      ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b, dist t s < δ →
        ∀ x ∈ K, ∀ i ∈ I,
          ‖fderiv ℝ ψ (s, x) (0, unitVector i) -
            fderiv ℝ ψ (t, x) (0, unitVector i) -
            (s - t) * fderiv ℝ (fun z => fderiv ℝ ψ z (1, 0))
              (t, x) (0, unitVector i)‖ ≤ ε * ‖s - t‖ := by
    classical
    induction I using Finset.induction_on with
    | empty =>
        refine ⟨1, zero_lt_one, ?_⟩
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true]
    | @insert i I hi ih =>
        obtain ⟨δ₁, hδ₁, h₁⟩ := ih
        obtain ⟨δ₂, hδ₂, h₂⟩ :=
          spacetime_test_spatial_uniform_time_remainder ψ hψ (unitVector i) K hK a b ε hε
        refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
        intro t ht s hs hts x hx j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h₂ t ht s hs (lt_of_lt_of_le hts (min_le_right _ _)) x hx
        · exact h₁ t ht s hs (lt_of_lt_of_le hts (min_le_left _ _)) x hx j hj
  obtain ⟨δ₁, hδ₁, h₁⟩ := hall Finset.univ
  obtain ⟨δ₂, hδ₂, h₂⟩ := spacetime_test_uniform_time_remainder ψ hψ K hK a b ε hε
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht s hs hts x hx
  refine ⟨h₂ t ht s hs (lt_of_lt_of_le hts (min_le_right _ _)) x hx, ?_⟩
  intro i
  exact h₁ t ht s hs (lt_of_lt_of_le hts (min_le_left _ _)) x hx i (Finset.mem_univ i)

#print axioms spacetime_test_all_uniform_time_remainders

/-- A common bound for the value and all gradient coordinates controls the
actual Dirichlet Hilbert norm. -/
theorem dirichletHilbert_norm_le_of_component_bounds {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (C : ℝ) (hC : 0 ≤ C)
    (hvalue : ‖(hilbertToSobolev _ u.val).1‖ ≤ C)
    (hgrad : ∀ i : Fin d, ‖(hilbertToSobolev _ u.val).2 i‖ ≤ C) :
    ‖u‖ ≤ Real.sqrt ((d : ℝ) + 1) * C := by
  have hv : ‖(hilbertToSobolev _ u.val).1‖ ^ 2 ≤ C ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hvalue 2
  have hg : (∑ i : Fin d, ‖(hilbertToSobolev _ u.val).2 i‖ ^ 2) ≤
      (d : ℝ) * C ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, C ^ 2 :=
        Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hgrad i) 2)
      _ = (d : ℝ) * C ^ 2 := by simp
  have hs : ‖u‖ ^ 2 ≤ ((d : ℝ) + 1) * C ^ 2 := by
    rw [dirichletHilbert_norm_sq R hR u]
    nlinarith
  have hr : 0 ≤ Real.sqrt ((d : ℝ) + 1) * C :=
    mul_nonneg (Real.sqrt_nonneg _) hC
  have he : (Real.sqrt ((d : ℝ) + 1) * C) ^ 2 =
      ((d : ℝ) + 1) * C ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (d : ℝ) + 1)]
  nlinarith [norm_nonneg u]

/-- Pointwise bounds on the value and coordinate representatives give an
explicit Dirichlet norm bound through the finite containing cube. -/
theorem dirichletHilbert_norm_le_of_ae_component_bounds {d : ℕ}
    (R : ℝ) (hR : 0 < R) (u : DirichletHilbertSpace (d := d) R hR)
    (C : ℝ) (hC : 0 ≤ C) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := volume.restrict (Q : Set (PDE.Vec d))
    (∀ᵐ x ∂μ, ‖(hilbertToSobolev Q u.val).1 x‖ ≤ C) →
    (∀ i : Fin d, ∀ᵐ x ∂μ, ‖(hilbertToSobolev Q u.val).2 i x‖ ≤ C) →
    ‖u‖ ≤ Real.sqrt ((d : ℝ) + 1) *
      (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * C) := by
  dsimp only
  intro hv hg
  let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (PDE.Vec d))
  haveI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hc : 0 ≤ (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * C) :=
    mul_nonneg (NNReal.coe_nonneg _) hC
  apply dirichletHilbert_norm_le_of_component_bounds R hR u _ hc
  · exact Lp.norm_le_of_ae_bound hC hv
  · intro i
    exact Lp.norm_le_of_ae_bound hC (hg i)

#print axioms dirichletHilbert_norm_le_of_ae_component_bounds

#print axioms dirichletHilbert_norm_le_of_component_bounds

/-- Bounds for a smooth test and its coordinate derivatives control the
Dirichlet norm of its native representative. -/
theorem dirichletSmoothElement_norm_le_of_bounds {d : ℕ}
    (R : ℝ) (hR : 0 < R) (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ x, ‖φ x‖ ≤ C)
    (hg : ∀ i : Fin d, ∀ x, ‖fderiv ℝ (φ : PDE.Vec d → ℝ) x (Pi.single i 1)‖ ≤ C) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := volume.restrict (Q : Set (PDE.Vec d))
    ‖dirichletSmoothElement R hR φ‖ ≤ Real.sqrt ((d : ℝ) + 1) *
      (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * C) := by
  dsimp only
  let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
  let ψ := dirichletTestInCube R hR φ
  apply dirichletHilbert_norm_le_of_ae_component_bounds R hR _ C hC
  · change ∀ᵐ x ∂volume.restrict (Q : Set (PDE.Vec d)),
      ‖(SubdiffusiveProcess.smoothSobolevData ψ).1 x‖ ≤ C
    filter_upwards [SubdiffusiveProcess.testL2_coeFn ψ] with x hx
    change ‖SubdiffusiveProcess.testL2 ψ x‖ ≤ C
    rw [hx]
    exact hv x
  · intro i
    change ∀ᵐ x ∂volume.restrict (Q : Set (PDE.Vec d)),
      ‖(SubdiffusiveProcess.smoothSobolevData ψ).2 i x‖ ≤ C
    filter_upwards [SubdiffusiveProcess.testPartialL2_coeFn ψ i] with x hx
    change ‖SubdiffusiveProcess.testPartialL2 ψ i x‖ ≤ C
    rw [hx]
    exact hg i x

#print axioms dirichletSmoothElement_norm_le_of_bounds

/-- A first-order remainder in smooth tests has the corresponding native
Hilbert-space norm bound. -/
theorem dirichletSmoothElement_remainder_norm_le {d : ℕ}
    (R : ℝ) (hR : 0 < R)
    (φs φt φd : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (c C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ x, ‖φs x - φt x - c * φd x‖ ≤ C)
    (hg : ∀ i : Fin d, ∀ x,
      ‖fderiv ℝ (φs : PDE.Vec d → ℝ) x (Pi.single i 1) -
        fderiv ℝ (φt : PDE.Vec d → ℝ) x (Pi.single i 1) -
        c * fderiv ℝ (φd : PDE.Vec d → ℝ) x (Pi.single i 1)‖ ≤ C) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := volume.restrict (Q : Set (PDE.Vec d))
    ‖dirichletSmoothElement R hR φs - dirichletSmoothElement R hR φt -
        c • dirichletSmoothElement R hR φd‖ ≤ Real.sqrt ((d : ℝ) + 1) *
      (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * C) := by
  let φ := φs - φt - c • φd
  have heq : dirichletSmoothElement R hR φ =
      dirichletSmoothElement R hR φs - dirichletSmoothElement R hR φt -
        c • dirichletSmoothElement R hR φd := by
    apply Subtype.ext
    simp only [dirichletSmoothElement, φ, map_sub, map_smul, Submodule.coe_sub,
      Submodule.coe_smul]
  rw [← heq]
  apply dirichletSmoothElement_norm_le_of_bounds R hR φ C hC
  · intro x
    simpa [φ] using hv x
  · intro i x
    have hs := φs.contDiff.differentiable (by simp) x
    have ht := φt.contDiff.differentiable (by simp) x
    have hd := φd.contDiff.differentiable (by simp) x
    change ‖fderiv ℝ ((φs : PDE.Vec d → ℝ) - (φt : PDE.Vec d → ℝ) - c • (φd : PDE.Vec d → ℝ)) x (Pi.single i 1)‖ ≤ C
    rw [fderiv_sub (hs.sub ht) (hd.const_smul c), fderiv_sub hs ht,
      fderiv_const_smul hd c]
    simpa using hg i x

#print axioms dirichletSmoothElement_remainder_norm_le

/-- Outside a common support, a smooth test and all of its spatial
coordinate derivatives vanish. -/
theorem spacetime_test_slice_zero_outside_support {d : ℕ} (R : ℝ)
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (K : Set (PDE.Vec d)) (hφ : tsupport φ ⊆ K)
    (x : PDE.Vec d) (hx : x ∉ K) :
    φ x = 0 ∧ ∀ i : Fin d,
      fderiv ℝ (φ : PDE.Vec d → ℝ) x (Pi.single i 1) = 0 := by
  have hnot : x ∉ tsupport (φ : PDE.Vec d → ℝ) := fun h => hx (hφ h)
  refine ⟨image_eq_zero_of_notMem_tsupport hnot, ?_⟩
  intro i
  have hn : x ∉ tsupport (fun z => fderiv ℝ (φ : PDE.Vec d → ℝ) z (Pi.single i 1)) :=
    fun h => hnot ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)) h)
  have hh := image_eq_zero_of_notMem_tsupport hn
  exact hh

#print axioms spacetime_test_slice_zero_outside_support

/-- Remainder bounds on the common support suffice for a bound in the
native Dirichlet Hilbert norm. -/
theorem dirichletSmoothElement_remainder_norm_le_on_support {d : ℕ}
    (R : ℝ) (hR : 0 < R)
    (φs φt φd : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (K : Set (PDE.Vec d)) (hs : tsupport φs ⊆ K)
    (ht : tsupport φt ⊆ K) (hd : tsupport φd ⊆ K)
    (c C : ℝ) (hC : 0 ≤ C)
    (hv : ∀ x ∈ K, ‖φs x - φt x - c * φd x‖ ≤ C)
    (hg : ∀ i : Fin d, ∀ x ∈ K,
      ‖fderiv ℝ (φs : PDE.Vec d → ℝ) x (Pi.single i 1) -
        fderiv ℝ (φt : PDE.Vec d → ℝ) x (Pi.single i 1) -
        c * fderiv ℝ (φd : PDE.Vec d → ℝ) x (Pi.single i 1)‖ ≤ C) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := volume.restrict (Q : Set (PDE.Vec d))
    ‖dirichletSmoothElement R hR φs - dirichletSmoothElement R hR φt -
        c • dirichletSmoothElement R hR φd‖ ≤ Real.sqrt ((d : ℝ) + 1) *
      (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) * C) := by
  apply dirichletSmoothElement_remainder_norm_le R hR φs φt φd c C hC
  · intro x
    by_cases hx : x ∈ K
    · exact hv x hx
    · obtain ⟨hsv, hsg⟩ := spacetime_test_slice_zero_outside_support R φs K hs x hx
      obtain ⟨htv, htg⟩ := spacetime_test_slice_zero_outside_support R φt K ht x hx
      obtain ⟨hdv, hdg⟩ := spacetime_test_slice_zero_outside_support R φd K hd x hx
      simpa [hsv, htv, hdv] using hC
  · intro i x
    by_cases hx : x ∈ K
    · exact hg i x hx
    · obtain ⟨hsv, hsg⟩ := spacetime_test_slice_zero_outside_support R φs K hs x hx
      obtain ⟨htv, htg⟩ := spacetime_test_slice_zero_outside_support R φt K ht x hx
      obtain ⟨hdv, hdg⟩ := spacetime_test_slice_zero_outside_support R φd K hd x hx
      simpa [hsg i, htg i, hdg i] using hC

#print axioms dirichletSmoothElement_remainder_norm_le_on_support

/-- The spatial derivative of a smooth slice is the corresponding spatial
partial derivative of the spacetime test. -/
theorem spacetime_test_slice_fderiv {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (t : ℝ) (x v : PDE.Vec d) :
    fderiv ℝ (fun z => ψ (t, z)) x v = fderiv ℝ ψ (t, x) (0, v) := by
  have h := ((contDiff_infty_iff_fderiv.mp hψ).1 (t, x)).hasFDerivAt.comp x
    ((hasFDerivAt_const t x).prodMk (hasFDerivAt_id x))
  change fderiv ℝ (ψ ∘ Prod.mk t) x v = fderiv ℝ ψ (t, x) (0, v)
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    zero_apply, ContinuousLinearMap.id_apply]

/-- Smooth spacetime slices have a uniform first-order remainder in the
native Dirichlet norm on every compact time interval. -/
theorem spacetime_test_native_uniform_remainder {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ψ : ℝ × PDE.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (K : Set (PDE.Vec d)) (hK : IsCompact K)
    (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (hsupp : ∀ t, tsupport (φ t) ⊆ K ∧ tsupport (φt t) ⊆ K)
    (heq : ∀ t, (φ t : PDE.Vec d → ℝ) = fun x => ψ (t, x))
    (heqt : ∀ t, (φt t : PDE.Vec d → ℝ) =
      fun x => fderiv ℝ ψ (t, x) (1, 0)) (a b : ℝ) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := volume.restrict (Q : Set (PDE.Vec d))
    ∀ ε > 0, ∃ δ > 0, ∀ t ∈ Set.Icc a b, ∀ s ∈ Set.Icc a b,
      dist t s < δ →
      ‖dirichletSmoothElement R hR (φ s) - dirichletSmoothElement R hR (φ t) -
          (s - t) • dirichletSmoothElement R hR (φt t)‖ ≤
        Real.sqrt ((d : ℝ) + 1) *
          (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ) *
            (ε * ‖s - t‖)) := by
  dsimp only
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := spacetime_test_all_uniform_time_remainders ψ hψ K hK a b ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht s hs hts
  apply dirichletSmoothElement_remainder_norm_le_on_support R hR (φ s) (φ t) (φt t)
    K (hsupp s).1 (hsupp t).1 (hsupp t).2 (s - t) (ε * ‖s - t‖)
    (mul_nonneg hε.le (norm_nonneg _))
  · intro x hx
    simpa only [heq, heqt] using (hrem t ht s hs hts x hx).1
  · intro i x hx
    have hψt : ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ ψ z (1, 0)) :=
      (contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const
    rw [heq s, heq t, heqt t, spacetime_test_slice_fderiv ψ hψ s x,
      spacetime_test_slice_fderiv ψ hψ t x,
      spacetime_test_slice_fderiv _ hψt t x]
    simpa only [unitVector] using (hrem t ht s hs hts x hx).2 i

/-- The native Dirichlet path of smooth slices has its actual time derivative. -/
theorem spacetime_test_native_hasDerivAt {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ψ : ℝ × PDE.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (K : Set (PDE.Vec d)) (hK : IsCompact K)
    (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (hsupp : ∀ t, tsupport (φ t) ⊆ K ∧ tsupport (φt t) ⊆ K)
    (heq : ∀ t, (φ t : PDE.Vec d → ℝ) = fun x => ψ (t, x))
    (heqt : ∀ t, (φt t : PDE.Vec d → ℝ) =
      fun x => fderiv ℝ ψ (t, x) (1, 0)) (t : ℝ) :
    HasDerivAt (fun s => dirichletSmoothElement R hR (φ s))
      (dirichletSmoothElement R hR (φt t)) t := by
  let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
  let μ := volume.restrict (Q : Set (PDE.Vec d))
  let C : ℝ := Real.sqrt ((d : ℝ) + 1) *
    (((measureUnivNNReal μ ^ (2 : ℝ≥0∞).toReal⁻¹ : ℝ≥0) : ℝ))
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) (NNReal.coe_nonneg _)
  apply hasDerivAt_iff_isLittleO.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := spacetime_test_native_uniform_remainder R hR ψ hψ K hK
    φ φt hsupp heq heqt (t - 1) (t + 1) (ε / (C + 1))
      (div_pos hε (by linarith))
  filter_upwards [Metric.ball_mem_nhds t (lt_min hδ zero_lt_one)] with s hs
  have hdist : dist t s < min δ 1 := by simpa [dist_comm] using hs
  have ht : t ∈ Set.Icc (t - 1) (t + 1) := by constructor <;> linarith
  have hs' : s ∈ Set.Icc (t - 1) (t + 1) := by
    have h := lt_of_lt_of_le hdist (min_le_right δ 1)
    rw [Real.dist_eq] at h
    have habs := abs_lt.mp h
    constructor <;> linarith
  have hb := hrem t ht s hs' (lt_of_lt_of_le hdist (min_le_left δ 1))
  change ‖dirichletSmoothElement R hR (φ s) - dirichletSmoothElement R hR (φ t) -
    (s - t) • dirichletSmoothElement R hR (φt t)‖ ≤ ε * ‖s - t‖
  have hc : C * (ε / (C + 1)) ≤ ε := by
    have hp : 0 < C + 1 := by linarith
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hp).2
    nlinarith
  calc
    _ ≤ C * ((ε / (C + 1)) * ‖s - t‖) := by
      simpa only [C, μ, Q, mul_assoc] using hb
    _ = (C * (ε / (C + 1))) * ‖s - t‖ := by ring
    _ ≤ ε * ‖s - t‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)

/-- The native path of time-derivative slices is continuous. -/
theorem spacetime_test_native_time_derivative_continuous {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ψ : ℝ × PDE.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R)
    (K : Set (PDE.Vec d)) (hK : IsCompact K)
    (φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (hsupp : ∀ t, tsupport (φt t) ⊆ K)
    (heqt : ∀ t, (φt t : PDE.Vec d → ℝ) =
      fun x => fderiv ℝ ψ (t, x) (1, 0)) :
    Continuous (fun t => dirichletSmoothElement R hR (φt t)) := by
  let ψt : ℝ × PDE.Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  obtain ⟨hψt, hct, hst, _⟩ := spacetime_test_time_derivative ψ hψ hc
  obtain ⟨hψtt, hctt, hstt, _⟩ := spacetime_test_time_derivative ψt hψt hct
  obtain ⟨Ktt, hKtt, _, hφtt⟩ :=
    spacetime_test_spatial_slices R (fun z => fderiv ℝ ψt z (1, 0)) hψtt hctt
      (hstt.trans (hst.trans hs))
  choose φtt hφtteq hφttsupp using hφtt
  apply continuous_iff_continuousAt.mpr
  intro t
  apply HasDerivAt.continuousAt
  apply spacetime_test_native_hasDerivAt R hR ψt hψt (K ∪ Ktt) (hK.union hKtt)
    φt φtt
  · intro s
    exact ⟨(hsupp s).trans Set.subset_union_left,
      (hφttsupp s).trans Set.subset_union_right⟩
  · exact heqt
  · exact hφtteq

/-- A smooth compact spacetime test yields continuously differentiable native paths. -/
theorem spacetime_test_native_c1_paths {d : ℕ} (R : ℝ) (hR : 0 < R)
    (a b : ℝ) (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) :
    ∃ (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤),
      (∀ t, (φ t : PDE.Vec d → ℝ) = fun x => ψ (t, x)) ∧
      (∀ t, (φt t : PDE.Vec d → ℝ) = fun x => fderiv ℝ ψ (t, x) (1, 0)) ∧
      Continuous (fun t => dirichletSmoothElement R hR (φ t)) ∧
      Continuous (fun t => dirichletSmoothElement R hR (φt t)) ∧
      (∀ t, HasDerivAt (fun s => dirichletSmoothElement R hR (φ s))
        (dirichletSmoothElement R hR (φt t)) t) ∧
      tsupport (fun t => dirichletSmoothElement R hR (φ t)) ⊆ Set.Ioo a b := by
  let ψt : ℝ × PDE.Vec d → ℝ := fun z => fderiv ℝ ψ z (1, 0)
  obtain ⟨hψt, hct, hst, _⟩ := spacetime_test_time_derivative ψ hψ hc
  have hs' : tsupport ψ ⊆ Set.univ ×ˢ sourceBall (0 : PDE.Vec d) R := by
    intro z hz
    exact ⟨Set.mem_univ _, (hs hz).2⟩
  obtain ⟨K, hK, _, hφ⟩ := spacetime_test_spatial_slices R ψ hψ hc hs'
  obtain ⟨Kt, hKt, _, hφt⟩ := spacetime_test_spatial_slices R ψt hψt hct (hst.trans hs')
  choose φ hφeq hφsupp using hφ
  choose φt hφteq hφtsupp using hφt
  have hsupp : ∀ t, tsupport (φ t) ⊆ K ∪ Kt ∧ tsupport (φt t) ⊆ K ∪ Kt := by
    intro t
    exact ⟨(hφsupp t).trans Set.subset_union_left, (hφtsupp t).trans Set.subset_union_right⟩
  have hd : ∀ t, HasDerivAt (fun s => dirichletSmoothElement R hR (φ s))
      (dirichletSmoothElement R hR (φt t)) t :=
    spacetime_test_native_hasDerivAt R hR ψ hψ (K ∪ Kt) (hK.union hKt)
      φ φt hsupp hφeq hφteq
  refine ⟨φ, φt, hφeq, hφteq, ?_, ?_, hd, ?_⟩
  · exact continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)
  · exact spacetime_test_native_time_derivative_continuous R hR ψ hψ hc hs'
      Kt hKt φt hφtsupp hφteq
  · apply spacetime_test_native_path_tsupport R hR a b ψ hc hs
    intro t
    exact ⟨φ t, rfl, hφeq t⟩

/-- Smooth spacetime tests satisfy the spectral weak identity in native form. -/
theorem spectral_heat_row_native_spacetime_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        ∃ (φ φt : ℝ → TestFunction (dirichletBall (d := d) R) ℝ ⊤),
          (∀ t, (φ t : PDE.Vec d → ℝ) = fun x => ψ (t, x)) ∧
          (∀ t, (φt t : PDE.Vec d → ℝ) = fun x => fderiv ℝ ψ (t, x) (1, 0)) ∧
          (∫ t in Set.Ioo a b, inner ℝ (spectralHeatRow s t y)
            (J (dirichletSmoothElement R hR (φt t)))) =
          ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (V t).val (some i) x))
              (fun i => (dirichletSmoothElement R hR (φ t)).val (some i) x) := by
  dsimp only
  obtain ⟨V, hVc, hV, htest⟩ :=
    spectral_heat_row_native_compact_path_time_test hd hκ h R hR s u hb hvar a b ha hab y hy
  refine ⟨V, hVc, hV, ?_⟩
  intro ψ hψ hc hs
  obtain ⟨φ, φt, heq, heqt, hv, hvt, hdv, hsup⟩ :=
    spacetime_test_native_c1_paths R hR a b ψ hψ hc hs
  exact ⟨φ, φt, heq, heqt, htest _ _ hv hvt hdv hsup⟩

/-- Native smooth-test coordinates agree with the literal spacetime slice on
almost every point of the source ball. -/
theorem spacetime_test_native_slice_representatives {d : ℕ}
    (R : ℝ) (hR : 0 < R) (ψ : ℝ × PDE.Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (t : ℝ)
    (φ : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (heq : (φ : PDE.Vec d → ℝ) = fun x => ψ (t, x)) :
    (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R),
      (dirichletSmoothElement R hR φ).val none x = ψ (t, x)) ∧
    (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R),
      ∀ i : Fin d, (dirichletSmoothElement R hR φ).val (some i) x =
        fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  have hle := Measure.restrict_mono_set (volume : Measure (PDE.Vec d))
    (sourceBall_subset_cube R hR)
  constructor
  · have hv := (SubdiffusiveProcess.testL2_coeFn (dirichletTestInCube R hR φ)).filter_mono
      (Measure.absolutelyContinuous_of_le hle).ae_le
    filter_upwards [hv] with x hx
    change (dirichletSmoothElement R hR φ).val none x = φ x at hx
    rw [hx, heq]
  · have hg (i : Fin d) :=
      (SubdiffusiveProcess.testPartialL2_coeFn (dirichletTestInCube R hR φ) i).filter_mono
        (Measure.absolutelyContinuous_of_le hle).ae_le
    filter_upwards [ae_all_iff.mpr hg] with x hx i
    have hxi := hx i
    change (dirichletSmoothElement R hR φ).val (some i) x =
      fderiv ℝ (φ : PDE.Vec d → ℝ) x (Pi.single i 1) at hxi
    rw [hxi, heq, spacetime_test_slice_fderiv ψ hψ]

/-- On a positive time slice the native scalar product and energy pairing
are the literal weighted value and spatial-gradient integrals. -/
theorem spectral_heat_row_spacetime_slice_pairings {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (t : ℝ) (ht : 0 < t) (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R)
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (φ φt : TestFunction (dirichletBall (d := d) R) ℝ ⊤)
    (heq : (φ : PDE.Vec d → ℝ) = fun x => ψ (t, x))
    (heqt : (φt : PDE.Vec d → ℝ) = fun x => fderiv ℝ ψ (t, x) (1, 0))
    (v : DirichletHilbertSpace (d := d) R hR) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    inner ℝ (spectralHeatRow s t y) (J (dirichletSmoothElement R hR φt)) =
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
          s.eigenfunction i y) * fderiv ℝ ψ (t, x) (1, 0)) ∧
    (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => v.val (some i) x))
        (fun i => (dirichletSmoothElement R hR φ).val (some i) x)) =
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => v.val (some i) x))
          (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  constructor
  · apply dirichletVolume_inner_eq_native hκ h
    · filter_upwards [spectral_heat_row_Lp_ae_eq hd hκ h hR s t ht y hy] with x hx
      change (spectralHeatRow s t y) x = _ at hx
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hx
    · filter_upwards [dirichletHilbertInclusion_smooth_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) φt] with x hx
      simpa only [heqt] using hx
  · apply integral_congr_ae
    filter_upwards [(spacetime_test_native_slice_representatives R hR ψ hψ t φ heq).2]
      with x hx
    rw [funext hx]

/-- The spectral weak identity with literal test derivatives in both
spatial integrals, on every positive time strip. -/
theorem spectral_heat_row_spacetime_iterated_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ V : ℝ → DirichletHilbertSpace (d := d) R hR,
      Continuous V ∧ (∀ t, a ≤ t → J (V t) = spectralHeatRow s t y) ∧
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
            s.eigenfunction i y) * fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, hVc, hV, htest⟩ :=
    spectral_heat_row_native_spacetime_test hd hκ h R hR s u hb hvar a b ha hab y hy
  refine ⟨V, hVc, hV, ?_⟩
  intro ψ hψ hc hs
  obtain ⟨φ, φt, heq, heqt, hid⟩ := htest ψ hψ hc hs
  have hpair : ∀ t ∈ Set.Ioo a b,
      inner ℝ (spectralHeatRow s t y) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (dirichletSmoothElement R hR (φt t))) =
        (∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
            s.eigenfunction i y) * fderiv ℝ ψ (t, x) (1, 0)) ∧
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => (dirichletSmoothElement R hR (φ t)).val (some i) x)) =
        ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (fun i => (V t).val (some i) x))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
    intro t ht
    exact spectral_heat_row_spacetime_slice_pairings hd hκ h R hR s t
      (ha.trans ht.1) y hy ψ hψ (φ t) (φt t) (heq t) (heqt t) (V t)
  have hl : (∫ t in Set.Ioo a b, inner ℝ (spectralHeatRow s t y)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        (dirichletSmoothElement R hR (φt t)))) =
      ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
          s.eigenfunction i y) * fderiv ℝ ψ (t, x) (1, 0) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hpair t ht).1
  have hr : (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (V t).val (some i) x))
        (fun i => (dirichletSmoothElement R hR (φ t)).val (some i) x)) =
      ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (V t).val (some i) x))
          (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hpair t ht).2
  exact hl.symm.trans (hid.trans hr)

/-- The iterated weak identity uses the same jointly measurable L²
spatial gradient as the spectral row's native Dirichlet path. -/
theorem spectral_heat_row_joint_gradient_iterated_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let Q := SubdiffusiveProcess.centeredCube (0 : PDE.Vec d) (2 * R) (mul_pos two_pos hR)
    let μ := (volume.restrict (Set.Ioo a b)).prod (volume.restrict (Q : Set (PDE.Vec d)))
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR) (G : ℝ × PDE.Vec d → PDE.Vec d),
      Continuous V ∧
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G μ ∧ MemLp (fun z => euclideanNorm (G z)) 2 μ ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (fun x => G (t, x)) =ᵐ[volume.restrict (Q : Set (PDE.Vec d))]
          (fun x i => (V t).val (some i) x)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) (fun x => G (t, x))) ∧
      ∀ (ψ : ℝ × PDE.Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ →
        tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * (∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x *
            s.eigenfunction i y) * fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs⟩ :=
    spectral_heat_row_gradient_vector_representative hd hκ h R hR s u hb hvar a b ha y hy
  obtain ⟨W, _, hW, htest⟩ :=
    spectral_heat_row_spacetime_iterated_test hd hκ h R hR s u hb hvar a b ha hab y hy
  have hVW : ∀ t ∈ Set.Icc a b, V t = W t := by
    intro t ht
    apply injective_dirichletHilbertInclusion hκ h R hR
    exact (hV t ht).trans (hW t ht.1).symm
  have hGs' : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V t).val (some i) x) := by
    filter_upwards [hGs] with t ht
    exact ht
  have hw0 := product_spatial_zeroExtension_weakGradient
    (volume.restrict (Set.Ioo a b)) R hR V G hGs'
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  have hw : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
        (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) (fun x => G (t, x)) := by
    filter_upwards [hw0, ae_restrict_mem measurableSet_Ioo] with t ht htab
    have he : (fun x => (V t).val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) := by
      apply hac.ae_le
      filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t),
        spectral_heat_row_Lp_ae_eq hd hκ h hR s t (lt_trans ha htab.1) y hy] with x hx hy'
      change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ (V t)) x = (V t).val none x at hx
      change (spectralHeatRow s t y) x = _ at hy'
      rw [hV t ⟨htab.1.le, htab.2.le⟩] at hx
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hx.symm.trans hy'
    apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae hball
      (EinsteinRelation.Correctors.hasWeakGradient_mono (Set.subset_univ _) ht)
    · filter_upwards [he, ae_restrict_mem hball.measurableSet] with x hx hxB
      simpa only [dirichletHilbertZeroExtension, Set.indicator_of_mem hxB] using hx
    · filter_upwards [ae_restrict_mem hball.measurableSet] with x hx
      have hp : (t, x) ∈ (Set.univ : Set ℝ) ×ˢ sourceBall (0 : PDE.Vec d) R :=
        ⟨Set.mem_univ _, hx⟩
      exact Set.indicator_of_mem hp G
  refine ⟨V, G, hVc, hV, hGm, hGL, hGs', hw, ?_⟩
  intro ψ hψ hc hs
  calc
    _ = ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (W t).val (some i) x))
          (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := htest ψ hψ hc hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hGs', ae_restrict_mem measurableSet_Ioo] with t ht htab
      have hball := ae_restrict_of_ae_restrict_of_subset (sourceBall_subset_cube R hR) ht
      apply integral_congr_ae
      filter_upwards [hball] with x hx
      rw [← hVW t ⟨htab.1.le, htab.2.le⟩, hx]

#print axioms spectral_heat_row_joint_gradient_iterated_test

/-- The same joint gradient satisfies the cylinder L² conditions and the
iterated spacetime test identity for the actual spectral row. -/
theorem spectral_heat_row_cylinder_iterated_test {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    let μ := (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      MemLp H 2 μ ∧ AEStronglyMeasurable G μ ∧
      MemLp (fun z => euclideanNorm (G z)) 2 μ ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) ∧
      ∀ ψ : ℝ × PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * H (t, x) * fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs, hw, ht⟩ :=
    spectral_heat_row_joint_gradient_iterated_test hd hκ h R hR s u hb hvar a b ha hab y hy
  have hle : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono le_rfl (Measure.restrict_mono (sourceBall_subset_cube R hR) le_rfl)
  exact ⟨G, spectral_heat_row_spacetime_memLp hd hκ h R hR s hs u hb hvar a b ha y hy,
    hGm.mono_measure hle, hGL.mono_measure hle, hw, ht⟩

#print axioms spectral_heat_row_cylinder_iterated_test

theorem spectral_heat_row_cylinder_iterated_test_with_zero_trace {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    let μ := (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      MemLp H 2 μ ∧ AEStronglyMeasurable G μ ∧
      MemLp (fun z => euclideanNorm (G z)) 2 μ ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => H (t, x)))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x)))) ∧
      ∀ ψ : ℝ × PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * H (t, x) * fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs, hw, ht⟩ :=
    spectral_heat_row_joint_gradient_iterated_test hd hκ h R hR s u hb hvar a b ha hab y hy
  have hle : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono le_rfl (Measure.restrict_mono (sourceBall_subset_cube R hR) le_rfl)
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  have hz := product_spatial_zeroExtension_weakGradient _ R hR V G hGs
  have hzero : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      EinsteinRelation.HasWeakGradient Set.univ
        ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
          Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
        ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x))) := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with t ht htab
    have he : (fun x => (V t).val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) := by
      apply hac.ae_le
      filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t),
        spectral_heat_row_Lp_ae_eq hd hκ h hR s t (lt_trans ha htab.1) y hy] with x hx hy'
      change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ (V t)) x = (V t).val none x at hx
      change (spectralHeatRow s t y) x = _ at hy'
      rw [hV t ⟨htab.1.le, htab.2.le⟩] at hx
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hx.symm.trans hy'
    have he' := (ae_eq_restrict_iff_indicator_ae_eq hball.measurableSet).mp he
    apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ ht
    · simpa only [Measure.restrict_univ, dirichletHilbertZeroExtension] using he'
    · apply ae_of_all
      intro x
      by_cases hx : x ∈ sourceBall (0 : PDE.Vec d) R <;>
        simp [Set.indicator, hx]
  exact ⟨G, spectral_heat_row_spacetime_memLp hd hκ h R hR s hs u hb hvar a b ha y hy,
    hGm.mono_measure hle, hGL.mono_measure hle, hw, hzero, ht⟩


#print axioms spectral_heat_row_cylinder_iterated_test_with_zero_trace

/-- The same cylinder gradient retains its native path and coordinate representative. -/
theorem spectral_heat_row_native_cylinder_with_zero_trace {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
      Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
    let μ := (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (fun x => G (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          (fun x i => (V t).val (some i) x)) ∧
      MemLp H 2 μ ∧ AEStronglyMeasurable G μ ∧
      MemLp (fun z => euclideanNorm (G z)) 2 μ ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient (sourceBall (0 : PDE.Vec d) R)
          (fun x => H (t, x)) (fun x => G (t, x))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => H (t, x)))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x)))) ∧
      ∀ ψ : ℝ × PDE.Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
        HasCompactSupport ψ → tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R →
        (∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          ρ x * H (t, x) * fderiv ℝ ψ (t, x) (1, 0)) =
        ∫ t in Set.Ioo a b, ∫ x in sourceBall (0 : PDE.Vec d) R,
          dot ((α x).mulVec (G (t, x)))
            (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1)) := by
  dsimp only
  obtain ⟨V, G, hVc, hV, hGm, hGL, hGs, hw, ht⟩ :=
    spectral_heat_row_joint_gradient_iterated_test hd hκ h R hR s u hb hvar a b ha hab y hy
  have hle : (volume : Measure (ℝ × PDE.Vec d)).restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R) ≤
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact Measure.prod_mono le_rfl (Measure.restrict_mono (sourceBall_subset_cube R hR) le_rfl)
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' h.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (h.2.2 x).1)).ne'
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  have hz := product_spatial_zeroExtension_weakGradient _ R hR V G hGs
  have hzero : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      EinsteinRelation.HasWeakGradient Set.univ
        ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
          Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
        ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x))) := by
    filter_upwards [hz, ae_restrict_mem measurableSet_Ioo] with t ht htab
    have he : (fun x => (V t).val none x) =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => ∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) := by
      apply hac.ae_le
      filter_upwards [dirichletHilbertInclusion_coe ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t),
        spectral_heat_row_Lp_ae_eq hd hκ h hR s t (lt_trans ha htab.1) y hy] with x hx hy'
      change (dirichletHilbertInclusion ρ R hR κ⁻¹ _ (V t)) x = (V t).val none x at hx
      change (spectralHeatRow s t y) x = _ at hy'
      rw [hV t ⟨htab.1.le, htab.2.le⟩] at hx
      simpa only [mul_comm, mul_left_comm, mul_assoc] using hx.symm.trans hy'
    have he' := (ae_eq_restrict_iff_indicator_ae_eq hball.measurableSet).mp he
    apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ ht
    · simpa only [Measure.restrict_univ, dirichletHilbertZeroExtension] using he'
    · apply ae_of_all
      intro x
      by_cases hx : x ∈ sourceBall (0 : PDE.Vec d) R <;>
        simp [Set.indicator, hx]
  exact ⟨V, G, hV, hGm, hGs, spectral_heat_row_spacetime_memLp hd hκ h R hR s hs u hb hvar a b ha y hy,
    hGm.mono_measure hle, hGL.mono_measure hle, hw, hzero, ht⟩


#print axioms spectral_heat_row_native_cylinder_with_zero_trace

/-- A smooth compact spacetime test has square-integrable directional
first derivatives on every restricted cylinder. -/
theorem spacetime_test_directional_derivative_memLp {d : ℕ}
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (v : ℝ × PDE.Vec d)
    (S : Set (ℝ × PDE.Vec d)) :
    MemLp (fun z => fderiv ℝ ψ z v) 2 (volume.restrict S) := by
  have hcont : Continuous (fun z => fderiv ℝ ψ z v) :=
    ((contDiff_infty_iff_fderiv.mp hψ).2.clm_apply contDiff_const).continuous
  exact (hcont.memLp_of_hasCompactSupport (hc.fderiv_apply ℝ v)).mono_measure
    Measure.restrict_le_self

#print axioms spacetime_test_directional_derivative_memLp

/-- The time term in the spacetime weak equation is integrable on the
actual cylinder, for any square-integrable row. -/
theorem spacetime_test_time_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (a b R : ℝ)
    (H : ℝ × PDE.Vec d → ℝ)
    (hH : MemLp H 2 (volume.restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)))
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun z => ρ z.2 * H z * fderiv ℝ ψ z (1, 0))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) := by
  have hρ : MemLp (fun z : ℝ × PDE.Vec d => ρ z.2) ⊤
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) := by
    apply memLp_top_of_bound (h.1.comp measurable_snd).aestronglyMeasurable κ⁻¹
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs]
      change |ρ z.2| ≤ κ⁻¹
      rw [abs_of_nonneg (hκ.le.trans (h.2.2 z.2).1)]
      exact (h.2.2 z.2).2.1
  have ht := spacetime_test_directional_derivative_memLp ψ hψ hc (1, 0)
    (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
  have hh := (hH.fun_mul (r := 2) hρ).integrable_mul ht
  apply hh.congr
  exact ae_of_all _ fun z => by dsimp; ring

#print axioms spacetime_test_time_integrable

/-- Each coordinate of a jointly measurable Euclidean L² gradient is L². -/
theorem spacetime_gradient_coordinate_memLp {d : ℕ}
    (μ : Measure (ℝ × PDE.Vec d)) (G : ℝ × PDE.Vec d → PDE.Vec d)
    (hG : AEStronglyMeasurable G μ)
    (hL : MemLp (fun z => euclideanNorm (G z)) 2 μ) (i : Fin d) :
    MemLp (fun z => G z i) 2 μ := by
  apply hL.mono' ((continuous_apply i).comp_aestronglyMeasurable hG)
  apply ae_of_all
  intro z
  simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
    (PiLp.norm_apply_le (WithLp.toLp 2 (G z)) i)

#print axioms spacetime_gradient_coordinate_memLp

/-- The spatial flux term is integrable on the same spacetime cylinder. -/
theorem spacetime_test_flux_integrable {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (a b R : ℝ)
    (G : ℝ × PDE.Vec d → PDE.Vec d)
    (hG : AEStronglyMeasurable G (volume.restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)))
    (hL : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict
      (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)))
    (ψ : ℝ × PDE.Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) :
    Integrable (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, Pi.single i 1)))
      (volume.restrict (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)) := by
  let μ := (volume : Measure (ℝ × PDE.Vec d)).restrict
    (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
  have hs : Integrable (fun z => ∑ i : Fin d, ∑ j : Fin d,
      α z.2 i j * G z j * fderiv ℝ ψ z (0, Pi.single i 1)) μ := by
    apply integrable_finsetSum Finset.univ
    intro i _
    apply integrable_finsetSum Finset.univ
    intro j _
    have hm : Measurable (fun z : ℝ × PDE.Vec d => α z.2 i j) := by
      let : MeasurableSpace (EinsteinRelation.Mat d) := EinsteinRelation.instMeasurableSpaceMat d
      let : BorelSpace (EinsteinRelation.Mat d) := EinsteinRelation.instBorelSpaceMat d
      exact ((((continuous_id : Continuous (id : EinsteinRelation.Mat d →
        EinsteinRelation.Mat d)).matrix_elem i j).measurable.comp h.2.1).comp measurable_snd)
    have ha : MemLp (fun z : ℝ × PDE.Vec d => α z.2 i j) ⊤ μ := by
      apply memLp_top_of_bound hm.aestronglyMeasurable κ⁻¹
      exact ae_of_all _ fun z => by
        rw [Real.norm_eq_abs]
        simpa only [dirichletValueGradientMatrix] using
          dirichletValueGradientMatrix_bound hκ h z.2 (some i) (some j)
    have hg := spacetime_gradient_coordinate_memLp μ G hG hL j
    have ht := spacetime_test_directional_derivative_memLp ψ hψ hc
      (0, Pi.single i 1) (Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R)
    apply ((hg.fun_mul (r := 2) ha).integrable_mul ht).congr
    exact ae_of_all _ fun z => by dsimp; ring
  simpa only [dot, Matrix.mulVec, dotProduct, Finset.sum_mul] using hs

#print axioms spacetime_test_flux_integrable

/-- The actual spectral heat row is weighted caloric on every positive strip. -/
theorem spectral_heat_row_weighted_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
        (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2 * s.eigenfunction i y) G := by
  let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
    Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
  obtain ⟨G, hH, hG, hL, hw, ht⟩ :=
    spectral_heat_row_cylinder_iterated_test hd hκ h R hR s hs u hb hvar a b ha hab y hy
  refine ⟨G, hH, hG, hL, hw, ?_⟩
  intro ψ hψ hc hsupport
  have hsupport' : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R := by
    simpa only [isOpen_Ioo.interior_eq] using hsupport
  have hiter := ht ψ hψ hc hsupport'
  have htime := spacetime_test_time_integrable hκ h a b R H hH ψ hψ hc
  have hflux := spacetime_test_flux_integrable hκ h a b R G hG hL ψ hψ hc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at htime hflux ⊢
  simp only [unitVector]
  change (∫ z, (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) z +
    (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, Pi.single i 1))) z ∂
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall (0 : PDE.Vec d) R))) = 0
  have heq : (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) =
      -(fun z => ρ z.2 * H z * fderiv ℝ ψ z (1, 0)) := by
    funext z
    simp only [Pi.neg_apply, neg_mul]
  rw [heq, integral_add htime.neg hflux]
  simp only [Pi.neg_apply, integral_neg]
  rw [← integral_integral (f := fun t x => ρ x * H (t, x) *
    fderiv ℝ ψ (t, x) (1, 0)) htime]
  rw [← integral_integral (f := fun t x => dot ((α x).mulVec (G (t, x)))
    (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1))) hflux]
  rw [hiter]
  exact neg_add_cancel _


theorem spectral_heat_row_weighted_caloric_with_zero_trace {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d,
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
        (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2 * s.eigenfunction i y) G ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x)))) := by
  let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
    Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
  obtain ⟨G, hH, hG, hL, hw, hzero, ht⟩ :=
    spectral_heat_row_cylinder_iterated_test_with_zero_trace hd hκ h R hR s hs u hb hvar a b ha hab y hy
  refine ⟨G, ⟨hH, hG, hL, hw, ?_⟩, hzero⟩
  intro ψ hψ hc hsupport
  have hsupport' : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R := by
    simpa only [isOpen_Ioo.interior_eq] using hsupport
  have hiter := ht ψ hψ hc hsupport'
  have htime := spacetime_test_time_integrable hκ h a b R H hH ψ hψ hc
  have hflux := spacetime_test_flux_integrable hκ h a b R G hG hL ψ hψ hc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at htime hflux ⊢
  simp only [unitVector]
  change (∫ z, (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) z +
    (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, Pi.single i 1))) z ∂
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall (0 : PDE.Vec d) R))) = 0
  have heq : (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) =
      -(fun z => ρ z.2 * H z * fderiv ℝ ψ z (1, 0)) := by
    funext z
    simp only [Pi.neg_apply, neg_mul]
  rw [heq, integral_add htime.neg hflux]
  simp only [Pi.neg_apply, integral_neg]
  rw [← integral_integral (f := fun t x => ρ x * H (t, x) *
    fderiv ℝ ψ (t, x) (1, 0)) htime]
  rw [← integral_integral (f := fun t x => dot ((α x).mulVec (G (t, x)))
    (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1))) hflux]
  rw [hiter]
  exact neg_add_cancel _


/-- The caloric and zero-trace gradient comes with its native spectral representative. -/
theorem spectral_heat_row_native_weighted_caloric_with_zero_trace {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        (fun x => G (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          (fun x i => (V t).val (some i) x)) ∧
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
        (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2 * s.eigenfunction i y) G ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x)))) := by
  let H : ℝ × PDE.Vec d → ℝ := fun z => ∑' i,
    Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y
  obtain ⟨V, G, hV, hGm, hGs, hH, hG, hL, hw, hzero, ht⟩ :=
    spectral_heat_row_native_cylinder_with_zero_trace hd hκ h R hR s hs u hb hvar a b ha hab y hy
  refine ⟨V, G, hV, hGm, hGs, ⟨hH, hG, hL, hw, ?_⟩, hzero⟩
  intro ψ hψ hc hsupport
  have hsupport' : tsupport ψ ⊆ Set.Ioo a b ×ˢ sourceBall (0 : PDE.Vec d) R := by
    simpa only [isOpen_Ioo.interior_eq] using hsupport
  have hiter := ht ψ hψ hc hsupport'
  have htime := spacetime_test_time_integrable hκ h a b R H hH ψ hψ hc
  have hflux := spacetime_test_flux_integrable hκ h a b R G hG hL ψ hψ hc
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at htime hflux ⊢
  simp only [unitVector]
  change (∫ z, (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) z +
    (fun z => dot ((α z.2).mulVec (G z))
      (fun i => fderiv ℝ ψ z (0, Pi.single i 1))) z ∂
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall (0 : PDE.Vec d) R))) = 0
  have heq : (fun z => -(ρ z.2 * H z) * fderiv ℝ ψ z (1, 0)) =
      -(fun z => ρ z.2 * H z * fderiv ℝ ψ z (1, 0)) := by
    funext z
    simp only [Pi.neg_apply, neg_mul]
  rw [heq, integral_add htime.neg hflux]
  simp only [Pi.neg_apply, integral_neg]
  rw [← integral_integral (f := fun t x => ρ x * H (t, x) *
    fderiv ℝ ψ (t, x) (1, 0)) htime]
  rw [← integral_integral (f := fun t x => dot ((α x).mulVec (G (t, x)))
    (fun i => fderiv ℝ ψ (t, x) (0, Pi.single i 1))) hflux]
  rw [hiter]
  exact neg_add_cancel _


#print axioms spectral_heat_row_native_weighted_caloric_with_zero_trace

/-- Native spectral paths on overlapping strips have the same coordinate
representatives almost everywhere on each common time slice. -/
theorem spectral_heat_row_native_gradient_overlap {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (a b c e : ℝ)
    (V W : ℝ → DirichletHilbertSpace (d := d) R hR)
    (G H : ℝ × PDE.Vec d → PDE.Vec d)
    (hV : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y)
    (hW : ∀ t ∈ Set.Icc c e, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (W t) = spectralHeatRow s t y)
    (hG : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V t).val (some i) x))
    (hH : ∀ᵐ t ∂volume.restrict (Set.Ioo c e),
      (fun x => H (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (W t).val (some i) x)) :
    ∀ᵐ t ∂volume.restrict (Set.Ioo a b ∩ Set.Ioo c e),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x => H (t, x)) := by
  have hG' := ae_restrict_of_ae_restrict_of_subset
    (show Set.Ioo a b ∩ Set.Ioo c e ⊆ Set.Ioo a b from Set.inter_subset_left) hG
  have hH' := ae_restrict_of_ae_restrict_of_subset
    (show Set.Ioo a b ∩ Set.Ioo c e ⊆ Set.Ioo c e from Set.inter_subset_right) hH
  filter_upwards [hG', hH', ae_restrict_mem (measurableSet_Ioo.inter measurableSet_Ioo)]
    with t hGt hHt ht
  have hVW : V t = W t := by
    apply injective_dirichletHilbertInclusion hκ h R hR
    exact (hV t ⟨ht.1.1.le, ht.1.2.le⟩).trans
      (hW t ⟨ht.2.1.le, ht.2.2.le⟩).symm
  rw [hVW] at hGt
  exact hGt.trans hHt.symm

#print axioms spectral_heat_row_native_gradient_overlap

/-- Every positive finite interval lies in one strip of the standard exhaustion. -/
theorem positive_time_interval_in_exhaustion (a b : ℝ) (ha : 0 < a) :
    ∃ n : ℕ, Set.Ioo a b ⊆ Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max b (1 / a))
  have hb : b < (n : ℝ) + 2 := by
    have := lt_of_le_of_lt (le_max_left b (1 / a)) hn
    linarith
  have hi : 1 / a < (n : ℝ) + 2 := by
    have := lt_of_le_of_lt (le_max_right b (1 / a)) hn
    linarith
  have hp : 0 < (n : ℝ) + 2 := by positivity
  have hlo : 1 / ((n : ℝ) + 2) < a := (one_div_lt hp ha).2 hi
  exact ⟨n, fun _ ht => ⟨lt_trans hlo ht.1, lt_trans ht.2 hb⟩⟩

/-- Choose the native caloric and zero-trace representatives on all exhaustion strips. -/
theorem spectral_heat_row_exhaustion_native_gradients {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ (V : ℕ → ℝ → DirichletHilbertSpace (d := d) R hR)
      (G : ℕ → ℝ × PDE.Vec d → PDE.Vec d), ∀ n : ℕ,
      (∀ t ∈ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
          (V n t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable (G n) ((volume.restrict
        (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
        (fun x => G n (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          (fun x i => (V n t).val (some i) x)) ∧
      IsWeightedCaloric ρ α (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))
        (sourceBall (0 : PDE.Vec d) R) (fun z => ∑' i,
          Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 *
            s.eigenfunction i y) (G n) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G n (t, x)))) := by
  have hex : ∀ n : ℕ, ∃ (V : ℝ → DirichletHilbertSpace (d := d) R hR)
      (G : ℝ × PDE.Vec d → PDE.Vec d),
      (∀ t ∈ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
          (V t) = spectralHeatRow s t y) ∧
      AEStronglyMeasurable G ((volume.restrict
        (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))) ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
        (fun x => G (t, x)) =ᵐ[volume.restrict
          ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
            (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
          (fun x i => (V t).val (some i) x)) ∧
      IsWeightedCaloric ρ α (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))
        (sourceBall (0 : PDE.Vec d) R) (fun z => ∑' i,
          Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 *
            s.eigenfunction i y) G ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x)))) := by
    intro n
    have hp : 0 < (n : ℝ) + 2 := by positivity
    have ha : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hab : 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
      apply (one_div_lt hp hp).2
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : 1 / ((n : ℝ) + 2) ≤ (1 : ℝ) := by
        apply (div_le_one hp).2
        linarith
      linarith
    exact spectral_heat_row_native_weighted_caloric_with_zero_trace hd hκ h R hR s hs u
      hb hvar _ _ ha hab y hy
  choose V G hVG using hex
  exact ⟨V, G, hVG⟩

/-- A nonpositive time or a strip containing the time always exists. -/
theorem positive_time_strip_exists (t : ℝ) : ∃ n : ℕ,
    t ≤ 0 ∨ t ∈ Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) := by
  by_cases ht : 0 < t
  · obtain ⟨n, hn⟩ := positive_time_interval_in_exhaustion (t / 2) (2 * t) (by linarith)
    exact ⟨n, Or.inr (hn ⟨by linarith, by linarith⟩)⟩
  · exact ⟨0, Or.inl (le_of_not_gt ht)⟩

/-- Select the first exhaustion strip containing a positive time. -/
noncomputable def positiveTimeStripIndex (t : ℝ) : ℕ :=
  Nat.find (positive_time_strip_exists t)

theorem positive_time_strip_index_mem (t : ℝ) (ht : 0 < t) :
    t ∈ Set.Ioo (1 / ((positiveTimeStripIndex t : ℝ) + 2))
      ((positiveTimeStripIndex t : ℝ) + 2) := by
  rcases Nat.find_spec (positive_time_strip_exists t) with h | h
  · exact (not_le_of_gt ht h).elim
  · exact h

theorem measurable_positive_time_strip_index : Measurable positiveTimeStripIndex := by
  classical
  apply measurable_find
  intro n
  change MeasurableSet (Set.Iic (0 : ℝ) ∪
    Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))
  exact measurableSet_Iic.union measurableSet_Ioo

/-- The selected gradient agrees on almost every slice with each strip gradient.
The overlap agreement is derived from the native spectral paths. -/
theorem spectral_heat_row_selected_gradient_slices {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (V : ℕ → ℝ → DirichletHilbertSpace (d := d) R hR)
    (G : ℕ → ℝ × PDE.Vec d → PDE.Vec d)
    (hV : ∀ n : ℕ, ∀ t ∈ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        (V n t) = spectralHeatRow s t y)
    (hG : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict
        (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
      (fun x => G n (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V n t).val (some i) x)) :
    ∀ n : ℕ, ∀ᵐ t ∂volume.restrict
        (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
      (fun x => G (positiveTimeStripIndex t) (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x => G n (t, x)) := by
  intro n
  have hh : ∀ m : ℕ, ∀ᵐ t ∂volume.restrict
      (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
      t ∈ Set.Ioo (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2) →
      (fun x => G m (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x => G n (t, x)) := by
    intro m
    have hmn := spectral_heat_row_native_gradient_overlap hκ h R hR s y
      (1 / ((m : ℝ) + 2)) ((m : ℝ) + 2) (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)
      (V m) (V n) (G m) (G n) (hV m) (hV n) (hG m) (hG n)
    apply (ae_restrict_iff' measurableSet_Ioo).1
    simpa only [Measure.restrict_restrict measurableSet_Ioo] using hmn
  filter_upwards [ae_all_iff.2 hh, ae_restrict_mem measurableSet_Ioo] with t ht hn
  have htpos : 0 < t := lt_trans (by positivity) hn.1
  exact ht (positiveTimeStripIndex t) (positive_time_strip_index_mem t htpos)

/-- Slice-wise equality lifts to product equality for almost-everywhere strongly
measurable fields. -/
theorem ae_eq_prod_of_ae_eq_slices {d : ℕ} (μ : Measure ℝ)
    (ν : Measure (PDE.Vec d)) [SFinite ν]
    (f g : ℝ × PDE.Vec d → PDE.Vec d)
    (hf : AEStronglyMeasurable f (μ.prod ν))
    (hg : AEStronglyMeasurable g (μ.prod ν))
    (hs : ∀ᵐ t ∂μ, (fun x => f (t, x)) =ᵐ[ν] (fun x => g (t, x))) :
    f =ᵐ[μ.prod ν] g := by
  have hfm := Measure.ae_ae_of_ae_prod hf.ae_eq_mk
  have hgm := Measure.ae_ae_of_ae_prod hg.ae_eq_mk
  have hmk : hf.mk f =ᵐ[μ.prod ν] hg.mk g := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      hf.stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable)).2
    filter_upwards [hfm, hgm, hs] with t hft hgt hst
    filter_upwards [hft, hgt, hst] with x hfx hgx hsx
    exact hfx.symm.trans (hsx.trans hgx)
  exact hf.ae_eq_mk.trans (hmk.trans hg.ae_eq_mk.symm)

/-- Native strip gradients coincide almost everywhere on each product overlap. -/
theorem spectral_heat_row_native_gradient_overlap_prod {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (a b c e : ℝ)
    (V W : ℝ → DirichletHilbertSpace (d := d) R hR)
    (G H : ℝ × PDE.Vec d → PDE.Vec d)
    (hV : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (V t) = spectralHeatRow s t y)
    (hW : ∀ t ∈ Set.Icc c e, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (W t) = spectralHeatRow s t y)
    (hG : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => G (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V t).val (some i) x))
    (hH : ∀ᵐ t ∂volume.restrict (Set.Ioo c e),
      (fun x => H (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (W t).val (some i) x))
    (hGm : AEStronglyMeasurable G ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))))
    (hHm : AEStronglyMeasurable H ((volume.restrict (Set.Ioo c e)).prod
      (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))))) :
    G =ᵐ[(volume.restrict (Set.Ioo a b ∩ Set.Ioo c e)).prod
      (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))] H := by
  apply ae_eq_prod_of_ae_eq_slices
  · exact hGm.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Set.inter_subset_left le_rfl) le_rfl)
  · exact hHm.mono_measure (Measure.prod_mono
      (Measure.restrict_mono Set.inter_subset_right le_rfl) le_rfl)
  · exact spectral_heat_row_native_gradient_overlap hκ h R hR s y a b c e V W G H
      hV hW hG hH

/-- Countable product overlap agreement identifies the selected gradient on any
positive time interval. -/
theorem positive_time_selected_product_eq {d : ℕ} (ν : Measure (PDE.Vec d))
    [SFinite ν] (a b : ℝ) (ha : 0 < a)
    (G : ℕ → ℝ × PDE.Vec d → PDE.Vec d) (H : ℝ × PDE.Vec d → PDE.Vec d)
    (h : ∀ n : ℕ, G n =ᵐ[(volume.restrict
      (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ∩ Set.Ioo a b)).prod ν] H) :
    (fun z => G (positiveTimeStripIndex z.1) z) =ᵐ[
      (volume.restrict (Set.Ioo a b)).prod ν] H := by
  have hh : ∀ n : ℕ, ∀ᵐ z ∂(volume.restrict (Set.Ioo a b)).prod ν,
      z.1 ∈ Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) → G n z = H z := by
    intro n
    have ht : ∀ᵐ z ∂((volume.restrict (Set.Ioo a b)).prod ν).restrict
        (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ
          (Set.univ : Set (PDE.Vec d))), G n z = H z := by
      rw [← Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict measurableSet_Ioo]
      exact h n
    have ht' := (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).1 ht
    filter_upwards [ht'] with z hz hzmem
    exact hz ⟨hzmem, Set.mem_univ _⟩
  have hpos : ∀ᵐ z ∂(volume.restrict (Set.Ioo a b)).prod ν, 0 < z.1 := by
    rw [Measure.restrict_prod_eq_prod_univ]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with z hz
    exact lt_trans ha hz.1.1
  filter_upwards [ae_all_iff.2 hh, hpos] with z hz hp
  exact hz (positiveTimeStripIndex z.1) (positive_time_strip_index_mem z.1 hp)

/-- The selected exhaustion gradient agrees with a native gradient on any
positive interval, almost everywhere on the interval and spatial cube. -/
theorem spectral_heat_row_selected_gradient_product {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (y : PDE.Vec d) (a b : ℝ) (ha : 0 < a)
    (V : ℕ → ℝ → DirichletHilbertSpace (d := d) R hR)
    (G : ℕ → ℝ × PDE.Vec d → PDE.Vec d)
    (W : ℝ → DirichletHilbertSpace (d := d) R hR)
    (H : ℝ × PDE.Vec d → PDE.Vec d)
    (hV : ∀ n : ℕ, ∀ t ∈ Set.Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2),
      dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
        (V n t) = spectralHeatRow s t y)
    (hW : ∀ t ∈ Set.Icc a b, dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (W t) = spectralHeatRow s t y)
    (hG : ∀ n : ℕ, ∀ᵐ t ∂volume.restrict
      (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2)),
      (fun x => G n (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (V n t).val (some i) x))
    (hH : ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
      (fun x => H (t, x)) =ᵐ[volume.restrict
        ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))]
        (fun x i => (W t).val (some i) x))
    (hGm : ∀ n : ℕ, AEStronglyMeasurable (G n) ((volume.restrict
      (Set.Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2))).prod
      (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))))
    (hHm : AEStronglyMeasurable H ((volume.restrict (Set.Ioo a b)).prod
      (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
        (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))))) :
    (fun z => G (positiveTimeStripIndex z.1) z) =ᵐ[
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d)))] H := by
  apply positive_time_selected_product_eq _ a b ha G H
  intro n
  exact spectral_heat_row_native_gradient_overlap_prod hκ h R hR s y
    (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) a b (V n) W (G n) H
    (hV n) hW (hG n) hH (hGm n) hHm

/-- Caloricity and zero trace are unchanged by replacing the gradient almost
 everywhere on the spacetime cylinder. -/
theorem weighted_caloric_zero_trace_congr {d : ℕ} (ρ : PDE.Vec d → ℝ)
    (α : PDE.Vec d → EinsteinRelation.Mat d) (I : Set ℝ) (U : Set (PDE.Vec d))
    (hU : IsOpen U) (u : ℝ × PDE.Vec d → ℝ)
    (G H : ℝ × PDE.Vec d → PDE.Vec d)
    (hcal : IsWeightedCaloric ρ α I U u G)
    (hzero : ∀ᵐ t ∂volume.restrict I,
      EinsteinRelation.HasWeakGradient Set.univ (U.indicator (fun x => u (t, x)))
        (U.indicator (fun x => G (t, x))))
    (he : G =ᵐ[(volume.restrict I).prod (volume.restrict U)] H) :
    IsWeightedCaloric ρ α I U u H ∧
      ∀ᵐ t ∂volume.restrict I,
        EinsteinRelation.HasWeakGradient Set.univ (U.indicator (fun x => u (t, x)))
          (U.indicator (fun x => H (t, x))) := by
  have he' : G =ᵐ[volume.restrict (I ×ˢ U)] H := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact he
  have hs := Measure.ae_ae_of_ae_prod he
  rcases hcal with ⟨hu, hm, hl, hw, ht⟩
  constructor
  · refine ⟨hu, hm.congr he', (memLp_congr_ae (he'.mono fun z hz => congrArg euclideanNorm hz)).1 hl, ?_, ?_⟩
    · filter_upwards [hw, hs] with t hwt hst
      exact EinsteinRelation.Correctors.hasWeakGradient_congr_ae hU hwt (ae_eq_refl _) hst
    · intro ψ hψ hc hsupport
      calc
        (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (H z))
              (fun j => fderiv ℝ ψ z (0, unitVector j))) =
            (∫ z in I ×ˢ U, -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
              dot ((α z.2).mulVec (G z))
                (fun j => fderiv ℝ ψ z (0, unitVector j))) := by
          apply integral_congr_ae
          filter_upwards [he'] with z hz
          rw [hz]
        _ = 0 := ht ψ hψ hc hsupport
  · filter_upwards [hzero, hs] with t hzt hst
    have hind := (ae_eq_restrict_iff_indicator_ae_eq hU.measurableSet).mp hst
    apply EinsteinRelation.Correctors.hasWeakGradient_congr_ae isOpen_univ hzt
    · exact ae_eq_refl _
    · simpa only [Measure.restrict_univ] using hind

/-- A single spectral gradient works on every positive finite time strip. -/
theorem spectral_heat_row_all_positive_strips {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (y : PDE.Vec d) (hy : y ∈ sourceBall 0 R) :
    ∃ G : ℝ × PDE.Vec d → PDE.Vec d, ∀ a b : ℝ, 0 < a → a < b →
      IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
        (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
          s.eigenfunction i z.2 * s.eigenfunction i y) G ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        EinsteinRelation.HasWeakGradient Set.univ
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
            Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
          ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G (t, x))) := by
  obtain ⟨V, G, hVG⟩ :=
    spectral_heat_row_exhaustion_native_gradients hd hκ h R hR s hs u hb hvar y hy
  refine ⟨fun z => G (positiveTimeStripIndex z.1) z, ?_⟩
  intro a b ha hab
  obtain ⟨W, H, hW, hHm, hHs, hcal, hzero⟩ :=
    spectral_heat_row_native_weighted_caloric_with_zero_trace hd hκ h R hR s hs u
      hb hvar a b ha hab y hy
  have he := spectral_heat_row_selected_gradient_product hκ h R hR s y a b ha
    V G W H (fun n => (hVG n).1) hW (fun n => (hVG n).2.2.1) hHs
    (fun n => (hVG n).2.1) hHm
  have hle : (volume.restrict (Set.Ioo a b)).prod
      (volume.restrict (sourceBall (0 : PDE.Vec d) R)) ≤
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict ((SubdiffusiveProcess.centeredCube (0 : PDE.Vec d)
          (2 * R) (mul_pos two_pos hR)) : Set (PDE.Vec d))) :=
    Measure.prod_mono le_rfl (Measure.restrict_mono (sourceBall_subset_cube R hR) le_rfl)
  have hball : IsOpen (sourceBall (0 : PDE.Vec d) R) :=
    (dirichletBall (d := d) R).isOpen
  have heball : (fun z => G (positiveTimeStripIndex z.1) z) =ᵐ[
      (volume.restrict (Set.Ioo a b)).prod
        (volume.restrict (sourceBall (0 : PDE.Vec d) R))] H :=
    (Measure.absolutelyContinuous_of_le hle).ae_le he
  exact weighted_caloric_zero_trace_congr ρ α _ _ hball _ H _ hcal hzero heball.symm

/-- One gradient, indexed by the source point, serves all positive strips. -/
theorem spectral_heat_global_positive_strip_gradient {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (hs : Tendsto s.eigenvalue atTop atTop)
    (u : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (u n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (u n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    ∃ G : ℝ → PDE.Vec d → PDE.Vec d → PDE.Vec d,
      ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
        IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2 * s.eigenfunction i y) (fun z => G z.1 z.2 y) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          EinsteinRelation.HasWeakGradient Set.univ
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
              Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G t x y)) := by
  classical
  refine ⟨fun t x y => if hy : y ∈ sourceBall (0 : PDE.Vec d) R then
    Classical.choose (spectral_heat_row_all_positive_strips hd hκ h R hR s hs u hb hvar y hy)
      (t, x) else 0, ?_⟩
  intro y hy a b ha hab
  simpa only [dite_eq_left hy] using
    (Classical.choose_spec (spectral_heat_row_all_positive_strips hd hκ h R hR s hs u
      hb hvar y hy)) a b ha hab

/-- The original coefficients supply one spectrum and one gradient valid on
all positive finite strips. -/
theorem exists_sourceBall_spectral_global_positive_strip_gradient {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → PDE.Vec d → PDE.Vec d → PDE.Vec d),
      ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
        IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2 * s.eigenfunction i y) (fun z => G z.1 z.2 y) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          EinsteinRelation.HasWeakGradient Set.univ
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
              Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G t x y)) := by
  obtain ⟨s, u, hs, hb, hvar, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ h R hR s hs u hb hvar
  exact ⟨s, G, hG⟩

/-- One actual spectrum and one gradient give nonnegativity, zero boundary
values, and the caloric equation on every positive strip. -/
theorem exists_sourceBall_spectral_nonneg_zero_boundary_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → PDE.Vec d → PDE.Vec d → PDE.Vec d),
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : PDE.Vec d) R,
        ∀ y ∈ sourceBall (0 : PDE.Vec d) R,
          0 ≤ ∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) ∧
      (∀ t : ℝ, ∀ x ∈ frontier (sourceBall (0 : PDE.Vec d) R),
        ∀ y : PDE.Vec d, (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) = 0) ∧
      ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
        IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2 * s.eigenfunction i y) (fun z => G z.1 z.2 y) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          EinsteinRelation.HasWeakGradient Set.univ
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
              Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G t x y)) := by
  obtain ⟨s, u, hs, hb, hvar, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ h R hR s hs u hb hvar
  refine ⟨s, G, ?_, ?_, hG⟩
  · intro t ht x hx y hy
    simpa only [Real.coe_toNNReal _ ht.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hvar).2
        t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) x hx y hy
  · intro t x hx y
    simp only [s.boundary_zero _ x hx, mul_zero, zero_mul, tsum_zero]

#print axioms exists_sourceBall_spectral_nonneg_zero_boundary_caloric

/-- Continuity and the caloric properties hold for one spectrum and one gradient. -/
theorem exists_sourceBall_spectral_continuous_nonneg_zero_boundary_caloric {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → PDE.Vec d → PDE.Vec d → PDE.Vec d),
      (∀ y ∈ sourceBall (0 : PDE.Vec d) R,
        ContinuousOn (fun z : ℝ × PDE.Vec d => ∑' i,
          Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y)
          (Set.Ioi 0 ×ˢ closure (sourceBall (0 : PDE.Vec d) R))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : PDE.Vec d) R,
        ∀ y ∈ sourceBall (0 : PDE.Vec d) R,
          0 ≤ ∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) ∧
      (∀ t : ℝ, ∀ x ∈ frontier (sourceBall (0 : PDE.Vec d) R),
        ∀ y : PDE.Vec d, (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) = 0) ∧
      ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
        IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2 * s.eigenfunction i y) (fun z => G z.1 z.2 y) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          EinsteinRelation.HasWeakGradient Set.univ
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
              Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G t x y)) := by
  obtain ⟨s, u, hs, hb, hvar, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ h R hR s hs u hb hvar
  refine ⟨s, G, ?_, ?_, ?_, hG⟩
  · intro y hy
    exact spectral_heat_row_continuousOn_closedBall hd hκ h hR s hs y hy
  · intro t ht x hx y hy
    simpa only [Real.coe_toNNReal _ ht.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hvar).2
        t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) x hx y hy
  · intro t x hx y
    simp only [s.boundary_zero _ x hx, mul_zero, zero_mul, tsum_zero]

#print axioms exists_sourceBall_spectral_continuous_nonneg_zero_boundary_caloric

/-- One native spectrum and gradient also provide closed-ball weighted row actions. -/
theorem exists_sourceBall_spectral_caloric_closedBall_row_action {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) :
    ∃ (s : DirichletSpectralResolution ρ α R)
      (G : ℝ → PDE.Vec d → PDE.Vec d → PDE.Vec d),
      ((∀ y ∈ sourceBall (0 : PDE.Vec d) R,
        ContinuousOn (fun z : ℝ × PDE.Vec d => ∑' i,
          Real.exp (-s.eigenvalue i * z.1) * s.eigenfunction i z.2 * s.eigenfunction i y)
          (Set.Ioi 0 ×ˢ closure (sourceBall (0 : PDE.Vec d) R))) ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : PDE.Vec d) R,
        ∀ y ∈ sourceBall (0 : PDE.Vec d) R,
          0 ≤ ∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) ∧
      (∀ t : ℝ, ∀ x ∈ frontier (sourceBall (0 : PDE.Vec d) R),
        ∀ y : PDE.Vec d, (∑' i, Real.exp (-s.eigenvalue i * t) *
          s.eigenfunction i x * s.eigenfunction i y) = 0) ∧
      ∀ y ∈ sourceBall (0 : PDE.Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
        IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall (0 : PDE.Vec d) R)
          (fun z => ∑' i, Real.exp (-s.eigenvalue i * z.1) *
            s.eigenfunction i z.2 * s.eigenfunction i y) (fun z => G z.1 z.2 y) ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
          EinsteinRelation.HasWeakGradient Set.univ
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => ∑' i,
              Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y))
            ((sourceBall (0 : PDE.Vec d) R).indicator (fun x => G t x y))) ∧
      ∀ t : ℝ, 0 < t →
        ContinuousOn (spectralHeatRow s t) (closure (sourceBall 0 R)) ∧
        (∀ x ∈ frontier (sourceBall 0 R), spectralHeatRow s t x = 0) ∧
        ∀ f : Lp ℝ 2 (dirichletVolume ρ R),
          ContinuousOn (fun x => ∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
            s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R)
            (closure (sourceBall 0 R)) ∧
          ∀ x ∈ frontier (sourceBall 0 R),
            (∫ y, (∑' i, Real.exp (-s.eigenvalue i * t) *
              s.eigenfunction i x * s.eigenfunction i y) * f y ∂dirichletVolume ρ R) = 0 := by
  obtain ⟨s, u, hs, hb, hvar, _⟩ :=
    exists_sourceBall_spectral_heat_native_lift hd hκ h R hR
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ h R hR s hs u hb hvar
  refine ⟨s, G, ⟨?_, ?_, ?_, hG⟩, ?_⟩
  · intro y hy
    exact spectral_heat_row_continuousOn_closedBall hd hκ h hR s hs y hy
  · intro t ht x hx y hy
    simpa only [Real.coe_toNNReal _ ht.le] using
      (spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs u hb hvar).2
        t.toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) x hx y hy
  · intro t x hx y
    simp only [s.boundary_zero _ x hx, mul_zero, zero_mul, tsum_zero]

  · intro t ht
    exact ⟨spectral_heat_row_continuousOn_closedBall_Lp hd hκ h hR s hs t ht,
      fun x hx => spectral_heat_row_zero_frontier s t x hx,
      fun f => ⟨spectral_heat_action_continuousOn_closedBall hd hκ h hR s hs t ht f,
        fun x hx => spectral_heat_action_zero_frontier s t f x hx⟩⟩

#print axioms exists_sourceBall_spectral_caloric_closedBall_row_action


#print axioms exists_sourceBall_spectral_global_positive_strip_gradient

#print axioms spectral_heat_global_positive_strip_gradient

#print axioms spectral_heat_row_all_positive_strips

#print axioms weighted_caloric_zero_trace_congr

#print axioms spectral_heat_row_selected_gradient_product

#print axioms positive_time_selected_product_eq

#print axioms ae_eq_prod_of_ae_eq_slices
#print axioms spectral_heat_row_native_gradient_overlap_prod

#print axioms positive_time_strip_exists
#print axioms positive_time_strip_index_mem
#print axioms measurable_positive_time_strip_index
#print axioms spectral_heat_row_selected_gradient_slices

#print axioms positive_time_interval_in_exhaustion
#print axioms spectral_heat_row_exhaustion_native_gradients


#print axioms spectral_heat_row_weighted_caloric_with_zero_trace

#print axioms spectral_heat_row_weighted_caloric

#print axioms spectral_heat_row_spacetime_iterated_test

#print axioms spectral_heat_row_spacetime_slice_pairings

#print axioms spacetime_test_native_slice_representatives

#print axioms spectral_heat_row_native_spacetime_test

#print axioms spacetime_test_native_c1_paths

#print axioms spacetime_test_native_time_derivative_continuous

#print axioms spacetime_test_native_hasDerivAt

#print axioms spacetime_test_native_uniform_remainder

#print axioms spacetime_test_slice_fderiv

#print axioms spacetime_test_spatial_uniform_time_remainder

#print axioms spacetime_test_uniform_time_remainder

#print axioms spacetime_test_spatial_derivative_time

#print axioms spacetime_test_directional_derivative_uniform_time

#print axioms spacetime_test_native_paired_paths

#print axioms spacetime_test_native_path_tsupport

#print axioms spacetime_test_time_derivative

#print axioms spacetime_test_spatial_slices

#print axioms spectral_heat_row_native_compact_path_time_test

#print axioms spectral_heat_row_native_path_time_test

#print axioms spectral_heat_row_native_path_derivative

#print axioms hasDerivAt_weak_functional_apply

#print axioms spectral_heat_row_separated_test_cylinder


/-- The structural ground mode and rank-one minimum projection for a supplied
native spectral resolution. -/
theorem exists_interior_ground_data_for_spectrum {d : ℕ}
    (hd : 2 ≤ d) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R) :
    ∃ E r a : ℝ, 0 < E ∧ 0 < r ∧ r < R ∧ 0 < a ∧
    ∀ {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d},
    ∀ (hell : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
    Tendsto s.eigenvalue atTop atTop →
    (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (hell.2.2 x).2.1) (vs n)) →
    (∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      s.eigenvalue n * inner ℝ (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)) →
    ∃ (eig δ : ℝ) (S : Finset ℕ)
      (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
      (g : Lp ℝ 2 (dirichletVolume ρ R)),
      0 < eig ∧ eig ≤ E ∧ 0 < δ ∧
      (∀ n, n ∈ S ↔ s.eigenvalue n = eig) ∧
      (∀ n, s.eigenvalue n = eig ∨ eig + δ ≤ s.eigenvalue n) ∧
      (∀ x, 0 ≤ u.toH1Function.toFun x) ∧
      (∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
        a ≤ u.toH1Function.toFun x) ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun ∧
      ‖g‖ = 1 ∧
      (∀ f, (∑ n ∈ S, (spectralHeatBasis s).repr f n • spectralHeatBasis s n) =
        inner ℝ f g • g) := by
  classical
  obtain ⟨E, K, r, a, hE, hK, hr, hrR, ha, hex⟩ :=
    exists_sourceBall_first_eigenfunction_uniform_interior_lower hd hκ hR
  refine ⟨E, r, a, hE, hr, hrR, ha, ?_⟩
  intro ρ α hell s vs hlim hb hvar
  obtain ⟨eig, u, heig, heE, hu0, hnorm, henergy, hmin, hweak, hub, hlower⟩ := hex hell
  obtain ⟨j, hj, δ, hδ, hgap⟩ := spectral_minimum_and_gap s.eigenvalue hlim
  have hnorm' : (∫ x in sourceBall (0 : PDE.Vec d) R,
      ρ x * u.toH1Function.toFun x * u.toH1Function.toFun x) = 1 := by
    simpa only [weightedL2Pairing] using hnorm
  have hmin' : ∀ w : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R),
      eig * (∫ x in sourceBall (0 : PDE.Vec d) R,
        ρ x * w.toH1Function.toFun x * w.toH1Function.toFun x) ≤
      ∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (w.toH1Function.grad x)) (w.toH1Function.grad x) := by
    simpa only [weightedL2Pairing, dirichletEnergyPairing, PDE.vecDot,
      PDE.matVecMul, Matrix.mulVec, dotProduct, dot] using hmin
  obtain ⟨v, hv, ⟨n, hn⟩, hsupport⟩ :=
    native_weakEigenfunction_spectral_coordinate hd hκ hell R hR s.eigenvalue vs
      (spectralHeatBasis s) hb hvar u eig hweak hnorm'
  have hneig : s.eigenvalue n = eig := by
    by_contra hne
    exact hn (hsupport n hne)
  have heq : s.eigenvalue j = eig := le_antisymm ((hj n).trans_eq hneig)
    (native_rayleigh_lower_le_spectral_value hκ hell R hR s.eigenvalue vs
      (spectralHeatBasis s) hb hvar eig hmin' j)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.1 hlim) (eig + 1))
  let S := (Finset.range N).filter (fun n => s.eigenvalue n = eig)
  have hS (n : ℕ) : n ∈ S ↔ s.eigenvalue n = eig := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact And.right
    · intro hn
      refine ⟨?_, hn⟩
      by_contra h
      have hh := hN n (Nat.le_of_not_gt h)
      linarith
  obtain ⟨g, hgu, hgnorm, hproj⟩ := sourceBall_complete_minimum_projection_rank_one
    hd hκ hR ρ α hell s.eigenvalue vs (spectralHeatBasis s) hb hvar S eig heig.le
    hS u hweak hmin hnorm
  refine ⟨eig, δ, S, u, g, heig, heE, hδ, hS, ?_, hu0, hlower, hgu, hgnorm, hproj⟩
  simpa only [heq] using hgap

#print axioms exists_interior_ground_data_for_spectrum


/-- A finite spectral projection has its canonical continuous representative,
with zero trace and the actual weighted almost-everywhere identity. -/
theorem spectral_finite_projection_representative {d : ℕ}
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R) (S : Finset ℕ)
    (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    let φ : PDE.Vec d → ℝ := fun x =>
      ∑ i ∈ S, (spectralHeatBasis s).repr f i * s.eigenfunction i x
    ContinuousOn φ (closure (sourceBall 0 R)) ∧
      (∀ x ∈ frontier (sourceBall 0 R), φ x = 0) ∧
      ((∑ i ∈ S, (spectralHeatBasis s).repr f i • spectralHeatBasis s i :
        Lp ℝ 2 (dirichletVolume ρ R)) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] φ := by
  classical
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · apply continuousOn_finsetSum
    intro i hi
    exact (s.continuous i).const_mul _
  · intro x hx
    apply Finset.sum_eq_zero
    intro i hi
    rw [s.boundary_zero i x hx, mul_zero]
  · have hb (i : ℕ) : spectralHeatBasis s i =
        (s.square_integrable i).toLp (s.eigenfunction i) := by
      exact congrFun (HilbertBasis.coe_mk s.orthonormal
        (le_of_eq (Submodule.dense_iff_topologicalClosure_eq_top.mp s.complete).symm)) i
    filter_upwards [Lp.coeFn_fun_finsetSum S
        (fun i => (spectralHeatBasis s).repr f i • spectralHeatBasis s i),
      ae_all_iff.mpr (fun i => Lp.coeFn_smul ((spectralHeatBasis s).repr f i)
        (spectralHeatBasis s i)),
      ae_all_iff.mpr (fun i => (s.square_integrable i).coeFn_toLp)] with x hx hy hz
    rw [hx]
    apply Finset.sum_congr rfl
    intro i hi
    have hmode : (spectralHeatBasis s i : PDE.Vec d → ℝ) x = s.eigenfunction i x := by
      rw [hb]
      exact hz i
    simpa only [Pi.smul_apply, smul_eq_mul, hmode] using hy i

#print axioms spectral_finite_projection_representative


/-- A continuous function on an open set inherits a Lebesgue almost-everywhere
lower bound at every point of that set. -/
theorem continuousOn_le_of_ae_restrict {d : ℕ}
    {U : Set (PDE.Vec d)} (hU : IsOpen U) {f : PDE.Vec d → ℝ} {a : ℝ}
    (hf : ContinuousOn f U) (ha : ∀ᵐ x ∂volume.restrict U, a ≤ f x) :
    ∀ x ∈ U, a ≤ f x := by
  have heq : f =ᵐ[volume.restrict U] (fun x => max a (f x)) := by
    filter_upwards [ha] with x hx
    exact (max_eq_right hx).symm
  have hp : Set.EqOn f (fun x => max a (f x)) U :=
    Measure.eqOn_open_of_ae_eq heq hU hf ((continuousOn_const : ContinuousOn (fun _ : PDE.Vec d => a) U).sup hf)
  intro x hx
  rw [hp hx]
  exact le_max_left _ _

#print axioms continuousOn_le_of_ae_restrict


/-- The finite ground projection inherits the pointwise sign and interior
lower bound of its native representative. -/
theorem spectral_ground_representative_bounds {d : ℕ}
    {κ R r a : ℝ} (hκ : 0 < κ) (hR : 0 < R) (hr : 0 < r) (hrR : r < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (S : Finset ℕ)
    (u : Homogenization.H10Function (sourceBall (0 : PDE.Vec d) R))
    (g : Lp ℝ 2 (dirichletVolume ρ R))
    (hgu : (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] u.toH1Function.toFun)
    (hnorm : ‖g‖ = 1)
    (hproj : (∑ i ∈ S, (spectralHeatBasis s).repr g i • spectralHeatBasis s i) =
      inner ℝ g g • g)
    (hu : ∀ x, 0 ≤ u.toH1Function.toFun x)
    (hlower : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r),
      a ≤ u.toH1Function.toFun x) :
    let φ : PDE.Vec d → ℝ := fun x =>
      ∑ i ∈ S, (spectralHeatBasis s).repr g i * s.eigenfunction i x
    ContinuousOn φ (closure (sourceBall 0 R)) ∧
      (∀ x ∈ frontier (sourceBall 0 R), φ x = 0) ∧
      (∀ x ∈ closure (sourceBall 0 R), 0 ≤ φ x) ∧
      (∀ x ∈ sourceBall 0 r, a ≤ φ x) ∧
      (g : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] φ := by
  classical
  dsimp only
  let φ : PDE.Vec d → ℝ := fun x =>
    ∑ i ∈ S, (spectralHeatBasis s).repr g i * s.eigenfunction i x
  obtain ⟨hcont, hboundary, hrep⟩ := spectral_finite_projection_representative s S g
  change ContinuousOn φ (closure (sourceBall 0 R)) at hcont
  change (∀ x ∈ frontier (sourceBall 0 R), φ x = 0) at hboundary
  change ((∑ i ∈ S, (spectralHeatBasis s).repr g i • spectralHeatBasis s i :
    Lp ℝ 2 (dirichletVolume ρ R)) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] φ at hrep
  have hself : inner ℝ g g = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num
  rw [hproj, hself, one_smul] at hrep
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (hell.2.2 x).1)).ne'
  have hB : IsOpen (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact PDE.isOpen_euclideanBall 0 _
  have hb : IsOpen (sourceBall (0 : PDE.Vec d) r) := by
    rw [← pde_ball_eq_sourceBall _ hr]
    exact PDE.isOpen_euclideanBall 0 _
  have hsub : sourceBall (0 : PDE.Vec d) r ⊆ sourceBall 0 R := by
    intro x hx
    exact lt_trans hx hrR
  have hposae : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) R), 0 ≤ φ x := by
    filter_upwards [hac.ae_le hrep, hac.ae_le hgu] with x hx hy
    rw [← hx, hy]
    exact hu x
  have hlowae : ∀ᵐ x ∂volume.restrict (sourceBall (0 : PDE.Vec d) r), a ≤ φ x := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hac.ae_le hrep),
      ae_restrict_of_ae_restrict_of_subset hsub (hac.ae_le hgu), hlower] with x hx hy hz
    rw [← hx, hy]
    exact hz
  have hpos := continuousOn_le_of_ae_restrict hB (hcont.mono subset_closure) hposae
  have hlow := continuousOn_le_of_ae_restrict hb
    (hcont.mono (hsub.trans subset_closure)) hlowae
  refine ⟨hcont, hboundary, ?_, hlow, hrep⟩
  intro x hx
  change 0 ≤ φ x
  by_cases hxB : x ∈ sourceBall (0 : PDE.Vec d) R
  · exact hpos x hxB
  · have hfront : x ∈ frontier (sourceBall (0 : PDE.Vec d) R) := by
      rw [frontier, hB.interior_eq]
      exact ⟨hx, hxB⟩
    rw [hboundary x hfront]

#print axioms spectral_ground_representative_bounds


/-- The normalized ground sum has unit weighted mass, and the finite
rank-one projection formula holds at every point of the closed ball. -/
theorem spectral_rank_one_projection_pointwise {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (S : Finset ℕ)
    (g : Lp ℝ 2 (dirichletVolume ρ R)) (hnorm : ‖g‖ = 1)
    (hproj : ∀ f, (∑ i ∈ S, (spectralHeatBasis s).repr f i • spectralHeatBasis s i) =
      inner ℝ f g • g) :
    let φ : PDE.Vec d → ℝ := fun x =>
      ∑ i ∈ S, (spectralHeatBasis s).repr g i * s.eigenfunction i x
    (∫ x, φ x ^ 2 ∂dirichletVolume ρ R) = 1 ∧
    ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (x : PDE.Vec d), x ∈ closure (sourceBall 0 R) →
      (∑ i ∈ S, (spectralHeatBasis s).repr f i * s.eigenfunction i x) =
        inner ℝ f g * φ x := by
  classical
  dsimp only
  let φ : PDE.Vec d → ℝ := fun x =>
    ∑ i ∈ S, (spectralHeatBasis s).repr g i * s.eigenfunction i x
  obtain ⟨hcont, _, hrep⟩ := spectral_finite_projection_representative s S g
  change ContinuousOn φ (closure (sourceBall 0 R)) at hcont
  change ((∑ i ∈ S, (spectralHeatBasis s).repr g i • spectralHeatBasis s i :
    Lp ℝ 2 (dirichletVolume ρ R)) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] φ at hrep
  have hself : inner ℝ g g = 1 := by
    rw [real_inner_self_eq_norm_sq, hnorm]
    norm_num
  rw [hproj g, hself, one_smul] at hrep
  have hac : volume.restrict (sourceBall (0 : PDE.Vec d) R) ≪ dirichletVolume ρ R := by
    apply withDensity_absolutelyContinuous' hell.1.ennreal_ofReal.aemeasurable
    exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (hκ.trans_le (hell.2.2 x).1)).ne'
  have hB : IsOpen (sourceBall (0 : PDE.Vec d) R) := by
    rw [← pde_ball_eq_sourceBall _ hR]
    exact PDE.isOpen_euclideanBall 0 _
  constructor
  · change (∫ x, φ x ^ 2 ∂dirichletVolume ρ R) = 1
    calc
      (∫ x, φ x ^ 2 ∂dirichletVolume ρ R) = inner ℝ g g := by
        rw [MeasureTheory.L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hrep] with x hx
        simp only [RCLike.inner_apply, conj_trivial, hx, pow_two]
      _ = 1 := hself
  · intro f
    let ψ : PDE.Vec d → ℝ := fun x =>
      ∑ i ∈ S, (spectralHeatBasis s).repr f i * s.eigenfunction i x
    obtain ⟨hψcont, _, hψrep⟩ := spectral_finite_projection_representative s S f
    change ContinuousOn ψ (closure (sourceBall 0 R)) at hψcont
    change ((∑ i ∈ S, (spectralHeatBasis s).repr f i • spectralHeatBasis s i :
      Lp ℝ 2 (dirichletVolume ρ R)) : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] ψ at hψrep
    rw [hproj f] at hψrep
    have hae : ψ =ᵐ[volume.restrict (sourceBall (0 : PDE.Vec d) R)]
        (fun x => inner ℝ f g * φ x) := by
      apply hac.ae_le
      filter_upwards [hψrep, hrep, Lp.coeFn_smul (inner ℝ f g) g] with x hx hy hz
      change _ = ψ x at hx
      change _ = inner ℝ f g * g x at hz
      rw [← hx, hz, hy]
    have heq : Set.EqOn ψ (fun x => inner ℝ f g * φ x) (sourceBall 0 R) :=
      Measure.eqOn_open_of_ae_eq hae hB (hψcont.mono subset_closure)
        ((hcont.const_mul _).mono subset_closure)
    have heq' : Set.EqOn ψ (fun x => inner ℝ f g * φ x) (closure (sourceBall 0 R)) :=
      heq.of_subset_closure hψcont (hcont.const_mul _) subset_closure (fun _ hx => hx)
    intro x hx
    exact heq' hx

#print axioms spectral_rank_one_projection_pointwise

end EinsteinFull.Blueprint.SbxS3UniformCrossHeat

#lint
