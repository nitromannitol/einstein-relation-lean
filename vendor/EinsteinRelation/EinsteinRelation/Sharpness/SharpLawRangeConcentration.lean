import EinsteinRelation.External.WhiteNoise
import EinsteinRelation.Sharpness.JacobianReconciliation
import EinsteinRelation.Sharpness.SharpExampleFromSteps
import EinsteinRelation.Sharpness.SharpGradientField
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ClusterPt
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # Almost sure orbit potentials of the sharp physical law

Source `paper/main.tex`, Proposition 7.1, Step 2 (lines 1235–1238), for the physical pair
`sharpPhysicalPair` of the scaled canonical seed.

The orbit-potential property of the clipped orbit gradient holds almost surely under the law
`P.map sharpPhysicalPair`, with no range hypothesis. The physical pair need not be injective, so
its range need not carry the law. Instead:

* `sharpPhysicalPair W` is the image under `jetFieldPair` of a jet `seedJet W` in the Polish space
  `JetMap d` of continuous maps `Vec d → ℝ × Vec d × ℝ` (normalized value, gradient, clock density).
* The jets with normalized value bounded by `2ε`, gradient bounded by `1/4`, clock density in
  `[3/4, 5/4]` and a derivative-consistent value form the closed set `admissibleJets`.
* `jetFieldPair` is continuous and injective on `admissibleJets`. By the Lusin–Souslin theorem the
  image `jetFieldPair '' admissibleJets` is Borel. It contains every physical pair, so it carries
  the law, and each of its points has an orbit potential.

The corrector items of `SharpEnvironmentInput` that do not involve the Step 4 energy identity or
the mean clock density follow: measurability, the `1/4` bound, `ā e₁ = e₁`, and, under a
white-noise witness, positivity of the mean sharp energy. -/

open MeasureTheory Filter Topology
open EinsteinRelation.Correctors

namespace EinsteinRelation.Sharpness

noncomputable section

/-! ### Covectors of gradients -/

/-- The continuous linear functional `y ↦ ∑ k, w k * y k` with coefficient vector `w`. -/
def covector {d : ℕ} (w : Vec d) : Vec d →L[ℝ] ℝ :=
  ∑ k, w k • (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ)

theorem covector_apply {d : ℕ} (w y : Vec d) : covector w y = ∑ k, w k * y k := by
  simp [covector, ContinuousLinearMap.sum_apply]

theorem covector_unitVector {d : ℕ} (w : Vec d) (k : Fin d) :
    covector w (unitVector k) = w k := by
  simp [covector_apply, unitVector, Pi.single_apply]

theorem continuous_covector {d : ℕ} : Continuous (fun w : Vec d => covector w) := by
  show Continuous fun w : Vec d => ∑ k, w k • (ContinuousLinearMap.proj k : Vec d →L[ℝ] ℝ)
  exact continuous_finset_sum _ fun k _ => (continuous_apply k).smul continuous_const

/-- The derivative of a real function is the covector of its gradient. -/
theorem fderiv_eq_covector_gradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) :
    fderiv ℝ f x = covector (gradient f x) := by
  refine ContinuousLinearMap.ext fun y => ?_
  have hy : y = ∑ k, y k • unitVector k := by
    funext j
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  have key : fderiv ℝ f x y = ∑ k, y k • fderiv ℝ f x (unitVector k) := by
    conv_lhs => rw [hy]
    rw [map_sum]
    simp only [map_smul]
  rw [key, covector_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gradient, coordinateDerivative, smul_eq_mul]
  ring

/-- The gradient of a smooth real function is continuous. -/
theorem continuous_gradient_of_contDiff {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : Continuous fun x => gradient f x := by
  refine continuous_pi fun k => ?_
  have h1 : Continuous fun x => fderiv ℝ f x := hf.continuous_fderiv (by simp)
  exact h1.clm_apply (continuous_const : Continuous fun _ : Vec d => unitVector k)

theorem continuous_euclideanNorm {d : ℕ} : Continuous (fun x : Vec d => euclideanNorm x) := by
  have h : (fun x : Vec d => euclideanNorm x) = fun x => Real.sqrt (∑ k, x k * x k) := rfl
  rw [h]
  exact Real.continuous_sqrt.comp
    (continuous_finset_sum _ fun k _ => (continuous_apply k).mul (continuous_apply k))

theorem abs_coord_le_of_euclideanNorm_le {d : ℕ} {v : Vec d} (k : Fin d)
    (h : euclideanNorm v ≤ 1 / 4) : |v k| ≤ 1 / 4 := by
  have hsq : v k * v k ≤ euclideanSq v := by
    unfold euclideanSq dot
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ k)
  have habs : |v k| ≤ euclideanNorm v := by
    unfold euclideanNorm
    apply Real.abs_le_sqrt
    rw [sq]
    exact hsq
  exact habs.trans h

/-! ### Coordinatewise clamping of gradients -/

/-- One coordinate clamped to `[-1/4, 1/4]`. -/
def clampCoord (t : ℝ) : ℝ := max (-(1 / 4 : ℝ)) (min (1 / 4 : ℝ) t)

theorem continuous_clampCoord : Continuous clampCoord := by
  unfold clampCoord
  exact continuous_const.max (continuous_const.min continuous_id)

theorem clampCoord_bounds (t : ℝ) : -(1 / 4 : ℝ) ≤ clampCoord t ∧ clampCoord t ≤ 1 / 4 := by
  unfold clampCoord
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clampCoord_of_abs_le {t : ℝ} (h : |t| ≤ 1 / 4) : clampCoord t = t := by
  have h' := abs_le.mp h
  unfold clampCoord
  rw [min_eq_right h'.2, max_eq_right h'.1]

/-- A vector clamped coordinatewise to `[-1/4, 1/4]`. It is continuous and the identity on the
closed Euclidean ball of radius `1/4`. -/
def clampVec {d : ℕ} (v : Vec d) : Vec d := fun k => clampCoord (v k)

theorem continuous_clampVec {d : ℕ} : Continuous (fun v : Vec d => clampVec v) :=
  continuous_pi fun k => continuous_clampCoord.comp (continuous_apply k)

theorem clampVec_of_norm_le {d : ℕ} {v : Vec d} (h : euclideanNorm v ≤ 1 / 4) :
    clampVec v = v := by
  funext k
  exact clampCoord_of_abs_le (abs_coord_le_of_euclideanNorm_le k h)

/-- Clock density clamped from below by `1/2`, continuous on all of `ℝ`. -/
def clampDensity (μ : ℝ) : ℝ := max μ (1 / 2)

theorem clampDensity_pos (μ : ℝ) : 0 < clampDensity μ := by
  unfold clampDensity
  exact lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem clampDensity_of_ge {μ : ℝ} (h : (3 / 4 : ℝ) ≤ μ) : clampDensity μ = μ := by
  unfold clampDensity
  exact max_eq_left (by linarith)

/-! ### Coefficients on clamped gradients -/

theorem coefficient_entry_eq_inverse_sum {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

theorem inverseCandidate_apply {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    inverseCandidate i g j k = (if j = k then (1 : ℝ) else 0) -
      (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
  simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

/-- The rank-one coefficient is continuous in the gradient after clamping. -/
theorem continuous_coefficient_clampVec {d : ℕ} (i : Fin d) :
    Continuous (fun w : Vec d => coefficient i (clampVec w)) := by
  have hJ : Continuous fun w : Vec d => jacobianFactor i (clampVec w) := by
    unfold jacobianFactor
    exact continuous_const.add ((continuous_apply i).comp continuous_clampVec)
  have hJne : ∀ w : Vec d, jacobianFactor i (clampVec w) ≠ 0 := fun w => by
    have h : (0 : ℝ) < 1 + clampCoord (w i) := by linarith [(clampCoord_bounds (w i)).1]
    exact h.ne'
  have hinv : Continuous fun w : Vec d => (jacobianFactor i (clampVec w))⁻¹ :=
    hJ.inv₀ hJne
  have hIC : ∀ j l : Fin d, Continuous fun w : Vec d => inverseCandidate i (clampVec w) j l := by
    intro j l
    simp only [inverseCandidate_apply]
    exact continuous_const.sub
      (hinv.mul (continuous_const.mul ((continuous_apply l).comp continuous_clampVec)))
  refine continuous_matrix fun j k => ?_
  simp only [coefficient_entry_eq_inverse_sum]
  exact hJ.mul (continuous_finset_sum _ fun l _ => (hIC j l).mul (hIC k l))

/-- Under the gradient bound, the coefficient determines its gradient. -/
theorem coefficient_eq_gradient {d : ℕ} (i : Fin d) {g g' : Vec d}
    (hg : euclideanNorm g ≤ 1 / 4) (hg' : euclideanNorm g' ≤ 1 / 4)
    (h : coefficient i g = coefficient i g') : g = g' := by
  have h1 := coefficient_mulVec_harmonic i g hg
  have h2 := coefficient_mulVec_harmonic i g' hg'
  rw [h, Matrix.mulVec_add] at h1
  rw [Matrix.mulVec_add] at h2
  have hAg := add_left_cancel (h1.trans h2.symm)
  have hdiff : (coefficient i g').mulVec (g - g') = 0 := by
    rw [Matrix.mulVec_sub, hAg, sub_self]
  have hlow := (coefficient_uniformlyElliptic i g' hg' (g - g')).1
  have h0 : dot (g - g') (0 : Vec d) = 0 := by simp [dot]
  rw [hdiff, h0] at hlow
  by_contra hne
  have hpos : 0 < euclideanSq (g - g') :=
    (euclideanSq_pos_iff (g - g')).mpr (sub_ne_zero.mpr hne)
  linarith

/-- A rank-one coefficient of a bounded gradient has unit determinant. -/
theorem isUnit_det_coefficient {d : ℕ} (i : Fin d) {g : Vec d} (hg : euclideanNorm g ≤ 1 / 4) :
    IsUnit (coefficient i g).det := by
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hav⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := coefficient i g)).mpr hdet
  have hlow := (coefficient_uniformlyElliptic i g hg v).1
  have h0 : dot v (0 : Vec d) = 0 := by simp [dot]
  rw [hav, h0] at hlow
  have hpos : 0 < euclideanSq v := (euclideanSq_pos_iff v).mpr hv
  linarith

/-- Inverting the harmonic flux of a bounded gradient recovers the gradient. -/
theorem inv_mulVec_unit_sub {d : ℕ} (i : Fin d) {g : Vec d} (hg : euclideanNorm g ≤ 1 / 4) :
    Matrix.mulVec (coefficient i g)⁻¹ (unitVector i) - unitVector i = g := by
  have h := coefficient_mulVec_harmonic i g hg
  have hA := Matrix.nonsing_inv_mul (coefficient i g) (isUnit_det_coefficient i hg)
  have h1 : Matrix.mulVec (coefficient i g)⁻¹ (unitVector i) = unitVector i + g := by
    calc Matrix.mulVec (coefficient i g)⁻¹ (unitVector i)
        = Matrix.mulVec (coefficient i g)⁻¹
            (Matrix.mulVec (coefficient i g) (unitVector i + g)) := by rw [h]
      _ = Matrix.mulVec ((coefficient i g)⁻¹ * coefficient i g) (unitVector i + g) := by
          rw [Matrix.mulVec_mulVec]
      _ = unitVector i + g := by rw [hA, Matrix.one_mulVec]
  rw [h1]
  abel

/-! ### The jet carrier -/

/-- Jets of a potential: value, gradient, and clock density at each point. -/
abbrev JetMap (d : ℕ) := ContinuousMap (Vec d) (ℝ × Vec d × ℝ)

instance polishSpace_jetMap (d : ℕ) : PolishSpace (JetMap d) := by
  infer_instance

/-- The physical pair value at one point of a jet triple `(value, gradient, density)`. -/
def jetPairValue {d : ℕ} (i : Fin d) (p : ℝ × Vec d × ℝ) : Mat d × ℝ :=
  ((clampDensity p.2.2)⁻¹ • coefficient i (clampVec p.2.1),
    -(1 / 2 : ℝ) * Real.log (clampDensity p.2.2))

theorem continuous_jetPairValue {d : ℕ} (i : Fin d) : Continuous (jetPairValue (d := d) i) := by
  have hm : Continuous fun p : ℝ × Vec d × ℝ => clampDensity p.2.2 := by
    unfold clampDensity
    exact (continuous_snd.comp continuous_snd).max continuous_const
  have hmpos : ∀ p : ℝ × Vec d × ℝ, clampDensity p.2.2 ≠ 0 := fun p =>
    (clampDensity_pos _).ne'
  have hv : Continuous fun p : ℝ × Vec d × ℝ => p.2.1 := continuous_fst.comp continuous_snd
  unfold jetPairValue
  exact Continuous.prodMk ((hm.inv₀ hmpos).smul ((continuous_coefficient_clampVec i).comp hv))
    (continuous_const.mul (hm.log hmpos))

/-- The first physical component of a jet, pointwise. -/
def jetFst {d : ℕ} (i : Fin d) : ContinuousMap (ℝ × Vec d × ℝ) (Mat d) :=
  ⟨fun p => (jetPairValue i p).1, (continuous_jetPairValue i).fst⟩

/-- The second physical component of a jet, pointwise. -/
def jetSnd {d : ℕ} (i : Fin d) : ContinuousMap (ℝ × Vec d × ℝ) ℝ :=
  ⟨fun p => (jetPairValue i p).2, (continuous_jetPairValue i).snd⟩

/-- The physical coefficient pair of a jet. -/
def jetFieldPair {d : ℕ} (i : Fin d) (b : JetMap d) : FieldPair d :=
  ((jetFst i).comp b, (jetSnd i).comp b)

theorem jetFieldPair_fst_apply {d : ℕ} (i : Fin d) (b : JetMap d) (x : Vec d) :
    (jetFieldPair i b).1 x = (clampDensity (b x).2.2)⁻¹ • coefficient i (clampVec (b x).2.1) :=
  rfl

theorem jetFieldPair_snd_apply {d : ℕ} (i : Fin d) (b : JetMap d) (x : Vec d) :
    (jetFieldPair i b).2 x = -(1 / 2 : ℝ) * Real.log (clampDensity (b x).2.2) :=
  rfl

theorem continuous_jetFieldPair {d : ℕ} (i : Fin d) : Continuous (jetFieldPair (d := d) i) := by
  show Continuous fun b : JetMap d => ((jetFst i).comp b, (jetSnd i).comp b)
  exact (ContinuousMap.continuous_postcomp (jetFst i)).prodMk
    (ContinuousMap.continuous_postcomp (jetSnd i))

/-! ### Consistent and admissible jets -/

/-- The covector-valued map `(value, gradient, density) ↦ covector gradient`. -/
def covectorMap (d : ℕ) : ContinuousMap (ℝ × Vec d × ℝ) (Vec d →L[ℝ] ℝ) :=
  ⟨fun p => covector p.2.1, continuous_covector.comp (continuous_fst.comp continuous_snd)⟩

/-- Jets whose value component is differentiable with derivative the covector of its gradient
component. -/
def ConsistentJets (d : ℕ) : Set (JetMap d) :=
  {b | ∀ x : Vec d, HasFDerivAt (fun y => (b y).1) (covector (b x).2.1) x}

/-- A set condition on the values of a continuous map that holds at every point is closed. -/
theorem isClosed_forall_eval {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : Y → Prop} (hp : IsClosed {y | p y}) :
    IsClosed {b : ContinuousMap X Y | ∀ x, p (b x)} := by
  have h : {b : ContinuousMap X Y | ∀ x, p (b x)} =
      ⋂ x : X, (fun b : ContinuousMap X Y => b x) ⁻¹' {y | p y} := by
    ext b
    simp
  rw [h]
  exact isClosed_iInter fun x => hp.preimage (continuous_eval_const x)

/-- The consistent jets form a closed set. A limit of consistent jets in the compact-open topology
has derivative equal to the limit of the gradients, because the gradients converge locally
uniformly. -/
theorem isClosed_consistentJets (d : ℕ) : IsClosed (ConsistentJets d) := by
  rw [isClosed_iff_clusterPt]
  intro a ha
  haveI : (𝓝 a ⊓ 𝓟 (ConsistentJets d)).NeBot := ha
  have hS : ∀ᶠ b in 𝓝 a ⊓ 𝓟 (ConsistentJets d), b ∈ ConsistentJets d :=
    Filter.le_principal_iff.mp inf_le_right
  have hT : Tendsto (fun b : JetMap d => (covectorMap d).comp b)
      (𝓝 a ⊓ 𝓟 (ConsistentJets d)) (𝓝 ((covectorMap d).comp a)) :=
    ((ContinuousMap.continuous_postcomp (covectorMap d)).tendsto a).mono_left inf_le_left
  have hloc := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hT
  show ∀ x : Vec d, HasFDerivAt (fun y => (a y).1) (covector (a x).2.1) x
  intro x
  have hu := tendstoLocallyUniformly_iff_filter.mp hloc x
  have hf : ∀ᶠ n : JetMap d × Vec d in (𝓝 a ⊓ 𝓟 (ConsistentJets d)) ×ˢ 𝓝 x,
      HasFDerivAt (fun y => (n.1 y).1) (covector (n.1 n.2).2.1) n.2 := by
    filter_upwards [Filter.Eventually.prod_inl hS (𝓝 x)] with n hn
    exact (show ∀ y : Vec d, HasFDerivAt (fun z => (n.1 z).1) (covector (n.1 y).2.1) y from hn)
      n.2
  have hfg : ∀ᶠ y in 𝓝 x, Tendsto (fun n : JetMap d => (n y).1)
      (𝓝 a ⊓ 𝓟 (ConsistentJets d)) (𝓝 (a y).1) :=
    Filter.Eventually.of_forall fun y =>
      ((continuous_fst.comp (continuous_eval_const y)).tendsto a).mono_left inf_le_left
  have key := hasFDerivAt_of_tendstoUniformlyOnFilter
    (f := fun (m : JetMap d) (y : Vec d) => (m y).1) hu hf hfg
  exact key

/-- The admissible jets: normalized value, value bounded by `M`, gradient bounded by `1/4`,
clock density in `[3/4, 5/4]`, and consistency. -/
def admissibleJets (d : ℕ) (M : ℝ) : Set (JetMap d) :=
  {b | (b 0).1 = 0} ∩ {b | ∀ x, |(b x).1| ≤ M} ∩
    {b | ∀ x, euclideanNorm (b x).2.1 ≤ 1 / 4} ∩
    {b | ∀ x, 3 / 4 ≤ (b x).2.2 ∧ (b x).2.2 ≤ 5 / 4} ∩ ConsistentJets d

theorem isClosed_admissibleJets (d : ℕ) (M : ℝ) : IsClosed (admissibleJets d M) := by
  have h0 : IsClosed {b : JetMap d | (b 0).1 = 0} :=
    isClosed_eq (continuous_fst.comp (continuous_eval_const (0 : Vec d))) continuous_const
  have hM : IsClosed {b : JetMap d | ∀ x, |(b x).1| ≤ M} :=
    isClosed_forall_eval (p := fun y : ℝ × Vec d × ℝ => |y.1| ≤ M)
      (isClosed_le (f := fun y : ℝ × Vec d × ℝ => |y.1|) (g := fun _ => M)
        (continuous_abs.comp continuous_fst) continuous_const)
  have hg : IsClosed {b : JetMap d | ∀ x, euclideanNorm (b x).2.1 ≤ 1 / 4} :=
    isClosed_forall_eval (p := fun y : ℝ × Vec d × ℝ => euclideanNorm y.2.1 ≤ 1 / 4)
      (isClosed_le (f := fun y : ℝ × Vec d × ℝ => euclideanNorm y.2.1) (g := fun _ => 1 / 4)
        (continuous_euclideanNorm.comp (continuous_fst.comp continuous_snd)) continuous_const)
  have hsnd : Continuous fun y : ℝ × Vec d × ℝ => y.2.2 := continuous_snd.comp continuous_snd
  have hμc : IsClosed {y : ℝ × Vec d × ℝ | 3 / 4 ≤ y.2.2 ∧ y.2.2 ≤ 5 / 4} :=
    (isClosed_le continuous_const hsnd).inter (isClosed_le hsnd continuous_const)
  have hμ : IsClosed {b : JetMap d | ∀ x, 3 / 4 ≤ (b x).2.2 ∧ (b x).2.2 ≤ 5 / 4} :=
    isClosed_forall_eval (p := fun y : ℝ × Vec d × ℝ => 3 / 4 ≤ y.2.2 ∧ y.2.2 ≤ 5 / 4) hμc
  exact (((h0.inter hM).inter hg).inter hμ).inter (isClosed_consistentJets d)

theorem admissible_norm_le {d : ℕ} {M : ℝ} {b : JetMap d} (hb : b ∈ admissibleJets d M)
    (x : Vec d) : euclideanNorm (b x).2.1 ≤ 1 / 4 := by
  obtain ⟨⟨⟨⟨-, -⟩, hg⟩, -⟩, -⟩ := hb
  exact hg x

/-! ### Injectivity of the physical pair on admissible jets -/

/-- Two clock densities at least `3/4` with equal log-potentials are equal. -/
theorem density_eq_of_snd {μ μ' : ℝ} (h : (3 / 4 : ℝ) ≤ μ) (h' : (3 / 4 : ℝ) ≤ μ')
    (e : -(1 / 2 : ℝ) * Real.log (clampDensity μ) = -(1 / 2 : ℝ) * Real.log (clampDensity μ')) :
    μ = μ' := by
  rw [clampDensity_of_ge h, clampDensity_of_ge h'] at e
  have hlog : Real.log μ = Real.log μ' := by linarith
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by linarith)) hlog

/-- The physical pair of an admissible jet determines the jet. -/
theorem jetFieldPair_injOn {d : ℕ} (i : Fin d) (M : ℝ) :
    Set.InjOn (jetFieldPair i) (admissibleJets d M) := by
  intro b hb b' hb' heq
  obtain ⟨⟨⟨⟨h0, -⟩, hg⟩, hμ⟩, hc⟩ := hb
  obtain ⟨⟨⟨⟨h0', -⟩, hg'⟩, hμ'⟩, hc'⟩ := hb'
  have hc1 : ∀ y, HasFDerivAt (fun z => (b z).1) (covector (b y).2.1) y := hc
  have hc1' : ∀ y, HasFDerivAt (fun z => (b' z).1) (covector (b' y).2.1) y := hc'
  have hpt : ∀ x, jetPairValue i (b x) = jetPairValue i (b' x) := fun x =>
    Prod.ext (congrArg (fun ω : FieldPair d => ω.1 x) heq)
      (congrArg (fun ω : FieldPair d => ω.2 x) heq)
  have hμeq : ∀ x, (b x).2.2 = (b' x).2.2 := fun x =>
    density_eq_of_snd (hμ x).1 (hμ' x).1 (congrArg Prod.snd (hpt x))
  have hvc : ∀ x, (b x).2.1 = (b' x).2.1 := fun x => by
    have h1 : (clampDensity (b x).2.2)⁻¹ • coefficient i (clampVec (b x).2.1) =
        (clampDensity (b' x).2.2)⁻¹ • coefficient i (clampVec (b' x).2.1) :=
      congrArg Prod.fst (hpt x)
    rw [hμeq x] at h1
    have hc0 : (clampDensity (b' x).2.2)⁻¹ ≠ 0 := inv_ne_zero (clampDensity_pos _).ne'
    have hco := smul_right_injective (Mat d) hc0 h1
    rw [clampVec_of_norm_le (hg x), clampVec_of_norm_le (hg' x)] at hco
    exact coefficient_eq_gradient i (hg x) (hg' x) hco
  have hcons : ∀ y, HasFDerivAt (fun z => (b z).1 - (b' z).1)
      (covector (b y).2.1 - covector (b' y).2.1) y := fun y => (hc1 y).sub (hc1' y)
  have hzero : ∀ y, fderiv ℝ (fun z => (b z).1 - (b' z).1) y = 0 := fun y => by
    rw [(hcons y).fderiv, hvc y, sub_self]
  have hconst : ∀ y, (b y).1 - (b' y).1 = (b 0).1 - (b' 0).1 := fun y =>
    is_const_of_fderiv_eq_zero (fun z => (hcons z).differentiableAt) hzero y 0
  have hu : ∀ y, (b y).1 = (b' y).1 := fun y => by
    have h : (b y).1 - (b' y).1 = (b 0).1 - (b' 0).1 := hconst y
    have e0 : (b 0).1 = 0 := h0
    have e0' : (b' 0).1 = 0 := h0'
    linarith
  refine ContinuousMap.ext fun y => ?_
  exact Prod.ext (hu y) (Prod.ext (hvc y) (hμeq y))

/-- The image of the admissible jets under the physical pair is Borel. The map is continuous and
injective on the closed set of admissible jets, so Lusin–Souslin applies. -/
theorem measurableSet_jetImage {d : ℕ} (i : Fin d) (M : ℝ) :
    MeasurableSet (jetFieldPair i '' admissibleJets d M) := by
  letI : MeasurableSpace (JetMap d) := borel _
  haveI : BorelSpace (JetMap d) := ⟨rfl⟩
  exact MeasurableSet.image_of_continuousOn_injOn (isClosed_admissibleJets d M).measurableSet
    (continuous_jetFieldPair i).continuousOn (jetFieldPair_injOn i M)

/-! ### The orbit potential on admissible jets -/

/-- The orbit gradient of the physical pair of an admissible jet is the gradient of the jet. -/
theorem jet_orbit_data {d : ℕ} (i : Fin d) {M : ℝ} {b : JetMap d}
    (hb : b ∈ admissibleJets d M) (x : Vec d) :
    reducedCoefficient (jetFieldPair i b) x = coefficient i (b x).2.1 ∧
      clippedSharpGradient i (translate x (jetFieldPair i b)) = (b x).2.1 := by
  obtain ⟨⟨⟨⟨-, -⟩, hg⟩, -⟩, -⟩ := hb
  have hpos : 0 < clampDensity (b x).2.2 := clampDensity_pos _
  have hexp : Real.exp (-2 * (jetFieldPair i b).2 x) = clampDensity (b x).2.2 := by
    rw [jetFieldPair_snd_apply, show (-2 : ℝ) * (-(1 / 2 : ℝ) * Real.log (clampDensity (b x).2.2))
      = Real.log (clampDensity (b x).2.2) by ring]
    exact Real.exp_log hpos
  have hred : reducedCoefficient (jetFieldPair i b) x = coefficient i (b x).2.1 := by
    unfold reducedCoefficient clockDensity
    rw [hexp, jetFieldPair_fst_apply, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul,
      clampVec_of_norm_le (hg x)]
  refine ⟨hred, ?_⟩
  have hsg : sharpGradientField i (translate x (jetFieldPair i b)) = (b x).2.1 := by
    rw [sharpGradientField_translate, hred]
    exact inv_mulVec_unit_sub i (hg x)
  unfold clippedSharpGradient
  rw [hsg, if_pos (hg x)]

theorem contDiff_jet_value {d : ℕ} {b : JetMap d} (hc : b ∈ ConsistentJets d) :
    ContDiff ℝ 1 (fun y => (b y).1) := by
  have hc1 : ∀ y, HasFDerivAt (fun z => (b z).1) (covector (b y).2.1) y := hc
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun y => (hc1 y).differentiableAt, ?_⟩
  have hfd : fderiv ℝ (fun y => (b y).1) = fun y => covector (b y).2.1 :=
    funext fun y => (hc1 y).fderiv
  rw [hfd]
  exact continuous_covector.comp (continuous_fst.comp (continuous_snd.comp b.continuous))

theorem gradient_jet_value {d : ℕ} {b : JetMap d} (hc : b ∈ ConsistentJets d) (x : Vec d) :
    gradient (fun y => (b y).1) x = (b x).2.1 := by
  have hc1 : ∀ y, HasFDerivAt (fun z => (b z).1) (covector (b y).2.1) y := hc
  funext k
  show coordinateDerivative k (fun y => (b y).1) x = (b x).2.1 k
  unfold coordinateDerivative
  rw [(hc1 x).fderiv, covector_unitVector]

/-- Every admissible jet carries the orbit potential given by its value component, bounded by the
bound `M` of the admissible set. -/
theorem orbit_potential_of_admissible {d : ℕ} (i : Fin d) (M : ℝ) {b : JetMap d}
    (hb : b ∈ admissibleJets d M) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ M) ∧
      ∀ x, gradient φ x = clippedSharpGradient i (translate x (jetFieldPair i b)) := by
  have hb' := hb
  obtain ⟨⟨⟨⟨-, hM⟩, -⟩, -⟩, hc⟩ := hb'
  refine ⟨fun y => (b y).1, contDiff_jet_value hc, hM, fun x => ?_⟩
  rw [gradient_jet_value hc x, (jet_orbit_data i hb x).2]

/-! ### The jet of the scaled canonical seed -/

theorem continuous_jetOfPotential_components {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hV : Continuous (potentialField i δ ψ)) :
    Continuous fun y => (ψ y - ψ 0, gradient ψ y, Real.exp (-2 * potentialField i δ ψ y)) := by
  have h1 : Continuous fun y => ψ y - ψ 0 := hψ.continuous.sub continuous_const
  have h2 : Continuous fun y => Real.exp (-2 * potentialField i δ ψ y) :=
    Real.continuous_exp.comp (continuous_const.mul hV)
  exact h1.prodMk ((continuous_gradient_of_contDiff hψ).prodMk h2)

/-- The jet of a smooth potential `ψ`, normalized at the origin: the value `ψ - ψ 0`, the gradient,
and the clock density `exp (-2 V)` of the physical pair with potential `V`. -/
noncomputable def jetOfPotential {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hV : Continuous (potentialField i δ ψ)) : JetMap d :=
  ⟨fun y => (ψ y - ψ 0, gradient ψ y, Real.exp (-2 * potentialField i δ ψ y)),
    continuous_jetOfPotential_components i δ ψ hψ hV⟩

theorem jetOfPotential_mem_consistent {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hV : Continuous (potentialField i δ ψ)) :
    jetOfPotential i δ ψ hψ hV ∈ ConsistentJets d := by
  show ∀ x : Vec d, HasFDerivAt (fun y => (jetOfPotential i δ ψ hψ hV y).1)
    (covector (jetOfPotential i δ ψ hψ hV x).2.1) x
  intro x
  have h : HasFDerivAt ψ (fderiv ℝ ψ x) x :=
    ((hψ.differentiable (by simp)) x).hasFDerivAt
  rw [fderiv_eq_covector_gradient] at h
  exact h.sub_const (ψ 0)

/-- The physical pair of a jet with potential `ψ` is the pair of the physical environment. -/
theorem jetFieldPair_jetOfPotential {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hV : Continuous (potentialField i δ ψ))
    (ha : Continuous (physicalCoefficientField i δ ψ))
    (hμ : ∀ y, (3 / 4 : ℝ) ≤ densityField i δ ψ y ∧ densityField i δ ψ y ≤ 5 / 4)
    (hgrad : ∀ y, euclideanNorm (gradient ψ y) ≤ 1 / 4) :
    jetFieldPair i (jetOfPotential i δ ψ hψ hV) = physicalEnvironment i δ ψ ha hV := by
  have hpos : ∀ y, 0 < densityField i δ ψ y := fun y => lt_of_lt_of_le (by norm_num) (hμ y).1
  refine Prod.ext (ContinuousMap.ext fun y => ?_) (ContinuousMap.ext fun y => ?_)
  · show (clampDensity (Real.exp (-2 * potentialField i δ ψ y)))⁻¹ •
        coefficient i (clampVec (gradient ψ y)) =
      (densityField i δ ψ y)⁻¹ • coefficient i (gradient ψ y)
    rw [exp_neg_two_potentialField i δ ψ y (hpos y), clampDensity_of_ge (hμ y).1,
      clampVec_of_norm_le (hgrad y)]
  · show -(1 / 2 : ℝ) * Real.log (clampDensity (Real.exp (-2 * potentialField i δ ψ y))) =
      -(1 / 2 : ℝ) * Real.log (densityField i δ ψ y)
    rw [exp_neg_two_potentialField i δ ψ y (hpos y), clampDensity_of_ge (hμ y).1]

/-- The jet of the scaled canonical seed `ε * seedField d W`, normalized at the origin. -/
noncomputable def seedJet {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) : JetMap d :=
  jetOfPotential i δ (fun y => ε * seedField d W y) (sharpSeed_contDiff ε W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W)

theorem jetFieldPair_seedJet {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) :
    jetFieldPair i (seedJet i δ ε hgrad hμ W) = sharpPhysicalPair i δ ε hgrad hμ W :=
  jetFieldPair_jetOfPotential i δ (fun y => ε * seedField d W y) (sharpSeed_contDiff ε W)
    (sharpSeed_continuous_potential i δ ε hgrad hμ W)
    (sharpSeed_continuous_coefficient i δ ε hgrad hμ W) (hμ W) (hgrad W)

theorem seedJet_mem_admissibleJets {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (hε : 0 < ε) (W : NoiseSample d) :
    seedJet i δ ε hgrad hμ W ∈ admissibleJets d (2 * ε) := by
  have hdens : ∀ x, (seedJet i δ ε hgrad hμ W x).2.2 =
      densityField i δ (fun y => ε * seedField d W y) x := fun x =>
    exp_neg_two_potentialField i δ (fun y => ε * seedField d W y) x
      (lt_of_lt_of_le (by norm_num) (hμ W x).1)
  have h0 : (seedJet i δ ε hgrad hμ W 0).1 = 0 := by
    show ε * seedField d W 0 - ε * seedField d W 0 = 0
    exact sub_self _
  have hM : ∀ x, |(seedJet i δ ε hgrad hμ W x).1| ≤ 2 * ε := fun x => by
    have h1 := abs_le.mp (sharpSeed_abs_le hε W x)
    have h2 := abs_le.mp (sharpSeed_abs_le hε W 0)
    show |ε * seedField d W x - ε * seedField d W 0| ≤ 2 * ε
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hg : ∀ x, euclideanNorm (seedJet i δ ε hgrad hμ W x).2.1 ≤ 1 / 4 := fun x => hgrad W x
  have hden : ∀ x, (3 / 4 : ℝ) ≤ (seedJet i δ ε hgrad hμ W x).2.2 ∧
      (seedJet i δ ε hgrad hμ W x).2.2 ≤ 5 / 4 := fun x => by
    rw [hdens x]
    exact hμ W x
  have hc : seedJet i δ ε hgrad hμ W ∈ ConsistentJets d :=
    jetOfPotential_mem_consistent i δ (fun y => ε * seedField d W y) (sharpSeed_contDiff ε W)
      (sharpSeed_continuous_potential i δ ε hgrad hμ W)
  unfold admissibleJets
  exact ⟨⟨⟨⟨h0, hM⟩, hg⟩, hden⟩, hc⟩

/-! ### The orbit property of the physical law, almost surely -/

/-- Almost surely under the law of the physical pair, the clipped orbit gradient has an orbit
potential bounded by `2ε`. The proof uses no range hypothesis: the image `T` of the admissible jets
is Borel, contains every physical pair, and each point of `T` carries an orbit potential. -/
theorem ae_clippedSharpGradient_orbit_law {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hε : 0 < ε) :
    ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)), ∃ φ : Vec d → ℝ,
      ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ 2 * ε) ∧
        ∀ x, gradient φ x = clippedSharpGradient i (translate x ω) := by
  have hF := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have hmem : ∀ W : NoiseSample d, sharpPhysicalPair i δ ε hgrad hμ W ∈
      jetFieldPair i '' admissibleJets d (2 * ε) := fun W =>
    ⟨seedJet i δ ε hgrad hμ W, seedJet_mem_admissibleJets i δ ε hgrad hμ hε W,
      jetFieldPair_seedJet i δ ε hgrad hμ W⟩
  have hset : MeasurableSet {ω : FieldPair d | ω ∈ jetFieldPair i '' admissibleJets d (2 * ε)} :=
    measurableSet_jetImage i (2 * ε)
  have hae : ∀ᵐ ω ∂(P.map (sharpPhysicalPair i δ ε hgrad hμ)),
      ω ∈ jetFieldPair i '' admissibleJets d (2 * ε) :=
    (ae_map_iff hF.aemeasurable hset).mpr (ae_of_all P hmem)
  filter_upwards [hae] with ω hω
  obtain ⟨b, hb, rfl⟩ := hω
  exact orbit_potential_of_admissible i (2 * ε) hb

/-! ### Corrector items of the sharp law -/

theorem sharpLocalGradient_eq_sharpGradientField {d : ℕ} (hd : 2 ≤ d) :
    sharpLocalGradient hd = sharpGradientField (⟨0, by omega⟩ : Fin d) := rfl

theorem measurable_sharpLocalGradient {d : ℕ} (hd : 2 ≤ d) :
    Measurable (sharpLocalGradient hd) := by
  rw [sharpLocalGradient_eq_sharpGradientField hd]
  exact measurable_sharpGradientField _

/-- The flux identity `ā e_i = e_i` for the law of a physical pair with `ε > 0`. The orbit
potentials of `ae_clippedSharpGradient_orbit_law` supply the domain hypothesis of
`gradient_field_corrector_identification_of_orbit`. -/
theorem abar_mulVec_unitVector_of_sharp {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hε : 0 < ε)
    (hQ : Q.measure = P.map (sharpPhysicalPair i δ ε hgrad hμ)) :
    (abar Q).mulVec (unitVector i) = unitVector i := by
  have hG : ∀ᵐ ω ∂Q.measure, ∃ φ : Vec d → ℝ, ContDiff ℝ 1 φ ∧ (∀ x, |φ x| ≤ 2 * ε) ∧
      ∀ x, gradient φ x = clippedSharpGradient i (translate x ω) := by
    rw [hQ]
    exact ae_clippedSharpGradient_orbit_law i δ ε hgrad hμ hε
  have hclip : ∀ᵐ ω ∂Q.measure, clippedSharpGradient i ω = sharpGradientField i ω := by
    rw [hQ]
    exact clippedSharpGradient_ae_eq i δ ε hgrad hμ P
  have hharm : ∀ᵐ ω ∂Q.measure,
      (reducedCoefficient ω 0).mulVec (unitVector i + clippedSharpGradient i ω) =
        unitVector i := by
    filter_upwards [ae_sharpGradientField_harmonic_zero Q i, hclip] with ω h1 h2
    rw [h2]
    exact h1
  have hflux : expectedCorrectorFlux Q i = correctorUnitVector i :=
    (gradient_field_corrector_identification_of_orbit Q i (clippedSharpGradient i) (2 * ε)
      (measurable_clippedSharpGradient i) (clippedSharpGradient_norm_le i) hG hharm).2
  funext k
  rw [mulVec_unitVector_apply]
  simp only [abar, Matrix.of_apply, hflux, correctorUnitVector, unitVector, WithLp.ofLp_toLp]

/-- Measurability, the `1/4` bound, and the flux identity `ā e₁ = e₁` of `SharpEnvironmentInput`,
for every law of the `IsSharpLaw` form. -/
theorem sharpEnvironment_items_of_isSharpLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ δ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} (hQ : IsSharpLaw hd δ Q) :
    Measurable (sharpLocalGradient hd) ∧
      (∀ᵐ ω ∂Q.measure, euclideanNorm (sharpLocalGradient hd ω) ≤ 1 / 4) ∧
      (abar Q).mulVec (unitVector (⟨0, by omega⟩ : Fin d)) =
        unitVector (⟨0, by omega⟩ : Fin d) := by
  obtain ⟨-, ε, P, hgrad, hμ, hε, hQm⟩ := hQ
  refine ⟨measurable_sharpLocalGradient hd, ?_,
    abar_mulVec_unitVector_of_sharp Q (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ hε hQm⟩
  rw [hQm, sharpLocalGradient_eq_sharpGradientField hd]
  exact ae_sharpGradientField_norm_le _ δ ε hgrad hμ P

/-- Positivity of the mean sharp energy of the local gradient. The witness `P` must be a
white-noise law: the energy vanishes on the zero noise sample, so `IsSharpLaw` alone does not
give positivity. -/
theorem sharpLocalGradient_energy_pos {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ∧
      densityField (⟨0, by omega⟩ : Fin d) δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) (hε : 0 < ε)
    (hQ : Q.measure = P.map (sharpPhysicalPair (⟨0, by omega⟩ : Fin d) δ ε hgrad hμ)) :
    0 < ∫ ω, sharpEnergy (⟨0, by omega⟩ : Fin d) (sharpLocalGradient hd ω) ∂Q.measure := by
  rw [hQ, sharpLocalGradient_eq_sharpGradientField hd]
  exact integral_sharpGradientField_energy_pos _ δ ε hgrad hμ hP hε

end

end EinsteinRelation.Sharpness
