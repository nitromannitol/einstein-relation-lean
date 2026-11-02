import EinsteinRelation.Environment.FieldMeasurability
import EinsteinRelation.Probability.LocalSigma
import EinsteinRelation.Sharpness.DivergenceProfile
import EinsteinRelation.Sharpness.PhysicalLawSampleBounds
import EinsteinRelation.Sharpness.PhysicalRegularityMeasurability
import EinsteinRelation.Sharpness.SeedFieldDerivatives
import EinsteinRelation.Sharpness.SeedJetFiniteRange
import EinsteinRelation.Sharpness.SeedJetStationarity
import EinsteinRelation.Sharpness.SharpEnvironmentLaw

/-! # The physical sharpness pair as an environment law

Source `paper/main.tex`, Proposition 7.1 (`sharp.example`), lines 1202–1231. The pushforward of a
white-noise law by the physical pair `sharpPhysicalPair` of the scaled canonical seed is Borel,
stationary and has joint finite range `4`. Together with the a.e. regularity and smoothness of the
pair, this gives an `EnvironmentLaw`.

The physical coefficient and potential at a point are fixed functions of the seed's coordinate
derivatives at that point (`sharpJetPair`). The joint jet laws of `SeedJetStationarity` and
`SeedJetFiniteRange` therefore transfer to the physical pair. The white-noise input enters only
through `External.IsWhiteNoiseLaw`. -/

open MeasureTheory

namespace EinsteinRelation.Sharpness

/-! ### The jet representation of the physical pair -/

/-- The coordinate-derivative jet of the canonical seed at a sample `W` and a point `x`, indexed by
ordered coordinate lists. -/
noncomputable def sharpJet {d : ℕ} (W : NoiseSample d) (x : Vec d) : List (Fin d) → ℝ :=
  fun l => iteratedCoordinateDerivative l (seedField d W) x

/-- The scaled gradient `ε ∂ₖ` read from a jet `v`. -/
noncomputable def sharpJetGradient {d : ℕ} (ε : ℝ) (v : List (Fin d) → ℝ) : Vec d :=
  fun k => ε * v [k]

/-- The scaled Hessian `ε ∂ₘ ∂ₙ` read from a jet `v`. -/
noncomputable def sharpJetHessian {d : ℕ} (ε : ℝ) (v : List (Fin d) → ℝ) :
    Fin d → Fin d → ℝ :=
  fun m n => ε * v [m, n]

/-- The clock density `1 + (δ/2) ∇·(a e₁)` as a function of the jet `v`. -/
noncomputable def sharpJetDensity {d : ℕ} (i : Fin d) (δ ε : ℝ) (v : List (Fin d) → ℝ) : ℝ :=
  1 + δ / 2 * coefficientDivergenceProfile i (sharpJetGradient ε v, sharpJetHessian ε v)

/-- The physical pair `(μ⁻¹ a, -(1/2) log μ)` as a function of the jet `v`. -/
noncomputable def sharpJetPair {d : ℕ} (i : Fin d) (δ ε : ℝ) (v : List (Fin d) → ℝ) :
    Mat d × ℝ :=
  ((sharpJetDensity i δ ε v)⁻¹ • coefficient i (sharpJetGradient ε v),
    -(1 / 2 : ℝ) * Real.log (sharpJetDensity i δ ε v))

/-- A constant multiple of a smooth function passes through its coordinate derivative. -/
private theorem coordinateDerivative_const_mul_smooth {d : ℕ} (c : ℝ) (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) (x : Vec d) :
    coordinateDerivative i (fun y => c * f y) x = c * coordinateDerivative i f x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul (hf.differentiable (by simp) x) c, ContinuousLinearMap.smul_apply,
    smul_eq_mul]

/-- The gradient of the scaled canonical seed at `x` is the scaled jet gradient. -/
private theorem gradient_scaled_eq_sharpJet {d : ℕ} (ε : ℝ) (W : NoiseSample d) (x : Vec d) :
    gradient (fun y => ε * seedField d W y) x = sharpJetGradient ε (sharpJet W x) := by
  funext k
  exact coordinateDerivative_const_mul_smooth ε (seedField d W) (contDiff_seedField d W) k x

/-- The Hessian of the scaled canonical seed at `x` is the scaled jet Hessian. -/
private theorem hessian_scaled_eq_sharpJet {d : ℕ} (ε : ℝ) (W : NoiseSample d) (x : Vec d) :
    (fun m n => coordinateDerivative m (coordinateDerivative n (fun y => ε * seedField d W y)) x) =
      sharpJetHessian ε (sharpJet W x) := by
  funext m n
  show coordinateDerivative m (coordinateDerivative n (fun y => ε * seedField d W y)) x =
    ε * sharpJet W x [m, n]
  have hinner : coordinateDerivative n (fun y => ε * seedField d W y) =
      fun z => ε * coordinateDerivative n (seedField d W) z :=
    funext fun z => coordinateDerivative_const_mul_smooth ε (seedField d W)
      (contDiff_seedField d W) n z
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative n (seedField d W)) :=
    contDiff_iteratedCoordinateDerivative (seedField d W) (contDiff_seedField d W) [n]
  rw [hinner]
  exact coordinateDerivative_const_mul_smooth ε _ hsmooth m x

/-- The gradient and Hessian of the scaled canonical seed at `x` are the scaled jet entries. -/
private theorem gradHess_scaled_eq {d : ℕ} (ε : ℝ) (W : NoiseSample d) (x : Vec d) :
    (gradient (fun y => ε * seedField d W y) x,
      fun m n => coordinateDerivative m (coordinateDerivative n (fun y => ε * seedField d W y)) x) =
      (sharpJetGradient ε (sharpJet W x), sharpJetHessian ε (sharpJet W x)) :=
  Prod.ext (gradient_scaled_eq_sharpJet ε W x) (hessian_scaled_eq_sharpJet ε W x)

/-- Under the gradient bound `1/4`, the Jacobian factor `1 + gᵢ` is nonzero. -/
private theorem jacobianFactor_ne_zero_of_gradient_le {d : ℕ} (i : Fin d) (g : Vec d)
    (hg : euclideanNorm g ≤ 1 / 4) : jacobianFactor i g ≠ 0 := by
  have hsq : g i * g i ≤ euclideanSq g := by
    unfold euclideanSq dot
    exact Finset.single_le_sum (fun j _ => mul_self_nonneg (g j)) (Finset.mem_univ i)
  have habs : |g i| ≤ euclideanNorm g := by
    unfold euclideanNorm
    apply Real.abs_le_sqrt
    rw [sq]
    exact hsq
  have hlo : -(1 / 4 : ℝ) ≤ g i := (abs_le.mp (habs.trans hg)).1
  have hpos : 0 < 1 + g i := by linarith
  exact hpos.ne'

/-- The clock density of the scaled canonical seed is the jet density at every point. -/
private theorem densityField_scaled_eq_sharpJet {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    densityField i δ (fun y => ε * seedField d W y) x =
      sharpJetDensity i δ ε (sharpJet W x) := by
  have hj : ∀ z, jacobianFactor i (gradient (fun y => ε * seedField d W y) z) ≠ 0 :=
    fun z => jacobianFactor_ne_zero_of_gradient_le i _ (hgrad W z)
  unfold densityField
  rw [divergence_coefficientField_column_eq_profile i _ (sharpSeed_contDiff ε W) hj x,
    gradHess_scaled_eq ε W x]
  rfl

/-- The physical coefficient of the scaled canonical seed is the jet coefficient. -/
theorem sharpPhysicalPair_apply_fst {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    (sharpPhysicalPair i δ ε hgrad hμ W).1 x = (sharpJetPair i δ ε (sharpJet W x)).1 := by
  show (densityField i δ (fun y => ε * seedField d W y) x)⁻¹ •
      coefficientField i (fun y => ε * seedField d W y) x =
    (sharpJetPair i δ ε (sharpJet W x)).1
  rw [densityField_scaled_eq_sharpJet i δ ε hgrad W x]
  unfold coefficientField
  rw [gradient_scaled_eq_sharpJet ε W x]
  rfl

/-- The physical potential of the scaled canonical seed is the jet potential. -/
theorem sharpPhysicalPair_apply_snd {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (W : NoiseSample d) (x : Vec d) :
    (sharpPhysicalPair i δ ε hgrad hμ W).2 x = (sharpJetPair i δ ε (sharpJet W x)).2 := by
  show -(1 / 2 : ℝ) * Real.log (densityField i δ (fun y => ε * seedField d W y) x) =
    (sharpJetPair i δ ε (sharpJet W x)).2
  rw [densityField_scaled_eq_sharpJet i δ ε hgrad W x]
  rfl

/-! ### Measurability of the jet functional -/

/-- A map into `Mat d` is Borel when every entry is measurable. -/
private theorem measurable_mat_of_entries {d : ℕ} {X : Type*} [MeasurableSpace X]
    {f : X → Mat d} (h : ∀ j k, Measurable fun x => f x j k) : Measurable f := by
  have hpi : @Measurable X (Fin d → Fin d → ℝ) inferInstance MeasurableSpace.pi f :=
    measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun k => h j k
  exact hpi.mono le_rfl (OpensMeasurableSpace.borel_le (α := Fin d → Fin d → ℝ))

/-- The jacobian factor is measurable in the gradient. -/
private theorem measurable_jacobianFactor_grad {d : ℕ} (i : Fin d) :
    Measurable (fun g : Vec d => jacobianFactor i g) := by
  unfold jacobianFactor
  exact measurable_const.add (measurable_pi_apply i)

/-- Each entry of the candidate inverse is measurable in the gradient. -/
private theorem measurable_inverseCandidate_entry {d : ℕ} (i j k : Fin d) :
    Measurable (fun g : Vec d => inverseCandidate i g j k) := by
  have hentry : ∀ g : Vec d, inverseCandidate i g j k =
      (if j = k then (1 : ℝ) else 0) - (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
    intro g
    simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
  have hk : Measurable (fun g : Vec d => g k) := measurable_pi_apply k
  simp only [hentry]
  exact measurable_const.sub ((measurable_jacobianFactor_grad i).inv.mul
    (hk.const_mul (unitVector i j)))

/-- The coefficient entry as the jacobian factor times a finite sum. -/
private theorem coefficient_entry_eq_sum_sharp {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Each coefficient entry is measurable in the gradient. -/
private theorem measurable_coefficient_entry {d : ℕ} (i j k : Fin d) :
    Measurable (fun g : Vec d => coefficient i g j k) := by
  simp only [coefficient_entry_eq_sum_sharp]
  exact (measurable_jacobianFactor_grad i).mul (Finset.measurable_sum Finset.univ fun l _ =>
    (measurable_inverseCandidate_entry i j l).mul (measurable_inverseCandidate_entry i k l))

/-- The coefficient matrix is measurable in the gradient. -/
private theorem measurable_coefficient_mat {d : ℕ} (i : Fin d) :
    Measurable (fun g : Vec d => coefficient i g) :=
  measurable_mat_of_entries fun j k => measurable_coefficient_entry i j k

/-- The scaled gradient is measurable in the jet. -/
private theorem measurable_sharpJetGradient {d : ℕ} (ε : ℝ) :
    Measurable (fun v : List (Fin d) → ℝ => sharpJetGradient ε v) := by
  refine measurable_pi_iff.mpr fun k => ?_
  have hk : Measurable (fun v : List (Fin d) → ℝ => v [k]) :=
    measurable_pi_apply ([k] : List (Fin d))
  show Measurable fun v : List (Fin d) → ℝ => ε * v [k]
  exact hk.const_mul ε

/-- The scaled Hessian is measurable in the jet. -/
private theorem measurable_sharpJetHessian {d : ℕ} (ε : ℝ) :
    Measurable (fun v : List (Fin d) → ℝ => sharpJetHessian ε v) := by
  refine measurable_pi_iff.mpr fun m => measurable_pi_iff.mpr fun n => ?_
  have hmn : Measurable (fun v : List (Fin d) → ℝ => v [m, n]) :=
    measurable_pi_apply ([m, n] : List (Fin d))
  show Measurable fun v : List (Fin d) → ℝ => ε * v [m, n]
  exact hmn.const_mul ε

/-- The divergence profile is measurable in its gradient and Hessian arguments. -/
private theorem measurable_coefficientDivergenceProfile {d : ℕ} (i : Fin d) :
    Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => coefficientDivergenceProfile i z) := by
  have hz1 : ∀ k : Fin d, Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => z.1 k) :=
    fun k => (measurable_pi_apply k).comp measurable_fst
  have hz2 : ∀ k n : Fin d, Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => z.2 k n) :=
    fun k n => (measurable_pi_apply n).comp ((measurable_pi_apply k).comp measurable_snd)
  have hden : Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => 1 + z.1 i) :=
    measurable_const.add (hz1 i)
  have hdiag : Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => ∑ k, z.2 k k) :=
    Finset.measurable_sum Finset.univ fun k _ => hz2 k k
  have hcross : Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => ∑ k, z.1 k * z.2 i k) :=
    Finset.measurable_sum Finset.univ fun k _ => (hz1 k).mul (hz2 i k)
  have hnorm : Measurable (fun z : Vec d × (Fin d → Fin d → ℝ) => euclideanSq z.1) := by
    unfold euclideanSq dot
    exact Finset.measurable_sum Finset.univ fun k _ => (hz1 k).mul (hz1 k)
  unfold coefficientDivergenceProfile
  simp only [div_eq_mul_inv]
  exact ((hdiag.neg).add ((measurable_const.mul hcross).mul hden.inv)).sub
    ((hnorm.mul (hz2 i i)).mul ((hden.pow_const 2).inv))

/-- The clock density of the jet is measurable. -/
private theorem measurable_sharpJetDensity {d : ℕ} (i : Fin d) (δ ε : ℝ) :
    Measurable (fun v : List (Fin d) → ℝ => sharpJetDensity i δ ε v) :=
  measurable_const.add (measurable_const.mul
    ((measurable_coefficientDivergenceProfile i).comp
      ((measurable_sharpJetGradient ε).prodMk (measurable_sharpJetHessian ε))))

/-- The jet physical pair is measurable in the jet. -/
private theorem measurable_sharpJetPair {d : ℕ} (i : Fin d) (δ ε : ℝ) :
    Measurable (fun v : List (Fin d) → ℝ => sharpJetPair i δ ε v) := by
  have hdens := measurable_sharpJetDensity i δ ε
  have hcoef : Measurable (fun v : List (Fin d) → ℝ => coefficient i (sharpJetGradient ε v)) :=
    (measurable_coefficient_mat i).comp (measurable_sharpJetGradient ε)
  exact ((hdens.inv).smul hcoef).prodMk
    ((Real.measurable_log.comp hdens).const_mul (-(1 / 2 : ℝ)))

/-- The jet of the canonical seed at a fixed point is measurable in the sample. -/
private theorem measurable_sharpJet {d : ℕ} (x : Vec d) :
    Measurable (fun W : NoiseSample d => sharpJet W x) :=
  measurable_pi_iff.mpr fun l => measurable_seedField_iteratedCoordinateDerivative d l x

/-- The physical pair of the scaled canonical seed is Borel on the sample space. -/
theorem measurable_sharpPhysicalPair {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)) :
    Measurable (sharpPhysicalPair i δ ε hgrad hμ) := by
  refine measurable_fieldPair_of_evaluations _ fun x => ?_
  have heq : (fun W : NoiseSample d => ((sharpPhysicalPair i δ ε hgrad hμ W).1 x,
      (sharpPhysicalPair i δ ε hgrad hμ W).2 x)) =
      fun W => sharpJetPair i δ ε (sharpJet W x) :=
    funext fun W => Prod.ext (sharpPhysicalPair_apply_fst i δ ε hgrad hμ W x)
      (sharpPhysicalPair_apply_snd i δ ε hgrad hμ W x)
  rw [heq]
  exact (measurable_sharpJetPair i δ ε).comp (measurable_sharpJet x)

/-! ### Stationarity through a countable dense evaluation -/

/-- The values of a field pair at the points of `D`. -/
private noncomputable def denseEval {d : ℕ} (D : Set (Vec d)) (ω : FieldPair d) :
    ↥D → Mat d × ℝ :=
  fun t => (ω.1 t.1, ω.2 t.1)

/-- The physical pair read from a jet array at the points of `D`. -/
private noncomputable def jetPairOnDense {d : ℕ} (i : Fin d) (δ ε : ℝ) (D : Set (Vec d))
    (v : ↥D × List (Fin d) → ℝ) : ↥D → Mat d × ℝ :=
  fun t => sharpJetPair i δ ε (fun l => v (t, l))

/-- The dense jet functional is measurable. -/
private theorem measurable_jetPairOnDense {d : ℕ} (i : Fin d) (δ ε : ℝ) (D : Set (Vec d)) :
    Measurable (jetPairOnDense i δ ε D) :=
  Measurable.of_eval fun t => (measurable_sharpJetPair i δ ε).comp
    (Measurable.of_eval fun l => measurable_pi_apply (t, l))

/-- Countably many dense point values of a field pair form a measurable embedding. -/
private theorem measurableEmbedding_denseEval {d : ℕ} {D : Set (Vec d)} (hDc : D.Countable)
    (hDd : Dense D) : MeasurableEmbedding (denseEval D) := by
  letI : Countable D := hDc.to_subtype
  letI : PolishSpace (Mat d) := inferInstanceAs (PolishSpace (Fin d → Fin d → ℝ))
  letI : PolishSpace C(Vec d, Mat d) := EinsteinRelation.Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  have hcont : Continuous (denseEval D) :=
    continuous_pi fun t => ((continuous_eval_const (t.1 : Vec d)).comp continuous_fst).prodMk
      ((continuous_eval_const (t.1 : Vec d)).comp continuous_snd)
  have hinj : Function.Injective (denseEval D) := by
    intro ω ω' h
    have h1 : ∀ t : D, ω.1 t.1 = ω'.1 t.1 ∧ ω.2 t.1 = ω'.2 t.1 := fun t =>
      ⟨congrArg Prod.fst (congrFun h t), congrArg Prod.snd (congrFun h t)⟩
    exact Prod.ext
      (ContinuousMap.injective_restrict hDd (ContinuousMap.ext fun t => (h1 t).1))
      (ContinuousMap.injective_restrict hDd (ContinuousMap.ext fun t => (h1 t).2))
  exact hcont.measurableEmbedding hinj

/-- Measures on a space are equal when their images under a measurable embedding are equal. -/
private theorem eq_of_map_eq_of_measurableEmbedding {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {E : X → Y} (hE : MeasurableEmbedding E) {μ ν : Measure X}
    (h : μ.map E = ν.map E) : μ = ν := by
  refine Measure.ext fun s hs => ?_
  have hEs : MeasurableSet (E '' s) := hE.measurableSet_image.2 hs
  have h' : μ.map E (E '' s) = ν.map E (E '' s) := by rw [h]
  rw [Measure.map_apply hE.measurable hEs, Measure.map_apply hE.measurable hEs,
    hE.injective.preimage_image] at h'
  exact h'

/-- Under a white-noise law, the physical pair of the scaled canonical seed has a stationary law.
The shifted pair is the jet functional of the shifted jet array, which has the same joint law at
the countably many points of a dense set by `identDistrib_seedField_jet_process_translate`. -/
theorem sharpPhysicalPair_isStationary {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) :
    IsStationary (P.map (sharpPhysicalPair i δ ε hgrad hμ)) := by
  unfold IsStationary
  intro x
  letI : IsProbabilityMeasure P := hP.1
  have hF := measurable_sharpPhysicalPair i δ ε hgrad hμ
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hE := measurableEmbedding_denseEval hDc hDd
  rw [Measure.map_map (EinsteinRelation.Probability.measurable_translate x) hF]
  refine eq_of_map_eq_of_measurableEmbedding hE ?_
  rw [Measure.map_map hE.measurable ((EinsteinRelation.Probability.measurable_translate x).comp hF),
    Measure.map_map hE.measurable hF]
  have hD1 : denseEval D ∘ (translate x ∘ sharpPhysicalPair i δ ε hgrad hμ) =
      jetPairOnDense i δ ε D ∘ (fun W : NoiseSample d => fun p : ↥D × List (Fin d) =>
        iteratedCoordinateDerivative p.2 (seedField d W) (x + (p.1 : Vec d))) :=
    funext fun W => funext fun t => Prod.ext
      (sharpPhysicalPair_apply_fst i δ ε hgrad hμ W (x + (t : Vec d)))
      (sharpPhysicalPair_apply_snd i δ ε hgrad hμ W (x + (t : Vec d)))
  have hD2 : denseEval D ∘ sharpPhysicalPair i δ ε hgrad hμ =
      jetPairOnDense i δ ε D ∘ (fun W : NoiseSample d => fun p : ↥D × List (Fin d) =>
        iteratedCoordinateDerivative p.2 (seedField d W) (p.1 : Vec d)) :=
    funext fun W => funext fun t => Prod.ext
      (sharpPhysicalPair_apply_fst i δ ε hgrad hμ W (t : Vec d))
      (sharpPhysicalPair_apply_snd i δ ε hgrad hμ W (t : Vec d))
  have hid := identDistrib_seedField_jet_process_translate hP ↥D (fun t : ↥D => (t : Vec d)) x
  rw [hD1, hD2]
  exact (hid.comp (measurable_jetPairOnDense i δ ε D)).map_eq

/-! ### Finite range through the jet arrays -/

/-- The jet array of the canonical seed on a set `V`, indexed by the points of `V` and ordered
coordinate lists. -/
private noncomputable def jetArray {d : ℕ} (V : Set (Vec d)) (W : NoiseSample d) :
    ↥V × List (Fin d) → ℝ :=
  fun p => iteratedCoordinateDerivative p.2 (seedField d W) (p.1 : Vec d)

/-- The physical pair is measurable from the σ-algebra generated by the jet array of `V` to the
local σ-algebra of `V`. -/
private theorem measurable_sharpPhysicalPair_comap {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (V : Set (Vec d)) :
    @Measurable (NoiseSample d) (FieldPair d)
      (MeasurableSpace.comap (jetArray V) MeasurableSpace.pi) (localSigma V)
      (sharpPhysicalPair i δ ε hgrad hμ) := by
  refine measurable_iff_comap_le.mpr ?_
  unfold localSigma
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun a => ?_
  rw [MeasurableSpace.comap_comp]
  have hφ : Measurable (fun v : ↥V × List (Fin d) → ℝ =>
      sharpJetPair i δ ε (fun l => v (a, l))) :=
    (measurable_sharpJetPair i δ ε).comp
      (Measurable.of_eval fun l => measurable_pi_apply (a, l))
  have hcomp : @Measurable (NoiseSample d) (Mat d × ℝ)
      (MeasurableSpace.comap (jetArray V) MeasurableSpace.pi) inferInstance
      (fun W => sharpJetPair i δ ε (fun l => jetArray V W (a, l))) :=
    hφ.comp (comap_measurable (jetArray V))
  have heq : (fun ω : FieldPair d => (ω.1 (a : Vec d), ω.2 (a : Vec d))) ∘
      sharpPhysicalPair i δ ε hgrad hμ =
      fun W => sharpJetPair i δ ε (fun l => jetArray V W (a, l)) :=
    funext fun W => Prod.ext (sharpPhysicalPair_apply_fst i δ ε hgrad hμ W (a : Vec d))
      (sharpPhysicalPair_apply_snd i δ ε hgrad hμ W (a : Vec d))
  rw [heq]
  exact hcomp.comap_le

/-- A set measurable for the local σ-algebra of `V` is the preimage of a set of the jet array. -/
private theorem exists_jetArray_preimage {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    (V : Set (Vec d)) {t : Set (FieldPair d)} (ht : MeasurableSet[localSigma V] t) :
    ∃ σ : Set (↥V × List (Fin d) → ℝ), MeasurableSet σ ∧
      sharpPhysicalPair i δ ε hgrad hμ ⁻¹' t = jetArray V ⁻¹' σ := by
  obtain ⟨σ, hσ, hpre⟩ := MeasurableSpace.measurableSet_comap.1
    (measurable_sharpPhysicalPair_comap i δ ε hgrad hμ V ht)
  exact ⟨σ, hσ, hpre.symm⟩

/-- The physical pair of the scaled canonical seed has joint finite range `4` under a white-noise
law. Observations on sets at Euclidean distance greater than `4` are functions of jet arrays on
those sets, and these jet arrays are independent by
`indepFun_seedField_jet_processes_of_separated`. -/
theorem sharpPhysicalPair_hasFiniteRange {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) :
    HasFiniteRange 4 (P.map (sharpPhysicalPair i δ ε hgrad hμ)) := by
  unfold HasFiniteRange
  intro U W _ _ hsep
  obtain ⟨s, hs, hdist⟩ := hsep
  letI : IsProbabilityMeasure P := hP.1
  have hF := measurable_sharpPhysicalPair i δ ε hgrad hμ
  have hsep' : ∀ a : ↥U, ∀ b : ↥W, (4 : ℝ) < euclideanNorm ((a : Vec d) - (b : Vec d)) :=
    fun a b => lt_of_lt_of_le hs (hdist a a.2 b b.2)
  have hind : ProbabilityTheory.IndepFun (jetArray U) (jetArray W) P :=
    indepFun_seedField_jet_processes_of_separated hP ↥U ↥W (fun a : ↥U => (a : Vec d))
      (fun b : ↥W => (b : Vec d)) hsep'
  rw [ProbabilityTheory.Indep_iff]
  intro t1 t2 h1 h2
  obtain ⟨σ1, hσ1, hpre1⟩ := exists_jetArray_preimage i δ ε hgrad hμ U h1
  obtain ⟨σ2, hσ2, hpre2⟩ := exists_jetArray_preimage i δ ε hgrad hμ W h2
  have ht1 : MeasurableSet t1 := EinsteinRelation.Probability.localSigma_le_borel U _ h1
  have ht2 : MeasurableSet t2 := EinsteinRelation.Probability.localSigma_le_borel W _ h2
  rw [Measure.map_apply hF (MeasurableSet.inter ht1 ht2), Measure.map_apply hF ht1,
    Measure.map_apply hF ht2, Set.preimage_inter, hpre1, hpre2]
  exact hind.measure_inter_preimage_eq_mul σ1 σ2 hσ1 hσ2

/-! ### The open environment-level propositions of `SharpEnvironmentLaw` -/

/-- The open proposition `SharpPhysicalPairMeasurable` holds for the physical pair. -/
theorem sharpPhysicalPairMeasurable_holds {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)) :
    SharpPhysicalPairMeasurable i δ ε hgrad hμ :=
  measurable_sharpPhysicalPair i δ ε hgrad hμ

/-- The open proposition `SharpPhysicalLawStationary` holds under a white-noise law. -/
theorem sharpPhysicalLawStationary_holds {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) :
    SharpPhysicalLawStationary i δ ε hgrad hμ P :=
  sharpPhysicalPair_isStationary i δ ε hgrad hμ hP

/-- The open proposition `SharpPhysicalLawFiniteRange` holds with range `4` under a white-noise
law. -/
theorem sharpPhysicalLawFiniteRange_holds {d : ℕ} (i : Fin d) (δ ε : ℝ)
    (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
      euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
    (hμ : ∀ (W : NoiseSample d) (x : Vec d),
      (3 / 4 : ℝ) ≤ densityField i δ (fun y => ε * seedField d W y) x ∧
      densityField i δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ))
    {P : Measure (NoiseSample d)} (hP : External.IsWhiteNoiseLaw P) :
    SharpPhysicalLawFiniteRange 4 i δ ε hgrad hμ P :=
  sharpPhysicalPair_hasFiniteRange i δ ε hgrad hμ hP

/-! ### The environment law -/

/-- The physical sharpness pair is an environment law. There are a white-noise law `P`, scales
`δ, ε > 0` with the gradient and density bounds of Step 1, a regularity constant `Λ₀ ≥ 1`, and a
range `r₀ = 4`, such that the law of the physical pair is an `EnvironmentLaw` and is almost surely
smooth. Source `paper/main.tex`, Proposition 7.1, lines 1202–1231. -/
theorem exists_sharp_environmentLaw (d : ℕ) (hd : 2 ≤ d) (hW : External.WhiteNoiseExistence d) :
    ∃ (Λ₀ r₀ δ ε : ℝ) (P : Measure (NoiseSample d)) (Q : EnvironmentLaw d Λ₀ r₀)
      (hgrad : ∀ (W : NoiseSample d) (x : Vec d),
        euclideanNorm (gradient (fun y => ε * seedField d W y) x) ≤ (1 / 4 : ℝ))
      (hμ : ∀ (W : NoiseSample d) (x : Vec d),
        (3 / 4 : ℝ) ≤ densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ∧
        densityField ⟨0, by omega⟩ δ (fun y => ε * seedField d W y) x ≤ (5 / 4 : ℝ)),
      0 < δ ∧ 0 < ε ∧ Q.measure = P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ) ∧
        ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := by
  obtain ⟨P, hP⟩ := hW
  obtain ⟨ε, δ, Λ, hgrad, hμ, hε, hδ, hΛ, hsmooth, hreg, -, -, -⟩ :=
    exists_sharp_physical_seed_step1 d ⟨0, by omega⟩ P hP
  letI : IsProbabilityMeasure P := hP.1
  have hF := measurable_sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ
  have hprob : IsProbabilityMeasure (P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)) :=
    inferInstance
  have hregLaw : ∀ᵐ ω ∂(P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)),
      IsRegular Λ ω :=
    (ae_map_iff hF.aemeasurable (measurableSet_isRegular_fieldPair Λ)).mpr (ae_of_all P hreg)
  have hsmoothLaw : ∀ᵐ ω ∂(P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ)),
      IsSmoothFieldPair ω :=
    (ae_map_iff hF.aemeasurable measurableSet_isSmoothFieldPair_fieldPair).mpr
      (ae_of_all P hsmooth)
  have hΛ1 : (1 : ℝ) ≤ Λ := by linarith
  have hr1 : (1 : ℝ) ≤ 4 := by norm_num
  refine ⟨Λ, 4, δ, ε, P,
    { measure := P.map (sharpPhysicalPair ⟨0, by omega⟩ δ ε hgrad hμ),
      probability := hprob,
      ellipticity_parameter := hΛ1,
      range_parameter := hr1,
      regular := hregLaw,
      stationary := sharpPhysicalPair_isStationary ⟨0, by omega⟩ δ ε hgrad hμ hP,
      finiteRange := sharpPhysicalPair_hasFiniteRange ⟨0, by omega⟩ δ ε hgrad hμ hP },
    hgrad, hμ, hδ, hε, rfl, hsmoothLaw⟩

end EinsteinRelation.Sharpness
