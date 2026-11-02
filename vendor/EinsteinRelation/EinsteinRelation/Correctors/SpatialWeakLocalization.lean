import EinsteinRelation.Correctors.SpatialWeakProduct

/-! # Compact localization of spatial weak equations

Source: `paper/main.tex:903–928`. The conditioned equations are valid
on a ball depending on the conditioning center. A smooth weight supported
strictly inside that ball extends the weighted equation to the whole
space. No weak equation for an unweighted field outside its domain is
assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- A derivative of a spatial test is another test on the same domain.
Source: `paper/main.tex:916–928`. -/
theorem isSpatialTest_coordinateDerivative {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d) :
    IsSpatialTest U (coordinateDerivative j ψ) := by
  refine ⟨(contDiff_infty_iff_fderiv.mp hψ.1).2.clm_apply contDiff_const,
    hψ.2.1.fderiv_apply ℝ (unitVector j), ?_⟩
  apply Set.Subset.trans ?_ hψ.2.2
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hxs
  have hz := fderiv_of_notMem_tsupport (𝕜 := ℝ) hxs
  exact hx (by simp only [coordinateDerivative, hz, ContinuousLinearMap.zero_apply])

private theorem derivative_zero_outside {d : ℕ} {U : Set (Vec d)}
    {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d)
    {x : Vec d} (hx : x ∉ U) : coordinateDerivative j ψ x = 0 := by
  have hx' : x ∉ tsupport ψ := fun h => hx (hψ.2.2 h)
  simp only [coordinateDerivative, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx',
    ContinuousLinearMap.zero_apply]

private theorem setIntegral_mul_test {d : ℕ} {U : Set (Vec d)}
    (f : Vec d → ℝ) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ x in U, f x * ψ x) = ∫ x, f x * ψ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ψ x = 0 := by
    by_contra hzero
    exact hx (hψ.2.2 (subset_tsupport ψ hzero))
  rw [hz, mul_zero]

private theorem setIntegral_mul_test_derivative {d : ℕ} {U : Set (Vec d)}
    (f : Vec d → ℝ) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) (j : Fin d) :
    (∫ x in U, f x * coordinateDerivative j ψ x) =
      ∫ x, f x * coordinateDerivative j ψ x :=
  setIntegral_mul_test f (isSpatialTest_coordinateDerivative hψ j)

private theorem setIntegral_dot_test_gradient {d : ℕ} {U : Set (Vec d)}
    (F : Vec d → Vec d) {ψ : Vec d → ℝ} (hψ : IsSpatialTest U ψ) :
    (∫ x in U, dot (F x) (gradient ψ x)) = ∫ x, dot (F x) (gradient ψ x) := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  simp only [dot, gradient, derivative_zero_outside hψ _ hx, mul_zero, Finset.sum_const_zero]

/-- Restriction to a smaller spatial domain preserves a weak partial
derivative. Source: `paper/main.tex:903–928`. -/
theorem hasWeakPartialDerivative_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {j : Fin d} {f g : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g) :
    HasWeakPartialDerivative V j f g := by
  refine ⟨h.1.mono_set hVU, h.2.1.mono_set hVU, ?_⟩
  intro ψ hψ
  have hψU : IsSpatialTest U ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hVU⟩
  have heq := h.2.2 ψ hψU
  rw [setIntegral_mul_test_derivative f hψU j, setIntegral_mul_test g hψU] at heq
  rwa [setIntegral_mul_test_derivative f hψ j, setIntegral_mul_test g hψ]

/-- Restriction of a weak gradient. Source: `paper/main.tex:903–928`. -/
theorem hasWeakGradient_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {f : Vec d → ℝ} {G : Vec d → Vec d} (h : HasWeakGradient U f G) :
    HasWeakGradient V f G := fun j => hasWeakPartialDerivative_mono hVU (h j)

/-- Restriction of a spatial weak divergence.
Source: `paper/main.tex:903–928`. -/
theorem hasWeakDivergence_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {F : Vec d → Vec d} {h : Vec d → ℝ} (hF : HasWeakDivergence U F h) :
    HasWeakDivergence V F h := by
  refine ⟨fun j => (hF.1 j).mono_set hVU, hF.2.1.mono_set hVU, ?_⟩
  intro ψ hψ
  have hψU : IsSpatialTest U ψ := ⟨hψ.1, hψ.2.1, hψ.2.2.trans hVU⟩
  have heq := hF.2.2 ψ hψU
  rw [setIntegral_dot_test_gradient F hψU, setIntegral_mul_test h hψU] at heq
  rwa [setIntegral_dot_test_gradient F hψ, setIntegral_mul_test h hψ]

/-- Restriction of spatial weak row divergence.
Source: `paper/main.tex:903–928`. -/
theorem hasWeakRowDivergence_mono {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {S : Vec d → Mat d} {g : Vec d → Vec d} (h : HasWeakRowDivergence U S g) :
    HasWeakRowDivergence V S g := fun j => hasWeakDivergence_mono hVU (h j)

private theorem integrable_mul_test {d : ℕ} {U : Set (Vec d)}
    {f ψ : Vec d → ℝ} (hf : LocallyIntegrableOn f U volume) (hψ : IsSpatialTest U ψ) :
    Integrable (fun x => f x * ψ x) volume := by
  have hs : Function.support (fun x => f x * ψ x) ⊆ U := by
    intro x hx
    exact hψ.2.2 (subset_tsupport ψ ((mul_ne_zero_iff.mp hx).2))
  exact (integrableOn_iff_integrable_of_support_subset hs).mp
    (integrableOn_mul_spatialTest hf hψ)

private theorem integrable_mul_compact {d : ℕ} {f ψ : Vec d → ℝ}
    (hf : Integrable f volume) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => f x * ψ x) volume := by
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuous hψ
  exact hf.mul_bdd hψ.measurable.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- A compact smooth weight supported inside the original domain yields
a genuine whole-space weak derivative, including the weight derivative.
Source: `paper/main.tex:916–928`. -/
theorem hasWeakPartialDerivative_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {j : Fin d} {f g w : Vec d → ℝ} (h : HasWeakPartialDerivative U j f g)
    (hw : IsSpatialTest U w) :
    HasWeakPartialDerivative Set.univ j (fun x => w x * f x)
      (fun x => w x * g x + f x * coordinateDerivative j w x) := by
  have hfw : Integrable (fun x => w x * f x) volume := by
    simpa only [mul_comm] using integrable_mul_test h.1 hw
  have hgw : Integrable (fun x => w x * g x) volume := by
    simpa only [mul_comm] using integrable_mul_test h.2.1 hw
  have hfdw := integrable_mul_test h.1 (isSpatialTest_coordinateDerivative hw j)
  refine ⟨hfw.locallyIntegrable.locallyIntegrableOn _,
    (hgw.add hfdw).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  rw [Measure.restrict_univ]
  have hA := integrable_mul_compact hfw
    (isSpatialTest_coordinateDerivative hψ j).1.continuous
    (isSpatialTest_coordinateDerivative hψ j).2.1
  have hB := integrable_mul_compact hfdw hψ.1.continuous hψ.2.1
  have hC := integrable_mul_compact hgw hψ.1.continuous hψ.2.1
  have ht : IsSpatialTest U (fun x => w x * ψ x) :=
    ⟨hw.1.mul hψ.1, hw.2.1.mul_right, (tsupport_mul_subset_left).trans hw.2.2⟩
  have heq := h.2.2 _ ht
  rw [setIntegral_mul_test_derivative f ht j, setIntegral_mul_test g ht] at heq
  have hsplit : (∫ x, w x * f x * coordinateDerivative j ψ x) +
      (∫ x, f x * coordinateDerivative j w x * ψ x) = -(∫ x, w x * g x * ψ x) := by
    rw [← integral_add hA hB]
    calc
      _ = ∫ x, f x * coordinateDerivative j (fun y => w y * ψ y) x := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          dsimp only
          rw [coordinateDerivative_mul j w ψ x
            (hw.1.differentiable (by simp) x) (hψ.1.differentiable (by simp) x)]
          ring
      _ = -(∫ x, g x * (w x * ψ x)) := heq
      _ = _ := by congr 1; apply integral_congr_ae; exact Filter.Eventually.of_forall fun x => by ring
  have hrhs : (∫ x, (w x * g x + f x * coordinateDerivative j w x) * ψ x) =
      (∫ x, w x * g x * ψ x) + ∫ x, f x * coordinateDerivative j w x * ψ x := by
    simp_rw [add_mul]
    exact integral_add hC hB
  rw [hrhs]
  linarith only [hsplit]

/-- Compact localization of an actual spatial weak gradient.
Source: `paper/main.tex:916–928`. -/
theorem hasWeakGradient_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {f w : Vec d → ℝ} {G : Vec d → Vec d} (h : HasWeakGradient U f G)
    (hw : IsSpatialTest U w) :
    HasWeakGradient Set.univ (fun x => w x * f x)
      (fun x j => w x * G x j + f x * coordinateDerivative j w x) :=
  fun j => hasWeakPartialDerivative_mul_spatialTest (h j) hw

/-- Compact localization of a spatial weak divergence, including its
weight-gradient contraction. Source: `paper/main.tex:916–928`. -/
theorem hasWeakDivergence_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → Vec d} {h w : Vec d → ℝ} (hF : HasWeakDivergence U F h)
    (hw : IsSpatialTest U w) :
    HasWeakDivergence Set.univ (fun x j => w x * F x j)
      (fun x => w x * h x + dot (F x) (gradient w x)) := by
  have hwF (j : Fin d) : Integrable (fun x => w x * F x j) volume := by
    simpa only [mul_comm] using integrable_mul_test (hF.1 j) hw
  have hwh : Integrable (fun x => w x * h x) volume := by
    simpa only [mul_comm] using integrable_mul_test hF.2.1 hw
  have hdw : Integrable (fun x => dot (F x) (gradient w x)) volume :=
    integrable_finset_sum Finset.univ fun j _ =>
      integrable_mul_test (hF.1 j) (isSpatialTest_coordinateDerivative hw j)
  refine ⟨fun j => (hwF j).locallyIntegrable.locallyIntegrableOn _,
    (hwh.add hdw).locallyIntegrable.locallyIntegrableOn _, ?_⟩
  intro ψ hψ
  rw [Measure.restrict_univ]
  have hA : Integrable (fun x => dot (fun j => w x * F x j) (gradient ψ x)) volume :=
    integrable_finset_sum Finset.univ fun j _ => integrable_mul_compact (hwF j)
      (isSpatialTest_coordinateDerivative hψ j).1.continuous
      (isSpatialTest_coordinateDerivative hψ j).2.1
  have hB := integrable_mul_compact hdw hψ.1.continuous hψ.2.1
  have hC := integrable_mul_compact hwh hψ.1.continuous hψ.2.1
  have ht : IsSpatialTest U (fun x => w x * ψ x) :=
    ⟨hw.1.mul hψ.1, hw.2.1.mul_right, (tsupport_mul_subset_left).trans hw.2.2⟩
  have heq := hF.2.2 _ ht
  rw [setIntegral_dot_test_gradient F ht, setIntegral_mul_test h ht] at heq
  have hprod (x : Vec d) : dot (F x) (gradient (fun y => w y * ψ y) x) =
      dot (fun j => w x * F x j) (gradient ψ x) + dot (F x) (gradient w x) * ψ x := by
    calc
      _ = ∑ j : Fin d, (w x * F x j * coordinateDerivative j ψ x +
          F x j * coordinateDerivative j w x * ψ x) := by
        apply Finset.sum_congr rfl
        intro j _
        change F x j * coordinateDerivative j (fun y => w y * ψ y) x = _
        rw [coordinateDerivative_mul j w ψ x
          (hw.1.differentiable (by simp) x) (hψ.1.differentiable (by simp) x)]
        ring
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul]; rfl
  have hsplit : (∫ x, dot (fun j => w x * F x j) (gradient ψ x)) +
      (∫ x, dot (F x) (gradient w x) * ψ x) = -(∫ x, w x * h x * ψ x) := by
    rw [← integral_add hA hB]
    calc
      _ = ∫ x, dot (F x) (gradient (fun y => w y * ψ y) x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (hprod x).symm)
      _ = -(∫ x, h x * (w x * ψ x)) := heq
      _ = _ := by congr 1; apply integral_congr_ae; exact Filter.Eventually.of_forall fun x => by ring
  have hrhs : (∫ x, (w x * h x + dot (F x) (gradient w x)) * ψ x) =
      (∫ x, w x * h x * ψ x) + ∫ x, dot (F x) (gradient w x) * ψ x := by
    simp_rw [add_mul]
    exact integral_add hC hB
  rw [hrhs]
  linarith only [hsplit]

/-- Compact localization preserves the row-divergence convention, with
exactly the matrix-gradient contraction defining `K_R`.
Source: `paper/main.tex:916–928`. -/
theorem hasWeakRowDivergence_mul_spatialTest {d : ℕ} {U : Set (Vec d)}
    {S : Vec d → Mat d} {g : Vec d → Vec d} {w : Vec d → ℝ}
    (hS : HasWeakRowDivergence U S g) (hw : IsSpatialTest U w) :
    HasWeakRowDivergence Set.univ (fun x j k => w x * S x j k)
      (fun x j => w x * g x j + ((S x).mulVec (gradient w x)) j) :=
  fun j => hasWeakDivergence_mul_spatialTest (hS j) hw

end EinsteinRelation.Correctors
