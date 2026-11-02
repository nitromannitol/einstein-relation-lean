import EinsteinFull.Work.W1.PhysicalCompactMollificationSupport
import EinsteinFull.Work.W1.PhysicalInteriorL2Support

/-! Compact-interior density in the literal physical zero-boundary H¹ core.
The constructed mollification sequence preserves the full distributional graph.
The real Hilbert realization uses its existing Euclidean gradient carrier.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

private def compactCoreGradientPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) : Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  ∑ j : Fin d, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).comp L).compLp (G j)

private theorem compactCoreGradientPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (compactCoreGradientPart m L) := by
  apply continuous_finset_sum
  intro j _
  let T := (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).comp L
  exact (T.compLpL 2 m).continuous.comp (continuous_apply j)

private theorem compactCoreGradientPart_coe {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) :
    ∀ᵐ x ∂m, ∀ j : Fin d, (compactCoreGradientPart m L G x) j = L (G j x) := by
  classical
  let f (j : Fin d) := ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).comp L).compLp (G j)
  have hsum (s : Finset (Fin d)) :
      ⇑(∑ j ∈ s, f j) =ᵐ[m] fun x => ∑ j ∈ s, f j x := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using! (Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 2 m)
    | @insert j s hj ih =>
      simp only [Finset.sum_insert hj]
      filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with x hx hi
      rw [hx]
      change f j x + (∑ k ∈ s, f k) x = _
      rw [hi]
  have hf : ∀ᵐ x ∂m, ∀ j : Fin d,
      f j x = L (G j x) • EuclideanSpace.single j (1 : ℝ) := by
    apply ae_all_iff.mpr
    intro j
    exact (((ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).comp L).coeFn_compLp (G j))
  filter_upwards [hsum Finset.univ, hf] with x hx hfx
  intro j
  change (WithLp.ofLp ((∑ k : Fin d, f k) x)) j = _
  rw [hx]
  change (PiLp.projₗ (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) j) (∑ k : Fin d, f k x) = _
  rw [map_sum]
  simp only [PiLp.projₗ_apply, hfx, PiLp.smul_apply, smul_eq_mul,
    EuclideanSpace.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

private theorem compactCoreWeightedGraph_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (v : Lp ℝ 2 (densityWeightedMeasure ρ))
    (g : Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ)) :
    (v, g) ∈ densityWeightedWeakGraphSet ρ hρ hρpos ↔
      ∀ j : Fin d, HasWeakPartialDerivative Set.univ j v (fun x => g x j) := by
  constructor
  · intro hp
    exact (densityWeightedGraphOfPair ρ hρ hρpos (v, g) hp).distributionalGradient
  · intro h
    let u : WeightedSobolevGraph (densityWeightedMeasure ρ) := {
      value := v
      weakGradient := g
      value_memLp := Lp.memLp v
      gradient_memLp := Lp.memLp g
      distributionalGradient := h
    }
    have heq : densityWeightedGraphPair ρ u = (v, g) :=
      Prod.ext (Lp.ext (Lp.memLp v).coeFn_toLp) (Lp.ext (Lp.memLp g).coeFn_toLp)
    rw [← heq]
    exact densityWeightedGraphPair_mem_weakGraphSet ρ hρ hρpos u

private def compactCoreGraphPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 m × (Fin d → Lp ℂ 2 m)) :
    Lp ℝ 2 m × Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  (L.compLp p.1, compactCoreGradientPart m L p.2)

private theorem compactCoreGraphPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (compactCoreGraphPart m L) :=
  ((L.compLpL 2 m).continuous.comp continuous_fst).prodMk
    ((compactCoreGradientPart_continuous m L).comp continuous_snd)

private theorem compactCoreGraphPart_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 (densityWeightedMeasure ρ) ×
      (Fin d → Lp ℂ 2 (densityWeightedMeasure ρ))) :
    compactCoreGraphPart (densityWeightedMeasure ρ) L p ∈ densityWeightedWeakGraphSet ρ hρ hρpos ↔
      ∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => L (p.1 x)) (fun x => L (p.2 j x)) := by
  rw [compactCoreWeightedGraph_mem_iff]
  apply forall_congr'
  intro j
  have hv : (volume : Measure (Vec d)) ≪ densityWeightedMeasure ρ := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp hρ.measurable).aemeasurable
    · exact Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hρpos x)).ne'
  exact hasWeakPartialDerivative_congr_of_absolutelyContinuous (densityWeightedMeasure ρ) hv j
    (L.coeFn_compLp p.1) ((compactCoreGradientPart_coe (densityWeightedMeasure ρ) L p.2).mono
      fun x hx => hx j)


private def compactCoreRealization {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam) ×
      (Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam)))
    (hp : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (p.1 x)) (fun x => L (p.2 j x))) : PhysicalH1Space hd lam :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
      (compactCoreGraphPart _ L p),
    (compactCoreGraphPart_mem_iff (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) L p).mpr hp⟩

private theorem compactCoreRealization_tendsto {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (L : ℂ →L[ℝ] ℝ)
    (p : ℕ → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam) ×
      (Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam)))
    (q : Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam) ×
      (Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam)))
    (hp : ∀ n j, HasWeakPartialDerivative univ j
      (fun x => L ((p n).1 x)) (fun x => L ((p n).2 j x)))
    (hq : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (q.1 x)) (fun x => L (q.2 j x)))
    (hlim : Tendsto p atTop (𝓝 q)) :
    Tendsto (fun n => compactCoreRealization hd lam L (p n) (hp n)) atTop
      (𝓝 (compactCoreRealization hd lam L q hq)) := by
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.tendsto _).comp
    (((compactCoreGraphPart_continuous _ L).tendsto q).comp hlim)

private theorem tendsto_pair_of_squared_error {d : ℕ} (m : Measure (Vec d))
    (v : ℕ → Lp ℂ 2 m) (H : ℕ → Fin d → Lp ℂ 2 m)
    (u : Lp ℂ 2 m) (G : Fin d → Lp ℂ 2 m)
    (h : Tendsto (fun n => ‖v n - u‖ ^ 2 + ∑ j, ‖H n j - G j‖ ^ 2)
      atTop (𝓝 0)) : Tendsto (fun n => (v n, H n)) atTop (𝓝 (u, G)) := by
  have hs := (Real.continuous_sqrt.tendsto 0).comp h
  simp only [Real.sqrt_zero] at hs
  have hv : Tendsto v atTop (𝓝 u) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hs
    apply Real.le_sqrt_of_sq_le
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hH (j) : Tendsto (fun n => H n j) atTop (𝓝 (G j)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hs
    apply Real.le_sqrt_of_sq_le
    exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖H n k - G k‖)
      (Finset.mem_univ j)).trans (le_add_of_nonneg_left (sq_nonneg _))
  exact hv.prodMk_nhds (tendsto_pi_nhds.mpr hH)

private theorem compactCore_value_injective {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u v : PhysicalH1Space hd lam)
    (hv : densityWeightedH1SpaceValue u = densityWeightedH1SpaceValue v) : u = v := by
  have hg : densityWeightedH1SpaceGradient u = densityWeightedH1SpaceGradient v := by
    apply Lp.ext
    exact densityWeightedGraph_gradient_ae_of_value_ae (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam)
      (physicalH1SpaceRepresentative hd lam u) (physicalH1SpaceRepresentative hd lam v)
      (by rw [show (physicalH1SpaceRepresentative hd lam u).value =
        densityWeightedH1SpaceValue u from rfl,
        show (physicalH1SpaceRepresentative hd lam v).value =
        densityWeightedH1SpaceValue v from rfl, hv])
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext hv hg

/-- The real and imaginary projections of every compact-interior complex physical
H¹ pair belong to the literal smooth interior core closure, with both value and
Euclidean gradient preserved. Only value support is assumed. -/
theorem physicalH1Graph_compact_projection_mem_zeroBoundary {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ)
    (u : Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam))
    (G : Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hu : IsPhysicalH1Graph _ (Or.inr ⟨firstCoordinateIndex hd, lam, rfl⟩) u G)
    {K U : Set (Vec d)} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (huK : ∀ᵐ x ∂EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam,
      x ∉ K → u x = 0)
    (L : ℂ →L[ℝ] ℝ) (hL : L = Complex.reCLM ∨ L = Complex.imCLM) :
    ∃ a : PhysicalH1Space hd lam, a ∈ physicalH1ZeroBoundary U hd lam ∧
      densityWeightedH1SpaceValue a =ᵐ[External.GantertSection7Support.physicalForceMeasure hd lam]
        (fun x => L (u x)) ∧
      (∀ᵐ x ∂External.GantertSection7Support.physicalForceMeasure hd lam, ∀ j,
        densityWeightedH1SpaceGradient a x j = L (G j x)) := by
  have hweak : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (u x)) (fun x => L (G j x)) := by
    rcases hL with rfl | rfl
    · exact hu.1
    · exact hu.2
  obtain ⟨ε, v, H, _, hp, hlim⟩ :=
    exists_physicalH1Graph_compact_interior_mollification_sequence
      (firstCoordinateIndex hd) lam u G hu hK hU hKU huK
  have hweakn (n) : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (v n x)) (fun x => L (H n j x)) := by
    rcases hL with rfl | rfl
    · exact (hp n).1.1
    · exact (hp n).1.2
  let a := compactCoreRealization hd lam L (u, G) hweak
  let an (n) := compactCoreRealization hd lam L (v n, H n) (hweakn n)
  have han (n) : an n ∈ physicalH1ZeroBoundary U hd lam := by
    let φ : Vec d → ℝ := fun x => L (spatialSmoothMollify (ε n) u x)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := L.contDiff.comp (hp n).2.2.2.1
    have hφc : HasCompactSupport φ := ((hp n).2.2.2.2.1).comp_left (map_zero L)
    have hφU : tsupport φ ⊆ U := by
      apply (tsupport_comp_subset (g := L) (map_zero L) _).trans
      exact (hp n).2.2.2.2.2
    have heq : an n = physicalH1SmoothTest hd lam φ hφ hφc := by
      apply compactCore_value_injective
      apply Lp.ext
      filter_upwards [L.coeFn_compLp (v n), (hp n).2.1,
        physicalH1SmoothTest_value hd lam φ hφ hφc] with x hx hy hz
      exact hx.trans ((congrArg L hy).trans hz.symm)
    rw [heq]
    exact physicalH1SmoothTest_mem_zeroBoundary U hd lam φ ⟨hφ, hφc, hφU⟩
  have ht : Tendsto an atTop (𝓝 a) := compactCoreRealization_tendsto hd lam L
    (fun n => (v n, H n)) (u, G) hweakn hweak
    (tendsto_pair_of_squared_error _ v H u G hlim)
  exact ⟨a, (physicalH1ZeroBoundary_isClosed U hd lam).mem_of_tendsto ht
    (Eventually.of_forall han), L.coeFn_compLp u, compactCoreGradientPart_coe _ L G⟩

/-- Every actual physical H¹ graph with compact value support strictly inside
an open domain lies in its literal smooth zero-boundary graph closure.
The gradient support is derived, and the full Euclidean graph is retained. -/
theorem physicalH1Space_compact_mem_zeroBoundary {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : PhysicalH1Space hd lam) {K U : Set (Vec d)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hfK : ∀ᵐ x ∂External.GantertSection7Support.physicalForceMeasure hd lam,
      x ∉ K → densityWeightedH1SpaceValue f x = 0) :
    f ∈ physicalH1ZeroBoundary U hd lam := by
  let m := EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam
  let v := densityWeightedH1SpaceValue f
  let g := densityWeightedH1SpaceGradient f
  let u : Lp ℂ 2 m := Complex.ofRealCLM.compLp v
  let G (j : Fin d) : Lp ℂ 2 m :=
    (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin d => ℝ) j)).compLp g
  have hv : u =ᵐ[m] fun x => (v x : ℂ) := Complex.ofRealCLM.coeFn_compLp v
  have hg (j) : G j =ᵐ[m] fun x => (g x j : ℂ) :=
    (Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : Fin d => ℝ) j)).coeFn_compLp g
  have hu : IsPhysicalH1Graph m (Or.inr ⟨firstCoordinateIndex hd, lam, rfl⟩) u G := by
    apply (isPhysicalH1Graph_iff_representatives m _ u G _ _ hv hg).mpr
    constructor
    · simpa only [Complex.ofReal_re] using!
        (physicalH1SpaceRepresentative hd lam f).distributionalGradient
    · intro j
      simp only [Complex.ofReal_im]
      exact ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, by
        intro φ _
        simp only [zero_mul, integral_zero, neg_zero]⟩
  have huK : ∀ᵐ x ∂m, x ∉ K → u x = 0 := by
    filter_upwards [hv, hfK] with x hx hKx hxK
    rw [hx, hKx hxK, Complex.ofReal_zero]
  obtain ⟨a, ha, hav, _⟩ := physicalH1Graph_compact_projection_mem_zeroBoundary
    hd lam u G hu hK hU hKU huK Complex.reCLM (Or.inl rfl)
  have heq : a = f := by
    apply compactCore_value_injective
    apply Lp.ext
    filter_upwards [hav, hv] with x hx hy
    simpa only [hy, Complex.reCLM_apply, Complex.ofReal_re] using hx
  exact heq ▸ ha

end EinsteinFull
