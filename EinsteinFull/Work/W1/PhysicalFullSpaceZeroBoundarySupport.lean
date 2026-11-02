import EinsteinFull.Work.W1.PhysicalH1CutoffExhaustionSupport
import EinsteinFull.Work.W1.PhysicalCompactZeroBoundaryCoreSupport

/-! Full-space smooth-core density in the actual physical H¹ graph.
Cutoff exhaustion converges in value and full Euclidean gradient; compact
mollification and closedness then remove the support restriction. -/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

private def fullSpaceGradientPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) : Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  ∑ j : Fin d, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).comp L).compLp (G j)

private theorem fullSpaceGradientPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (fullSpaceGradientPart m L) := by
  apply continuous_finset_sum
  intro j _
  let T := (ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single j (1 : ℝ))).comp L
  exact (T.compLpL 2 m).continuous.comp (continuous_apply j)

private theorem fullSpaceGradientPart_coe {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (G : Fin d → Lp ℂ 2 m) :
    ∀ᵐ x ∂m, ∀ j : Fin d, (fullSpaceGradientPart m L G x) j = L (G j x) := by
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

private theorem fullSpaceWeightedGraph_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
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

private def fullSpaceGraphPart {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 m × (Fin d → Lp ℂ 2 m)) :
    Lp ℝ 2 m × Lp (EuclideanSpace ℝ (Fin d)) 2 m :=
  (L.compLp p.1, fullSpaceGradientPart m L p.2)

private theorem fullSpaceGraphPart_continuous {d : ℕ} (m : Measure (Vec d)) (L : ℂ →L[ℝ] ℝ) :
    Continuous (fullSpaceGraphPart m L) :=
  ((L.compLpL 2 m).continuous.comp continuous_fst).prodMk
    ((fullSpaceGradientPart_continuous m L).comp continuous_snd)

private theorem fullSpaceGraphPart_mem_iff {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 (densityWeightedMeasure ρ) ×
      (Fin d → Lp ℂ 2 (densityWeightedMeasure ρ))) :
    fullSpaceGraphPart (densityWeightedMeasure ρ) L p ∈ densityWeightedWeakGraphSet ρ hρ hρpos ↔
      ∀ j : Fin d, HasWeakPartialDerivative Set.univ j
        (fun x => L (p.1 x)) (fun x => L (p.2 j x)) := by
  rw [fullSpaceWeightedGraph_mem_iff]
  apply forall_congr'
  intro j
  have hv : (volume : Measure (Vec d)) ≪ densityWeightedMeasure ρ := by
    apply withDensity_absolutelyContinuous'
    · exact (ENNReal.measurable_ofReal.comp hρ.measurable).aemeasurable
    · exact Filter.Eventually.of_forall fun x => (ENNReal.ofReal_pos.mpr (hρpos x)).ne'
  exact hasWeakPartialDerivative_congr_of_absolutelyContinuous (densityWeightedMeasure ρ) hv j
    (L.coeFn_compLp p.1) ((fullSpaceGradientPart_coe (densityWeightedMeasure ρ) L p.2).mono
      fun x hx => hx j)


private def fullSpaceRealization {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (L : ℂ →L[ℝ] ℝ)
    (p : Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam) ×
      (Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam)))
    (hp : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (p.1 x)) (fun x => L (p.2 j x))) : PhysicalH1Space hd lam :=
  ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm
      (fullSpaceGraphPart _ L p),
    (fullSpaceGraphPart_mem_iff (physicalForceWeight hd lam)
      (physicalForceWeight_continuous hd lam) (physicalForceWeight_pos hd lam) L p).mpr hp⟩

private theorem fullSpaceRealization_tendsto {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
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
    Tendsto (fun n => fullSpaceRealization hd lam L (p n) (hp n)) atTop
      (𝓝 (fullSpaceRealization hd lam L q hq)) := by
  apply tendsto_subtype_rng.mpr
  exact ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.continuous.tendsto _).comp
    (((fullSpaceGraphPart_continuous _ L).tendsto q).comp hlim)

private theorem fullSpace_value_injective {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
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

/-- Every real or imaginary projection of an arbitrary full physical complex
H¹ graph lies in the full-space smooth-core closure. No support restriction
is imposed on the datum, and the force is any signed real number. -/
theorem physicalH1Graph_projection_mem_zeroBoundary_univ {d : ℕ}
    (hd : 2 ≤ d) (lam : ℝ)
    (u : Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam))
    (G : Fin d → Lp ℂ 2 (EinsteinFull.physicalForceMeasure (firstCoordinateIndex hd) lam))
    (hu : IsPhysicalH1Graph _ (Or.inr ⟨firstCoordinateIndex hd, lam, rfl⟩) u G)
    (L : ℂ →L[ℝ] ℝ) (hL : L = Complex.reCLM ∨ L = Complex.imCLM) :
    ∃ a : PhysicalH1Space hd lam, a ∈ physicalH1ZeroBoundary univ hd lam ∧
      densityWeightedH1SpaceValue a =ᵐ[External.GantertSection7Support.physicalForceMeasure hd lam]
        (fun x => L (u x)) ∧
      (∀ᵐ x ∂External.GantertSection7Support.physicalForceMeasure hd lam, ∀ j,
        densityWeightedH1SpaceGradient a x j = L (G j x)) := by
  have hweak : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (u x)) (fun x => L (G j x)) := by
    rcases hL with rfl | rfl
    · exact hu.1
    · exact hu.2
  obtain ⟨χ, w, J, hχ, hw, _, _, hsupp, _, hwlim, hJlim, _⟩ :=
    physicalH1Graph_exists_compact_exhaustion _ _ u G hu
  have hweakn (n) : ∀ j, HasWeakPartialDerivative univ j
      (fun x => L (w n x)) (fun x => L (J n j x)) := by
    rcases hL with rfl | rfl
    · exact (hw n).1
    · exact (hw n).2
  let a := fullSpaceRealization hd lam L (u, G) hweak
  let an (n) := fullSpaceRealization hd lam L (w n, J n) (hweakn n)
  have han (n) : an n ∈ physicalH1ZeroBoundary univ hd lam := by
    obtain ⟨b, hb, hbv, _⟩ := physicalH1Graph_compact_projection_mem_zeroBoundary
      hd lam (w n) (J n) (hw n) (hχ n).2.isCompact isOpen_univ
      (subset_univ _) ((hsupp n).mono fun x hx hxoff => (hx hxoff).1) L hL
    have heq : an n = b := by
      apply fullSpace_value_injective
      apply Lp.ext
      filter_upwards [L.coeFn_compLp (w n), hbv] with x hx hy
      exact hx.trans hy.symm
    rw [heq]
    exact hb
  have ht : Tendsto an atTop (𝓝 a) := fullSpaceRealization_tendsto hd lam L
    (fun n => (w n, J n)) (u, G) hweakn hweak
    (hwlim.prodMk_nhds (tendsto_pi_nhds.mpr hJlim))
  exact ⟨a, (physicalH1ZeroBoundary_isClosed univ hd lam).mem_of_tendsto ht
    (Eventually.of_forall han), L.coeFn_compLp u, fullSpaceGradientPart_coe _ L G⟩

/-- Every actual real physical H¹ element belongs to the full-space closure
of smooth compactly supported tests, with the existing Euclidean gradient. -/
theorem physicalH1Space_mem_zeroBoundary_univ {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (f : PhysicalH1Space hd lam) : f ∈ physicalH1ZeroBoundary univ hd lam := by
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
  obtain ⟨a, ha, hav, _⟩ := physicalH1Graph_projection_mem_zeroBoundary_univ
    hd lam u G hu Complex.reCLM (Or.inl rfl)
  have heq : a = f := by
    apply fullSpace_value_injective
    apply Lp.ext
    filter_upwards [hav, hv] with x hx hy
    simpa only [hy, Complex.reCLM_apply, Complex.ofReal_re] using hx
  exact heq ▸ ha

end EinsteinFull
