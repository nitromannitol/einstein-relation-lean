import EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.WithDensity

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- For a continuous, strictly positive density, Lebesgue and weighted almost-everywhere
equality agree. -/
theorem ae_withDensity_iff_volume_of_continuous_pos {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (p : Vec d → Prop) :
    (∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x)), p x) ↔
      ∀ᵐ x ∂volume, p x := by
  have hEq := ae_withDensity_iff (μ := volume) (p := p)
    (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρ.measurable)
  change (∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (ρ x)), p x) ↔
    ∀ᵐ x ∂volume, p x
  rw [hEq]
  constructor
  · intro hp
    filter_upwards [hp] with x hx
    exact hx (ne_of_gt (ENNReal.ofReal_pos.mpr (hρpos x)))
  · intro hp
    filter_upwards [hp] with x hx
    exact fun _ => hx

/-- Weighted `L²` membership for a strictly positive continuous density implies local
integrability against Lebesgue measure. -/
theorem memLp_two_locallyIntegrable_volume_of_density {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (f : Vec d → E)
    (hμlf : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hf : MemLp f 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    LocallyIntegrable f volume := by
  let w : Vec d → ℝ≥0∞ := fun x => ENNReal.ofReal (ρ x)
  let μ : Measure (Vec d) := volume.withDensity w
  letI : IsLocallyFiniteMeasure μ := hμlf
  have hwmeas : Measurable w := ENNReal.measurable_ofReal.comp hρ.measurable
  intro x
  let K : Set (Vec d) := Metric.closedBall x 1
  have hK : IsCompact K := by simpa [K] using (isCompact_closedBall x (1 : ℝ))
  have hKnonempty : K.Nonempty := ⟨x, by simp [K]⟩
  obtain ⟨z, hzK, hzmin⟩ := hK.exists_isMinOn hKnonempty hρ.continuousOn
  have hzmin' : ∀ y ∈ K, ρ z ≤ ρ y := by
    simpa [IsMinOn, IsMinFilter] using hzmin
  let c : ℝ := ρ z / 2
  have hc : 0 < c := by
    dsimp [c]
    linarith [hρpos z]
  have hcρ : ∀ y ∈ K, c ≤ ρ y := by
    intro y hy
    dsimp [c]
    have hmin := hzmin' y hy
    linarith [hρpos z]
  have hKfin : μ K < ∞ := hK.measure_lt_top
  have hKlp : MemLp f 2 (μ.restrict K) := hf.restrict K
  letI : IsFiniteMeasure (μ.restrict K) := ⟨by simpa using hKfin⟩
  have hKlp1 : MemLp f 1 (μ.restrict K) :=
    hKlp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hKint : Integrable f (μ.restrict K) := by
    rw [← memLp_one_iff_integrable]
    exact hKlp1
  have hKmeas : MeasurableSet K := hK.isClosed.measurableSet
  have hKint' : Integrable f ((volume.restrict K).withDensity w) := by
    change Integrable f ((volume.withDensity w).restrict K) at hKint
    rw [restrict_withDensity hKmeas] at hKint
    exact hKint
  have hwfinite : ∀ᵐ y ∂volume.restrict K, w y < ∞ := by
    filter_upwards [] with y
    simp [w]
  have hweighted : Integrable (fun y => (w y).toReal • f y) (volume.restrict K) :=
    (integrable_withDensity_iff_integrable_smul' hwmeas hwfinite).mp hKint'
  have hweightedρ : Integrable (fun y => ρ y • f y) (volume.restrict K) := by
    refine hweighted.congr ?_
    filter_upwards [] with y
    simp [w, ENNReal.toReal_ofReal, (hρpos y).le]
  have hinvCont : Continuous (fun y => (ρ y)⁻¹) :=
    hρ.inv₀ (fun y => ne_of_gt (hρpos y))
  have hinvMeas : AEStronglyMeasurable (fun y => (ρ y)⁻¹) (volume.restrict K) :=
    hinvCont.measurable.aestronglyMeasurable
  have hinvBound : ∀ᵐ y ∂volume.restrict K, ‖(ρ y)⁻¹‖ ≤ c⁻¹ := by
    filter_upwards [ae_restrict_mem hKmeas] with y hy
    have hρy : c ≤ ρ y := hcρ y hy
    calc
      ‖(ρ y)⁻¹‖ = (ρ y)⁻¹ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos y))]
      _ ≤ c⁻¹ := by simpa only [one_div] using one_div_le_one_div_of_le hc hρy
  have hKvolumeInt : Integrable f (volume.restrict K) := by
    refine (hweightedρ.bdd_smul c⁻¹ hinvMeas hinvBound).congr ?_
    filter_upwards [] with y
    simp [smul_smul, inv_mul_cancel₀ (ne_of_gt (hρpos y))]
  have hKnhds : K ∈ nhds x := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1))
    intro y hy
    have hy' : dist y x < (1 : ℝ) := by
      simpa [Metric.mem_ball, dist_comm] using hy
    simpa [K, Metric.mem_closedBall, dist_comm] using hy'.le
  exact ⟨K, hKnhds, hKvolumeInt⟩

/-- The existing weak-gradient graph is exactly inhabited by the source data consisting of
weighted `L²` representatives and the compact-test distributional identity. Its local
integrability fields are derived from weighted `L²` and positivity of the density. -/
noncomputable def weightedSobolevGraph_mk_of_density_distributionalData {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : Vec d → ℝ) (g : Vec d → EuclideanSpace ℝ (Fin d))
    (hu : MemLp u 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hg : MemLp g 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hidentity : ∀ i : Fin d, ∀ φ : Vec d → ℝ, IsSpatialTest Set.univ φ →
      (∫ x in Set.univ, u x * coordinateDerivative i φ x) =
        -(∫ x in Set.univ, (WithLp.ofLp (g x)) i * φ x)) :
    WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  letI : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
    IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have huLocal := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos u
    (inferInstance : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) hu
  have hgLocal := memLp_two_locallyIntegrable_volume_of_density ρ hρ hρpos g
    (inferInstance : IsLocallyFiniteMeasure
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) hg
  have huOn : LocallyIntegrableOn u Set.univ volume := locallyIntegrableOn_univ.mpr huLocal
  have hgAestrongly : AEStronglyMeasurable g volume := hgLocal.aestronglyMeasurable
  refine ⟨u, g, hu, hg, ?_⟩
  intro i
  have hcoordinateContinuous : Continuous
      (fun z : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp z) i) :=
    (continuous_apply i).comp (PiLp.continuous_ofLp 2 _)
  have hcoordinateAestrongly : AEStronglyMeasurable
      (fun x => (WithLp.ofLp (g x)) i) volume :=
    hcoordinateContinuous.comp_aestronglyMeasurable hgAestrongly
  have hcoordinateNorm : ∀ x, ‖(WithLp.ofLp (g x)) i‖ ≤ ‖g x‖ := by
    intro x
    simpa using (PiLp.norm_apply_le (g x) i)
  have hcoordinateLocal : LocallyIntegrable
      (fun x => (WithLp.ofLp (g x)) i) volume :=
    hgLocal.mono hcoordinateAestrongly (ae_of_all _ hcoordinateNorm)
  have hcoordinateOn : LocallyIntegrableOn
      (fun x => (WithLp.ofLp (g x)) i) Set.univ volume :=
    locallyIntegrableOn_univ.mpr hcoordinateLocal
  exact ⟨huOn, hcoordinateOn, hidentity i⟩

/-- A compact-test distributional identity determines its locally integrable weak gradient. -/
theorem weakGradients_ae_eq_of_value_ae_eq {d : ℕ} {f f' : Vec d → ℝ}
    {g h : Vec d → Vec d} (hff' : f =ᵐ[volume] f')
    (hg : HasWeakGradient Set.univ f g) (hh : HasWeakGradient Set.univ f' h) :
    g =ᵐ[volume] h := by
  have hcoord : ∀ i, ∀ᵐ x ∂volume, g x i = h x i := by
    intro i
    apply ae_eq_of_integral_contDiff_smul_eq
    · exact (locallyIntegrableOn_univ.mp (hg i).2.1)
    · exact (locallyIntegrableOn_univ.mp (hh i).2.1)
    · intro φ hφ hφc
      have hgi := (hg i).2.2 φ ⟨hφ, hφc, Set.subset_univ _⟩
      have hhi := (hh i).2.2 φ ⟨hφ, hφc, Set.subset_univ _⟩
      simp only [setIntegral_univ] at hgi hhi
      have hval : (fun x => f x * coordinateDerivative i φ x) =ᵐ[volume]
          (fun x => f' x * coordinateDerivative i φ x) := by
        filter_upwards [hff'] with x hx
        rw [hx]
      have hvalint := integral_congr_ae hval
      have hgradint : (∫ x, g x i * φ x ∂volume) =
          ∫ x, h x i * φ x ∂volume := by
        linarith
      simpa only [smul_eq_mul, mul_comm] using hgradint
  filter_upwards [ae_all_iff.2 hcoord] with x hx
  funext i
  exact hx i

/-- For a positive continuous density, equality of graph values in weighted `L²` determines
the graph gradients in weighted `L²`. -/
theorem densityWeightedGraph_gradient_ae_of_value_ae {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u v : WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (huv : u.value =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] v.value) :
    u.weakGradient =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] v.weakGradient := by
  have huvVol : u.value =ᵐ[volume] v.value :=
    (ae_withDensity_iff_volume_of_continuous_pos ρ hρ hρpos _).mp huv
  have hgradVolCoord := weakGradients_ae_eq_of_value_ae_eq huvVol
    u.distributionalGradient v.distributionalGradient
  have hgradVol : (fun x => WithLp.ofLp (u.weakGradient x)) =ᵐ[volume]
      fun x => WithLp.ofLp (v.weakGradient x) := hgradVolCoord
  have hgradDensity : (fun x => WithLp.ofLp (u.weakGradient x)) =ᵐ[
      volume.withDensity (fun x => ENNReal.ofReal (ρ x))] fun x =>
        WithLp.ofLp (v.weakGradient x) :=
    (ae_withDensity_iff_volume_of_continuous_pos ρ hρ hρpos _).mpr hgradVol
  filter_upwards [hgradDensity] with x hx
  exact WithLp.ofLp_injective 2 (by simpa using hx)

/-- The weak `H¹` quotient identifies graph representatives with the same weighted `L²` value. -/
def densityWeightedH1Setoid {d : ℕ} (ρ : Vec d → ℝ) :
    Setoid (WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) where
  r u v := u.value =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] v.value
  iseqv := {
    refl := fun _ => Filter.EventuallyEq.rfl
    symm := fun {_ _} h => h.symm
    trans := fun {_ _ _} h₁ h₂ => h₁.trans h₂
  }

/-- Equivalence classes of the weighted weak-gradient graph. -/
abbrev DensityWeightedH1 {d : ℕ} (ρ : Vec d → ℝ) :=
  Quotient (densityWeightedH1Setoid ρ)

/-- The weighted `L²` value represented by an equivalence class. -/
noncomputable def densityWeightedH1Value {d : ℕ} (ρ : Vec d → ℝ) :
    DensityWeightedH1 ρ → Lp ℝ 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
  Quotient.lift (fun u => u.value_memLp.toLp u.value) (by
    intro u v huv
    apply Lp.ext
    have hu := u.value_memLp.coeFn_toLp
    have hv := v.value_memLp.coeFn_toLp
    filter_upwards [hu, huv, hv] with x hu hx hv
    exact hu.trans (hx.trans hv.symm))

/-- The quotient value map is injective into weighted `L²`. -/
theorem densityWeightedH1Value_injective {d : ℕ} (ρ : Vec d → ℝ) :
    Function.Injective (densityWeightedH1Value ρ) := by
  intro q q' h
  revert h
  refine Quotient.inductionOn₂ q q' ?_
  intro u v h
  apply Quotient.sound
  have hLp : u.value_memLp.toLp u.value = v.value_memLp.toLp v.value := by
    simpa [densityWeightedH1Value] using h
  exact (MemLp.toLp_eq_toLp_iff u.value_memLp v.value_memLp).mp hLp

/-- The weighted `L²` weak gradient represented by a quotient class. -/
noncomputable def densityWeightedH1Gradient {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) :
    DensityWeightedH1 ρ → Lp (EuclideanSpace ℝ (Fin d)) 2
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) :=
  Quotient.lift (fun u => u.gradient_memLp.toLp u.weakGradient) (by
    intro u v huv
    apply Lp.ext
    have hgrad := densityWeightedGraph_gradient_ae_of_value_ae ρ hρ hρpos u v huv
    have hu := u.gradient_memLp.coeFn_toLp
    have hv := v.gradient_memLp.coeFn_toLp
    filter_upwards [hu, hgrad, hv] with x hu hx hv
    exact hu.trans (hx.trans hv.symm))

/-- The weighted `H¹` domain embedded in the actual weighted `L²` space. -/
def weightedH1Domain {d : ℕ} (m : Measure (Vec d)) : Set (Lp ℝ 2 m) :=
  Set.range fun u : WeightedSobolevGraph m => u.value_memLp.toLp u.value

/-- The quotient value map has exactly the existing weighted `H¹` domain as its range. -/
theorem densityWeightedH1Value_range {d : ℕ} (ρ : Vec d → ℝ) :
    Set.range (densityWeightedH1Value ρ) =
      weightedH1Domain (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
  ext f
  change (∃ q, densityWeightedH1Value ρ q = f) ↔
    (∃ u : WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))),
      u.value_memLp.toLp u.value = f)
  constructor
  · rintro ⟨q, hq⟩
    revert hq
    refine Quotient.inductionOn q ?_
    intro u hq
    exact ⟨u, by simpa [densityWeightedH1Value] using hq⟩
  · rintro ⟨u, hu⟩
    refine ⟨Quotient.mk (densityWeightedH1Setoid ρ) u, ?_⟩
    simpa [densityWeightedH1Value] using hu

/-- The literal bilinear weighted Dirichlet integral on the weak-gradient graph. -/
def weightedSpatialForm {d : ℕ} {m : Measure (Vec d)} (A : Vec d → Mat d)
    (u v : WeightedSobolevGraph m) : ℝ :=
  ∫ x, weightedFormIntegrand A u v x ∂m

/-- The weighted bilinear energy is independent of representatives with the same values almost
everywhere under a positive continuous density. -/
theorem weightedSpatialForm_congr_of_graph_value_ae {d : ℕ} {ρ : Vec d → ℝ}
    {hρ : Continuous ρ} {hρpos : ∀ x, 0 < ρ x} (A : Vec d → Mat d)
    (u u' v v' : WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hu : u.value =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] u'.value)
    (hv : v.value =ᵐ[volume.withDensity (fun x => ENNReal.ofReal (ρ x))] v'.value) :
    weightedSpatialForm A u v = weightedSpatialForm A u' v' := by
  have hgradU := densityWeightedGraph_gradient_ae_of_value_ae ρ hρ hρpos u u' hu
  have hgradV := densityWeightedGraph_gradient_ae_of_value_ae ρ hρ hρpos v v' hv
  unfold weightedSpatialForm weightedFormIntegrand
  apply integral_congr_ae
  filter_upwards [hgradU, hgradV] with x hU hV
  rw [hU, hV]

/-- The literal weighted form descended to equivalence classes of graph representatives. -/
noncomputable def densityWeightedSpatialForm {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x) (A : Vec d → Mat d)
    (q q' : DensityWeightedH1 ρ) : ℝ :=
  Quotient.liftOn₂ q q' (fun u v => weightedSpatialForm A u v) (by
    intro u v u' v' huv hv
    exact weightedSpatialForm_congr_of_graph_value_ae
      (hρ := hρ) (hρpos := hρpos) A u u' v v' huv hv)

#print axioms ae_withDensity_iff_volume_of_continuous_pos
#print axioms memLp_two_locallyIntegrable_volume_of_density
#print axioms weightedSobolevGraph_mk_of_density_distributionalData
#print axioms weakGradients_ae_eq_of_value_ae_eq
#print axioms densityWeightedGraph_gradient_ae_of_value_ae
#print axioms densityWeightedH1Value_injective
#print axioms densityWeightedH1Gradient
#print axioms densityWeightedH1Value_range
#print axioms weightedSpatialForm_congr_of_graph_value_ae
#print axioms densityWeightedSpatialForm

end

end EinsteinRelation.SpatialDirichlet
