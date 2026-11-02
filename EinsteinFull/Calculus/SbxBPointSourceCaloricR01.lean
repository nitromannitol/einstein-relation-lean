import EinsteinFull.Calculus.SbxS4KilledRegularityR02
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Filter
open EinsteinRelation EinsteinFull.External.Source.GMP
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- Replacement by a spatially almost everywhere equal value preserves the
weighted equation and its zero-extension trace. -/
theorem b_weighted_caloric_trace_congr {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    (hU : IsOpen U) {u v : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hu : IsWeightedCaloric ρ α I U u G)
    (htrace : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient Set.univ (U.indicator (fun x => u (t,x)))
        (U.indicator (fun x => G (t,x))))
    (heq : u =ᵐ[volume.restrict (I ×ˢ U)] v) :
    IsWeightedCaloric ρ α I U v G ∧
      ∀ᵐ t ∂volume.restrict I,
        HasWeakGradient Set.univ (U.indicator (fun x => v (t,x)))
          (U.indicator (fun x => G (t,x))) := by
  have hslices : ∀ᵐ t ∂volume.restrict I,
      (fun x => u (t,x)) =ᵐ[volume.restrict U] (fun x => v (t,x)) := by
    have he := heq
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at he
    exact Measure.ae_ae_eq_curry_of_prod he
  constructor
  · refine ⟨(memLp_congr_ae heq).mp hu.1, hu.2.1, hu.2.2.1, ?_, ?_⟩
    · filter_upwards [hu.2.2.2.1, hslices] with t ht he
      exact Correctors.hasWeakGradient_congr_ae hU ht he (Filter.EventuallyEq.rfl)
    · intro ψ hψ hc hs
      have he : (∫ z in I ×ˢ U,
          -(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j))) =
        ∫ z in I ×ˢ U,
          -(ρ z.2 * v z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j)) := by
        apply integral_congr_ae
        filter_upwards [heq] with z hz
        rw [hz]
      rw [← he]
      exact hu.2.2.2.2 ψ hψ hc hs
  · filter_upwards [htrace, hslices] with t ht he
    apply Correctors.hasWeakGradient_congr_ae isOpen_univ ht
    · rw [Measure.restrict_univ]
      exact (ae_eq_restrict_iff_indicator_ae_eq hU.measurableSet).mp he
    · exact Filter.EventuallyEq.rfl

/-- Multiplying a weak gradient by a constant preserves the spatial derivative. -/
theorem b_hasWeakGradient_const_mul {d : ℕ} {U : Set (Vec d)}
    {u : Vec d → ℝ} {G : Vec d → Vec d}
    (hu : HasWeakGradient U u G) (c : ℝ) :
    HasWeakGradient U (fun x => c * u x) (fun x => c • G x) := by
  intro i
  refine ⟨fun x hx => ((hu i).1 x hx).smul c,
    fun x hx => ((hu i).2.1 x hx).smul c, ?_⟩
  intro ψ hψ
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
  rw [(hu i).2.2 ψ hψ, mul_neg]

/-- A constant multiple of a weighted solution retains the same equation and
zero-extension trace. -/
theorem b_weighted_caloric_trace_const_mul {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α I U u G)
    (htrace : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient Set.univ (U.indicator (fun x => u (t,x)))
        (U.indicator (fun x => G (t,x)))) (c : ℝ) :
    IsWeightedCaloric ρ α I U (fun z => c * u z) (fun z => c • G z) ∧
      ∀ᵐ t ∂volume.restrict I,
        HasWeakGradient Set.univ (U.indicator (fun x => c * u (t,x)))
          (U.indicator (fun x => c • G (t,x))) := by
  constructor
  · refine ⟨h.1.const_mul c, h.2.1.const_smul c, ?_, ?_, ?_⟩
    · have heq : (fun z => euclideanNorm (c • G z)) =
          (fun z => |c| * euclideanNorm (G z)) := by
        funext z
        exact TimeChange.euclideanNorm_smul c (G z)
      rw [heq]
      exact h.2.2.1.const_mul |c|
    · filter_upwards [h.2.2.2.1] with t ht
      exact b_hasWeakGradient_const_mul ht c
    · intro ψ hψ hc hs
      have heq : (fun z : ℝ × Vec d =>
          -(ρ z.2 * (c * u z)) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (c • G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j))) =
          (fun z => c * (-(ρ z.2 * u z) * fderiv ℝ ψ z (1, 0) +
            dot ((α z.2).mulVec (G z))
              (fun j => fderiv ℝ ψ z (0, unitVector j)))) := by
        funext z
        rw [Matrix.mulVec_smul]
        simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc]
        ring_nf
        rw [Finset.mul_sum]
        simp only [mul_assoc]
      rw [heq, integral_const_mul, h.2.2.2.2 ψ hψ hc hs, mul_zero]
  · filter_upwards [htrace] with t ht
    have hf : U.indicator (fun x => c * u (t,x)) =
        fun x => c * U.indicator (fun x => u (t,x)) x := by
      funext x
      by_cases hx : x ∈ U <;> simp [hx]
    have hg : U.indicator (fun x => c • G (t,x)) =
        fun x => c • U.indicator (fun x => G (t,x)) x := by
      funext x
      by_cases hx : x ∈ U <;> simp [hx]
    rw [hf, hg]
    exact b_hasWeakGradient_const_mul ht c

/-- The time-translation argument from C13TubeWeightedEnergyTrace:317 preserves Lebesgue measure on translated cylinders. -/
theorem b_time_translation_measurePreserving {d : ℕ} (c a b : ℝ)
    (U : Set (Vec d)) :
    MeasurePreserving (fun z : ℝ × Vec d => (z.1 + c, z.2))
      (volume.restrict (Set.Ioo (a-c) (b-c) ×ˢ U))
      (volume.restrict (Set.Ioo a b ×ˢ U)) := by
  let v : ℝ × Vec d := (c, 0)
  have hp : MeasurePreserving (fun z : ℝ × Vec d => z + v)
      (volume : Measure (ℝ × Vec d)) volume := by
    rw [Measure.volume_eq_prod]
    have he : (fun z : ℝ × Vec d => z + v) = Prod.map (fun t : ℝ => t+c) id := by
      funext z
      rcases z with ⟨t, x⟩
      simp [v]
    rw [he]
    exact (measurePreserving_add_right (volume : Measure ℝ) c).prod
      (MeasurePreserving.id (volume : Measure (Vec d)))
  have h := hp.restrict_preimage_emb (Homeomorph.addRight v).measurableEmbedding
    (Set.Ioo a b ×ˢ U)
  have heq : (fun z : ℝ × Vec d => z + v) ⁻¹' (Set.Ioo a b ×ˢ U) =
      Set.Ioo (a-c) (b-c) ×ˢ U := by
    ext z
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ioo, Prod.fst_add,
      Prod.snd_add, v, add_zero]
    constructor <;> rintro ⟨⟨h1, h2⟩, hx⟩ <;> exact ⟨⟨by linarith, by linarith⟩, hx⟩
  rw [heq] at h
  have he : (fun z : ℝ × Vec d => z + v) = (fun z => (z.1 + c, z.2)) := by
    funext z
    rcases z with ⟨t, x⟩
    simp [v]
  rwa [he] at h

/-- The weighted caloric predicate is invariant under translation of time. -/
theorem b_weighted_caloric_time_translation {d : ℕ} (c a b : ℝ)
    (U : Set (Vec d)) (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : IsWeightedCaloric ρ α (Set.Ioo a b) U u G) :
    IsWeightedCaloric ρ α (Set.Ioo (a-c) (b-c)) U
      (fun z => u (z.1+c, z.2)) (fun z => G (z.1+c, z.2)) := by
  rcases hu with ⟨hu, hg, hn, hw, he⟩
  have hm := b_time_translation_measurePreserving c a b U
  refine ⟨hu.comp_measurePreserving hm, hg.comp_measurePreserving hm,
    hn.comp_measurePreserving hm, ?_, ?_⟩
  · have ht := (measurePreserving_add_right (volume : Measure ℝ) c).restrict_preimage_emb
      (Homeomorph.addRight c).measurableEmbedding (Set.Ioo a b)
    have hp : (fun t : ℝ => t+c) ⁻¹' Set.Ioo a b = Set.Ioo (a-c) (b-c) := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [hp] at ht
    exact ht.quasiMeasurePreserving.ae hw
  · intro ψ hψ hc hs
    let v : ℝ × Vec d := (-c, 0)
    let φ : ℝ × Vec d → ℝ := fun z => ψ (z + v)
    have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
    have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight v)
    have hφs : tsupport φ ⊆ interior (Set.Ioo a b) ×ˢ U := by
      intro z hz
      have h := hs (tsupport_comp_subset_preimage ψ (continuous_id.add continuous_const) hz)
      simp only [interior_Ioo, Set.mem_prod, Set.mem_Ioo] at h ⊢
      have h1 : a-c < z.1-c := by simpa [v] using h.1.1
      have h2 : z.1-c < b-c := by simpa [v] using h.1.2
      exact ⟨⟨by linarith, by linarith⟩, by simpa [v] using h.2⟩
    have hweak := he φ hφ hφc hφs
    let F : ℝ × Vec d → ℝ := fun z =>
      -(ρ z.2 * u z) * fderiv ℝ φ z (1, 0) +
        dot ((α z.2).mulVec (G z)) (fun j => fderiv ℝ φ z (0, unitVector j))
    have hme : MeasurableEmbedding (fun z : ℝ × Vec d => (z.1+c, z.2)) := by
      convert (Homeomorph.addRight (c, (0 : Vec d))).measurableEmbedding using 1
      funext z
      rcases z with ⟨t,x⟩
      simp
    have hi := hm.integral_comp hme F
    have hd (z : ℝ × Vec d) : fderiv ℝ φ (z.1+c, z.2) = fderiv ℝ ψ z := by
      have h := fderiv_comp_add_right (𝕜 := ℝ) (f := ψ) v (x := (z.1+c, z.2))
      simpa [φ, v, Prod.ext_iff] using h
    simpa only [F, hd] using hi.trans hweak


/-- Translating the time coordinate carries both the equation and its
almost-everywhere zero-extension trace to the translated interval. -/
theorem b_weighted_caloric_trace_time_shift {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (a b s : ℝ) (U : Set (Vec d))
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (h : IsWeightedCaloric ρ α (Set.Ioo (a-s) (b-s)) U u G)
    (htrace : ∀ᵐ t ∂volume.restrict (Set.Ioo (a-s) (b-s)),
      HasWeakGradient Set.univ (U.indicator (fun x => u (t,x)))
        (U.indicator (fun x => G (t,x)))) :
    IsWeightedCaloric ρ α (Set.Ioo a b) U
        (fun z => u (z.1-s,z.2)) (fun z => G (z.1-s,z.2)) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasWeakGradient Set.univ (U.indicator (fun x => u (t-s,x)))
          (U.indicator (fun x => G (t-s,x))) := by
  constructor
  · have hc := b_weighted_caloric_time_translation
      (-s) (a-s) (b-s) U ρ α u G h
    simpa only [sub_neg_eq_add, sub_add_cancel, ← sub_eq_add_neg] using hc
  · have ht := (measurePreserving_add_right (volume : Measure ℝ) (-s)).restrict_preimage_emb
        (Homeomorph.addRight (-s)).measurableEmbedding (Set.Ioo (a-s) (b-s))
    have he : (fun t : ℝ => t + -s) ⁻¹' Set.Ioo (a-s) (b-s) = Set.Ioo a b := by
      ext t
      simp only [Set.mem_preimage, Set.mem_Ioo]
      constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
    rw [he] at ht
    simpa only [← sub_eq_add_neg] using ht.quasiMeasurePreserving.ae htrace

/-- Equality of measures determines their nonnegative real-valued densities. -/
theorem b_ae_eq_of_withDensity_eq {d : ℕ} (μ : Measure (Vec d)) [SigmaFinite μ]
    {f g : Vec d → ℝ} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (hfn : ∀ᵐ x ∂μ, 0 ≤ f x) (hgn : ∀ᵐ x ∂μ, 0 ≤ g x)
    (h : μ.withDensity (fun x => ENNReal.ofReal (f x)) =
      μ.withDensity (fun x => ENNReal.ofReal (g x))) : f =ᵐ[μ] g := by
  have he := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal hg.ennreal_ofReal).mp h
  filter_upwards [he, hfn, hgn] with x hx hfx hgx
  simpa only [ENNReal.toReal_ofReal hfx, ENNReal.toReal_ofReal hgx] using
    congrArg ENNReal.toReal hx

/-- A measurable comparison and almost-everywhere slice equality determine
the same spacetime function. -/
theorem b_spacetime_ae_eq_of_slices {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I)
    {u v : ℝ × Vec d → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict (I ×ˢ U)))
    (hv : Measurable v)
    (hslice : ∀ t ∈ I, (fun x => u (t,x)) =ᵐ[volume.restrict U] (fun x => v (t,x))) :
    u =ᵐ[volume.restrict (I ×ˢ U)] v := by
  let u' := hu.mk u
  have humod : u =ᵐ[volume.restrict (I ×ˢ U)] u' := hu.ae_eq_mk
  have humods : ∀ᵐ t ∂volume.restrict I,
      (fun x => u (t,x)) =ᵐ[volume.restrict U] (fun x => u' (t,x)) := by
    have he := humod
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at he
    exact Measure.ae_ae_eq_curry_of_prod he
  have hsec : ∀ᵐ t ∂volume.restrict I,
      (fun x => u' (t,x)) =ᵐ[volume.restrict U] (fun x => v (t,x)) := by
    filter_upwards [humods, ae_restrict_mem hI] with t ht htI
    exact ht.symm.trans (hslice t htI)
  have hprod : u' =ᵐ[(volume.restrict I).prod (volume.restrict U)] v := by
    apply (Measure.ae_prod_iff_ae_ae ?_).mpr hsec
    exact measurableSet_eq_fun hu.stronglyMeasurable_mk.measurable hv
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at humod ⊢
  exact humod.trans hprod

/-- A positive-time L² entrance and full caloricity of L² orbits imply
caloricity, with zero-extension trace, of the actual point-source row and its
source normalization. -/
theorem b_actual_point_source_caloric_of_L2_entrance
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (hOrbit : ∀ (f : physicalZeroBoundaryL2 U hd ω lam L hω)
        (l h : ℝ), 0 < l → l < h →
      ∃ G : ℝ × Vec d → Vec d,
        IsWeightedCaloric (s4PhysicalRho hd ω lam) (s4PhysicalAlpha hd ω lam)
          (Set.Ioo l h) U
          (fun z => (gmpKilledInteriorSemigroup r U hU z.1.toNNReal f).val z.2) G ∧
        ∀ᵐ t ∂volume.restrict (Set.Ioo l h),
          HasWeakGradient Set.univ
            (U.indicator (fun x => (gmpKilledInteriorSemigroup r U hU t.toNNReal f).val x))
            (U.indicator (fun x => G (t,x))))
    (hEntrance : ∀ (s : ℝ), 0 < s → ∀ y ∈ U,
      ∃ f : physicalZeroBoundaryL2 U hd ω lam L hω,
        (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f.val x) ∧
        gmpKilledEndpointKernel r U hU s.toNNReal y =
          (physicalReversibleMeasure ω hd lam).withDensity
            (fun x => ENNReal.ofReal (f.val x)) ∧
        ∀ t : ℝ, 0 < t →
          gmpKilledEndpointKernel r U hU (s+t).toNNReal y =
            (physicalReversibleMeasure ω hd lam).withDensity
              (fun x => ENNReal.ofReal
                ((gmpKilledInteriorSemigroup r U hU t.toNNReal f).val x)))
    (y : Vec d) (hy : y ∈ U) (k : ℝ → Vec d → ℝ)
    (hJoint : Measurable (fun z : ℝ × Vec d => k z.1 z.2))
    (hNonneg : ∀ t > 0, ∀ x, 0 ≤ k t x)
    (hRow : ∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
      (physicalReversibleMeasure ω hd lam).withDensity (fun x => ENNReal.ofReal (k t x)))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ G : ℝ × Vec d → Vec d,
      IsWeightedCaloric (s4PhysicalRho hd ω lam) (s4PhysicalAlpha hd ω lam)
        (Set.Ioo a b) U (fun z => k z.1 z.2) G ∧
      (∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasWeakGradient Set.univ (U.indicator (k t)) (U.indicator (fun x => G (t,x)))) ∧
      IsWeightedCaloric (s4PhysicalRho hd ω lam) (s4PhysicalAlpha hd ω lam)
        (Set.Ioo a b) U (fun z => s4PhysicalRho hd ω lam y * k z.1 z.2)
        (fun z => s4PhysicalRho hd ω lam y • G z) ∧
      ∀ᵐ t ∂volume.restrict (Set.Ioo a b),
        HasWeakGradient Set.univ
          (U.indicator (fun x => s4PhysicalRho hd ω lam y * k t x))
          (U.indicator (fun x => s4PhysicalRho hd ω lam y • G (t,x))) := by
  let s : ℝ := a / 2
  have hs : 0 < s := by dsimp [s]; linarith
  have hls : 0 < a - s := by dsimp [s]; linarith
  have hlh : a - s < b - s := by linarith
  obtain ⟨f, hfn, _, hrestart⟩ := hEntrance s hs y hy
  obtain ⟨G, hcal, htrace⟩ := hOrbit f (a-s) (b-s) hls hlh
  obtain ⟨hcal', htrace'⟩ := b_weighted_caloric_trace_time_shift a b s U hcal htrace
  let v : ℝ × Vec d → ℝ := fun z =>
    (gmpKilledInteriorSemigroup r U hU (z.1-s).toNNReal f).val z.2
  let H : ℝ × Vec d → Vec d := fun z => G (z.1-s,z.2)
  have hslice : ∀ t ∈ Set.Ioo a b,
      (fun x => v (t,x)) =ᵐ[volume.restrict U] (fun x => k t x) := by
    intro t ht
    have htpos : 0 < t := lt_trans ha ht.1
    have hτ : 0 < t-s := by linarith [ht.1]
    have hr := hrestart (t-s) hτ
    have hn : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        0 ≤ (gmpKilledInteriorSemigroup r U hU (t-s).toNNReal f).val x := by
      have hOp := gmpKilledInteriorOperator_ae_eq r U hU (t-s).toNNReal f
      change (fun x => (gmpKilledInteriorSemigroup r U hU (t-s).toNNReal f).val x) =ᵐ[_]
        (fun x => ∫ z, f.val z ∂gmpKilledEndpointKernel r U hU (t-s).toNNReal x) at hOp
      filter_upwards [hOp] with x hx
      rw [hx]
      exact integral_nonneg_of_ae
        ((gmpKilledEndpointKernel_absolutelyContinuous_physical r U hU
          (t-s).toNNReal (Real.toNNReal_pos.mpr hτ) x).ae_le hfn)
    have he : (physicalReversibleMeasure ω hd lam).withDensity
          (fun x => ENNReal.ofReal ((gmpKilledInteriorSemigroup r U hU (t-s).toNNReal f).val x)) =
        (physicalReversibleMeasure ω hd lam).withDensity (fun x => ENNReal.ofReal (k t x)) := by
      have ht' : s + (t-s) = t := by ring
      rw [ht'] at hr
      exact hr.symm.trans (hRow t htpos)
    letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
      EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
    have hkmeas : Measurable (k t) := hJoint.comp (measurable_const.prodMk measurable_id)
    have hSmeas : AEMeasurable
        (fun x => (gmpKilledInteriorSemigroup r U hU (t-s).toNNReal f).val x)
        (physicalReversibleMeasure ω hd lam) :=
      (Lp.aestronglyMeasurable
        ((gmpKilledInteriorSemigroup r U hU (t-s).toNNReal f).val)).aemeasurable
    have hm := b_ae_eq_of_withDensity_eq (physicalReversibleMeasure ω hd lam)
      hSmeas hkmeas.aemeasurable hn (ae_of_all _ (hNonneg t htpos)) he
    have hv : (fun x => v (t,x)) =ᵐ[volume] (fun x => k t x) := by
      apply (EinsteinRelation.SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
        (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
        (physicalReversibleDensity_pos ω hd lam) _).mp
      exact hm
    exact ae_restrict_of_ae hv
  have heq : v =ᵐ[volume.restrict (Set.Ioo a b ×ˢ U)] (fun z => k z.1 z.2) :=
    b_spacetime_ae_eq_of_slices measurableSet_Ioo hcal'.1.aestronglyMeasurable
      hJoint hslice
  obtain ⟨hk, ht⟩ := b_weighted_caloric_trace_congr hU hcal' htrace' heq
  obtain ⟨hK, htK⟩ := b_weighted_caloric_trace_const_mul hk ht (s4PhysicalRho hd ω lam y)
  exact ⟨H, hk, ht, hK, htK⟩

end EinsteinFull
