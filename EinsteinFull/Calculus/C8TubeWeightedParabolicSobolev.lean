import EllipticRegularity.Parabolic.Sobolev.ParabolicSlices
import EinsteinFull.External.Source.GMPDirichletKernel
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory Filter EinsteinRelation PDE EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The compactly supported spatial Gagliardo--Nirenberg estimate has a
constant chosen uniformly before the domain and function. -/
theorem c8_compact_spatial_gagliardo_nirenberg_uniform
    (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (U : Set (PDE.Vec d)), IsOpen U →
      ∀ (v : H1Function U) (K : Set (PDE.Vec d)), IsCompact K → K ⊆ U →
      (∀ x ∈ U, x ∉ K → v.toFun x = 0) →
      (eLpNorm (Set.indicator U v.toFun)
        (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
          (2 * ((d : ℝ) + 2) / d) ≤
        C * (eLpNorm (Set.indicator U v.toFun) 2 volume) ^ (4 / (d : ℝ)) *
          (eLpNorm (fun x => vecEuclideanNorm (Set.indicator U v.grad x))
            2 volume) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ :=
    Parabolic.exists_spatial_gagliardo_nirenberg_energy_constant d hd
  refine ⟨C, hC, ?_⟩
  intro U hU v K hK hKU hs
  let v₀ : H1Function (Set.univ : Set (PDE.Vec d)) := {
    toFun := Set.indicator U v.toFun
    grad := Set.indicator U v.grad
    memL2 := by
      simpa only [MemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using
        (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2 v.memL2
    gradMemL2 := by
      intro i
      rw [show (fun x => Set.indicator U v.grad x i) =
        Set.indicator U (fun x => v.grad x i) by
          funext x
          by_cases hx : x ∈ U <;> simp [hx]]
      simpa only [GradMemL2On, GradMemLpOn, MemLpOn, volumeOn,
        Measure.restrict_univ] using
        (memLp_indicator_iff_restrict (μ := volume) hU.measurableSet).2
          (v.gradMemL2 i)
    hasWeakGradient := by
      intro i
      have hzero := Ch4Infra.hasWeakPartialDerivOn_univ_zeroExtend
        hU v hKU hK hs i
      convert hzero using 1
      funext x
      by_cases hx : x ∈ U <;> simp [hx]
  }
  exact hGN v₀


/-- An L² function on a time-space cylinder has L² spatial slices almost everywhere. -/
theorem c8_native_ae_slice_memLp {d : ℕ} {I : Set ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : MeasurableSet U) (f : ℝ × EinsteinRelation.Vec d → ℝ)
    (hf : MemLp f 2 (volume.restrict (I ×ˢ U))) :
    ∀ᵐ t ∂volume.restrict I, MemLp (fun x => f (t, x)) 2 (volume.restrict U) := by
  have hprod : MemLp f 2 ((volume.restrict I).prod (volume.restrict U)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hf
  have hswap : MemLp (fun z : EinsteinRelation.Vec d × ℝ => f (z.2, z.1)) 2
      ((volume.restrict U).prod (volume.restrict I)) :=
    hprod.comp_measurePreserving Measure.measurePreserving_swap
  have hswap' : MemLp (fun z : PDE.Vec d × ℝ => f (z.2, z.1)) 2
      (volume.restrict (U ×ˢ I)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact hswap
  have hslice := PDE.Parabolic.Energy.ae_slice_memLp hU hswap'
  filter_upwards [hslice] with t ht
  exact (memLp_indicator_iff_restrict hU).1 ht

/-- The native value and gradient determine an H¹ function on almost every slice. -/
theorem c8_native_ae_slice_h1 {d : ℕ} {I : Set ℝ} {U : Set (EinsteinRelation.Vec d)}
    (hU : IsOpen U) (u : ℝ × EinsteinRelation.Vec d → ℝ)
    (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d)
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x))) :
    ∀ᵐ t ∂volume.restrict I, ∃ v : PDE.H1Function U,
      v.toFun = (fun x => u (t,x)) ∧ v.grad = (fun x => G (t,x)) := by
  have huv := c8_native_ae_slice_memLp hU.measurableSet u hu
  have hgv := c8_native_ae_slice_memLp hU.measurableSet _ hG
  filter_upwards [huv, hgv, hw] with t ht hg hw
  have hcoord (i : Fin d) : MemLp (fun x => G (t,x) i) 2 (volume.restrict U) := by
    apply hg.mono' (hw i).2.1.aestronglyMeasurable
    exact ae_of_all _ fun x => by
      simpa only [TimeChange.euclideanNorm_eq_norm_toLp] using
        (PiLp.norm_apply_le (WithLp.toLp 2 (G (t,x))) i)
  have hpde : PDE.HasWeakGradientOn U (fun x => u (t,x)) (fun x => G (t,x)) := by
    intro i φ hφ hc hs
    simpa only [coordinateDerivative, PDE.basisVec, unitVector] using
      (hw i).2.2 φ ⟨hφ, hc, hs⟩
  exact ⟨⟨_, _, ht, hcoord, hpde⟩, rfl, rfl⟩


/-- The compact spatial estimate applies uniformly to native almost-everywhere slices. -/
theorem c8_native_ae_spatial_gagliardo_nirenberg (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (I : Set ℝ) (U : Set (EinsteinRelation.Vec d)),
      IsOpen U → ∀ (u : ℝ × EinsteinRelation.Vec d → ℝ)
      (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d),
      MemLp u 2 (volume.restrict (I ×ˢ U)) →
      MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)) →
      (∀ᵐ t ∂volume.restrict I,
        HasWeakGradient U (fun x => u (t, x)) (fun x => G (t, x))) →
      ∀ (K : Set (EinsteinRelation.Vec d)), IsCompact K → K ⊆ U →
      (∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → u (t, x) = 0) →
      ∀ᵐ t ∂volume.restrict I,
        (eLpNorm (fun x => u (t, x))
          (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) (volume.restrict U)) ^
            (2 * ((d : ℝ) + 2) / d) ≤
          C * (eLpNorm (fun x => u (t, x)) 2 (volume.restrict U)) ^ (4 / (d : ℝ)) *
            (eLpNorm (fun x => euclideanNorm (G (t, x))) 2
              (volume.restrict U)) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ := c8_compact_spatial_gagliardo_nirenberg_uniform d hd
  refine ⟨C, hC, ?_⟩
  intro I U hU u G hu hG hw K hK hKU hs
  filter_upwards [c8_native_ae_slice_h1 hU u G hu hG hw, hs] with t ht hs
  obtain ⟨v, hv, hg⟩ := ht
  have hb := hGN U hU v K hK hKU (by simpa only [hv] using hs)
  rw [hv, hg] at hb
  have hgrad :
      (fun x => vecEuclideanNorm (Set.indicator U (fun x => G (t, x)) x)) =
        Set.indicator U (fun x => euclideanNorm (G (t, x))) := by
    funext x
    by_cases hx : x ∈ U <;>
      simp [Set.indicator, hx, PDE.vecEuclideanNorm, PDE.vecNormSq, PDE.vecDot,
        euclideanNorm, euclideanSq, dot]
  rw [hgrad] at hb
  simpa only [eLpNorm_indicator_eq_eLpNorm_restrict hU.measurableSet] using hb


/-- The unweighted time-integrated estimate holds for native measurable slices. -/
theorem c8_native_parabolic_sobolev_unweighted (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (I : Set ℝ) (U : Set (EinsteinRelation.Vec d)),
      IsOpen U → ∀ (u : ℝ × EinsteinRelation.Vec d → ℝ)
      (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d),
      MemLp u 2 (volume.restrict (I ×ˢ U)) →
      MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)) →
      (∀ᵐ t ∂volume.restrict I,
        HasWeakGradient U (fun x => u (t, x)) (fun x => G (t, x))) →
      ∀ (K : Set (EinsteinRelation.Vec d)), IsCompact K → K ⊆ U →
      (∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → u (t, x) = 0) →
      ∀ S : ℝ≥0∞,
      (∀ᵐ t ∂volume.restrict I,
        (∫⁻ x in U, ‖u (t, x)‖ₑ ^ (2 : ℝ)) ≤ S) →
      (∫⁻ t in I, ∫⁻ x in U, ‖u (t, x)‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t in I, ∫⁻ x in U, ‖euclideanNorm (G (t, x))‖ₑ ^ (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ := c8_native_ae_spatial_gagliardo_nirenberg d hd
  refine ⟨C, hC, ?_⟩
  intro I U hU u G hu hG hw K hK hKU hs S hS
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq : 0 < q := by dsimp [q]; positivity
  let A : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => u (t, x)) (ENNReal.ofReal q) (volume.restrict U)) ^ q
  let B : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => u (t, x)) 2 (volume.restrict U)) ^ (2 : ℝ)
  let D : ℝ → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => euclideanNorm (G (t, x))) 2 (volume.restrict U)) ^ (2 : ℝ)
  have hval := c8_native_ae_slice_memLp hU.measurableSet u hu
  have hgrad := c8_native_ae_slice_memLp hU.measurableSet _ hG
  have hA : ∀ᵐ t ∂volume.restrict I,
      A t = ∫⁻ x in U, ‖u (t, x)‖ₑ ^ q := by
    filter_upwards [hval] with t ht
    exact PDE.Parabolic.eLpNorm_rpow_eq_lintegral_enorm_rpow q hq ht.aestronglyMeasurable
  have hB : ∀ᵐ t ∂volume.restrict I, B t ≤ S := by
    filter_upwards [hval, hS] with t ht hs
    have heq := PDE.Parabolic.Energy.lintegral_enorm_sq_eq ht.aestronglyMeasurable
    simpa only [B, ← heq] using hs
  have hDval : ∀ᵐ t ∂volume.restrict I,
      D t = ∫⁻ x in U, ‖euclideanNorm (G (t, x))‖ₑ ^ (2 : ℝ) := by
    filter_upwards [hgrad] with t ht
    exact (PDE.Parabolic.Energy.lintegral_enorm_sq_eq ht.aestronglyMeasurable).symm
  have hprod : AEMeasurable (fun z : ℝ × EinsteinRelation.Vec d =>
      ‖euclideanNorm (G z)‖ₑ ^ (2 : ℝ))
      ((volume.restrict I).prod (volume.restrict U)) := by
    have hm := hG.aestronglyMeasurable.aemeasurable.enorm.pow_const (2 : ℝ)
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hm
  have hDm : AEMeasurable D (volume.restrict I) := by
    have hm := hprod.lintegral_prod_right'
    exact hm.congr (hDval.mono fun t ht => ht.symm)
  have hpoint : ∀ᵐ t ∂volume.restrict I,
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t := by
    filter_upwards [hGN I U hU u G hu hG hw K hK hKU hs] with t ht
    have he : (4 / (d : ℝ)) = (2 : ℝ) * (2 / (d : ℝ)) := by
      field_simp
      ring
    simpa only [A, B, D, q, he, ENNReal.rpow_mul, ENNReal.rpow_natCast] using ht
  have hi := PDE.Parabolic.lintegral_le_of_ae_gagliardo_nirenberg_aemeasurable
    (volume.restrict I) d hd C S hDm hB hpoint
  have ha : (∫⁻ t in I, A t) = ∫⁻ t in I, ∫⁻ x in U, ‖u (t, x)‖ₑ ^ q :=
    lintegral_congr_ae hA
  have he : (∫⁻ t in I, D t) =
      ∫⁻ t in I, ∫⁻ x in U, ‖euclideanNorm (G (t, x))‖ₑ ^ (2 : ℝ) :=
    lintegral_congr_ae hDval
  rw [ha, he] at hi
  exact hi


/-- Ellipticity controls the Euclidean square by the actual matrix energy. -/
theorem c8_elliptic_euclidean_energy_bound {d : ℕ} (κ : ℝ) (hκ : 0 < κ)
    (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d)
    (hcoeff : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x v : EinsteinRelation.Vec d) :
    ‖euclideanNorm v‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (dot ((α x).mulVec v) v) := by
  have hsq : euclideanNorm v ^ 2 = euclideanSq v := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
  have hell := ((hcoeff.2.2 x).2.2.2 v).1
  have hdot : dot ((α x).mulVec v) v = dot v ((α x).mulVec v) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hreal : euclideanNorm v ^ 2 ≤ κ⁻¹ * dot ((α x).mulVec v) v := by
    rw [hsq, hdot]
    have hh : euclideanSq v ≤ dot v ((α x).mulVec v) / κ :=
      (le_div_iff₀ hκ).2 (by simpa only [mul_comm] using hell)
    simpa only [div_eq_mul_inv, mul_comm] using hh
  calc
    ‖euclideanNorm v‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (euclideanNorm v ^ 2) := by
      rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
    _ ≤ ENNReal.ofReal (κ⁻¹ * dot ((α x).mulVec v) v) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (dot ((α x).mulVec v) v) := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le)]


/-- Uniform bounds on the density compare weighted and unweighted integrals. -/
theorem c8_density_lintegral_bounds {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (κ : ℝ) (hκ : 0 < κ) (ρ : X → ℝ)
    (hρ : ∀ x, κ ≤ ρ x ∧ ρ x ≤ κ⁻¹) (f : X → ℝ≥0∞) :
    (∫⁻ x, ENNReal.ofReal (ρ x) * f x ∂μ) ≤
      ENNReal.ofReal κ⁻¹ * ∫⁻ x, f x ∂μ ∧
    (∫⁻ x, f x ∂μ) ≤ ENNReal.ofReal κ⁻¹ *
      ∫⁻ x, ENNReal.ofReal (ρ x) * f x ∂μ := by
  have hc : ENNReal.ofReal κ⁻¹ ≠ ∞ := ENNReal.ofReal_ne_top
  constructor
  · calc
      (∫⁻ x, ENNReal.ofReal (ρ x) * f x ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal κ⁻¹ * f x ∂μ := by
            apply lintegral_mono
            intro x
            change ENNReal.ofReal (ρ x) * f x ≤ ENNReal.ofReal κ⁻¹ * f x
            gcongr
            exact (hρ x).2
      _ = ENNReal.ofReal κ⁻¹ * ∫⁻ x, f x ∂μ := lintegral_const_mul' _ _ hc
  · calc
      (∫⁻ x, f x ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (ρ x) * f x) ∂μ := by
            apply lintegral_mono
            intro x
            have hreal : (1 : ℝ) ≤ κ⁻¹ * ρ x := by
              have hmul := mul_le_mul_of_nonneg_left (hρ x).1 (inv_nonneg.mpr hκ.le)
              simpa only [inv_mul_cancel₀ (ne_of_gt hκ)] using hmul
            have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ x) := by
              rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hκ.le), ← ENNReal.ofReal_one]
              exact ENNReal.ofReal_le_ofReal hreal
            calc
              f x = 1 * f x := (one_mul _).symm
              _ ≤ (ENNReal.ofReal κ⁻¹ * ENNReal.ofReal (ρ x)) * f x :=
                by gcongr
              _ = ENNReal.ofReal κ⁻¹ * (ENNReal.ofReal (ρ x) * f x) := mul_assoc _ _ _
      _ = ENNReal.ofReal κ⁻¹ * ∫⁻ x, ENNReal.ofReal (ρ x) * f x ∂μ :=
        lintegral_const_mul' _ _ hc


/-- The native weighted parabolic Sobolev estimate. -/
theorem c8_native_weighted_parabolic_sobolev (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (ρ : EinsteinRelation.Vec d → ℝ) (α : EinsteinRelation.Vec d → EinsteinRelation.Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (EinsteinRelation.Vec d)),
    MeasurableSet I → IsOpen U → ∀ (u : ℝ × EinsteinRelation.Vec d → ℝ) (G : ℝ × EinsteinRelation.Vec d → EinsteinRelation.Vec d),
    MemLp u 2 (volume.restrict (I ×ˢ U)) →
    AEStronglyMeasurable G (volume.restrict (I ×ˢ U)) →
    MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (I ×ˢ U)) →
    (∀ᵐ t ∂volume.restrict I, HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x))) →
    ∀ (K : Set (EinsteinRelation.Vec d)), IsCompact K → K ⊆ U →
    (∀ᵐ t ∂volume.restrict I, ∀ x ∈ U, x ∉ K → u (t,x) = 0) →
    ∀ S : ℝ≥0∞,
    (∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖u (t,x)‖ₑ ^ (2 : ℝ)) ≤ S) →
    (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
      ‖u (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
    C * S ^ (2 / (d : ℝ)) *
      ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (dot ((α x).mulVec (G (t,x))) (G (t,x))) := by
  obtain ⟨C₀, hC₀, hbase⟩ := c8_native_parabolic_sobolev_unweighted d (by omega)
  let L : ℝ≥0∞ := ENNReal.ofReal κ⁻¹
  let r : ℝ := 2 / (d : ℝ)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hL : L ≠ ∞ := ENNReal.ofReal_ne_top
  refine ⟨L * C₀ * L ^ r * L, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hL hC₀) (ENNReal.rpow_ne_top_of_nonneg hr hL)) hL
  intro ρ α hcoeff I U hI hU u G hu hGm hG hw K hK hKU hs S hS
  have hρ : ∀ x, κ ≤ ρ x ∧ ρ x ≤ κ⁻¹ := fun x =>
    ⟨(hcoeff.2.2 x).1, (hcoeff.2.2 x).2.1⟩
  have hs' : ∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ‖u (t,x)‖ₑ ^ (2 : ℝ)) ≤ L * S := by
    filter_upwards [hS] with t ht
    calc
      (∫⁻ x in U, ‖u (t,x)‖ₑ ^ (2 : ℝ)) ≤
          L * ∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖u (t,x)‖ₑ ^ (2 : ℝ) :=
        (c8_density_lintegral_bounds (volume.restrict U) κ hκ ρ hρ _).2
      _ ≤ L * S := by gcongr
  have huweighted :
      (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ‖u (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d)) ≤
      L * ∫⁻ t in I, ∫⁻ x in U, ‖u (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d) := by
    calc
      _ ≤ ∫⁻ t in I, L * ∫⁻ x in U, ‖u (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d) ∂volume := by
        apply lintegral_mono
        intro t
        exact (c8_density_lintegral_bounds (volume.restrict U) κ hκ ρ hρ _).1
      _ = _ := lintegral_const_mul' _ _ hL
  have henergy :
      (∫⁻ t in I, ∫⁻ x in U, ‖euclideanNorm (G (t,x))‖ₑ ^ (2 : ℝ)) ≤
      L * ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (dot ((α x).mulVec (G (t,x))) (G (t,x))) := by
    calc
      _ ≤ ∫⁻ t in I, L * ∫⁻ x in U,
          ENNReal.ofReal (dot ((α x).mulVec (G (t,x))) (G (t,x))) ∂volume := by
        apply lintegral_mono
        intro t
        calc
          _ ≤ ∫⁻ x in U, L * ENNReal.ofReal (dot ((α x).mulVec (G (t,x))) (G (t,x))) := by
            apply lintegral_mono
            intro x
            exact c8_elliptic_euclidean_energy_bound κ hκ ρ α hcoeff x (G (t,x))
          _ = _ := lintegral_const_mul' _ _ hL
      _ = _ := lintegral_const_mul' _ _ hL
  have hmain := hbase I U hU u G hu hG hw K hK hKU hs (L * S) hs'
  calc
    _ ≤ L * (∫⁻ t in I, ∫⁻ x in U, ‖u (t,x)‖ₑ ^ (2 * ((d : ℝ)+2) / d)) := huweighted
    _ ≤ L * (C₀ * (L * S) ^ r *
        ∫⁻ t in I, ∫⁻ x in U, ‖euclideanNorm (G (t,x))‖ₑ ^ (2 : ℝ)) := by
      gcongr
    _ ≤ L * (C₀ * (L * S) ^ r * (L *
        ∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (dot ((α x).mulVec (G (t,x))) (G (t,x))))) := by
      gcongr
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hr]; dsimp [r]; ac_rfl

end EinsteinFull.Calculus
