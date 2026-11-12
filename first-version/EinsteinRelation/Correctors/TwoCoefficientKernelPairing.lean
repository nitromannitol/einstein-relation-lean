import EinsteinRelation.Correctors.TwoCoefficientDuality
import EinsteinRelation.Correctors.GaussianProbabilityKernel
import EinsteinRelation.Correctors.AKMHeatKernelPairingWeak
import EinsteinRelation.Correctors.AKMHeatKernelTimeContinuity
import EinsteinRelation.Correctors.ProbabilityKernelUniformError
import EinsteinRelation.Correctors.WeakTimePrimitiveIdentity

/-! # Pairing E.1 kernels of two coefficients

Source: `paper/main.tex:777–784,842`; AKM Proposition E.1, proof on p. 510.
For E.1 kernels `P` of `A` and `Q` of `B`, the pairing
`s ↦ ∫ P(s,z,y) Q(T-s,z,x) dz` has weak time derivative given by the
coefficient-difference pairing of the two spatial gradients. On interior
intervals its increment is bounded by that pairing's strip integral.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

theorem abs_coord_le_euclideanNorm {d : ℕ} (v : Vec d) (j : Fin d) :
    |v j| ≤ euclideanNorm v := by
  apply Real.abs_le_sqrt
  change v j ^ 2 ≤ ∑ k : Fin d, v k * v k
  rw [sq]
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg (v k)) (Finset.mem_univ j)

/-- A coefficient flux of a square-integrable field is square integrable on
every set, coordinatewise. Source: AKM (0.6). -/
theorem coefficient_flux_coordinate_memLp {d : ℕ} {K : ℝ} (hK : 0 < K)
    (A : Coefficient d K) {μ : Measure (ℝ × Vec d)} {S : Set (ℝ × Vec d)} {G : ℝ × Vec d → Vec d}
    (hGm : AEStronglyMeasurable G (μ.restrict S))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (μ.restrict S))
    (hAm : ∀ i k : Fin d, AEStronglyMeasurable (fun z : ℝ × Vec d => A z.2 i k) (μ.restrict S))
    (j : Fin d) :
    MemLp (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j) 2 (μ.restrict S) := by
  have hGk (k : Fin d) : AEStronglyMeasurable (fun z => G z k) (μ.restrict S) :=
    (continuous_apply k).comp_aestronglyMeasurable hGm
  have hm : AEStronglyMeasurable (fun z : ℝ × Vec d => ((A z.2).mulVec (G z)) j)
      (μ.restrict S) := by
    simpa only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply] using
      (Finset.aestronglyMeasurable_fun_sum Finset.univ fun k _ => (hAm j k).mul (hGk k))
  apply hG.of_le_mul hm (c := K)
  exact Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
    exact (abs_coord_le_euclideanNorm _ j).trans
      (mulVec_euclideanNorm_le_of_quadratic (A z.2) hK (A.symmetric z.2)
        (fun ξ => (by
          change 0 ≤ ∑ k : Fin d, ξ k * ξ k
          exact Finset.sum_nonneg fun k _ => mul_self_nonneg (ξ k) :
          0 ≤ euclideanSq ξ).trans (A.elliptic z.2 ξ).1)
        (fun ξ => (A.elliptic z.2 ξ).2) (G z))

/-- The coefficient-difference pairing of the spatial gradient `X₁` of a
forward kernel (coefficient `A`, pole `y`) with the gradient `X₂` of a
backward kernel (coefficient `B`, pole `x`, terminal time `T`).
Source: AKM Proposition E.1 proof, p. 510. -/
def kernelCoefficientDefect {d : ℕ} {K : ℝ} (A B : Coefficient d K)
    (X₁ X₂ : ℝ → Vec d → Vec d → Vec d) (T : ℝ) (x y : Vec d)
    (t : ℝ) (z : Vec d) : ℝ :=
  dot ((A z).mulVec (X₁ t z y)) (X₂ (T-t) z x) -
    dot ((B z).mulVec (X₂ (T-t) z x)) (X₁ t z y)

/-- The coefficient-difference pairing is integrable on every interior
time strip. Source: AKM (E.8). -/
theorem integrable_kernelCoefficientDefect {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A B : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties B Q X₂ Y₂ H₂ C₂)
    {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T) (x y : Vec d) :
    Integrable (fun z : ℝ × Vec d => kernelCoefficientDefect A B X₁ X₂ T x y z.1 z.2)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
  have htr := akm_time_reflection_strip_measurePreserving d T a b
  obtain ⟨hGm, hG⟩ := akm_heatKernel_global_gradient_memLp hK hP ha hab y
  obtain ⟨hHm₀, hH₀⟩ := akm_heatKernel_global_gradient_memLp hK hQ
    (sub_pos.mpr hbT) (by linarith : T-b < T-a) x
  have hHm : AEStronglyMeasurable (fun z : ℝ × Vec d => X₂ (T-z.1) z.2 x)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [Function.comp_def] using hHm₀.comp_measurePreserving htr
  have hH : MemLp (fun z : ℝ × Vec d => euclideanNorm (X₂ (T-z.1) z.2 x)) 2
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [Function.comp_def] using hH₀.comp_measurePreserving htr
  have hAm (A : Coefficient d K) (i k : Fin d) :
      AEStronglyMeasurable (fun z : ℝ × Vec d => A z.2 i k)
        (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    (A.locally_integrable i k).aestronglyMeasurable.comp_snd.mono_measure
      Measure.restrict_le_self
  have hcoord {F : ℝ × Vec d → Vec d}
      (hFm : AEStronglyMeasurable F (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))))
      (hF : MemLp (fun z => euclideanNorm (F z)) 2
        (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d))))) (j : Fin d) :
      MemLp (fun z => F z j) 2 (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    hF.mono' ((continuous_apply j).comp_aestronglyMeasurable hFm)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]
        exact abs_coord_le_euclideanNorm _ j)
  have h1 : Integrable (fun z : ℝ × Vec d =>
      dot ((A z.2).mulVec (X₁ z.1 z.2 y)) (X₂ (T-z.1) z.2 x))
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [dot] using integrable_finset_sum Finset.univ fun j _ =>
      (coefficient_flux_coordinate_memLp hK A hGm hG (hAm A) j).integrable_mul
        (hcoord hHm hH j)
  have h2 : Integrable (fun z : ℝ × Vec d =>
      dot ((B z.2).mulVec (X₂ (T-z.1) z.2 x)) (X₁ z.1 z.2 y))
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [dot] using integrable_finset_sum Finset.univ fun j _ =>
      (coefficient_flux_coordinate_memLp hK B hHm hH (hAm B) j).integrable_mul
        (hcoord hGm hG j)
  exact h1.sub h2

/-- The two-coefficient kernel pairing has the coefficient-difference
pairing as its weak time derivative on interior intervals.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1 proof, p. 510. -/
theorem kernel_two_coefficient_pairing_weak {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A B : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties B Q X₂ Y₂ H₂ C₂)
    {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (x y : Vec d) {η : ℝ → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η) (hηs : tsupport η ⊆ Set.Ioo a b) :
    (∫ t in a..b, (∫ z, P t z y * Q (T-t) z x ∂volume) * deriv η t) =
      ∫ t in a..b, η t * ∫ z, kernelCoefficientDefect A B X₁ X₂ T x y t z ∂volume := by
  let u : ℝ × Vec d → ℝ := fun z => P z.1 z.2 y
  let v : ℝ × Vec d → ℝ := fun z => Q (T-z.1) z.2 x
  let G : ℝ × Vec d → Vec d := fun z => X₁ z.1 z.2 y
  let H : ℝ × Vec d → Vec d := fun z => X₂ (T-z.1) z.2 x
  let E : ℝ × Vec d → ℝ := fun z => kernelCoefficientDefect A B X₁ X₂ T x y z.1 z.2
  have htr := akm_time_reflection_strip_measurePreserving d T a b
  have hu : MemLp u 2 (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    akm_heatKernel_strip_memLp hK hP ha y
  have hv : MemLp v 2 (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [v, Function.comp_def] using
      (akm_heatKernel_strip_memLp hK hQ (sub_pos.mpr hbT) x).comp_measurePreserving htr
  obtain ⟨hGm, hG⟩ := akm_heatKernel_global_gradient_memLp hK hP ha hab y
  obtain ⟨hHm₀, hH₀⟩ := akm_heatKernel_global_gradient_memLp hK hQ
    (sub_pos.mpr hbT) (by linarith : T-b < T-a) x
  have hHm : AEStronglyMeasurable H
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [H, Function.comp_def] using hHm₀.comp_measurePreserving htr
  have hH : MemLp (fun z => euclideanNorm (H z)) 2
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [H, Function.comp_def] using hH₀.comp_measurePreserving htr
  have hAm (A : Coefficient d K) (i k : Fin d) :
      AEStronglyMeasurable (fun z : ℝ × Vec d => A z.2 i k)
        (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    (A.locally_integrable i k).aestronglyMeasurable.comp_snd.mono_measure
      Measure.restrict_le_self
  let F : ℝ × Vec d → Vec d := fun z j =>
    v z * ((A z.2).mulVec (G z)) j - u z * ((B z.2).mulVec (H z)) j
  have hF (j : Fin d) : Integrable (fun z => F z j)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    (hv.integrable_mul (coefficient_flux_coordinate_memLp hK A hGm hG (hAm A) j)).sub
      (hu.integrable_mul (coefficient_flux_coordinate_memLp hK B hHm hH (hAm B) j))
  have hEi : Integrable E (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    integrable_kernelCoefficientDefect hK hP hQ ha hab hbT x y
  obtain ⟨Bd, _, hBd, _⟩ := paired_compact_time_slope_bound hη hηc
  obtain ⟨Mη, hMη⟩ := hηc.exists_bound_of_continuous hη.continuous
  have hηd : AEStronglyMeasurable (fun z : ℝ × Vec d => deriv η z.1)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    ((hη.continuous_deriv (by simp)).comp continuous_fst).aestronglyMeasurable
  have hf : Integrable (fun z => u z * v z * deriv η z.1)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    (hu.integrable_mul hv).mul_bdd hηd (Filter.Eventually.of_forall (fun z => hBd z.1))
  have hηE : Integrable (fun z => η z.1 * E z)
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) :=
    hEi.bdd_mul (hη.continuous.comp continuous_fst).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hMη z.1)
  have hz : (∫ z in Set.Ioo a b ×ˢ Set.univ, (u z * v z * deriv η z.1 - η z.1 * E z)) = 0 := by
    have hfE : Integrable (fun z => u z * v z * deriv η z.1 - η z.1 * E z)
        (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) := hf.sub hηE
    apply akm_global_duality_cutoff_removal hfE hF hη.continuous hηc
    intro χ hχ hχc
    obtain ⟨n, hn⟩ := akm_compact_subset_originBall hχc
    have hR : 0 < (n+1 : ℝ) := by positivity
    have hid := parabolicSolutions_two_coefficient_cutoff_pairing hK hab hR
      ((hP.2.2.1 y).1 a b (n+1) ha hab hR)
      ((hQ.2.2.1 x).1 (T-b) (T-a) (n+1) (sub_pos.mpr hbT) (by linarith) hR)
      hη hηc hηs ⟨hχ, hχc, hn⟩
    rw [akm_spatially_supported_strip_integral measurableSet_Ioo hn
      (f := fun z => (u z * v z * deriv η z.1 - η z.1 * E z) * χ z.2 ^ 2)
      (fun z hz => by simp only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero]),
      akm_spatially_supported_strip_integral measurableSet_Ioo hn
        (f := fun z => η z.1 * χ z.2 * dot (F z) (gradient χ z.2))
        (fun z hz => by simp only [hz, mul_zero, zero_mul])]
    have hI1 : Integrable (fun z => u z * v z * deriv η z.1 * χ z.2 ^ 2)
        (volume.restrict (Set.Ioo a b ×ˢ originBall d (n+1))) := hid.1
    have hI3 : Integrable (fun z => η z.1 * χ z.2 ^ 2 * E z)
        (volume.restrict (Set.Ioo a b ×ˢ originBall d (n+1))) := hid.2.2.1
    have hEq : (∫ z in Set.Ioo a b ×ˢ originBall d (n+1), u z * v z * deriv η z.1 * χ z.2 ^ 2) =
        2 * (∫ z in Set.Ioo a b ×ˢ originBall d (n+1),
          η z.1 * χ z.2 * dot (F z) (gradient χ z.2)) +
        ∫ z in Set.Ioo a b ×ˢ originBall d (n+1), η z.1 * χ z.2 ^ 2 * E z := hid.2.2.2
    have hsplit : (∫ z in Set.Ioo a b ×ˢ originBall d (n+1),
        (u z * v z * deriv η z.1 - η z.1 * E z) * χ z.2 ^ 2) =
        (∫ z in Set.Ioo a b ×ˢ originBall d (n+1), u z * v z * deriv η z.1 * χ z.2 ^ 2) -
          ∫ z in Set.Ioo a b ×ˢ originBall d (n+1), η z.1 * χ z.2 ^ 2 * E z := by
      rw [← integral_sub hI1 hI3]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
    rw [hsplit, hEq]
    ring
  have hz' : (∫ z in Set.Ioo a b ×ˢ Set.univ, u z * v z * deriv η z.1) =
      ∫ z in Set.Ioo a b ×ˢ Set.univ, η z.1 * E z := by
    have hs := integral_sub hf hηE
    rw [hz] at hs
    linarith only [hs]
  have hprod : (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec d)) := by
    change ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hfprod := hf
  rw [hprod] at hfprod
  have heq1 := integral_prod (fun z => u z * v z * deriv η z.1) hfprod
  simp only [integral_mul_const] at heq1
  have hgprod := hηE
  rw [hprod] at hgprod
  have heq2 := integral_prod (fun z => η z.1 * E z) hgprod
  simp only [integral_const_mul] at heq2
  rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  change (∫ t in Set.Ioo a b, (∫ z, u (t,z) * v (t,z)) * deriv η t) =
    ∫ t in Set.Ioo a b, η t * ∫ z, E (t,z)
  calc
    (∫ t in Set.Ioo a b, (∫ z, u (t,z) * v (t,z)) * deriv η t) =
        ∫ z, u z * v z * deriv η z.1 ∂((volume.restrict (Set.Ioo a b)).prod volume) :=
      heq1.symm
    _ = ∫ z in Set.Ioo a b ×ˢ Set.univ, u z * v z * deriv η z.1 := by rw [hprod]
    _ = ∫ z in Set.Ioo a b ×ˢ Set.univ, η z.1 * E z := hz'
    _ = ∫ z, η z.1 * E z ∂((volume.restrict (Set.Ioo a b)).prod volume) := by rw [hprod]
    _ = ∫ t in Set.Ioo a b, η t * ∫ z, E (t,z) := heq2

/-- On interior intervals the increment of the two-coefficient kernel
pairing is minus the time integral of the coefficient-difference pairing.
Source: AKM Proposition E.1 proof, p. 510. -/
theorem kernel_two_coefficient_pairing_sub_eq {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A B : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties B Q X₂ Y₂ H₂ C₂)
    {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T) (x y : Vec d) :
    (∫ z, P b z y * Q (T-b) z x ∂volume) - (∫ z, P a z y * Q (T-a) z x ∂volume) =
      -∫ t in a..b, ∫ z, kernelCoefficientDefect A B X₁ X₂ T x y t z ∂volume := by
  have hprod : (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec d)) := by
    change ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hEi := integrable_kernelCoefficientDefect hK hP hQ ha hab hbT x y
  rw [hprod] at hEi
  have hg : IntegrableOn
      (fun t => -∫ z, kernelCoefficientDefect A B X₁ X₂ T x y t z ∂volume) (Set.Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact hEi.integral_prod_left.neg
  have hf : ContinuousOn (fun s => ∫ z, P s z y * Q (T-s) z x ∂volume) (Set.Icc a b) :=
    (hP.isGaussianProbabilityKernel.pairing_continuousOn hQ.isGaussianProbabilityKernel
      hK T x y).mono (fun s hs => ⟨ha.trans_le hs.1, hs.2.trans_lt hbT⟩)
  have hmain := sub_eq_intervalIntegral_of_weak_time_derivative _ _ hf hg (by
    intro η hη hηc hηs
    have hw := kernel_two_coefficient_pairing_weak hK hP hQ ha hab hbT x y hη hηc hηs
    rw [intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo] at hw
    rw [hw, ← integral_neg]
    congr 1
    funext s
    ring) b ⟨hab.le, le_rfl⟩
  rw [hmain, intervalIntegral.integral_neg]

/-- The increment of the two-coefficient kernel pairing over an interior
interval is bounded by the strip integral of the coefficient-difference
pairing. Source: AKM Proposition E.1 proof, p. 510. -/
theorem kernel_two_coefficient_pairing_sub_abs_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {A B : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X₁ Y₁ X₂ Y₂ : ℝ → Vec d → Vec d → Vec d}
    {H₁ H₂ : ℝ → Vec d → Vec d → Mat d} {C₁ C₂ : ℝ → ℝ}
    (hP : HeatKernelProperties A P X₁ Y₁ H₁ C₁)
    (hQ : HeatKernelProperties B Q X₂ Y₂ H₂ C₂)
    {a b T : ℝ} (ha : 0 < a) (hab : a < b) (hbT : b < T) (x y : Vec d) :
    |(∫ z, P b z y * Q (T-b) z x ∂volume) - (∫ z, P a z y * Q (T-a) z x ∂volume)| ≤
      ∫ z in Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)),
        |kernelCoefficientDefect A B X₁ X₂ T x y z.1 z.2| := by
  rw [kernel_two_coefficient_pairing_sub_eq hK hP hQ ha hab hbT x y, abs_neg,
    intervalIntegral.integral_of_le hab.le, integral_Ioc_eq_integral_Ioo]
  have hprod : (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)))) =
      (volume.restrict (Set.Ioo a b)).prod (volume : Measure (Vec d)) := by
    change ((volume : Measure ℝ).prod volume).restrict (Set.Ioo a b ×ˢ Set.univ) = _
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hEi := integrable_kernelCoefficientDefect hK hP hQ ha hab hbT x y
  rw [hprod] at hEi ⊢
  rw [integral_prod _ hEi.abs]
  calc
    |∫ t in Set.Ioo a b, ∫ z, kernelCoefficientDefect A B X₁ X₂ T x y t z ∂volume| ≤
        ∫ t in Set.Ioo a b, |∫ z, kernelCoefficientDefect A B X₁ X₂ T x y t z ∂volume| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioo a b, ∫ z, |kernelCoefficientDefect A B X₁ X₂ T x y t z| ∂volume := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => abs_nonneg _)
        hEi.abs.integral_prod_left
      exact Filter.Eventually.of_forall fun t => abs_integral_le_integral_abs

/-- The whole-space gradient energy of an E.1 kernel on a positive-time
strip is bounded by its scalar energy on a slightly larger strip, with a
constant depending only on the strip, the dimension and the ellipticity
bound. Source: AKM (E.7)–(E.8), via the cutoff Caccioppoli estimate of
`akm_heatKernel_global_gradient_memLp`. -/
theorem akm_heatKernel_global_gradient_sq_le {d : ℕ} {K : ℝ} (hK : 0 < K)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {A : Coefficient d K} {P : ℝ → Vec d → Vec d → ℝ}
      {X Y : ℝ → Vec d → Vec d → Vec d} {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ},
      HeatKernelProperties A P X Y H C → ∀ y : Vec d,
        (∫ z in Set.Ioo a b ×ˢ (Set.univ : Set (Vec d)), euclideanNorm (X z.1 z.2 y) ^ 2) ≤
          E * ∫ z in Set.Ioo (a/2) (b+a/2) ×ˢ (Set.univ : Set (Vec d)), P z.1 z.2 y ^ 2 := by
  obtain ⟨η, M, hη, hηc, hηs, hηb, hηone, hM, hηD⟩ := exists_positive_time_plateau ha hab
  obtain ⟨χ, B, hB, hχ, hχb, hχlim, hχD⟩ := akm_exists_scaled_cutoffs d
  have hχabs (n : ℕ) (x : Vec d) : |χ n x| ≤ 1 := by
    rw [abs_of_nonneg (hχb n x).1]
    exact (hχb n x).2
  have hχDb (n : ℕ) (x : Vec d) : ‖gradient (χ n) x‖ ≤ B := by
    apply (hχD n x).trans
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n+1 : ℕ))).mpr
    exact le_mul_of_one_le_right hB (by exact_mod_cast (show 1 ≤ n+1 by omega))
  refine ⟨2*M + 4*K^2*d*B^2, by positivity, ?_⟩
  intro A P X Y H C h y
  have hGm := parabolic_gradient_aestronglyMeasurable
    (fun R hR => (h.2.2.1 y).1 a b R ha hab hR)
  have hnorm : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have he (n : ℕ) := parabolic_global_cutoff_energy hK measurableSet_Ioo measurableSet_Ioo
    (show Set.Ioo a b ⊆ Set.Ioo (a/2) (b+a/2) from fun t ht => by
      constructor <;> linarith [ht.1, ht.2])
    (fun R hR => (h.2.2.1 y).1 (a/2) (b+a/2) R (half_pos ha) (by linarith) hR)
    (akm_heatKernel_strip_memLp hK h (half_pos ha) y)
    hη hηc (by simpa only [isOpen_Ioo.interior_eq] using hηs)
    (fun t ht => hηone t ⟨ht.1.le, ht.2.le⟩)
    (hχ n).1 (hχ n).2 (show 0 ≤ 2*M + 4*K^2*d*B^2 by positivity)
    (fun z _ => parabolic_tensor_cutoff_error_bound K hη (hχ n).1 hM hB
      (fun t => by rw [abs_of_nonneg (hηb t).1]; exact (hηb t).2)
      hηD (hχabs n) (hχDb n) z)
  have hi (n : ℕ) : Integrable
      (fun z : ℝ × Vec d => χ n z.2 ^ 2 * euclideanNorm (X z.1 z.2 y) ^ 2)
      (volume.restrict (Set.Ioo a b ×ˢ Set.univ)) := by
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using (he n).1
  have hC (n : ℕ) :
      (∫ z in Set.Ioo a b ×ˢ Set.univ, χ n z.2 ^ 2 * euclideanNorm (X z.1 z.2 y) ^ 2) ≤
        (2*M + 4*K^2*d*B^2) *
          ∫ z in Set.Ioo (a/2) (b+a/2) ×ˢ (Set.univ : Set (Vec d)), P z.1 z.2 y ^ 2 := by
    simpa only [euclideanNorm, Real.sq_sqrt (euclideanSq_nonneg_fisher _)] using (he n).2
  exact (memLp_two_of_cutoff_energy_bound (hnorm.comp_aestronglyMeasurable hGm)
    (Filter.Eventually.of_forall (fun z => hχlim z.2)) hi hC).2

/-- A matrix pairing is bounded by the entrywise ℓ¹ norm of the matrix. -/
theorem abs_dot_mulVec_le {d : ℕ} (g w : Vec d) (M : Mat d) :
    |dot g (M.mulVec w)| ≤ (∑ i, ∑ j, |M i j|) * (euclideanNorm g * euclideanNorm w) := by
  unfold dot
  simp only [Matrix.mulVec, dotProduct]
  calc
    |∑ i, g i * ∑ j, M i j * w j| ≤ ∑ i, |g i * ∑ j, M i j * w j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (∑ j, |M i j|) * (euclideanNorm g * euclideanNorm w) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [abs_mul]
      calc
        |g i| * |∑ j, M i j * w j| ≤ euclideanNorm g * ∑ j, |M i j| * euclideanNorm w := by
          apply mul_le_mul (abs_coord_le_euclideanNorm g i) _ (abs_nonneg _) (Real.sqrt_nonneg _)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_coord_le_euclideanNorm w j) (abs_nonneg _)
        _ = (∑ j, |M i j|) * (euclideanNorm g * euclideanNorm w) := by
          rw [← Finset.sum_mul]
          ring
    _ = (∑ i, ∑ j, |M i j|) * (euclideanNorm g * euclideanNorm w) := by
      rw [Finset.sum_mul]

/-- The entries of an AKM coefficient are bounded by its ellipticity
constant. Source: AKM (0.6). -/
theorem coefficient_entry_abs_le {d : ℕ} {K : ℝ} (hK : 0 < K) (A : Coefficient d K)
    (x : Vec d) (i j : Fin d) : |A x i j| ≤ K := by
  have h := mulVec_euclideanNorm_le_of_quadratic (A x) hK (A.symmetric x)
    (fun ξ => (by
      change 0 ≤ ∑ k : Fin d, ξ k * ξ k
      exact Finset.sum_nonneg fun k _ => mul_self_nonneg (ξ k) :
      0 ≤ euclideanSq ξ).trans (A.elliptic x ξ).1)
    (fun ξ => (A.elliptic x ξ).2) (unitVector j)
  have hu : euclideanNorm (unitVector j : Vec d) = 1 := by
    change Real.sqrt (dotProduct (Pi.single j (1 : ℝ)) (Pi.single j 1)) = 1
    rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]
  have hc : (A x).mulVec (unitVector j) i = A x i j := by
    change dotProduct (A x i) (Pi.single j 1) = A x i j
    rw [dotProduct_single, mul_one]
  calc
    |A x i j| = |(A x).mulVec (unitVector j) i| := by rw [hc]
    _ ≤ euclideanNorm ((A x).mulVec (unitVector j)) := abs_coord_le_euclideanNorm _ i
    _ ≤ K * euclideanNorm (unitVector j : Vec d) := h
    _ = K := by rw [hu, mul_one]

end EinsteinRelation.Correctors
