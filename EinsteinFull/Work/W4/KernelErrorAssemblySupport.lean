import EinsteinFull.Work.W4.KernelGaussianTailSupport

/-! Literal half-line integral identities for the actual kernel remainder.
These lemmas do not assert any source expansion from hypothetical errors. -/

open MeasureTheory Set

namespace EinsteinFull

/-- Split a Lebesgue half-line integral; endpoints are removed only through
the atomless-measure identities. -/
theorem integral_Ici_split_Ioo {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntegrableOn f (Ici a)) :
    (∫ t in Ici a, f t) = (∫ t in Ioo a b, f t) + (∫ t in Ici b, f t) := by
  have H := setIntegral_union (Ioc_disjoint_Ioi_same (a := a) (b := b))
    measurableSet_Ioi (hi.mono_set (fun _ ht => ht.1.le))
    (hi.mono_set (fun _ ht => hab.trans ht.le))
  simpa only [Ioc_union_Ioi_eq_Ioi hab, integral_Ioc_eq_integral_Ioo,
    integral_Ici_eq_integral_Ioi] using H

private theorem abs_setIntegral_le {f : ℝ → ℝ} (s : Set ℝ) :
    |∫ t in s, f t| ≤ ∫ t in s, |f t| := by
  simpa only [Real.norm_eq_abs] using
    (norm_integral_le_integral_norm (μ := volume.restrict s) f)

private theorem abs_four_add_sub_le (a b c e q : ℝ) :
    |a + b + c + e - q| ≤ |a| + |b| + |c| + |e| + |q| := by
  linarith only [abs_sub (a + b + c + e) q, abs_add_le (a + b + c) e,
    abs_add_le (a + b) c, abs_add_le a b]

/-- The four time regions used in the source proof, with the polynomial tail
kept as a separate ordinary integral. All integrability is genuine intermediate
data, and every quantitative region estimate is supplied by actual producers. -/
theorem integral_four_region_error_bound {E P : ℝ → ℝ} {S T : ℝ}
    (hS : 1 ≤ S) (hST : S ≤ T)
    (hE : IntegrableOn E (Ici 0)) (hP : IntegrableOn P (Ici 0)) :
    |(∫ t in Ici (0 : ℝ), E t) - (∫ t in Ici (0 : ℝ), P t)| ≤
      (∫ t in Ioo (0 : ℝ) 1, |E t - P t|) +
      (∫ t in Ioo (1 : ℝ) S, |E t - P t|) +
      (∫ t in Ioo S T, |E t|) + (∫ t in Ici T, |E t|) +
      (∫ t in Ici S, |P t|) := by
  have hE₁ := hE.mono_set (Ici_subset_Ici.mpr zero_le_one)
  have hP₁ := hP.mono_set (Ici_subset_Ici.mpr zero_le_one)
  have hES := hE₁.mono_set (Ici_subset_Ici.mpr hS)
  have hPS := hP₁.mono_set (Ici_subset_Ici.mpr hS)
  have H₀ := integral_Ici_split_Ioo zero_le_one (hE.sub hP)
  have H₁ := integral_Ici_split_Ioo hS (hE₁.sub hP₁)
  have H₂ := integral_Ici_split_Ioo hST hES
  simp only [Pi.sub_apply] at H₀ H₁
  rw [integral_sub hE hP] at H₀
  rw [integral_sub hES hPS] at H₁
  have he : (∫ t in Ici (0 : ℝ), E t) - (∫ t in Ici (0 : ℝ), P t) =
      (∫ t in Ioo (0 : ℝ) 1, E t - P t) +
      (∫ t in Ioo (1 : ℝ) S, E t - P t) +
      (∫ t in Ioo S T, E t) + (∫ t in Ici T, E t) - (∫ t in Ici S, P t) := by
    linarith only [H₀, H₁, H₂]
  rw [he]
  calc
    _ ≤ |∫ t in Ioo (0 : ℝ) 1, E t - P t| +
        |∫ t in Ioo (1 : ℝ) S, E t - P t| +
        |∫ t in Ioo S T, E t| + |∫ t in Ici T, E t| + |∫ t in Ici S, P t| := by
      exact abs_four_add_sub_le _ _ _ _ _
    _ ≤ _ := by
      gcongr
      all_goals exact abs_setIntegral_le _

/-- Time integration of the actual remainder subtracts exactly the actual
cutoff Gaussian model, with no reality premise needed for the real part. -/
theorem kernel_remainder_real_integral_identity (d : ℕ) (u₀ u₂ γ : ℝ)
    (hγ : 0 < γ) (K : ℝ → ℂ → ℂ) {lam : ℝ} (hl : lam ≠ 0)
    (hiK : IntegrableOn (fun t : ℝ => (K t (lam : ℂ)).re) (Ici 0)) :
    IntegrableOn (fun t : ℝ => (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re)
      (Ici 0) ∧
    (∫ t in Ici (0 : ℝ), (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) =
      (∫ t in Ici (0 : ℝ), (K t (lam : ℂ)).re) -
      (∫ t in Ioi (1 : ℝ), t ^ (-1 - (d : ℝ) / 2) *
        gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)) := by
  let G : ℝ → ℝ := fun t => t ^ (-1 - (d : ℝ) / 2) *
    gaussianProfile u₀ u₂ γ (lam * Real.sqrt t)
  have hiG : IntegrableOn G (Ici 1) := (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    (gaussianProfile_time_integral d u₀ u₂ hγ hl).1
  have hiG' : IntegrableOn ((Ici (1 : ℝ)).indicator G) (Ici 0) :=
    (IntegrableOn.integrable_indicator hiG measurableSet_Ici).integrableOn
  have he : (fun t : ℝ => (kernelProfileRemainder d u₀ u₂ γ K t (lam : ℂ)).re) =
      fun t => (K t (lam : ℂ)).re - (Ici (1 : ℝ)).indicator G t := by
    funext t
    simp only [kernelProfileRemainder, Complex.sub_re]
    split_ifs with ht
    · rw [indicator_of_mem (show t ∈ Ici (1 : ℝ) from ht), ← Complex.ofReal_mul, complexGaussianProfile_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    · rw [indicator_of_notMem (show t ∉ Ici (1 : ℝ) from ht), Complex.zero_re]
  rw [he]
  refine ⟨hiK.sub hiG', ?_⟩
  rw [integral_sub hiK hiG', integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici, Ici_inter_Ici, max_eq_left zero_le_one,
    integral_Ici_eq_integral_Ioi]
  simp only [integral_Ici_eq_integral_Ioi, G]

end EinsteinFull
