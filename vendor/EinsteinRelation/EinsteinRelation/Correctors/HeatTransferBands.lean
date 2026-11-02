import EinsteinRelation.Correctors.HeatTransferMoments
import EinsteinRelation.Correctors.HeatTransferIdentity

/-!
# Scale bounds from heat transfer

Proposition 6.1, Step 2 (`paper/main.tex:1023–1031`): kernel masses of orders
`r² s` and `s` give moment bounds of order `r s`. The constants in these
lemmas are explicit and uniform in the environment law and in `0 < r ≤ R`.
The estimates on `heatTransferExpression` are unconditional. The lemmas
about `horizontalMollify K f` explicitly take the time-integrated heat
identity as an internal prerequisite; this file does not assert that identity.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- A compactly supported `C²` kernel has a continuous coordinate Laplacian. -/
theorem continuous_coordLaplacian {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) :
    Continuous (coordLaplacian K) := by
  exact continuous_finset_sum _ fun i _ =>
    continuous_fderiv_dir (contDiff_one_fderiv_dir hK (unitVector i)) (unitVector i)

/-- A compactly supported `C²` kernel has an integrable coordinate Laplacian. -/
theorem integrable_coordLaplacian {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K)
    (hKc : HasCompactSupport K) : Integrable (coordLaplacian K) := by
  apply integrable_finset_sum
  intro i _
  exact (continuous_fderiv_dir (contDiff_one_fderiv_dir hK (unitVector i))
    (unitVector i)).integrable_of_hasCompactSupport
      ((hKc.fderiv_apply ℝ (unitVector i)).fderiv_apply ℝ (unitVector i))

/-- The norm estimate for a band of the explicit heat-transfer expression.
For derivative order `k`, use `s = r⁻¹ ^ k` (`paper/main.tex:1023–1031`). -/
theorem heat_transfer_band_moment_le
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M r R A B s : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s)
    {K L : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K)
    (hL : Measurable L) (hLi : Integrable L)
    (hKa : (∫ x, |K x|) ≤ A * r ^ 2 * s) (hLa : (∫ x, |L x|) ≤ B * s)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t)) :
    MemLp (heatTransferExpression (r ^ 2) K L f) (ENNReal.ofReal m) Q ∧
    eLpNorm (heatTransferExpression (r ^ 2) K L f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r * s) := by
  have h := heat_transfer_moment_le Q hQ hm hM (hr.trans_le hrR) (sq_nonneg r)
    hK hKi hL hLi hf hfn
  exact ⟨h.1, h.2.trans (ENNReal.ofReal_le_ofReal
    (heat_transfer_scale_bound hr hrR hM hA hB hs hKa hLa))⟩

/-- The three band orders `r, 1, r⁻¹` for the explicit heat-transfer expression,
with the same constant for all three kernels (`paper/main.tex:1028–1031`). -/
theorem heat_transfer_three_band_bounds
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M r R A B : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {K L : Fin 3 → Vec d → ℝ}
    (hK : ∀ k, Measurable (K k)) (hKi : ∀ k, Integrable (K k))
    (hL : ∀ k, Measurable (L k)) (hLi : ∀ k, Integrable (L k))
    (hKa : ∀ k : Fin 3, (∫ x, |K k x|) ≤ A * r ^ 2 * r⁻¹ ^ k.val)
    (hLa : ∀ k : Fin 3, (∫ x, |L k x|) ≤ B * r⁻¹ ^ k.val)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t)) :
    (∀ k, MemLp (heatTransferExpression (r ^ 2) (K k) (L k) f) (ENNReal.ofReal m) Q) ∧
    eLpNorm (heatTransferExpression (r ^ 2) (K 0) (L 0) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r) ∧
    eLpNorm (heatTransferExpression (r ^ 2) (K 1) (L 1) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M) ∧
    eLpNorm (heatTransferExpression (r ^ 2) (K 2) (L 2) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r⁻¹) := by
  have h := fun k : Fin 3 => heat_transfer_band_moment_le Q hQ hm hM hr hrR hA hB
    (pow_nonneg (inv_nonneg.mpr hr.le) k.val)
    (hK k) (hKi k) (hL k) (hLi k) (hKa k) (hLa k) hf hfn
  refine ⟨fun k => (h k).1, ?_, ?_, ?_⟩
  · simpa only [Fin.val_zero, pow_zero, mul_one] using (h 0).2
  · simpa only [Fin.val_one, pow_one, mul_assoc, mul_inv_cancel₀ hr.ne', mul_one] using (h 1).2
  · convert (h 2).2 using 1
    congr 1
    change (2 * A + 3 * B) * M * r⁻¹ =
      (2 * A + 3 * B) * M * r * r⁻¹ ^ 2
    field_simp

/-- Transfer of the band estimate to the actual convolution, once the internal
time-integrated heat identity is supplied (`paper/main.tex:1020–1031`). -/
theorem horizontalMollify_band_moment_le_of_heat_transfer
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M r R A B s : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B) (hs : 0 ≤ s)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    (hKa : (∫ x, |K x|) ≤ A * r ^ 2 * s)
    (hLa : (∫ x, |coordLaplacian K x|) ≤ B * s)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t))
    (htransfer : horizontalMollify K f =ᵐ[Q]
      heatTransferExpression (r ^ 2) K (coordLaplacian K) f) :
    MemLp (horizontalMollify K f) (ENNReal.ofReal m) Q ∧
    eLpNorm (horizontalMollify K f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r * s) := by
  have h := heat_transfer_band_moment_le Q hQ hm hM hr hrR hA hB hs
    hK.continuous.measurable (hK.continuous.integrable_of_hasCompactSupport hKc)
    (continuous_coordLaplacian hK).measurable (integrable_coordLaplacian hK hKc)
    hKa hLa hf hfn
  exact ⟨h.1.ae_eq htransfer.symm, (eLpNorm_congr_ae htransfer).le.trans h.2⟩

/-- The three actual convolution bounds with one constant, conditional on the
internal heat identity for each kernel (`paper/main.tex:1028–1031`). -/
theorem horizontalMollify_three_band_bounds_of_heat_transfer
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M r R A B : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M)
    (hr : 0 < r) (hrR : r ≤ R) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {K : Fin 3 → Vec d → ℝ}
    (hK : ∀ k, ContDiff ℝ 2 (K k)) (hKc : ∀ k, HasCompactSupport (K k))
    (hKa : ∀ k : Fin 3, (∫ x, |K k x|) ≤ A * r ^ 2 * r⁻¹ ^ k.val)
    (hLa : ∀ k : Fin 3, (∫ x, |coordLaplacian (K k) x|) ≤ B * r⁻¹ ^ k.val)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t))
    (htransfer : ∀ k, horizontalMollify (K k) f =ᵐ[Q]
      heatTransferExpression (r ^ 2) (K k) (coordLaplacian (K k)) f) :
    (∀ k, MemLp (horizontalMollify (K k) f) (ENNReal.ofReal m) Q) ∧
    eLpNorm (horizontalMollify (K 0) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r) ∧
    eLpNorm (horizontalMollify (K 1) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M) ∧
    eLpNorm (horizontalMollify (K 2) f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * r⁻¹) := by
  have h := heat_transfer_three_band_bounds Q hQ hm hM hr hrR hA hB
    (fun k => (hK k).continuous.measurable)
    (fun k => (hK k).continuous.integrable_of_hasCompactSupport (hKc k))
    (fun k => (continuous_coordLaplacian (hK k)).measurable)
    (fun k => integrable_coordLaplacian (hK k) (hKc k)) hKa hLa hf hfn
  refine ⟨fun k => (h.1 k).ae_eq (htransfer k).symm, ?_, ?_, ?_⟩
  · exact (eLpNorm_congr_ae (htransfer 0)).le.trans h.2.1
  · exact (eLpNorm_congr_ae (htransfer 1)).le.trans h.2.2.1
  · exact (eLpNorm_congr_ae (htransfer 2)).le.trans h.2.2.2

/-- The largest-scale remainder estimate, from kernel masses `A` and `B/R²`
and the internal heat identity (`paper/main.tex:1031`). -/
theorem horizontalMollify_remainder_moment_le_of_heat_transfer
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M R A B : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) (hR : 0 < R)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {K : Vec d → ℝ} (hK : ContDiff ℝ 2 K) (hKc : HasCompactSupport K)
    (hKa : (∫ x, |K x|) ≤ A)
    (hLa : (∫ x, |coordLaplacian K x|) ≤ B * (R ^ 2)⁻¹)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t))
    (htransfer : horizontalMollify K f =ᵐ[Q]
      heatTransferExpression (R ^ 2) K (coordLaplacian K) f) :
    MemLp (horizontalMollify K f) (ENNReal.ofReal m) Q ∧
    eLpNorm (horizontalMollify K f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * R⁻¹) := by
  have hmass : (∫ x, |K x|) ≤ A * R ^ 2 * (R ^ 2)⁻¹ := by
    simpa only [mul_assoc, mul_inv_cancel₀ (pow_ne_zero 2 hR.ne'), mul_one] using hKa
  have h := horizontalMollify_band_moment_le_of_heat_transfer Q hQ hm hM hR le_rfl hA hB
    (inv_nonneg.mpr (sq_nonneg R)) hK hKc hmass hLa hf hfn htransfer
  refine ⟨h.1, ?_⟩
  convert h.2 using 1
  congr 1
  field_simp

end EinsteinRelation.Correctors
