import EinsteinRelation.Correctors.TwoCoefficientKernelPairing
import EinsteinRelation.Correctors.BorelKernelSelection

/-! # Limits of E.1 kernels and the closed E.1 graph

Source: `paper/main.tex:777–784,842`; AKM Proposition E.1, printed
pp. 499–501, and the duality argument in its proof, p. 510. Let
coefficients converge pointwise, and let E.1 kernels with one constant
function converge pointwise at positive times to a continuous kernel. Then
the limit is the E.1 kernel of the limit coefficient: pairing it against
that kernel, the coefficient-difference term vanishes in the limit and the
endpoints are identified by the Gaussian bound. Hence the E.1 graph over
the Polish continuous-coefficient carrier is closed. This is the analytic
graph obligation of `BorelKernel.measurableKernelHypothesis_of_analytic_graph`,
so the coefficient-joint measurable kernel selection follows from E.1 alone.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

private theorem mul_le_sq_add_sq {a b l : ℝ} (hl : 0 < l) :
    a * b ≤ a ^ 2 / (2 * l) + l / 2 * b ^ 2 := by
  have h := sq_nonneg (a - l * b)
  have h2 : a ^ 2 / (2 * l) + l / 2 * b ^ 2 - a * b = (a - l * b) ^ 2 / (2 * l) := by
    field_simp
    ring
  have h3 : 0 ≤ (a - l * b) ^ 2 / (2 * l) := div_nonneg h (by positivity)
  linarith

private theorem dot_mulVec_comm {d : ℕ} (M : Mat d) (hM : M.transpose = M)
    (x y : Vec d) : dot x (M.mulVec y) = dot (M.mulVec x) y := by
  change dotProduct x (M.mulVec y) = dotProduct (M.mulVec x) y
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hM]

/-- A pointwise limit of Gaussian probability kernels with one constant
function, continuous at positive times, is again such a kernel. -/
theorem IsGaussianProbabilityKernel.of_tendsto {d : ℕ} {K : ℝ} (hK : 0 < K) {C : ℝ → ℝ}
    {Pn : ℕ → ℝ → Vec d → Vec d → ℝ} (hn : ∀ n, IsGaussianProbabilityKernel K C (Pn n))
    {P : ℝ → Vec d → Vec d → ℝ}
    (hPc : ContinuousOn (fun z : ℝ × (Vec d × Vec d) => P z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hPn : ∀ t, 0 < t → ∀ x y, Tendsto (fun n => Pn n t x y) atTop (𝓝 (P t x y))) :
    IsGaussianProbabilityKernel K C P := by
  have hgauss : ∀ α : ℝ, 0 < α → α < K⁻¹ → ∀ t : ℝ, 0 < t → ∀ x y : Vec d,
      |P t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
        Real.exp (-α * euclideanSq (x - y) / (4 * t)) :=
    fun α hα hαK t ht x y =>
      le_of_tendsto' (hPn t ht x y).abs fun n => (hn n).2.2.2.2 α hα hαK t ht x y
  have hsym : ∀ t, 0 < t → ∀ x y, P t x y = P t y x := fun t ht x y =>
    tendsto_nhds_unique (hPn t ht x y)
      ((hPn t ht y x).congr fun n => ((hn n).2.2.1 t ht x y).symm)
  have hcont (t : ℝ) (ht : 0 < t) (x : Vec d) : Continuous (fun y => P t x y) := by
    apply continuousOn_univ.mp
    exact hPc.comp
      ((continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn)
      (fun _ _ => ⟨ht, Set.mem_univ _⟩)
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  have hmass : ∀ t, 0 < t → ∀ x, Integrable (P t x) volume ∧ (∫ y, P t x y ∂volume) = 1 := by
    intro t ht x
    have hbound : Integrable (fun y => C α * (4 * Real.pi / α) ^ ((d : ℝ) / 2) *
        euclideanHeatKernel (t / α) (x - y)) volume :=
      ((integrable_euclideanHeatKernel (div_pos ht hα)).comp_sub_left x).const_mul _
    have hdom (Q : ℝ → Vec d → Vec d → ℝ)
        (hQ : ∀ y, |Q t x y| ≤ C α * t ^ (-(d : ℝ) / 2) *
          Real.exp (-α * euclideanSq (x - y) / (4 * t))) (y : Vec d) :
        ‖Q t x y‖ ≤ C α * (4 * Real.pi / α) ^ ((d : ℝ) / 2) *
          euclideanHeatKernel (t / α) (x - y) := by
      rw [Real.norm_eq_abs]
      have hq := hQ y
      rw [mul_assoc, gaussian_majorant_eq_euclideanHeatKernel hα ht] at hq
      linarith only [hq]
    refine ⟨hbound.mono' (hcont t ht x).aestronglyMeasurable
      (Filter.Eventually.of_forall (hdom P (hgauss α hα hαK t ht x))), ?_⟩
    have hlim := tendsto_integral_of_dominated_convergence _
      (fun n => ((hn n).space_continuous_right ht x).aestronglyMeasurable) hbound
      (fun n => Filter.Eventually.of_forall (hdom (Pn n) ((hn n).2.2.2.2 α hα hαK t ht x)))
      (Filter.Eventually.of_forall fun y => hPn t ht x y)
    exact tendsto_nhds_unique (hlim.congr fun n => ((hn n).2.2.2.1 t ht x).2.1)
      tendsto_const_nhds
  refine ⟨hPc, fun t ht x y => ge_of_tendsto' (hPn t ht x y) fun n => (hn n).2.1 t ht x y,
    hsym, fun t ht x => ?_, hgauss⟩
  have hswap : (fun y => P t y x) = P t x := funext fun y => hsym t ht y x
  rw [hswap]
  exact ⟨(hmass t ht x).1, (hmass t ht x).2, (hmass t ht x).1, (hmass t ht x).2⟩

/-- Along converging coefficients, the coefficient-difference pairing of
the limit coefficient's E.1 kernel against the approximating kernels
vanishes in the strip integral. Source: AKM (E.7)–(E.8). -/
theorem tendsto_kernelCoefficientDefect_integral {d : ℕ} {K : ℝ} (hK : 0 < K)
    {C CA : ℝ → ℝ} {A : Coefficient d K} {PA : ℝ → Vec d → Vec d → ℝ}
    {XA YA : ℝ → Vec d → Vec d → Vec d} {HA : ℝ → Vec d → Vec d → Mat d}
    (hA : HeatKernelProperties A PA XA YA HA CA)
    {An : ℕ → Coefficient d K} {Pn : ℕ → ℝ → Vec d → Vec d → ℝ}
    {Xn Yn : ℕ → ℝ → Vec d → Vec d → Vec d} {Hn : ℕ → ℝ → Vec d → Vec d → Mat d}
    (hn : ∀ n, HeatKernelProperties (An n) (Pn n) (Xn n) (Yn n) (Hn n) C)
    (hAn : ∀ x, Tendsto (fun n => An n x) atTop (𝓝 (A x)))
    {T s : ℝ} (hs : 0 < s) (hsT : s < T - s) (x y : Vec d) :
    Tendsto (fun n => ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
      |kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2|) atTop (𝓝 0) := by
  have hbT : T - s < T := by linarith
  have htr : MeasurePreserving (fun z : ℝ × Vec d => (T-z.1, z.2))
      (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d))))
      (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [sub_sub_cancel] using akm_time_reflection_strip_measurePreserving d T s (T-s)
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  obtain ⟨E, hE0, hE⟩ := akm_heatKernel_global_gradient_sq_le (d := d) hK hs hsT
  have hCα : 0 ≤ C α := (hn 0).isGaussianProbabilityKernel.constant_nonneg hα hαK
  let Mb : ℝ := E * ((T - s + s/2 - s/2) * (C α * (s/2) ^ (-(d : ℝ) / 2)))
  have hMb0 : 0 ≤ Mb := mul_nonneg hE0 (mul_nonneg (by linarith)
    (mul_nonneg hCα (Real.rpow_nonneg (by linarith) _)))
  have hG := akm_heatKernel_global_gradient_memLp hK hA hs hsT y
  have hWn (n : ℕ) := akm_heatKernel_global_gradient_memLp hK (hn n) hs hsT x
  have hWm (n : ℕ) : MemLp (fun z : ℝ × Vec d => euclideanNorm (Xn n (T-z.1) z.2 x)) 2
      (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) := by
    simpa only [Function.comp_def] using (hWn n).2.comp_measurePreserving htr
  have hWsq (n : ℕ) : (∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
      euclideanNorm (Xn n (T-z.1) z.2 x) ^ 2) ≤ Mb := by
    have hm2 : AEStronglyMeasurable
        (fun z : ℝ × Vec d => euclideanNorm (Xn n z.1 z.2 x) ^ 2)
        (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) :=
      (hWn n).2.1.pow 2
    have hmap := integral_map (f := fun z : ℝ × Vec d => euclideanNorm (Xn n z.1 z.2 x) ^ 2)
      htr.measurable.aemeasurable (by rw [htr.map_eq]; exact hm2)
    rw [htr.map_eq] at hmap
    calc
      (∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
          euclideanNorm (Xn n (T-z.1) z.2 x) ^ 2) =
          ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
            euclideanNorm (Xn n z.1 z.2 x) ^ 2 := hmap.symm
      _ ≤ E * ∫ z in Set.Ioo (s/2) (T-s+s/2) ×ˢ (Set.univ : Set (Vec d)),
            Pn n z.1 z.2 x ^ 2 := hE (hn n) x
      _ ≤ Mb := mul_le_mul_of_nonneg_left
          ((hn n).isGaussianProbabilityKernel.strip_sq_integral_le hα hαK (half_pos hs)
            (by linarith) x) hE0
  have hpt (n : ℕ) (z : ℝ × Vec d) :
      |kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2| ≤
        (∑ i, ∑ j, |(A z.2 - An n z.2) i j|) *
          (euclideanNorm (XA z.1 z.2 y) * euclideanNorm (Xn n (T-z.1) z.2 x)) := by
    have h1 : kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2 =
        dot (XA z.1 z.2 y) ((A z.2 - An n z.2).mulVec (Xn n (T-z.1) z.2 x)) := by
      unfold kernelCoefficientDefect
      rw [← dot_mulVec_comm (A z.2) (A.symmetric z.2)]
      change dotProduct _ _ - dotProduct _ _ = dotProduct _ _
      rw [dotProduct_comm ((An n z.2).mulVec _), Matrix.sub_mulVec, dotProduct_sub]
    rw [h1]
    exact abs_dot_mulVec_le _ _ _
  have hentry (n : ℕ) (w : Vec d) :
      (∑ i, ∑ j, |(A w - An n w) i j|) ≤ (d : ℝ) * d * (2 * K) := by
    calc
      (∑ i, ∑ j, |(A w - An n w) i j|) ≤ ∑ _i : Fin d, ∑ _j : Fin d, (2 * K) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [Matrix.sub_apply]
        exact (abs_sub _ _).trans (by linarith [coefficient_entry_abs_le hK A w i j,
              coefficient_entry_abs_le hK (An n) w i j])
      _ = (d : ℝ) * d * (2 * K) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  have hentry0 (n : ℕ) (w : Vec d) : 0 ≤ ∑ i, ∑ j, |(A w - An n w) i j| :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hm0 (w : Vec d) :
      Tendsto (fun n => ∑ i, ∑ j, |(A w - An n w) i j|) atTop (𝓝 0) := by
    have h := tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun i _ =>
      tendsto_finset_sum (Finset.univ : Finset (Fin d)) fun j _ =>
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A w i j) atTop (𝓝 (A w i j))).sub
          (((continuous_id.matrix_elem i j).tendsto (A w)).comp (hAn w))).abs
    simpa using h
  have hAm (B : Coefficient d K) (i k : Fin d) :
      AEStronglyMeasurable (fun z : ℝ × Vec d => B z.2 i k)
        (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) :=
    (B.locally_integrable i k).aestronglyMeasurable.comp_snd.mono_measure
      Measure.restrict_le_self
  have hmm (n : ℕ) : AEStronglyMeasurable
      (fun z : ℝ × Vec d => ∑ i, ∑ j, |(A z.2 - An n z.2) i j|)
      (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) :=
    Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
        continuous_abs.comp_aestronglyMeasurable ((hAm A i j).sub (hAm (An n) i j))
  have hFb (n : ℕ) : ∀ z : ℝ × Vec d,
      ‖((∑ i, ∑ j, |(A z.2 - An n z.2) i j|) * euclideanNorm (XA z.1 z.2 y)) ^ 2‖ ≤
        ((d : ℝ) * d * (2 * K)) ^ 2 * euclideanNorm (XA z.1 z.2 y) ^ 2 := fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hentry0 n z.2) (hentry n z.2) 2) (sq_nonneg _)
  have hFi (n : ℕ) : Integrable
      (fun z : ℝ × Vec d =>
        ((∑ i, ∑ j, |(A z.2 - An n z.2) i j|) * euclideanNorm (XA z.1 z.2 y)) ^ 2)
      (volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)))) :=
    (hG.2.integrable_sq.const_mul _).mono' (((hmm n).mul hG.2.1).pow 2)
      (Filter.Eventually.of_forall (hFb n))
  let δ : ℕ → ℝ := fun n => ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
    ((∑ i, ∑ j, |(A z.2 - An n z.2) i j|) * euclideanNorm (XA z.1 z.2 y)) ^ 2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d))))
      (F := fun n z => ((∑ i, ∑ j, |(A z.2 - An n z.2) i j|) *
        euclideanNorm (XA z.1 z.2 y)) ^ 2)
      (f := fun _ => 0)
      (fun z => ((d : ℝ) * d * (2 * K)) ^ 2 * euclideanNorm (XA z.1 z.2 y) ^ 2)
      (fun n => ((hmm n).mul hG.2.1).pow 2) (hG.2.integrable_sq.const_mul _)
      (fun n => Filter.Eventually.of_forall (hFb n))
      (Filter.Eventually.of_forall fun z => by
        simpa using ((hm0 z.2).mul_const (euclideanNorm (XA z.1 z.2 y))).pow 2)
    rw [integral_zero] at h
    exact h
  have hδ0 (n : ℕ) : 0 ≤ δ n := integral_nonneg fun z => sq_nonneg _
  have hI (n : ℕ) {l : ℝ} (hl : 0 < l) :
      (∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
        |kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2|) ≤
        δ n / (2 * l) + l / 2 * Mb := by
    have hEi := integrable_kernelCoefficientDefect hK hA (hn n) hs hsT hbT x y
    have hi2 := (hWm n).integrable_sq
    calc
      (∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
          |kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2|) ≤
          ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
            (((∑ i, ∑ j, |(A z.2 - An n z.2) i j|) * euclideanNorm (XA z.1 z.2 y)) ^ 2 /
              (2 * l) + l / 2 * euclideanNorm (Xn n (T-z.1) z.2 x) ^ 2) := by
        refine integral_mono hEi.abs (((hFi n).div_const _).add (hi2.const_mul _)) fun z => ?_
        refine (hpt n z).trans ?_
        rw [← mul_assoc]
        exact mul_le_sq_add_sq hl
      _ = δ n / (2 * l) + l / 2 * ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
            euclideanNorm (Xn n (T-z.1) z.2 x) ^ 2 := by
        rw [integral_add ((hFi n).div_const _) (hi2.const_mul _), integral_div,
          integral_const_mul]
      _ ≤ δ n / (2 * l) + l / 2 * Mb := by
        gcongr
        exact hWsq n
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM1 : 0 < Mb + 1 := by linarith
  have hl0 : 0 < ε / (2 * (Mb + 1)) := div_pos hε (by linarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hδ (ε / (2 * (Mb + 1)) * ε) (mul_pos hl0 hε)
  refine ⟨N, fun n hn => ?_⟩
  have hδn : δ n < ε / (2 * (Mb + 1)) * ε := by
    have h := hN n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (hδ0 n)] at h
  have hIn := hI n hl0
  have hpos : 0 ≤ ∫ z in Set.Ioo s (T-s) ×ˢ (Set.univ : Set (Vec d)),
      |kernelCoefficientDefect A (An n) XA (Xn n) T x y z.1 z.2| :=
    integral_nonneg fun z => abs_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  have h1 : δ n / (2 * (ε / (2 * (Mb + 1)))) < ε / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    calc δ n < ε / (2 * (Mb + 1)) * ε := hδn
      _ = ε / 2 * (2 * (ε / (2 * (Mb + 1)))) := by ring
  have h2 : ε / (2 * (Mb + 1)) / 2 * Mb ≤ ε / 4 := by
    have hM1' : Mb + 1 ≠ 0 := hM1.ne'
    rw [show ε / (2 * (Mb + 1)) / 2 * Mb = ε / 4 * (Mb / (Mb + 1)) by field_simp; ring]
    exact mul_le_of_le_one_right (by linarith)
      ((div_le_one hM1).mpr (by linarith))
  linarith

/-- Pairing the limit coefficient's E.1 kernel against the limit of the
approximating kernels gives a time-symmetric interior pairing.
Source: AKM Proposition E.1 proof, p. 510. -/
theorem pairing_limit_interior_eq {d : ℕ} {K : ℝ} (hK : 0 < K)
    {C CA : ℝ → ℝ} {A : Coefficient d K} {PA : ℝ → Vec d → Vec d → ℝ}
    {XA YA : ℝ → Vec d → Vec d → Vec d} {HA : ℝ → Vec d → Vec d → Mat d}
    (hA : HeatKernelProperties A PA XA YA HA CA)
    {An : ℕ → Coefficient d K} {Pn : ℕ → ℝ → Vec d → Vec d → ℝ}
    {Xn Yn : ℕ → ℝ → Vec d → Vec d → Vec d} {Hn : ℕ → ℝ → Vec d → Vec d → Mat d}
    (hn : ∀ n, HeatKernelProperties (An n) (Pn n) (Xn n) (Yn n) (Hn n) C)
    (hAn : ∀ x, Tendsto (fun n => An n x) atTop (𝓝 (A x)))
    {P : ℝ → Vec d → Vec d → ℝ}
    (hPn : ∀ t, 0 < t → ∀ x y, Tendsto (fun n => Pn n t x y) atTop (𝓝 (P t x y)))
    {T s : ℝ} (hs : 0 < s) (hsT : s < T - s) (x y : Vec d) :
    (∫ z, PA (T-s) z y * P (T-(T-s)) z x ∂volume) = ∫ z, PA s z y * P (T-s) z x ∂volume := by
  have hbT : T - s < T := by linarith
  have hAL := hA.isGaussianProbabilityKernel
  let α : ℝ := K⁻¹ / 2
  have hα : 0 < α := half_pos (inv_pos.mpr hK)
  have hαK : α < K⁻¹ := half_lt_self (inv_pos.mpr hK)
  have hconv (r : ℝ) (hr : 0 < r) (hrT : r < T) :
      Tendsto (fun n => ∫ z, PA r z y * Pn n (T-r) z x ∂volume) atTop
        (𝓝 (∫ z, PA r z y * P (T-r) z x ∂volume)) := by
    have hTr : 0 < T - r := sub_pos.mpr hrT
    apply tendsto_integral_of_dominated_convergence
      (fun z => |PA r z y| * (C α * (T-r) ^ (-(d : ℝ) / 2)))
    · intro n
      exact ((hAL.space_continuous hr y).mul
        ((hn n).isGaussianProbabilityKernel.space_continuous hTr x)).aestronglyMeasurable
    · exact ((hAL.2.2.2.1 r hr y).2.2.1).abs.mul_const _
    · intro n
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        ((hn n).isGaussianProbabilityKernel.abs_le_rpow hα hαK hTr z x) (abs_nonneg _)
    · exact Filter.Eventually.of_forall fun z => (hPn (T-r) hTr z x).const_mul _
  have herr := tendsto_kernelCoefficientDefect_integral hK hA hn hAn hs hsT x y
  have hlim := ((hconv (T-s) (by linarith) hbT).sub (hconv s hs (by linarith))).abs
  have hle := le_of_tendsto_of_tendsto' hlim herr fun n =>
    kernel_two_coefficient_pairing_sub_abs_le hK hA (hn n) hs hsT hbT x y
  have h0 := abs_nonpos_iff.mp hle
  linarith only [h0]

/-- A pointwise limit of E.1 kernels of pointwise converging coefficients,
sharing one constant function and continuous at positive times, is the E.1
kernel of the limit coefficient at every positive time.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1, pp. 499–501,
and the duality argument of its proof, p. 510. -/
theorem heatKernel_eq_of_tendsto {d : ℕ} {K : ℝ} (hK : 0 < K)
    {C CA : ℝ → ℝ} {A : Coefficient d K} {PA : ℝ → Vec d → Vec d → ℝ}
    {XA YA : ℝ → Vec d → Vec d → Vec d} {HA : ℝ → Vec d → Vec d → Mat d}
    (hA : HeatKernelProperties A PA XA YA HA CA)
    {An : ℕ → Coefficient d K} {Pn : ℕ → ℝ → Vec d → Vec d → ℝ}
    {Xn Yn : ℕ → ℝ → Vec d → Vec d → Vec d} {Hn : ℕ → ℝ → Vec d → Vec d → Mat d}
    (hn : ∀ n, HeatKernelProperties (An n) (Pn n) (Xn n) (Yn n) (Hn n) C)
    (hAn : ∀ x, Tendsto (fun n => An n x) atTop (𝓝 (A x)))
    {P : ℝ → Vec d → Vec d → ℝ}
    (hPc : ContinuousOn (fun z : ℝ × (Vec d × Vec d) => P z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hPn : ∀ t, 0 < t → ∀ x y, Tendsto (fun n => Pn n t x y) atTop (𝓝 (P t x y))) :
    ∀ t, 0 < t → ∀ x y, P t x y = PA t x y := by
  have hL : IsGaussianProbabilityKernel K C P :=
    IsGaussianProbabilityKernel.of_tendsto hK (fun n => (hn n).isGaussianProbabilityKernel)
      hPc hPn
  have hAL := hA.isGaussianProbabilityKernel
  intro T hT x y
  have h0 := hAL.pairing_initial hL hK hT x y
  have h1 := hL.pairing_initial hAL hK hT y x
  have heq : (fun s => ∫ z, P s z x * PA (T-s) z y ∂volume) =ᶠ[𝓝[>] 0]
      (fun s => ∫ z, PA s z y * P (T-s) z x ∂volume) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (half_pos hT))] with s hs hsT
    have hs' : 0 < s := hs
    have hsT' : s < T - s := by
      have : s < T / 2 := hsT
      linarith
    rw [← pairing_limit_interior_eq hK hA hn hAn hPn hs' hsT' x y, sub_sub_cancel]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hTyx := tendsto_nhds_unique (h1.congr' heq) h0
  rw [hL.2.2.1 T hT x y]
  exact hTyx.symm

namespace BorelKernel

/-- The zero extension of a continuous positive-time kernel is continuous
at positive times. -/
theorem continuousOn_extendKernel {d : ℕ} (P : ContinuousKernel d) :
    ContinuousOn (fun z : ℝ × (Vec d × Vec d) => extendKernel P z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  rw [continuousOn_iff_continuous_restrict]
  have heq : (Set.restrict (Set.Ioi 0 ×ˢ Set.univ)
      fun z : ℝ × (Vec d × Vec d) => extendKernel P z.1 z.2.1 z.2.2) =
      fun w => P (⟨w.1.1, w.2.1⟩, w.1.2) := by
    funext w
    exact extendKernel_pos P _ w.2.1 _ _
  rw [heq]
  exact P.continuous.comp
    (((continuous_fst.comp continuous_subtype_val).subtype_mk fun w => w.2.1).prodMk
      (continuous_snd.comp continuous_subtype_val))

/-- The exact E.1 graph over continuous normalized coefficients is closed.
Source: `paper/main.tex:777–784,842`; AKM Proposition E.1, pp. 499–501. -/
theorem isClosed_kernelGraph {d : ℕ} {K : ℝ} (hK : 0 < K) (C : ℝ → ℝ)
    (hex : ∀ A : Coefficient d K,
      ∃ (P : ℝ → Vec d → Vec d → ℝ)
        (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C) :
    IsClosed {z : ContinuousCoefficient d K × ContinuousKernel d |
      kernelGraph C z.1 z.2} := by
  refine IsSeqClosed.isClosed ?_
  intro u z hu hlim
  have hu' : ∀ n, ∃ (X Y : ℝ → Vec d → Vec d → Vec d) (H : ℝ → Vec d → Vec d → Mat d),
      HeatKernelProperties (toCoefficient (u n).1) (extendKernel (u n).2) X Y H C := hu
  choose X Y H hXYH using hu'
  obtain ⟨PA, XA, YA, HA, hA⟩ := hex (toCoefficient z.1)
  have h1 : Tendsto (fun n => (u n).1) atTop (𝓝 z.1) :=
    ((continuous_fst.tendsto z).comp hlim)
  have h2 : Tendsto (fun n => (u n).2) atTop (𝓝 z.2) :=
    ((continuous_snd.tendsto z).comp hlim)
  have hcoef (x : Vec d) : Tendsto (fun n => toCoefficient (u n).1 x) atTop
      (𝓝 (toCoefficient z.1 x)) :=
    (((continuous_eval_const x).comp continuous_subtype_val).tendsto z.1).comp h1
  have hker (t : ℝ) (ht : 0 < t) (x y : Vec d) :
      Tendsto (fun n => extendKernel (u n).2 t x y) atTop (𝓝 (extendKernel z.2 t x y)) := by
    simp only [extendKernel_pos _ t ht]
    exact ((continuous_eval_const _).tendsto z.2).comp h2
  have heq := heatKernel_eq_of_tendsto hK hA hXYH hcoef (continuousOn_extendKernel z.2) hker
  show kernelGraph C z.1 z.2
  exact ⟨XA, YA, HA, heatKernelProperties_congr_positive hA
    fun t ht x y => (heq t ht x y).symm⟩

/-- The exact E.1 graph is analytic, which discharges the remaining graph
obligation of the measurable kernel selection. Source: `paper/main.tex:777–784,842`. -/
theorem analyticSet_kernelGraph {d : ℕ} {K : ℝ} (hK : 0 < K) (C : ℝ → ℝ)
    (hex : ∀ A : Coefficient d K,
      ∃ (P : ℝ → Vec d → Vec d → ℝ)
        (X Y : ℝ → Vec d → Vec d → Vec d)
        (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A P X Y H C) :
    AnalyticSet {z : ContinuousCoefficient d K × ContinuousKernel d |
      kernelGraph C z.1 z.2} :=
  (isClosed_kernelGraph hK C hex).analyticSet

/-- The coefficient-joint measurable scalar E.1 kernel selection used by
the final corrector chain, from the frozen E.1 input alone. The constant
function is chosen before the coefficient and the environment law.
Source: `paper/main.tex:693–698,777–784,842`; AKM Proposition E.1. -/
theorem measurableKernelHypothesis_of_parabolicHeatKernel (hE : ParabolicHeatKernel) :
    ∀ (d : ℕ) [Fact (2 ≤ d)] (L r₀ : ℝ) (Q : EnvironmentLaw d L r₀),
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK :=
  measurableKernelHypothesis_of_analytic_graph hE fun _ _ _ hK C hex =>
    analyticSet_kernelGraph (zero_lt_one.trans hK) C hex

end BorelKernel

end EinsteinRelation.Correctors
