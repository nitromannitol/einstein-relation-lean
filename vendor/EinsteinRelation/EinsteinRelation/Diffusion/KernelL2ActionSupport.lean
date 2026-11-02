import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.Invariance

/-! # Markov kernel actions on weighted `L²` spaces

For a Markov kernel preserving a sigma-finite reference measure, this module
constructs the induced action by integrating representatives and proves its
contraction and composition properties. The hypotheses are generic; no
canonical diffusion kernel or invariant weighted measure is constructed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory NNReal ProbabilityTheory

namespace EinsteinRelation.WeightedKernelL2

noncomputable section

variable {α : Type*} [MeasurableSpace α]

/-- The pointwise integral action of a kernel on a measurable representative. -/
def kernelIntegral (K : Kernel α α) (f : α → ℝ) : α → ℝ :=
  fun x => ∫ y, f y ∂K x

private theorem integral_sq_mean_le {m : Measure α} [IsProbabilityMeasure m] {f : α → ℝ}
    (hf : Integrable f m) (hf2 : Integrable (fun x => f x ^ 2) m) :
    (∫ x, f x ∂m) ^ 2 ≤ ∫ x, f x ^ 2 ∂m := by
  have hsq := (Even.convexOn_pow (n := 2) ⟨1, by norm_num⟩).map_integral_le
    (continuousOn_pow 2) isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _) hf hf2
  simpa [pow_two] using hsq

private theorem kernelIntegral_sq_le {K : Kernel α α} [IsMarkovKernel K]
    {f : α → ℝ} (hf : StronglyMeasurable f)
    (x : α) (hf2 : Integrable (fun y => f y ^ 2) (K x)) :
    (kernelIntegral K f x) ^ 2 ≤ ∫ y, f y ^ 2 ∂K x := by
  letI : IsProbabilityMeasure (K x) := inferInstance
  letI : IsFiniteMeasure (K x) := inferInstance
  have hf' : AEStronglyMeasurable f (K x) := hf.aestronglyMeasurable
  have hfmem : MemLp f 2 (K x) :=
    (memLp_two_iff_integrable_sq hf').2 hf2
  have hfx : Integrable f (K x) := by
    exact memLp_one_iff_integrable.mp (hfmem.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  simpa [kernelIntegral] using integral_sq_mean_le hfx hf2

/-- An invariant Markov kernel sends an `L²` representative to an `L²` function by actual kernel
integration. Markovness and invariance are generic interface conditions; this does not construct a
source transition kernel or prove that a source weighted measure is invariant. -/
theorem kernelIntegral_memLp {K : Kernel α α} [IsMarkovKernel K] {m : Measure α}
    [SigmaFinite m] (hInv : Kernel.Invariant K m) {f : α → ℝ}
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 m) :
    MemLp (kernelIntegral K f) 2 m := by
  have hsq : Integrable (fun y => f y ^ 2) m := hf2.integrable_sq
  have hinv : Measure.bind m K = m := hInv.def
  have hsqComp : Integrable (fun y => f y ^ 2) (K ∘ₘ m) := by
    change Integrable (fun y => f y ^ 2) (Measure.bind m K)
    rw [hinv]
    exact hsq
  have hsmComp : AEStronglyMeasurable (fun y => f y ^ 2) (Measure.bind m K) := by
    rw [hinv]
    exact hsq.aestronglyMeasurable
  have hcompParts :=
    (Measure.integrable_comp_iff (κ := K) (μ := m) hsmComp).1 hsqComp
  have hsm : StronglyMeasurable (kernelIntegral K f) := by
    exact hf.integral_kernel
  have hcompSq : Integrable (fun x => ∫ y, f y ^ 2 ∂K x) m := by
    refine hcompParts.2.congr ?_
    filter_upwards with x
    apply integral_congr_ae
    exact ae_of_all _ fun y => Real.norm_of_nonneg (sq_nonneg (f y))
  have hsmSq : AEStronglyMeasurable (fun x => kernelIntegral K f x ^ 2) m := by
    simp only [pow_two]
    exact (hsm.mul hsm).aestronglyMeasurable
  have hsqOut : Integrable (fun x => kernelIntegral K f x ^ 2) m := by
    refine hcompSq.mono' hsmSq ?_
    filter_upwards [hcompParts.1] with x hx
    have hbound := kernelIntegral_sq_le (K := K) hf x hx
    calc
      ‖kernelIntegral K f x ^ 2‖ = kernelIntegral K f x ^ 2 :=
        Real.norm_of_nonneg (sq_nonneg _)
      _ ≤ ∫ y, f y ^ 2 ∂K x := hbound
  exact (memLp_two_iff_integrable_sq hsm.aestronglyMeasurable).2 hsqOut

/-- Kernel integration respects equality of representatives almost everywhere under an invariant
reference measure. -/
theorem kernelIntegral_ae_congr {K : Kernel α α} [IsMarkovKernel K] {m : Measure α}
    (hInv : Kernel.Invariant K m) {f g : α → ℝ} (hfg : f =ᵐ[m] g) :
    kernelIntegral K f =ᵐ[m] kernelIntegral K g := by
  have hinv : Measure.bind m K = m := hInv.def
  have hfg' : f =ᵐ[Measure.bind m K] g := by rw [hinv]; exact hfg
  filter_upwards [Measure.ae_ae_of_ae_comp hfg'] with x hx
  exact integral_congr_ae hx

/-- The actual induced linear-space element on `L²(m)`, constructed by integrating a measurable
representative and passing the resulting function through the `MemLp.toLp` quotient map. -/
noncomputable def kernelIntegralL2 {K : Kernel α α} [IsMarkovKernel K] {m : Measure α}
    [SigmaFinite m] (hInv : Kernel.Invariant K m) (f : Lp ℝ 2 m) : Lp ℝ 2 m :=
  (kernelIntegral_memLp hInv (Lp.stronglyMeasurable f) (Lp.memLp f)).toLp
    (kernelIntegral K f)

/-- The `L²` action is represented almost everywhere by the actual kernel integral. -/
theorem kernelIntegralL2_coe {K : Kernel α α} [IsMarkovKernel K] {m : Measure α}
    [SigmaFinite m] (hInv : Kernel.Invariant K m) (f : Lp ℝ 2 m) :
    kernelIntegralL2 hInv f =ᵐ[m] kernelIntegral K f := by
  exact MemLp.coeFn_toLp (kernelIntegral_memLp hInv (Lp.stronglyMeasurable f) (Lp.memLp f))

theorem kernelIntegralL2_sq_integral_le {K : Kernel α α} [IsMarkovKernel K]
    {m : Measure α} [SigmaFinite m] (hInv : Kernel.Invariant K m) (f : Lp ℝ 2 m) :
    ∫ x, kernelIntegralL2 hInv f x ^ 2 ∂m ≤ ∫ x, f x ^ 2 ∂m := by
  let q : α → ℝ := fun x => f x ^ 2
  have hqsm : StronglyMeasurable q := by
    simp only [q, pow_two]
    exact (Lp.stronglyMeasurable f).mul (Lp.stronglyMeasurable f)
  have hqint : Integrable q m := by
    simpa [q] using (Lp.memLp f).integrable_sq
  have hinv : Measure.bind m K = m := hInv.def
  have hqbind : Integrable q (Measure.bind m K) := by rw [hinv]; exact hqint
  have hqsmBind : AEStronglyMeasurable q (Measure.bind m K) := by
    rw [hinv]
    exact hqint.aestronglyMeasurable
  have hcompParts :=
    (Measure.integrable_comp_iff (κ := K) (μ := m) hqsmBind).1 hqbind
  have hpoint : ∀ᵐ x ∂m, (kernelIntegral K f x) ^ 2 ≤ ∫ y, q y ∂K x := by
    filter_upwards [hcompParts.1] with x hx
    exact kernelIntegral_sq_le (K := K) (Lp.stronglyMeasurable f) x (by simpa [q] using hx)
  have hpointEnnreal : ∀ᵐ x ∂m,
      ENNReal.ofReal ((kernelIntegral K f x) ^ 2) ≤ ∫⁻ y, ENNReal.ofReal (q y) ∂K x := by
    filter_upwards [hpoint, hcompParts.1] with x hx hxi
    have hqnonneg : 0 ≤ᵐ[K x] q := ae_of_all _ fun y => sq_nonneg (f y)
    calc
      ENNReal.ofReal ((kernelIntegral K f x) ^ 2) ≤
          ENNReal.ofReal (∫ y, q y ∂K x) := ENNReal.ofReal_le_ofReal hx
      _ = ∫⁻ y, ENNReal.ofReal (q y) ∂K x :=
        ofReal_integral_eq_lintegral_ofReal hxi hqnonneg
  have hlintegralBound := lintegral_mono_ae hpointEnnreal
  have hqEnnrealAEM : AEMeasurable (fun y => ENNReal.ofReal (q y)) (Measure.bind m K) := by
    rw [hinv]
    exact hqsm.aemeasurable.ennreal_ofReal
  have hbind := Measure.lintegral_bind (Kernel.aemeasurable K) hqEnnrealAEM
  rw [hinv] at hbind
  rw [← hbind] at hlintegralBound
  have hleftAe : kernelIntegralL2 hInv f =ᵐ[m] kernelIntegral K f :=
    kernelIntegralL2_coe hInv f
  have hleftIntegral :
      ∫ x, kernelIntegralL2 hInv f x ^ 2 ∂m =
        ∫ x, kernelIntegral K f x ^ 2 ∂m := by
    apply integral_congr_ae
    filter_upwards [hleftAe] with x hx
    rw [hx]
  have hleftInt : Integrable (fun x => kernelIntegral K f x ^ 2) m :=
    (kernelIntegral_memLp hInv (Lp.stronglyMeasurable f) (Lp.memLp f)).integrable_sq
  have hleftNN : 0 ≤ᵐ[m] fun x => (kernelIntegral K f x) ^ 2 :=
    ae_of_all _ fun x => sq_nonneg _
  have hleftENN := ofReal_integral_eq_lintegral_ofReal hleftInt hleftNN
  have hrightNN : 0 ≤ᵐ[m] q := ae_of_all _ fun x => sq_nonneg (f x)
  have hrightENN := ofReal_integral_eq_lintegral_ofReal hqint hrightNN
  calc
    ∫ x, kernelIntegralL2 hInv f x ^ 2 ∂m =
        ∫ x, kernelIntegral K f x ^ 2 ∂m := hleftIntegral
    _ ≤ ∫ x, q x ∂m := by
      apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hrightNN)).1
      rw [hleftENN, hrightENN]
      exact hlintegralBound
    _ = ∫ x, f x ^ 2 ∂m := rfl

/-- Jensen's inequality and invariance make the induced `L²` action contractive. -/
theorem kernelIntegralL2_norm_le {K : Kernel α α} [IsMarkovKernel K]
    {m : Measure α} [SigmaFinite m] (hInv : Kernel.Invariant K m) (f : Lp ℝ 2 m) :
    ‖kernelIntegralL2 hInv f‖ ≤ ‖f‖ := by
  have hsq := kernelIntegralL2_sq_integral_le hInv f
  have hnormSq (g : Lp ℝ 2 m) : ‖g‖ ^ 2 = ∫ x, g x ^ 2 ∂m := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    congr 1
    funext x
    simp
  rw [← hnormSq, ← hnormSq] at hsq
  nlinarith [norm_nonneg (kernelIntegralL2 hInv f), norm_nonneg f]

private theorem kernelIntegral_comp_ae {κ η : Kernel α α} [IsMarkovKernel κ]
    [IsMarkovKernel η] {m : Measure α} [SigmaFinite m]
    (hκ : Kernel.Invariant κ m) (hη : Kernel.Invariant η m) {f : α → ℝ}
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 m) :
    kernelIntegral κ (kernelIntegral η f) =ᵐ[m] kernelIntegral (η ∘ₖ κ) f := by
  let q : α → ℝ := fun x => f x ^ 2
  have hqsm : StronglyMeasurable q := by
    simp only [q, pow_two]
    exact hf.mul hf
  have hqint : Integrable q m := by simpa [q] using hf2.integrable_sq
  have hInvComp : Kernel.Invariant (η ∘ₖ κ) m := Kernel.Invariant.comp hη hκ
  have hqBind : Integrable q (Measure.bind m (η ∘ₖ κ)) := by
    rw [hInvComp.def]
    exact hqint
  have hqsmBind : AEStronglyMeasurable q (Measure.bind m (η ∘ₖ κ)) := by
    rw [hInvComp.def]
    exact hqint.aestronglyMeasurable
  have hcompParts :=
    (Measure.integrable_comp_iff (κ := η ∘ₖ κ) (μ := m) hqsmBind).1 hqBind
  have hfComp : ∀ᵐ x ∂m, Integrable f ((η ∘ₖ κ) x) := by
    filter_upwards [hcompParts.1] with x hx
    letI : IsProbabilityMeasure ((η ∘ₖ κ) x) := inferInstance
    have hmem : MemLp f 2 ((η ∘ₖ κ) x) :=
      (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 (by simpa [q] using hx)
    exact memLp_one_iff_integrable.mp
      (hmem.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  filter_upwards [hfComp] with x hx
  simpa [kernelIntegral] using (Kernel.integral_comp (η := η) (κ := κ) hx).symm

/-- The `L²` actions compose according to Chapman–Kolmogorov kernel composition. The right-hand
kernel is applied first to functions, matching the kernel composition convention. -/
theorem kernelIntegralL2_comp {κ η : Kernel α α} [IsMarkovKernel κ]
    [IsMarkovKernel η] {m : Measure α} [SigmaFinite m]
    (hκ : Kernel.Invariant κ m) (hη : Kernel.Invariant η m) (f : Lp ℝ 2 m) :
    kernelIntegralL2 hκ (kernelIntegralL2 hη f) =
      kernelIntegralL2 (Kernel.Invariant.comp hη hκ) f := by
  apply Lp.ext
  have hfirst := kernelIntegralL2_coe hκ (kernelIntegralL2 hη f)
  have hrep := kernelIntegral_ae_congr hκ (kernelIntegralL2_coe hη f)
  have hcore := kernelIntegral_comp_ae hκ hη (Lp.stronglyMeasurable f) (Lp.memLp f)
  have hlast := kernelIntegralL2_coe (Kernel.Invariant.comp hη hκ) f
  exact hfirst.trans (hrep.trans (hcore.trans hlast.symm))

/-- A Chapman–Kolmogorov identity gives the corresponding semigroup law on `L²`. Invariance and
Markovness are explicit generic conditions on the kernels. -/
theorem kernelIntegralL2_semigroup_step {K : ℝ≥0 → Kernel α α} {s t : ℝ≥0}
    [IsMarkovKernel (K s)] [IsMarkovKernel (K t)] [IsMarkovKernel (K (s + t))]
    {m : Measure α} [SigmaFinite m] (hInv : ∀ u, Kernel.Invariant (K u) m)
    (hCK : K (s + t) = K t ∘ₖ K s) (f : Lp ℝ 2 m) :
    kernelIntegralL2 (hInv (s + t)) f =
      kernelIntegralL2 (hInv s) (kernelIntegralL2 (hInv t) f) := by
  simpa only [hCK] using (kernelIntegralL2_comp (hInv s) (hInv t) f).symm

end

end EinsteinRelation.WeightedKernelL2
