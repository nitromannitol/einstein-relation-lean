import EinsteinFull.Calculus.CLUnforcedReversibility

/-!
# The unforced environment kernel on physical observables

Every bounded measurable observable of the physical environment is an observable of its
reduction, because the reduction is a measurable embedding. The kernel mean of the physical
environment seen from the particle therefore inherits detailed balance and Chapman–Kolmogorov
from the reduced statements.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- A bounded measurable observable of the physical environment is a bounded measurable
observable of its reduction. -/
theorem exists_reduced_observable {g : FieldPair d → ℝ} (hg : Measurable g) {B : ℝ}
    (hB : ∀ ω, |g ω| ≤ B) :
    ∃ g' : FieldPair d → ℝ, Measurable g' ∧ (∀ ρ, |g' ρ| ≤ B) ∧
      ∀ ω, g' (reduce ω) = g ω := by
  classical
  let ω₀ : FieldPair d := (ContinuousMap.const _ 0, ContinuousMap.const _ 0)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB ω₀)
  refine ⟨Function.extend reduce g (fun _ => 0),
    measurableEmbedding_reduce.measurable_extend hg measurable_const, fun ρ => ?_,
    fun ω => reduce_injective.extend_apply _ _ _⟩
  by_cases hρ : ∃ ω, reduce ω = ρ
  · obtain ⟨ω, rfl⟩ := hρ
    rw [reduce_injective.extend_apply]
    exact hB ω
  · rw [Function.extend_apply' _ _ _ hρ, abs_zero]
    exact hB0

/-- Mean of a physical observable along the textbook reduced kernel at time `r`. -/
noncomputable def kernelPhysMean (K : Kernel (FieldPair d × Vec d) (Path d))
    (g : FieldPair d → ℝ) (r : ℝ≥0) (ω : FieldPair d) : ℝ :=
  ∫ η, g (translate (η r) ω) ∂K (ω, 0)

theorem kernelPhysMean_eq (K : Kernel (FieldPair d × Vec d) (Path d))
    {g g' : FieldPair d → ℝ} (hg' : ∀ ω, g' (reduce ω) = g ω) (r : ℝ≥0) (ω : FieldPair d) :
    kernelPhysMean K g r ω = kernelObsMean K g' r ω := by
  unfold kernelPhysMean kernelObsMean
  refine integral_congr_ae (ae_of_all _ fun η => ?_)
  dsimp only
  rw [← hg', reduce_translate]

theorem measurable_kernelPhysMean (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] {g : FieldPair d → ℝ} (hg : Measurable g) (r : ℝ≥0) :
    Measurable (kernelPhysMean K g r) := by
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have hf : StronglyMeasurable (Function.uncurry fun (ω : FieldPair d) (η : Path d) =>
      g (translate (η r) ω)) :=
    (hg.comp (Probability.continuous_translate.comp
      ((continuous_snd.eval continuous_const).prodMk continuous_fst)).measurable).stronglyMeasurable
  exact (StronglyMeasurable.integral_kernel_prod_right (κ := K0) hf).measurable

theorem abs_kernelPhysMean_le (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K]
    {g : FieldPair d → ℝ} {B : ℝ} (hB : ∀ ω, |g ω| ≤ B) (r : ℝ≥0) (ω : FieldPair d) :
    |kernelPhysMean K g r ω| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := K (ω, 0)) (C := B)
    (f := fun η => g (translate (η r) ω)) (ae_of_all _ fun η => by
      simpa only [Real.norm_eq_abs] using hB _)
  have h1 : (K (ω, 0)).real Set.univ = 1 := by simp [Measure.real]
  simpa only [kernelPhysMean, Real.norm_eq_abs, h1, mul_one] using h

/-- Iterated kernel means along a list of time gaps and physical observables:
`chainMean ((s, f) :: L) = T_s (f · chainMean L)`. -/
noncomputable def chainMean (K : Kernel (FieldPair d × Vec d) (Path d)) :
    List (ℝ≥0 × (FieldPair d → ℝ)) → FieldPair d → ℝ
  | [] => fun _ => 1
  | (s, f) :: L => kernelPhysMean K (fun ω => f ω * chainMean K L ω) s

/-- The product of the observables of a list, at the cumulative times after `t₀`, along a path
from the environment `ω`. -/
noncomputable def chainProd : List (ℝ≥0 × (FieldPair d → ℝ)) → ℝ≥0 → Path d →
    FieldPair d → ℝ
  | [], _, _, _ => 1
  | (s, f) :: L, t₀, γ, ω => f (translate (γ (t₀ + s)) ω) * chainProd L (t₀ + s) γ ω

/-- Observables bounded by one and measurable. -/
def IsUnitObservables (L : List (ℝ≥0 × (FieldPair d → ℝ))) : Prop :=
  ∀ p ∈ L, Measurable p.2 ∧ ∀ ω, |p.2 ω| ≤ 1

theorem chainMean_measurable_bound (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] :
    ∀ L : List (ℝ≥0 × (FieldPair d → ℝ)), IsUnitObservables L →
      Measurable (chainMean K L) ∧ ∀ ω, |chainMean K L ω| ≤ 1
  | [], _ => ⟨measurable_const, fun _ => by simp [chainMean]⟩
  | (s, f) :: L, h => by
    obtain ⟨hm, hb⟩ := chainMean_measurable_bound K L fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    refine ⟨measurable_kernelPhysMean K (hfm.mul hm) s, fun ω => ?_⟩
    refine abs_kernelPhysMean_le K (fun ω => ?_) s ω
    rw [abs_mul]
    exact (mul_le_mul (hfb ω) (hb ω) (abs_nonneg _) zero_le_one).trans (by norm_num)

theorem chainProd_restart :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))) (s t₀ : ℝ≥0) (γ : Path d) (ω : FieldPair d),
      chainProd L (s + t₀) γ ω = chainProd L t₀ (restartPath s γ) ω
  | [], _, _, _, _ => rfl
  | (r, f) :: L, s, t₀, γ, ω => by
    simp only [chainProd, restartPath_apply, add_assoc]
    rw [chainProd_restart L s (t₀ + r) γ ω]

theorem chainProd_translate :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))) (t₀ : ℝ≥0) (y : Vec d) (η : Path d)
      (ω : FieldPair d),
      chainProd L t₀ (translatePath y η) ω = chainProd L t₀ η (translate y ω)
  | [], _, _, _, _ => rfl
  | (r, f) :: L, t₀, y, η, ω => by
    simp only [chainProd, translatePath_apply]
    rw [chainProd_translate L (t₀ + r) y η ω, translate_add, add_comm (η (t₀ + r)) y]

theorem chainProd_measurable_bound :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))), IsUnitObservables L → ∀ (t₀ : ℝ≥0)
      (ω : FieldPair d),
      Measurable (fun γ : Path d => chainProd L t₀ γ ω) ∧ ∀ γ, |chainProd L t₀ γ ω| ≤ 1
  | [], _, _, _ => ⟨measurable_const, fun _ => by simp [chainProd]⟩
  | (s, f) :: L, h, t₀, ω => by
    obtain ⟨hm, hb⟩ := chainProd_measurable_bound L
      (fun p hp => h p (List.mem_cons_of_mem _ hp)) (t₀ + s) ω
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    have htr : Continuous fun γ : Path d => translate (γ (t₀ + s)) ω :=
      Probability.continuous_translate.comp ((continuous_eval_const _).prodMk continuous_const)
    refine ⟨(hfm.comp htr.measurable).mul hm, fun γ => ?_⟩
    simp only [chainProd]
    rw [abs_mul]
    exact (mul_le_mul (hfb _) (hb γ) (abs_nonneg _) zero_le_one).trans (by norm_num)

/-- Multi-time Markov formula on a regular environment: the expectation of a product of physical
observables at increasing times is the iterated kernel mean. -/
theorem integral_chainProd (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
    (hK : ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x))) :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))), IsUnitObservables L →
      ∀ (ω : FieldPair d), IsRegular Λ ω →
        ∫ γ, chainProd L 0 γ ω ∂K (ω, 0) = chainMean K L ω
  | [], _, ω, _ => by simp [chainProd, chainMean]
  | (s, f) :: L, h, ω, hω => by
    let i : Fin d := ⟨0, by omega⟩
    obtain ⟨M, hM⟩ := reduced_bddCoef hΛ i 0 hω
    have hL : IsUnitObservables L := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    let G : Path d → ℝ := fun η => f (translate (η 0) ω) * chainProd L 0 η ω
    have hG : Measurable G :=
      (hfm.comp (Probability.continuous_translate.comp
        ((continuous_eval_const 0).prodMk continuous_const)).measurable).mul
        (chainProd_measurable_bound L hL 0 ω).1
    have hGb (η : Path d) : |G η| ≤ 1 := by
      simp only [G]
      rw [abs_mul]
      exact (mul_le_mul (hfb _) ((chainProd_measurable_bound L hL 0 ω).2 η) (abs_nonneg _)
        zero_le_one).trans (by norm_num)
    have hrestart (γ : Path d) : G (restartPath s γ) = chainProd ((s, f) :: L) 0 γ ω := by
      simp only [G, chainProd, restartPath_apply, add_zero, zero_add]
      rw [← chainProd_restart L s 0 γ ω, add_zero]
    have hmk := integral_mul_restartPath hM (hK ω hω 0) (fun y => K (ω, y))
      (fun y P' hP' => reducedKernel_eq_of_solves hΛ i 0 hK (by omega) hω y hP') s
      (H := fun _ => 1) stronglyMeasurable_const (CH := 1) (fun _ => by simp) hG hGb
    simp only [one_mul, hrestart] at hmk
    rw [hmk]
    simp only [chainMean, kernelPhysMean]
    refine integral_congr_ae (ae_of_all _ fun γ => ?_)
    have hω' : IsRegular Λ (translate (γ s) ω) :=
      (ActualImageLpStateTransport.isRegular_translate_iff _ ω).mpr hω
    show (∫ η, G η ∂K (ω, γ s)) =
      f (translate (γ s) ω) * chainMean K L (translate (γ s) ω)
    rw [reducedKernel_translate hΛ i 0 hK (by omega) hω (γ s),
      integral_map (measurable_translatePath _).aemeasurable hG.aestronglyMeasurable,
      ← integral_chainProd hd hΛ hK L hL _ hω', ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [(hK _ hω' 0).2.1] with η hη
    simp only [G, translatePath_apply, hη, add_zero]
    rw [chainProd_translate]

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hK in
/-- Detailed balance of the environment kernel for bounded measurable physical observables. -/
theorem kernelPhys_detailed_balance {f g : FieldPair d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {B : ℝ} (hfB : ∀ ω, |f ω| ≤ B) (hgB : ∀ ω, |g ω| ≤ B) (s : ℝ≥0) :
    ∫ ω, f ω * kernelPhysMean K g s ω ∂Q.measure =
      ∫ ω, g ω * kernelPhysMean K f s ω ∂Q.measure := by
  obtain ⟨f', hf', hf'B, hff'⟩ := exists_reduced_observable hf hfB
  obtain ⟨g', hg', hg'B, hgg'⟩ := exists_reduced_observable hg hgB
  have h := kernel_detailed_balance hd D Q hQ hunforced hpath hK hf' hg' hf'B hg'B s
  simp only [hff', hgg'] at h
  simp only [kernelPhysMean_eq K hgg', kernelPhysMean_eq K hff']
  exact h


/-- The left-accumulated (time-reversed) nesting: `leftAcc a ((s, f) :: L) = leftAcc (f · T_s a) L`. -/
noncomputable def leftAcc (K : Kernel (FieldPair d × Vec d) (Path d)) :
    (FieldPair d → ℝ) → List (ℝ≥0 × (FieldPair d → ℝ)) → FieldPair d → ℝ
  | a, [] => a
  | a, (s, f) :: L => leftAcc K (fun ω => f ω * kernelPhysMean K a s ω) L

include hQ hunforced hpath hK in
/-- Finite-dimensional reversibility of the environment process: under the environment law the
right-nested multi-time kernel mean equals the left-nested one, the same expectation with time
reversed. -/
theorem integral_mul_chainMean_eq_leftAcc :
    ∀ (L : List (ℝ≥0 × (FieldPair d → ℝ))), IsUnitObservables L →
      ∀ (a : FieldPair d → ℝ), Measurable a → (∀ ω, |a ω| ≤ 1) →
        ∫ ω, a ω * chainMean K L ω ∂Q.measure = ∫ ω, leftAcc K a L ω ∂Q.measure
  | [], _, a, _, _ => by simp [chainMean, leftAcc]
  | (s, f) :: L, h, a, ham, hab => by
    have hL : IsUnitObservables L := fun p hp => h p (List.mem_cons_of_mem _ hp)
    obtain ⟨hfm, hfb⟩ := h (s, f) (List.mem_cons_self ..)
    obtain ⟨hcm, hcb⟩ := chainMean_measurable_bound K L hL
    have hprod_b (u v : ℝ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |u * v| ≤ 1 := by
      rw [abs_mul]
      exact (mul_le_mul hu hv (abs_nonneg _) zero_le_one).trans (by norm_num)
    have hdb := kernelPhys_detailed_balance hd D Q hQ hunforced hpath hK
      (g := fun ω => f ω * chainMean K L ω) ham
      (hfm.mul hcm) hab (fun ω => hprod_b _ _ (hfb ω) (hcb ω)) s
    have hTa_m := measurable_kernelPhysMean K ham s
    have hTa_b := abs_kernelPhysMean_le K hab s
    have hnext := integral_mul_chainMean_eq_leftAcc L hL
      (fun ω => f ω * kernelPhysMean K a s ω) (hfm.mul hTa_m)
      (fun ω => hprod_b _ _ (hfb ω) (hTa_b ω))
    simp only [chainMean, leftAcc]
    rw [hdb, ← hnext]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    ring


include hQ hunforced hpath hK in
/-- Ergodicity of the environment kernel in the state-space form of DFGW (p.790): a measurable
set of environments that the kernel preserves almost surely at every time is null or conull. -/
theorem kernelPhys_ergodic {A : Set (FieldPair d)} (hA : MeasurableSet A)
    (hinv : ∀ t : ℝ≥0, ∀ᵐ ω ∂Q.measure,
      kernelPhysMean K (A.indicator fun _ => 1) t ω = A.indicator (fun _ => 1) ω) :
    Q.measure A = 0 ∨ Q.measure A = 1 := by
  classical
  have : IsProbabilityMeasure Q.measure := Q.probability
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨P, _, _, _, hfixed, _, hrealize⟩ := id hunforced
  let g : FieldPair d → ℝ := A.indicator fun _ => 1
  have hgm : Measurable g := measurable_const.indicator hA
  have hgb : ∀ ω, |g ω| ≤ 1 := fun ω => by
    by_cases h : ω ∈ A <;> simp [g, h]
  obtain ⟨g', hg'm, hg'b, hgg'⟩ := exists_reduced_observable hgm hgb
  have hmem : MemLp (fun ρ => (g' ρ : ℂ)) 2 (reducedLaw Q) :=
    MemLp.of_bound (Complex.measurable_ofReal.comp hg'm).aestronglyMeasurable 1
      (ae_of_all _ fun ρ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hg'b ρ)
  let G := hmem.toLp _
  have hG : G =ᵐ[reducedLaw Q] fun ρ => (g' ρ : ℂ) := hmem.coeFn_toLp
  -- the semigroup fixes G
  have hfixG : ∀ t, P t G = G := by
    intro t
    have hK0 : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0
        ((K.comap (fun p : Vec d × FieldPair d => (p.2, p.1)) measurable_swap) (0, ω)) := by
      filter_upwards [Q.regular, hQ] with ω hω hsm
      exact (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK ω hω 0)
    have hreal := hrealize _ hK0 t G
    have hred := (map_translate_reducedKernel hd D Q hQ hunforced hpath hK t).1
    have hEr : Measurable fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1) :=
      (Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
        (Probability.continuous_reduce.comp continuous_fst))).measurable
    have hrep : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(K.comap (fun ω => (ω, (0 : Vec d)))
        (measurable_id.prodMk measurable_const)) ω,
        G (translate (γ t) (reduce ω)) = (g' (translate (γ t) (reduce ω)) : ℂ) := by
      have hG' : ∀ᵐ ρ ∂Measure.map (fun z : FieldPair d × Path d =>
          translate (z.2 t) (reduce z.1)) (Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d)))
            (measurable_id.prodMk measurable_const)), G ρ = (g' ρ : ℂ) := by
        rw [hred]
        exact hG
      exact Measure.ae_ae_of_ae_compProd (ae_of_ae_map hEr.aemeasurable hG')
    -- pointwise on environments, the semigroup representative equals the indicator
    have hpt : ∀ᵐ ω ∂Q.measure, P t G (reduce ω) = G (reduce ω) := by
      filter_upwards [hreal, hrep, hinv t, ae_of_ae_map Probability.measurable_reduce.aemeasurable hG]
        with ω hω hrω hinvω hGω
      rw [hω.2, hGω]
      have e : (∫ γ, G (translate (γ t) (reduce ω))
          ∂(K.comap (fun p : Vec d × FieldPair d => (p.2, p.1)) measurable_swap) (0, ω)) =
          ((kernelPhysMean K g t ω : ℝ) : ℂ) := by
        rw [kernelPhysMean_eq K hgg', kernelObsMean, ← integral_complex_ofReal]
        exact integral_congr_ae hrω
      rw [e, hinvω]
      exact congrArg _ (hgg' ω).symm
    -- equality in L² of the reduced law
    apply Lp.ext
    refine (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_eq_fun (Lp.stronglyMeasurable (P t G)).measurable
        (Lp.stronglyMeasurable G).measurable)).mpr ?_
    exact hpt
  obtain ⟨c, hc⟩ := (hfixed G).1 hfixG
  -- the indicator is a.e. constant under the environment law
  have hconst : ∀ᵐ ω ∂Q.measure, (g ω : ℂ) = c := by
    have h := ae_of_ae_map (μ := Q.measure) Probability.measurable_reduce.aemeasurable
      (hG.symm.trans hc)
    filter_upwards [h] with ω hω
    rw [← hgg']
    exact hω
  -- hence the set is null or conull
  by_cases hc1 : c = 1
  · right
    have hsub : ∀ᵐ ω ∂Q.measure, ω ∈ A := by
      filter_upwards [hconst] with ω hω
      by_contra hn
      simp [g, hn, hc1] at hω
    rw [← prob_compl_eq_zero_iff hA]
    exact mem_ae_iff.1 hsub
  · left
    have hsub : ∀ᵐ ω ∂Q.measure, ω ∉ A := by
      filter_upwards [hconst] with ω hω
      intro hm
      simp only [g, Set.indicator_of_mem hm, Complex.ofReal_one] at hω
      exact hc1 hω.symm
    exact measure_eq_zero_iff_ae_notMem.2 hsub

end Annealed

end EinsteinFull.Blueprint
