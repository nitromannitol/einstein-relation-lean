import EinsteinFull.Calculus.CLUnforcedClockL2

/-!
# Two-time reversibility of the unforced environment process

On smooth environments the reduced environment seen from the particle, `ω_t = τ_{Y_t} ω`, has
under the annealed unforced law a two-time joint law that is symmetric in the two times:
`E[f(ω_u) g(ω_v)] = E[g(ω_u) f(ω_v)]` for bounded measurable observables. The Markov property
and stationarity reduce both sides to the semigroup pairing, which is symmetric because the
unforced semigroup is its own transpose. This is the two-time form of the reversibility used
by the De Masi–Ferrari–Goldstein–Wick invariance principle.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- Mean of a reduced observable along the textbook reduced kernel at time `r`. -/
noncomputable def kernelObsMean (K : Kernel (FieldPair d × Vec d) (Path d))
    (g : FieldPair d → ℝ) (r : ℝ≥0) (ω : FieldPair d) : ℝ :=
  ∫ η, g (translate (η r) (reduce ω)) ∂K (ω, 0)

theorem measurable_kernelObsMean (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] {g : FieldPair d → ℝ} (hg : Measurable g) (r : ℝ≥0) :
    Measurable (kernelObsMean K g r) := by
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have hf : StronglyMeasurable (Function.uncurry fun (ω : FieldPair d) (η : Path d) =>
      g (translate (η r) (reduce ω))) :=
    (hg.comp (Probability.continuous_translate.comp
      ((continuous_snd.eval continuous_const).prodMk
        (Probability.continuous_reduce.comp continuous_fst))).measurable).stronglyMeasurable
  exact (StronglyMeasurable.integral_kernel_prod_right (κ := K0) hf).measurable

theorem abs_kernelObsMean_le (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K]
    {g : FieldPair d → ℝ} {B : ℝ} (hB : ∀ ρ, |g ρ| ≤ B) (r : ℝ≥0) (ω : FieldPair d) :
    |kernelObsMean K g r ω| ≤ B := by
  have h := norm_integral_le_of_norm_le_const (μ := K (ω, 0)) (C := B)
    (f := fun η => g (translate (η r) (reduce ω))) (ae_of_all _ fun η => by
      simpa only [Real.norm_eq_abs] using hB _)
  have h1 : (K (ω, 0)).real Set.univ = 1 := by simp [Measure.real]
  simpa only [kernelObsMean, Real.norm_eq_abs, h1, mul_one] using h

/-- Markov two-time identity for reduced observables along textbook reduced paths started at
the origin of a regular environment. -/
theorem integral_obs_mul_of_le (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
    (hK : ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))
    {f g : FieldPair d → ℝ} (hf : Measurable f) (hg : Measurable g) {B : ℝ}
    (hfB : ∀ ρ, |f ρ| ≤ B) (hgB : ∀ ρ, |g ρ| ≤ B)
    {ω : FieldPair d} (hω : IsRegular Λ ω) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ γ, f (translate (γ u) (reduce ω)) * g (translate (γ v) (reduce ω)) ∂K (ω, 0) =
      ∫ γ, f (translate (γ u) (reduce ω)) *
        kernelObsMean K g (v - u) (translate (γ u) ω) ∂K (ω, 0) := by
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨M, hM⟩ := reduced_bddCoef hΛ i 0 hω
  have htr : Continuous fun x : Vec d => translate x (reduce ω) :=
    Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)
  let G : Path d → ℝ := fun η => g (translate (η (v - u)) (reduce ω))
  have hG : Measurable G := hg.comp (htr.comp (continuous_eval_const (v - u))).measurable
  have hpos : Measurable[pathFiltration d u] (pathPosition (d := d) u) :=
    (Filtration.stronglyAdapted_natural
      (fun t => (measurable_pathPosition t).stronglyMeasurable) u).measurable
  have hH : StronglyMeasurable[pathFiltration d u]
      (fun γ : Path d => f (translate (γ u) (reduce ω))) :=
    ((hf.comp htr.measurable).comp hpos).stronglyMeasurable
  have hmk := integral_mul_restartPath hM (hK ω hω 0) (fun y => K (ω, y))
    (fun y P' hP' => reducedKernel_eq_of_solves hΛ i 0 hK (by omega) hω y hP') u hH
    (fun γ => hfB _) hG (fun η => hgB _)
  have hrestart (γ : Path d) :
      G (restartPath u γ) = g (translate (γ v) (reduce ω)) := by
    change g (translate (γ (u + (v - u))) (reduce ω)) = _
    rw [add_tsub_cancel_of_le huv]
  have hcond (y : Vec d) : (∫ η, G η ∂K (ω, y)) = kernelObsMean K g (v - u) (translate y ω) := by
    rw [reducedKernel_translate hΛ i 0 hK (by omega) hω y,
      integral_map (measurable_translatePath y).aemeasurable hG.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    change g (translate (y + η (v - u)) (reduce ω)) =
      g (translate (η (v - u)) (reduce (translate y ω)))
    rw [reduce_translate, translate_add, add_comm]
  simp only [hrestart] at hmk
  rw [hmk]
  simp_rw [hcond]

/-- Chapman–Kolmogorov for the reduced environment kernel on a regular environment:
`T_{s+t} g = T_s (T_t g)`. -/
theorem kernelObsMean_add (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
    (hK : ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))
    {g : FieldPair d → ℝ} (hg : Measurable g) {B : ℝ} (hgB : ∀ ρ, |g ρ| ≤ B)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (s t : ℝ≥0) :
    kernelObsMean K g (s + t) ω =
      ∫ η, kernelObsMean K g t (translate (η s) ω) ∂K (ω, 0) := by
  have h := integral_obs_mul_of_le hd hΛ hK (f := fun _ => 1) measurable_const hg
    (B := max B 1) (fun _ => by simp) (fun ρ => (hgB ρ).trans (le_max_left _ _)) hω
    (u := s) (v := s + t) le_self_add
  simp only [one_mul, add_tsub_cancel_left] at h
  exact h

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hK in
/-- Annealed two-time correlation of reduced observables. -/
theorem annealed_obs_mul_of_le {f g : FieldPair d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {B : ℝ} (hfB : ∀ ρ, |f ρ| ≤ B) (hgB : ∀ ρ, |g ρ| ≤ B)
    {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ z, f (translate (z.2 u) (reduce z.1)) * g (translate (z.2 v) (reduce z.1))
        ∂(Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d)))
          (measurable_id.prodMk measurable_const)) =
      ∫ ω, f (reduce ω) * kernelObsMean K g (v - u) ω ∂Q.measure := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  have hEt (t : ℝ≥0) : Continuous fun z : FieldPair d × Path d =>
      translate (z.2 t) (reduce z.1) :=
    Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
      (Probability.continuous_reduce.comp continuous_fst))
  have hEp (t : ℝ≥0) : Continuous fun z : FieldPair d × Path d => translate (z.2 t) z.1 :=
    Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
      continuous_fst)
  have hint (F : FieldPair d × Path d → ℝ) (hF : Measurable F) (C : ℝ)
      (hFb : ∀ z, |F z| ≤ C) : Integrable F (Q.measure ⊗ₘ K0) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFb z)
  have hbb (a b : ℝ) (ha : |a| ≤ B) (hb : |b| ≤ B) : |a * b| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  have hkm := measurable_kernelObsMean K hg (v - u)
  let F : FieldPair d → ℝ := fun ω => f (reduce ω) * kernelObsMean K g (v - u) ω
  have hF : Measurable F :=
    (hf.comp Probability.continuous_reduce.measurable).mul hkm
  have hmarg := (map_translate_reducedKernel hd D Q hQ hunforced hpath hK u).2
  calc
    _ = ∫ ω, ∫ γ, f (translate (γ u) (reduce ω)) * g (translate (γ v) (reduce ω))
          ∂K0 ω ∂Q.measure :=
      Measure.integral_compProd (hint (fun z => f (translate (z.2 u) (reduce z.1)) *
          g (translate (z.2 v) (reduce z.1)))
        ((hf.comp (hEt u).measurable).mul (hg.comp (hEt v).measurable)) (B * B) fun z =>
          hbb _ _ (hfB _) (hgB _))
    _ = ∫ ω, ∫ γ, F (translate (γ u) ω) ∂K0 ω ∂Q.measure := by
      refine integral_congr_ae (Q.regular.mono fun ω hω => ?_)
      exact integral_obs_mul_of_le hd hΛ hK hf hg hfB hgB hω huv
    _ = ∫ z, F (translate (z.2 u) z.1) ∂(Q.measure ⊗ₘ K0) :=
      (Measure.integral_compProd (hint (fun z => F (translate (z.2 u) z.1))
        (hF.comp (hEp u).measurable) (B * B) fun z =>
          hbb _ _ (hfB _) (abs_kernelObsMean_le K hgB _ _))).symm
    _ = ∫ ω, F ω ∂(Measure.map (fun z : FieldPair d × Path d => translate (z.2 u) z.1)
          (Q.measure ⊗ₘ K0)) :=
      (integral_map (hEp u).measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hmarg]


include hQ hunforced hpath hK in
/-- The annealed two-time correlation of reduced observables is the semigroup pairing. -/
theorem integral_obs_mul_kernelObsMean {f g : FieldPair d → ℝ} (hf : Measurable f)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hrealize : ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) = ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
    (fL gL : Lp ℂ 2 (reducedLaw Q)) (hfL : fL =ᵐ[reducedLaw Q] fun ρ => (f ρ : ℂ))
    (hgL : gL =ᵐ[reducedLaw Q] fun ρ => (g ρ : ℂ)) (r : ℝ≥0) :
    ∫ ω, f (reduce ω) * kernelObsMean K g r ω ∂Q.measure =
      (∫ ρ, fL ρ * P r gL ρ ∂reducedLaw Q).re := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  let Kq : QuenchedPathLaws d :=
    K.comap (fun p : Vec d × FieldPair d => (p.2, p.1)) measurable_swap
  have hKq : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Kq (0, ω)) := by
    filter_upwards [Q.regular, hQ] with ω hω hsm
    exact (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK ω hω 0)
  have hreal := hrealize Kq hKq r gL
  have hred := (map_translate_reducedKernel hd D Q hQ hunforced hpath hK r).1
  have hEr : Measurable fun z : FieldPair d × Path d => translate (z.2 r) (reduce z.1) :=
    (Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hrep : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K0 ω,
      gL (translate (γ r) (reduce ω)) = (g (translate (γ r) (reduce ω)) : ℂ) := by
    have h1 : ∀ᵐ z ∂(Q.measure ⊗ₘ K0), gL (translate (z.2 r) (reduce z.1)) =
        (g (translate (z.2 r) (reduce z.1)) : ℂ) := by
      have hg' : ∀ᵐ ρ ∂Measure.map (fun z : FieldPair d × Path d =>
          translate (z.2 r) (reduce z.1)) (Q.measure ⊗ₘ K0), gL ρ = (g ρ : ℂ) := by
        rw [hred]
        exact hgL
      exact ae_of_ae_map hEr.aemeasurable hg'
    exact Measure.ae_ae_of_ae_compProd h1
  have hkm : ∀ᵐ ω ∂Q.measure, kernelObsMean K g r ω = (P r gL (reduce ω)).re := by
    filter_upwards [hreal, hrep] with ω hω hrω
    have hrω' : ∀ᵐ γ ∂Kq (0, ω),
        gL (translate (γ r) (reduce ω)) = (g (translate (γ r) (reduce ω)) : ℂ) := hrω
    rw [hω.2]
    have hre := integral_re (𝕜 := ℂ) hω.1
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_congr_ae ?_
    filter_upwards [hrω'] with γ hγ
    rw [hγ, Complex.ofReal_re]
  have hPg : Measurable fun ρ : FieldPair d => (P r gL ρ).re :=
    Complex.measurable_re.comp (Lp.stronglyMeasurable (P r gL)).measurable
  have hprod : Integrable (fun ρ => fL ρ * P r gL ρ) (reducedLaw Q) :=
    (Lp.memLp fL).integrable_mul (Lp.memLp (P r gL))
  calc
    _ = ∫ ω, f (reduce ω) * (P r gL (reduce ω)).re ∂Q.measure :=
      integral_congr_ae (hkm.mono fun ω h => by rw [h])
    _ = ∫ ρ, f ρ * (P r gL ρ).re ∂reducedLaw Q :=
      (integral_map Probability.measurable_reduce.aemeasurable
        (hf.mul hPg).aestronglyMeasurable).symm
    _ = ∫ ρ, (fL ρ * P r gL ρ).re ∂reducedLaw Q :=
      integral_congr_ae (hfL.mono fun ρ h => by dsimp only; rw [h, Complex.re_ofReal_mul])
    _ = _ := by
      have hre := integral_re (𝕜 := ℂ) hprod
      simpa only [RCLike.re_to_complex] using hre

include hQ hunforced hpath hK in
/-- Detailed balance of the reduced environment kernel: for bounded measurable observables,
`∫ f · T_s g = ∫ g · T_s f` under the environment law, with `T_s` the kernel mean at time `s`. -/
theorem kernel_detailed_balance {f g : FieldPair d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {B : ℝ} (hfB : ∀ ρ, |f ρ| ≤ B) (hgB : ∀ ρ, |g ρ| ≤ B) (s : ℝ≥0) :
    ∫ ω, f (reduce ω) * kernelObsMean K g s ω ∂Q.measure =
      ∫ ω, g (reduce ω) * kernelObsMean K f s ω ∂Q.measure := by
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨P, _, hT, _, _, _, hrealize⟩ := id hunforced
  have hmem (h : FieldPair d → ℝ) (hc : Measurable h) (hb : ∀ ρ, |h ρ| ≤ B) :
      MemLp (fun ρ => (h ρ : ℂ)) 2 (reducedLaw Q) :=
    MemLp.of_bound (Complex.measurable_ofReal.comp hc).aestronglyMeasurable B
      (ae_of_all _ fun ρ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb ρ)
  let fL := (hmem f hf hfB).toLp _
  let gL := (hmem g hg hgB).toLp _
  rw [integral_obs_mul_kernelObsMean hd D Q hQ hunforced hpath hK hf P hrealize fL gL
      (hmem f hf hfB).coeFn_toLp (hmem g hg hgB).coeFn_toLp,
    integral_obs_mul_kernelObsMean hd D Q hQ hunforced hpath hK hg P hrealize gL fL
      (hmem g hg hgB).coeFn_toLp (hmem f hf hfB).coeFn_toLp]
  have h := hT s fL gL
  congr 1
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ρ => mul_comm _ _)

include hQ hunforced hpath hK in
/-- Two-time reversibility of the unforced environment process under the annealed law. -/
theorem annealed_obs_mul_comm {f g : FieldPair d → ℝ} (hf : Measurable f)
    (hg : Measurable g) {B : ℝ} (hfB : ∀ ρ, |f ρ| ≤ B) (hgB : ∀ ρ, |g ρ| ≤ B)
    {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ z, f (translate (z.2 u) (reduce z.1)) * g (translate (z.2 v) (reduce z.1))
        ∂(Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d)))
          (measurable_id.prodMk measurable_const)) =
      ∫ z, g (translate (z.2 u) (reduce z.1)) * f (translate (z.2 v) (reduce z.1))
        ∂(Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d)))
          (measurable_id.prodMk measurable_const)) := by
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨P, _, hT, _, _, _, hrealize⟩ := id hunforced
  have hmem (h : FieldPair d → ℝ) (hc : Measurable h) (hb : ∀ ρ, |h ρ| ≤ B) :
      MemLp (fun ρ => (h ρ : ℂ)) 2 (reducedLaw Q) :=
    MemLp.of_bound (Complex.measurable_ofReal.comp hc).aestronglyMeasurable B
      (ae_of_all _ fun ρ => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hb ρ)
  let fL := (hmem f hf hfB).toLp _
  let gL := (hmem g hg hgB).toLp _
  rw [annealed_obs_mul_of_le hd D Q hQ hunforced hpath hK hf hg hfB hgB huv,
    annealed_obs_mul_of_le hd D Q hQ hunforced hpath hK hg hf hgB hfB huv,
    integral_obs_mul_kernelObsMean hd D Q hQ hunforced hpath hK hf P hrealize fL gL
      (hmem f hf hfB).coeFn_toLp (hmem g hg hgB).coeFn_toLp,
    integral_obs_mul_kernelObsMean hd D Q hQ hunforced hpath hK hg P hrealize gL fL
      (hmem g hg hgB).coeFn_toLp (hmem f hf hfB).coeFn_toLp]
  have h := hT (v - u) fL gL
  congr 1
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ρ => mul_comm _ _)

end Annealed

end EinsteinFull.Blueprint
