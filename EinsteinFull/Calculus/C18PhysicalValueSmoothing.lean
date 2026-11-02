import EinsteinFull.Calculus.C18PhysicalEvolutionSmoothing
import Mathlib.Analysis.Distribution.TemperedDistribution

open MeasureTheory Filter LineDeriv
open scoped SchwartzMap Topology

namespace EinsteinFull
open EinsteinRelation

/-- An L² limit of Schwartz functions retains the distributional derivative
when their directional derivatives converge in L² to the same limit. -/
theorem c18_tempered_derivative_of_schwartz_L2_approximation {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) (m : Vec d)
    (a : ℕ → 𝓢(Vec d, ℂ))
    (hu : Tendsto (fun n => (a n).toLp 2 volume) atTop (𝓝 u))
    (hv : Tendsto (fun n => (∂_{m} (a n)).toLp 2 volume) atTop (𝓝 v)) :
    ∂_{m} (u : 𝓢'(Vec d, ℂ)) = (v : 𝓢'(Vec d, ℂ)) := by
  let T := Lp.toTemperedDistributionCLM ℂ (volume : Measure (Vec d)) 2
  have hu' : Tendsto (fun n => ∂_{m} (T ((a n).toLp 2 volume))) atTop
      (𝓝 (∂_{m} (T u))) :=
    (continuous_lineDerivOp m).continuousAt.tendsto.comp (T.continuous.continuousAt.tendsto.comp hu)
  have hv' : Tendsto (fun n => T ((∂_{m} (a n)).toLp 2 volume)) atTop (𝓝 (T v)) :=
    T.continuous.continuousAt.tendsto.comp hv
  change ∂_{m} (T u) = T v
  apply tendsto_nhds_unique hu'
  convert hv' using 1
  funext n
  simpa only [T, Lp.toTemperedDistributionCLM_apply, Lp.toTemperedDistribution_toLp_eq] using
    (TemperedDistribution.lineDerivOp_toTemperedDistributionCLM_eq
      (μ := (volume : Measure (Vec d))) (a n) m)

/-- Whole-space Sobolev functions admit Schwartz approximants converging in
L² together with each supplied weak gradient coordinate. -/
private theorem c18_real_H1_schwartz_approximation {d : ℕ}
    (u : PDE.W1pFunction (Set.univ : Set (Vec d)) 2) :
    ∃ a : ℕ → 𝓢(Vec d, ℝ),
      Tendsto (fun n => (a n).toLp 2 volume) atTop
        (𝓝 ((by simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ]
          using u.memLp : MemLp u.toFun 2 volume).toLp u.toFun)) ∧
      ∀ i : Fin d,
        Tendsto (fun n => (∂_{unitVector i} (a n)).toLp 2 volume) atTop
          (𝓝 ((by simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ]
            using u.gradMemLp i : MemLp (fun x => u.grad x i) 2 volume).toLp
              (fun x => u.grad x i))) := by
  obtain ⟨b⟩ := u.hasSupportedSmoothApproximation_univ (by norm_num) (by norm_num)
  let a : ℕ → 𝓢(Vec d, ℝ) := fun n =>
    (b.approx_hasCompactSupport n).toSchwartzMap (b.approx_smooth n)
  refine ⟨a, ?_, ?_⟩
  · apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ _).2
    convert b.tendsto_value using 1
    funext n
    simp only [PDE.volumeOn, Measure.restrict_univ]
    apply eLpNorm_congr_ae
    filter_upwards [(a n).coeFn_toLp 2 volume] with x hx
    change ((a n).toLp 2 volume) x = b.approx n x at hx
    simpa only [PDE.volumeOn, Measure.restrict_univ, Pi.sub_apply] using
      congrArg (fun y : ℝ => y - u.toFun x) hx
  · intro i
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm _ _ _).2
    convert b.tendsto_grad i using 1
    funext n
    simp only [PDE.volumeOn, Measure.restrict_univ]
    apply eLpNorm_congr_ae
    filter_upwards [(∂_{unitVector i} (a n)).coeFn_toLp 2 volume] with x hx
    change ((∂_{unitVector i} (a n)).toLp 2 volume) x =
      fderiv ℝ (b.approx n) x (unitVector i) at hx
    simpa only [PDE.volumeOn, Measure.restrict_univ, Pi.sub_apply,
      PDE.basisVec, unitVector] using
      congrArg (fun y : ℝ => y - u.grad x i) hx

/-- Postcomposition commutes with the L² realization of a Schwartz function. -/
private theorem c18_schwartz_postcomp_toLp {d : ℕ}
    (L : ℝ →L[ℝ] ℂ) (a : 𝓢(Vec d, ℝ)) :
    (a.postcompCLM L).toLp 2 volume = L.compLpL 2 volume (a.toLp 2 volume) := by
  apply Lp.ext
  filter_upwards [(a.postcompCLM L).coeFn_toLp 2 volume,
    L.coeFn_compLpL (a.toLp 2 volume), a.coeFn_toLp 2 volume] with x hx hy hz
  simpa only [SchwartzMap.postcompCLM_apply, hx, hy, hz]

/-- A real-linear map commutes with a Schwartz directional derivative. -/
private theorem c18_schwartz_postcomp_lineDeriv {d : ℕ}
    (L : ℝ →L[ℝ] ℂ) (a : 𝓢(Vec d, ℝ)) (m : Vec d) :
    ∂_{m} (a.postcompCLM L) = (∂_{m} a).postcompCLM L := by
  ext x
  change fderiv ℝ (L ∘ a) x m = L (fderiv ℝ a x m)
  rw [fderiv_comp x L.differentiableAt a.differentiableAt, L.fderiv]
  rfl

private theorem c18_schwartz_toLp_add {d : ℕ} (a b : 𝓢(Vec d, ℂ)) :
    (a + b).toLp 2 volume = a.toLp 2 volume + b.toLp 2 volume := by
  exact (SchwartzMap.toLpCLM ℝ ℂ 2 volume).map_add a b

/-- The weak real-coordinate formulation gives a whole-space Sobolev function. -/
private def c18_real_weak_H1 {d : ℕ} (f : Vec d → ℝ) (G : Fin d → Vec d → ℝ)
    (hf : MemLp f 2 volume) (hG : ∀ j, MemLp (G j) 2 volume)
    (hw : ∀ j, HasWeakPartialDerivative Set.univ j f (G j)) :
    PDE.W1pFunction (Set.univ : Set (Vec d)) 2 where
  toFun := f
  grad := fun x j => G j x
  memLp := by simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hf
  gradMemLp := by
    intro j
    simpa only [PDE.MemLpOn, PDE.volumeOn, Measure.restrict_univ] using hG j
  hasWeakGradient := by
    intro j φ hφ hc hs
    simpa only [PDE.basisVec, unitVector, coordinateDerivative] using
      (hw j).2.2 φ ⟨hφ, hc, hs⟩

/-- The supplied physical H¹ graph is the distributional derivative graph. -/
theorem c18_tempered_derivative_of_physical_H1Graph {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (l : Fin d) :
    ∂_{unitVector l} (f : 𝓢'(Vec d, ℂ)) = (G l : 𝓢'(Vec d, ℂ)) := by
  have hfre : MemLp (fun x => (f x).re) 2 volume := by
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp f)
  have hfim : MemLp (fun x => (f x).im) 2 volume := by
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp f)
  have hGre : ∀ j, MemLp (fun x => (G j x).re) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.reCLM_apply] using
      Complex.reCLM.comp_memLp' (Lp.memLp (G j))
  have hGim : ∀ j, MemLp (fun x => (G j x).im) 2 volume := by
    intro j
    simpa only [Function.comp_def, Complex.imCLM_apply] using
      Complex.imCLM.comp_memLp' (Lp.memLp (G j))
  let ur := c18_real_weak_H1 _ _ hfre hGre hG.1
  let ui := c18_real_weak_H1 _ _ hfim hGim hG.2
  obtain ⟨ar, har, hDar⟩ := c18_real_H1_schwartz_approximation ur
  obtain ⟨ai, hai, hDai⟩ := c18_real_H1_schwartz_approximation ui
  let Lr : ℝ →L[ℝ] ℂ := Complex.ofRealCLM
  let Li : ℝ →L[ℝ] ℂ := Complex.I • Complex.ofRealCLM
  let a : ℕ → 𝓢(Vec d, ℂ) := fun n => (ar n).postcompCLM Lr + (ai n).postcompCLM Li
  let fr := hfre.toLp _
  let fi := hfim.toLp _
  let gr := (hGre l).toLp _
  let gi := (hGim l).toLp _
  have hf : Lr.compLpL 2 volume fr + Li.compLpL 2 volume fi = f := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (Lr.compLpL 2 volume fr) (Li.compLpL 2 volume fi),
      Lr.coeFn_compLpL fr, Li.coeFn_compLpL fi, hfre.coeFn_toLp, hfim.coeFn_toLp] with x h1 h2 h3 h4 h5
    simpa only [h1, Pi.add_apply, h2, h3, fr, fi, h4, h5, Lr, Li,
      smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
      mul_comm Complex.I] using Complex.re_add_im (f x)
  have hg : Lr.compLpL 2 volume gr + Li.compLpL 2 volume gi = G l := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_add (Lr.compLpL 2 volume gr) (Li.compLpL 2 volume gi),
      Lr.coeFn_compLpL gr, Li.coeFn_compLpL gi, (hGre l).coeFn_toLp,
      (hGim l).coeFn_toLp] with x h1 h2 h3 h4 h5
    simpa only [h1, Pi.add_apply, h2, h3, gr, gi, h4, h5, Lr, Li,
      smul_apply, Complex.ofRealCLM_apply, smul_eq_mul,
      mul_comm Complex.I] using Complex.re_add_im (G l x)
  have hu : Tendsto (fun n => (a n).toLp 2 volume) atTop (𝓝 f) := by
    rw [← hf]
    have hr := (Lr.compLpL 2 volume).continuous.continuousAt.tendsto.comp har
    have hi := (Li.compLpL 2 volume).continuous.continuousAt.tendsto.comp hai
    simpa only [a, c18_schwartz_toLp_add, c18_schwartz_postcomp_toLp,
      ur, ui, c18_real_weak_H1, fr, fi, Function.comp_def] using hr.add hi
  have hv : Tendsto (fun n => (∂_{unitVector l} (a n)).toLp 2 volume) atTop (𝓝 (G l)) := by
    rw [← hg]
    have hr := (Lr.compLpL 2 volume).continuous.continuousAt.tendsto.comp (hDar l)
    have hi := (Li.compLpL 2 volume).continuous.continuousAt.tendsto.comp (hDai l)
    simpa only [a, lineDerivOp_add, c18_schwartz_toLp_add,
      c18_schwartz_postcomp_lineDeriv, c18_schwartz_postcomp_toLp,
      ur, ui, c18_real_weak_H1, gr, gi, Function.comp_def] using hr.add hi
  exact c18_tempered_derivative_of_schwartz_L2_approximation f (G l) _ a hu hv

/-- Distributional equality tested on a real compactly supported smooth function. -/
private theorem c18_tempered_test_identity {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) (i : Fin d)
    (h : ∂_{unitVector i} (f : 𝓢'(Vec d, ℂ)) = (g : 𝓢'(Vec d, ℂ)))
    (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
    (∫ x, (coordinateDerivative i φ x : ℂ) * f x) =
      -(∫ x, (φ x : ℂ) * g x) := by
  let a : 𝓢(Vec d, ℝ) := hφ.2.1.toSchwartzMap hφ.1
  let b : 𝓢(Vec d, ℂ) := a.postcompCLM Complex.ofRealCLM
  have he := congrArg (fun T : 𝓢'(Vec d, ℂ) => T b) h
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at he
  have hb : ∀ x, b x = (φ x : ℂ) := by
    intro x
    rfl
  have hd : ∀ x, (∂_{unitVector i} b) x = (coordinateDerivative i φ x : ℂ) := by
    intro x
    rw [c18_schwartz_postcomp_lineDeriv]
    change (fderiv ℝ φ x (unitVector i) : ℂ) = _
    rfl
  simp only [SchwartzMap.neg_apply, neg_smul, smul_eq_mul, hb, hd, neg_mul,
    integral_neg] at he
  exact neg_eq_iff_eq_neg.mp he

/-- The physical H¹ graph is precisely the distributional derivative graph. -/
theorem c18_physical_H1Graph_iff_tempered_derivative {d : ℕ}
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    IsPhysicalH1Graph volume (Or.inl rfl) f G ↔
      ∀ l : Fin d, ∂_{unitVector l} (f : 𝓢'(Vec d, ℂ)) =
        (G l : 𝓢'(Vec d, ℂ)) := by
  constructor
  · exact fun h l => c18_tempered_derivative_of_physical_H1Graph h l
  · intro h
    have hloc (u : Lp ℂ 2 (volume : Measure (Vec d))) :
        LocallyIntegrable (fun x => u x) volume := (Lp.memLp u).locallyIntegrable (by norm_num)
    have hreal (u : Lp ℂ 2 (volume : Measure (Vec d))) :
        LocallyIntegrableOn (fun x => (u x).re) Set.univ volume := by
      apply locallyIntegrableOn_univ.mpr
      have hm := Complex.reCLM.comp_memLp' (Lp.memLp u)
      exact hm.locallyIntegrable (by norm_num)
    have himag (u : Lp ℂ 2 (volume : Measure (Vec d))) :
        LocallyIntegrableOn (fun x => (u x).im) Set.univ volume := by
      apply locallyIntegrableOn_univ.mpr
      have hm := Complex.imCLM.comp_memLp' (Lp.memLp u)
      exact hm.locallyIntegrable (by norm_num)
    have htest (i : Fin d) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
        (∫ x, (coordinateDerivative i φ x : ℂ) * f x) =
          -(∫ x, (φ x : ℂ) * G i x) := c18_tempered_test_identity f (G i) i (h i) φ hφ
    have hint (u : Lp ℂ 2 (volume : Measure (Vec d))) (φ : Vec d → ℝ)
        (hc : Continuous φ) (hs : HasCompactSupport φ) :
        Integrable (fun x => (φ x : ℂ) * u x) volume := by
      simpa only [smul_eq_mul, Function.comp_apply] using
        (hloc u).integrable_smul_left_of_hasCompactSupport
          (Complex.continuous_ofReal.comp hc) (hs.comp_left rfl)
    constructor <;> intro i <;> refine ⟨?_, ?_, ?_⟩
    · exact hreal f
    · exact hreal (G i)
    · intro φ hφ
      have hdcont : Continuous (coordinateDerivative i φ) := by
        change Continuous (fun x => fderiv ℝ φ x (unitVector i))
        exact (hφ.1.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk continuous_const)
      have hdsupp : HasCompactSupport (coordinateDerivative i φ) :=
        hφ.2.1.fderiv_apply ℝ (unitVector i)
      have he := congrArg Complex.re (htest i φ hφ)
      have hr₁ := integral_re (hint f _ hdcont hdsupp)
      have hr₂ := integral_re (hint (G i) φ hφ.1.continuous hφ.2.1)
      simp only [RCLike.re_eq_complex_re] at hr₁ hr₂
      simp only [Complex.neg_re] at he
      rw [← hr₁, ← hr₂] at he
      simpa [Complex.mul_re, Measure.restrict_univ, mul_comm] using he
    · exact himag f
    · exact himag (G i)
    · intro φ hφ
      have hdcont : Continuous (coordinateDerivative i φ) := by
        change Continuous (fun x => fderiv ℝ φ x (unitVector i))
        exact (hφ.1.continuous_fderiv_apply (by simp)).comp
          (continuous_id.prodMk continuous_const)
      have hdsupp : HasCompactSupport (coordinateDerivative i φ) :=
        hφ.2.1.fderiv_apply ℝ (unitVector i)
      have he := congrArg Complex.im (htest i φ hφ)
      have hi₁ := integral_im (hint f _ hdcont hdsupp)
      have hi₂ := integral_im (hint (G i) φ hφ.1.continuous hφ.2.1)
      simp only [RCLike.im_eq_complex_im] at hi₁ hi₂
      simp only [Complex.neg_im] at he
      rw [← hi₁, ← hi₂] at he
      simpa [Complex.mul_im, Measure.restrict_univ, mul_comm] using he

/-- Directional derivatives commute on Schwartz test functions. -/
private theorem c18_schwartz_lineDeriv_comm {d : ℕ} (a : 𝓢(Vec d, ℂ))
    (v w : Vec d) : ∂_{v} (∂_{w} a) = ∂_{w} (∂_{v} a) := by
  ext x
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  change fderiv ℝ (fun y => fderiv ℝ a y w) x v =
    fderiv ℝ (fun y => fderiv ℝ a y v) x w
  have hs : ContDiff ℝ (1 : ℕ∞) (fderiv ℝ a) :=
    (a.smooth ⊤).fderiv_right (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ a) x := (hs.differentiable (by simp)) x
  rw [fderiv_clm_apply hd (differentiableAt_const w),
    fderiv_clm_apply hd (differentiableAt_const v)]
  simpa [fderiv_const] using
    ((a.smooth ⊤).contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- The supplied second physical derivatives commute. -/
theorem c18_physical_H2_mixed_partials_eq {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j)) :
    ∀ j k, H j k = H k j := by
  intro j k
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure (Vec d))) (p := 2)))
  change (H j k : 𝓢'(Vec d, ℂ)) = (H k j : 𝓢'(Vec d, ℂ))
  rw [← c18_tempered_derivative_of_physical_H1Graph (hH j) k,
    ← c18_tempered_derivative_of_physical_H1Graph (hH k) j,
    ← c18_tempered_derivative_of_physical_H1Graph hG j,
    ← c18_tempered_derivative_of_physical_H1Graph hG k]
  ext a
  simp only [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
    neg_neg]
  rw [c18_schwartz_lineDeriv_comm]

/-- First and second physical graph witnesses for the same function are unique. -/
theorem c18_physical_H2_derivatives_unique {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G G' : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    {H H' : Fin d → Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hG' : IsPhysicalH1Graph volume (Or.inl rfl) f G')
    (hH : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G j) (H j))
    (hH' : ∀ j, IsPhysicalH1Graph volume (Or.inl rfl) (G' j) (H' j)) :
    G = G' ∧ H = H' := by
  have hinj := LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure (Vec d))) (p := 2))
  have h : G = G' := by
    funext j
    apply hinj
    change (G j : 𝓢'(Vec d, ℂ)) = (G' j : 𝓢'(Vec d, ℂ))
    rw [← c18_tempered_derivative_of_physical_H1Graph hG j,
      ← c18_tempered_derivative_of_physical_H1Graph hG' j]
  refine ⟨h, ?_⟩
  subst G'
  funext j k
  apply hinj
  change (H j k : 𝓢'(Vec d, ℂ)) = (H' j k : 𝓢'(Vec d, ℂ))
  rw [← c18_tempered_derivative_of_physical_H1Graph (hH j) k,
    ← c18_tempered_derivative_of_physical_H1Graph (hH' j) k]


/-- A uniformly bounded continuous representative of each output determines
bounded linear point evaluation.  The representatives need not be selected
linearly: uniqueness forces the selected values to be linear. -/
theorem c18_point_evaluation_of_continuous_representatives {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (x : Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ y, ‖u y‖ ≤ C * ‖f‖) :
    ∃ L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      ‖L‖ ≤ C ∧ ∀ f u, Continuous u →
        u =ᵐ[volume] (T f : Vec d → ℂ) → L f = u x := by
  classical
  let u := fun f => Classical.choose (hrep f)
  have hu (f) := Classical.choose_spec (hrep f)
  have hadd (f g) : u (f + g) = fun y => u f y + u g y := by
    apply Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d))) _
      (hu (f + g)).1 ((hu f).1.add (hu g).1)
    filter_upwards [(hu (f + g)).2.1, (hu f).2.1, (hu g).2.1,
      Lp.coeFn_add (T f) (T g)] with y ha hf hg hab
    have ha' := ha.trans (congrArg (fun z : Lp ℂ 2 (volume : Measure (Vec d)) => z y)
      (T.map_add f g))
    simpa only [Pi.add_apply, hf, hg] using ha'.trans hab
  have hsmul (c : ℂ) f : u (c • f) = fun y => c • u f y := by
    apply Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d))) _ (hu (c • f)).1
      (show Continuous (fun y => c • u f y) from
        (continuous_const : Continuous (fun _ : Vec d => c)).smul (hu f).1)
    filter_upwards [(hu (c • f)).2.1, (hu f).2.1,
      Lp.coeFn_smul c (T f)] with y ha hf hc
    have ha' := ha.trans (congrArg (fun z : Lp ℂ 2 (volume : Measure (Vec d)) => z y)
      (T.map_smul c f))
    calc
      u (c • f) y = c • (T f) y := by simpa only [Pi.smul_apply] using ha'.trans hc
      _ = c • u f y := congrArg (fun z : ℂ => c • z) hf.symm
  let L₀ : Lp ℂ 2 (volume : Measure (Vec d)) →ₗ[ℂ] ℂ :=
    { toFun := fun f => u f x
      map_add' := fun f g => congrFun (hadd f g) x
      map_smul' := fun c f => congrFun (hsmul c f) x }
  have hbound : ∀ f, ‖L₀ f‖ ≤ C * ‖f‖ := fun f => (hu f).2.2 x
  refine ⟨L₀.mkContinuous C hbound, L₀.mkContinuous_norm_le hC hbound, ?_⟩
  intro f v hv hveq
  change u f x = v x
  exact congrFun (Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d))) ((hu f).2.1.trans hveq.symm) (hu f).1 hv) x


/-- Bounded C¹ representatives also determine bounded linear evaluation of a
fixed directional derivative. -/
theorem c18_derivative_evaluation_of_C1_representatives {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (x v : Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧
      (∀ y, ‖u y‖ ≤ C * ‖f‖) ∧ ‖fderiv ℝ u x v‖ ≤ C * ‖f‖) :
    ∃ L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      ‖L‖ ≤ C ∧ ∀ f u, ContDiff ℝ 1 u →
        u =ᵐ[volume] (T f : Vec d → ℂ) → L f = fderiv ℝ u x v := by
  classical
  have hvrep : ∀ f, ∃ u : Vec d → ℂ, Continuous u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ y, ‖u y‖ ≤ C * ‖f‖ := by
    intro f
    obtain ⟨u, hu, he, hb, _⟩ := hrep f
    exact ⟨u, hu.continuous, he, hb⟩
  choose E hEbound hE using fun y =>
    c18_point_evaluation_of_continuous_representatives T y C hC hvrep
  let u := fun f => Classical.choose (hrep f)
  have hu (f) := Classical.choose_spec (hrep f)
  have hadd (f g) : u (f + g) = fun y => u f y + u g y := by
    funext y
    calc
      u (f + g) y = E y (f + g) := (hE y (f + g) _ (hu (f + g)).1.continuous
        (hu (f + g)).2.1).symm
      _ = E y f + E y g := map_add (E y) f g
      _ = u f y + u g y := by
        rw [hE y f _ (hu f).1.continuous (hu f).2.1,
          hE y g _ (hu g).1.continuous (hu g).2.1]
  have hsmul (c : ℂ) f : u (c • f) = fun y => c • u f y := by
    funext y
    calc
      u (c • f) y = E y (c • f) := (hE y (c • f) _ (hu (c • f)).1.continuous
        (hu (c • f)).2.1).symm
      _ = c • E y f := map_smul (E y) c f
      _ = c • u f y := by rw [hE y f _ (hu f).1.continuous (hu f).2.1]
  have hd (f) : DifferentiableAt ℝ (u f) x :=
    ((hu f).1.differentiable (by simp)) x
  let L₀ : Lp ℂ 2 (volume : Measure (Vec d)) →ₗ[ℂ] ℂ :=
    { toFun := fun f => fderiv ℝ (u f) x v
      map_add' := by
        intro f g
        rw [hadd, fderiv_fun_add (hd f) (hd g)]
        rfl
      map_smul' := by
        intro c f
        rw [hsmul, fderiv_fun_const_smul (hd f) c]
        rfl }
  have hbound : ∀ f, ‖L₀ f‖ ≤ C * ‖f‖ := fun f => (hu f).2.2.2
  refine ⟨L₀.mkContinuous C hbound, L₀.mkContinuous_norm_le hC hbound, ?_⟩
  intro f w hw hweq
  change fderiv ℝ (u f) x v = fderiv ℝ w x v
  have heq : u f = w := Measure.eq_of_ae_eq (μ := (volume : Measure (Vec d)))
    ((hu f).2.1.trans hweq.symm) (hu f).1.continuous hw.continuous
  rw [heq]


/-- The Euclidean value-and-gradient estimate supplies bounded linear value and
coordinate-derivative evaluations for the same physical L² operator. -/
theorem c18_evaluations_of_euclidean_C1_bound {d : ℕ}
    (T : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))) (x : Vec d) (C : ℝ) (hC : 0 ≤ C)
    (hrep : ∀ f, ∃ u : Vec d → ℂ, ContDiff ℝ 1 u ∧
      u =ᵐ[volume] (T f : Vec d → ℂ) ∧ ∀ y,
        ‖u y‖ + Real.sqrt (∑ j : Fin d, ‖fderiv ℝ u y (unitVector j)‖ ^ 2) ≤
          C * ‖f‖) :
    (∃ L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      ‖L‖ ≤ C ∧ ∀ f u, ContDiff ℝ 1 u →
        u =ᵐ[volume] (T f : Vec d → ℂ) → L f = u x) ∧
    ∀ j : Fin d, ∃ L : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] ℂ,
      ‖L‖ ≤ C ∧ ∀ f u, ContDiff ℝ 1 u →
        u =ᵐ[volume] (T f : Vec d → ℂ) →
          L f = fderiv ℝ u x (unitVector j) := by
  classical
  have hvalue (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ)
      (h : ∀ y, ‖u y‖ + Real.sqrt (∑ j : Fin d,
        ‖fderiv ℝ u y (unitVector j)‖ ^ 2) ≤ C * ‖f‖) :
      ∀ y, ‖u y‖ ≤ C * ‖f‖ := by
    intro y
    have hs := Real.sqrt_nonneg (∑ j : Fin d, ‖fderiv ℝ u y (unitVector j)‖ ^ 2)
    linarith [h y]
  have hcoord (f : Lp ℂ 2 (volume : Measure (Vec d))) (u : Vec d → ℂ) (j : Fin d)
      (h : ∀ y, ‖u y‖ + Real.sqrt (∑ k : Fin d,
        ‖fderiv ℝ u y (unitVector k)‖ ^ 2) ≤ C * ‖f‖) :
      ‖fderiv ℝ u x (unitVector j)‖ ≤ C * ‖f‖ := by
    have hs : ‖fderiv ℝ u x (unitVector j)‖ ^ 2 ≤
        ∑ k : Fin d, ‖fderiv ℝ u x (unitVector k)‖ ^ 2 :=
      Finset.single_le_sum (f := fun k : Fin d => ‖fderiv ℝ u x (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)
    have hs' := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] at hs'
    have hu := norm_nonneg (u x)
    linarith [h x]
  constructor
  · obtain ⟨L, hL, hLeval⟩ := c18_point_evaluation_of_continuous_representatives
      T x C hC (fun f => by
        obtain ⟨u, hu, he, hb⟩ := hrep f
        exact ⟨u, hu.continuous, he, hvalue f u hb⟩)
    exact ⟨L, hL, fun f u hu he => hLeval f u hu.continuous he⟩
  · intro j
    apply c18_derivative_evaluation_of_C1_representatives T x (unitVector j) C hC
    intro f
    obtain ⟨u, hu, he, hb⟩ := hrep f
    exact ⟨u, hu, he, hvalue f u hb, hcoord f u j hb⟩

/-- A Euclidean C¹ representative pulls back to the project's coordinate
carrier, preserving its almost-everywhere identity and directional derivatives. -/
theorem c18_euclidean_C1_representative_pullback {d : ℕ}
    (v : EuclideanSpace ℝ (Fin d) → ℂ) (g : Vec d → ℂ)
    (hv : ContDiff ℝ 1 v)
    (he : v =ᵐ[volume] (fun y => g (WithLp.ofLp y))) :
    ContDiff ℝ 1 (fun x : Vec d => v (WithLp.toLp 2 x)) ∧
    (fun x : Vec d => v (WithLp.toLp 2 x)) =ᵐ[volume] g ∧
    ∀ x m : Vec d,
      fderiv ℝ (fun x : Vec d => v (WithLp.toLp 2 x)) x m =
        fderiv ℝ v (WithLp.toLp 2 x) (WithLp.toLp 2 m) := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  constructor
  · exact hv.comp J.contDiff
  constructor
  · have h := (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [h] with x hx
    exact hx
  · intro x m
    have hv' : DifferentiableAt ℝ v (J x) := hv.differentiable (by norm_num) _
    have hJ : DifferentiableAt ℝ J x := J.differentiableAt
    change fderiv ℝ (v ∘ J) x m = fderiv ℝ v (J x) (J m)
    rw [fderiv_comp x hv' hJ, J.fderiv]
    rfl

end EinsteinFull
