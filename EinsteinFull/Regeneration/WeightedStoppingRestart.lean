import EinsteinFull.Regeneration.CoordinateSlabStopping
import EinsteinFull.Calculus.U1RegularKernelContinuity
import MarkovProcess.Trajectory.StoppingLtTop

/-!
# Weighted restarts at extended stopping times

Events and weights that are decided by the path before a stopping time belong to
the stopped history, provided stopping the path at any later deterministic time
does not change them. For such weights, the strong Markov property of a supplied
realization restarts every nonnegative functional of the shifted path.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A set decided before a finite stopping time belongs to the stopped history. -/
theorem measurableSet_stopping_of_prefix {d : ℕ}
    (T : Path d → WithTop ℝ≥0) (hTm : Measurable T)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (hTpre : ∀ (γ : Path d) (t : ℝ≥0),
      (T (MarkovProcess.ContinuousPath.stoppedPath t γ) ≤ t ↔ T γ ≤ t))
    (s : Set (Path d)) (hs : MeasurableSet s) (hfin : ∀ γ ∈ s, T γ < ⊤)
    (hpre : ∀ (γ : Path d) (t : ℝ≥0), T γ ≤ t →
      (MarkovProcess.ContinuousPath.stoppedPath t γ ∈ s ↔ γ ∈ s)) :
    MeasurableSet[hT.measurableSpace] s := by
  have hcut : ∀ t : ℝ≥0, MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) t] (s ∩ {γ | T γ ≤ t}) := by
    intro t
    have heq : s ∩ {γ | T γ ≤ t} =
        (MarkovProcess.ContinuousPath.stoppedPath t) ⁻¹' (s ∩ {γ | T γ ≤ t}) := by
      ext γ
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage]
      constructor
      · rintro ⟨hγ, hle⟩
        exact ⟨(hpre γ t hle).mpr hγ, (hTpre γ t).mpr hle⟩
      · rintro ⟨hγ, hle⟩
        have hle' := (hTpre γ t).mp hle
        exact ⟨(hpre γ t hle').mp hγ, hle'⟩
    rw [heq]
    exact measurable_stoppedPath_canonicalHistory t
      (hs.inter (hTm measurableSet_Iic))
  refine ⟨?_, hcut⟩
  have hunion : s = ⋃ n : ℕ, (s ∩ {γ | T γ ≤ (n : ℝ≥0)}) := by
    ext γ
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · intro hγ
      obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp (hfin γ hγ).ne
      obtain ⟨n, hn⟩ := exists_nat_ge u
      exact ⟨n, hγ, by rw [← hu]; exact WithTop.coe_le_coe.mpr hn⟩
    · rintro ⟨_, hγ, _⟩
      exact hγ
  rw [hunion]
  exact MeasurableSet.iUnion fun n =>
    (le_iSup (fun t => MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t)
      (n : ℝ≥0)) _ (hcut n)

/-- A weight decided before a stopping time, and vanishing where the stopping time
is infinite, is measurable for the stopped history. -/
theorem measurable_stopping_of_prefix {d : ℕ}
    (T : Path d → WithTop ℝ≥0) (hTm : Measurable T)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (hTpre : ∀ (γ : Path d) (t : ℝ≥0),
      (T (MarkovProcess.ContinuousPath.stoppedPath t γ) ≤ t ↔ T γ ≤ t))
    (f : Path d → ℝ≥0∞) (hf : Measurable f) (hfin : ∀ γ, T γ = ⊤ → f γ = 0)
    (hpre : ∀ (γ : Path d) (t : ℝ≥0), T γ ≤ t →
      f (MarkovProcess.ContinuousPath.stoppedPath t γ) = f γ) :
    Measurable[hT.measurableSpace] f := by
  have hzero : ∀ B : Set ℝ≥0∞, MeasurableSet B → (0 : ℝ≥0∞) ∉ B →
      MeasurableSet[hT.measurableSpace] (f ⁻¹' B) := by
    intro B hB h0
    apply measurableSet_stopping_of_prefix T hTm hT hTpre _ (hf hB)
    · intro γ hγ
      by_contra htop
      have hγ' : f γ ∈ B := hγ
      rw [hfin γ (not_lt_top_iff.mp htop)] at hγ'
      exact h0 hγ'
    · intro γ t hle
      simp only [Set.mem_preimage, hpre γ t hle]
  intro B hB
  by_cases h0 : (0 : ℝ≥0∞) ∈ B
  · have hc := hzero Bᶜ hB.compl (fun h => h h0)
    have heq : f ⁻¹' B = (f ⁻¹' Bᶜ)ᶜ := by
      rw [Set.preimage_compl, compl_compl]
    rw [heq]
    exact hc.compl
  · exact hzero B hB h0

/-- Strong Markov restart of a supplied realization against a weight decided
before a stopping time. -/
theorem lintegral_mul_shift_extended_stopping {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (T : Path d → WithTop ℝ≥0) (hTm : Measurable T)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (x : Vec d) (w : Path d → ℝ≥0∞) (hw : Measurable[hT.measurableSpace] w)
    (hwT : ∀ γ, T γ = ⊤ → w γ = 0) (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ, w γ * F (MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) ∂G.pathLaw x) =
      ∫⁻ γ, w γ * (∫⁻ η, F η ∂G.pathLaw (γ ((T γ).untopD 0))) ∂G.pathLaw x := by
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  let μ := G.pathLaw x
  let A₀ : Set (Path d) := {γ | T γ < ⊤}
  have hA₀ : MeasurableSet[hT.measurableSpace] A₀ :=
    MarkovProcess.StoppingTime.measurableSet_stoppingTime_lt_top hT
  have hle : hT.measurableSpace ≤ borel (Path d) := hT.measurableSpace_le
  have hA₀m : MeasurableSet A₀ := hle _ hA₀
  have hU : Measurable (fun γ : Path d => (T γ).untopD 0) :=
    (WithTop.measurable_untopD 0).comp hTm
  let S : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ
  have hS : Measurable S :=
    MarkovProcess.ContinuousPath.continuous_shift.measurable.comp (hU.prodMk measurable_id)
  let E : Path d → Vec d := fun γ => γ ((T γ).untopD 0)
  have hE : Measurable E := continuous_eval.measurable.comp (measurable_id.prodMk hU)
  let Fb : Vec d → ℝ≥0∞ := fun y => ∫⁻ η, F η ∂G.pathLaw y
  have hFb : Measurable Fb := hF.lintegral_kernel
  let ν₁ := (μ.restrict A₀).withDensity (fun γ => F (S γ))
  let ν₂ := (μ.restrict A₀).withDensity (fun γ => Fb (E γ))
  have hsets : ∀ A, MeasurableSet[hT.measurableSpace] A → ν₁ A = ν₂ A := by
    intro A hA
    have hAm : MeasurableSet A := hle _ hA
    have hAA : MeasurableSet[hT.measurableSpace] (A ∩ A₀) := hA.inter hA₀
    have hr := u1_supplied_regular_extended_stopping_restart hd ω lam Λ hΛ hω h0 h1 G T hT x
      (A ∩ A₀) hAA (fun γ hγ => hγ.2)
    simp only [ν₁, ν₂]
    rw [withDensity_apply _ hAm, withDensity_apply _ hAm, Measure.restrict_restrict hAm]
    calc (∫⁻ γ in A ∩ A₀, F (S γ) ∂μ)
        = ∫⁻ η, F η ∂((μ.restrict (A ∩ A₀)).map S) := (lintegral_map hF hS).symm
      _ = ∫⁻ η, F η ∂(Measure.bind (μ.restrict (A ∩ A₀)) (fun γ => G.pathLaw (E γ))) := by
          rw [hr]
      _ = ∫⁻ γ in A ∩ A₀, Fb (E γ) ∂μ := by
          exact Measure.lintegral_bind ((G.pathLaw.measurable.comp hE).aemeasurable)
            hF.aemeasurable
  have htrim : ν₁.trim hle = ν₂.trim hle := by
    refine @Measure.ext _ hT.measurableSpace _ _ fun A hA => ?_
    rw [trim_measurableSet_eq hle hA, trim_measurableSet_eq hle hA]
    exact hsets A hA
  have hwm : Measurable w := hw.mono hle le_rfl
  have hsupp₁ : (fun γ => w γ * F (S γ)).support ⊆ A₀ := by
    intro γ hγ
    by_contra hnot
    exact hγ (by simp only [hwT γ (not_lt_top_iff.mp hnot), zero_mul])
  have hsupp₂ : (fun γ => w γ * Fb (E γ)).support ⊆ A₀ := by
    intro γ hγ
    by_contra hnot
    exact hγ (by simp only [hwT γ (not_lt_top_iff.mp hnot), zero_mul])
  have h₁ : (∫⁻ γ, w γ ∂ν₁) = ∫⁻ γ, w γ * F (S γ) ∂μ := by
    show (∫⁻ γ, w γ ∂(μ.restrict A₀).withDensity (F ∘ S)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ (hF.comp hS) hwm]
    simp only [Pi.mul_apply, Function.comp_apply, mul_comm (F (S _))]
    exact setLIntegral_eq_of_support_subset hsupp₁
  have h₂ : (∫⁻ γ, w γ ∂ν₂) = ∫⁻ γ, w γ * Fb (E γ) ∂μ := by
    show (∫⁻ γ, w γ ∂(μ.restrict A₀).withDensity (Fb ∘ E)) = _
    rw [lintegral_withDensity_eq_lintegral_mul _ (hFb.comp hE) hwm]
    simp only [Pi.mul_apply, Function.comp_apply, mul_comm (Fb (E _))]
    exact setLIntegral_eq_of_support_subset hsupp₂
  calc (∫⁻ γ, w γ * F (MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) ∂G.pathLaw x)
      = ∫⁻ γ, w γ ∂ν₁ := h₁.symm
    _ = ∫⁻ γ, w γ ∂(ν₁.trim hle) := (lintegral_trim hle hw).symm
    _ = ∫⁻ γ, w γ ∂(ν₂.trim hle) := by rw [htrim]
    _ = ∫⁻ γ, w γ ∂ν₂ := lintegral_trim hle hw
    _ = _ := h₂

end EinsteinFull.Regeneration
