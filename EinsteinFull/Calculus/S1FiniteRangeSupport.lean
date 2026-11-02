import EinsteinFull.Work.W7.ClockFiniteRangeSupport

/-! Independence of finitely many functions that are (a.e.) measurable with respect to
the joint restriction σ-algebras of pairwise `s`-separated regions, `s > r₀`, for a
law of finite range `r₀`. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinRelation

theorem localSigma_mono {d : ℕ} {U W : Set (Vec d)} (h : U ⊆ W) :
    localSigma U ≤ localSigma W :=
  iSup_le fun x => le_iSup (fun y : W =>
    MeasurableSpace.comap (fun ω : FieldPair d => (ω.1 y, ω.2 y)) inferInstance)
    ⟨x, h x.2⟩

theorem measurableSet_biInter_of {α β : Type*} {m : MeasurableSpace α} (S : Finset β)
    {f : β → Set α} (h : ∀ i ∈ S, MeasurableSet[m] (f i)) :
    MeasurableSet[m] (⋂ i ∈ S, f i) :=
  Finset.measurableSet_biInter S h

theorem iIndep_localSigma {d : ℕ} {r₀ : ℝ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hfr : HasFiniteRange r₀ μ) {ι : Type*} [DecidableEq ι]
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i)) {s : ℝ} (hs : r₀ < s)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, s ≤ euclideanNorm (x - y)) :
    iIndep (fun i => localSigma (U i)) μ := by
  rw [iIndep_iff]
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro f _
    simp
  | insert j S hj ih =>
    intro f hf
    have hW : MeasurableSet (⋃ i ∈ S, U i) := Finset.measurableSet_biUnion S (fun i _ => hU i)
    have hind : Indep (localSigma (U j)) (localSigma (⋃ i ∈ S, U i)) μ :=
      hfr (U j) (⋃ i ∈ S, U i) (hU j) hW ⟨s, hs, by
        intro x hx y hy
        obtain ⟨i, hiS, hyi⟩ := Set.mem_iUnion₂.1 hy
        refine hsep j i ?_ x hx y hyi
        rintro rfl
        exact hj hiS⟩
    have hfj : MeasurableSet[localSigma (U j)] (f j) := hf j (Finset.mem_insert_self j S)
    have hrest : MeasurableSet[localSigma (⋃ i ∈ S, U i)] (⋂ i ∈ S, f i) := by
      apply measurableSet_biInter_of
      intro i hi
      exact localSigma_mono (Set.subset_biUnion_of_mem hi) _
        (hf i (Finset.mem_insert_of_mem hi))
    rw [Finset.set_biInter_insert, Finset.prod_insert hj,
      (Indep_iff _ _ μ).1 hind _ _ hfj hrest,
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem iIndepFun_congr_ae {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {ι : Type*}
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {f g : ∀ i, Ω → β i}
    (hg : iIndepFun g μ) (h : ∀ i, f i =ᵐ[μ] g i) : iIndepFun f μ := by
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hg ⊢
  intro S sets hmeas
  have hall : ∀ᵐ ω ∂μ, ∀ i ∈ S, f i ω = g i ω :=
    (ae_ball_iff (Finset.countable_toSet S)).2 fun i _ => h i
  have A : ∀ i ∈ S, μ (f i ⁻¹' sets i) = μ (g i ⁻¹' sets i) := by
    intro i _
    apply measure_congr
    filter_upwards [h i] with ω hω
    change (f i ω ∈ sets i) = (g i ω ∈ sets i)
    simp [hω]
  have B : μ (⋂ i ∈ S, f i ⁻¹' sets i) = μ (⋂ i ∈ S, g i ⁻¹' sets i) := by
    apply measure_congr
    filter_upwards [hall] with ω hω
    change (ω ∈ ⋂ i ∈ S, f i ⁻¹' sets i) = (ω ∈ ⋂ i ∈ S, g i ⁻¹' sets i)
    simp +contextual [hω]
  rw [B, Finset.prod_congr rfl A]
  exact hg S hmeas

theorem iIndepFun_of_local {d : ℕ} {r₀ : ℝ} {μ : Measure (FieldPair d)}
    [IsProbabilityMeasure μ] (hfr : HasFiniteRange r₀ μ) {ι : Type*} [DecidableEq ι]
    (U : ι → Set (Vec d)) (hU : ∀ i, MeasurableSet (U i)) {s : ℝ} (hs : r₀ < s)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ U i, ∀ y ∈ U j, s ≤ euclideanNorm (x - y))
    {β : ι → Type*} [∀ i, MeasurableSpace (β i)] {f : ∀ i, FieldPair d → β i}
    (g : ∀ i, FieldPair d → β i) (hg : ∀ i, Measurable[localSigma (U i)] (g i))
    (hfg : ∀ i, f i =ᵐ[μ] g i) : iIndepFun f μ := by
  refine iIndepFun_congr_ae ?_ hfg
  rw [iIndepFun_iff_iIndep]
  exact iIndep_of_iIndep_of_le (iIndep_localSigma hfr U hU hs hsep)
    (fun i => (hg i).comap_le)

end EinsteinFull.Calculus.S1
