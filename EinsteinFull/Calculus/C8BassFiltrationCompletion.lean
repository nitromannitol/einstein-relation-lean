import EinsteinFull.External.Draft.BassFoundation

/-!
# Completion of the canonical Bass filtration

The completion uses all null sets of the ambient path law before taking the
right continuation. The underlying paths and the original law are preserved.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace EinsteinFull.External.Bass.Completion

open EinsteinRelation

/-- Adding all ambient null sets is exactly adjoining almost-everywhere representatives.
The measure in the filter is the ambient law, rather than its restriction to `m`. -/
theorem sup_nullSets_eq_eventuallyMeasurableSpace {d : ℕ}
    (P : Measure (Bass.Path d)) (m : MeasurableSpace (Bass.Path d)) :
    m ⊔ MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0} =
      eventuallyMeasurableSpace m (ae P) := by
  apply le_antisymm
  · refine sup_le le_eventuallyMeasurableSpace (MeasurableSpace.generateFrom_le ?_)
    intro A hA
    exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hA
    have hleft : m ≤ m ⊔ MeasurableSpace.generateFrom
        {A : Set (Bass.Path d) | P A = 0} := le_sup_left
    have hright : MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0} ≤
        m ⊔ MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0} := le_sup_right
    have h₁ : MeasurableSet[m ⊔ MeasurableSpace.generateFrom
        {A : Set (Bass.Path d) | P A = 0}] B := hleft _ hB
    have h₂ : MeasurableSet[m ⊔ MeasurableSpace.generateFrom
        {A : Set (Bass.Path d) | P A = 0}] (B \ A) :=
      hright _ (MeasurableSpace.measurableSet_generateFrom (ae_eq_set.mp hAB).2)
    have h₃ : MeasurableSet[m ⊔ MeasurableSpace.generateFrom
        {A : Set (Bass.Path d) | P A = 0}] (A \ B) :=
      hright _ (MeasurableSpace.measurableSet_generateFrom (ae_eq_set.mp hAB).1)
    have hset : (B \ (B \ A)) ∪ (A \ B) = A := by
      ext γ
      simp only [Set.mem_union, Set.mem_sdiff]
      tauto
    exact hset ▸ (h₁.diff h₂).union h₃

/-- Almost-everywhere augmentation commutes with a decreasing countable intersection.
All augmentations use the same ambient law; no restricted measure is completed. -/
theorem eventuallyMeasurableSpace_iInf_of_antitone {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (m : ℕ → MeasurableSpace Ω) (hm : Antitone m) :
    eventuallyMeasurableSpace (⨅ n, m n) (ae P) =
      ⨅ n, eventuallyMeasurableSpace (m n) (ae P) := by
  apply le_antisymm
  · intro A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact MeasurableSpace.measurableSet_iInf.mpr fun n =>
      ⟨B, MeasurableSpace.measurableSet_iInf.mp hB n, hAB⟩
  · intro A hA
    have hrep (n : ℕ) : ∃ B, MeasurableSet[m n] B ∧ A =ᵐ[P] B :=
      MeasurableSpace.measurableSet_iInf.mp hA n
    choose B hB hAB using hrep
    let D (n : ℕ) : Set Ω := ⋃ j ≥ n, B j
    have hD (n : ℕ) : MeasurableSet[m n] (D n) :=
      MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun hj => hm hj _ (hB j)
    have hDanti : Antitone D := by
      intro i j hij
      exact Set.iUnion₂_mono' fun k hk => ⟨k, hij.trans hk, le_rfl⟩
    refine ⟨⋂ n, D n, MeasurableSpace.measurableSet_iInf.mpr ?_, ?_⟩
    · intro k
      rw [← hDanti.iInter_nat_add k]
      exact MeasurableSet.iInter fun n => hm (Nat.le_add_left k n) _ (hD (n + k))
    · filter_upwards [ae_all_iff.mpr hAB] with ω hω
      simp only [Set.mem_iInter, D, Set.mem_iUnion]
      apply propext
      constructor
      · intro hωA n
        exact ⟨n, le_rfl, (hω n).mp hωA⟩
      · intro hωD
        obtain ⟨j, _, hj⟩ := hωD 0
        exact (hω j).mpr hj

/-- The ambient null sets, including subsets of measurable null sets. -/
@[instance_reducible]
def nullSets {d : ℕ} (P : Measure (Bass.Path d)) : MeasurableSpace (Bass.Path d) :=
  MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0}

theorem nullSets_le_completion {d : ℕ} (P : Measure (Bass.Path d)) :
    nullSets P ≤ (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) :=
  MeasurableSpace.generateFrom_le fun _ hA => NullMeasurableSet.of_null hA

/-- Add all ambient null sets, and then take the right continuation. -/
noncomputable def usualFiltration {d : ℕ} (P : Measure (Bass.Path d)) :
    Filtration ℝ≥0
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) where
  seq t := ⨅ s : {s : ℝ≥0 // t < s}, Bass.rawFiltration d s.val ⊔ nullSets P
  mono' _s _t hst := le_iInf fun u => iInf_le_of_le ⟨u.val, hst.trans_lt u.property⟩ le_rfl
  le' t := iInf_le_of_le ⟨t + 1, lt_add_one t⟩
    (sup_le ((Bass.rawFiltration d).le (t + 1) |>.trans le_eventuallyMeasurableSpace)
      (nullSets_le_completion P))

/-- The literal sigma algebra in the usual augmentation. -/
theorem usualFiltration_apply {d : ℕ} (P : Measure (Bass.Path d)) (t : ℝ≥0) :
    usualFiltration P t =
      ⨅ s : {s : ℝ≥0 // t < s}, Bass.rawFiltration d s.val ⊔
        MeasurableSpace.generateFrom {A : Set (Bass.Path d) | P A = 0} := rfl

instance {d : ℕ} (P : Measure (Bass.Path d)) : (usualFiltration P).IsRightContinuous := by
  constructor
  intro t
  rw [Filtration.rightCont_eq]
  change (⨅ s > t, usualFiltration P s) ≤
    ⨅ u : {u : ℝ≥0 // t < u}, Bass.rawFiltration d u.val ⊔ nullSets P
  refine le_iInf fun u => ?_
  obtain ⟨s, hts, hsu⟩ := exists_between u.property
  exact iInf₂_le_of_le s hts
    (iInf_le_of_le ⟨u.val, hsu⟩ le_rfl)

/-- Right continuation commutes with augmentation by the null sets of the fixed law.
In particular, usual-time events have representatives at the uncompleted right-continuous time. -/
theorem usualFiltration_eq_eventuallyMeasurableSpace {d : ℕ}
    (P : Measure (Bass.Path d)) (t : ℝ≥0) :
    usualFiltration P t = eventuallyMeasurableSpace (Bass.filtration d t) (ae P) := by
  obtain ⟨u, hu, htu, hlim⟩ := exists_seq_strictAnti_tendsto t
  have hcofinal (s : ℝ≥0) (hs : t < s) : ∃ n, u n ≤ s := by
    obtain ⟨n, hn⟩ := (hlim.eventually (eventually_lt_nhds hs)).exists
    exact ⟨n, hn.le⟩
  have hseq (m : ℝ≥0 → MeasurableSpace (Bass.Path d)) (hm : Monotone m) :
      (⨅ s : {s : ℝ≥0 // t < s}, m s.val) = ⨅ n, m (u n) := by
    apply le_antisymm
    · exact le_iInf fun n => iInf_le
        (fun s : {s : ℝ≥0 // t < s} => m s.val) ⟨u n, htu n⟩
    · refine le_iInf fun s => ?_
      obtain ⟨n, hn⟩ := hcofinal s.val s.property
      exact iInf_le_of_le n (hm hn)
  have hraw : Bass.filtration d t = ⨅ n, Bass.rawFiltration d (u n) := by
    rw [Bass.filtration, Filtration.rightCont_eq]
    apply le_antisymm
    · exact le_iInf fun n => iInf₂_le (u n) (htu n)
    · refine le_iInf fun s => le_iInf fun hs => ?_
      obtain ⟨n, hn⟩ := hcofinal s hs
      exact iInf_le_of_le n ((Bass.rawFiltration d).mono hn)
  change (⨅ s : {s : ℝ≥0 // t < s}, Bass.rawFiltration d s.val ⊔ nullSets P) = _
  rw [hseq _ (fun _ _ hst => sup_le_sup_right ((Bass.rawFiltration d).mono hst) _)]
  simp_rw [nullSets, sup_nullSets_eq_eventuallyMeasurableSpace]
  rw [← eventuallyMeasurableSpace_iInf_of_antitone P _
    (fun _ _ hnm => (Bass.rawFiltration d).mono (hu.antitone hnm)), ← hraw]

/-- A usual event has an almost-surely equal uncompleted event at the same time. -/
theorem measurableSet_usualFiltration_iff {d : ℕ} (P : Measure (Bass.Path d))
    (t : ℝ≥0) (A : Set (Bass.Path d)) :
    MeasurableSet[usualFiltration P t] A ↔
      ∃ B, MeasurableSet[Bass.filtration d t] B ∧ A =ᵐ[P] B := by
  rw [usualFiltration_eq_eventuallyMeasurableSpace]
  rfl

theorem filtration_le_usualFiltration {d : ℕ} (P : Measure (Bass.Path d))
    (t : ℝ≥0) : Bass.filtration d t ≤ usualFiltration P t := by
  rw [usualFiltration_eq_eventuallyMeasurableSpace]
  exact le_eventuallyMeasurableSpace

theorem rawFiltration_le_usualFiltration {d : ℕ} (P : Measure (Bass.Path d))
    (t : ℝ≥0) : Bass.rawFiltration d t ≤ usualFiltration P t :=
  le_iInf fun s => ((Bass.rawFiltration d).mono s.property.le).trans le_sup_left

theorem nullSets_le_usualFiltration {d : ℕ} (P : Measure (Bass.Path d))
    (t : ℝ≥0) : nullSets P ≤ usualFiltration P t :=
  le_iInf fun _ => le_sup_right

/-- All ambient null subsets are measurable at every usual time. -/
theorem measurableSet_usualFiltration_of_null {d : ℕ} {P : Measure (Bass.Path d)}
    {A : Set (Bass.Path d)} (hA : P A = 0) (t : ℝ≥0) :
    MeasurableSet[usualFiltration P t] A :=
  nullSets_le_usualFiltration P t _ (MeasurableSpace.measurableSet_generateFrom hA)

/-- Restricting the completed law to the original cylindrical sigma algebra recovers `P`. -/
theorem completion_trim {d : ℕ} (P : Measure (Bass.Path d)) :
    @Measure.trim (Bass.Path d) (inferInstance : MeasurableSpace (Bass.Path d))
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P))
      P.completion le_eventuallyMeasurableSpace = P := by
  ext A hA
  erw [trim_measurableSet_eq _ hA]
  rfl

/-- Finiteness with the original path carrier and the completed ambient sigma algebra. -/
theorem completion_isFiniteMeasure {d : ℕ} (P : Measure (Bass.Path d)) [IsFiniteMeasure P] :
    @IsFiniteMeasure (Bass.Path d)
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) P.completion :=
  ⟨measure_lt_top P _⟩

/-- The completed law is sigma finite at every usual time, with the path carrier explicit. -/
theorem completion_sigmaFiniteFiltration {d : ℕ} (P : Measure (Bass.Path d))
    [IsFiniteMeasure P] :
    SigmaFiniteFiltration (Ω := Bass.Path d) P.completion (usualFiltration P) :=
  @IsFiniteMeasure.sigmaFiniteFiltration _ _ _ _ P.completion
    (usualFiltration P) (completion_isFiniteMeasure P)

/-- Restriction of the completed finite law, with the original path carrier explicit. -/
theorem completion_restrict_isFiniteMeasure {d : ℕ} (P : Measure (Bass.Path d))
    [IsFiniteMeasure P] (A : Set (Bass.Path d)) :
    @IsFiniteMeasure (Bass.Path d)
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P))
      (@Measure.restrict (Bass.Path d)
        (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P))
        P.completion A) :=
  @isFiniteMeasureRestrict (Bass.Path d) _ P.completion A (completion_isFiniteMeasure P)

/-- Integrability of an originally strongly measurable function is unchanged by completion. -/
theorem integrable_completion_iff {d : ℕ} {P : Measure (Bass.Path d)}
    {f : Bass.Path d → ℝ} (hf : StronglyMeasurable f) :
    Integrable f P.completion ↔ Integrable f P := by
  constructor
  · intro h
    have ht := h.trim le_eventuallyMeasurableSpace hf
    erw [completion_trim P] at ht
    exact ht
  · intro h
    apply integrable_of_integrable_trim le_eventuallyMeasurableSpace
    erw [completion_trim P]
    exact h

/-- Completion preserves the integral of an originally strongly measurable function. -/
theorem integral_completion {d : ℕ} {P : Measure (Bass.Path d)}
    {f : Bass.Path d → ℝ} (hf : StronglyMeasurable f) :
    (∫ γ : Bass.Path d, f γ ∂P.completion) = ∫ γ, f γ ∂P := by
  erw [integral_trim le_eventuallyMeasurableSpace hf, completion_trim]

/-- Set integrals agree on every original measurable event. -/
theorem setIntegral_completion {d : ℕ} {P : Measure (Bass.Path d)}
    {f : Bass.Path d → ℝ} (hf : StronglyMeasurable f) {A : Set (Bass.Path d)}
    (hA : MeasurableSet A) :
    (∫ γ : Bass.Path d in A, f γ ∂P.completion) = ∫ γ : Bass.Path d in A, f γ ∂P := by
  have hAcomp : @MeasurableSet (Bass.Path d)
      (inferInstance : MeasurableSpace (NullMeasurableSpace (Bass.Path d) P)) A :=
    hA.nullMeasurableSet
  erw [← integral_indicator hAcomp, ← integral_indicator hA]
  exact integral_completion (hf.indicator hA)

/-- True martingales extend to the completed usual filtration for the same law. -/
theorem martingale_completion {d : ℕ} {P : Measure (Bass.Path d)} [IsFiniteMeasure P]
    {M : ℝ≥0 → Bass.Path d → ℝ} (hM : Martingale M (Bass.filtration d) P) :
    Martingale M (usualFiltration P) P.completion := by
  haveI := completion_isFiniteMeasure P
  haveI : IsFiniteMeasure P.completion := ⟨measure_lt_top P _⟩
  haveI := completion_sigmaFiniteFiltration P
  haveI : SigmaFiniteFiltration P.completion (usualFiltration P) :=
    completion_sigmaFiniteFiltration P
  have hmeas (t : ℝ≥0) : StronglyMeasurable (M t) :=
    (hM.stronglyAdapted t).mono ((Bass.filtration d).le t)
  have hint (t : ℝ≥0) : Integrable (M t) P.completion :=
    (integrable_completion_iff (hmeas t)).mpr (hM.integrable t)
  have had : StronglyAdapted (usualFiltration P) M :=
    fun t => (hM.stronglyAdapted t).mono (filtration_le_usualFiltration P t)
  refine ⟨had, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((usualFiltration P).le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (had s).aestronglyMeasurable
  obtain ⟨B, hB, hAB⟩ := (measurableSet_usualFiltration_iff P s A).mp hA
  have hBglobal := (Bass.filtration d).le s _ hB
  calc
    (∫ γ : Bass.Path d in A, M s γ ∂P.completion) = ∫ γ : Bass.Path d in B, M s γ ∂P.completion :=
      setIntegral_congr_set hAB
    _ = ∫ γ : Bass.Path d in B, M s γ ∂P := setIntegral_completion (hmeas s) hBglobal
    _ = ∫ γ : Bass.Path d in B, M t γ ∂P := hM.setIntegral_eq hst hB
    _ = ∫ γ : Bass.Path d in B, M t γ ∂P.completion := (setIntegral_completion (hmeas t) hBglobal).symm
    _ = ∫ γ : Bass.Path d in A, M t γ ∂P.completion := setIntegral_congr_set hAB.symm

/-- A completed true martingale descends when the actual process is originally adapted. -/
theorem martingale_of_completion {d : ℕ} {P : Measure (Bass.Path d)} [IsFiniteMeasure P]
    {M : ℝ≥0 → Bass.Path d → ℝ} (hM : Martingale M (usualFiltration P) P.completion)
    (had : StronglyAdapted (Bass.filtration d) M) :
    Martingale M (Bass.filtration d) P := by
  haveI := completion_isFiniteMeasure P
  haveI : IsFiniteMeasure P.completion := ⟨measure_lt_top P _⟩
  haveI := completion_sigmaFiniteFiltration P
  haveI : SigmaFiniteFiltration P.completion (usualFiltration P) :=
    completion_sigmaFiniteFiltration P
  have hmeas (t : ℝ≥0) : StronglyMeasurable (M t) :=
    (had t).mono ((Bass.filtration d).le t)
  have hint (t : ℝ≥0) : Integrable (M t) P :=
    (integrable_completion_iff (hmeas t)).mp (hM.integrable t)
  refine ⟨had, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((Bass.filtration d).le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (had s).aestronglyMeasurable
  have hAglobal := (Bass.filtration d).le s _ hA
  calc
    (∫ γ : Bass.Path d in A, M s γ ∂P) = ∫ γ : Bass.Path d in A, M s γ ∂P.completion :=
      (setIntegral_completion (hmeas s) hAglobal).symm
    _ = ∫ γ : Bass.Path d in A, M t γ ∂P.completion :=
      hM.setIntegral_eq hst (filtration_le_usualFiltration P s _ hA)
    _ = ∫ γ : Bass.Path d in A, M t γ ∂P := setIntegral_completion (hmeas t) hAglobal

/-- Completed local martingales retain explicit integrability of every stopped process. -/
def IsLocalMartingale {d : ℕ} (M : ℝ≥0 → Bass.Path d → ℝ)
    (P : Measure (Bass.Path d)) : Prop :=
  StronglyAdapted (usualFiltration P) M ∧
    ∃ τ : ℕ → Bass.Path d → WithTop ℝ≥0,
      IsLocalizingSequence (usualFiltration P) τ P.completion ∧
        ∀ n, (∀ t, Integrable (stoppedProcess M (τ n) t) P.completion) ∧
          Martingale (stoppedProcess M (τ n)) (usualFiltration P) P.completion

/-- Original stopping times remain stopping times after usual augmentation; the same
localizers and actual stopped processes give a completed local martingale. -/
theorem isLocalMartingale_completion {d : ℕ} {P : Measure (Bass.Path d)}
    [IsFiniteMeasure P] {M : ℝ≥0 → Bass.Path d → ℝ} (hM : Bass.IsLocalMartingale M P) :
    IsLocalMartingale M P := by
  obtain ⟨had, τ, hτ, hstop⟩ := hM
  refine ⟨fun t => (had t).mono (filtration_le_usualFiltration P t), τ, ?_, ?_⟩
  · refine ⟨⟨?_, hτ.tendsto_top⟩, hτ.mono⟩
    intro n t
    exact filtration_le_usualFiltration P t _ (hτ.isStoppingTime n t)
  · intro n
    have hm := martingale_completion (hstop n).2
    refine ⟨fun t => ?_, hm⟩
    exact (integrable_completion_iff
      (((hstop n).2.stronglyAdapted t).mono ((Bass.filtration d).le t))).mpr ((hstop n).1 t)

/-- A completed local martingale bounded on every deterministic time horizon is a
true completed martingale. This does not decomplete any stopping time. -/
theorem IsLocalMartingale.martingale_of_bounded {d : ℕ} {M : ℝ≥0 → Bass.Path d → ℝ}
    {P : Measure (Bass.Path d)} [IsFiniteMeasure P] (hM : IsLocalMartingale M P)
    (hbound : ∀ T : ℝ≥0, ∃ C : ℝ, ∀ t ≤ T, ∀ γ : Bass.Path d, ‖M t γ‖ ≤ C) :
    Martingale M (usualFiltration P) P.completion := by
  haveI := completion_isFiniteMeasure P
  haveI : IsFiniteMeasure P.completion := ⟨measure_lt_top P _⟩
  haveI := completion_sigmaFiniteFiltration P
  haveI : SigmaFiniteFiltration P.completion (usualFiltration P) :=
    completion_sigmaFiniteFiltration P
  obtain ⟨had, τ, hτ, hstop⟩ := hM
  have hint (t : ℝ≥0) : Integrable (M t) P.completion := by
    obtain ⟨C, hC⟩ := hbound t
    exact Integrable.of_bound ((had t).mono ((usualFiltration P).le t)).aestronglyMeasurable
      C (Filter.Eventually.of_forall (hC t le_rfl))
  have hlim (t : ℝ≥0) : ∀ᵐ γ ∂P.completion,
      Filter.Tendsto (fun n => stoppedProcess M (τ n) t γ)
        Filter.atTop (𝓝 (M t γ)) := by
    filter_upwards [hτ.tendsto_top] with γ hγ
    apply tendsto_const_nhds.congr'
    filter_upwards [hγ.eventually (eventually_gt_nhds
      (show (t : WithTop ℝ≥0) < ⊤ from WithTop.coe_lt_top t))] with n hn
    exact (stoppedProcess_eq_of_le hn.le).symm
  have hconv (t : ℝ≥0) (A : Set (Bass.Path d)) :
      Filter.Tendsto (fun n => ∫ γ : Bass.Path d in A, stoppedProcess M (τ n) t γ ∂P.completion)
        Filter.atTop (𝓝 (∫ γ : Bass.Path d in A, M t γ ∂P.completion)) := by
    haveI := completion_restrict_isFiniteMeasure P A
    haveI : IsFiniteMeasure (P.completion.restrict A) := completion_restrict_isFiniteMeasure P A
    obtain ⟨C, hC⟩ := hbound t
    refine tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => ((hstop n).1 t).aestronglyMeasurable.restrict)
      (integrable_const _) (fun n => Filter.Eventually.of_forall fun γ => ?_)
      (ae_restrict_of_ae (hlim t))
    exact hC _ (WithTop.untopA_le (min_le_left (t : WithTop ℝ≥0) (τ n γ))) γ
  refine ⟨had, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((usualFiltration P).le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (had s).aestronglyMeasurable
  have hconv_s := hconv s A
  have hconv_t := hconv t A
  have heq (n : ℕ) : (∫ γ : Bass.Path d in A, stoppedProcess M (τ n) s γ ∂P.completion) =
      ∫ γ : Bass.Path d in A, stoppedProcess M (τ n) t γ ∂P.completion :=
    ((hstop n).2).setIntegral_eq hst hA
  simp_rw [heq] at hconv_s
  exact tendsto_nhds_unique hconv_s hconv_t

/-- The all-C² martingale problem for the completed usual filtration, for the same law. -/
def SolvesMartingaleProblem {d : ℕ} (a : Vec d → Mat d) (b : Vec d → Vec d)
    (x : Vec d) (P : Measure (Bass.Path d)) : Prop :=
  IsProbabilityMeasure P ∧ (∀ᵐ γ ∂P.completion, (γ : Bass.Path d) 0 = x) ∧
    ∀ f : Vec d → ℝ, ContDiff ℝ (2 : ℕ∞) f →
      (∀ t : ℝ≥0, ∀ᵐ γ ∂P.completion,
        IntervalIntegrable (fun u : ℝ => Bass.generator a b f ((γ : Bass.Path d) u.toNNReal))
          volume 0 (t : ℝ)) ∧
      IsLocalMartingale (Bass.compensatedTest a b f) P

/-- A compact C² completed compensator is a true martingale for the original raw
filtration. Only its actual raw adaptation is used to descend the bounded process. -/
theorem compactC2_martingale_raw {d : ℕ} {a : Vec d → Mat d}
    {b : Vec d → Vec d} {x : Vec d} {P : Measure (Bass.Path d)}
    (hP : SolvesMartingaleProblem a b x P) (ha : Measurable a) (hb : Measurable b)
    {Ma Mb : ℝ} (haBound : ∀ y i j, |a y i j| ≤ Ma)
    (hbBound : ∀ y i, |b y i| ≤ Mb) {f : Vec d → ℝ}
    (hf : ContDiff ℝ (2 : ℕ∞) f) (hc : HasCompactSupport f) :
    Martingale (Bass.compensatedTest a b f) (Bass.rawFiltration d) P := by
  haveI : IsProbabilityMeasure P := hP.1
  have hcoef : EinsteinFull.BddCoef a b (max Ma Mb) :=
    ⟨fun i j => (show Continuous (fun A : Mat d => A i j) from
        (continuous_apply j).comp (continuous_apply i)).measurable.comp ha,
      fun i => (measurable_pi_apply i).comp hb,
      fun y i j => (haBound y i j).trans (le_max_left _ _),
      fun y i => (hbBound y i).trans (le_max_right _ _)⟩
  have had : StronglyAdapted (Bass.rawFiltration d) (Bass.compensatedTest a b f) := by
    intro t
    rw [Bass.rawFiltration_eq_comap]
    exact (EinsteinFull.stronglyAdapted_compensatedTest_of_measurable
      (Draft.svGenerator a b) f hf.continuous (hcoef.measurable_gen f) t).comp_measurable
        (comap_measurable Bass.Path.toContinuousMap)
  have hm := martingale_of_completion
    ((hP.2.2 f hf).2.martingale_of_bounded
      (Bass.compensatedTest_bounded haBound hbBound hf hc))
    (fun t => (had t).mono (Bass.rawFiltration_le_filtration d t))
  refine ⟨had, fun s t hst => ?_⟩
  symm
  refine ae_eq_condExp_of_forall_setIntegral_eq ((Bass.rawFiltration d).le s)
    (hm.integrable t) (fun _ _ _ => (hm.integrable s).integrableOn)
    (fun A hA _ => ?_) (had s).aestronglyMeasurable
  exact hm.setIntegral_eq hst (Bass.rawFiltration_le_filtration d s _ hA)

/-- Completion and usual augmentation preserve the all-C² martingale problem for
each supplied law. The converse descends bounded compact tests, then uses the
checked frozen-to-all-C² localization, rather than decompleting stopping times. -/
theorem solvesMartingaleProblem_iff {d : ℕ} {a : Vec d → Mat d}
    {b : Vec d → Vec d} {x : Vec d} {P : Measure (Bass.Path d)}
    (ha : Measurable a) (hb : Measurable b) {Ma Mb : ℝ}
    (haBound : ∀ y i j, |a y i j| ≤ Ma)
    (hbBound : ∀ y i, |b y i| ≤ Mb) :
    SolvesMartingaleProblem a b x P ↔ Bass.SolvesMartingaleProblem a b x P := by
  constructor
  · intro hP
    haveI : IsProbabilityMeasure P := hP.1
    have hcoef : EinsteinFull.BddCoef a b (max Ma Mb) :=
      ⟨fun i j => (show Continuous (fun A : Mat d => A i j) from
          (continuous_apply j).comp (continuous_apply i)).measurable.comp ha,
        fun i => (measurable_pi_apply i).comp hb,
        fun y i j => (haBound y i j).trans (le_max_left _ _),
        fun y i => (hbBound y i).trans (le_max_right _ _)⟩
    have hmap : EinsteinRelation.SolvesMartingaleProblem (Draft.svGenerator a b) x
        (P.map (Bass.pathMeasurableEquiv d)) := by
      refine ⟨inferInstance, ?_, fun f hf hc => ?_⟩
      · exact (Bass.pathMeasurableEquiv d).measurableEmbedding.ae_map_iff.mpr hP.2.1
      have hf2 : ContDiff ℝ 2 f := EinsteinFull.contDiff_two_of_top hf
      have had := EinsteinFull.stronglyAdapted_compensatedTest_of_measurable
        (Draft.svGenerator a b) f hf.continuous (hcoef.measurable_gen f)
      have hsource : StronglyAdapted (Bass.filtration d) (Bass.compensatedTest a b f) := by
        intro t
        have hraw : StronglyMeasurable[Bass.rawFiltration d t]
            (Bass.compensatedTest a b f t) := by
          rw [Bass.rawFiltration_eq_comap]
          exact (had t).comp_measurable (comap_measurable Bass.Path.toContinuousMap)
        exact hraw.mono (Bass.rawFiltration_le_filtration d t)
      have hm := Bass.martingale_map_pathMeasurableEquiv
        (martingale_of_completion
          ((hP.2.2 f hf2).2.martingale_of_bounded
            (Bass.compensatedTest_bounded haBound hbBound hf2 hc)) hsource) had
      refine ⟨?_, hm.integrable, hm⟩
      intro t
      exact (Bass.pathMeasurableEquiv d).measurableEmbedding.ae_map_iff.mpr
        ((hP.2.2 f hf2).1 t)
    have hback := Bass.solves_of_frozen hmap ha hb haBound hbBound
    simpa only [Bass.map_pathMeasurableEquiv_roundtrip] using hback
  · intro hP
    haveI : IsProbabilityMeasure P := hP.1
    exact ⟨hP.1, hP.2.1, fun f hf =>
      ⟨(hP.2.2 f hf).1, isLocalMartingale_completion (hP.2.2 f hf).2⟩⟩

-- Transitive axiom checks for the completed-filtration transport.
#print axioms sup_nullSets_eq_eventuallyMeasurableSpace
#print axioms eventuallyMeasurableSpace_iInf_of_antitone
#print axioms usualFiltration_eq_eventuallyMeasurableSpace
#print axioms measurableSet_usualFiltration_iff
#print axioms completion_trim
#print axioms completion_isFiniteMeasure
#print axioms completion_sigmaFiniteFiltration
#print axioms completion_restrict_isFiniteMeasure
#print axioms integrable_completion_iff
#print axioms integral_completion
#print axioms setIntegral_completion
#print axioms martingale_completion
#print axioms martingale_of_completion
#print axioms isLocalMartingale_completion
#print axioms IsLocalMartingale.martingale_of_bounded
#print axioms compactC2_martingale_raw
#print axioms solvesMartingaleProblem_iff

end EinsteinFull.External.Bass.Completion
